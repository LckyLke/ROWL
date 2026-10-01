import Rowl.StructuralCongruence

namespace Rowl.AxiomSet
open Aeneas Aeneas.Std RowlRust.model RowlRust.axiom_set
open Rowl.AxiomEquality (AxiomEq axiom_eq_refl axiom_eq_symm axiom_eq_trans)
attribute [local instance] Classical.propDecidable
attribute [local simp] alloc.vec.Vec.eq_iff
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- Logical content in source order; origin tokens are retained separately. -/
def Closure (rows : List AxiomOccurrence) : Rowl.Owl.AxiomClosure := rows.map (·.axiom)
/-- All original occurrences must be checked before grouping copies. -/
def Valid (rows : List AxiomOccurrence) : Prop :=
  ∀ row ∈ rows, Rowl.Arity.AxiomAllowed row.axiom
/-- Exact first forbidden original object, including its supplied provenance. -/
def FirstForbidden (rows : List AxiomOccurrence) (row : AxiomOccurrence) : Prop :=
  ∃ before after, rows = before ++ row :: after ∧ Valid before ∧
    ¬ Rowl.Arity.AxiomAllowed row.axiom
/-- Structural equivalence with an original occurrence at a given source index. -/
def MatchAt (rows : List AxiomOccurrence) (sought : AnnotatedAxiom) (index : Nat) : Prop :=
  ∃ row, rows[index]? = some row ∧ AxiomEq row.axiom sought
/-- First structural representative, specified by minimality rather than code. -/
def FirstRepresentative (rows : List AxiomOccurrence) (index representative : Nat) : Prop :=
  ∃ row, rows[index]? = some row ∧ representative ≤ index ∧
    MatchAt rows row.axiom representative ∧
    ∀ earlier, earlier < representative → ¬ MatchAt rows row.axiom earlier
/-- The first occurrences among a prefix, ordered by their source indices. -/
noncomputable def Roots (rows : List AxiomOccurrence) (count : Nat) : List Nat :=
  (List.range count).filter (fun index => decide (FirstRepresentative rows index index))
/-- A per-occurrence first-representative map and its ordered unique roots. -/
def IndexInvariant (rows : List AxiomOccurrence) (count : Nat)
    (mapping roots : alloc.vec.Vec Usize) : Prop :=
  mapping.val.length = count ∧ roots.val.map UScalar.val = Roots rows count ∧
    ∀ index, index < count → ∃ representative,
      mapping.val[index]? = some representative ∧
      FirstRepresentative rows index representative.val
/-- The invariant guaranteed by the private Rust constructor. -/
def WellFormed (set : AxiomSet) : Prop :=
  Valid set.source.val ∧
    IndexInvariant set.source.val set.source.val.length set.representative_of set.representatives
/-- Exact failure or a validated structural set retaining every source object. -/
def Correct (source : alloc.vec.Vec AxiomOccurrence) (result : BuildResult) : Prop :=
  match result with
  | .InvalidArity row => FirstForbidden source.val row
  | .Set set => set.source = source ∧ WellFormed set
/-- A mathematical view of the representative axioms, without copying Rust ASTs. -/
def RepresentativeClosure (set : AxiomSet) : Rowl.Owl.AxiomClosure :=
  set.representatives.val.filterMap (fun index => (set.source.val[index.val]?).map (·.axiom))

private noncomputable def forbidden (row : AxiomOccurrence) : Bool :=
  decide (¬ Rowl.Arity.AxiomAllowed row.axiom)

private theorem forbidden_total (source : alloc.vec.Vec AxiomOccurrence) (index : Usize) :
    first_forbidden_from source index = .ok ((source.val.drop index.val).find? forbidden) := by
  rw [first_forbidden_from]
  by_cases inside : index.val < source.val.length
  · have lookup : source.index_usize index = .ok source.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have step : (source.val.drop index.val).find? forbidden =
        if Rowl.Arity.AxiomAllowed source.val[index.val].axiom then
          (source.val.drop (index.val + 1)).find? forbidden else some source.val[index.val] := by
      rw [List.drop_eq_getElem_cons inside]
      by_cases accepted : Rowl.Arity.AxiomAllowed source.val[index.val].axiom <;>
        simp only [List.find?_cons, forbidden, accepted, not_true_eq_false, not_false_eq_true,
          decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
    by_cases accepted : Rowl.Arity.AxiomAllowed source.val[index.val].axiom
    · obtain ⟨next, advance, value⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using value
      have recurse := forbidden_total source next
      simp [inside, alloc.vec.Vec.index_slice_index, lookup,
        Rowl.Arity.axiom_allowed_total_correct, accepted, advance, recurse, step, nv]
    · simp [inside, alloc.vec.Vec.index_slice_index, lookup,
        Rowl.Arity.axiom_allowed_total_correct, accepted, step]
  · have empty : source.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside, empty]
termination_by source.val.length - index.val
decreasing_by all_goals omega

private theorem match_at_get (rows : List AxiomOccurrence) (sought : AnnotatedAxiom)
    (index : Nat) (inside : index < rows.length) :
    MatchAt rows sought index ↔ AxiomEq rows[index].axiom sought := by
  simp [MatchAt, List.getElem?_eq_getElem inside]

private theorem first_match_total (source : alloc.vec.Vec AxiomOccurrence)
    (sought : AnnotatedAxiom) (stop index : Usize)
    (order : index.val ≤ stop.val) (bound : stop.val ≤ source.val.length) :
    ∃ answer, first_match_from source sought stop index = .ok answer ∧
      index.val ≤ answer.val ∧ answer.val ≤ stop.val ∧
      (answer.val < stop.val → MatchAt source.val sought answer.val) ∧
      ∀ earlier, index.val ≤ earlier → earlier < answer.val → ¬ MatchAt source.val sought earlier := by
  rw [first_match_from]
  by_cases inside : index.val < stop.val
  · have sourceInside : index.val < source.val.length := by omega
    have lookup : source.index_usize index = .ok source.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem sourceInside]
    by_cases same : AxiomEq source.val[index.val].axiom sought
    · refine ⟨index, ?_, le_rfl, by omega, ?_, ?_⟩
      · simp [inside, alloc.vec.Vec.index_slice_index, lookup,
          Rowl.AxiomEquality.same_axiom_total_correct, same]
      · intro _; exact (match_at_get _ _ _ sourceInside).mpr same
      · intro earlier lower upper; omega
    · obtain ⟨next, advance, value⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using value
      obtain ⟨answer, executed, lower, upper, found, absent⟩ :=
        first_match_total source sought stop next (by omega) bound
      refine ⟨answer, ?_, by omega, upper, found, ?_⟩
      · simp [inside, alloc.vec.Vec.index_slice_index, lookup,
          Rowl.AxiomEquality.same_axiom_total_correct, same, advance, executed]
      · intro earlier lo hi
        by_cases equal : earlier = index.val
        · subst earlier; exact fun matching => same ((match_at_get _ _ _ sourceInside).mp matching)
        · exact absent earlier (by omega) hi
  · refine ⟨stop, by simp [inside], by omega, le_rfl, by omega, ?_⟩
    intro earlier lower upper; omega
termination_by stop.val - index.val
decreasing_by all_goals omega

private theorem first_for_index (source : alloc.vec.Vec AxiomOccurrence) (index : Usize)
    (inside : index.val < source.val.length) :
    ∃ answer, first_match_from source source.val[index.val].axiom index 0#usize = .ok answer ∧
      FirstRepresentative source.val index.val answer.val := by
  obtain ⟨answer, executed, _, upper, found, absent⟩ :=
    first_match_total source source.val[index.val].axiom index 0#usize (by simp) (by omega)
  refine ⟨answer, executed, source.val[index.val], List.getElem?_eq_getElem inside, upper, ?_, ?_⟩
  · by_cases earlier : answer.val < index.val
    · exact found earlier
    · have equal : answer.val = index.val := by omega
      rw [equal]; exact (match_at_get _ _ _ inside).mpr (axiom_eq_refl _)
  · intro earlier hi; exact absent earlier (by simp) hi

private theorem first_unique {rows : List AxiomOccurrence} {index a b : Nat}
    (left : FirstRepresentative rows index a) (right : FirstRepresentative rows index b) : a = b := by
  obtain ⟨x, hx, _, matchedA, priorA⟩ := left
  obtain ⟨y, hy, _, matchedB, priorB⟩ := right
  have xy : x = y := Option.some.inj (hx.symm.trans hy)
  subst y
  by_cases ab : a < b
  · exact False.elim (priorB a ab matchedA)
  · by_cases ba : b < a
    · exact False.elim (priorA b ba matchedB)
    · omega

private theorem root_iff {rows : List AxiomOccurrence} {index representative : Nat}
    (first : FirstRepresentative rows index representative) :
    representative = index ↔ FirstRepresentative rows index index := by
  constructor
  · intro equal; simpa [equal] using first
  · intro root; exact first_unique first root

private theorem roots_length (rows : List AxiomOccurrence) (count : Nat) :
    (Roots rows count).length ≤ count := by
  simpa [Roots] using List.length_filter_le
    (fun index => decide (FirstRepresentative rows index index)) (List.range count)

private theorem roots_succ (rows : List AxiomOccurrence) (count : Nat) :
    Roots rows (count + 1) = Roots rows count ++
      if FirstRepresentative rows count count then [count] else [] := by
  by_cases root : FirstRepresentative rows count count <;>
    simp [Roots, List.range_succ, List.filter_append, root]

private theorem invariant_step {rows : List AxiomOccurrence} {index : Nat}
    {mapping roots afterMap afterRoots : alloc.vec.Vec Usize} {answer current : Usize}
    (valid : IndexInvariant rows index mapping roots) (currentVal : current.val = index)
    (first : FirstRepresentative rows index answer.val)
    (mapContents : afterMap.val = mapping.val ++ [answer])
    (rootContents : afterRoots.val = roots.val ++ if answer = current then [current] else []) :
    IndexInvariant rows (index + 1) afterMap afterRoots := by
  refine ⟨by simp [mapContents, valid.1], ?_, ?_⟩
  · have same : answer = current ↔ FirstRepresentative rows index index := by
      rw [UScalar.eq_equiv, currentVal]; exact root_iff first
    by_cases root : FirstRepresentative rows index index <;>
      simp [rootContents, List.map_append, valid.2.1, roots_succ, same, currentVal, root]
  · intro j inside
    by_cases old : j < index
    · obtain ⟨r, lookup, correct⟩ := valid.2.2 j old
      refine ⟨r, ?_, correct⟩
      simpa [mapContents, List.getElem?_append, valid.1, old] using lookup
    · have ji : j = index := by omega
      subst j
      refine ⟨answer, ?_, first⟩
      simp [mapContents, List.getElem?_append, valid.1]

private theorem build_from_total (source : alloc.vec.Vec AxiomOccurrence) (index : Usize)
    (mapping roots : alloc.vec.Vec Usize) (order : index.val ≤ source.val.length)
    (invariant : IndexInvariant source.val index.val mapping roots) :
    ∃ set, build_from source index mapping roots = .ok set ∧ set.source = source ∧
      IndexInvariant source.val source.val.length set.representative_of set.representatives := by
  rw [build_from]
  by_cases inside : index.val < source.val.length
  · have lookup : source.index_usize index = .ok source.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨answer, matched, first⟩ := first_for_index source index inside
    have mapBound : mapping.val.length < Usize.max := by
      have := invariant.1; scalar_tac
    obtain ⟨afterMap, appended, mapContents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec mapping answer mapBound)
    have rootBound : roots.val.length < Usize.max := by
      have size := roots_length source.val index.val
      have equal := congrArg List.length invariant.2.1
      simp only [List.length_map] at equal
      scalar_tac
    obtain ⟨next, advance, value⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nv : next.val = index.val + 1 := by simpa using value
    by_cases root : answer = index
    · obtain ⟨afterRoots, rootAppend, rootContents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec roots index rootBound)
      have nextInvariant : IndexInvariant source.val next.val afterMap afterRoots := by
        rw [nv]; exact invariant_step invariant rfl first mapContents (by simpa [root] using rootContents)
      obtain ⟨set, recurse, unchanged, complete⟩ :=
        build_from_total source next afterMap afterRoots (by omega) nextInvariant
      refine ⟨set, ?_, unchanged, complete⟩
      simp [inside, alloc.vec.Vec.index_slice_index, lookup, matched, appended,
        root, rootAppend, advance, recurse, (show mapping.push index = .ok afterMap by simpa [root] using appended)]
    · have nextInvariant : IndexInvariant source.val next.val afterMap roots := by
        rw [nv]; exact invariant_step invariant rfl first mapContents (by simp [root])
      obtain ⟨set, recurse, unchanged, complete⟩ :=
        build_from_total source next afterMap roots (by omega) nextInvariant
      refine ⟨set, ?_, unchanged, complete⟩
      simp [inside, alloc.vec.Vec.index_slice_index, lookup, matched, appended,
        root, advance, recurse]
  · have finished : index.val = source.val.length := by omega
    refine ⟨⟨source, mapping, roots⟩, by simp [inside], rfl, ?_⟩
    simpa [finished] using invariant
termination_by source.val.length - index.val
decreasing_by all_goals omega

/-- Every input terminates with the exact first invalid original, or a complete
    minimal representative map and an ordered set of all first occurrences. -/
theorem build_total_correct (source : alloc.vec.Vec AxiomOccurrence) :
    ∃ result, build source = .ok result ∧ Correct source result := by
  have scan : first_forbidden_from source 0#usize = .ok (source.val.find? forbidden) := by
    simpa using forbidden_total source 0#usize
  cases outcome : source.val.find? forbidden with
  | some row =>
    refine ⟨.InvalidArity row, by simp [build, scan, outcome], ?_⟩
    obtain ⟨bad, before, after, equal, accepted⟩ :=
      List.find?_eq_some_iff_append.mp outcome
    refine ⟨before, after, equal, ?_, ?_⟩
    · simpa [Valid, forbidden] using accepted
    · simpa [forbidden] using bad
  | none =>
    have valid : Valid source.val := by
      simpa [Valid, forbidden] using List.find?_eq_none.mp outcome
    have empty : IndexInvariant source.val 0 (alloc.vec.Vec.new Usize) (alloc.vec.Vec.new Usize) := by
      simp [IndexInvariant, Roots, alloc.vec.Vec.new]
    obtain ⟨set, executed, unchanged, invariant⟩ :=
      build_from_total source 0#usize (alloc.vec.Vec.new Usize) (alloc.vec.Vec.new Usize) (by simp) empty
    refine ⟨.Set set, by simp [build, scan, outcome, executed], unchanged, ?_, ?_⟩
    · simpa [unchanged] using valid
    · simpa [unchanged] using invariant

/-- Original order, multiplicity, bodies, annotations and origin tokens survive. -/
theorem originals_total_correct (set : AxiomSet) : originals set = .ok set.source := rfl
/-- The accessor returns the actual immutable representative index vector. -/
theorem representatives_total_correct (set : AxiomSet) :
    representatives set = .ok set.representatives := rfl
/-- The accessor returns the complete per-source-occurrence mapping. -/
theorem representative_indices_total_correct (set : AxiomSet) :
    representative_indices set = .ok set.representative_of := rfl
/-- Checked lookup for every valid or out-of-range source index. -/
theorem occurrence_total_correct (set : AxiomSet) (index : Usize) :
    occurrence set index = .ok (set.source.val[index.val]?) := by
  rw [occurrence]
  by_cases inside : index.val < set.source.val.length
  · have lookup : set.source.index_usize index = .ok set.source.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    simp [inside, alloc.vec.Vec.index_slice_index, lookup, List.getElem?_eq_getElem inside]
  · have absent : set.source.val[index.val]? = none :=
      List.getElem?_eq_none (by omega)
    simp [inside, absent]

private theorem first_bound {rows : List AxiomOccurrence} {index representative : Nat}
    (first : FirstRepresentative rows index representative) : representative < rows.length := by
  obtain ⟨_, _, _, matching, _⟩ := first
  obtain ⟨row, lookup, _⟩ := matching
  by_contra no
  have absent : rows[representative]? = none := List.getElem?_eq_none (by omega)
  rw [absent] at lookup; contradiction

/-- The public resolver is total for every privately constructed valid set;
    a returned object is the exact original first representative with provenance. -/
theorem representative_of_total_correct (set : AxiomSet) (valid : WellFormed set) (index : Usize) :
    representative_of set index = .ok
      ((set.representative_of.val[index.val]?).bind (fun r => set.source.val[r.val]?)) := by
  rw [representative_of]
  by_cases inside : index.val < set.representative_of.val.length
  · have sourceInside : index.val < set.source.val.length := by
      have := valid.2.1; omega
    obtain ⟨r, lookup, first⟩ := valid.2.2.2 index.val sourceInside
    have bound := first_bound first
    have mapLookup : set.representative_of.index_usize index = .ok r := by
      simp [alloc.vec.Vec.index_usize, lookup]
    have sourceLookup : set.source.index_usize r = .ok set.source.val[r.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem bound]
    have mapValue : set.representative_of.val[index.val] = r :=
      Option.some.inj ((List.getElem?_eq_getElem inside).symm.trans lookup)
    simp [inside, alloc.vec.Vec.index_slice_index, mapLookup, sourceLookup,
      List.getElem?_eq_getElem inside, mapValue, List.getElem?_eq_getElem bound]
  · have absent : set.representative_of.val[index.val]? = none :=
      List.getElem?_eq_none (by omega)
    simp [inside, absent]

private theorem matched_trans {rows : List AxiomOccurrence} {a b : AnnotatedAxiom} {index : Nat}
    (matched : MatchAt rows a index) (equal : AxiomEq a b) : MatchAt rows b index := by
  obtain ⟨row, lookup, old⟩ := matched
  exact ⟨row, lookup, axiom_eq_trans _ _ _ old equal⟩

private theorem representative_is_root {rows : List AxiomOccurrence} {index r : Nat}
    (first : FirstRepresentative rows index r) : FirstRepresentative rows r r := by
  obtain ⟨original, _, _, ⟨row, lookup, equal⟩, absent⟩ := first
  refine ⟨row, lookup, le_rfl, ⟨row, lookup, axiom_eq_refl _⟩, ?_⟩
  intro earlier before matched
  exact absent earlier before (matched_trans matched equal)

private theorem roots_mem (rows : List AxiomOccurrence) (count index : Nat) :
    index ∈ Roots rows count ↔ index < count ∧ FirstRepresentative rows index index := by
  simp [Roots]

private theorem root_unique {rows : List AxiomOccurrence} {i j : Nat}
    (left : FirstRepresentative rows i i) (right : FirstRepresentative rows j j)
    {x y : AxiomOccurrence} (hx : rows[i]? = some x) (hy : rows[j]? = some y)
    (equal : AxiomEq x.axiom y.axiom) : i = j := by
  obtain ⟨a, ha, _, _, priorA⟩ := left
  obtain ⟨b, hb, _, _, priorB⟩ := right
  have ax : a = x := Option.some.inj (ha.symm.trans hx)
  have byy : b = y := Option.some.inj (hb.symm.trans hy)
  subst a; subst b
  by_cases ij : i < j
  · exact False.elim (priorB i ij ⟨x, hx, equal⟩)
  · by_cases ji : j < i
    · exact False.elim (priorA j ji ⟨y, hy, axiom_eq_symm _ _ equal⟩)
    · omega

/-- Acceptance is exactly validity of all original structural arities. This is
    not an assertion of full OWL DL validity. -/
theorem build_accepts_iff (source : alloc.vec.Vec AxiomOccurrence) :
    (∃ set, build source = .ok (.Set set)) ↔ Valid source.val := by
  obtain ⟨result, executed, correct⟩ := build_total_correct source
  constructor
  · rintro ⟨set, accepted⟩
    have same := Result.ok_injective (executed.symm.trans accepted)
    subst result
    simpa [correct.1] using correct.2.1
  · intro valid
    cases result with
    | Set set => exact ⟨set, executed⟩
    | InvalidArity row =>
      obtain ⟨before, after, equal, _, bad⟩ := correct
      have member : row ∈ source.val := by simp [equal]
      exact False.elim (bad (valid row member))

/-- Every public representative index is an in-range first occurrence. -/
theorem representatives_are_roots (set : AxiomSet) (valid : WellFormed set)
    (r : Usize) (member : r ∈ set.representatives.val) :
    r.val < set.source.val.length ∧ FirstRepresentative set.source.val r.val r.val := by
  have mapped : r.val ∈ set.representatives.val.map UScalar.val := List.mem_map.mpr ⟨r, member, rfl⟩
  rw [valid.2.2.1] at mapped
  exact (roots_mem _ _ _).mp mapped

/-- No representative source index occurs twice. -/
theorem representative_indices_unique (set : AxiomSet) (valid : WellFormed set) :
    (set.representatives.val.map UScalar.val).Nodup := by
  rw [valid.2.2.1]
  exact List.Nodup.filter _ List.nodup_range

/-- Representatives follow strictly increasing first-occurrence source order. -/
theorem representative_order (set : AxiomSet) (valid : WellFormed set) :
    (set.representatives.val.map UScalar.val).Pairwise (· < ·) := by
  rw [valid.2.2.1]
  exact List.Pairwise.filter _ List.pairwise_lt_range

/-- No two distinct representatives belong to the same complete annotated
    structural axiom class, even if their origin tokens differ. -/
theorem representatives_structurally_unique (set : AxiomSet) (valid : WellFormed set)
    (i j : Usize) (mi : i ∈ set.representatives.val) (mj : j ∈ set.representatives.val)
    (x y : AxiomOccurrence) (hx : set.source.val[i.val]? = some x)
    (hy : set.source.val[j.val]? = some y) (equal : AxiomEq x.axiom y.axiom) : i = j := by
  have firstI := (representatives_are_roots set valid i mi).2
  have firstJ := (representatives_are_roots set valid j mj).2
  exact UScalar.eq_of_val_eq (root_unique firstI firstJ hx hy equal)

/-- Every source occurrence maps to a present representative that is at or
    before that occurrence; metadata on both original objects is untouched. -/
theorem mapping_is_minimal_and_present (set : AxiomSet) (valid : WellFormed set)
    (index : Nat) (inside : index < set.source.val.length) :
    ∃ r, set.representative_of.val[index]? = some r ∧ r ∈ set.representatives.val ∧
      FirstRepresentative set.source.val index r.val := by
  obtain ⟨r, lookup, first⟩ := valid.2.2.2 index inside
  have root := representative_is_root first
  have bound := first_bound first
  have member : r.val ∈ set.representatives.val.map UScalar.val := by
    rw [valid.2.2.1]; exact (roots_mem _ _ _).mpr ⟨bound, root⟩
  obtain ⟨s, ms, equal⟩ := List.mem_map.mp member
  have sr : s = r := UScalar.eq_of_val_eq equal
  subst s
  exact ⟨r, lookup, ms, first⟩

/-- Resolving a representative again leaves the same source index. -/
theorem representative_map_idempotent (set : AxiomSet) (valid : WellFormed set)
    (index : Nat) (inside : index < set.source.val.length) (r : Usize)
    (mapped : set.representative_of.val[index]? = some r) :
    set.representative_of.val[r.val]? = some r := by
  obtain ⟨s, lookup, _, first⟩ := mapping_is_minimal_and_present set valid index inside
  have sr : s = r := Option.some.inj (lookup.symm.trans mapped)
  subst s
  obtain ⟨t, lookupT, firstT⟩ := valid.2.2.2 r.val (first_bound first)
  have tr : t = r := UScalar.eq_of_val_eq (first_unique firstT (representative_is_root first))
  simpa [tr] using lookupT

/-- Every selected representative is an actual original axiom. -/
theorem representative_closure_original (set : AxiomSet) (a : AnnotatedAxiom)
    (member : a ∈ RepresentativeClosure set) : ∃ row ∈ set.source.val, row.axiom = a := by
  obtain ⟨r, _, lookup⟩ := List.mem_filterMap.mp member
  cases sourceLookup : set.source.val[r.val]? with
  | none => simp [sourceLookup] at lookup
  | some row =>
    have equal : row.axiom = a := by simpa [sourceLookup] using lookup
    exact ⟨row, List.mem_of_getElem? sourceLookup, equal⟩

/-- Selected axioms inherit the checked original arities. -/
theorem representative_closure_valid (set : AxiomSet) (valid : WellFormed set) :
    Rowl.Arity.ClosureOK (RepresentativeClosure set) := by
  intro a member
  obtain ⟨row, mr, equal⟩ := representative_closure_original set a member
  simpa [equal] using valid.1 row mr

/-- The actual built representatives and the complete original closure have
    exactly the same structural axiom classes, annotations included. -/
theorem representative_closure_equivalent (set : AxiomSet) (valid : WellFormed set) :
    Rowl.StructuralCongruence.ClosureEq (Closure set.source.val) (RepresentativeClosure set) := by
  constructor
  · intro a member
    obtain ⟨row, mr, equal⟩ := List.mem_map.mp member
    obtain ⟨index, inside, element⟩ := List.mem_iff_getElem.mp mr
    obtain ⟨r, _, present, original, originalLookup, _, representative, _⟩ :=
      mapping_is_minimal_and_present set valid index inside
    have originalEqual : original = row :=
      Option.some.inj (originalLookup.symm.trans ((List.getElem?_eq_getElem inside).trans (congrArg some element)))
    subst original
    obtain ⟨chosen, chosenLookup, chosenEqual⟩ := representative
    refine ⟨chosen.axiom, List.mem_filterMap.mpr ⟨r, present, by simp [chosenLookup]⟩, ?_⟩
    simpa [equal] using axiom_eq_symm _ _ chosenEqual
  · intro a member
    obtain ⟨row, mr, equal⟩ := representative_closure_original set a member
    refine ⟨row.axiom, List.mem_map.mpr ⟨row, mr, rfl⟩, ?_⟩
    simpa [equal] using axiom_eq_refl row.axiom

private theorem original_closure_valid (set : AxiomSet) (valid : WellFormed set) :
    Rowl.Arity.ClosureOK (Closure set.source.val) := by
  intro a member
  obtain ⟨row, mr, equal⟩ := List.mem_map.mp member
  simpa [equal] using valid.1 row mr

universe u v w
/-- Actual set construction preserves OWL models for every fixed normative
    datatype map and vocabulary, including infinite domains. -/
theorem representative_models {Object : Type u} {Value : Type v} {Native : Type w}
    (D : Rowl.Owl.DatatypeMap Native) (embed : Rowl.Owl.ValueEmbedding D Value)
    (V : Rowl.Owl.Vocabulary) (I : Rowl.Owl.Interpretation Object Value)
    (set : AxiomSet) (valid : WellFormed set) :
    Rowl.Owl.Model D embed V I (Closure set.source.val) ↔
      Rowl.Owl.Model D embed V I (RepresentativeClosure set) :=
  Rowl.StructuralCongruence.closure_model D embed V I _ _
    (representative_closure_equivalent set valid) (original_closure_valid set valid)
    (representative_closure_valid set valid)

/-- Existence of models is preserved, without executing a consistency solver. -/
theorem representative_consistency {Native : Type w} (D : Rowl.Owl.DatatypeMap Native)
    (V : Rowl.Owl.Vocabulary) (set : AxiomSet) (valid : WellFormed set) :
    Rowl.Owl.Consistent.{u,v,w} D V (Closure set.source.val) ↔
      Rowl.Owl.Consistent.{u,v,w} D V (RepresentativeClosure set) :=
  Rowl.StructuralCongruence.closure_consistency D V _ _
    (representative_closure_equivalent set valid) (original_closure_valid set valid)
    (representative_closure_valid set valid)

/-- Every OWL consequence is preserved by replacing this supplied source
    closure with its built outer set; this is not an entailment decision. -/
theorem representative_entailment {Native : Type w} (D : Rowl.Owl.DatatypeMap Native)
    (V : Rowl.Owl.Vocabulary) (target : Rowl.Owl.AxiomClosure)
    (set : AxiomSet) (valid : WellFormed set) :
    Rowl.Owl.Entails.{u,v,w} D V (Closure set.source.val) target ↔
      Rowl.Owl.Entails.{u,v,w} D V (RepresentativeClosure set) target :=
  Rowl.StructuralCongruence.source_entailment D V _ _ target
    (representative_closure_equivalent set valid) (original_closure_valid set valid)
    (representative_closure_valid set valid)

/-- The public successful build has the invariants required by all accessors
    and semantic preservation theorems. -/
theorem successful_build_correct (source : alloc.vec.Vec AxiomOccurrence) (set : AxiomSet)
    (executed : build source = .ok (.Set set)) : set.source = source ∧ WellFormed set := by
  obtain ⟨result, total, correct⟩ := build_total_correct source
  have equal := Result.ok_injective (total.symm.trans executed)
  subst result
  exact correct

end Rowl.AxiomSet
