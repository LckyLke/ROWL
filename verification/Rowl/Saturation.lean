import Rowl.AlcOntology
import Rowl.Symbols

/-!
Classification of EL ontologies by saturation (`saturation::classify`), proved
against the independent Direct Semantics. The class expressions of the axioms
are interned into a table of concepts, and the axioms become rules over the
table that hold exactly when the axioms do. Saturation derives subsumers and
links of contexts; every derived fact holds in every model of the rules
(`StateOk`). The final check confirms that the saturated state is closed under
every rule, and the closed state then yields a canonical model of the axioms in
which every context satisfies its subsumers and every registered concept that
holds at a context is one of them. Together they make every answer the Direct
Semantics answer, under every vocabulary and datatype map.
-/
namespace Rowl.Saturation
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation classDenote objectRelation satisfies thing nothing topObject bottomObject
  DatatypeMap ValueEmbedding Vocabulary IsVocabulary IsInterpretation Model ClassSatisfiable Subsumed
  withAnonymous)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
universe u v w

/-! ### Stepping through the Rust code -/

theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by simp [core.num.Usize.MAX]

theorem bind_eq_ok {α β : Type} {x : Result α} {f : α → Result β} {y : β} (h : (x >>= f) = Result.ok y) :
    ∃ a, x = Result.ok a ∧ f a = Result.ok y := by
  cases hx : x.match with
  | ok a =>
    have xa : x = Result.ok a := Result.match.isOk.mp hx
    subst xa
    exact ⟨a, rfl, by simpa using h⟩
  | vis e k =>
    have xv : x = Result.vis e k := Result.match.isVis.mp hx
    subst xv
    have h' : Aeneas.Std.bind (Result.vis e k) f = Result.ok y := h
    rw [bind_vis] at h'
    exact absurd h' vis_not_ok
  | div =>
    have xd : x = Result.div := Result.match.isDiv.mp hx
    subst xd
    have h' : Aeneas.Std.bind Result.div f = Result.ok y := h
    rw [bind_div] at h'
    exact absurd h' div_not_ok

theorem buckets_val : saturation.BUCKETS.val = 4096 := by
  rw [saturation.BUCKETS]
  rfl

/-! ### Membership tests -/

theorem has_from_spec (list : alloc.vec.Vec Usize) (item : Usize) (index : Usize) :
    saturation.has_from list item index =
      .ok (decide (∃ (j : Nat), index.val ≤ j ∧ list.val[j]? = some item)) := by
  rw [saturation.has_from]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    by_cases here : list.val[index.val] = item
    · have found : ∃ (j : Nat), index.val ≤ j ∧ list.val[j]? = some item :=
        ⟨index.val, le_refl _, by rw [List.getElem?_eq_getElem more, here]⟩
      simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, here, found]
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        lookup, bind_ok, here, advance]
      rw [has_from_spec list item next]
      congr 2
      apply propext
      constructor
      · rintro ⟨j, low, at_j⟩
        exact ⟨j, by omega, at_j⟩
      · rintro ⟨j, low, at_j⟩
        by_cases same : j = index.val
        · subst same
          rw [List.getElem?_eq_getElem more] at at_j
          exact absurd (Option.some.inj at_j) here
        · exact ⟨j, by omega, at_j⟩
  · have none : ¬ ∃ (j : Nat), index.val ≤ j ∧ list.val[j]? = some item := by
      rintro ⟨j, low, at_j⟩
      have := (List.getElem?_eq_some_iff.mp at_j).1
      omega
    simp [UScalar.lt_equiv, more, none]
termination_by list.val.length - index.val
decreasing_by omega

theorem has_spec (list : alloc.vec.Vec Usize) (item : Usize) :
    saturation.has list item = .ok (decide (item ∈ list.val)) := by
  rw [saturation.has, has_from_spec]
  congr 2
  apply propext
  simp [List.mem_iff_getElem?]

theorem has_pair_from_spec (list : alloc.vec.Vec (Usize × Usize)) (first second : Usize) (index : Usize) :
    saturation.has_pair_from list first second index =
      .ok (decide (∃ (j : Nat), index.val ≤ j ∧ list.val[j]? = some (first, second))) := by
  rw [saturation.has_pair_from]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    rcases hp : list.val[index.val] with ⟨a, b⟩
    have at_index : list.val[index.val]? = some (a, b) := by rw [List.getElem?_eq_getElem more, hp]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup, bind_ok, hp, advance]
    show (if a = first then if b = second then ok true else saturation.has_pair_from list first second next
      else saturation.has_pair_from list first second next) = _
    rw [has_pair_from_spec list first second next]
    have shift : ¬ (a = first ∧ b = second) →
        ((∃ (j : Nat), next.val ≤ j ∧ list.val[j]? = some (first, second)) ↔
          (∃ (j : Nat), index.val ≤ j ∧ list.val[j]? = some (first, second))) := by
      intro differ
      constructor
      · rintro ⟨j, low, at_j⟩
        exact ⟨j, by omega, at_j⟩
      · rintro ⟨j, low, at_j⟩
        by_cases here : j = index.val
        · subst here
          rw [at_index] at at_j
          simp only [Option.some.injEq, Prod.mk.injEq] at at_j
          exact absurd at_j differ
        · exact ⟨j, by omega, at_j⟩
    by_cases fa : a = first
    · by_cases sb : b = second
      · subst fa
        subst sb
        have found : ∃ (j : Nat), index.val ≤ j ∧ list.val[j]? = some (a, b) := ⟨index.val, le_refl _, at_index⟩
        simp [found]
      · simp only [fa, sb, ↓reduceIte]
        rw [shift (fun h => sb h.2)]
    · simp only [fa, ↓reduceIte]
      rw [shift (fun h => fa h.1)]
  · have none : ¬ ∃ (j : Nat), index.val ≤ j ∧ list.val[j]? = some (first, second) := by
      rintro ⟨j, low, at_j⟩
      have := (List.getElem?_eq_some_iff.mp at_j).1
      omega
    simp [UScalar.lt_equiv, more, none]
termination_by list.val.length - index.val
decreasing_by omega

theorem has_pair_spec (list : alloc.vec.Vec (Usize × Usize)) (first second : Usize) :
    saturation.has_pair list first second = .ok (decide ((first, second) ∈ list.val)) := by
  rw [saturation.has_pair, has_pair_from_spec]
  congr 2
  apply propext
  simp [List.mem_iff_getElem?]

/-! ### Concepts, hashing and buckets -/

theorem same_concept_spec (left right : saturation.Concept) :
    saturation.same_concept left right = .ok (decide (left = right)) := by
  cases left <;> cases right <;>
    simp [saturation.same_concept, Rowl.Symbols.same_spelling_total_correct, Rowl.Tableau.class_eq_iff]
  all_goals (split <;> simp_all)

theorem mix_spec (hash value : Usize) : ∃ m, saturation.mix hash value = .ok m ∧ m.val < 4096 := by
  have nonzero : saturation.BUCKETS.val ≠ 0 := by rw [buckets_val]; omega
  obtain ⟨i, iRun, iValue⟩ := WP.spec_imp_exists (UScalar.rem_spec hash (y := saturation.BUCKETS) nonzero)
  have iLt : i.val < 4096 := by rw [iValue, buckets_val]; exact Nat.mod_lt _ (by omega)
  obtain ⟨i1, i1Run, i1Value⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := i) (y := 31#usize)
    (by have : (31#usize : Usize).val = 31 := rfl; rw [this]; scalar_tac))
  obtain ⟨i2, i2Run, i2Value⟩ := WP.spec_imp_exists (UScalar.rem_spec value (y := saturation.BUCKETS) nonzero)
  have i2Lt : i2.val < 4096 := by rw [i2Value, buckets_val]; exact Nat.mod_lt _ (by omega)
  have i1Lt : i1.val < 4096 * 31 := by
    have : (31#usize : Usize).val = 31 := rfl
    rw [i1Value, this]
    omega
  obtain ⟨i3, i3Run, i3Value⟩ := WP.spec_imp_exists (UScalar.add_spec (x := i1) (y := i2) (by scalar_tac))
  obtain ⟨m, mRun, mValue⟩ := WP.spec_imp_exists (UScalar.rem_spec i3 (y := saturation.BUCKETS) nonzero)
  refine ⟨m, ?_, by rw [mValue, buckets_val]; exact Nat.mod_lt _ (by omega)⟩
  simp [saturation.mix, iRun, i1Run, i2Run, i3Run, mRun]

theorem hash_from_spec (bytes : alloc.vec.Vec U8) (index hash : Usize) (small : hash.val < 4096) :
    ∃ h, saturation.hash_from bytes index hash = .ok h ∧ h.val < 4096 := by
  rw [saturation.hash_from]
  by_cases more : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    obtain ⟨m, mixRun, mLt⟩ := mix_spec hash (UScalar.cast .Usize bytes.val[index.val])
    obtain ⟨h, run, hLt⟩ := hash_from_spec bytes next m mLt
    exact ⟨h, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, advance, lookup, lift, mixRun, run], hLt⟩
  · exact ⟨hash, by simp [UScalar.lt_equiv, more], small⟩
termination_by bytes.val.length - index.val
decreasing_by (have := nextValue; simp at this; omega)

theorem hash_concept_spec (concept : saturation.Concept) :
    ∃ h, saturation.hash_concept concept = .ok h ∧ h.val < 4096 := by
  cases concept with
  | Top => exact ⟨1#usize, by simp [saturation.hash_concept], by decide⟩
  | Bottom => exact ⟨2#usize, by simp [saturation.hash_concept], by decide⟩
  | Atom k => simpa [saturation.hash_concept] using hash_from_spec k.iri.spelling 0#usize 7#usize (by decide)
  | And a b =>
    obtain ⟨m, mRun, _⟩ := mix_spec 3#usize a
    obtain ⟨h, hRun, hLt⟩ := mix_spec m b
    exact ⟨h, by simp [saturation.hash_concept, mRun, hRun], hLt⟩
  | Exists r f =>
    obtain ⟨m, mRun, _⟩ := mix_spec 5#usize r
    obtain ⟨h, hRun, hLt⟩ := mix_spec m f
    exact ⟨h, by simp [saturation.hash_concept, mRun, hRun], hLt⟩

theorem find_from_spec (concepts : alloc.vec.Vec saturation.Concept) (bucket : alloc.vec.Vec Usize)
    (concept : saturation.Concept) (index : Usize) :
    ∃ r, saturation.find_from concepts bucket concept index = .ok r ∧
      (∀ id, r = some id → concepts.val[id.val]? = some concept) ∧
      (r = none → ∀ (j : Nat) (id : Usize), index.val ≤ j → bucket.val[j]? = some id →
        concepts.val[id.val]? ≠ some concept) := by
  rw [saturation.find_from]
  by_cases more : index.val < bucket.val.length
  · have lookup : bucket.index_usize index = .ok bucket.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, run, found, missing⟩ := find_from_spec concepts bucket concept next
    have skip : concepts.val[bucket.val[index.val].val]? ≠ some concept →
        ∃ r, (do
          let i2 ← index + 1#usize
          saturation.find_from concepts bucket concept i2) = .ok r ∧
          (∀ id, r = some id → concepts.val[id.val]? = some concept) ∧
          (r = none → ∀ (j : Nat) (id : Usize), index.val ≤ j → bucket.val[j]? = some id →
            concepts.val[id.val]? ≠ some concept) := by
      intro differ
      refine ⟨r, by simp [advance, run], found, fun none j id low at_j => ?_⟩
      by_cases here : j = index.val
      · subst here
        rw [List.getElem?_eq_getElem more] at at_j
        cases at_j
        exact differ
      · exact missing none j id (by omega) at_j
    by_cases inside : bucket.val[index.val].val < concepts.val.length
    · have entry : concepts.index_usize bucket.val[index.val] = .ok concepts.val[bucket.val[index.val].val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      by_cases same : concepts.val[bucket.val[index.val].val] = concept
      · refine ⟨some bucket.val[index.val], ?_, ?_, by simp⟩
        · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, inside, entry, same_concept_spec, same]
        · intro id same_id
          cases same_id
          rw [List.getElem?_eq_getElem inside, same]
      · obtain ⟨r', run', found', missing'⟩ := skip (by rw [List.getElem?_eq_getElem inside]; simpa using same)
        refine ⟨r', ?_, found', missing'⟩
        simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
          lookup, bind_ok, inside, entry, same_concept_spec, same, decide_false, Bool.false_eq_true]
        exact run'
    · obtain ⟨r', run', found', missing'⟩ := skip (by rw [List.getElem?_eq_none (by omega)]; simp)
      refine ⟨r', ?_, found', missing'⟩
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        lookup, bind_ok, inside]
      exact run'
  · refine ⟨none, by simp [UScalar.lt_equiv, more], by simp, fun _ j id low at_j => ?_⟩
    have := (List.getElem?_eq_some_iff.mp at_j).1
    omega
termination_by bucket.val.length - index.val
decreasing_by omega

theorem empty_buckets_spec (out : alloc.vec.Vec (alloc.vec.Vec Usize)) (small : out.val.length ≤ 4096)
    (empty : ∀ b ∈ out.val, b.val = []) :
    ∃ r, saturation.empty_buckets out = .ok r ∧ r.val.length = 4096 ∧ ∀ b ∈ r.val, b.val = [] := by
  rw [saturation.empty_buckets]
  by_cases more : out.val.length < 4096
  · have moreU : alloc.vec.Vec.len out < saturation.BUCKETS := by
      rw [UScalar.lt_equiv, buckets_val]; simpa using more
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (alloc.vec.Vec.new Usize) (by scalar_tac))
    obtain ⟨r, run, length, all⟩ := empty_buckets_spec pushed (by rw [contents]; simp; omega) (by
      intro b member
      rw [contents] at member
      rcases List.mem_append.mp member with old | new
      · exact empty b old
      · rw [List.mem_singleton] at new; rw [new]; rfl)
    exact ⟨r, by simp [moreU, push, run], length, all⟩
  · have stop : ¬ alloc.vec.Vec.len out < saturation.BUCKETS := by
      rw [UScalar.lt_equiv, buckets_val]; simpa using more
    exact ⟨out, by simp [stop], by omega, empty⟩
termination_by 4096 - out.val.length
decreasing_by (rw [contents]; simp; omega)

/-! ### Names -/

theorem is_thing_spec (k : Class) : saturation.is_thing k = .ok (decide (k = thing)) := by
  rw [saturation.is_thing]
  simp only [Rowl.Tableau.class_eq_iff k thing]
  by_cases top : k.iri.spelling.val = thing.iri.spelling.val <;>
    simp_all [Rowl.AlcOntology.same_pattern_total, Array.to_slice, Array.make, lift, thing]

theorem is_nothing_spec (k : Class) : saturation.is_nothing k = .ok (decide (k = nothing)) := by
  rw [saturation.is_nothing]
  simp only [Rowl.Tableau.class_eq_iff k nothing]
  by_cases bottom : k.iri.spelling.val = nothing.iri.spelling.val <;>
    simp_all [Rowl.AlcOntology.same_pattern_total, Array.to_slice, Array.make, lift, nothing]

theorem builtin_role_spec (r : ObjectProperty) :
    saturation.builtin_role r = .ok (decide (r = topObject ∨ r = bottomObject)) := by
  rw [saturation.builtin_role]
  simp only [Rowl.Tableau.property_eq_iff r topObject, Rowl.Tableau.property_eq_iff r bottomObject]
  by_cases top : r.iri.spelling.val = topObject.iri.spelling.val <;>
    by_cases bottom : r.iri.spelling.val = bottomObject.iri.spelling.val <;>
    simp_all [Rowl.AlcOntology.same_pattern_total, Array.to_slice, Array.make, lift, topObject, bottomObject]

theorem copy_class_identity (k : Class) : saturation.copy_class k = .ok k := by
  cases k
  simp [saturation.copy_class, Rowl.Nnf.copy_iri_identity]

theorem copy_role_identity (r : ObjectProperty) : saturation.copy_role r = .ok r := by
  cases r
  simp [saturation.copy_role, Rowl.Nnf.copy_iri_identity]

theorem role_from_spec (roles : alloc.vec.Vec ObjectProperty) (role : ObjectProperty) (index : Usize) :
    ∃ r, saturation.role_from roles role index = .ok r ∧
      (∀ id, r = some id → roles.val[id.val]? = some role) ∧
      (r = none → ∀ (j : Nat), index.val ≤ j → roles.val[j]? ≠ some role) := by
  rw [saturation.role_from]
  by_cases more : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    by_cases same : roles.val[index.val] = role
    · refine ⟨some index, ?_, ?_, by simp⟩
      · have spelled : roles.val[index.val].iri.spelling.val = role.iri.spelling.val := by rw [same]
        simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, Rowl.Symbols.same_spelling_total_correct,
          spelled]
      · intro id same_id
        cases same_id
        rw [List.getElem?_eq_getElem more, same]
    · obtain ⟨r, run, found, missing⟩ := role_from_spec roles role next
      have spelled : roles.val[index.val].iri.spelling.val ≠ role.iri.spelling.val := fun equal =>
        same ((Rowl.Tableau.property_eq_iff _ _).mpr equal)
      refine ⟨r, ?_, found, fun none j low at_j => ?_⟩
      · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, Rowl.Symbols.same_spelling_total_correct,
          spelled, advance, run]
      · by_cases here : j = index.val
        · subst here
          rw [List.getElem?_eq_getElem more] at at_j
          exact same (Option.some.inj at_j)
        · exact missing none j (by omega) at_j
  · refine ⟨none, by simp [UScalar.lt_equiv, more], by simp, fun _ j low at_j => ?_⟩
    have := (List.getElem?_eq_some_iff.mp at_j).1
    omega
termination_by roles.val.length - index.val
decreasing_by omega

/-! ### Pushing -/

theorem push_rule_spec (rules : alloc.vec.Vec saturation.Rule) (rule : saturation.Rule) :
    ∃ r, saturation.push_rule rules rule = .ok r ∧ ∀ rules', r = some rules' → rules'.val = rules.val ++ [rule] := by
  rw [saturation.push_rule]
  by_cases room : rules.val.length < Usize.max
  · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec rules rule room)
    exact ⟨some pushed, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, push],
      fun rules' same => by cases same; exact contents⟩
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room], by simp⟩

theorem push_fact_spec (queue : alloc.vec.Vec saturation.Fact) (fact : saturation.Fact) :
    ∃ r, saturation.push_fact queue fact = .ok r ∧ ∀ queue', r = some queue' → queue'.val = queue.val ++ [fact] := by
  rw [saturation.push_fact]
  by_cases room : queue.val.length < Usize.max
  · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec queue fact room)
    exact ⟨some pushed, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, push],
      fun queue' same => by cases same; exact contents⟩
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room], by simp⟩

theorem push_item_spec (list : alloc.vec.Vec (alloc.vec.Vec Usize)) (at' item : Usize) :
    ∃ r, saturation.push_item list at' item = .ok r ∧ ∀ list', r = some list' →
      ∃ old new, list.val[at'.val]? = some old ∧ new.val = old.val ++ [item] ∧ list'.val = list.val.set at'.val new := by
  rw [saturation.push_item]
  by_cases inside : at'.val < list.val.length
  · have lookup : list.index_usize at' = .ok list.val[at'.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases room : list.val[at'.val].val.length < Usize.max
    · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec list.val[at'.val] item room)
      refine ⟨some (list.set at' pushed), ?_, fun list' same => ?_⟩
      · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, inside, lookup, room,
          alloc.vec.Vec.index_mut_usize, push]
      · cases same
        exact ⟨list.val[at'.val], pushed, List.getElem?_eq_getElem inside, contents, by
          simp [alloc.vec.Vec.set_val_eq]⟩
    · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, inside, lookup, room], by simp⟩
  · exact ⟨none, by simp [UScalar.lt_equiv, inside], by simp⟩

theorem push_pair_spec (list : alloc.vec.Vec (alloc.vec.Vec (Usize × Usize))) (at' : Usize) (pair : Usize × Usize) :
    ∃ r, saturation.push_pair list at' pair = .ok r ∧ ∀ list', r = some list' →
      ∃ old new, list.val[at'.val]? = some old ∧ new.val = old.val ++ [pair] ∧ list'.val = list.val.set at'.val new := by
  rw [saturation.push_pair]
  by_cases inside : at'.val < list.val.length
  · have lookup : list.index_usize at' = .ok list.val[at'.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases room : list.val[at'.val].val.length < Usize.max
    · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec list.val[at'.val] pair room)
      refine ⟨some (list.set at' pushed), ?_, fun list' same => ?_⟩
      · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, inside, lookup, room,
          alloc.vec.Vec.index_mut_usize, push]
      · cases same
        exact ⟨list.val[at'.val], pushed, List.getElem?_eq_getElem inside, contents, by
          simp [alloc.vec.Vec.set_val_eq]⟩
    · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, inside, lookup, room], by simp⟩
  · exact ⟨none, by simp [UScalar.lt_equiv, inside], by simp⟩

theorem empty_lists_spec (count : Usize) (out : alloc.vec.Vec (alloc.vec.Vec Usize)) (small : out.val.length ≤ count.val)
    (empty : ∀ b ∈ out.val, b.val = []) :
    ∃ r, saturation.empty_lists count out = .ok r ∧ r.val.length = count.val ∧ ∀ b ∈ r.val, b.val = [] := by
  rw [saturation.empty_lists]
  by_cases more : out.val.length < count.val
  · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (alloc.vec.Vec.new Usize) (by scalar_tac))
    obtain ⟨r, run, length, all⟩ := empty_lists_spec count pushed (by rw [contents]; simp; omega) (by
      intro b member
      rw [contents] at member
      rcases List.mem_append.mp member with old | new
      · exact empty b old
      · rw [List.mem_singleton] at new; rw [new]; rfl)
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, push, run], length, all⟩
  · exact ⟨out, by simp [UScalar.lt_equiv, more], by omega, empty⟩
termination_by count.val - out.val.length
decreasing_by (rw [contents]; simp; omega)

theorem empty_pairs_spec (count : Usize) (out : alloc.vec.Vec (alloc.vec.Vec (Usize × Usize)))
    (small : out.val.length ≤ count.val) (empty : ∀ b ∈ out.val, b.val = []) :
    ∃ r, saturation.empty_pairs count out = .ok r ∧ r.val.length = count.val ∧ ∀ b ∈ r.val, b.val = [] := by
  rw [saturation.empty_pairs]
  by_cases more : out.val.length < count.val
  · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (alloc.vec.Vec.new (Usize × Usize)) (by scalar_tac))
    obtain ⟨r, run, length, all⟩ := empty_pairs_spec count pushed (by rw [contents]; simp; omega) (by
      intro b member
      rw [contents] at member
      rcases List.mem_append.mp member with old | new
      · exact empty b old
      · rw [List.mem_singleton] at new; rw [new]; rfl)
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, push, run], length, all⟩
  · exact ⟨out, by simp [UScalar.lt_equiv, more], by omega, empty⟩
termination_by count.val - out.val.length
decreasing_by (rw [contents]; simp; omega)

theorem falses_spec (count : Usize) (out : alloc.vec.Vec Bool) (small : out.val.length ≤ count.val)
    (empty : ∀ b ∈ out.val, b = false) :
    ∃ r, saturation.falses count out = .ok r ∧ r.val.length = count.val ∧ ∀ b ∈ r.val, b = false := by
  rw [saturation.falses]
  by_cases more : out.val.length < count.val
  · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out false (by scalar_tac))
    obtain ⟨r, run, length, all⟩ := falses_spec count pushed (by rw [contents]; simp; omega) (by
      intro b member
      rw [contents] at member
      rcases List.mem_append.mp member with old | new
      · exact empty b old
      · exact List.mem_singleton.mp new)
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, push, run], length, all⟩
  · exact ⟨out, by simp [UScalar.lt_equiv, more], by omega, empty⟩
termination_by count.val - out.val.length
decreasing_by (rw [contents]; simp; omega)

/-! ### The meaning of a table -/

section Meaning
variable {Object : Type u} {Value : Type v}

/-- A role of the table relates as its named object property. -/
def rel (I : Interpretation Object Value) (roles : List ObjectProperty) (r : Nat) (x y : Object) : Prop :=
  ∃ p, roles[r]? = some p ∧ I.objectProperties p x y

/-- The meaning of a concept of the table at an element; the parts of a
    compound concept come before it. -/
def meaning (I : Interpretation Object Value) (concepts : List saturation.Concept) (roles : List ObjectProperty)
    (c : Nat) (x : Object) : Prop :=
  match concepts[c]? with
  | some .Top => True
  | some .Bottom => False
  | some (.Atom k) => I.classes k x
  | some (.And a b) =>
      (if _h : a.val < c then meaning I concepts roles a.val x else False) ∧
      (if _h : b.val < c then meaning I concepts roles b.val x else False)
  | some (.Exists r f) => ∃ y, rel I roles r.val x y ∧ (if _h : f.val < c then meaning I concepts roles f.val y else False)
  | none => False
termination_by c

end Meaning

/-- The parts of a concept come before index `bound`, its role is a role of the
    table, and an atom is no built-in class. -/
def PartsOk (bound roles : Nat) : saturation.Concept → Prop
  | .And a b => a.val < bound ∧ b.val < bound
  | .Exists r f => f.val < bound ∧ r.val < roles
  | .Atom k => k ≠ thing ∧ k ≠ nothing
  | _ => True

/-- The invariant of the concept table: every concept is in the bucket of its
    hash, no concept or role occurs twice, the parts of every concept come
    before it, and no built-in class or object property is a name. -/
structure TableOk (t : saturation.Table) : Prop where
  buckets : t.buckets.val.length = 4096
  placed : ∀ (i : Nat) c, t.concepts.val[i]? = some c → ∀ h, saturation.hash_concept c = .ok h →
    ∃ b, t.buckets.val[h.val]? = some b ∧ ∃ id ∈ b.val, id.val = i
  distinct : ∀ (i j : Nat) c, t.concepts.val[i]? = some c → t.concepts.val[j]? = some c → i = j
  parts : ∀ (i : Nat) c, t.concepts.val[i]? = some c → PartsOk i t.roles.val.length c
  rolesDistinct : ∀ (i j : Nat) p, t.roles.val[i]? = some p → t.roles.val[j]? = some p → i = j
  rolesProper : ∀ (i : Nat) p, t.roles.val[i]? = some p → p ≠ topObject ∧ p ≠ bottomObject

/-- A table extends another: both lists only grow at the end. -/
def Extends (t t' : saturation.Table) : Prop :=
  t.concepts.val <+: t'.concepts.val ∧ t.roles.val <+: t'.roles.val

theorem extends_refl (t : saturation.Table) : Extends t t := ⟨List.prefix_refl _, List.prefix_refl _⟩

theorem extends_trans {t t' t'' : saturation.Table} (a : Extends t t') (b : Extends t' t'') : Extends t t'' :=
  ⟨a.1.trans b.1, a.2.trans b.2⟩

theorem parts_mono {bound bound' roles roles' : Nat} {c : saturation.Concept} (ok : PartsOk bound roles c)
    (more : bound ≤ bound') (moreRoles : roles ≤ roles') : PartsOk bound' roles' c := by
  cases c with
  | And a b => exact ⟨by have := ok.1; omega, by have := ok.2; omega⟩
  | Exists r f => exact ⟨by have := ok.1; omega, by have := ok.2; omega⟩
  | Atom k => exact ok
  | Top => trivial
  | Bottom => trivial

theorem prefix_lookup {α : Type} {l l' : List α} (pre : l <+: l') {i : Nat} {a : α} (at_i : l[i]? = some a) :
    l'[i]? = some a := by
  obtain ⟨rest, rfl⟩ := pre
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp at_i).1]
  exact at_i

/-- The meaning of a concept stays when the table grows. -/
theorem meaning_extends {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (t t' : saturation.Table) (ok : TableOk t) (grown : Extends t t') :
    ∀ (c : Nat), c < t.concepts.val.length → ∀ x,
      meaning I t'.concepts.val t'.roles.val c x ↔ meaning I t.concepts.val t.roles.val c x := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro inside x
    have at_c : t.concepts.val[c]? = some t.concepts.val[c] := List.getElem?_eq_getElem inside
    have at_c' := prefix_lookup grown.1 at_c
    have partsOk := ok.parts c _ at_c
    rw [meaning, meaning, at_c, at_c']
    cases same : t.concepts.val[c] with
    | Top => simp
    | Bottom => simp
    | Atom k => simp
    | And a b =>
      rw [same] at partsOk
      have aLt : a.val < c := partsOk.1
      have bLt : b.val < c := partsOk.2
      simp only [dif_pos aLt, dif_pos bLt]
      rw [ih a.val aLt (by omega) x, ih b.val bLt (by omega) x]
    | Exists r f =>
      rw [same] at partsOk
      have fLt : f.val < c := partsOk.1
      simp only [dif_pos fLt]
      have role : t'.roles.val[r.val]? = t.roles.val[r.val]? :=
        prefix_lookup grown.2 (List.getElem?_eq_getElem partsOk.2) |>.trans (List.getElem?_eq_getElem partsOk.2).symm
      constructor
      · rintro ⟨y, ⟨p, at_p, edge⟩, inner⟩
        exact ⟨y, ⟨p, by rw [← role]; exact at_p, edge⟩, (ih f.val fLt (by omega) y).mp inner⟩
      · rintro ⟨y, ⟨p, at_p, edge⟩, inner⟩
        exact ⟨y, ⟨p, by rw [role]; exact at_p, edge⟩, (ih f.val fLt (by omega) y).mpr inner⟩

/-! ### Interning -/

theorem empty_table_spec : ∃ t, saturation.empty_table = .ok t ∧ TableOk t ∧ t.concepts.val = [] ∧ t.roles.val = [] := by
  obtain ⟨b, run, length, all⟩ := empty_buckets_spec (alloc.vec.Vec.new (alloc.vec.Vec Usize)) (by simp) (by simp)
  refine ⟨⟨alloc.vec.Vec.new _, b, alloc.vec.Vec.new _⟩, by simp [saturation.empty_table, run], ?_, rfl, rfl⟩
  exact {
    buckets := length
    placed := by intro i c at_i; simp at at_i
    distinct := by intro i j c at_i; simp at at_i
    parts := by intro i c at_i; simp at at_i
    rolesDistinct := by intro i j p at_i; simp at at_i
    rolesProper := by intro i p at_i; simp at at_i }

theorem intern_spec (t : saturation.Table) (ok : TableOk t) (c : saturation.Concept)
    (partsOk : PartsOk t.concepts.val.length t.roles.val.length c) :
    ∃ r, saturation.intern t c = .ok r ∧ ∀ t' id, r = some (t', id) →
      TableOk t' ∧ Extends t t' ∧ t'.concepts.val[id.val]? = some c := by
  obtain ⟨h, hashRun, hLt⟩ := hash_concept_spec c
  have hInside : h.val < t.buckets.val.length := by rw [ok.buckets]; exact hLt
  have bucketLookup : t.buckets.index_usize h = .ok t.buckets.val[h.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hInside]
  obtain ⟨found, findRun, someFound, noneFound⟩ := find_from_spec t.concepts t.buckets.val[h.val] c 0#usize
  cases found with
  | some id =>
    refine ⟨some (t, id), ?_, fun t' id' same => ?_⟩
    · simp [saturation.intern, hashRun, alloc.vec.Vec.len_val, UScalar.lt_equiv, hInside, bucketLookup, findRun]
    · simp only [Option.some.injEq, Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨ok, extends_refl _, someFound id rfl⟩
  | none =>
    have absent : ∀ (i : Nat), t.concepts.val[i]? ≠ some c := by
      intro i at_i
      obtain ⟨b, at_b, id, member, idIs⟩ := ok.placed i c at_i h hashRun
      rw [List.getElem?_eq_getElem hInside] at at_b
      cases at_b
      obtain ⟨j, at_j⟩ := List.mem_iff_getElem?.mp member
      exact noneFound rfl j id (by simp) at_j (by rw [idIs]; exact at_i)
    by_cases room : t.concepts.val.length < Usize.max
    · by_cases roomBucket : t.buckets.val[h.val].val.length < Usize.max
      · obtain ⟨concepts', pushConcepts, conceptsIs⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec t.concepts c room)
        obtain ⟨bucket', pushBucket, bucketIs⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec t.buckets.val[h.val] (alloc.vec.Vec.len t.concepts) roomBucket)
        let t' : saturation.Table := { t with concepts := concepts', buckets := t.buckets.set h bucket' }
        refine ⟨some (t', alloc.vec.Vec.len t.concepts), ?_, fun t'' id same => ?_⟩
        · simp [saturation.intern, hashRun, alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, hInside,
            bucketLookup, findRun, room, roomBucket, pushConcepts, alloc.vec.Vec.index_mut_usize, pushBucket, t']
        · simp only [Option.some.injEq, Prod.mk.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          have newAt : concepts'.val[t.concepts.val.length]? = some c := by simp [conceptsIs]
          have oldAt : ∀ (i : Nat) d, t.concepts.val[i]? = some d → concepts'.val[i]? = some d := by
            intro i d at_i
            rw [conceptsIs, List.getElem?_append_left (List.getElem?_eq_some_iff.mp at_i).1]
            exact at_i
          have lookup' : ∀ (i : Nat) d, concepts'.val[i]? = some d →
              (t.concepts.val[i]? = some d) ∨ (i = t.concepts.val.length ∧ d = c) := by
            intro i d at_i
            rw [conceptsIs] at at_i
            by_cases old : i < t.concepts.val.length
            · left; rwa [List.getElem?_append_left old] at at_i
            · right
              rw [List.getElem?_append_right (by omega)] at at_i
              have : i - t.concepts.val.length = 0 := by
                have := (List.getElem?_eq_some_iff.mp at_i).1
                simp at this
                omega
              rw [this] at at_i
              simp at at_i
              exact ⟨by have := (List.getElem?_eq_some_iff.mp (show (t.concepts.val ++ [c])[i]? = some d by
                rw [List.getElem?_append_right (by omega), this]; simp [at_i])).1; simp at this; omega, at_i.symm⟩
          refine ⟨{
            buckets := by simp [t', alloc.vec.Vec.set_val_eq, ok.buckets]
            placed := ?_
            distinct := ?_
            parts := ?_
            rolesDistinct := ok.rolesDistinct
            rolesProper := ok.rolesProper }, ⟨by rw [conceptsIs]; exact List.prefix_append _ _, List.prefix_refl _⟩,
            by simpa using newAt⟩
          · intro i d at_i h' hash'
            rcases lookup' i d at_i with old | ⟨rfl, rfl⟩
            · obtain ⟨b, at_b, id, member, idIs⟩ := ok.placed i d old h' hash'
              by_cases sameBucket : h'.val = h.val
              · refine ⟨bucket', by simp [t', alloc.vec.Vec.set_val_eq, sameBucket, hInside], id, ?_, idIs⟩
                rw [sameBucket, List.getElem?_eq_getElem hInside] at at_b
                cases at_b
                rw [bucketIs]
                exact List.mem_append_left _ member
              · refine ⟨b, ?_, id, member, idIs⟩
                simp only [t', alloc.vec.Vec.set_val_eq]
                rw [List.getElem?_set_ne (Ne.symm sameBucket)]
                exact at_b
            · have sameHash := Result.ok_injective (hashRun.symm.trans hash')
              subst sameHash
              refine ⟨bucket', by simp [t', alloc.vec.Vec.set_val_eq, hInside], alloc.vec.Vec.len t.concepts, ?_,
                by simp⟩
              rw [bucketIs]
              simp
          · intro i j d at_i at_j
            rcases lookup' i d at_i with old_i | ⟨rfl, rfl⟩
            · rcases lookup' j d at_j with old_j | ⟨rfl, rfl⟩
              · exact ok.distinct i j d old_i old_j
              · exact absurd old_i (absent i)
            · rcases lookup' j d at_j with old_j | ⟨rfl, _⟩
              · exact absurd old_j (absent j)
              · rfl
          · intro i d at_i
            rcases lookup' i d at_i with old | ⟨rfl, rfl⟩
            · exact parts_mono (ok.parts i d old) (le_refl _) (le_refl _)
            · exact partsOk
      · exact ⟨none, by simp [saturation.intern, hashRun, alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val,
          hInside, bucketLookup, findRun, room, roomBucket], by simp⟩
    · exact ⟨none, by simp [saturation.intern, hashRun, alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val,
        hInside, bucketLookup, findRun, room], by simp⟩

theorem intern_role_spec (t : saturation.Table) (ok : TableOk t) (role : ObjectProperty)
    (proper : role ≠ topObject ∧ role ≠ bottomObject) :
    ∃ r, saturation.intern_role t role = .ok r ∧ ∀ t' id, r = some (t', id) →
      TableOk t' ∧ Extends t t' ∧ t'.roles.val[id.val]? = some role := by
  obtain ⟨found, findRun, someFound, noneFound⟩ := role_from_spec t.roles role 0#usize
  cases found with
  | some id =>
    refine ⟨some (t, id), by simp [saturation.intern_role, findRun], fun t' id' same => ?_⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨ok, extends_refl _, someFound id rfl⟩
  | none =>
    have absent : ∀ (j : Nat), t.roles.val[j]? ≠ some role := fun j => noneFound rfl j (by simp)
    by_cases room : t.roles.val.length < Usize.max
    · obtain ⟨roles', push, rolesIs⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec t.roles role room)
      refine ⟨some ({ t with roles := roles' }, alloc.vec.Vec.len t.roles), ?_, fun t' id same => ?_⟩
      · simp [saturation.intern_role, findRun, alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room,
          copy_role_identity, push]
      · simp only [Option.some.injEq, Prod.mk.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        have lookup' : ∀ (i : Nat) p, roles'.val[i]? = some p →
            (t.roles.val[i]? = some p) ∨ (i = t.roles.val.length ∧ p = role) := by
          intro i p at_i
          rw [rolesIs] at at_i
          by_cases old : i < t.roles.val.length
          · left; rwa [List.getElem?_append_left old] at at_i
          · right
            have bound := (List.getElem?_eq_some_iff.mp at_i).1
            simp at bound
            have equal : i = t.roles.val.length := by omega
            subst equal
            simp at at_i
            exact ⟨rfl, at_i.symm⟩
        refine ⟨{
          buckets := ok.buckets
          placed := ok.placed
          distinct := ok.distinct
          parts := fun i c at_i => parts_mono (ok.parts i c at_i) (le_refl _) (by rw [rolesIs]; simp)
          rolesDistinct := ?_
          rolesProper := ?_ }, ⟨List.prefix_refl _, by rw [rolesIs]; exact List.prefix_append _ _⟩,
          by simp [rolesIs]⟩
        · intro i j p at_i at_j
          rcases lookup' i p at_i with old_i | ⟨rfl, rfl⟩
          · rcases lookup' j p at_j with old_j | ⟨rfl, rfl⟩
            · exact ok.rolesDistinct i j p old_i old_j
            · exact absurd old_i (absent i)
          · rcases lookup' j p at_j with old_j | ⟨rfl, _⟩
            · exact absurd old_j (absent j)
            · rfl
        · intro i p at_i
          rcases lookup' i p at_i with old | ⟨_, rfl⟩
          · exact ok.rolesProper i p old
          · exact proper
    · exact ⟨none, by simp [saturation.intern_role, findRun, alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val,
        room], by simp⟩

theorem named_role_spec (role : ObjectPropertyExpression) :
    ∃ r, saturation.named_role role = .ok r ∧ ∀ p, r = some p →
      role = .Property p ∧ p ≠ topObject ∧ p ≠ bottomObject := by
  cases role with
  | Property p =>
    by_cases builtin : p = topObject ∨ p = bottomObject
    · exact ⟨none, by simp [saturation.named_role, builtin_role_spec, builtin], by simp⟩
    · refine ⟨some p, by simp [saturation.named_role, builtin_role_spec, builtin], fun q same => ?_⟩
      cases same
      simp only [not_or] at builtin
      exact ⟨rfl, builtin⟩
  | Inverse _ => exact ⟨none, by simp [saturation.named_role], by simp⟩

/-! ### Class expressions -/

section Expressions
variable {Object : Type u} {Value : Type v}

/-- `owl:Thing` holds everywhere and `owl:Nothing` nowhere. -/
def Fixed (I : Interpretation Object Value) : Prop :=
  (∀ x, I.classes thing x) ∧ (∀ x, ¬ I.classes nothing x)

end Expressions

/-- The meaning of a concept of a table is its meaning in every later table. -/
theorem meaning_later {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    {t t' : saturation.Table} (ok : TableOk t) (grown : Extends t t') {c : Nat} (inside : c < t.concepts.val.length)
    (x : Object) :
    meaning I t'.concepts.val t'.roles.val c x ↔ meaning I t.concepts.val t.roles.val c x :=
  meaning_extends I t t' ok grown c inside x

theorem length_later {t t' : saturation.Table} (grown : Extends t t') :
    t.concepts.val.length ≤ t'.concepts.val.length := grown.1.length_le

/-- The conjunction of `members[index..]`, given that every member translates. -/
theorem conjunction_of_spec (members : alloc.vec.Vec ClassExpression)
    (good : ∀ (t : saturation.Table), TableOk t → ∀ e ∈ members.val,
      ∃ r, saturation.concept_of t e = .ok r ∧ ∀ t' c, r = some (t', c) →
        TableOk t' ∧ Extends t t' ∧ c.val < t'.concepts.val.length ∧
        ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Fixed I → ∀ x,
          meaning I t'.concepts.val t'.roles.val c.val x ↔ classDenote I e x)
    (index : Usize) (t : saturation.Table) (ok : TableOk t) :
    ∃ r, saturation.conjunction_of t members index = .ok r ∧ ∀ t' o, r = some (t', o) →
      TableOk t' ∧ Extends t t' ∧
      match o with
      | none => members.val.length ≤ index.val
      | some c => index.val < members.val.length ∧ c.val < t'.concepts.val.length ∧
          ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Fixed I → ∀ x,
            meaning I t'.concepts.val t'.roles.val c.val x ↔ ∀ e ∈ members.val.drop index.val, classDenote I e x := by
  rw [saturation.conjunction_of]
  by_cases more : index.val < members.val.length
  · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have lookup : members.index_usize index = .ok members.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have dropIs : members.val.drop index.val = members.val[index.val] :: members.val.drop (index.val + 1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨r1, run1, spec1⟩ := conjunction_of_spec members good next t ok
    cases r1 with
    | none =>
      exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, advance, run1], by simp⟩
    | some p1 =>
      obtain ⟨t1, rest⟩ := p1
      obtain ⟨ok1, grown1, restSpec⟩ := spec1 t1 rest rfl
      obtain ⟨r2, run2, spec2⟩ := good t1 ok1 members.val[index.val] (List.getElem_mem more)
      cases r2 with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, advance, run1, lookup, run2], by simp⟩
      | some p2 =>
        obtain ⟨t2, head⟩ := p2
        obtain ⟨ok2, grown2, headInside, headMeaning⟩ := spec2 t2 head rfl
        cases rest with
        | none =>
          refine ⟨some (t2, some head), by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, advance, run1, lookup,
            run2], fun t' o same => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          refine ⟨ok2, extends_trans grown1 grown2, more, headInside, fun I fixed x => ?_⟩
          have exhausted : members.val.length ≤ index.val + 1 := by simpa [nextIs] using restSpec
          have none : members.val.drop (index.val + 1) = [] := List.drop_eq_nil_iff.mpr exhausted
          rw [dropIs, none, headMeaning I fixed x]
          simp
        | some restId =>
          obtain ⟨_, restInside, restMeaning⟩ := restSpec
          have restInside2 : restId.val < t2.concepts.val.length :=
            lt_of_lt_of_le restInside (length_later grown2)
          obtain ⟨r3, run3, spec3⟩ := intern_spec t2 ok2 (.And head restId) ⟨headInside, restInside2⟩
          cases r3 with
          | none =>
            exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, advance, run1, lookup, run2, run3],
              by simp⟩
          | some p3 =>
            obtain ⟨t3, both⟩ := p3
            obtain ⟨ok3, grown3, bothAt⟩ := spec3 t3 both rfl
            refine ⟨some (t3, some both), by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, advance, run1, lookup,
              run2, run3], fun t' o same => ?_⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at same
            obtain ⟨rfl, rfl⟩ := same
            have bothInside : both.val < t3.concepts.val.length := (List.getElem?_eq_some_iff.mp bothAt).1
            refine ⟨ok3, extends_trans (extends_trans grown1 grown2) grown3, more, bothInside, fun I fixed x => ?_⟩
            have partsOk := ok3.parts both.val _ bothAt
            have headLt : head.val < both.val := partsOk.1
            have restLt : restId.val < both.val := partsOk.2
            rw [meaning, bothAt]
            simp only [dif_pos headLt, dif_pos restLt]
            rw [meaning_later I ok2 grown3 headInside, headMeaning I fixed x,
              meaning_later I ok1 (extends_trans grown2 grown3) restInside, restMeaning I fixed x, dropIs]
            rw [← nextIs]
            simp
  · refine ⟨some (t, none), by simp [UScalar.lt_equiv, more], fun t' o same => ?_⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨ok, extends_refl _, by omega⟩
termination_by members.val.length - index.val
decreasing_by omega

private theorem listN_mem_size {α : Type} [SizeOf α] {n : Nat}
    (xs : Aeneas.Data.ListN.ListN α n) {x : α} (h : x ∈ xs.toList) :
    sizeOf x < sizeOf xs := by
  induction xs with
  | nil => simp [Aeneas.Data.ListN.ListN.toList] at h
  | cons head tail ih =>
    simp only [Aeneas.Data.ListN.ListN.toList, List.mem_cons] at h
    rcases h with rfl | h
    · simp +arith
    · have := ih h
      simp only [Data.ListN.ListN.cons.sizeOf_spec]
      omega
private theorem vec_mem_size {α : Type} [SizeOf α] (xs : alloc.vec.Vec α)
    {x : α} (h : x ∈ xs.val) : sizeOf x < sizeOf xs := by
  have := listN_mem_size xs.slice.list h
  cases xs with | mk slice => cases slice; simp_all [alloc.vec.Vec.val, Slice.val]; omega
private theorem first_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.first < sizeOf xs := by
  cases xs; simp +arith
private theorem second_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.second < sizeOf xs := by
  cases xs; simp +arith
private theorem rest_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.rest < sizeOf xs := by
  cases xs; simp +arith

theorem nothing_ne_thing : nothing ≠ thing := by
  rw [Ne, Rowl.Tableau.class_eq_iff]; simp [thing, nothing]

theorem concept_of_spec_bounded : ∀ (n : Nat) (t : saturation.Table), TableOk t → ∀ (e : ClassExpression),
    sizeOf e < n →
    ∃ r, saturation.concept_of t e = .ok r ∧ ∀ t' c, r = some (t', c) →
      TableOk t' ∧ Extends t t' ∧ c.val < t'.concepts.val.length ∧
      ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Fixed I → ∀ x,
        meaning I t'.concepts.val t'.roles.val c.val x ↔ classDenote I e x := by
  intro n
  induction n with
  | zero => intro t ok e small; omega
  | succ n ih =>
    intro t ok e small
    rw [saturation.concept_of.eq_def]
    cases e with
    | Class k =>
      by_cases top : k = thing
      · obtain ⟨r, run, spec⟩ := intern_spec t ok .Top trivial
        refine ⟨r, by simp [is_thing_spec, top, run], fun t' c same => ?_⟩
        obtain ⟨ok', grown, at_c⟩ := spec t' c same
        refine ⟨ok', grown, (List.getElem?_eq_some_iff.mp at_c).1, fun I fixed x => ?_⟩
        rw [meaning, at_c, Rowl.Owl.classDenote, top]
        simp [fixed.1 x]
      · by_cases bottom : k = nothing
        · obtain ⟨r, run, spec⟩ := intern_spec t ok .Bottom trivial
          refine ⟨r, by simp [is_thing_spec, is_nothing_spec, top, bottom, nothing_ne_thing, run],
            fun t' c same => ?_⟩
          obtain ⟨ok', grown, at_c⟩ := spec t' c same
          refine ⟨ok', grown, (List.getElem?_eq_some_iff.mp at_c).1, fun I fixed x => ?_⟩
          rw [meaning, at_c, Rowl.Owl.classDenote, bottom]
          simp [fixed.2 x]
        · obtain ⟨r, run, spec⟩ := intern_spec t ok (.Atom k) ⟨top, bottom⟩
          refine ⟨r, by simp [is_thing_spec, is_nothing_spec, top, bottom, copy_class_identity, run],
            fun t' c same => ?_⟩
          obtain ⟨ok', grown, at_c⟩ := spec t' c same
          refine ⟨ok', grown, (List.getElem?_eq_some_iff.mp at_c).1, fun I fixed x => ?_⟩
          rw [meaning, at_c, Rowl.Owl.classDenote]
    | ObjectIntersectionOf members =>
      have sizeIs : sizeOf (ClassExpression.ObjectIntersectionOf members) = 1 + sizeOf members := by simp
      have restSmall := rest_size members
      have firstSmall := first_size members
      have secondSmall := second_size members
      have good : ∀ (t : saturation.Table), TableOk t → ∀ e ∈ members.rest.val,
          ∃ r, saturation.concept_of t e = .ok r ∧ ∀ t' c, r = some (t', c) →
            TableOk t' ∧ Extends t t' ∧ c.val < t'.concepts.val.length ∧
            ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Fixed I → ∀ x,
              meaning I t'.concepts.val t'.roles.val c.val x ↔ classDenote I e x := by
        intro t ok e member
        have := vec_mem_size members.rest member
        exact ih t ok e (by omega)
      obtain ⟨r1, run1, spec1⟩ := conjunction_of_spec members.rest good 0#usize t ok
      cases r1 with
      | none => exact ⟨none, by simp [run1], by simp⟩
      | some p1 =>
        obtain ⟨t1, last⟩ := p1
        obtain ⟨ok1, grown1, lastSpec⟩ := spec1 t1 last rfl
        obtain ⟨r2, run2, spec2⟩ := ih t1 ok1 members.second (by omega)
        cases r2 with
        | none => exact ⟨none, by simp [run1, run2], by simp⟩
        | some p2 =>
          obtain ⟨t2, second⟩ := p2
          obtain ⟨ok2, grown2, secondInside, secondMeaning⟩ := spec2 t2 second rfl
          obtain ⟨r3, run3, spec3⟩ := ih t2 ok2 members.first (by omega)
          cases r3 with
          | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
          | some p3 =>
            obtain ⟨t3, first⟩ := p3
            obtain ⟨ok3, grown3, firstInside, firstMeaning⟩ := spec3 t3 first rfl
            have secondInside3 : second.val < t3.concepts.val.length :=
              lt_of_lt_of_le secondInside (length_later grown3)
            cases last with
            | none =>
              obtain ⟨r4, run4, spec4⟩ := intern_spec t3 ok3 (.And first second) ⟨firstInside, secondInside3⟩
              refine ⟨r4, by simp [run1, run2, run3, run4], fun t' c same => ?_⟩
              obtain ⟨ok4, grown4, at_c⟩ := spec4 t' c same
              have partsOk := ok4.parts c.val _ at_c
              have firstLt : first.val < c.val := partsOk.1
              have secondLt : second.val < c.val := partsOk.2
              refine ⟨ok4, extends_trans (extends_trans (extends_trans grown1 grown2) grown3) grown4,
                (List.getElem?_eq_some_iff.mp at_c).1, fun I fixed x => ?_⟩
              have restEmpty : members.rest.val = [] := List.eq_nil_of_length_eq_zero (by simpa using lastSpec)
              rw [meaning, at_c, Rowl.Owl.classDenote]
              simp only [dif_pos firstLt, dif_pos secondLt]
              rw [meaning_later I ok3 grown4 firstInside, firstMeaning I fixed x,
                meaning_later I ok2 (extends_trans grown3 grown4) secondInside, secondMeaning I fixed x, restEmpty]
              simp
            | some restId =>
              obtain ⟨_, restInside, restMeaning⟩ := lastSpec
              have restInside3 : restId.val < t3.concepts.val.length :=
                lt_of_lt_of_le restInside (length_later (extends_trans grown2 grown3))
              obtain ⟨r4, run4, spec4⟩ := intern_spec t3 ok3 (.And second restId) ⟨secondInside3, restInside3⟩
              cases r4 with
              | none => exact ⟨none, by simp [run1, run2, run3, run4], by simp⟩
              | some p4 =>
                obtain ⟨t4, tail⟩ := p4
                obtain ⟨ok4, grown4, tailAt⟩ := spec4 t4 tail rfl
                have tailInside : tail.val < t4.concepts.val.length := (List.getElem?_eq_some_iff.mp tailAt).1
                have firstInside4 : first.val < t4.concepts.val.length :=
                  lt_of_lt_of_le firstInside (length_later grown4)
                obtain ⟨r5, run5, spec5⟩ := intern_spec t4 ok4 (.And first tail) ⟨firstInside4, tailInside⟩
                refine ⟨r5, by simp [run1, run2, run3, run4, run5], fun t' c same => ?_⟩
                obtain ⟨ok5, grown5, at_c⟩ := spec5 t' c same
                have partsOk := ok5.parts c.val _ at_c
                have firstLt : first.val < c.val := partsOk.1
                have tailLt : tail.val < c.val := partsOk.2
                have tailParts := ok4.parts tail.val _ tailAt
                have secondLt : second.val < tail.val := tailParts.1
                have restLt : restId.val < tail.val := tailParts.2
                refine ⟨ok5, extends_trans (extends_trans (extends_trans (extends_trans grown1 grown2) grown3) grown4)
                  grown5, (List.getElem?_eq_some_iff.mp at_c).1, fun I fixed x => ?_⟩
                have tailMeaning : meaning I t4.concepts.val t4.roles.val tail.val x ↔
                    meaning I t4.concepts.val t4.roles.val second.val x ∧
                      meaning I t4.concepts.val t4.roles.val restId.val x := by
                  rw [meaning, tailAt]
                  simp only [dif_pos secondLt, dif_pos restLt]
                rw [meaning, at_c, Rowl.Owl.classDenote]
                simp only [dif_pos firstLt, dif_pos tailLt]
                rw [meaning_later I ok4 grown5 tailInside, tailMeaning]
                rw [meaning_later I ok3 (extends_trans grown4 grown5) firstInside, firstMeaning I fixed x,
                  meaning_later I ok2 (extends_trans grown3 grown4) secondInside, secondMeaning I fixed x,
                  meaning_later I ok1 (extends_trans grown2 (extends_trans grown3 grown4)) restInside,
                  restMeaning I fixed x]
                simp
    | ObjectSomeValuesFrom role filler =>
      have fillerSmall : sizeOf filler < n := by simp at small; omega
      obtain ⟨r0, run0, spec0⟩ := named_role_spec role
      cases r0 with
      | none => exact ⟨none, by simp [run0], by simp⟩
      | some p =>
        obtain ⟨roleIs, proper⟩ := spec0 p rfl
        obtain ⟨r1, run1, spec1⟩ := ih t ok filler fillerSmall
        cases r1 with
        | none => exact ⟨none, by simp [run0, run1], by simp⟩
        | some p1 =>
          obtain ⟨t1, inner⟩ := p1
          obtain ⟨ok1, grown1, innerInside, innerMeaning⟩ := spec1 t1 inner rfl
          obtain ⟨r2, run2, spec2⟩ := intern_role_spec t1 ok1 p proper
          cases r2 with
          | none => exact ⟨none, by simp [run0, run1, run2], by simp⟩
          | some p2 =>
            obtain ⟨t2, rid⟩ := p2
            obtain ⟨ok2, grown2, ridAt⟩ := spec2 t2 rid rfl
            have innerInside2 : inner.val < t2.concepts.val.length :=
              lt_of_lt_of_le innerInside (length_later grown2)
            obtain ⟨r3, run3, spec3⟩ := intern_spec t2 ok2 (.Exists rid inner)
              ⟨innerInside2, (List.getElem?_eq_some_iff.mp ridAt).1⟩
            refine ⟨r3, by simp [run0, run1, run2, run3], fun t' c same => ?_⟩
            obtain ⟨ok3, grown3, at_c⟩ := spec3 t' c same
            have partsOk := ok3.parts c.val _ at_c
            have innerLt : inner.val < c.val := partsOk.1
            have ridAt3 : t'.roles.val[rid.val]? = some p := prefix_lookup grown3.2 ridAt
            refine ⟨ok3, extends_trans (extends_trans grown1 grown2) grown3,
              (List.getElem?_eq_some_iff.mp at_c).1, fun I fixed x => ?_⟩
            rw [meaning, at_c, Rowl.Owl.classDenote, roleIs]
            simp only [dif_pos innerLt]
            constructor
            · rintro ⟨y, ⟨q, at_q, edge⟩, inside⟩
              rw [ridAt3] at at_q
              cases at_q
              refine ⟨y, edge, ?_⟩
              rw [meaning_later I ok1 (extends_trans grown2 grown3) innerInside] at inside
              exact (innerMeaning I fixed y).mp inside
            · rintro ⟨y, edge, inside⟩
              refine ⟨y, ⟨p, ridAt3, edge⟩, ?_⟩
              rw [meaning_later I ok1 (extends_trans grown2 grown3) innerInside]
              exact (innerMeaning I fixed y).mpr inside
    | _ => exact ⟨none, by simp, by simp⟩

theorem concept_of_spec (t : saturation.Table) (ok : TableOk t) (e : ClassExpression) :
    ∃ r, saturation.concept_of t e = .ok r ∧ ∀ t' c, r = some (t', c) →
      TableOk t' ∧ Extends t t' ∧ c.val < t'.concepts.val.length ∧
      ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Fixed I → ∀ x,
        meaning I t'.concepts.val t'.roles.val c.val x ↔ classDenote I e x :=
  concept_of_spec_bounded (sizeOf e + 1) t ok e (by omega)

/-! ### Reading concepts -/

section Reading
variable {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
  {concepts : List saturation.Concept} {roles : List ObjectProperty}

theorem meaning_top {c : Nat} (at_c : concepts[c]? = some .Top) (x : Object) : meaning I concepts roles c x := by
  rw [meaning, at_c]; trivial

theorem meaning_bottom {c : Nat} (at_c : concepts[c]? = some .Bottom) (x : Object) :
    ¬ meaning I concepts roles c x := by
  rw [meaning, at_c]; simp

theorem meaning_atom {c : Nat} {k : Class} (at_c : concepts[c]? = some (.Atom k)) (x : Object) :
    meaning I concepts roles c x ↔ I.classes k x := by
  rw [meaning, at_c]

theorem meaning_and {c : Nat} {a b : Usize} (at_c : concepts[c]? = some (.And a b)) (aLt : a.val < c)
    (bLt : b.val < c) (x : Object) :
    meaning I concepts roles c x ↔ meaning I concepts roles a.val x ∧ meaning I concepts roles b.val x := by
  rw [meaning, at_c]; simp only [dif_pos aLt, dif_pos bLt]

theorem meaning_exists {c : Nat} {r f : Usize} (at_c : concepts[c]? = some (.Exists r f)) (fLt : f.val < c)
    (x : Object) :
    meaning I concepts roles c x ↔ ∃ y, rel I roles r.val x y ∧ meaning I concepts roles f.val y := by
  rw [meaning, at_c]; simp only [dif_pos fLt]

theorem rel_at {r : Nat} {p : ObjectProperty} (at_r : roles[r]? = some p) (x y : Object) :
    rel I roles r x y ↔ I.objectProperties p x y := by
  simp [rel, at_r]

end Reading

theorem rel_later {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    {t t' : saturation.Table} (grown : Extends t t') {r : Nat} (inside : r < t.roles.val.length) (x y : Object) :
    rel I t'.roles.val r x y ↔ rel I t.roles.val r x y := by
  have role : t'.roles.val[r]? = t.roles.val[r]? :=
    (prefix_lookup grown.2 (List.getElem?_eq_getElem inside)).trans (List.getElem?_eq_getElem inside).symm
  simp only [rel, role]

/-- The concept of a named class. -/
noncomputable def classConcept (k : Class) : saturation.Concept :=
  if k = thing then .Top else if k = nothing then .Bottom else .Atom k

theorem meaning_class {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (fixed : Fixed I)
    {concepts : List saturation.Concept} {roles : List ObjectProperty} {c : Nat} {k : Class}
    (at_c : concepts[c]? = some (classConcept k)) (x : Object) :
    meaning I concepts roles c x ↔ I.classes k x := by
  rw [meaning, at_c]
  by_cases top : k = thing
  · subst top; simp [classConcept, fixed.1 x]
  · by_cases bottom : k = nothing
    · subst bottom; simp [classConcept, nothing_ne_thing, fixed.2 x]
    · simp [classConcept, top, bottom]

theorem concept_of_class (t : saturation.Table) (ok : TableOk t) (k : Class) :
    ∃ r, saturation.concept_of t (.Class k) = .ok r ∧ ∀ t' c, r = some (t', c) →
      TableOk t' ∧ Extends t t' ∧ t'.concepts.val[c.val]? = some (classConcept k) := by
  rw [saturation.concept_of.eq_def]
  by_cases top : k = thing
  · obtain ⟨r, run, spec⟩ := intern_spec t ok .Top trivial
    refine ⟨r, by simp [is_thing_spec, top, run], fun t' c same => ?_⟩
    obtain ⟨ok', grown, at_c⟩ := spec t' c same
    exact ⟨ok', grown, by simp [classConcept, top, at_c]⟩
  · by_cases bottom : k = nothing
    · obtain ⟨r, run, spec⟩ := intern_spec t ok .Bottom trivial
      refine ⟨r, by simp [is_thing_spec, is_nothing_spec, top, bottom, nothing_ne_thing, run],
        fun t' c same => ?_⟩
      obtain ⟨ok', grown, at_c⟩ := spec t' c same
      exact ⟨ok', grown, by simp [classConcept, top, bottom, nothing_ne_thing, at_c]⟩
    · obtain ⟨r, run, spec⟩ := intern_spec t ok (.Atom k) ⟨top, bottom⟩
      refine ⟨r, by simp [is_thing_spec, is_nothing_spec, top, bottom, copy_class_identity, run],
        fun t' c same => ?_⟩
      obtain ⟨ok', grown, at_c⟩ := spec t' c same
      exact ⟨ok', grown, by simp [classConcept, top, bottom, at_c]⟩

/-! ### Rules -/

section Rules
variable {Object : Type u} {Value : Type v}

/-- An axiom over the table holds in an interpretation. -/
def RuleHolds (I : Interpretation Object Value) (concepts : List saturation.Concept) (roles : List ObjectProperty) :
    saturation.Rule → Prop
  | .Sub a b => ∀ x, meaning I concepts roles a.val x → meaning I concepts roles b.val x
  | .Role r s => ∀ x y, rel I roles r.val x y → rel I roles s.val x y
  | .Chain r s q => ∀ x y z, rel I roles r.val x y → rel I roles s.val y z → rel I roles q.val x z

end Rules

/-- The concepts and roles of a rule are in the table. -/
def RuleInside (t : saturation.Table) : saturation.Rule → Prop
  | .Sub a b => a.val < t.concepts.val.length ∧ b.val < t.concepts.val.length
  | .Role r s => r.val < t.roles.val.length ∧ s.val < t.roles.val.length
  | .Chain r s q => r.val < t.roles.val.length ∧ s.val < t.roles.val.length ∧ q.val < t.roles.val.length

theorem inside_later {t t' : saturation.Table} (grown : Extends t t') {rule : saturation.Rule}
    (inside : RuleInside t rule) : RuleInside t' rule := by
  have c := length_later grown
  have r : t.roles.val.length ≤ t'.roles.val.length := grown.2.length_le
  cases rule with
  | Sub a b => exact ⟨by have := inside.1; omega, by have := inside.2; omega⟩
  | Role a b => exact ⟨by have := inside.1; omega, by have := inside.2; omega⟩
  | Chain a b q => exact ⟨by have := inside.1; omega, by have := inside.2.1; omega, by have := inside.2.2; omega⟩

theorem holds_later {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    {t t' : saturation.Table} (ok : TableOk t) (grown : Extends t t') {rule : saturation.Rule}
    (inside : RuleInside t rule) :
    RuleHolds I t'.concepts.val t'.roles.val rule ↔ RuleHolds I t.concepts.val t.roles.val rule := by
  cases rule with
  | Sub a b =>
    simp only [RuleHolds]
    exact forall_congr' fun x => by rw [meaning_later I ok grown inside.1, meaning_later I ok grown inside.2]
  | Role r s =>
    simp only [RuleHolds]
    exact forall_congr' fun x => forall_congr' fun y => by
      rw [rel_later I grown inside.1, rel_later I grown inside.2]
  | Chain r s q =>
    simp only [RuleHolds]
    exact forall_congr' fun x => forall_congr' fun y => forall_congr' fun z => by
      rw [rel_later I grown inside.1, rel_later I grown inside.2.1, rel_later I grown inside.2.2]

/-! ### Lists of class expressions -/

theorem forall2_lookup {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) :
    ∀ (i : Nat) a b, xs[i]? = some a → ys[i]? = some b → R a b := by
  induction h with
  | nil => intro i a b at_a; simp at at_a
  | cons head _ ih =>
    intro i a b at_a at_b
    cases i with
    | zero => simp at at_a at_b; subst at_a; subst at_b; exact head
    | succ i => simp at at_a at_b; exact ih i a b at_a at_b

/-- `ids` are the concepts of the class expressions `es` in the table. -/
def Translated (t : saturation.Table) (ids : List Usize) (es : List ClassExpression) : Prop :=
  List.Forall₂ (fun (id : Usize) e => id.val < t.concepts.val.length ∧
    ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Fixed I → ∀ x,
      meaning I t.concepts.val t.roles.val id.val x ↔ classDenote I e x) ids es

theorem translated_later {t t' : saturation.Table} (ok : TableOk t) (grown : Extends t t') {ids : List Usize}
    {es : List ClassExpression} (before : Translated.{u,v} t ids es) : Translated.{u,v} t' ids es :=
  List.Forall₂.imp (fun id _ ⟨inside, means⟩ => ⟨lt_of_lt_of_le inside (length_later grown),
    fun I fixed x => by rw [meaning_later I ok grown inside]; exact means I fixed x⟩) before

theorem translated_lookup {t : saturation.Table} {ids : List Usize} {es : List ClassExpression}
    (translated : Translated.{u,v} t ids es) {i : Nat} {a : Usize} (at_a : ids[i]? = some a) :
    ∃ e, es[i]? = some e ∧ a.val < t.concepts.val.length ∧
      ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Fixed I → ∀ x,
        meaning I t.concepts.val t.roles.val a.val x ↔ classDenote I e x := by
  have inside : i < es.length := by
    rw [← translated.length_eq]; exact (List.getElem?_eq_some_iff.mp at_a).1
  exact ⟨es[i], List.getElem?_eq_getElem inside,
    forall2_lookup translated i a es[i] at_a (List.getElem?_eq_getElem inside)⟩

theorem translated_id {t : saturation.Table} {ids : List Usize} {es : List ClassExpression}
    (translated : Translated.{u,v} t ids es) {i : Nat} {e : ClassExpression} (at_e : es[i]? = some e) :
    ∃ a, ids[i]? = some a ∧ a.val < t.concepts.val.length ∧
      ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Fixed I → ∀ x,
        meaning I t.concepts.val t.roles.val a.val x ↔ classDenote I e x := by
  have inside : i < ids.length := by
    rw [translated.length_eq]; exact (List.getElem?_eq_some_iff.mp at_e).1
  exact ⟨ids[i], List.getElem?_eq_getElem inside,
    forall2_lookup translated i ids[i] e (List.getElem?_eq_getElem inside) at_e⟩

theorem concepts_of_spec (members : alloc.vec.Vec ClassExpression) (index : Usize) (t : saturation.Table)
    (ok : TableOk t) (out : alloc.vec.Vec Usize) (done : List ClassExpression)
    (before : Translated.{u,v} t out.val done) :
    ∃ r, saturation.concepts_of t members index out = .ok r ∧ ∀ t' out', r = some (t', out') →
      TableOk t' ∧ Extends t t' ∧ Translated.{u,v} t' out'.val (done ++ members.val.drop index.val) := by
  rw [saturation.concepts_of]
  by_cases more : index.val < members.val.length
  · have lookup : members.index_usize index = .ok members.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨r1, run1, spec1⟩ := concept_of_spec.{u,v} t ok members.val[index.val]
    cases r1 with
    | none => exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, run1], by simp⟩
    | some p1 =>
      obtain ⟨t1, id⟩ := p1
      obtain ⟨ok1, grown1, idInside, idMeaning⟩ := spec1 t1 id rfl
      by_cases room : out.val.length < Usize.max
      · obtain ⟨out1, push, outIs⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out id room)
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = index.val + 1 := by simpa using nextValue
        have now : Translated.{u,v} t1 out1.val (done ++ [members.val[index.val]]) := by
          rw [outIs]
          exact List.rel_append (translated_later ok grown1 before)
            (List.Forall₂.cons ⟨idInside, idMeaning⟩ List.Forall₂.nil)
        obtain ⟨r, run, spec⟩ := concepts_of_spec members next t1 ok1 out1 _ now
        refine ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, more, lookup, run1, room, push,
          advance, run], fun t' out' same => ?_⟩
        obtain ⟨ok', grown', after⟩ := spec t' out' same
        refine ⟨ok', extends_trans grown1 grown', ?_⟩
        rw [nextIs] at after
        rw [List.drop_eq_getElem_cons more]
        simpa using after
      · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, more, lookup, run1, room],
          by simp⟩
  · refine ⟨some (t, out), by simp [UScalar.lt_equiv, more], fun t' out' same => ?_⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    refine ⟨ok, extends_refl _, ?_⟩
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
    exact before
termination_by members.val.length - index.val
decreasing_by omega

theorem members_of_spec (t : saturation.Table) (ok : TableOk t) (first second : ClassExpression)
    (rest : alloc.vec.Vec ClassExpression) :
    ∃ r, saturation.members_of t first second rest = .ok r ∧ ∀ t' ids, r = some (t', ids) →
      TableOk t' ∧ Extends t t' ∧ Translated.{u,v} t' ids.val (first :: second :: rest.val) := by
  rw [saturation.members_of]
  obtain ⟨r1, run1, spec1⟩ := concept_of_spec.{u,v} t ok first
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some p1 =>
    obtain ⟨t1, a⟩ := p1
    obtain ⟨ok1, grown1, aInside, aMeaning⟩ := spec1 t1 a rfl
    obtain ⟨r2, run2, spec2⟩ := concept_of_spec.{u,v} t1 ok1 second
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some p2 =>
      obtain ⟨t2, b⟩ := p2
      obtain ⟨ok2, grown2, bInside, bMeaning⟩ := spec2 t2 b rfl
      obtain ⟨out, push, outIs⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec (alloc.vec.Vec.new Usize) a (by simp [usize_max_val]; scalar_tac))
      obtain ⟨out1, push1, out1Is⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out b (by rw [outIs]; simp [usize_max_val]; scalar_tac))
      have pair : out1.val = [a, b] := by rw [out1Is, outIs]; simp
      have before : Translated.{u,v} t2 out1.val [first, second] := by
        rw [pair]
        exact .cons ⟨lt_of_lt_of_le aInside (length_later grown2), fun I fixed x => by
          rw [meaning_later I ok1 grown2 aInside]; exact aMeaning I fixed x⟩ (.cons ⟨bInside, bMeaning⟩ .nil)
      obtain ⟨r, run, spec⟩ := concepts_of_spec rest 0#usize t2 ok2 out1 [first, second] before
      refine ⟨r, by simp [run1, run2, push, push1, run], fun t' ids same => ?_⟩
      obtain ⟨ok', grown', after⟩ := spec t' ids same
      exact ⟨ok', extends_trans (extends_trans grown1 grown2) grown', by simpa using after⟩

/-! ### Equivalent and disjoint classes -/

theorem equivalences_spec (rules : alloc.vec.Vec saturation.Rule) (members : alloc.vec.Vec Usize) (index : Usize) :
    ∃ r, saturation.equivalences rules members index = .ok r ∧ ∀ rules', r = some rules' →
      ∃ added, rules'.val = rules.val ++ added ∧
        (∀ rule ∈ added, ∃ (i : Nat) (a b : Usize), index.val ≤ i ∧ members.val[i]? = some a ∧ members.val[i+1]? = some b ∧
          (rule = .Sub a b ∨ rule = .Sub b a)) ∧
        (∀ (i : Nat) a b, index.val ≤ i → members.val[i]? = some a → members.val[i+1]? = some b →
          saturation.Rule.Sub a b ∈ added ∧ saturation.Rule.Sub b a ∈ added) := by
  rw [saturation.equivalences]
  by_cases more : index.val < members.val.length
  · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    by_cases more2 : next.val < members.val.length
    · have lookup : members.index_usize index = .ok members.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
      have lookup2 : members.index_usize next = .ok members.val[next.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more2]
      obtain ⟨r1, run1, spec1⟩ := push_rule_spec rules (.Sub members.val[index.val] members.val[next.val])
      cases r1 with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, advance, more2, lookup, lookup2, run1],
          by simp⟩
      | some rules1 =>
        have rules1Is := spec1 rules1 rfl
        obtain ⟨r2, run2, spec2⟩ := push_rule_spec rules1 (.Sub members.val[next.val] members.val[index.val])
        cases r2 with
        | none =>
          exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, advance, more2, lookup, lookup2, run1,
            run2], by simp⟩
        | some rules2 =>
          have rules2Is := spec2 rules2 rfl
          obtain ⟨r, run, spec⟩ := equivalences_spec rules2 members next
          refine ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, advance, more2, lookup, lookup2, run1,
            run2, run], fun rules' same => ?_⟩
          obtain ⟨added, addedIs, sound, complete⟩ := spec rules' same
          have at_a : members.val[index.val]? = some members.val[index.val] := List.getElem?_eq_getElem more
          have at_b : members.val[index.val + 1]? = some members.val[next.val] := by
            rw [← nextIs]; exact List.getElem?_eq_getElem more2
          refine ⟨.Sub members.val[index.val] members.val[next.val] ::
            .Sub members.val[next.val] members.val[index.val] :: added,
            by rw [addedIs, rules2Is, rules1Is]; simp, ?_, ?_⟩
          · intro rule member
            simp only [List.mem_cons] at member
            rcases member with rfl | rfl | member
            · exact ⟨index.val, _, _, le_refl _, at_a, at_b, Or.inl rfl⟩
            · exact ⟨index.val, _, _, le_refl _, at_a, at_b, Or.inr rfl⟩
            · obtain ⟨i, a, b, low, at_a', at_b', which⟩ := sound rule member
              exact ⟨i, a, b, by omega, at_a', at_b', which⟩
          · intro i a b low at_a' at_b'
            by_cases here : i = index.val
            · subst here
              rw [at_a] at at_a'
              rw [at_b] at at_b'
              cases at_a'; cases at_b'
              simp
            · have := complete i a b (by omega) at_a' at_b'
              exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ this.1),
                List.mem_cons_of_mem _ (List.mem_cons_of_mem _ this.2)⟩
    · refine ⟨some rules, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, advance, more2],
        fun rules' same => ?_⟩
      cases same
      refine ⟨[], by simp, by simp, fun i a b low at_a at_b => ?_⟩
      have := (List.getElem?_eq_some_iff.mp at_b).1
      omega
  · refine ⟨some rules, by simp [UScalar.lt_equiv, more], fun rules' same => ?_⟩
    cases same
    refine ⟨[], by simp, by simp, fun i a b low at_a at_b => ?_⟩
    have := (List.getElem?_eq_some_iff.mp at_a).1
    omega
termination_by members.val.length - index.val
decreasing_by omega

/-- Equal images of neighbours make all images equal. -/
theorem chain_equal {α : Type} {β : Sort _} (xs : List α) (f : α → β)
    (step : ∀ (i : Nat) a b, xs[i]? = some a → xs[i+1]? = some b → f a = f b) :
    ∀ a ∈ xs, ∀ b ∈ xs, f a = f b := by
  have toFirst : ∀ (i : Nat) a, xs[i]? = some a → ∀ z, xs[0]? = some z → f a = f z := by
    intro i
    induction i with
    | zero => intro a at_a z at_z; rw [at_a] at at_z; cases at_z; rfl
    | succ i ih =>
      intro a at_a z at_z
      have inside : i < xs.length := by have := (List.getElem?_eq_some_iff.mp at_a).1; omega
      rw [← ih xs[i] (List.getElem?_eq_getElem inside) z at_z]
      exact (step i xs[i] a (List.getElem?_eq_getElem inside) at_a).symm
  intro a aIn b bIn
  obtain ⟨i, at_a⟩ := List.mem_iff_getElem?.mp aIn
  obtain ⟨j, at_b⟩ := List.mem_iff_getElem?.mp bIn
  have nonempty : 0 < xs.length := List.length_pos_of_mem aIn
  rw [toFirst i a at_a xs[0] (List.getElem?_eq_getElem nonempty),
    toFirst j b at_b xs[0] (List.getElem?_eq_getElem nonempty)]

theorem equivalences_meaning {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (fixed : Fixed I)
    (t : saturation.Table) (ids : List Usize) (es : List ClassExpression) (translated : Translated.{u,v} t ids es)
    (added : List saturation.Rule)
    (sound : ∀ rule ∈ added, ∃ (i : Nat) (a b : Usize), 0 ≤ i ∧ ids[i]? = some a ∧ ids[i+1]? = some b ∧
      (rule = .Sub a b ∨ rule = .Sub b a))
    (complete : ∀ (i : Nat) a b, 0 ≤ i → ids[i]? = some a → ids[i+1]? = some b →
      saturation.Rule.Sub a b ∈ added ∧ saturation.Rule.Sub b a ∈ added) :
    Rowl.Owl.allEqual es (classDenote I) ↔ ∀ rule ∈ added, RuleHolds I t.concepts.val t.roles.val rule := by
  constructor
  · intro equal rule member
    obtain ⟨i, a, b, _, at_a, at_b, which⟩ := sound rule member
    obtain ⟨e, at_e, _, aMeans⟩ := translated_lookup translated at_a
    obtain ⟨e', at_e', _, bMeans⟩ := translated_lookup translated at_b
    have same := equal e (List.mem_of_getElem? at_e) e' (List.mem_of_getElem? at_e')
    have both : ∀ x, meaning I t.concepts.val t.roles.val a.val x ↔ meaning I t.concepts.val t.roles.val b.val x := by
      intro x; rw [aMeans I fixed x, bMeans I fixed x, same]
    rcases which with rfl | rfl
    · exact fun x => (both x).mp
    · exact fun x => (both x).mpr
  · intro holds
    apply chain_equal
    intro i e e' at_e at_e'
    obtain ⟨a, at_a, _, aMeans⟩ := translated_id translated at_e
    obtain ⟨b, at_b, _, bMeans⟩ := translated_id translated at_e'
    obtain ⟨forward, backward⟩ := complete i a b (Nat.zero_le _) at_a at_b
    have there := holds _ forward
    have back := holds _ backward
    simp only [RuleHolds] at there back
    funext x
    apply propext
    rw [← aMeans I fixed x, ← bMeans I fixed x]
    exact ⟨there x, back x⟩

theorem disjoint_pairs_spec (members : alloc.vec.Vec Usize) (bottom : Usize) (index other : Usize)
    (t : saturation.Table) (ok : TableOk t) (rules : alloc.vec.Vec saturation.Rule)
    (inside : ∀ id ∈ members.val, id.val < t.concepts.val.length)
    (bottomAt : t.concepts.val[bottom.val]? = some .Bottom) (order : index.val < other.val) :
    ∃ r, saturation.disjoint_pairs t rules members bottom index other = .ok r ∧ ∀ t' rules', r = some (t', rules') →
      TableOk t' ∧ Extends t t' ∧ ∃ added, rules'.val = rules.val ++ added ∧ (∀ rule ∈ added, RuleInside t' rule) ∧
        ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value),
          ((∀ rule ∈ added, RuleHolds I t'.concepts.val t'.roles.val rule) ↔
            ∀ (i j : Nat) a b, members.val[i]? = some a → members.val[j]? = some b → i < j →
              (index.val < i ∨ (i = index.val ∧ other.val ≤ j)) →
              ∀ x, ¬ (meaning I t.concepts.val t.roles.val a.val x ∧ meaning I t.concepts.val t.roles.val b.val x)) := by
  rw [saturation.disjoint_pairs]
  by_cases more : index.val < members.val.length
  · by_cases more2 : other.val < members.val.length
    · have lookup : members.index_usize index = .ok members.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
      have lookup2 : members.index_usize other = .ok members.val[other.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more2]
      have aInside := inside _ (List.getElem_mem more)
      have bInside := inside _ (List.getElem_mem more2)
      obtain ⟨r1, run1, spec1⟩ := intern_spec t ok (.And members.val[index.val] members.val[other.val])
        ⟨aInside, bInside⟩
      cases r1 with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, more2, lookup, lookup2, run1], by simp⟩
      | some p1 =>
        obtain ⟨t1, both⟩ := p1
        obtain ⟨ok1, grown1, bothAt⟩ := spec1 t1 both rfl
        obtain ⟨r2, run2, spec2⟩ := push_rule_spec rules (.Sub both bottom)
        cases r2 with
        | none =>
          exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, more2, lookup, lookup2, run1, run2],
            by simp⟩
        | some rules1 =>
          have rules1Is := spec2 rules1 rfl
          obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := other) (y := 1#usize) (by scalar_tac))
          have nextIs : next.val = other.val + 1 := by simpa using nextValue
          have inside1 : ∀ id ∈ members.val, id.val < t1.concepts.val.length :=
            fun id m => lt_of_lt_of_le (inside id m) (length_later grown1)
          obtain ⟨r, run, spec⟩ := disjoint_pairs_spec members bottom index next t1 ok1 rules1 inside1
            (prefix_lookup grown1.1 bottomAt) (by omega)
          refine ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, more2, lookup, lookup2, run1, run2,
            advance, run], fun t' rules' same => ?_⟩
          obtain ⟨ok', grown', added, addedIs, addedInside, addedMeaning⟩ := spec t' rules' same
          have bothInside : both.val < t1.concepts.val.length := (List.getElem?_eq_some_iff.mp bothAt).1
          have bottomInside : bottom.val < t.concepts.val.length := (List.getElem?_eq_some_iff.mp bottomAt).1
          refine ⟨ok', extends_trans grown1 grown', .Sub both bottom :: added, by rw [addedIs, rules1Is]; simp, ?_,
            fun I => ?_⟩
          · intro rule member
            rcases List.mem_cons.mp member with rfl | member
            · exact inside_later grown' ⟨bothInside, lt_of_lt_of_le bottomInside (length_later grown1)⟩
            · exact addedInside rule member
          · have partsOk := ok1.parts both.val _ bothAt
            have aLt : members.val[index.val].val < both.val := partsOk.1
            have bLt : members.val[other.val].val < both.val := partsOk.2
            have later : ∀ id ∈ members.val, ∀ x,
                meaning I t1.concepts.val t1.roles.val id.val x ↔ meaning I t.concepts.val t.roles.val id.val x :=
              fun id m x => meaning_later I ok grown1 (inside id m) x
            have pairMeaning : RuleHolds I t'.concepts.val t'.roles.val (.Sub both bottom) ↔
                ∀ x, ¬ (meaning I t.concepts.val t.roles.val members.val[index.val].val x ∧
                  meaning I t.concepts.val t.roles.val members.val[other.val].val x) := by
              simp only [RuleHolds]
              refine forall_congr' fun x => ?_
              rw [meaning_later I ok1 grown' bothInside, meaning_later I ok (extends_trans grown1 grown') bottomInside,
                meaning_and I bothAt aLt bLt, later _ (List.getElem_mem more), later _ (List.getElem_mem more2)]
              have := meaning_bottom I (roles := t.roles.val) bottomAt x
              constructor
              · intro holds both; exact this (holds both)
              · intro holds both; exact absurd both holds
            rw [List.forall_mem_cons, pairMeaning, addedMeaning I]
            constructor
            · rintro ⟨pair, rest⟩ i j a b at_a at_b lt pending x
              by_cases here : i = index.val ∧ j = other.val
              · obtain ⟨rfl, rfl⟩ := here
                rw [List.getElem?_eq_getElem more] at at_a
                rw [List.getElem?_eq_getElem more2] at at_b
                cases at_a; cases at_b
                exact pair x
              · have pending' : index.val < i ∨ (i = index.val ∧ next.val ≤ j) := by omega
                intro both
                exact rest i j a b at_a at_b lt pending' x
                  ⟨(later a (List.mem_of_getElem? at_a) x).mpr both.1, (later b (List.mem_of_getElem? at_b) x).mpr both.2⟩
            · intro all
              refine ⟨all index.val other.val _ _ (List.getElem?_eq_getElem more) (List.getElem?_eq_getElem more2)
                order (Or.inr ⟨rfl, le_refl _⟩), fun i j a b at_a at_b lt pending x both => ?_⟩
              exact all i j a b at_a at_b lt (by omega) x
                ⟨(later a (List.mem_of_getElem? at_a) x).mp both.1, (later b (List.mem_of_getElem? at_b) x).mp both.2⟩
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      by_cases room : next.val < Usize.max
      · obtain ⟨after, advance2, afterValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := next) (y := 1#usize) (by scalar_tac))
        have afterIs : after.val = next.val + 1 := by simpa using afterValue
        obtain ⟨r, run, spec⟩ := disjoint_pairs_spec members bottom next after t ok rules inside bottomAt (by omega)
        refine ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, more, more2, advance, room,
          advance2, run], fun t' rules' same => ?_⟩
        obtain ⟨ok', grown', added, addedIs, addedInside, addedMeaning⟩ := spec t' rules' same
        refine ⟨ok', grown', added, addedIs, addedInside, fun I => ?_⟩
        rw [addedMeaning I]
        constructor
        · intro all i j a b at_a at_b lt pending
          have := (List.getElem?_eq_some_iff.mp at_b).1
          exact all i j a b at_a at_b lt (by omega)
        · intro all i j a b at_a at_b lt pending
          exact all i j a b at_a at_b lt (by omega)
      · refine ⟨some (t, rules), by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, more, more2,
          advance, room], fun t' rules' same => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        refine ⟨ok, extends_refl _, [], by simp, by simp, fun I => ?_⟩
        simp only [List.not_mem_nil, false_imp_iff, imp_true_iff, true_iff]
        intro i j a b at_a at_b lt pending
        have := (List.getElem?_eq_some_iff.mp at_b).1
        have := members.property
        omega
  · refine ⟨some (t, rules), by simp [UScalar.lt_equiv, more], fun t' rules' same => ?_⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    refine ⟨ok, extends_refl _, [], by simp, by simp, fun I => ?_⟩
    simp only [List.not_mem_nil, false_imp_iff, imp_true_iff, true_iff]
    intro i j a b at_a at_b lt pending
    have := (List.getElem?_eq_some_iff.mp at_b).1
    omega
termination_by (members.val.length - index.val, members.val.length + 1 - other.val)
decreasing_by all_goals (simp_wf; omega)

theorem disjoint_meaning {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (fixed : Fixed I)
    (t : saturation.Table) (ids : List Usize) (es : List ClassExpression) (translated : Translated.{u,v} t ids es) :
    Rowl.Owl.pairwiseDisjoint es (classDenote I) ↔
      ∀ (i j : Nat) a b, ids[i]? = some a → ids[j]? = some b → i < j → (0 < i ∨ (i = 0 ∧ 1 ≤ j)) →
        ∀ x, ¬ (meaning I t.concepts.val t.roles.val a.val x ∧ meaning I t.concepts.val t.roles.val b.val x) := by
  rw [Rowl.Owl.pairwiseDisjoint, List.pairwise_iff_getElem]
  constructor
  · intro disjoint i j a b at_a at_b lt _ x both
    obtain ⟨e, at_e, _, aMeans⟩ := translated_lookup translated at_a
    obtain ⟨e', at_e', _, bMeans⟩ := translated_lookup translated at_b
    have iIn := (List.getElem?_eq_some_iff.mp at_e)
    have jIn := (List.getElem?_eq_some_iff.mp at_e')
    have := disjoint i j iIn.1 jIn.1 lt x
    rw [iIn.2, jIn.2] at this
    exact this ⟨(aMeans I fixed x).mp both.1, (bMeans I fixed x).mp both.2⟩
  · intro disjoint i j iIn jIn lt x both
    obtain ⟨a, at_a, _, aMeans⟩ := translated_id translated (List.getElem?_eq_getElem iIn)
    obtain ⟨b, at_b, _, bMeans⟩ := translated_id translated (List.getElem?_eq_getElem jIn)
    exact disjoint i j a b at_a at_b lt (by omega) x ⟨(aMeans I fixed x).mpr both.1, (bMeans I fixed x).mpr both.2⟩

/-! ### Axioms -/

/-- What translating an axiom gives: a grown table and added rules inside it
    that hold exactly when the axiom does. -/
def AxiomTranslated (t : saturation.Table) (rules : alloc.vec.Vec saturation.Rule) (ax : Axiom)
    (t' : saturation.Table) (rules' : alloc.vec.Vec saturation.Rule) : Prop :=
  TableOk t' ∧ Extends t t' ∧ ∃ added, rules'.val = rules.val ++ added ∧ (∀ rule ∈ added, RuleInside t' rule) ∧
    ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Fixed I →
      (satisfies I ax ↔ ∀ rule ∈ added, RuleHolds I t'.concepts.val t'.roles.val rule)

theorem unchanged_translated (t : saturation.Table) (ok : TableOk t) (rules : alloc.vec.Vec saturation.Rule)
    (ax : Axiom) (holds : ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), satisfies I ax) :
    ∀ t' rules', some (t, rules) = some (t', rules') → AxiomTranslated.{u,v} t rules ax t' rules' := by
  intro t' rules' same
  simp only [Option.some.injEq, Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  exact ⟨ok, extends_refl _, [], by simp, by simp, fun I _ => by simp [holds I]⟩

theorem translate_axiom_spec (t : saturation.Table) (ok : TableOk t) (rules : alloc.vec.Vec saturation.Rule)
    (ax : Axiom) (top bottom : Usize) (topAt : t.concepts.val[top.val]? = some .Top)
    (bottomAt : t.concepts.val[bottom.val]? = some .Bottom) :
    ∃ r, saturation.translate_axiom t rules ax top bottom = .ok r ∧ ∀ t' rules', r = some (t', rules') →
      AxiomTranslated.{u,v} t rules ax t' rules' := by
  rw [saturation.translate_axiom.eq_def]
  cases ax with
  | Declaration _ => exact ⟨_, rfl, unchanged_translated t ok rules _ (fun I => by simp [satisfies])⟩
  | AnnotationAssertion _ _ _ => exact ⟨_, rfl, unchanged_translated t ok rules _ (fun I => by simp [satisfies])⟩
  | SubAnnotationPropertyOf _ _ => exact ⟨_, rfl, unchanged_translated t ok rules _ (fun I => by simp [satisfies])⟩
  | AnnotationPropertyDomain _ _ => exact ⟨_, rfl, unchanged_translated t ok rules _ (fun I => by simp [satisfies])⟩
  | AnnotationPropertyRange _ _ => exact ⟨_, rfl, unchanged_translated t ok rules _ (fun I => by simp [satisfies])⟩
  | SubClassOf sub sup =>
    obtain ⟨r1, run1, spec1⟩ := concept_of_spec.{u,v} t ok sub
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some p1 =>
      obtain ⟨t1, a⟩ := p1
      obtain ⟨ok1, grown1, aInside, aMeaning⟩ := spec1 t1 a rfl
      obtain ⟨r2, run2, spec2⟩ := concept_of_spec.{u,v} t1 ok1 sup
      cases r2 with
      | none => exact ⟨none, by simp [run1, run2], by simp⟩
      | some p2 =>
        obtain ⟨t2, b⟩ := p2
        obtain ⟨ok2, grown2, bInside, bMeaning⟩ := spec2 t2 b rfl
        obtain ⟨r3, run3, spec3⟩ := push_rule_spec rules (.Sub a b)
        cases r3 with
        | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
        | some rules1 =>
          refine ⟨some (t2, rules1), by simp [run1, run2, run3], fun t' rules' same => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          refine ⟨ok2, extends_trans grown1 grown2, [.Sub a b], spec3 _ rfl, ?_, fun I fixed => ?_⟩
          · intro rule member
            rw [List.mem_singleton] at member
            subst member
            exact ⟨lt_of_lt_of_le aInside (length_later grown2), bInside⟩
          · simp only [List.mem_singleton, forall_eq, RuleHolds, satisfies]
            refine forall_congr' fun x => ?_
            rw [meaning_later I ok1 grown2 aInside, aMeaning I fixed x, bMeaning I fixed x]
  | EquivalentClasses members =>
    obtain ⟨r1, run1, spec1⟩ := members_of_spec.{u,v} t ok members.first members.second members.rest
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some p1 =>
      obtain ⟨t1, ids⟩ := p1
      obtain ⟨ok1, grown1, translated⟩ := spec1 t1 ids rfl
      obtain ⟨r2, run2, spec2⟩ := equivalences_spec rules ids 0#usize
      cases r2 with
      | none => exact ⟨none, by simp [run1, run2], by simp⟩
      | some rules1 =>
        obtain ⟨added, addedIs, sound, complete⟩ := spec2 rules1 rfl
        refine ⟨some (t1, rules1), by simp [run1, run2], fun t' rules' same => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        refine ⟨ok1, grown1, added, addedIs, ?_, fun I fixed => ?_⟩
        · intro rule member
          obtain ⟨i, a, b, _, at_a, at_b, which⟩ := sound rule member
          obtain ⟨_, _, aInside, _⟩ := translated_lookup translated at_a
          obtain ⟨_, _, bInside, _⟩ := translated_lookup translated at_b
          rcases which with rfl | rfl
          · exact ⟨aInside, bInside⟩
          · exact ⟨bInside, aInside⟩
        · simp only [satisfies]
          exact equivalences_meaning I fixed t1 ids.val _ translated added sound complete
  | DisjointClasses members =>
    obtain ⟨r1, run1, spec1⟩ := members_of_spec.{u,v} t ok members.first members.second members.rest
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some p1 =>
      obtain ⟨t1, ids⟩ := p1
      obtain ⟨ok1, grown1, translated⟩ := spec1 t1 ids rfl
      have inside : ∀ id ∈ ids.val, id.val < t1.concepts.val.length := by
        intro id member
        obtain ⟨i, at_i⟩ := List.mem_iff_getElem?.mp member
        obtain ⟨_, _, idInside, _⟩ := translated_lookup translated at_i
        exact idInside
      obtain ⟨r, run, spec⟩ := disjoint_pairs_spec.{u,v} ids bottom 0#usize 1#usize t1 ok1 rules inside
        (prefix_lookup grown1.1 bottomAt) (by simp)
      refine ⟨r, by simp [run1, run], fun t' rules' same => ?_⟩
      obtain ⟨ok', grown', added, addedIs, addedInside, addedMeaning⟩ := spec t' rules' same
      refine ⟨ok', extends_trans grown1 grown', added, addedIs, addedInside, fun I fixed => ?_⟩
      simp only [satisfies]
      rw [addedMeaning I, show members.elements = members.first :: members.second :: members.rest.val from rfl,
        disjoint_meaning I fixed t1 ids.val _ translated]
      simp
  | ObjectPropertyDomain role c =>
    obtain ⟨r0, run0, spec0⟩ := named_role_spec role
    cases r0 with
    | none => exact ⟨none, by simp [run0], by simp⟩
    | some p =>
      obtain ⟨roleIs, proper⟩ := spec0 p rfl
      subst roleIs
      obtain ⟨r1, run1, spec1⟩ := intern_role_spec t ok p proper
      cases r1 with
      | none => exact ⟨none, by simp [run0, run1], by simp⟩
      | some p1 =>
        obtain ⟨t1, rid⟩ := p1
        obtain ⟨ok1, grown1, ridAt⟩ := spec1 t1 rid rfl
        have topInside : top.val < t1.concepts.val.length :=
          lt_of_lt_of_le (List.getElem?_eq_some_iff.mp topAt).1 (length_later grown1)
        obtain ⟨r2, run2, spec2⟩ := intern_spec t1 ok1 (.Exists rid top)
          ⟨topInside, (List.getElem?_eq_some_iff.mp ridAt).1⟩
        cases r2 with
        | none => exact ⟨none, by simp [run0, run1, run2], by simp⟩
        | some p2 =>
          obtain ⟨t2, some1⟩ := p2
          obtain ⟨ok2, grown2, someAt⟩ := spec2 t2 some1 rfl
          obtain ⟨r3, run3, spec3⟩ := concept_of_spec.{u,v} t2 ok2 c
          cases r3 with
          | none => exact ⟨none, by simp [run0, run1, run2, run3], by simp⟩
          | some p3 =>
            obtain ⟨t3, d⟩ := p3
            obtain ⟨ok3, grown3, dInside, dMeaning⟩ := spec3 t3 d rfl
            obtain ⟨r4, run4, spec4⟩ := push_rule_spec rules (.Sub some1 d)
            cases r4 with
            | none => exact ⟨none, by simp [run0, run1, run2, run3, run4], by simp⟩
            | some rules1 =>
              refine ⟨some (t3, rules1), by simp [run0, run1, run2, run3, run4], fun t' rules' same => ?_⟩
              simp only [Option.some.injEq, Prod.mk.injEq] at same
              obtain ⟨rfl, rfl⟩ := same
              have someInside : some1.val < t2.concepts.val.length := (List.getElem?_eq_some_iff.mp someAt).1
              refine ⟨ok3, extends_trans (extends_trans grown1 grown2) grown3, [.Sub some1 d], spec4 _ rfl, ?_,
                fun I fixed => ?_⟩
              · intro rule member
                rw [List.mem_singleton] at member
                subst member
                exact ⟨lt_of_lt_of_le someInside (length_later grown3), dInside⟩
              · simp only [List.mem_singleton, forall_eq, RuleHolds, satisfies, objectRelation]
                have partsOk := ok2.parts some1.val _ someAt
                have topLt : top.val < some1.val := partsOk.1
                have topAt2 : t2.concepts.val[top.val]? = some .Top :=
                  prefix_lookup (extends_trans grown1 grown2).1 topAt
                have ridAt2 : t2.roles.val[rid.val]? = some p := prefix_lookup grown2.2 ridAt
                constructor
                · intro holds x
                  rw [meaning_later I ok2 grown3 someInside, meaning_exists I someAt topLt, dMeaning I fixed x]
                  rintro ⟨y, edge, _⟩
                  exact holds x y ((rel_at I ridAt2 x y).mp edge)
                · intro holds x y edge
                  have := holds x
                  rw [meaning_later I ok2 grown3 someInside, meaning_exists I someAt topLt, dMeaning I fixed x] at this
                  exact this ⟨y, (rel_at I ridAt2 x y).mpr edge, meaning_top I topAt2 y⟩
  | SubObjectPropertyOf sub sup =>
    obtain ⟨r0, run0, spec0⟩ := named_role_spec sup
    cases r0 with
    | none => exact ⟨none, by simp [run0], by simp⟩
    | some q =>
      obtain ⟨supIs, qProper⟩ := spec0 q rfl
      subst supIs
      obtain ⟨r1, run1, spec1⟩ := intern_role_spec t ok q qProper
      cases r1 with
      | none => exact ⟨none, by simp [run0, run1], by simp⟩
      | some p1 =>
        obtain ⟨t1, s⟩ := p1
        obtain ⟨ok1, grown1, sAt⟩ := spec1 t1 s rfl
        cases sub with
        | Single role =>
          obtain ⟨r2, run2, spec2⟩ := named_role_spec role
          cases r2 with
          | none => exact ⟨none, by simp [run0, run1, run2], by simp⟩
          | some p =>
            obtain ⟨roleIs, pProper⟩ := spec2 p rfl
            subst roleIs
            obtain ⟨r3, run3, spec3⟩ := intern_role_spec t1 ok1 p pProper
            cases r3 with
            | none => exact ⟨none, by simp [run0, run1, run2, run3], by simp⟩
            | some p3 =>
              obtain ⟨t2, r⟩ := p3
              obtain ⟨ok2, grown2, rAt⟩ := spec3 t2 r rfl
              obtain ⟨r4, run4, spec4⟩ := push_rule_spec rules (.Role r s)
              cases r4 with
              | none => exact ⟨none, by simp [run0, run1, run2, run3, run4], by simp⟩
              | some rules1 =>
                refine ⟨some (t2, rules1), by simp [run0, run1, run2, run3, run4], fun t' rules' same => ?_⟩
                simp only [Option.some.injEq, Prod.mk.injEq] at same
                obtain ⟨rfl, rfl⟩ := same
                have sAt2 := prefix_lookup grown2.2 sAt
                refine ⟨ok2, extends_trans grown1 grown2, [.Role r s], spec4 _ rfl, ?_, fun I fixed => ?_⟩
                · intro rule member
                  rw [List.mem_singleton] at member
                  subst member
                  exact ⟨(List.getElem?_eq_some_iff.mp rAt).1, (List.getElem?_eq_some_iff.mp sAt2).1⟩
                · simp only [List.mem_singleton, forall_eq, RuleHolds, satisfies, Rowl.Owl.subRelation,
                    objectRelation, rel_at I rAt, rel_at I sAt2]
        | Chain chain =>
          by_cases single : chain.rest.val.length = 0
          · have lenZero : alloc.vec.Vec.len chain.rest = 0#usize := UScalar.eq_of_val_eq (by simp [single])
            have restNil : chain.rest.val = [] := List.eq_nil_of_length_eq_zero single
            obtain ⟨r2, run2, spec2⟩ := named_role_spec chain.first
            cases r2 with
            | none => exact ⟨none, by simp [run0, run1, lenZero, run2], by simp⟩
            | some p =>
              obtain ⟨firstIs, pProper⟩ := spec2 p rfl
              obtain ⟨r3, run3, spec3⟩ := named_role_spec chain.second
              cases r3 with
              | none => exact ⟨none, by simp [run0, run1, lenZero, run2, run3], by simp⟩
              | some p' =>
                obtain ⟨secondIs, pProper'⟩ := spec3 p' rfl
                obtain ⟨r4, run4, spec4⟩ := intern_role_spec t1 ok1 p pProper
                cases r4 with
                | none => exact ⟨none, by simp [run0, run1, lenZero, run2, run3, run4], by simp⟩
                | some p4 =>
                  obtain ⟨t2, r1⟩ := p4
                  obtain ⟨ok2, grown2, r1At⟩ := spec4 t2 r1 rfl
                  obtain ⟨r5, run5, spec5⟩ := intern_role_spec t2 ok2 p' pProper'
                  cases r5 with
                  | none => exact ⟨none, by simp [run0, run1, lenZero, run2, run3, run4, run5], by simp⟩
                  | some p5 =>
                    obtain ⟨t3, r2⟩ := p5
                    obtain ⟨ok3, grown3, r2At⟩ := spec5 t3 r2 rfl
                    obtain ⟨r6, run6, spec6⟩ := push_rule_spec rules (.Chain r1 r2 s)
                    cases r6 with
                    | none => exact ⟨none, by simp [run0, run1, lenZero, run2, run3, run4, run5, run6], by simp⟩
                    | some rules1 =>
                      refine ⟨some (t3, rules1), by simp [run0, run1, lenZero, run2, run3, run4, run5, run6],
                        fun t' rules' same => ?_⟩
                      simp only [Option.some.injEq, Prod.mk.injEq] at same
                      obtain ⟨rfl, rfl⟩ := same
                      have sAt3 := prefix_lookup (extends_trans grown2 grown3).2 sAt
                      have r1At3 := prefix_lookup grown3.2 r1At
                      refine ⟨ok3, extends_trans (extends_trans grown1 grown2) grown3, [.Chain r1 r2 s], spec6 _ rfl,
                        ?_, fun I fixed => ?_⟩
                      · intro rule member
                        rw [List.mem_singleton] at member
                        subst member
                        exact ⟨(List.getElem?_eq_some_iff.mp r1At3).1, (List.getElem?_eq_some_iff.mp r2At).1,
                          (List.getElem?_eq_some_iff.mp sAt3).1⟩
                      · simp only [List.mem_singleton, forall_eq, RuleHolds, satisfies, Rowl.Owl.subRelation,
                          AtLeastTwo.elements, restNil, firstIs, secondIs, Rowl.Owl.chainRelation, objectRelation,
                          rel_at I r1At3, rel_at I r2At, rel_at I sAt3]
                        constructor
                        · intro holds x y z first second
                          exact holds x z ⟨y, first, z, second, rfl⟩
                        · rintro holds x y ⟨z, first, w, second, rfl⟩
                          exact holds x z w first second
          · have lenNonzero : ¬ alloc.vec.Vec.len chain.rest = 0#usize := fun same =>
              single (by simpa using congrArg UScalar.val same)
            exact ⟨none, by simp [run0, run1, lenNonzero], by simp⟩
  | EquivalentObjectProperties members =>
    by_cases single : members.rest.val.length = 0
    · have lenZero : alloc.vec.Vec.len members.rest = 0#usize := UScalar.eq_of_val_eq (by simp [single])
      have restNil : members.rest.val = [] := List.eq_nil_of_length_eq_zero single
      obtain ⟨r0, run0, spec0⟩ := named_role_spec members.first
      cases r0 with
      | none => exact ⟨none, by simp [lenZero, run0], by simp⟩
      | some p =>
        obtain ⟨firstIs, pProper⟩ := spec0 p rfl
        obtain ⟨r1, run1, spec1⟩ := named_role_spec members.second
        cases r1 with
        | none => exact ⟨none, by simp [lenZero, run0, run1], by simp⟩
        | some q =>
          obtain ⟨secondIs, qProper⟩ := spec1 q rfl
          obtain ⟨r2, run2, spec2⟩ := intern_role_spec t ok p pProper
          cases r2 with
          | none => exact ⟨none, by simp [lenZero, run0, run1, run2], by simp⟩
          | some p2 =>
            obtain ⟨t1, r⟩ := p2
            obtain ⟨ok1, grown1, rAt⟩ := spec2 t1 r rfl
            obtain ⟨r3, run3, spec3⟩ := intern_role_spec t1 ok1 q qProper
            cases r3 with
            | none => exact ⟨none, by simp [lenZero, run0, run1, run2, run3], by simp⟩
            | some p3 =>
              obtain ⟨t2, s⟩ := p3
              obtain ⟨ok2, grown2, sAt⟩ := spec3 t2 s rfl
              obtain ⟨r4, run4, spec4⟩ := push_rule_spec rules (.Role r s)
              cases r4 with
              | none => exact ⟨none, by simp [lenZero, run0, run1, run2, run3, run4], by simp⟩
              | some rules1 =>
                obtain ⟨r5, run5, spec5⟩ := push_rule_spec rules1 (.Role s r)
                cases r5 with
                | none => exact ⟨none, by simp [lenZero, run0, run1, run2, run3, run4, run5], by simp⟩
                | some rules2 =>
                  refine ⟨some (t2, rules2), by simp [lenZero, run0, run1, run2, run3, run4, run5],
                    fun t' rules' same => ?_⟩
                  simp only [Option.some.injEq, Prod.mk.injEq] at same
                  obtain ⟨rfl, rfl⟩ := same
                  have rAt2 := prefix_lookup grown2.2 rAt
                  have rInside := (List.getElem?_eq_some_iff.mp rAt2).1
                  have sInside := (List.getElem?_eq_some_iff.mp sAt).1
                  refine ⟨ok2, extends_trans grown1 grown2, [.Role r s, .Role s r],
                    by rw [spec5 _ rfl, spec4 _ rfl]; simp, ?_, fun I fixed => ?_⟩
                  · intro rule member
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                    rcases member with rfl | rfl
                    · exact ⟨rInside, sInside⟩
                    · exact ⟨sInside, rInside⟩
                  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, RuleHolds,
                      satisfies, Rowl.Owl.allEqual, AtLeastTwo.elements, restNil, firstIs, secondIs, objectRelation,
                      rel_at I rAt2, rel_at I sAt]
                    constructor
                    · rintro ⟨⟨_, same⟩, _, _⟩
                      exact ⟨fun x y edge => by rw [← same]; exact edge, fun x y edge => by rw [same]; exact edge⟩
                    · rintro ⟨forward, backward⟩
                      have same : I.objectProperties p = I.objectProperties q := by
                        funext x y; exact propext ⟨forward x y, backward x y⟩
                      exact ⟨⟨trivial, same⟩, same.symm, trivial⟩
    · have lenNonzero : ¬ alloc.vec.Vec.len members.rest = 0#usize := fun same =>
        single (by simpa using congrArg UScalar.val same)
      exact ⟨none, by simp [lenNonzero], by simp⟩
  | TransitiveObjectProperty role =>
    obtain ⟨r0, run0, spec0⟩ := named_role_spec role
    cases r0 with
    | none => exact ⟨none, by simp [run0], by simp⟩
    | some p =>
      obtain ⟨roleIs, proper⟩ := spec0 p rfl
      subst roleIs
      obtain ⟨r1, run1, spec1⟩ := intern_role_spec t ok p proper
      cases r1 with
      | none => exact ⟨none, by simp [run0, run1], by simp⟩
      | some p1 =>
        obtain ⟨t1, r⟩ := p1
        obtain ⟨ok1, grown1, rAt⟩ := spec1 t1 r rfl
        obtain ⟨r2, run2, spec2⟩ := push_rule_spec rules (.Chain r r r)
        cases r2 with
        | none => exact ⟨none, by simp [run0, run1, run2], by simp⟩
        | some rules1 =>
          refine ⟨some (t1, rules1), by simp [run0, run1, run2], fun t' rules' same => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          have rInside := (List.getElem?_eq_some_iff.mp rAt).1
          refine ⟨ok1, grown1, [.Chain r r r], spec2 _ rfl, ?_, fun I fixed => ?_⟩
          · intro rule member
            rw [List.mem_singleton] at member
            subst member
            exact ⟨rInside, rInside, rInside⟩
          · simp only [List.mem_singleton, forall_eq, RuleHolds, satisfies, objectRelation, rel_at I rAt]
  | _ => exact ⟨none, by simp, by simp⟩

theorem translate_spec (items : alloc.vec.Vec AnnotatedAxiom) (top bottom : Usize) (index : Usize)
    (t : saturation.Table) (ok : TableOk t) (rules : alloc.vec.Vec saturation.Rule)
    (topAt : t.concepts.val[top.val]? = some .Top) (bottomAt : t.concepts.val[bottom.val]? = some .Bottom) :
    ∃ r, saturation.translate t rules items top bottom index = .ok r ∧ ∀ t' rules', r = some (t', rules') →
      TableOk t' ∧ Extends t t' ∧ ∃ added, rules'.val = rules.val ++ added ∧ (∀ rule ∈ added, RuleInside t' rule) ∧
        ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Fixed I →
          ((∀ a ∈ items.val.drop index.val, satisfies I a.axiom) ↔
            ∀ rule ∈ added, RuleHolds I t'.concepts.val t'.roles.val rule) := by
  rw [saturation.translate]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨r1, run1, spec1⟩ := translate_axiom_spec.{u,v} t ok rules items.val[index.val].axiom top bottom topAt
      bottomAt
    cases r1 with
    | none => exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, run1], by simp⟩
    | some p1 =>
      obtain ⟨t1, rules1⟩ := p1
      obtain ⟨ok1, grown1, added1, added1Is, inside1, meaning1⟩ := spec1 t1 rules1 rfl
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, spec⟩ := translate_spec items top bottom next t1 ok1 rules1 (prefix_lookup grown1.1 topAt)
        (prefix_lookup grown1.1 bottomAt)
      refine ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, run1, advance, run],
        fun t' rules' same => ?_⟩
      obtain ⟨ok', grown', added2, added2Is, inside2, meaning2⟩ := spec t' rules' same
      refine ⟨ok', extends_trans grown1 grown', added1 ++ added2, by rw [added2Is, added1Is, List.append_assoc], ?_,
        fun I fixed => ?_⟩
      · intro rule member
        rcases List.mem_append.mp member with old | new
        · exact inside_later grown' (inside1 rule old)
        · exact inside2 rule new
      · rw [List.drop_eq_getElem_cons more, List.forall_mem_cons, meaning1 I fixed, ← nextIs, meaning2 I fixed,
          List.forall_mem_append]
        constructor
        · rintro ⟨first, rest⟩
          exact ⟨fun rule member => (holds_later I ok1 grown' (inside1 rule member)).mpr (first rule member), rest⟩
        · rintro ⟨first, rest⟩
          exact ⟨fun rule member => (holds_later I ok1 grown' (inside1 rule member)).mp (first rule member), rest⟩
  · refine ⟨some (t, rules), by simp [UScalar.lt_equiv, more], fun t' rules' same => ?_⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    refine ⟨ok, extends_refl _, [], by simp, by simp, fun I _ => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by items.val.length - index.val
decreasing_by omega

/-- The concepts of the named classes. -/
def ClassIds (t : saturation.Table) (ids : List Usize) (classes : List Class) : Prop :=
  List.Forall₂ (fun (id : Usize) k => t.concepts.val[id.val]? = some (classConcept k)) ids classes

theorem class_ids_later {t t' : saturation.Table} (grown : Extends t t') {ids : List Usize} {classes : List Class}
    (before : ClassIds t ids classes) : ClassIds t' ids classes :=
  List.Forall₂.imp (fun _ _ at_id => prefix_lookup grown.1 at_id) before

theorem class_concepts_spec (classes : alloc.vec.Vec Class) (index : Usize) (t : saturation.Table) (ok : TableOk t)
    (out : alloc.vec.Vec Usize) (done : List Class) (before : ClassIds t out.val done) :
    ∃ r, saturation.class_concepts t classes index out = .ok r ∧ ∀ t' out', r = some (t', out') →
      TableOk t' ∧ Extends t t' ∧ ClassIds t' out'.val (done ++ classes.val.drop index.val) := by
  rw [saturation.class_concepts]
  by_cases more : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨r1, run1, spec1⟩ := concept_of_class t ok classes.val[index.val]
    cases r1 with
    | none => exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, copy_class_identity, run1],
        by simp⟩
    | some p1 =>
      obtain ⟨t1, id⟩ := p1
      obtain ⟨ok1, grown1, idAt⟩ := spec1 t1 id rfl
      by_cases room : out.val.length < Usize.max
      · obtain ⟨out1, push, outIs⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out id room)
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = index.val + 1 := by simpa using nextValue
        have now : ClassIds t1 out1.val (done ++ [classes.val[index.val]]) := by
          rw [outIs]
          exact List.rel_append (class_ids_later grown1 before) (List.Forall₂.cons idAt List.Forall₂.nil)
        obtain ⟨r, run, spec⟩ := class_concepts_spec classes next t1 ok1 out1 _ now
        refine ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, more, lookup, copy_class_identity,
          run1, room, push, advance, run], fun t' out' same => ?_⟩
        obtain ⟨ok', grown', after⟩ := spec t' out' same
        refine ⟨ok', extends_trans grown1 grown', ?_⟩
        rw [nextIs] at after
        rw [List.drop_eq_getElem_cons more]
        simpa using after
      · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, more, lookup, copy_class_identity,
          run1, room], by simp⟩
  · refine ⟨some (t, out), by simp [UScalar.lt_equiv, more], fun t' out' same => ?_⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    refine ⟨ok, extends_refl _, ?_⟩
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
    exact before
termination_by classes.val.length - index.val
decreasing_by omega

/-! ### The rule index -/

/-- The entries of `list[at]`; none outside the list. -/
def entries {α : Type} (list : List (alloc.vec.Vec α)) (at' : Nat) : List α :=
  match list[at']? with
  | some l => l.val
  | none => []

theorem mem_entries_push {α : Type} {list list' : List (alloc.vec.Vec α)} {at' : Nat} {old new : alloc.vec.Vec α}
    {x : α} (at_old : list[at']? = some old) (newIs : new.val = old.val ++ [x]) (listIs : list' = list.set at' new)
    (i : Nat) (y : α) : y ∈ entries list' i ↔ y ∈ entries list i ∨ (i = at' ∧ y = x) := by
  subst listIs
  have inside : at' < list.length := (List.getElem?_eq_some_iff.mp at_old).1
  unfold entries
  by_cases same : i = at'
  · subst same
    rw [List.getElem?_set_self inside, at_old]
    simp [newIs]
  · rw [List.getElem?_set_ne (Ne.symm same)]
    simp [same]

theorem entries_empty {α : Type} {list : List (alloc.vec.Vec α)} (empty : ∀ b ∈ list, b.val = []) (i : Nat) :
    entries list i = [] := by
  unfold entries
  cases at_i : list[i]? with
  | none => rfl
  | some b => exact empty b (List.mem_of_getElem? at_i)

/-- The conjunction and existential entries name their concepts. -/
def PartsIndexed (concepts : List saturation.Concept)
    (conjunctions existentials : List (alloc.vec.Vec (Usize × Usize))) : Prop :=
  (∀ (a b c : Usize), (b, c) ∈ entries conjunctions a.val →
    concepts[c.val]? = some (.And a b) ∨ concepts[c.val]? = some (.And b a)) ∧
  (∀ (f r c : Usize), (r, c) ∈ entries existentials f.val → concepts[c.val]? = some (.Exists r f))

def Grows {α : Type} (old new : List (alloc.vec.Vec α)) : Prop :=
  ∀ (i : Nat) x, x ∈ entries old i → x ∈ entries new i

def SeenGrows (old new : List Bool) : Prop := ∀ (i : Nat), old[i]? = some true → new[i]? = some true

/-- A registered conjunction is indexed under both parts and an existential
    restriction under its filler, and their parts are registered. -/
def Registered (concepts : List saturation.Concept) (conjunctions existentials : List (alloc.vec.Vec (Usize × Usize)))
    (seen : List Bool) (c : Usize) : Prop :=
  match concepts[c.val]? with
  | some (.And a b) => (b, c) ∈ entries conjunctions a.val ∧ (a, c) ∈ entries conjunctions b.val ∧
      seen[a.val]? = some true ∧ seen[b.val]? = some true
  | some (.Exists r f) => (r, c) ∈ entries existentials f.val ∧ seen[f.val]? = some true
  | _ => True

theorem registered_mono {concepts : List saturation.Concept} {conj conj' ex ex' : List (alloc.vec.Vec (Usize × Usize))}
    {seen seen' : List Bool} {c : Usize} (h : Registered concepts conj ex seen c)
    (g1 : Grows conj conj') (g2 : Grows ex ex') (g3 : SeenGrows seen seen') : Registered concepts conj' ex' seen' c := by
  unfold Registered at h ⊢
  cases at_c : concepts[c.val]? with
  | none => trivial
  | some d =>
    rw [at_c] at h
    cases d with
    | And a b => exact ⟨g1 _ _ h.1, g1 _ _ h.2.1, g3 _ h.2.2.1, g3 _ h.2.2.2⟩
    | Exists r f => exact ⟨g2 _ _ h.1, g3 _ h.2⟩
    | Top => trivial
    | Bottom => trivial
    | Atom _ => trivial

theorem register_spec (t : saturation.Table) (ok : TableOk t) (c : Usize)
    (conjunctions existentials : alloc.vec.Vec (alloc.vec.Vec (Usize × Usize))) (seen : alloc.vec.Vec Bool)
    (pending : Usize → Prop) (indexed : PartsIndexed t.concepts.val conjunctions.val existentials.val)
    (closed : ∀ d : Usize, seen.val[d.val]? = some true →
      Registered t.concepts.val conjunctions.val existentials.val seen.val d ∨ pending d) :
    ∃ r, saturation.register t.concepts conjunctions existentials seen c = .ok r ∧
      ∀ conj' ex' seen', r = some (conj', ex', seen') →
        PartsIndexed t.concepts.val conj'.val ex'.val ∧
        (∀ d : Usize, seen'.val[d.val]? = some true →
          Registered t.concepts.val conj'.val ex'.val seen'.val d ∨ pending d) ∧
        seen'.val[c.val]? = some true ∧
        Grows conjunctions.val conj'.val ∧ Grows existentials.val ex'.val ∧ SeenGrows seen.val seen'.val := by
  rw [saturation.register]
  by_cases inside : c.val < t.concepts.val.length
  · by_cases insideSeen : c.val < seen.val.length
    · have seenLookup : seen.index_usize c = .ok seen.val[c.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem insideSeen]
      have seenAt : seen.val[c.val]? = some seen.val[c.val] := List.getElem?_eq_getElem insideSeen
      by_cases already : seen.val[c.val] = true
      · refine ⟨some (conjunctions, existentials, seen), by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside,
          insideSeen, seenLookup, already], fun conj' ex' seen' same => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at same
        obtain ⟨rfl, rfl, rfl⟩ := same
        exact ⟨indexed, closed, by rw [seenAt, already], fun _ _ h => h, fun _ _ h => h, fun _ h => h⟩
      · have notYet : seen.val[c.val] = false := by simpa using already
        have conceptLookup : t.concepts.index_usize c = .ok t.concepts.val[c.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
        have at_c : t.concepts.val[c.val]? = some t.concepts.val[c.val] := List.getElem?_eq_getElem inside
        have seen1At : ∀ (i : Nat), (seen.set c true).val[i]? = if i = c.val then some true else seen.val[i]? := by
          intro i
          rw [alloc.vec.Vec.set_val_eq]
          by_cases same : i = c.val
          · subst same; rw [List.getElem?_set_self insideSeen]; simp
          · rw [List.getElem?_set_ne (Ne.symm same)]; simp [same]
        have seen1Grows : SeenGrows seen.val (seen.set c true).val := by
          intro i h
          rw [seen1At]
          by_cases same : i = c.val
          · simp [same]
          · simp [same, h]
        have seen1Self : (seen.set c true).val[c.val]? = some true := by rw [seen1At]; simp
        have seen1Closed : ∀ d : Usize, (seen.set c true).val[d.val]? = some true →
            Registered t.concepts.val conjunctions.val existentials.val (seen.set c true).val d ∨ pending d ∨ d = c := by
          intro d h
          rw [seen1At] at h
          by_cases same : d.val = c.val
          · exact Or.inr (Or.inr (UScalar.eq_of_val_eq same))
          · rw [if_neg same] at h
            rcases closed d h with reg | wait
            · exact Or.inl (registered_mono reg (fun _ _ h => h) (fun _ _ h => h) seen1Grows)
            · exact Or.inr (Or.inl wait)
        have partsOk := ok.parts c.val _ at_c
        have leaf : ∀ (k : saturation.Concept), t.concepts.val[c.val] = k →
            (∀ a b, k ≠ .And a b) → (∀ r f, k ≠ .Exists r f) →
            ∀ conj' ex' seen', some (conjunctions, existentials, seen.set c true) = some (conj', ex', seen') →
              PartsIndexed t.concepts.val conj'.val ex'.val ∧
              (∀ d : Usize, seen'.val[d.val]? = some true →
                Registered t.concepts.val conj'.val ex'.val seen'.val d ∨ pending d) ∧
              seen'.val[c.val]? = some true ∧
              Grows conjunctions.val conj'.val ∧ Grows existentials.val ex'.val ∧ SeenGrows seen.val seen'.val := by
          intro k concept notAnd notExists conj' ex' seen' same
          simp only [Option.some.injEq, Prod.mk.injEq] at same
          obtain ⟨rfl, rfl, rfl⟩ := same
          refine ⟨indexed, fun d h => ?_, seen1Self, fun _ _ h => h, fun _ _ h => h, seen1Grows⟩
          rcases seen1Closed d h with reg | wait | rfl
          · exact Or.inl reg
          · exact Or.inr wait
          · left
            unfold Registered
            rw [at_c, concept]
            cases k with
            | And a b => exact absurd rfl (notAnd a b)
            | Exists r f => exact absurd rfl (notExists r f)
            | Top => trivial
            | Bottom => trivial
            | Atom _ => trivial
        cases concept : t.concepts.val[c.val] with
        | Top =>
          exact ⟨_, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, insideSeen, seenLookup, notYet,
            alloc.vec.Vec.index_mut_usize, conceptLookup, concept], leaf _ concept (by simp) (by simp)⟩
        | Bottom =>
          exact ⟨_, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, insideSeen, seenLookup, notYet,
            alloc.vec.Vec.index_mut_usize, conceptLookup, concept], leaf _ concept (by simp) (by simp)⟩
        | Atom k =>
          exact ⟨_, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, insideSeen, seenLookup, notYet,
            alloc.vec.Vec.index_mut_usize, conceptLookup, concept], leaf _ concept (by simp) (by simp)⟩
        | And a b =>
          rw [concept] at partsOk at_c
          have aLt : a.val < c.val := partsOk.1
          have bLt : b.val < c.val := partsOk.2
          obtain ⟨r1, run1, spec1⟩ := push_pair_spec conjunctions a (b, c)
          cases r1 with
          | none =>
            exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, insideSeen, seenLookup, notYet,
              alloc.vec.Vec.index_mut_usize, conceptLookup, concept, run1], by simp⟩
          | some list =>
            obtain ⟨old1, new1, at1, new1Is, list1Is⟩ := spec1 list rfl
            have mem1 := mem_entries_push at1 new1Is list1Is
            obtain ⟨r2, run2, spec2⟩ := push_pair_spec list b (a, c)
            cases r2 with
            | none =>
              exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, insideSeen, seenLookup, notYet,
                alloc.vec.Vec.index_mut_usize, conceptLookup, concept, run1, run2], by simp⟩
            | some list' =>
              obtain ⟨old2, new2, at2, new2Is, list2Is⟩ := spec2 list' rfl
              have mem2 := mem_entries_push at2 new2Is list2Is
              have grow12 : Grows conjunctions.val list'.val :=
                fun i x h => (mem2 i x).mpr (Or.inl ((mem1 i x).mpr (Or.inl h)))
              have indexed' : PartsIndexed t.concepts.val list'.val existentials.val := by
                refine ⟨fun a' b' c' h => ?_, indexed.2⟩
                rcases (mem2 _ _).mp h with h | ⟨same, pair⟩
                · rcases (mem1 _ _).mp h with h | ⟨same, pair⟩
                  · exact indexed.1 a' b' c' h
                  · simp only [Prod.mk.injEq] at pair
                    obtain ⟨rfl, rfl⟩ := pair
                    rw [UScalar.eq_of_val_eq same]
                    exact Or.inl at_c
                · simp only [Prod.mk.injEq] at pair
                  obtain ⟨rfl, rfl⟩ := pair
                  rw [UScalar.eq_of_val_eq same]
                  exact Or.inr at_c
              obtain ⟨r3, run3, spec3⟩ := register_spec t ok a list' existentials (seen.set c true)
                (fun d => pending d ∨ d = c) indexed' (by
                  intro d h
                  rcases seen1Closed d h with reg | wait | rfl
                  · exact Or.inl (registered_mono reg grow12 (fun _ _ h => h) (fun _ h => h))
                  · exact Or.inr (Or.inl wait)
                  · exact Or.inr (Or.inr rfl))
              cases r3 with
              | none =>
                exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, insideSeen, seenLookup, notYet,
                  alloc.vec.Vec.index_mut_usize, conceptLookup, concept, run1, run2, run3], by simp⟩
              | some found =>
                obtain ⟨conj2, ex2, seen2⟩ := found
                obtain ⟨indexed2, closed2, seenA, grow2, growEx2, seenGrow2⟩ := spec3 conj2 ex2 seen2 rfl
                obtain ⟨r4, run4, spec4⟩ := register_spec t ok b conj2 ex2 seen2 (fun d => pending d ∨ d = c)
                  indexed2 closed2
                refine ⟨r4, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, insideSeen, seenLookup, notYet,
                  alloc.vec.Vec.index_mut_usize, conceptLookup, concept, run1, run2, run3, run4],
                  fun conj' ex' seen' same => ?_⟩
                obtain ⟨indexed3, closed3, seenB, grow3, growEx3, seenGrow3⟩ := spec4 conj' ex' seen' same
                refine ⟨indexed3, fun d h => ?_, seenGrow3 _ (seenGrow2 _ seen1Self),
                  fun i x h => grow3 i x (grow2 i x (grow12 i x h)), fun i x h => growEx3 i x (growEx2 i x h),
                  fun i h => seenGrow3 i (seenGrow2 i (seen1Grows i h))⟩
                rcases closed3 d h with reg | wait | rfl
                · exact Or.inl reg
                · exact Or.inr wait
                · left
                  unfold Registered
                  rw [at_c]
                  exact ⟨grow3 _ _ (grow2 _ _ ((mem2 _ _).mpr (Or.inl ((mem1 _ _).mpr (Or.inr ⟨rfl, rfl⟩))))),
                    grow3 _ _ (grow2 _ _ ((mem2 _ _).mpr (Or.inr ⟨rfl, rfl⟩))), seenGrow3 _ seenA, seenB⟩
        | Exists r f =>
          rw [concept] at partsOk at_c
          have fLt : f.val < c.val := partsOk.1
          obtain ⟨r1, run1, spec1⟩ := push_pair_spec existentials f (r, c)
          cases r1 with
          | none =>
            exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, insideSeen, seenLookup, notYet,
              alloc.vec.Vec.index_mut_usize, conceptLookup, concept, run1], by simp⟩
          | some list =>
            obtain ⟨old1, new1, at1, new1Is, list1Is⟩ := spec1 list rfl
            have mem1 := mem_entries_push at1 new1Is list1Is
            have growEx : Grows existentials.val list.val := fun i x h => (mem1 i x).mpr (Or.inl h)
            have indexed' : PartsIndexed t.concepts.val conjunctions.val list.val := by
              refine ⟨indexed.1, fun f' r' c' h => ?_⟩
              rcases (mem1 _ _).mp h with h | ⟨same, pair⟩
              · exact indexed.2 f' r' c' h
              · simp only [Prod.mk.injEq] at pair
                obtain ⟨rfl, rfl⟩ := pair
                rw [UScalar.eq_of_val_eq same]
                exact at_c
            obtain ⟨r2, run2, spec2⟩ := register_spec t ok f conjunctions list (seen.set c true)
              (fun d => pending d ∨ d = c) indexed' (by
                intro d h
                rcases seen1Closed d h with reg | wait | rfl
                · exact Or.inl (registered_mono reg (fun _ _ h => h) growEx (fun _ h => h))
                · exact Or.inr (Or.inl wait)
                · exact Or.inr (Or.inr rfl))
            refine ⟨r2, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, insideSeen, seenLookup, notYet,
              alloc.vec.Vec.index_mut_usize, conceptLookup, concept, run1, run2], fun conj' ex' seen' same => ?_⟩
            obtain ⟨indexed2, closed2, seenF, grow2, growEx2, seenGrow2⟩ := spec2 conj' ex' seen' same
            refine ⟨indexed2, fun d h => ?_, seenGrow2 _ seen1Self, grow2, fun i x h => growEx2 i x (growEx i x h),
              fun i h => seenGrow2 i (seen1Grows i h)⟩
            rcases closed2 d h with reg | wait | rfl
            · exact Or.inl reg
            · exact Or.inr wait
            · left
              unfold Registered
              rw [at_c]
              exact ⟨growEx2 _ _ ((mem1 _ _).mpr (Or.inr ⟨rfl, rfl⟩)), seenF⟩
    · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, insideSeen], by simp⟩
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside], by simp⟩
termination_by c.val
decreasing_by all_goals omega

/-- Every index entry comes from a rule of `list`, and the conjunction and
    existential entries name their concepts. -/
structure IndexSound (concepts : List saturation.Concept) (list : List saturation.Rule) (rules : saturation.Rules) :
    Prop where
  told : ∀ (c d : Usize), d ∈ entries rules.told.val c.val → saturation.Rule.Sub c d ∈ list
  parts : PartsIndexed concepts rules.conjunctions.val rules.existentials.val
  supers : ∀ (r s : Usize), s ∈ entries rules.supers.val r.val → saturation.Rule.Role r s ∈ list
  firsts : ∀ (r s q : Usize), (s, q) ∈ entries rules.firsts.val r.val → saturation.Rule.Chain r s q ∈ list
  seconds : ∀ (s r q : Usize), (r, q) ∈ entries rules.seconds.val s.val → saturation.Rule.Chain r s q ∈ list

/-- Every rule of `list` is indexed, its left-hand side is registered, and the
    registered concepts are closed under parts. -/
structure IndexComplete (concepts : List saturation.Concept) (list : List saturation.Rule) (rules : saturation.Rules)
    (seen : List Bool) : Prop where
  told : ∀ (a b : Usize), saturation.Rule.Sub a b ∈ list → b ∈ entries rules.told.val a.val ∧ seen[a.val]? = some true
  supers : ∀ (r s : Usize), saturation.Rule.Role r s ∈ list → s ∈ entries rules.supers.val r.val
  firsts : ∀ (r s q : Usize), saturation.Rule.Chain r s q ∈ list → (s, q) ∈ entries rules.firsts.val r.val
  registered : ∀ (c : Usize), seen[c.val]? = some true →
    Registered concepts rules.conjunctions.val rules.existentials.val seen c

theorem index_from_spec (t : saturation.Table) (ok : TableOk t) (list : alloc.vec.Vec saturation.Rule) (index : Usize)
    (rules : saturation.Rules) (seen : alloc.vec.Vec Bool) (sound : IndexSound t.concepts.val list.val rules)
    (complete : IndexComplete t.concepts.val (list.val.take index.val) rules seen.val) :
    ∃ r, saturation.index_from t.concepts list index rules seen = .ok r ∧ ∀ rules', r = some rules' →
      rules'.top = rules.top ∧ rules'.bottom = rules.bottom ∧ IndexSound t.concepts.val list.val rules' ∧
      ∃ seen' : List Bool, IndexComplete t.concepts.val list.val rules' seen' := by
  rw [saturation.index_from]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have member : list.val[index.val] ∈ list.val := List.getElem_mem more
    have takeNext : list.val.take (index.val + 1) = list.val.take index.val ++ [list.val[index.val]] :=
      List.take_succ_eq_append_getElem more
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    cases rule : list.val[index.val] with
    | Sub a b =>
      rw [rule] at member takeNext
      obtain ⟨r1, run1, spec1⟩ := push_item_spec rules.told a b
      cases r1 with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, rule, run1], by simp⟩
      | some told =>
        obtain ⟨old, new, at_old, newIs, toldIs⟩ := spec1 told rfl
        have mem := mem_entries_push at_old newIs toldIs
        obtain ⟨r2, run2, spec2⟩ := register_spec t ok a rules.conjunctions rules.existentials seen (fun _ => False)
          sound.parts (fun d h => Or.inl (complete.registered d h))
        cases r2 with
        | none =>
          exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, rule, run1, run2], by simp⟩
        | some found =>
          obtain ⟨conj, ex, seen1⟩ := found
          obtain ⟨indexed, closed, seenA, growConj, growEx, seenGrows⟩ := spec2 conj ex seen1 rfl
          let rules1 : saturation.Rules := { rules with told := told, conjunctions := conj, existentials := ex }
          have sound1 : IndexSound t.concepts.val list.val rules1 := {
            told := fun c d h => by
              rcases (mem _ _).mp h with h | ⟨same, rfl⟩
              · exact sound.told c d h
              · rw [UScalar.eq_of_val_eq same]; exact member
            parts := indexed
            supers := sound.supers
            firsts := sound.firsts
            seconds := sound.seconds }
          have complete1 : IndexComplete t.concepts.val (list.val.take next.val) rules1 seen1.val := by
            rw [nextIs, takeNext]
            refine {
              told := fun a' b' h => ?_
              supers := fun r s h => ?_
              firsts := fun r s q h => ?_
              registered := fun c h => ?_ }
            · rcases List.mem_append.mp h with h | h
              · obtain ⟨told', seen'⟩ := complete.told a' b' h
                exact ⟨(mem _ _).mpr (Or.inl told'), seenGrows _ seen'⟩
              · rw [List.mem_singleton] at h
                cases h
                exact ⟨(mem _ _).mpr (Or.inr ⟨rfl, rfl⟩), seenA⟩
            · rcases List.mem_append.mp h with h | h
              · exact complete.supers r s h
              · simp at h
            · rcases List.mem_append.mp h with h | h
              · exact complete.firsts r s q h
              · simp at h
            · rcases closed c h with reg | nope
              · exact reg
              · exact nope.elim
          obtain ⟨r, run, spec⟩ := index_from_spec t ok list next rules1 seen1 sound1 complete1
          refine ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, rule, run1, run2, advance, run,
            rules1], fun rules' same => ?_⟩
          obtain ⟨top', bottom', sound', seen', complete'⟩ := spec rules' same
          exact ⟨top', bottom', sound', seen', complete'⟩
    | Role r s =>
      rw [rule] at member takeNext
      obtain ⟨r1, run1, spec1⟩ := push_item_spec rules.supers r s
      cases r1 with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, rule, run1], by simp⟩
      | some supers =>
        obtain ⟨old, new, at_old, newIs, supersIs⟩ := spec1 supers rfl
        have mem := mem_entries_push at_old newIs supersIs
        let rules1 : saturation.Rules := { rules with supers := supers }
        have sound1 : IndexSound t.concepts.val list.val rules1 := {
          told := sound.told
          parts := sound.parts
          supers := fun r' s' h => by
            rcases (mem _ _).mp h with h | ⟨same, rfl⟩
            · exact sound.supers r' s' h
            · rw [UScalar.eq_of_val_eq same]; exact member
          firsts := sound.firsts
          seconds := sound.seconds }
        have complete1 : IndexComplete t.concepts.val (list.val.take next.val) rules1 seen.val := by
          rw [nextIs, takeNext]
          refine {
            told := fun a b h => ?_
            supers := fun r' s' h => ?_
            firsts := fun r' s' q h => ?_
            registered := complete.registered }
          · rcases List.mem_append.mp h with h | h
            · exact complete.told a b h
            · simp at h
          · rcases List.mem_append.mp h with h | h
            · exact (mem _ _).mpr (Or.inl (complete.supers r' s' h))
            · rw [List.mem_singleton] at h
              cases h
              exact (mem _ _).mpr (Or.inr ⟨rfl, rfl⟩)
          · rcases List.mem_append.mp h with h | h
            · exact complete.firsts r' s' q h
            · simp at h
        obtain ⟨r', run, spec⟩ := index_from_spec t ok list next rules1 seen sound1 complete1
        refine ⟨r', by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, rule, run1, advance, run, rules1],
          fun rules' same => ?_⟩
        obtain ⟨top', bottom', sound', seen', complete'⟩ := spec rules' same
        exact ⟨top', bottom', sound', seen', complete'⟩
    | Chain r1 r2 s =>
      rw [rule] at member takeNext
      obtain ⟨o1, run1, spec1⟩ := push_pair_spec rules.firsts r1 (r2, s)
      cases o1 with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, rule, run1], by simp⟩
      | some firsts =>
        obtain ⟨old, new, at_old, newIs, firstsIs⟩ := spec1 firsts rfl
        have mem := mem_entries_push at_old newIs firstsIs
        obtain ⟨o2, run2, spec2⟩ := push_pair_spec rules.seconds r2 (r1, s)
        cases o2 with
        | none =>
          exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, rule, run1, run2], by simp⟩
        | some seconds =>
          obtain ⟨old2, new2, at_old2, newIs2, secondsIs⟩ := spec2 seconds rfl
          have mem2 := mem_entries_push at_old2 newIs2 secondsIs
          let rules1 : saturation.Rules := { rules with firsts := firsts, seconds := seconds }
          have sound1 : IndexSound t.concepts.val list.val rules1 := {
            told := sound.told
            parts := sound.parts
            supers := sound.supers
            firsts := fun r' s' q h => by
              rcases (mem _ _).mp h with h | ⟨same, pair⟩
              · exact sound.firsts r' s' q h
              · simp only [Prod.mk.injEq] at pair
                obtain ⟨rfl, rfl⟩ := pair
                rw [UScalar.eq_of_val_eq same]; exact member
            seconds := fun s' r' q h => by
              rcases (mem2 _ _).mp h with h | ⟨same, pair⟩
              · exact sound.seconds s' r' q h
              · simp only [Prod.mk.injEq] at pair
                obtain ⟨rfl, rfl⟩ := pair
                rw [UScalar.eq_of_val_eq same]; exact member }
          have complete1 : IndexComplete t.concepts.val (list.val.take next.val) rules1 seen.val := by
            rw [nextIs, takeNext]
            refine {
              told := fun a b h => ?_
              supers := fun r' s' h => ?_
              firsts := fun r' s' q h => ?_
              registered := complete.registered }
            · rcases List.mem_append.mp h with h | h
              · exact complete.told a b h
              · simp at h
            · rcases List.mem_append.mp h with h | h
              · exact complete.supers r' s' h
              · simp at h
            · rcases List.mem_append.mp h with h | h
              · exact (mem _ _).mpr (Or.inl (complete.firsts r' s' q h))
              · rw [List.mem_singleton] at h
                cases h
                exact (mem _ _).mpr (Or.inr ⟨rfl, rfl⟩)
          obtain ⟨r', run, spec⟩ := index_from_spec t ok list next rules1 seen sound1 complete1
          refine ⟨r', by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, rule, run1, run2, advance, run,
            rules1], fun rules' same => ?_⟩
          obtain ⟨top', bottom', sound', seen', complete'⟩ := spec rules' same
          exact ⟨top', bottom', sound', seen', complete'⟩
  · refine ⟨some rules, by simp [UScalar.lt_equiv, more], fun rules' same => ?_⟩
    cases same
    refine ⟨rfl, rfl, sound, seen.val, ?_⟩
    rw [List.take_of_length_le (by omega)] at complete
    exact complete
termination_by list.val.length - index.val
decreasing_by all_goals omega

/-! ### Saturation derives only consequences -/

section Entailment
variable (t : saturation.Table) (list : List saturation.Rule)

/-- Every rule holds. -/
def Models {Object : Type u} {Value : Type v} (I : Interpretation Object Value) : Prop :=
  ∀ rule ∈ list, RuleHolds I t.concepts.val t.roles.val rule

/-- In every model of the rules, `c` holds wherever `x` does. -/
def SubOk (x c : Nat) : Prop :=
  ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Models t list I →
    ∀ e, meaning I t.concepts.val t.roles.val x e → meaning I t.concepts.val t.roles.val c e

/-- In every model of the rules, everything where `x` holds has an `r`-successor where `y` holds. -/
def LinkOk (x r y : Nat) : Prop :=
  ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Models t list I →
    ∀ e, meaning I t.concepts.val t.roles.val x e →
      ∃ e', rel I t.roles.val r e e' ∧ meaning I t.concepts.val t.roles.val y e'

def FactOk : saturation.Fact → Prop
  | .Sub x c => SubOk.{u,v} t list x.val c.val
  | .Link x r y => LinkOk.{u,v} t list x.val r.val y.val

/-- Every subsumer, link and queued fact of the state follows from the rules,
    and the contexts `keep` are active. -/
structure StateOk (keep : Nat → Prop) (state : saturation.State) : Prop where
  subsumers : ∀ (x : Nat) (c : Usize), c ∈ entries state.subsumers.val x → SubOk.{u,v} t list x c.val
  out : ∀ (x : Nat) (r y : Usize), (r, y) ∈ entries state.out.val x → LinkOk.{u,v} t list x r.val y.val
  into : ∀ (y : Nat) (r x : Usize), (r, x) ∈ entries state.into.val y → LinkOk.{u,v} t list x.val r.val y
  queue : ∀ fact ∈ state.queue.val, FactOk.{u,v} t list fact
  active : ∀ x, keep x → state.active.val[x]? = some true

end Entailment

theorem entries_lookup {α : Type} {list : List (alloc.vec.Vec α)} {i : Nat} {l : alloc.vec.Vec α}
    (at_i : list[i]? = some l) : entries list i = l.val := by
  simp [entries, at_i]

theorem entry_mem {α : Type} (list : List (alloc.vec.Vec α)) (i j : Nat) (hi : i < list.length)
    (hj : j < list[i].val.length) : list[i].val[j] ∈ entries list i := by
  rw [entries_lookup (List.getElem?_eq_getElem hi)]; exact List.getElem_mem hj

theorem state_ok_weaken {t : saturation.Table} {list : List saturation.Rule} {keep keep' : Nat → Prop}
    {state : saturation.State} (stateOk : StateOk.{u,v} t list keep state) (fewer : ∀ x, keep' x → keep x) :
    StateOk.{u,v} t list keep' state :=
  ⟨stateOk.subsumers, stateOk.out, stateOk.into, stateOk.queue, fun x h => stateOk.active x (fewer x h)⟩

section Steps
variable {t : saturation.Table} {list : List saturation.Rule} {keep : Nat → Prop}

theorem sub_refl (x : Nat) : SubOk.{u,v} t list x x := fun _ _ _ h => h

theorem sub_top {x top : Nat} (topAt : t.concepts.val[top]? = some .Top) : SubOk.{u,v} t list x top :=
  fun I _ e _ => meaning_top I topAt e

theorem sub_rule {x : Nat} {c d : Usize} (rule : saturation.Rule.Sub c d ∈ list) (h : SubOk.{u,v} t list x c.val) :
    SubOk.{u,v} t list x d.val :=
  fun I models e m => models _ rule e (h I models e m)

theorem sub_and {x : Nat} {c a b : Usize} (ok : TableOk t) (at_c : t.concepts.val[c.val]? = some (.And a b))
    (h : SubOk.{u,v} t list x c.val) : SubOk.{u,v} t list x a.val ∧ SubOk.{u,v} t list x b.val := by
  have partsOk := ok.parts c.val _ at_c
  have aLt : a.val < c.val := partsOk.1
  have bLt : b.val < c.val := partsOk.2
  exact ⟨fun I models e m => ((meaning_and I at_c aLt bLt e).mp (h I models e m)).1,
    fun I models e m => ((meaning_and I at_c aLt bLt e).mp (h I models e m)).2⟩

theorem sub_conj {x : Nat} {c a b : Usize} (ok : TableOk t)
    (at_c : t.concepts.val[c.val]? = some (.And a b) ∨ t.concepts.val[c.val]? = some (.And b a))
    (ha : SubOk.{u,v} t list x a.val) (hb : SubOk.{u,v} t list x b.val) : SubOk.{u,v} t list x c.val := by
  rcases at_c with at_c | at_c
  · have partsOk := ok.parts c.val _ at_c
    intro _ _ I models e m
    exact (meaning_and I at_c partsOk.1 partsOk.2 e).mpr ⟨ha I models e m, hb I models e m⟩
  · have partsOk := ok.parts c.val _ at_c
    intro _ _ I models e m
    exact (meaning_and I at_c partsOk.1 partsOk.2 e).mpr ⟨hb I models e m, ha I models e m⟩

theorem link_of_exists {x : Nat} {c r y : Usize} (ok : TableOk t)
    (at_c : t.concepts.val[c.val]? = some (.Exists r y)) (h : SubOk.{u,v} t list x c.val) :
    LinkOk.{u,v} t list x r.val y.val := by
  have partsOk := ok.parts c.val _ at_c
  intro _ _ I models e m
  exact (meaning_exists I at_c partsOk.1 e).mp (h I models e m)

theorem link_sub {x r y c : Nat} (link : LinkOk.{u,v} t list x r y) (sub : SubOk.{u,v} t list y c) :
    LinkOk.{u,v} t list x r c := fun I models e m => by
  obtain ⟨e', edge, inside⟩ := link I models e m
  exact ⟨e', edge, sub I models e' inside⟩

theorem sub_of_link_bottom {x r c : Nat} (at_c : t.concepts.val[c]? = some .Bottom)
    (link : LinkOk.{u,v} t list x r c) (d : Nat) : SubOk.{u,v} t list x d := fun I models e m => by
  obtain ⟨e', _, inside⟩ := link I models e m
  exact absurd inside (meaning_bottom I at_c e')

theorem sub_exists_back {w : Nat} {r c e : Usize} (ok : TableOk t)
    (at_e : t.concepts.val[e.val]? = some (.Exists r c)) (link : LinkOk.{u,v} t list w r.val c.val) :
    SubOk.{u,v} t list w e.val := by
  have partsOk := ok.parts e.val _ at_e
  intro _ _ I models el m
  exact (meaning_exists I at_e partsOk.1 el).mpr (link I models el m)

theorem link_super {x y : Nat} {r s : Usize} (rule : saturation.Rule.Role r s ∈ list)
    (link : LinkOk.{u,v} t list x r.val y) : LinkOk.{u,v} t list x s.val y := fun I models e m => by
  obtain ⟨e', edge, inside⟩ := link I models e m
  exact ⟨e', models _ rule e e' edge, inside⟩

theorem link_chain {x y z : Nat} {r1 r2 s : Usize} (rule : saturation.Rule.Chain r1 r2 s ∈ list)
    (first : LinkOk.{u,v} t list x r1.val y) (second : LinkOk.{u,v} t list y r2.val z) :
    LinkOk.{u,v} t list x s.val z := fun I models e m => by
  obtain ⟨e', edge, inside⟩ := first I models e m
  obtain ⟨e'', edge', inside'⟩ := second I models e' inside
  exact ⟨e'', models _ rule e e' e'' edge edge', inside'⟩

theorem add_sub_spec (state : saturation.State) (x c : Usize) (stateOk : StateOk.{u,v} t list keep state)
    (fact : SubOk.{u,v} t list x.val c.val) :
    ∃ r, saturation.add_sub state x c = .ok r ∧ ∀ state', r = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.add_sub]
  by_cases inside : x.val < state.subsumers.val.length
  · have lookup : state.subsumers.index_usize x = .ok state.subsumers.val[x.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases present : c ∈ state.subsumers.val[x.val].val
    · refine ⟨some state, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, has_spec, present],
        fun state' same => ?_⟩
      cases same; exact stateOk
    · obtain ⟨r1, run1, spec1⟩ := push_item_spec state.subsumers x c
      cases r1 with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, has_spec, present, run1],
          by simp⟩
      | some subsumers =>
        obtain ⟨old, new, at_old, newIs, subsumersIs⟩ := spec1 subsumers rfl
        have mem := mem_entries_push at_old newIs subsumersIs
        obtain ⟨r2, run2, spec2⟩ := push_fact_spec state.queue (.Sub x c)
        cases r2 with
        | none =>
          exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, has_spec, present, run1,
            run2], by simp⟩
        | some queue =>
          have queueIs := spec2 queue rfl
          refine ⟨some { state with subsumers := subsumers, queue := queue }, by simp [alloc.vec.Vec.len_val,
            UScalar.lt_equiv, inside, lookup, has_spec, present, run1, run2], fun state' same => ?_⟩
          cases same
          refine ⟨fun x' c' h => ?_, stateOk.out, stateOk.into, fun f h => ?_, stateOk.active⟩
          · rcases (mem _ _).mp h with h | ⟨rfl, rfl⟩
            · exact stateOk.subsumers x' c' h
            · exact fact
          · rw [queueIs] at h
            rcases List.mem_append.mp h with h | h
            · exact stateOk.queue f h
            · rw [List.mem_singleton] at h; subst h; exact fact
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside], by simp⟩

theorem add_link_spec (state : saturation.State) (x r y : Usize) (stateOk : StateOk.{u,v} t list keep state)
    (fact : LinkOk.{u,v} t list x.val r.val y.val) :
    ∃ o, saturation.add_link state x r y = .ok o ∧ ∀ state', o = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.add_link]
  by_cases inside : x.val < state.out.val.length
  · have lookup : state.out.index_usize x = .ok state.out.val[x.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases present : (r, y) ∈ state.out.val[x.val].val
    · refine ⟨some state, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, has_pair_spec, present],
        fun state' same => ?_⟩
      cases same; exact stateOk
    · have missing : saturation.has_pair state.out.val[x.val] r y = .ok false := by
        rw [has_pair_spec]; simp [present]
      obtain ⟨r1, run1, spec1⟩ := push_pair_spec state.out x (r, y)
      cases r1 with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, missing, run1], by simp⟩
      | some out =>
        obtain ⟨old, new, at_old, newIs, outIs⟩ := spec1 out rfl
        have mem := mem_entries_push at_old newIs outIs
        obtain ⟨r2, run2, spec2⟩ := push_pair_spec state.into y (r, x)
        cases r2 with
        | none =>
          exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, missing, run1, run2],
            by simp⟩
        | some into =>
          obtain ⟨old2, new2, at_old2, newIs2, intoIs⟩ := spec2 into rfl
          have mem2 := mem_entries_push at_old2 newIs2 intoIs
          obtain ⟨r3, run3, spec3⟩ := push_fact_spec state.queue (.Link x r y)
          cases r3 with
          | none =>
            exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, missing, run1, run2,
              run3], by simp⟩
          | some queue =>
            have queueIs := spec3 queue rfl
            refine ⟨some { state with out := out, into := into, queue := queue }, by simp [alloc.vec.Vec.len_val,
              UScalar.lt_equiv, inside, lookup, missing, run1, run2, run3], fun state' same => ?_⟩
            cases same
            refine ⟨stateOk.subsumers, fun x' r' y' h => ?_, fun y' r' x' h => ?_, fun f h => ?_, stateOk.active⟩
            · rcases (mem _ _).mp h with h | ⟨rfl, pair⟩
              · exact stateOk.out x' r' y' h
              · simp only [Prod.mk.injEq] at pair
                obtain ⟨rfl, rfl⟩ := pair
                exact fact
            · rcases (mem2 _ _).mp h with h | ⟨rfl, pair⟩
              · exact stateOk.into y' r' x' h
              · simp only [Prod.mk.injEq] at pair
                obtain ⟨rfl, rfl⟩ := pair
                exact fact
            · rw [queueIs] at h
              rcases List.mem_append.mp h with h | h
              · exact stateOk.queue f h
              · rw [List.mem_singleton] at h; subst h; exact fact
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside], by simp⟩

theorem activate_spec (state : saturation.State) (x top : Usize) (stateOk : StateOk.{u,v} t list keep state)
    (topAt : t.concepts.val[top.val]? = some .Top) :
    ∃ r, saturation.activate state x top = .ok r ∧
      ∀ state', r = some state' → StateOk.{u,v} t list (fun j => keep j ∨ j = x.val) state' := by
  rw [saturation.activate]
  by_cases inside : x.val < state.active.val.length
  · have lookup : state.active.index_usize x = .ok state.active.val[x.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases already : state.active.val[x.val] = true
    · refine ⟨some state, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, already],
        fun s same => ?_⟩
      cases same
      refine ⟨stateOk.subsumers, stateOk.out, stateOk.into, stateOk.queue, fun j h => ?_⟩
      rcases h with h | rfl
      · exact stateOk.active j h
      · rw [List.getElem?_eq_getElem inside, already]
    · have notYet : state.active.val[x.val] = false := by simpa using already
      have stateOk1 : StateOk.{u,v} t list (fun j => keep j ∨ j = x.val)
          { state with active := state.active.set x true } := by
        refine ⟨stateOk.subsumers, stateOk.out, stateOk.into, stateOk.queue, fun j h => ?_⟩
        simp only [alloc.vec.Vec.set_val_eq]
        rcases h with h | rfl
        · by_cases same : j = x.val
          · subst same; rw [List.getElem?_set_self inside]
          · rw [List.getElem?_set_ne (Ne.symm same)]; exact stateOk.active j h
        · rw [List.getElem?_set_self inside]
      obtain ⟨r1, run1, spec1⟩ := add_sub_spec _ x x stateOk1 (sub_refl x.val)
      cases r1 with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, notYet,
          alloc.vec.Vec.index_mut_usize, run1], by simp⟩
      | some state1 =>
        obtain ⟨r2, run2, spec2⟩ := add_sub_spec state1 x top (spec1 state1 rfl) (sub_top topAt)
        exact ⟨r2, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, notYet,
          alloc.vec.Vec.index_mut_usize, run1, run2], spec2⟩
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside], by simp⟩

end Steps

section Loops
variable {t : saturation.Table} {list : List saturation.Rule} {keep : Nat → Prop}

theorem into_length_spec (state : saturation.State) (x : Usize) : ∃ r, saturation.into_length state x = .ok r := by
  rw [saturation.into_length]
  by_cases inside : x.val < state.into.val.length
  · exact ⟨some (alloc.vec.Vec.len state.into.val[x.val]), by
      simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, alloc.vec.Vec.index_usize,
        List.getElem?_eq_getElem inside]⟩
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]⟩

theorem out_length_spec (state : saturation.State) (x : Usize) : ∃ r, saturation.out_length state x = .ok r := by
  rw [saturation.out_length]
  by_cases inside : x.val < state.out.val.length
  · exact ⟨some (alloc.vec.Vec.len state.out.val[x.val]), by
      simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, alloc.vec.Vec.index_usize,
        List.getElem?_eq_getElem inside]⟩
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]⟩

theorem subsumers_length_spec (state : saturation.State) (x : Usize) :
    ∃ r, saturation.subsumers_length state x = .ok r := by
  rw [saturation.subsumers_length]
  by_cases inside : x.val < state.subsumers.val.length
  · exact ⟨some (alloc.vec.Vec.len state.subsumers.val[x.val]), by
      simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, alloc.vec.Vec.index_usize,
        List.getElem?_eq_getElem inside]⟩
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]⟩

theorem bottom_back_spec (state : saturation.State) (x c index end' : Usize) (stateOk : StateOk.{u,v} t list keep state)
    (bottom : t.concepts.val[c.val]? = some .Bottom) (fact : SubOk.{u,v} t list x.val c.val) :
    ∃ r, saturation.bottom_back state x c index end' = .ok r ∧
      ∀ state', r = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.bottom_back]
  by_cases more : index.val < end'.val
  · by_cases inside : x.val < state.into.val.length
    · have lookup : state.into.index_usize x = .ok state.into.val[x.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      by_cases inside2 : index.val < state.into.val[x.val].val.length
      · have lookup2 : state.into.val[x.val].index_usize index = .ok state.into.val[x.val].val[index.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside2]
        have member := entry_mem state.into.val x.val index.val inside inside2
        rcases pairIs : state.into.val[x.val].val[index.val] with ⟨r', w⟩
        rw [pairIs] at member
        have link : LinkOk.{u,v} t list w.val r'.val x.val := stateOk.into x.val r' w member
        obtain ⟨r1, run1, spec1⟩ := add_sub_spec state w c stateOk
          (sub_of_link_bottom bottom (link_sub link fact) c.val)
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = index.val + 1 := by simpa using nextValue
        cases r1 with
        | none =>
          exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2, lookup2,
            pairIs, run1], by simp⟩
        | some state1 =>
          obtain ⟨r, run, spec⟩ := bottom_back_spec state1 x c next end' (spec1 state1 rfl) bottom fact
          exact ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2, lookup2, pairIs,
            run1, advance, run], spec⟩
      · exact ⟨some state, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2],
          fun s same => by cases same; exact stateOk⟩
    · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside], by simp⟩
  · exact ⟨some state, by simp [UScalar.lt_equiv, more], fun s same => by cases same; exact stateOk⟩
termination_by end'.val - index.val
decreasing_by omega

theorem told_from_spec (rules : saturation.Rules) (sound : IndexSound t.concepts.val list rules)
    (state : saturation.State) (x c index : Usize) (stateOk : StateOk.{u,v} t list keep state)
    (fact : SubOk.{u,v} t list x.val c.val) :
    ∃ r, saturation.told_from rules state x c index = .ok r ∧
      ∀ state', r = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.told_from]
  by_cases inside : c.val < rules.told.val.length
  · have lookup : rules.told.index_usize c = .ok rules.told.val[c.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have measure : (entries rules.told.val c.val).length = rules.told.val[c.val].val.length := by
      rw [entries_lookup (List.getElem?_eq_getElem inside)]
    by_cases more : index.val < rules.told.val[c.val].val.length
    · have lookup2 : rules.told.val[c.val].index_usize index = .ok rules.told.val[c.val].val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
      have member := entry_mem rules.told.val c.val index.val inside more
      obtain ⟨r1, run1, spec1⟩ := add_sub_spec state x _ stateOk (sub_rule (sound.told c _ member) fact)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      cases r1 with
      | none =>
        exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, lookup2, run1], by simp⟩
      | some state1 =>
        obtain ⟨r, run, spec⟩ := told_from_spec rules sound state1 x c next (spec1 state1 rfl) fact
        exact ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, lookup2, run1, advance,
          run], spec⟩
    · exact ⟨some state, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more],
        fun s same => by cases same; exact stateOk⟩
  · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside], by simp⟩
termination_by (entries rules.told.val c.val).length - index.val
decreasing_by omega

theorem conjunctions_from_spec (ok : TableOk t) (rules : saturation.Rules)
    (sound : IndexSound t.concepts.val list rules) (state : saturation.State) (x c index : Usize)
    (stateOk : StateOk.{u,v} t list keep state) (fact : SubOk.{u,v} t list x.val c.val) :
    ∃ r, saturation.conjunctions_from rules state x c index = .ok r ∧
      ∀ state', r = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.conjunctions_from]
  by_cases inside : c.val < rules.conjunctions.val.length
  · have lookup : rules.conjunctions.index_usize c = .ok rules.conjunctions.val[c.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have measure : (entries rules.conjunctions.val c.val).length = rules.conjunctions.val[c.val].val.length := by
      rw [entries_lookup (List.getElem?_eq_getElem inside)]
    by_cases more : index.val < rules.conjunctions.val[c.val].val.length
    · by_cases insideX : x.val < state.subsumers.val.length
      · have lookup2 : rules.conjunctions.val[c.val].index_usize index =
            .ok rules.conjunctions.val[c.val].val[index.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
        have lookup3 : state.subsumers.index_usize x = .ok state.subsumers.val[x.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem insideX]
        have member := entry_mem rules.conjunctions.val c.val index.val inside more
        rcases pairIs : rules.conjunctions.val[c.val].val[index.val] with ⟨other, both⟩
        rw [pairIs] at member
        have shape := sound.parts.1 c other both member
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = index.val + 1 := by simpa using nextValue
        by_cases present : other ∈ state.subsumers.val[x.val].val
        · have otherOk : SubOk.{u,v} t list x.val other.val := stateOk.subsumers x.val other (by
            rw [entries_lookup (List.getElem?_eq_getElem insideX)]; exact present)
          obtain ⟨r1, run1, spec1⟩ := add_sub_spec state x both stateOk (sub_conj ok shape fact otherOk)
          cases r1 with
          | none =>
            exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, insideX, lookup2,
              lookup3, pairIs, has_spec, present, run1], by simp⟩
          | some state1 =>
            obtain ⟨r, run, spec⟩ := conjunctions_from_spec ok rules sound state1 x c next (spec1 state1 rfl) fact
            exact ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, insideX, lookup2,
              lookup3, pairIs, has_spec, present, run1, advance, run], spec⟩
        · obtain ⟨r, run, spec⟩ := conjunctions_from_spec ok rules sound state x c next stateOk fact
          exact ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, insideX, lookup2,
            lookup3, pairIs, has_spec, present, advance, run], spec⟩
      · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, insideX], by simp⟩
    · exact ⟨some state, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more],
        fun s same => by cases same; exact stateOk⟩
  · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside], by simp⟩
termination_by (entries rules.conjunctions.val c.val).length - index.val
decreasing_by all_goals omega

theorem existentials_from_spec (ok : TableOk t) (rules : saturation.Rules)
    (sound : IndexSound t.concepts.val list rules) (state : saturation.State) (w c r index : Usize)
    (stateOk : StateOk.{u,v} t list keep state) (link : LinkOk.{u,v} t list w.val r.val c.val) :
    ∃ o, saturation.existentials_from rules state w c r index = .ok o ∧
      ∀ state', o = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.existentials_from]
  by_cases inside : c.val < rules.existentials.val.length
  · have lookup : rules.existentials.index_usize c = .ok rules.existentials.val[c.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have measure : (entries rules.existentials.val c.val).length = rules.existentials.val[c.val].val.length := by
      rw [entries_lookup (List.getElem?_eq_getElem inside)]
    by_cases more : index.val < rules.existentials.val[c.val].val.length
    · have lookup2 : rules.existentials.val[c.val].index_usize index =
          .ok rules.existentials.val[c.val].val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
      have member := entry_mem rules.existentials.val c.val index.val inside more
      rcases pairIs : rules.existentials.val[c.val].val[index.val] with ⟨s, e⟩
      rw [pairIs] at member
      have shape := sound.parts.2 c s e member
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      by_cases same : s = r
      · rw [same] at shape
        obtain ⟨r1, run1, spec1⟩ := add_sub_spec state w e stateOk (sub_exists_back ok shape link)
        cases r1 with
        | none =>
          exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, lookup2, pairIs, same,
            run1], by simp⟩
        | some state1 =>
          obtain ⟨o, run, spec⟩ := existentials_from_spec ok rules sound state1 w c r next (spec1 state1 rfl) link
          exact ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, lookup2, pairIs, same,
            run1, advance, run], spec⟩
      · obtain ⟨o, run, spec⟩ := existentials_from_spec ok rules sound state w c r next stateOk link
        exact ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, lookup2, pairIs, same,
          advance, run], spec⟩
    · exact ⟨some state, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more],
        fun s same => by cases same; exact stateOk⟩
  · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside], by simp⟩
termination_by (entries rules.existentials.val c.val).length - index.val
decreasing_by all_goals omega

theorem existentials_back_spec (ok : TableOk t) (rules : saturation.Rules)
    (sound : IndexSound t.concepts.val list rules) (state : saturation.State) (x c index end' : Usize)
    (stateOk : StateOk.{u,v} t list keep state) (fact : SubOk.{u,v} t list x.val c.val) :
    ∃ r, saturation.existentials_back rules state x c index end' = .ok r ∧
      ∀ state', r = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.existentials_back]
  by_cases more : index.val < end'.val
  · by_cases inside : x.val < state.into.val.length
    · have lookup : state.into.index_usize x = .ok state.into.val[x.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      by_cases inside2 : index.val < state.into.val[x.val].val.length
      · have lookup2 : state.into.val[x.val].index_usize index = .ok state.into.val[x.val].val[index.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside2]
        have member := entry_mem state.into.val x.val index.val inside inside2
        rcases pairIs : state.into.val[x.val].val[index.val] with ⟨r', w⟩
        rw [pairIs] at member
        have link : LinkOk.{u,v} t list w.val r'.val x.val := stateOk.into x.val r' w member
        obtain ⟨r1, run1, spec1⟩ := existentials_from_spec ok rules sound state w c r' 0#usize stateOk
          (link_sub link fact)
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = index.val + 1 := by simpa using nextValue
        cases r1 with
        | none =>
          exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2, lookup2,
            pairIs, run1], by simp⟩
        | some state1 =>
          obtain ⟨r, run, spec⟩ := existentials_back_spec ok rules sound state1 x c next end' (spec1 state1 rfl) fact
          exact ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2, lookup2, pairIs,
            run1, advance, run], spec⟩
      · exact ⟨some state, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2],
          fun s same => by cases same; exact stateOk⟩
    · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside], by simp⟩
  · exact ⟨some state, by simp [UScalar.lt_equiv, more], fun s same => by cases same; exact stateOk⟩
termination_by end'.val - index.val
decreasing_by omega

/-- The rules every new subsumer goes through: told subsumers, conjunctions and
    existential restrictions back along the links into the context. -/
theorem tail_parts (ok : TableOk t) (rules : saturation.Rules) (sound : IndexSound t.concepts.val list rules)
    (state : saturation.State) (x c : Usize) (stateOk : StateOk.{u,v} t list keep state)
    (fact : SubOk.{u,v} t list x.val c.val) :
    ∃ r1, saturation.told_from rules state x c 0#usize = .ok r1 ∧ ∀ s1, r1 = some s1 →
      ∃ r2, saturation.conjunctions_from rules s1 x c 0#usize = .ok r2 ∧ ∀ s2, r2 = some s2 →
        ∃ r3, saturation.into_length s2 x = .ok r3 ∧ ∀ e, r3 = some e →
          ∃ r4, saturation.existentials_back rules s2 x c 0#usize e = .ok r4 ∧
            ∀ s4, r4 = some s4 → StateOk.{u,v} t list keep s4 := by
  obtain ⟨r1, run1, spec1⟩ := told_from_spec rules sound state x c 0#usize stateOk fact
  refine ⟨r1, run1, fun s1 same1 => ?_⟩
  obtain ⟨r2, run2, spec2⟩ := conjunctions_from_spec ok rules sound s1 x c 0#usize (spec1 s1 same1) fact
  refine ⟨r2, run2, fun s2 same2 => ?_⟩
  obtain ⟨r3, run3⟩ := into_length_spec s2 x
  exact ⟨r3, run3, fun e _ => existentials_back_spec ok rules sound s2 x c 0#usize e (spec2 s2 same2) fact⟩

end Loops

section Processing
variable {t : saturation.Table} {list : List saturation.Rule} {keep : Nat → Prop}

theorem process_sub_spec (ok : TableOk t) (rules : saturation.Rules) (sound : IndexSound t.concepts.val list rules)
    (state : saturation.State) (x c : Usize) (stateOk : StateOk.{u,v} t list keep state)
    (fact : SubOk.{u,v} t list x.val c.val) :
    ∃ r, saturation.process_sub rules t.concepts state x c = .ok r ∧
      ∀ state', r = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.process_sub]
  by_cases inside : c.val < t.concepts.val.length
  · have conceptLookup : t.concepts.index_usize c = .ok t.concepts.val[c.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have at_c : t.concepts.val[c.val]? = some t.concepts.val[c.val] := List.getElem?_eq_getElem inside
    cases concept : t.concepts.val[c.val] with
    | Top =>
      obtain ⟨r1, run1, rest1⟩ := tail_parts ok rules sound state x c stateOk fact
      cases r1 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, run1],
          by simp⟩
      | some s1 =>
        obtain ⟨r2, run2, rest2⟩ := rest1 s1 rfl
        cases r2 with
        | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, run1,
            run2], by simp⟩
        | some s2 =>
          obtain ⟨r3, run3, rest3⟩ := rest2 s2 rfl
          cases r3 with
          | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept,
              run1, run2, run3], by simp⟩
          | some e =>
            obtain ⟨r4, run4, spec4⟩ := rest3 e rfl
            exact ⟨r4, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, run1, run2,
              run3, run4], spec4⟩
    | Atom k =>
      obtain ⟨r1, run1, rest1⟩ := tail_parts ok rules sound state x c stateOk fact
      cases r1 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, run1],
          by simp⟩
      | some s1 =>
        obtain ⟨r2, run2, rest2⟩ := rest1 s1 rfl
        cases r2 with
        | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, run1,
            run2], by simp⟩
        | some s2 =>
          obtain ⟨r3, run3, rest3⟩ := rest2 s2 rfl
          cases r3 with
          | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept,
              run1, run2, run3], by simp⟩
          | some e =>
            obtain ⟨r4, run4, spec4⟩ := rest3 e rfl
            exact ⟨r4, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, run1, run2,
              run3, run4], spec4⟩
    | Bottom =>
      rw [concept] at at_c
      obtain ⟨o, runO⟩ := into_length_spec state x
      cases o with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, runO],
          by simp⟩
      | some e0 =>
        obtain ⟨b, runB, specB⟩ := bottom_back_spec state x c 0#usize e0 stateOk at_c fact
        cases b with
        | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, runO,
            runB], by simp⟩
        | some s0 =>
          obtain ⟨r1, run1, rest1⟩ := tail_parts ok rules sound s0 x c (specB s0 rfl) fact
          cases r1 with
          | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept,
              runO, runB, run1], by simp⟩
          | some s1 =>
            obtain ⟨r2, run2, rest2⟩ := rest1 s1 rfl
            cases r2 with
            | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept,
                runO, runB, run1, run2], by simp⟩
            | some s2 =>
              obtain ⟨r3, run3, rest3⟩ := rest2 s2 rfl
              cases r3 with
              | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept,
                  runO, runB, run1, run2, run3], by simp⟩
              | some e =>
                obtain ⟨r4, run4, spec4⟩ := rest3 e rfl
                exact ⟨r4, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, runO,
                  runB, run1, run2, run3, run4], spec4⟩
    | And a b =>
      rw [concept] at at_c
      obtain ⟨aOk, bOk⟩ := sub_and ok at_c fact
      obtain ⟨p, runP, specP⟩ := add_sub_spec state x a stateOk aOk
      cases p with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, runP],
          by simp⟩
      | some sa =>
        obtain ⟨q, runQ, specQ⟩ := add_sub_spec sa x b (specP sa rfl) bOk
        cases q with
        | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, runP,
            runQ], by simp⟩
        | some s0 =>
          obtain ⟨r1, run1, rest1⟩ := tail_parts ok rules sound s0 x c (specQ s0 rfl) fact
          cases r1 with
          | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept,
              runP, runQ, run1], by simp⟩
          | some s1 =>
            obtain ⟨r2, run2, rest2⟩ := rest1 s1 rfl
            cases r2 with
            | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept,
                runP, runQ, run1, run2], by simp⟩
            | some s2 =>
              obtain ⟨r3, run3, rest3⟩ := rest2 s2 rfl
              cases r3 with
              | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept,
                  runP, runQ, run1, run2, run3], by simp⟩
              | some e =>
                obtain ⟨r4, run4, spec4⟩ := rest3 e rfl
                exact ⟨r4, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, runP,
                  runQ, run1, run2, run3, run4], spec4⟩
    | Exists r y =>
      rw [concept] at at_c
      obtain ⟨p, runP, specP⟩ := add_link_spec state x r y stateOk (link_of_exists ok at_c fact)
      cases p with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, runP],
          by simp⟩
      | some s0 =>
        obtain ⟨r1, run1, rest1⟩ := tail_parts ok rules sound s0 x c (specP s0 rfl) fact
        cases r1 with
        | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept,
            runP, run1], by simp⟩
        | some s1 =>
          obtain ⟨r2, run2, rest2⟩ := rest1 s1 rfl
          cases r2 with
          | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept,
              runP, run1, run2], by simp⟩
          | some s2 =>
            obtain ⟨r3, run3, rest3⟩ := rest2 s2 rfl
            cases r3 with
            | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept,
                runP, run1, run2, run3], by simp⟩
            | some e =>
              obtain ⟨r4, run4, spec4⟩ := rest3 e rfl
              exact ⟨r4, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, conceptLookup, concept, runP,
                run1, run2, run3, run4], spec4⟩
  · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside], by simp⟩

theorem targets_from_spec (ok : TableOk t) (rules : saturation.Rules) (sound : IndexSound t.concepts.val list rules)
    (bottomAt : t.concepts.val[rules.bottom.val]? = some .Bottom) (state : saturation.State)
    (x r y index end' : Usize) (stateOk : StateOk.{u,v} t list keep state) (link : LinkOk.{u,v} t list x.val r.val y.val) :
    ∃ o, saturation.targets_from rules state x r y index end' = .ok o ∧
      ∀ state', o = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.targets_from]
  by_cases more : index.val < end'.val
  · by_cases inside : y.val < state.subsumers.val.length
    · have lookup : state.subsumers.index_usize y = .ok state.subsumers.val[y.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      by_cases inside2 : index.val < state.subsumers.val[y.val].val.length
      · have lookup2 : state.subsumers.val[y.val].index_usize index =
            .ok state.subsumers.val[y.val].val[index.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside2]
        have member := entry_mem state.subsumers.val y.val index.val inside inside2
        have linkC : LinkOk.{u,v} t list x.val r.val state.subsumers.val[y.val].val[index.val].val :=
          link_sub link (stateOk.subsumers y.val _ member)
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = index.val + 1 := by simpa using nextValue
        by_cases isBottom : state.subsumers.val[y.val].val[index.val] = rules.bottom
        · have linkB : LinkOk.{u,v} t list x.val r.val rules.bottom.val := by rw [← isBottom]; exact linkC
          obtain ⟨r1, run1, spec1⟩ := add_sub_spec state x rules.bottom stateOk
            (sub_of_link_bottom bottomAt linkB _)
          cases r1 with
          | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2,
              lookup2, isBottom, run1], by simp⟩
          | some s1 =>
            obtain ⟨r2, run2, spec2⟩ := existentials_from_spec ok rules sound s1 x rules.bottom r 0#usize
              (spec1 s1 rfl) linkB
            cases r2 with
            | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2,
                lookup2, isBottom, run1, run2], by simp⟩
            | some s2 =>
              obtain ⟨o, run, spec⟩ := targets_from_spec ok rules sound bottomAt s2 x r y next end' (spec2 s2 rfl) link
              exact ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2, lookup2,
                isBottom, run1, run2, advance, run], spec⟩
        · obtain ⟨r2, run2, spec2⟩ := existentials_from_spec ok rules sound state x _ r 0#usize stateOk linkC
          cases r2 with
          | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2,
              lookup2, isBottom, run2], by simp⟩
          | some s2 =>
            obtain ⟨o, run, spec⟩ := targets_from_spec ok rules sound bottomAt s2 x r y next end' (spec2 s2 rfl) link
            exact ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2, lookup2,
              isBottom, run2, advance, run], spec⟩
      · exact ⟨some state, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2],
          fun s same => by cases same; exact stateOk⟩
    · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside], by simp⟩
  · exact ⟨some state, by simp [UScalar.lt_equiv, more], fun s same => by cases same; exact stateOk⟩
termination_by end'.val - index.val
decreasing_by all_goals omega

theorem supers_from_spec (rules : saturation.Rules) (sound : IndexSound t.concepts.val list rules)
    (state : saturation.State) (x r y index : Usize) (stateOk : StateOk.{u,v} t list keep state)
    (link : LinkOk.{u,v} t list x.val r.val y.val) :
    ∃ o, saturation.supers_from rules state x r y index = .ok o ∧
      ∀ state', o = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.supers_from]
  by_cases inside : r.val < rules.supers.val.length
  · have lookup : rules.supers.index_usize r = .ok rules.supers.val[r.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have measure : (entries rules.supers.val r.val).length = rules.supers.val[r.val].val.length := by
      rw [entries_lookup (List.getElem?_eq_getElem inside)]
    by_cases more : index.val < rules.supers.val[r.val].val.length
    · have lookup2 : rules.supers.val[r.val].index_usize index = .ok rules.supers.val[r.val].val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
      have member := entry_mem rules.supers.val r.val index.val inside more
      obtain ⟨r1, run1, spec1⟩ := add_link_spec state x _ y stateOk (link_super (sound.supers r _ member) link)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      cases r1 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, lookup2, run1],
          by simp⟩
      | some s1 =>
        obtain ⟨o, run, spec⟩ := supers_from_spec rules sound s1 x r y next (spec1 s1 rfl) link
        exact ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, lookup2, run1, advance, run],
          spec⟩
    · exact ⟨some state, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more],
        fun s same => by cases same; exact stateOk⟩
  · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside], by simp⟩
termination_by (entries rules.supers.val r.val).length - index.val
decreasing_by omega

theorem chain_out_spec (state : saturation.State) (x y second result index end' : Usize)
    (stateOk : StateOk.{u,v} t list keep state) {r : Usize} (rule : saturation.Rule.Chain r second result ∈ list)
    (link : LinkOk.{u,v} t list x.val r.val y.val) :
    ∃ o, saturation.chain_out state x y second result index end' = .ok o ∧
      ∀ state', o = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.chain_out]
  by_cases more : index.val < end'.val
  · by_cases inside : y.val < state.out.val.length
    · have lookup : state.out.index_usize y = .ok state.out.val[y.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      by_cases inside2 : index.val < state.out.val[y.val].val.length
      · have lookup2 : state.out.val[y.val].index_usize index = .ok state.out.val[y.val].val[index.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside2]
        have member := entry_mem state.out.val y.val index.val inside inside2
        rcases pairIs : state.out.val[y.val].val[index.val] with ⟨role, z⟩
        rw [pairIs] at member
        have edge : LinkOk.{u,v} t list y.val role.val z.val := stateOk.out y.val role z member
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = index.val + 1 := by simpa using nextValue
        by_cases same : role = second
        · rw [same] at edge
          obtain ⟨r1, run1, spec1⟩ := add_link_spec state x result z stateOk (link_chain rule link edge)
          cases r1 with
          | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2,
              lookup2, pairIs, same, run1], by simp⟩
          | some s1 =>
            obtain ⟨o, run, spec⟩ := chain_out_spec s1 x y second result next end' (spec1 s1 rfl) rule link
            exact ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2, lookup2,
              pairIs, same, run1, advance, run], spec⟩
        · obtain ⟨o, run, spec⟩ := chain_out_spec state x y second result next end' stateOk rule link
          exact ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2, lookup2, pairIs,
            same, advance, run], spec⟩
      · exact ⟨some state, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2],
          fun s same => by cases same; exact stateOk⟩
    · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside], by simp⟩
  · exact ⟨some state, by simp [UScalar.lt_equiv, more], fun s same => by cases same; exact stateOk⟩
termination_by end'.val - index.val
decreasing_by all_goals omega

theorem firsts_from_spec (rules : saturation.Rules) (sound : IndexSound t.concepts.val list rules)
    (state : saturation.State) (x r y index : Usize) (stateOk : StateOk.{u,v} t list keep state)
    (link : LinkOk.{u,v} t list x.val r.val y.val) :
    ∃ o, saturation.firsts_from rules state x r y index = .ok o ∧
      ∀ state', o = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.firsts_from]
  by_cases inside : r.val < rules.firsts.val.length
  · have lookup : rules.firsts.index_usize r = .ok rules.firsts.val[r.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have measure : (entries rules.firsts.val r.val).length = rules.firsts.val[r.val].val.length := by
      rw [entries_lookup (List.getElem?_eq_getElem inside)]
    by_cases more : index.val < rules.firsts.val[r.val].val.length
    · have lookup2 : rules.firsts.val[r.val].index_usize index = .ok rules.firsts.val[r.val].val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
      have member := entry_mem rules.firsts.val r.val index.val inside more
      rcases pairIs : rules.firsts.val[r.val].val[index.val] with ⟨second, result⟩
      rw [pairIs] at member
      have rule := sound.firsts r second result member
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨e, runE⟩ := out_length_spec state y
      cases e with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, lookup2, pairIs,
          runE], by simp⟩
      | some e =>
        obtain ⟨r1, run1, spec1⟩ := chain_out_spec state x y second result 0#usize e stateOk rule link
        cases r1 with
        | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, lookup2, pairIs,
            runE, run1], by simp⟩
        | some s1 =>
          obtain ⟨o, run, spec⟩ := firsts_from_spec rules sound s1 x r y next (spec1 s1 rfl) link
          exact ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, lookup2, pairIs, runE,
            run1, advance, run], spec⟩
    · exact ⟨some state, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more],
        fun s same => by cases same; exact stateOk⟩
  · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside], by simp⟩
termination_by (entries rules.firsts.val r.val).length - index.val
decreasing_by omega

theorem chain_in_spec (state : saturation.State) (x y first result index end' : Usize)
    (stateOk : StateOk.{u,v} t list keep state) {r : Usize} (rule : saturation.Rule.Chain first r result ∈ list)
    (link : LinkOk.{u,v} t list x.val r.val y.val) :
    ∃ o, saturation.chain_in state x y first result index end' = .ok o ∧
      ∀ state', o = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.chain_in]
  by_cases more : index.val < end'.val
  · by_cases inside : x.val < state.into.val.length
    · have lookup : state.into.index_usize x = .ok state.into.val[x.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      by_cases inside2 : index.val < state.into.val[x.val].val.length
      · have lookup2 : state.into.val[x.val].index_usize index = .ok state.into.val[x.val].val[index.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside2]
        have member := entry_mem state.into.val x.val index.val inside inside2
        rcases pairIs : state.into.val[x.val].val[index.val] with ⟨role, w⟩
        rw [pairIs] at member
        have edge : LinkOk.{u,v} t list w.val role.val x.val := stateOk.into x.val role w member
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = index.val + 1 := by simpa using nextValue
        by_cases same : role = first
        · rw [same] at edge
          obtain ⟨r1, run1, spec1⟩ := add_link_spec state w result y stateOk (link_chain rule edge link)
          cases r1 with
          | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2,
              lookup2, pairIs, same, run1], by simp⟩
          | some s1 =>
            obtain ⟨o, run, spec⟩ := chain_in_spec s1 x y first result next end' (spec1 s1 rfl) rule link
            exact ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2, lookup2,
              pairIs, same, run1, advance, run], spec⟩
        · obtain ⟨o, run, spec⟩ := chain_in_spec state x y first result next end' stateOk rule link
          exact ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2, lookup2, pairIs,
            same, advance, run], spec⟩
      · exact ⟨some state, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside, lookup, inside2],
          fun s same => by cases same; exact stateOk⟩
    · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, inside], by simp⟩
  · exact ⟨some state, by simp [UScalar.lt_equiv, more], fun s same => by cases same; exact stateOk⟩
termination_by end'.val - index.val
decreasing_by all_goals omega

theorem seconds_from_spec (rules : saturation.Rules) (sound : IndexSound t.concepts.val list rules)
    (state : saturation.State) (x r y index : Usize) (stateOk : StateOk.{u,v} t list keep state)
    (link : LinkOk.{u,v} t list x.val r.val y.val) :
    ∃ o, saturation.seconds_from rules state x r y index = .ok o ∧
      ∀ state', o = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.seconds_from]
  by_cases inside : r.val < rules.seconds.val.length
  · have lookup : rules.seconds.index_usize r = .ok rules.seconds.val[r.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have measure : (entries rules.seconds.val r.val).length = rules.seconds.val[r.val].val.length := by
      rw [entries_lookup (List.getElem?_eq_getElem inside)]
    by_cases more : index.val < rules.seconds.val[r.val].val.length
    · have lookup2 : rules.seconds.val[r.val].index_usize index = .ok rules.seconds.val[r.val].val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
      have member := entry_mem rules.seconds.val r.val index.val inside more
      rcases pairIs : rules.seconds.val[r.val].val[index.val] with ⟨first, result⟩
      rw [pairIs] at member
      have rule := sound.seconds r first result member
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨e, runE⟩ := into_length_spec state x
      cases e with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, lookup2, pairIs,
          runE], by simp⟩
      | some e =>
        obtain ⟨r1, run1, spec1⟩ := chain_in_spec state x y first result 0#usize e stateOk rule link
        cases r1 with
        | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, lookup2, pairIs,
            runE, run1], by simp⟩
        | some s1 =>
          obtain ⟨o, run, spec⟩ := seconds_from_spec rules sound s1 x r y next (spec1 s1 rfl) link
          exact ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more, lookup2, pairIs, runE,
            run1, advance, run], spec⟩
    · exact ⟨some state, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, more],
        fun s same => by cases same; exact stateOk⟩
  · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside], by simp⟩
termination_by (entries rules.seconds.val r.val).length - index.val
decreasing_by omega

theorem process_link_spec (ok : TableOk t) (rules : saturation.Rules) (sound : IndexSound t.concepts.val list rules)
    (topAt : t.concepts.val[rules.top.val]? = some .Top) (bottomAt : t.concepts.val[rules.bottom.val]? = some .Bottom)
    (state : saturation.State) (x r y : Usize) (stateOk : StateOk.{u,v} t list keep state)
    (link : LinkOk.{u,v} t list x.val r.val y.val) :
    ∃ o, saturation.process_link rules state x r y = .ok o ∧
      ∀ state', o = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.process_link]
  obtain ⟨r1, run1, spec1⟩ := activate_spec state y rules.top stateOk topAt
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some s1 =>
    obtain ⟨e, runE⟩ := subsumers_length_spec s1 y
    cases e with
    | none => exact ⟨none, by simp [run1, runE], by simp⟩
    | some e =>
      obtain ⟨r2, run2, spec2⟩ := targets_from_spec ok rules sound bottomAt s1 x r y 0#usize e
        (state_ok_weaken (spec1 s1 rfl) (fun j h => Or.inl h)) link
      cases r2 with
      | none => exact ⟨none, by simp [run1, runE, run2], by simp⟩
      | some s2 =>
        obtain ⟨r3, run3, spec3⟩ := supers_from_spec rules sound s2 x r y 0#usize (spec2 s2 rfl) link
        cases r3 with
        | none => exact ⟨none, by simp [run1, runE, run2, run3], by simp⟩
        | some s3 =>
          obtain ⟨r4, run4, spec4⟩ := firsts_from_spec rules sound s3 x r y 0#usize (spec3 s3 rfl) link
          cases r4 with
          | none => exact ⟨none, by simp [run1, runE, run2, run3, run4], by simp⟩
          | some s4 =>
            obtain ⟨r5, run5, spec5⟩ := seconds_from_spec rules sound s4 x r y 0#usize (spec4 s4 rfl) link
            exact ⟨r5, by simp [run1, runE, run2, run3, run4, run5], spec5⟩

theorem saturate_spec (ok : TableOk t) (rules : saturation.Rules) (sound : IndexSound t.concepts.val list rules)
    (topAt : t.concepts.val[rules.top.val]? = some .Top) (bottomAt : t.concepts.val[rules.bottom.val]? = some .Bottom)
    (state : saturation.State) (fuel : Usize) (stateOk : StateOk.{u,v} t list keep state) :
    ∃ o, saturation.saturate rules t.concepts state fuel = .ok o ∧
      ∀ state', o = some state' → StateOk.{u,v} t list keep state' := by
  rw [saturation.saturate]
  by_cases more : state.next.val < state.queue.val.length
  · by_cases empty : fuel.val = 0
    · have zero : fuel = 0#usize := UScalar.eq_of_val_eq (by simp [empty])
      exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, zero], by simp⟩
    · have nonzero : ¬ fuel = 0#usize := fun same => empty (by simp [same])
      have lookup : state.queue.index_usize state.next = .ok state.queue.val[state.next.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
      have factOk := stateOk.queue _ (List.getElem_mem more)
      obtain ⟨next, advance, _⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := state.next) (y := 1#usize) (by scalar_tac))
      obtain ⟨less, minus, lessValue⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := fuel) (y := 1#usize) (by scalar_tac))
      have lessIs : less.val = fuel.val - 1 := by have := lessValue; simp at this; exact this.1
      have stateOk0 : StateOk.{u,v} t list keep { state with next := next } :=
        ⟨stateOk.subsumers, stateOk.out, stateOk.into, stateOk.queue, stateOk.active⟩
      cases fact : state.queue.val[state.next.val] with
      | Sub x c =>
        rw [fact] at factOk
        obtain ⟨r1, run1, spec1⟩ := process_sub_spec ok rules sound { state with next := next } x c stateOk0 factOk
        cases r1 with
        | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, nonzero, lookup, fact,
            advance, run1], by simp⟩
        | some s1 =>
          obtain ⟨o, run, spec⟩ := saturate_spec ok rules sound topAt bottomAt s1 less (spec1 s1 rfl)
          exact ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, nonzero, lookup, fact, advance, run1,
            minus, run], spec⟩
      | Link x r y =>
        rw [fact] at factOk
        obtain ⟨r1, run1, spec1⟩ := process_link_spec ok rules sound topAt bottomAt { state with next := next } x r y
          stateOk0 factOk
        cases r1 with
        | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, nonzero, lookup, fact,
            advance, run1], by simp⟩
        | some s1 =>
          obtain ⟨o, run, spec⟩ := saturate_spec ok rules sound topAt bottomAt s1 less (spec1 s1 rfl)
          exact ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, nonzero, lookup, fact, advance, run1,
            minus, run], spec⟩
  · exact ⟨some state, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more],
      fun s same => by cases same; exact stateOk⟩
termination_by fuel.val
decreasing_by all_goals omega

theorem activate_all_spec (kept : Nat → Prop) (state : saturation.State) (ids : alloc.vec.Vec Usize)
    (top index : Usize) (stateOk : StateOk.{u,v} t list kept state) (topAt : t.concepts.val[top.val]? = some .Top) :
    ∃ o, saturation.activate_all state ids top index = .ok o ∧
      ∀ state', o = some state' → StateOk.{u,v} t list
        (fun j => kept j ∨ ∃ (i : Nat) (id : Usize), index.val ≤ i ∧ ids.val[i]? = some id ∧ id.val = j) state' := by
  rw [saturation.activate_all]
  by_cases more : index.val < ids.val.length
  · have lookup : ids.index_usize index = .ok ids.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨r1, run1, spec1⟩ := activate_spec state ids.val[index.val] top stateOk topAt
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, run1], by simp⟩
    | some s1 =>
      obtain ⟨o, run, spec⟩ := activate_all_spec _ s1 ids top next (spec1 s1 rfl) topAt
      refine ⟨o, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, run1, advance, run],
        fun state' same => state_ok_weaken (spec state' same) (fun j h => ?_)⟩
      rcases h with h | ⟨i, id, low, at_i, rfl⟩
      · exact Or.inl (Or.inl h)
      · by_cases here : i = index.val
        · subst here
          rw [List.getElem?_eq_getElem more] at at_i
          cases at_i
          exact Or.inl (Or.inr rfl)
        · exact Or.inr ⟨i, id, by omega, at_i, rfl⟩
  · refine ⟨some state, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more],
      fun s same => ?_⟩
    cases same
    refine state_ok_weaken stateOk (fun j h => ?_)
    rcases h with h | ⟨i, id, low, at_i, rfl⟩
    · exact h
    · have := (List.getElem?_eq_some_iff.mp at_i).1
      omega
termination_by ids.val.length - index.val
decreasing_by omega

end Processing

/-! ### The final check -/

/-- A subsumer `c` of a context with subsumers `list` and links `links` is
    closed under the rules: its parts and link are there, and so are its told
    subsumers and the conjunctions it completes. -/
def SubsumerClosed (rules : saturation.Rules) (concepts : List saturation.Concept) (list : List Usize)
    (links : List (Usize × Usize)) (c : Usize) : Prop :=
  c.val < concepts.length ∧
  (∀ a b, concepts[c.val]? = some (.And a b) → a ∈ list ∧ b ∈ list) ∧
  (∀ r y, concepts[c.val]? = some (.Exists r y) → (r, y) ∈ links) ∧
  (∀ d ∈ entries rules.told.val c.val, d ∈ list) ∧
  (∀ p ∈ entries rules.conjunctions.val c.val, p.1 ∈ list → p.2 ∈ list)

/-- The link `x r y` leads to a context, carries `owl:Nothing` and the
    existential restrictions back, and is closed under inclusions and chains. -/
def LinkClosed (rules : saturation.Rules) (state : saturation.State) (x r y : Usize) : Prop :=
  y.val < state.subsumers.val.length ∧ state.active.val[y.val]? = some true ∧
  (rules.bottom ∈ entries state.subsumers.val y.val → rules.bottom ∈ entries state.subsumers.val x.val) ∧
  (∀ c ∈ entries state.subsumers.val y.val, ∀ p ∈ entries rules.existentials.val c.val, p.1 = r →
    p.2 ∈ entries state.subsumers.val x.val) ∧
  (∀ s ∈ entries rules.supers.val r.val, (s, y) ∈ entries state.out.val x.val) ∧
  (∀ p ∈ entries rules.firsts.val r.val, ∀ q ∈ entries state.out.val y.val, q.1 = p.1 →
    (p.2, q.2) ∈ entries state.out.val x.val)

/-- A context starts from itself and `owl:Thing`, and its subsumers and links are closed. -/
def ContextClosed (rules : saturation.Rules) (concepts : List saturation.Concept) (state : saturation.State)
    (x : Usize) : Prop :=
  (state.active.val[x.val]? = some true →
    x ∈ entries state.subsumers.val x.val ∧ rules.top ∈ entries state.subsumers.val x.val) ∧
  (∀ c ∈ entries state.subsumers.val x.val,
    SubsumerClosed rules concepts (entries state.subsumers.val x.val) (entries state.out.val x.val) c) ∧
  ∀ p ∈ entries state.out.val x.val, LinkClosed rules state x p.1 p.2

/-- What an accepting final check guarantees. -/
structure Closure (rules : saturation.Rules) (concepts : List saturation.Concept) (state : saturation.State) :
    Prop where
  subsumersLength : state.subsumers.val.length = concepts.length
  activeLength : state.active.val.length = concepts.length
  outLength : state.out.val.length = concepts.length
  top : rules.top.val < concepts.length
  bottom : rules.bottom.val < concepts.length
  contexts : ∀ x : Usize, x.val < concepts.length → ContextClosed rules concepts state x

theorem told_closed_spec (told list : alloc.vec.Vec Usize) (index : Usize) :
    ∃ b, saturation.told_closed told list index = .ok b ∧
      (b = true → ∀ d ∈ told.val.drop index.val, d ∈ list.val) := by
  rw [saturation.told_closed]
  by_cases more : index.val < told.val.length
  · have lookup : told.index_usize index = .ok told.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    rw [List.drop_eq_getElem_cons more]
    by_cases present : told.val[index.val] ∈ list.val
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b, run, spec⟩ := told_closed_spec told list next
      refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, has_spec, present, advance, run],
        fun yes => ?_⟩
      rw [List.forall_mem_cons]
      exact ⟨present, by rw [← nextIs]; exact spec yes⟩
    · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, has_spec, present], by simp⟩
  · refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more], fun _ => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by told.val.length - index.val
decreasing_by omega

theorem conjunctions_closed_spec (conjunctions : alloc.vec.Vec (Usize × Usize)) (list : alloc.vec.Vec Usize)
    (index : Usize) :
    ∃ b, saturation.conjunctions_closed conjunctions list index = .ok b ∧
      (b = true → ∀ p ∈ conjunctions.val.drop index.val, p.1 ∈ list.val → p.2 ∈ list.val) := by
  rw [saturation.conjunctions_closed]
  by_cases more : index.val < conjunctions.val.length
  · have lookup : conjunctions.index_usize index = .ok conjunctions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    rw [List.drop_eq_getElem_cons more]
    rcases pairIs : conjunctions.val[index.val] with ⟨other, both⟩
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨b, run, spec⟩ := conjunctions_closed_spec conjunctions list next
    by_cases hasOther : other ∈ list.val
    · by_cases hasBoth : both ∈ list.val
      · refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, pairIs, has_spec, hasOther,
          hasBoth, advance, run], fun yes => ?_⟩
        rw [List.forall_mem_cons]
        exact ⟨fun _ => hasBoth, by rw [← nextIs]; exact spec yes⟩
      · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, pairIs, has_spec, hasOther,
          hasBoth], by simp⟩
    · refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, pairIs, has_spec, hasOther, advance,
        run], fun yes => ?_⟩
      rw [List.forall_mem_cons]
      exact ⟨fun h => absurd h hasOther, by rw [← nextIs]; exact spec yes⟩
  · refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more], fun _ => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by conjunctions.val.length - index.val
decreasing_by all_goals omega

theorem parts_closed_spec (concepts : alloc.vec.Vec saturation.Concept) (c : Usize) (list : alloc.vec.Vec Usize)
    (links : alloc.vec.Vec (Usize × Usize)) :
    ∃ b, saturation.parts_closed concepts c list links = .ok b ∧ (b = true →
      c.val < concepts.val.length ∧
      (∀ a b, concepts.val[c.val]? = some (.And a b) → a ∈ list.val ∧ b ∈ list.val) ∧
      (∀ r y, concepts.val[c.val]? = some (.Exists r y) → (r, y) ∈ links.val)) := by
  rw [saturation.parts_closed]
  by_cases inside : c.val < concepts.val.length
  · have lookup : concepts.index_usize c = .ok concepts.val[c.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have at_c : concepts.val[c.val]? = some concepts.val[c.val] := List.getElem?_eq_getElem inside
    cases concept : concepts.val[c.val] with
    | Top =>
      refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, concept], fun _ => ?_⟩
      rw [concept] at at_c
      simp [inside, at_c, concept]
    | Bottom =>
      refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, concept], fun _ => ?_⟩
      rw [concept] at at_c
      simp [inside, at_c, concept]
    | Atom k =>
      refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, concept], fun _ => ?_⟩
      rw [concept] at at_c
      simp [inside, at_c, concept]
    | And a b =>
      rw [concept] at at_c
      by_cases hasA : a ∈ list.val
      · by_cases hasB : b ∈ list.val
        · refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, concept, has_spec, hasA,
            hasB], fun _ => ⟨inside, fun a' b' same => ?_, fun r y same => ?_⟩⟩
          · rw [at_c] at same
            simp only [Option.some.injEq, saturation.Concept.And.injEq] at same
            obtain ⟨rfl, rfl⟩ := same
            exact ⟨hasA, hasB⟩
          · rw [at_c] at same; cases same
        · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, concept, has_spec, hasA,
            hasB], by simp⟩
      · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, concept, has_spec, hasA],
          by simp⟩
    | Exists r y =>
      rw [concept] at at_c
      by_cases has : (r, y) ∈ links.val
      · refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, concept, has_pair_spec, has],
          fun _ => ⟨inside, fun a b same => ?_, fun r' y' same => ?_⟩⟩
        · rw [at_c] at same; cases same
        · rw [at_c] at same
          simp only [Option.some.injEq, saturation.Concept.Exists.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          exact has
      · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, concept, has_pair_spec, has],
          by simp⟩
  · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside], by simp⟩

theorem subsumers_closed_spec (rules : saturation.Rules) (concepts : alloc.vec.Vec saturation.Concept)
    (list : alloc.vec.Vec Usize) (links : alloc.vec.Vec (Usize × Usize)) (index : Usize) :
    ∃ b, saturation.subsumers_closed rules concepts list links index = .ok b ∧
      (b = true → ∀ c ∈ list.val.drop index.val, SubsumerClosed rules concepts.val list.val links.val c) := by
  rw [saturation.subsumers_closed]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    rw [List.drop_eq_getElem_cons more]
    by_cases h1 : list.val[index.val].val < rules.told.val.length
    · by_cases h2 : list.val[index.val].val < rules.conjunctions.val.length
      · obtain ⟨b1, run1, spec1⟩ := parts_closed_spec concepts list.val[index.val] list links
        cases b1 with
        | false => exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, h1, h2, run1],
            by simp⟩
        | true =>
          have l1 : rules.told.index_usize list.val[index.val] = .ok rules.told.val[list.val[index.val].val] := by
            simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h1]
          obtain ⟨b2, run2, spec2⟩ := told_closed_spec rules.told.val[list.val[index.val].val] list 0#usize
          cases b2 with
          | false => exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, h1, h2, run1, l1,
              run2], by simp⟩
          | true =>
            have l2 : rules.conjunctions.index_usize list.val[index.val] =
                .ok rules.conjunctions.val[list.val[index.val].val] := by
              simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h2]
            obtain ⟨b3, run3, spec3⟩ := conjunctions_closed_spec rules.conjunctions.val[list.val[index.val].val]
              list 0#usize
            cases b3 with
            | false => exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, h1, h2, run1,
                l1, run2, l2, run3], by simp⟩
            | true =>
              obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
                (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
              have nextIs : next.val = index.val + 1 := by simpa using nextValue
              obtain ⟨b, run, spec⟩ := subsumers_closed_spec rules concepts list links next
              refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, h1, h2, run1, l1, run2, l2,
                run3, advance, run], fun yes => ?_⟩
              rw [List.forall_mem_cons]
              refine ⟨?_, by rw [← nextIs]; exact spec yes⟩
              obtain ⟨inside, ands, somes⟩ := spec1 rfl
              refine ⟨inside, ands, somes, ?_, ?_⟩
              · rw [entries_lookup (List.getElem?_eq_getElem h1)]; simpa using spec2 rfl
              · rw [entries_lookup (List.getElem?_eq_getElem h2)]; simpa using spec3 rfl
      · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, h1, h2], by simp⟩
    · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, h1], by simp⟩
  · refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more], fun _ => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by list.val.length - index.val
decreasing_by omega

theorem existentials_closed_spec (existentials : alloc.vec.Vec (Usize × Usize)) (list : alloc.vec.Vec Usize)
    (r index : Usize) :
    ∃ b, saturation.existentials_closed existentials list r index = .ok b ∧
      (b = true → ∀ p ∈ existentials.val.drop index.val, p.1 = r → p.2 ∈ list.val) := by
  rw [saturation.existentials_closed]
  by_cases more : index.val < existentials.val.length
  · have lookup : existentials.index_usize index = .ok existentials.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    rw [List.drop_eq_getElem_cons more]
    rcases pairIs : existentials.val[index.val] with ⟨s, e⟩
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨b, run, spec⟩ := existentials_closed_spec existentials list r next
    by_cases same : s = r
    · by_cases has : e ∈ list.val
      · refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, pairIs, same, has_spec, has,
          advance, run], fun yes => ?_⟩
        rw [List.forall_mem_cons]
        exact ⟨fun _ => has, by rw [← nextIs]; exact spec yes⟩
      · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, pairIs, same, has_spec, has],
          by simp⟩
    · refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, pairIs, same, advance, run],
        fun yes => ?_⟩
      rw [List.forall_mem_cons]
      exact ⟨fun h => absurd h same, by rw [← nextIs]; exact spec yes⟩
  · refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more], fun _ => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by existentials.val.length - index.val
decreasing_by all_goals omega

theorem targets_closed_spec (rules : saturation.Rules) (list target : alloc.vec.Vec Usize) (r index : Usize) :
    ∃ b, saturation.targets_closed rules list target r index = .ok b ∧
      (b = true → ∀ c ∈ target.val.drop index.val, ∀ p ∈ entries rules.existentials.val c.val, p.1 = r →
        p.2 ∈ list.val) := by
  rw [saturation.targets_closed]
  by_cases more : index.val < target.val.length
  · have lookup : target.index_usize index = .ok target.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    rw [List.drop_eq_getElem_cons more]
    by_cases inside : target.val[index.val].val < rules.existentials.val.length
    · have l1 : rules.existentials.index_usize target.val[index.val] =
          .ok rules.existentials.val[target.val[index.val].val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      obtain ⟨b1, run1, spec1⟩ := existentials_closed_spec rules.existentials.val[target.val[index.val].val] list r
        0#usize
      cases b1 with
      | false => exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, inside, l1, run1],
          by simp⟩
      | true =>
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = index.val + 1 := by simpa using nextValue
        obtain ⟨b, run, spec⟩ := targets_closed_spec rules list target r next
        refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, inside, l1, run1, advance, run],
          fun yes => ?_⟩
        rw [List.forall_mem_cons]
        refine ⟨?_, by rw [← nextIs]; exact spec yes⟩
        rw [entries_lookup (List.getElem?_eq_getElem inside)]
        simpa using spec1 rfl
    · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, inside], by simp⟩
  · refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more], fun _ => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by target.val.length - index.val
decreasing_by omega

theorem supers_closed_spec (supers : alloc.vec.Vec Usize) (links : alloc.vec.Vec (Usize × Usize)) (y index : Usize) :
    ∃ b, saturation.supers_closed supers links y index = .ok b ∧
      (b = true → ∀ s ∈ supers.val.drop index.val, (s, y) ∈ links.val) := by
  rw [saturation.supers_closed]
  by_cases more : index.val < supers.val.length
  · have lookup : supers.index_usize index = .ok supers.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    rw [List.drop_eq_getElem_cons more]
    by_cases has : (supers.val[index.val], y) ∈ links.val
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b, run, spec⟩ := supers_closed_spec supers links y next
      refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, has_pair_spec, has, advance, run],
        fun yes => ?_⟩
      rw [List.forall_mem_cons]
      exact ⟨has, by rw [← nextIs]; exact spec yes⟩
    · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, has_pair_spec, has], by simp⟩
  · refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more], fun _ => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by supers.val.length - index.val
decreasing_by omega

theorem chain_closed_spec (links onward : alloc.vec.Vec (Usize × Usize)) (second result index : Usize) :
    ∃ b, saturation.chain_closed links onward second result index = .ok b ∧
      (b = true → ∀ q ∈ onward.val.drop index.val, q.1 = second → (result, q.2) ∈ links.val) := by
  rw [saturation.chain_closed]
  by_cases more : index.val < onward.val.length
  · have lookup : onward.index_usize index = .ok onward.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    rw [List.drop_eq_getElem_cons more]
    rcases pairIs : onward.val[index.val] with ⟨role, z⟩
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨b, run, spec⟩ := chain_closed_spec links onward second result next
    by_cases same : role = second
    · by_cases has : (result, z) ∈ links.val
      · refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, pairIs, same, has_pair_spec, has,
          advance, run], fun yes => ?_⟩
        rw [List.forall_mem_cons]
        exact ⟨fun _ => has, by rw [← nextIs]; exact spec yes⟩
      · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, pairIs, same, has_pair_spec,
          has], by simp⟩
    · refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, pairIs, same, advance, run],
        fun yes => ?_⟩
      rw [List.forall_mem_cons]
      exact ⟨fun h => absurd h same, by rw [← nextIs]; exact spec yes⟩
  · refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more], fun _ => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by onward.val.length - index.val
decreasing_by all_goals omega

theorem firsts_closed_spec (firsts links onward : alloc.vec.Vec (Usize × Usize)) (index : Usize) :
    ∃ b, saturation.firsts_closed firsts links onward index = .ok b ∧
      (b = true → ∀ p ∈ firsts.val.drop index.val, ∀ q ∈ onward.val, q.1 = p.1 → (p.2, q.2) ∈ links.val) := by
  rw [saturation.firsts_closed]
  by_cases more : index.val < firsts.val.length
  · have lookup : firsts.index_usize index = .ok firsts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    rw [List.drop_eq_getElem_cons more]
    rcases pairIs : firsts.val[index.val] with ⟨second, result⟩
    obtain ⟨b1, run1, spec1⟩ := chain_closed_spec links onward second result 0#usize
    cases b1 with
    | false => exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, pairIs, run1], by simp⟩
    | true =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b, run, spec⟩ := firsts_closed_spec firsts links onward next
      refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, pairIs, run1, advance, run],
        fun yes => ?_⟩
      rw [List.forall_mem_cons]
      exact ⟨by simpa using spec1 rfl, by rw [← nextIs]; exact spec yes⟩
  · refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more], fun _ => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by firsts.val.length - index.val
decreasing_by omega

theorem back_closed_spec (list target : alloc.vec.Vec Usize) (bottom : Usize) :
    ∃ b, saturation.back_closed list target bottom = .ok b ∧
      (b = true → bottom ∈ target.val → bottom ∈ list.val) := by
  rw [saturation.back_closed]
  by_cases inTarget : bottom ∈ target.val
  · by_cases inList : bottom ∈ list.val
    · exact ⟨true, by simp [has_spec, inTarget, inList], fun _ _ => inList⟩
    · exact ⟨false, by simp [has_spec, inTarget, inList], by simp⟩
  · exact ⟨true, by simp [has_spec, inTarget], fun _ h => absurd h inTarget⟩

theorem start_closed_spec (active : Bool) (list : alloc.vec.Vec Usize) (x top : Usize) :
    ∃ b, saturation.start_closed active list x top = .ok b ∧
      (b = true → active = true → x ∈ list.val ∧ top ∈ list.val) := by
  rw [saturation.start_closed]
  cases active with
  | true =>
    by_cases hx : x ∈ list.val
    · by_cases ht : top ∈ list.val
      · exact ⟨true, by simp [has_spec, hx, ht], fun _ _ => ⟨hx, ht⟩⟩
      · exact ⟨false, by simp [has_spec, hx, ht], by simp⟩
    · exact ⟨false, by simp [has_spec, hx], by simp⟩
  | false => exact ⟨_, rfl, fun _ h => by cases h⟩

theorem link_closed_spec (rules : saturation.Rules) (state : saturation.State) (x r y : Usize) :
    ∃ b, saturation.link_closed rules state x r y = .ok b ∧ (b = true → LinkClosed rules state x r y) := by
  rw [saturation.link_closed]
  by_cases h1 : x.val < state.subsumers.val.length
  · by_cases h2 : x.val < state.out.val.length
    · by_cases h3 : y.val < state.subsumers.val.length
      · by_cases h4 : y.val < state.active.val.length
        · by_cases h5 : y.val < state.out.val.length
          · by_cases h6 : r.val < rules.supers.val.length
            · by_cases h7 : r.val < rules.firsts.val.length
              · have l1 : state.active.index_usize y = .ok state.active.val[y.val] := by
                  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h4]
                have l2 : state.subsumers.index_usize x = .ok state.subsumers.val[x.val] := by
                  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h1]
                have l3 : state.subsumers.index_usize y = .ok state.subsumers.val[y.val] := by
                  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h3]
                have l4 : rules.supers.index_usize r = .ok rules.supers.val[r.val] := by
                  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h6]
                have l5 : state.out.index_usize x = .ok state.out.val[x.val] := by
                  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h2]
                have l6 : rules.firsts.index_usize r = .ok rules.firsts.val[r.val] := by
                  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h7]
                have l7 : state.out.index_usize y = .ok state.out.val[y.val] := by
                  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h5]
                have e1 := entries_lookup (List.getElem?_eq_getElem h1)
                have e2 := entries_lookup (List.getElem?_eq_getElem h3)
                have e3 := entries_lookup (List.getElem?_eq_getElem h6)
                have e4 := entries_lookup (List.getElem?_eq_getElem h2)
                have e5 := entries_lookup (List.getElem?_eq_getElem h7)
                have e6 := entries_lookup (List.getElem?_eq_getElem h5)
                by_cases active : state.active.val[y.val] = true
                · obtain ⟨b1, run1, spec1⟩ := back_closed_spec state.subsumers.val[x.val] state.subsumers.val[y.val]
                    rules.bottom
                  cases b1 with
                  | false => exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3, h4, h5, h6,
                      h7, l1, active, l2, l3, run1], by simp⟩
                  | true =>
                    obtain ⟨b2, run2, spec2⟩ := targets_closed_spec rules state.subsumers.val[x.val]
                      state.subsumers.val[y.val] r 0#usize
                    cases b2 with
                    | false => exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3, h4, h5, h6,
                        h7, l1, active, l2, l3, run1, run2], by simp⟩
                    | true =>
                      obtain ⟨b3, run3, spec3⟩ := supers_closed_spec rules.supers.val[r.val] state.out.val[x.val] y
                        0#usize
                      cases b3 with
                      | false => exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3, h4, h5,
                          h6, h7, l1, active, l2, l3, run1, run2, l4, l5, run3], by simp⟩
                      | true =>
                        obtain ⟨b4, run4, spec4⟩ := firsts_closed_spec rules.firsts.val[r.val] state.out.val[x.val]
                          state.out.val[y.val] 0#usize
                        refine ⟨b4, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3, h4, h5, h6, h7, l1,
                          active, l2, l3, run1, run2, l4, l5, run3, l6, l7, run4], fun yes => ?_⟩
                        refine ⟨h3, by rw [List.getElem?_eq_getElem h4, active], ?_, ?_, ?_, ?_⟩
                        · rw [e1, e2]; exact spec1 rfl
                        · rw [e1, e2]; simpa using spec2 rfl
                        · rw [e3, e4]; simpa using spec3 rfl
                        · rw [e5, e6, e4]; simpa using spec4 yes
                · have notActive : state.active.val[y.val] = false := by simpa using active
                  exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3, h4, h5, h6, h7, l1,
                    notActive], by simp⟩
              · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3, h4, h5, h6, h7], by simp⟩
            · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3, h4, h5, h6], by simp⟩
          · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3, h4, h5], by simp⟩
        · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3, h4], by simp⟩
      · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3], by simp⟩
    · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2], by simp⟩
  · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1], by simp⟩

theorem links_closed_spec (rules : saturation.Rules) (state : saturation.State) (x index : Usize) :
    ∃ b, saturation.links_closed rules state x index = .ok b ∧
      (b = true → ∀ p ∈ (entries state.out.val x.val).drop index.val, LinkClosed rules state x p.1 p.2) := by
  rw [saturation.links_closed]
  by_cases h1 : x.val < state.out.val.length
  · have l1 : state.out.index_usize x = .ok state.out.val[x.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h1]
    have e1 := entries_lookup (List.getElem?_eq_getElem h1)
    have measure : (entries state.out.val x.val).length = state.out.val[x.val].val.length := by rw [e1]
    by_cases more : index.val < state.out.val[x.val].val.length
    · have l2 : state.out.val[x.val].index_usize index = .ok state.out.val[x.val].val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
      rcases pairIs : state.out.val[x.val].val[index.val] with ⟨r, y⟩
      obtain ⟨b1, run1, spec1⟩ := link_closed_spec rules state x r y
      cases b1 with
      | false => exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, l1, more, l2, pairIs, run1],
          by simp⟩
      | true =>
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = index.val + 1 := by simpa using nextValue
        obtain ⟨b, run, spec⟩ := links_closed_spec rules state x next
        refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, l1, more, l2, pairIs, run1, advance, run],
          fun yes => ?_⟩
        rw [e1, List.drop_eq_getElem_cons more, pairIs, List.forall_mem_cons]
        refine ⟨spec1 rfl, ?_⟩
        have rest := spec yes
        rw [e1, nextIs] at rest
        exact rest
    · refine ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, l1, more], fun _ => ?_⟩
      rw [e1, List.drop_eq_nil_of_le (by omega)]
      simp
  · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1], by simp⟩
termination_by (entries state.out.val x.val).length - index.val
decreasing_by omega

theorem contexts_closed_spec (rules : saturation.Rules) (concepts : alloc.vec.Vec saturation.Concept)
    (state : saturation.State) (x : Usize) :
    ∃ b, saturation.contexts_closed rules concepts state x = .ok b ∧ (b = true →
      ∀ x' : Usize, x.val ≤ x'.val → x'.val < state.subsumers.val.length →
        ContextClosed rules concepts.val state x') := by
  rw [saturation.contexts_closed]
  by_cases h1 : x.val < state.subsumers.val.length
  · by_cases h2 : x.val < state.active.val.length
    · by_cases h3 : x.val < state.out.val.length
      · have l1 : state.active.index_usize x = .ok state.active.val[x.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h2]
        have l2 : state.subsumers.index_usize x = .ok state.subsumers.val[x.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h1]
        have l3 : state.out.index_usize x = .ok state.out.val[x.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h3]
        have e1 := entries_lookup (List.getElem?_eq_getElem h1)
        have e2 := entries_lookup (List.getElem?_eq_getElem h3)
        obtain ⟨b1, run1, spec1⟩ := start_closed_spec state.active.val[x.val] state.subsumers.val[x.val] x rules.top
        cases b1 with
        | false => exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3, l1, l2, run1],
            by simp⟩
        | true =>
          obtain ⟨b2, run2, spec2⟩ := subsumers_closed_spec rules concepts state.subsumers.val[x.val]
            state.out.val[x.val] 0#usize
          cases b2 with
          | false => exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3, l1, l2, run1, l3,
              run2], by simp⟩
          | true =>
            obtain ⟨b3, run3, spec3⟩ := links_closed_spec rules state x 0#usize
            cases b3 with
            | false => exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3, l1, l2, run1, l3,
                run2, run3], by simp⟩
            | true =>
              obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
                (Usize.add_spec (x := x) (y := 1#usize) (by scalar_tac))
              have nextIs : next.val = x.val + 1 := by simpa using nextValue
              obtain ⟨b, run, spec⟩ := contexts_closed_spec rules concepts state next
              refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3, l1, l2, run1, l3, run2, run3,
                advance, run], fun yes x' low inside => ?_⟩
              by_cases here : x'.val = x.val
              · obtain rfl : x' = x := UScalar.eq_of_val_eq here
                refine ⟨fun act => ?_, ?_, ?_⟩
                · rw [e1]
                  rw [List.getElem?_eq_getElem h2] at act
                  exact spec1 rfl (by simpa using act)
                · rw [e1, e2]; simpa using spec2 rfl
                · simpa using spec3 rfl
              · exact spec yes x' (by omega) inside
      · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2, h3], by simp⟩
    · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1, h2], by simp⟩
  · exact ⟨true, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, h1], fun _ x' low inside => by omega⟩
termination_by state.subsumers.val.length - x.val
decreasing_by omega

theorem closed_spec (rules : saturation.Rules) (concepts : alloc.vec.Vec saturation.Concept)
    (state : saturation.State) :
    ∃ b, saturation.closed rules concepts state = .ok b ∧ (b = true → Closure rules concepts.val state) := by
  rw [saturation.closed]
  by_cases h1 : state.subsumers.val.length = concepts.val.length
  · have s1 : alloc.vec.Vec.len state.subsumers = alloc.vec.Vec.len concepts := UScalar.eq_of_val_eq (by simp [h1])
    by_cases h2 : state.active.val.length = concepts.val.length
    · have s2 : alloc.vec.Vec.len state.active = alloc.vec.Vec.len concepts := UScalar.eq_of_val_eq (by simp [h2])
      by_cases h3 : state.out.val.length = concepts.val.length
      · have s3 : alloc.vec.Vec.len state.out = alloc.vec.Vec.len concepts := UScalar.eq_of_val_eq (by simp [h3])
        by_cases h4 : rules.top.val < concepts.val.length
        · by_cases h5 : rules.bottom.val < concepts.val.length
          · obtain ⟨b, run, spec⟩ := contexts_closed_spec rules concepts state 0#usize
            refine ⟨b, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, s1, s2, s3, h4, h5, run], fun yes =>
              ⟨h1, h2, h3, h4, h5, fun x inside => spec yes x (by simp) (by omega)⟩⟩
          · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, s1, s2, s3, h4, h5], by simp⟩
        · exact ⟨false, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, s1, s2, s3, h4], by simp⟩
      · have s3 : ¬ alloc.vec.Vec.len state.out = alloc.vec.Vec.len concepts := fun same =>
          h3 (by simpa using congrArg UScalar.val same)
        exact ⟨false, by simp [s1, s2, s3], by simp⟩
    · have s2 : ¬ alloc.vec.Vec.len state.active = alloc.vec.Vec.len concepts := fun same =>
        h2 (by simpa using congrArg UScalar.val same)
      exact ⟨false, by simp [s1, s2], by simp⟩
  · have s1 : ¬ alloc.vec.Vec.len state.subsumers = alloc.vec.Vec.len concepts := fun same =>
      h1 (by simpa using congrArg UScalar.val same)
    exact ⟨false, by simp [s1], by simp⟩

/-! ### The canonical model -/

section Canonical
variable (t : saturation.Table) (rules : saturation.Rules) (state : saturation.State)

/-- The contexts that make up the canonical model: active and not unsatisfiable. -/
def InDomain (x : Usize) : Prop :=
  state.active.val[x.val]? = some true ∧ rules.bottom ∉ entries state.subsumers.val x.val

abbrev Domain := {x : Usize // InDomain rules state x}

/-- The canonical interpretation: a context is in the atoms among its subsumers
    and linked along the roles of its links. -/
def canonical (root : Domain rules state) : Interpretation (Domain rules state) Unit where
  objectsNonempty := ⟨root⟩
  dataNonempty := ⟨()⟩
  classes k x := ∃ c ∈ entries state.subsumers.val x.val.val, t.concepts.val[c.val]? = some (.Atom k)
  objectProperties p x y := ∃ r : Usize, t.roles.val[r.val]? = some p ∧ (r, y.val) ∈ entries state.out.val x.val.val
  dataProperties _ _ _ := False
  namedIndividuals _ := root
  anonymousIndividuals _ := root
  datatypes _ _ := False
  literals _ := ()
  facets _ _ := False
  named _ := True

/-- The canonical interpretation with the built-in names given their meaning. -/
abbrev lifted (root : Domain rules state) {Native : Type w} (D : DatatypeMap Native) :=
  Rowl.AlcOntology.owlModel.{u,v,w} (canonical t rules state root) root (fun _ => root) D

end Canonical

section Lifted
variable {t : saturation.Table} {rules : saturation.Rules} {state : saturation.State}

/-- A concept with no parts. -/
def Simple (concepts : List saturation.Concept) (c : Usize) : Prop :=
  (∀ a b, concepts[c.val]? ≠ some (.And a b)) ∧ ∀ r f, concepts[c.val]? ≠ some (.Exists r f)

theorem class_simple {concepts : List saturation.Concept} {c : Usize} {k : Class}
    (at_c : concepts[c.val]? = some (classConcept k)) : Simple concepts c := by
  refine ⟨fun a b same => ?_, fun r f same => ?_⟩ <;> rw [at_c] at same <;>
    by_cases top : k = thing <;> by_cases bottom : k = nothing <;>
    simp [classConcept, top, bottom, nothing_ne_thing] at same

theorem lifted_fixed (root : Domain rules state) {Native : Type w} (D : DatatypeMap Native) :
    Fixed (lifted.{u,v,w} t rules state root D) :=
  ⟨fun x => by simp [Rowl.AlcOntology.owlModel], fun x => by
    have differ : nothing ≠ thing := nothing_ne_thing
    simp [Rowl.AlcOntology.owlModel, differ]⟩

theorem lifted_rel (root : Domain rules state) {Native : Type w} (D : DatatypeMap Native) (ok : TableOk t)
    {r : Usize} {p : ObjectProperty} (at_r : t.roles.val[r.val]? = some p) (x y : Domain rules state) :
    rel (lifted.{u,v,w} t rules state root D) t.roles.val r.val (ULift.up x) (ULift.up y) ↔
      (r, y.val) ∈ entries state.out.val x.val.val := by
  rw [rel_at _ at_r]
  have proper := ok.rolesProper r.val p at_r
  simp only [Rowl.AlcOntology.owlModel, proper.1, proper.2, if_false, canonical]
  constructor
  · rintro ⟨r', at_r', edge⟩
    have same : r'.val = r.val := ok.rolesDistinct r'.val r.val p at_r' at_r
    rw [UScalar.eq_of_val_eq same] at edge
    exact edge
  · intro edge; exact ⟨r, at_r, edge⟩

theorem lifted_atom (root : Domain rules state) {Native : Type w} (D : DatatypeMap Native) {k : Class}
    (proper : k ≠ thing ∧ k ≠ nothing) (x : Domain rules state) :
    (lifted.{u,v,w} t rules state root D).classes k (ULift.up x) ↔
      ∃ c ∈ entries state.subsumers.val x.val.val, t.concepts.val[c.val]? = some (.Atom k) := by
  simp only [Rowl.AlcOntology.owlModel, proper.1, proper.2, if_false, canonical]

theorem domain_inside (closure : Closure rules t.concepts.val state) (x : Domain rules state) :
    x.val.val < t.concepts.val.length := by
  have := (List.getElem?_eq_some_iff.mp x.property.1).1
  rw [closure.activeLength] at this
  exact this

/-- Every subsumer of a context holds at its element. -/
theorem positive (root : Domain rules state) {Native : Type w} (D : DatatypeMap Native) (ok : TableOk t)
    (closure : Closure rules t.concepts.val state) (bottomAt : t.concepts.val[rules.bottom.val]? = some .Bottom) :
    ∀ (n : Nat) (c : Usize), c.val = n → ∀ x : Domain rules state, c ∈ entries state.subsumers.val x.val.val →
      meaning (lifted.{u,v,w} t rules state root D) t.concepts.val t.roles.val c.val (ULift.up x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c cn x member
    subst cn
    have context := closure.contexts x.val (domain_inside closure x)
    obtain ⟨inside, ands, somes, _, _⟩ := context.2.1 c member
    have at_c : t.concepts.val[c.val]? = some t.concepts.val[c.val] := List.getElem?_eq_getElem inside
    have partsOk := ok.parts c.val _ at_c
    cases concept : t.concepts.val[c.val] with
    | Top => rw [concept] at at_c; exact meaning_top _ at_c _
    | Bottom =>
      rw [concept] at at_c
      have same : c.val = rules.bottom.val := ok.distinct c.val rules.bottom.val _ at_c bottomAt
      rw [UScalar.eq_of_val_eq same] at member
      exact absurd member x.property.2
    | Atom k =>
      rw [concept] at at_c partsOk
      rw [meaning_atom _ at_c, lifted_atom root D partsOk x]
      exact ⟨c, member, at_c⟩
    | And a b =>
      rw [concept] at at_c partsOk
      have aLt : a.val < c.val := partsOk.1
      have bLt : b.val < c.val := partsOk.2
      obtain ⟨hasA, hasB⟩ := ands a b at_c
      rw [meaning_and _ at_c aLt bLt]
      exact ⟨ih a.val aLt a rfl x hasA, ih b.val bLt b rfl x hasB⟩
    | Exists r y =>
      rw [concept] at at_c partsOk
      have yLt : y.val < c.val := partsOk.1
      have rInside : r.val < t.roles.val.length := partsOk.2
      have edge := somes r y at_c
      obtain ⟨_, active, back, _, _, _⟩ := context.2.2 (r, y) edge
      have inDomain : InDomain rules state y := ⟨active, fun bottom => x.property.2 (back bottom)⟩
      have yContext := closure.contexts y (by
        have := (List.getElem?_eq_some_iff.mp active).1
        rw [closure.activeLength] at this
        exact this)
      have self := (yContext.1 active).1
      rw [meaning_exists _ at_c yLt]
      refine ⟨ULift.up ⟨y, inDomain⟩, ?_, ih y.val yLt y rfl ⟨y, inDomain⟩ self⟩
      rw [lifted_rel root D ok (List.getElem?_eq_getElem rInside)]
      exact edge

/-- A registered or simple concept that holds at the element of a context is one of its subsumers. -/
theorem negative (root : Domain rules state) {Native : Type w} (D : DatatypeMap Native) (ok : TableOk t)
    (closure : Closure rules t.concepts.val state) (topAt : t.concepts.val[rules.top.val]? = some .Top)
    {list : List saturation.Rule} {seen : List Bool} (complete : IndexComplete t.concepts.val list rules seen) :
    ∀ (n : Nat) (c : Usize), c.val = n → (seen[c.val]? = some true ∨ Simple t.concepts.val c) →
      ∀ x : Domain rules state,
        meaning (lifted.{u,v,w} t rules state root D) t.concepts.val t.roles.val c.val (ULift.up x) →
        c ∈ entries state.subsumers.val x.val.val := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c cn which x holds
    subst cn
    have context := closure.contexts x.val (domain_inside closure x)
    cases at_c : t.concepts.val[c.val]? with
    | none => rw [meaning, at_c] at holds; exact holds.elim
    | some concept =>
      have partsOk := ok.parts c.val _ at_c
      cases concept with
      | Top =>
        have same : c.val = rules.top.val := ok.distinct c.val rules.top.val _ at_c topAt
        rw [UScalar.eq_of_val_eq same]
        exact (context.1 x.property.1).2
      | Bottom => exact absurd holds (meaning_bottom _ at_c _)
      | Atom k =>
        rw [meaning_atom _ at_c, lifted_atom root D partsOk x] at holds
        obtain ⟨c', member, at_c'⟩ := holds
        have same : c'.val = c.val := ok.distinct c'.val c.val _ at_c' at_c
        rw [← UScalar.eq_of_val_eq same]
        exact member
      | And a b =>
        have aLt : a.val < c.val := partsOk.1
        have bLt : b.val < c.val := partsOk.2
        have isSeen : seen[c.val]? = some true := by
          rcases which with h | simple
          · exact h
          · exact absurd at_c (simple.1 a b)
        have registered := complete.registered c isSeen
        unfold Registered at registered
        rw [at_c] at registered
        obtain ⟨inA, _, seenA, seenB⟩ := registered
        rw [meaning_and _ at_c aLt bLt] at holds
        have hasA := ih a.val aLt a rfl (Or.inl seenA) x holds.1
        have hasB := ih b.val bLt b rfl (Or.inl seenB) x holds.2
        exact (context.2.1 a hasA).2.2.2.2 (b, c) inA hasB
      | Exists r f =>
        have fLt : f.val < c.val := partsOk.1
        have rInside : r.val < t.roles.val.length := partsOk.2
        have isSeen : seen[c.val]? = some true := by
          rcases which with h | simple
          · exact h
          · exact absurd at_c (simple.2 r f)
        have registered := complete.registered c isSeen
        unfold Registered at registered
        rw [at_c] at registered
        obtain ⟨inF, seenF⟩ := registered
        rw [meaning_exists _ at_c fLt] at holds
        obtain ⟨⟨y⟩, edge, there⟩ := holds
        rw [lifted_rel root D ok (List.getElem?_eq_getElem rInside)] at edge
        have hasF := ih f.val fLt f rfl (Or.inl seenF) y there
        obtain ⟨_, _, _, backExists, _, _⟩ := context.2.2 (r, y.val) edge
        exact backExists f hasF (r, c) inF rfl

/-- The canonical model satisfies every rule. -/
theorem canonical_models (root : Domain rules state) {Native : Type w} (D : DatatypeMap Native) (ok : TableOk t)
    (closure : Closure rules t.concepts.val state) (topAt : t.concepts.val[rules.top.val]? = some .Top)
    (bottomAt : t.concepts.val[rules.bottom.val]? = some .Bottom)
    {list : List saturation.Rule} {seen : List Bool} (complete : IndexComplete t.concepts.val list rules seen)
    (inside : ∀ rule ∈ list, RuleInside t rule) :
    Models.{u, max w v} t list (lifted.{u,v,w} t rules state root D) := by
  intro rule member
  have ruleInside := inside rule member
  cases rule with
  | Sub a b =>
    obtain ⟨told, seenA⟩ := complete.told a b member
    intro z holds
    obtain ⟨x⟩ := z
    have hasA := negative root D ok closure topAt complete a.val a rfl (Or.inl seenA) x holds
    have context := closure.contexts x.val (domain_inside closure x)
    exact positive root D ok closure bottomAt b.val b rfl x ((context.2.1 a hasA).2.2.2.1 b told)
  | Role r s =>
    have super := complete.supers r s member
    intro z z' edge
    obtain ⟨x⟩ := z
    obtain ⟨y⟩ := z'
    rw [lifted_rel root D ok (List.getElem?_eq_getElem ruleInside.1)] at edge
    rw [lifted_rel root D ok (List.getElem?_eq_getElem ruleInside.2)]
    have context := closure.contexts x.val (domain_inside closure x)
    exact (context.2.2 (r, y.val) edge).2.2.2.2.1 s super
  | Chain r1 r2 s =>
    have first := complete.firsts r1 r2 s member
    intro z z' z'' edge edge'
    obtain ⟨x⟩ := z
    obtain ⟨y⟩ := z'
    obtain ⟨w⟩ := z''
    rw [lifted_rel root D ok (List.getElem?_eq_getElem ruleInside.1)] at edge
    rw [lifted_rel root D ok (List.getElem?_eq_getElem ruleInside.2.1)] at edge'
    rw [lifted_rel root D ok (List.getElem?_eq_getElem ruleInside.2.2)]
    have context := closure.contexts x.val (domain_inside closure x)
    exact (context.2.2 (r1, y.val) edge).2.2.2.2.2 (r2, s) first (r2, w.val) edge' rfl

end Lifted

/-! ### Reading the answers -/

theorem row_from_spec (list : alloc.vec.Vec Usize) (empty : Bool) (ids : alloc.vec.Vec Usize) (index : Usize)
    (out : alloc.vec.Vec Bool) :
    ∃ r, saturation.row_from list empty ids index out = .ok r ∧ ∀ row, r = some row →
      row.val = out.val ++ (ids.val.drop index.val).map (fun id => empty || decide (id ∈ list.val)) := by
  rw [saturation.row_from]
  by_cases more : index.val < ids.val.length
  · by_cases room : out.val.length < Usize.max
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      cases empty with
      | true =>
        obtain ⟨out1, push, outIs⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out true room)
        obtain ⟨r, run, spec⟩ := row_from_spec list true ids next out1
        refine ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val, more, room, push, advance, run],
          fun row same => ?_⟩
        rw [spec row same, outIs, nextIs]
        conv_rhs => rw [List.drop_eq_getElem_cons more]
        simp only [List.map_cons, List.append_assoc, List.singleton_append, Bool.true_or]
      | false =>
        have lookup : ids.index_usize index = .ok ids.val[index.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
        obtain ⟨out1, push, outIs⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec out (decide (ids.val[index.val] ∈ list.val)) room)
        obtain ⟨r, run, spec⟩ := row_from_spec list false ids next out1
        refine ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val, more, room, lookup, has_spec,
          push, advance, run], fun row same => ?_⟩
        rw [spec row same, outIs, nextIs]
        conv_rhs => rw [List.drop_eq_getElem_cons more]
        simp only [List.map_cons, List.append_assoc, List.singleton_append, Bool.false_or]
    · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val, more, room], by simp⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more], fun row same => ?_⟩
    cases same
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by ids.val.length - index.val
decreasing_by all_goals omega

/-- Whether the class with concept `id` comes out unsatisfiable. -/
def EmptyAt (state : saturation.State) (bottom : Usize) (inconsistent : Bool) (id : Usize) : Bool :=
  inconsistent || decide (bottom ∈ entries state.subsumers.val id.val)

/-- The answers for the first `n` classes. -/
def AnswersOk (state : saturation.State) (bottom : Usize) (inconsistent : Bool) (ids : List Usize) (n : Nat)
    (sats : List Bool) (rows : List (alloc.vec.Vec Bool)) : Prop :=
  sats.length = n ∧ rows.length = n ∧ ∀ (i : Nat) (id : Usize), i < n → ids[i]? = some id →
    sats[i]? = some (!EmptyAt state bottom inconsistent id) ∧
    ∃ row, rows[i]? = some row ∧
      row.val = ids.map (fun id' => EmptyAt state bottom inconsistent id || decide (id' ∈ entries state.subsumers.val id.val))

theorem answers_from_spec (state : saturation.State) (bottom : Usize) (inconsistent : Bool) (ids : alloc.vec.Vec Usize)
    (index : Usize) (satisfiable : alloc.vec.Vec Bool) (subsumed : alloc.vec.Vec (alloc.vec.Vec Bool))
    (low : index.val ≤ ids.val.length)
    (before : AnswersOk state bottom inconsistent ids.val index.val satisfiable.val subsumed.val) :
    ∃ r, saturation.answers_from state bottom inconsistent ids index satisfiable subsumed = .ok r ∧
      ∀ result, r = some result →
        AnswersOk state bottom inconsistent ids.val ids.val.length result.satisfiable.val result.subsumed.val := by
  rw [saturation.answers_from]
  by_cases more : index.val < ids.val.length
  · have lookup : ids.index_usize index = .ok ids.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    by_cases inside : ids.val[index.val].val < state.subsumers.val.length
    · have lookup2 : state.subsumers.index_usize ids.val[index.val] =
          .ok state.subsumers.val[ids.val[index.val].val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      have e1 := entries_lookup (List.getElem?_eq_getElem inside)
      have emptyIs : (if inconsistent = true then (Result.ok true : Result Bool) else
          saturation.has state.subsumers.val[ids.val[index.val].val] bottom) =
          .ok (EmptyAt state bottom inconsistent ids.val[index.val]) := by
        cases inconsistent <;> simp [EmptyAt, has_spec, e1]
      obtain ⟨r1, run1, spec1⟩ := row_from_spec state.subsumers.val[ids.val[index.val].val]
        (EmptyAt state bottom inconsistent ids.val[index.val]) ids 0#usize (alloc.vec.Vec.new Bool)
      cases r1 with
      | none =>
        exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, inside, lookup2, emptyIs, run1],
          by simp⟩
      | some row =>
        have rowIs := spec1 row rfl
        by_cases room1 : satisfiable.val.length < Usize.max
        · by_cases room2 : subsumed.val.length < Usize.max
          · obtain ⟨sat1, push1, sat1Is⟩ := WP.spec_imp_exists
              (alloc.vec.Vec.push_spec satisfiable (!EmptyAt state bottom inconsistent ids.val[index.val]) room1)
            obtain ⟨sub1, push2, sub1Is⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec subsumed row room2)
            obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
              (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
            have nextIs : next.val = index.val + 1 := by simpa using nextValue
            obtain ⟨satLen, subLen, old⟩ := before
            have now : AnswersOk state bottom inconsistent ids.val next.val sat1.val sub1.val := by
              refine ⟨by rw [sat1Is, nextIs]; simp [satLen], by rw [sub1Is, nextIs]; simp [subLen],
                fun i id lt at_i => ?_⟩
              rw [nextIs] at lt
              by_cases here : i = index.val
              · subst here
                rw [List.getElem?_eq_getElem more] at at_i
                cases at_i
                refine ⟨by rw [sat1Is]; simp [satLen], row, by rw [sub1Is]; simp [subLen], ?_⟩
                rw [rowIs, ← e1]
                simp
              · obtain ⟨satAt, row', rowAt, rowVal⟩ := old i id (by omega) at_i
                refine ⟨by rw [sat1Is, List.getElem?_append_left (by omega)]; exact satAt, row',
                  by rw [sub1Is, List.getElem?_append_left (by omega)]; exact rowAt, rowVal⟩
            obtain ⟨r, run, spec⟩ := answers_from_spec state bottom inconsistent ids next sat1 sub1 (by omega) now
            exact ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val, more, lookup, inside, lookup2,
              emptyIs, run1, room1, room2, push1, push2, advance, run], spec⟩
          · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val, more, lookup, inside, lookup2,
              emptyIs, run1, room1, room2], by simp⟩
        · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val, more, lookup, inside, lookup2,
            emptyIs, run1, room1], by simp⟩
    · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, lookup, inside], by simp⟩
  · refine ⟨some { satisfiable, subsumed }, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more],
      fun result same => ?_⟩
    cases same
    have equal : index.val = ids.val.length := by omega
    rw [← equal]
    exact before
termination_by ids.val.length - index.val
decreasing_by omega

/-! ### Saturation as a whole -/

theorem saturated_spec (items : alloc.vec.Vec AnnotatedAxiom) (classes : alloc.vec.Vec Class) :
    ∃ r, saturation.saturated items classes = .ok r ∧ ∀ T rules state ids, r = some (T, rules, state, ids) →
      ∃ (t3 : saturation.Table) (list : List saturation.Rule) (seen : List Bool),
        TableOk t3 ∧ TableOk T ∧ Extends t3 T ∧ (∀ rule ∈ list, RuleInside t3 rule) ∧
        (∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Fixed I →
          ((∀ a ∈ items.val, satisfies I a.axiom) ↔ ∀ rule ∈ list, RuleHolds I t3.concepts.val t3.roles.val rule)) ∧
        ClassIds T ids.val classes.val ∧
        T.concepts.val[rules.top.val]? = some .Top ∧ T.concepts.val[rules.bottom.val]? = some .Bottom ∧
        IndexComplete T.concepts.val list rules seen ∧
        StateOk.{u,v} T list (fun _ => False) state ∧
        (∀ id ∈ ids.val, state.active.val[id.val]? = some true) ∧
        Closure rules T.concepts.val state := by
  rw [saturation.saturated]
  obtain ⟨t0, run0, ok0, _, _⟩ := empty_table_spec
  obtain ⟨r1, run1, spec1⟩ := intern_spec t0 ok0 .Top trivial
  cases r1 with
  | none => exact ⟨none, by simp [run0, run1], by simp⟩
  | some p1 =>
    obtain ⟨t1, top⟩ := p1
    obtain ⟨ok1, _, topAt1⟩ := spec1 t1 top rfl
    obtain ⟨r2, run2, spec2⟩ := intern_spec t1 ok1 .Bottom trivial
    cases r2 with
    | none => exact ⟨none, by simp [run0, run1, run2], by simp⟩
    | some p2 =>
      obtain ⟨t2, bottom⟩ := p2
      obtain ⟨ok2, grown2, bottomAt2⟩ := spec2 t2 bottom rfl
      have topAt2 := prefix_lookup grown2.1 topAt1
      obtain ⟨r3, run3, spec3⟩ := translate_spec.{u,v} items top bottom 0#usize t2 ok2
        (alloc.vec.Vec.new saturation.Rule) topAt2 bottomAt2
      cases r3 with
      | none => exact ⟨none, by simp [run0, run1, run2, run3], by simp⟩
      | some p3 =>
        obtain ⟨t3, list⟩ := p3
        obtain ⟨ok3, grown3, added, addedIs, inside3, meaning3⟩ := spec3 t3 list rfl
        have listIs : list.val = added := by simpa using addedIs
        obtain ⟨r4, run4, spec4⟩ := class_concepts_spec classes 0#usize t3 ok3 (alloc.vec.Vec.new Usize) []
          (by simp [ClassIds])
        cases r4 with
        | none => exact ⟨none, by simp [run0, run1, run2, run3, run4], by simp⟩
        | some p4 =>
          obtain ⟨T, ids⟩ := p4
          obtain ⟨okT, grownT, classIds⟩ := spec4 T ids rfl
          have topAtT := prefix_lookup (extends_trans grown3 grownT).1 topAt2
          have bottomAtT := prefix_lookup (extends_trans grown3 grownT).1 bottomAt2
          obtain ⟨v, runV, _, allV⟩ := empty_lists_spec (alloc.vec.Vec.len T.concepts)
            (alloc.vec.Vec.new (alloc.vec.Vec Usize)) (by simp) (by simp)
          obtain ⟨v1, runV1, _, allV1⟩ := empty_pairs_spec (alloc.vec.Vec.len T.concepts)
            (alloc.vec.Vec.new (alloc.vec.Vec (Usize × Usize))) (by simp) (by simp)
          obtain ⟨v2, runV2, _, allV2⟩ := empty_lists_spec (alloc.vec.Vec.len T.roles)
            (alloc.vec.Vec.new (alloc.vec.Vec Usize)) (by simp) (by simp)
          obtain ⟨v3, runV3, _, allV3⟩ := empty_pairs_spec (alloc.vec.Vec.len T.roles)
            (alloc.vec.Vec.new (alloc.vec.Vec (Usize × Usize))) (by simp) (by simp)
          obtain ⟨v4, runV4, _, allV4⟩ := falses_spec (alloc.vec.Vec.len T.concepts) (alloc.vec.Vec.new Bool)
            (by simp) (by simp)
          let empty : saturation.Rules :=
            { top := top, bottom := bottom, told := v, conjunctions := v1, existentials := v1,
              supers := v2, firsts := v3, seconds := v3 }
          have emptySound : IndexSound T.concepts.val list.val empty := {
            told := fun c d h => by simp [empty, entries_empty allV] at h
            parts := ⟨fun a b c h => by simp [empty, entries_empty allV1] at h,
              fun f r c h => by simp [empty, entries_empty allV1] at h⟩
            supers := fun r s h => by simp [empty, entries_empty allV2] at h
            firsts := fun r s q h => by simp [empty, entries_empty allV3] at h
            seconds := fun s r q h => by simp [empty, entries_empty allV3] at h }
          have emptyComplete : IndexComplete T.concepts.val (list.val.take (0#usize).val) empty v4.val := {
            told := fun a b h => by simp at h
            supers := fun r s h => by simp at h
            firsts := fun r s q h => by simp at h
            registered := fun c h => by
              have := allV4 _ (List.mem_of_getElem? h)
              simp at this }
          obtain ⟨r5, run5, spec5⟩ := index_from_spec T okT list 0#usize empty v4 emptySound emptyComplete
          cases r5 with
          | none => exact ⟨none, by simp [run0, run1, run2, run3, run4, runV, runV1, runV2, runV3, runV4, run5, empty],
              by simp⟩
          | some rules =>
            obtain ⟨rulesTop, rulesBottom, sound, seen, complete⟩ := spec5 rules rfl
            have rulesTopAt : T.concepts.val[rules.top.val]? = some .Top := by rw [rulesTop]; exact topAtT
            have rulesBottomAt : T.concepts.val[rules.bottom.val]? = some .Bottom := by
              rw [rulesBottom]; exact bottomAtT
            let state0 : saturation.State :=
              { subsumers := v, active := v4, out := v1, into := v1,
                queue := alloc.vec.Vec.new saturation.Fact, next := 0#usize }
            have state0Ok : StateOk.{u,v} T list.val (fun _ => False) state0 := {
              subsumers := fun x c h => by simp [state0, entries_empty allV] at h
              out := fun x r y h => by simp [state0, entries_empty allV1] at h
              into := fun y r x h => by simp [state0, entries_empty allV1] at h
              queue := fun f h => by simp [state0] at h
              active := fun x h => h.elim }
            obtain ⟨r6, run6, spec6⟩ := activate_spec state0 top top state0Ok topAtT
            cases r6 with
            | none => exact ⟨none, by simp [run0, run1, run2, run3, run4, runV, runV1, runV2, runV3, runV4, run5,
                empty, state0, run6], by simp⟩
            | some s1 =>
              obtain ⟨r7, run7, spec7⟩ := activate_all_spec _ s1 ids top 0#usize (spec6 s1 rfl) topAtT
              cases r7 with
              | none => exact ⟨none, by simp [run0, run1, run2, run3, run4, runV, runV1, runV2, runV3, runV4, run5,
                  empty, state0, run6, run7], by simp⟩
              | some s2 =>
                obtain ⟨r8, run8, spec8⟩ := saturate_spec okT rules sound rulesTopAt rulesBottomAt s2
                  core.num.Usize.MAX (spec7 s2 rfl)
                cases r8 with
                | none => exact ⟨none, by simp [run0, run1, run2, run3, run4, runV, runV1, runV2, runV3, runV4, run5,
                    empty, state0, run6, run7, run8], by simp⟩
                | some s3 =>
                  have s3Ok := spec8 s3 rfl
                  obtain ⟨b, runB, specB⟩ := closed_spec rules T.concepts s3
                  cases b with
                  | false => exact ⟨none, by simp [run0, run1, run2, run3, run4, runV, runV1, runV2, runV3, runV4,
                      run5, empty, state0, run6, run7, run8, runB], by simp⟩
                  | true =>
                    refine ⟨some (T, rules, s3, ids), by simp [run0, run1, run2, run3, run4, runV, runV1, runV2, runV3,
                      runV4, run5, empty, state0, run6, run7, run8, runB], fun T' rules' state' ids' same => ?_⟩
                    simp only [Option.some.injEq, Prod.mk.injEq] at same
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := same
                    refine ⟨t3, list.val, seen, ok3, okT, grownT, by rw [listIs]; exact inside3, fun I fixed => ?_,
                      by simpa using classIds, rulesTopAt, rulesBottomAt, complete,
                      state_ok_weaken s3Ok (fun _ h => h.elim), fun id member => ?_, specB rfl⟩
                    · rw [listIs, ← meaning3 I fixed]
                      simp
                    · obtain ⟨i, at_i⟩ := List.mem_iff_getElem?.mp member
                      exact s3Ok.active id.val (Or.inr ⟨i, id, by simp, at_i, rfl⟩)

/-! ### Classification -/

theorem with_anonymous_self {Object : Type u} {Value : Type v} (I : Interpretation Object Value) :
    withAnonymous I I.anonymousIndividuals = I := by
  cases I; rfl

/-- A model of the axioms satisfies every rule. -/
theorem model_models {items : alloc.vec.Vec AnnotatedAxiom} {t3 T : saturation.Table} {list : List saturation.Rule}
    (ok3 : TableOk t3) (grown : Extends t3 T) (inside3 : ∀ rule ∈ list, RuleInside t3 rule)
    (meaning3 : ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), Fixed I →
      ((∀ a ∈ items.val, satisfies I a.axiom) ↔ ∀ rule ∈ list, RuleHolds I t3.concepts.val t3.roles.val rule))
    {Native : Type w} {D : DatatypeMap Native} {V : Vocabulary} {Object : Type u} {Value : Type v}
    {embed : ValueEmbedding D Value} {I : Interpretation Object Value} (model : Model D embed V I items.val) :
    ∃ I' : Interpretation Object Value, Fixed I' ∧ Models.{u,v} T list I' ∧ I'.classes = I.classes := by
  obtain ⟨_, valid, assignment, holds⟩ := model
  have fixed : Fixed (withAnonymous I assignment) := ⟨valid.1, valid.2.1⟩
  refine ⟨withAnonymous I assignment, fixed, fun rule member => ?_, rfl⟩
  rw [holds_later _ ok3 grown (inside3 rule member)]
  exact (meaning3 _ fixed).mp holds rule member

/-- A class whose concept has `owl:Nothing` among its subsumers, or any class
    when `owl:Thing` does, has no instance in any model of the rules. -/
theorem no_instances {T : saturation.Table} {list : List saturation.Rule} {rules : saturation.Rules}
    {state : saturation.State} {keep : Nat → Prop} (topAt : T.concepts.val[rules.top.val]? = some .Top)
    (bottomAt : T.concepts.val[rules.bottom.val]? = some .Bottom) (stateOk : StateOk.{u,v} T list keep state)
    {id : Usize} {a : Class} (at_id : T.concepts.val[id.val]? = some (classConcept a))
    (empty : EmptyAt state rules.bottom (decide (rules.bottom ∈ entries state.subsumers.val rules.top.val)) id = true)
    {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (fixed : Fixed I)
    (models : Models.{u,v} T list I) (x : Object) : ¬ I.classes a x := by
  intro member
  simp only [EmptyAt, Bool.or_eq_true, decide_eq_true_eq] at empty
  rcases empty with inconsistent | unsat
  · exact meaning_bottom I bottomAt x
      (stateOk.subsumers rules.top.val rules.bottom inconsistent I models x (meaning_top I topAt x))
  · exact meaning_bottom I bottomAt x
      (stateOk.subsumers id.val rules.bottom unsat I models x ((meaning_class I fixed at_id x).mpr member))

/-- Saturation classifies the named classes of an EL ontology: for every listed
    class, whether the class is satisfiable and, for every pair of listed
    classes, whether the first is subsumed by the second, exactly as the
    semantics decides over every vocabulary and datatype map. -/
theorem classify_correct (items : alloc.vec.Vec AnnotatedAxiom) (classes : alloc.vec.Vec Class) :
    ∃ r, saturation.classify items classes = .ok r ∧
      ∀ result, r = some result →
        result.satisfiable.val.length = classes.val.length ∧
        result.subsumed.val.length = classes.val.length ∧
        (∀ (i : Nat) (a : Class), classes.val[i]? = some a → ∃ s : Bool, result.satisfiable.val[i]? = some s ∧
          ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary), IsVocabulary D V →
            (s = true ↔ ClassSatisfiable.{u, max w v, w} D V items.val (.Class a))) ∧
        (∀ (i j : Nat) (a b : Class), classes.val[i]? = some a → classes.val[j]? = some b →
          ∃ (row : alloc.vec.Vec Bool) (s : Bool), result.subsumed.val[i]? = some row ∧ row.val[j]? = some s ∧
            ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary), IsVocabulary D V →
              (s = true ↔ Subsumed.{u, max w v, w} D V items.val (.Class a) (.Class b))) := by
  rw [saturation.classify]
  obtain ⟨r1, run1, spec1⟩ := saturated_spec.{u, max w v} items classes
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some found =>
    obtain ⟨T, rules, state, ids⟩ := found
    obtain ⟨t3, list, seen, ok3, okT, grownT, inside3, meaning3, classIds, topAt, bottomAt, complete, stateOk,
      activeIds, closure⟩ := spec1 T rules state ids rfl
    have topInside : rules.top.val < state.subsumers.val.length := by
      rw [closure.subsumersLength]; exact closure.top
    have lookupTop : state.subsumers.index_usize rules.top = .ok state.subsumers.val[rules.top.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem topInside]
    have e0 := entries_lookup (List.getElem?_eq_getElem topInside)
    let inconsistent := decide (rules.bottom ∈ entries state.subsumers.val rules.top.val)
    obtain ⟨r2, run2, spec2⟩ := answers_from_spec state rules.bottom inconsistent ids 0#usize
      (alloc.vec.Vec.new Bool) (alloc.vec.Vec.new (alloc.vec.Vec Bool)) (by simp)
      ⟨by simp, by simp, fun i id lt => by simp at lt⟩
    have run2' : saturation.answers_from state rules.bottom
        (decide (rules.bottom ∈ state.subsumers.val[rules.top.val].val)) ids 0#usize (alloc.vec.Vec.new Bool)
        (alloc.vec.Vec.new (alloc.vec.Vec Bool)) = .ok r2 := by
      rw [← e0]; exact run2
    refine ⟨r2, by simp [run1, UScalar.lt_equiv, alloc.vec.Vec.len_val, topInside, lookupTop, has_spec, run2'],
      fun result same => ?_⟩
    obtain ⟨satsLength, rowsLength, answers⟩ := spec2 result same
    have idsLength : ids.val.length = classes.val.length := classIds.length_eq
    have insideT : ∀ rule ∈ list, RuleInside T rule := fun rule member => inside_later grownT (inside3 rule member)
    -- the concept of a listed class
    have conceptOf : ∀ (i : Nat) (a : Class), classes.val[i]? = some a →
        ∃ id, ids.val[i]? = some id ∧ T.concepts.val[id.val]? = some (classConcept a) := by
      intro i a at_a
      have inside : i < ids.val.length := by rw [idsLength]; exact (List.getElem?_eq_some_iff.mp at_a).1
      exact ⟨ids.val[i], List.getElem?_eq_getElem inside,
        forall2_lookup classIds i _ a (List.getElem?_eq_getElem inside) at_a⟩
    -- the canonical model at a satisfiable class
    have witness : ∀ (id : Usize) (a : Class), id ∈ ids.val → T.concepts.val[id.val]? = some (classConcept a) →
        EmptyAt state rules.bottom inconsistent id = false →
        ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary), IsVocabulary D V →
          ∃ root : Domain rules state, root.val = id ∧
            Model D (Rowl.AlcOntology.embedding.{v,w} D) V (lifted.{u,v,w} T rules state root D) items.val ∧
            classDenote (lifted.{u,v,w} T rules state root D) (.Class a) (ULift.up root) := by
      intro id a member at_id notEmpty Native D V vocabulary
      simp only [EmptyAt, Bool.or_eq_false_iff, decide_eq_false_iff_not] at notEmpty
      have inDomain : InDomain rules state id := ⟨activeIds id member, notEmpty.2⟩
      let root : Domain rules state := ⟨id, inDomain⟩
      have valid := Rowl.AlcOntology.owl_model_valid.{u,v,w} (canonical T rules state root) root (fun _ => root) D V
      have fixed := lifted_fixed.{u,v,w} (t := T) root D
      have models := canonical_models.{u,v,w} root D okT closure topAt bottomAt complete insideT
      refine ⟨root, rfl, ⟨vocabulary, valid, (lifted.{u,v,w} T rules state root D).anonymousIndividuals, ?_⟩, ?_⟩
      · rw [with_anonymous_self]
        exact (meaning3 _ fixed).mpr fun rule member => (holds_later _ ok3 grownT (inside3 rule member)).mp
          (models rule member)
      · have context := closure.contexts id (domain_inside closure root)
        have self := (context.1 inDomain.1).1
        rw [Rowl.Owl.classDenote, ← meaning_class _ fixed at_id]
        exact positive root D okT closure bottomAt id.val id rfl root self
    refine ⟨by rw [satsLength, idsLength], by rw [rowsLength, idsLength], fun i a at_a => ?_,
      fun i j a b at_a at_b => ?_⟩
    · obtain ⟨id, at_id, conceptAt⟩ := conceptOf i a at_a
      have lt : i < ids.val.length := (List.getElem?_eq_some_iff.mp at_id).1
      obtain ⟨satAt, _⟩ := answers i id lt at_id
      refine ⟨_, satAt, fun D V vocabulary => ?_⟩
      cases emptyIs : EmptyAt state rules.bottom inconsistent id with
      | false =>
        simp only [Bool.not_false, true_iff]
        obtain ⟨root, _, model, holds⟩ := witness id a (List.mem_of_getElem? at_id) conceptAt emptyIs D V vocabulary
        exact ⟨_, _, _, _, model, _, holds⟩
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, false_iff]
        rintro ⟨Object, Value, embed, I, model, x, holds⟩
        obtain ⟨I', fixed, models, sameClasses⟩ := model_models ok3 grownT inside3 meaning3 model
        rw [Rowl.Owl.classDenote, ← sameClasses] at holds
        exact no_instances topAt bottomAt stateOk conceptAt emptyIs I' fixed models x holds
    · obtain ⟨ida, at_ida, conceptA⟩ := conceptOf i a at_a
      obtain ⟨idb, at_idb, conceptB⟩ := conceptOf j b at_b
      have lt : i < ids.val.length := (List.getElem?_eq_some_iff.mp at_ida).1
      obtain ⟨_, row, rowAt, rowIs⟩ := answers i ida lt at_ida
      have cellAt : row.val[j]? = some (EmptyAt state rules.bottom inconsistent ida ||
          decide (idb ∈ entries state.subsumers.val ida.val)) := by
        rw [rowIs, List.getElem?_map, at_idb]; rfl
      refine ⟨row, _, rowAt, cellAt, fun D V vocabulary => ?_⟩
      constructor
      · intro yes Object Value embed I model x holds
        obtain ⟨I', fixed, models, sameClasses⟩ := model_models ok3 grownT inside3 meaning3 model
        rw [Rowl.Owl.classDenote, ← sameClasses] at holds ⊢
        cases emptyIs : EmptyAt state rules.bottom inconsistent ida with
        | true => exact absurd holds (no_instances topAt bottomAt stateOk conceptA emptyIs I' fixed models x)
        | false =>
          rw [emptyIs, Bool.false_or, decide_eq_true_eq] at yes
          have sub := stateOk.subsumers ida.val idb yes I' models x ((meaning_class I' fixed conceptA x).mpr holds)
          exact (meaning_class I' fixed conceptB x).mp sub
      · intro subsumed
        cases emptyIs : EmptyAt state rules.bottom inconsistent ida with
        | true => simp
        | false =>
          simp only [Bool.false_or, decide_eq_true_eq]
          obtain ⟨root, rootIs, model, holds⟩ := witness ida a (List.mem_of_getElem? at_ida) conceptA emptyIs D V
            vocabulary
          have there := subsumed _ _ _ _ model _ holds
          rw [Rowl.Owl.classDenote, ← meaning_class _ (lifted_fixed.{u,v,w} (t := T) root D) conceptB] at there
          have found := negative root D okT closure topAt complete idb.val idb rfl (Or.inr (class_simple conceptB))
            root there
          rw [rootIs] at found
          exact found

end Rowl.Saturation
