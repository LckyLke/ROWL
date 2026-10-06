import Rowl.RdfMapping
import Rowl.Builtins

/-!
# Acceptance completeness of the RDF mapping for the EL fragment

`Rowl.RdfMapping.map_graph_correct` proves that whatever `rdf_mapping::map_graph`
reads is right. This module proves the converse for the EL fragment: the graph of
the forward mapping (`Rowl.RdfMapping.TOntology`) of every ontology of the
fragment is read back to exactly that ontology (`map_graph_complete`).

The fragment (`ElOntology`) is the ontologies that are anonymous or named without
a version IRI, without imports or ontology annotations, whose axioms are
unannotated declarations and subclass axioms between class expressions built from
named classes and existential restrictions of object properties. Each such
property is declared as an object property and neither declared nor built in as a
data or annotation property (`ObjectTyped`), and no main triple of an axiom is
about the ontology IRI. The graph lists the triples of the forward mapping in its
order, with pairwise distinct blank nodes.

The proof follows the reader: the declaration and subject indexes are complete
(`declared_kinds_spec`, `subjects_from_spec`), so their lookups find exactly the
triples of each construct (`find_hit`, `find_type_hit`); the blank nodes of a
construct have their triples in its block of the graph (`Owned`), and each block
is read whole, in order (`existential_complete`, `sub_class_complete`,
`read_axiom_declaration`, `axioms_complete`).
-/

namespace Rowl.RdfMappingComplete
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust Rowl.RdfMapping
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false


theorem array_slice_val (n : Usize) (bytes : List U8) (h : bytes.length = n.val) :
    (Array.to_slice (Array.make n bytes h)).val = bytes := by
  simp [Array.to_slice, Array.make]

theorem mix_ok (hash : Usize) (byte : U8) : ∃ m, rdf_mapping.mix hash byte = .ok m := by
  have nonzero : (16777216#usize : Usize).val ≠ 0 := by decide
  obtain ⟨i, iRun, iValue⟩ := WP.spec_imp_exists (UScalar.rem_spec hash (y := 16777216#usize) nonzero)
  have iLt : i.val < 16777216 := by
    rw [iValue]
    exact Nat.mod_lt _ (by decide)
  obtain ⟨i1, i1Run, i1Value⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := i) (y := 31#usize)
    (by have : (31#usize : Usize).val = 31 := rfl; rw [this]; scalar_tac))
  have i1Lt : i1.val < 16777216 * 31 := by
    have : (31#usize : Usize).val = 31 := rfl
    rw [i1Value, this]
    omega
  have castLt : (UScalar.cast .Usize byte).val < 256 := by
    simp [UScalar.cast_val_eq]
    have bound : byte.val < 256 := by have := byte.hBounds; simpa using this
    exact lt_of_le_of_lt (Nat.mod_le _ _) bound
  obtain ⟨m, mRun, -⟩ := WP.spec_imp_exists (UScalar.add_spec (x := i1) (y := UScalar.cast .Usize byte)
    (by scalar_tac))
  exact ⟨m, by simp [rdf_mapping.mix, iRun, i1Run, lift, mRun]⟩

theorem hash_from_ok (bytes : alloc.vec.Vec U8) :
    ∀ (index hash : Usize), ∃ h, rdf_mapping.hash_from bytes index hash = .ok h := by
  intro index
  induction e : bytes.val.length - index.val generalizing index with
  | zero =>
    intro hash
    have done : ¬ index.val < bytes.val.length := by omega
    exact ⟨hash, by rw [rdf_mapping.hash_from]; simp [UScalar.lt_equiv, done]⟩
  | succ n ih =>
    intro hash
    have more : index.val < bytes.val.length := by omega
    have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨m, mixRun⟩ := mix_ok hash bytes.val[index.val]
    obtain ⟨h, run⟩ := ih next (by omega) m
    exact ⟨h, by rw [rdf_mapping.hash_from]; simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, advance, lookup,
      mixRun, run]⟩

theorem hash_blank_ok (node : rdf.BlankNode) : ∃ h, rdf_mapping.hash_blank node = .ok h := by
  obtain ⟨h1, run1⟩ := hash_from_ok node.scope 0#usize 7#usize
  obtain ⟨h2, run2⟩ := hash_from_ok node.label 0#usize h1
  exact ⟨h2, by simp [rdf_mapping.hash_blank, run1, run2]⟩

theorem bucket_of_spec (hash count : Usize) :
    ∃ b, rdf_mapping.bucket_of hash count = .ok b ∧ (0 < count.val → b.val < count.val) := by
  rw [rdf_mapping.bucket_of]
  by_cases positive : 0#usize < count
  · have nonzero : count.val ≠ 0 := by scalar_tac
    obtain ⟨b, run, value⟩ := WP.spec_imp_exists (UScalar.rem_spec hash (y := count) nonzero)
    exact ⟨b, by simp [positive, run], fun _ => by rw [value]; exact Nat.mod_lt _ (by omega)⟩
  · exact ⟨0#usize, by simp [positive], fun h => by scalar_tac⟩

/-- The bucket a blank node's triples go to among `count` buckets. -/
def BucketOf (node : rdf.BlankNode) (count : Usize) (bucket : Usize) : Prop :=
  ∃ h, rdf_mapping.hash_blank node = .ok h ∧ rdf_mapping.bucket_of h count = .ok bucket

/-- The subject index of `triples`: every triple whose subject is a blank node
    has its position in the bucket of that node. -/
def SubjectsComplete (triples : List rdf.Triple) (subjects : List (alloc.vec.Vec Usize)) (count : Usize)
    (below : Nat) : Prop :=
  ∀ (i : Nat) (t : rdf.Triple) (node : rdf.BlankNode) (bucket : Usize), i < below → triples[i]? = some t →
    t.subject = .Blank node → BucketOf node count bucket →
    ∃ b, subjects[bucket.val]? = some b ∧ ∃ k ∈ b.val, k.val = i

theorem subjects_from_spec (triples : alloc.vec.Vec rdf.Triple) :
    ∀ (index : Usize) (buckets result : alloc.vec.Vec (alloc.vec.Vec Usize)),
      0 < buckets.val.length → (∀ b ∈ buckets.val, b.val.length ≤ index.val) →
      SubjectsComplete triples.val buckets.val (alloc.vec.Vec.len buckets) index.val →
      rdf_mapping.subjects_from triples index buckets = .ok result →
      result.val.length = buckets.val.length ∧
        SubjectsComplete triples.val result.val (alloc.vec.Vec.len buckets) triples.val.length := by
  intro index
  induction e : triples.val.length - index.val generalizing index with
  | zero =>
    intro buckets result positive small complete ran
    rw [rdf_mapping.subjects_from] at ran
    have done : ¬ index.val < triples.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    subst ran
    refine ⟨rfl, fun i t node bucket inside at_i blank which => ?_⟩
    have : index.val ≥ triples.val.length := by omega
    exact complete i t node bucket (by have := (List.getElem?_eq_some_iff.mp at_i).1; omega) at_i blank which
  | succ n ih =>
    intro buckets result positive small complete ran
    rw [rdf_mapping.subjects_from] at ran
    have more : index.val < triples.val.length := by omega
    have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup, bind_ok] at ran
    cases subject : triples.val[index.val].subject with
    | Iri iri =>
      simp only [subject, advance, bind_ok] at ran
      exact ih next (by omega) buckets result positive (fun b member => by have := small b member; omega)
        (fun i t node bucket inside at_i blank which => by
          by_cases here : i = index.val
          · subst here
            rw [List.getElem?_eq_getElem more] at at_i
            cases at_i
            rw [subject] at blank
            cases blank
          · exact complete i t node bucket (by omega) at_i blank which) ran
    | Blank node =>
      simp only [subject] at ran
      obtain ⟨h, hashRun⟩ := hash_blank_ok node
      obtain ⟨bucket, bucketRun, bucketLt⟩ := bucket_of_spec h (alloc.vec.Vec.len buckets)
      simp only [hashRun, bucketRun, bind_ok] at ran
      have inside : bucket.val < buckets.val.length := by
        have := bucketLt (by simpa using positive)
        simpa using this
      have entry : buckets.index_usize bucket = .ok buckets.val[bucket.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      have fits : buckets.val[bucket.val].val.length < Usize.max := by
        have := small _ (List.getElem_mem inside)
        have : triples.val.length ≤ Usize.max := triples.property
        omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec buckets.val[bucket.val] index fits)
      simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, inside, entry, fits,
        alloc.vec.Vec.index_mut_usize, push, advance] at ran
      have sameLength : (buckets.set bucket pushed).val.length = buckets.val.length := by
        simp [alloc.vec.Vec.set_val_eq]
      have sameLen : alloc.vec.Vec.len (buckets.set bucket pushed) = alloc.vec.Vec.len buckets := by
        apply UScalar.eq_of_val_eq
        simp [alloc.vec.Vec.len_val, sameLength]
      obtain ⟨length, done⟩ := ih next (by omega) _ result (by rw [sameLength]; exact positive)
        (by
          intro b member
          rw [alloc.vec.Vec.set_val_eq] at member
          obtain ⟨j, at_j⟩ := List.mem_iff_getElem?.mp member
          by_cases same : j = bucket.val
          · subst same
            rw [List.getElem?_set_self inside] at at_j
            cases at_j
            rw [contents]
            simp
            have := small _ (List.getElem_mem inside)
            omega
          · rw [List.getElem?_set_ne (Ne.symm same)] at at_j
            have := small b (List.mem_of_getElem? at_j)
            omega)
        (by
          rw [sameLen]
          intro i t node' bucket' below at_i blank which
          by_cases here : i = index.val
          · subst here
            rw [List.getElem?_eq_getElem more] at at_i
            cases at_i
            rw [subject] at blank
            cases blank
            obtain ⟨h', hashRun', bucketRun'⟩ := which
            rw [hashRun] at hashRun'
            cases Result.ok_injective hashRun'
            rw [bucketRun] at bucketRun'
            cases Result.ok_injective bucketRun'
            refine ⟨pushed, by simp [alloc.vec.Vec.set_val_eq, List.getElem?_set_self inside], index, ?_, rfl⟩
            rw [contents]
            simp
          · obtain ⟨b, at_b, k, member, kIs⟩ := complete i t node' bucket' (by omega) at_i blank which
            by_cases same : bucket'.val = bucket.val
            · rw [same, List.getElem?_eq_getElem inside] at at_b
              cases at_b
              refine ⟨pushed, by simp [alloc.vec.Vec.set_val_eq, same, List.getElem?_set_self inside], k, ?_, kIs⟩
              rw [contents]
              exact List.mem_append_left _ member
            · exact ⟨b, by rw [alloc.vec.Vec.set_val_eq, List.getElem?_set_ne (Ne.symm same)]; exact at_b, k,
                member, kIs⟩)
        ran
      exact ⟨by rw [length, sameLength], by rw [← sameLen]; exact done⟩


/-- `fits` decides exactly whether the triple at `index` is unused, about the
    node and has the predicate. -/
theorem fits_correct (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool) (index : Usize)
    (node : rdf.BlankNode) (key : Slice U8) :
    rdf_mapping.fits triples used index node key = .ok (decide (∃ t, Unused triples.val used.val index.val t ∧
      subjectView t.subject = .blank node ∧ t.predicate.spelling.val = key.val)) := by
  rw [rdf_mapping.fits]
  by_cases more : index.val < triples.val.length
  · have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, about_correct, same_correct]
    have at_t : triples.val[index.val]? = some triples.val[index.val] := List.getElem?_eq_getElem more
    by_cases isUsed : used.val[index.val]? = some false
    · simp only [isUsed, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases here : subjectView triples.val[index.val].subject = .blank node
      · simp only [here, decide_true, ↓reduceIte, Result.ok.injEq]
        congr 1
        apply propext
        constructor
        · intro named; exact ⟨_, ⟨at_t, isUsed⟩, here, named⟩
        · rintro ⟨t, ⟨at_i, -⟩, -, named⟩
          rw [at_t] at at_i
          cases at_i
          exact named
      · simp only [here, decide_false, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq]
        symm
        simp only [decide_eq_false_iff_not, not_exists, not_and]
        rintro t ⟨at_i, -⟩ about
        rw [at_t] at at_i
        cases at_i
        exact absurd about here
    · simp only [isUsed, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, Result.ok.injEq]
      symm
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      rintro t ⟨-, used⟩
      exact absurd used isUsed
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, Result.ok.injEq]
    symm
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    rintro t ⟨at_i, -⟩
    have := (List.getElem?_eq_some_iff.mp at_i).1
    omega

/-- A bucket search that finds nothing leaves no candidate that fits. -/
theorem find_in_none (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool)
    (bucket : alloc.vec.Vec Usize) (node : rdf.BlankNode) (key : Slice U8) (k : Usize)
    (ran : rdf_mapping.find_in triples used bucket node key k = .ok none) :
    ∀ (j : Nat) (pos : Usize), k.val ≤ j → bucket.val[j]? = some pos →
      ¬ ∃ t, Unused triples.val used.val pos.val t ∧ subjectView t.subject = .blank node ∧
        t.predicate.spelling.val = key.val := by
  rw [rdf_mapping.find_in] at ran
  by_cases more : k.val < bucket.val.length
  · have lookup : bucket.index_usize k = .ok bucket.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = k.val + 1 := by simpa using nextValue
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, fits_correct] at ran
    by_cases fit : ∃ t, Unused triples.val used.val bucket.val[k.val].val t ∧ subjectView t.subject = .blank node ∧
        t.predicate.spelling.val = key.val
    · simp [fit] at ran
    · simp only [fit, decide_false, Bool.false_eq_true, ↓reduceIte, advance, bind_ok] at ran
      intro j pos low at_j
      by_cases here : j = k.val
      · subst here
        rw [List.getElem?_eq_getElem more] at at_j
        cases at_j
        exact fit
      · exact find_in_none triples used bucket node key next ran j pos (by omega) at_j
  · intro j pos low at_j
    have := (List.getElem?_eq_some_iff.mp at_j).1
    omega
termination_by bucket.val.length - k.val
decreasing_by all_goals (have := nextValue; simp at this; omega)

/-- With a complete subject index, a lookup that finds nothing proves that no
    unused triple about the node has the predicate. -/
theorem find_none (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (node : rdf.BlankNode)
    (key : Slice U8) (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects)
      triples.val.length)
    (ran : rdf_mapping.find triples s node key = .ok none) :
    ∀ (i : Nat) (t : rdf.Triple), Unused triples.val s.used.val i t → subjectView t.subject = .blank node →
      t.predicate.spelling.val ≠ key.val := by
  intro i t unused about named
  rw [rdf_mapping.find] at ran
  obtain ⟨h, hashRun, ran⟩ := bind_eq_ok ran
  obtain ⟨bucket, bucketRun, ran⟩ := bind_eq_ok ran
  have blank : t.subject = .Blank node := by
    cases subject : t.subject with
    | Iri _ => rw [subject] at about; simp [subjectView] at about
    | Blank b => rw [subject] at about; simp [subjectView] at about; rw [about]
  obtain ⟨b, at_b, k, member, kIs⟩ := complete i t node bucket (List.getElem?_eq_some_iff.mp unused.1).1 unused.1 blank
    ⟨h, hashRun, bucketRun⟩
  have inside : bucket.val < s.subjects.val.length := (List.getElem?_eq_some_iff.mp at_b).1
  have lookup : s.subjects.index_usize bucket = .ok s.subjects.val[bucket.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
    lookup, bind_ok] at ran
  rw [List.getElem?_eq_getElem inside] at at_b
  cases at_b
  obtain ⟨j, at_j⟩ := List.mem_iff_getElem?.mp member
  exact find_in_none triples s.used _ node key 0#usize ran j k (by simp) at_j ⟨t, by rw [kIs]; exact unused, about, named⟩

theorem same_kind_correct (left right : typing.EntityKind) :
    rdf_mapping.same_kind left right = .ok (decide (left = right)) := by
  cases left <;> cases right <;> simp [rdf_mapping.same_kind]

/-- `declared_in` decides exactly whether `bucket[index..]` holds the declaration. -/
theorem declared_in_correct (bucket : alloc.vec.Vec rdf_mapping.Declared) (iri : alloc.vec.Vec U8)
    (kind : typing.EntityKind) :
    ∀ (index : Usize), rdf_mapping.declared_in bucket iri kind index =
      .ok (decide (∃ (j : Nat) (d : rdf_mapping.Declared), index.val ≤ j ∧ bucket.val[j]? = some d ∧ d.iri = iri ∧
        d.kind = kind)) := by
  intro index
  induction e : bucket.val.length - index.val generalizing index with
  | zero =>
    rw [rdf_mapping.declared_in]
    have done : ¬ index.val < bucket.val.length := by omega
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, done, ↓reduceIte, Result.ok.injEq]
    symm
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro j d low at_j
    have := (List.getElem?_eq_some_iff.mp at_j).1
    omega
  | succ n ih =>
    rw [rdf_mapping.declared_in]
    have more : index.val < bucket.val.length := by omega
    have lookup : bucket.index_usize index = .ok bucket.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have rest := ih next (by omega)
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
      bind_ok, same_vec_correct, same_kind_correct, advance, rest]
    have at_index : bucket.val[index.val]? = some bucket.val[index.val] := List.getElem?_eq_getElem more
    by_cases sameIri : bucket.val[index.val].iri = iri
    · by_cases sameKind : bucket.val[index.val].kind = kind
      · simp only [sameIri, sameKind, decide_true, ↓reduceIte, Result.ok.injEq]
        symm
        exact decide_eq_true ⟨index.val, _, le_refl _, at_index, sameIri, sameKind⟩
      · simp only [sameIri, sameKind, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true, Result.ok.injEq]
        congr 1
        apply propext
        constructor
        · rintro ⟨j, d, low, at_j, hi, hk⟩
          exact ⟨j, d, by omega, at_j, hi, hk⟩
        · rintro ⟨j, d, low, at_j, hi, hk⟩
          by_cases here : j = index.val
          · subst here
            rw [at_index] at at_j
            cases at_j
            exact absurd hk sameKind
          · exact ⟨j, d, by omega, at_j, hi, hk⟩
    · simp only [sameIri, decide_false, ↓reduceIte, Bool.false_eq_true, Result.ok.injEq]
      congr 1
      apply propext
      constructor
      · rintro ⟨j, d, low, at_j, hi, hk⟩
        exact ⟨j, d, by omega, at_j, hi, hk⟩
      · rintro ⟨j, d, low, at_j, hi, hk⟩
        by_cases here : j = index.val
        · subst here
          rw [at_index] at at_j
          cases at_j
          exact absurd hi sameIri
        · exact ⟨j, d, by omega, at_j, hi, hk⟩



/-- Every pattern of the list is about one of the nodes. -/
def SubjectsIn (nodes : List rdf.BlankNode) (ps : List Pattern) : Prop :=
  ∀ p ∈ ps, ∃ y ∈ nodes, p.subject = .blank y

theorem subjects_in_nil (nodes : List rdf.BlankNode) : SubjectsIn nodes [] := by
  intro p member; simp at member

theorem subjects_in_append {nodes : List rdf.BlankNode} {ps qs : List Pattern} (h1 : SubjectsIn nodes ps)
    (h2 : SubjectsIn nodes qs) : SubjectsIn nodes (ps ++ qs) := by
  intro p member
  rcases List.mem_append.mp member with left | right
  · exact h1 p left
  · exact h2 p right

theorem subjects_in_mono {nodes nodes' : List rdf.BlankNode} {ps : List Pattern} (h : SubjectsIn nodes ps)
    (sub : ∀ y ∈ nodes, y ∈ nodes') : SubjectsIn nodes' ps := by
  intro p member
  obtain ⟨y, inside, about⟩ := h p member
  exact ⟨y, sub y inside, about⟩

theorem list_of_subjects : ∀ (cells : List rdf.BlankNode) (elements : List Node),
    SubjectsIn cells (listOf cells elements).2
  | [], _ => by simp [listOf, subjects_in_nil]
  | _ :: _, [] => by simp [listOf, subjects_in_nil]
  | c :: cells, e :: elements => by
    intro p member
    simp only [listOf, List.mem_cons] at member
    rcases member with rfl | rfl | rest
    · exact ⟨c, by simp, rfl⟩
    · exact ⟨c, by simp, rfl⟩
    · obtain ⟨y, inside, about⟩ := list_of_subjects cells elements p rest
      exact ⟨y, List.mem_cons_of_mem _ inside, about⟩

theorem tope_fresh {e : model.ObjectPropertyExpression} {s : Supply} {n : Node} {ps : List Pattern} {s' : Supply}
    (h : TOPE e s n ps s') : ∃ fresh, s = fresh ++ s' ∧ SubjectsIn fresh ps := by
  cases h with
  | named => exact ⟨[], by simp, subjects_in_nil _⟩
  | inverse property x s => exact ⟨[x], by simp, fun p member => by simp at member; subst member; exact ⟨x, by simp, rfl⟩⟩

theorem tfacets_fresh {fs : List model.FacetRestriction} {s : Supply} {ns : List Node} {ps : List Pattern}
    {s' : Supply} (h : TFacets fs s ns ps s') : ∃ fresh, s = fresh ++ s' ∧ SubjectsIn fresh ps := by
  induction h with
  | nil s => exact ⟨[], by simp, subjects_in_nil _⟩
  | cons f fs y s s' value ns ps literal tail ih =>
    obtain ⟨fresh, eq, sub⟩ := ih
    refine ⟨y :: fresh, by rw [eq]; rfl, ?_⟩
    intro p member
    simp only [List.mem_cons] at member
    rcases member with rfl | rest
    · exact ⟨y, by simp, rfl⟩
    · obtain ⟨z, inside, about⟩ := sub p rest
      exact ⟨z, List.mem_cons_of_mem _ inside, about⟩

mutual
theorem tdr_fresh : ∀ {d : model.DataRange} {s : Supply} {n : Node} {ps : List Pattern} {s' : Supply},
    TDR d s n ps s' → ∃ fresh, s = fresh ++ s' ∧ SubjectsIn fresh ps
  | _, _, _, _, _, .datatype _ _ => ⟨[], by simp, subjects_in_nil _⟩
  | _, _, _, _, _, .intersection _ x cells _ _ _ _ _ inner => by
    obtain ⟨f, eq, sub⟩ := tdrs_fresh inner
    refine ⟨x :: (cells ++ f), by rw [eq]; simp, ?_⟩
    intro p member
    simp only [List.mem_cons, List.mem_append] at member
    rcases member with rfl | rfl | cellsPart | innerPart
    · exact ⟨x, by simp, rfl⟩
    · exact ⟨x, by simp, rfl⟩
    · obtain ⟨y, inside, about⟩ := list_of_subjects _ _ p cellsPart
      exact ⟨y, by simp [inside], about⟩
    · obtain ⟨y, inside, about⟩ := sub p innerPart
      exact ⟨y, by simp [inside], about⟩
  | _, _, _, _, _, .union _ x cells _ _ _ _ _ inner => by
    obtain ⟨f, eq, sub⟩ := tdrs_fresh inner
    refine ⟨x :: (cells ++ f), by rw [eq]; simp, ?_⟩
    intro p member
    simp only [List.mem_cons, List.mem_append] at member
    rcases member with rfl | rfl | cellsPart | innerPart
    · exact ⟨x, by simp, rfl⟩
    · exact ⟨x, by simp, rfl⟩
    · obtain ⟨y, inside, about⟩ := list_of_subjects _ _ p cellsPart
      exact ⟨y, by simp [inside], about⟩
    · obtain ⟨y, inside, about⟩ := sub p innerPart
      exact ⟨y, by simp [inside], about⟩
  | _, _, _, _, _, .complement _ x _ _ _ _ inner => by
    obtain ⟨f, eq, sub⟩ := tdr_fresh inner
    refine ⟨x :: f, by rw [eq]; simp, ?_⟩
    intro p member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | innerPart
    · exact ⟨x, by simp, rfl⟩
    · exact ⟨x, by simp, rfl⟩
    · obtain ⟨y, inside, about⟩ := sub p innerPart
      exact ⟨y, by simp [inside], about⟩
  | _, _, _, _, _, .oneOf _ x cells _ _ _ _ => by
    refine ⟨x :: cells, by simp, ?_⟩
    intro p member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | cellsPart
    · exact ⟨x, by simp, rfl⟩
    · exact ⟨x, by simp, rfl⟩
    · obtain ⟨y, inside, about⟩ := list_of_subjects _ _ p cellsPart
      exact ⟨y, by simp [inside], about⟩
  | _, _, _, _, _, .restriction _ _ x cells _ _ _ _ _ facets => by
    obtain ⟨f, eq, sub⟩ := tfacets_fresh facets
    refine ⟨x :: (cells ++ f), by rw [eq]; simp, ?_⟩
    intro p member
    simp only [List.mem_cons, List.mem_append] at member
    rcases member with rfl | rfl | rfl | cellsPart | innerPart
    · exact ⟨x, by simp, rfl⟩
    · exact ⟨x, by simp, rfl⟩
    · exact ⟨x, by simp, rfl⟩
    · obtain ⟨y, inside, about⟩ := list_of_subjects _ _ p cellsPart
      exact ⟨y, by simp [inside], about⟩
    · obtain ⟨y, inside, about⟩ := sub p innerPart
      exact ⟨y, by simp [inside], about⟩

theorem tdrs_fresh : ∀ {ds : List model.DataRange} {s : Supply} {ns : List Node} {ps : List Pattern} {s' : Supply},
    TDRs ds s ns ps s' → ∃ fresh, s = fresh ++ s' ∧ SubjectsIn fresh ps
  | _, _, _, _, _, .nil _ => ⟨[], by simp, subjects_in_nil _⟩
  | _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ head tail => by
    obtain ⟨f1, eq1, sub1⟩ := tdr_fresh head
    obtain ⟨f2, eq2, sub2⟩ := tdrs_fresh tail
    refine ⟨f1 ++ f2, by rw [eq1, eq2, List.append_assoc], subjects_in_append ?_ ?_⟩
    · exact subjects_in_mono sub1 (fun _ m => List.mem_append_left _ m)
    · exact subjects_in_mono sub2 (fun _ m => List.mem_append_right _ m)
end

theorem subjects_cons {x : rdf.BlankNode} {fresh : List rdf.BlankNode} {p : Pattern} {ps : List Pattern}
    (head : p.subject = .blank x) (rest : SubjectsIn (x :: fresh) ps) : SubjectsIn (x :: fresh) (p :: ps) := by
  intro q member
  rcases List.mem_cons.mp member with rfl | tail
  · exact ⟨x, by simp, head⟩
  · exact rest q tail

theorem subjects_widen {x : rdf.BlankNode} {fresh : List rdf.BlankNode} {ps : List Pattern}
    (h : SubjectsIn fresh ps) : SubjectsIn (x :: fresh) ps :=
  subjects_in_mono h (fun _ m => List.mem_cons_of_mem _ m)

theorem subjects_pair {f1 f2 : List rdf.BlankNode} {ps qs : List Pattern} (h1 : SubjectsIn f1 ps)
    (h2 : SubjectsIn f2 qs) : SubjectsIn (f1 ++ f2) (ps ++ qs) :=
  subjects_in_append (subjects_in_mono h1 (fun _ m => List.mem_append_left _ m))
    (subjects_in_mono h2 (fun _ m => List.mem_append_right _ m))

mutual
theorem tce_fresh : ∀ {c : model.ClassExpression} {s : Supply} {n : Node} {ps : List Pattern} {s' : Supply},
    TCE c s n ps s' → ∃ fresh, s = fresh ++ s' ∧ SubjectsIn fresh ps
  | _, _, _, _, _, .named _ _ => ⟨[], by simp, subjects_in_nil _⟩
  | _, _, _, _, _, .intersection _ x cells _ _ _ _ _ inner => by
    obtain ⟨f, eq, sub⟩ := tces_fresh inner
    refine ⟨x :: (cells ++ f), by rw [eq]; simp, ?_⟩
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen (subjects_pair (list_of_subjects _ _) sub)
  | _, _, _, _, _, .union _ x cells _ _ _ _ _ inner => by
    obtain ⟨f, eq, sub⟩ := tces_fresh inner
    refine ⟨x :: (cells ++ f), by rw [eq]; simp, ?_⟩
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen (subjects_pair (list_of_subjects _ _) sub)
  | _, _, _, _, _, .complement _ x _ _ _ _ inner => by
    obtain ⟨f, eq, sub⟩ := tce_fresh inner
    refine ⟨x :: f, by rw [eq]; simp, ?_⟩
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen sub
  | _, _, _, _, _, .oneOf _ x cells _ _ => by
    refine ⟨x :: cells, by simp, ?_⟩
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen (list_of_subjects _ _)
  | _, _, _, _, _, .some _ _ x _ _ _ _ _ _ _ role inner => by
    obtain ⟨f1, eq1, sub1⟩ := tope_fresh role
    obtain ⟨f2, eq2, sub2⟩ := tce_fresh inner
    refine ⟨x :: (f1 ++ f2), by rw [eq1, eq2]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen (subjects_pair sub1 sub2)
  | _, _, _, _, _, .all _ _ x _ _ _ _ _ _ _ role inner => by
    obtain ⟨f1, eq1, sub1⟩ := tope_fresh role
    obtain ⟨f2, eq2, sub2⟩ := tce_fresh inner
    refine ⟨x :: (f1 ++ f2), by rw [eq1, eq2]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen (subjects_pair sub1 sub2)
  | _, _, _, _, _, .hasValue _ _ x _ _ _ _ role => by
    obtain ⟨f1, eq1, sub1⟩ := tope_fresh role
    refine ⟨x :: f1, by rw [eq1]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen sub1
  | _, _, _, _, _, .hasSelf _ x _ _ _ _ role => by
    obtain ⟨f1, eq1, sub1⟩ := tope_fresh role
    refine ⟨x :: f1, by rw [eq1]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen sub1
  | _, _, _, _, _, .min _ _ x _ _ _ _ _ role _ => by
    obtain ⟨f1, eq1, sub1⟩ := tope_fresh role
    refine ⟨x :: f1, by rw [eq1]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen sub1
  | _, _, _, _, _, .max _ _ x _ _ _ _ _ role _ => by
    obtain ⟨f1, eq1, sub1⟩ := tope_fresh role
    refine ⟨x :: f1, by rw [eq1]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen sub1
  | _, _, _, _, _, .exact _ _ x _ _ _ _ _ role _ => by
    obtain ⟨f1, eq1, sub1⟩ := tope_fresh role
    refine ⟨x :: f1, by rw [eq1]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen sub1
  | _, _, _, _, _, .minQualified _ _ _ x _ _ _ _ _ _ _ _ role _ inner => by
    obtain ⟨f1, eq1, sub1⟩ := tope_fresh role
    obtain ⟨f2, eq2, sub2⟩ := tce_fresh inner
    refine ⟨x :: (f1 ++ f2), by rw [eq1, eq2]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen (subjects_pair sub1 sub2)
  | _, _, _, _, _, .maxQualified _ _ _ x _ _ _ _ _ _ _ _ role _ inner => by
    obtain ⟨f1, eq1, sub1⟩ := tope_fresh role
    obtain ⟨f2, eq2, sub2⟩ := tce_fresh inner
    refine ⟨x :: (f1 ++ f2), by rw [eq1, eq2]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen (subjects_pair sub1 sub2)
  | _, _, _, _, _, .exactQualified _ _ _ x _ _ _ _ _ _ _ _ role _ inner => by
    obtain ⟨f1, eq1, sub1⟩ := tope_fresh role
    obtain ⟨f2, eq2, sub2⟩ := tce_fresh inner
    refine ⟨x :: (f1 ++ f2), by rw [eq1, eq2]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen (subjects_pair sub1 sub2)
  | _, _, _, _, _, .dataSome _ _ x _ _ _ _ inner => by
    obtain ⟨f, eq, sub⟩ := tdr_fresh inner
    refine ⟨x :: f, by rw [eq]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen sub
  | _, _, _, _, _, .dataAll _ _ x _ _ _ _ inner => by
    obtain ⟨f, eq, sub⟩ := tdr_fresh inner
    refine ⟨x :: f, by rw [eq]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen sub
  | _, _, _, _, _, .dataHasValue _ _ x _ _ _ => by
    refine ⟨[x], by simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_in_nil _
  | _, _, _, _, _, .dataMin _ _ x _ _ _ => by
    refine ⟨[x], by simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_in_nil _
  | _, _, _, _, _, .dataMax _ _ x _ _ _ => by
    refine ⟨[x], by simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_in_nil _
  | _, _, _, _, _, .dataExact _ _ x _ _ _ => by
    refine ⟨[x], by simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_in_nil _
  | _, _, _, _, _, .dataMinQualified _ _ _ x _ _ _ _ _ _ inner => by
    obtain ⟨f, eq, sub⟩ := tdr_fresh inner
    refine ⟨x :: f, by rw [eq]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen sub
  | _, _, _, _, _, .dataMaxQualified _ _ _ x _ _ _ _ _ _ inner => by
    obtain ⟨f, eq, sub⟩ := tdr_fresh inner
    refine ⟨x :: f, by rw [eq]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen sub
  | _, _, _, _, _, .dataExactQualified _ _ _ x _ _ _ _ _ _ inner => by
    obtain ⟨f, eq, sub⟩ := tdr_fresh inner
    refine ⟨x :: f, by rw [eq]; simp, ?_⟩
    simp only [restrictionHead, List.cons_append, List.nil_append]
    repeat (refine subjects_cons rfl ?_)
    exact subjects_widen sub

theorem tces_fresh : ∀ {cs : List model.ClassExpression} {s : Supply} {ns : List Node} {ps : List Pattern}
    {s' : Supply}, TCEs cs s ns ps s' → ∃ fresh, s = fresh ++ s' ∧ SubjectsIn fresh ps
  | _, _, _, _, _, .nil _ => ⟨[], by simp, subjects_in_nil _⟩
  | _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ head tail => by
    obtain ⟨f1, eq1, sub1⟩ := tce_fresh head
    obtain ⟨f2, eq2, sub2⟩ := tces_fresh tail
    exact ⟨f1 ++ f2, by rw [eq1, eq2, List.append_assoc], subjects_pair sub1 sub2⟩
end



/-- `s'` is `s` with the positions `marked` used and the blank nodes `fresh`
    recorded; the indexes are unchanged. -/
structure Marked (s s' : rdf_mapping.State) (marked : Nat → Prop) (fresh : List rdf.BlankNode) : Prop where
  subjects : s'.subjects = s.subjects
  sources : s'.sources = s.sources
  blanks : s'.blanks.val = s.blanks.val ++ fresh
  length : s'.used.val.length = s.used.val.length
  used : ∀ (i : Nat), i < s.used.val.length → (s'.used.val[i]? = some true ↔ (s.used.val[i]? = some true ∨ marked i))

theorem marked_refl (s : rdf_mapping.State) : Marked s s (fun _ => False) [] where
  subjects := rfl
  sources := rfl
  blanks := by simp
  length := rfl
  used := by intro i _; simp

theorem marked_trans {s s1 s2 : rdf_mapping.State} {m1 m2 : Nat → Prop} {f1 f2 : List rdf.BlankNode}
    (first : Marked s s1 m1 f1) (second : Marked s1 s2 m2 f2) : Marked s s2 (fun i => m1 i ∨ m2 i) (f1 ++ f2) where
  subjects := by rw [second.subjects, first.subjects]
  sources := by rw [second.sources, first.sources]
  blanks := by rw [second.blanks, first.blanks, List.append_assoc]
  length := by rw [second.length, first.length]
  used := by
    intro i inside
    have inside1 : i < s1.used.val.length := by rw [first.length]; exact inside
    rw [second.used i inside1, first.used i inside]
    tauto

theorem marked_same {s s' : rdf_mapping.State} {m m' : Nat → Prop} {f : List rdf.BlankNode} (h : Marked s s' m f)
    (same : ∀ i, m i ↔ m' i) : Marked s s' m' f where
  subjects := h.subjects
  sources := h.sources
  blanks := h.blanks
  length := h.length
  used := fun i inside => by rw [h.used i inside, same i]

theorem marked_take (s : rdf_mapping.State) (index : Usize) :
    Marked s { s with used := s.used.set index true } (fun i => i = index.val) [] where
  subjects := rfl
  sources := rfl
  blanks := by simp
  length := by simp [alloc.vec.Vec.set_val_eq]
  used := by
    intro i inside
    simp only [alloc.vec.Vec.set_val_eq]
    by_cases here : i = index.val
    · subst here
      simp [List.getElem?_set_self inside]
    · rw [List.getElem?_set_ne (Ne.symm here)]
      simp [here]

theorem marked_record (s s' : rdf_mapping.State) (node : rdf.BlankNode) (ran : rdf_mapping.record s node = .ok s') :
    Marked s s' (fun _ => False) [node] := by
  rw [rdf_mapping.record, copy_blank_identity] at ran
  simp only [bind_ok, alloc.vec.Vec.push] at ran
  split at ran
  · simp only [bind_ok, Result.ok.injEq] at ran
    subst ran
    exact { subjects := rfl, sources := rfl, blanks := by simp, length := rfl, used := by intro i _; simp }
  · simp at ran

/-- An unused position stays unused while other positions are marked. -/
theorem marked_unused {s s' : rdf_mapping.State} {m : Nat → Prop} {f : List rdf.BlankNode} (h : Marked s s' m f)
    {i : Nat} (unused : s.used.val[i]? = some false) (outside : ¬ m i) : s'.used.val[i]? = some false := by
  have inside : i < s.used.val.length := (List.getElem?_eq_some_iff.mp unused).1
  have inside' : i < s'.used.val.length := by rw [h.length]; exact inside
  cases value : s'.used.val[i]'inside' with
  | false => rw [List.getElem?_eq_getElem inside', value]
  | true =>
    have := (h.used i inside).mp (by rw [List.getElem?_eq_getElem inside', value])
    rw [unused] at this
    simp at this
    exact absurd this outside


/-- All triples about `x` are at the positions `a ..< a + head.length`, which hold
    the patterns `⟨x, p, o⟩` of `head` in order, and the predicates of `head` differ. -/
structure Heads (triples : List rdf.Triple) (used : List Bool) (x : rdf.BlankNode) (a : Nat)
    (head : List (List U8 × Node)) : Prop where
  holds : ∀ (k : Nat) (h : k < head.length), ∃ t, triples[a + k]? = some t ∧ Matches ⟨.blank x, head[k].1, head[k].2⟩ t
  confined : ∀ (i : Nat) (t : rdf.Triple), triples[i]? = some t → used[i]? = some false →
    subjectView t.subject = .blank x → a ≤ i ∧ i < a + head.length
  distinct : (head.map (·.1)).Nodup

theorem heads_key {triples : List rdf.Triple} {used : List Bool} {x : rdf.BlankNode} {a : Nat}
    {head : List (List U8 × Node)} (heads : Heads triples used x a head) {i : Nat} {t : rdf.Triple}
    (at_i : triples[i]? = some t) (unused : used[i]? = some false) (about : subjectView t.subject = .blank x) :
    ∃ (k : Nat) (h : k < head.length), i = a + k ∧ t.predicate.spelling.val = head[k].1 ∧ objectView t.object = head[k].2 := by
  obtain ⟨low, high⟩ := heads.confined i t at_i unused about
  obtain ⟨t', at_k, fits⟩ := heads.holds (i - a) (by omega)
  have same : a + (i - a) = i := by omega
  rw [same, at_i] at at_k
  cases at_k
  exact ⟨i - a, by omega, by omega, fits.2.1, fits.2.2⟩

theorem find_in_total (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool)
    (bucket : alloc.vec.Vec Usize) (node : rdf.BlankNode) (key : Slice U8) :
    ∀ (k : Usize), ∃ r, rdf_mapping.find_in triples used bucket node key k = .ok r := by
  intro k
  induction e : bucket.val.length - k.val generalizing k with
  | zero =>
    have done : ¬ k.val < bucket.val.length := by omega
    exact ⟨none, by rw [rdf_mapping.find_in]; simp [UScalar.lt_equiv, done]⟩
  | succ n ih =>
    have more : k.val < bucket.val.length := by omega
    have lookup : bucket.index_usize k = .ok bucket.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = k.val + 1 := by simpa using nextValue
    obtain ⟨r, run⟩ := ih next (by omega)
    rw [rdf_mapping.find_in]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, fits_correct]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨r, by simp [advance, run]⟩

theorem find_total (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (node : rdf.BlankNode)
    (key : Slice U8) : ∃ r, rdf_mapping.find triples s node key = .ok r := by
  obtain ⟨h, hashRun⟩ := hash_blank_ok node
  obtain ⟨bucket, bucketRun, -⟩ := bucket_of_spec h (alloc.vec.Vec.len s.subjects)
  rw [rdf_mapping.find]
  simp only [hashRun, bucketRun, bind_ok]
  by_cases inside : bucket.val < s.subjects.val.length
  · have lookup : s.subjects.index_usize bucket = .ok s.subjects.val[bucket.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨r, run⟩ := find_in_total triples s.used s.subjects.val[bucket.val] node key 0#usize
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, run]⟩
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]⟩

/-- A lookup finds the head triple with its predicate when it is unused. -/
theorem find_at (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (x : rdf.BlankNode) (key : Slice U8)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {a : Nat} {head : List (List U8 × Node)} (heads : Heads triples.val s.used.val x a head) (k : Nat) (h : k < head.length)
    (named : head[k].1 = key.val) (unused : s.used.val[a + k]? = some false) :
    ∃ found : Usize, rdf_mapping.find triples s x key = .ok (some found) ∧ found.val = a + k := by
  obtain ⟨t, at_t, fits⟩ := heads.holds k h
  obtain ⟨r, run⟩ := find_total triples s x key
  cases r with
  | none =>
    exact absurd (find_none triples s x key complete run (a + k) t ⟨at_t, unused⟩ fits.1) (by
      rw [fits.2.1, named]; simp)
  | some found =>
    obtain ⟨t', unused', about', named'⟩ := find_spec triples s x key found run
    obtain ⟨k', h', position, predicate, -⟩ := heads_key heads unused'.1 unused'.2 about'
    refine ⟨found, run, ?_⟩
    have same : k' = k := by
      have keys : (head.map (·.1))[k']'(by simpa using h') = (head.map (·.1))[k]'(by simpa using h) := by
        simp only [List.getElem_map]
        rw [← predicate, named', named]
      exact (List.Nodup.getElem_inj_iff heads.distinct).mp keys
    rw [position, same]

theorem fits_type_correct (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool) (index : Usize)
    (node : rdf.BlankNode) (key : Slice U8) :
    rdf_mapping.fits_type triples used index node key = .ok (decide (∃ t, Unused triples.val used.val index.val t ∧
      subjectView t.subject = .blank node ∧ t.predicate.spelling.val = rdfType ∧ objectView t.object = .iri key.val)) := by
  rw [rdf_mapping.fits_type]
  by_cases more : index.val < triples.val.length
  · have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, about_correct, same_correct, object_is_correct, lift, array_slice_val]
    have at_t : triples.val[index.val]? = some triples.val[index.val] := List.getElem?_eq_getElem more
    by_cases isUsed : used.val[index.val]? = some false
    · simp only [isUsed, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases here : subjectView triples.val[index.val].subject = .blank node
      · by_cases typed : triples.val[index.val].predicate.spelling.val = rdfType
        · have typed' := typed
          simp only [rdfType] at typed'
          simp only [here, typed', decide_true, ↓reduceIte, Result.ok.injEq]
          congr 1
          apply propext
          constructor
          · intro object; exact ⟨_, ⟨at_t, isUsed⟩, here, typed, object⟩
          · rintro ⟨t, ⟨at_i, -⟩, -, -, object⟩
            rw [at_t] at at_i
            cases at_i
            exact object
        · have typed' := typed
          simp only [rdfType] at typed'
          simp only [here, typed', decide_true, decide_false, ↓reduceIte, Bool.false_eq_true, Result.ok.injEq]
          symm
          simp only [decide_eq_false_iff_not, not_exists, not_and]
          rintro t ⟨at_i, -⟩ - named
          rw [at_t] at at_i
          cases at_i
          exact absurd named typed
      · simp only [here, decide_false, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq]
        symm
        simp only [decide_eq_false_iff_not, not_exists, not_and]
        rintro t ⟨at_i, -⟩ about
        rw [at_t] at at_i
        cases at_i
        exact absurd about here
    · simp only [isUsed, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, Result.ok.injEq]
      symm
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      rintro t ⟨-, used⟩
      exact absurd used isUsed
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, Result.ok.injEq]
    symm
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    rintro t ⟨at_i, -⟩
    have := (List.getElem?_eq_some_iff.mp at_i).1
    omega

theorem find_type_in_total (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool)
    (bucket : alloc.vec.Vec Usize) (node : rdf.BlankNode) (key : Slice U8) :
    ∀ (k : Usize), ∃ r, rdf_mapping.find_type_in triples used bucket node key k = .ok r := by
  intro k
  induction e : bucket.val.length - k.val generalizing k with
  | zero =>
    have done : ¬ k.val < bucket.val.length := by omega
    exact ⟨none, by rw [rdf_mapping.find_type_in]; simp [UScalar.lt_equiv, done]⟩
  | succ n ih =>
    have more : k.val < bucket.val.length := by omega
    have lookup : bucket.index_usize k = .ok bucket.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = k.val + 1 := by simpa using nextValue
    obtain ⟨r, run⟩ := ih next (by omega)
    rw [rdf_mapping.find_type_in]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, fits_type_correct]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨r, by simp [advance, run]⟩

theorem find_type_total (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (node : rdf.BlankNode)
    (key : Slice U8) : ∃ r, rdf_mapping.find_type triples s node key = .ok r := by
  obtain ⟨h, hashRun⟩ := hash_blank_ok node
  obtain ⟨bucket, bucketRun, -⟩ := bucket_of_spec h (alloc.vec.Vec.len s.subjects)
  rw [rdf_mapping.find_type]
  simp only [hashRun, bucketRun, bind_ok]
  by_cases inside : bucket.val < s.subjects.val.length
  · have lookup : s.subjects.index_usize bucket = .ok s.subjects.val[bucket.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨r, run⟩ := find_type_in_total triples s.used s.subjects.val[bucket.val] node key 0#usize
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, run]⟩
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]⟩

theorem find_type_in_none (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool)
    (bucket : alloc.vec.Vec Usize) (node : rdf.BlankNode) (key : Slice U8) (k : Usize)
    (ran : rdf_mapping.find_type_in triples used bucket node key k = .ok none) :
    ∀ (j : Nat) (pos : Usize), k.val ≤ j → bucket.val[j]? = some pos →
      ¬ ∃ t, Unused triples.val used.val pos.val t ∧ subjectView t.subject = .blank node ∧
        t.predicate.spelling.val = rdfType ∧ objectView t.object = .iri key.val := by
  rw [rdf_mapping.find_type_in] at ran
  by_cases more : k.val < bucket.val.length
  · have lookup : bucket.index_usize k = .ok bucket.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = k.val + 1 := by simpa using nextValue
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, fits_type_correct] at ran
    by_cases fit : ∃ t, Unused triples.val used.val bucket.val[k.val].val t ∧ subjectView t.subject = .blank node ∧
        t.predicate.spelling.val = rdfType ∧ objectView t.object = .iri key.val
    · simp [fit] at ran
    · simp only [fit, decide_false, Bool.false_eq_true, ↓reduceIte, advance, bind_ok] at ran
      intro j pos low at_j
      by_cases here : j = k.val
      · subst here
        rw [List.getElem?_eq_getElem more] at at_j
        cases at_j
        exact fit
      · exact find_type_in_none triples used bucket node key next ran j pos (by omega) at_j
  · intro j pos low at_j
    have := (List.getElem?_eq_some_iff.mp at_j).1
    omega
termination_by bucket.val.length - k.val
decreasing_by all_goals (have := nextValue; simp at this; omega)

theorem find_type_none (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (node : rdf.BlankNode)
    (key : Slice U8) (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects)
      triples.val.length)
    (ran : rdf_mapping.find_type triples s node key = .ok none) :
    ∀ (i : Nat) (t : rdf.Triple), Unused triples.val s.used.val i t → subjectView t.subject = .blank node →
      t.predicate.spelling.val = rdfType → objectView t.object ≠ .iri key.val := by
  intro i t unused about typed object
  rw [rdf_mapping.find_type] at ran
  obtain ⟨h, hashRun, ran⟩ := bind_eq_ok ran
  obtain ⟨bucket, bucketRun, ran⟩ := bind_eq_ok ran
  have blank : t.subject = .Blank node := by
    cases subject : t.subject with
    | Iri _ => rw [subject] at about; simp [subjectView] at about
    | Blank b => rw [subject] at about; simp [subjectView] at about; rw [about]
  obtain ⟨b, at_b, k, member, kIs⟩ := complete i t node bucket (List.getElem?_eq_some_iff.mp unused.1).1 unused.1 blank
    ⟨h, hashRun, bucketRun⟩
  have inside : bucket.val < s.subjects.val.length := (List.getElem?_eq_some_iff.mp at_b).1
  have lookup : s.subjects.index_usize bucket = .ok s.subjects.val[bucket.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
    lookup, bind_ok] at ran
  rw [List.getElem?_eq_getElem inside] at at_b
  cases at_b
  obtain ⟨j, at_j⟩ := List.mem_iff_getElem?.mp member
  exact find_type_in_none triples s.used _ node key 0#usize ran j k (by simp) at_j
    ⟨t, by rw [kIs]; exact unused, about, typed, object⟩

/-- A type lookup finds the head typing triple when it is unused. -/
theorem find_type_at (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (x : rdf.BlankNode)
    (key : Slice U8)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {a : Nat} {head : List (List U8 × Node)} (heads : Heads triples.val s.used.val x a head) (k : Nat) (h : k < head.length)
    (typed : head[k] = (rdfType, .iri key.val)) (unused : s.used.val[a + k]? = some false) :
    ∃ found : Usize, rdf_mapping.find_type triples s x key = .ok (some found) ∧ found.val = a + k := by
  obtain ⟨t, at_t, fits⟩ := heads.holds k h
  obtain ⟨r, run⟩ := find_type_total triples s x key
  cases r with
  | none =>
    exact absurd (find_type_none triples s x key complete run (a + k) t ⟨at_t, unused⟩ fits.1
      (by rw [fits.2.1, typed])) (by rw [fits.2.2, typed]; simp)
  | some found =>
    obtain ⟨t', unused', about', named', object'⟩ := find_type_spec triples s x key found run
    obtain ⟨k', h', position, predicate, -⟩ := heads_key heads unused'.1 unused'.2 about'
    refine ⟨found, run, ?_⟩
    have same : k' = k := by
      have keys : (head.map (·.1))[k']'(by simpa using h') = (head.map (·.1))[k]'(by simpa using h) := by
        simp only [List.getElem_map]
        rw [← predicate, named', typed]
      exact (List.Nodup.getElem_inj_iff heads.distinct).mp keys
    rw [position, same]

/-- The positions `a ..< a + ps.length` of the graph hold the patterns `ps`. -/
def Holds (triples : List rdf.Triple) (a : Nat) (ps : List Pattern) : Prop :=
  ∀ (j : Nat) (h : j < ps.length), ∃ t, triples[a + j]? = some t ∧ Matches ps[j] t

/-- Every unused triple about one of the nodes `fresh` is at a position `a ..< a + len`. -/
def Owned (triples : List rdf.Triple) (used : List Bool) (a len : Nat) (fresh : List rdf.BlankNode) : Prop :=
  ∀ (i : Nat) (t : rdf.Triple) (y : rdf.BlankNode), triples[i]? = some t → used[i]? = some false →
    subjectView t.subject = .blank y → y ∈ fresh → a ≤ i ∧ i < a + len

/-- The positions `a ..< a + len` are unused. -/
def Pending (used : List Bool) (a len : Nat) : Prop :=
  ∀ (j : Nat), j < len → used[a + j]? = some false

theorem holds_append {triples : List rdf.Triple} {a : Nat} {ps qs : List Pattern} (h : Holds triples a (ps ++ qs)) :
    Holds triples a ps ∧ Holds triples (a + ps.length) qs := by
  constructor
  · intro j hj
    obtain ⟨t, at_t, fits⟩ := h j (by simp; omega)
    exact ⟨t, at_t, by rw [List.getElem_append_left hj] at fits; exact fits⟩
  · intro j hj
    obtain ⟨t, at_t, fits⟩ := h (ps.length + j) (by simp; omega)
    refine ⟨t, by rw [Nat.add_assoc]; exact at_t, ?_⟩
    rw [List.getElem_append_right (by omega)] at fits
    simpa using fits

theorem pending_split {used : List Bool} {a len1 len2 : Nat} (h : Pending used a (len1 + len2)) :
    Pending used a len1 ∧ Pending used (a + len1) len2 :=
  ⟨fun j hj => h j (by omega), fun j hj => by rw [Nat.add_assoc]; exact h (len1 + j) (by omega)⟩

/-- The head patterns of a node `x` at the start of a segment whose other
    patterns are about other nodes give `Heads`. -/
theorem heads_of {triples : List rdf.Triple} {used : List Bool} {x : rdf.BlankNode} {a : Nat}
    {head : List (List U8 × Node)} {rest : List Pattern} {fresh' : List rdf.BlankNode}
    (holds : Holds triples a (head.map (fun e => (⟨.blank x, e.1, e.2⟩ : Pattern)) ++ rest))
    (owned : Owned triples used a (head.length + rest.length) (x :: fresh'))
    (restSubjects : SubjectsIn fresh' rest) (outside : x ∉ fresh') (distinct : (head.map (·.1)).Nodup) :
    Heads triples used x a head where
  holds := by
    intro k hk
    obtain ⟨t, at_t, fits⟩ := holds k (by simp; omega)
    refine ⟨t, at_t, ?_⟩
    rw [List.getElem_append_left (by simpa using hk)] at fits
    simpa using fits
  confined := by
    intro i t at_i unused about
    obtain ⟨low, high⟩ := owned i t x at_i unused about (by simp)
    refine ⟨low, ?_⟩
    by_cases inside : i < a + head.length
    · exact inside
    · exfalso
      have hj : i - a < (head.map (fun e => (⟨.blank x, e.1, e.2⟩ : Pattern)) ++ rest).length := by simp; omega
      obtain ⟨t', at_t', fits⟩ := holds (i - a) hj
      have same : a + (i - a) = i := by omega
      rw [same, at_i] at at_t'
      cases at_t'
      rw [List.getElem_append_right (by simp; omega)] at fits
      obtain ⟨y, member, subject⟩ := restSubjects _ (List.getElem_mem _)
      have view := fits.1.trans subject
      rw [about] at view
      cases view
      exact outside member
  distinct := distinct


theorem position_usize {triples : alloc.vec.Vec rdf.Triple} {i : Nat} {t : rdf.Triple} (at_i : triples.val[i]? = some t) :
    i < 2 ^ UScalarTy.Usize.numBits := by
  have inside := (List.getElem?_eq_some_iff.mp at_i).1
  have bound : triples.val.length ≤ Usize.max := triples.property
  have positive : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.pow_pos (by decide)
  have : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
    simp only [Usize.max, Usize.numBits]
    omega
  omega

/-- A lookup of the head predicate at offset `k` finds position `a + k`, for every
    spelling of the predicate. -/
theorem find_hit (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (x : rdf.BlankNode)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {a : Nat} {head : List (List U8 × Node)} (heads : Heads triples.val s.used.val x a head) (k : Nat) (h : k < head.length)
    (P : List U8) (predicate : head[k].1 = P) (unused : s.used.val[a + k]? = some false) :
    ∃ found : Usize, found.val = a + k ∧
      ∀ key : Slice U8, key.val = P → rdf_mapping.find triples s x key = .ok (some found) := by
  obtain ⟨t, at_t, -⟩ := heads.holds k h
  refine ⟨UScalar.ofNatCore (a + k) (position_usize at_t), UScalar.ofNatCore_val_eq _, fun key named => ?_⟩
  obtain ⟨found, run, value⟩ := find_at triples s x key complete heads k h (by rw [predicate, named]) unused
  have same : found = UScalar.ofNatCore (a + k) (position_usize at_t) :=
    UScalar.eq_of_val_eq (by rw [value, UScalar.ofNatCore_val_eq])
  rw [run, same]

/-- A type lookup of the head type at offset `k` finds position `a + k`, for every
    spelling of the type. -/
theorem find_type_hit (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (x : rdf.BlankNode)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {a : Nat} {head : List (List U8 × Node)} (heads : Heads triples.val s.used.val x a head) (k : Nat) (h : k < head.length)
    (T : List U8) (typed : head[k] = (rdfType, .iri T)) (unused : s.used.val[a + k]? = some false) :
    ∃ found : Usize, found.val = a + k ∧
      ∀ key : Slice U8, key.val = T → rdf_mapping.find_type triples s x key = .ok (some found) := by
  obtain ⟨t, at_t, -⟩ := heads.holds k h
  refine ⟨UScalar.ofNatCore (a + k) (position_usize at_t), UScalar.ofNatCore_val_eq _, fun key named => ?_⟩
  obtain ⟨found, run, value⟩ := find_type_at triples s x key complete heads k h (by rw [typed, named]) unused
  have same : found = UScalar.ofNatCore (a + k) (position_usize at_t) :=
    UScalar.eq_of_val_eq (by rw [value, UScalar.ofNatCore_val_eq])
  rw [run, same]

theorem record_ok (s : rdf_mapping.State) (node : rdf.BlankNode) (room : s.blanks.val.length < Usize.max) :
    ∃ s', rdf_mapping.record s node = .ok s' ∧ Marked s s' (fun _ => False) [node] := by
  obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec s.blanks node room)
  have run : rdf_mapping.record s node = .ok { s with blanks := pushed } := by
    rw [rdf_mapping.record, copy_blank_identity]
    simp [push]
  exact ⟨_, run, marked_record s _ node run⟩

/-- The triples about the nodes of the parts lie after the head of a node. -/
theorem owned_after_head {triples : List rdf.Triple} {used : List Bool} {b : rdf.BlankNode} {a : Nat}
    {head : List (List U8 × Node)} {rest : List Pattern} {f' : List rdf.BlankNode}
    (holds : Holds triples a (head.map (fun e => (⟨.blank b, e.1, e.2⟩ : Pattern)) ++ rest))
    (owned : Owned triples used a (head.length + rest.length) (b :: f')) (outside : b ∉ f') :
    Owned triples used (a + head.length) rest.length f' := by
  intro i t y at_i unused about member
  obtain ⟨low, high⟩ := owned i t y at_i unused about (List.mem_cons_of_mem _ member)
  refine ⟨?_, by omega⟩
  by_cases before : i < a + head.length
  · exfalso
    obtain ⟨t', at_t', fits⟩ := holds (i - a) (by simp; omega)
    have same : a + (i - a) = i := by omega
    rw [same, at_i] at at_t'
    cases at_t'
    rw [List.getElem_append_left (by simp; omega)] at fits
    simp only [List.getElem_map] at fits
    have view := fits.1
    rw [about] at view
    cases view
    exact outside member
  · omega

/-- A position unused after marking was unused before. -/
theorem marked_back {s s' : rdf_mapping.State} {m : Nat → Prop} {f : List rdf.BlankNode} (h : Marked s s' m f)
    {i : Nat} (unused : s'.used.val[i]? = some false) : s.used.val[i]? = some false := by
  have inside' : i < s'.used.val.length := (List.getElem?_eq_some_iff.mp unused).1
  have inside : i < s.used.val.length := by rw [← h.length]; exact inside'
  cases value : s.used.val[i]'inside with
  | false => rw [List.getElem?_eq_getElem inside, value]
  | true =>
    have := (h.used i inside).mpr (Or.inl (by rw [List.getElem?_eq_getElem inside, value]))
    rw [unused] at this
    cases this

theorem heads_mono {triples : List rdf.Triple} {used used' : List Bool} {x : rdf.BlankNode} {a : Nat}
    {head : List (List U8 × Node)} (heads : Heads triples used x a head)
    (back : ∀ i : Nat, used'[i]? = some false → used[i]? = some false) : Heads triples used' x a head where
  holds := heads.holds
  confined := fun i t at_i unused about => heads.confined i t at_i (back i unused) about
  distinct := heads.distinct

theorem owned_mono {triples : List rdf.Triple} {used used' : List Bool} {a len : Nat} {fresh : List rdf.BlankNode}
    (owned : Owned triples used a len fresh) (back : ∀ i : Nat, used'[i]? = some false → used[i]? = some false) :
    Owned triples used' a len fresh :=
  fun i t y at_i unused about member => owned i t y at_i (back i unused) about member

/-- Class expressions built from named classes and existential restrictions on
    named object properties that the declarations classify as object properties. -/
inductive Existential (kinds : rdf_mapping.Kinds) : model.ClassExpression → Prop
  | named (c : model.Class) : Existential kinds (.Class c)
  | some (p : model.ObjectProperty) (c : model.ClassExpression) :
      rdf_mapping.property_kind kinds p.iri.spelling = .ok (some .Object) → Existential kinds c →
      Existential kinds (.ObjectSomeValuesFrom (.Property p) c)

theorem vec_eq_of_val {α : Type} {u v : alloc.vec.Vec α} (h : u.val = v.val) : u = v :=
  (alloc.vec.Vec.eq_iff u v).mpr h

theorem existential_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (c : model.ClassExpression) (existential : Existential kinds c) :
    ∀ (s0 s1 : Supply) (n : Node) (ps : List Pattern), TCE c s0 n ps s1 →
    ∀ (fresh : Supply), s0 = fresh ++ s1 → fresh.Nodup →
    ∀ (a : Nat) (s : rdf_mapping.State) (node : rdf.Object) (fuel : Usize), objectView node = n →
      SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length →
      Holds triples.val a ps → Pending s.used.val a ps.length → Owned triples.val s.used.val a ps.length fresh →
      ps.length ≤ fuel.val → s.blanks.val.length + ps.length ≤ Usize.max →
      ∃ s', rdf_mapping.class_expression triples kinds node s fuel = .ok (some (c, s')) ∧
        Marked s s' (fun i => a ≤ i ∧ i < a + ps.length) fresh := by
  induction existential with
  | named c =>
    intro s0 s1 n ps tce fresh split nodup a s node fuel view complete holds pending owned fuelOk room
    cases tce
    have empty : fresh = [] := by simpa using split
    subst empty
    cases node with
    | Iri iri =>
      have spell : iri.spelling = c.iri.spelling := vec_eq_of_val (by simpa [objectView, iriNode] using view)
      refine ⟨s, ?_, marked_same (marked_refl s) (fun i => by simp)⟩
      rw [rdf_mapping.class_expression.eq_def]
      simp [iri_of_identity, spell]
    | Blank _ => simp [objectView, iriNode] at view
    | Literal _ => simp [objectView, iriNode] at view
  | some p c kindp inner ih =>
    intro s0 s1 n ps tce fresh split nodup a s node fuel view complete holds pending owned fuelOk room
    cases tce with
    | some role c' x s' s1' s2 n1 n2 p1 p2 tope tce' =>
      cases tope
      obtain ⟨f2, eq2, sub2⟩ := tce_fresh tce'
      have freshIs : fresh = x :: f2 := by
        rw [eq2] at split
        have h : (x :: f2) ++ s1 = fresh ++ s1 := by simpa using split
        exact (List.append_cancel_right h).symm
      subst freshIs
      have outside : x ∉ f2 := (List.nodup_cons.mp nodup).1
      have nodup2 : f2.Nodup := (List.nodup_cons.mp nodup).2
      cases node with
      | Iri _ => simp [objectView] at view
      | Literal _ => simp [objectView] at view
      | Blank b =>
        have bx : b = x := by simpa [objectView] using view
        subst bx
        have shape : restrictionHead b (iriNode p.iri) ++ ⟨.blank b, owlSomeValuesFrom, n2⟩ :: ([] ++ p2) =
            ([(rdfType, .iri owlRestriction), (owlOnProperty, iriNode p.iri), (owlSomeValuesFrom, n2)] :
              List (List U8 × Node)).map (fun e => (⟨.blank b, e.1, e.2⟩ : Pattern)) ++ p2 := by
          simp [restrictionHead]
        rw [shape] at holds pending owned fuelOk room ⊢
        simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at pending owned fuelOk room ⊢
        have heads := heads_of holds (by simpa using owned) sub2 outside (by simp [rdfType, owlOnProperty,
          owlSomeValuesFrom])
        have owned2 := owned_after_head holds (by simpa using owned) outside
        obtain ⟨holdsHead, holds2⟩ := holds_append holds
        simp only [List.length_map, List.length_cons, List.length_nil] at owned2 holds2
        have positive : fuel > 0#usize := by scalar_tac
        obtain ⟨f0, f0val, typeRun⟩ := find_type_hit triples s b complete heads 0 (by simp) owlRestriction
          (by simp) (pending 0 (by omega))
        have m1 := marked_take s f0
        obtain ⟨s2, recordRun, m2⟩ := record_ok { s with used := s.used.set f0 true } b (by simp; omega)
        obtain ⟨fewer, back, fewerValue⟩ := WP.spec_imp_exists
          (Usize.sub_spec (x := fuel) (y := 1#usize) (by scalar_tac))
        have fewerIs : fewer.val + 1 = fuel.val := by simp at fewerValue; omega
        have m12 := marked_trans m1 m2
        have complete2 : SubjectsComplete triples.val s2.subjects.val (alloc.vec.Vec.len s2.subjects)
            triples.val.length := by rw [m12.subjects]; exact complete
        have unused1 : s2.used.val[a + 1]? = some false :=
          marked_unused m12 (pending 1 (by omega)) (by simp [f0val])
        obtain ⟨f1, f1val, findRun1⟩ := find_hit triples s2 b complete2 (heads_mono heads (fun i => marked_back m12))
          1 (by simp) owlOnProperty (by simp)
          unused1
        obtain ⟨t1, at1, fits1⟩ := heads.holds 1 (by simp)
        simp only [List.getElem_cons_succ, List.getElem_cons_zero] at fits1
        have m3 := marked_take s2 f1
        let s3 : rdf_mapping.State := { s2 with used := s2.used.set f1 true }
        have m123 := marked_trans m12 m3
        have unused2 : s3.used.val[a + 2]? = some false :=
          marked_unused m123 (pending 2 (by omega)) (by simp [f0val, f1val])
        have complete3 : SubjectsComplete triples.val s3.subjects.val (alloc.vec.Vec.len s3.subjects)
            triples.val.length := by rw [m123.subjects]; exact complete
        obtain ⟨f2', f2val, findRun2⟩ := find_hit triples s3 b complete3 (heads_mono heads (fun i => marked_back m123))
          2 (by simp) owlSomeValuesFrom (by simp)
          unused2
        obtain ⟨t2, at2, fits2⟩ := heads.holds 2 (by simp)
        simp only [List.getElem_cons_succ, List.getElem_cons_zero] at fits2
        have m4 := marked_take s3 f2'
        let s4 : rdf_mapping.State := { s3 with used := s3.used.set f2' true }
        have m1234 := marked_trans m123 m4
        have pending4 : Pending s4.used.val (a + 3) p2.length := by
          intro j hj
          have := marked_unused m1234 (pending (3 + j) (by omega)) (by simp [f0val, f1val, f2val]; omega)
          rw [show a + (3 + j) = a + 3 + j by omega] at this
          exact this
        have complete4 : SubjectsComplete triples.val s4.subjects.val (alloc.vec.Vec.len s4.subjects)
            triples.val.length := by rw [m1234.subjects]; exact complete
        have room4 : s4.blanks.val.length + p2.length ≤ Usize.max := by
          rw [m1234.blanks]; simp; omega
        obtain ⟨s5, filler, m5⟩ := ih s' s1 n2 p2 tce' f2 eq2 nodup2 (a + 3) s4 t2.object fewer fits2.2.2 complete4
          (by simpa using holds2) pending4 (owned_mono (by simpa using owned2) (fun i => marked_back m1234)) (by omega)
          room4
        have object1 : t1.object = .Iri ⟨p.iri.spelling⟩ := by
          have view1 := fits1.2.2
          cases object : t1.object with
          | Iri iri =>
            rw [object] at view1
            have : iri.spelling = p.iri.spelling := vec_eq_of_val (by simpa [objectView, iriNode] using view1)
            rw [← this]
          | Blank _ => rw [object] at view1; simp [objectView, iriNode] at view1
          | Literal _ => rw [object] at view1; simp [objectView, iriNode] at view1
        have kindRun : rdf_mapping.node_kind kinds t1.object = .ok (some .Object) := by
          rw [object1, rdf_mapping.node_kind.eq_def]
          exact kindp
        refine ⟨s5, ?_, ?_⟩
        · rw [rdf_mapping.class_expression.eq_def]
          simp only [positive, ↓reduceIte, lift, bind_ok, typeRun, array_slice_val, owlRestriction, take_correct,
            recordRun, back]
          rw [rdf_mapping.restriction]
          simp only [lift, bind_ok, findRun1, array_slice_val, owlOnProperty, take_correct,
            alloc.vec.Vec.index_slice_index, main_lookup triples f1 t1 (by rw [f1val]; exact at1), kindRun]
          rw [object1, rdf_mapping.property_expression.eq_def]
          simp only [iri_of_identity, bind_ok]
          have step : rdf_mapping.object_restriction triples kinds b (.Property ⟨⟨p.iri.spelling⟩⟩) s3 fewer =
              .ok (some (.ObjectSomeValuesFrom (.Property p) c, s5)) := by
            rw [rdf_mapping.object_restriction]
            simp only [lift, bind_ok, findRun2, array_slice_val, owlSomeValuesFrom, take_correct,
              alloc.vec.Vec.index_slice_index, main_lookup triples f2' t2 (by rw [f2val]; exact at2)]
            have filler' : rdf_mapping.class_expression triples kinds t2.object
                { used := s3.used.set f2' true, blanks := s3.blanks, subjects := s3.subjects, sources := s3.sources }
                fewer = .ok (some (c, s5)) := filler
            rw [filler']
            simp only [bind_ok]
            rfl
          exact step
        · have whole := marked_trans m1234 m5
          refine marked_same (by simpa using whole) ?_
          intro i
          simp only [f0val, f1val, f2val, false_or, or_false]
          omega


/-! ### Segments of axioms -/

/-- Every blank subject of the patterns is one of the nodes. -/
def BlankSubjects (nodes : List rdf.BlankNode) (ps : List Pattern) : Prop :=
  ∀ p ∈ ps, ∀ y, p.subject = .blank y → y ∈ nodes

theorem blank_subjects_of {nodes : List rdf.BlankNode} {ps : List Pattern} (h : SubjectsIn nodes ps) :
    BlankSubjects nodes ps := by
  intro p member y subject
  obtain ⟨z, inside, about⟩ := h p member
  rw [about] at subject
  cases subject
  exact inside

/-- Ownership of a segment splits between two parts with disjoint nodes. -/
theorem owned_split {triples : List rdf.Triple} {used : List Bool} {a : Nat} {ps qs : List Pattern}
    {f1 f2 : List rdf.BlankNode} (holds : Holds triples a (ps ++ qs))
    (owned : Owned triples used a (ps.length + qs.length) (f1 ++ f2)) (nodup : (f1 ++ f2).Nodup)
    (left : BlankSubjects f1 ps) (right : BlankSubjects f2 qs) :
    Owned triples used a ps.length f1 ∧ Owned triples used (a + ps.length) qs.length f2 := by
  have apart := (List.nodup_append.mp nodup).2.2
  constructor
  · intro i t y at_i unused about member
    obtain ⟨low, high⟩ := owned i t y at_i unused about (List.mem_append_left _ member)
    refine ⟨low, ?_⟩
    apply Classical.byContradiction
    intro beyond
    obtain ⟨t', at_t', fits⟩ := holds (i - a) (by simp; omega)
    rw [show a + (i - a) = i by omega, at_i] at at_t'
    cases at_t'
    rw [List.getElem_append_right (by omega)] at fits
    have inside := right _ (List.getElem_mem _) y (fits.1.symm.trans about)
    exact apart y member y inside rfl
  · intro i t y at_i unused about member
    obtain ⟨low, high⟩ := owned i t y at_i unused about (List.mem_append_right _ member)
    refine ⟨?_, by omega⟩
    apply Classical.byContradiction
    intro before
    obtain ⟨t', at_t', fits⟩ := holds (i - a) (by simp; omega)
    rw [show a + (i - a) = i by omega, at_i] at at_t'
    cases at_t'
    rw [List.getElem_append_left (by omega)] at fits
    have inside := left _ (List.getElem_mem _) y (fits.1.symm.trans about)
    exact apart y inside y member rfl

/-- Once the first position of a segment is used, the rest of it owns the nodes. -/
theorem owned_after_take {triples : List rdf.Triple} {used : alloc.vec.Vec Bool} {a : Usize} {len : Nat}
    {fresh : List rdf.BlankNode} (owned : Owned triples used.val a.val (1 + len) fresh) :
    Owned triples (used.set a true).val (a.val + 1) len fresh := by
  intro i t y at_i unused about member
  rw [alloc.vec.Vec.set_val_eq] at unused
  have notHere : i ≠ a.val := by
    intro here
    rw [here] at unused
    have inside : a.val < used.val.length := by
      have := (List.getElem?_eq_some_iff.mp unused).1
      simpa using this
    rw [List.getElem?_set_self inside] at unused
    cases unused
  rw [List.getElem?_set_ne (Ne.symm notHere)] at unused
  obtain ⟨low, high⟩ := owned i t y at_i unused about member
  omega

/-- At most as many fresh nodes as patterns in an existential class expression. -/
theorem existential_fresh_length {kinds : rdf_mapping.Kinds} {c : model.ClassExpression}
    (existential : Existential kinds c) :
    ∀ {s0 s1 : Supply} {n : Node} {ps : List Pattern}, TCE c s0 n ps s1 →
      ∀ {fresh : Supply}, s0 = fresh ++ s1 → fresh.length ≤ ps.length := by
  induction existential with
  | named c =>
    intro s0 s1 n ps tce fresh split
    cases tce
    have empty : fresh = [] := by simpa using split
    simp [empty]
  | some p c kindp inner ih =>
    intro s0 s1 n ps tce fresh split
    cases tce with
    | some role c' x s' s1' s2 n1 n2 p1 p2 tope tce' =>
      cases tope
      obtain ⟨f2, eq2, -⟩ := tce_fresh tce'
      have freshIs : fresh = x :: f2 := by
        rw [eq2] at split
        have h : (x :: f2) ++ s1 = fresh ++ s1 := by simpa using split
        exact (List.append_cancel_right h).symm
      subst freshIs
      have := ih tce' eq2
      simp [restrictionHead]
      omega

/-! ### Reading the axioms of the fragment -/

theorem sub_class_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (c1 c2 : model.ClassExpression) (e1 : Existential kinds c1) (e2 : Existential kinds c2)
    (s0 s2 : Supply) (ps : List Pattern) (tax : TAxiom (.SubClassOf c1 c2) s0 ps s2)
    (fresh : Supply) (split : s0 = fresh ++ s2) (nodup : fresh.Nodup)
    (a : Usize) (s : rdf_mapping.State) (fuel : Usize)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    (holds : Holds triples.val a.val ps) (pending : Pending s.used.val a.val ps.length)
    (owned : Owned triples.val s.used.val a.val ps.length fresh)
    (fuelOk : ps.length ≤ fuel.val) (room : s.blanks.val.length + ps.length ≤ Usize.max) :
    ∃ s', rdf_mapping.read_axiom triples kinds a s fuel = .ok (.Found (.SubClassOf c1 c2) s') ∧
      Marked s s' (fun i => a.val ≤ i ∧ i < a.val + ps.length) fresh := by
  cases tax with
  | subClassOf _ _ _ s1 _ n1 n2 p1 p2 tce1 tce2 =>
    obtain ⟨f1, eq1, sub1⟩ := tce_fresh tce1
    obtain ⟨f2, eq2, sub2⟩ := tce_fresh tce2
    have freshIs : fresh = f1 ++ f2 := by
      rw [eq1, eq2] at split
      have h : (f1 ++ f2) ++ s2 = fresh ++ s2 := by simpa using split
      exact (List.append_cancel_right h).symm
    subst freshIs
    have nodup1 : f1.Nodup := (List.nodup_append.mp nodup).1
    have nodup2 : f2.Nodup := (List.nodup_append.mp nodup).2.1
    have len1 := existential_fresh_length e1 tce1 eq1
    simp only [List.length_cons, List.length_append] at pending owned fuelOk room ⊢
    obtain ⟨t, at_t, fits⟩ := holds 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at at_t fits
    have parts := holds_append (ps := [⟨n1, rdfsSubClassOf, n2⟩]) (qs := p1 ++ p2) holds
    have holdsRest : Holds triples.val (a.val + 1) (p1 ++ p2) := by simpa using parts.2
    obtain ⟨holds1, holds2⟩ := holds_append holdsRest
    -- the main triple is used first
    have m0 := marked_take s a
    let s1' : rdf_mapping.State := { s with used := s.used.set a true }
    have complete1 : SubjectsComplete triples.val s1'.subjects.val (alloc.vec.Vec.len s1'.subjects)
        triples.val.length := complete
    have owned' : Owned triples.val s1'.used.val (a.val + 1) (p1.length + p2.length) (f1 ++ f2) :=
      owned_after_take (by rw [Nat.add_comm 1]; simpa [Nat.add_assoc] using owned)
    obtain ⟨owned1, owned2⟩ := owned_split holdsRest owned' nodup (blank_subjects_of sub1) (blank_subjects_of sub2)
    have pending1 : Pending s1'.used.val (a.val + 1) p1.length := by
      intro j hj
      have := marked_unused m0 (pending (1 + j) (by omega)) (by intro h; omega)
      rwa [show a.val + (1 + j) = a.val + 1 + j by omega] at this
    obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
    obtain ⟨s2', run1, m1⟩ := existential_complete triples kinds c1 e1 _ _ n1 p1 tce1 f1 eq1 nodup1 (a.val + 1) s1'
      node fuel (nodeView.trans fits.1) complete1 holds1 pending1 owned1 (by omega)
      (by show s.blanks.val.length + p1.length ≤ Usize.max; omega)
    have m01 := marked_trans m0 m1
    have complete2 : SubjectsComplete triples.val s2'.subjects.val (alloc.vec.Vec.len s2'.subjects)
        triples.val.length := by rw [m01.subjects]; exact complete
    have pending2 : Pending s2'.used.val (a.val + 1 + p1.length) p2.length := by
      intro j hj
      have := marked_unused m01 (pending (1 + p1.length + j) (by omega)) (by intro h; omega)
      rwa [show a.val + (1 + p1.length + j) = a.val + 1 + p1.length + j by omega] at this
    have owned2' := owned_mono owned2 (fun i => marked_back m1)
    obtain ⟨s3', run2, m2⟩ := existential_complete triples kinds c2 e2 _ _ n2 p2 tce2 f2 eq2 nodup2
      (a.val + 1 + p1.length) s2' t.object fuel fits.2.2 complete2 holds2 pending2 owned2' (by omega)
      (by rw [m01.blanks]; simp; omega)
    refine ⟨s3', ?_, ?_⟩
    · rw [rdf_mapping.read_axiom]
      simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, bind_ok, same_correct,
        array_slice_val]
      have predicate : t.predicate.spelling.val = rdfsSubClassOf := fits.2.1
      have notType : ¬ (t.predicate.spelling.val = rdfType) := by
        rw [predicate]; simp [rdfsSubClassOf, rdfType]
      simp only [rdfType] at notType
      simp only [rdfsSubClassOf] at predicate
      simp only [notType, decide_false, Bool.false_eq_true, ↓reduceIte]
      simp only [predicate, decide_true, ↓reduceIte]
      have run1' : rdf_mapping.class_expression triples kinds node
          { used := s.used.set a true, blanks := s.blanks, subjects := s.subjects, sources := s.sources } fuel =
          .ok (some (c1, s2')) := run1
      have pairRun : rdf_mapping.class_pair triples kinds a s fuel = .ok (some (c1, c2, s3')) := by
        rw [rdf_mapping.class_pair]
        simp only [take_correct, bind_ok, alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, nodeRun]
        rw [run1']
        simp only [bind_ok]
        change (Std.bind (rdf_mapping.class_expression triples kinds t.object s2' fuel) _) = _
        rw [run2, bind_ok]
        rfl
      rw [rdf_mapping.sub_class, pairRun, bind_ok]
      rfl
    · have whole := marked_trans m01 m2
      refine marked_same (by simpa using whole) ?_
      intro i
      omega
  | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct

theorem iri_ext {i j : model.Iri} (h : i.spelling.val = j.spelling.val) : i = j := by
  cases i; cases j
  simp only [model.Iri.mk.injEq]
  exact vec_eq_of_val h

theorem pattern_of_matches {p : Pattern} {t : rdf.Triple} (h : Matches p t) :
    p = ⟨subjectView t.subject, t.predicate.spelling.val, objectView t.object⟩ := by
  obtain ⟨s, pr, o⟩ := h
  cases p
  simp only at s pr o
  rw [s, pr, o]

theorem declaration_pattern_injective {e e' : model.Entity} (h : declarationPattern e = declarationPattern e') :
    e = e' := by
  cases e <;> cases e' <;>
    simp [declarationPattern, iriNode, owlClass, rdfsDatatype, owlObjectProperty, owlDatatypeProperty,
      owlAnnotationProperty, owlNamedIndividual] at h ⊢ <;>
    first
    | (rename_i x y; cases x; cases y; simp only [model.Class.mk.injEq, model.Datatype.mk.injEq,
        model.ObjectProperty.mk.injEq, model.DataProperty.mk.injEq, model.AnnotationProperty.mk.injEq,
        model.NamedIndividual.mk.injEq]; exact iri_ext h)

theorem declaration_kind_some (e : model.Entity) (object : rdf.Object)
    (h : objectView object = (declarationPattern e).object) :
    ∃ kind, rdf_mapping.declaration_kind object = .ok (some kind) := by
  rw [rdf_mapping.declaration_kind]
  simp only [lift, bind_ok, object_is_correct, array_slice_val]
  cases e <;> simp only [declarationPattern] at h <;>
    simp [h, owlClass, rdfsDatatype, owlObjectProperty, owlDatatypeProperty, owlAnnotationProperty,
      owlNamedIndividual]

/-- The type triple of a declaration goes to the declaration reader. -/
theorem typing_declares (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (index : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[index.val]? = some t)
    (e : model.Entity) (fits : Matches (declarationPattern e) t) :
    rdf_mapping.typing triples kinds index s fuel = rdf_mapping.declaration triples index s := by
  have object := fits.2.2
  have subject := fits.1
  obtain ⟨iri, isIri⟩ : ∃ iri, t.subject = .Iri iri := by
    cases h : t.subject with
    | Iri iri => exact ⟨iri, rfl⟩
    | Blank b =>
      rw [h] at subject
      cases e <;> simp [declarationPattern, iriNode, subjectView] at subject
  have notBlank : rdf_mapping.blank_subject t = .ok false := by
    rw [rdf_mapping.blank_subject]; simp [isIri]
  rw [rdf_mapping.typing]
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples index t at_t, lift, bind_ok, object_is_correct,
    array_slice_val, notBlank]
  cases e <;> simp only [declarationPattern, iriNode] at object <;>
    simp [object, owlClass, rdfsDatatype, owlObjectProperty, owlDatatypeProperty, owlAnnotationProperty,
      owlNamedIndividual, rdf_mapping.declares, rdf_mapping.declaration_kind, object_is_correct, array_slice_val,
      lift]

/-- A declaration triple reads as its declaration. -/
theorem read_axiom_declaration (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (e : model.Entity) (fits : Matches (declarationPattern e) t) :
    rdf_mapping.read_axiom triples kinds a s fuel =
      .ok (.Found (.Declaration e) { s with used := s.used.set a true }) := by
  have typed : t.predicate.spelling.val = rdfType := by
    have := fits.2.1
    cases e <;> exact this
  have object := fits.2.2
  obtain ⟨iri, isIri⟩ : ∃ iri, t.subject = .Iri iri := by
    cases h : t.subject with
    | Iri iri => exact ⟨iri, rfl⟩
    | Blank b =>
      have subject := fits.1
      rw [h] at subject
      cases e <;> simp [declarationPattern, iriNode, subjectView] at subject
  rw [rdf_mapping.read_axiom]
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, bind_ok, same_correct,
    array_slice_val]
  have typed' := typed
  simp only [rdfType] at typed'
  simp only [typed', decide_true, ↓reduceIte]
  rw [typing_declares triples kinds a s fuel t at_t e fits, rdf_mapping.declaration]
  obtain ⟨kind, kindRun⟩ := declaration_kind_some e t.object object
  obtain ⟨e', entityRun, pattern⟩ := entity_of_spec t.object kind kindRun iri.spelling
  have same : e' = e := by
    apply declaration_pattern_injective
    rw [pattern, pattern_of_matches fits, isIri, typed]
    rfl
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, isIri, kindRun, entityRun,
    take_correct, same]

/-! ### The indexes of a graph of the fragment -/

theorem bucket_count_spec (n : Usize) : ∃ c, rdf_mapping.bucket_count n = .ok c ∧ 0 < c.val := by
  obtain ⟨limit, limitRun, limitValue⟩ := WP.spec_imp_exists
    (UScalar.ShiftLeft_IScalar_spec (x := 1#usize) (y := 20#i32) (UScalar.size .Usize) (by decide)
      (by have := System.Platform.numBits_eq; simp [UScalarTy.numBits]; omega) rfl)
  have limitPos : 0 < limit.val := by
    rw [limitValue.1]
    have big : 2 ^ 32 ≤ UScalar.size .Usize := by
      have := System.Platform.numBits_eq
      simp only [UScalar.size, UScalarTy.numBits]
      rcases this with h | h <;> simp [h]
    simp only [Nat.shiftLeft_eq]
    have : ((1#usize : Usize).val * 2 ^ (20#i32 : I32).toNat) = 2 ^ 20 := by decide
    rw [this, Nat.mod_eq_of_lt (by omega)]
    decide
  rw [rdf_mapping.bucket_count, rdf_mapping.BUCKET_LIMIT]
  simp only [limitRun, bind_ok]
  by_cases small : n < limit
  · obtain ⟨c, cRun, cValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := n) (y := 1#usize) (by scalar_tac))
    exact ⟨c, by simp [small, cRun], by simp at cValue; omega⟩
  · exact ⟨limit, by simp [small], limitPos⟩

theorem empty_buckets_spec {T : Type} (count : Usize) :
    ∀ (out : alloc.vec.Vec (alloc.vec.Vec T)), out.val.length ≤ count.val → (∀ b ∈ out.val, b.val = []) →
      ∃ v, rdf_mapping.empty_buckets count out = .ok v ∧ v.val.length = count.val ∧ ∀ b ∈ v.val, b.val = [] := by
  intro out
  induction e : count.val - out.val.length generalizing out with
  | zero =>
    intro small empty
    have done : ¬ out.val.length < count.val := by omega
    exact ⟨out, by rw [rdf_mapping.empty_buckets]; simp [UScalar.lt_equiv, done], by omega, empty⟩
  | succ n ih =>
    intro small empty
    have more : out.val.length < count.val := by omega
    have room : out.val.length < Usize.max := by scalar_tac
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (alloc.vec.Vec.new T) room)
    obtain ⟨v, run, length, all⟩ := ih pushed (by rw [contents]; simp; omega) (by rw [contents]; simp; omega)
      (by
        intro b member
        rw [contents] at member
        rcases List.mem_append.mp member with old | new
        · exact empty b old
        · simp at new; rw [new]; rfl)
    refine ⟨v, ?_, length, all⟩
    rw [rdf_mapping.empty_buckets]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, push, run]

theorem subjects_from_total (triples : alloc.vec.Vec rdf.Triple) :
    ∀ (index : Usize) (buckets : alloc.vec.Vec (alloc.vec.Vec Usize)),
      ∃ r, rdf_mapping.subjects_from triples index buckets = .ok r := by
  intro index
  induction e : triples.val.length - index.val generalizing index with
  | zero =>
    intro buckets
    have done : ¬ index.val < triples.val.length := by omega
    exact ⟨buckets, by rw [rdf_mapping.subjects_from]; simp [UScalar.lt_equiv, done]⟩
  | succ n ih =>
    intro buckets
    have more : index.val < triples.val.length := by omega
    have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    rw [rdf_mapping.subjects_from]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup, bind_ok]
    cases subject : triples.val[index.val].subject with
    | Iri iri =>
      obtain ⟨r, run⟩ := ih next (by omega) buckets
      exact ⟨r, by simp [advance, run]⟩
    | Blank node =>
      obtain ⟨h, hashRun⟩ := hash_blank_ok node
      obtain ⟨bucket, bucketRun, -⟩ := bucket_of_spec h (alloc.vec.Vec.len buckets)
      simp only [hashRun, bucketRun, bind_ok]
      by_cases inside : bucket.val < buckets.val.length
      · have entry : buckets.index_usize bucket = .ok buckets.val[bucket.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
        by_cases fits : buckets.val[bucket.val].val.length < Usize.max
        · obtain ⟨pushed, push, -⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec buckets.val[bucket.val] index fits)
          obtain ⟨r, run⟩ := ih next (by omega) (buckets.set bucket pushed)
          exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, inside, entry, fits,
            alloc.vec.Vec.index_mut_usize, push, advance, run]⟩
        · obtain ⟨r, run⟩ := ih next (by omega) buckets
          exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, inside, entry, fits, advance,
            run]⟩
      · obtain ⟨r, run⟩ := ih next (by omega) buckets
        exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, advance, run]⟩

/-- Without `owl:annotatedSource` triples the source index stays as it is. -/
theorem sources_from_none (triples : alloc.vec.Vec rdf.Triple)
    (noSource : ∀ (i : Nat) (t : rdf.Triple), triples.val[i]? = some t →
      t.predicate.spelling.val ≠ owlAnnotatedSource) :
    ∀ (index : Usize) (buckets : alloc.vec.Vec (alloc.vec.Vec Usize)),
      rdf_mapping.sources_from triples index buckets = .ok buckets := by
  intro index
  induction e : triples.val.length - index.val generalizing index with
  | zero =>
    intro buckets
    have done : ¬ index.val < triples.val.length := by omega
    rw [rdf_mapping.sources_from]; simp [UScalar.lt_equiv, done]
  | succ n ih =>
    intro buckets
    have more : index.val < triples.val.length := by omega
    have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have notSource : rdf_mapping.is_source triples.val[index.val] = .ok false := by
      have other := noSource index.val _ (List.getElem?_eq_getElem more)
      rw [rdf_mapping.is_source]
      cases triples.val[index.val].subject with
      | Iri _ => simp
      | Blank _ =>
        simp only [lift, bind_ok, same_correct, array_slice_val]
        simp only [owlAnnotatedSource] at other
        simp [other]
    rw [rdf_mapping.sources_from]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup, bind_ok, notSource, Bool.false_eq_true, advance]
    exact ih next (by omega) buckets

theorem hash_subject_ok (subject : rdf.Subject) : ∃ h, rdf_mapping.hash_subject subject = .ok h := by
  cases subject with
  | Iri iri =>
    obtain ⟨h, run⟩ := hash_from_ok iri.spelling 0#usize 7#usize
    exact ⟨h, by simp [rdf_mapping.hash_subject, rdf_mapping.hash_iri, run]⟩
  | Blank node =>
    obtain ⟨h, run⟩ := hash_blank_ok node
    exact ⟨h, by simp [rdf_mapping.hash_subject, run]⟩

/-- With an empty source index no reification is found. -/
theorem reifier_none (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (main : rdf.Triple)
    (kind : Slice U8) (empty : ∀ b ∈ s.sources.val, b.val = []) :
    rdf_mapping.reifier triples s main kind = .ok none := by
  obtain ⟨h, hashRun⟩ := hash_subject_ok main.subject
  obtain ⟨bucket, bucketRun, -⟩ := bucket_of_spec h (alloc.vec.Vec.len s.sources)
  rw [rdf_mapping.reifier]
  simp only [hashRun, bucketRun, bind_ok]
  by_cases inside : bucket.val < s.sources.val.length
  · have lookup : s.sources.index_usize bucket = .ok s.sources.val[bucket.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have nothing := empty _ (List.getElem_mem inside)
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup, bind_ok]
    rw [rdf_mapping.reifier_in]
    simp [nothing]
  · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]

/-- An axiom with one main triple and no reification reads without annotations. -/
theorem annotate_plain (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (index : Usize)
    (ax : model.Axiom) (s : rdf_mapping.State) (fuel : Usize) (shape : rdf_mapping.main_triples ax = .ok 1#u8)
    (inside : index.val < triples.val.length) (empty : ∀ b ∈ s.sources.val, b.val = []) :
    rdf_mapping.annotate triples kinds index ax s fuel = .ok (some (⟨alloc.vec.Vec.new _, ax⟩, s)) := by
  have lookup : triples.index_usize index = .ok triples.val[index.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
  have reifiedRun : ∀ kind : Slice U8, rdf_mapping.reified triples kinds index kind s fuel =
      .ok (some (alloc.vec.Vec.new _, s)) := by
    intro kind
    rw [rdf_mapping.reified]
    simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok, reifier_none triples s _ _ empty]
  rw [rdf_mapping.annotate]
  have zero : ¬ ((1#u8 : U8) = 0#u8) := by decide
  simp only [shape, bind_ok]
  rw [if_neg zero]
  simp only [↓reduceIte, lift, bind_ok, reifiedRun]
  rfl

/-! ### The header and the loop over the axioms -/

/-- The first triple, typing an IRI as `owl:Ontology` and unused, is the header. -/
theorem find_header_at (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool) (index : Usize)
    (t : rdf.Triple) (at_t : triples.val[index.val]? = some t) (unused : used.val[index.val]? = some false)
    (typed : t.predicate.spelling.val = rdfType) (onto : objectView t.object = .iri owlOntology)
    (iri : rdf.RdfIri) (subject : t.subject = .Iri iri) :
    rdf_mapping.find_header triples used index = .ok (some index) := by
  have inside : index.val < triples.val.length := (List.getElem?_eq_some_iff.mp at_t).1
  rw [rdf_mapping.find_header]
  simp only [owlOntology] at onto
  simp only [rdfType] at typed
  simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, is_used_correct, unused,
    main_lookup triples index t at_t, lift, same_correct, array_slice_val, typed, object_is_correct, onto, subject]

/-- Without a header triple from `index` on, no header is found. -/
theorem find_header_none (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool) :
    ∀ (index : Usize), (∀ (i : Nat) (t : rdf.Triple), index.val ≤ i → triples.val[i]? = some t →
      t.predicate.spelling.val = rdfType → objectView t.object = .iri owlOntology → ∀ iri, t.subject ≠ .Iri iri) →
      rdf_mapping.find_header triples used index = .ok none := by
  intro index
  induction e : triples.val.length - index.val generalizing index with
  | zero =>
    intro _
    have done : ¬ index.val < triples.val.length := by omega
    rw [rdf_mapping.find_header]; simp [UScalar.lt_equiv, done]
  | succ n ih =>
    intro none
    have more : index.val < triples.val.length := by omega
    have at_t : triples.val[index.val]? = some triples.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have rest := ih next (by omega) (fun i t low => none i t (by omega))
    rw [rdf_mapping.find_header]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok,
      alloc.vec.Vec.index_slice_index, main_lookup triples index _ at_t, lift, same_correct, array_slice_val,
      object_is_correct, advance, rest]
    have here := none index.val _ (le_refl _) at_t
    simp only [rdfType, owlOntology] at here
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    rename_i typed onto
    cases subject : triples.val[index.val].subject with
    | Iri iri => exact absurd subject (here (by simpa using typed) (by simpa using onto) iri)
    | Blank _ => simp [subject, advance, rest]

/-- The header reader skips every triple that is not about the ontology IRI. -/
theorem header_parts_skip (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8) (version : Option model.Iri) (imports : alloc.vec.Vec model.Iri)
    (annotations : alloc.vec.Vec model.Annotation) (s : rdf_mapping.State) :
    ∀ (index : Usize), (∀ (i : Nat) (t : rdf.Triple), index.val ≤ i → triples.val[i]? = some t →
      s.used.val[i]? = some false → subjectView t.subject ≠ .iri ontology.val) →
      rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
        .ok (some (version, imports, annotations, s)) := by
  intro index
  induction e : triples.val.length - index.val generalizing index with
  | zero =>
    intro _
    have done : ¬ index.val < triples.val.length := by omega
    rw [rdf_mapping.header_parts]; simp [UScalar.lt_equiv, done]
  | succ n ih =>
    intro apart
    have more : index.val < triples.val.length := by omega
    have at_t : triples.val[index.val]? = some triples.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have rest := ih next (by omega) (fun i t low => apart i t (by omega))
    rw [rdf_mapping.header_parts]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok, advance, rest]
    by_cases isUsed : s.used.val[index.val]? = some false
    · have notAbout : rdf_mapping.about_iri triples.val[index.val] ontology = .ok false := by
        have other := apart index.val _ (le_refl _) at_t isUsed
        rw [rdf_mapping.about_iri]
        cases subject : triples.val[index.val].subject with
        | Iri iri =>
          rw [subject] at other
          simp only [same_vec_correct]
          have : iri.spelling ≠ ontology := fun h => other (by simp [subjectView, h])
          simp [this]
        | Blank _ => simp
      simp [isUsed, main_lookup triples index _ at_t, notAbout, advance, rest]
    · simp [isUsed]

/-- `all_read` holds once every triple from `index` on is used. -/
theorem all_read_used (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool) :
    ∀ (index : Usize), (∀ (i : Nat), index.val ≤ i → i < triples.val.length → used.val[i]? = some true) →
      rdf_mapping.all_read triples used index = .ok true := by
  intro index
  induction e : triples.val.length - index.val generalizing index with
  | zero =>
    intro _
    have done : ¬ index.val < triples.val.length := by omega
    rw [rdf_mapping.all_read]; simp [UScalar.lt_equiv, done]
  | succ n ih =>
    intro all
    have more : index.val < triples.val.length := by omega
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have rest := ih next (by omega) (fun i low high => all i (by omega) high)
    rw [rdf_mapping.all_read]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, is_used_correct, all index.val (le_refl _) more, advance,
      rest]

/-- The axiom loop passes over used triples. -/
theorem axioms_from_skip (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (s : rdf_mapping.State)
    (out : alloc.vec.Vec model.AnnotatedAxiom) (j : Usize) (bound : j.val ≤ triples.val.length) :
    ∀ (index : Usize), index.val ≤ j.val → (∀ (i : Nat), index.val ≤ i → i < j.val → s.used.val[i]? ≠ some false) →
      rdf_mapping.axioms_from triples kinds index s out = rdf_mapping.axioms_from triples kinds j s out := by
  intro index
  induction e : j.val - index.val generalizing index with
  | zero =>
    intro low _
    have same : index = j := UScalar.eq_of_val_eq (by omega)
    rw [same]
  | succ n ih =>
    intro low used
    have more : index.val < triples.val.length := by omega
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have rest := ih next (by omega) (by omega) (fun i low' high => used i (by omega) high)
    have isUsed := used index.val (le_refl _) (by omega)
    rw [rdf_mapping.axioms_from]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, is_used_correct, isUsed, advance, rest]

theorem axioms_from_end (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (s : rdf_mapping.State)
    (out : alloc.vec.Vec model.AnnotatedAxiom) (index : Usize) (done : triples.val.length ≤ index.val) :
    rdf_mapping.axioms_from triples kinds index s out = .ok (some (out, s)) := by
  have stop : ¬ index.val < triples.val.length := by omega
  rw [rdf_mapping.axioms_from]; simp [UScalar.lt_equiv, stop]

/-! ### Reading the axioms back -/

/-- The axioms that a classification of the properties reads back: declarations,
    and subclass axioms between existential class expressions. -/
inductive Readable (kinds : rdf_mapping.Kinds) : model.Axiom → Prop
  | declaration (e : model.Entity) : Readable kinds (.Declaration e)
  | subClassOf (c1 c2 : model.ClassExpression) : Existential kinds c1 → Existential kinds c2 →
      Readable kinds (.SubClassOf c1 c2)

theorem existential_node {kinds : rdf_mapping.Kinds} {c : model.ClassExpression} (existential : Existential kinds c)
    {s0 s1 : Supply} {n : Node} {ps : List Pattern} (tce : TCE c s0 n ps s1) {fresh : Supply}
    (split : s0 = fresh ++ s1) : ∀ y, n = .blank y → y ∈ fresh := by
  cases existential with
  | named c =>
    cases tce
    intro y h
    simp [iriNode] at h
  | some p c kindp inner =>
    cases tce with
    | some role c' x s' s1' s2 n1 n2 p1 p2 tope tce' =>
      intro y h
      have same : y = x := by cases h; rfl
      subst same
      cases tope
      obtain ⟨f2, eq2, -⟩ := tce_fresh tce'
      have freshIs : fresh = y :: f2 := by
        rw [eq2] at split
        have h : (y :: f2) ++ s1 = fresh ++ s1 := by simpa using split
        exact (List.append_cancel_right h).symm
      simp [freshIs]

theorem readable_fresh {kinds : rdf_mapping.Kinds} {ax : model.Axiom} (readable : Readable kinds ax)
    {s0 s1 : Supply} {p : List Pattern} (tax : TAxiom ax s0 p s1) :
    ∃ f, s0 = f ++ s1 ∧ BlankSubjects f p ∧ f.length ≤ p.length ∧ 0 < p.length := by
  cases readable with
  | declaration e =>
    cases tax with
    | declaration =>
      refine ⟨[], by simp, ?_, by simp, by simp⟩
      intro q member y h
      simp only [List.mem_singleton] at member
      subst member
      cases e <;> simp [declarationPattern, iriNode] at h
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | subClassOf c1 c2 e1 e2 =>
    cases tax with
    | subClassOf _ _ _ s1' _ n1 n2 p1 p2 tce1 tce2 =>
      obtain ⟨f1, eq1, sub1⟩ := tce_fresh tce1
      obtain ⟨f2, eq2, sub2⟩ := tce_fresh tce2
      refine ⟨f1 ++ f2, by rw [eq1, eq2, List.append_assoc], ?_, ?_, by simp⟩
      · intro q member y h
        simp only [List.mem_cons, List.mem_append] at member
        rcases member with rfl | inner | inner
        · exact List.mem_append_left _ (existential_node e1 tce1 eq1 y h)
        · exact List.mem_append_left _ (blank_subjects_of sub1 q inner y h)
        · exact List.mem_append_right _ (blank_subjects_of sub2 q inner y h)
      · have l1 := existential_fresh_length e1 tce1 eq1
        have l2 := existential_fresh_length e2 tce2 eq2
        simp
        omega
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct

theorem plain_axiom {ax : model.AnnotatedAxiom} {s0 s1 : Supply} {p : List Pattern}
    (h : TAnnotatedAxiom ax s0 p s1) (plain : ax.annotations.val = []) : TAxiom ax.axiom s0 p s1 := by
  cases h with
  | plain _ _ _ _ tax => exact tax
  | reified _ _ _ _ _ nonempty => exact absurd plain nonempty
  | blank _ _ _ _ _ _ _ _ nonempty => exact absurd plain nonempty

theorem axioms_fresh {kinds : rdf_mapping.Kinds} {axs : List model.AnnotatedAxiom} {s0 s1 : Supply}
    {ps : List Pattern} (h : TAxioms axs s0 ps s1)
    (fragment : ∀ ax ∈ axs, ax.annotations.val = [] ∧ Readable kinds ax.axiom) :
    ∃ f, s0 = f ++ s1 ∧ BlankSubjects f ps := by
  induction h with
  | nil s => exact ⟨[], by simp, fun p member => by simp at member⟩
  | cons ax rest s s1 s2 p q head tail ih =>
    have this := fragment ax (by simp)
    obtain ⟨f1, eq1, sub1, -⟩ := readable_fresh this.2 (plain_axiom head this.1)
    obtain ⟨f2, eq2, sub2⟩ := ih (fun b member => fragment b (List.mem_cons_of_mem _ member))
    refine ⟨f1 ++ f2, by rw [eq1, eq2, List.append_assoc], ?_⟩
    intro r member y h
    rcases List.mem_append.mp member with left | right
    · exact List.mem_append_left _ (sub1 r left y h)
    · exact List.mem_append_right _ (sub2 r right y h)

theorem plain_annotated (ax : model.AnnotatedAxiom) (plain : ax.annotations.val = []) :
    (⟨alloc.vec.Vec.new _, ax.axiom⟩ : model.AnnotatedAxiom) = ax := by
  obtain ⟨anns, axm⟩ := ax
  simp only at plain ⊢
  rw [vec_eq_of_val (u := alloc.vec.Vec.new model.Annotation) (v := anns) (by simp [plain])]

/-- One axiom of the fragment reads back from the first triple of its block. -/
theorem read_block (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (ax : model.AnnotatedAxiom)
    (plain : ax.annotations.val = []) (readable : Readable kinds ax.axiom)
    (s0 s1 : Supply) (p : List Pattern) (tax : TAxiom ax.axiom s0 p s1)
    (fresh : Supply) (split : s0 = fresh ++ s1) (nodup : fresh.Nodup)
    (a : Usize) (s : rdf_mapping.State)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    (empty : ∀ b ∈ s.sources.val, b.val = [])
    (holds : Holds triples.val a.val p) (pending : Pending s.used.val a.val p.length)
    (owned : Owned triples.val s.used.val a.val p.length fresh)
    (fuelOk : p.length ≤ triples.val.length) (room : s.blanks.val.length + p.length ≤ Usize.max) :
    ∃ s', rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found ax.axiom s') ∧
      rdf_mapping.annotate triples kinds a ax.axiom s' (alloc.vec.Vec.len triples) = .ok (some (ax, s')) ∧
      Marked s s' (fun i => a.val ≤ i ∧ i < a.val + p.length) fresh := by
  obtain ⟨anns, axm⟩ := ax
  simp only at plain readable tax ⊢
  obtain ⟨_, _, _, _, positive⟩ := readable_fresh readable tax
  obtain ⟨t, at_t, fits⟩ := holds 0 positive
  simp only [Nat.add_zero] at at_t
  have inside : a.val < triples.val.length := (List.getElem?_eq_some_iff.mp at_t).1
  have annotateRun : ∀ s', (∀ b ∈ s'.sources.val, b.val = []) →
      rdf_mapping.annotate triples kinds a axm s' (alloc.vec.Vec.len triples) =
        .ok (some (⟨anns, axm⟩, s')) := by
    intro s' empty'
    have shape : rdf_mapping.main_triples axm = .ok 1#u8 := by
      cases readable <;> simp [rdf_mapping.main_triples]
    rw [annotate_plain triples kinds a axm s' _ shape inside empty']
    have := plain_annotated ⟨anns, axm⟩ plain
    simp only at this
    rw [this]
  cases readable with
  | declaration e =>
    cases tax with
    | declaration =>
      have none : fresh = [] := by simpa using split
      subst none
      refine ⟨_, read_axiom_declaration triples kinds a s _ t at_t e fits, annotateRun _ empty, ?_⟩
      refine marked_same (marked_take s a) ?_
      intro i
      simp only [List.length_singleton]
      omega
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | subClassOf c1 c2 e1 e2 =>
    obtain ⟨s', run, marked⟩ := sub_class_complete triples kinds c1 c2 e1 e2 s0 s1 p tax fresh split nodup a s
      (alloc.vec.Vec.len triples) complete holds pending owned (by simpa using fuelOk) room
    exact ⟨s', run, annotateRun s' (by rw [marked.sources]; exact empty), marked⟩

/-- One turn of the axiom loop at the first triple of a block. -/
theorem axioms_from_step (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a next : Usize)
    (st s' : rdf_mapping.State) (out pushed : alloc.vec.Vec model.AnnotatedAxiom) (ax : model.AnnotatedAxiom)
    (inside : a.val < triples.val.length) (isUnused : st.used.val[a.val]? = some false)
    (readRun : rdf_mapping.read_axiom triples kinds a st (alloc.vec.Vec.len triples) = .ok (.Found ax.axiom s'))
    (annotateRun : rdf_mapping.annotate triples kinds a ax.axiom s' (alloc.vec.Vec.len triples) =
      .ok (some (ax, s')))
    (pushRoom : out.val.length < Usize.max) (push : alloc.vec.Vec.push out ax = .ok pushed)
    (advance : (a + 1#usize : Result Usize) = .ok next) :
    rdf_mapping.axioms_from triples kinds a st out = rdf_mapping.axioms_from triples kinds next s' pushed := by
  rw [rdf_mapping.axioms_from]
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, is_used_correct, isUnused, ne_eq,
    not_true_eq_false, decide_false, Bool.false_eq_true, bind_ok, readRun, annotateRun, usize_max_val, pushRoom]
  change (Std.bind (alloc.vec.Vec.push out ax) _) = _
  rw [push, bind_ok]
  simp only [advance, bind_ok]

/-- The axiom loop reads back the blocks of the axioms of the fragment, in order. -/
theorem axioms_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) :
    ∀ (axs : List model.AnnotatedAxiom) (s0 s1 : Supply) (ps : List Pattern), TAxioms axs s0 ps s1 →
    (∀ ax ∈ axs, ax.annotations.val = [] ∧ Readable kinds ax.axiom) →
    ∀ (fresh : Supply), s0 = fresh ++ s1 → fresh.Nodup →
    ∀ (a : Usize) (st : rdf_mapping.State) (out : alloc.vec.Vec model.AnnotatedAxiom),
      a.val + ps.length = triples.val.length →
      SubjectsComplete triples.val st.subjects.val (alloc.vec.Vec.len st.subjects) triples.val.length →
      (∀ b ∈ st.sources.val, b.val = []) →
      Holds triples.val a.val ps →
      st.used.val.length = triples.val.length →
      (∀ (i : Nat), i < a.val → st.used.val[i]? = some true) →
      Pending st.used.val a.val ps.length →
      st.blanks.val.length ≤ a.val →
      out.val.length + axs.length ≤ Usize.max →
      ∃ v s', rdf_mapping.axioms_from triples kinds a st out = .ok (some (v, s')) ∧ v.val = out.val ++ axs ∧
        s'.blanks.val = st.blanks.val ++ fresh ∧
        ∀ (i : Nat), i < triples.val.length → s'.used.val[i]? = some true := by
  intro axs s0 s1 ps h
  induction h with
  | nil s =>
    intro _ fresh split nodup a st out ends complete empty holds length before pending blanks room
    have none : fresh = [] := by simpa using split
    subst none
    simp only [List.length_nil, Nat.add_zero] at ends
    refine ⟨out, st, axioms_from_end triples kinds st out a (by omega), by simp, by simp, ?_⟩
    intro i hi
    exact before i (by omega)
  | cons ax rest s0 s1 s2 p q head tail ih =>
    intro fragment fresh split nodup a st out ends complete empty holds length before pending blanks room
    have this := fragment ax (by simp)
    have tax := plain_axiom head this.1
    obtain ⟨f1, eq1, sub1, len1, positive⟩ := readable_fresh this.2 tax
    obtain ⟨f2, eq2, sub2⟩ := axioms_fresh tail (fun b member => fragment b (List.mem_cons_of_mem _ member))
    have freshIs : fresh = f1 ++ f2 := by
      rw [eq1, eq2] at split
      have h : (f1 ++ f2) ++ s2 = fresh ++ s2 := by simpa using split
      exact (List.append_cancel_right h).symm
    subst freshIs
    have nodup1 : f1.Nodup := (List.nodup_append.mp nodup).1
    have nodup2 : f2.Nodup := (List.nodup_append.mp nodup).2.1
    simp only [List.length_append] at ends pending
    obtain ⟨holds1, holds2⟩ := holds_append holds
    have ownedAll : Owned triples.val st.used.val a.val (p.length + q.length) (f1 ++ f2) := by
      intro i t y at_i unused about member
      have inside : i < triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
      refine ⟨?_, by omega⟩
      apply Classical.byContradiction
      intro low
      have := before i (by omega)
      rw [unused] at this
      cases this
    obtain ⟨owned1, -⟩ := owned_split holds ownedAll nodup sub1 sub2
    obtain ⟨pending1, pending2⟩ := pending_split pending
    have total : triples.val.length ≤ Usize.max := triples.property
    obtain ⟨s', readRun, annotateRun, marked⟩ := read_block triples kinds ax this.1 this.2 s0 s1 p tax f1 eq1 nodup1
      a st complete empty holds1 pending1 owned1 (by omega) (by omega)
    have isUnused : st.used.val[a.val]? = some false := by simpa using pending1 0 positive
    have inside : a.val < triples.val.length := by omega
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := a) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = a.val + 1 := by simpa using nextValue
    have pushRoom : out.val.length < Usize.max := by simp at room; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out ax pushRoom)
    have step := axioms_from_step triples kinds a next st s' out pushed ax inside isUnused readRun annotateRun
      pushRoom push advance
    have jBound : a.val + p.length < 2 ^ UScalarTy.Usize.numBits := by
      have : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
        simp only [Usize.max, Usize.numBits]
        have := Nat.pow_pos (n := UScalarTy.Usize.numBits) (show 0 < 2 by decide)
        omega
      omega
    let j : Usize := UScalar.ofNatCore (a.val + p.length) jBound
    have jVal : j.val = a.val + p.length := UScalar.ofNatCore_val_eq _
    have usedIn : ∀ (i : Nat), i < s'.used.val.length → (s'.used.val[i]? = some true ↔
        (st.used.val[i]? = some true ∨ (a.val ≤ i ∧ i < a.val + p.length))) := by
      intro i hi
      exact marked.used i (by rw [← marked.length]; exact hi)
    have lengthS' : s'.used.val.length = triples.val.length := by rw [marked.length, length]
    have skip := axioms_from_skip triples kinds s' pushed j (by omega) next (by omega) (by
      intro i low high
      have hi : i < s'.used.val.length := by omega
      rw [(usedIn i hi).mpr (Or.inr ⟨by omega, by omega⟩)]
      simp)
    obtain ⟨v, s'', run, vIs, blanksIs, allUsed⟩ := ih (fun b member => fragment b (List.mem_cons_of_mem _ member))
      f2 eq2 nodup2 j s' pushed (by omega)
      (by rw [marked.subjects]; exact complete)
      (by rw [marked.sources]; exact empty)
      (by rw [jVal]; exact holds2)
      lengthS'
      (by
        intro i hi
        have inside' : i < s'.used.val.length := by omega
        apply (usedIn i inside').mpr
        by_cases low : i < a.val
        · exact Or.inl (before i low)
        · exact Or.inr ⟨by omega, by omega⟩)
      (by
        intro k hk
        rw [jVal]
        have := marked_unused marked (pending2 k hk) (by intro h; omega)
        exact this)
      (by rw [marked.blanks, jVal]; simp; omega)
      (by rw [contents]; simp at room ⊢; omega)
    refine ⟨v, s'', by rw [step, skip, run], by rw [vIs, contents]; simp, by rw [blanksIs, marked.blanks]; simp,
      allUsed⟩

/-! ### The classification of the declared entities -/

/-- The declaration the reader takes a triple to make. -/
def DeclaresAs (t : rdf.Triple) (spelling : List U8) (kind : typing.EntityKind) : Prop :=
  ∃ v, rdf_mapping.declared_entity t = .ok (some (v, kind)) ∧ v.val = spelling

/-- The bucket of an IRI among `count` buckets. -/
def IriBucket (iri : alloc.vec.Vec U8) (count : Usize) (bucket : Usize) : Prop :=
  ∃ h, rdf_mapping.hash_iri iri = .ok h ∧ rdf_mapping.bucket_of h count = .ok bucket

/-- The declaration index after the triples before `below`: exactly their
    declarations, each in the bucket of its IRI. -/
structure KindsAt (triples : List rdf.Triple) (count : Usize) (below : Nat) (kinds : rdf_mapping.Kinds) : Prop where
  length : kinds.buckets.val.length = count.val
  sound : ∀ (j : Nat) (b : alloc.vec.Vec rdf_mapping.Declared), kinds.buckets.val[j]? = some b → ∀ d ∈ b.val,
    (∃ i t, i < below ∧ triples[i]? = some t ∧ DeclaresAs t d.iri.val d.kind) ∧
      ∃ bucket, IriBucket d.iri count bucket ∧ bucket.val = j
  complete : ∀ (i : Nat) (t : rdf.Triple) (spelling : alloc.vec.Vec U8) (kind : typing.EntityKind), i < below →
    triples[i]? = some t → DeclaresAs t spelling.val kind → ∀ bucket, IriBucket spelling count bucket →
    ∃ b, kinds.buckets.val[bucket.val]? = some b ∧ ∃ d ∈ b.val, d.iri = spelling ∧ d.kind = kind
  small : ∀ b ∈ kinds.buckets.val, b.val.length ≤ below

theorem declaration_kind_total (object : rdf.Object) : ∃ o, rdf_mapping.declaration_kind object = .ok o := by
  rw [rdf_mapping.declaration_kind]
  simp only [lift, bind_ok, object_is_correct, array_slice_val]
  repeat (split; exact ⟨_, rfl⟩)
  exact ⟨_, rfl⟩

theorem declared_entity_total (t : rdf.Triple) : ∃ o, rdf_mapping.declared_entity t = .ok o := by
  rw [rdf_mapping.declared_entity]
  simp only [lift, bind_ok, same_correct, array_slice_val]
  split
  · cases t.subject with
    | Iri iri =>
      obtain ⟨o, run⟩ := declaration_kind_total t.object
      simp only [run, bind_ok]
      cases o with
      | none => exact ⟨_, rfl⟩
      | some kind => exact ⟨some (iri.spelling, kind), by simp [Rowl.Nnf.copy_bytes_identity]⟩
    | Blank _ => exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem declared_entity_some (t : rdf.Triple) (v : alloc.vec.Vec U8) (kind : typing.EntityKind)
    (ran : rdf_mapping.declared_entity t = .ok (some (v, kind))) :
    t.predicate.spelling.val = rdfType ∧ ∃ iri, t.subject = .Iri iri ∧ v = iri.spelling ∧
      rdf_mapping.declaration_kind t.object = .ok (some kind) := by
  rw [rdf_mapping.declared_entity] at ran
  simp only [lift, bind_ok, same_correct, array_slice_val] at ran
  by_cases typed : t.predicate.spelling.val = rdfType
  · have typed' := typed
    simp only [rdfType] at typed'
    simp only [typed', decide_true, ↓reduceIte] at ran
    refine ⟨typed, ?_⟩
    cases subject : t.subject with
    | Iri iri =>
      simp only [subject] at ran
      obtain ⟨o, run⟩ := declaration_kind_total t.object
      simp only [run, bind_ok] at ran
      cases o with
      | none => simp at ran
      | some k =>
        simp only [Rowl.Nnf.copy_bytes_identity, bind_ok, Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ran
        obtain ⟨rfl, rfl⟩ := ran
        exact ⟨iri, rfl, rfl, run⟩
    | Blank _ => simp [subject] at ran
  · simp only [rdfType] at typed
    simp [typed] at ran

theorem iri_bucket_exists (iri : alloc.vec.Vec U8) (count : Usize) :
    ∃ bucket, IriBucket iri count bucket ∧ (0 < count.val → bucket.val < count.val) := by
  obtain ⟨h, hRun⟩ := hash_from_ok iri 0#usize 7#usize
  obtain ⟨bucket, bRun, lt⟩ := bucket_of_spec h count
  exact ⟨bucket, ⟨h, by simp [rdf_mapping.hash_iri, hRun], bRun⟩, lt⟩

theorem iri_bucket_unique {iri : alloc.vec.Vec U8} {count b1 b2 : Usize} (h1 : IriBucket iri count b1)
    (h2 : IriBucket iri count b2) : b1 = b2 := by
  obtain ⟨x1, r1, s1⟩ := h1
  obtain ⟨x2, r2, s2⟩ := h2
  rw [r1] at r2
  cases Result.ok_injective r2
  rw [s1] at s2
  exact Result.ok_injective s2

theorem declared_kinds_spec (triples : alloc.vec.Vec rdf.Triple) (count : Usize) (positive : 0 < count.val) :
    ∀ (index : Usize) (kinds : rdf_mapping.Kinds), index.val ≤ triples.val.length →
      KindsAt triples.val count index.val kinds →
      ∃ kinds', rdf_mapping.declared_kinds triples index kinds = .ok (some kinds') ∧
        KindsAt triples.val count triples.val.length kinds' := by
  intro index
  induction e : triples.val.length - index.val generalizing index with
  | zero =>
    intro kinds bounded at_index
    have done : ¬ index.val < triples.val.length := by omega
    refine ⟨kinds, by rw [rdf_mapping.declared_kinds]; simp [UScalar.lt_equiv, done], ?_⟩
    have below : triples.val.length ≤ index.val := by omega
    exact { length := at_index.length
            sound := fun j b at_j d member => by
              obtain ⟨⟨i, t, low, at_i, decl⟩, rest⟩ := at_index.sound j b at_j d member
              exact ⟨⟨i, t, (List.getElem?_eq_some_iff.mp at_i).1, at_i, decl⟩, rest⟩
            complete := fun i t sp k low at_i decl bucket which =>
              at_index.complete i t sp k (by have := (List.getElem?_eq_some_iff.mp at_i).1; omega) at_i decl bucket
                which
            small := fun b member => by have := at_index.small b member; omega }
  | succ n ih =>
    intro kinds bounded at_index
    have more : index.val < triples.val.length := by omega
    have at_t : triples.val[index.val]? = some triples.val[index.val] := List.getElem?_eq_getElem more
    have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, at_t]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨o, entityRun⟩ := declared_entity_total triples.val[index.val]
    rw [rdf_mapping.declared_kinds]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
      bind_ok, entityRun]
    cases o with
    | none =>
      simp only [advance, bind_ok]
      apply ih next (by omega) _ (by omega)
      exact { length := at_index.length
              sound := fun j b at_j d member => by
                obtain ⟨⟨i, t, low, at_i, decl⟩, rest⟩ := at_index.sound j b at_j d member
                exact ⟨⟨i, t, by omega, at_i, decl⟩, rest⟩
              complete := fun i t sp k low at_i decl bucket which => by
                by_cases here : i = index.val
                · subst here
                  rw [at_t] at at_i
                  cases at_i
                  obtain ⟨v, run, -⟩ := decl
                  rw [entityRun] at run
                  cases Result.ok_injective run
                · exact at_index.complete i t sp k (by omega) at_i decl bucket which
              small := fun b member => by have := at_index.small b member; omega }
    | some entry =>
      obtain ⟨spelling, kind⟩ := entry
      simp only
      obtain ⟨bucket, which, lt⟩ := iri_bucket_exists spelling count
      obtain ⟨h, hashRun, bucketRun⟩ := which
      have lenIs : alloc.vec.Vec.len kinds.buckets = count :=
        UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len_val, at_index.length])
      have inside : bucket.val < kinds.buckets.val.length := by rw [at_index.length]; exact lt positive
      have entry : kinds.buckets.index_usize bucket = .ok kinds.buckets.val[bucket.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      have fits : kinds.buckets.val[bucket.val].val.length < Usize.max := by
        have := at_index.small _ (List.getElem_mem inside)
        have : triples.val.length ≤ Usize.max := triples.property
        omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec kinds.buckets.val[bucket.val] ⟨spelling, kind⟩ fits)
      have addRun : rdf_mapping.add_kind kinds spelling kind =
          .ok (some { buckets := kinds.buckets.set bucket pushed }) := by
        rw [rdf_mapping.add_kind]
        simp [hashRun, lenIs, bucketRun, alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, entry, usize_max_val, fits,
          alloc.vec.Vec.index_mut_usize, push, lt positive]
      have decl0 : DeclaresAs triples.val[index.val] spelling.val kind := ⟨spelling, entityRun, rfl⟩
      obtain ⟨kinds', run, at_end⟩ := ih next (by omega) { buckets := kinds.buckets.set bucket pushed } (by omega) {
        length := by simp [alloc.vec.Vec.set_val_eq, at_index.length]
        sound := by
          intro j b at_j d member
          simp only [alloc.vec.Vec.set_val_eq] at at_j
          by_cases same : j = bucket.val
          · subst same
            rw [List.getElem?_set_self inside] at at_j
            cases at_j
            rw [contents] at member
            rcases List.mem_append.mp member with old | new
            · obtain ⟨⟨i, t, low, at_i, decl⟩, rest⟩ :=
                at_index.sound _ _ (List.getElem?_eq_getElem inside) d old
              exact ⟨⟨i, t, by omega, at_i, decl⟩, rest⟩
            · simp only [List.mem_singleton] at new
              subst new
              exact ⟨⟨index.val, _, by omega, at_t, decl0⟩, bucket, ⟨h, hashRun, bucketRun⟩, rfl⟩
          · rw [List.getElem?_set_ne (Ne.symm same)] at at_j
            obtain ⟨⟨i, t, low, at_i, decl⟩, rest⟩ := at_index.sound j b at_j d member
            exact ⟨⟨i, t, by omega, at_i, decl⟩, rest⟩
        complete := by
          intro i t sp k low at_i decl bucket' which'
          by_cases here : i = index.val
          · subst here
            rw [at_t] at at_i
            cases at_i
            obtain ⟨v, run, vIs⟩ := decl
            rw [entityRun] at run
            have result := Option.some.inj (Result.ok_injective run)
            simp only [Prod.mk.injEq] at result
            obtain ⟨hv, hk⟩ := result
            have spIs : sp = spelling := vec_eq_of_val (by rw [← vIs, ← hv])
            subst spIs
            subst hk
            have sameBucket := iri_bucket_unique which' ⟨h, hashRun, bucketRun⟩
            subst sameBucket
            refine ⟨pushed, by simp [alloc.vec.Vec.set_val_eq, List.getElem?_set_self inside], ⟨sp, kind⟩, ?_, rfl,
              rfl⟩
            rw [contents]
            simp
          · obtain ⟨b, at_b, d, member, dIri, dKind⟩ := at_index.complete i t sp k (by omega) at_i decl bucket' which'
            by_cases same : bucket'.val = bucket.val
            · rw [same, List.getElem?_eq_getElem inside] at at_b
              cases at_b
              refine ⟨pushed, by simp [alloc.vec.Vec.set_val_eq, same, List.getElem?_set_self inside], d, ?_,
                dIri, dKind⟩
              rw [contents]
              exact List.mem_append_left _ member
            · exact ⟨b, by rw [alloc.vec.Vec.set_val_eq, List.getElem?_set_ne (Ne.symm same)]; exact at_b, d, member,
                dIri, dKind⟩
        small := by
          intro b member
          rw [alloc.vec.Vec.set_val_eq] at member
          obtain ⟨j, at_j⟩ := List.mem_iff_getElem?.mp member
          by_cases same : j = bucket.val
          · subst same
            rw [List.getElem?_set_self inside] at at_j
            cases at_j
            rw [contents]
            simp
            have := at_index.small _ (List.getElem_mem inside)
            omega
          · rw [List.getElem?_set_ne (Ne.symm same)] at at_j
            have := at_index.small b (List.mem_of_getElem? at_j)
            omega }
      refine ⟨kinds', ?_, at_end⟩
      change (Std.bind (rdf_mapping.add_kind kinds spelling kind) _) = _
      rw [addRun, bind_ok]
      simp only [advance, bind_ok]
      exact run

/-- The declaration lookup decides exactly whether a triple of the graph declares
    the IRI with the kind. -/
theorem declared_correct (triples : List rdf.Triple) (count : Usize) (positive : 0 < count.val)
    (kinds : rdf_mapping.Kinds) (at_end : KindsAt triples count triples.length kinds) (iri : alloc.vec.Vec U8)
    (kind : typing.EntityKind) :
    rdf_mapping.declared kinds iri kind =
      .ok (decide (∃ (i : Nat) (t : rdf.Triple), triples[i]? = some t ∧ DeclaresAs t iri.val kind)) := by
  obtain ⟨bucket, which, lt⟩ := iri_bucket_exists iri count
  obtain ⟨h, hashRun, bucketRun⟩ := which
  have lenIs : alloc.vec.Vec.len kinds.buckets = count :=
    UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len_val, at_end.length])
  have inside : bucket.val < kinds.buckets.val.length := by rw [at_end.length]; exact lt positive
  have entry : kinds.buckets.index_usize bucket = .ok kinds.buckets.val[bucket.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
  rw [rdf_mapping.declared]
  simp only [hashRun, lenIs, bucketRun, bind_ok, alloc.vec.Vec.len_val, UScalar.lt_equiv, at_end.length,
    lt positive, ↓reduceIte, alloc.vec.Vec.index_slice_index, entry, declared_in_correct]
  congr 1
  rw [decide_eq_decide]
  constructor
  · rintro ⟨j, d, -, at_j, dIri, dKind⟩
    obtain ⟨⟨i, t, -, at_i, decl⟩, -⟩ := at_end.sound bucket.val _ (List.getElem?_eq_getElem inside) d
      (List.mem_of_getElem? at_j)
    rw [dIri, dKind] at decl
    exact ⟨i, t, at_i, decl⟩
  · rintro ⟨i, t, at_i, decl⟩
    obtain ⟨b, at_b, d, member, dIri, dKind⟩ := at_end.complete i t iri kind (List.getElem?_eq_some_iff.mp at_i).1
      at_i decl bucket ⟨h, hashRun, bucketRun⟩
    rw [List.getElem?_eq_getElem inside] at at_b
    cases at_b
    obtain ⟨j, at_j⟩ := List.mem_iff_getElem?.mp member
    exact ⟨j, d, Nat.zero_le _, at_j, dIri, dKind⟩

/-! ### The EL fragment -/

/-- The IRI that the main triple of an axiom is about, when it is about an IRI. -/
def subjectIri : model.Axiom → Option model.Iri
  | .Declaration (.Class c) => some c.iri
  | .Declaration (.Datatype d) => some d.iri
  | .Declaration (.ObjectProperty p) => some p.iri
  | .Declaration (.DataProperty p) => some p.iri
  | .Declaration (.AnnotationProperty p) => some p.iri
  | .Declaration (.NamedIndividual a) => some a.iri
  | .SubClassOf (.Class c) _ => some c.iri
  | _ => none

/-- An object property that the axioms declare as an object property and
    neither declare nor build in as a data or annotation property. -/
structure ObjectTyped (axioms : List model.AnnotatedAxiom) (p : model.ObjectProperty) : Prop where
  declared : ∃ ax ∈ axioms, ax.axiom = .Declaration (.ObjectProperty p)
  notData : ∀ ax ∈ axioms, ∀ d : model.DataProperty, ax.axiom = .Declaration (.DataProperty d) → d.iri ≠ p.iri
  notAnnotation : ∀ ax ∈ axioms, ∀ d : model.AnnotationProperty,
    ax.axiom = .Declaration (.AnnotationProperty d) → d.iri ≠ p.iri
  notBuiltinData : Rowl.Builtins.role p.iri.spelling.val ≠ some .DataProperty
  notBuiltinAnnotation : Rowl.Builtins.role p.iri.spelling.val ≠ some .AnnotationProperty

/-- The class expressions of the EL fragment: named classes and existential
    restrictions of object properties typed as such. -/
inductive ElClass (axioms : List model.AnnotatedAxiom) : model.ClassExpression → Prop
  | named (c : model.Class) : ElClass axioms (.Class c)
  | some (p : model.ObjectProperty) (c : model.ClassExpression) : ObjectTyped axioms p → ElClass axioms c →
      ElClass axioms (.ObjectSomeValuesFrom (.Property p) c)

/-- The axioms of the EL fragment: declarations, and subclass axioms between EL
    class expressions. -/
inductive ElAxiom (axioms : List model.AnnotatedAxiom) : model.Axiom → Prop
  | declaration (e : model.Entity) : ElAxiom axioms (.Declaration e)
  | subClassOf (c1 c2 : model.ClassExpression) : ElClass axioms c1 → ElClass axioms c2 →
      ElAxiom axioms (.SubClassOf c1 c2)

/-- The ontologies of the EL fragment: anonymous, or named without a version IRI;
    without imports or ontology annotations; with unannotated axioms of the EL
    fragment, none of whose main triples is about the ontology IRI. -/
structure ElOntology (o : model.RawOntology) : Prop where
  identity : o.identity = .Anonymous ∨ ∃ iri, o.identity = .Named iri none
  imports : o.imports.val = []
  annotations : o.annotations.val = []
  axioms : ∀ ax ∈ o.axioms.val, ax.annotations.val = [] ∧ ElAxiom o.axioms.val ax.axiom
  apart : ∀ iri version, o.identity = .Named iri version → ∀ ax ∈ o.axioms.val, subjectIri ax.axiom ≠ some iri

/-- The patterns of the axioms of the fragment: declarations, main triples of
    subclass axioms, and the triples of restrictions about their blank nodes. -/
inductive AxiomPattern (axs : List model.AnnotatedAxiom) : Pattern → Prop
  | declaration (ax : model.AnnotatedAxiom) (e : model.Entity) : ax ∈ axs → ax.axiom = .Declaration e →
      AxiomPattern axs (declarationPattern e)
  | main (ax : model.AnnotatedAxiom) (q : Pattern) : ax ∈ axs → q.predicate = rdfsSubClassOf →
      (∀ sp, q.subject = .iri sp → ∃ iri, subjectIri ax.axiom = some iri ∧ iri.spelling.val = sp) →
      AxiomPattern axs q
  | side (q : Pattern) (y : rdf.BlankNode) : q.subject = .blank y →
      (q.predicate = rdfType ∨ q.predicate = owlOnProperty ∨ q.predicate = owlSomeValuesFrom) → AxiomPattern axs q

theorem el_class_patterns {axs : List model.AnnotatedAxiom} {c : model.ClassExpression} (el : ElClass axs c) :
    ∀ {s0 s1 : Supply} {n : Node} {ps : List Pattern}, TCE c s0 n ps s1 →
      ∀ q ∈ ps, q.predicate = rdfType ∨ q.predicate = owlOnProperty ∨ q.predicate = owlSomeValuesFrom := by
  induction el with
  | named c =>
    intro s0 s1 n ps tce q member
    cases tce
    simp at member
  | some p c typed inner ih =>
    intro s0 s1 n ps tce q member
    cases tce with
    | some role c' x s' s1' s2 n1 n2 p1 p2 tope tce' =>
      cases tope
      simp only [restrictionHead, List.cons_append, List.nil_append, List.mem_cons] at member
      rcases member with rfl | rfl | rfl | rest
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact ih tce' q rest

theorem el_class_node {axs : List model.AnnotatedAxiom} {c : model.ClassExpression} (el : ElClass axs c)
    {s0 s1 : Supply} {n : Node} {ps : List Pattern} (tce : TCE c s0 n ps s1) :
    ∀ sp, n = .iri sp → ∃ cl, c = .Class cl ∧ cl.iri.spelling.val = sp := by
  intro sp h
  cases el with
  | named cl =>
    cases tce
    simp only [iriNode, Node.iri.injEq] at h
    exact ⟨cl, rfl, h⟩
  | some p c typed inner =>
    cases tce
    simp at h

theorem axiom_patterns {axsAll : List model.AnnotatedAxiom} {axs : List model.AnnotatedAxiom} {s0 s1 : Supply}
    {ps : List Pattern} (h : TAxioms axs s0 ps s1)
    (fragment : ∀ ax ∈ axs, ax.annotations.val = [] ∧ ElAxiom axsAll ax.axiom) (sub : ∀ ax ∈ axs, ax ∈ axsAll) :
    ∀ q ∈ ps, AxiomPattern axsAll q := by
  induction h with
  | nil s => intro q member; simp at member
  | cons ax rest s s1 s2 p q' head tail ih =>
    intro r member
    have this := fragment ax (by simp)
    have tax := plain_axiom head this.1
    rcases List.mem_append.mp member with inHead | inTail
    · obtain ⟨anns, axm⟩ := ax
      simp only at this tax
      have axIn := sub ⟨anns, axm⟩ (List.mem_cons_self ..)
      cases this.2 with
      | declaration e =>
        cases tax with
        | declaration =>
          simp only [List.mem_singleton] at inHead
          subst inHead
          exact .declaration _ e axIn rfl
        | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
      | subClassOf c1 c2 e1 e2 =>
        cases tax with
        | subClassOf _ _ _ s1' _ n1 n2 p1 p2 tce1 tce2 =>
          obtain ⟨f1, -, sub1⟩ := tce_fresh tce1
          obtain ⟨f2, -, sub2⟩ := tce_fresh tce2
          simp only [List.mem_cons, List.mem_append] at inHead
          rcases inHead with rfl | inner | inner
          · refine .main _ _ axIn rfl ?_
            intro sp hn
            obtain ⟨cl, rfl, spelled⟩ := el_class_node e1 tce1 sp hn
            exact ⟨cl.iri, rfl, spelled⟩
          · obtain ⟨y, -, about⟩ := sub1 r inner
            exact .side r y about (el_class_patterns e1 tce1 r inner)
          · obtain ⟨y, -, about⟩ := sub2 r inner
            exact .side r y about (el_class_patterns e2 tce2 r inner)
        | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
    · exact ih (fun b m => fragment b (List.mem_cons_of_mem _ m)) (fun b m => sub b (List.mem_cons_of_mem _ m)) r
        inTail

theorem declaration_patterns_in {axsAll : List model.AnnotatedAxiom} {axs : List model.AnnotatedAxiom}
    {s0 s1 : Supply} {ps : List Pattern} (h : TAxioms axs s0 ps s1)
    (fragment : ∀ ax ∈ axs, ax.annotations.val = [] ∧ ElAxiom axsAll ax.axiom) :
    ∀ ax ∈ axs, ∀ e, ax.axiom = .Declaration e → declarationPattern e ∈ ps := by
  induction h with
  | nil s => intro ax member; simp at member
  | cons ax rest s s1 s2 p q head tail ih =>
    intro b member e isDecl
    rcases List.mem_cons.mp member with rfl | inTail
    · have this := fragment b (by simp)
      have tax := plain_axiom head this.1
      rw [isDecl] at tax
      cases tax with
      | declaration => simp
      | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
    · exact List.mem_append_right _ (ih (fun c m => fragment c (List.mem_cons_of_mem _ m)) b inTail e isDecl)

/-! ### The classification of the properties of a graph of the fragment -/

/-- The pattern typing the ontology IRI `owl:Ontology`. -/
def headerPattern (iri : model.Iri) : Pattern := ⟨iriNode iri, rdfType, .iri owlOntology⟩

/-- The patterns of an ontology of the fragment: its header, and patterns of its axioms. -/
def GraphShape (axs : List model.AnnotatedAxiom) (onto : Option model.Iri) (q : Pattern) : Prop :=
  (∃ iri, onto = some iri ∧ q = headerPattern iri) ∨ AxiomPattern axs q

def entityOf (kind : typing.EntityKind) (v : alloc.vec.Vec U8) : model.Entity :=
  match kind with
  | .Class => .Class ⟨⟨v⟩⟩
  | .Datatype => .Datatype ⟨⟨v⟩⟩
  | .ObjectProperty => .ObjectProperty ⟨⟨v⟩⟩
  | .DataProperty => .DataProperty ⟨⟨v⟩⟩
  | .AnnotationProperty => .AnnotationProperty ⟨⟨v⟩⟩
  | .NamedIndividual => .NamedIndividual ⟨⟨v⟩⟩

theorem entity_of_pure (kind : typing.EntityKind) (v : alloc.vec.Vec U8) :
    rdf_mapping.entity_of kind v = .ok (entityOf kind v) := by
  cases kind <;> simp [rdf_mapping.entity_of, iri_of_identity, entityOf]

theorem declaration_kind_ontology (object : rdf.Object) (onto : objectView object = .iri owlOntology) :
    rdf_mapping.declaration_kind object = .ok none := by
  rw [rdf_mapping.declaration_kind]
  simp only [lift, bind_ok, object_is_correct, array_slice_val]
  simp [onto, owlOntology]

/-- The type triple of a declaration declares its entity. -/
theorem declares_of_declaration (e : model.Entity) (t : rdf.Triple) (fits : Matches (declarationPattern e) t) :
    ∃ v kind, rdf_mapping.declared_entity t = .ok (some (v, kind)) ∧ entityOf kind v = e := by
  have typed : t.predicate.spelling.val = rdfType := by
    have := fits.2.1
    cases e <;> exact this
  obtain ⟨iri, isIri⟩ : ∃ iri, t.subject = .Iri iri := by
    cases h : t.subject with
    | Iri iri => exact ⟨iri, rfl⟩
    | Blank b =>
      have subject := fits.1
      rw [h] at subject
      cases e <;> simp [declarationPattern, iriNode, subjectView] at subject
  obtain ⟨kind, kindRun⟩ := declaration_kind_some e t.object fits.2.2
  obtain ⟨e', entityRun, pattern⟩ := entity_of_spec t.object kind kindRun iri.spelling
  have same : e' = e := by
    apply declaration_pattern_injective
    rw [pattern, pattern_of_matches fits, isIri, typed]
    rfl
  refine ⟨iri.spelling, kind, ?_, ?_⟩
  · rw [rdf_mapping.declared_entity]
    have typed' := typed
    simp only [rdfType] at typed'
    simp [lift, same_correct, array_slice_val, typed', isIri, kindRun, Rowl.Nnf.copy_bytes_identity]
  · rw [entity_of_pure] at entityRun
    rw [← same]
    exact Result.ok_injective entityRun

/-- A declaration that a triple of a graph of the fragment makes is one of its
    declaration axioms. -/
theorem declares_in_graph {axs : List model.AnnotatedAxiom} {onto : Option model.Iri} {q : Pattern}
    {t : rdf.Triple} {spelling : List U8} {kind : typing.EntityKind} (shape : GraphShape axs onto q)
    (fits : Matches q t) (decl : DeclaresAs t spelling kind) :
    ∃ ax ∈ axs, ∃ v : alloc.vec.Vec U8, v.val = spelling ∧ ax.axiom = .Declaration (entityOf kind v) := by
  obtain ⟨v, run, vIs⟩ := decl
  obtain ⟨typed, iri, isIri, vIri, kindRun⟩ := declared_entity_some t v kind run
  rcases shape with ⟨iri', -, rfl⟩ | shape
  · have := declaration_kind_ontology t.object fits.2.2
    rw [this] at kindRun
    cases Result.ok_injective kindRun
  · cases shape with
    | declaration ax e member isDecl =>
      obtain ⟨v', kind', run', same⟩ := declares_of_declaration e t fits
      rw [run] at run'
      have result := Option.some.inj (Result.ok_injective run')
      simp only [Prod.mk.injEq] at result
      obtain ⟨rfl, rfl⟩ := result
      exact ⟨ax, member, v, vIs, by rw [isDecl, same]⟩
    | main ax q member predicate _ =>
      have := fits.2.1
      rw [predicate, typed] at this
      simp [rdfType, rdfsSubClassOf] at this
    | side q y blank _ =>
      have := fits.1
      rw [blank, isIri] at this
      simp [subjectView] at this

theorem matches_at {triples : List rdf.Triple} {ps : List Pattern} (holds : Holds triples 0 ps)
    (length : triples.length = ps.length) {i : Nat} {t : rdf.Triple} (at_i : triples[i]? = some t) :
    ∃ q ∈ ps, Matches q t := by
  have inside : i < ps.length := by rw [← length]; exact (List.getElem?_eq_some_iff.mp at_i).1
  obtain ⟨t', at_t', fits⟩ := holds i inside
  rw [Nat.zero_add, at_i] at at_t'
  cases at_t'
  exact ⟨ps[i], List.getElem_mem _, fits⟩

theorem has_kind_correct (triples : List rdf.Triple) (count : Usize) (positive : 0 < count.val)
    (kinds : rdf_mapping.Kinds) (at_end : KindsAt triples count triples.length kinds) (iri : alloc.vec.Vec U8)
    (kind : typing.EntityKind) :
    rdf_mapping.has_kind kinds iri kind = .ok (decide ((∃ (i : Nat) (t : rdf.Triple), triples[i]? = some t ∧
      DeclaresAs t iri.val kind) ∨ Rowl.Builtins.role iri.val = some kind)) := by
  rw [rdf_mapping.has_kind, declared_correct triples count positive kinds at_end iri kind]
  simp only [bind_ok, Rowl.Builtins.builtin_kind_total_correct]
  by_cases found : ∃ (i : Nat) (t : rdf.Triple), triples[i]? = some t ∧ DeclaresAs t iri.val kind
  · simp [found]
  · simp only [found, decide_false, Bool.false_eq_true, ↓reduceIte, false_or]
    cases Rowl.Builtins.role iri.val with
    | none => simp
    | some b => simp [same_kind_correct]

/-- The properties of the existential restrictions of a graph of the fragment
    are classified as object properties. -/
theorem object_typed_kind (triples : List rdf.Triple) (count : Usize) (positive : 0 < count.val)
    (kinds : rdf_mapping.Kinds) (at_end : KindsAt triples count triples.length kinds)
    (axs : List model.AnnotatedAxiom) (onto : Option model.Iri) (patterns : List Pattern)
    (shape : ∀ q ∈ patterns, GraphShape axs onto q) (holds : Holds triples 0 patterns)
    (length : triples.length = patterns.length)
    (declsIn : ∀ ax ∈ axs, ∀ e, ax.axiom = .Declaration e → declarationPattern e ∈ patterns)
    (p : model.ObjectProperty) (typed : ObjectTyped axs p) :
    rdf_mapping.property_kind kinds p.iri.spelling = .ok (some .Object) := by
  have object : ∃ (i : Nat) (t : rdf.Triple), triples[i]? = some t ∧ DeclaresAs t p.iri.spelling.val .ObjectProperty := by
    obtain ⟨ax, member, isDecl⟩ := typed.declared
    have inPatterns := declsIn ax member _ isDecl
    obtain ⟨i, at_i⟩ := List.mem_iff_getElem?.mp inPatterns
    have inside : i < patterns.length := (List.getElem?_eq_some_iff.mp at_i).1
    obtain ⟨t, at_t, fits⟩ := holds i inside
    rw [Nat.zero_add] at at_t
    have fits' : Matches (declarationPattern (.ObjectProperty p)) t := by
      rw [List.getElem?_eq_getElem inside] at at_i
      rw [← Option.some.inj at_i]
      exact fits
    obtain ⟨v, kind, run, same⟩ := declares_of_declaration _ t fits'
    cases kind <;> simp [entityOf] at same
    exact ⟨i, t, at_t, v, run, by rw [← same]⟩
  have notKind : ∀ k, (k = .DataProperty ∨ k = .AnnotationProperty) →
      ¬ ∃ (i : Nat) (t : rdf.Triple), triples[i]? = some t ∧ DeclaresAs t p.iri.spelling.val k := by
    rintro k which ⟨i, t, at_t, decl⟩
    obtain ⟨q, member, fits⟩ := matches_at holds length at_t
    obtain ⟨ax, axIn, v, vIs, isDecl⟩ := declares_in_graph (shape q member) fits decl
    have iriIs : (⟨v⟩ : model.Iri) = p.iri := iri_ext vIs
    rcases which with rfl | rfl
    · exact typed.notData ax axIn ⟨⟨v⟩⟩ isDecl iriIs
    · exact typed.notAnnotation ax axIn ⟨⟨v⟩⟩ isDecl iriIs
  have notData := notKind .DataProperty (Or.inl rfl)
  have notAnnotation := notKind .AnnotationProperty (Or.inr rfl)
  rw [rdf_mapping.property_kind]
  simp only [has_kind_correct triples count positive kinds at_end, bind_ok]
  simp [object, notData, notAnnotation, typed.notBuiltinData, typed.notBuiltinAnnotation]

theorem el_class_existential {axs : List model.AnnotatedAxiom} {kinds : rdf_mapping.Kinds}
    (kindsOk : ∀ p, ObjectTyped axs p → rdf_mapping.property_kind kinds p.iri.spelling = .ok (some .Object))
    {c : model.ClassExpression} (el : ElClass axs c) : Existential kinds c := by
  induction el with
  | named c => exact .named c
  | some p c typed inner ih => exact .some p c (kindsOk p typed) ih

theorem el_axiom_readable {axs : List model.AnnotatedAxiom} {kinds : rdf_mapping.Kinds}
    (kindsOk : ∀ p, ObjectTyped axs p → rdf_mapping.property_kind kinds p.iri.spelling = .ok (some .Object))
    {ax : model.Axiom} (el : ElAxiom axs ax) : Readable kinds ax := by
  cases el with
  | declaration e => exact .declaration e
  | subClassOf c1 c2 e1 e2 => exact .subClassOf c1 c2 (el_class_existential kindsOk e1) (el_class_existential kindsOk e2)

/-! ### The mapping of a graph of the fragment -/

theorem forall2_holds {ps : List Pattern} {ts : List rdf.Triple} (h : List.Forall₂ Matches ps ts) :
    ts.length = ps.length ∧ Holds ts 0 ps := by
  obtain ⟨len, each⟩ := List.forall₂_iff_get.mp h
  refine ⟨len.symm, fun j hj => ⟨ts[j]'(by omega), by rw [Nat.zero_add]; exact List.getElem?_eq_getElem _, ?_⟩⟩
  simpa using each j hj (by omega)

theorem unused_total (count : Usize) :
    ∀ (out : alloc.vec.Vec Bool), ∃ v, rdf_mapping.unused count out = .ok v := by
  intro out
  induction h : count.val - out.val.length generalizing out with
  | zero =>
    have done : ¬ out.val.length < count.val := by omega
    exact ⟨out, by rw [rdf_mapping.unused]; simp [UScalar.lt_equiv, done]⟩
  | succ n ih =>
    have more : out.val.length < count.val := by omega
    have room : out.val.length < Usize.max := by scalar_tac
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out false room)
    obtain ⟨v, run⟩ := ih pushed (by rw [contents]; simp; omega)
    exact ⟨v, by rw [rdf_mapping.unused]; simp [UScalar.lt_equiv, more, push, run]⟩

/-- The header of an ontology of the fragment: none, or the triple typing its IRI. -/
theorem el_header {o : model.RawOntology} (el : ElOntology o) {supply : Supply} {header : List Pattern}
    {rest : Supply} (h : THeader o supply header rest) :
    rest = supply ∧ ((o.identity = .Anonymous ∧ header = []) ∨
      ∃ iri, o.identity = .Named iri none ∧ header = [headerPattern iri]) := by
  cases h with
  | anonymous _ hid _ _ => exact ⟨rfl, Or.inl ⟨hid, rfl⟩⟩
  | named iri version s s' anns hid tanns =>
    rw [el.annotations] at tanns
    obtain ⟨rfl, rfl⟩ := tanns_nil tanns
    have versionNone : version = none := by
      rcases el.identity with h | ⟨iri', h⟩
      · rw [hid] at h; cases h
      · rw [hid] at h
        simp only [model.OntologyIdentity.Named.injEq] at h
        exact h.2
    subst versionNone
    refine ⟨rfl, Or.inr ⟨iri, hid, ?_⟩⟩
    simp [headerPattern, el.imports]

theorem declaration_subject (e : model.Entity) :
    ∃ iri, subjectIri (.Declaration e) = some iri ∧ (declarationPattern e).subject = iriNode iri := by
  cases e <;> exact ⟨_, rfl, rfl⟩

/-- **The RDF mapping reads back every ontology of the EL fragment.** For an
    ontology of the fragment, a graph that lists, in order, the triples of its
    forward mapping with pairwise distinct blank nodes is mapped back to exactly
    that ontology, with exactly those blank nodes. -/
theorem map_graph_complete (graph : rdf.RawGraph) (o : model.RawOntology) (supply : Supply)
    (patterns : List Pattern) (el : ElOntology o) (forward : TOntology o supply patterns)
    (distinct : supply.Nodup) (image : List.Forall₂ Matches patterns graph.triples.val) :
    ∃ m, rdf_mapping.map_graph graph = .ok (some m) ∧ m.ontology = o ∧ m.blanks.val = supply := by
  obtain ⟨header, axiomPs, rest, theader, taxioms, split⟩ := forward
  obtain ⟨restIs, headerShape⟩ := el_header el theader
  rw [restIs] at taxioms
  obtain ⟨length, holds⟩ := forall2_holds image
  have total : graph.triples.val.length ≤ Usize.max := graph.triples.property
  have elAxioms := el.axioms
  have axiomShape := axiom_patterns taxioms elAxioms (fun ax m => m)
  have declsIn : ∀ ax ∈ o.axioms.val, ∀ e, ax.axiom = .Declaration e → declarationPattern e ∈ patterns :=
    fun ax m e d => by rw [split]; exact List.mem_append_right _ (declaration_patterns_in taxioms elAxioms ax m e d)
  -- the onto IRI, if any
  let onto : Option model.Iri := match o.identity with
    | .Named iri _ => some iri
    | .Anonymous => none
  have shape : ∀ q ∈ patterns, GraphShape o.axioms.val onto q := by
    intro q member
    rw [split] at member
    rcases List.mem_append.mp member with inHeader | inAxioms
    · rcases headerShape with ⟨-, rfl⟩ | ⟨iri, hid, rfl⟩
      · simp at inHeader
      · simp only [List.mem_singleton] at inHeader
        subst inHeader
        exact Or.inl ⟨iri, by simp [onto, hid], rfl⟩
    · exact Or.inr (axiomShape q inAxioms)
  have noSource : ∀ (i : Nat) (t : rdf.Triple), graph.triples.val[i]? = some t →
      t.predicate.spelling.val ≠ owlAnnotatedSource := by
    intro i t at_i
    obtain ⟨q, member, fits⟩ := matches_at holds length at_i
    rw [fits.2.1]
    rcases shape q member with ⟨iri, -, rfl⟩ | shapeQ
    · simp [headerPattern, rdfType, owlAnnotatedSource]
    · cases shapeQ with
      | declaration ax e _ _ => cases e <;> simp [declarationPattern, rdfType, owlAnnotatedSource]
      | main ax q _ predicate _ => rw [predicate]; simp [rdfsSubClassOf, owlAnnotatedSource]
      | side q y _ predicate =>
        rcases predicate with h | h | h <;> rw [h] <;> simp [rdfType, owlOnProperty, owlSomeValuesFrom, owlAnnotatedSource]
  -- the indexes
  obtain ⟨c, countRun, cPos⟩ := bucket_count_spec (alloc.vec.Vec.len graph.triples)
  obtain ⟨vk, kindBucketsRun, vkLength, vkEmpty⟩ := empty_buckets_spec (T := rdf_mapping.Declared) c
    (alloc.vec.Vec.new _) (by simp) (by simp)
  have kinds0 : KindsAt graph.triples.val c (0#usize : Usize).val { buckets := vk } :=
    { length := vkLength
      sound := fun j b at_j d member => by
        have := vkEmpty b (List.mem_of_getElem? at_j)
        rw [this] at member
        simp at member
      complete := fun i t sp k low => by simp at low
      small := fun b member => by rw [vkEmpty b member]; simp }
  obtain ⟨kinds, kindsRun, kindsEnd⟩ := declared_kinds_spec graph.triples c cPos 0#usize { buckets := vk }
    (by simp) kinds0
  have kindsOk : ∀ p, ObjectTyped o.axioms.val p →
      rdf_mapping.property_kind kinds p.iri.spelling = .ok (some .Object) :=
    object_typed_kind graph.triples.val c cPos kinds kindsEnd o.axioms.val onto patterns shape holds length declsIn
  have readable : ∀ ax ∈ o.axioms.val, ax.annotations.val = [] ∧ Readable kinds ax.axiom :=
    fun ax m => ⟨(elAxioms ax m).1, el_axiom_readable kindsOk (elAxioms ax m).2⟩
  obtain ⟨v1, unusedRun⟩ := unused_total (alloc.vec.Vec.len graph.triples) (alloc.vec.Vec.new Bool)
  have v1Is := unused_spec _ _ v1 unusedRun
  simp at v1Is
  obtain ⟨v2, bucketsRun, v2Length, v2Empty⟩ := empty_buckets_spec (T := Usize) c (alloc.vec.Vec.new _) (by simp)
    (by simp)
  obtain ⟨v3, subjectsRun⟩ := subjects_from_total graph.triples 0#usize v2
  have v2Len : (alloc.vec.Vec.len v2).val = c.val := by simp [alloc.vec.Vec.len_val, v2Length]
  obtain ⟨-, complete⟩ := subjects_from_spec graph.triples 0#usize v2 v3 (by rw [v2Length]; exact cPos)
    (fun b member => by rw [v2Empty b member]; simp)
    (fun i t node bucket low => by simp at low) subjectsRun
  have sourcesRun := sources_from_none graph.triples noSource 0#usize v2
  have lengthV3 : alloc.vec.Vec.len v3 = alloc.vec.Vec.len v2 := by
    apply UScalar.eq_of_val_eq
    obtain ⟨l, -⟩ := subjects_from_spec graph.triples 0#usize v2 v3 (by rw [v2Length]; exact cPos)
      (fun b member => by rw [v2Empty b member]; simp) (fun i t node bucket low => by simp at low) subjectsRun
    simp [alloc.vec.Vec.len_val, l]
  rw [← lengthV3] at complete
  let st0 : rdf_mapping.State := { used := v1, blanks := alloc.vec.Vec.new _, subjects := v3, sources := v2 }
  have st0Used : ∀ (i : Nat), i < graph.triples.val.length → st0.used.val[i]? = some false := by
    intro i hi
    simp [st0, v1Is, List.getElem?_replicate, hi]
  have st0Length : st0.used.val.length = graph.triples.val.length := by simp [st0, v1Is]
  have nodupAll := distinct
  rcases headerShape with ⟨anonymous, rfl⟩ | ⟨iri, named, rfl⟩
  · -- an anonymous ontology: no header
    simp only [List.nil_append] at split
    subst split
    have headerRun : rdf_mapping.find_header graph.triples v1 0#usize = .ok none := by
      apply find_header_none
      intro i t _ at_i typed onto' iri isIri
      obtain ⟨q, member, fits⟩ := matches_at holds length at_i
      rcases shape q member with ⟨iri', isSome, -⟩ | shapeQ
      · simp [onto, anonymous] at isSome
      · cases shapeQ with
        | declaration ax e _ _ =>
          have := fits.2.2
          rw [onto'] at this
          cases e <;> simp [declarationPattern, owlOntology, owlClass, rdfsDatatype, owlObjectProperty,
            owlDatatypeProperty, owlAnnotationProperty, owlNamedIndividual] at this
        | main ax q _ predicate _ =>
          have := fits.2.1
          rw [predicate, typed] at this
          simp [rdfType, rdfsSubClassOf] at this
        | side q y blank _ =>
          have := fits.1
          rw [blank, isIri] at this
          simp [subjectView] at this
    have st0Blanks : st0.blanks.val = [] := by simp [st0]
    have st0Sources : ∀ b ∈ st0.sources.val, b.val = [] := v2Empty
    obtain ⟨v, s', axiomsRun, vIs, blanksIs, allUsed⟩ := axioms_complete graph.triples kinds o.axioms.val supply []
      patterns taxioms readable supply (by simp) distinct 0#usize st0 (alloc.vec.Vec.new _)
      (by have z : (0#usize : Usize).val = 0 := by simp
          omega)
      complete st0Sources (by have z : (0#usize : Usize).val = 0 := by simp
                              rw [z]; exact holds) st0Length (fun i hi => by simp at hi)
      (fun j hj => by
        have z : (0#usize : Usize).val = 0 := by simp
        rw [z, Nat.zero_add]
        exact st0Used j (by omega))
      (by rw [st0Blanks]; simp)
      (by have := o.axioms.property
          have z : (alloc.vec.Vec.new model.AnnotatedAxiom).val.length = 0 := by simp
          omega)
    have allRun := all_read_used graph.triples s'.used 0#usize (fun i _ hi => allUsed i hi)
    refine ⟨⟨⟨.Anonymous, alloc.vec.Vec.new _, alloc.vec.Vec.new _, v⟩, s'.blanks⟩, ?_, ?_, ?_⟩
    · rw [rdf_mapping.map_graph]
      simp only [countRun, bind_ok, kindBucketsRun, kindsRun, unusedRun, bucketsRun, subjectsRun, sourcesRun,
        headerRun]
      have axiomsRun' : rdf_mapping.axioms_from graph.triples kinds 0#usize
          { used := v1, blanks := alloc.vec.Vec.new rdf.BlankNode, subjects := v3, sources := v2 }
          (alloc.vec.Vec.new model.AnnotatedAxiom) = .ok (some (v, s')) := axiomsRun
      rw [axiomsRun']
      simp only [bind_ok]
      change (Std.bind (rdf_mapping.all_read graph.triples s'.used 0#usize) _) = _
      rw [allRun, bind_ok]
      rfl
    · obtain ⟨identity, imports, annotations, axioms⟩ := o
      simp only at anonymous el ⊢
      subst anonymous
      have importsNil : imports.val = [] := el.imports
      have annotationsNil : annotations.val = [] := el.annotations
      simp only [model.RawOntology.mk.injEq, true_and]
      refine ⟨vec_eq_of_val (by simp [importsNil]), vec_eq_of_val (by simp [annotationsNil]),
        vec_eq_of_val (by simpa using vIs)⟩
    · rw [blanksIs, st0Blanks]
      simp
  · -- a named ontology: its header triple first
    simp only [List.singleton_append] at split
    subst split
    obtain ⟨t0, at0, fits0⟩ := holds 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at at0 fits0
    have holdsRest : Holds graph.triples.val 1 axiomPs := by
      have := (holds_append (ps := [headerPattern iri]) (qs := axiomPs) holds).2
      simpa using this
    obtain ⟨iri0, isIri0, spelled0⟩ : ∃ iri0, t0.subject = .Iri iri0 ∧ iri0.spelling.val = iri.spelling.val := by
      have subject := fits0.1
      cases h : t0.subject with
      | Iri iri0 =>
        rw [h] at subject
        simp only [headerPattern, iriNode, subjectView, Node.iri.injEq] at subject
        exact ⟨iri0, rfl, subject⟩
      | Blank _ => rw [h] at subject; simp [headerPattern, iriNode, subjectView] at subject
    have lengthPos : 0 < graph.triples.val.length := by rw [length]; simp
    have unused0 : v1.val[0]? = some false := by simp [v1Is, List.getElem?_replicate, lengthPos]
    have headerRun : rdf_mapping.find_header graph.triples v1 0#usize = .ok (some 0#usize) := by
      have z : (0#usize : Usize).val = 0 := by simp
      apply find_header_at graph.triples v1 0#usize t0 (by rw [z]; exact at0) (by rw [z]; exact unused0)
        fits0.2.1 fits0.2.2 iri0 isIri0
    let st1 : rdf_mapping.State :=
      { used := v1.set 0#usize true, blanks := alloc.vec.Vec.new _, subjects := v3, sources := v2 }
    have z : (0#usize : Usize).val = 0 := by simp
    have st1Used0 : st1.used.val[0]? = some true := by
      simp [st1, alloc.vec.Vec.set_val_eq, z, List.getElem?_set_self (show 0 < v1.val.length by simp [v1Is, lengthPos])]
    have st1UsedRest : ∀ (i : Nat), 0 < i → st1.used.val[i]? = v1.val[i]? := by
      intro i pos
      simp only [st1, alloc.vec.Vec.set_val_eq, z]
      rw [List.getElem?_set_ne (by omega)]
    have st1Length : st1.used.val.length = graph.triples.val.length := by simp [st1, alloc.vec.Vec.set_val_eq, v1Is]
    have partsRun : rdf_mapping.header_parts graph.triples kinds iri0.spelling 0#usize st1 none
        (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) =
        .ok (some (none, alloc.vec.Vec.new _, alloc.vec.Vec.new _, st1)) := by
      apply header_parts_skip
      intro i t _ at_i unused about
      have pos : 0 < i := by
        apply Nat.pos_of_ne_zero
        intro zero
        subst zero
        rw [st1Used0] at unused
        cases unused
      have hi : i - 1 < axiomPs.length := by
        have := (List.getElem?_eq_some_iff.mp at_i).1
        simp at length
        omega
      obtain ⟨t', at_t', fits⟩ := holdsRest (i - 1) hi
      rw [show 1 + (i - 1) = i by omega, at_i] at at_t'
      cases at_t'
      have shapeQ := axiomShape _ (List.getElem_mem hi)
      have subject := fits.1
      rw [about, spelled0] at subject
      generalize axiomPs[i - 1]'hi = q at shapeQ subject
      cases shapeQ with
      | declaration ax e member isDecl =>
        obtain ⟨iri', subjectIs, patternSubject⟩ := declaration_subject e
        rw [patternSubject] at subject
        simp only [iriNode, Node.iri.injEq] at subject
        have same : iri' = iri := iri_ext subject.symm
        rw [same] at subjectIs
        exact el.apart iri none named ax member (by rw [isDecl]; exact subjectIs)
      | main ax q member _ subjectIri' =>
        obtain ⟨iri', subjectIs, spelling⟩ := subjectIri' _ subject.symm
        have same : iri' = iri := iri_ext spelling
        rw [same] at subjectIs
        exact el.apart iri none named ax member subjectIs
      | side q y blank _ =>
        rw [blank] at subject
        cases subject
    have st1Blanks : st1.blanks.val = [] := by simp [st1]
    have st1Sources : ∀ b ∈ st1.sources.val, b.val = [] := v2Empty
    have one : (1#usize : Usize).val = 1 := by simp
    obtain ⟨v, s', axiomsRun, vIs, blanksIs, allUsed⟩ := axioms_complete graph.triples kinds o.axioms.val supply []
      axiomPs taxioms readable supply (by simp) distinct 1#usize st1 (alloc.vec.Vec.new _)
      (by rw [one]; simp at length; omega)
      complete st1Sources (by rw [one]; exact holdsRest) st1Length
      (fun i hi => by
        rw [one] at hi
        have : i = 0 := by omega
        subst this
        exact st1Used0)
      (fun j hj => by
        rw [one, st1UsedRest (1 + j) (by omega)]
        exact st0Used (1 + j) (by simp at length; omega))
      (by rw [st1Blanks, one]; simp)
      (by have := o.axioms.property
          have z : (alloc.vec.Vec.new model.AnnotatedAxiom).val.length = 0 := by simp
          omega)
    have skip := axioms_from_skip graph.triples kinds st1 (alloc.vec.Vec.new _) 1#usize (by rw [one]; omega) 0#usize
      (by rw [z, one]; omega) (by
        intro i low high
        rw [one] at high
        have : i = 0 := by omega
        subst this
        rw [st1Used0]
        simp)
    have allRun := all_read_used graph.triples s'.used 0#usize (fun i _ hi => allUsed i hi)
    refine ⟨⟨⟨.Named ⟨iri0.spelling⟩ none, alloc.vec.Vec.new _, alloc.vec.Vec.new _, v⟩, s'.blanks⟩, ?_, ?_, ?_⟩
    · rw [rdf_mapping.map_graph]
      simp only [countRun, bind_ok, kindBucketsRun, kindsRun, unusedRun, bucketsRun, subjectsRun, sourcesRun,
        headerRun, alloc.vec.Vec.index_slice_index, main_lookup graph.triples 0#usize t0 (by rw [z]; exact at0),
        isIri0, take_correct]
      have partsRun' : rdf_mapping.header_parts graph.triples kinds iri0.spelling 0#usize
          { used := v1.set 0#usize true, blanks := alloc.vec.Vec.new rdf.BlankNode, subjects := v3, sources := v2 }
          none (alloc.vec.Vec.new model.Iri) (alloc.vec.Vec.new model.Annotation) =
          .ok (some (none, alloc.vec.Vec.new _, alloc.vec.Vec.new _, st1)) := partsRun
      rw [partsRun']
      simp only [bind_ok]
      change (Std.bind (rdf_mapping.iri_of iri0.spelling) _) = _
      rw [iri_of_identity, bind_ok]
      have axiomsRun' : rdf_mapping.axioms_from graph.triples kinds 0#usize st1
          (alloc.vec.Vec.new model.AnnotatedAxiom) = .ok (some (v, s')) := by rw [skip]; exact axiomsRun
      simp only [axiomsRun', bind_ok]
      change (Std.bind (rdf_mapping.all_read graph.triples s'.used 0#usize) _) = _
      rw [allRun, bind_ok]
      rfl
    · obtain ⟨identity, imports, annotations, axioms⟩ := o
      simp only at named el ⊢
      subst named
      have importsNil : imports.val = [] := el.imports
      have annotationsNil : annotations.val = [] := el.annotations
      simp only [model.RawOntology.mk.injEq, model.OntologyIdentity.Named.injEq, and_true]
      refine ⟨iri_ext spelled0, vec_eq_of_val (by simp [importsNil]), vec_eq_of_val (by simp [annotationsNil]),
        vec_eq_of_val (by simpa using vIs)⟩
    · rw [blanksIs, st1Blanks]
      simp

end Rowl.RdfMappingComplete
