import Rowl.RdfMapping
import Rowl.Builtins

/-!
# Complete indexes and exact lookups of the RDF mapping reader

The completeness proofs of `rdf_mapping::map_graph` (`RdfReadExpressions.lean`,
`RdfMappingComplete.lean`) rest on this module. It proves the indexes of the
reader complete: the subject index holds every triple with a blank subject in
the bucket of its node (`subjects_from_spec`), and the declaration index keeps
exactly the declarations of the graph (`declared_kinds_spec`, `declared_correct`,
`has_kind_correct`). Given the positions of all unused triples about a blank node
(`HeadsAt`), the lookups then find exactly those triples (`find_hit`,
`find_type_hit`, `find_any_hit`) and nothing else (`find_miss`, `find_type_miss`).
`Ready` bundles what a reader needs to read the patterns of a construct at their
positions, and `ready_middle` passes it on to the parts of a construct.
-/

namespace Rowl.RdfReadIndexes
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust Rowl.RdfMapping
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

theorem vec_eq_of_val {α : Type} {u v : alloc.vec.Vec α} (h : u.val = v.val) : u = v :=
  (alloc.vec.Vec.eq_iff u v).mpr h

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

theorem hash_subject_ok (subject : rdf.Subject) : ∃ h, rdf_mapping.hash_subject subject = .ok h := by
  cases subject with
  | Iri iri =>
    obtain ⟨h, run⟩ := hash_from_ok iri.spelling 0#usize 7#usize
    exact ⟨h, by simp [rdf_mapping.hash_subject, rdf_mapping.hash_iri, run]⟩
  | Blank node =>
    obtain ⟨h, run⟩ := hash_blank_ok node
    exact ⟨h, by simp [rdf_mapping.hash_subject, run]⟩

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

theorem position_usize {triples : alloc.vec.Vec rdf.Triple} {i : Nat} {t : rdf.Triple} (at_i : triples.val[i]? = some t) :
    i < 2 ^ UScalarTy.Usize.numBits := by
  have inside := (List.getElem?_eq_some_iff.mp at_i).1
  have bound : triples.val.length ≤ Usize.max := triples.property
  have positive : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.pow_pos (by decide)
  have : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
    simp only [Usize.max, Usize.numBits]
    omega
  omega

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

theorem record_ok (s : rdf_mapping.State) (node : rdf.BlankNode) (room : s.blanks.val.length < Usize.max) :
    ∃ s', rdf_mapping.record s node = .ok s' ∧ Marked s s' (fun _ => False) [node] := by
  obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec s.blanks node room)
  have run : rdf_mapping.record s node = .ok { s with blanks := pushed } := by
    rw [rdf_mapping.record, copy_blank_identity]
    simp [push]
  exact ⟨_, run, marked_record s _ node run⟩


/-! ### Lookups of any triple about a node -/

theorem fits_any_correct (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool) (index : Usize)
    (node : rdf.BlankNode) :
    rdf_mapping.fits_any triples used index node = .ok (decide (∃ t, Unused triples.val used.val index.val t ∧
      subjectView t.subject = .blank node)) := by
  rw [rdf_mapping.fits_any]
  by_cases more : index.val < triples.val.length
  · have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, about_correct]
    have at_t : triples.val[index.val]? = some triples.val[index.val] := List.getElem?_eq_getElem more
    by_cases isUsed : used.val[index.val]? = some false
    · simp only [isUsed, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq]
      rw [decide_eq_decide]
      constructor
      · intro here; exact ⟨_, ⟨at_t, isUsed⟩, here⟩
      · rintro ⟨t, ⟨at_i, -⟩, here⟩
        rw [at_t] at at_i
        cases at_i
        exact here
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

theorem find_any_in_total (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool)
    (bucket : alloc.vec.Vec Usize) (node : rdf.BlankNode) :
    ∀ (k : Usize), ∃ r, rdf_mapping.find_any_in triples used bucket node k = .ok r := by
  intro k
  induction e : bucket.val.length - k.val generalizing k with
  | zero =>
    have done : ¬ k.val < bucket.val.length := by omega
    exact ⟨none, by rw [rdf_mapping.find_any_in]; simp [UScalar.lt_equiv, done]⟩
  | succ n ih =>
    have more : k.val < bucket.val.length := by omega
    have lookup : bucket.index_usize k = .ok bucket.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = k.val + 1 := by simpa using nextValue
    obtain ⟨r, run⟩ := ih next (by omega)
    rw [rdf_mapping.find_any_in]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, fits_any_correct]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨r, by simp [advance, run]⟩

theorem find_any_total (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (node : rdf.BlankNode) :
    ∃ r, rdf_mapping.find_any triples s node = .ok r := by
  obtain ⟨h, hashRun⟩ := hash_blank_ok node
  obtain ⟨bucket, bucketRun, -⟩ := bucket_of_spec h (alloc.vec.Vec.len s.subjects)
  rw [rdf_mapping.find_any]
  simp only [hashRun, bucketRun, bind_ok]
  by_cases inside : bucket.val < s.subjects.val.length
  · have lookup : s.subjects.index_usize bucket = .ok s.subjects.val[bucket.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨r, run⟩ := find_any_in_total triples s.used s.subjects.val[bucket.val] node 0#usize
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, run]⟩
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]⟩

theorem find_any_in_none (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool)
    (bucket : alloc.vec.Vec Usize) (node : rdf.BlankNode) (k : Usize)
    (ran : rdf_mapping.find_any_in triples used bucket node k = .ok none) :
    ∀ (j : Nat) (pos : Usize), k.val ≤ j → bucket.val[j]? = some pos →
      ¬ ∃ t, Unused triples.val used.val pos.val t ∧ subjectView t.subject = .blank node := by
  rw [rdf_mapping.find_any_in] at ran
  by_cases more : k.val < bucket.val.length
  · have lookup : bucket.index_usize k = .ok bucket.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = k.val + 1 := by simpa using nextValue
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, fits_any_correct] at ran
    by_cases fit : ∃ t, Unused triples.val used.val bucket.val[k.val].val t ∧ subjectView t.subject = .blank node
    · simp [fit] at ran
    · simp only [fit, decide_false, Bool.false_eq_true, ↓reduceIte, advance, bind_ok] at ran
      intro j pos low at_j
      by_cases here : j = k.val
      · subst here
        rw [List.getElem?_eq_getElem more] at at_j
        cases at_j
        exact fit
      · exact find_any_in_none triples used bucket node next ran j pos (by omega) at_j
  · intro j pos low at_j
    have := (List.getElem?_eq_some_iff.mp at_j).1
    omega
termination_by bucket.val.length - k.val
decreasing_by all_goals (have := nextValue; simp at this; omega)

theorem find_any_none (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (node : rdf.BlankNode)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    (ran : rdf_mapping.find_any triples s node = .ok none) :
    ∀ (i : Nat) (t : rdf.Triple), Unused triples.val s.used.val i t → subjectView t.subject ≠ .blank node := by
  intro i t unused about
  rw [rdf_mapping.find_any] at ran
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
  exact find_any_in_none triples s.used _ node 0#usize ran j k (by simp) at_j ⟨t, by rw [kIs]; exact unused, about⟩

/-! ### Positions of patterns -/

/-- The triples at the positions `pos` instantiate the patterns `ps`, in order. -/
def At (triples : List rdf.Triple) (pos : List Nat) (ps : List Pattern) : Prop :=
  List.Forall₂ (fun i p => ∃ t, triples[i]? = some t ∧ Matches p t) pos ps

theorem at_length {triples : List rdf.Triple} {pos : List Nat} {ps : List Pattern} (h : At triples pos ps) :
    pos.length = ps.length := List.Forall₂.length_eq h

theorem at_append {triples : List rdf.Triple} {pos1 pos2 : List Nat} {ps1 ps2 : List Pattern}
    (h1 : At triples pos1 ps1) (h2 : At triples pos2 ps2) : At triples (pos1 ++ pos2) (ps1 ++ ps2) :=
  List.rel_append h1 h2

theorem at_split {triples : List rdf.Triple} {pos : List Nat} {ps qs : List Pattern} (h : At triples pos (ps ++ qs)) :
    ∃ pos1 pos2, pos = pos1 ++ pos2 ∧ At triples pos1 ps ∧ At triples pos2 qs := by
  induction ps generalizing pos with
  | nil => exact ⟨[], pos, rfl, List.Forall₂.nil, h⟩
  | cons p ps ih =>
    cases pos with
    | nil => cases h
    | cons i pos =>
      obtain ⟨hp, rest⟩ := List.forall₂_cons.mp h
      obtain ⟨pos1, pos2, eq, h1, h2⟩ := ih rest
      exact ⟨i :: pos1, pos2, by rw [eq]; rfl, List.Forall₂.cons hp h1, h2⟩

theorem at_append_inv {triples : List rdf.Triple} {pos1 pos2 : List Nat} {ps1 ps2 : List Pattern}
    (h : At triples (pos1 ++ pos2) (ps1 ++ ps2)) (len : pos1.length = ps1.length) :
    At triples pos1 ps1 ∧ At triples pos2 ps2 := by
  obtain ⟨q1, q2, eq, h1, h2⟩ := at_split h
  have l1 := at_length h1
  have : q1 = pos1 ∧ q2 = pos2 := by
    have := List.append_inj eq.symm (by rw [len, l1])
    exact ⟨this.1, this.2⟩
  obtain ⟨rfl, rfl⟩ := this
  exact ⟨h1, h2⟩

theorem at_mem {triples : List rdf.Triple} {pos : List Nat} {ps : List Pattern} (h : At triples pos ps)
    {i : Nat} (member : i ∈ pos) {t : rdf.Triple} (at_i : triples[i]? = some t) : ∃ p ∈ ps, Matches p t := by
  induction h with
  | nil => simp at member
  | @cons j p pos' ps' hp rest ih =>
    rcases List.mem_cons.mp member with here | inner
    · subst here
      obtain ⟨t', at', fits⟩ := hp
      rw [at_i] at at'
      cases at'
      exact ⟨p, List.mem_cons_self .., fits⟩
    · obtain ⟨q, mem, fits⟩ := ih inner
      exact ⟨q, List.mem_cons_of_mem _ mem, fits⟩

theorem at_get {triples : List rdf.Triple} {pos : List Nat} {ps : List Pattern} (h : At triples pos ps)
    {k : Nat} {i : Nat} (hi : pos[k]? = some i) :
    ∃ (hk : k < ps.length) (t : rdf.Triple), triples[i]? = some t ∧ Matches ps[k] t := by
  have kLt : k < pos.length := (List.getElem?_eq_some_iff.mp hi).1
  have len := at_length h
  have kLt' : k < ps.length := by omega
  have each := List.Forall₂.get h kLt kLt'
  simp only [List.get_eq_getElem] at each
  have posK : pos[k] = i := by
    rw [List.getElem?_eq_getElem kLt] at hi
    exact Option.some.inj hi
  rw [posK] at each
  exact ⟨kLt', each⟩

/-- The patterns of a blank node from its predicates and objects. -/
def headPatterns (x : rdf.BlankNode) (head : List (List U8 × Node)) : List Pattern :=
  head.map (fun e => ⟨.blank x, e.1, e.2⟩)

theorem head_patterns_length (x : rdf.BlankNode) (head : List (List U8 × Node)) :
    (headPatterns x head).length = head.length := by simp [headPatterns]

/-- The unused triples about `x` are at the positions `hpos`, which hold the
    triples of `head` about `x` in order, and the predicates of `head` differ. -/
structure HeadsAt (triples : List rdf.Triple) (used : List Bool) (x : rdf.BlankNode) (hpos : List Nat)
    (head : List (List U8 × Node)) : Prop where
  holds : At triples hpos (headPatterns x head)
  confined : ∀ (i : Nat) (t : rdf.Triple), triples[i]? = some t → used[i]? = some false →
    subjectView t.subject = .blank x → i ∈ hpos
  distinct : (head.map (·.1)).Nodup

theorem heads_at_key {triples : List rdf.Triple} {used : List Bool} {x : rdf.BlankNode} {hpos : List Nat}
    {head : List (List U8 × Node)} (heads : HeadsAt triples used x hpos head) {i : Nat} {t : rdf.Triple}
    (at_i : triples[i]? = some t) (unused : used[i]? = some false) (about : subjectView t.subject = .blank x) :
    ∃ (k : Nat) (h : k < head.length), hpos[k]? = some i ∧ t.predicate.spelling.val = head[k].1 ∧
      objectView t.object = head[k].2 := by
  have member := heads.confined i t at_i unused about
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨kLt, t', at', fits⟩ := at_get heads.holds hk
  rw [at_i] at at'
  cases at'
  have kLt' : k < head.length := by rw [head_patterns_length] at kLt; exact kLt
  refine ⟨k, kLt', hk, ?_, ?_⟩
  · have := fits.2.1
    simpa [headPatterns] using this
  · have := fits.2.2
    simpa [headPatterns] using this

theorem heads_at_mono {triples : List rdf.Triple} {used used' : List Bool} {x : rdf.BlankNode} {hpos : List Nat}
    {head : List (List U8 × Node)} (heads : HeadsAt triples used x hpos head)
    (back : ∀ i : Nat, used'[i]? = some false → used[i]? = some false) : HeadsAt triples used' x hpos head where
  holds := heads.holds
  confined := fun i t at_i unused about => heads.confined i t at_i (back i unused) about
  distinct := heads.distinct

theorem heads_at_triple {triples : List rdf.Triple} {used : List Bool} {x : rdf.BlankNode} {hpos : List Nat}
    {head : List (List U8 × Node)} (heads : HeadsAt triples used x hpos head) {k i : Nat} (hi : hpos[k]? = some i) :
    ∃ (hk : k < head.length) (t : rdf.Triple), triples[i]? = some t ∧ subjectView t.subject = .blank x ∧
      t.predicate.spelling.val = head[k].1 ∧ objectView t.object = head[k].2 := by
  obtain ⟨kLt, t, at_t, fits⟩ := at_get heads.holds hi
  have kLt' : k < head.length := by rw [head_patterns_length] at kLt; exact kLt
  refine ⟨kLt', t, at_t, ?_, ?_, ?_⟩
  · have := fits.1; simpa [headPatterns] using this
  · have := fits.2.1; simpa [headPatterns] using this
  · have := fits.2.2; simpa [headPatterns] using this

theorem usize_of_position {triples : alloc.vec.Vec rdf.Triple} {i : Nat} {t : rdf.Triple}
    (at_i : triples.val[i]? = some t) : ∃ u : Usize, u.val = i :=
  ⟨UScalar.ofNatCore i (position_usize at_i), UScalar.ofNatCore_val_eq _⟩

/-- A lookup of a head predicate finds its position, for every spelling of the predicate. -/
theorem find_hit (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (x : rdf.BlankNode)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {hpos : List Nat} {head : List (List U8 × Node)} (heads : HeadsAt triples.val s.used.val x hpos head)
    {k i : Nat} (hi : hpos[k]? = some i) (P : List U8) (named : ∀ hk : k < head.length, head[k].1 = P)
    (unused : s.used.val[i]? = some false) :
    ∃ found : Usize, found.val = i ∧
      ∀ key : Slice U8, key.val = P → rdf_mapping.find triples s x key = .ok (some found) := by
  obtain ⟨kLt, t, at_t, about, predicate, -⟩ := heads_at_triple heads hi
  obtain ⟨u, uVal⟩ := usize_of_position at_t
  refine ⟨u, uVal, fun key keyIs => ?_⟩
  obtain ⟨r, run⟩ := find_total triples s x key
  cases r with
  | none =>
    exact absurd (find_none triples s x key complete run i t ⟨at_t, unused⟩ about) (by
      rw [predicate, named kLt, keyIs]; simp)
  | some found =>
    obtain ⟨t', unused', about', named'⟩ := find_spec triples s x key found run
    obtain ⟨k', kLt', hk', predicate', -⟩ := heads_at_key heads unused'.1 unused'.2 about'
    have same : k' = k := by
      have keys : (head.map (·.1))[k']'(by simpa using kLt') = (head.map (·.1))[k]'(by simpa using kLt) := by
        simp only [List.getElem_map]
        rw [← predicate', named', keyIs, named kLt]
      exact (List.Nodup.getElem_inj_iff heads.distinct).mp keys
    subst same
    rw [hi] at hk'
    have value : found.val = i := (Option.some.inj hk').symm
    rw [run, show found = u from UScalar.eq_of_val_eq (by rw [value, uVal])]

/-- A lookup of a predicate that no head triple has finds nothing. -/
theorem find_miss (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (x : rdf.BlankNode)
    {hpos : List Nat} {head : List (List U8 × Node)} (heads : HeadsAt triples.val s.used.val x hpos head)
    (P : List U8) (absent : ∀ (k : Nat) (h : k < head.length), head[k].1 ≠ P) :
    ∀ key : Slice U8, key.val = P → rdf_mapping.find triples s x key = .ok none := by
  intro key keyIs
  obtain ⟨r, run⟩ := find_total triples s x key
  cases r with
  | none => exact run
  | some found =>
    obtain ⟨t', unused', about', named'⟩ := find_spec triples s x key found run
    obtain ⟨k', kLt', -, predicate', -⟩ := heads_at_key heads unused'.1 unused'.2 about'
    exact absurd (predicate'.symm.trans (named'.trans keyIs)) (absent k' kLt')

/-- A type lookup of a head type finds its position, for every spelling of the type. -/
theorem find_type_hit (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (x : rdf.BlankNode)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {hpos : List Nat} {head : List (List U8 × Node)} (heads : HeadsAt triples.val s.used.val x hpos head)
    {k i : Nat} (hi : hpos[k]? = some i) (T : List U8) (typed : ∀ hk : k < head.length, head[k] = (rdfType, .iri T))
    (unused : s.used.val[i]? = some false) :
    ∃ found : Usize, found.val = i ∧
      ∀ key : Slice U8, key.val = T → rdf_mapping.find_type triples s x key = .ok (some found) := by
  obtain ⟨kLt, t, at_t, about, predicate, object⟩ := heads_at_triple heads hi
  obtain ⟨u, uVal⟩ := usize_of_position at_t
  refine ⟨u, uVal, fun key keyIs => ?_⟩
  obtain ⟨r, run⟩ := find_type_total triples s x key
  cases r with
  | none =>
    exact absurd (find_type_none triples s x key complete run i t ⟨at_t, unused⟩ about
      (by rw [predicate, typed kLt])) (by rw [object, typed kLt, keyIs]; simp)
  | some found =>
    obtain ⟨t', unused', about', named', object'⟩ := find_type_spec triples s x key found run
    obtain ⟨k', kLt', hk', predicate', objectK'⟩ := heads_at_key heads unused'.1 unused'.2 about'
    have same : k' = k := by
      have keys : (head.map (·.1))[k']'(by simpa using kLt') = (head.map (·.1))[k]'(by simpa using kLt) := by
        simp only [List.getElem_map]
        rw [← predicate', named', typed kLt]
      exact (List.Nodup.getElem_inj_iff heads.distinct).mp keys
    subst same
    rw [hi] at hk'
    have value : found.val = i := (Option.some.inj hk').symm
    rw [run, show found = u from UScalar.eq_of_val_eq (by rw [value, uVal])]

/-- A type lookup for a type that no head triple gives finds nothing. -/
theorem find_type_miss (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (x : rdf.BlankNode)
    {hpos : List Nat} {head : List (List U8 × Node)} (heads : HeadsAt triples.val s.used.val x hpos head)
    (T : List U8) (absent : ∀ (k : Nat) (h : k < head.length), head[k] ≠ (rdfType, .iri T)) :
    ∀ key : Slice U8, key.val = T → rdf_mapping.find_type triples s x key = .ok none := by
  intro key keyIs
  obtain ⟨r, run⟩ := find_type_total triples s x key
  cases r with
  | none => exact run
  | some found =>
    obtain ⟨t', unused', about', named', object'⟩ := find_type_spec triples s x key found run
    obtain ⟨k', kLt', -, predicate', objectK'⟩ := heads_at_key heads unused'.1 unused'.2 about'
    exfalso
    apply absent k' kLt'
    apply Prod.ext
    · exact predicate'.symm.trans named'
    · rw [← objectK', object', keyIs]

/-- With one head triple, a lookup of any triple about the node finds it. -/
theorem find_any_hit (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (x : rdf.BlankNode)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {i : Nat} {e : List U8 × Node} (heads : HeadsAt triples.val s.used.val x [i] [e])
    (unused : s.used.val[i]? = some false) :
    ∃ found : Usize, found.val = i ∧ rdf_mapping.find_any triples s x = .ok (some found) := by
  obtain ⟨-, t, at_t, about, -, -⟩ := heads_at_triple heads (k := 0) (i := i) rfl
  obtain ⟨u, uVal⟩ := usize_of_position at_t
  refine ⟨u, uVal, ?_⟩
  obtain ⟨r, run⟩ := find_any_total triples s x
  cases r with
  | none => exact absurd about (find_any_none triples s x complete run i t ⟨at_t, unused⟩)
  | some found =>
    obtain ⟨t', unused', about'⟩ := find_any_spec triples s x found run
    have member := heads.confined _ t' unused'.1 unused'.2 about'
    simp only [List.mem_singleton] at member
    rw [run, show found = u from UScalar.eq_of_val_eq (by rw [member, uVal])]

/-! ### Reading a part of the patterns -/

/-- Every blank subject of the patterns is one of the nodes. -/
def BlankSubjects (nodes : List rdf.BlankNode) (ps : List Pattern) : Prop :=
  ∀ p ∈ ps, ∀ y, p.subject = .blank y → y ∈ nodes

theorem blank_subjects_append {nodes : List rdf.BlankNode} {ps qs : List Pattern} (h1 : BlankSubjects nodes ps)
    (h2 : BlankSubjects nodes qs) : BlankSubjects nodes (ps ++ qs) := by
  intro p member y subject
  rcases List.mem_append.mp member with left | right
  · exact h1 p left y subject
  · exact h2 p right y subject

theorem blank_subjects_mono {nodes nodes' : List rdf.BlankNode} {ps : List Pattern} (h : BlankSubjects nodes ps)
    (sub : ∀ y ∈ nodes, y ∈ nodes') : BlankSubjects nodes' ps :=
  fun p member y subject => sub y (h p member y subject)

theorem blank_subjects_head (x : rdf.BlankNode) (head : List (List U8 × Node)) :
    BlankSubjects [x] (headPatterns x head) := by
  intro p member y subject
  simp only [headPatterns, List.mem_map] at member
  obtain ⟨e, -, rfl⟩ := member
  simp only [Node.blank.injEq] at subject
  simp [subject]

/-- The state is ready to read the patterns `ps` at the positions `pos`, whose
    blank nodes are `fresh`: the subject index is complete, the positions are
    distinct and unused and hold the patterns, every unused triple about a node
    of `fresh` is at one of them, and the nodes can be recorded. -/
structure Ready (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (pos : List Nat) (ps : List Pattern)
    (fresh : List rdf.BlankNode) : Prop where
  complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length
  holds : At triples.val pos ps
  nodup : pos.Nodup
  free : ∀ i ∈ pos, s.used.val[i]? = some false
  owns : ∀ (i : Nat) (t : rdf.Triple) (y : rdf.BlankNode), triples.val[i]? = some t → s.used.val[i]? = some false →
    subjectView t.subject = .blank y → y ∈ fresh → i ∈ pos
  room : s.blanks.val.length + fresh.length ≤ Usize.max

/-- The middle part of the patterns is ready once the first part is read. -/
theorem ready_middle {triples : alloc.vec.Vec rdf.Triple} {s s' : rdf_mapping.State}
    {pos1 pos2 pos3 : List Nat} {ps1 ps2 ps3 : List Pattern} {f1 f2 f3 : List rdf.BlankNode}
    {m : Nat → Prop} {g : List rdf.BlankNode}
    (ready : Ready triples s (pos1 ++ pos2 ++ pos3) (ps1 ++ ps2 ++ ps3) (f1 ++ f2 ++ f3))
    (len1 : pos1.length = ps1.length) (len2 : pos2.length = ps2.length)
    (nodup : (f1 ++ f2 ++ f3).Nodup) (sub1 : BlankSubjects f1 ps1) (sub3 : BlankSubjects f3 ps3)
    (marked : Marked s s' m g) (inside : ∀ i, m i → i ∈ pos1) (recorded : g.length ≤ f1.length) :
    Ready triples s' pos2 ps2 f2 := by
  obtain ⟨at12, at3⟩ := at_append_inv ready.holds (by simp [len1, len2])
  obtain ⟨at1, at2⟩ := at_append_inv at12 len1
  have nodupPos := ready.nodup
  rw [List.nodup_append, List.nodup_append] at nodupPos
  have nodupF := nodup
  rw [List.nodup_append, List.nodup_append] at nodupF
  refine { complete := by rw [marked.subjects]; exact ready.complete
           holds := at2
           nodup := nodupPos.1.2.1
           free := ?_
           owns := ?_
           room := ?_ }
  · intro i member
    have before := ready.free i (by simp [member])
    exact marked_unused marked before (fun hm => nodupPos.1.2.2 i (inside i hm) i member rfl)
  · intro i t y at_i unused about member
    have before := marked_back marked unused
    have inAll := ready.owns i t y at_i before about (by simp [member])
    simp only [List.mem_append] at inAll
    rcases inAll with (in1 | in2) | in3
    · exfalso
      obtain ⟨p, pMem, fits⟩ := at_mem at1 in1 at_i
      have subject : p.subject = .blank y := fits.1.symm.trans about
      exact nodupF.1.2.2 y (sub1 p pMem y subject) y member rfl
    · exact in2
    · exfalso
      obtain ⟨p, pMem, fits⟩ := at_mem at3 in3 at_i
      have subject : p.subject = .blank y := fits.1.symm.trans about
      exact nodupF.2.2 y (by simp [member]) y (sub3 p pMem y subject) rfl
  · have room := ready.room
    rw [marked.blanks]
    simp only [List.length_append] at room ⊢
    omega

/-- The head triples of a node at the start of a part give `HeadsAt`. -/
theorem heads_of_ready {triples : alloc.vec.Vec rdf.Triple} {s : rdf_mapping.State} {hpos pos : List Nat}
    {x : rdf.BlankNode} {head : List (List U8 × Node)} {ps : List Pattern} {f : List rdf.BlankNode}
    (ready : Ready triples s (hpos ++ pos) (headPatterns x head ++ ps) (x :: f))
    (len : hpos.length = head.length) (sub : BlankSubjects f ps) (outside : x ∉ f)
    (distinct : (head.map (·.1)).Nodup) : HeadsAt triples.val s.used.val x hpos head := by
  obtain ⟨atH, atR⟩ := at_append_inv ready.holds (by rw [len, head_patterns_length])
  refine { holds := atH, confined := ?_, distinct := distinct }
  intro i t at_i unused about
  have inAll := ready.owns i t x at_i unused about (by simp)
  rcases List.mem_append.mp inAll with inH | inR
  · exact inH
  · exfalso
    obtain ⟨p, pMem, fits⟩ := at_mem atR inR at_i
    exact outside (sub p pMem x (fits.1.symm.trans about))

/-- Reading nothing. -/
theorem ready_nil_marked (s : rdf_mapping.State) : Marked s s (fun i => i ∈ ([] : List Nat)) [] :=
  marked_same (marked_refl s) (fun i => by simp)


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



theorem blank_subjects_of {nodes : List rdf.BlankNode} {ps : List Pattern} (h : SubjectsIn nodes ps) :
    BlankSubjects nodes ps := by
  intro p member y subject
  obtain ⟨z, inside, about⟩ := h p member
  rw [about] at subject
  cases subject
  exact inside

/-! ### How many blank nodes the forward mapping allocates -/

theorem list_of_length : ∀ (cells : List rdf.BlankNode) (elements : List Node), cells.length = elements.length →
    (listOf cells elements).2.length = 2 * cells.length
  | [], [], _ => by simp [listOf]
  | c :: cells, e :: elements, h => by
    have rest := list_of_length cells elements (by simpa using h)
    simp only [listOf, List.length_cons, rest]
    omega
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem tces_length : ∀ {cs : List model.ClassExpression} {s : Supply} {ns : List Node} {ps : List Pattern}
    {s' : Supply}, TCEs cs s ns ps s' → ns.length = cs.length
  | _, _, _, _, _, .nil _ => rfl
  | _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ _ tail => by simp [tces_length tail]

theorem tdrs_length : ∀ {ds : List model.DataRange} {s : Supply} {ns : List Node} {ps : List Pattern}
    {s' : Supply}, TDRs ds s ns ps s' → ns.length = ds.length
  | _, _, _, _, _, .nil _ => rfl
  | _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ _ tail => by simp [tdrs_length tail]

theorem tope_count {e : model.ObjectPropertyExpression} {s : Supply} {n : Node} {ps : List Pattern} {s' : Supply}
    (h : TOPE e s n ps s') : s.length ≤ s'.length + ps.length := by
  cases h <;> simp

theorem topes_count {es : List model.ObjectPropertyExpression} {s : Supply} {ns : List Node} {ps : List Pattern}
    {s' : Supply} (h : TOPEs es s ns ps s') : s.length ≤ s'.length + ps.length := by
  induction h with
  | nil => simp
  | cons e es s s1 s2 n ns ps qs head tail ih =>
    have := tope_count head
    simp only [List.length_append]
    omega

theorem tfacets_count {fs : List model.FacetRestriction} {s : Supply} {ns : List Node} {ps : List Pattern}
    {s' : Supply} (h : TFacets fs s ns ps s') : s.length ≤ s'.length + ps.length := by
  induction h with
  | nil => simp
  | cons => simp_all; omega

mutual
theorem tdr_count : ∀ {d : model.DataRange} {s : Supply} {n : Node} {ps : List Pattern} {s' : Supply},
    TDR d s n ps s' → s.length ≤ s'.length + ps.length
  | _, _, _, _, _, .datatype _ _ => by simp
  | _, _, _, _, _, .intersection _ x cells _ _ _ _ cellsLen inner => by
    have := tdrs_count inner
    have nodesLen := tdrs_length inner
    have lists := list_of_length cells _ (by rw [cellsLen, nodesLen])
    simp only [List.length_cons, List.length_append, lists]
    omega
  | _, _, _, _, _, .union _ x cells _ _ _ _ cellsLen inner => by
    have := tdrs_count inner
    have nodesLen := tdrs_length inner
    have lists := list_of_length cells _ (by rw [cellsLen, nodesLen])
    simp only [List.length_cons, List.length_append, lists]
    omega
  | _, _, _, _, _, .complement _ x _ _ _ _ inner => by
    have := tdr_count inner
    simp only [List.length_cons]
    omega
  | _, _, _, _, _, .oneOf _ x cells _ _ cellsLen literals => by
    have nodesLen := List.Forall₂.length_eq literals
    have lists := list_of_length cells _ (by rw [cellsLen, nodesLen])
    simp only [List.length_cons, List.length_append, lists]
    omega
  | _, _, _, _, _, .restriction _ _ x cells _ _ _ _ cellsLen facets => by
    have := tfacets_count facets
    have nodesLen := tfacets_length facets
    have lists := list_of_length cells _ (by rw [cellsLen, nodesLen])
    simp only [List.length_cons, List.length_append, lists]
    omega

theorem tdrs_count : ∀ {ds : List model.DataRange} {s : Supply} {ns : List Node} {ps : List Pattern} {s' : Supply},
    TDRs ds s ns ps s' → s.length ≤ s'.length + ps.length
  | _, _, _, _, _, .nil _ => by simp
  | _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ head tail => by
    have := tdr_count head
    have := tdrs_count tail
    simp only [List.length_append]
    omega
end

mutual
theorem tce_count : ∀ {c : model.ClassExpression} {s : Supply} {n : Node} {ps : List Pattern} {s' : Supply},
    TCE c s n ps s' → s.length ≤ s'.length + ps.length
  | _, _, _, _, _, .named _ _ => by simp
  | _, _, _, _, _, .intersection _ x cells _ _ _ _ cellsLen inner => by
    have := tces_count inner
    have nodesLen := tces_length inner
    have lists := list_of_length cells _ (by rw [cellsLen, nodesLen])
    simp only [List.length_cons, List.length_append, lists]
    omega
  | _, _, _, _, _, .union _ x cells _ _ _ _ cellsLen inner => by
    have := tces_count inner
    have nodesLen := tces_length inner
    have lists := list_of_length cells _ (by rw [cellsLen, nodesLen])
    simp only [List.length_cons, List.length_append, lists]
    omega
  | _, _, _, _, _, .complement _ x _ _ _ _ inner => by
    have := tce_count inner
    simp only [List.length_cons]
    omega
  | _, _, _, _, _, .oneOf xs x cells _ cellsLen => by
    have lists := list_of_length cells ((members1 xs).map individualNode) (by rw [cellsLen, List.length_map])
    simp only [List.length_cons, List.length_append, lists]
    omega
  | _, _, _, _, _, .some _ _ x _ _ _ _ _ _ _ role inner => by
    have := tope_count role
    have := tce_count inner
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .all _ _ x _ _ _ _ _ _ _ role inner => by
    have := tope_count role
    have := tce_count inner
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .hasValue _ _ x _ _ _ _ role => by
    have := tope_count role
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .hasSelf _ x _ _ _ _ role => by
    have := tope_count role
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .min _ _ x _ _ _ _ _ role _ => by
    have := tope_count role
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .max _ _ x _ _ _ _ _ role _ => by
    have := tope_count role
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .exact _ _ x _ _ _ _ _ role _ => by
    have := tope_count role
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .minQualified _ _ _ x _ _ _ _ _ _ _ _ role _ inner => by
    have := tope_count role
    have := tce_count inner
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .maxQualified _ _ _ x _ _ _ _ _ _ _ _ role _ inner => by
    have := tope_count role
    have := tce_count inner
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .exactQualified _ _ _ x _ _ _ _ _ _ _ _ role _ inner => by
    have := tope_count role
    have := tce_count inner
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .dataSome _ _ x _ _ _ _ inner => by
    have := tdr_count inner
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .dataAll _ _ x _ _ _ _ inner => by
    have := tdr_count inner
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .dataHasValue _ _ x _ _ _ => by
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .dataMin _ _ x _ _ _ => by
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .dataMax _ _ x _ _ _ => by
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .dataExact _ _ x _ _ _ => by
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .dataMinQualified _ _ _ x _ _ _ _ _ _ inner => by
    have := tdr_count inner
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .dataMaxQualified _ _ _ x _ _ _ _ _ _ inner => by
    have := tdr_count inner
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega
  | _, _, _, _, _, .dataExactQualified _ _ _ x _ _ _ _ _ _ inner => by
    have := tdr_count inner
    simp only [restrictionHead, List.length_cons, List.length_append, List.length_nil]
    omega

theorem tces_count : ∀ {cs : List model.ClassExpression} {s : Supply} {ns : List Node} {ps : List Pattern}
    {s' : Supply}, TCEs cs s ns ps s' → s.length ≤ s'.length + ps.length
  | _, _, _, _, _, .nil _ => by simp
  | _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ head tail => by
    have := tce_count head
    have := tces_count tail
    simp only [List.length_append]
    omega
end

end Rowl.RdfReadIndexes
