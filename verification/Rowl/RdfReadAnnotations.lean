import Rowl.RdfReadAxioms

/-!
# Reading the annotations of axioms and ontologies

The reverse RDF mapping reads the annotations of an axiom from the blank node
typed `owl:Axiom` that reifies its main triple, or from the blank node that
represents the axiom, and the annotations of an ontology from the triples about
its IRI (§2.2, §2.3). This module proves those readers complete for annotations
without annotations of their own:

* the source index lists every `owl:annotatedSource` triple
  (`sources_from_spec`) and the subject index lists the positions of each blank
  node in increasing order (`subjects_from_sorted`);
* `reifier` finds the reification of a triple that the graph has, when no other
  reifies the same triple (`reifier_found`), and nothing when none does
  (`reifier_absent`);
* `node_annotations` reads the annotations of a blank node in the order of
  their triples (`node_annotations_plain`), and `annotate` reads the annotations
  of the reification of an axiom (`reified_found`, `annotate_main`) or of the
  blank node that represents it (`annotate_node`).
-/

namespace Rowl.RdfReadAnnotations
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust Rowl.RdfMapping Rowl.RdfReadIndexes Rowl.RdfReadExpressions
  Rowl.RdfReadAxioms

attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-! ### The indexes -/

/-- The positions in every bucket increase. -/
def BucketsSorted (buckets : List (alloc.vec.Vec Usize)) : Prop :=
  ∀ b ∈ buckets, b.val.Pairwise (fun i j => i.val < j.val)

theorem subjects_from_sorted (triples : alloc.vec.Vec rdf.Triple) :
    ∀ (index : Usize) (buckets result : alloc.vec.Vec (alloc.vec.Vec Usize)),
      0 < buckets.val.length → (∀ b ∈ buckets.val, b.val.length ≤ index.val) →
      (∀ b ∈ buckets.val, ∀ k ∈ b.val, k.val < index.val) → BucketsSorted buckets.val →
      rdf_mapping.subjects_from triples index buckets = .ok result → BucketsSorted result.val := by
  intro index
  induction e : triples.val.length - index.val generalizing index with
  | zero =>
    intro buckets result _ _ _ sorted ran
    rw [rdf_mapping.subjects_from] at ran
    have done : ¬ index.val < triples.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    subst ran
    exact sorted
  | succ n ih =>
    intro buckets result positive small below sorted ran
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
        (fun b member k kIn => by have := below b member k kIn; omega) sorted ran
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
      have memberSet : ∀ b ∈ (buckets.set bucket pushed).val, b ∈ buckets.val ∨ b = pushed := by
        intro b member
        rw [alloc.vec.Vec.set_val_eq] at member
        obtain ⟨j, at_j⟩ := List.mem_iff_getElem?.mp member
        by_cases same : j = bucket.val
        · subst same
          rw [List.getElem?_set_self inside] at at_j
          exact Or.inr (Option.some.inj at_j).symm
        · rw [List.getElem?_set_ne (Ne.symm same)] at at_j
          exact Or.inl (List.mem_of_getElem? at_j)
      have oldBelow := below _ (List.getElem_mem inside)
      exact ih next (by omega) _ result (by rw [sameLength]; exact positive)
        (by
          intro b member
          rcases memberSet b member with old | rfl
          · have := small b old; omega
          · rw [contents]; simp; have := small _ (List.getElem_mem inside); omega)
        (by
          intro b member k kIn
          rcases memberSet b member with old | rfl
          · have := below b old k kIn; omega
          · rw [contents] at kIn
            rcases List.mem_append.mp kIn with old | new
            · have := oldBelow k old; omega
            · simp at new; rw [new]; omega)
        (by
          intro b member
          rcases memberSet b member with old | rfl
          · exact sorted b old
          · rw [contents]
            refine List.pairwise_append.mpr ⟨sorted _ (List.getElem_mem inside), by simp, ?_⟩
            intro i iIn j jIn
            simp at jIn
            rw [jIn]
            exact oldBelow i iIn)
        ran

/-- The bucket an object's source triples go to among `count` buckets. -/
def SourceBucketOf (object : rdf.Object) (count : Usize) (bucket : Usize) : Prop :=
  ∃ h, rdf_mapping.hash_object object = .ok h ∧ rdf_mapping.bucket_of h count = .ok bucket

/-- The source index of `triples`: every `owl:annotatedSource` triple of a blank
    node has its position in the bucket of its object. -/
def SourcesComplete (triples : List rdf.Triple) (sources : List (alloc.vec.Vec Usize)) (count : Usize)
    (below : Nat) : Prop :=
  ∀ (i : Nat) (t : rdf.Triple) (x : rdf.BlankNode) (bucket : Usize), i < below → triples[i]? = some t →
    t.subject = .Blank x → t.predicate.spelling.val = owlAnnotatedSource → SourceBucketOf t.object count bucket →
    ∃ b, sources[bucket.val]? = some b ∧ ∃ k ∈ b.val, k.val = i

theorem hash_object_ok (object : rdf.Object) : ∃ h, rdf_mapping.hash_object object = .ok h := by
  cases object with
  | Iri iri =>
    obtain ⟨h, run⟩ := hash_from_ok iri.spelling 0#usize 7#usize
    exact ⟨h, by simp [rdf_mapping.hash_object, rdf_mapping.hash_iri, run]⟩
  | Blank node =>
    obtain ⟨h, run⟩ := hash_blank_ok node
    exact ⟨h, by simp [rdf_mapping.hash_object, run]⟩
  | Literal literal =>
    obtain ⟨h, run⟩ := hash_from_ok literal.lexical 0#usize 7#usize
    exact ⟨h, by simp [rdf_mapping.hash_object, rdf_mapping.hash_iri, run]⟩

/-- An object hashes as the subject that is the same node. -/
theorem hash_object_subject (object : rdf.Object) (subject : rdf.Subject)
    (same : objectView object = subjectView subject) :
    rdf_mapping.hash_object object = rdf_mapping.hash_subject subject := by
  cases subject with
  | Iri iri =>
    cases object with
    | Iri iri' =>
      simp only [objectView, subjectView, Node.iri.injEq] at same
      have : iri'.spelling = iri.spelling := vec_eq_of_val same
      simp [rdf_mapping.hash_object, rdf_mapping.hash_subject, this]
    | Blank _ => simp [objectView, subjectView] at same
    | Literal _ => simp [objectView, subjectView] at same
  | Blank node =>
    cases object with
    | Iri _ => simp [objectView, subjectView] at same
    | Blank node' =>
      simp only [objectView, subjectView, Node.blank.injEq] at same
      simp [rdf_mapping.hash_object, rdf_mapping.hash_subject, same]
    | Literal _ => simp [objectView, subjectView] at same

theorem is_source_correct (t : rdf.Triple) :
    rdf_mapping.is_source t = .ok (decide ((∃ x, t.subject = .Blank x) ∧
      t.predicate.spelling.val = owlAnnotatedSource)) := by
  rw [rdf_mapping.is_source]
  cases subject : t.subject with
  | Iri _ => simp
  | Blank x =>
    simp only [lift, bind_ok, same_correct, array_slice_val]
    by_cases named : t.predicate.spelling.val = owlAnnotatedSource
    · have named' := named
      simp only [owlAnnotatedSource] at named'
      simp [named', owlAnnotatedSource]
    · have named' := named
      simp only [owlAnnotatedSource] at named'
      simp [named', named]

theorem sources_from_total (triples : alloc.vec.Vec rdf.Triple) :
    ∀ (index : Usize) (buckets : alloc.vec.Vec (alloc.vec.Vec Usize)),
      ∃ r, rdf_mapping.sources_from triples index buckets = .ok r := by
  intro index
  induction e : triples.val.length - index.val generalizing index with
  | zero =>
    intro buckets
    have done : ¬ index.val < triples.val.length := by omega
    exact ⟨buckets, by rw [rdf_mapping.sources_from]; simp [UScalar.lt_equiv, done]⟩
  | succ n ih =>
    intro buckets
    have more : index.val < triples.val.length := by omega
    have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    rw [rdf_mapping.sources_from]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup, bind_ok, is_source_correct]
    by_cases source : (∃ x, triples.val[index.val].subject = .Blank x) ∧
        triples.val[index.val].predicate.spelling.val = owlAnnotatedSource
    · obtain ⟨h, hashRun⟩ := hash_object_ok triples.val[index.val].object
      obtain ⟨bucket, bucketRun, -⟩ := bucket_of_spec h (alloc.vec.Vec.len buckets)
      simp only [source, decide_true, ↓reduceIte, hashRun, bucketRun, bind_ok]
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
    · obtain ⟨r, run⟩ := ih next (by omega) buckets
      exact ⟨r, by simp [source, advance, run]⟩

theorem sources_from_spec (triples : alloc.vec.Vec rdf.Triple) :
    ∀ (index : Usize) (buckets result : alloc.vec.Vec (alloc.vec.Vec Usize)),
      0 < buckets.val.length → (∀ b ∈ buckets.val, b.val.length ≤ index.val) →
      SourcesComplete triples.val buckets.val (alloc.vec.Vec.len buckets) index.val →
      rdf_mapping.sources_from triples index buckets = .ok result →
      result.val.length = buckets.val.length ∧
        SourcesComplete triples.val result.val (alloc.vec.Vec.len buckets) triples.val.length := by
  intro index
  induction e : triples.val.length - index.val generalizing index with
  | zero =>
    intro buckets result positive small complete ran
    rw [rdf_mapping.sources_from] at ran
    have done : ¬ index.val < triples.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    subst ran
    refine ⟨rfl, fun i t x bucket inside at_i blank named which => ?_⟩
    exact complete i t x bucket (by have := (List.getElem?_eq_some_iff.mp at_i).1; omega) at_i blank named which
  | succ n ih =>
    intro buckets result positive small complete ran
    rw [rdf_mapping.sources_from] at ran
    have more : index.val < triples.val.length := by omega
    have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup, bind_ok, is_source_correct] at ran
    by_cases source : (∃ x, triples.val[index.val].subject = .Blank x) ∧
        triples.val[index.val].predicate.spelling.val = owlAnnotatedSource
    · obtain ⟨h, hashRun⟩ := hash_object_ok triples.val[index.val].object
      obtain ⟨bucket, bucketRun, bucketLt⟩ := bucket_of_spec h (alloc.vec.Vec.len buckets)
      simp only [source, decide_true, ↓reduceIte, hashRun, bucketRun, bind_ok] at ran
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
          intro i t x' bucket' below at_i blank named which
          by_cases here : i = index.val
          · subst here
            rw [List.getElem?_eq_getElem more] at at_i
            cases at_i
            obtain ⟨h', hashRun', bucketRun'⟩ := which
            rw [hashRun] at hashRun'
            cases Result.ok_injective hashRun'
            rw [bucketRun] at bucketRun'
            cases Result.ok_injective bucketRun'
            refine ⟨pushed, by simp [alloc.vec.Vec.set_val_eq, List.getElem?_set_self inside], index, ?_, rfl⟩
            rw [contents]
            simp
          · obtain ⟨b, at_b, k, member, kIs⟩ := complete i t x' bucket' (by omega) at_i blank named which
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
    · simp only [source, decide_false, Bool.false_eq_true, ↓reduceIte, advance, bind_ok] at ran
      obtain ⟨length, done⟩ := ih next (by omega) buckets result positive
        (fun b member => by have := small b member; omega)
        (by
          intro i t x' bucket' below at_i blank named which
          by_cases here : i = index.val
          · subst here
            rw [List.getElem?_eq_getElem more] at at_i
            cases at_i
            exact absurd ⟨⟨x', blank⟩, named⟩ source
          · exact complete i t x' bucket' (by omega) at_i blank named which)
        ran
      exact ⟨length, done⟩

/-! ### Lookups of unique triples -/

/-- A lookup finds the only unused triple about a node with a predicate, for
    every spelling of the predicate. -/
theorem find_unique (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (x : rdf.BlankNode)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {i : Nat} {t : rdf.Triple} (at_i : triples.val[i]? = some t) (unused : s.used.val[i]? = some false)
    (about : subjectView t.subject = .blank x) (P : List U8) (named : t.predicate.spelling.val = P)
    (alone : ∀ (j : Nat) (u : rdf.Triple), triples.val[j]? = some u → s.used.val[j]? = some false →
      subjectView u.subject = .blank x → u.predicate.spelling.val = P → j = i) :
    ∃ found : Usize, found.val = i ∧
      ∀ key : Slice U8, key.val = P → rdf_mapping.find triples s x key = .ok (some found) := by
  obtain ⟨w, wVal⟩ := usize_of_position at_i
  refine ⟨w, wVal, fun key keyIs => ?_⟩
  obtain ⟨r, run⟩ := find_total triples s x key
  cases r with
  | none =>
    exact absurd (named.trans keyIs.symm) (find_none triples s x key complete run i t ⟨at_i, unused⟩ about)
  | some found =>
    obtain ⟨u, unused', about', named'⟩ := find_spec triples s x key found run
    have value := alone found.val u unused'.1 unused'.2 about' (named'.trans keyIs)
    rw [run, show found = w from UScalar.eq_of_val_eq (by rw [value, wVal])]

/-- A type lookup finds the only unused triple typing a node with a type, for
    every spelling of the type. -/
theorem find_type_unique (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (x : rdf.BlankNode)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {i : Nat} {t : rdf.Triple} (at_i : triples.val[i]? = some t) (unused : s.used.val[i]? = some false)
    (about : subjectView t.subject = .blank x) (typed : t.predicate.spelling.val = rdfType) (T : List U8)
    (object : objectView t.object = .iri T)
    (alone : ∀ (j : Nat) (u : rdf.Triple), triples.val[j]? = some u → s.used.val[j]? = some false →
      subjectView u.subject = .blank x → u.predicate.spelling.val = rdfType → objectView u.object = .iri T →
      j = i) :
    ∃ found : Usize, found.val = i ∧
      ∀ key : Slice U8, key.val = T → rdf_mapping.find_type triples s x key = .ok (some found) := by
  obtain ⟨w, wVal⟩ := usize_of_position at_i
  refine ⟨w, wVal, fun key keyIs => ?_⟩
  obtain ⟨r, run⟩ := find_type_total triples s x key
  cases r with
  | none =>
    exact absurd (by rw [object, keyIs]) (find_type_none triples s x key complete run i t ⟨at_i, unused⟩ about typed)
  | some found =>
    obtain ⟨u, unused', about', named', object'⟩ := find_type_spec triples s x key found run
    have value := alone found.val u unused'.1 unused'.2 about' named' (by rw [object', keyIs])
    rw [run, show found = w from UScalar.eq_of_val_eq (by rw [value, wVal])]

/-! ### The first annotation triple of a blank node -/

theorem is_annotation_true {kinds : rdf_mapping.Kinds} {spelling : alloc.vec.Vec U8}
    (kind : rdf_mapping.property_kind kinds spelling = .ok (some .Annotation)) :
    rdf_mapping.is_annotation kinds spelling = .ok true := by
  rw [rdf_mapping.is_annotation]; simp [kind]

theorem is_annotation_false {kinds : rdf_mapping.Kinds} {spelling : alloc.vec.Vec U8} {r : Option rdf_mapping.PropertyKind}
    (kind : rdf_mapping.property_kind kinds spelling = .ok r) (other : r ≠ some .Annotation) :
    rdf_mapping.is_annotation kinds spelling = .ok false := by
  rw [rdf_mapping.is_annotation]
  rcases r with _ | k
  · simp [kind]
  · cases k with
    | Object => simp [kind]
    | Data => simp [kind]
    | Annotation => exact absurd rfl other

/-- An unused annotation triple about the node fits. -/
theorem fits_annotation_true (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (used : alloc.vec.Vec Bool) (index : Usize) (node : rdf.BlankNode) {t : rdf.Triple}
    (at_t : triples.val[index.val]? = some t) (unused : used.val[index.val]? = some false)
    (about : subjectView t.subject = .blank node)
    (kind : rdf_mapping.property_kind kinds t.predicate.spelling = .ok (some .Annotation)) :
    rdf_mapping.fits_annotation triples kinds used index node = .ok true := by
  have inside : index.val < triples.val.length := (List.getElem?_eq_some_iff.mp at_t).1
  rw [rdf_mapping.fits_annotation]
  simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, is_used_correct, unused, main_lookup triples index t at_t,
    about_correct, about, is_annotation_true kind]

/-- A triple that is used, about another node or not an annotation does not fit. -/
theorem fits_annotation_false (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (used : alloc.vec.Vec Bool) (index : Usize) (node : rdf.BlankNode)
    (other : ∀ t, triples.val[index.val]? = some t → used.val[index.val]? = some false →
      subjectView t.subject = .blank node →
      ∃ r, rdf_mapping.property_kind kinds t.predicate.spelling = .ok r ∧ r ≠ some .Annotation) :
    rdf_mapping.fits_annotation triples kinds used index node = .ok false := by
  rw [rdf_mapping.fits_annotation]
  by_cases inside : index.val < triples.val.length
  · have at_t : triples.val[index.val]? = some triples.val[index.val] := List.getElem?_eq_getElem inside
    by_cases unused : used.val[index.val]? = some false
    · by_cases about : subjectView triples.val[index.val].subject = .blank node
      · obtain ⟨r, kind, notAnnotation⟩ := other _ at_t unused about
        simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, is_used_correct, unused,
          main_lookup triples index _ at_t, about_correct, about, is_annotation_false kind notAnnotation]
      · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, is_used_correct, unused,
          main_lookup triples index _ at_t, about_correct, about]
    · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, is_used_correct, unused]
  · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]

theorem find_annotation_in_first (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (used : alloc.vec.Vec Bool) (bucket : alloc.vec.Vec Usize) (node : rdf.BlankNode) (m : Nat) (e : Usize)
    (at_m : bucket.val[m]? = some e) (fit : rdf_mapping.fits_annotation triples kinds used e node = .ok true)
    (before : ∀ (m' : Nat) (e' : Usize), m' < m → bucket.val[m']? = some e' →
      rdf_mapping.fits_annotation triples kinds used e' node = .ok false) :
    ∀ (k : Usize), k.val ≤ m → rdf_mapping.find_annotation_in triples kinds used bucket node k = .ok (some e) := by
  intro k
  induction d : m - k.val generalizing k with
  | zero =>
    intro le
    have same : k.val = m := by omega
    have more : k.val < bucket.val.length := by rw [same]; exact (List.getElem?_eq_some_iff.mp at_m).1
    have lookup : bucket.index_usize k = .ok e := by
      simp [alloc.vec.Vec.index_usize, same, at_m]
    rw [rdf_mapping.find_annotation_in]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, fit]
  | succ n ih =>
    intro le
    have lt : k.val < m := by omega
    have mLt : m < bucket.val.length := (List.getElem?_eq_some_iff.mp at_m).1
    have more : k.val < bucket.val.length := by omega
    have lookup : bucket.index_usize k = .ok bucket.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have notFit := before k.val bucket.val[k.val] lt (List.getElem?_eq_getElem more)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := k) (y := 1#usize) (by have := bucket.property; scalar_tac))
    have nextIs : next.val = k.val + 1 := by simpa using nextValue
    rw [rdf_mapping.find_annotation_in]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
      bind_ok, notFit, Bool.false_eq_true, advance]
    exact ih next (by omega) (by omega)

/-- With a complete and sorted subject index, the first annotation lookup of a
    node finds its unused annotation triple at the least position. -/
theorem find_annotation_first (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (s : rdf_mapping.State) (node : rdf.BlankNode)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    (sorted : BucketsSorted s.subjects.val) {i : Nat} {t : rdf.Triple} (at_i : triples.val[i]? = some t)
    (unused : s.used.val[i]? = some false) (about : subjectView t.subject = .blank node)
    (kind : rdf_mapping.property_kind kinds t.predicate.spelling = .ok (some .Annotation))
    (least : ∀ (j : Nat) (u : rdf.Triple), j < i → triples.val[j]? = some u → s.used.val[j]? = some false →
      subjectView u.subject = .blank node →
      ∃ r, rdf_mapping.property_kind kinds u.predicate.spelling = .ok r ∧ r ≠ some .Annotation) :
    ∃ found : Usize, found.val = i ∧ rdf_mapping.find_annotation triples kinds s node = .ok (some found) := by
  have blank : t.subject = .Blank node := subject_blank about
  obtain ⟨h, hashRun⟩ := hash_blank_ok node
  obtain ⟨bucket, bucketRun, -⟩ := bucket_of_spec h (alloc.vec.Vec.len s.subjects)
  obtain ⟨b, at_b, e, member, eIs⟩ := complete i t node bucket (List.getElem?_eq_some_iff.mp at_i).1 at_i blank
    ⟨h, hashRun, bucketRun⟩
  have inside : bucket.val < s.subjects.val.length := (List.getElem?_eq_some_iff.mp at_b).1
  have lookup : s.subjects.index_usize bucket = .ok b := by
    simp [alloc.vec.Vec.index_usize, at_b]
  obtain ⟨m, at_m⟩ := List.mem_iff_getElem?.mp member
  have sortedB : b.val.Pairwise (fun i j => i.val < j.val) := sorted b (List.mem_of_getElem? at_b)
  have fit : rdf_mapping.fits_annotation triples kinds s.used e node = .ok true :=
    fits_annotation_true triples kinds s.used e node (by rw [eIs]; exact at_i) (by rw [eIs]; exact unused)
      about kind
  have before : ∀ (m' : Nat) (e' : Usize), m' < m → b.val[m']? = some e' →
      rdf_mapping.fits_annotation triples kinds s.used e' node = .ok false := by
    intro m' e' lt at_m'
    have smaller : e'.val < e.val := by
      have mLt : m < b.val.length := (List.getElem?_eq_some_iff.mp at_m).1
      have m'Lt : m' < b.val.length := by omega
      have pair := List.pairwise_iff_getElem.mp sortedB m' m m'Lt mLt lt
      rw [List.getElem?_eq_getElem m'Lt] at at_m'
      rw [List.getElem?_eq_getElem mLt] at at_m
      rw [Option.some.inj at_m', Option.some.inj at_m] at pair
      exact pair
    apply fits_annotation_false
    intro u at_u unusedU aboutU
    exact least e'.val u (by omega) at_u unusedU aboutU
  refine ⟨e, eIs, ?_⟩
  rw [rdf_mapping.find_annotation]
  simp only [hashRun, bucketRun, bind_ok, alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte,
    alloc.vec.Vec.index_slice_index, lookup]
  exact find_annotation_in_first triples kinds s.used b node m e at_m fit before 0#usize (by simp)

/-! ### Finding a reification -/

theorem object_view_injective {a b : rdf.Object} (same : objectView a = objectView b) : a = b := by
  cases a with
  | Iri i =>
    cases b with
    | Iri j =>
      simp only [objectView, Node.iri.injEq] at same
      obtain ⟨i⟩ := i
      obtain ⟨j⟩ := j
      simp only at same
      rw [vec_eq_of_val same]
    | Blank _ => simp [objectView] at same
    | Literal _ => simp [objectView] at same
  | Blank x =>
    cases b with
    | Iri _ => simp [objectView] at same
    | Blank y => simp only [objectView, Node.blank.injEq] at same; rw [same]
    | Literal _ => simp [objectView] at same
  | Literal l =>
    cases b with
    | Iri _ => simp [objectView] at same
    | Blank _ => simp [objectView] at same
    | Literal m =>
      simp only [objectView, Node.literal.injEq] at same
      obtain ⟨lexical, kind⟩ := l
      obtain ⟨lexical', kind'⟩ := m
      cases kind with
      | Datatype d =>
        cases kind' with
        | Datatype d' =>
          simp only [literalView, LiteralView.typed.injEq] at same
          obtain ⟨d⟩ := d
          obtain ⟨d'⟩ := d'
          obtain ⟨h1, h2⟩ := same
          simp only at h2
          rw [vec_eq_of_val h1, vec_eq_of_val h2]
        | Language _ => simp [literalView] at same
      | Language tag =>
        cases kind' with
        | Datatype _ => simp [literalView] at same
        | Language tag' =>
          simp only [literalView, LiteralView.tagged.injEq] at same
          obtain ⟨h1, h2⟩ := same
          rw [vec_eq_of_val h1, vec_eq_of_val h2]

theorem bind_total {α β : Type} {x : Result α} {f : α → Result β} {P : α → Prop}
    (hx : ∃ a, x = .ok a ∧ P a) (hf : ∀ a, P a → ∃ b, f a = .ok b) : ∃ b, (x >>= f) = .ok b := by
  obtain ⟨a, rfl, pa⟩ := hx
  obtain ⟨b, hb⟩ := hf a pa
  exact ⟨b, by simp [bind_ok, hb]⟩

theorem find_total_in (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (node : rdf.BlankNode)
    (key : Slice U8) :
    ∃ r, rdf_mapping.find triples s node key = .ok r ∧ ∀ f, r = some f → f.val < triples.val.length := by
  obtain ⟨r, run⟩ := find_total triples s node key
  refine ⟨r, run, fun f isSome => ?_⟩
  subst isSome
  obtain ⟨t, unused, -, -⟩ := find_spec triples s node key f run
  exact (List.getElem?_eq_some_iff.mp unused.1).1

theorem reifier_parts_total (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (node : rdf.BlankNode)
    (main : rdf.Triple) (kind : Slice U8) : ∃ r, rdf_mapping.reifier_parts triples s node main kind = .ok r := by
  rw [rdf_mapping.reifier_parts]
  simp only [lift, bind_ok]
  apply bind_total (find_total_in triples s node _)
  intro o inRange
  cases o with
  | none => exact ⟨_, rfl⟩
  | some property =>
    have insideP := inRange property rfl
    have at_p : triples.val[property.val]? = some triples.val[property.val] := List.getElem?_eq_getElem insideP
    simp only [alloc.vec.Vec.index_slice_index, main_lookup triples property _ at_p, bind_ok, object_spells_correct]
    split
    · apply bind_total (find_total_in triples s node _)
      intro o1 inRange1
      cases o1 with
      | none => exact ⟨_, rfl⟩
      | some target =>
        have insideT := inRange1 target rfl
        have at_t : triples.val[target.val]? = some triples.val[target.val] := List.getElem?_eq_getElem insideT
        simp only [alloc.vec.Vec.index_slice_index, main_lookup triples target _ at_t, bind_ok, same_object_correct]
        split
        · obtain ⟨o2, run2⟩ := find_type_total triples s node kind
          simp only [run2, bind_ok]
          cases o2 <;> exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem reifier_source_total (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (main : rdf.Triple)
    (kind : Slice U8) (source : Usize) (triple : rdf.Triple) :
    ∃ r, rdf_mapping.reifier_source triples s main kind source triple = .ok r := by
  rw [rdf_mapping.reifier_source.eq_def]
  cases subject : triple.subject with
  | Iri _ => exact ⟨none, by simp⟩
  | Blank node =>
    simp only [lift, bind_ok, same_correct, subject_is_correct]
    split
    · split
      · obtain ⟨r, run⟩ := reifier_parts_total triples s node main kind
        simp only [run, bind_ok]
        cases r <;> exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem reifier_at_total (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (main : rdf.Triple)
    (kind : Slice U8) (source : Usize) : ∃ r, rdf_mapping.reifier_at triples s main kind source = .ok r := by
  rw [rdf_mapping.reifier_at]
  by_cases more : source.val < triples.val.length
  · have at_s : triples.val[source.val]? = some triples.val[source.val] := List.getElem?_eq_getElem more
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok]
    split
    · exact ⟨_, rfl⟩
    · simp only [alloc.vec.Vec.index_slice_index, main_lookup triples source _ at_s, bind_ok]
      exact reifier_source_total triples s main kind source _
  · exact ⟨none, by simp [UScalar.lt_equiv, more]⟩

/-- The scan of a bucket finds the reification at its entry `m` when every
    reification it may meet before is that one. -/
theorem reifier_in_hit (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (main : rdf.Triple)
    (kind : Slice U8) (bucket : alloc.vec.Vec Usize) (m : Nat) (e : Usize) (at_m : bucket.val[m]? = some e)
    (found : Usize × Usize × Usize × Usize)
    (hit : rdf_mapping.reifier_at triples s main kind e = .ok (some found))
    (same : ∀ f x, ReifierOk triples.val s.used.val main kind.val f x → f = found) :
    ∀ (k : Usize), k.val ≤ m → rdf_mapping.reifier_in triples s main kind bucket k = .ok (some found) := by
  intro k
  induction d : m - k.val generalizing k with
  | zero =>
    intro le
    have kIs : k.val = m := by omega
    have more : k.val < bucket.val.length := by rw [kIs]; exact (List.getElem?_eq_some_iff.mp at_m).1
    have lookup : bucket.index_usize k = .ok e := by
      simp [alloc.vec.Vec.index_usize, kIs, at_m]
    rw [rdf_mapping.reifier_in]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, hit]
  | succ n ih =>
    intro le
    have mLt : m < bucket.val.length := (List.getElem?_eq_some_iff.mp at_m).1
    have more : k.val < bucket.val.length := by omega
    have lookup : bucket.index_usize k = .ok bucket.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := k) (y := 1#usize) (by have := bucket.property; scalar_tac))
    have nextIs : next.val = k.val + 1 := by simpa using nextValue
    obtain ⟨r, atRun⟩ := reifier_at_total triples s main kind bucket.val[k.val]
    rw [rdf_mapping.reifier_in]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
      bind_ok, atRun]
    cases r with
    | none =>
      simp only [advance, bind_ok]
      exact ih next (by omega) (by omega)
    | some f =>
      obtain ⟨x, okF⟩ := reifier_at_spec triples s main kind _ f atRun
      rw [same f x okF]

/-- The scan of a bucket finds nothing when no reification fits. -/
theorem reifier_in_absent (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (main : rdf.Triple)
    (kind : Slice U8) (bucket : alloc.vec.Vec Usize)
    (absent : ∀ f x, ¬ ReifierOk triples.val s.used.val main kind.val f x) :
    ∀ (k : Usize), rdf_mapping.reifier_in triples s main kind bucket k = .ok none := by
  intro k
  induction d : bucket.val.length - k.val generalizing k with
  | zero =>
    have done : ¬ k.val < bucket.val.length := by omega
    rw [rdf_mapping.reifier_in]; simp [UScalar.lt_equiv, done]
  | succ n ih =>
    have more : k.val < bucket.val.length := by omega
    have lookup : bucket.index_usize k = .ok bucket.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := k) (y := 1#usize) (by have := bucket.property; scalar_tac))
    have nextIs : next.val = k.val + 1 := by simpa using nextValue
    obtain ⟨r, atRun⟩ := reifier_at_total triples s main kind bucket.val[k.val]
    rw [rdf_mapping.reifier_in]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
      bind_ok, atRun]
    cases r with
    | none =>
      simp only [advance, bind_ok]
      exact ih next (by omega)
    | some f =>
      obtain ⟨x, okF⟩ := reifier_at_spec triples s main kind _ f atRun
      exact absurd okF (absent f x)

/-- No reification is found when no blank node reifies the triple. -/
theorem reifier_absent (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (main : rdf.Triple)
    (kind : Slice U8) (absent : ∀ f x, ¬ ReifierOk triples.val s.used.val main kind.val f x) :
    rdf_mapping.reifier triples s main kind = .ok none := by
  obtain ⟨h, hashRun⟩ := hash_subject_ok main.subject
  obtain ⟨bucket, bucketRun, -⟩ := bucket_of_spec h (alloc.vec.Vec.len s.sources)
  rw [rdf_mapping.reifier]
  simp only [hashRun, bucketRun, bind_ok]
  by_cases inside : bucket.val < s.sources.val.length
  · have lookup : s.sources.index_usize bucket = .ok s.sources.val[bucket.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup, bind_ok]
    exact reifier_in_absent triples s main kind _ absent 0#usize
  · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]

/-- The reifier finds the reification of a triple that the source index lists,
    when no other reifies the same triple and the reification node has one
    `owl:annotatedProperty`, one `owl:annotatedTarget` and one typing triple. -/
theorem reifier_found (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (main : rdf.Triple)
    (kind : Slice U8)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    (sources : SourcesComplete triples.val s.sources.val (alloc.vec.Vec.len s.sources) triples.val.length)
    (found : Usize × Usize × Usize × Usize) (x : rdf.BlankNode)
    (ok : ReifierOk triples.val s.used.val main kind.val found x)
    (aloneP : ∀ (j : Nat) (u : rdf.Triple), triples.val[j]? = some u → s.used.val[j]? = some false →
      subjectView u.subject = .blank x → u.predicate.spelling.val = owlAnnotatedProperty → j = found.2.1.val)
    (aloneT : ∀ (j : Nat) (u : rdf.Triple), triples.val[j]? = some u → s.used.val[j]? = some false →
      subjectView u.subject = .blank x → u.predicate.spelling.val = owlAnnotatedTarget → j = found.2.2.1.val)
    (aloneY : ∀ (j : Nat) (u : rdf.Triple), triples.val[j]? = some u → s.used.val[j]? = some false →
      subjectView u.subject = .blank x → u.predicate.spelling.val = rdfType → objectView u.object = .iri kind.val →
      j = found.2.2.2.val)
    (same : ∀ f x', ReifierOk triples.val s.used.val main kind.val f x' → f = found) :
    rdf_mapping.reifier triples s main kind = .ok (some found) := by
  obtain ⟨source, property, target, typing⟩ := found
  obtain ⟨ts, tp, tt, ty, unusedS, unusedP, unusedT, unusedY, subjectS, fitsS, fitsP, fitsT, fitsY⟩ := ok
  simp only at unusedS unusedP unusedT unusedY aloneP aloneT aloneY
  -- the bucket of the source triple
  obtain ⟨h, hashRun⟩ := hash_subject_ok main.subject
  obtain ⟨bucket, bucketRun, -⟩ := bucket_of_spec h (alloc.vec.Vec.len s.sources)
  have objectHash : rdf_mapping.hash_object ts.object = .ok h := by
    rw [hash_object_subject ts.object main.subject fitsS.2.2]; exact hashRun
  obtain ⟨b, at_b, e, member, eIs⟩ := sources source.val ts x bucket (List.getElem?_eq_some_iff.mp unusedS.1).1
    unusedS.1 subjectS fitsS.2.1 ⟨h, objectHash, bucketRun⟩
  have eSame : e = source := UScalar.eq_of_val_eq eIs
  subst eSame
  obtain ⟨m, at_m⟩ := List.mem_iff_getElem?.mp member
  have inside : bucket.val < s.sources.val.length := (List.getElem?_eq_some_iff.mp at_b).1
  have lookup : s.sources.index_usize bucket = .ok b := by
    simp [alloc.vec.Vec.index_usize, at_b]
  -- the reification at the source triple
  have sourceIn : e.val < triples.val.length := (List.getElem?_eq_some_iff.mp unusedS.1).1
  obtain ⟨pFound, pIs, pRun⟩ := find_unique triples s x complete unusedP.1 unusedP.2 fitsP.1 owlAnnotatedProperty
    fitsP.2.1 aloneP
  obtain ⟨tFound, tIs, tRun⟩ := find_unique triples s x complete unusedT.1 unusedT.2 fitsT.1 owlAnnotatedTarget
    fitsT.2.1 aloneT
  obtain ⟨yFound, yIs, yRun⟩ := find_type_unique triples s x complete unusedY.1 unusedY.2 fitsY.1 fitsY.2.1 kind.val
    fitsY.2.2 aloneY
  have pEq : pFound = property := UScalar.eq_of_val_eq pIs
  have tEq : tFound = target := UScalar.eq_of_val_eq tIs
  have yEq : yFound = typing := UScalar.eq_of_val_eq yIs
  subst pEq tEq yEq
  have targetObject : tt.object = main.object := object_view_injective fitsT.2.2
  have partsRun : rdf_mapping.reifier_parts triples s x main kind = .ok (some (pFound, tFound, yFound)) := by
    rw [rdf_mapping.reifier_parts]
    simp only [lift, bind_ok]
    rw [pRun _ (by simp [array_slice_val, owlAnnotatedProperty])]
    simp only [bind_ok, alloc.vec.Vec.index_slice_index, main_lookup triples pFound tp unusedP.1, object_spells_correct,
      fitsP.2.2, decide_true, ↓reduceIte, lift]
    rw [tRun _ (by simp [array_slice_val, owlAnnotatedTarget])]
    simp [main_lookup triples tFound tt unusedT.1, same_object_correct, targetObject, yRun kind rfl]
  have hit : rdf_mapping.reifier_at triples s main kind e = .ok (some (e, pFound, tFound, yFound)) := by
    rw [rdf_mapping.reifier_at]
    have named := fitsS.2.1
    simp only [owlAnnotatedSource] at named
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, sourceIn, is_used_correct, unusedS.2,
      main_lookup triples e ts unusedS.1, rdf_mapping.reifier_source, subjectS, lift, same_correct, array_slice_val,
      named, subject_is_correct, fitsS.2.2, partsRun]
  rw [rdf_mapping.reifier]
  simp only [hashRun, bucketRun, bind_ok, alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte,
    alloc.vec.Vec.index_slice_index, lookup]
  exact reifier_in_hit triples s main kind b m e at_m _ hit same 0#usize (by simp)

/-! ### Reading annotations without annotations of their own -/

/-- The annotations of the reification of a triple that no blank node reifies
    are none. -/
theorem reified_absent (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (main : Usize)
    (kind : Slice U8) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[main.val]? = some t)
    (absent : ∀ f x, ¬ ReifierOk triples.val s.used.val t kind.val f x) :
    rdf_mapping.reified triples kinds main kind s fuel = .ok (some (alloc.vec.Vec.new _, s)) := by
  rw [rdf_mapping.reified]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples main t at_t, reifier_absent triples s t kind absent]

/-- The annotation the reader builds from a triple is the annotation of the
    triple's predicate and value. -/
theorem annotation_read (a : model.Annotation) (plain : a.annotations.val = []) (spelling : alloc.vec.Vec U8)
    (spelled : spelling.val = a.property.iri.spelling.val) :
    model.Annotation.mk (alloc.vec.Vec.new model.Annotation) { iri := ⟨spelling⟩ } a.value = a := by
  have h1 : alloc.vec.Vec.new model.Annotation = a.annotations := vec_eq_of_val (by rw [plain]; rfl)
  have h2 : spelling = a.property.iri.spelling := vec_eq_of_val spelled
  rw [h1, h2]
  cases a
  rfl

theorem tann_plain {y : Node} {a : model.Annotation} {s0 : Supply} {ps : List Pattern} {s1 : Supply}
    (h : TAnn y a s0 ps s1) (plain : a.annotations.val = []) :
    ∃ n, ps = [⟨y, a.property.iri.spelling.val, n⟩] ∧ s1 = s0 ∧ AnnotationValueNode a.value n := by
  cases h with
  | plain _ _ n _ _ valueNode => exact ⟨n, rfl, rfl, valueNode⟩
  | annotated _ _ _ _ _ _ _ nonempty => exact absurd plain nonempty

/-- **The annotations of a blank node are read in the order of their triples.**
    With a complete and sorted subject index, the annotation triples of `x` at
    increasing positions `hs`, every other triple about `x` used, and no
    annotation with annotations of its own, `node_annotations` reads exactly
    those annotations, using exactly their triples. -/
theorem node_annotations_plain (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (x : rdf.BlankNode)
    (noAnnotation : ∀ (used : List Bool) (t : rdf.Triple) f x, ¬ ReifierOk triples.val used t owlAnnotation f x) :
    ∀ (anns : List model.Annotation) {s0 : Supply} {ps : List Pattern} {s1 : Supply},
      TAnns (.blank x) anns s0 ps s1 → (∀ a ∈ anns, a.annotations.val = []) →
      (∀ a ∈ anns, ∀ v, a.value = .Literal v → LiteralReadable v) →
      (∀ a ∈ anns, rdf_mapping.property_kind kinds a.property.iri.spelling = .ok (some .Annotation)) →
      ∀ (hs : List Nat) (s : rdf_mapping.State) (out : alloc.vec.Vec model.Annotation) (fuel : Usize),
        SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length →
        BucketsSorted s.subjects.val → At triples.val hs ps → hs.Pairwise (· < ·) →
        (∀ i ∈ hs, s.used.val[i]? = some false) →
        (∀ (i : Nat) (t : rdf.Triple), triples.val[i]? = some t → s.used.val[i]? = some false →
          subjectView t.subject = .blank x → i ∈ hs) →
        anns.length ≤ fuel.val → out.val.length + anns.length ≤ Usize.max →
        ∃ v s', rdf_mapping.node_annotations triples kinds x s out fuel = .ok (some (v, s')) ∧
          v.val = out.val ++ anns ∧ Marked s s' (fun i => i ∈ hs) [] := by
  intro anns
  induction anns with
  | nil =>
    intro s0 ps s1 h _ _ _ hs s out fuel _ _ holds _ _ confined _ _
    obtain ⟨rfl, -⟩ := tanns_nil h
    have empty : hs = [] := by have := at_length holds; simpa using this
    subst empty
    refine ⟨out, s, ?_, by simp, marked_same (marked_refl s) (fun i => by simp)⟩
    rw [rdf_mapping.node_annotations]
    simp only [find_annotation_none triples kinds s x (fun i t at_i unused about => by
      have := confined i t at_i unused about; simp at this), bind_ok]
  | cons a rest ih =>
    intro s0 ps s1 h plain readable kindsOk hs s out fuel complete sorted holds increasing free confined fuelOk room
    cases h with
    | cons _ _ _ _ sMid _ p q ha hrest =>
      obtain ⟨n, rfl, rfl, valueNode⟩ := tann_plain ha (plain a (by simp))
      obtain ⟨hsA, hsB, rfl, holdsA, holdsB⟩ := at_split holds
      obtain ⟨h0, rfl⟩ : ∃ h0, hsA = [h0] := by
        have := at_length holdsA
        simp at this
        exact List.length_eq_one_iff.mp this
      obtain ⟨t0, at0, fits0⟩ : ∃ t, triples.val[h0]? = some t ∧ Matches ⟨.blank x, a.property.iri.spelling.val, n⟩ t := by
        cases holdsA with
        | cons hx _ => exact hx
      have increasing' : hsB.Pairwise (· < ·) := (List.pairwise_cons.mp increasing).2
      have after : ∀ j ∈ hsB, h0 < j := (List.pairwise_cons.mp increasing).1
      have unused0 : s.used.val[h0]? = some false := free h0 (by simp)
      have spelled : t0.predicate.spelling = a.property.iri.spelling := vec_eq_of_val fits0.2.1
      have kind0 : rdf_mapping.property_kind kinds t0.predicate.spelling = .ok (some .Annotation) := by
        rw [spelled]; exact kindsOk a (by simp)
      obtain ⟨f0, f0Is, findRun⟩ := find_annotation_first triples kinds s x complete sorted at0 unused0 fits0.1 kind0
        (by
          intro j u lt at_j unusedJ about
          have member := confined j u at_j unusedJ about
          rcases List.mem_cons.mp member with same | inB
          · omega
          · have := after j inB; omega)
      have fuelPos : 0 < fuel.val := by simp at fuelOk; omega
      obtain ⟨fuel', fuelRun, fuelValue⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := fuel) (y := 1#usize) (by simp; omega))
      have fuel'Is : fuel'.val = fuel.val - 1 := by simp at fuelValue; exact fuelValue.1
      have valueRun := annotation_value_complete t0.object a.value n valueNode (readable a (by simp)) fits0.2.2
      let s1 : rdf_mapping.State := { s with used := s.used.set f0 true }
      have mTake : Marked s s1 (fun i => i = h0) [] := by
        have := marked_take s f0
        rw [f0Is] at this
        exact this
      have reifiedRun : ∀ kind : Slice U8, kind.val = owlAnnotation →
          rdf_mapping.reified triples kinds f0 kind s1 fuel' = .ok (some (alloc.vec.Vec.new _, s1)) := by
        intro kind kindIs
        exact reified_absent triples kinds f0 kind s1 fuel' t0 (by rw [f0Is]; exact at0)
          (fun f x ok => noAnnotation _ t0 f x (by rw [← kindIs]; exact ok))
      have outRoom : out.val.length < Usize.max := by simp at room; omega
      obtain ⟨out1, push, contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out (model.Annotation.mk (alloc.vec.Vec.new model.Annotation)
          { iri := ⟨t0.predicate.spelling⟩ } a.value) outRoom)
      obtain ⟨v, s', run, vIs, marked⟩ := ih hrest (fun b m => plain b (List.mem_cons_of_mem _ m))
        (fun b m => readable b (List.mem_cons_of_mem _ m)) (fun b m => kindsOk b (List.mem_cons_of_mem _ m))
        hsB s1 out1 fuel' complete sorted holdsB increasing'
        (fun i inB => marked_unused mTake (free i (List.mem_cons_of_mem _ inB))
          (by show i ≠ h0; have := after i inB; omega))
        (by
          intro i t at_i unusedI about
          have before := marked_back mTake unusedI
          have member := confined i t at_i before about
          rcases List.mem_cons.mp member with same | inB
          · rw [same] at unusedI
            have inside : h0 < s.used.val.length := (List.getElem?_eq_some_iff.mp unused0).1
            rw [marked_used mTake inside rfl] at unusedI
            cases unusedI
          · exact inB)
        (by simp at fuelOk; omega) (by rw [contents]; simp at room ⊢; omega)
      refine ⟨v, s', ?_, ?_, ?_⟩
      · rw [rdf_mapping.node_annotations]
        simp only [findRun, bind_ok]
        have pos : (0#usize : Usize) < fuel := by scalar_tac
        simp only [pos, ↓reduceIte, alloc.vec.Vec.index_slice_index, main_lookup triples f0 t0 (by rw [f0Is]; exact at0),
          bind_ok, valueRun, lift, take_correct, fuelRun]
        rw [reifiedRun _ (by simp [array_slice_val, owlAnnotation])]
        simp only [bind_ok, uncurry_apply_pair, alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, outRoom,
          ↓reduceIte, iri_of_identity, push]
        exact run
      · rw [vIs, contents, annotation_read a (plain a (by simp)) t0.predicate.spelling fits0.2.1]
        simp
      · refine marked_same (marked_trans mTake marked) (fun i => ?_)
        simp

/-! ### The annotations of an axiom -/

/-- The state with the four triples of a reification used. -/
def takeFour (s : rdf_mapping.State) (found : Usize × Usize × Usize × Usize) : rdf_mapping.State :=
  { s with used := (((s.used.set found.1 true).set found.2.1 true).set found.2.2.1 true).set found.2.2.2 true }

theorem marked_take_four (s : rdf_mapping.State) (found : Usize × Usize × Usize × Usize) :
    Marked s (takeFour s found)
      (fun i => i = found.1.val ∨ i = found.2.1.val ∨ i = found.2.2.1.val ∨ i = found.2.2.2.val) [] := by
  have m1 := marked_take s found.1
  have m2 := marked_take { s with used := s.used.set found.1 true } found.2.1
  have m3 := marked_take { s with used := (s.used.set found.1 true).set found.2.1 true } found.2.2.1
  have m4 := marked_take { s with used := ((s.used.set found.1 true).set found.2.1 true).set found.2.2.1 true }
    found.2.2.2
  exact marked_same (marked_trans (marked_trans (marked_trans m1 m2) m3) m4) (fun i => by tauto)

/-- The annotations of a reification that the reader finds are those of its node. -/
theorem reified_found (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (main : Usize)
    (kind : Slice U8) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[main.val]? = some t)
    (found : Usize × Usize × Usize × Usize) (reifierRun : rdf_mapping.reifier triples s t kind = .ok (some found))
    (ts : rdf.Triple) (at_s : triples.val[found.1.val]? = some ts) (x : rdf.BlankNode) (subject : ts.subject = .Blank x)
    (s2 : rdf_mapping.State) (recordRun : rdf_mapping.record (takeFour s found) x = .ok s2)
    (v : alloc.vec.Vec model.Annotation) (s3 : rdf_mapping.State)
    (nodeRun : rdf_mapping.node_annotations triples kinds x s2 (alloc.vec.Vec.new _) fuel = .ok (some (v, s3)))
    (nonempty : v.val ≠ []) :
    rdf_mapping.reified triples kinds main kind s fuel = .ok (some (v, s3)) := by
  obtain ⟨source, property, target, typing⟩ := found
  have positive : (0#usize : Usize) < alloc.vec.Vec.len v := by
    have : 0 < v.val.length := List.length_pos_of_ne_nil nonempty
    scalar_tac
  rw [rdf_mapping.reified]
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples main t at_t, bind_ok, reifierRun,
    uncurry_apply_pair, take_correct]
  simp only [main_lookup triples source ts at_s, bind_ok, subject]
  have recordRun' : rdf_mapping.record
      { used := (((s.used.set source true).set property true).set target true).set typing true,
        blanks := s.blanks, subjects := s.subjects, sources := s.sources } x = .ok s2 := recordRun
  simp only [recordRun', bind_ok, nodeRun, uncurry_apply_pair, positive, ↓reduceIte]

/-- An axiom with one main triple reads with the annotations of its reification. -/
theorem annotate_main (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (index : Usize)
    (ax : model.Axiom) (s : rdf_mapping.State) (fuel : Usize) (shape : rdf_mapping.main_triples ax = .ok 1#u8)
    (v : alloc.vec.Vec model.Annotation) (s' : rdf_mapping.State)
    (reifiedRun : ∀ kind : Slice U8, kind.val = owlAxiom →
      rdf_mapping.reified triples kinds index kind s fuel = .ok (some (v, s'))) :
    rdf_mapping.annotate triples kinds index ax s fuel = .ok (some (⟨v, ax⟩, s')) := by
  rw [rdf_mapping.annotate]
  have zero : ¬ ((1#u8 : U8) = 0#u8) := by decide
  simp only [shape, bind_ok]
  rw [if_neg zero]
  simp only [↓reduceIte, lift, bind_ok]
  rw [reifiedRun _ (by simp [array_slice_val, owlAxiom])]
  simp only [bind_ok, uncurry_apply_pair]

/-- An axiom that a blank node represents reads with the annotations of that node. -/
theorem annotate_node (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (index : Usize)
    (ax : model.Axiom) (s : rdf_mapping.State) (fuel : Usize) (shape : rdf_mapping.main_triples ax = .ok 0#u8)
    (t : rdf.Triple) (at_t : triples.val[index.val]? = some t) (x : rdf.BlankNode) (subject : t.subject = .Blank x)
    (v : alloc.vec.Vec model.Annotation) (s' : rdf_mapping.State)
    (nodeRun : rdf_mapping.node_annotations triples kinds x s (alloc.vec.Vec.new _) fuel = .ok (some (v, s'))) :
    rdf_mapping.annotate triples kinds index ax s fuel = .ok (some (⟨v, ax⟩, s')) := by
  rw [rdf_mapping.annotate]
  simp only [shape, bind_ok, ↓reduceIte, alloc.vec.Vec.index_slice_index, main_lookup triples index t at_t, subject,
    nodeRun, uncurry_apply_pair]

end Rowl.RdfReadAnnotations
