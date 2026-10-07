import Rowl.RdfReadAnnotated

/-!
# Completeness of the reverse RDF mapping for annotated graphs in any order

The triples of a graph of an annotated ontology come in any order. For every
ontology with ontology annotations and annotated axioms that the reverse
mapping reads back (`ReadableAnnotated`), a graph whose triples are a
permutation of the triples of its forward mapping is mapped to that ontology:
the same identity, the same imports, annotations and axioms up to their order,
each axiom with its annotations up to their order, and the blank nodes up to
their order (`map_graph_complete_annotated_perm`). The reader needs no change
for this:

* `read_axiom` passes over the reification of an annotated axiom and the
  annotation triples of its reifying node when it meets them before the main
  triple (`agraph_skip`): the triple typing the node `owl:Axiom` and the three
  triples with the predicates `owl:annotatedSource`, `owl:annotatedProperty`
  and `owl:annotatedTarget` are no axioms (`typing_reifier_blank`,
  `read_axiom_reification_skip`), and an annotation triple of a node typed
  `owl:Axiom` is left to the axiom that node annotates (`read_axiom_head_skip`);
* the axiom loop reads each annotated axiom when it meets its main triple, with
  its annotations in the order of their triples (`annotated_loop_perm`, with
  the blocks sorted by their main positions, `sort_ablocks_sorted`);
* `header_parts` takes the version, the imports and the ontology annotations
  wherever they are (`header_parts_rest_a`).
-/

namespace Rowl.RdfReadAnnotatedPermuted
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust Rowl.RdfMapping Rowl.RdfReadIndexes Rowl.RdfReadExpressions
  Rowl.RdfReadAxioms Rowl.RdfReadOntology Rowl.RdfReadPermuted Rowl.RdfReadAnnotations Rowl.RdfReadAnnotated

set_option maxRecDepth 16384 in
/-- The predicates of the reification triples are reserved, name no built-in
    entity and are not dispatched on. -/
theorem reification_predicates_structural : ∀ key ∈ [owlAnnotatedSource, owlAnnotatedProperty, owlAnnotatedTarget],
    Rowl.Vocabulary.Reserved key ∧ Rowl.Builtins.role key = none ∧ key ∉ specialPredicates := by
  decide

set_option maxRecDepth 16384 in
/-- The predicates that `read_axiom` dispatches on are vocabulary of the mapping. -/
theorem special_vocabulary : ∀ key ∈ specialPredicates, key ∈ mappingVocabulary := by
  decide

attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-! ### The triples of a reification met before its axiom -/

/-- The typing triple of the node of a reification is passed over. -/
theorem typing_reifier_blank (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t) (x : rdf.BlankNode)
    (subject : t.subject = .Blank x) (object : objectView t.object = .iri owlAxiom) :
    rdf_mapping.typing triples kinds a s fuel = .ok (.Skip s) := by
  have blank := blank_subject_true t x subject
  rw [rdf_mapping.typing]
  simp only [owlAxiom] at object
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val,
    object, blank]

theorem reifier_typing_true (triples : alloc.vec.Vec rdf.Triple) (index : Usize) (node : rdf.BlankNode)
    (t : rdf.Triple) (at_t : triples.val[index.val]? = some t) (about : subjectView t.subject = .blank node)
    (typed : t.predicate.spelling.val = rdfType) (object : objectView t.object = .iri owlAxiom) :
    rdf_mapping.reifier_typing triples index node = .ok true := by
  have inside : index.val < triples.val.length := (List.getElem?_eq_some_iff.mp at_t).1
  have typed' := typed
  simp only [rdfType] at typed'
  have typeRun : rdf_mapping.reifier_type t.object = .ok true := by
    rw [rdf_mapping.reifier_type]
    simp only [owlAxiom] at object
    simp [lift, object_is_correct, array_slice_val, object]
  rw [rdf_mapping.reifier_typing]
  simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index,
    main_lookup triples index t at_t, about_correct, about, lift, same_correct, array_slice_val, typed', typeRun]

theorem reifier_typing_total (triples : alloc.vec.Vec rdf.Triple) (index : Usize) (node : rdf.BlankNode) :
    ∃ b, rdf_mapping.reifier_typing triples index node = .ok b := by
  rw [rdf_mapping.reifier_typing]
  by_cases inside : index.val < triples.val.length
  · have at_t : triples.val[index.val]? = some triples.val[index.val] := List.getElem?_eq_getElem inside
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      main_lookup triples index _ at_t, bind_ok, about_correct, lift, same_correct, array_slice_val]
    split
    · split
      · rw [rdf_mapping.reifier_type]
        simp only [lift, bind_ok, object_is_correct, array_slice_val]
        split <;> try exact ⟨_, rfl⟩
        split <;> try exact ⟨_, rfl⟩
        split <;> try exact ⟨_, rfl⟩
        split <;> try exact ⟨_, rfl⟩
        split <;> exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]⟩

theorem typed_reifier_in_true (triples : alloc.vec.Vec rdf.Triple) (bucket : alloc.vec.Vec Usize)
    (node : rdf.BlankNode) (m : Nat) (e : Usize) (at_m : bucket.val[m]? = some e)
    (hit : rdf_mapping.reifier_typing triples e node = .ok true) :
    ∀ k : Usize, k.val ≤ m → rdf_mapping.typed_reifier_in triples bucket node k = .ok true := by
  intro k
  induction d : m - k.val generalizing k with
  | zero =>
    intro le
    have kIs : k.val = m := by omega
    have more : k.val < bucket.val.length := by rw [kIs]; exact (List.getElem?_eq_some_iff.mp at_m).1
    have lookup : bucket.index_usize k = .ok e := by simp [alloc.vec.Vec.index_usize, kIs, at_m]
    rw [rdf_mapping.typed_reifier_in]
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
    obtain ⟨b, run⟩ := reifier_typing_total triples bucket.val[k.val] node
    rw [rdf_mapping.typed_reifier_in]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
      bind_ok, run]
    cases b with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, advance, bind_ok]
      exact ih next (by omega) (by omega)

/-- A blank node typed `owl:Axiom` by a triple of the graph is the node of a
    reification for the reader. -/
theorem reifier_subject_true (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (x : rdf.BlankNode)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {j : Nat} {u : rdf.Triple} (at_j : triples.val[j]? = some u) (about : subjectView u.subject = .blank x)
    (typed : u.predicate.spelling.val = rdfType) (object : objectView u.object = .iri owlAxiom) :
    rdf_mapping.reifier_subject triples s (.Blank x) = .ok true := by
  obtain ⟨h, hashRun⟩ := hash_blank_ok x
  obtain ⟨bucket, bucketRun, -⟩ := bucket_of_spec h (alloc.vec.Vec.len s.subjects)
  obtain ⟨b, at_b, e, member, eIs⟩ := complete j u x bucket (List.getElem?_eq_some_iff.mp at_j).1 at_j
    (subject_blank about) ⟨h, hashRun, bucketRun⟩
  have inside : bucket.val < s.subjects.val.length := (List.getElem?_eq_some_iff.mp at_b).1
  have lookup : s.subjects.index_usize bucket = .ok b := by simp [alloc.vec.Vec.index_usize, at_b]
  obtain ⟨m, at_m⟩ := List.mem_iff_getElem?.mp member
  have hit := reifier_typing_true triples e x u (by rw [eIs]; exact at_j) about typed object
  rw [rdf_mapping.reifier_subject]
  simp only [hashRun, bucketRun, bind_ok, alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte,
    alloc.vec.Vec.index_slice_index, lookup]
  exact typed_reifier_in_true triples b x m e at_m hit 0#usize (by simp)

/-- An annotation triple of the node of a reification is passed over: the node
    is typed `owl:Axiom`, so the reader leaves its annotations to the axiom. -/
theorem read_axiom_head_skip (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t) (x : rdf.BlankNode)
    (subject : t.subject = .Blank x)
    (allowed : Rowl.Vocabulary.EntityAllowed ⟨t.predicate.spelling⟩ .AnnotationProperty)
    (kind : rdf_mapping.property_kind kinds t.predicate.spelling = .ok (some .Annotation))
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {j : Nat} {u : rdf.Triple} (at_j : triples.val[j]? = some u) (about : subjectView u.subject = .blank x)
    (typed : u.predicate.spelling.val = rdfType) (object : objectView u.object = .iri owlAxiom) :
    rdf_mapping.read_axiom triples kinds a s fuel = .ok (.Skip s) := by
  rw [read_axiom_assertion triples kinds a s fuel t at_t allowed (Or.inr (Or.inr rfl))]
  have reifier := reifier_subject_true triples s x complete at_j about typed object
  rw [rdf_mapping.assertion]
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, kind]
  rw [rdf_mapping.annotation_assertion]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, subject, reifier]

/-- A reification triple with a structural predicate is passed over. -/
theorem read_axiom_reification_skip (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (which : t.predicate.spelling.val = owlAnnotatedSource ∨ t.predicate.spelling.val = owlAnnotatedProperty ∨
      t.predicate.spelling.val = owlAnnotatedTarget) :
    rdf_mapping.read_axiom triples kinds a s fuel = .ok (.Skip s) := by
  have member : t.predicate.spelling.val ∈ [owlAnnotatedSource, owlAnnotatedProperty, owlAnnotatedTarget] := by
    rcases which with h | h | h <;> simp [h]
  obtain ⟨reserved, notBuiltin, notSpecial⟩ := reification_predicates_structural _ member
  exact read_axiom_structural triples kinds a s fuel t at_t reserved notBuiltin notSpecial

/-! ### The header with its annotations in any order -/

/-- The unused triples about the ontology IRI from `index` on: the imports
    `rem`, the version `vrem` and the annotations `arem` at their positions, and
    triples that are no part of the header. -/
structure HeaderRestA (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (ontology : alloc.vec.Vec U8)
    (used : List Bool) (index : Nat) (vrem : Option (Nat × model.Iri)) (rem : List (Nat × model.Iri))
    (arem : List (Nat × model.Annotation)) : Prop where
  imports : ∀ p ∈ rem, index ≤ p.1 ∧ used[p.1]? = some false ∧ ∃ t, triples.val[p.1]? = some t ∧
    subjectView t.subject = .iri ontology.val ∧ t.predicate.spelling.val = owlImports ∧
    objectView t.object = iriNode p.2
  nodup : (rem.map Prod.fst).Nodup
  version : ∀ p ∈ vrem, index ≤ p.1 ∧ used[p.1]? = some false ∧ ∃ t, triples.val[p.1]? = some t ∧
    subjectView t.subject = .iri ontology.val ∧ t.predicate.spelling.val = owlVersionIRI ∧
    objectView t.object = iriNode p.2
  annotations : ∀ p ∈ arem, index ≤ p.1 ∧ used[p.1]? = some false ∧ ∃ t n, triples.val[p.1]? = some t ∧
    subjectView t.subject = .iri ontology.val ∧ t.predicate.spelling.val = p.2.property.iri.spelling.val ∧
    objectView t.object = n ∧ AnnotationValueNode p.2.value n
  props : ∀ p ∈ arem, p.2.annotations.val = [] ∧ (∀ v, p.2.value = .Literal v → LiteralReadable v) ∧
    rdf_mapping.property_kind kinds p.2.property.iri.spelling = .ok (some .Annotation) ∧
    p.2.property.iri.spelling.val ≠ owlVersionIRI ∧ p.2.property.iri.spelling.val ≠ owlImports
  anodup : (arem.map Prod.fst).Nodup
  other : ∀ (i : Nat) (t : rdf.Triple), index ≤ i → triples.val[i]? = some t → used[i]? = some false →
    subjectView t.subject = .iri ontology.val → (∃ v, (i, v) ∈ rem) ∨ (∃ v, vrem = some (i, v)) ∨
      (∃ a, (i, a) ∈ arem) ∨
      (t.predicate.spelling.val ≠ owlVersionIRI ∧ t.predicate.spelling.val ≠ owlImports ∧
        ∃ r, rdf_mapping.property_kind kinds t.predicate.spelling = .ok r ∧ r ≠ some .Annotation)

theorem header_rest_a_step {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {ontology : alloc.vec.Vec U8} {used used' : List Bool} {index : Nat} {vrem vrem' : Option (Nat × model.Iri)}
    {rem rem' : List (Nat × model.Iri)} {arem arem' : List (Nat × model.Annotation)}
    (h : HeaderRestA triples kinds ontology used index vrem rem arem)
    (keep : ∀ (i : Nat), index < i → used[i]? = some false → used'[i]? = some false)
    (back : ∀ (i : Nat), used'[i]? = some false → used[i]? = some false)
    (remSub : ∀ p ∈ rem', p ∈ rem) (remNot : ∀ p ∈ rem', p.1 ≠ index) (nodup' : (rem'.map Prod.fst).Nodup)
    (vSub : ∀ p ∈ vrem', p ∈ vrem) (vNot : ∀ p ∈ vrem', p.1 ≠ index)
    (aSub : ∀ p ∈ arem', p ∈ arem) (aNot : ∀ p ∈ arem', p.1 ≠ index) (anodup' : (arem'.map Prod.fst).Nodup)
    (covered : ∀ p ∈ rem, p.1 ≠ index → p ∈ rem') (vcovered : ∀ p ∈ vrem, p.1 ≠ index → p ∈ vrem')
    (acovered : ∀ p ∈ arem, p.1 ≠ index → p ∈ arem') :
    HeaderRestA triples kinds ontology used' (index + 1) vrem' rem' arem' where
  imports := by
    intro p m
    obtain ⟨low, unused, rest⟩ := h.imports p (remSub p m)
    have ne := remNot p m
    exact ⟨by omega, keep p.1 (by omega) unused, rest⟩
  nodup := nodup'
  version := by
    intro p m
    obtain ⟨low, unused, rest⟩ := h.version p (vSub p m)
    have ne := vNot p m
    exact ⟨by omega, keep p.1 (by omega) unused, rest⟩
  annotations := by
    intro p m
    obtain ⟨low, unused, rest⟩ := h.annotations p (aSub p m)
    have ne := aNot p m
    exact ⟨by omega, keep p.1 (by omega) unused, rest⟩
  props := fun p m => h.props p (aSub p m)
  anodup := anodup'
  other := by
    intro i t low at_i unused about
    rcases h.other i t (by omega) at_i (back i unused) about with ⟨v, m⟩ | ⟨v, m⟩ | ⟨a, m⟩ | rest
    · exact Or.inl ⟨v, covered (i, v) m (by simp only; omega)⟩
    · refine Or.inr (Or.inl ⟨v, ?_⟩)
      exact Option.mem_def.mp (vcovered (i, v) (Option.mem_def.mpr m) (by simp only; omega))
    · exact Or.inr (Or.inr (Or.inl ⟨a, acovered (i, a) m (by simp only; omega)⟩))
    · exact Or.inr (Or.inr (Or.inr rest))

theorem header_rest_a_end {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {ontology : alloc.vec.Vec U8} {used : List Bool} {index : Nat} {vrem : Option (Nat × model.Iri)}
    {rem : List (Nat × model.Iri)} {arem : List (Nat × model.Annotation)}
    (h : HeaderRestA triples kinds ontology used index vrem rem arem) (done : triples.val.length ≤ index) :
    rem = [] ∧ vrem = none ∧ arem = [] := by
  refine ⟨?_, ?_, ?_⟩
  · cases rem with
    | nil => rfl
    | cons p ps =>
      exfalso
      obtain ⟨low, -, t, at_t, -⟩ := h.imports p (by simp)
      have := (List.getElem?_eq_some_iff.mp at_t).1
      omega
  · cases vrem with
    | none => rfl
    | some p =>
      exfalso
      obtain ⟨low, -, t, at_t, -⟩ := h.version p (by simp)
      have := (List.getElem?_eq_some_iff.mp at_t).1
      omega
  · cases arem with
    | nil => rfl
    | cons p ps =>
      exfalso
      obtain ⟨low, -, t, n, at_t, -⟩ := h.annotations p (by simp)
      have := (List.getElem?_eq_some_iff.mp at_t).1
      omega

/-- The positions of a list without one entry. -/
theorem erase_positions {α : Type} [DecidableEq α] {l : List (Nat × α)} {p : Nat × α} (m : p ∈ l)
    (nodup : (l.map Prod.fst).Nodup) :
    ((l.erase p).map Prod.fst).Nodup ∧ (∀ q ∈ l.erase p, q.1 ≠ p.1) ∧
      ∀ q ∈ l, q.1 ≠ p.1 → q ∈ l.erase p := by
  have permErase := List.perm_cons_erase m
  have nodupE := (permErase.map Prod.fst).nodup_iff.mp nodup
  simp only [List.map_cons, List.nodup_cons] at nodupE
  obtain ⟨notIn, nodupTail⟩ := nodupE
  refine ⟨nodupTail, fun q qIn same => notIn (List.mem_map.mpr ⟨q, qIn, same⟩), fun q qIn ne => ?_⟩
  refine (List.mem_erase_of_ne ?_).mpr qIn
  intro e; rw [e] at ne; exact ne rfl

/-- **The header reader takes the version, the imports and the annotations
    wherever they are.** From `index` on, `header_parts` takes the version
    `vrem`, the imports `rem` and the annotations `arem` in the order of their
    positions, and uses exactly their triples. -/
theorem header_parts_rest_a (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8)
    (noAnnotation : ∀ (used : List Bool) (t : rdf.Triple) f x, ¬ ReifierOk triples.val used t owlAnnotation f x) :
    ∀ (n : Nat) (index : Usize) (s : rdf_mapping.State) (version : Option model.Iri)
      (imports : alloc.vec.Vec model.Iri) (annotations : alloc.vec.Vec model.Annotation)
      (vrem : Option (Nat × model.Iri)) (rem : List (Nat × model.Iri)) (arem : List (Nat × model.Annotation)),
      triples.val.length - index.val = n → HeaderRestA triples kinds ontology s.used.val index.val vrem rem arem →
      (vrem ≠ none → version = none) → imports.val.length + rem.length ≤ Usize.max →
      annotations.val.length + arem.length ≤ Usize.max →
      ∃ ver imp ann s', rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
          .ok (some (ver, imp, ann, s')) ∧
        ver = (vrem.map Prod.snd).or version ∧ imp.val.Perm (imports.val ++ rem.map Prod.snd) ∧
        ann.val.Perm (annotations.val ++ arem.map Prod.snd) ∧
        Marked s s' (fun i => (∃ v, (i, v) ∈ rem) ∨ (∃ v, vrem = some (i, v)) ∨ ∃ a, (i, a) ∈ arem) [] := by
  intro n
  induction n with
  | zero =>
    intro index s version imports annotations vrem rem arem ends rest _ _ _
    have done : ¬ index.val < triples.val.length := by omega
    obtain ⟨rfl, rfl, rfl⟩ := header_rest_a_end rest (by omega)
    refine ⟨version, imports, annotations, s, ?_, rfl, by simp, by simp,
      marked_same (marked_refl s) (fun i => by simp)⟩
    rw [rdf_mapping.header_parts]; simp [UScalar.lt_equiv, done]
  | succ n ih =>
    intro index s version imports annotations vrem rem arem ends rest versionFree room aroom
    have more : index.val < triples.val.length := by omega
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := triples.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have ends' : triples.val.length - next.val = n := by omega
    obtain ⟨t, at_t⟩ : ∃ t, triples.val[index.val]? = some t := ⟨_, List.getElem?_eq_getElem more⟩
    -- the entries at `index` describe this triple
    have importAt : ∀ p ∈ rem, p.1 = index.val → s.used.val[index.val]? = some false ∧
        subjectView t.subject = .iri ontology.val ∧ t.predicate.spelling.val = owlImports ∧
        objectView t.object = iriNode p.2 := by
      intro p m same
      obtain ⟨-, unused, t', at', about, predicate, object⟩ := rest.imports p m
      rw [same, at_t] at at'
      cases at'
      rw [same] at unused
      exact ⟨unused, about, predicate, object⟩
    have versionAt : ∀ p ∈ vrem, p.1 = index.val → s.used.val[index.val]? = some false ∧
        subjectView t.subject = .iri ontology.val ∧ t.predicate.spelling.val = owlVersionIRI ∧
        objectView t.object = iriNode p.2 := by
      intro p m same
      obtain ⟨-, unused, t', at', about, predicate, object⟩ := rest.version p m
      rw [same, at_t] at at'
      cases at'
      rw [same] at unused
      exact ⟨unused, about, predicate, object⟩
    have annotationAt : ∀ p ∈ arem, p.1 = index.val → s.used.val[index.val]? = some false ∧
        subjectView t.subject = .iri ontology.val ∧ t.predicate.spelling.val = p.2.property.iri.spelling.val ∧
        ∃ m, objectView t.object = m ∧ AnnotationValueNode p.2.value m := by
      intro p m same
      obtain ⟨-, unused, t', m', at', about, predicate, object, valueNode⟩ := rest.annotations p m
      rw [same, at_t] at at'
      cases at'
      rw [same] at unused
      exact ⟨unused, about, predicate, m', object, valueNode⟩
    have importsVersion : owlImports ≠ owlVersionIRI := by simp [owlImports, owlVersionIRI]
    -- passing over the triple at `index`
    have passOver : ∀ (s' : rdf_mapping.State), (∀ (i : Nat), index.val < i → s.used.val[i]? = some false →
          s'.used.val[i]? = some false) → (∀ (i : Nat), s'.used.val[i]? = some false → s.used.val[i]? = some false) →
        (∀ p ∈ rem, p.1 ≠ index.val) → (∀ p ∈ vrem, p.1 ≠ index.val) → (∀ p ∈ arem, p.1 ≠ index.val) →
        HeaderRestA triples kinds ontology s'.used.val next.val vrem rem arem := by
      intro s' keep back remNot vNot aNot
      rw [nextIs]
      exact header_rest_a_step rest keep back (fun p m => m) remNot rest.nodup (fun p m => m) vNot (fun p m => m)
        aNot rest.anodup (fun p m _ => m) (fun p m _ => m) (fun p m _ => m)
    by_cases unused : s.used.val[index.val]? = some false
    · by_cases about : subjectView t.subject = .iri ontology.val
      · by_cases isVersion : t.predicate.spelling.val = owlVersionIRI
        · -- the version
          obtain ⟨v, rfl⟩ : ∃ v, vrem = some (index.val, v) := by
            rcases rest.other index.val t (le_refl _) at_t unused about with ⟨v, m⟩ | ⟨v, m⟩ | ⟨a, m⟩ | ⟨notV, -⟩
            · exfalso
              have := (importAt _ m rfl).2.2.1
              rw [isVersion] at this
              exact importsVersion this.symm
            · exact ⟨v, m⟩
            · exfalso
              exact (rest.props _ m).2.2.2.1 ((annotationAt _ m rfl).2.2.1 ▸ isVersion)
            · exact absurd isVersion notV
          have versionNone := versionFree (by simp)
          subst versionNone
          obtain ⟨-, -, -, object⟩ := versionAt (index.val, v) (by simp) rfl
          have step := header_parts_version triples kinds ontology imports annotations index next s t at_t unused
            about isVersion v object advance
          have mTake := marked_take s index
          obtain ⟨ver, imp, ann, s', run, verIs, impPerm, annPerm, marked⟩ := ih next
            { s with used := s.used.set index true } (some v) imports annotations none rem arem ends'
            (by
              rw [nextIs]
              refine header_rest_a_step rest (fun i low u => marked_unused mTake u (by show i ≠ index.val; omega))
                (fun i u => marked_back mTake u) (fun p m => m) ?_ rest.nodup (by simp) (by simp)
                (fun p m => m) ?_ rest.anodup (fun p m _ => m) ?_ (fun p m _ => m)
              · intro p m same
                have := (importAt p m same).2.2.1
                rw [isVersion] at this
                exact importsVersion this.symm
              · intro p m same
                exact (rest.props p m).2.2.2.1 ((annotationAt p m same).2.2.1 ▸ isVersion)
              · intro p m ne
                simp only [Option.mem_def, Option.some.injEq] at m
                subst m
                exact absurd rfl ne)
            (by simp) room aroom
          refine ⟨ver, imp, ann, s', by rw [step]; exact run, by simp [verIs], by simpa using impPerm, annPerm, ?_⟩
          refine marked_same (marked_trans mTake marked) (fun i => ?_)
          constructor
          · rintro (same | (⟨w, m⟩ | ⟨w, m⟩ | ⟨a, m⟩))
            · exact Or.inr (Or.inl ⟨v, by rw [same]⟩)
            · exact Or.inl ⟨w, m⟩
            · simp at m
            · exact Or.inr (Or.inr ⟨a, m⟩)
          · rintro (⟨w, m⟩ | ⟨w, m⟩ | ⟨a, m⟩)
            · exact Or.inr (Or.inl ⟨w, m⟩)
            · simp only [Option.some.injEq, Prod.mk.injEq] at m
              exact Or.inl m.1.symm
            · exact Or.inr (Or.inr (Or.inr ⟨a, m⟩))
        · by_cases isImports : t.predicate.spelling.val = owlImports
          · -- an import
            obtain ⟨j, m⟩ : ∃ j, (index.val, j) ∈ rem := by
              rcases rest.other index.val t (le_refl _) at_t unused about with ⟨v, m⟩ | ⟨v, m⟩ | ⟨a, m⟩ | ⟨-, notI, -⟩
              · exact ⟨v, m⟩
              · exact absurd (versionAt (index.val, v) (by rw [m]; simp) rfl).2.2.1 isVersion
              · exact absurd ((annotationAt _ m rfl).2.2.1 ▸ isImports) (rest.props _ m).2.2.2.2
              · exact absurd isImports notI
            obtain ⟨-, -, -, object⟩ := importAt _ m rfl
            have remPos : 0 < rem.length := List.length_pos_of_mem m
            have importsRoom : imports.val.length < Usize.max := by omega
            obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec imports j importsRoom)
            have step := header_parts_import triples kinds ontology version imports annotations index next s t at_t
              unused about isImports j object importsRoom pushed push advance
            have mTake := marked_take s index
            obtain ⟨nodupE, notE, coveredE⟩ := erase_positions m rest.nodup
            have permErase := List.perm_cons_erase m
            obtain ⟨ver, imp, ann, s', run, verIs, impPerm, annPerm, marked⟩ := ih next
              { s with used := s.used.set index true } version pushed annotations vrem (rem.erase (index.val, j)) arem
              ends'
              (by
                rw [nextIs]
                exact header_rest_a_step rest (fun i low u => marked_unused mTake u (by show i ≠ index.val; omega))
                  (fun i u => marked_back mTake u) (fun p m' => List.mem_of_mem_erase m') notE nodupE
                  (fun p m' => m') (fun p m' same => isVersion ((versionAt p m' same).2.2.1 ▸ isImports ▸ rfl))
                  (fun p m' => m')
                  (fun p m' same => (rest.props p m').2.2.2.2 ((annotationAt p m' same).2.2.1 ▸ isImports))
                  rest.anodup coveredE (fun p m' _ => m') (fun p m' _ => m'))
              versionFree
              (by
                rw [contents, List.length_erase_of_mem m]
                simp only [List.length_append, List.length_singleton]
                omega)
              aroom
            refine ⟨ver, imp, ann, s', by rw [step]; exact run, verIs, ?_, annPerm, ?_⟩
            · refine impPerm.trans ?_
              rw [contents, List.append_assoc]
              refine List.Perm.append_left imports.val ?_
              have := (permErase.map Prod.snd).symm
              simpa using this
            · refine marked_same (marked_trans mTake marked) (fun i => ?_)
              constructor
              · rintro (same | (⟨w, m'⟩ | ⟨w, m'⟩ | ⟨a, m'⟩))
                · exact Or.inl ⟨j, by rw [same]; exact m⟩
                · exact Or.inl ⟨w, List.mem_of_mem_erase m'⟩
                · exact Or.inr (Or.inl ⟨w, m'⟩)
                · exact Or.inr (Or.inr ⟨a, m'⟩)
              · rintro (⟨w, m'⟩ | ⟨w, m'⟩ | ⟨a, m'⟩)
                · by_cases same : i = index.val
                  · exact Or.inl same
                  · exact Or.inr (Or.inl ⟨w, coveredE (i, w) m' same⟩)
                · exact Or.inr (Or.inr (Or.inl ⟨w, m'⟩))
                · exact Or.inr (Or.inr (Or.inr ⟨a, m'⟩))
          · rcases rest.other index.val t (le_refl _) at_t unused about with ⟨v, m⟩ | ⟨v, m⟩ | ⟨a, m⟩ | facts
            · exact absurd (importAt _ m rfl).2.2.1 isImports
            · exact absurd (versionAt (index.val, v) (by rw [m]; simp) rfl).2.2.1 isVersion
            · -- an annotation of the ontology
              obtain ⟨-, -, spelledA, m0, object, valueNode⟩ := annotationAt _ m rfl
              obtain ⟨plainA, readableA, kindA, -, -⟩ := rest.props _ m
              have spelled : t.predicate.spelling = a.property.iri.spelling := vec_eq_of_val spelledA
              have valueRun := annotation_value_complete t.object a.value m0 valueNode readableA object
              have arPos : 0 < arem.length := List.length_pos_of_mem m
              have annRoom : annotations.val.length < Usize.max := by omega
              obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
                (alloc.vec.Vec.push_spec annotations
                  (model.Annotation.mk (alloc.vec.Vec.new _) { iri := ⟨t.predicate.spelling⟩ } a.value) annRoom)
              have step := header_parts_annotation triples kinds ontology version imports annotations index next s t
                at_t unused about isVersion isImports (by rw [spelled]; exact kindA) a.value valueRun
                (noAnnotation · t) annRoom pushed push advance
              have mTake := marked_take s index
              obtain ⟨nodupE, notE, coveredE⟩ := erase_positions m rest.anodup
              have permErase := List.perm_cons_erase m
              obtain ⟨ver, imp, ann, s', run, verIs, impPerm, annPerm, marked⟩ := ih next
                { s with used := s.used.set index true } version imports pushed vrem rem (arem.erase (index.val, a))
                ends'
                (by
                  rw [nextIs]
                  exact header_rest_a_step rest (fun i low u => marked_unused mTake u (by show i ≠ index.val; omega))
                    (fun i u => marked_back mTake u) (fun p m' => m')
                    (fun p m' same => isImports (importAt p m' same).2.2.1) rest.nodup (fun p m' => m')
                    (fun p m' same => isVersion (versionAt p m' same).2.2.1)
                    (fun p m' => List.mem_of_mem_erase m') notE nodupE (fun p m' _ => m') (fun p m' _ => m')
                    coveredE)
                versionFree room
                (by
                  rw [contents, List.length_erase_of_mem m]
                  simp only [List.length_append, List.length_singleton]
                  omega)
              refine ⟨ver, imp, ann, s', by rw [step]; exact run, verIs, impPerm, ?_, ?_⟩
              · refine annPerm.trans ?_
                rw [contents, annotation_read a plainA t.predicate.spelling spelledA, List.append_assoc]
                refine List.Perm.append_left annotations.val ?_
                have := (permErase.map Prod.snd).symm
                simpa using this
              · refine marked_same (marked_trans mTake marked) (fun i => ?_)
                constructor
                · rintro (same | (⟨w, m'⟩ | ⟨w, m'⟩ | ⟨b, m'⟩))
                  · exact Or.inr (Or.inr ⟨a, by rw [same]; exact m⟩)
                  · exact Or.inl ⟨w, m'⟩
                  · exact Or.inr (Or.inl ⟨w, m'⟩)
                  · exact Or.inr (Or.inr ⟨b, List.mem_of_mem_erase m'⟩)
                · rintro (⟨w, m'⟩ | ⟨w, m'⟩ | ⟨b, m'⟩)
                  · exact Or.inr (Or.inl ⟨w, m'⟩)
                  · exact Or.inr (Or.inr (Or.inl ⟨w, m'⟩))
                  · by_cases same : i = index.val
                    · exact Or.inl same
                    · exact Or.inr (Or.inr (Or.inr ⟨b, coveredE (i, b) m' same⟩))
            · -- a triple about the ontology IRI that is no part of the header
              obtain ⟨notV, notI, kind⟩ := facts
              have step := header_parts_other triples kinds ontology version imports annotations index next s t at_t
                unused about notV notI kind advance
              obtain ⟨ver, imp, ann, s', run, verIs, impPerm, annPerm, marked⟩ := ih next s version imports annotations
                vrem rem arem ends'
                (passOver s (fun _ _ u => u) (fun _ u => u) (fun p m same => isImports (importAt p m same).2.2.1)
                  (fun p m same => isVersion (versionAt p m same).2.2.1)
                  (by
                    intro p m same
                    obtain ⟨r, kindRun, notAnnotation⟩ := kind
                    have spelled := vec_eq_of_val (annotationAt p m same).2.2.1
                    rw [spelled, (rest.props p m).2.2.1] at kindRun
                    exact notAnnotation (Result.ok_injective kindRun).symm))
                versionFree room aroom
              exact ⟨ver, imp, ann, s', by rw [step]; exact run, verIs, impPerm, annPerm, marked⟩
      · -- a triple about another subject
        have step := header_parts_elsewhere triples kinds ontology version imports annotations index next s t at_t
          unused about advance
        obtain ⟨ver, imp, ann, s', run, verIs, impPerm, annPerm, marked⟩ := ih next s version imports annotations vrem
          rem arem ends'
          (passOver s (fun _ _ u => u) (fun _ u => u) (fun p m same => about (importAt p m same).2.1)
            (fun p m same => about (versionAt p m same).2.1) (fun p m same => about (annotationAt p m same).2.1))
          versionFree room aroom
        exact ⟨ver, imp, ann, s', by rw [step]; exact run, verIs, impPerm, annPerm, marked⟩
    · -- a used triple
      have step := header_parts_passed triples kinds ontology version imports annotations index next s more unused
        advance
      obtain ⟨ver, imp, ann, s', run, verIs, impPerm, annPerm, marked⟩ := ih next s version imports annotations vrem
        rem arem ends'
        (passOver s (fun _ _ u => u) (fun _ u => u) (fun p m same => unused (importAt p m same).1)
          (fun p m same => unused (versionAt p m same).1) (fun p m same => unused (annotationAt p m same).1))
        versionFree room aroom
      exact ⟨ver, imp, ann, s', by rw [step]; exact run, verIs, impPerm, annPerm, marked⟩

/-! ### The blocks of annotated axioms at any positions -/

/-- The patterns of an annotated axiom of a readable ontology: those of its axiom
    and those of the reification of its main triple, if it is annotated. -/
theorem annotated_parts {o : model.RawOntology} (readable : ReadableAnnotated o) {ax : model.AnnotatedAxiom}
    (axIn : ax ∈ o.axioms.val) {s : Supply} {p : List Pattern} {s1 : Supply} (head : TAnnotatedAxiom ax s p s1) :
    ∃ (corePats apats : List Pattern) (afresh : Supply) (sMid : Supply),
      TAxiom ax.axiom s corePats (afresh ++ sMid) ∧ p = corePats ++ apats ∧ s1 = sMid ∧
      ((ax.annotations.val = [] ∧ apats = [] ∧ afresh = []) ∨
        (ax.annotations.val ≠ [] ∧ ∃ (x : rdf.BlankNode) (main : Pattern) (heads : List Pattern) (sx : Supply),
          afresh = [x] ∧ corePats.head? = some main ∧ apats = reification owlAxiom x main ++ heads ∧
          TAnns (.blank x) ax.annotations.val sx heads sx ∧ rdf_mapping.main_triples ax.axiom = .ok 1#u8)) := by
  have stripped := readable_strip readable
  obtain ⟨axReadable, plainAnns, oneMain⟩ := readable.axioms ax axIn
  cases head with
  | plain _ _ _ plainH tax => exact ⟨p, [], [], s1, by simpa using tax, by simp, rfl, Or.inl ⟨plainH, rfl, rfl⟩⟩
  | reified _ _ _ ps _ nonempty _ tax treified =>
    have one := oneMain nonempty
    obtain ⟨main, side, f, psIs, -, -, -⟩ := block_shape stripped (strip_member axIn) tax
    rw [one, psIs] at treified
    simp only [List.take_succ_cons, List.take_zero] at treified
    obtain ⟨x, sx, hs, rfl, rfl, tanns⟩ := treified_one treified
    have plainAll : ∀ a ∈ ax.annotations.val, a.annotations.val = [] := fun a m => (plainAnns a m).1
    have same := tanns_plain_supply tanns plainAll
    rw [same] at tanns
    exact ⟨ps, reification owlAxiom x main ++ hs, [x], sx, tax, by simp, same,
      Or.inr ⟨nonempty, x, main, hs, sx, rfl, by rw [psIs]; rfl, by simp, tanns,
        main_triples_one axReadable one⟩⟩
  | blank _ _ _ _ _ _ _ _ nonempty zero _ _ =>
    have := oneMain nonempty
    omega

/-- The blocks of the annotated axioms whose triples the graph holds at the
    positions `pos`, in any order. -/
theorem annotated_position_blocks {o : model.RawOntology} (readable : ReadableAnnotated o)
    (triples : alloc.vec.Vec rdf.Triple) :
    ∀ {axs : List model.AnnotatedAxiom} {s0 : Supply} {ps : List Pattern} {s1 : Supply}, TAxioms axs s0 ps s1 →
    (∀ ax ∈ axs, ax ∈ o.axioms.val) → ∀ (pos : List Nat), At triples.val pos ps → pos.Nodup →
    ∃ bs : List ABlock,
      bs.map ABlock.ax = axs ∧ s0 = bs.flatMap ABlock.fresh ++ s1 ∧ ps = bs.flatMap ABlock.pats ∧
      bs.Pairwise AApart ∧
      (∀ b ∈ bs, AImage o b ∧ At triples.val b.pos b.pats ∧ b.pos.Nodup ∧ b.apos.length = b.apats.length ∧
        ∀ i ∈ b.pos, i ∈ pos) ∧
      (∀ i ∈ pos, ∃ b ∈ bs, i ∈ b.pos) := by
  have stripped := readable_strip readable
  intro axs s0 ps s1 h
  induction h with
  | nil s =>
    intro _ pos holds _
    have empty : pos = [] := by have := at_length holds; simpa using this
    subst empty
    exact ⟨[], by simp, by simp, by simp, by simp, by simp, by simp⟩
  | cons ax rest s s1 s2 p q head tail ih =>
    intro members pos holds nodup
    have axIn := members ax (by simp)
    obtain ⟨-, plainAnns, -⟩ := readable.axioms ax axIn
    obtain ⟨corePats, apats, afresh, sMid, tax, pIs, sIs, part⟩ := annotated_parts readable axIn head
    obtain ⟨main, side, f, coreIs, eqf, sides, facts⟩ := block_shape stripped (strip_member axIn) tax
    obtain ⟨posP, posQ, rfl, holdsP, holdsQ⟩ := at_split holds
    rw [pIs] at holdsP
    obtain ⟨posC, posA, rfl, holdsC, holdsA⟩ := at_split holdsP
    have nodupQ := (List.nodup_append.mp nodup).2.1
    obtain ⟨bs, mapIs, freshIs, patsIs, disjoint, each, covers⟩ :=
      ih (fun b m => members b (List.mem_cons_of_mem _ m)) posQ holdsQ nodupQ
    obtain ⟨m0, restC, rfl⟩ : ∃ m0 restC, posC = m0 :: restC := by
      cases posC with
      | nil => have := at_length holdsC; rw [coreIs] at this; simp at this
      | cons m0 restC => exact ⟨m0, restC, rfl⟩
    let cb : Block := { ax := ax.axiom, main := m0, rest := restC, pats := corePats, fresh := f }
    let b : ABlock := { core := cb, ann := ax.annotations, apos := posA, apats := apats, afresh := afresh }
    have bPos : b.pos = (m0 :: restC) ++ posA := rfl
    refine ⟨b :: bs, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, mapIs, b, ABlock.ax]
      rfl
    · simp only [List.flatMap_cons, b, ABlock.fresh, cb]
      rw [eqf, ← sIs, freshIs]
      simp
    · simp only [List.flatMap_cons, b, ABlock.pats, cb]
      rw [pIs, patsIs]
    · refine List.Pairwise.cons ?_ disjoint
      intro c m i ib ic
      have inQ := (each c m).2.2.2.2 i ic
      rw [bPos] at ib
      exact (List.nodup_append.mp nodup).2.2 i ib i inQ rfl
    · intro c m
      rcases List.mem_cons.mp m with rfl | inRest
      · refine ⟨⟨by simp [ABlock.ax, b, cb, axIn], ⟨⟨bare ax, strip_member axIn, rfl, rfl⟩,
            ⟨_, by rw [← eqf]; exact tax⟩, ⟨main, side, coreIs, sides, facts⟩⟩, part, plainAnns⟩,
          by rw [bPos]; exact at_append holdsC holdsA, by rw [bPos]; exact (List.nodup_append.mp nodup).1,
          at_length holdsA, fun i m' => List.mem_append_left _ m'⟩
      · obtain ⟨image, holdsB, nodupB, lenB, inPos⟩ := each c inRest
        exact ⟨image, holdsB, nodupB, lenB, fun i m' => List.mem_append_right _ (inPos i m')⟩
    · intro i m
      rcases List.mem_append.mp m with inP | inQ
      · exact ⟨b, by simp, by rw [bPos]; exact inP⟩
      · obtain ⟨c, cIn, ic⟩ := covers i inQ
        exact ⟨c, List.mem_cons_of_mem _ cIn, ic⟩

/-! ### The axiom loop over annotated blocks in any order -/

/-- **The axiom loop reads the annotated blocks in the order of their main
    triples, wherever their other triples are.** From an index at or before
    every main position, with every block read from its main position with its
    annotations up to their order, and every other position of a block before
    its main one passed over, `axioms_from` returns the axioms of the blocks in
    order, records their blank nodes in order and uses every triple. -/
theorem annotated_loop_perm (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (all : List ABlock)
    (step : ∀ (s : rdf_mapping.State) (b : ABlock) (rest : List ABlock), (∀ c ∈ b :: rest, c ∈ all) →
      ALoop triples s (b :: rest) → ∀ (a : Usize), a.val = b.core.main →
      ∃ (s1 s' : rdf_mapping.State) (v : alloc.vec.Vec model.Annotation),
        rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found b.ax.axiom s1) ∧
        rdf_mapping.annotate triples kinds a b.ax.axiom s1 (alloc.vec.Vec.len triples) =
          .ok (some (⟨v, b.ax.axiom⟩, s')) ∧ v.val.Perm b.ann.val ∧ Marked s s' (fun i => i ∈ b.pos) b.fresh)
    (skip : ∀ b ∈ all, ∀ i ∈ b.pos, i < b.core.main → ∀ (u : Usize) (s' : rdf_mapping.State), u.val = i →
      SubjectsComplete triples.val s'.subjects.val (alloc.vec.Vec.len s'.subjects) triples.val.length →
      rdf_mapping.read_axiom triples kinds u s' (alloc.vec.Vec.len triples) = .ok (.Skip s')) :
    ∀ (n : Nat) (a : Usize) (bs : List ABlock) (s : rdf_mapping.State) (out : alloc.vec.Vec model.AnnotatedAxiom),
      triples.val.length - a.val = n → (∀ b ∈ bs, b ∈ all) →
      bs.Pairwise (fun b c => b.core.main < c.core.main) → bs.Pairwise AApart → (∀ b ∈ bs, a.val ≤ b.core.main) →
      (∀ b ∈ bs, ∀ i ∈ b.pos, i < triples.val.length) → ALoop triples s bs → out.val.length + bs.length ≤ Usize.max →
      ∃ (v : alloc.vec.Vec model.AnnotatedAxiom) (s' : rdf_mapping.State) (rs : List model.AnnotatedAxiom),
        rdf_mapping.axioms_from triples kinds a s out = .ok (some (v, s')) ∧
        v.val = out.val ++ rs ∧
        List.Forall₂ (fun r b => r.axiom = b.ax.axiom ∧ r.annotations.val.Perm b.ann.val) rs bs ∧
        s'.blanks.val = s.blanks.val ++ bs.flatMap ABlock.fresh ∧
        ∀ (i : Nat), i < triples.val.length → s'.used.val[i]? = some true := by
  intro n
  induction n with
  | zero =>
    intro a bs s out ends members sorted disjoint after inRange state room
    have done : triples.val.length ≤ a.val := by omega
    have empty : bs = [] := by
      cases bs with
      | nil => rfl
      | cons b rest =>
        have := inRange b (by simp) b.core.main (by simp [ABlock.pos, Block.pos])
        have := after b (by simp)
        omega
    subst empty
    refine ⟨out, s, [], axioms_from_end triples kinds s out a done, by simp, .nil, by simp, ?_⟩
    intro i hi
    have inside : i < s.used.val.length := by rw [state.length]; exact hi
    cases value : s.used.val[i]'inside with
    | true => simp [List.getElem?_eq_getElem inside, value]
    | false =>
      obtain ⟨b, member, -⟩ := state.covered i (by simp [List.getElem?_eq_getElem inside, value])
      simp at member
  | succ n ih =>
    intro a bs s out ends members sorted disjoint after inRange state room
    have more : a.val < triples.val.length := by omega
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := a) (y := 1#usize) (by have := triples.property; scalar_tac))
    have nextIs : next.val = a.val + 1 := by simpa using nextValue
    by_cases unused : s.used.val[a.val]? = some false
    · obtain ⟨b, member, inB⟩ := state.covered a.val unused
      by_cases isMain : a.val = b.core.main
      · -- the main triple of the first block
        obtain ⟨c, rest, rfl⟩ : ∃ c rest, bs = c :: rest := by
          cases bs with
          | nil => simp at member
          | cons c rest => exact ⟨c, rest, rfl⟩
        have bIsC : b = c := by
          rcases List.mem_cons.mp member with same | inRest
          · exact same
          · exfalso
            have lt := (List.pairwise_cons.mp sorted).1 b inRest
            have le := after c (by simp)
            omega
        subst bIsC
        obtain ⟨s1, s', v, readRun, annotateRun, vPerm, marked⟩ := step s b rest members state a isMain
        have pushRoom : out.val.length < Usize.max := by simp at room; omega
        obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec out (⟨v, b.ax.axiom⟩ : model.AnnotatedAxiom) pushRoom)
        have stepRun := axioms_from_annotated triples kinds a next s s1 s' out pushed ⟨v, b.ax.axiom⟩ more unused
          readRun annotateRun pushRoom push advance
        obtain ⟨w, s'', rs, run, wIs, rel, blanksIs, allUsed⟩ := ih next rest s' pushed (by omega)
          (fun c m => members c (List.mem_cons_of_mem _ m)) (List.pairwise_cons.mp sorted).2
          (List.pairwise_cons.mp disjoint).2
          (fun c m => by have := (List.pairwise_cons.mp sorted).1 c m; omega)
          (fun c m => inRange c (List.mem_cons_of_mem _ m))
          (aloop_after state (List.pairwise_cons.mp disjoint).1 marked)
          (by rw [contents]; simp at room ⊢; omega)
        refine ⟨w, s'', ⟨v, b.ax.axiom⟩ :: rs, by rw [stepRun, run], by rw [wIs, contents]; simp,
          List.Forall₂.cons ⟨rfl, vPerm⟩ rel, ?_, allUsed⟩
        rw [blanksIs, marked.blanks]
        simp
      · -- a triple of a later block, passed over
        have before : a.val < b.core.main := by have := after b member; omega
        have read := skip b (members b member) a.val inB before a s rfl state.complete
        have stepRun := axioms_from_skipped triples kinds s out a next more unused read advance
        obtain ⟨v, s', rs, run, vIs, rel, blanksIs, allUsed⟩ := ih next bs s out (by omega) members sorted disjoint
          (by
            intro c m
            have le := after c m
            rw [nextIs]
            apply Nat.lt_of_le_of_ne le
            intro same
            by_cases cb : c = b
            · subst cb
              exact isMain same
            · exact disjoint.forall m member cb a.val (by rw [same]; simp [ABlock.pos, Block.pos]) inB)
          inRange state room
        exact ⟨v, s', rs, by rw [stepRun, run], vIs, rel, blanksIs, allUsed⟩
    · -- a used triple
      have stepRun := axioms_from_used triples kinds s out a next more unused advance
      obtain ⟨v, s', rs, run, vIs, rel, blanksIs, allUsed⟩ := ih next bs s out (by omega) members sorted disjoint
        (by
          intro c m
          have le := after c m
          rw [nextIs]
          apply Nat.lt_of_le_of_ne le
          intro same
          exact unused (by rw [same]; exact state.free c m c.core.main (by simp [ABlock.pos, Block.pos])))
        inRange state room
      exact ⟨v, s', rs, by rw [stepRun, run], vIs, rel, blanksIs, allUsed⟩

/-! ### The triples of a block met before its main triple -/

theorem at_present {triples : List rdf.Triple} {pos : List Nat} {ps : List Pattern} (h : At triples pos ps)
    {i : Nat} (member : i ∈ pos) : ∃ t, triples[i]? = some t := by
  induction h with
  | nil => simp at member
  | @cons j p pos' ps' hp rest ih =>
    rcases List.mem_cons.mp member with here | inner
    · subst here
      obtain ⟨t, at_t, -⟩ := hp
      exact ⟨t, at_t⟩
    · exact ih inner

/-- The annotation triples of a node at their positions, with the positions and
    the annotations in order. -/
theorem tanns_zip {triples : List rdf.Triple} {y : Node} :
    ∀ {anns : List model.Annotation} {sx : Supply} {heads : List Pattern} {hs : List Nat},
      TAnns y anns sx heads sx → (∀ a ∈ anns, a.annotations.val = []) → At triples hs heads →
      (∀ r ∈ hs.zip anns, ∃ t n, triples[r.1]? = some t ∧ Matches ⟨y, r.2.property.iri.spelling.val, n⟩ t ∧
        AnnotationValueNode r.2.value n) ∧ (hs.zip anns).map Prod.fst = hs ∧ (hs.zip anns).map Prod.snd = anns := by
  intro anns
  induction anns with
  | nil =>
    intro sx heads hs h _ holds
    obtain ⟨rfl, -⟩ := tanns_nil h
    have : hs = [] := by have := at_length holds; simpa using this
    subst this
    simp
  | cons a rest ih =>
    intro sx heads hs h plain holds
    cases h with
    | cons _ _ _ _ sMid _ p q ha hrest =>
      obtain ⟨n, rfl, rfl, valueNode⟩ := tann_plain ha (plain a (by simp))
      obtain ⟨h0, hs', rfl, ⟨t, at_t, fits⟩, holdsRest⟩ : ∃ h0 hs', hs = h0 :: hs' ∧
          (∃ t, triples[h0]? = some t ∧ Matches ⟨y, a.property.iri.spelling.val, n⟩ t) ∧
          At triples hs' q := by
        cases holds with
        | cons hx rest => exact ⟨_, _, rfl, hx, rest⟩
      obtain ⟨heads', fsts, snds⟩ := ih hrest (fun b m => plain b (List.mem_cons_of_mem _ m)) holdsRest
      refine ⟨?_, by simp [fsts], by simp [snds]⟩
      intro r m
      simp only [List.zip_cons_cons, List.mem_cons] at m
      rcases m with rfl | inner
      · exact ⟨t, n, at_t, fits, valueNode⟩
      · exact heads' r inner

theorem mem_zip_any {α : Type} : ∀ {pos : List Nat} {l : List α}, pos.length = l.length → ∀ {i : Nat}, i ∈ pos →
    ∃ x, (i, x) ∈ pos.zip l
  | [], _, _, _, m => by simp at m
  | _ :: _, [], len, _, _ => by simp at len
  | j :: pos, x :: l, len, i, m => by
    rcases List.mem_cons.mp m with rfl | inner
    · exact ⟨x, by simp⟩
    · obtain ⟨y, my⟩ := mem_zip_any (by simpa using len) inner
      exact ⟨y, by simp [my]⟩

section

variable {o : model.RawOntology} {triples : alloc.vec.Vec rdf.Triple} {header : List Pattern} {bs : List ABlock}
  {supply : Supply}

/-- **The axiom loop passes over every triple of a block but its main one**:
    the triples of the expressions and lists of its axiom, the reification of
    its main triple and the annotation triples of the reifying node, which is
    typed `owl:Axiom`. -/
theorem agraph_skip (g : AGraph o triples.val header bs supply) {kinds : rdf_mapping.Kinds}
    (hk : KindsOf kinds o.axioms.val) {b : ABlock} (bIn : b ∈ bs) {i : Nat} (inB : i ∈ b.pos)
    (notMain : i ≠ b.core.main) (u : Usize) (s : rdf_mapping.State) (uIs : u.val = i)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length) :
    rdf_mapping.read_axiom triples kinds u s (alloc.vec.Vec.len triples) = .ok (.Skip s) := by
  rcases List.mem_append.mp inB with inCore | inA
  · have inRest : i ∈ b.core.rest := by
      simp only [Block.pos] at inCore
      rcases List.mem_cons.mp inCore with same | inRest
      · exact absurd same notMain
      · exact inRest
    exact block_rest_skip triples kinds (g.blocks b bIn).1.core ((agraph_split_at g) bIn).1 inRest u s uIs
  · obtain ⟨main, side, pIs, sides, facts, part⟩ := (agraph_shape g) bIn
    rcases part with ⟨-, apatsNil, -⟩ | ⟨-, x, heads, sx, afreshIs, apatsIs, tanns, -⟩
    · have aposNil : b.apos = [] := by
        have := (g.blocks b bIn).2.2.2
        rw [apatsNil] at this
        exact List.eq_nil_of_length_eq_zero this
      rw [aposNil] at inA
      simp at inA
    · obtain ⟨p0, p1, p2, p3, hs, aposIs, ⟨t0, at0, fits0⟩, ⟨t1, at1, fits1⟩, ⟨t2, at2, fits2⟩,
        ⟨t3, at3, fits3⟩, holdsHeads⟩ := (agraph_reified_layout g) bIn apatsIs
      rw [aposIs] at inA
      simp only [List.mem_cons] at inA
      rcases inA with same | same | same | same | inHeads
      · -- the typing of the reifying node
        have at_u : triples.val[u.val]? = some t0 := by rw [uIs, same]; exact at0
        rw [read_axiom_typing triples kinds u s _ t0 at_u fits0.2.1]
        exact typing_reifier_blank triples kinds u s _ t0 at_u x (subject_blank fits0.1) fits0.2.2
      · have at_u : triples.val[u.val]? = some t1 := by rw [uIs, same]; exact at1
        exact read_axiom_reification_skip triples kinds u s _ t1 at_u (Or.inl fits1.2.1)
      · have at_u : triples.val[u.val]? = some t2 := by rw [uIs, same]; exact at2
        exact read_axiom_reification_skip triples kinds u s _ t2 at_u (Or.inr (Or.inl fits2.2.1))
      · have at_u : triples.val[u.val]? = some t3 := by rw [uIs, same]; exact at3
        exact read_axiom_reification_skip triples kinds u s _ t3 at_u (Or.inr (Or.inr fits3.2.1))
      · -- an annotation triple of the reifying node
        obtain ⟨t, at_t⟩ := at_present holdsHeads inHeads
        have at_u : triples.val[u.val]? = some t := by rw [uIs]; exact at_t
        obtain ⟨q, qIn, fits⟩ := at_mem holdsHeads inHeads at_t
        have plainAll : ∀ a ∈ b.ann.val, a.annotations.val = [] := fun a m => ((g.blocks b bIn).1.plain a m).1
        obtain ⟨qSubject, a, aIn, predicate, -⟩ := tanns_heads tanns plainAll q qIn
        have row := annotation_row_axiom (ax := b.ax) (g.blocks b bIn).1.member (a := a) aIn
        have spelled : t.predicate.spelling = a.property.iri.spelling := vec_eq_of_val (fits.2.1.trans predicate)
        have allowed : Rowl.Vocabulary.EntityAllowed ⟨t.predicate.spelling⟩ .AnnotationProperty := by
          have same : (⟨t.predicate.spelling⟩ : model.Iri) = a.property.iri := iri_ext (by rw [spelled])
          rw [same]
          exact g.readable.vocabulary.2 _ row
        have kind : rdf_mapping.property_kind kinds t.predicate.spelling = .ok (some .Annotation) := by
          rw [spelled]
          exact (annotation_property_facts g.readable hk row).1
        exact read_axiom_head_skip triples kinds u s _ t at_u x (subject_blank (fits.1.trans qSubject)) allowed
          kind complete at0 fits0.1 fits0.2.1 fits0.2.2

end

/-! ### Annotated blocks in the order of their main triples -/

/-- Annotated blocks in the order of their main positions. -/
def sortABlocks (bs : List ABlock) : List ABlock := bs.mergeSort (fun b c => decide (b.core.main ≤ c.core.main))

theorem sort_ablocks_perm (bs : List ABlock) : (sortABlocks bs).Perm bs := List.mergeSort_perm _ _

theorem sort_ablocks_apart {bs : List ABlock} (disjoint : bs.Pairwise AApart) : (sortABlocks bs).Pairwise AApart :=
  (List.Perm.pairwise_iff (fun h i iy ix => h i ix iy) (sort_ablocks_perm bs).symm).mp disjoint

theorem sort_ablocks_sorted {bs : List ABlock} (disjoint : bs.Pairwise AApart) :
    (sortABlocks bs).Pairwise (fun b c => b.core.main < c.core.main) := by
  have le := List.pairwise_mergeSort (le := fun b c : ABlock => decide (b.core.main ≤ c.core.main))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega) (fun a b => by simp; omega) bs
  refine (le.and (sort_ablocks_apart disjoint)).imp ?_
  intro b c ⟨hle, hapart⟩
  simp only [decide_eq_true_eq] at hle
  apply Nat.lt_of_le_of_ne hle
  intro same
  exact hapart b.core.main (by simp [ABlock.pos, Block.pos]) (by rw [same]; simp [ABlock.pos, Block.pos])

/-! ### The mapping of a graph of an annotated ontology in any order -/

/-- **The reverse RDF mapping reads back every readable annotated ontology from
    its triples in any order.** For an ontology with ontology annotations and
    annotated axioms that the reverse mapping reads back (`ReadableAnnotated`),
    a graph whose triples are a permutation of the triples of its forward
    mapping (`TOntology`), with blank nodes distinct from each other and from
    the anonymous individuals the assertions are about (`FreshSupply`), is
    mapped to that ontology: the same identity, the same imports, annotations
    and axioms up to their order, each axiom with its annotations up to their
    order, and the blank nodes of the forward mapping up to their order. -/
theorem map_graph_complete_annotated_perm (graph : rdf.RawGraph) (o : model.RawOntology) (supply : Supply)
    (patterns : List Pattern) (readable : ReadableAnnotated o) (forward : TOntology o supply patterns)
    (distinct : supply.Nodup) (fresh : FreshSupply o supply)
    (image : ∃ ts, List.Forall₂ Matches patterns ts ∧ graph.triples.val.Perm ts) :
    ∃ m, rdf_mapping.map_graph graph = .ok (some m) ∧ m.ontology.identity = o.identity ∧
      m.ontology.imports.val.Perm o.imports.val ∧ m.ontology.annotations.val.Perm o.annotations.val ∧
      (∃ axs : List model.AnnotatedAxiom, axs.Perm o.axioms.val ∧
        List.Forall₂ (fun r a => r.axiom = a.axiom ∧ r.annotations.val.Perm a.annotations.val)
          m.ontology.axioms.val axs) ∧
      m.blanks.val.Perm supply := by
  obtain ⟨ts, matching, perm⟩ := image
  obtain ⟨ps, psPerm, psImage⟩ := forall2_perm matching perm.symm
  have lengthEq : graph.triples.val.length = patterns.length := by
    rw [← psPerm.length_eq]; exact (List.Forall₂.length_eq psImage).symm
  have holdsPs : At graph.triples.val (List.range' 0 ps.length) ps :=
    forall2_at ps graph.triples.val 0 (by simpa using psImage)
  obtain ⟨pos, posPerm, holdsAll⟩ := perm_positions psPerm holdsPs
  have posNodup : pos.Nodup := posPerm.nodup_iff.mpr (List.nodup_range' (s := 0) (n := ps.length))
  have psLength : ps.length = graph.triples.val.length := by rw [psPerm.length_eq, lengthEq]
  have posMem : ∀ i, i ∈ pos ↔ i < graph.triples.val.length := by
    intro i; rw [posPerm.mem_iff, List.mem_range'_1, psLength]; omega
  obtain ⟨header, axiomPs, rest, theader, taxioms, split⟩ := forward
  obtain ⟨heads, headerIs, restIs, anonymousFacts, namedFacts⟩ := header_annotated readable.annotations theader
  rw [restIs] at taxioms
  subst headerIs
  rw [split] at holdsAll
  obtain ⟨posH, posA, rfl, holdsH, holdsA⟩ := at_split holdsAll
  obtain ⟨nodupH, nodupA, apartHA⟩ := List.nodup_append.mp posNodup
  obtain ⟨bs, mapIs, freshIs, patsIs, disjoint, each, covers⟩ :=
    annotated_position_blocks readable graph.triples taxioms (fun ax m => m) posA holdsA nodupA
  simp only [List.append_nil] at freshIs
  have total : graph.triples.val.length ≤ Usize.max := graph.triples.property
  have plainOnt : ∀ a ∈ o.annotations.val, a.annotations.val = [] := fun a m => (readable.annotations a m).1
  -- the facts about the graph
  have g : AGraph o graph.triples.val (headerPatterns o ++ heads) bs supply :=
    { readable := readable
      headerFacts := by
        intro q qIn
        rcases List.mem_append.mp qIn with inH | inA
        · obtain ⟨iri, version, named, subject, which⟩ := header_patterns_shape inH
          refine ⟨iri, version, named, subject, ?_⟩
          rcases which with typing | version | imports
          · exact Or.inl typing
          · exact Or.inr (Or.inl version)
          · exact Or.inr (Or.inr (Or.inl imports))
        · cases identity : o.identity with
          | Anonymous => rw [(anonymousFacts identity).1] at inA; simp at inA
          | Named iri version =>
            obtain ⟨subject, a, aIn, predicate, -⟩ := tanns_heads (namedFacts iri version identity) plainOnt q inA
            exact ⟨iri, version, rfl, subject, Or.inr (Or.inr (Or.inr ⟨a, aIn, predicate⟩))⟩
      blocks := fun b m => ⟨(each b m).1, (each b m).2.1, (each b m).2.2.1, (each b m).2.2.2.1⟩
      axiomsIs := mapIs
      sourced := by
        intro i t at_i
        have inside : i < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
        rcases List.mem_append.mp ((posMem i).mpr inside) with inH | inA
        · exact Or.inl (at_mem holdsH inH at_i)
        · obtain ⟨c, cIn, ic⟩ := covers i inA
          exact Or.inr ⟨c, cIn, ic⟩
      supplyIs := freshIs
      distinct := distinct
      fresh := fresh
      disjoint := disjoint }
  have supplyCount : supply.length ≤ axiomPs.length := by
    rw [freshIs, patsIs]
    exact (agraph_flat_fresh_le g) bs (fun c m => m)
  have axiomsLength : axiomPs.length ≤ graph.triples.val.length := by
    rw [lengthEq, split, List.length_append]; omega
  -- the declarations
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
  have hk : KindsOf kinds o.axioms.val := (agraph_graph_kinds g) c cPos kinds kindsEnd
  -- the indexes
  obtain ⟨v1, unusedRun⟩ := unused_total (alloc.vec.Vec.len graph.triples) (alloc.vec.Vec.new Bool)
  have v1Is := unused_spec _ _ v1 unusedRun
  simp at v1Is
  obtain ⟨v2, bucketsRun, v2Length, v2Empty⟩ := empty_buckets_spec (T := Usize) c (alloc.vec.Vec.new _) (by simp)
    (by simp)
  obtain ⟨v3, subjectsRun⟩ := subjects_from_total graph.triples 0#usize v2
  obtain ⟨lengthV3, complete⟩ := subjects_from_spec graph.triples 0#usize v2 v3 (by rw [v2Length]; exact cPos)
    (fun b member => by rw [v2Empty b member]; simp)
    (fun i t node bucket low => by simp at low) subjectsRun
  have sortedV3 : BucketsSorted v3.val := subjects_from_sorted graph.triples 0#usize v2 v3
    (by rw [v2Length]; exact cPos) (fun b member => by rw [v2Empty b member]; simp)
    (fun b member k kIn => by rw [v2Empty b member] at kIn; simp at kIn)
    (fun b member => by rw [v2Empty b member]; simp) subjectsRun
  obtain ⟨v4, sourcesRun⟩ := sources_from_total graph.triples 0#usize v2
  obtain ⟨lengthV4, sourcesComplete⟩ := sources_from_spec graph.triples 0#usize v2 v4
    (by rw [v2Length]; exact cPos) (fun b member => by rw [v2Empty b member]; simp)
    (fun i t x bucket low => by simp at low) sourcesRun
  have lenV3 : alloc.vec.Vec.len v3 = alloc.vec.Vec.len v2 := by
    apply UScalar.eq_of_val_eq
    simp [alloc.vec.Vec.len_val, lengthV3]
  have lenV4 : alloc.vec.Vec.len v4 = alloc.vec.Vec.len v2 := by
    apply UScalar.eq_of_val_eq
    simp [alloc.vec.Vec.len_val, lengthV4]
  rw [← lenV3] at complete
  rw [← lenV4] at sourcesComplete
  -- the axiom loop over the blocks in the order of their main triples, from a
  -- state where exactly the triples of the axioms are unused
  have sbPerm : (sortABlocks bs).Perm bs := sort_ablocks_perm bs
  have loop : ∀ st : rdf_mapping.State,
      SubjectsComplete graph.triples.val st.subjects.val (alloc.vec.Vec.len st.subjects) graph.triples.val.length →
      BucketsSorted st.subjects.val →
      SourcesComplete graph.triples.val st.sources.val (alloc.vec.Vec.len st.sources) graph.triples.val.length →
      st.used.val.length = graph.triples.val.length →
      (∀ (i : Nat), i < graph.triples.val.length → (st.used.val[i]? = some false ↔ i ∈ posA)) →
      st.blanks.val = [] →
      ∃ v s', rdf_mapping.axioms_from graph.triples kinds 0#usize st (alloc.vec.Vec.new _) = .ok (some (v, s')) ∧
        (∃ axs : List model.AnnotatedAxiom, axs.Perm o.axioms.val ∧
          List.Forall₂ (fun r a => r.axiom = a.axiom ∧ r.annotations.val.Perm a.annotations.val) v.val axs) ∧
        s'.blanks.val.Perm supply ∧
        ∀ (i : Nat), i < graph.triples.val.length → s'.used.val[i]? = some true := by
    intro st completeSt sortedSt sourcesSt lengthSt usedSt blanksSt
    have inRange : ∀ b ∈ sortABlocks bs, ∀ i ∈ b.pos, i < graph.triples.val.length := by
      intro b m i inB
      exact (posMem i).mp (List.mem_append_right _ ((each b (sbPerm.subset m)).2.2.2.2 i inB))
    have state : ALoop graph.triples st (sortABlocks bs) :=
      { complete := completeSt
        sorted := sortedSt
        sources := sourcesSt
        length := lengthSt
        free := fun b m i inB => by
          have inA := (each b (sbPerm.subset m)).2.2.2.2 i inB
          exact (usedSt i ((posMem i).mp (List.mem_append_right _ inA))).mpr inA
        covered := fun i unused => by
          have inside : i < graph.triples.val.length := by
            rw [← lengthSt]; exact (List.getElem?_eq_some_iff.mp unused).1
          obtain ⟨c, cIn, ic⟩ := covers i ((usedSt i inside).mp unused)
          exact ⟨c, sbPerm.symm.subset cIn, ic⟩
        room := by
          rw [blanksSt, (sbPerm.flatMap_right ABlock.fresh).length_eq, ← freshIs]
          simp
          omega }
    have axiomsCount : (sortABlocks bs).length ≤ Usize.max := by
      have := o.axioms.property
      have lengths : bs.length = o.axioms.val.length := by rw [← mapIs, List.length_map]
      rw [sbPerm.length_eq]
      omega
    obtain ⟨v, s', rs, run, vIs, rel, blanksIs, allUsed⟩ := annotated_loop_perm graph.triples kinds bs
      (fun s b rest members state a aIs => by
        obtain ⟨s1, s', v, readRun, annotateRun, vPerm, -, marked⟩ :=
          (agraph_step g) hk s b rest members state a aIs
        exact ⟨s1, s', v, readRun, annotateRun, vPerm, marked⟩)
      (fun b bIn i inB lt u s' uIs completeS => (agraph_skip g) hk bIn inB (Nat.ne_of_lt lt) u s' uIs completeS)
      _ 0#usize (sortABlocks bs) st (alloc.vec.Vec.new _) rfl (fun b m => sbPerm.subset m)
      (sort_ablocks_sorted disjoint) (sort_ablocks_apart disjoint) (fun b m => by simp) inRange state
      (by simp; omega)
    have vRs : v.val = rs := by rw [vIs]; simp
    refine ⟨v, s', run, ⟨(sortABlocks bs).map ABlock.ax, ?_, ?_⟩, ?_, allUsed⟩
    · rw [← mapIs]; exact sbPerm.map ABlock.ax
    · rw [vRs]
      exact List.forall₂_map_right_iff.mpr rel
    · rw [blanksIs, blanksSt, freshIs]
      simpa using sbPerm.flatMap_right ABlock.fresh
  -- the header
  cases identity : o.identity with
  | Anonymous =>
    obtain ⟨headsNil, importsNil, annotationsNil⟩ := anonymousFacts identity
    subst headsNil
    have headerNil : headerPatterns o = [] := by simp [headerPatterns, identity]
    have posHNil : posH = [] := by
      have := at_length holdsH
      rw [headerNil] at this
      simpa using this
    have inAxioms : ∀ i, i < graph.triples.val.length → i ∈ posA := by
      intro i hi
      have := (posMem i).mpr hi
      rw [posHNil] at this
      simpa using this
    have headerRun : rdf_mapping.find_header graph.triples v1 0#usize = .ok none := by
      apply find_header_none
      intro i t _ at_i typed onto iri isIri
      have inside : i < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
      obtain ⟨b, bIn, ib⟩ := covers i (inAxioms i inside)
      exact (agraph_block_not_ontology g) bIn at_i ib typed onto iri isIri
    obtain ⟨v, s', axiomsRun, axsRel, blanksIs, allUsed⟩ := loop
      { used := v1, blanks := alloc.vec.Vec.new _, subjects := v3, sources := v4 } complete sortedV3
      sourcesComplete (by simp [v1Is])
      (fun i hi => by simp [v1Is, List.getElem?_replicate, hi, inAxioms i hi])
      (by simp)
    have allRun := all_read_used graph.triples s'.used 0#usize (fun i _ hi => allUsed i hi)
    refine ⟨⟨⟨.Anonymous, alloc.vec.Vec.new _, alloc.vec.Vec.new _, v⟩, s'.blanks⟩, ?_, rfl, ?_, ?_, axsRel,
      blanksIs⟩
    · rw [rdf_mapping.map_graph]
      simp only [countRun, bind_ok, kindBucketsRun, kindsRun, unusedRun, bucketsRun, subjectsRun, sourcesRun,
        headerRun]
      have axiomsRun' : rdf_mapping.axioms_from graph.triples kinds 0#usize
          { used := v1, blanks := alloc.vec.Vec.new rdf.BlankNode, subjects := v3, sources := v4 }
          (alloc.vec.Vec.new model.AnnotatedAxiom) = .ok (some (v, s')) := axiomsRun
      rw [axiomsRun']
      simp only [bind_ok]
      change (Std.bind (rdf_mapping.all_read graph.triples s'.used 0#usize) _) = _
      rw [allRun, bind_ok]
      rfl
    · simp [importsNil]
    · simp [annotationsNil]
  | Named iri version =>
    have tannsH := namedFacts iri version identity
    -- the patterns of the header
    let typingP : Pattern := ⟨iriNode iri, rdfType, .iri owlOntology⟩
    let vps : List Pattern := version.toList.map (fun v => ⟨iriNode iri, owlVersionIRI, iriNode v⟩)
    let ips : List Pattern := o.imports.val.map (fun i => ⟨iriNode iri, owlImports, iriNode i⟩)
    have hdrIs : headerPatterns o = typingP :: (vps ++ ips) := by
      cases version <;> simp [headerPatterns, identity, typingP, vps, ips]
    obtain ⟨posHP, posHeads, rfl, holdsHP, holdsHeads⟩ := at_split holdsH
    rw [hdrIs] at holdsHP
    obtain ⟨h0, posVI, rfl, ⟨t0, at0, fits0⟩, holdsVI⟩ : ∃ h0 posVI, posHP = h0 :: posVI ∧
        (∃ t, graph.triples.val[h0]? = some t ∧ Matches typingP t) ∧ At graph.triples.val posVI (vps ++ ips) := by
      cases holdsHP with
      | cons hx rest => exact ⟨_, _, rfl, hx, rest⟩
    obtain ⟨posV, posI, rfl, holdsV, holdsI⟩ := at_split holdsVI
    obtain ⟨nodupHP, nodupHeads, apartHP⟩ := List.nodup_append.mp nodupH
    obtain ⟨h0Out, nodupVI⟩ := List.nodup_cons.mp nodupHP
    obtain ⟨nodupV, nodupI, apartVI⟩ := List.nodup_append.mp nodupVI
    have lenI : posI.length = o.imports.val.length := by rw [at_length holdsI]; simp [ips]
    obtain ⟨headsAt, fstsIs, sndsIs⟩ := tanns_zip tannsH plainOnt holdsHeads
    have lenHeads : posHeads.length = o.annotations.val.length := by
      have l1 := congrArg List.length fstsIs
      have l2 := congrArg List.length sndsIs
      simp only [List.length_map] at l1 l2
      omega
    -- the triple typing the ontology IRI
    obtain ⟨iri0, isIri0, spelled0⟩ : ∃ iri0, t0.subject = .Iri iri0 ∧ iri0.spelling = iri.spelling := by
      have subject := fits0.1
      cases h : t0.subject with
      | Iri iri0 =>
        rw [h] at subject
        simp only [iriNode, subjectView, Node.iri.injEq, typingP] at subject
        exact ⟨iri0, rfl, vec_eq_of_val subject⟩
      | Blank _ => rw [h] at subject; simp [iriNode, subjectView, typingP] at subject
    have aboutIs : ∀ t : rdf.Triple, subjectView t.subject = iriNode iri →
        subjectView t.subject = .iri iri0.spelling.val := by
      intro t h; rw [h, spelled0]; rfl
    have h0Inside : h0 < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at0).1
    have unused0 : v1.val[h0]? = some false := by simp [v1Is, List.getElem?_replicate, h0Inside]
    obtain ⟨hdr, hdrVal, headerRun⟩ := find_header_first graph.triples v1 h0 t0 at0 unused0 fits0.2.1 fits0.2.2
      iri0 isIri0 (h0 - (0#usize : Usize).val) 0#usize rfl (by simp)
      (by
        intro i t _ high at_i typed onto iri' isIri
        have inside : i < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
        rcases List.mem_append.mp ((posMem i).mpr inside) with inH | inA
        · rcases List.mem_append.mp inH with inHP | inHeads
          · rcases List.mem_cons.mp inHP with same | inVI
            · omega
            · obtain ⟨q, qIn, fits⟩ := at_mem holdsVI inVI at_i
              have predicate := fits.2.1
              rw [typed] at predicate
              simp only [List.mem_append, vps, ips, List.mem_map, Option.mem_toList] at qIn
              rcases qIn with ⟨v, -, rfl⟩ | ⟨j, -, rfl⟩
              · simp [rdfType, owlVersionIRI] at predicate
              · simp [rdfType, owlImports] at predicate
          · obtain ⟨q, qIn, fits⟩ := at_mem holdsHeads inHeads at_i
            obtain ⟨-, a, aIn, predicate, -⟩ := tanns_heads tannsH plainOnt q qIn
            have notType := (annotation_property_facts readable hk (annotation_row_ontology aIn)).2 rdfType
              (by simp [mappingVocabulary])
            exact absurd (predicate.symm.trans (fits.2.1.symm.trans typed)) notType
        · obtain ⟨c, cIn, ic⟩ := covers i inA
          exact (agraph_block_not_ontology g) cIn at_i ic typed onto iri' isIri)
    let st0 : rdf_mapping.State := { used := v1, blanks := alloc.vec.Vec.new _, subjects := v3, sources := v4 }
    let st1 : rdf_mapping.State := { st0 with used := st0.used.set hdr true }
    have m01 : Marked st0 st1 (fun i => i = h0) [] := by
      have := marked_take st0 hdr
      rw [hdrVal] at this
      exact this
    have st0Unused : ∀ i, i < graph.triples.val.length → st0.used.val[i]? = some false := by
      intro i hi
      simp [st0, v1Is, List.getElem?_replicate, hi]
    have st1Unused : ∀ i, i < graph.triples.val.length → i ≠ h0 → st1.used.val[i]? = some false :=
      fun i hi ne => marked_unused m01 (st0Unused i hi) ne
    have st1Used : st1.used.val[h0]? = some true :=
      marked_used m01 (by simp [st0, v1Is]; exact h0Inside) rfl
    -- the version
    obtain ⟨vrem, vremIn, vremAll, vremIs⟩ : ∃ vrem : Option (Nat × model.Iri),
        (∀ p ∈ vrem, p.1 ∈ posV ∧ version = some p.2) ∧ (∀ i ∈ posV, ∃ v, vrem = some (i, v)) ∧
        (vrem.map Prod.snd).or none = version := by
      have len := at_length holdsV
      cases versionIs : version with
      | none =>
        have : posV = [] := by simpa [vps, versionIs] using len
        exact ⟨none, by simp, by simp [this], rfl⟩
      | some v =>
        obtain ⟨hv, rfl⟩ : ∃ hv, posV = [hv] := List.length_eq_one_iff.mp (by simpa [vps, versionIs] using len)
        exact ⟨some (hv, v), by simp, by simp, rfl⟩
    -- the header read
    obtain ⟨ver, imp, ann, sH, partsRun, verIs, impPerm, annPerm, mH⟩ := header_parts_rest_a graph.triples kinds
      iri0.spelling (agraph_no_annotation_kind g) _ 0#usize st1 none (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)
      vrem (posI.zip o.imports.val) (posHeads.zip o.annotations.val) rfl
      { imports := by
          intro p m
          have inI := (List.of_mem_zip m).1
          have inside : p.1 < graph.triples.val.length := (posMem p.1).mp
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _ inI))))
          have ne : p.1 ≠ h0 := fun same => h0Out (by rw [← same]; exact List.mem_append_right _ inI)
          obtain ⟨t, at_t, fits⟩ := at_zip holdsI p m
          exact ⟨by simp, st1Unused p.1 inside ne, t, at_t, aboutIs t fits.1, fits.2.1, fits.2.2⟩
        nodup := by rw [List.map_fst_zip (by omega)]; exact nodupI
        version := by
          intro p m
          obtain ⟨inV, versionIs⟩ := vremIn p m
          have inside : p.1 < graph.triples.val.length := (posMem p.1).mp
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_left _ inV))))
          have ne : p.1 ≠ h0 := fun same => h0Out (by rw [← same]; exact List.mem_append_left _ inV)
          obtain ⟨t, at_t⟩ : ∃ t, graph.triples.val[p.1]? = some t := ⟨_, List.getElem?_eq_getElem inside⟩
          obtain ⟨q, qIn, fits⟩ := at_mem holdsV inV at_t
          simp only [vps, versionIs, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at qIn
          subst qIn
          exact ⟨by simp, st1Unused p.1 inside ne, t, at_t, aboutIs t fits.1, fits.2.1, fits.2.2⟩
        annotations := by
          intro p m
          have inHeads := (List.of_mem_zip m).1
          have inside : p.1 < graph.triples.val.length :=
            (posMem p.1).mp (List.mem_append_left _ (List.mem_append_right _ inHeads))
          have ne : p.1 ≠ h0 := fun same => apartHP h0 (by simp) p.1 inHeads same.symm
          obtain ⟨t, n, at_t, fits, valueNode⟩ := headsAt p m
          exact ⟨by simp, st1Unused p.1 inside ne, t, n, at_t, aboutIs t fits.1, fits.2.1, fits.2.2, valueNode⟩
        props := by
          intro p m
          have aIn : p.2 ∈ o.annotations.val := (List.of_mem_zip m).2
          obtain ⟨plainA, literals⟩ := readable.annotations p.2 aIn
          obtain ⟨kind, notVocabulary⟩ := annotation_property_facts readable hk (annotation_row_ontology aIn)
          exact ⟨plainA, literals, kind, notVocabulary _ (by simp [mappingVocabulary]),
            notVocabulary _ (by simp [mappingVocabulary])⟩
        anodup := by rw [fstsIs]; exact nodupHeads
        other := by
          intro i t _ at_i unused about
          have inside : i < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
          rcases List.mem_append.mp ((posMem i).mpr inside) with inH | inA
          · rcases List.mem_append.mp inH with inHP | inHeads
            · rcases List.mem_cons.mp inHP with same | inVI
              · rw [same, st1Used] at unused
                cases unused
              · rcases List.mem_append.mp inVI with inV | inI
                · exact Or.inr (Or.inl (vremAll i inV))
                · exact Or.inl (mem_zip_of_mem lenI inI)
            · exact Or.inr (Or.inr (Or.inl (mem_zip_any lenHeads inHeads)))
          · obtain ⟨c, cIn, ic⟩ := covers i inA
            exact Or.inr (Or.inr (Or.inr
              ((agraph_block_header_skip g) hk identity cIn at_i ic (by rw [about, spelled0])))) }
      (by simp) (by simp) (by simp)
    have impIs : imp.val.Perm o.imports.val := by
      rw [List.map_snd_zip (by omega)] at impPerm
      simpa using impPerm
    have annIs : ann.val.Perm o.annotations.val := by
      rw [sndsIs] at annPerm
      simpa using annPerm
    -- every triple of the header is used, and only those
    have usedH : ∀ (i : Nat), i < graph.triples.val.length → (sH.used.val[i]? = some false ↔ i ∈ posA) := by
      intro i hi
      have inside : i < st1.used.val.length := by simp [st1, st0, alloc.vec.Vec.set_val_eq, v1Is]; exact hi
      constructor
      · intro unused
        apply Classical.byContradiction
        intro notA
        have inH : i ∈ (h0 :: (posV ++ posI)) ++ posHeads := by
          rcases List.mem_append.mp ((posMem i).mpr hi) with inH | inA
          · exact inH
          · exact absurd inA notA
        have usedNow : sH.used.val[i]? = some true := by
          rcases List.mem_append.mp inH with inHP | inHeads
          · rcases List.mem_cons.mp inHP with same | inVI
            · exact (mH.used i inside).mpr (Or.inl (by rw [same]; exact st1Used))
            · rcases List.mem_append.mp inVI with inV | inI
              · exact marked_used mH inside (Or.inr (Or.inl (vremAll i inV)))
              · exact marked_used mH inside (Or.inl (mem_zip_of_mem lenI inI))
          · exact marked_used mH inside (Or.inr (Or.inr (mem_zip_any lenHeads inHeads)))
        rw [usedNow] at unused
        cases unused
      · intro inA
        have notH : i ∉ (h0 :: (posV ++ posI)) ++ posHeads := fun inH => apartHA i inH i inA rfl
        have ne : i ≠ h0 := fun same => notH (by rw [same]; simp)
        refine marked_unused mH (st1Unused i hi ne) ?_
        rintro (⟨v, m⟩ | ⟨v, m⟩ | ⟨a, m⟩)
        · exact notH (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.of_mem_zip m).1)))
        · exact notH (List.mem_append_left _
            (List.mem_cons_of_mem _ (List.mem_append_left _ (vremIn (i, v) (by rw [m]; simp)).1)))
        · exact notH (List.mem_append_right _ (List.of_mem_zip m).1)
    -- the axioms
    obtain ⟨v, s', axiomsRun, axsRel, blanksIs, allUsed⟩ := loop sH
      (by rw [mH.subjects]; exact complete) (by rw [mH.subjects]; exact sortedV3)
      (by rw [mH.sources]; exact sourcesComplete)
      (by rw [mH.length]; simp [st1, st0, alloc.vec.Vec.set_val_eq, v1Is]) usedH
      (by rw [mH.blanks]; simp [st1, st0])
    have allRun := all_read_used graph.triples s'.used 0#usize (fun i _ hi => allUsed i hi)
    refine ⟨⟨⟨.Named ⟨iri0.spelling⟩ ver, imp, ann, v⟩, s'.blanks⟩, ?_, ?_, impIs, annIs, axsRel, blanksIs⟩
    · rw [rdf_mapping.map_graph]
      simp only [countRun, bind_ok, kindBucketsRun, kindsRun, unusedRun, bucketsRun, subjectsRun, sourcesRun,
        headerRun, alloc.vec.Vec.index_slice_index, main_lookup graph.triples hdr t0 (by rw [hdrVal]; exact at0),
        isIri0, take_correct]
      have partsRun' : rdf_mapping.header_parts graph.triples kinds iri0.spelling 0#usize
          { used := v1.set hdr true, blanks := alloc.vec.Vec.new rdf.BlankNode, subjects := v3, sources := v4 }
          none (alloc.vec.Vec.new model.Iri) (alloc.vec.Vec.new model.Annotation) =
          .ok (some (ver, imp, ann, sH)) := partsRun
      rw [partsRun']
      simp only [bind_ok]
      change (Std.bind (rdf_mapping.iri_of iri0.spelling) _) = _
      rw [iri_of_identity, bind_ok]
      simp only [axiomsRun, bind_ok]
      change (Std.bind (rdf_mapping.all_read graph.triples s'.used 0#usize) _) = _
      rw [allRun, bind_ok]
      rfl
    · rw [verIs, vremIs]
      simp only [model.OntologyIdentity.Named.injEq, and_true]
      exact iri_ext (by rw [spelled0])

end Rowl.RdfReadAnnotatedPermuted
