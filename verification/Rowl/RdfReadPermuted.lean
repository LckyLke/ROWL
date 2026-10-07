import Rowl.RdfReadOntology

/-!
# Completeness of the reverse RDF mapping for graphs in any order

The triples of a graph come in any order. For every ontology that the reverse
mapping reads back (`ReadableOntology`), a graph whose triples are a permutation
of the triples of its forward mapping is mapped to that ontology, its axioms and
imports up to their order and its blank nodes up to their order
(`map_graph_complete_perm`). The reader needs no change for this:

* `read_axiom` passes over the triples of expressions and lists that come
  before the main triple of their axiom (`side_skip`), so the axiom loop reads
  each axiom when it meets its main triple (`block_rest_skip`, with the blocks
  sorted by their main positions, `sort_blocks_sorted`);
* `find_header` finds the only triple typing an IRI `owl:Ontology` wherever it
  is (`find_header_first`), and `header_parts` takes the version and the
  imports wherever they are (`header_parts_rest`).
-/

namespace Rowl.RdfReadPermuted
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust Rowl.RdfMapping Rowl.RdfReadIndexes Rowl.RdfReadExpressions
  Rowl.RdfReadAxioms Rowl.RdfReadOntology

/-! ### The predicates of main triples -/

/-- The predicates that `read_axiom` dispatches on. -/
def specialPredicates : List (List U8) :=
  [rdfType, rdfsSubClassOf, owlEquivalentClass, owlDisjointWith, owlDisjointUnionOf, rdfsSubPropertyOf,
    owlPropertyChainAxiom, owlEquivalentProperty, owlPropertyDisjointWith, owlInverseOf, rdfsDomain, rdfsRange,
    owlSameAs, owlDifferentFrom, owlHasKey]

set_option maxRecDepth 16384 in
/-- The predicates of the triples of expressions and lists are reserved, name no
    built-in entity and are not dispatched on. -/
theorem side_predicates_structural : ∀ key ∈ sideVocabulary ++ owl2Facets,
    Rowl.Vocabulary.Reserved key ∧ Rowl.Builtins.role key = none ∧ key ∉ specialPredicates := by
  decide

attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

theorem structural_true (predicate : alloc.vec.Vec U8) (reserved : Rowl.Vocabulary.Reserved predicate.val)
    (notBuiltin : Rowl.Builtins.role predicate.val = none) : rdf_mapping.structural predicate = .ok true := by
  rw [rdf_mapping.structural]
  simp [Rowl.Vocabulary.reserved_iri_total_correct, reserved, Rowl.Builtins.builtin_kind_total_correct, notBuiltin]

/-- A triple with a reserved predicate that is not dispatched on and names no
    property is passed over. -/
theorem read_axiom_structural (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (reserved : Rowl.Vocabulary.Reserved t.predicate.spelling.val)
    (notBuiltin : Rowl.Builtins.role t.predicate.spelling.val = none)
    (notSpecial : t.predicate.spelling.val ∉ specialPredicates) :
    rdf_mapping.read_axiom triples kinds a s fuel = .ok (.Skip s) := by
  have n : ∀ K ∈ specialPredicates, t.predicate.spelling.val ≠ K := fun K m same => notSpecial (same ▸ m)
  have n1 := n rdfType (by simp [specialPredicates])
  have n2 := n rdfsSubClassOf (by simp [specialPredicates])
  have n3 := n owlEquivalentClass (by simp [specialPredicates])
  have n4 := n owlDisjointWith (by simp [specialPredicates])
  have n5 := n owlDisjointUnionOf (by simp [specialPredicates])
  have n6 := n rdfsSubPropertyOf (by simp [specialPredicates])
  have n7 := n owlPropertyChainAxiom (by simp [specialPredicates])
  have n8 := n owlEquivalentProperty (by simp [specialPredicates])
  have n9 := n owlPropertyDisjointWith (by simp [specialPredicates])
  have n10 := n owlInverseOf (by simp [specialPredicates])
  have n11 := n rdfsDomain (by simp [specialPredicates])
  have n12 := n rdfsRange (by simp [specialPredicates])
  have n13 := n owlSameAs (by simp [specialPredicates])
  have n14 := n owlDifferentFrom (by simp [specialPredicates])
  have n15 := n owlHasKey (by simp [specialPredicates])
  simp only [rdfType, rdfsSubClassOf, owlEquivalentClass, owlDisjointWith, owlDisjointUnionOf, rdfsSubPropertyOf,
    owlPropertyChainAxiom, owlEquivalentProperty] at n1 n2 n3 n4 n5 n6 n7 n8
  simp only [owlPropertyDisjointWith, owlInverseOf, rdfsDomain, rdfsRange, owlSameAs, owlDifferentFrom,
    owlHasKey] at n9 n10 n11 n12 n13 n14 n15
  have isStructural := structural_true t.predicate.spelling reserved notBuiltin
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, n1, n2,
    n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, isStructural]

theorem blank_subject_true (t : rdf.Triple) (x : rdf.BlankNode) (subject : t.subject = .Blank x) :
    rdf_mapping.blank_subject t = .ok true := by
  rw [rdf_mapping.blank_subject]; simp [subject]

/-- The typing triple of a restriction, class or datatype node is passed over. -/
theorem typing_blank (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t) (x : rdf.BlankNode)
    (subject : t.subject = .Blank x)
    (which : objectView t.object = .iri owlRestriction ∨ objectView t.object = .iri owlClass ∨
      objectView t.object = .iri rdfsDatatype) :
    rdf_mapping.typing triples kinds a s fuel = .ok (.Skip s) := by
  have blank := blank_subject_true t x subject
  rw [rdf_mapping.typing]
  rcases which with h | h | h <;> simp only [owlRestriction, owlClass, rdfsDatatype] at h <;>
    simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val, h,
      blank]

/-- The triples of expressions and lists are passed over by `read_axiom`. -/
theorem side_skip (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t) {q : Pattern}
    (side : SideKind q) (fits : Matches q t) {y : rdf.BlankNode} (blank : q.subject = .blank y) :
    rdf_mapping.read_axiom triples kinds a s fuel = .ok (.Skip s) := by
  have subject : t.subject = .Blank y := subject_blank (fits.1.trans blank)
  rcases side with inSide | inFacets | inverse | ⟨typed, which⟩
  · obtain ⟨reserved, notBuiltin, notSpecial⟩ := side_predicates_structural q.predicate
      (List.mem_append_left _ inSide)
    rw [← fits.2.1] at reserved notBuiltin notSpecial
    exact read_axiom_structural triples kinds a s fuel t at_t reserved notBuiltin notSpecial
  · obtain ⟨reserved, notBuiltin, notSpecial⟩ := side_predicates_structural q.predicate
      (List.mem_append_right _ inFacets)
    rw [← fits.2.1] at reserved notBuiltin notSpecial
    exact read_axiom_structural triples kinds a s fuel t at_t reserved notBuiltin notSpecial
  · rw [read_axiom_inverse_properties triples kinds a s fuel t at_t (by rw [fits.2.1]; exact inverse),
      rdf_mapping.inverse_properties]
    simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, subject]
  · rw [read_axiom_typing triples kinds a s fuel t at_t (by rw [fits.2.1]; exact typed)]
    exact typing_blank triples kinds a s fuel t at_t y subject (by rw [fits.2.2]; simpa using which)

/-! ### Positions of the patterns in a permuted graph -/

/-- The patterns of a permutation of a list hold at a permutation of its positions. -/
theorem perm_positions {triples : List rdf.Triple} :
    ∀ {ps qs : List Pattern}, ps.Perm qs → ∀ {pos : List Nat}, At triples pos ps →
      ∃ pos', pos'.Perm pos ∧ At triples pos' qs := by
  intro ps qs perm
  induction perm with
  | nil => intro pos holds; exact ⟨pos, List.Perm.refl _, holds⟩
  | cons x _ ih =>
    intro pos holds
    obtain ⟨i, rest, rfl, hx, hrest⟩ : ∃ i rest, pos = i :: rest ∧
        (∃ t, triples[i]? = some t ∧ Matches x t) ∧ At triples rest _ := by
      cases holds with
      | cons hx hrest => exact ⟨_, _, rfl, hx, hrest⟩
    obtain ⟨rest', perm', holds'⟩ := ih hrest
    exact ⟨i :: rest', perm'.cons i, List.Forall₂.cons hx holds'⟩
  | swap x y l =>
    intro pos holds
    cases holds with
    | cons hy rest =>
      cases rest with
      | cons hx rest' =>
        exact ⟨_, List.Perm.swap _ _ _, List.Forall₂.cons hx (List.Forall₂.cons hy rest')⟩
  | trans _ _ ih1 ih2 =>
    intro pos holds
    obtain ⟨pos1, perm1, holds1⟩ := ih1 holds
    obtain ⟨pos2, perm2, holds2⟩ := ih2 holds1
    exact ⟨pos2, perm2.trans perm1, holds2⟩

/-! ### The blocks of the axioms at any positions -/

/-- The blocks of the axioms whose triples the graph holds at the positions `pos`. -/
theorem position_blocks {o : model.RawOntology} (readable : ReadableOntology o) (triples : alloc.vec.Vec rdf.Triple) :
    ∀ {axs : List model.AnnotatedAxiom} {s0 : Supply} {ps : List Pattern} {s1 : Supply}, TAxioms axs s0 ps s1 →
    (∀ ax ∈ axs, ax ∈ o.axioms.val) → ∀ (pos : List Nat), At triples.val pos ps → pos.Nodup →
    ∃ bs : List Block,
      bs.map (fun b => (⟨alloc.vec.Vec.new _, b.ax⟩ : model.AnnotatedAxiom)) = axs ∧
      s0 = bs.flatMap Block.fresh ++ s1 ∧ bs.Pairwise Apart ∧
      (∀ b ∈ bs, ImageBlock o b ∧ At triples.val b.pos b.pats ∧ b.pos.Nodup ∧ ∀ i ∈ b.pos, i ∈ pos) ∧
      (∀ i ∈ pos, ∃ b ∈ bs, i ∈ b.pos) := by
  intro axs s0 ps s1 h
  induction h with
  | nil s =>
    intro _ pos holds _
    have empty : pos = [] := by have := at_length holds; simpa using this
    subst empty
    exact ⟨[], by simp, by simp, by simp, by simp, by simp⟩
  | cons ax rest s s1 s2 p q head tail ih =>
    intro members pos holds nodup
    have axIn := members ax (by simp)
    have plain := (readable.axioms ax axIn).1
    have tax := plain_axiom head plain
    obtain ⟨main, side, f, pIs, eqf, sides, facts⟩ := block_shape readable axIn tax
    obtain ⟨posP, posQ, rfl, holdsP, holdsQ⟩ := at_split holds
    have nodupQ := (List.nodup_append.mp nodup).2.1
    obtain ⟨bs, mapIs, freshIs, disjoint, each, covers⟩ :=
      ih (fun b m => members b (List.mem_cons_of_mem _ m)) posQ holdsQ nodupQ
    obtain ⟨m0, restP, rfl⟩ : ∃ m0 restP, posP = m0 :: restP := by
      cases posP with
      | nil => have := at_length holdsP; rw [pIs] at this; simp at this
      | cons m0 restP => exact ⟨m0, restP, rfl⟩
    let b : Block := { ax := ax.axiom, main := m0, rest := restP, pats := p, fresh := f }
    have bPos : b.pos = m0 :: restP := rfl
    refine ⟨b :: bs, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, mapIs, b]
      rw [plain_annotated ax plain]
    · simp only [List.flatMap_cons, b]
      rw [eqf, freshIs, List.append_assoc]
    · refine List.Pairwise.cons ?_ disjoint
      intro c m i ib ic
      have inQ := (each c m).2.2.2 i ic
      rw [bPos] at ib
      exact (List.nodup_append.mp nodup).2.2 i ib i inQ rfl
    · intro c m
      rcases List.mem_cons.mp m with rfl | inRest
      · refine ⟨⟨⟨ax, axIn, rfl, plain⟩, ⟨s1, by rw [← eqf]; exact tax⟩, ⟨main, side, pIs, sides, facts⟩⟩,
          holdsP, (List.nodup_append.mp nodup).1, fun i m' => List.mem_append_left _ m'⟩
      · obtain ⟨image, holdsC, nodupC, inPos⟩ := each c inRest
        exact ⟨image, holdsC, nodupC, fun i m' => List.mem_append_right _ (inPos i m')⟩
    · intro i m
      rcases List.mem_append.mp m with inP | inQ
      · exact ⟨b, by simp, inP⟩
      · obtain ⟨c, cIn, ic⟩ := covers i inQ
        exact ⟨c, List.mem_cons_of_mem _ cIn, ic⟩

/-- Blocks in the order of their main positions. -/
def sortBlocks (bs : List Block) : List Block := bs.mergeSort (fun b c => decide (b.main ≤ c.main))

theorem sort_blocks_perm (bs : List Block) : (sortBlocks bs).Perm bs := List.mergeSort_perm _ _

theorem sort_blocks_sorted {bs : List Block} (disjoint : bs.Pairwise Apart) :
    (sortBlocks bs).Pairwise (fun b c => b.main < c.main) := by
  have le := List.pairwise_mergeSort (le := fun b c : Block => decide (b.main ≤ c.main))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega) (fun a b => by simp; omega) bs
  have apart : (sortBlocks bs).Pairwise Apart :=
    (List.Perm.pairwise_iff (fun h i iy ix => h i ix iy) (sort_blocks_perm bs).symm).mp disjoint
  refine (le.and apart).imp ?_
  intro b c ⟨hle, hapart⟩
  simp only [decide_eq_true_eq] at hle
  apply Nat.lt_of_le_of_ne hle
  intro same
  exact hapart b.main (by simp [Block.pos]) (by rw [same]; simp [Block.pos])

/-! ### The header in any order -/

/-- The header reader passes over a used triple. -/
theorem header_parts_passed (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8) (version : Option model.Iri) (imports : alloc.vec.Vec model.Iri)
    (annotations : alloc.vec.Vec model.Annotation) (index next : Usize) (s : rdf_mapping.State)
    (more : index.val < triples.val.length) (used : s.used.val[index.val]? ≠ some false)
    (advance : (index + 1#usize : Result Usize) = .ok next) :
    rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
      rdf_mapping.header_parts triples kinds ontology next s version imports annotations := by
  rw [rdf_mapping.header_parts]
  simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, is_used_correct, used, advance]

/-- The header reader passes over a triple about another subject. -/
theorem header_parts_elsewhere (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8) (version : Option model.Iri) (imports : alloc.vec.Vec model.Iri)
    (annotations : alloc.vec.Vec model.Annotation) (index next : Usize) (s : rdf_mapping.State) (t : rdf.Triple)
    (at_t : triples.val[index.val]? = some t) (unused : s.used.val[index.val]? = some false)
    (elsewhere : subjectView t.subject ≠ .iri ontology.val) (advance : (index + 1#usize : Result Usize) = .ok next) :
    rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
      rdf_mapping.header_parts triples kinds ontology next s version imports annotations := by
  have more : index.val < triples.val.length := (List.getElem?_eq_some_iff.mp at_t).1
  rw [rdf_mapping.header_parts]
  simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, is_used_correct, unused, alloc.vec.Vec.index_slice_index,
    main_lookup triples index t at_t, about_iri_correct, elsewhere, advance]

/-- The header reader passes over a triple about the ontology IRI that is no
    part of the header. -/
theorem header_parts_other (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8) (version : Option model.Iri) (imports : alloc.vec.Vec model.Iri)
    (annotations : alloc.vec.Vec model.Annotation) (index next : Usize) (s : rdf_mapping.State) (t : rdf.Triple)
    (at_t : triples.val[index.val]? = some t) (unused : s.used.val[index.val]? = some false)
    (about : subjectView t.subject = .iri ontology.val) (notVersion : t.predicate.spelling.val ≠ owlVersionIRI)
    (notImports : t.predicate.spelling.val ≠ owlImports)
    (kind : ∃ r, rdf_mapping.property_kind kinds t.predicate.spelling = .ok r ∧ r ≠ some .Annotation)
    (advance : (index + 1#usize : Result Usize) = .ok next) :
    rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
      rdf_mapping.header_parts triples kinds ontology next s version imports annotations := by
  have more : index.val < triples.val.length := (List.getElem?_eq_some_iff.mp at_t).1
  obtain ⟨r, kindRun, notAnnotation⟩ := kind
  simp only [owlVersionIRI] at notVersion
  simp only [owlImports] at notImports
  rw [rdf_mapping.header_parts]
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, unused, ne_eq,
    not_true_eq_false, decide_false, Bool.false_eq_true, bind_ok, alloc.vec.Vec.index_slice_index,
    main_lookup triples index t at_t, about_iri_correct, about, decide_true, lift, same_correct, array_slice_val,
    notVersion, notImports, kindRun]
  rcases r with _ | k
  · simp [advance]
  · cases k with
    | Object => simp [advance]
    | Data => simp [advance]
    | Annotation => exact absurd rfl notAnnotation

/-- The header reader takes an import. -/
theorem header_parts_import (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8) (version : Option model.Iri) (imports : alloc.vec.Vec model.Iri)
    (annotations : alloc.vec.Vec model.Annotation) (index next : Usize) (s : rdf_mapping.State) (t : rdf.Triple)
    (at_t : triples.val[index.val]? = some t) (unused : s.used.val[index.val]? = some false)
    (about : subjectView t.subject = .iri ontology.val) (predicate : t.predicate.spelling.val = owlImports)
    (j : model.Iri) (object : objectView t.object = iriNode j) (room : imports.val.length < Usize.max)
    (pushed : alloc.vec.Vec model.Iri) (push : alloc.vec.Vec.push imports j = .ok pushed)
    (advance : (index + 1#usize : Result Usize) = .ok next) :
    rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
      rdf_mapping.header_parts triples kinds ontology next { s with used := s.used.set index true } version pushed
        annotations := by
  have more : index.val < triples.val.length := (List.getElem?_eq_some_iff.mp at_t).1
  rw [rdf_mapping.header_parts]
  have predicate' := predicate
  simp only [owlImports] at predicate'
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, unused, ne_eq,
    not_true_eq_false, decide_false, Bool.false_eq_true, bind_ok, alloc.vec.Vec.index_slice_index,
    main_lookup triples index t at_t, about_iri_correct, about, decide_true, lift, same_correct, array_slice_val,
    predicate']
  simp [node_iri_complete t.object j object, usize_max_val, room, push, advance, take_correct]

/-- The unused triples about the ontology IRI from `index` on: the imports `rem`
    and the version `vrem` at their positions, and triples that are no part of
    the header. -/
structure HeaderRest (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (ontology : alloc.vec.Vec U8)
    (used : List Bool) (index : Nat) (vrem : Option (Nat × model.Iri)) (rem : List (Nat × model.Iri)) : Prop where
  imports : ∀ p ∈ rem, index ≤ p.1 ∧ used[p.1]? = some false ∧ ∃ t, triples.val[p.1]? = some t ∧
    subjectView t.subject = .iri ontology.val ∧ t.predicate.spelling.val = owlImports ∧
    objectView t.object = iriNode p.2
  nodup : (rem.map Prod.fst).Nodup
  version : ∀ p ∈ vrem, index ≤ p.1 ∧ used[p.1]? = some false ∧ ∃ t, triples.val[p.1]? = some t ∧
    subjectView t.subject = .iri ontology.val ∧ t.predicate.spelling.val = owlVersionIRI ∧
    objectView t.object = iriNode p.2
  other : ∀ (i : Nat) (t : rdf.Triple), index ≤ i → triples.val[i]? = some t → used[i]? = some false →
    subjectView t.subject = .iri ontology.val → (∃ v, (i, v) ∈ rem) ∨ (∃ v, vrem = some (i, v)) ∨
      (t.predicate.spelling.val ≠ owlVersionIRI ∧ t.predicate.spelling.val ≠ owlImports ∧
        ∃ r, rdf_mapping.property_kind kinds t.predicate.spelling = .ok r ∧ r ≠ some .Annotation)

theorem header_rest_step {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {ontology : alloc.vec.Vec U8} {used used' : List Bool} {index : Nat} {vrem vrem' : Option (Nat × model.Iri)}
    {rem rem' : List (Nat × model.Iri)} (h : HeaderRest triples kinds ontology used index vrem rem)
    (keep : ∀ (i : Nat), index < i → used[i]? = some false → used'[i]? = some false)
    (back : ∀ (i : Nat), used'[i]? = some false → used[i]? = some false)
    (remSub : ∀ p ∈ rem', p ∈ rem) (remNot : ∀ p ∈ rem', p.1 ≠ index) (nodup' : (rem'.map Prod.fst).Nodup)
    (vSub : ∀ p ∈ vrem', p ∈ vrem) (vNot : ∀ p ∈ vrem', p.1 ≠ index)
    (covered : ∀ p ∈ rem, p.1 ≠ index → p ∈ rem') (vcovered : ∀ p ∈ vrem, p.1 ≠ index → p ∈ vrem') :
    HeaderRest triples kinds ontology used' (index + 1) vrem' rem' where
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
  other := by
    intro i t low at_i unused about
    rcases h.other i t (by omega) at_i (back i unused) about with ⟨v, m⟩ | ⟨v, m⟩ | rest
    · exact Or.inl ⟨v, covered (i, v) m (by simp only; omega)⟩
    · refine Or.inr (Or.inl ⟨v, ?_⟩)
      exact Option.mem_def.mp (vcovered (i, v) (Option.mem_def.mpr m) (by simp only; omega))
    · exact Or.inr (Or.inr rest)

theorem header_rest_end {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {ontology : alloc.vec.Vec U8} {used : List Bool} {index : Nat} {vrem : Option (Nat × model.Iri)}
    {rem : List (Nat × model.Iri)} (h : HeaderRest triples kinds ontology used index vrem rem)
    (done : triples.val.length ≤ index) : rem = [] ∧ vrem = none := by
  constructor
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

/-- **The header reader takes the version and the imports wherever they are.**
    From `index` on, `header_parts` takes the version `vrem` and the imports
    `rem`, in the order of their positions, and uses exactly their triples. -/
theorem header_parts_rest (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8) (annotations : alloc.vec.Vec model.Annotation) :
    ∀ (n : Nat) (index : Usize) (s : rdf_mapping.State) (version : Option model.Iri)
      (imports : alloc.vec.Vec model.Iri) (vrem : Option (Nat × model.Iri)) (rem : List (Nat × model.Iri)),
      triples.val.length - index.val = n → HeaderRest triples kinds ontology s.used.val index.val vrem rem →
      (vrem ≠ none → version = none) → imports.val.length + rem.length ≤ Usize.max →
      ∃ ver imp s', rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
          .ok (some (ver, imp, annotations, s')) ∧
        ver = (vrem.map Prod.snd).or version ∧ imp.val.Perm (imports.val ++ rem.map Prod.snd) ∧
        Marked s s' (fun i => (∃ v, (i, v) ∈ rem) ∨ ∃ v, vrem = some (i, v)) [] := by
  intro n
  induction n with
  | zero =>
    intro index s version imports vrem rem ends rest _ _
    have done : ¬ index.val < triples.val.length := by omega
    obtain ⟨rfl, rfl⟩ := header_rest_end rest (by omega)
    refine ⟨version, imports, s, ?_, rfl, by simp, marked_same (marked_refl s) (fun i => by simp)⟩
    rw [rdf_mapping.header_parts]; simp [UScalar.lt_equiv, done]
  | succ n ih =>
    intro index s version imports vrem rem ends rest versionFree room
    have more : index.val < triples.val.length := by omega
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := triples.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have ends' : triples.val.length - next.val = n := by omega
    obtain ⟨t, at_t⟩ : ∃ t, triples.val[index.val]? = some t := ⟨_, List.getElem?_eq_getElem more⟩
    -- the triples of the imports and the version at `index` are this triple
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
    have importsVersion : owlImports ≠ owlVersionIRI := by simp [owlImports, owlVersionIRI]
    -- passing over the triple at `index`
    have passOver : ∀ (s' : rdf_mapping.State), (∀ (i : Nat), index.val < i → s.used.val[i]? = some false →
          s'.used.val[i]? = some false) → (∀ (i : Nat), s'.used.val[i]? = some false → s.used.val[i]? = some false) →
        (∀ p ∈ rem, p.1 ≠ index.val) → (∀ p ∈ vrem, p.1 ≠ index.val) →
        HeaderRest triples kinds ontology s'.used.val next.val vrem rem := by
      intro s' keep back remNot vNot
      rw [nextIs]
      exact header_rest_step rest keep back (fun p m => m) remNot rest.nodup (fun p m => m) vNot (fun p m _ => m)
        (fun p m _ => m)
    by_cases unused : s.used.val[index.val]? = some false
    · by_cases about : subjectView t.subject = .iri ontology.val
      · by_cases isVersion : t.predicate.spelling.val = owlVersionIRI
        · -- the version
          obtain ⟨v, rfl⟩ : ∃ v, vrem = some (index.val, v) := by
            rcases rest.other index.val t (le_refl _) at_t unused about with ⟨v, m⟩ | ⟨v, m⟩ | ⟨notV, -⟩
            · exfalso
              have := (importAt _ m rfl).2.2.1
              rw [isVersion] at this
              exact importsVersion this.symm
            · exact ⟨v, m⟩
            · exact absurd isVersion notV
          have versionNone := versionFree (by simp)
          subst versionNone
          obtain ⟨-, -, -, object⟩ := versionAt (index.val, v) (by simp) rfl
          have step := header_parts_version triples kinds ontology imports annotations index next s t at_t unused
            about isVersion v object advance
          have mTake := marked_take s index
          obtain ⟨ver, imp, s', run, verIs, impPerm, marked⟩ := ih next { s with used := s.used.set index true }
            (some v) imports none rem ends'
            (by
              rw [nextIs]
              refine header_rest_step rest (fun i low u => marked_unused mTake u (by show i ≠ index.val; omega))
                (fun i u => marked_back mTake u) (fun p m => m) ?_ rest.nodup (by simp) (by simp)
                (fun p m _ => m) ?_
              · intro p m same
                have := (importAt p m same).2.2.1
                rw [isVersion] at this
                exact importsVersion this.symm
              · intro p m ne
                simp only [Option.mem_def, Option.some.injEq] at m
                subst m
                exact absurd rfl ne)
            (by simp) room
          refine ⟨ver, imp, s', by rw [step]; exact run, by simp [verIs], by simpa using impPerm, ?_⟩
          refine marked_same (marked_trans mTake marked) (fun i => ?_)
          constructor
          · rintro (same | (⟨w, m⟩ | ⟨w, m⟩))
            · exact Or.inr ⟨v, by rw [same]⟩
            · exact Or.inl ⟨w, m⟩
            · simp at m
          · rintro (⟨w, m⟩ | ⟨w, m⟩)
            · exact Or.inr (Or.inl ⟨w, m⟩)
            · simp only [Option.some.injEq, Prod.mk.injEq] at m
              exact Or.inl m.1.symm
        · by_cases isImports : t.predicate.spelling.val = owlImports
          · -- an import
            obtain ⟨j, m⟩ : ∃ j, (index.val, j) ∈ rem := by
              rcases rest.other index.val t (le_refl _) at_t unused about with ⟨v, m⟩ | ⟨v, m⟩ | ⟨-, notI, -⟩
              · exact ⟨v, m⟩
              · exfalso
                exact isVersion (versionAt (index.val, v) (by rw [m]; simp) rfl).2.2.1
              · exact absurd isImports notI
            obtain ⟨-, -, -, object⟩ := importAt _ m rfl
            have remPos : 0 < rem.length := List.length_pos_of_mem m
            have importsRoom : imports.val.length < Usize.max := by omega
            obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec imports j importsRoom)
            have step := header_parts_import triples kinds ontology version imports annotations index next s t at_t
              unused about isImports j object importsRoom pushed push advance
            have mTake := marked_take s index
            have permErase := List.perm_cons_erase m
            have nodupE := (permErase.map Prod.fst).nodup_iff.mp rest.nodup
            simp only [List.map_cons, List.nodup_cons] at nodupE
            obtain ⟨notIn, nodupTail⟩ := nodupE
            obtain ⟨ver, imp, s', run, verIs, impPerm, marked⟩ := ih next { s with used := s.used.set index true }
              version pushed vrem (rem.erase (index.val, j)) ends'
              (by
                rw [nextIs]
                refine header_rest_step rest (fun i low u => marked_unused mTake u (by show i ≠ index.val; omega))
                  (fun i u => marked_back mTake u) (fun p m' => List.mem_of_mem_erase m') ?_ nodupTail
                  (fun p m' => m') ?_ ?_ (fun p m' _ => m')
                · intro p m' same
                  exact notIn (List.mem_map.mpr ⟨p, m', same⟩)
                · intro p m' same
                  exact isVersion ((versionAt p m' same).2.2.1 ▸ isImports ▸ rfl)
                · intro p m' ne
                  refine (List.mem_erase_of_ne ?_).mpr m'
                  intro e
                  rw [e] at ne
                  exact ne rfl)
              versionFree
              (by
                rw [contents, List.length_erase_of_mem m]
                simp only [List.length_append, List.length_singleton]
                omega)
            refine ⟨ver, imp, s', by rw [step]; exact run, verIs, ?_, ?_⟩
            · refine impPerm.trans ?_
              rw [contents, List.append_assoc]
              refine List.Perm.append_left imports.val ?_
              have := (permErase.map Prod.snd).symm
              simpa using this
            · refine marked_same (marked_trans mTake marked) (fun i => ?_)
              constructor
              · rintro (same | (⟨w, m'⟩ | ⟨w, m'⟩))
                · exact Or.inl ⟨j, by rw [same]; exact m⟩
                · exact Or.inl ⟨w, List.mem_of_mem_erase m'⟩
                · exact Or.inr ⟨w, m'⟩
              · rintro (⟨w, m'⟩ | ⟨w, m'⟩)
                · by_cases same : i = index.val
                  · exact Or.inl same
                  · refine Or.inr (Or.inl ⟨w, (List.mem_erase_of_ne ?_).mpr m'⟩)
                    intro e
                    simp only [Prod.mk.injEq] at e
                    exact same e.1
                · exact Or.inr (Or.inr ⟨w, m'⟩)
          · -- a triple about the ontology IRI that is no part of the header
            obtain ⟨notV, notI, kind⟩ : t.predicate.spelling.val ≠ owlVersionIRI ∧
                t.predicate.spelling.val ≠ owlImports ∧
                ∃ r, rdf_mapping.property_kind kinds t.predicate.spelling = .ok r ∧ r ≠ some .Annotation := by
              rcases rest.other index.val t (le_refl _) at_t unused about with ⟨v, m⟩ | ⟨v, m⟩ | facts
              · exact absurd (importAt _ m rfl).2.2.1 isImports
              · exact absurd (versionAt (index.val, v) (by rw [m]; simp) rfl).2.2.1 isVersion
              · exact facts
            have step := header_parts_other triples kinds ontology version imports annotations index next s t at_t
              unused about notV notI kind advance
            obtain ⟨ver, imp, s', run, verIs, impPerm, marked⟩ := ih next s version imports vrem rem ends'
              (passOver s (fun _ _ u => u) (fun _ u => u) (fun p m same => isImports (importAt p m same).2.2.1)
                (fun p m same => isVersion (versionAt p m same).2.2.1))
              versionFree room
            exact ⟨ver, imp, s', by rw [step]; exact run, verIs, impPerm, marked⟩
      · -- a triple about another subject
        have step := header_parts_elsewhere triples kinds ontology version imports annotations index next s t at_t
          unused about advance
        obtain ⟨ver, imp, s', run, verIs, impPerm, marked⟩ := ih next s version imports vrem rem ends'
          (passOver s (fun _ _ u => u) (fun _ u => u) (fun p m same => about (importAt p m same).2.1)
            (fun p m same => about (versionAt p m same).2.1))
          versionFree room
        exact ⟨ver, imp, s', by rw [step]; exact run, verIs, impPerm, marked⟩
    · -- a used triple
      have step := header_parts_passed triples kinds ontology version imports annotations index next s more unused
        advance
      obtain ⟨ver, imp, s', run, verIs, impPerm, marked⟩ := ih next s version imports vrem rem ends'
        (passOver s (fun _ _ u => u) (fun _ u => u) (fun p m same => unused (importAt p m same).1)
          (fun p m same => unused (versionAt p m same).1))
        versionFree room
      exact ⟨ver, imp, s', by rw [step]; exact run, verIs, impPerm, marked⟩

/-- The first unused triple typing an IRI `owl:Ontology` is the header. -/
theorem find_header_first (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool) (h0 : Nat)
    (t0 : rdf.Triple) (at0 : triples.val[h0]? = some t0) (unused0 : used.val[h0]? = some false)
    (typed0 : t0.predicate.spelling.val = rdfType) (onto0 : objectView t0.object = .iri owlOntology)
    (iri0 : rdf.RdfIri) (subject0 : t0.subject = .Iri iri0) :
    ∀ (n : Nat) (index : Usize), h0 - index.val = n → index.val ≤ h0 →
      (∀ (i : Nat) (t : rdf.Triple), index.val ≤ i → i < h0 → triples.val[i]? = some t →
        t.predicate.spelling.val = rdfType → objectView t.object = .iri owlOntology → ∀ iri, t.subject ≠ .Iri iri) →
      ∃ header : Usize, header.val = h0 ∧ rdf_mapping.find_header triples used index = .ok (some header) := by
  intro n
  induction n with
  | zero =>
    intro index ends le _
    have same : index.val = h0 := by omega
    subst same
    exact ⟨index, rfl, find_header_at triples used index t0 at0 unused0 typed0 onto0 iri0 subject0⟩
  | succ n ih =>
    intro index ends le none
    have inside0 : h0 < triples.val.length := (List.getElem?_eq_some_iff.mp at0).1
    have more : index.val < triples.val.length := by omega
    have at_t : triples.val[index.val]? = some triples.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := triples.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨header, headerIs, rest⟩ := ih next (by omega) (by omega) (fun i t low high => none i t (by omega) high)
    refine ⟨header, headerIs, ?_⟩
    rw [rdf_mapping.find_header]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok,
      alloc.vec.Vec.index_slice_index, main_lookup triples index _ at_t, lift, same_correct, array_slice_val,
      object_is_correct, advance, rest]
    have here := none index.val _ (le_refl _) (by omega) at_t
    simp only [rdfType, owlOntology] at here
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    rename_i typed onto
    cases subject : triples.val[index.val].subject with
    | Iri iri => exact absurd subject (here (by simpa using typed) (by simpa using onto) iri)
    | Blank _ => simp [subject, advance, rest]

/-! ### Positions of a permuted graph -/

/-- A list related elementwise to a list is related elementwise, after a
    permutation, to every permutation of that list. -/
theorem forall2_perm {α β : Type} {R : α → β → Prop} {xs : List α} {bs cs : List β}
    (h : List.Forall₂ R xs bs) (perm : bs.Perm cs) : ∃ xs', xs'.Perm xs ∧ List.Forall₂ R xs' cs := by
  induction perm generalizing xs with
  | nil => exact ⟨xs, List.Perm.refl _, h⟩
  | cons x _ ih =>
    cases h with
    | cons hx rest =>
      obtain ⟨xs', perm', h'⟩ := ih rest
      exact ⟨_ :: xs', perm'.cons _, List.Forall₂.cons hx h'⟩
  | swap x y l =>
    cases h with
    | cons hy rest =>
      cases rest with
      | cons hx rest' =>
        exact ⟨_, List.Perm.swap _ _ _, List.Forall₂.cons hx (List.Forall₂.cons hy rest')⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨as1, perm1, h1⟩ := ih1 h
    obtain ⟨as2, perm2, h2⟩ := ih2 h1
    exact ⟨as2, perm2.trans perm1, h2⟩

theorem sort_blocks_apart {bs : List Block} (disjoint : bs.Pairwise Apart) : (sortBlocks bs).Pairwise Apart :=
  (List.Perm.pairwise_iff (fun h i iy ix => h i ix iy) (sort_blocks_perm bs).symm).mp disjoint

/-- The patterns at the positions of a list of IRIs. -/
theorem at_zip {triples : List rdf.Triple} {f : model.Iri → Pattern} :
    ∀ {pos : List Nat} {l : List model.Iri}, At triples pos (l.map f) →
      ∀ p ∈ pos.zip l, ∃ t, triples[p.1]? = some t ∧ Matches (f p.2) t
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | i :: pos, x :: l, h => by
    intro p m
    simp only [List.map_cons] at h
    obtain ⟨hx, rest⟩ := List.forall₂_cons.mp h
    simp only [List.zip_cons_cons, List.mem_cons] at m
    rcases m with rfl | inner
    · exact hx
    · exact at_zip rest p inner

theorem mem_zip_of_mem : ∀ {pos : List Nat} {l : List model.Iri}, pos.length = l.length → ∀ {i : Nat}, i ∈ pos →
    ∃ x, (i, x) ∈ pos.zip l
  | [], _, _, _, m => by simp at m
  | _ :: _, [], len, _, _ => by simp at len
  | j :: pos, x :: l, len, i, m => by
    rcases List.mem_cons.mp m with rfl | inner
    · exact ⟨x, by simp⟩
    · obtain ⟨y, my⟩ := mem_zip_of_mem (by simpa using len) inner
      exact ⟨y, by simp [my]⟩

/-- No triple of a block types an IRI `owl:Ontology`. -/
theorem block_not_ontology {o : model.RawOntology} {b : Block} (image : ImageBlock o b) {q : Pattern}
    (member : q ∈ b.pats) {t : rdf.Triple} (fits : Matches q t) (typed : t.predicate.spelling.val = rdfType)
    (onto : objectView t.object = .iri owlOntology) (iri : rdf.RdfIri) : t.subject ≠ .Iri iri := by
  intro isIri
  obtain ⟨main, side, -, sides, facts, rfl | inSide⟩ := block_pattern image member
  · have subject := fits.1
    rw [isIri] at subject
    exact facts.notOntology (by rw [← fits.2.1]; exact typed) _ subject.symm (by rw [← fits.2.2]; exact onto)
  · obtain ⟨y, -, about⟩ := (sides q inSide).2
    have subject := fits.1
    rw [isIri, about] at subject
    simp [subjectView] at subject

/-- A triple of a block about the IRI of a named ontology is no part of the header. -/
theorem block_not_header {o : model.RawOntology} {iri : model.Iri} {version : Option model.Iri}
    (identity : o.identity = .Named iri version) {kinds : rdf_mapping.Kinds} (hk : KindsOf kinds o.axioms.val)
    {b : Block} (image : ImageBlock o b) {q : Pattern} (member : q ∈ b.pats) {t : rdf.Triple} (fits : Matches q t)
    (about : subjectView t.subject = .iri iri.spelling.val) :
    t.predicate.spelling.val ≠ owlVersionIRI ∧ t.predicate.spelling.val ≠ owlImports ∧
      ∃ r, rdf_mapping.property_kind kinds t.predicate.spelling = .ok r ∧ r ≠ some .Annotation := by
  have qSubject : q.subject = iriNode iri := by rw [← fits.1, about]; rfl
  obtain ⟨main, side, -, sides, facts, rfl | inSide⟩ := block_pattern image member
  · obtain ⟨notVersion, notImports, notAnnotation⟩ := facts.header iri version identity qSubject
    rw [fits.2.1]
    exact ⟨notVersion, notImports, property_kind_other hk (iri := ⟨t.predicate.spelling⟩) (notAnnotation _ fits.2.1)⟩
  · obtain ⟨y, -, subject⟩ := (sides q inSide).2
    rw [qSubject] at subject
    simp [iriNode] at subject

/-- Every position of a block other than its main one holds a triple of an
    expression or a list, which `read_axiom` passes over. -/
theorem block_rest_skip {o : model.RawOntology} (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    {b : Block} (image : ImageBlock o b) (holds : At triples.val b.pos b.pats) {i : Nat} (inRest : i ∈ b.rest)
    (u : Usize) (s : rdf_mapping.State) (uIs : u.val = i) :
    rdf_mapping.read_axiom triples kinds u s (alloc.vec.Vec.len triples) = .ok (.Skip s) := by
  obtain ⟨main, side, pIs, sides, -⟩ := image.shape
  rw [pIs] at holds
  simp only [Block.pos] at holds
  obtain ⟨-, holdsRest⟩ := List.forall₂_cons.mp holds
  obtain ⟨t, at_t⟩ : ∃ t, triples.val[i]? = some t := by
    obtain ⟨k, hk, kIs⟩ := List.getElem_of_mem inRest
    have kLt : k < side.length := by rw [← at_length holdsRest]; exact hk
    obtain ⟨-, t, at_t, -⟩ := at_get holdsRest (k := k) (i := i) (by rw [List.getElem?_eq_getElem hk, kIs])
    exact ⟨t, at_t⟩
  obtain ⟨q, qIn, fits⟩ := at_mem holdsRest inRest at_t
  obtain ⟨kind, y, -, blank⟩ := sides q qIn
  exact side_skip triples kinds u s _ t (by rw [uIs]; exact at_t) kind fits blank

/-! ### The mapping of a graph in any order -/

/-- **The reverse RDF mapping reads back every readable ontology from its
    triples in any order.** For an ontology that the reverse mapping reads back
    (`ReadableOntology`), a graph whose triples are a permutation of the triples
    of its forward mapping (`TOntology`), with blank nodes distinct from each
    other and from the anonymous individuals the assertions are about
    (`FreshSupply`), is mapped to that ontology: the same identity and
    annotations, the same imports and axioms up to their order, and the blank
    nodes of the forward mapping up to their order. -/
theorem map_graph_complete_perm (graph : rdf.RawGraph) (o : model.RawOntology) (supply : Supply)
    (patterns : List Pattern) (readable : ReadableOntology o) (forward : TOntology o supply patterns)
    (distinct : supply.Nodup) (fresh : FreshSupply o supply)
    (image : ∃ ts, List.Forall₂ Matches patterns ts ∧ graph.triples.val.Perm ts) :
    ∃ m, rdf_mapping.map_graph graph = .ok (some m) ∧ m.ontology.identity = o.identity ∧
      m.ontology.imports.val.Perm o.imports.val ∧ m.ontology.annotations = o.annotations ∧
      m.ontology.axioms.val.Perm o.axioms.val ∧ m.blanks.val.Perm supply := by
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
  obtain ⟨headerIs, restIs⟩ := header_of readable.annotations theader
  rw [restIs] at taxioms
  subst headerIs
  rw [split] at holdsAll
  obtain ⟨posH, posA, rfl, holdsH, holdsA⟩ := at_split holdsAll
  obtain ⟨nodupH, nodupA, apartHA⟩ := List.nodup_append.mp posNodup
  obtain ⟨bs, mapIs, freshIs, disjoint, each, covers⟩ :=
    position_blocks readable graph.triples taxioms (fun ax m => m) posA holdsA nodupA
  simp only [List.append_nil] at freshIs
  have total : graph.triples.val.length ≤ Usize.max := graph.triples.property
  have images : ∀ b ∈ bs, ImageBlock o b := fun b m => (each b m).1
  have imagesAt : ∀ b ∈ bs, ImageBlock o b ∧ At graph.triples.val b.pos b.pats :=
    fun b m => ⟨(each b m).1, (each b m).2.1⟩
  have sourced : Sourced graph.triples.val (headerPatterns o) bs := by
    intro i t at_i
    have inside : i < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
    rcases List.mem_append.mp ((posMem i).mpr inside) with inH | inA
    · exact Or.inl (at_mem holdsH inH at_i)
    · obtain ⟨c, cIn, ic⟩ := covers i inA
      obtain ⟨q, qIn, fits⟩ := at_mem (each c cIn).2.1 ic at_i
      exact Or.inr ⟨c, cIn, q, qIn, fits⟩
  have inSupply : ∀ b ∈ bs, ∀ y ∈ b.fresh, y ∈ supply := by
    intro b m y yIn
    rw [freshIs]
    exact List.mem_flatMap.mpr ⟨b, m, yIn⟩
  have freshNodup : (bs.flatMap Block.fresh).Nodup := by rw [← freshIs]; exact distinct
  have plain : ∀ ax ∈ o.axioms.val, ax.annotations.val = [] := fun ax m => (readable.axioms ax m).1
  have supplyCount : supply.length ≤ axiomPs.length := by
    have := taxioms_count taxioms plain
    simpa using this
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
  have hk : KindsOf kinds o.axioms.val := graph_kinds graph.triples sourced mapIs imagesAt c cPos kinds kindsEnd
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
  have sourcesRun := sources_from_none graph.triples (graph_no_source sourced images) 0#usize v2
  have lenV3 : alloc.vec.Vec.len v3 = alloc.vec.Vec.len v2 := by
    apply UScalar.eq_of_val_eq
    simp [alloc.vec.Vec.len_val, lengthV3]
  rw [← lenV3] at complete
  -- the blocks read
  have ok : ∀ b ∈ bs, BlockOk graph.triples kinds b := by
    intro b m
    obtain ⟨image, holds, nodupPos, -⟩ := each b m
    refine ⟨holds, nodupPos, ?_⟩
    intro s a aIs ready empty
    obtain ⟨ax, axIn, axIs, -⟩ := image.member
    obtain ⟨s1, tax⟩ := image.forward
    obtain ⟨allowed, typed⟩ := readable_uses readable axIn
    have axReadable := (readable.axioms ax axIn).2
    rw [axIs] at allowed typed axReadable
    have reads := axiom_reads graph.triples kinds hk tax axReadable allowed typed
      (fun p sub v isAnnotation => graph_not_reifier sourced images inSupply fresh
        ⟨ax, axIn, by rw [axIs, isAnnotation]⟩)
    have nodupFresh : b.fresh.Nodup := (List.nodup_flatMap.mp freshNodup).1 b m
    obtain ⟨s', readRun, annotateRun, marked⟩ := reads b.fresh rfl nodupFresh s a b.rest (by rw [aIs]; exact ready)
      empty
    exact ⟨s', readRun, annotateRun, marked_same marked (fun i => by simp [Block.pos, aIs])⟩
  -- the blocks in the order of their main triples
  have sbPerm : (sortBlocks bs).Perm bs := sort_blocks_perm bs
  -- the axiom loop from a state where exactly the triples of the axioms are unused
  have loop : ∀ st : rdf_mapping.State,
      SubjectsComplete graph.triples.val st.subjects.val (alloc.vec.Vec.len st.subjects) graph.triples.val.length →
      (∀ x ∈ st.sources.val, x.val = []) → st.used.val.length = graph.triples.val.length →
      (∀ (i : Nat), i < graph.triples.val.length → (st.used.val[i]? = some false ↔ i ∈ posA)) →
      st.blanks.val = [] →
      ∃ v s', rdf_mapping.axioms_from graph.triples kinds 0#usize st (alloc.vec.Vec.new _) = .ok (some (v, s')) ∧
        v.val.Perm o.axioms.val ∧ s'.blanks.val.Perm supply ∧
        ∀ (i : Nat), i < graph.triples.val.length → s'.used.val[i]? = some true := by
    intro st completeSt sourcesSt lengthSt usedSt blanksSt
    have state : LoopState graph.triples st (sortBlocks bs) :=
      { complete := completeSt
        sources := sourcesSt
        length := lengthSt
        free := fun b m i inB => by
          have inA := (each b (sbPerm.subset m)).2.2.2 i inB
          exact (usedSt i ((posMem i).mp (List.mem_append_right _ inA))).mpr inA
        covered := fun i unused => by
          have inside : i < graph.triples.val.length := by
            rw [← lengthSt]; exact (List.getElem?_eq_some_iff.mp unused).1
          obtain ⟨c, cIn, ic⟩ := covers i ((usedSt i inside).mp unused)
          exact ⟨c, sbPerm.symm.subset cIn, ic⟩
        owns := fun b m i t y at_i unused about inB => by
          have bIn := sbPerm.subset m
          have inside : i < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
          obtain ⟨c, cIn, ic⟩ := covers i ((usedSt i inside).mp unused)
          obtain ⟨q, qIn, fits⟩ := at_mem (each c cIn).2.1 ic at_i
          have yInC := block_subject_fresh (images c cIn) qIn fits about (by
            intro an isSome same
            obtain ⟨ax, axIn, axIs, -⟩ := (images c cIn).member
            have notIn := fresh ax axIn an (by rw [axIs]; exact isSome)
            rw [same] at notIn
            exact notIn (inSupply b bIn y inB))
          rw [fresh_unique freshNodup bIn cIn inB yInC]
          exact ic
        room := by
          rw [blanksSt, ((sort_blocks_perm bs).flatMap_right Block.fresh).length_eq, ← freshIs]
          simp
          omega }
    have axiomsCount : (sortBlocks bs).length ≤ Usize.max := by
      have := o.axioms.property
      have lengths : bs.length = o.axioms.val.length := by rw [← mapIs, List.length_map]
      rw [sbPerm.length_eq]
      omega
    obtain ⟨v, s', run, vIs, blanksIs, allUsed⟩ := axioms_loop graph.triples kinds _ 0#usize (sortBlocks bs) st
      (alloc.vec.Vec.new _) rfl (fun b m => ok b (sbPerm.subset m)) (sort_blocks_sorted disjoint)
      (sort_blocks_apart disjoint) (fun b m => by simp)
      (fun b m i inRest _ u s' uIs => block_rest_skip graph.triples kinds (images b (sbPerm.subset m))
        (each b (sbPerm.subset m)).2.1 inRest u s' uIs) state (by simp; omega)
    refine ⟨v, s', run, ?_, ?_, allUsed⟩
    · rw [vIs, ← mapIs]
      simpa using sbPerm.map (fun b => (⟨alloc.vec.Vec.new _, b.ax⟩ : model.AnnotatedAxiom))
    · rw [blanksIs, blanksSt, freshIs]
      simpa using sbPerm.flatMap_right Block.fresh
  -- the header
  cases identity : o.identity with
  | Anonymous =>
    have headerNil : headerPatterns o = [] := by simp [headerPatterns, identity]
    have posHNil : posH = [] := by
      have := at_length holdsH
      rw [headerNil] at this
      simpa using this
    have headerRun : rdf_mapping.find_header graph.triples v1 0#usize = .ok none := by
      apply find_header_none
      intro i t _ at_i typed onto iri isIri
      exact graph_no_ontology identity sourced images i t at_i typed onto iri isIri
    obtain ⟨v, s', axiomsRun, vIs, blanksIs, allUsed⟩ := loop
      { used := v1, blanks := alloc.vec.Vec.new _, subjects := v3, sources := v2 } complete v2Empty
      (by simp [v1Is])
      (fun i hi => by
        have inA : i ∈ posA := by
          have := (posMem i).mpr hi
          rw [posHNil] at this
          simpa using this
        simp [v1Is, List.getElem?_replicate, hi, inA])
      (by simp)
    have allRun := all_read_used graph.triples s'.used 0#usize (fun i _ hi => allUsed i hi)
    refine ⟨⟨⟨.Anonymous, alloc.vec.Vec.new _, alloc.vec.Vec.new _, v⟩, s'.blanks⟩, ?_, rfl, ?_, ?_, vIs,
      blanksIs⟩
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
    · have importsNil : o.imports.val = [] := by
        obtain ⟨identity', imports, annotations, axioms⟩ := o
        simp only at identity theader ⊢
        subst identity
        cases theader with
        | anonymous _ _ importsEmpty _ => exact importsEmpty
      simp [importsNil]
    · exact vec_eq_of_val (by simp [readable.annotations])
  | Named iri version =>
    -- the patterns of the header
    let typingP : Pattern := ⟨iriNode iri, rdfType, .iri owlOntology⟩
    let vps : List Pattern := version.toList.map (fun v => ⟨iriNode iri, owlVersionIRI, iriNode v⟩)
    let ips : List Pattern := o.imports.val.map (fun i => ⟨iriNode iri, owlImports, iriNode i⟩)
    have hdrIs : headerPatterns o = typingP :: (vps ++ ips) := by
      cases version <;> simp [headerPatterns, identity, typingP, vps, ips]
    rw [hdrIs] at holdsH
    obtain ⟨h0, posVI, rfl, ⟨t0, at0, fits0⟩, holdsVI⟩ : ∃ h0 posVI, posH = h0 :: posVI ∧
        (∃ t, graph.triples.val[h0]? = some t ∧ Matches typingP t) ∧ At graph.triples.val posVI (vps ++ ips) := by
      cases holdsH with
      | cons hx rest => exact ⟨_, _, rfl, hx, rest⟩
    obtain ⟨posV, posI, rfl, holdsV, holdsI⟩ := at_split holdsVI
    have nodupVI := (List.nodup_cons.mp nodupH)
    obtain ⟨h0Out, nodupVI'⟩ := nodupVI
    obtain ⟨nodupV, nodupI, apartVI⟩ := List.nodup_append.mp nodupVI'
    have lenI : posI.length = o.imports.val.length := by rw [at_length holdsI]; simp [ips]
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
        · rcases List.mem_cons.mp inH with same | inVI
          · omega
          · obtain ⟨q, qIn, fits⟩ := at_mem holdsVI inVI at_i
            have predicate := fits.2.1
            rw [typed] at predicate
            simp only [List.mem_append, vps, ips, List.mem_map, Option.mem_toList] at qIn
            rcases qIn with ⟨v, -, rfl⟩ | ⟨j, -, rfl⟩
            · simp [rdfType, owlVersionIRI] at predicate
            · simp [rdfType, owlImports] at predicate
        · obtain ⟨c, cIn, ic⟩ := covers i inA
          obtain ⟨q, qIn, fits⟩ := at_mem (each c cIn).2.1 ic at_i
          exact block_not_ontology (images c cIn) qIn fits typed onto iri' isIri)
    let st0 : rdf_mapping.State := { used := v1, blanks := alloc.vec.Vec.new _, subjects := v3, sources := v2 }
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
    obtain ⟨ver, imp, sH, partsRun, verIs, impPerm, mH⟩ := header_parts_rest graph.triples kinds iri0.spelling
      (alloc.vec.Vec.new _) _ 0#usize st1 none (alloc.vec.Vec.new _) vrem (posI.zip o.imports.val) rfl
      { imports := by
          intro p m
          have inI := (List.of_mem_zip m).1
          have inside : p.1 < graph.triples.val.length :=
            (posMem p.1).mp (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _ inI)))
          have ne : p.1 ≠ h0 := fun same => h0Out (by rw [← same]; exact List.mem_append_right _ inI)
          obtain ⟨t, at_t, fits⟩ := at_zip holdsI p m
          exact ⟨by simp, st1Unused p.1 inside ne, t, at_t, aboutIs t fits.1, fits.2.1, fits.2.2⟩
        nodup := by rw [List.map_fst_zip (by omega)]; exact nodupI
        version := by
          intro p m
          obtain ⟨inV, versionIs⟩ := vremIn p m
          have inside : p.1 < graph.triples.val.length :=
            (posMem p.1).mp (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_left _ inV)))
          have ne : p.1 ≠ h0 := fun same => h0Out (by rw [← same]; exact List.mem_append_left _ inV)
          obtain ⟨t, at_t⟩ : ∃ t, graph.triples.val[p.1]? = some t := ⟨_, List.getElem?_eq_getElem inside⟩
          obtain ⟨q, qIn, fits⟩ := at_mem holdsV inV at_t
          simp only [vps, versionIs, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at qIn
          subst qIn
          exact ⟨by simp, st1Unused p.1 inside ne, t, at_t, aboutIs t fits.1, fits.2.1, fits.2.2⟩
        other := by
          intro i t _ at_i unused about
          have inside : i < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
          rcases List.mem_append.mp ((posMem i).mpr inside) with inH | inA
          · rcases List.mem_cons.mp inH with same | inVI
            · rw [same, st1Used] at unused
              cases unused
            · rcases List.mem_append.mp inVI with inV | inI
              · exact Or.inr (Or.inl (vremAll i inV))
              · exact Or.inl (mem_zip_of_mem lenI inI)
          · obtain ⟨c, cIn, ic⟩ := covers i inA
            obtain ⟨q, qIn, fits⟩ := at_mem (each c cIn).2.1 ic at_i
            refine Or.inr (Or.inr (block_not_header identity hk (images c cIn) qIn fits ?_))
            rw [about, spelled0] }
      (by simp) (by simp)
    have impIs : imp.val.Perm o.imports.val := by
      rw [List.map_snd_zip (by omega)] at impPerm
      simpa using impPerm
    -- every triple of the header is used, and only those
    have usedH : ∀ (i : Nat), i < graph.triples.val.length → (sH.used.val[i]? = some false ↔ i ∈ posA) := by
      intro i hi
      have inside : i < st1.used.val.length := by simp [st1, st0, alloc.vec.Vec.set_val_eq, v1Is]; exact hi
      constructor
      · intro unused
        apply Classical.byContradiction
        intro notA
        have inH : i ∈ h0 :: (posV ++ posI) := by
          rcases List.mem_append.mp ((posMem i).mpr hi) with inH | inA
          · exact inH
          · exact absurd inA notA
        have usedNow : sH.used.val[i]? = some true := by
          rcases List.mem_cons.mp inH with same | inVI
          · exact (mH.used i inside).mpr (Or.inl (by rw [same]; exact st1Used))
          · rcases List.mem_append.mp inVI with inV | inI
            · exact marked_used mH inside (Or.inr (vremAll i inV))
            · exact marked_used mH inside (Or.inl (mem_zip_of_mem lenI inI))
        rw [usedNow] at unused
        cases unused
      · intro inA
        have notH : i ∉ h0 :: (posV ++ posI) := fun inH => apartHA i inH i inA rfl
        have ne : i ≠ h0 := fun same => notH (by rw [same]; simp)
        refine marked_unused mH (st1Unused i hi ne) ?_
        rintro (⟨v, m⟩ | ⟨v, m⟩)
        · exact notH (List.mem_cons_of_mem _ (List.mem_append_right _ (List.of_mem_zip m).1))
        · exact notH (List.mem_cons_of_mem _ (List.mem_append_left _ (vremIn (i, v) (by rw [m]; simp)).1))
    -- the axioms
    obtain ⟨v, s', axiomsRun, vIs, blanksIs, allUsed⟩ := loop sH
      (by rw [mH.subjects]; exact complete) (by rw [mH.sources]; exact v2Empty)
      (by rw [mH.length]; simp [st1, st0, alloc.vec.Vec.set_val_eq, v1Is]) usedH
      (by rw [mH.blanks]; simp [st1, st0])
    have allRun := all_read_used graph.triples s'.used 0#usize (fun i _ hi => allUsed i hi)
    refine ⟨⟨⟨.Named ⟨iri0.spelling⟩ ver, imp, alloc.vec.Vec.new _, v⟩, s'.blanks⟩, ?_, ?_, impIs, ?_, vIs,
      blanksIs⟩
    · rw [rdf_mapping.map_graph]
      simp only [countRun, bind_ok, kindBucketsRun, kindsRun, unusedRun, bucketsRun, subjectsRun, sourcesRun,
        headerRun, alloc.vec.Vec.index_slice_index, main_lookup graph.triples hdr t0 (by rw [hdrVal]; exact at0),
        isIri0, take_correct]
      have partsRun' : rdf_mapping.header_parts graph.triples kinds iri0.spelling 0#usize
          { used := v1.set hdr true, blanks := alloc.vec.Vec.new rdf.BlankNode, subjects := v3, sources := v2 }
          none (alloc.vec.Vec.new model.Iri) (alloc.vec.Vec.new model.Annotation) =
          .ok (some (ver, imp, alloc.vec.Vec.new _, sH)) := partsRun
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
    · exact vec_eq_of_val (by simp [readable.annotations])

end Rowl.RdfReadPermuted
