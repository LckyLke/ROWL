import Rowl.RdfReadAnnotations
import Rowl.RdfReadPermuted

/-!
# Completeness of the reverse RDF mapping for annotated ontologies

For every ontology with ontology annotations and annotated axioms that the
reverse mapping reads back (`ReadableAnnotated`), a graph that lists the triples
of its forward mapping (`TOntology`) in order, with fresh blank nodes
(`FreshSupply`), is mapped to exactly that ontology, its annotations and the
annotations of its axioms included, with exactly those blank nodes
(`map_graph_complete_annotated`).

The annotations have no annotations of their own, and the annotated axioms
have one main triple (§2.3.1): an annotated axiom is written as its triples
followed by the `owl:Axiom` reification of its main triple and the annotation
triples of the reifying node. The proof reads the triples of each axiom as for
the ontology without annotations (`strip`, `agraph_block_reads`), shows that the
reader takes the reification of an annotated axiom for that axiom and for no
other (`agraph_exclusive`: two axioms with the same main triple are the same
axiom, and an annotated axiom occurs once), reads the annotations of the
reifying node (`agraph_step`), runs the axiom loop over the blocks
(`annotated_loop`), and reads the ontology annotations in the header
(`header_parts_annotations`). The facts about the blocks (`AGraph`) and the
reading of a block (`agraph_step`) hold for blocks at any positions of the
graph; `RdfReadAnnotatedPermuted` uses them for graphs in any order.
-/

namespace Rowl.RdfReadAnnotated
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust Rowl.RdfMapping Rowl.RdfReadIndexes Rowl.RdfReadExpressions
  Rowl.RdfReadAxioms Rowl.RdfReadOntology Rowl.RdfReadPermuted Rowl.RdfReadAnnotations

attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-! ### The annotated ontologies the reverse mapping reads back -/

/-- Annotations without annotations of their own whose literal values the
    reverse mapping reads back. -/
def PlainAnnotations (anns : List model.Annotation) : Prop :=
  ∀ a ∈ anns, a.annotations.val = [] ∧ ∀ v, a.value = .Literal v → LiteralReadable v

/-- The annotated ontologies whose forward mapping the reverse mapping reads
    back exactly: the conditions of `ReadableOntology` for the axioms, with
    ontology annotations and annotated axioms whose annotations have no
    annotations of their own; an annotated axiom has one main triple (§2.3.1),
    and its axiom occurs in the ontology only once (the reader takes the
    reification of a main triple for the first axiom with that triple). -/
structure ReadableAnnotated (o : model.RawOntology) : Prop where
  vocabulary : Rowl.Vocabulary.VocabularyOK o
  typed : ∀ row ∈ Rowl.Vocabulary.ontologyUses o, KindTyped o.axioms.val row.1 row.2
  annotations : PlainAnnotations o.annotations.val
  axioms : ∀ ax ∈ o.axioms.val, AxiomReadable o.axioms.val ax.axiom ∧ PlainAnnotations ax.annotations.val ∧
    (ax.annotations.val ≠ [] → mainTriples ax.axiom = 1)
  once : o.axioms.val.Pairwise (fun a b => a.axiom = b.axiom → a.annotations.val = [] ∧ b.annotations.val = [])
  apart : ∀ iri version, o.identity = .Named iri version → ∀ ax ∈ o.axioms.val, ∀ p v,
    ax.axiom ≠ .AnnotationAssertion p (.Iri iri) v

/-! ### The ontology without annotations -/

/-- An axiom without its annotations. -/
def bare (ax : model.AnnotatedAxiom) : model.AnnotatedAxiom := ⟨alloc.vec.Vec.new _, ax.axiom⟩

/-- The ontology without its annotations and those of its axioms. -/
def strip (o : model.RawOntology) : model.RawOntology where
  identity := o.identity
  imports := o.imports
  annotations := alloc.vec.Vec.new _
  axioms := .from (o.axioms.val.map bare) (by simp)

theorem strip_axioms (o : model.RawOntology) : (strip o).axioms.val = o.axioms.val.map bare := by
  simp [strip]

theorem strip_member {o : model.RawOntology} {ax : model.AnnotatedAxiom} (member : ax ∈ o.axioms.val) :
    bare ax ∈ (strip o).axioms.val := by
  rw [strip_axioms]; exact List.mem_map_of_mem member

theorem strip_member_inv {o : model.RawOntology} {ax : model.AnnotatedAxiom} (member : ax ∈ (strip o).axioms.val) :
    ∃ ax' ∈ o.axioms.val, ax = bare ax' := by
  rw [strip_axioms] at member
  obtain ⟨ax', m, rfl⟩ := List.mem_map.mp member
  exact ⟨ax', m, rfl⟩

theorem strip_typed (o : model.RawOntology) (iri : model.Iri) (kind : typing.EntityKind) :
    Typed (strip o).axioms.val iri kind ↔ Typed o.axioms.val iri kind := by
  unfold Typed
  constructor
  · rintro (⟨ax, m, isDecl⟩ | builtin)
    · obtain ⟨ax', m', rfl⟩ := strip_member_inv m
      exact Or.inl ⟨ax', m', isDecl⟩
    · exact Or.inr builtin
  · rintro (⟨ax, m, isDecl⟩ | builtin)
    · exact Or.inl ⟨bare ax, strip_member m, isDecl⟩
    · exact Or.inr builtin

theorem strip_kind_typed (o : model.RawOntology) (iri : model.Iri) (kind : typing.EntityKind) :
    KindTyped (strip o).axioms.val iri kind ↔ KindTyped o.axioms.val iri kind := by
  cases kind <;> simp [KindTyped, strip_typed]

theorem axiom_readable_transfer {l l' : List model.AnnotatedAxiom} {ax : model.Axiom} (h : AxiomReadable l ax)
    (typed : ∀ iri kind, Typed l iri kind → Typed l' iri kind) : AxiomReadable l' ax := by
  cases h
  case datatypeDefinition d r hr ht => exact .datatypeDefinition d r hr (typed _ _ ht)
  all_goals (constructor <;> assumption)

theorem strip_uses {o : model.RawOntology} {row : model.Iri × typing.EntityKind}
    (member : row ∈ Rowl.Vocabulary.ontologyUses (strip o)) : row ∈ Rowl.Vocabulary.ontologyUses o := by
  simp only [Rowl.Vocabulary.ontologyUses, List.mem_append, List.mem_flatMap] at member ⊢
  rcases member with ⟨a, m, _⟩ | ⟨ax, m, inUses⟩
  · simp [strip] at m
  · obtain ⟨ax', m', rfl⟩ := strip_member_inv m
    refine Or.inr ⟨ax', m', ?_⟩
    simp only [bare, Rowl.Collection.annotatedUses, List.mem_append, List.mem_flatMap] at inUses ⊢
    rcases inUses with ⟨a, aIn, _⟩ | inAxiom
    · simp at aIn
    · exact Or.inr inAxiom

theorem strip_vocabulary {o : model.RawOntology} (vocabulary : Rowl.Vocabulary.VocabularyOK o) :
    Rowl.Vocabulary.VocabularyOK (strip o) :=
  ⟨vocabulary.1, fun row m => vocabulary.2 row (strip_uses m)⟩

/-- Without its annotations, a readable annotated ontology is readable. -/
theorem readable_strip {o : model.RawOntology} (readable : ReadableAnnotated o) : ReadableOntology (strip o) where
  vocabulary := strip_vocabulary readable.vocabulary
  typed := fun row m => (strip_kind_typed o row.1 row.2).mpr (readable.typed row (strip_uses m))
  annotations := rfl
  axioms := by
    intro ax m
    obtain ⟨ax', m', rfl⟩ := strip_member_inv m
    exact ⟨rfl, axiom_readable_transfer (readable.axioms ax' m').1 (fun iri kind h => (strip_typed o iri kind).mpr h)⟩
  apart := by
    intro iri version named ax m p v
    obtain ⟨ax', m', rfl⟩ := strip_member_inv m
    exact readable.apart iri version named ax' m' p v

theorem strip_kinds {kinds : rdf_mapping.Kinds} {o : model.RawOntology} (hk : KindsOf kinds o.axioms.val) :
    KindsOf kinds (strip o).axioms.val := by
  intro iri kind
  rw [hk iri kind]
  congr 1
  exact decide_eq_decide.mpr (strip_typed o iri kind).symm

theorem strip_fresh {o : model.RawOntology} {supply : Supply} (fresh : FreshSupply o supply) :
    FreshSupply (strip o) supply := by
  intro ax m an isSome
  obtain ⟨ax', m', rfl⟩ := strip_member_inv m
  exact fresh ax' m' an isSome

/-! ### The main triples of readable axioms -/

/-- The reader's count of main triples agrees with the forward mapping's for an
    axiom with one main triple. -/
theorem main_triples_one {l : List model.AnnotatedAxiom} {ax : model.Axiom} (readable : AxiomReadable l ax)
    (one : mainTriples ax = 1) : rdf_mapping.main_triples ax = .ok 1#u8 := by
  cases readable with
  | equivalentClasses xs emptyRest _ => simp [rdf_mapping.main_triples, len_empty_not_pos emptyRest]
  | equivalentObjectProperties xs emptyRest => simp [rdf_mapping.main_triples, len_empty_not_pos emptyRest]
  | equivalentDataProperties xs emptyRest => simp [rdf_mapping.main_triples, len_empty_not_pos emptyRest]
  | sameIndividual xs emptyRest => simp [rdf_mapping.main_triples, len_empty_not_pos emptyRest]
  | disjointClasses xs _ =>
    by_cases emptyRest : xs.rest.val = []
    · simp [rdf_mapping.main_triples, len_empty_not_pos emptyRest]
    · simp [mainTriples, emptyRest] at one
  | disjointObjectProperties xs =>
    by_cases emptyRest : xs.rest.val = []
    · simp [rdf_mapping.main_triples, len_empty_not_pos emptyRest]
    · simp [mainTriples, emptyRest] at one
  | disjointDataProperties xs =>
    by_cases emptyRest : xs.rest.val = []
    · simp [rdf_mapping.main_triples, len_empty_not_pos emptyRest]
    · simp [mainTriples, emptyRest] at one
  | differentIndividuals xs =>
    by_cases emptyRest : xs.rest.val = []
    · simp [rdf_mapping.main_triples, len_empty_not_pos emptyRest]
    · simp [mainTriples, emptyRest] at one
  | negativeObject => simp [mainTriples] at one
  | negativeData => simp [mainTriples] at one
  | _ => simp [rdf_mapping.main_triples]

/-! ### The blocks of annotated axioms -/

/-- A block of the forward image of an axiom with its annotations: the block of
    the axiom (`core`), and, for an annotated axiom, the reification of its main
    triple with the annotation triples of the reifying node (`apos`, `apats`,
    `afresh`). -/
structure ABlock where
  core : Block
  ann : alloc.vec.Vec model.Annotation
  apos : List Nat
  apats : List Pattern
  afresh : Supply

def ABlock.ax (b : ABlock) : model.AnnotatedAxiom := ⟨b.ann, b.core.ax⟩

def ABlock.pos (b : ABlock) : List Nat := b.core.pos ++ b.apos

def ABlock.pats (b : ABlock) : List Pattern := b.core.pats ++ b.apats

def ABlock.fresh (b : ABlock) : Supply := b.core.fresh ++ b.afresh

/-- The annotation part of a block: nothing for an unannotated axiom; for an
    annotated one, a fresh node `x` reifying the main triple, followed by the
    annotation triples of `x`. -/
def AnnPart (b : ABlock) : Prop :=
  (b.ann.val = [] ∧ b.apats = [] ∧ b.afresh = []) ∨
    (b.ann.val ≠ [] ∧ ∃ (x : rdf.BlankNode) (main : Pattern) (heads : List Pattern) (s : Supply),
      b.afresh = [x] ∧ b.core.pats.head? = some main ∧ b.apats = reification owlAxiom x main ++ heads ∧
      TAnns (.blank x) b.ann.val s heads s ∧ rdf_mapping.main_triples b.core.ax = .ok 1#u8)

/-- A block of the forward image of an axiom of the ontology. -/
structure AImage (o : model.RawOntology) (b : ABlock) : Prop where
  member : b.ax ∈ o.axioms.val
  core : ImageBlock (strip o) b.core
  part : AnnPart b
  plain : PlainAnnotations b.ann.val

/-- Blocks with disjoint positions. -/
def AApart (b c : ABlock) : Prop := ∀ i ∈ b.pos, i ∉ c.pos

instance aApartSymm : Std.Symm AApart where
  symm := fun _ _ h i ic ib => h i ib ic

theorem tanns_plain_supply {y : Node} :
    ∀ {anns : List model.Annotation} {s0 : Supply} {ps : List Pattern} {s1 : Supply},
      TAnns y anns s0 ps s1 → (∀ a ∈ anns, a.annotations.val = []) → s1 = s0 := by
  intro anns
  induction anns with
  | nil => intro s0 ps s1 h _; exact (tanns_nil h).2.symm
  | cons a rest ih =>
    intro s0 ps s1 h plain
    cases h with
    | cons _ _ _ _ sMid _ p q ha hrest =>
      obtain ⟨n, -, rfl, -⟩ := tann_plain ha (plain a (by simp))
      exact ih hrest (fun b m => plain b (List.mem_cons_of_mem _ m))

theorem tanns_any_supply {y : Node} :
    ∀ {anns : List model.Annotation} {s0 : Supply} {ps : List Pattern} {s1 : Supply},
      TAnns y anns s0 ps s1 → (∀ a ∈ anns, a.annotations.val = []) → ∀ s, TAnns y anns s ps s := by
  intro anns
  induction anns with
  | nil => intro s0 ps s1 h _ s; obtain ⟨rfl, -⟩ := tanns_nil h; exact .nil y s
  | cons a rest ih =>
    intro s0 ps s1 h plain s
    cases h with
    | cons _ _ _ _ sMid _ p q ha hrest =>
      obtain ⟨n, rfl, rfl, valueNode⟩ := tann_plain ha (plain a (by simp))
      exact .cons y a rest s s s [_] q (.plain y a n s (plain a (by simp)) valueNode)
        (ih hrest (fun b m => plain b (List.mem_cons_of_mem _ m)) s)

theorem treified_one {anns : List model.Annotation} {main : Pattern} {s0 : Supply} {qs : List Pattern}
    {s1 : Supply} (h : TReified anns [main] s0 qs s1) :
    ∃ x sx ps, s0 = x :: sx ∧ qs = reification owlAxiom x main ++ ps ∧ TAnns (.blank x) anns sx ps s1 := by
  cases h with
  | cons _ _ x sx sy _ ps qs' tanns trest =>
    cases trest
    exact ⟨x, sx, ps, rfl, by simp, tanns⟩

/-- The blocks of the axioms with their annotations whose triples the graph
    lists in order from `start` on. -/
theorem annotated_blocks {o : model.RawOntology} (readable : ReadableAnnotated o)
    (triples : alloc.vec.Vec rdf.Triple) :
    ∀ {axs : List model.AnnotatedAxiom} {s0 : Supply} {ps : List Pattern} {s1 : Supply}, TAxioms axs s0 ps s1 →
    (∀ ax ∈ axs, ax ∈ o.axioms.val) → ∀ (start : Nat), At triples.val (List.range' start ps.length) ps →
    ∃ bs : List ABlock,
      bs.map ABlock.ax = axs ∧ s0 = bs.flatMap ABlock.fresh ++ s1 ∧ ps = bs.flatMap ABlock.pats ∧
      bs.Pairwise (fun b c => b.core.main < c.core.main) ∧ bs.Pairwise AApart ∧
      (∀ b ∈ bs, AImage o b ∧ At triples.val b.pos b.pats ∧ b.pos = List.range' b.core.main b.pats.length ∧
        b.core.rest = List.range' (b.core.main + 1) (b.core.pats.length - 1) ∧
        b.apos = List.range' (b.core.main + b.core.pats.length) b.apats.length ∧
        start ≤ b.core.main ∧ b.core.main + b.pats.length ≤ start + ps.length) ∧
      (∀ i, start ≤ i → i < start + ps.length → ∃ b ∈ bs, i ∈ b.pos) := by
  have stripped := readable_strip readable
  intro axs s0 ps s1 h
  induction h with
  | nil s =>
    intro _ start _
    refine ⟨[], by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
    intro i low high
    simp at high
    omega
  | cons ax rest s s1 s2 p q head tail ih =>
    intro members start holds
    have axIn := members ax (by simp)
    obtain ⟨axReadable, plainAnns, oneMain⟩ := readable.axioms ax axIn
    -- the patterns of the axiom and of its annotations
    obtain ⟨corePats, apats, afresh, sMid, tax, pIs, sIs, part⟩ : ∃ (corePats apats : List Pattern) (afresh : Supply)
        (sMid : Supply), TAxiom ax.axiom s corePats (afresh ++ sMid) ∧ p = corePats ++ apats ∧ s1 = sMid ∧
        ((ax.annotations.val = [] ∧ apats = [] ∧ afresh = []) ∨
          (ax.annotations.val ≠ [] ∧ ∃ (x : rdf.BlankNode) (main : Pattern) (heads : List Pattern) (sx : Supply),
            afresh = [x] ∧ corePats.head? = some main ∧ apats = reification owlAxiom x main ++ heads ∧
            TAnns (.blank x) ax.annotations.val sx heads sx ∧ rdf_mapping.main_triples ax.axiom = .ok 1#u8)) := by
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
    obtain ⟨main, side, f, coreIs, eqf, sides, facts⟩ := block_shape stripped (strip_member axIn) tax
    rw [pIs, List.length_append, ← List.range'_append_1] at holds
    obtain ⟨holdsP, holdsQ⟩ := at_append_inv holds (by simp)
    have holdsP' := holdsP
    rw [List.length_append, ← List.range'_append_1] at holdsP'
    obtain ⟨-, holdsA⟩ := at_append_inv holdsP' (by simp)
    obtain ⟨bs, mapIs, freshIs, patsIs, sorted, disjoint, each, covers⟩ :=
      ih (fun b m => members b (List.mem_cons_of_mem _ m)) (start + (corePats ++ apats).length) holdsQ
    have pLen : 0 < corePats.length := by rw [coreIs]; simp
    let cb : Block := { ax := ax.axiom, main := start, rest := List.range' (start + 1) (corePats.length - 1),
                        pats := corePats, fresh := f }
    let b : ABlock := { core := cb, ann := ax.annotations, apos := List.range' (start + corePats.length) apats.length,
                        apats := apats, afresh := afresh }
    have cbPos : cb.pos = List.range' start corePats.length := by
      simp only [Block.pos, cb]
      obtain ⟨k, hk⟩ : ∃ k, corePats.length = k + 1 := ⟨corePats.length - 1, by omega⟩
      rw [hk, List.range'_succ]
      simp
    have bPos : b.pos = List.range' start (corePats.length + apats.length) := by
      simp only [ABlock.pos, b, cbPos]
      rw [List.range'_append_1]
    have bPats : b.pats = corePats ++ apats := rfl
    have bLen : b.pats.length = corePats.length + apats.length := by simp [bPats]
    have bInRange : ∀ i ∈ b.pos, start ≤ i ∧ i < start + (corePats.length + apats.length) := by
      intro i m
      rw [bPos, List.mem_range'_1] at m
      exact m
    have qLen : (p ++ q).length = corePats.length + apats.length + q.length := by rw [pIs]; simp; omega
    have caLen : (corePats ++ apats).length = corePats.length + apats.length := by simp
    refine ⟨b :: bs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, mapIs, b, ABlock.ax]
      rfl
    · simp only [List.flatMap_cons, b, ABlock.fresh, cb]
      rw [eqf, ← sIs, freshIs]
      simp
    · simp only [List.flatMap_cons, b, ABlock.pats, cb]
      rw [pIs, patsIs]
    · refine List.Pairwise.cons ?_ sorted
      intro c m
      have := (each c m).2.2.2.2.2.1
      simp only [b, cb]
      simp only [List.length_append] at this
      omega
    · refine List.Pairwise.cons ?_ disjoint
      intro c m i ib ic
      have h1 := bInRange i ib
      obtain ⟨-, -, cPos, -, -, low, -⟩ := each c m
      rw [cPos, List.mem_range'_1] at ic
      simp only [List.length_append] at low
      omega
    · intro c m
      rcases List.mem_cons.mp m with rfl | inRest
      · refine ⟨⟨by simp [ABlock.ax, b, cb, axIn], ⟨⟨bare ax, strip_member axIn, rfl, rfl⟩,
            ⟨_, by rw [← eqf]; exact tax⟩, ⟨main, side, coreIs, sides, facts⟩⟩, part, plainAnns⟩,
          by rw [bPos, bPats, ← List.length_append]; exact holdsP, by rw [bPos, bLen], rfl,
          rfl, le_refl _, by
            have mainIs : b.core.main = start := rfl
            rw [qLen, bLen, mainIs]
            omega⟩
      · obtain ⟨image, holdsC, cPos, cRest, cApos, low, high⟩ := each c inRest
        simp only [List.length_append] at low high
        exact ⟨image, holdsC, cPos, cRest, cApos, by omega, by rw [qLen]; omega⟩
    · intro i low high
      rw [qLen] at high
      by_cases inP : i < start + (corePats.length + apats.length)
      · exact ⟨b, by simp, by rw [bPos, List.mem_range'_1]; exact ⟨low, inP⟩⟩
      · obtain ⟨c, m, ic⟩ := covers i (by simp only [List.length_append]; omega)
          (by simp only [List.length_append]; omega)
        exact ⟨c, List.mem_cons_of_mem _ m, ic⟩

/-! ### The header with its annotations -/

/-- The header reader takes an annotation of the ontology without annotations. -/
theorem header_parts_annotation (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8) (version : Option model.Iri) (imports : alloc.vec.Vec model.Iri)
    (annotations : alloc.vec.Vec model.Annotation) (index next : Usize) (s : rdf_mapping.State) (t : rdf.Triple)
    (at_t : triples.val[index.val]? = some t) (unused : s.used.val[index.val]? = some false)
    (about : subjectView t.subject = .iri ontology.val) (notVersion : t.predicate.spelling.val ≠ owlVersionIRI)
    (notImports : t.predicate.spelling.val ≠ owlImports)
    (kind : rdf_mapping.property_kind kinds t.predicate.spelling = .ok (some .Annotation))
    (value : model.AnnotationValue) (valueRun : rdf_mapping.annotation_value t.object = .ok (some value))
    (noAnnotation : ∀ (used : List Bool) f x, ¬ ReifierOk triples.val used t owlAnnotation f x)
    (room : annotations.val.length < Usize.max) (pushed : alloc.vec.Vec model.Annotation)
    (push : alloc.vec.Vec.push annotations
      (model.Annotation.mk (alloc.vec.Vec.new _) { iri := ⟨t.predicate.spelling⟩ } value) = .ok pushed)
    (advance : (index + 1#usize : Result Usize) = .ok next) :
    rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
      rdf_mapping.header_parts triples kinds ontology next { s with used := s.used.set index true } version imports
        pushed := by
  have more : index.val < triples.val.length := (List.getElem?_eq_some_iff.mp at_t).1
  have notVersion' := notVersion
  simp only [owlVersionIRI] at notVersion'
  have notImports' := notImports
  simp only [owlImports] at notImports'
  have reifiedRun : ∀ kindSlice : Slice U8, kindSlice.val = owlAnnotation →
      rdf_mapping.reified triples kinds index kindSlice { s with used := s.used.set index true }
        (alloc.vec.Vec.len triples) =
        .ok (some (alloc.vec.Vec.new _, { s with used := s.used.set index true })) := by
    intro kindSlice kindIs
    exact reified_absent triples kinds index kindSlice _ _ t at_t
      (fun f x ok => noAnnotation _ f x (by rw [← kindIs]; exact ok))
  rw [rdf_mapping.header_parts]
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, unused, ne_eq,
    not_true_eq_false, decide_false, Bool.false_eq_true, bind_ok, alloc.vec.Vec.index_slice_index,
    main_lookup triples index t at_t, about_iri_correct, about, decide_true, lift, same_correct, array_slice_val,
    notVersion', notImports', kind, valueRun, take_correct]
  rw [reifiedRun _ (by simp [array_slice_val, owlAnnotation])]
  simp only [bind_ok, uncurry_apply_pair, alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, ↓reduceIte,
    iri_of_identity, push, advance]

/-- The header reader takes imports at consecutive positions, in order. -/
theorem header_parts_imports_then (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8) (version : Option model.Iri) (annotations : alloc.vec.Vec model.Annotation) :
    ∀ (js : List model.Iri) (index : Usize) (s : rdf_mapping.State) (imports : alloc.vec.Vec model.Iri),
      (∀ (k : Nat) (hk : k < js.length), ∃ t, triples.val[index.val + k]? = some t ∧
        subjectView t.subject = .iri ontology.val ∧ t.predicate.spelling.val = owlImports ∧
        objectView t.object = iriNode js[k] ∧ s.used.val[index.val + k]? = some false) →
      imports.val.length + js.length ≤ Usize.max →
      ∃ (next : Usize) (s' : rdf_mapping.State) (imp : alloc.vec.Vec model.Iri), next.val = index.val + js.length ∧
        imp.val = imports.val ++ js ∧ Marked s s' (fun i => index.val ≤ i ∧ i < index.val + js.length) [] ∧
        rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
          rdf_mapping.header_parts triples kinds ontology next s' version imp annotations := by
  intro js
  induction js with
  | nil =>
    intro index s imports _ _
    exact ⟨index, s, imports, by simp, by simp, marked_same (marked_refl s) (fun i => by simp), rfl⟩
  | cons j js ih =>
    intro index s imports at_js room
    obtain ⟨t, at_t, about, predicate, object, unused⟩ := at_js 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at at_t unused object
    have more : index.val < triples.val.length := (List.getElem?_eq_some_iff.mp at_t).1
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := triples.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have importsRoom : imports.val.length < Usize.max := by simp at room; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec imports j importsRoom)
    have step := header_parts_import triples kinds ontology version imports annotations index next s t at_t unused
      about predicate j object importsRoom pushed push advance
    have mTake := marked_take s index
    obtain ⟨last, s', imp, lastIs, impIs, marked, run⟩ := ih next { s with used := s.used.set index true } pushed
      (by
        intro k hk
        obtain ⟨t', at', about', predicate', object', unused'⟩ := at_js (k + 1) (by simp; omega)
        have shift : index.val + (k + 1) = next.val + k := by omega
        rw [shift] at at' unused'
        refine ⟨t', at', about', predicate', by simpa using object', ?_⟩
        apply marked_unused mTake unused'
        intro h
        omega)
      (by rw [contents]; simp at room ⊢; omega)
    refine ⟨last, s', imp, by rw [lastIs, nextIs]; simp; omega, by rw [impIs, contents]; simp, ?_, by rw [step, run]⟩
    refine marked_same (marked_trans mTake marked) (fun i => ?_)
    rw [nextIs]
    simp only [List.length_cons]
    omega

/-- The header reader takes the annotations of the ontology at consecutive
    positions, in order, and passes over every later triple. -/
theorem header_parts_annotations (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8) (version : Option model.Iri) (imports : alloc.vec.Vec model.Iri)
    (noAnnotation : ∀ (used : List Bool) (t : rdf.Triple) f x, ¬ ReifierOk triples.val used t owlAnnotation f x) :
    ∀ (anns : List model.Annotation) {sx : Supply} {heads : List Pattern},
      TAnns (.iri ontology.val) anns sx heads sx → PlainAnnotations anns →
      (∀ a ∈ anns, rdf_mapping.property_kind kinds a.property.iri.spelling = .ok (some .Annotation)) →
      (∀ a ∈ anns, a.property.iri.spelling.val ≠ owlVersionIRI ∧ a.property.iri.spelling.val ≠ owlImports) →
      ∀ (index : Usize) (s : rdf_mapping.State) (annotations : alloc.vec.Vec model.Annotation),
        At triples.val (List.range' index.val heads.length) heads →
        (∀ (i : Nat), index.val ≤ i → i < index.val + heads.length → s.used.val[i]? = some false) →
        HeaderSkip triples kinds ontology s.used.val (index.val + heads.length) →
        annotations.val.length + anns.length ≤ Usize.max →
        ∃ v s', rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
            .ok (some (version, imports, v, s')) ∧ v.val = annotations.val ++ anns ∧
          Marked s s' (fun i => index.val ≤ i ∧ i < index.val + heads.length) [] := by
  intro anns
  induction anns with
  | nil =>
    intro sx heads h _ _ _ index s annotations _ _ skip _
    obtain ⟨rfl, -⟩ := tanns_nil h
    refine ⟨annotations, s, header_parts_skip triples kinds ontology version imports annotations s index
      (by simpa using skip), by simp, marked_same (marked_refl s) (fun i => by simp)⟩
  | cons a rest ih =>
    intro sx heads h plain kindsOk notHeader index s annotations holds free skip room
    cases h with
    | cons _ _ _ _ sMid _ p q ha hrest =>
      obtain ⟨n, rfl, rfl, valueNode⟩ := tann_plain ha (plain a (by simp)).1
      simp only [List.cons_append, List.nil_append, List.length_cons] at holds
      rw [List.range'_succ] at holds
      obtain ⟨⟨t, at_t, fits⟩, holdsRest⟩ := List.forall₂_cons.mp holds
      have more : index.val < triples.val.length := (List.getElem?_eq_some_iff.mp at_t).1
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by have := triples.property; scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      have spelled : t.predicate.spelling = a.property.iri.spelling := vec_eq_of_val fits.2.1
      obtain ⟨notVersion, notImports⟩ := notHeader a (by simp)
      have valueRun := annotation_value_complete t.object a.value n valueNode (plain a (by simp)).2 fits.2.2
      have roomA : annotations.val.length < Usize.max := by simp at room; omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec annotations
          (model.Annotation.mk (alloc.vec.Vec.new _) { iri := ⟨t.predicate.spelling⟩ } a.value) roomA)
      have step := header_parts_annotation triples kinds ontology version imports annotations index next s t at_t
        (free index.val (le_refl _) (by simp)) fits.1 (by rw [fits.2.1]; exact notVersion)
        (by rw [fits.2.1]; exact notImports) (by rw [spelled]; exact kindsOk a (by simp)) a.value valueRun
        (noAnnotation · t) roomA pushed push advance
      have mTake := marked_take s index
      obtain ⟨v, s', run, vIs, marked⟩ := ih hrest (fun b m => plain b (List.mem_cons_of_mem _ m))
        (fun b m => kindsOk b (List.mem_cons_of_mem _ m)) (fun b m => notHeader b (List.mem_cons_of_mem _ m))
        next { s with used := s.used.set index true } pushed (by rw [nextIs]; exact holdsRest)
        (by
          intro i low high
          exact marked_unused mTake (free i (by omega) (by simp; omega)) (by show i ≠ index.val; omega))
        (header_skip_mono skip (fun i h => marked_back mTake h) (by simp; omega))
        (by rw [contents]; simp at room ⊢; omega)
      refine ⟨v, s', by rw [step, run], ?_, ?_⟩
      · rw [vIs, contents, annotation_read a (plain a (by simp)).1 t.predicate.spelling fits.2.1]
        simp
      · refine marked_same (marked_trans mTake marked) (fun i => ?_)
        rw [nextIs]
        simp only [List.length_append, List.length_singleton]
        omega

/-! ### The axiom loop over annotated blocks -/

theorem axioms_from_annotated (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a next : Usize)
    (st s1 s' : rdf_mapping.State) (out pushed : alloc.vec.Vec model.AnnotatedAxiom) (ax : model.AnnotatedAxiom)
    (inside : a.val < triples.val.length) (isUnused : st.used.val[a.val]? = some false)
    (readRun : rdf_mapping.read_axiom triples kinds a st (alloc.vec.Vec.len triples) = .ok (.Found ax.axiom s1))
    (annotateRun : rdf_mapping.annotate triples kinds a ax.axiom s1 (alloc.vec.Vec.len triples) = .ok (some (ax, s')))
    (pushRoom : out.val.length < Usize.max) (push : alloc.vec.Vec.push out ax = .ok pushed)
    (advance : (a + 1#usize : Result Usize) = .ok next) :
    rdf_mapping.axioms_from triples kinds a st out = rdf_mapping.axioms_from triples kinds next s' pushed := by
  rw [rdf_mapping.axioms_from]
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, is_used_correct, isUnused, ne_eq,
    not_true_eq_false, decide_false, Bool.false_eq_true, bind_ok, readRun, annotateRun, usize_max_val, pushRoom]
  change (Std.bind (alloc.vec.Vec.push out ax) _) = _
  rw [push, bind_ok]
  simp only [advance, bind_ok]

/-- The state of the axiom loop before the annotated blocks `bs`: the indexes
    complete, the positions of the blocks unused and every other position used,
    and room for their blank nodes. -/
structure ALoop (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (bs : List ABlock) : Prop where
  complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length
  sorted : BucketsSorted s.subjects.val
  sources : SourcesComplete triples.val s.sources.val (alloc.vec.Vec.len s.sources) triples.val.length
  length : s.used.val.length = triples.val.length
  free : ∀ b ∈ bs, ∀ i ∈ b.pos, s.used.val[i]? = some false
  covered : ∀ i, s.used.val[i]? = some false → ∃ b ∈ bs, i ∈ b.pos
  room : s.blanks.val.length + (bs.flatMap ABlock.fresh).length ≤ Usize.max

theorem aloop_after {triples : alloc.vec.Vec rdf.Triple} {s s' : rdf_mapping.State} {b : ABlock}
    {rest : List ABlock} (state : ALoop triples s (b :: rest)) (disjoint : ∀ c ∈ rest, AApart b c)
    (marked : Marked s s' (fun i => i ∈ b.pos) b.fresh) : ALoop triples s' rest where
  complete := by rw [marked.subjects]; exact state.complete
  sorted := by rw [marked.subjects]; exact state.sorted
  sources := by rw [marked.sources]; exact state.sources
  length := by rw [marked.length]; exact state.length
  free := fun c member i inC =>
    marked_unused marked (state.free c (List.mem_cons_of_mem _ member) i inC) (fun inB => disjoint c member i inB inC)
  covered := fun i unused => by
    have before := marked_back marked unused
    obtain ⟨c, member, inC⟩ := state.covered i before
    rcases List.mem_cons.mp member with rfl | inRest
    · exfalso
      have inside : i < s.used.val.length := (List.getElem?_eq_some_iff.mp before).1
      rw [marked_used marked inside inC] at unused
      cases unused
    · exact ⟨c, inRest, inC⟩
  room := by
    have room := state.room
    rw [marked.blanks]
    simp only [List.flatMap_cons, List.length_append] at room ⊢
    omega

/-- **The axiom loop reads the annotated blocks in the order of their main
    triples.** From an index at or before every main position, with every
    block read from its main position with its annotations and every position
    of a block at or after its main one, `axioms_from` returns the axioms of the
    blocks in order, records their blank nodes in order and uses every triple. -/
theorem annotated_loop (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (all : List ABlock)
    (step : ∀ (s : rdf_mapping.State) (b : ABlock) (rest : List ABlock), (∀ c ∈ b :: rest, c ∈ all) →
      ALoop triples s (b :: rest) → ∀ (a : Usize), a.val = b.core.main →
      ∃ s1 s', rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found b.ax.axiom s1) ∧
        rdf_mapping.annotate triples kinds a b.ax.axiom s1 (alloc.vec.Vec.len triples) = .ok (some (b.ax, s')) ∧
        Marked s s' (fun i => i ∈ b.pos) b.fresh) :
    ∀ (n : Nat) (a : Usize) (bs : List ABlock) (s : rdf_mapping.State) (out : alloc.vec.Vec model.AnnotatedAxiom),
      triples.val.length - a.val = n → (∀ b ∈ bs, b ∈ all) →
      bs.Pairwise (fun b c => b.core.main < c.core.main) → bs.Pairwise AApart → (∀ b ∈ bs, a.val ≤ b.core.main) →
      (∀ b ∈ bs, ∀ i ∈ b.pos, b.core.main ≤ i ∧ i < triples.val.length) →
      ALoop triples s bs → out.val.length + bs.length ≤ Usize.max →
      ∃ v s', rdf_mapping.axioms_from triples kinds a s out = .ok (some (v, s')) ∧
        v.val = out.val ++ bs.map ABlock.ax ∧ s'.blanks.val = s.blanks.val ++ bs.flatMap ABlock.fresh ∧
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
        have := (inRange b (by simp) b.core.main (by simp [ABlock.pos, Block.pos])).2
        have := after b (by simp)
        omega
    subst empty
    refine ⟨out, s, axioms_from_end triples kinds s out a done, by simp, by simp, ?_⟩
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
      have isMain : a.val = b.core.main := by
        have := (inRange b member a.val inB).1
        have := after b member
        omega
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
      obtain ⟨s1, s', readRun, annotateRun, marked⟩ := step s b rest members state a isMain
      have pushRoom : out.val.length < Usize.max := by simp at room; omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out b.ax pushRoom)
      have stepRun := axioms_from_annotated triples kinds a next s s1 s' out pushed b.ax more unused readRun
        annotateRun pushRoom push advance
      obtain ⟨v, s'', run, vIs, blanksIs, allUsed⟩ := ih next rest s' pushed (by omega)
        (fun c m => members c (List.mem_cons_of_mem _ m)) (List.pairwise_cons.mp sorted).2
        (List.pairwise_cons.mp disjoint).2
        (fun c m => by have := (List.pairwise_cons.mp sorted).1 c m; omega)
        (fun c m => inRange c (List.mem_cons_of_mem _ m))
        (aloop_after state (List.pairwise_cons.mp disjoint).1 marked)
        (by rw [contents]; simp at room ⊢; omega)
      refine ⟨v, s'', by rw [stepRun, run], by rw [vIs, contents]; simp, ?_, allUsed⟩
      rw [blanksIs, marked.blanks]
      simp
    · have stepRun := axioms_from_used triples kinds s out a next more unused advance
      obtain ⟨v, s', run, vIs, blanksIs, allUsed⟩ := ih next bs s out (by omega) members sorted disjoint
        (by
          intro c m
          have le := after c m
          rw [nextIs]
          apply Nat.lt_of_le_of_ne le
          intro same
          exact unused (by rw [same]; exact state.free c m c.core.main (by simp [ABlock.pos, Block.pos])))
        inRange state room
      exact ⟨v, s', by rw [stepRun, run], vIs, blanksIs, allUsed⟩

/-! ### The triples of the graph of an annotated ontology -/

theorem tanns_heads {y : Node} :
    ∀ {anns : List model.Annotation} {s0 : Supply} {ps : List Pattern} {s1 : Supply},
      TAnns y anns s0 ps s1 → (∀ a ∈ anns, a.annotations.val = []) →
      ∀ q ∈ ps, q.subject = y ∧ ∃ a ∈ anns, q.predicate = a.property.iri.spelling.val ∧
        AnnotationValueNode a.value q.object := by
  intro anns
  induction anns with
  | nil => intro s0 ps s1 h _ q m; obtain ⟨rfl, -⟩ := tanns_nil h; simp at m
  | cons a rest ih =>
    intro s0 ps s1 h plain q m
    cases h with
    | cons _ _ _ _ sMid _ p r ha hrest =>
      obtain ⟨n, rfl, rfl, valueNode⟩ := tann_plain ha (plain a (by simp))
      rcases List.mem_append.mp m with inP | inR
      · simp only [List.mem_singleton] at inP
        subst inP
        exact ⟨rfl, a, by simp, rfl, valueNode⟩
      · obtain ⟨subject, b, bIn, predicate, value⟩ := ih hrest (fun c m => plain c (List.mem_cons_of_mem _ m)) q inR
        exact ⟨subject, b, List.mem_cons_of_mem _ bIn, predicate, value⟩

/-- The rows of the annotations of an ontology and of its axioms are rows of the ontology. -/
theorem annotation_row_ontology {o : model.RawOntology} {a : model.Annotation} (member : a ∈ o.annotations.val) :
    (a.property.iri, typing.EntityKind.AnnotationProperty) ∈ Rowl.Vocabulary.ontologyUses o := by
  simp only [Rowl.Vocabulary.ontologyUses]
  apply List.mem_append_left
  refine List.mem_flatMap.mpr ⟨a, member, ?_⟩
  obtain ⟨nested, property, value⟩ := a
  rw [Rowl.Collection.annotationUses]
  simp

theorem annotation_row_axiom {o : model.RawOntology} {ax : model.AnnotatedAxiom} (axIn : ax ∈ o.axioms.val)
    {a : model.Annotation} (member : a ∈ ax.annotations.val) :
    (a.property.iri, typing.EntityKind.AnnotationProperty) ∈ Rowl.Vocabulary.ontologyUses o := by
  simp only [Rowl.Vocabulary.ontologyUses]
  apply List.mem_append_right
  refine List.mem_flatMap.mpr ⟨ax, axIn, ?_⟩
  simp only [Rowl.Collection.annotatedUses]
  apply List.mem_append_left
  refine List.mem_flatMap.mpr ⟨a, member, ?_⟩
  obtain ⟨nested, property, value⟩ := a
  rw [Rowl.Collection.annotationUses]
  simp

/-- The property of an annotation of a readable ontology is an annotation property
    for the reader and no vocabulary of the mapping. -/
theorem annotation_property_facts {o : model.RawOntology} (readable : ReadableAnnotated o)
    {kinds : rdf_mapping.Kinds} (hk : KindsOf kinds o.axioms.val) {a : model.Annotation}
    (row : (a.property.iri, typing.EntityKind.AnnotationProperty) ∈ Rowl.Vocabulary.ontologyUses o) :
    rdf_mapping.property_kind kinds a.property.iri.spelling = .ok (some .Annotation) ∧
      ∀ K ∈ mappingVocabulary, a.property.iri.spelling.val ≠ K :=
  ⟨property_kind_annotation hk (readable.typed _ row), fun _ member => allowed_ne (readable.vocabulary.2 _ row) member⟩

/-- The facts about the graph of an annotated ontology listed in the order of
    its forward mapping that the reading of its blocks needs. -/
structure AGraph (o : model.RawOntology) (triples : List rdf.Triple) (header : List Pattern) (bs : List ABlock)
    (supply : Supply) : Prop where
  readable : ReadableAnnotated o
  headerFacts : ∀ q ∈ header, ∃ iri version, o.identity = .Named iri version ∧ q.subject = iriNode iri ∧
    ((q.predicate = rdfType ∧ q.object = .iri owlOntology) ∨ q.predicate = owlVersionIRI ∨ q.predicate = owlImports ∨
      ∃ a ∈ o.annotations.val, q.predicate = a.property.iri.spelling.val)
  blocks : ∀ b ∈ bs, AImage o b ∧ At triples b.pos b.pats ∧ b.pos.Nodup ∧ b.apos.length = b.apats.length
  sourced : ∀ (i : Nat) (t : rdf.Triple), triples[i]? = some t → (∃ q ∈ header, Matches q t) ∨ ∃ b ∈ bs, i ∈ b.pos
  axiomsIs : bs.map ABlock.ax = o.axioms.val
  supplyIs : supply = bs.flatMap ABlock.fresh
  distinct : supply.Nodup
  fresh : FreshSupply o supply
  disjoint : bs.Pairwise AApart

section

variable {o : model.RawOntology} {triples : List rdf.Triple} {header : List Pattern} {bs : List ABlock}
  {supply : Supply}

theorem agraph_in_supply (g : AGraph o triples header bs supply) {b : ABlock} (bIn : b ∈ bs) {y : rdf.BlankNode}
    (yIn : y ∈ b.fresh) : y ∈ supply := by
  rw [g.supplyIs]; exact List.mem_flatMap.mpr ⟨b, bIn, yIn⟩

theorem agraph_fresh_unique (g : AGraph o triples header bs supply) {b c : ABlock} (bIn : b ∈ bs) (cIn : c ∈ bs)
    {y : rdf.BlankNode} (yb : y ∈ b.fresh) (yc : y ∈ c.fresh) : b = c := by
  apply Classical.byContradiction
  intro different
  have nodup : (bs.flatMap ABlock.fresh).Nodup := by rw [← g.supplyIs]; exact g.distinct
  have pairwise := (List.nodup_flatMap.mp nodup).2
  have symm : Std.Symm (Function.onFun List.Disjoint ABlock.fresh) := ⟨fun _ _ h => List.Disjoint.symm h⟩
  exact pairwise.forall bIn cIn different yb yc

theorem agraph_fresh_nodup (g : AGraph o triples header bs supply) {b : ABlock} (bIn : b ∈ bs) : b.fresh.Nodup := by
  have nodup : (bs.flatMap ABlock.fresh).Nodup := by rw [← g.supplyIs]; exact g.distinct
  exact (List.nodup_flatMap.mp nodup).1 b bIn

/-- The shape of the patterns of a block: its main pattern, the patterns of its
    expressions and lists, and for an annotated axiom the reification of the
    main pattern by a node `x` and the annotation triples of `x`. -/
theorem agraph_shape (g : AGraph o triples header bs supply) {b : ABlock} (bIn : b ∈ bs) :
    ∃ main side, b.core.pats = main :: side ∧ Sides b.core.fresh side ∧
      MainFacts (strip o) b.core.ax b.core.fresh main ∧
      ((b.ann.val = [] ∧ b.apats = [] ∧ b.afresh = []) ∨
        (b.ann.val ≠ [] ∧ ∃ (x : rdf.BlankNode) (heads : List Pattern) (sx : Supply), b.afresh = [x] ∧
          b.apats = reification owlAxiom x main ++ heads ∧ TAnns (.blank x) b.ann.val sx heads sx ∧
          rdf_mapping.main_triples b.core.ax = .ok 1#u8)) := by
  obtain ⟨image, -, -, -⟩ := g.blocks b bIn
  obtain ⟨main, side, pIs, sides, facts⟩ := image.core.shape
  refine ⟨main, side, pIs, sides, facts, ?_⟩
  rcases image.part with plain | ⟨nonempty, x, main', heads, sx, afreshIs, headIs, apatsIs, tanns, one⟩
  · exact Or.inl plain
  · rw [pIs] at headIs
    simp only [List.head?_cons, Option.some.injEq] at headIs
    subst headIs
    exact Or.inr ⟨nonempty, x, heads, sx, afreshIs, apatsIs, tanns, one⟩

/-- The patterns of a block with a blank subject have it among the blank nodes
    of the block, unless it is an anonymous individual of the axiom. -/
theorem agraph_pattern_subject (g : AGraph o triples header bs supply) {b : ABlock} (bIn : b ∈ bs) {q : Pattern}
    (member : q ∈ b.pats) {y : rdf.BlankNode} (blank : q.subject = .blank y) :
    y ∈ b.fresh ∨ ∃ an, subjectAnonymous b.core.ax = some an ∧ y = ⟨an.scope, an.label⟩ := by
  obtain ⟨main, side, pIs, sides, facts, part⟩ := (agraph_shape g) bIn
  simp only [ABlock.pats, List.mem_append] at member
  rcases member with inCore | inA
  · rw [pIs] at inCore
    rcases List.mem_cons.mp inCore with rfl | inSide
    · rcases facts.blank y blank with inside | anonymous
      · exact Or.inl (List.mem_append_left _ inside)
      · exact Or.inr anonymous
    · obtain ⟨z, inside, subject⟩ := (sides q inSide).2
      rw [subject] at blank
      cases blank
      exact Or.inl (List.mem_append_left _ inside)
  · rcases part with ⟨-, empty, -⟩ | ⟨-, x, heads, sx, afreshIs, apatsIs, tanns, -⟩
    · rw [empty] at inA; simp at inA
    · have plain : ∀ a ∈ b.ann.val, a.annotations.val = [] := fun a m => ((g.blocks b bIn).1.plain a m).1
      rw [apatsIs] at inA
      have subjectX : q.subject = .blank x := by
        rcases List.mem_append.mp inA with inR | inH
        · simp only [reification, List.mem_cons, List.not_mem_nil, or_false] at inR
          rcases inR with rfl | rfl | rfl | rfl <;> rfl
        · exact (tanns_heads tanns plain q inH).1
      rw [subjectX] at blank
      cases blank
      exact Or.inl (List.mem_append_right _ (by rw [afreshIs]; simp))

/-- Every triple about a blank node of a block is at a position of that block. -/
theorem agraph_owner (g : AGraph o triples header bs supply) {b : ABlock} (bIn : b ∈ bs) {i : Nat} {t : rdf.Triple}
    (at_i : triples[i]? = some t) {y : rdf.BlankNode} (about : subjectView t.subject = .blank y)
    (yIn : y ∈ b.fresh) : i ∈ b.pos := by
  rcases g.sourced i t at_i with ⟨q, qIn, fits⟩ | ⟨c, cIn, ic⟩
  · obtain ⟨iri, -, -, subject, -⟩ := g.headerFacts q qIn
    rw [← fits.1, about] at subject
    simp [iriNode] at subject
  · obtain ⟨-, holds, -, -⟩ := g.blocks c cIn
    obtain ⟨q, qIn, fits⟩ := at_mem holds ic at_i
    rcases (agraph_pattern_subject g) cIn qIn (fits.1.symm.trans about) with inC | ⟨an, isSome, same⟩
    · rw [(agraph_fresh_unique g) bIn cIn yIn inC]; exact ic
    · exfalso
      obtain ⟨image, -, -, -⟩ := g.blocks c cIn
      have notIn := g.fresh c.ax image.member an isSome
      rw [← same] at notIn
      exact notIn ((agraph_in_supply g) bIn yIn)

theorem agraph_split_at (g : AGraph o triples header bs supply) {b : ABlock} (bIn : b ∈ bs) :
    At triples b.core.pos b.core.pats ∧ At triples b.apos b.apats := by
  obtain ⟨-, holds, -, aposLen⟩ := g.blocks b bIn
  have lengths := at_length holds
  simp only [ABlock.pos, ABlock.pats, List.length_append] at lengths
  exact at_append_inv holds (by omega)

/-- The positions of the reification and of the annotation triples of an
    annotated block. -/
theorem agraph_reified_layout (g : AGraph o triples header bs supply) {b : ABlock} (bIn : b ∈ bs)
    {x : rdf.BlankNode} {main : Pattern} {heads : List Pattern}
    (apatsIs : b.apats = reification owlAxiom x main ++ heads) :
    ∃ (p0 p1 p2 p3 : Nat) (hs : List Nat), b.apos = p0 :: p1 :: p2 :: p3 :: hs ∧
      (∃ t, triples[p0]? = some t ∧ Matches ⟨.blank x, rdfType, .iri owlAxiom⟩ t) ∧
      (∃ t, triples[p1]? = some t ∧ Matches ⟨.blank x, owlAnnotatedSource, main.subject⟩ t) ∧
      (∃ t, triples[p2]? = some t ∧ Matches ⟨.blank x, owlAnnotatedProperty, .iri main.predicate⟩ t) ∧
      (∃ t, triples[p3]? = some t ∧ Matches ⟨.blank x, owlAnnotatedTarget, main.object⟩ t) ∧
      At triples hs heads := by
  have holdsA := (agraph_split_at g bIn).2
  rw [apatsIs] at holdsA
  simp only [reification, List.cons_append, List.nil_append] at holdsA
  generalize b.apos = apos at holdsA ⊢
  cases holdsA with
  | cons h0 rest =>
    cases rest with
    | cons h1 rest =>
      cases rest with
      | cons h2 rest =>
        cases rest with
        | cons h3 rest => exact ⟨_, _, _, _, _, rfl, h0, h1, h2, h3, rest⟩

/-- A triple at a position of the axiom part of a block whose subject is a
    blank node of the block, or an anonymous individual of the axiom. -/
theorem agraph_core_subject (g : AGraph o triples header bs supply) {b : ABlock} (bIn : b ∈ bs) {i : Nat} {t : rdf.Triple}
    (at_i : triples[i]? = some t) (inCore : i ∈ b.core.pos) {y : rdf.BlankNode}
    (about : subjectView t.subject = .blank y) :
    y ∈ b.core.fresh ∨ ∃ an, subjectAnonymous b.core.ax = some an ∧ y = ⟨an.scope, an.label⟩ := by
  obtain ⟨main, side, pIs, sides, facts, -⟩ := (agraph_shape g) bIn
  obtain ⟨q, qIn, fits⟩ := at_mem ((agraph_split_at g) bIn).1 inCore at_i
  rw [pIs] at qIn
  rcases List.mem_cons.mp qIn with rfl | inSide
  · exact facts.blank y (fits.1.symm.trans about)
  · obtain ⟨z, inside, subject⟩ := (sides q inSide).2
    rw [← fits.1, about] at subject
    simp only [Node.blank.injEq] at subject
    rw [subject]
    exact Or.inl inside

/-- The reifying node of an annotated block is no blank node of its axiom part. -/
theorem agraph_reifier_not_core (g : AGraph o triples header bs supply) {b : ABlock} (bIn : b ∈ bs) {x : rdf.BlankNode}
    (afreshIs : b.afresh = [x]) : x ∉ b.core.fresh := by
  intro inCore
  have nodup := (agraph_fresh_nodup g) bIn
  simp only [ABlock.fresh, afreshIs] at nodup
  exact (List.nodup_append.mp nodup).2.2 x inCore x (by simp) rfl

/-- A triple about the reifying node of an annotated block is a triple of the
    reification or an annotation triple of that node. -/
theorem agraph_reifier_triple (g : AGraph o triples header bs supply) {b : ABlock} (bIn : b ∈ bs)
    {x : rdf.BlankNode} {main : Pattern} {heads : List Pattern} {sx : Supply} (afreshIs : b.afresh = [x])
    (tanns : TAnns (.blank x) b.ann.val sx heads sx) {p0 p1 p2 p3 : Nat} {hs : List Nat}
    (layout : b.apos = p0 :: p1 :: p2 :: p3 :: hs)
    (typing : ∃ t, triples[p0]? = some t ∧ Matches ⟨.blank x, rdfType, .iri owlAxiom⟩ t)
    (source : ∃ t, triples[p1]? = some t ∧ Matches ⟨.blank x, owlAnnotatedSource, main.subject⟩ t)
    (property : ∃ t, triples[p2]? = some t ∧ Matches ⟨.blank x, owlAnnotatedProperty, .iri main.predicate⟩ t)
    (target : ∃ t, triples[p3]? = some t ∧ Matches ⟨.blank x, owlAnnotatedTarget, main.object⟩ t)
    (holdsH : At triples hs heads) {j : Nat} {t : rdf.Triple}
    (at_j : triples[j]? = some t) (about : subjectView t.subject = .blank x) :
    (j = p0 ∧ Matches ⟨.blank x, rdfType, .iri owlAxiom⟩ t) ∨
      (j = p1 ∧ Matches ⟨.blank x, owlAnnotatedSource, main.subject⟩ t) ∨
      (j = p2 ∧ Matches ⟨.blank x, owlAnnotatedProperty, .iri main.predicate⟩ t) ∨
      (j = p3 ∧ Matches ⟨.blank x, owlAnnotatedTarget, main.object⟩ t) ∨
      (j ∈ hs ∧ ∃ a ∈ b.ann.val, t.predicate.spelling.val = a.property.iri.spelling.val) := by
  have xIn : x ∈ b.fresh := by simp [ABlock.fresh, afreshIs]
  have inB := agraph_owner g bIn at_j about xIn
  simp only [ABlock.pos, List.mem_append] at inB
  rcases inB with inCore | inA
  · exfalso
    rcases agraph_core_subject g bIn at_j inCore about with inside | ⟨an, isSome, same⟩
    · exact agraph_reifier_not_core g bIn afreshIs inside
    · obtain ⟨image, -, -, -⟩ := g.blocks b bIn
      have notIn := g.fresh b.ax image.member an isSome
      rw [← same] at notIn
      exact notIn (agraph_in_supply g bIn xIn)
  · rw [layout] at inA
    have same : ∀ {k : Nat} {u : rdf.Triple} {q : Pattern}, triples[k]? = some u → Matches q u → k = j →
        Matches q t := by
      intro k u q at_k fits kj
      rw [kj, at_j] at at_k
      cases at_k
      exact fits
    simp only [List.mem_cons] at inA
    rcases inA with rfl | rfl | rfl | rfl | inH
    · obtain ⟨u, at_u, fits⟩ := typing; exact Or.inl ⟨rfl, same at_u fits rfl⟩
    · obtain ⟨u, at_u, fits⟩ := source; exact Or.inr (Or.inl ⟨rfl, same at_u fits rfl⟩)
    · obtain ⟨u, at_u, fits⟩ := property; exact Or.inr (Or.inr (Or.inl ⟨rfl, same at_u fits rfl⟩))
    · obtain ⟨u, at_u, fits⟩ := target; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, same at_u fits rfl⟩)))
    · have plain : ∀ a ∈ b.ann.val, a.annotations.val = [] := fun a m => ((g.blocks b bIn).1.plain a m).1
      obtain ⟨q, qIn, fits⟩ := at_mem holdsH inH at_j
      obtain ⟨-, a, aIn, predicate, -⟩ := tanns_heads tanns plain q qIn
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨inH, a, aIn, ?_⟩)))
      rw [fits.2.1, predicate]

/-- The annotation property of an annotation of an axiom is no vocabulary of the mapping. -/
theorem agraph_annotation_not_vocabulary (g : AGraph o triples header bs supply) {b : ABlock} (bIn : b ∈ bs)
    {a : model.Annotation} (aIn : a ∈ b.ann.val) : ∀ K ∈ mappingVocabulary, a.property.iri.spelling.val ≠ K := by
  obtain ⟨image, -, -, -⟩ := g.blocks b bIn
  intro K member
  exact allowed_ne (g.readable.vocabulary.2 _ (annotation_row_axiom image.member aIn)) member

/-- Every `owl:annotatedSource` triple of the graph is the source triple of the
    reification of an annotated block. -/
theorem agraph_source_triple (g : AGraph o triples header bs supply) {i : Nat} {t : rdf.Triple}
    (at_i : triples[i]? = some t) (named : t.predicate.spelling.val = owlAnnotatedSource) :
    ∃ b ∈ bs, ∃ (main : Pattern) (side : List Pattern) (x : rdf.BlankNode) (heads : List Pattern) (sx : Supply)
      (p0 p1 p2 p3 : Nat) (hs : List Nat), b.core.pats = main :: side ∧
      MainFacts (strip o) b.core.ax b.core.fresh main ∧ b.ann.val ≠ [] ∧
      b.afresh = [x] ∧ b.apats = reification owlAxiom x main ++ heads ∧ TAnns (.blank x) b.ann.val sx heads sx ∧
      rdf_mapping.main_triples b.core.ax = .ok 1#u8 ∧ b.apos = p0 :: p1 :: p2 :: p3 :: hs ∧ i = p1 ∧
      Matches ⟨.blank x, owlAnnotatedSource, main.subject⟩ t := by
  rcases g.sourced i t at_i with ⟨q, qIn, fits⟩ | ⟨b, bIn, ib⟩
  · exfalso
    obtain ⟨iri, version, -, -, which⟩ := g.headerFacts q qIn
    rw [← fits.2.1] at which
    rw [named] at which
    rcases which with ⟨typed, -⟩ | version | imports | ⟨a, aIn, spelled⟩
    · simp [owlAnnotatedSource, rdfType] at typed
    · simp [owlAnnotatedSource, owlVersionIRI] at version
    · simp [owlAnnotatedSource, owlImports] at imports
    · exact allowed_ne (g.readable.vocabulary.2 _ (annotation_row_ontology aIn)) (key := owlAnnotatedSource)
        (by simp [mappingVocabulary]) spelled.symm
  · obtain ⟨main, side, pIs, sides, facts, part⟩ := (agraph_shape g) bIn
    simp only [ABlock.pos, List.mem_append] at ib
    rcases ib with inCore | inA
    · exfalso
      obtain ⟨q, qIn, fits⟩ := at_mem ((agraph_split_at g) bIn).1 inCore at_i
      rw [pIs] at qIn
      rcases List.mem_cons.mp qIn with rfl | inSide
      · exact facts.notSource (by rw [← fits.2.1]; exact named)
      · exact side_not_source (sides q inSide).1 (by rw [← fits.2.1]; exact named)
    · rcases part with ⟨-, empty, -⟩ | ⟨nonempty, x, heads, sx, afreshIs, apatsIs, tanns, one⟩
      · exfalso
        obtain ⟨q, qIn, -⟩ := at_mem ((agraph_split_at g) bIn).2 inA at_i
        rw [empty] at qIn
        simp at qIn
      · obtain ⟨p0, p1, p2, p3, hs, layout, typing, source, property, target, holdsH⟩ :=
          (agraph_reified_layout g) bIn apatsIs
        have subjectX : subjectView t.subject = .blank x := by
          have holdsA := ((agraph_split_at g) bIn).2
          obtain ⟨q, qIn, fits⟩ := at_mem holdsA inA at_i
          rw [fits.1]
          have plain : ∀ a ∈ b.ann.val, a.annotations.val = [] := fun a m => ((g.blocks b bIn).1.plain a m).1
          rw [apatsIs] at qIn
          rcases List.mem_append.mp qIn with inR | inH
          · simp only [reification, List.mem_cons, List.not_mem_nil, or_false] at inR
            rcases inR with rfl | rfl | rfl | rfl <;> rfl
          · exact (tanns_heads tanns plain q inH).1
        rcases (agraph_reifier_triple g) bIn afreshIs tanns layout typing source property target holdsH at_i subjectX with
          ⟨-, fits⟩ | ⟨rfl, fits⟩ | ⟨-, fits⟩ | ⟨-, fits⟩ | ⟨-, a, aIn, spelled⟩
        · exfalso; have := fits.2.1; rw [named] at this; simp [owlAnnotatedSource, rdfType] at this
        · exact ⟨b, bIn, main, side, x, heads, sx, p0, _, p2, p3, hs, pIs, facts, nonempty, afreshIs, apatsIs, tanns,
            one, layout, rfl, fits⟩
        · exfalso; have := fits.2.1; rw [named] at this; simp [owlAnnotatedSource, owlAnnotatedProperty] at this
        · exfalso; have := fits.2.1; rw [named] at this; simp [owlAnnotatedSource, owlAnnotatedTarget] at this
        · exfalso
          exact (agraph_annotation_not_vocabulary g) bIn aIn owlAnnotatedSource (by simp [mappingVocabulary])
            (spelled.symm.trans named)

/-- No blank node of the graph reifies a triple as an annotation: no annotation
    has annotations of its own. -/
theorem agraph_no_annotation_kind (g : AGraph o triples header bs supply) :
    ∀ (used : List Bool) (t : rdf.Triple) f x, ¬ ReifierOk triples used t owlAnnotation f x := by
  intro used t f x ok
  obtain ⟨ts, -, -, ty, unusedS, -, -, unusedY, subjectS, fitsS, -, -, fitsY⟩ := ok
  obtain ⟨b, bIn, main, side, x', heads, sx, p0, p1, p2, p3, hs, -, -, -, afreshIs, apatsIs, tanns, -, -, -,
    fitsS'⟩ := (agraph_source_triple g) unusedS.1 fitsS.2.1
  have same : x' = x := by
    have := fitsS'.1
    rw [subjectS] at this
    simp only [subjectView, Node.blank.injEq] at this
    exact this.symm
  rw [same] at afreshIs apatsIs tanns
  obtain ⟨q0, q1, q2, q3, hs', layout', typing, source, property, target, holdsH⟩ :=
    (agraph_reified_layout g) bIn apatsIs
  rcases (agraph_reifier_triple g) bIn afreshIs tanns layout' typing source property target holdsH unusedY.1 fitsY.1 with
    ⟨-, fits⟩ | ⟨-, fits⟩ | ⟨-, fits⟩ | ⟨-, fits⟩ | ⟨-, a, aIn, spelled⟩
  · have := fits.2.2; rw [fitsY.2.2] at this; simp [owlAnnotation, owlAxiom] at this
  · have := fits.2.1; rw [fitsY.2.1] at this; simp [rdfType, owlAnnotatedSource] at this
  · have := fits.2.1; rw [fitsY.2.1] at this; simp [rdfType, owlAnnotatedProperty] at this
  · have := fits.2.1; rw [fitsY.2.1] at this; simp [rdfType, owlAnnotatedTarget] at this
  · exact (agraph_annotation_not_vocabulary g) bIn aIn rdfType (by simp [mappingVocabulary]) (spelled.symm.trans fitsY.2.1)

/-- No triple of the graph types a blank node outside the supply with a type of
    Table 8. -/
theorem agraph_not_reifier_type (g : AGraph o triples header bs supply) {z : rdf.BlankNode} (notIn : z ∉ supply) :
    ∀ (i : Nat) (t : rdf.Triple), triples[i]? = some t → subjectView t.subject = .blank z →
      t.predicate.spelling.val = rdfType → ∀ K ∈ reifierTypes, objectView t.object ≠ .iri K := by
  intro i t at_i about typed K member isK
  rcases g.sourced i t at_i with ⟨q, qIn, fits⟩ | ⟨b, bIn, ib⟩
  · obtain ⟨iri, -, -, subject, -⟩ := g.headerFacts q qIn
    rw [← fits.1, about] at subject
    simp [iriNode] at subject
  · simp only [ABlock.pos, List.mem_append] at ib
    rcases ib with inCore | inA
    · obtain ⟨main, side, pIs, sides, facts, -⟩ := (agraph_shape g) bIn
      obtain ⟨q, qIn, fits⟩ := at_mem ((agraph_split_at g) bIn).1 inCore at_i
      rw [pIs] at qIn
      rcases List.mem_cons.mp qIn with rfl | inSide
      · exact facts.reifier z (fits.1.symm.trans about)
          (fun inF => notIn ((agraph_in_supply g) bIn (List.mem_append_left _ inF))) (by rw [← fits.2.1]; exact typed) K
          member (by rw [← fits.2.2]; exact isK)
      · obtain ⟨y, inside, subject⟩ := (sides q inSide).2
        rw [← fits.1, about] at subject
        simp only [Node.blank.injEq] at subject
        rw [subject] at notIn
        exact notIn ((agraph_in_supply g) bIn (List.mem_append_left _ inside))
    · obtain ⟨q, qIn, fits⟩ := at_mem ((agraph_split_at g) bIn).2 inA at_i
      rcases (agraph_pattern_subject g) bIn (List.mem_append_right _ qIn) (fits.1.symm.trans about) with inF | ⟨an, isSome, same⟩
      · exact notIn ((agraph_in_supply g) bIn inF)
      · exfalso
        obtain ⟨main', side', pIs', sides', facts', part⟩ := (agraph_shape g) bIn
        rcases part with ⟨-, empty, -⟩ | ⟨-, x, heads, sx, afreshIs, apatsIs, tanns, -⟩
        · rw [empty] at qIn; simp at qIn
        · have plain : ∀ a ∈ b.ann.val, a.annotations.val = [] := fun a m => ((g.blocks b bIn).1.plain a m).1
          have subjectX : q.subject = .blank x := by
            rw [apatsIs] at qIn
            rcases List.mem_append.mp qIn with inR | inH
            · simp only [reification, List.mem_cons, List.not_mem_nil, or_false] at inR
              rcases inR with rfl | rfl | rfl | rfl <;> rfl
            · exact (tanns_heads tanns plain q inH).1
          have := fits.1
          rw [subjectX, about] at this
          simp only [Node.blank.injEq] at this
          rw [this] at notIn
          exact notIn ((agraph_in_supply g) bIn (by simp [ABlock.fresh, afreshIs]))

end

/-! ### Reading a block with its annotations -/

theorem reifier_ok_back {triples : List rdf.Triple} {s s1 : rdf_mapping.State} {m : Nat → Prop}
    {fr : List rdf.BlankNode} (marked : Marked s s1 m fr) {t : rdf.Triple} {kind : List U8}
    {found : Usize × Usize × Usize × Usize} {x : rdf.BlankNode}
    (ok : ReifierOk triples s1.used.val t kind found x) : ReifierOk triples s.used.val t kind found x := by
  obtain ⟨ts, tp, tt, ty, uS, uP, uT, uY, subjectS, fS, fP, fT, fY⟩ := ok
  exact ⟨ts, tp, tt, ty, ⟨uS.1, marked_back marked uS.2⟩, ⟨uP.1, marked_back marked uP.2⟩,
    ⟨uT.1, marked_back marked uT.2⟩, ⟨uY.1, marked_back marked uY.2⟩, subjectS, fS, fP, fT, fY⟩

theorem tanns_length {y : Node} :
    ∀ {anns : List model.Annotation} {s0 : Supply} {ps : List Pattern} {s1 : Supply},
      TAnns y anns s0 ps s1 → (∀ a ∈ anns, a.annotations.val = []) → ps.length = anns.length := by
  intro anns
  induction anns with
  | nil => intro s0 ps s1 h _; obtain ⟨rfl, -⟩ := tanns_nil h; rfl
  | cons a rest ih =>
    intro s0 ps s1 h plain
    cases h with
    | cons _ _ _ _ sMid _ p q ha hrest =>
      obtain ⟨n, rfl, rfl, -⟩ := tann_plain ha (plain a (by simp))
      simp [ih hrest (fun b m => plain b (List.mem_cons_of_mem _ m))]

section

variable {o : model.RawOntology} {triples : alloc.vec.Vec rdf.Triple} {header : List Pattern} {bs : List ABlock}
  {supply : Supply}

/-- The axiom part of the first block of the loop is ready to be read. -/
theorem agraph_core_ready (g : AGraph o triples.val header bs supply) {s : rdf_mapping.State} {b : ABlock}
    {rest : List ABlock} (bIn : b ∈ bs) (state : ALoop triples s (b :: rest)) :
    Ready triples s b.core.pos b.core.pats b.core.fresh where
  complete := state.complete
  holds := ((agraph_split_at g) bIn).1
  nodup := by
    have nodup := (g.blocks b bIn).2.2.1
    simp only [ABlock.pos] at nodup
    exact (List.nodup_append.mp nodup).1
  free := fun i m => state.free b (by simp) i (List.mem_append_left _ m)
  owns := by
    intro i t y at_i unused about yIn
    have inB := (agraph_owner g) bIn at_i about (List.mem_append_left _ yIn)
    simp only [ABlock.pos, List.mem_append] at inB
    rcases inB with inCore | inA
    · exact inCore
    · exfalso
      obtain ⟨main, side, -, -, -, part⟩ := (agraph_shape g) bIn
      obtain ⟨q, qIn, fits⟩ := at_mem ((agraph_split_at g) bIn).2 inA at_i
      rcases part with ⟨-, empty, -⟩ | ⟨-, x, heads, sx, afreshIs, apatsIs, tanns, -⟩
      · rw [empty] at qIn; simp at qIn
      · have plain : ∀ a ∈ b.ann.val, a.annotations.val = [] := fun a m => ((g.blocks b bIn).1.plain a m).1
        have subjectX : q.subject = .blank x := by
          rw [apatsIs] at qIn
          rcases List.mem_append.mp qIn with inR | inH
          · simp only [reification, List.mem_cons, List.not_mem_nil, or_false] at inR
            rcases inR with rfl | rfl | rfl | rfl <;> rfl
          · exact (tanns_heads tanns plain q inH).1
        have := fits.1
        rw [about, subjectX] at this
        simp only [Node.blank.injEq] at this
        rw [this] at yIn
        exact (agraph_reifier_not_core g) bIn afreshIs yIn
  room := by
    have room := state.room
    simp only [List.flatMap_cons, List.length_append, ABlock.fresh] at room
    omega

/-- The axiom part of a block is read from any position whose triple
    instantiates its main pattern, when its other positions are ready. -/
theorem agraph_block_reads (g : AGraph o triples.val header bs supply) {kinds : rdf_mapping.Kinds}
    (hk : KindsOf kinds o.axioms.val) {c : ABlock} (cIn : c ∈ bs) {s : rdf_mapping.State} {a : Usize}
    {pos : List Nat} (ready : Ready triples s (a.val :: pos) c.core.pats c.core.fresh) :
    ∃ s', rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found c.core.ax s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) c.core.fresh ∧ ShapeOk triples a c.core.ax c.core.fresh := by
  obtain ⟨image, -, -, -⟩ := g.blocks c cIn
  have stripped := readable_strip g.readable
  obtain ⟨ax, axIn, axIs, -⟩ := image.core.member
  obtain ⟨s1, tax⟩ := image.core.forward
  obtain ⟨allowed, typed⟩ := readable_uses stripped axIn
  have axReadable := (stripped.axioms ax axIn).2
  rw [axIs] at allowed typed axReadable
  have nodupCore : c.core.fresh.Nodup := by
    have := (agraph_fresh_nodup g) cIn
    simp only [ABlock.fresh] at this
    exact (List.nodup_append.mp this).1
  exact axiom_reads_core triples kinds (strip_kinds hk) tax axReadable allowed typed
    (fun p sub v isAnnotation x node => by
      apply (agraph_not_reifier_type g)
      intro inSupply
      cases sub with
      | Iri _ => simp [annotationSubjectNode, iriNode] at node
      | Anonymous an =>
        simp only [annotationSubjectNode, anonymousNode, Node.blank.injEq] at node
        subst node
        exact g.fresh c.ax image.member an (by simp [ABlock.ax, isAnnotation, subjectAnonymous]) inSupply)
    c.core.fresh rfl nodupCore s a pos ready

end

theorem fresh_length_le {d : ABlock} : ∀ {rest : List ABlock}, d ∈ rest →
    d.fresh.length ≤ (rest.flatMap ABlock.fresh).length := by
  intro rest
  induction rest with
  | nil => intro m; simp at m
  | cons c cs ih =>
    intro m
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp m with rfl | inCs
    · omega
    · have := ih inCs; omega

section

variable {o : model.RawOntology} {triples : alloc.vec.Vec rdf.Triple} {header : List Pattern} {bs : List ABlock}
  {supply : Supply}

theorem agraph_apart_of_ne (g : AGraph o triples.val header bs supply) {b c : ABlock} (bIn : b ∈ bs) (cIn : c ∈ bs)
    (ne : b ≠ c) : AApart b c :=
  g.disjoint.forall bIn cIn ne

/-- Two blocks of the graph with the same axiom are blocks of unannotated axioms. -/
theorem agraph_once_blocks (g : AGraph o triples.val header bs supply) {b c : ABlock} (bIn : b ∈ bs) (cIn : c ∈ bs)
    (ne : b ≠ c) (same : b.core.ax = c.core.ax) : b.ann.val = [] ∧ c.ann.val = [] := by
  have pairwise : bs.Pairwise (fun b c : ABlock => b.ax.axiom = c.ax.axiom →
      b.ax.annotations.val = [] ∧ c.ax.annotations.val = []) := by
    have := g.readable.once
    rw [← g.axiomsIs] at this
    exact List.pairwise_map.mp this
  have symm : Std.Symm (fun b c : ABlock => b.ax.axiom = c.ax.axiom →
      b.ax.annotations.val = [] ∧ c.ax.annotations.val = []) := ⟨fun _ _ h e => (h e.symm).symm⟩
  exact pairwise.forall bIn cIn ne same

/-- **The reader takes the reification of an annotated axiom for no other
    axiom.** In a loop state before the blocks `b :: rest`, a blank node that
    the unused triples make reify the main triple of `b` as an axiom is the
    reifying node of `b`, and the positions are those of its reification. -/
theorem agraph_exclusive (g : AGraph o triples.val header bs supply) {kinds : rdf_mapping.Kinds}
    (hk : KindsOf kinds o.axioms.val) {s : rdf_mapping.State} {b : ABlock} {rest : List ABlock}
    (members : ∀ c ∈ b :: rest, c ∈ bs) (state : ALoop triples s (b :: rest)) {main : Pattern}
    {side : List Pattern} (pIs : b.core.pats = main :: side) (facts : MainFacts (strip o) b.core.ax b.core.fresh main)
    {t : rdf.Triple} (at_t : triples.val[b.core.main]? = some t) (fits : Matches main t)
    (found : Usize × Usize × Usize × Usize) (x : rdf.BlankNode)
    (ok : ReifierOk triples.val s.used.val t owlAxiom found x) :
    ∃ (heads : List Pattern) (sx : Supply) (p0 p1 p2 p3 : Nat) (hs : List Nat), b.ann.val ≠ [] ∧ b.afresh = [x] ∧
      b.apats = reification owlAxiom x main ++ heads ∧ TAnns (.blank x) b.ann.val sx heads sx ∧
      b.apos = p0 :: p1 :: p2 :: p3 :: hs ∧
      found.1.val = p1 ∧ found.2.1.val = p2 ∧ found.2.2.1.val = p3 ∧ found.2.2.2.val = p0 := by
  have bIn := members b (by simp)
  obtain ⟨ts, tp, tt, ty, uS, uP, uT, uY, subjectS, fS, fP, fT, fY⟩ := ok
  obtain ⟨d, dIn, mainD, sideD, xD, headsD, sxD, q0, q1, q2, q3, hsD, pIsD, -, nonemptyD, afreshD, apatsD, tannsD,
    -, layoutD, srcPos, fitsSD⟩ := (agraph_source_triple g) uS.1 fS.2.1
  have xSame : xD = x := by
    have := fitsSD.1
    rw [subjectS] at this
    simp only [subjectView, Node.blank.injEq] at this
    exact this.symm
  rw [xSame] at afreshD apatsD tannsD
  obtain ⟨r0, r1, r2, r3, hsR, layoutD', typing, source, property, target, holdsH⟩ :=
    (agraph_reified_layout g) dIn apatsD
  have rSame : r0 = q0 ∧ r1 = q1 ∧ r2 = q2 ∧ r3 = q3 ∧ hsR = hsD := by
    rw [layoutD] at layoutD'
    simp only [List.cons.injEq] at layoutD'
    obtain ⟨h0, h1, h2, h3, h4⟩ := layoutD'
    exact ⟨h0.symm, h1.symm, h2.symm, h3.symm, h4.symm⟩
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := rSame
  -- the property, target and typing triples are those of the reification of `d`
  have propertyPos : found.2.1.val = r2 ∧ objectView tp.object = .iri mainD.predicate := by
    rcases (agraph_reifier_triple g) dIn afreshD tannsD layoutD typing source property target holdsH uP.1 fP.1 with
      ⟨-, f⟩ | ⟨-, f⟩ | ⟨pos, f⟩ | ⟨-, f⟩ | ⟨-, a, aIn, spelled⟩
    · exfalso; have := f.2.1; rw [fP.2.1] at this; simp [owlAnnotatedProperty, rdfType] at this
    · exfalso; have := f.2.1; rw [fP.2.1] at this; simp [owlAnnotatedProperty, owlAnnotatedSource] at this
    · exact ⟨pos, f.2.2⟩
    · exfalso; have := f.2.1; rw [fP.2.1] at this; simp [owlAnnotatedProperty, owlAnnotatedTarget] at this
    · exact absurd (spelled.symm.trans fP.2.1) ((agraph_annotation_not_vocabulary g) dIn aIn owlAnnotatedProperty
        (by simp [mappingVocabulary]))
  have targetPos : found.2.2.1.val = r3 ∧ objectView tt.object = mainD.object := by
    rcases (agraph_reifier_triple g) dIn afreshD tannsD layoutD typing source property target holdsH uT.1 fT.1 with
      ⟨-, f⟩ | ⟨-, f⟩ | ⟨-, f⟩ | ⟨pos, f⟩ | ⟨-, a, aIn, spelled⟩
    · exfalso; have := f.2.1; rw [fT.2.1] at this; simp [owlAnnotatedTarget, rdfType] at this
    · exfalso; have := f.2.1; rw [fT.2.1] at this; simp [owlAnnotatedTarget, owlAnnotatedSource] at this
    · exfalso; have := f.2.1; rw [fT.2.1] at this; simp [owlAnnotatedTarget, owlAnnotatedProperty] at this
    · exact ⟨pos, f.2.2⟩
    · exact absurd (spelled.symm.trans fT.2.1) ((agraph_annotation_not_vocabulary g) dIn aIn owlAnnotatedTarget
        (by simp [mappingVocabulary]))
  have typingPos : found.2.2.2.val = r0 := by
    rcases (agraph_reifier_triple g) dIn afreshD tannsD layoutD typing source property target holdsH uY.1 fY.1 with
      ⟨pos, -⟩ | ⟨-, f⟩ | ⟨-, f⟩ | ⟨-, f⟩ | ⟨-, a, aIn, spelled⟩
    · exact pos
    · exfalso; have := f.2.1; rw [fY.2.1] at this; simp [rdfType, owlAnnotatedSource] at this
    · exfalso; have := f.2.1; rw [fY.2.1] at this; simp [rdfType, owlAnnotatedProperty] at this
    · exfalso; have := f.2.1; rw [fY.2.1] at this; simp [rdfType, owlAnnotatedTarget] at this
    · exact absurd (spelled.symm.trans fY.2.1) ((agraph_annotation_not_vocabulary g) dIn aIn rdfType
        (by simp [mappingVocabulary]))
  -- the main patterns agree
  have mainSame : mainD = main := by
    rw [pattern_of_matches fits]
    obtain ⟨sD, prD, oD⟩ := mainD
    simp only [Pattern.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · have h1 := fitsSD.2.2
      have h2 := fS.2.2
      exact h1.symm.trans h2
    · have h1 := propertyPos.2
      have h2 := fP.2.2
      rw [h1] at h2
      simpa using h2
    · exact targetPos.2.symm.trans fT.2.2
  subst mainSame
  by_cases same : d = b
  · subst same
    exact ⟨headsD, sxD, r0, r1, r2, r3, hsR, nonemptyD, afreshD, apatsD, tannsD, layoutD', srcPos, propertyPos.1,
      targetPos.1, typingPos⟩
  · exfalso
    -- `d` is a later block: its source triple is unused
    have dLater : d ∈ rest := by
      obtain ⟨c, cIn, inC⟩ := state.covered found.1.val uS.2
      have inD : found.1.val ∈ d.pos := by
        simp only [ABlock.pos, List.mem_append]
        exact Or.inr (by rw [layoutD', srcPos]; simp)
      have cd : c = d := by
        apply Classical.byContradiction
        intro ne
        exact (agraph_apart_of_ne g) (members c cIn) dIn ne _ inC inD
      subst cd
      rcases List.mem_cons.mp cIn with h | h
      · exact absurd h same
      · exact h
    obtain ⟨a, aIs⟩ := usize_of_position at_t
    -- the axiom part of `d`, read from the main position of `b`
    have holdsD := ((agraph_split_at g) dIn).1
    rw [pIsD] at holdsD
    simp only [Block.pos] at holdsD
    obtain ⟨-, holdsSide⟩ := List.forall₂_cons.mp holdsD
    have bd : AApart b d := (agraph_apart_of_ne g) bIn dIn (Ne.symm same)
    have mainInB : b.core.main ∈ b.pos := by simp [ABlock.pos, Block.pos]
    have readyD : Ready triples s (a.val :: d.core.rest) d.core.pats d.core.fresh :=
      { complete := state.complete
        holds := by rw [pIsD, aIs]; exact List.Forall₂.cons ⟨t, at_t, fits⟩ holdsSide
        nodup := by
          have nodup := (g.blocks d dIn).2.2.1
          simp only [ABlock.pos, Block.pos, List.nodup_append, List.nodup_cons] at nodup
          refine List.nodup_cons.mpr ⟨?_, nodup.1.2⟩
          intro inRest
          rw [aIs] at inRest
          exact bd _ mainInB (by simp [ABlock.pos, Block.pos, inRest])
        free := by
          intro i m
          rcases List.mem_cons.mp m with rfl | inRest
          · rw [aIs]; exact state.free b (by simp) _ mainInB
          · exact state.free d (by simp [dLater]) i (by simp [ABlock.pos, Block.pos, inRest])
        owns := by
          intro i u y at_i unused about yIn
          have inD := (agraph_owner g) dIn at_i about (List.mem_append_left _ yIn)
          simp only [ABlock.pos, List.mem_append] at inD
          rcases inD with inCore | inA
          · simp only [Block.pos, List.mem_cons] at inCore
            rcases inCore with rfl | inRest
            · exfalso
              have mainAt : ∃ t', triples.val[d.core.main]? = some t' ∧ Matches mainD t' := by
                have := ((agraph_split_at g) dIn).1
                rw [pIsD] at this
                simp only [Block.pos] at this
                exact (List.forall₂_cons.mp this).1
              obtain ⟨t', at', fits'⟩ := mainAt
              rw [at_i] at at'
              cases at'
              rcases facts.blank y (fits'.1.symm.trans about) with inB | ⟨an, isSome, yIs⟩
              · exact same ((agraph_fresh_unique g) dIn bIn (List.mem_append_left _ yIn) (List.mem_append_left _ inB))
              · obtain ⟨image, -, -, -⟩ := g.blocks b bIn
                have notIn := g.fresh b.ax image.member an isSome
                rw [← yIs] at notIn
                exact notIn ((agraph_in_supply g) dIn (List.mem_append_left _ yIn))
            · exact List.mem_cons_of_mem _ inRest
          · exfalso
            obtain ⟨q, qIn, fitsQ⟩ := at_mem ((agraph_split_at g) dIn).2 inA at_i
            have plain : ∀ a ∈ d.ann.val, a.annotations.val = [] := fun a m => ((g.blocks d dIn).1.plain a m).1
            have subjectX : q.subject = .blank x := by
              rw [apatsD] at qIn
              rcases List.mem_append.mp qIn with inR | inH
              · simp only [reification, List.mem_cons, List.not_mem_nil, or_false] at inR
                rcases inR with rfl | rfl | rfl | rfl <;> rfl
              · exact (tanns_heads tannsD plain q inH).1
            have := fitsQ.1
            rw [about, subjectX] at this
            simp only [Node.blank.injEq] at this
            rw [this] at yIn
            exact (agraph_reifier_not_core g) dIn afreshD yIn
        room := by
          have room := state.room
          have le := fresh_length_le dLater
          simp only [List.flatMap_cons, List.length_append, ABlock.fresh] at room le
          omega }
    obtain ⟨sD, readD, -, -⟩ := (agraph_block_reads g) hk dIn readyD
    obtain ⟨sB, readB, -, -⟩ := (agraph_block_reads g) hk bIn (pos := b.core.rest)
      (by rw [aIs]; exact (agraph_core_ready g) bIn state)
    rw [readB] at readD
    have axSame : b.core.ax = d.core.ax := by
      have := Result.ok_injective readD
      simp only [rdf_mapping.Read.Found.injEq] at this
      exact this.1
    exact nonemptyD ((agraph_once_blocks g) bIn dIn (Ne.symm same) axSame).2

end

section

variable {o : model.RawOntology} {triples : alloc.vec.Vec rdf.Triple} {header : List Pattern} {bs : List ABlock}
  {supply : Supply}

/-- The positions of the annotation triples of a block increase. -/
def ABlock.Ordered (b : ABlock) : Prop := (b.apos.drop 4).Pairwise (· < ·)

theorem heads_zip {triples : List rdf.Triple} {x : rdf.BlankNode} :
    ∀ {anns : List model.Annotation} {sx : Supply} {heads : List Pattern} {hs : List Nat},
      TAnns (.blank x) anns sx heads sx → (∀ a ∈ anns, a.annotations.val = []) → At triples hs heads →
      HeadsOf triples x (hs.zip anns) ∧ (hs.zip anns).map Prod.fst = hs ∧ (hs.zip anns).map Prod.snd = anns := by
  intro anns
  induction anns with
  | nil =>
    intro sx heads hs h _ holds
    obtain ⟨rfl, -⟩ := tanns_nil h
    have : hs = [] := by have := at_length holds; simpa using this
    subst this
    simp [HeadsOf]
  | cons a rest ih =>
    intro sx heads hs h plain holds
    cases h with
    | cons _ _ _ _ sMid _ p q ha hrest =>
      obtain ⟨n, rfl, rfl, valueNode⟩ := tann_plain ha (plain a (by simp))
      obtain ⟨h0, hs', rfl, ⟨t, at_t, fits⟩, holdsRest⟩ : ∃ h0 hs', hs = h0 :: hs' ∧
          (∃ t, triples[h0]? = some t ∧ Matches ⟨.blank x, a.property.iri.spelling.val, n⟩ t) ∧
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

/-- **Every block of the axiom loop is read with its annotations.** In a loop
    state before the blocks `b :: rest` of the graph, `read_axiom` reads the
    axiom of `b` from its main position, and `annotate` the annotations of its
    reification in the order of their positions, using exactly the positions of
    `b` and recording exactly its blank nodes. -/
theorem agraph_step (g : AGraph o triples.val header bs supply) {kinds : rdf_mapping.Kinds} (hk : KindsOf kinds o.axioms.val)
    (s : rdf_mapping.State) (b : ABlock) (rest : List ABlock) (members : ∀ c ∈ b :: rest, c ∈ bs)
    (state : ALoop triples s (b :: rest)) (a : Usize) (aIs : a.val = b.core.main) :
    ∃ (s1 s' : rdf_mapping.State) (v : alloc.vec.Vec model.Annotation),
      rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found b.ax.axiom s1) ∧
      rdf_mapping.annotate triples kinds a b.ax.axiom s1 (alloc.vec.Vec.len triples) =
        .ok (some (⟨v, b.ax.axiom⟩, s')) ∧ v.val.Perm b.ann.val ∧ (b.Ordered → v = b.ann) ∧
      Marked s s' (fun i => i ∈ b.pos) b.fresh := by
  have bIn := members b (by simp)
  have ready := (agraph_core_ready g) bIn state
  obtain ⟨s1, readRun, markedCore, shape⟩ := (agraph_block_reads g) hk bIn (a := a) (pos := b.core.rest)
    (by rw [aIs]; exact ready)
  obtain ⟨main, side, pIs, sides, facts, part⟩ := (agraph_shape g) bIn
  have holdsCore := ((agraph_split_at g) bIn).1
  rw [pIs] at holdsCore
  simp only [Block.pos] at holdsCore
  obtain ⟨⟨t, at_t, fits⟩, -⟩ := List.forall₂_cons.mp holdsCore
  have at_a : triples.val[a.val]? = some t := by rw [aIs]; exact at_t
  have axIs : b.ax.axiom = b.core.ax := rfl
  rw [axIs]
  have posNodup := (g.blocks b bIn).2.2.1
  have aposIs := (g.blocks b bIn).2.2.2
  have coreIs : ∀ i, i ∈ a.val :: b.core.rest ↔ i ∈ b.core.pos := by
    intro i; simp [Block.pos, aIs]
  rcases part with ⟨annNil, apatsNil, afreshNil⟩ | ⟨nonempty, x, heads, sx, afreshIs, apatsIs, tanns, one⟩
  · -- an unannotated axiom
    have aposNil : b.apos = [] := by
      have := aposIs
      rw [apatsNil] at this
      exact List.eq_nil_of_length_eq_zero this
    have posIs : ∀ i, i ∈ a.val :: b.core.rest ↔ i ∈ b.pos := by
      intro i; simp [ABlock.pos, aposNil, Block.pos, aIs]
    have freshIs : b.core.fresh = b.fresh := by simp [ABlock.fresh, afreshNil]
    have axEq : (⟨alloc.vec.Vec.new _, b.core.ax⟩ : model.AnnotatedAxiom) = b.ax := by
      simp only [ABlock.ax]
      rw [vec_eq_of_val (u := alloc.vec.Vec.new _) (v := b.ann) (by rw [annNil]; rfl)]
    have marked : Marked s s1 (fun i => i ∈ b.pos) b.fresh :=
      marked_fresh_eq (marked_same markedCore posIs) freshIs
    have vEq : (alloc.vec.Vec.new model.Annotation) = b.ann :=
      vec_eq_of_val (by rw [annNil]; rfl)
    rcases shape with ⟨shape1, -⟩ | ⟨shape0, t0, x0, at0, subject0, inFresh⟩
    · refine ⟨s1, s1, alloc.vec.Vec.new _, readRun, ?_, by rw [annNil]; rfl, fun _ => vEq, marked⟩
      apply annotate_main triples kinds a b.core.ax s1 _ shape1
      intro kind kindIs
      apply reified_absent triples kinds a kind s1 _ t at_a
      intro f x' ok
      rw [kindIs] at ok
      obtain ⟨-, -, -, -, -, -, -, nonempty, -⟩ := (agraph_exclusive g) hk members state pIs facts at_t fits f x'
        (reifier_ok_back markedCore ok)
      exact nonempty annNil
    · refine ⟨s1, s1, alloc.vec.Vec.new _, readRun, ?_, by rw [annNil]; rfl, fun _ => vEq, marked⟩
      apply annotate_blank triples kinds a b.core.ax s1 _ shape0 t0 at0 x0 subject0
      intro i t' at_i unused about
      have before := marked_back markedCore unused
      have member := ready.owns i t' x0 at_i before about inFresh
      have inside : i < s.used.val.length := (List.getElem?_eq_some_iff.mp before).1
      rw [marked_used markedCore inside ((coreIs i).mpr member)] at unused
      cases unused
  · -- an annotated axiom: its main triple, reified by `x`
    rcases shape with ⟨shape1, -⟩ | ⟨shape0, -⟩
    swap
    · rw [one] at shape0
      exact absurd (Result.ok_injective shape0) (by decide)
    obtain ⟨p0, p1, p2, p3, hs, layout, ⟨tY, atY, fitsY⟩, ⟨tS, atS, fitsS⟩, ⟨tP, atP, fitsP⟩, ⟨tT, atT, fitsT⟩,
      holdsH⟩ := (agraph_reified_layout g) bIn apatsIs
    have plain : ∀ a ∈ b.ann.val, a.annotations.val = [] := fun a m => ((g.blocks b bIn).1.plain a m).1
    have xIn : x ∈ b.fresh := by simp [ABlock.fresh, afreshIs]
    -- the positions of the annotation part are free in `s1`
    have inApos : ∀ i ∈ b.apos, i ∈ b.pos := fun i m => List.mem_append_right _ m
    have freeA : ∀ i ∈ b.apos, s1.used.val[i]? = some false := by
      intro i m
      refine marked_unused markedCore (state.free b (by simp) i (inApos i m)) ?_
      intro inCore
      rw [coreIs] at inCore
      simp only [ABlock.pos] at posNodup
      exact (List.nodup_append.mp posNodup).2.2 i inCore i m rfl
    have aposNodup : b.apos.Nodup := by
      simp only [ABlock.pos] at posNodup
      exact (List.nodup_append.mp posNodup).2.1
    rw [layout] at freeA aposNodup
    simp only [List.nodup_cons, List.mem_cons, not_or] at aposNodup
    obtain ⟨⟨n01, n02, n03, n0h⟩, ⟨n12, n13, n1h⟩, ⟨n23, n2h⟩, n3h, hsNodup⟩ := aposNodup
    obtain ⟨uY, uYIs⟩ := usize_of_position atY
    obtain ⟨uS, uSIs⟩ := usize_of_position atS
    obtain ⟨uP, uPIs⟩ := usize_of_position atP
    obtain ⟨uT, uTIs⟩ := usize_of_position atT
    let found : Usize × Usize × Usize × Usize := (uS, uP, uT, uY)
    have mainIs := pattern_of_matches fits
    have okRe : ∀ kind : Slice U8, kind.val = owlAxiom → ReifierOk triples.val s1.used.val t kind.val found x := by
      intro kind kindIs
      rw [kindIs]
      refine ⟨tS, tP, tT, tY, ⟨by rw [uSIs]; exact atS, by rw [uSIs]; exact freeA _ (by simp)⟩,
        ⟨by rw [uPIs]; exact atP, by rw [uPIs]; exact freeA _ (by simp)⟩,
        ⟨by rw [uTIs]; exact atT, by rw [uTIs]; exact freeA _ (by simp)⟩,
        ⟨by rw [uYIs]; exact atY, by rw [uYIs]; exact freeA _ (by simp)⟩, subject_blank fitsS.1, ?_, ?_, ?_, fitsY⟩
      · rw [mainIs] at fitsS; exact fitsS
      · rw [mainIs] at fitsP; exact fitsP
      · rw [mainIs] at fitsT; exact fitsT
    -- the triples of the reifying node in `s1`
    have classify := fun {j : Nat} {u : rdf.Triple} (at_j : triples.val[j]? = some u)
        (about : subjectView u.subject = .blank x) =>
      (agraph_reifier_triple g) bIn afreshIs tanns layout ⟨tY, atY, fitsY⟩ ⟨tS, atS, fitsS⟩ ⟨tP, atP, fitsP⟩
        ⟨tT, atT, fitsT⟩ holdsH at_j about
    have reifierRun : ∀ kind : Slice U8, kind.val = owlAxiom →
        rdf_mapping.reifier triples s1 t kind = .ok (some found) := by
      intro kind kindIs
      apply reifier_found triples s1 t kind (by rw [markedCore.subjects]; exact state.complete)
        (by rw [markedCore.sources]; exact state.sources) found x (okRe kind kindIs)
      · intro j u at_j _ about named
        rcases classify at_j about with ⟨-, f⟩ | ⟨-, f⟩ | ⟨pos, -⟩ | ⟨-, f⟩ | ⟨-, a, aIn, spelled⟩
        · exfalso; have := f.2.1; rw [named] at this; simp [owlAnnotatedProperty, rdfType] at this
        · exfalso; have := f.2.1; rw [named] at this; simp [owlAnnotatedProperty, owlAnnotatedSource] at this
        · rw [pos, ← uPIs]
        · exfalso; have := f.2.1; rw [named] at this; simp [owlAnnotatedProperty, owlAnnotatedTarget] at this
        · exact absurd (spelled.symm.trans named)
            ((agraph_annotation_not_vocabulary g) bIn aIn owlAnnotatedProperty (by simp [mappingVocabulary]))
      · intro j u at_j _ about named
        rcases classify at_j about with ⟨-, f⟩ | ⟨-, f⟩ | ⟨-, f⟩ | ⟨pos, -⟩ | ⟨-, a, aIn, spelled⟩
        · exfalso; have := f.2.1; rw [named] at this; simp [owlAnnotatedTarget, rdfType] at this
        · exfalso; have := f.2.1; rw [named] at this; simp [owlAnnotatedTarget, owlAnnotatedSource] at this
        · exfalso; have := f.2.1; rw [named] at this; simp [owlAnnotatedTarget, owlAnnotatedProperty] at this
        · rw [pos, ← uTIs]
        · exact absurd (spelled.symm.trans named)
            ((agraph_annotation_not_vocabulary g) bIn aIn owlAnnotatedTarget (by simp [mappingVocabulary]))
      · intro j u at_j _ about named _
        rcases classify at_j about with ⟨pos, -⟩ | ⟨-, f⟩ | ⟨-, f⟩ | ⟨-, f⟩ | ⟨-, a, aIn, spelled⟩
        · rw [pos, ← uYIs]
        · exfalso; have := f.2.1; rw [named] at this; simp [rdfType, owlAnnotatedSource] at this
        · exfalso; have := f.2.1; rw [named] at this; simp [rdfType, owlAnnotatedProperty] at this
        · exfalso; have := f.2.1; rw [named] at this; simp [rdfType, owlAnnotatedTarget] at this
        · exact absurd (spelled.symm.trans named)
            ((agraph_annotation_not_vocabulary g) bIn aIn rdfType (by simp [mappingVocabulary]))
      · intro f x' ok
        rw [kindIs] at ok
        obtain ⟨heads', sx', q0, q1, q2, q3, hs', -, -, -, -, layout', f1, f2, f3, f4⟩ :=
          (agraph_exclusive g) hk members state pIs facts at_t fits f x' (reifier_ok_back markedCore ok)
        have qSame : q0 = p0 ∧ q1 = p1 ∧ q2 = p2 ∧ q3 = p3 := by
          rw [layout] at layout'
          simp only [List.cons.injEq] at layout'
          exact ⟨layout'.1.symm, layout'.2.1.symm, layout'.2.2.1.symm, layout'.2.2.2.1.symm⟩
        obtain ⟨rfl, rfl, rfl, rfl⟩ := qSame
        obtain ⟨f1', f2', f3', f4'⟩ := f
        simp only at f1 f2 f3 f4
        simp only [found, Prod.mk.injEq]
        exact ⟨UScalar.eq_of_val_eq (by rw [f1, uSIs]), UScalar.eq_of_val_eq (by rw [f2, uPIs]),
          UScalar.eq_of_val_eq (by rw [f3, uTIs]), UScalar.eq_of_val_eq (by rw [f4, uYIs])⟩
    -- the reifying node recorded, and its annotations read
    have mFour := marked_take_four s1 found
    have roomX : (takeFour s1 found).blanks.val.length < Usize.max := by
      have room := state.room
      have blanks := markedCore.blanks
      simp only [takeFour]
      rw [blanks]
      simp only [List.flatMap_cons, List.length_append, ABlock.fresh, afreshIs] at room ⊢
      simp only [List.length_cons, List.length_nil] at room
      omega
    obtain ⟨s2, recordRun, mRecord⟩ := record_ok (takeFour s1 found) x roomX
    have annLength : heads.length = b.ann.val.length := tanns_length tanns plain
    have hsLength : hs.length = heads.length := at_length holdsH
    have hsBound : hs.length ≤ triples.val.length := by
      have sub : hs ⊆ List.range triples.val.length := by
        intro i m
        rw [List.mem_range]
        obtain ⟨k, hk, kIs⟩ := List.getElem_of_mem m
        obtain ⟨-, tl, atl, -⟩ := at_get holdsH (k := k) (i := i) (by rw [List.getElem?_eq_getElem hk, kIs])
        exact (List.getElem?_eq_some_iff.mp atl).1
      have := (List.Nodup.subperm hsNodup sub).length_le
      simpa using this
    have freeH : ∀ i ∈ hs, s2.used.val[i]? = some false := by
      intro i m
      refine marked_unused mRecord (marked_unused mFour (freeA i (by simp [m])) ?_) (by simp)
      simp only [found]
      rw [uSIs, uPIs, uTIs, uYIs]
      intro h
      rcases h with rfl | rfl | rfl | rfl
      · exact n1h m
      · exact n2h m
      · exact n3h m
      · exact n0h m
    have confinedH : ∀ (i : Nat) (u : rdf.Triple), triples.val[i]? = some u → s2.used.val[i]? = some false →
        subjectView u.subject = .blank x → i ∈ hs := by
      intro i u at_i unused about
      have before := marked_back mRecord unused
      rcases classify at_i about with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨inH, -⟩
      all_goals first
        | exact inH
        | (exfalso
           have inside : _ < s1.used.val.length := (List.getElem?_eq_some_iff.mp (marked_back mFour before)).1
           rw [marked_used mFour inside (by simp only [found]; rw [uSIs, uPIs, uTIs, uYIs]; simp)] at before
           cases before)
    obtain ⟨headsOf, fsts, snds⟩ := heads_zip tanns plain holdsH (triples := triples.val)
    have kindsOk : ∀ a ∈ b.ann.val, rdf_mapping.property_kind kinds a.property.iri.spelling = .ok (some .Annotation) :=
      fun a m => (annotation_property_facts g.readable hk (annotation_row_axiom (g.blocks b bIn).1.member m)).1
    obtain ⟨v, s3, l, nodeRun, vIs, lPerm, mNode⟩ := node_annotations_any triples kinds x
      (agraph_no_annotation_kind g) _ (hs.zip b.ann.val) s2 (alloc.vec.Vec.new _) (alloc.vec.Vec.len triples) rfl
      headsOf (by rw [fsts]; exact hsNodup)
      (fun r m => by
        have aIn := (List.of_mem_zip m).2
        exact ⟨plain r.2 aIn, ((g.blocks b bIn).1.plain r.2 aIn).2, kindsOk r.2 aIn⟩)
      (by rw [mRecord.subjects, mFour.subjects, markedCore.subjects]; exact state.complete)
      (by rw [mRecord.subjects, mFour.subjects, markedCore.subjects]; exact state.sorted)
      (fun r m => freeH r.1 (List.of_mem_zip m).1)
      (fun i u at_i unused about => by rw [fsts]; exact confinedH i u at_i unused about)
      (by simp [alloc.vec.Vec.len_val]; omega) (by simp)
    rw [snds] at lPerm
    have vIs' : v.val = l := by simpa using vIs
    have vPerm : v.val.Perm b.ann.val := by rw [vIs']; exact lPerm
    have nonemptyV : v.val ≠ [] := by
      intro empty
      rw [empty] at vPerm
      exact nonempty (List.Perm.nil_eq vPerm).symm
    refine ⟨s1, s3, v, readRun, ?_, vPerm, ?_, ?_⟩
    · apply annotate_main triples kinds a b.core.ax s1 _ shape1 v s3
      intro kind kindIs
      exact reified_found triples kinds a kind s1 _ t at_a found (reifierRun kind kindIs) tS
        (by simp only [found]; rw [uSIs]; exact atS) x (subject_blank fitsS.1) s2 recordRun v s3 nodeRun
        nonemptyV
    · intro ordered
      have increasing : hs.Pairwise (· < ·) := by
        unfold ABlock.Ordered at ordered
        rw [layout] at ordered
        simpa using ordered
      obtain ⟨v', s3', nodeRun', vIs', -⟩ := node_annotations_plain triples kinds x (agraph_no_annotation_kind g)
        b.ann.val tanns plain (fun a m => ((g.blocks b bIn).1.plain a m).2) kindsOk hs s2 (alloc.vec.Vec.new _)
        (alloc.vec.Vec.len triples)
        (by rw [mRecord.subjects, mFour.subjects, markedCore.subjects]; exact state.complete)
        (by rw [mRecord.subjects, mFour.subjects, markedCore.subjects]; exact state.sorted)
        holdsH increasing freeH confinedH (by simp [alloc.vec.Vec.len_val]; omega) (by simp)
      rw [nodeRun] at nodeRun'
      have same := Option.some.inj (Result.ok_injective nodeRun')
      simp only [Prod.mk.injEq] at same
      rw [same.1]
      exact vec_eq_of_val (by rw [vIs']; simp)
    · have m := marked_trans (marked_trans (marked_trans markedCore mFour) mRecord) mNode
      refine marked_fresh_eq (marked_same m (fun i => ?_)) (by simp [ABlock.fresh, afreshIs])
      simp only [ABlock.pos, List.mem_append, layout, List.mem_cons, found, uSIs, uPIs, uTIs, uYIs, fsts] at ⊢
      rw [← coreIs]
      simp only [List.mem_cons]
      tauto

end

/-! ### The header and the declarations of the graph -/

/-- The forward header of an ontology with annotations without annotations of
    their own: the header patterns of `RdfReadOntology` and then one triple
    per annotation. -/
theorem header_annotated {o : model.RawOntology} (plain : PlainAnnotations o.annotations.val) {supply rest : Supply}
    {header : List Pattern} (h : THeader o supply header rest) :
    ∃ heads, header = headerPatterns o ++ heads ∧ rest = supply ∧
      (o.identity = .Anonymous → heads = [] ∧ o.imports.val = [] ∧ o.annotations.val = []) ∧
      (∀ iri version, o.identity = .Named iri version → TAnns (iriNode iri) o.annotations.val supply heads supply) := by
  cases h with
  | anonymous _ hid importsEmpty annotationsEmpty =>
    refine ⟨[], by simp [headerPatterns, hid], rfl, fun _ => ⟨rfl, importsEmpty, annotationsEmpty⟩, ?_⟩
    intro iri version named
    rw [hid] at named
    cases named
  | named iri version s s' anns hid tanns =>
    have plainAll : ∀ a ∈ o.annotations.val, a.annotations.val = [] := fun a m => (plain a m).1
    have same := tanns_plain_supply tanns plainAll
    subst same
    refine ⟨anns, ?_, rfl, (fun anonymous => by rw [hid] at anonymous; cases anonymous), ?_⟩
    · cases version <;> simp [headerPatterns, hid]
    · intro iri' version' named
      rw [hid] at named
      simp only [model.OntologyIdentity.Named.injEq] at named
      obtain ⟨rfl, -⟩ := named
      exact tanns

section

variable {o : model.RawOntology} {triples : List rdf.Triple} {header : List Pattern} {bs : List ABlock}
  {supply : Supply}

/-- A triple at a position of the annotation part of a block is about its reifying node. -/
theorem agraph_apos_subject (g : AGraph o triples header bs supply) {b : ABlock} (bIn : b ∈ bs) {i : Nat}
    {t : rdf.Triple} (at_i : triples[i]? = some t) (inA : i ∈ b.apos) :
    ∃ x, b.afresh = [x] ∧ subjectView t.subject = .blank x := by
  obtain ⟨q, qIn, fits⟩ := at_mem ((agraph_split_at g) bIn).2 inA at_i
  obtain ⟨main', side', pIs', sides', facts', part⟩ := (agraph_shape g) bIn
  rcases part with ⟨-, empty, -⟩ | ⟨-, x, heads, sx, afreshIs, apatsIs, tanns, -⟩
  · rw [empty] at qIn; simp at qIn
  · have plain : ∀ a ∈ b.ann.val, a.annotations.val = [] := fun a m => ((g.blocks b bIn).1.plain a m).1
    have subjectX : q.subject = .blank x := by
      rw [apatsIs] at qIn
      rcases List.mem_append.mp qIn with inR | inH
      · simp only [reification, List.mem_cons, List.not_mem_nil, or_false] at inR
        rcases inR with rfl | rfl | rfl | rfl <;> rfl
      · exact (tanns_heads tanns plain q inH).1
    exact ⟨x, afreshIs, by rw [fits.1, subjectX]⟩

/-- A declaration that a triple of the graph makes is a declaration axiom of the ontology. -/
theorem agraph_declares (g : AGraph o triples header bs supply) {i : Nat} {t : rdf.Triple} (at_i : triples[i]? = some t)
    {v : alloc.vec.Vec U8} {kind : typing.EntityKind}
    (run : rdf_mapping.declared_entity t = .ok (some (v, kind))) :
    ∃ ax ∈ o.axioms.val, ax.axiom = .Declaration (entityOf kind v) := by
  obtain ⟨typed, iri, isIri, vIs, kindRun⟩ := declared_entity_some t v kind run
  rcases g.sourced i t at_i with ⟨q, member, fits⟩ | ⟨b, bIn, ib⟩
  · exfalso
    obtain ⟨_, _, _, _, which⟩ := g.headerFacts q member
    rcases which with ⟨-, object⟩ | version | imports | ⟨a, aIn, spelled⟩
    · rw [declaration_kind_ontology t.object (by rw [fits.2.2, object])] at kindRun
      cases Result.ok_injective kindRun
    · have := fits.2.1; rw [version, typed] at this; simp [rdfType, owlVersionIRI] at this
    · have := fits.2.1; rw [imports, typed] at this; simp [rdfType, owlImports] at this
    · exact allowed_ne (g.readable.vocabulary.2 _ (annotation_row_ontology aIn)) (key := rdfType)
        (by simp [mappingVocabulary]) (by rw [← spelled, ← fits.2.1, typed])
  · simp only [ABlock.pos, List.mem_append] at ib
    rcases ib with inCore | inA
    · obtain ⟨main, side, pIs, sides, facts, -⟩ := (agraph_shape g) bIn
      obtain ⟨q, qIn, fits⟩ := at_mem ((agraph_split_at g) bIn).1 inCore at_i
      rw [pIs] at qIn
      rcases List.mem_cons.mp qIn with rfl | inSide
      · obtain ⟨T, typeIn, object⟩ := declaration_kind_types t.object kind kindRun
        have subject := fits.1
        rw [isIri] at subject
        obtain ⟨e, axIs, mainIs⟩ := facts.declares (by rw [← fits.2.1]; exact typed) _ subject.symm T typeIn
          (by rw [← fits.2.2]; exact object)
        rw [mainIs] at fits
        obtain ⟨v', kind', run', same⟩ := declares_of_declaration e t fits
        rw [run] at run'
        have result := Option.some.inj (Result.ok_injective run')
        simp only [Prod.mk.injEq] at result
        obtain ⟨rfl, rfl⟩ := result
        obtain ⟨image, -, -, -⟩ := g.blocks b bIn
        exact ⟨b.ax, image.member, by rw [show b.ax.axiom = b.core.ax from rfl, axIs, same]⟩
      · exfalso
        obtain ⟨y, -, about⟩ := (sides q inSide).2
        have subject := fits.1
        rw [isIri, about] at subject
        simp [subjectView] at subject
    · exfalso
      obtain ⟨x, -, about⟩ := (agraph_apos_subject g) bIn at_i inA
      rw [isIri] at about
      simp [subjectView] at about

end

section

variable {o : model.RawOntology} {triples : alloc.vec.Vec rdf.Triple} {header : List Pattern} {bs : List ABlock}
  {supply : Supply}

/-- The kinds that the declarations of the graph give are those the ontology gives. -/
theorem agraph_graph_kinds (g : AGraph o triples.val header bs supply) (count : Usize) (positive : 0 < count.val)
    (kinds : rdf_mapping.Kinds) (at_end : KindsAt triples.val count triples.val.length kinds) :
    KindsOf kinds o.axioms.val := by
  have coreIs : (bs.map ABlock.core).map (fun b => (⟨alloc.vec.Vec.new _, b.ax⟩ : model.AnnotatedAxiom)) =
      (strip o).axioms.val := by
    rw [strip_axioms, ← g.axiomsIs, List.map_map, List.map_map]
    rfl
  have images : ∀ c ∈ bs.map ABlock.core, ImageBlock (strip o) c ∧ At triples.val c.pos c.pats := by
    intro c m
    obtain ⟨b, bIn, rfl⟩ := List.mem_map.mp m
    exact ⟨(g.blocks b bIn).1.core, ((agraph_split_at g) bIn).1⟩
  intro iri kind
  rw [has_kind_correct triples.val count positive kinds at_end iri.spelling kind]
  congr 1
  apply decide_eq_decide.mpr
  unfold Typed
  apply or_congr_left
  constructor
  · rintro ⟨i, t, at_i, v, run, vIs⟩
    obtain ⟨ax, axIn, isDecl⟩ := (agraph_declares g) at_i run
    refine ⟨ax, axIn, ?_⟩
    rw [isDecl, vec_eq_of_val vIs]
  · rintro ⟨ax, axIn, isDecl⟩
    obtain ⟨i, t, at_i, fits⟩ := graph_declaration_present coreIs images (strip_member axIn)
      (show (bare ax).axiom = _ from isDecl)
    obtain ⟨v, kind', run, same⟩ := declares_of_declaration _ t fits
    obtain ⟨rfl, rfl⟩ := entity_of_injective same
    exact ⟨i, t, at_i, _, run, rfl⟩

/-- A triple of a block about the ontology IRI is no part of the header. -/
theorem agraph_block_header_skip (g : AGraph o triples.val header bs supply) {kinds : rdf_mapping.Kinds}
    (hk : KindsOf kinds o.axioms.val) {iri : model.Iri} {version : Option model.Iri}
    (identity : o.identity = .Named iri version) {b : ABlock} (bIn : b ∈ bs) {i : Nat} {t : rdf.Triple}
    (at_i : triples.val[i]? = some t) (inB : i ∈ b.pos) (about : subjectView t.subject = .iri iri.spelling.val) :
    t.predicate.spelling.val ≠ owlVersionIRI ∧ t.predicate.spelling.val ≠ owlImports ∧
      ∃ r, rdf_mapping.property_kind kinds t.predicate.spelling = .ok r ∧ r ≠ some .Annotation := by
  simp only [ABlock.pos, List.mem_append] at inB
  rcases inB with inCore | inA
  · obtain ⟨main, side, pIs, sides, facts, -⟩ := (agraph_shape g) bIn
    obtain ⟨q, qIn, fits⟩ := at_mem ((agraph_split_at g) bIn).1 inCore at_i
    have qSubject : q.subject = iriNode iri := by rw [← fits.1, about]; rfl
    rw [pIs] at qIn
    rcases List.mem_cons.mp qIn with rfl | inSide
    · obtain ⟨notVersion, notImports, notAnnotation⟩ := facts.header iri version identity qSubject
      rw [fits.2.1]
      exact ⟨notVersion, notImports,
        property_kind_other (strip_kinds hk) (iri := ⟨t.predicate.spelling⟩) (notAnnotation _ fits.2.1)⟩
    · exfalso
      obtain ⟨y, -, subject⟩ := (sides q inSide).2
      rw [qSubject] at subject
      simp [iriNode] at subject
  · exfalso
    obtain ⟨x, -, about'⟩ := (agraph_apos_subject g) bIn at_i inA
    rw [about] at about'
    cases about'

/-- No triple of a block types an IRI `owl:Ontology`. -/
theorem agraph_block_not_ontology (g : AGraph o triples.val header bs supply) {b : ABlock} (bIn : b ∈ bs) {i : Nat}
    {t : rdf.Triple} (at_i : triples.val[i]? = some t) (inB : i ∈ b.pos) (typed : t.predicate.spelling.val = rdfType)
    (onto : objectView t.object = .iri owlOntology) (iri : rdf.RdfIri) : t.subject ≠ .Iri iri := by
  intro isIri
  simp only [ABlock.pos, List.mem_append] at inB
  rcases inB with inCore | inA
  · obtain ⟨main, side, pIs, sides, facts, -⟩ := (agraph_shape g) bIn
    obtain ⟨q, qIn, fits⟩ := at_mem ((agraph_split_at g) bIn).1 inCore at_i
    rw [pIs] at qIn
    rcases List.mem_cons.mp qIn with rfl | inSide
    · have subject := fits.1
      rw [isIri] at subject
      exact facts.notOntology (by rw [← fits.2.1]; exact typed) _ subject.symm (by rw [← fits.2.2]; exact onto)
    · obtain ⟨y, -, about⟩ := (sides q inSide).2
      have subject := fits.1
      rw [isIri, about] at subject
      simp [subjectView] at subject
  · obtain ⟨x, -, about⟩ := (agraph_apos_subject g) bIn at_i inA
    rw [isIri] at about
    simp [subjectView] at about

theorem agraph_fresh_le_pats (g : AGraph o triples.val header bs supply) {b : ABlock} (bIn : b ∈ bs) :
    b.fresh.length ≤ b.pats.length := by
  obtain ⟨image, -, -, -⟩ := g.blocks b bIn
  obtain ⟨s1, tax⟩ := image.core.forward
  have count := taxiom_count tax
  simp only [List.length_append] at count
  obtain ⟨main, side, pIs, -, -, part⟩ := (agraph_shape g) bIn
  simp only [ABlock.fresh, ABlock.pats, List.length_append]
  rcases part with ⟨-, apatsNil, afreshNil⟩ | ⟨-, x, heads, sx, afreshIs, apatsIs, -, -⟩
  · rw [apatsNil, afreshNil]; simp; omega
  · rw [afreshIs, apatsIs]; simp [reification]; omega

theorem agraph_flat_fresh_le (g : AGraph o triples.val header bs supply) :
    ∀ cs : List ABlock, (∀ c ∈ cs, c ∈ bs) →
      (cs.flatMap ABlock.fresh).length ≤ (cs.flatMap ABlock.pats).length := by
  intro cs
  induction cs with
  | nil => intro _; simp
  | cons c cs ih =>
    intro members
    have h1 := (agraph_fresh_le_pats g) (members c (by simp))
    have h2 := ih (fun d m => members d (List.mem_cons_of_mem _ m))
    simp only [List.flatMap_cons, List.length_append]
    omega

end

/-! ### The mapping of a graph of an annotated ontology -/

/-- **The reverse RDF mapping reads back every readable annotated ontology.**
    For an ontology with ontology annotations and annotated axioms that the
    reverse mapping reads back (`ReadableAnnotated`), a graph that lists, in
    order, the triples of its forward mapping (`TOntology`) with blank nodes
    distinct from each other and from the anonymous individuals the assertions
    are about (`FreshSupply`) is mapped to exactly that ontology, its version
    IRI, imports, annotations and the annotations of its axioms included, with
    exactly those blank nodes. -/
theorem map_graph_complete_annotated (graph : rdf.RawGraph) (o : model.RawOntology) (supply : Supply)
    (patterns : List Pattern) (readable : ReadableAnnotated o) (forward : TOntology o supply patterns)
    (distinct : supply.Nodup) (fresh : FreshSupply o supply)
    (image : List.Forall₂ Matches patterns graph.triples.val) :
    ∃ m, rdf_mapping.map_graph graph = .ok (some m) ∧ m.ontology = o ∧ m.blanks.val = supply := by
  obtain ⟨header, axiomPs, rest, theader, taxioms, split⟩ := forward
  obtain ⟨heads, headerIs, restIs, anonymousFacts, namedFacts⟩ := header_annotated readable.annotations theader
  rw [restIs] at taxioms
  subst headerIs
  have lengthEq : graph.triples.val.length = patterns.length := (List.Forall₂.length_eq image).symm
  have holdsAll : At graph.triples.val (List.range' 0 patterns.length) patterns :=
    forall2_at patterns graph.triples.val 0 (by simpa using image)
  rw [split, List.length_append, ← List.range'_append_1] at holdsAll
  obtain ⟨holdsH, holdsA⟩ := at_append_inv holdsAll (by simp)
  simp only [Nat.zero_add] at holdsA
  obtain ⟨bs, mapIs, freshIs, patsIs, sorted, disjoint, each, covers⟩ :=
    annotated_blocks readable graph.triples taxioms (fun ax m => m) (headerPatterns o ++ heads).length holdsA
  simp only [List.append_nil] at freshIs
  have hLen : (headerPatterns o ++ heads).length + axiomPs.length = graph.triples.val.length := by
    rw [lengthEq, split]; simp only [List.length_append]
  have hLen2 : (headerPatterns o).length + heads.length + axiomPs.length = graph.triples.val.length := by
    rw [← hLen]; simp
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
      blocks := fun b m => ⟨(each b m).1, (each b m).2.1, by rw [(each b m).2.2.1]; exact List.nodup_range',
        by rw [(each b m).2.2.2.2.1, List.length_range']⟩
      axiomsIs := mapIs
      sourced := by
        intro i t at_i
        have inside : i < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
        by_cases inHeader : i < (headerPatterns o ++ heads).length
        · exact Or.inl (at_mem holdsH (by simp only [List.mem_range'_1]; omega) at_i)
        · obtain ⟨c, cIn, ic⟩ := covers i (by omega) (by omega)
          exact Or.inr ⟨c, cIn, ic⟩
      supplyIs := freshIs
      distinct := distinct
      fresh := fresh
      disjoint := disjoint }
  have supplyCount : supply.length ≤ axiomPs.length := by
    rw [freshIs, patsIs]
    exact (agraph_flat_fresh_le g) bs (fun c m => m)
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
  -- the axiom loop from a state where exactly the header is used
  have loop : ∀ st : rdf_mapping.State,
      SubjectsComplete graph.triples.val st.subjects.val (alloc.vec.Vec.len st.subjects) graph.triples.val.length →
      BucketsSorted st.subjects.val →
      SourcesComplete graph.triples.val st.sources.val (alloc.vec.Vec.len st.sources) graph.triples.val.length →
      st.used.val.length = graph.triples.val.length →
      (∀ (i : Nat), i < graph.triples.val.length →
        (st.used.val[i]? = some false ↔ (headerPatterns o ++ heads).length ≤ i)) →
      st.blanks.val = [] →
      ∃ v s', rdf_mapping.axioms_from graph.triples kinds 0#usize st (alloc.vec.Vec.new _) = .ok (some (v, s')) ∧
        v.val = o.axioms.val ∧ s'.blanks.val = supply ∧
        ∀ (i : Nat), i < graph.triples.val.length → s'.used.val[i]? = some true := by
    intro st completeSt sortedSt sourcesSt lengthSt usedSt blanksSt
    have inRange : ∀ b ∈ bs, ∀ i ∈ b.pos, b.core.main ≤ i ∧ i < graph.triples.val.length := by
      intro b m i inB
      obtain ⟨-, -, posIs, -, -, low, high⟩ := each b m
      rw [posIs, List.mem_range'_1] at inB
      omega
    have state : ALoop graph.triples st bs :=
      { complete := completeSt
        sorted := sortedSt
        sources := sourcesSt
        length := lengthSt
        free := fun b m i inB => by
          have := inRange b m i inB
          have low := (each b m).2.2.2.2.2.1
          exact (usedSt i this.2).mpr (by omega)
        covered := fun i unused => by
          have inside : i < graph.triples.val.length := by
            rw [← lengthSt]; exact (List.getElem?_eq_some_iff.mp unused).1
          exact covers i ((usedSt i inside).mp unused) (by omega)
        room := by
          rw [blanksSt, ← freshIs]
          simp
          omega }
    have axiomsCount : bs.length ≤ Usize.max := by
      have := o.axioms.property
      have lengths : bs.length = o.axioms.val.length := by rw [← mapIs, List.length_map]
      omega
    obtain ⟨v, s', run, vIs, blanksIs, allUsed⟩ := annotated_loop graph.triples kinds bs
      (fun s b rest members state a aIs => by
        obtain ⟨s1, s', v, readRun, annotateRun, -, exact, marked⟩ :=
          (agraph_step g) hk s b rest members state a aIs
        have ordered : b.Ordered := by
          unfold ABlock.Ordered
          rw [(each b (members b (by simp))).2.2.2.2.1]
          exact List.Pairwise.sublist (List.drop_sublist _ _) List.pairwise_lt_range'
        rw [exact ordered] at annotateRun
        exact ⟨s1, s', readRun, annotateRun, marked⟩) _ 0#usize bs st
      (alloc.vec.Vec.new _) rfl (fun b m => m) sorted disjoint (fun b m => by simp) inRange state (by simp; omega)
    refine ⟨v, s', run, by rw [vIs, ← mapIs]; simp, by rw [blanksIs, blanksSt, freshIs]; simp, allUsed⟩
  -- the header
  cases identity : o.identity with
  | Anonymous =>
    obtain ⟨headsNil, importsNil, annotationsNil⟩ := anonymousFacts identity
    subst headsNil
    have headerNil : headerPatterns o = [] := by simp [headerPatterns, identity]
    have headerRun : rdf_mapping.find_header graph.triples v1 0#usize = .ok none := by
      apply find_header_none
      intro i t _ at_i typed onto iri isIri
      have inside : i < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
      obtain ⟨b, bIn, ib⟩ := covers i (by simp [headerNil]) (by simp [headerNil] at hLen ⊢; omega)
      exact (agraph_block_not_ontology g) bIn at_i ib typed onto iri isIri
    obtain ⟨v, s', axiomsRun, vIs, blanksIs, allUsed⟩ := loop
      { used := v1, blanks := alloc.vec.Vec.new _, subjects := v3, sources := v4 } complete sortedV3
      sourcesComplete (by simp [v1Is])
      (fun i hi => by simp [v1Is, List.getElem?_replicate, hi, headerNil])
      (by simp)
    have allRun := all_read_used graph.triples s'.used 0#usize (fun i _ hi => allUsed i hi)
    refine ⟨⟨⟨.Anonymous, alloc.vec.Vec.new _, alloc.vec.Vec.new _, v⟩, s'.blanks⟩, ?_, ?_, blanksIs⟩
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
    · obtain ⟨identity', imports, annotations, axioms⟩ := o
      simp only at identity importsNil annotationsNil vIs ⊢
      subst identity
      simp only [model.RawOntology.mk.injEq, true_and]
      refine ⟨vec_eq_of_val (by simp [importsNil]), vec_eq_of_val (by simp [annotationsNil]),
        vec_eq_of_val (by simpa using vIs)⟩
  | Named iri version =>
    have tannsH := namedFacts iri version identity
    have hpLen : (headerPatterns o).length = 1 + (match version with | some _ => 1 | none => 0) + o.imports.val.length := by
      cases version <;> simp [headerPatterns, identity] <;> omega
    rw [List.length_append, ← List.range'_append_1] at holdsH
    obtain ⟨holdsHP, holdsHeads⟩ := at_append_inv holdsH (by simp)
    simp only [Nat.zero_add] at holdsHeads
    -- the triple typing the ontology IRI, first
    have typingAt := at_nth holdsHP 0 (by simp [headerPatterns, identity])
    obtain ⟨t0, at0, fits0⟩ := typingAt
    have fits0' : Matches ⟨iriNode iri, rdfType, .iri owlOntology⟩ t0 := by
      simpa [headerPatterns, identity] using fits0
    obtain ⟨iri0, isIri0, spelled0⟩ : ∃ iri0, t0.subject = .Iri iri0 ∧ iri0.spelling = iri.spelling := by
      have subject := fits0'.1
      cases h : t0.subject with
      | Iri iri0 =>
        rw [h] at subject
        simp only [iriNode, subjectView, Node.iri.injEq] at subject
        exact ⟨iri0, rfl, vec_eq_of_val subject⟩
      | Blank _ => rw [h] at subject; simp [iriNode, subjectView] at subject
    have lengthPos : 0 < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at0).1
    have z : (0#usize : Usize).val = 0 := by simp
    have unused0 : v1.val[0]? = some false := by simp [v1Is, List.getElem?_replicate, lengthPos]
    have headerRun : rdf_mapping.find_header graph.triples v1 0#usize = .ok (some 0#usize) :=
      find_header_at graph.triples v1 0#usize t0 (by rw [z]; simpa using at0) (by rw [z]; exact unused0)
        fits0'.2.1 fits0'.2.2 iri0 isIri0
    let st0 : rdf_mapping.State := { used := v1, blanks := alloc.vec.Vec.new _, subjects := v3, sources := v4 }
    let st1 : rdf_mapping.State := { st0 with used := st0.used.set 0#usize true }
    have m01 : Marked st0 st1 (fun i => i < 1) [] := marked_same (marked_take st0 0#usize) (fun i => by simp)
    have aboutIs : ∀ t : rdf.Triple, subjectView t.subject = iriNode iri →
        subjectView t.subject = .iri iri0.spelling.val := by
      intro t h; rw [h, spelled0]; rfl
    -- every triple about the ontology IRI after the header is no part of it
    have skip : ∀ (used : List Bool), HeaderSkip graph.triples kinds iri0.spelling used
        (headerPatterns o ++ heads).length := by
      intro used i t low at_i _ about
      have inside : i < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
      obtain ⟨b, bIn, ib⟩ := covers i low (by omega)
      exact (agraph_block_header_skip g) hk identity bIn at_i ib (by rw [about, spelled0])
    have noAnn := (agraph_no_annotation_kind g)
    -- the annotations, then nothing more of the header
    have annotationsPhase : ∀ (index : Usize) (s : rdf_mapping.State) (ver : Option model.Iri)
        (imp : alloc.vec.Vec model.Iri), index.val = (headerPatterns o).length →
        Marked st0 s (fun i => i < index.val) [] →
        ∃ v s', rdf_mapping.header_parts graph.triples kinds iri0.spelling index s ver imp (alloc.vec.Vec.new _) =
          .ok (some (ver, imp, v, s')) ∧ v.val = o.annotations.val ∧
          Marked st0 s' (fun i => i < (headerPatterns o ++ heads).length) [] := by
      intro index s ver imp indexIs marked
      have tannsH' : TAnns (.iri iri0.spelling.val) o.annotations.val supply heads supply := by
        have : (iriNode iri) = .iri iri0.spelling.val := by rw [spelled0]; rfl
        rw [← this]; exact tannsH
      obtain ⟨v, s', run, vIs, marked'⟩ := header_parts_annotations graph.triples kinds iri0.spelling ver imp noAnn
        o.annotations.val tannsH' readable.annotations
        (fun a m => (annotation_property_facts readable hk (annotation_row_ontology m)).1)
        (fun a m => ⟨(annotation_property_facts readable hk (annotation_row_ontology m)).2 _
            (by simp [mappingVocabulary]),
          (annotation_property_facts readable hk (annotation_row_ontology m)).2 _ (by simp [mappingVocabulary])⟩)
        index s (alloc.vec.Vec.new _) (by rw [indexIs]; exact holdsHeads)
        (by
          intro i low high
          apply marked_unused marked (by simp [st0, v1Is, List.getElem?_replicate]; omega)
          omega)
        (by rw [indexIs, ← List.length_append]; exact skip s.used.val)
        (by simp)
      refine ⟨v, s', run, by simpa using vIs, marked_same (marked_trans marked marked') (fun i => ?_)⟩
      simp only [List.length_append]
      omega
    -- the imports, then the annotations
    have importsPhase : ∀ (index : Usize) (s : rdf_mapping.State) (ver : Option model.Iri),
        index.val + o.imports.val.length = (headerPatterns o).length →
        (∀ (k : Nat) (hk : k < o.imports.val.length), ∃ t, graph.triples.val[index.val + k]? = some t ∧
          Matches ⟨iriNode iri, owlImports, iriNode o.imports.val[k]⟩ t) →
        Marked st0 s (fun i => i < index.val) [] →
        ∃ v imp s', rdf_mapping.header_parts graph.triples kinds iri0.spelling index s ver (alloc.vec.Vec.new _)
          (alloc.vec.Vec.new _) = .ok (some (ver, imp, v, s')) ∧ imp.val = o.imports.val ∧
          v.val = o.annotations.val ∧ Marked st0 s' (fun i => i < (headerPatterns o ++ heads).length) [] := by
      intro index s ver ends importsAt marked
      obtain ⟨next, s1, imp, nextIs, impIs, marked1, run1⟩ := header_parts_imports_then graph.triples kinds
        iri0.spelling ver (alloc.vec.Vec.new _) o.imports.val index s (alloc.vec.Vec.new _)
        (by
          intro k hk
          obtain ⟨t, at_t, fits⟩ := importsAt k hk
          refine ⟨t, at_t, aboutIs t fits.1, fits.2.1, fits.2.2, ?_⟩
          apply marked_unused marked (by simp [st0, v1Is, List.getElem?_replicate]; omega)
          simp)
        (by simp)
      obtain ⟨v, s', run2, vIs, marked2⟩ := annotationsPhase next s1 ver imp (by rw [nextIs]; exact ends)
        (marked_same (marked_trans marked marked1) (fun i => by rw [nextIs]; omega))
      refine ⟨v, imp, s', by rw [run1, run2], by simpa using impIs, vIs, marked2⟩
    -- the header read
    obtain ⟨ver, imp, va, sH, partsRun, impIs, vaIs, mH, verIs⟩ : ∃ (ver : Option model.Iri)
        (imp : alloc.vec.Vec model.Iri) (va : alloc.vec.Vec model.Annotation) (sH : rdf_mapping.State),
        rdf_mapping.header_parts graph.triples kinds iri0.spelling 0#usize st1 none (alloc.vec.Vec.new _)
          (alloc.vec.Vec.new _) = .ok (some (ver, imp, va, sH)) ∧
        imp.val = o.imports.val ∧ va.val = o.annotations.val ∧
        Marked st0 sH (fun i => i < (headerPatterns o ++ heads).length) [] ∧ ver = version := by
      have one : (0#usize + 1#usize : Result Usize) = .ok 1#usize := by
        obtain ⟨n, run, value⟩ := WP.spec_imp_exists (Usize.add_spec (x := 0#usize) (y := 1#usize) (by scalar_tac))
        have same : n = 1#usize := UScalar.eq_of_val_eq (by simp at value ⊢; exact value)
        rw [run, same]
      have used0 : st1.used.val[(0#usize : Usize).val]? = some true := by
        simp [st1, st0, alloc.vec.Vec.set_val_eq, v1Is, List.getElem?_set_self, lengthPos]
      rw [header_parts_used graph.triples kinds iri0.spelling none _ _ 0#usize 1#usize st1 (by rw [z]; exact lengthPos)
        used0 one]
      cases versionIs : version with
      | none =>
        have hdr : headerPatterns o = ⟨iriNode iri, rdfType, .iri owlOntology⟩ ::
            o.imports.val.map (fun i => ⟨iriNode iri, owlImports, iriNode i⟩) := by
          simp [headerPatterns, identity, versionIs]
        obtain ⟨v, imp, s', run, impIs, vIs, marked⟩ := importsPhase 1#usize st1 none (by rw [hdr]; simp; omega)
          (by
            intro k hk
            obtain ⟨t, at_t, fits⟩ := at_nth holdsHP (k + 1) (by rw [hdr]; simp; omega)
            simp only [hdr, List.getElem_cons_succ, List.getElem_map] at fits
            exact ⟨t, by simpa [Nat.add_comm] using at_t, fits⟩)
          m01
        exact ⟨none, imp, v, s', run, impIs, vIs, marked, rfl⟩
      | some vIri =>
        have hdr : headerPatterns o = ⟨iriNode iri, rdfType, .iri owlOntology⟩ ::
            ⟨iriNode iri, owlVersionIRI, iriNode vIri⟩ ::
            o.imports.val.map (fun i => ⟨iriNode iri, owlImports, iriNode i⟩) := by
          simp [headerPatterns, identity, versionIs]
        obtain ⟨t1, at1, fits1⟩ := at_nth holdsHP 1 (by rw [hdr]; simp)
        simp only [hdr, List.getElem_cons_succ, List.getElem_cons_zero] at fits1
        have one' : (1#usize : Usize).val = 1 := by simp
        have two : (1#usize + 1#usize : Result Usize) = .ok 2#usize := by
          obtain ⟨n, run, value⟩ := WP.spec_imp_exists (Usize.add_spec (x := 1#usize) (y := 1#usize) (by scalar_tac))
          have same : n = 2#usize := UScalar.eq_of_val_eq (by simp at value ⊢; exact value)
          rw [run, same]
        have unused1 : st1.used.val[(1#usize : Usize).val]? = some false := by
          rw [one']
          apply marked_unused m01 (by simp [st0, v1Is, List.getElem?_replicate]; rw [hdr] at hLen; simp at hLen; omega)
          simp
        rw [header_parts_version graph.triples kinds iri0.spelling _ _ 1#usize 2#usize st1 t1
          (by rw [one']; simpa using at1) unused1 (by rw [fits1.1, spelled0]; rfl) fits1.2.1 vIri fits1.2.2 two]
        have m12 : Marked st0 { st1 with used := st1.used.set 1#usize true } (fun i => i < 2) [] :=
          marked_same (marked_trans m01 (marked_take st1 1#usize)) (fun i => by simp; omega)
        obtain ⟨v, imp, s', run, impIs, vIs, marked⟩ := importsPhase 2#usize _ (some vIri) (by rw [hdr]; simp; omega)
          (by
            intro k hk
            obtain ⟨t, at_t, fits⟩ := at_nth holdsHP (k + 2) (by rw [hdr]; simp; omega)
            simp only [hdr, List.getElem_cons_succ, List.getElem_map] at fits
            exact ⟨t, by simpa [Nat.add_comm] using at_t, fits⟩)
          m12
        exact ⟨some vIri, imp, v, s', run, impIs, vIs, marked, rfl⟩
    -- the axioms
    obtain ⟨v, s', axiomsRun, vIs, blanksIs, allUsed⟩ := loop sH (by rw [mH.subjects]; exact complete)
      (by rw [mH.subjects]; exact sortedV3) (by rw [mH.sources]; exact sourcesComplete)
      (by rw [mH.length]; simp [st0, v1Is])
      (by
        intro i hi
        have inside : i < st0.used.val.length := by simp [st0, v1Is]; exact hi
        have before : st0.used.val[i]? = some false := by simp [st0, v1Is, List.getElem?_replicate, hi]
        constructor
        · intro unused
          apply Classical.byContradiction
          intro low
          rw [marked_used mH inside (by omega)] at unused
          cases unused
        · intro low
          exact marked_unused mH before (by omega))
      (by rw [mH.blanks]; simp [st0])
    have allRun := all_read_used graph.triples s'.used 0#usize (fun i _ hi => allUsed i hi)
    refine ⟨⟨⟨.Named ⟨iri0.spelling⟩ ver, imp, va, v⟩, s'.blanks⟩, ?_, ?_, blanksIs⟩
    · rw [rdf_mapping.map_graph]
      simp only [countRun, bind_ok, kindBucketsRun, kindsRun, unusedRun, bucketsRun, subjectsRun, sourcesRun,
        headerRun, alloc.vec.Vec.index_slice_index, main_lookup graph.triples 0#usize t0 (by rw [z]; simpa using at0),
        isIri0, take_correct]
      have partsRun' : rdf_mapping.header_parts graph.triples kinds iri0.spelling 0#usize
          { used := v1.set 0#usize true, blanks := alloc.vec.Vec.new rdf.BlankNode, subjects := v3, sources := v4 }
          none (alloc.vec.Vec.new model.Iri) (alloc.vec.Vec.new model.Annotation) =
          .ok (some (ver, imp, va, sH)) := partsRun
      rw [partsRun']
      simp only [bind_ok]
      change (Std.bind (rdf_mapping.iri_of iri0.spelling) _) = _
      rw [iri_of_identity, bind_ok]
      simp only [axiomsRun, bind_ok]
      change (Std.bind (rdf_mapping.all_read graph.triples s'.used 0#usize) _) = _
      rw [allRun, bind_ok]
      rfl
    · obtain ⟨identity', imports, annotations, axioms⟩ := o
      simp only at identity impIs vaIs vIs ⊢
      subst identity verIs
      simp only [model.RawOntology.mk.injEq, model.OntologyIdentity.Named.injEq, and_true]
      refine ⟨iri_ext (by rw [spelled0]), vec_eq_of_val impIs, vec_eq_of_val vaIs, vec_eq_of_val vIs⟩

end Rowl.RdfReadAnnotated
