import Rowl.RdfReadExpressions
import Rowl.Vocabulary

/-!
# Completeness of the axiom readers of the RDF mapping

For every axiom that the reverse mapping reads back (`AxiomReadable`), with the
kinds of its IRIs given by the declarations of its ontology (`KindsOf`) and its
IRIs allowed by the reserved-vocabulary condition of OWL 2 DL, `read_axiom`
reads the axiom from the first triple of its forward image, uses exactly the
positions of that image and records exactly its blank nodes, in order, and
`annotate` adds no annotations (`axiom_reads`).
-/

namespace Rowl.RdfReadAxioms
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust Rowl.RdfMapping Rowl.RdfReadIndexes Rowl.RdfReadExpressions

/-! ### The vocabulary of the mapping and the built-in entities -/

instance reservedDecidable (key : List U8) : Decidable (Rowl.Vocabulary.Reserved key) := by
  unfold Rowl.Vocabulary.Reserved; infer_instance

def owlThing : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 84#u8, 104#u8, 105#u8, 110#u8, 103#u8]

def owlNothing : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 78#u8, 111#u8, 116#u8, 104#u8, 105#u8, 110#u8, 103#u8]

/-- The IRIs that the mapping writes as predicates and types of its own. -/
def mappingVocabulary : List (List U8) :=
  [rdfType, rdfFirst, rdfRest, rdfNil, rdfsSubClassOf, rdfsSubPropertyOf, rdfsDomain, rdfsRange, rdfsDatatype,
    owlClass, owlRestriction, owlOntology, owlVersionIRI, owlImports, owlObjectProperty, owlDatatypeProperty,
    owlAnnotationProperty, owlNamedIndividual, owlEquivalentClass, owlDisjointWith, owlDisjointUnionOf,
    owlPropertyChainAxiom, owlEquivalentProperty, owlPropertyDisjointWith, owlInverseOf, owlSameAs,
    owlDifferentFrom, owlHasKey, owlMembers, owlAllDisjointClasses, owlAllDisjointProperties, owlAllDifferent,
    owlNegativePropertyAssertion, owlSourceIndividual, owlAssertionProperty, owlTargetIndividual, owlTargetValue,
    owlFunctionalProperty, owlInverseFunctionalProperty, owlReflexiveProperty, owlIrreflexiveProperty,
    owlSymmetricProperty, owlAsymmetricProperty, owlTransitiveProperty, owlIntersectionOf, owlUnionOf,
    owlComplementOf, owlOneOf, owlOnProperty, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlHasSelf,
    owlMinCardinality, owlMaxCardinality, owlCardinality, owlMinQualifiedCardinality, owlMaxQualifiedCardinality,
    owlQualifiedCardinality, owlOnClass, owlOnDataRange, owlDatatypeComplementOf, owlOnDatatype,
    owlWithRestrictions, owlAxiom, owlAnnotation, owlAnnotatedSource, owlAnnotatedProperty, owlAnnotatedTarget]

set_option maxRecDepth 16384 in
/-- The vocabulary of the mapping is reserved and names no built-in entity. -/
theorem mapping_vocabulary_reserved :
    ∀ key ∈ mappingVocabulary, Rowl.Vocabulary.Reserved key ∧ Rowl.Builtins.role key = none := by
  decide

set_option maxRecDepth 16384 in
/-- Every built-in entity is reserved vocabulary. -/
theorem builtins_reserved : ∀ e ∈ Rowl.Builtins.entities, Rowl.Vocabulary.Reserved e.1 := by
  decide

def isClassKind : typing.EntityKind → Bool
  | .Class => true
  | _ => false

set_option maxRecDepth 16384 in
theorem builtin_classes :
    ∀ e ∈ Rowl.Builtins.entities, isClassKind e.2 = true → e.1 = owlThing ∨ e.1 = owlNothing := by
  decide

theorem role_mem (key : List U8) (kind : typing.EntityKind) (h : Rowl.Builtins.role key = some kind) :
    (key, kind) ∈ Rowl.Builtins.entities := by
  have h' : (Rowl.Builtins.entities.find? (fun entry => decide (key = entry.1))).map Prod.snd = some kind := h
  rcases e : Rowl.Builtins.entities.find? (fun entry => decide (key = entry.1)) with _ | entry
  · rw [e] at h'; cases h'
  · rw [e] at h'
    simp only [Option.map_some, Option.some.injEq] at h'
    have mem := List.mem_of_find?_eq_some e
    have keyIs := List.find?_some e
    simp only [decide_eq_true_eq] at keyIs
    subst h'
    rw [keyIs]
    exact mem

theorem role_reserved {key : List U8} {kind : typing.EntityKind} (h : Rowl.Builtins.role key = some kind) :
    Rowl.Vocabulary.Reserved key :=
  builtins_reserved _ (role_mem key kind h)

theorem role_class {key : List U8} (h : Rowl.Builtins.role key = some .Class) : key = owlThing ∨ key = owlNothing :=
  builtin_classes _ (role_mem key .Class h) rfl

/-- An allowed IRI is none of the vocabulary of the mapping. -/
theorem allowed_ne {iri : model.Iri} {kind : typing.EntityKind} (allowed : Rowl.Vocabulary.EntityAllowed iri kind)
    {key : List U8} (member : key ∈ mappingVocabulary) : iri.spelling.val ≠ key := by
  obtain ⟨reserved, notBuiltin⟩ := mapping_vocabulary_reserved key member
  intro same
  rcases allowed with free | builtin
  · exact free (same ▸ reserved)
  · rw [same, notBuiltin] at builtin
    cases builtin

attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-! ### The kinds of the IRIs of an ontology -/

/-- The kinds an ontology gives an IRI: those it declares it with, and its
    built-in kind. -/
def Typed (axioms : List model.AnnotatedAxiom) (iri : model.Iri) (kind : typing.EntityKind) : Prop :=
  (∃ ax ∈ axioms, ax.axiom = .Declaration (entityOf kind iri.spelling)) ∨
    Rowl.Builtins.role iri.spelling.val = some kind

/-- How an ontology must type an IRI that it uses with a kind for the reverse
    mapping to recognize the use: a property used as one kind of property is
    typed as that kind and as no other kind of property, and a class is not typed
    as a datatype (the typing constraints of OWL 2 DL). -/
def KindTyped (axioms : List model.AnnotatedAxiom) (iri : model.Iri) : typing.EntityKind → Prop
  | .ObjectProperty => Typed axioms iri .ObjectProperty ∧ ¬ Typed axioms iri .DataProperty ∧
      ¬ Typed axioms iri .AnnotationProperty
  | .DataProperty => Typed axioms iri .DataProperty ∧ ¬ Typed axioms iri .ObjectProperty ∧
      ¬ Typed axioms iri .AnnotationProperty
  | .AnnotationProperty => Typed axioms iri .AnnotationProperty ∧ ¬ Typed axioms iri .ObjectProperty ∧
      ¬ Typed axioms iri .DataProperty
  | .Class => ¬ Typed axioms iri .Datatype
  | .Datatype => True
  | .NamedIndividual => True

/-- The kinds that the reader computes are those the ontology gives. -/
def KindsOf (kinds : rdf_mapping.Kinds) (axioms : List model.AnnotatedAxiom) : Prop :=
  ∀ (iri : model.Iri) (kind : typing.EntityKind),
    rdf_mapping.has_kind kinds iri.spelling kind = .ok (decide (Typed axioms iri kind))

theorem has_kind_of {kinds : rdf_mapping.Kinds} {axioms : List model.AnnotatedAxiom} (hk : KindsOf kinds axioms)
    (v : alloc.vec.Vec U8) (kind : typing.EntityKind) :
    rdf_mapping.has_kind kinds v kind = .ok (decide (Typed axioms ⟨v⟩ kind)) :=
  hk ⟨v⟩ kind

theorem property_kind_object {kinds : rdf_mapping.Kinds} {axioms : List model.AnnotatedAxiom}
    (hk : KindsOf kinds axioms) {iri : model.Iri} (typed : KindTyped axioms iri .ObjectProperty) :
    rdf_mapping.property_kind kinds iri.spelling = .ok (some .Object) := by
  obtain ⟨o, d, a⟩ := typed
  rw [rdf_mapping.property_kind]
  simp only [hk iri .ObjectProperty, hk iri .DataProperty, hk iri .AnnotationProperty, bind_ok]
  simp [o, d, a]

theorem property_kind_data {kinds : rdf_mapping.Kinds} {axioms : List model.AnnotatedAxiom}
    (hk : KindsOf kinds axioms) {iri : model.Iri} (typed : KindTyped axioms iri .DataProperty) :
    rdf_mapping.property_kind kinds iri.spelling = .ok (some .Data) := by
  obtain ⟨d, o, a⟩ := typed
  rw [rdf_mapping.property_kind]
  simp only [hk iri .ObjectProperty, hk iri .DataProperty, hk iri .AnnotationProperty, bind_ok]
  simp [o, d, a]

theorem property_kind_annotation {kinds : rdf_mapping.Kinds} {axioms : List model.AnnotatedAxiom}
    (hk : KindsOf kinds axioms) {iri : model.Iri} (typed : KindTyped axioms iri .AnnotationProperty) :
    rdf_mapping.property_kind kinds iri.spelling = .ok (some .Annotation) := by
  obtain ⟨a, o, d⟩ := typed
  rw [rdf_mapping.property_kind]
  simp only [hk iri .ObjectProperty, hk iri .DataProperty, hk iri .AnnotationProperty, bind_ok]
  simp [o, d, a]

/-- The uses of an expression typed by the ontology are classified by the reader. -/
theorem uses_typed_of {kinds : rdf_mapping.Kinds} {axioms : List model.AnnotatedAxiom} (hk : KindsOf kinds axioms)
    {rows : List (model.Iri × typing.EntityKind)} (typed : ∀ row ∈ rows, KindTyped axioms row.1 row.2) :
    UsesTyped kinds rows := by
  intro row member
  refine ⟨fun isObject => ?_, fun isData => ?_⟩
  · have h := typed row member
    rw [isObject] at h
    exact property_kind_object hk h
  · have h := typed row member
    rw [isData] at h
    exact property_kind_data hk h

/-! ### Reading the parts of a block -/

theorem marked_used {s s' : rdf_mapping.State} {m : Nat → Prop} {f : List rdf.BlankNode} (h : Marked s s' m f)
    {i : Nat} (inside : i < s.used.val.length) (hm : m i) : s'.used.val[i]? = some true :=
  (h.used i inside).mpr (Or.inr hm)

/-- The rest of the patterns is ready once the first part is read completely. -/
theorem ready_rest {triples : alloc.vec.Vec rdf.Triple} {s s' : rdf_mapping.State} {pos1 pos2 : List Nat}
    {ps1 ps2 : List Pattern} {f1 f2 : List rdf.BlankNode} {m : Nat → Prop} {g : List rdf.BlankNode}
    (ready : Ready triples s (pos1 ++ pos2) (ps1 ++ ps2) (f1 ++ f2)) (len1 : pos1.length = ps1.length)
    (marked : Marked s s' m g) (inside : ∀ i, m i → i ∈ pos1) (all : ∀ i ∈ pos1, m i)
    (recorded : g.length ≤ f1.length) : Ready triples s' pos2 ps2 f2 := by
  obtain ⟨at1, at2⟩ := at_append_inv ready.holds len1
  have nodupPos := ready.nodup
  rw [List.nodup_append] at nodupPos
  refine { complete := by rw [marked.subjects]; exact ready.complete
           holds := at2
           nodup := nodupPos.2.1
           free := ?_
           owns := ?_
           room := ?_ }
  · intro i member
    have before := ready.free i (by simp [member])
    exact marked_unused marked before (fun hm => nodupPos.2.2 i (inside i hm) i member rfl)
  · intro i t y at_i unused about member
    have before := marked_back marked unused
    have inAll := ready.owns i t y at_i before about (by simp [member])
    rcases List.mem_append.mp inAll with in1 | in2
    · exfalso
      have inside' : i < s.used.val.length := (List.getElem?_eq_some_iff.mp before).1
      rw [marked_used marked inside' (all i in1)] at unused
      cases unused
    · exact in2
  · have room := ready.room
    rw [marked.blanks]
    simp only [List.length_append] at room ⊢
    omega

/-- Readiness does not depend on the order of the blank nodes. -/
theorem ready_perm {triples : alloc.vec.Vec rdf.Triple} {s : rdf_mapping.State} {pos : List Nat}
    {ps : List Pattern} {f f' : List rdf.BlankNode} (ready : Ready triples s pos ps f) (perm : f.Perm f') :
    Ready triples s pos ps f' where
  complete := ready.complete
  holds := ready.holds
  nodup := ready.nodup
  free := ready.free
  owns := fun i t y at_i unused about member => ready.owns i t y at_i unused about (perm.mem_iff.mpr member)
  room := by have := ready.room; rw [← perm.length_eq]; exact this

/-- Readiness does not depend on the order of the parts of the patterns. -/
theorem ready_swap {triples : alloc.vec.Vec rdf.Triple} {s : rdf_mapping.State} {pos1 pos2 pos3 : List Nat}
    {ps1 ps2 ps3 : List Pattern} {f : List rdf.BlankNode}
    (ready : Ready triples s (pos1 ++ pos2 ++ pos3) (ps1 ++ ps2 ++ ps3) f) (len1 : pos1.length = ps1.length)
    (len2 : pos2.length = ps2.length) : Ready triples s (pos2 ++ pos1 ++ pos3) (ps2 ++ ps1 ++ ps3) f := by
  obtain ⟨at12, at3⟩ := at_append_inv ready.holds (by simp [len1, len2])
  obtain ⟨at1, at2⟩ := at_append_inv at12 len1
  have perm : (pos1 ++ pos2 ++ pos3).Perm (pos2 ++ pos1 ++ pos3) :=
    List.Perm.append_right _ List.perm_append_comm
  exact { complete := ready.complete
          holds := at_append (at_append at2 at1) at3
          nodup := perm.nodup_iff.mp ready.nodup
          free := fun i member => ready.free i (perm.mem_iff.mpr member)
          owns := fun i t y at_i unused about inF => perm.mem_iff.mp (ready.owns i t y at_i unused about inF)
          room := ready.room }

/-- The main triple of a block is at its first position, unused. -/
theorem ready_main {triples : alloc.vec.Vec rdf.Triple} {s : rdf_mapping.State} {a : Nat} {pos : List Nat}
    {main : Pattern} {rest : List Pattern} {fresh : List rdf.BlankNode}
    (ready : Ready triples s (a :: pos) (main :: rest) fresh) :
    ∃ t, triples.val[a]? = some t ∧ Matches main t ∧ s.used.val[a]? = some false := by
  obtain ⟨⟨t, at_t, fits⟩, -⟩ := List.forall₂_cons.mp ready.holds
  exact ⟨t, at_t, fits, ready.free a (by simp)⟩

/-- Once the main triple is used, the rest of the block is ready. -/
theorem ready_take {triples : alloc.vec.Vec rdf.Triple} {s : rdf_mapping.State} {a : Usize} {pos : List Nat}
    {main : Pattern} {rest : List Pattern} {fresh : List rdf.BlankNode}
    (ready : Ready triples s (a.val :: pos) (main :: rest) fresh) :
    Ready triples { s with used := s.used.set a true } pos rest fresh := by
  have r := ready_rest (pos1 := [a.val]) (ps1 := [main]) (f1 := []) (f2 := fresh) (by simpa using ready) rfl
    (marked_take s a) (fun i h => by simp [h]) (fun i h => by simpa using h) (by simp)
  exact r

/-- The patterns of a ready block are at most as many as the triples. -/
theorem ready_length {triples : alloc.vec.Vec rdf.Triple} {s : rdf_mapping.State} {pos : List Nat}
    {ps : List Pattern} {fresh : List rdf.BlankNode} (ready : Ready triples s pos ps fresh) :
    ps.length ≤ triples.val.length := by
  have inRange : ∀ i ∈ pos, i ∈ List.range triples.val.length := by
    intro i member
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem member
    obtain ⟨-, t, at_t, -⟩ := at_get ready.holds (k := k) (List.getElem?_eq_getElem hk)
    exact List.mem_range.mpr (List.getElem?_eq_some_iff.mp at_t).1
  have sub := (List.subperm_of_subset ready.nodup inRange).length_le
  rw [List.length_range, at_length ready.holds] at sub
  exact sub

theorem fuel_of_ready {triples : alloc.vec.Vec rdf.Triple} {s : rdf_mapping.State} {pos : List Nat}
    {ps : List Pattern} {fresh : List rdf.BlankNode} (ready : Ready triples s pos ps fresh) :
    ps.length ≤ (alloc.vec.Vec.len triples).val := by
  simpa using ready_length ready

theorem two_ext {α : Type} {xs : model.AtLeastTwo α} (empty : xs.rest.val = []) :
    ({ first := xs.first, second := xs.second, rest := alloc.vec.Vec.new α } : model.AtLeastTwo α) = xs :=
  at_least_two_ext rfl rfl (by simp [empty])

/-! ### The subjects and objects of main triples -/

/-- `class_pair` reads the class expressions of the subject and object of a main triple. -/
theorem class_pair_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    {c1 c2 : model.ClassExpression} {s0 s1 s2 : Supply} {n1 n2 : Node} {p1 p2 : List Pattern}
    (tce1 : TCE c1 s0 n1 p1 s1) (tce2 : TCE c2 s1 n2 p2 s2)
    (reads1 : ClassReads triples kinds c1 s0 n1 p1 s1) (reads2 : ClassReads triples kinds c2 s1 n2 p2 s2)
    {fresh : Supply} (split : s0 = fresh ++ s2) (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize)
    (pos : List Nat) (predicate : List U8)
    (ready : Ready triples s (a.val :: pos) (⟨n1, predicate, n2⟩ :: (p1 ++ p2)) fresh) (fuel : Usize)
    (fuelOk : (p1 ++ p2).length ≤ fuel.val) :
    ∃ s', rdf_mapping.class_pair triples kinds a s fuel = .ok (some (c1, c2, s')) ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have readyRest := ready_take ready
  obtain ⟨f1, eq1, sub1⟩ := tce_fresh tce1
  obtain ⟨f2, eq2, sub2⟩ := tce_fresh tce2
  have freshIs := fresh_split (by rw [← eq1]; exact split) eq2
  subst freshIs
  obtain ⟨pos1, pos2, rfl, at1, at2⟩ := at_split readyRest.holds
  have nodup1 : f1.Nodup := (List.nodup_append.mp nodup).1
  have nodup2 : f2.Nodup := (List.nodup_append.mp nodup).2.1
  have ready1 := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (by simpa using readyRest) rfl (at_length at1)
    (by simpa using nodup) (fun _ m => by simp at m) (blank_subjects_of sub2)
    (marked_refl { s with used := s.used.set a true }) (fun _ h => h.elim) (by simp)
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  simp only [List.length_append] at fuelOk
  obtain ⟨s3, run1, m1⟩ := reads1 f1 eq1 nodup1 _ pos1 node fuel (by rw [nodeView]; exact fits.1) ready1
    (by omega)
  have ready2 := ready_middle (pos3 := []) (ps3 := []) (f3 := []) (by simpa using readyRest) (at_length at1)
    (at_length at2) (by simpa using nodup) (blank_subjects_of sub1) (fun _ m => by simp at m) m1
    (fun _ h => h) (le_refl _)
  obtain ⟨s4, run2, m2⟩ := reads2 f2 eq2 nodup2 s3 pos2 t.object fuel fits.2.2 ready2 (by omega)
  refine ⟨s4, ?_, ?_⟩
  · rw [rdf_mapping.class_pair]
    simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun,
      run1, uncurry_apply_pair, run2]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_take s a) (marked_trans m1 m2)) (by simp))
      (fun j => ?_)
    simp only [List.mem_cons, List.mem_append]

/-- `property_pair` reads the object property expressions of the subject and
    object of a main triple. -/
theorem property_pair_complete (triples : alloc.vec.Vec rdf.Triple)
    {e1 e2 : model.ObjectPropertyExpression} {s0 s1 s2 : Supply} {n1 n2 : Node} {p1 p2 : List Pattern}
    (tope1 : TOPE e1 s0 n1 p1 s1) (tope2 : TOPE e2 s1 n2 p2 s2)
    {fresh : Supply} (split : s0 = fresh ++ s2) (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize)
    (t : rdf.Triple) (at_t : triples.val[a.val]? = some t) (subject : subjectView t.subject = n1)
    (object : objectView t.object = n2) (pos : List Nat) (ready : Ready triples s pos (p1 ++ p2) fresh) :
    ∃ s', rdf_mapping.property_pair triples a s = .ok (some (e1, e2, s')) ∧
      Marked s s' (fun i => i ∈ pos) fresh := by
  obtain ⟨f1, eq1, sub1⟩ := tope_fresh tope1
  obtain ⟨f2, eq2, sub2⟩ := tope_fresh tope2
  have freshIs := fresh_split (by rw [← eq1]; exact split) eq2
  subst freshIs
  obtain ⟨pos1, pos2, rfl, at1, at2⟩ := at_split ready.holds
  have ready1 := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (by simpa using ready) rfl (at_length at1)
    (by simpa using nodup) (fun _ m => by simp at m) (blank_subjects_of sub2) (marked_refl s) (fun _ h => h.elim)
    (by simp)
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  obtain ⟨s3, run1, m1⟩ := role_complete triples tope1 eq1 (by rw [nodeView]; exact subject) ready1
  have ready2 := ready_middle (pos3 := []) (ps3 := []) (f3 := []) (by simpa using ready) (at_length at1)
    (at_length at2) (by simpa using nodup) (blank_subjects_of sub1) (fun _ m => by simp at m) m1
    (fun _ h => h) (le_refl _)
  obtain ⟨s4, run2, m2⟩ := role_complete triples tope2 eq2 object ready2
  refine ⟨s4, ?_, ?_⟩
  · rw [rdf_mapping.property_pair]
    simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun, run1,
      uncurry_apply_pair, run2]
  · refine marked_same (marked_trans m1 m2) (fun j => ?_)
    simp only [List.mem_append]

/-- `data_pair` reads the IRIs of the subject and object of a main triple. -/
theorem data_pair_complete (triples : alloc.vec.Vec rdf.Triple) (a : Usize) (t : rdf.Triple)
    (at_t : triples.val[a.val]? = some t) (d1 d2 : model.DataProperty)
    (subject : subjectView t.subject = iriNode d1.iri) (object : objectView t.object = iriNode d2.iri) :
    rdf_mapping.data_pair triples a = .ok (some (d1, d2)) := by
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  rw [rdf_mapping.data_pair]
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun,
    node_iri_complete node d1.iri (by rw [nodeView]; exact subject), node_iri_complete t.object d2.iri object]

/-- `individual_pair` reads the individuals of the subject and object of a main triple. -/
theorem individual_pair_complete (triples : alloc.vec.Vec rdf.Triple) (a : Usize) (t : rdf.Triple)
    (at_t : triples.val[a.val]? = some t) (i1 i2 : model.Individual)
    (subject : subjectView t.subject = individualNode i1) (object : objectView t.object = individualNode i2) :
    rdf_mapping.individual_pair triples a = .ok (some (i1, i2)) := by
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  rw [rdf_mapping.individual_pair]
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun,
    node_individual_complete node i1 (by rw [nodeView]; exact subject),
    node_individual_complete t.object i2 object]

/-! ### Class axioms -/

theorem tce_node {c : model.ClassExpression} {s : Supply} {n : Node} {ps : List Pattern} {s' : Supply}
    (h : TCE c s n ps s') : (∃ cl, c = .Class cl ∧ n = iriNode cl.iri) ∨ ∃ x, n = .blank x := by
  cases h <;> first | exact Or.inl ⟨_, rfl, rfl⟩ | exact Or.inr ⟨_, rfl⟩

theorem subject_iri {subject : rdf.Subject} {iri : model.Iri} (view : subjectView subject = iriNode iri) :
    ∃ r : rdf.RdfIri, subject = .Iri r ∧ r.spelling = iri.spelling := by
  cases subject with
  | Iri r => exact ⟨r, rfl, vec_eq_of_val (by simpa [subjectView, iriNode] using view)⟩
  | Blank _ => simp [subjectView, iriNode] at view

theorem subject_blank {subject : rdf.Subject} {x : rdf.BlankNode} (view : subjectView subject = .blank x) :
    subject = .Blank x := by
  cases subject with
  | Iri _ => simp [subjectView] at view
  | Blank b => simp only [subjectView, Node.blank.injEq] at view; rw [view]

/-- The subject of an equivalence of classes is not a datatype. -/
theorem datatype_subject_false {kinds : rdf_mapping.Kinds} {axioms : List model.AnnotatedAxiom}
    (hk : KindsOf kinds axioms) {c : model.ClassExpression} {s0 s1 : Supply} {n : Node} {ps : List Pattern}
    (tce : TCE c s0 n ps s1) (classTyped : ∀ cl : model.Class, c = .Class cl → ¬ Typed axioms cl.iri .Datatype)
    {subject : rdf.Subject} (view : subjectView subject = n) :
    rdf_mapping.datatype_subject kinds subject = .ok false := by
  rcases tce_node tce with ⟨cl, rfl, rfl⟩ | ⟨x, rfl⟩
  · obtain ⟨r, rfl, spelling⟩ := subject_iri view
    rw [rdf_mapping.datatype_subject, spelling, hk cl.iri .Datatype]
    simp [classTyped cl rfl]
  · rw [subject_blank view, rdf_mapping.datatype_subject]

theorem sub_class_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    {c1 c2 : model.ClassExpression} {s0 s1 s2 : Supply} {n1 n2 : Node} {p1 p2 : List Pattern}
    (tce1 : TCE c1 s0 n1 p1 s1) (tce2 : TCE c2 s1 n2 p2 s2)
    (reads1 : ClassReads triples kinds c1 s0 n1 p1 s1) (reads2 : ClassReads triples kinds c2 s1 n2 p2 s2)
    {fresh : Supply} (split : s0 = fresh ++ s2) (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize)
    (pos : List Nat) (ready : Ready triples s (a.val :: pos) (⟨n1, rdfsSubClassOf, n2⟩ :: (p1 ++ p2)) fresh)
    (fuel : Usize) (fuelOk : (p1 ++ p2).length ≤ fuel.val) :
    ∃ s', rdf_mapping.sub_class triples kinds a s fuel = .ok (.Found (.SubClassOf c1 c2) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨s', run, marked⟩ := class_pair_complete triples kinds tce1 tce2 reads1 reads2 split nodup s a pos _ ready
    fuel fuelOk
  exact ⟨s', by rw [rdf_mapping.sub_class]; simp only [run, bind_ok, uncurry_apply_pair], marked⟩

theorem equivalent_classes_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    {axioms : List model.AnnotatedAxiom} (hk : KindsOf kinds axioms)
    {c1 c2 : model.ClassExpression} {s0 s1 s2 : Supply} {n1 n2 : Node} {p1 p2 : List Pattern}
    (tce1 : TCE c1 s0 n1 p1 s1) (tce2 : TCE c2 s1 n2 p2 s2)
    (reads1 : ClassReads triples kinds c1 s0 n1 p1 s1) (reads2 : ClassReads triples kinds c2 s1 n2 p2 s2)
    (classTyped : ∀ cl : model.Class, c1 = .Class cl → ¬ Typed axioms cl.iri .Datatype)
    {fresh : Supply} (split : s0 = fresh ++ s2) (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize)
    (pos : List Nat) (ready : Ready triples s (a.val :: pos) (⟨n1, owlEquivalentClass, n2⟩ :: (p1 ++ p2)) fresh)
    (fuel : Usize) (fuelOk : (p1 ++ p2).length ≤ fuel.val) :
    ∃ s', rdf_mapping.equivalent_class triples kinds a s fuel =
        .ok (.Found (.EquivalentClasses ⟨c1, c2, alloc.vec.Vec.new _⟩) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have notDatatype := datatype_subject_false hk tce1 classTyped fits.1
  obtain ⟨s', run, marked⟩ := class_pair_complete triples kinds tce1 tce2 reads1 reads2 split nodup s a pos _ ready
    fuel fuelOk
  refine ⟨s', ?_, marked⟩
  rw [rdf_mapping.equivalent_class]
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, notDatatype,
    Bool.false_eq_true, ↓reduceIte, run, uncurry_apply_pair, rdf_mapping.two]

theorem datatype_definition_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    {axioms : List model.AnnotatedAxiom} (hk : KindsOf kinds axioms) (d : model.Datatype)
    {r : model.DataRange} {s0 s1 : Supply} {n : Node} {p : List Pattern}
    (reads : RangeReads triples kinds r s0 n p s1) (declared : Typed axioms d.iri .Datatype)
    {fresh : Supply} (split : s0 = fresh ++ s1) (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize)
    (pos : List Nat) (ready : Ready triples s (a.val :: pos) (⟨iriNode d.iri, owlEquivalentClass, n⟩ :: p) fresh)
    (fuel : Usize) (fuelOk : p.length ≤ fuel.val) :
    ∃ s', rdf_mapping.equivalent_class triples kinds a s fuel = .ok (.Found (.DatatypeDefinition d r) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  obtain ⟨iri, subjectIs, spelling⟩ := subject_iri fits.1
  have isDatatype : rdf_mapping.datatype_subject kinds (.Iri iri) = .ok true := by
    rw [rdf_mapping.datatype_subject, spelling, hk d.iri .Datatype]
    simp [declared]
  obtain ⟨s', run, marked⟩ := reads fresh split nodup _ pos t.object fuel fits.2.2 (ready_take ready) fuelOk
  refine ⟨s', ?_, ?_⟩
  · rw [rdf_mapping.equivalent_class]
    simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, subjectIs, isDatatype,
      ↓reduceIte, take_correct, run, uncurry_apply_pair, iri_of_identity, spelling]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_take s a) marked) (by simp)) (fun j => ?_)
    simp only [List.mem_cons]

theorem disjoint_classes_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    {c1 c2 : model.ClassExpression} {s0 s1 s2 : Supply} {n1 n2 : Node} {p1 p2 : List Pattern}
    (tce1 : TCE c1 s0 n1 p1 s1) (tce2 : TCE c2 s1 n2 p2 s2)
    (reads1 : ClassReads triples kinds c1 s0 n1 p1 s1) (reads2 : ClassReads triples kinds c2 s1 n2 p2 s2)
    {fresh : Supply} (split : s0 = fresh ++ s2) (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize)
    (pos : List Nat) (ready : Ready triples s (a.val :: pos) (⟨n1, owlDisjointWith, n2⟩ :: (p1 ++ p2)) fresh)
    (fuel : Usize) (fuelOk : (p1 ++ p2).length ≤ fuel.val) :
    ∃ s', rdf_mapping.disjoint_class triples kinds a s fuel =
        .ok (.Found (.DisjointClasses ⟨c1, c2, alloc.vec.Vec.new _⟩) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨s', run, marked⟩ := class_pair_complete triples kinds tce1 tce2 reads1 reads2 split nodup s a pos _ ready
    fuel fuelOk
  exact ⟨s', by rw [rdf_mapping.disjoint_class]; simp only [run, bind_ok, uncurry_apply_pair, rdf_mapping.two],
    marked⟩

theorem disjoint_union_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (c : model.Class) (xs : model.AtLeastTwo model.ClassExpression) (cells : List rdf.BlankNode) (s0 s1 : Supply)
    (nodes : List Node) (ps : List Pattern) (cellsLen : cells.length = (members2 xs).length)
    (members : ClassesRead triples kinds (members2 xs) s0 nodes ps s1)
    {fresh : Supply} (split : cells ++ s0 = fresh ++ s1) (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize)
    (pos : List Nat)
    (ready : Ready triples s (a.val :: pos)
      (⟨iriNode c.iri, owlDisjointUnionOf, (listOf cells nodes).1⟩ :: ((listOf cells nodes).2 ++ ps)) fresh)
    (fuel : Usize) (fuelOk : ((listOf cells nodes).2 ++ ps).length ≤ fuel.val) :
    ∃ s', rdf_mapping.disjoint_union triples kinds a s fuel = .ok (.Found (.DisjointUnion c xs) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  obtain ⟨iri, subjectIs, spelling⟩ := subject_iri fits.1
  obtain ⟨f, eqf, subf⟩ := classes_read_fresh members
  have freshIs : fresh = cells ++ f := by
    rw [eqf] at split
    have h : (cells ++ f) ++ s1 = fresh ++ s1 := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  obtain ⟨s', run, marked⟩ := class_list2_complete triples kinds xs cells nodes ps s0 s1 cellsLen members f eqf nodup
    _ pos t.object fuel fits.2.2 (ready_take ready) fuelOk
  refine ⟨s', ?_, ?_⟩
  · rw [rdf_mapping.disjoint_union]
    simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, subjectIs, take_correct, run,
      uncurry_apply_pair, iri_of_identity, spelling]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_take s a) marked) (by simp)) (fun j => ?_)
    simp only [List.mem_cons]

/-! ### Axioms that a blank node represents -/

/-- The node of an axiom that a blank node represents: its typing triple used,
    the node recorded, and the triples about it. -/
theorem axiom_node_complete (triples : alloc.vec.Vec rdf.Triple) (x : rdf.BlankNode) (T : List U8)
    (head : List (List U8 × Node)) (rest : List Pattern) (f : List rdf.BlankNode) (sub : BlankSubjects f rest)
    (distinct : (rdfType :: head.map (·.1)).Nodup) (s : rdf_mapping.State) (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) (⟨.blank x, rdfType, .iri T⟩ :: (headPatterns x head ++ rest)) (x :: f))
    (nodup : (x :: f).Nodup) :
    ∃ (s1 : rdf_mapping.State) (hpos rpos : List Nat), pos = hpos ++ rpos ∧ hpos.length = head.length ∧
      rdf_mapping.axiom_node triples a s = .ok (some (x, s1)) ∧ Marked s s1 (fun j => j ∈ [a.val]) [x] ∧
      HeadsAt triples.val s1.used.val x hpos head ∧ (∀ i ∈ hpos, s1.used.val[i]? = some false) ∧
      Ready triples s1 (hpos ++ rpos) (headPatterns x head ++ rest) f := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have subjectIs := subject_blank fits.1
  have ready' : Ready triples s ([a.val] ++ pos) (headPatterns x ((rdfType, .iri T) :: head) ++ rest) (x :: f) := by
    simpa [headPatterns] using ready
  have outside : x ∉ f := (List.nodup_cons.mp nodup).1
  obtain ⟨hpos0, rpos, posIs, lenH0, -, heads0⟩ := construct_setup ready' sub outside distinct
  obtain ⟨hpos, rfl⟩ : ∃ hpos, hpos0 = a.val :: hpos := by
    match hpos0, lenH0 with
    | i :: hpos, _ =>
      have := congrArg List.head? posIs
      simp at this
      exact ⟨hpos, by rw [this]⟩
  have posSplit : pos = hpos ++ rpos := by simpa using posIs
  subst posSplit
  have room := ready.room
  simp only [List.length_cons] at room
  obtain ⟨s1, recordRun, mRecord⟩ := record_ok { s with used := s.used.set a true } x (by simp at room ⊢; omega)
  have m1 : Marked s s1 (fun j => j ∈ [a.val]) [x] :=
    marked_same (marked_fresh_eq (marked_trans (marked_take s a) mRecord) (by simp)) (fun j => by simp)
  have nodupPos := ready.nodup
  simp only [List.nodup_cons, List.mem_append, not_or] at nodupPos
  refine ⟨s1, hpos, rpos, rfl, by simpa using lenH0, ?_, m1, ?_, ?_, ?_⟩
  · rw [rdf_mapping.axiom_node]
    simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, subjectIs, take_correct, recordRun,
      bind_ok, copy_blank_identity]
  · have heads1 := heads_rest heads0 rfl rfl m1
    have holds1 : At triples.val ([a.val] ++ hpos) ([⟨.blank x, rdfType, .iri T⟩] ++ headPatterns x head) :=
      heads1.holds
    exact { holds := (at_append_inv holds1 rfl).2
            confined := fun i t' at_i unused about => by
              have member := heads1.confined i t' at_i unused about
              rcases List.mem_cons.mp member with here | there
              · exfalso
                subst here
                have inside : a.val < s.used.val.length := (List.getElem?_eq_some_iff.mp (ready.free a.val
                  (by simp))).1
                rw [marked_used m1 inside (by simp)] at unused
                cases unused
              · exact there
            distinct := (List.nodup_cons.mp (by simpa using heads0.distinct)).2 }
  · intro i member
    exact marked_unused m1 (ready.free i (by simp [member])) (by
      simp only [List.mem_singleton]
      intro same
      subst same
      exact nodupPos.1.1 member)
  · have r := ready_rest (pos1 := [a.val]) (ps1 := [⟨.blank x, rdfType, .iri T⟩]) (f1 := [x]) (f2 := f)
      (by simpa using ready) rfl m1 (fun j h => h) (fun j h => h) (by simp)
    exact r

theorem all_disjoint_classes_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (xs : model.AtLeastTwo model.ClassExpression) (x : rdf.BlankNode) (cells : List rdf.BlankNode) (s0 s1 : Supply)
    (nodes : List Node) (ps : List Pattern) (many : xs.rest.val ≠ []) (cellsLen : cells.length = (members2 xs).length)
    (members : ClassesRead triples kinds (members2 xs) s0 nodes ps s1)
    {fresh : Supply} (split : x :: (cells ++ s0) = fresh ++ s1) (nodup : fresh.Nodup) (s : rdf_mapping.State)
    (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) (⟨.blank x, rdfType, .iri owlAllDisjointClasses⟩ ::
      ⟨.blank x, owlMembers, (listOf cells nodes).1⟩ :: ((listOf cells nodes).2 ++ ps)) fresh)
    (fuel : Usize) (fuelOk : ((listOf cells nodes).2 ++ ps).length ≤ fuel.val) :
    ∃ s', rdf_mapping.all_disjoint_classes triples kinds a s fuel = .ok (.Found (.DisjointClasses xs) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨f, eqf, subf⟩ := classes_read_fresh members
  have freshIs : fresh = x :: (cells ++ f) := by
    rw [eqf] at split
    have h : (x :: (cells ++ f)) ++ s1 = fresh ++ s1 := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  have sub : BlankSubjects (cells ++ f) ((listOf cells nodes).2 ++ ps) :=
    blank_subjects_of (subjects_pair (list_of_subjects cells nodes) subf)
  obtain ⟨s2, hpos, rpos, rfl, lenH, nodeRun, m1, heads, unusedH, ready2⟩ := axiom_node_complete triples x
    owlAllDisjointClasses [(owlMembers, (listOf cells nodes).1)] _ (cells ++ f) sub
    (by simp [rdfType, owlMembers]) s a pos (by simpa [headPatterns] using ready) nodup
  obtain ⟨b, rfl⟩ : ∃ b, hpos = [b] := by
    match hpos, lenH with
    | [b], _ => exact ⟨b, rfl⟩
  have complete2 : SubjectsComplete triples.val s2.subjects.val (alloc.vec.Vec.len s2.subjects)
      triples.val.length := by rw [m1.subjects]; exact ready.complete
  obtain ⟨found, foundVal, hit⟩ := find_hit triples s2 x complete2 heads (k := 0) rfl owlMembers (fun _ => rfl)
    (unusedH b (by simp))
  obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads (k := 0) rfl
  simp only [List.getElem_cons_zero] at object
  have ready3 := ready_rest (pos1 := [b]) (ps1 := headPatterns x [(owlMembers, (listOf cells nodes).1)]) (f1 := [])
    (f2 := cells ++ f) (by simpa using ready2) rfl (marked_take s2 found) (fun j h => by simp [h, foundVal])
    (fun j h => by simp at h; simp [h, foundVal]) (by simp)
  obtain ⟨s3, run, m3⟩ := class_list2_complete triples kinds xs cells nodes ps s0 s1 cellsLen members f eqf
    (List.nodup_cons.mp nodup).2 _ rpos t.object fuel object ready3 fuelOk
  have long : alloc.vec.Vec.len xs.rest ≥ 1#usize := by
    have h : 0 < xs.rest.val.length := List.length_pos_iff.mpr many
    clear * - h
    scalar_tac
  refine ⟨s3, ?_, ?_⟩
  · rw [rdf_mapping.all_disjoint_classes]
    simp only [nodeRun, bind_ok, uncurry_apply_pair, lift, hit, array_slice_val, owlMembers,
      take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples found t (by rw [foundVal]; exact at_t), run,
      long, ↓reduceIte]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_trans m1 (marked_take s2 found)) m3) (by simp))
      (fun j => ?_)
    simp only [List.mem_cons, List.mem_singleton, List.mem_append, foundVal, List.not_mem_nil, or_false, or_assoc]

/-! ### Property axioms -/

theorem topes_two {e1 e2 : model.ObjectPropertyExpression} {s0 s2 : Supply} {ns : List Node} {ps : List Pattern}
    (h : TOPEs [e1, e2] s0 ns ps s2) :
    ∃ (s1 : Supply) (n1 n2 : Node) (p1 p2 : List Pattern), ns = [n1, n2] ∧ ps = p1 ++ p2 ∧
      TOPE e1 s0 n1 p1 s1 ∧ TOPE e2 s1 n2 p2 s2 := by
  obtain ⟨s1, n1, ns', p1, q, rfl, rfl, h1, rest⟩ := topes_cons_inv h
  obtain ⟨s1', n2, ns'', p2, q', rfl, rfl, h2, rest'⟩ := topes_cons_inv rest
  cases rest'
  exact ⟨s1, n1, n2, p1, p2, rfl, by simp, h1, h2⟩

theorem node_kind_annotation (kinds : rdf_mapping.Kinds) (p : model.AnnotationProperty) (node : rdf.Object)
    (view : objectView node = iriNode p.iri)
    (typed : rdf_mapping.property_kind kinds p.iri.spelling = .ok (some .Annotation)) :
    rdf_mapping.node_kind kinds node = .ok (some .Annotation) := by
  cases node with
  | Iri r =>
    have same : r.spelling = p.iri.spelling := vec_eq_of_val (by simpa [objectView, iriNode] using view)
    rw [rdf_mapping.node_kind.eq_def]
    simp only [same]
    exact typed
  | Blank _ => simp [objectView, iriNode] at view
  | Literal _ => simp [objectView, iriNode] at view

theorem subject_kind_of (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (t : rdf.Triple) (at_t : triples.val[a.val]? = some t) (k : rdf_mapping.PropertyKind)
    (h : ∀ node : rdf.Object, objectView node = subjectView t.subject → rdf_mapping.node_kind kinds node = .ok (some k)) :
    rdf_mapping.subject_kind triples kinds a = .ok (some k) := by
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  rw [rdf_mapping.subject_kind]
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun, h node nodeView]

/-- The pair of object property expressions after a main triple, with its marks. -/
theorem property_pair_after (triples : alloc.vec.Vec rdf.Triple)
    {e1 e2 : model.ObjectPropertyExpression} {s0 s1 s2 : Supply} {n1 n2 : Node} {p1 p2 : List Pattern}
    (tope1 : TOPE e1 s0 n1 p1 s1) (tope2 : TOPE e2 s1 n2 p2 s2) {fresh : Supply} (split : s0 = fresh ++ s2)
    (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize) (pos : List Nat) (predicate : List U8)
    (ready : Ready triples s (a.val :: pos) (⟨n1, predicate, n2⟩ :: (p1 ++ p2)) fresh) :
    ∃ (t : rdf.Triple) (s' : rdf_mapping.State), triples.val[a.val]? = some t ∧
      subjectView t.subject = n1 ∧ objectView t.object = n2 ∧
      rdf_mapping.property_pair triples a { s with used := s.used.set a true } = .ok (some (e1, e2, s')) ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  obtain ⟨s', run, marked⟩ := property_pair_complete triples tope1 tope2 split nodup _ a t at_t fits.1 fits.2.2 pos
    (ready_take ready)
  refine ⟨t, s', at_t, fits.1, fits.2.2, run, ?_⟩
  refine marked_same (marked_fresh_eq (marked_trans (marked_take s a) marked) (by simp)) (fun j => ?_)
  simp only [List.mem_cons]

theorem sub_object_property_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    {e1 e2 : model.ObjectPropertyExpression} {s0 s1 s2 : Supply} {n1 n2 : Node} {p1 p2 : List Pattern}
    (tope1 : TOPE e1 s0 n1 p1 s1) (tope2 : TOPE e2 s1 n2 p2 s2)
    (typed : UsesTyped kinds (Rowl.Collection.objectUses e1)) {fresh : Supply} (split : s0 = fresh ++ s2)
    (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) (⟨n1, rdfsSubPropertyOf, n2⟩ :: (p1 ++ p2)) fresh) :
    ∃ s', rdf_mapping.sub_property triples kinds a s =
        .ok (.Found (.SubObjectPropertyOf (.Single e1) e2) s') ∧ Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, s', at_t, subject, -, run, marked⟩ := property_pair_after triples tope1 tope2 split nodup s a pos _ ready
  have kind := subject_kind_of triples kinds a t at_t .Object
    (fun node view => node_kind_object kinds tope1 node (view.trans subject) (role_typed typed))
  refine ⟨s', ?_, marked⟩
  rw [rdf_mapping.sub_property]
  simp only [take_correct, bind_ok, kind, run, uncurry_apply_pair]

theorem sub_data_property_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (d1 d2 : model.DataProperty) (typed : UsesTyped kinds (Rowl.Collection.dataUses d1)) (s : rdf_mapping.State)
    (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) [⟨iriNode d1.iri, rdfsSubPropertyOf, iriNode d2.iri⟩] []) :
    ∃ s', rdf_mapping.sub_property triples kinds a s = .ok (.Found (.SubDataPropertyOf d1 d2) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) [] := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
  have kind := subject_kind_of triples kinds a t at_t .Data
    (fun node view => node_kind_data kinds d1 node (view.trans fits.1) (data_typed typed))
  refine ⟨_, ?_, marked_nil_take s a⟩
  rw [rdf_mapping.sub_property]
  simp only [take_correct, bind_ok, kind, data_pair_complete triples a t at_t d1 d2 fits.1 fits.2.2,
    uncurry_apply_pair]

theorem sub_annotation_property_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (p1 p2 : model.AnnotationProperty)
    (typed : rdf_mapping.property_kind kinds p1.iri.spelling = .ok (some .Annotation)) (s : rdf_mapping.State)
    (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) [⟨iriNode p1.iri, rdfsSubPropertyOf, iriNode p2.iri⟩] []) :
    ∃ s', rdf_mapping.sub_property triples kinds a s = .ok (.Found (.SubAnnotationPropertyOf p1 p2) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) [] := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
  have kind := subject_kind_of triples kinds a t at_t .Annotation
    (fun node view => node_kind_annotation kinds p1 node (view.trans fits.1) typed)
  refine ⟨_, ?_, marked_nil_take s a⟩
  rw [rdf_mapping.sub_property]
  simp only [take_correct, bind_ok, kind,
    data_pair_complete triples a t at_t ⟨p1.iri⟩ ⟨p2.iri⟩ fits.1 fits.2.2, uncurry_apply_pair]

theorem property_chain_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (chain : model.AtLeastTwo model.ObjectPropertyExpression) (sup : model.ObjectPropertyExpression)
    (cells : List rdf.BlankNode) (s0 s1 s2 : Supply) (n : Node) (nodes : List Node) (p ps : List Pattern)
    (topeSup : TOPE sup s0 n p (cells ++ s1)) (cellsLen : cells.length = (members2 chain).length)
    (members : TOPEs (members2 chain) s1 nodes ps s2)
    (typed : ∀ e ∈ members2 chain, UsesTyped kinds (Rowl.Collection.objectUses e))
    {fresh : Supply} (split : s0 = fresh ++ s2) (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize)
    (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) (⟨n, owlPropertyChainAxiom, (listOf cells nodes).1⟩ ::
      ((listOf cells nodes).2 ++ p ++ ps)) fresh)
    (fuel : Usize) (fuelOk : cells.length ≤ fuel.val) :
    ∃ s', rdf_mapping.property_chain triples kinds a s fuel =
        .ok (.Found (.SubObjectPropertyOf (.Chain chain) sup) s') ∧ Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  obtain ⟨fS, eqS, subS⟩ := tope_fresh topeSup
  obtain ⟨fC, eqC, subC⟩ := topes_fresh members
  have freshIs : fresh = fS ++ (cells ++ fC) := by
    rw [eqC] at eqS
    rw [eqS] at split
    have h : (fS ++ (cells ++ fC)) ++ s2 = fresh ++ s2 := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  have readyRest := ready_take ready
  obtain ⟨posLP, posC, rfl, atLP, atC⟩ := at_split readyRest.holds
  obtain ⟨posL, posP, rfl, atL, atP⟩ := at_split atLP
  have swapped := ready_swap readyRest (at_length atL) (at_length atP)
  have nodupAll := nodup
  rw [List.nodup_append] at nodupAll
  have readyP := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (pos3 := posL ++ posC)
    (ps3 := (listOf cells nodes).2 ++ ps) (f3 := cells ++ fC) (by simpa [List.append_assoc] using swapped) rfl
    (at_length atP) (by simpa using nodup) (fun _ m => by simp at m)
    (blank_subjects_of (subjects_pair (list_of_subjects cells nodes) subC)) (marked_refl _) (fun _ h => h.elim)
    (by simp)
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  obtain ⟨s3, run1, m1⟩ := role_complete triples topeSup eqS (by rw [nodeView]; exact fits.1) readyP
  have readyL := ready_middle (pos1 := posP) (ps1 := p) (f1 := fS) (pos3 := []) (ps3 := []) (f3 := [])
    (pos2 := posL ++ posC) (ps2 := (listOf cells nodes).2 ++ ps) (f2 := cells ++ fC)
    (by simpa [List.append_assoc] using swapped) (at_length atP) (by simp [at_length atL, at_length atC])
    (by simpa using nodup) (blank_subjects_of subS) (fun _ m => by simp at m) m1 (fun _ h => h) (le_refl _)
  obtain ⟨s4, run2, m2⟩ := property_list2_complete triples kinds chain cells nodes ps s1 s2 cellsLen members typed fC
    eqC nodupAll.2.1 s3 (posL ++ posC) t.object fuel fits.2.2 readyL fuelOk
  refine ⟨s4, ?_, ?_⟩
  · rw [rdf_mapping.property_chain]
    simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun, run1,
      uncurry_apply_pair, run2]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_take s a) (marked_trans m1 m2)) (by simp))
      (fun j => ?_)
    simp only [List.mem_cons, List.mem_append]
    tauto

theorem equivalent_object_properties_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    {e1 e2 : model.ObjectPropertyExpression} {s0 s1 s2 : Supply} {n1 n2 : Node} {p1 p2 : List Pattern}
    (tope1 : TOPE e1 s0 n1 p1 s1) (tope2 : TOPE e2 s1 n2 p2 s2)
    (typed : UsesTyped kinds (Rowl.Collection.objectUses e1)) {fresh : Supply} (split : s0 = fresh ++ s2)
    (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) (⟨n1, owlEquivalentProperty, n2⟩ :: (p1 ++ p2)) fresh) :
    ∃ s', rdf_mapping.equivalent_property triples kinds a s =
        .ok (.Found (.EquivalentObjectProperties ⟨e1, e2, alloc.vec.Vec.new _⟩) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, s', at_t, subject, -, run, marked⟩ := property_pair_after triples tope1 tope2 split nodup s a pos _ ready
  have kind := subject_kind_of triples kinds a t at_t .Object
    (fun node view => node_kind_object kinds tope1 node (view.trans subject) (role_typed typed))
  refine ⟨s', ?_, marked⟩
  rw [rdf_mapping.equivalent_property]
  simp only [take_correct, bind_ok, kind, run, uncurry_apply_pair, rdf_mapping.two]

theorem equivalent_data_properties_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (d1 d2 : model.DataProperty) (typed : UsesTyped kinds (Rowl.Collection.dataUses d1)) (s : rdf_mapping.State)
    (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) [⟨iriNode d1.iri, owlEquivalentProperty, iriNode d2.iri⟩] []) :
    ∃ s', rdf_mapping.equivalent_property triples kinds a s =
        .ok (.Found (.EquivalentDataProperties ⟨d1, d2, alloc.vec.Vec.new _⟩) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) [] := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
  have kind := subject_kind_of triples kinds a t at_t .Data
    (fun node view => node_kind_data kinds d1 node (view.trans fits.1) (data_typed typed))
  refine ⟨_, ?_, marked_nil_take s a⟩
  rw [rdf_mapping.equivalent_property]
  simp only [take_correct, bind_ok, kind, data_pair_complete triples a t at_t d1 d2 fits.1 fits.2.2,
    uncurry_apply_pair, rdf_mapping.two]

theorem disjoint_object_properties_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    {e1 e2 : model.ObjectPropertyExpression} {s0 s1 s2 : Supply} {n1 n2 : Node} {p1 p2 : List Pattern}
    (tope1 : TOPE e1 s0 n1 p1 s1) (tope2 : TOPE e2 s1 n2 p2 s2)
    (typed : UsesTyped kinds (Rowl.Collection.objectUses e1)) {fresh : Supply} (split : s0 = fresh ++ s2)
    (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) (⟨n1, owlPropertyDisjointWith, n2⟩ :: (p1 ++ p2)) fresh) :
    ∃ s', rdf_mapping.disjoint_property triples kinds a s =
        .ok (.Found (.DisjointObjectProperties ⟨e1, e2, alloc.vec.Vec.new _⟩) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, s', at_t, subject, -, run, marked⟩ := property_pair_after triples tope1 tope2 split nodup s a pos _ ready
  have kind := subject_kind_of triples kinds a t at_t .Object
    (fun node view => node_kind_object kinds tope1 node (view.trans subject) (role_typed typed))
  refine ⟨s', ?_, marked⟩
  rw [rdf_mapping.disjoint_property]
  simp only [take_correct, bind_ok, kind, run, uncurry_apply_pair, rdf_mapping.two]

theorem disjoint_data_properties_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (d1 d2 : model.DataProperty) (typed : UsesTyped kinds (Rowl.Collection.dataUses d1)) (s : rdf_mapping.State)
    (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) [⟨iriNode d1.iri, owlPropertyDisjointWith, iriNode d2.iri⟩] []) :
    ∃ s', rdf_mapping.disjoint_property triples kinds a s =
        .ok (.Found (.DisjointDataProperties ⟨d1, d2, alloc.vec.Vec.new _⟩) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) [] := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
  have kind := subject_kind_of triples kinds a t at_t .Data
    (fun node view => node_kind_data kinds d1 node (view.trans fits.1) (data_typed typed))
  refine ⟨_, ?_, marked_nil_take s a⟩
  rw [rdf_mapping.disjoint_property]
  simp only [take_correct, bind_ok, kind, data_pair_complete triples a t at_t d1 d2 fits.1 fits.2.2,
    uncurry_apply_pair, rdf_mapping.two]

theorem inverse_properties_complete (triples : alloc.vec.Vec rdf.Triple) (p : model.ObjectProperty)
    {e2 : model.ObjectPropertyExpression} {s0 s2 : Supply} {n2 : Node} {p2 : List Pattern}
    (tope2 : TOPE e2 s0 n2 p2 s2) {fresh : Supply} (split : s0 = fresh ++ s2) (nodup : fresh.Nodup)
    (s : rdf_mapping.State) (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) (⟨iriNode p.iri, owlInverseOf, n2⟩ :: ([] ++ p2)) fresh) :
    ∃ s', rdf_mapping.inverse_properties triples a s =
        .ok (.Found (.InverseObjectProperties (.Property p) e2) s') ∧ Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, s', at_t, subject, -, run, marked⟩ := property_pair_after triples (.named p s0) tope2 split nodup s a pos _
    ready
  obtain ⟨iri, subjectIs, -⟩ := subject_iri subject
  refine ⟨s', ?_, marked⟩
  rw [rdf_mapping.inverse_properties]
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, subjectIs, take_correct, run,
    uncurry_apply_pair]

theorem object_domain_range_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (range : Bool) {role : model.ObjectPropertyExpression} {c : model.ClassExpression} {s0 s1 s2 : Supply}
    {n1 n2 : Node} {p1 p2 : List Pattern} (tope : TOPE role s0 n1 p1 s1) (tce : TCE c s1 n2 p2 s2)
    (typed : UsesTyped kinds (Rowl.Collection.objectUses role)) (reads : ClassReads triples kinds c s1 n2 p2 s2)
    {fresh : Supply} (split : s0 = fresh ++ s2) (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize)
    (pos : List Nat) (predicate : List U8)
    (ready : Ready triples s (a.val :: pos) (⟨n1, predicate, n2⟩ :: (p1 ++ p2)) fresh) (fuel : Usize)
    (fuelOk : (p1 ++ p2).length ≤ fuel.val) :
    ∃ s', rdf_mapping.domain_range triples kinds a s range fuel =
        .ok (.Found (if range then .ObjectPropertyRange role c else .ObjectPropertyDomain role c) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have readyRest := ready_take ready
  obtain ⟨f1, eq1, sub1⟩ := tope_fresh tope
  obtain ⟨f2, eq2, sub2⟩ := tce_fresh tce
  have freshIs := fresh_split (by rw [← eq1]; exact split) eq2
  subst freshIs
  obtain ⟨pos1, pos2, rfl, at1, at2⟩ := at_split readyRest.holds
  have nodup2 : f2.Nodup := (List.nodup_append.mp nodup).2.1
  have ready1 := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (by simpa using readyRest) rfl (at_length at1)
    (by simpa using nodup) (fun _ m => by simp at m) (blank_subjects_of sub2) (marked_refl _) (fun _ h => h.elim)
    (by simp)
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  have view : objectView node = n1 := by rw [nodeView]; exact fits.1
  obtain ⟨s3, run1, m1⟩ := role_complete triples tope eq1 view ready1
  have ready2 := ready_middle (pos3 := []) (ps3 := []) (f3 := []) (by simpa using readyRest) (at_length at1)
    (at_length at2) (by simpa using nodup) (blank_subjects_of sub1) (fun _ m => by simp at m) m1
    (fun _ h => h) (le_refl _)
  simp only [List.length_append] at fuelOk
  obtain ⟨s4, run2, m2⟩ := reads f2 eq2 nodup2 s3 pos2 t.object fuel fits.2.2 ready2 (by omega)
  refine ⟨s4, ?_, ?_⟩
  · rw [rdf_mapping.domain_range]
    cases range <;>
      simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun,
        node_kind_object kinds tope node view (role_typed typed), run1, uncurry_apply_pair, run2,
        Bool.false_eq_true, ↓reduceIte]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_take s a) (marked_trans m1 m2)) (by simp))
      (fun j => ?_)
    simp only [List.mem_cons, List.mem_append]

theorem data_domain_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (d : model.DataProperty) {c : model.ClassExpression} {s0 s1 : Supply} {n : Node} {p : List Pattern}
    (typed : UsesTyped kinds (Rowl.Collection.dataUses d)) (reads : ClassReads triples kinds c s0 n p s1)
    {fresh : Supply} (split : s0 = fresh ++ s1) (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize)
    (pos : List Nat) (ready : Ready triples s (a.val :: pos) (⟨iriNode d.iri, rdfsDomain, n⟩ :: p) fresh)
    (fuel : Usize) (fuelOk : p.length ≤ fuel.val) :
    ∃ s', rdf_mapping.domain_range triples kinds a s false fuel = .ok (.Found (.DataPropertyDomain d c) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  have view : objectView node = iriNode d.iri := by rw [nodeView]; exact fits.1
  obtain ⟨s', run, marked⟩ := reads fresh split nodup _ pos t.object fuel fits.2.2 (ready_take ready) fuelOk
  refine ⟨s', ?_, ?_⟩
  · rw [rdf_mapping.domain_range]
    simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun,
      node_kind_data kinds d node view (data_typed typed), node_iri_complete node d.iri view, run,
      uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_take s a) marked) (by simp)) (fun j => ?_)
    simp only [List.mem_cons]

theorem data_range_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (d : model.DataProperty) {r : model.DataRange} {s0 s1 : Supply} {n : Node} {p : List Pattern}
    (typed : UsesTyped kinds (Rowl.Collection.dataUses d)) (reads : RangeReads triples kinds r s0 n p s1)
    {fresh : Supply} (split : s0 = fresh ++ s1) (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize)
    (pos : List Nat) (ready : Ready triples s (a.val :: pos) (⟨iriNode d.iri, rdfsRange, n⟩ :: p) fresh)
    (fuel : Usize) (fuelOk : p.length ≤ fuel.val) :
    ∃ s', rdf_mapping.domain_range triples kinds a s true fuel = .ok (.Found (.DataPropertyRange d r) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  have view : objectView node = iriNode d.iri := by rw [nodeView]; exact fits.1
  obtain ⟨s', run, marked⟩ := reads fresh split nodup _ pos t.object fuel fits.2.2 (ready_take ready) fuelOk
  refine ⟨s', ?_, ?_⟩
  · rw [rdf_mapping.domain_range]
    simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun,
      node_kind_data kinds d node view (data_typed typed), node_iri_complete node d.iri view, run,
      uncurry_apply_pair, ↓reduceIte]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_take s a) marked) (by simp)) (fun j => ?_)
    simp only [List.mem_cons]

theorem annotation_domain_range_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (range : Bool) (p : model.AnnotationProperty) (iri : model.Iri)
    (typed : rdf_mapping.property_kind kinds p.iri.spelling = .ok (some .Annotation)) (s : rdf_mapping.State)
    (a : Usize) (pos : List Nat) (predicate : List U8)
    (ready : Ready triples s (a.val :: pos) [⟨iriNode p.iri, predicate, iriNode iri⟩] []) (fuel : Usize) :
    ∃ s', rdf_mapping.domain_range triples kinds a s range fuel =
        .ok (.Found (if range then .AnnotationPropertyRange p iri else .AnnotationPropertyDomain p iri) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) [] := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  have view : objectView node = iriNode p.iri := by rw [nodeView]; exact fits.1
  refine ⟨_, ?_, marked_nil_take s a⟩
  rw [rdf_mapping.domain_range]
  cases range <;>
    simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun,
      node_kind_annotation kinds p node view typed, node_iri_complete node p.iri view,
      node_iri_complete t.object iri fits.2.2, Bool.false_eq_true, ↓reduceIte]

/-- An object property characteristic of the subject of the main triple. -/
theorem characteristic_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ax : model.Axiom) (k : U8) {role : model.ObjectPropertyExpression} {s0 s1 : Supply} {n : Node}
    {p : List Pattern} (tope : TOPE role s0 n p s1) (typed : UsesTyped kinds (Rowl.Collection.objectUses role))
    (pick : ∀ s', (if k = 0#u8 then Result.ok (rdf_mapping.Read.Found (model.Axiom.FunctionalObjectProperty role) s')
      else if k = 1#u8 then .ok (.Found (.InverseFunctionalObjectProperty role) s')
      else if k = 2#u8 then .ok (.Found (.ReflexiveObjectProperty role) s')
      else if k = 3#u8 then .ok (.Found (.IrreflexiveObjectProperty role) s')
      else if k = 4#u8 then .ok (.Found (.SymmetricObjectProperty role) s')
      else if k = 5#u8 then .ok (.Found (.AsymmetricObjectProperty role) s')
      else .ok (.Found (.TransitiveObjectProperty role) s')) = .ok (.Found ax s'))
    {fresh : Supply} (split : s0 = fresh ++ s1) (s : rdf_mapping.State) (a : Usize) (pos : List Nat) (T : List U8)
    (ready : Ready triples s (a.val :: pos) (⟨n, rdfType, .iri T⟩ :: p) fresh) :
    ∃ s', rdf_mapping.characteristic triples kinds a s k = .ok (.Found ax s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  have view : objectView node = n := by rw [nodeView]; exact fits.1
  obtain ⟨s', run, marked⟩ := role_complete triples tope split view (ready_take ready)
  refine ⟨s', ?_, ?_⟩
  · rw [rdf_mapping.characteristic]
    simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun,
      node_kind_object kinds tope node view (role_typed typed), run, uncurry_apply_pair]
    exact pick s'
  · refine marked_same (marked_fresh_eq (marked_trans (marked_take s a) marked) (by simp)) (fun j => ?_)
    simp only [List.mem_cons]

theorem functional_data_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (d : model.DataProperty) (typed : UsesTyped kinds (Rowl.Collection.dataUses d)) (s : rdf_mapping.State)
    (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) [⟨iriNode d.iri, rdfType, .iri owlFunctionalProperty⟩] []) :
    ∃ s', rdf_mapping.characteristic triples kinds a s 0#u8 = .ok (.Found (.FunctionalDataProperty d) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) [] := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  have view : objectView node = iriNode d.iri := by rw [nodeView]; exact fits.1
  refine ⟨_, ?_, marked_nil_take s a⟩
  rw [rdf_mapping.characteristic]
  simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun,
    node_kind_data kinds d node view (data_typed typed), ↓reduceIte, node_iri_complete node d.iri view]

/-! ### Individual axioms and assertions -/

theorem same_individual_complete (triples : alloc.vec.Vec rdf.Triple) (i1 i2 : model.Individual)
    (s : rdf_mapping.State) (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) [⟨individualNode i1, owlSameAs, individualNode i2⟩] []) :
    ∃ s', rdf_mapping.same_individual triples a s =
        .ok (.Found (.SameIndividual ⟨i1, i2, alloc.vec.Vec.new _⟩) s') ∧ Marked s s' (fun i => i ∈ a.val :: pos) [] := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
  refine ⟨_, ?_, marked_nil_take s a⟩
  rw [rdf_mapping.same_individual]
  simp only [individual_pair_complete triples a t at_t i1 i2 fits.1 fits.2.2, bind_ok, uncurry_apply_pair,
    rdf_mapping.two, take_correct]

theorem different_individuals_complete (triples : alloc.vec.Vec rdf.Triple) (i1 i2 : model.Individual)
    (s : rdf_mapping.State) (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) [⟨individualNode i1, owlDifferentFrom, individualNode i2⟩] []) :
    ∃ s', rdf_mapping.different_individuals triples a s =
        .ok (.Found (.DifferentIndividuals ⟨i1, i2, alloc.vec.Vec.new _⟩) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) [] := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
  refine ⟨_, ?_, marked_nil_take s a⟩
  rw [rdf_mapping.different_individuals]
  simp only [individual_pair_complete triples a t at_t i1 i2 fits.1 fits.2.2, bind_ok, uncurry_apply_pair,
    rdf_mapping.two, take_correct]

theorem class_assertion_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (individual : model.Individual) {c : model.ClassExpression} {s0 s1 : Supply} {n : Node} {p : List Pattern}
    (reads : ClassReads triples kinds c s0 n p s1) {fresh : Supply} (split : s0 = fresh ++ s1) (nodup : fresh.Nodup)
    (s : rdf_mapping.State) (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) (⟨individualNode individual, rdfType, n⟩ :: p) fresh) (fuel : Usize)
    (fuelOk : p.length ≤ fuel.val) :
    ∃ s', rdf_mapping.class_assertion triples kinds a s fuel = .ok (.Found (.ClassAssertion c individual) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  obtain ⟨s', run, marked⟩ := reads fresh split nodup _ pos t.object fuel fits.2.2 (ready_take ready) fuelOk
  refine ⟨s', ?_, ?_⟩
  · rw [rdf_mapping.class_assertion]
    simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun,
      node_individual_complete node individual (by rw [nodeView]; exact fits.1), run, uncurry_apply_pair]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_take s a) marked) (by simp)) (fun j => ?_)
    simp only [List.mem_cons]

theorem predicate_spelling {t : rdf.Triple} {iri : model.Iri} (h : t.predicate.spelling.val = iri.spelling.val) :
    t.predicate.spelling = iri.spelling := vec_eq_of_val h

theorem object_assertion_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (p : model.ObjectProperty) (i1 i2 : model.Individual)
    (typed : rdf_mapping.property_kind kinds p.iri.spelling = .ok (some .Object)) (s : rdf_mapping.State)
    (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) [⟨individualNode i1, p.iri.spelling.val, individualNode i2⟩] []) :
    ∃ s', rdf_mapping.assertion triples kinds a s =
        .ok (.Found (.ObjectPropertyAssertion (.Property p) i1 i2) s') ∧ Marked s s' (fun i => i ∈ a.val :: pos) [] := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
  have spelling := predicate_spelling fits.2.1
  refine ⟨_, ?_, marked_nil_take s a⟩
  rw [rdf_mapping.assertion]
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, spelling, typed,
    individual_pair_complete triples a t at_t i1 i2 fits.1 fits.2.2, uncurry_apply_pair, iri_of_identity,
    take_correct]

theorem data_assertion_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (d : model.DataProperty) (individual : model.Individual) (v : model.Literal) (n : Node) (literal : LiteralNode v n)
    (readable : LiteralReadable v) (typed : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data))
    (s : rdf_mapping.State) (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) [⟨individualNode individual, d.iri.spelling.val, n⟩] []) :
    ∃ s', rdf_mapping.assertion triples kinds a s = .ok (.Found (.DataPropertyAssertion d individual v) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) [] := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
  have spelling := predicate_spelling fits.2.1
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  refine ⟨_, ?_, marked_nil_take s a⟩
  rw [rdf_mapping.assertion]
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, spelling, typed, nodeRun,
    node_individual_complete node individual (by rw [nodeView]; exact fits.1),
    literal_complete t.object v n literal readable fits.2.2, iri_of_identity, take_correct]

/-! ### Annotation assertions -/

/-- The types of the blank nodes of reifications and of axioms that blank
    nodes represent (Table 8). -/
def reifierTypes : List (List U8) :=
  [owlAxiom, owlAnnotation, owlAllDisjointClasses, owlAllDisjointProperties, owlAllDifferent,
    owlNegativePropertyAssertion]

theorem reifier_type_false (object : rdf.Object) (h : ∀ K ∈ reifierTypes, objectView object ≠ .iri K) :
    rdf_mapping.reifier_type object = .ok false := by
  have h1 := h owlAxiom (by simp [reifierTypes])
  have h2 := h owlAnnotation (by simp [reifierTypes])
  have h3 := h owlAllDisjointClasses (by simp [reifierTypes])
  have h4 := h owlAllDisjointProperties (by simp [reifierTypes])
  have h5 := h owlAllDifferent (by simp [reifierTypes])
  have h6 := h owlNegativePropertyAssertion (by simp [reifierTypes])
  simp only [owlAxiom, owlAnnotation, owlAllDisjointClasses, owlAllDisjointProperties, owlAllDifferent,
    owlNegativePropertyAssertion] at h1 h2 h3 h4 h5 h6
  rw [rdf_mapping.reifier_type]
  simp only [lift, bind_ok, object_is_correct, array_slice_val, h1, h2, h3, h4, h5, h6, decide_false,
    Bool.false_eq_true, ↓reduceIte]

theorem reifier_typing_false (triples : alloc.vec.Vec rdf.Triple) (node : rdf.BlankNode)
    (none : ∀ (i : Nat) (t : rdf.Triple), triples.val[i]? = some t → subjectView t.subject = .blank node →
      t.predicate.spelling.val = rdfType → ∀ K ∈ reifierTypes, objectView t.object ≠ .iri K)
    (index : Usize) : rdf_mapping.reifier_typing triples index node = .ok false := by
  rw [rdf_mapping.reifier_typing]
  by_cases inside : index.val < triples.val.length
  · have at_t : triples.val[index.val]? = some triples.val[index.val] := List.getElem?_eq_getElem inside
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      main_lookup triples index _ at_t, bind_ok, about_correct]
    by_cases about : subjectView triples.val[index.val].subject = .blank node
    · simp only [about, decide_true, ↓reduceIte, lift, bind_ok, same_correct, array_slice_val]
      by_cases typed : triples.val[index.val].predicate.spelling.val = rdfType
      · have typed' := typed
        simp only [rdfType] at typed'
        simp only [typed', decide_true, ↓reduceIte]
        exact reifier_type_false _ (none index.val _ at_t about typed)
      · simp only [rdfType] at typed
        simp [typed]
    · simp [about]
  · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]

theorem typed_reifier_in_false (triples : alloc.vec.Vec rdf.Triple) (bucket : alloc.vec.Vec Usize)
    (node : rdf.BlankNode) (none : ∀ index : Usize, rdf_mapping.reifier_typing triples index node = .ok false) :
    ∀ k : Usize, rdf_mapping.typed_reifier_in triples bucket node k = .ok false := by
  intro k
  induction e : bucket.val.length - k.val generalizing k with
  | zero =>
    have done : ¬ k.val < bucket.val.length := by omega
    rw [rdf_mapping.typed_reifier_in]; simp [UScalar.lt_equiv, done]
  | succ n ih =>
    have more : k.val < bucket.val.length := by omega
    have lookup : bucket.index_usize k = .ok bucket.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := k) (y := 1#usize) (by have := bucket.property; scalar_tac))
    have nextIs : next.val = k.val + 1 := by simpa using nextValue
    rw [rdf_mapping.typed_reifier_in]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
      bind_ok, none, Bool.false_eq_true, advance]
    exact ih next (by omega)

/-- A subject that no triple types with a type of Table 8 is no reifier. -/
theorem reifier_subject_false (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (subject : rdf.Subject)
    (none : ∀ b : rdf.BlankNode, subject = .Blank b → ∀ (i : Nat) (t : rdf.Triple), triples.val[i]? = some t →
      subjectView t.subject = .blank b → t.predicate.spelling.val = rdfType →
      ∀ K ∈ reifierTypes, objectView t.object ≠ .iri K) :
    rdf_mapping.reifier_subject triples s subject = .ok false := by
  cases subject with
  | Iri _ => simp [rdf_mapping.reifier_subject]
  | Blank b =>
    obtain ⟨h, hashRun⟩ := hash_blank_ok b
    obtain ⟨bucket, bucketRun, -⟩ := bucket_of_spec h (alloc.vec.Vec.len s.subjects)
    rw [rdf_mapping.reifier_subject]
    simp only [hashRun, bucketRun, bind_ok]
    by_cases inside : bucket.val < s.subjects.val.length
    · have lookup : s.subjects.index_usize bucket = .ok s.subjects.val[bucket.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        lookup, bind_ok]
      exact typed_reifier_in_false triples _ b (reifier_typing_false triples b (none b rfl)) 0#usize
    · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]

theorem annotation_value_complete (node : rdf.Object) (value : model.AnnotationValue) (n : Node)
    (h : AnnotationValueNode value n) (readable : ∀ v, value = .Literal v → LiteralReadable v)
    (view : objectView node = n) : rdf_mapping.annotation_value node = .ok (some value) := by
  cases h with
  | iri iri =>
    cases node with
    | Iri r =>
      have same : r.spelling.val = iri.spelling.val := by simpa [objectView, iriNode] using view
      simp only [rdf_mapping.annotation_value, iri_of_identity, bind_ok]
      rw [iri_ext (i := ⟨r.spelling⟩) (j := iri) same]
    | Blank _ => simp [objectView, iriNode] at view
    | Literal _ => simp [objectView, iriNode] at view
  | anonymous an =>
    cases node with
    | Iri _ => simp [objectView, anonymousNode] at view
    | Blank b =>
      have same : b = ⟨an.scope, an.label⟩ := by simpa [objectView, anonymousNode] using view
      subst same
      simp [rdf_mapping.annotation_value, Rowl.Nnf.copy_bytes_identity]
    | Literal _ => simp [objectView, anonymousNode] at view
  | literal v n literal =>
    have run := literal_complete node v n literal (readable v rfl) view
    cases node with
    | Iri _ => cases literal <;> simp [objectView] at view
    | Blank _ => cases literal <;> simp [objectView] at view
    | Literal lit =>
      rw [rdf_mapping.node_literal.eq_def] at run
      simp only at run
      simp only [rdf_mapping.annotation_value, run, bind_ok]

theorem annotation_subject_complete (subject : rdf.Subject) (sub : model.AnnotationSubject)
    (view : subjectView subject = annotationSubjectNode sub) : rdf_mapping.annotation_subject subject = .ok sub := by
  cases sub with
  | Iri iri =>
    cases subject with
    | Iri r =>
      have same : r.spelling.val = iri.spelling.val := by simpa [subjectView, annotationSubjectNode, iriNode] using view
      simp only [rdf_mapping.annotation_subject, iri_of_identity, bind_ok]
      rw [iri_ext (i := ⟨r.spelling⟩) (j := iri) same]
    | Blank _ => simp [subjectView, annotationSubjectNode, iriNode] at view
  | Anonymous an =>
    cases subject with
    | Iri _ => simp [subjectView, annotationSubjectNode, anonymousNode] at view
    | Blank b =>
      have same : b = ⟨an.scope, an.label⟩ := by simpa [subjectView, annotationSubjectNode, anonymousNode] using view
      subst same
      simp [rdf_mapping.annotation_subject, Rowl.Nnf.copy_bytes_identity]

theorem annotation_assertion_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (p : model.AnnotationProperty) (sub : model.AnnotationSubject) (value : model.AnnotationValue) (n : Node)
    (valueNode : AnnotationValueNode value n) (readable : ∀ v, value = .Literal v → LiteralReadable v)
    (typed : rdf_mapping.property_kind kinds p.iri.spelling = .ok (some .Annotation)) (s : rdf_mapping.State)
    (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) [⟨annotationSubjectNode sub, p.iri.spelling.val, n⟩] [])
    (notReifier : ∀ x, annotationSubjectNode sub = .blank x → ∀ (i : Nat) (t : rdf.Triple),
      triples.val[i]? = some t → subjectView t.subject = .blank x → t.predicate.spelling.val = rdfType →
      ∀ K ∈ reifierTypes, objectView t.object ≠ .iri K) :
    ∃ s', rdf_mapping.assertion triples kinds a s = .ok (.Found (.AnnotationAssertion p sub value) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) [] := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
  have spelling := predicate_spelling fits.2.1
  have reifierRun := reifier_subject_false triples s t.subject (fun b isBlank => by
    have : subjectView t.subject = .blank b := by rw [isBlank]; rfl
    exact notReifier b (fits.1.symm.trans this))
  refine ⟨_, ?_, marked_nil_take s a⟩
  rw [rdf_mapping.assertion]
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, spelling, typed]
  rw [rdf_mapping.annotation_assertion]
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, reifierRun,
    Bool.false_eq_true, ↓reduceIte, annotation_value_complete t.object value n valueNode readable fits.2.2,
    iri_of_identity, spelling, annotation_subject_complete t.subject sub fits.1, take_correct]

/-! ### Readiness under marks elsewhere -/

/-- A part of the patterns about none of the blank nodes can be left aside. -/
theorem ready_drop {triples : alloc.vec.Vec rdf.Triple} {s : rdf_mapping.State} {pos1 pos2 : List Nat}
    {ps1 ps2 : List Pattern} {f : List rdf.BlankNode} (ready : Ready triples s (pos1 ++ pos2) (ps1 ++ ps2) f)
    (len1 : pos1.length = ps1.length) (apart : ∀ q ∈ ps1, ∀ y ∈ f, q.subject ≠ .blank y) :
    Ready triples s pos2 ps2 f := by
  obtain ⟨at1, at2⟩ := at_append_inv ready.holds len1
  refine { complete := ready.complete
           holds := at2
           nodup := (List.nodup_append.mp ready.nodup).2.1
           free := fun i member => ready.free i (by simp [member])
           owns := ?_
           room := ready.room }
  intro i t y at_i unused about member
  rcases List.mem_append.mp (ready.owns i t y at_i unused about member) with in1 | in2
  · exfalso
    obtain ⟨q, qMem, fits⟩ := at_mem at1 in1 at_i
    exact apart q qMem y member (fits.1.symm.trans about)
  · exact in2

/-- Marks outside the positions keep them ready. -/
theorem ready_mark_outside {triples : alloc.vec.Vec rdf.Triple} {s s' : rdf_mapping.State} {pos : List Nat}
    {ps : List Pattern} {f : List rdf.BlankNode} {m : Nat → Prop} (ready : Ready triples s pos ps f)
    (marked : Marked s s' m []) (outside : ∀ i, m i → i ∉ pos) : Ready triples s' pos ps f where
  complete := by rw [marked.subjects]; exact ready.complete
  holds := ready.holds
  nodup := ready.nodup
  free := fun i member => marked_unused marked (ready.free i member) (fun hm => outside i hm member)
  owns := fun i t y at_i unused about member => ready.owns i t y at_i (marked_back marked unused) about member
  room := by have := ready.room; rw [marked.blanks]; simpa using this

theorem head_apart {x : rdf.BlankNode} {head : List (List U8 × Node)} {f : List rdf.BlankNode} (outside : x ∉ f) :
    ∀ q ∈ headPatterns x head, ∀ y ∈ f, q.subject ≠ .blank y := by
  intro q member y inF same
  simp only [headPatterns, List.mem_map] at member
  obtain ⟨e, -, rfl⟩ := member
  simp only [Node.blank.injEq] at same
  subst same
  exact outside inF

/-! ### The kind of the first member of a list -/

/-- The first member of a list has the kind of the node of its first element. -/
theorem first_member_kind_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (c0 : rdf.BlankNode) (cells : List rdf.BlankNode) (n0 : Node) (ns : List Node) (rest : List Pattern)
    (f : List rdf.BlankNode) (sub : BlankSubjects (cells ++ f) ((listOf cells ns).2 ++ rest))
    (outside : c0 ∉ cells ++ f) (k : rdf_mapping.PropertyKind)
    (firstKind : ∀ node : rdf.Object, objectView node = n0 → rdf_mapping.node_kind kinds node = .ok (some k))
    (s : rdf_mapping.State) (pos : List Nat)
    (ready : Ready triples s pos ((listOf (c0 :: cells) (n0 :: ns)).2 ++ rest) (c0 :: (cells ++ f))) :
    rdf_mapping.first_member_kind triples kinds s (.Blank c0) = .ok (some k) := by
  have ready' : Ready triples s pos (headPatterns c0 [(rdfFirst, n0), (rdfRest, (listOf cells ns).1)] ++
      ((listOf cells ns).2 ++ rest)) (c0 :: (cells ++ f)) := by
    simpa [headPatterns, list_of_cons] using ready
  obtain ⟨hpos, rpos, rfl, lenH, -, heads⟩ := construct_setup ready' sub outside (by simp [rdfFirst, rdfRest])
  obtain ⟨h0, h1, rfl⟩ : ∃ h0 h1, hpos = [h0, h1] := by
    match hpos, lenH with
    | [h0, h1], _ => exact ⟨h0, h1, rfl⟩
  obtain ⟨found, foundVal, hit⟩ := find_hit triples s c0 ready.complete heads (k := 0) rfl rdfFirst (fun _ => rfl)
    (ready.free h0 (by simp))
  obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads (k := 0) rfl
  simp only [List.getElem_cons_zero] at object
  rw [rdf_mapping.first_member_kind]
  simp only [lift, bind_ok, hit, array_slice_val, rdfFirst, alloc.vec.Vec.index_slice_index,
    main_lookup triples found t (by rw [foundVal]; exact at_t), firstKind t.object object]

/-! ### Disjoint properties and different individuals of three or more -/

theorem all_disjoint_object_properties_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (xs : model.AtLeastTwo model.ObjectPropertyExpression) (x : rdf.BlankNode) (cells : List rdf.BlankNode)
    (s0 s1 : Supply) (nodes : List Node) (ps : List Pattern) (many : xs.rest.val ≠ [])
    (cellsLen : cells.length = (members2 xs).length) (members : TOPEs (members2 xs) s0 nodes ps s1)
    (typed : ∀ e ∈ members2 xs, UsesTyped kinds (Rowl.Collection.objectUses e))
    {fresh : Supply} (split : x :: (cells ++ s0) = fresh ++ s1) (nodup : fresh.Nodup) (s : rdf_mapping.State)
    (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) (⟨.blank x, rdfType, .iri owlAllDisjointProperties⟩ ::
      ⟨.blank x, owlMembers, (listOf cells nodes).1⟩ :: ((listOf cells nodes).2 ++ ps)) fresh)
    (fuel : Usize) (fuelOk : cells.length ≤ fuel.val) :
    ∃ s', rdf_mapping.all_disjoint_properties triples kinds a s fuel =
        .ok (.Found (.DisjointObjectProperties xs) s') ∧ Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨f, eqf, subf⟩ := topes_fresh members
  have freshIs : fresh = x :: (cells ++ f) := by
    rw [eqf] at split
    have h : (x :: (cells ++ f)) ++ s1 = fresh ++ s1 := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  have sub : BlankSubjects (cells ++ f) ((listOf cells nodes).2 ++ ps) :=
    blank_subjects_of (subjects_pair (list_of_subjects cells nodes) subf)
  obtain ⟨s2, hpos, rpos, rfl, lenH, nodeRun, m1, heads, unusedH, ready2⟩ := axiom_node_complete triples x
    owlAllDisjointProperties [(owlMembers, (listOf cells nodes).1)] _ (cells ++ f) sub
    (by simp [rdfType, owlMembers]) s a pos (by simpa [headPatterns] using ready) nodup
  obtain ⟨b, rfl⟩ : ∃ b, hpos = [b] := by
    match hpos, lenH with
    | [b], _ => exact ⟨b, rfl⟩
  have complete2 : SubjectsComplete triples.val s2.subjects.val (alloc.vec.Vec.len s2.subjects)
      triples.val.length := by rw [m1.subjects]; exact ready.complete
  obtain ⟨found, foundVal, hit⟩ := find_hit triples s2 x complete2 heads (k := 0) rfl owlMembers (fun _ => rfl)
    (unusedH b (by simp))
  obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads (k := 0) rfl
  simp only [List.getElem_cons_zero] at object
  have ready3 := ready_rest (pos1 := [b]) (ps1 := headPatterns x [(owlMembers, (listOf cells nodes).1)]) (f1 := [])
    (f2 := cells ++ f) (by simpa using ready2) rfl (marked_take s2 found) (fun j h => by simp [h, foundVal])
    (fun j h => by simp at h; simp [h, foundVal]) (by simp)
  have nodupRest := (List.nodup_cons.mp nodup).2
  -- the first member is an object property expression
  obtain ⟨sA, nA, nsA, pA, qA, rfl, rfl, headA, tailA⟩ := topes_cons_inv members
  obtain ⟨c0, cells', rfl⟩ : ∃ c0 cells', cells = c0 :: cells' := by
    cases cells with
    | nil => simp [members2] at cellsLen
    | cons c0 cells' => exact ⟨c0, cells', rfl⟩
  obtain ⟨fA, eqA, subA⟩ := tope_fresh headA
  obtain ⟨fQ, eqQ, subQ⟩ := topes_fresh tailA
  have kindRun := first_member_kind_complete triples kinds c0 cells' nA nsA (pA ++ qA) f
    (blank_subjects_of (subjects_pair (list_of_subjects cells' nsA) subf))
    (List.nodup_cons.mp (by simpa using nodupRest)).1 .Object
    (fun node view => node_kind_object kinds headA node view (role_typed (typed xs.first (by simp [members2]))))
    _ rpos (by simpa using ready3)
  obtain ⟨s3, run, m3⟩ := property_list2_complete triples kinds xs (c0 :: cells') (nA :: nsA) (pA ++ qA) s0 s1
    cellsLen members typed f eqf nodupRest _ rpos t.object fuel object ready3 fuelOk
  have long : alloc.vec.Vec.len xs.rest ≥ 1#usize := by
    have h : 0 < xs.rest.val.length := List.length_pos_iff.mpr many
    clear * - h
    scalar_tac
  have objectIs : t.object = .Blank c0 := by
    cases objectEq : t.object with
    | Blank b' =>
      rw [objectEq] at object
      simp [objectView, listOf] at object
      rw [object]
    | Iri _ => rw [objectEq] at object; simp [objectView, listOf] at object
    | Literal _ => rw [objectEq] at object; simp [objectView, listOf] at object
  refine ⟨s3, ?_, ?_⟩
  · rw [rdf_mapping.all_disjoint_properties]
    rw [objectIs] at run
    simp only [nodeRun, bind_ok, uncurry_apply_pair, lift, hit, array_slice_val, owlMembers, take_correct,
      alloc.vec.Vec.index_slice_index, main_lookup triples found t (by rw [foundVal]; exact at_t), objectIs,
      kindRun, run, long, ↓reduceIte]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_trans m1 (marked_take s2 found)) m3) (by simp))
      (fun j => ?_)
    simp only [List.mem_cons, List.mem_singleton, List.mem_append, foundVal, List.not_mem_nil, or_false, or_assoc]

theorem all_disjoint_data_properties_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (xs : model.AtLeastTwo model.DataProperty) (x : rdf.BlankNode) (cells : List rdf.BlankNode) (s1 : Supply)
    (many : xs.rest.val ≠ []) (cellsLen : cells.length = (members2 xs).length)
    (typed : ∀ d ∈ members2 xs, UsesTyped kinds (Rowl.Collection.dataUses d))
    {fresh : Supply} (split : x :: (cells ++ s1) = fresh ++ s1) (nodup : fresh.Nodup) (s : rdf_mapping.State)
    (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) (⟨.blank x, rdfType, .iri owlAllDisjointProperties⟩ ::
      ⟨.blank x, owlMembers, (listOf cells ((members2 xs).map (iriNode ·.iri))).1⟩ ::
      (listOf cells ((members2 xs).map (iriNode ·.iri))).2) fresh)
    (fuel : Usize) (fuelOk : cells.length ≤ fuel.val) :
    ∃ s', rdf_mapping.all_disjoint_properties triples kinds a s fuel =
        .ok (.Found (.DisjointDataProperties xs) s') ∧ Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  have freshIs : fresh = x :: cells := by
    have h : (x :: cells) ++ s1 = fresh ++ s1 := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  have sub : BlankSubjects cells ((listOf cells ((members2 xs).map (iriNode ·.iri))).2 ++ []) := by
    simpa using blank_subjects_of (list_of_subjects cells ((members2 xs).map (iriNode ·.iri)))
  obtain ⟨s2, hpos, rpos, rfl, lenH, nodeRun, m1, heads, unusedH, ready2⟩ := axiom_node_complete triples x
    owlAllDisjointProperties [(owlMembers, (listOf cells ((members2 xs).map (iriNode ·.iri))).1)] _ cells sub
    (by simp [rdfType, owlMembers]) s a pos (by simpa [headPatterns] using ready) nodup
  obtain ⟨b, rfl⟩ : ∃ b, hpos = [b] := by
    match hpos, lenH with
    | [b], _ => exact ⟨b, rfl⟩
  have complete2 : SubjectsComplete triples.val s2.subjects.val (alloc.vec.Vec.len s2.subjects)
      triples.val.length := by rw [m1.subjects]; exact ready.complete
  obtain ⟨found, foundVal, hit⟩ := find_hit triples s2 x complete2 heads (k := 0) rfl owlMembers (fun _ => rfl)
    (unusedH b (by simp))
  obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads (k := 0) rfl
  simp only [List.getElem_cons_zero] at object
  have ready3 := ready_rest (pos1 := [b])
    (ps1 := headPatterns x [(owlMembers, (listOf cells ((members2 xs).map (iriNode ·.iri))).1)]) (f1 := [])
    (f2 := cells) (by simpa using ready2) rfl (marked_take s2 found) (fun j h => by simp [h, foundVal])
    (fun j h => by simp at h; simp [h, foundVal]) (by simp)
  have nodupRest := (List.nodup_cons.mp nodup).2
  obtain ⟨c0, cells', rfl⟩ : ∃ c0 cells', cells = c0 :: cells' := by
    cases cells with
    | nil => simp [members2] at cellsLen
    | cons c0 cells' => exact ⟨c0, cells', rfl⟩
  have kindRun := first_member_kind_complete triples kinds c0 cells' (iriNode xs.first.iri)
    ((xs.second :: xs.rest.val).map (iriNode ·.iri)) [] []
    (by simpa using blank_subjects_of (list_of_subjects cells' ((xs.second :: xs.rest.val).map (iriNode ·.iri))))
    (by simpa using (List.nodup_cons.mp nodupRest).1) .Data
    (fun node view => node_kind_data kinds xs.first node view (data_typed (typed xs.first (by simp [members2]))))
    _ rpos (by simpa [members2] using ready3)
  obtain ⟨s3, run, m3⟩ := data_list2_complete triples kinds xs (c0 :: cells') cellsLen nodupRest typed _ rpos
    t.object fuel object (by simpa using ready3) fuelOk
  have long : alloc.vec.Vec.len xs.rest ≥ 1#usize := by
    have h : 0 < xs.rest.val.length := List.length_pos_iff.mpr many
    clear * - h
    scalar_tac
  have objectIs : t.object = .Blank c0 := by
    cases objectEq : t.object with
    | Blank b' =>
      rw [objectEq] at object
      simp [objectView, listOf, members2] at object
      rw [object]
    | Iri _ => rw [objectEq] at object; simp [objectView, listOf, members2] at object
    | Literal _ => rw [objectEq] at object; simp [objectView, listOf, members2] at object
  refine ⟨s3, ?_, ?_⟩
  · rw [rdf_mapping.all_disjoint_properties]
    rw [objectIs] at run
    simp only [nodeRun, bind_ok, uncurry_apply_pair, lift, hit, array_slice_val, owlMembers, take_correct,
      alloc.vec.Vec.index_slice_index, main_lookup triples found t (by rw [foundVal]; exact at_t), objectIs,
      kindRun, run, long, ↓reduceIte]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_trans m1 (marked_take s2 found)) m3) (by simp))
      (fun j => ?_)
    simp only [List.mem_cons, List.mem_singleton, List.mem_append, foundVal, List.not_mem_nil, or_false, or_assoc]

theorem all_different_complete (triples : alloc.vec.Vec rdf.Triple) (xs : model.AtLeastTwo model.Individual)
    (x : rdf.BlankNode) (cells : List rdf.BlankNode) (s1 : Supply) (many : xs.rest.val ≠ [])
    (cellsLen : cells.length = (members2 xs).length)
    {fresh : Supply} (split : x :: (cells ++ s1) = fresh ++ s1) (nodup : fresh.Nodup) (s : rdf_mapping.State)
    (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) (⟨.blank x, rdfType, .iri owlAllDifferent⟩ ::
      ⟨.blank x, owlMembers, (listOf cells ((members2 xs).map individualNode)).1⟩ ::
      (listOf cells ((members2 xs).map individualNode)).2) fresh)
    (fuel : Usize) (fuelOk : cells.length ≤ fuel.val) :
    ∃ s', rdf_mapping.all_different triples a s fuel = .ok (.Found (.DifferentIndividuals xs) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  have freshIs : fresh = x :: cells := by
    have h : (x :: cells) ++ s1 = fresh ++ s1 := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  have sub : BlankSubjects cells ((listOf cells ((members2 xs).map individualNode)).2 ++ []) := by
    simpa using blank_subjects_of (list_of_subjects cells ((members2 xs).map individualNode))
  obtain ⟨s2, hpos, rpos, rfl, lenH, nodeRun, m1, heads, unusedH, ready2⟩ := axiom_node_complete triples x
    owlAllDifferent [(owlMembers, (listOf cells ((members2 xs).map individualNode)).1)] _ cells sub
    (by simp [rdfType, owlMembers]) s a pos (by simpa [headPatterns] using ready) nodup
  obtain ⟨b, rfl⟩ : ∃ b, hpos = [b] := by
    match hpos, lenH with
    | [b], _ => exact ⟨b, rfl⟩
  have complete2 : SubjectsComplete triples.val s2.subjects.val (alloc.vec.Vec.len s2.subjects)
      triples.val.length := by rw [m1.subjects]; exact ready.complete
  obtain ⟨found, foundVal, hit⟩ := find_hit triples s2 x complete2 heads (k := 0) rfl owlMembers (fun _ => rfl)
    (unusedH b (by simp))
  obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads (k := 0) rfl
  simp only [List.getElem_cons_zero] at object
  have ready3 := ready_rest (pos1 := [b])
    (ps1 := headPatterns x [(owlMembers, (listOf cells ((members2 xs).map individualNode)).1)]) (f1 := [])
    (f2 := cells) (by simpa using ready2) rfl (marked_take s2 found) (fun j h => by simp [h, foundVal])
    (fun j h => by simp at h; simp [h, foundVal]) (by simp)
  obtain ⟨s3, run, m3⟩ := individual_list2_complete triples xs cells cellsLen (List.nodup_cons.mp nodup).2 _ rpos
    t.object fuel object (by simpa using ready3) fuelOk
  have long : alloc.vec.Vec.len xs.rest ≥ 1#usize := by
    have h : 0 < xs.rest.val.length := List.length_pos_iff.mpr many
    clear * - h
    scalar_tac
  refine ⟨s3, ?_, ?_⟩
  · rw [rdf_mapping.all_different]
    simp only [nodeRun, bind_ok, uncurry_apply_pair, lift, hit, array_slice_val, owlMembers, take_correct,
      alloc.vec.Vec.index_slice_index, main_lookup triples found t (by rw [foundVal]; exact at_t), run, long,
      ↓reduceIte]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_trans m1 (marked_take s2 found)) m3) (by simp))
      (fun j => ?_)
    simp only [List.mem_cons, List.mem_singleton, List.mem_append, foundVal, List.not_mem_nil, or_false, or_assoc]

/-! ### Negative property assertions -/

theorem negative_object_assertion_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (role : model.ObjectPropertyExpression) (i1 i2 : model.Individual) (x : rdf.BlankNode) {s0 s1 : Supply}
    {n : Node} {p : List Pattern} (tope : TOPE role s0 n p s1)
    (typed : UsesTyped kinds (Rowl.Collection.objectUses role)) {fresh : Supply} (split : x :: s0 = fresh ++ s1)
    (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize) (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) (⟨.blank x, rdfType, .iri owlNegativePropertyAssertion⟩ ::
      ⟨.blank x, owlSourceIndividual, individualNode i1⟩ :: ⟨.blank x, owlAssertionProperty, n⟩ ::
      ⟨.blank x, owlTargetIndividual, individualNode i2⟩ :: p) fresh) :
    ∃ s', rdf_mapping.negative_assertion triples kinds a s =
        .ok (.Found (.NegativeObjectPropertyAssertion role i1 i2) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨f, eqf, subf⟩ := tope_fresh tope
  have freshIs : fresh = x :: f := by
    rw [eqf] at split
    have h : (x :: f) ++ s1 = fresh ++ s1 := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  have outside : x ∉ f := (List.nodup_cons.mp nodup).1
  obtain ⟨s2, hpos, rpos, rfl, lenH, nodeRun, m1, heads, unusedH, ready2⟩ := axiom_node_complete triples x
    owlNegativePropertyAssertion [(owlSourceIndividual, individualNode i1), (owlAssertionProperty, n),
      (owlTargetIndividual, individualNode i2)] p f (blank_subjects_of subf)
    (by simp [rdfType, owlSourceIndividual, owlAssertionProperty, owlTargetIndividual]) s a pos
    (by simpa [headPatterns] using ready) nodup
  obtain ⟨h1, h2, h3, rfl⟩ : ∃ h1 h2 h3, hpos = [h1, h2, h3] := by
    match hpos, lenH with
    | [h1, h2, h3], _ => exact ⟨h1, h2, h3, rfl⟩
  have nodupPos := ready.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, List.mem_singleton, not_or, List.cons_append,
    List.nil_append] at nodupPos
  obtain ⟨-, ⟨h12, h13, h1r⟩, ⟨h23, h2r⟩, h3r, -⟩ := nodupPos
  have readyP0 := ready_drop ready2 (by simp [headPatterns]) (head_apart outside)
  have complete2 : SubjectsComplete triples.val s2.subjects.val (alloc.vec.Vec.len s2.subjects)
      triples.val.length := by rw [m1.subjects]; exact ready.complete
  -- the source individual
  obtain ⟨found1, foundVal1, hit1⟩ := find_hit triples s2 x complete2 heads (k := 0) rfl owlSourceIndividual
    (fun _ => rfl) (unusedH h1 (by simp))
  obtain ⟨_, t1, at_t1, -, -, object1⟩ := heads_at_triple heads (k := 0) rfl
  simp only [List.getElem_cons_zero] at object1
  have mT1 := marked_take s2 found1
  -- the property
  have heads3 := heads_rest heads rfl rfl mT1
  obtain ⟨found2, foundVal2, hit2⟩ := find_hit triples _ x (by rw [mT1.subjects]; exact complete2) heads3 (k := 1)
    rfl owlAssertionProperty (fun _ => rfl)
    (marked_unused mT1 (unusedH h2 (by simp)) (by rw [foundVal1]; exact fun h => h12 h.symm))
  obtain ⟨_, t2, at_t2, -, -, object2⟩ := heads_at_triple heads (k := 1) rfl
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at object2
  have mT2 := marked_take { s2 with used := s2.used.set found1 true } found2
  have m12 := marked_trans mT1 mT2
  have readyP := ready_mark_outside readyP0 m12 (by
    rintro j (h | h) member
    · rw [h, foundVal1] at member; exact h1r member
    · rw [h, foundVal2] at member; exact h2r member)
  obtain ⟨s5, run, m5⟩ := role_complete triples tope eqf object2 readyP
  -- the target individual
  have m125 := marked_trans m12 m5
  have heads5 := heads_rest heads rfl rfl m125
  obtain ⟨found3, foundVal3, hit3⟩ := find_hit triples s5 x (by rw [m125.subjects]; exact complete2) heads5 (k := 2)
    rfl owlTargetIndividual (fun _ => rfl)
    (marked_unused m125 (unusedH h3 (by simp)) (by
      rintro ((h | h) | h)
      · rw [foundVal1] at h; exact h13 h.symm
      · rw [foundVal2] at h; exact h23 h.symm
      · exact h3r h))
  obtain ⟨_, t3, at_t3, -, -, object3⟩ := heads_at_triple heads (k := 2) rfl
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at object3
  refine ⟨{ s5 with used := s5.used.set found3 true }, ?_, ?_⟩
  · rw [rdf_mapping.negative_assertion]
    simp only [nodeRun, bind_ok, uncurry_apply_pair, lift, hit1, hit2, hit3, array_slice_val, owlSourceIndividual,
      owlAssertionProperty, owlTargetIndividual, alloc.vec.Vec.index_slice_index,
      main_lookup triples found1 t1 (by rw [foundVal1]; exact at_t1),
      main_lookup triples found2 t2 (by rw [foundVal2]; exact at_t2),
      main_lookup triples found3 t3 (by rw [foundVal3]; exact at_t3),
      node_individual_complete t1.object i1 object1, node_individual_complete t3.object i2 object3, take_correct,
      node_kind_object kinds tope t2.object object2 (role_typed typed), run]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_trans m1 m125) (marked_take s5 found3)) (by simp))
      (fun j => ?_)
    simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, foundVal1,
      foundVal2, foundVal3]
    tauto

theorem negative_data_assertion_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (d : model.DataProperty) (i1 : model.Individual) (v : model.Literal) (x : rdf.BlankNode) (s0 : Supply) (n : Node)
    (literal : LiteralNode v n) (readable : LiteralReadable v) (typed : UsesTyped kinds (Rowl.Collection.dataUses d))
    {fresh : Supply} (split : x :: s0 = fresh ++ s0) (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize)
    (pos : List Nat)
    (ready : Ready triples s (a.val :: pos) [⟨.blank x, rdfType, .iri owlNegativePropertyAssertion⟩,
      ⟨.blank x, owlSourceIndividual, individualNode i1⟩, ⟨.blank x, owlAssertionProperty, iriNode d.iri⟩,
      ⟨.blank x, owlTargetValue, n⟩] fresh) :
    ∃ s', rdf_mapping.negative_assertion triples kinds a s =
        .ok (.Found (.NegativeDataPropertyAssertion d i1 v) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  have freshIs : fresh = [x] := by
    have h : [x] ++ s0 = fresh ++ s0 := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  obtain ⟨s2, hpos, rpos, rfl, lenH, nodeRun, m1, heads, unusedH, -⟩ := axiom_node_complete triples x
    owlNegativePropertyAssertion [(owlSourceIndividual, individualNode i1), (owlAssertionProperty, iriNode d.iri),
      (owlTargetValue, n)] [] [] (fun _ m => by simp at m)
    (by simp [rdfType, owlSourceIndividual, owlAssertionProperty, owlTargetValue]) s a pos
    (by simpa [headPatterns] using ready) nodup
  obtain ⟨h1, h2, h3, rfl⟩ : ∃ h1 h2 h3, hpos = [h1, h2, h3] := by
    match hpos, lenH with
    | [h1, h2, h3], _ => exact ⟨h1, h2, h3, rfl⟩
  have nodupPos := ready.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, List.mem_singleton, not_or, List.cons_append,
    List.nil_append] at nodupPos
  obtain ⟨-, ⟨h12, h13, -⟩, ⟨h23, -⟩, -, -⟩ := nodupPos
  have complete2 : SubjectsComplete triples.val s2.subjects.val (alloc.vec.Vec.len s2.subjects)
      triples.val.length := by rw [m1.subjects]; exact ready.complete
  obtain ⟨found1, foundVal1, hit1⟩ := find_hit triples s2 x complete2 heads (k := 0) rfl owlSourceIndividual
    (fun _ => rfl) (unusedH h1 (by simp))
  obtain ⟨_, t1, at_t1, -, -, object1⟩ := heads_at_triple heads (k := 0) rfl
  simp only [List.getElem_cons_zero] at object1
  have mT1 := marked_take s2 found1
  have heads3 := heads_rest heads rfl rfl mT1
  obtain ⟨found2, foundVal2, hit2⟩ := find_hit triples _ x (by rw [mT1.subjects]; exact complete2) heads3 (k := 1)
    rfl owlAssertionProperty (fun _ => rfl)
    (marked_unused mT1 (unusedH h2 (by simp)) (by rw [foundVal1]; exact fun h => h12 h.symm))
  obtain ⟨_, t2, at_t2, -, -, object2⟩ := heads_at_triple heads (k := 1) rfl
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at object2
  have mT2 := marked_take { s2 with used := s2.used.set found1 true } found2
  have m12 := marked_trans mT1 mT2
  have heads4 := heads_rest heads rfl rfl m12
  obtain ⟨found3, foundVal3, hit3⟩ := find_hit triples _ x (by rw [m12.subjects]; exact complete2) heads4 (k := 2)
    rfl owlTargetValue (fun _ => rfl)
    (marked_unused m12 (unusedH h3 (by simp)) (by
      rintro (h | h)
      · rw [foundVal1] at h; exact h13 h.symm
      · rw [foundVal2] at h; exact h23 h.symm))
  obtain ⟨_, t3, at_t3, -, -, object3⟩ := heads_at_triple heads (k := 2) rfl
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at object3
  refine ⟨{ s2 with used := ((s2.used.set found1 true).set found2 true).set found3 true }, ?_, ?_⟩
  · rw [rdf_mapping.negative_assertion]
    simp only [nodeRun, bind_ok, uncurry_apply_pair, lift, hit1, hit2, hit3, array_slice_val, owlSourceIndividual,
      owlAssertionProperty, owlTargetValue, alloc.vec.Vec.index_slice_index,
      main_lookup triples found1 t1 (by rw [foundVal1]; exact at_t1),
      main_lookup triples found2 t2 (by rw [foundVal2]; exact at_t2),
      main_lookup triples found3 t3 (by rw [foundVal3]; exact at_t3),
      node_individual_complete t1.object i1 object1, take_correct,
      node_kind_data kinds d t2.object object2 (data_typed typed), node_iri_complete t2.object d.iri object2,
      literal_complete t3.object v n literal readable object3]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_trans m1 m12) (marked_take _ found3)) (by simp))
      (fun j => ?_)
    have noRest : rpos = [] := by
      have := at_length ready.holds
      simp at this
      omega
    subst noRest
    simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, foundVal1,
      foundVal2, foundVal3, List.append_nil]
    tauto

/-! ### Keys -/

theorem has_key_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (c : model.ClassExpression)
    (objects : alloc.vec.Vec model.ObjectPropertyExpression) (datas : alloc.vec.Vec model.DataProperty)
    (cells : List rdf.BlankNode) (s0 s1 s2 : Supply) (n : Node) (nodes : List Node) (p ps : List Pattern)
    (tce : TCE c s0 n p (cells ++ s1)) (reads : ClassReads triples kinds c s0 n p (cells ++ s1))
    (cellsLen : cells.length = objects.val.length + datas.val.length) (members : TOPEs objects.val s1 nodes ps s2)
    (objectTyped : ∀ e ∈ objects.val, UsesTyped kinds (Rowl.Collection.objectUses e))
    (dataTyped : ∀ d ∈ datas.val, UsesTyped kinds (Rowl.Collection.dataUses d))
    {fresh : Supply} (split : s0 = fresh ++ s2) (nodup : fresh.Nodup) (s : rdf_mapping.State) (a : Usize)
    (pos : List Nat)
    (ready : Ready triples s (a.val :: pos)
      (⟨n, owlHasKey, (listOf cells (nodes ++ datas.val.map (iriNode ·.iri))).1⟩ ::
        ((listOf cells (nodes ++ datas.val.map (iriNode ·.iri))).2 ++ p ++ ps)) fresh)
    (fuel : Usize) (fuelOk : p.length ≤ fuel.val) (cellsOk : cells.length ≤ fuel.val) :
    ∃ s', rdf_mapping.has_key triples kinds a s fuel = .ok (.Found (.HasKey c objects datas) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  obtain ⟨fC, eqC, subC⟩ := tce_fresh tce
  obtain ⟨fO, eqO, subO⟩ := topes_fresh members
  have freshIs : fresh = fC ++ (cells ++ fO) := by
    rw [eqO] at eqC
    rw [eqC] at split
    have h : (fC ++ (cells ++ fO)) ++ s2 = fresh ++ s2 := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  have elementsLen : cells.length = (nodes ++ datas.val.map (iriNode ·.iri)).length := by
    rw [cellsLen, List.length_append, List.length_map, topes_length members]
  have readyRest := ready_take ready
  obtain ⟨posLP, posO, rfl, atLP, atO⟩ := at_split readyRest.holds
  obtain ⟨posL, posP, rfl, atL, atP⟩ := at_split atLP
  have swapped := ready_swap readyRest (at_length atL) (at_length atP)
  have nodupAll := nodup
  rw [List.nodup_append] at nodupAll
  have nodupRest := List.nodup_append.mp nodupAll.2.1
  have readyP := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (pos3 := posL ++ posO)
    (ps3 := (listOf cells (nodes ++ datas.val.map (iriNode ·.iri))).2 ++ ps) (f3 := cells ++ fO)
    (by simpa [List.append_assoc] using swapped) rfl (at_length atP) (by simpa using nodup)
    (fun _ m => by simp at m)
    (blank_subjects_of (subjects_pair (list_of_subjects cells _) subO)) (marked_refl _) (fun _ h => h.elim)
    (by simp)
  obtain ⟨node, nodeRun, nodeView⟩ := subject_node_view t.subject
  obtain ⟨sC, runC, mC⟩ := reads fC (by rw [eqC]) nodupAll.1 _ posP node fuel (by rw [nodeView]; exact fits.1)
    readyP fuelOk
  have readyL := ready_middle (pos1 := posP) (ps1 := p) (f1 := fC) (pos2 := posL)
    (ps2 := (listOf cells (nodes ++ datas.val.map (iriNode ·.iri))).2) (f2 := cells) (pos3 := posO) (ps3 := ps)
    (f3 := fO) (by simpa [List.append_assoc] using swapped) (at_length atP) (at_length atL)
    (by simpa [List.append_assoc] using nodup) (blank_subjects_of subC) (blank_subjects_of subO) mC
    (fun _ h => h) (le_refl _)
  obtain ⟨firsts, news, sL, cellsRun, firstsIs, elementsOk, mL⟩ := cells_complete triples cells
    (nodes ++ datas.val.map (iriNode ·.iri)) elementsLen nodupRest.1 sC posL t.object
    (alloc.vec.Vec.new Usize) fuel fits.2.2 readyL cellsOk (by simp; have := fuel.hBounds; scalar_tac)
  have mCL := marked_trans mC mL
  have readyO := ready_middle (pos1 := posP ++ posL)
    (ps1 := p ++ (listOf cells (nodes ++ datas.val.map (iriNode ·.iri))).2) (f1 := fC ++ cells) (pos2 := posO)
    (ps2 := ps) (f2 := fO) (pos3 := []) (ps3 := []) (f3 := [])
    (by simpa [List.append_assoc] using swapped) (by simp [at_length atP, at_length atL]) (at_length atO)
    (by simpa [List.append_assoc] using nodup)
    (blank_subjects_of (subjects_pair subC (list_of_subjects cells _))) (fun _ m => by simp at m) mCL
    (fun j hj => by simp only [List.mem_append]; exact hj) (le_refl _)
  have dataRoom : datas.val.length ≤ Usize.max := datas.property
  obtain ⟨vo, vd, sO, keyRun, voIs, vdIs, mO⟩ := key_members_complete triples kinds firsts datas.val dataTyped
    dataRoom members objectTyped fO eqO nodupRest.2.1 0#usize sL posO (alloc.vec.Vec.new _)
    (firsts_from_cells firstsIs elementsOk) readyO (by rw [new_length]; have := objects.property; omega)
  have voEq : vo = objects := vec_eq_of_val (by rw [voIs]; simp)
  have vdEq : vd = datas := vec_eq_of_val vdIs
  subst voEq vdEq
  refine ⟨sO, ?_, ?_⟩
  · rw [rdf_mapping.has_key]
    simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, bind_ok, nodeRun, runC,
      uncurry_apply_pair, cellsRun, keyRun]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_take s a) (marked_trans mCL mO)) (by simp))
      (fun j => ?_)
    simp only [List.mem_cons, List.mem_append]
    tauto

/-! ### Declarations -/

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
theorem declaration_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (e : model.Entity)
    (s : rdf_mapping.State) (a : Usize) (pos : List Nat) (ready : Ready triples s (a.val :: pos) [declarationPattern e] [])
    (fuel : Usize) :
    ∃ s', rdf_mapping.read_axiom triples kinds a s fuel = .ok (.Found (.Declaration e) s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) [] := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
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
  refine ⟨_, ?_, marked_nil_take s a⟩
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

/-! ### Dispatch on the predicate of the main triple -/

theorem read_axiom_typing (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = rdfType) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.typing triples kinds a s fuel := by
  simp only [rdfType] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_sub_class (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = rdfsSubClassOf) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.sub_class triples kinds a s fuel := by
  simp only [rdfsSubClassOf] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_equivalent_class (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = owlEquivalentClass) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.equivalent_class triples kinds a s fuel := by
  simp only [owlEquivalentClass] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_disjoint_class (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = owlDisjointWith) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.disjoint_class triples kinds a s fuel := by
  simp only [owlDisjointWith] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_disjoint_union (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = owlDisjointUnionOf) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.disjoint_union triples kinds a s fuel := by
  simp only [owlDisjointUnionOf] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_sub_property (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = rdfsSubPropertyOf) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.sub_property triples kinds a s := by
  simp only [rdfsSubPropertyOf] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_property_chain (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = owlPropertyChainAxiom) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.property_chain triples kinds a s fuel := by
  simp only [owlPropertyChainAxiom] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_equivalent_property (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = owlEquivalentProperty) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.equivalent_property triples kinds a s := by
  simp only [owlEquivalentProperty] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_disjoint_property (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = owlPropertyDisjointWith) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.disjoint_property triples kinds a s := by
  simp only [owlPropertyDisjointWith] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_inverse_properties (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = owlInverseOf) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.inverse_properties triples a s := by
  simp only [owlInverseOf] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_domain (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = rdfsDomain) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.domain_range triples kinds a s false fuel := by
  simp only [rdfsDomain] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_range (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = rdfsRange) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.domain_range triples kinds a s true fuel := by
  simp only [rdfsRange] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_same_individual (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = owlSameAs) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.same_individual triples a s := by
  simp only [owlSameAs] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_different_individuals (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = owlDifferentFrom) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.different_individuals triples a s := by
  simp only [owlDifferentFrom] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

theorem read_axiom_has_key (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : t.predicate.spelling.val = owlHasKey) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.has_key triples kinds a s fuel := by
  simp only [owlHasKey] at h
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, h]

/-! ### Dispatch on the type of a typing triple -/

theorem typing_functional (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : objectView t.object = .iri owlFunctionalProperty) :
    rdf_mapping.typing triples kinds a s fuel = rdf_mapping.characteristic triples kinds a s 0#u8 := by
  simp only [owlFunctionalProperty] at h
  rw [rdf_mapping.typing]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val, h,
    rdf_mapping.declares, rdf_mapping.declaration_kind]

theorem typing_inverse_functional (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : objectView t.object = .iri owlInverseFunctionalProperty) :
    rdf_mapping.typing triples kinds a s fuel = rdf_mapping.characteristic triples kinds a s 1#u8 := by
  simp only [owlInverseFunctionalProperty] at h
  rw [rdf_mapping.typing]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val, h,
    rdf_mapping.declares, rdf_mapping.declaration_kind]

theorem typing_reflexive (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : objectView t.object = .iri owlReflexiveProperty) :
    rdf_mapping.typing triples kinds a s fuel = rdf_mapping.characteristic triples kinds a s 2#u8 := by
  simp only [owlReflexiveProperty] at h
  rw [rdf_mapping.typing]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val, h,
    rdf_mapping.declares, rdf_mapping.declaration_kind]

theorem typing_irreflexive (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : objectView t.object = .iri owlIrreflexiveProperty) :
    rdf_mapping.typing triples kinds a s fuel = rdf_mapping.characteristic triples kinds a s 3#u8 := by
  simp only [owlIrreflexiveProperty] at h
  rw [rdf_mapping.typing]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val, h,
    rdf_mapping.declares, rdf_mapping.declaration_kind]

theorem typing_symmetric (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : objectView t.object = .iri owlSymmetricProperty) :
    rdf_mapping.typing triples kinds a s fuel = rdf_mapping.characteristic triples kinds a s 4#u8 := by
  simp only [owlSymmetricProperty] at h
  rw [rdf_mapping.typing]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val, h,
    rdf_mapping.declares, rdf_mapping.declaration_kind]

theorem typing_asymmetric (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : objectView t.object = .iri owlAsymmetricProperty) :
    rdf_mapping.typing triples kinds a s fuel = rdf_mapping.characteristic triples kinds a s 5#u8 := by
  simp only [owlAsymmetricProperty] at h
  rw [rdf_mapping.typing]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val, h,
    rdf_mapping.declares, rdf_mapping.declaration_kind]

theorem typing_transitive (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : objectView t.object = .iri owlTransitiveProperty) :
    rdf_mapping.typing triples kinds a s fuel = rdf_mapping.characteristic triples kinds a s 6#u8 := by
  simp only [owlTransitiveProperty] at h
  rw [rdf_mapping.typing]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val, h,
    rdf_mapping.declares, rdf_mapping.declaration_kind]

theorem typing_all_disjoint_classes (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : objectView t.object = .iri owlAllDisjointClasses) :
    rdf_mapping.typing triples kinds a s fuel = rdf_mapping.all_disjoint_classes triples kinds a s fuel := by
  simp only [owlAllDisjointClasses] at h
  rw [rdf_mapping.typing]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val, h,
    rdf_mapping.declares, rdf_mapping.declaration_kind]

theorem typing_all_disjoint_properties (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : objectView t.object = .iri owlAllDisjointProperties) :
    rdf_mapping.typing triples kinds a s fuel = rdf_mapping.all_disjoint_properties triples kinds a s fuel := by
  simp only [owlAllDisjointProperties] at h
  rw [rdf_mapping.typing]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val, h,
    rdf_mapping.declares, rdf_mapping.declaration_kind]

theorem typing_all_different (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : objectView t.object = .iri owlAllDifferent) :
    rdf_mapping.typing triples kinds a s fuel = rdf_mapping.all_different triples a s fuel := by
  simp only [owlAllDifferent] at h
  rw [rdf_mapping.typing]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val, h,
    rdf_mapping.declares, rdf_mapping.declaration_kind]

theorem typing_negative (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (h : objectView t.object = .iri owlNegativePropertyAssertion) :
    rdf_mapping.typing triples kinds a s fuel = rdf_mapping.negative_assertion triples kinds a s := by
  simp only [owlNegativePropertyAssertion] at h
  rw [rdf_mapping.typing]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val, h,
    rdf_mapping.declares, rdf_mapping.declaration_kind]

/-! ### Assertions and class assertions -/

theorem structural_false {iri : model.Iri} {kind : typing.EntityKind}
    (allowed : Rowl.Vocabulary.EntityAllowed iri kind)
    (property : kind = .ObjectProperty ∨ kind = .DataProperty ∨ kind = .AnnotationProperty) :
    rdf_mapping.structural iri.spelling = .ok false := by
  rw [rdf_mapping.structural]
  rcases allowed with free | builtin
  · simp [Rowl.Vocabulary.reserved_iri_total_correct, free]
  · simp only [Rowl.Vocabulary.reserved_iri_total_correct, bind_ok, role_reserved builtin, decide_true, ↓reduceIte,
      Rowl.Builtins.builtin_kind_total_correct, builtin]
    rcases property with rfl | rfl | rfl <;> rfl

/-- The main triple of an assertion along an allowed property goes to `assertion`. -/
theorem read_axiom_assertion (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    {kind : typing.EntityKind} (allowed : Rowl.Vocabulary.EntityAllowed ⟨t.predicate.spelling⟩ kind)
    (property : kind = .ObjectProperty ∨ kind = .DataProperty ∨ kind = .AnnotationProperty) :
    rdf_mapping.read_axiom triples kinds a s fuel = rdf_mapping.assertion triples kinds a s := by
  have n1 := allowed_ne allowed (key := rdfType) (by simp [mappingVocabulary])
  have n2 := allowed_ne allowed (key := rdfsSubClassOf) (by simp [mappingVocabulary])
  have n3 := allowed_ne allowed (key := owlEquivalentClass) (by simp [mappingVocabulary])
  have n4 := allowed_ne allowed (key := owlDisjointWith) (by simp [mappingVocabulary])
  have n5 := allowed_ne allowed (key := owlDisjointUnionOf) (by simp [mappingVocabulary])
  have n6 := allowed_ne allowed (key := rdfsSubPropertyOf) (by simp [mappingVocabulary])
  have n7 := allowed_ne allowed (key := owlPropertyChainAxiom) (by simp [mappingVocabulary])
  have n8 := allowed_ne allowed (key := owlEquivalentProperty) (by simp [mappingVocabulary])
  have n9 := allowed_ne allowed (key := owlPropertyDisjointWith) (by simp [mappingVocabulary])
  have n10 := allowed_ne allowed (key := owlInverseOf) (by simp [mappingVocabulary])
  have n11 := allowed_ne allowed (key := rdfsDomain) (by simp [mappingVocabulary])
  have n12 := allowed_ne allowed (key := rdfsRange) (by simp [mappingVocabulary])
  have n13 := allowed_ne allowed (key := owlSameAs) (by simp [mappingVocabulary])
  have n14 := allowed_ne allowed (key := owlDifferentFrom) (by simp [mappingVocabulary])
  have n15 := allowed_ne allowed (key := owlHasKey) (by simp [mappingVocabulary])
  simp only [rdfType, rdfsSubClassOf, owlEquivalentClass, owlDisjointWith, owlDisjointUnionOf, rdfsSubPropertyOf,
    owlPropertyChainAxiom, owlEquivalentProperty] at n1 n2 n3 n4 n5 n6 n7 n8
  simp only [owlPropertyDisjointWith, owlInverseOf, rdfsDomain, rdfsRange, owlSameAs, owlDifferentFrom,
    owlHasKey] at n9 n10 n11 n12 n13 n14 n15
  have notStructural := structural_false allowed property
  rw [rdf_mapping.read_axiom]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, same_correct, array_slice_val, n1, n2,
    n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, notStructural]

/-- No typing triple of a class assertion has a type of the mapping as its class. -/
theorem typing_class_assertion (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a : Usize)
    (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple) (at_t : triples.val[a.val]? = some t)
    (notTyping : ∀ K ∈ mappingVocabulary, objectView t.object ≠ .iri K)
    (notReserved : rdf_mapping.reserved_object t.object = .ok false) :
    rdf_mapping.typing triples kinds a s fuel = rdf_mapping.class_assertion triples kinds a s fuel := by
  have n1 := notTyping owlRestriction (by simp [mappingVocabulary])
  have n2 := notTyping owlClass (by simp [mappingVocabulary])
  have n3 := notTyping rdfsDatatype (by simp [mappingVocabulary])
  have n4 := notTyping owlAxiom (by simp [mappingVocabulary])
  have n5 := notTyping owlAnnotation (by simp [mappingVocabulary])
  have n6 := notTyping owlObjectProperty (by simp [mappingVocabulary])
  have n7 := notTyping owlDatatypeProperty (by simp [mappingVocabulary])
  have n8 := notTyping owlAnnotationProperty (by simp [mappingVocabulary])
  have n9 := notTyping owlNamedIndividual (by simp [mappingVocabulary])
  have n10 := notTyping owlFunctionalProperty (by simp [mappingVocabulary])
  have n11 := notTyping owlInverseFunctionalProperty (by simp [mappingVocabulary])
  have n12 := notTyping owlReflexiveProperty (by simp [mappingVocabulary])
  have n13 := notTyping owlIrreflexiveProperty (by simp [mappingVocabulary])
  have n14 := notTyping owlSymmetricProperty (by simp [mappingVocabulary])
  have n15 := notTyping owlAsymmetricProperty (by simp [mappingVocabulary])
  have n16 := notTyping owlTransitiveProperty (by simp [mappingVocabulary])
  have n17 := notTyping owlAllDisjointClasses (by simp [mappingVocabulary])
  have n18 := notTyping owlAllDisjointProperties (by simp [mappingVocabulary])
  have n19 := notTyping owlAllDifferent (by simp [mappingVocabulary])
  have n20 := notTyping owlNegativePropertyAssertion (by simp [mappingVocabulary])
  simp only [owlRestriction, owlClass, rdfsDatatype, owlAxiom, owlAnnotation, owlObjectProperty, owlDatatypeProperty,
    owlAnnotationProperty, owlNamedIndividual, owlFunctionalProperty] at n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
  simp only [owlInverseFunctionalProperty, owlReflexiveProperty, owlIrreflexiveProperty, owlSymmetricProperty,
    owlAsymmetricProperty, owlTransitiveProperty, owlAllDisjointClasses, owlAllDisjointProperties, owlAllDifferent,
    owlNegativePropertyAssertion] at n11 n12 n13 n14 n15 n16 n17 n18 n19 n20
  rw [rdf_mapping.typing]
  simp [alloc.vec.Vec.index_slice_index, main_lookup triples a t at_t, lift, object_is_correct, array_slice_val, n1,
    n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, rdf_mapping.declares,
    rdf_mapping.declaration_kind, notReserved]

theorem reserved_object_allowed {o : rdf.Object} {c : model.Class}
    (allowed : Rowl.Vocabulary.EntityAllowed c.iri .Class) (view : objectView o = iriNode c.iri) :
    rdf_mapping.reserved_object o = .ok false := by
  cases o with
  | Iri r =>
    have same : r.spelling.val = c.iri.spelling.val := by simpa [objectView, iriNode] using view
    rw [rdf_mapping.reserved_object]
    rcases allowed with free | builtin
    · simp [Rowl.Vocabulary.reserved_iri_total_correct, same, free]
    · rcases role_class builtin with thing | nothing
      · simp only [owlThing] at thing
        simp [Rowl.Vocabulary.reserved_iri_total_correct, same, role_reserved builtin, lift, same_correct,
          array_slice_val, thing]
      · simp only [owlNothing] at nothing
        simp [Rowl.Vocabulary.reserved_iri_total_correct, same, role_reserved builtin, lift, same_correct,
          array_slice_val, nothing]
  | Blank _ => simp [objectView, iriNode] at view
  | Literal _ => simp [objectView, iriNode] at view

/-- The node of a class expression of an assertion is no type of the mapping. -/
theorem class_object_typing {c : model.ClassExpression} {s0 s1 : Supply} {n : Node} {ps : List Pattern}
    (tce : TCE c s0 n ps s1) (allowed : ∀ cl : model.Class, c = .Class cl → Rowl.Vocabulary.EntityAllowed cl.iri .Class)
    {o : rdf.Object} (view : objectView o = n) :
    (∀ K ∈ mappingVocabulary, objectView o ≠ .iri K) ∧ rdf_mapping.reserved_object o = .ok false := by
  rcases tce_node tce with ⟨cl, rfl, rfl⟩ | ⟨x, rfl⟩
  · refine ⟨fun K member same => ?_, reserved_object_allowed (allowed cl rfl) view⟩
    rw [view] at same
    simp only [iriNode, Node.iri.injEq] at same
    exact allowed_ne (allowed cl rfl) member same
  · refine ⟨fun K _ same => ?_, ?_⟩
    · rw [view] at same
      cases same
    · cases o with
      | Blank _ => simp [rdf_mapping.reserved_object]
      | Iri _ => simp [objectView] at view
      | Literal _ => simp [objectView] at view

/-! ### No annotations -/

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

theorem fits_annotation_false (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (used : alloc.vec.Vec Bool) (node : rdf.BlankNode)
    (noneLeft : ∀ (i : Nat) (t : rdf.Triple), triples.val[i]? = some t → used.val[i]? = some false →
      subjectView t.subject ≠ .blank node) (index : Usize) :
    rdf_mapping.fits_annotation triples kinds used index node = .ok false := by
  rw [rdf_mapping.fits_annotation]
  by_cases inside : index.val < triples.val.length
  · have at_t : triples.val[index.val]? = some triples.val[index.val] := List.getElem?_eq_getElem inside
    by_cases unused : used.val[index.val]? = some false
    · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, is_used_correct, unused, main_lookup triples index _ at_t,
        about_correct, noneLeft index.val _ at_t unused]
    · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, is_used_correct, unused]
  · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]

theorem find_annotation_in_none (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (used : alloc.vec.Vec Bool) (bucket : alloc.vec.Vec Usize) (node : rdf.BlankNode)
    (noneLeft : ∀ (i : Nat) (t : rdf.Triple), triples.val[i]? = some t → used.val[i]? = some false →
      subjectView t.subject ≠ .blank node) :
    ∀ k : Usize, rdf_mapping.find_annotation_in triples kinds used bucket node k = .ok none := by
  intro k
  induction e : bucket.val.length - k.val generalizing k with
  | zero =>
    have done : ¬ k.val < bucket.val.length := by omega
    rw [rdf_mapping.find_annotation_in]; simp [UScalar.lt_equiv, done]
  | succ n ih =>
    have more : k.val < bucket.val.length := by omega
    have lookup : bucket.index_usize k = .ok bucket.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := k) (y := 1#usize) (by have := bucket.property; scalar_tac))
    have nextIs : next.val = k.val + 1 := by simpa using nextValue
    rw [rdf_mapping.find_annotation_in]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
      bind_ok, fits_annotation_false triples kinds used node noneLeft, Bool.false_eq_true, advance]
    exact ih next (by omega)

theorem find_annotation_none (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (s : rdf_mapping.State)
    (node : rdf.BlankNode)
    (noneLeft : ∀ (i : Nat) (t : rdf.Triple), triples.val[i]? = some t → s.used.val[i]? = some false →
      subjectView t.subject ≠ .blank node) :
    rdf_mapping.find_annotation triples kinds s node = .ok none := by
  obtain ⟨h, hashRun⟩ := hash_blank_ok node
  obtain ⟨bucket, bucketRun, -⟩ := bucket_of_spec h (alloc.vec.Vec.len s.subjects)
  rw [rdf_mapping.find_annotation]
  simp only [hashRun, bucketRun, bind_ok]
  by_cases inside : bucket.val < s.subjects.val.length
  · have lookup : s.subjects.index_usize bucket = .ok s.subjects.val[bucket.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
      bind_ok]
    exact find_annotation_in_none triples kinds s.used _ node noneLeft 0#usize
  · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]

/-- An axiom that a blank node represents, with no triple about that node left,
    reads without annotations. -/
theorem annotate_blank (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (index : Usize)
    (ax : model.Axiom) (s : rdf_mapping.State) (fuel : Usize) (shape : rdf_mapping.main_triples ax = .ok 0#u8)
    (t : rdf.Triple) (at_t : triples.val[index.val]? = some t) (x : rdf.BlankNode) (subject : t.subject = .Blank x)
    (noneLeft : ∀ (i : Nat) (t' : rdf.Triple), triples.val[i]? = some t' → s.used.val[i]? = some false →
      subjectView t'.subject ≠ .blank x) :
    rdf_mapping.annotate triples kinds index ax s fuel = .ok (some (⟨alloc.vec.Vec.new _, ax⟩, s)) := by
  have nodeRun : rdf_mapping.node_annotations triples kinds x s (alloc.vec.Vec.new _) fuel =
      .ok (some (alloc.vec.Vec.new _, s)) := by
    rw [rdf_mapping.node_annotations]
    simp only [find_annotation_none triples kinds s x noneLeft, bind_ok]
  rw [rdf_mapping.annotate]
  simp only [shape, bind_ok, ↓reduceIte, alloc.vec.Vec.index_slice_index, main_lookup triples index t at_t, subject,
    nodeRun, uncurry_apply_pair]

/-! ### Reading a block -/

/-- `read_axiom` reads `ax` from the first position of its block, using exactly
    the positions of the block and recording exactly its blank nodes, and
    `annotate` adds no annotations. -/
def BlockReads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (ax : model.Axiom) (s0 : Supply)
    (ps : List Pattern) (s1 : Supply) : Prop :=
  ∀ (fresh : Supply), s0 = fresh ++ s1 → fresh.Nodup →
  ∀ (s : rdf_mapping.State) (a : Usize) (pos : List Nat), Ready triples s (a.val :: pos) ps fresh →
    (∀ b ∈ s.sources.val, b.val = []) →
    ∃ s', rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found ax s') ∧
      rdf_mapping.annotate triples kinds a ax s' (alloc.vec.Vec.len triples) =
        .ok (some (⟨alloc.vec.Vec.new _, ax⟩, s')) ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh

theorem finish_plain {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds} {ax : model.Axiom}
    {s s' : rdf_mapping.State} {a : Usize} {pos : List Nat} {ps : List Pattern} {fresh : Supply}
    (ready : Ready triples s (a.val :: pos) ps fresh) (empty : ∀ b ∈ s.sources.val, b.val = [])
    (shape : rdf_mapping.main_triples ax = .ok 1#u8)
    (read : rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found ax s'))
    (marked : Marked s s' (fun i => i ∈ a.val :: pos) fresh) :
    ∃ s', rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found ax s') ∧
      rdf_mapping.annotate triples kinds a ax s' (alloc.vec.Vec.len triples) =
        .ok (some (⟨alloc.vec.Vec.new _, ax⟩, s')) ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  have inside : a.val < triples.val.length := by
    cases ps with
    | nil => have := at_length ready.holds; simp at this
    | cons p rest =>
      obtain ⟨t, at_t, -, -⟩ := ready_main ready
      exact (List.getElem?_eq_some_iff.mp at_t).1
  exact ⟨s', read, annotate_plain triples kinds a ax s' _ shape inside (by rw [marked.sources]; exact empty), marked⟩

theorem finish_blank {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds} {ax : model.Axiom}
    {s s' : rdf_mapping.State} {a : Usize} {pos : List Nat} {x : rdf.BlankNode} {T : List U8}
    {rest : List Pattern} {fresh : Supply}
    (ready : Ready triples s (a.val :: pos) (⟨.blank x, rdfType, .iri T⟩ :: rest) fresh) (inFresh : x ∈ fresh)
    (shape : rdf_mapping.main_triples ax = .ok 0#u8)
    (read : rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found ax s'))
    (marked : Marked s s' (fun i => i ∈ a.val :: pos) fresh) :
    ∃ s', rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found ax s') ∧
      rdf_mapping.annotate triples kinds a ax s' (alloc.vec.Vec.len triples) =
        .ok (some (⟨alloc.vec.Vec.new _, ax⟩, s')) ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  have noneLeft : ∀ (i : Nat) (t' : rdf.Triple), triples.val[i]? = some t' → s'.used.val[i]? = some false →
      subjectView t'.subject ≠ .blank x := by
    intro i t' at_i unused about
    have before := marked_back marked unused
    have member := ready.owns i t' x at_i before about inFresh
    have inside : i < s.used.val.length := (List.getElem?_eq_some_iff.mp before).1
    rw [marked_used marked inside member] at unused
    cases unused
  exact ⟨s', read, annotate_blank triples kinds a ax s' _ shape t at_t x (subject_blank fits.1) noneLeft, marked⟩

/-! ### The axioms that the reverse mapping reads back -/

/-- The axioms that the reverse mapping reads back exactly from the triples of
    their forward mapping: every axiom whose class expressions, data ranges and
    literals are readable, except three forms whose triples the reader takes for
    other axioms. Equivalences and equalities of three or more members are
    written as several pairwise triples and read back as pairwise axioms; an
    inverse-property axiom whose first member is an inverse is written about a
    blank node, which the reader takes for an inverse property expression; and an
    object property assertion on an inverse is written as an assertion on the
    property itself. The datatype of a datatype definition is declared or built
    in as a datatype, since the reader tells a datatype definition from an
    equivalence of classes by the kind of its subject. -/
inductive AxiomReadable (axioms : List model.AnnotatedAxiom) : model.Axiom → Prop
  | declaration (e : model.Entity) : AxiomReadable axioms (.Declaration e)
  | subClassOf (c1 c2 : model.ClassExpression) : ClassReadable c1 → ClassReadable c2 →
      AxiomReadable axioms (.SubClassOf c1 c2)
  | equivalentClasses (xs : model.AtLeastTwo model.ClassExpression) : xs.rest.val = [] →
      ClassesReadable (members2 xs) → AxiomReadable axioms (.EquivalentClasses xs)
  | disjointClasses (xs : model.AtLeastTwo model.ClassExpression) : ClassesReadable (members2 xs) →
      AxiomReadable axioms (.DisjointClasses xs)
  | disjointUnion (c : model.Class) (xs : model.AtLeastTwo model.ClassExpression) :
      ClassesReadable (members2 xs) → AxiomReadable axioms (.DisjointUnion c xs)
  | subObjectProperty (sub : model.SubObjectPropertyExpression) (sup : model.ObjectPropertyExpression) :
      AxiomReadable axioms (.SubObjectPropertyOf sub sup)
  | equivalentObjectProperties (xs : model.AtLeastTwo model.ObjectPropertyExpression) : xs.rest.val = [] →
      AxiomReadable axioms (.EquivalentObjectProperties xs)
  | disjointObjectProperties (xs : model.AtLeastTwo model.ObjectPropertyExpression) :
      AxiomReadable axioms (.DisjointObjectProperties xs)
  | inverseProperties (p : model.ObjectProperty) (q : model.ObjectPropertyExpression) :
      AxiomReadable axioms (.InverseObjectProperties (.Property p) q)
  | objectDomain (role : model.ObjectPropertyExpression) (c : model.ClassExpression) : ClassReadable c →
      AxiomReadable axioms (.ObjectPropertyDomain role c)
  | objectRange (role : model.ObjectPropertyExpression) (c : model.ClassExpression) : ClassReadable c →
      AxiomReadable axioms (.ObjectPropertyRange role c)
  | functional (role : model.ObjectPropertyExpression) : AxiomReadable axioms (.FunctionalObjectProperty role)
  | inverseFunctional (role : model.ObjectPropertyExpression) :
      AxiomReadable axioms (.InverseFunctionalObjectProperty role)
  | reflexive (role : model.ObjectPropertyExpression) : AxiomReadable axioms (.ReflexiveObjectProperty role)
  | irreflexive (role : model.ObjectPropertyExpression) : AxiomReadable axioms (.IrreflexiveObjectProperty role)
  | symmetric (role : model.ObjectPropertyExpression) : AxiomReadable axioms (.SymmetricObjectProperty role)
  | asymmetric (role : model.ObjectPropertyExpression) : AxiomReadable axioms (.AsymmetricObjectProperty role)
  | transitive (role : model.ObjectPropertyExpression) : AxiomReadable axioms (.TransitiveObjectProperty role)
  | subDataProperty (d1 d2 : model.DataProperty) : AxiomReadable axioms (.SubDataPropertyOf d1 d2)
  | equivalentDataProperties (xs : model.AtLeastTwo model.DataProperty) : xs.rest.val = [] →
      AxiomReadable axioms (.EquivalentDataProperties xs)
  | disjointDataProperties (xs : model.AtLeastTwo model.DataProperty) :
      AxiomReadable axioms (.DisjointDataProperties xs)
  | dataDomain (d : model.DataProperty) (c : model.ClassExpression) : ClassReadable c →
      AxiomReadable axioms (.DataPropertyDomain d c)
  | dataRange (d : model.DataProperty) (r : model.DataRange) : RangeReadable r →
      AxiomReadable axioms (.DataPropertyRange d r)
  | functionalData (d : model.DataProperty) : AxiomReadable axioms (.FunctionalDataProperty d)
  | datatypeDefinition (d : model.Datatype) (r : model.DataRange) : RangeReadable r →
      Typed axioms d.iri .Datatype → AxiomReadable axioms (.DatatypeDefinition d r)
  | hasKey (c : model.ClassExpression) (objects : alloc.vec.Vec model.ObjectPropertyExpression)
      (datas : alloc.vec.Vec model.DataProperty) : ClassReadable c → AxiomReadable axioms (.HasKey c objects datas)
  | sameIndividual (xs : model.AtLeastTwo model.Individual) : xs.rest.val = [] →
      AxiomReadable axioms (.SameIndividual xs)
  | differentIndividuals (xs : model.AtLeastTwo model.Individual) : AxiomReadable axioms (.DifferentIndividuals xs)
  | classAssertion (c : model.ClassExpression) (a : model.Individual) : ClassReadable c →
      AxiomReadable axioms (.ClassAssertion c a)
  | objectAssertion (p : model.ObjectProperty) (a b : model.Individual) :
      AxiomReadable axioms (.ObjectPropertyAssertion (.Property p) a b)
  | negativeObject (role : model.ObjectPropertyExpression) (a b : model.Individual) :
      AxiomReadable axioms (.NegativeObjectPropertyAssertion role a b)
  | dataAssertion (d : model.DataProperty) (a : model.Individual) (v : model.Literal) : LiteralReadable v →
      AxiomReadable axioms (.DataPropertyAssertion d a v)
  | negativeData (d : model.DataProperty) (a : model.Individual) (v : model.Literal) : LiteralReadable v →
      AxiomReadable axioms (.NegativeDataPropertyAssertion d a v)
  | annotationAssertion (p : model.AnnotationProperty) (subject : model.AnnotationSubject)
      (value : model.AnnotationValue) : (∀ v, value = .Literal v → LiteralReadable v) →
      AxiomReadable axioms (.AnnotationAssertion p subject value)
  | subAnnotationProperty (p1 p2 : model.AnnotationProperty) : AxiomReadable axioms (.SubAnnotationPropertyOf p1 p2)
  | annotationDomain (p : model.AnnotationProperty) (iri : model.Iri) :
      AxiomReadable axioms (.AnnotationPropertyDomain p iri)
  | annotationRange (p : model.AnnotationProperty) (iri : model.Iri) :
      AxiomReadable axioms (.AnnotationPropertyRange p iri)

/-! ### Helpers for the members of axioms -/

theorem tces_two {c1 c2 : model.ClassExpression} {s0 s2 : Supply} {ns : List Node} {ps : List Pattern}
    (h : TCEs [c1, c2] s0 ns ps s2) :
    ∃ (s1 : Supply) (n1 n2 : Node) (p1 p2 : List Pattern), ns = [n1, n2] ∧ ps = p1 ++ p2 ∧
      TCE c1 s0 n1 p1 s1 ∧ TCE c2 s1 n2 p2 s2 := by
  cases h with
  | cons _ _ _ s1 _ n1 ns' p1 q h1 rest =>
    cases rest with
    | cons _ _ _ s1' _ n2 ns'' p2 q' h2 rest' =>
      cases rest'
      exact ⟨s1, n1, n2, p1, p2, rfl, by simp, h1, h2⟩

theorem members_two {α : Type} {xs : model.AtLeastTwo α} (empty : xs.rest.val = []) :
    members2 xs = [xs.first, xs.second] := by
  simp [members2, empty]

theorem classes_readable_two {c1 c2 : model.ClassExpression} (h : ClassesReadable [c1, c2]) :
    ClassReadable c1 ∧ ClassReadable c2 := by
  cases h with
  | cons _ _ r1 rest =>
    cases rest with
    | cons _ _ r2 _ => exact ⟨r1, r2⟩

theorem rows_sub {P : model.Iri × typing.EntityKind → Prop} {rows rows' : List (model.Iri × typing.EntityKind)}
    (h : ∀ row ∈ rows, P row) (sub : ∀ row ∈ rows', row ∈ rows) : ∀ row ∈ rows', P row :=
  fun row member => h row (sub row member)

theorem flat_map_sub {α : Type} {f : α → List (model.Iri × typing.EntityKind)} {l : List α} {x : α}
    (member : x ∈ l) : ∀ row ∈ f x, row ∈ l.flatMap f :=
  fun _ m => List.mem_flatMap.mpr ⟨x, member, m⟩

theorem uses_flat {kinds : rdf_mapping.Kinds} {α : Type} {f : α → List (model.Iri × typing.EntityKind)} {l : List α}
    (h : UsesTyped kinds (l.flatMap f)) : ∀ x ∈ l, UsesTyped kinds (f x) :=
  fun _ member => rows_sub h (flat_map_sub member)

theorem elements_members {α : Type} (xs : model.AtLeastTwo α) : xs.elements = members2 xs := rfl

theorem len_new_not_pos (T : Type) : ¬ ((0#usize : Usize) < alloc.vec.Vec.len (alloc.vec.Vec.new T)) := by
  simp [UScalar.lt_equiv, alloc.vec.Vec.len_val]

theorem len_empty_not_pos {T : Type} {v : alloc.vec.Vec T} (empty : v.val = []) :
    ¬ ((0#usize : Usize) < alloc.vec.Vec.len v) := by
  simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, empty]

theorem len_many_pos {T : Type} {v : alloc.vec.Vec T} (many : v.val ≠ []) :
    (0#usize : Usize) < alloc.vec.Vec.len v := by
  have h : 0 < v.val.length := List.length_pos_iff.mpr many
  simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]
  simpa using h

theorem fresh_of_cons {x : rdf.BlankNode} {cells f s fresh : Supply} (split : x :: (cells ++ (f ++ s)) = fresh ++ s) :
    fresh = x :: (cells ++ f) := by
  have h : (x :: (cells ++ f)) ++ s = fresh ++ s := by simpa using split
  exact (List.append_cancel_right h).symm

theorem allowed_property {row : model.Iri × typing.EntityKind} {rows : List (model.Iri × typing.EntityKind)}
    (allowed : ∀ r ∈ rows, Rowl.Vocabulary.EntityAllowed r.1 r.2) (member : row ∈ rows) {t : rdf.Triple}
    (spelling : t.predicate.spelling = row.1.spelling) :
    Rowl.Vocabulary.EntityAllowed ⟨t.predicate.spelling⟩ row.2 := by
  have h := allowed row member
  rw [spelling]
  exact h

theorem fresh_cons_self {x : rdf.BlankNode} {cells S fresh : Supply} (h : x :: (cells ++ S) = fresh ++ S) :
    fresh = x :: cells := by
  have h' : (x :: cells) ++ S = fresh ++ S := by simpa using h
  exact (List.append_cancel_right h').symm

theorem fresh_cons_tail {x : rdf.BlankNode} {f S fresh : Supply} (h : x :: (f ++ S) = fresh ++ S) :
    fresh = x :: f := by
  have h' : (x :: f) ++ S = fresh ++ S := by simpa using h
  exact (List.append_cancel_right h').symm

theorem fresh_single {x : rdf.BlankNode} {S fresh : Supply} (h : x :: S = fresh ++ S) : fresh = [x] := by
  have h' : [x] ++ S = fresh ++ S := by simpa using h
  exact (List.append_cancel_right h').symm

/-! ### Every readable axiom is read back -/

theorem fuel_rest {triples : alloc.vec.Vec rdf.Triple} {p : Pattern} {ps : List Pattern}
    (h : (p :: ps).length ≤ (alloc.vec.Vec.len triples).val) : ps.length ≤ (alloc.vec.Vec.len triples).val := by
  simp only [List.length_cons] at h; omega

theorem fuel_cells {triples : alloc.vec.Vec rdf.Triple} {cells : List rdf.BlankNode} {nodes : List Node}
    {ps : List Pattern} (lengths : cells.length = nodes.length)
    (h : ((listOf cells nodes).2 ++ ps).length ≤ (alloc.vec.Vec.len triples).val) :
    cells.length ≤ (alloc.vec.Vec.len triples).val := by
  rw [List.length_append, list_of_length cells nodes lengths] at h; omega

/-- How `annotate` treats an axiom read from the triple at `a`: an axiom with
    one main triple, or an axiom that a blank node of its block represents. -/
def ShapeOk (triples : alloc.vec.Vec rdf.Triple) (a : Usize) (ax : model.Axiom) (fresh : Supply) : Prop :=
  (rdf_mapping.main_triples ax = .ok 1#u8 ∧ a.val < triples.val.length) ∨
    (rdf_mapping.main_triples ax = .ok 0#u8 ∧
      ∃ (t : rdf.Triple) (x : rdf.BlankNode), triples.val[a.val]? = some t ∧ t.subject = .Blank x ∧ x ∈ fresh)

/-- `read_axiom` reads `ax` from the first position of its block, using exactly
    the positions of the block and recording exactly its blank nodes, whatever
    the source index holds. -/
def BlockReadsCore (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (ax : model.Axiom)
    (s0 : Supply) (ps : List Pattern) (s1 : Supply) : Prop :=
  ∀ (fresh : Supply), s0 = fresh ++ s1 → fresh.Nodup →
  ∀ (s : rdf_mapping.State) (a : Usize) (pos : List Nat), Ready triples s (a.val :: pos) ps fresh →
    ∃ s', rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found ax s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh ∧ ShapeOk triples a ax fresh

theorem core_plain {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds} {ax : model.Axiom}
    {s s' : rdf_mapping.State} {a : Usize} {pos : List Nat} {ps : List Pattern} {fresh : Supply}
    (ready : Ready triples s (a.val :: pos) ps fresh) (shape : rdf_mapping.main_triples ax = .ok 1#u8)
    (read : rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found ax s'))
    (marked : Marked s s' (fun i => i ∈ a.val :: pos) fresh) :
    ∃ s', rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found ax s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh ∧ ShapeOk triples a ax fresh := by
  have inside : a.val < triples.val.length := by
    cases ps with
    | nil => have := at_length ready.holds; simp at this
    | cons p rest =>
      obtain ⟨t, at_t, -, -⟩ := ready_main ready
      exact (List.getElem?_eq_some_iff.mp at_t).1
  exact ⟨s', read, marked, Or.inl ⟨shape, inside⟩⟩

theorem core_blank {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds} {ax : model.Axiom}
    {s s' : rdf_mapping.State} {a : Usize} {pos : List Nat} {x : rdf.BlankNode} {T : List U8}
    {rest : List Pattern} {fresh : Supply}
    (ready : Ready triples s (a.val :: pos) (⟨.blank x, rdfType, .iri T⟩ :: rest) fresh) (inFresh : x ∈ fresh)
    (shape : rdf_mapping.main_triples ax = .ok 0#u8)
    (read : rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found ax s'))
    (marked : Marked s s' (fun i => i ∈ a.val :: pos) fresh) :
    ∃ s', rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found ax s') ∧
      Marked s s' (fun i => i ∈ a.val :: pos) fresh ∧ ShapeOk triples a ax fresh := by
  obtain ⟨t, at_t, fits, -⟩ := ready_main ready
  exact ⟨s', read, marked, Or.inr ⟨shape, t, x, at_t, subject_blank fits.1, inFresh⟩⟩

/-- **Every readable axiom is read back from the triples of its forward
    mapping.** For an axiom that the reverse mapping reads back, whose IRIs the
    ontology types and allows, `read_axiom` reads it from the first position of
    its block, using exactly the positions of the block and recording exactly
    its blank nodes in order, whatever the source index holds. -/
theorem axiom_reads_core (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    {axioms : List model.AnnotatedAxiom} (hk : KindsOf kinds axioms) {ax : model.Axiom} {s0 : Supply}
    {ps : List Pattern} {s1 : Supply} (tax : TAxiom ax s0 ps s1) (readable : AxiomReadable axioms ax)
    (allowed : ∀ row ∈ Rowl.Collection.axiomUses ax, Rowl.Vocabulary.EntityAllowed row.1 row.2)
    (typed : ∀ row ∈ Rowl.Collection.axiomUses ax, KindTyped axioms row.1 row.2)
    (notReifier : ∀ p sub v, ax = .AnnotationAssertion p sub v → ∀ x, annotationSubjectNode sub = .blank x →
      ∀ (i : Nat) (t : rdf.Triple), triples.val[i]? = some t → subjectView t.subject = .blank x →
      t.predicate.spelling.val = rdfType → ∀ K ∈ reifierTypes, objectView t.object ≠ .iri K) :
    BlockReadsCore triples kinds ax s0 ps s1 := by
  intro fresh split nodup st a pos ready
  have fuelOk := fuel_of_ready ready
  have usesTyped : UsesTyped kinds (Rowl.Collection.axiomUses ax) := uses_typed_of hk typed
  cases readable with
  | declaration e =>
    cases tax with
    | declaration =>
      have none : fresh = [] := by simpa using split
      subst none
      obtain ⟨s', run, marked⟩ := declaration_complete triples kinds e st a pos ready _
      exact core_plain ready (by simp [rdf_mapping.main_triples]) run marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | subClassOf c1 c2 r1 r2 =>
    cases tax with
    | subClassOf _ _ _ _ _ n1 n2 p1 p2 tce1 tce2 =>
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨u1, u2⟩ := uses_typed_append.mp usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := sub_class_complete triples kinds tce1 tce2 (class_reads triples kinds tce1 r1 u1)
        (class_reads triples kinds tce2 r2 u2) split nodup st a pos ready _ (fuel_rest fuelOk)
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_sub_class triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | equivalentClasses xs emptyRest members =>
    cases tax with
    | equivalentClasses _ _ _ nodes eps tces =>
      rw [members_two emptyRest] at tces members
      obtain ⟨sMid, n1, n2, p1, p2, rfl, rfl, tce1, tce2⟩ := tces_two tces
      obtain ⟨r1, r2⟩ := classes_readable_two members
      simp only [Rowl.Collection.axiomUses, elements_members, members_two emptyRest] at usesTyped typed
      have u1 := uses_flat usesTyped xs.first (by simp)
      have u2 := uses_flat usesTyped xs.second (by simp)
      have ready' : Ready triples st (a.val :: pos) (⟨n1, owlEquivalentClass, n2⟩ :: (p1 ++ p2)) fresh := by
        simpa [chainOf] using ready
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready'
      have classTyped : ∀ cl : model.Class, xs.first = .Class cl → ¬ Typed axioms cl.iri .Datatype := by
        intro cl isClass
        exact typed (cl.iri, .Class) (by simp [isClass, Rowl.Collection.classUses])
      obtain ⟨s', run, marked⟩ := equivalent_classes_complete triples kinds hk tce1 tce2
        (class_reads triples kinds tce1 r1 u1) (class_reads triples kinds tce2 r2 u2) classTyped split nodup st a pos
        ready' _ (fuel_rest (fuel_of_ready ready'))
      rw [two_ext emptyRest] at run
      exact core_plain ready (by simp [rdf_mapping.main_triples, len_empty_not_pos emptyRest])
        (by rw [read_axiom_equivalent_class triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | disjointClasses xs members =>
    simp only [Rowl.Collection.axiomUses, elements_members] at usesTyped
    have uMembers := uses_flat usesTyped
    cases tax with
    | disjointClasses c1 c2 _ _ _ n1 n2 p1 p2 tce1 tce2 =>
      have members' : ClassesReadable [c1, c2] := by simpa [members2] using members
      obtain ⟨r1, r2⟩ := classes_readable_two members'
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := disjoint_classes_complete triples kinds tce1 tce2
        (class_reads triples kinds tce1 r1 (uMembers c1 (by simp [members2])))
        (class_reads triples kinds tce2 r2 (uMembers c2 (by simp [members2]))) split nodup st a pos ready _
        (fuel_rest fuelOk)
      exact core_plain ready (by simp [rdf_mapping.main_triples, len_new_not_pos])
        (by rw [read_axiom_disjoint_class triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | allDisjointClasses _ x cells _ _ nodes eps many cellsLen tces =>
      obtain ⟨f, eqf, -⟩ := tces_fresh tces
      have inFresh : x ∈ fresh := by
        rw [eqf] at split
        rw [fresh_of_cons split]
        simp
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s'', run, marked⟩ := all_disjoint_classes_complete triples kinds xs x cells _ _ nodes eps many cellsLen
        (classes_read triples kinds tces members uMembers) split nodup st a pos ready _ (fuel_rest (fuel_rest fuelOk))
      exact core_blank ready inFresh (by simp [rdf_mapping.main_triples, len_many_pos many])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1,
            typing_all_disjoint_classes triples kinds a st _ t at_t fits.2.2]
          exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | disjointUnion c xs members =>
    cases tax with
    | disjointUnion _ _ cells _ _ nodes eps cellsLen tces =>
      simp only [Rowl.Collection.axiomUses, elements_members] at usesTyped
      have uMembers : ∀ x ∈ members2 xs, UsesTyped kinds (Rowl.Collection.classUses x) :=
        uses_flat (rows_sub usesTyped (fun row m => List.mem_cons_of_mem _ m))
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s'', run, marked⟩ := disjoint_union_complete triples kinds c xs cells _ _ nodes eps cellsLen
        (classes_read triples kinds tces members uMembers) split nodup st a pos ready _ (fuel_rest fuelOk)
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_disjoint_union triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | subObjectProperty sub sup =>
    cases tax with
    | subObjectProperty e1 e2 _ _ _ n1 n2 p1 p2 tope1 tope2 =>
      simp only [Rowl.Collection.axiomUses, Rowl.Collection.subObjectUses] at usesTyped
      obtain ⟨u1, -⟩ := uses_typed_append.mp usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := sub_object_property_complete triples kinds tope1 tope2 u1 split nodup st a pos ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_sub_property triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | propertyChain chain _ cells _ _ _ n nodes p eps topeSup cellsLen topes =>
      simp only [Rowl.Collection.axiomUses, Rowl.Collection.subObjectUses, elements_members] at usesTyped
      obtain ⟨uChain, -⟩ := uses_typed_append.mp usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      have lengths : cells.length = nodes.length := by rw [cellsLen, ← topes_length topes]
      have cellsFuel : cells.length ≤ (alloc.vec.Vec.len triples).val := by
        have h := fuel_rest fuelOk
        rw [List.length_append, List.length_append, list_of_length cells nodes lengths] at h
        omega
      obtain ⟨s4, run, marked⟩ := property_chain_complete triples kinds chain _ cells _ _ _ n nodes p eps topeSup
        cellsLen topes (uses_flat uChain) split nodup st a pos ready _ cellsFuel
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_property_chain triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | equivalentObjectProperties xs emptyRest =>
    cases tax with
    | equivalentObjectProperties _ _ _ nodes eps topes =>
      rw [members_two emptyRest] at topes
      obtain ⟨sMid, n1, n2, p1, p2, rfl, rfl, tope1, tope2⟩ := topes_two topes
      simp only [Rowl.Collection.axiomUses, elements_members, members_two emptyRest] at usesTyped
      have ready' : Ready triples st (a.val :: pos) (⟨n1, owlEquivalentProperty, n2⟩ :: (p1 ++ p2)) fresh := by
        simpa [chainOf] using ready
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready'
      obtain ⟨s', run, marked⟩ := equivalent_object_properties_complete triples kinds tope1 tope2
        (uses_flat usesTyped xs.first (by simp)) split nodup st a pos ready'
      rw [two_ext emptyRest] at run
      exact core_plain ready (by simp [rdf_mapping.main_triples, len_empty_not_pos emptyRest])
        (by rw [read_axiom_equivalent_property triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | disjointObjectProperties xs =>
    simp only [Rowl.Collection.axiomUses, elements_members] at usesTyped
    have uMembers := uses_flat usesTyped
    cases tax with
    | disjointObjectProperties e1 e2 _ _ _ n1 n2 q1 q2 tope1 tope2 =>
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := disjoint_object_properties_complete triples kinds tope1 tope2
        (uMembers e1 (by simp [members2])) split nodup st a pos ready
      exact core_plain ready (by simp [rdf_mapping.main_triples, len_new_not_pos])
        (by rw [read_axiom_disjoint_property triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | allDisjointObjectProperties _ x cells _ _ nodes eps many cellsLen topes =>
      obtain ⟨f, eqf, -⟩ := topes_fresh topes
      have inFresh : x ∈ fresh := by
        rw [eqf] at split
        rw [fresh_of_cons split]
        simp
      have lengths : cells.length = nodes.length := by rw [cellsLen, ← topes_length topes]
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s'', run, marked⟩ := all_disjoint_object_properties_complete triples kinds xs x cells _ _ nodes eps
        many cellsLen topes uMembers split nodup st a pos ready _ (fuel_cells lengths (fuel_rest (fuel_rest fuelOk)))
      exact core_blank ready inFresh (by simp [rdf_mapping.main_triples, len_many_pos many])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1,
            typing_all_disjoint_properties triples kinds a st _ t at_t fits.2.2]
          exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | inverseProperties p q =>
    cases tax with
    | inverseProperties _ _ _ _ _ n1 n2 q1 q2 tope1 tope2 =>
      cases tope1
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := inverse_properties_complete triples p tope2 split nodup st a pos ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_inverse_properties triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | objectDomain role c r =>
    cases tax with
    | objectDomain _ _ _ _ _ n1 n2 p1 p2 tope tce =>
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨u1, u2⟩ := uses_typed_append.mp usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := object_domain_range_complete triples kinds false tope tce u1
        (class_reads triples kinds tce r u2) split nodup st a pos _ ready _ (fuel_rest fuelOk)
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_domain triples kinds a st _ t at_t fits.2.1]; simpa using run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | objectRange role c r =>
    cases tax with
    | objectRange _ _ _ _ _ n1 n2 p1 p2 tope tce =>
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨u1, u2⟩ := uses_typed_append.mp usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := object_domain_range_complete triples kinds true tope tce u1
        (class_reads triples kinds tce r u2) split nodup st a pos _ ready _ (fuel_rest fuelOk)
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_range triples kinds a st _ t at_t fits.2.1]; simpa using run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | functional role =>
    cases tax with
    | characteristic _ role' kind _ _ n p ct tope =>
      simp only [characteristicType, Option.some.injEq, Prod.mk.injEq] at ct
      obtain ⟨rfl, rfl⟩ := ct
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := characteristic_complete triples kinds (.FunctionalObjectProperty role) 0#u8 tope usesTyped
        (fun _ => by simp) split st a pos _ ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1, typing_functional triples kinds a st _ t at_t fits.2.2]
          exact run) marked
  | inverseFunctional role =>
    cases tax with
    | characteristic _ role' kind _ _ n p ct tope =>
      simp only [characteristicType, Option.some.injEq, Prod.mk.injEq] at ct
      obtain ⟨rfl, rfl⟩ := ct
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := characteristic_complete triples kinds (.InverseFunctionalObjectProperty role) 1#u8 tope usesTyped
        (fun _ => by simp) split st a pos _ ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1,
            typing_inverse_functional triples kinds a st _ t at_t fits.2.2]
          exact run) marked
  | reflexive role =>
    cases tax with
    | characteristic _ role' kind _ _ n p ct tope =>
      simp only [characteristicType, Option.some.injEq, Prod.mk.injEq] at ct
      obtain ⟨rfl, rfl⟩ := ct
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := characteristic_complete triples kinds (.ReflexiveObjectProperty role) 2#u8 tope usesTyped
        (fun _ => by simp) split st a pos _ ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1, typing_reflexive triples kinds a st _ t at_t fits.2.2]
          exact run) marked
  | irreflexive role =>
    cases tax with
    | characteristic _ role' kind _ _ n p ct tope =>
      simp only [characteristicType, Option.some.injEq, Prod.mk.injEq] at ct
      obtain ⟨rfl, rfl⟩ := ct
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := characteristic_complete triples kinds (.IrreflexiveObjectProperty role) 3#u8 tope usesTyped
        (fun _ => by simp) split st a pos _ ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1,
            typing_irreflexive triples kinds a st _ t at_t fits.2.2]
          exact run) marked
  | symmetric role =>
    cases tax with
    | characteristic _ role' kind _ _ n p ct tope =>
      simp only [characteristicType, Option.some.injEq, Prod.mk.injEq] at ct
      obtain ⟨rfl, rfl⟩ := ct
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := characteristic_complete triples kinds (.SymmetricObjectProperty role) 4#u8 tope usesTyped
        (fun _ => by simp) split st a pos _ ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1, typing_symmetric triples kinds a st _ t at_t fits.2.2]
          exact run) marked
  | asymmetric role =>
    cases tax with
    | characteristic _ role' kind _ _ n p ct tope =>
      simp only [characteristicType, Option.some.injEq, Prod.mk.injEq] at ct
      obtain ⟨rfl, rfl⟩ := ct
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := characteristic_complete triples kinds (.AsymmetricObjectProperty role) 5#u8 tope usesTyped
        (fun _ => by simp) split st a pos _ ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1,
            typing_asymmetric triples kinds a st _ t at_t fits.2.2]
          exact run) marked
  | transitive role =>
    cases tax with
    | characteristic _ role' kind _ _ n p ct tope =>
      simp only [characteristicType, Option.some.injEq, Prod.mk.injEq] at ct
      obtain ⟨rfl, rfl⟩ := ct
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := characteristic_complete triples kinds (.TransitiveObjectProperty role) 6#u8 tope usesTyped
        (fun _ => by simp) split st a pos _ ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1,
            typing_transitive triples kinds a st _ t at_t fits.2.2]
          exact run) marked
  | subDataProperty d1 d2 =>
    cases tax with
    | subDataProperty _ _ _ =>
      have none : fresh = [] := by simpa using split
      subst none
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨u1, -⟩ := uses_typed_append.mp usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := sub_data_property_complete triples kinds d1 d2 u1 st a pos ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_sub_property triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | equivalentDataProperties xs emptyRest =>
    cases tax with
    | equivalentDataProperties _ _ =>
      have none : fresh = [] := by simpa using split
      subst none
      simp only [Rowl.Collection.axiomUses, elements_members, members_two emptyRest] at usesTyped
      have ready' : Ready triples st (a.val :: pos)
          [⟨iriNode xs.first.iri, owlEquivalentProperty, iriNode xs.second.iri⟩] [] := by
        simpa [chainOf, members_two emptyRest] using ready
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready'
      obtain ⟨s', run, marked⟩ := equivalent_data_properties_complete triples kinds xs.first xs.second
        (uses_flat usesTyped xs.first (by simp)) st a pos ready'
      rw [two_ext emptyRest] at run
      exact core_plain ready (by simp [rdf_mapping.main_triples, len_empty_not_pos emptyRest])
        (by rw [read_axiom_equivalent_property triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | disjointDataProperties xs =>
    simp only [Rowl.Collection.axiomUses, elements_members] at usesTyped
    have uMembers := uses_flat usesTyped
    cases tax with
    | disjointDataProperties d1 d2 _ =>
      have none : fresh = [] := by simpa using split
      subst none
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := disjoint_data_properties_complete triples kinds d1 d2
        (uMembers d1 (by simp [members2])) st a pos ready
      exact core_plain ready (by simp [rdf_mapping.main_triples, len_new_not_pos])
        (by rw [read_axiom_disjoint_property triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | allDisjointDataProperties _ x cells _ many cellsLen =>
      have inFresh : x ∈ fresh := by
        rw [fresh_cons_self split]
        simp
      have lengths : cells.length = ((members2 xs).map (iriNode ·.iri)).length := by rw [cellsLen, List.length_map]
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s'', run, marked⟩ := all_disjoint_data_properties_complete triples kinds xs x cells _ many cellsLen
        uMembers split nodup st a pos ready _
        (fuel_cells (ps := []) lengths (by simpa using fuel_rest (fuel_rest fuelOk)))
      exact core_blank ready inFresh (by simp [rdf_mapping.main_triples, len_many_pos many])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1,
            typing_all_disjoint_properties triples kinds a st _ t at_t fits.2.2]
          exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | dataDomain d c r =>
    cases tax with
    | dataDomain _ _ _ _ n p tce =>
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨u1, u2⟩ := uses_typed_append.mp usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := data_domain_complete triples kinds d u1 (class_reads triples kinds tce r u2) split
        nodup st a pos ready _ (fuel_rest fuelOk)
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_domain triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | dataRange d r readableRange =>
    cases tax with
    | dataRange _ _ _ _ n p tdr =>
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨u1, -⟩ := uses_typed_append.mp usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := data_range_complete triples kinds d u1 (range_reads triples kinds tdr readableRange)
        split nodup st a pos ready _ (fuel_rest fuelOk)
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_range triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | functionalData d =>
    cases tax with
    | functionalData _ _ =>
      have none : fresh = [] := by simpa using split
      subst none
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := functional_data_complete triples kinds d usesTyped st a pos ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1, typing_functional triples kinds a st _ t at_t fits.2.2]
          exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | datatypeDefinition d r readableRange declared =>
    cases tax with
    | datatypeDefinition _ _ _ _ n p tdr =>
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := datatype_definition_complete triples kinds hk d
        (range_reads triples kinds tdr readableRange) declared split nodup st a pos ready _ (fuel_rest fuelOk)
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_equivalent_class triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | hasKey c objects datas r =>
    cases tax with
    | hasKey _ _ _ cells _ _ _ n nodes p eps tce cellsLen topes =>
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨uCO, uD⟩ := uses_typed_append.mp usesTyped
      obtain ⟨uC, uO⟩ := uses_typed_append.mp uCO
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      have lengths : cells.length = (nodes ++ datas.val.map (iriNode ·.iri)).length := by
        rw [cellsLen, List.length_append, List.length_map, ← topes_length topes]
      have restFuel := fuel_rest fuelOk
      rw [List.length_append, List.length_append, list_of_length cells _ lengths] at restFuel
      obtain ⟨s4, run, marked⟩ := has_key_complete triples kinds c objects datas cells _ _ _ n nodes p eps tce
        (class_reads triples kinds tce r uC) cellsLen topes (uses_flat uO) (uses_flat uD) split nodup st a pos ready
        (alloc.vec.Vec.len triples) (by omega) (by omega)
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_has_key triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | sameIndividual xs emptyRest =>
    cases tax with
    | sameIndividual _ _ =>
      have none : fresh = [] := by simpa using split
      subst none
      have ready' : Ready triples st (a.val :: pos)
          [⟨individualNode xs.first, owlSameAs, individualNode xs.second⟩] [] := by
        simpa [chainOf, members_two emptyRest] using ready
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready'
      obtain ⟨s', run, marked⟩ := same_individual_complete triples xs.first xs.second st a pos ready'
      rw [two_ext emptyRest] at run
      exact core_plain ready (by simp [rdf_mapping.main_triples, len_empty_not_pos emptyRest])
        (by rw [read_axiom_same_individual triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | differentIndividuals xs =>
    cases tax with
    | differentIndividuals i1 i2 _ =>
      have none : fresh = [] := by simpa using split
      subst none
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s', run, marked⟩ := different_individuals_complete triples i1 i2 st a pos ready
      exact core_plain ready (by simp [rdf_mapping.main_triples, len_new_not_pos])
        (by rw [read_axiom_different_individuals triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | allDifferent _ x cells _ many cellsLen =>
      have inFresh : x ∈ fresh := by
        rw [fresh_cons_self split]
        simp
      have lengths : cells.length = ((members2 xs).map individualNode).length := by rw [cellsLen, List.length_map]
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s'', run, marked⟩ := all_different_complete triples xs x cells _ many cellsLen split nodup st a pos
        ready _ (fuel_cells (ps := []) lengths (by simpa using fuel_rest (fuel_rest fuelOk)))
      exact core_blank ready inFresh (by simp [rdf_mapping.main_triples, len_many_pos many])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1,
            typing_all_different triples kinds a st _ t at_t fits.2.2]
          exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | classAssertion c individual r =>
    cases tax with
    | classAssertion _ _ _ _ n p tce =>
      simp only [Rowl.Collection.axiomUses] at usesTyped allowed
      obtain ⟨uC, -⟩ := uses_typed_append.mp usesTyped
      have allowedClass : ∀ cl : model.Class, c = .Class cl → Rowl.Vocabulary.EntityAllowed cl.iri .Class := by
        intro cl isClass
        exact allowed (cl.iri, .Class) (by simp [isClass, Rowl.Collection.classUses])
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨notTyping, notReserved⟩ := class_object_typing tce allowedClass fits.2.2
      obtain ⟨s', run, marked⟩ := class_assertion_complete triples kinds individual
        (class_reads triples kinds tce r uC) split nodup st a pos ready _ (fuel_rest fuelOk)
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1,
            typing_class_assertion triples kinds a st _ t at_t notTyping notReserved]
          exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | objectAssertion p i1 i2 =>
    cases tax with
    | objectAssertion _ _ _ _ =>
      have none : fresh = [] := by simpa using split
      subst none
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      have member : (p.iri, typing.EntityKind.ObjectProperty) ∈ Rowl.Collection.axiomUses
          (.ObjectPropertyAssertion (.Property p) i1 i2) := by
        simp [Rowl.Collection.axiomUses, Rowl.Collection.objectUses]
      obtain ⟨s', run, marked⟩ := object_assertion_complete triples kinds p i1 i2
        (property_kind_object hk (typed _ member)) st a pos ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_assertion triples kinds a st _ t at_t
            (allowed_property allowed member (predicate_spelling fits.2.1)) (Or.inl rfl)]
          exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | negativeObject role i1 i2 =>
    cases tax with
    | negativeObject _ _ _ x _ _ n p tope =>
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨uRA, -⟩ := uses_typed_append.mp usesTyped
      obtain ⟨uR, -⟩ := uses_typed_append.mp uRA
      obtain ⟨f, eqf, -⟩ := tope_fresh tope
      have inFresh : x ∈ fresh := by
        rw [eqf] at split
        rw [fresh_cons_tail split]
        simp
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s'', run, marked⟩ := negative_object_assertion_complete triples kinds role i1 i2 x tope uR split nodup st
        a pos ready
      exact core_blank ready inFresh (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1, typing_negative triples kinds a st _ t at_t fits.2.2]
          exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | dataAssertion d individual v readableValue =>
    cases tax with
    | dataAssertion _ _ _ _ n literal =>
      have none : fresh = [] := by simpa using split
      subst none
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      have member : (d.iri, typing.EntityKind.DataProperty) ∈ Rowl.Collection.axiomUses
          (.DataPropertyAssertion d individual v) := by
        simp [Rowl.Collection.axiomUses, Rowl.Collection.dataUses]
      obtain ⟨s', run, marked⟩ := data_assertion_complete triples kinds d individual v n literal readableValue
        (property_kind_data hk (typed _ member)) st a pos ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_assertion triples kinds a st _ t at_t
            (allowed_property allowed member (predicate_spelling fits.2.1)) (Or.inr (Or.inl rfl))]
          exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | negativeData d i1 v readableValue =>
    cases tax with
    | negativeData _ _ _ x _ n literal =>
      simp only [Rowl.Collection.axiomUses] at usesTyped
      obtain ⟨uDA, -⟩ := uses_typed_append.mp usesTyped
      obtain ⟨uD, -⟩ := uses_typed_append.mp uDA
      have inFresh : x ∈ fresh := by
        rw [fresh_single split]
        simp
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      obtain ⟨s'', run, marked⟩ := negative_data_assertion_complete triples kinds d i1 v x _ n literal readableValue
        uD split nodup st a pos ready
      exact core_blank ready inFresh (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_typing triples kinds a st _ t at_t fits.2.1, typing_negative triples kinds a st _ t at_t fits.2.2]
          exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | annotationAssertion p sub value readableValue =>
    cases tax with
    | annotationAssertion _ _ _ _ n valueNode =>
      have none : fresh = [] := by simpa using split
      subst none
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      have member : (p.iri, typing.EntityKind.AnnotationProperty) ∈ Rowl.Collection.axiomUses
          (.AnnotationAssertion p sub value) := by
        simp [Rowl.Collection.axiomUses]
      obtain ⟨s', run, marked⟩ := annotation_assertion_complete triples kinds p sub value n valueNode readableValue
        (property_kind_annotation hk (typed _ member)) st a pos ready (notReifier p sub value rfl)
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by
          rw [read_axiom_assertion triples kinds a st _ t at_t
            (allowed_property allowed member (predicate_spelling fits.2.1)) (Or.inr (Or.inr rfl))]
          exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | subAnnotationProperty p1 p2 =>
    cases tax with
    | subAnnotationProperty _ _ _ =>
      have none : fresh = [] := by simpa using split
      subst none
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      have member : (p1.iri, typing.EntityKind.AnnotationProperty) ∈ Rowl.Collection.axiomUses
          (.SubAnnotationPropertyOf p1 p2) := by
        simp [Rowl.Collection.axiomUses]
      obtain ⟨s', run, marked⟩ := sub_annotation_property_complete triples kinds p1 p2
        (property_kind_annotation hk (typed _ member)) st a pos ready
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_sub_property triples kinds a st _ t at_t fits.2.1]; exact run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | annotationDomain p iri =>
    cases tax with
    | annotationDomain _ _ _ =>
      have none : fresh = [] := by simpa using split
      subst none
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      have member : (p.iri, typing.EntityKind.AnnotationProperty) ∈ Rowl.Collection.axiomUses
          (.AnnotationPropertyDomain p iri) := by
        simp [Rowl.Collection.axiomUses]
      obtain ⟨s', run, marked⟩ := annotation_domain_range_complete triples kinds false p iri
        (property_kind_annotation hk (typed _ member)) st a pos _ ready (alloc.vec.Vec.len triples)
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_domain triples kinds a st _ t at_t fits.2.1]; simpa using run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | annotationRange p iri =>
    cases tax with
    | annotationRange _ _ _ =>
      have none : fresh = [] := by simpa using split
      subst none
      obtain ⟨t, at_t, fits, -⟩ := ready_main ready
      have member : (p.iri, typing.EntityKind.AnnotationProperty) ∈ Rowl.Collection.axiomUses
          (.AnnotationPropertyRange p iri) := by
        simp [Rowl.Collection.axiomUses]
      obtain ⟨s', run, marked⟩ := annotation_domain_range_complete triples kinds true p iri
        (property_kind_annotation hk (typed _ member)) st a pos _ ready (alloc.vec.Vec.len triples)
      exact core_plain ready (by simp [rdf_mapping.main_triples])
        (by rw [read_axiom_range triples kinds a st _ t at_t fits.2.1]; simpa using run) marked
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct

/-- **Every readable axiom is read back from the triples of its forward
    mapping.** For an axiom that the reverse mapping reads back, whose IRIs the
    ontology types and allows, `read_axiom` reads it from the first position of
    its block, using exactly the positions of the block and recording exactly
    its blank nodes in order, and `annotate` adds no annotations. -/
theorem axiom_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    {axioms : List model.AnnotatedAxiom} (hk : KindsOf kinds axioms) {ax : model.Axiom} {s0 : Supply}
    {ps : List Pattern} {s1 : Supply} (tax : TAxiom ax s0 ps s1) (readable : AxiomReadable axioms ax)
    (allowed : ∀ row ∈ Rowl.Collection.axiomUses ax, Rowl.Vocabulary.EntityAllowed row.1 row.2)
    (typed : ∀ row ∈ Rowl.Collection.axiomUses ax, KindTyped axioms row.1 row.2)
    (notReifier : ∀ p sub v, ax = .AnnotationAssertion p sub v → ∀ x, annotationSubjectNode sub = .blank x →
      ∀ (i : Nat) (t : rdf.Triple), triples.val[i]? = some t → subjectView t.subject = .blank x →
      t.predicate.spelling.val = rdfType → ∀ K ∈ reifierTypes, objectView t.object ≠ .iri K) :
    BlockReads triples kinds ax s0 ps s1 := by
  intro fresh split nodup st a pos ready empty
  obtain ⟨s', read, marked, shape⟩ := axiom_reads_core triples kinds hk tax readable allowed typed notReifier fresh
    split nodup st a pos ready
  rcases shape with ⟨shape, inside⟩ | ⟨shape, t, x, at_t, subject, inFresh⟩
  · exact ⟨s', read, annotate_plain triples kinds a ax s' _ shape inside (by rw [marked.sources]; exact empty),
      marked⟩
  · have noneLeft : ∀ (i : Nat) (t' : rdf.Triple), triples.val[i]? = some t' → s'.used.val[i]? = some false →
        subjectView t'.subject ≠ .blank x := by
      intro i t' at_i unused about
      have before := marked_back marked unused
      have member := ready.owns i t' x at_i before about inFresh
      have inside : i < st.used.val.length := (List.getElem?_eq_some_iff.mp before).1
      rw [marked_used marked inside member] at unused
      cases unused
    exact ⟨s', read, annotate_blank triples kinds a ax s' _ shape t at_t x subject noneLeft, marked⟩

end Rowl.RdfReadAxioms
