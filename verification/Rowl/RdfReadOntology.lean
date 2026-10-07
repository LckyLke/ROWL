import Rowl.RdfReadAxioms

/-!
# Completeness of the reverse RDF mapping

For every ontology whose forward mapping the reverse mapping reads back
(`ReadableOntology`: the reserved-vocabulary and typing conditions of OWL 2 DL,
no ontology annotations, unannotated readable axioms, and no annotation
assertion about the ontology IRI), a graph that lists the triples of its forward
mapping (`TOntology` of `RdfMapping.lean`) in order, with blank nodes distinct
from each other and from the anonymous individuals the assertions are about, is
mapped by `map_graph` to exactly that ontology with exactly those blank nodes
(`map_graph_complete`).
-/

namespace Rowl.RdfReadOntology
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust Rowl.RdfMapping Rowl.RdfReadIndexes Rowl.RdfReadExpressions
  Rowl.RdfReadAxioms
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-! ### The ontologies the reverse mapping reads back -/

/-- The anonymous individual that the main triple of an assertion is about. -/
def subjectAnonymous : model.Axiom → Option model.AnonymousIndividual
  | .ClassAssertion _ (.Anonymous a) => some a
  | .ObjectPropertyAssertion _ (.Anonymous a) _ => some a
  | .DataPropertyAssertion _ (.Anonymous a) _ => some a
  | .SameIndividual xs => match xs.first with
    | .Anonymous a => some a
    | .Named _ => none
  | .DifferentIndividuals xs => match xs.first with
    | .Anonymous a => some a
    | .Named _ => none
  | .AnnotationAssertion _ (.Anonymous a) _ => some a
  | _ => none

/-- The ontologies whose forward mapping the reverse mapping reads back exactly:
    those that satisfy the reserved-vocabulary condition of OWL 2 DL
    (`VocabularyOK`) and the typing constraints the reverse mapping relies on
    (`KindTyped`: every property is declared or built in as one kind of property
    only, and no class is a datatype), without ontology annotations, whose axioms
    are unannotated and readable (`AxiomReadable`), and none of whose annotation
    assertions is about the ontology IRI (the reverse mapping reads such a triple
    as an ontology annotation). -/
structure ReadableOntology (o : model.RawOntology) : Prop where
  vocabulary : Rowl.Vocabulary.VocabularyOK o
  typed : ∀ row ∈ Rowl.Vocabulary.ontologyUses o, KindTyped o.axioms.val row.1 row.2
  annotations : o.annotations.val = []
  axioms : ∀ ax ∈ o.axioms.val, ax.annotations.val = [] ∧ AxiomReadable o.axioms.val ax.axiom
  apart : ∀ iri version, o.identity = .Named iri version → ∀ ax ∈ o.axioms.val, ∀ p v,
    ax.axiom ≠ .AnnotationAssertion p (.Iri iri) v

/-- The blank nodes the forward mapping allocates are distinct from the
    anonymous individuals the assertions are about. -/
def FreshSupply (o : model.RawOntology) (supply : Supply) : Prop :=
  ∀ ax ∈ o.axioms.val, ∀ an, subjectAnonymous ax.axiom = some an → (⟨an.scope, an.label⟩ : rdf.BlankNode) ∉ supply

theorem readable_uses {o : model.RawOntology} (readable : ReadableOntology o) {ax : model.AnnotatedAxiom}
    (member : ax ∈ o.axioms.val) :
    (∀ row ∈ Rowl.Collection.axiomUses ax.axiom, Rowl.Vocabulary.EntityAllowed row.1 row.2) ∧
      ∀ row ∈ Rowl.Collection.axiomUses ax.axiom, KindTyped o.axioms.val row.1 row.2 := by
  have sub : ∀ row ∈ Rowl.Collection.axiomUses ax.axiom, row ∈ Rowl.Vocabulary.ontologyUses o := by
    intro row m
    simp only [Rowl.Vocabulary.ontologyUses]
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨ax, member, by simp [Rowl.Collection.annotatedUses, m]⟩
  exact ⟨fun row m => readable.vocabulary.2 row (sub row m), fun row m => readable.typed row (sub row m)⟩

/-! ### The triples of expressions and lists -/

/-- The predicates of the triples of expressions, lists and the nodes of axioms
    that blank nodes represent, other than their typing triples. -/
def sideVocabulary : List (List U8) :=
  [rdfFirst, rdfRest, owlOnProperty, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlHasSelf,
    owlMinCardinality, owlMaxCardinality, owlCardinality, owlMinQualifiedCardinality, owlMaxQualifiedCardinality,
    owlQualifiedCardinality, owlOnClass, owlOnDataRange, owlIntersectionOf, owlUnionOf, owlComplementOf, owlOneOf,
    owlDatatypeComplementOf, owlOnDatatype, owlWithRestrictions, owlMembers, owlSourceIndividual,
    owlAssertionProperty, owlTargetIndividual, owlTargetValue]

/-- A triple of an expression or a list: its predicate is one of
    `sideVocabulary`, a facet of OWL 2 or `owl:inverseOf`, or it types its blank
    node as a restriction, class or datatype. -/
def SideKind (q : Pattern) : Prop :=
  q.predicate ∈ sideVocabulary ∨ q.predicate ∈ owl2Facets ∨ q.predicate = owlInverseOf ∨
    (q.predicate = rdfType ∧ (q.object = .iri owlRestriction ∨ q.object = .iri owlClass ∨
      q.object = .iri rdfsDatatype))

theorem side_nil : ∀ q ∈ ([] : List Pattern), SideKind q := by
  intro q member; simp at member

theorem side_cons {p : Pattern} {ps : List Pattern} (head : SideKind p) (tail : ∀ q ∈ ps, SideKind q) :
    ∀ q ∈ p :: ps, SideKind q := by
  intro q member
  rcases List.mem_cons.mp member with rfl | inner
  · exact head
  · exact tail q inner

theorem side_append {ps qs : List Pattern} (h1 : ∀ q ∈ ps, SideKind q) (h2 : ∀ q ∈ qs, SideKind q) :
    ∀ q ∈ ps ++ qs, SideKind q := by
  intro q member
  rcases List.mem_append.mp member with left | right
  · exact h1 q left
  · exact h2 q right

theorem side_key {x : rdf.BlankNode} {key : List U8} {value : Node} (member : key ∈ sideVocabulary) :
    SideKind ⟨.blank x, key, value⟩ := Or.inl member

theorem side_typed {x : rdf.BlankNode} {T : List U8}
    (which : T = owlRestriction ∨ T = owlClass ∨ T = rdfsDatatype) : SideKind ⟨.blank x, rdfType, .iri T⟩ := by
  refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
  rcases which with rfl | rfl | rfl <;> simp

theorem list_side : ∀ (cells : List rdf.BlankNode) (elements : List Node), ∀ q ∈ (listOf cells elements).2, SideKind q
  | [], _ => by simp [listOf]
  | _ :: _, [] => by simp [listOf]
  | c :: cells, e :: elements => by
    simp only [listOf]
    exact side_cons (side_key (by simp [sideVocabulary])) (side_cons (side_key (by simp [sideVocabulary]))
      (list_side cells elements))

theorem tope_side {e : model.ObjectPropertyExpression} {s : Supply} {n : Node} {ps : List Pattern} {s' : Supply}
    (h : TOPE e s n ps s') : ∀ q ∈ ps, SideKind q := by
  cases h with
  | named => exact side_nil
  | inverse => exact side_cons (Or.inr (Or.inr (Or.inl rfl))) side_nil

theorem topes_side {es : List model.ObjectPropertyExpression} {s : Supply} {ns : List Node} {ps : List Pattern}
    {s' : Supply} (h : TOPEs es s ns ps s') : ∀ q ∈ ps, SideKind q := by
  induction h with
  | nil => exact side_nil
  | cons _ _ _ _ _ _ _ _ _ head _ ih => exact side_append (tope_side head) ih

theorem tfacets_side {fs : List model.FacetRestriction} {s : Supply} {ns : List Node} {ps : List Pattern}
    {s' : Supply} (h : TFacets fs s ns ps s') (facets : ∀ f ∈ fs, f.facet.spelling.val ∈ owl2Facets) :
    ∀ q ∈ ps, SideKind q := by
  induction h with
  | nil => exact side_nil
  | cons f fs y s s' value ns ps _ _ ih =>
    exact side_cons (Or.inr (Or.inl (facets f (by simp)))) (ih (fun g m => facets g (List.mem_cons_of_mem _ m)))

mutual
theorem tdr_side : ∀ {d : model.DataRange} {s : Supply} {n : Node} {ps : List Pattern} {s' : Supply},
    TDR d s n ps s' → RangeReadable d → ∀ q ∈ ps, SideKind q
  | _, _, _, _, _, .datatype _ _, _ => side_nil
  | _, _, _, _, _, .intersection _ _ _ _ _ _ _ _ inner, readable => by
    cases readable with
    | intersection _ members =>
      exact side_cons (side_typed (by simp)) (side_cons (side_key (by simp [sideVocabulary]))
        (side_append (list_side _ _) (tdrs_side inner members)))
  | _, _, _, _, _, .union _ _ _ _ _ _ _ _ inner, readable => by
    cases readable with
    | union _ members =>
      exact side_cons (side_typed (by simp)) (side_cons (side_key (by simp [sideVocabulary]))
        (side_append (list_side _ _) (tdrs_side inner members)))
  | _, _, _, _, _, .complement _ _ _ _ _ _ inner, readable => by
    cases readable with
    | complement _ innerReadable =>
      exact side_cons (side_typed (by simp)) (side_cons (side_key (by simp [sideVocabulary]))
        (tdr_side inner innerReadable))
  | _, _, _, _, _, .oneOf _ _ _ _ _ _ _, _ =>
    side_cons (side_typed (by simp)) (side_cons (side_key (by simp [sideVocabulary])) (list_side _ _))
  | _, _, _, _, _, .restriction _ _ _ _ _ _ _ _ _ facets, readable => by
    cases readable with
    | restriction _ _ facetsReadable =>
      exact side_cons (side_typed (by simp)) (side_cons (side_key (by simp [sideVocabulary]))
        (side_cons (side_key (by simp [sideVocabulary])) (side_append (list_side _ _)
          (tfacets_side facets (fun f m => (facetsReadable f m).2)))))

theorem tdrs_side : ∀ {ds : List model.DataRange} {s : Supply} {ns : List Node} {ps : List Pattern} {s' : Supply},
    TDRs ds s ns ps s' → RangesReadable ds → ∀ q ∈ ps, SideKind q
  | _, _, _, _, _, .nil _, _ => side_nil
  | _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ head tail, readable => by
    cases readable with
    | cons _ _ headReadable tailReadable =>
      exact side_append (tdr_side head headReadable) (tdrs_side tail tailReadable)
end

theorem restriction_head_side {x : rdf.BlankNode} {property : Node} {rest : List Pattern}
    (tail : ∀ q ∈ rest, SideKind q) : ∀ q ∈ restrictionHead x property ++ rest, SideKind q := by
  simp only [restrictionHead, List.cons_append, List.nil_append]
  exact side_cons (side_typed (by simp)) (side_cons (side_key (by simp [sideVocabulary])) tail)

mutual
theorem tce_side : ∀ {c : model.ClassExpression} {s : Supply} {n : Node} {ps : List Pattern} {s' : Supply},
    TCE c s n ps s' → ClassReadable c → ∀ q ∈ ps, SideKind q
  | _, _, _, _, _, .named _ _, _ => side_nil
  | _, _, _, _, _, .intersection _ _ _ _ _ _ _ _ inner, readable => by
    cases readable with
    | intersection _ members =>
      exact side_cons (side_typed (by simp)) (side_cons (side_key (by simp [sideVocabulary]))
        (side_append (list_side _ _) (tces_side inner members)))
  | _, _, _, _, _, .union _ _ _ _ _ _ _ _ inner, readable => by
    cases readable with
    | union _ members =>
      exact side_cons (side_typed (by simp)) (side_cons (side_key (by simp [sideVocabulary]))
        (side_append (list_side _ _) (tces_side inner members)))
  | _, _, _, _, _, .complement _ _ _ _ _ _ inner, readable => by
    cases readable with
    | complement _ innerReadable =>
      exact side_cons (side_typed (by simp)) (side_cons (side_key (by simp [sideVocabulary]))
        (tce_side inner innerReadable))
  | _, _, _, _, _, .oneOf _ _ _ _ _, _ =>
    side_cons (side_typed (by simp)) (side_cons (side_key (by simp [sideVocabulary])) (list_side _ _))
  | _, _, _, _, _, .some _ _ _ _ _ _ _ _ _ _ role inner, readable => by
    cases readable with
    | some _ _ innerReadable =>
      exact restriction_head_side (side_cons (side_key (by simp [sideVocabulary]))
        (side_append (tope_side role) (tce_side inner innerReadable)))
  | _, _, _, _, _, .all _ _ _ _ _ _ _ _ _ _ role inner, readable => by
    cases readable with
    | all _ _ innerReadable =>
      exact restriction_head_side (side_cons (side_key (by simp [sideVocabulary]))
        (side_append (tope_side role) (tce_side inner innerReadable)))
  | _, _, _, _, _, .hasValue _ _ _ _ _ _ _ role, _ =>
    restriction_head_side (side_cons (side_key (by simp [sideVocabulary])) (tope_side role))
  | _, _, _, _, _, .hasSelf _ _ _ _ _ _ role, _ =>
    restriction_head_side (side_cons (side_key (by simp [sideVocabulary])) (tope_side role))
  | _, _, _, _, _, .min _ _ _ _ _ _ _ _ role _, _ =>
    restriction_head_side (side_cons (side_key (by simp [sideVocabulary])) (tope_side role))
  | _, _, _, _, _, .max _ _ _ _ _ _ _ _ role _, _ =>
    restriction_head_side (side_cons (side_key (by simp [sideVocabulary])) (tope_side role))
  | _, _, _, _, _, .exact _ _ _ _ _ _ _ _ role _, _ =>
    restriction_head_side (side_cons (side_key (by simp [sideVocabulary])) (tope_side role))
  | _, _, _, _, _, .minQualified _ _ _ _ _ _ _ _ _ _ _ _ role _ inner, readable => by
    cases readable with
    | minQualified _ _ _ _ innerReadable =>
      exact restriction_head_side (side_cons (side_key (by simp [sideVocabulary]))
        (side_cons (side_key (by simp [sideVocabulary])) (side_append (tope_side role) (tce_side inner innerReadable))))
  | _, _, _, _, _, .maxQualified _ _ _ _ _ _ _ _ _ _ _ _ role _ inner, readable => by
    cases readable with
    | maxQualified _ _ _ _ innerReadable =>
      exact restriction_head_side (side_cons (side_key (by simp [sideVocabulary]))
        (side_cons (side_key (by simp [sideVocabulary])) (side_append (tope_side role) (tce_side inner innerReadable))))
  | _, _, _, _, _, .exactQualified _ _ _ _ _ _ _ _ _ _ _ _ role _ inner, readable => by
    cases readable with
    | exactQualified _ _ _ _ innerReadable =>
      exact restriction_head_side (side_cons (side_key (by simp [sideVocabulary]))
        (side_cons (side_key (by simp [sideVocabulary])) (side_append (tope_side role) (tce_side inner innerReadable))))
  | _, _, _, _, _, .dataSome _ _ _ _ _ _ _ inner, readable => by
    cases readable with
    | dataSome _ _ innerReadable =>
      exact restriction_head_side (side_cons (side_key (by simp [sideVocabulary])) (tdr_side inner innerReadable))
  | _, _, _, _, _, .dataAll _ _ _ _ _ _ _ inner, readable => by
    cases readable with
    | dataAll _ _ innerReadable =>
      exact restriction_head_side (side_cons (side_key (by simp [sideVocabulary])) (tdr_side inner innerReadable))
  | _, _, _, _, _, .dataHasValue _ _ _ _ _ _, _ =>
    restriction_head_side (side_cons (side_key (by simp [sideVocabulary])) side_nil)
  | _, _, _, _, _, .dataMin _ _ _ _ _ _, _ =>
    restriction_head_side (side_cons (side_key (by simp [sideVocabulary])) side_nil)
  | _, _, _, _, _, .dataMax _ _ _ _ _ _, _ =>
    restriction_head_side (side_cons (side_key (by simp [sideVocabulary])) side_nil)
  | _, _, _, _, _, .dataExact _ _ _ _ _ _, _ =>
    restriction_head_side (side_cons (side_key (by simp [sideVocabulary])) side_nil)
  | _, _, _, _, _, .dataMinQualified _ _ _ _ _ _ _ _ _ _ inner, readable => by
    cases readable with
    | dataMinQualified _ _ _ _ innerReadable =>
      exact restriction_head_side (side_cons (side_key (by simp [sideVocabulary]))
        (side_cons (side_key (by simp [sideVocabulary])) (tdr_side inner innerReadable)))
  | _, _, _, _, _, .dataMaxQualified _ _ _ _ _ _ _ _ _ _ inner, readable => by
    cases readable with
    | dataMaxQualified _ _ _ _ innerReadable =>
      exact restriction_head_side (side_cons (side_key (by simp [sideVocabulary]))
        (side_cons (side_key (by simp [sideVocabulary])) (tdr_side inner innerReadable)))
  | _, _, _, _, _, .dataExactQualified _ _ _ _ _ _ _ _ _ _ inner, readable => by
    cases readable with
    | dataExactQualified _ _ _ _ innerReadable =>
      exact restriction_head_side (side_cons (side_key (by simp [sideVocabulary]))
        (side_cons (side_key (by simp [sideVocabulary])) (tdr_side inner innerReadable)))

theorem tces_side : ∀ {cs : List model.ClassExpression} {s : Supply} {ns : List Node} {ps : List Pattern}
    {s' : Supply}, TCEs cs s ns ps s' → ClassesReadable cs → ∀ q ∈ ps, SideKind q
  | _, _, _, _, _, .nil _, _ => side_nil
  | _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ head tail, readable => by
    cases readable with
    | cons _ _ headReadable tailReadable =>
      exact side_append (tce_side head headReadable) (tces_side tail tailReadable)
end

/-! ### The main triples of axioms -/

/-- The types that declaration triples declare entities with. -/
def declarationTypes : List (List U8) :=
  [owlClass, rdfsDatatype, owlObjectProperty, owlDatatypeProperty, owlAnnotationProperty, owlNamedIndividual]

/-- An IRI that the ontology types as an annotation property and as no other
    property: the reader takes triples with it as their predicate for
    annotations. -/
def AnnotationOnly (axioms : List model.AnnotatedAxiom) (iri : model.Iri) : Prop :=
  Typed axioms iri .AnnotationProperty ∧ ¬ Typed axioms iri .ObjectProperty ∧ ¬ Typed axioms iri .DataProperty

/-- What the graph-level reasoning needs to know about the main triple of an
    axiom whose blank nodes are `fresh`. -/
structure MainFacts (o : model.RawOntology) (ax : model.Axiom) (fresh : Supply) (main : Pattern) : Prop where
  declares : main.predicate = rdfType → ∀ sp, main.subject = .iri sp → ∀ T ∈ declarationTypes,
    main.object = .iri T → ∃ e, ax = .Declaration e ∧ main = declarationPattern e
  notOntology : main.predicate = rdfType → ∀ sp, main.subject = .iri sp → main.object ≠ .iri owlOntology
  notSource : main.predicate ≠ owlAnnotatedSource
  header : ∀ iri version, o.identity = .Named iri version → main.subject = iriNode iri →
    main.predicate ≠ owlVersionIRI ∧ main.predicate ≠ owlImports ∧
      ∀ p : model.Iri, p.spelling.val = main.predicate → ¬ AnnotationOnly o.axioms.val p
  blank : ∀ y, main.subject = .blank y → y ∈ fresh ∨
    ∃ an, subjectAnonymous ax = some an ∧ y = ⟨an.scope, an.label⟩
  reifier : ∀ y, main.subject = .blank y → y ∉ fresh → main.predicate = rdfType →
    ∀ K ∈ reifierTypes, main.object ≠ .iri K

theorem entity_uses_of (kind : typing.EntityKind) (iri : model.Iri) :
    Rowl.Collection.entityUses (entityOf kind iri.spelling) = [(iri, kind)] := by
  cases kind <;> rfl

/-- The vocabulary of the mapping is typed as nothing. -/
theorem vocabulary_not_typed {o : model.RawOntology} (vocabulary : Rowl.Vocabulary.VocabularyOK o)
    {iri : model.Iri} {K : List U8} (member : K ∈ mappingVocabulary) (spelling : iri.spelling.val = K)
    (kind : typing.EntityKind) : ¬ Typed o.axioms.val iri kind := by
  rintro (⟨ax, axIn, isDecl⟩ | builtin)
  · have row : (iri, kind) ∈ Rowl.Vocabulary.ontologyUses o := by
      simp only [Rowl.Vocabulary.ontologyUses]
      apply List.mem_append_right
      refine List.mem_flatMap.mpr ⟨ax, axIn, ?_⟩
      simp [Rowl.Collection.annotatedUses, isDecl, Rowl.Collection.axiomUses, entity_uses_of]
    exact allowed_ne (vocabulary.2 _ row) member spelling
  · rw [spelling, (mapping_vocabulary_reserved K member).2] at builtin
    cases builtin

theorem vocabulary_not_annotation {o : model.RawOntology} (vocabulary : Rowl.Vocabulary.VocabularyOK o)
    {K : List U8} (member : K ∈ mappingVocabulary) :
    ∀ p : model.Iri, p.spelling.val = K → ¬ AnnotationOnly o.axioms.val p :=
  fun _ spelling annotationOnly => vocabulary_not_typed vocabulary member spelling _ annotationOnly.1

/-- The main triple of an axiom whose predicate is vocabulary of the mapping
    other than `rdf:type`. -/
theorem main_structural {o : model.RawOntology} (vocabulary : Rowl.Vocabulary.VocabularyOK o) {ax : model.Axiom}
    {fresh : Supply} {sub obj : Node} {K : List U8} (member : K ∈ mappingVocabulary) (notType : K ≠ rdfType)
    (notSource : K ≠ owlAnnotatedSource) (notVersion : K ≠ owlVersionIRI) (notImports : K ≠ owlImports)
    (blank : ∀ y, sub = .blank y → y ∈ fresh ∨ ∃ an, subjectAnonymous ax = some an ∧ y = ⟨an.scope, an.label⟩) :
    MainFacts o ax fresh ⟨sub, K, obj⟩ where
  declares := fun h => absurd h notType
  notOntology := fun h => absurd h notType
  notSource := notSource
  header := fun _ _ _ _ => ⟨notVersion, notImports, vocabulary_not_annotation vocabulary member⟩
  blank := blank
  reifier := fun _ _ _ h => absurd h notType

theorem iri_not_blank {iri : model.Iri} {fresh : Supply} {ax : model.Axiom} :
    ∀ y, iriNode iri = .blank y → y ∈ fresh ∨ ∃ an, subjectAnonymous ax = some an ∧ y = ⟨an.scope, an.label⟩ := by
  intro y h
  simp [iriNode] at h

theorem tce_node_subject {c : model.ClassExpression} {s : Supply} {n : Node} {ps : List Pattern} {s' : Supply}
    (h : TCE c s n ps s') {y : rdf.BlankNode} (hy : n = .blank y) : ∃ q ∈ ps, q.subject = .blank y := by
  cases h <;> simp only [iriNode, Node.blank.injEq, reduceCtorEq] at hy <;> subst hy <;>
    exact ⟨_, List.mem_cons_self .., rfl⟩

theorem tce_node_fresh {c : model.ClassExpression} {s : Supply} {n : Node} {ps : List Pattern} {s' : Supply}
    (h : TCE c s n ps s') {f : Supply} (split : s = f ++ s') {ax : model.Axiom} {fresh : Supply}
    (sub : ∀ y ∈ f, y ∈ fresh) :
    ∀ y, n = .blank y → y ∈ fresh ∨ ∃ an, subjectAnonymous ax = some an ∧ y = ⟨an.scope, an.label⟩ := by
  intro y hy
  obtain ⟨q, member, subject⟩ := tce_node_subject h hy
  obtain ⟨f', eq', sub'⟩ := tce_fresh h
  have same : f' = f := by
    rw [eq'] at split
    exact List.append_cancel_right split
  subst same
  obtain ⟨z, inside, about⟩ := sub' q member
  rw [subject] at about
  simp only [Node.blank.injEq] at about
  rw [about]
  exact Or.inl (sub z inside)

theorem tope_node_fresh {e : model.ObjectPropertyExpression} {s : Supply} {n : Node} {ps : List Pattern} {s' : Supply}
    (h : TOPE e s n ps s') {f : Supply} (split : s = f ++ s') {ax : model.Axiom} {fresh : Supply}
    (sub : ∀ y ∈ f, y ∈ fresh) :
    ∀ y, n = .blank y → y ∈ fresh ∨ ∃ an, subjectAnonymous ax = some an ∧ y = ⟨an.scope, an.label⟩ := by
  intro y hy
  cases h with
  | named => simp [iriNode] at hy
  | inverse p x =>
    simp only [Node.blank.injEq] at hy
    subst hy
    have same : f = [x] := by
      have h' : [x] ++ s' = f ++ s' := by simpa using split
      exact (List.append_cancel_right h').symm
    subst same
    exact Or.inl (sub x (by simp))

/-- The main triple of an axiom that a blank node represents. -/
theorem main_typed_fresh {o : model.RawOntology} {ax : model.Axiom} {fresh : Supply} {x : rdf.BlankNode}
    {T : List U8} (inFresh : x ∈ fresh) : MainFacts o ax fresh ⟨.blank x, rdfType, .iri T⟩ where
  declares := fun _ _ h => by cases h
  notOntology := fun _ _ h => by cases h
  notSource := by simp [rdfType, owlAnnotatedSource]
  header := fun _ _ _ h => by simp [iriNode] at h
  blank := fun y h => by cases h; exact Or.inl inFresh
  reifier := fun y h notIn => by cases h; exact absurd inFresh notIn

/-- The typing triple of a property characteristic. -/
theorem main_typed_property {o : model.RawOntology} (vocabulary : Rowl.Vocabulary.VocabularyOK o)
    {ax : model.Axiom} {fresh : Supply} {n : Node} {T : List U8} (notDeclaration : T ∉ declarationTypes)
    (notOntology : T ≠ owlOntology) (blank : ∀ y, n = .blank y → y ∈ fresh) :
    MainFacts o ax fresh ⟨n, rdfType, .iri T⟩ where
  declares := fun _ _ _ K member h => by
    simp only [Node.iri.injEq] at h
    subst h
    exact absurd member notDeclaration
  notOntology := fun _ _ _ h => by
    simp only [Node.iri.injEq] at h
    exact notOntology h
  notSource := by simp [rdfType, owlAnnotatedSource]
  header := fun _ _ _ _ => ⟨by simp [rdfType, owlVersionIRI], by simp [rdfType, owlImports],
    vocabulary_not_annotation vocabulary (by simp [mappingVocabulary])⟩
  blank := fun y h => Or.inl (blank y h)
  reifier := fun y h notIn => absurd (blank y h) notIn

/-- The typing triple of a declaration. -/
theorem main_declaration {o : model.RawOntology} (vocabulary : Rowl.Vocabulary.VocabularyOK o) (e : model.Entity)
    {fresh : Supply} : MainFacts o (.Declaration e) fresh (declarationPattern e) where
  declares := fun _ _ _ _ _ _ => ⟨e, rfl, rfl⟩
  notOntology := fun _ _ _ h => by
    cases e <;> simp [declarationPattern, owlOntology, owlClass, rdfsDatatype, owlObjectProperty,
      owlDatatypeProperty, owlAnnotationProperty, owlNamedIndividual] at h
  notSource := by cases e <;> simp [declarationPattern, rdfType, owlAnnotatedSource]
  header := fun _ _ _ _ => by
    have typed : (declarationPattern e).predicate = rdfType := by cases e <;> rfl
    rw [typed]
    exact ⟨by simp [rdfType, owlVersionIRI], by simp [rdfType, owlImports],
      vocabulary_not_annotation vocabulary (by simp [mappingVocabulary])⟩
  blank := fun y h => by cases e <;> simp [declarationPattern, iriNode] at h
  reifier := fun y h => by cases e <;> simp [declarationPattern, iriNode] at h

/-- The typing triple of a class assertion. -/
theorem main_class_assertion {o : model.RawOntology} (vocabulary : Rowl.Vocabulary.VocabularyOK o)
    {c : model.ClassExpression} {a : model.Individual} {s0 s1 : Supply} {n : Node} {p : List Pattern}
    (tce : TCE c s0 n p s1) (allowed : ∀ cl : model.Class, c = .Class cl → Rowl.Vocabulary.EntityAllowed cl.iri .Class)
    {fresh : Supply} (blankFresh : ∀ y, n = .blank y → y ∈ fresh) :
    MainFacts o (.ClassAssertion c a) fresh ⟨individualNode a, rdfType, n⟩ where
  declares := fun _ _ _ T member h => by
    exfalso
    rcases tce_node tce with ⟨cl, rfl, rfl⟩ | ⟨x, rfl⟩
    · simp only [iriNode, Node.iri.injEq] at h
      exact allowed_ne (allowed cl rfl) (by simp [declarationTypes] at member; rcases member with rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp [mappingVocabulary]) h
    · cases h
  notOntology := fun _ _ _ h => by
    rcases tce_node tce with ⟨cl, rfl, rfl⟩ | ⟨x, rfl⟩
    · simp only [iriNode, Node.iri.injEq] at h
      exact allowed_ne (allowed cl rfl) (by simp [mappingVocabulary]) h
    · cases h
  notSource := by simp [rdfType, owlAnnotatedSource]
  header := fun _ _ _ _ => ⟨by simp [rdfType, owlVersionIRI], by simp [rdfType, owlImports],
    vocabulary_not_annotation vocabulary (by simp [mappingVocabulary])⟩
  blank := fun y h => by
    cases a with
    | Named _ => simp [individualNode, iriNode] at h
    | Anonymous an =>
      simp only [individualNode, anonymousNode, Node.blank.injEq] at h
      exact Or.inr ⟨an, rfl, h.symm⟩
  reifier := fun _ _ _ _ K member same => by
    rcases tce_node tce with ⟨cl, rfl, rfl⟩ | ⟨x, rfl⟩
    · simp only [iriNode, Node.iri.injEq] at same
      exact allowed_ne (allowed cl rfl) (by
        simp [reifierTypes] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mappingVocabulary]) same
    · cases same

/-- The main triple of an assertion along an object or data property. -/
theorem main_assertion {o : model.RawOntology} {ax : model.Axiom} {fresh : Supply} {p : model.Iri}
    {kind : typing.EntityKind} (allowed : Rowl.Vocabulary.EntityAllowed p kind)
    (typed : Typed o.axioms.val p .ObjectProperty ∨ Typed o.axioms.val p .DataProperty) {a : model.Individual}
    (subjectIs : subjectAnonymous ax = match a with | .Anonymous an => some an | .Named _ => none) {obj : Node} :
    MainFacts o ax fresh ⟨individualNode a, p.spelling.val, obj⟩ where
  declares := fun h => absurd h (allowed_ne allowed (by simp [mappingVocabulary]))
  notOntology := fun h => absurd h (allowed_ne allowed (by simp [mappingVocabulary]))
  notSource := allowed_ne allowed (by simp [mappingVocabulary])
  header := fun _ _ _ _ => ⟨allowed_ne allowed (by simp [mappingVocabulary]),
    allowed_ne allowed (by simp [mappingVocabulary]), fun q spelling annotationOnly => by
      have same : q = p := iri_ext spelling
      subst same
      rcases typed with object | data
      · exact annotationOnly.2.1 object
      · exact annotationOnly.2.2 data⟩
  blank := fun y h => by
    cases a with
    | Named _ => simp [individualNode, iriNode] at h
    | Anonymous an =>
      simp only [individualNode, anonymousNode, Node.blank.injEq] at h
      exact Or.inr ⟨an, subjectIs, h.symm⟩
  reifier := fun _ _ _ h => absurd h (allowed_ne allowed (by simp [mappingVocabulary]))

/-- The main triple of an annotation assertion, not about the ontology IRI. -/
theorem main_annotation {o : model.RawOntology} {p : model.AnnotationProperty} {sub : model.AnnotationSubject}
    {value : model.AnnotationValue} {fresh : Supply}
    (allowed : Rowl.Vocabulary.EntityAllowed p.iri .AnnotationProperty)
    (apart : ∀ iri version, o.identity = .Named iri version → sub ≠ .Iri iri) {obj : Node} :
    MainFacts o (.AnnotationAssertion p sub value) fresh ⟨annotationSubjectNode sub, p.iri.spelling.val, obj⟩ where
  declares := fun h => absurd h (allowed_ne allowed (by simp [mappingVocabulary]))
  notOntology := fun h => absurd h (allowed_ne allowed (by simp [mappingVocabulary]))
  notSource := allowed_ne allowed (by simp [mappingVocabulary])
  header := fun iri version named h => by
    exfalso
    cases sub with
    | Iri iri' =>
      simp only [annotationSubjectNode, iriNode, Node.iri.injEq] at h
      exact apart iri version named (by rw [iri_ext h])
    | Anonymous _ => simp [annotationSubjectNode, anonymousNode, iriNode] at h
  blank := fun y h => by
    cases sub with
    | Iri _ => simp [annotationSubjectNode, iriNode] at h
    | Anonymous an =>
      simp only [annotationSubjectNode, anonymousNode, Node.blank.injEq] at h
      exact Or.inr ⟨an, rfl, h.symm⟩
  reifier := fun _ _ _ h => absurd h (allowed_ne allowed (by simp [mappingVocabulary]))

/-! ### The blocks of the axioms -/

/-- The predicates of main triples other than `rdf:type`. -/
def mainPredicates : List (List U8) :=
  [rdfsSubClassOf, owlEquivalentClass, owlDisjointWith, owlDisjointUnionOf, rdfsSubPropertyOf,
    owlPropertyChainAxiom, owlEquivalentProperty, owlPropertyDisjointWith, owlInverseOf, rdfsDomain, rdfsRange,
    owlSameAs, owlDifferentFrom, owlHasKey]

theorem main_predicates_facts : ∀ K ∈ mainPredicates, K ∈ mappingVocabulary ∧ K ≠ rdfType ∧
    K ≠ owlAnnotatedSource ∧ K ≠ owlVersionIRI ∧ K ≠ owlImports := by
  intro K h
  simp only [mainPredicates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨by simp [mappingVocabulary], ?_, ?_, ?_, ?_⟩ <;>
    simp [rdfsSubClassOf, owlEquivalentClass, owlDisjointWith, owlDisjointUnionOf, rdfsSubPropertyOf,
      owlPropertyChainAxiom, owlEquivalentProperty, owlPropertyDisjointWith, owlInverseOf, rdfsDomain, rdfsRange,
      owlSameAs, owlDifferentFrom, owlHasKey, rdfType, owlAnnotatedSource, owlVersionIRI, owlImports]

theorem main_special {o : model.RawOntology} (vocabulary : Rowl.Vocabulary.VocabularyOK o) {ax : model.Axiom}
    {fresh : Supply} {sub obj : Node} {K : List U8} (special : K ∈ mainPredicates)
    (blank : ∀ y, sub = .blank y → y ∈ fresh ∨ ∃ an, subjectAnonymous ax = some an ∧ y = ⟨an.scope, an.label⟩) :
    MainFacts o ax fresh ⟨sub, K, obj⟩ :=
  have facts := main_predicates_facts K special
  main_structural vocabulary facts.1 facts.2.1 facts.2.2.1 facts.2.2.2.1 facts.2.2.2.2 blank

/-- The triples of a block after its main triple: of expressions and lists,
    about blank nodes of the block. -/
def Sides (fresh : Supply) (ps : List Pattern) : Prop :=
  ∀ q ∈ ps, SideKind q ∧ ∃ y ∈ fresh, q.subject = .blank y

theorem sides_of {f : Supply} {ps : List Pattern} (kinds : ∀ q ∈ ps, SideKind q) (subjects : SubjectsIn f ps) :
    Sides f ps :=
  fun q m => ⟨kinds q m, subjects q m⟩

theorem sides_nil (f : Supply) : Sides f [] := fun q m => by simp at m

theorem subjects_sub {f g : Supply} {ps : List Pattern} (h : SubjectsIn f ps) (sub : ∀ y ∈ f, y ∈ g) :
    SubjectsIn g ps :=
  subjects_in_mono h sub

theorem fresh_two {s0 s1 s2 f1 f2 : Supply} (eq1 : s0 = f1 ++ s1) (eq2 : s1 = f2 ++ s2) : s0 = (f1 ++ f2) ++ s2 := by
  rw [eq1, eq2, List.append_assoc]

theorem characteristic_types {a : model.Axiom} {role : model.ObjectPropertyExpression} {kind : List U8}
    (ct : characteristicType a = some (role, kind)) :
    kind ∉ declarationTypes ∧ kind ≠ owlOntology ∧ subjectAnonymous a = none := by
  cases a <;> simp only [characteristicType, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at ct <;>
    obtain ⟨_, rfl⟩ := ct <;>
    refine ⟨?_, ?_, rfl⟩ <;>
    simp [declarationTypes, owlClass, rdfsDatatype, owlObjectProperty, owlDatatypeProperty, owlAnnotationProperty,
      owlNamedIndividual, owlFunctionalProperty, owlInverseFunctionalProperty, owlReflexiveProperty,
      owlIrreflexiveProperty, owlSymmetricProperty, owlAsymmetricProperty, owlTransitiveProperty, owlOntology]

theorem characteristic_shape {o : model.RawOntology} (vocab : Rowl.Vocabulary.VocabularyOK o) {a : model.Axiom}
    {role : model.ObjectPropertyExpression} {kind : List U8} (ct : characteristicType a = some (role, kind))
    {s0 s1 : Supply} {n : Node} {p : List Pattern} (tope : TOPE role s0 n p s1) :
    ∃ main side f, (⟨n, rdfType, .iri kind⟩ :: p : List Pattern) = main :: side ∧ s0 = f ++ s1 ∧ Sides f side ∧
      MainFacts o a f main := by
  obtain ⟨notDeclaration, notOntology, none⟩ := characteristic_types ct
  obtain ⟨f, eqf, subf⟩ := tope_fresh tope
  refine ⟨_, _, f, rfl, eqf, sides_of (tope_side tope) subf, main_typed_property vocab notDeclaration notOntology ?_⟩
  intro y h
  rcases tope_node_fresh (ax := a) tope eqf (fun z m => m) y h with inside | ⟨an, isSome, _⟩
  · exact inside
  · rw [none] at isSome
    cases isSome

/-- The facts about the block of a readable axiom: its main triple first, then
    triples of expressions and lists about its blank nodes. -/
theorem block_shape {o : model.RawOntology} (readable : ReadableOntology o) {ax : model.AnnotatedAxiom}
    (member : ax ∈ o.axioms.val) {s0 : Supply} {ps : List Pattern} {s1 : Supply} (tax : TAxiom ax.axiom s0 ps s1) :
    ∃ main side f, ps = main :: side ∧ s0 = f ++ s1 ∧ Sides f side ∧ MainFacts o ax.axiom f main := by
  have axReadable := (readable.axioms ax member).2
  obtain ⟨allowed, typed⟩ := readable_uses readable member
  have vocab := readable.vocabulary
  have apart : ∀ p sub v, ax.axiom = .AnnotationAssertion p sub v → ∀ iri version, o.identity = .Named iri version →
      sub ≠ .Iri iri := by
    intro p sub v isAnnotation iri version named same
    subst same
    exact readable.apart iri version named ax member p v isAnnotation
  generalize ax.axiom = a at axReadable allowed typed apart tax ⊢
  cases axReadable with
  | declaration e =>
    cases tax with
    | declaration => exact ⟨_, [], [], rfl, by simp, sides_nil _, main_declaration vocab e⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | subClassOf c1 c2 r1 r2 =>
    cases tax with
    | subClassOf _ _ _ _ _ n1 n2 p1 p2 tce1 tce2 =>
      obtain ⟨f1, eq1, sub1⟩ := tce_fresh tce1
      obtain ⟨f2, eq2, sub2⟩ := tce_fresh tce2
      exact ⟨_, _, f1 ++ f2, rfl, fresh_two eq1 eq2,
        sides_of (side_append (tce_side tce1 r1) (tce_side tce2 r2)) (subjects_pair sub1 sub2),
        main_special vocab (by simp [mainPredicates])
          (tce_node_fresh tce1 eq1 (fun y m => List.mem_append_left _ m))⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | equivalentClasses xs emptyRest members =>
    cases tax with
    | equivalentClasses _ _ _ nodes eps tces =>
      rw [members_two emptyRest] at tces members
      obtain ⟨sMid, n1, n2, p1, p2, rfl, rfl, tce1, tce2⟩ := tces_two tces
      obtain ⟨r1, r2⟩ := classes_readable_two members
      obtain ⟨f1, eq1, sub1⟩ := tce_fresh tce1
      obtain ⟨f2, eq2, sub2⟩ := tce_fresh tce2
      exact ⟨⟨n1, owlEquivalentClass, n2⟩, p1 ++ p2, f1 ++ f2, rfl, fresh_two eq1 eq2,
        sides_of (side_append (tce_side tce1 r1) (tce_side tce2 r2)) (subjects_pair sub1 sub2),
        main_special vocab (by simp [mainPredicates])
          (tce_node_fresh tce1 eq1 (fun y m => List.mem_append_left _ m))⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | disjointClasses xs members =>
    cases tax with
    | disjointClasses c1 c2 _ _ _ n1 n2 p1 p2 tce1 tce2 =>
      have members' : ClassesReadable [c1, c2] := by simpa [members2] using members
      obtain ⟨r1, r2⟩ := classes_readable_two members'
      obtain ⟨f1, eq1, sub1⟩ := tce_fresh tce1
      obtain ⟨f2, eq2, sub2⟩ := tce_fresh tce2
      exact ⟨_, _, f1 ++ f2, rfl, fresh_two eq1 eq2,
        sides_of (side_append (tce_side tce1 r1) (tce_side tce2 r2)) (subjects_pair sub1 sub2),
        main_special vocab (by simp [mainPredicates])
          (tce_node_fresh tce1 eq1 (fun y m => List.mem_append_left _ m))⟩
    | allDisjointClasses _ x cells _ _ nodes eps _ _ tces =>
      obtain ⟨f, eqf, subf⟩ := tces_fresh tces
      refine ⟨_, _, x :: (cells ++ f), rfl, by rw [eqf]; simp, ?_, main_typed_fresh (by simp)⟩
      refine sides_of (side_cons (side_key (by simp [sideVocabulary]))
        (side_append (list_side _ _) (tces_side tces members))) ?_
      exact subjects_cons rfl (subjects_widen (subjects_pair (list_of_subjects _ _) subf))
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | disjointUnion c xs members =>
    cases tax with
    | disjointUnion _ _ cells _ _ nodes eps _ tces =>
      obtain ⟨f, eqf, subf⟩ := tces_fresh tces
      exact ⟨_, _, cells ++ f, rfl, by rw [eqf]; simp,
        sides_of (side_append (list_side _ _) (tces_side tces members))
          (subjects_pair (list_of_subjects _ _) subf),
        main_special vocab (by simp [mainPredicates]) iri_not_blank⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | subObjectProperty sub sup =>
    cases tax with
    | subObjectProperty e1 e2 _ _ _ n1 n2 p1 p2 tope1 tope2 =>
      obtain ⟨f1, eq1, sub1⟩ := tope_fresh tope1
      obtain ⟨f2, eq2, sub2⟩ := tope_fresh tope2
      exact ⟨_, _, f1 ++ f2, rfl, fresh_two eq1 eq2,
        sides_of (side_append (tope_side tope1) (tope_side tope2)) (subjects_pair sub1 sub2),
        main_special vocab (by simp [mainPredicates])
          (tope_node_fresh tope1 eq1 (fun y m => List.mem_append_left _ m))⟩
    | propertyChain chain _ cells _ _ _ n nodes p eps topeSup _ topes =>
      obtain ⟨fS, eqS, subS⟩ := tope_fresh topeSup
      obtain ⟨fC, eqC, subC⟩ := topes_fresh topes
      refine ⟨_, _, fS ++ (cells ++ fC), rfl, by rw [eqS, eqC]; simp, ?_,
        main_special vocab (by simp [mainPredicates])
          (tope_node_fresh topeSup eqS (fun y m => List.mem_append_left _ m))⟩
      refine sides_of (side_append (side_append (list_side _ _) (tope_side topeSup)) (topes_side topes)) ?_
      refine subjects_in_append (subjects_in_append ?_ ?_) ?_
      · exact subjects_sub (list_of_subjects _ _) (fun y m => by simp [m])
      · exact subjects_sub subS (fun y m => by simp [m])
      · exact subjects_sub subC (fun y m => by simp [m])
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | equivalentObjectProperties xs emptyRest =>
    cases tax with
    | equivalentObjectProperties _ _ _ nodes eps topes =>
      rw [members_two emptyRest] at topes
      obtain ⟨sMid, n1, n2, p1, p2, rfl, rfl, tope1, tope2⟩ := topes_two topes
      obtain ⟨f1, eq1, sub1⟩ := tope_fresh tope1
      obtain ⟨f2, eq2, sub2⟩ := tope_fresh tope2
      exact ⟨⟨n1, owlEquivalentProperty, n2⟩, p1 ++ p2, f1 ++ f2, rfl, fresh_two eq1 eq2,
        sides_of (side_append (tope_side tope1) (tope_side tope2)) (subjects_pair sub1 sub2),
        main_special vocab (by simp [mainPredicates])
          (tope_node_fresh tope1 eq1 (fun y m => List.mem_append_left _ m))⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | disjointObjectProperties xs =>
    cases tax with
    | disjointObjectProperties e1 e2 _ _ _ n1 n2 q1 q2 tope1 tope2 =>
      obtain ⟨f1, eq1, sub1⟩ := tope_fresh tope1
      obtain ⟨f2, eq2, sub2⟩ := tope_fresh tope2
      exact ⟨_, _, f1 ++ f2, rfl, fresh_two eq1 eq2,
        sides_of (side_append (tope_side tope1) (tope_side tope2)) (subjects_pair sub1 sub2),
        main_special vocab (by simp [mainPredicates])
          (tope_node_fresh tope1 eq1 (fun y m => List.mem_append_left _ m))⟩
    | allDisjointObjectProperties _ x cells _ _ nodes eps _ _ topes =>
      obtain ⟨f, eqf, subf⟩ := topes_fresh topes
      refine ⟨_, _, x :: (cells ++ f), rfl, by rw [eqf]; simp, ?_, main_typed_fresh (by simp)⟩
      refine sides_of (side_cons (side_key (by simp [sideVocabulary]))
        (side_append (list_side _ _) (topes_side topes))) ?_
      exact subjects_cons rfl (subjects_widen (subjects_pair (list_of_subjects _ _) subf))
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | inverseProperties p q =>
    cases tax with
    | inverseProperties _ _ _ _ _ n1 n2 q1 q2 tope1 tope2 =>
      cases tope1
      obtain ⟨f2, eq2, sub2⟩ := tope_fresh tope2
      exact ⟨_, _, f2, rfl, eq2, sides_of (side_append side_nil (tope_side tope2)) (by simpa using sub2),
        main_special vocab (by simp [mainPredicates]) iri_not_blank⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | objectDomain role c r =>
    cases tax with
    | objectDomain _ _ _ _ _ n1 n2 p1 p2 tope tce =>
      obtain ⟨f1, eq1, sub1⟩ := tope_fresh tope
      obtain ⟨f2, eq2, sub2⟩ := tce_fresh tce
      exact ⟨_, _, f1 ++ f2, rfl, fresh_two eq1 eq2,
        sides_of (side_append (tope_side tope) (tce_side tce r)) (subjects_pair sub1 sub2),
        main_special vocab (by simp [mainPredicates])
          (tope_node_fresh tope eq1 (fun y m => List.mem_append_left _ m))⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | objectRange role c r =>
    cases tax with
    | objectRange _ _ _ _ _ n1 n2 p1 p2 tope tce =>
      obtain ⟨f1, eq1, sub1⟩ := tope_fresh tope
      obtain ⟨f2, eq2, sub2⟩ := tce_fresh tce
      exact ⟨_, _, f1 ++ f2, rfl, fresh_two eq1 eq2,
        sides_of (side_append (tope_side tope) (tce_side tce r)) (subjects_pair sub1 sub2),
        main_special vocab (by simp [mainPredicates])
          (tope_node_fresh tope eq1 (fun y m => List.mem_append_left _ m))⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | functional role =>
    cases tax with
    | characteristic _ _ _ _ _ _ _ ct tope => exact characteristic_shape vocab ct tope
  | inverseFunctional role =>
    cases tax with
    | characteristic _ _ _ _ _ _ _ ct tope => exact characteristic_shape vocab ct tope
  | reflexive role =>
    cases tax with
    | characteristic _ _ _ _ _ _ _ ct tope => exact characteristic_shape vocab ct tope
  | irreflexive role =>
    cases tax with
    | characteristic _ _ _ _ _ _ _ ct tope => exact characteristic_shape vocab ct tope
  | symmetric role =>
    cases tax with
    | characteristic _ _ _ _ _ _ _ ct tope => exact characteristic_shape vocab ct tope
  | asymmetric role =>
    cases tax with
    | characteristic _ _ _ _ _ _ _ ct tope => exact characteristic_shape vocab ct tope
  | transitive role =>
    cases tax with
    | characteristic _ _ _ _ _ _ _ ct tope => exact characteristic_shape vocab ct tope
  | subDataProperty d1 d2 =>
    cases tax with
    | subDataProperty _ _ _ =>
      exact ⟨_, [], [], rfl, by simp, sides_nil _, main_special vocab (by simp [mainPredicates]) iri_not_blank⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | equivalentDataProperties xs emptyRest =>
    cases tax with
    | equivalentDataProperties _ _ =>
      refine ⟨⟨iriNode xs.first.iri, owlEquivalentProperty, iriNode xs.second.iri⟩, [], [],
        by simp [chainOf, members_two emptyRest], by simp, sides_nil _,
        main_special vocab (by simp [mainPredicates]) iri_not_blank⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | disjointDataProperties xs =>
    cases tax with
    | disjointDataProperties d1 d2 _ =>
      exact ⟨_, [], [], rfl, by simp, sides_nil _, main_special vocab (by simp [mainPredicates]) iri_not_blank⟩
    | allDisjointDataProperties _ x cells _ _ _ =>
      refine ⟨_, _, x :: cells, rfl, by simp, ?_, main_typed_fresh (by simp)⟩
      refine sides_of (side_cons (side_key (by simp [sideVocabulary])) (list_side _ _)) ?_
      exact subjects_cons rfl (subjects_widen (list_of_subjects _ _))
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | dataDomain d c r =>
    cases tax with
    | dataDomain _ _ _ _ n p tce =>
      obtain ⟨f, eqf, subf⟩ := tce_fresh tce
      exact ⟨_, _, f, rfl, eqf, sides_of (tce_side tce r) subf,
        main_special vocab (by simp [mainPredicates]) iri_not_blank⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | dataRange d r readableRange =>
    cases tax with
    | dataRange _ _ _ _ n p tdr =>
      obtain ⟨f, eqf, subf⟩ := tdr_fresh tdr
      exact ⟨_, _, f, rfl, eqf, sides_of (tdr_side tdr readableRange) subf,
        main_special vocab (by simp [mainPredicates]) iri_not_blank⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | functionalData d =>
    cases tax with
    | functionalData _ _ =>
      refine ⟨_, [], [], rfl, by simp, sides_nil _, main_typed_property vocab ?_ ?_ ?_⟩
      · simp [declarationTypes, owlClass, rdfsDatatype, owlObjectProperty, owlDatatypeProperty, owlAnnotationProperty,
          owlNamedIndividual, owlFunctionalProperty]
      · simp [owlOntology, owlFunctionalProperty]
      · intro y h; simp [iriNode] at h
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | datatypeDefinition d r readableRange _ =>
    cases tax with
    | datatypeDefinition _ _ _ _ n p tdr =>
      obtain ⟨f, eqf, subf⟩ := tdr_fresh tdr
      exact ⟨_, _, f, rfl, eqf, sides_of (tdr_side tdr readableRange) subf,
        main_special vocab (by simp [mainPredicates]) iri_not_blank⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | hasKey c objects datas r =>
    cases tax with
    | hasKey _ _ _ cells _ _ _ n nodes p eps tce _ topes =>
      obtain ⟨fC, eqC, subC⟩ := tce_fresh tce
      obtain ⟨fO, eqO, subO⟩ := topes_fresh topes
      refine ⟨_, _, fC ++ (cells ++ fO), rfl, by rw [eqC, eqO]; simp, ?_,
        main_special vocab (by simp [mainPredicates])
          (tce_node_fresh tce eqC (fun y m => List.mem_append_left _ m))⟩
      refine sides_of (side_append (side_append (list_side _ _) (tce_side tce r)) (topes_side topes)) ?_
      refine subjects_in_append (subjects_in_append ?_ ?_) ?_
      · exact subjects_sub (list_of_subjects _ _) (fun y m => by simp [m])
      · exact subjects_sub subC (fun y m => by simp [m])
      · exact subjects_sub subO (fun y m => by simp [m])
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | sameIndividual xs emptyRest =>
    cases tax with
    | sameIndividual _ _ =>
      refine ⟨⟨individualNode xs.first, owlSameAs, individualNode xs.second⟩, [], [],
        by simp [chainOf, members_two emptyRest], by simp, sides_nil _,
        main_special vocab (by simp [mainPredicates]) ?_⟩
      intro y h
      cases first : xs.first with
      | Named _ => rw [first] at h; simp [individualNode, iriNode] at h
      | Anonymous an =>
        rw [first] at h
        simp only [individualNode, anonymousNode, Node.blank.injEq] at h
        exact Or.inr ⟨an, by simp [subjectAnonymous, first], h.symm⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | differentIndividuals xs =>
    cases tax with
    | differentIndividuals i1 i2 _ =>
      refine ⟨_, [], [], rfl, by simp, sides_nil _, main_special vocab (by simp [mainPredicates]) ?_⟩
      intro y h
      cases i1 with
      | Named _ => simp [individualNode, iriNode] at h
      | Anonymous an =>
        simp only [individualNode, anonymousNode, Node.blank.injEq] at h
        exact Or.inr ⟨an, by simp [subjectAnonymous], h.symm⟩
    | allDifferent _ x cells _ _ _ =>
      refine ⟨_, _, x :: cells, rfl, by simp, ?_, main_typed_fresh (by simp)⟩
      refine sides_of (side_cons (side_key (by simp [sideVocabulary])) (list_side _ _)) ?_
      exact subjects_cons rfl (subjects_widen (list_of_subjects _ _))
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | classAssertion c individual r =>
    cases tax with
    | classAssertion _ _ _ _ n p tce =>
      obtain ⟨f, eqf, subf⟩ := tce_fresh tce
      have allowedClass : ∀ cl : model.Class, c = .Class cl → Rowl.Vocabulary.EntityAllowed cl.iri .Class := by
        intro cl isClass
        exact allowed (cl.iri, .Class) (by simp [Rowl.Collection.axiomUses, isClass, Rowl.Collection.classUses])
      refine ⟨_, _, f, rfl, eqf, sides_of (tce_side tce r) subf, main_class_assertion vocab tce allowedClass ?_⟩
      intro y h
      rcases tce_node_fresh (ax := .Declaration (.Class ⟨⟨alloc.vec.Vec.new _⟩⟩)) tce eqf (fun z m => m) y h with
        inside | ⟨an, isSome, _⟩
      · exact inside
      · simp [subjectAnonymous] at isSome
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | objectAssertion p i1 i2 =>
    cases tax with
    | objectAssertion _ _ _ _ =>
      have member : (p.iri, typing.EntityKind.ObjectProperty) ∈ Rowl.Collection.axiomUses
          (.ObjectPropertyAssertion (.Property p) i1 i2) := by
        simp [Rowl.Collection.axiomUses, Rowl.Collection.objectUses]
      exact ⟨_, [], [], rfl, by simp, sides_nil _,
        main_assertion (allowed _ member) (Or.inl (typed _ member).1) (by cases i1 <;> rfl)⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | negativeObject role i1 i2 =>
    cases tax with
    | negativeObject _ _ _ x _ _ n p tope =>
      obtain ⟨f, eqf, subf⟩ := tope_fresh tope
      refine ⟨_, _, x :: f, rfl, by rw [eqf]; simp, ?_, main_typed_fresh (by simp)⟩
      refine sides_of (side_cons (side_key (by simp [sideVocabulary])) (side_cons (side_key (by simp [sideVocabulary]))
        (side_cons (side_key (by simp [sideVocabulary])) (tope_side tope)))) ?_
      exact subjects_cons rfl (subjects_cons rfl (subjects_cons rfl (subjects_widen subf)))
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | dataAssertion d individual v _ =>
    cases tax with
    | dataAssertion _ _ _ _ n _ =>
      have member : (d.iri, typing.EntityKind.DataProperty) ∈ Rowl.Collection.axiomUses
          (.DataPropertyAssertion d individual v) := by
        simp [Rowl.Collection.axiomUses, Rowl.Collection.dataUses]
      exact ⟨_, [], [], rfl, by simp, sides_nil _,
        main_assertion (allowed _ member) (Or.inr (typed _ member).1) (by cases individual <;> rfl)⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | negativeData d i1 v _ =>
    cases tax with
    | negativeData _ _ _ x _ n _ =>
      refine ⟨_, _, [x], rfl, by simp, ?_, main_typed_fresh (by simp)⟩
      refine sides_of (side_cons (side_key (by simp [sideVocabulary])) (side_cons (side_key (by simp [sideVocabulary]))
        (side_cons (side_key (by simp [sideVocabulary])) side_nil))) ?_
      exact subjects_cons rfl (subjects_cons rfl (subjects_cons rfl (subjects_in_nil _)))
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | annotationAssertion p sub value _ =>
    cases tax with
    | annotationAssertion _ _ _ _ n _ =>
      have member : (p.iri, typing.EntityKind.AnnotationProperty) ∈ Rowl.Collection.axiomUses
          (.AnnotationAssertion p sub value) := by
        simp [Rowl.Collection.axiomUses]
      exact ⟨_, [], [], rfl, by simp, sides_nil _,
        main_annotation (allowed _ member) (fun iri version named => apart p sub value rfl iri version named)⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | subAnnotationProperty p1 p2 =>
    cases tax with
    | subAnnotationProperty _ _ _ =>
      exact ⟨_, [], [], rfl, by simp, sides_nil _, main_special vocab (by simp [mainPredicates]) iri_not_blank⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | annotationDomain p iri =>
    cases tax with
    | annotationDomain _ _ _ =>
      exact ⟨_, [], [], rfl, by simp, sides_nil _, main_special vocab (by simp [mainPredicates]) iri_not_blank⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct
  | annotationRange p iri =>
    cases tax with
    | annotationRange _ _ _ =>
      exact ⟨_, [], [], rfl, by simp, sides_nil _, main_special vocab (by simp [mainPredicates]) iri_not_blank⟩
    | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct

/-! ### The axiom loop -/

/-- A block of the axiom loop: an axiom, the position of its main triple and the
    positions of its other triples, its patterns (the main one first) and its
    blank nodes. -/
structure Block where
  ax : model.Axiom
  main : Nat
  rest : List Nat
  pats : List Pattern
  fresh : Supply

def Block.pos (b : Block) : List Nat := b.main :: b.rest

/-- The axiom loop reads the block at its main position: the axiom, without
    annotations, using exactly its positions and recording exactly its blank
    nodes. -/
def BlockOk (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (b : Block) : Prop :=
  At triples.val b.pos b.pats ∧ b.pos.Nodup ∧
  ∀ (s : rdf_mapping.State) (a : Usize), a.val = b.main → Ready triples s b.pos b.pats b.fresh →
    (∀ x ∈ s.sources.val, x.val = []) →
    ∃ s', rdf_mapping.read_axiom triples kinds a s (alloc.vec.Vec.len triples) = .ok (.Found b.ax s') ∧
      rdf_mapping.annotate triples kinds a b.ax s' (alloc.vec.Vec.len triples) =
        .ok (some (⟨alloc.vec.Vec.new _, b.ax⟩, s')) ∧
      Marked s s' (fun i => i ∈ b.pos) b.fresh

/-- The state of the axiom loop before the blocks `bs`: their positions unused
    and every other position used, every unused triple about a blank node of a
    block at a position of that block, and room for their blank nodes. -/
structure LoopState (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (bs : List Block) : Prop where
  complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length
  sources : ∀ x ∈ s.sources.val, x.val = []
  length : s.used.val.length = triples.val.length
  free : ∀ b ∈ bs, ∀ i ∈ b.pos, s.used.val[i]? = some false
  covered : ∀ i, s.used.val[i]? = some false → ∃ b ∈ bs, i ∈ b.pos
  owns : ∀ b ∈ bs, ∀ (i : Nat) (t : rdf.Triple) (y : rdf.BlankNode), triples.val[i]? = some t →
    s.used.val[i]? = some false → subjectView t.subject = .blank y → y ∈ b.fresh → i ∈ b.pos
  room : s.blanks.val.length + (bs.flatMap Block.fresh).length ≤ Usize.max

/-- Blocks with disjoint positions. -/
def Apart (b c : Block) : Prop := ∀ i ∈ b.pos, i ∉ c.pos

instance apartSymm : Std.Symm Apart where
  symm := fun _ _ h i ic ib => h i ib ic

theorem axioms_from_end (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (s : rdf_mapping.State)
    (out : alloc.vec.Vec model.AnnotatedAxiom) (index : Usize) (done : triples.val.length ≤ index.val) :
    rdf_mapping.axioms_from triples kinds index s out = .ok (some (out, s)) := by
  have stop : ¬ index.val < triples.val.length := by omega
  rw [rdf_mapping.axioms_from]; simp [UScalar.lt_equiv, stop]

theorem axioms_from_used (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (s : rdf_mapping.State)
    (out : alloc.vec.Vec model.AnnotatedAxiom) (index next : Usize) (inside : index.val < triples.val.length)
    (used : s.used.val[index.val]? ≠ some false) (advance : (index + 1#usize : Result Usize) = .ok next) :
    rdf_mapping.axioms_from triples kinds index s out = rdf_mapping.axioms_from triples kinds next s out := by
  rw [rdf_mapping.axioms_from]
  simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, is_used_correct, used, advance]

theorem axioms_from_skipped (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (s : rdf_mapping.State)
    (out : alloc.vec.Vec model.AnnotatedAxiom) (index next : Usize) (inside : index.val < triples.val.length)
    (unused : s.used.val[index.val]? = some false)
    (read : rdf_mapping.read_axiom triples kinds index s (alloc.vec.Vec.len triples) = .ok (.Skip s))
    (advance : (index + 1#usize : Result Usize) = .ok next) :
    rdf_mapping.axioms_from triples kinds index s out = rdf_mapping.axioms_from triples kinds next s out := by
  rw [rdf_mapping.axioms_from]
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, is_used_correct, unused, ne_eq,
    not_true_eq_false, decide_false, Bool.false_eq_true, bind_ok, read, advance]

theorem axioms_from_found (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (a next : Usize)
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

theorem loop_state_after {triples : alloc.vec.Vec rdf.Triple} {s s' : rdf_mapping.State} {b : Block}
    {rest : List Block} (state : LoopState triples s (b :: rest)) (disjoint : ∀ c ∈ rest, Apart b c)
    (marked : Marked s s' (fun i => i ∈ b.pos) b.fresh) : LoopState triples s' rest where
  complete := by rw [marked.subjects]; exact state.complete
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
  owns := fun c member i t y at_i unused about inF =>
    state.owns c (List.mem_cons_of_mem _ member) i t y at_i (marked_back marked unused) about inF
  room := by
    have room := state.room
    rw [marked.blanks]
    simp only [List.flatMap_cons, List.length_append] at room ⊢
    omega

theorem loop_ready {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds} {s : rdf_mapping.State}
    {b : Block} {rest : List Block} (state : LoopState triples s (b :: rest)) (ok : BlockOk triples kinds b) :
    Ready triples s b.pos b.pats b.fresh where
  complete := state.complete
  holds := ok.1
  nodup := ok.2.1
  free := state.free b (by simp)
  owns := state.owns b (by simp)
  room := by
    have room := state.room
    simp only [List.flatMap_cons, List.length_append] at room
    omega

theorem block_main_inside {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds} {b : Block}
    (ok : BlockOk triples kinds b) : b.main < triples.val.length := by
  have holds := ok.1
  simp only [Block.pos, At] at holds
  obtain ⟨_, _, ⟨t, at_t, -⟩, -, -⟩ := List.forall₂_cons_left_iff.mp holds
  exact (List.getElem?_eq_some_iff.mp at_t).1

/-- **The axiom loop reads the blocks in the order of their main positions.**
    From an index at or before every main position, with every block read by
    `read_axiom` from its main position and every other position of a block
    before its main one passed over, `axioms_from` returns the axioms of the
    blocks in order, records their blank nodes in order and uses every triple. -/
theorem axioms_loop (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) :
    ∀ (n : Nat) (a : Usize) (bs : List Block) (s : rdf_mapping.State) (out : alloc.vec.Vec model.AnnotatedAxiom),
      triples.val.length - a.val = n → (∀ b ∈ bs, BlockOk triples kinds b) →
      bs.Pairwise (fun b c => b.main < c.main) → bs.Pairwise Apart → (∀ b ∈ bs, a.val ≤ b.main) →
      (∀ b ∈ bs, ∀ i ∈ b.rest, i < b.main → ∀ (u : Usize) (s' : rdf_mapping.State), u.val = i →
        rdf_mapping.read_axiom triples kinds u s' (alloc.vec.Vec.len triples) = .ok (.Skip s')) →
      LoopState triples s bs → out.val.length + bs.length ≤ Usize.max →
      ∃ v s', rdf_mapping.axioms_from triples kinds a s out = .ok (some (v, s')) ∧
        v.val = out.val ++ bs.map (fun b => (⟨alloc.vec.Vec.new _, b.ax⟩ : model.AnnotatedAxiom)) ∧
        s'.blanks.val = s.blanks.val ++ bs.flatMap Block.fresh ∧
        ∀ (i : Nat), i < triples.val.length → s'.used.val[i]? = some true := by
  intro n
  induction n with
  | zero =>
    intro a bs s out ends ok sorted disjoint after skip state room
    have done : triples.val.length ≤ a.val := by omega
    have empty : bs = [] := by
      cases bs with
      | nil => rfl
      | cons b rest =>
        have := block_main_inside (ok b (by simp))
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
    intro a bs s out ends ok sorted disjoint after skip state room
    have more : a.val < triples.val.length := by omega
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := a) (y := 1#usize) (by have := triples.property; scalar_tac))
    have nextIs : next.val = a.val + 1 := by simpa using nextValue
    have inside : a.val < s.used.val.length := by rw [state.length]; exact more
    by_cases unused : s.used.val[a.val]? = some false
    · obtain ⟨b, member, inB⟩ := state.covered a.val unused
      by_cases isMain : a.val = b.main
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
        obtain ⟨s', readRun, annotateRun, marked⟩ := (ok b (by simp)).2.2 s a isMain (loop_ready state (ok b (by simp)))
          state.sources
        have pushRoom : out.val.length < Usize.max := by simp at room; omega
        obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec out (⟨alloc.vec.Vec.new _, b.ax⟩ : model.AnnotatedAxiom) pushRoom)
        have step := axioms_from_found triples kinds a next s s' out pushed ⟨alloc.vec.Vec.new _, b.ax⟩ more unused
          readRun annotateRun pushRoom push advance
        obtain ⟨v, s'', run, vIs, blanksIs, allUsed⟩ := ih next rest s' pushed (by omega)
          (fun c m => ok c (List.mem_cons_of_mem _ m)) (List.pairwise_cons.mp sorted).2
          (List.pairwise_cons.mp disjoint).2
          (fun c m => by have := (List.pairwise_cons.mp sorted).1 c m; omega)
          (fun c m => skip c (List.mem_cons_of_mem _ m))
          (loop_state_after state (List.pairwise_cons.mp disjoint).1 marked)
          (by rw [contents]; simp at room ⊢; omega)
        refine ⟨v, s'', by rw [step, run], by rw [vIs, contents]; simp, ?_, allUsed⟩
        rw [blanksIs, marked.blanks]
        simp
      · -- another triple of a later block, passed over
        have inRest : a.val ∈ b.rest := by
          simp only [Block.pos, List.mem_cons] at inB
          rcases inB with h | h
          · exact absurd h isMain
          · exact h
        have before : a.val < b.main := by have := after b member; omega
        have read := skip b member a.val inRest before a s rfl
        have step := axioms_from_skipped triples kinds s out a next more unused read advance
        obtain ⟨v, s', run, vIs, blanksIs, allUsed⟩ := ih next bs s out (by omega) ok sorted disjoint
          (by
            intro c m
            have le := after c m
            rw [nextIs]
            apply Nat.lt_of_le_of_ne le
            intro same
            by_cases cb : c = b
            · subst cb
              exact isMain same
            · exact disjoint.forall m member cb a.val (by rw [same]; simp [Block.pos]) inB)
          skip state room
        exact ⟨v, s', by rw [step, run], vIs, blanksIs, allUsed⟩
    · -- a used triple
      have step := axioms_from_used triples kinds s out a next more unused advance
      obtain ⟨v, s', run, vIs, blanksIs, allUsed⟩ := ih next bs s out (by omega) ok sorted disjoint
        (by
          intro c m
          have le := after c m
          rw [nextIs]
          apply Nat.lt_of_le_of_ne le
          intro same
          exact unused (by rw [same]; exact state.free c m c.main (by simp [Block.pos])))
        skip state room
      exact ⟨v, s', by rw [step, run], vIs, blanksIs, allUsed⟩

/-! ### How many blank nodes an axiom allocates -/

theorem list_count {cells : List rdf.BlankNode} {nodes : List Node} (h : cells.length = nodes.length) :
    cells.length ≤ (listOf cells nodes).2.length := by
  rw [list_of_length cells nodes h]; omega

/-- An axiom allocates at most as many blank nodes as its forward image has triples. -/
theorem taxiom_count {ax : model.Axiom} {s0 : Supply} {ps : List Pattern} {s1 : Supply} (h : TAxiom ax s0 ps s1) :
    s0.length ≤ s1.length + ps.length := by
  cases h with
  | declaration => simp
  | subClassOf _ _ _ _ _ _ _ _ _ tce1 tce2 =>
    have := tce_count tce1; have := tce_count tce2; simp; omega
  | equivalentClasses _ _ _ _ _ tces =>
    have := tces_count tces; simp; omega
  | disjointClasses _ _ _ _ _ _ _ _ _ tce1 tce2 =>
    have := tce_count tce1; have := tce_count tce2; simp; omega
  | allDisjointClasses _ _ cells _ _ nodes _ _ cellsLen tces =>
    have := tces_count tces
    have := list_count (cells := cells) (nodes := nodes) (by rw [cellsLen, tces_length tces])
    simp; omega
  | disjointUnion _ _ cells _ _ nodes _ cellsLen tces =>
    have := tces_count tces
    have := list_count (cells := cells) (nodes := nodes) (by rw [cellsLen, tces_length tces])
    simp; omega
  | subObjectProperty _ _ _ _ _ _ _ _ _ tope1 tope2 =>
    have := tope_count tope1; have := tope_count tope2; simp; omega
  | propertyChain _ _ cells _ _ _ _ nodes _ _ topeSup cellsLen topes =>
    have := tope_count topeSup
    have := topes_count topes
    have := list_count (cells := cells) (nodes := nodes) (by rw [cellsLen, ← topes_length topes])
    simp at *; omega
  | equivalentObjectProperties _ _ _ _ _ topes =>
    have := topes_count topes; simp; omega
  | disjointObjectProperties _ _ _ _ _ _ _ _ _ tope1 tope2 =>
    have := tope_count tope1; have := tope_count tope2; simp; omega
  | allDisjointObjectProperties _ _ cells _ _ nodes _ _ cellsLen topes =>
    have := topes_count topes
    have := list_count (cells := cells) (nodes := nodes) (by rw [cellsLen, ← topes_length topes])
    simp; omega
  | inverseProperties _ _ _ _ _ _ _ _ _ tope1 tope2 =>
    have := tope_count tope1; have := tope_count tope2; simp; omega
  | objectDomain _ _ _ _ _ _ _ _ _ tope tce =>
    have := tope_count tope; have := tce_count tce; simp; omega
  | objectRange _ _ _ _ _ _ _ _ _ tope tce =>
    have := tope_count tope; have := tce_count tce; simp; omega
  | characteristic _ _ _ _ _ _ _ _ tope =>
    have := tope_count tope; simp; omega
  | subDataProperty => simp
  | equivalentDataProperties => simp
  | disjointDataProperties => simp
  | allDisjointDataProperties xs _ cells _ _ cellsLen =>
    have := list_count (cells := cells) (nodes := (members2 xs).map (iriNode ·.iri)) (by rw [cellsLen, List.length_map])
    simp; omega
  | dataDomain _ _ _ _ _ _ tce => have := tce_count tce; simp; omega
  | dataRange _ _ _ _ _ _ tdr => have := tdr_count tdr; simp; omega
  | functionalData => simp
  | datatypeDefinition _ _ _ _ _ _ tdr => have := tdr_count tdr; simp; omega
  | hasKey _ objects datas cells _ _ _ _ nodes _ _ tce cellsLen topes =>
    have := tce_count tce
    have := topes_count topes
    have := list_count (cells := cells) (nodes := nodes ++ datas.val.map (iriNode ·.iri))
      (by rw [cellsLen, List.length_append, List.length_map, topes_length topes])
    simp at *; omega
  | sameIndividual => simp
  | differentIndividuals => simp
  | allDifferent xs _ cells _ _ cellsLen =>
    have := list_count (cells := cells) (nodes := (members2 xs).map individualNode) (by rw [cellsLen, List.length_map])
    simp; omega
  | classAssertion _ _ _ _ _ _ tce => have := tce_count tce; simp; omega
  | objectAssertion => simp
  | inverseAssertion => simp
  | negativeObject _ _ _ _ _ _ _ _ tope => have := tope_count tope; simp; omega
  | dataAssertion => simp
  | negativeData => simp
  | annotationAssertion => simp
  | subAnnotationProperty => simp
  | annotationDomain => simp
  | annotationRange => simp

/-! ### The blocks of the axioms in the order of the forward mapping -/

/-- A block of the forward image of an unannotated axiom of the ontology. -/
structure ImageBlock (o : model.RawOntology) (b : Block) : Prop where
  member : ∃ ax ∈ o.axioms.val, ax.axiom = b.ax ∧ ax.annotations.val = []
  forward : ∃ s1, TAxiom b.ax (b.fresh ++ s1) b.pats s1
  shape : ∃ main side, b.pats = main :: side ∧ Sides b.fresh side ∧ MainFacts o b.ax b.fresh main

theorem plain_axiom {ax : model.AnnotatedAxiom} {s0 s1 : Supply} {p : List Pattern}
    (h : TAnnotatedAxiom ax s0 p s1) (plain : ax.annotations.val = []) : TAxiom ax.axiom s0 p s1 := by
  cases h with
  | plain _ _ _ _ tax => exact tax
  | reified _ _ _ _ _ nonempty => exact absurd plain nonempty
  | blank _ _ _ _ _ _ _ _ nonempty => exact absurd plain nonempty

theorem plain_annotated (ax : model.AnnotatedAxiom) (plain : ax.annotations.val = []) :
    (⟨alloc.vec.Vec.new _, ax.axiom⟩ : model.AnnotatedAxiom) = ax := by
  obtain ⟨anns, axm⟩ := ax
  simp only at plain
  rw [vec_eq_of_val (u := alloc.vec.Vec.new model.Annotation) (v := anns) (by simp [plain])]

/-- The blocks of the axioms whose triples the graph lists in order from `start` on. -/
theorem forward_blocks {o : model.RawOntology} (readable : ReadableOntology o) (triples : alloc.vec.Vec rdf.Triple) :
    ∀ {axs : List model.AnnotatedAxiom} {s0 : Supply} {ps : List Pattern} {s1 : Supply}, TAxioms axs s0 ps s1 →
    (∀ ax ∈ axs, ax ∈ o.axioms.val) → ∀ (start : Nat), At triples.val (List.range' start ps.length) ps →
    ∃ bs : List Block,
      bs.map (fun b => (⟨alloc.vec.Vec.new _, b.ax⟩ : model.AnnotatedAxiom)) = axs ∧
      s0 = bs.flatMap Block.fresh ++ s1 ∧
      bs.Pairwise (fun b c => b.main < c.main) ∧ bs.Pairwise Apart ∧
      (∀ b ∈ bs, ImageBlock o b ∧ At triples.val b.pos b.pats ∧ b.pos.Nodup ∧ (∀ i ∈ b.rest, b.main < i) ∧
        ∀ i ∈ b.pos, start ≤ i ∧ i < start + ps.length) ∧
      (∀ i, start ≤ i → i < start + ps.length → ∃ b ∈ bs, i ∈ b.pos) := by
  intro axs s0 ps s1 h
  induction h with
  | nil s =>
    intro _ start _
    refine ⟨[], by simp, by simp, by simp, by simp, by simp, ?_⟩
    intro i low high
    simp at high
    omega
  | cons ax rest s s1 s2 p q head tail ih =>
    intro members start holds
    have axIn := members ax (by simp)
    have plain := (readable.axioms ax axIn).1
    have tax := plain_axiom head plain
    obtain ⟨main, side, f, pIs, eqf, sides, facts⟩ := block_shape readable axIn tax
    rw [List.length_append, ← List.range'_append_1] at holds
    obtain ⟨holdsP, holdsQ⟩ := at_append_inv holds (by simp)
    obtain ⟨bs, mapIs, freshIs, sorted, disjoint, each, covers⟩ :=
      ih (fun b m => members b (List.mem_cons_of_mem _ m)) (start + p.length) holdsQ
    have pLen : 0 < p.length := by rw [pIs]; simp
    let b : Block := { ax := ax.axiom, main := start, rest := List.range' (start + 1) (p.length - 1), pats := p,
                       fresh := f }
    have bPos : b.pos = List.range' start p.length := by
      simp only [Block.pos, b]
      obtain ⟨k, hk⟩ : ∃ k, p.length = k + 1 := ⟨p.length - 1, by omega⟩
      rw [hk, List.range'_succ]
      simp
    have bInRange : ∀ i ∈ b.pos, start ≤ i ∧ i < start + p.length := by
      intro i m
      rw [bPos, List.mem_range'_1] at m
      exact m
    refine ⟨b :: bs, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, mapIs, b]
      rw [plain_annotated ax plain]
    · simp only [List.flatMap_cons, b]
      rw [eqf, freshIs, List.append_assoc]
    · refine List.Pairwise.cons ?_ sorted
      intro c m
      have := ((each c m).2.2.2.2 c.main (by simp [Block.pos])).1
      simp only [b]
      omega
    · refine List.Pairwise.cons ?_ disjoint
      intro c m i ib ic
      have h1 := bInRange i ib
      have h2 := (each c m).2.2.2.2 i ic
      omega
    · intro c m
      rcases List.mem_cons.mp m with rfl | inRest
      · refine ⟨⟨⟨ax, axIn, rfl, plain⟩, ⟨s1, by rw [← eqf]; exact tax⟩, ⟨main, side, pIs, sides, facts⟩⟩,
          by rw [bPos]; exact holdsP, by rw [bPos]; exact List.nodup_range', ?_, ?_⟩
        · intro i m'
          simp only [b, List.mem_range'_1] at m'
          simp only [b]
          omega
        · intro i m'
          have := bInRange i m'
          simp only [List.length_append]
          omega
      · obtain ⟨image, holdsC, nodupC, restC, rangeC⟩ := each c inRest
        refine ⟨image, holdsC, nodupC, restC, fun i m' => ?_⟩
        have := rangeC i m'
        simp only [List.length_append]
        omega
    · intro i low high
      by_cases inP : i < start + p.length
      · exact ⟨b, by simp, by rw [bPos, List.mem_range'_1]; exact ⟨low, inP⟩⟩
      · obtain ⟨c, m, ic⟩ := covers i (by omega) (by simp only [List.length_append] at high; omega)
        exact ⟨c, List.mem_cons_of_mem _ m, ic⟩

/-! ### The triples of a graph of the forward mapping -/

/-- The forward header of an ontology without ontology annotations. -/
def headerPatterns (o : model.RawOntology) : List Pattern :=
  match o.identity with
  | .Anonymous => []
  | .Named iri version => ⟨iriNode iri, rdfType, .iri owlOntology⟩ ::
      ((match version with
        | some v => [⟨iriNode iri, owlVersionIRI, iriNode v⟩]
        | none => []) ++ o.imports.val.map (fun i => ⟨iriNode iri, owlImports, iriNode i⟩))

theorem header_of {o : model.RawOntology} (empty : o.annotations.val = []) {supply rest : Supply}
    {header : List Pattern} (h : THeader o supply header rest) : header = headerPatterns o ∧ rest = supply := by
  cases h with
  | anonymous _ hid _ _ => simp [headerPatterns, hid]
  | named iri version s s' anns hid tanns =>
    rw [empty] at tanns
    cases tanns
    cases version <;> simp [headerPatterns, hid]

theorem header_patterns_shape {o : model.RawOntology} {q : Pattern} (member : q ∈ headerPatterns o) :
    ∃ iri version, o.identity = .Named iri version ∧ q.subject = iriNode iri ∧
      ((q.predicate = rdfType ∧ q.object = .iri owlOntology) ∨ q.predicate = owlVersionIRI ∨
        q.predicate = owlImports) := by
  unfold headerPatterns at member
  split at member
  · simp at member
  · rename_i iri version hid
    refine ⟨iri, version, hid, ?_⟩
    simp only [List.mem_cons, List.mem_append, List.mem_map] at member
    rcases member with rfl | inVersion | ⟨i, -, rfl⟩
    · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    · cases version with
      | none => simp at inVersion
      | some v =>
        simp only [List.mem_singleton] at inVersion
        subst inVersion
        exact ⟨rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨rfl, Or.inr (Or.inr rfl)⟩

/-- Every triple of the graph is a triple of the header or of a block. -/
def Sourced (triples : List rdf.Triple) (header : List Pattern) (bs : List Block) : Prop :=
  ∀ (i : Nat) (t : rdf.Triple), triples[i]? = some t → (∃ q ∈ header, Matches q t) ∨ ∃ b ∈ bs, ∃ q ∈ b.pats, Matches q t

theorem block_pattern {o : model.RawOntology} {b : Block} (image : ImageBlock o b) {q : Pattern} (member : q ∈ b.pats) :
    ∃ main side, b.pats = main :: side ∧ Sides b.fresh side ∧ MainFacts o b.ax b.fresh main ∧
      (q = main ∨ q ∈ side) := by
  obtain ⟨main, side, pats, sides, facts⟩ := image.shape
  rw [pats] at member
  exact ⟨main, side, pats, sides, facts, List.mem_cons.mp member⟩

theorem side_not_source {q : Pattern} (h : SideKind q) : q.predicate ≠ owlAnnotatedSource := by
  intro same
  rcases h with inSide | inFacets | inverse | ⟨typed, -⟩
  · rw [same] at inSide
    simp [sideVocabulary, rdfFirst, rdfRest, owlOnProperty, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue,
      owlHasSelf, owlMinCardinality, owlMaxCardinality, owlCardinality, owlMinQualifiedCardinality,
      owlMaxQualifiedCardinality, owlQualifiedCardinality, owlOnClass, owlOnDataRange, owlIntersectionOf, owlUnionOf,
      owlComplementOf, owlOneOf, owlDatatypeComplementOf, owlOnDatatype, owlWithRestrictions, owlMembers,
      owlSourceIndividual, owlAssertionProperty, owlTargetIndividual, owlTargetValue, owlAnnotatedSource] at inSide
  · rw [same] at inFacets
    simp [owl2Facets, xsdLength, xsdMinLength, xsdMaxLength, xsdPattern, xsdMinInclusive, xsdMaxInclusive,
      xsdMinExclusive, xsdMaxExclusive, rdfLangRange, owlAnnotatedSource] at inFacets
  · rw [same] at inverse
    simp [owlInverseOf, owlAnnotatedSource] at inverse
  · rw [same] at typed
    simp [rdfType, owlAnnotatedSource] at typed

/-- No triple of the graph is an `owl:annotatedSource` triple. -/
theorem graph_no_source {o : model.RawOntology} {triples : List rdf.Triple} {bs : List Block}
    (sourced : Sourced triples (headerPatterns o) bs) (images : ∀ b ∈ bs, ImageBlock o b) :
    ∀ (i : Nat) (t : rdf.Triple), triples[i]? = some t → t.predicate.spelling.val ≠ owlAnnotatedSource := by
  intro i t at_i
  rcases sourced i t at_i with ⟨q, member, fits⟩ | ⟨b, bIn, q, member, fits⟩
  · rw [fits.2.1]
    obtain ⟨_, _, _, _, which⟩ := header_patterns_shape member
    rcases which with ⟨typed, -⟩ | version | imports
    · rw [typed]; simp [rdfType, owlAnnotatedSource]
    · rw [version]; simp [owlVersionIRI, owlAnnotatedSource]
    · rw [imports]; simp [owlImports, owlAnnotatedSource]
  · rw [fits.2.1]
    obtain ⟨main, side, -, sides, facts, rfl | inSide⟩ := block_pattern (images b bIn) member
    · exact facts.notSource
    · exact side_not_source (sides q inSide).1

/-- No triple of the graph of an anonymous ontology types an IRI `owl:Ontology`. -/
theorem graph_no_ontology {o : model.RawOntology} (anonymous : o.identity = .Anonymous) {triples : List rdf.Triple}
    {bs : List Block} (sourced : Sourced triples (headerPatterns o) bs) (images : ∀ b ∈ bs, ImageBlock o b) :
    ∀ (i : Nat) (t : rdf.Triple), triples[i]? = some t → t.predicate.spelling.val = rdfType →
      objectView t.object = .iri owlOntology → ∀ iri, t.subject ≠ .Iri iri := by
  intro i t at_i typed onto iri isIri
  rcases sourced i t at_i with ⟨q, member, fits⟩ | ⟨b, bIn, q, member, fits⟩
  · simp [headerPatterns, anonymous] at member
  · obtain ⟨main, side, -, sides, facts, rfl | inSide⟩ := block_pattern (images b bIn) member
    · have subject := fits.1
      rw [isIri] at subject
      exact facts.notOntology (by rw [← fits.2.1]; exact typed) _ subject.symm (by rw [← fits.2.2]; exact onto)
    · obtain ⟨y, -, about⟩ := (sides q inSide).2
      have subject := fits.1
      rw [isIri, about] at subject
      simp [subjectView] at subject

/-! ### Declarations -/

theorem declaration_kind_ontology (object : rdf.Object) (onto : objectView object = .iri owlOntology) :
    rdf_mapping.declaration_kind object = .ok none := by
  rw [rdf_mapping.declaration_kind]
  simp only [lift, bind_ok, object_is_correct, array_slice_val]
  simp [onto, owlOntology]

theorem declaration_kind_types (object : rdf.Object) (kind : typing.EntityKind)
    (h : rdf_mapping.declaration_kind object = .ok (some kind)) :
    ∃ T ∈ declarationTypes, objectView object = .iri T := by
  rw [rdf_mapping.declaration_kind] at h
  simp only [lift, bind_ok, object_is_correct, array_slice_val] at h
  by_cases c0 : objectView object = .iri owlClass
  · exact ⟨owlClass, by simp [declarationTypes], c0⟩
  by_cases c1 : objectView object = .iri rdfsDatatype
  · exact ⟨rdfsDatatype, by simp [declarationTypes], c1⟩
  by_cases c2 : objectView object = .iri owlObjectProperty
  · exact ⟨owlObjectProperty, by simp [declarationTypes], c2⟩
  by_cases c3 : objectView object = .iri owlDatatypeProperty
  · exact ⟨owlDatatypeProperty, by simp [declarationTypes], c3⟩
  by_cases c4 : objectView object = .iri owlAnnotationProperty
  · exact ⟨owlAnnotationProperty, by simp [declarationTypes], c4⟩
  by_cases c5 : objectView object = .iri owlNamedIndividual
  · exact ⟨owlNamedIndividual, by simp [declarationTypes], c5⟩
  exfalso
  simp only [owlClass, rdfsDatatype, owlObjectProperty, owlDatatypeProperty, owlAnnotationProperty,
    owlNamedIndividual] at c0 c1 c2 c3 c4 c5
  simp [c0, c1, c2, c3, c4, c5] at h

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

theorem entity_of_injective {k k' : typing.EntityKind} {v v' : alloc.vec.Vec U8} (h : entityOf k v = entityOf k' v') :
    k = k' ∧ v = v' := by
  cases k <;> cases k' <;> simp [entityOf] at h ⊢ <;> exact h

/-- A declaration that a triple of the graph makes is a declaration axiom of the ontology. -/
theorem graph_declares {o : model.RawOntology} {triples : List rdf.Triple} {bs : List Block}
    (sourced : Sourced triples (headerPatterns o) bs) (images : ∀ b ∈ bs, ImageBlock o b) {i : Nat}
    {t : rdf.Triple} (at_i : triples[i]? = some t) {v : alloc.vec.Vec U8} {kind : typing.EntityKind}
    (run : rdf_mapping.declared_entity t = .ok (some (v, kind))) :
    ∃ ax ∈ o.axioms.val, ax.axiom = .Declaration (entityOf kind v) := by
  obtain ⟨typed, iri, isIri, vIs, kindRun⟩ := declared_entity_some t v kind run
  rcases sourced i t at_i with ⟨q, member, fits⟩ | ⟨b, bIn, q, member, fits⟩
  · obtain ⟨_, _, _, _, which⟩ := header_patterns_shape member
    rcases which with ⟨-, object⟩ | version | imports
    · rw [declaration_kind_ontology t.object (by rw [fits.2.2, object])] at kindRun
      cases Result.ok_injective kindRun
    · have := fits.2.1; rw [version, typed] at this; simp [rdfType, owlVersionIRI] at this
    · have := fits.2.1; rw [imports, typed] at this; simp [rdfType, owlImports] at this
  · obtain ⟨main, side, -, sides, facts, rfl | inSide⟩ := block_pattern (images b bIn) member
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
      obtain ⟨ax, axIn, axIs', -⟩ := (images b bIn).member
      exact ⟨ax, axIn, by rw [axIs', axIs, same]⟩
    · obtain ⟨y, -, about⟩ := (sides q inSide).2
      have subject := fits.1
      rw [isIri, about] at subject
      simp [subjectView] at subject

/-- Every declaration axiom of the ontology has its type triple in the graph. -/
theorem graph_declaration_present {o : model.RawOntology} {triples : List rdf.Triple} {bs : List Block}
    (axiomsIs : bs.map (fun b => (⟨alloc.vec.Vec.new _, b.ax⟩ : model.AnnotatedAxiom)) = o.axioms.val)
    (images : ∀ b ∈ bs, ImageBlock o b ∧ At triples b.pos b.pats) {ax : model.AnnotatedAxiom} (axIn : ax ∈ o.axioms.val)
    {e : model.Entity} (isDecl : ax.axiom = .Declaration e) :
    ∃ (i : Nat) (t : rdf.Triple), triples[i]? = some t ∧ Matches (declarationPattern e) t := by
  rw [← axiomsIs] at axIn
  obtain ⟨b, bIn, rfl⟩ := List.mem_map.mp axIn
  simp only at isDecl
  obtain ⟨image, holds⟩ := images b bIn
  obtain ⟨s1, tax⟩ := image.forward
  rw [isDecl] at tax
  simp only [Block.pos, At] at holds
  generalize b.pats = pats at tax holds
  generalize b.fresh ++ s1 = s0 at tax
  cases tax with
  | declaration =>
    obtain ⟨⟨t, at_t, fits⟩, -⟩ := List.forall₂_cons.mp holds
    exact ⟨b.main, t, at_t, fits⟩
  | characteristic _ _ _ _ _ _ _ ct _ => simp [characteristicType] at ct

/-- The kinds that the declarations of the graph give are those the ontology gives. -/
theorem graph_kinds {o : model.RawOntology} (triples : alloc.vec.Vec rdf.Triple) {bs : List Block}
    (sourced : Sourced triples.val (headerPatterns o) bs)
    (axiomsIs : bs.map (fun b => (⟨alloc.vec.Vec.new _, b.ax⟩ : model.AnnotatedAxiom)) = o.axioms.val)
    (images : ∀ b ∈ bs, ImageBlock o b ∧ At triples.val b.pos b.pats) (count : Usize) (positive : 0 < count.val)
    (kinds : rdf_mapping.Kinds) (at_end : KindsAt triples.val count triples.val.length kinds) :
    KindsOf kinds o.axioms.val := by
  intro iri kind
  rw [has_kind_correct triples.val count positive kinds at_end iri.spelling kind]
  congr 1
  apply decide_eq_decide.mpr
  unfold Typed
  apply or_congr_left
  constructor
  · rintro ⟨i, t, at_i, v, run, vIs⟩
    obtain ⟨ax, axIn, isDecl⟩ := graph_declares sourced (fun b m => (images b m).1) at_i run
    refine ⟨ax, axIn, ?_⟩
    rw [isDecl, vec_eq_of_val vIs]
  · rintro ⟨ax, axIn, isDecl⟩
    obtain ⟨i, t, at_i, fits⟩ := graph_declaration_present axiomsIs images axIn isDecl
    obtain ⟨v, kind', run, same⟩ := declares_of_declaration _ t fits
    obtain ⟨rfl, rfl⟩ := entity_of_injective same
    exact ⟨i, t, at_i, _, run, rfl⟩

/-! ### The header -/

theorem about_iri_correct (t : rdf.Triple) (ontology : alloc.vec.Vec U8) :
    rdf_mapping.about_iri t ontology = .ok (decide (subjectView t.subject = .iri ontology.val)) := by
  rw [rdf_mapping.about_iri]
  cases subject : t.subject with
  | Iri iri =>
    simp only [same_vec_correct, subjectView, Node.iri.injEq]
    by_cases h : iri.spelling = ontology
    · simp [h]
    · have h' : iri.spelling.val ≠ ontology.val := fun e => h (vec_eq_of_val e)
      simp [h, h']
  | Blank _ => simp [subjectView]

theorem property_kind_other {kinds : rdf_mapping.Kinds} {axioms : List model.AnnotatedAxiom} (hk : KindsOf kinds axioms)
    {iri : model.Iri} (other : ¬ AnnotationOnly axioms iri) :
    ∃ r, rdf_mapping.property_kind kinds iri.spelling = .ok r ∧ r ≠ some .Annotation := by
  rw [rdf_mapping.property_kind]
  simp only [hk iri .ObjectProperty, hk iri .DataProperty, hk iri .AnnotationProperty, bind_ok]
  unfold AnnotationOnly at other
  by_cases o : Typed axioms iri .ObjectProperty <;> by_cases d : Typed axioms iri .DataProperty <;>
    by_cases a : Typed axioms iri .AnnotationProperty <;> simp_all

/-- From `index` on, every unused triple about the ontology IRI is no part of the
    header: its predicate is neither `owl:versionIRI` nor `owl:imports` nor an
    annotation property only. -/
def HeaderSkip (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (ontology : alloc.vec.Vec U8)
    (used : List Bool) (index : Nat) : Prop :=
  ∀ (i : Nat) (t : rdf.Triple), index ≤ i → triples.val[i]? = some t → used[i]? = some false →
    subjectView t.subject = .iri ontology.val → t.predicate.spelling.val ≠ owlVersionIRI ∧
      t.predicate.spelling.val ≠ owlImports ∧
      ∃ r, rdf_mapping.property_kind kinds t.predicate.spelling = .ok r ∧ r ≠ some .Annotation

theorem header_skip_mono {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {ontology : alloc.vec.Vec U8} {used used' : List Bool} {index index' : Nat}
    (h : HeaderSkip triples kinds ontology used index)
    (back : ∀ (i : Nat), used'[i]? = some false → used[i]? = some false)
    (le : index ≤ index') : HeaderSkip triples kinds ontology used' index' :=
  fun i t low at_i unused about => h i t (by omega) at_i (back i unused) about

/-- The header reader passes over the triples that are no part of the header. -/
theorem header_parts_skip (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8) (version : Option model.Iri) (imports : alloc.vec.Vec model.Iri)
    (annotations : alloc.vec.Vec model.Annotation) (s : rdf_mapping.State) :
    ∀ (index : Usize), HeaderSkip triples kinds ontology s.used.val index.val →
      rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
        .ok (some (version, imports, annotations, s)) := by
  intro index
  induction e : triples.val.length - index.val generalizing index with
  | zero =>
    intro _
    have done : ¬ index.val < triples.val.length := by omega
    rw [rdf_mapping.header_parts]; simp [UScalar.lt_equiv, done]
  | succ n ih =>
    intro skip
    have more : index.val < triples.val.length := by omega
    have at_t : triples.val[index.val]? = some triples.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := triples.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have rest := ih next (by omega) (header_skip_mono skip (fun _ h => h) (by omega))
    rw [rdf_mapping.header_parts]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok, advance, rest]
    by_cases unused : s.used.val[index.val]? = some false
    · simp only [unused, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        alloc.vec.Vec.index_slice_index, main_lookup triples index _ at_t, bind_ok, about_iri_correct]
      by_cases about : subjectView triples.val[index.val].subject = .iri ontology.val
      · obtain ⟨notVersion, notImports, r, kindRun, notAnnotation⟩ :=
          skip index.val _ (le_refl _) at_t unused about
        simp only [owlVersionIRI] at notVersion
        simp only [owlImports] at notImports
        simp only [about, decide_true, ↓reduceIte, lift, bind_ok, same_correct, array_slice_val, notVersion,
          notImports, decide_false, Bool.false_eq_true, kindRun]
        rcases r with _ | k
        · simp [advance, rest]
        · cases k with
          | Object => simp [advance, rest]
          | Data => simp [advance, rest]
          | Annotation => exact absurd rfl notAnnotation
      · simp [about, advance, rest]
    · simp [unused, advance, rest]

/-- The header reader takes the imports, in order. -/
theorem header_parts_imports (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8) (version : Option model.Iri) (annotations : alloc.vec.Vec model.Annotation) :
    ∀ (js : List model.Iri) (index : Usize) (s : rdf_mapping.State) (imports : alloc.vec.Vec model.Iri),
      (∀ (k : Nat) (hk : k < js.length), ∃ t, triples.val[index.val + k]? = some t ∧
        subjectView t.subject = .iri ontology.val ∧ t.predicate.spelling.val = owlImports ∧
        objectView t.object = iriNode js[k] ∧ s.used.val[index.val + k]? = some false) →
      HeaderSkip triples kinds ontology s.used.val (index.val + js.length) →
      imports.val.length + js.length ≤ Usize.max →
      ∃ v s', rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
        .ok (some (version, v, annotations, s')) ∧ v.val = imports.val ++ js ∧
        Marked s s' (fun i => index.val ≤ i ∧ i < index.val + js.length) [] := by
  intro js
  induction js with
  | nil =>
    intro index s imports _ skip _
    refine ⟨imports, s, header_parts_skip triples kinds ontology version imports annotations s index
      (by simpa using skip), by simp, marked_same (marked_refl s) (fun i => by simp)⟩
  | cons j js ih =>
    intro index s imports at_js skip room
    obtain ⟨t, at_t, about, predicate, object, unused⟩ := at_js 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at at_t unused object
    have more : index.val < triples.val.length := (List.getElem?_eq_some_iff.mp at_t).1
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := triples.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have importsRoom : imports.val.length < Usize.max := by simp at room; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec imports j importsRoom)
    have mTake := marked_take s index
    obtain ⟨v, s', run, vIs, marked⟩ := ih next { s with used := s.used.set index true } pushed
      (by
        intro k hk
        obtain ⟨t', at', about', predicate', object', unused'⟩ := at_js (k + 1) (by simp; omega)
        have shift : index.val + (k + 1) = next.val + k := by omega
        rw [shift] at at' unused'
        refine ⟨t', at', about', predicate', by simpa using object', ?_⟩
        apply marked_unused mTake unused'
        intro h
        omega)
      (header_skip_mono skip (fun i h => marked_back mTake h) (by simp; omega))
      (by rw [contents]; simp at room ⊢; omega)
    refine ⟨v, s', ?_, by rw [vIs, contents]; simp, ?_⟩
    · rw [rdf_mapping.header_parts]
      have predicate' := predicate
      simp only [owlImports] at predicate'
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, unused, ne_eq,
        not_true_eq_false, decide_false, Bool.false_eq_true, bind_ok, alloc.vec.Vec.index_slice_index,
        main_lookup triples index t at_t, about_iri_correct, about, decide_true, lift, same_correct, array_slice_val,
        predicate']
      simp [node_iri_complete t.object j object, usize_max_val, importsRoom, push, advance, take_correct, run]
    · refine marked_same (marked_trans mTake marked) (fun i => ?_)
      rw [nextIs]
      simp only [List.length_cons]
      omega

/-- The header reader takes the version IRI. -/
theorem header_parts_version (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8) (imports : alloc.vec.Vec model.Iri) (annotations : alloc.vec.Vec model.Annotation)
    (index next : Usize) (s : rdf_mapping.State) (t : rdf.Triple) (at_t : triples.val[index.val]? = some t)
    (unused : s.used.val[index.val]? = some false) (about : subjectView t.subject = .iri ontology.val)
    (predicate : t.predicate.spelling.val = owlVersionIRI) (v : model.Iri) (object : objectView t.object = iriNode v)
    (advance : (index + 1#usize : Result Usize) = .ok next) :
    rdf_mapping.header_parts triples kinds ontology index s none imports annotations =
      rdf_mapping.header_parts triples kinds ontology next { s with used := s.used.set index true } (some v) imports
        annotations := by
  have more : index.val < triples.val.length := (List.getElem?_eq_some_iff.mp at_t).1
  rw [rdf_mapping.header_parts]
  have predicate' := predicate
  simp only [owlVersionIRI] at predicate'
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, unused, ne_eq,
    not_true_eq_false, decide_false, Bool.false_eq_true, bind_ok, alloc.vec.Vec.index_slice_index,
    main_lookup triples index t at_t, about_iri_correct, about, decide_true, lift, same_correct, array_slice_val,
    predicate']
  simp [node_iri_complete t.object v object, advance, take_correct]

/-- The header reader passes over a used triple. -/
theorem header_parts_used (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (ontology : alloc.vec.Vec U8) (version : Option model.Iri) (imports : alloc.vec.Vec model.Iri)
    (annotations : alloc.vec.Vec model.Annotation) (index next : Usize) (s : rdf_mapping.State)
    (more : index.val < triples.val.length) (used : s.used.val[index.val]? = some true)
    (advance : (index + 1#usize : Result Usize) = .ok next) :
    rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
      rdf_mapping.header_parts triples kinds ontology next s version imports annotations := by
  rw [rdf_mapping.header_parts]
  simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, is_used_correct, used, advance]

/-! ### The mapping of a graph of the forward mapping -/

theorem forall2_at : ∀ (ps : List Pattern) (ts : List rdf.Triple) (start : Nat),
    List.Forall₂ Matches ps (ts.drop start) → At ts (List.range' start ps.length) ps
  | [], _, _, _ => by simp [At]
  | p :: ps, ts, start, h => by
    rw [List.length_cons, List.range'_succ]
    have inside : start < ts.length := by
      apply Classical.byContradiction
      intro outside
      rw [List.drop_eq_nil_iff.mpr (by omega)] at h
      cases h
    rw [List.drop_eq_getElem_cons inside] at h
    obtain ⟨fits, rest⟩ := List.forall₂_cons.mp h
    refine List.Forall₂.cons ⟨ts[start], List.getElem?_eq_getElem inside, fits⟩ ?_
    exact forall2_at ps ts (start + 1) (by simpa using rest)

theorem fresh_unique {bs : List Block} (nodup : (bs.flatMap Block.fresh).Nodup) {b c : Block} (hb : b ∈ bs)
    (hc : c ∈ bs) {y : rdf.BlankNode} (yb : y ∈ b.fresh) (yc : y ∈ c.fresh) : b = c := by
  apply Classical.byContradiction
  intro different
  have pairwise := (List.nodup_flatMap.mp nodup).2
  have symm : Std.Symm (Function.onFun List.Disjoint Block.fresh) := ⟨fun _ _ h => List.Disjoint.symm h⟩
  exact pairwise.forall hb hc different yb yc

/-- A blank node of the supply that is the subject of a triple of a block is a
    blank node of the block. -/
theorem block_subject_fresh {o : model.RawOntology} {c : Block} (image : ImageBlock o c) {t : rdf.Triple}
    {q : Pattern} (member : q ∈ c.pats) (fits : Matches q t) {y : rdf.BlankNode}
    (about : subjectView t.subject = .blank y)
    (notAnonymous : ∀ an, subjectAnonymous c.ax = some an → (⟨an.scope, an.label⟩ : rdf.BlankNode) ≠ y) :
    y ∈ c.fresh := by
  obtain ⟨main, side, -, sides, facts, rfl | inSide⟩ := block_pattern image member
  · rcases facts.blank y (fits.1.symm.trans about) with inside | ⟨an, isSome, same⟩
    · exact inside
    · exact absurd same.symm (notAnonymous an isSome)
  · obtain ⟨z, inside, subject⟩ := (sides q inSide).2
    rw [← fits.1, about] at subject
    simp only [Node.blank.injEq] at subject
    rw [subject]
    exact inside

theorem taxioms_count {axs : List model.AnnotatedAxiom} {s0 : Supply} {ps : List Pattern} {s1 : Supply}
    (h : TAxioms axs s0 ps s1) (plain : ∀ ax ∈ axs, ax.annotations.val = []) : s0.length ≤ s1.length + ps.length := by
  induction h with
  | nil => simp
  | cons ax rest s s1 s2 p q head tail ih =>
    have := taxiom_count (plain_axiom head (plain ax (by simp)))
    have := ih (fun b m => plain b (List.mem_cons_of_mem _ m))
    simp only [List.length_append]
    omega

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

theorem at_nth {triples : List rdf.Triple} {ps : List Pattern} {start : Nat}
    (h : At triples (List.range' start ps.length) ps) :
    ∀ (k : Nat) (hk : k < ps.length), ∃ t, triples[start + k]? = some t ∧ Matches ps[k] t := by
  intro k hk
  obtain ⟨_, t, at_t, fits⟩ := at_get h (k := k) (i := start + k) (by simp [List.getElem?_range', hk])
  exact ⟨t, at_t, fits⟩

/-- No triple of the graph types an anonymous individual that an annotation
    assertion is about with a type of Table 8. -/
theorem graph_not_reifier {o : model.RawOntology} {triples : List rdf.Triple} {bs : List Block}
    (sourced : Sourced triples (headerPatterns o) bs) (images : ∀ b ∈ bs, ImageBlock o b) {supply : Supply}
    (inSupply : ∀ b ∈ bs, ∀ y ∈ b.fresh, y ∈ supply) (fresh : FreshSupply o supply) {p : model.AnnotationProperty}
    {sub : model.AnnotationSubject} {v : model.AnnotationValue}
    (axIn : ∃ ax ∈ o.axioms.val, ax.axiom = .AnnotationAssertion p sub v) :
    ∀ x, annotationSubjectNode sub = .blank x → ∀ (i : Nat) (t : rdf.Triple), triples[i]? = some t →
      subjectView t.subject = .blank x → t.predicate.spelling.val = rdfType →
      ∀ K ∈ reifierTypes, objectView t.object ≠ .iri K := by
  intro x node i t at_i about typed K member same
  obtain ⟨ax, axIn, axIs⟩ := axIn
  cases sub with
  | Iri _ => simp [annotationSubjectNode, iriNode] at node
  | Anonymous an =>
    simp only [annotationSubjectNode, anonymousNode, Node.blank.injEq] at node
    subst node
    have notIn := fresh ax axIn an (by rw [axIs]; rfl)
    rcases sourced i t at_i with ⟨q, qIn, fits⟩ | ⟨c, cIn, q, qIn, fits⟩
    · obtain ⟨iri, -, -, subject, -⟩ := header_patterns_shape qIn
      rw [fits.1, subject] at about
      simp [iriNode] at about
    · obtain ⟨main, side, -, sides, facts, rfl | inSide⟩ := block_pattern (images c cIn) qIn
      · exact facts.reifier _ (fits.1.symm.trans about) (fun inC => notIn (inSupply c cIn _ inC))
          (by rw [← fits.2.1]; exact typed) K member (by rw [← fits.2.2]; exact same)
      · obtain ⟨y, yIn, subject⟩ := (sides q inSide).2
        rw [← fits.1, about] at subject
        simp only [Node.blank.injEq] at subject
        rw [subject] at notIn
        exact notIn (inSupply c cIn y yIn)

/-- **The reverse RDF mapping reads back every readable ontology.** For an
    ontology that the reverse mapping reads back (`ReadableOntology`), a graph
    that lists, in order, the triples of its forward mapping (`TOntology`) with
    blank nodes distinct from each other and from the anonymous individuals the
    assertions are about (`FreshSupply`) is mapped to exactly that ontology, with
    exactly those blank nodes. -/
theorem map_graph_complete (graph : rdf.RawGraph) (o : model.RawOntology) (supply : Supply)
    (patterns : List Pattern) (readable : ReadableOntology o) (forward : TOntology o supply patterns)
    (distinct : supply.Nodup) (fresh : FreshSupply o supply)
    (image : List.Forall₂ Matches patterns graph.triples.val) :
    ∃ m, rdf_mapping.map_graph graph = .ok (some m) ∧ m.ontology = o ∧ m.blanks.val = supply := by
  obtain ⟨header, axiomPs, rest, theader, taxioms, split⟩ := forward
  obtain ⟨headerIs, restIs⟩ := header_of readable.annotations theader
  rw [restIs] at taxioms
  subst headerIs
  have lengthEq : graph.triples.val.length = patterns.length := (List.Forall₂.length_eq image).symm
  have holdsAll : At graph.triples.val (List.range' 0 patterns.length) patterns :=
    forall2_at patterns graph.triples.val 0 (by simpa using image)
  rw [split, List.length_append, ← List.range'_append_1] at holdsAll
  obtain ⟨holdsH, holdsA⟩ := at_append_inv holdsAll (by simp)
  simp only [Nat.zero_add] at holdsA
  obtain ⟨bs, mapIs, freshIs, sorted, disjoint, each, covers⟩ :=
    forward_blocks readable graph.triples taxioms (fun ax m => m) (headerPatterns o).length holdsA
  simp only [List.append_nil] at freshIs
  have lengthSum : graph.triples.val.length = (headerPatterns o).length + axiomPs.length := by
    rw [lengthEq, split, List.length_append]
  have total : graph.triples.val.length ≤ Usize.max := graph.triples.property
  have images : ∀ b ∈ bs, ImageBlock o b := fun b m => (each b m).1
  have imagesAt : ∀ b ∈ bs, ImageBlock o b ∧ At graph.triples.val b.pos b.pats :=
    fun b m => ⟨(each b m).1, (each b m).2.1⟩
  have sourced : Sourced graph.triples.val (headerPatterns o) bs := by
    intro i t at_i
    have inside : i < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
    by_cases inHeader : i < (headerPatterns o).length
    · exact Or.inl (at_mem holdsH (by simp [List.mem_range'_1]; omega) at_i)
    · obtain ⟨c, cIn, ic⟩ := covers i (by omega) (by omega)
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
    obtain ⟨image, holds, nodupPos, -, -⟩ := each b m
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
  -- the axiom loop from a state where exactly the header is used
  have loop : ∀ st : rdf_mapping.State,
      SubjectsComplete graph.triples.val st.subjects.val (alloc.vec.Vec.len st.subjects) graph.triples.val.length →
      (∀ x ∈ st.sources.val, x.val = []) → st.used.val.length = graph.triples.val.length →
      (∀ (i : Nat), i < graph.triples.val.length → (st.used.val[i]? = some false ↔ (headerPatterns o).length ≤ i)) →
      st.blanks.val = [] →
      ∃ v s', rdf_mapping.axioms_from graph.triples kinds 0#usize st (alloc.vec.Vec.new _) = .ok (some (v, s')) ∧
        v.val = o.axioms.val ∧ s'.blanks.val = supply ∧
        ∀ (i : Nat), i < graph.triples.val.length → s'.used.val[i]? = some true := by
    intro st completeSt sourcesSt lengthSt usedSt blanksSt
    have state : LoopState graph.triples st bs :=
      { complete := completeSt
        sources := sourcesSt
        length := lengthSt
        free := fun b m i inB => by
          have := (each b m).2.2.2.2 i inB
          exact (usedSt i (by omega)).mpr this.1
        covered := fun i unused => by
          have inside : i < graph.triples.val.length := by
            rw [← lengthSt]; exact (List.getElem?_eq_some_iff.mp unused).1
          have low := (usedSt i inside).mp unused
          exact covers i low (by omega)
        owns := fun b m i t y at_i unused about inB => by
          have inside : i < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
          have low := (usedSt i inside).mp unused
          obtain ⟨c, cIn, ic⟩ := covers i low (by omega)
          obtain ⟨q, qIn, fits⟩ := at_mem (each c cIn).2.1 ic at_i
          have yInC := block_subject_fresh (images c cIn) qIn fits about (by
            intro an isSome same
            obtain ⟨ax, axIn, axIs, -⟩ := (images c cIn).member
            have notIn := fresh ax axIn an (by rw [axIs]; exact isSome)
            rw [same] at notIn
            exact notIn (inSupply b m y inB))
          rw [fresh_unique freshNodup m cIn inB yInC]
          exact ic
        room := by
          rw [blanksSt, ← freshIs]
          simp
          omega }
    have axiomsCount : bs.length ≤ Usize.max := by
      have := o.axioms.property
      have lengths : bs.length = o.axioms.val.length := by rw [← mapIs, List.length_map]
      omega
    obtain ⟨v, s', run, vIs, blanksIs, allUsed⟩ := axioms_loop graph.triples kinds _ 0#usize bs st
      (alloc.vec.Vec.new _) rfl ok sorted disjoint (fun b m => by simp) (fun b m i inRest before => by
        have := (each b m).2.2.2.1 i inRest
        omega) state (by simp; omega)
    refine ⟨v, s', run, by rw [vIs, ← mapIs]; simp, by rw [blanksIs, blanksSt, ← freshIs]; simp, allUsed⟩
  -- the header
  cases identity : o.identity with
  | Anonymous =>
    have headerNil : headerPatterns o = [] := by simp [headerPatterns, identity]
    have headerRun : rdf_mapping.find_header graph.triples v1 0#usize = .ok none := by
      apply find_header_none
      intro i t _ at_i typed onto iri isIri
      exact graph_no_ontology identity sourced images i t at_i typed onto iri isIri
    obtain ⟨v, s', axiomsRun, vIs, blanksIs, allUsed⟩ := loop
      { used := v1, blanks := alloc.vec.Vec.new _, subjects := v3, sources := v2 } complete v2Empty
      (by simp [v1Is])
      (fun i hi => by simp [v1Is, List.getElem?_replicate, hi, headerNil])
      (by simp)
    have allRun := all_read_used graph.triples s'.used 0#usize (fun i _ hi => allUsed i hi)
    refine ⟨⟨⟨.Anonymous, alloc.vec.Vec.new _, alloc.vec.Vec.new _, v⟩, s'.blanks⟩, ?_, ?_, blanksIs⟩
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
    · obtain ⟨identity', imports, annotations, axioms⟩ := o
      simp only at identity readable ⊢
      subst identity
      have importsNil : imports.val = [] := by
        cases theader with
        | anonymous _ _ importsEmpty _ => exact importsEmpty
      have annotationsNil : annotations.val = [] := readable.annotations
      simp only [model.RawOntology.mk.injEq, true_and]
      refine ⟨vec_eq_of_val (by simp [importsNil]), vec_eq_of_val (by simp [annotationsNil]),
        vec_eq_of_val (by simpa using vIs)⟩
  | Named iri version =>
    -- the triple typing the ontology IRI, first
    have typingAt := at_nth holdsH 0 (by simp [headerPatterns, identity])
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
    let st0 : rdf_mapping.State := { used := v1, blanks := alloc.vec.Vec.new _, subjects := v3, sources := v2 }
    let st1 : rdf_mapping.State := { st0 with used := st0.used.set 0#usize true }
    have m01 : Marked st0 st1 (fun i => i < 1) [] := marked_same (marked_take st0 0#usize) (fun i => by simp)
    -- every triple about the ontology IRI after the header is no part of it
    have skip : ∀ (used : List Bool), HeaderSkip graph.triples kinds iri0.spelling used (headerPatterns o).length := by
      intro used i t low at_i _ about
      have inside : i < graph.triples.val.length := (List.getElem?_eq_some_iff.mp at_i).1
      obtain ⟨c, cIn, ic⟩ := covers i low (by omega)
      obtain ⟨q, qIn, fits⟩ := at_mem (each c cIn).2.1 ic at_i
      have qSubject : q.subject = iriNode iri := by
        rw [← fits.1, about, spelled0]; rfl
      obtain ⟨main, side, -, sides, facts, rfl | inSide⟩ := block_pattern (images c cIn) qIn
      · obtain ⟨notVersion, notImports, notAnnotation⟩ := facts.header iri version identity qSubject
        rw [fits.2.1]
        refine ⟨notVersion, notImports, ?_⟩
        exact property_kind_other hk (iri := ⟨t.predicate.spelling⟩) (notAnnotation _ fits.2.1)
      · obtain ⟨y, -, subject⟩ := (sides q inSide).2
        rw [qSubject] at subject
        simp [iriNode] at subject
    -- the imports, then nothing more of the header
    have importsPhase : ∀ (index : Usize) (s : rdf_mapping.State) (ver : Option model.Iri),
        index.val + o.imports.val.length = (headerPatterns o).length →
        (∀ (k : Nat) (hk : k < o.imports.val.length), ∃ t, graph.triples.val[index.val + k]? = some t ∧
          Matches ⟨iriNode iri, owlImports, iriNode o.imports.val[k]⟩ t) →
        Marked st0 s (fun i => i < index.val) [] →
        ∃ v s', rdf_mapping.header_parts graph.triples kinds iri0.spelling index s ver (alloc.vec.Vec.new _)
          (alloc.vec.Vec.new _) = .ok (some (ver, v, alloc.vec.Vec.new _, s')) ∧ v.val = o.imports.val ∧
          Marked st0 s' (fun i => i < (headerPatterns o).length) [] := by
      intro index s ver ends importsAt marked
      obtain ⟨v, s', run, vIs, marked'⟩ := header_parts_imports graph.triples kinds iri0.spelling ver
        (alloc.vec.Vec.new _) o.imports.val index s (alloc.vec.Vec.new _)
        (by
          intro k hk
          obtain ⟨t, at_t, fits⟩ := importsAt k hk
          refine ⟨t, at_t, by rw [fits.1, spelled0]; rfl, fits.2.1, fits.2.2, ?_⟩
          apply marked_unused marked (by simp [st0, v1Is, List.getElem?_replicate]; omega)
          simp)
        (by rw [ends]; exact skip s.used.val)
        (by simp)
      refine ⟨v, s', run, by simpa using vIs, marked_same (marked_trans marked marked') (fun i => ?_)⟩
      omega
    -- the header read
    obtain ⟨ver, imp, sH, partsRun, impIs, mH, verIs⟩ : ∃ (ver : Option model.Iri) (imp : alloc.vec.Vec model.Iri)
        (sH : rdf_mapping.State), rdf_mapping.header_parts graph.triples kinds iri0.spelling 0#usize st1 none
          (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) = .ok (some (ver, imp, alloc.vec.Vec.new _, sH)) ∧
        imp.val = o.imports.val ∧ Marked st0 sH (fun i => i < (headerPatterns o).length) [] ∧ ver = version := by
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
        obtain ⟨v, s', run, vIs, marked⟩ := importsPhase 1#usize st1 none (by rw [hdr]; simp; omega)
          (by
            intro k hk
            obtain ⟨t, at_t, fits⟩ := at_nth holdsH (k + 1) (by rw [hdr]; simp; omega)
            simp only [hdr, List.getElem_cons_succ, List.getElem_map] at fits
            exact ⟨t, by simpa [Nat.add_comm] using at_t, fits⟩)
          m01
        exact ⟨none, v, s', run, vIs, marked, rfl⟩
      | some vIri =>
        have hdr : headerPatterns o = ⟨iriNode iri, rdfType, .iri owlOntology⟩ ::
            ⟨iriNode iri, owlVersionIRI, iriNode vIri⟩ ::
            o.imports.val.map (fun i => ⟨iriNode iri, owlImports, iriNode i⟩) := by
          simp [headerPatterns, identity, versionIs]
        obtain ⟨t1, at1, fits1⟩ := at_nth holdsH 1 (by rw [hdr]; simp)
        simp only [hdr, List.getElem_cons_succ, List.getElem_cons_zero] at fits1
        have one' : (1#usize : Usize).val = 1 := by simp
        have two : (1#usize + 1#usize : Result Usize) = .ok 2#usize := by
          obtain ⟨n, run, value⟩ := WP.spec_imp_exists (Usize.add_spec (x := 1#usize) (y := 1#usize) (by scalar_tac))
          have same : n = 2#usize := UScalar.eq_of_val_eq (by simp at value ⊢; exact value)
          rw [run, same]
        have unused1 : st1.used.val[(1#usize : Usize).val]? = some false := by
          rw [one']
          apply marked_unused m01 (by simp [st0, v1Is, List.getElem?_replicate]; rw [hdr] at lengthSum; simp at lengthSum; omega)
          simp
        rw [header_parts_version graph.triples kinds iri0.spelling _ _ 1#usize 2#usize st1 t1 (by rw [one']; simpa using at1)
          unused1 (by rw [fits1.1, spelled0]; rfl) fits1.2.1 vIri fits1.2.2 two]
        have m12 : Marked st0 { st1 with used := st1.used.set 1#usize true } (fun i => i < 2) [] :=
          marked_same (marked_trans m01 (marked_take st1 1#usize)) (fun i => by simp; omega)
        obtain ⟨v, s', run, vIs, marked⟩ := importsPhase 2#usize _ (some vIri) (by rw [hdr]; simp; omega)
          (by
            intro k hk
            obtain ⟨t, at_t, fits⟩ := at_nth holdsH (k + 2) (by rw [hdr]; simp; omega)
            simp only [hdr, List.getElem_cons_succ, List.getElem_map] at fits
            exact ⟨t, by simpa [Nat.add_comm] using at_t, fits⟩)
          m12
        exact ⟨some vIri, v, s', run, vIs, marked, rfl⟩
    -- the axioms
    obtain ⟨v, s', axiomsRun, vIs, blanksIs, allUsed⟩ := loop sH (by rw [mH.subjects]; exact complete)
      (by rw [mH.sources]; exact v2Empty) (by rw [mH.length]; simp [st0, v1Is])
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
    refine ⟨⟨⟨.Named ⟨iri0.spelling⟩ ver, imp, alloc.vec.Vec.new _, v⟩, s'.blanks⟩, ?_, ?_, blanksIs⟩
    · rw [rdf_mapping.map_graph]
      simp only [countRun, bind_ok, kindBucketsRun, kindsRun, unusedRun, bucketsRun, subjectsRun, sourcesRun,
        headerRun, alloc.vec.Vec.index_slice_index, main_lookup graph.triples 0#usize t0 (by rw [z]; simpa using at0),
        isIri0, take_correct]
      have partsRun' : rdf_mapping.header_parts graph.triples kinds iri0.spelling 0#usize
          { used := v1.set 0#usize true, blanks := alloc.vec.Vec.new rdf.BlankNode, subjects := v3, sources := v2 }
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
    · obtain ⟨identity', imports, annotations, axioms⟩ := o
      simp only at identity readable impIs vIs ⊢
      subst identity verIs
      have annotationsNil : annotations.val = [] := readable.annotations
      simp only [model.RawOntology.mk.injEq, model.OntologyIdentity.Named.injEq, and_true]
      refine ⟨iri_ext (by rw [spelled0]), vec_eq_of_val impIs, vec_eq_of_val (by simp [annotationsNil]),
        vec_eq_of_val vIs⟩

end Rowl.RdfReadOntology
