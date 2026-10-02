import Rowl.Internalization

/-!
Ontology-level answers for ALC axiom closures, proved against the independent
Direct Semantics: consistency, class satisfiability and subsumption. Every
answer the kernel gives is exact for the OWL definitions: an acceptance comes
with an actual OWL model of the closure (built from the tableau's model, with
the built-in classes, properties and the datatype map fixed as OWL requires),
and every OWL model, in any universe, forces acceptance.
-/
namespace Rowl.AlcOntology
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation classDenote thing nothing topObject bottomObject topData bottomData
  literalDatatype DatatypeMap ValueEmbedding Vocabulary IsVocabulary IsInterpretation Model Consistent
  ClassSatisfiable Subsumed withAnonymous)
open Rowl.Nnf (conceptDenote Fixes nnf_total_correct nnf_meaning fixes_of_interpretation)
open Rowl.Internalization (internalize_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v w

/-- No built-in class occurs as a named class and no built-in object property
    as a role, so the tableau's reading of every name is an ordinary one. -/
def Proper : nnf.NnfConcept → Prop
  | .Top => True
  | .Bottom => True
  | .Atom c => c ≠ thing ∧ c ≠ nothing
  | .NotAtom c => c ≠ thing ∧ c ≠ nothing
  | .And a b => Proper a ∧ Proper b
  | .Or a b => Proper a ∧ Proper b
  | .Exists r c => r ≠ topObject ∧ r ≠ bottomObject ∧ Proper c
  | .Forall r c => r ≠ topObject ∧ r ≠ bottomObject ∧ Proper c

private theorem equal_total (key : alloc.vec.Vec U8) (pattern : Slice U8)
    (equalLength : key.val.length = pattern.val.length) (index : Usize) :
    alc_ontology.equal_from key pattern index =
      .ok (decide (key.val.drop index.val = pattern.val.drop index.val)) := by
  rw [alc_ontology.equal_from]
  by_cases h : index.val < key.val.length
  · have hr : index.val < pattern.val.length := by omega
    have hkIndex : key.index_usize index = .ok key.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem h]
    have hpIndex : pattern.index_usize index = .ok pattern.val[index.val] := by
      simp [Slice.index_usize,List.getElem?_eq_getElem hr]
    by_cases heads : key.val[index.val] = pattern.val[index.val]
    · obtain ⟨next,hn,hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have ih := equal_total key pattern equalLength next
      simp [h,hkIndex,hpIndex,heads,hn,ih]
      rw [List.drop_eq_getElem_cons h,List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq,heads,true_and,nextval]
    · simp [h,hkIndex,hpIndex,heads]
      rw [List.drop_eq_getElem_cons h,List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq,heads,false_and,not_false_eq_true]
  · have hk : key.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hp : pattern.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [h,hk,hp]
termination_by key.val.length - index.val
decreasing_by omega
private theorem same_pattern_total (key : alloc.vec.Vec U8) (pattern : Slice U8) :
    alc_ontology.same_pattern key pattern = .ok (decide (key.val = pattern.val)) := by
  rw [alc_ontology.same_pattern]
  by_cases h : key.val.length = pattern.val.length
  · simpa [h] using equal_total key pattern h 0#usize
  · have unequal : key.val ≠ pattern.val := fun same => h (congrArg List.length same)
    simp [h,unequal]

/-- Exact recognition of the two built-in classes. -/
theorem builtin_class_correct (c : Class) :
    alc_ontology.builtin_class c = .ok (decide (c = thing ∨ c = nothing)) := by
  rw [alc_ontology.builtin_class]
  simp only [Rowl.Tableau.class_eq_iff c thing,Rowl.Tableau.class_eq_iff c nothing]
  by_cases top : c.iri.spelling.val = thing.iri.spelling.val <;>
    simp_all [same_pattern_total,Array.to_slice,Array.make,lift,thing,nothing]
/-- Exact recognition of the two built-in object properties. -/
theorem builtin_role_correct (r : ObjectProperty) :
    alc_ontology.builtin_role r = .ok (decide (r = topObject ∨ r = bottomObject)) := by
  rw [alc_ontology.builtin_role]
  simp only [Rowl.Tableau.property_eq_iff r topObject,Rowl.Tableau.property_eq_iff r bottomObject]
  by_cases top : r.iri.spelling.val = topObject.iri.spelling.val <;>
    simp_all [same_pattern_total,Array.to_slice,Array.make,lift,topObject,bottomObject]
/-- The kernel's check decides `Proper` exactly. -/
theorem proper_correct (c : nnf.NnfConcept) : alc_ontology.proper c = .ok (decide (Proper c)) := by
  induction c with
  | Top => rw [alc_ontology.proper]; simp [Proper]
  | Bottom => rw [alc_ontology.proper]; simp [Proper]
  | Atom k => rw [alc_ontology.proper]; simp [Proper,builtin_class_correct]
  | NotAtom k => rw [alc_ontology.proper]; simp [Proper,builtin_class_correct]
  | And a b iha ihb =>
    rw [alc_ontology.proper]
    by_cases left : Proper a <;> simp [Proper,iha,ihb,left]
  | Or a b iha ihb =>
    rw [alc_ontology.proper]
    by_cases left : Proper a <;> simp [Proper,iha,ihb,left]
  | Exists r c ih =>
    rw [alc_ontology.proper]
    by_cases top : r = topObject <;> by_cases bottom : r = bottomObject <;>
      simp [Proper,builtin_role_correct,ih,top,bottom]
  | Forall r c ih =>
    rw [alc_ontology.proper]
    by_cases top : r = topObject <;> by_cases bottom : r = bottomObject <;>
      simp [Proper,builtin_role_correct,ih,top,bottom]

/-- Reinterpreting anonymous individuals leaves every concept's meaning unchanged. -/
theorem concept_with_anonymous {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (assignment : AnonymousIndividual → Object) :
    ∀ c x, conceptDenote (withAnonymous I assignment) c x ↔ conceptDenote I c x := by
  intro c
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ => intro x; exact Iff.rfl
  | And a b iha ihb => intro x; simp only [conceptDenote,iha x,ihb x]
  | Or a b iha ihb => intro x; simp only [conceptDenote,iha x,ihb x]
  | Exists r c ih => intro x; simp only [conceptDenote,ih]; exact Iff.rfl
  | Forall r c ih => intro x; simp only [conceptDenote,ih]; exact Iff.rfl

/-- Native datatype values become distinct data values. -/
def embedding {Native : Type w} (D : DatatypeMap Native) : ValueEmbedding D (ULift.{v} (Option Native)) :=
  ⟨fun n => ULift.up (some n),fun _ _ _ _ same => by simpa using same⟩
/-- The OWL interpretation of a tableau model: the built-in classes and object
    and data properties get their fixed meaning, every other class and object
    property keeps the tableau's reading, and data values, datatypes, literals
    and facets come from the datatype map. -/
def owlModel {Object : Type} (J : Interpretation Object Unit) (root : Object) {Native : Type w}
    (D : DatatypeMap Native) : Interpretation (ULift.{u} Object) (ULift.{v} (Option Native)) where
  objectsNonempty := ⟨ULift.up root⟩
  dataNonempty := ⟨ULift.up none⟩
  classes k x := if k = thing then True else if k = nothing then False else J.classes k x.down
  objectProperties r x y :=
    if r = topObject then True else if r = bottomObject then False else J.objectProperties r x.down y.down
  dataProperties p _ _ := p = topData
  namedIndividuals _ := ULift.up root
  anonymousIndividuals _ := ULift.up root
  datatypes dt x := if dt = literalDatatype then True else ∃ y, D.valueSpace dt y ∧ ULift.up (some y) = x
  literals lt := ULift.up (some (D.lexicalValue lt.datatype lt.lexical.val))
  facets f x := ∃ y, D.facetValue f.facet (D.lexicalValue f.value.datatype f.value.lexical.val) y ∧
    ULift.up (some y) = x
  named _ := True

/-- The constructed interpretation satisfies every condition OWL places on an
    interpretation. -/
theorem owl_model_valid {Object : Type} (J : Interpretation Object Unit) (root : Object) {Native : Type w}
    (D : DatatypeMap Native) (V : Vocabulary) :
    IsInterpretation D (embedding.{v,w} D) V (owlModel.{u,v,w} J root D) := by
  have classes : nothing ≠ thing := by
    intro same
    have := congrArg (fun c : Class => c.iri.spelling.val) same
    simp [thing,nothing] at this
  have roles : bottomObject ≠ topObject := by
    intro same
    have := congrArg (fun r : ObjectProperty => r.iri.spelling.val) same
    simp [topObject,bottomObject] at this
  have data : bottomData ≠ topData := by
    intro same
    have := congrArg (fun p : DataProperty => p.iri.spelling.val) same
    simp [topData,bottomData] at this
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x; simp [owlModel]
  · intro x; simp [owlModel,classes]
  · intro x y; simp [owlModel]
  · intro x y; simp [owlModel,roles]
  · intro x y; simp [owlModel]
  · intro x y; simp [owlModel,data]
  · intro dt supported x
    have notLiteral : dt ≠ literalDatatype := fun same => D.excludesLiteral (same ▸ supported)
    simp [owlModel,notLiteral,embedding]
  · intro x; simp [owlModel]
  · intro lt _; rfl
  · intro f _ x; exact Iff.rfl
  · intro a _; trivial
/-- On proper concepts the constructed interpretation agrees with the tableau model. -/
theorem owl_model_agrees {Object : Type} (J : Interpretation Object Unit) (root : Object) {Native : Type w}
    (D : DatatypeMap Native) :
    ∀ c, Proper c → ∀ x, conceptDenote (owlModel.{u,v,w} J root D) c x ↔ conceptDenote J c x.down := by
  intro c
  induction c with
  | Top => intro _ x; simp [conceptDenote]
  | Bottom => intro _ x; simp [conceptDenote]
  | Atom k => intro proper x; simp [conceptDenote,owlModel,proper.1,proper.2]
  | NotAtom k => intro proper x; simp [conceptDenote,owlModel,proper.1,proper.2]
  | And a b iha ihb => intro proper x; simp only [conceptDenote,iha proper.1 x,ihb proper.2 x]
  | Or a b iha ihb => intro proper x; simp only [conceptDenote,iha proper.1 x,ihb proper.2 x]
  | Exists r c ih =>
    intro proper x
    simp only [conceptDenote,owlModel,proper.1,proper.2.1,↓reduceIte]
    constructor
    · rintro ⟨y,edge,inner⟩
      exact ⟨y.down,edge,(ih proper.2.2 y).mp inner⟩
    · rintro ⟨y,edge,inner⟩
      exact ⟨ULift.up y,edge,(ih proper.2.2 (ULift.up y)).mpr inner⟩
  | Forall r c ih =>
    intro proper x
    simp only [conceptDenote,owlModel,proper.1,proper.2.1,↓reduceIte]
    constructor
    · intro every y edge
      exact (ih proper.2.2 (ULift.up y)).mp (every (ULift.up y) edge)
    · intro every y edge
      exact (ih proper.2.2 y).mpr (every y.down edge)

/-- Every model of the closure is an interpretation fixing the built-in classes
    in which the closure's TBox concept holds at every element. -/
private theorem model_tbox {Object : Type u} {Value : Type v} {Native : Type w} {D : DatatypeMap Native}
    {embed : ValueEmbedding D Value} {V : Vocabulary} {I : Interpretation Object Value}
    {items : alloc.vec.Vec AnnotatedAxiom} {axioms : nnf.NnfConcept}
    (internalized : alc_ontology.internalize items = .ok (some axioms))
    (model : Model D embed V I items.val) : Fixes I ∧ ∀ x, conceptDenote I axioms x := by
  obtain ⟨_,valid,assignment,satisfied⟩ := model
  have fixes : Fixes I := fixes_of_interpretation valid
  obtain ⟨result,executed,_,meaning⟩ := internalize_correct.{u,v} items
  rw [internalized] at executed
  cases Result.ok_injective executed
  refine ⟨fixes,fun x => ?_⟩
  have everywhere := (meaning axioms rfl Object Value (withAnonymous I assignment) fixes).mp satisfied
  exact (concept_with_anonymous I assignment axioms x).mp (everywhere x)
/-- A tableau model of a proper TBox concept with an instance of a proper
    concept becomes an OWL model of the closure with an instance of the concept. -/
private theorem owl_model_of {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (vocabulary : IsVocabulary D V) (items : alloc.vec.Vec AnnotatedAxiom) (axioms concept : nnf.NnfConcept)
    (internalized : alc_ontology.internalize items = .ok (some axioms))
    (properAxioms : Proper axioms) (properConcept : Proper concept)
    {Object : Type} (J : Interpretation Object Unit) (everywhere : ∀ y, conceptDenote J axioms y)
    (x : Object) (holds : conceptDenote J concept x) :
    Model D (embedding.{v,w} D) V (owlModel.{u,v,w} J x D) items.val ∧
      conceptDenote (owlModel.{u,v,w} J x D) concept (ULift.up x) := by
  have valid := owl_model_valid.{u,v,w} J x D V
  have fixes : Fixes (owlModel.{u,v,w} J x D) := fixes_of_interpretation valid
  obtain ⟨result,executed,_,meaning⟩ := internalize_correct.{u, max w v} items
  rw [internalized] at executed
  cases Result.ok_injective executed
  refine ⟨⟨vocabulary,valid,(owlModel.{u,v,w} J x D).anonymousIndividuals,?_⟩,
    (owl_model_agrees J x D concept properConcept (ULift.up x)).mpr holds⟩
  apply (meaning axioms rfl _ _ (withAnonymous (owlModel.{u,v,w} J x D)
    (owlModel.{u,v,w} J x D).anonymousIndividuals) fixes).mpr
  intro y
  exact (concept_with_anonymous _ _ axioms y).mpr ((owl_model_agrees J x D axioms properAxioms y).mpr
    (everywhere y.down))

/-- Consistency of an ALC axiom closure: the kernel answers exactly when the
    closure is supported and its TBox concept is proper, and then the answer is
    whether the closure has an OWL model. -/
theorem consistent_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, alc_ontology.consistent items = .ok result ∧
      (result.isSome ↔ ∃ axioms, alc_ontology.internalize items = .ok (some axioms) ∧ Proper axioms) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ Consistent.{u, max w v, w} D V items.val) := by
  obtain ⟨internal,internalRead,_,_⟩ := internalize_correct.{0,0} items
  cases internal with
  | none =>
    refine ⟨none,by rw [alc_ontology.consistent]; simp [internalRead],by simp [internalRead],by simp⟩
  | some axioms =>
    by_cases properAxioms : Proper axioms
    · obtain ⟨accepted,acceptedRead,sound,complete⟩ := Rowl.TboxTableau.satisfiable_in_correct.{u, max w v} .Top axioms
      refine ⟨some accepted,by rw [alc_ontology.consistent]; simp [internalRead,proper_correct,properAxioms,
        acceptedRead],by simp [internalRead,properAxioms],?_⟩
      intro answer same Native D V vocabulary
      cases same
      constructor
      · intro yes
        obtain ⟨Object,J,everywhere,x,_⟩ := sound yes
        obtain ⟨model,_⟩ := owl_model_of.{u,v,w} D V vocabulary items axioms .Top internalRead properAxioms trivial
          J everywhere x trivial
        exact ⟨_,_,_,_,model⟩
      · rintro ⟨Object,Value,embed,I,model⟩
        obtain ⟨_,everywhere⟩ := model_tbox internalRead model
        obtain ⟨x⟩ := I.objectsNonempty
        exact complete ⟨Object,Value,I,everywhere,x,trivial⟩
    · refine ⟨none,by rw [alc_ontology.consistent]; simp [internalRead,proper_correct,properAxioms],
        by simp [internalRead,properAxioms],by simp⟩

/-- Class satisfiability with respect to an ALC axiom closure: the kernel answers
    exactly when the closure and the expression are supported and their
    translations are proper, and then the answer is whether some OWL model of the
    closure has an instance of the expression. -/
theorem class_satisfiable_correct (items : alloc.vec.Vec AnnotatedAxiom) (e : ClassExpression) :
    ∃ result, alc_ontology.class_satisfiable items e = .ok result ∧
      (result.isSome ↔ ∃ axioms concept, alc_ontology.internalize items = .ok (some axioms) ∧
        nnf.nnf e true = .ok (some concept) ∧ Proper axioms ∧ Proper concept) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ ClassSatisfiable.{u, max w v, w} D V items.val e) := by
  obtain ⟨internal,internalRead,_,_⟩ := internalize_correct.{0,0} items
  obtain ⟨translated,translatedRead,_⟩ := nnf_total_correct.{0,0} e true
  cases internal with
  | none =>
    refine ⟨none,by rw [alc_ontology.class_satisfiable]; simp [internalRead],by simp [internalRead],by simp⟩
  | some axioms =>
    cases translated with
    | none =>
      refine ⟨none,by rw [alc_ontology.class_satisfiable]; simp [internalRead,translatedRead],
        by simp [internalRead,translatedRead],by simp⟩
    | some concept =>
      by_cases properAxioms : Proper axioms
      · by_cases properConcept : Proper concept
        · obtain ⟨accepted,acceptedRead,sound,complete⟩ :=
            Rowl.TboxTableau.satisfiable_in_correct.{u, max w v} concept axioms
          refine ⟨some accepted,by rw [alc_ontology.class_satisfiable]; simp [internalRead,translatedRead,
            proper_correct,properAxioms,properConcept,acceptedRead],
            by simp [internalRead,translatedRead,properAxioms,properConcept],?_⟩
          intro answer same Native D V vocabulary
          cases same
          constructor
          · intro yes
            obtain ⟨Object,J,everywhere,x,holds⟩ := sound yes
            obtain ⟨model,instance'⟩ := owl_model_of.{u,v,w} D V vocabulary items axioms concept internalRead
              properAxioms properConcept J everywhere x holds
            have fixes := fixes_of_interpretation model.2.1
            exact ⟨_,_,_,_,model,ULift.up x,(nnf_meaning e true concept translatedRead _ fixes _).mp instance'⟩
          · rintro ⟨Object,Value,embed,I,model,x,member⟩
            obtain ⟨fixes,everywhere⟩ := model_tbox internalRead model
            exact complete ⟨Object,Value,I,everywhere,x,(nnf_meaning e true concept translatedRead I fixes x).mpr member⟩
        · refine ⟨none,by rw [alc_ontology.class_satisfiable]; simp [internalRead,translatedRead,proper_correct,
            properAxioms,properConcept],by simp [internalRead,translatedRead,properConcept],by simp⟩
      · refine ⟨none,by rw [alc_ontology.class_satisfiable]; simp [internalRead,translatedRead,proper_correct,
          properAxioms],by simp [internalRead,translatedRead,properAxioms],by simp⟩

/-- Subsumption with respect to an ALC axiom closure: the kernel answers exactly
    when the closure and both expressions are supported and the translations are
    proper, and then the answer is whether every instance of `sub` is an instance
    of `sup` in every OWL model of the closure. -/
theorem subsumed_correct (items : alloc.vec.Vec AnnotatedAxiom) (sub sup : ClassExpression) :
    ∃ result, alc_ontology.subsumed items sub sup = .ok result ∧
      (result.isSome ↔ ∃ axioms inside outside, alc_ontology.internalize items = .ok (some axioms) ∧
        nnf.nnf sub true = .ok (some inside) ∧ nnf.nnf sup false = .ok (some outside) ∧
        Proper axioms ∧ Proper (.And inside outside)) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ Subsumed.{u, max w v, w} D V items.val sub sup) := by
  obtain ⟨internal,internalRead,_,_⟩ := internalize_correct.{0,0} items
  obtain ⟨insideResult,insideRead,_⟩ := nnf_total_correct.{0,0} sub true
  obtain ⟨outsideResult,outsideRead,_⟩ := nnf_total_correct.{0,0} sup false
  cases internal with
  | none =>
    refine ⟨none,by rw [alc_ontology.subsumed]; simp [internalRead],by simp [internalRead],by simp⟩
  | some axioms =>
    cases insideResult with
    | none =>
      refine ⟨none,by rw [alc_ontology.subsumed]; simp [internalRead,insideRead],
        by simp [internalRead,insideRead],by simp⟩
    | some inside =>
      cases outsideResult with
      | none =>
        refine ⟨none,by rw [alc_ontology.subsumed]; simp [internalRead,insideRead,outsideRead],
          by simp [internalRead,insideRead,outsideRead],by simp⟩
      | some outside =>
        by_cases properAxioms : Proper axioms
        · by_cases properConcept : Proper (.And inside outside)
          · obtain ⟨accepted,acceptedRead,sound,complete⟩ :=
              Rowl.TboxTableau.satisfiable_in_correct.{u, max w v} (.And inside outside) axioms
            refine ⟨some (decide ¬ accepted = true),by rw [alc_ontology.subsumed]; simp [internalRead,insideRead,
              outsideRead,proper_correct,properAxioms,properConcept,acceptedRead],
              by simp [internalRead,insideRead,outsideRead,properAxioms,properConcept],?_⟩
            intro answer same Native D V vocabulary
            cases same
            cases accepted with
            | true =>
              obtain ⟨Object,J,everywhere,x,holds⟩ := sound rfl
              obtain ⟨model,instance'⟩ := owl_model_of.{u,v,w} D V vocabulary items axioms (.And inside outside)
                internalRead properAxioms properConcept J everywhere x holds
              have fixes := fixes_of_interpretation model.2.1
              constructor
              · intro impossible
                simp at impossible
              · intro subsumed
                exfalso
                have inSub := (nnf_meaning sub true inside insideRead _ fixes _).mp instance'.1
                have notSup := (nnf_meaning sup false outside outsideRead _ fixes _).mp instance'.2
                exact notSup (subsumed _ _ _ _ model _ inSub)
            | false =>
              constructor
              · intro _ Object Value embed I model x member
                obtain ⟨fixes,everywhere⟩ := model_tbox internalRead model
                by_contra outsideSup
                have accepted := complete ⟨Object,Value,I,everywhere,x,
                  (nnf_meaning sub true inside insideRead I fixes x).mpr member,
                  (nnf_meaning sup false outside outsideRead I fixes x).mpr outsideSup⟩
                cases accepted
              · intro _
                simp
          · refine ⟨none,by rw [alc_ontology.subsumed]; simp [internalRead,insideRead,outsideRead,proper_correct,
              properAxioms,properConcept],by simp [internalRead,insideRead,outsideRead,properConcept],by simp⟩
        · refine ⟨none,by rw [alc_ontology.subsumed]; simp [internalRead,insideRead,outsideRead,proper_correct,
            properAxioms],by simp [internalRead,insideRead,outsideRead,properAxioms],by simp⟩
/-- Any OWL model of the closure, in any universes and for any vocabulary, makes
    a consistency answer positive. -/
theorem consistent_complete (items : alloc.vec.Vec AnnotatedAxiom) (answer : Bool)
    (answered : alc_ontology.consistent items = .ok (some answer)) {Native : Type w} (D : DatatypeMap Native)
    (V : Vocabulary) (consistent : Consistent.{u,v,w} D V items.val) : answer = true := by
  obtain ⟨internal,internalRead,_,_⟩ := internalize_correct.{0,0} items
  rw [alc_ontology.consistent] at answered
  cases internal with
  | none => simp [internalRead] at answered
  | some axioms =>
    by_cases properAxioms : Proper axioms
    · obtain ⟨accepted,acceptedRead,_,complete⟩ := Rowl.TboxTableau.satisfiable_in_correct.{u,v} .Top axioms
      simp [internalRead,proper_correct,properAxioms,acceptedRead] at answered
      subst answered
      obtain ⟨Object,Value,embed,I,model⟩ := consistent
      obtain ⟨_,everywhere⟩ := model_tbox internalRead model
      obtain ⟨x⟩ := I.objectsNonempty
      exact complete ⟨Object,Value,I,everywhere,x,trivial⟩
    · simp [internalRead,proper_correct,properAxioms] at answered
/-- An instance of the expression in any OWL model of the closure, in any
    universes and for any vocabulary, makes a satisfiability answer positive. -/
theorem class_satisfiable_complete (items : alloc.vec.Vec AnnotatedAxiom) (e : ClassExpression) (answer : Bool)
    (answered : alc_ontology.class_satisfiable items e = .ok (some answer)) {Native : Type w}
    (D : DatatypeMap Native) (V : Vocabulary) (satisfiable : ClassSatisfiable.{u,v,w} D V items.val e) :
    answer = true := by
  obtain ⟨internal,internalRead,_,_⟩ := internalize_correct.{0,0} items
  obtain ⟨translated,translatedRead,_⟩ := nnf_total_correct.{0,0} e true
  rw [alc_ontology.class_satisfiable] at answered
  cases internal with
  | none => simp [internalRead] at answered
  | some axioms =>
    cases translated with
    | none => simp [internalRead,translatedRead] at answered
    | some concept =>
      by_cases properAxioms : Proper axioms
      · by_cases properConcept : Proper concept
        · obtain ⟨accepted,acceptedRead,_,complete⟩ := Rowl.TboxTableau.satisfiable_in_correct.{u,v} concept axioms
          simp [internalRead,translatedRead,proper_correct,properAxioms,properConcept,acceptedRead] at answered
          subst answered
          obtain ⟨Object,Value,embed,I,model,x,member⟩ := satisfiable
          obtain ⟨fixes,everywhere⟩ := model_tbox internalRead model
          exact complete ⟨Object,Value,I,everywhere,x,(nnf_meaning e true concept translatedRead I fixes x).mpr member⟩
        · simp [internalRead,translatedRead,proper_correct,properAxioms,properConcept] at answered
      · simp [internalRead,translatedRead,proper_correct,properAxioms] at answered
/-- A positive subsumption answer holds in every OWL model of the closure, in
    any universes and for any vocabulary. -/
theorem subsumed_sound (items : alloc.vec.Vec AnnotatedAxiom) (sub sup : ClassExpression)
    (answered : alc_ontology.subsumed items sub sup = .ok (some true)) {Native : Type w} (D : DatatypeMap Native)
    (V : Vocabulary) : Subsumed.{u,v,w} D V items.val sub sup := by
  obtain ⟨internal,internalRead,_,_⟩ := internalize_correct.{0,0} items
  obtain ⟨insideResult,insideRead,_⟩ := nnf_total_correct.{0,0} sub true
  obtain ⟨outsideResult,outsideRead,_⟩ := nnf_total_correct.{0,0} sup false
  rw [alc_ontology.subsumed] at answered
  cases internal with
  | none => simp [internalRead] at answered
  | some axioms =>
    cases insideResult with
    | none => simp [internalRead,insideRead] at answered
    | some inside =>
      cases outsideResult with
      | none => simp [internalRead,insideRead,outsideRead] at answered
      | some outside =>
        by_cases properAxioms : Proper axioms
        · by_cases properConcept : Proper (.And inside outside)
          · obtain ⟨accepted,acceptedRead,_,complete⟩ :=
              Rowl.TboxTableau.satisfiable_in_correct.{u,v} (.And inside outside) axioms
            simp [internalRead,insideRead,outsideRead,proper_correct,properAxioms,properConcept,acceptedRead]
              at answered
            intro Object Value embed I model x member
            obtain ⟨fixes,everywhere⟩ := model_tbox internalRead model
            by_contra outsideSup
            have yes := complete ⟨Object,Value,I,everywhere,x,
              (nnf_meaning sub true inside insideRead I fixes x).mpr member,
              (nnf_meaning sup false outside outsideRead I fixes x).mpr outsideSup⟩
            rw [answered] at yes
            cases yes
          · simp [internalRead,insideRead,outsideRead,proper_correct,properAxioms,properConcept] at answered
        · simp [internalRead,insideRead,outsideRead,proper_correct,properAxioms] at answered
end Rowl.AlcOntology
