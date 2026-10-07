import Rowl.ImportClosure

/-!
Functional Syntax documents lie in their scope.

The Functional Syntax reader maps every node ID to an anonymous individual of
the caller's scope (`FunctionalModel.AnonymousOf`). `ontology_model_scoped`
proves that every anonymous individual of the raw OWL ontology of a read
document, in its axioms, class expressions, annotations and ontology
annotations, has that scope (`AnonymousScopes.ScopedOntology`), so
`source_ontology_scoped` holds for every ontology read from Functional Syntax
bytes. Hence the scope check of `import_closure::assemble` never fails for a
catalog of Functional Syntax documents (`source_closure_functional_in_scope`):
for them the standardization apart of the import closure is proved, not only
checked.
-/
namespace Rowl.FunctionalScopes
open Aeneas Aeneas.Std RowlRust RowlRust.model
open RowlRust.functional_annotations (SourceAnnotation SourceAnnotationValue)
open RowlRust.functional_annotation_axioms (SourceAnnotationAxiomBody SourceAnnotationSubject)
open RowlRust.functional_individuals (SourceIndividual)
open RowlRust.functional_classes (SourceClass)
open RowlRust.functional_document (SourceAxiom SourceDocumentTail)
open RowlRust.import_catalog (Source)
open RowlRust.import_closure (Closure ClosureError)
open Rowl.FunctionalModel
open Rowl.AnonymousScopes
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

private theorem individual_scoped (scope : alloc.vec.Vec U8) (i : SourceIndividual) :
    ScopedIndividual scope.val (IndividualOf scope i) := by
  cases i <;> simp [IndividualOf, ScopedIndividual, AnonymousOf]

private theorem value_scoped (scope : alloc.vec.Vec U8) (v : SourceAnnotationValue) :
    ScopedValue scope.val (ValueOf scope v) := by
  cases v <;> simp [ValueOf, ScopedValue, AnonymousOf]

private theorem subject_scoped (scope : alloc.vec.Vec U8) (v : SourceAnnotationSubject) :
    ScopedSubject scope.val (SubjectOf scope v) := by
  cases v <;> simp [SubjectOf, ScopedSubject, AnonymousOf]

mutual
/-- Every class expression the mapping builds is scoped. -/
theorem class_model_scoped {scope : alloc.vec.Vec U8} :
    ∀ {src : SourceClass} {tgt : ClassExpression}, ClassModel scope src tgt → ScopedClass scope.val tgt
  | _, _, .named => by rw [ScopedClass]; trivial
  | _, _, .intersection inner => by
    obtain ⟨one, two, rest⟩ := members_model_scoped inner
    rw [ScopedClass]
    exact ⟨one, two, fun e => rest e.val e.property⟩
  | _, _, .union inner => by
    obtain ⟨one, two, rest⟩ := members_model_scoped inner
    rw [ScopedClass]
    exact ⟨one, two, fun e => rest e.val e.property⟩
  | _, _, .complement inner => by rw [ScopedClass]; exact class_model_scoped inner
  | _, _, .some inner => by rw [ScopedClass]; exact class_model_scoped inner
  | _, _, .all inner => by rw [ScopedClass]; exact class_model_scoped inner
  | _, _, .oneOf (members := members) (target := target) inner => by
    rw [ScopedClass]
    intro i member
    have inList : i ∈ members.val.map (IndividualOf scope) := by
      rw [← inner]; simpa [NonEmpty.elements] using member
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp inList
    exact individual_scoped scope m
  | _, _, .value => by rw [ScopedClass]; exact individual_scoped _ _
  | _, _, .self => by rw [ScopedClass]; trivial
  | _, _, .cardinality (bound := bound) => by
    cases bound <;> simp [CardinalityOf, ScopedClass]
  | _, _, .qualified (bound := bound) inner => by
    have filler := class_model_scoped inner
    cases bound <;> simp [CardinalityOf, ScopedClass, filler]
  | _, _, .dataSome _ => by rw [ScopedClass]; trivial
  | _, _, .dataAll _ => by rw [ScopedClass]; trivial
  | _, _, .dataValue => by rw [ScopedClass]; trivial
  | _, _, .dataCardinality (bound := bound) => by
    cases bound <;> simp [DataCardinalityOf, ScopedClass]
  | _, _, .dataQualified (bound := bound) _ => by
    cases bound <;> simp [DataCardinalityOf, ScopedClass]
/-- The members of a member list the mapping builds are scoped. -/
theorem members_model_scoped {scope : alloc.vec.Vec U8} :
    ∀ {srcs : List SourceClass} {tgt : AtLeastTwo ClassExpression}, MembersModel scope srcs tgt →
      ScopedClass scope.val tgt.first ∧ ScopedClass scope.val tgt.second ∧
        ∀ e ∈ tgt.rest.val, ScopedClass scope.val e
  | _, _, .mk one two others => ⟨class_model_scoped one, class_model_scoped two, rest_model_scoped others⟩
/-- The remaining members a list mapping builds are scoped. -/
theorem rest_model_scoped {scope : alloc.vec.Vec U8} :
    ∀ {srcs : List SourceClass} {tgts : List ClassExpression}, RestModel scope srcs tgts →
      ∀ e ∈ tgts, ScopedClass scope.val e
  | _, _, .nil => by simp
  | _, _, .cons head tail => by
    intro e member
    rcases List.mem_cons.mp member with same | later
    · rw [same]; exact class_model_scoped head
    · exact rest_model_scoped tail e later
end

private theorem elements_scoped {scope : alloc.vec.Vec U8} {srcs : List SourceClass}
    {tgt : AtLeastTwo ClassExpression} (h : MembersModel scope srcs tgt) :
    ∀ e ∈ tgt.elements, ScopedClass scope.val e := by
  obtain ⟨one, two, rest⟩ := members_model_scoped h
  intro e member
  simp only [AtLeastTwo.elements, List.mem_cons] at member
  rcases member with same | same | later
  · rw [same]; exact one
  · rw [same]; exact two
  · exact rest e later

mutual
/-- Every annotation the mapping builds, with its nested annotations, is scoped. -/
theorem annotation_model_scoped {scope : alloc.vec.Vec U8} :
    ∀ {src : SourceAnnotation} {tgt : Annotation}, AnnotationModel scope src tgt → ScopedAnnotation scope.val tgt
  | _, _, .mk (value := value) inner => by
    rw [ScopedAnnotation]
    exact ⟨value_scoped scope value, fun nested => annotations_model_scoped inner nested.val nested.property⟩
/-- Every annotation of a sequence the mapping builds is scoped. -/
theorem annotations_model_scoped {scope : alloc.vec.Vec U8} :
    ∀ {srcs : List SourceAnnotation} {tgts : List Annotation}, AnnotationsModel scope srcs tgts →
      ∀ a ∈ tgts, ScopedAnnotation scope.val a
  | _, _, .nil => by simp
  | _, _, .cons head tail => by
    intro a member
    rcases List.mem_cons.mp member with same | later
    · rw [same]; exact annotation_model_scoped head
    · exact annotations_model_scoped tail a later
end

private theorem members_individuals_scoped (scope : alloc.vec.Vec U8) (members : List SourceIndividual)
    (target : AtLeastTwo Individual) (h : IndividualMembersModel scope members target) :
    ∀ i ∈ target.elements, ScopedIndividual scope.val i := by
  intro i member
  have inList : i ∈ members.map (IndividualOf scope) := by
    rw [← h]; simpa [AtLeastTwo.elements] using member
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp inList
  exact individual_scoped scope m

private theorem class_axiom_scoped {scope : alloc.vec.Vec U8}
    {src : RowlRust.functional_class_axioms.SourceClassAxiomBody} {tgt : Axiom}
    (h : ClassAxiomModel scope src tgt) : ScopedAxiom scope.val tgt := by
  cases h with
  | subClassOf one two => exact ⟨class_model_scoped one, class_model_scoped two⟩
  | equivalent inner => exact elements_scoped inner
  | disjoint inner => exact elements_scoped inner
  | disjointUnion inner => exact elements_scoped inner
  | domain inner => exact class_model_scoped inner
  | range inner => exact class_model_scoped inner

private theorem property_axiom_scoped (scope : List U8)
    {src : RowlRust.functional_property_axioms.SourcePropertyAxiomBody} {tgt : Axiom}
    (h : PropertyAxiomModel src tgt) : ScopedAxiom scope tgt := by
  cases h with
  | @characteristic characteristic property =>
    cases characteristic <;> simp [CharacteristicOf, ScopedAxiom]
  | _ => simp [ScopedAxiom]

private theorem data_axiom_scoped {scope : alloc.vec.Vec U8}
    {src : RowlRust.functional_data_axioms.SourceDataAxiomBody} {tgt : Axiom}
    (h : DataAxiomModel scope src tgt) : ScopedAxiom scope.val tgt := by
  cases h with
  | domain inner => exact class_model_scoped inner
  | key inner _ _ => exact class_model_scoped inner
  | _ => simp [ScopedAxiom]

private theorem assertion_scoped {scope : alloc.vec.Vec U8}
    {src : RowlRust.functional_assertions.SourceAssertionBody} {tgt : Axiom}
    (h : AssertionModel scope src tgt) : ScopedAxiom scope.val tgt := by
  cases h with
  | same inner => exact members_individuals_scoped scope _ _ inner
  | different inner => exact members_individuals_scoped scope _ _ inner
  | classAssertion inner => exact ⟨class_model_scoped inner, individual_scoped _ _⟩
  | propertyAssertion => exact ⟨individual_scoped _ _, individual_scoped _ _⟩
  | negativeAssertion => exact ⟨individual_scoped _ _, individual_scoped _ _⟩
  | dataAssertion => exact individual_scoped _ _
  | negativeDataAssertion => exact individual_scoped _ _

/-- Every axiom the mapping builds, with its annotations, is scoped. -/
theorem axiom_model_scoped {scope : alloc.vec.Vec U8} {src : SourceAxiom} {tgt : AnnotatedAxiom}
    (h : AxiomModel scope src tgt) : ScopedAnnotated scope.val tgt := by
  cases h with
  | declaration inner => exact ⟨annotations_model_scoped inner, by simp [ScopedAxiom]⟩
  | @annotation record annotations inner =>
    refine ⟨annotations_model_scoped inner, ?_⟩
    cases record.body <;>
      simp [AnnotationAxiomOf, ScopedAxiom, subject_scoped, value_scoped]
  | «class» inner body => exact ⟨annotations_model_scoped inner, class_axiom_scoped body⟩
  | property inner body => exact ⟨annotations_model_scoped inner, property_axiom_scoped _ body⟩
  | data inner body => exact ⟨annotations_model_scoped inner, data_axiom_scoped body⟩
  | assertion inner body => exact ⟨annotations_model_scoped inner, assertion_scoped body⟩

private theorem forall₂_scoped {scope : alloc.vec.Vec U8} :
    ∀ {srcs : List SourceAxiom} {tgts : List AnnotatedAxiom}, List.Forall₂ (AxiomModel scope) srcs tgts →
      ∀ item ∈ tgts, ScopedAnnotated scope.val item
  | _, _, .nil => by simp
  | _, _, .cons head tail => by
    intro item member
    rcases List.mem_cons.mp member with same | later
    · rw [same]; exact axiom_model_scoped head
    · exact forall₂_scoped tail item later

/-- The raw OWL ontology of a read Functional Syntax document is scoped by the
    caller's scope: annotations, axioms and their annotations. -/
theorem ontology_model_scoped {scope : alloc.vec.Vec U8} {tail : SourceDocumentTail} {o : RawOntology}
    (h : OntologyModel scope tail o) : ScopedOntology scope.val o := by
  obtain ⟨_, _, annotations, axioms⟩ := h
  exact ⟨annotations_model_scoped annotations, forall₂_scoped axioms⟩

/-- Every ontology read from Functional Syntax bytes in a scope is scoped by it. -/
theorem source_ontology_scoped {bytes : alloc.vec.Vec U8} {limits : functional_document.DocumentLimits}
    {scope : alloc.vec.Vec U8} {o : RawOntology} (read : Rowl.SourceReasoning.SourceOntology bytes limits scope o) :
    ScopedOntology scope.val o := by
  obtain ⟨document, _, model⟩ := read
  exact ontology_model_scoped model

/-- A catalog of Functional Syntax documents never fails the scope check: the
    assembled closure of its import closure is standardized apart by proof. -/
theorem source_closure_functional_in_scope (sources : alloc.vec.Vec Source) (root : Usize)
    (limits : functional_document.DocumentLimits) (all : ∀ s ∈ sources.val, s.format = .Functional)
    (result : core.result.Result Closure ClosureError)
    (ran : import_closure.source_closure sources root limits = .ok result) (d : Usize) :
    result ≠ .Err (.OutOfScope d) := by
  intro same
  subst same
  obtain ⟨docs, read, inside, _, _, closure, notScoped, _⟩ :=
    Rowl.ImportClosure.source_closure_correct sources root limits _ ran
  have dInside : d.val < docs.length := Rowl.ImportClosure.closure_inside _ _ _ inside closure
  obtain ⟨lengths, readAt⟩ := read
  have sInside : d.val < sources.val.length := by omega
  have readIt := readAt d.val (sources.val[d.val]'sInside) (docs[d.val]'dInside)
    (List.getElem?_eq_getElem sInside) (List.getElem?_eq_getElem dInside)
  have functional := all _ (List.getElem_mem sInside)
  have inScope : ScopedOntology (Rowl.ImportCatalog.scopeVec d.val).val (docs[d.val]'dInside) := by
    unfold Rowl.ImportCatalog.ReadAs at readIt
    rw [functional] at readIt
    exact source_ontology_scoped readIt
  have scopeIs : (Rowl.ImportCatalog.scopeVec d.val).val = Rowl.ImportCatalog.scopeOf d.val := by
    simp [Rowl.ImportCatalog.scopeVec]
  rw [scopeIs] at inScope
  exact notScoped _ (List.getElem?_eq_getElem dInside) inScope

end Rowl.FunctionalScopes
