import Rowl.FunctionalModel
import Rowl.AlcOntology

/-!
Answers for Functional Syntax source bytes, proved end to end. The proved
document reader, the proved mapping into the raw OWL model and the proved ALC
queries compose into one extracted function from the original bytes to an
answer. An error is exactly the reader's first error. Every document the reader
accepts maps to a raw OWL ontology that corresponds to its source records, and
the result is then the kernel's query on those axioms: no answer means the
axioms or the query are outside the supported fragment, and an answer is exact
for the OWL 2 Direct Semantics of the axioms.
-/
namespace Rowl.SourceReasoning
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open RowlRust.functional_document (SourceDocument DocumentLimits DocumentError read_document)
open RowlRust.functional_prefixes (read_prefix_header)
open Rowl.FunctionalDocument (TailRun WithPrefixes)
open Rowl.FunctionalModel (OntologyModel document_ontology_correct)
open Rowl.Owl (DatatypeMap Vocabulary IsVocabulary Consistent ClassSatisfiable Subsumed)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
universe u v w

/-- A document read from source bytes: its prefix header parsed from the same
    bytes, its namespace table accepted by the normative checker, and everything
    after `Ontology(` derived by the independent document grammar with exactly
    those namespace rows. -/
def Read (bytes : alloc.vec.Vec U8) (limits : DocumentLimits) (document : SourceDocument) : Prop :=
  ∃ opening table,
    read_prefix_header bytes limits.tokens limits.prefixes limits.prefix_value = .ok (.Ok opening) ∧
    prefixes.check opening.declarations = .ok (.Ready table) ∧
    document.prefixes = opening.declarations ∧
    TailRun opening.declarations.val bytes.val bytes.len limits.imports.val limits.iri.val
      limits.annotations.count.val limits.annotations.iri.val limits.annotations.lexical.val
      limits.annotations.depth.val limits.classes.count.val limits.classes.iri.val limits.classes.depth.val
      limits.axioms.val opening.remaining (.Ok document.tail)
/-- The raw OWL ontology of source bytes: the model of a document read from them,
    with node IDs as anonymous individuals of the caller's scope. -/
def SourceOntology (bytes : alloc.vec.Vec U8) (limits : DocumentLimits) (scope : alloc.vec.Vec U8)
    (ontology : RawOntology) : Prop :=
  ∃ document, Read bytes limits document ∧ OntologyModel scope document.tail ontology

/-- Every document the actual reader accepts is read from the bytes. -/
theorem read_document_read (bytes : alloc.vec.Vec U8) (limits : DocumentLimits) (document : SourceDocument)
    (accepted : read_document bytes limits = .ok (.Ok document)) : Read bytes limits document := by
  obtain ⟨header,headerRead,_⟩ :=
    Rowl.FunctionalPrefixes.read_prefix_header_total_correct bytes limits.tokens limits.prefixes limits.prefix_value
  cases header with
  | Err error =>
    rw [Rowl.FunctionalDocument.read_document_prefix_error bytes limits error headerRead] at accepted
    cases Result.ok_injective accepted
  | Ok opening =>
    cases checked : Rowl.Prefixes.Scan opening.declarations [] opening.declarations.val with
    | Ready table =>
      have checkRead : prefixes.check opening.declarations = .ok (.Ready table) := by
        rw [Rowl.Prefixes.check_total_correct,checked]
      obtain ⟨tail,run,same⟩ := (Rowl.FunctionalDocument.read_document_result_iff bytes limits opening table
        headerRead checkRead (.Ok document)).mp accepted
      cases tail with
      | Err error => cases same
      | Ok tail =>
        cases same
        exact ⟨opening,table,headerRead,checkRead,rfl,run⟩
    | _ =>
      rw [Rowl.FunctionalDocument.read_document_table_error bytes limits opening _ headerRead
        (by rw [Rowl.Prefixes.check_total_correct,checked]) (by intro table impossible; cases impossible)] at accepted
      cases Result.ok_injective accepted

/-- The mapping never declines a document the reader accepts: every read
    document has a raw OWL ontology. -/
theorem read_document_maps (bytes : alloc.vec.Vec U8) (limits : DocumentLimits) (scope : alloc.vec.Vec U8)
    (document : SourceDocument) (accepted : read_document bytes limits = .ok (.Ok document)) :
    ∃ ontology, functional_model.document_ontology document scope = .ok (some ontology) ∧
      SourceOntology bytes limits scope ontology := by
  have read := read_document_read bytes limits document accepted
  obtain ⟨_,_,_,_,_,run⟩ := read
  obtain ⟨result,mapped,correct,total⟩ := document_ontology_correct document scope
  cases result with
  | none => exact absurd (total (Rowl.FunctionalModel.tail_run_shaped run rfl)) (by simp)
  | some ontology =>
    exact ⟨ontology,mapped,document,read_document_read bytes limits document accepted,correct ontology rfl⟩

/-- Every stage before the query: reading terminates with the reader's exact
    result, and an accepted document maps to a raw OWL ontology of the bytes. -/
private theorem pipeline (bytes : alloc.vec.Vec U8) (limits : DocumentLimits) (scope : alloc.vec.Vec U8) :
    (∃ error, read_document bytes limits = .ok (.Err error)) ∨
    ∃ document ontology, read_document bytes limits = .ok (.Ok document) ∧
      functional_model.document_ontology document scope = .ok (some ontology) ∧
      SourceOntology bytes limits scope ontology := by
  obtain ⟨read,readRun⟩ := Rowl.FunctionalDocument.read_document_total bytes limits
  cases read with
  | Err error => exact .inl ⟨error,readRun⟩
  | Ok document =>
    obtain ⟨ontology,mapped,source⟩ := read_document_maps bytes limits scope document readRun
    exact .inr ⟨document,ontology,readRun,mapped,source⟩

/-- Consistency from source bytes always terminates. An error is exactly the
    reader's first error; otherwise the result is the kernel's consistency query
    on the raw OWL ontology of the bytes, and an answer is exactly whether its
    axioms have an OWL model. -/
theorem source_consistent_correct (bytes : alloc.vec.Vec U8) (limits : DocumentLimits) (scope : alloc.vec.Vec U8) :
    ∃ result, source_reasoning.source_consistent bytes limits scope = .ok result ∧
      (∀ error, result = .Err error ↔ read_document bytes limits = .ok (.Err error)) ∧
      (∀ answer, result = .Ok answer → ∃ ontology, SourceOntology bytes limits scope ontology ∧
        alc_ontology.consistent ontology.axioms = .ok answer) ∧
      ∀ answer, result = .Ok (some answer) → ∃ ontology, SourceOntology bytes limits scope ontology ∧
        ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary), IsVocabulary D V →
          (answer = true ↔ Consistent.{u, max w v, w} D V ontology.axioms.val) := by
  rcases pipeline bytes limits scope with ⟨error,readRun⟩ | ⟨document,ontology,readRun,mappedRun,source⟩
  · refine ⟨.Err error,by simp [source_reasoning.source_consistent,readRun],?_,?_,?_⟩
    · intro other; simp [readRun]
    · intro answer impossible; cases impossible
    · intro answer impossible; cases impossible
  · obtain ⟨answered,answeredRun,_,semantic⟩ := Rowl.AlcOntology.consistent_correct.{u,v,w} ontology.axioms
    refine ⟨.Ok answered,by simp [source_reasoning.source_consistent,readRun,mappedRun,answeredRun],?_,?_,?_⟩
    · intro error; simp [readRun]
    · intro answer same
      cases same
      exact ⟨ontology,source,answeredRun⟩
    · intro answer same
      cases same
      exact ⟨ontology,source,semantic answer rfl⟩
/-- A consistency answer from source bytes is complete for OWL models in every
    universe: if the axioms of the bytes' raw OWL ontology have a model, the
    answer is `true`. -/
theorem source_consistent_complete (bytes : alloc.vec.Vec U8) (limits : DocumentLimits) (scope : alloc.vec.Vec U8)
    (answer : Bool) (answered : source_reasoning.source_consistent bytes limits scope = .ok (.Ok (some answer))) :
    ∃ ontology, SourceOntology bytes limits scope ontology ∧
      ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        Consistent.{u,v,w} D V ontology.axioms.val → answer = true := by
  rcases pipeline bytes limits scope with ⟨error,readRun⟩ | ⟨document,ontology,readRun,mappedRun,source⟩
  · simp [source_reasoning.source_consistent,readRun] at answered
  · obtain ⟨result,resultRun,_,_⟩ := Rowl.AlcOntology.consistent_correct.{0,0,0} ontology.axioms
    simp [source_reasoning.source_consistent,readRun,mappedRun,resultRun] at answered
    subst answered
    exact ⟨ontology,source,
      fun D V consistent => Rowl.AlcOntology.consistent_complete.{u,v,w} ontology.axioms answer resultRun D V consistent⟩

/-- Class satisfiability from source bytes always terminates. An error is
    exactly the reader's first error; otherwise the result is the kernel's
    satisfiability query on the raw OWL ontology of the bytes, and an answer is
    exactly whether some OWL model of its axioms has an instance of the
    expression. -/
theorem source_class_satisfiable_correct (bytes : alloc.vec.Vec U8) (limits : DocumentLimits)
    (scope : alloc.vec.Vec U8) (e : ClassExpression) :
    ∃ result, source_reasoning.source_class_satisfiable bytes limits scope e = .ok result ∧
      (∀ error, result = .Err error ↔ read_document bytes limits = .ok (.Err error)) ∧
      (∀ answer, result = .Ok answer → ∃ ontology, SourceOntology bytes limits scope ontology ∧
        alc_ontology.class_satisfiable ontology.axioms e = .ok answer) ∧
      ∀ answer, result = .Ok (some answer) → ∃ ontology, SourceOntology bytes limits scope ontology ∧
        ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary), IsVocabulary D V →
          (answer = true ↔ ClassSatisfiable.{u, max w v, w} D V ontology.axioms.val e) := by
  rcases pipeline bytes limits scope with ⟨error,readRun⟩ | ⟨document,ontology,readRun,mappedRun,source⟩
  · refine ⟨.Err error,by simp [source_reasoning.source_class_satisfiable,readRun],?_,?_,?_⟩
    · intro other; simp [readRun]
    · intro answer impossible; cases impossible
    · intro answer impossible; cases impossible
  · obtain ⟨answered,answeredRun,_,semantic⟩ := Rowl.AlcOntology.class_satisfiable_correct.{u,v,w} ontology.axioms e
    refine ⟨.Ok answered,by simp [source_reasoning.source_class_satisfiable,readRun,mappedRun,answeredRun],
      ?_,?_,?_⟩
    · intro error; simp [readRun]
    · intro answer same
      cases same
      exact ⟨ontology,source,answeredRun⟩
    · intro answer same
      cases same
      exact ⟨ontology,source,semantic answer rfl⟩
/-- A satisfiability answer from source bytes is complete for OWL models in
    every universe: if some model of the axioms of the bytes' raw OWL ontology
    has an instance of the expression, the answer is `true`. -/
theorem source_class_satisfiable_complete (bytes : alloc.vec.Vec U8) (limits : DocumentLimits)
    (scope : alloc.vec.Vec U8) (e : ClassExpression) (answer : Bool)
    (answered : source_reasoning.source_class_satisfiable bytes limits scope e = .ok (.Ok (some answer))) :
    ∃ ontology, SourceOntology bytes limits scope ontology ∧
      ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        ClassSatisfiable.{u,v,w} D V ontology.axioms.val e → answer = true := by
  rcases pipeline bytes limits scope with ⟨error,readRun⟩ | ⟨document,ontology,readRun,mappedRun,source⟩
  · simp [source_reasoning.source_class_satisfiable,readRun] at answered
  · obtain ⟨result,resultRun,_,_⟩ := Rowl.AlcOntology.class_satisfiable_correct.{0,0,0} ontology.axioms e
    simp [source_reasoning.source_class_satisfiable,readRun,mappedRun,resultRun] at answered
    subst answered
    exact ⟨ontology,source,fun D V satisfiable =>
      Rowl.AlcOntology.class_satisfiable_complete.{u,v,w} ontology.axioms e answer resultRun D V satisfiable⟩

/-- Subsumption from source bytes always terminates. An error is exactly the
    reader's first error; otherwise the result is the kernel's subsumption query
    on the raw OWL ontology of the bytes, and an answer is exactly whether every
    instance of `sub` is an instance of `sup` in every OWL model of its axioms. -/
theorem source_subsumed_correct (bytes : alloc.vec.Vec U8) (limits : DocumentLimits) (scope : alloc.vec.Vec U8)
    (sub sup : ClassExpression) :
    ∃ result, source_reasoning.source_subsumed bytes limits scope sub sup = .ok result ∧
      (∀ error, result = .Err error ↔ read_document bytes limits = .ok (.Err error)) ∧
      (∀ answer, result = .Ok answer → ∃ ontology, SourceOntology bytes limits scope ontology ∧
        alc_ontology.subsumed ontology.axioms sub sup = .ok answer) ∧
      ∀ answer, result = .Ok (some answer) → ∃ ontology, SourceOntology bytes limits scope ontology ∧
        ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary), IsVocabulary D V →
          (answer = true ↔ Subsumed.{u, max w v, w} D V ontology.axioms.val sub sup) := by
  rcases pipeline bytes limits scope with ⟨error,readRun⟩ | ⟨document,ontology,readRun,mappedRun,source⟩
  · refine ⟨.Err error,by simp [source_reasoning.source_subsumed,readRun],?_,?_,?_⟩
    · intro other; simp [readRun]
    · intro answer impossible; cases impossible
    · intro answer impossible; cases impossible
  · obtain ⟨answered,answeredRun,_,semantic⟩ := Rowl.AlcOntology.subsumed_correct.{u,v,w} ontology.axioms sub sup
    refine ⟨.Ok answered,by simp [source_reasoning.source_subsumed,readRun,mappedRun,answeredRun],?_,?_,?_⟩
    · intro error; simp [readRun]
    · intro answer same
      cases same
      exact ⟨ontology,source,answeredRun⟩
    · intro answer same
      cases same
      exact ⟨ontology,source,semantic answer rfl⟩
/-- A positive subsumption answer from source bytes is sound for OWL models in
    every universe. -/
theorem source_subsumed_sound (bytes : alloc.vec.Vec U8) (limits : DocumentLimits) (scope : alloc.vec.Vec U8)
    (sub sup : ClassExpression)
    (answered : source_reasoning.source_subsumed bytes limits scope sub sup = .ok (.Ok (some true))) :
    ∃ ontology, SourceOntology bytes limits scope ontology ∧
      ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary), Subsumed.{u,v,w} D V ontology.axioms.val sub sup := by
  rcases pipeline bytes limits scope with ⟨error,readRun⟩ | ⟨document,ontology,readRun,mappedRun,source⟩
  · simp [source_reasoning.source_subsumed,readRun] at answered
  · obtain ⟨result,resultRun,_,_⟩ := Rowl.AlcOntology.subsumed_correct.{0,0,0} ontology.axioms sub sup
    simp [source_reasoning.source_subsumed,readRun,mappedRun,resultRun] at answered
    subst answered
    exact ⟨ontology,source,
      fun D V => Rowl.AlcOntology.subsumed_sound.{u,v,w} ontology.axioms sub sup resultRun D V⟩
end Rowl.SourceReasoning
