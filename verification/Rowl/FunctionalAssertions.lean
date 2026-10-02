import Rowl.FunctionalClasses
import Rowl.FunctionalAnnotations

/-!
Functional Syntax class assertions and positive and negative object property
assertions, proved total and exact against an independent grammar that
composes the proved annotation, class-expression and object-property grammars
with an independent individual grammar. Every result and first error has its
independent derivation, and every derivation is the actual result.
-/
namespace Rowl.FunctionalAssertions
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional_assertions
open RowlRust.functional_classes (ClassError ClassLimits SourceClass SourceObjectProperty)
open RowlRust.functional_annotations (AnnotationLimits SourceAnnotations)
open RowlRust.functional_header (HeaderIri)
open RowlRust.functional_lexer RowlRust.functional
open Rowl.FunctionalLexer (TokenCount)
open Rowl.FunctionalClasses (ClassRun PropertyRun)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The three assertion keywords this stage reads. -/
def FormOf : Terminal → Option AssertionForm
  | .Keyword .ClassAssertion => some .Class
  | .Keyword .ObjectPropertyAssertion => some .Property
  | .Keyword .NegativeObjectPropertyAssertion => some .NegativeProperty
  | _ => none
/-- The two individual families: a named individual's IRI or a node ID. -/
def IndividualKindOf : Terminal → Option IndividualKind
  | .FullIri => some (.Named .Full)
  | .AbbreviatedIri => some (.Named .Abbreviated)
  | .NodeId => some .Anonymous
  | _ => none
/-- Independent first-terminal class required at each assertion position. -/
def Expected : AssertionExpected → Terminal → Prop
  | .Axiom, terminal => ∃ form, FormOf terminal = some form
  | .Open, terminal => terminal = .Open
  | .Individual, terminal => ∃ kind, IndividualKindOf terminal = some kind
  | .Close, terminal => terminal = .Close

theorem assertion_form_total_correct (terminal : Terminal) : assertion_form terminal = .ok (FormOf terminal) := by
  cases terminal <;> first | rfl | (rename_i keyword; cases keyword <;> rfl)
theorem individual_kind_total_correct (terminal : Terminal) :
    individual_kind terminal = .ok (IndividualKindOf terminal) := by
  cases terminal <;> rfl
theorem expected_terminal_total_correct (expected : AssertionExpected) (terminal : Terminal) :
    expected_terminal expected terminal = .ok (decide (Expected expected terminal)) := by
  cases expected <;> cases terminal <;> (try (rename_i keyword; cases keyword)) <;>
    simp [expected_terminal,Expected,assertion_form_total_correct,individual_kind_total_correct,FormOf,
      IndividualKindOf,core.option.Option.is_some]

/-- One syntax step: the first token must belong to the expected class. A
    missing token reports the original source length, a wrong one its start. -/
inductive TakeRun (eof : Usize) (expected : AssertionExpected) :
    Tokens → core.result.Result (Token × Tokens) AssertionError → Prop
  | empty : TakeRun eof expected .Empty (.Err (.Expected expected eof))
  | wrong (token : Token) (rest : Tokens) (different : ¬ Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Err (.Expected expected token.start))
  | taken (token : Token) (rest : Tokens) (accepted : Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Ok (token,rest))

theorem take_expected_total_correct (tokens : Tokens) (expected : AssertionExpected) (eof : Usize) :
    ∃ result, take_expected tokens expected eof = .ok result ∧ TakeRun eof expected tokens result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected expected eof),rfl,.empty⟩
  | Cons token rest =>
    by_cases accepted : Expected expected token.terminal
    · exact ⟨.Ok (token,rest),by simp [take_expected,expected_terminal_total_correct,accepted],.taken _ _ accepted⟩
    · exact ⟨.Err (.Expected expected token.start),by simp [take_expected,expected_terminal_total_correct,accepted],
        .wrong _ _ accepted⟩
private theorem take_run_unique {eof : Usize} {expected : AssertionExpected} {tokens : Tokens}
    {one two : core.result.Result (Token × Tokens) AssertionError}
    (first : TakeRun eof expected tokens one) (second : TakeRun eof expected tokens two) : one = two := by
  cases first <;> cases second <;> first | rfl | contradiction
theorem take_expected_result_iff (tokens : Tokens) (expected : AssertionExpected) (eof : Usize)
    (result : core.result.Result (Token × Tokens) AssertionError) :
    take_expected tokens expected eof = .ok result ↔ TakeRun eof expected tokens result := by
  obtain ⟨actual,executed,correct⟩ := take_expected_total_correct tokens expected eof
  constructor
  · intro output
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    have same := take_run_unique correct source
    simpa [same] using executed
theorem take_progress {eof : Usize} {expected : AssertionExpected} {tokens rest : Tokens} {token : Token}
    (taken : TakeRun eof expected tokens (.Ok (token,rest))) : TokenCount tokens = 1+TokenCount rest := by
  cases taken
  rfl

/-- Independent individual grammar: an IRI resolves through the checked prefix
    rows; a node ID keeps its exact label without `_:`. -/
inductive IndividualRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (SourceIndividual × Tokens) AssertionError → Prop
  | syntaxError {tokens : Tokens} {error : AssertionError} (failure : TakeRun eof .Individual tokens (.Err error)) :
      IndividualRun rows source eof limit tokens (.Err error)
  | iriError {token : Token} {rest : Tokens} {kind : functional_iris.SourceIriKind}
      {error : functional_iris.SourceIriError} (individualKind : IndividualKindOf token.terminal = some (.Named kind))
      (failure : Rowl.FunctionalIris.ErrorCorrect rows kind source token.start.val token.end.val limit error) :
      IndividualRun rows source eof limit (.Cons token rest) (.Err (.Iri error))
  | named {token : Token} {rest : Tokens} {kind : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8}
      (individualKind : IndividualKindOf token.terminal = some (.Named kind))
      (valueSource : Rowl.FunctionalIris.Success rows kind source token.start.val token.end.val limit value) :
      IndividualRun rows source eof limit (.Cons token rest) (.Ok (.Named ⟨token,value⟩,rest))
  | anonymousError {token : Token} {rest : Tokens} {error : functional_names.NameError}
      (individualKind : IndividualKindOf token.terminal = some .Anonymous)
      (failure : Rowl.FunctionalNames.ErrorCorrect .NodeId source token.start.val token.end.val limit error) :
      IndividualRun rows source eof limit (.Cons token rest) (.Err (.Anonymous error))
  | anonymous {token : Token} {rest : Tokens} {label : alloc.vec.Vec U8}
      (individualKind : IndividualKindOf token.terminal = some .Anonymous)
      (labelValue : Rowl.FunctionalNames.Correct .NodeId source token.start.val token.end.val limit (.Ok label)) :
      IndividualRun rows source eof limit (.Cons token rest) (.Ok (.Anonymous token label,rest))

/-- Individual reading is total; its fallback after a checked individual token is unreachable. -/
theorem read_individual_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) :
    ∃ result, read_individual table bytes tokens limit = .ok result ∧
      IndividualRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  obtain ⟨taken,takeRead,takeCorrect⟩ := take_expected_total_correct tokens .Individual bytes.len
  rw [read_individual]
  simp only [takeRead,bind_ok]
  cases taken with
  | Err error => exact ⟨.Err error,rfl,.syntaxError takeCorrect⟩
  | Ok pair =>
    obtain ⟨token,rest⟩ := pair
    cases takeCorrect with
    | taken _ _ accepted =>
      obtain ⟨kind,classified⟩ := accepted
      simp only [uncurry_apply_pair,individual_kind_total_correct,classified,bind_ok]
      cases kind with
      | Named family =>
        obtain ⟨result,executed,correct⟩ :=
          Rowl.FunctionalIris.resolve_span_total_correct table family bytes token.start token.end limit
        simp only [executed,bind_ok]
        cases result with
        | Ok value => exact ⟨.Ok (.Named ⟨token,value⟩,rest),rfl,.named classified correct⟩
        | Err error => exact ⟨.Err (.Iri error),rfl,.iriError classified correct⟩
      | Anonymous =>
        obtain ⟨result,executed,correct⟩ :=
          Rowl.FunctionalNames.read_span_total_correct .NodeId bytes token.start token.end limit
        simp only [executed,bind_ok]
        cases result with
        | Ok label => exact ⟨.Ok (.Anonymous token label,rest),rfl,.anonymous classified correct⟩
        | Err error => exact ⟨.Err (.Anonymous error),rfl,.anonymousError classified correct⟩
/-- Every exact individual and first error is equivalent to its independent derivation. -/
theorem read_individual_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize)
    (result : core.result.Result (SourceIndividual × Tokens) AssertionError) :
    read_individual table bytes tokens limit = .ok result ↔
      IndividualRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_individual_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | syntaxError failure =>
      have takeRead := (take_expected_result_iff tokens .Individual bytes.len _).mpr failure
      simp [read_individual,takeRead]
    | @iriError token rest kind error individualKind failure =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Individual bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,individualKind⟩)
      have iriRead := (Rowl.FunctionalIris.resolve_span_error_iff table kind bytes token.start token.end limit error).mpr failure
      simp [read_individual,takeRead,individual_kind_total_correct,individualKind,iriRead]
    | @named token rest kind value individualKind valueSource =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Individual bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,individualKind⟩)
      have iriRead := (Rowl.FunctionalIris.resolve_span_value_iff table kind bytes token.start token.end limit value).mpr valueSource
      simp [read_individual,takeRead,individual_kind_total_correct,individualKind,iriRead]
    | @anonymousError token rest error individualKind failure =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Individual bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,individualKind⟩)
      have labelRead := (Rowl.FunctionalNames.read_span_error_iff .NodeId bytes token.start token.end limit error).mpr failure
      simp [read_individual,takeRead,individual_kind_total_correct,individualKind,labelRead]
    | @anonymous token rest label individualKind labelValue =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Individual bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,individualKind⟩)
      have labelRead := (Rowl.FunctionalNames.read_span_accepted_iff .NodeId bytes token.start token.end limit label).mpr labelValue
      simp [read_individual,takeRead,individual_kind_total_correct,individualKind,labelRead]
/-- An accepted individual consumes exactly its one token. -/
theorem individual_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens rest : Tokens} {individual : SourceIndividual}
    (accepted : IndividualRun rows source eof limit tokens (.Ok (individual,rest))) :
    TokenCount tokens = 1+TokenCount rest := by
  cases accepted <;> rfl

/-- A class expression at an assertion position: the independent class grammar
    at the full nesting allowance, with its errors wrapped. -/
inductive ClassStep (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit depth : Nat) :
    Tokens → core.result.Result (SourceClass × Tokens) AssertionError → Prop
  | error {tokens : Tokens} {error : ClassError} (run : ClassRun rows source eof count limit depth tokens (.Err error)) :
      ClassStep rows source eof count limit depth tokens (.Err (.Class error))
  | ok {tokens rest : Tokens} {value : SourceClass}
      (run : ClassRun rows source eof count limit depth tokens (.Ok (value,rest))) :
      ClassStep rows source eof count limit depth tokens (.Ok (value,rest))
/-- An object property expression at an assertion position, with its errors wrapped. -/
inductive PropertyStep (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (SourceObjectProperty × Tokens) AssertionError → Prop
  | error {tokens : Tokens} {error : ClassError} (run : PropertyRun rows source eof limit tokens (.Err error)) :
      PropertyStep rows source eof limit tokens (.Err (.Class error))
  | ok {tokens rest : Tokens} {value : SourceObjectProperty}
      (run : PropertyRun rows source eof limit tokens (.Ok (value,rest))) :
      PropertyStep rows source eof limit tokens (.Ok (value,rest))
/-- An object property expression followed by its source and target individuals. -/
inductive EdgeRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens →
      core.result.Result ((SourceObjectProperty × SourceIndividual × SourceIndividual) × Tokens) AssertionError →
      Prop
  | propertyError {tokens : Tokens} {error : AssertionError}
      (property : PropertyStep rows source eof limit tokens (.Err error)) :
      EdgeRun rows source eof limit tokens (.Err error)
  | sourceError {tokens rest : Tokens} {property : SourceObjectProperty} {error : AssertionError}
      (propertyRun : PropertyStep rows source eof limit tokens (.Ok (property,rest)))
      (failure : IndividualRun rows source eof limit rest (.Err error)) :
      EdgeRun rows source eof limit tokens (.Err error)
  | targetError {tokens rest after : Tokens} {property : SourceObjectProperty} {subject : SourceIndividual}
      {error : AssertionError}
      (propertyRun : PropertyStep rows source eof limit tokens (.Ok (property,rest)))
      (sourceRun : IndividualRun rows source eof limit rest (.Ok (subject,after)))
      (failure : IndividualRun rows source eof limit after (.Err error)) :
      EdgeRun rows source eof limit tokens (.Err error)
  | ok {tokens rest after remaining : Tokens} {property : SourceObjectProperty} {subject object : SourceIndividual}
      (propertyRun : PropertyStep rows source eof limit tokens (.Ok (property,rest)))
      (sourceRun : IndividualRun rows source eof limit rest (.Ok (subject,after)))
      (targetRun : IndividualRun rows source eof limit after (.Ok (object,remaining))) :
      EdgeRun rows source eof limit tokens (.Ok ((property,subject,object),remaining))
/-- Independent assertion bodies after the axiom annotations, in source order:
    a class expression and an individual, or an object property expression and
    two individuals. -/
inductive BodyRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit depth : Nat) :
    AssertionForm → Tokens → core.result.Result (SourceAssertionBody × Tokens) AssertionError → Prop
  | classError {tokens : Tokens} {error : AssertionError}
      (classRun : ClassStep rows source eof count limit depth tokens (.Err error)) :
      BodyRun rows source eof count limit depth .Class tokens (.Err error)
  | individualError {tokens rest : Tokens} {value : SourceClass} {error : AssertionError}
      (classRun : ClassStep rows source eof count limit depth tokens (.Ok (value,rest)))
      (failure : IndividualRun rows source eof limit rest (.Err error)) :
      BodyRun rows source eof count limit depth .Class tokens (.Err error)
  | classAssertion {tokens rest remaining : Tokens} {value : SourceClass} {individual : SourceIndividual}
      (classRun : ClassStep rows source eof count limit depth tokens (.Ok (value,rest)))
      (individualRun : IndividualRun rows source eof limit rest (.Ok (individual,remaining))) :
      BodyRun rows source eof count limit depth .Class tokens (.Ok (.ClassAssertion value individual,remaining))
  | propertyError {tokens : Tokens} {error : AssertionError}
      (edge : EdgeRun rows source eof limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .Property tokens (.Err error)
  | propertyAssertion {tokens remaining : Tokens} {property : SourceObjectProperty} {subject object : SourceIndividual}
      (edge : EdgeRun rows source eof limit tokens (.Ok ((property,subject,object),remaining))) :
      BodyRun rows source eof count limit depth .Property tokens
        (.Ok (.ObjectPropertyAssertion property subject object,remaining))
  | negativeError {tokens : Tokens} {error : AssertionError}
      (edge : EdgeRun rows source eof limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .NegativeProperty tokens (.Err error)
  | negativeAssertion {tokens remaining : Tokens} {property : SourceObjectProperty} {subject object : SourceIndividual}
      (edge : EdgeRun rows source eof limit tokens (.Ok ((property,subject,object),remaining))) :
      BodyRun rows source eof count limit depth .NegativeProperty tokens
        (.Ok (.NegativeObjectPropertyAssertion property subject object,remaining))

theorem read_class_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) :
    ∃ result, functional_assertions.read_class table bytes tokens limits = .ok result ∧
      ClassStep table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val tokens
        result := by
  obtain ⟨result,executed,correct⟩ := Rowl.FunctionalClasses.read_class_expression_total_correct table bytes tokens limits
  rw [functional_assertions.read_class]
  cases result with
  | Err error => exact ⟨.Err (.Class error),by simp [executed],.error correct⟩
  | Ok pair => exact ⟨.Ok pair,by simp [executed],.ok correct⟩
theorem read_class_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) (result : core.result.Result (SourceClass × Tokens) AssertionError) :
    functional_assertions.read_class table bytes tokens limits = .ok result ↔
      ClassStep table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val tokens
        result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_class_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [functional_assertions.read_class]
    cases source with
    | error run => simp [(Rowl.FunctionalClasses.read_class_expression_result_iff table bytes tokens limits _).mpr run]
    | ok run => simp [(Rowl.FunctionalClasses.read_class_expression_result_iff table bytes tokens limits _).mpr run]

theorem read_property_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limit : Usize) :
    ∃ result, read_property table bytes tokens limit = .ok result ∧
      PropertyStep table.declarations.val bytes.val bytes.len limit.val tokens result := by
  obtain ⟨result,executed,correct⟩ := Rowl.FunctionalClasses.read_object_property_total_correct table bytes tokens limit
  rw [read_property]
  cases result with
  | Err error => exact ⟨.Err (.Class error),by simp [executed],.error correct⟩
  | Ok pair => exact ⟨.Ok pair,by simp [executed],.ok correct⟩
theorem read_property_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limit : Usize) (result : core.result.Result (SourceObjectProperty × Tokens) AssertionError) :
    read_property table bytes tokens limit = .ok result ↔
      PropertyStep table.declarations.val bytes.val bytes.len limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_property_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_property]
    cases source with
    | error run => simp [(Rowl.FunctionalClasses.read_object_property_result_iff table bytes tokens limit _).mpr run]
    | ok run => simp [(Rowl.FunctionalClasses.read_object_property_result_iff table bytes tokens limit _).mpr run]

theorem read_edge_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) :
    ∃ result, read_edge table bytes tokens limits = .ok result ∧
      EdgeRun table.declarations.val bytes.val bytes.len limits.iri.val tokens result := by
  rw [read_edge]
  obtain ⟨property,propertyRead,propertyCorrect⟩ := read_property_total_correct table bytes tokens limits.iri
  cases property with
  | Err error => exact ⟨.Err error,by simp [propertyRead],.propertyError propertyCorrect⟩
  | Ok pair =>
    obtain ⟨property,rest⟩ := pair
    obtain ⟨subject,subjectRead,subjectCorrect⟩ := read_individual_total_correct table bytes rest limits.iri
    cases subject with
    | Err error => exact ⟨.Err error,by simp [propertyRead,subjectRead],.sourceError propertyCorrect subjectCorrect⟩
    | Ok pair =>
      obtain ⟨subject,after⟩ := pair
      obtain ⟨object,objectRead,objectCorrect⟩ := read_individual_total_correct table bytes after limits.iri
      cases object with
      | Err error =>
        exact ⟨.Err error,by simp [propertyRead,subjectRead,objectRead],
          .targetError propertyCorrect subjectCorrect objectCorrect⟩
      | Ok pair =>
        obtain ⟨object,remaining⟩ := pair
        exact ⟨.Ok ((property,subject,object),remaining),by simp [propertyRead,subjectRead,objectRead],
          .ok propertyCorrect subjectCorrect objectCorrect⟩
theorem read_edge_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits)
    (result : core.result.Result ((SourceObjectProperty × SourceIndividual × SourceIndividual) × Tokens)
      AssertionError) :
    read_edge table bytes tokens limits = .ok result ↔
      EdgeRun table.declarations.val bytes.val bytes.len limits.iri.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_edge_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_edge]
    cases source with
    | propertyError property => simp [(read_property_result_iff table bytes tokens limits.iri _).mpr property]
    | sourceError propertyRun failure =>
      simp [(read_property_result_iff table bytes tokens limits.iri _).mpr propertyRun,
        (read_individual_result_iff table bytes _ limits.iri _).mpr failure]
    | targetError propertyRun sourceRun failure =>
      simp [(read_property_result_iff table bytes tokens limits.iri _).mpr propertyRun,
        (read_individual_result_iff table bytes _ limits.iri _).mpr sourceRun,
        (read_individual_result_iff table bytes _ limits.iri _).mpr failure]
    | ok propertyRun sourceRun targetRun =>
      simp [(read_property_result_iff table bytes tokens limits.iri _).mpr propertyRun,
        (read_individual_result_iff table bytes _ limits.iri _).mpr sourceRun,
        (read_individual_result_iff table bytes _ limits.iri _).mpr targetRun]

/-- The actual body reader terminates and follows the independent grammar. -/
theorem read_body_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (form : AssertionForm)
    (tokens : Tokens) (limits : ClassLimits) :
    ∃ result, read_body table bytes form tokens limits = .ok result ∧
      BodyRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val form tokens
        result := by
  rw [read_body.eq_def]
  cases form with
  | Class =>
    obtain ⟨value,valueRead,valueCorrect⟩ := read_class_total_correct table bytes tokens limits
    cases value with
    | Err error => exact ⟨.Err error,by simp [valueRead],.classError valueCorrect⟩
    | Ok pair =>
      obtain ⟨value,rest⟩ := pair
      obtain ⟨individual,individualRead,individualCorrect⟩ := read_individual_total_correct table bytes rest limits.iri
      cases individual with
      | Err error =>
        exact ⟨.Err error,by simp [valueRead,individualRead],.individualError valueCorrect individualCorrect⟩
      | Ok pair =>
        obtain ⟨individual,remaining⟩ := pair
        exact ⟨.Ok (.ClassAssertion value individual,remaining),by simp [valueRead,individualRead],
          .classAssertion valueCorrect individualCorrect⟩
  | Property =>
    obtain ⟨edge,edgeRead,edgeCorrect⟩ := read_edge_total_correct table bytes tokens limits
    cases edge with
    | Err error => exact ⟨.Err error,by simp [edgeRead],.propertyError edgeCorrect⟩
    | Ok pair =>
      obtain ⟨⟨property,subject,object⟩,remaining⟩ := pair
      exact ⟨.Ok (.ObjectPropertyAssertion property subject object,remaining),by simp [edgeRead],
        .propertyAssertion edgeCorrect⟩
  | NegativeProperty =>
    obtain ⟨edge,edgeRead,edgeCorrect⟩ := read_edge_total_correct table bytes tokens limits
    cases edge with
    | Err error => exact ⟨.Err error,by simp [edgeRead],.negativeError edgeCorrect⟩
    | Ok pair =>
      obtain ⟨⟨property,subject,object⟩,remaining⟩ := pair
      exact ⟨.Ok (.NegativeObjectPropertyAssertion property subject object,remaining),by simp [edgeRead],
        .negativeAssertion edgeCorrect⟩
/-- Every exact body and first error is equivalent to its independent derivation. -/
theorem read_body_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (form : AssertionForm)
    (tokens : Tokens) (limits : ClassLimits)
    (result : core.result.Result (SourceAssertionBody × Tokens) AssertionError) :
    read_body table bytes form tokens limits = .ok result ↔
      BodyRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val form tokens
        result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_body_total_correct table bytes form tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_body.eq_def]
    cases source with
    | classError classRun => simp [(read_class_result_iff table bytes _ limits _).mpr classRun]
    | individualError classRun failure =>
      simp [(read_class_result_iff table bytes _ limits _).mpr classRun,
        (read_individual_result_iff table bytes _ limits.iri _).mpr failure]
    | classAssertion classRun individualRun =>
      simp [(read_class_result_iff table bytes _ limits _).mpr classRun,
        (read_individual_result_iff table bytes _ limits.iri _).mpr individualRun]
    | propertyError edge => simp [(read_edge_result_iff table bytes _ limits _).mpr edge]
    | propertyAssertion edge => simp [(read_edge_result_iff table bytes _ limits _).mpr edge]
    | negativeError edge => simp [(read_edge_result_iff table bytes _ limits _).mpr edge]
    | negativeAssertion edge => simp [(read_edge_result_iff table bytes _ limits _).mpr edge]

/-- Independent assertion grammar in source order: one of the three keywords,
    `(`, the maximal axiom-annotation sequence (the independent annotation
    grammar with the caller's annotation limits), the body with the caller's
    class limits, then `)`. -/
inductive AxiomRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize)
    (annotationCount annotationIri annotationLexical annotationDepth classCount classIri classDepth : Nat) :
    Tokens → core.result.Result (SourceAssertion × Tokens) AssertionError → Prop
  | keywordError {tokens : Tokens} {error : AssertionError} (failure : TakeRun eof .Axiom tokens (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth tokens (.Err error)
  | openError {keyword : Token} {tail : Tokens} {form : AssertionForm} {error : AssertionError}
      (formOf : FormOf keyword.terminal = some form) (failure : TakeRun eof .Open tail (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Err error)
  | annotationError {keyword opening : Token} {tail inner : Tokens} {form : AssertionForm}
      {error : functional_annotations.AnnotationError}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (failure : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Err (.Annotation error))
  | bodyError {keyword opening : Token} {tail inner : Tokens} {form : AssertionForm} {annotations : SourceAnnotations}
      {error : AssertionError}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Ok annotations))
      (failure : BodyRun rows source eof classCount classIri classDepth form annotations.remaining (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Err error)
  | closeError {keyword opening : Token} {tail inner rest : Tokens} {form : AssertionForm}
      {annotations : SourceAnnotations} {body : SourceAssertionBody} {error : AssertionError}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Ok annotations))
      (bodyRun : BodyRun rows source eof classCount classIri classDepth form annotations.remaining (.Ok (body,rest)))
      (failure : TakeRun eof .Close rest (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Err error)
  | ready {keyword opening close : Token} {tail inner rest remaining : Tokens} {form : AssertionForm}
      {annotations : SourceAnnotations} {body : SourceAssertionBody}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Ok annotations))
      (bodyRun : BodyRun rows source eof classCount classIri classDepth form annotations.remaining (.Ok (body,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Ok (⟨keyword,annotations.annotations,body⟩,remaining))

/-- The actual assertion reader terminates on every token stream and follows
    the independent grammar. -/
theorem read_assertion_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (annotations : AnnotationLimits) (classes : ClassLimits) :
    ∃ result, read_assertion table bytes tokens annotations classes = .ok result ∧
      AxiomRun table.declarations.val bytes.val bytes.len annotations.count.val annotations.iri.val
        annotations.lexical.val annotations.depth.val classes.count.val classes.iri.val classes.depth.val tokens result := by
  obtain ⟨first,firstRead,firstCorrect⟩ := take_expected_total_correct tokens .Axiom bytes.len
  rw [read_assertion]
  cases first with
  | Err error => exact ⟨.Err error,by simp [firstRead],.keywordError firstCorrect⟩
  | Ok pair =>
    obtain ⟨keyword,tail⟩ := pair
    cases firstCorrect with
    | taken _ _ accepted =>
      obtain ⟨form,formOf⟩ := accepted
      obtain ⟨opened,openRead,openCorrect⟩ := take_expected_total_correct tail .Open bytes.len
      cases opened with
      | Err error =>
        exact ⟨.Err error,by simp [firstRead,assertion_form_total_correct,formOf,openRead],.openError formOf openCorrect⟩
      | Ok pair =>
        obtain ⟨opening,inner⟩ := pair
        obtain ⟨annotated,annotatedRead,annotatedCorrect⟩ :=
          Rowl.FunctionalAnnotations.read_annotations_total_correct table bytes inner annotations
        cases annotated with
        | Err error =>
          exact ⟨.Err (.Annotation error),by simp [firstRead,assertion_form_total_correct,formOf,openRead,
            annotatedRead],.annotationError formOf openCorrect annotatedCorrect⟩
        | Ok sequence =>
          obtain ⟨body,bodyRead,bodyCorrect⟩ := read_body_total_correct table bytes form sequence.remaining classes
          cases body with
          | Err error =>
            exact ⟨.Err error,by simp [firstRead,assertion_form_total_correct,formOf,openRead,annotatedRead,bodyRead],
              .bodyError formOf openCorrect annotatedCorrect bodyCorrect⟩
          | Ok pair =>
            obtain ⟨body,rest⟩ := pair
            obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
            cases closed with
            | Err error =>
              exact ⟨.Err error,by simp [firstRead,assertion_form_total_correct,formOf,openRead,annotatedRead,
                bodyRead,closeRead],.closeError formOf openCorrect annotatedCorrect bodyCorrect closeCorrect⟩
            | Ok pair =>
              obtain ⟨close,remaining⟩ := pair
              exact ⟨.Ok (⟨keyword,sequence.annotations,body⟩,remaining),
                by simp [firstRead,assertion_form_total_correct,formOf,openRead,annotatedRead,bodyRead,closeRead],
                .ready formOf openCorrect annotatedCorrect bodyCorrect closeCorrect⟩
/-- Every exact assertion and first error is equivalent to its independent derivation. -/
theorem read_assertion_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (annotations : AnnotationLimits) (classes : ClassLimits)
    (result : core.result.Result (SourceAssertion × Tokens) AssertionError) :
    read_assertion table bytes tokens annotations classes = .ok result ↔
      AxiomRun table.declarations.val bytes.val bytes.len annotations.count.val annotations.iri.val
        annotations.lexical.val annotations.depth.val classes.count.val classes.iri.val classes.depth.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_assertion_total_correct table bytes tokens annotations classes
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_assertion]
    cases source with
    | keywordError failure => simp [(take_expected_result_iff tokens .Axiom bytes.len _).mpr failure]
    | @openError keyword tail form error formOf failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,assertion_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr failure]
    | @annotationError keyword opening tail inner form error formOf opened failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,assertion_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr opened,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner annotations _).mpr failure]
    | @bodyError keyword opening tail inner form sequence error formOf opened annotated failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,assertion_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr opened,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner annotations _).mpr annotated,
        (read_body_result_iff table bytes form _ classes _).mpr failure]
    | @closeError keyword opening tail inner rest form sequence body error formOf opened annotated bodyRun failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,assertion_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr opened,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner annotations _).mpr annotated,
        (read_body_result_iff table bytes form _ classes _).mpr bodyRun,
        (take_expected_result_iff rest .Close bytes.len _).mpr failure]
    | @ready keyword opening close tail inner rest remaining form sequence body formOf opened annotated bodyRun closing =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,assertion_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr opened,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner annotations _).mpr annotated,
        (read_body_result_iff table bytes form _ classes _).mpr bodyRun,
        (take_expected_result_iff rest .Close bytes.len _).mpr closing]

/-- A successful assertion consumes at least its keyword and its closing
    parenthesis, so an axiom loop always makes progress. -/
theorem assertion_progress (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens rest : Tokens)
    (annotations : AnnotationLimits) (classes : ClassLimits) (record : SourceAssertion)
    (accepted : read_assertion table bytes tokens annotations classes = .ok (.Ok (record,rest))) :
    TokenCount rest+2 ≤ TokenCount tokens := by
  have run := (read_assertion_result_iff table bytes tokens annotations classes _).mp accepted
  have classStep : ∀ {start after : Tokens} {value : SourceClass},
      ClassStep table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val classes.depth.val start
        (.Ok (value,after)) → TokenCount after ≤ TokenCount start := by
    intro start after value step
    cases step with
    | ok classRun =>
      have read := (Rowl.FunctionalClasses.read_class_expression_result_iff table bytes start classes _).mpr classRun
      rw [functional_classes.read_class_expression] at read
      have := Rowl.FunctionalClasses.class_progress read
      omega
  have propertyStep : ∀ {start after : Tokens} {value : SourceObjectProperty},
      PropertyStep table.declarations.val bytes.val bytes.len classes.iri.val start (.Ok (value,after)) →
        TokenCount after ≤ TokenCount start := by
    intro start after value step
    cases step with
    | ok propertyRun =>
      have := Rowl.FunctionalClasses.property_progress propertyRun
      omega
  have edgeStep : ∀ {start after : Tokens} {value : SourceObjectProperty × SourceIndividual × SourceIndividual},
      EdgeRun table.declarations.val bytes.val bytes.len classes.iri.val start (.Ok (value,after)) →
        TokenCount after ≤ TokenCount start := by
    intro start after value step
    generalize outputEq : core.result.Result.Ok (value,after) = output at step
    cases step with
    | ok propertyRun sourceRun targetRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := propertyStep propertyRun
      have two := individual_progress sourceRun
      have three := individual_progress targetRun
      omega
    | propertyError | sourceError | targetError => cases outputEq
  have bodyStep : ∀ {form : AssertionForm} {start after : Tokens} {body : SourceAssertionBody},
      BodyRun table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val classes.depth.val form start
        (.Ok (body,after)) → TokenCount after ≤ TokenCount start := by
    intro form start after body step
    generalize outputEq : core.result.Result.Ok (body,after) = output at step
    cases step with
    | classAssertion classRun individualRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := classStep classRun
      have two := individual_progress individualRun
      omega
    | propertyAssertion edge =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      exact edgeStep edge
    | negativeAssertion edge =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      exact edgeStep edge
    | classError | individualError | propertyError | negativeError => cases outputEq
  generalize outputEq : core.result.Result.Ok (record,rest) = output at run
  cases run with
  | keywordError | openError | annotationError | bodyError | closeError => cases outputEq
  | ready formOf opened annotated bodyRun closing =>
    injection outputEq with same
    injection same with _ restSame
    subst restSame
    have one := take_progress opened
    have two := Rowl.FunctionalAnnotations.scan_remaining_le annotated _ rfl
    have three := bodyStep bodyRun
    have four := take_progress closing
    simp only [TokenCount] at *
    omega
end Rowl.FunctionalAssertions
