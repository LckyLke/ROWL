import Rowl.FunctionalClasses
import Rowl.FunctionalAnnotations

/-!
Functional Syntax individual equalities and inequalities, class assertions and
positive and negative object property assertions, proved total and exact
against an independent grammar that composes the proved annotation,
class-expression, object-property and individual grammars. Every result and
first error has its independent derivation, and every derivation is the actual
result.
-/
namespace Rowl.FunctionalAssertions
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional_assertions
open RowlRust.functional_classes (ClassError ClassLimits SourceClass SourceObjectProperty)
open RowlRust.functional_annotations (AnnotationLimits SourceAnnotations)
open RowlRust.functional_individuals (IndividualError SourceIndividual)
open RowlRust.functional_lexer RowlRust.functional
open Rowl.FunctionalLexer (TokenCount)
open Rowl.FunctionalClasses (ClassRun PropertyRun)
open Rowl.FunctionalIndividuals (IndividualRun ListRun)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The five assertion keywords this stage reads. -/
def FormOf : Terminal → Option AssertionForm
  | .Keyword .SameIndividual => some .Same
  | .Keyword .DifferentIndividuals => some .Different
  | .Keyword .ClassAssertion => some .Class
  | .Keyword .ObjectPropertyAssertion => some .Property
  | .Keyword .NegativeObjectPropertyAssertion => some .NegativeProperty
  | _ => none
/-- Independent first-terminal class required at each assertion position. -/
def Expected : AssertionExpected → Terminal → Prop
  | .Axiom, terminal => ∃ form, FormOf terminal = some form
  | .Open, terminal => terminal = .Open
  | .Close, terminal => terminal = .Close

theorem assertion_form_total_correct (terminal : Terminal) : assertion_form terminal = .ok (FormOf terminal) := by
  cases terminal <;> first | rfl | (rename_i keyword; cases keyword <;> rfl)
theorem expected_terminal_total_correct (expected : AssertionExpected) (terminal : Terminal) :
    expected_terminal expected terminal = .ok (decide (Expected expected terminal)) := by
  cases expected <;> cases terminal <;> (try (rename_i keyword; cases keyword)) <;>
    simp [expected_terminal,Expected,assertion_form_total_correct,FormOf,core.option.Option.is_some]

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

/-- An individual at an assertion position: the independent individual
    grammar, with its errors wrapped. -/
inductive MemberStep (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (SourceIndividual × Tokens) AssertionError → Prop
  | error {tokens : Tokens} {error : IndividualError} (run : IndividualRun rows source eof limit tokens (.Err error)) :
      MemberStep rows source eof limit tokens (.Err (.Individual error))
  | ok {tokens rest : Tokens} {value : SourceIndividual}
      (run : IndividualRun rows source eof limit tokens (.Ok (value,rest))) :
      MemberStep rows source eof limit tokens (.Ok (value,rest))
/-- The individuals of an equality or inequality: the independent individual
    list of at least two members, with its errors wrapped. -/
inductive MembersStep (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Tokens → core.result.Result (alloc.vec.Vec SourceIndividual × Tokens) AssertionError → Prop
  | error {tokens : Tokens} {error : IndividualError}
      (run : ListRun rows source eof 2 count limit tokens (.Err error)) :
      MembersStep rows source eof count limit tokens (.Err (.Individual error))
  | ok {tokens rest : Tokens} {members : alloc.vec.Vec SourceIndividual}
      (run : ListRun rows source eof 2 count limit tokens (.Ok (members,rest))) :
      MembersStep rows source eof count limit tokens (.Ok (members,rest))

theorem read_member_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limit : Usize) :
    ∃ result, read_member table bytes tokens limit = .ok result ∧
      MemberStep table.declarations.val bytes.val bytes.len limit.val tokens result := by
  obtain ⟨result,executed,correct⟩ := Rowl.FunctionalIndividuals.read_individual_total_correct table bytes tokens limit
  rw [read_member]
  cases result with
  | Err error => exact ⟨.Err (.Individual error),by simp [executed],.error correct⟩
  | Ok pair => exact ⟨.Ok pair,by simp [executed],.ok correct⟩
theorem read_member_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limit : Usize) (result : core.result.Result (SourceIndividual × Tokens) AssertionError) :
    read_member table bytes tokens limit = .ok result ↔
      MemberStep table.declarations.val bytes.val bytes.len limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_member_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_member]
    cases source with
    | error run => simp [(Rowl.FunctionalIndividuals.read_individual_result_iff table bytes tokens limit _).mpr run]
    | ok run => simp [(Rowl.FunctionalIndividuals.read_individual_result_iff table bytes tokens limit _).mpr run]
/-- An accepted individual consumes exactly its one token. -/
theorem member_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens rest : Tokens} {individual : SourceIndividual}
    (accepted : MemberStep rows source eof limit tokens (.Ok (individual,rest))) :
    TokenCount tokens = 1+TokenCount rest := by
  cases accepted with
  | ok run => exact Rowl.FunctionalIndividuals.individual_progress run

theorem read_members_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) :
    ∃ result, functional_assertions.read_members table bytes tokens limits = .ok result ∧
      MembersStep table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val tokens result := by
  obtain ⟨result,executed,correct,_⟩ :=
    Rowl.FunctionalIndividuals.read_individual_list_total_correct table bytes tokens 2#usize limits.count limits.iri
  have two : (2#usize).val = 2 := rfl
  rw [two] at correct
  rw [functional_assertions.read_members]
  cases result with
  | Err error => exact ⟨.Err (.Individual error),by simp [executed],.error correct⟩
  | Ok pair => exact ⟨.Ok pair,by simp [executed],.ok correct⟩
theorem read_members_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) (result : core.result.Result (alloc.vec.Vec SourceIndividual × Tokens) AssertionError) :
    functional_assertions.read_members table bytes tokens limits = .ok result ↔
      MembersStep table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_members_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [functional_assertions.read_members]
    cases source with
    | error run =>
      simp [(Rowl.FunctionalIndividuals.read_individual_list_result_iff table bytes tokens 2#usize limits.count
        limits.iri _).mpr run]
    | ok run =>
      simp [(Rowl.FunctionalIndividuals.read_individual_list_result_iff table bytes tokens 2#usize limits.count
        limits.iri _).mpr run]
/-- An accepted individual list never consumes more tokens than it is given. -/
theorem members_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {count limit : Nat}
    {tokens rest : Tokens} {members : alloc.vec.Vec SourceIndividual}
    (accepted : MembersStep rows source eof count limit tokens (.Ok (members,rest))) :
    TokenCount rest ≤ TokenCount tokens := by
  cases accepted with
  | ok run => exact Rowl.FunctionalIndividuals.list_progress run

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
      (failure : MemberStep rows source eof limit rest (.Err error)) :
      EdgeRun rows source eof limit tokens (.Err error)
  | targetError {tokens rest after : Tokens} {property : SourceObjectProperty} {subject : SourceIndividual}
      {error : AssertionError}
      (propertyRun : PropertyStep rows source eof limit tokens (.Ok (property,rest)))
      (sourceRun : MemberStep rows source eof limit rest (.Ok (subject,after)))
      (failure : MemberStep rows source eof limit after (.Err error)) :
      EdgeRun rows source eof limit tokens (.Err error)
  | ok {tokens rest after remaining : Tokens} {property : SourceObjectProperty} {subject object : SourceIndividual}
      (propertyRun : PropertyStep rows source eof limit tokens (.Ok (property,rest)))
      (sourceRun : MemberStep rows source eof limit rest (.Ok (subject,after)))
      (targetRun : MemberStep rows source eof limit after (.Ok (object,remaining))) :
      EdgeRun rows source eof limit tokens (.Ok ((property,subject,object),remaining))
/-- Independent assertion bodies after the axiom annotations, in source order:
    an individual list of at least two members, a class expression and an
    individual, or an object property expression and two individuals. -/
inductive BodyRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit depth : Nat) :
    AssertionForm → Tokens → core.result.Result (SourceAssertionBody × Tokens) AssertionError → Prop
  | sameError {tokens : Tokens} {error : AssertionError}
      (members : MembersStep rows source eof count limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .Same tokens (.Err error)
  | same {tokens remaining : Tokens} {members : alloc.vec.Vec SourceIndividual}
      (membersRun : MembersStep rows source eof count limit tokens (.Ok (members,remaining))) :
      BodyRun rows source eof count limit depth .Same tokens (.Ok (.SameIndividual members,remaining))
  | differentError {tokens : Tokens} {error : AssertionError}
      (members : MembersStep rows source eof count limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .Different tokens (.Err error)
  | different {tokens remaining : Tokens} {members : alloc.vec.Vec SourceIndividual}
      (membersRun : MembersStep rows source eof count limit tokens (.Ok (members,remaining))) :
      BodyRun rows source eof count limit depth .Different tokens (.Ok (.DifferentIndividuals members,remaining))
  | classError {tokens : Tokens} {error : AssertionError}
      (classRun : ClassStep rows source eof count limit depth tokens (.Err error)) :
      BodyRun rows source eof count limit depth .Class tokens (.Err error)
  | individualError {tokens rest : Tokens} {value : SourceClass} {error : AssertionError}
      (classRun : ClassStep rows source eof count limit depth tokens (.Ok (value,rest)))
      (failure : MemberStep rows source eof limit rest (.Err error)) :
      BodyRun rows source eof count limit depth .Class tokens (.Err error)
  | classAssertion {tokens rest remaining : Tokens} {value : SourceClass} {individual : SourceIndividual}
      (classRun : ClassStep rows source eof count limit depth tokens (.Ok (value,rest)))
      (individualRun : MemberStep rows source eof limit rest (.Ok (individual,remaining))) :
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
    obtain ⟨subject,subjectRead,subjectCorrect⟩ := read_member_total_correct table bytes rest limits.iri
    cases subject with
    | Err error => exact ⟨.Err error,by simp [propertyRead,subjectRead],.sourceError propertyCorrect subjectCorrect⟩
    | Ok pair =>
      obtain ⟨subject,after⟩ := pair
      obtain ⟨object,objectRead,objectCorrect⟩ := read_member_total_correct table bytes after limits.iri
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
        (read_member_result_iff table bytes _ limits.iri _).mpr failure]
    | targetError propertyRun sourceRun failure =>
      simp [(read_property_result_iff table bytes tokens limits.iri _).mpr propertyRun,
        (read_member_result_iff table bytes _ limits.iri _).mpr sourceRun,
        (read_member_result_iff table bytes _ limits.iri _).mpr failure]
    | ok propertyRun sourceRun targetRun =>
      simp [(read_property_result_iff table bytes tokens limits.iri _).mpr propertyRun,
        (read_member_result_iff table bytes _ limits.iri _).mpr sourceRun,
        (read_member_result_iff table bytes _ limits.iri _).mpr targetRun]

/-- The actual body reader terminates and follows the independent grammar. -/
theorem read_body_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (form : AssertionForm)
    (tokens : Tokens) (limits : ClassLimits) :
    ∃ result, read_body table bytes form tokens limits = .ok result ∧
      BodyRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val form tokens
        result := by
  rw [read_body.eq_def]
  cases form with
  | Same =>
    obtain ⟨members,membersRead,membersCorrect⟩ := read_members_total_correct table bytes tokens limits
    cases members with
    | Err error => exact ⟨.Err error,by simp [membersRead],.sameError membersCorrect⟩
    | Ok pair =>
      obtain ⟨members,remaining⟩ := pair
      exact ⟨.Ok (.SameIndividual members,remaining),by simp [membersRead],.same membersCorrect⟩
  | Different =>
    obtain ⟨members,membersRead,membersCorrect⟩ := read_members_total_correct table bytes tokens limits
    cases members with
    | Err error => exact ⟨.Err error,by simp [membersRead],.differentError membersCorrect⟩
    | Ok pair =>
      obtain ⟨members,remaining⟩ := pair
      exact ⟨.Ok (.DifferentIndividuals members,remaining),by simp [membersRead],.different membersCorrect⟩
  | Class =>
    obtain ⟨value,valueRead,valueCorrect⟩ := read_class_total_correct table bytes tokens limits
    cases value with
    | Err error => exact ⟨.Err error,by simp [valueRead],.classError valueCorrect⟩
    | Ok pair =>
      obtain ⟨value,rest⟩ := pair
      obtain ⟨individual,individualRead,individualCorrect⟩ := read_member_total_correct table bytes rest limits.iri
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
    | sameError members => simp [(read_members_result_iff table bytes _ limits _).mpr members]
    | same membersRun => simp [(read_members_result_iff table bytes _ limits _).mpr membersRun]
    | differentError members => simp [(read_members_result_iff table bytes _ limits _).mpr members]
    | different membersRun => simp [(read_members_result_iff table bytes _ limits _).mpr membersRun]
    | classError classRun => simp [(read_class_result_iff table bytes _ limits _).mpr classRun]
    | individualError classRun failure =>
      simp [(read_class_result_iff table bytes _ limits _).mpr classRun,
        (read_member_result_iff table bytes _ limits.iri _).mpr failure]
    | classAssertion classRun individualRun =>
      simp [(read_class_result_iff table bytes _ limits _).mpr classRun,
        (read_member_result_iff table bytes _ limits.iri _).mpr individualRun]
    | propertyError edge => simp [(read_edge_result_iff table bytes _ limits _).mpr edge]
    | propertyAssertion edge => simp [(read_edge_result_iff table bytes _ limits _).mpr edge]
    | negativeError edge => simp [(read_edge_result_iff table bytes _ limits _).mpr edge]
    | negativeAssertion edge => simp [(read_edge_result_iff table bytes _ limits _).mpr edge]

/-- Independent assertion grammar in source order: one of the five keywords,
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
      have two := member_progress sourceRun
      have three := member_progress targetRun
      omega
    | propertyError | sourceError | targetError => cases outputEq
  have bodyStep : ∀ {form : AssertionForm} {start after : Tokens} {body : SourceAssertionBody},
      BodyRun table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val classes.depth.val form start
        (.Ok (body,after)) → TokenCount after ≤ TokenCount start := by
    intro form start after body step
    generalize outputEq : core.result.Result.Ok (body,after) = output at step
    cases step with
    | same membersRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      exact members_progress membersRun
    | different membersRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      exact members_progress membersRun
    | classAssertion classRun individualRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := classStep classRun
      have two := member_progress individualRun
      omega
    | propertyAssertion edge =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      exact edgeStep edge
    | negativeAssertion edge =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      exact edgeStep edge
    | sameError | differentError | classError | individualError | propertyError | negativeError => cases outputEq
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
