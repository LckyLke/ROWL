import Rowl.FunctionalClasses
import Rowl.FunctionalAnnotations

/-!
Functional Syntax class axioms and object property domain and range axioms,
proved total and exact against an independent grammar that composes the proved
annotation, class-expression and object-property grammars. Every result and
first error has its independent derivation, and every derivation is the actual
result.
-/
namespace Rowl.FunctionalClassAxioms
open Aeneas Aeneas.Std Aeneas.Std.Result RowlFrontendRust
open RowlFrontendRust.functional_class_axioms
open RowlFrontendRust.functional_classes (ClassError ClassExpected ClassLimits SourceClass SourceObjectProperty)
open RowlFrontendRust.functional_annotations (AnnotationLimits SourceAnnotations)
open RowlFrontendRust.functional_header (HeaderIri)
open RowlFrontendRust.functional_lexer RowlFrontendRust.functional
open Rowl.FunctionalHeaderIdentity (Kind iri_kind_total_correct)
open Rowl.FunctionalLexer (TokenCount)
open Rowl.FunctionalClasses (ClassRun MembersRun PropertyRun Position)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The six axiom keywords this stage reads. -/
def FormOf : Terminal → Option AxiomForm
  | .Keyword .SubClassOf => some .SubClassOf
  | .Keyword .EquivalentClasses => some .EquivalentClasses
  | .Keyword .DisjointClasses => some .DisjointClasses
  | .Keyword .DisjointUnion => some .DisjointUnion
  | .Keyword .ObjectPropertyDomain => some .ObjectPropertyDomain
  | .Keyword .ObjectPropertyRange => some .ObjectPropertyRange
  | _ => none
/-- Independent first-terminal class required at each axiom position. -/
def Expected : ClassAxiomExpected → Terminal → Prop
  | .Axiom, terminal => ∃ form, FormOf terminal = some form
  | .Open, terminal => terminal = .Open
  | .Iri, terminal => ∃ kind, Kind terminal = some kind
  | .Close, terminal => terminal = .Close

theorem axiom_form_total_correct (terminal : Terminal) : axiom_form terminal = .ok (FormOf terminal) := by
  cases terminal <;> first | rfl | (rename_i keyword; cases keyword <;> rfl)
theorem expected_terminal_total_correct (expected : ClassAxiomExpected) (terminal : Terminal) :
    expected_terminal expected terminal = .ok (decide (Expected expected terminal)) := by
  cases expected <;> cases terminal <;> (try (rename_i keyword; cases keyword)) <;>
    simp [expected_terminal,Expected,axiom_form_total_correct,iri_kind_total_correct,FormOf,Kind,
      core.option.Option.is_some]

/-- One syntax step: the first token must belong to the expected class. -/
inductive TakeRun (eof : Usize) (expected : ClassAxiomExpected) :
    Tokens → core.result.Result (Token × Tokens) ClassAxiomError → Prop
  | empty : TakeRun eof expected .Empty (.Err (.Expected expected eof))
  | wrong (token : Token) (rest : Tokens) (different : ¬ Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Err (.Expected expected token.start))
  | taken (token : Token) (rest : Tokens) (accepted : Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Ok (token,rest))

theorem take_expected_total_correct (tokens : Tokens) (expected : ClassAxiomExpected) (eof : Usize) :
    ∃ result, take_expected tokens expected eof = .ok result ∧ TakeRun eof expected tokens result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected expected eof),rfl,.empty⟩
  | Cons token rest =>
    by_cases accepted : Expected expected token.terminal
    · exact ⟨.Ok (token,rest),by simp [take_expected,expected_terminal_total_correct,accepted],.taken _ _ accepted⟩
    · exact ⟨.Err (.Expected expected token.start),by simp [take_expected,expected_terminal_total_correct,accepted],
        .wrong _ _ accepted⟩
private theorem take_run_unique {eof : Usize} {expected : ClassAxiomExpected} {tokens : Tokens}
    {one two : core.result.Result (Token × Tokens) ClassAxiomError}
    (first : TakeRun eof expected tokens one) (second : TakeRun eof expected tokens two) : one = two := by
  cases first <;> cases second <;> first | rfl | contradiction
theorem take_expected_result_iff (tokens : Tokens) (expected : ClassAxiomExpected) (eof : Usize)
    (result : core.result.Result (Token × Tokens) ClassAxiomError) :
    take_expected tokens expected eof = .ok result ↔ TakeRun eof expected tokens result := by
  obtain ⟨actual,executed,correct⟩ := take_expected_total_correct tokens expected eof
  constructor
  · intro output
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    have same := take_run_unique correct source
    simpa [same] using executed
theorem take_progress {eof : Usize} {expected : ClassAxiomExpected} {tokens rest : Tokens} {token : Token}
    (taken : TakeRun eof expected tokens (.Ok (token,rest))) : TokenCount tokens = 1+TokenCount rest := by
  cases taken
  rfl

/-- A class expression at a top-level axiom position: the independent class
    grammar at the full nesting allowance, with its errors wrapped. -/
inductive ClassStep (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit depth : Nat) :
    Tokens → core.result.Result (SourceClass × Tokens) ClassAxiomError → Prop
  | error {tokens : Tokens} {error : ClassError} (run : ClassRun rows source eof count limit depth tokens (.Err error)) :
      ClassStep rows source eof count limit depth tokens (.Err (.Class error))
  | ok {tokens rest : Tokens} {value : SourceClass}
      (run : ClassRun rows source eof count limit depth tokens (.Ok (value,rest))) :
      ClassStep rows source eof count limit depth tokens (.Ok (value,rest))
/-- At least two class expressions, read as the maximal member sequence at the
    full nesting allowance and then checked for the two-member minimum. -/
inductive ListRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit depth : Nat) :
    Tokens → core.result.Result (alloc.vec.Vec SourceClass × Tokens) ClassAxiomError → Prop
  | error {tokens : Tokens} {error : ClassError} (run : MembersRun rows source eof count limit depth [] tokens (.Err error)) :
      ListRun rows source eof count limit depth tokens (.Err (.Class error))
  | tooFew {tokens rest : Tokens} {list : alloc.vec.Vec SourceClass}
      (run : MembersRun rows source eof count limit depth [] tokens (.Ok (list,rest))) (few : list.val.length < 2) :
      ListRun rows source eof count limit depth tokens (.Err (.Class (.Expected .Class (Position eof rest))))
  | ok {tokens rest : Tokens} {list : alloc.vec.Vec SourceClass}
      (run : MembersRun rows source eof count limit depth [] tokens (.Ok (list,rest))) (enough : 2 ≤ list.val.length) :
      ListRun rows source eof count limit depth tokens (.Ok (list,rest))
/-- The disjoint union's class IRI, resolved through the checked prefix rows. -/
inductive NamedRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (HeaderIri × Tokens) ClassAxiomError → Prop
  | tokenError {tokens : Tokens} {error : ClassAxiomError} (failure : TakeRun eof .Iri tokens (.Err error)) :
      NamedRun rows source eof limit tokens (.Err error)
  | iriError {tokens rest : Tokens} {token : Token} {family : functional_iris.SourceIriKind}
      {error : functional_iris.SourceIriError}
      (taken : TakeRun eof .Iri tokens (.Ok (token,rest))) (kind : Kind token.terminal = some family)
      (failure : Rowl.FunctionalIris.ErrorCorrect rows family source token.start.val token.end.val limit error) :
      NamedRun rows source eof limit tokens (.Err (.Iri error))
  | ok {tokens rest : Tokens} {token : Token} {family : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8}
      (taken : TakeRun eof .Iri tokens (.Ok (token,rest))) (kind : Kind token.terminal = some family)
      (success : Rowl.FunctionalIris.Success rows family source token.start.val token.end.val limit value) :
      NamedRun rows source eof limit tokens (.Ok (⟨token,value⟩,rest))
/-- Independent axiom bodies after the axiom annotations, in source order. -/
inductive BodyRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit depth : Nat) :
    AxiomForm → Tokens → core.result.Result (SourceClassAxiomBody × Tokens) ClassAxiomError → Prop
  | subError {tokens : Tokens} {error : ClassAxiomError}
      (sub : ClassStep rows source eof count limit depth tokens (.Err error)) :
      BodyRun rows source eof count limit depth .SubClassOf tokens (.Err error)
  | supError {tokens rest : Tokens} {sub : SourceClass} {error : ClassAxiomError}
      (subRun : ClassStep rows source eof count limit depth tokens (.Ok (sub,rest)))
      (sup : ClassStep rows source eof count limit depth rest (.Err error)) :
      BodyRun rows source eof count limit depth .SubClassOf tokens (.Err error)
  | subClassOf {tokens rest remaining : Tokens} {sub sup : SourceClass}
      (subRun : ClassStep rows source eof count limit depth tokens (.Ok (sub,rest)))
      (supRun : ClassStep rows source eof count limit depth rest (.Ok (sup,remaining))) :
      BodyRun rows source eof count limit depth .SubClassOf tokens (.Ok (.SubClassOf sub sup,remaining))
  | equivalentError {tokens : Tokens} {error : ClassAxiomError}
      (list : ListRun rows source eof count limit depth tokens (.Err error)) :
      BodyRun rows source eof count limit depth .EquivalentClasses tokens (.Err error)
  | equivalent {tokens remaining : Tokens} {members : alloc.vec.Vec SourceClass}
      (list : ListRun rows source eof count limit depth tokens (.Ok (members,remaining))) :
      BodyRun rows source eof count limit depth .EquivalentClasses tokens (.Ok (.EquivalentClasses members,remaining))
  | disjointError {tokens : Tokens} {error : ClassAxiomError}
      (list : ListRun rows source eof count limit depth tokens (.Err error)) :
      BodyRun rows source eof count limit depth .DisjointClasses tokens (.Err error)
  | disjoint {tokens remaining : Tokens} {members : alloc.vec.Vec SourceClass}
      (list : ListRun rows source eof count limit depth tokens (.Ok (members,remaining))) :
      BodyRun rows source eof count limit depth .DisjointClasses tokens (.Ok (.DisjointClasses members,remaining))
  | unionNameError {tokens : Tokens} {error : ClassAxiomError}
      (named : NamedRun rows source eof limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .DisjointUnion tokens (.Err error)
  | unionListError {tokens rest : Tokens} {iri : HeaderIri} {error : ClassAxiomError}
      (named : NamedRun rows source eof limit tokens (.Ok (iri,rest)))
      (list : ListRun rows source eof count limit depth rest (.Err error)) :
      BodyRun rows source eof count limit depth .DisjointUnion tokens (.Err error)
  | disjointUnion {tokens rest remaining : Tokens} {iri : HeaderIri} {members : alloc.vec.Vec SourceClass}
      (named : NamedRun rows source eof limit tokens (.Ok (iri,rest)))
      (list : ListRun rows source eof count limit depth rest (.Ok (members,remaining))) :
      BodyRun rows source eof count limit depth .DisjointUnion tokens (.Ok (.DisjointUnion iri members,remaining))
  | domainPropertyError {tokens : Tokens} {error : ClassError}
      (property : PropertyRun rows source eof limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .ObjectPropertyDomain tokens (.Err (.Class error))
  | domainError {tokens rest : Tokens} {property : SourceObjectProperty} {error : ClassAxiomError}
      (propertyRun : PropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (domain : ClassStep rows source eof count limit depth rest (.Err error)) :
      BodyRun rows source eof count limit depth .ObjectPropertyDomain tokens (.Err error)
  | domain {tokens rest remaining : Tokens} {property : SourceObjectProperty} {domain : SourceClass}
      (propertyRun : PropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (domainRun : ClassStep rows source eof count limit depth rest (.Ok (domain,remaining))) :
      BodyRun rows source eof count limit depth .ObjectPropertyDomain tokens
        (.Ok (.ObjectPropertyDomain property domain,remaining))
  | rangePropertyError {tokens : Tokens} {error : ClassError}
      (property : PropertyRun rows source eof limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .ObjectPropertyRange tokens (.Err (.Class error))
  | rangeError {tokens rest : Tokens} {property : SourceObjectProperty} {error : ClassAxiomError}
      (propertyRun : PropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (range : ClassStep rows source eof count limit depth rest (.Err error)) :
      BodyRun rows source eof count limit depth .ObjectPropertyRange tokens (.Err error)
  | range {tokens rest remaining : Tokens} {property : SourceObjectProperty} {range : SourceClass}
      (propertyRun : PropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (rangeRun : ClassStep rows source eof count limit depth rest (.Ok (range,remaining))) :
      BodyRun rows source eof count limit depth .ObjectPropertyRange tokens
        (.Ok (.ObjectPropertyRange property range,remaining))

theorem read_class_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) :
    ∃ result, functional_class_axioms.read_class table bytes tokens limits = .ok result ∧
      ClassStep table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val tokens
        result := by
  obtain ⟨result,executed,correct⟩ := Rowl.FunctionalClasses.read_class_expression_total_correct table bytes tokens limits
  rw [functional_class_axioms.read_class]
  cases result with
  | Err error => exact ⟨.Err (.Class error),by simp [executed],.error correct⟩
  | Ok pair => exact ⟨.Ok pair,by simp [executed],.ok correct⟩
theorem read_class_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) (result : core.result.Result (SourceClass × Tokens) ClassAxiomError) :
    functional_class_axioms.read_class table bytes tokens limits = .ok result ↔
      ClassStep table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val tokens
        result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_class_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [functional_class_axioms.read_class]
    cases source with
    | error run => simp [(Rowl.FunctionalClasses.read_class_expression_result_iff table bytes tokens limits _).mpr run]
    | ok run => simp [(Rowl.FunctionalClasses.read_class_expression_result_iff table bytes tokens limits _).mpr run]

theorem read_list_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) :
    ∃ result, read_list table bytes tokens limits = .ok result ∧
      ListRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val tokens
        result := by
  obtain ⟨result,executed,correct,_⟩ :=
    Rowl.FunctionalClasses.read_members_total_correct table bytes tokens (alloc.vec.Vec.new SourceClass) limits.depth limits
  have start : (alloc.vec.Vec.new SourceClass).val = [] := rfl
  rw [start] at correct
  rw [read_list]
  cases result with
  | Err error => exact ⟨.Err (.Class error),by simp [executed],.error correct⟩
  | Ok pair =>
    obtain ⟨list,rest⟩ := pair
    by_cases few : list.val.length < 2
    · exact ⟨.Err (.Class (.Expected .Class (Position bytes.len rest))),
        by simp [executed,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,Nat.lt_succ_iff.mp few,
          Rowl.FunctionalClasses.offset_of_total_correct],
        .tooFew correct few⟩
    · have enough : 2 ≤ list.val.length := by omega
      exact ⟨.Ok (list,rest),by simp [executed,alloc.vec.Vec.len_val,UScalar.lt_equiv,Nat.not_lt.mpr enough,
        Nat.not_le.mpr enough],.ok correct enough⟩
theorem read_list_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) (result : core.result.Result (alloc.vec.Vec SourceClass × Tokens) ClassAxiomError) :
    read_list table bytes tokens limits = .ok result ↔
      ListRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val tokens
        result := by
  have members := fun result =>
    Rowl.FunctionalClasses.read_members_result_iff table bytes tokens (alloc.vec.Vec.new SourceClass) limits.depth limits
      result
  have start : (alloc.vec.Vec.new SourceClass).val = [] := rfl
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_list_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_list]
    cases source with
    | error run =>
      rw [← start] at run
      simp [(members _).mpr run]
    | tooFew run few =>
      rw [← start] at run
      simp [(members _).mpr run,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,Nat.lt_succ_iff.mp few,
        Rowl.FunctionalClasses.offset_of_total_correct]
    | ok run enough =>
      rw [← start] at run
      simp [(members _).mpr run,alloc.vec.Vec.len_val,UScalar.lt_equiv,Nat.not_lt.mpr enough,Nat.not_le.mpr enough]

theorem read_named_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limit : Usize) :
    ∃ result, read_named table bytes tokens limit = .ok result ∧
      NamedRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  obtain ⟨taken,takenRead,takenCorrect⟩ := take_expected_total_correct tokens .Iri bytes.len
  rw [read_named]
  cases taken with
  | Err error => exact ⟨.Err error,by simp [takenRead],.tokenError takenCorrect⟩
  | Ok pair =>
    obtain ⟨token,rest⟩ := pair
    obtain ⟨family,kind⟩ : ∃ family, Kind token.terminal = some family := by
      cases takenCorrect with
      | taken _ _ accepted => exact accepted
    obtain ⟨resolved,resolveRead,resolveCorrect⟩ :=
      Rowl.FunctionalIris.resolve_span_total_correct table family bytes token.start token.end limit
    cases resolved with
    | Err error =>
      exact ⟨.Err (.Iri error),by simp [takenRead,iri_kind_total_correct,kind,resolveRead],
        .iriError takenCorrect kind resolveCorrect⟩
    | Ok value =>
      exact ⟨.Ok (⟨token,value⟩,rest),by simp [takenRead,iri_kind_total_correct,kind,resolveRead],
        .ok takenCorrect kind resolveCorrect⟩
theorem read_named_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limit : Usize) (result : core.result.Result (HeaderIri × Tokens) ClassAxiomError) :
    read_named table bytes tokens limit = .ok result ↔
      NamedRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_named_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_named]
    cases source with
    | tokenError failure => simp [(take_expected_result_iff tokens .Iri bytes.len _).mpr failure]
    | iriError taken kind failure =>
      simp [(take_expected_result_iff tokens .Iri bytes.len _).mpr taken,iri_kind_total_correct,kind,
        (Rowl.FunctionalIris.resolve_span_error_iff table _ bytes _ _ limit _).mpr failure]
    | ok taken kind success =>
      simp [(take_expected_result_iff tokens .Iri bytes.len _).mpr taken,iri_kind_total_correct,kind,
        (Rowl.FunctionalIris.resolve_span_value_iff table _ bytes _ _ limit _).mpr success]

/-- The actual body reader terminates and follows the independent grammar. -/
theorem read_body_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (form : AxiomForm)
    (tokens : Tokens) (limits : ClassLimits) :
    ∃ result, read_body table bytes form tokens limits = .ok result ∧
      BodyRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val form tokens
        result := by
  rw [read_body.eq_def]
  cases form with
  | SubClassOf =>
    obtain ⟨sub,subRead,subCorrect⟩ := read_class_total_correct table bytes tokens limits
    cases sub with
    | Err error => exact ⟨.Err error,by simp [subRead],.subError subCorrect⟩
    | Ok pair =>
      obtain ⟨sub,rest⟩ := pair
      obtain ⟨sup,supRead,supCorrect⟩ := read_class_total_correct table bytes rest limits
      cases sup with
      | Err error => exact ⟨.Err error,by simp [subRead,supRead],.supError subCorrect supCorrect⟩
      | Ok pair =>
        obtain ⟨sup,remaining⟩ := pair
        exact ⟨.Ok (.SubClassOf sub sup,remaining),by simp [subRead,supRead],.subClassOf subCorrect supCorrect⟩
  | EquivalentClasses =>
    obtain ⟨list,listRead,listCorrect⟩ := read_list_total_correct table bytes tokens limits
    cases list with
    | Err error => exact ⟨.Err error,by simp [listRead],.equivalentError listCorrect⟩
    | Ok pair =>
      obtain ⟨members,remaining⟩ := pair
      exact ⟨.Ok (.EquivalentClasses members,remaining),by simp [listRead],.equivalent listCorrect⟩
  | DisjointClasses =>
    obtain ⟨list,listRead,listCorrect⟩ := read_list_total_correct table bytes tokens limits
    cases list with
    | Err error => exact ⟨.Err error,by simp [listRead],.disjointError listCorrect⟩
    | Ok pair =>
      obtain ⟨members,remaining⟩ := pair
      exact ⟨.Ok (.DisjointClasses members,remaining),by simp [listRead],.disjoint listCorrect⟩
  | DisjointUnion =>
    obtain ⟨named,namedRead,namedCorrect⟩ := read_named_total_correct table bytes tokens limits.iri
    cases named with
    | Err error => exact ⟨.Err error,by simp [namedRead],.unionNameError namedCorrect⟩
    | Ok pair =>
      obtain ⟨iri,rest⟩ := pair
      obtain ⟨list,listRead,listCorrect⟩ := read_list_total_correct table bytes rest limits
      cases list with
      | Err error => exact ⟨.Err error,by simp [namedRead,listRead],.unionListError namedCorrect listCorrect⟩
      | Ok pair =>
        obtain ⟨members,remaining⟩ := pair
        exact ⟨.Ok (.DisjointUnion iri members,remaining),by simp [namedRead,listRead],
          .disjointUnion namedCorrect listCorrect⟩
  | ObjectPropertyDomain =>
    obtain ⟨property,propertyRead,propertyCorrect⟩ :=
      Rowl.FunctionalClasses.read_object_property_total_correct table bytes tokens limits.iri
    cases property with
    | Err error => exact ⟨.Err (.Class error),by simp [propertyRead],.domainPropertyError propertyCorrect⟩
    | Ok pair =>
      obtain ⟨property,rest⟩ := pair
      obtain ⟨domain,domainRead,domainCorrect⟩ := read_class_total_correct table bytes rest limits
      cases domain with
      | Err error => exact ⟨.Err error,by simp [propertyRead,domainRead],.domainError propertyCorrect domainCorrect⟩
      | Ok pair =>
        obtain ⟨domain,remaining⟩ := pair
        exact ⟨.Ok (.ObjectPropertyDomain property domain,remaining),by simp [propertyRead,domainRead],
          .domain propertyCorrect domainCorrect⟩
  | ObjectPropertyRange =>
    obtain ⟨property,propertyRead,propertyCorrect⟩ :=
      Rowl.FunctionalClasses.read_object_property_total_correct table bytes tokens limits.iri
    cases property with
    | Err error => exact ⟨.Err (.Class error),by simp [propertyRead],.rangePropertyError propertyCorrect⟩
    | Ok pair =>
      obtain ⟨property,rest⟩ := pair
      obtain ⟨range,rangeRead,rangeCorrect⟩ := read_class_total_correct table bytes rest limits
      cases range with
      | Err error => exact ⟨.Err error,by simp [propertyRead,rangeRead],.rangeError propertyCorrect rangeCorrect⟩
      | Ok pair =>
        obtain ⟨range,remaining⟩ := pair
        exact ⟨.Ok (.ObjectPropertyRange property range,remaining),by simp [propertyRead,rangeRead],
          .range propertyCorrect rangeCorrect⟩
/-- Every exact body and first error is equivalent to its independent derivation. -/
theorem read_body_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (form : AxiomForm)
    (tokens : Tokens) (limits : ClassLimits)
    (result : core.result.Result (SourceClassAxiomBody × Tokens) ClassAxiomError) :
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
    | subError sub => simp [(read_class_result_iff table bytes _ limits _).mpr sub]
    | supError subRun sup =>
      simp [(read_class_result_iff table bytes _ limits _).mpr subRun,(read_class_result_iff table bytes _ limits _).mpr sup]
    | subClassOf subRun supRun =>
      simp [(read_class_result_iff table bytes _ limits _).mpr subRun,
        (read_class_result_iff table bytes _ limits _).mpr supRun]
    | equivalentError list => simp [(read_list_result_iff table bytes _ limits _).mpr list]
    | equivalent list => simp [(read_list_result_iff table bytes _ limits _).mpr list]
    | disjointError list => simp [(read_list_result_iff table bytes _ limits _).mpr list]
    | disjoint list => simp [(read_list_result_iff table bytes _ limits _).mpr list]
    | unionNameError named => simp [(read_named_result_iff table bytes _ limits.iri _).mpr named]
    | unionListError named list =>
      simp [(read_named_result_iff table bytes _ limits.iri _).mpr named,(read_list_result_iff table bytes _ limits _).mpr list]
    | disjointUnion named list =>
      simp [(read_named_result_iff table bytes _ limits.iri _).mpr named,(read_list_result_iff table bytes _ limits _).mpr list]
    | domainPropertyError property =>
      simp [(Rowl.FunctionalClasses.read_object_property_result_iff table bytes _ limits.iri _).mpr property]
    | domainError propertyRun domain =>
      simp [(Rowl.FunctionalClasses.read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
        (read_class_result_iff table bytes _ limits _).mpr domain]
    | domain propertyRun domainRun =>
      simp [(Rowl.FunctionalClasses.read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
        (read_class_result_iff table bytes _ limits _).mpr domainRun]
    | rangePropertyError property =>
      simp [(Rowl.FunctionalClasses.read_object_property_result_iff table bytes _ limits.iri _).mpr property]
    | rangeError propertyRun range =>
      simp [(Rowl.FunctionalClasses.read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
        (read_class_result_iff table bytes _ limits _).mpr range]
    | range propertyRun rangeRun =>
      simp [(Rowl.FunctionalClasses.read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
        (read_class_result_iff table bytes _ limits _).mpr rangeRun]

/-- Independent class-axiom grammar in source order: one of the six keywords,
    `(`, the maximal axiom-annotation sequence (the independent annotation
    grammar with the caller's annotation limits), the body with the caller's
    class limits, then `)`. -/
inductive AxiomRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize)
    (annotationCount annotationIri annotationLexical annotationDepth classCount classIri classDepth : Nat) :
    Tokens → core.result.Result (SourceClassAxiom × Tokens) ClassAxiomError → Prop
  | keywordError {tokens : Tokens} {error : ClassAxiomError} (failure : TakeRun eof .Axiom tokens (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth tokens (.Err error)
  | openError {keyword : Token} {tail : Tokens} {form : AxiomForm} {error : ClassAxiomError}
      (formOf : FormOf keyword.terminal = some form) (failure : TakeRun eof .Open tail (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Err error)
  | annotationError {keyword opening : Token} {tail inner : Tokens} {form : AxiomForm}
      {error : functional_annotations.AnnotationError}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (failure : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Err (.Annotation error))
  | bodyError {keyword opening : Token} {tail inner : Tokens} {form : AxiomForm} {annotations : SourceAnnotations}
      {error : ClassAxiomError}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Ok annotations))
      (failure : BodyRun rows source eof classCount classIri classDepth form annotations.remaining (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Err error)
  | closeError {keyword opening : Token} {tail inner rest : Tokens} {form : AxiomForm}
      {annotations : SourceAnnotations} {body : SourceClassAxiomBody} {error : ClassAxiomError}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Ok annotations))
      (bodyRun : BodyRun rows source eof classCount classIri classDepth form annotations.remaining (.Ok (body,rest)))
      (failure : TakeRun eof .Close rest (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Err error)
  | ready {keyword opening close : Token} {tail inner rest remaining : Tokens} {form : AxiomForm}
      {annotations : SourceAnnotations} {body : SourceClassAxiomBody}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Ok annotations))
      (bodyRun : BodyRun rows source eof classCount classIri classDepth form annotations.remaining (.Ok (body,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Ok (⟨keyword,annotations.annotations,body⟩,remaining))

/-- The actual class-axiom reader terminates on every token stream and follows
    the independent grammar. -/
theorem read_class_axiom_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (annotations : AnnotationLimits) (classes : ClassLimits) :
    ∃ result, read_class_axiom table bytes tokens annotations classes = .ok result ∧
      AxiomRun table.declarations.val bytes.val bytes.len annotations.count.val annotations.iri.val
        annotations.lexical.val annotations.depth.val classes.count.val classes.iri.val classes.depth.val tokens result := by
  obtain ⟨first,firstRead,firstCorrect⟩ := take_expected_total_correct tokens .Axiom bytes.len
  rw [read_class_axiom]
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
        exact ⟨.Err error,by simp [firstRead,axiom_form_total_correct,formOf,openRead],.openError formOf openCorrect⟩
      | Ok pair =>
        obtain ⟨opening,inner⟩ := pair
        obtain ⟨annotated,annotatedRead,annotatedCorrect⟩ :=
          Rowl.FunctionalAnnotations.read_annotations_total_correct table bytes inner annotations
        cases annotated with
        | Err error =>
          exact ⟨.Err (.Annotation error),by simp [firstRead,axiom_form_total_correct,formOf,openRead,annotatedRead],
            .annotationError formOf openCorrect annotatedCorrect⟩
        | Ok sequence =>
          obtain ⟨body,bodyRead,bodyCorrect⟩ := read_body_total_correct table bytes form sequence.remaining classes
          cases body with
          | Err error =>
            exact ⟨.Err error,by simp [firstRead,axiom_form_total_correct,formOf,openRead,annotatedRead,bodyRead],
              .bodyError formOf openCorrect annotatedCorrect bodyCorrect⟩
          | Ok pair =>
            obtain ⟨body,rest⟩ := pair
            obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
            cases closed with
            | Err error =>
              exact ⟨.Err error,by simp [firstRead,axiom_form_total_correct,formOf,openRead,annotatedRead,bodyRead,
                closeRead],.closeError formOf openCorrect annotatedCorrect bodyCorrect closeCorrect⟩
            | Ok pair =>
              obtain ⟨close,remaining⟩ := pair
              exact ⟨.Ok (⟨keyword,sequence.annotations,body⟩,remaining),
                by simp [firstRead,axiom_form_total_correct,formOf,openRead,annotatedRead,bodyRead,closeRead],
                .ready formOf openCorrect annotatedCorrect bodyCorrect closeCorrect⟩
/-- Every exact class axiom and first error is equivalent to its independent derivation. -/
theorem read_class_axiom_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (annotations : AnnotationLimits) (classes : ClassLimits)
    (result : core.result.Result (SourceClassAxiom × Tokens) ClassAxiomError) :
    read_class_axiom table bytes tokens annotations classes = .ok result ↔
      AxiomRun table.declarations.val bytes.val bytes.len annotations.count.val annotations.iri.val
        annotations.lexical.val annotations.depth.val classes.count.val classes.iri.val classes.depth.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_class_axiom_total_correct table bytes tokens annotations classes
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_class_axiom]
    cases source with
    | keywordError failure => simp [(take_expected_result_iff tokens .Axiom bytes.len _).mpr failure]
    | @openError keyword tail form error formOf failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,axiom_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr failure]
    | @annotationError keyword opening tail inner form error formOf opened failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,axiom_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr opened,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner annotations _).mpr failure]
    | @bodyError keyword opening tail inner form sequence error formOf opened annotated failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,axiom_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr opened,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner annotations _).mpr annotated,
        (read_body_result_iff table bytes form _ classes _).mpr failure]
    | @closeError keyword opening tail inner rest form sequence body error formOf opened annotated bodyRun failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,axiom_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr opened,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner annotations _).mpr annotated,
        (read_body_result_iff table bytes form _ classes _).mpr bodyRun,
        (take_expected_result_iff rest .Close bytes.len _).mpr failure]
    | @ready keyword opening close tail inner rest remaining form sequence body formOf opened annotated bodyRun closing =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,axiom_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr opened,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner annotations _).mpr annotated,
        (read_body_result_iff table bytes form _ classes _).mpr bodyRun,
        (take_expected_result_iff rest .Close bytes.len _).mpr closing]
end Rowl.FunctionalClassAxioms
