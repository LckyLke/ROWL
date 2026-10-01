import Rowl.FunctionalAnnotations

namespace Rowl.FunctionalAnnotationAxioms
open Aeneas Aeneas.Std Aeneas.Std.Result RowlFrontendRust
open RowlFrontendRust.functional_annotation_axioms
open RowlFrontendRust.functional_annotations (AnnotationLimits SourceAnnotations SourceAnnotationValue)
open RowlFrontendRust.functional_header (HeaderIri)
open RowlFrontendRust.functional_lexer RowlFrontendRust.functional
open Rowl.FunctionalHeaderIdentity (Kind IriValue iri_kind_total_correct)
open Rowl.FunctionalLexer (TokenCount)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The four standard annotation-axiom keywords and their axiom kinds. -/
def AxiomKind : Terminal → Option AnnotationAxiomKind
  | .Keyword .AnnotationAssertion => some .Assertion
  | .Keyword .SubAnnotationPropertyOf => some .SubProperty
  | .Keyword .AnnotationPropertyDomain => some .Domain
  | .Keyword .AnnotationPropertyRange => some .Range
  | _ => none
/-- The two annotation-subject families: an IRI or an anonymous individual. -/
def SubjectKind : Terminal → Option AnnotationSubjectKind
  | .FullIri => some (.Iri .Full)
  | .AbbreviatedIri => some (.Iri .Abbreviated)
  | .NodeId => some .Anonymous
  | _ => none
/-- Independent first-terminal class required at each annotation-axiom position. -/
def Expected : AnnotationAxiomExpected → Terminal → Prop
  | .Keyword, terminal => ∃ kind, AxiomKind terminal = some kind
  | .Open, terminal => terminal = .Open
  | .Property, terminal => ∃ kind, Kind terminal = some kind
  | .Subject, terminal => ∃ kind, SubjectKind terminal = some kind
  | .Iri, terminal => ∃ kind, Kind terminal = some kind
  | .Close, terminal => terminal = .Close
/-- One syntax step: the first token must belong to the expected class. A
    missing token reports the original source length, a wrong one its start. -/
inductive TakeRun (eof : Usize) (expected : AnnotationAxiomExpected) :
    Tokens → core.result.Result (Token × Tokens) AnnotationAxiomError → Prop
  | empty : TakeRun eof expected .Empty (.Err (.Expected expected eof))
  | wrong (token : Token) (rest : Tokens) (different : ¬ Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Err (.Expected expected token.start))
  | taken (token : Token) (rest : Tokens) (accepted : Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Ok (token,rest))

/-- Actual axiom-keyword classification equals the independent four kinds. -/
theorem axiom_kind_total_correct (terminal : Terminal) : axiom_kind terminal = .ok (AxiomKind terminal) := by
  cases terminal <;> first | rfl | (rename_i keyword; cases keyword <;> rfl)
/-- Actual subject classification equals the independent two families. -/
theorem subject_kind_total_correct (terminal : Terminal) : subject_kind terminal = .ok (SubjectKind terminal) := by
  cases terminal <;> rfl
/-- Actual position checks decide exactly the independent terminal classes. -/
theorem expected_terminal_total_correct (expected : AnnotationAxiomExpected) (terminal : Terminal) :
    expected_terminal expected terminal = .ok (decide (Expected expected terminal)) := by
  cases expected <;> cases terminal <;> (try (rename_i keyword; cases keyword)) <;>
    simp [expected_terminal,Expected,axiom_kind_total_correct,subject_kind_total_correct,iri_kind_total_correct,
      AxiomKind,SubjectKind,Kind,core.option.Option.is_some]

/-- One-token syntax checking is total and follows the independent step. -/
theorem take_expected_total_correct (tokens : Tokens) (expected : AnnotationAxiomExpected) (eof : Usize) :
    ∃ result, take_expected tokens expected eof = .ok result ∧ TakeRun eof expected tokens result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected expected eof),rfl,.empty⟩
  | Cons token rest =>
    by_cases accepted : Expected expected token.terminal
    · exact ⟨.Ok (token,rest),by simp [take_expected,expected_terminal_total_correct,accepted],.taken _ _ accepted⟩
    · exact ⟨.Err (.Expected expected token.start),by simp [take_expected,expected_terminal_total_correct,accepted],
        .wrong _ _ accepted⟩
private theorem take_run_unique {eof : Usize} {expected : AnnotationAxiomExpected} {tokens : Tokens}
    {one two : core.result.Result (Token × Tokens) AnnotationAxiomError}
    (first : TakeRun eof expected tokens one) (second : TakeRun eof expected tokens two) : one = two := by
  cases first <;> cases second <;> first | rfl | contradiction
/-- Every exact one-token result or syntax error is equivalent to the independent step. -/
theorem take_expected_result_iff (tokens : Tokens) (expected : AnnotationAxiomExpected) (eof : Usize)
    (result : core.result.Result (Token × Tokens) AnnotationAxiomError) :
    take_expected tokens expected eof = .ok result ↔ TakeRun eof expected tokens result := by
  obtain ⟨actual,executed,correct⟩ := take_expected_total_correct tokens expected eof
  constructor
  · intro output
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    have same := take_run_unique correct source
    simpa [same] using executed
/-- An accepted syntax step consumes exactly its own token. -/
theorem take_progress {eof : Usize} {expected : AnnotationAxiomExpected} {tokens rest : Tokens} {token : Token}
    (taken : TakeRun eof expected tokens (.Ok (token,rest))) : TokenCount tokens = 1+TokenCount rest := by
  cases taken
  rfl

/-- The two IRI positions accept exactly the full and abbreviated IRI terminals. -/
theorem iri_position_expected {expected : AnnotationAxiomExpected} (position : expected = .Property ∨ expected = .Iri)
    (terminal : Terminal) : Expected expected terminal ↔ ∃ kind, Kind terminal = some kind := by
  rcases position with rfl | rfl <;> exact Iff.rfl
/-- Independent IRI-position grammar: one full or abbreviated IRI token whose
    original span resolves through the checked prefix rows. -/
inductive IriRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat)
    (expected : AnnotationAxiomExpected) :
    Tokens → core.result.Result (HeaderIri × Tokens) AnnotationAxiomError → Prop
  | syntaxError {tokens : Tokens} {error : AnnotationAxiomError} (failure : TakeRun eof expected tokens (.Err error)) :
      IriRun rows source eof limit expected tokens (.Err error)
  | iriError {token : Token} {rest : Tokens} {kind : functional_iris.SourceIriKind}
      {error : functional_iris.SourceIriError} (iriKind : Kind token.terminal = some kind)
      (failure : Rowl.FunctionalIris.ErrorCorrect rows kind source token.start.val token.end.val limit error) :
      IriRun rows source eof limit expected (.Cons token rest) (.Err (.Iri error))
  | value {token : Token} {rest : Tokens} {kind : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8}
      (iriKind : Kind token.terminal = some kind)
      (valueSource : Rowl.FunctionalIris.Success rows kind source token.start.val token.end.val limit value) :
      IriRun rows source eof limit expected (.Cons token rest) (.Ok (⟨token,value⟩,rest))

/-- IRI reading at a property or IRI position is total; its fallback is unreachable. -/
theorem read_iri_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (expected : AnnotationAxiomExpected) (limit : Usize) (position : expected = .Property ∨ expected = .Iri) :
    ∃ result, read_iri table bytes tokens expected limit = .ok result ∧
      IriRun table.declarations.val bytes.val bytes.len limit.val expected tokens result := by
  obtain ⟨taken,takeRead,takeCorrect⟩ := take_expected_total_correct tokens expected bytes.len
  rw [read_iri]
  simp only [takeRead,bind_ok]
  cases taken with
  | Err error => exact ⟨.Err error,rfl,.syntaxError takeCorrect⟩
  | Ok pair =>
    obtain ⟨token,rest⟩ := pair
    cases takeCorrect with
    | taken _ _ accepted =>
      obtain ⟨kind,classified⟩ := (iri_position_expected position token.terminal).mp accepted
      simp only [uncurry_apply_pair,iri_kind_total_correct,classified,bind_ok]
      obtain ⟨result,executed,correct⟩ :=
        Rowl.FunctionalIris.resolve_span_total_correct table kind bytes token.start token.end limit
      simp only [executed,bind_ok]
      cases result with
      | Ok value => exact ⟨.Ok (⟨token,value⟩,rest),rfl,.value classified correct⟩
      | Err error => exact ⟨.Err (.Iri error),rfl,.iriError classified correct⟩

/-- Every exact IRI value and first error is equivalent to its derivation. -/
theorem read_iri_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (expected : AnnotationAxiomExpected) (limit : Usize) (position : expected = .Property ∨ expected = .Iri)
    (result : core.result.Result (HeaderIri × Tokens) AnnotationAxiomError) :
    read_iri table bytes tokens expected limit = .ok result ↔
      IriRun table.declarations.val bytes.val bytes.len limit.val expected tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_iri_total_correct table bytes tokens expected limit position
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | syntaxError failure =>
      have takeRead := (take_expected_result_iff tokens expected bytes.len _).mpr failure
      simp [read_iri,takeRead]
    | @iriError token rest kind error iriKind failure =>
      have takeRead := (take_expected_result_iff (.Cons token rest) expected bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ((iri_position_expected position token.terminal).mpr ⟨kind,iriKind⟩))
      have iriRead := (Rowl.FunctionalIris.resolve_span_error_iff table kind bytes token.start token.end limit error).mpr failure
      simp [read_iri,takeRead,iri_kind_total_correct,iriKind,iriRead]
    | @value token rest kind value iriKind valueSource =>
      have takeRead := (take_expected_result_iff (.Cons token rest) expected bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ((iri_position_expected position token.terminal).mpr ⟨kind,iriKind⟩))
      have iriRead := (Rowl.FunctionalIris.resolve_span_value_iff table kind bytes token.start token.end limit value).mpr valueSource
      simp [read_iri,takeRead,iri_kind_total_correct,iriKind,iriRead]

/-- Accepted IRIs are exact source-linked values and consume their one token. -/
theorem iri_source_value {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {expected : AnnotationAxiomExpected} {tokens rest : Tokens} {iri : HeaderIri}
    (accepted : IriRun rows source eof limit expected tokens (.Ok (iri,rest))) :
    tokens = .Cons iri.token rest ∧ IriValue rows source limit iri := by
  cases accepted with
  | value iriKind valueSource => exact ⟨rfl,_,iriKind,valueSource⟩

/-- Independent annotation-subject grammar: an IRI resolves through the checked
    prefix rows; a node ID keeps its exact label without `_:`. -/
inductive SubjectRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (SourceAnnotationSubject × Tokens) AnnotationAxiomError → Prop
  | syntaxError {tokens : Tokens} {error : AnnotationAxiomError} (failure : TakeRun eof .Subject tokens (.Err error)) :
      SubjectRun rows source eof limit tokens (.Err error)
  | iriError {token : Token} {rest : Tokens} {kind : functional_iris.SourceIriKind}
      {error : functional_iris.SourceIriError} (subjectKind : SubjectKind token.terminal = some (.Iri kind))
      (failure : Rowl.FunctionalIris.ErrorCorrect rows kind source token.start.val token.end.val limit error) :
      SubjectRun rows source eof limit (.Cons token rest) (.Err (.Iri error))
  | iri {token : Token} {rest : Tokens} {kind : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8}
      (subjectKind : SubjectKind token.terminal = some (.Iri kind))
      (valueSource : Rowl.FunctionalIris.Success rows kind source token.start.val token.end.val limit value) :
      SubjectRun rows source eof limit (.Cons token rest) (.Ok (.Iri ⟨token,value⟩,rest))
  | anonymousError {token : Token} {rest : Tokens} {error : functional_names.NameError}
      (subjectKind : SubjectKind token.terminal = some .Anonymous)
      (failure : Rowl.FunctionalNames.ErrorCorrect .NodeId source token.start.val token.end.val limit error) :
      SubjectRun rows source eof limit (.Cons token rest) (.Err (.Anonymous error))
  | anonymous {token : Token} {rest : Tokens} {label : alloc.vec.Vec U8}
      (subjectKind : SubjectKind token.terminal = some .Anonymous)
      (labelValue : Rowl.FunctionalNames.Correct .NodeId source token.start.val token.end.val limit (.Ok label)) :
      SubjectRun rows source eof limit (.Cons token rest) (.Ok (.Anonymous token label,rest))

/-- Subject reading is total; its fallback after a checked subject token is unreachable. -/
theorem read_subject_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) :
    ∃ result, read_subject table bytes tokens limit = .ok result ∧
      SubjectRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  obtain ⟨taken,takeRead,takeCorrect⟩ := take_expected_total_correct tokens .Subject bytes.len
  rw [read_subject]
  simp only [takeRead,bind_ok]
  cases taken with
  | Err error => exact ⟨.Err error,rfl,.syntaxError takeCorrect⟩
  | Ok pair =>
    obtain ⟨token,rest⟩ := pair
    cases takeCorrect with
    | taken _ _ accepted =>
      obtain ⟨kind,classified⟩ := accepted
      simp only [uncurry_apply_pair,subject_kind_total_correct,classified,bind_ok]
      cases kind with
      | Iri family =>
        obtain ⟨result,executed,correct⟩ :=
          Rowl.FunctionalIris.resolve_span_total_correct table family bytes token.start token.end limit
        simp only [executed,bind_ok]
        cases result with
        | Ok value => exact ⟨.Ok (.Iri ⟨token,value⟩,rest),rfl,.iri classified correct⟩
        | Err error => exact ⟨.Err (.Iri error),rfl,.iriError classified correct⟩
      | Anonymous =>
        obtain ⟨result,executed,correct⟩ :=
          Rowl.FunctionalNames.read_span_total_correct .NodeId bytes token.start token.end limit
        simp only [executed,bind_ok]
        cases result with
        | Ok label => exact ⟨.Ok (.Anonymous token label,rest),rfl,.anonymous classified correct⟩
        | Err error => exact ⟨.Err (.Anonymous error),rfl,.anonymousError classified correct⟩

/-- Every exact subject and first error is equivalent to its independent derivation. -/
theorem read_subject_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize)
    (result : core.result.Result (SourceAnnotationSubject × Tokens) AnnotationAxiomError) :
    read_subject table bytes tokens limit = .ok result ↔
      SubjectRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_subject_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | syntaxError failure =>
      have takeRead := (take_expected_result_iff tokens .Subject bytes.len _).mpr failure
      simp [read_subject,takeRead]
    | @iriError token rest kind error subjectKind failure =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Subject bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,subjectKind⟩)
      have iriRead := (Rowl.FunctionalIris.resolve_span_error_iff table kind bytes token.start token.end limit error).mpr failure
      simp [read_subject,takeRead,subject_kind_total_correct,subjectKind,iriRead]
    | @iri token rest kind value subjectKind valueSource =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Subject bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,subjectKind⟩)
      have iriRead := (Rowl.FunctionalIris.resolve_span_value_iff table kind bytes token.start token.end limit value).mpr valueSource
      simp [read_subject,takeRead,subject_kind_total_correct,subjectKind,iriRead]
    | @anonymousError token rest error subjectKind failure =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Subject bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,subjectKind⟩)
      have labelRead := (Rowl.FunctionalNames.read_span_error_iff .NodeId bytes token.start token.end limit error).mpr failure
      simp [read_subject,takeRead,subject_kind_total_correct,subjectKind,labelRead]
    | @anonymous token rest label subjectKind labelValue =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Subject bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,subjectKind⟩)
      have labelRead := (Rowl.FunctionalNames.read_span_accepted_iff .NodeId bytes token.start token.end limit label).mpr labelValue
      simp [read_subject,takeRead,subject_kind_total_correct,subjectKind,labelRead]

/-- An accepted subject consumes exactly its one token. -/
theorem subject_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens rest : Tokens} {subject : SourceAnnotationSubject}
    (accepted : SubjectRun rows source eof limit tokens (.Ok (subject,rest))) :
    TokenCount tokens = 1+TokenCount rest := by
  cases accepted <;> rfl

/-- The axiom kind each body constructor represents. -/
def BodyKind : SourceAnnotationAxiomBody → AnnotationAxiomKind
  | .Assertion _ _ _ => .Assertion
  | .SubProperty _ _ => .SubProperty
  | .Domain _ _ => .Domain
  | .Range _ _ => .Range
/-- Independent annotation-axiom body grammar in source order. Every body starts
    with an annotation property; an assertion continues with a subject and a value,
    a subproperty axiom with a second property, and domain/range axioms with an IRI. -/
inductive BodyRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (iriLimit lexLimit : Nat) :
    AnnotationAxiomKind → Tokens → core.result.Result (SourceAnnotationAxiomBody × Tokens) AnnotationAxiomError →
      Prop
  | propertyError {kind : AnnotationAxiomKind} {tokens : Tokens} {error : AnnotationAxiomError}
      (failure : IriRun rows source eof iriLimit .Property tokens (.Err error)) :
      BodyRun rows source eof iriLimit lexLimit kind tokens (.Err error)
  | subjectError {tokens middle : Tokens} {property : HeaderIri} {error : AnnotationAxiomError}
      (named : IriRun rows source eof iriLimit .Property tokens (.Ok (property,middle)))
      (failure : SubjectRun rows source eof iriLimit middle (.Err error)) :
      BodyRun rows source eof iriLimit lexLimit .Assertion tokens (.Err error)
  | valueError {tokens middle rest : Tokens} {property : HeaderIri} {subject : SourceAnnotationSubject}
      {error : functional_annotations.AnnotationError}
      (named : IriRun rows source eof iriLimit .Property tokens (.Ok (property,middle)))
      (subjected : SubjectRun rows source eof iriLimit middle (.Ok (subject,rest)))
      (failure : Rowl.FunctionalAnnotationParts.ValueRun rows source eof iriLimit lexLimit rest (.Err error)) :
      BodyRun rows source eof iriLimit lexLimit .Assertion tokens (.Err (.Value error))
  | assertion {tokens middle rest remaining : Tokens} {property : HeaderIri} {subject : SourceAnnotationSubject}
      {value : SourceAnnotationValue}
      (named : IriRun rows source eof iriLimit .Property tokens (.Ok (property,middle)))
      (subjected : SubjectRun rows source eof iriLimit middle (.Ok (subject,rest)))
      (valued : Rowl.FunctionalAnnotationParts.ValueRun rows source eof iriLimit lexLimit rest (.Ok (value,remaining))) :
      BodyRun rows source eof iriLimit lexLimit .Assertion tokens (.Ok (.Assertion property subject value,remaining))
  | superError {tokens middle : Tokens} {property : HeaderIri} {error : AnnotationAxiomError}
      (named : IriRun rows source eof iriLimit .Property tokens (.Ok (property,middle)))
      (failure : IriRun rows source eof iriLimit .Property middle (.Err error)) :
      BodyRun rows source eof iriLimit lexLimit .SubProperty tokens (.Err error)
  | subProperty {tokens middle remaining : Tokens} {property superProperty : HeaderIri}
      (named : IriRun rows source eof iriLimit .Property tokens (.Ok (property,middle)))
      (superNamed : IriRun rows source eof iriLimit .Property middle (.Ok (superProperty,remaining))) :
      BodyRun rows source eof iriLimit lexLimit .SubProperty tokens (.Ok (.SubProperty property superProperty,remaining))
  | domainError {tokens middle : Tokens} {property : HeaderIri} {error : AnnotationAxiomError}
      (named : IriRun rows source eof iriLimit .Property tokens (.Ok (property,middle)))
      (failure : IriRun rows source eof iriLimit .Iri middle (.Err error)) :
      BodyRun rows source eof iriLimit lexLimit .Domain tokens (.Err error)
  | domain {tokens middle remaining : Tokens} {property target : HeaderIri}
      (named : IriRun rows source eof iriLimit .Property tokens (.Ok (property,middle)))
      (targeted : IriRun rows source eof iriLimit .Iri middle (.Ok (target,remaining))) :
      BodyRun rows source eof iriLimit lexLimit .Domain tokens (.Ok (.Domain property target,remaining))
  | rangeError {tokens middle : Tokens} {property : HeaderIri} {error : AnnotationAxiomError}
      (named : IriRun rows source eof iriLimit .Property tokens (.Ok (property,middle)))
      (failure : IriRun rows source eof iriLimit .Iri middle (.Err error)) :
      BodyRun rows source eof iriLimit lexLimit .Range tokens (.Err error)
  | range {tokens middle remaining : Tokens} {property target : HeaderIri}
      (named : IriRun rows source eof iriLimit .Property tokens (.Ok (property,middle)))
      (targeted : IriRun rows source eof iriLimit .Iri middle (.Ok (target,remaining))) :
      BodyRun rows source eof iriLimit lexLimit .Range tokens (.Ok (.Range property target,remaining))

/-- Body reading is total for every axiom kind and follows the independent grammar. -/
theorem read_body_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (kind : AnnotationAxiomKind) (tokens : Tokens) (limits : AnnotationLimits) :
    ∃ result, read_body table bytes kind tokens limits = .ok result ∧
      BodyRun table.declarations.val bytes.val bytes.len limits.iri.val limits.lexical.val kind tokens result := by
  obtain ⟨named,nameRead,nameCorrect⟩ := read_iri_total_correct table bytes tokens .Property limits.iri (.inl rfl)
  rw [read_body]
  simp only [nameRead,bind_ok]
  cases named with
  | Err error => exact ⟨.Err error,rfl,.propertyError nameCorrect⟩
  | Ok pair =>
    obtain ⟨property,middle⟩ := pair
    simp only [uncurry_apply_pair]
    cases kind with
    | Assertion =>
      obtain ⟨subjected,subjectRead,subjectCorrect⟩ := read_subject_total_correct table bytes middle limits.iri
      simp only [subjectRead,bind_ok]
      cases subjected with
      | Err error => exact ⟨.Err error,rfl,.subjectError nameCorrect subjectCorrect⟩
      | Ok pair =>
        obtain ⟨subject,rest⟩ := pair
        obtain ⟨valued,valueRead,valueCorrect⟩ := Rowl.FunctionalAnnotationParts.read_value_total_correct table bytes rest limits
        simp only [uncurry_apply_pair,valueRead,bind_ok]
        cases valued with
        | Err error => exact ⟨.Err (.Value error),rfl,.valueError nameCorrect subjectCorrect valueCorrect⟩
        | Ok pair =>
          obtain ⟨value,remaining⟩ := pair
          exact ⟨.Ok (.Assertion property subject value,remaining),rfl,.assertion nameCorrect subjectCorrect valueCorrect⟩
    | SubProperty =>
      obtain ⟨superNamed,superRead,superCorrect⟩ := read_iri_total_correct table bytes middle .Property limits.iri (.inl rfl)
      simp only [superRead,bind_ok]
      cases superNamed with
      | Err error => exact ⟨.Err error,rfl,.superError nameCorrect superCorrect⟩
      | Ok pair =>
        obtain ⟨superProperty,remaining⟩ := pair
        exact ⟨.Ok (.SubProperty property superProperty,remaining),rfl,.subProperty nameCorrect superCorrect⟩
    | Domain =>
      obtain ⟨targeted,targetRead,targetCorrect⟩ := read_iri_total_correct table bytes middle .Iri limits.iri (.inr rfl)
      simp only [targetRead,bind_ok]
      cases targeted with
      | Err error => exact ⟨.Err error,rfl,.domainError nameCorrect targetCorrect⟩
      | Ok pair =>
        obtain ⟨target,remaining⟩ := pair
        exact ⟨.Ok (.Domain property target,remaining),rfl,.domain nameCorrect targetCorrect⟩
    | Range =>
      obtain ⟨targeted,targetRead,targetCorrect⟩ := read_iri_total_correct table bytes middle .Iri limits.iri (.inr rfl)
      simp only [targetRead,bind_ok]
      cases targeted with
      | Err error => exact ⟨.Err error,rfl,.rangeError nameCorrect targetCorrect⟩
      | Ok pair =>
        obtain ⟨target,remaining⟩ := pair
        exact ⟨.Ok (.Range property target,remaining),rfl,.range nameCorrect targetCorrect⟩

/-- Every exact body and first error is equivalent to its independent derivation. -/
theorem read_body_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (kind : AnnotationAxiomKind) (tokens : Tokens) (limits : AnnotationLimits)
    (result : core.result.Result (SourceAnnotationAxiomBody × Tokens) AnnotationAxiomError) :
    read_body table bytes kind tokens limits = .ok result ↔
      BodyRun table.declarations.val bytes.val bytes.len limits.iri.val limits.lexical.val kind tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_body_total_correct table bytes kind tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    have property := fun result => read_iri_result_iff table bytes tokens .Property limits.iri (.inl rfl) result
    cases source with
    | propertyError failure =>
      have nameRead := (property _).mpr failure
      cases kind <;> simp [read_body,nameRead]
    | subjectError named failure =>
      have nameRead := (property _).mpr named
      have subjectRead := (read_subject_result_iff table bytes _ limits.iri _).mpr failure
      simp [read_body,nameRead,subjectRead]
    | valueError named subjected failure =>
      have nameRead := (property _).mpr named
      have subjectRead := (read_subject_result_iff table bytes _ limits.iri _).mpr subjected
      have valueRead := (Rowl.FunctionalAnnotationParts.read_value_result_iff table bytes _ limits _).mpr failure
      simp [read_body,nameRead,subjectRead,valueRead]
    | assertion named subjected valued =>
      have nameRead := (property _).mpr named
      have subjectRead := (read_subject_result_iff table bytes _ limits.iri _).mpr subjected
      have valueRead := (Rowl.FunctionalAnnotationParts.read_value_result_iff table bytes _ limits _).mpr valued
      simp [read_body,nameRead,subjectRead,valueRead]
    | superError named failure =>
      have nameRead := (property _).mpr named
      have superRead := (read_iri_result_iff table bytes _ .Property limits.iri (.inl rfl) _).mpr failure
      simp [read_body,nameRead,superRead]
    | subProperty named superNamed =>
      have nameRead := (property _).mpr named
      have superRead := (read_iri_result_iff table bytes _ .Property limits.iri (.inl rfl) _).mpr superNamed
      simp [read_body,nameRead,superRead]
    | domainError named failure =>
      have nameRead := (property _).mpr named
      have targetRead := (read_iri_result_iff table bytes _ .Iri limits.iri (.inr rfl) _).mpr failure
      simp [read_body,nameRead,targetRead]
    | domain named targeted =>
      have nameRead := (property _).mpr named
      have targetRead := (read_iri_result_iff table bytes _ .Iri limits.iri (.inr rfl) _).mpr targeted
      simp [read_body,nameRead,targetRead]
    | rangeError named failure =>
      have nameRead := (property _).mpr named
      have targetRead := (read_iri_result_iff table bytes _ .Iri limits.iri (.inr rfl) _).mpr failure
      simp [read_body,nameRead,targetRead]
    | range named targeted =>
      have nameRead := (property _).mpr named
      have targetRead := (read_iri_result_iff table bytes _ .Iri limits.iri (.inr rfl) _).mpr targeted
      simp [read_body,nameRead,targetRead]

/-- A successful body has the requested kind, starts with an exact source-linked
    annotation property and consumes at least two tokens. -/
theorem body_source_values {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}
    {iriLimit lexLimit : Nat} {kind : AnnotationAxiomKind} {tokens remaining : Tokens}
    {body : SourceAnnotationAxiomBody}
    (accepted : BodyRun rows source eof iriLimit lexLimit kind tokens (.Ok (body,remaining))) :
    BodyKind body = kind ∧ TokenCount remaining+2 ≤ TokenCount tokens := by
  cases accepted with
  | assertion named subjected valued =>
    have one := (iri_source_value named).1
    have two := subject_progress subjected
    have three := Rowl.FunctionalAnnotationParts.value_progress valued
    subst one
    refine ⟨rfl,?_⟩
    simp only [TokenCount] at *
    omega
  | subProperty named superNamed =>
    have one := (iri_source_value named).1
    have two := (iri_source_value superNamed).1
    subst one two
    exact ⟨rfl,by simp only [TokenCount]; omega⟩
  | domain named targeted =>
    have one := (iri_source_value named).1
    have two := (iri_source_value targeted).1
    subst one two
    exact ⟨rfl,by simp only [TokenCount]; omega⟩
  | range named targeted =>
    have one := (iri_source_value named).1
    have two := (iri_source_value targeted).1
    subst one two
    exact ⟨rfl,by simp only [TokenCount]; omega⟩

/-- Independent annotation-axiom grammar in source order: the axiom keyword, `(`,
    the maximal axiom-annotation sequence (the independent annotation grammar
    with the caller's limits), the body for that keyword's kind, then `)`. -/
inductive AxiomRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize)
    (count iriLimit lexLimit depth : Nat) :
    Tokens → core.result.Result (SourceAnnotationAxiom × Tokens) AnnotationAxiomError → Prop
  | keywordError {tokens : Tokens} {error : AnnotationAxiomError}
      (failure : TakeRun eof .Keyword tokens (.Err error)) :
      AxiomRun rows source eof count iriLimit lexLimit depth tokens (.Err error)
  | openError {keyword : Token} {tail : Tokens} {kind : AnnotationAxiomKind} {error : AnnotationAxiomError}
      (axiomKind : AxiomKind keyword.terminal = some kind) (failure : TakeRun eof .Open tail (.Err error)) :
      AxiomRun rows source eof count iriLimit lexLimit depth (.Cons keyword tail) (.Err error)
  | annotationError {keyword opening : Token} {tail inner : Tokens} {kind : AnnotationAxiomKind}
      {error : functional_annotations.AnnotationError}
      (axiomKind : AxiomKind keyword.terminal = some kind) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (failure : Rowl.FunctionalAnnotations.ScanRun rows source eof count iriLimit lexLimit depth inner [] (.Err error)) :
      AxiomRun rows source eof count iriLimit lexLimit depth (.Cons keyword tail) (.Err (.Annotation error))
  | bodyError {keyword opening : Token} {tail inner : Tokens} {kind : AnnotationAxiomKind}
      {annotations : SourceAnnotations} {error : AnnotationAxiomError}
      (axiomKind : AxiomKind keyword.terminal = some kind) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof count iriLimit lexLimit depth inner []
        (.Ok annotations))
      (failure : BodyRun rows source eof iriLimit lexLimit kind annotations.remaining (.Err error)) :
      AxiomRun rows source eof count iriLimit lexLimit depth (.Cons keyword tail) (.Err error)
  | closeError {keyword opening : Token} {tail inner rest : Tokens} {kind : AnnotationAxiomKind}
      {annotations : SourceAnnotations} {body : SourceAnnotationAxiomBody} {error : AnnotationAxiomError}
      (axiomKind : AxiomKind keyword.terminal = some kind) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof count iriLimit lexLimit depth inner []
        (.Ok annotations))
      (bodied : BodyRun rows source eof iriLimit lexLimit kind annotations.remaining (.Ok (body,rest)))
      (failure : TakeRun eof .Close rest (.Err error)) :
      AxiomRun rows source eof count iriLimit lexLimit depth (.Cons keyword tail) (.Err error)
  | ready {keyword opening close : Token} {tail inner rest remaining : Tokens} {kind : AnnotationAxiomKind}
      {annotations : SourceAnnotations} {body : SourceAnnotationAxiomBody}
      (axiomKind : AxiomKind keyword.terminal = some kind) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof count iriLimit lexLimit depth inner []
        (.Ok annotations))
      (bodied : BodyRun rows source eof iriLimit lexLimit kind annotations.remaining (.Ok (body,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      AxiomRun rows source eof count iriLimit lexLimit depth (.Cons keyword tail)
        (.Ok (⟨keyword,annotations.annotations,body⟩,remaining))

/-- The actual annotation-axiom reader terminates on every token stream and follows
    the independent grammar, including all axiom annotations. -/
theorem read_annotation_axiom_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limits : AnnotationLimits) :
    ∃ result, read_annotation_axiom table bytes tokens limits = .ok result ∧
      AxiomRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val
        limits.lexical.val limits.depth.val tokens result := by
  obtain ⟨first,firstRead,firstCorrect⟩ := take_expected_total_correct tokens .Keyword bytes.len
  rw [read_annotation_axiom]
  simp only [firstRead,bind_ok]
  cases first with
  | Err error => exact ⟨.Err error,rfl,.keywordError firstCorrect⟩
  | Ok pair =>
    obtain ⟨keyword,tail⟩ := pair
    cases firstCorrect with
    | taken _ _ accepted =>
      obtain ⟨kind,classified⟩ := accepted
      simp only [uncurry_apply_pair,axiom_kind_total_correct,classified,bind_ok]
      obtain ⟨opened,openRead,openCorrect⟩ := take_expected_total_correct tail .Open bytes.len
      simp only [openRead,bind_ok]
      cases opened with
      | Err error => exact ⟨.Err error,rfl,.openError classified openCorrect⟩
      | Ok pair =>
        obtain ⟨opening,inner⟩ := pair
        obtain ⟨annotated,annotatedRead,annotatedCorrect⟩ :=
          Rowl.FunctionalAnnotations.read_annotations_total_correct table bytes inner limits
        simp only [uncurry_apply_pair,annotatedRead,bind_ok]
        cases annotated with
        | Err error => exact ⟨.Err (.Annotation error),rfl,.annotationError classified openCorrect annotatedCorrect⟩
        | Ok annotations =>
          obtain ⟨bodied,bodyRead,bodyCorrect⟩ := read_body_total_correct table bytes kind annotations.remaining limits
          simp only [bodyRead,bind_ok]
          cases bodied with
          | Err error => exact ⟨.Err error,rfl,.bodyError classified openCorrect annotatedCorrect bodyCorrect⟩
          | Ok pair =>
            obtain ⟨body,rest⟩ := pair
            obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
            simp only [uncurry_apply_pair,closeRead,bind_ok]
            cases closed with
            | Err error =>
              exact ⟨.Err error,rfl,.closeError classified openCorrect annotatedCorrect bodyCorrect closeCorrect⟩
            | Ok pair =>
              obtain ⟨close,remaining⟩ := pair
              exact ⟨.Ok (⟨keyword,annotations.annotations,body⟩,remaining),rfl,
                .ready classified openCorrect annotatedCorrect bodyCorrect closeCorrect⟩

/-- Every exact annotation axiom and first error is equivalent to its derivation. -/
theorem read_annotation_axiom_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limits : AnnotationLimits)
    (result : core.result.Result (SourceAnnotationAxiom × Tokens) AnnotationAxiomError) :
    read_annotation_axiom table bytes tokens limits = .ok result ↔
      AxiomRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val
        limits.lexical.val limits.depth.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_annotation_axiom_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | keywordError failure =>
      have firstRead := (take_expected_result_iff tokens .Keyword bytes.len _).mpr failure
      simp [read_annotation_axiom,firstRead]
    | @openError keyword tail kind error axiomKind failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Keyword bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨kind,axiomKind⟩)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr failure
      simp [read_annotation_axiom,firstRead,axiom_kind_total_correct,axiomKind,openRead]
    | @annotationError keyword opening tail inner kind error axiomKind opened failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Keyword bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨kind,axiomKind⟩)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
      have annotatedRead := (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner limits _).mpr failure
      simp [read_annotation_axiom,firstRead,axiom_kind_total_correct,axiomKind,openRead,annotatedRead]
    | @bodyError keyword opening tail inner kind annotations error axiomKind opened annotated failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Keyword bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨kind,axiomKind⟩)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
      have annotatedRead := (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner limits _).mpr annotated
      have bodyRead := (read_body_result_iff table bytes kind annotations.remaining limits _).mpr failure
      simp [read_annotation_axiom,firstRead,axiom_kind_total_correct,axiomKind,openRead,annotatedRead,bodyRead]
    | @closeError keyword opening tail inner rest kind annotations body error axiomKind opened annotated bodied failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Keyword bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨kind,axiomKind⟩)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
      have annotatedRead := (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner limits _).mpr annotated
      have bodyRead := (read_body_result_iff table bytes kind annotations.remaining limits _).mpr bodied
      have closeRead := (take_expected_result_iff rest .Close bytes.len _).mpr failure
      simp [read_annotation_axiom,firstRead,axiom_kind_total_correct,axiomKind,openRead,annotatedRead,bodyRead,closeRead]
    | @ready keyword opening close tail inner rest remaining kind annotations body axiomKind opened annotated bodied
        closing =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Keyword bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨kind,axiomKind⟩)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
      have annotatedRead := (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner limits _).mpr annotated
      have bodyRead := (read_body_result_iff table bytes kind annotations.remaining limits _).mpr bodied
      have closeRead := (take_expected_result_iff rest .Close bytes.len _).mpr closing
      simp [read_annotation_axiom,firstRead,axiom_kind_total_correct,axiomKind,openRead,annotatedRead,bodyRead,closeRead]

/-- A successful annotation axiom keeps its original keyword, whose kind matches
    the body; its axiom annotations form exactly the independent maximal section
    within the count limit, and it consumes at least five tokens plus five for
    every top-level axiom annotation. -/
theorem annotation_axiom_source_values {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}
    {count iriLimit lexLimit depth : Nat} {tokens remaining : Tokens} {record : SourceAnnotationAxiom}
    (accepted : AxiomRun rows source eof count iriLimit lexLimit depth tokens (.Ok (record,remaining))) :
    AxiomKind record.keyword.terminal = some (BodyKind record.body) ∧
    record.annotations.val.length ≤ count ∧
    (∃ inner middle, Rowl.FunctionalAnnotations.Section rows source eof count iriLimit lexLimit depth inner
      record.annotations.val middle) ∧
    TokenCount remaining+5+5*record.annotations.val.length ≤ TokenCount tokens := by
  generalize outputEq : core.result.Result.Ok (record,remaining) = output at accepted
  cases accepted with
  | keywordError | openError | annotationError | bodyError | closeError => cases outputEq
  | @ready keyword opening close tail inner rest remaining' kind annotations body axiomKind opened annotated bodied
      closing =>
    injection outputEq with same
    injection same with recordSame remainingSame
    subst recordSame remainingSame
    obtain ⟨bound,derivation⟩ := Rowl.FunctionalAnnotations.scan_section_accepted annotated
    obtain ⟨bodyKind,bodyCount⟩ := body_source_values bodied
    have one := take_progress opened
    have two := Rowl.FunctionalAnnotations.section_token_count derivation
    have three := take_progress closing
    refine ⟨by simpa [bodyKind] using axiomKind,bound,⟨inner,annotations.remaining,derivation⟩,?_⟩
    simp only [TokenCount] at *
    omega
end Rowl.FunctionalAnnotationAxioms
