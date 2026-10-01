import Rowl.FunctionalLiterals

namespace Rowl.FunctionalAnnotationParts
open Aeneas Aeneas.Std Aeneas.Std.Result RowlFrontendRust
open RowlFrontendRust.functional_annotations
open RowlFrontendRust.functional_header (HeaderIri)
open RowlFrontendRust.functional_lexer RowlFrontendRust.functional
open Rowl.FunctionalHeaderIdentity (Kind IriValue iri_kind_total_correct)
open Rowl.FunctionalLexer (TokenCount)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The three standard annotation-value terminal families: a full or
    abbreviated IRI, an anonymous-individual node ID, or a literal's quote. -/
def ValueKind : Terminal → Option AnnotationValueKind
  | .FullIri => some (.Iri .Full)
  | .AbbreviatedIri => some (.Iri .Abbreviated)
  | .NodeId => some .Anonymous
  | .QuotedString => some .Literal
  | _ => none
/-- Independent first-terminal class required at each annotation position. -/
def Expected : AnnotationExpected → Terminal → Prop
  | .Open, terminal => terminal = .Open
  | .Property, terminal => ∃ kind, Kind terminal = some kind
  | .Value, terminal => ∃ kind, ValueKind terminal = some kind
  | .Close, terminal => terminal = .Close
/-- One syntax step: the first token must belong to the expected class. A
    missing token reports the original source length, a wrong one its start. -/
inductive TakeRun (eof : Usize) (expected : AnnotationExpected) :
    Tokens → core.result.Result (Token × Tokens) AnnotationError → Prop
  | empty : TakeRun eof expected .Empty (.Err (.Expected expected eof))
  | wrong (token : Token) (rest : Tokens) (different : ¬ Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Err (.Expected expected token.start))
  | taken (token : Token) (rest : Tokens) (accepted : Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Ok (token,rest))

/-- Actual value-family classification equals the independent standard families. -/
theorem value_kind_total_correct (terminal : Terminal) : value_kind terminal = .ok (ValueKind terminal) := by
  cases terminal <;> rfl
/-- Actual position checks decide exactly the independent terminal classes. -/
theorem expected_terminal_total_correct (expected : AnnotationExpected) (terminal : Terminal) :
    expected_terminal expected terminal = .ok (decide (Expected expected terminal)) := by
  cases expected <;> cases terminal <;>
    simp [expected_terminal,Expected,iri_kind_total_correct,value_kind_total_correct,Kind,ValueKind,
      core.option.Option.is_some]

/-- One-token syntax checking is total and follows the independent step. -/
theorem take_expected_total_correct (tokens : Tokens) (expected : AnnotationExpected) (eof : Usize) :
    ∃ result, take_expected tokens expected eof = .ok result ∧ TakeRun eof expected tokens result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected expected eof),rfl,.empty⟩
  | Cons token rest =>
    by_cases accepted : Expected expected token.terminal
    · exact ⟨.Ok (token,rest),by simp [take_expected,expected_terminal_total_correct,accepted],.taken _ _ accepted⟩
    · exact ⟨.Err (.Expected expected token.start),by simp [take_expected,expected_terminal_total_correct,accepted],
        .wrong _ _ accepted⟩
private theorem take_run_unique {eof : Usize} {expected : AnnotationExpected} {tokens : Tokens}
    {one two : core.result.Result (Token × Tokens) AnnotationError}
    (first : TakeRun eof expected tokens one) (second : TakeRun eof expected tokens two) : one = two := by
  cases first <;> cases second <;> first | rfl | contradiction
/-- Every exact one-token result or syntax error is equivalent to the independent step. -/
theorem take_expected_result_iff (tokens : Tokens) (expected : AnnotationExpected) (eof : Usize)
    (result : core.result.Result (Token × Tokens) AnnotationError) :
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
theorem take_progress {eof : Usize} {expected : AnnotationExpected} {tokens rest : Tokens} {token : Token}
    (taken : TakeRun eof expected tokens (.Ok (token,rest))) : TokenCount tokens = 1+TokenCount rest := by
  cases taken
  rfl

/-- Independent annotation-property grammar: one full or abbreviated IRI whose
    original span resolves through the checked prefix rows. -/
inductive PropertyRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (HeaderIri × Tokens) AnnotationError → Prop
  | syntaxError {tokens : Tokens} {error : AnnotationError} (failure : TakeRun eof .Property tokens (.Err error)) :
      PropertyRun rows source eof limit tokens (.Err error)
  | iriError {token : Token} {rest : Tokens} {kind : functional_iris.SourceIriKind}
      {error : functional_iris.SourceIriError} (iriKind : Kind token.terminal = some kind)
      (failure : Rowl.FunctionalIris.ErrorCorrect rows kind source token.start.val token.end.val limit error) :
      PropertyRun rows source eof limit (.Cons token rest) (.Err (.Property error))
  | value {token : Token} {rest : Tokens} {kind : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8}
      (iriKind : Kind token.terminal = some kind)
      (valueSource : Rowl.FunctionalIris.Success rows kind source token.start.val token.end.val limit value) :
      PropertyRun rows source eof limit (.Cons token rest) (.Ok (⟨token,value⟩,rest))

/-- Property reading is total; its fallback after a checked IRI token is unreachable. -/
theorem read_property_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) :
    ∃ result, read_property table bytes tokens limit = .ok result ∧
      PropertyRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  obtain ⟨taken,takeRead,takeCorrect⟩ := take_expected_total_correct tokens .Property bytes.len
  rw [read_property]
  simp only [takeRead,bind_ok]
  cases taken with
  | Err error => exact ⟨.Err error,rfl,.syntaxError takeCorrect⟩
  | Ok pair =>
    obtain ⟨token,rest⟩ := pair
    cases takeCorrect with
    | taken _ _ accepted =>
      obtain ⟨kind,classified⟩ := accepted
      simp only [uncurry_apply_pair,iri_kind_total_correct,classified,bind_ok]
      obtain ⟨result,executed,correct⟩ :=
        Rowl.FunctionalIris.resolve_span_total_correct table kind bytes token.start token.end limit
      simp only [executed,bind_ok]
      cases result with
      | Ok value => exact ⟨.Ok (⟨token,value⟩,rest),rfl,.value classified correct⟩
      | Err error => exact ⟨.Err (.Property error),rfl,.iriError classified correct⟩

/-- Every exact property value and first error is equivalent to its derivation. -/
theorem read_property_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) (result : core.result.Result (HeaderIri × Tokens) AnnotationError) :
    read_property table bytes tokens limit = .ok result ↔
      PropertyRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_property_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | syntaxError failure =>
      have takeRead := (take_expected_result_iff tokens .Property bytes.len _).mpr failure
      simp [read_property,takeRead]
    | @iriError token rest kind error iriKind failure =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Property bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨kind,iriKind⟩)
      have iriRead := (Rowl.FunctionalIris.resolve_span_error_iff table kind bytes token.start token.end limit error).mpr failure
      simp [read_property,takeRead,iri_kind_total_correct,iriKind,iriRead]
    | @value token rest kind value iriKind valueSource =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Property bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨kind,iriKind⟩)
      have iriRead := (Rowl.FunctionalIris.resolve_span_value_iff table kind bytes token.start token.end limit value).mpr valueSource
      simp [read_property,takeRead,iri_kind_total_correct,iriKind,iriRead]

/-- An accepted property consumes exactly its one IRI token. -/
theorem property_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens rest : Tokens} {property : HeaderIri}
    (accepted : PropertyRun rows source eof limit tokens (.Ok (property,rest))) :
    TokenCount tokens = 1+TokenCount rest := by
  cases accepted
  rfl
/-- Accepted properties are exact source-linked header-style IRI values. -/
theorem property_source_value {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens rest : Tokens} {property : HeaderIri}
    (accepted : PropertyRun rows source eof limit tokens (.Ok (property,rest))) :
    tokens = .Cons property.token rest ∧ IriValue rows source limit property := by
  cases accepted with
  | value iriKind valueSource => exact ⟨rfl,_,iriKind,valueSource⟩

/-- Independent annotation-value grammar. The first value terminal selects the
    family: IRIs resolve through the checked prefix rows, node IDs keep their
    exact label without `_:`, and literals obey the proved literal source contract
    (including mandatory plain-literal expansion). IRI, label and literal datatype
    values share the IRI limit; literal lexical forms use the lexical limit. -/
inductive ValueRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (iriLimit lexLimit : Nat) :
    Tokens → core.result.Result (SourceAnnotationValue × Tokens) AnnotationError → Prop
  | syntaxError {tokens : Tokens} {error : AnnotationError} (failure : TakeRun eof .Value tokens (.Err error)) :
      ValueRun rows source eof iriLimit lexLimit tokens (.Err error)
  | iriError {token : Token} {rest : Tokens} {kind : functional_iris.SourceIriKind}
      {error : functional_iris.SourceIriError} (valueKind : ValueKind token.terminal = some (.Iri kind))
      (failure : Rowl.FunctionalIris.ErrorCorrect rows kind source token.start.val token.end.val iriLimit error) :
      ValueRun rows source eof iriLimit lexLimit (.Cons token rest) (.Err (.Iri error))
  | iri {token : Token} {rest : Tokens} {kind : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8}
      (valueKind : ValueKind token.terminal = some (.Iri kind))
      (valueSource : Rowl.FunctionalIris.Success rows kind source token.start.val token.end.val iriLimit value) :
      ValueRun rows source eof iriLimit lexLimit (.Cons token rest) (.Ok (.Iri ⟨token,value⟩,rest))
  | anonymousError {token : Token} {rest : Tokens} {error : functional_names.NameError}
      (valueKind : ValueKind token.terminal = some .Anonymous)
      (failure : Rowl.FunctionalNames.ErrorCorrect .NodeId source token.start.val token.end.val iriLimit error) :
      ValueRun rows source eof iriLimit lexLimit (.Cons token rest) (.Err (.Anonymous error))
  | anonymous {token : Token} {rest : Tokens} {label : alloc.vec.Vec U8}
      (valueKind : ValueKind token.terminal = some .Anonymous)
      (labelValue : Rowl.FunctionalNames.Correct .NodeId source token.start.val token.end.val iriLimit (.Ok label)) :
      ValueRun rows source eof iriLimit lexLimit (.Cons token rest) (.Ok (.Anonymous token label,rest))
  | literalError {token : Token} {rest : Tokens} {error : functional_literals.SourceLiteralError}
      (valueKind : ValueKind token.terminal = some .Literal)
      (failure : Rowl.FunctionalLiterals.Run rows source eof lexLimit iriLimit (.Cons token rest) (.Err error)) :
      ValueRun rows source eof iriLimit lexLimit (.Cons token rest) (.Err (.Literal error))
  | literal {token : Token} {rest remaining : Tokens} {literal : functional_literals.SourceLiteral}
      (valueKind : ValueKind token.terminal = some .Literal)
      (read : Rowl.FunctionalLiterals.Run rows source eof lexLimit iriLimit (.Cons token rest) (.Ok (literal,remaining))) :
      ValueRun rows source eof iriLimit lexLimit (.Cons token rest) (.Ok (.Literal literal,remaining))

/-- Value reading is total; its fallback after a checked value token is unreachable. -/
theorem read_value_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limits : AnnotationLimits) :
    ∃ result, read_value table bytes tokens limits = .ok result ∧
      ValueRun table.declarations.val bytes.val bytes.len limits.iri.val limits.lexical.val tokens result := by
  obtain ⟨taken,takeRead,takeCorrect⟩ := take_expected_total_correct tokens .Value bytes.len
  rw [read_value]
  simp only [takeRead,bind_ok]
  cases taken with
  | Err error => exact ⟨.Err error,rfl,.syntaxError takeCorrect⟩
  | Ok pair =>
    obtain ⟨token,rest⟩ := pair
    cases takeCorrect with
    | taken _ _ accepted =>
      obtain ⟨kind,classified⟩ := accepted
      simp only [uncurry_apply_pair,value_kind_total_correct,classified,bind_ok]
      cases kind with
      | Iri family =>
        obtain ⟨result,executed,correct⟩ :=
          Rowl.FunctionalIris.resolve_span_total_correct table family bytes token.start token.end limits.iri
        simp only [executed,bind_ok]
        cases result with
        | Ok value => exact ⟨.Ok (.Iri ⟨token,value⟩,rest),rfl,.iri classified correct⟩
        | Err error => exact ⟨.Err (.Iri error),rfl,.iriError classified correct⟩
      | Anonymous =>
        obtain ⟨result,executed,correct⟩ :=
          Rowl.FunctionalNames.read_span_total_correct .NodeId bytes token.start token.end limits.iri
        simp only [executed,bind_ok]
        cases result with
        | Ok label => exact ⟨.Ok (.Anonymous token label,rest),rfl,.anonymous classified correct⟩
        | Err error => exact ⟨.Err (.Anonymous error),rfl,.anonymousError classified correct⟩
      | Literal =>
        obtain ⟨result,executed,correct⟩ :=
          Rowl.FunctionalLiterals.read_literal_total_correct table bytes (.Cons token rest) limits.lexical limits.iri
        simp only [executed,bind_ok]
        cases result with
        | Ok pair =>
          obtain ⟨literal,remaining⟩ := pair
          exact ⟨.Ok (.Literal literal,remaining),rfl,.literal classified correct⟩
        | Err error => exact ⟨.Err (.Literal error),rfl,.literalError classified correct⟩

/-- Every exact value and first error is equivalent to its independent derivation. -/
theorem read_value_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limits : AnnotationLimits)
    (result : core.result.Result (SourceAnnotationValue × Tokens) AnnotationError) :
    read_value table bytes tokens limits = .ok result ↔
      ValueRun table.declarations.val bytes.val bytes.len limits.iri.val limits.lexical.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_value_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | syntaxError failure =>
      have takeRead := (take_expected_result_iff tokens .Value bytes.len _).mpr failure
      simp [read_value,takeRead]
    | @iriError token rest kind error valueKind failure =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Value bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,valueKind⟩)
      have iriRead := (Rowl.FunctionalIris.resolve_span_error_iff table kind bytes token.start token.end limits.iri error).mpr failure
      simp [read_value,takeRead,value_kind_total_correct,valueKind,iriRead]
    | @iri token rest kind value valueKind valueSource =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Value bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,valueKind⟩)
      have iriRead := (Rowl.FunctionalIris.resolve_span_value_iff table kind bytes token.start token.end limits.iri value).mpr valueSource
      simp [read_value,takeRead,value_kind_total_correct,valueKind,iriRead]
    | @anonymousError token rest error valueKind failure =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Value bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,valueKind⟩)
      have labelRead := (Rowl.FunctionalNames.read_span_error_iff .NodeId bytes token.start token.end limits.iri error).mpr failure
      simp [read_value,takeRead,value_kind_total_correct,valueKind,labelRead]
    | @anonymous token rest label valueKind labelValue =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Value bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,valueKind⟩)
      have labelRead := (Rowl.FunctionalNames.read_span_accepted_iff .NodeId bytes token.start token.end limits.iri label).mpr labelValue
      simp [read_value,takeRead,value_kind_total_correct,valueKind,labelRead]
    | @literalError token rest error valueKind failure =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Value bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,valueKind⟩)
      have literalRead := (Rowl.FunctionalLiterals.read_literal_result_iff table bytes (.Cons token rest)
        limits.lexical limits.iri (.Err error)).mpr failure
      simp [read_value,takeRead,value_kind_total_correct,valueKind,literalRead]
    | @literal token rest remaining literal valueKind read =>
      have takeRead := (take_expected_result_iff (.Cons token rest) .Value bytes.len (.Ok (token,rest))).mpr
        (.taken token rest ⟨_,valueKind⟩)
      have literalRead := (Rowl.FunctionalLiterals.read_literal_result_iff table bytes (.Cons token rest)
        limits.lexical limits.iri (.Ok (literal,remaining))).mpr read
      simp [read_value,takeRead,value_kind_total_correct,valueKind,literalRead]

/-- A successful literal source derivation consumes at least its quote token. -/
theorem literal_run_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}
    {lexLimit datatypeLimit : Nat} {tokens rest : Tokens} {literal : functional_literals.SourceLiteral}
    (run : Rowl.FunctionalLiterals.Run rows source eof lexLimit datatypeLimit tokens (.Ok (literal,rest))) :
    TokenCount rest < TokenCount tokens := by
  generalize outputEq : core.result.Result.Ok (literal,rest) = output at run
  cases run with
  | syntaxFailure => cases outputEq
  | quoted => cases outputEq
  | @finished shape payload result body decoded finish =>
    cases result with
    | Err error => cases outputEq
    | Ok produced =>
      have same : produced = literal ∧ shape.remaining = rest := by
        simpa [Rowl.FunctionalLiterals.WithSuffix,eq_comm] using outputEq
      have count := Rowl.FunctionalLiteralShape.shape_token_count body
      have positive : 0 < Rowl.FunctionalLiteralShape.FormTokens shape.form := by
        cases shape.form <;> simp [Rowl.FunctionalLiteralShape.FormTokens]
      rw [← same.2]
      omega
/-- Every accepted annotation value consumes at least one token. -/
theorem value_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {iriLimit lexLimit : Nat}
    {tokens rest : Tokens} {value : SourceAnnotationValue}
    (accepted : ValueRun rows source eof iriLimit lexLimit tokens (.Ok (value,rest))) :
    TokenCount rest < TokenCount tokens := by
  cases accepted with
  | iri => simp [TokenCount]
  | anonymous => simp [TokenCount]
  | literal _ read => exact literal_run_progress read

/-- Independent property-value-close grammar after nested annotations, with the
    first failing phase returned in source order. -/
inductive FinishRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (iriLimit lexLimit : Nat) :
    Tokens → core.result.Result AnnotationTail AnnotationError → Prop
  | propertyError {tokens : Tokens} {error : AnnotationError}
      (property : PropertyRun rows source eof iriLimit tokens (.Err error)) :
      FinishRun rows source eof iriLimit lexLimit tokens (.Err error)
  | valueError {tokens middle : Tokens} {property : HeaderIri} {error : AnnotationError}
      (named : PropertyRun rows source eof iriLimit tokens (.Ok (property,middle)))
      (value : ValueRun rows source eof iriLimit lexLimit middle (.Err error)) :
      FinishRun rows source eof iriLimit lexLimit tokens (.Err error)
  | closeError {tokens middle rest : Tokens} {property : HeaderIri} {value : SourceAnnotationValue}
      {error : AnnotationError}
      (named : PropertyRun rows source eof iriLimit tokens (.Ok (property,middle)))
      (valued : ValueRun rows source eof iriLimit lexLimit middle (.Ok (value,rest)))
      (closing : TakeRun eof .Close rest (.Err error)) :
      FinishRun rows source eof iriLimit lexLimit tokens (.Err error)
  | ready {tokens middle rest remaining : Tokens} {property : HeaderIri} {value : SourceAnnotationValue}
      {close : Token}
      (named : PropertyRun rows source eof iriLimit tokens (.Ok (property,middle)))
      (valued : ValueRun rows source eof iriLimit lexLimit middle (.Ok (value,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      FinishRun rows source eof iriLimit lexLimit tokens (.Ok ⟨property,value,remaining⟩)

/-- Property, value and closing parenthesis reading is total and phase-exact. -/
theorem finish_annotation_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limits : AnnotationLimits) :
    ∃ result, finish_annotation table bytes tokens limits = .ok result ∧
      FinishRun table.declarations.val bytes.val bytes.len limits.iri.val limits.lexical.val tokens result := by
  obtain ⟨named,namedRead,namedCorrect⟩ := read_property_total_correct table bytes tokens limits.iri
  rw [finish_annotation]
  simp only [namedRead,bind_ok]
  cases named with
  | Err error => exact ⟨.Err error,rfl,.propertyError namedCorrect⟩
  | Ok pair =>
    obtain ⟨property,middle⟩ := pair
    obtain ⟨valued,valueRead,valueCorrect⟩ := read_value_total_correct table bytes middle limits
    simp only [uncurry_apply_pair,valueRead,bind_ok]
    cases valued with
    | Err error => exact ⟨.Err error,rfl,.valueError namedCorrect valueCorrect⟩
    | Ok pair =>
      obtain ⟨value,rest⟩ := pair
      obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
      simp only [uncurry_apply_pair,closeRead,bind_ok]
      cases closed with
      | Err error => exact ⟨.Err error,rfl,.closeError namedCorrect valueCorrect closeCorrect⟩
      | Ok pair =>
        obtain ⟨close,remaining⟩ := pair
        exact ⟨.Ok ⟨property,value,remaining⟩,rfl,.ready namedCorrect valueCorrect closeCorrect⟩

/-- Every exact annotation tail and first error is equivalent to its derivation. -/
theorem finish_annotation_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limits : AnnotationLimits) (result : core.result.Result AnnotationTail AnnotationError) :
    finish_annotation table bytes tokens limits = .ok result ↔
      FinishRun table.declarations.val bytes.val bytes.len limits.iri.val limits.lexical.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := finish_annotation_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | propertyError property =>
      have namedRead := (read_property_result_iff table bytes tokens limits.iri _).mpr property
      simp [finish_annotation,namedRead]
    | valueError named value =>
      have namedRead := (read_property_result_iff table bytes tokens limits.iri _).mpr named
      have valueRead := (read_value_result_iff table bytes _ limits _).mpr value
      simp [finish_annotation,namedRead,valueRead]
    | closeError named valued closing =>
      have namedRead := (read_property_result_iff table bytes tokens limits.iri _).mpr named
      have valueRead := (read_value_result_iff table bytes _ limits _).mpr valued
      have closeRead := (take_expected_result_iff _ .Close bytes.len _).mpr closing
      simp [finish_annotation,namedRead,valueRead,closeRead]
    | ready named valued closing =>
      have namedRead := (read_property_result_iff table bytes tokens limits.iri _).mpr named
      have valueRead := (read_value_result_iff table bytes _ limits _).mpr valued
      have closeRead := (take_expected_result_iff _ .Close bytes.len _).mpr closing
      simp [finish_annotation,namedRead,valueRead,closeRead]

/-- An accepted property, value and closing parenthesis consume at least three tokens. -/
theorem finish_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {iriLimit lexLimit : Nat}
    {tokens : Tokens} {tail : AnnotationTail}
    (accepted : FinishRun rows source eof iriLimit lexLimit tokens (.Ok tail)) :
    TokenCount tail.remaining+3 ≤ TokenCount tokens := by
  cases accepted with
  | ready named valued closing =>
    have one := property_progress named
    have two := value_progress valued
    have three := take_progress closing
    simp only
    omega
end Rowl.FunctionalAnnotationParts
