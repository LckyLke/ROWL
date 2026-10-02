import Rowl.FunctionalLiteralShape
import Rowl.FunctionalLiteralValues

namespace Rowl.FunctionalLiterals
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open functional_literals functional_lexer functional
open Rowl.FunctionalLiteralShape (BodyShape ShapeError ShapeCorrect typed_shape_kind)
open Rowl.FunctionalLiteralValues (StringValue SpanError SpanCorrect PlainDatatype PlainLexical DatatypeCorrect)
open Rowl.FunctionalHeaderIdentity (Kind iri_kind_total_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- Preserve the unconsumed source tokens on success; errors expose no partial value. -/
def WithSuffix (rest : Tokens) : core.result.Result SourceLiteral SourceLiteralError →
    core.result.Result (SourceLiteral × Tokens) SourceLiteralError
  | .Ok value => .Ok (value,rest)
  | .Err error => .Err error
/-- Independent literal finishing rules: explicit types retain lexical bytes;
    the two plain-string shortcuts require exact rdf:PlainLiteral expansion.
    Language and IRI errors precede output assembly; final lexical limits
    precede the constant datatype limit. No datatype value-space claim is made. -/
inductive FinishRun (rows : List prefixes.Declaration) (source : List U8) (lexLimit datatypeLimit : Nat)
    (quoted : Token) (payload : alloc.vec.Vec U8) :
    SourceLiteralForm → core.result.Result SourceLiteral SourceLiteralError → Prop
  | typedValue {indicator datatype : Token} {family : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8}
      (kind : Kind datatype.terminal = some family)
      (iri : Rowl.FunctionalIris.Success rows family source datatype.start.val datatype.end.val datatypeLimit value) :
      FinishRun rows source lexLimit datatypeLimit quoted payload (.Typed indicator datatype)
        (.Ok ⟨quoted,.Typed indicator datatype,payload,value⟩)
  | typedError {indicator datatype : Token} {family : functional_iris.SourceIriKind} {error : functional_iris.SourceIriError}
      (kind : Kind datatype.terminal = some family)
      (iri : Rowl.FunctionalIris.ErrorCorrect rows family source datatype.start.val datatype.end.val datatypeLimit error) :
      FinishRun rows source lexLimit datatypeLimit quoted payload (.Typed indicator datatype) (.Err (.Datatype error))
  | plainLimit (full : lexLimit < (PlainLexical payload.val []).length) :
      FinishRun rows source lexLimit datatypeLimit quoted payload .Plain (.Err (.LexicalLimit quoted.start))
  | plainDatatypeError {lexical : alloc.vec.Vec U8} {error : SourceLiteralError}
      (lex : Rowl.Prefixes.Joined (payload.val ++ [64#u8]) [] lexLimit (some lexical))
      (datatype : DatatypeCorrect datatypeLimit quoted.start (.Err error)) :
      FinishRun rows source lexLimit datatypeLimit quoted payload .Plain (.Err error)
  | plainValue {lexical datatype : alloc.vec.Vec U8}
      (lex : Rowl.Prefixes.Joined (payload.val ++ [64#u8]) [] lexLimit (some lexical))
      (typed : DatatypeCorrect datatypeLimit quoted.start (.Ok datatype)) :
      FinishRun rows source lexLimit datatypeLimit quoted payload .Plain (.Ok ⟨quoted,.Plain,lexical,datatype⟩)
  | languageError {tag : Token} {error : functional_names.NameError}
      (failure : Rowl.FunctionalNames.ErrorCorrect .LanguageTag source tag.start.val tag.end.val lexLimit error) :
      FinishRun rows source lexLimit datatypeLimit quoted payload (.Language tag) (.Err (.Language error))
  | languageLimit {tag : Token} {language : alloc.vec.Vec U8}
      (tagValue : Rowl.FunctionalNames.Correct .LanguageTag source tag.start.val tag.end.val lexLimit (.Ok language))
      (full : lexLimit < (PlainLexical payload.val language.val).length) :
      FinishRun rows source lexLimit datatypeLimit quoted payload (.Language tag) (.Err (.LexicalLimit quoted.start))
  | languageDatatypeError {tag : Token} {language lexical : alloc.vec.Vec U8} {error : SourceLiteralError}
      (tagValue : Rowl.FunctionalNames.Correct .LanguageTag source tag.start.val tag.end.val lexLimit (.Ok language))
      (lex : Rowl.Prefixes.Joined (payload.val ++ [64#u8]) language.val lexLimit (some lexical))
      (datatype : DatatypeCorrect datatypeLimit quoted.start (.Err error)) :
      FinishRun rows source lexLimit datatypeLimit quoted payload (.Language tag) (.Err error)
  | languageValue {tag : Token} {language lexical datatype : alloc.vec.Vec U8}
      (tagValue : Rowl.FunctionalNames.Correct .LanguageTag source tag.start.val tag.end.val lexLimit (.Ok language))
      (lex : Rowl.Prefixes.Joined (payload.val ++ [64#u8]) language.val lexLimit (some lexical))
      (typed : DatatypeCorrect datatypeLimit quoted.start (.Ok datatype)) :
      FinishRun rows source lexLimit datatypeLimit quoted payload (.Language tag)
        (.Ok ⟨quoted,.Language tag,lexical,datatype⟩)
/-- Independent syntax, source-payload and finishing derivations in their exact
    priority order. The entire original suffix remains on every successful result. -/
inductive Run (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (lexLimit datatypeLimit : Nat) :
    Tokens → core.result.Result (SourceLiteral × Tokens) SourceLiteralError → Prop
  | syntaxFailure {tokens : Tokens} {error : SourceLiteralError} (failure : ShapeError eof tokens error) :
      Run rows source eof lexLimit datatypeLimit tokens (.Err error)
  | quoted {tokens : Tokens} {shape : LiteralShape} {error : SourceLiteralError}
      (body : BodyShape tokens shape) (failure : SpanError source shape.quoted lexLimit error) :
      Run rows source eof lexLimit datatypeLimit tokens (.Err error)
  | finished {tokens : Tokens} {shape : LiteralShape} {payload : alloc.vec.Vec U8}
      {result : core.result.Result SourceLiteral SourceLiteralError}
      (body : BodyShape tokens shape) (decoded : StringValue source shape.quoted lexLimit payload)
      (finish : FinishRun rows source lexLimit datatypeLimit shape.quoted payload shape.form result) :
      Run rows source eof lexLimit datatypeLimit tokens (WithSuffix shape.remaining result)

/-- The actual Rust literal reader terminates for arbitrary source bytes/tokens,
    with exact source spelling, mandatory expansion and first-phase diagnostics. -/
theorem read_literal_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (lexLimit datatypeLimit : Usize) :
    ∃ result, read_literal table bytes tokens lexLimit datatypeLimit = .ok result ∧
      Run table.declarations.val bytes.val bytes.len lexLimit.val datatypeLimit.val tokens result := by
  obtain ⟨shapeResult,shapeRead,shapeCorrect⟩ := Rowl.FunctionalLiteralShape.read_shape_total_correct tokens bytes.len
  rw [read_literal,shapeRead,bind_ok]
  cases shapeResult with
  | Err error => exact ⟨.Err error,rfl,.syntaxFailure shapeCorrect⟩
  | Ok shape =>
    simp only
    obtain ⟨payloadResult,payloadRead,payloadCorrect⟩ := Rowl.FunctionalLiteralValues.string_span_total_correct bytes shape.quoted lexLimit
    rw [payloadRead,bind_ok]
    cases payloadResult with
    | Err error => exact ⟨.Err error,rfl,.quoted shapeCorrect payloadCorrect⟩
    | Ok payload =>
      simp only
      cases shape with
      | mk quoted form rest =>
        cases form with
        | Typed indicator datatype =>
          simp only
          obtain ⟨family,kind⟩ := typed_shape_kind shapeCorrect
          rw [iri_kind_total_correct,kind,bind_ok]
          simp only
          obtain ⟨iriResult,iriRead,iriCorrect⟩ := Rowl.FunctionalIris.resolve_span_total_correct table family bytes datatype.start datatype.end datatypeLimit
          rw [iriRead,bind_ok]
          cases iriResult with
          | Ok value => exact ⟨.Ok (⟨quoted,.Typed indicator datatype,payload,value⟩,rest),rfl,
              .finished shapeCorrect payloadCorrect (.typedValue kind iriCorrect)⟩
          | Err error => exact ⟨.Err (.Datatype error),rfl,.finished shapeCorrect payloadCorrect (.typedError kind iriCorrect)⟩
        | Plain =>
          simp only
          obtain ⟨lexResult,lexRead,lexCorrect⟩ := Rowl.FunctionalLiteralValues.plain_lexical_total_correct payload (alloc.vec.Vec.new U8) lexLimit
          rw [lexRead,bind_ok]
          cases lexResult with
          | none =>
            have full : lexLimit.val < (PlainLexical payload.val []).length := by simpa [Rowl.Prefixes.Joined,PlainLexical,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using lexCorrect
            exact ⟨.Err (.LexicalLimit quoted.start),rfl,.finished shapeCorrect payloadCorrect (.plainLimit full)⟩
          | some lexical =>
            simp only
            obtain ⟨datatypeResult,datatypeRead,datatypeCorrect⟩ := Rowl.FunctionalLiteralValues.plain_datatype_total_correct datatypeLimit quoted.start
            rw [datatypeRead,bind_ok]
            cases datatypeResult with
            | Ok datatype => exact ⟨.Ok (⟨quoted,.Plain,lexical,datatype⟩,rest),rfl,
                .finished shapeCorrect payloadCorrect (.plainValue (by simpa using lexCorrect) datatypeCorrect)⟩
            | Err error => exact ⟨.Err error,rfl,.finished shapeCorrect payloadCorrect
                (.plainDatatypeError (by simpa using lexCorrect) datatypeCorrect)⟩
        | Language tag =>
          simp only
          obtain ⟨tagResult,tagRead,tagCorrect⟩ := Rowl.FunctionalNames.read_span_total_correct .LanguageTag bytes tag.start tag.end lexLimit
          rw [tagRead,bind_ok]
          cases tagResult with
          | Err error => exact ⟨.Err (.Language error),rfl,.finished shapeCorrect payloadCorrect (.languageError tagCorrect)⟩
          | Ok language =>
            simp only
            obtain ⟨lexResult,lexRead,lexCorrect⟩ := Rowl.FunctionalLiteralValues.plain_lexical_total_correct payload language lexLimit
            rw [lexRead,bind_ok]
            cases lexResult with
            | none =>
              have full : lexLimit.val < (PlainLexical payload.val language.val).length := by simpa [Rowl.Prefixes.Joined,PlainLexical,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using lexCorrect
              exact ⟨.Err (.LexicalLimit quoted.start),rfl,.finished shapeCorrect payloadCorrect (.languageLimit tagCorrect full)⟩
            | some lexical =>
              simp only
              obtain ⟨datatypeResult,datatypeRead,datatypeCorrect⟩ := Rowl.FunctionalLiteralValues.plain_datatype_total_correct datatypeLimit quoted.start
              rw [datatypeRead,bind_ok]
              cases datatypeResult with
              | Ok datatype => exact ⟨.Ok (⟨quoted,.Language tag,lexical,datatype⟩,rest),rfl,
                  .finished shapeCorrect payloadCorrect (.languageValue tagCorrect lexCorrect datatypeCorrect)⟩
              | Err error => exact ⟨.Err error,rfl,.finished shapeCorrect payloadCorrect
                  (.languageDatatypeError tagCorrect lexCorrect datatypeCorrect)⟩

/-- Every exact literal result and error is equivalent to the independent source
    derivation; neither unsupported fallback nor a partial payload can escape. -/
theorem read_literal_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (lexLimit datatypeLimit : Usize)
    (result : core.result.Result (SourceLiteral × Tokens) SourceLiteralError) :
    read_literal table bytes tokens lexLimit datatypeLimit = .ok result ↔
      Run table.declarations.val bytes.val bytes.len lexLimit.val datatypeLimit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_literal_total_correct table bytes tokens lexLimit datatypeLimit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | syntaxFailure failure =>
      have shapeRead := (Rowl.FunctionalLiteralShape.read_shape_result_iff tokens bytes.len (.Err _)).mpr failure
      simp [read_literal,shapeRead]
    | @quoted shape error body failure =>
      have shapeRead := (Rowl.FunctionalLiteralShape.read_shape_result_iff tokens bytes.len (.Ok shape)).mpr body
      have payloadRead := (Rowl.FunctionalLiteralValues.string_span_error_iff bytes shape.quoted lexLimit error).mpr failure
      simp [read_literal,shapeRead,payloadRead]
    | @finished shape payload result body decoded finish =>
      have shapeRead := (Rowl.FunctionalLiteralShape.read_shape_result_iff tokens bytes.len (.Ok shape)).mpr body
      have payloadRead := (Rowl.FunctionalLiteralValues.string_span_value_iff bytes shape.quoted lexLimit payload).mpr decoded
      rw [read_literal,shapeRead,bind_ok]
      simp only
      rw [payloadRead,bind_ok]
      simp only
      cases shape with
      | mk quoted form rest =>
        cases finish with
        | typedValue kind iri =>
          have iriRead := (Rowl.FunctionalIris.resolve_span_value_iff table _ bytes _ _ datatypeLimit _).mpr iri
          simp [iri_kind_total_correct,kind,iriRead,WithSuffix]
        | typedError kind iri =>
          have iriRead := (Rowl.FunctionalIris.resolve_span_error_iff table _ bytes _ _ datatypeLimit _).mpr iri
          simp [iri_kind_total_correct,kind,iriRead,WithSuffix]
        | plainLimit full =>
          have lexCorrect : Rowl.Prefixes.Joined (payload.val ++ [64#u8]) (alloc.vec.Vec.new U8).val lexLimit.val none := by
            simpa [Rowl.Prefixes.Joined,PlainLexical,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using full
          have lexRead := (Rowl.FunctionalLiteralValues.plain_lexical_result_iff payload (alloc.vec.Vec.new U8) lexLimit none).mpr lexCorrect
          simp [lexRead,WithSuffix]
        | plainDatatypeError lex datatype =>
          have lexRead := (Rowl.FunctionalLiteralValues.plain_lexical_result_iff payload (alloc.vec.Vec.new U8) lexLimit _).mpr (by simpa using lex)
          have datatypeRead := (Rowl.FunctionalLiteralValues.plain_datatype_result_iff datatypeLimit quoted.start _).mpr datatype
          simp [lexRead,datatypeRead,WithSuffix]
        | plainValue lex datatype =>
          have lexRead := (Rowl.FunctionalLiteralValues.plain_lexical_result_iff payload (alloc.vec.Vec.new U8) lexLimit _).mpr (by simpa using lex)
          have datatypeRead := (Rowl.FunctionalLiteralValues.plain_datatype_result_iff datatypeLimit quoted.start _).mpr datatype
          simp [lexRead,datatypeRead,WithSuffix]
        | languageError failure =>
          have tagRead := (Rowl.FunctionalNames.read_span_error_iff .LanguageTag bytes _ _ lexLimit _).mpr failure
          simp [tagRead,WithSuffix]
        | @languageLimit tag language tagValue full =>
          have tagRead := (Rowl.FunctionalNames.read_span_accepted_iff .LanguageTag bytes tag.start tag.end lexLimit language).mpr tagValue
          have lexCorrect : Rowl.Prefixes.Joined (payload.val ++ [64#u8]) language.val lexLimit.val none := by
            simpa [Rowl.Prefixes.Joined,PlainLexical,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using full
          have lexRead := (Rowl.FunctionalLiteralValues.plain_lexical_result_iff payload language lexLimit none).mpr lexCorrect
          simp [tagRead,lexRead,WithSuffix]
        | @languageDatatypeError tag language lexical error tagValue lex datatype =>
          have tagRead := (Rowl.FunctionalNames.read_span_accepted_iff .LanguageTag bytes tag.start tag.end lexLimit language).mpr tagValue
          have lexRead := (Rowl.FunctionalLiteralValues.plain_lexical_result_iff payload language lexLimit _).mpr lex
          have datatypeRead := (Rowl.FunctionalLiteralValues.plain_datatype_result_iff datatypeLimit quoted.start _).mpr datatype
          simp [tagRead,lexRead,datatypeRead,WithSuffix]
        | @languageValue tag language lexical datatype tagValue lex typed =>
          have tagRead := (Rowl.FunctionalNames.read_span_accepted_iff .LanguageTag bytes tag.start tag.end lexLimit language).mpr tagValue
          have lexRead := (Rowl.FunctionalLiteralValues.plain_lexical_result_iff payload language lexLimit _).mpr lex
          have datatypeRead := (Rowl.FunctionalLiteralValues.plain_datatype_result_iff datatypeLimit quoted.start _).mpr typed
          simp [tagRead,lexRead,datatypeRead,WithSuffix]
/-- Every successful finishing derivation retains the exact original quote/form
    and establishes both final structural byte budgets. -/
theorem finish_value_bounds {rows : List prefixes.Declaration} {source : List U8} {lexLimit datatypeLimit : Nat}
    {quoted : Token} {payload : alloc.vec.Vec U8} {form : SourceLiteralForm} {value : SourceLiteral}
    (run : FinishRun rows source lexLimit datatypeLimit quoted payload form (.Ok value))
    (payloadBound : payload.val.length ≤ lexLimit) :
    value.quoted = quoted ∧ value.form = form ∧ value.lexical.val.length ≤ lexLimit ∧ value.datatype.val.length ≤ datatypeLimit := by
  cases run with
  | @typedValue indicator datatype family value kind iri =>
    refine ⟨rfl,rfl,payloadBound,?_⟩
    cases family with
    | Full => obtain ⟨_,bound,contents⟩ := iri; rw [contents]; exact bound
    | Abbreviated =>
      obtain ⟨parts,_,_,_,ns,_,fits,contents,_⟩ := iri
      rw [contents,List.length_append]; exact fits
  | plainValue lex typed =>
    exact ⟨rfl,rfl,by rw [lex.2]; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using lex.1,by rw [typed.1]; exact typed.2⟩
  | languageValue tagValue lex typed =>
    exact ⟨rfl,rfl,by rw [lex.2]; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using lex.1,by rw [typed.1]; exact typed.2⟩

/-- Successful source readings expose the complete independent shape/payload/
    finishing derivation, both final budgets, and bounded quote-token progress. -/
theorem read_literal_source_values (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (lexLimit datatypeLimit : Usize) (value : SourceLiteral) (rest : Tokens)
    (read : read_literal table bytes tokens lexLimit datatypeLimit = .ok (.Ok (value,rest))) :
    value.lexical.val.length ≤ lexLimit.val ∧ value.datatype.val.length ≤ datatypeLimit.val ∧
    value.quoted.start.val < value.quoted.end.val ∧ value.quoted.end.val ≤ bytes.val.length ∧
    BodyShape tokens ⟨value.quoted,value.form,rest⟩ ∧
    ∃ payload, StringValue bytes.val value.quoted lexLimit.val payload ∧
      FinishRun table.declarations.val bytes.val lexLimit.val datatypeLimit.val value.quoted payload value.form (.Ok value) := by
  have run := (read_literal_result_iff table bytes tokens lexLimit datatypeLimit (.Ok (value,rest))).mp read
  generalize outputEq : core.result.Result.Ok (value,rest) = output at run
  cases run with
  | syntaxFailure => cases outputEq
  | quoted => cases outputEq
  | @finished shape payload result body decoded finish =>
    cases result with
    | Err error => cases outputEq
    | Ok produced =>
      have same : value = produced ∧ rest = shape.remaining := by simpa [WithSuffix] using outputEq
      obtain ⟨valueEqual,restEqual⟩ := same
      subst produced
      have bounds := finish_value_bounds finish decoded.2
      have progress := Rowl.FunctionalPayload.quoted_token_progress decoded.1
      have shapeEqual : shape = ⟨value.quoted,value.form,rest⟩ := by
        cases shape
        simp_all
      subst shape
      exact ⟨bounds.2.2.1,bounds.2.2.2,progress.1,progress.2,body,payload,decoded,finish⟩
/-- Plain-string success uses exactly the mandatory shortcut expansion. -/
theorem finish_plain_expansion {rows : List prefixes.Declaration} {source : List U8} {lexLimit datatypeLimit : Nat}
    {quoted : Token} {payload : alloc.vec.Vec U8} {value : SourceLiteral}
    (run : FinishRun rows source lexLimit datatypeLimit quoted payload .Plain (.Ok value)) :
    value.lexical.val = PlainLexical payload.val [] ∧ value.datatype.val = PlainDatatype := by
  cases run with
  | plainValue lex typed => exact ⟨by simpa [PlainLexical] using lex.2,typed.1⟩
/-- Tagged-string success expands with the exact source tag spelling/case. -/
theorem finish_language_expansion {rows : List prefixes.Declaration} {source : List U8} {lexLimit datatypeLimit : Nat}
    {quoted tag : Token} {payload : alloc.vec.Vec U8} {value : SourceLiteral}
    (run : FinishRun rows source lexLimit datatypeLimit quoted payload (.Language tag) (.Ok value)) :
    ∃ language, Rowl.FunctionalNames.Correct .LanguageTag source tag.start.val tag.end.val lexLimit (.Ok language) ∧
      value.lexical.val = PlainLexical payload.val language.val ∧ value.datatype.val = PlainDatatype := by
  cases run with
  | languageValue tagValue lex typed => exact ⟨_,tagValue,by simpa [PlainLexical] using lex.2,typed.1⟩
/-- Explicitly typed success does not rewrite lexical bytes, including explicit
    rdf:PlainLiteral; only its original datatype IRI is resolved. -/
theorem finish_typed_spelling {rows : List prefixes.Declaration} {source : List U8} {lexLimit datatypeLimit : Nat}
    {quoted indicator datatype : Token} {payload : alloc.vec.Vec U8} {value : SourceLiteral}
    (run : FinishRun rows source lexLimit datatypeLimit quoted payload (.Typed indicator datatype) (.Ok value)) :
    value.lexical = payload ∧ ∃ family, Kind datatype.terminal = some family ∧
      Rowl.FunctionalIris.Success rows family source datatype.start.val datatype.end.val datatypeLimit value.datatype := by
  cases run with
  | typedValue kind iri => exact ⟨rfl,_,kind,iri⟩
/-- The actual literal reader consumes exactly the source terminals for its form,
    guaranteeing progress for later recursive annotation/axiom parsing. -/
theorem literal_token_progress (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (lexLimit datatypeLimit : Usize) (value : SourceLiteral) (rest : Tokens)
    (read : read_literal table bytes tokens lexLimit datatypeLimit = .ok (.Ok (value,rest))) :
    Rowl.FunctionalLexer.TokenCount tokens = Rowl.FunctionalLiteralShape.FormTokens value.form + Rowl.FunctionalLexer.TokenCount rest ∧
      Rowl.FunctionalLexer.TokenCount rest < Rowl.FunctionalLexer.TokenCount tokens := by
  have shape := (read_literal_source_values table bytes tokens lexLimit datatypeLimit value rest read).2.2.2.2.1
  have count := Rowl.FunctionalLiteralShape.shape_token_count shape
  refine ⟨count,?_⟩
  change Rowl.FunctionalLexer.TokenCount tokens = Rowl.FunctionalLiteralShape.FormTokens value.form + Rowl.FunctionalLexer.TokenCount rest at count
  have positive : 0 < Rowl.FunctionalLiteralShape.FormTokens value.form := by
    cases value.form <;> simp [Rowl.FunctionalLiteralShape.FormTokens]
  omega
end Rowl.FunctionalLiterals
