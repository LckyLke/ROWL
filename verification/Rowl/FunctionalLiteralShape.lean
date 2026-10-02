import Rowl.FunctionalHeaderIdentity

namespace Rowl.FunctionalLiteralShape
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open functional_literals functional_lexer functional
open Rowl.FunctionalHeaderIdentity (Kind iri_kind_total_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- A following language tag or datatype indicator belongs to this literal;
    every other terminal begins the unchanged remaining suffix. -/
inductive TailShape : Tokens → SourceLiteralForm → Tokens → Prop
  | empty : TailShape .Empty .Plain .Empty
  | stop (token : Token) (rest : Tokens)
      (notTyped : token.terminal ≠ .DatatypeIndicator) (notLanguage : token.terminal ≠ .LanguageTag) :
      TailShape (.Cons token rest) .Plain (.Cons token rest)
  | language (token : Token) (rest : Tokens) (tag : token.terminal = .LanguageTag) :
      TailShape (.Cons token rest) (.Language token) rest
  | typed (indicator datatype : Token) (rest : Tokens) (marker : indicator.terminal = .DatatypeIndicator)
      (kind : ∃ family, Kind datatype.terminal = some family) :
      TailShape (.Cons indicator (.Cons datatype rest)) (.Typed indicator datatype) rest
/-- The independent one/two/three-token literal grammar retains all source tokens. -/
def BodyShape (tokens : Tokens) (shape : LiteralShape) : Prop :=
  shape.quoted.terminal = .QuotedString ∧
    ∃ tail, tokens = .Cons shape.quoted tail ∧ TailShape tail shape.form shape.remaining
/-- Exact first missing or incorrect terminal, before any payload interpretation. -/
inductive ShapeError (eof : Usize) : Tokens → SourceLiteralError → Prop
  | empty : ShapeError eof .Empty (.Expected .Quoted eof)
  | wrong (token : Token) (tail : Tokens) (different : token.terminal ≠ .QuotedString) :
      ShapeError eof (.Cons token tail) (.Expected .Quoted token.start)
  | missingDatatype (quoted indicator : Token) (quote : quoted.terminal = .QuotedString)
      (marker : indicator.terminal = .DatatypeIndicator) :
      ShapeError eof (.Cons quoted (.Cons indicator .Empty)) (.Expected .Datatype eof)
  | wrongDatatype (quoted indicator datatype : Token) (rest : Tokens)
      (quote : quoted.terminal = .QuotedString) (marker : indicator.terminal = .DatatypeIndicator)
      (notIri : Kind datatype.terminal = none) :
      ShapeError eof (.Cons quoted (.Cons indicator (.Cons datatype rest))) (.Expected .Datatype datatype.start)
def ShapeCorrect (tokens : Tokens) (eof : Usize) : core.result.Result LiteralShape SourceLiteralError → Prop
  | .Ok shape => BodyShape tokens shape
  | .Err error => ShapeError eof tokens error

private theorem plain_actual (quoted : Token) (tail : Tokens) (eof : Usize)
    (quote : quoted.terminal = .QuotedString) (plain : TailShape tail .Plain tail) :
    read_shape (.Cons quoted tail) eof = .ok (.Ok ⟨quoted,.Plain,tail⟩) := by
  cases plain with
  | empty => cases quoted; simp_all [read_shape]
  | stop token rest notTyped notLanguage =>
    cases quoted with
    | mk terminal start finish =>
      simp only [Token.terminal] at quote
      subst terminal
      cases token with
      | mk terminal start finish => cases terminal <;> simp_all [read_shape]
private theorem language_actual (quoted tag : Token) (rest : Tokens) (eof : Usize)
    (quote : quoted.terminal = .QuotedString) (language : tag.terminal = .LanguageTag) :
    read_shape (.Cons quoted (.Cons tag rest)) eof = .ok (.Ok ⟨quoted,.Language tag,rest⟩) := by
  cases quoted; cases tag; simp_all [read_shape]
private theorem typed_actual (quoted indicator datatype : Token) (rest : Tokens) (eof : Usize)
    (quote : quoted.terminal = .QuotedString) (marker : indicator.terminal = .DatatypeIndicator)
    (kind : ∃ family, Kind datatype.terminal = some family) :
    read_shape (.Cons quoted (.Cons indicator (.Cons datatype rest))) eof =
      .ok (.Ok ⟨quoted,.Typed indicator datatype,rest⟩) := by
  obtain ⟨family,kind⟩ := kind
  cases quoted; cases indicator; simp_all [read_shape,iri_kind_total_correct,core.option.Option.is_some]
private theorem shape_error_actual {tokens : Tokens} {eof : Usize} {error : SourceLiteralError}
    (failure : ShapeError eof tokens error) : read_shape tokens eof = .ok (.Err error) := by
  cases failure with
  | empty => rfl
  | wrong token tail different => cases token with
    | mk terminal start finish => cases terminal <;> simp_all [read_shape]
  | missingDatatype quoted indicator quote marker =>
    cases quoted; cases indicator; simp_all [read_shape]
  | wrongDatatype quoted indicator datatype rest quote marker notIri =>
    cases quoted; cases indicator; simp_all [read_shape,iri_kind_total_correct,core.option.Option.is_some]
private theorem shape_actual {tokens : Tokens} {shape : LiteralShape} {eof : Usize}
    (body : BodyShape tokens shape) : read_shape tokens eof = .ok (.Ok shape) := by
  obtain ⟨quote,tail,rfl,tailDerivation⟩ := body
  cases shape with
  | mk quoted form remaining =>
    cases form with
    | Plain => cases tailDerivation with
      | empty => exact plain_actual quoted .Empty eof quote .empty
      | stop token rest notTyped notLanguage => exact plain_actual quoted (.Cons token rest) eof quote (.stop token rest notTyped notLanguage)
    | Language token => cases tailDerivation with
      | language => exact language_actual quoted token remaining eof quote (by assumption)
    | Typed indicator datatype => cases tailDerivation with
      | typed => exact typed_actual quoted indicator datatype remaining eof quote (by assumption) (by assumption)

/-- Actual literal-shape reading is total for arbitrary supplied token streams. -/
theorem read_shape_total_correct (tokens : Tokens) (eof : Usize) :
    ∃ result, read_shape tokens eof = .ok result ∧ ShapeCorrect tokens eof result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected .Quoted eof),rfl,.empty⟩
  | Cons quoted tail =>
    by_cases quote : quoted.terminal = .QuotedString
    · cases tail with
      | Empty => exact ⟨.Ok ⟨quoted,.Plain,.Empty⟩,plain_actual quoted .Empty eof quote .empty,quote,.Empty,rfl,.empty⟩
      | Cons token rest =>
        by_cases marker : token.terminal = .DatatypeIndicator
        · cases rest with
          | Empty =>
            have failure := ShapeError.missingDatatype (eof := eof) quoted token quote marker
            exact ⟨.Err (.Expected .Datatype eof),shape_error_actual failure,failure⟩
          | Cons datatype remaining =>
            cases classified : Kind datatype.terminal with
            | none =>
              have failure := ShapeError.wrongDatatype (eof := eof) quoted token datatype remaining quote marker classified
              exact ⟨.Err (.Expected .Datatype datatype.start),shape_error_actual failure,failure⟩
            | some family =>
              have kind : ∃ family, Kind datatype.terminal = some family := ⟨family,classified⟩
              exact ⟨.Ok ⟨quoted,.Typed token datatype,remaining⟩,
                typed_actual quoted token datatype remaining eof quote marker kind,quote,_,rfl,.typed token datatype remaining marker kind⟩
        · by_cases language : token.terminal = .LanguageTag
          · exact ⟨.Ok ⟨quoted,.Language token,rest⟩,language_actual quoted token rest eof quote language,
              quote,_,rfl,.language token rest language⟩
          · exact ⟨.Ok ⟨quoted,.Plain,.Cons token rest⟩,
              plain_actual quoted (.Cons token rest) eof quote (.stop token rest marker language),
              quote,_,rfl,.stop token rest marker language⟩
    · have failure := ShapeError.wrong (eof := eof) quoted tail quote
      exact ⟨.Err (.Expected .Quoted quoted.start),shape_error_actual failure,failure⟩

/-- Every exact literal shape or syntax error is equivalent to the independent grammar. -/
theorem read_shape_result_iff (tokens : Tokens) (eof : Usize)
    (result : core.result.Result LiteralShape SourceLiteralError) :
    read_shape tokens eof = .ok result ↔ ShapeCorrect tokens eof result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_shape_total_correct tokens eof
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases result with
    | Ok shape => exact shape_actual source
    | Err error => exact shape_error_actual source

/-- Typed shapes always supply one of the two accepted source IRI terminal kinds. -/
theorem typed_shape_kind {tokens : Tokens} {quoted indicator datatype : Token} {rest : Tokens}
    (shape : BodyShape tokens ⟨quoted,.Typed indicator datatype,rest⟩) :
    ∃ family, Kind datatype.terminal = some family := by
  obtain ⟨_,_,_,form⟩ := shape
  cases form with
  | typed _ _ _ _ kind => exact kind
/-- Each literal form consumes exactly its one, two or three source terminals. -/
def FormTokens : SourceLiteralForm → Nat
  | .Plain => 1
  | .Language _ => 2
  | .Typed _ _ => 3
/-- A complete shape strictly consumes the literal and preserves its entire suffix. -/
theorem shape_token_count {tokens : Tokens} {shape : LiteralShape} (body : BodyShape tokens shape) :
    Rowl.FunctionalLexer.TokenCount tokens = FormTokens shape.form + Rowl.FunctionalLexer.TokenCount shape.remaining := by
  cases shape
  obtain ⟨_,tail,rfl,derived⟩ := body
  cases derived <;> simp [Rowl.FunctionalLexer.TokenCount,FormTokens] <;> omega
end Rowl.FunctionalLiteralShape
