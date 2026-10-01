import Rowl.FunctionalPrefixShape

namespace Rowl.FunctionalPrefixDeclaration
open Aeneas Aeneas.Std Aeneas.Std.Result RowlFrontendRust
open RowlFrontendRust.functional_prefixes RowlFrontendRust.functional_lexer RowlFrontendRust.functional
open Rowl.FunctionalPrefixShape
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- Independent complete declaration-body grammar and diagnostic order:
    all five syntax tokens, prefix value, then namespace value. Exact original
    byte spelling and all payload budgets are inherited from the name grammars. -/
inductive BodyRun (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (prefixes.Declaration × Tokens) PrefixSyntaxError → Prop
  | syntaxError {tokens : Tokens} {error : PrefixSyntaxError}
      (failure : Mismatch [.Open,.Name,.Equals,.Namespace,.Close] tokens eof error) :
      BodyRun source eof limit tokens (.Err error)
  | nameError {tokens rest : Tokens} {nameToken namespaceToken : Token} {error : functional_names.NameError}
      (shape : BodyShape tokens nameToken namespaceToken rest)
      (failure : Rowl.FunctionalNames.ErrorCorrect .PrefixName source nameToken.start.val nameToken.end.val limit error) :
      BodyRun source eof limit tokens (.Err (.Name error))
  | namespaceError {tokens rest : Tokens} {nameToken namespaceToken : Token} {nameBytes : alloc.vec.Vec U8}
      {error : functional_names.NameError} (shape : BodyShape tokens nameToken namespaceToken rest)
      (prefixValue : Rowl.FunctionalNames.Correct .PrefixName source nameToken.start.val nameToken.end.val limit (.Ok nameBytes))
      (failure : Rowl.FunctionalNames.ErrorCorrect .FullIri source namespaceToken.start.val namespaceToken.end.val limit error) :
      BodyRun source eof limit tokens (.Err (.Name error))
  | ready {tokens rest : Tokens} {nameToken namespaceToken : Token} {nameBytes namespaceBytes : alloc.vec.Vec U8}
      (shape : BodyShape tokens nameToken namespaceToken rest)
      (prefixValue : Rowl.FunctionalNames.Correct .PrefixName source nameToken.start.val nameToken.end.val limit (.Ok nameBytes))
      (namespaceValue : Rowl.FunctionalNames.Correct .FullIri source namespaceToken.start.val namespaceToken.end.val limit (.Ok namespaceBytes)) :
      BodyRun source eof limit tokens (.Ok (⟨nameBytes,namespaceBytes⟩,rest))

/-- Actual complete prefix-declaration reading terminates, preserves the exact
    source-derived values and obeys every syntax/value/error/budget phase. -/
theorem read_declaration_total_correct (bytes : alloc.vec.Vec U8) (tokens : Tokens) (limit : Usize) :
    ∃ result, read_declaration bytes tokens limit = .ok result ∧ BodyRun bytes.val bytes.len limit.val tokens result := by
  rw [read_declaration]
  obtain ⟨shapeResult,shapeRead,shapeCorrect⟩ := read_shape_total_correct tokens bytes.len
  rw [shapeRead,bind_ok]
  cases shapeResult with
  | Err error => exact ⟨.Err error,rfl,.syntaxError shapeCorrect⟩
  | Ok shape =>
    simp only
    obtain ⟨nameResult,nameRead,nameCorrect⟩ := Rowl.FunctionalNames.read_span_total_correct .PrefixName bytes shape.name.start shape.name.end limit
    rw [nameRead,bind_ok]
    cases nameResult with
    | Err error => exact ⟨.Err (.Name error),rfl,.nameError shapeCorrect nameCorrect⟩
    | Ok nameBytes =>
      simp only
      obtain ⟨namespaceResult,namespaceRead,namespaceCorrect⟩ := Rowl.FunctionalNames.read_span_total_correct .FullIri bytes shape.namespace.start shape.namespace.end limit
      rw [namespaceRead,bind_ok]
      cases namespaceResult with
      | Err error => exact ⟨.Err (.Name error),rfl,.namespaceError shapeCorrect nameCorrect namespaceCorrect⟩
      | Ok namespaceBytes => exact ⟨.Ok (⟨nameBytes,namespaceBytes⟩,shape.remaining),rfl,.ready shapeCorrect nameCorrect namespaceCorrect⟩

/-- Every independent grammatical result, including each exact first syntax
    or payload error, is exactly the result of the actual declaration reader. -/
theorem read_declaration_result_iff (bytes : alloc.vec.Vec U8) (tokens : Tokens) (limit : Usize)
    (result : core.result.Result (prefixes.Declaration × Tokens) PrefixSyntaxError) :
    read_declaration bytes tokens limit = .ok result ↔ BodyRun bytes.val bytes.len limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_declaration_total_correct bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | syntaxError failure =>
      have read := (read_shape_result_iff tokens bytes.len (.Err _)).mpr failure
      simp only [read_declaration,read,bind_ok]
    | @nameError rest nameToken namespaceToken error shape failure =>
      have read := (read_shape_result_iff tokens bytes.len (.Ok ⟨nameToken,namespaceToken,rest⟩)).mpr shape
      have nameRead := (Rowl.FunctionalNames.read_span_error_iff .PrefixName bytes nameToken.start nameToken.end limit error).mpr failure
      simp only [read_declaration,read,bind_ok,nameRead]
    | @namespaceError rest nameToken namespaceToken nameBytes error shape value failure =>
      have read := (read_shape_result_iff tokens bytes.len (.Ok ⟨nameToken,namespaceToken,rest⟩)).mpr shape
      have nameRead := (Rowl.FunctionalNames.read_span_accepted_iff .PrefixName bytes nameToken.start nameToken.end limit nameBytes).mpr value
      have namespaceRead := (Rowl.FunctionalNames.read_span_error_iff .FullIri bytes namespaceToken.start namespaceToken.end limit error).mpr failure
      simp only [read_declaration,read,bind_ok,nameRead,namespaceRead]
    | @ready rest nameToken namespaceToken nameBytes namespaceBytes shape nameValue namespaceValue =>
      have read := (read_shape_result_iff tokens bytes.len (.Ok ⟨nameToken,namespaceToken,rest⟩)).mpr shape
      have nameRead := (Rowl.FunctionalNames.read_span_accepted_iff .PrefixName bytes nameToken.start nameToken.end limit nameBytes).mpr nameValue
      have namespaceRead := (Rowl.FunctionalNames.read_span_accepted_iff .FullIri bytes namespaceToken.start namespaceToken.end limit namespaceBytes).mpr namespaceValue
      simp only [read_declaration,read,bind_ok,nameRead,namespaceRead]

/-- A successful original body has complete name/namespace source tokens, exact
    byte payloads and an unchanged suffix after exactly five syntax tokens. -/
theorem body_source_values {source : List U8} {eof : Usize} {limit : Nat} {tokens rest : Tokens}
    {declaration : prefixes.Declaration} (accepted : BodyRun source eof limit tokens (.Ok (declaration,rest))) :
    ∃ nameToken namespaceToken, BodyShape tokens nameToken namespaceToken rest ∧
      Rowl.FunctionalNames.Token .PrefixName source nameToken.start.val nameToken.end.val ∧
      Rowl.FunctionalNames.Token .FullIri source namespaceToken.start.val namespaceToken.end.val ∧
      declaration.name.val = Rowl.FunctionalNames.Payload .PrefixName source nameToken.start.val nameToken.end.val ∧
      declaration.namespace.val = Rowl.FunctionalNames.Payload .FullIri source namespaceToken.start.val namespaceToken.end.val ∧
      declaration.name.val.length ≤ limit ∧ declaration.namespace.val.length ≤ limit := by
  cases accepted with
  | @ready _ nameToken namespaceToken _ _ shape nameValue namespaceValue =>
    exact ⟨nameToken,namespaceToken,shape,nameValue.1,namespaceValue.1,nameValue.2.2,namespaceValue.2.2,
      by simpa [nameValue.2.2] using nameValue.2.1,by simpa [namespaceValue.2.2] using namespaceValue.2.1⟩

/-- Successful declarations are lexically valid standard prefix names and
    complete absolute namespace IRIs; reserved-name/duplicate rules stay separate. -/
theorem declaration_value_grammars {source : List U8} {eof : Usize} {limit : Nat} {tokens rest : Tokens}
    {declaration : prefixes.Declaration} (accepted : BodyRun source eof limit tokens (.Ok (declaration,rest))) :
    Rowl.Prefixes.PrefixAccepted declaration.name.val ∧ Rowl.Prefixes.IriAccepted declaration.namespace.val := by
  obtain ⟨nameToken,namespaceToken,_,nameTokenValid,namespaceTokenValid,nameValue,namespaceValue,_⟩ := body_source_values accepted
  constructor
  · obtain ⟨word,text,legal⟩ := Rowl.FunctionalNames.payload_grammar nameTokenValid
    exact ⟨word,by simpa [nameValue] using text,legal⟩
  · obtain ⟨word,text,legal⟩ := Rowl.FunctionalNames.payload_grammar namespaceTokenValid
    exact ⟨word,by simpa [namespaceValue] using text,legal⟩

/-- Every accepted body strictly decreases the caller token stream by exactly
    five, independently of Unicode spelling or supplied byte budgets. -/
theorem declaration_token_progress {source : List U8} {eof : Usize} {limit : Nat} {tokens rest : Tokens}
    {declaration : prefixes.Declaration} (accepted : BodyRun source eof limit tokens (.Ok (declaration,rest))) :
    Rowl.FunctionalLexer.TokenCount tokens = 5+Rowl.FunctionalLexer.TokenCount rest := by
  obtain ⟨nameToken,namespaceToken,shape,_⟩ := body_source_values accepted
  exact body_shape_count shape

end Rowl.FunctionalPrefixDeclaration
