import Rowl.FunctionalHeaderShape

namespace Rowl.FunctionalHeaderImport
open Aeneas Aeneas.Std Aeneas.Std.Result RowlFrontendRust
open RowlFrontendRust.functional_header RowlFrontendRust.functional_lexer RowlFrontendRust.functional
open Rowl.FunctionalHeaderIdentity Rowl.FunctionalHeaderShape
set_option linter.unusedSimpArgs false

/-- Independent complete import-body source grammar and resolution priority.
    All punctuation/kind checks precede target IRI expansion and its budget. -/
inductive BodyRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (HeaderIri × Tokens) HeaderError → Prop
  | syntaxError {tokens : Tokens} {error : HeaderError}
      (failure : Mismatch [.Open,.Iri,.Close] tokens eof error) :
      BodyRun rows source eof limit tokens (.Err error)
  | iriError {tokens rest : Tokens} {target : Token} {kind : functional_iris.SourceIriKind}
      {error : functional_iris.SourceIriError}
      (shape : BodyShape tokens target rest) (iriKind : Kind target.terminal = some kind)
      (failure : Rowl.FunctionalIris.ErrorCorrect rows kind source target.start.val target.end.val limit error) :
      BodyRun rows source eof limit tokens (.Err (.Iri error))
  | ready {tokens rest : Tokens} {target : Token} {kind : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8}
      (shape : BodyShape tokens target rest) (iriKind : Kind target.terminal = some kind)
      (valueSource : Rowl.FunctionalIris.Success rows kind source target.start.val target.end.val limit value) :
      BodyRun rows source eof limit tokens (.Ok (⟨target,value⟩,rest))

theorem read_import_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) :
    ∃ result, read_import table bytes tokens limit = .ok result ∧
      BodyRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  obtain ⟨shapeResult,shapeRead,shapeCorrect⟩ := read_import_shape_total_correct tokens bytes.len
  rw [read_import,shapeRead,bind_ok]
  cases shapeResult with
  | Err error => exact ⟨.Err error,rfl,.syntaxError shapeCorrect⟩
  | Ok shape =>
    have skeleton := shapeCorrect
    obtain ⟨opening,closing,_,_,targetKind,_⟩ := skeleton
    obtain ⟨kind,classified⟩ := (expected_iri_kind shape.target.terminal).mp targetKind
    simp only
    rw [iri_kind_total_correct,classified,bind_ok]
    obtain ⟨result,executed,correct⟩ := Rowl.FunctionalIris.resolve_span_total_correct table kind bytes shape.target.start shape.target.end limit
    simp only
    rw [executed,bind_ok]
    cases result with
    | Err error => exact ⟨.Err (.Iri error),rfl,.iriError shapeCorrect classified correct⟩
    | Ok value => exact ⟨.Ok (⟨shape.target,value⟩,shape.remaining),rfl,.ready shapeCorrect classified correct⟩

theorem read_import_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) (result : core.result.Result (HeaderIri × Tokens) HeaderError) :
    read_import table bytes tokens limit = .ok result ↔
      BodyRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_import_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | syntaxError failure =>
      have shapeRead := (read_import_shape_result_iff tokens bytes.len (.Err _)).mpr failure
      simp [read_import,shapeRead]
    | @iriError rest target kind error shape iriKind failure =>
      have shapeRead := (read_import_shape_result_iff tokens bytes.len (.Ok ⟨target,rest⟩)).mpr shape
      have iriRead := (Rowl.FunctionalIris.resolve_span_error_iff table kind bytes target.start target.end limit error).mpr failure
      simp [read_import,shapeRead,iri_kind_total_correct,iriKind,iriRead]
    | @ready rest target kind value shape iriKind valueSource =>
      have shapeRead := (read_import_shape_result_iff tokens bytes.len (.Ok ⟨target,rest⟩)).mpr shape
      have iriRead := (Rowl.FunctionalIris.resolve_span_value_iff table kind bytes target.start target.end limit value).mpr valueSource
      simp [read_import,shapeRead,iri_kind_total_correct,iriKind,iriRead]

theorem import_source_value {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens rest : Tokens} {target : HeaderIri} (accepted : BodyRun rows source eof limit tokens (.Ok (target,rest))) :
    BodyShape tokens target.token rest ∧ IriValue rows source limit target := by
  cases accepted with
  | ready shape iriKind valueSource => exact ⟨shape,_,iriKind,valueSource⟩

theorem import_token_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens rest : Tokens} {target : HeaderIri} (accepted : BodyRun rows source eof limit tokens (.Ok (target,rest))) :
    Rowl.FunctionalLexer.TokenCount tokens = 3+Rowl.FunctionalLexer.TokenCount rest := by
  exact import_shape_count (import_source_value accepted).1

end Rowl.FunctionalHeaderImport
