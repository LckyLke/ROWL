import Rowl.FunctionalIris
import Rowl.FunctionalLexer

namespace Rowl.FunctionalHeaderIdentity
open Aeneas Aeneas.Std Aeneas.Std.Result RowlFrontendRust
open RowlFrontendRust.functional_header RowlFrontendRust.functional_lexer RowlFrontendRust.functional
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The two standard IRI source-terminal families. -/
def Kind : Terminal → Option functional_iris.SourceIriKind
  | .FullIri => some .Full
  | .AbbreviatedIri => some .Abbreviated
  | _ => none
/-- Exact source-linked resolved IRI value and final output budget. -/
def IriValue (rows : List prefixes.Declaration) (source : List U8) (limit : Nat) (iri : HeaderIri) : Prop :=
  ∃ kind, Kind iri.token.terminal = some kind ∧
    Rowl.FunctionalIris.Success rows kind source iri.token.start.val iri.token.end.val limit iri.value
/-- Independent optional-IRI grammar: one complete IRI is consumed when present,
    otherwise the entire original suffix is retained. Errors stop at that IRI. -/
inductive OptionalRun (rows : List prefixes.Declaration) (source : List U8) (limit : Nat) :
    Tokens → core.result.Result (Option HeaderIri × Tokens) HeaderError → Prop
  | empty : OptionalRun rows source limit .Empty (.Ok (none,.Empty))
  | absent (token : Token) (tail : Tokens) (notIri : Kind token.terminal = none) :
      OptionalRun rows source limit (.Cons token tail) (.Ok (none,.Cons token tail))
  | value {token : Token} {tail : Tokens} {kind : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8}
      (iriKind : Kind token.terminal = some kind)
      (valueSource : Rowl.FunctionalIris.Success rows kind source token.start.val token.end.val limit value) :
      OptionalRun rows source limit (.Cons token tail) (.Ok (some ⟨token,value⟩,tail))
  | failure {token : Token} {tail : Tokens} {kind : functional_iris.SourceIriKind} {error : functional_iris.SourceIriError}
      (iriKind : Kind token.terminal = some kind)
      (errorSource : Rowl.FunctionalIris.ErrorCorrect rows kind source token.start.val token.end.val limit error) :
      OptionalRun rows source limit (.Cons token tail) (.Err (.Iri error))
/-- The full optional ontology/version identity grammar and first resolution error.
    The second IRI is read only after the first; zero/one/two values are distinct. -/
inductive IdentityRun (rows : List prefixes.Declaration) (source : List U8) (limit : Nat) :
    Tokens → core.result.Result (SourceOntologyIdentity × Tokens) HeaderError → Prop
  | firstError {tokens : Tokens} {error : HeaderError}
      (first : OptionalRun rows source limit tokens (.Err error)) :
      IdentityRun rows source limit tokens (.Err error)
  | anonymous {tokens rest : Tokens}
      (first : OptionalRun rows source limit tokens (.Ok (none,rest))) :
      IdentityRun rows source limit tokens (.Ok (.Anonymous,rest))
  | secondError {tokens middle : Tokens} {ontology : HeaderIri} {error : HeaderError}
      (first : OptionalRun rows source limit tokens (.Ok (some ontology,middle)))
      (second : OptionalRun rows source limit middle (.Err error)) :
      IdentityRun rows source limit tokens (.Err error)
  | named {tokens middle rest : Tokens} {ontology : HeaderIri} {version : Option HeaderIri}
      (first : OptionalRun rows source limit tokens (.Ok (some ontology,middle)))
      (second : OptionalRun rows source limit middle (.Ok (version,rest))) :
      IdentityRun rows source limit tokens (.Ok (.Named ontology version,rest))

/-- Actual terminal classification equals the independent standard IRI families. -/
theorem iri_kind_total_correct (terminal : Terminal) : iri_kind terminal = .ok (Kind terminal) := by
  cases terminal <;> rfl

/-- Optional IRI reading is total, preserves exact source tokens and unchanged
    absent suffixes, and obeys the complete value/error resolution contract. -/
theorem read_optional_iri_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) :
    ∃ result, read_optional_iri table bytes tokens limit = .ok result ∧
      OptionalRun table.declarations.val bytes.val limit.val tokens result := by
  cases tokens with
  | Empty => exact ⟨.Ok (none,.Empty),rfl,.empty⟩
  | Cons token tail =>
    rw [read_optional_iri,iri_kind_total_correct,bind_ok]
    cases classified : Kind token.terminal with
    | none => exact ⟨.Ok (none,.Cons token tail),rfl,.absent token tail classified⟩
    | some kind =>
      obtain ⟨result,executed,correct⟩ := Rowl.FunctionalIris.resolve_span_total_correct table kind bytes token.start token.end limit
      simp only
      rw [executed,bind_ok]
      cases result with
      | Ok value => exact ⟨.Ok (some ⟨token,value⟩,tail),rfl,.value classified correct⟩
      | Err error => exact ⟨.Err (.Iri error),rfl,.failure classified correct⟩

/-- Exact optional values, preserved suffixes and every resolution error occur
    precisely when their independent source derivation holds. -/
theorem read_optional_iri_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) (result : core.result.Result (Option HeaderIri × Tokens) HeaderError) :
    read_optional_iri table bytes tokens limit = .ok result ↔
      OptionalRun table.declarations.val bytes.val limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_optional_iri_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | empty => rfl
    | absent token tail absent => simp [read_optional_iri,iri_kind_total_correct,absent]
    | @value token tail kind value accepted valueSource =>
      have executed := (Rowl.FunctionalIris.resolve_span_value_iff table kind bytes token.start token.end limit value).mpr valueSource
      simp [read_optional_iri,iri_kind_total_correct,accepted,executed]
    | @failure token tail kind error accepted errorSource =>
      have executed := (Rowl.FunctionalIris.resolve_span_error_iff table kind bytes token.start token.end limit error).mpr errorSource
      simp [read_optional_iri,iri_kind_total_correct,accepted,executed]

/-- Reading ontology identity and its optional version is total and follows the
    independent zero/one/two-IRI grammar and its exact first-error priority. -/
theorem read_identity_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) :
    ∃ result, read_identity table bytes tokens limit = .ok result ∧
      IdentityRun table.declarations.val bytes.val limit.val tokens result := by
  obtain ⟨first,firstRead,firstCorrect⟩ := read_optional_iri_total_correct table bytes tokens limit
  rw [read_identity,firstRead,bind_ok]
  cases first with
  | Err error => exact ⟨.Err error,rfl,.firstError firstCorrect⟩
  | Ok pair =>
    obtain ⟨ontology,middle⟩ := pair
    simp only [uncurry_apply_pair]
    cases ontology with
    | none => exact ⟨.Ok (.Anonymous,middle),rfl,.anonymous firstCorrect⟩
    | some ontology =>
      obtain ⟨second,secondRead,secondCorrect⟩ := read_optional_iri_total_correct table bytes middle limit
      simp only
      rw [secondRead,bind_ok]
      cases second with
      | Err error => exact ⟨.Err error,rfl,.secondError firstCorrect secondCorrect⟩
      | Ok pair =>
        obtain ⟨version,rest⟩ := pair
        exact ⟨.Ok (.Named ontology version,rest),by simp [uncurry_apply_pair],.named firstCorrect secondCorrect⟩

/-- Every exact identity result and first error is equivalent to its independent
    source grammar, including the unchanged tokens after at most two IRIs. -/
theorem read_identity_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) (result : core.result.Result (SourceOntologyIdentity × Tokens) HeaderError) :
    read_identity table bytes tokens limit = .ok result ↔
      IdentityRun table.declarations.val bytes.val limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_identity_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | firstError first =>
      have executed := (read_optional_iri_result_iff table bytes _ limit _).mpr first
      simp [read_identity,executed]
    | anonymous first =>
      have executed := (read_optional_iri_result_iff table bytes _ limit _).mpr first
      simp [read_identity,executed]
    | secondError first second =>
      have firstRead := (read_optional_iri_result_iff table bytes _ limit _).mpr first
      have secondRead := (read_optional_iri_result_iff table bytes _ limit _).mpr second
      simp [read_identity,firstRead,secondRead]
    | named first second =>
      have firstRead := (read_optional_iri_result_iff table bytes _ limit _).mpr first
      have secondRead := (read_optional_iri_result_iff table bytes _ limit _).mpr second
      simp [read_identity,firstRead,secondRead]

/-- Every accepted header IRI is valid in the complete absolute-IRI grammar. -/
theorem header_iri_grammar (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (limit : Usize) (iri : HeaderIri) (value : IriValue table.declarations.val bytes.val limit.val iri) :
    Rowl.Prefixes.IriAccepted iri.value.val := by
  obtain ⟨kind,_,source⟩ := value
  have executed := (Rowl.FunctionalIris.resolve_span_value_iff table kind bytes iri.token.start iri.token.end limit iri.value).mpr source
  exact Rowl.FunctionalIris.resolved_iri_grammar table kind bytes iri.token.start iri.token.end limit iri.value executed

/-- The source value conditions of the three legal ontology identity forms. -/
def IdentityValues (rows : List prefixes.Declaration) (source : List U8) (limit : Nat) : SourceOntologyIdentity → Prop
  | .Anonymous => True
  | .Named ontology none => IriValue rows source limit ontology
  | .Named ontology (some version) => IriValue rows source limit ontology ∧ IriValue rows source limit version

theorem optional_present_source {rows : List prefixes.Declaration} {source : List U8} {limit : Nat}
    {tokens rest : Tokens} {iri : HeaderIri} (accepted : OptionalRun rows source limit tokens (.Ok (some iri,rest))) :
    tokens = .Cons iri.token rest ∧ IriValue rows source limit iri := by
  cases accepted with
  | value iriKind valueSource => exact ⟨rfl,_,iriKind,valueSource⟩

theorem optional_absent_unchanged {rows : List prefixes.Declaration} {source : List U8} {limit : Nat}
    {tokens rest : Tokens} (accepted : OptionalRun rows source limit tokens (.Ok (none,rest))) : rest = tokens := by
  cases accepted <;> rfl

theorem identity_source_values {rows : List prefixes.Declaration} {source : List U8} {limit : Nat}
    {tokens rest : Tokens} {identity : SourceOntologyIdentity}
    (accepted : IdentityRun rows source limit tokens (.Ok (identity,rest))) : IdentityValues rows source limit identity := by
  cases accepted with
  | anonymous => trivial
  | @named _ _ ontology version first second =>
    have ontologyValue := (optional_present_source first).2
    cases version with
    | none => exact ontologyValue
    | some version => exact ⟨ontologyValue,(optional_present_source second).2⟩

end Rowl.FunctionalHeaderIdentity
