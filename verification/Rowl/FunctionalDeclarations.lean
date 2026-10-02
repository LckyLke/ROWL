import Rowl.FunctionalAnnotations

namespace Rowl.FunctionalDeclarations
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional_declarations
open RowlRust.functional_annotations (AnnotationLimits SourceAnnotations)
open RowlRust.functional_header (HeaderIri)
open RowlRust.functional_lexer RowlRust.functional
open Rowl.FunctionalHeaderIdentity (Kind IriValue iri_kind_total_correct)
open Rowl.FunctionalLexer (TokenCount)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The six standard entity keywords and their structural entity kinds. -/
def EntityKindOf : Terminal → Option SourceEntityKind
  | .Keyword .Class => some .Class
  | .Keyword .Datatype => some .Datatype
  | .Keyword .ObjectProperty => some .ObjectProperty
  | .Keyword .DataProperty => some .DataProperty
  | .Keyword .AnnotationProperty => some .AnnotationProperty
  | .Keyword .NamedIndividual => some .NamedIndividual
  | _ => none
/-- Independent first-terminal class required at each declaration position. -/
def Expected : DeclarationExpected → Terminal → Prop
  | .Declaration, terminal => terminal = .Keyword .Declaration
  | .Open, terminal => terminal = .Open
  | .Entity, terminal => ∃ kind, EntityKindOf terminal = some kind
  | .Iri, terminal => ∃ kind, Kind terminal = some kind
  | .Close, terminal => terminal = .Close
/-- One syntax step: the first token must belong to the expected class. A
    missing token reports the original source length, a wrong one its start. -/
inductive TakeRun (eof : Usize) (expected : DeclarationExpected) :
    Tokens → core.result.Result (Token × Tokens) DeclarationError → Prop
  | empty : TakeRun eof expected .Empty (.Err (.Expected expected eof))
  | wrong (token : Token) (rest : Tokens) (different : ¬ Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Err (.Expected expected token.start))
  | taken (token : Token) (rest : Tokens) (accepted : Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Ok (token,rest))

/-- Actual entity-keyword classification equals the independent six kinds. -/
theorem entity_kind_total_correct (terminal : Terminal) : entity_kind terminal = .ok (EntityKindOf terminal) := by
  cases terminal <;> first | rfl | (rename_i keyword; cases keyword <;> rfl)
/-- Actual position checks decide exactly the independent terminal classes. -/
theorem expected_terminal_total_correct (expected : DeclarationExpected) (terminal : Terminal) :
    expected_terminal expected terminal = .ok (decide (Expected expected terminal)) := by
  cases expected <;> cases terminal <;> (try (rename_i keyword; cases keyword)) <;>
    simp [expected_terminal,Expected,entity_kind_total_correct,iri_kind_total_correct,EntityKindOf,Kind,
      core.option.Option.is_some]

/-- One-token syntax checking is total and follows the independent step. -/
theorem take_expected_total_correct (tokens : Tokens) (expected : DeclarationExpected) (eof : Usize) :
    ∃ result, take_expected tokens expected eof = .ok result ∧ TakeRun eof expected tokens result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected expected eof),rfl,.empty⟩
  | Cons token rest =>
    by_cases accepted : Expected expected token.terminal
    · exact ⟨.Ok (token,rest),by simp [take_expected,expected_terminal_total_correct,accepted],.taken _ _ accepted⟩
    · exact ⟨.Err (.Expected expected token.start),by simp [take_expected,expected_terminal_total_correct,accepted],
        .wrong _ _ accepted⟩
private theorem take_run_unique {eof : Usize} {expected : DeclarationExpected} {tokens : Tokens}
    {one two : core.result.Result (Token × Tokens) DeclarationError}
    (first : TakeRun eof expected tokens one) (second : TakeRun eof expected tokens two) : one = two := by
  cases first <;> cases second <;> first | rfl | contradiction
/-- Every exact one-token result or syntax error is equivalent to the independent step. -/
theorem take_expected_result_iff (tokens : Tokens) (expected : DeclarationExpected) (eof : Usize)
    (result : core.result.Result (Token × Tokens) DeclarationError) :
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
theorem take_progress {eof : Usize} {expected : DeclarationExpected} {tokens rest : Tokens} {token : Token}
    (taken : TakeRun eof expected tokens (.Ok (token,rest))) : TokenCount tokens = 1+TokenCount rest := by
  cases taken
  rfl

/-- Independent entity grammar `Kind ( IRI )` in source order: the entity
    keyword, `(`, the IRI token and its resolution through the checked prefix
    rows, then `)`. -/
inductive EntityRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (SourceEntity × Tokens) DeclarationError → Prop
  | keywordError {tokens : Tokens} {error : DeclarationError} (failure : TakeRun eof .Entity tokens (.Err error)) :
      EntityRun rows source eof limit tokens (.Err error)
  | openError {keyword : Token} {tail : Tokens} {kind : SourceEntityKind} {error : DeclarationError}
      (entityKind : EntityKindOf keyword.terminal = some kind) (failure : TakeRun eof .Open tail (.Err error)) :
      EntityRun rows source eof limit (.Cons keyword tail) (.Err error)
  | iriTokenError {keyword opening : Token} {tail rest : Tokens} {kind : SourceEntityKind} {error : DeclarationError}
      (entityKind : EntityKindOf keyword.terminal = some kind) (opened : TakeRun eof .Open tail (.Ok (opening,rest)))
      (failure : TakeRun eof .Iri rest (.Err error)) :
      EntityRun rows source eof limit (.Cons keyword tail) (.Err error)
  | iriError {keyword opening token : Token} {tail rest after : Tokens} {kind : SourceEntityKind}
      {family : functional_iris.SourceIriKind} {error : functional_iris.SourceIriError}
      (entityKind : EntityKindOf keyword.terminal = some kind) (opened : TakeRun eof .Open tail (.Ok (opening,rest)))
      (named : TakeRun eof .Iri rest (.Ok (token,after))) (iriKind : Kind token.terminal = some family)
      (failure : Rowl.FunctionalIris.ErrorCorrect rows family source token.start.val token.end.val limit error) :
      EntityRun rows source eof limit (.Cons keyword tail) (.Err (.Iri error))
  | closeError {keyword opening token : Token} {tail rest after : Tokens} {kind : SourceEntityKind}
      {family : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8} {error : DeclarationError}
      (entityKind : EntityKindOf keyword.terminal = some kind) (opened : TakeRun eof .Open tail (.Ok (opening,rest)))
      (named : TakeRun eof .Iri rest (.Ok (token,after))) (iriKind : Kind token.terminal = some family)
      (valueSource : Rowl.FunctionalIris.Success rows family source token.start.val token.end.val limit value)
      (failure : TakeRun eof .Close after (.Err error)) :
      EntityRun rows source eof limit (.Cons keyword tail) (.Err error)
  | ready {keyword opening token close : Token} {tail rest after remaining : Tokens} {kind : SourceEntityKind}
      {family : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8}
      (entityKind : EntityKindOf keyword.terminal = some kind) (opened : TakeRun eof .Open tail (.Ok (opening,rest)))
      (named : TakeRun eof .Iri rest (.Ok (token,after))) (iriKind : Kind token.terminal = some family)
      (valueSource : Rowl.FunctionalIris.Success rows family source token.start.val token.end.val limit value)
      (closing : TakeRun eof .Close after (.Ok (close,remaining))) :
      EntityRun rows source eof limit (.Cons keyword tail) (.Ok (⟨kind,keyword,⟨token,value⟩⟩,remaining))

/-- Entity reading is total; its fallbacks after checked tokens are unreachable. -/
theorem read_entity_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) :
    ∃ result, read_entity table bytes tokens limit = .ok result ∧
      EntityRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  obtain ⟨first,firstRead,firstCorrect⟩ := take_expected_total_correct tokens .Entity bytes.len
  rw [read_entity]
  simp only [firstRead,bind_ok]
  cases first with
  | Err error => exact ⟨.Err error,rfl,.keywordError firstCorrect⟩
  | Ok pair =>
    obtain ⟨keyword,tail⟩ := pair
    cases firstCorrect with
    | taken _ _ accepted =>
      obtain ⟨kind,classified⟩ := accepted
      simp only [uncurry_apply_pair,entity_kind_total_correct,classified,bind_ok]
      obtain ⟨opened,openRead,openCorrect⟩ := take_expected_total_correct tail .Open bytes.len
      simp only [openRead,bind_ok]
      cases opened with
      | Err error => exact ⟨.Err error,rfl,.openError classified openCorrect⟩
      | Ok pair =>
        obtain ⟨opening,rest⟩ := pair
        obtain ⟨named,nameRead,nameCorrect⟩ := take_expected_total_correct rest .Iri bytes.len
        simp only [uncurry_apply_pair,nameRead,bind_ok]
        cases named with
        | Err error => exact ⟨.Err error,rfl,.iriTokenError classified openCorrect nameCorrect⟩
        | Ok pair =>
          obtain ⟨token,after⟩ := pair
          have iriAccepted : ∃ family, Kind token.terminal = some family := by
            cases nameCorrect with
            | taken _ _ accepted => exact accepted
          obtain ⟨family,iriKind⟩ := iriAccepted
          simp only [uncurry_apply_pair,iri_kind_total_correct,iriKind,bind_ok]
          obtain ⟨resolved,resolveRead,resolveCorrect⟩ :=
            Rowl.FunctionalIris.resolve_span_total_correct table family bytes token.start token.end limit
          simp only [resolveRead,bind_ok]
          cases resolved with
          | Err error =>
            exact ⟨.Err (.Iri error),rfl,.iriError classified openCorrect nameCorrect iriKind resolveCorrect⟩
          | Ok value =>
            obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct after .Close bytes.len
            simp only [closeRead,bind_ok]
            cases closed with
            | Err error =>
              exact ⟨.Err error,rfl,.closeError classified openCorrect nameCorrect iriKind resolveCorrect closeCorrect⟩
            | Ok pair =>
              obtain ⟨close,remaining⟩ := pair
              exact ⟨.Ok (⟨kind,keyword,⟨token,value⟩⟩,remaining),rfl,
                .ready classified openCorrect nameCorrect iriKind resolveCorrect closeCorrect⟩

/-- Every exact entity and first error is equivalent to its independent derivation. -/
theorem read_entity_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) (result : core.result.Result (SourceEntity × Tokens) DeclarationError) :
    read_entity table bytes tokens limit = .ok result ↔
      EntityRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_entity_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | keywordError failure =>
      have firstRead := (take_expected_result_iff tokens .Entity bytes.len _).mpr failure
      simp [read_entity,firstRead]
    | @openError keyword tail kind error entityKind failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Entity bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨kind,entityKind⟩)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr failure
      simp [read_entity,firstRead,entity_kind_total_correct,entityKind,openRead]
    | @iriTokenError keyword opening tail rest kind error entityKind opened failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Entity bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨kind,entityKind⟩)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
      have nameRead := (take_expected_result_iff rest .Iri bytes.len _).mpr failure
      simp [read_entity,firstRead,entity_kind_total_correct,entityKind,openRead,nameRead]
    | @iriError keyword opening token tail rest after kind family error entityKind opened named iriKind failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Entity bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨kind,entityKind⟩)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
      have nameRead := (take_expected_result_iff rest .Iri bytes.len _).mpr named
      have resolveRead := (Rowl.FunctionalIris.resolve_span_error_iff table family bytes token.start token.end limit error).mpr failure
      simp [read_entity,firstRead,entity_kind_total_correct,entityKind,openRead,nameRead,iri_kind_total_correct,iriKind,
        resolveRead]
    | @closeError keyword opening token tail rest after kind family value error entityKind opened named iriKind
        valueSource failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Entity bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨kind,entityKind⟩)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
      have nameRead := (take_expected_result_iff rest .Iri bytes.len _).mpr named
      have resolveRead := (Rowl.FunctionalIris.resolve_span_value_iff table family bytes token.start token.end limit value).mpr valueSource
      have closeRead := (take_expected_result_iff after .Close bytes.len _).mpr failure
      simp [read_entity,firstRead,entity_kind_total_correct,entityKind,openRead,nameRead,iri_kind_total_correct,iriKind,
        resolveRead,closeRead]
    | @ready keyword opening token close tail rest after remaining kind family value entityKind opened named iriKind
        valueSource closing =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Entity bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨kind,entityKind⟩)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
      have nameRead := (take_expected_result_iff rest .Iri bytes.len _).mpr named
      have resolveRead := (Rowl.FunctionalIris.resolve_span_value_iff table family bytes token.start token.end limit value).mpr valueSource
      have closeRead := (take_expected_result_iff after .Close bytes.len _).mpr closing
      simp [read_entity,firstRead,entity_kind_total_correct,entityKind,openRead,nameRead,iri_kind_total_correct,iriKind,
        resolveRead,closeRead]

/-- An accepted entity is exactly `Kind ( IRI )`: its kind is the keyword's kind,
    its IRI is the exact source-linked value, and it consumes four tokens. -/
theorem entity_source_value {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens remaining : Tokens} {entity : SourceEntity}
    (accepted : EntityRun rows source eof limit tokens (.Ok (entity,remaining))) :
    EntityKindOf entity.keyword.terminal = some entity.kind ∧ IriValue rows source limit entity.iri ∧
      TokenCount tokens = 4+TokenCount remaining := by
  cases accepted with
  | ready entityKind opened named iriKind valueSource closing =>
    have one := take_progress opened
    have two := take_progress named
    have three := take_progress closing
    refine ⟨entityKind,⟨_,iriKind,valueSource⟩,?_⟩
    simp only [TokenCount] at *
    omega

/-- Independent `Declaration( {Annotation} Entity )` grammar in source order:
    the keyword, `(`, the maximal axiom-annotation sequence (the independent
    annotation grammar with the caller's limits), the entity, then `)`. -/
inductive DeclarationRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize)
    (count iriLimit lexLimit depth : Nat) :
    Tokens → core.result.Result (SourceDeclaration × Tokens) DeclarationError → Prop
  | keywordError {tokens : Tokens} {error : DeclarationError}
      (failure : TakeRun eof .Declaration tokens (.Err error)) :
      DeclarationRun rows source eof count iriLimit lexLimit depth tokens (.Err error)
  | openError {keyword : Token} {tail : Tokens} {error : DeclarationError}
      (declarationKind : keyword.terminal = .Keyword .Declaration) (failure : TakeRun eof .Open tail (.Err error)) :
      DeclarationRun rows source eof count iriLimit lexLimit depth (.Cons keyword tail) (.Err error)
  | annotationError {keyword opening : Token} {tail inner : Tokens}
      {error : functional_annotations.AnnotationError}
      (declarationKind : keyword.terminal = .Keyword .Declaration)
      (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (failure : Rowl.FunctionalAnnotations.ScanRun rows source eof count iriLimit lexLimit depth inner [] (.Err error)) :
      DeclarationRun rows source eof count iriLimit lexLimit depth (.Cons keyword tail) (.Err (.Annotation error))
  | entityError {keyword opening : Token} {tail inner : Tokens} {annotations : SourceAnnotations}
      {error : DeclarationError}
      (declarationKind : keyword.terminal = .Keyword .Declaration)
      (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof count iriLimit lexLimit depth inner []
        (.Ok annotations))
      (failure : EntityRun rows source eof iriLimit annotations.remaining (.Err error)) :
      DeclarationRun rows source eof count iriLimit lexLimit depth (.Cons keyword tail) (.Err error)
  | closeError {keyword opening : Token} {tail inner rest : Tokens} {annotations : SourceAnnotations}
      {entity : SourceEntity} {error : DeclarationError}
      (declarationKind : keyword.terminal = .Keyword .Declaration)
      (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof count iriLimit lexLimit depth inner []
        (.Ok annotations))
      (named : EntityRun rows source eof iriLimit annotations.remaining (.Ok (entity,rest)))
      (failure : TakeRun eof .Close rest (.Err error)) :
      DeclarationRun rows source eof count iriLimit lexLimit depth (.Cons keyword tail) (.Err error)
  | ready {keyword opening close : Token} {tail inner rest remaining : Tokens} {annotations : SourceAnnotations}
      {entity : SourceEntity}
      (declarationKind : keyword.terminal = .Keyword .Declaration)
      (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof count iriLimit lexLimit depth inner []
        (.Ok annotations))
      (named : EntityRun rows source eof iriLimit annotations.remaining (.Ok (entity,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      DeclarationRun rows source eof count iriLimit lexLimit depth (.Cons keyword tail)
        (.Ok (⟨keyword,annotations.annotations,entity⟩,remaining))

/-- The actual declaration reader terminates on every token stream and follows
    the independent grammar, including all axiom annotations. -/
theorem read_declaration_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limits : AnnotationLimits) :
    ∃ result, read_declaration table bytes tokens limits = .ok result ∧
      DeclarationRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val
        limits.lexical.val limits.depth.val tokens result := by
  obtain ⟨first,firstRead,firstCorrect⟩ := take_expected_total_correct tokens .Declaration bytes.len
  rw [read_declaration]
  simp only [firstRead,bind_ok]
  cases first with
  | Err error => exact ⟨.Err error,rfl,.keywordError firstCorrect⟩
  | Ok pair =>
    obtain ⟨keyword,tail⟩ := pair
    cases firstCorrect with
    | taken _ _ accepted =>
      obtain ⟨opened,openRead,openCorrect⟩ := take_expected_total_correct tail .Open bytes.len
      simp only [uncurry_apply_pair,openRead,bind_ok]
      cases opened with
      | Err error => exact ⟨.Err error,rfl,.openError accepted openCorrect⟩
      | Ok pair =>
        obtain ⟨opening,inner⟩ := pair
        obtain ⟨annotated,annotatedRead,annotatedCorrect⟩ :=
          Rowl.FunctionalAnnotations.read_annotations_total_correct table bytes inner limits
        simp only [uncurry_apply_pair,annotatedRead,bind_ok]
        cases annotated with
        | Err error => exact ⟨.Err (.Annotation error),rfl,.annotationError accepted openCorrect annotatedCorrect⟩
        | Ok annotations =>
          obtain ⟨named,nameRead,nameCorrect⟩ := read_entity_total_correct table bytes annotations.remaining limits.iri
          simp only [nameRead,bind_ok]
          cases named with
          | Err error => exact ⟨.Err error,rfl,.entityError accepted openCorrect annotatedCorrect nameCorrect⟩
          | Ok pair =>
            obtain ⟨entity,rest⟩ := pair
            obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
            simp only [uncurry_apply_pair,closeRead,bind_ok]
            cases closed with
            | Err error =>
              exact ⟨.Err error,rfl,.closeError accepted openCorrect annotatedCorrect nameCorrect closeCorrect⟩
            | Ok pair =>
              obtain ⟨close,remaining⟩ := pair
              exact ⟨.Ok (⟨keyword,annotations.annotations,entity⟩,remaining),rfl,
                .ready accepted openCorrect annotatedCorrect nameCorrect closeCorrect⟩

/-- Every exact declaration and first error is equivalent to its derivation. -/
theorem read_declaration_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limits : AnnotationLimits)
    (result : core.result.Result (SourceDeclaration × Tokens) DeclarationError) :
    read_declaration table bytes tokens limits = .ok result ↔
      DeclarationRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val
        limits.lexical.val limits.depth.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_declaration_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | keywordError failure =>
      have firstRead := (take_expected_result_iff tokens .Declaration bytes.len _).mpr failure
      simp [read_declaration,firstRead]
    | @openError keyword tail error declarationKind failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Declaration bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail declarationKind)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr failure
      simp [read_declaration,firstRead,openRead]
    | @annotationError keyword opening tail inner error declarationKind opened failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Declaration bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail declarationKind)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
      have annotatedRead := (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner limits _).mpr failure
      simp [read_declaration,firstRead,openRead,annotatedRead]
    | @entityError keyword opening tail inner annotations error declarationKind opened annotated failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Declaration bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail declarationKind)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
      have annotatedRead := (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner limits _).mpr annotated
      have nameRead := (read_entity_result_iff table bytes annotations.remaining limits.iri _).mpr failure
      simp [read_declaration,firstRead,openRead,annotatedRead,nameRead]
    | @closeError keyword opening tail inner rest annotations entity error declarationKind opened annotated named failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Declaration bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail declarationKind)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
      have annotatedRead := (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner limits _).mpr annotated
      have nameRead := (read_entity_result_iff table bytes annotations.remaining limits.iri _).mpr named
      have closeRead := (take_expected_result_iff rest .Close bytes.len _).mpr failure
      simp [read_declaration,firstRead,openRead,annotatedRead,nameRead,closeRead]
    | @ready keyword opening close tail inner rest remaining annotations entity declarationKind opened annotated named
        closing =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Declaration bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail declarationKind)
      have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
      have annotatedRead := (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner limits _).mpr annotated
      have nameRead := (read_entity_result_iff table bytes annotations.remaining limits.iri _).mpr named
      have closeRead := (take_expected_result_iff rest .Close bytes.len _).mpr closing
      simp [read_declaration,firstRead,openRead,annotatedRead,nameRead,closeRead]

/-- A successful declaration keeps its original `Declaration` keyword, its axiom
    annotations form exactly the independent maximal section within the limits,
    and its entity is the exact source-linked `Kind ( IRI )`. -/
theorem declaration_source_values {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}
    {count iriLimit lexLimit depth : Nat} {tokens remaining : Tokens} {declaration : SourceDeclaration}
    (accepted : DeclarationRun rows source eof count iriLimit lexLimit depth tokens (.Ok (declaration,remaining))) :
    declaration.keyword.terminal = .Keyword .Declaration ∧
    declaration.annotations.val.length ≤ count ∧
    EntityKindOf declaration.entity.keyword.terminal = some declaration.entity.kind ∧
    IriValue rows source iriLimit declaration.entity.iri ∧
    ∃ inner middle, Rowl.FunctionalAnnotations.Section rows source eof count iriLimit lexLimit depth inner
      declaration.annotations.val middle := by
  generalize outputEq : core.result.Result.Ok (declaration,remaining) = output at accepted
  cases accepted with
  | keywordError | openError | annotationError | entityError | closeError => cases outputEq
  | @ready keyword opening close tail inner rest remaining' annotations entity declarationKind opened annotated named
      closing =>
    injection outputEq with same
    injection same with declarationSame remainingSame
    subst declarationSame
    obtain ⟨bound,derivation⟩ := Rowl.FunctionalAnnotations.scan_section_accepted annotated
    have values := entity_source_value named
    exact ⟨declarationKind,bound,values.1,values.2.1,inner,annotations.remaining,derivation⟩

/-- A successful declaration consumes at least seven tokens, plus five for every
    top-level axiom annotation, so a later axiom loop always makes progress. -/
theorem declaration_token_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}
    {count iriLimit lexLimit depth : Nat} {tokens remaining : Tokens} {declaration : SourceDeclaration}
    (accepted : DeclarationRun rows source eof count iriLimit lexLimit depth tokens (.Ok (declaration,remaining))) :
    TokenCount remaining+7+5*declaration.annotations.val.length ≤ TokenCount tokens := by
  generalize outputEq : core.result.Result.Ok (declaration,remaining) = output at accepted
  cases accepted with
  | keywordError | openError | annotationError | entityError | closeError => cases outputEq
  | @ready keyword opening close tail inner rest remaining' annotations entity declarationKind opened annotated named
      closing =>
    injection outputEq with same
    injection same with declarationSame remainingSame
    subst declarationSame remainingSame
    obtain ⟨_,derivation⟩ := Rowl.FunctionalAnnotations.scan_section_accepted annotated
    have one := take_progress opened
    have two := Rowl.FunctionalAnnotations.section_token_count derivation
    have three := (entity_source_value named).2.2
    have four := take_progress closing
    simp only [TokenCount] at *
    omega
end Rowl.FunctionalDeclarations
