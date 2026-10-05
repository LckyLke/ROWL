import Rowl.FunctionalHeaderIdentity
import Rowl.FunctionalLiterals

/-!
Functional Syntax data ranges, proved total and exact against an independent
recursive grammar: datatypes, intersections, unions, complements, enumerations
of literals and datatype restrictions with their facets, with literals read by
the independent literal grammar. Every result and first error has its
independent derivation, and every derivation is the actual result.
-/
namespace Rowl.FunctionalRanges
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional_ranges
open RowlRust.functional_header (HeaderIri)
open RowlRust.functional_literals (SourceLiteral SourceLiteralError)
open RowlRust.functional_lexer RowlRust.functional
open Rowl.FunctionalHeaderIdentity (Kind iri_kind_total_correct)
open Rowl.FunctionalLexer (TokenCount)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The data range keywords and their connectives. -/
def FormOf : Terminal → Option RangeForm
  | .Keyword .DataIntersectionOf => some (.Junction true)
  | .Keyword .DataUnionOf => some (.Junction false)
  | .Keyword .DataComplementOf => some .Complement
  | .Keyword .DataOneOf => some .OneOf
  | .Keyword .DatatypeRestriction => some .Restriction
  | _ => none
/-- Independent first-terminal class required at each position. -/
def Expected : RangeExpected → Terminal → Prop
  | .Range, terminal => (FormOf terminal).isSome ∨ ∃ kind, Kind terminal = some kind
  | .Open, terminal => terminal = .Open
  | .Iri, terminal => ∃ kind, Kind terminal = some kind
  | .Literal, terminal => terminal = .QuotedString
  | .Close, terminal => terminal = .Close
/-- Where the next token starts, or the source length at the end. -/
def Position (eof : Usize) : Tokens → Usize
  | .Empty => eof
  | .Cons token _ => token.start

theorem range_form_total_correct (terminal : Terminal) : range_form terminal = .ok (FormOf terminal) := by
  cases terminal <;> first | rfl | (rename_i keyword; cases keyword <;> rfl)
theorem closes_total_correct (terminal : Terminal) :
    functional_ranges.closes terminal = .ok (decide (terminal = .Close)) := by
  cases terminal <;> simp [functional_ranges.closes]
theorem offset_of_total_correct (tokens : Tokens) (eof : Usize) :
    functional_ranges.offset_of tokens eof = .ok (Position eof tokens) := by
  cases tokens <;> rfl
/-- Actual position checks decide exactly the independent terminal classes. -/
theorem expected_terminal_total_correct (expected : RangeExpected) (terminal : Terminal) :
    functional_ranges.expected_terminal expected terminal = .ok (decide (Expected expected terminal)) := by
  cases expected <;> cases terminal <;> (try (rename_i keyword; cases keyword)) <;>
    simp [functional_ranges.expected_terminal,Expected,range_form_total_correct,closes_total_correct,
      iri_kind_total_correct,FormOf,Kind,core.option.Option.is_some]

/-- One syntax step: the first token must belong to the expected class. -/
inductive TakeRun (eof : Usize) (expected : RangeExpected) :
    Tokens → core.result.Result (Token × Tokens) RangeError → Prop
  | empty : TakeRun eof expected .Empty (.Err (.Expected expected eof))
  | wrong (token : Token) (rest : Tokens) (different : ¬ Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Err (.Expected expected token.start))
  | taken (token : Token) (rest : Tokens) (accepted : Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Ok (token,rest))

theorem take_expected_total_correct (tokens : Tokens) (expected : RangeExpected) (eof : Usize) :
    ∃ result, functional_ranges.take_expected tokens expected eof = .ok result ∧ TakeRun eof expected tokens result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected expected eof),rfl,.empty⟩
  | Cons token rest =>
    by_cases accepted : Expected expected token.terminal
    · exact ⟨.Ok (token,rest),by simp [functional_ranges.take_expected,expected_terminal_total_correct,accepted],
        .taken _ _ accepted⟩
    · exact ⟨.Err (.Expected expected token.start),
        by simp [functional_ranges.take_expected,expected_terminal_total_correct,accepted],.wrong _ _ accepted⟩
private theorem take_run_unique {eof : Usize} {expected : RangeExpected} {tokens : Tokens}
    {one two : core.result.Result (Token × Tokens) RangeError}
    (first : TakeRun eof expected tokens one) (second : TakeRun eof expected tokens two) : one = two := by
  cases first <;> cases second <;> first | rfl | contradiction
theorem take_expected_result_iff (tokens : Tokens) (expected : RangeExpected) (eof : Usize)
    (result : core.result.Result (Token × Tokens) RangeError) :
    functional_ranges.take_expected tokens expected eof = .ok result ↔ TakeRun eof expected tokens result := by
  obtain ⟨actual,executed,correct⟩ := take_expected_total_correct tokens expected eof
  constructor
  · intro output
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    have same := take_run_unique correct source
    simpa [same] using executed
/-- An accepted syntax step consumes exactly its own token. -/
theorem take_progress {eof : Usize} {expected : RangeExpected} {tokens rest : Tokens} {token : Token}
    (taken : TakeRun eof expected tokens (.Ok (token,rest))) : TokenCount tokens = 1+TokenCount rest := by
  cases taken
  rfl

/-- An IRI token resolves its original span through the checked prefix rows;
    any other token is reported as missing the expected syntax. -/
inductive ResolveRun (rows : List prefixes.Declaration) (source : List U8) (limit : Nat) (expected : RangeExpected) :
    Token → core.result.Result HeaderIri RangeError → Prop
  | notIri (token : Token) (none : Kind token.terminal = none) :
      ResolveRun rows source limit expected token (.Err (.Expected expected token.start))
  | error {token : Token} {family : functional_iris.SourceIriKind} {error : functional_iris.SourceIriError}
      (kind : Kind token.terminal = some family)
      (failure : Rowl.FunctionalIris.ErrorCorrect rows family source token.start.val token.end.val limit error) :
      ResolveRun rows source limit expected token (.Err (.Iri error))
  | value {token : Token} {family : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8}
      (kind : Kind token.terminal = some family)
      (success : Rowl.FunctionalIris.Success rows family source token.start.val token.end.val limit value) :
      ResolveRun rows source limit expected token (.Ok ⟨token,value⟩)

theorem resolve_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (token : Token)
    (expected : RangeExpected) (limit : Usize) :
    ∃ result, functional_ranges.resolve table bytes token expected limit = .ok result ∧
      ResolveRun table.declarations.val bytes.val limit.val expected token result := by
  rw [functional_ranges.resolve]
  simp only [iri_kind_total_correct,bind_ok]
  cases kind : Kind token.terminal with
  | none => exact ⟨.Err (.Expected expected token.start),rfl,.notIri _ kind⟩
  | some family =>
    obtain ⟨resolved,resolveRead,resolveCorrect⟩ :=
      Rowl.FunctionalIris.resolve_span_total_correct table family bytes token.start token.end limit
    simp only [resolveRead,bind_ok]
    cases resolved with
    | Err error => exact ⟨.Err (.Iri error),rfl,.error kind resolveCorrect⟩
    | Ok value => exact ⟨.Ok ⟨token,value⟩,rfl,.value kind resolveCorrect⟩
theorem resolve_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (token : Token)
    (expected : RangeExpected) (limit : Usize) (result : core.result.Result HeaderIri RangeError) :
    functional_ranges.resolve table bytes token expected limit = .ok result ↔
      ResolveRun table.declarations.val bytes.val limit.val expected token result := by
  obtain ⟨actual,executed,correct⟩ := resolve_total_correct table bytes token expected limit
  constructor
  · intro output
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [executed]
    congr 1
    cases correct with
    | notIri none => cases source <;> simp_all
    | @error family error kind failure =>
      cases source with
      | notIri none => simp_all
      | @error family' error' kind' failure' =>
        rw [kind] at kind'
        cases kind'
        have one := (Rowl.FunctionalIris.resolve_span_error_iff table family bytes token.start token.end limit error).mpr
          failure
        have two := (Rowl.FunctionalIris.resolve_span_error_iff table family bytes token.start token.end limit error').mpr
          failure'
        rw [one] at two
        cases Result.ok_injective two
        rfl
      | @value family' value kind' success =>
        rw [kind] at kind'
        cases kind'
        have one := (Rowl.FunctionalIris.resolve_span_error_iff table family bytes token.start token.end limit error).mpr
          failure
        have two := (Rowl.FunctionalIris.resolve_span_value_iff table family bytes token.start token.end limit value).mpr
          success
        rw [one] at two
        cases Result.ok_injective two
    | @value family value kind success =>
      cases source with
      | notIri none => simp_all
      | @error family' error kind' failure =>
        rw [kind] at kind'
        cases kind'
        have one := (Rowl.FunctionalIris.resolve_span_value_iff table family bytes token.start token.end limit value).mpr
          success
        have two := (Rowl.FunctionalIris.resolve_span_error_iff table family bytes token.start token.end limit error).mpr
          failure
        rw [one] at two
        cases Result.ok_injective two
      | @value family' value' kind' success' =>
        rw [kind] at kind'
        cases kind'
        have one := (Rowl.FunctionalIris.resolve_span_value_iff table family bytes token.start token.end limit value).mpr
          success
        have two := (Rowl.FunctionalIris.resolve_span_value_iff table family bytes token.start token.end limit value').mpr
          success'
        rw [one] at two
        cases Result.ok_injective two
        rfl

/-- Independent maximal literal sequence of an enumeration: it stops before `)`
    or at the end; otherwise the count is checked, then one literal is read and
    appended in source order. -/
inductive LiteralsRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    List SourceLiteral → Tokens → core.result.Result (alloc.vec.Vec SourceLiteral × Tokens) RangeError → Prop
  | empty {prior : List SourceLiteral} {records : alloc.vec.Vec SourceLiteral} (contents : records.val = prior) :
      LiteralsRun rows source eof count limit prior .Empty (.Ok (records,.Empty))
  | stop {prior : List SourceLiteral} {token : Token} {tail : Tokens} {records : alloc.vec.Vec SourceLiteral}
      (close : token.terminal = .Close) (contents : records.val = prior) :
      LiteralsRun rows source eof count limit prior (.Cons token tail) (.Ok (records,.Cons token tail))
  | countLimit {prior : List SourceLiteral} {token : Token} {tail : Tokens}
      (notClose : token.terminal ≠ .Close) (full : count ≤ prior.length) :
      LiteralsRun rows source eof count limit prior (.Cons token tail) (.Err (.CountLimit token.start))
  | memberError {prior : List SourceLiteral} {token : Token} {tail : Tokens} {error : SourceLiteralError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (member : Rowl.FunctionalLiterals.Run rows source eof limit limit (.Cons token tail) (.Err error)) :
      LiteralsRun rows source eof count limit prior (.Cons token tail) (.Err (.Literal error))
  | member {prior : List SourceLiteral} {token : Token} {tail rest : Tokens} {item : SourceLiteral}
      {result : core.result.Result (alloc.vec.Vec SourceLiteral × Tokens) RangeError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (memberRun : Rowl.FunctionalLiterals.Run rows source eof limit limit (.Cons token tail) (.Ok (item,rest)))
      (later : LiteralsRun rows source eof count limit (prior++[item]) rest result) :
      LiteralsRun rows source eof count limit prior (.Cons token tail) result

/-- The actual literal scanner terminates, follows the independent grammar, and
    never returns more tokens than it received. -/
theorem read_literals_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (members : alloc.vec.Vec SourceLiteral) (count limit : Usize) :
    ∃ result, read_literals table bytes tokens members count limit = .ok result ∧
      LiteralsRun table.declarations.val bytes.val bytes.len count.val limit.val members.val tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest ≤ TokenCount tokens := by
  rw [read_literals.eq_def]
  cases tokens with
  | Empty =>
    exact ⟨.Ok (members,.Empty),rfl,.empty rfl,by intro value rest same; cases same; simp⟩
  | Cons token tail =>
    simp only [closes_total_correct,bind_ok]
    by_cases close : token.terminal = .Close
    · refine ⟨.Ok (members,.Cons token tail),by simp [close],.stop close rfl,?_⟩
      intro value rest same
      cases same
      simp
    · by_cases full : count.val ≤ members.val.length
      · refine ⟨.Err (.CountLimit token.start),?_,.countLimit close full,by intro value rest impossible; cases impossible⟩
        simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full]
      · have room : members.val.length < count.val := by omega
        obtain ⟨member,memberRead,memberCorrect⟩ :=
          Rowl.FunctionalLiterals.read_literal_total_correct table bytes (.Cons token tail) limit limit
        cases member with
        | Err error =>
          refine ⟨.Err (.Literal error),?_,.memberError close room memberCorrect,
            by intro value rest impossible; cases impossible⟩
          simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,memberRead]
        | Ok pair =>
          obtain ⟨member,rest⟩ := pair
          have memberStep := (Rowl.FunctionalLiterals.literal_token_progress table bytes _ limit limit member rest
            memberRead).2
          obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec members member (by scalar_tac))
          obtain ⟨result,executed,correct,progress⟩ :=
            read_literals_total_correct table bytes rest appended count limit
          refine ⟨result,?_,.member close room memberCorrect (by simpa [contents] using correct),?_⟩
          · simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,memberRead,push,executed]
          · intro value rest' same
            have one := progress value rest' same
            omega
termination_by TokenCount tokens
decreasing_by
  all_goals
    try subst_vars
    try simp only [TokenCount] at *
    try omega

/-- Every independent literal-sequence derivation is the actual result. -/
theorem literals_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (count limit : Usize)
    (members : alloc.vec.Vec SourceLiteral) {prior : List SourceLiteral} (contents : members.val = prior)
    {tokens : Tokens} {result : core.result.Result (alloc.vec.Vec SourceLiteral × Tokens) RangeError}
    (run : LiteralsRun table.declarations.val bytes.val bytes.len count.val limit.val prior tokens result) :
    read_literals table bytes tokens members count limit = .ok result := by
  cases run with
  | empty records =>
    have equal : members = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_literals.eq_def,equal]
  | stop close records =>
    have equal : members = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_literals.eq_def,equal]
    simp [closes_total_correct,close]
  | countLimit notClose full =>
    rw [read_literals.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,full]
  | memberError notClose room member =>
    have memberRead := (Rowl.FunctionalLiterals.read_literal_result_iff table bytes _ limit limit _).mpr member
    rw [read_literals.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,
      show ¬ count.val ≤ prior.length by omega,memberRead]
  | member notClose room memberRun later =>
    have memberRead := (Rowl.FunctionalLiterals.read_literal_result_iff table bytes _ limit limit _).mpr memberRun
    have step := (Rowl.FunctionalLiterals.literal_token_progress table bytes _ limit limit _ _ memberRead).2
    obtain ⟨appended,push,appendedContents⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.push_spec members _ (by rw [contents]; scalar_tac))
    have laterRead := literals_execution table bytes count limit appended
      (by rw [appendedContents,contents]) later
    rw [read_literals.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,
      show ¬ count.val ≤ prior.length by omega,memberRead,push,laterRead]
termination_by TokenCount tokens
decreasing_by
  all_goals
    try subst_vars
    try simp only [TokenCount] at *
    try omega

/-- Independent maximal facet sequence of a datatype restriction: it stops
    before `)` or at the end; otherwise the count is checked, then a facet IRI
    and its literal are read and appended in source order. -/
inductive FacetsRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    List SourceFacet → Tokens → core.result.Result (alloc.vec.Vec SourceFacet × Tokens) RangeError → Prop
  | empty {prior : List SourceFacet} {records : alloc.vec.Vec SourceFacet} (contents : records.val = prior) :
      FacetsRun rows source eof count limit prior .Empty (.Ok (records,.Empty))
  | stop {prior : List SourceFacet} {token : Token} {tail : Tokens} {records : alloc.vec.Vec SourceFacet}
      (close : token.terminal = .Close) (contents : records.val = prior) :
      FacetsRun rows source eof count limit prior (.Cons token tail) (.Ok (records,.Cons token tail))
  | countLimit {prior : List SourceFacet} {token : Token} {tail : Tokens}
      (notClose : token.terminal ≠ .Close) (full : count ≤ prior.length) :
      FacetsRun rows source eof count limit prior (.Cons token tail) (.Err (.CountLimit token.start))
  | facetError {prior : List SourceFacet} {token : Token} {tail : Tokens} {error : RangeError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (resolved : ResolveRun rows source limit .Iri token (.Err error)) :
      FacetsRun rows source eof count limit prior (.Cons token tail) (.Err error)
  | valueError {prior : List SourceFacet} {token : Token} {tail : Tokens} {facet : HeaderIri}
      {error : SourceLiteralError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (resolved : ResolveRun rows source limit .Iri token (.Ok facet))
      (value : Rowl.FunctionalLiterals.Run rows source eof limit limit tail (.Err error)) :
      FacetsRun rows source eof count limit prior (.Cons token tail) (.Err (.Literal error))
  | facet {prior : List SourceFacet} {token : Token} {tail rest : Tokens} {facet : HeaderIri} {item : SourceLiteral}
      {result : core.result.Result (alloc.vec.Vec SourceFacet × Tokens) RangeError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (resolved : ResolveRun rows source limit .Iri token (.Ok facet))
      (valueRun : Rowl.FunctionalLiterals.Run rows source eof limit limit tail (.Ok (item,rest)))
      (later : FacetsRun rows source eof count limit (prior++[⟨facet,item⟩]) rest result) :
      FacetsRun rows source eof count limit prior (.Cons token tail) result

/-- The actual facet scanner terminates, follows the independent grammar, and
    never returns more tokens than it received. -/
theorem read_facets_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (facets : alloc.vec.Vec SourceFacet) (count limit : Usize) :
    ∃ result, read_facets table bytes tokens facets count limit = .ok result ∧
      FacetsRun table.declarations.val bytes.val bytes.len count.val limit.val facets.val tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest ≤ TokenCount tokens := by
  rw [read_facets.eq_def]
  cases tokens with
  | Empty =>
    exact ⟨.Ok (facets,.Empty),rfl,.empty rfl,by intro value rest same; cases same; simp⟩
  | Cons token tail =>
    simp only [closes_total_correct,bind_ok]
    by_cases close : token.terminal = .Close
    · refine ⟨.Ok (facets,.Cons token tail),by simp [close],.stop close rfl,?_⟩
      intro value rest same
      cases same
      simp
    · by_cases full : count.val ≤ facets.val.length
      · refine ⟨.Err (.CountLimit token.start),?_,.countLimit close full,by intro value rest impossible; cases impossible⟩
        simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full]
      · have room : facets.val.length < count.val := by omega
        obtain ⟨resolved,resolveRead,resolveCorrect⟩ := resolve_total_correct table bytes token .Iri limit
        cases resolved with
        | Err error =>
          refine ⟨.Err error,?_,.facetError close room resolveCorrect,by intro value rest impossible; cases impossible⟩
          simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,resolveRead]
        | Ok facet =>
          obtain ⟨value,valueRead,valueCorrect⟩ :=
            Rowl.FunctionalLiterals.read_literal_total_correct table bytes tail limit limit
          cases value with
          | Err error =>
            refine ⟨.Err (.Literal error),?_,.valueError close room resolveCorrect valueCorrect,
              by intro value rest impossible; cases impossible⟩
            simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,resolveRead,valueRead]
          | Ok pair =>
            obtain ⟨item,rest⟩ := pair
            have valueStep := (Rowl.FunctionalLiterals.literal_token_progress table bytes _ limit limit item rest
              valueRead).2
            obtain ⟨appended,push,contents⟩ :=
              WP.spec_imp_exists (alloc.vec.Vec.push_spec facets ⟨facet,item⟩ (by scalar_tac))
            obtain ⟨result,executed,correct,progress⟩ :=
              read_facets_total_correct table bytes rest appended count limit
            refine ⟨result,?_,.facet close room resolveCorrect valueCorrect (by simpa [contents] using correct),?_⟩
            · simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,resolveRead,valueRead,push,executed]
            · intro value rest' same
              have one := progress value rest' same
              simp only [TokenCount]
              omega
termination_by TokenCount tokens
decreasing_by
  all_goals
    try subst_vars
    try simp only [TokenCount] at *
    try omega

/-- Every independent facet-sequence derivation is the actual result. -/
theorem facets_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (count limit : Usize)
    (facets : alloc.vec.Vec SourceFacet) {prior : List SourceFacet} (contents : facets.val = prior)
    {tokens : Tokens} {result : core.result.Result (alloc.vec.Vec SourceFacet × Tokens) RangeError}
    (run : FacetsRun table.declarations.val bytes.val bytes.len count.val limit.val prior tokens result) :
    read_facets table bytes tokens facets count limit = .ok result := by
  cases run with
  | empty records =>
    have equal : facets = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_facets.eq_def,equal]
  | stop close records =>
    have equal : facets = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_facets.eq_def,equal]
    simp [closes_total_correct,close]
  | countLimit notClose full =>
    rw [read_facets.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,full]
  | facetError notClose room resolved =>
    rw [read_facets.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,
      show ¬ count.val ≤ prior.length by omega,(resolve_result_iff table bytes _ .Iri limit _).mpr resolved]
  | valueError notClose room resolved value =>
    rw [read_facets.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,
      show ¬ count.val ≤ prior.length by omega,(resolve_result_iff table bytes _ .Iri limit _).mpr resolved,
      (Rowl.FunctionalLiterals.read_literal_result_iff table bytes _ limit limit _).mpr value]
  | facet notClose room resolved valueRun later =>
    have valueRead := (Rowl.FunctionalLiterals.read_literal_result_iff table bytes _ limit limit _).mpr valueRun
    have step := (Rowl.FunctionalLiterals.literal_token_progress table bytes _ limit limit _ _ valueRead).2
    obtain ⟨appended,push,appendedContents⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.push_spec facets _ (by rw [contents]; scalar_tac))
    have laterRead := facets_execution table bytes count limit appended
      (by rw [appendedContents,contents]) later
    rw [read_facets.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,
      show ¬ count.val ≤ prior.length by omega,(resolve_result_iff table bytes _ .Iri limit _).mpr resolved,
      valueRead,push,laterRead]
termination_by TokenCount tokens
decreasing_by
  all_goals
    try subst_vars
    try simp only [TokenCount] at *
    try omega

mutual
/-- Independent data range grammar in source order. A datatype is an IRI token
    resolved through the checked prefix rows. At a connective keyword the
    remaining nesting allowance is checked, then `(`, then the body one level
    deeper. -/
inductive RangeRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Nat → Tokens → core.result.Result (SourceDataRange × Tokens) RangeError → Prop
  | empty {depth : Nat} : RangeRun rows source eof count limit depth .Empty (.Err (.Expected .Range eof))
  | datatypeError {depth : Nat} {token : Token} {tail : Tokens} {error : RangeError}
      (other : FormOf token.terminal = none) (resolved : ResolveRun rows source limit .Range token (.Err error)) :
      RangeRun rows source eof count limit depth (.Cons token tail) (.Err error)
  | datatype {depth : Nat} {token : Token} {tail : Tokens} {iri : HeaderIri}
      (other : FormOf token.terminal = none) (resolved : ResolveRun rows source limit .Range token (.Ok iri)) :
      RangeRun rows source eof count limit depth (.Cons token tail) (.Ok (.Datatype iri,tail))
  | depthLimit {token : Token} {tail : Tokens} {form : RangeForm}
      (keyword : FormOf token.terminal = some form) :
      RangeRun rows source eof count limit 0 (.Cons token tail) (.Err (.DepthLimit token.start))
  | openError {depth : Nat} {token : Token} {tail : Tokens} {form : RangeForm} {error : RangeError}
      (keyword : FormOf token.terminal = some form) (failure : TakeRun eof .Open tail (.Err error)) :
      RangeRun rows source eof count limit (depth+1) (.Cons token tail) (.Err error)
  | connective {depth : Nat} {token opening : Token} {tail inner : Tokens} {form : RangeForm}
      {result : core.result.Result (SourceDataRange × Tokens) RangeError}
      (keyword : FormOf token.terminal = some form)
      (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (body : BodyRun rows source eof count limit depth token form inner result) :
      RangeRun rows source eof count limit (depth+1) (.Cons token tail) result
/-- Independent connective bodies after `(`. Intersections and unions read the
    maximal member sequence, then require two members, then `)`. Complements read
    one operand and `)`. Enumerations read the maximal literal sequence, then
    require one literal, then `)`. Datatype restrictions read a datatype IRI, the
    maximal facet sequence, then require one facet, then `)`. -/
inductive BodyRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Nat → Token → RangeForm → Tokens → core.result.Result (SourceDataRange × Tokens) RangeError → Prop
  | membersError {depth : Nat} {keyword : Token} {conjunctive : Bool} {tokens : Tokens} {error : RangeError}
      (members : MembersRun rows source eof count limit depth [] tokens (.Err error)) :
      BodyRun rows source eof count limit depth keyword (.Junction conjunctive) tokens (.Err error)
  | tooFew {depth : Nat} {keyword : Token} {conjunctive : Bool} {tokens rest : Tokens}
      {list : alloc.vec.Vec SourceDataRange}
      (members : MembersRun rows source eof count limit depth [] tokens (.Ok (list,rest)))
      (few : list.val.length < 2) :
      BodyRun rows source eof count limit depth keyword (.Junction conjunctive) tokens
        (.Err (.Expected .Range (Position eof rest)))
  | junctionCloseError {depth : Nat} {keyword : Token} {conjunctive : Bool} {tokens rest : Tokens}
      {list : alloc.vec.Vec SourceDataRange} {error : RangeError}
      (members : MembersRun rows source eof count limit depth [] tokens (.Ok (list,rest)))
      (enough : 2 ≤ list.val.length) (failure : TakeRun eof .Close rest (.Err error)) :
      BodyRun rows source eof count limit depth keyword (.Junction conjunctive) tokens (.Err error)
  | junction {depth : Nat} {keyword close : Token} {conjunctive : Bool} {tokens rest remaining : Tokens}
      {list : alloc.vec.Vec SourceDataRange}
      (members : MembersRun rows source eof count limit depth [] tokens (.Ok (list,rest)))
      (enough : 2 ≤ list.val.length) (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      BodyRun rows source eof count limit depth keyword (.Junction conjunctive) tokens
        (.Ok (if conjunctive then .IntersectionOf keyword list else .UnionOf keyword list,remaining))
  | operandError {depth : Nat} {keyword : Token} {tokens : Tokens} {error : RangeError}
      (operand : RangeRun rows source eof count limit depth tokens (.Err error)) :
      BodyRun rows source eof count limit depth keyword .Complement tokens (.Err error)
  | complementCloseError {depth : Nat} {keyword : Token} {tokens rest : Tokens} {operand : SourceDataRange}
      {error : RangeError}
      (operandRun : RangeRun rows source eof count limit depth tokens (.Ok (operand,rest)))
      (failure : TakeRun eof .Close rest (.Err error)) :
      BodyRun rows source eof count limit depth keyword .Complement tokens (.Err error)
  | complement {depth : Nat} {keyword close : Token} {tokens rest remaining : Tokens} {operand : SourceDataRange}
      (operandRun : RangeRun rows source eof count limit depth tokens (.Ok (operand,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      BodyRun rows source eof count limit depth keyword .Complement tokens
        (.Ok (.ComplementOf keyword operand,remaining))
  | literalsError {depth : Nat} {keyword : Token} {tokens : Tokens} {error : RangeError}
      (list : LiteralsRun rows source eof count limit [] tokens (.Err error)) :
      BodyRun rows source eof count limit depth keyword .OneOf tokens (.Err error)
  | noLiteral {depth : Nat} {keyword : Token} {tokens rest : Tokens} {members : alloc.vec.Vec SourceLiteral}
      (list : LiteralsRun rows source eof count limit [] tokens (.Ok (members,rest)))
      (few : members.val.length < 1) :
      BodyRun rows source eof count limit depth keyword .OneOf tokens (.Err (.Expected .Literal (Position eof rest)))
  | oneOfCloseError {depth : Nat} {keyword : Token} {tokens rest : Tokens} {members : alloc.vec.Vec SourceLiteral}
      {error : RangeError}
      (list : LiteralsRun rows source eof count limit [] tokens (.Ok (members,rest)))
      (enough : 1 ≤ members.val.length) (failure : TakeRun eof .Close rest (.Err error)) :
      BodyRun rows source eof count limit depth keyword .OneOf tokens (.Err error)
  | oneOf {depth : Nat} {keyword close : Token} {tokens rest remaining : Tokens}
      {members : alloc.vec.Vec SourceLiteral}
      (list : LiteralsRun rows source eof count limit [] tokens (.Ok (members,rest)))
      (enough : 1 ≤ members.val.length) (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      BodyRun rows source eof count limit depth keyword .OneOf tokens (.Ok (.OneOf keyword members,remaining))
  | datatypeTokenError {depth : Nat} {keyword : Token} {tokens : Tokens} {error : RangeError}
      (failure : TakeRun eof .Iri tokens (.Err error)) :
      BodyRun rows source eof count limit depth keyword .Restriction tokens (.Err error)
  | restrictionDatatypeError {depth : Nat} {keyword named : Token} {tokens rest : Tokens} {error : RangeError}
      (taken : TakeRun eof .Iri tokens (.Ok (named,rest)))
      (resolved : ResolveRun rows source limit .Iri named (.Err error)) :
      BodyRun rows source eof count limit depth keyword .Restriction tokens (.Err error)
  | facetsError {depth : Nat} {keyword named : Token} {tokens rest : Tokens} {datatype : HeaderIri}
      {error : RangeError}
      (taken : TakeRun eof .Iri tokens (.Ok (named,rest)))
      (resolved : ResolveRun rows source limit .Iri named (.Ok datatype))
      (facets : FacetsRun rows source eof count limit [] rest (.Err error)) :
      BodyRun rows source eof count limit depth keyword .Restriction tokens (.Err error)
  | noFacet {depth : Nat} {keyword named : Token} {tokens rest after : Tokens} {datatype : HeaderIri}
      {list : alloc.vec.Vec SourceFacet}
      (taken : TakeRun eof .Iri tokens (.Ok (named,rest)))
      (resolved : ResolveRun rows source limit .Iri named (.Ok datatype))
      (facets : FacetsRun rows source eof count limit [] rest (.Ok (list,after)))
      (few : list.val.length < 1) :
      BodyRun rows source eof count limit depth keyword .Restriction tokens (.Err (.Expected .Iri (Position eof after)))
  | restrictionCloseError {depth : Nat} {keyword named : Token} {tokens rest after : Tokens} {datatype : HeaderIri}
      {list : alloc.vec.Vec SourceFacet} {error : RangeError}
      (taken : TakeRun eof .Iri tokens (.Ok (named,rest)))
      (resolved : ResolveRun rows source limit .Iri named (.Ok datatype))
      (facets : FacetsRun rows source eof count limit [] rest (.Ok (list,after)))
      (enough : 1 ≤ list.val.length) (failure : TakeRun eof .Close after (.Err error)) :
      BodyRun rows source eof count limit depth keyword .Restriction tokens (.Err error)
  | restriction {depth : Nat} {keyword named close : Token} {tokens rest after remaining : Tokens}
      {datatype : HeaderIri} {list : alloc.vec.Vec SourceFacet}
      (taken : TakeRun eof .Iri tokens (.Ok (named,rest)))
      (resolved : ResolveRun rows source limit .Iri named (.Ok datatype))
      (facets : FacetsRun rows source eof count limit [] rest (.Ok (list,after)))
      (enough : 1 ≤ list.val.length) (closing : TakeRun eof .Close after (.Ok (close,remaining))) :
      BodyRun rows source eof count limit depth keyword .Restriction tokens
        (.Ok (.Restriction keyword datatype list,remaining))
/-- Independent maximal member sequence: it stops before `)` or at the end;
    otherwise the member count is checked, then one data range is read and
    appended in source order. -/
inductive MembersRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Nat → List SourceDataRange → Tokens →
      core.result.Result (alloc.vec.Vec SourceDataRange × Tokens) RangeError → Prop
  | empty {depth : Nat} {prior : List SourceDataRange} {records : alloc.vec.Vec SourceDataRange}
      (contents : records.val = prior) :
      MembersRun rows source eof count limit depth prior .Empty (.Ok (records,.Empty))
  | stop {depth : Nat} {prior : List SourceDataRange} {token : Token} {tail : Tokens}
      {records : alloc.vec.Vec SourceDataRange}
      (close : token.terminal = .Close) (contents : records.val = prior) :
      MembersRun rows source eof count limit depth prior (.Cons token tail) (.Ok (records,.Cons token tail))
  | countLimit {depth : Nat} {prior : List SourceDataRange} {token : Token} {tail : Tokens}
      (notClose : token.terminal ≠ .Close) (full : count ≤ prior.length) :
      MembersRun rows source eof count limit depth prior (.Cons token tail) (.Err (.CountLimit token.start))
  | memberError {depth : Nat} {prior : List SourceDataRange} {token : Token} {tail : Tokens} {error : RangeError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (member : RangeRun rows source eof count limit depth (.Cons token tail) (.Err error)) :
      MembersRun rows source eof count limit depth prior (.Cons token tail) (.Err error)
  | member {depth : Nat} {prior : List SourceDataRange} {token : Token} {tail rest : Tokens} {item : SourceDataRange}
      {result : core.result.Result (alloc.vec.Vec SourceDataRange × Tokens) RangeError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (memberRun : RangeRun rows source eof count limit depth (.Cons token tail) (.Ok (item,rest)))
      (later : MembersRun rows source eof count limit depth (prior++[item]) rest result) :
      MembersRun rows source eof count limit depth prior (.Cons token tail) result
end

mutual
/-- The actual recursive data range reader terminates on every token stream,
    follows the independent grammar, and consumes at least one token on success. -/
theorem read_range_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (depth count limit : Usize) :
    ∃ result, read_range table bytes tokens depth count limit = .ok result ∧
      RangeRun table.declarations.val bytes.val bytes.len count.val limit.val depth.val tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest < TokenCount tokens := by
  cases tokens with
  | Empty =>
    exact ⟨.Err (.Expected .Range bytes.len),by rw [read_range.eq_def],.empty,
      by intro value rest impossible; cases impossible⟩
  | Cons token tail =>
    rw [read_range.eq_def]
    simp only [range_form_total_correct,bind_ok]
    cases keyword : FormOf token.terminal with
    | none =>
      obtain ⟨resolved,resolveRead,resolveCorrect⟩ := resolve_total_correct table bytes token .Range limit
      cases resolved with
      | Err error =>
        exact ⟨.Err error,by simp [resolveRead],.datatypeError keyword resolveCorrect,
          by intro value rest impossible; cases impossible⟩
      | Ok iri =>
        refine ⟨.Ok (.Datatype iri,tail),by simp [resolveRead],.datatype keyword resolveCorrect,?_⟩
        intro value rest same
        cases same
        simp [TokenCount]
    | some form =>
      by_cases zero : depth.val = 0
      · refine ⟨.Err (.DepthLimit token.start),by simp [UScalar.eq_equiv,zero],?_,
          by intro value rest impossible; cases impossible⟩
        rw [zero]
        exact .depthLimit keyword
      · obtain ⟨level,levelValue⟩ : ∃ level, depth.val = level+1 := ⟨depth.val-1,by omega⟩
        obtain ⟨opened,openRead,openCorrect⟩ := take_expected_total_correct tail .Open bytes.len
        cases opened with
        | Err error =>
          refine ⟨.Err error,by simp [UScalar.eq_equiv,zero,openRead],?_,by intro value rest impossible; cases impossible⟩
          rw [levelValue]
          exact .openError keyword openCorrect
        | Ok pair =>
          obtain ⟨opening,inner⟩ := pair
          obtain ⟨smaller,subExecuted,subValue⟩ :=
            WP.spec_imp_exists (Usize.sub_spec (x := depth) (y := 1#usize) (by scalar_tac))
          have smallerValue : smaller.val = level := by
            have : (1#usize).val = 1 := rfl
            omega
          obtain ⟨result,executed,correct,progress⟩ :=
            read_body_total_correct table bytes token form inner smaller count limit
          refine ⟨result,by simp [UScalar.eq_equiv,zero,openRead,subExecuted,executed],?_,?_⟩
          · rw [levelValue]
            rw [smallerValue] at correct
            exact .connective keyword openCorrect correct
          · intro value rest same
            have one := progress value rest same
            have two := take_progress openCorrect
            try simp only [TokenCount] at *
            omega
termination_by (TokenCount tokens,0)
decreasing_by
  all_goals
    have one := take_progress openCorrect
    simp_wf
    try subst_vars
    try rw [Prod.lex_def]
    try simp only [TokenCount] at *
    try simp only [or_true]
    try omega

/-- The actual connective bodies terminate, follow the independent grammar, and
    consume at least their closing token on success. -/
theorem read_body_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (keyword : Token)
    (form : RangeForm) (tokens : Tokens) (depth count limit : Usize) :
    ∃ result, read_body table bytes keyword form tokens depth count limit = .ok result ∧
      BodyRun table.declarations.val bytes.val bytes.len count.val limit.val depth.val keyword form tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest < TokenCount tokens := by
  rw [read_body.eq_def]
  cases form with
  | Junction conjunctive =>
    obtain ⟨members,membersRead,membersCorrect,membersProgress⟩ :=
      read_members_total_correct table bytes tokens (alloc.vec.Vec.new SourceDataRange) depth count limit
    have start : (alloc.vec.Vec.new SourceDataRange).val = [] := rfl
    rw [start] at membersCorrect
    cases members with
    | Err error =>
      exact ⟨.Err error,by simp [membersRead],.membersError membersCorrect,by intro value rest impossible; cases impossible⟩
    | Ok pair =>
      obtain ⟨list,rest⟩ := pair
      by_cases few : list.val.length < 2
      · refine ⟨.Err (.Expected .Range (Position bytes.len rest)),?_,.tooFew membersCorrect few,
          by intro value rest impossible; cases impossible⟩
        simp [membersRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,offset_of_total_correct,
          show list.val.length ≤ 1 by omega]
      · have enough : 2 ≤ list.val.length := by omega
        have many : ¬ list.val.length ≤ 1 := by omega
        obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
        cases closed with
        | Err error =>
          refine ⟨.Err error,?_,.junctionCloseError membersCorrect enough closeCorrect,
            by intro value rest impossible; cases impossible⟩
          simp [membersRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,many,closeRead]
        | Ok pair =>
          obtain ⟨close,remaining⟩ := pair
          refine ⟨.Ok (if conjunctive then .IntersectionOf keyword list else .UnionOf keyword list,remaining),?_,
            .junction membersCorrect enough closeCorrect,?_⟩
          · cases conjunctive <;> simp [membersRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,many,closeRead]
          · intro value rest' same
            have one := membersProgress list rest rfl
            have two := take_progress closeCorrect
            cases same
            try simp only [TokenCount] at *
            omega
  | Complement =>
    obtain ⟨operand,operandRead,operandCorrect,operandProgress⟩ :=
      read_range_total_correct table bytes tokens depth count limit
    cases operand with
    | Err error =>
      exact ⟨.Err error,by simp [operandRead],.operandError operandCorrect,by intro value rest impossible; cases impossible⟩
    | Ok pair =>
      obtain ⟨operand,rest⟩ := pair
      obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
      cases closed with
      | Err error =>
        exact ⟨.Err error,by simp [operandRead,closeRead],.complementCloseError operandCorrect closeCorrect,
          by intro value rest impossible; cases impossible⟩
      | Ok pair =>
        obtain ⟨close,remaining⟩ := pair
        refine ⟨.Ok (.ComplementOf keyword operand,remaining),by simp [operandRead,closeRead],
          .complement operandCorrect closeCorrect,?_⟩
        intro value rest' same
        have one := operandProgress operand rest rfl
        have two := take_progress closeCorrect
        cases same
        omega
  | OneOf =>
    obtain ⟨list,listRead,listCorrect,listProgress⟩ :=
      read_literals_total_correct table bytes tokens (alloc.vec.Vec.new SourceLiteral) count limit
    have start : (alloc.vec.Vec.new SourceLiteral).val = [] := rfl
    rw [start] at listCorrect
    cases list with
    | Err error =>
      exact ⟨.Err error,by simp [listRead],.literalsError listCorrect,by intro value rest impossible; cases impossible⟩
    | Ok pair =>
      obtain ⟨members,rest⟩ := pair
      by_cases few : members.val.length < 1
      · have empty : members.val = [] := List.eq_nil_of_length_eq_zero (by omega)
        refine ⟨.Err (.Expected .Literal (Position bytes.len rest)),?_,.noLiteral listCorrect few,
          by intro value rest impossible; cases impossible⟩
        simp [listRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,empty,offset_of_total_correct]
      · have enough : 1 ≤ members.val.length := by omega
        have nonempty : members.val ≠ [] := by intro empty; simp [empty] at enough
        obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
        cases closed with
        | Err error =>
          refine ⟨.Err error,?_,.oneOfCloseError listCorrect enough closeCorrect,
            by intro value rest impossible; cases impossible⟩
          simp [listRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,nonempty,closeRead]
        | Ok pair =>
          obtain ⟨close,remaining⟩ := pair
          refine ⟨.Ok (.OneOf keyword members,remaining),?_,.oneOf listCorrect enough closeCorrect,?_⟩
          · simp [listRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,nonempty,closeRead]
          · intro value rest' same
            have one := listProgress members rest rfl
            have two := take_progress closeCorrect
            cases same
            omega
  | Restriction =>
    obtain ⟨taken,takenRead,takenCorrect⟩ := take_expected_total_correct tokens .Iri bytes.len
    cases taken with
    | Err error =>
      exact ⟨.Err error,by simp [takenRead],.datatypeTokenError takenCorrect,
        by intro value rest impossible; cases impossible⟩
    | Ok pair =>
      obtain ⟨named,rest⟩ := pair
      have namedStep := take_progress takenCorrect
      obtain ⟨resolved,resolveRead,resolveCorrect⟩ := resolve_total_correct table bytes named .Iri limit
      cases resolved with
      | Err error =>
        exact ⟨.Err error,by simp [takenRead,resolveRead],.restrictionDatatypeError takenCorrect resolveCorrect,
          by intro value rest impossible; cases impossible⟩
      | Ok datatype =>
        obtain ⟨facets,facetsRead,facetsCorrect,facetsProgress⟩ :=
          read_facets_total_correct table bytes rest (alloc.vec.Vec.new SourceFacet) count limit
        have start : (alloc.vec.Vec.new SourceFacet).val = [] := rfl
        rw [start] at facetsCorrect
        cases facets with
        | Err error =>
          exact ⟨.Err error,by simp [takenRead,resolveRead,facetsRead],
            .facetsError takenCorrect resolveCorrect facetsCorrect,by intro value rest impossible; cases impossible⟩
        | Ok pair =>
          obtain ⟨list,after⟩ := pair
          by_cases few : list.val.length < 1
          · have empty : list.val = [] := List.eq_nil_of_length_eq_zero (by omega)
            refine ⟨.Err (.Expected .Iri (Position bytes.len after)),?_,
              .noFacet takenCorrect resolveCorrect facetsCorrect few,by intro value rest impossible; cases impossible⟩
            simp [takenRead,resolveRead,facetsRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,empty,
              offset_of_total_correct]
          · have enough : 1 ≤ list.val.length := by omega
            have nonempty : list.val ≠ [] := by intro empty; simp [empty] at enough
            obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct after .Close bytes.len
            cases closed with
            | Err error =>
              refine ⟨.Err error,?_,.restrictionCloseError takenCorrect resolveCorrect facetsCorrect enough closeCorrect,
                by intro value rest impossible; cases impossible⟩
              simp [takenRead,resolveRead,facetsRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,nonempty,closeRead]
            | Ok pair =>
              obtain ⟨close,remaining⟩ := pair
              refine ⟨.Ok (.Restriction keyword datatype list,remaining),?_,
                .restriction takenCorrect resolveCorrect facetsCorrect enough closeCorrect,?_⟩
              · simp [takenRead,resolveRead,facetsRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,nonempty,closeRead]
              · intro value rest' same
                have one := facetsProgress list after rfl
                have two := take_progress closeCorrect
                cases same
                try simp only [TokenCount] at *
                omega
termination_by (TokenCount tokens,2)
decreasing_by
  all_goals
    simp_wf
    try subst_vars
    try rw [Prod.lex_def]
    try simp only [TokenCount] at *
    try simp only [or_true]
    try omega

/-- The actual member scanner terminates, follows the independent grammar, and
    never returns more tokens than it received. -/
theorem read_members_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (members : alloc.vec.Vec SourceDataRange) (depth count limit : Usize) :
    ∃ result, read_members table bytes tokens members depth count limit = .ok result ∧
      MembersRun table.declarations.val bytes.val bytes.len count.val limit.val depth.val members.val tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest ≤ TokenCount tokens := by
  rw [read_members.eq_def]
  cases tokens with
  | Empty =>
    exact ⟨.Ok (members,.Empty),rfl,.empty rfl,by intro value rest same; cases same; simp⟩
  | Cons token tail =>
    simp only [closes_total_correct,bind_ok]
    by_cases close : token.terminal = .Close
    · refine ⟨.Ok (members,.Cons token tail),by simp [close],.stop close rfl,?_⟩
      intro value rest same
      cases same
      simp
    · by_cases full : count.val ≤ members.val.length
      · refine ⟨.Err (.CountLimit token.start),?_,.countLimit close full,by intro value rest impossible; cases impossible⟩
        simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full]
      · have room : members.val.length < count.val := by omega
        obtain ⟨member,memberRead,memberCorrect,memberProgress⟩ :=
          read_range_total_correct table bytes (.Cons token tail) depth count limit
        cases member with
        | Err error =>
          refine ⟨.Err error,?_,.memberError close room memberCorrect,by intro value rest impossible; cases impossible⟩
          simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,memberRead]
        | Ok pair =>
          obtain ⟨member,rest⟩ := pair
          have memberStep := memberProgress member rest rfl
          obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec members member (by scalar_tac))
          obtain ⟨result,executed,correct,progress⟩ :=
            read_members_total_correct table bytes rest appended depth count limit
          refine ⟨result,?_,.member close room memberCorrect (by simpa [contents] using correct),?_⟩
          · simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,memberRead,push,executed]
          · intro value rest' same
            have one := progress value rest' same
            omega
termination_by (TokenCount tokens,1)
decreasing_by
  all_goals
    simp_wf
    try subst_vars
    try rw [Prod.lex_def]
    try simp only [TokenCount] at *
    try simp only [or_true]
    try omega
end

mutual
/-- Every independent data range derivation is the actual result. -/
theorem range_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (count limit : Usize)
    (depth : Usize) {d : Nat} (same : depth.val = d) {tokens : Tokens}
    {result : core.result.Result (SourceDataRange × Tokens) RangeError}
    (run : RangeRun table.declarations.val bytes.val bytes.len count.val limit.val d tokens result) :
    read_range table bytes tokens depth count limit = .ok result := by
  cases run with
  | empty => rw [read_range.eq_def]
  | datatypeError other resolved =>
    rw [read_range.eq_def]
    simp [range_form_total_correct,other,(resolve_result_iff table bytes _ .Range limit _).mpr resolved]
  | datatype other resolved =>
    rw [read_range.eq_def]
    simp [range_form_total_correct,other,(resolve_result_iff table bytes _ .Range limit _).mpr resolved]
  | depthLimit keyword =>
    rw [read_range.eq_def]
    simp [range_form_total_correct,keyword,UScalar.eq_equiv,same]
  | openError keyword failure =>
    rw [read_range.eq_def]
    simp [range_form_total_correct,keyword,UScalar.eq_equiv,same,
      (take_expected_result_iff _ .Open bytes.len _).mpr failure]
  | connective keyword opened body =>
    have positive : depth.val ≠ 0 := by omega
    obtain ⟨smaller,subExecuted,subValue⟩ :=
      WP.spec_imp_exists (Usize.sub_spec (x := depth) (y := 1#usize) (by scalar_tac))
    have one : (1#usize).val = 1 := rfl
    have bodyRead := body_execution table bytes count limit _ _ smaller (by omega) body
    rw [read_range.eq_def]
    simp [range_form_total_correct,keyword,UScalar.eq_equiv,positive,
      (take_expected_result_iff _ .Open bytes.len _).mpr opened,subExecuted,bodyRead]
termination_by (TokenCount tokens,0)
decreasing_by
  all_goals
    have step := take_progress opened
    simp_wf
    try subst_vars
    try rw [Prod.lex_def]
    try simp only [TokenCount] at *
    try simp only [or_true]
    try omega

/-- Every independent connective-body derivation is the actual result. -/
theorem body_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (count limit : Usize)
    (keyword : Token) (form : RangeForm) (depth : Usize) {d : Nat} (same : depth.val = d) {tokens : Tokens}
    {result : core.result.Result (SourceDataRange × Tokens) RangeError}
    (run : BodyRun table.declarations.val bytes.val bytes.len count.val limit.val d keyword form tokens result) :
    read_body table bytes keyword form tokens depth count limit = .ok result := by
  have start : (alloc.vec.Vec.new SourceDataRange).val = [] := rfl
  have startLiterals : (alloc.vec.Vec.new SourceLiteral).val = [] := rfl
  have startFacets : (alloc.vec.Vec.new SourceFacet).val = [] := rfl
  cases run with
  | membersError members =>
    have membersRead := members_execution table bytes count limit depth same _ start members
    rw [read_body.eq_def]
    simp [membersRead]
  | tooFew members few =>
    have membersRead := members_execution table bytes count limit depth same _ start members
    rw [read_body.eq_def]
    simp [membersRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,Nat.lt_succ_iff.mp few,offset_of_total_correct]
  | junctionCloseError members enough failure =>
    have membersRead := members_execution table bytes count limit depth same _ start members
    rw [read_body.eq_def]
    simp [membersRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,Nat.not_lt.mpr enough,Nat.not_le.mpr enough,
      (take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | junction members enough closing =>
    have membersRead := members_execution table bytes count limit depth same _ start members
    rw [read_body.eq_def]
    cases ‹Bool› <;>
      simp [membersRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,Nat.not_lt.mpr enough,Nat.not_le.mpr enough,
        (take_expected_result_iff _ .Close bytes.len _).mpr closing]
  | operandError operand =>
    have operandRead := range_execution table bytes count limit depth same operand
    rw [read_body.eq_def]
    simp [operandRead]
  | complementCloseError operandRun failure =>
    have operandRead := range_execution table bytes count limit depth same operandRun
    rw [read_body.eq_def]
    simp [operandRead,(take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | complement operandRun closing =>
    have operandRead := range_execution table bytes count limit depth same operandRun
    rw [read_body.eq_def]
    simp [operandRead,(take_expected_result_iff _ .Close bytes.len _).mpr closing]
  | literalsError list =>
    have listRead := literals_execution table bytes count limit _ startLiterals list
    rw [read_body.eq_def]
    simp [listRead]
  | noLiteral list few =>
    have listRead := literals_execution table bytes count limit _ startLiterals list
    have empty := List.eq_nil_of_length_eq_zero (Nat.lt_one_iff.mp few)
    rw [read_body.eq_def]
    simp [listRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,empty,offset_of_total_correct]
  | oneOfCloseError list enough failure =>
    have listRead := literals_execution table bytes count limit _ startLiterals list
    have nonempty : _ ≠ [] := List.ne_nil_of_length_pos enough
    rw [read_body.eq_def]
    simp [listRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,Nat.not_lt.mpr enough,nonempty,
      (take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | oneOf list enough closing =>
    have listRead := literals_execution table bytes count limit _ startLiterals list
    have nonempty : _ ≠ [] := List.ne_nil_of_length_pos enough
    rw [read_body.eq_def]
    simp [listRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,Nat.not_lt.mpr enough,nonempty,
      (take_expected_result_iff _ .Close bytes.len _).mpr closing]
  | datatypeTokenError failure =>
    rw [read_body.eq_def]
    simp [(take_expected_result_iff _ .Iri bytes.len _).mpr failure]
  | restrictionDatatypeError taken resolved =>
    rw [read_body.eq_def]
    simp [(take_expected_result_iff _ .Iri bytes.len _).mpr taken,
      (resolve_result_iff table bytes _ .Iri limit _).mpr resolved]
  | facetsError taken resolved facets =>
    have facetsRead := facets_execution table bytes count limit _ startFacets facets
    rw [read_body.eq_def]
    simp [(take_expected_result_iff _ .Iri bytes.len _).mpr taken,
      (resolve_result_iff table bytes _ .Iri limit _).mpr resolved,facetsRead]
  | noFacet taken resolved facets few =>
    have facetsRead := facets_execution table bytes count limit _ startFacets facets
    have empty := List.eq_nil_of_length_eq_zero (Nat.lt_one_iff.mp few)
    rw [read_body.eq_def]
    simp [(take_expected_result_iff _ .Iri bytes.len _).mpr taken,
      (resolve_result_iff table bytes _ .Iri limit _).mpr resolved,facetsRead,alloc.vec.Vec.len_val,
      UScalar.lt_equiv,few,empty,offset_of_total_correct]
  | restrictionCloseError taken resolved facets enough failure =>
    have facetsRead := facets_execution table bytes count limit _ startFacets facets
    have nonempty : _ ≠ [] := List.ne_nil_of_length_pos enough
    rw [read_body.eq_def]
    simp [(take_expected_result_iff _ .Iri bytes.len _).mpr taken,
      (resolve_result_iff table bytes _ .Iri limit _).mpr resolved,facetsRead,alloc.vec.Vec.len_val,
      UScalar.lt_equiv,Nat.not_lt.mpr enough,nonempty,(take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | restriction taken resolved facets enough closing =>
    have facetsRead := facets_execution table bytes count limit _ startFacets facets
    have nonempty : _ ≠ [] := List.ne_nil_of_length_pos enough
    rw [read_body.eq_def]
    simp [(take_expected_result_iff _ .Iri bytes.len _).mpr taken,
      (resolve_result_iff table bytes _ .Iri limit _).mpr resolved,facetsRead,alloc.vec.Vec.len_val,
      UScalar.lt_equiv,Nat.not_lt.mpr enough,nonempty,(take_expected_result_iff _ .Close bytes.len _).mpr closing]
termination_by (TokenCount tokens,2)
decreasing_by
  all_goals
    simp_wf
    try subst_vars
    try rw [Prod.lex_def]
    try simp only [TokenCount] at *
    try simp only [or_true]
    try omega

/-- Every independent member-sequence derivation is the actual result. -/
theorem members_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (count limit : Usize)
    (depth : Usize) {d : Nat} (same : depth.val = d) (members : alloc.vec.Vec SourceDataRange)
    {prior : List SourceDataRange} (contents : members.val = prior) {tokens : Tokens}
    {result : core.result.Result (alloc.vec.Vec SourceDataRange × Tokens) RangeError}
    (run : MembersRun table.declarations.val bytes.val bytes.len count.val limit.val d prior tokens result) :
    read_members table bytes tokens members depth count limit = .ok result := by
  cases run with
  | empty records =>
    have equal : members = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_members.eq_def,equal]
  | stop close records =>
    have equal : members = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_members.eq_def,equal]
    simp [closes_total_correct,close]
  | countLimit notClose full =>
    rw [read_members.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,full]
  | memberError notClose room member =>
    have memberRead := range_execution table bytes count limit depth same member
    rw [read_members.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,
      show ¬ count.val ≤ prior.length by omega,memberRead]
  | member notClose room memberRun later =>
    have memberRead := range_execution table bytes count limit depth same memberRun
    obtain ⟨actual,executed,_,progress⟩ := read_range_total_correct table bytes _ depth count limit
    rw [memberRead] at executed
    have step := progress _ _ (Result.ok_injective executed).symm
    obtain ⟨appended,push,appendedContents⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.push_spec members _ (by rw [contents]; scalar_tac))
    have laterRead := members_execution table bytes count limit depth same appended
      (by rw [appendedContents,contents]) later
    rw [read_members.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,
      show ¬ count.val ≤ prior.length by omega,memberRead,push,laterRead]
termination_by (TokenCount tokens,1)
decreasing_by
  all_goals
    simp_wf
    try subst_vars
    try rw [Prod.lex_def]
    try simp only [TokenCount] at *
    try simp only [or_true]
    try omega
end

/-- Every exact data range and first error is equivalent to its independent derivation. -/
theorem read_range_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (depth count limit : Usize) (result : core.result.Result (SourceDataRange × Tokens) RangeError) :
    read_range table bytes tokens depth count limit = .ok result ↔
      RangeRun table.declarations.val bytes.val bytes.len count.val limit.val depth.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct,_⟩ := read_range_total_correct table bytes tokens depth count limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · exact range_execution table bytes count limit depth rfl
/-- The public reader: every exact data range and first error is equivalent to
    its independent derivation at the caller's nesting allowance. -/
theorem read_data_range_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (depth count limit : Usize) (result : core.result.Result (SourceDataRange × Tokens) RangeError) :
    read_data_range table bytes tokens depth count limit = .ok result ↔
      RangeRun table.declarations.val bytes.val bytes.len count.val limit.val depth.val tokens result := by
  rw [read_data_range]
  exact read_range_result_iff table bytes tokens depth count limit result
/-- The public reader is total and follows the independent grammar. -/
theorem read_data_range_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (depth count limit : Usize) :
    ∃ result, read_data_range table bytes tokens depth count limit = .ok result ∧
      RangeRun table.declarations.val bytes.val bytes.len count.val limit.val depth.val tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest < TokenCount tokens := by
  rw [read_data_range]
  exact read_range_total_correct table bytes tokens depth count limit
/-- An accepted data range consumes at least one token. -/
theorem range_progress {table : prefixes.PrefixTable} {bytes : alloc.vec.Vec U8} {tokens rest : Tokens}
    {depth count limit : Usize} {value : SourceDataRange}
    (accepted : RangeRun table.declarations.val bytes.val bytes.len count.val limit.val depth.val tokens
      (.Ok (value,rest))) : TokenCount rest < TokenCount tokens := by
  obtain ⟨actual,executed,correct,progress⟩ := read_range_total_correct table bytes tokens depth count limit
  rw [(read_range_result_iff table bytes tokens depth count limit _).mpr accepted] at executed
  exact progress value rest (Result.ok_injective executed).symm

/-- Independent optional data range of a data number restriction: none before
    `)` or at the end, and otherwise one data range. -/
inductive OptionalRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Nat → Tokens → core.result.Result (Option SourceDataRange × Tokens) RangeError → Prop
  | empty {depth : Nat} : OptionalRun rows source eof count limit depth .Empty (.Ok (none,.Empty))
  | stop {depth : Nat} {token : Token} {tail : Tokens} (close : token.terminal = .Close) :
      OptionalRun rows source eof count limit depth (.Cons token tail) (.Ok (none,.Cons token tail))
  | rangeError {depth : Nat} {token : Token} {tail : Tokens} {error : RangeError}
      (notClose : token.terminal ≠ .Close)
      (range : RangeRun rows source eof count limit depth (.Cons token tail) (.Err error)) :
      OptionalRun rows source eof count limit depth (.Cons token tail) (.Err error)
  | range {depth : Nat} {token : Token} {tail rest : Tokens} {value : SourceDataRange}
      (notClose : token.terminal ≠ .Close)
      (rangeRun : RangeRun rows source eof count limit depth (.Cons token tail) (.Ok (value,rest))) :
      OptionalRun rows source eof count limit depth (.Cons token tail) (.Ok (some value,rest))

/-- The optional data range is total, follows the independent grammar, and never
    returns more tokens than it received. -/
theorem read_optional_range_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (depth count limit : Usize) :
    ∃ result, read_optional_range table bytes tokens depth count limit = .ok result ∧
      OptionalRun table.declarations.val bytes.val bytes.len count.val limit.val depth.val tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest ≤ TokenCount tokens := by
  rw [read_optional_range.eq_def]
  cases tokens with
  | Empty => exact ⟨.Ok (none,.Empty),rfl,.empty,by intro value rest same; cases same; simp⟩
  | Cons token tail =>
    simp only [closes_total_correct,bind_ok]
    by_cases close : token.terminal = .Close
    · refine ⟨.Ok (none,.Cons token tail),by simp [close],.stop close,?_⟩
      intro value rest same
      cases same
      simp
    · obtain ⟨range,rangeRead,rangeCorrect,rangeProgress⟩ :=
        read_range_total_correct table bytes (.Cons token tail) depth count limit
      cases range with
      | Err error =>
        exact ⟨.Err error,by simp [close,rangeRead],.rangeError close rangeCorrect,
          by intro value rest impossible; cases impossible⟩
      | Ok pair =>
        obtain ⟨range,rest⟩ := pair
        refine ⟨.Ok (some range,rest),by simp [close,rangeRead],.range close rangeCorrect,?_⟩
        intro value rest' same
        have step := rangeProgress range rest rfl
        cases same
        omega
/-- Every exact optional data range and first error is equivalent to its
    independent derivation. -/
theorem read_optional_range_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (depth count limit : Usize)
    (result : core.result.Result (Option SourceDataRange × Tokens) RangeError) :
    read_optional_range table bytes tokens depth count limit = .ok result ↔
      OptionalRun table.declarations.val bytes.val bytes.len count.val limit.val depth.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct,_⟩ := read_optional_range_total_correct table bytes tokens depth count limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro run
    cases run with
    | empty => rw [read_optional_range.eq_def]
    | stop close =>
      rw [read_optional_range.eq_def]
      simp [closes_total_correct,close]
    | rangeError notClose range =>
      rw [read_optional_range.eq_def]
      simp [closes_total_correct,notClose,(read_range_result_iff table bytes _ depth count limit _).mpr range]
    | range notClose rangeRun =>
      rw [read_optional_range.eq_def]
      simp [closes_total_correct,notClose,(read_range_result_iff table bytes _ depth count limit _).mpr rangeRun]
end Rowl.FunctionalRanges
