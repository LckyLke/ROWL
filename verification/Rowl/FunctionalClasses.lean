import Rowl.Decimal
import Rowl.FunctionalHeaderIdentity
import Rowl.FunctionalIndividuals
import Rowl.FunctionalRanges

/-!
Functional Syntax class expressions of the reasoner's fragment, proved total
and exact against an independent recursive grammar: named classes,
intersections, unions, complements, enumerations of individuals, existential
and universal restrictions, individual value restrictions, self restrictions,
number restrictions with or without a filler, whose number is an integer token
of ASCII digits with a value of at most the count limit, object property
expressions, and the data restrictions over one data property, with
individuals, literals and data ranges read by their independent grammars. Every
result and first error has its independent derivation, and every derivation is
the actual result.
-/
namespace Rowl.FunctionalClasses
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional_classes
open RowlRust.functional_header (HeaderIri)
open RowlRust.functional_individuals (IndividualError SourceIndividual)
open RowlRust.functional_lexer RowlRust.functional
open Rowl.FunctionalHeaderIdentity (Kind iri_kind_total_correct)
open Rowl.FunctionalLexer (TokenCount)
open Rowl.FunctionalIndividuals (IndividualRun ListRun)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The class-expression keywords: the seventeen connectives and every other
    terminal. -/
def KeywordOf : Terminal → ClassKeyword
  | .Keyword .ObjectIntersectionOf => .Connective (.Junction true)
  | .Keyword .ObjectUnionOf => .Connective (.Junction false)
  | .Keyword .ObjectComplementOf => .Connective .Complement
  | .Keyword .ObjectSomeValuesFrom => .Connective (.Restriction true)
  | .Keyword .ObjectAllValuesFrom => .Connective (.Restriction false)
  | .Keyword .ObjectOneOf => .Connective .OneOf
  | .Keyword .ObjectHasValue => .Connective .HasValue
  | .Keyword .ObjectHasSelf => .Connective .SelfRestriction
  | .Keyword .ObjectMinCardinality => .Connective (.Cardinality .Min)
  | .Keyword .ObjectMaxCardinality => .Connective (.Cardinality .Max)
  | .Keyword .ObjectExactCardinality => .Connective (.Cardinality .Exact)
  | .Keyword .DataSomeValuesFrom => .Connective (.DataRestriction true)
  | .Keyword .DataAllValuesFrom => .Connective (.DataRestriction false)
  | .Keyword .DataHasValue => .Connective .DataValue
  | .Keyword .DataMinCardinality => .Connective (.DataCardinality .Min)
  | .Keyword .DataMaxCardinality => .Connective (.DataCardinality .Max)
  | .Keyword .DataExactCardinality => .Connective (.DataCardinality .Exact)
  | _ => .Other
/-- Independent first-terminal class required at each position. -/
def Expected : ClassExpected → Terminal → Prop
  | .Class, terminal => KeywordOf terminal ≠ .Other ∨ ∃ kind, Kind terminal = some kind
  | .Open, terminal => terminal = .Open
  | .Property, terminal => terminal = .Keyword .ObjectInverseOf ∨ ∃ kind, Kind terminal = some kind
  | .Iri, terminal => ∃ kind, Kind terminal = some kind
  | .Close, terminal => terminal = .Close
  | .Number, terminal => terminal = .Integer
/-- Where the next token starts, or the source length at the end. -/
def Position (eof : Usize) : Tokens → Usize
  | .Empty => eof
  | .Cons token _ => token.start

theorem class_keyword_total_correct (terminal : Terminal) : class_keyword terminal = .ok (KeywordOf terminal) := by
  cases terminal <;> first | rfl | (rename_i keyword; cases keyword <;> rfl)
theorem inverse_keyword_total_correct (terminal : Terminal) :
    inverse_keyword terminal = .ok (decide (terminal = .Keyword .ObjectInverseOf)) := by
  cases terminal <;> (try (rename_i keyword; cases keyword)) <;> simp [inverse_keyword]
theorem closes_total_correct (terminal : Terminal) : closes terminal = .ok (decide (terminal = .Close)) := by
  cases terminal <;> simp [closes]
theorem offset_of_total_correct (tokens : Tokens) (eof : Usize) : offset_of tokens eof = .ok (Position eof tokens) := by
  cases tokens <;> rfl
/-- Actual position checks decide exactly the independent terminal classes. -/
theorem expected_terminal_total_correct (expected : ClassExpected) (terminal : Terminal) :
    expected_terminal expected terminal = .ok (decide (Expected expected terminal)) := by
  cases expected <;> cases terminal <;> (try (rename_i keyword; cases keyword)) <;>
    simp [expected_terminal,Expected,class_keyword_total_correct,inverse_keyword_total_correct,
      closes_total_correct,iri_kind_total_correct,KeywordOf,Kind,core.option.Option.is_some]

/-- One syntax step: the first token must belong to the expected class. A
    missing token reports the original source length, a wrong one its start. -/
inductive TakeRun (eof : Usize) (expected : ClassExpected) :
    Tokens → core.result.Result (Token × Tokens) ClassError → Prop
  | empty : TakeRun eof expected .Empty (.Err (.Expected expected eof))
  | wrong (token : Token) (rest : Tokens) (different : ¬ Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Err (.Expected expected token.start))
  | taken (token : Token) (rest : Tokens) (accepted : Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Ok (token,rest))

theorem take_expected_total_correct (tokens : Tokens) (expected : ClassExpected) (eof : Usize) :
    ∃ result, take_expected tokens expected eof = .ok result ∧ TakeRun eof expected tokens result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected expected eof),rfl,.empty⟩
  | Cons token rest =>
    by_cases accepted : Expected expected token.terminal
    · exact ⟨.Ok (token,rest),by simp [take_expected,expected_terminal_total_correct,accepted],.taken _ _ accepted⟩
    · exact ⟨.Err (.Expected expected token.start),by simp [take_expected,expected_terminal_total_correct,accepted],
        .wrong _ _ accepted⟩
private theorem take_run_unique {eof : Usize} {expected : ClassExpected} {tokens : Tokens}
    {one two : core.result.Result (Token × Tokens) ClassError}
    (first : TakeRun eof expected tokens one) (second : TakeRun eof expected tokens two) : one = two := by
  cases first <;> cases second <;> first | rfl | contradiction
theorem take_expected_result_iff (tokens : Tokens) (expected : ClassExpected) (eof : Usize)
    (result : core.result.Result (Token × Tokens) ClassError) :
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
theorem take_progress {eof : Usize} {expected : ClassExpected} {tokens rest : Tokens} {token : Token}
    (taken : TakeRun eof expected tokens (.Ok (token,rest))) : TokenCount tokens = 1+TokenCount rest := by
  cases taken
  rfl

/-- An IRI token resolves its original span through the checked prefix rows;
    any other token is reported as missing the expected syntax. -/
inductive ResolveRun (rows : List prefixes.Declaration) (source : List U8) (limit : Nat) (expected : ClassExpected) :
    Token → core.result.Result HeaderIri ClassError → Prop
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
    (expected : ClassExpected) (limit : Usize) :
    ∃ result, resolve table bytes token expected limit = .ok result ∧
      ResolveRun table.declarations.val bytes.val limit.val expected token result := by
  rw [resolve]
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
    (expected : ClassExpected) (limit : Usize) (result : core.result.Result HeaderIri ClassError) :
    resolve table bytes token expected limit = .ok result ↔
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

/-- Independent object property expression grammar: an IRI, or
    `ObjectInverseOf ( IRI )` in source order. -/
inductive PropertyRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (SourceObjectProperty × Tokens) ClassError → Prop
  | empty : PropertyRun rows source eof limit .Empty (.Err (.Expected .Property eof))
  | namedError {token : Token} {tail : Tokens} {error : ClassError}
      (notInverse : token.terminal ≠ .Keyword .ObjectInverseOf)
      (resolved : ResolveRun rows source limit .Property token (.Err error)) :
      PropertyRun rows source eof limit (.Cons token tail) (.Err error)
  | named {token : Token} {tail : Tokens} {iri : HeaderIri}
      (notInverse : token.terminal ≠ .Keyword .ObjectInverseOf)
      (resolved : ResolveRun rows source limit .Property token (.Ok iri)) :
      PropertyRun rows source eof limit (.Cons token tail) (.Ok (.Named iri,tail))
  | openError {token : Token} {tail : Tokens} {error : ClassError}
      (inverse : token.terminal = .Keyword .ObjectInverseOf) (failure : TakeRun eof .Open tail (.Err error)) :
      PropertyRun rows source eof limit (.Cons token tail) (.Err error)
  | iriTokenError {token opening : Token} {tail rest : Tokens} {error : ClassError}
      (inverse : token.terminal = .Keyword .ObjectInverseOf) (opened : TakeRun eof .Open tail (.Ok (opening,rest)))
      (failure : TakeRun eof .Iri rest (.Err error)) :
      PropertyRun rows source eof limit (.Cons token tail) (.Err error)
  | iriError {token opening named : Token} {tail rest after : Tokens} {error : ClassError}
      (inverse : token.terminal = .Keyword .ObjectInverseOf) (opened : TakeRun eof .Open tail (.Ok (opening,rest)))
      (taken : TakeRun eof .Iri rest (.Ok (named,after)))
      (resolved : ResolveRun rows source limit .Iri named (.Err error)) :
      PropertyRun rows source eof limit (.Cons token tail) (.Err error)
  | closeError {token opening named : Token} {tail rest after : Tokens} {iri : HeaderIri} {error : ClassError}
      (inverse : token.terminal = .Keyword .ObjectInverseOf) (opened : TakeRun eof .Open tail (.Ok (opening,rest)))
      (taken : TakeRun eof .Iri rest (.Ok (named,after)))
      (resolved : ResolveRun rows source limit .Iri named (.Ok iri)) (failure : TakeRun eof .Close after (.Err error)) :
      PropertyRun rows source eof limit (.Cons token tail) (.Err error)
  | inverse {token opening named close : Token} {tail rest after remaining : Tokens} {iri : HeaderIri}
      (inverse : token.terminal = .Keyword .ObjectInverseOf) (opened : TakeRun eof .Open tail (.Ok (opening,rest)))
      (taken : TakeRun eof .Iri rest (.Ok (named,after)))
      (resolved : ResolveRun rows source limit .Iri named (.Ok iri))
      (closing : TakeRun eof .Close after (.Ok (close,remaining))) :
      PropertyRun rows source eof limit (.Cons token tail) (.Ok (.Inverse token iri,remaining))

/-- Object property reading is total and follows the independent grammar. -/
theorem read_object_property_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) :
    ∃ result, read_object_property table bytes tokens limit = .ok result ∧
      PropertyRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected .Property bytes.len),by rw [read_object_property],.empty⟩
  | Cons token tail =>
    rw [read_object_property]
    simp only [inverse_keyword_total_correct,bind_ok]
    by_cases inverse : token.terminal = .Keyword .ObjectInverseOf
    · simp only [inverse,decide_true,↓reduceIte,eq_self_iff_true]
      obtain ⟨opened,openRead,openCorrect⟩ := take_expected_total_correct tail .Open bytes.len
      cases opened with
      | Err error => exact ⟨.Err error,by simp [openRead],.openError inverse openCorrect⟩
      | Ok pair =>
        obtain ⟨opening,rest⟩ := pair
        obtain ⟨taken,takenRead,takenCorrect⟩ := take_expected_total_correct rest .Iri bytes.len
        cases taken with
        | Err error => exact ⟨.Err error,by simp [openRead,takenRead],.iriTokenError inverse openCorrect takenCorrect⟩
        | Ok pair =>
          obtain ⟨named,after⟩ := pair
          obtain ⟨resolved,resolveRead,resolveCorrect⟩ := resolve_total_correct table bytes named .Iri limit
          cases resolved with
          | Err error =>
            exact ⟨.Err error,by simp [openRead,takenRead,resolveRead],
              .iriError inverse openCorrect takenCorrect resolveCorrect⟩
          | Ok iri =>
            obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct after .Close bytes.len
            cases closed with
            | Err error =>
              exact ⟨.Err error,by simp [openRead,takenRead,resolveRead,closeRead],
                .closeError inverse openCorrect takenCorrect resolveCorrect closeCorrect⟩
            | Ok pair =>
              obtain ⟨close,remaining⟩ := pair
              exact ⟨.Ok (.Inverse token iri,remaining),by simp [openRead,takenRead,resolveRead,closeRead],
                .inverse inverse openCorrect takenCorrect resolveCorrect closeCorrect⟩
    · simp only [inverse,decide_false,Bool.false_eq_true,↓reduceIte]
      obtain ⟨resolved,resolveRead,resolveCorrect⟩ := resolve_total_correct table bytes token .Property limit
      cases resolved with
      | Err error => exact ⟨.Err error,by simp [resolveRead],.namedError inverse resolveCorrect⟩
      | Ok iri => exact ⟨.Ok (.Named iri,tail),by simp [resolveRead],.named inverse resolveCorrect⟩
/-- Every exact object property expression and first error is its independent derivation. -/
theorem read_object_property_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) (result : core.result.Result (SourceObjectProperty × Tokens) ClassError) :
    read_object_property table bytes tokens limit = .ok result ↔
      PropertyRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_object_property_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | empty => rw [read_object_property]
    | namedError notInverse resolved =>
      rw [read_object_property]
      simp [inverse_keyword_total_correct,notInverse,(resolve_result_iff table bytes _ .Property limit _).mpr resolved]
    | named notInverse resolved =>
      rw [read_object_property]
      simp [inverse_keyword_total_correct,notInverse,(resolve_result_iff table bytes _ .Property limit _).mpr resolved]
    | openError inverse failure =>
      rw [read_object_property]
      simp [inverse_keyword_total_correct,inverse,(take_expected_result_iff _ .Open bytes.len _).mpr failure]
    | iriTokenError inverse opened failure =>
      rw [read_object_property]
      simp [inverse_keyword_total_correct,inverse,(take_expected_result_iff _ .Open bytes.len _).mpr opened,
        (take_expected_result_iff _ .Iri bytes.len _).mpr failure]
    | iriError inverse opened taken resolved =>
      rw [read_object_property]
      simp [inverse_keyword_total_correct,inverse,(take_expected_result_iff _ .Open bytes.len _).mpr opened,
        (take_expected_result_iff _ .Iri bytes.len _).mpr taken,(resolve_result_iff table bytes _ .Iri limit _).mpr resolved]
    | closeError inverse opened taken resolved failure =>
      rw [read_object_property]
      simp [inverse_keyword_total_correct,inverse,(take_expected_result_iff _ .Open bytes.len _).mpr opened,
        (take_expected_result_iff _ .Iri bytes.len _).mpr taken,(resolve_result_iff table bytes _ .Iri limit _).mpr resolved,
        (take_expected_result_iff _ .Close bytes.len _).mpr failure]
    | inverse inverse opened taken resolved closing =>
      rw [read_object_property]
      simp [inverse_keyword_total_correct,inverse,(take_expected_result_iff _ .Open bytes.len _).mpr opened,
        (take_expected_result_iff _ .Iri bytes.len _).mpr taken,(resolve_result_iff table bytes _ .Iri limit _).mpr resolved,
        (take_expected_result_iff _ .Close bytes.len _).mpr closing]
/-- An accepted object property expression consumes at least its first token. -/
theorem property_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens rest : Tokens} {property : SourceObjectProperty}
    (accepted : PropertyRun rows source eof limit tokens (.Ok (property,rest))) : TokenCount rest < TokenCount tokens := by
  cases accepted with
  | named => simp only [TokenCount]; omega
  | inverse inverse opened taken resolved closing =>
    have one := take_progress opened
    have two := take_progress taken
    have three := take_progress closing
    try simp only [TokenCount] at *
    omega

/-- A data property: an IRI resolved through the checked prefix rows. -/
inductive DataPropertyRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (HeaderIri × Tokens) ClassError → Prop
  | empty : DataPropertyRun rows source eof limit .Empty (.Err (.Expected .Iri eof))
  | error {token : Token} {tail : Tokens} {error : ClassError}
      (resolved : ResolveRun rows source limit .Iri token (.Err error)) :
      DataPropertyRun rows source eof limit (.Cons token tail) (.Err error)
  | property {token : Token} {tail : Tokens} {iri : HeaderIri}
      (resolved : ResolveRun rows source limit .Iri token (.Ok iri)) :
      DataPropertyRun rows source eof limit (.Cons token tail) (.Ok (iri,tail))

/-- Data property reading is total and follows the independent grammar. -/
theorem read_data_property_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) :
    ∃ result, read_data_property table bytes tokens limit = .ok result ∧
      DataPropertyRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected .Iri bytes.len),by rw [read_data_property],.empty⟩
  | Cons token tail =>
    rw [read_data_property]
    obtain ⟨resolved,resolveRead,resolveCorrect⟩ := resolve_total_correct table bytes token .Iri limit
    cases resolved with
    | Err error => exact ⟨.Err error,by simp [resolveRead],.error resolveCorrect⟩
    | Ok iri => exact ⟨.Ok (iri,tail),by simp [resolveRead],.property resolveCorrect⟩
/-- Every data property and first error is its independent derivation. -/
theorem read_data_property_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) (result : core.result.Result (HeaderIri × Tokens) ClassError) :
    read_data_property table bytes tokens limit = .ok result ↔
      DataPropertyRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_data_property_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | empty => rw [read_data_property]
    | error resolved =>
      rw [read_data_property]
      simp [(resolve_result_iff table bytes _ .Iri limit _).mpr resolved]
    | property resolved =>
      rw [read_data_property]
      simp [(resolve_result_iff table bytes _ .Iri limit _).mpr resolved]
/-- An accepted data property consumes its token. -/
theorem data_property_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens rest : Tokens} {property : HeaderIri}
    (accepted : DataPropertyRun rows source eof limit tokens (.Ok (property,rest))) :
    TokenCount tokens = 1+TokenCount rest := by
  cases accepted
  rfl

mutual
/-- Independent class-expression grammar in source order. A named class is an
    IRI token resolved through the checked prefix rows. At a connective keyword
    the remaining nesting allowance is checked, then `(`, then the connective's
    body one level deeper. -/
inductive ClassRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Nat → Tokens → core.result.Result (SourceClass × Tokens) ClassError → Prop
  | empty {depth : Nat} : ClassRun rows source eof count limit depth .Empty (.Err (.Expected .Class eof))
  | namedError {depth : Nat} {token : Token} {tail : Tokens} {error : ClassError}
      (other : KeywordOf token.terminal = .Other) (resolved : ResolveRun rows source limit .Class token (.Err error)) :
      ClassRun rows source eof count limit depth (.Cons token tail) (.Err error)
  | named {depth : Nat} {token : Token} {tail : Tokens} {iri : HeaderIri}
      (other : KeywordOf token.terminal = .Other) (resolved : ResolveRun rows source limit .Class token (.Ok iri)) :
      ClassRun rows source eof count limit depth (.Cons token tail) (.Ok (.Named iri,tail))
  | depthLimit {token : Token} {tail : Tokens} {form : ClassForm}
      (keyword : KeywordOf token.terminal = .Connective form) :
      ClassRun rows source eof count limit 0 (.Cons token tail) (.Err (.DepthLimit token.start))
  | openError {depth : Nat} {token : Token} {tail : Tokens} {form : ClassForm} {error : ClassError}
      (keyword : KeywordOf token.terminal = .Connective form) (failure : TakeRun eof .Open tail (.Err error)) :
      ClassRun rows source eof count limit (depth+1) (.Cons token tail) (.Err error)
  | connective {depth : Nat} {token opening : Token} {tail inner : Tokens} {form : ClassForm}
      {result : core.result.Result (SourceClass × Tokens) ClassError}
      (keyword : KeywordOf token.terminal = .Connective form)
      (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (body : ConnectiveRun rows source eof count limit depth token form inner result) :
      ClassRun rows source eof count limit (depth+1) (.Cons token tail) result
/-- Independent connective bodies after `(`. Intersections and unions read the
    maximal member sequence, then require two members, then `)`. Complements read
    one operand and `)`. Restrictions read an object property expression, the
    filler and `)`. Enumerations read an individual list of at least one member
    and `)`; value restrictions read an object property expression, one
    individual and `)`. Self restrictions read an object property expression and
    `)`; number restrictions read the number, an integer token whose bounded
    reading is its value, then an object property expression, the optional
    filler and `)`. Data restrictions read one data property, then a data range,
    a literal or a number before the property and an optional data range, and
    `)`; data ranges nest within the remaining allowance. -/
inductive ConnectiveRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Nat → Token → ClassForm → Tokens → core.result.Result (SourceClass × Tokens) ClassError → Prop
  | membersError {depth : Nat} {keyword : Token} {conjunctive : Bool} {tokens : Tokens} {error : ClassError}
      (members : MembersRun rows source eof count limit depth [] tokens (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.Junction conjunctive) tokens (.Err error)
  | tooFew {depth : Nat} {keyword : Token} {conjunctive : Bool} {tokens rest : Tokens}
      {list : alloc.vec.Vec SourceClass}
      (members : MembersRun rows source eof count limit depth [] tokens (.Ok (list,rest)))
      (few : list.val.length < 2) :
      ConnectiveRun rows source eof count limit depth keyword (.Junction conjunctive) tokens
        (.Err (.Expected .Class (Position eof rest)))
  | junctionCloseError {depth : Nat} {keyword : Token} {conjunctive : Bool} {tokens rest : Tokens}
      {list : alloc.vec.Vec SourceClass} {error : ClassError}
      (members : MembersRun rows source eof count limit depth [] tokens (.Ok (list,rest)))
      (enough : 2 ≤ list.val.length) (failure : TakeRun eof .Close rest (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.Junction conjunctive) tokens (.Err error)
  | junction {depth : Nat} {keyword close : Token} {conjunctive : Bool} {tokens rest remaining : Tokens}
      {list : alloc.vec.Vec SourceClass}
      (members : MembersRun rows source eof count limit depth [] tokens (.Ok (list,rest)))
      (enough : 2 ≤ list.val.length) (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      ConnectiveRun rows source eof count limit depth keyword (.Junction conjunctive) tokens
        (.Ok (if conjunctive then .IntersectionOf keyword list else .UnionOf keyword list,remaining))
  | operandError {depth : Nat} {keyword : Token} {tokens : Tokens} {error : ClassError}
      (operand : ClassRun rows source eof count limit depth tokens (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword .Complement tokens (.Err error)
  | complementCloseError {depth : Nat} {keyword : Token} {tokens rest : Tokens} {operand : SourceClass}
      {error : ClassError}
      (operandRun : ClassRun rows source eof count limit depth tokens (.Ok (operand,rest)))
      (failure : TakeRun eof .Close rest (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword .Complement tokens (.Err error)
  | complement {depth : Nat} {keyword close : Token} {tokens rest remaining : Tokens} {operand : SourceClass}
      (operandRun : ClassRun rows source eof count limit depth tokens (.Ok (operand,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      ConnectiveRun rows source eof count limit depth keyword .Complement tokens
        (.Ok (.ComplementOf keyword operand,remaining))
  | propertyError {depth : Nat} {keyword : Token} {existential : Bool} {tokens : Tokens} {error : ClassError}
      (property : PropertyRun rows source eof limit tokens (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.Restriction existential) tokens (.Err error)
  | fillerError {depth : Nat} {keyword : Token} {existential : Bool} {tokens rest : Tokens}
      {property : SourceObjectProperty} {error : ClassError}
      (propertyRun : PropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (filler : ClassRun rows source eof count limit depth rest (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.Restriction existential) tokens (.Err error)
  | restrictionCloseError {depth : Nat} {keyword : Token} {existential : Bool} {tokens rest after : Tokens}
      {property : SourceObjectProperty} {filler : SourceClass} {error : ClassError}
      (propertyRun : PropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (fillerRun : ClassRun rows source eof count limit depth rest (.Ok (filler,after)))
      (failure : TakeRun eof .Close after (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.Restriction existential) tokens (.Err error)
  | restriction {depth : Nat} {keyword close : Token} {existential : Bool} {tokens rest after remaining : Tokens}
      {property : SourceObjectProperty} {filler : SourceClass}
      (propertyRun : PropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (fillerRun : ClassRun rows source eof count limit depth rest (.Ok (filler,after)))
      (closing : TakeRun eof .Close after (.Ok (close,remaining))) :
      ConnectiveRun rows source eof count limit depth keyword (.Restriction existential) tokens
        (.Ok (if existential then .SomeValuesFrom keyword property filler
          else .AllValuesFrom keyword property filler,remaining))
  | oneOfError {depth : Nat} {keyword : Token} {tokens : Tokens} {error : IndividualError}
      (list : ListRun rows source eof 1 count limit tokens (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword .OneOf tokens (.Err (.Individual error))
  | oneOfCloseError {depth : Nat} {keyword : Token} {tokens rest : Tokens}
      {members : alloc.vec.Vec SourceIndividual} {error : ClassError}
      (list : ListRun rows source eof 1 count limit tokens (.Ok (members,rest)))
      (failure : TakeRun eof .Close rest (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword .OneOf tokens (.Err error)
  | oneOf {depth : Nat} {keyword close : Token} {tokens rest remaining : Tokens}
      {members : alloc.vec.Vec SourceIndividual}
      (list : ListRun rows source eof 1 count limit tokens (.Ok (members,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      ConnectiveRun rows source eof count limit depth keyword .OneOf tokens (.Ok (.OneOf keyword members,remaining))
  | valuePropertyError {depth : Nat} {keyword : Token} {tokens : Tokens} {error : ClassError}
      (property : PropertyRun rows source eof limit tokens (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword .HasValue tokens (.Err error)
  | valueError {depth : Nat} {keyword : Token} {tokens rest : Tokens} {property : SourceObjectProperty}
      {error : IndividualError}
      (propertyRun : PropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (failure : IndividualRun rows source eof limit rest (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword .HasValue tokens (.Err (.Individual error))
  | valueCloseError {depth : Nat} {keyword : Token} {tokens rest after : Tokens} {property : SourceObjectProperty}
      {individual : SourceIndividual} {error : ClassError}
      (propertyRun : PropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (valueRun : IndividualRun rows source eof limit rest (.Ok (individual,after)))
      (failure : TakeRun eof .Close after (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword .HasValue tokens (.Err error)
  | hasValue {depth : Nat} {keyword close : Token} {tokens rest after remaining : Tokens}
      {property : SourceObjectProperty} {individual : SourceIndividual}
      (propertyRun : PropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (valueRun : IndividualRun rows source eof limit rest (.Ok (individual,after)))
      (closing : TakeRun eof .Close after (.Ok (close,remaining))) :
      ConnectiveRun rows source eof count limit depth keyword .HasValue tokens
        (.Ok (.HasValue keyword property individual,remaining))
  | selfPropertyError {depth : Nat} {keyword : Token} {tokens : Tokens} {error : ClassError}
      (property : PropertyRun rows source eof limit tokens (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword .SelfRestriction tokens (.Err error)
  | selfCloseError {depth : Nat} {keyword : Token} {tokens rest : Tokens} {property : SourceObjectProperty}
      {error : ClassError}
      (propertyRun : PropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (failure : TakeRun eof .Close rest (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword .SelfRestriction tokens (.Err error)
  | hasSelf {depth : Nat} {keyword close : Token} {tokens rest remaining : Tokens} {property : SourceObjectProperty}
      (propertyRun : PropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      ConnectiveRun rows source eof count limit depth keyword .SelfRestriction tokens
        (.Ok (.HasSelf keyword property,remaining))
  | numberError {depth : Nat} {keyword : Token} {bound : Bound} {tokens : Tokens} {error : ClassError}
      (failure : TakeRun eof .Number tokens (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.Cardinality bound) tokens (.Err error)
  | countError {depth : Nat} {keyword number : Token} {bound : Bound} {tokens rest : Tokens}
      (taken : TakeRun eof .Number tokens (.Ok (number,rest)))
      (excess : ∀ value, ¬ Rowl.Decimal.Bounded source number.start.val number.end.val count value) :
      ConnectiveRun rows source eof count limit depth keyword (.Cardinality bound) tokens
        (.Err (.CountLimit number.start))
  | countPropertyError {depth : Nat} {keyword number : Token} {bound : Bound} {tokens rest : Tokens} {value : Usize}
      {error : ClassError}
      (taken : TakeRun eof .Number tokens (.Ok (number,rest)))
      (counted : Rowl.Decimal.Bounded source number.start.val number.end.val count value.val)
      (property : PropertyRun rows source eof limit rest (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.Cardinality bound) tokens (.Err error)
  | countFillerError {depth : Nat} {keyword number : Token} {bound : Bound} {tokens rest after : Tokens}
      {value : Usize} {property : SourceObjectProperty} {error : ClassError}
      (taken : TakeRun eof .Number tokens (.Ok (number,rest)))
      (counted : Rowl.Decimal.Bounded source number.start.val number.end.val count value.val)
      (propertyRun : PropertyRun rows source eof limit rest (.Ok (property,after)))
      (filler : FillerRun rows source eof count limit depth after (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.Cardinality bound) tokens (.Err error)
  | countCloseError {depth : Nat} {keyword number : Token} {bound : Bound} {tokens rest after last : Tokens}
      {value : Usize} {property : SourceObjectProperty} {filler : Option SourceClass} {error : ClassError}
      (taken : TakeRun eof .Number tokens (.Ok (number,rest)))
      (counted : Rowl.Decimal.Bounded source number.start.val number.end.val count value.val)
      (propertyRun : PropertyRun rows source eof limit rest (.Ok (property,after)))
      (fillerRun : FillerRun rows source eof count limit depth after (.Ok (filler,last)))
      (failure : TakeRun eof .Close last (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.Cardinality bound) tokens (.Err error)
  | cardinality {depth : Nat} {keyword number close : Token} {bound : Bound} {tokens rest after last remaining : Tokens}
      {value : Usize} {property : SourceObjectProperty} {filler : Option SourceClass}
      (taken : TakeRun eof .Number tokens (.Ok (number,rest)))
      (counted : Rowl.Decimal.Bounded source number.start.val number.end.val count value.val)
      (propertyRun : PropertyRun rows source eof limit rest (.Ok (property,after)))
      (fillerRun : FillerRun rows source eof count limit depth after (.Ok (filler,last)))
      (closing : TakeRun eof .Close last (.Ok (close,remaining))) :
      ConnectiveRun rows source eof count limit depth keyword (.Cardinality bound) tokens
        (.Ok (.Cardinality keyword bound number value property filler,remaining))
  | dataPropertyError {depth : Nat} {keyword : Token} {existential : Bool} {tokens : Tokens} {error : ClassError}
      (property : DataPropertyRun rows source eof limit tokens (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.DataRestriction existential) tokens (.Err error)
  | rangeError {depth : Nat} {keyword : Token} {existential : Bool} {tokens rest : Tokens} {property : HeaderIri}
      {error : functional_ranges.RangeError}
      (propertyRun : DataPropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (range : Rowl.FunctionalRanges.RangeRun rows source eof count limit depth rest (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.DataRestriction existential) tokens
        (.Err (.Range error))
  | dataCloseError {depth : Nat} {keyword : Token} {existential : Bool} {tokens rest after : Tokens}
      {property : HeaderIri} {range : functional_ranges.SourceDataRange} {error : ClassError}
      (propertyRun : DataPropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (rangeRun : Rowl.FunctionalRanges.RangeRun rows source eof count limit depth rest (.Ok (range,after)))
      (failure : TakeRun eof .Close after (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.DataRestriction existential) tokens (.Err error)
  | dataRestriction {depth : Nat} {keyword close : Token} {existential : Bool} {tokens rest after remaining : Tokens}
      {property : HeaderIri} {range : functional_ranges.SourceDataRange}
      (propertyRun : DataPropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (rangeRun : Rowl.FunctionalRanges.RangeRun rows source eof count limit depth rest (.Ok (range,after)))
      (closing : TakeRun eof .Close after (.Ok (close,remaining))) :
      ConnectiveRun rows source eof count limit depth keyword (.DataRestriction existential) tokens
        (.Ok (if existential then .DataSomeValuesFrom keyword property range
          else .DataAllValuesFrom keyword property range,remaining))
  | dataValuePropertyError {depth : Nat} {keyword : Token} {tokens : Tokens} {error : ClassError}
      (property : DataPropertyRun rows source eof limit tokens (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword .DataValue tokens (.Err error)
  | literalError {depth : Nat} {keyword : Token} {tokens rest : Tokens} {property : HeaderIri}
      {error : functional_literals.SourceLiteralError}
      (propertyRun : DataPropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (literal : Rowl.FunctionalLiterals.Run rows source eof limit limit rest (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword .DataValue tokens (.Err (.Literal error))
  | dataValueCloseError {depth : Nat} {keyword : Token} {tokens rest after : Tokens} {property : HeaderIri}
      {value : functional_literals.SourceLiteral} {error : ClassError}
      (propertyRun : DataPropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (literalRun : Rowl.FunctionalLiterals.Run rows source eof limit limit rest (.Ok (value,after)))
      (failure : TakeRun eof .Close after (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword .DataValue tokens (.Err error)
  | dataHasValue {depth : Nat} {keyword close : Token} {tokens rest after remaining : Tokens} {property : HeaderIri}
      {value : functional_literals.SourceLiteral}
      (propertyRun : DataPropertyRun rows source eof limit tokens (.Ok (property,rest)))
      (literalRun : Rowl.FunctionalLiterals.Run rows source eof limit limit rest (.Ok (value,after)))
      (closing : TakeRun eof .Close after (.Ok (close,remaining))) :
      ConnectiveRun rows source eof count limit depth keyword .DataValue tokens
        (.Ok (.DataHasValue keyword property value,remaining))
  | dataNumberError {depth : Nat} {keyword : Token} {bound : Bound} {tokens : Tokens} {error : ClassError}
      (failure : TakeRun eof .Number tokens (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.DataCardinality bound) tokens (.Err error)
  | dataCountError {depth : Nat} {keyword number : Token} {bound : Bound} {tokens rest : Tokens}
      (taken : TakeRun eof .Number tokens (.Ok (number,rest)))
      (excess : ∀ value, ¬ Rowl.Decimal.Bounded source number.start.val number.end.val count value) :
      ConnectiveRun rows source eof count limit depth keyword (.DataCardinality bound) tokens
        (.Err (.CountLimit number.start))
  | dataCountPropertyError {depth : Nat} {keyword number : Token} {bound : Bound} {tokens rest : Tokens}
      {value : Usize} {error : ClassError}
      (taken : TakeRun eof .Number tokens (.Ok (number,rest)))
      (counted : Rowl.Decimal.Bounded source number.start.val number.end.val count value.val)
      (property : DataPropertyRun rows source eof limit rest (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.DataCardinality bound) tokens (.Err error)
  | optionalRangeError {depth : Nat} {keyword number : Token} {bound : Bound} {tokens rest after : Tokens}
      {value : Usize} {property : HeaderIri} {error : functional_ranges.RangeError}
      (taken : TakeRun eof .Number tokens (.Ok (number,rest)))
      (counted : Rowl.Decimal.Bounded source number.start.val number.end.val count value.val)
      (propertyRun : DataPropertyRun rows source eof limit rest (.Ok (property,after)))
      (range : Rowl.FunctionalRanges.OptionalRun rows source eof count limit depth after (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.DataCardinality bound) tokens (.Err (.Range error))
  | dataCountCloseError {depth : Nat} {keyword number : Token} {bound : Bound} {tokens rest after last : Tokens}
      {value : Usize} {property : HeaderIri} {range : Option functional_ranges.SourceDataRange} {error : ClassError}
      (taken : TakeRun eof .Number tokens (.Ok (number,rest)))
      (counted : Rowl.Decimal.Bounded source number.start.val number.end.val count value.val)
      (propertyRun : DataPropertyRun rows source eof limit rest (.Ok (property,after)))
      (rangeRun : Rowl.FunctionalRanges.OptionalRun rows source eof count limit depth after (.Ok (range,last)))
      (failure : TakeRun eof .Close last (.Err error)) :
      ConnectiveRun rows source eof count limit depth keyword (.DataCardinality bound) tokens (.Err error)
  | dataCardinality {depth : Nat} {keyword number close : Token} {bound : Bound}
      {tokens rest after last remaining : Tokens} {value : Usize} {property : HeaderIri}
      {range : Option functional_ranges.SourceDataRange}
      (taken : TakeRun eof .Number tokens (.Ok (number,rest)))
      (counted : Rowl.Decimal.Bounded source number.start.val number.end.val count value.val)
      (propertyRun : DataPropertyRun rows source eof limit rest (.Ok (property,after)))
      (rangeRun : Rowl.FunctionalRanges.OptionalRun rows source eof count limit depth after (.Ok (range,last)))
      (closing : TakeRun eof .Close last (.Ok (close,remaining))) :
      ConnectiveRun rows source eof count limit depth keyword (.DataCardinality bound) tokens
        (.Ok (.DataCardinality keyword bound number value property range,remaining))
/-- Independent maximal member sequence: it stops before `)` or at the end;
    otherwise the member count is checked, then one class expression is read and
    appended in source order. -/
inductive MembersRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Nat → List SourceClass → Tokens → core.result.Result (alloc.vec.Vec SourceClass × Tokens) ClassError → Prop
  | empty {depth : Nat} {prior : List SourceClass} {records : alloc.vec.Vec SourceClass} (contents : records.val = prior) :
      MembersRun rows source eof count limit depth prior .Empty (.Ok (records,.Empty))
  | stop {depth : Nat} {prior : List SourceClass} {token : Token} {tail : Tokens} {records : alloc.vec.Vec SourceClass}
      (close : token.terminal = .Close) (contents : records.val = prior) :
      MembersRun rows source eof count limit depth prior (.Cons token tail) (.Ok (records,.Cons token tail))
  | countLimit {depth : Nat} {prior : List SourceClass} {token : Token} {tail : Tokens}
      (notClose : token.terminal ≠ .Close) (full : count ≤ prior.length) :
      MembersRun rows source eof count limit depth prior (.Cons token tail) (.Err (.CountLimit token.start))
  | memberError {depth : Nat} {prior : List SourceClass} {token : Token} {tail : Tokens} {error : ClassError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (member : ClassRun rows source eof count limit depth (.Cons token tail) (.Err error)) :
      MembersRun rows source eof count limit depth prior (.Cons token tail) (.Err error)
  | member {depth : Nat} {prior : List SourceClass} {token : Token} {tail rest : Tokens} {item : SourceClass}
      {result : core.result.Result (alloc.vec.Vec SourceClass × Tokens) ClassError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (memberRun : ClassRun rows source eof count limit depth (.Cons token tail) (.Ok (item,rest)))
      (later : MembersRun rows source eof count limit depth (prior++[item]) rest result) :
      MembersRun rows source eof count limit depth prior (.Cons token tail) result
/-- Independent optional filler of a number restriction: none before `)` or at
    the end, and otherwise one class expression. -/
inductive FillerRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Nat → Tokens → core.result.Result (Option SourceClass × Tokens) ClassError → Prop
  | empty {depth : Nat} : FillerRun rows source eof count limit depth .Empty (.Ok (none,.Empty))
  | stop {depth : Nat} {token : Token} {tail : Tokens} (close : token.terminal = .Close) :
      FillerRun rows source eof count limit depth (.Cons token tail) (.Ok (none,.Cons token tail))
  | fillerError {depth : Nat} {token : Token} {tail : Tokens} {error : ClassError}
      (notClose : token.terminal ≠ .Close)
      (filler : ClassRun rows source eof count limit depth (.Cons token tail) (.Err error)) :
      FillerRun rows source eof count limit depth (.Cons token tail) (.Err error)
  | filler {depth : Nat} {token : Token} {tail rest : Tokens} {value : SourceClass}
      (notClose : token.terminal ≠ .Close)
      (fillerRun : ClassRun rows source eof count limit depth (.Cons token tail) (.Ok (value,rest))) :
      FillerRun rows source eof count limit depth (.Cons token tail) (.Ok (some value,rest))
end

mutual
/-- The actual recursive class reader terminates on every token stream, follows
    the independent grammar, and consumes at least one token on success. -/
theorem read_class_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (depth : Usize) (limits : ClassLimits) :
    ∃ result, read_class table bytes tokens depth limits = .ok result ∧
      ClassRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val depth.val tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest < TokenCount tokens := by
  cases tokens with
  | Empty =>
    exact ⟨.Err (.Expected .Class bytes.len),by rw [read_class.eq_def],.empty,by intro value rest impossible; cases impossible⟩
  | Cons token tail =>
    rw [read_class.eq_def]
    simp only [class_keyword_total_correct,bind_ok]
    cases keyword : KeywordOf token.terminal with
    | Other =>
      obtain ⟨resolved,resolveRead,resolveCorrect⟩ := resolve_total_correct table bytes token .Class limits.iri
      cases resolved with
      | Err error =>
        exact ⟨.Err error,by simp [resolveRead],.namedError keyword resolveCorrect,
          by intro value rest impossible; cases impossible⟩
      | Ok iri =>
        refine ⟨.Ok (.Named iri,tail),by simp [resolveRead],.named keyword resolveCorrect,?_⟩
        intro value rest same
        cases same
        simp [TokenCount]
    | Connective form =>
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
            read_connective_total_correct table bytes token form inner smaller limits
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
theorem read_connective_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (keyword : Token)
    (form : ClassForm) (tokens : Tokens) (depth : Usize) (limits : ClassLimits) :
    ∃ result, read_connective table bytes keyword form tokens depth limits = .ok result ∧
      ConnectiveRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val depth.val keyword form
        tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest < TokenCount tokens := by
  rw [read_connective.eq_def]
  cases form with
  | Junction conjunctive =>
    obtain ⟨members,membersRead,membersCorrect,membersProgress⟩ :=
      read_members_total_correct table bytes tokens (alloc.vec.Vec.new SourceClass) depth limits
    have start : (alloc.vec.Vec.new SourceClass).val = [] := rfl
    rw [start] at membersCorrect
    cases members with
    | Err error =>
      exact ⟨.Err error,by simp [membersRead],.membersError membersCorrect,by intro value rest impossible; cases impossible⟩
    | Ok pair =>
      obtain ⟨list,rest⟩ := pair
      by_cases few : list.val.length < 2
      · refine ⟨.Err (.Expected .Class (Position bytes.len rest)),?_,.tooFew membersCorrect few,
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
    obtain ⟨operand,operandRead,operandCorrect,operandProgress⟩ := read_class_total_correct table bytes tokens depth limits
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
  | Restriction existential =>
    obtain ⟨property,propertyRead,propertyCorrect⟩ :=
      read_object_property_total_correct table bytes tokens limits.iri
    cases property with
    | Err error =>
      exact ⟨.Err error,by simp [propertyRead],.propertyError propertyCorrect,by intro value rest impossible; cases impossible⟩
    | Ok pair =>
      obtain ⟨property,rest⟩ := pair
      have propertyStep := property_progress propertyCorrect
      obtain ⟨filler,fillerRead,fillerCorrect,fillerProgress⟩ := read_class_total_correct table bytes rest depth limits
      cases filler with
      | Err error =>
        exact ⟨.Err error,by simp [propertyRead,fillerRead],.fillerError propertyCorrect fillerCorrect,
          by intro value rest impossible; cases impossible⟩
      | Ok pair =>
        obtain ⟨filler,after⟩ := pair
        obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct after .Close bytes.len
        cases closed with
        | Err error =>
          exact ⟨.Err error,by simp [propertyRead,fillerRead,closeRead],
            .restrictionCloseError propertyCorrect fillerCorrect closeCorrect,by intro value rest impossible; cases impossible⟩
        | Ok pair =>
          obtain ⟨close,remaining⟩ := pair
          refine ⟨.Ok (if existential then .SomeValuesFrom keyword property filler
              else .AllValuesFrom keyword property filler,remaining),?_,
            .restriction propertyCorrect fillerCorrect closeCorrect,?_⟩
          · cases existential <;> simp [propertyRead,fillerRead,closeRead]
          · intro value rest' same
            have one := fillerProgress filler after rfl
            have two := take_progress closeCorrect
            cases same
            try simp only [TokenCount] at *
            omega
  | OneOf =>
    obtain ⟨list,listRead,listCorrect,listProgress⟩ :=
      Rowl.FunctionalIndividuals.read_individual_list_total_correct table bytes tokens 1#usize limits.count limits.iri
    have one : (1#usize).val = 1 := rfl
    rw [one] at listCorrect
    cases list with
    | Err error =>
      exact ⟨.Err (.Individual error),by simp [listRead],.oneOfError listCorrect,
        by intro value rest impossible; cases impossible⟩
    | Ok pair =>
      obtain ⟨members,rest⟩ := pair
      obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
      cases closed with
      | Err error =>
        exact ⟨.Err error,by simp [listRead,closeRead],.oneOfCloseError listCorrect closeCorrect,
          by intro value rest impossible; cases impossible⟩
      | Ok pair =>
        obtain ⟨close,remaining⟩ := pair
        refine ⟨.Ok (.OneOf keyword members,remaining),by simp [listRead,closeRead],
          .oneOf listCorrect closeCorrect,?_⟩
        intro value rest' same
        have scanned := listProgress members rest rfl
        have closed := take_progress closeCorrect
        cases same
        omega
  | HasValue =>
    obtain ⟨property,propertyRead,propertyCorrect⟩ :=
      read_object_property_total_correct table bytes tokens limits.iri
    cases property with
    | Err error =>
      exact ⟨.Err error,by simp [propertyRead],.valuePropertyError propertyCorrect,
        by intro value rest impossible; cases impossible⟩
    | Ok pair =>
      obtain ⟨property,rest⟩ := pair
      have propertyStep := property_progress propertyCorrect
      obtain ⟨individual,individualRead,individualCorrect⟩ :=
        Rowl.FunctionalIndividuals.read_individual_total_correct table bytes rest limits.iri
      cases individual with
      | Err error =>
        exact ⟨.Err (.Individual error),by simp [propertyRead,individualRead],
          .valueError propertyCorrect individualCorrect,by intro value rest impossible; cases impossible⟩
      | Ok pair =>
        obtain ⟨individual,after⟩ := pair
        have individualStep := Rowl.FunctionalIndividuals.individual_progress individualCorrect
        obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct after .Close bytes.len
        cases closed with
        | Err error =>
          exact ⟨.Err error,by simp [propertyRead,individualRead,closeRead],
            .valueCloseError propertyCorrect individualCorrect closeCorrect,
            by intro value rest impossible; cases impossible⟩
        | Ok pair =>
          obtain ⟨close,remaining⟩ := pair
          refine ⟨.Ok (.HasValue keyword property individual,remaining),
            by simp [propertyRead,individualRead,closeRead],.hasValue propertyCorrect individualCorrect closeCorrect,?_⟩
          intro value rest' same
          have closed := take_progress closeCorrect
          cases same
          omega
  | SelfRestriction =>
    obtain ⟨property,propertyRead,propertyCorrect⟩ :=
      read_object_property_total_correct table bytes tokens limits.iri
    cases property with
    | Err error =>
      exact ⟨.Err error,by simp [propertyRead],.selfPropertyError propertyCorrect,
        by intro value rest impossible; cases impossible⟩
    | Ok pair =>
      obtain ⟨property,rest⟩ := pair
      have propertyStep := property_progress propertyCorrect
      obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
      cases closed with
      | Err error =>
        exact ⟨.Err error,by simp [propertyRead,closeRead],.selfCloseError propertyCorrect closeCorrect,
          by intro value rest impossible; cases impossible⟩
      | Ok pair =>
        obtain ⟨close,remaining⟩ := pair
        refine ⟨.Ok (.HasSelf keyword property,remaining),by simp [propertyRead,closeRead],
          .hasSelf propertyCorrect closeCorrect,?_⟩
        intro value rest' same
        have closed := take_progress closeCorrect
        cases same
        omega
  | Cardinality bound =>
    obtain ⟨taken,takenRead,takenCorrect⟩ := take_expected_total_correct tokens .Number bytes.len
    cases taken with
    | Err error =>
      exact ⟨.Err error,by simp [takenRead],.numberError takenCorrect,by intro value rest impossible; cases impossible⟩
    | Ok pair =>
      obtain ⟨number,rest⟩ := pair
      have numberStep := take_progress takenCorrect
      obtain ⟨counted,countRead,countCorrect⟩ :=
        Rowl.Decimal.read_bounded_total_correct bytes number.start number.end limits.count
      cases counted with
      | none =>
        have excess := (Rowl.Decimal.read_bounded_none_iff bytes number.start number.end limits.count).mp countRead
        exact ⟨.Err (.CountLimit number.start),by simp [takenRead,countRead],.countError takenCorrect excess,
          by intro value rest impossible; cases impossible⟩
      | some value =>
        have bounded := (countCorrect value).mp rfl
        obtain ⟨property,propertyRead,propertyCorrect⟩ :=
          read_object_property_total_correct table bytes rest limits.iri
        cases property with
        | Err error =>
          exact ⟨.Err error,by simp [takenRead,countRead,propertyRead],
            .countPropertyError takenCorrect bounded propertyCorrect,by intro value rest impossible; cases impossible⟩
        | Ok pair =>
          obtain ⟨property,after⟩ := pair
          have propertyStep := property_progress propertyCorrect
          obtain ⟨filled,fillerRead,fillerCorrect,fillerProgress⟩ :=
            read_filler_total_correct table bytes after depth limits
          cases filled with
          | Err error =>
            exact ⟨.Err error,by simp [takenRead,countRead,propertyRead,fillerRead],
              .countFillerError takenCorrect bounded propertyCorrect fillerCorrect,
              by intro value rest impossible; cases impossible⟩
          | Ok pair =>
            obtain ⟨filler,last⟩ := pair
            have fillerStep := fillerProgress filler last rfl
            obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct last .Close bytes.len
            cases closed with
            | Err error =>
              exact ⟨.Err error,by simp [takenRead,countRead,propertyRead,fillerRead,closeRead],
                .countCloseError takenCorrect bounded propertyCorrect fillerCorrect closeCorrect,
                by intro value rest impossible; cases impossible⟩
            | Ok pair =>
              obtain ⟨close,remaining⟩ := pair
              refine ⟨.Ok (.Cardinality keyword bound number value property filler,remaining),
                by simp [takenRead,countRead,propertyRead,fillerRead,closeRead],
                .cardinality takenCorrect bounded propertyCorrect fillerCorrect closeCorrect,?_⟩
              intro value' rest' same
              have closed := take_progress closeCorrect
              cases same
              try simp only [TokenCount] at *
              omega
  | DataRestriction existential =>
    obtain ⟨property,propertyRead,propertyCorrect⟩ := read_data_property_total_correct table bytes tokens limits.iri
    cases property with
    | Err error =>
      exact ⟨.Err error,by simp [propertyRead],.dataPropertyError propertyCorrect,
        by intro value rest impossible; cases impossible⟩
    | Ok pair =>
      obtain ⟨property,rest⟩ := pair
      have propertyStep := data_property_progress propertyCorrect
      obtain ⟨range,rangeRead,rangeCorrect,rangeProgress⟩ :=
        Rowl.FunctionalRanges.read_data_range_total_correct table bytes rest depth limits.count limits.iri
      cases range with
      | Err error =>
        exact ⟨.Err (.Range error),by simp [propertyRead,rangeRead],.rangeError propertyCorrect rangeCorrect,
          by intro value rest impossible; cases impossible⟩
      | Ok pair =>
        obtain ⟨range,after⟩ := pair
        have rangeStep := rangeProgress range after rfl
        obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct after .Close bytes.len
        cases closed with
        | Err error =>
          exact ⟨.Err error,by simp [propertyRead,rangeRead,closeRead],
            .dataCloseError propertyCorrect rangeCorrect closeCorrect,by intro value rest impossible; cases impossible⟩
        | Ok pair =>
          obtain ⟨close,remaining⟩ := pair
          refine ⟨.Ok (if existential then .DataSomeValuesFrom keyword property range
              else .DataAllValuesFrom keyword property range,remaining),?_,
            .dataRestriction propertyCorrect rangeCorrect closeCorrect,?_⟩
          · cases existential <;> simp [propertyRead,rangeRead,closeRead]
          · intro value rest' same
            have two := take_progress closeCorrect
            cases same
            try simp only [TokenCount] at *
            omega
  | DataValue =>
    obtain ⟨property,propertyRead,propertyCorrect⟩ := read_data_property_total_correct table bytes tokens limits.iri
    cases property with
    | Err error =>
      exact ⟨.Err error,by simp [propertyRead],.dataValuePropertyError propertyCorrect,
        by intro value rest impossible; cases impossible⟩
    | Ok pair =>
      obtain ⟨property,rest⟩ := pair
      have propertyStep := data_property_progress propertyCorrect
      obtain ⟨literal,literalRead,literalCorrect⟩ :=
        Rowl.FunctionalLiterals.read_literal_total_correct table bytes rest limits.iri limits.iri
      cases literal with
      | Err error =>
        exact ⟨.Err (.Literal error),by simp [propertyRead,literalRead],.literalError propertyCorrect literalCorrect,
          by intro value rest impossible; cases impossible⟩
      | Ok pair =>
        obtain ⟨value,after⟩ := pair
        have literalStep := (Rowl.FunctionalLiterals.literal_token_progress table bytes _ limits.iri limits.iri
          value after literalRead).2
        obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct after .Close bytes.len
        cases closed with
        | Err error =>
          exact ⟨.Err error,by simp [propertyRead,literalRead,closeRead],
            .dataValueCloseError propertyCorrect literalCorrect closeCorrect,
            by intro value rest impossible; cases impossible⟩
        | Ok pair =>
          obtain ⟨close,remaining⟩ := pair
          refine ⟨.Ok (.DataHasValue keyword property value,remaining),by simp [propertyRead,literalRead,closeRead],
            .dataHasValue propertyCorrect literalCorrect closeCorrect,?_⟩
          intro value' rest' same
          have two := take_progress closeCorrect
          cases same
          try simp only [TokenCount] at *
          omega
  | DataCardinality bound =>
    obtain ⟨taken,takenRead,takenCorrect⟩ := take_expected_total_correct tokens .Number bytes.len
    cases taken with
    | Err error =>
      exact ⟨.Err error,by simp [takenRead],.dataNumberError takenCorrect,by intro value rest impossible; cases impossible⟩
    | Ok pair =>
      obtain ⟨number,rest⟩ := pair
      have numberStep := take_progress takenCorrect
      obtain ⟨counted,countRead,countCorrect⟩ :=
        Rowl.Decimal.read_bounded_total_correct bytes number.start number.end limits.count
      cases counted with
      | none =>
        have excess := (Rowl.Decimal.read_bounded_none_iff bytes number.start number.end limits.count).mp countRead
        exact ⟨.Err (.CountLimit number.start),by simp [takenRead,countRead],.dataCountError takenCorrect excess,
          by intro value rest impossible; cases impossible⟩
      | some value =>
        have bounded := (countCorrect value).mp rfl
        obtain ⟨property,propertyRead,propertyCorrect⟩ := read_data_property_total_correct table bytes rest limits.iri
        cases property with
        | Err error =>
          exact ⟨.Err error,by simp [takenRead,countRead,propertyRead],
            .dataCountPropertyError takenCorrect bounded propertyCorrect,by intro value rest impossible; cases impossible⟩
        | Ok pair =>
          obtain ⟨property,after⟩ := pair
          have propertyStep := data_property_progress propertyCorrect
          obtain ⟨range,rangeRead,rangeCorrect,rangeProgress⟩ :=
            Rowl.FunctionalRanges.read_optional_range_total_correct table bytes after depth limits.count limits.iri
          cases range with
          | Err error =>
            exact ⟨.Err (.Range error),by simp [takenRead,countRead,propertyRead,rangeRead],
              .optionalRangeError takenCorrect bounded propertyCorrect rangeCorrect,
              by intro value rest impossible; cases impossible⟩
          | Ok pair =>
            obtain ⟨range,last⟩ := pair
            have rangeStep := rangeProgress range last rfl
            obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct last .Close bytes.len
            cases closed with
            | Err error =>
              exact ⟨.Err error,by simp [takenRead,countRead,propertyRead,rangeRead,closeRead],
                .dataCountCloseError takenCorrect bounded propertyCorrect rangeCorrect closeCorrect,
                by intro value rest impossible; cases impossible⟩
            | Ok pair =>
              obtain ⟨close,remaining⟩ := pair
              refine ⟨.Ok (.DataCardinality keyword bound number value property range,remaining),
                by simp [takenRead,countRead,propertyRead,rangeRead,closeRead],
                .dataCardinality takenCorrect bounded propertyCorrect rangeCorrect closeCorrect,?_⟩
              intro value' rest' same
              have closed := take_progress closeCorrect
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
    (members : alloc.vec.Vec SourceClass) (depth : Usize) (limits : ClassLimits) :
    ∃ result, read_members table bytes tokens members depth limits = .ok result ∧
      MembersRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val depth.val members.val
        tokens result ∧
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
    · by_cases full : limits.count.val ≤ members.val.length
      · refine ⟨.Err (.CountLimit token.start),?_,.countLimit close full,by intro value rest impossible; cases impossible⟩
        simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full]
      · have room : members.val.length < limits.count.val := by omega
        obtain ⟨member,memberRead,memberCorrect,memberProgress⟩ :=
          read_class_total_correct table bytes (.Cons token tail) depth limits
        cases member with
        | Err error =>
          refine ⟨.Err error,?_,.memberError close room memberCorrect,by intro value rest impossible; cases impossible⟩
          simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,memberRead]
        | Ok pair =>
          obtain ⟨member,rest⟩ := pair
          have memberStep := memberProgress member rest rfl
          obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec members member (by scalar_tac))
          obtain ⟨result,executed,correct,progress⟩ :=
            read_members_total_correct table bytes rest appended depth limits
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

/-- The actual optional filler terminates, follows the independent grammar, and
    never returns more tokens than it received. -/
theorem read_filler_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (depth : Usize) (limits : ClassLimits) :
    ∃ result, read_filler table bytes tokens depth limits = .ok result ∧
      FillerRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val depth.val tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest ≤ TokenCount tokens := by
  rw [read_filler.eq_def]
  cases tokens with
  | Empty => exact ⟨.Ok (none,.Empty),rfl,.empty,by intro value rest same; cases same; simp⟩
  | Cons token tail =>
    simp only [closes_total_correct,bind_ok]
    by_cases close : token.terminal = .Close
    · refine ⟨.Ok (none,.Cons token tail),by simp [close],.stop close,?_⟩
      intro value rest same
      cases same
      simp
    · obtain ⟨filled,fillerRead,fillerCorrect,fillerProgress⟩ :=
        read_class_total_correct table bytes (.Cons token tail) depth limits
      cases filled with
      | Err error =>
        exact ⟨.Err error,by simp [close,fillerRead],.fillerError close fillerCorrect,
          by intro value rest impossible; cases impossible⟩
      | Ok pair =>
        obtain ⟨filler,rest⟩ := pair
        refine ⟨.Ok (some filler,rest),by simp [close,fillerRead],.filler close fillerCorrect,?_⟩
        intro value rest' same
        have step := fillerProgress filler rest rfl
        cases same
        omega
termination_by (TokenCount tokens,3)
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
/-- Every independent class derivation is the actual result. -/
theorem class_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (limits : ClassLimits)
    (depth : Usize) {d : Nat} (same : depth.val = d) {tokens : Tokens}
    {result : core.result.Result (SourceClass × Tokens) ClassError}
    (run : ClassRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val d tokens result) :
    read_class table bytes tokens depth limits = .ok result := by
  cases run with
  | empty => rw [read_class.eq_def]
  | namedError other resolved =>
    rw [read_class.eq_def]
    simp [class_keyword_total_correct,other,(resolve_result_iff table bytes _ .Class limits.iri _).mpr resolved]
  | named other resolved =>
    rw [read_class.eq_def]
    simp [class_keyword_total_correct,other,(resolve_result_iff table bytes _ .Class limits.iri _).mpr resolved]
  | depthLimit keyword =>
    rw [read_class.eq_def]
    simp [class_keyword_total_correct,keyword,UScalar.eq_equiv,same]
  | openError keyword failure =>
    rw [read_class.eq_def]
    simp [class_keyword_total_correct,keyword,UScalar.eq_equiv,same,
      (take_expected_result_iff _ .Open bytes.len _).mpr failure]
  | connective keyword opened body =>
    have positive : depth.val ≠ 0 := by omega
    obtain ⟨smaller,subExecuted,subValue⟩ :=
      WP.spec_imp_exists (Usize.sub_spec (x := depth) (y := 1#usize) (by scalar_tac))
    have one : (1#usize).val = 1 := rfl
    have bodyRead := connective_execution table bytes limits _ _ smaller (by omega) body
    rw [read_class.eq_def]
    simp [class_keyword_total_correct,keyword,UScalar.eq_equiv,positive,
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
theorem connective_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (limits : ClassLimits)
    (keyword : Token) (form : ClassForm) (depth : Usize) {d : Nat} (same : depth.val = d) {tokens : Tokens}
    {result : core.result.Result (SourceClass × Tokens) ClassError}
    (run : ConnectiveRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val d keyword form
      tokens result) :
    read_connective table bytes keyword form tokens depth limits = .ok result := by
  have start : (alloc.vec.Vec.new SourceClass).val = [] := rfl
  cases run with
  | membersError members =>
    have membersRead := members_execution table bytes limits depth same (alloc.vec.Vec.new SourceClass) start members
    rw [read_connective.eq_def]
    simp [membersRead]
  | tooFew members few =>
    have membersRead := members_execution table bytes limits depth same (alloc.vec.Vec.new SourceClass) start members
    rw [read_connective.eq_def]
    simp [membersRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,Nat.lt_succ_iff.mp few,offset_of_total_correct]
  | junctionCloseError members enough failure =>
    have membersRead := members_execution table bytes limits depth same (alloc.vec.Vec.new SourceClass) start members
    rw [read_connective.eq_def]
    simp [membersRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,Nat.not_lt.mpr enough,Nat.not_le.mpr enough,
      (take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | junction members enough closing =>
    have membersRead := members_execution table bytes limits depth same (alloc.vec.Vec.new SourceClass) start members
    rw [read_connective.eq_def]
    cases ‹Bool› <;>
      simp [membersRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,Nat.not_lt.mpr enough,Nat.not_le.mpr enough,
        (take_expected_result_iff _ .Close bytes.len _).mpr closing]
  | operandError operand =>
    have operandRead := class_execution table bytes limits depth same operand
    rw [read_connective.eq_def]
    simp [operandRead]
  | complementCloseError operandRun failure =>
    have operandRead := class_execution table bytes limits depth same operandRun
    rw [read_connective.eq_def]
    simp [operandRead,(take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | complement operandRun closing =>
    have operandRead := class_execution table bytes limits depth same operandRun
    rw [read_connective.eq_def]
    simp [operandRead,(take_expected_result_iff _ .Close bytes.len _).mpr closing]
  | propertyError property =>
    rw [read_connective.eq_def]
    simp [(read_object_property_result_iff table bytes _ limits.iri _).mpr property]
  | fillerError propertyRun filler =>
    have step := property_progress propertyRun
    have fillerRead := class_execution table bytes limits depth same filler
    rw [read_connective.eq_def]
    simp [(read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,fillerRead]
  | restrictionCloseError propertyRun fillerRun failure =>
    have step := property_progress propertyRun
    have fillerRead := class_execution table bytes limits depth same fillerRun
    rw [read_connective.eq_def]
    simp [(read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,fillerRead,
      (take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | restriction propertyRun fillerRun closing =>
    have step := property_progress propertyRun
    have fillerRead := class_execution table bytes limits depth same fillerRun
    rw [read_connective.eq_def]
    cases ‹Bool› <;>
      simp [(read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,fillerRead,
        (take_expected_result_iff _ .Close bytes.len _).mpr closing]
  | oneOfError list =>
    have listRead :=
      (Rowl.FunctionalIndividuals.read_individual_list_result_iff table bytes _ 1#usize limits.count limits.iri _).mpr list
    rw [read_connective.eq_def]
    simp [listRead]
  | oneOfCloseError list failure =>
    have listRead :=
      (Rowl.FunctionalIndividuals.read_individual_list_result_iff table bytes _ 1#usize limits.count limits.iri _).mpr list
    rw [read_connective.eq_def]
    simp [listRead,(take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | oneOf list closing =>
    have listRead :=
      (Rowl.FunctionalIndividuals.read_individual_list_result_iff table bytes _ 1#usize limits.count limits.iri _).mpr list
    rw [read_connective.eq_def]
    simp [listRead,(take_expected_result_iff _ .Close bytes.len _).mpr closing]
  | valuePropertyError property =>
    rw [read_connective.eq_def]
    simp [(read_object_property_result_iff table bytes _ limits.iri _).mpr property]
  | valueError propertyRun failure =>
    rw [read_connective.eq_def]
    simp [(read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
      (Rowl.FunctionalIndividuals.read_individual_result_iff table bytes _ limits.iri _).mpr failure]
  | valueCloseError propertyRun valueRun failure =>
    rw [read_connective.eq_def]
    simp [(read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
      (Rowl.FunctionalIndividuals.read_individual_result_iff table bytes _ limits.iri _).mpr valueRun,
      (take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | hasValue propertyRun valueRun closing =>
    rw [read_connective.eq_def]
    simp [(read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
      (Rowl.FunctionalIndividuals.read_individual_result_iff table bytes _ limits.iri _).mpr valueRun,
      (take_expected_result_iff _ .Close bytes.len _).mpr closing]
  | selfPropertyError property =>
    rw [read_connective.eq_def]
    simp [(read_object_property_result_iff table bytes _ limits.iri _).mpr property]
  | selfCloseError propertyRun failure =>
    rw [read_connective.eq_def]
    simp [(read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
      (take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | hasSelf propertyRun closing =>
    rw [read_connective.eq_def]
    simp [(read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
      (take_expected_result_iff _ .Close bytes.len _).mpr closing]
  | numberError failure =>
    rw [read_connective.eq_def]
    simp [(take_expected_result_iff _ .Number bytes.len _).mpr failure]
  | countError taken excess =>
    rw [read_connective.eq_def]
    simp [(take_expected_result_iff _ .Number bytes.len _).mpr taken,
      (Rowl.Decimal.read_bounded_none_iff bytes _ _ limits.count).mpr excess]
  | countPropertyError taken counted property =>
    rw [read_connective.eq_def]
    simp [(take_expected_result_iff _ .Number bytes.len _).mpr taken,
      (Rowl.Decimal.read_bounded_some_iff bytes _ _ limits.count _).mpr counted,
      (read_object_property_result_iff table bytes _ limits.iri _).mpr property]
  | countFillerError taken counted propertyRun filler =>
    have numberStep := take_progress taken
    have propertyStep := property_progress propertyRun
    have fillerRead := filler_execution table bytes limits depth same filler
    rw [read_connective.eq_def]
    simp [(take_expected_result_iff _ .Number bytes.len _).mpr taken,
      (Rowl.Decimal.read_bounded_some_iff bytes _ _ limits.count _).mpr counted,
      (read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,fillerRead]
  | countCloseError taken counted propertyRun fillerRun failure =>
    have numberStep := take_progress taken
    have propertyStep := property_progress propertyRun
    have fillerRead := filler_execution table bytes limits depth same fillerRun
    rw [read_connective.eq_def]
    simp [(take_expected_result_iff _ .Number bytes.len _).mpr taken,
      (Rowl.Decimal.read_bounded_some_iff bytes _ _ limits.count _).mpr counted,
      (read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,fillerRead,
      (take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | cardinality taken counted propertyRun fillerRun closing =>
    have numberStep := take_progress taken
    have propertyStep := property_progress propertyRun
    have fillerRead := filler_execution table bytes limits depth same fillerRun
    rw [read_connective.eq_def]
    simp [(take_expected_result_iff _ .Number bytes.len _).mpr taken,
      (Rowl.Decimal.read_bounded_some_iff bytes _ _ limits.count _).mpr counted,
      (read_object_property_result_iff table bytes _ limits.iri _).mpr propertyRun,fillerRead,
      (take_expected_result_iff _ .Close bytes.len _).mpr closing]
  | dataPropertyError property =>
    rw [read_connective.eq_def]
    simp [(read_data_property_result_iff table bytes _ limits.iri _).mpr property]
  | rangeError propertyRun range =>
    rw [read_connective.eq_def]
    simp [(read_data_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
      (Rowl.FunctionalRanges.read_data_range_result_iff table bytes _ depth limits.count limits.iri _).mpr
        (by rw [same]; exact range)]
  | dataCloseError propertyRun rangeRun failure =>
    rw [read_connective.eq_def]
    simp [(read_data_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
      (Rowl.FunctionalRanges.read_data_range_result_iff table bytes _ depth limits.count limits.iri _).mpr
        (by rw [same]; exact rangeRun),
      (take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | dataRestriction propertyRun rangeRun closing =>
    rw [read_connective.eq_def]
    cases ‹Bool› <;>
      simp [(read_data_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
        (Rowl.FunctionalRanges.read_data_range_result_iff table bytes _ depth limits.count limits.iri _).mpr
          (by rw [same]; exact rangeRun),
        (take_expected_result_iff _ .Close bytes.len _).mpr closing]
  | dataValuePropertyError property =>
    rw [read_connective.eq_def]
    simp [(read_data_property_result_iff table bytes _ limits.iri _).mpr property]
  | literalError propertyRun literal =>
    rw [read_connective.eq_def]
    simp [(read_data_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
      (Rowl.FunctionalLiterals.read_literal_result_iff table bytes _ limits.iri limits.iri _).mpr literal]
  | dataValueCloseError propertyRun literalRun failure =>
    rw [read_connective.eq_def]
    simp [(read_data_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
      (Rowl.FunctionalLiterals.read_literal_result_iff table bytes _ limits.iri limits.iri _).mpr literalRun,
      (take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | dataHasValue propertyRun literalRun closing =>
    rw [read_connective.eq_def]
    simp [(read_data_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
      (Rowl.FunctionalLiterals.read_literal_result_iff table bytes _ limits.iri limits.iri _).mpr literalRun,
      (take_expected_result_iff _ .Close bytes.len _).mpr closing]
  | dataNumberError failure =>
    rw [read_connective.eq_def]
    simp [(take_expected_result_iff _ .Number bytes.len _).mpr failure]
  | dataCountError taken excess =>
    rw [read_connective.eq_def]
    simp [(take_expected_result_iff _ .Number bytes.len _).mpr taken,
      (Rowl.Decimal.read_bounded_none_iff bytes _ _ limits.count).mpr excess]
  | dataCountPropertyError taken counted property =>
    rw [read_connective.eq_def]
    simp [(take_expected_result_iff _ .Number bytes.len _).mpr taken,
      (Rowl.Decimal.read_bounded_some_iff bytes _ _ limits.count _).mpr counted,
      (read_data_property_result_iff table bytes _ limits.iri _).mpr property]
  | optionalRangeError taken counted propertyRun range =>
    rw [read_connective.eq_def]
    simp [(take_expected_result_iff _ .Number bytes.len _).mpr taken,
      (Rowl.Decimal.read_bounded_some_iff bytes _ _ limits.count _).mpr counted,
      (read_data_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
      (Rowl.FunctionalRanges.read_optional_range_result_iff table bytes _ depth limits.count limits.iri _).mpr
        (by rw [same]; exact range)]
  | dataCountCloseError taken counted propertyRun rangeRun failure =>
    rw [read_connective.eq_def]
    simp [(take_expected_result_iff _ .Number bytes.len _).mpr taken,
      (Rowl.Decimal.read_bounded_some_iff bytes _ _ limits.count _).mpr counted,
      (read_data_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
      (Rowl.FunctionalRanges.read_optional_range_result_iff table bytes _ depth limits.count limits.iri _).mpr
        (by rw [same]; exact rangeRun),
      (take_expected_result_iff _ .Close bytes.len _).mpr failure]
  | dataCardinality taken counted propertyRun rangeRun closing =>
    rw [read_connective.eq_def]
    simp [(take_expected_result_iff _ .Number bytes.len _).mpr taken,
      (Rowl.Decimal.read_bounded_some_iff bytes _ _ limits.count _).mpr counted,
      (read_data_property_result_iff table bytes _ limits.iri _).mpr propertyRun,
      (Rowl.FunctionalRanges.read_optional_range_result_iff table bytes _ depth limits.count limits.iri _).mpr
        (by rw [same]; exact rangeRun),
      (take_expected_result_iff _ .Close bytes.len _).mpr closing]
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
theorem members_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (limits : ClassLimits)
    (depth : Usize) {d : Nat} (same : depth.val = d) (members : alloc.vec.Vec SourceClass) {prior : List SourceClass}
    (contents : members.val = prior) {tokens : Tokens}
    {result : core.result.Result (alloc.vec.Vec SourceClass × Tokens) ClassError}
    (run : MembersRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val d prior tokens
      result) :
    read_members table bytes tokens members depth limits = .ok result := by
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
    have memberRead := class_execution table bytes limits depth same member
    rw [read_members.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,
      show ¬ limits.count.val ≤ prior.length by omega,memberRead]
  | member notClose room memberRun later =>
    have memberRead := class_execution table bytes limits depth same memberRun
    obtain ⟨actual,executed,_,progress⟩ := read_class_total_correct table bytes _ depth limits
    rw [memberRead] at executed
    have step := progress _ _ (Result.ok_injective executed).symm
    obtain ⟨appended,push,appendedContents⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.push_spec members _ (by rw [contents]; scalar_tac))
    have laterRead := members_execution table bytes limits depth same appended
      (by rw [appendedContents,contents]) later
    rw [read_members.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,
      show ¬ limits.count.val ≤ prior.length by omega,memberRead,push,laterRead]
termination_by (TokenCount tokens,1)
decreasing_by
  all_goals
    simp_wf
    try subst_vars
    try rw [Prod.lex_def]
    try simp only [TokenCount] at *
    try simp only [or_true]
    try omega

/-- Every independent optional-filler derivation is the actual result. -/
theorem filler_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (limits : ClassLimits)
    (depth : Usize) {d : Nat} (same : depth.val = d) {tokens : Tokens}
    {result : core.result.Result (Option SourceClass × Tokens) ClassError}
    (run : FillerRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val d tokens result) :
    read_filler table bytes tokens depth limits = .ok result := by
  cases run with
  | empty => rw [read_filler.eq_def]
  | stop close =>
    rw [read_filler.eq_def]
    simp [closes_total_correct,close]
  | fillerError notClose filler =>
    have fillerRead := class_execution table bytes limits depth same filler
    rw [read_filler.eq_def]
    simp [closes_total_correct,notClose,fillerRead]
  | filler notClose fillerRun =>
    have fillerRead := class_execution table bytes limits depth same fillerRun
    rw [read_filler.eq_def]
    simp [closes_total_correct,notClose,fillerRead]
termination_by (TokenCount tokens,3)
decreasing_by
  all_goals
    simp_wf
    try subst_vars
    try rw [Prod.lex_def]
    try simp only [TokenCount] at *
    try simp only [or_true]
    try omega
end

/-- Every exact class expression and first error is equivalent to its independent derivation. -/
theorem read_class_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (depth : Usize) (limits : ClassLimits) (result : core.result.Result (SourceClass × Tokens) ClassError) :
    read_class table bytes tokens depth limits = .ok result ↔
      ClassRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val depth.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct,_⟩ := read_class_total_correct table bytes tokens depth limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · exact class_execution table bytes limits depth rfl
/-- The public reader: every exact class expression and first error is
    equivalent to its independent derivation at the caller's nesting allowance. -/
theorem read_class_expression_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limits : ClassLimits) (result : core.result.Result (SourceClass × Tokens) ClassError) :
    read_class_expression table bytes tokens limits = .ok result ↔
      ClassRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val tokens
        result := by
  rw [read_class_expression]
  exact read_class_result_iff table bytes tokens limits.depth limits result
/-- Every exact member sequence and first error is equivalent to its independent derivation. -/
theorem read_members_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (members : alloc.vec.Vec SourceClass) (depth : Usize) (limits : ClassLimits)
    (result : core.result.Result (alloc.vec.Vec SourceClass × Tokens) ClassError) :
    read_members table bytes tokens members depth limits = .ok result ↔
      MembersRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val depth.val members.val
        tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct,_⟩ := read_members_total_correct table bytes tokens members depth limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · exact members_execution table bytes limits depth rfl members rfl
/-- A successful class expression consumes at least one token; a successful
    member sequence never consumes more than it is given. -/
theorem class_progress {table : prefixes.PrefixTable} {bytes : alloc.vec.Vec U8} {limits : ClassLimits} {level : Usize}
    {tokens rest : Tokens} {value : SourceClass}
    (accepted : read_class table bytes tokens level limits = .ok (.Ok (value,rest))) :
    TokenCount rest < TokenCount tokens := by
  obtain ⟨actual,executed,_,progress⟩ := read_class_total_correct table bytes tokens level limits
  rw [accepted] at executed
  exact progress value rest (Result.ok_injective executed).symm

/-- The public reader starts at the caller's nesting allowance. -/
theorem read_class_expression_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limits : ClassLimits) :
    ∃ result, read_class_expression table bytes tokens limits = .ok result ∧
      ClassRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val tokens result := by
  obtain ⟨result,executed,correct,_⟩ := read_class_total_correct table bytes tokens limits.depth limits
  exact ⟨result,by rw [read_class_expression]; exact executed,correct⟩
end Rowl.FunctionalClasses
