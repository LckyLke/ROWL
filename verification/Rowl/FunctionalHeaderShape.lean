import Rowl.FunctionalHeaderIdentity

namespace Rowl.FunctionalHeaderShape
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional_header RowlRust.functional_lexer RowlRust.functional
open Rowl.FunctionalHeaderIdentity
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-- Exact punctuation and full/abbreviated IRI alternatives in an import body. -/
def Expected : HeaderExpected → Terminal → Prop
  | .Open, terminal => terminal = .Open
  | .Iri, terminal => terminal = .FullIri ∨ terminal = .AbbreviatedIri
  | .Close, terminal => terminal = .Close
def Taken (tokens : Tokens) (expected : HeaderExpected) (token : Token) (rest : Tokens) : Prop :=
  tokens = .Cons token rest ∧ Expected expected token.terminal
/-- Independent first wrong/missing terminal; EOF is the original source length. -/
inductive Mismatch : List HeaderExpected → Tokens → Usize → HeaderError → Prop
  | empty (expected : HeaderExpected) (tail : List HeaderExpected) (eof : Usize) :
      Mismatch (expected::tail) .Empty eof (.Expected expected eof)
  | wrong (expected : HeaderExpected) (tail : List HeaderExpected) (token : Token) (rest : Tokens) (eof : Usize)
      (wrong : ¬ Expected expected token.terminal) :
      Mismatch (expected::tail) (.Cons token rest) eof (.Expected expected token.start)
  | later {expected : HeaderExpected} {tail : List HeaderExpected} {token : Token} {rest : Tokens}
      {eof : Usize} {error : HeaderError} (acceptedKind : Expected expected token.terminal)
      (failure : Mismatch tail rest eof error) : Mismatch (expected::tail) (.Cons token rest) eof error
def TakeCorrect (tokens : Tokens) (expected : HeaderExpected) (eof : Usize) :
    core.result.Result (Token × Tokens) HeaderError → Prop
  | .Ok (token,rest) => Taken tokens expected token rest
  | .Err error => Mismatch [expected] tokens eof error
/-- Complete three-token import body and its unchanged suffix. -/
def BodyShape (tokens : Tokens) (target : Token) (rest : Tokens) : Prop :=
  ∃ opening closing, tokens = .Cons opening (.Cons target (.Cons closing rest)) ∧
    Expected .Open opening.terminal ∧ Expected .Iri target.terminal ∧ Expected .Close closing.terminal
def ShapeCorrect (tokens : Tokens) (eof : Usize) : core.result.Result ImportShape HeaderError → Prop
  | .Ok shape => BodyShape tokens shape.target shape.remaining
  | .Err error => Mismatch [.Open,.Iri,.Close] tokens eof error

theorem expected_terminal_total_correct (expected : HeaderExpected) (terminal : Terminal) :
    expected_terminal expected terminal = .ok (decide (Expected expected terminal)) := by
  cases expected <;> cases terminal <;> simp [expected_terminal,Expected]
theorem expected_iri_kind (terminal : Terminal) :
    Expected .Iri terminal ↔ ∃ kind, Kind terminal = some kind := by
  cases terminal <;> simp [Expected,Kind]
theorem take_expected_total_correct (tokens : Tokens) (expected : HeaderExpected) (eof : Usize) :
    ∃ result, take_expected tokens expected eof = .ok result ∧ TakeCorrect tokens expected eof result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected expected eof),rfl,.empty _ _ _⟩
  | Cons token rest =>
    by_cases accepted : Expected expected token.terminal
    · exact ⟨.Ok (token,rest),by simp [take_expected,expected_terminal_total_correct,accepted],rfl,accepted⟩
    · exact ⟨.Err (.Expected expected token.start),by simp [take_expected,expected_terminal_total_correct,accepted],.wrong _ _ _ _ _ accepted⟩
private theorem prepend_failure {tokens rest : Tokens} {expected : HeaderExpected} {token : Token}
    {tail : List HeaderExpected} {eof : Usize} {error : HeaderError}
    (taken : Taken tokens expected token rest) (failure : Mismatch tail rest eof error) :
    Mismatch (expected::tail) tokens eof error := by
  rw [taken.1]
  exact .later taken.2 failure
theorem read_import_shape_total_correct (tokens : Tokens) (eof : Usize) :
    ∃ result, read_import_shape tokens eof = .ok result ∧ ShapeCorrect tokens eof result := by
  rw [read_import_shape]
  obtain ⟨first,firstRead,firstCorrect⟩ := take_expected_total_correct tokens .Open eof
  simp only [firstRead,bind_ok]
  cases first with
  | Err error => exact ⟨.Err error,rfl,by
      cases firstCorrect with
      | empty => exact .empty _ _ _
      | wrong _ _ _ _ _ wrong => exact .wrong _ _ _ _ _ wrong
      | later _ impossible => cases impossible⟩
  | Ok pair =>
    obtain ⟨opening,one⟩ := pair
    simp only [uncurry_apply_pair]
    obtain ⟨second,secondRead,secondCorrect⟩ := take_expected_total_correct one .Iri eof
    simp only [secondRead,bind_ok]
    cases second with
    | Err error => exact ⟨.Err error,rfl,prepend_failure firstCorrect (by
        cases secondCorrect with
        | empty => exact .empty _ _ _
        | wrong _ _ _ _ _ wrong => exact .wrong _ _ _ _ _ wrong
        | later _ impossible => cases impossible)⟩
    | Ok pair =>
      obtain ⟨target,two⟩ := pair
      simp only [uncurry_apply_pair]
      obtain ⟨third,thirdRead,thirdCorrect⟩ := take_expected_total_correct two .Close eof
      simp only [thirdRead,bind_ok]
      cases third with
      | Err error => exact ⟨.Err error,rfl,prepend_failure firstCorrect (prepend_failure secondCorrect (by
          cases thirdCorrect with
          | empty => exact .empty _ _ _
          | wrong _ _ _ _ _ wrong => exact .wrong _ _ _ _ _ wrong
          | later _ impossible => cases impossible))⟩
      | Ok pair =>
        obtain ⟨closing,rest⟩ := pair
        simp only [uncurry_apply_pair]
        exact ⟨.Ok ⟨target,rest⟩,rfl,opening,closing,
          by rw [firstCorrect.1,secondCorrect.1,thirdCorrect.1],firstCorrect.2,secondCorrect.2,thirdCorrect.2⟩
private theorem mismatch_unique {expected : List HeaderExpected} {tokens : Tokens} {eof : Usize}
    {one two : HeaderError} (first : Mismatch expected tokens eof one)
    (second : Mismatch expected tokens eof two) : one = two := by
  induction first with
  | empty => cases second; rfl
  | wrong _ _ _ _ _ wrong =>
    cases second with
    | wrong => rfl
    | later accepted _ => exact False.elim (wrong accepted)
  | later accepted failed ih =>
    cases second with
    | wrong _ _ _ _ _ wrong => exact False.elim (wrong accepted)
    | later _ failed => exact ih failed
private theorem failure_after {tokens rest : Tokens} {expected : HeaderExpected} {token : Token}
    {tail : List HeaderExpected} {eof : Usize} {error : HeaderError}
    (taken : Taken tokens expected token rest) (failure : Mismatch (expected::tail) tokens eof error) :
    Mismatch tail rest eof error := by
  rw [taken.1] at failure
  cases failure with
  | wrong _ _ _ _ _ wrong => exact False.elim (wrong taken.2)
  | later _ failed => exact failed
private theorem shape_excludes_failure {tokens rest : Tokens} {target : Token} {eof : Usize} {error : HeaderError}
    (shape : BodyShape tokens target rest) (failure : Mismatch [.Open,.Iri,.Close] tokens eof error) : False := by
  obtain ⟨opening,closing,same,openKind,iriKind,closeKind⟩ := shape
  rw [same] at failure
  have first := failure_after ⟨rfl,openKind⟩ failure
  have second := failure_after ⟨rfl,iriKind⟩ first
  have third := failure_after ⟨rfl,closeKind⟩ second
  cases third
private theorem shape_unique {tokens oneRest twoRest : Tokens} {oneTarget twoTarget : Token}
    (first : BodyShape tokens oneTarget oneRest) (second : BodyShape tokens twoTarget twoRest) :
    oneTarget = twoTarget ∧ oneRest = twoRest := by
  obtain ⟨openOne,closeOne,inputOne,_⟩ := first
  obtain ⟨openTwo,closeTwo,inputTwo,_⟩ := second
  have same := inputOne.symm.trans inputTwo
  injection same with _ same
  injection same with targetSame same
  injection same with _ restSame
  exact ⟨targetSame,restSame⟩
private theorem shape_correct_unique (tokens : Tokens) (eof : Usize)
    (one two : core.result.Result ImportShape HeaderError)
    (first : ShapeCorrect tokens eof one) (second : ShapeCorrect tokens eof two) : one = two := by
  cases one with
  | Ok one =>
    cases two with
    | Err error => exact False.elim (shape_excludes_failure first second)
    | Ok two =>
      obtain ⟨targetSame,restSame⟩ := shape_unique first second
      cases one; cases two; cases targetSame; cases restSame; rfl
  | Err one =>
    cases two with
    | Ok shape => exact False.elim (shape_excludes_failure second first)
    | Err two => exact congrArg core.result.Result.Err (mismatch_unique first second)
theorem read_import_shape_result_iff (tokens : Tokens) (eof : Usize) (result : core.result.Result ImportShape HeaderError) :
    read_import_shape tokens eof = .ok result ↔ ShapeCorrect tokens eof result := by
  obtain ⟨actual,executed,correct⟩ := read_import_shape_total_correct tokens eof
  constructor
  · intro output
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    have same := shape_correct_unique tokens eof actual result correct source
    simpa [same] using executed
theorem import_shape_count {tokens rest : Tokens} {target : Token} (shape : BodyShape tokens target rest) :
    Rowl.FunctionalLexer.TokenCount tokens = 3+Rowl.FunctionalLexer.TokenCount rest := by
  obtain ⟨opening,closing,rfl,_⟩ := shape
  simp [Rowl.FunctionalLexer.TokenCount]
  omega

end Rowl.FunctionalHeaderShape
