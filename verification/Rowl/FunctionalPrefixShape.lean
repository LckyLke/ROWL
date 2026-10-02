import Rowl.FunctionalNames

namespace Rowl.FunctionalPrefixShape
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional_prefixes RowlRust.functional_lexer
open RowlRust.functional
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The exact terminal classes in the standard prefix/ontology-opening grammar. -/
def Expected : PrefixExpected → Terminal → Prop
  | .Ontology, terminal => terminal = .Keyword .Ontology
  | .Open, terminal => terminal = .Open
  | .Name, terminal => terminal = .PrefixName
  | .Equals, terminal => terminal = .Equals
  | .Namespace, terminal => terminal = .FullIri
  | .Close, terminal => terminal = .Close
/-- A consumed original token and unchanged remaining token stream. -/
def Taken (tokens : Tokens) (expected : PrefixExpected) (token : Token) (rest : Tokens) : Prop :=
  tokens = .Cons token rest ∧ Expected expected token.terminal
/-- First missing/wrong terminal of an independent expected sequence. EOF errors
    retain the original source length; other errors retain the actual token start. -/
inductive Mismatch : List PrefixExpected → Tokens → Usize → PrefixSyntaxError → Prop
  | empty (expected : PrefixExpected) (tail : List PrefixExpected) (eof : Usize) :
      Mismatch (expected::tail) .Empty eof (.Expected expected eof)
  | wrong (expected : PrefixExpected) (tail : List PrefixExpected) (token : Token) (rest : Tokens) (eof : Usize)
      (wrong : ¬ Expected expected token.terminal) :
      Mismatch (expected::tail) (.Cons token rest) eof (.Expected expected token.start)
  | later {expected : PrefixExpected} {tail : List PrefixExpected} {token : Token} {rest : Tokens}
      {eof : Usize} {error : PrefixSyntaxError} (acceptedKind : Expected expected token.terminal)
      (failure : Mismatch tail rest eof error) : Mismatch (expected::tail) (.Cons token rest) eof error
/-- Total contract for consuming one exact expected token. -/
def TakeCorrect (tokens : Tokens) (expected : PrefixExpected) (eof : Usize) :
    core.result.Result (Token × Tokens) PrefixSyntaxError → Prop
  | .Ok (token,rest) => Taken tokens expected token rest
  | .Err error => Mismatch [expected] tokens eof error
/-- The complete punctuation/name skeleton after the original Prefix keyword. -/
def BodyShape (tokens : Tokens) (nameToken namespaceToken : Token) (rest : Tokens) : Prop :=
  ∃ opening equals closing,
    tokens = .Cons opening (.Cons nameToken (.Cons equals (.Cons namespaceToken (.Cons closing rest)))) ∧
    Expected .Open opening.terminal ∧ Expected .Name nameToken.terminal ∧
    Expected .Equals equals.terminal ∧ Expected .Namespace namespaceToken.terminal ∧ Expected .Close closing.terminal
/-- Source-token grammar and first-mismatch contract of the actual shape reader. -/
def ShapeCorrect (tokens : Tokens) (eof : Usize) :
    core.result.Result DeclarationShape PrefixSyntaxError → Prop
  | .Ok shape => BodyShape tokens shape.name shape.namespace shape.remaining
  | .Err error => Mismatch [.Open,.Name,.Equals,.Namespace,.Close] tokens eof error

/-- Actual terminal discrimination equals the independent grammar for every
    expected kind and all 84 possible actual terminal classes. -/
theorem expected_terminal_total_correct (expected : PrefixExpected) (terminal : Terminal) :
    expected_terminal expected terminal = .ok (decide (Expected expected terminal)) := by
  cases terminal with
  | Keyword keyword => cases expected <;> cases keyword <;> simp [expected_terminal,Expected]
  | Open | Close | Equals | DatatypeIndicator | Integer | QuotedString | LanguageTag | NodeId | FullIri | PrefixName | AbbreviatedIri | Whitespace | Comment =>
    cases expected <;> simp [expected_terminal,Expected]

/-- Actual single-token consumption is total, preserves every accepted field,
    and reports exactly the first original mismatch/EOF boundary. -/
theorem take_expected_total_correct (tokens : Tokens) (expected : PrefixExpected) (eof : Usize) :
    ∃ result, take_expected tokens expected eof = .ok result ∧ TakeCorrect tokens expected eof result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected expected eof),rfl,.empty expected [] eof⟩
  | Cons token rest =>
    by_cases acceptedKind : Expected expected token.terminal
    · exact ⟨.Ok (token,rest),by simp [take_expected,expected_terminal_total_correct,acceptedKind],rfl,acceptedKind⟩
    · exact ⟨.Err (.Expected expected token.start),by simp [take_expected,expected_terminal_total_correct,acceptedKind],.wrong expected [] token rest eof acceptedKind⟩

private theorem prepend_failure {tokens rest : Tokens} {expected : PrefixExpected} {token : Token}
    {tail : List PrefixExpected} {eof : Usize} {error : PrefixSyntaxError}
    (taken : Taken tokens expected token rest) (failure : Mismatch tail rest eof error) :
    Mismatch (expected::tail) tokens eof error := by
  rw [taken.1]
  exact .later taken.2 failure

/-- The actual declaration skeleton reader is total and has the independent
    complete five-terminal grammar and exact first-mismatch specification. -/
theorem read_shape_total_correct (tokens : Tokens) (eof : Usize) :
    ∃ result, read_shape tokens eof = .ok result ∧ ShapeCorrect tokens eof result := by
  rw [read_shape]
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
    obtain ⟨second,secondRead,secondCorrect⟩ := take_expected_total_correct one .Name eof
    simp only [secondRead,bind_ok]
    cases second with
    | Err error => exact ⟨.Err error,rfl,prepend_failure firstCorrect (by
        cases secondCorrect with
        | empty => exact .empty _ _ _
        | wrong _ _ _ _ _ wrong => exact .wrong _ _ _ _ _ wrong
        | later _ impossible => cases impossible)⟩
    | Ok pair =>
      obtain ⟨nameToken,two⟩ := pair
      simp only [uncurry_apply_pair]
      obtain ⟨third,thirdRead,thirdCorrect⟩ := take_expected_total_correct two .Equals eof
      simp only [thirdRead,bind_ok]
      cases third with
      | Err error => exact ⟨.Err error,rfl,prepend_failure firstCorrect (prepend_failure secondCorrect (by
          cases thirdCorrect with
          | empty => exact .empty _ _ _
          | wrong _ _ _ _ _ wrong => exact .wrong _ _ _ _ _ wrong
          | later _ impossible => cases impossible))⟩
      | Ok pair =>
        obtain ⟨equals,three⟩ := pair
        simp only [uncurry_apply_pair]
        obtain ⟨fourth,fourthRead,fourthCorrect⟩ := take_expected_total_correct three .Namespace eof
        simp only [fourthRead,bind_ok]
        cases fourth with
        | Err error => exact ⟨.Err error,rfl,prepend_failure firstCorrect (prepend_failure secondCorrect
            (prepend_failure thirdCorrect (by
            cases fourthCorrect with
            | empty => exact .empty _ _ _
            | wrong _ _ _ _ _ wrong => exact .wrong _ _ _ _ _ wrong
            | later _ impossible => cases impossible)))⟩
        | Ok pair =>
          obtain ⟨namespaceToken,four⟩ := pair
          simp only [uncurry_apply_pair]
          obtain ⟨fifth,fifthRead,fifthCorrect⟩ := take_expected_total_correct four .Close eof
          simp only [fifthRead,bind_ok]
          cases fifth with
          | Err error => exact ⟨.Err error,rfl,prepend_failure firstCorrect (prepend_failure secondCorrect
              (prepend_failure thirdCorrect (prepend_failure fourthCorrect (by
              cases fifthCorrect with
              | empty => exact .empty _ _ _
              | wrong _ _ _ _ _ wrong => exact .wrong _ _ _ _ _ wrong
              | later _ impossible => cases impossible))))⟩
          | Ok pair =>
            obtain ⟨closing,rest⟩ := pair
            simp only [uncurry_apply_pair]
            exact ⟨.Ok ⟨nameToken,namespaceToken,rest⟩,rfl,opening,equals,closing,
              by rw [firstCorrect.1,secondCorrect.1,thirdCorrect.1,fourthCorrect.1,fifthCorrect.1],
              firstCorrect.2,secondCorrect.2,thirdCorrect.2,fourthCorrect.2,fifthCorrect.2⟩

private theorem mismatch_unique {expected : List PrefixExpected} {tokens : Tokens} {eof : Usize}
    {one two : PrefixSyntaxError} (first : Mismatch expected tokens eof one)
    (second : Mismatch expected tokens eof two) : one = two := by
  induction first with
  | empty => cases second; rfl
  | wrong _ _ _ _ _ wrong =>
    cases second with
    | wrong => rfl
    | later acceptedKind _ => exact False.elim (wrong acceptedKind)
  | later acceptedKind failed ih =>
    cases second with
    | wrong _ _ _ _ _ wrong => exact False.elim (wrong acceptedKind)
    | later _ failed => exact ih failed
private theorem failure_after {tokens rest : Tokens} {expected : PrefixExpected} {token : Token}
    {tail : List PrefixExpected} {eof : Usize} {error : PrefixSyntaxError}
    (taken : Taken tokens expected token rest) (failure : Mismatch (expected::tail) tokens eof error) :
    Mismatch tail rest eof error := by
  rw [taken.1] at failure
  cases failure with
  | wrong _ _ _ _ _ wrong => exact False.elim (wrong taken.2)
  | later _ failed => exact failed
private theorem shape_excludes_failure {tokens rest : Tokens} {nameToken namespaceToken : Token}
    {eof : Usize} {error : PrefixSyntaxError} (shape : BodyShape tokens nameToken namespaceToken rest)
    (failure : Mismatch [.Open,.Name,.Equals,.Namespace,.Close] tokens eof error) : False := by
  obtain ⟨opening,equals,closing,same,openKind,nameKind,equalKind,namespaceKind,closeKind⟩ := shape
  rw [same] at failure
  have first := failure_after ⟨rfl,openKind⟩ failure
  have second := failure_after ⟨rfl,nameKind⟩ first
  have third := failure_after ⟨rfl,equalKind⟩ second
  have fourth := failure_after ⟨rfl,namespaceKind⟩ third
  have fifth := failure_after ⟨rfl,closeKind⟩ fourth
  cases fifth
private theorem shape_unique {tokens oneRest twoRest : Tokens} {oneName oneNamespace twoName twoNamespace : Token}
    (first : BodyShape tokens oneName oneNamespace oneRest)
    (second : BodyShape tokens twoName twoNamespace twoRest) :
    oneName = twoName ∧ oneNamespace = twoNamespace ∧ oneRest = twoRest := by
  obtain ⟨openOne,equalsOne,closeOne,inputOne,_⟩ := first
  obtain ⟨openTwo,equalsTwo,closeTwo,inputTwo,_⟩ := second
  have same := inputOne.symm.trans inputTwo
  injection same with _ same
  injection same with nameSame same
  injection same with _ same
  injection same with namespaceSame same
  injection same with _ restSame
  exact ⟨nameSame,namespaceSame,restSame⟩
private theorem shape_correct_unique (tokens : Tokens) (eof : Usize)
    (one two : core.result.Result DeclarationShape PrefixSyntaxError)
    (first : ShapeCorrect tokens eof one) (second : ShapeCorrect tokens eof two) : one = two := by
  cases one with
  | Ok one =>
    cases two with
    | Err error => exact False.elim (shape_excludes_failure first second)
    | Ok two =>
      obtain ⟨nameSame,namespaceSame,restSame⟩ := shape_unique first second
      cases one
      cases two
      cases nameSame
      cases namespaceSame
      cases restSame
      rfl
  | Err one =>
    cases two with
    | Ok shape => exact False.elim (shape_excludes_failure second first)
    | Err two => exact congrArg core.result.Result.Err (mismatch_unique first second)

/-- Exact grammar, successful original token fields and all first-error offsets
    characterize the actual skeleton reader in both directions. -/
theorem read_shape_result_iff (tokens : Tokens) (eof : Usize)
    (result : core.result.Result DeclarationShape PrefixSyntaxError) :
    read_shape tokens eof = .ok result ↔ ShapeCorrect tokens eof result := by
  obtain ⟨actual,executed,correct⟩ := read_shape_total_correct tokens eof
  constructor
  · intro output
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    have same := shape_correct_unique tokens eof actual result correct source
    simpa [same] using executed

/-- A successful declaration body consumes exactly five emitted tokens and
    retains the unchanged suffix; this supplies the parser's termination measure. -/
theorem body_shape_count {tokens rest : Tokens} {nameToken namespaceToken : Token}
    (shape : BodyShape tokens nameToken namespaceToken rest) :
    Rowl.FunctionalLexer.TokenCount tokens = 5+Rowl.FunctionalLexer.TokenCount rest := by
  obtain ⟨opening,equals,closing,rfl,_⟩ := shape
  simp [Rowl.FunctionalLexer.TokenCount]
  omega

end Rowl.FunctionalPrefixShape
