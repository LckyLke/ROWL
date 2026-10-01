import Rowl.FunctionalSelection
import Rowl.NTriples

namespace Rowl.FunctionalLexer
open Aeneas Aeneas.Std Aeneas.Std.Result RowlFrontendRust RowlFrontendRust.functional_lexer
open Rowl.Unicode Rowl.NTriples
open RowlFrontendRust.functional (Terminal Token)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- All seven delimiter codepoints in OWL 2 Functional Syntax section 2.2. -/
def Delimiter (cp : Nat) : Prop := cp = 61 ∨ cp = 40 ∨ cp = 41 ∨ cp = 60 ∨ cp = 62 ∨ cp = 64 ∨ cp = 94
/-- Only these terminal kinds are discarded. -/
def Special (terminal : Terminal) : Prop := terminal = .Whitespace ∨ terminal = .Comment

theorem delimiter_total_correct (cp : U32) : delimiter cp = .ok (decide (Delimiter cp.val)) := by
  simp [delimiter,Delimiter,UScalar.eq_equiv]
  split_ifs <;> simp_all

theorem special_total_correct (terminal : Terminal) : special terminal = .ok (decide (Special terminal)) := by
  cases terminal <;> simp [special,Special]

/-- The final source codepoint, or the supplied previous value for an empty
    segment. Codepoints and boundaries come from the independent UTF-8 grammar. -/
def LastCorrect (word : List Nat) (previous result : Option U32) : Prop :=
  result.map UScalar.val = word.getLast?.or (previous.map UScalar.val)

private theorem span_bounds {bs : List U8} {start finish : Nat} {word : List Nat}
    (span : Rowl.Longest.Utf8Span bs start finish word) : start ≤ finish ∧ finish ≤ bs.length := by
  induction span with
  | empty bound => exact ⟨le_rfl,bound⟩
  | character _ positive fits tail ih => constructor <;> omega

private theorem last_update (word : List Nat) (cp : Nat) (previous : Option Nat) :
    word.getLast?.or (some cp) = (cp::word).getLast?.or previous := by
  simp only [List.getLast?_cons]
  cases word.getLast? <;> rfl

private theorem last_on_span (bytes : alloc.vec.Vec U8) {start finish : Nat} {word : List Nat}
    (span : Rowl.Longest.Utf8Span bytes.val start finish word) :
    ∀ position stop : Usize, ∀ previous : Option U32, position.val = start → stop.val = finish →
      ∃ result, last_codepoint bytes position stop previous = .ok result ∧ LastCorrect word previous result := by
  induction span with
  | empty bound =>
    intro position stop previous positionValue stopValue
    have same : position = stop := UScalar.eq_of_val_eq (positionValue.trans stopValue.symm)
    exact ⟨previous,by simp [last_codepoint,same],by simp [LastCorrect]⟩
  | @character start cp width finish word unit positive fits tail ih =>
    intro position stop previous positionValue stopValue
    have bounds := span_bounds tail
    have before : position.val < stop.val := by omega
    obtain ⟨decoded,executed,correct⟩ := decode_next_total_correct bytes position
    cases decoded with
    | End => have eof : position.val = bytes.val.length := correct; omega
    | Error error =>
      cases error with
      | InvalidPosition offset => have := correct.2; omega
      | InvalidUtf8 offset =>
        have invalid := correct.2.2
        rw [positionValue,unit] at invalid
        contradiction
      | NonXmlCharacter _ _ => exact False.elim correct
    | Scalar value next =>
      obtain ⟨advance,bounded,unitPrefix⟩ := correct
      have sourceUnit : Rowl.Unicode.Prefix bytes.val position.val = some (cp,width) := by simpa [positionValue] using unit
      have same := Prod.mk.inj (Option.some.inj (sourceUnit.symm.trans unitPrefix))
      have valueMatches : value.val = cp := same.1.symm
      have nextValue : next.val = start+width := by omega
      have nextFits : next.val ≤ stop.val := by omega
      obtain ⟨result,rest,restCorrect⟩ := ih next stop (some value) nextValue stopValue
      refine ⟨result,?_,?_⟩
      · rw [last_codepoint]
        simp [UScalar.eq_equiv,UScalar.lt_equiv,UScalar.le_equiv,before,show ¬ stop.val < position.val from by omega,
          executed,nextFits,rest]
      · change result.map UScalar.val = (cp::word).getLast?.or (previous.map UScalar.val)
        rw [← last_update]
        simpa only [LastCorrect,Option.map_some,valueMatches] using restCorrect

/-- The source-linked final-codepoint reader is total and exact on every
    supplied grammar-valid segment. Invalid/split-span fallback is excluded. -/
theorem last_codepoint_total_correct (bytes : alloc.vec.Vec U8) (start stop : Usize) (previous : Option U32)
    (word : List Nat) (span : Rowl.Longest.Utf8Span bytes.val start.val stop.val word) :
    ∃ result, last_codepoint bytes start stop previous = .ok result ∧ LastCorrect word previous result :=
  last_on_span bytes span start stop previous rfl rfl


/-- Independent final-codepoint evidence at both original token boundaries. -/
def Ending (bs : List U8) (token : Token) (cp : Nat) : Prop :=
  ∃ word, Rowl.Longest.Utf8Span bs token.start.val token.end.val word ∧ word.getLast? = some cp
/-- The next unit begins with a delimiter; no native backwards byte indexing is
    part of this specification. -/
def LeadingDelimiter (bs : List U8) (position : Nat) : Prop :=
  ∃ cp width, Rowl.Unicode.Prefix bs position = some (cp,width) ∧ Delimiter cp
/-- A token boundary that requires no discarded separator. -/
def Ready (bs : List U8) (token : Token) (last : Nat) : Prop :=
  Delimiter last ∨ token.end.val = bs.length ∨ LeadingDelimiter bs token.end.val
/-- The permitted next source position: an immediate delimiter/EOF boundary,
    or a greatest whitespace/comment endpoint. Whitespace has priority when
    both classes are eligible. -/
def GapAllowed (bs : List U8) (token : Token) (position : Nat) : Prop :=
  ∃ last, Ending bs token last ∧
    ((Ready bs token last ∧ position = token.end.val) ∨
     (¬ Ready bs token last ∧ ∃ endpoint : Usize, position = endpoint.val ∧
       Rowl.Longest.Maximal (Rowl.FunctionalSelection.Candidate bs token.end.val .Whitespace) (some endpoint)) ∨
     (¬ Ready bs token last ∧
       Rowl.Longest.Maximal (Rowl.FunctionalSelection.Candidate bs token.end.val .Whitespace) none ∧
       ∃ endpoint : Usize, position = endpoint.val ∧
       Rowl.Longest.Maximal (Rowl.FunctionalSelection.Candidate bs token.end.val .Comment) (some endpoint)))
/-- A valid non-delimiter boundary with neither separator language available. -/
def GapMissing (bs : List U8) (token : Token) : Prop :=
  ∃ last, Ending bs token last ∧ ¬ Ready bs token last ∧
    Rowl.Longest.Maximal (Rowl.FunctionalSelection.Candidate bs token.end.val .Whitespace) none ∧
    Rowl.Longest.Maximal (Rowl.FunctionalSelection.Candidate bs token.end.val .Comment) none
/-- Malformed-text/split-span fallbacks are unreachable after a selected token
    in a fully valid suffix. -/
def GapCorrect (bs : List U8) (token : Token) : Gap → Prop
  | .Next position => GapAllowed bs token position.val
  | .Missing => GapMissing bs token
  | .InvalidText _ | .InvalidSpan => False

private theorem utf8_bounds {bs : List U8} {position : Nat} {word : List Nat}
    (valid : Rowl.Regular.Utf8From bs position word) : position ≤ bs.length := by
  cases valid with
  | endOfInput => omega
  | character _ _ fits _ => omega

private theorem after_span {bs : List U8} {start finish : Nat} {word : List Nat}
    (span : Rowl.Longest.Utf8Span bs start finish word) :
    ∀ text, Rowl.Regular.Utf8From bs start text → ∃ tail, Rowl.Regular.Utf8From bs finish tail := by
  induction span with
  | empty _ => intro text valid; exact ⟨text,valid⟩
  | character unit positive fits tail ih =>
    intro text valid
    cases valid with
    | endOfInput => omega
    | character otherUnit _ _ rest =>
      have equal := Prod.mk.inj (Option.some.inj (unit.symm.trans otherUnit))
      rcases equal with ⟨rfl,rfl⟩
      exact ih _ rest

private theorem error_excluded (bs : List U8) (position : Usize) (error : unicode.TextError)
    (correct : StepCorrect bs position (.Error error))
    (valid : ∃ word, Rowl.Regular.Utf8From bs position.val word) : False := by
  obtain ⟨word,valid⟩ := valid
  cases error with
  | InvalidPosition _ => have bound := utf8_bounds valid; have := correct.2; omega
  | InvalidUtf8 _ =>
    exact Rowl.Regular.failure_excludes_utf8 _ _ _
      (.utf8 (congrArg UScalar.val correct.1) correct.2.1 correct.2.2) word valid
  | NonXmlCharacter _ _ => exact correct

private theorem scalar_not_ready (bs : List U8) (token : Token) (last : Nat) (cp : U32) (next : Usize)
    (unit : StepCorrect bs token.end (.Scalar cp next))
    (notLast : ¬ Delimiter last) (notNext : ¬ Delimiter cp.val) : ¬ Ready bs token last := by
  rintro (lastDelimiter | atEnd | ⟨other,width,otherUnit,otherDelimiter⟩)
  · exact notLast lastDelimiter
  · have := unit.1; have := unit.2.1; omega
  · have equal := Prod.mk.inj (Option.some.inj (unit.2.2.symm.trans otherUnit))
    exact notNext (equal.1.symm ▸ otherDelimiter)

private theorem gap_from_trivia (bytes : alloc.vec.Vec U8) (token : Token) (last : Nat)
    (ending : Ending bytes.val token last) (notReady : ¬ Ready bytes.val token last)
    (valid : ∃ word, Rowl.Regular.Utf8From bytes.val token.end.val word) :
    ∃ result, (do
      let space ← functional.longest .Whitespace bytes token.end
      match space with
      | .Matched endpoint => match endpoint with
        | none =>
          let comment ← functional.longest .Comment bytes token.end
          match comment with
          | .Matched endpoint => match endpoint with
            | none => .ok Gap.Missing
            | some finish => .ok (Gap.Next finish)
          | .MalformedUtf8 error => .ok (Gap.InvalidText error)
        | some finish => .ok (Gap.Next finish)
      | .MalformedUtf8 error => .ok (Gap.InvalidText error)) = .ok result ∧ GapCorrect bytes.val token result := by
  obtain ⟨space,spaceExecuted,spaceCorrect⟩ := Rowl.Functional.longest_total_correct .Whitespace bytes token.end
  simp only [spaceExecuted,bind_ok]
  cases space with
  | MalformedUtf8 error =>
    obtain ⟨word,valid⟩ := valid
    exact False.elim (Rowl.Regular.failure_excludes_utf8 _ _ _ spaceCorrect word valid)
  | Matched endpoint =>
    cases endpoint with
    | some finish => exact ⟨.Next finish,by simp, last,ending,Or.inr (Or.inl ⟨notReady,finish,rfl,spaceCorrect.2⟩)⟩
    | none =>
      obtain ⟨comment,commentExecuted,commentCorrect⟩ := Rowl.Functional.longest_total_correct .Comment bytes token.end
      simp only [commentExecuted,bind_ok]
      cases comment with
      | MalformedUtf8 error =>
        obtain ⟨word,valid⟩ := valid
        exact False.elim (Rowl.Regular.failure_excludes_utf8 _ _ _ commentCorrect word valid)
      | Matched endpoint =>
        cases endpoint with
        | some finish => exact ⟨.Next finish,by simp, last,ending,Or.inr (Or.inr ⟨notReady,spaceCorrect.2,finish,rfl,commentCorrect.2⟩)⟩
        | none => exact ⟨.Missing,by simp, last,ending,notReady,spaceCorrect.2,commentCorrect.2⟩

/-- The actual separator checker is total and exact at every independently
    selected token. This includes byte-correct Unicode endings, EOF/delimiters
    and maximal discarded trivia; malformed/split-span results are excluded. -/
theorem separator_total_correct (bytes : alloc.vec.Vec U8) (token : Token)
    (selected : Rowl.FunctionalSelection.Correct bytes.val token.start.val (.Token token)) :
    ∃ result, separator bytes token = .ok result ∧ GapCorrect bytes.val token result := by
  obtain ⟨word,span,accepted⟩ := selected.2.2.1
  have nonempty : word ≠ [] := by
    intro equal
    exact Rowl.Functional.grammar_nonempty token.terminal (by simpa [equal] using accepted)
  obtain ⟨last,lastExecuted,lastCorrect⟩ := last_codepoint_total_correct bytes token.start token.end none word span
  have lastEqual : last.map UScalar.val = word.getLast? := by simpa [LastCorrect] using lastCorrect
  cases last with
  | none =>
    have empty : word = [] := List.getLast?_eq_none_iff.mp (by simpa using lastEqual.symm)
    contradiction
  | some cp =>
    have ending : Ending bytes.val token cp.val := ⟨word,span,by simpa using lastEqual.symm⟩
    rw [separator,lastExecuted,bind_ok]
    dsimp only
    rw [delimiter_total_correct,bind_ok]
    by_cases delimited : Delimiter cp.val
    · exact ⟨.Next token.end,by simp [delimited],cp.val,ending,Or.inl ⟨Or.inl delimited,rfl⟩⟩
    · simp only [delimited,decide_false,Bool.false_eq_true,↓reduceIte]
      obtain ⟨suffix,valid⟩ := selected.1
      obtain ⟨tail,tailValid⟩ := after_span span suffix valid
      obtain ⟨next,nextExecuted,nextCorrect⟩ := decode_next_total_correct bytes token.end
      rw [nextExecuted,bind_ok]
      cases next with
      | Error error => exact False.elim (error_excluded _ _ _ nextCorrect ⟨tail,tailValid⟩)
      | End => exact ⟨.Next token.end,rfl,cp.val,ending,Or.inl ⟨Or.inr (Or.inl nextCorrect),rfl⟩⟩
      | Scalar other finish =>
        dsimp only
        rw [delimiter_total_correct,bind_ok]
        by_cases nextDelimiter : Delimiter other.val
        · exact ⟨.Next token.end,by simp [nextDelimiter],cp.val,ending,
            Or.inl ⟨Or.inr (Or.inr ⟨other.val,finish.val-token.end.val,nextCorrect.2.2,nextDelimiter⟩),rfl⟩⟩
        · simp only [nextDelimiter,decide_false,Bool.false_eq_true,↓reduceIte]
          exact gap_from_trivia bytes token cp.val ending
            (scalar_not_ready _ _ _ _ _ nextCorrect delimited nextDelimiter) ⟨tail,tailValid⟩

/-- Every permitted separator position stays after the token and inside the
    original source. This is the progress premise for the document loop. -/
theorem gap_allowed_bounds (bs : List U8) (token : Token) (position : Nat)
    (allowed : GapAllowed bs token position) : token.end.val ≤ position ∧ position ≤ bs.length := by
  obtain ⟨last,⟨word,span,_⟩,casesAllowed⟩ := allowed
  rcases casesAllowed with ⟨_,rfl⟩ | ⟨_,endpoint,rfl,maximum⟩ | ⟨_,_,endpoint,rfl,maximum⟩
  · exact ⟨le_rfl,(span_bounds span).2⟩
  · obtain ⟨word,span,_⟩ := maximum.1; exact span_bounds span
  · obtain ⟨word,span,_⟩ := maximum.1; exact span_bounds span


private theorem ending_unique (bytes : alloc.vec.Vec U8) (token : Token) (one two : Nat)
    (first : Ending bytes.val token one) (second : Ending bytes.val token two) : one = two := by
  obtain ⟨firstWord,firstSpan,firstLast⟩ := first
  obtain ⟨secondWord,secondSpan,secondLast⟩ := second
  obtain ⟨a,ha,ca⟩ := last_codepoint_total_correct bytes token.start token.end none firstWord firstSpan
  obtain ⟨b,hb,cb⟩ := last_codepoint_total_correct bytes token.start token.end none secondWord secondSpan
  have same := Result.ok_injective (ha.symm.trans hb)
  subst b
  have va : a.map UScalar.val = some one := by simpa [LastCorrect,firstLast] using ca
  have vb : a.map UScalar.val = some two := by simpa [LastCorrect,secondLast] using cb
  exact Option.some.inj (va.symm.trans vb)

private theorem maximum_unique (eligible : Nat → Prop) (one two : Usize)
    (first : Rowl.Longest.Maximal eligible (some one))
    (second : Rowl.Longest.Maximal eligible (some two)) : one.val = two.val :=
  Nat.le_antisymm (second.2 one.val first.1) (first.2 two.val second.1)

private theorem gap_unique (bytes : alloc.vec.Vec U8) (token : Token) (one two : Nat)
    (first : GapAllowed bytes.val token one) (second : GapAllowed bytes.val token two) : one = two := by
  obtain ⟨a,ea,ga⟩ := first
  obtain ⟨b,eb,gb⟩ := second
  have same := ending_unique bytes token a b ea eb
  subst b
  rcases ga with ⟨ready,rfl⟩ | ⟨notReady,finish,rfl,white⟩ | ⟨notReady,noWhite,finish,rfl,comment⟩
  · rcases gb with ⟨_,rfl⟩ | ⟨notReady,_,_,_⟩ | ⟨notReady,_,_,_,_⟩
    · rfl
    · contradiction
    · contradiction
  · rcases gb with ⟨ready,_⟩ | ⟨_,other,rfl,otherWhite⟩ | ⟨_,noWhite,_,_,_⟩
    · contradiction
    · exact maximum_unique _ finish other white otherWhite
    · exact False.elim (noWhite finish.val white.1)
  · rcases gb with ⟨ready,_⟩ | ⟨_,other,_,white⟩ | ⟨_,_,other,rfl,otherComment⟩
    · contradiction
    · exact False.elim (noWhite other.val white.1)
    · exact maximum_unique _ finish other comment otherComment

private theorem gap_missing_excludes (bytes : alloc.vec.Vec U8) (token : Token) (position : Nat)
    (allowed : GapAllowed bytes.val token position) (missing : GapMissing bytes.val token) : False := by
  obtain ⟨a,ea,ga⟩ := allowed
  obtain ⟨b,eb,notReady,noWhite,noComment⟩ := missing
  have same := ending_unique bytes token a b ea eb
  subst b
  rcases ga with ⟨ready,_⟩ | ⟨_,finish,_,white⟩ | ⟨_,_,finish,_,comment⟩
  · contradiction
  · exact noWhite finish.val white.1
  · exact noComment finish.val comment.1

/-- Exact complete acceptance of a separator endpoint, without supplied
    execution metadata or unchecked source-boundary assumptions. -/
theorem separator_next_iff (bytes : alloc.vec.Vec U8) (token : Token) (position : Usize)
    (selected : Rowl.FunctionalSelection.Correct bytes.val token.start.val (.Token token)) :
    separator bytes token = .ok (.Next position) ↔ GapAllowed bytes.val token position.val := by
  obtain ⟨result,executed,correct⟩ := separator_total_correct bytes token selected
  constructor
  · intro accepted
    have same := Result.ok_injective (executed.symm.trans accepted)
    simpa [same,GapCorrect] using correct
  · intro allowed
    cases result with
    | Next actual =>
      have same : actual = position := UScalar.eq_of_val_eq (gap_unique bytes token _ _ correct allowed)
      simpa [same] using executed
    | Missing => exact False.elim (gap_missing_excludes bytes token _ allowed correct)
    | InvalidText _ | InvalidSpan => exact False.elim correct

/-- Missing separators are exactly the valid boundaries where neither required
    separator language has a candidate. -/
theorem separator_missing_iff (bytes : alloc.vec.Vec U8) (token : Token)
    (selected : Rowl.FunctionalSelection.Correct bytes.val token.start.val (.Token token)) :
    separator bytes token = .ok .Missing ↔ GapMissing bytes.val token := by
  obtain ⟨result,executed,correct⟩ := separator_total_correct bytes token selected
  constructor
  · intro accepted
    have same := Result.ok_injective (executed.symm.trans accepted)
    simpa [same,GapCorrect] using correct
  · intro missing
    cases result with
    | Next actual => exact False.elim (gap_missing_excludes bytes token _ correct missing)
    | Missing => exact executed
    | InvalidText _ | InvalidSpan => exact False.elim correct


/-- Prepend a successfully accepted regular token; a later diagnostic retains
    its original form and offset rather than exposing a successful prefix. -/
def WithToken (token : Token) : LexResult → LexResult
  | .Tokens tail => .Tokens (.Cons token tail)
  | result => result
/-- Independent whole-stream derivations. Each step uses a source-language
    greatest token, exact separator conditions and a mathematical token budget.
    Failure derivations record the first failing stage after valid predecessors. -/
inductive Run (bs : List U8) : Nat → Nat → LexResult → Prop
  | endOfInput {remaining} : Run bs bs.length remaining (.Tokens .Empty)
  | noToken (position : Usize) (remaining : Nat) : position.val < bs.length →
      (∀ terminal endpoint, ¬ Rowl.FunctionalSelection.Candidate bs position.val terminal endpoint) →
      Run bs position.val remaining (.NoToken position)
  | tokenLimit (position : Usize) (token : Token) :
      Rowl.FunctionalSelection.Correct bs position.val (.Token token) → ¬ Special token.terminal →
      Run bs position.val 0 (.TokenLimit position)
  | missingSeparator (position : Usize) (remaining : Nat) (token : Token) :
      Rowl.FunctionalSelection.Correct bs position.val (.Token token) → ¬ Special token.terminal →
      0 < remaining → GapMissing bs token → Run bs position.val remaining (.MissingSeparator token.end)
  | trivia {position remaining token result} :
      Rowl.FunctionalSelection.Correct bs position (.Token token) → Special token.terminal →
      Run bs token.end.val remaining result → Run bs position remaining result
  | regular {position remaining token next result} :
      Rowl.FunctionalSelection.Correct bs position (.Token token) → ¬ Special token.terminal →
      0 < remaining → GapAllowed bs token next → Run bs next (remaining-1) result →
      Run bs position remaining (WithToken token result)

private theorem gap_suffix (bs : List U8) (token : Token) (position : Nat)
    (valid : ∃ word, Rowl.Regular.Utf8From bs token.end.val word)
    (allowed : GapAllowed bs token position) : ∃ word, Rowl.Regular.Utf8From bs position word := by
  obtain ⟨_,_,casesAllowed⟩ := allowed
  rcases casesAllowed with ⟨_,rfl⟩ | ⟨_,endpoint,rfl,maximum⟩ | ⟨_,_,endpoint,rfl,maximum⟩
  · exact valid
  · obtain ⟨word,span,_⟩ := maximum.1
    obtain ⟨text,valid⟩ := valid
    exact after_span span text valid
  · obtain ⟨word,span,_⟩ := maximum.1
    obtain ⟨text,valid⟩ := valid
    exact after_span span text valid

private theorem scan_total (bytes : alloc.vec.Vec U8) (position remaining : Usize)
    (valid : ∃ word, Rowl.Regular.Utf8From bytes.val position.val word) :
    ∃ result, scan bytes position remaining = .ok result ∧ Run bytes.val position.val remaining.val result := by
  by_cases atEnd : position.val = bytes.val.length
  · refine ⟨.Tokens .Empty,?_,?_⟩
    · rw [scan]
      simp [alloc.vec.Vec.len,UScalar.eq_equiv,atEnd]
    · simpa [atEnd] using (Run.endOfInput (bs := bytes.val) (remaining := remaining.val))
  · obtain ⟨selected,selectionExecuted,selectionCorrect⟩ := Rowl.FunctionalSelection.next_terminal_total_correct bytes position
    rw [scan]
    simp only [UScalar.eq_equiv,alloc.vec.Vec.len_val,atEnd,↓reduceIte,selectionExecuted,bind_ok]
    cases selected with
    | NoMatch =>
      obtain ⟨word,valid⟩ := valid
      exact ⟨.NoToken position,rfl,.noToken position remaining.val (by have := utf8_bounds valid; omega) selectionCorrect.2⟩
    | MalformedUtf8 error =>
      obtain ⟨word,valid⟩ := valid
      exact False.elim (Rowl.Regular.failure_excludes_utf8 _ _ _ selectionCorrect word valid)
    | Token token =>
      have progress := Rowl.FunctionalSelection.next_terminal_advances bytes position token selectionExecuted
      obtain ⟨word,span,_⟩ := selectionCorrect.2.2.1
      obtain ⟨source,sourceValid⟩ := valid
      have tailValid := after_span span source sourceValid
      have tokenSelected : Rowl.FunctionalSelection.Correct bytes.val token.start.val (.Token token) := by
        simpa [selectionCorrect.2.1] using selectionCorrect
      dsimp only
      rw [special_total_correct,bind_ok]
      by_cases discarded : Special token.terminal
      · simp only [discarded,decide_true,↓reduceIte]
        obtain ⟨result,executed,correct⟩ := scan_total bytes token.end remaining tailValid
        exact ⟨result,executed,.trivia selectionCorrect discarded correct⟩
      · simp only [discarded,decide_false,Bool.false_eq_true,↓reduceIte]
        by_cases noBudget : remaining.val = 0
        · refine ⟨.TokenLimit position,?_,?_⟩
          · simp [UScalar.eq_equiv,noBudget]
          · simpa [noBudget] using (Run.tokenLimit position token selectionCorrect discarded)
        · simp only [UScalar.eq_equiv,show (0#usize).val = 0 from rfl,noBudget,↓reduceIte]
          obtain ⟨gap,gapExecuted,gapCorrect⟩ := separator_total_correct bytes token tokenSelected
          rw [gapExecuted,bind_ok]
          cases gap with
          | Missing => exact ⟨.MissingSeparator token.end,rfl,.missingSeparator position remaining.val token selectionCorrect discarded (by omega) gapCorrect⟩
          | InvalidText _ | InvalidSpan => exact False.elim gapCorrect
          | Next finish =>
            have gapBound := gap_allowed_bounds bytes.val token finish.val gapCorrect
            have suffix := gap_suffix bytes.val token finish.val tailValid gapCorrect
            have subtraction := Usize.sub_spec (x := remaining) (y := 1#usize) (by scalar_tac)
            obtain ⟨smaller,subExecuted,subValue⟩ := WP.spec_imp_exists subtraction
            obtain ⟨result,executed,correct⟩ := scan_total bytes finish smaller suffix
            refine ⟨WithToken token result,?_,?_⟩
            · cases result <;> simp [subExecuted,executed,WithToken,bind_ok]
            · exact .regular selectionCorrect discarded (by omega) gapCorrect (by simpa [subValue] using correct)
termination_by bytes.val.length-position.val
decreasing_by all_goals omega

private theorem text_utf8 {bs : List U8} {position : Nat} {text : List (Nat × Nat)}
    (valid : TextFrom bs position text) : Rowl.Regular.Utf8From bs position (text.map Prod.fst) := by
  induction valid with
  | endOfInput => exact .endOfInput
  | character unit _ positive fits _ ih => exact .character unit positive fits ih

private def Ordinary : LexResult → Prop
  | .InvalidText _ | .InvalidSpan _ => False
  | _ => True
private theorem run_ordinary {bs : List U8} {position remaining : Nat} {result : LexResult}
    (run : Run bs position remaining result) : Ordinary result := by
  induction run with
  | endOfInput => trivial
  | noToken => trivial
  | tokenLimit => trivial
  | missingSeparator => trivial
  | trivia _ _ _ ih => exact ih
  | @regular position remaining token next result _ _ _ _ _ ih =>
    cases result <;> simp_all [Ordinary,WithToken]

/-- The complete byte-boundary contract: initial XML text rejection, or one
    whole source derivation with exact emitted spans and stage diagnostics. -/
def Correct (bs : List U8) (limit : Nat) : LexResult → Prop
  | .InvalidText error => Rejected bs 0 error
  | result => (∃ text, TextFrom bs 0 text) ∧ Run bs 0 limit result

/-- Actual byte-to-token-stream termination and correctness, including first
    source diagnostics and token-limit precedence. All recursive calls advance
    within the immutable source, including discarded trivia. -/
theorem lex_total_correct (bytes : alloc.vec.Vec U8) (limit : Usize) :
    ∃ result, lex bytes limit = .ok result ∧ Correct bytes.val limit.val result := by
  obtain ⟨text,textExecuted,textCorrect⟩ := read_text_total_correct bytes
  rw [lex,textExecuted,bind_ok]
  cases text with
  | Invalid error => exact ⟨.InvalidText error,rfl,textCorrect⟩
  | Valid decoded =>
    have utf8 := text_utf8 textCorrect
    obtain ⟨result,executed,correct⟩ := scan_total bytes 0#usize limit ⟨_,utf8⟩
    refine ⟨result,executed,?_⟩
    cases result with
    | InvalidText error => exact False.elim (run_ordinary correct)
    | _ => exact ⟨⟨_,textCorrect⟩,correct⟩


private theorem selected_before_end (bytes : alloc.vec.Vec U8) (position : Usize) (token : Token)
    (selected : Rowl.FunctionalSelection.Correct bytes.val position.val (.Token token)) :
    position.val < token.end.val ∧ token.end.val ≤ bytes.val.length := by
  have executed := (Rowl.FunctionalSelection.next_terminal_token_iff bytes position token).mpr selected
  exact (Rowl.FunctionalSelection.next_terminal_advances bytes position token executed).2

private theorem run_execution (bytes : alloc.vec.Vec U8) {start budget : Nat} {result : LexResult}
    (run : Run bytes.val start budget result) :
    ∀ position remaining : Usize, position.val = start → remaining.val = budget →
      (∃ word, Rowl.Regular.Utf8From bytes.val start word) → scan bytes position remaining = .ok result := by
  induction run with
  | endOfInput =>
    intro position remaining positionValue remainingValue valid
    rw [scan]
    simp [UScalar.eq_equiv,alloc.vec.Vec.len_val,positionValue]
  | noToken original budget inside absent =>
    intro position remaining positionValue remainingValue valid
    have same : position = original := UScalar.eq_of_val_eq positionValue
    subst position
    obtain ⟨selected,executed,correct⟩ := Rowl.FunctionalSelection.next_terminal_total_correct bytes original
    cases selected with
    | Token token => exact False.elim (absent token.terminal token.end.val correct.2.2.1)
    | MalformedUtf8 error =>
      obtain ⟨word,valid⟩ := valid
      exact False.elim (Rowl.Regular.failure_excludes_utf8 _ _ _ correct word valid)
    | NoMatch =>
      rw [scan]
      simp [UScalar.eq_equiv,alloc.vec.Vec.len_val,show original.val ≠ bytes.val.length from by omega,executed]
  | tokenLimit original token selected notSpecial =>
    intro position remaining positionValue remainingValue valid
    have same : position = original := UScalar.eq_of_val_eq positionValue
    subst position
    have before := selected_before_end bytes original token selected
    have executed := (Rowl.FunctionalSelection.next_terminal_token_iff bytes original token).mpr selected
    rw [scan]
    simp [UScalar.eq_equiv,alloc.vec.Vec.len_val,show original.val ≠ bytes.val.length from by omega,
      executed,special_total_correct,notSpecial,remainingValue]
  | missingSeparator original budget token selected notSpecial positive missing =>
    intro position remaining positionValue remainingValue valid
    have same : position = original := UScalar.eq_of_val_eq positionValue
    subst position
    have before := selected_before_end bytes original token selected
    have executed := (Rowl.FunctionalSelection.next_terminal_token_iff bytes original token).mpr selected
    have tokenSelected : Rowl.FunctionalSelection.Correct bytes.val token.start.val (.Token token) := by
      simpa [selected.2.1] using selected
    have gapExecuted := (separator_missing_iff bytes token tokenSelected).mpr missing
    rw [scan]
    simp [UScalar.eq_equiv,alloc.vec.Vec.len_val,show original.val ≠ bytes.val.length from by omega,
      executed,special_total_correct,notSpecial,show remaining.val ≠ 0 from by omega,gapExecuted]
  | @trivia start budget token result selected discarded tail ih =>
    intro position remaining positionValue remainingValue valid
    have selectedNow : Rowl.FunctionalSelection.Correct bytes.val position.val (.Token token) := by simpa [positionValue] using selected
    have before := selected_before_end bytes position token selectedNow
    have executed := (Rowl.FunctionalSelection.next_terminal_token_iff bytes position token).mpr selectedNow
    obtain ⟨word,span,_⟩ := selected.2.2.1
    obtain ⟨text,valid⟩ := valid
    have suffix := after_span span text valid
    have restExecuted := ih token.end remaining rfl remainingValue suffix
    rw [scan]
    simp [UScalar.eq_equiv,alloc.vec.Vec.len_val,show position.val ≠ bytes.val.length from by omega,
      executed,special_total_correct,discarded,restExecuted]
  | @regular start budget token next result selected notSpecial positive allowed tail ih =>
    intro position remaining positionValue remainingValue valid
    have selectedNow : Rowl.FunctionalSelection.Correct bytes.val position.val (.Token token) := by simpa [positionValue] using selected
    have before := selected_before_end bytes position token selectedNow
    have executed := (Rowl.FunctionalSelection.next_terminal_token_iff bytes position token).mpr selectedNow
    have tokenSelected : Rowl.FunctionalSelection.Correct bytes.val token.start.val (.Token token) := by
      simpa [selected.2.1] using selected
    have bound := gap_allowed_bounds bytes.val token next allowed
    let finish : Usize := Usize.ofNatCore next (by have := alloc.vec.Vec.len_ineq bytes; scalar_tac)
    have finishValue : finish.val = next := UScalar.ofNatCore_val_eq _
    have gapExecuted := (separator_next_iff bytes token finish tokenSelected).mpr (by simpa [finishValue] using allowed)
    obtain ⟨word,span,_⟩ := selected.2.2.1
    obtain ⟨text,valid⟩ := valid
    have atEnd := after_span span text valid
    have suffix := gap_suffix bytes.val token next atEnd allowed
    obtain ⟨smaller,subExecuted,subValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := remaining) (y := 1#usize) (by scalar_tac))
    have smallerValue : smaller.val = budget-1 := by simpa [remainingValue] using subValue.1
    have restExecuted := ih finish smaller finishValue smallerValue suffix
    rw [scan]
    cases result <;> simp [UScalar.eq_equiv,alloc.vec.Vec.len_val,show position.val ≠ bytes.val.length from by omega,
      executed,special_total_correct,notSpecial,show remaining.val ≠ 0 from by omega,gapExecuted,
      subExecuted,restExecuted,WithToken]

/-- Complete byte-to-stream acceptance for the independent whole-source
    derivation and XML-character grammar, with exact token spans and budgets. -/
theorem lex_tokens_iff (bytes : alloc.vec.Vec U8) (limit : Usize) (tokens : Tokens) :
    lex bytes limit = .ok (.Tokens tokens) ↔
      (∃ text, TextFrom bytes.val 0 text) ∧ Run bytes.val 0 limit.val (.Tokens tokens) := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := lex_total_correct bytes limit
    have same := Result.ok_injective (executed.symm.trans accepted)
    simpa [same,Correct] using correct
  · rintro ⟨⟨text,valid⟩,run⟩
    obtain ⟨decoded,textExecuted,textCorrect⟩ := read_text_total_correct bytes
    rw [lex,textExecuted,bind_ok]
    cases decoded with
    | Invalid error => exact False.elim (rejected_excludes_text _ _ _ textCorrect text valid)
    | Valid source =>
      exact run_execution bytes run 0#usize limit rfl rfl ⟨_,text_utf8 valid⟩

/-- Invalid-token-span fallbacks are unreachable from the public byte entry point. -/
theorem lex_excludes_invalid_span (bytes : alloc.vec.Vec U8) (limit position : Usize) :
    lex bytes limit ≠ .ok (.InvalidSpan position) := by
  intro invalid
  obtain ⟨result,executed,correct⟩ := lex_total_correct bytes limit
  have same := Result.ok_injective (executed.symm.trans invalid)
  subst result
  exact run_ordinary correct.2


/-- Mathematical emitted-token count, with discarded trivia contributing zero. -/
def TokenCount : Tokens → Nat
  | .Empty => 0
  | .Cons _ tail => 1+TokenCount tail
/-- Nonempty ordered original source spans, regular kinds only, and independent
    terminal-language membership for every emitted token. -/
def Stream (bs : List U8) (lower : Nat) : Tokens → Prop
  | .Empty => True
  | .Cons token tail => lower ≤ token.start.val ∧ token.start.val < token.end.val ∧
      token.end.val ≤ bs.length ∧ ¬ Special token.terminal ∧
      Rowl.FunctionalSelection.Candidate bs token.start.val token.terminal token.end.val ∧
      Stream bs token.end.val tail
private theorem stream_weaken (bs : List U8) (one two : Nat) (tokens : Tokens)
    (bound : one ≤ two) (stream : Stream bs two tokens) : Stream bs one tokens := by
  cases tokens with
  | Empty => trivial
  | Cons token tail => exact ⟨bound.trans stream.1,stream.2⟩
private theorem candidate_progress (bs : List U8) (start finish : Nat) (terminal : Terminal)
    (candidate : Rowl.FunctionalSelection.Candidate bs start terminal finish) : start < finish ∧ finish ≤ bs.length := by
  obtain ⟨word,span,accepted⟩ := candidate
  have nonempty : word ≠ [] := by
    intro equal
    exact Rowl.Functional.grammar_nonempty terminal (by simpa [equal] using accepted)
  have bound := span_bounds span
  cases span with
  | empty _ => contradiction
  | character _ positive _ tail => have restBound := span_bounds tail; constructor <;> omega
private def OutputCorrect (bs : List U8) (lower budget : Nat) : LexResult → Prop
  | .Tokens tokens => TokenCount tokens ≤ budget ∧ Stream bs lower tokens
  | _ => True
private theorem run_output {bs : List U8} {position remaining : Nat} {result : LexResult}
    (run : Run bs position remaining result) : OutputCorrect bs position remaining result := by
  induction run with
  | endOfInput => exact ⟨by simp [TokenCount],trivial⟩
  | noToken => trivial
  | tokenLimit => trivial
  | missingSeparator => trivial
  | @trivia position remaining token result selected discarded tail ih =>
    cases result with
    | Tokens tokens =>
      have advance := candidate_progress bs position token.end.val token.terminal selected.2.2.1
      exact ⟨ih.1,stream_weaken bs position token.end.val tokens (by omega) ih.2⟩
    | _ => trivial
  | @regular position remaining token next result selected notSpecial positive allowed tail ih =>
    cases result with
    | Tokens tokens =>
      have advance := candidate_progress bs position token.end.val token.terminal selected.2.2.1
      have gapBound := gap_allowed_bounds bs token next allowed
      refine ⟨?_,?_,?_,advance.2,notSpecial,?_,?_⟩
      · change 1+TokenCount tokens ≤ remaining
        have count := ih.1
        omega
      · exact Nat.le_of_eq selected.2.1.symm
      · simpa [selected.2.1] using advance.1
      · simpa [selected.2.1] using selected.2.2.1
      · exact stream_weaken bs token.end.val next tokens gapBound.1 ih.2
    | _ => trivial

/-- Every successful actual whole-source token stream fits the supplied token
    budget and retains ordered, bounded, grammar-valid nontrivia source spans. -/
theorem lex_tokens_properties (bytes : alloc.vec.Vec U8) (limit : Usize) (tokens : Tokens)
    (accepted : lex bytes limit = .ok (.Tokens tokens)) :
    TokenCount tokens ≤ limit.val ∧ Stream bytes.val 0 tokens := by
  have run := ((lex_tokens_iff bytes limit tokens).mp accepted).2
  exact run_output run

end Rowl.FunctionalLexer
