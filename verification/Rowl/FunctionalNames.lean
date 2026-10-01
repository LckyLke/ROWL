import Rowl.SourceSpans
import Rowl.FunctionalIntegers
import Rowl.Prefixes
import Rowl.NTriples

namespace Rowl.FunctionalNames
open Aeneas Aeneas.Std Aeneas.Std.Result RowlFrontendRust RowlFrontendRust.functional_names
open scoped Computability
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The five nonquoted standard name-bearing terminal families. -/
def TerminalOf : NameKind → functional.Terminal
  | .FullIri => .FullIri
  | .PrefixName => .PrefixName
  | .AbbreviatedIri => .AbbreviatedIri
  | .NodeId => .NodeId
  | .LanguageTag => .LanguageTag
/-- Fixed leading ASCII syntax markers, counted in original bytes. -/
def Leading : NameKind → Nat
  | .FullIri | .LanguageTag => 1
  | .NodeId => 2
  | .PrefixName | .AbbreviatedIri => 0
/-- Only full IRIs have a trailing syntax marker. -/
def Trailing : NameKind → Nat
  | .FullIri => 1
  | _ => 0
/-- Independent canonical source grammar, with original unchanged endpoints. -/
def Token (kind : NameKind) (source : List U8) (start finish : Nat) : Prop :=
  Rowl.FunctionalSelection.Candidate source start (TerminalOf kind) finish
/-- Exact original spelling with just the fixed syntax markers removed. -/
def Payload (kind : NameKind) (source : List U8) (start finish : Nat) : List U8 :=
  Rowl.SourceSpans.Bytes source (start+Leading kind) (finish-Trailing kind)
/-- Value grammars after removal of the specified ASCII markers. -/
def ValueLanguage : NameKind → Language Nat
  | .FullIri => Rowl.Iri.IriLanguage
  | .PrefixName => Rowl.Names.Prefix
  | .AbbreviatedIri => Rowl.Names.Abbreviated
  | .NodeId => Rowl.Names.Local
  | .LanguageTag => Rowl.LangTag.NormalLanguage
/-- Token failure identifies the original entire span; no finer character
    position is asserted. Budget failures identify the original payload start. -/
def ErrorCorrect (kind : NameKind) (source : List U8) (start finish limit : Nat) : NameError → Prop
  | .InvalidSpan offset => offset.val = start ∧ (finish < start ∨ source.length < finish)
  | .InvalidToken offset => offset.val = start ∧ start ≤ finish ∧ finish ≤ source.length ∧ ¬ Token kind source start finish
  | .ResourceLimit offset => offset.val = start+Leading kind ∧ Token kind source start finish ∧
      limit < (Payload kind source start finish).length
/-- Complete byte-to-name-value specification, including exact source grammar,
    spelling, value budget and original phase/offset diagnostics. -/
def Correct (kind : NameKind) (source : List U8) (start finish limit : Nat) :
    core.result.Result (alloc.vec.Vec U8) NameError → Prop
  | .Ok value => Token kind source start finish ∧ (Payload kind source start finish).length ≤ limit ∧
      value.val = Payload kind source start finish
  | .Err error => ErrorCorrect kind source start finish limit error

private def Head : NameKind → Usize
  | .FullIri | .LanguageTag => 1#usize
  | .NodeId => 2#usize
  | .PrefixName | .AbbreviatedIri => 0#usize
private def Tail : NameKind → Usize
  | .FullIri => 1#usize
  | _ => 0#usize
private theorem head_value (kind : NameKind) : (Head kind).val = Leading kind := by cases kind <;> rfl
private theorem tail_value (kind : NameKind) : (Tail kind).val = Trailing kind := by cases kind <;> rfl
private theorem leading_actual (kind : NameKind) : leading kind = .ok (Head kind) := by cases kind <;> rfl
private theorem trailing_actual (kind : NameKind) : trailing kind = .ok (Tail kind) := by cases kind <;> rfl
private theorem terminal_actual (kind : NameKind) : terminal kind = .ok (TerminalOf kind) := by cases kind <;> rfl
private theorem span_bounds {source : List U8} {start finish : Nat} {word : List Nat}
    (span : Rowl.Longest.Utf8Span source start finish word) : start ≤ finish ∧ finish ≤ source.length := by
  induction span with
  | empty bound => exact ⟨le_rfl,bound⟩
  | character _ positive _ _ ih => constructor <;> omega
private theorem token_bounds {kind : NameKind} {source : List U8} {start finish : Nat}
    (token : Token kind source start finish) : start ≤ finish ∧ finish ≤ source.length := by
  obtain ⟨word,span,_⟩ := token
  exact span_bounds span
private theorem bytes_length (source : List U8) (start finish : Nat)
    (range : start ≤ finish ∧ finish ≤ source.length) :
    (Rowl.SourceSpans.Bytes source start finish).length = finish-start := by
  simp [Rowl.SourceSpans.Bytes]
  omega
private theorem range_word {word : List Nat} {cp : Nat}
    (member : word ∈ Rowl.Iri.Range cp cp) : word = [cp] := by
  obtain ⟨value,rfl,lower,upper⟩ := member
  have same : value = cp := by omega
  simp [same]
private theorem minimum_word (kind : NameKind) (word : List Nat)
    (language : word ∈ Rowl.Functional.TerminalLanguage (TerminalOf kind)) :
    Leading kind+Trailing kind ≤ word.length := by
  cases kind with
  | PrefixName | AbbreviatedIri => simp [Leading,Trailing]
  | LanguageTag =>
    obtain ⟨first,head,tail,_,rfl⟩ := Language.mem_mul.mp language
    rw [range_word head]
    simp [Leading,Trailing]
  | FullIri =>
    obtain ⟨first,head,tail,tailLegal,rfl⟩ := Language.mem_mul.mp language
    obtain ⟨iri,_,closing,close,rfl⟩ := Language.mem_mul.mp tailLegal
    rw [range_word head,range_word close]
    simp [Leading,Trailing]
  | NodeId =>
    obtain ⟨first,head,tail,_,rfl⟩ := Language.mem_mul.mp language
    obtain ⟨underscore,under,colon,col,rfl⟩ := Language.mem_mul.mp head
    rw [range_word under,range_word col]
    simp [Leading,Trailing]
private theorem token_minimum {kind : NameKind} {source : List U8} {start finish : Nat}
    (token : Token kind source start finish) : Leading kind+Trailing kind ≤ finish-start := by
  obtain ⟨word,span,language⟩ := token
  exact (minimum_word kind word language).trans (Rowl.SourceSpans.source_length span)
private theorem token_copy_iff (kind : NameKind) (source : List U8) (start finish : Nat)
    (range : start ≤ finish ∧ finish ≤ source.length) :
    Token kind source start finish ↔
      ∃ word, Rowl.Regular.Utf8From (Rowl.SourceSpans.Bytes source start finish) 0 word ∧
        word ∈ Rowl.Functional.TerminalLanguage (TerminalOf kind) := by
  unfold Token Rowl.FunctionalSelection.Candidate Rowl.Longest.Candidate
  simp_rw [Rowl.SourceSpans.utf8_source_iff source start finish _ range]

private theorem ascii_width {source : List U8} {start finish : Nat} {word : List Nat}
    (span : Rowl.Longest.Utf8Span source start finish word) (ascii : ∀ cp ∈ word, cp < 128) :
    finish = start+word.length := by
  have copied := Rowl.FunctionalIntegers.ascii_span_source span ascii
  have lengths := congrArg List.length copied
  have range := span_bounds span
  have same : Rowl.Decimal.Slice source start finish = Rowl.SourceSpans.Bytes source start finish := by
    simp [Rowl.Decimal.Slice,Rowl.SourceSpans.Bytes,List.drop_take]
  simp only [List.length_map,same,bytes_length source start finish range] at lengths
  omega

/-- Every source token has a value in the exact standard grammar after marker
    removal, including absolute IRIs and the normative language-tag subgrammar. -/
theorem payload_grammar {kind : NameKind} {source : List U8} {start finish : Nat}
    (token : Token kind source start finish) :
    ∃ word, Rowl.Regular.Utf8From (Payload kind source start finish) 0 word ∧ word ∈ ValueLanguage kind := by
  obtain ⟨word,span,language⟩ := token
  cases kind with
  | PrefixName =>
    refine ⟨word,?_,language⟩
    simpa [Payload,Leading,Trailing] using
      (Rowl.SourceSpans.utf8_source_iff source start finish word (span_bounds span)).mp span
  | AbbreviatedIri =>
    refine ⟨word,?_,language⟩
    simpa [Payload,Leading,Trailing] using
      (Rowl.SourceSpans.utf8_source_iff source start finish word (span_bounds span)).mp span
  | FullIri =>
    obtain ⟨first,head,tail,tailLegal,rfl⟩ := Language.mem_mul.mp language
    obtain ⟨iri,iriLegal,closing,close,rfl⟩ := Language.mem_mul.mp tailLegal
    rw [range_word head,range_word close] at span
    obtain ⟨begin,opening,rest⟩ := Rowl.SourceSpans.source_split [60] (iri++[62]) span
    obtain ⟨stop,body,closing⟩ := Rowl.SourceSpans.source_split iri [62] rest
    have beginValue : begin = start+1 := by simpa using ascii_width opening (by simp)
    have closingWidth := ascii_width closing (by simp)
    have stopValue : stop = finish-1 := by simp at closingWidth; omega
    refine ⟨iri,?_,iriLegal⟩
    have text := (Rowl.SourceSpans.utf8_source_iff source begin stop iri (span_bounds body)).mp body
    simpa [Payload,Leading,Trailing,beginValue,stopValue] using text
  | NodeId =>
    obtain ⟨first,head,tail,tailLegal,rfl⟩ := Language.mem_mul.mp language
    obtain ⟨underscore,under,colon,col,rfl⟩ := Language.mem_mul.mp head
    rw [range_word under,range_word col] at span
    obtain ⟨begin,opening,body⟩ := Rowl.SourceSpans.source_split [95,58] tail span
    have beginValue : begin = start+2 := by simpa using ascii_width opening (by simp)
    refine ⟨tail,?_,tailLegal⟩
    have text := (Rowl.SourceSpans.utf8_source_iff source begin finish tail (span_bounds body)).mp body
    simpa [Payload,Leading,Trailing,beginValue] using text
  | LanguageTag =>
    obtain ⟨first,head,tail,tailLegal,rfl⟩ := Language.mem_mul.mp language
    rw [range_word head] at span
    obtain ⟨begin,opening,body⟩ := Rowl.SourceSpans.source_split [64] tail span
    have beginValue : begin = start+1 := by simpa using ascii_width opening (by simp)
    refine ⟨tail,?_,tailLegal⟩
    have text := (Rowl.SourceSpans.utf8_source_iff source begin finish tail (span_bounds body)).mp body
    simpa [Payload,Leading,Trailing,beginValue] using text

/-- The actual name reader terminates, preserves exact values and obeys each
    independent source grammar/budget/diagnostic phase for arbitrary byte input. -/
theorem read_span_total_correct (kind : NameKind) (bytes : alloc.vec.Vec U8) (start finish limit : Usize) :
    ∃ result, read_span kind bytes start finish limit = .ok result ∧
      Correct kind bytes.val start.val finish.val limit.val result := by
  rw [read_span]
  by_cases reversed : finish.val < start.val
  · exact ⟨.Err (.InvalidSpan start),by simp [UScalar.lt_equiv,reversed],rfl,Or.inl reversed⟩
  · simp only [UScalar.lt_equiv,reversed,↓reduceIte]
    by_cases beyond : bytes.val.length < finish.val
    · exact ⟨.Err (.InvalidSpan start),by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,beyond],rfl,Or.inr beyond⟩
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,beyond,↓reduceIte]
      have range : start.val ≤ finish.val ∧ finish.val ≤ bytes.val.length := by omega
      obtain ⟨count,countExecuted,countCorrect⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := finish) (y := start) (by scalar_tac))
      have countValue : count.val = finish.val-start.val := countCorrect.1
      rw [countExecuted,bind_ok,leading_actual,trailing_actual,bind_ok]
      by_cases shortHead : count.val < (Head kind).val
      · refine ⟨.Err (.InvalidToken start),by simp [shortHead],rfl,range.1,range.2,?_⟩
        intro token
        have enough := token_minimum token
        have := head_value kind
        omega
      · simp only [shortHead,↓reduceIte]
        obtain ⟨rest,restExecuted,restCorrect⟩ := WP.spec_imp_exists
          (Usize.sub_spec (x := count) (y := Head kind) (by scalar_tac))
        have restValue : rest.val = count.val-Leading kind := by simpa [head_value] using restCorrect.1
        rw [restExecuted,bind_ok]
        by_cases shortTail : rest.val < (Tail kind).val
        · refine ⟨.Err (.InvalidToken start),by simp [shortTail],rfl,range.1,range.2,?_⟩
          intro token
          have enough := token_minimum token
          have := tail_value kind
          have := head_value kind
          omega
        · try simp only [UScalar.lt_equiv,shortTail,↓reduceIte]
          have enough : Leading kind+Trailing kind ≤ finish.val-start.val := by
            have := head_value kind
            have := tail_value kind
            omega
          obtain ⟨copied,copiedExecuted,copiedCorrect⟩ := Rowl.NTriples.copy_term_total_correct bytes start finish count range
          rw [copiedExecuted,bind_ok]
          cases copied with
          | Err error => have over := copiedCorrect.1; omega
          | Ok tokenBytes =>
            simp only [shortTail,↓reduceIte,bind_ok]
            rw [terminal_actual,bind_ok]
            obtain ⟨matched,matchedExecuted,matchedCorrect⟩ := Rowl.Functional.recognize_total_correct (TerminalOf kind) tokenBytes
            have equivalent : matched = .Matched true ↔ Token kind bytes.val start.val finish.val := by
              have grammar := Rowl.Functional.recognize_accepted_iff (TerminalOf kind) tokenBytes
              rw [token_copy_iff kind bytes.val start.val finish.val range]
              simpa [matchedExecuted,copiedCorrect.2,Rowl.SourceSpans.Bytes] using grammar
            rw [matchedExecuted,bind_ok]
            cases matched with
            | MalformedUtf8 error =>
              exact ⟨.Err (.InvalidToken start),by simp [bind_ok],rfl,range.1,range.2,by intro token; have impossible := equivalent.mpr token; cases impossible⟩
            | Matched accepted =>
              cases accepted with
              | false =>
                exact ⟨.Err (.InvalidToken start),by simp [bind_ok],rfl,range.1,range.2,by intro token; have impossible := equivalent.mpr token; cases impossible⟩
              | true =>
                have token := equivalent.mp rfl
                simp only [bind_ok,↓reduceIte]
                have headValue := head_value kind
                have tailValue := tail_value kind
                have size := bytes.property
                obtain ⟨begin,beginExecuted,beginCorrect⟩ := WP.spec_imp_exists
                  (Usize.add_spec (x := start) (y := Head kind) (by scalar_tac))
                obtain ⟨stop,stopExecuted,stopCorrect⟩ := WP.spec_imp_exists
                  (Usize.sub_spec (x := finish) (y := Tail kind) (by scalar_tac))
                have beginValue : begin.val = start.val+Leading kind := by simpa [head_value] using beginCorrect
                have stopValue : stop.val = finish.val-Trailing kind := by simpa [tail_value] using stopCorrect.1
                have bodyRange : begin.val ≤ stop.val ∧ stop.val ≤ bytes.val.length := by omega
                have payloadLength : (Payload kind bytes.val start.val finish.val).length = stop.val-begin.val := by
                  simpa [Payload,beginValue,stopValue] using bytes_length bytes.val begin.val stop.val bodyRange
                obtain ⟨result,executed,correct⟩ := Rowl.NTriples.copy_term_total_correct bytes begin stop limit bodyRange
                cases result with
                | Ok value =>
                  refine ⟨.Ok value,by simp [beginExecuted,stopExecuted,executed],token,?_,?_⟩
                  · rw [payloadLength]; exact correct.1
                  · simpa [Payload,Rowl.SourceSpans.Bytes,beginValue,stopValue] using correct.2
                | Err error =>
                  exact ⟨.Err (.ResourceLimit error.offset),by simp [beginExecuted,stopExecuted,executed],
                    by simpa [beginValue] using correct.2.2,token,by simpa [payloadLength] using correct.1⟩

private theorem source_excludes_error (kind : NameKind) (source : List U8) (start finish limit : Nat)
    (token : Token kind source start finish) (fits : (Payload kind source start finish).length ≤ limit)
    (error : NameError) (correct : ErrorCorrect kind source start finish limit error) : False := by
  have bounds := token_bounds token
  cases error with
  | InvalidSpan offset => rcases correct.2 with reversed | beyond; omega; omega
  | InvalidToken offset => exact correct.2.2.2 token
  | ResourceLimit offset => have := correct.2.2; omega

/-- Actual acceptance is precisely a grammar-valid source token whose full
    unchanged payload fits, and returns exactly that original value. -/
theorem read_span_accepted_iff (kind : NameKind) (bytes : alloc.vec.Vec U8)
    (start finish limit : Usize) (value : alloc.vec.Vec U8) :
    read_span kind bytes start finish limit = .ok (.Ok value) ↔
      Token kind bytes.val start.val finish.val ∧ (Payload kind bytes.val start.val finish.val).length ≤ limit.val ∧
      value.val = Payload kind bytes.val start.val finish.val := by
  obtain ⟨result,executed,correct⟩ := read_span_total_correct kind bytes start finish limit
  constructor
  · intro accepted
    have same := Result.ok_injective (executed.symm.trans accepted)
    simpa [same,Correct] using correct
  · rintro ⟨token,fits,contents⟩
    cases result with
    | Ok actual =>
      have same : actual = value := (alloc.vec.Vec.eq_iff actual value).mpr (correct.2.2.trans contents.symm)
      simpa [same] using executed
    | Err error => exact False.elim (source_excludes_error _ _ _ _ _ token fits error correct)

/-- No additional numeric/token-size restriction is imposed beyond the caller
    payload byte budget and the complete independent source terminal grammar. -/
theorem read_span_accepts_iff (kind : NameKind) (bytes : alloc.vec.Vec U8) (start finish limit : Usize) :
    (∃ value, read_span kind bytes start finish limit = .ok (.Ok value)) ↔
      Token kind bytes.val start.val finish.val ∧ (Payload kind bytes.val start.val finish.val).length ≤ limit.val := by
  constructor
  · rintro ⟨value,executed⟩
    have correct := (read_span_accepted_iff kind bytes start finish limit value).mp executed
    exact ⟨correct.1,correct.2.1⟩
  · rintro ⟨token,fits⟩
    obtain ⟨result,executed,correct⟩ := read_span_total_correct kind bytes start finish limit
    cases result with
    | Ok value => exact ⟨value,executed⟩
    | Err error => exact False.elim (source_excludes_error _ _ _ _ _ token fits error correct)

/-- Actual successful values obey their complete independent value grammar,
    not just a raw byte-copy contract. -/
theorem read_value_grammar (kind : NameKind) (bytes : alloc.vec.Vec U8) (start finish limit : Usize)
    (value : alloc.vec.Vec U8) (accepted : read_span kind bytes start finish limit = .ok (.Ok value)) :
    ∃ word, Rowl.Regular.Utf8From value.val 0 word ∧ word ∈ ValueLanguage kind := by
  have correct := (read_span_accepted_iff kind bytes start finish limit value).mp accepted
  simpa [← correct.2.2] using payload_grammar correct.1

private theorem error_unique (kind : NameKind) (source : List U8) (start finish limit : Nat)
    (one two : NameError) (first : ErrorCorrect kind source start finish limit one)
    (second : ErrorCorrect kind source start finish limit two) : one = two := by
  cases one with
  | InvalidSpan offset =>
    cases two with
    | InvalidSpan other =>
      have same := UScalar.eq_of_val_eq (first.1.trans second.1.symm)
      simp [same]
    | InvalidToken other => rcases first.2 with reversed | beyond; have := second.2.1; omega; have := second.2.2.1; omega
    | ResourceLimit other => have bounded := token_bounds second.2.1; rcases first.2 with reversed | beyond; omega; omega
  | InvalidToken offset =>
    cases two with
    | InvalidSpan other => rcases second.2 with reversed | beyond; have := first.2.1; omega; have := first.2.2.1; omega
    | InvalidToken other =>
      have same := UScalar.eq_of_val_eq (first.1.trans second.1.symm)
      simp [same]
    | ResourceLimit other => exact False.elim (first.2.2.2 second.2.1)
  | ResourceLimit offset =>
    cases two with
    | InvalidSpan other => have bounded := token_bounds first.2.1; rcases second.2 with reversed | beyond; omega; omega
    | InvalidToken other => exact False.elim (second.2.2.2 first.2.1)
    | ResourceLimit other =>
      have same := UScalar.eq_of_val_eq (first.1.trans second.1.symm)
      simp [same]

/-- Both directions of every exact source/grammar/budget rejection phase. -/
theorem read_span_error_iff (kind : NameKind) (bytes : alloc.vec.Vec U8) (start finish limit : Usize) (error : NameError) :
    read_span kind bytes start finish limit = .ok (.Err error) ↔
      ErrorCorrect kind bytes.val start.val finish.val limit.val error := by
  obtain ⟨result,executed,correct⟩ := read_span_total_correct kind bytes start finish limit
  constructor
  · intro rejected
    have same := Result.ok_injective (executed.symm.trans rejected)
    simpa [same,Correct] using correct
  · intro sourceError
    cases result with
    | Ok value => exact False.elim (source_excludes_error _ _ _ _ _ correct.1 correct.2.1 error sourceError)
    | Err actual =>
      have same := error_unique _ _ _ _ _ actual error correct sourceError
      simpa [same] using executed

/-- A name kind and all its original span/grammar facts are derived from the
    actual greatest-selected token. A fitting value budget supplies its value. -/
theorem selected_name_value (kind : NameKind) (bytes : alloc.vec.Vec U8) (start limit : Usize)
    (token : functional.Token) (family : token.terminal = TerminalOf kind)
    (selected : functional.next_terminal bytes start = .ok (.Token token))
    (fits : (Payload kind bytes.val token.start.val token.end.val).length ≤ limit.val) :
    ∃ value, read_span kind bytes token.start token.end limit = .ok (.Ok value) ∧
      value.val = Payload kind bytes.val token.start.val token.end.val := by
  have greatest := (Rowl.FunctionalDisjointness.next_terminal_greatest_iff bytes start token).mp selected
  have candidate : Token kind bytes.val token.start.val token.end.val := by
    simpa [Token,greatest.2.1,family] using greatest.2.2.1
  obtain ⟨value,executed⟩ := (read_span_accepts_iff kind bytes token.start token.end limit).mpr ⟨candidate,fits⟩
  exact ⟨value,executed,((read_span_accepted_iff kind bytes token.start token.end limit value).mp executed).2.2⟩

/-- All five name-bearing families throughout a complete emitted stream
    supply their exact values whenever each original payload fits the budget. -/
def NameValues (bytes : alloc.vec.Vec U8) (limit : Usize) : functional_lexer.Tokens → Prop
  | .Empty => True
  | .Cons token tail =>
      (∀ kind, token.terminal = TerminalOf kind →
        (Payload kind bytes.val token.start.val token.end.val).length ≤ limit.val →
        ∃ value, read_span kind bytes token.start token.end limit = .ok (.Ok value) ∧
          value.val = Payload kind bytes.val token.start.val token.end.val) ∧ NameValues bytes limit tail
private theorem stream_values (bytes : alloc.vec.Vec U8) (limit : Usize) (lower : Nat) (tokens : functional_lexer.Tokens)
    (stream : Rowl.FunctionalLexer.Stream bytes.val lower tokens) : NameValues bytes limit tokens := by
  induction tokens generalizing lower with
  | Empty => trivial
  | Cons token tail ih =>
    refine ⟨?_,ih token.end.val stream.2.2.2.2.2⟩
    intro kind family fits
    have candidate : Token kind bytes.val token.start.val token.end.val := by
      simpa [Token,family] using stream.2.2.2.2.1
    obtain ⟨value,executed⟩ := (read_span_accepts_iff kind bytes token.start token.end limit).mpr ⟨candidate,fits⟩
    exact ⟨value,executed,((read_span_accepted_iff kind bytes token.start token.end limit value).mp executed).2.2⟩

/-- Complete actual byte lexing supplies the source grammar and endpoint facts
    for every nonquoted name payload, without trusting caller token metadata. -/
theorem lex_name_values (bytes : alloc.vec.Vec U8) (tokenLimit valueLimit : Usize) (tokens : functional_lexer.Tokens)
    (accepted : functional_lexer.lex bytes tokenLimit = .ok (.Tokens tokens)) : NameValues bytes valueLimit tokens := by
  exact stream_values bytes valueLimit 0 tokens ((Rowl.FunctionalLexer.lex_tokens_properties bytes tokenLimit tokens accepted).2)

end Rowl.FunctionalNames
