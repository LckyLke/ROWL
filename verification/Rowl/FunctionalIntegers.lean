import Rowl.Decimal
import Rowl.FunctionalDisjointness
import Rowl.FunctionalLexer

namespace Rowl.FunctionalIntegers
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open Rowl.Unicode
open scoped Computability
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

private theorem prefix_ascii {bs : List U8} {position cp width : Nat}
    (unit : Prefix bs position = some (cp,width)) (ascii : cp < 128) :
    width = 1 ∧ ∃ byte, bs[position]? = some byte ∧ byte.val = cp := by
  unfold Prefix at unit
  cases first : bs[position]? with
  | none => simp [first] at unit
  | some a =>
    simp only [first,Option.bind_some,Option.bind_eq_bind] at unit
    by_cases small : a.val < 128
    · try simp only [small,↓reduceIte] at unit
      have same := Prod.mk.inj (Option.some.inj unit)
      exact ⟨same.2.symm,a,rfl,same.1⟩
    · try simp only [small,↓reduceIte] at unit
      by_cases pairLead : a.val < 224
      · simp only [pairLead,↓reduceIte] at unit
        cases second : bs[position+1]? with
        | none => simp [second] at unit
        | some b =>
          simp only [second,Option.bind_some,Option.bind_eq_bind] at unit
          by_cases legal : Pair a.val b.val
          · simp only [legal,↓reduceIte] at unit
            have same := Prod.mk.inj (Option.some.inj unit)
            have lower := ((byte_grammar_scalar_ranges a.val b.val 0 0).1 legal).1
            omega
          · simp [legal] at unit
      · simp only [pairLead,↓reduceIte] at unit
        by_cases tripleLead : a.val < 240
        · simp only [tripleLead,↓reduceIte] at unit
          cases second : bs[position+1]? with
          | none => simp [second] at unit
          | some b =>
            simp only [second,Option.bind_some,Option.bind_eq_bind] at unit
            cases third : bs[position+2]? with
            | none => simp [third] at unit
            | some c =>
              simp only [third,Option.bind_some,Option.bind_eq_bind] at unit
              by_cases legal : Triple a.val b.val c.val
              · simp only [legal,↓reduceIte] at unit
                have same := Prod.mk.inj (Option.some.inj unit)
                have lower := (byte_grammar_scalar_ranges a.val b.val c.val 0).2.1 legal
                omega
              · simp [legal] at unit
        · simp only [tripleLead,↓reduceIte] at unit
          cases second : bs[position+1]? with
          | none => simp [second] at unit
          | some b =>
            simp only [second,Option.bind_some,Option.bind_eq_bind] at unit
            cases third : bs[position+2]? with
            | none => simp [third] at unit
            | some c =>
              simp only [third,Option.bind_some,Option.bind_eq_bind] at unit
              cases fourth : bs[position+3]? with
              | none => simp [fourth] at unit
              | some d =>
                simp only [fourth,Option.bind_some,Option.bind_eq_bind] at unit
                by_cases legal : Quad a.val b.val c.val d.val
                · simp only [legal,↓reduceIte] at unit
                  have same := Prod.mk.inj (Option.some.inj unit)
                  have lower := ((byte_grammar_scalar_ranges a.val b.val c.val d.val).2.2 legal).1
                  omega
                · simp [legal] at unit
private theorem span_bounds {bs : List U8} {start finish : Nat} {word : List Nat}
    (span : Rowl.Longest.Utf8Span bs start finish word) : start ≤ finish ∧ finish ≤ bs.length := by
  induction span with
  | empty bounded => exact ⟨le_rfl,bounded⟩
  | character _ positive _ _ ih => constructor <;> omega
private theorem slice_step (bs : List U8) (start finish : Nat)
    (before : start < finish) (fits : finish ≤ bs.length) :
    Rowl.Decimal.Slice bs start finish = bs[start]'(by omega)::Rowl.Decimal.Slice bs (start+1) finish := by
  have inside : start < (bs.take finish).length := by simp; omega
  rw [Rowl.Decimal.Slice,List.drop_eq_getElem_cons inside]
  simp only [List.getElem_take]
  rfl

/-- Every canonical all-ASCII source segment is exactly its original byte values,
    with no hidden multibyte/overlong encoding or normalization assumption. -/
theorem ascii_span_source {bs : List U8} {start finish : Nat} {word : List Nat}
    (span : Rowl.Longest.Utf8Span bs start finish word) (ascii : ∀ cp ∈ word, cp < 128) :
    (Rowl.Decimal.Slice bs start finish).map UScalar.val = word := by
  induction span with
  | empty bounded => simp [Rowl.Decimal.Slice,List.drop_take]
  | @character start cp width finish tail unit positive fits rest ih =>
    have headAscii : cp < 128 := ascii cp (by simp)
    obtain ⟨widthIs,byte,lookup,byteValue⟩ := prefix_ascii unit headAscii
    subst width
    have bounds := span_bounds rest
    rw [slice_step _ _ _ (by omega) (by omega),List.map_cons]
    have headValue : bs[start]'(by omega) = byte := Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans lookup)
    rw [headValue,byteValue,ih (by intro value member; exact ascii value (by simp [member]))]

/-- Mathematical decimal positional interpretation of codepoint words. -/
def WordValue (word : List Nat) : Nat := word.foldl (fun value cp => 10*value+(cp-48)) 0

private theorem digit_language {word : List Nat} (accepted : word ∈ Rowl.Functional.IntegerLanguage) :
    word ≠ [] ∧ ∀ cp ∈ word, 48 ≤ cp ∧ cp ≤ 57 := by
  obtain ⟨first,firstLegal,rest,restLegal,rfl⟩ := Language.mem_mul.mp accepted
  obtain ⟨cp,rfl,lower,upper⟩ := firstLegal
  obtain ⟨parts,rfl,legal⟩ := Language.mem_kstar.mp restLegal
  refine ⟨by simp,?_⟩
  intro value member
  rcases List.mem_cons.mp member with rfl | inside
  · exact ⟨lower,upper⟩
  · obtain ⟨part,included,contained⟩ := List.mem_flatten.mp inside
    obtain ⟨scalar,rfl,scalarLower,scalarUpper⟩ := legal part included
    have same : value = scalar := by simpa using contained
    simpa [same] using And.intro scalarLower scalarUpper

private theorem flatten_singletons (word : List Nat) :
    (word.map (fun value => [value])).flatten = word := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
    change head::(tail.map (fun value => [value])).flatten = head::tail
    rw [ih]

/-- The normative integer terminal is exactly a nonempty word of ASCII digits. -/
theorem integer_language_iff (word : List Nat) : word ∈ Rowl.Functional.IntegerLanguage ↔
    word ≠ [] ∧ ∀ cp ∈ word, 48 ≤ cp ∧ cp ≤ 57 := by
  constructor
  · exact digit_language
  · rintro ⟨nonempty,digits⟩
    cases word with
    | nil => exact False.elim (nonempty rfl)
    | cons cp tail =>
      apply Language.mem_mul.mpr
      refine ⟨[cp],⟨cp,rfl,(digits cp (by simp)).1,(digits cp (by simp)).2⟩,tail,?_,rfl⟩
      apply Language.mem_kstar.mpr
      refine ⟨tail.map (fun value => [value]),(flatten_singletons tail).symm,?_⟩
      intro part member
      obtain ⟨value,included,rfl⟩ := List.mem_map.mp member
      exact ⟨value,rfl,(digits value (List.mem_cons_of_mem _ included)).1,(digits value (List.mem_cons_of_mem _ included)).2⟩

private theorem digits_map (bytes : List U8) : Rowl.Decimal.Digits bytes ↔
    ∀ cp ∈ bytes.map UScalar.val, 48 ≤ cp ∧ cp ≤ 57 := by
  simp [Rowl.Decimal.Digits,Rowl.Decimal.Digit]

private theorem digits_span (bytes : List U8) (start finish : Nat)
    (range : start ≤ finish ∧ finish ≤ bytes.length)
    (digits : Rowl.Decimal.Digits (Rowl.Decimal.Slice bytes start finish)) :
    Rowl.Longest.Utf8Span bytes start finish
      ((Rowl.Decimal.Slice bytes start finish).map UScalar.val) := by
  by_cases atEnd : start = finish
  · subst finish
    simpa [Rowl.Decimal.Slice,List.drop_take] using (Rowl.Longest.Utf8Span.empty range.2)
  · have before : start < finish := by omega
    have inside : start < bytes.length := by omega
    have step := slice_step bytes start finish before range.2
    have headDigit : Rowl.Decimal.Digit bytes[start] := by
      apply digits
      simp [step]
    have headAscii : bytes[start].val < 128 := by have := headDigit.2; omega
    have unit : Prefix bytes start = some (bytes[start].val,1) := by
      simp [Prefix,List.getElem?_eq_getElem inside,headAscii]
    have tailDigits : Rowl.Decimal.Digits (Rowl.Decimal.Slice bytes (start+1) finish) := by
      intro byte member
      exact digits byte (by simp [step,member])
    have rest := digits_span bytes (start+1) finish ⟨by omega,range.2⟩ tailDigits
    rw [step,List.map_cons]
    exact .character unit (by omega) (by omega) rest
termination_by finish-start
decreasing_by omega

/-- Canonical byte candidates for the normative OWL integer terminal are
    exactly bounded, nonempty spans of the original ASCII digit bytes. -/
theorem integer_candidate_iff (bytes : List U8) (start finish : Nat) :
    Rowl.FunctionalSelection.Candidate bytes start .Integer finish ↔
      start < finish ∧ finish ≤ bytes.length ∧
      Rowl.Decimal.Digits (Rowl.Decimal.Slice bytes start finish) := by
  constructor
  · rintro ⟨word,span,language⟩
    have integer : word ∈ Rowl.Functional.IntegerLanguage := language
    obtain ⟨nonempty,digits⟩ := (integer_language_iff word).mp integer
    have exactBytes := ascii_span_source span (by intro cp member; have := (digits cp member).2; omega)
    have bounds := span_bounds span
    have nonemptyBytes : Rowl.Decimal.Slice bytes start finish ≠ [] := by
      intro empty
      simp [empty] at exactBytes
      exact nonempty exactBytes
    have nonemptyLength := List.length_pos_iff_ne_nil.mpr nonemptyBytes
    have positive : start < finish := by
      simp only [Rowl.Decimal.Slice,List.length_drop,List.length_take] at nonemptyLength
      omega
    exact ⟨positive,bounds.2,(digits_map _).mpr (by simpa [exactBytes] using digits)⟩
  · rintro ⟨nonempty,fits,digits⟩
    refine ⟨(Rowl.Decimal.Slice bytes start finish).map UScalar.val,digits_span bytes start finish ⟨by omega,fits⟩ digits,?_⟩
    apply (integer_language_iff _).mpr
    refine ⟨?_,(digits_map _).mp digits⟩
    intro empty
    have sameLength := congrArg List.length empty
    simp only [List.length_map,Rowl.Decimal.Slice,List.length_drop,List.length_take,List.length_nil] at sameLength
    omega

private theorem numeric_word (bytes : List U8) :
    Rowl.Decimal.Numeric bytes 0 = WordValue (bytes.map UScalar.val) := by
  simp [Rowl.Decimal.Numeric,WordValue,List.foldl_map]

/-- Actual Rust digit reading and the independent Functional Syntax candidate
    coincide in both directions; accepted values are the exact positional value
    of the canonical source word, with no additional numeric-size restriction. -/
theorem read_integer_iff (bytes : alloc.vec.Vec U8) (start finish : Usize) (value : RowlRust.probes.Natural) :
    RowlRust.decimal.read_span bytes start finish = .ok (.Ok value) ↔
      ∃ word, Rowl.Longest.Utf8Span bytes.val start.val finish.val word ∧
        word ∈ Rowl.Functional.IntegerLanguage ∧ Rowl.Probes.naturalValue value = WordValue word := by
  constructor
  · intro executed
    obtain ⟨nonempty,fits,digits,correct⟩ := (Rowl.Decimal.read_span_accepted_iff bytes start finish value).mp executed
    have candidate := (integer_candidate_iff bytes.val start.val finish.val).mpr ⟨nonempty,fits,digits⟩
    obtain ⟨word,span,language⟩ := candidate
    have integer : word ∈ Rowl.Functional.IntegerLanguage := language
    have allDigits := ((integer_language_iff word).mp integer).2
    have exactBytes := ascii_span_source span (by intro cp member; have := (allDigits cp member).2; omega)
    refine ⟨word,span,integer,?_⟩
    rw [correct,numeric_word,exactBytes]
  · rintro ⟨word,span,language,correct⟩
    have candidate : Rowl.FunctionalSelection.Candidate bytes.val start.val .Integer finish.val := ⟨word,span,language⟩
    obtain ⟨nonempty,fits,digits⟩ := (integer_candidate_iff bytes.val start.val finish.val).mp candidate
    have allDigits := ((integer_language_iff word).mp language).2
    have exactBytes := ascii_span_source span (by intro cp member; have := (allDigits cp member).2; omega)
    apply (Rowl.Decimal.read_span_accepted_iff bytes start finish value).mpr
    refine ⟨nonempty,fits,digits,?_⟩
    rw [numeric_word,exactBytes]
    exact correct

/-- Every actual greatest-selected integer token has a successful exact value
    at its original endpoints. Token kind, range and digits are derived from the
    actual selector result rather than trusted caller-supplied span metadata. -/
theorem selected_integer_value (bytes : alloc.vec.Vec U8) (start : Usize)
    (token : functional.Token) (integer : token.terminal = .Integer)
    (selected : functional.next_terminal bytes start = .ok (.Token token)) :
    ∃ value word, RowlRust.decimal.read_span bytes token.start token.end = .ok (.Ok value) ∧
      Rowl.Longest.Utf8Span bytes.val token.start.val token.end.val word ∧
      word ∈ Rowl.Functional.IntegerLanguage ∧ Rowl.Probes.naturalValue value = WordValue word := by
  have greatest := (Rowl.FunctionalDisjointness.next_terminal_greatest_iff bytes start token).mp selected
  have candidate : Rowl.FunctionalSelection.Candidate bytes.val token.start.val .Integer token.end.val := by
    simpa [greatest.2.1,integer] using greatest.2.2.1
  have grammar := (integer_candidate_iff bytes.val token.start.val token.end.val).mp candidate
  obtain ⟨value,executed⟩ := (Rowl.Decimal.read_span_accepts_iff bytes token.start token.end).mpr grammar
  obtain ⟨word,span,language,correct⟩ := (read_integer_iff bytes token.start token.end value).mp executed
  exact ⟨value,word,executed,span,language,correct⟩

/-- All integer tokens in a complete emitted stream admit their exact values
    at the original source spans. This does not construct a document AST. -/
def IntegerValues (bytes : alloc.vec.Vec U8) : functional_lexer.Tokens → Prop
  | .Empty => True
  | .Cons token tail =>
      (token.terminal = .Integer →
        ∃ value word, RowlRust.decimal.read_span bytes token.start token.end = .ok (.Ok value) ∧
          Rowl.Longest.Utf8Span bytes.val token.start.val token.end.val word ∧
          word ∈ Rowl.Functional.IntegerLanguage ∧ Rowl.Probes.naturalValue value = WordValue word) ∧
      IntegerValues bytes tail
private theorem stream_values (bytes : alloc.vec.Vec U8) (lower : Nat) (tokens : functional_lexer.Tokens)
    (stream : Rowl.FunctionalLexer.Stream bytes.val lower tokens) : IntegerValues bytes tokens := by
  induction tokens generalizing lower with
  | Empty => trivial
  | Cons token tail ih =>
    refine ⟨?_,ih token.end.val stream.2.2.2.2.2⟩
    intro integer
    have candidate : Rowl.FunctionalSelection.Candidate bytes.val token.start.val .Integer token.end.val := by
      simpa [integer] using stream.2.2.2.2.1
    have grammar := (integer_candidate_iff bytes.val token.start.val token.end.val).mp candidate
    obtain ⟨value,executed⟩ := (Rowl.Decimal.read_span_accepts_iff bytes token.start token.end).mpr grammar
    obtain ⟨word,span,language,correct⟩ := (read_integer_iff bytes token.start token.end value).mp executed
    exact ⟨value,word,executed,span,language,correct⟩

/-- Complete actual byte lexing supplies all integer source evidence required
    for successful exact decimal interpretation throughout the emitted stream. -/
theorem lex_integer_values (bytes : alloc.vec.Vec U8) (limit : Usize) (tokens : functional_lexer.Tokens)
    (accepted : functional_lexer.lex bytes limit = .ok (.Tokens tokens)) : IntegerValues bytes tokens := by
  exact stream_values bytes 0 tokens ((Rowl.FunctionalLexer.lex_tokens_properties bytes limit tokens accepted).2)

end Rowl.FunctionalIntegers
