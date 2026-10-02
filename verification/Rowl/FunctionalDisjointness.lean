import Rowl.FunctionalSelection

namespace Rowl.FunctionalDisjointness
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.functional
open Rowl.Functional Rowl.Names
open scoped Computability
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

-- A proof-only family discriminator. Its arguments are mathematical codepoint
-- words; the actual lexer does not execute this classification.
private def family : Terminal → Nat
  | .Keyword _ => 0
  | .Open => 1
  | .Close => 2
  | .Equals => 3
  | .DatatypeIndicator => 4
  | .Integer => 5
  | .QuotedString => 6
  | .LanguageTag => 7
  | .NodeId => 8
  | .FullIri => 9
  | .PrefixName => 10
  | .AbbreviatedIri => 11
  | .Whitespace => 12
  | .Comment => 13
private def shape (word : List Nat) : Nat :=
  match word.head? with
  | none => 14
  | some cp =>
    if cp == 40 then 1 else if cp == 41 then 2 else if cp == 61 then 3 else
    if cp == 94 then 4 else if decide (48 ≤ cp ∧ cp ≤ 57) then 5 else
    if cp == 34 then 6 else if cp == 64 then 7 else if cp == 95 then 8 else
    if cp == 60 then 9 else if cp == 32 || cp == 9 || cp == 10 || cp == 13 then 12 else
    if cp == 35 then 13 else if word.contains 58 then
      if word.getLast? == some 58 then 10 else 11
    else 0
private theorem keyword_shape (key : Keyword) : shape (KeywordWord key) = 0 := by
  cases key <;> decide


private theorem range_word {word : List Nat} {cp : Nat}
    (accepted : word ∈ Rowl.Iri.Range cp cp) : word = [cp] := by
  obtain ⟨value,rfl,lower,upper⟩ := accepted
  have same : value = cp := by omega
  simp [same]
private theorem single_prefix {word : List Nat} {cp : Nat} {language : Language Nat}
    (accepted : word ∈ Rowl.Iri.Range cp cp * language) : ∃ tail, word = cp::tail := by
  obtain ⟨first,firstLegal,tail,_,rfl⟩ := Language.mem_mul.mp accepted
  rw [range_word firstLegal]
  exact ⟨tail,rfl⟩
private theorem all_mul (a b : Language Nat) (predicate : Nat → Prop)
    (first : ∀ word ∈ a, ∀ cp ∈ word, predicate cp)
    (second : ∀ word ∈ b, ∀ cp ∈ word, predicate cp) :
    ∀ word ∈ a*b, ∀ cp ∈ word, predicate cp := by
  rintro word ⟨left,leftLegal,right,rightLegal,rfl⟩ cp member
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact first left leftLegal cp leftMember
  · exact second right rightLegal cp rightMember
private theorem all_star (a : Language Nat) (predicate : Nat → Prop)
    (part : ∀ word ∈ a, ∀ cp ∈ word, predicate cp) : ∀ word ∈ a∗, ∀ cp ∈ word, predicate cp := by
  rintro word ⟨parts,rfl,legal⟩ cp member
  obtain ⟨item,included,contained⟩ := List.mem_flatten.mp member
  exact part item (legal item included) cp contained
private theorem chars_no_colon : ∀ word ∈ Chars, ∀ cp ∈ word, cp ≠ 58 := by
  intro word legal cp member
  simp only [Chars,CharsU,Language.mem_add] at legal
  rcases legal with ((base | underscore) | (dash | (digit | (middle | (combining | connector)))))
  · obtain ⟨value,rfl,base⟩ := base
    have same : cp = value := by simpa using member
    subst cp
    simp only [BaseCode] at base
    omega
  all_goals
    obtain ⟨value,rfl,lower,upper⟩ := ‹word ∈ Rowl.Iri.Range _ _›
    have same : cp = value := by simpa using member
    subst cp
    omega
private theorem ending_no_colon : ∀ word ∈ Ending, ∀ cp ∈ word, cp ≠ 58 := by
  intro word legal cp member
  rcases (Language.mem_add _ _ word).mp legal with empty | ending
  · have same : word = [] := empty
    simp [same] at member
  · apply all_mul _ _ (fun value => value ≠ 58) ?_ chars_no_colon word ending cp member
    apply all_star
    intro word legal cp member
    rcases (Language.mem_add _ _ word).mp legal with nameChars | dot
    · exact chars_no_colon word nameChars cp member
    · obtain ⟨value,rfl,lower,upper⟩ := dot
      have same : cp = value := by simpa using member
      subst cp
      omega
private theorem local_no_colon : ∀ word ∈ Local, ∀ cp ∈ word, cp ≠ 58 := by
  apply all_mul _ _ (fun cp => cp ≠ 58) ?_ ending_no_colon
  intro word legal cp member
  rcases (Language.mem_add _ _ word).mp legal with baseOrU | digit
  · exact chars_no_colon word (Or.inl baseOrU) cp member
  · obtain ⟨value,rfl,lower,upper⟩ := digit
    have same : cp = value := by simpa using member
    subst cp
    omega
private theorem local_nonempty {word : List Nat} (legal : word ∈ Local) : word ≠ [] := by
  obtain ⟨first,firstLegal,rest,_,rfl⟩ := Language.mem_mul.mp legal
  rcases (Language.mem_add _ _ first).mp firstLegal with baseOrU | digit
  · rcases (Language.mem_add _ _ first).mp baseOrU with base | underscore
    · obtain ⟨value,rfl,_⟩ := base; simp
    · obtain ⟨value,rfl,_,_⟩ := underscore; simp
  · obtain ⟨value,rfl,_,_⟩ := digit; simp

private theorem prefix_decompose {word : List Nat} (legal : word ∈ Prefix) :
    ∃ label, word = label++[58] ∧ (label = [] ∨ ∃ head tail, label = head::tail ∧ BaseCode head) := by
  obtain ⟨label,labelLegal,colon,colonLegal,rfl⟩ := Language.mem_mul.mp legal
  rw [range_word colonLegal]
  refine ⟨label,rfl,?_⟩
  rcases (Language.mem_add _ _ label).mp labelLegal with empty | named
  · exact Or.inl empty
  · obtain ⟨base,baseLegal,tail,_,rfl⟩ := Language.mem_mul.mp named
    obtain ⟨head,rfl,headLegal⟩ := baseLegal
    exact Or.inr ⟨head,tail,rfl,headLegal⟩
private theorem name_shape (head : Nat) (tail : List Nat) (legal : BaseCode head ∨ head = 58) :
    shape (head::tail) = if (head::tail).contains 58 then
      if (head::tail).getLast? == some 58 then 10 else 11
    else 0 := by
  have exclude : head ≠ 40 ∧ head ≠ 41 ∧ head ≠ 61 ∧ head ≠ 94 ∧ ¬ (48 ≤ head ∧ head ≤ 57) ∧
      head ≠ 34 ∧ head ≠ 64 ∧ head ≠ 95 ∧ head ≠ 60 ∧ head ≠ 32 ∧ head ≠ 9 ∧ head ≠ 10 ∧ head ≠ 13 ∧ head ≠ 35 := by
    rcases legal with base | colon
    · simp only [BaseCode] at base; omega
    · omega
  simp [shape,exclude]
private theorem prefix_shape {word : List Nat} (legal : word ∈ Prefix) : shape word = 10 := by
  obtain ⟨label,rfl,form⟩ := prefix_decompose legal
  have contains : (label++[58]).contains 58 = true := by simp
  have last : (label++[58]).getLast? = some 58 := by simp
  rcases form with rfl | ⟨head,tail,rfl,base⟩
  · decide
  · rw [List.cons_append,name_shape head (tail++[58]) (Or.inl base)]
    simp only [List.cons_append] at contains last
    simp only [contains,beq_iff_eq,last,↓reduceIte]
private theorem abbreviated_shape {word : List Nat} (legal : word ∈ Abbreviated) : shape word = 11 := by
  obtain ⟨namespaceWord,prefixLegal,localWord,localLegal,rfl⟩ := Language.mem_mul.mp legal
  obtain ⟨label,rfl,form⟩ := prefix_decompose prefixLegal
  have nonempty := local_nonempty localLegal
  have notColon : localWord.getLast? ≠ some 58 := by
    intro same
    have member : 58 ∈ localWord := List.mem_of_getLast? same
    exact local_no_colon localWord localLegal 58 member rfl
  have contains : ((label++[58])++localWord).contains 58 = true := by simp
  have last : ((label++[58])++localWord).getLast? ≠ some 58 := by
    rw [List.getLast?_append]
    cases lastValue : localWord.getLast? with
    | none =>
      have empty : localWord = [] := List.getLast?_eq_none_iff.mp lastValue
      contradiction
    | some value =>
      simpa only [Option.or] using (show some value ≠ some 58 from by simpa [lastValue] using notColon)
  rcases form with rfl | ⟨head,tail,rfl,base⟩
  · change shape (58::localWord) = 11
    rw [name_shape 58 localWord (Or.inr rfl)]
    change (58::localWord).getLast? ≠ some 58 at last
    simp only [List.contains_cons,beq_self_eq_true,Bool.true_or,beq_iff_eq,last,↓reduceIte]
  · rw [List.cons_append,List.cons_append,name_shape head ((tail++[58])++localWord) (Or.inl base)]
    simp only [List.cons_append] at contains last
    simp only [contains,beq_iff_eq,last,↓reduceIte]

private theorem terminal_shape (terminal : Terminal) (word : List Nat)
    (accepted : word ∈ TerminalLanguage terminal) : shape word = family terminal := by
  cases terminal with
  | Keyword key =>
    change word = KeywordWord key at accepted
    subst word
    exact keyword_shape key
  | Open => rw [range_word accepted]; rfl
  | Close => rw [range_word accepted]; rfl
  | Equals => rw [range_word accepted]; rfl
  | DatatypeIndicator =>
    obtain ⟨tail,rfl⟩ := single_prefix accepted
    simp [shape,family]
  | Integer =>
    obtain ⟨first,firstLegal,tail,_,rfl⟩ := Language.mem_mul.mp accepted
    obtain ⟨cp,rfl,lower,upper⟩ := firstLegal
    have outside : cp ≠ 40 ∧ cp ≠ 41 ∧ cp ≠ 61 ∧ cp ≠ 94 := by omega
    simp [shape,family,outside,lower,upper]
  | QuotedString =>
    obtain ⟨tail,rfl⟩ := single_prefix accepted
    simp [shape,family]
  | LanguageTag =>
    obtain ⟨tail,rfl⟩ := single_prefix accepted
    simp [shape,family]
  | NodeId =>
    change word ∈ (Rowl.Iri.Range 95 95 * Rowl.Iri.Range 58 58) * Local at accepted
    rw [mul_assoc] at accepted
    obtain ⟨tail,rfl⟩ := single_prefix accepted
    simp [shape,family]
  | FullIri =>
    obtain ⟨tail,rfl⟩ := single_prefix accepted
    simp [shape,family]
  | PrefixName => exact prefix_shape accepted
  | AbbreviatedIri => exact abbreviated_shape accepted
  | Whitespace =>
    obtain ⟨first,firstLegal,tail,_,rfl⟩ := Language.mem_mul.mp accepted
    rcases firstLegal with rfl | rfl | rfl | rfl <;> simp [shape,family]
  | Comment =>
    obtain ⟨tail,rfl⟩ := single_prefix accepted
    simp [shape,family]

/-- Distinct terminal kinds have disjoint complete codepoint languages. This
    covers all 71 keywords, punctuation, variable and special terminal classes;
    it does not assume an inventory priority or restrict Unicode words. -/
theorem terminal_language_unique (one two : Terminal) (word : List Nat)
    (first : word ∈ TerminalLanguage one) (second : word ∈ TerminalLanguage two) : one = two := by
  have sameFamily : family one = family two := (terminal_shape one word first).symm.trans (terminal_shape two word second)
  cases one <;> cases two <;> simp only [family] at sameFamily
  all_goals try contradiction
  all_goals try rfl
  rename_i one two
  change word = KeywordWord one at first
  change word = KeywordWord two at second
  have same := keyword_words_injective one two (first.symm.trans second)
  simp [same]

private theorem span_word_unique {bs : List U8} {start finish : Nat} {word : List Nat}
    (first : Rowl.Longest.Utf8Span bs start finish word) :
    ∀ other, Rowl.Longest.Utf8Span bs start finish other → word = other := by
  induction first with
  | empty bound =>
    intro other second
    cases second with
    | empty _ => rfl
    | character _ positive fits tail =>
      have endBound : ∀ {position endPoint : Nat} {text : List Nat},
          Rowl.Longest.Utf8Span bs position endPoint text → position ≤ endPoint := by
        intro position endPoint text span
        induction span with
        | empty => omega
        | character _ positive _ _ ih => omega
      have := endBound tail
      omega
  | character unit positive fits tail ih =>
    intro other second
    cases second with
    | empty _ =>
      have endBound : ∀ {position endPoint : Nat} {text : List Nat},
          Rowl.Longest.Utf8Span bs position endPoint text → position ≤ endPoint := by
        intro position endPoint text span
        induction span with
        | empty => omega
        | character _ positive _ _ ih => omega
      have := endBound tail
      omega
    | character otherUnit _ _ otherTail =>
      have same := Prod.mk.inj (Option.some.inj (unit.symm.trans otherUnit))
      rcases same with ⟨rfl,rfl⟩
      exact congrArg _ (ih _ otherTail)

/-- Canonical source bytes and equal original endpoints determine one terminal
    kind. This is the normative no-ties claim for the actual byte candidates. -/
theorem candidate_kind_unique (bytes : List U8) (start endpoint : Nat) (one two : Terminal)
    (first : Rowl.FunctionalSelection.Candidate bytes start one endpoint)
    (second : Rowl.FunctionalSelection.Candidate bytes start two endpoint) : one = two := by
  obtain ⟨firstWord,firstSpan,firstLanguage⟩ := first
  obtain ⟨secondWord,secondSpan,secondLanguage⟩ := second
  have same := span_word_unique firstSpan secondWord secondSpan
  subst secondWord
  exact terminal_language_unique one two firstWord firstLanguage secondLanguage

/-- Independent standard greatest-token contract. There is no priority or
    first-inventory premise: maximal source-language matching alone suffices. -/
def Greatest (bytes : List U8) (start : Nat) (token : Token) : Prop :=
  (∃ word, Rowl.Regular.Utf8From bytes start word) ∧ token.start.val = start ∧
    Rowl.FunctionalSelection.Candidate bytes start token.terminal token.end.val ∧
    ∀ terminal endpoint, Rowl.FunctionalSelection.Candidate bytes start terminal endpoint → endpoint ≤ token.end.val

/-- The prior inventory-priority condition is redundant under the fully proved
    standard terminal-language disjointness. -/
theorem greatest_correct_iff (bytes : List U8) (start : Nat) (token : Token) :
    Greatest bytes start token ↔ Rowl.FunctionalSelection.Correct bytes start (.Token token) := by
  classical
  constructor
  · intro greatest
    refine ⟨greatest.1,greatest.2.1,greatest.2.2.1,greatest.2.2.2,?_⟩
    unfold Rowl.FunctionalSelection.FirstCandidate
    have present : token.terminal ∈ Rowl.FunctionalSelection.AllTerminals.filter
        (fun terminal => decide (Rowl.FunctionalSelection.Candidate bytes start terminal token.end.val)) := by
      simp [Rowl.FunctionalSelection.inventory_complete,greatest.2.2.1]
    cases filtered : Rowl.FunctionalSelection.AllTerminals.filter
        (fun terminal => decide (Rowl.FunctionalSelection.Candidate bytes start terminal token.end.val)) with
    | nil => simp [filtered] at present
    | cons head tail =>
      have headCandidate : Rowl.FunctionalSelection.Candidate bytes start head token.end.val := by
        have included : head ∈ Rowl.FunctionalSelection.AllTerminals.filter
            (fun terminal => decide (Rowl.FunctionalSelection.Candidate bytes start terminal token.end.val)) := by simp [filtered]
        exact of_decide_eq_true (List.mem_filter.mp included).2
      have same := candidate_kind_unique bytes start token.end.val head token.terminal headCandidate greatest.2.2.1
      simp [same]
  · intro correct
    exact ⟨correct.1,correct.2.1,correct.2.2.1,correct.2.2.2.1⟩

/-- Full token identity is uniquely determined by standard greatest matching
    without any caller-supplied tie rule or terminal metadata. -/
theorem greatest_token_unique (bytes : List U8) (start : Nat) (one two : Token)
    (first : Greatest bytes start one) (second : Greatest bytes start two) : one = two :=
  Rowl.FunctionalSelection.selected_token_unique bytes start one two
    ((greatest_correct_iff bytes start one).mp first) ((greatest_correct_iff bytes start two).mp second)

/-- The actual selector accepts exactly the standard greatest-token predicate;
    its implementation priority cannot affect any grammar-valid result. -/
theorem next_terminal_greatest_iff (bytes : alloc.vec.Vec U8) (start : Usize) (token : Token) :
    next_terminal bytes start = .ok (.Token token) ↔ Greatest bytes.val start.val token := by
  rw [Rowl.FunctionalSelection.next_terminal_token_iff,← greatest_correct_iff]

end Rowl.FunctionalDisjointness
