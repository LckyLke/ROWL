import Rowl.Names
import Rowl.LangTag
import Rowl.Longest

namespace Rowl.Functional
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.functional Rowl.Regular
open scoped Computability
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- Independent singleton finite-word language. -/
def Word (characters : List Nat) : Language Nat := {word | word = characters}
@[local simp] private theorem mem_word (characters word : List Nat) : word ∈ Word characters ↔ word = characters := Iff.rfl
/-- All case-sensitive keywords in the normative 2012 complete grammar. -/
def KeywordWord : Keyword → List Nat
  | .Prefix => "Prefix".toList.map Char.toNat
  | .Ontology => "Ontology".toList.map Char.toNat
  | .Import => "Import".toList.map Char.toNat
  | .Declaration => "Declaration".toList.map Char.toNat
  | .Class => "Class".toList.map Char.toNat
  | .Datatype => "Datatype".toList.map Char.toNat
  | .ObjectProperty => "ObjectProperty".toList.map Char.toNat
  | .DataProperty => "DataProperty".toList.map Char.toNat
  | .AnnotationProperty => "AnnotationProperty".toList.map Char.toNat
  | .NamedIndividual => "NamedIndividual".toList.map Char.toNat
  | .Annotation => "Annotation".toList.map Char.toNat
  | .AnnotationAssertion => "AnnotationAssertion".toList.map Char.toNat
  | .SubAnnotationPropertyOf => "SubAnnotationPropertyOf".toList.map Char.toNat
  | .AnnotationPropertyDomain => "AnnotationPropertyDomain".toList.map Char.toNat
  | .AnnotationPropertyRange => "AnnotationPropertyRange".toList.map Char.toNat
  | .ObjectInverseOf => "ObjectInverseOf".toList.map Char.toNat
  | .DataIntersectionOf => "DataIntersectionOf".toList.map Char.toNat
  | .DataUnionOf => "DataUnionOf".toList.map Char.toNat
  | .DataComplementOf => "DataComplementOf".toList.map Char.toNat
  | .DataOneOf => "DataOneOf".toList.map Char.toNat
  | .DatatypeRestriction => "DatatypeRestriction".toList.map Char.toNat
  | .ObjectIntersectionOf => "ObjectIntersectionOf".toList.map Char.toNat
  | .ObjectUnionOf => "ObjectUnionOf".toList.map Char.toNat
  | .ObjectComplementOf => "ObjectComplementOf".toList.map Char.toNat
  | .ObjectOneOf => "ObjectOneOf".toList.map Char.toNat
  | .ObjectSomeValuesFrom => "ObjectSomeValuesFrom".toList.map Char.toNat
  | .ObjectAllValuesFrom => "ObjectAllValuesFrom".toList.map Char.toNat
  | .ObjectHasValue => "ObjectHasValue".toList.map Char.toNat
  | .ObjectHasSelf => "ObjectHasSelf".toList.map Char.toNat
  | .ObjectMinCardinality => "ObjectMinCardinality".toList.map Char.toNat
  | .ObjectMaxCardinality => "ObjectMaxCardinality".toList.map Char.toNat
  | .ObjectExactCardinality => "ObjectExactCardinality".toList.map Char.toNat
  | .DataSomeValuesFrom => "DataSomeValuesFrom".toList.map Char.toNat
  | .DataAllValuesFrom => "DataAllValuesFrom".toList.map Char.toNat
  | .DataHasValue => "DataHasValue".toList.map Char.toNat
  | .DataMinCardinality => "DataMinCardinality".toList.map Char.toNat
  | .DataMaxCardinality => "DataMaxCardinality".toList.map Char.toNat
  | .DataExactCardinality => "DataExactCardinality".toList.map Char.toNat
  | .SubClassOf => "SubClassOf".toList.map Char.toNat
  | .EquivalentClasses => "EquivalentClasses".toList.map Char.toNat
  | .DisjointClasses => "DisjointClasses".toList.map Char.toNat
  | .DisjointUnion => "DisjointUnion".toList.map Char.toNat
  | .SubObjectPropertyOf => "SubObjectPropertyOf".toList.map Char.toNat
  | .ObjectPropertyChain => "ObjectPropertyChain".toList.map Char.toNat
  | .EquivalentObjectProperties => "EquivalentObjectProperties".toList.map Char.toNat
  | .DisjointObjectProperties => "DisjointObjectProperties".toList.map Char.toNat
  | .ObjectPropertyDomain => "ObjectPropertyDomain".toList.map Char.toNat
  | .ObjectPropertyRange => "ObjectPropertyRange".toList.map Char.toNat
  | .InverseObjectProperties => "InverseObjectProperties".toList.map Char.toNat
  | .FunctionalObjectProperty => "FunctionalObjectProperty".toList.map Char.toNat
  | .InverseFunctionalObjectProperty => "InverseFunctionalObjectProperty".toList.map Char.toNat
  | .ReflexiveObjectProperty => "ReflexiveObjectProperty".toList.map Char.toNat
  | .IrreflexiveObjectProperty => "IrreflexiveObjectProperty".toList.map Char.toNat
  | .SymmetricObjectProperty => "SymmetricObjectProperty".toList.map Char.toNat
  | .AsymmetricObjectProperty => "AsymmetricObjectProperty".toList.map Char.toNat
  | .TransitiveObjectProperty => "TransitiveObjectProperty".toList.map Char.toNat
  | .SubDataPropertyOf => "SubDataPropertyOf".toList.map Char.toNat
  | .EquivalentDataProperties => "EquivalentDataProperties".toList.map Char.toNat
  | .DisjointDataProperties => "DisjointDataProperties".toList.map Char.toNat
  | .DataPropertyDomain => "DataPropertyDomain".toList.map Char.toNat
  | .DataPropertyRange => "DataPropertyRange".toList.map Char.toNat
  | .FunctionalDataProperty => "FunctionalDataProperty".toList.map Char.toNat
  | .DatatypeDefinition => "DatatypeDefinition".toList.map Char.toNat
  | .HasKey => "HasKey".toList.map Char.toNat
  | .SameIndividual => "SameIndividual".toList.map Char.toNat
  | .DifferentIndividuals => "DifferentIndividuals".toList.map Char.toNat
  | .ClassAssertion => "ClassAssertion".toList.map Char.toNat
  | .ObjectPropertyAssertion => "ObjectPropertyAssertion".toList.map Char.toNat
  | .NegativeObjectPropertyAssertion => "NegativeObjectPropertyAssertion".toList.map Char.toNat
  | .DataPropertyAssertion => "DataPropertyAssertion".toList.map Char.toNat
  | .NegativeDataPropertyAssertion => "NegativeDataPropertyAssertion".toList.map Char.toNat

/-- The complete 71-keyword inventory has distinct exact codepoint spellings. -/
theorem keyword_words_injective (one two : Keyword) (same : KeywordWord one = KeywordWord two) : one = two := by
  cases one <;> cases two <;> simp_all [KeywordWord]

/-- Nonempty decimal digits; numeric value construction is separate. -/
def IntegerLanguage : Language Nat := Rowl.Iri.Range 48 57 * (Rowl.Iri.Range 48 57)∗
/-- Unescaped XML characters, with quote and backslash excluded. -/
def QuotedRaw : Language Nat := {word | ∃ cp, word = [cp] ∧ Rowl.Unicode.XmlChar cp ∧ cp ≠ 34 ∧ cp ≠ 92}
/-- The only two Functional Syntax string escapes. -/
def QuotedBody : Language Nat := QuotedRaw + Rowl.Iri.Range 92 92 * (Rowl.Iri.Range 34 34 + Rowl.Iri.Range 92 92)
def QuotedLanguage : Language Nat := Rowl.Iri.Range 34 34 * (QuotedBody∗ * Rowl.Iri.Range 34 34)
/-- Exactly the four whitespace characters, without Unicode space normalization. -/
def Space : Language Nat := {word | word = [32] ∨ word = [9] ∨ word = [10] ∨ word = [13]}
def WhitespaceLanguage : Language Nat := Space * Space∗
/-- Comments contain XML characters other than CR and LF. -/
def CommentRaw : Language Nat := {word | ∃ cp, word = [cp] ∧ Rowl.Unicode.XmlChar cp ∧ cp ≠ 10 ∧ cp ≠ 13}
def CommentLanguage : Language Nat := Rowl.Iri.Range 35 35 * CommentRaw∗
/-- The complete terminal-language family, including discarded special tokens. -/
def TerminalLanguage : Terminal → Language Nat
  | .Keyword key => Word (KeywordWord key)
  | .Open => Rowl.Iri.Range 40 40
  | .Close => Rowl.Iri.Range 41 41
  | .Equals => Rowl.Iri.Range 61 61
  | .DatatypeIndicator => Rowl.Iri.Range 94 94 * Rowl.Iri.Range 94 94
  | .Integer => IntegerLanguage
  | .QuotedString => QuotedLanguage
  | .LanguageTag => Rowl.Iri.Range 64 64 * Rowl.LangTag.NormalLanguage
  | .NodeId => Rowl.Names.Node
  | .FullIri => Rowl.Iri.Range 60 60 * (Rowl.Iri.IriLanguage * Rowl.Iri.Range 62 62)
  | .PrefixName => Rowl.Names.Prefix
  | .AbbreviatedIri => Rowl.Names.Abbreviated
  | .Whitespace => WhitespaceLanguage
  | .Comment => CommentLanguage

@[local step] private theorem range_spec (lower upper : U32) :
    functional.range lower upper ⦃ e => Denotes e = Rowl.Iri.Range lower.val upper.val ⦄ := by
  simp [functional.range, Denotes, Rowl.Iri.Range]
@[local step] private theorem ch_spec (cp : U32) :
    functional.ch cp ⦃ e => Denotes e = Rowl.Iri.Range cp.val cp.val ⦄ := by
  simp [functional.ch, functional.range, Denotes, Rowl.Iri.Range]
@[local step] private theorem alt_spec (a b : regular.Expression) :
    functional.alt a b ⦃ e => Denotes e = Denotes a + Denotes b ⦄ := by simp [functional.alt, Denotes]
@[local step] private theorem cat_spec (a b : regular.Expression) :
    functional.cat a b ⦃ e => Denotes e = Denotes a * Denotes b ⦄ := by simp [functional.cat, Denotes]
@[local step] private theorem star_spec (a : regular.Expression) :
    functional.star a ⦃ e => Denotes e = (Denotes a)∗ ⦄ := by simp [functional.star, Denotes]

private theorem word_cons (cp : Nat) (tail : List Nat) :
    Rowl.Iri.Range cp cp * Word tail = Word (cp :: tail) := by
  ext word
  simp only [Language.mem_mul, Rowl.Iri.Range, Word, Set.mem_setOf_eq]
  constructor
  · rintro ⟨left, ⟨value, equal, lower, upper⟩, right, same, contents⟩
    have valueEq : value = cp := by omega
    subst value; subst left; subst right; exact contents.symm
  · intro equal
    exact ⟨[cp], ⟨cp, rfl, le_rfl, le_rfl⟩, tail, rfl, equal.symm⟩

private theorem literal_from_spec (bytes : Slice U8) (position : Usize) :
    functional.literal_from bytes position ⦃ e => Denotes e = Word ((bytes.val.drop position.val).map UScalar.val) ⦄ := by
  rw [functional.literal_from]
  split
  · rename_i inside
    have beforeEnd : position.val < bytes.val.length := by scalar_tac
    step as ⟨byte, hb⟩
    simp only [lift, bind_ok]
    step as ⟨head, headCorrect⟩
    step as ⟨next, nextCorrect⟩
    obtain ⟨tail, recursed, tailCorrect⟩ := WP.spec_imp_exists (literal_from_spec bytes next)
    simp only [recursed, bind_ok, functional.cat, WP.spec_ok, Denotes, tailCorrect]
    have nextVal : next.val = position.val + 1 := by scalar_tac
    rw [List.drop_eq_getElem_cons beforeEnd]
    simp only [List.map_cons]
    simp_all [nextVal, word_cons]
  · rename_i outside
    have atEnd : bytes.val.length ≤ position.val := by scalar_tac
    simp [List.drop_eq_nil_of_le atEnd, Denotes, Word]
    rfl
termination_by bytes.val.length - position.val
decreasing_by scalar_tac

@[local step] private theorem literal_spec (bytes : Slice U8) :
    functional.literal bytes ⦃ e => Denotes e = Word (bytes.val.map UScalar.val) ⦄ := by
  simpa [functional.literal] using literal_from_spec bytes 0#usize

/-- Derived keyword copying retains the exact constructor. -/
theorem keyword_clone_total_correct (key : Keyword) : functional.Keyword.Insts.CoreCloneClone.clone key = .ok key := rfl
/-- Derived terminal copying retains all kind/keyword metadata. -/
theorem terminal_clone_total_correct (terminal : Terminal) : functional.Terminal.Insts.CoreCloneClone.clone terminal = .ok terminal := rfl

/-- Exact actual-source compilation for all 71 normative keywords. -/
theorem keyword_grammar_total_correct (key : Keyword) :
    ∃ e, functional.keyword_grammar key = .ok e ∧ Denotes e = Word (KeywordWord key) := by
  cases key <;> apply WP.spec_imp_exists <;> unfold functional.keyword_grammar
  all_goals simp only [lift]; step*; simp_all [KeywordWord]
@[local step] private theorem keyword_spec (key : Keyword) :
    functional.keyword_grammar key ⦃ e => Denotes e = Word (KeywordWord key) ⦄ := by
  obtain ⟨e, compiled, language⟩ := keyword_grammar_total_correct key
  simp [compiled, language]

@[local step] private theorem digits_spec : functional.digits ⦃ e => Denotes e = IntegerLanguage ⦄ := by
  unfold functional.digits; step*; simp_all [IntegerLanguage]
@[local step] private theorem quoted_raw_spec : functional.quoted_raw ⦃ e => Denotes e = QuotedRaw ⦄ := by
  unfold functional.quoted_raw; step*
  ext word
  simp_all [QuotedRaw, Rowl.Unicode.XmlChar, Rowl.Iri.Range, and_or_left, exists_or]
  constructor
  all_goals aesop (add safe tactic (by omega))
@[local step] private theorem quoted_spec : functional.quoted ⦃ e => Denotes e = QuotedLanguage ⦄ := by
  unfold functional.quoted; step*; simp_all [QuotedLanguage, QuotedBody]
@[local step] private theorem space_spec : functional.space ⦃ e => Denotes e = Space ⦄ := by
  unfold functional.space; step*
  ext word
  simp_all [Space, Rowl.Iri.Range, and_or_left, exists_or]
  aesop (add safe tactic (by omega))
@[local step] private theorem whitespace_spec : functional.whitespace ⦃ e => Denotes e = WhitespaceLanguage ⦄ := by
  unfold functional.whitespace; step*; simp_all [WhitespaceLanguage]
@[local step] private theorem comment_raw_spec : functional.comment_raw ⦃ e => Denotes e = CommentRaw ⦄ := by
  unfold functional.comment_raw; step*
  ext word
  simp_all [CommentRaw, Rowl.Unicode.XmlChar, Rowl.Iri.Range, and_or_left, exists_or]
  constructor
  all_goals aesop (add safe tactic (by omega))
@[local step] private theorem comment_spec : functional.comment ⦃ e => Denotes e = CommentLanguage ⦄ := by
  unfold functional.comment; step*; simp_all [CommentLanguage]
@[local step] private theorem normal_tag_spec : langtag.normal_grammar ⦃ e => Denotes e = Rowl.LangTag.NormalLanguage ⦄ := by
  obtain ⟨e, compiled, language⟩ := Rowl.LangTag.normal_grammar_total_correct
  simp [compiled, language]
@[local step] private theorem iri_spec : iri.iri ⦃ e => Denotes e = Rowl.Iri.IriLanguage ⦄ := by
  obtain ⟨e, compiled, language⟩ := Rowl.Iri.iri_grammar_total_correct
  simp [compiled, language]
@[local step] private theorem node_spec : names.node_grammar ⦃ e => Denotes e = Rowl.Names.Node ⦄ := by
  obtain ⟨e, compiled, language⟩ := Rowl.Names.node_grammar_total_correct
  simp [compiled, language]
@[local step] private theorem prefix_spec : names.prefix_grammar ⦃ e => Denotes e = Rowl.Names.Prefix ⦄ := by
  obtain ⟨e, compiled, language⟩ := Rowl.Names.prefix_grammar_total_correct
  simp [compiled, language]
@[local step] private theorem abbreviated_spec : names.abbreviated_grammar ⦃ e => Denotes e = Rowl.Names.Abbreviated ⦄ := by
  obtain ⟨e, compiled, language⟩ := Rowl.Names.abbreviated_grammar_total_correct
  simp [compiled, language]

/-- Complete terminal-family compilation, including every variable production
    and both discarded token classes. -/
theorem grammar_total_correct (terminal : Terminal) :
    ∃ e, functional.grammar terminal = .ok e ∧ Denotes e = TerminalLanguage terminal := by
  cases terminal <;> apply WP.spec_imp_exists <;> unfold functional.grammar
  all_goals step*; simp_all [TerminalLanguage]

@[local simp] private theorem nil_range (lower upper : Nat) :
    ¬ [] ∈ Rowl.Iri.Range lower upper := by simp [Rowl.Iri.Range]
@[local simp] private theorem nil_mul (a b : Language Nat) :
    [] ∈ a * b ↔ [] ∈ a ∧ [] ∈ b := by
  rw [Language.mem_mul]
  constructor
  · rintro ⟨left, acceptedLeft, right, acceptedRight, equal⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp equal
    exact ⟨acceptedLeft, acceptedRight⟩
  · rintro ⟨acceptedLeft, acceptedRight⟩
    exact ⟨[], acceptedLeft, [], acceptedRight, rfl⟩

/-- No standard terminal can produce an empty match, so a recognized token
    strictly advances instead of stalling the document lexer. -/
theorem grammar_nonempty (terminal : Terminal) : ¬ [] ∈ TerminalLanguage terminal := by
  cases terminal with
  | Keyword key => cases key <;> simp [TerminalLanguage, mem_word, KeywordWord]
  | PrefixName => simp [TerminalLanguage, Rowl.Names.Prefix]
  | AbbreviatedIri => simp [TerminalLanguage, Rowl.Names.Abbreviated, Rowl.Names.Prefix]
  | NodeId => simp [TerminalLanguage, Rowl.Names.Node]
  | Whitespace => simp [TerminalLanguage, WhitespaceLanguage, Space]
  | Integer => simp [TerminalLanguage, IntegerLanguage]
  | QuotedString => simp [TerminalLanguage, QuotedLanguage]
  | Comment => simp [TerminalLanguage, CommentLanguage]
  | _ => simp [TerminalLanguage]

/-- Exact whole-byte terminal recognition and malformed-unit evidence. -/
theorem recognize_total_correct (terminal : Terminal) (bytes : alloc.vec.Vec U8) :
    ∃ result, functional.recognize terminal bytes = .ok result ∧
      Rowl.Iri.ValidationCorrect (TerminalLanguage terminal) bytes.val result := by
  obtain ⟨e, compiled, language⟩ := grammar_total_correct terminal
  obtain ⟨result, executed, correct⟩ := matches_utf8_total_correct e bytes
  refine ⟨result, by simp [functional.recognize, compiled, executed], ?_⟩
  cases result <;> simpa [MatchCorrect, Rowl.Iri.ValidationCorrect, language] using correct
/-- Sound and complete whole-token acceptance for every standard terminal. -/
theorem recognize_accepted_iff (terminal : Terminal) (bytes : alloc.vec.Vec U8) :
    functional.recognize terminal bytes = .ok (.Matched true) ↔
      ∃ word, Utf8From bytes.val 0 word ∧ word ∈ TerminalLanguage terminal := by
  obtain ⟨e, compiled, language⟩ := grammar_total_correct terminal
  simpa [functional.recognize, compiled, language] using matches_utf8_accepted_iff e bytes
/-- Exact greedy endpoint selection, or precise malformed suffix evidence. -/
theorem longest_total_correct (terminal : Terminal) (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ result, functional.longest terminal bytes position = .ok result ∧
      Rowl.Longest.Correct (TerminalLanguage terminal) bytes.val position.val result := by
  obtain ⟨e, compiled, language⟩ := grammar_total_correct terminal
  obtain ⟨result, executed, correct⟩ := Rowl.Longest.longest_prefix_total_correct e bytes position
  exact ⟨result, by simp [functional.longest, compiled, executed], by simpa [language] using correct⟩
/-- All and only the mathematically greatest terminal endpoints are returned. -/
theorem longest_matched_iff (terminal : Terminal) (bytes : alloc.vec.Vec U8)
    (position : Usize) (endpoint : Option Usize) :
    functional.longest terminal bytes position = .ok (.Matched endpoint) ↔
      (∃ word, Utf8From bytes.val position.val word) ∧
        Rowl.Longest.Maximal (Rowl.Longest.Candidate bytes.val position.val (TerminalLanguage terminal)) endpoint := by
  obtain ⟨e, compiled, language⟩ := grammar_total_correct terminal
  simpa [functional.longest, compiled, language] using Rowl.Longest.longest_prefix_matched_iff e bytes position endpoint

private theorem span_bound {bs : List U8} {start finish : Nat} {word : List Nat}
    (span : Rowl.Longest.Utf8Span bs start finish word) : start ≤ finish ∧ finish ≤ bs.length := by
  induction span with
  | empty bound => exact ⟨le_rfl, bound⟩
  | character _ positive _ _ ih => constructor <;> omega
/-- Any successful standard terminal consumes a nonempty source segment, with
    its exact exclusive endpoint bounded by the source length. -/
theorem longest_advances (terminal : Terminal) (bytes : alloc.vec.Vec U8) (position endpoint : Usize)
    (success : functional.longest terminal bytes position = .ok (.Matched (some endpoint))) :
    position.val < endpoint.val ∧ endpoint.val ≤ bytes.val.length := by
  have correct := (longest_matched_iff terminal bytes position (some endpoint)).mp success
  obtain ⟨word, span, accepted⟩ := correct.2.1
  have nonempty : word ≠ [] := by
    intro equal
    exact grammar_nonempty terminal (by simpa [equal] using accepted)
  have strict : ∀ {start finish : Nat} {word : List Nat}, Rowl.Longest.Utf8Span bytes.val start finish word →
      word ≠ [] → start < finish := by
    intro start finish word span notEmpty
    cases span with
    | empty _ => contradiction
    | character _ positive _ tail =>
      have bound := span_bound tail
      omega
  exact ⟨strict span nonempty, (span_bound span).2⟩

end Rowl.Functional
