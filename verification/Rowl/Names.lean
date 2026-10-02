import Rowl.Iri

namespace Rowl.Names
open Aeneas Aeneas.Std RowlRust Rowl.Regular
open scoped Computability
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-- SPARQL 2008 production 95, as a predicate on Unicode code points. -/
def BaseCode (cp : Nat) : Prop :=
  (0x41 ≤ cp ∧ cp ≤ 0x5a) ∨ (0x61 ≤ cp ∧ cp ≤ 0x7a) ∨
  (0xc0 ≤ cp ∧ cp ≤ 0xd6) ∨ (0xd8 ≤ cp ∧ cp ≤ 0xf6) ∨
  (0xf8 ≤ cp ∧ cp ≤ 0x2ff) ∨ (0x370 ≤ cp ∧ cp ≤ 0x37d) ∨
  (0x37f ≤ cp ∧ cp ≤ 0x1fff) ∨ (0x200c ≤ cp ∧ cp ≤ 0x200d) ∨
  (0x2070 ≤ cp ∧ cp ≤ 0x218f) ∨ (0x2c00 ≤ cp ∧ cp ≤ 0x2fef) ∨
  (0x3001 ≤ cp ∧ cp ≤ 0xd7ff) ∨ (0xf900 ≤ cp ∧ cp ≤ 0xfdcf) ∨
  (0xfdf0 ≤ cp ∧ cp ≤ 0xfffd) ∨ (0x10000 ≤ cp ∧ cp ≤ 0xeffff)
/-- A one-character base name. -/
def Base : Language Nat := {word | ∃ cp, word = [cp] ∧ BaseCode cp}
/-- Name characters also permitting underscore. -/
def CharsU : Language Nat := Base + Rowl.Iri.Range 95 95
/-- SPARQL 2008 production 98; combining marks cannot begin a local name. -/
def Chars : Language Nat := CharsU + (Rowl.Iri.Range 45 45 + (Rowl.Iri.Range 48 57 +
  (Rowl.Iri.Range 0xb7 0xb7 + (Rowl.Iri.Range 0x300 0x36f + Rowl.Iri.Range 0x203f 0x2040))))
/-- An optional suffix with internal dots but a non-dot final character. -/
def Ending : Language Nat := 1 + (Chars + Rowl.Iri.Range 46 46)∗ * Chars
/-- Nonempty prefix label before its colon. -/
def PrefixWord : Language Nat := Base * Ending
/-- Nonempty local name, permitting an initial digit or underscore. -/
def Local : Language Nat := (CharsU + Rowl.Iri.Range 48 57) * Ending
/-- PNAME_NS; the empty prefix label is allowed. -/
def Prefix : Language Nat := (1 + PrefixWord) * Rowl.Iri.Range 58 58
/-- OWL abbreviatedIRI is PNAME_LN, with a nonempty local part. -/
def Abbreviated : Language Nat := Prefix * Local
/-- OWL nodeID follows the referenced SPARQL 2008 BLANK_NODE_LABEL. -/
def Node : Language Nat := (Rowl.Iri.Range 95 95 * Rowl.Iri.Range 58 58) * Local

@[local step] private theorem range_spec (lower upper : U32) :
    names.range lower upper ⦃ e => Denotes e = Rowl.Iri.Range lower.val upper.val ⦄ := by
  simp [names.range, Denotes, Rowl.Iri.Range]
@[local step] private theorem ch_spec (cp : U32) :
    names.ch cp ⦃ e => Denotes e = Rowl.Iri.Range cp.val cp.val ⦄ := by
  simp [names.ch, names.range, Denotes, Rowl.Iri.Range]
@[local step] private theorem alt_spec (a b : regular.Expression) :
    names.alt a b ⦃ e => Denotes e = Denotes a + Denotes b ⦄ := by
  simp [names.alt, Denotes]
@[local step] private theorem cat_spec (a b : regular.Expression) :
    names.cat a b ⦃ e => Denotes e = Denotes a * Denotes b ⦄ := by
  simp [names.cat, Denotes]
@[local step] private theorem opt_spec (a : regular.Expression) :
    names.opt a ⦃ e => Denotes e = 1 + Denotes a ⦄ := by
  simp [names.opt, names.alt, Denotes]
@[local step] private theorem star_spec (a : regular.Expression) :
    names.star a ⦃ e => Denotes e = (Denotes a)∗ ⦄ := by
  simp [names.star, Denotes]

@[local step] private theorem base_spec : names.base ⦃ e => Denotes e = Base ⦄ := by
  unfold names.base
  step*
  ext word
  simp_all [Base, BaseCode, Rowl.Iri.Range, and_or_left, exists_or]
@[local step] private theorem u_spec : names.chars_u ⦃ e => Denotes e = CharsU ⦄ := by
  unfold names.chars_u; step*; simp_all [CharsU]
@[local step] private theorem chars_spec : names.chars ⦃ e => Denotes e = Chars ⦄ := by
  unfold names.chars; step*; simp_all [Chars]
@[local step] private theorem ending_spec : names.ending ⦃ e => Denotes e = Ending ⦄ := by
  unfold names.ending; step*; simp_all [Ending]
@[local step] private theorem prefix_word_spec : names.prefix_word ⦃ e => Denotes e = PrefixWord ⦄ := by
  unfold names.prefix_word; step*; simp_all [PrefixWord]
@[local step] private theorem local_spec : names.local_word ⦃ e => Denotes e = Local ⦄ := by
  unfold names.local_word; step*; simp_all [Local]
@[local step] private theorem prefix_spec : names.prefix_grammar ⦃ e => Denotes e = Prefix ⦄ := by
  unfold names.prefix_grammar; step*; simp_all [Prefix]
@[local step] private theorem abbreviated_spec : names.abbreviated_grammar ⦃ e => Denotes e = Abbreviated ⦄ := by
  unfold names.abbreviated_grammar; step*; simp_all [Abbreviated]
@[local step] private theorem node_spec : names.node_grammar ⦃ e => Denotes e = Node ⦄ := by
  unfold names.node_grammar; step*; simp_all [Node]

/-- Actual compiled prefix-name grammar equals the independent language. -/
theorem prefix_grammar_total_correct : ∃ e, names.prefix_grammar = .ok e ∧ Denotes e = Prefix :=
  WP.spec_imp_exists prefix_spec
/-- Actual compiled local-name grammar equals the independent language. -/
theorem local_grammar_total_correct : ∃ e, names.local_word = .ok e ∧ Denotes e = Local :=
  WP.spec_imp_exists local_spec
/-- Actual compiled abbreviated-IRI grammar equals the independent language. -/
theorem abbreviated_grammar_total_correct : ∃ e, names.abbreviated_grammar = .ok e ∧ Denotes e = Abbreviated :=
  WP.spec_imp_exists abbreviated_spec
/-- Actual compiled OWL node-ID grammar equals the independent language. -/
theorem node_grammar_total_correct : ∃ e, names.node_grammar = .ok e ∧ Denotes e = Node :=
  WP.spec_imp_exists node_spec

private theorem converted (grammar : Language Nat) (e : regular.Expression) (bytes : List U8)
    (result : regular.MatchResult) (equal : Denotes e = grammar) :
    MatchCorrect e bytes 0 result ↔ Rowl.Iri.ValidationCorrect grammar bytes result := by
  cases result <;> simp [MatchCorrect, Rowl.Iri.ValidationCorrect, equal]

/-- Whole-byte exact prefix acceptance or the original malformed UTF-8 error. -/
theorem validate_prefix_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ result, names.validate_prefix bytes = .ok result ∧ Rowl.Iri.ValidationCorrect Prefix bytes.val result := by
  obtain ⟨e, compiled, semantic⟩ := prefix_grammar_total_correct
  obtain ⟨result, executed, correct⟩ := matches_utf8_total_correct e bytes
  exact ⟨result, by simp [names.validate_prefix, compiled, executed], (converted _ _ _ _ semantic).mp correct⟩
/-- Whole-byte exact local-name acceptance or the original malformed UTF-8 error. -/
theorem validate_local_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ result, names.validate_local bytes = .ok result ∧ Rowl.Iri.ValidationCorrect Local bytes.val result := by
  obtain ⟨e, compiled, semantic⟩ := local_grammar_total_correct
  obtain ⟨result, executed, correct⟩ := matches_utf8_total_correct e bytes
  exact ⟨result, by simp [names.validate_local, compiled, executed], (converted _ _ _ _ semantic).mp correct⟩
/-- Whole-byte exact abbreviated-IRI acceptance and complete suffix validation. -/
theorem validate_abbreviated_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ result, names.validate_abbreviated bytes = .ok result ∧ Rowl.Iri.ValidationCorrect Abbreviated bytes.val result := by
  obtain ⟨e, compiled, semantic⟩ := abbreviated_grammar_total_correct
  obtain ⟨result, executed, correct⟩ := matches_utf8_total_correct e bytes
  exact ⟨result, by simp [names.validate_abbreviated, compiled, executed], (converted _ _ _ _ semantic).mp correct⟩
/-- Whole-byte exact node-ID acceptance; scope assignment remains separate. -/
theorem validate_node_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ result, names.validate_node bytes = .ok result ∧ Rowl.Iri.ValidationCorrect Node bytes.val result := by
  obtain ⟨e, compiled, semantic⟩ := node_grammar_total_correct
  obtain ⟨result, executed, correct⟩ := matches_utf8_total_correct e bytes
  exact ⟨result, by simp [names.validate_node, compiled, executed], (converted _ _ _ _ semantic).mp correct⟩

theorem validate_prefix_accepted_iff (bytes : alloc.vec.Vec U8) :
    names.validate_prefix bytes = .ok (.Matched true) ↔ ∃ word, Utf8From bytes.val 0 word ∧ word ∈ Prefix := by
  obtain ⟨e, compiled, semantic⟩ := prefix_grammar_total_correct
  simpa [names.validate_prefix, compiled, semantic] using matches_utf8_accepted_iff e bytes
theorem validate_local_accepted_iff (bytes : alloc.vec.Vec U8) :
    names.validate_local bytes = .ok (.Matched true) ↔ ∃ word, Utf8From bytes.val 0 word ∧ word ∈ Local := by
  obtain ⟨e, compiled, semantic⟩ := local_grammar_total_correct
  simpa [names.validate_local, compiled, semantic] using matches_utf8_accepted_iff e bytes
theorem validate_abbreviated_accepted_iff (bytes : alloc.vec.Vec U8) :
    names.validate_abbreviated bytes = .ok (.Matched true) ↔ ∃ word, Utf8From bytes.val 0 word ∧ word ∈ Abbreviated := by
  obtain ⟨e, compiled, semantic⟩ := abbreviated_grammar_total_correct
  simpa [names.validate_abbreviated, compiled, semantic] using matches_utf8_accepted_iff e bytes
theorem validate_node_accepted_iff (bytes : alloc.vec.Vec U8) :
    names.validate_node bytes = .ok (.Matched true) ↔ ∃ word, Utf8From bytes.val 0 word ∧ word ∈ Node := by
  obtain ⟨e, compiled, semantic⟩ := node_grammar_total_correct
  simpa [names.validate_node, compiled, semantic] using matches_utf8_accepted_iff e bytes

end Rowl.Names
