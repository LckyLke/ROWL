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

/-! ## Prefix names and abbreviated IRIs scanned over ASCII bytes

`names::ascii_prefix` and `names::ascii_abbreviated` find the greatest endpoint
of a PNAME_NS or PNAME_LN at a position without building the grammars. They
read the run of label bytes (ASCII letters, digits, `_`, `-` and `.`) from the
position and require a colon right after it; for PNAME_LN they read the run
after the colon and back off over its trailing dots. They decline (`none`) when
a byte outside ASCII ends a run, since such a byte may continue a name. Every
answer they give is the greatest candidate endpoint for the languages above.
-/

section Scan
open Aeneas.Std.Result
open Rowl.Longest (Utf8Span Candidate Maximal)
set_option maxHeartbeats 3000000

/-! ### Byte classes and the name languages -/

/-- ASCII letters: the ASCII members of PN_CHARS_BASE. -/
private def LetterCode (n : Nat) : Prop := (65 ≤ n ∧ n ≤ 90) ∨ (97 ≤ n ∧ n ≤ 122)
/-- ASCII letters, `_` and digits: the ASCII code points that begin a local name. -/
private def StartCode (n : Nat) : Prop := LetterCode n ∨ n = 95 ∨ (48 ≤ n ∧ n ≤ 57)
/-- ASCII label bytes: the ASCII members of PN_CHARS and the dot. -/
private def LabelCode (n : Nat) : Prop := StartCode n ∨ n = 45 ∨ n = 46
/-- The code points of a label or local name after its first: PN_CHARS and the dot. -/
private def NameChar (c : Nat) : Prop := [c] ∈ Chars + Rowl.Iri.Range 46 46

private theorem label_ascii {n : Nat} (label : LabelCode n) : n < 128 := by
  unfold LabelCode StartCode LetterCode at label; omega

private theorem colon_not_label : ¬ LabelCode 58 := by
  unfold LabelCode StartCode LetterCode; omega

private theorem single_range {c lower upper : Nat} :
    [c] ∈ Rowl.Iri.Range lower upper ↔ lower ≤ c ∧ c ≤ upper := by
  constructor
  · rintro ⟨cp, equal, low, high⟩
    obtain ⟨rfl, -⟩ := List.cons_eq_cons.mp equal
    exact ⟨low, high⟩
  · rintro ⟨low, high⟩
    exact ⟨c, rfl, low, high⟩

private theorem single_base {c : Nat} : [c] ∈ Base ↔ BaseCode c := by
  constructor
  · rintro ⟨cp, equal, base⟩
    obtain ⟨rfl, -⟩ := List.cons_eq_cons.mp equal
    exact base
  · intro base
    exact ⟨c, rfl, base⟩

private theorem single_chars {c : Nat} :
    [c] ∈ Chars ↔ BaseCode c ∨ c = 95 ∨ c = 45 ∨ (48 ≤ c ∧ c ≤ 57) ∨ c = 0xb7 ∨
      (0x300 ≤ c ∧ c ≤ 0x36f) ∨ (0x203f ≤ c ∧ c ≤ 0x2040) := by
  simp only [Chars, CharsU, Language.mem_add, single_base, single_range]
  constructor
  · rintro ((base | underscore) | (dash | (digit | (middle | (combining | connector)))))
    · exact Or.inl base
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl digit)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl combining)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr connector)))))
  · rintro (base | underscore | dash | digit | middle | combining | connector)
    · exact Or.inl (Or.inl base)
    · exact Or.inl (Or.inr (by omega))
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inl digit))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl combining))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr connector))))

private theorem base_ascii {c : Nat} (small : c < 128) : BaseCode c ↔ LetterCode c := by
  unfold BaseCode LetterCode; omega

private theorem name_char_ascii {c : Nat} (small : c < 128) : NameChar c ↔ LabelCode c := by
  unfold NameChar
  rw [Language.mem_add, single_chars, single_range, base_ascii small]
  unfold LabelCode StartCode LetterCode
  omega

private theorem chars_not_dot {c : Nat} (member : [c] ∈ Chars) : c ≠ 46 := by
  rw [single_chars] at member
  unfold BaseCode at member
  omega

private theorem colon_not_name : ¬ NameChar 58 := by
  rw [name_char_ascii (by omega)]
  exact colon_not_label

/-- Every word of `Chars` is one code point. -/
private theorem chars_single {w : List Nat} (member : w ∈ Chars) : ∃ c, w = [c] := by
  simp only [Chars, CharsU, Language.mem_add] at member
  rcases member with ((⟨c, rfl, -⟩ | ⟨c, rfl, -⟩) |
    (⟨c, rfl, -⟩ | (⟨c, rfl, -⟩ | (⟨c, rfl, -⟩ | (⟨c, rfl, -⟩ | ⟨c, rfl, -⟩))))) <;> exact ⟨c, rfl⟩

private theorem names_single {w : List Nat} (member : w ∈ Chars + Rowl.Iri.Range 46 46) :
    ∃ c, w = [c] ∧ NameChar c := by
  rcases (Language.mem_add _ _ _).mp member with chars | ⟨c, rfl, -⟩
  · obtain ⟨c, rfl⟩ := chars_single chars
    exact ⟨c, rfl, member⟩
  · exact ⟨c, rfl, member⟩

private theorem flatten_singletons (w : List Nat) : (w.map fun c => [c]).flatten = w := by
  induction w with
  | nil => rfl
  | cons c rest ih => simp [ih]

private theorem star_names {w : List Nat} :
    w ∈ (Chars + Rowl.Iri.Range 46 46)∗ ↔ ∀ c ∈ w, NameChar c := by
  constructor
  · rintro ⟨parts, rfl, legal⟩ c member
    obtain ⟨part, inParts, inPart⟩ := List.mem_flatten.mp member
    obtain ⟨d, rfl, named⟩ := names_single (legal part inParts)
    obtain rfl : c = d := by simpa using inPart
    exact named
  · intro all
    rw [← flatten_singletons w]
    refine Language.join_mem_kstar ?_
    intro part member
    obtain ⟨c, inW, rfl⟩ := List.mem_map.mp member
    exact all c inW

private theorem ending_names {w : List Nat} (member : w ∈ Ending) : ∀ c ∈ w, NameChar c := by
  rcases (Language.mem_add _ _ _).mp member with empty | nonempty
  · rw [(Language.mem_one _).mp empty]
    simp
  · obtain ⟨init, inInit, last, inLast, rfl⟩ := Language.mem_mul.mp nonempty
    intro c member
    rcases List.mem_append.mp member with inI | inL
    · exact star_names.mp inInit c inI
    · obtain ⟨d, rfl⟩ := chars_single inLast
      obtain rfl : c = d := by simpa using inL
      exact (Language.mem_add _ _ _).mpr (Or.inl inLast)

private theorem ending_last {w : List Nat} (member : w ∈ Ending) :
    ∀ c, w.getLast? = some c → c ≠ 46 := by
  rcases (Language.mem_add _ _ _).mp member with empty | nonempty
  · rw [(Language.mem_one _).mp empty]
    simp
  · obtain ⟨init, inInit, last, inLast, rfl⟩ := Language.mem_mul.mp nonempty
    obtain ⟨d, rfl⟩ := chars_single inLast
    intro c found
    obtain rfl : d = c := by simpa using found
    exact chars_not_dot inLast

private theorem ending_of {w : List Nat} (names : ∀ c ∈ w, NameChar c)
    (last : ∀ c, w.getLast? = some c → c ≠ 46) : w ∈ Ending := by
  rcases List.eq_nil_or_concat w with rfl | ⟨init, d, rfl⟩
  · exact (Language.mem_add _ _ _).mpr (Or.inl ((Language.mem_one _).mpr rfl))
  · rw [List.concat_eq_append] at names last ⊢
    refine (Language.mem_add _ _ _).mpr (Or.inr (Language.mem_mul.mpr ⟨init, star_names.mpr ?_, [d], ?_, rfl⟩))
    · intro c member
      exact names c (List.mem_append_left _ member)
    · have named := names d (by simp)
      have notDot := last d (by simp)
      rcases (Language.mem_add _ _ _).mp named with chars | dot
      · exact chars
      · exact absurd (single_range.mp dot) (by omega)

/-- A word of PNAME_NS is a label in `1 + PrefixWord` and the colon. -/
private theorem prefix_split {w : List Nat} (member : w ∈ Prefix) :
    ∃ m, w = m ++ [58] ∧ m ∈ 1 + PrefixWord := by
  obtain ⟨m, inM, colon, ⟨d, rfl, low, high⟩, rfl⟩ := Language.mem_mul.mp member
  obtain rfl : d = 58 := by omega
  exact ⟨m, rfl, inM⟩

private theorem prefix_of {m : List Nat} (member : m ∈ 1 + PrefixWord) : m ++ [58] ∈ Prefix :=
  Language.mem_mul.mpr ⟨m, member, [58], single_range.mpr ⟨le_rfl, le_rfl⟩, rfl⟩

private theorem label_names {m : List Nat} (member : m ∈ 1 + PrefixWord) : ∀ c ∈ m, NameChar c := by
  rcases (Language.mem_add _ _ _).mp member with empty | word
  · rw [(Language.mem_one _).mp empty]
    simp
  · obtain ⟨first, ⟨d, rfl, base⟩, rest, inRest, rfl⟩ := Language.mem_mul.mp word
    intro c member
    rcases List.mem_cons.mp member with rfl | inRest'
    · exact (Language.mem_add _ _ _).mpr (Or.inl (single_chars.mpr (Or.inl base)))
    · exact ending_names inRest c inRest'

/-- The first code points of a local name: PN_CHARS_U and the digits. -/
private theorem local_split {v : List Nat} (member : v ∈ Local) :
    ∃ c rest, v = c :: rest ∧ [c] ∈ CharsU + Rowl.Iri.Range 48 57 ∧ rest ∈ Ending := by
  obtain ⟨first, inFirst, rest, inRest, rfl⟩ := Language.mem_mul.mp member
  rcases (Language.mem_add _ _ _).mp inFirst with charsU | ⟨d, rfl, -⟩
  · rcases (Language.mem_add _ _ _).mp charsU with ⟨d, rfl, -⟩ | ⟨d, rfl, -⟩
    all_goals exact ⟨d, rest, rfl, inFirst, inRest⟩
  · exact ⟨d, rest, rfl, inFirst, inRest⟩

private theorem start_name {c : Nat} (member : [c] ∈ CharsU + Rowl.Iri.Range 48 57) : NameChar c := by
  refine (Language.mem_add _ _ _).mpr (Or.inl ?_)
  rcases (Language.mem_add _ _ _).mp member with charsU | digit
  · exact (Language.mem_add _ _ _).mpr (Or.inl charsU)
  · exact (Language.mem_add _ _ _).mpr (Or.inr ((Language.mem_add _ _ _).mpr
      (Or.inr ((Language.mem_add _ _ _).mpr (Or.inl digit)))))

private theorem start_ascii {c : Nat} (small : c < 128) :
    [c] ∈ CharsU + Rowl.Iri.Range 48 57 ↔ StartCode c := by
  simp only [CharsU, Language.mem_add, single_base, single_range, base_ascii small]
  unfold StartCode LetterCode
  omega

private theorem local_names {v : List Nat} (member : v ∈ Local) : ∀ c ∈ v, NameChar c := by
  obtain ⟨c, rest, rfl, first, inRest⟩ := local_split member
  intro d member
  rcases List.mem_cons.mp member with rfl | inRest'
  · exact start_name first
  · exact ending_names inRest d inRest'

/-! ### What the scanners test, in terms of the languages -/

/-- The label test of the scanner: empty, or a letter first and no dot last. -/
private def LabelOk (pre : List U8) : Prop :=
  pre = [] ∨ ∃ b rest, pre = b :: rest ∧ LetterCode b.val ∧ ∀ last, pre.getLast? = some last → last.val ≠ 46
/-- The local-name test of the scanner: a letter, `_` or digit first and no dot last. -/
private def LocalOk (pre : List U8) : Prop :=
  ∃ b rest, pre = b :: rest ∧ StartCode b.val ∧ ∀ last, pre.getLast? = some last → last.val ≠ 46

private theorem last_map {pre : List U8} {c : Nat} (found : (pre.map (·.val)).getLast? = some c) :
    ∃ last, pre.getLast? = some last ∧ last.val = c := by
  rw [List.getLast?_map] at found
  cases h : pre.getLast? with
  | none => rw [h] at found; cases found
  | some last => rw [h] at found; exact ⟨last, rfl, Option.some.inj found⟩

private theorem last_cons_map {b : U8} {rest : List U8} {c : Nat}
    (found : (rest.map (·.val)).getLast? = some c) : ∃ last, (b :: rest).getLast? = some last ∧ last.val = c := by
  obtain ⟨last, isLast, value⟩ := last_map found
  refine ⟨last, ?_, value⟩
  rw [List.getLast?_cons, isLast]
  rfl

/-- A word of `PrefixWord`: a base code point and an ending. -/
private theorem prefix_word_split {m : List Nat} (word : m ∈ PrefixWord) :
    ∃ c rest, m = c :: rest ∧ BaseCode c ∧ rest ∈ Ending := by
  obtain ⟨first, ⟨d, rfl, base⟩, rest, inRest, rfl⟩ := Language.mem_mul.mp word
  exact ⟨d, rest, rfl, base, inRest⟩

private theorem label_ok_of_mem {pre : List U8} (codes : ∀ b ∈ pre, LabelCode b.val)
    (member : pre.map (·.val) ∈ 1 + PrefixWord) : LabelOk pre := by
  cases pre with
  | nil => exact Or.inl rfl
  | cons b rest =>
    rcases (Language.mem_add _ _ _).mp member with empty | word
    · cases (Language.mem_one _).mp empty
    · obtain ⟨c, tail, equal, base, inTail⟩ := prefix_word_split word
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨rfl, tailIs⟩ := equal
      refine Or.inr ⟨b, rest, rfl, (base_ascii (label_ascii (codes b (by simp)))).mp base, ?_⟩
      intro last found
      cases rest with
      | nil =>
        obtain rfl : b = last := by simpa using found
        unfold BaseCode at base
        omega
      | cons x more =>
        rw [List.getLast?_cons_cons] at found
        subst tailIs
        exact ending_last inTail last.val (by rw [List.getLast?_map, found]; rfl)

private theorem mem_of_label_ok {pre : List U8} (codes : ∀ b ∈ pre, LabelCode b.val) (ok : LabelOk pre) :
    pre.map (·.val) ∈ 1 + PrefixWord := by
  rcases ok with rfl | ⟨b, rest, rfl, letter, last⟩
  · exact (Language.mem_add _ _ _).mpr (Or.inl ((Language.mem_one _).mpr rfl))
  · refine (Language.mem_add _ _ _).mpr (Or.inr (Language.mem_mul.mpr
      ⟨[b.val], single_base.mpr ?_, rest.map (·.val), ?_, by simp⟩))
    · exact (base_ascii (label_ascii (codes b (by simp)))).mpr letter
    · apply ending_of
      · intro c member
        obtain ⟨x, inRest, rfl⟩ := List.mem_map.mp member
        have code := codes x (List.mem_cons_of_mem _ inRest)
        exact (name_char_ascii (label_ascii code)).mpr code
      · intro c found
        obtain ⟨l, isLast, rfl⟩ := last_cons_map (b := b) found
        exact last l isLast

private theorem local_ok_of_mem {pre : List U8} (codes : ∀ b ∈ pre, LabelCode b.val)
    (member : pre.map (·.val) ∈ Local) : LocalOk pre := by
  obtain ⟨c, tail, equal, first, inTail⟩ := local_split member
  cases pre with
  | nil => simp at equal
  | cons b rest =>
    simp only [List.map_cons, List.cons.injEq] at equal
    obtain ⟨rfl, tailIs⟩ := equal
    have small := label_ascii (codes b (by simp))
    have start := (start_ascii small).mp first
    refine ⟨b, rest, rfl, start, ?_⟩
    intro last found
    cases rest with
    | nil =>
      obtain rfl : b = last := by simpa using found
      unfold StartCode LetterCode at start
      omega
    | cons x more =>
      rw [List.getLast?_cons_cons] at found
      subst tailIs
      exact ending_last inTail last.val (by rw [List.getLast?_map, found]; rfl)

private theorem mem_of_local_ok {pre : List U8} (codes : ∀ b ∈ pre, LabelCode b.val) (ok : LocalOk pre) :
    pre.map (·.val) ∈ Local := by
  obtain ⟨b, rest, rfl, start, last⟩ := ok
  refine Language.mem_mul.mpr
    ⟨[b.val], (start_ascii (label_ascii (codes b (by simp)))).mpr start, rest.map (·.val), ?_, by simp⟩
  apply ending_of
  · intro c member
    obtain ⟨x, inRest, rfl⟩ := List.mem_map.mp member
    have code := codes x (List.mem_cons_of_mem _ inRest)
    exact (name_char_ascii (label_ascii code)).mpr code
  · intro c found
    obtain ⟨l, isLast, rfl⟩ := last_cons_map (b := b) found
    exact last l isLast

/-! ### Spans over ASCII bytes -/

private theorem ascii_unit {bs : List U8} {i : Nat} {b : U8} (found : bs[i]? = some b) (small : b.val < 128) :
    Rowl.Unicode.Prefix bs i = some (b.val, 1) := by
  simp [Rowl.Unicode.Prefix, found, small]

private theorem unit_found {bs : List U8} {i : Nat} {x : Nat × Nat}
    (unit : Rowl.Unicode.Prefix bs i = some x) : ∃ b, bs[i]? = some b := by
  cases found : bs[i]? with
  | none => simp [Rowl.Unicode.Prefix, found] at unit
  | some b => exact ⟨b, rfl⟩

/-- A span whose word begins with a code point starts on a byte. -/
private theorem span_found {bs : List U8} {i e c : Nat} {w : List Nat} (span : Utf8Span bs i e (c :: w)) :
    ∃ b, bs[i]? = some b := by
  cases span with
  | character unit _ _ _ => exact unit_found unit

/-- Over an ASCII byte a span steps exactly that byte. -/
private theorem span_ascii {bs : List U8} {i e c : Nat} {w : List Nat} {b : U8}
    (span : Utf8Span bs i e (c :: w)) (found : bs[i]? = some b) (small : b.val < 128) :
    c = b.val ∧ Utf8Span bs (i + 1) e w := by
  cases span with
  | character unit _ _ rest =>
    rw [ascii_unit found small] at unit
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj unit)
    exact ⟨rfl, rest⟩

private theorem drop_cons {bs rest : List U8} {i : Nat} {b : U8} (split : bs.drop i = b :: rest) :
    bs[i]? = some b ∧ bs.drop (i + 1) = rest := by
  constructor
  · rw [← List.head?_drop, split]
    rfl
  · have step : bs.drop (i + 1) = (bs.drop i).drop 1 := by simp [List.drop_drop]
    rw [step, split]
    rfl

private theorem drop_get {bs pre rest : List U8} {i k : Nat} (split : bs.drop i = pre ++ rest)
    (small : k < pre.length) : bs[i + k]? = pre[k]? := by
  rw [← List.getElem?_drop, split, List.getElem?_append_left small]

private theorem span_append {bs : List U8} {a b c : Nat} {u v : List Nat}
    (first : Utf8Span bs a b u) (second : Utf8Span bs b c v) : Utf8Span bs a c (u ++ v) := by
  revert second
  induction first with
  | empty _ => intro second; simpa using second
  | character unit positive fits _ ih =>
    intro second
    exact .character unit positive fits (ih second)

/-- The bytes after a run start, if at all, with an ASCII byte that is no label byte. -/
private def Stops (rest : List U8) : Prop := ∀ b, rest.head? = some b → b.val < 128 ∧ ¬ LabelCode b.val

/-- Over a run of label bytes ending before an ASCII byte that is not a label
    byte, a span of name characters, a colon and more reads exactly the run,
    and the colon is the byte after it. -/
private theorem walk_label (bs rest : List U8) (stop : Stops rest) :
    ∀ (pre : List U8) (i : Nat), bs.drop i = pre ++ rest → (∀ b ∈ pre, LabelCode b.val) →
    ∀ e m v, Utf8Span bs i e (m ++ 58 :: v) → (∀ c ∈ m, NameChar c) →
    m = pre.map (·.val) ∧ rest.head? = some 58#u8 ∧ Utf8Span bs (i + pre.length + 1) e v := by
  intro pre
  induction pre with
  | nil =>
    intro i split _ e m v span names
    rw [List.nil_append] at split
    have head : bs[i]? = rest.head? := by rw [← split, List.head?_drop]
    cases m with
    | nil =>
      obtain ⟨b, found⟩ := span_found span
      have restHead : rest.head? = some b := by rw [← head, found]
      obtain ⟨small, -⟩ := stop b restHead
      obtain ⟨equal, after⟩ := span_ascii span found small
      have colon : b = 58#u8 := UScalar.eq_of_val_eq equal.symm
      exact ⟨rfl, by rw [restHead, colon], by simpa using after⟩
    | cons c m =>
      obtain ⟨b, found⟩ := span_found span
      have restHead : rest.head? = some b := by rw [← head, found]
      obtain ⟨small, notLabel⟩ := stop b restHead
      obtain ⟨equal, -⟩ := span_ascii span found small
      have named := names c (by simp)
      rw [equal, name_char_ascii small] at named
      exact absurd named notLabel
  | cons b pre ih =>
    intro i split codes e m v span names
    rw [List.cons_append] at split
    obtain ⟨found, split'⟩ := drop_cons split
    have small := label_ascii (codes b (by simp))
    cases m with
    | nil =>
      obtain ⟨equal, -⟩ := span_ascii span found small
      have code := codes b (by simp)
      rw [← equal] at code
      exact absurd code colon_not_label
    | cons c m =>
      obtain ⟨equal, after⟩ := span_ascii span found small
      obtain ⟨same, colon, tail⟩ := ih (i + 1) split' (fun x member => codes x (List.mem_cons_of_mem _ member))
        e m v after (fun x member => names x (List.mem_cons_of_mem _ member))
      refine ⟨by simp [equal, same], colon, ?_⟩
      have index : i + (b :: pre).length + 1 = i + 1 + pre.length + 1 := by simp; omega
      rw [index]
      exact tail

/-- Over a run of label bytes ending before an ASCII byte that is not a label
    byte, a span of name characters reads a prefix of the run. -/
private theorem walk_local (bs rest : List U8) (stop : Stops rest) :
    ∀ (pre : List U8) (i : Nat), bs.drop i = pre ++ rest → (∀ b ∈ pre, LabelCode b.val) →
    ∀ e v, Utf8Span bs i e v → (∀ c ∈ v, NameChar c) →
    ∃ k, k ≤ pre.length ∧ e = i + k ∧ v = (pre.take k).map (·.val) := by
  intro pre
  induction pre with
  | nil =>
    intro i split _ e v span names
    rw [List.nil_append] at split
    cases v with
    | nil =>
      cases span
      exact ⟨0, le_rfl, rfl, rfl⟩
    | cons c v =>
      obtain ⟨b, found⟩ := span_found span
      have restHead : rest.head? = some b := by rw [← split, List.head?_drop, found]
      obtain ⟨small, notLabel⟩ := stop b restHead
      obtain ⟨equal, -⟩ := span_ascii span found small
      have named := names c (by simp)
      rw [equal, name_char_ascii small] at named
      exact absurd named notLabel
  | cons b pre ih =>
    intro i split codes e v span names
    rw [List.cons_append] at split
    obtain ⟨found, split'⟩ := drop_cons split
    have small := label_ascii (codes b (by simp))
    cases v with
    | nil =>
      cases span
      exact ⟨0, by simp, rfl, rfl⟩
    | cons c v =>
      obtain ⟨equal, after⟩ := span_ascii span found small
      obtain ⟨k, bound, endpoint, word⟩ := ih (i + 1) split' (fun x member => codes x (List.mem_cons_of_mem _ member))
        e v after (fun x member => names x (List.mem_cons_of_mem _ member))
      refine ⟨k + 1, by simp; omega, by omega, ?_⟩
      simp [equal, word]

/-- ASCII bytes are a span of their own values. -/
private theorem ascii_span (bs : List U8) :
    ∀ (pre rest : List U8) (i : Nat), bs.drop i = pre ++ rest → (∀ b ∈ pre, b.val < 128) →
    ∀ e w, Utf8Span bs (i + pre.length) e w → Utf8Span bs i e (pre.map (·.val) ++ w) := by
  intro pre rest
  induction pre with
  | nil => intro i _ _ e w span; simpa using span
  | cons b pre ih =>
    intro i split small e w span
    rw [List.cons_append] at split
    obtain ⟨found, split'⟩ := drop_cons split
    have inside : i < bs.length := (List.getElem?_eq_some_iff.mp found).1
    have tail := ih (i + 1) split' (fun x member => small x (List.mem_cons_of_mem _ member)) e w
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using span)
    exact .character (ascii_unit found (small b (by simp))) (by omega) (by omega) tail

/-! ### The byte tests and the run scan -/

private theorem ascii_letter_spec (b : U8) : names.ascii_letter b = .ok (decide (LetterCode b.val)) := by
  unfold names.ascii_letter LetterCode
  by_cases h1 : 65 ≤ b.val <;> by_cases h2 : b.val ≤ 90 <;> by_cases h3 : 97 ≤ b.val <;>
    by_cases h4 : b.val ≤ 122 <;> simp [UScalar.le_equiv, h1, h2, h3, h4]

private theorem local_start_spec (b : U8) : names.local_start b = .ok (decide (StartCode b.val)) := by
  unfold names.local_start StartCode
  rw [ascii_letter_spec]
  by_cases l : LetterCode b.val
  · simp [l]
  · by_cases u : b.val = 95 <;> by_cases d1 : 48 ≤ b.val <;> by_cases d2 : b.val ≤ 57 <;>
      simp [l, u, d1, d2, UScalar.eq_equiv, UScalar.le_equiv]

private theorem label_byte_spec (b : U8) : names.label_byte b = .ok (decide (LabelCode b.val)) := by
  unfold names.label_byte LabelCode
  rw [local_start_spec]
  by_cases s : StartCode b.val
  · simp [s]
  · by_cases e1 : b.val = 45 <;> by_cases e2 : b.val = 46 <;> simp [s, UScalar.eq_equiv, e1, e2]

/-- The run of label bytes from `index`, and the byte after it is no label byte. -/
private theorem label_end_spec (bytes : alloc.vec.Vec U8) (index : Usize) :
    ∃ e, names.label_end bytes index = .ok e ∧ ∃ pre, e.val = index.val + pre.length ∧
      bytes.val.drop index.val = pre ++ bytes.val.drop e.val ∧ (∀ b ∈ pre, LabelCode b.val) ∧
      ∀ b, (bytes.val.drop e.val).head? = some b → ¬ LabelCode b.val := by
  rw [names.label_end]
  by_cases more : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    by_cases code : LabelCode bytes.val[index.val].val
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨e, run, pre, length, split, codes, stop⟩ := label_end_spec bytes next
      refine ⟨e, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, label_byte_spec, code, advance,
        run], bytes.val[index.val] :: pre, by simp; omega, ?_, ?_, stop⟩
      · rw [List.drop_eq_getElem_cons more, ← nextIs, split]
        rfl
      · intro b member
        rcases List.mem_cons.mp member with rfl | member
        · exact code
        · exact codes b member
    · refine ⟨index, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, label_byte_spec, code],
        [], by simp, by simp, by simp, ?_⟩
      intro b found
      rw [List.head?_drop, List.getElem?_eq_getElem more] at found
      obtain rfl := Option.some.inj found
      exact code
  · refine ⟨index, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], [], by simp, by simp, by simp, ?_⟩
    intro b found
    rw [List.drop_eq_nil_of_le (by omega)] at found
    cases found
termination_by bytes.val.length - index.val
decreasing_by omega

/-- The label test: empty, or a letter first and no dot last. -/
private theorem prefix_label_spec (bytes : alloc.vec.Vec U8) (position colon : Usize) (pre : List U8)
    (length : colon.val = position.val + pre.length)
    (split : bytes.val.drop position.val = pre ++ bytes.val.drop colon.val)
    (inside : colon.val < bytes.val.length) :
    names.prefix_label bytes position colon = .ok (decide (LabelOk pre)) := by
  unfold names.prefix_label
  cases pre with
  | nil =>
    have same : colon = position := UScalar.eq_of_val_eq (by simpa using length)
    simp [same, LabelOk]
  | cons b rest =>
    have different : ¬ colon = position := by
      intro same
      have := congrArg UScalar.val same
      simp at length
      omega
    have before : position.val < bytes.val.length := by simp at length; omega
    have first : bytes.val[position.val]? = some b := by
      simpa using drop_get (k := 0) split (by simp)
    have firstIs : bytes.val[position.val] = b := by
      rw [List.getElem?_eq_getElem before] at first
      exact Option.some.inj first
    have lookup : bytes.index_usize position = .ok b := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem before, firstIs]
    by_cases letter : LetterCode b.val
    · obtain ⟨prev, sub, prevValue⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := colon) (y := 1#usize) (by simp at length ⊢; omega))
      have prevIs : prev.val = position.val + rest.length := by simp at prevValue length; omega
      have lastAt : bytes.val[prev.val]? = (b :: rest).getLast? := by
        rw [prevIs, drop_get split (by simp), List.getLast?_eq_getElem?]
        simp
      obtain ⟨last, lastIs⟩ : ∃ last, (b :: rest).getLast? = some last := by
        cases found : (b :: rest).getLast? with
        | none => simp at found
        | some last => exact ⟨last, rfl⟩
      have lastIn : prev.val < bytes.val.length := by simp at length; omega
      have lookupLast : bytes.index_usize prev = .ok last := by
        rw [lastIs, List.getElem?_eq_getElem lastIn] at lastAt
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem lastIn, Option.some.inj lastAt]
      have ok : LabelOk (b :: rest) ↔ last.val ≠ 46 := by
        constructor
        · rintro (empty | ⟨x, more, equal, -, notDot⟩)
          · cases empty
          · exact notDot last lastIs
        · intro notDot
          refine Or.inr ⟨b, rest, rfl, letter, ?_⟩
          intro other found
          rw [lastIs] at found
          obtain rfl := Option.some.inj found
          exact notDot
      simp [different, lookup, ascii_letter_spec, letter, sub, lookupLast, ok, bne, beq_eq_decide, UScalar.eq_equiv]
    · have notOk : ¬ LabelOk (b :: rest) := by
        rintro (empty | ⟨x, more, equal, isLetter, -⟩)
        · cases empty
        · obtain ⟨rfl, -⟩ := List.cons_eq_cons.mp equal
          exact letter isLetter
      simp [different, lookup, ascii_letter_spec, letter, notOk]

/-! ### Prefix names -/

/-- What the prefix-name decision establishes. With `some none` no word made of
    a label, the colon and more has a span from the position; with
    `some (some next)` the label and colon end at `next`, and every such span
    reads its rest from `next`. -/
private def PrefixEnd (bs : List U8) (position : Nat) : Option (Option Usize) → Prop
  | none => True
  | some none => ∀ e m v, Utf8Span bs position e (m ++ 58 :: v) → m ∈ 1 + PrefixWord → False
  | some (some next) =>
    (∃ m, Utf8Span bs position next.val (m ++ [58]) ∧ m ∈ 1 + PrefixWord) ∧
    ∀ e m v, Utf8Span bs position e (m ++ 58 :: v) → m ∈ 1 + PrefixWord → Utf8Span bs next.val e v

private theorem ascii_prefix_end_spec (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ r, names.ascii_prefix_end bytes position = .ok r ∧ PrefixEnd bytes.val position.val r := by
  obtain ⟨colon, run, pre, length, split, codes, stop⟩ := label_end_spec bytes position
  by_cases inside : colon.val < bytes.val.length
  · have lookup : bytes.index_usize colon = .ok bytes.val[colon.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have head : (bytes.val.drop colon.val).head? = some bytes.val[colon.val] := by
      rw [List.head?_drop, List.getElem?_eq_getElem inside]
    by_cases isColon : bytes.val[colon.val] = 58#u8
    · have stops : Stops (bytes.val.drop colon.val) := by
        intro b found
        rw [head, isColon] at found
        obtain rfl := Option.some.inj found
        exact ⟨by simp, colon_not_label⟩
      have walk := fun e m v (span : Utf8Span bytes.val position.val e (m ++ 58 :: v))
          (member : m ∈ 1 + PrefixWord) =>
        walk_label bytes.val _ stops pre position.val split codes e m v span (label_names member)
      have tested := prefix_label_spec bytes position colon pre length split inside
      by_cases ok : LabelOk pre
      · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := colon) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = colon.val + 1 := by simpa using nextValue
        refine ⟨some (some next), by simp [names.ascii_prefix_end, run, alloc.vec.Vec.len_val, UScalar.lt_equiv,
          inside, lookup, isColon, tested, ok, advance], ?_, ?_⟩
        · refine ⟨pre.map (·.val), ?_, mem_of_label_ok codes ok⟩
          have found : bytes.val[colon.val]? = some 58#u8 := by rw [List.getElem?_eq_getElem inside, isColon]
          have colonSpan : Utf8Span bytes.val colon.val next.val [58] := by
            rw [nextIs]
            exact .character (by simpa using ascii_unit found (by simp)) (by omega) (by omega) (.empty (by omega))
          exact ascii_span bytes.val pre _ position.val split (fun b member => label_ascii (codes b member))
            next.val [58] (by rw [← length]; exact colonSpan)
        · intro e m v span member
          obtain ⟨-, -, after⟩ := walk e m v span member
          rw [nextIs, length]
          exact after
      · refine ⟨some none, by simp [names.ascii_prefix_end, run, alloc.vec.Vec.len_val, UScalar.lt_equiv,
          inside, lookup, isColon, tested, ok], ?_⟩
        intro e m v span member
        obtain ⟨same, -, -⟩ := walk e m v span member
        exact ok (label_ok_of_mem codes (same ▸ member))
    · by_cases small : bytes.val[colon.val].val < 128
      · have stops : Stops (bytes.val.drop colon.val) := by
          intro b found
          have notLabel := stop b found
          rw [head] at found
          obtain rfl := Option.some.inj found
          exact ⟨small, notLabel⟩
        have notColon : ¬ bytes.val[colon.val].val = 58 := fun equal => isColon (UScalar.eq_of_val_eq equal)
        refine ⟨some none, by simp [names.ascii_prefix_end, run, alloc.vec.Vec.len_val, UScalar.lt_equiv,
          inside, lookup, isColon, small], ?_⟩
        intro e m v span member
        obtain ⟨-, colonHead, -⟩ :=
          walk_label bytes.val _ stops pre position.val split codes e m v span (label_names member)
        rw [head] at colonHead
        exact isColon (Option.some.inj colonHead)
      · refine ⟨none, by simp [names.ascii_prefix_end, run, alloc.vec.Vec.len_val, UScalar.lt_equiv,
          inside, lookup, isColon, small], trivial⟩
  · have empty : bytes.val.drop colon.val = [] := List.drop_eq_nil_of_le (by omega)
    have stops : Stops (bytes.val.drop colon.val) := by
      rw [empty]
      intro b found
      cases found
    refine ⟨some none, by simp [names.ascii_prefix_end, run, alloc.vec.Vec.len_val, UScalar.lt_equiv, inside], ?_⟩
    intro e m v span member
    obtain ⟨-, colonHead, -⟩ :=
      walk_label bytes.val _ stops pre position.val split codes e m v span (label_names member)
    rw [empty] at colonHead
    cases colonHead

/-- Whenever the ASCII scanner answers, its answer is the greatest endpoint of a
    PNAME_NS word from the position, or no endpoint when none has one. -/
theorem ascii_prefix_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ r, names.ascii_prefix bytes position = .ok r ∧
      ∀ result, r = some result → ∃ endpoint, result = .Matched endpoint ∧
        Maximal (Candidate bytes.val position.val Prefix) endpoint := by
  obtain ⟨decided, run, correct⟩ := ascii_prefix_end_spec bytes position
  cases decided with
  | none => exact ⟨none, by simp [names.ascii_prefix, run], by simp⟩
  | some found =>
    refine ⟨some (.Matched found), by simp [names.ascii_prefix, run], ?_⟩
    rintro result equal
    obtain rfl := Option.some.inj equal
    refine ⟨found, rfl, ?_⟩
    cases found with
    | none =>
      rintro e ⟨w, span, member⟩
      obtain ⟨m, rfl, label⟩ := prefix_split member
      exact correct e m [] span label
    | some next =>
      obtain ⟨⟨m, span, label⟩, through⟩ := correct
      refine ⟨⟨m ++ [58], span, prefix_of label⟩, ?_⟩
      rintro e ⟨w, other, member⟩
      obtain ⟨m', rfl, label'⟩ := prefix_split member
      have rest := through e m' [] other label'
      cases rest
      exact le_rfl

/-! ### Local names and abbreviated IRIs -/

/-- Backing off over trailing dots ends after a byte other than a dot, or just
    after the first byte, with only dots between the result and `finish`. -/
private theorem trim_dots_spec (bytes : alloc.vec.Vec U8) (start finish : Usize)
    (before : start.val < finish.val) (inside : finish.val ≤ bytes.val.length) :
    ∃ t, names.trim_dots bytes start finish = .ok t ∧ start.val < t.val ∧ t.val ≤ finish.val ∧
      (t.val = start.val + 1 ∨ ∀ b, bytes.val[t.val - 1]? = some b → b.val ≠ 46) ∧
      ∀ j, t.val ≤ j → j < finish.val → bytes.val[j]? = some 46#u8 := by
  rw [names.trim_dots]
  obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := start) (y := 1#usize) (by scalar_tac))
  have nextIs : next.val = start.val + 1 := by simpa using nextValue
  by_cases more : next.val < finish.val
  · obtain ⟨prev, sub, prevValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := finish) (y := 1#usize) (by simp; omega))
    have prevIs : prev.val = finish.val - 1 := by simpa using prevValue.1
    have prevIn : prev.val < bytes.val.length := by omega
    have lookup : bytes.index_usize prev = .ok bytes.val[prev.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem prevIn]
    by_cases dot : bytes.val[prev.val] = 46#u8
    · obtain ⟨t, run, low, high, last, dots⟩ := trim_dots_spec bytes start prev (by omega) (by omega)
      refine ⟨t, by simp [add, UScalar.lt_equiv, more, sub, lookup, dot, run], low, by omega, last, ?_⟩
      intro j from_ below
      by_cases same : j = prev.val
      · rw [same, List.getElem?_eq_getElem prevIn, dot]
      · exact dots j from_ (by omega)
    · refine ⟨finish, by simp [add, UScalar.lt_equiv, more, sub, lookup, dot], before, le_rfl, Or.inr ?_,
        fun j from_ below => absurd below (by omega)⟩
      intro b found
      rw [show finish.val - 1 = prev.val by omega, List.getElem?_eq_getElem prevIn] at found
      obtain rfl := Option.some.inj found
      exact fun equal => dot (UScalar.eq_of_val_eq equal)
  · refine ⟨finish, by simp [add, UScalar.lt_equiv, more], before, le_rfl, Or.inl (by omega),
      fun j from_ below => absurd below (by omega)⟩
termination_by finish.val - start.val
decreasing_by omega

private theorem last_take {l : List U8} {k : Nat} (positive : 0 < k) (bound : k ≤ l.length) :
    (l.take k).getLast? = l[k - 1]? := by
  rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left bound, List.getElem?_take]
  simp [show k - 1 < k by omega]

/-- The local name in a run of label bytes followed by an ASCII byte that is no
    label byte: up to the last byte other than a dot, when the run begins with a
    letter, `_` or a digit; no local name otherwise. -/
private theorem local_end_spec (bytes : alloc.vec.Vec U8) (start finish : Usize) (pre : List U8)
    (length : finish.val = start.val + pre.length)
    (split : bytes.val.drop start.val = pre ++ bytes.val.drop finish.val)
    (codes : ∀ b ∈ pre, LabelCode b.val) (stops : Stops (bytes.val.drop finish.val)) :
    ∃ o, names.local_end bytes start finish = .ok o ∧ Maximal (Candidate bytes.val start.val Local) o := by
  have walk := fun e v (span : Utf8Span bytes.val start.val e v) (member : v ∈ Local) =>
    walk_local bytes.val _ stops pre start.val split codes e v span (local_names member)
  have takeCodes : ∀ k, ∀ b ∈ pre.take k, LabelCode b.val := fun k b member => codes b (List.mem_of_mem_take member)
  cases pre with
  | nil =>
    have notBefore : ¬ start.val < finish.val := by simp at length; omega
    refine ⟨none, by simp [names.local_end, UScalar.lt_equiv, notBefore], ?_⟩
    rintro e ⟨v, span, member⟩
    obtain ⟨k, bound, -, word⟩ := walk e v span member
    obtain ⟨c, rest, equal, -⟩ := local_split member
    rw [word] at equal
    simp at equal
  | cons b rest =>
    have before : start.val < finish.val := by simp at length; omega
    have inside : finish.val ≤ bytes.val.length := by
      have sizes := congrArg List.length split
      simp at sizes length
      omega
    have first : bytes.val[start.val]? = some b := by simpa using drop_get (k := 0) split (by simp)
    have startIn : start.val < bytes.val.length := by omega
    have lookup : bytes.index_usize start = .ok b := by
      rw [List.getElem?_eq_getElem startIn] at first
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem startIn, Option.some.inj first]
    by_cases startCode : StartCode b.val
    · obtain ⟨t, trimmed, low, high, lastOk, dots⟩ := trim_dots_spec bytes start finish before inside
      refine ⟨some t, by simp [names.local_end, UScalar.lt_equiv, before, lookup, local_start_spec, startCode,
        trimmed], ?_, ?_⟩
      · have kBound : t.val - start.val ≤ (b :: rest).length := by simp at length ⊢; omega
        have takeSplit : bytes.val.drop start.val =
            (b :: rest).take (t.val - start.val) ++ ((b :: rest).drop (t.val - start.val) ++ bytes.val.drop finish.val) := by
          rw [split, ← List.append_assoc, List.take_append_drop]
        have span := ascii_span bytes.val ((b :: rest).take (t.val - start.val)) _ start.val takeSplit
          (fun x member => label_ascii (takeCodes _ x member)) t.val []
          (by rw [List.length_take, Nat.min_eq_left kBound, show start.val + (t.val - start.val) = t.val by omega]
              exact .empty (by omega))
        refine ⟨_, by simpa using span, mem_of_local_ok (takeCodes _) ?_⟩
        refine ⟨b, rest.take (t.val - start.val - 1), ?_, startCode, ?_⟩
        · rw [show t.val - start.val = (t.val - start.val - 1) + 1 by omega, List.take_succ_cons]
          simp
        · intro last found
          rw [last_take (by omega) kBound] at found
          have at_ : bytes.val[start.val + (t.val - start.val - 1)]? = some last := by
            rw [drop_get split (by simp at length ⊢; omega), found]
          rcases lastOk with isFirst | notDot
          · rw [show t.val - start.val - 1 = 0 by omega] at found
            simp at found
            subst found
            unfold StartCode LetterCode at startCode
            omega
          · exact notDot last (by rw [show t.val - 1 = start.val + (t.val - start.val - 1) by omega]; exact at_)
      · rintro x ⟨v, span, member⟩
        obtain ⟨k, bound, endpoint, word⟩ := walk x v span member
        obtain ⟨y, more, equal, -, notDot⟩ := local_ok_of_mem (takeCodes k) (word ▸ member)
        have positive : 0 < k := by
          rcases Nat.eq_zero_or_pos k with zero | positive
          · rw [zero] at equal; simp at equal
          · exact positive
        by_contra greater
        have dotAt := dots (x - 1) (by omega) (by omega)
        obtain ⟨last, lastIs⟩ : ∃ last, ((b :: rest).take k).getLast? = some last := by
          rw [equal]
          cases found : (y :: more).getLast? with
          | none => simp at found
          | some last => exact ⟨last, rfl⟩
        have notDotLast := notDot last lastIs
        rw [last_take positive bound] at lastIs
        rw [show x - 1 = start.val + (k - 1) by omega, drop_get split (by omega), lastIs] at dotAt
        exact notDotLast (by rw [Option.some.inj dotAt]; rfl)
    · refine ⟨none, by simp [names.local_end, UScalar.lt_equiv, before, lookup, local_start_spec, startCode], ?_⟩
      rintro x ⟨v, span, member⟩
      obtain ⟨k, bound, endpoint, word⟩ := walk x v span member
      obtain ⟨y, more, equal, startY, -⟩ := local_ok_of_mem (takeCodes k) (word ▸ member)
      cases k with
      | zero => simp at equal
      | succ k =>
        rw [List.take_succ_cons] at equal
        obtain ⟨rfl, -⟩ := List.cons_eq_cons.mp equal
        exact startCode startY

private theorem ascii_at_spec (bytes : alloc.vec.Vec U8) (index : Usize) :
    names.ascii_at bytes index = .ok (decide (∀ b, bytes.val[index.val]? = some b → b.val < 128)) := by
  unfold names.ascii_at
  by_cases more : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, List.getElem?_eq_getElem more]
  · have none_ : bytes.val[index.val]? = none := List.getElem?_eq_none (by omega)
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, none_]

/-- Whenever the local scan answers, its answer is the greatest endpoint of a
    local name from `start`. -/
private theorem ascii_local_spec (bytes : alloc.vec.Vec U8) (start : Usize) :
    ∃ r, names.ascii_local bytes start = .ok r ∧
      ∀ result, r = some result → ∃ endpoint, result = .Matched endpoint ∧
        Maximal (Candidate bytes.val start.val Local) endpoint := by
  obtain ⟨finish, run, pre, length, split, codes, stop⟩ := label_end_spec bytes start
  by_cases ascii : ∀ b, bytes.val[finish.val]? = some b → b.val < 128
  · have stops : Stops (bytes.val.drop finish.val) := fun b found =>
      ⟨ascii b (by rw [← List.head?_drop]; exact found), stop b found⟩
    obtain ⟨o, local_, maximal⟩ := local_end_spec bytes start finish pre length split codes stops
    have tested : names.ascii_at bytes finish = .ok true := by rw [ascii_at_spec, decide_eq_true ascii]
    refine ⟨some (.Matched o), by simp [names.ascii_local, run, tested, local_], ?_⟩
    rintro result equal
    obtain rfl := Option.some.inj equal
    exact ⟨o, rfl, maximal⟩
  · have tested : names.ascii_at bytes finish = .ok false := by rw [ascii_at_spec, decide_eq_false ascii]
    exact ⟨none, by simp [names.ascii_local, run, tested], by simp⟩

/-- Whenever the ASCII scanner answers, its answer is the greatest endpoint of a
    PNAME_LN word from the position, or no endpoint when none has one. -/
theorem ascii_abbreviated_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ r, names.ascii_abbreviated bytes position = .ok r ∧
      ∀ result, r = some result → ∃ endpoint, result = .Matched endpoint ∧
        Maximal (Candidate bytes.val position.val Abbreviated) endpoint := by
  obtain ⟨decided, run, correct⟩ := ascii_prefix_end_spec bytes position
  cases decided with
  | none => exact ⟨none, by simp [names.ascii_abbreviated, run], by simp⟩
  | some found =>
    cases found with
    | none =>
      refine ⟨some (.Matched none), by simp [names.ascii_abbreviated, run], ?_⟩
      rintro result equal
      obtain rfl := Option.some.inj equal
      refine ⟨none, rfl, ?_⟩
      rintro e ⟨w, span, member⟩
      obtain ⟨u, inU, v, -, rfl⟩ := Language.mem_mul.mp member
      obtain ⟨m, rfl, label⟩ := prefix_split inU
      exact correct e m v (by simpa using span) label
    | some next =>
      obtain ⟨⟨m, labelSpan, label⟩, through⟩ := correct
      obtain ⟨r, local_, decidedLocal⟩ := ascii_local_spec bytes next
      refine ⟨r, by simp [names.ascii_abbreviated, run, local_], ?_⟩
      intro result equal
      obtain ⟨endpoint, rfl, maximal⟩ := decidedLocal result equal
      refine ⟨endpoint, rfl, ?_⟩
      have same : Candidate bytes.val position.val Abbreviated = Candidate bytes.val next.val Local := by
        funext x
        apply propext
        constructor
        · rintro ⟨w, span, member⟩
          obtain ⟨u, inU, v, inV, rfl⟩ := Language.mem_mul.mp member
          obtain ⟨m', rfl, label'⟩ := prefix_split inU
          exact ⟨v, through x m' v (by simpa using span) label', inV⟩
        · rintro ⟨v, span, member⟩
          exact ⟨(m ++ [58]) ++ v, span_append labelSpan span, Language.append_mem_mul (prefix_of label) member⟩
      rw [same]
      exact maximal

end Scan

/-! ## Whole names over ASCII bytes

`validate_prefix`, `validate_local` and `validate_abbreviated`, and the
lexer's `recognize` for the two prefixed-name terminals, accept a buffer that
an ASCII scan from its start reads whole without matching the grammar. -/

section Whole
open Rowl.Longest (Utf8Span Candidate Maximal)

/-- A span that ends at the end of the bytes decodes the rest of them. -/
private theorem span_to_end {bs : List U8} {i : Nat} {w : List Nat}
    (span : Utf8Span bs i bs.length w) : Utf8From bs i w := by
  generalize finish : bs.length = e at span
  induction span with
  | empty _ => subst finish; exact .endOfInput
  | character unit positive fits _ ih => exact .character unit positive fits (ih finish)

/-- The whole-buffer test of a scan result. -/
theorem whole_total_correct (r : Option longest.PrefixResult) (length : Usize) :
    names.whole r length = .ok (decide (r = some (.Matched (some length)))) := by
  rcases r with _ | ((_ | e) | error) <;> simp [names.whole]

/-- When an ASCII scan from the start of the bytes, whose answers are greatest
    candidate endpoints, reads them whole, they decode to a word of the language. -/
theorem whole_scan_accepted {language : Language Nat} {bytes : alloc.vec.Vec U8}
    {r : Option longest.PrefixResult}
    (decided : ∀ result, r = some result → ∃ endpoint, result = .Matched endpoint ∧
      Maximal (Candidate bytes.val (0#usize).val language) endpoint)
    (full : r = some (.Matched (some (alloc.vec.Vec.len bytes)))) :
    ∃ word, Utf8From bytes.val 0 word ∧ word ∈ language := by
  obtain ⟨endpoint, same, maximal⟩ := decided _ full
  cases same
  obtain ⟨⟨word, span, member⟩, -⟩ := maximal
  simp only [alloc.vec.Vec.len_val] at span
  exact ⟨word, span_to_end (by simpa using span), member⟩

end Whole

private theorem converted (grammar : Language Nat) (e : regular.Expression) (bytes : List U8)
    (result : regular.MatchResult) (equal : Denotes e = grammar) :
    MatchCorrect e bytes 0 result ↔ Rowl.Iri.ValidationCorrect grammar bytes result := by
  cases result <;> simp [MatchCorrect, Rowl.Iri.ValidationCorrect, equal]

/-- Whole-byte exact prefix acceptance or the original malformed UTF-8 error. -/
theorem validate_prefix_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ result, names.validate_prefix bytes = .ok result ∧ Rowl.Iri.ValidationCorrect Prefix bytes.val result := by
  obtain ⟨r, scanned, decided⟩ := ascii_prefix_correct bytes 0#usize
  by_cases full : r = some (.Matched (some (alloc.vec.Vec.len bytes)))
  · obtain ⟨word, utf8, member⟩ := whole_scan_accepted decided full
    exact ⟨.Matched true, by simp [names.validate_prefix, scanned, whole_total_correct, full],
      word, utf8, by simp [member]⟩
  · obtain ⟨e, compiled, semantic⟩ := prefix_grammar_total_correct
    obtain ⟨result, executed, correct⟩ := matches_utf8_total_correct e bytes
    exact ⟨result, by simp [names.validate_prefix, scanned, whole_total_correct, full, compiled, executed],
      (converted _ _ _ _ semantic).mp correct⟩
/-- Whole-byte exact local-name acceptance or the original malformed UTF-8 error. -/
theorem validate_local_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ result, names.validate_local bytes = .ok result ∧ Rowl.Iri.ValidationCorrect Local bytes.val result := by
  obtain ⟨r, scanned, decided⟩ := ascii_local_spec bytes 0#usize
  by_cases full : r = some (.Matched (some (alloc.vec.Vec.len bytes)))
  · obtain ⟨word, utf8, member⟩ := whole_scan_accepted decided full
    exact ⟨.Matched true, by simp [names.validate_local, scanned, whole_total_correct, full],
      word, utf8, by simp [member]⟩
  · obtain ⟨e, compiled, semantic⟩ := local_grammar_total_correct
    obtain ⟨result, executed, correct⟩ := matches_utf8_total_correct e bytes
    exact ⟨result, by simp [names.validate_local, scanned, whole_total_correct, full, compiled, executed],
      (converted _ _ _ _ semantic).mp correct⟩
/-- Whole-byte exact abbreviated-IRI acceptance and complete suffix validation. -/
theorem validate_abbreviated_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ result, names.validate_abbreviated bytes = .ok result ∧ Rowl.Iri.ValidationCorrect Abbreviated bytes.val result := by
  obtain ⟨r, scanned, decided⟩ := ascii_abbreviated_correct bytes 0#usize
  by_cases full : r = some (.Matched (some (alloc.vec.Vec.len bytes)))
  · obtain ⟨word, utf8, member⟩ := whole_scan_accepted decided full
    exact ⟨.Matched true, by simp [names.validate_abbreviated, scanned, whole_total_correct, full],
      word, utf8, by simp [member]⟩
  · obtain ⟨e, compiled, semantic⟩ := abbreviated_grammar_total_correct
    obtain ⟨result, executed, correct⟩ := matches_utf8_total_correct e bytes
    exact ⟨result, by simp [names.validate_abbreviated, scanned, whole_total_correct, full, compiled, executed],
      (converted _ _ _ _ semantic).mp correct⟩
/-- Whole-byte exact node-ID acceptance; scope assignment remains separate. -/
theorem validate_node_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ result, names.validate_node bytes = .ok result ∧ Rowl.Iri.ValidationCorrect Node bytes.val result := by
  obtain ⟨e, compiled, semantic⟩ := node_grammar_total_correct
  obtain ⟨result, executed, correct⟩ := matches_utf8_total_correct e bytes
  exact ⟨result, by simp [names.validate_node, compiled, executed], (converted _ _ _ _ semantic).mp correct⟩

theorem validate_prefix_accepted_iff (bytes : alloc.vec.Vec U8) :
    names.validate_prefix bytes = .ok (.Matched true) ↔ ∃ word, Utf8From bytes.val 0 word ∧ word ∈ Prefix := by
  obtain ⟨r, scanned, decided⟩ := ascii_prefix_correct bytes 0#usize
  by_cases full : r = some (.Matched (some (alloc.vec.Vec.len bytes)))
  · have accepted := whole_scan_accepted decided full
    simp [names.validate_prefix, scanned, whole_total_correct, full, accepted]
  · obtain ⟨e, compiled, semantic⟩ := prefix_grammar_total_correct
    simpa [names.validate_prefix, scanned, whole_total_correct, full, compiled, semantic] using
      matches_utf8_accepted_iff e bytes
theorem validate_local_accepted_iff (bytes : alloc.vec.Vec U8) :
    names.validate_local bytes = .ok (.Matched true) ↔ ∃ word, Utf8From bytes.val 0 word ∧ word ∈ Local := by
  obtain ⟨r, scanned, decided⟩ := ascii_local_spec bytes 0#usize
  by_cases full : r = some (.Matched (some (alloc.vec.Vec.len bytes)))
  · have accepted := whole_scan_accepted decided full
    simp [names.validate_local, scanned, whole_total_correct, full, accepted]
  · obtain ⟨e, compiled, semantic⟩ := local_grammar_total_correct
    simpa [names.validate_local, scanned, whole_total_correct, full, compiled, semantic] using
      matches_utf8_accepted_iff e bytes
theorem validate_abbreviated_accepted_iff (bytes : alloc.vec.Vec U8) :
    names.validate_abbreviated bytes = .ok (.Matched true) ↔ ∃ word, Utf8From bytes.val 0 word ∧ word ∈ Abbreviated := by
  obtain ⟨r, scanned, decided⟩ := ascii_abbreviated_correct bytes 0#usize
  by_cases full : r = some (.Matched (some (alloc.vec.Vec.len bytes)))
  · have accepted := whole_scan_accepted decided full
    simp [names.validate_abbreviated, scanned, whole_total_correct, full, accepted]
  · obtain ⟨e, compiled, semantic⟩ := abbreviated_grammar_total_correct
    simpa [names.validate_abbreviated, scanned, whole_total_correct, full, compiled, semantic] using
      matches_utf8_accepted_iff e bytes
theorem validate_node_accepted_iff (bytes : alloc.vec.Vec U8) :
    names.validate_node bytes = .ok (.Matched true) ↔ ∃ word, Utf8From bytes.val 0 word ∧ word ∈ Node := by
  obtain ⟨e, compiled, semantic⟩ := node_grammar_total_correct
  simpa [names.validate_node, compiled, semantic] using matches_utf8_accepted_iff e bytes

end Rowl.Names
