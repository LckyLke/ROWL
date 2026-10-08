import Rowl.Iri
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open scoped Computability
namespace Rowl.LangTag
open regular Rowl.Regular
open Rowl.Iri (Range AtMost)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable
private def Ch (cp : Nat) : Language Nat := Range cp cp
private def Optional (a : Language Nat) : Language Nat := 1 + a
private def Positive (a : Language Nat) : Language Nat := a * a∗
private def Between (a : Language Nat) (lower extra : Nat) : Language Nat := a^lower * AtMost a extra
private def Alpha : Language Nat := Range 65 90 + Range 97 122
private def Digit : Language Nat := Range 48 57
private def Alnum : Language Nat := Alpha + Digit
private def Singleton : Language Nat := Digit + ((Range 65 87 + Range 89 90) + (Range 97 119 + Range 121 122))
private def Dashed (a : Language Nat) : Language Nat := Ch 45 * a
private def CaseChar (cp : Nat) : Language Nat := if 97 ≤ cp ∧ cp ≤ 122 then Ch cp + Ch (cp-32) else Ch cp
private def CaseWord : List Nat → Language Nat
  | [] => 1
  | cp :: tail => CaseChar cp * CaseWord tail
private def Word (s : String) : Language Nat := CaseWord (s.toList.map Char.toNat)
private def Grandfathered : Language Nat :=
  Word "en-gb-oed" + (Word "i-ami" + (Word "i-bnn" +
  (Word "i-default" + (Word "i-enochian" + (Word "i-hak" +
  (Word "i-klingon" + (Word "i-lux" + (Word "i-mingo" +
  (Word "i-navajo" + (Word "i-pwn" + (Word "i-tao" +
  (Word "i-tay" + (Word "i-tsu" + (Word "sgn-be-fr" +
  (Word "sgn-be-nl" + (Word "sgn-ch-de" + (Word "art-lojban" +
  (Word "cel-gaulish" + (Word "no-bok" + (Word "no-nyn" +
  (Word "zh-guoyu" + (Word "zh-hakka" + (Word "zh-min" +
  (Word "zh-min-nan" + Word "zh-xiang"))))))))))))))))))))))))
private def Extlang : Language Nat := Alpha^3 * AtMost (Dashed (Alpha^3)) 2
private def LanguageSubtag : Language Nat := Between Alpha 2 1 * Optional (Dashed Extlang) + (Alpha^4 + Between Alpha 5 3)
private def Variant : Language Nat := Between Alnum 5 3 + Digit * Alnum^3
private def Extension : Language Nat := Singleton * Positive (Dashed (Between Alnum 2 6))
private def PrivateUse : Language Nat := (Ch 120 + Ch 88) * Positive (Dashed (Between Alnum 1 7))
private def Langtag : Language Nat := LanguageSubtag * (Optional (Dashed (Alpha^4)) *
  (Optional (Dashed (Alpha^2 + Digit^3)) * ((Dashed Variant)∗ * ((Dashed Extension)∗ * Optional (Dashed PrivateUse)))))
/-- RFC 5646 §2.1/§2.2.9 ABNF. Registry validity and duplicate-validity
    restrictions are not prerequisites for RDF well-formed language tags. -/
def WellFormedLanguage : Language Nat := Langtag + (PrivateUse + Grandfathered)
/-- The explicitly named RFC langtag production, with no standalone alternatives. -/
def NormalLanguage : Language Nat := Langtag
@[local step] private theorem range_spec (lower upper : U32) :
    langtag.range lower upper ⦃ e => Denotes e = Range lower.val upper.val ⦄ := by
  simp [langtag.range, Denotes, Range]
@[local step] private theorem ch_spec (cp : U32) :
    langtag.ch cp ⦃ e => Denotes e = Ch cp.val ⦄ := by
  simp [langtag.ch, langtag.range, Denotes, Ch, Range]
@[local step] private theorem alt_spec (a b : Expression) :
    langtag.alt a b ⦃ e => Denotes e = Denotes a + Denotes b ⦄ := by simp [langtag.alt, Denotes]
@[local step] private theorem cat_spec (a b : Expression) :
    langtag.cat a b ⦃ e => Denotes e = Denotes a * Denotes b ⦄ := by simp [langtag.cat, Denotes]
@[local step] private theorem opt_spec (a : Expression) :
    langtag.opt a ⦃ e => Denotes e = Optional (Denotes a) ⦄ := by simp [langtag.opt, langtag.alt, Denotes, Optional]
@[local step] private theorem star_spec (a : Expression) :
    langtag.star a ⦃ e => Denotes e = (Denotes a)∗ ⦄ := by simp [langtag.star, Denotes]
@[local step] private theorem plus_spec (a : Expression) :
    langtag.plus a ⦃ e => Denotes e = Positive (Denotes a) ⦄ := by
  simp [langtag.plus, copy_expression_total, langtag.star, langtag.cat, Denotes, Positive]
@[local step] private theorem exact_spec (a : Expression) (count : U8) :
    langtag.exact a count ⦃ e => Denotes e = (Denotes a)^count.val ⦄ := by
  rw [langtag.exact]
  split
  · rename_i zero
    simp [zero, Denotes]
  · rw [copy_expression_total]
    simp only [bind_ok]
    step as ⟨next, hn⟩
    obtain ⟨e, he, sem⟩ := WP.spec_imp_exists (exact_spec a next)
    simp only [he, bind_ok, langtag.cat, WP.spec_ok, Denotes, sem]
    have eq : count.val = next.val + 1 := by scalar_tac
    rw [eq, pow_succ']
termination_by count.val
decreasing_by scalar_tac
@[local step] private theorem up_to_spec (a : Expression) (count : U8) :
    langtag.up_to a count ⦃ e => Denotes e = AtMost (Denotes a) count.val ⦄ := by
  rw [langtag.up_to]
  split
  · rename_i zero
    simp [zero, Denotes, AtMost]
  · rw [copy_expression_total]
    simp only [bind_ok]
    step as ⟨next, hn⟩
    obtain ⟨e, he, sem⟩ := WP.spec_imp_exists (up_to_spec a next)
    simp only [he, bind_ok, langtag.cat, langtag.opt, langtag.alt, WP.spec_ok, Denotes, sem]
    have eq : count.val = next.val + 1 := by scalar_tac
    rw [eq, AtMost]
termination_by count.val
decreasing_by scalar_tac
@[local step] private theorem between_spec (a : Expression) (lower extra : U8) :
    langtag.between a lower extra ⦃ e => Denotes e = Between (Denotes a) lower.val extra.val ⦄ := by
  unfold langtag.between
  step*
  simp_all [Between]
@[local step] private theorem alpha_spec : langtag.alpha ⦃ e => Denotes e = Alpha ⦄ := by
  unfold langtag.alpha
  step*
  simp_all [Alpha]
@[local step] private theorem digit_spec : langtag.digit ⦃ e => Denotes e = Digit ⦄ := by
  unfold langtag.digit
  step*
  simp_all [Digit]
@[local step] private theorem alnum_spec : langtag.alnum ⦃ e => Denotes e = Alnum ⦄ := by
  unfold langtag.alnum
  step*
  simp_all [Alnum]
@[local step] private theorem singleton_spec : langtag.singleton ⦃ e => Denotes e = Singleton ⦄ := by
  unfold langtag.singleton
  step*
  simp_all [Singleton]
@[local step] private theorem dashed_spec (a : Expression) :
    langtag.dashed a ⦃ e => Denotes e = Dashed (Denotes a) ⦄ := by
  unfold langtag.dashed
  step*
  simp_all [Dashed]
private theorem literal_from_spec (bytes : Slice U8) (position : Usize)
    (bounded : position.val ≤ bytes.val.length) :
    langtag.literal_from bytes position ⦃ e => Denotes e = CaseWord ((bytes.val.drop position.val).map UScalar.val) ⦄ := by
  rw [langtag.literal_from]
  split
  · rename_i endOfInput
    simp [endOfInput, Denotes, CaseWord]
  · rename_i notEnd
    have beforeEnd : position.val < bytes.val.length := by scalar_tac
    step as ⟨byte, hb⟩
    simp only [lift, bind_ok]
    generalize cp_eq : core.convert.num.FromU32U8.from byte = cp
    have hc' : cp.val = byte.val := by rw [← cp_eq]; simp
    have tokenSpec :
      (if cp >= 97#u32 then if cp <= 122#u32 then do
        let e ← langtag.ch cp
        let upper ← cp - 32#u32
        let e' ← langtag.ch upper
        langtag.alt e e'
       else langtag.ch cp else langtag.ch cp) ⦃ token => Denotes token = CaseChar byte.val ⦄ := by
      split
      · split
        · step*
          simp_all [CaseChar]
        · step*
          simp_all [CaseChar]
      · step*
        simp_all [CaseChar]
    step as ⟨token, ht⟩
    step as ⟨next, hn⟩
    obtain ⟨tail, he, hs⟩ := WP.spec_imp_exists (literal_from_spec bytes next (by scalar_tac))
    simp only [he, bind_ok, langtag.cat, WP.spec_ok, Denotes, hs]
    rw [List.drop_eq_getElem_cons beforeEnd]
    simp only [List.map_cons, CaseWord]
    have eq : next.val = position.val + 1 := by scalar_tac
    simp_all [eq]
termination_by bytes.val.length - position.val
decreasing_by scalar_tac
@[local step] private theorem literal_spec (bytes : Slice U8) :
    langtag.literal bytes ⦃ e => Denotes e = CaseWord (bytes.val.map UScalar.val) ⦄ := by
  simpa [langtag.literal] using literal_from_spec bytes 0#usize (by simp)
@[local step] private theorem grandfathered_spec : langtag.grandfathered ⦃ e => Denotes e = Grandfathered ⦄ := by
  unfold langtag.grandfathered
  step*
  simp_all [Grandfathered, Word]
@[local step] private theorem language_spec : langtag.language ⦃ e => Denotes e = LanguageSubtag ⦄ := by
  unfold langtag.language
  step*
  simp_all [LanguageSubtag, Extlang]
@[local step] private theorem variant_spec : langtag.variant ⦃ e => Denotes e = Variant ⦄ := by
  unfold langtag.variant
  step*
  simp_all [Variant]
@[local step] private theorem extension_spec : langtag.extension ⦃ e => Denotes e = Extension ⦄ := by
  unfold langtag.extension
  step*
  simp_all [Extension]
@[local step] private theorem private_use_spec : langtag.private_use ⦃ e => Denotes e = PrivateUse ⦄ := by
  unfold langtag.private_use
  step*
  simp_all [PrivateUse]
@[local step] private theorem langtag_spec : langtag.langtag ⦃ e => Denotes e = Langtag ⦄ := by
  unfold langtag.langtag
  step*
  simp_all [Langtag]
theorem grammar_total_correct : ∃ e, langtag.grammar = .ok e ∧ Denotes e = WellFormedLanguage := by
  apply WP.spec_imp_exists
  unfold langtag.grammar
  step*
  simp_all [WellFormedLanguage]
/-- Exact explicitly named RFC 5646 langtag subproduction, distinct from the
    broader Language-Tag alternatives. -/
theorem normal_grammar_total_correct : ∃ e, langtag.normal_grammar = .ok e ∧ Denotes e = NormalLanguage := by
  simpa [langtag.normal_grammar, NormalLanguage] using WP.spec_imp_exists langtag_spec
theorem well_formed_total_correct (bytes : alloc.vec.Vec U8) : ∃ accepted, langtag.well_formed bytes = .ok accepted := by
  obtain ⟨e, he, hs⟩ := grammar_total_correct
  obtain ⟨result, hr, hc⟩ := matches_utf8_total_correct e bytes
  cases result <;> simp [langtag.well_formed, he, hr]
theorem well_formed_accepted_iff (bytes : alloc.vec.Vec U8) :
    langtag.well_formed bytes = .ok true ↔ ∃ word, Utf8From bytes.val 0 word ∧ word ∈ WellFormedLanguage := by
  obtain ⟨e, he, hs⟩ := grammar_total_correct
  obtain ⟨result, hr, hc⟩ := matches_utf8_total_correct e bytes
  have matcher := matches_utf8_accepted_iff e bytes
  cases result <;> simp_all [langtag.well_formed]
private theorem nil_not_range (lower upper : Nat) : ([] : List Nat) ∉ Range lower upper := by
  simp [Range]
private theorem nil_not_mul {a b : Language Nat} (h : ([] : List Nat) ∉ a) : ([] : List Nat) ∉ a * b := by
  rw [Language.mem_mul]
  rintro ⟨x, hx, y, _, e⟩
  rw [List.append_eq_nil_iff] at e
  exact h (e.1 ▸ hx)
private theorem nil_not_pow {a : Language Nat} (h : ([] : List Nat) ∉ a) (n : Nat) :
    ([] : List Nat) ∉ a ^ (n + 1) := by
  rw [pow_succ']
  exact nil_not_mul h
private theorem nil_not_case_char (cp : Nat) : ([] : List Nat) ∉ CaseChar cp := by
  unfold CaseChar
  split <;> simp [Language.mem_add, Ch, nil_not_range]
private theorem nil_not_word (text : String) (nonempty : text.toList ≠ []) : ([] : List Nat) ∉ Word text := by
  unfold Word
  cases h : text.toList with
  | nil => exact absurd h nonempty
  | cons c rest => exact nil_not_mul (nil_not_case_char _)
/-- Every well-formed language tag has at least one character. -/
theorem well_formed_nonempty : ([] : List Nat) ∉ WellFormedLanguage := by
  have alpha : ([] : List Nat) ∉ Alpha := by simp [Alpha, Language.mem_add, nil_not_range]
  have subtag : ([] : List Nat) ∉ LanguageSubtag := by
    simp only [LanguageSubtag, Language.mem_add, Between, not_or]
    exact ⟨nil_not_mul (nil_not_mul (nil_not_pow alpha 1)), nil_not_pow alpha 3, nil_not_mul (nil_not_pow alpha 4)⟩
  have priv : ([] : List Nat) ∉ PrivateUse := nil_not_mul (by simp [Language.mem_add, Ch, nil_not_range])
  have grand : ([] : List Nat) ∉ Grandfathered := by
    simp only [Grandfathered, Language.mem_add, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact nil_not_word _ (by decide)
  simp only [WellFormedLanguage, Language.mem_add, not_or]
  exact ⟨nil_not_mul subtag, priv, grand⟩
/-- Two lower-case letters are a well-formed language tag. -/
theorem two_letters_well_formed (a b : Nat) (ha : 97 ≤ a ∧ a ≤ 122) (hb : 97 ≤ b ∧ b ≤ 122) :
    [a, b] ∈ WellFormedLanguage := by
  have alphaA : [a] ∈ Alpha := (Language.mem_add _ _ _).mpr (.inr ⟨a, rfl, ha.1, ha.2⟩)
  have alphaB : [b] ∈ Alpha := (Language.mem_add _ _ _).mpr (.inr ⟨b, rfl, hb.1, hb.2⟩)
  have one : ([] : List Nat) ∈ (1 : Language Nat) := (Language.mem_one _).mpr rfl
  have optional : ∀ l : Language Nat, ([] : List Nat) ∈ Optional l :=
    fun l => (Language.mem_add _ _ _).mpr (.inl one)
  have pair : [a, b] ∈ Alpha ^ 2 := by
    rw [pow_two]
    exact Language.mem_mul.mpr ⟨[a], alphaA, [b], alphaB, rfl⟩
  have atMost : ([] : List Nat) ∈ AtMost Alpha 1 := (Language.mem_add _ _ _).mpr (.inl one)
  have subtag : [a, b] ∈ LanguageSubtag :=
    (Language.mem_add _ _ _).mpr (.inl (Language.mem_mul.mpr ⟨[a, b],
      Language.mem_mul.mpr ⟨[a, b], pair, [], atMost, rfl⟩, [], optional _, rfl⟩))
  have rest : ([] : List Nat) ∈ Optional (Dashed (Alpha ^ 4)) *
      (Optional (Dashed (Alpha ^ 2 + Digit ^ 3)) * ((Dashed Variant)∗ * ((Dashed Extension)∗ *
        Optional (Dashed PrivateUse)))) :=
    Language.mem_mul.mpr ⟨[], optional _, [], Language.mem_mul.mpr ⟨[], optional _, [],
      Language.mem_mul.mpr ⟨[], Language.nil_mem_kstar _, [], Language.mem_mul.mpr ⟨[], Language.nil_mem_kstar _,
        [], optional _, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  have tagged : [a, b] ∈ Langtag := Language.mem_mul.mpr ⟨[a, b], subtag, [], rest, rfl⟩
  exact (Language.mem_add _ _ _).mpr (.inl tagged)
/-- `x` followed by `n + 1` subtags `a` is a well-formed language tag: one for
    private use. -/
theorem private_use_well_formed (n : Nat) :
    (120 :: (List.replicate (n + 1) [45, 97]).flatten) ∈ WellFormedLanguage := by
  have one : ([] : List Nat) ∈ (1 : Language Nat) := (Language.mem_one _).mpr rfl
  have letter : [97] ∈ Alnum :=
    (Language.mem_add _ _ _).mpr (.inl ((Language.mem_add _ _ _).mpr (.inr ⟨97, rfl, by omega, by omega⟩)))
  have between : [97] ∈ Between Alnum 1 7 :=
    Language.mem_mul.mpr ⟨[97], by rw [pow_one]; exact letter, [], (Language.mem_add _ _ _).mpr (.inl one), rfl⟩
  have dashed : [45, 97] ∈ Dashed (Between Alnum 1 7) :=
    Language.mem_mul.mpr ⟨[45], ⟨45, rfl, le_refl _, le_refl _⟩, [97], between, rfl⟩
  have positive : (List.replicate (n + 1) [45, 97]).flatten ∈ Positive (Dashed (Between Alnum 1 7)) := by
    rw [List.replicate_succ, List.flatten_cons]
    exact Language.mem_mul.mpr ⟨[45, 97], dashed, _, Language.join_mem_kstar (fun y hy => by
      rw [(List.mem_replicate.mp hy).2]; exact dashed), rfl⟩
  have priv : (120 :: (List.replicate (n + 1) [45, 97]).flatten) ∈ PrivateUse :=
    Language.mem_mul.mpr ⟨[120], (Language.mem_add _ _ _).mpr (.inl ⟨120, rfl, le_refl _, le_refl _⟩), _,
      positive, rfl⟩
  exact (Language.mem_add _ _ _).mpr (.inr ((Language.mem_add _ _ _).mpr (.inl priv)))
/-- RFC 4647 §2.1 basic language ranges: `*`, or one to eight ASCII letters
    followed by subtags of one to eight ASCII letters and digits, each after a
    `-`. -/
def BasicRangeLanguage : Language Nat := Ch 42 + Between Alpha 1 7 * (Dashed (Between Alnum 1 7))∗
theorem range_grammar_total_correct : ∃ e, langtag.range_grammar = .ok e ∧ Denotes e = BasicRangeLanguage := by
  apply WP.spec_imp_exists
  unfold langtag.range_grammar
  step*
  simp_all [BasicRangeLanguage]
/-- The lower case of an ASCII code point. -/
def lowerNat (c : Nat) : Nat := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c
/-- The letters of language tags: the ASCII letters and digits and `-`. -/
def TagLetter (c : Nat) : Prop := (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ (48 ≤ c ∧ c ≤ 57) ∨ c = 45
/-- A language of words of the letters of language tags that keeps each of
    its words in lower case. -/
def LowerClosed (l : Language Nat) : Prop := ∀ w ∈ l, (∀ c ∈ w, TagLetter c) ∧ w.map lowerNat ∈ l
private theorem closed_add {a b : Language Nat} (ha : LowerClosed a) (hb : LowerClosed b) :
    LowerClosed (a + b) := by
  intro w hw
  rcases (Language.mem_add _ _ _).mp hw with h | h
  · exact ⟨(ha w h).1, (Language.mem_add _ _ _).mpr (.inl (ha w h).2)⟩
  · exact ⟨(hb w h).1, (Language.mem_add _ _ _).mpr (.inr (hb w h).2)⟩
private theorem closed_mul {a b : Language Nat} (ha : LowerClosed a) (hb : LowerClosed b) :
    LowerClosed (a * b) := by
  intro w hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp hw
  refine ⟨fun c hc => ?_, Language.mem_mul.mpr ⟨_, (ha x hx).2, _, (hb y hy).2, by simp⟩⟩
  rcases List.mem_append.mp hc with h | h
  exacts [(ha x hx).1 c h, (hb y hy).1 c h]
private theorem closed_one : LowerClosed 1 := by
  intro w hw
  rw [Language.mem_one] at hw
  subst hw
  exact ⟨by simp, (Language.mem_one _).mpr rfl⟩
private theorem closed_kstar {a : Language Nat} (ha : LowerClosed a) : LowerClosed a∗ := by
  intro w hw
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hw
  refine ⟨fun c hc => ?_, Language.mem_kstar.mpr ⟨L.map (List.map lowerNat), by simp [List.map_flatten], ?_⟩⟩
  · obtain ⟨y, hy, hc⟩ := List.mem_flatten.mp hc
    exact (ha y (hL y hy)).1 c hc
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    exact (ha y' (hL y' hy')).2
private theorem closed_pow {a : Language Nat} (ha : LowerClosed a) (n : Nat) : LowerClosed (a ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact closed_one
  | succ n ih => rw [pow_succ]; exact closed_mul ih ha
private theorem closed_atMost {a : Language Nat} (ha : LowerClosed a) (n : Nat) : LowerClosed (AtMost a n) := by
  induction n with
  | zero => exact closed_one
  | succ n ih => exact closed_add closed_one (closed_mul ha ih)
private theorem closed_between {a : Language Nat} (ha : LowerClosed a) (lower extra : Nat) :
    LowerClosed (Between a lower extra) :=
  closed_mul (closed_pow ha lower) (closed_atMost ha extra)
private theorem closed_optional {a : Language Nat} (ha : LowerClosed a) : LowerClosed (Optional a) :=
  closed_add closed_one ha
private theorem closed_positive {a : Language Nat} (ha : LowerClosed a) : LowerClosed (Positive a) :=
  closed_mul ha (closed_kstar ha)
/-- A range of code points that are letters of tags in lower case already. -/
private theorem closed_range {lo hi : Nat} (letters : ∀ c, lo ≤ c → c ≤ hi → TagLetter c)
    (fixed : ∀ c, lo ≤ c → c ≤ hi → lowerNat c = c) : LowerClosed (Range lo hi) := by
  rintro w ⟨c, rfl, l, h⟩
  refine ⟨by simpa using letters c l h, ?_⟩
  simp only [List.map_cons, List.map_nil, fixed c l h]
  exact ⟨c, rfl, l, h⟩
/-- Two ranges of code points, the capital letters of the first in lower case
    in the second. -/
private theorem closed_cases {lo hi lo' hi' : Nat} (upper : 65 ≤ lo ∧ hi ≤ 90) (lower : lo' = lo + 32 ∧ hi' = hi + 32) :
    LowerClosed (Range lo hi + Range lo' hi') := by
  intro w hw
  rcases (Language.mem_add _ _ _).mp hw with ⟨c, rfl, l, h⟩ | ⟨c, rfl, l, h⟩
  · refine ⟨by simp [TagLetter]; omega, (Language.mem_add _ _ _).mpr (.inr ⟨c + 32, ?_, by omega, by omega⟩)⟩
    have : 65 ≤ c ∧ c ≤ 90 := by omega
    simp [lowerNat, this]
  · refine ⟨by simp [TagLetter]; omega, (Language.mem_add _ _ _).mpr (.inr ⟨c, ?_, l, h⟩)⟩
    have : ¬ (65 ≤ c ∧ c ≤ 90) := by omega
    simp [lowerNat, this]
private theorem closed_alpha : LowerClosed Alpha := closed_cases (by omega) (by omega)
private theorem closed_digit : LowerClosed Digit :=
  closed_range (fun c l h => by simp [TagLetter]; omega) (fun c l h => by simp [lowerNat]; omega)
private theorem closed_alnum : LowerClosed Alnum := closed_add closed_alpha closed_digit
private theorem closed_ch {cp : Nat} (letter : TagLetter cp) (fixed : lowerNat cp = cp) : LowerClosed (Ch cp) :=
  closed_range (fun c l h => by have : c = cp := by omega
                                subst this; exact letter)
    (fun c l h => by have : c = cp := by omega
                     subst this; exact fixed)
private theorem closed_dash : LowerClosed (Ch 45) := closed_ch (by simp [TagLetter]) (by simp [lowerNat])
private theorem closed_dashed {a : Language Nat} (ha : LowerClosed a) : LowerClosed (Dashed a) :=
  closed_mul closed_dash ha
private theorem closed_singleton : LowerClosed Singleton := by
  unfold Singleton
  refine closed_add closed_digit ?_
  intro w hw
  rcases (Language.mem_add _ _ _).mp hw with h | h
  · rcases (Language.mem_add _ _ _).mp h with ⟨c, rfl, l, hc⟩ | ⟨c, rfl, l, hc⟩
    · refine ⟨by simp [TagLetter]; omega, (Language.mem_add _ _ _).mpr (.inr ((Language.mem_add _ _ _).mpr
        (.inl ⟨c + 32, ?_, by omega, by omega⟩)))⟩
      have : 65 ≤ c ∧ c ≤ 90 := by omega
      simp [lowerNat, this]
    · refine ⟨by simp [TagLetter]; omega, (Language.mem_add _ _ _).mpr (.inr ((Language.mem_add _ _ _).mpr
        (.inr ⟨c + 32, ?_, by omega, by omega⟩)))⟩
      have : 65 ≤ c ∧ c ≤ 90 := by omega
      simp [lowerNat, this]
  · rcases (Language.mem_add _ _ _).mp h with ⟨c, rfl, l, hc⟩ | ⟨c, rfl, l, hc⟩
    · refine ⟨by simp [TagLetter]; omega, (Language.mem_add _ _ _).mpr (.inr ((Language.mem_add _ _ _).mpr
        (.inl ⟨c, ?_, l, hc⟩)))⟩
      have : ¬ (65 ≤ c ∧ c ≤ 90) := by omega
      simp [lowerNat, this]
    · refine ⟨by simp [TagLetter]; omega, (Language.mem_add _ _ _).mpr (.inr ((Language.mem_add _ _ _).mpr
        (.inr ⟨c, ?_, l, hc⟩)))⟩
      have : ¬ (65 ≤ c ∧ c ≤ 90) := by omega
      simp [lowerNat, this]
private theorem closed_x : LowerClosed (Ch 120 + Ch 88) := by
  intro w hw
  rcases (Language.mem_add _ _ _).mp hw with ⟨c, rfl, l, hc⟩ | ⟨c, rfl, l, hc⟩
  · have : c = 120 := by omega
    subst this
    exact ⟨by simp [TagLetter], (Language.mem_add _ _ _).mpr (.inl ⟨120, by simp [lowerNat], le_rfl, le_rfl⟩)⟩
  · have : c = 88 := by omega
    subst this
    exact ⟨by simp [TagLetter], (Language.mem_add _ _ _).mpr (.inl ⟨120, by simp [lowerNat], le_rfl, le_rfl⟩)⟩
private theorem closed_case_char {cp : Nat} (h : (97 ≤ cp ∧ cp ≤ 122) ∨ cp = 45) : LowerClosed (CaseChar cp) := by
  unfold CaseChar
  split_ifs with low
  · have := closed_cases (lo := cp - 32) (hi := cp - 32) (lo' := cp) (hi' := cp) (by omega) (by omega)
    intro w hw
    rcases (Language.mem_add _ _ _).mp hw with hw | hw
    · obtain ⟨both, lowered⟩ := this w ((Language.mem_add _ _ _).mpr (.inr hw))
      exact ⟨both, by rcases (Language.mem_add _ _ _).mp lowered with x | x
                      · exact (Language.mem_add _ _ _).mpr (.inr x)
                      · exact (Language.mem_add _ _ _).mpr (.inl x)⟩
    · obtain ⟨both, lowered⟩ := this w ((Language.mem_add _ _ _).mpr (.inl hw))
      exact ⟨both, by rcases (Language.mem_add _ _ _).mp lowered with x | x
                      · exact (Language.mem_add _ _ _).mpr (.inr x)
                      · exact (Language.mem_add _ _ _).mpr (.inl x)⟩
  · have : cp = 45 := by omega
    subst this
    exact closed_dash
private theorem closed_case_word : ∀ (cps : List Nat), (∀ c ∈ cps, (97 ≤ c ∧ c ≤ 122) ∨ c = 45) →
    LowerClosed (CaseWord cps)
  | [], _ => closed_one
  | cp :: tail, h => closed_mul (closed_case_char (h cp List.mem_cons_self))
      (closed_case_word tail (fun c m => h c (List.mem_cons_of_mem _ m)))
private theorem closed_word (text : String)
    (h : ∀ c ∈ text.toList.map Char.toNat, (97 ≤ c ∧ c ≤ 122) ∨ c = 45) : LowerClosed (Word text) :=
  closed_case_word _ h
private theorem closed_grandfathered : LowerClosed Grandfathered := by
  unfold Grandfathered
  repeat' first
    | apply closed_add
    | exact closed_word _ (by decide)
/-- Well-formed language tags are of the letters of tags and stay well-formed
    in lower case. -/
theorem well_formed_lower : LowerClosed WellFormedLanguage := by
  have extlang : LowerClosed Extlang := closed_mul (closed_pow closed_alpha 3)
    (closed_atMost (closed_dashed (closed_pow closed_alpha 3)) 2)
  have subtag : LowerClosed LanguageSubtag := closed_add
    (closed_mul (closed_between closed_alpha 2 1) (closed_optional (closed_dashed extlang)))
    (closed_add (closed_pow closed_alpha 4) (closed_between closed_alpha 5 3))
  have variant : LowerClosed Variant := closed_add (closed_between closed_alnum 5 3)
    (closed_mul closed_digit (closed_pow closed_alnum 3))
  have extension : LowerClosed Extension := closed_mul closed_singleton
    (closed_positive (closed_dashed (closed_between closed_alnum 2 6)))
  have privateUse : LowerClosed PrivateUse := closed_mul closed_x
    (closed_positive (closed_dashed (closed_between closed_alnum 1 7)))
  have langtag : LowerClosed Langtag := closed_mul subtag
    (closed_mul (closed_optional (closed_dashed (closed_pow closed_alpha 4)))
      (closed_mul (closed_optional (closed_dashed (closed_add (closed_pow closed_alpha 2) (closed_pow closed_digit 3))))
        (closed_mul (closed_kstar (closed_dashed variant))
          (closed_mul (closed_kstar (closed_dashed extension)) (closed_optional (closed_dashed privateUse))))))
  exact closed_add langtag (closed_add privateUse closed_grandfathered)
/-- The words of the basic language ranges: `*`, or words of the letters of
    language tags. -/
theorem range_letters : ∀ w ∈ BasicRangeLanguage, w = [42] ∨ ∀ c ∈ w, TagLetter c := by
  intro w hw
  rcases (Language.mem_add _ _ _).mp hw with star | ranged
  · left
    obtain ⟨cp, rfl, lo, hi⟩ := star
    have : cp = 42 := by omega
    rw [this]
  · right
    exact (closed_mul (closed_between closed_alpha 1 7)
      (closed_kstar (closed_dashed (closed_between closed_alnum 1 7))) w ranged).1

end Rowl.LangTag
