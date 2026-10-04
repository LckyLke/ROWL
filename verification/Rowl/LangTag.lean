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
end Rowl.LangTag
