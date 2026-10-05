import Rowl.Compiled

open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open scoped Computability

namespace Rowl.Iri
open regular
open Rowl.Regular
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable

/-- Single code-point ABNF interval. -/
def Range (lower upper : Nat) : Language Nat :=
  {word | ∃ cp, word = [cp] ∧ lower ≤ cp ∧ cp ≤ upper}
private def Ch (cp : Nat) : Language Nat := Range cp cp
private def Optional (a : Language Nat) : Language Nat := 1 + a
private def Positive (a : Language Nat) : Language Nat := a * a∗
/-- ABNF bounded repetition, independent of the Rust bounded counter. -/
def AtMost (a : Language Nat) : Nat → Language Nat
  | 0 => 1
  | n + 1 => 1 + a * AtMost a n

@[local step] private theorem range_spec (lower upper : U32) :
    iri.range lower upper ⦃ e => Denotes e = Range lower.val upper.val ⦄ := by
  simp [iri.range, Denotes, Range]
@[local step] private theorem chr_spec (cp : U32) :
    iri.chr cp ⦃ e => Denotes e = Ch cp.val ⦄ := by
  simp [iri.chr, iri.range, Denotes, Ch, Range]
@[local step] private theorem alt_spec (a b : Expression) :
    iri.alt a b ⦃ e => Denotes e = Denotes a + Denotes b ⦄ := by
  simp [iri.alt, Denotes]
@[local step] private theorem cat_spec (a b : Expression) :
    iri.cat a b ⦃ e => Denotes e = Denotes a * Denotes b ⦄ := by
  simp [iri.cat, Denotes]
@[local step] private theorem opt_spec (a : Expression) :
    iri.opt a ⦃ e => Denotes e = Optional (Denotes a) ⦄ := by
  simp [iri.opt, iri.alt, Denotes, Optional]
@[local step] private theorem star_spec (a : Expression) :
    iri.star a ⦃ e => Denotes e = (Denotes a)∗ ⦄ := by
  simp [iri.star, Denotes]
@[local step] private theorem plus_spec (a : Expression) :
    iri.plus a ⦃ e => Denotes e = Positive (Denotes a) ⦄ := by
  simp [iri.plus, copy_expression_total, iri.star, iri.cat, Denotes, Positive]

@[local step] private theorem exact_spec (a : Expression) (count : U8) :
    iri.exact a count ⦃ e => Denotes e = (Denotes a) ^ count.val ⦄ := by
  rw [iri.exact]
  split
  · rename_i zero
    simp [zero, Denotes]
  · rename_i nonzero
    rw [copy_expression_total]
    simp only [bind_ok]
    step as ⟨next, hn⟩
    obtain ⟨e, he, sem⟩ := WP.spec_imp_exists (exact_spec a next)
    simp only [he, bind_ok, iri.cat, WP.spec_ok, Denotes, sem]
    have countEq : count.val = next.val + 1 := by scalar_tac
    rw [countEq, pow_succ']
termination_by count.val
decreasing_by scalar_tac

@[local step] private theorem up_to_spec (a : Expression) (count : U8) :
    iri.up_to a count ⦃ e => Denotes e = AtMost (Denotes a) count.val ⦄ := by
  rw [iri.up_to]
  split
  · rename_i zero
    simp [zero, Denotes, AtMost]
  · rename_i nonzero
    rw [copy_expression_total]
    simp only [bind_ok]
    step as ⟨next, hn⟩
    obtain ⟨e, he, sem⟩ := WP.spec_imp_exists (up_to_spec a next)
    simp only [he, bind_ok, iri.cat, iri.opt, iri.alt, WP.spec_ok, Denotes, sem]
    have countEq : count.val = next.val + 1 := by scalar_tac
    rw [countEq, AtMost]
termination_by count.val
decreasing_by scalar_tac


private def Alpha : Language Nat :=
  Range 65 90 + Range 97 122

@[local step] private theorem alpha_spec :
    iri.alpha ⦃ e => Denotes e = Alpha ⦄ := by
  unfold iri.alpha
  step*
  simp_all [Alpha]

private def Digit : Language Nat :=
  Range 48 57

@[local step] private theorem digit_spec :
    iri.digit ⦃ e => Denotes e = Digit ⦄ := by
  unfold iri.digit
  step*
  simp_all [Digit]

private def Hex : Language Nat :=
  Digit + (Range 65 70 + Range 97 102)

@[local step] private theorem hex_spec :
    iri.hex ⦃ e => Denotes e = Hex ⦄ := by
  unfold iri.hex
  step*
  simp_all [Hex]

private def Unreserved : Language Nat :=
  Alpha + (Digit + (Ch 45 + (Ch 46 + (Ch 95 + Ch 126))))

@[local step] private theorem unreserved_spec :
    iri.unreserved ⦃ e => Denotes e = Unreserved ⦄ := by
  unfold iri.unreserved
  step*
  simp_all [Unreserved]

private def SubDelims : Language Nat :=
  Ch 33 + (Ch 36 + (Ch 38 + (Ch 39 + (Ch 40 + (Ch 41 + (Ch 42 + (Ch 43 + (Ch 44 + (Ch 59 + Ch 61)))))))))

@[local step] private theorem sub_delims_spec :
    iri.sub_delims ⦃ e => Denotes e = SubDelims ⦄ := by
  unfold iri.sub_delims
  step*
  simp_all [SubDelims]

private def PctEncoded : Language Nat :=
  Ch 37 * Hex ^ 2

@[local step] private theorem pct_encoded_spec :
    iri.pct_encoded ⦃ e => Denotes e = PctEncoded ⦄ := by
  unfold iri.pct_encoded
  step*
  simp_all [PctEncoded]

private def Ucschar : Language Nat :=
  Range 0xa0 0xd7ff + (Range 0xf900 0xfdcf + (Range 0xfdf0 0xffef +
  (Range 0x10000 0x1fffd + (Range 0x20000 0x2fffd + (Range 0x30000 0x3fffd +
  (Range 0x40000 0x4fffd + (Range 0x50000 0x5fffd + (Range 0x60000 0x6fffd +
  (Range 0x70000 0x7fffd + (Range 0x80000 0x8fffd + (Range 0x90000 0x9fffd +
  (Range 0xa0000 0xafffd + (Range 0xb0000 0xbfffd + (Range 0xc0000 0xcfffd +
  (Range 0xd0000 0xdfffd + Range 0xe1000 0xefffd)))))))))))))))

@[local step] private theorem ucschar_spec :
    iri.ucschar ⦃ e => Denotes e = Ucschar ⦄ := by
  unfold iri.ucschar
  step*
  simp_all [Ucschar]

private def Iprivate : Language Nat :=
  Range 0xe000 0xf8ff + (Range 0xf0000 0xffffd + Range 0x100000 0x10fffd)

@[local step] private theorem iprivate_spec :
    iri.iprivate ⦃ e => Denotes e = Iprivate ⦄ := by
  unfold iri.iprivate
  step*
  simp_all [Iprivate]

private def Iunreserved : Language Nat :=
  Unreserved + Ucschar

@[local step] private theorem iunreserved_spec :
    iri.iunreserved ⦃ e => Denotes e = Iunreserved ⦄ := by
  unfold iri.iunreserved
  step*
  simp_all [Iunreserved]

private def Ipchar : Language Nat :=
  Iunreserved + (PctEncoded + (SubDelims + (Ch 58 + Ch 64)))

@[local step] private theorem ipchar_spec :
    iri.ipchar ⦃ e => Denotes e = Ipchar ⦄ := by
  unfold iri.ipchar
  step*
  simp_all [Ipchar]

private def Segment : Language Nat :=
  Ipchar∗

@[local step] private theorem segment_spec :
    iri.segment ⦃ e => Denotes e = Segment ⦄ := by
  unfold iri.segment
  step*
  simp_all [Segment]

private def SegmentNz : Language Nat :=
  Positive Ipchar

@[local step] private theorem segment_nz_spec :
    iri.segment_nz ⦃ e => Denotes e = SegmentNz ⦄ := by
  unfold iri.segment_nz
  step*
  simp_all [SegmentNz]

private def SegmentNzNc : Language Nat :=
  Positive (Iunreserved + (PctEncoded + (SubDelims + Ch 64)))

@[local step] private theorem segment_nz_nc_spec :
    iri.segment_nz_nc ⦃ e => Denotes e = SegmentNzNc ⦄ := by
  unfold iri.segment_nz_nc
  step*
  simp_all [SegmentNzNc]

private def PathTail : Language Nat :=
  (Ch 47 * Segment)∗

@[local step] private theorem path_tail_spec :
    iri.path_tail ⦃ e => Denotes e = PathTail ⦄ := by
  unfold iri.path_tail
  step*
  simp_all [PathTail]

private def PathAbsolute : Language Nat :=
  Ch 47 * Optional (SegmentNz * PathTail)

@[local step] private theorem path_absolute_spec :
    iri.path_absolute ⦃ e => Denotes e = PathAbsolute ⦄ := by
  unfold iri.path_absolute
  step*
  simp_all [PathAbsolute]

private def PathRootless : Language Nat :=
  SegmentNz * PathTail

@[local step] private theorem path_rootless_spec :
    iri.path_rootless ⦃ e => Denotes e = PathRootless ⦄ := by
  unfold iri.path_rootless
  step*
  simp_all [PathRootless]

private def PathNoscheme : Language Nat :=
  SegmentNzNc * PathTail

@[local step] private theorem path_noscheme_spec :
    iri.path_noscheme ⦃ e => Denotes e = PathNoscheme ⦄ := by
  unfold iri.path_noscheme
  step*
  simp_all [PathNoscheme]

private def Query : Language Nat :=
  (Ipchar + (Iprivate + (Ch 47 + Ch 63)))∗

@[local step] private theorem query_spec :
    iri.query ⦃ e => Denotes e = Query ⦄ := by
  unfold iri.query
  step*
  simp_all [Query]

private def Fragment : Language Nat :=
  (Ipchar + (Ch 47 + Ch 63))∗

@[local step] private theorem fragment_spec :
    iri.fragment ⦃ e => Denotes e = Fragment ⦄ := by
  unfold iri.fragment
  step*
  simp_all [Fragment]

private def Scheme : Language Nat :=
  Alpha * (Alpha + (Digit + (Ch 43 + (Ch 45 + Ch 46))))∗

@[local step] private theorem scheme_spec :
    iri.scheme ⦃ e => Denotes e = Scheme ⦄ := by
  unfold iri.scheme
  step*
  simp_all [Scheme]

private def Userinfo : Language Nat :=
  (Iunreserved + (PctEncoded + (SubDelims + Ch 58)))∗

@[local step] private theorem userinfo_spec :
    iri.userinfo ⦃ e => Denotes e = Userinfo ⦄ := by
  unfold iri.userinfo
  step*
  simp_all [Userinfo]

private def RegName : Language Nat :=
  (Iunreserved + (PctEncoded + SubDelims))∗

@[local step] private theorem reg_name_spec :
    iri.reg_name ⦃ e => Denotes e = RegName ⦄ := by
  unfold iri.reg_name
  step*
  simp_all [RegName]

private def DecOctet : Language Nat :=
  Digit + (Range 49 57 * Digit + (Ch 49 * Digit ^ 2 +
  (Ch 50 * (Range 48 52 * Digit) + Ch 50 * (Ch 53 * Range 48 53))))

@[local step] private theorem dec_octet_spec :
    iri.dec_octet ⦃ e => Denotes e = DecOctet ⦄ := by
  unfold iri.dec_octet
  step*
  simp_all [DecOctet]

private def Ipv4 : Language Nat :=
  (DecOctet * Ch 46) ^ 3 * DecOctet

@[local step] private theorem ipv4_spec :
    iri.ipv4 ⦃ e => Denotes e = Ipv4 ⦄ := by
  unfold iri.ipv4
  step*
  simp_all [Ipv4]

private def H16 : Language Nat :=
  Hex * AtMost Hex 3

@[local step] private theorem h16_spec :
    iri.h16 ⦃ e => Denotes e = H16 ⦄ := by
  unfold iri.h16
  step*
  simp_all [H16]

private def Ls32 : Language Nat :=
  H16 * (Ch 58 * H16) + Ipv4

@[local step] private theorem ls32_spec :
    iri.ls32 ⦃ e => Denotes e = Ls32 ⦄ := by
  unfold iri.ls32
  step*
  simp_all [Ls32]

private def ColonPair : Language Nat :=
  Ch 58 * Ch 58

@[local step] private theorem colon_pair_spec :
    iri.colon_pair ⦃ e => Denotes e = ColonPair ⦄ := by
  unfold iri.colon_pair
  step*
  simp_all [ColonPair]

private def H16Colon : Language Nat :=
  H16 * Ch 58

@[local step] private theorem h16_colon_spec :
    iri.h16_colon ⦃ e => Denotes e = H16Colon ⦄ := by
  unfold iri.h16_colon
  step*
  simp_all [H16Colon]

private def CompressedPrefix (n : Nat) : Language Nat :=
  Optional (AtMost H16Colon n * H16)

@[local step] private theorem compressed_prefix_spec (n : U8) :
    iri.compressed_prefix n ⦃ e => Denotes e = CompressedPrefix n.val ⦄ := by
  unfold iri.compressed_prefix
  step*
  simp_all [CompressedPrefix]

private def Ipv6 : Language Nat :=
  H16Colon ^ 6 * Ls32 +
  (ColonPair * (H16Colon ^ 5 * Ls32) +
  (Optional H16 * (ColonPair * (H16Colon ^ 4 * Ls32)) +
  (CompressedPrefix 1 * (ColonPair * (H16Colon ^ 3 * Ls32)) +
  (CompressedPrefix 2 * (ColonPair * (H16Colon ^ 2 * Ls32)) +
  (CompressedPrefix 3 * (ColonPair * (H16Colon * Ls32)) +
  (CompressedPrefix 4 * (ColonPair * Ls32) +
  (CompressedPrefix 5 * (ColonPair * H16) +
  CompressedPrefix 6 * ColonPair)))))))

@[local step] private theorem ipv6_spec :
    iri.ipv6 ⦃ e => Denotes e = Ipv6 ⦄ := by
  unfold iri.ipv6
  step*
  simp_all [Ipv6]

private def IpvFuture : Language Nat :=
  (Ch 118 + Ch 86) * (Positive Hex * (Ch 46 * Positive (Unreserved + (SubDelims + Ch 58))))

@[local step] private theorem ipv_future_spec :
    iri.ipv_future ⦃ e => Denotes e = IpvFuture ⦄ := by
  unfold iri.ipv_future
  step*
  simp_all [IpvFuture]

private def IpLiteral : Language Nat :=
  Ch 91 * ((Ipv6 + IpvFuture) * Ch 93)

@[local step] private theorem ip_literal_spec :
    iri.ip_literal ⦃ e => Denotes e = IpLiteral ⦄ := by
  unfold iri.ip_literal
  step*
  simp_all [IpLiteral]

private def Host : Language Nat :=
  IpLiteral + (Ipv4 + RegName)

@[local step] private theorem host_spec :
    iri.host ⦃ e => Denotes e = Host ⦄ := by
  unfold iri.host
  step*
  simp_all [Host]

private def Authority : Language Nat :=
  Optional (Userinfo * Ch 64) * (Host * Optional (Ch 58 * Digit∗))

@[local step] private theorem authority_spec :
    iri.authority ⦃ e => Denotes e = Authority ⦄ := by
  unfold iri.authority
  step*
  simp_all [Authority]

private def DoubleSlash : Language Nat :=
  Ch 47 * Ch 47

@[local step] private theorem double_slash_spec :
    iri.double_slash ⦃ e => Denotes e = DoubleSlash ⦄ := by
  unfold iri.double_slash
  step*
  simp_all [DoubleSlash]

private def AuthorityPath : Language Nat :=
  DoubleSlash * (Authority * PathTail)

@[local step] private theorem authority_path_spec :
    iri.authority_path ⦃ e => Denotes e = AuthorityPath ⦄ := by
  unfold iri.authority_path
  step*
  simp_all [AuthorityPath]

private def HierPart : Language Nat :=
  AuthorityPath + (PathAbsolute + (PathRootless + 1))

@[local step] private theorem hier_part_spec :
    iri.hier_part ⦃ e => Denotes e = HierPart ⦄ := by
  unfold iri.hier_part
  step*
  simp_all [HierPart, Denotes]

private def RelativePart : Language Nat :=
  AuthorityPath + (PathAbsolute + (PathNoscheme + 1))

@[local step] private theorem relative_part_spec :
    iri.relative_part ⦃ e => Denotes e = RelativePart ⦄ := by
  unfold iri.relative_part
  step*
  simp_all [RelativePart, Denotes]

private def Suffix : Language Nat :=
  Optional (Ch 63 * Query) * Optional (Ch 35 * Fragment)

@[local step] private theorem suffix_spec :
    iri.suffix ⦃ e => Denotes e = Suffix ⦄ := by
  unfold iri.suffix
  step*
  simp_all [Suffix]

def IriLanguage : Language Nat :=
  Scheme * (Ch 58 * (HierPart * Suffix))

@[local step] private theorem iri_spec :
    iri.iri ⦃ e => Denotes e = IriLanguage ⦄ := by
  unfold iri.iri
  step*
  simp_all [IriLanguage]

private def RelativeRef : Language Nat :=
  RelativePart * Suffix

@[local step] private theorem relative_ref_spec :
    iri.relative_ref ⦃ e => Denotes e = RelativeRef ⦄ := by
  unfold iri.relative_ref
  step*
  simp_all [RelativeRef]

def ReferenceLanguage : Language Nat :=
  IriLanguage + RelativeRef

@[local step] private theorem iri_reference_spec :
    iri.iri_reference ⦃ e => Denotes e = ReferenceLanguage ⦄ := by
  unfold iri.iri_reference
  step*
  simp_all [ReferenceLanguage]

/-- Bounded ABNF repetition permits exactly zero through n repetitions. -/
theorem at_most_iff (a : Language Nat) (n : Nat) (word : List Nat) :
    word ∈ AtMost a n ↔ ∃ k, k ≤ n ∧ word ∈ a ^ k := by
  induction n generalizing word with
  | zero => simp [AtMost]
  | succ n ih =>
    rw [AtMost, Language.mem_add, Language.mem_mul]
    constructor
    · rintro (empty | ⟨left, hl, right, hr, eq⟩)
      · exact ⟨0, by omega, by simpa using empty⟩
      · obtain ⟨k, bound, accepted⟩ := (ih right).mp hr
        refine ⟨k + 1, by omega, ?_⟩
        rw [pow_succ', Language.mem_mul]
        exact ⟨left, hl, right, accepted, eq⟩
    · rintro ⟨k, bound, accepted⟩
      cases k with
      | zero => exact Or.inl (by simpa using accepted)
      | succ k =>
        rw [pow_succ', Language.mem_mul] at accepted
        obtain ⟨left, hl, right, hr, eq⟩ := accepted
        exact Or.inr ⟨left, hl, right, (ih right).mpr ⟨k, by omega, hr⟩, eq⟩

/-- Actual compiled grammar denotes precisely the RFC 3987 IRI production. -/
theorem iri_grammar_total_correct :
    ∃ expression, iri.iri = .ok expression ∧ Denotes expression = IriLanguage :=
  WP.spec_imp_exists iri_spec

/-- Actual compiled grammar denotes precisely the IRI-reference production. -/
theorem reference_grammar_total_correct :
    ∃ expression, iri.iri_reference = .ok expression ∧ Denotes expression = ReferenceLanguage :=
  WP.spec_imp_exists iri_reference_spec

/-- Whole-buffer grammar result, distinct from malformed UTF-8 evidence. -/
def ValidationCorrect (grammar : Language Nat) (bytes : List U8) : MatchResult → Prop
  | .Matched accepted => ∃ word, Utf8From bytes 0 word ∧ accepted = decide (word ∈ grammar)
  | .MalformedUtf8 error => Utf8Failure bytes 0 error

private theorem converted (grammar : Language Nat) (expression : Expression)
    (bytes : List U8) (result : MatchResult) (same : Denotes expression = grammar) :
    MatchCorrect expression bytes 0 result ↔ ValidationCorrect grammar bytes result := by
  cases result <;> simp [MatchCorrect, ValidationCorrect, same]

/-- Matching with the compiled table returns the derivative matcher's result. -/
private theorem validate_eq (grammar : Expression) (bytes : alloc.vec.Vec U8) :
    iri.validate grammar bytes = matches_utf8 grammar bytes := by
  obtain ⟨t, root, t', made, compiledRun, flagged, rooted⟩ := Rowl.Compiled.compile_fresh grammar
  obtain ⟨r, run, spec⟩ := Rowl.Compiled.matches_eq t' root bytes grammar flagged rooted
  cases r with
  | none => simp [iri.validate, made, compiledRun, run]
  | some m => simp [iri.validate, made, compiledRun, run, spec m rfl]

/-! ### Plain IRIs

`validate_iri` accepts IRIs of the plain form `scheme://host/segment…#fragment`,
whose host, segments and fragment have only ASCII letters, digits, `-`, `.`, `_`
and `~` (and the fragment also `/`), without building the grammar. Such bytes are
ASCII, hence well-encoded, and spell an IRI. -/

private def LetterCode (n : Nat) : Prop := (65 ≤ n ∧ n ≤ 90) ∨ (97 ≤ n ∧ n ≤ 122)
private def DigitCode (n : Nat) : Prop := 48 ≤ n ∧ n ≤ 57
private def PlainCode (n : Nat) : Prop :=
  LetterCode n ∨ DigitCode n ∨ n = 45 ∨ n = 46 ∨ n = 95 ∨ n = 126
private def SchemeCode (n : Nat) : Prop :=
  LetterCode n ∨ DigitCode n ∨ n = 43 ∨ n = 45 ∨ n = 46
private def FragmentCode (n : Nat) : Prop := PlainCode n ∨ n = 47

private theorem ascii_letter_spec (b : U8) : iri.ascii_letter b = .ok (decide (LetterCode b.val)) := by
  unfold iri.ascii_letter LetterCode
  by_cases h1 : 65 ≤ b.val <;> by_cases h2 : b.val ≤ 90 <;> by_cases h3 : 97 ≤ b.val <;>
    by_cases h4 : b.val ≤ 122 <;> simp [UScalar.le_equiv, h1, h2, h3, h4]

private theorem ascii_digit_spec (b : U8) : iri.ascii_digit b = .ok (decide (DigitCode b.val)) := by
  unfold iri.ascii_digit DigitCode
  by_cases h1 : 48 ≤ b.val <;> by_cases h2 : b.val ≤ 57 <;> simp [UScalar.le_equiv, h1, h2]

private theorem plain_spec (b : U8) : iri.plain b = .ok (decide (PlainCode b.val)) := by
  unfold iri.plain PlainCode
  rw [ascii_letter_spec, ascii_digit_spec]
  by_cases l : LetterCode b.val
  · simp [l]
  · by_cases d : DigitCode b.val
    · simp [l, d]
    · by_cases e1 : b.val = 45 <;> by_cases e2 : b.val = 46 <;> by_cases e3 : b.val = 95 <;>
        simp [l, d, UScalar.eq_equiv, e1, e2, e3]

private theorem scheme_char_spec (b : U8) : iri.scheme_char b = .ok (decide (SchemeCode b.val)) := by
  unfold iri.scheme_char SchemeCode
  rw [ascii_letter_spec, ascii_digit_spec]
  by_cases l : LetterCode b.val
  · simp [l]
  · by_cases d : DigitCode b.val
    · simp [l, d]
    · by_cases e1 : b.val = 43 <;> by_cases e2 : b.val = 45 <;> simp [l, d, UScalar.eq_equiv, e1, e2]

private theorem plain_ascii {n : Nat} (h : PlainCode n) : n < 128 := by
  unfold PlainCode LetterCode DigitCode at h; omega
private theorem scheme_ascii {n : Nat} (h : SchemeCode n) : n < 128 := by
  unfold SchemeCode LetterCode DigitCode at h; omega
private theorem fragment_ascii {n : Nat} (h : FragmentCode n) : n < 128 := by
  rcases h with h | h
  · exact plain_ascii h
  · omega

private theorem range_mem {n lower upper : Nat} (low : lower ≤ n) (high : n ≤ upper) :
    [n] ∈ Range lower upper :=
  ⟨n, rfl, low, high⟩
private theorem ch_mem (n : Nat) : [n] ∈ Ch n := range_mem (le_refl n) (le_refl n)

private theorem letter_mem {n : Nat} (h : LetterCode n) : [n] ∈ Alpha := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩
  · exact (Language.mem_add _ _ _).mpr (Or.inl (range_mem a b))
  · exact (Language.mem_add _ _ _).mpr (Or.inr (range_mem a b))

private theorem plain_mem {n : Nat} (h : PlainCode n) : [n] ∈ Unreserved := by
  unfold Unreserved
  simp only [Language.mem_add]
  rcases h with l | d | rfl | rfl | rfl | rfl
  · exact Or.inl (letter_mem l)
  · exact Or.inr (Or.inl (range_mem d.1 d.2))
  · exact Or.inr (Or.inr (Or.inl (ch_mem _)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (ch_mem _))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ch_mem _)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ch_mem _)))))

private theorem plain_iunreserved {n : Nat} (h : PlainCode n) : [n] ∈ Iunreserved :=
  (Language.mem_add _ _ _).mpr (Or.inl (plain_mem h))

private theorem plain_ipchar {n : Nat} (h : PlainCode n) : [n] ∈ Ipchar := by
  unfold Ipchar
  exact (Language.mem_add _ _ _).mpr (Or.inl (plain_iunreserved h))

private theorem scheme_char_mem {n : Nat} (h : SchemeCode n) :
    [n] ∈ Alpha + (Digit + (Ch 43 + (Ch 45 + Ch 46))) := by
  simp only [Language.mem_add]
  rcases h with l | d | rfl | rfl | rfl
  · exact Or.inl (letter_mem l)
  · exact Or.inr (Or.inl (range_mem d.1 d.2))
  · exact Or.inr (Or.inr (Or.inl (ch_mem _)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (ch_mem _))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (ch_mem _))))

private theorem flatten_singletons (w : List Nat) : (w.map fun c => [c]).flatten = w := by
  induction w with
  | nil => rfl
  | cons c rest ih => simp [ih]

private theorem star_of_chars {C : Language Nat} {w : List Nat} (each : ∀ c ∈ w, [c] ∈ C) : w ∈ C∗ := by
  rw [← flatten_singletons w]
  exact Language.join_mem_kstar (by simpa using each)

private theorem star_append {C : Language Nat} {s w : List Nat} (hs : s ∈ C) (hw : w ∈ C∗) : s ++ w ∈ C∗ := by
  obtain ⟨L, rfl, all⟩ := Language.mem_kstar.mp hw
  have joined : s ++ L.flatten = (s :: L).flatten := by simp
  rw [joined]
  exact Language.join_mem_kstar (by
    intro y member
    rcases List.mem_cons.mp member with rfl | member
    · exact hs
    · exact all y member)

private theorem optional_nil (a : Language Nat) : [] ∈ Optional a :=
  (Language.mem_add _ _ _).mpr (Or.inl Language.nil_mem_one)
private theorem optional_of {a : Language Nat} {w : List Nat} (h : w ∈ a) : w ∈ Optional a :=
  (Language.mem_add _ _ _).mpr (Or.inr h)

private theorem scheme_end_spec (bytes : alloc.vec.Vec U8) (index : Usize) (inside : index.val ≤ bytes.val.length) :
    ∃ e, iri.scheme_end bytes index = .ok e ∧ index.val ≤ e.val ∧ e.val ≤ bytes.val.length ∧
      ∃ pre, bytes.val.drop index.val = pre ++ bytes.val.drop e.val ∧ ∀ b ∈ pre, SchemeCode b.val := by
  rw [iri.scheme_end]
  by_cases more : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    by_cases code : SchemeCode bytes.val[index.val].val
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨e, run, low, high, pre, split, all⟩ := scheme_end_spec bytes next (by omega)
      refine ⟨e, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, scheme_char_spec, code, advance,
        run], by omega, high, bytes.val[index.val] :: pre, ?_, ?_⟩
      · rw [List.drop_eq_getElem_cons more, ← nextIs, split]; rfl
      · intro b member
        rcases List.mem_cons.mp member with rfl | member
        · exact code
        · exact all b member
    · exact ⟨index, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, scheme_char_spec, code],
        le_refl _, inside, [], by simp, by simp⟩
  · exact ⟨index, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], le_refl _, inside, [], by simp, by simp⟩
termination_by bytes.val.length - index.val
decreasing_by omega

private theorem plain_end_spec (bytes : alloc.vec.Vec U8) (index : Usize) (inside : index.val ≤ bytes.val.length) :
    ∃ e, iri.plain_end bytes index = .ok e ∧ index.val ≤ e.val ∧ e.val ≤ bytes.val.length ∧
      ∃ pre, bytes.val.drop index.val = pre ++ bytes.val.drop e.val ∧ ∀ b ∈ pre, PlainCode b.val := by
  rw [iri.plain_end]
  by_cases more : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    by_cases code : PlainCode bytes.val[index.val].val
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨e, run, low, high, pre, split, all⟩ := plain_end_spec bytes next (by omega)
      refine ⟨e, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, plain_spec, code, advance, run],
        by omega, high, bytes.val[index.val] :: pre, ?_, ?_⟩
      · rw [List.drop_eq_getElem_cons more, ← nextIs, split]; rfl
      · intro b member
        rcases List.mem_cons.mp member with rfl | member
        · exact code
        · exact all b member
    · exact ⟨index, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, plain_spec, code],
        le_refl _, inside, [], by simp, by simp⟩
  · exact ⟨index, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], le_refl _, inside, [], by simp, by simp⟩
termination_by bytes.val.length - index.val
decreasing_by omega

private theorem fragment_end_spec (bytes : alloc.vec.Vec U8) (index : Usize)
    (inside : index.val ≤ bytes.val.length) :
    ∃ e, iri.fragment_end bytes index = .ok e ∧ index.val ≤ e.val ∧ e.val ≤ bytes.val.length ∧
      ∃ pre, bytes.val.drop index.val = pre ++ bytes.val.drop e.val ∧ ∀ b ∈ pre, FragmentCode b.val := by
  rw [iri.fragment_end]
  by_cases more : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    by_cases code : FragmentCode bytes.val[index.val].val
    · obtain ⟨e, run, low, high, pre, split, all⟩ := fragment_end_spec bytes next (by omega)
      have step : iri.fragment_end bytes next = .ok e := run
      refine ⟨e, ?_, by omega, high, bytes.val[index.val] :: pre, ?_, ?_⟩
      · rcases code with plainCode | slash
        · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, plain_spec, plainCode, advance, step]
        · have isSlash : bytes.val[index.val] = 47#u8 := UScalar.eq_of_val_eq (by simp [slash])
          have notPlain : ¬ PlainCode bytes.val[index.val].val := by
            unfold PlainCode LetterCode DigitCode; omega
          simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, plain_spec, notPlain, isSlash, advance, step]
      · rw [List.drop_eq_getElem_cons more, ← nextIs, split]; rfl
      · intro b member
        rcases List.mem_cons.mp member with rfl | member
        · exact code
        · exact all b member
    · have notPlain : ¬ PlainCode bytes.val[index.val].val := fun h => code (Or.inl h)
      have notSlash : ¬ bytes.val[index.val] = 47#u8 := fun h => code (Or.inr (by simp [h]))
      exact ⟨index, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, plain_spec, notPlain, notSlash],
        le_refl _, inside, [], by simp, by simp⟩
  · exact ⟨index, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], le_refl _, inside, [], by simp, by simp⟩
termination_by bytes.val.length - index.val
decreasing_by omega

private theorem plain_path_spec (bytes : alloc.vec.Vec U8) (index : Usize) (inside : index.val ≤ bytes.val.length) :
    ∃ r, iri.plain_path bytes index = .ok r ∧ (r = true →
      (∀ b ∈ bytes.val.drop index.val, b.val < 128) ∧
      (bytes.val.drop index.val).map (·.val) ∈ PathTail * Optional (Ch 35 * Fragment)) := by
  rw [iri.plain_path]
  by_cases more : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have dropIs : bytes.val.drop index.val = bytes.val[index.val] :: bytes.val.drop next.val := by
      rw [nextIs]; exact List.drop_eq_getElem_cons more
    by_cases slash : bytes.val[index.val] = 47#u8
    · have byteIs : bytes.val[index.val].val = 47 := by rw [slash]; rfl
      obtain ⟨e, run, low, high, pre, split, all⟩ := plain_end_spec bytes next (by omega)
      obtain ⟨r, rest, spec⟩ := plain_path_spec bytes e high
      refine ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, slash, advance, run, rest],
        fun yes => ?_⟩
      obtain ⟨ascii, member⟩ := spec yes
      rw [dropIs, split]
      refine ⟨fun b member' => ?_, ?_⟩
      · simp only [List.mem_cons, List.mem_append] at member'
        rcases member' with rfl | inPre | inRest
        · omega
        · exact plain_ascii (all b inPre)
        · exact ascii b inRest
      · obtain ⟨p, hp, f, hf, eq⟩ := Language.mem_mul.mp member
        have segment : (47 :: pre.map (·.val)) ∈ Ch 47 * Segment := by
          have : (47 :: pre.map (·.val)) = [47] ++ pre.map (·.val) := rfl
          rw [this]
          refine Language.append_mem_mul (ch_mem 47) (star_of_chars fun c member => ?_)
          obtain ⟨b, inPre, rfl⟩ := List.mem_map.mp member
          exact plain_ipchar (all b inPre)
        refine Language.mem_mul.mpr ⟨(47 :: pre.map (·.val)) ++ p, star_append segment hp, f, hf, ?_⟩
        rw [List.map_cons, List.map_append, ← eq, byteIs]
        simp
    · by_cases hash : bytes.val[index.val] = 35#u8
      · have byteIs : bytes.val[index.val].val = 35 := by rw [hash]; rfl
        obtain ⟨e, run, low, high, pre, split, all⟩ := fragment_end_spec bytes next (by omega)
        refine ⟨decide (e = alloc.vec.Vec.len bytes), by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup,
          slash, hash, advance, run], fun yes => ?_⟩
        have atEnd : e.val = bytes.val.length := by
          have := congrArg UScalar.val (of_decide_eq_true yes)
          simpa using this
        have rest : bytes.val.drop e.val = [] := List.drop_eq_nil_of_le (by omega)
        rw [dropIs, split, rest, List.append_nil]
        refine ⟨fun b member' => ?_, ?_⟩
        · rcases List.mem_cons.mp member' with rfl | inPre
          · omega
          · exact fragment_ascii (all b inPre)
        · refine Language.mem_mul.mpr ⟨[], Language.nil_mem_kstar _, 35 :: pre.map (·.val), optional_of ?_, ?_⟩
          · have : (35 :: pre.map (·.val)) = [35] ++ pre.map (·.val) := rfl
            rw [this]
            refine Language.append_mem_mul (ch_mem 35) (star_of_chars fun c member => ?_)
            obtain ⟨b, inPre, rfl⟩ := List.mem_map.mp member
            rcases all b inPre with plainCode | isSlash
            · exact (Language.mem_add _ _ _).mpr (Or.inl (plain_ipchar plainCode))
            · rw [isSlash]
              exact (Language.mem_add _ _ _).mpr (Or.inr ((Language.mem_add _ _ _).mpr (Or.inl (ch_mem 47))))
          · rw [List.map_cons, byteIs]; rfl
      · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, slash, hash], by simp⟩
  · refine ⟨true, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], fun _ => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    exact ⟨by simp, Language.mem_mul.mpr ⟨[], Language.nil_mem_kstar _, [], optional_nil _, rfl⟩⟩
termination_by bytes.val.length - index.val
decreasing_by omega

private theorem drop_cons_of {l : List U8} {i : Nat} {v : U8} (h : l[i]? = some v) :
    l.drop i = v :: l.drop (i + 1) := by
  obtain ⟨inside, value⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons inside, value]

/-- Plain bytes are ASCII and spell an IRI. -/
private theorem plain_iri_spec (bytes : alloc.vec.Vec U8) :
    ∃ r, iri.plain_iri bytes = .ok r ∧ (r = true →
      (∀ b ∈ bytes.val, b.val < 128) ∧ bytes.val.map (·.val) ∈ IriLanguage) := by
  rw [iri.plain_iri]
  by_cases nonempty : 0 < bytes.val.length
  · have lookup0 : bytes.index_usize 0#usize = .ok bytes.val[0] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem nonempty]
    by_cases letter : LetterCode bytes.val[0].val
    · obtain ⟨colon, run1, low1, high1, pre1, split1, all1⟩ := scheme_end_spec bytes 1#usize (by simp; omega)
      by_cases inside : colon.val < bytes.val.length
      · obtain ⟨room, minus, roomValue⟩ := WP.spec_imp_exists
          (Usize.sub_spec (x := alloc.vec.Vec.len bytes) (y := colon) (by scalar_tac))
        have roomIs : room.val = bytes.val.length - colon.val := by
          have := roomValue; simp at this; omega
        by_cases enough : 2 < room.val
        · have c0 : bytes.index_usize colon = .ok bytes.val[colon.val] := by
            simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
          obtain ⟨c1, advance1, c1Value⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := colon) (y := 1#usize) (by scalar_tac))
          have c1Is : c1.val = colon.val + 1 := by simpa using c1Value
          have inside1 : c1.val < bytes.val.length := by omega
          have l1 : bytes.index_usize c1 = .ok bytes.val[c1.val] := by
            simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside1]
          obtain ⟨c2, advance2, c2Value⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := colon) (y := 2#usize) (by scalar_tac))
          have c2Is : c2.val = colon.val + 2 := by simpa using c2Value
          have inside2 : c2.val < bytes.val.length := by omega
          have l2 : bytes.index_usize c2 = .ok bytes.val[c2.val] := by
            simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside2]
          obtain ⟨c3, advance3, c3Value⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := colon) (y := 3#usize) (by scalar_tac))
          have c3Is : c3.val = colon.val + 3 := by simpa using c3Value
          by_cases b0 : bytes.val[colon.val] = 58#u8
          · by_cases b1 : bytes.val[c1.val] = 47#u8
            · by_cases b2 : bytes.val[c2.val] = 47#u8
              · obtain ⟨h, run2, low2, high2, pre2, split2, all2⟩ := plain_end_spec bytes c3 (by omega)
                obtain ⟨r, run3, spec3⟩ := plain_path_spec bytes h high2
                refine ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nonempty, lookup0, ascii_letter_spec, letter,
                  run1, inside, minus, enough, c0, b0, advance1, l1, b1, advance2, l2, b2, advance3, run2, run3],
                  fun yes => ?_⟩
                obtain ⟨ascii3, member3⟩ := spec3 yes
                have g0 : bytes.val[colon.val]? = some 58#u8 := by rw [List.getElem?_eq_getElem inside, b0]
                have g1 : bytes.val[colon.val + 1]? = some 47#u8 := by
                  rw [← c1Is, List.getElem?_eq_getElem inside1, b1]
                have g2 : bytes.val[colon.val + 1 + 1]? = some 47#u8 := by
                  rw [show colon.val + 1 + 1 = c2.val by omega, List.getElem?_eq_getElem inside2, b2]
                have fromColon : bytes.val.drop colon.val = 58#u8 :: 47#u8 :: 47#u8 :: bytes.val.drop c3.val := by
                  rw [drop_cons_of g0, drop_cons_of g1, drop_cons_of g2, show colon.val + 1 + 1 + 1 = c3.val by omega]
                obtain ⟨first, at0⟩ : ∃ v, bytes.val[0]? = some v := ⟨_, List.getElem?_eq_getElem nonempty⟩
                have firstIs : bytes.val[0] = first := by
                  have := List.getElem?_eq_getElem nonempty
                  rw [at0] at this
                  exact (Option.some.inj this).symm
                rw [firstIs] at letter
                have one : (1#usize).val = 1 := rfl
                rw [one] at split1
                have whole : bytes.val = first :: (pre1 ++ (58#u8 :: 47#u8 :: 47#u8 :: (pre2 ++ bytes.val.drop h.val))) := by
                  rw [← split2, ← fromColon, ← split1, ← drop_cons_of at0, List.drop_zero]
                obtain ⟨p, hp, f, hf, eq⟩ := Language.mem_mul.mp member3
                refine ⟨fun b member => ?_, ?_⟩
                · rw [whole] at member
                  simp only [List.mem_cons, List.mem_append] at member
                  rcases member with rfl | inPre1 | rfl | rfl | rfl | inPre2 | inRest
                  · unfold LetterCode at letter; omega
                  · exact scheme_ascii (all1 b inPre1)
                  · decide
                  · decide
                  · decide
                  · exact plain_ascii (all2 b inPre2)
                  · exact ascii3 b inRest
                · have scheme : (first.val :: pre1.map (·.val)) ∈ Scheme := by
                    have : (first.val :: pre1.map (·.val)) = [first.val] ++ pre1.map (·.val) := rfl
                    rw [this]
                    refine Language.append_mem_mul (letter_mem letter) (star_of_chars fun c member => ?_)
                    obtain ⟨b, inPre, rfl⟩ := List.mem_map.mp member
                    exact scheme_char_mem (all1 b inPre)
                  have host : pre2.map (·.val) ∈ Host := by
                    unfold Host
                    refine (Language.mem_add _ _ _).mpr (Or.inr ((Language.mem_add _ _ _).mpr (Or.inr ?_)))
                    unfold RegName
                    refine star_of_chars fun c member => ?_
                    obtain ⟨b, inPre, rfl⟩ := List.mem_map.mp member
                    exact (Language.mem_add _ _ _).mpr (Or.inl (plain_iunreserved (all2 b inPre)))
                  have authority : pre2.map (·.val) ∈ Authority := by
                    unfold Authority
                    have : pre2.map (·.val) = [] ++ (pre2.map (·.val) ++ []) := by simp
                    rw [this]
                    exact Language.append_mem_mul (optional_nil _) (Language.append_mem_mul host (optional_nil _))
                  have hier : [47, 47] ++ (pre2.map (·.val) ++ p) ∈ HierPart := by
                    unfold HierPart
                    refine (Language.mem_add _ _ _).mpr (Or.inl ?_)
                    unfold AuthorityPath DoubleSlash
                    exact Language.append_mem_mul (Language.append_mem_mul (ch_mem 47) (ch_mem 47))
                      (Language.append_mem_mul authority hp)
                  have suffix : f ∈ Suffix := by
                    unfold Suffix
                    have : f = [] ++ f := rfl
                    rw [this]
                    exact Language.append_mem_mul (optional_nil _) hf
                  have iriMember := Language.append_mem_mul scheme
                    (Language.append_mem_mul (ch_mem 58) (Language.append_mem_mul hier suffix))
                  unfold IriLanguage
                  convert iriMember using 1
                  rw [whole]
                  simp only [List.map_cons, List.map_append, ← eq]
                  simp
              · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nonempty, lookup0, ascii_letter_spec,
                  letter, run1, inside, minus, enough, c0, b0, advance1, l1, b1, advance2, l2, b2], by simp⟩
            · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nonempty, lookup0, ascii_letter_spec, letter,
                run1, inside, minus, enough, c0, b0, advance1, l1, b1], by simp⟩
          · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nonempty, lookup0, ascii_letter_spec, letter,
              run1, inside, minus, enough, c0, b0], by simp⟩
        · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nonempty, lookup0, ascii_letter_spec, letter,
            run1, inside, minus, enough], by simp⟩
      · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nonempty, lookup0, ascii_letter_spec, letter,
          run1, inside], by simp⟩
    · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nonempty, lookup0, ascii_letter_spec, letter],
        by simp⟩
  · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nonempty], by simp⟩

/-- ASCII bytes decode one code point each. -/
private theorem ascii_utf8 (bs : List U8) (ascii : ∀ b ∈ bs, b.val < 128) :
    ∀ (i : Nat), i ≤ bs.length → Utf8From bs i ((bs.drop i).map (·.val)) := by
  intro i
  induction h : bs.length - i generalizing i with
  | zero =>
    intro low
    have atEnd : i = bs.length := by omega
    subst atEnd
    simpa using (Utf8From.endOfInput : Utf8From bs bs.length [])
  | succ n ih =>
    intro low
    have more : i < bs.length := by omega
    have unit : Rowl.Unicode.Prefix bs i = some (bs[i].val, 1) := by
      have small := ascii bs[i] (List.getElem_mem more)
      simp [Rowl.Unicode.Prefix, List.getElem?_eq_getElem more, small]
    rw [List.drop_eq_getElem_cons more, List.map_cons]
    exact Utf8From.character unit (by omega) (by omega) (ih (i + 1) (by omega) (by omega))

/-- The real byte entry point terminates with exact grammar acceptance or failure. -/
theorem validate_iri_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ result, iri.validate_iri bytes = .ok result ∧ ValidationCorrect IriLanguage bytes.val result := by
  obtain ⟨plain, plainRun, plainSound⟩ := plain_iri_spec bytes
  cases plain with
  | true =>
    obtain ⟨ascii, member⟩ := plainSound rfl
    refine ⟨.Matched true, by rw [iri.validate_iri, plainRun]; simp, bytes.val.map (·.val), ?_, by simp [member]⟩
    simpa using ascii_utf8 bytes.val ascii 0 (Nat.zero_le _)
  | false =>
    obtain ⟨expression, he, sem⟩ := iri_grammar_total_correct
    obtain ⟨result, hr, hc⟩ := matches_utf8_total_correct expression bytes
    exact ⟨result, by rw [iri.validate_iri, plainRun]; simp [he, validate_eq, hr], (converted _ _ _ _ sem).mp hc⟩

theorem validate_reference_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ result, iri.validate_reference bytes = .ok result ∧ ValidationCorrect ReferenceLanguage bytes.val result := by
  obtain ⟨expression, he, sem⟩ := reference_grammar_total_correct
  obtain ⟨result, hr, hc⟩ := matches_utf8_total_correct expression bytes
  exact ⟨result, by rw [iri.validate_reference, he, bind_ok, validate_eq, hr], (converted _ _ _ _ sem).mp hc⟩

/-- All and only well-encoded RFC 3987 IRIs are accepted; fragments are allowed. -/
theorem validate_iri_accepted_iff (bytes : alloc.vec.Vec U8) :
    iri.validate_iri bytes = .ok (.Matched true) ↔
      ∃ word, Utf8From bytes.val 0 word ∧ word ∈ IriLanguage := by
  obtain ⟨plain, plainRun, plainSound⟩ := plain_iri_spec bytes
  cases plain with
  | true =>
    obtain ⟨ascii, member⟩ := plainSound rfl
    rw [iri.validate_iri, plainRun]
    simp only [bind_ok, ite_true]
    exact ⟨fun _ => ⟨bytes.val.map (·.val), by simpa using ascii_utf8 bytes.val ascii 0 (Nat.zero_le _), member⟩,
      fun _ => trivial⟩
  | false =>
    obtain ⟨expression, he, sem⟩ := iri_grammar_total_correct
    rw [iri.validate_iri, plainRun]
    simp only [bind_ok, Bool.false_eq_true, ite_false]
    rw [he, bind_ok, validate_eq]
    simpa [sem] using matches_utf8_accepted_iff expression bytes

theorem validate_reference_accepted_iff (bytes : alloc.vec.Vec U8) :
    iri.validate_reference bytes = .ok (.Matched true) ↔
      ∃ word, Utf8From bytes.val 0 word ∧ word ∈ ReferenceLanguage := by
  obtain ⟨expression, he, sem⟩ := reference_grammar_total_correct
  rw [iri.validate_reference, he, bind_ok, validate_eq]
  simpa [sem] using matches_utf8_accepted_iff expression bytes

end Rowl.Iri
