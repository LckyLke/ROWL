import Rowl.Regular

open Aeneas Aeneas.Std Aeneas.Std.Result RowlFrontendRust
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

/-- The real byte entry point terminates with exact grammar acceptance or failure. -/
theorem validate_iri_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ result, iri.validate_iri bytes = .ok result ∧ ValidationCorrect IriLanguage bytes.val result := by
  obtain ⟨expression, he, sem⟩ := iri_grammar_total_correct
  obtain ⟨result, hr, hc⟩ := matches_utf8_total_correct expression bytes
  exact ⟨result, by simp [iri.validate_iri, he, hr], (converted _ _ _ _ sem).mp hc⟩

theorem validate_reference_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ result, iri.validate_reference bytes = .ok result ∧ ValidationCorrect ReferenceLanguage bytes.val result := by
  obtain ⟨expression, he, sem⟩ := reference_grammar_total_correct
  obtain ⟨result, hr, hc⟩ := matches_utf8_total_correct expression bytes
  exact ⟨result, by simp [iri.validate_reference, he, hr], (converted _ _ _ _ sem).mp hc⟩

/-- All and only well-encoded RFC 3987 IRIs are accepted; fragments are allowed. -/
theorem validate_iri_accepted_iff (bytes : alloc.vec.Vec U8) :
    iri.validate_iri bytes = .ok (.Matched true) ↔
      ∃ word, Utf8From bytes.val 0 word ∧ word ∈ IriLanguage := by
  obtain ⟨expression, he, sem⟩ := iri_grammar_total_correct
  simpa [iri.validate_iri, he, sem] using matches_utf8_accepted_iff expression bytes

theorem validate_reference_accepted_iff (bytes : alloc.vec.Vec U8) :
    iri.validate_reference bytes = .ok (.Matched true) ↔
      ∃ word, Utf8From bytes.val 0 word ∧ word ∈ ReferenceLanguage := by
  obtain ⟨expression, he, sem⟩ := reference_grammar_total_correct
  simpa [iri.validate_reference, he, sem] using matches_utf8_accepted_iff expression bytes

end Rowl.Iri
