import Rowl.Unicode

namespace Rowl.Encoding
open Aeneas Aeneas.Std RowlFrontendRust.encoding
open Rowl.Unicode
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- Unicode scalar values, independent of the Rust machine arithmetic. -/
def Scalar (cp : Nat) : Prop := cp ≤ 1114111 ∧ ¬ (55296 ≤ cp ∧ cp ≤ 57343)
def Bytes : Encoded → List U8
  | .One a => [a]
  | .Two a b => [a,b]
  | .Three a b c => [a,b,c]
  | .Four a b c d => [a,b,c,d]
/-- Exactly one canonical RFC 3629 production denotes the requested scalar.
    Invalid values are explicit, rather than replacement characters. -/
def EncodeCorrect (cp : Nat) : Option Encoded → Prop
  | none => ¬ Scalar cp
  | some (.One a) => a.val < 128 ∧ a.val = cp
  | some (.Two a b) => Pair a.val b.val ∧ value2 a.val b.val = cp
  | some (.Three a b c) => Triple a.val b.val c.val ∧ value3 a.val b.val c.val = cp
  | some (.Four a b c d) => Quad a.val b.val c.val d.val ∧ value4 a.val b.val c.val d.val = cp

theorem scalar_total_correct (cp : U32) :
    scalar cp = .ok (decide (Scalar cp.val)) := by
  simp [scalar, Scalar]
  split <;> simp_all
  split <;> simp_all

theorem encode_total_correct (cp : U32) :
    ∃ r, encode cp = .ok r ∧ EncodeCorrect cp.val r := by
  apply WP.spec_imp_exists
  unfold encode
  rw [scalar_total_correct]
  simp only [bind_ok]
  split
  · rename_i valid
    have hs : Scalar cp.val := by simpa using valid
    split
    · step*
      simp_all [EncodeCorrect]
      scalar_tac
    · split
      · step*
        simp_all [EncodeCorrect, Pair, Tail, value2]
        scalar_tac
      · split
        · step*
          simp_all [EncodeCorrect, Triple, Tail, value3, Scalar]
          scalar_tac
        · step*
          simp_all [EncodeCorrect, Quad, Tail, value4, Scalar]
          scalar_tac
  · rename_i invalid
    simp_all [EncodeCorrect]

private theorem successful_scalar (cp : Nat) (e : Encoded)
    (correct : EncodeCorrect cp (some e)) : Scalar cp := by
  cases e with
  | One a => simp only [EncodeCorrect] at correct; unfold Scalar; omega
  | Two a b =>
    simp only [EncodeCorrect] at correct
    have bounds := (byte_grammar_scalar_ranges a.val b.val 0 0).1 correct.1
    unfold Scalar
    omega

  | Three a b c =>
    simp only [EncodeCorrect] at correct
    have bounds := (byte_grammar_scalar_ranges a.val b.val c.val 0).2.1 correct.1
    unfold Scalar
    omega
  | Four a b c d =>
    simp only [EncodeCorrect] at correct
    have bounds := (byte_grammar_scalar_ranges a.val b.val c.val d.val).2.2 correct.1
    unfold Scalar
    omega

/-- The RFC byte productions have a unique canonical spelling for each scalar.
    This is a property of the independent grammar, rather than an equality
    obtained by rerunning the encoder. -/
theorem encoded_unique (cp : Nat) (one two : Encoded)
    (first : EncodeCorrect cp (some one)) (second : EncodeCorrect cp (some two)) :
    one = two := by
  cases one <;> cases two <;>
    simp only [EncodeCorrect] at first second
  all_goals
    try simp only [Pair, Triple, Quad, Tail, value2, value3, value4] at first second
  all_goals try first
    | omega
    | congr 1 <;> apply UScalar.eq_of_val_eq <;> omega
/-- Every grammar-legal encoded unit is exactly the unit the executable
    encoder returns. -/
theorem encode_some_iff (cp : U32) (e : Encoded) :
    encode cp = .ok (some e) ↔ EncodeCorrect cp.val (some e) := by
  obtain ⟨result, executed, correct⟩ := encode_total_correct cp
  constructor
  · intro accepted
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal] using correct
  · intro valid
    cases result with
    | none => exact False.elim (correct (successful_scalar cp.val e valid))
    | some actual =>
      have equal := encoded_unique cp.val actual e correct valid
      simpa [equal] using executed
/-- Failure is exactly a non-scalar input, for every machine u32 value. -/
theorem encode_none_iff (cp : U32) : encode cp = .ok none ↔ ¬ Scalar cp.val := by
  obtain ⟨r, hr, hc⟩ := encode_total_correct cp
  cases r with
  | none => simpa [hr, EncodeCorrect] using hc
  | some e =>
    have valid := successful_scalar cp.val e hc
    simp [hr, valid]

/-- The independent strict UTF-8 recognizer recovers the exact encoded value
    and consumes precisely the encoded width. -/
theorem encode_prefix_inverse (cp : U32) (e : Encoded)
    (success : encode cp = .ok (some e)) :
    Prefix (Bytes e) 0 = some (cp.val, (Bytes e).length) := by
  obtain ⟨r, hr, hc⟩ := encode_total_correct cp
  have eq := Result.ok_injective (hr.symm.trans success)
  subst r
  cases e with
  | One a =>
    obtain ⟨ha, hv⟩ := hc
    have hcp : cp.val < 128 := by omega
    simp [Prefix, Bytes, ha, hv, hcp]
  | Two a b =>
    obtain ⟨hg, hv⟩ := hc
    have hi : ¬ a.val < 128 := by simp only [Pair] at hg; omega
    have h2 : a.val < 224 := by simp only [Pair] at hg; omega
    simp [Prefix, Bytes, hi, h2, hg, hv]
  | Three a b c =>
    obtain ⟨hg, hv⟩ := hc
    have hi : ¬ a.val < 128 := by simp only [Triple] at hg; omega
    have h2 : ¬ a.val < 224 := by simp only [Triple] at hg; omega
    have h3 : a.val < 240 := by simp only [Triple] at hg; omega
    simp [Prefix, Bytes, hi, h2, h3, hg, hv]
  | Four a b c d =>
    obtain ⟨hg, hv⟩ := hc
    have hi : ¬ a.val < 128 := by simp only [Quad] at hg; omega
    have h2 : ¬ a.val < 224 := by simp only [Quad] at hg; omega
    have h3 : ¬ a.val < 240 := by simp only [Quad] at hg; omega
    simp [Prefix, Bytes, hi, h2, h3, hg, hv]

/-- Composition with the actual extracted decoder, including its byte offset.
    The supplied vector consists of exactly the fixed-size encoded unit. -/
theorem decode_encoded_unit (cp : U32) (e : Encoded)
    (bytes : alloc.vec.Vec U8) (success : encode cp = .ok (some e))
    (contents : bytes.val = Bytes e) :
    ∃ next, RowlFrontendRust.unicode.decode_next bytes 0#usize =
      .ok (.Scalar cp next) ∧ next.val = bytes.val.length := by
  have unitPrefix := encode_prefix_inverse cp e success
  rw [← contents] at unitPrefix
  have nonempty : 0 < bytes.val.length := by rw [contents]; cases e <;> simp [Bytes]
  obtain ⟨r, hr, hc⟩ := decode_next_total_correct bytes 0#usize
  cases r with
  | End =>
    have empty : bytes.val.length = 0 := by simpa [StepCorrect] using hc.symm
    omega
  | Scalar decoded next =>
    obtain ⟨advanced, bounded, unitMatch⟩ := hc
    have eq := Prod.mk.inj (Option.some.inj (unitPrefix.symm.trans (by simpa using unitMatch)))
    have cpEq : decoded = cp := by apply UScalar.eq_of_val_eq; exact eq.1.symm
    have widthEq : next.val = bytes.val.length := by simpa using eq.2.symm
    exact ⟨next, by simpa [cpEq] using hr, widthEq⟩
  | Error error =>
    cases error <;> simp_all [StepCorrect]

end Rowl.Encoding
