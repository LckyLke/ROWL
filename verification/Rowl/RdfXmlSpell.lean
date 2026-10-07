import Rowl.RdfXmlGrammar

namespace Rowl.RdfXmlSpell
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar Rowl.RdfXmlGrammar
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ## Bytes and UTF-8 spellings -/

theorem byte_val_eq (n : Nat) (h : n < 256) : (byte n).val = n := by
  simp only [byte]
  show (BitVec.ofNat 8 n).toNat = n
  rw [BitVec.toNat_ofNat]
  omega

theorem byte_val (b : U8) : byte b.val = b := by
  apply UScalar.eq_of_val_eq
  have : b.val < 256 := by have := b.hBounds; simpa using this
  exact byte_val_eq _ this

/-- The canonical encoding of a scalar value is its UTF-8 bytes. -/
theorem encode_bytes (cp : U32) (e : encoding.Encoded) (h : encoding.encode cp = .ok (some e)) :
    Rowl.Encoding.Bytes e = (Rowl.IriResolution.utf8 cp.val).map byte := by
  have hc := (Rowl.Encoding.encode_some_iff cp e).mp h
  cases e with
  | One a =>
    simp only [Rowl.Encoding.EncodeCorrect] at hc
    obtain ⟨lt, eq⟩ := hc
    have u : Rowl.IriResolution.utf8 cp.val = [a.val] := by
      unfold Rowl.IriResolution.utf8; rw [if_pos (by omega)]; rw [eq]
    rw [u]; simp [Rowl.Encoding.Bytes, byte_val]
  | Two a b =>
    simp only [Rowl.Encoding.EncodeCorrect, Rowl.Unicode.Pair, Rowl.Unicode.Tail, Rowl.Unicode.value2] at hc
    obtain ⟨⟨a1, a2, b1, b2⟩, eq⟩ := hc
    have u : Rowl.IriResolution.utf8 cp.val = [a.val, b.val] := by
      unfold Rowl.IriResolution.utf8
      rw [if_neg (by omega), if_pos (by omega)]
      simp only [List.cons.injEq, and_true]
      refine ⟨by omega, by omega⟩
    rw [u]; simp [Rowl.Encoding.Bytes, byte_val]
  | Three a b c =>
    simp only [Rowl.Encoding.EncodeCorrect, Rowl.Unicode.Triple, Rowl.Unicode.Tail, Rowl.Unicode.value3] at hc
    obtain ⟨⟨h1, c1, c2⟩, eq⟩ := hc
    have u : Rowl.IriResolution.utf8 cp.val = [a.val, b.val, c.val] := by
      unfold Rowl.IriResolution.utf8
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      simp only [List.cons.injEq, and_true]
      refine ⟨by omega, by omega, by omega⟩
    rw [u]; simp [Rowl.Encoding.Bytes, byte_val]
  | Four a b c d =>
    simp only [Rowl.Encoding.EncodeCorrect, Rowl.Unicode.Quad, Rowl.Unicode.Tail, Rowl.Unicode.value4] at hc
    obtain ⟨⟨h1, ⟨c1, c2⟩, ⟨d1, d2⟩⟩, eq⟩ := hc
    have u : Rowl.IriResolution.utf8 cp.val = [a.val, b.val, c.val, d.val] := by
      unfold Rowl.IriResolution.utf8
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp only [List.cons.injEq, and_true]
      refine ⟨by omega, by omega, by omega, by omega⟩
    rw [u]; simp [Rowl.Encoding.Bytes, byte_val]

theorem utf8Bytes_nil : utf8Bytes [] = [] := by simp [utf8Bytes]

theorem utf8Bytes_cons (c : Nat) (w : Word) :
    utf8Bytes (c :: w) = (Rowl.IriResolution.utf8 c).map byte ++ utf8Bytes w := by
  simp [utf8Bytes]

theorem utf8Bytes_append (v w : Word) : utf8Bytes (v ++ w) = utf8Bytes v ++ utf8Bytes w := by
  simp [utf8Bytes]

theorem utf8_ascii (c : Nat) (h : c < 128) : Rowl.IriResolution.utf8 c = [c] := by
  unfold Rowl.IriResolution.utf8; rw [if_pos h]

theorem utf8_small (c : Nat) (h : Rowl.Encoding.Scalar c) : ∀ x ∈ Rowl.IriResolution.utf8 c, x < 256 := by
  unfold Rowl.Encoding.Scalar at h
  unfold Rowl.IriResolution.utf8
  split_ifs <;> simp <;> omega

/-- The byte values of the UTF-8 bytes of scalar values. -/
theorem word_utf8Bytes (w : Word) (h : ∀ c ∈ w, Rowl.Encoding.Scalar c) :
    Rowl.References.Word (utf8Bytes w) = w.flatMap Rowl.IriResolution.utf8 := by
  induction w with
  | nil => simp [utf8Bytes, Rowl.References.Word]
  | cons c rest ih =>
    rw [utf8Bytes_cons]
    simp only [Rowl.References.Word, List.map_append, List.flatMap_cons] at ih ⊢
    rw [ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    congr 1
    rw [List.map_map]
    conv => rhs; rw [← List.map_id (Rowl.IriResolution.utf8 c)]
    apply List.map_congr_left
    intro x hx
    exact byte_val_eq x (utf8_small c (h c List.mem_cons_self) x hx)

end Rowl.RdfXmlSpell
