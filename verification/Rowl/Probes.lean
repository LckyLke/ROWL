import Rowl.Generated.RowlKernel

namespace Rowl.Probes
open Aeneas Aeneas.Std RowlRust.probes

def naturalValue : Natural → Nat
  | .Zero => 0
  | .Succ n => naturalValue n + 1

/-- Exact unbounded addition and termination of the actual Rust recursion. -/
theorem add_total_correct (left right : Natural) :
    ∃ sum, add left right = .ok sum ∧
      naturalValue sum = naturalValue left + naturalValue right := by
  induction left with
  | Zero => exact ⟨right, by simp [add], by simp [naturalValue]⟩
  | Succ previous ih =>
    obtain ⟨sum, hs, hv⟩ := ih
    refine ⟨.Succ sum, ?_, ?_⟩
    · simp [add, hs]
    · simp [naturalValue, hv, Nat.add_comm, Nat.add_left_comm]

/-- Mathematical first-match semantics, independent of the operational lookup. -/
def firstMatch : Catalog → U32 → Option (alloc.vec.Vec U8)
  | .Empty, _ => none
  | .Entry entryKey bytes next, key =>
    if key = entryKey then some bytes else firstMatch next key

theorem lookup_total_correct (catalog : Catalog) (key : U32) :
    lookup catalog key = .ok (firstMatch catalog key) := by
  induction catalog with
  | Empty => simp [lookup, firstMatch]
  | Entry entryKey bytes next ih =>
    rw [lookup]
    by_cases h : key = entryKey <;> simp [h, firstMatch, ih]

/-- Mutation affects exactly the selected slot; invalid indices preserve state. -/
theorem replace_slot_total_correct (slots : alloc.vec.Vec U32) (index : Usize) (value : U32) :
    ∃ changed after, replace_slot slots index value = .ok (changed, after) ∧
      (changed = true ↔ index.val < slots.val.length) ∧
      after.val = slots.val.set index.val value := by
  unfold replace_slot
  by_cases h : index.val < slots.val.length
  · have hi : slots.index_usize index = .ok slots.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    refine ⟨true, slots.set index value, ?_, by simp [h], ?_⟩
    · simp [h, alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize, hi]
    · simp
  · refine ⟨false, slots, by simp [h], by simp [h], ?_⟩
    exact (List.set_eq_of_length_le (l := slots.val) (by omega)).symm

/-- Byte recognition returns a decimal value exactly on the ASCII digit interval. -/
theorem decimal_digit_total_correct (byte : U8) :
    ∃ result, decimal_digit byte = .ok result ∧
      (match result with
       | none => ¬ (48 ≤ byte.val ∧ byte.val ≤ 57)
       | some digit => digit.val < 10 ∧ byte.val = 48 + digit.val) := by
  unfold decimal_digit
  split
  · split
    · have hLower : 48 ≤ byte.val := by scalar_tac
      have hUpper : byte.val ≤ 57 := by scalar_tac
      have hSub := U8.sub_spec (x := byte) (y := 48#u8) hLower
      obtain ⟨digit, hd, hv⟩ := WP.spec_imp_exists hSub
      refine ⟨some digit, by simp [hd], ?_⟩
      norm_num at hv ⊢
      omega
    · simp_all
  · simp_all

end Rowl.Probes
