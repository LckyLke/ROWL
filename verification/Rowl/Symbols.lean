import Rowl.Generated.RowlKernel

namespace Rowl.Symbols
open Aeneas Aeneas.Std RowlRust.symbols

def byteKeys (table : SymbolTable) : List (List U8) := table.keys.val.map alloc.vec.Vec.val

def WellFormed (table : SymbolTable) : Prop :=
  (byteKeys table).Nodup ∧ table.keys.val.length ≤ table.limit.val

def firstIndex (table : SymbolTable) (key : alloc.vec.Vec U8) : Option Nat :=
  table.keys.val.findIdx? (fun stored => decide (stored.val = key.val))

def InternCorrect (before : SymbolTable) (key : alloc.vec.Vec U8)
    (outcome : InternResult) (after : SymbolTable) : Prop :=
  match outcome with
  | .Existing symbol => after = before ∧ firstIndex before key = some symbol.val
  | .Inserted symbol => firstIndex before key = none ∧ symbol.val = before.keys.val.length ∧
      before.keys.val.length < before.limit.val ∧ after.limit = before.limit ∧
      after.keys.val = before.keys.val ++ [key]
  | .CapacityExceeded => after = before ∧ firstIndex before key = none ∧
      before.keys.val.length = before.limit.val

private theorem compare_correct (left right : alloc.vec.Vec U8)
    (equalLength : left.val.length = right.val.length) (index : Usize) :
    compare_from left right index =
      .ok (decide (left.val.drop index.val = right.val.drop index.val)) := by
  rw [compare_from]
  by_cases h : index.val < left.val.length
  · have hr : index.val < right.val.length := by omega
    have hlIndex : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    have hrIndex : right.index_usize index = .ok right.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hr]
    by_cases heads : left.val[index.val] = right.val[index.val]
    · have size := left.property
      obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have ih := compare_correct left right equalLength next
      simp [h, hlIndex, hrIndex, heads, hn, ih]
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq, heads, true_and, nextval]
    · simp [h, hlIndex, hrIndex, heads]
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq, heads, false_and, not_false_eq_true]
  · have hl : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hr : right.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [h, hl, hr]
termination_by left.val.length - index.val
decreasing_by omega

theorem same_spelling_total_correct (left right : alloc.vec.Vec U8) :
    same_spelling left right = .ok (decide (left.val = right.val)) := by
  rw [same_spelling]
  by_cases h : left.val.length = right.val.length
  · have ih := compare_correct left right h 0#usize
    simpa [h] using ih
  · have unequal : left.val ≠ right.val := fun eq => h (congrArg List.length eq)
    simp [h, unequal]

private theorem find_correct (keys : alloc.vec.Vec (alloc.vec.Vec U8))
    (key : alloc.vec.Vec U8) (bounded : keys.val.length ≤ U32.max)
    (index : Usize) :
    ∃ result, find_from keys key index = .ok result ∧
      result.map UScalar.val = ((keys.val.drop index.val).findIdx?
        (fun stored => decide (stored.val = key.val))).map (fun offset => index.val + offset) := by
  rw [find_from]
  by_cases h : index.val < keys.val.length
  · have hi : keys.index_usize index = .ok keys.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    have same := same_spelling_total_correct keys.val[index.val] key
    by_cases equalKey : keys.val[index.val].val = key.val
    · obtain ⟨symbol, hs, hv⟩ := WP.spec_imp_exists (UScalar.cast_inBounds_spec .U32 index (by scalar_tac))
      refine ⟨some symbol, by simp [h, hi, same, equalKey, hs], ?_⟩
      rw [List.drop_eq_getElem_cons h]
      simp only [List.findIdx?_cons, equalKey, decide_true, ↓reduceIte,
        Option.map_some, Nat.add_zero, hv]
    · have size := keys.property
      obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      obtain ⟨result, hr, correct⟩ := find_correct keys key bounded next
      refine ⟨result, by simp [h, hi, same, equalKey, hn, hr], ?_⟩
      rw [correct, List.drop_eq_getElem_cons h]
      simp only [List.findIdx?_cons, equalKey, decide_false, Bool.false_eq_true, ↓reduceIte,
        Option.map_map, nextval]
      congr 1
      funext offset
      simp only [Function.comp_def]
      omega
  · have drop : keys.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    exact ⟨none, by simp [h], by simp [drop]⟩
termination_by keys.val.length - index.val
decreasing_by omega

theorem empty_total_correct (limit : U32) :
    ∃ table, empty limit = .ok table ∧ WellFormed table ∧ byteKeys table = [] ∧ table.limit = limit := by
  refine ⟨{ keys := alloc.vec.Vec.new _, limit }, rfl, ?_, ?_, rfl⟩ <;>
    simp [WellFormed, byteKeys]

theorem lookup_total_correct (table : SymbolTable) (key : alloc.vec.Vec U8) (valid : WellFormed table) :
    ∃ result, lookup table key = .ok result ∧ result.map UScalar.val = firstIndex table key := by
  have bound : table.keys.val.length ≤ U32.max := by
    have := valid.2
    scalar_tac
  obtain ⟨result, hr, meaning⟩ := find_correct table.keys key bound 0#usize
  exact ⟨result, hr, by simpa [firstIndex] using meaning⟩

theorem key_of_total_correct (table : SymbolTable) (symbol : U32) :
    key_of table symbol = .ok (table.keys.val[symbol.val]?) := by
  unfold key_of
  simp only [lift, bind_ok]
  by_cases h : symbol.val < table.keys.val.length
  · have hi : table.keys.index_usize (UScalar.cast .Usize symbol) =
        .ok table.keys.val[symbol.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    simp [h, hi]
  · simp [h]

private theorem absent_key (table : SymbolTable) (key : alloc.vec.Vec U8)
    (absent : firstIndex table key = none) : key.val ∉ byteKeys table := by
  have all := List.findIdx?_eq_none_iff.mp absent
  simp only [byteKeys, List.mem_map]
  rintro ⟨stored, mem, equal⟩
  have := all stored mem
  simp [equal] at this

/-- Successful execution, exact outcome and invariant preservation. The private
    Rust fields ensure callers construct tables through empty/intern only. -/
theorem intern_total_correct (table : SymbolTable) (key : alloc.vec.Vec U8) (valid : WellFormed table) :
    ∃ outcome after, intern table key = .ok (outcome, after) ∧
      InternCorrect table key outcome after ∧ WellFormed after := by
  obtain ⟨found, hf, first⟩ := lookup_total_correct table key valid
  cases found with
  | some symbol =>
    refine ⟨.Existing symbol, table, by simp [intern, hf], ⟨rfl, ?_⟩, valid⟩
    exact first.symm
  | none =>
    have absent : firstIndex table key = none := first.symm
    obtain ⟨count, hc, hv⟩ := WP.spec_imp_exists
      (UScalar.cast_inBounds_spec .U32 table.keys.len (by have := valid.2; scalar_tac))
    have countval : count.val = table.keys.val.length := by simpa using hv
    by_cases room : table.keys.val.length < table.limit.val
    · have pushBound : table.keys.val.length < Usize.max := by scalar_tac
      obtain ⟨appended, hp, content⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec table.keys key pushBound)
      let after : SymbolTable := { table with keys := appended }
      refine ⟨.Inserted count, after, by simp [intern, hf, hc, countval, room, hp, after],
        ⟨absent, countval, room, rfl, content⟩, ?_⟩
      have fresh := absent_key table key absent
      constructor
      · simp only [byteKeys, after, content, List.map_append, List.map_singleton, List.nodup_append]
        refine ⟨valid.1, by simp, ?_⟩
        intro old mem value singleton
        simp only [List.mem_singleton] at singleton
        subst value
        exact fun equal => fresh (equal ▸ mem)
      · simp only [after, content, List.length_append, List.length_singleton]
        omega
    · refine ⟨.CapacityExceeded, table, by simp [intern, hf, hc, countval, room],
        ⟨rfl, absent, by have := valid.2; omega⟩, valid⟩

/-- An insertion or capacity rejection cannot renumber or replace an old key. -/
theorem intern_preserves_existing_symbols (before : SymbolTable) (key : alloc.vec.Vec U8)
    (valid : WellFormed before) (outcome : InternResult) (after : SymbolTable)
    (executed : intern before key = .ok (outcome, after)) (symbol : U32)
    (old : symbol.val < before.keys.val.length) :
    key_of after symbol = key_of before symbol := by
  obtain ⟨result, checked, hr, correct, _⟩ := intern_total_correct before key valid
  have equal := Result.ok_injective (hr.symm.trans executed)
  cases equal
  rw [key_of_total_correct, key_of_total_correct]
  cases outcome with
  | Existing s => rw [correct.1]
  | CapacityExceeded => rw [correct.1]
  | Inserted s =>
    rw [correct.2.2.2.2]
    exact congrArg Result.ok (List.getElem?_append_left old)

/-- A well-formed table maps different valid symbols to different byte keys. -/
theorem symbols_distinguish_keys (table : SymbolTable) (valid : WellFormed table)
    (left right : U32) (hl : left.val < (byteKeys table).length)
    (hr : right.val < (byteKeys table).length)
    (same : (byteKeys table)[left.val] = (byteKeys table)[right.val]) : left = right := by
  have ids := valid.1.getElem_inj_iff.mp same
  exact UScalar.eq_of_val_eq ids

end Rowl.Symbols
