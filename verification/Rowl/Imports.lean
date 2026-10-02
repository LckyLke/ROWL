import Rowl.Generated.RowlKernel
import Mathlib.Logic.Relation

namespace Rowl.Imports
open Aeneas Aeneas.Std RowlRust.imports

def ids : DocumentIds → List U32
  | .Empty => []
  | .Cons key tail => key :: ids tail

abbrev Row := U32 × alloc.vec.Vec U8 × DocumentIds

def rows : DocumentCatalog → List Row
  | .Empty => []
  | .Document key bytes imports next => (key, bytes, imports) :: rows next

def keys (catalog : DocumentCatalog) : List U32 := (rows catalog).map Prod.fst

def Edge (catalog : DocumentCatalog) (source target : U32) : Prop :=
  ∃ bytes imports, (source, bytes, imports) ∈ rows catalog ∧ target ∈ ids imports

def Reachable (catalog : DocumentCatalog) (root target : U32) : Prop :=
  Relation.ReflTransGen (Edge catalog) root target

/-- Exact reachable set with original payloads; reachable missing or ambiguous keys. -/
def Correct (catalog : DocumentCatalog) (root : U32) : Resolution → Prop
  | .Complete closure =>
    (keys closure).Nodup ∧
    (∀ row ∈ rows closure, row ∈ rows catalog) ∧
    ∀ key, key ∈ keys closure ↔ Reachable catalog root key
  | .MissingDocument key => Reachable catalog root key ∧ key ∉ keys catalog
  | .DuplicateDocument key => 2 ≤ (keys catalog).count key

private theorem keys_cons (key : U32) (bytes : alloc.vec.Vec U8) (im : DocumentIds) (next : DocumentCatalog) :
    keys (.Document key bytes im next) = key :: keys next := rfl

private theorem mem_keys (catalog : DocumentCatalog) (key : U32) :
    key ∈ keys catalog ↔ ∃ bytes imports, (key, bytes, imports) ∈ rows catalog := by
  simp only [keys, List.mem_map]
  constructor
  · rintro ⟨⟨k, b, im⟩, hm, rfl⟩; exact ⟨b, im, hm⟩
  · rintro ⟨b, im, hm⟩; exact ⟨(key, b, im), hm, rfl⟩

private theorem contains_correct (catalog : DocumentCatalog) (key : U32) :
    contains catalog key = .ok (decide (key ∈ keys catalog)) := by
  induction catalog with
  | Empty => simp [contains, keys, rows]
  | Document k b im next ih =>
    rw [contains]
    by_cases h : k = key
    · simp [h, keys, rows]
    · simp only [h, ↓reduceIte, ih, keys_cons, List.mem_cons, Ne.symm h, false_or]

private theorem copy_correct (im : DocumentIds) : copy_ids im = .ok im := by
  induction im with
  | Empty => simp [copy_ids]
  | Cons k tail ih => simp [copy_ids, ih]

private theorem append_correct (a b : DocumentIds) :
    ∃ c, append_ids a b = .ok c ∧ ids c = ids a ++ ids b := by
  induction a with
  | Empty => exact ⟨b, by simp [append_ids], by simp [ids]⟩
  | Cons k tail ih =>
    obtain ⟨c, hc, hv⟩ := ih
    exact ⟨.Cons k c, by simp [append_ids, hc], by simp [ids, hv]⟩

private theorem duplicate_correct (catalog : DocumentCatalog) :
    ∃ result, duplicate catalog = .ok result ∧
      (result = none ↔ (keys catalog).Nodup) ∧
      (∀ key, result = some key → 2 ≤ (keys catalog).count key) := by
  induction catalog with
  | Empty => exact ⟨none, by simp [duplicate], by simp [keys, rows], by simp⟩
  | Document k b im next ih =>
    obtain ⟨result, hr, hn, hd⟩ := ih
    have hc := contains_correct next k
    by_cases hm : k ∈ keys next
    · refine ⟨some k, ?_, ?_, ?_⟩
      · simp [duplicate, hc, hm]
      · simp only [keys_cons, List.nodup_cons, hm, not_true_eq_false, false_and, Option.some_ne_none]
      · intro key hk
        have heq : k = key := Option.some.inj hk
        subst key
        rw [keys_cons, List.count_cons_self]
        have hp := List.count_pos_iff.mpr hm
        omega
    · refine ⟨result, ?_, ?_, ?_⟩
      · simp [duplicate, hc, hm, hr]
      · simpa only [keys_cons, List.nodup_cons, hm, not_false_eq_true, true_and] using hn
      · intro key hk
        have bound := hd key hk
        rw [keys_cons, List.count_cons]
        split <;> omega

private def TakeCorrect (catalog : DocumentCatalog) (key : U32) : Taken → Prop
  | .Missing => key ∉ keys catalog
  | .Found b im remaining =>
    (rows catalog).Perm ((key, b, im) :: rows remaining)

private theorem take_correct (catalog : DocumentCatalog) (key : U32) :
    ∃ result, take catalog key = .ok result ∧ TakeCorrect catalog key result := by
  induction catalog with
  | Empty => exact ⟨.Missing, by simp [take], by simp [TakeCorrect, keys, rows]⟩
  | Document k b im next ih =>
    by_cases heq : k = key
    · subst k
      exact ⟨.Found b im next, by simp [take], List.Perm.refl _⟩
    · obtain ⟨result, hr, hs⟩ := ih
      cases result with
      | Missing =>
        exact ⟨.Missing, by simp [take, heq, hr], by simpa only [TakeCorrect, keys_cons, List.mem_cons, Ne.symm heq, false_or] using hs⟩
      | Found b' im' remaining =>
        refine ⟨.Found b' im' (.Document k b im remaining), by simp [take, heq, hr], ?_⟩
        exact (List.Perm.cons _ hs).trans (List.Perm.swap ..)

private structure Invariant (catalog : DocumentCatalog) (root : U32)
    (pending : DocumentIds) (available resolved : DocumentCatalog) : Prop where
  partition : (rows available ++ rows resolved).Perm (rows catalog)
  pendingReachable : ∀ key ∈ ids pending, Reachable catalog root key
  resolvedReachable : ∀ key ∈ keys resolved, Reachable catalog root key
  rootFrontier : root ∈ keys resolved ∨ root ∈ ids pending
  edgeFrontier : ∀ source bytes imports, (source, bytes, imports) ∈ rows resolved →
    ∀ target ∈ ids imports, target ∈ keys resolved ∨ target ∈ ids pending

private theorem row_unique (catalog : DocumentCatalog) (unique : (keys catalog).Nodup)
    (a b : Row) (ha : a ∈ rows catalog) (hb : b ∈ rows catalog) (eq : a.1 = b.1) : a = b := by
  have inj := List.inj_on_of_nodup_map unique
  exact inj ha hb eq

private theorem finish (catalog : DocumentCatalog) (root : U32) (available resolved : DocumentCatalog)
    (unique : (keys catalog).Nodup) (inv : Invariant catalog root .Empty available resolved) :
    Correct catalog root (.Complete resolved) := by
  have subset : ∀ row ∈ rows resolved, row ∈ rows catalog := by
    intro row hm
    exact inv.partition.mem_iff.mp (List.mem_append_right _ hm)
  have noDup : (keys resolved).Nodup := by
    have hp := inv.partition.map Prod.fst
    have hn : ((rows available ++ rows resolved).map Prod.fst).Nodup := hp.nodup_iff.mpr unique
    exact (List.nodup_append.mp (by simpa [List.map_append, keys] using hn)).2.1
  refine ⟨noDup, subset, fun key => ⟨inv.resolvedReachable key, ?_⟩⟩
  intro reachable
  have rootMem : root ∈ keys resolved := by simpa [ids] using inv.rootFrontier
  induction reachable with
  | refl => exact rootMem
  | @tail key target path edge ih =>
    obtain ⟨b, im, hrow, ht⟩ := edge
    obtain ⟨b', im', hrow'⟩ := (mem_keys resolved key).mp ih
    have same := row_unique catalog unique (key, b, im) (key, b', im') hrow (subset _ hrow') rfl
    cases same
    simpa [ids] using inv.edgeFrontier key b im hrow' target ht

private theorem advance_seen (catalog : DocumentCatalog) (root key : U32) (tail : DocumentIds)
    (available resolved : DocumentCatalog) (inv : Invariant catalog root (.Cons key tail) available resolved)
    (seen : key ∈ keys resolved) : Invariant catalog root tail available resolved := by
  refine ⟨inv.partition, ?_, inv.resolvedReachable, ?_, ?_⟩
  · intro k hk; exact inv.pendingReachable k (by simp [ids, hk])
  · rcases inv.rootFrontier with h | h
    · exact Or.inl h
    · rcases (List.mem_cons.mp h) with h | h
      · exact Or.inl (h ▸ seen)
      · exact Or.inr h
  · intro source b im hm target ht
    rcases inv.edgeFrontier source b im hm target ht with h | h
    · exact Or.inl h
    · rcases (List.mem_cons.mp h) with h | h
      · exact Or.inl (h ▸ seen)
      · exact Or.inr h

private theorem advance_new (catalog : DocumentCatalog) (root key : U32) (tail pending : DocumentIds)
    (available resolved remaining : DocumentCatalog) (b : alloc.vec.Vec U8) (im : DocumentIds)
    (inv : Invariant catalog root (.Cons key tail) available resolved)
    (taken : (rows available).Perm ((key, b, im) :: rows remaining))
    (hp : ids pending = ids im ++ ids tail) :
    Invariant catalog root pending remaining (.Document key b im resolved) := by
  have rowOrig : (key, b, im) ∈ rows catalog := by
    apply inv.partition.mem_iff.mp
    exact List.mem_append_left _ (taken.mem_iff.mpr (by simp))
  have keyReach : Reachable catalog root key := inv.pendingReachable key (by simp [ids])
  have moveFrontier (target : U32) (h : target ∈ keys resolved ∨ target ∈ ids (.Cons key tail)) :
      target ∈ keys (.Document key b im resolved) ∨ target ∈ ids pending := by
    rcases h with h | h
    · exact Or.inl (by rw [keys_cons]; exact List.mem_cons_of_mem _ h)
    · rcases (List.mem_cons.mp h) with h | h
      · exact Or.inl (by rw [keys_cons]; exact List.mem_cons.mpr (Or.inl h))
      · exact Or.inr (by rw [hp]; exact List.mem_append_right _ h)
  refine ⟨?_, ?_, ?_, moveFrontier root inv.rootFrontier, ?_⟩
  · have moved := taken.append_right (rows resolved)
    have reorder : (((key, b, im) :: rows remaining) ++ rows resolved).Perm
        (rows remaining ++ (key, b, im) :: rows resolved) := List.perm_middle.symm
    exact (moved.trans reorder).symm.trans inv.partition
  · intro target ht
    rw [hp] at ht
    rcases List.mem_append.mp ht with h | h
    · exact keyReach.tail ⟨b, im, rowOrig, h⟩
    · exact inv.pendingReachable target (by simp [ids, h])
  · intro target ht
    rw [keys_cons] at ht
    rcases List.mem_cons.mp ht with h | h
    · exact h ▸ keyReach
    · exact inv.resolvedReachable target h
  · intro source bytes imports hm target ht
    change (source, bytes, imports) ∈ (key, b, im) :: rows resolved at hm
    rcases List.mem_cons.mp hm with h | h
    · cases h
      exact Or.inr (by rw [hp]; exact List.mem_append_left _ ht)
    · exact moveFrontier target (inv.edgeFrontier source bytes imports h target ht)

private theorem discover_correct (catalog : DocumentCatalog) (root : U32)
    (unique : (keys catalog).Nodup) (pending : DocumentIds) (available resolved : DocumentCatalog)
    (inv : Invariant catalog root pending available resolved) :
    ∃ result, discover pending available resolved = .ok result ∧ Correct catalog root result := by
  cases pending with
  | Empty => exact ⟨.Complete resolved, by simp [discover], finish catalog root available resolved unique inv⟩
  | Cons key tail =>
    have hc := contains_correct resolved key
    by_cases seen : key ∈ keys resolved
    · obtain ⟨result, hr, hs⟩ := discover_correct catalog root unique tail available resolved
        (advance_seen catalog root key tail available resolved inv seen)
      exact ⟨result, by simp [discover, hc, seen, hr], hs⟩
    · obtain ⟨taken, ht, ts⟩ := take_correct available key
      cases taken with
      | Missing =>
        refine ⟨.MissingDocument key, by simp [discover, hc, seen, ht], ?_⟩
        refine ⟨inv.pendingReachable key (by simp [ids]), ?_⟩
        intro hm
        obtain ⟨b, im, hrow⟩ := (mem_keys catalog key).mp hm
        have hp := inv.partition.mem_iff.mpr hrow
        rcases List.mem_append.mp hp with ha | hr
        · exact ts ((mem_keys available key).mpr ⟨b, im, ha⟩)
        · exact seen ((mem_keys resolved key).mpr ⟨b, im, hr⟩)
      | Found b im remaining =>
        obtain ⟨next, hn, hl⟩ := append_correct im tail
        have nextInv := advance_new catalog root key tail next available resolved remaining b im inv ts hl
        obtain ⟨result, hr, hs⟩ := discover_correct catalog root unique next remaining
          (.Document key b im resolved) nextInv
        exact ⟨result, by simp [discover, hc, seen, ht, copy_correct, hn, hr], hs⟩
termination_by ((rows available).length, (ids pending).length)
decreasing_by
  · simp_all [ids]
  · have len := ts.length_eq
    change (rows available).length = ((key, b, im) :: rows remaining).length at len
    simp only [List.length_cons] at len
    simp_wf
    omega

/-- Actual Rust closure discovery is total and returns exactly the graph closure.
    Cycles do not require fuel. Document bytes and edge metadata are preserved. -/
theorem resolve_total_correct (root : U32) (catalog : DocumentCatalog) :
    ∃ result, resolve root catalog = .ok result ∧ Correct catalog root result := by
  obtain ⟨dup, hd, unique, count⟩ := duplicate_correct catalog
  cases dup with
  | some key => exact ⟨.DuplicateDocument key, by simp [resolve, hd], count key rfl⟩
  | none =>
    have inv : Invariant catalog root (.Cons root .Empty) catalog .Empty := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [rows]
      · intro key hk
        have same : key = root := by simpa [ids] using hk
        subst key
        exact Relation.ReflTransGen.refl
      · simp [keys, rows]
      · simp [ids]
      · simp [rows]
    obtain ⟨result, hr, hs⟩ := discover_correct catalog root (unique.mp rfl) _ _ _ inv
    exact ⟨result, by simp [resolve, hd, hr], hs⟩

/-- Complete discovery is possible exactly when the catalog is unambiguous and
    every reachable document is present. Missing imports are never ignored. -/
theorem resolve_complete_iff (root : U32) (catalog : DocumentCatalog) :
    (∃ closure, resolve root catalog = .ok (.Complete closure)) ↔
      (keys catalog).Nodup ∧ ∀ key, Reachable catalog root key → key ∈ keys catalog := by
  constructor
  · rintro ⟨closure, hc⟩
    obtain ⟨dup, hd, hn, _⟩ := duplicate_correct catalog
    have unique : (keys catalog).Nodup := by
      cases dup with
      | none => exact hn.mp rfl
      | some key => simp [resolve, hd] at hc
    obtain ⟨result, hr, hs⟩ := resolve_total_correct root catalog
    have same := Result.ok_injective (hr.symm.trans hc)
    rw [same] at hs
    refine ⟨unique, ?_⟩
    intro key reach
    obtain ⟨b, im, hm⟩ := (mem_keys closure key).mp ((hs.2.2 key).mpr reach)
    exact (mem_keys catalog key).mpr ⟨b, im, hs.2.1 _ hm⟩
  · rintro ⟨unique, present⟩
    obtain ⟨result, hr, hs⟩ := resolve_total_correct root catalog
    cases result with
    | Complete closure => exact ⟨closure, hr⟩
    | MissingDocument key => exact False.elim (hs.2 (present key hs.1))
    | DuplicateDocument key =>
      have upper := List.nodup_iff_count_le_one.mp unique key
      change 2 ≤ (keys catalog).count key at hs
      omega

/-- Actual recursion reaches a result without a user-supplied fuel bound. -/
theorem resolve_terminates (root : U32) (catalog : DocumentCatalog) :
    ∃ result, resolve root catalog = .ok result := by
  obtain ⟨result, hr, _⟩ := resolve_total_correct root catalog
  exact ⟨result, hr⟩

end Rowl.Imports
