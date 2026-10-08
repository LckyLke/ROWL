import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.MinMax

/-!
Counting the words of a regular language over a large alphabet. The letters
(code points) fall into finitely many atoms, disjoint finite sets of known
sizes, and a finite automaton reads each letter by its atom (`Dfa`,
`Dfa.Accepts`). The words of each length that an automaton accepts from a state
form a finite set (`Dfa.words`) whose number is the sum, over the atoms, of the
atom's size times the number of words one letter shorter from the state the
atom leads to (`Dfa.count`, `words_card`). Capped at a bound, these numbers
obey the same recurrence with every sum and product capped (`capped_count`),
which is what the kernel computes with fixed-width numbers; once the capped
numbers of all states repeat, they stay (`steps_fixed`).
-/
namespace Rowl.WordCounts
open Finset

/-! ### Automata over atoms -/

/-- A finite automaton over the atoms `0, …, atoms - 1`, each atom a finite set
    of letters: from each state, each atom leads to a state or nowhere. -/
structure Dfa where
  atoms : ℕ
  atom : ℕ → Finset ℕ
  next : ℕ → ℕ → Option ℕ
  accept : ℕ → Bool

namespace Dfa

/-- The atoms are disjoint. -/
def Disjoint (d : Dfa) : Prop :=
  ∀ a b c, a < d.atoms → b < d.atoms → c ∈ d.atom a → c ∈ d.atom b → a = b

/-- The automaton accepts a word from a state: each letter is in an atom that
    leads on, and the last state accepts. -/
def Accepts (d : Dfa) : ℕ → List ℕ → Prop
  | q, [] => d.accept q = true
  | q, c :: w => ∃ a < d.atoms, c ∈ d.atom a ∧ ∃ q', d.next q a = some q' ∧ d.Accepts q' w

/-- The words of a length that the automaton accepts from a state. -/
def words (d : Dfa) : ℕ → ℕ → Finset (List ℕ)
  | q, 0 => if d.accept q then {[]} else ∅
  | q, ℓ + 1 => (range d.atoms).biUnion fun a =>
      match d.next q a with
      | some q' => (d.atom a).biUnion fun c => (d.words q' ℓ).image (c :: ·)
      | none => ∅

/-- The number of the words of a length that the automaton accepts from a
    state. -/
def count (d : Dfa) : ℕ → ℕ → ℕ
  | q, 0 => if d.accept q then 1 else 0
  | q, ℓ + 1 => ∑ a ∈ range d.atoms, (d.atom a).card *
      match d.next q a with
      | some q' => d.count q' ℓ
      | none => 0

end Dfa

open Dfa (Accepts words count)

theorem mem_words (d : Dfa) (q ℓ : ℕ) (w : List ℕ) : w ∈ d.words q ℓ ↔ w.length = ℓ ∧ d.Accepts q w := by
  induction ℓ generalizing q w with
  | zero =>
    cases w with
    | nil => by_cases h : d.accept q <;> simp [words, Accepts, h]
    | cons c w => by_cases h : d.accept q <;> simp [words, h]
  | succ ℓ ih =>
    cases w with
    | nil =>
      simp only [words, mem_biUnion, mem_range, List.length_nil, Nat.zero_ne_add_one, false_and, iff_false,
        not_exists, not_and]
      intro a _
      cases d.next q a <;> simp
    | cons c w =>
      simp only [words, mem_biUnion, mem_range, List.length_cons, Nat.add_right_cancel_iff, Accepts]
      constructor
      · rintro ⟨a, ha, inA⟩
        cases hn : d.next q a with
        | none => simp [hn] at inA
        | some q' =>
          simp only [hn, mem_biUnion, mem_image] at inA
          obtain ⟨c', hc', w', hw', same⟩ := inA
          simp only [List.cons.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          obtain ⟨len, acc⟩ := (ih q' w').mp hw'
          exact ⟨len, a, ha, hc', q', hn, acc⟩
      · rintro ⟨len, a, ha, hc, q', hn, acc⟩
        refine ⟨a, ha, ?_⟩
        simp only [hn, mem_biUnion, mem_image]
        exact ⟨c, hc, w, (ih q' w).mpr ⟨len, acc⟩, rfl⟩

theorem words_card (d : Dfa) (disjoint : d.Disjoint) (q ℓ : ℕ) : (d.words q ℓ).card = d.count q ℓ := by
  induction ℓ generalizing q with
  | zero => by_cases h : d.accept q <;> simp [words, count, h]
  | succ ℓ ih =>
    simp only [words, count]
    rw [card_biUnion]
    · apply sum_congr rfl
      intro a _
      cases hn : d.next q a with
      | none => simp
      | some q' =>
        simp only
        rw [card_biUnion]
        · rw [sum_congr rfl fun c _ => card_image_of_injective _ (List.cons_injective (a := c)), ih q']
          simp
        · intro c _ c' _ ne
          simp only [Function.onFun, Finset.disjoint_left, mem_image]
          rintro _ ⟨w, _, rfl⟩ ⟨w', _, same⟩
          simp only [List.cons.injEq] at same
          exact ne same.1.symm
    · intro a ha b hb ne
      simp only [Function.onFun, Finset.disjoint_left]
      intro w inA inB
      cases hna : d.next q a with
      | none => simp [hna] at inA
      | some qa =>
        cases hnb : d.next q b with
        | none => simp [hnb] at inB
        | some qb =>
          simp only [hna, hnb, mem_biUnion, mem_image] at inA inB
          obtain ⟨c, hc, w1, _, rfl⟩ := inA
          obtain ⟨c', hc', w2, _, same⟩ := inB
          simp only [List.cons.injEq] at same
          rw [same.1] at hc'
          exact ne (disjoint a b c (by simpa using ha) (by simpa using hb) hc hc')

/-- The number of the words of a length that the automaton accepts from a
    state is the number of its words. -/
theorem accepted_ncard (d : Dfa) (disjoint : d.Disjoint) (q ℓ : ℕ) :
    {w : List ℕ | w.length = ℓ ∧ d.Accepts q w}.ncard = d.count q ℓ := by
  rw [← words_card d disjoint q ℓ, ← Set.ncard_coe_finset]
  congr 1
  ext w
  simp [mem_words]

theorem accepted_finite (d : Dfa) (q ℓ : ℕ) : {w : List ℕ | w.length = ℓ ∧ d.Accepts q w}.Finite := by
  apply (d.words q ℓ).finite_toSet.subset
  intro w hw
  simpa [mem_words] using hw


/-! ### Capped numbers -/

/-- A number capped at a bound. -/
def capAt (cap n : ℕ) : ℕ := min cap n

theorem capAt_add (cap a b : ℕ) : capAt cap (a + b) = capAt cap (capAt cap a + capAt cap b) := by
  unfold capAt; omega

theorem capAt_mul (cap a b : ℕ) : capAt cap (a * b) = capAt cap (a * capAt cap b) := by
  unfold capAt
  rcases le_total b cap with h | h
  · rw [min_eq_right h]
  · rw [min_eq_left h]
    rcases Nat.eq_zero_or_pos a with rfl | pos
    · simp
    · have : cap ≤ a * cap := Nat.le_mul_of_pos_left cap pos
      have : a * cap ≤ a * b := Nat.mul_le_mul_left a h
      omega

theorem capAt_sum {ι : Type*} (cap : ℕ) (s : Finset ι) (f : ι → ℕ) :
    capAt cap (∑ i ∈ s, f i) = capAt cap (∑ i ∈ s, capAt cap (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s notIn ih =>
    rw [sum_insert notIn, sum_insert notIn, capAt_add, ih, ← capAt_add]
    unfold capAt; omega

theorem capAt_capAt (cap n : ℕ) : capAt cap (capAt cap n) = capAt cap n := by
  unfold capAt; omega

namespace Dfa

/-- The capped numbers of the words of each length, one length after the
    other: each capped sum of the atoms' sizes times the capped numbers one
    letter shorter. -/
def capStep (d : Dfa) (cap : ℕ) (v : ℕ → ℕ) (q : ℕ) : ℕ :=
  capAt cap (∑ a ∈ range d.atoms, (d.atom a).card *
    match d.next q a with
    | some q' => v q'
    | none => 0)

/-- The capped numbers of the words of length `ℓ` from every state. -/
def capCounts (d : Dfa) (cap : ℕ) : ℕ → ℕ → ℕ
  | 0, q => capAt cap (if d.accept q then 1 else 0)
  | ℓ + 1, q => d.capStep cap (d.capCounts cap ℓ) q

end Dfa

open Dfa (capStep capCounts)

theorem capped_count (d : Dfa) (cap ℓ q : ℕ) : d.capCounts cap ℓ q = capAt cap (d.count q ℓ) := by
  induction ℓ generalizing q with
  | zero => rfl
  | succ ℓ ih =>
    simp only [capCounts, capStep, count]
    conv_lhs => rw [capAt_sum]
    conv_rhs => rw [capAt_sum]
    congr 1
    apply sum_congr rfl
    intro a _
    cases d.next q a with
    | none => rfl
    | some q' =>
      simp only [ih q']
      rw [← capAt_mul]

/-- Once the capped numbers of all states repeat, they stay. -/
theorem steps_fixed (d : Dfa) (cap ℓ : ℕ) (fixed : ∀ q, d.capCounts cap (ℓ + 1) q = d.capCounts cap ℓ q) :
    ∀ m, ℓ ≤ m → ∀ q, d.capCounts cap m q = d.capCounts cap ℓ q := by
  intro m le
  induction m, le using Nat.le_induction with
  | base => intro q; rfl
  | succ m le ih =>
    intro q
    have same : d.capCounts cap m = d.capCounts cap ℓ := funext ih
    show d.capStep cap (d.capCounts cap m) q = d.capCounts cap ℓ q
    rw [same]
    exact fixed q

/-- The capped number from a state depends only on the numbers at the states
    its atoms lead to. -/
theorem capStep_congr (d : Dfa) (cap : ℕ) {v v' : ℕ → ℕ} (q : ℕ)
    (agree : ∀ a < d.atoms, ∀ q', d.next q a = some q' → v q' = v' q') :
    d.capStep cap v q = d.capStep cap v' q := by
  unfold capStep
  congr 1
  apply sum_congr rfl
  intro a ha
  rw [mem_range] at ha
  cases h : d.next q a with
  | none => rfl
  | some q' => simp only; rw [agree a ha q' h]

/-- Once the capped numbers of the states of a set closed under the atoms
    repeat, they stay. -/
theorem steps_fixed_on (d : Dfa) (cap ℓ : ℕ) (S : ℕ → Prop)
    (closed : ∀ q, S q → ∀ a < d.atoms, ∀ q', d.next q a = some q' → S q')
    (fixed : ∀ q, S q → d.capCounts cap (ℓ + 1) q = d.capCounts cap ℓ q) :
    ∀ m, ℓ ≤ m → ∀ q, S q → d.capCounts cap m q = d.capCounts cap ℓ q := by
  intro m le
  induction m, le using Nat.le_induction with
  | base => intro q _; rfl
  | succ m le ih =>
    intro q hq
    show d.capStep cap (d.capCounts cap m) q = d.capCounts cap ℓ q
    rw [capStep_congr d cap q (v' := d.capCounts cap ℓ) (fun a ha q' h => ih q' (closed q hq a ha q' h))]
    exact fixed q hq


/-- A number capped and added to is the sum capped. -/
theorem capAt_add_left (cap a b : ℕ) : capAt cap (capAt cap a + b) = capAt cap (a + b) := by
  unfold capAt; omega

theorem capAt_add_right (cap a b : ℕ) : capAt cap (a + capAt cap b) = capAt cap (a + b) := by
  unfold capAt; omega

end Rowl.WordCounts
