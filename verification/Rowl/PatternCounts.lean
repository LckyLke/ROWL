import Rowl.LengthCounts
import Rowl.Compiled
import Rowl.Patterns
import Mathlib.Data.Set.Card

/-!
The kernel's counting of the strings of combinations of regular expressions
(`pattern_counts.rs`).

Atoms. The XML characters fall into the intervals of the nine atoms of
`Rowl.StringCounts` (`baseTriples`, `base_partition`), which the kernel cuts
wherever an interval node of the compiled expressions begins and after it ends
(`splitOne`, `refine_spec`): the atoms still cover exactly the XML characters,
apart from each other, each within one base atom (`Partition`), and no interval
node begins or ends inside an atom (`Cut`), so that two characters of one atom
are in the same interval nodes (`interval_same`, `NodesCut`).

Alike on atoms. Every language of a node, a continuation stack or a state of
stacks has a word exactly when it has the words whose letters are, one by one,
in the same atoms (`Uniform`, `stateLang_uniform`), so the words after a
character are those after the first character of its atom (`after_same`).

Joint states. A joint state stands for its strings' state and the languages of
its stack states (`meaning`); a step by an atom moves the strings' state by the
base atom and each language to the words after the atom's first character
(`joint_step_spec`, `afterAtom`). Joint states with the same strings' state and
stacks that are the same sets stand for the same (`same_joint_spec`), and the
exploration gives every reached state a row of next states that agree with it
(`row_spec`, `explore_spec`, `RowsAgree`), so that the kernel's automaton is
`Built` from the expressions (`automaton_spec`).

Words. From the first joint state, the automaton of the joint states takes a
word to a state where exactly the expressions of a profile accept and the rank
is in a range exactly when the word's letters are XML characters, its rank, as
the automaton of the strings reads it, is in the range and exactly those
expressions have it (`joint_accepts`, `profile_accepts`, `ProfileWord`).

Counts. The kernel's capped counts follow the capped numbers of words of each
length one length after the other (`initial_from_spec`, `step_from_spec`), and
stop once their sum reaches the cap, the lengths reach the slot's end, or the
numbers repeat (`count_from_spec`); so `pattern_counts::profile_count` gives the
capped number of the words of a profile with lengths in a slot, or, for a slot
without end, the value at which these capped numbers settle
(`profile_count_words`).
-/
namespace Rowl.PatternCounts
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open Rowl.WordCounts Rowl.StringCounts
open Rowl.Compiled (lang stackLang stateLang Flagged After)
open Rowl.Patterns (add_one usize_big new_val)
open Rowl.LengthCounts (countsOf countsOf_push tail_sum capAt_add_congr capped_sum_spec capped_product_spec)
open scoped Computability
attribute [local instance low] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-! ### Atoms -/

/-- An atom as its first and last code point and its base atom. -/
def triple (a : pattern_counts.Atom) : ℕ × ℕ × ℕ := (a.lower.val, a.upper.val, a.base.val)

/-- The code points of an atom. -/
def InT (t : ℕ × ℕ × ℕ) (c : ℕ) : Prop := t.1 ≤ c ∧ c ≤ t.2.1

/-- Atoms of the XML characters: together they hold exactly the XML characters,
    each lies within the base atom it names, no two share a character, and each
    ends before `#x110000`. -/
structure Partition (ts : List (ℕ × ℕ × ℕ)) : Prop where
  cover : ∀ c, Rowl.Unicode.XmlChar c ↔ ∃ t ∈ ts, InT t c
  based : ∀ t ∈ ts, t.2.2 < 9 ∧ ∀ c, InT t c → atomOf c = t.2.2
  apart : ts.Pairwise (fun t u => ∀ c, InT t c → ¬ InT u c)
  bounded : ∀ t ∈ ts, t.2.1 < 1114112

/-- No atom holds both the code point before `x` and `x`. -/
def Cut (ts : List (ℕ × ℕ × ℕ)) (x : ℕ) : Prop := ∀ t ∈ ts, ¬ (t.1 < x ∧ x ≤ t.2.1)

/-- The intervals of the nine base atoms, each with its base atom. -/
def baseTriples : List (ℕ × ℕ × ℕ) :=
  (List.range 9).flatMap fun a => (atomRanges a).map fun r => (r.1, r.2, a)

theorem ascending_mem : ∀ {rs : List (ℕ × ℕ)}, Ascending rs = true → ∀ r ∈ rs, r.1 ≤ r.2
  | [], _, r, mem => by simp at mem
  | s :: rs, h, r, mem => by
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact ascending_head h
    · exact ascending_mem (ascending_tail h) r mem

theorem ascending_pairwise : ∀ {rs : List (ℕ × ℕ)}, Ascending rs = true → rs.Pairwise (fun r s => r.2 < s.1)
  | [], _ => List.Pairwise.nil
  | _ :: rs, h => List.Pairwise.cons
      (fun s mem => ascending_above h ((mem_rangeSet rs s.1).mpr
        ⟨s, mem, le_rfl, ascending_mem (ascending_tail h) s mem⟩))
      (ascending_pairwise (ascending_tail h))

theorem atom_ascending (a : ℕ) (ha : a < 9) : Ascending (atomRanges a) = true := by
  match a, ha with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ => decide

theorem mem_baseTriples {t : ℕ × ℕ × ℕ} :
    t ∈ baseTriples ↔ ∃ a < 9, ∃ r ∈ atomRanges a, t = (r.1, r.2, a) := by
  simp only [baseTriples, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨a, ha, r, hr, rfl⟩; exact ⟨a, ha, r, hr, rfl⟩
  · rintro ⟨a, ha, r, hr, rfl⟩; exact ⟨a, ha, r, hr, rfl⟩

theorem range_bounded (a : ℕ) (ha : a < 9) : ∀ r ∈ atomRanges a, r.2 < 1114112 := by
  match a, ha with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ => decide

theorem base_partition : Partition baseTriples where
  cover c := by
    constructor
    · intro xml
      obtain ⟨r, hr, lo, hi⟩ := atomOf_spec xml
      exact ⟨(r.1, r.2, atomOf c), mem_baseTriples.mpr ⟨atomOf c, atomOf_lt c, r, hr, rfl⟩, lo, hi⟩
    · rintro ⟨t, mem, lo, hi⟩
      obtain ⟨a, _, r, hr, rfl⟩ := mem_baseTriples.mp mem
      exact atom_xml ⟨r, hr, lo, hi⟩
  based t mem := by
    obtain ⟨a, ha, r, hr, rfl⟩ := mem_baseTriples.mp mem
    refine ⟨ha, fun c ⟨lo, hi⟩ => ?_⟩
    have inside : InRanges (atomRanges a) c := ⟨r, hr, lo, hi⟩
    exact (atom_iff (atom_xml inside) a ha).mp inside
  apart := by
    rw [baseTriples, List.pairwise_flatMap]
    refine ⟨fun a ha => ?_, ?_⟩
    · rw [List.pairwise_map]
      have := ascending_pairwise (atom_ascending a (List.mem_range.mp ha))
      refine this.imp fun {r s} lt c hc hs => ?_
      simp only [InT] at hc hs
      omega
    · refine (List.pairwise_lt_range (n := 9)).imp_of_mem fun {a b} ma mb lt t ht u hu c hc hu' => ?_
      have ha := List.mem_range.mp ma
      have hb := List.mem_range.mp mb
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hu
      have inR : InRanges (atomRanges a) c := ⟨r, hr, hc⟩
      have inS : InRanges (atomRanges b) c := ⟨s, hs, hu'⟩
      have xml := atom_xml inR
      have ea := (atom_iff xml a ha).mp inR
      have eb := (atom_iff xml b hb).mp inS
      omega
  bounded t mem := by
    obtain ⟨a, ha, r, hr, rfl⟩ := mem_baseTriples.mp mem
    exact range_bounded a ha r hr

/-! ### Cutting atoms -/

/-- An atom cut in two where `x` falls after its first code point. -/
def splitOne (x : ℕ) (t : ℕ × ℕ × ℕ) : List (ℕ × ℕ × ℕ) :=
  if t.1 < x ∧ x ≤ t.2.1 then [(t.1, x - 1, t.2.2), (x, t.2.1, t.2.2)] else [t]

theorem splitOne_cover (x : ℕ) (t : ℕ × ℕ × ℕ) (c : ℕ) : (∃ u ∈ splitOne x t, InT u c) ↔ InT t c := by
  unfold splitOne InT
  split_ifs with h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    omega
  · simp

theorem splitOne_within {x : ℕ} {t u : ℕ × ℕ × ℕ} (h : u ∈ splitOne x t) :
    t.1 ≤ u.1 ∧ u.2.1 ≤ t.2.1 ∧ u.2.2 = t.2.2 := by
  unfold splitOne at h
  split_ifs at h with hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> (simp; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    simp

theorem splitOne_apart (x : ℕ) (t : ℕ × ℕ × ℕ) :
    (splitOne x t).Pairwise (fun t u => ∀ c, InT t c → ¬ InT u c) := by
  unfold splitOne
  split_ifs with h
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, InT,
      List.Pairwise.nil, and_true, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true]
    intro c hc
    omega
  · simp

theorem split_partition {ts : List (ℕ × ℕ × ℕ)} (h : Partition ts) (x : ℕ) :
    Partition (ts.flatMap (splitOne x)) where
  cover c := by
    rw [h.cover c]
    simp only [List.mem_flatMap]
    constructor
    · rintro ⟨t, mem, ht⟩
      obtain ⟨u, hu, inU⟩ := (splitOne_cover x t c).mpr ht
      exact ⟨u, ⟨t, mem, hu⟩, inU⟩
    · rintro ⟨u, ⟨t, mem, hu⟩, inU⟩
      exact ⟨t, mem, (splitOne_cover x t c).mp ⟨u, hu, inU⟩⟩
  based u mem := by
    obtain ⟨t, tm, hu⟩ := List.mem_flatMap.mp mem
    obtain ⟨lo, hi, base⟩ := splitOne_within hu
    obtain ⟨lt, same⟩ := h.based t tm
    refine ⟨base ▸ lt, fun c hc => ?_⟩
    rw [base]
    exact same c ⟨by simp only [InT] at hc; omega, by simp only [InT] at hc; omega⟩
  apart := by
    rw [List.pairwise_flatMap]
    refine ⟨fun t _ => splitOne_apart x t, h.apart.imp fun {t s} apart u hu v hv c hc hv' => ?_⟩
    obtain ⟨lo, hi, _⟩ := splitOne_within hu
    obtain ⟨lo', hi', _⟩ := splitOne_within hv
    simp only [InT] at hc hv'
    exact apart c ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  bounded u mem := by
    obtain ⟨t, tm, hu⟩ := List.mem_flatMap.mp mem
    have := (splitOne_within hu).2.1
    have := h.bounded t tm
    omega

theorem split_cut (ts : List (ℕ × ℕ × ℕ)) (x : ℕ) : Cut (ts.flatMap (splitOne x)) x := by
  intro u mem
  obtain ⟨t, _, hu⟩ := List.mem_flatMap.mp mem
  unfold splitOne at hu
  split_ifs at hu with hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> (simp; try omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    subst hu
    exact hx

theorem split_keeps {ts : List (ℕ × ℕ × ℕ)} {y : ℕ} (h : Cut ts y) (x : ℕ) : Cut (ts.flatMap (splitOne x)) y := by
  intro u mem
  obtain ⟨t, tm, hu⟩ := List.mem_flatMap.mp mem
  obtain ⟨lo, hi, _⟩ := splitOne_within hu
  have := h t tm
  unfold splitOne at hu
  split_ifs at hu with hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> (simp at lo hi ⊢; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    subst hu
    exact this

/-- Two code points of one atom, with no cut at the first code point of an
    interval or after its last, are both in it or both outside it. -/
theorem interval_same {t : ℕ × ℕ × ℕ} {ts : List (ℕ × ℕ × ℕ)} (mem : t ∈ ts) (bounded : t.2.1 < 1114112)
    {lo hi : ℕ} (cutLo : Cut ts lo) (cutHi : Cut ts (min (hi + 1) 1114112)) {c c' : ℕ}
    (hc : InT t c) (hc' : InT t c') : (lo ≤ c ∧ c ≤ hi) ↔ (lo ≤ c' ∧ c' ≤ hi) := by
  have l := cutLo t mem
  have h := cutHi t mem
  simp only [InT] at hc hc'
  constructor
  · intro ⟨a, b⟩
    constructor
    · by_contra lt; exact l ⟨by omega, by omega⟩
    · by_contra gt
      exact h ⟨by omega, by omega⟩
  · intro ⟨a, b⟩
    constructor
    · by_contra lt; exact l ⟨by omega, by omega⟩
    · by_contra gt
      exact h ⟨by omega, by omega⟩

/-! ### The kernel's atoms -/

theorem atom_eq (l u : U32) (b : Usize) : pattern_counts.atom l u b = .ok ⟨l, u, b⟩ := rfl

theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by simp [core.num.Usize.MAX]

theorem split_from_spec (atoms : alloc.vec.Vec pattern_counts.Atom) (cut : U32) (index : Usize)
    (out : alloc.vec.Vec pattern_counts.Atom) :
    ∃ r, pattern_counts.split_from atoms cut index out = .ok r ∧ ∀ v, r = some v →
      v.val.map triple = out.val.map triple ++ (atoms.val.drop index.val).flatMap (fun a => splitOne cut.val (triple a)) := by
  rw [pattern_counts.split_from]
  have big := usize_big
  by_cases inside : index.val < atoms.val.length
  · have lookup : atoms.index_usize index = .ok atoms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := add_one inside atoms.property
    have drop : atoms.val.drop index.val = atoms.val[index.val] :: atoms.val.drop next.val := by
      rw [nextValue, List.drop_eq_getElem_cons inside]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, UScalar.le_equiv, inside, ↓reduceIte,
      alloc.vec.Vec.index_slice_index, lookup, bind_ok]
    by_cases straddle : atoms.val[index.val].lower.val < cut.val ∧ cut.val ≤ atoms.val[index.val].upper.val
    · have cond : (decide (atoms.val[index.val].lower.val < cut.val) &&
          decide (cut.val ≤ atoms.val[index.val].upper.val)) = true := by
        simp [straddle.1, straddle.2]
      simp only [cond, ↓reduceIte]
      obtain ⟨m, mRun, mVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := core.num.Usize.MAX) (y := 1#usize)
        (by simp [usize_max_val]; omega))
      have mv : m.val = Usize.max - 1 := by simp [usize_max_val] at mVal; omega
      simp only [mRun, bind_ok]
      by_cases room : out.val.length < Usize.max - 1
      · obtain ⟨c1, c1Run, c1Val⟩ := WP.spec_imp_exists (U32.sub_spec (x := cut) (y := 1#u32) (by simp; omega))
        obtain ⟨out1, push1, contents1⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out
          ⟨atoms.val[index.val].lower, c1, atoms.val[index.val].base⟩ (by omega))
        obtain ⟨out2, push2, contents2⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out1
          ⟨cut, atoms.val[index.val].upper, atoms.val[index.val].base⟩ (by rw [contents1]; simp; omega))
        obtain ⟨r, run, spec⟩ := split_from_spec atoms cut next out2
        refine ⟨r, ?_, ?_⟩
        · simp only [UScalar.lt_equiv, mv, room, decide_true, ↓reduceIte, c1Run, atom_eq, push1, push2, advance,
            bind_ok, run]
        · intro v hv
          rw [spec v hv, contents2, contents1, drop]
          have c1v : c1.val = cut.val - 1 := by simp at c1Val; omega
          simp [triple, splitOne, straddle, c1v]
      · refine ⟨none, ?_, by simp⟩
        simp [UScalar.lt_equiv, mv, room]
    · have cond : (decide (atoms.val[index.val].lower.val < cut.val) &&
          decide (cut.val ≤ atoms.val[index.val].upper.val)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        omega
      simp only [cond, Bool.false_eq_true, ↓reduceIte]
      by_cases room : out.val.length < Usize.max
      · obtain ⟨out1, push1, contents1⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out
          ⟨atoms.val[index.val].lower, atoms.val[index.val].upper, atoms.val[index.val].base⟩ room)
        obtain ⟨r, run, spec⟩ := split_from_spec atoms cut next out1
        refine ⟨r, ?_, ?_⟩
        · simp only [UScalar.lt_equiv, usize_max_val, room, decide_true, ↓reduceIte, atom_eq, push1, advance,
            bind_ok, run]
        · intro v hv
          rw [spec v hv, contents1, drop]
          simp [triple, splitOne, straddle]
      · refine ⟨none, ?_, by simp⟩
        simp [UScalar.lt_equiv, usize_max_val, room]
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], ?_⟩
    intro v hv
    simp only [Option.some.injEq] at hv
    subst hv
    simp [List.drop_eq_nil_iff.mpr (show atoms.val.length ≤ index.val by omega)]
termination_by atoms.val.length - index.val
decreasing_by all_goals omega

theorem end_val : pattern_counts.END.val = 1114112 := by simp [pattern_counts.END]

theorem refine_spec (nodes : alloc.vec.Vec compiled.Node) (index : Usize) (atoms : alloc.vec.Vec pattern_counts.Atom)
    (part : Partition (atoms.val.map triple)) :
    ∃ r, pattern_counts.refine nodes index atoms = .ok r ∧ ∀ v, r = some v →
      Partition (v.val.map triple) ∧ (∀ y, Cut (atoms.val.map triple) y → Cut (v.val.map triple) y) ∧
      ∀ j (hj : j < nodes.val.length), index.val ≤ j → ∀ lo hi, (nodes.val[j]).kind = .Interval lo hi →
        Cut (v.val.map triple) lo.val ∧ Cut (v.val.map triple) (min (hi.val + 1) 1114112) := by
  rw [pattern_counts.refine]
  by_cases inside : index.val < nodes.val.length
  · have lookup : nodes.index_usize index = .ok nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := add_one inside nodes.property
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
      bind_ok]
    have later : ∀ (ts : alloc.vec.Vec pattern_counts.Atom), Partition (ts.val.map triple) →
        (∀ y, Cut (atoms.val.map triple) y → Cut (ts.val.map triple) y) →
        (∀ lo hi, (nodes.val[index.val]).kind = .Interval lo hi →
          Cut (ts.val.map triple) lo.val ∧ Cut (ts.val.map triple) (min (hi.val + 1) 1114112)) →
        ∃ r, pattern_counts.refine nodes next ts = .ok r ∧ ∀ v, r = some v →
          Partition (v.val.map triple) ∧ (∀ y, Cut (atoms.val.map triple) y → Cut (v.val.map triple) y) ∧
          ∀ j (hj : j < nodes.val.length), index.val ≤ j → ∀ lo hi, (nodes.val[j]).kind = .Interval lo hi →
            Cut (v.val.map triple) lo.val ∧ Cut (v.val.map triple) (min (hi.val + 1) 1114112) := by
      intro ts tsPart tsKeeps tsHere
      obtain ⟨r, run, spec⟩ := refine_spec nodes next ts tsPart
      refine ⟨r, run, fun v hv => ?_⟩
      obtain ⟨vPart, vKeeps, vCuts⟩ := spec v hv
      refine ⟨vPart, fun y hy => vKeeps y (tsKeeps y hy), fun j hj le lo hi kind => ?_⟩
      by_cases here : j = index.val
      · subst here
        obtain ⟨c1, c2⟩ := tsHere lo hi kind
        exact ⟨vKeeps _ c1, vKeeps _ c2⟩
      · exact vCuts j hj (by omega) lo hi kind
    cases hk : (nodes.val[index.val]).kind with
    | Interval lo hi =>
      obtain ⟨e1, e1Run, e1Val⟩ := WP.spec_imp_exists (U32.sub_spec (x := pattern_counts.END) (y := 1#u32)
        (by simp [end_val]))
      have e1v : e1.val = 1114111 := by simp [end_val] at e1Val; omega
      obtain ⟨after, afterRun, afterVal⟩ : ∃ after : U32,
          (if hi.val < e1.val then hi + 1#u32 else ok pattern_counts.END) = ok after ∧
            after.val = min (hi.val + 1) 1114112 := by
        by_cases small : hi.val < 1114111
        · obtain ⟨a, aRun, aVal⟩ := WP.spec_imp_exists (U32.add_spec (x := hi) (y := 1#u32)
            (by have := small; scalar_tac))
          refine ⟨a, by simp [e1v, small, aRun], ?_⟩
          simp at aVal
          omega
        · refine ⟨pattern_counts.END, by simp [e1v, small], ?_⟩
          rw [end_val]
          omega
      obtain ⟨o1, o1Run, o1Spec⟩ := split_from_spec atoms lo 0#usize (alloc.vec.Vec.new pattern_counts.Atom)
      simp only [e1Run, afterRun, o1Run, bind_ok]
      cases o1 with
      | none => exact ⟨none, rfl, by simp⟩
      | some once =>
        have onceVal := o1Spec once rfl
        simp only [new_val, List.map_nil, List.nil_append, show (0#usize : Usize).val = 0 from rfl,
          List.drop_zero] at onceVal
        obtain ⟨o2, o2Run, o2Spec⟩ := split_from_spec once after 0#usize (alloc.vec.Vec.new pattern_counts.Atom)
        simp only [o2Run, bind_ok]
        cases o2 with
        | none => exact ⟨none, rfl, by simp⟩
        | some twice =>
          have twiceVal := o2Spec twice rfl
          simp only [new_val, List.map_nil, List.nil_append, show (0#usize : Usize).val = 0 from rfl,
            List.drop_zero] at twiceVal
          have onceMap : once.val.map triple = (atoms.val.map triple).flatMap (splitOne lo.val) := by
            rw [onceVal, List.flatMap_map]
          have twiceMap : twice.val.map triple = (once.val.map triple).flatMap (splitOne after.val) := by
            rw [twiceVal, List.flatMap_map]
          simp only [advance, bind_ok]
          refine later twice ?_ ?_ ?_
          · rw [twiceMap, onceMap]
            exact split_partition (split_partition part _) _
          · intro y hy
            rw [twiceMap, onceMap]
            exact split_keeps (split_keeps hy _) _
          · intro lo' hi' kind
            rw [hk] at kind
            simp only [compiled.Kind.Interval.injEq] at kind
            obtain ⟨rfl, rfl⟩ := kind
            rw [twiceMap, onceMap]
            refine ⟨split_keeps (split_cut _ _) _, ?_⟩
            rw [← afterVal]
            exact split_cut _ _
    | Empty =>
      simp only [advance, bind_ok]
      exact later atoms part (fun _ h => h) (fun lo hi kind => by rw [hk] at kind; cases kind)
    | Epsilon =>
      simp only [advance, bind_ok]
      exact later atoms part (fun _ h => h) (fun lo hi kind => by rw [hk] at kind; cases kind)
    | Alternative l r =>
      simp only [advance, bind_ok]
      exact later atoms part (fun _ h => h) (fun lo hi kind => by rw [hk] at kind; cases kind)
    | Sequence l r =>
      simp only [advance, bind_ok]
      exact later atoms part (fun _ h => h) (fun lo hi kind => by rw [hk] at kind; cases kind)
    | Repeat b =>
      simp only [advance, bind_ok]
      exact later atoms part (fun _ h => h) (fun lo hi kind => by rw [hk] at kind; cases kind)
  · refine ⟨some atoms, by simp [UScalar.lt_equiv, inside], ?_⟩
    intro v hv
    simp only [Option.some.injEq] at hv
    subst hv
    exact ⟨part, fun _ h => h, fun j hj le => absurd hj (by omega)⟩
termination_by nodes.val.length - index.val
decreasing_by all_goals omega

/-! ### Languages alike on each atom -/

/-- Two code points are the same or in one atom. -/
def SameAtom (ts : List (ℕ × ℕ × ℕ)) (c c' : ℕ) : Prop := c = c' ∨ ∃ t ∈ ts, InT t c ∧ InT t c'

/-- Two words whose letters are, one by one, the same or in one atom. -/
def Similar (ts : List (ℕ × ℕ × ℕ)) (w w' : List ℕ) : Prop := List.Forall₂ (SameAtom ts) w w'

/-- A language with every word similar to one of its words. -/
def Uniform (ts : List (ℕ × ℕ × ℕ)) (L : Language ℕ) : Prop := ∀ w w', Similar ts w w' → w ∈ L → w' ∈ L

theorem sameAtom_symm {ts : List (ℕ × ℕ × ℕ)} {c c' : ℕ} (h : SameAtom ts c c') : SameAtom ts c' c := by
  rcases h with rfl | ⟨t, mem, a, b⟩
  · exact .inl rfl
  · exact .inr ⟨t, mem, b, a⟩

theorem similar_refl (ts : List (ℕ × ℕ × ℕ)) (w : List ℕ) : Similar ts w w := by
  induction w with
  | nil => exact .nil
  | cons c w ih => exact .cons (.inl rfl) ih

theorem similar_symm {ts : List (ℕ × ℕ × ℕ)} {w w' : List ℕ} (h : Similar ts w w') : Similar ts w' w := by
  induction h with
  | nil => exact .nil
  | cons hc _ ih => exact .cons (sameAtom_symm hc) ih

theorem similar_append {ts : List (ℕ × ℕ × ℕ)} :
    ∀ {u v w' : List ℕ}, Similar ts (u ++ v) w' → ∃ u' v', w' = u' ++ v' ∧ Similar ts u u' ∧ Similar ts v v'
  | [], v, w', h => ⟨[], w', rfl, .nil, h⟩
  | c :: u, v, w', h => by
    cases h with
    | cons hc rest =>
      obtain ⟨u', v', rfl, hu, hv⟩ := similar_append rest
      exact ⟨_ :: u', v', rfl, .cons hc hu, hv⟩

theorem uniform_zero (ts : List (ℕ × ℕ × ℕ)) : Uniform ts 0 := fun _ _ _ h => absurd h (Language.notMem_zero _)

theorem uniform_one (ts : List (ℕ × ℕ × ℕ)) : Uniform ts 1 := by
  intro w w' h hw
  rw [Language.mem_one] at hw ⊢
  subst hw
  cases h
  rfl

theorem uniform_add {ts : List (ℕ × ℕ × ℕ)} {L M : Language ℕ} (hL : Uniform ts L) (hM : Uniform ts M) :
    Uniform ts (L + M) := by
  intro w w' h hw
  rcases (Language.mem_add _ _ _).mp hw with hw | hw
  · exact (Language.mem_add _ _ _).mpr (.inl (hL w w' h hw))
  · exact (Language.mem_add _ _ _).mpr (.inr (hM w w' h hw))

theorem uniform_mul {ts : List (ℕ × ℕ × ℕ)} {L M : Language ℕ} (hL : Uniform ts L) (hM : Uniform ts M) :
    Uniform ts (L * M) := by
  intro w w' h hw
  obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp hw
  obtain ⟨u', v', rfl, su, sv⟩ := similar_append h
  exact Language.mem_mul.mpr ⟨u', hL u u' su hu, v', hM v v' sv hv, rfl⟩

theorem uniform_star {ts : List (ℕ × ℕ × ℕ)} {L : Language ℕ} (hL : Uniform ts L) : Uniform ts (L∗) := by
  intro w w' h hw
  obtain ⟨chunks, rfl, good⟩ := Language.mem_kstar.mp hw
  clear hw
  apply Language.mem_kstar.mpr
  induction chunks generalizing w' with
  | nil => cases h; exact ⟨[], rfl, by simp⟩
  | cons first rest ih =>
    simp only [List.flatten_cons] at h
    obtain ⟨u', v', rfl, su, sv⟩ := similar_append h
    obtain ⟨more, eq, good'⟩ := ih v' (fun y m => good y (List.mem_cons_of_mem _ m)) sv
    refine ⟨u' :: more, by simp [eq], fun y m => ?_⟩
    simp only [List.mem_cons] at m
    rcases m with rfl | m
    · exact hL first y su (good first (by simp))
    · exact good' y m

/-- The atoms cut every interval node of a table: two characters of one atom are
    in the same interval nodes. -/
def NodesCut (ts : List (ℕ × ℕ × ℕ)) (nodes : List compiled.Node) : Prop :=
  ∀ i (h : i < nodes.length) lo hi, nodes[i].kind = .Interval lo hi → ∀ t ∈ ts, ∀ c c', InT t c → InT t c' →
    ((lo.val ≤ c ∧ c ≤ hi.val) ↔ (lo.val ≤ c' ∧ c' ≤ hi.val))

theorem uniform_interval {ts : List (ℕ × ℕ × ℕ)} {lo hi : ℕ}
    (same : ∀ t ∈ ts, ∀ c c', InT t c → InT t c' → ((lo ≤ c ∧ c ≤ hi) ↔ (lo ≤ c' ∧ c' ≤ hi))) :
    Uniform ts {w | ∃ c, w = [c] ∧ lo ≤ c ∧ c ≤ hi} := by
  intro w w' h ⟨c, hw, lo', hi'⟩
  subst hw
  cases h with
  | cons hc rest =>
    cases rest
    rcases hc with rfl | ⟨t, mem, a, b⟩
    · exact ⟨c, rfl, lo', hi'⟩
    · exact ⟨_, rfl, (same t mem c _ a b).mp ⟨lo', hi'⟩⟩

theorem lang_uniform {ts : List (ℕ × ℕ × ℕ)} {nodes : List compiled.Node} (cut : NodesCut ts nodes) :
    ∀ i, Uniform ts (lang nodes i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [Rowl.Compiled.lang_eq]
    split
    · exact uniform_zero ts
    · rename_i n hn
      have inside : i < nodes.length := by
        by_contra out
        rw [List.getElem?_eq_none (by omega)] at hn
        cases hn
      have hni : nodes[i] = n := by simpa [List.getElem?_eq_getElem inside] using hn
      have part : ∀ j : Usize, Uniform ts (if _h : j.val < i then lang nodes j.val else 0) := by
        intro j
        split
        · exact ih j.val ‹_›
        · exact uniform_zero ts
      cases hk : n.kind with
      | Empty => exact uniform_zero ts
      | Epsilon => exact uniform_one ts
      | Interval lo hi =>
        exact uniform_interval (cut i inside lo hi (by rw [hni, hk]))
      | Alternative a b => exact uniform_add (part a) (part b)
      | Sequence a b => exact uniform_mul (part a) (part b)
      | Repeat a => exact uniform_star (part a)

theorem stackLang_uniform {ts : List (ℕ × ℕ × ℕ)} {nodes : List compiled.Node} (cut : NodesCut ts nodes)
    (stack : List Usize) : Uniform ts (stackLang nodes stack) := by
  unfold stackLang
  induction stack.reverse with
  | nil => simpa using uniform_one ts
  | cons j rest ih => simpa using uniform_mul (lang_uniform cut j.val) ih

theorem stateLang_uniform {ts : List (ℕ × ℕ × ℕ)} {nodes : List compiled.Node} (cut : NodesCut ts nodes)
    (state : List (alloc.vec.Vec Usize)) : Uniform ts (stateLang nodes state) := by
  unfold stateLang
  induction state with
  | nil => simpa using uniform_zero ts
  | cons s rest ih => simpa using uniform_add (stackLang_uniform cut s.val) ih

/-- The words after two code points of one atom are the same in a language alike
    on each atom. -/
theorem after_same {ts : List (ℕ × ℕ × ℕ)} {L : Language ℕ} (hL : Uniform ts L) {c c' : ℕ}
    (h : SameAtom ts c c') : After L c = After L c' := by
  ext u
  simp only [Rowl.Compiled.mem_after]
  exact ⟨hL _ _ (.cons h (similar_refl ts u)), hL _ _ (.cons (sameAtom_symm h) (similar_refl ts u))⟩

/-! ### Joint states -/

/-- The languages of stack states. -/
def langs (nodes : List compiled.Node) (stks : List (alloc.vec.Vec (alloc.vec.Vec Usize))) : List (Language ℕ) :=
  stks.map fun s => stateLang nodes s.val

/-- What a joint state stands for: its strings' state and the languages of its
    stack states. -/
def meaning (nodes : List compiled.Node) (j : pattern_counts.Joint) : ℕ × List (Language ℕ) :=
  (j.text.val, langs nodes j.«stacks».val)

/-- What a joint state stands for after an atom. -/
def afterAtom (m : ℕ × List (Language ℕ)) (a : pattern_counts.Atom) : ℕ × List (Language ℕ) :=
  (textNext m.1 a.base.val, m.2.map fun L => After L a.lower.val)

theorem lookup_vec {α : Type} {v : alloc.vec.Vec α} {i : Usize} (inside : i.val < v.val.length) :
    v.index_usize i = .ok v.val[i.val] := by
  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]

theorem step_all_spec (nodes : alloc.vec.Vec compiled.Node) (flagged : Flagged nodes.val)
    (stks : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec Usize))) (index : Usize) (cp : U32)
    (out : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec Usize))) :
    ∃ r, pattern_counts.step_all nodes stks index cp out = .ok r ∧ ∀ v, r = some v →
      langs nodes.val v.val =
        langs nodes.val out.val ++ (langs nodes.val (stks.val.drop index.val)).map (After · cp.val) := by
  rw [pattern_counts.step_all]
  by_cases inside : index.val < stks.val.length
  · obtain ⟨st, stRun, stSpec⟩ := Rowl.Compiled.step_spec nodes flagged cp stks.val[index.val] 0#usize
      (alloc.vec.Vec.new (alloc.vec.Vec Usize))
    obtain ⟨b, next⟩ := st
    obtain ⟨n1, a1, v1⟩ := add_one inside stks.property
    have drop : stks.val.drop index.val = stks.val[index.val] :: stks.val.drop n1.val := by
      rw [v1, List.drop_eq_getElem_cons inside]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup_vec inside, bind_ok, stRun, uncurry_apply_pair]
    cases b with
    | false => exact ⟨none, by simp, by simp⟩
    | true =>
      have nextLang := stSpec rfl
      simp only [new_val, Rowl.Compiled.stateLang_nil, show (0#usize : Usize).val = 0 from rfl, List.drop_zero,
        zero_add] at nextLang
      by_cases room : out.val.length < Usize.max
      · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out next room)
        obtain ⟨r, run, spec⟩ := step_all_spec nodes flagged stks n1 cp pushed
        refine ⟨r, ?_, ?_⟩
        · simp only [↓reduceIte, alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, decide_true,
            push, a1, bind_ok, run]
        · intro v hv
          rw [spec v hv, contents, drop]
          simp [langs, nextLang]
      · refine ⟨none, ?_, by simp⟩
        simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room]
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], ?_⟩
    intro v hv
    simp only [Option.some.injEq] at hv
    subst hv
    simp [List.drop_eq_nil_iff.mpr (show stks.val.length ≤ index.val by omega), langs]
termination_by stks.val.length - index.val
decreasing_by omega

theorem joint_step_spec (nodes : alloc.vec.Vec compiled.Node) (flagged : Flagged nodes.val)
    (j : pattern_counts.Joint) (a : pattern_counts.Atom) (hj : j.text.val < 1216) :
    ∃ r, pattern_counts.joint_step nodes j a = .ok r ∧ ∀ j', r = some j' →
      meaning nodes.val j' = afterAtom (meaning nodes.val j) a ∧ j'.text.val < 1216 := by
  rw [pattern_counts.joint_step]
  obtain ⟨sa, saRun, saSpec⟩ := step_all_spec nodes flagged j.«stacks» 0#usize a.lower
    (alloc.vec.Vec.new (alloc.vec.Vec (alloc.vec.Vec Usize)))
  simp only [saRun, bind_ok]
  cases sa with
  | none => exact ⟨none, rfl, by simp⟩
  | some stks =>
    obtain ⟨t, tRun, tVal⟩ := Rowl.LengthCounts.next_text_spec j.text a.base hj
    simp only [tRun, bind_ok]
    refine ⟨_, rfl, ?_⟩
    intro j' h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨?_, by rw [tVal]; exact textNext_lt _ _ hj⟩
    have := saSpec stks rfl
    simp only [new_val, show (0#usize : Usize).val = 0 from rfl, List.drop_zero, langs, List.map_nil,
      List.nil_append] at this
    simp only [meaning, afterAtom, Prod.mk.injEq, tVal, true_and, langs]
    exact this

theorem same_from_spec (left right : alloc.vec.Vec Usize) (equal : left.val.length = right.val.length)
    (index : Usize) : pattern_counts.same_from left right index =
      .ok (decide (left.val.drop index.val = right.val.drop index.val)) := by
  rw [pattern_counts.same_from]
  by_cases more : index.val < left.val.length
  · have moreRight : index.val < right.val.length := by omega
    have split : left.val.drop index.val = right.val.drop index.val ↔
        left.val[index.val] = right.val[index.val] ∧
          left.val.drop (index.val + 1) = right.val.drop (index.val + 1) := by
      rw [List.drop_eq_getElem_cons more, List.drop_eq_getElem_cons moreRight, List.cons.injEq]
    by_cases head : left.val[index.val] = right.val[index.val]
    · obtain ⟨next, advance, nextValue⟩ := add_one more left.property
      have rest := same_from_spec left right equal next
      rw [nextValue] at rest
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, moreRight, ↓reduceIte,
        alloc.vec.Vec.index_slice_index, lookup_vec more, lookup_vec moreRight, bind_ok, head, advance, rest]
      simp only [split, head, true_and]
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, moreRight, ↓reduceIte,
        alloc.vec.Vec.index_slice_index, lookup_vec more, lookup_vec moreRight, bind_ok, head]
      simp only [split, head, false_and, decide_false]
  · have emptyLeft : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have emptyRight : right.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, emptyLeft, emptyRight]
termination_by left.val.length - index.val
decreasing_by omega

theorem same_stack_spec (left right : alloc.vec.Vec Usize) :
    pattern_counts.same_stack left right = .ok (decide (left.val = right.val)) := by
  rw [pattern_counts.same_stack]
  by_cases equal : left.val.length = right.val.length
  · have lengths : alloc.vec.Vec.len left = alloc.vec.Vec.len right :=
      UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len_val, equal])
    simp only [lengths, ↓reduceIte, same_from_spec left right equal, show (0#usize).val = 0 from rfl,
      List.drop_zero]
  · have lengths : alloc.vec.Vec.len left ≠ alloc.vec.Vec.len right := by
      intro same; exact equal (by simpa [alloc.vec.Vec.len_val] using congrArg UScalar.val same)
    have different : left.val ≠ right.val := fun same => equal (by rw [same])
    simp only [lengths, ↓reduceIte, different, decide_false]

theorem listed_stack_spec (states : alloc.vec.Vec (alloc.vec.Vec Usize)) (stack : alloc.vec.Vec Usize)
    (index : Usize) : pattern_counts.listed_stack states stack index =
      .ok (decide (∃ s ∈ states.val.drop index.val, s.val = stack.val)) := by
  rw [pattern_counts.listed_stack]
  by_cases more : index.val < states.val.length
  · have split : (∃ s ∈ states.val.drop index.val, s.val = stack.val) ↔
        states.val[index.val].val = stack.val ∨ ∃ s ∈ states.val.drop (index.val + 1), s.val = stack.val := by
      rw [List.drop_eq_getElem_cons more]
      constructor
      · rintro ⟨s, member, same⟩
        rcases List.mem_cons.mp member with rfl | later
        · exact Or.inl same
        · exact Or.inr ⟨s, later, same⟩
      · rintro (same | ⟨s, member, same⟩)
        · exact ⟨_, List.mem_cons_self .., same⟩
        · exact ⟨s, List.mem_cons_of_mem _ member, same⟩
    by_cases here : states.val[index.val].val = stack.val
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        lookup_vec more, bind_ok, same_stack_spec, here, decide_true]
      simp only [split, here, true_or, decide_true]
    · obtain ⟨next, advance, nextValue⟩ := add_one more states.property
      have rest := listed_stack_spec states stack next
      rw [nextValue] at rest
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        lookup_vec more, bind_ok, same_stack_spec, here, decide_false, Bool.false_eq_true, advance, rest]
      simp only [split, here, false_or]
  · have empty : states.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, empty]
termination_by states.val.length - index.val
decreasing_by omega

theorem within_spec (left right : alloc.vec.Vec (alloc.vec.Vec Usize)) (index : Usize) :
    ∃ b, pattern_counts.within left right index = .ok b ∧
      (b = true → ∀ s ∈ left.val.drop index.val, ∃ s' ∈ right.val, s'.val = s.val) := by
  rw [pattern_counts.within]
  by_cases more : index.val < left.val.length
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup_vec more, bind_ok, listed_stack_spec, show (0#usize : Usize).val = 0 from rfl, List.drop_zero]
    by_cases here : ∃ s ∈ right.val, s.val = left.val[index.val].val
    · obtain ⟨next, advance, nextValue⟩ := add_one more left.property
      obtain ⟨b, run, spec⟩ := within_spec left right next
      refine ⟨b, by simp [here, advance, run], ?_⟩
      intro hb s mem
      rw [List.drop_eq_getElem_cons more] at mem
      rcases List.mem_cons.mp mem with rfl | later
      · exact here
      · exact spec hb s (by rw [nextValue]; exact later)
    · exact ⟨false, by simp [here], by simp⟩
  · refine ⟨true, by simp [UScalar.lt_equiv, more], ?_⟩
    intro _ s mem
    rw [List.drop_eq_nil_iff.mpr (by omega)] at mem
    cases mem
termination_by left.val.length - index.val
decreasing_by omega

theorem stateLang_of_within {nodes : List compiled.Node} {a b : List (alloc.vec.Vec Usize)}
    (ab : ∀ s ∈ a, ∃ s' ∈ b, s'.val = s.val) (ba : ∀ s ∈ b, ∃ s' ∈ a, s'.val = s.val) :
    stateLang nodes a = stateLang nodes b := by
  ext w
  rw [Rowl.Compiled.mem_stateLang, Rowl.Compiled.mem_stateLang]
  constructor
  · rintro ⟨s, mem, hw⟩
    obtain ⟨s', mem', same⟩ := ab s mem
    exact ⟨s', mem', by rw [same]; exact hw⟩
  · rintro ⟨s, mem, hw⟩
    obtain ⟨s', mem', same⟩ := ba s mem
    exact ⟨s', mem', by rw [same]; exact hw⟩

theorem same_sets_spec (nodes : List compiled.Node) (left right : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec Usize)))
    (index : Usize) (equal : left.val.length = right.val.length) :
    ∃ b, pattern_counts.same_sets left right index = .ok b ∧
      (b = true → langs nodes (left.val.drop index.val) = langs nodes (right.val.drop index.val)) := by
  rw [pattern_counts.same_sets]
  by_cases more : index.val < left.val.length
  · have moreRight : index.val < right.val.length := by omega
    obtain ⟨w1, w1Run, w1Spec⟩ := within_spec left.val[index.val] right.val[index.val] 0#usize
    obtain ⟨w2, w2Run, w2Spec⟩ := within_spec right.val[index.val] left.val[index.val] 0#usize
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, moreRight, ↓reduceIte,
      alloc.vec.Vec.index_slice_index, lookup_vec more, lookup_vec moreRight, bind_ok, w1Run]
    cases w1 with
    | false => exact ⟨false, by simp, by simp⟩
    | true =>
      simp only [↓reduceIte, w2Run, bind_ok]
      cases w2 with
      | false => exact ⟨false, by simp, by simp⟩
      | true =>
        obtain ⟨next, advance, nextValue⟩ := add_one more left.property
        obtain ⟨b, run, spec⟩ := same_sets_spec nodes left right next equal
        refine ⟨b, by simp [advance, run], ?_⟩
        intro hb
        rw [List.drop_eq_getElem_cons more, List.drop_eq_getElem_cons moreRight]
        simp only [langs, List.map_cons, List.cons.injEq]
        refine ⟨stateLang_of_within (by simpa using w1Spec rfl) (by simpa using w2Spec rfl), ?_⟩
        have := spec hb
        rw [nextValue] at this
        exact this
  · refine ⟨true, by simp [UScalar.lt_equiv, more], ?_⟩
    intro _
    rw [List.drop_eq_nil_iff.mpr (by omega), List.drop_eq_nil_iff.mpr (by omega)]
termination_by left.val.length - index.val
decreasing_by omega

theorem same_joint_spec (nodes : List compiled.Node) (left right : pattern_counts.Joint) :
    ∃ b, pattern_counts.same_joint left right = .ok b ∧ (b = true → meaning nodes left = meaning nodes right) := by
  rw [pattern_counts.same_joint]
  by_cases text : left.text = right.text
  · by_cases lengths : left.«stacks».val.length = right.«stacks».val.length
    · have lens : alloc.vec.Vec.len left.«stacks» = alloc.vec.Vec.len right.«stacks» :=
        UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len_val, lengths])
      obtain ⟨b, run, spec⟩ := same_sets_spec nodes left.«stacks» right.«stacks» 0#usize lengths
      refine ⟨b, by simp [text, lens, run], ?_⟩
      intro hb
      have := spec hb
      simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at this
      simp [meaning, text, this]
    · have lens : alloc.vec.Vec.len left.«stacks» ≠ alloc.vec.Vec.len right.«stacks» := by
        intro h; exact lengths (by simpa [alloc.vec.Vec.len_val] using congrArg UScalar.val h)
      exact ⟨false, by simp [text, lens], by simp⟩
  · exact ⟨false, by simp [text], by simp⟩

theorem find_joint_spec (nodes : List compiled.Node) (states : alloc.vec.Vec pattern_counts.Joint)
    (joint : pattern_counts.Joint) (index : Usize) :
    ∃ r, pattern_counts.find_joint states joint index = .ok r ∧ ∀ t, r = some t →
      ∃ inside : t.val < states.val.length, meaning nodes states.val[t.val] = meaning nodes joint := by
  rw [pattern_counts.find_joint]
  by_cases more : index.val < states.val.length
  · obtain ⟨b, bRun, bSpec⟩ := same_joint_spec nodes states.val[index.val] joint
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup_vec more, bind_ok, bRun]
    cases b with
    | true =>
      refine ⟨_, rfl, ?_⟩
      intro t h
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨more, bSpec rfl⟩
    | false =>
      obtain ⟨next, advance, nextValue⟩ := add_one more states.property
      obtain ⟨r, run, spec⟩ := find_joint_spec nodes states joint next
      exact ⟨r, by simp [advance, run], spec⟩
  · exact ⟨none, by simp [UScalar.lt_equiv, more], by simp⟩
termination_by states.val.length - index.val
decreasing_by omega

/-! ### Exploring the joint states -/

/-- Rows of next states that agree with the joint states: each row has a next
    state for each atom, which stands for the row's state after the atom. -/
def RowsAgree (nodes : List compiled.Node) (atoms : List pattern_counts.Atom) (states : List pattern_counts.Joint)
    (rows : List (alloc.vec.Vec Usize)) : Prop :=
  ∀ (q : ℕ) (row : alloc.vec.Vec Usize), rows[q]? = some row → row.val.length = atoms.length ∧
    ∀ (k : ℕ) (t : Usize) (a : pattern_counts.Atom), row.val[k]? = some t → atoms[k]? = some a →
      ∃ jt jq, states[t.val]? = some jt ∧ states[q]? = some jq ∧ meaning nodes jt = afterAtom (meaning nodes jq) a

theorem prefix_get {α : Type} {l l' : List α} (h : l <+: l') {i : ℕ} {x : α} (hx : l[i]? = some x) :
    l'[i]? = some x := by
  obtain ⟨t, rfl⟩ := h
  have : i < l.length := by
    by_contra out
    rw [List.getElem?_eq_none (by omega)] at hx
    cases hx
  rw [List.getElem?_append_left this, hx]

theorem rows_agree_mono {nodes : List compiled.Node} {atoms : List pattern_counts.Atom}
    {states found : List pattern_counts.Joint} {rows : List (alloc.vec.Vec Usize)} (h : states <+: found)
    (agree : RowsAgree nodes atoms states rows) : RowsAgree nodes atoms found rows := by
  intro q row hrow
  obtain ⟨len, each⟩ := agree q row hrow
  refine ⟨len, fun k t a ht ha => ?_⟩
  obtain ⟨jt, jq, et, eq, same⟩ := each k t a ht ha
  exact ⟨jt, jq, prefix_get h et, prefix_get h eq, same⟩

theorem get_of_lt {α : Type} {l : List α} {i : ℕ} (h : i < l.length) : l[i]? = some l[i] :=
  List.getElem?_eq_getElem h

theorem row_spec (nodes : alloc.vec.Vec compiled.Node) (flagged : Flagged nodes.val)
    (atoms : alloc.vec.Vec pattern_counts.Atom) (state atomIndex : Usize)
    (states : alloc.vec.Vec pattern_counts.Joint) (out : alloc.vec.Vec Usize) (js : pattern_counts.Joint)
    (hjs : states.val[state.val]? = some js)
    (texts : ∀ j ∈ states.val, j.text.val < 1216)
    (aligned : out.val.length = atomIndex.val) (le : atomIndex.val ≤ atoms.val.length)
    (good : ∀ (k : ℕ) (t : Usize) (a : pattern_counts.Atom), out.val[k]? = some t → atoms.val[k]? = some a →
      ∃ jt, states.val[t.val]? = some jt ∧ meaning nodes.val jt = afterAtom (meaning nodes.val js) a) :
    ∃ r, pattern_counts.row nodes atoms state atomIndex states out = .ok r ∧ ∀ found row, r = some (found, row) →
      states.val <+: found.val ∧ (∀ j ∈ found.val, j.text.val < 1216) ∧ row.val.length = atoms.val.length ∧
      ∀ (k : ℕ) (t : Usize) (a : pattern_counts.Atom), row.val[k]? = some t → atoms.val[k]? = some a →
        ∃ jt, found.val[t.val]? = some jt ∧ meaning nodes.val jt = afterAtom (meaning nodes.val js) a := by
  rw [pattern_counts.row]
  have inside : state.val < states.val.length := by
    by_contra out'
    rw [List.getElem?_eq_none (by omega)] at hjs
    cases hjs
  have jsEq : states.val[state.val] = js := by
    rw [get_of_lt inside] at hjs
    exact Option.some.inj hjs
  by_cases more : atomIndex.val < atoms.val.length
  · have cond : (decide (atomIndex.val < atoms.val.length) && decide (state.val < states.val.length)) = true := by
      simp [more, inside]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, cond, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup_vec inside, lookup_vec more, bind_ok]
    obtain ⟨jstep, jsRun, jsSpec⟩ := joint_step_spec nodes flagged states.val[state.val] atoms.val[atomIndex.val]
      (texts _ (List.getElem_mem inside))
    simp only [jsRun, bind_ok]
    cases jstep with
    | none => exact ⟨none, rfl, by simp⟩
    | some joint =>
      obtain ⟨jointMeaning, jointText⟩ := jsSpec joint rfl
      rw [jsEq] at jointMeaning
      obtain ⟨fj, fjRun, fjSpec⟩ := find_joint_spec nodes.val states joint 0#usize
      simp only [fjRun, bind_ok]
      obtain ⟨n1, a1, v1⟩ := add_one more atoms.property
      have rest : ∀ (states1 : alloc.vec.Vec pattern_counts.Joint) (target : Usize),
          states.val <+: states1.val → (∀ j ∈ states1.val, j.text.val < 1216) →
          (∀ (jt : pattern_counts.Joint), states1.val[target.val]? = some jt → meaning nodes.val jt =
            afterAtom (meaning nodes.val js) atoms.val[atomIndex.val]) →
          ∃ r, (if (decide (target.val < states1.val.length) && decide (out.val.length < Usize.max)) = true then
              (do
                let out1 ← out.push target
                let i4 ← atomIndex + 1#usize
                pattern_counts.row nodes atoms state i4 states1 out1 : Result _)
            else ok none) = ok r ∧ ∀ found row, r = some (found, row) →
            states.val <+: found.val ∧ (∀ j ∈ found.val, j.text.val < 1216) ∧ row.val.length = atoms.val.length ∧
            ∀ (k : ℕ) (t : Usize) (a : pattern_counts.Atom), row.val[k]? = some t → atoms.val[k]? = some a →
              ∃ jt, found.val[t.val]? = some jt ∧ meaning nodes.val jt = afterAtom (meaning nodes.val js) a := by
        intro states1 target prefix1 texts1 targetSpec
        by_cases ok' : target.val < states1.val.length ∧ out.val.length < Usize.max
        · have cond2 : (decide (target.val < states1.val.length) && decide (out.val.length < Usize.max)) = true := by
            simp [ok'.1, ok'.2]
          simp only [cond2, ↓reduceIte]
          obtain ⟨out1, push1, contents1⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out target ok'.2)
          obtain ⟨r, run, spec⟩ := row_spec nodes flagged atoms state n1 states1 out1 js (prefix_get prefix1 hjs)
            texts1 (by rw [contents1]; simp [aligned, v1]) (by omega) (by
              intro k t a ht ha
              rw [contents1] at ht
              by_cases old : k < out.val.length
              · rw [List.getElem?_append_left old] at ht
                obtain ⟨jt, et, same⟩ := good k t a ht ha
                exact ⟨jt, prefix_get prefix1 et, same⟩
              · have hk : k = out.val.length := by
                  by_contra ne
                  rw [List.getElem?_eq_none (by simp; omega)] at ht
                  cases ht
                subst hk
                simp only [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
                  Option.some.injEq] at ht
                subst ht
                rw [aligned, get_of_lt more] at ha
                cases ha
                exact ⟨_, get_of_lt ok'.1, targetSpec _ (get_of_lt ok'.1)⟩)
          refine ⟨r, by simp [push1, a1, run], ?_⟩
          intro found row h
          obtain ⟨pre, textsF, len, each⟩ := spec found row h
          exact ⟨prefix1.trans pre, textsF, len, each⟩
        · have cond2 : (decide (target.val < states1.val.length) && decide (out.val.length < Usize.max)) = false := by
            simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
            omega
          simp only [cond2, Bool.false_eq_true, ↓reduceIte]
          exact ⟨none, rfl, by simp⟩
      cases fj with
      | some t =>
        obtain ⟨ht, same⟩ := fjSpec t rfl
        have := rest states t (List.prefix_refl _) texts (by
          intro jt e
          rw [get_of_lt ht] at e
          cases e
          rw [same, jointMeaning])
        simpa [usize_max_val] using this
      | none =>
        by_cases room : states.val.length < Usize.max
        · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec states joint room)
          have := rest pushed (alloc.vec.Vec.len states) (by rw [contents]; exact List.prefix_append _ _)
            (by
              intro j mem
              rw [contents] at mem
              rcases List.mem_append.mp mem with m | m
              · exact texts j m
              · simp only [List.mem_singleton] at m; rw [m]; exact jointText)
            (by
              intro jt e
              rw [contents] at e
              simp only [alloc.vec.Vec.len_val, List.getElem?_append_right (le_refl _), Nat.sub_self,
                List.getElem?_cons_zero, Option.some.injEq] at e
              rw [← e]
              exact jointMeaning)
          simpa [usize_max_val, room, push] using this
        · simp [usize_max_val, room]
  · have cond : (decide (atomIndex.val < atoms.val.length) && decide (state.val < states.val.length)) = false := by
      simp [more]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, cond, Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, rfl, ?_⟩
    intro found row h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨List.prefix_refl _, texts, by omega, good⟩
termination_by atoms.val.length - atomIndex.val
decreasing_by omega

theorem explore_spec (nodes : alloc.vec.Vec compiled.Node) (flagged : Flagged nodes.val)
    (atoms : alloc.vec.Vec pattern_counts.Atom) (states : alloc.vec.Vec pattern_counts.Joint)
    (next : alloc.vec.Vec (alloc.vec.Vec Usize)) (fuel : Usize)
    (texts : ∀ j ∈ states.val, j.text.val < 1216) (le : next.val.length ≤ states.val.length)
    (agree : RowsAgree nodes.val atoms.val states.val next.val) :
    ∃ r, pattern_counts.explore nodes atoms states next fuel = .ok r ∧ ∀ found rows, r = some (found, rows) →
      states.val <+: found.val ∧ (∀ j ∈ found.val, j.text.val < 1216) ∧ rows.val.length = found.val.length ∧
      RowsAgree nodes.val atoms.val found.val rows.val := by
  rw [pattern_counts.explore]
  by_cases more : next.val.length < states.val.length
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte]
    by_cases zero : fuel.val = 0
    · have : fuel = 0#usize := UScalar.eq_of_val_eq (by simpa using zero)
      simp only [this, ↓reduceIte]
      exact ⟨none, rfl, by simp⟩
    · have ne : ¬ fuel = 0#usize := fun h => zero (by simp [h])
      simp only [ne, ↓reduceIte]
      have hjs : states.val[(alloc.vec.Vec.len next).val]? = some states.val[next.val.length] := by
        simp only [alloc.vec.Vec.len_val]; exact get_of_lt more
      obtain ⟨rw', rwRun, rwSpec⟩ := row_spec nodes flagged atoms (alloc.vec.Vec.len next) 0#usize states
        (alloc.vec.Vec.new Usize) states.val[next.val.length] hjs texts (by simp) (by simp)
        (by intro k t a ht; simp at ht)
      simp only [rwRun, bind_ok]
      cases rw' with
      | none => exact ⟨none, rfl, by simp⟩
      | some p =>
        obtain ⟨found, out⟩ := p
        obtain ⟨pre, textsF, len, each⟩ := rwSpec found out rfl
        simp only [uncurry_apply_pair]
        have room : next.val.length < Usize.max := by have := states.property; omega
        obtain ⟨next1, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec next out room)
        obtain ⟨f1, f1Run, f1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := fuel) (y := 1#usize) (by simp; omega))
        have foundLen : states.val.length ≤ found.val.length := pre.length_le
        obtain ⟨r, run, spec⟩ := explore_spec nodes flagged atoms found next1 f1 textsF
          (by rw [contents]; simp; omega) (by
            intro q row hrow
            rw [contents] at hrow
            by_cases old : q < next.val.length
            · rw [List.getElem?_append_left old] at hrow
              exact rows_agree_mono pre agree q row hrow
            · have hq : q = next.val.length := by
                by_contra ne'
                rw [List.getElem?_eq_none (by simp; omega)] at hrow
                cases hrow
              subst hq
              simp only [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
                Option.some.injEq] at hrow
              subst hrow
              refine ⟨len, fun k t a ht ha => ?_⟩
              obtain ⟨jt, et, same⟩ := each k t a ht ha
              exact ⟨jt, _, et, prefix_get pre (get_of_lt more), same⟩)
        refine ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, push, f1Run, run], ?_⟩
        intro found' rows h
        obtain ⟨pre', texts', len', agree'⟩ := spec found' rows h
        exact ⟨pre.trans pre', texts', len', agree'⟩
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte]
    refine ⟨_, rfl, ?_⟩
    intro found rows h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨List.prefix_refl _, texts, by omega, agree⟩
termination_by fuel.val
decreasing_by simp at f1Val; omega

theorem starts_spec (nodes : List compiled.Node) (roots : alloc.vec.Vec Usize) (index : Usize)
    (out : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec Usize))) :
    ∃ r, pattern_counts.starts roots index out = .ok r ∧ ∀ v, r = some v →
      langs nodes v.val = langs nodes out.val ++ (roots.val.drop index.val).map (fun root => lang nodes root.val) := by
  rw [pattern_counts.starts]
  by_cases inside : index.val < roots.val.length
  · by_cases room : out.val.length < Usize.max
    · obtain ⟨st, stRun, stLang⟩ := Rowl.Compiled.start_spec nodes roots.val[index.val]
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out st room)
      obtain ⟨n1, a1, v1⟩ := add_one inside roots.property
      obtain ⟨r, run, spec⟩ := starts_spec nodes roots n1 pushed
      refine ⟨r, by simp [UScalar.lt_equiv, inside, usize_max_val, room, alloc.vec.Vec.index_slice_index,
        lookup_vec inside, stRun, push, a1, run], ?_⟩
      intro v hv
      rw [spec v hv, contents, v1, List.drop_eq_getElem_cons inside]
      simp only [langs, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
        List.nil_append, stLang]
    · refine ⟨none, by simp [UScalar.lt_equiv, inside, usize_max_val, room], by simp⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], ?_⟩
    intro v hv
    simp only [Option.some.injEq] at hv
    subst hv
    simp [List.drop_eq_nil_iff.mpr (show roots.val.length ≤ index.val by omega)]
termination_by roots.val.length - index.val
decreasing_by omega

theorem accepts_from_spec (nodes : alloc.vec.Vec compiled.Node) (flagged : Flagged nodes.val)
    (stks : alloc.vec.Vec (alloc.vec.Vec (alloc.vec.Vec Usize))) (index : Usize) (out : alloc.vec.Vec Bool)
    (len : out.val.length = index.val) :
    ∃ r, pattern_counts.accepts_from nodes stks index out = .ok r ∧
      r.val = out.val ++ (langs nodes.val (stks.val.drop index.val)).map (fun L => decide ([] ∈ L)) := by
  rw [pattern_counts.accepts_from]
  by_cases inside : index.val < stks.val.length
  · have room : out.val.length < Usize.max := by have := stks.property; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out
      (decide ([] ∈ stateLang nodes.val stks.val[index.val].val)) room)
    obtain ⟨n1, a1, v1⟩ := add_one inside stks.property
    obtain ⟨r, run, spec⟩ := accepts_from_spec nodes flagged stks n1 pushed (by rw [contents]; simp [len, v1])
    refine ⟨r, ?_, ?_⟩
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, usize_max_val, room,
        alloc.vec.Vec.index_slice_index, lookup_vec inside, bind_ok, Rowl.Compiled.accepting_spec _ flagged,
        show (0#usize : Usize).val = 0 from rfl, List.drop_zero, push, a1, run]
    · rw [spec, contents, v1, List.drop_eq_getElem_cons inside]
      simp only [langs, List.map_cons, List.map_append, List.map_nil, List.append_assoc, List.cons_append,
        List.nil_append]
  · refine ⟨out, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show stks.val.length ≤ index.val by omega), langs]
termination_by stks.val.length - index.val
decreasing_by omega

/-- Whether each language of a joint state has the empty word. -/
noncomputable def acceptsOf (nodes : List compiled.Node) (j : pattern_counts.Joint) : List Bool :=
  (langs nodes j.«stacks».val).map fun L => decide ([] ∈ L)

theorem profiles_from_spec (nodes : alloc.vec.Vec compiled.Node) (flagged : Flagged nodes.val)
    (states : alloc.vec.Vec pattern_counts.Joint) (index : Usize) (ranks : alloc.vec.Vec U8)
    (accepts : alloc.vec.Vec (alloc.vec.Vec Bool)) (lr : ranks.val.length = index.val)
    (la : accepts.val.length = index.val) :
    ∃ r, pattern_counts.profiles_from nodes states index ranks accepts = .ok r ∧
      r.1.val.map (·.val) = ranks.val.map (·.val) ++ (states.val.drop index.val).map (fun j => textRank j.text.val) ∧
      r.2.val.map (·.val) = accepts.val.map (·.val) ++ (states.val.drop index.val).map (acceptsOf nodes.val) := by
  rw [pattern_counts.profiles_from]
  by_cases inside : index.val < states.val.length
  · have room1 : ranks.val.length < Usize.max := by have := states.property; omega
    have room2 : accepts.val.length < Usize.max := by have := states.property; omega
    have cond : (decide (ranks.val.length < Usize.max) && decide (accepts.val.length < Usize.max)) = true := by
      simp [room1, room2]
    obtain ⟨rk, rkRun, rkVal⟩ := Rowl.LengthCounts.rank_spec states.val[index.val].text
    obtain ⟨ranks2, push1, contents1⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec ranks rk room1)
    obtain ⟨acc, accRun, accVal⟩ := accepts_from_spec nodes flagged states.val[index.val].«stacks» 0#usize
      (alloc.vec.Vec.new Bool) (by simp)
    obtain ⟨accepts2, push2, contents2⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec accepts acc room2)
    obtain ⟨n1, a1, v1⟩ := add_one inside states.property
    obtain ⟨r, run, spec1, spec2⟩ := profiles_from_spec nodes flagged states n1 ranks2 accepts2
      (by rw [contents1]; simp [lr, v1]) (by rw [contents2]; simp [la, v1])
    refine ⟨r, ?_, ?_, ?_⟩
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, usize_max_val, cond,
        alloc.vec.Vec.index_slice_index, lookup_vec inside, bind_ok, rkRun, push1, accRun, push2, a1,
        uncurry_apply_pair, run]
    · rw [spec1, contents1, v1, List.drop_eq_getElem_cons inside]
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
        List.nil_append, rkVal]
    · rw [spec2, contents2, v1, List.drop_eq_getElem_cons inside]
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
        List.nil_append, accVal, new_val, show (0#usize : Usize).val = 0 from rfl, List.drop_zero, acceptsOf]
  · refine ⟨(ranks, accepts), by simp [UScalar.lt_equiv, inside], ?_, ?_⟩
    · simp [List.drop_eq_nil_iff.mpr (show states.val.length ≤ index.val by omega)]
    · simp [List.drop_eq_nil_iff.mpr (show states.val.length ≤ index.val by omega)]
termination_by states.val.length - index.val
decreasing_by omega

theorem compile_all_spec (t : compiled.Table) (es : alloc.vec.Vec regular.Expression) (index : Usize)
    (out : alloc.vec.Vec Usize) (flagged : Flagged t.nodes.val) (len : out.val.length = index.val)
    (le : index.val ≤ es.val.length)
    (prior : t.full = false → ∀ (i : ℕ) (root : Usize) (e : regular.Expression), out.val[i]? = some root →
      es.val[i]? = some e → root.val < t.nodes.val.length ∧ lang t.nodes.val root.val = Rowl.Regular.Denotes e) :
    ∃ roots t', pattern_counts.compile_all t es index out = .ok (roots, t') ∧ Flagged t'.nodes.val ∧
      (t'.full = false → roots.val.length = es.val.length ∧ ∀ (i : ℕ) (root : Usize) (e : regular.Expression),
        roots.val[i]? = some root → es.val[i]? = some e →
          root.val < t'.nodes.val.length ∧ lang t'.nodes.val root.val = Rowl.Regular.Denotes e) := by
  rw [pattern_counts.compile_all]
  by_cases inside : index.val < es.val.length
  · obtain ⟨root, t1, cRun, flagged1, grows, cSpec⟩ := Rowl.Compiled.compile_spec es.val[index.val] t flagged
    have room : out.val.length < Usize.max := by have := es.property; omega
    obtain ⟨out1, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out root room)
    obtain ⟨n1, a1, v1⟩ := add_one inside es.property
    obtain ⟨roots, t', run, flagged', spec⟩ := compile_all_spec t1 es n1 out1 flagged1
      (by rw [contents]; simp [len, v1]) (by omega) (by
        intro open1 i r e hr he
        rw [contents] at hr
        by_cases old : i < out.val.length
        · rw [List.getElem?_append_left old] at hr
          obtain ⟨lt, lg⟩ := prior (Rowl.Compiled.grows_open grows open1) i r e hr he
          exact ⟨lt_of_lt_of_le lt (Rowl.Compiled.grows_length grows),
            by rw [Rowl.Compiled.grows_lang grows _ lt]; exact lg⟩
        · have hi : i = out.val.length := by
            by_contra ne
            rw [List.getElem?_eq_none (by simp; omega)] at hr
            cases hr
          subst hi
          simp only [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
            Option.some.injEq] at hr
          subst hr
          rw [len, get_of_lt inside] at he
          cases he
          exact cSpec open1)
    refine ⟨roots, t', ?_, flagged', spec⟩
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup_vec inside, bind_ok, cRun, uncurry_apply_pair, usize_max_val, room, decide_true, push, a1, run]
  · refine ⟨out, t, by simp [UScalar.lt_equiv, inside], flagged, ?_⟩
    intro open'
    exact ⟨by omega, prior open'⟩
termination_by es.val.length - index.val
decreasing_by omega

/-- What the kernel's joint automaton of expressions is: over a table of nodes
    whose roots have the expressions' languages, its atoms are atoms of the XML
    characters that cut every interval node, and its joint states, the first
    the start of the strings' automaton with the expressions' languages, have
    rows of next states that agree with them, the ranks of their strings'
    states and whether each language has the empty word. -/
def Built (es : List regular.Expression) (A : pattern_counts.Automaton) : Prop :=
  ∃ (nodes : List compiled.Node) (found : List pattern_counts.Joint),
    Flagged nodes ∧ Partition (A.atoms.val.map triple) ∧ NodesCut (A.atoms.val.map triple) nodes ∧
    (found[0]?).map (meaning nodes) = some (0, es.map Rowl.Regular.Denotes) ∧
    (∀ j ∈ found, j.text.val < 1216) ∧ A.next.val.length = found.length ∧
    RowsAgree nodes A.atoms.val found A.next.val ∧
    A.ranks.val.map (·.val) = found.map (fun j => textRank j.text.val) ∧
    A.accepts.val.map (·.val) = found.map (acceptsOf nodes)

theorem nodes_cut {ts : List (ℕ × ℕ × ℕ)} {nodes : List compiled.Node} (part : Partition ts)
    (cuts : ∀ j (hj : j < nodes.length), ∀ lo hi, nodes[j].kind = .Interval lo hi →
      Cut ts lo.val ∧ Cut ts (min (hi.val + 1) 1114112)) : NodesCut ts nodes := by
  intro i hi lo hi' kind t mem c c' hc hc'
  obtain ⟨cl, ch⟩ := cuts i hi lo hi' kind
  exact interval_same mem (part.bounded t mem) cl ch hc hc'

@[local step] theorem atom_step (l u : U32) (b : Usize) : pattern_counts.atom l u b ⦃ a => a = ⟨l, u, b⟩ ⦄ := by
  simp [pattern_counts.atom]

theorem base_atoms_val : pattern_counts.base_atoms ⦃ r => r.val.map triple = baseTriples ⦄ := by
  unfold pattern_counts.base_atoms
  have big := usize_big
  step*
  all_goals (simp_all [triple, baseTriples, atomRanges]; try omega)
  all_goals rfl

theorem automaton_spec (es : alloc.vec.Vec regular.Expression) :
    ∃ r, pattern_counts.automaton es = .ok r ∧ ∀ A, r = some A → Built es.val A := by
  rw [pattern_counts.automaton]
  obtain ⟨t, tRun, tNodes, tOpen, tFlagged⟩ := Rowl.Compiled.table_spec
  obtain ⟨roots, t', caRun, flagged', caSpec⟩ := compile_all_spec t es 0#usize (alloc.vec.Vec.new Usize) tFlagged
    (by simp) (by simp) (by intro _ i root e h; simp at h)
  simp only [tRun, caRun, bind_ok, uncurry_apply_pair]
  by_cases full : t'.full = true ∨ roots.val.length ≠ es.val.length
  · have cond : (t'.full || (alloc.vec.Vec.len roots != alloc.vec.Vec.len es)) = true := by
      rcases full with f | f
      · simp [f]
      · have : alloc.vec.Vec.len roots ≠ alloc.vec.Vec.len es := fun h => f (by simpa using congrArg UScalar.val h)
        simp [this]
    simp only [cond, ↓reduceIte]
    exact ⟨none, rfl, by simp⟩
  · simp only [not_or, Bool.not_eq_true, ne_eq, Decidable.not_not] at full
    have cond : (t'.full || (alloc.vec.Vec.len roots != alloc.vec.Vec.len es)) = false := by
      have : alloc.vec.Vec.len roots = alloc.vec.Vec.len es := UScalar.eq_of_val_eq (by simpa using full.2)
      simp [full.1, this]
    simp only [cond, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨_, rootsSpec⟩ := caSpec full.1
    obtain ⟨base, baseRun, baseVal⟩ := WP.spec_imp_exists base_atoms_val
    have basePart : Partition (base.val.map triple) := by rw [baseVal]; exact base_partition
    obtain ⟨rf, rfRun, rfSpec⟩ := refine_spec t'.nodes 0#usize base basePart
    simp only [baseRun, rfRun, bind_ok]
    cases rf with
    | none => exact ⟨none, rfl, by simp⟩
    | some atoms =>
      obtain ⟨atomsPart, _, atomsCuts⟩ := rfSpec atoms rfl
      obtain ⟨st, stRun, stSpec⟩ := starts_spec t'.nodes.val roots 0#usize
        (alloc.vec.Vec.new (alloc.vec.Vec (alloc.vec.Vec Usize)))
      simp only [stRun, bind_ok]
      cases st with
      | none => exact ⟨none, rfl, by simp⟩
      | some first =>
        have firstLangs := stSpec first rfl
        simp only [new_val, langs, List.map_nil, List.nil_append, show (0#usize : Usize).val = 0 from rfl,
          List.drop_zero] at firstLangs
        have room : (alloc.vec.Vec.new pattern_counts.Joint).val.length < Usize.max := by simp; scalar_tac
        obtain ⟨states, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec
          (alloc.vec.Vec.new pattern_counts.Joint) ⟨0#usize, first⟩ room)
        obtain ⟨ex, exRun, exSpec⟩ := explore_spec t'.nodes flagged' atoms states
          (alloc.vec.Vec.new (alloc.vec.Vec Usize)) pattern_counts.JOINT_STATES
          (by rw [contents]; simp) (by simp) (by intro q row h; simp at h)
        simp only [push, exRun, bind_ok]
        cases ex with
        | none => exact ⟨none, rfl, by simp⟩
        | some p =>
          obtain ⟨found, next⟩ := p
          obtain ⟨pre, texts, len, agree⟩ := exSpec found next rfl
          obtain ⟨pf, pfRun, pfRanks, pfAccepts⟩ := profiles_from_spec t'.nodes flagged' found 0#usize
            (alloc.vec.Vec.new U8) (alloc.vec.Vec.new (alloc.vec.Vec Bool)) (by simp) (by simp)
          obtain ⟨ranks, accepts⟩ := pf
          simp only [uncurry_apply_pair, pfRun, bind_ok]
          refine ⟨_, rfl, ?_⟩
          intro A h
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨t'.nodes.val, found.val, flagged', atomsPart,
            nodes_cut atomsPart (fun j hj lo hi kind => atomsCuts j hj (by simp) lo hi kind), ?_, texts, len,
            agree, ?_, ?_⟩
          · have h0 : found.val[0]? = some ⟨0#usize, first⟩ := prefix_get pre (by rw [contents]; simp)
            rw [h0]
            simp only [Option.map_some, meaning, Option.some.injEq, Prod.mk.injEq, true_and]
            refine ⟨rfl, ?_⟩
            simp only [langs] at firstLangs ⊢
            rw [firstLangs]
            apply List.ext_getElem
            · simp [full.2]
            · intro i h1 h2
              simp only [List.getElem_map]
              have hr : i < roots.val.length := by simpa using h1
              have he : i < es.val.length := by omega
              exact (rootsSpec i _ _ (get_of_lt hr) (get_of_lt he)).2
          · simpa using pfRanks
          · simpa using pfAccepts

/-! ### Reading words -/

/-- The automaton of the joint states that counts the words ending in a state
    where `accept` holds: each atom is its code points. -/
def jointDfa (A : pattern_counts.Automaton) (accept : ℕ → Bool) : Dfa where
  atoms := A.atoms.val.length
  atom a := match A.atoms.val[a]? with
    | some x => Finset.Icc x.lower.val x.upper.val
    | none => ∅
  next q a := (A.next.val[q]?).bind fun row => (row.val[a]?).map (·.val)
  accept := accept

/-- What a joint state stands for after a word. -/
noncomputable def afterWord (m : ℕ × List (Language ℕ)) (w : List ℕ) : ℕ × List (Language ℕ) :=
  (runWith textNext m.1 w, m.2.map fun L => {u | w ++ u ∈ L})

theorem afterWord_nil (m : ℕ × List (Language ℕ)) : afterWord m [] = m := by
  obtain ⟨t, Ls⟩ := m
  simp only [afterWord, runWith, List.nil_append, Prod.mk.injEq, true_and]
  conv_rhs => rw [← List.map_id Ls]
  apply List.map_congr_left
  intro L _
  rfl

theorem langs_uniform {ts : List (ℕ × ℕ × ℕ)} {nodes : List compiled.Node} (cut : NodesCut ts nodes)
    (stks : List (alloc.vec.Vec (alloc.vec.Vec Usize))) : ∀ L ∈ langs nodes stks, Uniform ts L := by
  intro L mem
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp mem
  exact stateLang_uniform cut s.val

theorem joint_accepts {A : pattern_counts.Automaton} {nodes : List compiled.Node}
    {found : List pattern_counts.Joint} (part : Partition (A.atoms.val.map triple))
    (cut : NodesCut (A.atoms.val.map triple) nodes) (len : A.next.val.length = found.length)
    (agree : RowsAgree nodes A.atoms.val found A.next.val)
    (accept : ℕ → Bool) (P : ℕ × List (Language ℕ) → Prop)
    (hacc : ∀ q j, found[q]? = some j → (accept q = true ↔ P (meaning nodes j))) :
    ∀ (w : List ℕ) (q : ℕ) (j : pattern_counts.Joint), found[q]? = some j →
      ((jointDfa A accept).Accepts q w ↔ (∀ c ∈ w, Rowl.Unicode.XmlChar c) ∧ P (afterWord (meaning nodes j) w)) := by
  intro w
  induction w with
  | nil =>
    intro q j hj
    simp only [Dfa.Accepts, jointDfa, List.not_mem_nil, IsEmpty.forall_iff, implies_true, true_and, afterWord_nil]
    exact hacc q j hj
  | cons c w ih =>
    intro q j hj
    have hq : q < found.length := by
      by_contra out
      rw [List.getElem?_eq_none (by omega)] at hj
      cases hj
    have hrow : A.next.val[q]? = some A.next.val[q] := get_of_lt (by omega)
    obtain ⟨rowLen, rowEach⟩ := agree q A.next.val[q] hrow
    -- the step for an atom `a` that holds `c`
    have step : ∀ a (ha : a < A.atoms.val.length), c ∈ Finset.Icc A.atoms.val[a].lower.val A.atoms.val[a].upper.val →
        ∃ q' j', (jointDfa A accept).next q a = some q' ∧ found[q']? = some j' ∧ Rowl.Unicode.XmlChar c ∧
          afterWord (meaning nodes j') w = afterWord (meaning nodes j) (c :: w) := by
      intro a ha mem
      rw [Finset.mem_Icc] at mem
      have hra : a < A.next.val[q].val.length := by omega
      obtain ⟨jt, jq, et, eq, same⟩ := rowEach a A.next.val[q].val[a] A.atoms.val[a] (get_of_lt hra) (get_of_lt ha)
      rw [hj] at eq
      cases eq
      have tmem : triple A.atoms.val[a] ∈ A.atoms.val.map triple := List.mem_map_of_mem (List.getElem_mem ha)
      refine ⟨A.next.val[q].val[a].val, jt, ?_, et, (part.cover c).mpr ⟨_, tmem, mem⟩, ?_⟩
      · simp [jointDfa, hrow, get_of_lt hra]
      · rw [same]
        obtain ⟨_, based⟩ := part.based _ tmem
        have baseEq : atomOf c = A.atoms.val[a].base.val := based c mem
        simp only [afterWord, afterAtom, meaning, runWith, baseEq, List.map_map, Prod.mk.injEq, true_and]
        apply List.map_congr_left
        intro L hL
        have unif := langs_uniform cut j.«stacks».val L hL
        have sameAtom : SameAtom (A.atoms.val.map triple) A.atoms.val[a].lower.val c :=
          .inr ⟨_, tmem, by simp only [InT, triple]; omega, by simp only [InT, triple]; exact mem⟩
        simp only [Function.comp, after_same unif sameAtom]
        ext u
        simp
    constructor
    · rintro ⟨a, ha, inA, q', hnext, acc⟩
      have ha' : a < A.atoms.val.length := ha
      have inA' : c ∈ Finset.Icc A.atoms.val[a].lower.val A.atoms.val[a].upper.val := by
        simpa [jointDfa, get_of_lt ha'] using inA
      obtain ⟨q'', j', hn, hj', xml, eqAfter⟩ := step a ha' inA'
      have same : q' = q'' := Option.some.inj (hnext.symm.trans hn)
      subst same
      obtain ⟨xmls, pw⟩ := (ih q' j' hj').mp acc
      refine ⟨fun x hx => ?_, by rw [← eqAfter]; exact pw⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact xml
      · exact xmls x hx
    · rintro ⟨xmls, pw⟩
      obtain ⟨t, tmem, inT⟩ := (part.cover c).mp (xmls c (by simp))
      obtain ⟨x, xmem, rfl⟩ := List.mem_map.mp tmem
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem xmem
      have inA : c ∈ Finset.Icc A.atoms.val[a].lower.val A.atoms.val[a].upper.val := by
        rw [Finset.mem_Icc]; exact inT
      obtain ⟨q', j', hn, hj', _, eqAfter⟩ := step a ha inA
      refine ⟨a, ha, by simpa [jointDfa, get_of_lt ha] using inA, q', hn, ?_⟩
      exact (ih q' j' hj').mpr ⟨fun x hx => xmls x (by simp [hx]), by rw [eqAfter]; exact pw⟩

/-- The states the kernel counts: of a rank from `first` on and before `last`,
    where exactly the expressions of `profile` accept. -/
def profileAccept (A : pattern_counts.Automaton) (first last : ℕ) (profile : List Bool) (q : ℕ) : Bool :=
  match A.ranks.val[q]?, A.accepts.val[q]? with
  | some r, some acc => decide (first ≤ r.val ∧ r.val < last ∧ acc.val = profile)
  | _, _ => false

/-- The words that the kernel counts for a profile: words of XML characters
    whose rank is from `first` on and before `last` and that exactly the
    expressions of `profile` have. -/
def ProfileWord (es : List regular.Expression) (first last : ℕ) (profile : List Bool) (w : List ℕ) : Prop :=
  (∀ c ∈ w, Rowl.Unicode.XmlChar c) ∧ first ≤ textRank (runWith textNext 0 w) ∧
    textRank (runWith textNext 0 w) < last ∧ es.map (fun e => decide (w ∈ Rowl.Regular.Denotes e)) = profile

theorem profile_accepts {es : List regular.Expression} {A : pattern_counts.Automaton} (built : Built es A)
    (first last : ℕ) (profile : List Bool) (w : List ℕ) :
    (jointDfa A (profileAccept A first last profile)).Accepts 0 w ↔ ProfileWord es first last profile w := by
  obtain ⟨nodes, found, _, part, cut, start, _, len, agree, ranks, accepts⟩ := built
  obtain ⟨j0, hj0, mj0⟩ : ∃ j0, found[0]? = some j0 ∧ meaning nodes j0 = (0, es.map Rowl.Regular.Denotes) := by
    cases h : found[0]? with
    | none => rw [h] at start; cases start
    | some j0 => rw [h] at start; exact ⟨j0, rfl, Option.some.inj start⟩
  have hacc : ∀ q j, found[q]? = some j → (profileAccept A first last profile q = true ↔
      (first ≤ textRank (meaning nodes j).1 ∧ textRank (meaning nodes j).1 < last ∧
        (meaning nodes j).2.map (fun L => decide ([] ∈ L)) = profile)) := by
    intro q j hj
    have hr : (A.ranks.val.map (·.val))[q]? = some (textRank j.text.val) := by rw [ranks]; simp [hj]
    have ha : (A.accepts.val.map (·.val))[q]? = some (acceptsOf nodes j) := by rw [accepts]; simp [hj]
    rw [List.getElem?_map] at hr ha
    cases hrq : A.ranks.val[q]? with
    | none => rw [hrq] at hr; cases hr
    | some r =>
      cases haq : A.accepts.val[q]? with
      | none => rw [haq] at ha; cases ha
      | some acc =>
        rw [hrq] at hr
        rw [haq] at ha
        simp only [Option.map_some, Option.some.injEq] at hr ha
        simp [profileAccept, hrq, haq, hr, ha, meaning, acceptsOf]
  rw [joint_accepts part cut len agree _ (fun m => first ≤ textRank m.1 ∧ textRank m.1 < last ∧
    m.2.map (fun L => decide ([] ∈ L)) = profile) hacc w 0 j0 hj0, mj0]
  simp only [ProfileWord, afterWord, List.map_map]
  constructor
  · rintro ⟨xmls, a, b, c⟩
    refine ⟨xmls, a, b, ?_⟩
    rw [← c]
    apply List.map_congr_left
    intro e _
    simp
  · rintro ⟨xmls, a, b, c⟩
    refine ⟨xmls, a, b, ?_⟩
    rw [← c]
    apply List.map_congr_left
    intro e _
    simp

/-! ### Counting -/

theorem same_flags_spec (left right : alloc.vec.Vec Bool) (index : Usize) :
    pattern_counts.same_flags left right index = .ok (decide (left.val.drop index.val = right.val.drop index.val)) := by
  rw [pattern_counts.same_flags]
  by_cases inLeft : index.val < left.val.length
  · by_cases inRight : index.val < right.val.length
    · have split : left.val.drop index.val = right.val.drop index.val ↔
          left.val[index.val] = right.val[index.val] ∧
            left.val.drop (index.val + 1) = right.val.drop (index.val + 1) := by
        rw [List.drop_eq_getElem_cons inLeft, List.drop_eq_getElem_cons inRight, List.cons.injEq]
      by_cases head : left.val[index.val] = right.val[index.val]
      · obtain ⟨next, advance, nextValue⟩ := add_one inLeft left.property
        have rest := same_flags_spec left right next
        rw [nextValue] at rest
        simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inLeft, inRight, ↓reduceIte,
          alloc.vec.Vec.index_slice_index, lookup_vec inLeft, lookup_vec inRight, bind_ok, head, advance, rest]
        simp only [split, head, true_and]
      · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inLeft, inRight, ↓reduceIte,
          alloc.vec.Vec.index_slice_index, lookup_vec inLeft, lookup_vec inRight, bind_ok, head]
        simp only [split, head, false_and, decide_false]
    · have differ : left.val.drop index.val ≠ right.val.drop index.val := by
        rw [List.drop_eq_nil_iff.mpr (show right.val.length ≤ index.val by omega)]
        exact List.ne_nil_of_length_pos (by simp; omega)
      simp [UScalar.lt_equiv, inLeft, inRight, differ]
  · have done : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [UScalar.lt_equiv, inLeft, done, List.drop_eq_nil_iff, UScalar.le_equiv]
termination_by left.val.length - index.val
decreasing_by omega

theorem initial_from_spec (A : pattern_counts.Automaton) (first last : U8) (profile : alloc.vec.Vec Bool)
    (cap state : Usize) (out : alloc.vec.Vec Usize)
    (hr : A.ranks.val.length = A.next.val.length) (ha : A.accepts.val.length = A.next.val.length)
    (hs : state.val ≤ A.next.val.length) (hout : out.val.length = state.val) :
    ∃ res, pattern_counts.initial_from A first last profile cap state out = .ok res ∧
      res.val.length = A.next.val.length ∧ ∀ q < A.next.val.length, countsOf res.val q =
        if q < state.val then countsOf out.val q
        else (jointDfa A (profileAccept A first.val last.val profile.val)).capCounts cap.val 0 q := by
  rw [pattern_counts.initial_from]
  by_cases inside : state.val < A.next.val.length
  · have inR : state.val < A.ranks.val.length := by omega
    have inA : state.val < A.accepts.val.length := by omega
    have cond : (decide (state.val < A.ranks.val.length) && decide (state.val < A.accepts.val.length)) = true := by
      simp [inR, inA]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, cond, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup_vec inR, lookup_vec inA, bind_ok, same_flags_spec, show (0#usize : Usize).val = 0 from rfl,
      List.drop_zero, UScalar.le_equiv]
    obtain ⟨one, oneRun, oneVal⟩ := capped_sum_spec 0#usize 1#usize cap
    have counted : (jointDfa A (profileAccept A first.val last.val profile.val)).capCounts cap.val 0 state.val =
        (if ((decide (first.val ≤ (A.ranks.val[state.val]).val) && decide ((A.ranks.val[state.val]).val < last.val)) &&
            decide ((A.accepts.val[state.val]).val = profile.val)) = true then one.val else 0) := by
      simp only [Dfa.capCounts, jointDfa, profileAccept, get_of_lt inR, get_of_lt inA]
      rw [oneVal]
      split_ifs with h1 h2 h2 <;> simp_all [capAt]
    obtain ⟨value, valueRun, valueVal⟩ : ∃ value : Usize,
        (if ((decide (first.val ≤ (A.ranks.val[state.val]).val) && decide ((A.ranks.val[state.val]).val < last.val)) &&
            decide ((A.accepts.val[state.val]).val = profile.val)) = true then lengths.capped_sum 0#usize 1#usize cap
          else ok 0#usize) = ok value ∧
          value.val = (jointDfa A (profileAccept A first.val last.val profile.val)).capCounts cap.val 0 state.val := by
      rw [counted]
      split_ifs
      · exact ⟨one, oneRun, rfl⟩
      · exact ⟨0#usize, rfl, rfl⟩
    have short : out.val.length < Usize.max := by have := A.next.property; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out value short)
    obtain ⟨next, advance, nextValue⟩ := add_one inside A.next.property
    obtain ⟨res, run, resLen, resVal⟩ := initial_from_spec A first last profile cap next pushed hr ha (by omega)
      (by rw [contents]; simp [hout, nextValue])
    refine ⟨res, ?_, resLen, fun q hq => ?_⟩
    · simp only [valueRun, bind_ok, usize_max_val, short, decide_true, ↓reduceIte, push, advance, run]
    · rw [resVal q hq, nextValue, contents, countsOf_push, hout]
      by_cases below : q < state.val
      · simp [below, show q < state.val + 1 by omega]
      · by_cases same : q = state.val
        · subst same
          simp [valueVal]
        · simp [below, same, show ¬ q < state.val + 1 by omega]
  · have notIn : (decide (state.val < A.ranks.val.length) && decide (state.val < A.accepts.val.length)) = false := by
      simp; omega
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, notIn, Bool.false_eq_true, ↓reduceIte]
    refine ⟨out, rfl, by omega, fun q hq => ?_⟩
    simp [show q < state.val by omega]
termination_by A.next.val.length - state.val
decreasing_by omega

theorem end_lt (a : pattern_counts.Atom) (bounded : a.upper.val < 1114112) :
    ∃ size : Usize, (if a.lower.val ≤ a.upper.val ∧ a.upper.val < 1114112 then
        (do
          let i4 ← a.upper - a.lower
          let i5 ← lift (UScalar.cast .Usize i4)
          i5 + 1#usize : Result Usize)
      else ok 0#usize) = ok size ∧ size.val = (Finset.Icc a.lower.val a.upper.val).card := by
  by_cases le : a.lower.val ≤ a.upper.val
  · have cond : a.lower.val ≤ a.upper.val ∧ a.upper.val < 1114112 := ⟨le, bounded⟩
    simp only [cond, ↓reduceIte]
    obtain ⟨d, dRun, dVal⟩ := WP.spec_imp_exists (U32.sub_spec (x := a.upper) (y := a.lower) le)
    have dv : d.val = a.upper.val - a.lower.val := by omega
    have castVal : (UScalar.cast UScalarTy.Usize d).val = d.val := by simp
    obtain ⟨s, sRun, sVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := UScalar.cast UScalarTy.Usize d) (y := 1#usize)
      (by have := usize_big; rw [castVal]; simp; omega))
    refine ⟨s, by simp [dRun, lift, sRun], ?_⟩
    rw [Nat.card_Icc]
    simp at sVal
    omega
  · have cond : ¬ (a.lower.val ≤ a.upper.val ∧ a.upper.val < 1114112) := fun h => le h.1
    simp only [cond, ↓reduceIte]
    refine ⟨0#usize, rfl, ?_⟩
    rw [Nat.card_Icc]
    simp
    omega

/-- The term of an atom in the capped sum of a state. -/
noncomputable def atomTerm (A : pattern_counts.Automaton) (acc : ℕ → Bool) (counts : List Usize) (q a : ℕ) : ℕ :=
  ((jointDfa A acc).atom a).card * (match (jointDfa A acc).next q a with
    | some q' => countsOf counts q'
    | none => 0)

theorem state_sum_spec (A : pattern_counts.Automaton) (acc : ℕ → Bool) (counts : alloc.vec.Vec Usize)
    (cap state atomIndex total : Usize) (hq : state.val < A.next.val.length)
    (bounded : ∀ a ∈ A.atoms.val, a.upper.val < 1114112) (ht : total.val ≤ cap.val) :
    ∃ r : Usize, pattern_counts.state_sum A counts cap state atomIndex total = .ok r ∧
      r.val = capAt cap.val (total.val + ∑ a ∈ Finset.Ico atomIndex.val (jointDfa A acc).atoms,
        atomTerm A acc counts.val state.val a) := by
  rw [pattern_counts.state_sum]
  have row : A.next.val[state.val]? = some A.next.val[state.val] := get_of_lt hq
  by_cases inside : atomIndex.val < A.atoms.val.length
  · have cond : (decide (state.val < A.next.val.length) && decide (atomIndex.val < A.atoms.val.length)) = true := by
      simp [hq, inside]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, cond, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup_vec hq, bind_ok]
    by_cases inRow : atomIndex.val < A.next.val[state.val].val.length
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inRow, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        lookup_vec inRow, lookup_vec inside, bind_ok]
      set target := A.next.val[state.val].val[atomIndex.val] with htarget
      obtain ⟨words, wordsRun, wordsVal⟩ : ∃ words : Usize,
          (if target.val < counts.val.length then counts.index_usize target else ok 0#usize) = ok words ∧
            words.val = countsOf counts.val target.val := by
        by_cases lt : target.val < counts.val.length
        · exact ⟨counts.val[target.val], by simp [lt, lookup_vec lt], by simp [countsOf, get_of_lt lt]⟩
        · refine ⟨0#usize, by simp [lt], ?_⟩
          simp [countsOf, List.getElem?_eq_none (show counts.val.length ≤ target.val by omega)]
      obtain ⟨size, sizeRun, sizeVal⟩ := end_lt A.atoms.val[atomIndex.val]
        (bounded _ (List.getElem_mem inside))
      obtain ⟨prod, prodRun, prodVal⟩ := capped_product_spec size words cap
      obtain ⟨sum, sumRun, sumVal⟩ := capped_sum_spec total prod cap
      obtain ⟨next, advance, nextValue⟩ := add_one inside A.atoms.property
      have sumLe : sum.val ≤ cap.val := by rw [sumVal]; unfold capAt; omega
      obtain ⟨r, run, val⟩ := state_sum_spec A acc counts cap state next sum hq bounded sumLe
      refine ⟨r, ?_, ?_⟩
      · simp only [wordsRun, bind_ok, UScalar.le_equiv, end_val] at *
        simp [wordsRun, UScalar.le_equiv, sizeRun, advance, prodRun, sumRun, run]
      · have atomsIs : (jointDfa A acc).atoms = A.atoms.val.length := rfl
        rw [val, sumVal, prodVal, sizeVal, wordsVal, nextValue, atomsIs,
          Finset.sum_eq_sum_Ico_succ_bot inside]
        have term : atomTerm A acc counts.val state.val atomIndex.val =
            (Finset.Icc A.atoms.val[atomIndex.val].lower.val A.atoms.val[atomIndex.val].upper.val).card *
              countsOf counts.val target.val := by
          simp [atomTerm, jointDfa, get_of_lt inside, row, get_of_lt inRow, htarget]
        rw [term]
        unfold capAt
        omega
    · refine ⟨total, by simp [UScalar.lt_equiv, inRow], ?_⟩
      have zero : ∀ a ∈ Finset.Ico atomIndex.val (jointDfa A acc).atoms, atomTerm A acc counts.val state.val a = 0 := by
        intro a ha
        simp only [Finset.mem_Ico] at ha
        have none : A.next.val[state.val].val[a]? = none := List.getElem?_eq_none (by omega)
        simp [atomTerm, jointDfa, row, none]
      rw [Finset.sum_eq_zero zero, Nat.add_zero]
      unfold capAt
      omega
  · have cond : (decide (state.val < A.next.val.length) && decide (atomIndex.val < A.atoms.val.length)) = false := by
      simp [inside]
    refine ⟨total, by simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, cond, Bool.false_eq_true, ↓reduceIte], ?_⟩
    rw [Finset.Ico_eq_empty (show ¬ atomIndex.val < (jointDfa A acc).atoms by simpa [jointDfa] using inside),
      Finset.sum_empty, Nat.add_zero]
    unfold capAt
    omega
termination_by (jointDfa A acc).atoms - atomIndex.val
decreasing_by simp [jointDfa]; omega

theorem capStep_joint (A : pattern_counts.Automaton) (acc : ℕ → Bool) (cap : ℕ) (counts : List Usize) (q : ℕ) :
    (jointDfa A acc).capStep cap (countsOf counts) q =
      capAt cap (∑ a ∈ Finset.range (jointDfa A acc).atoms, atomTerm A acc counts q a) := by
  unfold Dfa.capStep atomTerm
  rfl

theorem step_from_spec (A : pattern_counts.Automaton) (acc : ℕ → Bool) (counts : alloc.vec.Vec Usize)
    (cap state : Usize) (out : alloc.vec.Vec Usize) (bounded : ∀ a ∈ A.atoms.val, a.upper.val < 1114112)
    (hs : state.val ≤ A.next.val.length) (hout : out.val.length = state.val) :
    ∃ res, pattern_counts.step_from A counts cap state out = .ok res ∧ res.val.length = A.next.val.length ∧
      ∀ q < A.next.val.length, countsOf res.val q =
        if q < state.val then countsOf out.val q
        else (jointDfa A acc).capStep cap.val (countsOf counts.val) q := by
  rw [pattern_counts.step_from]
  by_cases inside : state.val < A.next.val.length
  · obtain ⟨v, vRun, vVal⟩ := state_sum_spec A acc counts cap state 0#usize 0#usize inside bounded (by simp)
    have short : out.val.length < Usize.max := by have := A.next.property; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out v short)
    obtain ⟨next, advance, nextValue⟩ := add_one inside A.next.property
    obtain ⟨res, run, resLen, resVal⟩ := step_from_spec A acc counts cap next pushed bounded (by omega)
      (by rw [contents]; simp [hout, nextValue])
    refine ⟨res, ?_, resLen, fun q hq => ?_⟩
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, vRun, bind_ok, usize_max_val, short,
        decide_true, push, advance, run]
    · rw [resVal q hq, nextValue, contents, countsOf_push, hout]
      by_cases below : q < state.val
      · simp [below, show q < state.val + 1 by omega]
      · by_cases same : q = state.val
        · subst same
          simp only [lt_irrefl, if_false, show state.val < state.val + 1 by omega, if_true]
          rw [vVal, capStep_joint, Finset.range_eq_Ico]
          simp
        · simp [below, same, show ¬ q < state.val + 1 by omega]
  · refine ⟨out, by simp [UScalar.lt_equiv, inside], by omega, fun q hq => ?_⟩
    simp [show q < state.val by omega]
termination_by A.next.val.length - state.val
decreasing_by omega

/-- The capped number of the counted words of a slot of lengths: from `low` on
    and before `high`, the capped sum; without `high`, the value at which the
    capped sums from `low` on settle. -/
def SlotCount (d : Dfa) (cap low : ℕ) : Option ℕ → ℕ → Prop
  | some h, n => n = capAt cap (∑ ℓ ∈ Finset.Ico low h, d.count 0 ℓ)
  | none, n => ∃ M, ∀ N, M ≤ N → n = capAt cap (∑ ℓ ∈ Finset.Ico low N, d.count 0 ℓ)

theorem capAt_full {cap a b : ℕ} (le : a ≤ b) (full : cap ≤ capAt cap a) : capAt cap b = cap := by
  unfold capAt at *; omega

theorem sum_Ico_le (f : ℕ → ℕ) {a b c : ℕ} (h : b ≤ c) : ∑ ℓ ∈ Finset.Ico a b, f ℓ ≤ ∑ ℓ ∈ Finset.Ico a c, f ℓ :=
  Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl h)

theorem sum_Ico_succ (f : ℕ → ℕ) (low length : ℕ) :
    ∑ ℓ ∈ Finset.Ico low (length + 1), f ℓ = ∑ ℓ ∈ Finset.Ico low length, f ℓ + (if low ≤ length then f length else 0) := by
  split_ifs with h
  · exact Finset.sum_Ico_succ_top h f
  · rw [Finset.Ico_eq_empty (by omega), Finset.Ico_eq_empty (by omega)]
    simp

/-- The facts the counting loop keeps: the capped numbers of the words of the
    current length from each state, and the capped sum of the slot so far. -/
theorem count_from_spec (A : pattern_counts.Automaton) (acc : ℕ → Bool) (cap : Usize) (counts : alloc.vec.Vec Usize)
    (length low : Usize) (high : Option Usize) (total fuel : Usize)
    (bounded : ∀ a ∈ A.atoms.val, a.upper.val < 1114112)
    (closed : ∀ q, q < A.next.val.length → ∀ a < (jointDfa A acc).atoms, ∀ q',
      (jointDfa A acc).next q a = some q' → q' < A.next.val.length)
    (pos : 0 < A.next.val.length) (len : counts.val.length = A.next.val.length)
    (inv : ∀ q < A.next.val.length, countsOf counts.val q = (jointDfa A acc).capCounts cap.val length.val q)
    (upTo : ∀ h, high = some h → length.val ≤ h.val) (room : length.val + fuel.val < Usize.max)
    (tot : total.val = capAt cap.val (∑ ℓ ∈ Finset.Ico low.val length.val, (jointDfa A acc).count 0 ℓ)) :
    ∃ res, pattern_counts.count_from A cap counts length low high total fuel = .ok res ∧ ∀ s, res = some s →
      SlotCount (jointDfa A acc) cap.val low.val (high.map (·.val)) s.val := by
  rw [pattern_counts.count_from.eq_def]
  have hasZero : 0 < counts.val.length := by omega
  have zeroVal : (0#usize : Usize).val < counts.val.length := by simpa using hasZero
  have look0 : counts.index_usize 0#usize = .ok (counts.val[0]'hasZero) := by
    simp [alloc.vec.Vec.index_usize, get_of_lt hasZero]
  have hereIs : (counts.val[0]'hasZero).val = capAt cap.val ((jointDfa A acc).count 0 length.val) := by
    have := inv 0 pos
    rw [Rowl.WordCounts.capped_count] at this
    rw [← this]
    simp [countsOf, get_of_lt hasZero]
  obtain ⟨sum, sumRun, sumVal⟩ : ∃ sum : Usize,
      (if low.val ≤ length.val then lengths.capped_sum total (counts.val[0]'hasZero) cap else ok total) = ok sum ∧
        sum.val = capAt cap.val (∑ ℓ ∈ Finset.Ico low.val (length.val + 1), (jointDfa A acc).count 0 ℓ) := by
    by_cases lowLe : low.val ≤ length.val
    · obtain ⟨r, run, val⟩ := capped_sum_spec total (counts.val[0]'hasZero) cap
      refine ⟨r, by simp [lowLe, run], ?_⟩
      rw [val, tot, hereIs, sum_Ico_succ, if_pos lowLe, capAt_add_left, capAt_add_right]
    · refine ⟨total, by simp [lowLe], ?_⟩
      rw [tot, sum_Ico_succ, if_neg lowLe, Nat.add_zero]
  obtain ⟨next, nextRun, nextLen, nextVal⟩ := step_from_spec A acc counts cap 0#usize (alloc.vec.Vec.new Usize)
    bounded (by simp) (by simp)
  have nextIs : ∀ q < A.next.val.length, countsOf next.val q = (jointDfa A acc).capCounts cap.val (length.val + 1) q := by
    intro q hq
    rw [nextVal q hq]
    simp only [show (0#usize : Usize).val = 0 from rfl, Nat.not_lt_zero, if_false]
    exact Rowl.WordCounts.capStep_congr _ cap.val q fun a ha q' h => inv q' (closed q hq a ha q' h)
  have sameRun := Rowl.LengthCounts.same_counts_spec next counts 0#usize
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at sameRun
  have stayOf : next.val = counts.val → ∀ m, length.val ≤ m →
      capAt cap.val ((jointDfa A acc).count 0 m) = (counts.val[0]'hasZero).val := by
    intro fixed m hm
    have stay : ∀ m, length.val ≤ m → ∀ q, q < A.next.val.length →
        (jointDfa A acc).capCounts cap.val m q = (jointDfa A acc).capCounts cap.val length.val q := by
      apply Rowl.WordCounts.steps_fixed_on _ cap.val length.val (· < A.next.val.length) closed
      intro q hq
      rw [← nextIs q hq, ← inv q hq, fixed]
    rw [hereIs, ← Rowl.WordCounts.capped_count, ← Rowl.WordCounts.capped_count]
    exact stay m hm 0 pos
  have common : ∀ s : Usize, cap.val ≤ sum.val → s = sum → ∀ N, length.val + 1 ≤ N →
      s.val = capAt cap.val (∑ ℓ ∈ Finset.Ico low.val N, (jointDfa A acc).count 0 ℓ) := by
    intro s sat hs N hN
    subst hs
    have full : cap.val ≤ capAt cap.val (∑ ℓ ∈ Finset.Ico low.val (length.val + 1), (jointDfa A acc).count 0 ℓ) := by
      rw [← sumVal]; exact sat
    rw [capAt_full (sum_Ico_le _ hN) full, sumVal]
    unfold capAt at full ⊢
    omega
  -- the recursive step
  have recurse : (∀ h, high = some h → length.val < h.val) → next.val ≠ counts.val → ¬ cap.val ≤ sum.val →
      ∃ res, (if (fuel = 0#usize) || (length = core.num.Usize.MAX) then ok none else
          (do
            let i1 ← length + 1#usize
            let i2 ← fuel - 1#usize
            pattern_counts.count_from A cap next i1 low high sum i2 : Result (Option Usize))) = .ok res ∧
        ∀ s, res = some s → SlotCount (jointDfa A acc) cap.val low.val (high.map (·.val)) s.val := by
    intro notEnded _ _
    by_cases stop : fuel.val = 0
    · have : fuel = 0#usize := UScalar.eq_of_val_eq (by simpa using stop)
      simp only [this, decide_true, Bool.true_or, ↓reduceIte]
      exact ⟨none, rfl, by simp⟩
    · have h1 : ¬ fuel = 0#usize := fun h => stop (by simp [h])
      have h2 : ¬ length = core.num.Usize.MAX := fun h => by
        have := congrArg UScalar.val h
        rw [usize_max_val] at this
        omega
      have cond : ((fuel = 0#usize) || (length = core.num.Usize.MAX)) = false := by simp [h1, h2]
      simp only [cond, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨n1, a1, v1⟩ := WP.spec_imp_exists (Usize.add_spec (x := length) (y := 1#usize) (by simp; omega))
      obtain ⟨f1, f1Run, f1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := fuel) (y := 1#usize) (by simp; omega))
      have n1v : n1.val = length.val + 1 := by simpa using v1
      have f1v : f1.val = fuel.val - 1 := by simp at f1Val; omega
      obtain ⟨res, run, resVal⟩ := count_from_spec A acc cap next n1 low high sum f1 bounded closed pos
        (by rw [nextLen]) (by intro q hq; rw [n1v]; exact nextIs q hq)
        (by intro h hh; have := notEnded h hh; omega) (by omega) (by rw [sumVal, n1v])
      exact ⟨res, by simp [a1, f1Run, run], resVal⟩
  cases high with
  | none =>
    simp only [Bool.false_eq_true, ↓reduceIte, alloc.vec.Vec.len_val, UScalar.lt_equiv, hasZero,
      alloc.vec.Vec.index_slice_index, zeroVal, look0, bind_ok, UScalar.le_equiv, sumRun]
    by_cases sat : cap.val ≤ sum.val
    · simp only [sat, decide_true, ↓reduceIte]
      exact ⟨_, rfl, fun s hs => ⟨length.val + 1, common s sat (Option.some.inj hs).symm⟩⟩
    · simp only [sat, decide_false, Bool.false_eq_true, ↓reduceIte, nextRun, sameRun, bind_ok]
      have capPos : 0 < cap.val := by rw [sumVal] at sat; unfold capAt at sat; omega
      by_cases fixed : next.val = counts.val
      · simp only [fixed, decide_true, ↓reduceIte]
        have later := stayOf fixed
        obtain ⟨fromV, fromRun, _⟩ : ∃ fromV : Usize,
            (if low.val ≤ length.val then length + 1#usize else ok low) = ok fromV ∧ True := by
          by_cases lowLe : low.val ≤ length.val
          · obtain ⟨n, a, _⟩ := WP.spec_imp_exists (Usize.add_spec (x := length) (y := 1#usize) (by simp; omega))
            exact ⟨n, by simp [lowLe, a], trivial⟩
          · exact ⟨low, by simp [lowLe], trivial⟩
        simp only [fromRun, bind_ok]
        by_cases zero : (counts.val[0]'hasZero).val = 0
        · have hz : (counts.val[0]'hasZero) = 0#usize := UScalar.eq_of_val_eq (by simpa using zero)
          obtain ⟨r, rRun, rVal⟩ := capped_sum_spec sum 0#usize cap
          simp only [hz, ↓reduceIte, rRun, bind_ok]
          refine ⟨_, rfl, fun s hs => ?_⟩
          simp only [Option.some.injEq] at hs
          subst hs
          refine ⟨length.val + 1, fun N hN => ?_⟩
          have none' : ∀ m, length.val ≤ m → (jointDfa A acc).count 0 m = 0 := by
            intro m hm
            have := later m hm
            rw [zero] at this
            unfold capAt at this
            omega
          have split := Finset.sum_Ico_consecutive (fun ℓ => (jointDfa A acc).count 0 ℓ)
            (show low.val ≤ max low.val (length.val + 1) by omega)
            (show max low.val (length.val + 1) ≤ max N low.val by omega)
          have rest0 : ∑ ℓ ∈ Finset.Ico (max low.val (length.val + 1)) (max N low.val), (jointDfa A acc).count 0 ℓ = 0 :=
            Finset.sum_eq_zero fun m hm => none' m (by simp at hm; omega)
          have first : ∑ ℓ ∈ Finset.Ico low.val (max low.val (length.val + 1)), (jointDfa A acc).count 0 ℓ =
              ∑ ℓ ∈ Finset.Ico low.val (length.val + 1), (jointDfa A acc).count 0 ℓ := by
            by_cases h : low.val ≤ length.val + 1
            · rw [show max low.val (length.val + 1) = length.val + 1 by omega]
            · rw [show max low.val (length.val + 1) = low.val by omega, Finset.Ico_self,
                Finset.Ico_eq_empty (by omega)]
          have whole : ∑ ℓ ∈ Finset.Ico low.val N, (jointDfa A acc).count 0 ℓ =
              ∑ ℓ ∈ Finset.Ico low.val (max N low.val), (jointDfa A acc).count 0 ℓ := by
            by_cases h : low.val ≤ N
            · rw [show max N low.val = N by omega]
            · rw [show max N low.val = low.val by omega, Finset.Ico_self, Finset.Ico_eq_empty (by omega)]
          rw [rVal, sumVal, whole, ← split, rest0, first]
          simp [capAt_capAt]
        · have hnz : ¬ (counts.val[0]'hasZero) = 0#usize := fun h => zero (by simp [h])
          obtain ⟨r, rRun, rVal⟩ := capped_sum_spec sum cap cap
          simp only [hnz, ↓reduceIte, rRun, bind_ok]
          refine ⟨_, rfl, fun s hs => ?_⟩
          simp only [Option.some.injEq] at hs
          subst hs
          have one : ∀ m, length.val ≤ m → 1 ≤ (jointDfa A acc).count 0 m := by
            intro m hm
            have := later m hm
            unfold capAt at this
            omega
          refine ⟨max low.val length.val + cap.val, fun N hN => ?_⟩
          have big : cap.val ≤ ∑ ℓ ∈ Finset.Ico low.val N, (jointDfa A acc).count 0 ℓ := by
            calc cap.val ≤ ∑ ℓ ∈ Finset.Ico (max low.val length.val) N, 1 := by simp; omega
              _ ≤ ∑ ℓ ∈ Finset.Ico (max low.val length.val) N, (jointDfa A acc).count 0 ℓ :=
                Finset.sum_le_sum fun m hm => one m (by simp at hm; omega)
              _ ≤ ∑ ℓ ∈ Finset.Ico low.val N, (jointDfa A acc).count 0 ℓ :=
                Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (by omega) le_rfl)
          rw [rVal]
          unfold capAt at *
          omega
      · simp only [fixed, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact recurse (fun h hh => by cases hh) fixed sat
  | some h =>
    by_cases ended : h.val ≤ length.val
    · simp only [UScalar.le_equiv, ended, decide_true, bind_ok, ↓reduceIte]
      refine ⟨_, rfl, fun s hs => ?_⟩
      simp only [Option.some.injEq] at hs
      subst hs
      have same : length.val = h.val := by have := upTo h rfl; omega
      show total.val = _
      rw [tot, same]
    · simp only [UScalar.le_equiv, ended, decide_false, bind_ok, Bool.false_eq_true, ↓reduceIte,
        alloc.vec.Vec.len_val, UScalar.lt_equiv, zeroVal, alloc.vec.Vec.index_slice_index, look0, sumRun]
      by_cases sat : cap.val ≤ sum.val
      · simp only [sat, decide_true, ↓reduceIte]
        exact ⟨_, rfl, fun s hs => common s sat (Option.some.inj hs).symm h.val (by omega)⟩
      · simp only [sat, decide_false, Bool.false_eq_true, ↓reduceIte, nextRun, sameRun, bind_ok]
        by_cases fixed : next.val = counts.val
        · simp only [fixed, decide_true, ↓reduceIte]
          have later := stayOf fixed
          obtain ⟨fromV, fromRun, fromVal⟩ : ∃ fromV : Usize,
              (if low.val ≤ length.val then length + 1#usize else ok low) = ok fromV ∧
                fromV.val = if low.val ≤ length.val then length.val + 1 else low.val := by
            by_cases lowLe : low.val ≤ length.val
            · obtain ⟨n, a, v⟩ := WP.spec_imp_exists (Usize.add_spec (x := length) (y := 1#usize) (by simp; omega))
              exact ⟨n, by simp [lowLe, a], by simp [lowLe] at v ⊢; omega⟩
            · exact ⟨low, by simp [lowLe], by simp [lowLe]⟩
          simp only [fromRun, bind_ok]
          have tailEq := tail_sum cap.val ((jointDfa A acc).count 0) ((counts.val[0]'hasZero).val) h.val
            (le_refl length.val) later
          by_cases ahead : fromV.val < h.val
          · obtain ⟨restV, restRun, restVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := h) (y := fromV) (by omega))
            obtain ⟨prod, prodRun, prodVal⟩ := capped_product_spec restV (counts.val[0]'hasZero) cap
            obtain ⟨r, rRun, rVal⟩ := capped_sum_spec sum prod cap
            simp only [UScalar.lt_equiv, ahead, decide_true, ↓reduceIte, restRun, prodRun, rRun, bind_ok]
            refine ⟨_, rfl, fun s hs => ?_⟩
            simp only [Option.some.injEq] at hs
            subst hs
            show r.val = _
            have restIs : restV.val = h.val - fromV.val := by omega
            have tail' := tail_sum cap.val ((jointDfa A acc).count 0) ((counts.val[0]'hasZero).val) h.val
              (show length.val ≤ fromV.val by split_ifs at fromVal <;> omega) later
            have split := Finset.sum_Ico_consecutive (fun ℓ => (jointDfa A acc).count 0 ℓ)
              (show low.val ≤ fromV.val by split_ifs at fromVal <;> omega) (show fromV.val ≤ h.val by omega)
            have firstPart : ∑ ℓ ∈ Finset.Ico low.val fromV.val, (jointDfa A acc).count 0 ℓ =
                ∑ ℓ ∈ Finset.Ico low.val (length.val + 1), (jointDfa A acc).count 0 ℓ := by
              split_ifs at fromVal with lowLe
              · rw [fromVal]
              · rw [fromVal, Finset.Ico_self, Finset.Ico_eq_empty (by omega)]
            rw [rVal, prodVal, sumVal, restIs, ← split, firstPart, capAt_add_congr _ _ tail']
            unfold capAt
            omega
          · obtain ⟨r, rRun, rVal⟩ := capped_sum_spec sum 0#usize cap
            simp only [UScalar.lt_equiv, ahead, decide_false, Bool.false_eq_true, ↓reduceIte, rRun, bind_ok]
            refine ⟨_, rfl, fun s hs => ?_⟩
            simp only [Option.some.injEq] at hs
            subst hs
            show r.val = _
            have firstPart : ∑ ℓ ∈ Finset.Ico low.val h.val, (jointDfa A acc).count 0 ℓ =
                ∑ ℓ ∈ Finset.Ico low.val (length.val + 1), (jointDfa A acc).count 0 ℓ := by
              split_ifs at fromVal with lowLe
              · rw [show h.val = length.val + 1 by omega]
              · rw [Finset.Ico_eq_empty (by omega), Finset.Ico_eq_empty (by omega)]
            rw [rVal, sumVal, firstPart]
            simp [capAt_capAt]
        · simp only [fixed, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact recurse (fun h' hh => by cases hh; omega) fixed sat
termination_by fuel.val
decreasing_by all_goals omega

theorem profile_count_spec (A : pattern_counts.Automaton) (first last : U8) (profile : alloc.vec.Vec Bool)
    (low : Usize) (high : Option Usize) (cap : Usize)
    (hr : A.ranks.val.length = A.next.val.length) (ha : A.accepts.val.length = A.next.val.length)
    (bounded : ∀ a ∈ A.atoms.val, a.upper.val < 1114112)
    (closed : ∀ q, q < A.next.val.length → ∀ a < (jointDfa A (profileAccept A first.val last.val profile.val)).atoms,
      ∀ q', (jointDfa A (profileAccept A first.val last.val profile.val)).next q a = some q' →
        q' < A.next.val.length)
    (pos : 0 < A.next.val.length) :
    ∃ res, pattern_counts.profile_count A first last profile low high cap = .ok res ∧ ∀ n, res = some n →
      SlotCount (jointDfa A (profileAccept A first.val last.val profile.val)) cap.val low.val (high.map (·.val))
        n.val := by
  rw [pattern_counts.profile_count]
  obtain ⟨counts, countsRun, countsLen, countsVal⟩ := initial_from_spec A first last profile cap 0#usize
    (alloc.vec.Vec.new Usize) hr ha (by simp) (by simp)
  have big := usize_big
  have settle : pattern_counts.PROFILE_SETTLE.val = 4096 := by simp [pattern_counts.PROFILE_SETTLE]
  obtain ⟨res, run, resVal⟩ := count_from_spec A (profileAccept A first.val last.val profile.val) cap counts 0#usize
    low high 0#usize pattern_counts.PROFILE_SETTLE bounded closed pos countsLen
    (fun q hq => by rw [countsVal q hq]; simp) (by simp) (by simp [settle]; omega) (by simp [capAt])
  exact ⟨res, by simp [countsRun, run], resVal⟩

/-- The words of one length that the kernel counts for a profile. -/
def profileWords (es : List regular.Expression) (first last : ℕ) (profile : List Bool) (ℓ : ℕ) : Set (List ℕ) :=
  {w | w.length = ℓ ∧ ProfileWord es first last profile w}

theorem joint_disjoint {A : pattern_counts.Automaton} (part : Partition (A.atoms.val.map triple)) (acc : ℕ → Bool) :
    (jointDfa A acc).Disjoint := by
  intro a b c ha hb inA inB
  have ha' : a < A.atoms.val.length := ha
  have hb' : b < A.atoms.val.length := hb
  simp only [jointDfa, get_of_lt ha', get_of_lt hb', Finset.mem_Icc] at inA inB
  by_contra ne
  have pw := List.pairwise_iff_getElem.mp part.apart
  rcases Nat.lt_or_gt_of_ne ne with lt | gt
  · exact pw a b (by simpa using ha') (by simpa using hb') lt c (by simpa [triple, InT] using inA)
      (by simpa [triple, InT] using inB)
  · exact pw b a (by simpa using hb') (by simpa using ha') gt c (by simpa [triple, InT] using inB)
      (by simpa [triple, InT] using inA)

/-- The kernel's count of the words of a profile in a slot of lengths: the
    capped number of the words of XML characters whose rank is from `first` on
    and before `last` and that exactly the expressions of `profile` have, with
    lengths from `low` on and before `high`, or, without `high`, the value at
    which these capped numbers settle. -/
theorem profile_count_words {es : alloc.vec.Vec regular.Expression} {A : pattern_counts.Automaton}
    (built : Built es.val A) (first last : U8) (profile : alloc.vec.Vec Bool) (low : Usize) (high : Option Usize)
    (cap : Usize) :
    ∃ res, pattern_counts.profile_count A first last profile low high cap = .ok res ∧ ∀ n, res = some n →
      match high with
      | some h => n.val = capAt cap.val (∑ ℓ ∈ Finset.Ico low.val h.val,
          (profileWords es.val first.val last.val profile.val ℓ).ncard)
      | none => ∃ M, ∀ N, M ≤ N → n.val = capAt cap.val (∑ ℓ ∈ Finset.Ico low.val N,
          (profileWords es.val first.val last.val profile.val ℓ).ncard) := by
  have built' := built
  obtain ⟨nodes, found, _, part, _, start, _, len, agree, ranks, accepts⟩ := built'
  have hr : A.ranks.val.length = A.next.val.length := by
    have := congrArg List.length ranks; simp at this; omega
  have ha : A.accepts.val.length = A.next.val.length := by
    have := congrArg List.length accepts; simp at this; omega
  have bounded : ∀ a ∈ A.atoms.val, a.upper.val < 1114112 := fun a mem =>
    part.bounded (triple a) (List.mem_map_of_mem mem)
  have pos : 0 < A.next.val.length := by
    rw [len]
    cases h : found with
    | nil => rw [h] at start; simp at start
    | cons _ _ => simp
  have closed : ∀ q, q < A.next.val.length → ∀ a < (jointDfa A (profileAccept A first.val last.val profile.val)).atoms,
      ∀ q', (jointDfa A (profileAccept A first.val last.val profile.val)).next q a = some q' →
        q' < A.next.val.length := by
    intro q hq a ha' q' h
    simp only [jointDfa, get_of_lt hq, Option.bind_some] at h
    cases hk : A.next.val[q].val[a]? with
    | none => rw [hk] at h; cases h
    | some t =>
      rw [hk] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨_, each⟩ := agree q A.next.val[q] (get_of_lt hq)
      obtain ⟨jt, _, et, _, _⟩ := each a t A.atoms.val[a] hk (get_of_lt ha')
      have : t.val < found.length := by
        by_contra out
        rw [List.getElem?_eq_none (by omega)] at et
        cases et
      omega
  obtain ⟨res, run, resVal⟩ := profile_count_spec A first last profile low high cap hr ha bounded closed pos
  refine ⟨res, run, fun n hn => ?_⟩
  have counts : ∀ ℓ, (jointDfa A (profileAccept A first.val last.val profile.val)).count 0 ℓ =
      (profileWords es.val first.val last.val profile.val ℓ).ncard := by
    intro ℓ
    rw [← Rowl.WordCounts.accepted_ncard _ (joint_disjoint part _) 0 ℓ]
    congr 1
    ext w
    simp only [Set.mem_setOf_eq, profileWords]
    rw [profile_accepts built]
  have := resVal n hn
  cases high with
  | some h =>
    simp only [SlotCount, Option.map_some] at this
    rw [this]
    simp only [counts]
  | none =>
    obtain ⟨M, hM⟩ := this
    exact ⟨M, fun N hN => by rw [hM N hN]; simp only [counts]⟩

end Rowl.PatternCounts
