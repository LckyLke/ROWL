import Rowl.StringCounts
import Rowl.Datatypes

/-!
The kernel's counting of the values of the length facets (`lengths.rs`).
`lengths::slot_size` returns, when the capped numbers settle within its fuel,
the number of the words with lengths from `low` on and before `high` that the
automaton of the octets or of the strings (`lengthDfa`) takes from its first
state to a counted state, capped at `cap` (`slot_size_spec`): the automata are
those of `Rowl.StringCounts`, the kernel's vectors of capped numbers are
`Rowl.WordCounts.Dfa.capCounts` (`words_from_spec`), and once two lengths have
the same capped numbers every later length has them too. `characters_from`
counts the characters of XML text (`value_length_spec`), and `length_bound`
reads the natural numbers below `lengths::LENGTHS` (`length_bound_spec`).
-/
namespace Rowl.LengthCounts
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open Rowl.WordCounts Rowl.StringCounts
open Rowl.DatatypeMap (TextLength XmlText TextChars)
attribute [local instance low] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ### Capped arithmetic -/

theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

theorem usize_big_enough : 4294967295 ≤ Usize.max := by
  have := Usize.max_def
  rcases System.Platform.numBits_eq with e | e <;> simp_all [Usize.numBits]

theorem capped_sum_spec (left right cap : Usize) :
    ∃ r : Usize, lengths.capped_sum left right cap = .ok r ∧ r.val = capAt cap.val (left.val + right.val) := by
  rw [lengths.capped_sum]
  by_cases lt : left.val < cap.val
  · obtain ⟨room, roomRun, roomVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := cap) (y := left) (by omega))
    by_cases fits : right.val < room.val
    · obtain ⟨sum, sumRun, sumVal⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := left) (y := right) (by scalar_tac))
      refine ⟨sum, by simp [UScalar.lt_equiv, lt, roomRun, fits, sumRun], ?_⟩
      unfold capAt
      omega
    · refine ⟨cap, by simp [UScalar.lt_equiv, lt, roomRun, fits], ?_⟩
      unfold capAt
      omega
  · refine ⟨cap, by simp [UScalar.lt_equiv, lt], ?_⟩
    unfold capAt
    omega

theorem capped_product_spec (left right cap : Usize) :
    ∃ r : Usize, lengths.capped_product left right cap = .ok r ∧ r.val = capAt cap.val (left.val * right.val) := by
  rw [lengths.capped_product]
  by_cases zl : left.val = 0
  · have e : left = 0#usize := UScalar.eq_of_val_eq (by simpa using zl)
    exact ⟨0#usize, by simp [e], by simp [capAt, zl]⟩
  by_cases zr : right.val = 0
  · have e : right = 0#usize := UScalar.eq_of_val_eq (by simpa using zr)
    exact ⟨0#usize, by simp [e], by simp [capAt, zr]⟩
  by_cases zc : cap.val = 0
  · have e : cap = 0#usize := UScalar.eq_of_val_eq (by simpa using zc)
    exact ⟨0#usize, by simp [e], by simp [capAt, zc]⟩
  have nl : ¬ left = 0#usize := fun e => zl (by simp [e])
  have nr : ¬ right = 0#usize := fun e => zr (by simp [e])
  have nc : ¬ cap = 0#usize := fun e => zc (by simp [e])
  obtain ⟨below, belowRun, belowVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := cap) (y := 1#usize) (by
    simp; omega))
  obtain ⟨quot, quotRun, quotVal⟩ := WP.spec_imp_exists (Usize.div_spec below (y := left) zl)
  have belowIs : below.val = cap.val - 1 := by simp at belowVal; exact belowVal.1
  have quotIs : quot.val = (cap.val - 1) / left.val := by rw [quotVal, belowIs]
  by_cases small : right.val ≤ quot.val
  · have bound : left.val * right.val ≤ cap.val - 1 := by
      rw [quotIs] at small
      calc left.val * right.val ≤ left.val * ((cap.val - 1) / left.val) := Nat.mul_le_mul_left _ small
        _ ≤ cap.val - 1 := Nat.mul_div_le _ _
    obtain ⟨prod, prodRun, prodVal⟩ := WP.spec_imp_exists
      (Usize.mul_spec (x := left) (y := right) (by scalar_tac))
    refine ⟨prod, by simp [nl, nr, nc, belowRun, quotRun, UScalar.le_equiv, small, prodRun], ?_⟩
    unfold capAt
    omega
  · refine ⟨cap, by simp [nl, nr, nc, belowRun, quotRun, UScalar.le_equiv, small], ?_⟩
    have big : cap.val ≤ left.val * right.val := by
      rw [quotIs] at small
      have pos : 0 < left.val := by omega
      have h1 : (cap.val - 1) / left.val + 1 ≤ right.val := by omega
      have h2 : cap.val - 1 < left.val * ((cap.val - 1) / left.val + 1) := Nat.lt_mul_div_succ _ pos
      calc cap.val ≤ left.val * ((cap.val - 1) / left.val + 1) := by omega
        _ ≤ left.val * right.val := Nat.mul_le_mul_left _ h1
    unfold capAt
    omega


/-! ### The automata -/

theorem usize_lit_eq (x : Usize) (n : ℕ) (y : Usize) (hy : y.val = n) : x = y ↔ x.val = n := by
  rw [UScalar.eq_equiv, hy]

theorem next_breaks_spec (s a : Usize) :
    ∃ r : Usize, lengths.next_breaks s a = .ok r ∧ r.val = nextBreaks s.val a.val := by
  unfold lengths.next_breaks nextBreaks
  have e0 := usize_lit_eq a 0 0#usize (by simp)
  by_cases h : a.val = 0
  · exact ⟨1#usize, by simp [e0, h], by simp [h]⟩
  · exact ⟨s, by simp [e0, h], by simp [h]⟩

theorem next_colons_spec (s a : Usize) :
    ∃ r : Usize, lengths.next_colons s a = .ok r ∧ r.val = nextColons s.val a.val := by
  unfold lengths.next_colons nextColons
  have e2 := usize_lit_eq a 2 2#usize (by simp)
  by_cases h : a.val = 2
  · exact ⟨1#usize, by simp [e2, h], by simp [h]⟩
  · exact ⟨s, by simp [e2, h], by simp [h]⟩

theorem next_spaces_spec (s a : Usize) :
    ∃ r : Usize, lengths.next_spaces s a = .ok r ∧ r.val = nextSpaces s.val a.val := by
  unfold lengths.next_spaces nextSpaces
  have s3 := usize_lit_eq s 3 3#usize (by simp)
  have s1 := usize_lit_eq s 1 1#usize (by simp)
  have a1 := usize_lit_eq a 1 1#usize (by simp)
  by_cases h3 : s.val = 3
  · exact ⟨3#usize, by simp [s3, h3], by simp [h3]⟩
  · by_cases ha : a.val = 1
    · by_cases h1 : s.val = 1
      · exact ⟨2#usize, by simp [s3, h3, a1, ha, s1, h1], by simp [h3, ha, h1]⟩
      · exact ⟨3#usize, by simp [s3, h3, a1, ha, s1, h1], by simp [h3, ha, h1]⟩
    · exact ⟨1#usize, by simp [s3, h3, a1, ha], by simp [h3, ha]⟩

theorem next_names_spec (s a : Usize) :
    ∃ r : Usize, lengths.next_names s a = .ok r ∧ r.val = nextNames s.val a.val := by
  unfold lengths.next_names lengths.name_atom lengths.start_atom nextNames
  have s0 := usize_lit_eq s 0 0#usize (by simp)
  have a2 := usize_lit_eq a 2 2#usize (by simp)
  have a3 := usize_lit_eq a 3 3#usize (by simp)
  have a6 := usize_lit_eq a 6 6#usize (by simp)
  by_cases hn : 2 ≤ a.val ∧ a.val ≤ 7
  · by_cases h0 : s.val = 0
    · by_cases hs : a.val = 2 ∨ a.val = 3 ∨ a.val = 6
      · refine ⟨2#usize, ?_, by simp [hn, h0, hs]⟩
        simp only [UScalar.le_equiv, s0, a2, a3, a6, h0, hn, true_and]
        rcases hs with h | h | h <;> simp [h]
      · refine ⟨1#usize, ?_, by simp [hn, h0, hs]⟩
        simp only [not_or] at hs
        simp [UScalar.le_equiv, s0, a2, a3, a6, h0, hn, hs]
    · exact ⟨s, by simp [UScalar.le_equiv, s0, h0, hn], by simp [hn, h0]⟩
  · refine ⟨3#usize, ?_, by simp [hn]⟩
    simp only [not_and_or, not_le] at hn
    rcases hn with h | h <;> simp [UScalar.le_equiv, h, Nat.not_le.mpr h]

theorem next_tag_spec (s a : Usize) :
    ∃ r : Usize, lengths.next_tag s a = .ok r ∧ r.val = nextTag s.val a.val := by
  unfold lengths.next_tag nextTag
  have a3 := usize_lit_eq a 3 3#usize (by simp)
  have a4 := usize_lit_eq a 4 4#usize (by simp)
  have a5 := usize_lit_eq a 5 5#usize (by simp)
  have s0 := usize_lit_eq s 0 0#usize (by simp)
  have s8 := usize_lit_eq s 8 8#usize (by simp)
  have s9 := usize_lit_eq s 9 9#usize (by simp)
  have s17 := usize_lit_eq s 17 17#usize (by simp)
  by_cases c1 : 18 ≤ s.val
  · exact ⟨18#usize, by simp [UScalar.le_equiv, c1], by simp [c1]⟩
  · by_cases c2 : a.val = 5
    · by_cases c3 : s.val = 0 ∨ s.val = 9
      · refine ⟨18#usize, ?_, by simp [c1, c2, c3]⟩
        rcases c3 with h | h <;> simp [UScalar.le_equiv, c1, a5, c2, s0, s9, h]
      · refine ⟨9#usize, ?_, by simp [c1, c2, c3]⟩
        simp only [not_or] at c3
        simp [UScalar.le_equiv, c1, a5, c2, s0, s9, c3]
    · by_cases c4 : a.val = 3 ∨ (a.val = 4 ∧ 9 ≤ s.val)
      · by_cases c5 : s.val = 8 ∨ s.val = 17
        · refine ⟨18#usize, ?_, by simp [c1, c2, c4, c5]⟩
          rcases c5 with h | h <;> simp [UScalar.le_equiv, c1, a3, a4, a5, c2, c4, s8, s17, h]
        · obtain ⟨next, nextRun, nextVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := s) (y := 1#usize)
            (by scalar_tac))
          refine ⟨next, ?_, by simp [c1, c2, c4, c5] at *; simpa using nextVal⟩
          simp only [not_or] at c5
          simp [UScalar.le_equiv, c1, a3, a4, a5, c2, c4, s8, s17, c5, nextRun]
      · refine ⟨18#usize, ?_, by simp [c1, c2, c4]⟩
        simp only [not_or, not_and, not_le] at c4
        by_cases h3 : a.val = 3
        · exact absurd h3 c4.1
        · by_cases h4 : a.val = 4
          · simp [UScalar.le_equiv, c1, a3, a4, a5, c2, h3, h4, c4.2 h4]
          · simp [UScalar.le_equiv, c1, a3, a4, a5, c2, h3, h4]


theorem next_text_spec (q a : Usize) (hq : q.val < 1216) :
    ∃ r : Usize, lengths.next_text q a = .ok r ∧ r.val = textNext q.val a.val := by
  rw [lengths.next_text]
  obtain ⟨tag, tagRun, tagVal⟩ := WP.spec_imp_exists (Usize.rem_spec q (y := 19#usize) (by simp))
  obtain ⟨rest, restRun, restVal⟩ := WP.spec_imp_exists (Usize.div_spec q (y := 19#usize) (by simp))
  obtain ⟨colons, colonsRun, colonsVal⟩ := WP.spec_imp_exists (Usize.rem_spec rest (y := 2#usize) (by simp))
  obtain ⟨rest1, rest1Run, rest1Val⟩ := WP.spec_imp_exists (Usize.div_spec rest (y := 2#usize) (by simp))
  obtain ⟨names, namesRun, namesVal⟩ := WP.spec_imp_exists (Usize.rem_spec rest1 (y := 4#usize) (by simp))
  obtain ⟨rest2, rest2Run, rest2Val⟩ := WP.spec_imp_exists (Usize.div_spec rest1 (y := 4#usize) (by simp))
  obtain ⟨spaces, spacesRun, spacesVal⟩ := WP.spec_imp_exists (Usize.rem_spec rest2 (y := 4#usize) (by simp))
  obtain ⟨breaks, breaksRun, breaksVal⟩ := WP.spec_imp_exists (Usize.div_spec rest2 (y := 4#usize) (by simp))
  have tagIs : tag.val = q.val % 19 := by simpa using tagVal
  have restIs : rest.val = q.val / 19 := by simpa using restVal
  have colonsIs : colons.val = q.val / 19 % 2 := by rw [← restIs]; simpa using colonsVal
  have rest1Is : rest1.val = q.val / 19 / 2 := by rw [← restIs]; simpa using rest1Val
  have namesIs : names.val = q.val / 19 / 2 % 4 := by rw [← rest1Is]; simpa using namesVal
  have rest2Is : rest2.val = q.val / 19 / 2 / 4 := by rw [← rest1Is]; simpa using rest2Val
  have spacesIs : spaces.val = q.val / 19 / 2 / 4 % 4 := by rw [← rest2Is]; simpa using spacesVal
  have breaksIs : breaks.val = q.val / 19 / 2 / 4 / 4 := by rw [← rest2Is]; simpa using breaksVal
  obtain ⟨b, bRun, bVal⟩ := next_breaks_spec breaks a
  obtain ⟨sp, spRun, spVal⟩ := next_spaces_spec spaces a
  obtain ⟨n, nRun, nVal⟩ := next_names_spec names a
  obtain ⟨c, cRun, cVal⟩ := next_colons_spec colons a
  obtain ⟨t, tRun, tVal⟩ := next_tag_spec tag a
  obtain ⟨h1, h2, h3, h4, h5⟩ := next_bounds (q.val / 19 / 2 / 4 / 4) (q.val / 19 / 2 / 4 % 4)
    (q.val / 19 / 2 % 4) (q.val / 19 % 2) (q.val % 19) a.val (by omega) (by omega) (by omega) (by omega)
  rw [breaksIs] at bVal
  rw [spacesIs] at spVal
  rw [namesIs] at nVal
  rw [colonsIs] at cVal
  rw [tagIs] at tVal
  obtain ⟨i1, i1Run, i1Val⟩ := WP.spec_imp_exists (Usize.mul_spec (x := b) (y := 4#usize) (by scalar_tac))
  obtain ⟨i3, i3Run, i3Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := i1) (y := sp) (by scalar_tac))
  obtain ⟨i4, i4Run, i4Val⟩ := WP.spec_imp_exists (Usize.mul_spec (x := i3) (y := 4#usize) (by scalar_tac))
  obtain ⟨i6, i6Run, i6Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := i4) (y := n) (by scalar_tac))
  obtain ⟨i7, i7Run, i7Val⟩ := WP.spec_imp_exists (Usize.mul_spec (x := i6) (y := 2#usize) (by scalar_tac))
  obtain ⟨i9, i9Run, i9Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := i7) (y := c) (by scalar_tac))
  obtain ⟨i10, i10Run, i10Val⟩ := WP.spec_imp_exists (Usize.mul_spec (x := i9) (y := 19#usize) (by scalar_tac))
  obtain ⟨r, rRun, rVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := i10) (y := t) (by scalar_tac))
  refine ⟨r, by simp [tagRun, restRun, colonsRun, rest1Run, namesRun, rest2Run, spacesRun, breaksRun, bRun, spRun,
    nRun, cRun, tRun, i1Run, i3Run, i4Run, i6Run, i7Run, i9Run, i10Run, rRun], ?_⟩
  rw [rVal, i10Val, i9Val, i7Val, i6Val, i4Val, i3Val, i1Val, bVal, spVal, nVal, cVal, tVal]
  simp [textNext, joinState]

theorem rank_spec (q : Usize) : ∃ r : U8, lengths.rank q = .ok r ∧ r.val = textRank q.val := by
  obtain ⟨tag, tagRun, tagVal⟩ := WP.spec_imp_exists (Usize.rem_spec q (y := 19#usize) (by simp))
  obtain ⟨rest, restRun, restVal⟩ := WP.spec_imp_exists (Usize.div_spec q (y := 19#usize) (by simp))
  obtain ⟨colons, colonsRun, colonsVal⟩ := WP.spec_imp_exists (Usize.rem_spec rest (y := 2#usize) (by simp))
  obtain ⟨rest1, rest1Run, rest1Val⟩ := WP.spec_imp_exists (Usize.div_spec rest (y := 2#usize) (by simp))
  obtain ⟨names, namesRun, namesVal⟩ := WP.spec_imp_exists (Usize.rem_spec rest1 (y := 4#usize) (by simp))
  obtain ⟨rest2, rest2Run, rest2Val⟩ := WP.spec_imp_exists (Usize.div_spec rest1 (y := 4#usize) (by simp))
  obtain ⟨spaces, spacesRun, spacesVal⟩ := WP.spec_imp_exists (Usize.rem_spec rest2 (y := 4#usize) (by simp))
  obtain ⟨breaks, breaksRun, breaksVal⟩ := WP.spec_imp_exists (Usize.div_spec rest2 (y := 4#usize) (by simp))
  have tagIs : tag.val = q.val % 19 := by simpa using tagVal
  have restIs : rest.val = q.val / 19 := by simpa using restVal
  have colonsIs : colons.val = q.val / 19 % 2 := by rw [← restIs]; simpa using colonsVal
  have rest1Is : rest1.val = q.val / 19 / 2 := by rw [← restIs]; simpa using rest1Val
  have namesIs : names.val = q.val / 19 / 2 % 4 := by rw [← rest1Is]; simpa using namesVal
  have rest2Is : rest2.val = q.val / 19 / 2 / 4 := by rw [← rest1Is]; simpa using rest2Val
  have spacesIs : spaces.val = q.val / 19 / 2 / 4 % 4 := by rw [← rest2Is]; simpa using spacesVal
  have breaksIs : breaks.val = q.val / 19 / 2 / 4 / 4 := by rw [← rest2Is]; simpa using breaksVal
  have runs : lengths.rank q = (if breaks != 0#usize then ok 0#u8 else if 1#usize < spaces then ok 1#u8
      else if (names = 0#usize) || (names = 3#usize) then ok 2#u8 else if names = 1#usize then ok 3#u8
      else if colons != 0#usize then ok 4#u8
      else if ((tag = 0#usize) || (tag = 9#usize)) || (tag = 18#usize) then ok 5#u8 else ok 6#u8) := by
    rw [lengths.rank]
    simp [tagRun, restRun, colonsRun, rest1Run, namesRun, rest2Run, spacesRun, breaksRun]
  rw [runs]
  have e0 := usize_lit_eq breaks 0 0#usize (by simp)
  have n0 := usize_lit_eq names 0 0#usize (by simp)
  have n1 := usize_lit_eq names 1 1#usize (by simp)
  have n3 := usize_lit_eq names 3 3#usize (by simp)
  have c0 := usize_lit_eq colons 0 0#usize (by simp)
  have t0 := usize_lit_eq tag 0 0#usize (by simp)
  have t9 := usize_lit_eq tag 9 9#usize (by simp)
  have t18 := usize_lit_eq tag 18 18#usize (by simp)
  have sp : 1#usize < spaces ↔ 1 < spaces.val := by rw [UScalar.lt_equiv]; simp
  unfold textRank
  rw [← breaksIs, ← spacesIs, ← namesIs, ← colonsIs, ← tagIs]
  by_cases hb : breaks.val ≠ 0
  · exact ⟨0#u8, by simp [e0, hb], by simp [hb]⟩
  · have hb0 : breaks.val = 0 := by omega
    by_cases hs : 1 < spaces.val
    · exact ⟨1#u8, by simp [e0, hb0, sp, hs], by simp [hb0, hs]⟩
    · by_cases hn : names.val = 0 ∨ names.val = 3
      · refine ⟨2#u8, ?_, by simp [hb0, hs, hn]⟩
        rcases hn with h | h <;> simp [e0, hb0, sp, hs, n0, n3, h]
      · simp only [not_or] at hn
        by_cases h1 : names.val = 1
        · exact ⟨3#u8, by simp [e0, hb0, sp, hs, n0, n3, hn, n1, h1], by simp [hb0, hs, hn, h1]⟩
        · by_cases hc : colons.val ≠ 0
          · exact ⟨4#u8, by simp [e0, hb0, sp, hs, n0, n3, hn, n1, h1, c0, hc], by simp [hb0, hs, hn, h1, hc]⟩
          · have hc0 : colons.val = 0 := by omega
            by_cases ht : tag.val = 0 ∨ tag.val = 9 ∨ tag.val = 18
            · refine ⟨5#u8, ?_, by simp [hb0, hs, hn, h1, hc0, ht]⟩
              rcases ht with h | h | h <;> simp [e0, hb0, sp, hs, n0, n3, hn, n1, h1, c0, hc0, t0, t9, t18, h]
            · simp only [not_or] at ht
              exact ⟨6#u8, by simp [e0, hb0, sp, hs, n0, n3, hn, n1, h1, c0, hc0, t0, t9, t18, ht],
                by simp [hb0, hs, hn, h1, hc0, ht]⟩


/-! ### The automaton the kernel counts with -/

/-- The automaton of the octets (`octets`), or of the strings of the ranks
    from `first` on and before `last`. -/
def lengthDfa (octets : Bool) (first last : ℕ) : Dfa := if octets then octetDfa else textDfa first last

/-- The number of its states. -/
def stateCount (octets : Bool) : ℕ := if octets then 1 else 1216

/-- The state after an atom. -/
def nextOf (octets : Bool) (q a : ℕ) : ℕ := if octets then 0 else textNext q a

theorem lengthDfa_atoms (octets : Bool) (first last : ℕ) :
    (lengthDfa octets first last).atoms = if octets then 1 else 9 := by
  cases octets <;> rfl

theorem lengthDfa_next (octets : Bool) (first last q a : ℕ) :
    (lengthDfa octets first last).next q a = some (nextOf octets q a) := by
  cases octets <;> rfl

theorem lengthDfa_card (octets : Bool) (first last a : ℕ) :
    ((lengthDfa octets first last).atom a).card = if octets then 256 else atomSize a := by
  cases octets
  · exact atom_card a
  · simp [lengthDfa, octetDfa]

theorem nextOf_lt (octets : Bool) (q a : ℕ) (hq : q < stateCount octets) : nextOf octets q a < stateCount octets := by
  cases octets
  · exact textNext_lt q a hq
  · simp [nextOf, stateCount]

theorem lengthDfa_closed (octets : Bool) (first last : ℕ) :
    ∀ q, q < stateCount octets → ∀ a < (lengthDfa octets first last).atoms, ∀ q',
      (lengthDfa octets first last).next q a = some q' → q' < stateCount octets := by
  intro q hq a _ q' h
  rw [lengthDfa_next, Option.some.injEq] at h
  rw [← h]
  exact nextOf_lt octets q a hq

/-- The capped numbers of a vector, by state. -/
def countsOf (counts : List Usize) (q : ℕ) : ℕ := (counts[q]?.map (·.val)).getD 0

theorem capStep_length (octets : Bool) (first last cap : ℕ) (v : ℕ → ℕ) (q : ℕ) :
    (lengthDfa octets first last).capStep cap v q = capAt cap (∑ a ∈ Finset.range (lengthDfa octets first last).atoms,
      ((lengthDfa octets first last).atom a).card * v (nextOf octets q a)) := by
  unfold Dfa.capStep
  simp only [lengthDfa_next]

theorem states_spec (octets : Bool) : ∃ r : Usize, lengths.states octets = .ok r ∧ r.val = stateCount octets := by
  cases octets
  · exact ⟨1216#usize, by simp [lengths.states, lengths.TEXT_STATES], rfl⟩
  · exact ⟨1#usize, by simp [lengths.states], rfl⟩

theorem atoms_spec (octets : Bool) (first last : ℕ) :
    ∃ r : Usize, lengths.atoms octets = .ok r ∧ r.val = (lengthDfa octets first last).atoms := by
  rw [lengthDfa_atoms]
  cases octets
  · exact ⟨9#usize, by simp [lengths.atoms], rfl⟩
  · exact ⟨1#usize, by simp [lengths.atoms], rfl⟩

theorem atom_size_spec (octets : Bool) (first last : ℕ) (a : Usize) (ha : a.val < (lengthDfa octets first last).atoms) :
    ∃ r : Usize, lengths.atom_size octets a = .ok r ∧ r.val = ((lengthDfa octets first last).atom a.val).card := by
  rw [lengthDfa_card]
  rw [lengthDfa_atoms] at ha
  cases octets
  · simp only [Bool.false_eq_true, ↓reduceIte] at ha ⊢
    unfold lengths.atom_size
    have e0 := usize_lit_eq a 0 0#usize (by simp)
    have e1 := usize_lit_eq a 1 1#usize (by simp)
    have e2 := usize_lit_eq a 2 2#usize (by simp)
    have e3 := usize_lit_eq a 3 3#usize (by simp)
    have e4 := usize_lit_eq a 4 4#usize (by simp)
    have e5 := usize_lit_eq a 5 5#usize (by simp)
    have e6 := usize_lit_eq a 6 6#usize (by simp)
    have e7 := usize_lit_eq a 7 7#usize (by simp)
    have cases : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 3 ∨ a.val = 4 ∨ a.val = 5 ∨ a.val = 6 ∨ a.val = 7 ∨
        a.val = 8 := by omega
    rcases cases with h | h | h | h | h | h | h | h | h
    · exact ⟨3#usize, by simp [e0, h], by simp [h, atomSize]⟩
    · exact ⟨1#usize, by simp [e0, e1, h], by simp [h, atomSize]⟩
    · exact ⟨1#usize, by simp [e0, e1, e2, h], by simp [h, atomSize]⟩
    · exact ⟨52#usize, by simp [e0, e1, e2, e3, h], by simp [h, atomSize]⟩
    · exact ⟨10#usize, by simp [e0, e1, e2, e3, e4, h], by simp [h, atomSize]⟩
    · exact ⟨1#usize, by simp [e0, e1, e2, e3, e4, e5, h], by simp [h, atomSize]⟩
    · exact ⟨971453#usize, by simp [e0, e1, e2, e3, e4, e5, e6, h], by simp [h, atomSize]⟩
    · exact ⟨116#usize, by simp [e0, e1, e2, e3, e4, e5, e6, e7, h], by simp [h, atomSize]⟩
    · exact ⟨140396#usize, by simp [e0, e1, e2, e3, e4, e5, e6, e7, h], by simp [h, atomSize]⟩
  · exact ⟨256#usize, by simp [lengths.atom_size], rfl⟩

theorem next_state_spec (octets : Bool) (q a : Usize) (hq : q.val < stateCount octets) :
    ∃ r : Usize, lengths.next_state octets q a = .ok r ∧ r.val = nextOf octets q.val a.val := by
  cases octets
  · obtain ⟨r, run, val⟩ := next_text_spec q a hq
    exact ⟨r, by simp [lengths.next_state, run], val⟩
  · exact ⟨0#usize, by simp [lengths.next_state], rfl⟩

theorem accepts_spec (octets : Bool) (first last : U8) (q : Usize) :
    lengths.accepts octets first last q = .ok ((lengthDfa octets first.val last.val).accept q.val) := by
  cases octets
  · obtain ⟨r, run, val⟩ := rank_spec q
    simp only [lengths.accepts, run, bind_ok, Bool.false_eq_true, if_false]
    simp [lengthDfa, textDfa, UScalar.le_equiv, UScalar.lt_equiv, val]
  · simp [lengths.accepts, lengthDfa, octetDfa]

/-! ### The steps of the counts -/

theorem state_step_spec (octets : Bool) (first last : ℕ) (counts : alloc.vec.Vec Usize) (cap state atom total : Usize)
    (hq : state.val < stateCount octets) (len : counts.val.length = stateCount octets) (ht : total.val ≤ cap.val) :
    ∃ r : Usize, lengths.state_step octets counts cap state atom total = .ok r ∧
      r.val = capAt cap.val (total.val + ∑ a ∈ Finset.Ico atom.val (lengthDfa octets first last).atoms,
        ((lengthDfa octets first last).atom a).card * countsOf counts.val (nextOf octets state.val a)) := by
  rw [lengths.state_step]
  obtain ⟨n, nRun, nVal⟩ := atoms_spec octets first last
  by_cases inside : atom.val < (lengthDfa octets first last).atoms
  · have lt : atom.val < n.val := by rw [nVal]; exact inside
    obtain ⟨target, tRun, tVal⟩ := next_state_spec octets state atom hq
    have tLt : target.val < counts.val.length := by rw [tVal, len]; exact nextOf_lt octets _ _ hq
    have lookup : counts.index_usize target = .ok counts.val[target.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem tLt]
    obtain ⟨size, sizeRun, sizeVal⟩ := atom_size_spec octets first last atom inside
    obtain ⟨prod, prodRun, prodVal⟩ := capped_product_spec size counts.val[target.val] cap
    obtain ⟨sum, sumRun, sumVal⟩ := capped_sum_spec total prod cap
    have atomsLe : (lengthDfa octets first last).atoms ≤ 9 := by rw [lengthDfa_atoms]; split_ifs <;> omega
    obtain ⟨next, nextRun, nextVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := atom) (y := 1#usize)
      (by scalar_tac))
    have nextIs : next.val = atom.val + 1 := by simpa using nextVal
    have sumLe : sum.val ≤ cap.val := by rw [sumVal]; unfold capAt; omega
    obtain ⟨r, run, val⟩ := state_step_spec octets first last counts cap state next sum hq len sumLe
    refine ⟨r, by simp [nRun, UScalar.lt_equiv, lt, tRun, tLt, lookup, sizeRun, prodRun, sumRun, nextRun, run], ?_⟩
    have word : countsOf counts.val (nextOf octets state.val atom.val) = counts.val[target.val].val := by
      rw [← tVal]; simp [countsOf, List.getElem?_eq_getElem tLt]
    rw [val, sumVal, prodVal, sizeVal, nextIs, Finset.sum_eq_sum_Ico_succ_bot inside, word]
    unfold capAt
    omega
  · have notLt : ¬ atom.val < n.val := by rw [nVal]; exact inside
    refine ⟨total, by simp [nRun, UScalar.lt_equiv, notLt], ?_⟩
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, Nat.add_zero]
    unfold capAt
    omega
termination_by (lengthDfa octets first last).atoms - atom.val
decreasing_by simp at nextVal; omega


theorem countsOf_push (l : List Usize) (v : Usize) (q : ℕ) :
    countsOf (l ++ [v]) q = if q < l.length then countsOf l q else if q = l.length then v.val else 0 := by
  unfold countsOf
  by_cases lt : q < l.length
  · simp [lt, List.getElem?_append_left lt]
  · by_cases eq : q = l.length
    · subst eq; simp
    · have : l.length + 1 ≤ q := by omega
      simp [lt, eq, List.getElem?_eq_none (show (l ++ [v]).length ≤ q by simp; omega)]

theorem stateCount_le (octets : Bool) : stateCount octets ≤ 1216 := by
  unfold stateCount; split_ifs <;> omega

theorem step_from_spec (octets : Bool) (first last : ℕ) (counts : alloc.vec.Vec Usize) (cap state : Usize)
    (out : alloc.vec.Vec Usize) (len : counts.val.length = stateCount octets) (hs : state.val ≤ stateCount octets)
    (hout : out.val.length = state.val) :
    ∃ res, lengths.step_from octets counts cap state out = .ok res ∧ res.val.length = stateCount octets ∧
      ∀ q < stateCount octets, countsOf res.val q =
        if q < state.val then countsOf out.val q
        else (lengthDfa octets first last).capStep cap.val (countsOf counts.val) q := by
  rw [lengths.step_from]
  obtain ⟨n, nRun, nVal⟩ := states_spec octets
  have big := stateCount_le octets
  by_cases inside : state.val < stateCount octets
  · have lt : state.val < n.val := by rw [nVal]; exact inside
    obtain ⟨v, vRun, vVal⟩ := state_step_spec octets first last counts cap state 0#usize 0#usize inside len (by simp)
    have short : out.val.length < Usize.max := by
      have := usize_big_enough; omega
    have room : alloc.vec.Vec.len out < core.num.Usize.MAX := by
      rw [UScalar.lt_equiv, usize_max_val]; simpa using short
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out v short)
    obtain ⟨next, nextRun, nextVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := state) (y := 1#usize)
      (by scalar_tac))
    have nextIs : next.val = state.val + 1 := by simpa using nextVal
    obtain ⟨res, run, resLen, resVal⟩ := step_from_spec octets first last counts cap next pushed len (by omega)
      (by rw [contents]; simp [hout, nextIs])
    refine ⟨res, by simp [nRun, UScalar.lt_equiv, lt, vRun, room, push, nextRun, run], resLen, fun q hq => ?_⟩
    rw [resVal q hq, nextIs, contents, countsOf_push, hout]
    by_cases below : q < state.val
    · simp [below, show q < state.val + 1 by omega]
    · by_cases same : q = state.val
      · subst same
        simp only [lt_irrefl, if_false, show state.val < state.val + 1 by omega, if_true]
        rw [vVal, capStep_length]
        simp
      · simp [below, same, show ¬ q < state.val + 1 by omega]
  · have notLt : ¬ state.val < n.val := by rw [nVal]; exact inside
    refine ⟨out, by simp [nRun, UScalar.lt_equiv, notLt], by omega, fun q hq => ?_⟩
    simp [show q < state.val by omega]
termination_by stateCount octets - state.val
decreasing_by simp at nextVal; omega

theorem initial_from_spec (octets : Bool) (first last : U8) (cap state : Usize) (out : alloc.vec.Vec Usize)
    (hs : state.val ≤ stateCount octets) (hout : out.val.length = state.val) :
    ∃ res, lengths.initial_from octets first last cap state out = .ok res ∧ res.val.length = stateCount octets ∧
      ∀ q < stateCount octets, countsOf res.val q =
        if q < state.val then countsOf out.val q
        else (lengthDfa octets first.val last.val).capCounts cap.val 0 q := by
  rw [lengths.initial_from]
  obtain ⟨n, nRun, nVal⟩ := states_spec octets
  have big := stateCount_le octets
  by_cases inside : state.val < stateCount octets
  · have lt : state.val < n.val := by rw [nVal]; exact inside
    have acc := accepts_spec octets first last state
    obtain ⟨one, oneRun, oneVal⟩ := capped_sum_spec 0#usize 1#usize cap
    have short : out.val.length < Usize.max := by
      have := usize_big_enough; omega
    have room : alloc.vec.Vec.len out < core.num.Usize.MAX := by
      rw [UScalar.lt_equiv, usize_max_val]; simpa using short
    obtain ⟨next, nextRun, nextVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := state) (y := 1#usize)
      (by scalar_tac))
    have nextIs : next.val = state.val + 1 := by simpa using nextVal
    by_cases yes : (lengthDfa octets first.val last.val).accept state.val = true
    · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out one short)
      obtain ⟨res, run, resLen, resVal⟩ := initial_from_spec octets first last cap next pushed (by omega)
        (by rw [contents]; simp [hout, nextIs])
      refine ⟨res, by simp [nRun, UScalar.lt_equiv, lt, acc, yes, oneRun, room, push, nextRun, run], resLen,
        fun q hq => ?_⟩
      rw [resVal q hq, nextIs, contents, countsOf_push, hout]
      by_cases below : q < state.val
      · simp [below, show q < state.val + 1 by omega]
      · by_cases same : q = state.val
        · subst same
          simp only [lt_irrefl, if_false, show state.val < state.val + 1 by omega, if_true]
          rw [oneVal]
          simp [Dfa.capCounts, yes]
        · simp [below, same, show ¬ q < state.val + 1 by omega]
    · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out 0#usize short)
      obtain ⟨res, run, resLen, resVal⟩ := initial_from_spec octets first last cap next pushed (by omega)
        (by rw [contents]; simp [hout, nextIs])
      refine ⟨res, by simp [nRun, UScalar.lt_equiv, lt, acc, yes, room, push, nextRun, run], resLen,
        fun q hq => ?_⟩
      rw [resVal q hq, nextIs, contents, countsOf_push, hout]
      by_cases below : q < state.val
      · simp [below, show q < state.val + 1 by omega]
      · by_cases same : q = state.val
        · subst same
          simp only [lt_irrefl, if_false, show state.val < state.val + 1 by omega, if_true]
          simp [Dfa.capCounts, yes, capAt]
        · simp [below, same, show ¬ q < state.val + 1 by omega]
  · have notLt : ¬ state.val < n.val := by rw [nVal]; exact inside
    refine ⟨out, by simp [nRun, UScalar.lt_equiv, notLt], by omega, fun q hq => ?_⟩
    simp [show q < state.val by omega]
termination_by stateCount octets - state.val
decreasing_by all_goals (simp at nextVal; omega)

theorem same_counts_spec (left right : alloc.vec.Vec Usize) (index : Usize) :
    lengths.same_counts left right index = .ok (decide (left.val.drop index.val = right.val.drop index.val)) := by
  rw [lengths.same_counts]
  by_cases inLeft : index.val < left.val.length
  · have lookL : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inLeft]
    by_cases inRight : index.val < right.val.length
    · have lookR : right.index_usize index = .ok right.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inRight]
      obtain ⟨next, nextRun, nextVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextVal
      have ih := same_counts_spec left right next
      rw [nextIs] at ih
      have split : (left.val.drop index.val = right.val.drop index.val) ↔
          left.val[index.val] = right.val[index.val] ∧
            left.val.drop (index.val + 1) = right.val.drop (index.val + 1) := by
        rw [List.drop_eq_getElem_cons inLeft, List.drop_eq_getElem_cons inRight, List.cons.injEq]
      by_cases same : left.val[index.val] = right.val[index.val]
      · simp [UScalar.lt_equiv, inLeft, inRight, alloc.vec.Vec.index_slice_index, lookL, lookR, same, nextRun, ih,
          split]
      · simp [UScalar.lt_equiv, inLeft, inRight, alloc.vec.Vec.index_slice_index, lookL, lookR, same, split]
    · have differ : left.val.drop index.val ≠ right.val.drop index.val := by
        rw [List.drop_eq_nil_iff.mpr (show right.val.length ≤ index.val by omega)]
        exact List.ne_nil_of_length_pos (by simp; omega)
      simp [UScalar.lt_equiv, inLeft, inRight, differ]
  · have done : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [UScalar.lt_equiv, inLeft, done, List.drop_eq_nil_iff, UScalar.le_equiv]
termination_by left.val.length - index.val
decreasing_by simp at nextVal; omega


/-! ### The words of a slot of lengths -/

theorem stateCount_pos (octets : Bool) : 0 < stateCount octets := by
  unfold stateCount; split_ifs <;> omega

/-- The capped sum of counts whose capped values from `a` on are all `c`. -/
theorem tail_sum (cap : ℕ) (f : ℕ → ℕ) {a b : ℕ} (c high : ℕ) (hab : a ≤ b)
    (later : ∀ m, a ≤ m → capAt cap (f m) = c) :
    capAt cap (∑ m ∈ Finset.Ico b high, f m) = capAt cap ((high - b) * c) := by
  rw [capAt_sum, Finset.sum_congr rfl fun m hm => later m (by simp at hm; omega)]
  simp

theorem capAt_add_congr (cap a : ℕ) {b b' : ℕ} (h : capAt cap b = capAt cap b') :
    capAt cap (a + b) = capAt cap (a + b') := by
  rw [← capAt_add_right, h, capAt_add_right]

theorem words_from_spec (octets : Bool) (first last : ℕ) (cap : Usize) (counts : alloc.vec.Vec Usize)
    (length low high total fuel : Usize)
    (len : counts.val.length = stateCount octets)
    (inv : ∀ q < stateCount octets, countsOf counts.val q = (lengthDfa octets first last).capCounts cap.val length.val q)
    (upTo : length.val ≤ high.val)
    (tot : total.val = capAt cap.val (∑ ℓ ∈ Finset.Ico low.val length.val, (lengthDfa octets first last).count 0 ℓ)) :
    ∃ res, lengths.words_from octets cap counts length low high total fuel = .ok res ∧ ∀ s, res = some s →
      s.val = capAt cap.val (∑ ℓ ∈ Finset.Ico low.val high.val, (lengthDfa octets first last).count 0 ℓ) := by
  rw [lengths.words_from]
  by_cases done : high.val ≤ length.val
  · have same : length.val = high.val := by omega
    refine ⟨some total, by simp [UScalar.le_equiv, done], fun s hs => ?_⟩
    simp only [Option.some.injEq] at hs
    rw [← hs, tot, same]
  · have pos := stateCount_pos octets
    have hasZero : 0 < counts.val.length := by omega
    have look0 : counts.index_usize 0#usize = .ok (counts.val[0]'hasZero) := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hasZero]
    have hereIs : (counts.val[0]'hasZero).val = capAt cap.val ((lengthDfa octets first last).count 0 length.val) := by
      have := inv 0 pos
      rw [Rowl.WordCounts.capped_count] at this
      rw [← this]
      simp [countsOf, List.getElem?_eq_getElem hasZero]
    obtain ⟨next, nextRun, nextLen, nextVal⟩ := step_from_spec octets first last counts cap 0#usize
      (alloc.vec.Vec.new Usize) len (by simp) (by simp)
    have nextIs : ∀ q < stateCount octets,
        countsOf next.val q = (lengthDfa octets first last).capCounts cap.val (length.val + 1) q := by
      intro q hq
      rw [nextVal q hq]
      simp only [show (0#usize : Usize).val = 0 from rfl, Nat.not_lt_zero, if_false]
      exact Rowl.WordCounts.capStep_congr _ cap.val q fun a ha q' h => inv q' (lengthDfa_closed octets first last q hq a ha q' h)
    have sameRun := same_counts_spec next counts 0#usize
    simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at sameRun
    by_cases fixed : next.val = counts.val
    · have stay : ∀ m, length.val ≤ m → ∀ q, q < stateCount octets →
          (lengthDfa octets first last).capCounts cap.val m q =
            (lengthDfa octets first last).capCounts cap.val length.val q := by
        apply Rowl.WordCounts.steps_fixed_on _ cap.val length.val (· < stateCount octets) (lengthDfa_closed octets first last)
        intro q hq
        rw [← nextIs q hq, ← inv q hq, fixed]
      have later : ∀ m, length.val ≤ m → capAt cap.val ((lengthDfa octets first last).count 0 m) =
          (counts.val[0]'hasZero).val := by
        intro m hm
        rw [hereIs, ← Rowl.WordCounts.capped_count, ← Rowl.WordCounts.capped_count]
        exact stay m hm 0 pos
      have start : (0#usize : Usize) < alloc.vec.Vec.len counts := by
        rw [UScalar.lt_equiv]; simpa using hasZero
      by_cases early : low.val < length.val
      · obtain ⟨rest, restRun, restVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := high) (y := length)
          (by omega))
        have restIs : rest.val = high.val - length.val := by simpa using restVal.1
        obtain ⟨prod, prodRun, prodVal⟩ := capped_product_spec rest (counts.val[0]'hasZero) cap
        obtain ⟨sum, sumRun, sumVal⟩ := capped_sum_spec total prod cap
        refine ⟨some sum, ?_, fun s hs => ?_⟩
        · simp [UScalar.le_equiv, done, start, look0, nextRun, sameRun, fixed, UScalar.lt_equiv, early,
            show length.val < high.val by omega, restRun, prodRun, sumRun]
        · simp only [Option.some.injEq] at hs
          have tail := tail_sum cap.val ((lengthDfa octets first last).count 0) ((counts.val[0]'hasZero).val)
            high.val (le_refl length.val) later
          rw [← hs, sumVal, prodVal, tot, restIs, ← Finset.sum_Ico_consecutive _ (le_of_lt early) upTo,
            capAt_add_congr _ _ tail]
          unfold capAt
          omega
      · by_cases ahead : low.val < high.val
        · obtain ⟨rest, restRun, restVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := high) (y := low)
            (by omega))
          have restIs : rest.val = high.val - low.val := by simpa using restVal.1
          obtain ⟨prod, prodRun, prodVal⟩ := capped_product_spec rest (counts.val[0]'hasZero) cap
          obtain ⟨sum, sumRun, sumVal⟩ := capped_sum_spec total prod cap
          refine ⟨some sum, ?_, fun s hs => ?_⟩
          · simp [UScalar.le_equiv, done, start, look0, nextRun, sameRun, fixed, UScalar.lt_equiv, early, ahead,
              restRun, prodRun, sumRun]
          · simp only [Option.some.injEq] at hs
            have empty : Finset.Ico low.val length.val = ∅ := Finset.Ico_eq_empty (by omega)
            rw [empty, Finset.sum_empty] at tot
            have tail := tail_sum cap.val ((lengthDfa octets first last).count 0) ((counts.val[0]'hasZero).val)
              high.val (show length.val ≤ low.val by omega) later
            rw [← hs, sumVal, prodVal, tot, restIs, tail]
            unfold capAt
            omega
        · obtain ⟨prod, prodRun, prodVal⟩ := capped_product_spec 0#usize (counts.val[0]'hasZero) cap
          obtain ⟨sum, sumRun, sumVal⟩ := capped_sum_spec total prod cap
          refine ⟨some sum, ?_, fun s hs => ?_⟩
          · simp [UScalar.le_equiv, done, start, look0, nextRun, sameRun, fixed, UScalar.lt_equiv, early, ahead,
              prodRun, sumRun]
          · simp only [Option.some.injEq] at hs
            have empty : Finset.Ico low.val length.val = ∅ := Finset.Ico_eq_empty (by omega)
            rw [empty, Finset.sum_empty] at tot
            rw [← hs, sumVal, prodVal, tot, Finset.Ico_eq_empty (show ¬ low.val < high.val from ahead)]
            simp [capAt]
    · have start : (0#usize : Usize) < alloc.vec.Vec.len counts := by
        rw [UScalar.lt_equiv]; simpa using hasZero
      by_cases out : fuel.val = 0
      · have e : fuel = 0#usize := UScalar.eq_of_val_eq (by simpa using out)
        refine ⟨none, by simp [UScalar.le_equiv, done, start, look0, nextRun, sameRun, fixed, e], fun s hs => ?_⟩
        cases hs
      · have ne : ¬ fuel = 0#usize := fun e => out (by simp [e])
        obtain ⟨next1, next1Run, next1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := length) (y := 1#usize)
          (by scalar_tac))
        have next1Is : next1.val = length.val + 1 := by simpa using next1Val
        obtain ⟨fuel1, fuel1Run, fuel1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := fuel) (y := 1#usize)
          (by simp; omega))
        have fuel1Is : fuel1.val = fuel.val - 1 := by simpa using fuel1Val.1
        have nextInv : ∀ q < stateCount octets, countsOf next.val q =
            (lengthDfa octets first last).capCounts cap.val next1.val q := by
          intro q hq; rw [next1Is]; exact nextIs q hq
        by_cases counted : low.val ≤ length.val
        · obtain ⟨sum, sumRun, sumVal⟩ := capped_sum_spec total (counts.val[0]'hasZero) cap
          obtain ⟨res, run, resVal⟩ := words_from_spec octets first last cap next next1 low high sum fuel1
            nextLen nextInv (by omega) (by
              rw [sumVal, hereIs, tot, next1Is, Finset.sum_Ico_succ_top counted, capAt_add_left, capAt_add_right])
          refine ⟨res, ?_, resVal⟩
          simp [UScalar.le_equiv, done, start, look0, nextRun, sameRun, fixed, ne, counted, sumRun, next1Run,
            fuel1Run, run]
        · obtain ⟨res, run, resVal⟩ := words_from_spec octets first last cap next next1 low high total fuel1
            nextLen nextInv (by omega) (by
              rw [tot, next1Is, Finset.Ico_eq_empty (show ¬ low.val < length.val by omega),
                Finset.Ico_eq_empty (show ¬ low.val < length.val + 1 by omega)])
          refine ⟨res, ?_, resVal⟩
          simp [UScalar.le_equiv, done, start, look0, nextRun, sameRun, fixed, ne, counted, next1Run, fuel1Run, run]
termination_by fuel.val
decreasing_by all_goals omega

/-- The kernel's count of the words with lengths from `low` on and before
    `high`, when the capped numbers settle: the words that the automaton
    counts, capped. -/
theorem slot_size_spec (octets : Bool) (first last : U8) (low high cap : Usize) :
    ∃ res, lengths.slot_size octets first last low high cap = .ok res ∧ ∀ s, res = some s →
      s.val = capAt cap.val (∑ ℓ ∈ Finset.Ico low.val high.val,
        (lengthDfa octets first.val last.val).count 0 ℓ) := by
  rw [lengths.slot_size]
  obtain ⟨counts, countsRun, countsLen, countsVal⟩ := initial_from_spec octets first last cap 0#usize
    (alloc.vec.Vec.new Usize) (by simp) (by simp)
  obtain ⟨res, run, resVal⟩ := words_from_spec octets first.val last.val cap counts 0#usize low high 0#usize
    lengths.SETTLE countsLen (fun q hq => by
      rw [countsVal q hq]; simp) (by simp) (by simp [capAt])
  exact ⟨res, by simp [countsRun, run], resVal⟩

/-! ### The lengths of values -/

/-- The bytes that start a character of UTF-8 text: no continuation bytes. -/
def charStarts (bs : List U8) : ℕ := (bs.filter fun b => decide (b.val < 128 ∨ 192 ≤ b.val)).length

theorem charStarts_append (a b : List U8) : charStarts (a ++ b) = charStarts a + charStarts b := by
  simp [charStarts, List.filter_append]

theorem charStarts_utf8 {c : ℕ} (high : c ≤ 1114111) : charStarts ((Rowl.IriResolution.utf8 c).map toByte) = 1 := by
  by_cases small : c < 128
  · rw [utf8_ascii small]
    simp [charStarts, toByte_val (show c < 256 by omega), small]
  · obtain ⟨b, rest, e, hb1, hb2, hr, _⟩ := utf8_high (by omega) high
    rw [e]
    have restNone : (rest.map toByte).filter (fun x => decide (x.val < 128 ∨ 192 ≤ x.val)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x mem
      obtain ⟨y, my, rfl⟩ := List.mem_map.mp mem
      have := hr y my
      rw [toByte_val (by omega)]
      simp only [decide_eq_true_eq, not_or, not_lt]
      omega
    simp only [charStarts, List.map_cons, List.filter_cons, toByte_val hb2]
    rw [if_pos (by simp; omega), restNone]
    rfl

theorem charStarts_encode {w : List ℕ} (high : ∀ c ∈ w, c ≤ 1114111) : charStarts (encodeText w) = w.length := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [encodeText_cons, charStarts_append, charStarts_utf8 (high c (by simp)),
      ih (fun d m => high d (List.mem_cons_of_mem c m))]
    simp [Nat.add_comm]

/-- The characters of XML text are its starts of characters. -/
theorem text_length_starts {t : List U8} {n : ℕ} (h : TextLength t n) : charStarts t = n := by
  obtain ⟨w, chars, rfl⟩ := h
  obtain ⟨xml, rfl⟩ := chars_encode chars
  exact charStarts_encode fun c m => xml_high (xml c m)

theorem xml_text_length {t : List U8} (h : XmlText t) : TextLength t (charStarts t) := by
  obtain ⟨text, from0⟩ := h
  have chars : TextChars t (text.map Prod.fst) := ⟨text, from0, rfl⟩
  exact ⟨_, chars, (text_length_starts ⟨_, chars, rfl⟩).symm⟩

theorem characters_from_spec (bytes : alloc.vec.Vec U8) (index count : Usize)
    (room : count.val + (bytes.val.length - index.val) ≤ Usize.max) :
    ∃ r : Usize, lengths.characters_from bytes index count = .ok r ∧
      r.val = count.val + charStarts (bytes.val.drop index.val) := by
  rw [lengths.characters_from]
  by_cases inside : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, nextRun, nextVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
      (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextVal
    have split : charStarts (bytes.val.drop index.val) =
        (if bytes.val[index.val].val < 128 ∨ 192 ≤ bytes.val[index.val].val then 1 else 0) +
          charStarts (bytes.val.drop (index.val + 1)) := by
      rw [List.drop_eq_getElem_cons inside]
      simp only [charStarts, List.filter_cons]
      split_ifs with h1 h2 h2 <;> simp_all [Nat.add_comm]
    by_cases start : bytes.val[index.val].val < 128 ∨ 192 ≤ bytes.val[index.val].val
    · obtain ⟨count1, c1Run, c1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := count) (y := 1#usize)
        (by scalar_tac))
      have c1Is : count1.val = count.val + 1 := by simpa using c1Val
      obtain ⟨r, run, val⟩ := characters_from_spec bytes next count1 (by rw [c1Is, nextIs]; omega)
      refine ⟨r, by simp [UScalar.lt_equiv, UScalar.le_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, start,
        nextRun, c1Run, run], ?_⟩
      rw [val, c1Is, nextIs, split, if_pos start]
      omega
    · obtain ⟨r, run, val⟩ := characters_from_spec bytes next count (by rw [nextIs]; omega)
      have s1 : ¬ bytes.val[index.val].val < 128 := fun h => start (.inl h)
      have s2 : ¬ 192 ≤ bytes.val[index.val].val := fun h => start (.inr h)
      refine ⟨r, by simp [UScalar.lt_equiv, UScalar.le_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, s1, s2,
        nextRun, run], ?_⟩
      rw [val, nextIs, split, if_neg start]
      omega
  · refine ⟨count, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show bytes.val.length ≤ index.val by omega), charStarts]
termination_by bytes.val.length - index.val
decreasing_by all_goals (simp at nextVal; omega)

/-- The length of a kernel value of a datatype with the length facets: the
    characters of a string, of the string of a plain literal with a language
    tag and of an IRI, and the octets of binary data. -/
def ValueLength : datatypes.DataValue → ℕ → Prop
  | .Text t, n => TextLength t.val n
  | .Tagged t _, n => TextLength t.val n
  | .Uri t, n => TextLength t.val n
  | .Hex o, n => o.val.length = n
  | .Base64 o, n => o.val.length = n
  | _, _ => False

theorem value_length_unique {v : datatypes.DataValue} {m n : ℕ} (hm : ValueLength v m) (hn : ValueLength v n) :
    m = n := by
  cases v <;> simp only [ValueLength] at hm hn
  all_goals first | exact text_length_unique hm hn | omega

theorem value_length_spec (v : datatypes.DataValue) (cv : Rowl.Datatypes.Canonical v) :
    ∃ r, lengths.value_length v = .ok r ∧ ∀ n, ValueLength v n ↔ ∃ m : Usize, r = some m ∧ m.val = n := by
  have text : ∀ t : alloc.vec.Vec U8, XmlText t.val → ∃ r : Usize,
      lengths.characters_from t 0#usize 0#usize = .ok r ∧ ∀ n, TextLength t.val n ↔ r.val = n := by
    intro t xt
    obtain ⟨r, run, val⟩ := characters_from_spec t 0#usize 0#usize (by simp)
    simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, Nat.zero_add] at val
    refine ⟨r, run, fun n => ?_⟩
    rw [val]
    constructor
    · exact text_length_starts
    · rintro rfl; exact xml_text_length xt
  cases v with
  | Text t =>
    obtain ⟨r, run, val⟩ := text t cv
    exact ⟨some r, by simp [lengths.value_length, run], fun n => by simp [ValueLength, val]⟩
  | Tagged t m =>
    obtain ⟨r, run, val⟩ := text t cv.1
    exact ⟨some r, by simp [lengths.value_length, run], fun n => by simp [ValueLength, val]⟩
  | Uri t =>
    obtain ⟨r, run, val⟩ := text t cv
    exact ⟨some r, by simp [lengths.value_length, run], fun n => by simp [ValueLength, val]⟩
  | Hex o => exact ⟨some (alloc.vec.Vec.len o), by simp [lengths.value_length], fun n => by simp [ValueLength]⟩
  | Base64 o => exact ⟨some (alloc.vec.Vec.len o), by simp [lengths.value_length], fun n => by simp [ValueLength]⟩
  | _ => exact ⟨none, by simp [lengths.value_length], fun n => by simp [ValueLength]⟩

/-! ### The bounds of the length facets -/

/-- `lengths::LENGTHS`. -/
def lengthLimit : ℕ := Usize.max / 16

theorem lengths_val : ∃ l : Usize, lengths.LENGTHS = .ok l ∧ l.val = lengthLimit := by
  obtain ⟨l, run, val⟩ := WP.spec_imp_exists (Usize.div_spec core.num.Usize.MAX (y := 16#usize) (by simp))
  exact ⟨l, by simp [lengths.LENGTHS, run], by rw [val, usize_max_val]; rfl⟩

/-- The value of the digits after `value`. -/
def digitsFrom (value : ℕ) (digits : List U8) : ℕ := digits.foldl (fun v b => 10 * v + (b.val - 48)) value

theorem digits_value_spec (digits : alloc.vec.Vec U8) (index value : Usize) :
    ∃ r, lengths.digits_value digits index value = .ok r ∧ ∀ n : Usize, r = some n →
      Rowl.DatatypeMap.Digits (digits.val.drop index.val) ∧
        n.val = digitsFrom value.val (digits.val.drop index.val) ∧ n.val < lengthLimit := by
  rw [lengths.digits_value]
  obtain ⟨l, lRun, lVal⟩ := lengths_val
  by_cases inside : index.val < digits.val.length
  · have lookup : digits.index_usize index = .ok digits.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨tenth, tRun, tVal⟩ := WP.spec_imp_exists (Usize.div_spec l (y := 10#usize) (by simp))
    have tIs : tenth.val = lengthLimit / 10 := by rw [tVal, lVal]; rfl
    by_cases good : 48 ≤ digits.val[index.val].val ∧ digits.val[index.val].val ≤ 57 ∧ value.val < lengthLimit / 10
    · have limit : lengthLimit ≤ Usize.max := Nat.div_le_self _ _
      obtain ⟨d, dRun, dVal⟩ := WP.spec_imp_exists (U8.sub_spec (x := digits.val[index.val]) (y := 48#u8)
        (by simp; omega))
      obtain ⟨tens, tensRun, tensVal⟩ := WP.spec_imp_exists (Usize.mul_spec (x := value) (y := 10#usize)
        (by simp; omega))
      obtain ⟨sum, sumRun, sumVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := tens) (y := UScalar.cast .Usize d)
        (by simp at tensVal dVal ⊢; omega))
      obtain ⟨next, nextRun, nextVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextVal
      have sumIs : sum.val = 10 * value.val + (digits.val[index.val].val - 48) := by
        simp at sumVal tensVal dVal
        omega
      obtain ⟨r, run, val⟩ := digits_value_spec digits next sum
      have small : value.val < tenth.val := by rw [tIs]; exact good.2.2
      refine ⟨r, by simp [UScalar.lt_equiv, UScalar.le_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, lRun,
        tRun, good.1, good.2.1, small, dRun, tensRun, lift, sumRun, nextRun, run], fun n hn => ?_⟩
      obtain ⟨digitsOk, value', small⟩ := val n hn
      rw [nextIs] at digitsOk value'
      rw [List.drop_eq_getElem_cons inside]
      refine ⟨fun b mem => ?_, ?_, small⟩
      · rcases List.mem_cons.mp mem with rfl | m
        · exact ⟨good.1, good.2.1⟩
        · exact digitsOk b m
      · rw [value', sumIs, digitsFrom, digitsFrom, List.foldl_cons]
    · refine ⟨none, ?_, fun n hn => by cases hn⟩
      have g : ¬ ((48 ≤ digits.val[index.val].val ∧ digits.val[index.val].val ≤ 57) ∧ value.val < tenth.val) := by
        rw [tIs]; tauto
      simp [UScalar.lt_equiv, UScalar.le_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, lRun, tRun, g]
      intro h1 h2 h3
      exact absurd ⟨⟨h1, h2⟩, h3⟩ g
  · have done : digits.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    by_cases small : value.val < lengthLimit
    · refine ⟨some value, by simp [UScalar.lt_equiv, inside, lRun, lVal, small], fun n hn => ?_⟩
      simp only [Option.some.injEq] at hn
      subst hn
      rw [done]
      exact ⟨fun b mem => by simp at mem, rfl, small⟩
    · exact ⟨none, by simp [UScalar.lt_equiv, inside, lRun, lVal, small], fun n hn => by cases hn⟩
termination_by digits.val.length - index.val
decreasing_by simp at nextVal; omega

/-- The bound of a length facet: a natural number below `lengthLimit`, written
    without fraction. -/
theorem length_bound_spec (v : datatypes.DataValue) :
    ∃ r, lengths.length_bound v = .ok r ∧ ∀ n : Usize, r = some n →
      ∃ whole fraction, v = .Number false whole fraction ∧ fraction.val = [] ∧
        Rowl.DatatypeMap.Digits whole.val ∧ n.val = Rowl.DatatypeMap.digitsValue whole.val ∧ n.val < lengthLimit := by
  cases v with
  | Number negative whole fraction =>
    by_cases ok : negative = false ∧ fraction.val = []
    · obtain ⟨rfl, empty⟩ := ok
      obtain ⟨r, run, val⟩ := digits_value_spec whole 0#usize 0#usize
      have len : alloc.vec.Vec.len fraction = 0#usize := by
        apply UScalar.eq_of_val_eq; simp [empty]
      refine ⟨r, by simp [lengths.length_bound, len, run], fun n hn => ?_⟩
      obtain ⟨digits, value, small⟩ := val n hn
      simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at digits value
      exact ⟨whole, fraction, rfl, empty, digits, value, small⟩
    · refine ⟨none, ?_, fun n hn => by cases hn⟩
      simp only [lengths.length_bound]
      by_cases neg : negative = false
      · have : fraction.val ≠ [] := fun e => ok ⟨neg, e⟩
        have len : ¬ alloc.vec.Vec.len fraction = 0#usize := by
          intro e; apply this; have := congrArg UScalar.val e; simpa using this
        simp [neg, len]
      · simp [neg]
  | _ => exact ⟨none, by simp [lengths.length_bound], fun n hn => by cases hn⟩

end Rowl.LengthCounts
