import Rowl.XmlGrammar

/-!
# The scanners of the XML reader

Exact results of the small functions of `xml.rs`: characters at positions,
character classes, white space, names, literal words, comments, processing
instructions, CDATA sections, character data and references. Each scanner is
characterized as a function of the input word from its position, so that the
grammar proofs in `XmlContent.lean` can use it in both directions.
-/

namespace Rowl.XmlScan
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## Positions in a buffer -/

/-- The code point of a buffer at a position, 0 past its end. -/
def charAt (cs : alloc.vec.Vec U32) (i : Nat) : Nat := ((word cs)[i]?).getD 0

/-- The `U32` that `xml.at` returns. -/
def atU (cs : alloc.vec.Vec U32) (i : Nat) : U32 := (cs.val[i]?).getD 0#u32

theorem word_length (cs : alloc.vec.Vec U32) : (word cs).length = cs.val.length := by
  simp [word]

theorem word_getElem_opt (cs : alloc.vec.Vec U32) (i : Nat) :
    (word cs)[i]? = cs.val[i]?.map (·.val) := by
  simp [word]

theorem atU_val (cs : alloc.vec.Vec U32) (i : Nat) : (atU cs i).val = charAt cs i := by
  simp only [atU, charAt, word_getElem_opt]
  cases cs.val[i]? <;> simp

theorem at_eq (cs : alloc.vec.Vec U32) (i : Usize) : xml.at cs i = .ok (atU cs i.val) := by
  unfold xml.at atU
  by_cases h : i.val < cs.val.length
  · simp [alloc.vec.Vec.len_val, h, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
  · have : cs.val.length ≤ i.val := by omega
    simp [alloc.vec.Vec.len_val, h, List.getElem?_eq_none this]

/-- A character other than 0 lies inside the buffer. -/
theorem charAt_inside {cs : alloc.vec.Vec U32} {i : Nat} (h : charAt cs i ≠ 0) :
    i < cs.val.length := by
  by_contra outside
  apply h
  simp [charAt, word_getElem_opt, List.getElem?_eq_none (by omega : cs.val.length ≤ i)]

theorem charAt_getElem {cs : alloc.vec.Vec U32} {i : Nat} (h : i < cs.val.length) :
    (word cs)[i]? = some (charAt cs i) := by
  simp [charAt, word_getElem_opt, List.getElem?_eq_getElem h]

/-- The word from a position starts with the character there. -/
theorem drop_charAt {cs : alloc.vec.Vec U32} {i : Nat} (h : i < cs.val.length) :
    (word cs).drop i = charAt cs i :: (word cs).drop (i + 1) := by
  have hw : i < (word cs).length := by rw [word_length]; exact h
  rw [List.drop_eq_getElem_cons hw]
  congr 1
  have := charAt_getElem h
  rw [List.getElem?_eq_getElem hw] at this
  exact Option.some.inj this

theorem drop_end {cs : alloc.vec.Vec U32} {i : Nat} (h : cs.val.length ≤ i) :
    (word cs).drop i = [] := by
  apply List.drop_eq_nil_of_le
  rw [word_length]; exact h

/-- The first character of the word from a position is `charAt`, or the word
    is empty and `charAt` is 0. -/
theorem charAt_head (cs : alloc.vec.Vec U32) (i : Nat) :
    ((word cs).drop i = [] ∧ charAt cs i = 0) ∨
      ∃ rest, (word cs).drop i = charAt cs i :: rest := by
  by_cases h : i < cs.val.length
  · exact Or.inr ⟨_, drop_charAt h⟩
  · have hle : cs.val.length ≤ i := by omega
    refine Or.inl ⟨drop_end hle, ?_⟩
    simp [charAt, word_getElem_opt, List.getElem?_eq_none hle]

/-! ## Machine bounds -/

theorem usize_le_max (x : Usize) : x.val ≤ Usize.max := by scalar_tac

/-- Adding one to a position below another position does not overflow. -/
theorem succ_spec {x y : Usize} (h : x.val < y.val) :
    ∃ z : Usize, (x + 1#usize : Result Usize) = Result.ok z ∧ z.val = x.val + 1 := by
  have := usize_le_max y
  obtain ⟨z, hz, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := x) (y := 1#usize) (by simp; omega))
  exact ⟨z, hz, by simpa using hv⟩

/-! ## Results of `?` -/

theorem same_residual {T : Type} (e : xml.XmlError) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      T (core.convert.FromSame xml.XmlError) (.Err e) = .ok (.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame]

/-! ## Character classes -/

theorem space_eq (c : U32) : xml.space c = .ok (decide (IsSpace c.val)) := by
  simp [xml.space, IsSpace, UScalar.eq_equiv, Bool.or_assoc]

theorem name_start_eq (c : U32) : xml.name_start c = .ok (decide (NameStartChar c.val)) := by
  simp [xml.name_start, NameStartChar, UScalar.eq_equiv, Bool.or_assoc]

theorem name_char_eq (c : U32) : xml.name_char c = .ok (decide (NameChar c.val)) := by
  simp [xml.name_char, name_start_eq, NameChar, UScalar.eq_equiv, Bool.or_assoc]

theorem not_space_zero : ¬ IsSpace 0 := by simp [IsSpace]
theorem not_name_start_zero : ¬ NameStartChar 0 := by simp [NameStartChar]
theorem not_name_char_zero : ¬ NameChar 0 := by simp [NameChar, NameStartChar]

/-! ## Runs of characters -/

/-- The leading characters of a word satisfying `p`. -/
noncomputable abbrev run (p : Nat → Prop) (w : Word) : Word := w.takeWhile (fun c => decide (p c))

theorem run_cons_true {p : Nat → Prop} {c : Nat} {w : Word} (h : p c) :
    run p (c :: w) = c :: run p w := by
  simp [run, List.takeWhile_cons, h]

theorem run_cons_false {p : Nat → Prop} {c : Nat} {w : Word} (h : ¬ p c) :
    run p (c :: w) = [] := by
  simp [run, List.takeWhile_cons, h]

/-- A scanner over `p`, where `p 0` fails, from position `i` stops at
    `i + |run|`. -/
theorem run_step {p : Nat → Prop} (cs : alloc.vec.Vec U32) (i : Nat) (h : p (charAt cs i))
    (zero : ¬ p 0) :
    i < cs.val.length ∧ (run p ((word cs).drop i)).length = (run p ((word cs).drop (i + 1))).length + 1 := by
  have inside : i < cs.val.length := charAt_inside (fun z => zero (z ▸ h))
  refine ⟨inside, ?_⟩
  rw [drop_charAt inside, run_cons_true h]
  simp

theorem run_stop {p : Nat → Prop} (cs : alloc.vec.Vec U32) (i : Nat) (h : ¬ p (charAt cs i)) :
    (run p ((word cs).drop i)).length = 0 := by
  rcases charAt_head cs i with ⟨empty, _⟩ | ⟨rest, split⟩
  · simp [empty]
  · rw [split, run_cons_false h]; simp

theorem skip_spaces_eq (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ j : Usize, xml.skip_spaces cs i = .ok j ∧
      j.val = i.val + (run IsSpace ((word cs).drop i.val)).length := by
  rw [xml.skip_spaces]
  by_cases h : IsSpace (charAt cs i.val)
  · obtain ⟨inside, step⟩ := run_step cs i.val h not_space_zero
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := i) (y := 1#usize) (by have := cs.property; scalar_tac))
    have nextValue : next.val = i.val + 1 := by simpa using hv
    obtain ⟨j, hj, hjv⟩ := skip_spaces_eq cs next
    refine ⟨j, ?_, ?_⟩
    · simp [at_eq, space_eq, atU_val, h, hn, hj]
    · rw [hjv, nextValue, step]; omega
  · refine ⟨i, ?_, ?_⟩
    · simp [at_eq, space_eq, atU_val, h]
    · rw [run_stop cs i.val h]; simp
termination_by cs.val.length - i.val
decreasing_by
  have := (run_step cs i.val h not_space_zero).1
  omega

theorem names_end_eq (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ j : Usize, xml.names_end cs i = .ok j ∧
      j.val = i.val + (run NameChar ((word cs).drop i.val)).length := by
  rw [xml.names_end]
  by_cases h : NameChar (charAt cs i.val)
  · obtain ⟨inside, step⟩ := run_step cs i.val h not_name_char_zero
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := i) (y := 1#usize) (by have := cs.property; scalar_tac))
    have nextValue : next.val = i.val + 1 := by simpa using hv
    obtain ⟨j, hj, hjv⟩ := names_end_eq cs next
    refine ⟨j, ?_, ?_⟩
    · simp [at_eq, name_char_eq, atU_val, h, hn, hj]
    · rw [hjv, nextValue, step]; omega
  · refine ⟨i, ?_, ?_⟩
    · simp [at_eq, name_char_eq, atU_val, h]
    · rw [run_stop cs i.val h]; simp
termination_by cs.val.length - i.val
decreasing_by
  have := (run_step cs i.val h not_name_char_zero).1
  omega

/-! ## Runs as consumed words -/

theorem run_append_drop (p : Nat → Prop) (w : Word) : w = run p w ++ w.drop (run p w).length := by
  induction w with
  | nil => simp
  | cons c rest ih =>
    by_cases h : p c
    · rw [run_cons_true h]
      simp only [List.cons_append, List.length_cons, List.drop_succ_cons]
      exact congrArg (c :: ·) ih
    · rw [run_cons_false h]; simp

theorem run_all {p : Nat → Prop} {w : Word} : ∀ c ∈ run p w, p c := by
  induction w with
  | nil => simp
  | cons d more ih =>
    intro c member
    by_cases hd : p d
    · rw [run_cons_true hd] at member
      rcases List.mem_cons.mp member with rfl | m
      · exact hd
      · exact ih c m
    · rw [run_cons_false hd] at member; simp at member

theorem run_length_le_length (p : Nat → Prop) (w : Word) : (run p w).length ≤ w.length := by
  induction w with
  | nil => simp
  | cons d more ih =>
    by_cases hd : p d
    · rw [run_cons_true hd]; simp; exact ih
    · rw [run_cons_false hd]; simp

theorem run_next {p : Nat → Prop} {w : Word} {c : Nat} {rest : Word}
    (h : w.drop (run p w).length = c :: rest) : ¬ p c := by
  induction w generalizing c rest with
  | nil => simp at h
  | cons d more ih =>
    by_cases hd : p d
    · rw [run_cons_true hd] at h
      simp only [List.length_cons, List.drop_succ_cons] at h
      exact ih h
    · rw [run_cons_false hd] at h
      simp only [List.length_nil, List.drop_zero, List.cons.injEq] at h
      rw [← h.1]; exact hd

/-- A word of characters satisfying `p` followed by a stop is the run of `p`. -/
theorem run_unique {p : Nat → Prop} {w rest : Word} (all : ∀ c ∈ w, p c)
    (stop : ∀ c more, rest = c :: more → ¬ p c) : run p (w ++ rest) = w := by
  induction w with
  | nil =>
    cases rest with
    | nil => simp
    | cons c more => simp [run_cons_false (stop c more rfl)]
  | cons c more ih =>
    rw [List.cons_append, run_cons_true (all c (List.mem_cons_self ..))]
    exact congrArg (c :: ·) (ih (fun d hd => all d (List.mem_cons_of_mem _ hd)))

/-- The word from `i` is the run of `p` followed by the word from its end. -/
theorem drop_run (p : Nat → Prop) (cs : alloc.vec.Vec U32) (i : Nat) :
    (word cs).drop i = run p ((word cs).drop i) ++ (word cs).drop (i + (run p ((word cs).drop i)).length) := by
  conv => lhs; rw [run_append_drop p ((word cs).drop i)]
  rw [List.drop_drop]

/-- The character after a run fails `p`. -/
theorem run_follow {p : Nat → Prop} (cs : alloc.vec.Vec U32) (i : Nat) (zero : ¬ p 0) :
    ¬ p (charAt cs (i + (run p ((word cs).drop i)).length)) := by
  rcases charAt_head cs (i + (run p ((word cs).drop i)).length) with ⟨_, z⟩ | ⟨rest, split⟩
  · rw [z]; exact zero
  · apply run_next (w := (word cs).drop i) (rest := rest)
    rw [List.drop_drop, ← split]

theorem run_length_le (p : Nat → Prop) (cs : alloc.vec.Vec U32) (i : Nat) :
    i + (run p ((word cs).drop i)).length ≤ max i cs.val.length := by
  have h1 : (run p ((word cs).drop i)).length ≤ ((word cs).drop i).length := run_length_le_length _ _
  simp [word_length] at h1
  omega

/-! ## White space and names -/

theorem spaces_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.spaces cs i = .ok r ∧
      match r with
      | .Ok j => IsSpace (charAt cs i.val) ∧ j.val = i.val + (run IsSpace ((word cs).drop i.val)).length
      | .Err _ => ¬ IsSpace (charAt cs i.val) := by
  unfold xml.spaces
  by_cases h : IsSpace (charAt cs i.val)
  · obtain ⟨inside, step⟩ := run_step cs i.val h not_space_zero
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := i) (y := 1#usize) (by have := cs.property; scalar_tac))
    have nextValue : next.val = i.val + 1 := by simpa using hv
    obtain ⟨j, hj, hjv⟩ := skip_spaces_eq cs next
    refine ⟨.Ok j, by simp [at_eq, space_eq, atU_val, h, hn, hj], h, ?_⟩
    rw [hjv, nextValue, step]; omega
  · exact ⟨.Err ⟨.Syntax, i⟩, by simp [at_eq, space_eq, atU_val, h, xml.fail], h⟩

theorem name_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.name cs i = .ok r ∧
      match r with
      | .Ok j => NameStartChar (charAt cs i.val) ∧ j.val = i.val + (run NameChar ((word cs).drop i.val)).length
      | .Err _ => ¬ NameStartChar (charAt cs i.val) := by
  unfold xml.name
  by_cases h : NameStartChar (charAt cs i.val)
  · have hc : NameChar (charAt cs i.val) := Or.inl h
    obtain ⟨inside, step⟩ := run_step cs i.val hc not_name_char_zero
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := i) (y := 1#usize) (by have := cs.property; scalar_tac))
    have nextValue : next.val = i.val + 1 := by simpa using hv
    obtain ⟨j, hj, hjv⟩ := names_end_eq cs next
    refine ⟨.Ok j, by simp [at_eq, name_start_eq, atU_val, h, hn, hj], h, ?_⟩
    rw [hjv, nextValue, step]; omega
  · exact ⟨.Err ⟨.InvalidName, i⟩, by simp [at_eq, name_start_eq, atU_val, h, xml.fail], h⟩

/-- The first colon of `cs[i..stop]`, or `stop`. -/
theorem colon_spec (cs : alloc.vec.Vec U32) (i stop : Usize) (h : i.val ≤ stop.val) :
    ∃ j : Usize, xml.colon cs i stop = .ok j ∧ i.val ≤ j.val ∧ j.val ≤ stop.val ∧
      (∀ k, i.val ≤ k → k < j.val → charAt cs k ≠ 58) ∧ (j.val = stop.val ∨ charAt cs j.val = 58) := by
  rw [xml.colon]
  by_cases more : i.val < stop.val
  · by_cases found : charAt cs i.val = 58
    · refine ⟨i, ?_, le_refl _, by omega, fun k hk hk2 => by omega, Or.inr found⟩
      have : atU cs i.val = 58#u32 := by
        apply UScalar.eq_of_val_eq; rw [atU_val]; simpa using found
      simp [more, at_eq, this]
    · obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      have nextValue : next.val = i.val + 1 := by simpa using hv
      obtain ⟨j, hj, lo, hi, none, last⟩ := colon_spec cs next stop (by omega)
      have ne : atU cs i.val ≠ 58#u32 := by
        intro e; apply found; rw [← atU_val, e]; rfl
      refine ⟨j, by simp [more, at_eq, ne, hn, hj], by omega, hi, ?_, last⟩
      intro k hk hk2
      by_cases e : k = i.val
      · subst e; exact found
      · exact none k (by omega) hk2
  · refine ⟨stop, by simp [more], h, le_refl _, fun k hk hk2 => ?_, Or.inl rfl⟩
    omega
termination_by stop.val - i.val
decreasing_by omega

/-! ## Literal words -/

/-- The code points of a byte slice. -/
def bytes (s : Slice U8) : Word := s.val.map (·.val)

theorem starts_from_eq (cs : alloc.vec.Vec U32) (i : Usize) (pat : Slice U8) (k : Usize) :
    xml.starts_from cs i pat k = .ok (decide ((bytes pat).drop k.val <+: (word cs).drop i.val)) := by
  rw [xml.starts_from]
  by_cases hk : k.val < pat.val.length
  · have hpat : (bytes pat).drop k.val = pat.val[k.val].val :: (bytes pat).drop (k.val + 1) := by
      have hb : k.val < (bytes pat).length := by simp [bytes]; exact hk
      rw [List.drop_eq_getElem_cons hb]; simp [bytes]
    by_cases hi : i.val < cs.val.length
    · have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) cs i =
          .ok cs.val[i.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hi]
      have plookup : Slice.index_usize pat k = .ok pat.val[k.val] := by
        simp [Slice.index_usize, List.getElem?_eq_getElem hk]
      have hcs := drop_charAt hi
      have hcv : charAt cs i.val = cs.val[i.val].val := by
        have := charAt_getElem hi
        rw [word_getElem_opt, List.getElem?_eq_getElem hi] at this
        simp at this; exact this.symm
      obtain ⟨i6, hi6, hv6⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := i) (y := 1#usize) (by have := cs.property; scalar_tac))
      obtain ⟨k6, hk6, hvk6⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := k) (y := 1#usize) (by have := pat.property; scalar_tac))
      have i6v : i6.val = i.val + 1 := by simpa using hv6
      have k6v : k6.val = k.val + 1 := by simpa using hvk6
      by_cases eq : cs.val[i.val].val = pat.val[k.val].val
      · have same : cs.val[i.val] = core.convert.num.FromU32U8.from pat.val[k.val] := by
          apply UScalar.eq_of_val_eq
          rw [core.convert.num.FromU32U8.from_val_eq]; exact eq
        have rest := starts_from_eq cs i6 pat k6
        simp only [Slice.len, alloc.vec.Vec.len_val, UScalar.lt_equiv, hk, hi, lookup, plookup,
          lift, bind_ok, same, hi6, hk6, rest, ite_true, decide_true, Slice.len_val]
        rw [hpat, hcs, hcv, i6v, k6v, eq]
        simp [List.cons_prefix_cons]
      · have differ : cs.val[i.val] ≠ core.convert.num.FromU32U8.from pat.val[k.val] := by
          intro e; apply eq; rw [e, core.convert.num.FromU32U8.from_val_eq]
        simp only [Slice.len, alloc.vec.Vec.len_val, UScalar.lt_equiv, hk, hi, lookup, plookup,
          lift, bind_ok, differ, ite_true, ite_false, Slice.len_val]
        rw [hpat, hcs, hcv]
        simp only [List.cons_prefix_cons]
        congr 1
        exact (decide_eq_false (fun h => eq h.1.symm)).symm
    · have empty : (word cs).drop i.val = [] := drop_end (by omega)
      simp [Slice.len_val, alloc.vec.Vec.len_val, UScalar.lt_equiv, hk, hi, hpat, empty]
  · have empty : (bytes pat).drop k.val = [] := by
      apply List.drop_eq_nil_of_le; simp [bytes]; omega
    simp [Slice.len_val, UScalar.lt_equiv, hk, empty]
termination_by pat.val.length - k.val
decreasing_by omega

theorem starts_eq (cs : alloc.vec.Vec U32) (i : Usize) (pat : Slice U8) :
    xml.starts cs i pat = .ok (decide (bytes pat <+: (word cs).drop i.val)) := by
  simp [xml.starts, starts_from_eq]

/-! ## Characters inside a consumed word -/

/-- The characters of a word consumed from position `i`. -/
theorem charAt_of_drop {cs : alloc.vec.Vec U32} {i : Nat} {w rest : Word}
    (split : (word cs).drop i = w ++ rest) {t : Nat} (ht : t < w.length) :
    charAt cs (i + t) = w[t] := by
  have inside : i + t < cs.val.length := by
    have := congrArg List.length split
    simp [word_length] at this
    omega
  have e := charAt_getElem inside
  have e2 : (word cs)[i + t]? = some w[t] := by
    rw [← List.getElem?_drop, split, List.getElem?_append_left ht, List.getElem?_eq_getElem ht]
  rw [e] at e2
  exact Option.some.inj e2

/-- The character right after a consumed word. -/
theorem charAt_after {cs : alloc.vec.Vec U32} {i : Nat} {w rest : Word}
    (split : (word cs).drop i = w ++ rest) :
    charAt cs (i + w.length) = rest.headD 0 := by
  cases rest with
  | nil =>
    have : cs.val.length ≤ i + w.length := by
      have := congrArg List.length split
      simp [word_length] at this
      omega
    simp [charAt, word_getElem_opt, List.getElem?_eq_none this]
  | cons c more =>
    have := charAt_of_drop (w := w ++ [c]) (rest := more) (by simpa using split)
      (t := w.length) (by simp)
    simpa using this

/-- Dropping a consumed word. -/
theorem drop_after {cs : alloc.vec.Vec U32} {i : Nat} {w rest : Word}
    (split : (word cs).drop i = w ++ rest) : (word cs).drop (i + w.length) = rest := by
  rw [← List.drop_drop, split]; simp

/-- A consumed word ends inside the buffer. -/
theorem consumed_le {cs : alloc.vec.Vec U32} {i : Nat} {w rest : Word}
    (split : (word cs).drop i = w ++ rest) (hw : w ≠ []) : i + w.length ≤ cs.val.length := by
  have := congrArg List.length split
  simp [word_length] at this
  have : 0 < w.length := List.length_pos_of_ne_nil hw
  omega

/-! ## Qualified names -/

/-- The index of the first colon of a word, its length when it has none. -/
def colonIndex : Word → Nat
  | [] => 0
  | c :: rest => if c = 58 then 0 else colonIndex rest + 1

theorem colonIndex_le (w : Word) : colonIndex w ≤ w.length := by
  induction w with
  | nil => simp [colonIndex]
  | cons c rest ih => by_cases h : c = 58 <;> simp [colonIndex, h]; omega

theorem colonIndex_none {w : Word} (h : 58 ∉ w) : colonIndex w = w.length := by
  induction w with
  | nil => simp [colonIndex]
  | cons c rest ih =>
    have hc : c ≠ 58 := fun e => h (e ▸ List.mem_cons_self ..)
    have hr : 58 ∉ rest := fun m => h (List.mem_cons_of_mem _ m)
    simp [colonIndex, hc, ih hr]

theorem colonIndex_split {w : Word} (h : 58 ∈ w) :
    w = w.take (colonIndex w) ++ 58 :: w.drop (colonIndex w + 1) ∧ 58 ∉ w.take (colonIndex w) := by
  induction w with
  | nil => simp at h
  | cons c rest ih =>
    by_cases hc : c = 58
    · subst hc; simp [colonIndex]
    · have hr : 58 ∈ rest := by
        rcases List.mem_cons.mp h with e | m
        · exact absurd e.symm hc
        · exact m
      obtain ⟨e, n⟩ := ih hr
      simp only [colonIndex, hc, ite_false, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      refine ⟨congrArg (c :: ·) e, ?_⟩
      simp only [List.mem_cons, not_or]
      exact ⟨fun e2 => hc e2.symm, n⟩

/-- The first colon of `p ++ 58 :: l` when `p` has none. -/
theorem colonIndex_append {p l : Word} (h : 58 ∉ p) : colonIndex (p ++ 58 :: l) = p.length := by
  induction p with
  | nil => simp [colonIndex]
  | cons c rest ih =>
    have hc : c ≠ 58 := fun e => h (e ▸ List.mem_cons_self ..)
    have hr : 58 ∉ rest := fun m => h (List.mem_cons_of_mem _ m)
    simp [colonIndex, hc, ih hr]

theorem qname_unique_of_eq {n n' : Word} {p p' : Option Word} {l l' : Word}
    (one : QName n p l) (two : QName n' p' l') (same : n = n') : p = p' ∧ l = l' := by
  cases one with
  | unprefixed h =>
    cases two with
    | unprefixed _ => exact ⟨rfl, same⟩
    | prefixed _ _ => exact absurd (by rw [same]; simp) h.2
  | @prefixed a b ha hb =>
    cases two with
    | unprefixed h => exact absurd (by rw [← same]; simp) h.2
    | @prefixed c d hc hd =>
      have ia := colonIndex_append (l := l) ha.2
      have ic := colonIndex_append (l := l') hc.2
      have lens : a.length = c.length := by rw [← ia, ← ic, same]
      obtain ⟨rfl, h2⟩ := List.append_inj same lens
      simp at h2
      exact ⟨rfl, h2⟩

/-- A QName has one reading. -/
theorem qname_unique {n : Word} {p p' : Option Word} {l l' : Word}
    (one : QName n p l) (two : QName n p' l') : p = p' ∧ l = l' :=
  qname_unique_of_eq one two rfl

/-- The first colon of a word is the unique position before which there is
    no colon and at which there is one or the word ends. -/
theorem colonIndex_char {w : Word} {t : Nat} (le : t ≤ w.length)
    (before : ∀ s (hs : s < t), w[s]'(by omega) ≠ 58)
    (at_t : t = w.length ∨ ∃ ht : t < w.length, w[t] = 58) : colonIndex w = t := by
  induction w generalizing t with
  | nil => simp [colonIndex] at le ⊢; omega
  | cons c rest ih =>
    cases t with
    | zero =>
      rcases at_t with e | ⟨_, e⟩
      · simp at e
      · simp at e; simp [colonIndex, e]
    | succ t =>
      have hc : c ≠ 58 := by have := before 0 (by omega); simpa using this
      simp only [colonIndex, hc, ite_false]
      congr 1
      apply ih (by simp at le; omega)
      · intro s hs; have := before (s + 1) (by omega); simpa using this
      · rcases at_t with e | ⟨ht, e⟩
        · left; simp at e; omega
        · right; exact ⟨by simp at ht; omega, by simpa using e⟩

/-- `colon` over a consumed word finds its first colon. -/
theorem colon_word (cs : alloc.vec.Vec U32) (i stop : Usize) {w rest : Word}
    (split : (word cs).drop i.val = w ++ rest) (hs : stop.val = i.val + w.length) :
    ∃ j : Usize, xml.colon cs i stop = .ok j ∧ j.val = i.val + colonIndex w := by
  obtain ⟨j, run, lo, hi, none, last⟩ := colon_spec cs i stop (by omega)
  refine ⟨j, run, ?_⟩
  have key : colonIndex w = j.val - i.val := by
    apply colonIndex_char (t := j.val - i.val) (by omega)
    · intro s hs
      have := none (i.val + s) (by omega) (by omega)
      rwa [charAt_of_drop split (by omega)] at this
    · by_cases je : j.val = stop.val
      · left; omega
      · right
        have jlt : j.val - i.val < w.length := by omega
        refine ⟨jlt, ?_⟩
        rcases last with e | e
        · exact absurd e je
        · have := charAt_of_drop split jlt
          rw [show i.val + (j.val - i.val) = j.val by omega] at this
          rw [← this]; exact e
  omega

/-- The name characters from a position. -/
noncomputable def nameRun (cs : alloc.vec.Vec U32) (i : Nat) : Word := run NameChar ((word cs).drop i)

theorem nameRun_split (cs : alloc.vec.Vec U32) (i : Nat) :
    (word cs).drop i = nameRun cs i ++ (word cs).drop (i + (nameRun cs i).length) :=
  drop_run NameChar cs i

theorem nameRun_name {cs : alloc.vec.Vec U32} {i : Nat} (h : NameStartChar (charAt cs i)) :
    Name (nameRun cs i) := by
  have hc : NameChar (charAt cs i) := Or.inl h
  have inside := charAt_inside (fun z => not_name_start_zero (z ▸ h))
  have e : nameRun cs i = charAt cs i :: run NameChar ((word cs).drop (i + 1)) := by
    unfold nameRun; rw [drop_charAt inside, run_cons_true hc]
  refine ⟨charAt cs i, run NameChar ((word cs).drop (i + 1)), e, h, run_all⟩

/-- No name starts where the first character is no NameStartChar. -/
theorem nameRun_not_name {cs : alloc.vec.Vec U32} {i : Nat} (h : ¬ NameStartChar (charAt cs i)) :
    ¬ Name (nameRun cs i) := by
  rintro ⟨c, rest, e, hc, _⟩
  have inside : i < cs.val.length := by
    by_contra out
    have : (word cs).drop i = [] := drop_end (by omega)
    simp [nameRun, this] at e
  have : nameRun cs i = charAt cs i :: run NameChar ((word cs).drop (i + 1)) ∨ nameRun cs i = [] := by
    unfold nameRun; rw [drop_charAt inside]
    by_cases hn : NameChar (charAt cs i)
    · left; rw [run_cons_true hn]
    · right; rw [run_cons_false hn]
  rcases this with e2 | e2
  · rw [e2] at e; injection e with e3; exact h (e3 ▸ hc)
  · rw [e2] at e; simp at e

theorem name_run_all (cs : alloc.vec.Vec U32) (i : Nat) : ∀ c ∈ nameRun cs i, NameChar c := run_all

/-- Every word read by a QName is a Name. -/
theorem qname_name {n : Word} {p : Option Word} {l : Word} (h : QName n p l) : Name n := by
  cases h with
  | unprefixed h => exact h.1
  | prefixed hp hl =>
    obtain ⟨c, rest, e, hc, hr⟩ := hp.1
    refine ⟨c, rest ++ 58 :: l, by rw [e]; simp, hc, ?_⟩
    intro d hd
    rcases List.mem_append.mp hd with m | m
    · exact hr d m
    · rcases List.mem_cons.mp m with rfl | m
      · left; simp [NameStartChar]
      · obtain ⟨c2, rest2, e2, hc2, hr2⟩ := hl.1
        rw [e2] at m
        rcases List.mem_cons.mp m with rfl | m
        · exact Or.inl hc2
        · exact hr2 d m

/-- The position of the colon of a QName read from `i` (its end when it has
    no prefix). -/
def markOf (i : Nat) (n : Word) : Option Word → Nat
  | none => i + n.length
  | some p => i + p.length

/-- Where `colonIndex` lies in a word with a colon. -/
theorem colonIndex_lt {w : Word} (h : 58 ∈ w) : colonIndex w < w.length := by
  induction w with
  | nil => simp at h
  | cons c rest ih =>
    by_cases hc : c = 58
    · simp [colonIndex, hc]
    · have hr : 58 ∈ rest := by
        rcases List.mem_cons.mp h with e | m
        · exact absurd e.symm hc
        · exact m
      have := ih hr
      simp [colonIndex, hc]; omega

/-- A word with a colon splits at its first one. -/
theorem colon_parts {n : Word} (h : 58 ∈ n) :
    ∃ pre l, n = pre ++ 58 :: l ∧ pre.length = colonIndex n ∧ 58 ∉ pre := by
  obtain ⟨e, nb⟩ := colonIndex_split h
  refine ⟨_, _, e, ?_, nb⟩
  simp [List.length_take]
  have := colonIndex_le n
  omega

/-- A name whose characters are name characters, read from its first one. -/
theorem name_of_parts {c : Nat} {rest : Word} (hc : NameStartChar c) (hr : ∀ d ∈ rest, NameChar d) :
    Name (c :: rest) := ⟨c, rest, rfl, hc, hr⟩

theorem qname_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.qname cs i = .ok r ∧
      (∀ stop mark, r = .Ok (stop, mark) →
        stop.val = i.val + (nameRun cs i.val).length ∧
        ∃ p l, QName (nameRun cs i.val) p l ∧ mark.val = markOf i.val (nameRun cs i.val) p) ∧
      (∀ p l, QName (nameRun cs i.val) p l → ∃ stop mark, r = .Ok (stop, mark)) := by
  unfold xml.qname
  obtain ⟨r1, h1, c1⟩ := name_spec cs i
  cases r1 with
  | Err e =>
    refine ⟨.Err e, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
    intro p l q
    exact absurd (qname_name q) (nameRun_not_name c1)
  | Ok val =>
    obtain ⟨start, hval⟩ := c1
    have hname := nameRun_name start
    have hall := name_run_all cs i.val
    have split : (word cs).drop i.val = nameRun cs i.val ++ (word cs).drop val.val := by
      rw [hval]; exact nameRun_split cs i.val
    have hv : val.val = i.val + (nameRun cs i.val).length := hval
    generalize nameRun cs i.val = n at *
    obtain ⟨mark, hmark, hmv⟩ := colon_word cs i val split hv
    by_cases plain : mark = val
    · subst plain
      have noColon : 58 ∉ n := by
        intro m
        have := colonIndex_lt m
        omega
      refine ⟨.Ok (mark, mark), by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, hmark], ?_, ?_⟩
      · intro stop mk e
        simp at e
        obtain ⟨rfl, rfl⟩ := e
        exact ⟨hv, none, n, QName.unprefixed ⟨hname, noColon⟩, by simp [markOf]; omega⟩
      · intro _ _ _; exact ⟨mark, mark, rfl⟩
    · have hasColon : 58 ∈ n := by
        by_contra m
        have := colonIndex_none m
        apply plain
        apply UScalar.eq_of_val_eq
        omega
      obtain ⟨pre, l, splitN, preLen, noneBefore⟩ := colon_parts hasColon
      have lenN : n.length = pre.length + 1 + l.length := by
        rw [splitN]; simp only [List.length_append, List.length_cons]; omega
      have mlt : mark.val < val.val := by have := colonIndex_lt hasColon; omega
      obtain ⟨m1, hm1, m1v⟩ := succ_spec mlt
      have e1 : (word cs).drop i.val = (pre ++ [(58 : Nat)]) ++ (l ++ (word cs).drop val.val) := by
        rw [split, splitN]
        simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
      have plen : (pre ++ [(58 : Nat)]).length = pre.length + 1 := by simp
      have lsplit : (word cs).drop m1.val = l ++ (word cs).drop val.val := by
        have e2 := drop_after e1
        rw [plen, show i.val + (pre.length + 1) = m1.val from by omega] at e2
        exact e2
      obtain ⟨j, hj, hjv⟩ := colon_word cs m1 val lsplit (by omega)
      have nameAt : l ≠ [] → charAt cs (mark.val + 1) = l.headD 0 := by
        intro ne
        have := charAt_after e1
        rw [plen, show i.val + (pre.length + 1) = mark.val + 1 from by omega] at this
        rw [this]; cases l with
        | nil => exact absurd rfl ne
        | cons c rest => simp
      have hbool : xml.prefixed cs i mark val =
          .ok (decide (i.val < mark.val ∧ m1.val < val.val ∧ NameStartChar (charAt cs (mark.val + 1)) ∧
            j.val = val.val)) := by
        simp only [xml.prefixed, hm1, bind_ok, at_eq, name_start_eq, atU_val, m1v, hj]
        simp [UScalar.eq_equiv, m1v, Bool.and_assoc]
      have notPlain : ¬ mark = val := plain
      by_cases good : i.val < mark.val ∧ m1.val < val.val ∧ NameStartChar (charAt cs (mark.val + 1)) ∧
          j.val = val.val
      · obtain ⟨lt1, lt2, ns0, jv⟩ := good
        have lNoColon : 58 ∉ l := by
          intro m
          have := colonIndex_lt m
          omega
        have preName : NCName pre := by
          cases pre with
          | nil => simp at preLen; omega
          | cons c rest =>
            obtain ⟨c0, rest0, e0, hc0, hr0⟩ := hname
            rw [splitN] at e0
            simp at e0
            obtain ⟨rfl, e0⟩ := e0
            refine ⟨name_of_parts hc0 ?_, noneBefore⟩
            intro d hd
            exact hr0 d (by rw [← e0]; simp [hd])
        have lNe : l ≠ [] := by
          intro e; rw [e] at lenN; simp at lenN; omega
        have ns : NameStartChar (l.headD 0) := nameAt lNe ▸ ns0
        have lName : NCName l := by
          cases l with
          | nil => exact absurd rfl lNe
          | cons c rest =>
            refine ⟨name_of_parts (by simpa using ns) ?_, lNoColon⟩
            intro d hd
            exact hall d (by rw [splitN]; simp [hd])
        refine ⟨.Ok (val, mark), ?_, ?_, ?_⟩
        · simp [h1, core.result.Result.Insts.CoreOpsTry.branch, hmark, notPlain, hbool, lt1, lt2, ns0, jv]
        · intro stop mk e
          simp at e
          obtain ⟨rfl, rfl⟩ := e
          refine ⟨hv, some pre, l, splitN ▸ QName.prefixed preName lName, ?_⟩
          simp [markOf]; omega
        · intro _ _ _; exact ⟨val, mark, rfl⟩
      · refine ⟨.Err ⟨.InvalidName, i⟩, ?_, by simp, ?_⟩
        · rw [decide_eq_false good] at hbool
          simp [h1, core.result.Result.Insts.CoreOpsTry.branch, hmark, notPlain, hbool, xml.fail]
        · intro p l' q
          cases q with
          | unprefixed h => exact (h.2 hasColon).elim
          | @prefixed a b ha hb =>
            exfalso
            have ia := colonIndex_append (l := l') ha.2
            have lens : a.length = pre.length := by omega
            obtain ⟨rfl, e2⟩ := List.append_inj splitN lens
            simp at e2
            subst e2
            apply good
            obtain ⟨c, rest, ec, hc, _⟩ := hb.1
            have bne : l'.length = rest.length + 1 := by rw [ec]; simp
            have := colonIndex_none hb.2
            have lNe : l' ≠ [] := by rw [ec]; simp
            have apos : 0 < a.length := by obtain ⟨c0, r0, e0, _, _⟩ := ha.1; rw [e0]; simp
            refine ⟨by omega, by omega, by rw [nameAt lNe, ec]; simpa using hc, by omega⟩
theorem ncname_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.ncname cs i = .ok r ∧
      (∀ stop, r = .Ok stop → stop.val = i.val + (nameRun cs i.val).length ∧ NCName (nameRun cs i.val)) ∧
      (NCName (nameRun cs i.val) → ∃ stop, r = .Ok stop) := by
  unfold xml.ncname
  obtain ⟨r1, h1, c1⟩ := name_spec cs i
  cases r1 with
  | Err e =>
    refine ⟨.Err e, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
    intro q
    exact absurd q.1 (nameRun_not_name c1)
  | Ok val =>
    obtain ⟨start, hval⟩ := c1
    have hname := nameRun_name start
    have split : (word cs).drop i.val = nameRun cs i.val ++ (word cs).drop val.val := by
      rw [hval]; exact nameRun_split cs i.val
    have hv : val.val = i.val + (nameRun cs i.val).length := hval
    obtain ⟨mark, hmark, hmv⟩ := colon_word cs i val split hv
    by_cases plain : mark = val
    · subst plain
      have noColon : 58 ∉ nameRun cs i.val := by
        intro m
        have := colonIndex_lt m
        omega
      exact ⟨.Ok mark, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, hmark],
        fun stop e => by simp at e; subst e; exact ⟨hv, hname, noColon⟩, fun _ => ⟨mark, rfl⟩⟩
    · have hasColon : 58 ∈ nameRun cs i.val := by
        by_contra m
        have := colonIndex_none m
        apply plain
        apply UScalar.eq_of_val_eq
        omega
      refine ⟨.Err ⟨.InvalidName, i⟩, ?_, by simp, fun q => absurd hasColon q.2⟩
      simp [h1, core.result.Result.Insts.CoreOpsTry.branch, hmark, plain, xml.fail]

/-! ## Spans -/

theorem sub_eq {x y : Usize} (h : y.val ≤ x.val) :
    ∃ z : Usize, (x - y : Result Usize) = Result.ok z ∧ z.val = x.val - y.val := by
  obtain ⟨z, hz, hv, _⟩ := WP.spec_imp_exists (Usize.sub_spec (x := x) (y := y) h)
  exact ⟨z, hz, hv⟩

theorem prefix_same_length {p w rest : Word} (h : p <+: w ++ rest) (l : p.length = w.length) :
    p = w := by
  obtain ⟨t, ht⟩ := h
  exact (List.append_inj ht l).1

/-- The span of a consumed word is the literal `pat` exactly when the word is. -/
theorem span_is_eq (cs : alloc.vec.Vec U32) (start stop : Usize) (pat : Slice U8) {w rest : Word}
    (split : (word cs).drop start.val = w ++ rest) (hs : stop.val = start.val + w.length) :
    xml.span_is cs start stop pat = .ok (decide (w = bytes pat)) := by
  obtain ⟨d, hd, hdv⟩ := sub_eq (x := stop) (y := start) (by omega)
  unfold xml.span_is
  simp only [hd, bind_ok, starts_eq, split]
  congr 1
  have hlen : (bytes pat).length = pat.val.length := by simp [bytes]
  by_cases e : w = bytes pat
  · subst e
    simp [UScalar.eq_equiv, hdv, hs, Slice.len_val, hlen]
  · simp only [UScalar.eq_equiv, Slice.len_val]
    simp only [e, decide_false]
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases l : d.val = pat.val.length
    · right
      intro p
      exact e (prefix_same_length p (by omega)).symm
    · left; exact l

theorem usize_add_le {x c y : Usize} (h : x.val + c.val ≤ y.val) :
    ∃ z : Usize, (x + c : Result Usize) = Result.ok z ∧ z.val = x.val + c.val := by
  have := usize_le_max y
  obtain ⟨z, hz, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := x) (y := c) (by omega))
  exact ⟨z, hz, hv⟩

/-- `xml`, `XML` and the other spellings of `xml` in any case. -/
def XmlName (t : Word) : Prop :=
  ∃ a b c, t = [a, b, c] ∧ (a = 120 ∨ a = 88) ∧ (b = 109 ∨ b = 77) ∧ (c = 108 ∨ c = 76)

theorem caseless_eq (c lower : U32) (h : 32 ≤ lower.val) :
    xml.caseless c lower = .ok (decide (c.val = lower.val ∨ c.val = lower.val - 32)) := by
  obtain ⟨d, hd, hdv, _⟩ := WP.spec_imp_exists (U32.sub_spec (x := lower) (y := 32#u32) (by simpa using h))
  simp [xml.caseless, hd, UScalar.eq_equiv, hdv]

theorem reserved_target_eq (cs : alloc.vec.Vec U32) (start stop : Usize) {w rest : Word}
    (split : (word cs).drop start.val = w ++ rest) (hs : stop.val = start.val + w.length) :
    xml.reserved_target cs start stop = .ok (decide (XmlName w)) := by
  obtain ⟨d, hd, hdv⟩ := sub_eq (x := stop) (y := start) (by omega)
  unfold xml.reserved_target
  simp only [hd, bind_ok]
  by_cases three : w.length = 3
  · have dv : d = 3#usize := by apply UScalar.eq_of_val_eq; simp; omega
    obtain ⟨s1, hs1, hs1v⟩ := usize_add_le (x := start) (c := 1#usize) (y := stop) (by simp; omega)
    obtain ⟨s2, hs2, hs2v⟩ := usize_add_le (x := start) (c := 2#usize) (y := stop) (by simp; omega)
    have c0 := charAt_of_drop split (t := 0) (by omega)
    have c1 := charAt_of_drop split (t := 1) (by omega)
    have c2 := charAt_of_drop split (t := 2) (by omega)
    simp only [Nat.add_zero] at c0
    unfold xml.xml_letters
    simp only [dv, ite_true, at_eq, bind_ok, hs1, hs2]
    rw [caseless_eq _ _ (by simp), caseless_eq _ _ (by simp), caseless_eq _ _ (by simp)]
    simp only [bind_ok, atU_val, c0, show s1.val = start.val + 1 by simpa using hs1v,
      show s2.val = start.val + 2 by simpa using hs2v, c1, c2]
    congr 1
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c, w = [a, b, c] := by
      match w, three with
      | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
    simp [XmlName, Bool.and_assoc]
  · have dv : ¬ d = 3#usize := by intro e; apply three; have := congrArg UScalar.val e; simp at this; omega
    simp only [dv, ite_false]
    congr 1
    refine (decide_eq_false ?_).symm
    rintro ⟨a, b, c, rfl, _⟩
    simp at three

theorem same_from_eq (cs : alloc.vec.Vec U32) (a b n k : Usize)
    (ha : a.val + n.val ≤ Usize.max) (hb : b.val + n.val ≤ Usize.max) :
    xml.same_from cs a b n k =
      .ok (decide (∀ t, k.val ≤ t → t < n.val → charAt cs (a.val + t) = charAt cs (b.val + t))) := by
  rw [xml.same_from]
  by_cases more : k.val < n.val
  · obtain ⟨ak, hak, hakv⟩ := WP.spec_imp_exists (Usize.add_spec (x := a) (y := k) (by omega))
    obtain ⟨bk, hbk, hbkv⟩ := WP.spec_imp_exists (Usize.add_spec (x := b) (y := k) (by omega))
    obtain ⟨k1, hk1, hk1v⟩ := succ_spec more
    have rest := same_from_eq cs a b n k1 ha hb
    by_cases same : charAt cs (a.val + k.val) = charAt cs (b.val + k.val)
    · have su : atU cs ak.val = atU cs bk.val := by
        apply UScalar.eq_of_val_eq; rw [atU_val, atU_val, hakv, hbkv]; exact same
      simp only [UScalar.lt_equiv, more, ite_true, hak, hbk, at_eq, bind_ok, su, hk1, rest]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · intro h t lo hi
        by_cases e : t = k.val
        · subst e; exact same
        · exact h t (by omega) hi
      · intro h t lo hi; exact h t (by omega) hi
    · have su : ¬ atU cs ak.val = atU cs bk.val := by
        intro e; apply same; rw [← hakv, ← hbkv, ← atU_val, ← atU_val, e]
      simp only [UScalar.lt_equiv, more, ite_true, hak, hbk, at_eq, bind_ok, su, ite_false]
      congr 1
      symm; simp only [decide_eq_false_iff_not, not_forall]
      exact ⟨k.val, le_refl _, more, same⟩
  · simp only [UScalar.lt_equiv, more, ite_false]
    congr 1
    symm; simp only [decide_eq_true_eq]
    intro t lo hi; omega
termination_by n.val - k.val
decreasing_by omega

/-- Two consumed words are compared exactly. -/
theorem same_span_eq (cs : alloc.vec.Vec U32) (a a_end b b_end : Usize) {w1 r1 w2 r2 : Word}
    (s1 : (word cs).drop a.val = w1 ++ r1) (h1 : a_end.val = a.val + w1.length)
    (s2 : (word cs).drop b.val = w2 ++ r2) (h2 : b_end.val = b.val + w2.length) :
    xml.same_span cs a a_end b b_end = .ok (decide (w1 = w2)) := by
  obtain ⟨d1, hd1, hd1v⟩ := sub_eq (x := a_end) (y := a) (by omega)
  obtain ⟨d2, hd2, hd2v⟩ := sub_eq (x := b_end) (y := b) (by omega)
  unfold xml.same_span
  simp only [hd1, hd2, bind_ok]
  by_cases lens : w1.length = w2.length
  · have de : d1 = d2 := by apply UScalar.eq_of_val_eq; omega
    simp only [de, ite_true]
    rw [same_from_eq cs a b d2 0#usize (by have := usize_le_max a_end; omega)
      (by have := usize_le_max b_end; omega)]
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · intro h
      apply List.ext_getElem lens
      intro t ht1 ht2
      have := h t (by simp) (by omega)
      rwa [charAt_of_drop s1 ht1, charAt_of_drop s2 ht2] at this
    · intro e t _ ht
      subst e
      rw [charAt_of_drop s1 (by omega), charAt_of_drop s2 (by omega)]
  · have de : ¬ d1 = d2 := by intro e; apply lens; have := congrArg UScalar.val e; omega
    simp only [de, ite_false]
    congr 1
    symm; simp only [decide_eq_false_iff_not]
    intro e; exact lens (by rw [e])

theorem word_from_eq (v cs : alloc.vec.Vec U32) (start k : Usize)
    (hs : start.val + v.val.length ≤ Usize.max) :
    xml.word_from v cs start k =
      .ok (decide (∀ t, k.val ≤ t → (ht : t < v.val.length) → v.val[t].val = charAt cs (start.val + t))) := by
  rw [xml.word_from]
  by_cases more : k.val < v.val.length
  · have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) v k = .ok v.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨sk, hsk, hskv⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := k) (by omega))
    obtain ⟨k1, hk1, hk1v⟩ := succ_spec (y := ⟨v.val.length, by have := v.property; scalar_tac⟩) more
    have rest := word_from_eq v cs start k1 hs
    by_cases same : v.val[k.val].val = charAt cs (start.val + k.val)
    · have su : v.val[k.val] = atU cs sk.val := by
        apply UScalar.eq_of_val_eq; rw [atU_val, hskv]; exact same
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_true, lookup, hsk, at_eq, bind_ok,
        su, hk1, rest]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · intro h t lo ht
        by_cases e : t = k.val
        · subst e; exact same
        · exact h t (by omega) ht
      · intro h t lo ht; exact h t (by omega) ht
    · have su : ¬ v.val[k.val] = atU cs sk.val := by
        intro e; apply same; rw [← hskv, ← atU_val, e]
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_true, lookup, hsk, at_eq, bind_ok,
        su, ite_false]
      congr 1
      symm; simp only [decide_eq_false_iff_not, not_forall]
      exact ⟨k.val, le_refl _, more, same⟩
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_false]
    congr 1
    symm; simp only [decide_eq_true_eq]
    intro t lo ht; omega
termination_by v.val.length - k.val
decreasing_by omega


/-- A buffer is compared exactly with a consumed word. -/
theorem word_is_eq (v cs : alloc.vec.Vec U32) (start stop : Usize) {w rest : Word}
    (split : (word cs).drop start.val = w ++ rest) (hs : stop.val = start.val + w.length) :
    xml.word_is v cs start stop = .ok (decide (word v = w)) := by
  obtain ⟨d, hd, hdv⟩ := sub_eq (x := stop) (y := start) (by omega)
  unfold xml.word_is
  simp only [hd, bind_ok]
  by_cases lens : v.val.length = w.length
  · have de : alloc.vec.Vec.len v = d := by apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len_val]; omega
    simp only [de, ite_true]
    rw [word_from_eq v cs start 0#usize (by have := usize_le_max stop; omega)]
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · intro h
      apply List.ext_getElem (by rw [word_length]; exact lens)
      intro t ht1 ht2
      have := h t (by simp) (by rw [word_length] at ht1; exact ht1)
      rw [charAt_of_drop split ht2] at this
      simpa [word] using this
    · intro e t _ ht
      rw [charAt_of_drop split (by omega)]
      simp [← e, word]
  · have de : ¬ alloc.vec.Vec.len v = d := by
      intro e; apply lens; have := congrArg UScalar.val e; simp [alloc.vec.Vec.len_val] at this; omega
    simp only [de, ite_false]
    congr 1
    symm; simp only [decide_eq_false_iff_not]
    intro e; apply lens; rw [← word_length, e]

/-! ## Buffers -/

theorem push_char_eq (text : alloc.vec.Vec U32) (c : U32) (offset : Usize) :
    xml.push_char text c offset =
      if h : text.val.length < Usize.max then .ok (.Ok (alloc.vec.Vec.from (text.val ++ [c]) (by simp; omega)))
      else .ok (.Err ⟨.ResourceLimit, offset⟩) := by
  unfold xml.push_char
  by_cases h : text.val.length < Usize.max
  · obtain ⟨t, ht, hv⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec text c h)
    have : t = alloc.vec.Vec.from (text.val ++ [c]) (by simp; omega) := by
      apply alloc.vec.Vec.ext; simp [hv]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, h, ht, this, core.num.Usize.MAX]
  · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, h, xml.fail, core.num.Usize.MAX]

theorem word_push (text : alloc.vec.Vec U32) (c : U32) (h : (text.val ++ [c]).length ≤ Usize.max) :
    word (alloc.vec.Vec.from (text.val ++ [c]) h) = word text ++ [c.val] := by
  simp [word]

theorem word_inj {u v : alloc.vec.Vec U32} (h : word u = word v) : u = v := by
  apply alloc.vec.Vec.ext
  have hl : u.val.length = v.val.length := by
    have := congrArg List.length h; simpa [word] using this
  apply List.ext_getElem hl
  intro t h1 h2
  have := congrArg (fun l => l[t]?) h
  simp [word, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at this
  exact UScalar.eq_of_val_eq this

theorem copy_from_spec (cs : alloc.vec.Vec U32) (i stop : Usize) (out : alloc.vec.Vec U32)
    {w rest : Word} (split : (word cs).drop i.val = w ++ rest) (hs : stop.val = i.val + w.length) :
    ∃ r, xml.copy_from cs i stop out = .ok r ∧ (∀ v, r = .Ok v → word v = word out ++ w) ∧
      (out.val.length + w.length ≤ Usize.max → ∃ v, r = .Ok v) := by
  rw [xml.copy_from]
  cases w with
  | nil =>
    have : ¬ i.val < stop.val := by simp at hs; omega
    exact ⟨.Ok out, by simp [UScalar.lt_equiv, this], by simp, fun _ => ⟨out, rfl⟩⟩
  | cons c more =>
    have more_ : i.val < stop.val := by simp at hs; omega
    have c0 := charAt_of_drop split (t := 0) (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at c0
    obtain ⟨i1, hi1, hi1v⟩ := succ_spec more_
    have split1 : (word cs).drop i1.val = more ++ rest := by
      have := drop_after (cs := cs) (i := i.val) (w := [c]) (rest := more ++ rest) (by simpa using split)
      rwa [show i.val + [c].length = i1.val by simp; omega] at this
    by_cases room : out.val.length < Usize.max
    · obtain ⟨r, hr, sound, complete⟩ := copy_from_spec cs i1 stop
        (alloc.vec.Vec.from (out.val ++ [atU cs i.val]) (by simp; omega)) split1 (by simp at hs; omega)
      refine ⟨r, ?_, ?_, ?_⟩
      · simp only [UScalar.lt_equiv, more_, ite_true, at_eq, bind_ok, push_char_eq, room, _root_.dite_true,
          core.result.Result.Insts.CoreOpsTry.branch, hi1, hr]
      · intro v e
        rw [sound v e, word_push, atU_val, c0]; simp
      · intro bound
        exact complete (by simp at bound ⊢; omega)
    · refine ⟨.Err ⟨.ResourceLimit, i⟩, ?_, by simp, ?_⟩
      · simp [UScalar.lt_equiv, more_, at_eq, push_char_eq, room,
          core.result.Result.Insts.CoreOpsTry.branch, same_residual]
      · intro bound; simp at bound; omega
termination_by stop.val - i.val
decreasing_by simp at hs; omega

/-- Copying a consumed word. -/
theorem copy_span_spec (cs : alloc.vec.Vec U32) (start stop : Usize) {w rest : Word}
    (split : (word cs).drop start.val = w ++ rest) (hs : stop.val = start.val + w.length) :
    ∃ v, xml.copy_span cs start stop = .ok (.Ok v) ∧ word v = w := by
  obtain ⟨r, hr, sound, complete⟩ := copy_from_spec cs start stop (alloc.vec.Vec.new U32) split hs
  have bound : (alloc.vec.Vec.new U32).val.length + w.length ≤ Usize.max := by
    have := congrArg List.length split
    simp [word_length] at this
    have := cs.property
    simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.length_nil, Nat.zero_add]
    omega
  obtain ⟨v, rfl⟩ := complete bound
  exact ⟨v, by simp [xml.copy_span, hr], by simpa [word] using sound v rfl⟩

theorem copy_all_eq (u : alloc.vec.Vec U32) : xml.copy_all u = .ok (.Ok u) := by
  have split : (word u).drop (0#usize).val = word u ++ [] := by simp
  obtain ⟨r, hr, sound, complete⟩ := copy_from_spec u 0#usize (alloc.vec.Vec.len u)
    (alloc.vec.Vec.new U32) split (by simp [alloc.vec.Vec.len_val, word_length])
  have bound : (alloc.vec.Vec.new U32).val.length + (word u).length ≤ Usize.max := by
    have := u.property; simp [word_length]
  obtain ⟨v, rfl⟩ := complete bound
  have : v = u := word_inj (by simpa [word] using sound v rfl)
  subst this
  simp [xml.copy_all, hr]

/-! ## Comments -/

theorem lit_dashes : lit "-->" = [45, 45, 62] := by decide
theorem lit_comment : lit "<!--" = [60, 33, 45, 45] := by decide
theorem lit_pi : lit "<?" = [60, 63] := by decide
theorem lit_cdata : lit "<![CDATA[" = [60, 33, 91, 67, 68, 65, 84, 65, 91] := by decide
theorem lit_pi_end : lit "?>" = [63, 62] := by decide
theorem lit_cdata_end : lit "]]>" = [93, 93, 62] := by decide

theorem len_val_eq (cs : alloc.vec.Vec U32) : (alloc.vec.Vec.len cs).val = cs.val.length :=
  alloc.vec.Vec.len_val cs

/-- Advancing inside a buffer does not overflow. -/
theorem next_spec {cs : alloc.vec.Vec U32} {i : Usize} (h : i.val < cs.val.length) :
    ∃ z : Usize, (i + 1#usize : Result Usize) = Result.ok z ∧ z.val = i.val + 1 :=
  succ_spec (y := alloc.vec.Vec.len cs) (by rw [len_val_eq]; exact h)

/-- Advancing to a position inside or at the end of a buffer does not overflow. -/
theorem skip_spec {cs : alloc.vec.Vec U32} {i c : Usize} (h : i.val + c.val ≤ cs.val.length) :
    ∃ z : Usize, (i + c : Result Usize) = Result.ok z ∧ z.val = i.val + c.val :=
  usize_add_le (y := alloc.vec.Vec.len cs) (by rw [len_val_eq]; exact h)

/-- The first character of the word from a position. -/
theorem first_char {cs : alloc.vec.Vec U32} {i : Nat} {c : Nat} {rest : Word}
    (split : (word cs).drop i = c :: rest) : charAt cs i = c := by
  have := charAt_of_drop (w := [c]) (rest := rest) (by simpa using split) (t := 0) (by simp)
  simpa using this

/-- The word from a position starts with the character there, which is not 0. -/
theorem drop_nonzero {cs : alloc.vec.Vec U32} {i : Nat} (h : charAt cs i ≠ 0) :
    i < cs.val.length ∧ (word cs).drop i = charAt cs i :: (word cs).drop (i + 1) :=
  ⟨charAt_inside h, drop_charAt (charAt_inside h)⟩

theorem atU_eq {cs : alloc.vec.Vec U32} {i : Nat} {c : U32} (h : charAt cs i = c.val) : atU cs i = c := by
  apply UScalar.eq_of_val_eq; rw [atU_val, h]

theorem atU_ne {cs : alloc.vec.Vec U32} {i : Nat} {c : U32} (h : charAt cs i ≠ c.val) : ¬ atU cs i = c := by
  intro e; apply h; rw [← atU_val, e]

theorem comment_body_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.comment_body cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ body, (word cs).drop i.val = body ++ lit "-->" ++ (word cs).drop j.val ∧
        CommentBody body) ∧
      (∀ body rest, (word cs).drop i.val = body ++ lit "-->" ++ rest → CommentBody body →
        (∀ c ∈ body, c ≠ 0) → ∃ j, r = .Ok j ∧ j.val = i.val + body.length + 3) := by
  rw [xml.comment_body]
  by_cases zero : charAt cs i.val = 0
  · refine ⟨.Err ⟨.UnexpectedEnd, i⟩, by simp [at_eq, atU_eq (c := 0#u32) (by simpa using zero), xml.fail],
      by simp, ?_⟩
    intro body rest split hb nz
    rw [lit_dashes] at split
    cases body with
    | nil => have := first_char (c := 45) (by simpa using split); omega
    | cons c _ => exact (nz c (by simp) ((first_char (by simpa using split)).symm.trans zero)).elim
  · obtain ⟨inside, hd⟩ := drop_nonzero zero
    obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
    have anz : ¬ atU cs i.val = 0#u32 := atU_ne (by simpa using zero)
    by_cases dash : charAt cs i.val = 45
    · rw [xml.comment_dash]
      by_cases dash2 : charAt cs (i.val + 1) = 45
      · obtain ⟨inside1, hd1⟩ := drop_nonzero (by rw [dash2]; decide : charAt cs (i.val + 1) ≠ 0)
        obtain ⟨i2, hi2, hi2v⟩ := skip_spec (cs := cs) (i := i) (c := 2#usize) (by simp; omega)
        have i2v : i2.val = i.val + 2 := by simpa using hi2v
        by_cases close : charAt cs (i.val + 2) = 62
        · obtain ⟨inside2, hd2⟩ := drop_nonzero (by rw [close]; decide : charAt cs (i.val + 2) ≠ 0)
          obtain ⟨i3, hi3, hi3v⟩ := skip_spec (cs := cs) (i := i) (c := 3#usize) (by simp; omega)
          refine ⟨.Ok i3, ?_, ?_, ?_⟩
          · simp [at_eq, anz, atU_eq (c := 45#u32) (by simpa using dash), hi1,
              atU_eq (c := 45#u32) (show charAt cs i1.val = (45#u32).val by rw [hi1v]; simpa using dash2), hi2,
              atU_eq (c := 62#u32) (show charAt cs i2.val = (62#u32).val by rw [i2v]; simpa using close), hi3]
          · intro j e
            simp at e; subst e
            refine ⟨[], ?_, CommentBody.nil⟩
            rw [show i3.val = i.val + 2 + 1 by simpa using hi3v, lit_dashes, hd, dash, hd1, dash2,
              show i.val + 1 + 1 = i.val + 2 by omega, hd2, close]
            simp
          · intro body rest split hb nz
            refine ⟨i3, rfl, ?_⟩
            have i3v : i3.val = i.val + 3 := by simpa using hi3v
            cases hb with
            | nil => simp [i3v]
            | char hc _ => exact absurd ((first_char (by simpa using split)).symm.trans dash) hc
            | @dash c rest' hc _ =>
              rw [hd] at split
              simp only [List.cons_append, List.cons.injEq] at split
              exact absurd ((first_char (by simpa using split.2)).symm.trans dash2) hc
        · refine ⟨.Err ⟨.Syntax, i⟩, ?_, by simp, ?_⟩
          · simp [at_eq, anz, atU_eq (c := 45#u32) (by simpa using dash), hi1,
              atU_eq (c := 45#u32) (show charAt cs i1.val = (45#u32).val by rw [hi1v]; simpa using dash2), hi2,
              atU_ne (c := 62#u32) (show charAt cs i2.val ≠ (62#u32).val by rw [i2v]; simpa using close),
              xml.fail]
          · intro body rest split hb nz
            exfalso
            rw [lit_dashes] at split
            cases hb with
            | nil =>
              have := charAt_of_drop (w := [45, 45, 62]) (by simpa using split) (t := 2) (by simp)
              exact close this
            | char hc _ => exact hc ((first_char (by simpa using split)).symm.trans dash)
            | @dash c rest' hc _ =>
              rw [hd] at split
              simp only [List.cons_append, List.cons.injEq] at split
              exact hc ((first_char (by simpa using split.2)).symm.trans dash2)
      · obtain ⟨r, hr, sound, complete⟩ := comment_body_spec cs i1
        refine ⟨r, ?_, ?_, ?_⟩
        · simp [at_eq, anz, atU_eq (c := 45#u32) (by simpa using dash), hi1,
            atU_ne (c := 45#u32) (show charAt cs i1.val ≠ (45#u32).val by rw [hi1v]; simpa using dash2), hr]
        · intro j e
          obtain ⟨body, split, hb⟩ := sound j e
          rw [hi1v] at split
          cases body with
          | nil =>
            have := first_char (c := 45) (by rw [lit_dashes] at split; simpa using split)
            exact absurd this dash2
          | cons d rest' =>
            have hdv := first_char (by simpa using split)
            have hb' : CommentBody rest' := by
              cases hb with
              | char _ h => exact h
              | dash h _ => exact absurd hdv dash2
            refine ⟨45 :: d :: rest', ?_, CommentBody.dash (hdv ▸ dash2) hb'⟩
            rw [hd, dash, split]; simp
        · intro body rest split hb nz
          cases hb with
          | nil =>
            rw [lit_dashes] at split
            have := charAt_of_drop (w := [45, 45, 62]) (by simpa using split) (t := 1) (by simp)
            exact absurd this dash2
          | char hc _ => exact absurd ((first_char (by simpa using split)).symm.trans dash) hc
          | @dash c rest' hc hr' =>
            rw [hd] at split
            simp only [List.cons_append, List.cons.injEq] at split
            obtain ⟨j, hj, hjv⟩ := complete (c :: rest') rest (by rw [hi1v]; simpa using split.2)
              (CommentBody.char hc hr') (fun d hd' => nz d (by simp at hd' ⊢; tauto))
            exact ⟨j, hj, by rw [hjv, hi1v]; simp; omega⟩
    · obtain ⟨r, hr, sound, complete⟩ := comment_body_spec cs i1
      refine ⟨r, ?_, ?_, ?_⟩
      · simp [at_eq, anz, atU_ne (c := 45#u32) (by simpa using dash), hi1, hr]
      · intro j e
        obtain ⟨body, split, hb⟩ := sound j e
        refine ⟨charAt cs i.val :: body, ?_, CommentBody.char dash hb⟩
        rw [hi1v] at split
        rw [hd, split]; simp
      · intro body rest split hb nz
        cases hb with
        | nil =>
          rw [lit_dashes] at split
          exact absurd (first_char (c := 45) (by simpa using split)) dash
        | char hc hr' =>
          rw [hd] at split
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨j, hj, hjv⟩ := complete _ rest (by rw [hi1v]; simpa using split.2) hr'
            (fun d hd' => nz d (by simp [hd']))
          exact ⟨j, hj, by rw [hjv, hi1v]; simp; omega⟩
        | dash _ _ => exact absurd ((first_char (by simpa using split)).symm) (Ne.symm dash)
termination_by cs.val.length - i.val
decreasing_by all_goals omega

theorem comment_spec (cs : alloc.vec.Vec U32) (i : Usize) (start : lit "<!--" <+: (word cs).drop i.val) :
    ∃ r, xml.comment cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ w, (word cs).drop i.val = w ++ (word cs).drop j.val ∧ Comment w) ∧
      (∀ w rest, (word cs).drop i.val = w ++ rest → Comment w → (∀ c ∈ w, c ≠ 0) →
        ∃ j, r = .Ok j ∧ j.val = i.val + w.length) := by
  obtain ⟨tail, htail⟩ := start
  have lenOk : i.val + 4 ≤ cs.val.length := by
    have := congrArg List.length htail
    simp [word_length, lit] at this; omega
  obtain ⟨i4, hi4, hi4v⟩ := skip_spec (cs := cs) (i := i) (c := 4#usize) (by simp; omega)
  have i4v : i4.val = i.val + 4 := by simpa using hi4v
  have d4 : (word cs).drop i4.val = tail := by
    have := drop_after (cs := cs) (i := i.val) (w := lit "<!--") (rest := tail) htail.symm
    rwa [show i.val + (lit "<!--").length = i4.val by simp [lit]; omega] at this
  obtain ⟨r, hr, sound, complete⟩ := comment_body_spec cs i4
  refine ⟨r, by simp [xml.comment, hi4, hr], ?_, ?_⟩
  · intro j e
    obtain ⟨body, split, hb⟩ := sound j e
    refine ⟨lit "<!--" ++ body ++ lit "-->", ?_, body, rfl, hb⟩
    rw [← htail, ← d4, split]; simp
  · intro w rest split hw nz
    obtain ⟨body, rfl, hb⟩ := hw
    have e : tail = body ++ lit "-->" ++ rest := by
      have := split.symm.trans htail.symm
      simp only [List.append_assoc] at this
      exact (List.append_cancel_left this).symm.trans (by simp)
    obtain ⟨j, hj, hjv⟩ := complete body rest (d4 ▸ e) hb (fun c hc => nz c (by simp [hc]))
    exact ⟨j, hj, by rw [hjv, i4v]; simp [lit]; omega⟩

/-! ## Processing instructions, CDATA sections and character data -/

theorem pi_end_eq (cs : alloc.vec.Vec U32) (i : Usize) :
    xml.pi_end cs i = .ok (decide (lit "?>" <+: (word cs).drop i.val)) := by
  simp only [xml.pi_end, lift, bind_ok, starts_eq]
  congr 3

theorem cdata_end_eq (cs : alloc.vec.Vec U32) (i : Usize) :
    xml.cdata_end cs i = .ok (decide (lit "]]>" <+: (word cs).drop i.val)) := by
  simp only [xml.cdata_end, lift, bind_ok, starts_eq]
  congr 3

theorem contains_nil {pat : Word} (h : pat ≠ []) : ¬ Contains pat [] := by
  rintro ⟨a, b, e⟩
  exact h (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp e.symm).1).2

theorem contains_cons {pat : Word} {c : Nat} {w : Word} :
    Contains pat (c :: w) ↔ pat <+: c :: w ∨ Contains pat w := by
  constructor
  · rintro ⟨a, b, e⟩
    cases a with
    | nil => left; exact ⟨b, by simpa using e.symm⟩
    | cons d a' =>
      right
      simp only [List.cons_append, List.cons.injEq] at e
      exact ⟨a', b, by simpa using e.2⟩
  · rintro (⟨t, e⟩ | ⟨a, b, e⟩)
    · exact ⟨[], t, by simpa using e.symm⟩
    · exact ⟨c :: a, b, by simp [e]⟩

theorem contains_prefix {pat w more : Word} (h : pat <+: w) : Contains pat (w ++ more) := by
  obtain ⟨t, e⟩ := h
  exact ⟨[], t ++ more, by simp [← e]⟩

theorem prefix_cons_append {pat : Word} {c : Nat} {w more : Word} (h : pat <+: c :: w) :
    pat <+: c :: (w ++ more) := by
  obtain ⟨t, e⟩ := h
  exact ⟨t ++ more, by rw [← List.append_assoc, e]; simp⟩

/-- `?>` cannot begin inside a nonempty word without `?>` that it ends. -/
theorem not_starts_pi {c : Nat} {d rest : Word} (h : ¬ Contains (lit "?>") (c :: d)) :
    ¬ lit "?>" <+: (c :: d) ++ lit "?>" ++ rest := by
  intro p
  rw [lit_pi_end] at p h
  cases d with
  | nil => simp at p
  | cons e d' =>
    simp only [List.cons_append, List.append_assoc] at p
    obtain ⟨t, ht⟩ := p
    simp at ht
    apply h
    rw [ht.1, ht.2.1]
    exact ⟨[], d', rfl⟩

/-- `]]>` cannot begin inside a nonempty word without `]]>` that it ends. -/
theorem not_starts_cdata {c : Nat} {d rest : Word} (h : ¬ Contains (lit "]]>") (c :: d)) :
    ¬ lit "]]>" <+: (c :: d) ++ lit "]]>" ++ rest := by
  intro p
  rw [lit_cdata_end] at p h
  obtain ⟨t, ht⟩ := p
  cases d with
  | nil => simp at ht
  | cons e d' =>
    cases d' with
    | nil => simp at ht
    | cons f d'' =>
      simp at ht
      apply h
      rw [ht.1, ht.2.1, ht.2.2.1]
      exact ⟨[], d'', rfl⟩

theorem pi_body_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.pi_body cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ d, (word cs).drop i.val = d ++ lit "?>" ++ (word cs).drop j.val ∧
        ¬ Contains (lit "?>") d) ∧
      (∀ d rest, (word cs).drop i.val = d ++ lit "?>" ++ rest → ¬ Contains (lit "?>") d →
        (∀ c ∈ d, c ≠ 0) → ∃ j, r = .Ok j ∧ j.val = i.val + d.length + 2) := by
  rw [xml.pi_body]
  by_cases zero : charAt cs i.val = 0
  · refine ⟨.Err ⟨.UnexpectedEnd, i⟩, by simp [at_eq, atU_eq (c := 0#u32) (by simpa using zero), xml.fail],
      by simp, ?_⟩
    intro d rest split _ nz
    rw [lit_pi_end] at split
    cases d with
    | nil => have := first_char (c := 63) (by simpa using split); omega
    | cons c _ => exact (nz c (by simp) ((first_char (by simpa using split)).symm.trans zero)).elim
  · obtain ⟨inside, hd⟩ := drop_nonzero zero
    have anz : ¬ atU cs i.val = 0#u32 := atU_ne (by simpa using zero)
    by_cases close : lit "?>" <+: (word cs).drop i.val
    · obtain ⟨i2, hi2, hi2v⟩ := skip_spec (cs := cs) (i := i) (c := 2#usize) (by
        obtain ⟨t, ht⟩ := close
        have := congrArg List.length ht
        simp [word_length, lit] at this; simp; omega)
      refine ⟨.Ok i2, by simp [at_eq, anz, pi_end_eq, close, hi2], ?_, ?_⟩
      · intro j e
        simp at e; subst e
        refine ⟨[], ?_, contains_nil (by simp [lit])⟩
        obtain ⟨t, ht⟩ := close
        have := drop_after (cs := cs) (i := i.val) (w := lit "?>") (rest := t) ht.symm
        rw [show i.val + (lit "?>").length = i2.val by simp [lit]; simpa using hi2v.symm] at this
        rw [← ht, this]; simp
      · intro d rest split nc nz
        refine ⟨i2, rfl, ?_⟩
        cases d with
        | nil => simpa using hi2v
        | cons c d' => exact absurd (split ▸ close) (not_starts_pi nc)
    · obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
      obtain ⟨r, hr, sound, complete⟩ := pi_body_spec cs i1
      refine ⟨r, by simp [at_eq, anz, pi_end_eq, close, hi1, hr], ?_, ?_⟩
      · intro j e
        obtain ⟨d, split, nc⟩ := sound j e
        refine ⟨charAt cs i.val :: d, ?_, ?_⟩
        · rw [hi1v] at split; rw [hd, split]; simp
        · intro c'
          rcases contains_cons.mp c' with p | p
          · apply close
            rw [hd]
            rw [hi1v] at split
            rw [split]
            simpa [List.append_assoc] using prefix_cons_append (more := lit "?>" ++ (word cs).drop j.val) p
          · exact nc p
      · intro d rest split nc nz
        cases d with
        | nil => exact absurd (by rw [split]; simp) close
        | cons c d' =>
          rw [hd] at split
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨j, hj, hjv⟩ := complete d' rest (by rw [hi1v]; exact split.2)
            (fun p => nc (contains_cons.mpr (Or.inr p))) (fun e he => nz e (by simp [he]))
          exact ⟨j, hj, by rw [hjv, hi1v]; simp; omega⟩
termination_by cs.val.length - i.val
decreasing_by omega

/-- A nonempty prefix of a buffer's word, as a split at its end. -/
theorem prefix_split {cs : alloc.vec.Vec U32} {i : Nat} {w : Word} (h : w <+: (word cs).drop i)
    (hw : w ≠ []) :
    (word cs).drop i = w ++ (word cs).drop (i + w.length) ∧ i + w.length ≤ cs.val.length := by
  obtain ⟨t, ht⟩ := h
  have e := drop_after (cs := cs) (i := i) (w := w) (rest := t) ht.symm
  refine ⟨by rw [e]; exact ht.symm, consumed_le ht.symm hw⟩

theorem no_pi_end_after {a d : Word} (ha : ∀ c ∈ a, c ≠ 63) (h : Contains (lit "?>") (a ++ d)) :
    Contains (lit "?>") d := by
  induction a with
  | nil => simpa using h
  | cons c a' ih =>
    rcases contains_cons.mp (by simpa using h) with p | p
    · obtain ⟨t, ht⟩ := p
      rw [lit_pi_end] at ht
      simp at ht
      exact absurd ht.1 (ha c (by simp))
    · exact ih (fun x hx => ha x (by simp [hx])) p

theorem name_all {t : Word} (h : Name t) : ∀ c ∈ t, NameChar c := by
  obtain ⟨c, rest, rfl, hc, hr⟩ := h
  intro d hd
  rcases List.mem_cons.mp hd with rfl | m
  · exact Or.inl hc
  · exact hr d m

theorem space_not_name {c : Nat} (h : IsSpace c) : ¬ NameChar c := by
  rcases h with rfl | rfl | rfl | rfl <;> simp [NameChar, NameStartChar]

theorem question_not_name : ¬ NameChar 63 := by simp [NameChar, NameStartChar]

/-- The words read by `nameRun` when a known name is followed by a non-name
    character. -/
theorem nameRun_eq {cs : alloc.vec.Vec U32} {i : Nat} {t more : Word}
    (split : (word cs).drop i = t ++ more) (all : ∀ c ∈ t, NameChar c)
    (stop : ∀ c m, more = c :: m → ¬ NameChar c) : nameRun cs i = t := by
  unfold nameRun; rw [split]; exact run_unique all stop

theorem pi_spec (cs : alloc.vec.Vec U32) (i : Usize) (start : lit "<?" <+: (word cs).drop i.val) :
    ∃ r, xml.pi cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ w, (word cs).drop i.val = w ++ (word cs).drop j.val ∧ PI w) ∧
      (∀ w rest, (word cs).drop i.val = w ++ rest → PI w → (∀ c ∈ w, c ≠ 0) →
        ∃ j, r = .Ok j ∧ j.val = i.val + w.length) := by
  obtain ⟨s0, len0⟩ := prefix_split start (by simp [lit_pi])
  rw [lit_pi] at len0
  obtain ⟨i2, hi2, hi2v⟩ := skip_spec (cs := cs) (i := i) (c := 2#usize) (by simp at len0 ⊢; omega)
  have i2v : i2.val = i.val + 2 := by simpa using hi2v
  have s0' : (word cs).drop i.val = lit "<?" ++ (word cs).drop i2.val := by
    rw [i2v]; rw [lit_pi] at s0 ⊢; simpa using s0
  -- Every PI read from `i` has the name run from `i + 2` as its target.
  have shape : ∀ w rest, (word cs).drop i.val = w ++ rest → PI w →
      ∃ body, w = lit "<?" ++ nameRun cs i2.val ++ body ++ lit "?>" ∧ PITarget (nameRun cs i2.val) ∧
        (body = [] ∨ ∃ s d, body = s ++ d ∧ S s ∧ ¬ Contains (lit "?>") d) ∧
        (word cs).drop i2.val = nameRun cs i2.val ++ (body ++ lit "?>" ++ rest) := by
    intro w rest split hw
    obtain ⟨t, body, rfl, ht, hb⟩ := hw
    have e : (word cs).drop i2.val = t ++ (body ++ lit "?>" ++ rest) := by
      have := split
      rw [s0'] at this
      simp only [List.append_assoc] at this ⊢
      exact List.append_cancel_left this
    have tn : nameRun cs i2.val = t := by
      apply nameRun_eq e (name_all ht.1.1)
      intro c m em
      rcases hb with rfl | ⟨sp, d, rfl, ⟨ne, sps⟩, _⟩
      · have : c = 63 := by rw [lit_pi_end] at em; simp at em; omega
        rw [this]; exact question_not_name
      · cases sp with
        | nil => exact absurd rfl ne
        | cons c' sp' =>
          simp at em
          rw [← em.1]; exact space_not_name (sps c' (by simp))
    rw [tn]
    exact ⟨body, rfl, ht, hb, e⟩
  unfold xml.pi
  obtain ⟨r1, h1, sound1, complete1⟩ := ncname_spec cs i2
  cases r1 with
  | Err e =>
    refine ⟨.Err e, by simp [hi2, h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
      by simp, ?_⟩
    intro w rest split hw _
    obtain ⟨body, _, ht, _, _⟩ := shape w rest split hw
    obtain ⟨stop, hstop⟩ := complete1 ht.1
    cases hstop
  | Ok stop =>
    obtain ⟨hstop, ncn⟩ := sound1 stop rfl
    have nsplit : (word cs).drop i2.val = nameRun cs i2.val ++ (word cs).drop stop.val := by
      rw [hstop]; exact nameRun_split cs i2.val
    by_cases reserved : XmlName (nameRun cs i2.val)
    · refine ⟨.Err ⟨.Syntax, i⟩, by simp [hi2, h1, core.result.Result.Insts.CoreOpsTry.branch,
        reserved_target_eq cs i2 stop nsplit hstop, reserved, xml.fail], by simp, ?_⟩
      intro w rest split hw _
      obtain ⟨body, _, ht, _, _⟩ := shape w rest split hw
      exact absurd reserved ht.2
    · have target : PITarget (nameRun cs i2.val) := ⟨ncn, reserved⟩
      unfold xml.pi_rest
      by_cases close : lit "?>" <+: (word cs).drop stop.val
      · obtain ⟨cs1, len1⟩ := prefix_split close (by simp [lit_pi_end])
        obtain ⟨j, hj, hjv⟩ := skip_spec (cs := cs) (i := stop) (c := 2#usize) (by simp [lit] at len1; simp; omega)
        refine ⟨.Ok j, by simp [hi2, h1, core.result.Result.Insts.CoreOpsTry.branch,
          reserved_target_eq cs i2 stop nsplit hstop, reserved, pi_end_eq, close, hj], ?_, ?_⟩
        · intro j' e; simp at e; subst e
          refine ⟨lit "<?" ++ nameRun cs i2.val ++ [] ++ lit "?>", ?_, nameRun cs i2.val, [], rfl, target, Or.inl rfl⟩
          rw [s0', nsplit, cs1, show stop.val + (lit "?>").length = j.val by rw [lit_pi_end]; simpa using hjv.symm]
          simp
        · intro w rest split hw _
          obtain ⟨body, rfl, _, hb, e⟩ := shape w rest split hw
          refine ⟨j, rfl, ?_⟩
          rcases hb with rfl | ⟨sp, d, rfl, ⟨ne, sps⟩, _⟩
          · simp [lit] at hjv ⊢; omega
          · exfalso
            rw [nsplit] at e
            have e2 := List.append_cancel_left e
            cases sp with
            | nil => exact ne rfl
            | cons c' sp' =>
              have hc := first_char (cs := cs) (i := stop.val) (c := c') (rest := sp' ++ d ++ lit "?>" ++ rest)
                (by rw [e2]; simp)
              obtain ⟨t, ht⟩ := close
              have hq := first_char (cs := cs) (i := stop.val) (c := 63) (rest := 62 :: t)
                (by rw [← ht, lit_pi_end]; rfl)
              have := sps c' (by simp)
              rw [← hc, hq] at this
              simp [IsSpace] at this
      · by_cases sp0 : IsSpace (charAt cs stop.val)
        · obtain ⟨inside, hd⟩ := drop_nonzero (by intro z; rw [z] at sp0; exact not_space_zero sp0)
          obtain ⟨s1, hs1, hs1v⟩ := next_spec inside
          obtain ⟨r, hr, sound, complete⟩ := pi_body_spec cs s1
          refine ⟨r, by simp [hi2, h1, core.result.Result.Insts.CoreOpsTry.branch,
            reserved_target_eq cs i2 stop nsplit hstop, reserved, pi_end_eq, close, at_eq, space_eq, atU_val,
            sp0, hs1, hr], ?_, ?_⟩
          · intro j e
            obtain ⟨d, split, nc⟩ := sound j e
            refine ⟨lit "<?" ++ nameRun cs i2.val ++ ([charAt cs stop.val] ++ d) ++ lit "?>", ?_,
              nameRun cs i2.val, [charAt cs stop.val] ++ d, rfl, target,
              Or.inr ⟨[charAt cs stop.val], d, rfl, ⟨by simp, by simp [sp0]⟩, nc⟩⟩
            rw [hs1v] at split
            rw [s0', nsplit, hd, split]; simp
          · intro w rest split hw nz
            obtain ⟨body, rfl, _, hb, e⟩ := shape w rest split hw
            rw [nsplit] at e
            have e2 := List.append_cancel_left e
            rcases hb with rfl | ⟨sp, d, rfl, ⟨ne, sps⟩, nc⟩
            · exact absurd ⟨rest, by rw [e2]; simp⟩ close
            · cases sp with
              | nil => exact absurd rfl ne
              | cons c' sp' =>
                rw [hd] at e2
                simp only [List.cons_append, List.append_assoc, List.cons.injEq] at e2
                obtain ⟨j, hj, hjv⟩ := complete (sp' ++ d) rest (by rw [hs1v]; simpa using e2.2)
                  (fun p => nc (no_pi_end_after (fun x hx => by
                    have := sps x (by simp [hx]); intro e3; rw [e3] at this; simp [IsSpace] at this) p))
                  (fun x hx => nz x (by simp at hx ⊢; tauto))
                refine ⟨j, hj, ?_⟩
                rw [hjv, hs1v, hstop, i2v]; simp [lit]; omega
        · refine ⟨.Err ⟨.Syntax, stop⟩, by simp [hi2, h1, core.result.Result.Insts.CoreOpsTry.branch,
            reserved_target_eq cs i2 stop nsplit hstop, reserved, pi_end_eq, close, at_eq, space_eq, atU_val,
            sp0, xml.fail], by simp, ?_⟩
          intro w rest split hw _
          obtain ⟨body, rfl, _, hb, e⟩ := shape w rest split hw
          rw [nsplit] at e
          have e2 := List.append_cancel_left e
          rcases hb with rfl | ⟨sp, d, rfl, ⟨ne, sps⟩, _⟩
          · exact absurd ⟨rest, by rw [e2]; simp⟩ close
          · cases sp with
            | nil => exact absurd rfl ne
            | cons c' sp' =>
              have hc := first_char (cs := cs) (i := stop.val) (c := c') (rest := sp' ++ d ++ lit "?>" ++ rest)
                (by rw [e2]; simp)
              exact absurd (hc ▸ sps c' (by simp)) sp0

theorem cdata_body_spec (cs : alloc.vec.Vec U32) (i : Usize) (text : alloc.vec.Vec U32) :
    ∃ r, xml.cdata_body cs i text = .ok r ∧
      (∀ t j, r = .Ok (t, j) → ∃ data, (word cs).drop i.val = data ++ lit "]]>" ++ (word cs).drop j.val ∧
        ¬ Contains (lit "]]>") data ∧ word t = word text ++ data) ∧
      (∀ data rest, (word cs).drop i.val = data ++ lit "]]>" ++ rest → ¬ Contains (lit "]]>") data →
        (∀ c ∈ data, c ≠ 0) → text.val.length + data.length ≤ Usize.max →
        ∃ t j, r = .Ok (t, j) ∧ j.val = i.val + data.length + 3) := by
  rw [xml.cdata_body]
  by_cases zero : charAt cs i.val = 0
  · refine ⟨.Err ⟨.UnexpectedEnd, i⟩, by simp [at_eq, atU_eq (c := 0#u32) (by simpa using zero), xml.fail],
      by simp, ?_⟩
    intro d rest split _ nz _
    rw [lit_cdata_end] at split
    cases d with
    | nil => have := first_char (c := 93) (by simpa using split); omega
    | cons c _ => exact (nz c (by simp) ((first_char (by simpa using split)).symm.trans zero)).elim
  · obtain ⟨inside, hd⟩ := drop_nonzero zero
    have anz : ¬ atU cs i.val = 0#u32 := atU_ne (by simpa using zero)
    by_cases close : lit "]]>" <+: (word cs).drop i.val
    · obtain ⟨cs1, len1⟩ := prefix_split close (by simp [lit_cdata_end])
      obtain ⟨i3, hi3, hi3v⟩ := skip_spec (cs := cs) (i := i) (c := 3#usize) (by
        rw [lit_cdata_end] at len1; simp at len1 ⊢; omega)
      refine ⟨.Ok (text, i3), by simp [at_eq, anz, cdata_end_eq, close, hi3], ?_, ?_⟩
      · intro t j e
        simp at e; obtain ⟨rfl, rfl⟩ := e
        refine ⟨[], ?_, contains_nil (by simp [lit_cdata_end]), by simp⟩
        rw [cs1, show i.val + (lit "]]>").length = i3.val by rw [lit_cdata_end]; simpa using hi3v.symm]
        simp
      · intro d rest split nc _ _
        refine ⟨text, i3, rfl, ?_⟩
        cases d with
        | nil => simpa using hi3v
        | cons c d' => exact absurd (split ▸ close) (not_starts_cdata nc)
    · obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
      by_cases room : text.val.length < Usize.max
      · obtain ⟨r, hr, sound, complete⟩ := cdata_body_spec cs i1
          (alloc.vec.Vec.from (text.val ++ [atU cs i.val]) (by simp; omega))
        refine ⟨r, by simp [at_eq, anz, cdata_end_eq, close, push_char_eq, room, hi1, hr,
          core.result.Result.Insts.CoreOpsTry.branch], ?_, ?_⟩
        · intro t j e
          obtain ⟨d, split, nc, ht⟩ := sound t j e
          refine ⟨charAt cs i.val :: d, ?_, ?_, ?_⟩
          · rw [hi1v] at split; rw [hd, split]; simp
          · intro c'
            rcases contains_cons.mp c' with p | p
            · apply close
              rw [hi1v] at split
              rw [hd, split]
              simpa [List.append_assoc] using prefix_cons_append (more := lit "]]>" ++ (word cs).drop j.val) p
            · exact nc p
          · rw [ht, word_push, atU_val]; simp
        · intro d rest split nc nz bound
          cases d with
          | nil => exact absurd (by rw [split]; simp) close
          | cons c d' =>
            rw [hd] at split
            simp only [List.cons_append, List.cons.injEq] at split
            obtain ⟨t, j, hj, hjv⟩ := complete d' rest (by rw [hi1v]; exact split.2)
              (fun p => nc (contains_cons.mpr (Or.inr p))) (fun e he => nz e (by simp [he]))
              (by simp at bound ⊢; omega)
            exact ⟨t, j, hj, by rw [hjv, hi1v]; simp; omega⟩
      · refine ⟨.Err ⟨.ResourceLimit, i⟩, by simp [at_eq, anz, cdata_end_eq, close, push_char_eq, room,
          core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
        intro d rest split nc nz bound
        cases d with
        | nil => exact absurd (by rw [split]; simp) close
        | cons c d' => simp at bound; omega
termination_by cs.val.length - i.val
decreasing_by omega

theorem cdata_spec (cs : alloc.vec.Vec U32) (i : Usize) (text : alloc.vec.Vec U32)
    (start : lit "<![CDATA[" <+: (word cs).drop i.val) :
    ∃ r, xml.cdata cs i text = .ok r ∧
      (∀ t j, r = .Ok (t, j) → ∃ w data, (word cs).drop i.val = w ++ (word cs).drop j.val ∧ CDSect w data ∧
        word t = word text ++ data) ∧
      (∀ w data rest, (word cs).drop i.val = w ++ rest → CDSect w data → (∀ c ∈ w, c ≠ 0) →
        text.val.length + data.length ≤ Usize.max → ∃ t j, r = .Ok (t, j) ∧ j.val = i.val + w.length) := by
  obtain ⟨s0, len0⟩ := prefix_split start (by simp [lit_cdata])
  rw [lit_cdata] at len0
  obtain ⟨i9, hi9, hi9v⟩ := skip_spec (cs := cs) (i := i) (c := 9#usize) (by simp at len0 ⊢; omega)
  have i9v : i9.val = i.val + 9 := by simpa using hi9v
  have d9 : (word cs).drop i.val = lit "<![CDATA[" ++ (word cs).drop i9.val := by
    rw [i9v]; rw [lit_cdata] at s0 ⊢; simpa using s0
  obtain ⟨r, hr, sound, complete⟩ := cdata_body_spec cs i9 text
  refine ⟨r, by simp [xml.cdata, hi9, hr], ?_, ?_⟩
  · intro t j e
    obtain ⟨data, split, nc, ht⟩ := sound t j e
    refine ⟨lit "<![CDATA[" ++ data ++ lit "]]>", data, ?_, ⟨rfl, nc⟩, ht⟩
    rw [d9, split]; simp
  · intro w data rest split hw nz bound
    obtain ⟨rfl, nc⟩ := hw
    have e : (word cs).drop i9.val = data ++ lit "]]>" ++ rest := by
      have := split
      rw [d9] at this
      simp only [List.append_assoc] at this ⊢
      exact List.append_cancel_left this
    obtain ⟨t, j, hj, hjv⟩ := complete data rest e nc (fun c hc => nz c (by simp [hc])) bound
    exact ⟨t, j, hj, by rw [hjv, i9v, lit_cdata, lit_cdata_end]; simp; omega⟩

/-! ## Character data -/

/-- A character that character data may hold: not `<` nor `&` (and not the
    end of the buffer). -/
def DataChar (c : Nat) : Prop := c ≠ 0 ∧ c ≠ 60 ∧ c ≠ 38

theorem data_stop_eq (c : U32) : xml.data_stop c = .ok (decide (¬ DataChar c.val)) := by
  simp [xml.data_stop, DataChar, UScalar.eq_equiv, Bool.or_assoc]

theorem run_append_all {p : Nat → Prop} {w t : Word} (h : ∀ c ∈ w, p c) : run p (w ++ t) = w ++ run p t := by
  induction w with
  | nil => simp
  | cons c w' ih =>
    rw [List.cons_append, run_cons_true (h c (by simp)), ih (fun d hd => h d (by simp [hd]))]
    simp

theorem char_data_spec (cs : alloc.vec.Vec U32) (i : Usize) (text : alloc.vec.Vec U32) :
    ∃ r, xml.char_data cs i text = .ok r ∧
      (∀ t j, r = .Ok (t, j) → j.val = i.val + (run DataChar ((word cs).drop i.val)).length ∧
        word t = word text ++ run DataChar ((word cs).drop i.val) ∧
        ¬ Contains (lit "]]>") (run DataChar ((word cs).drop i.val))) ∧
      (¬ Contains (lit "]]>") (run DataChar ((word cs).drop i.val)) →
        text.val.length + (run DataChar ((word cs).drop i.val)).length ≤ Usize.max →
        ∃ t j, r = .Ok (t, j)) := by
  rw [xml.char_data]
  by_cases data : DataChar (charAt cs i.val)
  · obtain ⟨inside, step⟩ := run_step cs i.val data (by simp [DataChar])
    have hd := drop_charAt inside
    have hrun : run DataChar ((word cs).drop i.val) = charAt cs i.val :: run DataChar ((word cs).drop (i.val + 1)) := by
      rw [hd, run_cons_true data]
    by_cases close : lit "]]>" <+: (word cs).drop i.val
    · refine ⟨.Err ⟨.Syntax, i⟩, by simp [at_eq, data_stop_eq, atU_val, data, cdata_end_eq, close, xml.fail],
        by simp, ?_⟩
      intro nc _
      exfalso
      apply nc
      obtain ⟨t, ht⟩ := close
      have : run DataChar ((word cs).drop i.val) = lit "]]>" ++ run DataChar t := by
        rw [← ht]; exact run_append_all (by rw [lit_cdata_end]; simp [DataChar])
      rw [this]; exact ⟨[], run DataChar t, by simp⟩
    · obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
      by_cases room : text.val.length < Usize.max
      · obtain ⟨r, hr, sound, complete⟩ := char_data_spec cs i1
          (alloc.vec.Vec.from (text.val ++ [atU cs i.val]) (by simp; omega))
        refine ⟨r, by simp [at_eq, data_stop_eq, atU_val, data, cdata_end_eq, close, push_char_eq, room, hi1,
          hr, core.result.Result.Insts.CoreOpsTry.branch], ?_, ?_⟩
        · intro t j e
          obtain ⟨hj, ht, nc⟩ := sound t j e
          rw [hi1v] at hj ht nc
          refine ⟨by rw [hj, step]; omega, by rw [ht, word_push, atU_val, hrun]; simp, ?_⟩
          rw [hrun]
          intro c'
          rcases contains_cons.mp c' with p | p
          · apply close
            have e : (word cs).drop i.val = (charAt cs i.val :: run DataChar ((word cs).drop (i.val + 1))) ++
                (word cs).drop (i.val + 1 + (run DataChar ((word cs).drop (i.val + 1))).length) := by
              rw [hd]
              conv => lhs; rw [drop_run DataChar cs (i.val + 1)]
              simp
            rw [e]; exact p.trans (List.prefix_append _ _)
          · exact nc p
        · intro nc bound
          rw [hrun] at nc bound
          apply complete
          · rw [hi1v]; exact fun p => nc (contains_cons.mpr (Or.inr p))
          · rw [hi1v]; simp at bound ⊢; omega
      · refine ⟨.Err ⟨.ResourceLimit, i⟩, by simp [at_eq, data_stop_eq, atU_val, data, cdata_end_eq, close,
          push_char_eq, room, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
        intro _ bound
        rw [hrun] at bound; simp at bound; omega
  · refine ⟨.Ok (text, i), by simp [at_eq, data_stop_eq, atU_val, data], ?_, fun _ _ => ⟨text, i, rfl⟩⟩
    intro t j e
    simp at e; obtain ⟨rfl, rfl⟩ := e
    have := run_stop cs i.val data
    have empty : run DataChar ((word cs).drop i.val) = [] := List.eq_nil_of_length_eq_zero this
    rw [empty]
    exact ⟨by simp, by simp, contains_nil (by simp [lit_cdata_end])⟩
termination_by cs.val.length - i.val
decreasing_by omega

/-! ## Character references -/

def decFold (v : Nat) (ds : Word) : Nat := ds.foldl (fun a d => a * 10 + (d - 48)) v
def hexFold (v : Nat) (ds : Word) : Nat := ds.foldl (fun a d => a * 16 + (hexDigit d).getD 0) v

/-- A hexadecimal digit. -/
def HexChar (c : Nat) : Prop := hexDigit c ≠ none

theorem decFold_ge (v : Nat) (ds : Word) : v ≤ decFold v ds := by
  induction ds generalizing v with
  | nil => simp [decFold]
  | cons d ds ih =>
    have := ih (v * 10 + (d - 48))
    simp only [decFold, List.foldl_cons] at this ⊢
    omega

theorem hexFold_ge (v : Nat) (ds : Word) : v ≤ hexFold v ds := by
  induction ds generalizing v with
  | nil => simp [hexFold]
  | cons d ds ih =>
    have := ih (v * 16 + (hexDigit d).getD 0)
    simp only [hexFold, List.foldl_cons] at this ⊢
    omega

theorem digit_eq (c : U32) : xml.digit c = .ok (decide (IsDigit c.val)) := by
  simp [xml.digit, IsDigit]

theorem not_digit_zero : ¬ IsDigit 0 := by simp [IsDigit]
theorem not_hex_zero : ¬ HexChar 0 := by simp [HexChar, hexDigit]

theorem hex_value_spec (c : U32) :
    ∃ h, xml.hex_value c = .ok h ∧ h.val = (hexDigit c.val).getD 16 := by
  unfold xml.hex_value
  by_cases d : 48 ≤ c.val ∧ c.val ≤ 57
  · obtain ⟨h, hh, hv, _⟩ := WP.spec_imp_exists (U32.sub_spec (x := c) (y := 48#u32) (by simp; omega))
    refine ⟨h, by simp [digit_eq, IsDigit, d, hh], ?_⟩
    simp [hexDigit, d, hv]
  · by_cases u : 65 ≤ c.val ∧ c.val ≤ 70
    · obtain ⟨h, hh, hv, _⟩ := WP.spec_imp_exists (U32.sub_spec (x := c) (y := 55#u32) (by simp; omega))
      refine ⟨h, ?_, ?_⟩
      · simp only [digit_eq, IsDigit, bind_ok]
        simp [d, u, hh]
      · simp [hexDigit, d, u, hv]
    · by_cases l : 97 ≤ c.val ∧ c.val ≤ 102
      · obtain ⟨h, hh, hv, _⟩ := WP.spec_imp_exists (U32.sub_spec (x := c) (y := 87#u32) (by simp; omega))
        refine ⟨h, ?_, ?_⟩
        · simp only [digit_eq, IsDigit, bind_ok]
          simp [d, u, l, hh]
        · simp [hexDigit, d, u, l, hv]
      · refine ⟨16#u32, ?_, ?_⟩
        · simp only [digit_eq, IsDigit, bind_ok]
          simp [d, u, l]
        · simp [hexDigit, d, u, l]

theorem hexDigit_lt {c : Nat} {h : Nat} (e : hexDigit c = some h) : h < 16 := by
  unfold hexDigit at e
  split at e
  · simp at e; omega
  · split at e
    · simp at e; omega
    · split at e
      · simp at e; omega
      · simp at e

theorem decimal_spec (cs : alloc.vec.Vec U32) (i start : Usize) (v : U32) (origin : Usize)
    (hv : v.val ≤ 0x10FFFF) (hs : start.val ≤ i.val) :
    ∃ r, xml.decimal cs i start v origin = .ok r ∧
      (∀ val j, r = .Ok (val, j) → j.val = i.val + (run IsDigit ((word cs).drop i.val)).length ∧
        val.val = decFold v.val (run IsDigit ((word cs).drop i.val)) ∧
        (i ≠ start ∨ run IsDigit ((word cs).drop i.val) ≠ [])) ∧
      ((i ≠ start ∨ run IsDigit ((word cs).drop i.val) ≠ []) →
        decFold v.val (run IsDigit ((word cs).drop i.val)) ≤ 0x10FFFF → ∃ val j, r = .Ok (val, j)) := by
  rw [xml.decimal]
  by_cases dig : IsDigit (charAt cs i.val)
  · obtain ⟨inside, step⟩ := run_step cs i.val dig not_digit_zero
    have hd := drop_charAt inside
    have hrun : run IsDigit ((word cs).drop i.val) = charAt cs i.val :: run IsDigit ((word cs).drop (i.val + 1)) := by
      rw [hd, run_cons_true dig]
    obtain ⟨m, hm, hmv⟩ := WP.spec_imp_exists (U32.mul_spec (x := v) (y := 10#u32) (by
      rw [U32.max_eq]; simp; omega))
    obtain ⟨d, hd2, hdv, _⟩ := WP.spec_imp_exists (U32.sub_spec (x := atU cs i.val) (y := 48#u32)
      (by rw [atU_val]; simp; exact dig.1))
    obtain ⟨n, hn, hnv⟩ := WP.spec_imp_exists (U32.add_spec (x := m) (y := d) (by
      rw [U32.max_eq, hmv, hdv, atU_val]; simp; have := dig.2; omega))
    have nv : n.val = v.val * 10 + (charAt cs i.val - 48) := by rw [hnv, hmv, hdv, atU_val]; simp
    have fold : decFold v.val (run IsDigit ((word cs).drop i.val)) =
        decFold n.val (run IsDigit ((word cs).drop (i.val + 1))) := by
      rw [hrun, nv]; simp [decFold]
    by_cases big : n.val > 0x10FFFF
    · refine ⟨.Err ⟨.InvalidCharacterReference, origin⟩, by
        simp [at_eq, digit_eq, atU_val, dig, hm, hd2, hn, UScalar.lt_equiv, big, xml.fail], by simp, ?_⟩
      intro _ bound
      have := decFold_ge n.val (run IsDigit ((word cs).drop (i.val + 1)))
      omega
    · obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
      obtain ⟨r, hr, sound, complete⟩ := decimal_spec cs i1 start n origin (by omega) (by omega)
      refine ⟨r, by simp [at_eq, digit_eq, atU_val, dig, hm, hd2, hn, UScalar.lt_equiv, big, hi1, hr], ?_, ?_⟩
      · intro val j e
        obtain ⟨hj, hval, _⟩ := sound val j e
        rw [hi1v] at hj hval
        exact ⟨by rw [hj, step]; omega, by rw [hval, fold], Or.inr (by rw [hrun]; simp)⟩
      · intro _ bound
        rw [fold] at bound
        apply complete _ (by rw [hi1v]; exact bound)
        left; intro e; rw [e] at hi1v; omega
  · have empty : run IsDigit ((word cs).drop i.val) = [] :=
      List.eq_nil_of_length_eq_zero (run_stop cs i.val dig)
    by_cases first : i = start
    · subst first
      refine ⟨.Err ⟨.Syntax, origin⟩, by simp [at_eq, digit_eq, atU_val, dig, xml.fail], by simp, ?_⟩
      intro h; rw [empty] at h; simp at h
    · refine ⟨.Ok (v, i), by simp [at_eq, digit_eq, atU_val, dig, first], ?_, fun _ _ => ⟨v, i, rfl⟩⟩
      intro val j e
      simp at e; obtain ⟨rfl, rfl⟩ := e
      rw [empty]; exact ⟨by simp, by simp [decFold], Or.inl first⟩
termination_by cs.val.length - i.val
decreasing_by omega

theorem hexadecimal_spec (cs : alloc.vec.Vec U32) (i start : Usize) (v : U32) (origin : Usize)
    (hv : v.val ≤ 0x10FFFF) (hs : start.val ≤ i.val) :
    ∃ r, xml.hexadecimal cs i start v origin = .ok r ∧
      (∀ val j, r = .Ok (val, j) → j.val = i.val + (run HexChar ((word cs).drop i.val)).length ∧
        val.val = hexFold v.val (run HexChar ((word cs).drop i.val)) ∧
        (i ≠ start ∨ run HexChar ((word cs).drop i.val) ≠ [])) ∧
      ((i ≠ start ∨ run HexChar ((word cs).drop i.val) ≠ []) →
        hexFold v.val (run HexChar ((word cs).drop i.val)) ≤ 0x10FFFF → ∃ val j, r = .Ok (val, j)) := by
  rw [xml.hexadecimal]
  obtain ⟨h, hh, hhv⟩ := hex_value_spec (atU cs i.val)
  rw [atU_val] at hhv
  by_cases dig : HexChar (charAt cs i.val)
  · obtain ⟨inside, step⟩ := run_step cs i.val dig not_hex_zero
    have hd := drop_charAt inside
    have hrun : run HexChar ((word cs).drop i.val) = charAt cs i.val :: run HexChar ((word cs).drop (i.val + 1)) := by
      rw [hd, run_cons_true dig]
    obtain ⟨hx, hhx⟩ := Option.ne_none_iff_exists'.mp dig
    have hlt := hexDigit_lt hhx
    rw [hhx] at hhv
    simp at hhv
    have small : h < 16#u32 := by rw [UScalar.lt_equiv]; simp [hhv]; exact hlt
    have small' : h.val < 16 := by rw [hhv]; exact hlt
    obtain ⟨m, hm, hmv⟩ := WP.spec_imp_exists (U32.mul_spec (x := v) (y := 16#u32) (by
      rw [U32.max_eq]; simp; omega))
    obtain ⟨n, hn, hnv⟩ := WP.spec_imp_exists (U32.add_spec (x := m) (y := h) (by
      rw [U32.max_eq, hmv, hhv]; simp; omega))
    have nv : n.val = v.val * 16 + hx := by rw [hnv, hmv, hhv]; simp
    have fold : hexFold v.val (run HexChar ((word cs).drop i.val)) =
        hexFold n.val (run HexChar ((word cs).drop (i.val + 1))) := by
      rw [hrun, nv]; simp [hexFold, hhx]
    by_cases big : n.val > 0x10FFFF
    · refine ⟨.Err ⟨.InvalidCharacterReference, origin⟩, by
        simp [at_eq, hh, small, small', hm, hn, UScalar.lt_equiv, big, xml.fail], by simp, ?_⟩
      intro _ bound
      have := hexFold_ge n.val (run HexChar ((word cs).drop (i.val + 1)))
      omega
    · obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
      obtain ⟨r, hr, sound, complete⟩ := hexadecimal_spec cs i1 start n origin (by omega) (by omega)
      refine ⟨r, by simp [at_eq, hh, small, small', hm, hn, UScalar.lt_equiv, big, hi1, hr], ?_, ?_⟩
      · intro val j e
        obtain ⟨hj, hval, _⟩ := sound val j e
        rw [hi1v] at hj hval
        exact ⟨by rw [hj, step]; omega, by rw [hval, fold], Or.inr (by rw [hrun]; simp)⟩
      · intro _ bound
        rw [fold] at bound
        apply complete _ (by rw [hi1v]; exact bound)
        left; intro e; rw [e] at hi1v; omega
  · have empty : run HexChar ((word cs).drop i.val) = [] :=
      List.eq_nil_of_length_eq_zero (run_stop cs i.val dig)
    have none_ : hexDigit (charAt cs i.val) = none := by simpa [HexChar] using dig
    rw [none_] at hhv
    simp at hhv
    have big : ¬ h < 16#u32 := by rw [UScalar.lt_equiv]; simp [hhv]
    have big' : ¬ h.val < 16 := by rw [hhv]; simp
    by_cases first : i = start
    · subst first
      refine ⟨.Err ⟨.Syntax, origin⟩, by simp [at_eq, hh, big, big', xml.fail], by simp, ?_⟩
      intro h'; rw [empty] at h'; simp at h'
    · refine ⟨.Ok (v, i), by simp [at_eq, hh, big, big', first], ?_, fun _ _ => ⟨v, i, rfl⟩⟩
      intro val j e
      simp at e; obtain ⟨rfl, rfl⟩ := e
      rw [empty]; exact ⟨by simp, by simp [hexFold], Or.inl first⟩
termination_by cs.val.length - i.val
decreasing_by omega

end Rowl.XmlScan
