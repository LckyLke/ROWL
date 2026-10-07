import Rowl.XmlComplete

/-!
# The XML declaration and Misc

`xml_declaration` reads the grammar's `XMLDecl` (version 1.x, an encoding
declaration naming UTF-8, a standalone declaration) and `misc` reads `Misc*`.
-/

namespace Rowl.XmlDecl
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs Rowl.XmlEntities Rowl.XmlAttributes Rowl.XmlTags Rowl.XmlNamespaces Rowl.XmlContent Rowl.XmlElements Rowl.XmlComplete
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

theorem lit_xmlDecl : lit "<?xml" = [60, 63, 120, 109, 108] := by decide
theorem lit_version : lit "version" = [118, 101, 114, 115, 105, 111, 110] := by decide
theorem lit_encoding : lit "encoding" = [101, 110, 99, 111, 100, 105, 110, 103] := by decide
theorem lit_standalone : lit "standalone" = [115, 116, 97, 110, 100, 97, 108, 111, 110, 101] := by decide
theorem lit_one_dot : lit "1." = [49, 46] := by decide
theorem lit_yes : lit "yes" = [121, 101, 115] := by decide
theorem lit_no : lit "no" = [110, 111] := by decide

theorem map_one_dot : ([49#u8, 46#u8] : List U8).map (·.val) = lit "1." := by decide
theorem map_yes : ([121#u8, 101#u8, 115#u8] : List U8).map (·.val) = lit "yes" := by decide
theorem map_no : ([110#u8, 111#u8] : List U8).map (·.val) = lit "no" := by decide
theorem map_encoding :
    ([101#u8, 110#u8, 99#u8, 111#u8, 100#u8, 105#u8, 110#u8, 103#u8] : List U8).map (·.val) = lit "encoding" := by
  decide
theorem map_standalone :
    ([115#u8, 116#u8, 97#u8, 110#u8, 100#u8, 97#u8, 108#u8, 111#u8, 110#u8, 101#u8] : List U8).map (·.val) =
      lit "standalone" := by decide
theorem map_version :
    ([118#u8, 101#u8, 114#u8, 115#u8, 105#u8, 111#u8, 110#u8] : List U8).map (·.val) = lit "version" := by decide
theorem map_xmlDecl : ([60#u8, 63#u8, 120#u8, 109#u8, 108#u8] : List U8).map (·.val) = lit "<?xml" := by decide

/-- Two maximal runs of spaces end at the same character. -/
theorem keyword_after_spaces {a x s y : Word} {c c' : Nat} (ha : OptS a) (hc : ¬ IsSpace c)
    (hs : OptS s) (hc' : ¬ IsSpace c') (e : a ++ c :: x = s ++ c' :: y) : a = s ∧ c = c' := by
  have r1 : run IsSpace (a ++ c :: x) = a :=
    run_unique ha (fun d m e' => by simp at e'; rw [← e'.1]; exact hc)
  have r2 : run IsSpace (s ++ c' :: y) = s :=
    run_unique hs (fun d m e' => by simp at e'; rw [← e'.1]; exact hc')
  have hsa : a = s := by rw [← r1, ← r2, e]
  subst hsa
  simp at e
  exact ⟨rfl, e.1⟩

theorem quote_not_space {q : Nat} (h : Quote q) : ¬ IsSpace q := by
  rcases h with rfl | rfl <;> simp [IsSpace]

theorem quote_not_digit {q : Nat} (h : Quote q) : ¬ IsDigit q := by
  rcases h with rfl | rfl <;> simp [IsDigit]

/-! ## VersionInfo -/

theorem version_digits_spec (cs : alloc.vec.Vec U32) (i start : Usize) (q : U32) (hq : ¬ IsDigit q.val)
    (hq0 : q.val ≠ 0) (hs : start.val ≤ i.val) :
    ∃ r, xml.version_digits cs i start q = .ok r ∧
      (∀ j, r = .Ok j → ∃ ds, (word cs).drop i.val = ds ++ q.val :: (word cs).drop j.val ∧
        (∀ d ∈ ds, IsDigit d) ∧ (i.val = start.val → ds ≠ []) ∧ j.val = i.val + ds.length + 1) ∧
      (∀ ds rest, (word cs).drop i.val = ds ++ q.val :: rest → (∀ d ∈ ds, IsDigit d) →
        (i.val = start.val → ds ≠ []) → ∃ j, r = .Ok j) := by
  rw [xml.version_digits]
  simp only [at_eq, bind_ok, digit_eq, atU_val]
  by_cases dg : IsDigit (charAt cs i.val)
  · have nz : charAt cs i.val ≠ 0 := fun z => not_digit_zero (z ▸ dg)
    obtain ⟨inside, hd⟩ := drop_nonzero nz
    obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
    obtain ⟨r, hr, sound, complete⟩ := version_digits_spec cs i1 start q hq hq0 (by omega)
    refine ⟨r, by simp [dg, hi1, hr], ?_, ?_⟩
    · intro j e
      obtain ⟨ds, split, all, _, hj⟩ := sound j e
      refine ⟨charAt cs i.val :: ds, ?_, ?_, fun _ => by simp, by rw [hj, hi1v]; simp; omega⟩
      · rw [hd, ← hi1v, split]; simp
      · intro d hd'; simp at hd'; rcases hd' with rfl | m
        · exact dg
        · exact all d m
    · intro ds rest split all _
      cases ds with
      | nil =>
        exfalso; have := first_char (by simpa using split); rw [this] at dg; exact hq dg
      | cons d ds' =>
        rw [hd] at split; simp at split
        exact complete ds' rest (by rw [hi1v]; exact split.2) (fun d' h => all d' (by simp [h]))
          (fun e => by omega)
  · by_cases st : i = start
    · subst st
      refine ⟨.Err ⟨.Syntax, i⟩, by simp [dg, xml.fail], by simp, ?_⟩
      intro ds rest split all ne
      exfalso
      cases ds with
      | nil => exact ne rfl rfl
      | cons d ds' => exact dg (by rw [first_char (rest := ds' ++ q.val :: rest) (by simpa using split)];
                                   exact all d (by simp))
    · have st' : ¬ i.val = start.val := fun e => st (UScalar.eq_of_val_eq e)
      by_cases eq : charAt cs i.val = q.val
      · obtain ⟨inside, hd⟩ := drop_nonzero (fun z => hq0 (by rw [← eq, z]))
        obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
        have qe : atU cs i.val = q := atU_eq eq
        refine ⟨.Ok i1, by simp [dg, st, qe, hi1], ?_, fun _ _ _ _ _ => ⟨i1, rfl⟩⟩
        intro j e; simp at e; subst e
        refine ⟨[], ?_, by simp, fun e => absurd e st', by simp [hi1v]⟩
        rw [hd, eq, ← hi1v]; simp
      · have qe : ¬ atU cs i.val = q := atU_ne eq
        refine ⟨.Err ⟨.Syntax, i⟩, by simp [dg, st, qe, xml.fail], by simp, ?_⟩
        intro ds rest split all _
        exfalso
        cases ds with
        | nil => exact eq (first_char (by simpa using split))
        | cons d ds' => exact dg (by rw [first_char (rest := ds' ++ q.val :: rest) (by simpa using split)];
                                     exact all d (by simp))
termination_by cs.val.length - i.val
decreasing_by omega

theorem version_value_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.version_value cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ q num, (word cs).drop i.val = q :: num ++ q :: (word cs).drop j.val ∧ Quote q ∧
        VersionNum num ∧ j.val = i.val + num.length + 2) ∧
      (∀ q num rest, (word cs).drop i.val = q :: num ++ q :: rest → Quote q → VersionNum num →
        ∃ j, r = .Ok j) := by
  unfold xml.version_value
  simp only [at_eq, bind_ok, quote_eq, atU_val]
  by_cases hq : Quote (charAt cs i.val)
  · have nz : charAt cs i.val ≠ 0 := fun z => by rw [z] at hq; rcases hq with h | h <;> simp at h
    obtain ⟨inside, hd⟩ := drop_nonzero nz
    obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
    simp only [hq, decide_true, ite_true, hi1, bind_ok, lift, starts_eq, bytes_make, map_one_dot,
      decide_eq_true_eq]
    by_cases one : lit "1." <+: (word cs).drop i1.val
    · rw [if_pos one]
      obtain ⟨d2, inside2⟩ := prefix_split one (by rw [lit_one_dot]; simp)
      rw [lit_one_dot] at d2 inside2
      simp only [List.length_cons, List.length_nil] at d2 inside2
      obtain ⟨i3, hi3, hi3v⟩ := skip_spec (cs := cs) (i := i) (c := 3#usize) (by simp; omega)
      have i3v : i3.val = i.val + 3 := by simpa using hi3v
      have qv : (atU cs i.val).val = charAt cs i.val := atU_val cs i.val
      obtain ⟨r, hr, sound, complete⟩ := version_digits_spec cs i3 i3 (atU cs i.val)
        (by rw [qv]; exact quote_not_digit hq) (by rw [qv]; exact nz) (le_refl _)
      refine ⟨r, by simp [hi3, hr], ?_, ?_⟩
      · intro j e
        obtain ⟨ds, split, all, ne, hj⟩ := sound j e
        refine ⟨charAt cs i.val, lit "1." ++ ds, ?_, hq, ⟨ds, rfl, ne rfl, all⟩, by rw [hj, i3v]; simp [lit_one_dot]; omega⟩
        rw [hd, ← hi1v, d2, show i1.val + 2 = i3.val by omega, split, qv]; simp [lit_one_dot]
      · intro q num rest split hq' hnum
        obtain ⟨ds, rfl, ne, all⟩ := hnum
        have cq : charAt cs i.val = q := first_char (rest := lit "1." ++ ds ++ q :: rest) (by rw [split]; simp)
        apply complete ds rest _ all (fun _ => ne)
        have := drop_after (cs := cs) (i := i.val) (w := q :: lit "1.") (rest := ds ++ q :: rest) (by rw [split]; simp)
        rw [qv, cq, i3v]; simpa [lit_one_dot] using this
    · rw [if_neg one]
      refine ⟨.Err ⟨.Syntax, i⟩, by simp [xml.fail], by simp, ?_⟩
      intro q num rest split _ hnum
      exfalso; apply one
      obtain ⟨ds, rfl, _, _⟩ := hnum
      rw [hi1v, hd] at *
      rw [hd] at split; simp at split
      rw [split.2]; exact ⟨ds ++ q :: rest, by simp⟩
  · refine ⟨.Err ⟨.Syntax, i⟩, by simp [hq, xml.fail], by simp, ?_⟩
    intro q num rest split hq' _
    exact absurd (by rw [first_char (c := q) (rest := num ++ q :: rest) (by rw [split]; simp)]; exact hq') hq

/-! ## EncodingDecl -/

def AsciiLetter (c : Nat) : Prop := (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122)
def EncChar (c : Nat) : Prop := (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ IsDigit c ∨ c = 46 ∨ c = 95 ∨ c = 45

theorem ascii_letter_eq (c : U32) : xml.ascii_letter c = .ok (decide (AsciiLetter c.val)) := by
  simp [xml.ascii_letter, AsciiLetter, UScalar.le_equiv]

theorem enc_char_eq (c : U32) : xml.enc_char c = .ok (decide (EncChar c.val)) := by
  simp [xml.enc_char, ascii_letter_eq, digit_eq, EncChar, AsciiLetter, UScalar.eq_equiv, Bool.or_assoc]

theorem not_enc_char_zero : ¬ EncChar 0 := by simp [EncChar, AsciiLetter, IsDigit]

theorem enc_end_eq (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ j : Usize, xml.enc_end cs i = .ok j ∧ j.val = i.val + (run EncChar ((word cs).drop i.val)).length := by
  rw [xml.enc_end]
  by_cases h : EncChar (charAt cs i.val)
  · obtain ⟨inside, step⟩ := run_step cs i.val h not_enc_char_zero
    obtain ⟨next, hn, hv⟩ := next_spec inside
    obtain ⟨j, hj, hjv⟩ := enc_end_eq cs next
    refine ⟨j, ?_, ?_⟩
    · simp [at_eq, enc_char_eq, atU_val, h, hn, hj]
    · rw [hjv, hv, step]; omega
  · refine ⟨i, ?_, ?_⟩
    · simp [at_eq, enc_char_eq, atU_val, h]
    · rw [run_stop cs i.val h]; simp
termination_by cs.val.length - i.val
decreasing_by
  have := (run_step cs i.val h not_enc_char_zero).1
  omega

theorem utf8_letters_eq (cs : alloc.vec.Vec U32) (start : Usize) {w rest : Word}
    (split : (word cs).drop start.val = w ++ rest) (hw : w.length = 5) :
    xml.utf8_letters cs start = .ok (decide (Utf8Name w)) := by
  have fit : start.val + 5 ≤ cs.val.length := by
    have := congrArg List.length split; simp [word_length] at this; omega
  obtain ⟨s1, h1, v1⟩ := skip_spec (cs := cs) (i := start) (c := 1#usize) (by simp; omega)
  obtain ⟨s2, h2, v2⟩ := skip_spec (cs := cs) (i := start) (c := 2#usize) (by simp; omega)
  obtain ⟨s3, h3, v3⟩ := skip_spec (cs := cs) (i := start) (c := 3#usize) (by simp; omega)
  obtain ⟨s4, h4, v4⟩ := skip_spec (cs := cs) (i := start) (c := 4#usize) (by simp; omega)
  have e1 : s1.val = start.val + 1 := by simpa using v1
  have e2 : s2.val = start.val + 2 := by simpa using v2
  have e3 : s3.val = start.val + 3 := by simpa using v3
  have e4 : s4.val = start.val + 4 := by simpa using v4
  have c0 := charAt_of_drop split (t := 0) (by omega)
  have c1 := charAt_of_drop split (t := 1) (by omega)
  have c2 := charAt_of_drop split (t := 2) (by omega)
  have c3 := charAt_of_drop split (t := 3) (by omega)
  have c4 := charAt_of_drop split (t := 4) (by omega)
  have k117 : 32 ≤ (117#u32 : U32).val := by simp
  have k116 : 32 ≤ (116#u32 : U32).val := by simp
  have k102 : 32 ≤ (102#u32 : U32).val := by simp
  unfold xml.utf8_letters
  simp only [at_eq, bind_ok, h1, h2, h3, h4, caseless_eq _ _ k117, caseless_eq _ _ k116, caseless_eq _ _ k102,
    atU_val, atU_eq_iff, e1, e2, e3, e4]
  simp only [Nat.add_zero] at c0
  rw [c0, c1, c2, c3, c4]
  obtain ⟨a, b, c, d, e, rfl⟩ : ∃ a b c d e, w = [a, b, c, d, e] := by
    match w, hw with
    | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩
  simp [Utf8Name]
  ac_rfl

theorem utf8_name_eq (cs : alloc.vec.Vec U32) (start stop : Usize) {w rest : Word}
    (split : (word cs).drop start.val = w ++ rest) (hs : stop.val = start.val + w.length) :
    xml.utf8_name cs start stop = .ok (decide (Utf8Name w)) := by
  unfold xml.utf8_name
  obtain ⟨d, hd, hdv⟩ := sub_eq (x := stop) (y := start) (by omega)
  simp only [hd, bind_ok]
  by_cases five : w.length = 5
  · have : d = 5#usize := UScalar.eq_of_val_eq (by simp; omega)
    rw [if_pos this, utf8_letters_eq cs start split five]
  · have : ¬ d = 5#usize := fun e => five (by have := congrArg UScalar.val e; simp at this; omega)
    rw [if_neg this]
    congr 1; symm; apply decide_eq_false
    rintro ⟨a, b, c, rfl, _⟩; exact five rfl

theorem quote_ne_zero {q : Nat} (h : Quote q) : q ≠ 0 := by rcases h with rfl | rfl <;> simp

theorem quote_not_enc {q : Nat} (h : Quote q) : ¬ EncChar q := by
  rcases h with rfl | rfl <;> simp [EncChar, AsciiLetter, IsDigit]

theorem encoding_value_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.encoding_value cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ q ename, (word cs).drop i.val = q :: ename ++ q :: (word cs).drop j.val ∧ Quote q ∧
        EncName ename ∧ Utf8Name ename ∧ j.val = i.val + ename.length + 2) ∧
      (∀ q ename rest, (word cs).drop i.val = q :: ename ++ q :: rest → Quote q → EncName ename →
        Utf8Name ename → ∃ j, r = .Ok j) := by
  unfold xml.encoding_value
  simp only [at_eq, bind_ok, quote_eq, atU_val]
  by_cases hq : Quote (charAt cs i.val)
  · obtain ⟨inside, hd⟩ := drop_nonzero (quote_ne_zero hq)
    obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
    simp only [hq, decide_true, ite_true, hi1, bind_ok, at_eq, ascii_letter_eq, atU_val]
    by_cases al : AsciiLetter (charAt cs i1.val)
    · have nz1 : charAt cs i1.val ≠ 0 := fun z => by rw [z] at al; simp [AsciiLetter] at al
      obtain ⟨inside1, hd1⟩ := drop_nonzero nz1
      obtain ⟨i2, hi2, hi2v⟩ := skip_spec (cs := cs) (i := i) (c := 2#usize) (by simp; omega)
      have i2v : i2.val = i1.val + 1 := by simp at hi2v; omega
      obtain ⟨e, he, hev⟩ := enc_end_eq cs i2
      have esplit := drop_run EncChar cs i2.val
      rw [← hev] at esplit
      have eall : ∀ c ∈ run EncChar ((word cs).drop i2.val), EncChar c := run_all
      have efollow : ¬ EncChar (charAt cs e.val) := by rw [hev]; exact run_follow cs i2.val not_enc_char_zero
      generalize hr : run EncChar ((word cs).drop i2.val) = tl at esplit hev eall
      have nsplit : (word cs).drop i1.val = (charAt cs i1.val :: tl) ++ (word cs).drop e.val := by
        rw [hd1, ← i2v, esplit]; simp
      simp only [al, decide_true, ite_true, hi2, he, bind_ok, at_eq]
      by_cases qe : charAt cs e.val = charAt cs i.val
      · have qe' : atU cs e.val = atU cs i.val := UScalar.eq_of_val_eq (by rw [atU_val, atU_val, qe])
        obtain ⟨insideE, hdE⟩ := drop_nonzero (by rw [qe]; exact quote_ne_zero hq)
        rw [utf8_name_eq cs i1 e nsplit (by simp; omega)]
        simp only [qe', ne_eq, not_true_eq_false, ite_false, bind_ok]
        have hename : EncName (charAt cs i1.val :: tl) := ⟨_, tl, rfl, al, eall⟩
        by_cases u8 : Utf8Name (charAt cs i1.val :: tl)
        · obtain ⟨e1, he1, he1v⟩ := next_spec insideE
          refine ⟨.Ok e1, by simp [u8, he1], ?_, fun _ _ _ _ _ _ _ => ⟨e1, rfl⟩⟩
          intro j eq; simp at eq; subst eq
          refine ⟨charAt cs i.val, charAt cs i1.val :: tl, ?_, hq, hename, u8, by simp; omega⟩
          rw [hd, ← hi1v, nsplit, hdE, qe, ← he1v]; simp
        · refine ⟨.Err ⟨.UnsupportedEncoding, i1⟩, by simp [u8, xml.fail], by simp, ?_⟩
          intro q ename rest split hq' hen hu
          exfalso; apply u8
          have cq : charAt cs i.val = q := first_char (rest := ename ++ q :: rest) (by rw [split]; simp)
          have d1 : (word cs).drop i1.val = ename ++ q :: rest := by
            rw [hd, cq] at split; simp at split; rw [hi1v]; exact split
          have : charAt cs i1.val :: tl = ename := by
            obtain ⟨c0, r0, rfl, _, rall⟩ := hen
            have c0e : charAt cs i1.val = c0 := first_char (rest := r0 ++ q :: rest) (by rw [d1]; simp)
            have d2 : (word cs).drop i2.val = r0 ++ q :: rest := by
              rw [hd1, c0e] at d1; simp at d1; rw [i2v]; exact d1
            have tlr : tl = r0 := by
              rw [← hr, d2]; exact run_unique rall (fun c m e' => by simp at e'; rw [← e'.1]; exact quote_not_enc hq')
            rw [c0e, tlr]
          rw [this]; exact hu
      · have qe' : ¬ atU cs e.val = atU cs i.val := fun h => qe (by rw [← atU_val, h, atU_val])
        refine ⟨.Err ⟨.Syntax, e⟩, by simp [qe', xml.fail], by simp, ?_⟩
        intro q ename rest split hq' hen _
        exfalso; apply qe
        have cq : charAt cs i.val = q := first_char (rest := ename ++ q :: rest) (by rw [split]; simp)
        have d1 : (word cs).drop i1.val = ename ++ q :: rest := by
          rw [hd, cq] at split; simp at split; rw [hi1v]; exact split
        obtain ⟨c0, r0, rfl, _, rall⟩ := hen
        have c0e : charAt cs i1.val = c0 := first_char (rest := r0 ++ q :: rest) (by rw [d1]; simp)
        have d2 : (word cs).drop i2.val = r0 ++ q :: rest := by
          rw [hd1, c0e] at d1; simp at d1; rw [i2v]; exact d1
        have tlr : tl = r0 := by
          rw [← hr, d2]; exact run_unique rall (fun c m e' => by simp at e'; rw [← e'.1]; exact quote_not_enc hq')
        rw [cq]
        have ca := charAt_after (cs := cs) (i := i2.val) (w := r0) (rest := q :: rest) d2
        rw [hev, tlr]
        simpa using ca
    · refine ⟨.Err ⟨.Syntax, i1⟩, by simp [al, xml.fail], by simp, ?_⟩
      intro q ename rest split hq' hen _
      exfalso; apply al
      have cq : charAt cs i.val = q := first_char (rest := ename ++ q :: rest) (by rw [split]; simp)
      have d1 : (word cs).drop i1.val = ename ++ q :: rest := by
        rw [hd, cq] at split; simp at split; rw [hi1v]; exact split
      obtain ⟨c0, r0, rfl, h0, _⟩ := hen
      rw [first_char (c := c0) (rest := r0 ++ q :: rest) (by rw [d1]; simp)]; exact h0
  · refine ⟨.Err ⟨.Syntax, i⟩, by simp [hq, xml.fail], by simp, ?_⟩
    intro q ename rest split hq' _ _
    exact absurd (by rw [first_char (c := q) (rest := ename ++ q :: rest) (by rw [split]; simp)]; exact hq') hq

/-! ## SDDecl -/

theorem yes_no_end_eq (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ j : Usize, xml.yes_no_end cs i = .ok j ∧
      j.val = if lit "yes" <+: (word cs).drop i.val then i.val + 3
              else if lit "no" <+: (word cs).drop i.val then i.val + 2 else i.val := by
  unfold xml.yes_no_end
  simp only [lift, bind_ok, starts_eq, bytes_make, map_yes, map_no, decide_eq_true_eq]
  by_cases y : lit "yes" <+: (word cs).drop i.val
  · obtain ⟨_, fit⟩ := prefix_split y (by rw [lit_yes]; simp)
    obtain ⟨j, hj, hjv⟩ := skip_spec (cs := cs) (i := i) (c := 3#usize) (by simp [lit_yes] at fit; simp; omega)
    exact ⟨j, by rw [if_pos y]; exact hj, by rw [if_pos y]; simpa using hjv⟩
  · by_cases n : lit "no" <+: (word cs).drop i.val
    · obtain ⟨_, fit⟩ := prefix_split n (by rw [lit_no]; simp)
      obtain ⟨j, hj, hjv⟩ := skip_spec (cs := cs) (i := i) (c := 2#usize) (by simp [lit_no] at fit; simp; omega)
      exact ⟨j, by rw [if_neg y, if_pos n]; exact hj, by rw [if_neg y, if_pos n]; simpa using hjv⟩
    · exact ⟨i, by rw [if_neg y, if_neg n], by rw [if_neg y, if_neg n]⟩

theorem standalone_value_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.standalone_value cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ q yn, (word cs).drop i.val = q :: yn ++ q :: (word cs).drop j.val ∧ Quote q ∧
        (yn = lit "yes" ∨ yn = lit "no") ∧ j.val = i.val + yn.length + 2) ∧
      (∀ q yn rest, (word cs).drop i.val = q :: yn ++ q :: rest → Quote q → (yn = lit "yes" ∨ yn = lit "no") →
        ∃ j, r = .Ok j) := by
  unfold xml.standalone_value
  simp only [at_eq, bind_ok, quote_eq, atU_val]
  by_cases hq : Quote (charAt cs i.val)
  · obtain ⟨inside, hd⟩ := drop_nonzero (quote_ne_zero hq)
    obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
    obtain ⟨e, he, hev⟩ := yes_no_end_eq cs i1
    simp only [hq, decide_true, ite_true, hi1, he, bind_ok]
    unfold xml.standalone_close
    simp only [hi1, bind_ok, at_eq]
    -- what follows the opening quote
    have after : ∀ yn rest, (word cs).drop i.val = charAt cs i.val :: yn ++ charAt cs i.val :: rest →
        (word cs).drop i1.val = yn ++ charAt cs i.val :: rest := by
      intro yn rest split; rw [hd] at split; simp at split; rw [hi1v]; exact split
    have closing : ∀ (yn : Word) (k : Nat), (word cs).drop i1.val = yn ++ (word cs).drop k → yn.length = 3 ∨ yn.length = 2 →
        e.val = i1.val + yn.length → (word cs).drop e.val = (word cs).drop k := by
      intro yn k split _ hev'
      rw [hev']; exact drop_after split
    by_cases y : lit "yes" <+: (word cs).drop i1.val
    · rw [if_pos y] at hev
      have ne : ¬ e = i1 := fun h => by have := congrArg UScalar.val h; omega
      rw [if_neg ne]
      obtain ⟨d3, fit⟩ := prefix_split y (by rw [lit_yes]; simp)
      simp only [lit_yes, List.length_cons, List.length_nil] at d3 fit
      by_cases qe : charAt cs e.val = charAt cs i.val
      · have qe' : atU cs e.val = atU cs i.val := UScalar.eq_of_val_eq (by rw [atU_val, atU_val, qe])
        obtain ⟨insideE, dE⟩ := drop_nonzero (by rw [qe]; exact quote_ne_zero hq)
        obtain ⟨e1, he1, he1v⟩ := next_spec insideE
        refine ⟨.Ok e1, by simp [qe', he1], ?_, fun _ _ _ _ _ _ => ⟨e1, rfl⟩⟩
        intro j eq; simp at eq; subst eq
        refine ⟨charAt cs i.val, lit "yes", ?_, hq, Or.inl rfl, by rw [he1v, hev, hi1v]; simp [lit_yes]⟩
        rw [hd, ← hi1v, d3, show i1.val + (0 + 1 + 1 + 1) = e.val by omega, dE, qe, ← he1v]; simp [lit_yes]
      · have qe' : ¬ atU cs e.val = atU cs i.val := fun h => qe (by rw [← atU_val, h, atU_val])
        refine ⟨.Err ⟨.Syntax, e⟩, by simp [qe', xml.fail], by simp, ?_⟩
        intro q yn rest split hq' hyn
        exfalso
        have cq : charAt cs i.val = q := first_char (rest := yn ++ q :: rest) (by rw [split]; simp)
        subst cq
        have d1 := after yn rest split
        rcases hyn with rfl | rfl
        · apply qe
          have := charAt_after (cs := cs) (i := i1.val) (w := lit "yes") (rest := charAt cs i.val :: rest) d1
          rw [hev]; simpa [lit_yes] using this
        · rw [d1, lit_yes, lit_no] at y; obtain ⟨t, ht⟩ := y; simp at ht
    · by_cases n : lit "no" <+: (word cs).drop i1.val
      · rw [if_neg y, if_pos n] at hev
        have ne : ¬ e = i1 := fun h => by have := congrArg UScalar.val h; omega
        rw [if_neg ne]
        obtain ⟨d2, fit⟩ := prefix_split n (by rw [lit_no]; simp)
        simp only [lit_no, List.length_cons, List.length_nil] at d2 fit
        by_cases qe : charAt cs e.val = charAt cs i.val
        · have qe' : atU cs e.val = atU cs i.val := UScalar.eq_of_val_eq (by rw [atU_val, atU_val, qe])
          obtain ⟨insideE, dE⟩ := drop_nonzero (by rw [qe]; exact quote_ne_zero hq)
          obtain ⟨e1, he1, he1v⟩ := next_spec insideE
          refine ⟨.Ok e1, by simp [qe', he1], ?_, fun _ _ _ _ _ _ => ⟨e1, rfl⟩⟩
          intro j eq; simp at eq; subst eq
          refine ⟨charAt cs i.val, lit "no", ?_, hq, Or.inr rfl, by rw [he1v, hev, hi1v]; simp [lit_no]⟩
          rw [hd, ← hi1v, d2, show i1.val + (0 + 1 + 1) = e.val by omega, dE, qe, ← he1v]; simp [lit_no]
        · have qe' : ¬ atU cs e.val = atU cs i.val := fun h => qe (by rw [← atU_val, h, atU_val])
          refine ⟨.Err ⟨.Syntax, e⟩, by simp [qe', xml.fail], by simp, ?_⟩
          intro q yn rest split hq' hyn
          exfalso
          have cq : charAt cs i.val = q := first_char (rest := yn ++ q :: rest) (by rw [split]; simp)
          subst cq
          have d1 := after yn rest split
          rcases hyn with rfl | rfl
          · exact y (by rw [d1]; exact ⟨_, rfl⟩)
          · apply qe
            have := charAt_after (cs := cs) (i := i1.val) (w := lit "no") (rest := charAt cs i.val :: rest) d1
            rw [hev]; simpa [lit_no] using this
      · rw [if_neg y, if_neg n] at hev
        have eq1 : e = i1 := UScalar.eq_of_val_eq hev
        rw [if_pos eq1]
        refine ⟨.Err ⟨.Syntax, i⟩, by simp [xml.fail], by simp, ?_⟩
        intro q yn rest split hq' hyn
        exfalso
        have cq : charAt cs i.val = q := first_char (rest := yn ++ q :: rest) (by rw [split]; simp)
        subst cq
        have d1 := after yn rest split
        rcases hyn with rfl | rfl
        · exact y (by rw [d1]; exact ⟨_, rfl⟩)
        · exact n (by rw [d1]; exact ⟨_, rfl⟩)
  · refine ⟨.Err ⟨.Syntax, i⟩, by simp [hq, xml.fail], by simp, ?_⟩
    intro q yn rest split hq' _
    exact absurd (by rw [first_char (c := q) (rest := yn ++ q :: rest) (by rw [split]; simp)]; exact hq') hq

/-! ## The optional parts of the XML declaration -/

theorem keyword_follows_eq (cs : alloc.vec.Vec U32) (i j : Usize) (kw : Slice U8) :
    xml.keyword_follows cs i j kw = .ok (decide (i.val < j.val ∧ bytes kw <+: (word cs).drop j.val)) := by
  simp [xml.keyword_follows, starts_eq, UScalar.lt_equiv]

theorem quoted_unique {a b x y : Word} {q : Nat} (ha : ∀ c ∈ a, c ≠ q) (hb : ∀ c ∈ b, c ≠ q)
    (h : a ++ q :: x = b ++ q :: y) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons c b' => simp at h; exact absurd h.1.symm (hb c (by simp))
  | cons c a' ih =>
    cases b with
    | nil => simp at h; exact absurd h.1 (ha c (by simp))
    | cons d b' =>
      simp at h
      obtain ⟨rfl, h2⟩ := h
      rw [ih (fun c' hc' => ha c' (by simp [hc'])) (fun c' hc' => hb c' (by simp [hc'])) h2]

theorem encName_not_quote {ename : Word} {q : Nat} (h : EncName ename) (hq : Quote q) : ∀ c ∈ ename, c ≠ q := by
  obtain ⟨c0, r0, rfl, h0, hr⟩ := h
  intro c hc e; subst e
  simp only [List.mem_cons] at hc
  rcases hc with rfl | m
  · rcases hq with rfl | rfl <;> simp at h0
  · have := hr _ m; rcases hq with rfl | rfl <;> simp [IsDigit] at this

/-- Reading `S keyword` after `i`: the spaces are the maximal run. -/
theorem spaces_reading {cs : alloc.vec.Vec U32} {i : Nat} {sp : Word}
    (hr0 : run IsSpace ((word cs).drop i) = sp) {kw : Word} (hk : ∀ c t, kw = c :: t → ¬ IsSpace c)
    (hkne : kw ≠ []) :
    ∀ s t, (word cs).drop i = s ++ (kw ++ t) → OptS s → s = sp := by
  intro s t e hs
  rw [← hr0, e]
  obtain ⟨c, t', rfl⟩ := List.exists_cons_of_ne_nil hkne
  exact (run_unique hs (fun c' m e' => by simp at e'; rw [← e'.1]; exact hk c t' rfl)).symm

theorem encoding_part_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.encoding_part cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ e, (word cs).drop i.val = e ++ (word cs).drop j.val ∧ (e = [] ∨ EncodingDecl e) ∧
        j.val = i.val + e.length) ∧
      (∀ e rest, (word cs).drop i.val = e ++ rest → EncodingDecl e → ∃ j, r = .Ok j ∧ j.val = i.val + e.length) ∧
      ((¬ ∃ s t, (word cs).drop i.val = s ++ lit "encoding" ++ t ∧ S s) → r = .Ok i) := by
  unfold xml.encoding_part
  obtain ⟨j, hj, hjv⟩ := skip_spaces_eq cs i
  have split0 := drop_run IsSpace cs i.val
  rw [← hjv] at split0
  have all0 : ∀ c ∈ run IsSpace ((word cs).drop i.val), IsSpace c := run_all
  generalize hr0 : run IsSpace ((word cs).drop i.val) = sp at split0 hjv all0
  have kwHead : ∀ c t, lit "encoding" = c :: t → ¬ IsSpace c := by
    rw [lit_encoding]; intro c t e; simp at e; rw [e.1]; simp [IsSpace]
  have reads := spaces_reading hr0 kwHead (by rw [lit_encoding]; simp)
  simp only [hj, bind_ok, lift, keyword_follows_eq, bytes_make, map_encoding, decide_eq_true_eq]
  by_cases kw : i.val < j.val ∧ lit "encoding" <+: (word cs).drop j.val
  · rw [if_pos kw]
    obtain ⟨dk, fitk⟩ := prefix_split kw.2 (by rw [lit_encoding]; simp)
    simp only [lit_encoding, List.length_cons, List.length_nil] at dk fitk
    obtain ⟨k, hk, hkv⟩ := skip_spec (cs := cs) (i := j) (c := 8#usize) (by simp; omega)
    have kv : k.val = j.val + 8 := by simpa using hkv
    have spne : sp ≠ [] := by intro e; rw [e] at hjv; simp at hjv; omega
    have notNone : ∃ s t, (word cs).drop i.val = s ++ lit "encoding" ++ t ∧ S s :=
      ⟨sp, (word cs).drop k.val, by rw [split0, dk, kv, lit_encoding]; simp, spne, all0⟩
    obtain ⟨r1, h1, s1, c1⟩ := eq_spec cs k
    -- what a complete reading gives from `k`
    have fromK : ∀ e rest, (word cs).drop i.val = e ++ rest → EncodingDecl e →
        ∃ e' q ename, (word cs).drop k.val = e' ++ q :: ename ++ q :: rest ∧ Eq e' ∧ Quote q ∧ EncName ename ∧
          Utf8Name ename ∧ e.length = sp.length + 8 + e'.length + ename.length + 2 := by
      intro e rest split he
      obtain ⟨s, e', q, ename, rfl, hs, he', hq, hen, hu⟩ := he
      have ss : s = sp := reads s (e' ++ q :: ename ++ [q] ++ rest) (by rw [split]; simp) hs.2
      subst ss
      refine ⟨e', q, ename, ?_, he', hq, hen, hu, by simp [lit_encoding]; omega⟩
      have := drop_after (cs := cs) (i := i.val) (w := s ++ lit "encoding")
        (rest := e' ++ q :: ename ++ q :: rest) (by rw [split]; simp)
      rw [kv, hjv]; simpa [lit_encoding, Nat.add_assoc] using this
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [hk, h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_,
        fun h => absurd notNone h⟩
      intro e rest split he
      obtain ⟨e', q, ename, dk', he', hq, _, _, _⟩ := fromK e rest split he
      obtain ⟨j', hj', _⟩ := c1 e' (q :: ename ++ q :: rest) (by rw [dk']; simp) he'
        (fun c m em => by simp at em; rw [← em.1]; exact quote_not_space hq)
      cases hj'
    | Ok k2 =>
      obtain ⟨ew, ksplit, hk2, hew, _⟩ := s1 k2 rfl
      obtain ⟨r2, h2, s2, c2⟩ := encoding_value_spec cs k2
      refine ⟨r2, by simp [hk, h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_, ?_,
        fun h => absurd notNone h⟩
      · intro j2 e2
        obtain ⟨q, ename, vsplit, hq, hen, hu, hj2⟩ := s2 j2 e2
        refine ⟨sp ++ lit "encoding" ++ ew ++ q :: ename ++ [q], ?_,
          Or.inr ⟨sp, ew, q, ename, rfl, ⟨spne, all0⟩, hew, hq, hen, hu⟩, ?_⟩
        · rw [split0, dk, ← kv, ksplit, vsplit, lit_encoding]; simp
        · rw [hj2, hk2, kv, hjv]; simp [lit_encoding]; omega
      · intro e rest split he
        obtain ⟨e', q, ename, dk', he', hq, hen, hu, elen⟩ := fromK e rest split he
        obtain ⟨j', hj', hj'v⟩ := c1 e' (q :: ename ++ q :: rest) (by rw [dk']; simp) he'
          (fun c m em => by simp at em; rw [← em.1]; exact quote_not_space hq)
        cases hj'
        have dk2 : (word cs).drop k2.val = q :: ename ++ q :: rest := by
          rw [hj'v]; have := drop_after (cs := cs) (i := k.val) (w := e') (rest := q :: ename ++ q :: rest)
            (by rw [dk']; simp); simpa using this
        obtain ⟨j2, hj2⟩ := c2 q ename rest dk2 hq hen hu
        refine ⟨j2, hj2, ?_⟩
        obtain ⟨q', ename', vsplit, hq', hen', _, hj2v⟩ := s2 j2 hj2
        rw [dk2] at vsplit
        simp only [List.cons_append, List.cons.injEq] at vsplit
        obtain ⟨rfl, vsplit⟩ := vsplit
        have hl : ename.length = ename'.length := by
          rw [quoted_unique (encName_not_quote hen hq) (encName_not_quote hen' hq) vsplit]
        rw [hj2v, hj'v, kv, hjv]; omega
  · rw [if_neg kw]
    refine ⟨.Ok i, rfl, ?_, ?_, fun _ => rfl⟩
    · intro j' e; simp at e; subst e; exact ⟨[], by simp, Or.inl rfl, by simp⟩
    · intro e rest split he
      exfalso; apply kw
      obtain ⟨s, e', q, ename, rfl, hs, _, _, _, _⟩ := he
      have ss : s = sp := reads s (e' ++ q :: ename ++ [q] ++ rest) (by rw [split]; simp) hs.2
      subst ss
      refine ⟨by rw [hjv]; have := List.length_pos_of_ne_nil hs.1; omega, ?_⟩
      have := drop_after (cs := cs) (i := i.val) (w := s) (rest := lit "encoding" ++ (e' ++ q :: ename ++ q :: rest))
        (by rw [split]; simp)
      rw [hjv, this]; exact ⟨_, rfl⟩

theorem yn_not_quote {yn : Word} {q : Nat} (h : yn = lit "yes" ∨ yn = lit "no") (hq : Quote q) :
    ∀ c ∈ yn, c ≠ q := by
  intro c hc e; subst e
  rcases h with rfl | rfl <;> rcases hq with h | h <;> simp [lit_yes, lit_no] at hc <;> omega

theorem standalone_part_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.standalone_part cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ e, (word cs).drop i.val = e ++ (word cs).drop j.val ∧ (e = [] ∨ SDDecl e) ∧
        j.val = i.val + e.length) ∧
      (∀ e rest, (word cs).drop i.val = e ++ rest → SDDecl e → ∃ j, r = .Ok j ∧ j.val = i.val + e.length) ∧
      ((¬ ∃ s t, (word cs).drop i.val = s ++ lit "standalone" ++ t ∧ S s) → r = .Ok i) := by
  unfold xml.standalone_part
  obtain ⟨j, hj, hjv⟩ := skip_spaces_eq cs i
  have split0 := drop_run IsSpace cs i.val
  rw [← hjv] at split0
  have all0 : ∀ c ∈ run IsSpace ((word cs).drop i.val), IsSpace c := run_all
  generalize hr0 : run IsSpace ((word cs).drop i.val) = sp at split0 hjv all0
  have kwHead : ∀ c t, lit "standalone" = c :: t → ¬ IsSpace c := by
    rw [lit_standalone]; intro c t e; simp at e; rw [e.1]; simp [IsSpace]
  have reads := spaces_reading hr0 kwHead (by rw [lit_standalone]; simp)
  simp only [hj, bind_ok, lift, keyword_follows_eq, bytes_make, map_standalone, decide_eq_true_eq]
  by_cases kw : i.val < j.val ∧ lit "standalone" <+: (word cs).drop j.val
  · rw [if_pos kw]
    obtain ⟨dk, fitk⟩ := prefix_split kw.2 (by rw [lit_standalone]; simp)
    simp only [lit_standalone, List.length_cons, List.length_nil] at dk fitk
    obtain ⟨k, hk, hkv⟩ := skip_spec (cs := cs) (i := j) (c := 10#usize) (by simp; omega)
    have kv : k.val = j.val + 10 := by simpa using hkv
    have spne : sp ≠ [] := by intro e; rw [e] at hjv; simp at hjv; omega
    have notNone : ∃ s t, (word cs).drop i.val = s ++ lit "standalone" ++ t ∧ S s :=
      ⟨sp, (word cs).drop k.val, by rw [split0, dk, kv, lit_standalone]; simp, spne, all0⟩
    obtain ⟨r1, h1, s1, c1⟩ := eq_spec cs k
    -- what a complete reading gives from `k`
    have fromK : ∀ e rest, (word cs).drop i.val = e ++ rest → SDDecl e →
        ∃ e' q yn, (word cs).drop k.val = e' ++ q :: yn ++ q :: rest ∧ Eq e' ∧ Quote q ∧
          (yn = lit "yes" ∨ yn = lit "no") ∧ e.length = sp.length + 10 + e'.length + yn.length + 2 := by
      intro e rest split he
      obtain ⟨s, e', q, yn, rfl, hs, he', hq, hen⟩ := he
      have ss : s = sp := reads s (e' ++ q :: yn ++ [q] ++ rest) (by rw [split]; simp) hs.2
      subst ss
      refine ⟨e', q, yn, ?_, he', hq, hen, by simp [lit_standalone]; omega⟩
      have := drop_after (cs := cs) (i := i.val) (w := s ++ lit "standalone")
        (rest := e' ++ q :: yn ++ q :: rest) (by rw [split]; simp)
      rw [kv, hjv]; simpa [lit_standalone, Nat.add_assoc] using this
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [hk, h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_,
        fun h => absurd notNone h⟩
      intro e rest split he
      obtain ⟨e', q, yn, dk', he', hq, _, _⟩ := fromK e rest split he
      obtain ⟨j', hj', _⟩ := c1 e' (q :: yn ++ q :: rest) (by rw [dk']; simp) he'
        (fun c m em => by simp at em; rw [← em.1]; exact quote_not_space hq)
      cases hj'
    | Ok k2 =>
      obtain ⟨ew, ksplit, hk2, hew, _⟩ := s1 k2 rfl
      obtain ⟨r2, h2, s2, c2⟩ := standalone_value_spec cs k2
      refine ⟨r2, by simp [hk, h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_, ?_,
        fun h => absurd notNone h⟩
      · intro j2 e2
        obtain ⟨q, yn, vsplit, hq, hen, hj2⟩ := s2 j2 e2
        refine ⟨sp ++ lit "standalone" ++ ew ++ q :: yn ++ [q], ?_,
          Or.inr ⟨sp, ew, q, yn, rfl, ⟨spne, all0⟩, hew, hq, hen⟩, ?_⟩
        · rw [split0, dk, ← kv, ksplit, vsplit, lit_standalone]; simp
        · rw [hj2, hk2, kv, hjv]; simp [lit_standalone]; omega
      · intro e rest split he
        obtain ⟨e', q, yn, dk', he', hq, hen, elen⟩ := fromK e rest split he
        obtain ⟨j', hj', hj'v⟩ := c1 e' (q :: yn ++ q :: rest) (by rw [dk']; simp) he'
          (fun c m em => by simp at em; rw [← em.1]; exact quote_not_space hq)
        cases hj'
        have dk2 : (word cs).drop k2.val = q :: yn ++ q :: rest := by
          rw [hj'v]; have := drop_after (cs := cs) (i := k.val) (w := e') (rest := q :: yn ++ q :: rest)
            (by rw [dk']; simp); simpa using this
        obtain ⟨j2, hj2⟩ := c2 q yn rest dk2 hq hen
        refine ⟨j2, hj2, ?_⟩
        obtain ⟨q', yn', vsplit, hq', hen', hj2v⟩ := s2 j2 hj2
        rw [dk2] at vsplit
        simp only [List.cons_append, List.cons.injEq] at vsplit
        obtain ⟨rfl, vsplit⟩ := vsplit
        have hl : yn.length = yn'.length := by
          rw [quoted_unique (yn_not_quote hen hq) (yn_not_quote hen' hq) vsplit]
        rw [hj2v, hj'v, kv, hjv]; omega
  · rw [if_neg kw]
    refine ⟨.Ok i, rfl, ?_, ?_, fun _ => rfl⟩
    · intro j' e; simp at e; subst e; exact ⟨[], by simp, Or.inl rfl, by simp⟩
    · intro e rest split he
      exfalso; apply kw
      obtain ⟨s, e', q, yn, rfl, hs, _, _, _⟩ := he
      have ss : s = sp := reads s (e' ++ q :: yn ++ [q] ++ rest) (by rw [split]; simp) hs.2
      subst ss
      refine ⟨by rw [hjv]; have := List.length_pos_of_ne_nil hs.1; omega, ?_⟩
      have := drop_after (cs := cs) (i := i.val) (w := s) (rest := lit "standalone" ++ (e' ++ q :: yn ++ q :: rest))
        (by rw [split]; simp)
      rw [hjv, this]; exact ⟨_, rfl⟩


/-! ## XMLDecl -/

theorem no_keyword {X a y kw : Word} {c : Nat} (hX : X = a ++ c :: y) (ha : OptS a) (hc : ¬ IsSpace c)
    (hk : ∀ k0 kw', kw = k0 :: kw' → k0 ≠ c ∧ ¬ IsSpace k0) (hne : kw ≠ []) :
    ¬ ∃ s t, X = s ++ kw ++ t ∧ S s := by
  rintro ⟨s, t, e, hs⟩
  obtain ⟨k0, kw', rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨hne0, hns⟩ := hk k0 kw' rfl
  rw [hX] at e
  have := keyword_after_spaces (x := y) (y := kw' ++ t) ha hc hs.2 hns (by rw [e]; simp)
  exact hne0 this.2.symm

theorem head_not_space {q : Nat} {x : Word} (hq : ¬ IsSpace q) : ∀ c m, (q :: x) = c :: m → ¬ IsSpace c := by
  intro c m e; simp at e; rw [← e.1]; exact hq

theorem declaration_start_eq (cs : alloc.vec.Vec U32) :
    xml.declaration_start cs = .ok (decide (lit "<?xml" <+: word cs ∧ IsSpace (charAt cs 5))) := by
  unfold xml.declaration_start
  have z0 : (0#usize : Usize).val = 0 := rfl
  have z5 : (5#usize : Usize).val = 5 := rfl
  simp [lift, starts_eq, bytes_make, map_xmlDecl, at_eq, space_eq, atU_val, z0, z5, lit_xmlDecl]

theorem versionNum_not_quote {num : Word} {q : Nat} (h : VersionNum num) (hq : Quote q) : ∀ c ∈ num, c ≠ q := by
  obtain ⟨ds, rfl, _, all⟩ := h
  intro c hc e; subst e
  simp only [List.mem_append] at hc
  rcases hc with m | m
  · rw [lit_one_dot] at m; rcases hq with h | h <;> simp at m <;> omega
  · have := all _ m; rcases hq with h | h <;> simp [IsDigit] at this <;> omega

theorem declaration_body_spec (cs : alloc.vec.Vec U32) (start : lit "<?xml" <+: word cs)
    (sp5 : IsSpace (charAt cs 5)) :
    ∃ r, xml.declaration_body cs = .ok r ∧
      (∀ j, r = .Ok j → ∃ d, word cs = d ++ (word cs).drop j.val ∧ XMLDecl d ∧ j.val = d.length) ∧
      (∀ d rest, word cs = d ++ rest → XMLDecl d → ∃ j, r = .Ok j ∧ j.val = d.length) := by
  have z5 : (5#usize : Usize).val = 5 := rfl
  obtain ⟨t5, ht5⟩ := start
  have d5 : (word cs).drop 5 = t5 := by rw [← ht5, lit_xmlDecl]; rfl
  have w5 : word cs = lit "<?xml" ++ (word cs).drop 5 := by rw [d5, ht5]
  unfold xml.declaration_body
  obtain ⟨i, hi, hiv⟩ := skip_spaces_eq cs 5#usize
  rw [z5] at hiv
  have split0 := drop_run IsSpace cs 5
  rw [← hiv] at split0
  have all0 : ∀ c ∈ run IsSpace ((word cs).drop 5), IsSpace c := run_all
  have spne : run IsSpace ((word cs).drop 5) ≠ [] := by
    have := (run_step cs 5 sp5 not_space_zero).2
    intro e; rw [e] at this; simp at this
  generalize hr0 : run IsSpace ((word cs).drop 5) = sp at split0 hiv all0 spne
  have vHead : ∀ c t, lit "version" = c :: t → ¬ IsSpace c := by
    rw [lit_version]; intro c t e; simp at e; rw [e.1]; simp [IsSpace]
  have reads := spaces_reading hr0 vHead (by rw [lit_version]; simp)
  have qHead : ∀ q, Quote q → ∀ c m, (q :: m : Word) = c :: m → ¬ IsSpace c := by
    intro q hq c m e; simp at e; rw [← e]; exact quote_not_space hq
  -- what every XML declaration at the start gives
  have parts : ∀ d rest, word cs = d ++ rest → XMLDecl d → ∃ e1 q num e sd s,
      (word cs).drop i.val = lit "version" ++ e1 ++ q :: num ++ q :: (e ++ sd ++ s ++ lit "?>" ++ rest) ∧
      Eq e1 ∧ Quote q ∧ VersionNum num ∧ (e = [] ∨ EncodingDecl e) ∧ (sd = [] ∨ SDDecl sd) ∧ OptS s ∧
      d.length = i.val + 7 + e1.length + num.length + 2 + e.length + sd.length + s.length + 2 := by
    intro d rest split hd
    obtain ⟨v, e, sd, s, rfl, ⟨s1, e1, q, num, rfl, hs1, he1, hq, hnum⟩, he, hsd, hs⟩ := hd
    have d5' : (word cs).drop 5 = s1 ++ (lit "version" ++ (e1 ++ q :: num ++ q :: (e ++ sd ++ s ++ lit "?>" ++
        rest))) := by
      have := drop_after (cs := cs) (i := 0) (w := lit "<?xml")
        (rest := s1 ++ (lit "version" ++ (e1 ++ q :: num ++ q :: (e ++ sd ++ s ++ lit "?>" ++ rest))))
        (by simp only [List.drop_zero]; rw [split]; simp)
      simpa [lit_xmlDecl] using this
    have ss : s1 = sp := reads s1 _ d5' hs1.2
    subst ss
    refine ⟨e1, q, num, e, sd, s, ?_, he1, hq, hnum, he, hsd, hs, ?_⟩
    · rw [hiv]; have := drop_after (cs := cs) (i := 5) (w := s1) (rest := lit "version" ++ (e1 ++ q :: num ++ q ::
        (e ++ sd ++ s ++ lit "?>" ++ rest))) d5'
      simpa using this
    · simp [lit_xmlDecl, lit_version, lit_pi_end, hiv]; omega
  simp only [hi, bind_ok, lift, starts_eq, bytes_make, map_version, decide_eq_true_eq]
  by_cases hv : lit "version" <+: (word cs).drop i.val
  · rw [if_pos hv]
    obtain ⟨dv, fitv⟩ := prefix_split hv (by rw [lit_version]; simp)
    simp only [lit_version, List.length_cons, List.length_nil] at dv fitv
    obtain ⟨i7, hi7, hi7v⟩ := skip_spec (cs := cs) (i := i) (c := 7#usize) (by simp; omega)
    have i7v : i7.val = i.val + 7 := by simpa using hi7v
    -- the reading from `i7` of a declaration
    have at7 : ∀ d rest, word cs = d ++ rest → XMLDecl d → ∃ e1 q num e sd s,
        (word cs).drop i7.val = e1 ++ q :: num ++ q :: (e ++ sd ++ s ++ lit "?>" ++ rest) ∧
        Eq e1 ∧ Quote q ∧ VersionNum num ∧ (e = [] ∨ EncodingDecl e) ∧ (sd = [] ∨ SDDecl sd) ∧ OptS s ∧
        d.length = i7.val + e1.length + num.length + 2 + e.length + sd.length + s.length + 2 := by
      intro d rest split hd
      obtain ⟨e1, q, num, e, sd, s, dpart, he1, hq, hnum, he, hsd, hs, hlen⟩ := parts d rest split hd
      refine ⟨e1, q, num, e, sd, s, ?_, he1, hq, hnum, he, hsd, hs, by omega⟩
      have := drop_after (cs := cs) (i := i.val) (w := lit "version")
        (rest := e1 ++ q :: num ++ q :: (e ++ sd ++ s ++ lit "?>" ++ rest)) (by rw [dpart]; simp)
      rw [i7v]; simpa [lit_version] using this
    obtain ⟨r1, h1, s1, c1⟩ := eq_spec cs i7
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [hi7, h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
      intro d rest split hd
      obtain ⟨e1, q, num, e, sd, s, d7, he1, hq, _, _, _, _, _⟩ := at7 d rest split hd
      obtain ⟨_, hj, _⟩ := c1 e1 (q :: num ++ q :: (e ++ sd ++ s ++ lit "?>" ++ rest)) (by rw [d7]; simp) he1
        (head_not_space (quote_not_space hq))
      cases hj
    | Ok k1 =>
      obtain ⟨e1w, sp1, hk1, he1w, _⟩ := s1 k1 rfl
      -- the reading from `k1`
      have at1 : ∀ d rest, word cs = d ++ rest → XMLDecl d → ∃ q num e sd s,
          (word cs).drop k1.val = q :: num ++ q :: (e ++ sd ++ s ++ lit "?>" ++ rest) ∧
          Quote q ∧ VersionNum num ∧ (e = [] ∨ EncodingDecl e) ∧ (sd = [] ∨ SDDecl sd) ∧ OptS s ∧
          d.length = k1.val + num.length + 2 + e.length + sd.length + s.length + 2 := by
        intro d rest split hd
        obtain ⟨e1, q, num, e, sd, s, d7, he1, hq, hnum, he, hsd, hs, hlen⟩ := at7 d rest split hd
        obtain ⟨_, hj, hjv⟩ := c1 e1 (q :: num ++ q :: (e ++ sd ++ s ++ lit "?>" ++ rest)) (by rw [d7]; simp) he1
          (head_not_space (quote_not_space hq))
        simp only [core.result.Result.Ok.injEq] at hj; subst hj
        refine ⟨q, num, e, sd, s, ?_, hq, hnum, he, hsd, hs, by omega⟩
        rw [hjv]; have := drop_after (cs := cs) (i := i7.val) (w := e1)
          (rest := q :: num ++ q :: (e ++ sd ++ s ++ lit "?>" ++ rest)) (by rw [d7]; simp)
        simpa using this
      obtain ⟨r2, h2, s2, c2⟩ := version_value_spec cs k1
      cases r2 with
      | Err err =>
        refine ⟨.Err err, by simp [hi7, h1, h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
          by simp, ?_⟩
        intro d rest split hd
        obtain ⟨q, num, e, sd, s, d1, hq, hnum, _, _, _, _⟩ := at1 d rest split hd
        obtain ⟨_, hj⟩ := c2 q num (e ++ sd ++ s ++ lit "?>" ++ rest) (by rw [d1]) hq hnum
        cases hj
      | Ok k2 =>
        obtain ⟨qv, numv, vsplit, hqv, hnumv, hk2⟩ := s2 k2 rfl
        have at2 : ∀ d rest, word cs = d ++ rest → XMLDecl d → ∃ e sd s,
            (word cs).drop k2.val = e ++ sd ++ s ++ lit "?>" ++ rest ∧
            (e = [] ∨ EncodingDecl e) ∧ (sd = [] ∨ SDDecl sd) ∧ OptS s ∧
            d.length = k2.val + e.length + sd.length + s.length + 2 := by
          intro d rest split hd
          obtain ⟨q, num, e, sd, s, d1, hq, hnum, he, hsd, hs, hlen⟩ := at1 d rest split hd
          rw [d1] at vsplit
          simp only [List.cons_append, List.cons.injEq] at vsplit
          obtain ⟨hqq, vs⟩ := vsplit
          subst hqq
          have nn : num = numv := quoted_unique (versionNum_not_quote hnum hq) (versionNum_not_quote hnumv hq)
            (by simpa using vs)
          subst nn
          refine ⟨e, sd, s, ?_, he, hsd, hs, by omega⟩
          have := drop_after (cs := cs) (i := k1.val) (w := q :: num ++ [q])
            (rest := e ++ sd ++ s ++ lit "?>" ++ rest) (by rw [d1]; simp)
          rw [hk2]; simpa [Nat.add_assoc] using this
        -- the parts that may be missing
        have noEnc : ∀ sd s rest, (word cs).drop k2.val = [] ++ sd ++ s ++ lit "?>" ++ rest → (sd = [] ∨ SDDecl sd) →
            OptS s → ¬ ∃ s' t, (word cs).drop k2.val = s' ++ lit "encoding" ++ t ∧ S s' := by
          intro sd s rest d2 hsd hs
          rcases hsd with rfl | ⟨s1, e1', q', yn, rfl, hs1, _, _, _⟩
          · apply no_keyword (a := s) (c := 63) (y := 62 :: rest) (by rw [d2, lit_pi_end]; simp) hs (by simp [IsSpace])
              (by rw [lit_encoding]; intro k0 kw' e; simp at e; rw [e.1]; simp [IsSpace]) (by rw [lit_encoding]; simp)
          · apply no_keyword (a := s1) (c := 115) (y := (lit "standalone").tail ++ e1' ++ q' :: yn ++ [q'] ++ s ++
                lit "?>" ++ rest) (by rw [d2, lit_standalone]; simp) hs1.2 (by simp [IsSpace])
              (by rw [lit_encoding]; intro k0 kw' e; simp at e; rw [e.1]; simp [IsSpace]) (by rw [lit_encoding]; simp)
        obtain ⟨r3, h3, s3, c3, d3⟩ := encoding_part_spec cs k2
        cases r3 with
        | Err err =>
          refine ⟨.Err err, by simp [hi7, h1, h2, h3, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
            by simp, ?_⟩
          intro d rest split hd
          obtain ⟨e, sd, s, d2, he, hsd, hs, _⟩ := at2 d rest split hd
          rcases he with rfl | he
          · have := d3 (noEnc sd s rest d2 hsd hs); cases this
          · obtain ⟨_, hj, _⟩ := c3 e (sd ++ s ++ lit "?>" ++ rest) (by rw [d2]; simp) he; cases hj
        | Ok k3 =>
          obtain ⟨ew, sp3, hew, hk3⟩ := s3 k3 rfl
          have at3 : ∀ d rest, word cs = d ++ rest → XMLDecl d → ∃ sd s,
              (word cs).drop k3.val = sd ++ s ++ lit "?>" ++ rest ∧ (sd = [] ∨ SDDecl sd) ∧ OptS s ∧
              d.length = k3.val + sd.length + s.length + 2 := by
            intro d rest split hd
            obtain ⟨e, sd, s, d2, he, hsd, hs, hlen⟩ := at2 d rest split hd
            rcases he with rfl | he
            · have := d3 (noEnc sd s rest d2 hsd hs)
              simp only [core.result.Result.Ok.injEq] at this; subst this
              exact ⟨sd, s, by simpa using d2, hsd, hs, by simpa using hlen⟩
            · obtain ⟨j, hj, hjv⟩ := c3 e (sd ++ s ++ lit "?>" ++ rest) (by rw [d2]; simp) he
              simp only [core.result.Result.Ok.injEq] at hj; subst hj
              refine ⟨sd, s, ?_, hsd, hs, by omega⟩
              rw [hjv]; have := drop_after (cs := cs) (i := k2.val) (w := e) (rest := sd ++ s ++ lit "?>" ++ rest)
                (by rw [d2]; simp)
              simpa using this
          have noSd : ∀ s rest, (word cs).drop k3.val = [] ++ s ++ lit "?>" ++ rest → OptS s →
              ¬ ∃ s' t, (word cs).drop k3.val = s' ++ lit "standalone" ++ t ∧ S s' := by
            intro s rest d3' hs
            apply no_keyword (a := s) (c := 63) (y := 62 :: rest) (by rw [d3', lit_pi_end]; simp) hs (by simp [IsSpace])
              (by rw [lit_standalone]; intro k0 kw' e; simp at e; rw [e.1]; simp [IsSpace])
              (by rw [lit_standalone]; simp)
          obtain ⟨r4, h4, s4, c4, d4⟩ := standalone_part_spec cs k3
          cases r4 with
          | Err err =>
            refine ⟨.Err err, by simp [hi7, h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch,
              same_residual], by simp, ?_⟩
            intro d rest split hd
            obtain ⟨sd, s, d3', hsd, hs, _⟩ := at3 d rest split hd
            rcases hsd with rfl | hsd
            · have := d4 (noSd s rest d3' hs); cases this
            · obtain ⟨_, hj, _⟩ := c4 sd (s ++ lit "?>" ++ rest) (by rw [d3']; simp) hsd; cases hj
          | Ok k4 =>
            obtain ⟨sdw, sp4, hsdw, hk4⟩ := s4 k4 rfl
            have at4 : ∀ d rest, word cs = d ++ rest → XMLDecl d → ∃ s,
                (word cs).drop k4.val = s ++ lit "?>" ++ rest ∧ OptS s ∧ d.length = k4.val + s.length + 2 := by
              intro d rest split hd
              obtain ⟨sd, s, d3', hsd, hs, hlen⟩ := at3 d rest split hd
              rcases hsd with rfl | hsd
              · have := d4 (noSd s rest d3' hs)
                simp only [core.result.Result.Ok.injEq] at this; subst this
                exact ⟨s, by simpa using d3', hs, by simpa using hlen⟩
              · obtain ⟨j, hj, hjv⟩ := c4 sd (s ++ lit "?>" ++ rest) (by rw [d3']; simp) hsd
                simp only [core.result.Result.Ok.injEq] at hj; subst hj
                refine ⟨s, ?_, hs, by omega⟩
                rw [hjv]; have := drop_after (cs := cs) (i := k3.val) (w := sd) (rest := s ++ lit "?>" ++ rest)
                  (by rw [d3']; simp)
                simpa using this
            obtain ⟨j, hj, hjv⟩ := skip_spaces_eq cs k4
            have split5 := drop_run IsSpace cs k4.val
            rw [← hjv] at split5
            have all5 : ∀ c ∈ run IsSpace ((word cs).drop k4.val), IsSpace c := run_all
            generalize hr5 : run IsSpace ((word cs).drop k4.val) = s5 at split5 hjv all5
            simp only [hi7, h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hj, pi_end_eq,
              decide_eq_true_eq]
            have sp5' : ∀ d rest, word cs = d ++ rest → XMLDecl d → (word cs).drop j.val = lit "?>" ++ rest ∧
                d.length = j.val + 2 := by
              intro d rest split hd
              obtain ⟨s, d4', hs, hlen⟩ := at4 d rest split hd
              have ss : s = s5 := by
                rw [← hr5, d4', lit_pi_end, List.append_assoc]
                exact (run_unique hs (head_not_space (q := 63) (x := [62] ++ rest) (by simp [IsSpace]))).symm
              subst ss
              refine ⟨?_, by omega⟩
              rw [hjv]; have := drop_after (cs := cs) (i := k4.val) (w := s) (rest := lit "?>" ++ rest)
                (by rw [d4']; simp)
              simpa using this
            by_cases pe : lit "?>" <+: (word cs).drop j.val
            · rw [if_pos pe]
              obtain ⟨dpe, fitpe⟩ := prefix_split pe (by rw [lit_pi_end]; simp)
              simp only [lit_pi_end, List.length_cons, List.length_nil] at dpe fitpe
              obtain ⟨j2, hj2, hj2v⟩ := skip_spec (cs := cs) (i := j) (c := 2#usize) (by simp; omega)
              have j2v : j2.val = j.val + 2 := by simpa using hj2v
              have dpe' : (word cs).drop j.val = lit "?>" ++ (word cs).drop j2.val := by
                rw [j2v, lit_pi_end]; simpa using dpe
              have dv' : (word cs).drop i.val = lit "version" ++ (word cs).drop i7.val := by
                rw [i7v, lit_version]; simpa using dv
              refine ⟨.Ok j2, by simp [hj2], ?_, fun _ _ _ _ => ⟨j2, rfl, ?_⟩⟩
              · intro j' e; simp at e; subst e
                refine ⟨lit "<?xml" ++ (sp ++ lit "version" ++ e1w ++ qv :: numv ++ [qv]) ++ ew ++ sdw ++ s5 ++
                  lit "?>", ?_, ⟨_, ew, sdw, s5, rfl, ⟨sp, e1w, qv, numv, rfl, ⟨spne, all0⟩, he1w, hqv, hnumv⟩, hew,
                  hsdw, all5⟩, ?_⟩
                · conv => lhs; rw [w5, split0, dv', sp1, vsplit, sp3, sp4, split5, dpe']
                  simp
                · simp [lit_xmlDecl, lit_version, lit_pi_end]
                  omega
              · rename_i d rest split hd
                have := (sp5' d rest split hd).2
                simp at hj2v ⊢; omega
            · rw [if_neg pe]
              refine ⟨.Err ⟨.Syntax, j⟩, by simp [xml.fail], by simp, ?_⟩
              intro d rest split hd
              exfalso; apply pe
              rw [(sp5' d rest split hd).1]; exact ⟨rest, rfl⟩
  · rw [if_neg hv]
    refine ⟨.Err ⟨.Syntax, i⟩, by simp [xml.fail], by simp, ?_⟩
    intro d rest split hd
    exfalso; apply hv
    obtain ⟨e1, q, num, e, sd, s, dpart, _⟩ := parts d rest split hd
    rw [dpart]; exact ⟨e1 ++ q :: num ++ q :: (e ++ sd ++ s ++ lit "?>" ++ rest), by simp⟩

theorem xml_declaration_spec (cs : alloc.vec.Vec U32) :
    ∃ r, xml.xml_declaration cs = .ok r ∧
      (∀ j, r = .Ok j → ∃ d, word cs = d ++ (word cs).drop j.val ∧ (d = [] ∨ XMLDecl d) ∧ j.val = d.length) ∧
      (∀ d rest, word cs = d ++ rest → XMLDecl d → ∃ j, r = .Ok j ∧ j.val = d.length) ∧
      (¬ (lit "<?xml" <+: word cs ∧ IsSpace (charAt cs 5)) → r = .Ok 0#usize) := by
  unfold xml.xml_declaration
  rw [declaration_start_eq]
  simp only [bind_ok, decide_eq_true_eq]
  by_cases ds : lit "<?xml" <+: word cs ∧ IsSpace (charAt cs 5)
  · rw [if_pos ds]
    obtain ⟨r, hr, sound, complete⟩ := declaration_body_spec cs ds.1 ds.2
    refine ⟨r, hr, ?_, complete, fun h => absurd ds h⟩
    intro j e; obtain ⟨d, split, hd, hj⟩ := sound j e; exact ⟨d, split, Or.inr hd, hj⟩
  · rw [if_neg ds]
    refine ⟨.Ok 0#usize, rfl, ?_, ?_, fun _ => rfl⟩
    · intro j e; simp at e; subst e; exact ⟨[], by simp, Or.inl rfl, rfl⟩
    · intro d rest split hd
      exfalso; apply ds
      obtain ⟨v, e, sd, s, rfl, ⟨s1, e1, q, num, rfl, hs1, _⟩, _⟩ := hd
      obtain ⟨c, t, ht⟩ := List.exists_cons_of_ne_nil hs1.1
      have hc : IsSpace c := hs1.2 c (by rw [ht]; simp)
      refine ⟨⟨s1 ++ lit "version" ++ e1 ++ q :: num ++ [q] ++ e ++ sd ++ s ++ lit "?>" ++ rest, by rw [split]; simp⟩, ?_⟩
      have := charAt_of_drop (cs := cs) (i := 0) (w := lit "<?xml" ++ [c]) (rest := t ++ lit "version" ++ e1 ++ q ::
        num ++ [q] ++ e ++ sd ++ s ++ lit "?>" ++ rest) (by rw [List.drop_zero, split, ht]; simp) (t := 5)
        (by simp [lit_xmlDecl])
      simp [lit_xmlDecl] at this; rw [this]; exact hc

/-! ## Misc -/

/-- What may follow `Misc*` that it does not read: no white space, comment or
    processing instruction. -/
def MiscEnd (rest : Word) : Prop :=
  (∀ c m, rest = c :: m → ¬ IsSpace c) ∧ ¬ lit "<!--" <+: rest ∧ ¬ lit "<?" <+: rest

theorem map_pi_start : ([60#u8, 63#u8] : List U8).map (·.val) = lit "<?" := by decide

theorem misc_rule_eq (cs : alloc.vec.Vec U32) (i : Usize) :
    xml.misc_rule cs i = .ok (if lit "<!--" <+: (word cs).drop i.val then .Comment
      else if lit "<?" <+: (word cs).drop i.val then .Pi else .Other) := by
  unfold xml.misc_rule
  simp only [lift, bind_ok, starts_eq, bytes_make, map_comment_bytes, map_pi_start, decide_eq_true_eq]
  split_ifs <;> rfl

theorem miscs_spaces {sp m : Word} (hsp : OptS sp) (hm : Miscs m) : Miscs (sp ++ m) := by
  by_cases e : sp = []
  · subst e; simpa using hm
  · exact Miscs.space ⟨e, hsp⟩ hm

theorem misc_sound (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.misc cs i = .ok r ∧
      ∀ j, r = .Ok j → ∃ m, (word cs).drop i.val = m ++ (word cs).drop j.val ∧ Miscs m := by
  rw [xml.misc]
  obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
  have split0 := drop_run IsSpace cs i.val
  rw [← h0v] at split0
  have all0 : ∀ c ∈ run IsSpace ((word cs).drop i.val), IsSpace c := run_all
  generalize hr0 : run IsSpace ((word cs).drop i.val) = sp at split0 h0v all0
  simp only [h0, bind_ok, misc_rule_eq]
  by_cases hc : lit "<!--" <+: (word cs).drop j0.val
  · rw [if_pos hc]
    obtain ⟨r1, h1, sound1, _⟩ := comment_spec cs j0 hc
    cases r1 with
    | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
    | Ok k =>
      obtain ⟨cw, csplit, hcw⟩ := sound1 k rfl
      have cne : cw ≠ [] := by obtain ⟨body, rfl, _⟩ := hcw; simp [lit]
      have progress : cs.val.length - k.val < cs.val.length - i.val := by
        apply drop_lt (w := sp ++ cw) _ (by simp [cne])
        rw [split0, csplit]; simp
      obtain ⟨r2, h2, sound2⟩ := misc_sound cs k
      refine ⟨r2, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_⟩
      intro j e
      obtain ⟨m, msplit, hm⟩ := sound2 j e
      exact ⟨sp ++ (cw ++ m), by rw [split0, csplit, msplit]; simp, miscs_spaces all0 (Miscs.comment hcw hm)⟩
  · rw [if_neg hc]
    by_cases hp : lit "<?" <+: (word cs).drop j0.val
    · rw [if_pos hp]
      obtain ⟨r1, h1, sound1, _⟩ := pi_spec cs j0 hp
      cases r1 with
      | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
      | Ok k =>
        obtain ⟨cw, csplit, hcw⟩ := sound1 k rfl
        have cne : cw ≠ [] := by obtain ⟨t, rest', rfl, _, _⟩ := hcw; simp [lit]
        have progress : cs.val.length - k.val < cs.val.length - i.val := by
          apply drop_lt (w := sp ++ cw) _ (by simp [cne])
          rw [split0, csplit]; simp
        obtain ⟨r2, h2, sound2⟩ := misc_sound cs k
        refine ⟨r2, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_⟩
        intro j e
        obtain ⟨m, msplit, hm⟩ := sound2 j e
        exact ⟨sp ++ (cw ++ m), by rw [split0, csplit, msplit]; simp, miscs_spaces all0 (Miscs.pi hcw hm)⟩
    · rw [if_neg hp]
      refine ⟨.Ok j0, rfl, ?_⟩
      intro j e; simp at e; subst e
      exact ⟨sp, split0, by simpa using miscs_spaces all0 Miscs.nil⟩
termination_by cs.val.length - i.val
decreasing_by all_goals omega

theorem misc_complete {m : Word} (h : Miscs m) :
    ∀ (cs : alloc.vec.Vec U32) (i : Usize) (sp rest : Word), (word cs).drop i.val = sp ++ m ++ rest → OptS sp →
      MiscEnd rest → NoZero cs → ∃ j, xml.misc cs i = .ok (.Ok j) ∧ j.val = i.val + sp.length + m.length := by
  induction h with
  | nil =>
    intro cs i sp rest split hsp hend nz
    rw [xml.misc]
    obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
    have rs : run IsSpace ((word cs).drop i.val) = sp := by
      rw [split]; simpa using run_unique hsp hend.1
    rw [rs] at h0v
    have d0 : (word cs).drop j0.val = rest := by rw [h0v]; simpa using drop_after (rest := rest) (by rw [split]; simp)
    refine ⟨j0, ?_, by simp [h0v]⟩
    simp only [h0, bind_ok, misc_rule_eq, d0, if_neg hend.2.1, if_neg hend.2.2]
  | @space c rest' hc hrest ih =>
    intro cs i sp rest split hsp hend nz
    obtain ⟨j, hj, hjv⟩ := ih cs i (sp ++ c) rest (by rw [split]; simp)
      (fun d hd => by simp at hd; rcases hd with h | h; exact hsp d h; exact hc.2 d h) hend nz
    exact ⟨j, hj, by rw [hjv]; simp; omega⟩
  | @comment c rest' hc hrest ih =>
    intro cs i sp rest split hsp hend nz
    rw [xml.misc]
    obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
    obtain ⟨body, hcb, _⟩ := id hc
    have rs : run IsSpace ((word cs).drop i.val) = sp := by
      rw [split, hcb, lit_comment]; simpa using run_unique hsp (head_not_space (q := 60) (by simp [IsSpace]))
    rw [rs] at h0v
    have d0 : (word cs).drop j0.val = c ++ (rest' ++ rest) := by
      rw [h0v]; simpa using drop_after (rest := c ++ (rest' ++ rest)) (by rw [split]; simp)
    have start : lit "<!--" <+: (word cs).drop j0.val := by
      rw [d0, hcb]; exact ⟨body ++ lit "-->" ++ (rest' ++ rest), by simp⟩
    obtain ⟨r1, h1, _, complete1⟩ := comment_spec cs j0 start
    obtain ⟨k, hk, hkv⟩ := complete1 c (rest' ++ rest) d0 hc (nz_of_drop nz d0)
    subst hk
    obtain ⟨j, hj, hjv⟩ := ih cs k [] rest (by rw [hkv]; simpa using drop_after d0) (by simp [OptS]) hend nz
    refine ⟨j, ?_, by rw [hjv, hkv, h0v]; simp; omega⟩
    simp only [h0, bind_ok, misc_rule_eq, if_pos start, h1, core.result.Result.Insts.CoreOpsTry.branch, hj]
  | @pi c rest' hc hrest ih =>
    intro cs i sp rest split hsp hend nz
    rw [xml.misc]
    obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
    obtain ⟨t, rp, hcp, _, _⟩ := id hc
    have rs : run IsSpace ((word cs).drop i.val) = sp := by
      rw [split, hcp, lit_pi]; simpa using run_unique hsp (head_not_space (q := 60) (by simp [IsSpace]))
    rw [rs] at h0v
    have d0 : (word cs).drop j0.val = c ++ (rest' ++ rest) := by
      rw [h0v]; simpa using drop_after (rest := c ++ (rest' ++ rest)) (by rw [split]; simp)
    have start : lit "<?" <+: (word cs).drop j0.val := by
      rw [d0, hcp]; exact ⟨t ++ rp ++ lit "?>" ++ (rest' ++ rest), by simp⟩
    have notc : ¬ lit "<!--" <+: (word cs).drop j0.val := by
      rw [d0, hcp, lit_pi, lit_comment]; rintro ⟨u, hu⟩; simp at hu
    obtain ⟨r1, h1, _, complete1⟩ := pi_spec cs j0 start
    obtain ⟨k, hk, hkv⟩ := complete1 c (rest' ++ rest) d0 hc (nz_of_drop nz d0)
    subst hk
    obtain ⟨j, hj, hjv⟩ := ih cs k [] rest (by rw [hkv]; simpa using drop_after d0) (by simp [OptS]) hend nz
    refine ⟨j, ?_, by rw [hjv, hkv, h0v]; simp; omega⟩
    simp only [h0, bind_ok, misc_rule_eq, if_neg notc, if_pos start, h1, core.result.Result.Insts.CoreOpsTry.branch, hj]

end Rowl.XmlDecl
