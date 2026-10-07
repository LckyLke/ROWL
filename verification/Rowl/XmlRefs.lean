import Rowl.XmlScan

/-!
# References in the XML reader

Exact results of the reference readers of `xml.rs`: character references,
predefined entities and entity names.
-/

namespace Rowl.XmlRefs
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

theorem lit_amp_hash : lit "&#" = [38, 35] := by decide
theorem lit_amp_hash_x : lit "&#x" = [38, 35, 120] := by decide

theorem not_digit_x : ¬ IsDigit 120 := by simp [IsDigit]
theorem not_digit_semi : ¬ IsDigit 59 := by simp [IsDigit]
theorem not_hex_semi : ¬ HexChar 59 := by simp [HexChar, hexDigit]

theorem xml_char_le {v : Nat} (h : Rowl.Unicode.XmlChar v) : v ≤ 0x10FFFF := by
  unfold Rowl.Unicode.XmlChar at h; omega

theorem xml_char_ne_zero {v : Nat} (h : Rowl.Unicode.XmlChar v) : v ≠ 0 := by
  unfold Rowl.Unicode.XmlChar at h; omega

/-- The characters of a reference read from `i`, past `&#`. -/
theorem char_ref_shapes {cs : alloc.vec.Vec U32} {i i2 : Nat}
    (d2 : (word cs).drop i = [38, 35] ++ (word cs).drop i2) {w : Word} {v : Nat} {rest : Word}
    (split : (word cs).drop i = w ++ rest) (hw : CharRef w v) :
    (∃ ds, w = lit "&#" ++ ds ++ [59] ∧ v = decimalValue ds ∧ ds ≠ [] ∧ (∀ d ∈ ds, IsDigit d) ∧
      (word cs).drop i2 = ds ++ 59 :: rest) ∨
    (∃ ds, w = lit "&#x" ++ ds ++ [59] ∧ v = hexValue ds ∧ ds ≠ [] ∧ (∀ d ∈ ds, HexChar d) ∧
      (word cs).drop i2 = 120 :: (ds ++ 59 :: rest)) := by
  cases hw with
  | @decimal ds ne all =>
    left; refine ⟨ds, rfl, rfl, ne, all, ?_⟩
    rw [d2, lit_amp_hash] at split
    simpa using split
  | @hex ds ne all =>
    right; refine ⟨ds, rfl, rfl, ne, fun d hd => all d hd, ?_⟩
    rw [d2, lit_amp_hash_x] at split
    simpa using split

theorem decimalValue_fold (ds : Word) : decimalValue ds = decFold 0 ds := rfl
theorem hexValue_fold (ds : Word) : hexValue ds = hexFold 0 ds := rfl

/-- Reading the digits and the `;` of a character reference: the run of
    digits read is the one of the grammar. -/
theorem digits_run {cs : alloc.vec.Vec U32} {k : Nat} {p : Nat → Prop} {ds rest : Word}
    (split : (word cs).drop k = ds ++ 59 :: rest) (all : ∀ d ∈ ds, p d) (semi : ¬ p 59) :
    run p ((word cs).drop k) = ds := by
  rw [split]
  exact run_unique all (fun c m e => by simp at e; rw [e.1]; exact semi)

theorem char_reference_spec (cs : alloc.vec.Vec U32) (i : Usize)
    (start : lit "&#" <+: (word cs).drop i.val) :
    ∃ r, xml.char_reference cs i = .ok r ∧
      (∀ c j, r = .Ok (c, j) → ∃ w, (word cs).drop i.val = w ++ (word cs).drop j.val ∧
        j.val = i.val + w.length ∧ CharRef w c.val ∧
        Rowl.Unicode.XmlChar c.val) ∧
      (∀ w v rest, (word cs).drop i.val = w ++ rest → CharRef w v → Rowl.Unicode.XmlChar v →
        ∃ c j, r = .Ok (c, j) ∧ c.val = v ∧ j.val = i.val + w.length) := by
  obtain ⟨s0, len0⟩ := prefix_split start (by simp [lit_amp_hash])
  rw [lit_amp_hash] at len0 s0
  simp at len0
  obtain ⟨i2, hi2, hi2v⟩ := skip_spec (cs := cs) (i := i) (c := 2#usize) (by simp; omega)
  have i2v : i2.val = i.val + 2 := by simpa using hi2v
  have d2 : (word cs).drop i.val = [38, 35] ++ (word cs).drop i2.val := by rw [i2v]; simpa using s0
  unfold xml.char_reference xml.reference_digits
  by_cases x : charAt cs i2.val = 120
  · obtain ⟨inside2, hd2⟩ := drop_nonzero (by rw [x]; decide : charAt cs i2.val ≠ 0)
    obtain ⟨i3, hi3, hi3v⟩ := skip_spec (cs := cs) (i := i) (c := 3#usize) (by simp; omega)
    have i3v : i3.val = i2.val + 1 := by simp at hi3v; omega
    have d3 : (word cs).drop i2.val = 120 :: (word cs).drop i3.val := by rw [i3v, ← x]; exact hd2
    obtain ⟨r1, h1, sound1, complete1⟩ := hexadecimal_spec cs i3 i3 0#u32 i (by simp) (le_refl _)
    have ax : atU cs i2.val = 120#u32 := atU_eq (by simpa using x)
    -- a reference read from `i` is hexadecimal
    have hexOnly : ∀ w v rest, (word cs).drop i.val = w ++ rest → CharRef w v →
        ∃ ds, w = lit "&#x" ++ ds ++ [59] ∧ v = hexValue ds ∧ ds ≠ [] ∧ (∀ d ∈ ds, HexChar d) ∧
          (word cs).drop i3.val = ds ++ 59 :: rest := by
      intro w v rest split hw
      rcases char_ref_shapes d2 split hw with ⟨ds, _, _, ne, all, e⟩ | ⟨ds, ew, ev, ne, all, e⟩
      · exfalso
        cases ds with
        | nil => exact ne rfl
        | cons d tail =>
          have := first_char (cs := cs) (i := i2.val) (c := d) (rest := tail ++ 59 :: rest) (by rw [e]; simp)
          rw [x] at this
          exact not_digit_x (this ▸ all d (by simp))
      · rw [d3] at e
        simp at e
        exact ⟨ds, ew, ev, ne, all, e⟩
    cases r1 with
    | Err e =>
      refine ⟨.Err e, by simp [hi2, at_eq, ax, hi3, h1, core.result.Result.Insts.CoreOpsTry.branch,
        same_residual], by simp, ?_⟩
      intro w v rest split hw hv
      obtain ⟨ds, _, rfl, ne, all, e3⟩ := hexOnly w v rest split hw
      have run3 := digits_run e3 all not_hex_semi
      obtain ⟨val, j, h⟩ := complete1 (Or.inr (by rw [run3]; exact ne))
        (by rw [run3]; have := xml_char_le hv; rw [hexValue_fold] at this; simpa using this)
      cases h
    | Ok pair =>
      obtain ⟨val, j⟩ := pair
      obtain ⟨hj, hval, hne⟩ := sound1 val j rfl
      simp only [show (0#u32 : U32).val = 0 from rfl] at hval
      have dsNe : run HexChar ((word cs).drop i3.val) ≠ [] := by
        rcases hne with h | h
        · exact absurd rfl h
        · exact h
      have jsplit : (word cs).drop i3.val = run HexChar ((word cs).drop i3.val) ++ (word cs).drop j.val := by
        rw [hj]; exact drop_run HexChar cs i3.val
      by_cases semi : charAt cs j.val = 59
      · obtain ⟨insideJ, hdJ⟩ := drop_nonzero (by rw [semi]; decide : charAt cs j.val ≠ 0)
        have aj : atU cs j.val = 59#u32 := atU_eq (by simpa using semi)
        by_cases xc : Rowl.Unicode.XmlChar val.val
        · obtain ⟨j1, hj1, hj1v⟩ := next_spec insideJ
          refine ⟨.Ok (val, j1), ?_, ?_, ?_⟩
          · simp [hi2, at_eq, ax, hi3, h1, core.result.Result.Insts.CoreOpsTry.branch, aj,
              Rowl.Unicode.xml_character_total_correct, xc, hj1]
          · intro c j' e
            simp at e; obtain ⟨rfl, rfl⟩ := e
            refine ⟨lit "&#x" ++ run HexChar ((word cs).drop i3.val) ++ [59], ?_, ?_, ?_, xc⟩
            · have e1 : (word cs).drop i3.val = run HexChar ((word cs).drop i3.val) ++ 59 :: (word cs).drop j1.val := by
                conv => lhs; rw [jsplit]
                rw [hdJ, semi, hj1v]
              generalize run HexChar ((word cs).drop i3.val) = ds at e1 ⊢
              rw [d2, d3, e1, lit_amp_hash_x]; simp
            · rw [hj1v, hj, i3v, i2v, lit_amp_hash_x]; simp; omega
            · rw [hval, ← hexValue_fold]
              exact CharRef.hex dsNe (fun d hd => run_all d hd)
          · intro w v rest split hw hv
            obtain ⟨ds, rfl, rfl, ne, all, e3⟩ := hexOnly w v rest split hw
            have run3 := digits_run e3 all not_hex_semi
            refine ⟨val, j1, rfl, by rw [hval, run3]; rfl, ?_⟩
            rw [hj1v, hj, run3, i3v, i2v, lit_amp_hash_x]; simp; omega
        · refine ⟨.Err ⟨.InvalidCharacterReference, i⟩, by
            simp [hi2, at_eq, ax, hi3, h1, core.result.Result.Insts.CoreOpsTry.branch, aj,
              Rowl.Unicode.xml_character_total_correct, xc, xml.fail], by simp, ?_⟩
          intro w v rest split hw hv
          obtain ⟨ds, rfl, rfl, ne, all, e3⟩ := hexOnly w v rest split hw
          have run3 := digits_run e3 all not_hex_semi
          exfalso; apply xc
          rw [hval, run3, ← hexValue_fold]; exact hv
      · have aj : ¬ (atU cs j.val).val = 59 := by rw [atU_val]; exact semi
        refine ⟨.Err ⟨.Syntax, j⟩, by
          simp [hi2, at_eq, ax, hi3, h1, core.result.Result.Insts.CoreOpsTry.branch, aj, xml.fail],
          by simp, ?_⟩
        intro w v rest split hw hv
        obtain ⟨ds, rfl, rfl, ne, all, e3⟩ := hexOnly w v rest split hw
        have run3 := digits_run e3 all not_hex_semi
        exfalso; apply semi
        have := charAt_after (w := ds) (rest := 59 :: rest) e3
        rw [hj, run3]; simpa using this
  · have ax : ¬ atU cs i2.val = 120#u32 := atU_ne (by simpa using x)
    obtain ⟨r1, h1, sound1, complete1⟩ := decimal_spec cs i2 i2 0#u32 i (by simp) (le_refl _)
    have decOnly : ∀ w v rest, (word cs).drop i.val = w ++ rest → CharRef w v →
        ∃ ds, w = lit "&#" ++ ds ++ [59] ∧ v = decimalValue ds ∧ ds ≠ [] ∧ (∀ d ∈ ds, IsDigit d) ∧
          (word cs).drop i2.val = ds ++ 59 :: rest := by
      intro w v rest split hw
      rcases char_ref_shapes d2 split hw with ⟨ds, ew, ev, ne, all, e⟩ | ⟨ds, _, _, _, _, e⟩
      · exact ⟨ds, ew, ev, ne, all, e⟩
      · exact absurd (first_char e) x
    cases r1 with
    | Err e =>
      refine ⟨.Err e, by simp [hi2, at_eq, ax, h1, core.result.Result.Insts.CoreOpsTry.branch,
        same_residual], by simp, ?_⟩
      intro w v rest split hw hv
      obtain ⟨ds, _, rfl, ne, all, e2⟩ := decOnly w v rest split hw
      have run2 := digits_run e2 all not_digit_semi
      obtain ⟨val, j, h⟩ := complete1 (Or.inr (by rw [run2]; exact ne))
        (by rw [run2]; have := xml_char_le hv; rw [decimalValue_fold] at this; simpa using this)
      cases h
    | Ok pair =>
      obtain ⟨val, j⟩ := pair
      obtain ⟨hj, hval, hne⟩ := sound1 val j rfl
      simp only [show (0#u32 : U32).val = 0 from rfl] at hval
      have dsNe : run IsDigit ((word cs).drop i2.val) ≠ [] := by
        rcases hne with h | h
        · exact absurd rfl h
        · exact h
      have jsplit : (word cs).drop i2.val = run IsDigit ((word cs).drop i2.val) ++ (word cs).drop j.val := by
        rw [hj]; exact drop_run IsDigit cs i2.val
      by_cases semi : charAt cs j.val = 59
      · obtain ⟨insideJ, hdJ⟩ := drop_nonzero (by rw [semi]; decide : charAt cs j.val ≠ 0)
        have aj : atU cs j.val = 59#u32 := atU_eq (by simpa using semi)
        by_cases xc : Rowl.Unicode.XmlChar val.val
        · obtain ⟨j1, hj1, hj1v⟩ := next_spec insideJ
          refine ⟨.Ok (val, j1), ?_, ?_, ?_⟩
          · simp [hi2, at_eq, ax, h1, core.result.Result.Insts.CoreOpsTry.branch, aj,
              Rowl.Unicode.xml_character_total_correct, xc, hj1]
          · intro c j' e
            simp at e; obtain ⟨rfl, rfl⟩ := e
            refine ⟨lit "&#" ++ run IsDigit ((word cs).drop i2.val) ++ [59], ?_, ?_, ?_, xc⟩
            · have e1 : (word cs).drop i2.val = run IsDigit ((word cs).drop i2.val) ++ 59 :: (word cs).drop j1.val := by
                conv => lhs; rw [jsplit]
                rw [hdJ, semi, hj1v]
              generalize run IsDigit ((word cs).drop i2.val) = ds at e1 ⊢
              rw [d2, e1, lit_amp_hash]; simp
            · rw [hj1v, hj, i2v, lit_amp_hash]; simp; omega
            · rw [hval, ← decimalValue_fold]
              exact CharRef.decimal dsNe (fun d hd => run_all d hd)
          · intro w v rest split hw hv
            obtain ⟨ds, rfl, rfl, ne, all, e2⟩ := decOnly w v rest split hw
            have run2 := digits_run e2 all not_digit_semi
            refine ⟨val, j1, rfl, by rw [hval, run2]; rfl, ?_⟩
            rw [hj1v, hj, run2, i2v, lit_amp_hash]; simp; omega
        · refine ⟨.Err ⟨.InvalidCharacterReference, i⟩, by
            simp [hi2, at_eq, ax, h1, core.result.Result.Insts.CoreOpsTry.branch, aj,
              Rowl.Unicode.xml_character_total_correct, xc, xml.fail], by simp, ?_⟩
          intro w v rest split hw hv
          obtain ⟨ds, rfl, rfl, ne, all, e2⟩ := decOnly w v rest split hw
          have run2 := digits_run e2 all not_digit_semi
          exfalso; apply xc
          rw [hval, run2, ← decimalValue_fold]; exact hv
      · have aj : ¬ (atU cs j.val).val = 59 := by rw [atU_val]; exact semi
        refine ⟨.Err ⟨.Syntax, j⟩, by
          simp [hi2, at_eq, ax, h1, core.result.Result.Insts.CoreOpsTry.branch, aj, xml.fail],
          by simp, ?_⟩
        intro w v rest split hw hv
        obtain ⟨ds, rfl, rfl, ne, all, e2⟩ := decOnly w v rest split hw
        have run2 := digits_run e2 all not_digit_semi
        exfalso; apply semi
        have := charAt_after (w := ds) (rest := 59 :: rest) e2
        rw [hj, run2]; simpa using this

/-! ## Predefined entities and entity names -/

theorem bytes_make (n : Usize) (l : List U8) (h : l.length = n.val) :
    bytes (Array.to_slice (Array.make n l h)) = l.map (·.val) := by
  simp [bytes, Array.to_slice, Array.make]

theorem lit_lt : lit "lt" = [108, 116] := by decide
theorem lit_gt : lit "gt" = [103, 116] := by decide
theorem lit_amp : lit "amp" = [97, 109, 112] := by decide
theorem lit_apos : lit "apos" = [97, 112, 111, 115] := by decide
theorem lit_quot : lit "quot" = [113, 117, 111, 116] := by decide

theorem predefined_eq (cs : alloc.vec.Vec U32) (start stop : Usize) {w rest : Word}
    (split : (word cs).drop start.val = w ++ rest) (hs : stop.val = start.val + w.length) :
    ∃ c : U32, xml.predefined cs start stop = .ok c ∧ c.val = (predefinedChar w).getD 0 := by
  unfold xml.predefined
  simp only [lift, bind_ok, span_is_eq cs start stop _ split hs, bytes_make]
  simp only [predefinedChar, lit_lt, lit_gt, lit_amp, lit_apos, lit_quot]
  by_cases a : w = [108, 116]
  · subst a; exact ⟨60#u32, by simp, by simp⟩
  · by_cases b : w = [103, 116]
    · subst b; exact ⟨62#u32, by simp, by simp⟩
    · by_cases c : w = [97, 109, 112]
      · subst c; exact ⟨38#u32, by simp, by simp⟩
      · by_cases d : w = [97, 112, 111, 115]
        · subst d; exact ⟨39#u32, by simp, by simp⟩
        · by_cases e : w = [113, 117, 111, 116]
          · subst e; exact ⟨34#u32, by simp, by simp⟩
          · exact ⟨0#u32, by simp [a, b, c, d, e], by simp [a, b, c, d, e]⟩

theorem entity_name_spec (cs : alloc.vec.Vec U32) (i : Usize) (inside : i.val < cs.val.length) :
    ∃ r, xml.entity_name cs i = .ok r ∧
      (∀ stop j, r = .Ok (stop, j) → stop.val = i.val + 1 + (nameRun cs (i.val + 1)).length ∧
        NCName (nameRun cs (i.val + 1)) ∧ charAt cs stop.val = 59 ∧ j.val = stop.val + 1) ∧
      (NCName (nameRun cs (i.val + 1)) → charAt cs (i.val + 1 + (nameRun cs (i.val + 1)).length) = 59 →
        ∃ stop j, r = .Ok (stop, j)) := by
  unfold xml.entity_name
  obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
  obtain ⟨r1, h1, sound1, complete1⟩ := ncname_spec cs i1
  rw [hi1v] at sound1 complete1
  cases r1 with
  | Err e =>
    refine ⟨.Err e, by simp [hi1, h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
    intro n _
    obtain ⟨stop, h⟩ := complete1 n
    cases h
  | Ok stop =>
    obtain ⟨hstop, ncn⟩ := sound1 stop rfl
    by_cases semi : charAt cs stop.val = 59
    · obtain ⟨insideS, _⟩ := drop_nonzero (by rw [semi]; decide : charAt cs stop.val ≠ 0)
      obtain ⟨j, hj, hjv⟩ := next_spec insideS
      refine ⟨.Ok (stop, j), by simp [hi1, h1, core.result.Result.Insts.CoreOpsTry.branch, at_eq,
        atU_eq (c := 59#u32) (by simpa using semi), hj], ?_, fun _ _ => ⟨stop, j, rfl⟩⟩
      intro stop' j' e
      simp at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨hstop, ncn, semi, hjv⟩
    · refine ⟨.Err ⟨.Syntax, stop⟩, by simp [hi1, h1, core.result.Result.Insts.CoreOpsTry.branch, at_eq,
        atU_ne (c := 59#u32) (by simpa using semi), xml.fail], by simp, ?_⟩
      intro _ h
      rw [← hstop] at h
      exact absurd h semi

/-- What a reference read at a position denotes. -/
def RefMeaning (i : Nat) (w : Word) : xml.Reference → Prop
  | .Character c => (CharRef w c.val ∧ Rowl.Unicode.XmlChar c.val) ∨
      (∃ nm, EntityRef w nm ∧ predefinedChar nm = some c.val)
  | .Entity s e => ∃ nm, EntityRef w nm ∧ predefinedChar nm = none ∧ s.val = i + 1 ∧
      e.val = i + 1 + nm.length

theorem lit_amp_char : lit "&" = [38] := by decide

theorem reference_spec (cs : alloc.vec.Vec U32) (i : Usize) (amp : charAt cs i.val = 38) :
    ∃ r, xml.reference cs i = .ok r ∧
      (∀ ref j, r = .Ok (ref, j) → ∃ w, (word cs).drop i.val = w ++ (word cs).drop j.val ∧
        j.val = i.val + w.length ∧ RefMeaning i.val w ref) ∧
      (∀ w rest, (word cs).drop i.val = w ++ rest →
        ((∃ v, CharRef w v ∧ Rowl.Unicode.XmlChar v) ∨ (∃ nm, EntityRef w nm)) →
        ∃ ref j, r = .Ok (ref, j) ∧ j.val = i.val + w.length) := by
  obtain ⟨inside, hd⟩ := drop_nonzero (by rw [amp]; decide : charAt cs i.val ≠ 0)
  rw [amp] at hd
  obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
  unfold xml.reference
  by_cases hash : charAt cs (i.val + 1) = 35
  · have ah : atU cs i1.val = 35#u32 := atU_eq (by rw [hi1v]; simpa using hash)
    have start : lit "&#" <+: (word cs).drop i.val := by
      obtain ⟨inside1, hd1⟩ := drop_nonzero (by rw [hash]; decide : charAt cs (i.val + 1) ≠ 0)
      rw [hd, hd1, hash, lit_amp_hash]; exact ⟨_, rfl⟩
    obtain ⟨r1, h1, sound1, complete1⟩ := char_reference_spec cs i start
    cases r1 with
    | Err e =>
      refine ⟨.Err e, by simp [hi1, at_eq, ah, h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
        by simp, ?_⟩
      intro w rest split hw
      rcases hw with ⟨v, hv, xc⟩ | ⟨nm, ⟨rfl, hn⟩⟩
      · obtain ⟨c, j, h, _⟩ := complete1 w v rest split hv xc
        cases h
      · exfalso
        obtain ⟨c0, r0, rfl, hc0, _⟩ := hn.1
        have := charAt_of_drop split (t := 1) (by simp)
        simp at this
        rw [hash] at this
        rw [← this] at hc0
        simp [NameStartChar] at hc0
    | Ok pair =>
      obtain ⟨c, j⟩ := pair
      obtain ⟨w, split, jlen, hw, xc⟩ := sound1 c j rfl
      refine ⟨.Ok (.Character c, j), by simp [hi1, at_eq, ah, h1, core.result.Result.Insts.CoreOpsTry.branch],
        ?_, ?_⟩
      · intro ref j' e
        simp at e; obtain ⟨rfl, rfl⟩ := e
        exact ⟨w, split, jlen, Or.inl ⟨hw, xc⟩⟩
      · intro w' rest' split' hw'
        refine ⟨_, j, rfl, ?_⟩
        rcases hw' with ⟨v, hv, xc'⟩ | ⟨nm, ⟨rfl, hn⟩⟩
        · obtain ⟨c', j', h, _, hj'⟩ := complete1 w' v rest' split' hv xc'
          simp at h; obtain ⟨_, rfl⟩ := h
          exact hj'
        · exfalso
          obtain ⟨c0, r0, rfl, hc0, _⟩ := hn.1
          have := charAt_of_drop split' (t := 1) (by simp)
          simp at this
          rw [hash] at this
          rw [← this] at hc0
          simp [NameStartChar] at hc0
  · have ah : ¬ atU cs i1.val = 35#u32 := atU_ne (by rw [hi1v]; simpa using hash)
    obtain ⟨r1, h1, sound1, complete1⟩ := entity_name_spec cs i inside
    -- a reference read from `i` is an entity reference
    have entOnly : ∀ w rest, (word cs).drop i.val = w ++ rest →
        ((∃ v, CharRef w v ∧ Rowl.Unicode.XmlChar v) ∨ (∃ nm, EntityRef w nm)) →
        ∃ nm, EntityRef w nm ∧ nameRun cs (i.val + 1) = nm := by
      intro w rest split hw
      rcases hw with ⟨v, hv, _⟩ | ⟨nm, hn⟩
      · exfalso
        cases hv with
        | decimal _ _ =>
          rw [hd, lit_amp_hash] at split
          simp at split
          exact hash (first_char split)
        | hex _ _ =>
          rw [hd, lit_amp_hash_x] at split
          simp at split
          exact hash (first_char split)
      · refine ⟨nm, hn, ?_⟩
        obtain ⟨rfl, ncn⟩ := hn
        have e : (word cs).drop (i.val + 1) = nm ++ 59 :: rest := by
          rw [hd] at split; simpa using split
        exact nameRun_eq e (name_all ncn.1) (fun c m em => by
          simp at em; rw [em.1]; simp [NameChar, NameStartChar])
    cases r1 with
    | Err e =>
      refine ⟨.Err e, by simp [hi1, at_eq, ah, h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
        by simp, ?_⟩
      intro w rest split hw
      obtain ⟨nm, ⟨rfl, ncn⟩, run⟩ := entOnly w rest split hw
      have e : (word cs).drop (i.val + 1) = nm ++ 59 :: rest := by
        rw [hd] at split; simpa using split
      obtain ⟨stop, j, h⟩ := complete1 (run ▸ ncn) (by
        rw [run]; have := charAt_after e; simpa using this)
      cases h
    | Ok pair =>
      obtain ⟨stop, j⟩ := pair
      obtain ⟨hstop, ncn, semi, hj⟩ := sound1 stop j rfl
      have stopSplit : (word cs).drop (i.val + 1) = nameRun cs (i.val + 1) ++ (word cs).drop stop.val := by
        rw [hstop]; exact nameRun_split cs (i.val + 1)
      obtain ⟨insideS, hdS⟩ := drop_nonzero (by rw [semi]; decide : charAt cs stop.val ≠ 0)
      have wsplit : (word cs).drop i.val = (38 :: nameRun cs (i.val + 1) ++ [59]) ++ (word cs).drop j.val := by
        rw [hd, stopSplit, hdS, semi, hj]; simp
      have nameSplit : (word cs).drop i1.val = nameRun cs (i.val + 1) ++ (word cs).drop stop.val := by
        rw [hi1v]; exact stopSplit
      obtain ⟨c, hc, hcv⟩ := predefined_eq cs i1 stop nameSplit (by rw [hstop, hi1v])
      by_cases pre : predefinedChar (nameRun cs (i.val + 1)) = none
      · have c0 : c = 0#u32 := by apply UScalar.eq_of_val_eq; rw [hcv, pre]; rfl
        refine ⟨.Ok (.Entity i1 stop, j), by simp [hi1, at_eq, ah, h1, core.result.Result.Insts.CoreOpsTry.branch,
          hc, c0], ?_, ?_⟩
        · intro ref j' e
          simp at e; obtain ⟨rfl, rfl⟩ := e
          exact ⟨_, wsplit, by rw [hj, hstop]; simp; omega, nameRun cs (i.val + 1), ⟨rfl, ncn⟩, pre, hi1v, hstop⟩
        · intro w rest split hw
          obtain ⟨nm, ⟨rfl, _⟩, run⟩ := entOnly w rest split hw
          refine ⟨_, j, rfl, ?_⟩
          rw [hj, hstop, run]; simp; omega
      · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp pre
        have cnz : ¬ c = 0#u32 := by
          intro e
          have z : (predefinedChar (nameRun cs (i.val + 1))).getD 0 = 0 := by rw [← hcv, e]; rfl
          rw [hv] at z
          simp at z
          subst z
          unfold predefinedChar at hv
          split_ifs at hv <;> simp at hv
        refine ⟨.Ok (.Character c, j), by simp [hi1, at_eq, ah, h1, core.result.Result.Insts.CoreOpsTry.branch,
          hc, cnz], ?_, ?_⟩
        · intro ref j' e
          simp at e; obtain ⟨rfl, rfl⟩ := e
          refine ⟨_, wsplit, by rw [hj, hstop]; simp; omega, Or.inr ⟨nameRun cs (i.val + 1), ⟨rfl, ncn⟩, ?_⟩⟩
          rw [hcv, hv]; rfl
        · intro w rest split hw
          obtain ⟨nm, ⟨rfl, _⟩, run⟩ := entOnly w rest split hw
          refine ⟨_, j, rfl, ?_⟩
          rw [hj, hstop, run]; simp; omega

end Rowl.XmlRefs
