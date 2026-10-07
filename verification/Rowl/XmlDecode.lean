import Rowl.XmlScan

/-!
# Decoding the characters of a document

`decode` reads strict UTF-8 into code points that are all `Char`s, drops a
leading byte order mark and normalizes line ends (XML 1.0 §2.11, §4.3.3):
the grammar's `Decoded`. `byte_offset`, which maps a character position back
to a byte offset for error reports, never fails.
-/

namespace Rowl.XmlDecode
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar Rowl.Unicode
open Rowl.XmlScan
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-- §2.11 line-end normalization with the state "the previous character was
    a carriage return". -/
def norm : Bool → Word → Word
  | _, [] => []
  | _, 13 :: rest => 10 :: norm true rest
  | true, 10 :: rest => norm false rest
  | _, c :: rest => c :: norm false rest

theorem norm_true_eq {w : Word} (h : ∀ m, w ≠ 10 :: m) : norm true w = norm false w := by
  match w, h with
  | [], _ => rfl
  | 13 :: rest, _ => rfl
  | c :: rest, h =>
    have hc : c ≠ 10 := fun e => h rest (by rw [e])
    by_cases c13 : c = 13
    · subst c13; rfl
    · simp [norm, hc, c13]

theorem norm_false_le : ∀ (n : Nat) (w : Word), w.length ≤ n → norm false w = normalizeLines w
  | 0, w, h => by rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]; rfl
  | _ + 1, [], _ => rfl
  | n + 1, c :: rest, h => by
    by_cases c13 : c = 13
    · subst c13
      cases rest with
      | nil => simp [norm, normalizeLines]
      | cons d r =>
        by_cases d10 : d = 10
        · subst d10
          simp only [norm, normalizeLines]
          rw [norm_false_le n r (by simp at h; omega)]
        · simp only [norm]
          rw [norm_true_eq (by intro m e; simp at e; exact d10 e.1), norm_false_le n (d :: r) (by simp at h ⊢; omega)]
          simp [normalizeLines, d10]
    · have e1 : norm false (c :: rest) = c :: norm false rest := by simp [norm, c13]
      have e2 : normalizeLines (c :: rest) = c :: normalizeLines rest := by simp [normalizeLines, c13]
      rw [e1, e2, norm_false_le n rest (by simp at h; omega)]

theorem norm_false_eq (w : Word) : norm false w = normalizeLines w := norm_false_le w.length w (le_refl _)

theorem order_mark_eq (offset : Usize) (cp : U32) :
    xml.order_mark offset cp = .ok (decide (offset.val = 0 ∧ cp.val = 0xFEFF)) := by
  simp [xml.order_mark, UScalar.eq_equiv]

theorem crlf_eq (cp : U32) (cr : Bool) : xml.crlf cp cr = .ok (decide (cp.val = 10 ∧ cr = true)) := by
  simp [xml.crlf, UScalar.eq_equiv]

/-- One decoded character that is not a leading byte order mark. -/
theorem take_spec (chars : alloc.vec.Vec U32) (cp : U32) (offset : Usize) (cr : Bool)
    (om : ¬ (offset.val = 0 ∧ cp.val = 0xFEFF)) (room : chars.val.length < Usize.max) :
    ∃ chars', xml.take chars cp offset cr = .ok (.Ok chars') ∧ chars'.val.length ≤ chars.val.length + 1 ∧
      ∀ rest, word chars' ++ norm (decide (cp.val = 13)) rest = word chars ++ norm cr (cp.val :: rest) := by
  unfold xml.take
  simp only [order_mark_eq, om, decide_false, bind_ok, Bool.false_eq_true, ite_false]
  by_cases c13 : cp.val = 13
  · have c13' : cp = 13#u32 := UScalar.eq_of_val_eq (by simp [c13])
    rw [if_pos c13', push_char_eq, dif_pos room]
    refine ⟨_, rfl, by simp, fun rest => ?_⟩
    rw [word_push]; simp [c13, norm]
  · have c13' : ¬ cp = 13#u32 := fun e => c13 (by rw [e]; simp)
    rw [if_neg c13', crlf_eq]
    simp only [bind_ok]
    by_cases lf : cp.val = 10 ∧ cr = true
    · rw [if_pos (decide_eq_true lf)]
      obtain ⟨c10, rfl⟩ := lf
      refine ⟨chars, rfl, by omega, fun rest => ?_⟩
      simp [c13, c10, norm]
    · rw [if_neg (by simpa using lf), push_char_eq, dif_pos room]
      refine ⟨_, rfl, by simp, fun rest => ?_⟩
      rw [word_push]
      have : norm cr (cp.val :: rest) = cp.val :: norm false rest := by
        cases cr <;> simp_all [norm]
      rw [this]; simp [c13]

/-! ## Strict UTF-8 text -/

theorem textFrom_inv {bs : List U8} {offset : Nat} {units : List (Nat × Nat)} (h : TextFrom bs offset units) :
    (offset = bs.length ∧ units = []) ∨
    ∃ cp width tail, Prefix bs offset = some (cp, width) ∧ XmlChar cp ∧ 0 < width ∧ offset + width ≤ bs.length ∧
      TextFrom bs (offset + width) tail ∧ units = (cp, offset) :: tail := by
  cases h with
  | endOfInput => exact .inl ⟨rfl, rfl⟩
  | character p x w f t => exact .inr ⟨_, _, _, p, x, w, f, t, rfl⟩

/-- A byte string has at most one decomposition into strict UTF-8 units. -/
theorem textFrom_unique {bs : List U8} {offset : Nat} {u1 u2 : List (Nat × Nat)}
    (h1 : TextFrom bs offset u1) (h2 : TextFrom bs offset u2) : u1 = u2 := by
  induction h1 generalizing u2 with
  | endOfInput =>
    rcases textFrom_inv h2 with ⟨_, rfl⟩ | ⟨cp, w, tail, _, _, wpos, fits, _, _⟩
    · rfl
    · omega
  | character p x w f t ih =>
    rcases textFrom_inv h2 with ⟨e, _⟩ | ⟨cp, w', tail, p', _, _, _, t', rfl⟩
    · omega
    · rw [p] at p'; simp at p'; obtain ⟨rfl, rfl⟩ := p'; rw [ih t']

theorem textFrom_length {bs : List U8} {offset : Nat} {units : List (Nat × Nat)} (h : TextFrom bs offset units) :
    units.length + offset ≤ bs.length := by
  induction h with
  | endOfInput => simp
  | character p x w f t ih => simp; omega

theorem textFrom_chars {bs : List U8} {offset : Nat} {units : List (Nat × Nat)} (h : TextFrom bs offset units) :
    ∀ u ∈ units, XmlChar u.1 := by
  induction h with
  | endOfInput => simp
  | character p x w f t ih =>
    intro u hu
    simp at hu
    rcases hu with rfl | hu
    · exact x
    · exact ih u hu

/-! ## Line ends and the byte order mark -/

theorem norm_length : ∀ (b : Bool) (w : Word), (norm b w).length ≤ w.length
  | _, [] => by simp [norm]
  | b, c :: rest => by
    have ih := norm_length false rest
    have ih' := norm_length true rest
    by_cases c13 : c = 13
    · subst c13; simp [norm]; omega
    · by_cases c10 : c = 10 ∧ b = true
      · obtain ⟨rfl, rfl⟩ := c10; simp [norm]; omega
      · have : norm b (c :: rest) = c :: norm false rest := by
          cases b <;> simp_all [norm]
        rw [this]; simp; omega

theorem norm_mem : ∀ (b : Bool) (w : Word), ∀ c ∈ norm b w, c ∈ w ∨ c = 10
  | _, [] => by simp [norm]
  | b, d :: rest => by
    intro c hc
    have ih := norm_mem false rest
    have ih' := norm_mem true rest
    by_cases d13 : d = 13
    · subst d13
      simp [norm] at hc
      rcases hc with rfl | hc
      · exact .inr rfl
      · rcases ih' c hc with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h
    · by_cases d10 : d = 10 ∧ b = true
      · obtain ⟨rfl, rfl⟩ := d10
        simp [norm] at hc
        rcases ih c hc with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h
      · have : norm b (d :: rest) = d :: norm false rest := by
          cases b <;> simp_all [norm]
        rw [this] at hc
        simp at hc
        rcases hc with rfl | hc
        · exact .inl List.mem_cons_self
        · rcases ih c hc with h | h
          · exact .inl (List.mem_cons_of_mem _ h)
          · exact .inr h

theorem stripOrderMark_suffix (w : Word) : stripOrderMark w <:+ w := by
  unfold stripOrderMark
  split
  · exact List.suffix_cons _ _
  · exact List.suffix_refl _

theorem stripOrderMark_ne (c : Nat) (rest : Word) (h : c ≠ 0xFEFF) : stripOrderMark (c :: rest) = c :: rest := by
  unfold stripOrderMark
  split
  · rename_i e; simp at e; exact absurd e.1 h
  · rfl

theorem decode_from_spec (bytes : alloc.vec.Vec U8) (offset : Usize) (chars : alloc.vec.Vec U32) (cr : Bool)
    (pos : 0 < offset.val) (room : chars.val.length + (bytes.val.length - offset.val) ≤ Usize.max) :
    ∃ r, xml.decode_from bytes offset chars cr = .ok r ∧
      (∀ cs, r = .Ok cs → ∃ units, TextFrom bytes.val offset.val units ∧
        word cs = word chars ++ norm cr (units.map (·.1))) ∧
      (∀ units, TextFrom bytes.val offset.val units → ∃ cs, r = .Ok cs) := by
  rw [xml.decode_from]
  obtain ⟨d, hd, hstep⟩ := decode_next_total_correct bytes offset
  simp only [hd, bind_ok]
  cases d with
  | End =>
    refine ⟨.Ok chars, rfl, ?_, fun _ _ => ⟨chars, rfl⟩⟩
    intro cs e; simp at e; subst e
    refine ⟨[], ?_, by simp [norm]⟩
    have : offset.val = bytes.val.length := hstep
    rw [this]; exact TextFrom.endOfInput
  | Error err =>
    refine ⟨.Err ⟨.MalformedUtf8, offset⟩, by simp [xml.fail], by simp, ?_⟩
    intro units ht
    exfalso
    cases err with
    | InvalidPosition p =>
      exact rejected_excludes_text _ _ _ (Rejected.position (congrArg UScalar.val hstep.1) hstep.2) units ht
    | InvalidUtf8 p =>
      exact rejected_excludes_text _ _ _ (Rejected.utf8 (congrArg UScalar.val hstep.1) hstep.2.1 hstep.2.2) units ht
    | NonXmlCharacter _ _ => exact hstep.elim
  | Scalar cp next =>
    obtain ⟨adv, bound, unit⟩ := hstep
    dsimp only
    rw [xml_character_total_correct]
    simp only [bind_ok]
    have cr13 : decide (cp = 13#u32) = decide (cp.val = 13) := by
      by_cases h : cp.val = 13
      · have : cp = 13#u32 := UScalar.eq_of_val_eq (by simp [h])
        simp [this, h]
      · have : ¬ cp = 13#u32 := fun e => h (by rw [e]; simp)
        simp [this, h]
    by_cases xc : XmlChar cp.val
    · rw [if_pos (decide_eq_true xc)]
      have r1 : chars.val.length < Usize.max := by omega
      obtain ⟨chars', ht, hlen, hnorm⟩ := take_spec chars cp offset cr (fun h => by omega) r1
      obtain ⟨r, hr, sound, complete⟩ := decode_from_spec bytes next chars' (decide (cp.val = 13)) (by omega)
        (by omega)
      refine ⟨r, by simp [ht, core.result.Result.Insts.CoreOpsTry.branch, cr13, hr], ?_, ?_⟩
      · intro cs e
        obtain ⟨units, htu, hw⟩ := sound cs e
        refine ⟨(cp.val, offset.val) :: units, TextFrom.character unit xc (by omega) (by omega)
          (by rw [show offset.val + (next.val - offset.val) = next.val by omega]; exact htu), ?_⟩
        rw [hw]; simp only [List.map_cons]; exact hnorm _
      · intro units htu
        rcases textFrom_inv htu with ⟨e, -⟩ | ⟨cp', w', tail, unit', xc', wpos, fits, htail, rfl⟩
        · omega
        · rw [unit] at unit'; simp at unit'; obtain ⟨rfl, rfl⟩ := unit'
          exact complete _ (by rw [show offset.val + (next.val - offset.val) = next.val by omega] at htail; exact htail)
    · rw [if_neg (by simpa using xc)]
      refine ⟨.Err ⟨.NonXmlCharacter, offset⟩, by simp [xml.fail], by simp, ?_⟩
      intro units htu
      exfalso
      rcases textFrom_inv htu with ⟨e, -⟩ | ⟨cp', w', tail, unit', xc', wpos, fits, htail, rfl⟩
      · omega
      · rw [unit] at unit'; simp at unit'; obtain ⟨rfl, rfl⟩ := unit'
        exact xc xc'
termination_by bytes.val.length - offset.val
decreasing_by omega

/-- The first character: a byte order mark there is dropped. -/
theorem decode_start (bytes : alloc.vec.Vec U8) :
    ∃ r, xml.decode_from bytes 0#usize (alloc.vec.Vec.new U32) false = .ok r ∧
      (∀ cs, r = .Ok cs → ∃ units, TextFrom bytes.val 0 units ∧
        word cs = norm false (stripOrderMark (units.map (·.1)))) ∧
      (∀ units, TextFrom bytes.val 0 units → ∃ cs, r = .Ok cs) := by
  rw [xml.decode_from]
  obtain ⟨d, hd, hstep⟩ := decode_next_total_correct bytes 0#usize
  simp only [hd, bind_ok]
  have blen := bytes.property
  cases d with
  | End =>
    refine ⟨.Ok (alloc.vec.Vec.new U32), rfl, ?_, fun _ _ => ⟨_, rfl⟩⟩
    intro cs e; simp at e; subst e
    refine ⟨[], ?_, by simp [word, norm, stripOrderMark]⟩
    have : (0#usize).val = bytes.val.length := hstep
    simp at this
    rw [this]; exact TextFrom.endOfInput
  | Error err =>
    refine ⟨.Err ⟨.MalformedUtf8, 0#usize⟩, by simp [xml.fail], by simp, ?_⟩
    intro units ht
    exfalso
    cases err with
    | InvalidPosition p =>
      exact rejected_excludes_text _ _ _ (Rejected.position (congrArg UScalar.val hstep.1) hstep.2) units ht
    | InvalidUtf8 p =>
      exact rejected_excludes_text _ _ _ (Rejected.utf8 (congrArg UScalar.val hstep.1) hstep.2.1 hstep.2.2) units ht
    | NonXmlCharacter _ _ => exact hstep.elim
  | Scalar cp next =>
    obtain ⟨adv, bound, unit⟩ := hstep
    have z0 : (0#usize : Usize).val = 0 := by simp
    rw [z0] at adv unit
    dsimp only
    rw [xml_character_total_correct]
    simp only [bind_ok]
    have cr13 : decide (cp = 13#u32) = decide (cp.val = 13) := by
      by_cases h : cp.val = 13
      · have : cp = 13#u32 := UScalar.eq_of_val_eq (by simp [h])
        simp [this, h]
      · have : ¬ cp = 13#u32 := fun e => h (by rw [e]; simp)
        simp [this, h]
    by_cases xc : XmlChar cp.val
    · rw [if_pos (decide_eq_true xc)]
      by_cases bom : cp.val = 0xFEFF
      · have ht : xml.take (alloc.vec.Vec.new U32) cp 0#usize false = .ok (.Ok (alloc.vec.Vec.new U32)) := by
          unfold xml.take; simp [order_mark_eq, bom]
        obtain ⟨r, hr, sound, complete⟩ := decode_from_spec bytes next (alloc.vec.Vec.new U32) false adv
          (by simp; omega)
        have c13 : decide (cp.val = 13) = false := by simp [bom]
        refine ⟨r, by simp [ht, core.result.Result.Insts.CoreOpsTry.branch, cr13, c13, hr], ?_, ?_⟩
        · intro cs e
          obtain ⟨units, htu, hw⟩ := sound cs e
          refine ⟨(cp.val, 0) :: units, TextFrom.character unit xc (by omega) (by omega)
            (by rw [show 0 + (next.val - 0) = next.val by omega]; exact htu), ?_⟩
          rw [hw]; simp [bom, stripOrderMark, word]
        · intro units htu
          rcases textFrom_inv htu with ⟨e, -⟩ | ⟨cp', w', tail, unit', xc', wpos, fits, htail, rfl⟩
          · omega
          · rw [unit] at unit'; simp at unit'; obtain ⟨rfl, rfl⟩ := unit'
            exact complete _ (by simpa using htail)
      · obtain ⟨chars', ht, hlen, hnorm⟩ := take_spec (alloc.vec.Vec.new U32) cp 0#usize false
          (fun h => bom h.2) (by simp; scalar_tac)
        simp at hlen
        obtain ⟨r, hr, sound, complete⟩ := decode_from_spec bytes next chars' (decide (cp.val = 13)) adv
          (by omega)
        refine ⟨r, by simp [ht, core.result.Result.Insts.CoreOpsTry.branch, cr13, hr], ?_, ?_⟩
        · intro cs e
          obtain ⟨units, htu, hw⟩ := sound cs e
          refine ⟨(cp.val, 0) :: units, TextFrom.character unit xc (by omega) (by omega)
            (by rw [show 0 + (next.val - 0) = next.val by omega]; exact htu), ?_⟩
          rw [hw]; simp only [List.map_cons]; rw [stripOrderMark_ne _ _ bom, hnorm]; simp [word]
        · intro units htu
          rcases textFrom_inv htu with ⟨e, -⟩ | ⟨cp', w', tail, unit', xc', wpos, fits, htail, rfl⟩
          · omega
          · rw [unit] at unit'; simp at unit'; obtain ⟨rfl, rfl⟩ := unit'
            exact complete _ (by simpa using htail)
    · rw [if_neg (by simpa using xc)]
      refine ⟨.Err ⟨.NonXmlCharacter, 0#usize⟩, by simp [xml.fail], by simp, ?_⟩
      intro units htu
      exfalso
      rcases textFrom_inv htu with ⟨e, -⟩ | ⟨cp', w', tail, unit', xc', wpos, fits, htail, rfl⟩
      · omega
      · rw [unit] at unit'; simp at unit'; obtain ⟨rfl, rfl⟩ := unit'
        exact xc xc'

/-! ## The decoded characters -/

theorem decoded_unique {bs : List U8} {w1 w2 : Word} (h1 : Decoded bs w1) (h2 : Decoded bs w2) : w1 = w2 := by
  obtain ⟨u1, t1, rfl⟩ := h1
  obtain ⟨u2, t2, rfl⟩ := h2
  rw [textFrom_unique t1 t2]

/-- Decoding yields the unique decoded characters, or an error when the
    bytes have none. -/
theorem decode_spec (bytes : alloc.vec.Vec U8) :
    ∃ r, xml.decode bytes = .ok r ∧ (∀ cs, r = .Ok cs → Decoded bytes.val (word cs)) ∧
      (∀ w, Decoded bytes.val w → ∃ cs, r = .Ok cs ∧ word cs = w) := by
  obtain ⟨r, hr, sound, complete⟩ := decode_start bytes
  refine ⟨r, by rw [xml.decode]; exact hr, ?_, ?_⟩
  · intro cs e
    obtain ⟨units, ht, hw⟩ := sound cs e
    exact ⟨units, ht, by rw [hw, norm_false_eq]⟩
  · intro w hw
    obtain ⟨units, ht, rfl⟩ := hw
    obtain ⟨cs, rfl⟩ := complete units ht
    obtain ⟨units', ht', hw'⟩ := sound cs rfl
    refine ⟨cs, rfl, ?_⟩
    rw [hw', norm_false_eq, textFrom_unique ht' ht]

theorem decoded_length {bs : List U8} {w : Word} (h : Decoded bs w) : w.length ≤ bs.length := by
  obtain ⟨units, ht, rfl⟩ := h
  have l1 := textFrom_length ht
  rw [← norm_false_eq]
  have l2 := norm_length false (stripOrderMark (units.map (·.1)))
  have l3 := (stripOrderMark_suffix (units.map (·.1))).length_le
  simp at l3
  omega

theorem decoded_no_zero {bs : List U8} {w : Word} (h : Decoded bs w) : ∀ c ∈ w, c ≠ 0 := by
  obtain ⟨units, ht, rfl⟩ := h
  intro c hc
  rw [← norm_false_eq] at hc
  rcases norm_mem false _ c hc with hm | rfl
  · have hm' := (stripOrderMark_suffix (units.map (·.1))).subset hm
    simp at hm'
    obtain ⟨a, hu⟩ := hm'
    have := textFrom_chars ht _ hu
    simp [XmlChar] at this
    omega
  · omega

/-! ## Byte offsets of errors -/

theorem emitted_eq (offset : Usize) (cp : U32) (cr : Bool) :
    ∃ b, xml.emitted offset cp cr = .ok b := by
  simp [xml.emitted, order_mark_eq, crlf_eq]

theorem offset_from_total (bytes : alloc.vec.Vec U8) (offset count index : Usize) (cr : Bool)
    (h : count.val ≤ index.val) : ∃ o, xml.offset_from bytes offset count index cr = .ok o := by
  rw [xml.offset_from]
  obtain ⟨d, hd, hstep⟩ := decode_next_total_correct bytes offset
  simp only [hd, bind_ok]
  cases d with
  | End => exact ⟨_, rfl⟩
  | Error _ => exact ⟨_, rfl⟩
  | Scalar cp next =>
    obtain ⟨adv, bound, unit⟩ := hstep
    dsimp only
    obtain ⟨b, hb⟩ := emitted_eq offset cp cr
    rw [hb]; simp only [bind_ok]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      exact offset_from_total bytes next count index _ h
    · simp only [ite_true]
      by_cases e : count = index
      · rw [if_pos e]; exact ⟨_, rfl⟩
      · rw [if_neg e]
        have lt : count.val < index.val := by
          have : count.val ≠ index.val := fun v => e (UScalar.eq_of_val_eq v)
          omega
        obtain ⟨z, hz, hv⟩ := succ_spec lt
        rw [hz]; simp only [bind_ok]
        exact offset_from_total bytes next z index _ (by omega)
termination_by bytes.val.length - offset.val
decreasing_by all_goals omega

/-- Mapping a character position back to a byte offset never fails. -/
theorem byte_offset_total (bytes : alloc.vec.Vec U8) (index : Usize) :
    ∃ o, xml.byte_offset bytes index = .ok o := by
  rw [xml.byte_offset]; exact offset_from_total bytes 0#usize 0#usize index false (by simp)

end Rowl.XmlDecode
