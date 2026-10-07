import Rowl.XmlEntities

/-!
# Attribute values in the XML reader

`att_text` and `att_reference` normalize attribute text as §3.3.3 prescribes,
expanding entity references recursively within the budget. They are proved to
read exactly the grammar's `AttText`.
-/

namespace Rowl.XmlAttributes
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs Rowl.XmlEntities
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- The delimiting quote of attribute text; 0 stands for a replacement text. -/
def quoteOpt (q : U32) : Option Nat := if q.val = 0 then none else some q.val

theorem normalized_eq (c : U32) : ∃ n, xml.normalized c = .ok n ∧ n.val = normalized c.val := by
  by_cases h : IsSpace c.val
  · exact ⟨32#u32, by simp [xml.normalized, space_eq, h], by simp [XmlGrammar.normalized, h]⟩
  · exact ⟨c, by simp [xml.normalized, space_eq, h], by simp [XmlGrammar.normalized, h]⟩

/-- A replacement text read to its end. -/
theorem whole_text {t : alloc.vec.Vec U32} (nz : NoZero t) {j : Nat} {body : Word}
    (split : (word t).drop 0 = body ++ (word t).drop j) (stop : charAt t j = 0) : body = word t := by
  have : (word t).drop j = [] := by
    rcases charAt_head t j with ⟨e, _⟩ | ⟨rest, e⟩
    · exact e
    · exfalso
      have m : charAt t j ∈ word t := List.mem_of_mem_drop (show charAt t j ∈ (word t).drop j by rw [e]; simp)
      exact nz _ m stop
  rw [this] at split; simpa using split.symm

theorem charRef_len {w : Word} {v : Nat} (h : CharRef w v) : 0 < w.length := by
  cases h <;> simp

/-- Pushing a first declaration position whose name is not being expanded. -/
theorem stack_push {env : alloc.vec.Vec xml.Entity} {stack stack' : alloc.vec.Vec Usize} {names : List Word}
    (hstack : StackOk env stack names) {k : Usize} {nm : Word} (first : First env k.val)
    (hname : nameAt env k.val = some nm) (notIn : nm ∉ names) (hs : stack'.val = stack.val ++ [k]) :
    StackOk env stack' (nm :: names) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]; simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.mpr ⟨hstack.1, by simp, ?_⟩
    intro a ha b hb
    simp at hb; subst hb
    intro e2
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    apply notIn
    exact (hstack.2.2 _).mpr ⟨x, hx, by rw [UScalar.eq_of_val_eq e2]; exact hname⟩
  · intro x hx
    rw [hs] at hx
    rcases List.mem_append.mp hx with m | m
    · exact hstack.2.1 x m
    · simp at m; subst m; exact first
  · intro n
    rw [List.mem_cons, hstack.2.2 n, hs]
    constructor
    · rintro (rfl | ⟨x, hx, hn⟩)
      · exact ⟨k, by simp, hname⟩
      · exact ⟨x, by simp [hx], hn⟩
    · rintro ⟨x, hx, hn⟩
      rcases List.mem_append.mp hx with m | m
      · exact Or.inr ⟨x, m, hn⟩
      · simp at m; subst m; left
        rw [hname] at hn; exact (Option.some.inj hn).symm

theorem refMeaning_len {i : Nat} {w : Word} {ref : xml.Reference} (h : RefMeaning i w ref) :
    0 < w.length := by
  cases ref with
  | Character c =>
    rcases h with ⟨hr, _⟩ | ⟨nm, ⟨rfl, _⟩, _⟩
    · exact charRef_len hr
    · simp
  | Entity s e => obtain ⟨nm, ⟨rfl, _⟩, _⟩ := h; simp

theorem att_text_sound (cs : alloc.vec.Vec U32) (i : Usize) (quote : U32) (env : alloc.vec.Vec xml.Entity)
    (stack : alloc.vec.Vec Usize) (budget : Usize) (out : alloc.vec.Vec U32) {names : List Word}
    (henv : EnvOk env) (hstack : StackOk env stack names) :
    ∃ r, xml.att_text cs i quote env stack budget out = .ok r ∧
      ∀ out' j b', r = .Ok (out', j, b') →
        ∃ body value k, (word cs).drop i.val = body ++ (word cs).drop j.val ∧
          AttText (envView env) names (quoteOpt quote) body value k ∧
          word out' = word out ++ value ∧ b'.val + k = budget.val ∧ charAt cs j.val = quote.val := by
  rw [xml.att_text]
  by_cases stop : charAt cs i.val = quote.val
  · refine ⟨.Ok (out, i, budget), by simp [at_eq, atU_eq stop], ?_⟩
    intro out' j b' e
    simp at e; obtain ⟨rfl, rfl, rfl⟩ := e
    exact ⟨[], [], 0, by simp, AttText.nil, by simp, by simp, stop⟩
  · have ne : ¬ atU cs i.val = quote := atU_ne stop
    by_cases zero : charAt cs i.val = 0
    · have q0 : ¬ quote.val = 0 := fun e => stop (by rw [zero, e])
      exact ⟨.Err ⟨.UnexpectedEnd, i⟩, by simp [at_eq, ne, atU_eq (c := 0#u32) (by simpa using zero), q0,
        xml.fail], by simp⟩
    · have nz : ¬ atU cs i.val = 0#u32 := atU_ne (by simpa using zero)
      obtain ⟨inside, hd⟩ := drop_nonzero zero
      by_cases lt : charAt cs i.val = 60
      · have q60 : ¬ quote.val = 60 := fun e => stop (by rw [lt, e])
        exact ⟨.Err ⟨.Syntax, i⟩, by simp [at_eq, ne, nz, atU_eq (c := 60#u32) (by simpa using lt), q60,
          xml.fail], by simp⟩
      · have nlt : ¬ atU cs i.val = 60#u32 := atU_ne (by simpa using lt)
        by_cases amp : charAt cs i.val = 38
        · have namp : atU cs i.val = 38#u32 := atU_eq (by simpa using amp)
          have q38 : ¬ quote.val = 38 := fun e => stop (by rw [amp, e])
          have q38' : ¬ (38#u32 : U32) = quote := fun e => q38 (by rw [← e]; rfl)
          obtain ⟨r1, h1, sound1, _⟩ := reference_spec cs i amp
          cases r1 with
          | Err e =>
            exact ⟨.Err e, by simp [at_eq, ne, nz, nlt, namp, q38', xml.att_reference, h1,
              core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
          | Ok pair =>
            obtain ⟨ref, j1⟩ := pair
            obtain ⟨w, split1, j1v, meaning⟩ := sound1 ref j1 rfl
            have wpos := refMeaning_len meaning
            cases ref with
            | Character c =>
              by_cases room : out.val.length < Usize.max
              · obtain ⟨r2, h2, sound2⟩ := att_text_sound cs j1 quote env stack budget
                  (alloc.vec.Vec.from (out.val ++ [c]) (by simp; omega)) henv hstack
                refine ⟨r2, by simp [at_eq, ne, nz, nlt, namp, q38', xml.att_reference, h1,
                  core.result.Result.Insts.CoreOpsTry.branch, push_char_eq, room, h2], ?_⟩
                intro out' j b' e
                obtain ⟨body, value, k, split2, hav, hout, hb, hstop⟩ := sound2 out' j b' e
                refine ⟨w ++ body, c.val :: value, k, by rw [split1, split2]; simp, ?_, ?_, hb, hstop⟩
                · rcases meaning with ⟨hr, xc⟩ | ⟨nm, hn, hp⟩
                  · exact AttText.charRef hr xc hav
                  · exact AttText.predefined hn hp hav
                · rw [hout, word_push]; simp
              · exact ⟨.Err ⟨.ResourceLimit, i⟩, by simp [at_eq, ne, nz, nlt, namp, q38', xml.att_reference, h1,
                  core.result.Result.Insts.CoreOpsTry.branch, push_char_eq, room, same_residual], by simp⟩
            | Entity s e =>
              obtain ⟨nm, ⟨rfl, ncn⟩, pre, sv, ev⟩ := meaning
              have nmSplit : (word cs).drop s.val = nm ++ (59 :: (word cs).drop j1.val) := by
                rw [sv]; have := split1; rw [hd] at this; simp at this; exact this.2
              obtain ⟨r3, h3, sound3, _⟩ := expandable_spec cs s e env stack i hstack nmSplit (by rw [ev, sv])
              cases r3 with
              | Err err =>
                exact ⟨.Err err, by simp [at_eq, ne, nz, nlt, namp, q38', xml.att_reference, h1,
                  core.result.Result.Insts.CoreOpsTry.branch, h3, same_residual], by simp⟩
              | Ok k =>
                obtain ⟨ent, hent, first, hname, look, notIn⟩ := sound3 k rfl
                have kin : k.val < env.val.length := first.1
                have ek : env.val[k.val] = ent := by
                  rw [List.getElem?_eq_getElem kin] at hent; exact Option.some.inj hent
                obtain ⟨r4, h4, c4⟩ := spend_spec env k budget i kin
                cases r4 with
                | Err err =>
                  exact ⟨.Err err, by simp [at_eq, ne, nz, nlt, namp, q38', xml.att_reference, h1,
                    core.result.Result.Insts.CoreOpsTry.branch, h3, h4, same_residual], by simp⟩
                | Ok b1 =>
                  obtain ⟨costOk, b1v⟩ := c4
                  rw [ek] at costOk b1v
                  have room : stack.val.length < Usize.max := by
                    refine stack_room hstack first (fun x hx e2 => ?_)
                    apply notIn
                    exact (hstack.2.2 _).mpr ⟨x, hx, by rw [e2]; simp [nameAt, hent, hname]⟩
                  obtain ⟨stack', h5, hs5⟩ := pushed_spec stack k i room
                  have hstack' : StackOk env stack' (word ent.«name» :: names) := by
                    refine ⟨?_, ?_, ?_⟩
                    · rw [hs5]; simp only [List.map_append, List.map_cons, List.map_nil]
                      refine List.nodup_append.mpr ⟨hstack.1, by simp, ?_⟩
                      intro a ha b hb
                      simp at hb; subst hb
                      intro e2
                      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
                      apply notIn
                      rw [← hname]
                      exact (hstack.2.2 _).mpr ⟨x, hx, by rw [UScalar.eq_of_val_eq e2]; simp [nameAt, hent]⟩
                    · intro x hx
                      rw [hs5] at hx
                      rcases List.mem_append.mp hx with m | m
                      · exact hstack.2.1 x m
                      · simp at m; subst m; exact first
                    · intro n
                      rw [List.mem_cons, hstack.2.2 n, hs5]
                      constructor
                      · rintro (rfl | ⟨x, hx, hn⟩)
                        · exact ⟨k, by simp, by simp [nameAt, hent]⟩
                        · exact ⟨x, by simp [hx], hn⟩
                      · rintro ⟨x, hx, hn⟩
                        rcases List.mem_append.mp hx with m | m
                        · exact Or.inr ⟨x, m, hn⟩
                        · simp at m; subst m; left
                          simp [nameAt, hent] at hn; exact hn.symm
                  have lookEnt : env.val[k.val] = ent := ek
                  obtain ⟨r6, h6, sound6⟩ := att_text_sound ent.text 0#usize 0#u32 env stack' b1 out henv hstack'
                  cases r6 with
                  | Err err =>
                    exact ⟨.Err ⟨err.kind, i⟩, by simp [at_eq, ne, nz, nlt, namp, q38', xml.att_reference, h1,
                      core.result.Result.Insts.CoreOpsTry.branch, h3, h4, h5, alloc.vec.Vec.index_usize,
                      List.getElem?_eq_getElem kin, lookEnt, h6, xml.fail, same_residual], by simp⟩
                  | Ok triple =>
                    obtain ⟨out1, jj, b2⟩ := triple
                    obtain ⟨body1, value1, k1, split6, hav1, hout1, hb1, hstop1⟩ := sound6 out1 jj b2 rfl
                    have bodyAll : body1 = word ent.text :=
                      whole_text (henv ent (by rw [← lookEnt]; exact List.getElem_mem kin)) split6
                        (by simpa using hstop1)
                    obtain ⟨r7, h7, sound7⟩ := att_text_sound cs j1 quote env stack b2 out1 henv hstack
                    refine ⟨r7, by simp [at_eq, ne, nz, nlt, namp, q38', xml.att_reference, h1,
                      core.result.Result.Insts.CoreOpsTry.branch, h3, h4, h5, alloc.vec.Vec.index_usize,
                      List.getElem?_eq_getElem kin, lookEnt, h6, h7], ?_⟩
                    intro out' j b' e7
                    obtain ⟨body2, value2, k2, split7, hav2, hout2, hb2, hstop2⟩ := sound7 out' j b' e7
                    refine ⟨(38 :: nm ++ [59]) ++ body2, value1 ++ value2, (word ent.text).length + 1 + k1 + k2,
                      by rw [split1, split7]; simp, ?_, by rw [hout2, hout1]; simp, ?_, hstop2⟩
                    · rw [← hname] at pre look notIn ⊢
                      rw [bodyAll] at hav1
                      exact AttText.entity ⟨rfl, hname ▸ ncn⟩ pre look notIn hav1 hav2
                    · rw [word_length] ; omega
        · -- a plain character
          have namp : ¬ atU cs i.val = 38#u32 := atU_ne (by simpa using amp)
          obtain ⟨n, hn, hnv⟩ := normalized_eq (atU cs i.val)
          rw [atU_val] at hnv
          obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
          by_cases room : out.val.length < Usize.max
          · obtain ⟨r2, h2, sound2⟩ := att_text_sound cs i1 quote env stack budget
              (alloc.vec.Vec.from (out.val ++ [n]) (by simp; omega)) henv hstack
            refine ⟨r2, by simp [at_eq, ne, nz, nlt, namp, hn, push_char_eq, room, hi1, h2,
              core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
            intro out' j b' e
            obtain ⟨body, value, k, split2, hav, hout, hb, hstop⟩ := sound2 out' j b' e
            refine ⟨charAt cs i.val :: body, normalized (charAt cs i.val) :: value, k, ?_, ?_, ?_, hb, hstop⟩
            · rw [hd, ← hi1v, split2]; simp
            · refine AttText.char lt amp ?_ hav
              unfold quoteOpt
              split_ifs with q0
              · simp
              · intro e; simp at e; exact stop e.symm
            · rw [hout, word_push, hnv]; simp
          · exact ⟨.Err ⟨.ResourceLimit, i⟩, by simp [at_eq, ne, nz, nlt, namp, hn, push_char_eq, room,
              core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
termination_by (budget.val, cs.val.length - i.val)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; omega)

/-- Two words consumed from the same position with the same length agree. -/
theorem same_consumed {cs : alloc.vec.Vec U32} {i : Nat} {w1 w2 r1 r2 : Word}
    (s1 : (word cs).drop i = w1 ++ r1) (s2 : (word cs).drop i = w2 ++ r2) (l : w1.length = w2.length) :
    w1 = w2 :=
  (List.append_inj (s1.symm.trans s2) l).1

theorem charRef_unique_of {w w' : Word} {v v' : Nat} (h1 : CharRef w v) (h2 : CharRef w' v') (e : w = w') :
    v = v' := by
  cases h1 with
  | @decimal ds ne all =>
    cases h2 with
    | @decimal ds' _ _ =>
      rw [lit_amp_hash] at e
      have : ds = ds' := by simpa using e
      rw [this]
    | @hex ds' _ _ =>
      exfalso
      rw [lit_amp_hash, lit_amp_hash_x] at e
      cases ds with
      | nil => exact ne rfl
      | cons d _ =>
        simp at e
        have := all d (by simp); rw [e.1] at this; exact not_digit_x this
  | @hex ds ne all =>
    cases h2 with
    | @decimal ds' ne' all' =>
      exfalso
      rw [lit_amp_hash, lit_amp_hash_x] at e
      cases ds' with
      | nil => exact ne' rfl
      | cons d _ =>
        simp at e
        have := all' d (by simp); rw [e.1] at this; exact not_digit_x this
    | @hex ds' _ _ =>
      rw [lit_amp_hash_x] at e
      have : ds = ds' := by simpa using e
      rw [this]

theorem charRef_unique {w : Word} {v v' : Nat} (h1 : CharRef w v) (h2 : CharRef w v') : v = v' :=
  charRef_unique_of h1 h2 rfl

theorem entityRef_unique {w nm nm' : Word} (h1 : EntityRef w nm) (h2 : EntityRef w nm') : nm = nm' := by
  obtain ⟨e1, _⟩ := h1
  obtain ⟨e2, _⟩ := h2
  rw [e1] at e2
  simpa using e2

theorem charRef_not_entity {w nm : Word} {v : Nat} (h1 : CharRef w v) (h2 : EntityRef w nm) : False := by
  obtain ⟨e2, ncn⟩ := h2
  obtain ⟨c, rest, e, hc, _⟩ := ncn.1
  have hash : (w.drop 1).head? = some 35 := by
    cases h1 <;> simp [lit_amp_hash, lit_amp_hash_x]
  rw [e2, e] at hash
  simp at hash
  rw [hash] at hc
  simp [NameStartChar] at hc

theorem charRef_head {w : Word} {v : Nat} (h : CharRef w v) : ∃ t, w = 38 :: t := by
  cases h with
  | @decimal ds _ _ => exact ⟨35 :: (ds ++ [59]), by rw [lit_amp_hash]; simp⟩
  | @hex ds _ _ => exact ⟨35 :: 120 :: (ds ++ [59]), by rw [lit_amp_hash_x]; simp⟩

theorem entityRef_head {w nm : Word} (h : EntityRef w nm) : ∃ t, w = 38 :: t := ⟨_, h.1⟩

/-- The quotes of attribute text: none, `"` or `'`. -/
def QuoteOk (q : U32) : Prop := q.val = 0 ∨ q.val = 34 ∨ q.val = 39

theorem att_text_complete {E : Env} {names : List Word} {q : Option Nat} {body value : Word} {k : Nat}
    (h : AttText E names q body value k) :
    ∀ (cs : alloc.vec.Vec U32) (i : Usize) (quote : U32) (env : alloc.vec.Vec xml.Entity)
      (stack : alloc.vec.Vec Usize) (budget : Usize) (out : alloc.vec.Vec U32) (rest : Word),
      E = envView env → EnvOk env → StackOk env stack names → q = quoteOpt quote → QuoteOk quote →
      (word cs).drop i.val = body ++ rest → charAt cs (i.val + body.length) = quote.val →
      (∀ c ∈ body, c ≠ 0) → k ≤ budget.val → out.val.length + value.length ≤ Usize.max →
      ∃ out' j b', xml.att_text cs i quote env stack budget out = .ok (.Ok (out', j, b')) ∧
        word out' = word out ++ value ∧ j.val = i.val + body.length ∧ b'.val + k = budget.val := by
  induction h with
  | nil =>
    intro cs i quote env stack budget out rest _ _ _ _ _ split stop _ _ _
    refine ⟨out, i, budget, ?_, by simp, by simp, by simp⟩
    rw [xml.att_text]
    simp [at_eq, atU_eq (by simpa using stop)]
  | @char stack' q' c rest' out' k' hc60 hc38 hq hrest ih =>
    intro cs i quote env stack budget out rest hE henv hstack hqq hquote split stop nz kb room
    have c0 := first_char (cs := cs) (i := i.val) (c := c) (rest := rest' ++ rest) (by rw [split]; simp)
    have cnz : c ≠ 0 := nz c (by simp)
    obtain ⟨inside, hd⟩ := drop_nonzero (by rw [c0]; exact cnz)
    have cq : ¬ charAt cs i.val = quote.val := by
      rw [c0]
      intro e
      unfold quoteOpt at hqq
      split_ifs at hqq with q0
      · exact cnz (by rw [e, q0])
      · exact hq (by rw [hqq, e])
    obtain ⟨n, hn, hnv⟩ := normalized_eq (atU cs i.val)
    rw [atU_val, c0] at hnv
    obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
    have room1 : out.val.length < Usize.max := by simp at room; omega
    obtain ⟨o, j, b, run, hout, hj, hb⟩ := ih cs i1 quote env stack budget
      (alloc.vec.Vec.from (out.val ++ [n]) (by simp; omega)) rest hE henv hstack hqq hquote
      (by rw [hi1v]; rw [hd, c0] at split; simpa using split)
      (by rw [hi1v, show i.val + 1 + rest'.length = i.val + (c :: rest').length by simp; omega]; exact stop)
      (fun x hx => nz x (by simp [hx])) kb (by simp at room ⊢; omega)
    refine ⟨o, j, b, ?_, by rw [hout, word_push, hnv]; simp, by rw [hj, hi1v]; simp; omega, hb⟩
    rw [xml.att_text]
    simp [at_eq, atU_ne (c := quote) cq,
      atU_ne (cs := cs) (i := i.val) (c := 0#u32) (by rw [c0]; simpa using cnz),
      atU_ne (cs := cs) (i := i.val) (c := 60#u32) (by rw [c0]; simpa using hc60),
      atU_ne (cs := cs) (i := i.val) (c := 38#u32) (by rw [c0]; simpa using hc38),
      hn, push_char_eq, room1, hi1, run, core.result.Result.Insts.CoreOpsTry.branch]
  | @charRef stack' q' r v rest' out' k' hr xc hrest ih =>
    intro cs i quote env stack budget out rest hE henv hstack hqq hquote split stop nz kb room
    obtain ⟨t, rt⟩ := charRef_head hr
    have amp : charAt cs i.val = 38 := first_char (rest := t ++ rest' ++ rest) (by rw [split, rt]; simp)
    have q38 : ¬ (38#u32 : U32) = quote := by
      intro e; have := congrArg UScalar.val e; simp at this
      rcases hquote with h | h | h <;> omega
    have split' : (word cs).drop i.val = r ++ (rest' ++ rest) := by rw [split]; simp
    obtain ⟨r1, h1, sound1, complete1⟩ := reference_spec cs i amp
    obtain ⟨ref, j1, hr1, hj1⟩ := complete1 r (rest' ++ rest) split' (Or.inl ⟨v, hr, xc⟩)
    subst hr1
    obtain ⟨w, sw, jw, meaning⟩ := sound1 ref j1 rfl
    have wr : w = r := same_consumed sw split' (by omega)
    subst wr
    cases ref with
    | Entity s e =>
      obtain ⟨nm, hn, _⟩ := meaning
      exact absurd hn (fun hn => charRef_not_entity hr hn)
    | Character c =>
      have cv : c.val = v := by
        rcases meaning with ⟨hr', _⟩ | ⟨nm, hn, _⟩
        · exact charRef_unique hr' hr
        · exact (charRef_not_entity hr hn).elim
      have room1 : out.val.length < Usize.max := by simp at room; omega
      have after : (word cs).drop j1.val = rest' ++ rest := by rw [hj1]; exact drop_after split'
      obtain ⟨o, j, b, run, hout, hj, hb⟩ := ih cs j1 quote env stack budget
        (alloc.vec.Vec.from (out.val ++ [c]) (by simp; omega)) rest hE henv hstack hqq hquote after
        (by rw [hj1, show i.val + w.length + rest'.length = i.val + (w ++ rest').length by simp; omega]; exact stop)
        (fun x hx => nz x (by simp [hx])) kb (by simp at room ⊢; omega)
      refine ⟨o, j, b, ?_, by rw [hout, word_push, cv]; simp, by rw [hj, hj1]; simp; omega, hb⟩
      rw [xml.att_text]
      simp [at_eq, atU_eq (c := 38#u32) (by simpa using amp), q38, xml.att_reference, h1, push_char_eq,
        room1, run, core.result.Result.Insts.CoreOpsTry.branch]
  | @predefined stack' q' r nm v rest' out' k' hr hp hrest ih =>
    intro cs i quote env stack budget out rest hE henv hstack hqq hquote split stop nz kb room
    obtain ⟨t, rt⟩ := entityRef_head hr
    have amp : charAt cs i.val = 38 := first_char (rest := t ++ rest' ++ rest) (by rw [split, rt]; simp)
    have q38 : ¬ (38#u32 : U32) = quote := by
      intro e; have := congrArg UScalar.val e; simp at this
      rcases hquote with h | h | h <;> omega
    have split' : (word cs).drop i.val = r ++ (rest' ++ rest) := by rw [split]; simp
    obtain ⟨r1, h1, sound1, complete1⟩ := reference_spec cs i amp
    obtain ⟨ref, j1, hr1, hj1⟩ := complete1 r (rest' ++ rest) split' (Or.inr ⟨nm, hr⟩)
    subst hr1
    obtain ⟨w, sw, jw, meaning⟩ := sound1 ref j1 rfl
    have wr : w = r := same_consumed sw split' (by omega)
    subst wr
    cases ref with
    | Entity s e =>
      obtain ⟨nm', hn, hpn, _⟩ := meaning
      rw [entityRef_unique hn hr] at hpn
      rw [hp] at hpn; cases hpn
    | Character c =>
      have cv : c.val = v := by
        rcases meaning with ⟨hr', _⟩ | ⟨nm', hn, hpn⟩
        · exact (charRef_not_entity hr' hr).elim
        · rw [entityRef_unique hn hr, hp] at hpn; exact (Option.some.inj hpn).symm
      have room1 : out.val.length < Usize.max := by simp at room; omega
      have after : (word cs).drop j1.val = rest' ++ rest := by rw [hj1]; exact drop_after split'
      obtain ⟨o, j, b, run, hout, hj, hb⟩ := ih cs j1 quote env stack budget
        (alloc.vec.Vec.from (out.val ++ [c]) (by simp; omega)) rest hE henv hstack hqq hquote after
        (by rw [hj1, show i.val + w.length + rest'.length = i.val + (w ++ rest').length by simp; omega]; exact stop)
        (fun x hx => nz x (by simp [hx])) kb (by simp at room ⊢; omega)
      refine ⟨o, j, b, ?_, by rw [hout, word_push, cv]; simp, by rw [hj, hj1]; simp; omega, hb⟩
      rw [xml.att_text]
      simp [at_eq, atU_eq (c := 38#u32) (by simpa using amp), q38, xml.att_reference, h1, push_char_eq,
        room1, run, core.result.Result.Insts.CoreOpsTry.branch]
  | @entity stack' q' r nm text sub rest' out' k1 k2 hr hp look notIn hinner hrest ihInner ihRest =>
    intro cs i quote env stack budget out rest hE henv hstack hqq hquote split stop nz kb room
    obtain ⟨t, rt⟩ := entityRef_head hr
    have amp : charAt cs i.val = 38 := first_char (rest := t ++ rest' ++ rest) (by rw [split, rt]; simp)
    have q38 : ¬ (38#u32 : U32) = quote := by
      intro e; have := congrArg UScalar.val e; simp at this
      rcases hquote with h | h | h <;> omega
    have split' : (word cs).drop i.val = r ++ (rest' ++ rest) := by rw [split]; simp
    obtain ⟨r1, h1, sound1, complete1⟩ := reference_spec cs i amp
    obtain ⟨ref, j1, hr1, hj1⟩ := complete1 r (rest' ++ rest) split' (Or.inr ⟨nm, hr⟩)
    subst hr1
    obtain ⟨w, sw, jw, meaning⟩ := sound1 ref j1 rfl
    have wr : w = r := same_consumed sw split' (by omega)
    subst wr
    have after : (word cs).drop j1.val = rest' ++ rest := by rw [hj1]; exact drop_after split'
    cases ref with
    | Character c =>
      exfalso
      rcases meaning with ⟨hr', _⟩ | ⟨nm', hn, hpn⟩
      · exact charRef_not_entity hr' hr
      · rw [entityRef_unique hn hr, hp] at hpn; cases hpn
    | Entity s e =>
      obtain ⟨nm', hn, _, sv, ev⟩ := meaning
      have nme : nm' = nm := entityRef_unique hn hr
      subst nme
      have nmSplit : (word cs).drop s.val = nm' ++ 59 :: (word cs).drop j1.val := by
        rw [sv, after]
        have := drop_after (cs := cs) (i := i.val) (w := [38]) (rest := nm' ++ 59 :: (rest' ++ rest))
          (by rw [split', hr.1]; simp)
        simpa using this
      obtain ⟨r3, h3, sound3, complete3⟩ := expandable_spec cs s e env stack i hstack nmSplit (by rw [ev, sv])
      rw [hE] at look
      obtain ⟨k, hk⟩ := complete3 text look notIn
      subst hk
      obtain ⟨ent, hent, first, hname, look', _⟩ := sound3 k rfl
      have tv : text = word ent.text := by rw [look] at look'; simpa using look'
      subst tv
      have kin : k.val < env.val.length := first.1
      have ek : env.val[k.val] = ent := by
        rw [List.getElem?_eq_getElem kin] at hent; exact Option.some.inj hent
      obtain ⟨r4, h4, c4⟩ := spend_spec env k budget i kin
      rw [ek] at c4
      cases r4 with
      | Err _ =>
        exfalso; rw [word_length] at kb; simp at c4; omega
      | Ok b1 =>
        obtain ⟨costOk, b1v⟩ := c4
        rw [word_length] at kb
        have roomS : stack.val.length < Usize.max := by
          refine stack_room hstack first (fun x hx e2 => ?_)
          apply notIn
          exact (hstack.2.2 _).mpr ⟨x, hx, by rw [e2]; simp [nameAt, hent, hname]⟩
        obtain ⟨stack'', h5, hs5⟩ := pushed_spec stack k i roomS
        have hstack'' : StackOk env stack'' (nm' :: stack') :=
          stack_push hstack first (by simp [nameAt, hent, hname]) notIn hs5
        have endText : charAt ent.text ((0#usize : Usize).val + (word ent.text).length) = (0#u32 : U32).val := by
          simp [charAt, word_length, word_getElem_opt]
        obtain ⟨o1, jj, b2, run1, hout1, hjj, hb2⟩ := ihInner ent.text 0#usize 0#u32 env stack'' b1 out []
          hE henv hstack'' (by simp [quoteOpt]) (Or.inl rfl) (by simp) endText
          (henv ent (by rw [← ek]; exact List.getElem_mem kin)) (by omega) (by simp at room ⊢; omega)
        have o1len : o1.val.length = out.val.length + (word ent.text).length - (word ent.text).length +
            sub.length := by
          have := congrArg List.length hout1
          simp [word] at this; omega
        have stop' : charAt cs (j1.val + rest'.length) = quote.val := by
          rw [hj1, show i.val + w.length + rest'.length = i.val + (w ++ rest').length by simp; omega]
          exact stop
        obtain ⟨o, j, b, run2, hout, hj, hb⟩ := ihRest cs j1 quote env stack b2 o1 rest hE henv hstack hqq
          hquote after stop' (fun x hx => nz x (by simp [hx])) (by omega)
          (by simp at room; omega)
        have wl := word_length ent.text
        refine ⟨o, j, b, ?_, by rw [hout, hout1]; simp, by rw [hj, hj1]; simp; omega, by omega⟩
        rw [xml.att_text]
        simp [at_eq, atU_eq (c := 38#u32) (by simpa using amp), q38, xml.att_reference, h1, h3, h4, h5,
          alloc.vec.Vec.index_usize, List.getElem?_eq_getElem kin, ek, run1, run2,
          core.result.Result.Insts.CoreOpsTry.branch]

end Rowl.XmlAttributes
