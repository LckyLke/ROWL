import Rowl.XmlLiterals

/-!
# Entity values and entity declarations

`entity_value` reads the grammar's `EntityValue` with its replacement text,
and the declaration functions read `GEDecl` and `PEDecl`.
-/

namespace Rowl.XmlEntityDecls
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs Rowl.XmlEntities Rowl.XmlAttributes Rowl.XmlTags Rowl.XmlNamespaces Rowl.XmlContent Rowl.XmlElements Rowl.XmlComplete Rowl.XmlDecl Rowl.XmlLiterals
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-- What a reference in an entity value stands for: a character reference
    is replaced, a general entity reference is kept. -/
def ValueRef (w x : Word) : Prop :=
  (∃ v, CharRef w v ∧ Rowl.Unicode.XmlChar v ∧ x = [v]) ∨ (∃ ename, EntityRef w ename ∧ x = w)

theorem valueRef_head {w x : Word} (h : ValueRef w x) : ∃ t, w = 38 :: t := by
  rcases h with ⟨v, hr, _, _⟩ | ⟨ename, hr, _⟩
  · exact charRef_head hr
  · exact entityRef_head hr

theorem valueRef_len {w x : Word} (h : ValueRef w x) : x.length ≤ w.length ∧ 0 < w.length := by
  rcases h with ⟨v, hr, _, rfl⟩ | ⟨ename, hr, rfl⟩
  · have := charRef_len hr; simp; omega
  · obtain ⟨t, rfl⟩ := entityRef_head hr; simp

theorem charRef_hash {w : Word} {v : Nat} (h : CharRef w v) : ∃ t, w = 38 :: 35 :: t := by
  cases h with
  | decimal _ _ => exact ⟨_, by rw [lit_amp_hash]; rfl⟩
  | hex _ _ => exact ⟨_, by rw [lit_amp_hash_x]; rfl⟩

theorem value_reference_spec (cs : alloc.vec.Vec U32) (i : Usize) (text : alloc.vec.Vec U32)
    (amp : charAt cs i.val = 38) :
    ∃ r, xml.value_reference cs i text = .ok r ∧
      (∀ t j, r = .Ok (t, j) → ∃ w x, (word cs).drop i.val = w ++ (word cs).drop j.val ∧ j.val = i.val + w.length ∧
        ValueRef w x ∧ word t = word text ++ x) ∧
      (∀ w x rest, (word cs).drop i.val = w ++ rest → ValueRef w x → text.val.length + w.length ≤ Usize.max →
        ∃ t j, r = .Ok (t, j) ∧ word t = word text ++ x ∧ j.val = i.val + w.length) := by
  unfold xml.value_reference
  obtain ⟨inside, hd⟩ := drop_nonzero (by rw [amp]; decide : charAt cs i.val ≠ 0)
  obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
  simp only [hi1, bind_ok, at_eq, atU_eq_iff, hi1v]
  by_cases hash : charAt cs (i.val + 1) = 35
  · have start : lit "&#" <+: (word cs).drop i.val := by
      have h1 : i.val + 1 < cs.val.length := charAt_inside (by rw [hash]; decide)
      rw [hd, amp, drop_charAt h1, hash, lit_amp_hash]; exact ⟨_, rfl⟩
    rw [if_pos (by simpa using hash)]
    obtain ⟨r1, h1, sound1, complete1⟩ := char_reference_spec cs i start
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
      intro w x rest split hv _
      rcases hv with ⟨v, hr, hx, _⟩ | ⟨ename, ⟨rfl, ncn⟩, _⟩
      · obtain ⟨c, j, hc, _⟩ := complete1 w v rest split hr hx
        cases hc
      · exfalso
        obtain ⟨c0, r0, e0, hc0, _⟩ := ncn.1
        have : charAt cs (i.val + 1) = c0 := by
          have := charAt_of_drop (cs := cs) split (t := 1) (by rw [e0]; simp)
          simpa [e0] using this
        rw [this] at hash; rw [hash] at hc0; simp [NameStartChar] at hc0
    | Ok pair =>
      obtain ⟨c, j⟩ := pair
      obtain ⟨w, split, hj, hr, hx⟩ := sound1 c j rfl
      have wl := charRef_len hr
      by_cases room : text.val.length < Usize.max
      · refine ⟨.Ok (alloc.vec.Vec.from (text.val ++ [c]) (by simp; omega), j), by
          simp [h1, core.result.Result.Insts.CoreOpsTry.branch, push_char_eq, room], ?_, ?_⟩
        · intro t j' e; simp at e; obtain ⟨rfl, rfl⟩ := e
          exact ⟨w, [c.val], split, hj, Or.inl ⟨c.val, hr, hx, rfl⟩, word_push text c _⟩
        · intro w' x rest split' hv _
          have ww : w' = w := by
            rcases hv with ⟨v, hr', hx', _⟩ | ⟨ename, hr', _⟩
            · obtain ⟨c', j', hc', _, hj'⟩ := complete1 w' v rest split' hr' hx'
              simp at hc'; obtain ⟨rfl, rfl⟩ := hc'
              exact same_consumed split' split (by omega)
            · exfalso
              obtain ⟨rfl, ncn⟩ := hr'
              obtain ⟨c0, r0, e0, hc0, _⟩ := ncn.1
              have : charAt cs (i.val + 1) = c0 := by
                have := charAt_of_drop (cs := cs) split' (t := 1) (by rw [e0]; simp)
                simpa [e0] using this
              rw [this] at hash; rw [hash] at hc0; simp [NameStartChar] at hc0
          subst ww
          rcases hv with ⟨v, hr', hx', rfl⟩ | ⟨ename, hr', _⟩
          · refine ⟨_, j, rfl, ?_, hj⟩
            rw [word_push, charRef_unique hr hr']
          · exact (charRef_not_entity hr hr').elim
      · refine ⟨.Err ⟨.ResourceLimit, i⟩, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, push_char_eq,
          room, same_residual], by simp, ?_⟩
        intro w' x rest split' hv hroom
        exfalso; apply room
        have := (valueRef_len hv).2
        omega
  · rw [if_neg (by simpa using hash)]
    obtain ⟨r1, h1, sound1, complete1⟩ := entity_name_spec cs i inside
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
      intro w x rest split hv _
      rcases hv with ⟨v, hr, _, _⟩ | ⟨ename, ⟨rfl, ncn⟩, _⟩
      · exfalso; apply hash
        obtain ⟨t, rfl⟩ := charRef_hash hr
        have := charAt_of_drop (cs := cs) split (t := 1) (by simp)
        simpa using this
      · have d1 : (word cs).drop (i.val + 1) = ename ++ 59 :: rest := by
          rw [hd] at split; simp at split; exact split.2
        have nr : nameRun cs (i.val + 1) = ename :=
          nameRun_eq d1 (name_all ncn.1) (fun c m e => by simp at e; rw [e.1]; simp [NameChar, NameStartChar])
        have semi : charAt cs (i.val + 1 + ename.length) = 59 := by
          have := charAt_after d1; simpa using this
        obtain ⟨stop, j, hsj⟩ := complete1 (by rw [nr]; exact ncn) (by rw [nr]; exact semi)
        cases hsj
    | Ok pair =>
      obtain ⟨stop, j⟩ := pair
      obtain ⟨hstop, ncn, semi, hj⟩ := sound1 stop j rfl
      generalize hn : nameRun cs (i.val + 1) = nm at hstop ncn
      have nsplit : (word cs).drop i.val = (38 :: nm ++ [59]) ++ (word cs).drop j.val := by
        have e1 := nameRun_split cs (i.val + 1)
        rw [hn, ← hstop] at e1
        obtain ⟨_, ds⟩ := drop_nonzero (by rw [semi]; decide : charAt cs stop.val ≠ 0)
        rw [hd, amp, e1, ds, semi, ← hj]; simp
      have hjv : j.val = i.val + (38 :: nm ++ [59]).length := by simp; omega
      obtain ⟨r2, h2, s2, c2⟩ := copy_from_spec cs i j text nsplit hjv
      cases r2 with
      | Err err =>
        refine ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, xml.bypass, h2, same_residual],
          by simp, ?_⟩
        intro w x rest split hv hroom
        have ww : w = 38 :: nm ++ [59] := by
          rcases hv with ⟨v, hr, _, _⟩ | ⟨ename, ⟨rfl, ncn'⟩, _⟩
          · exfalso; apply hash
            obtain ⟨t, rfl⟩ := charRef_hash hr
            have := charAt_of_drop (cs := cs) split (t := 1) (by simp)
            simpa using this
          · have d1 : (word cs).drop (i.val + 1) = ename ++ 59 :: rest := by
              rw [hd] at split; simp at split; exact split.2
            have nr : nameRun cs (i.val + 1) = ename :=
              nameRun_eq d1 (name_all ncn'.1) (fun c m e => by simp at e; rw [e.1]; simp [NameChar, NameStartChar])
            rw [← hn, nr]
        subst ww
        obtain ⟨v, hv'⟩ := c2 (by simpa using hroom)
        cases hv'
      | Ok t =>
        refine ⟨.Ok (t, j), by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, xml.bypass, h2], ?_, ?_⟩
        · intro t' j' e; simp at e; obtain ⟨rfl, rfl⟩ := e
          exact ⟨38 :: nm ++ [59], 38 :: nm ++ [59], nsplit, hjv, Or.inr ⟨nm, ⟨rfl, ncn⟩, rfl⟩, s2 t rfl⟩
        · intro w x rest split hv hroom
          rcases hv with ⟨v, hr, _, _⟩ | ⟨ename, ⟨rfl, ncn'⟩, rfl⟩
          · exfalso; apply hash
            obtain ⟨t, rfl⟩ := charRef_hash hr
            have := charAt_of_drop (cs := cs) split (t := 1) (by simp)
            simpa using this
          · have d1 : (word cs).drop (i.val + 1) = ename ++ 59 :: rest := by
              rw [hd] at split; simp at split; exact split.2
            have nr : nameRun cs (i.val + 1) = ename :=
              nameRun_eq d1 (name_all ncn'.1) (fun c m e => by simp at e; rw [e.1]; simp [NameChar, NameStartChar])
            rw [hn] at nr; subst nr
            exact ⟨t, j, rfl, s2 t rfl, by rw [hjv]⟩

theorem valueText_nil {q : Nat} {out : Word} (h : ValueText q [] out) : out = [] := by
  generalize hb : ([] : Word) = b at h
  cases h with
  | nil => rfl
  | char _ _ _ _ => simp at hb
  | charRef hr _ _ => obtain ⟨t, ht⟩ := charRef_head hr; rw [ht] at hb; simp at hb
  | entityRef hr _ => obtain ⟨t, ht⟩ := entityRef_head hr; rw [ht] at hb; simp at hb

theorem quote_ne_38 {q : Nat} (h : Quote q) : q ≠ 38 := by rcases h with rfl | rfl <;> simp
theorem quote_ne_37 {q : Nat} (h : Quote q) : q ≠ 37 := by rcases h with rfl | rfl <;> simp

theorem entity_value_spec (cs : alloc.vec.Vec U32) (i : Usize) (q : U32) (hq : Quote q.val)
    (text : alloc.vec.Vec U32) :
    ∃ r, xml.entity_value cs i q text = .ok r ∧
      (∀ t j, r = .Ok (t, j) → ∃ body out, (word cs).drop i.val = body ++ (word cs).drop j.val ∧
        charAt cs j.val = q.val ∧ j.val = i.val + body.length ∧ ValueText q.val body out ∧
        word t = word text ++ out) ∧
      (∀ body out rest, (word cs).drop i.val = body ++ q.val :: rest → ValueText q.val body out →
        (∀ c ∈ body, c ≠ 0) → text.val.length + body.length ≤ Usize.max →
        ∃ t j, r = .Ok (t, j) ∧ word t = word text ++ out ∧ j.val = i.val + body.length) := by
  rw [xml.entity_value]
  simp only [at_eq, bind_ok, atU_eq_iff]
  have q0 := quote_ne_zero hq
  -- the first character read by a derivation
  have headOf : ∀ body out rest, (word cs).drop i.val = body ++ q.val :: rest → ValueText q.val body out →
      (body = [] ∧ charAt cs i.val = q.val) ∨
      (∃ c t, body = c :: t ∧ charAt cs i.val = c ∧ c ≠ q.val ∧ c ≠ 37 ∧ c ≠ 38) ∨
      (∃ w x t, body = w ++ t ∧ ValueRef w x ∧ charAt cs i.val = 38) := by
    intro body out rest split hv
    cases hv with
    | nil => exact Or.inl ⟨rfl, first_char (by simpa using split)⟩
    | @char c t o hc h37 h38 _ =>
      exact Or.inr (Or.inl ⟨c, t, rfl, first_char (rest := t ++ q.val :: rest) (by rw [split]; simp), hc, h37, h38⟩)
    | @charRef r v t o hr hx _ =>
      obtain ⟨u, hu⟩ := charRef_head hr
      exact Or.inr (Or.inr ⟨r, [v], t, rfl, Or.inl ⟨v, hr, hx, rfl⟩,
        first_char (rest := u ++ t ++ q.val :: rest) (by rw [split, hu]; simp)⟩)
    | @entityRef r ename t o hr _ =>
      obtain ⟨u, hu⟩ := entityRef_head hr
      exact Or.inr (Or.inr ⟨r, r, t, rfl, Or.inr ⟨ename, hr, rfl⟩,
        first_char (rest := u ++ t ++ q.val :: rest) (by rw [split, hu]; simp)⟩)
  by_cases eq : charAt cs i.val = q.val
  · refine ⟨.Ok (text, i), by simp [eq], ?_, ?_⟩
    · intro t j e; simp at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨[], [], by simp, eq, by simp, ValueText.nil, by simp⟩
    · intro body out rest split hv nz room
      rcases headOf body out rest split hv with ⟨rfl, _⟩ | ⟨c, t, _, hc, hcq, _, _⟩ | ⟨w, x, t, _, _, h38⟩
      · rw [valueText_nil hv]; exact ⟨text, i, rfl, by simp, by simp⟩
      · exact absurd (hc.symm.trans eq) hcq
      · exact absurd (h38.symm.trans eq) (Ne.symm (quote_ne_38 hq))
  · by_cases z : charAt cs i.val = 0
    · refine ⟨.Err ⟨.UnexpectedEnd, i⟩, by simp [eq, z, q0, Ne.symm q0, xml.fail], by simp, ?_⟩
      intro body out rest split hv nz _
      exfalso
      rcases headOf body out rest split hv with ⟨_, h⟩ | ⟨c, t, rfl, hc, _⟩ | ⟨w, x, t, _, _, h38⟩
      · exact eq h
      · exact nz c (by simp) (hc.symm.trans z)
      · rw [z] at h38; simp at h38
    · obtain ⟨inside, hd⟩ := drop_nonzero z
      by_cases pc : charAt cs i.val = 37
      · refine ⟨.Err ⟨.UnsupportedDeclaration, i⟩, by simp [eq, z, pc, xml.fail, Ne.symm (quote_ne_37 hq)],
          by simp, ?_⟩
        intro body out rest split hv nz _
        exfalso
        rcases headOf body out rest split hv with ⟨_, h⟩ | ⟨c, t, _, hc, _, h37, _⟩ | ⟨w, x, t, _, _, h38⟩
        · exact eq h
        · exact h37 (hc.symm.trans pc)
        · rw [pc] at h38; simp at h38
      · by_cases amp : charAt cs i.val = 38
        · obtain ⟨r1, h1, sound1, complete1⟩ := value_reference_spec cs i text amp
          -- a complete reading begins with a reference
          have refOf : ∀ body out rest, (word cs).drop i.val = body ++ q.val :: rest → ValueText q.val body out →
              ∃ w x t o, body = w ++ t ∧ out = x ++ o ∧ ValueRef w x ∧ ValueText q.val t o := by
            intro body out rest split hv
            cases hv with
            | nil => exact absurd (first_char (by simpa using split)) eq
            | @char c t o hc _ h38 _ =>
              exact absurd ((first_char (rest := t ++ q.val :: rest) (by rw [split]; simp)).symm.trans amp) h38
            | @charRef r v t o hr hx ht => exact ⟨r, [v], t, o, rfl, rfl, Or.inl ⟨v, hr, hx, rfl⟩, ht⟩
            | @entityRef r ename t o hr ht => exact ⟨r, r, t, o, rfl, rfl, Or.inr ⟨ename, hr, rfl⟩, ht⟩
          cases r1 with
          | Err err =>
            refine ⟨.Err err, by simp [eq, z, pc, amp, h1, core.result.Result.Insts.CoreOpsTry.branch,
              same_residual, Ne.symm (quote_ne_38 hq)], by simp, ?_⟩
            intro body out rest split hv nz room
            obtain ⟨w, x, t, o, rfl, rfl, hw, _⟩ := refOf body out rest split hv
            obtain ⟨t', j', hr', _⟩ := complete1 w x (t ++ q.val :: rest) (by rw [split]; simp) hw (by simp at room; omega)
            cases hr'
          | Ok pair =>
            obtain ⟨text1, j1⟩ := pair
            obtain ⟨w1, x1, wsplit, hj1, hw1, ht1⟩ := sound1 text1 j1 rfl
            have wpos := (valueRef_len hw1).2
            have progress : cs.val.length - j1.val < cs.val.length - i.val := by
              apply drop_lt wsplit; intro e; rw [e] at wpos; simp at wpos
            obtain ⟨r2, h2, sound2, complete2⟩ := entity_value_spec cs j1 q hq text1
            refine ⟨r2, by simp [eq, z, pc, amp, h1, core.result.Result.Insts.CoreOpsTry.branch, h2,
              Ne.symm (quote_ne_38 hq)], ?_, ?_⟩
            · intro t j e
              obtain ⟨body, out, bsplit, hjq, hj, hv, ht⟩ := sound2 t j e
              refine ⟨w1 ++ body, x1 ++ out, by rw [wsplit, bsplit]; simp, hjq, by rw [hj, hj1]; simp; omega, ?_,
                by rw [ht, ht1]; simp⟩
              rcases hw1 with ⟨v, hr, hx, rfl⟩ | ⟨ename, hr, rfl⟩
              · exact ValueText.charRef hr hx hv
              · exact ValueText.entityRef hr hv
            · intro body out rest split hv nz room
              obtain ⟨w, x, t, o, rfl, rfl, hw, ht⟩ := refOf body out rest split hv
              obtain ⟨t', j', hr', ht', hj'⟩ := complete1 w x (t ++ q.val :: rest) (by rw [split]; simp) hw
                (by simp at room; omega)
              simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at hr'
              obtain ⟨rfl, rfl⟩ := hr'
              have dj : (word cs).drop j1.val = t ++ q.val :: rest := by
                rw [hj']; have := drop_after (cs := cs) (i := i.val) (w := w) (rest := t ++ q.val :: rest)
                  (by rw [split]; simp)
                exact this
              have xl := (valueRef_len hw).1
              have tl : text1.val.length = text.val.length + x.length := by
                rw [← word_length, ht', List.length_append, word_length]
              obtain ⟨t2, j2, h2', ht2, hj2⟩ := complete2 t o rest dj ht (fun c hc => nz c (by simp [hc]))
                (by simp at room; omega)
              exact ⟨t2, j2, h2', by rw [ht2, ht']; simp, by rw [hj2, hj']; simp; omega⟩
        · -- a plain character
          obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
          have charOf : ∀ body out rest, (word cs).drop i.val = body ++ q.val :: rest → ValueText q.val body out →
              ∃ t o, body = charAt cs i.val :: t ∧ out = charAt cs i.val :: o ∧ ValueText q.val t o := by
            intro body out rest split hv
            cases hv with
            | nil => exact absurd (first_char (by simpa using split)) eq
            | @char c t o hc _ _ ht =>
              have := first_char (c := c) (rest := t ++ q.val :: rest) (by rw [split]; simp)
              rw [this]; exact ⟨t, o, rfl, rfl, ht⟩
            | @charRef r v t o hr _ _ =>
              obtain ⟨u, hu⟩ := charRef_head hr
              exact absurd (first_char (rest := u ++ t ++ q.val :: rest) (by rw [split, hu]; simp)) amp
            | @entityRef r ename t o hr _ =>
              obtain ⟨u, hu⟩ := entityRef_head hr
              exact absurd (first_char (rest := u ++ t ++ q.val :: rest) (by rw [split, hu]; simp)) amp
          by_cases room : text.val.length < Usize.max
          · obtain ⟨r2, h2, sound2, complete2⟩ := entity_value_spec cs i1 q hq
              (alloc.vec.Vec.from (text.val ++ [atU cs i.val]) (by simp; omega))
            refine ⟨r2, by simp [eq, z, pc, amp, push_char_eq, room, core.result.Result.Insts.CoreOpsTry.branch,
              hi1, h2], ?_, ?_⟩
            · intro t j e
              obtain ⟨body, out, bsplit, hjq, hj, hv, ht⟩ := sound2 t j e
              refine ⟨charAt cs i.val :: body, charAt cs i.val :: out, by rw [hd, ← hi1v, bsplit]; simp, hjq,
                by rw [hj, hi1v]; simp; omega, ValueText.char eq pc amp hv, ?_⟩
              rw [ht, word_push, atU_val]; simp
            · intro body out rest split hv nz room'
              obtain ⟨t, o, rfl, rfl, ht⟩ := charOf body out rest split hv
              have d1 : (word cs).drop i1.val = t ++ q.val :: rest := by
                rw [hd] at split; simp at split; rw [hi1v]; exact split
              obtain ⟨t2, j2, h2', ht2, hj2⟩ := complete2 t o rest d1 ht (fun c hc => nz c (by simp [hc]))
                (by simp at room' ⊢; omega)
              refine ⟨t2, j2, h2', by rw [ht2, word_push, atU_val]; simp, by rw [hj2, hi1v]; simp; omega⟩
          · refine ⟨.Err ⟨.ResourceLimit, i⟩, by simp [eq, z, pc, amp, push_char_eq, room,
              core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
            intro body out rest split hv _ room'
            exfalso; apply room
            obtain ⟨t, o, rfl, _, _⟩ := charOf body out rest split hv
            simp at room'; omega
termination_by cs.val.length - i.val
decreasing_by all_goals omega

end Rowl.XmlEntityDecls
