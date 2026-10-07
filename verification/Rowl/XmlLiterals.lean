import Rowl.XmlDecl

/-!
# Literals and external identifiers

`system_literal`, `pubid_literal` and `external_id` read the grammar's
`SystemLiteral`, `PubidLiteral` and `ExternalID`.
-/

namespace Rowl.XmlLiterals
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs Rowl.XmlEntities Rowl.XmlAttributes Rowl.XmlTags Rowl.XmlNamespaces Rowl.XmlContent Rowl.XmlElements Rowl.XmlComplete Rowl.XmlDecl
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

theorem lit_system : lit "SYSTEM" = [83, 89, 83, 84, 69, 77] := by decide
theorem lit_public : lit "PUBLIC" = [80, 85, 66, 76, 73, 67] := by decide
theorem map_system : ([83#u8, 89#u8, 83#u8, 84#u8, 69#u8, 77#u8] : List U8).map (·.val) = lit "SYSTEM" := by decide
theorem map_public : ([80#u8, 85#u8, 66#u8, 76#u8, 73#u8, 67#u8] : List U8).map (·.val) = lit "PUBLIC" := by decide

/-- The word up to the first `q` from `i`. -/
theorem literal_end_spec (cs : alloc.vec.Vec U32) (i : Usize) (q : U32) (hq0 : q.val ≠ 0) :
    ∃ r, xml.literal_end cs i q = .ok r ∧
      (∀ j, r = .Ok j → ∃ body, (word cs).drop i.val = body ++ q.val :: (word cs).drop j.val ∧ q.val ∉ body ∧
        j.val = i.val + body.length + 1) ∧
      (∀ body rest, (word cs).drop i.val = body ++ q.val :: rest → q.val ∉ body → (∀ c ∈ body, c ≠ 0) →
        ∃ j, r = .Ok j) := by
  rw [xml.literal_end]
  simp only [at_eq, bind_ok, atU_eq_iff]
  by_cases eq : charAt cs i.val = q.val
  · obtain ⟨inside, hd⟩ := drop_nonzero (by rw [eq]; exact hq0)
    obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
    refine ⟨.Ok i1, by simp [eq, hi1], ?_, fun _ _ _ _ _ => ⟨i1, rfl⟩⟩
    intro j e; simp at e; subst e
    exact ⟨[], by rw [hd, eq, hi1v]; simp, by simp, by simp [hi1v]⟩
  · by_cases z : charAt cs i.val = 0
    · refine ⟨.Err ⟨.UnexpectedEnd, i⟩, by simp [eq, z, hq0, Ne.symm hq0, xml.fail], by simp, ?_⟩
      intro body rest split _ nz
      exfalso
      cases body with
      | nil => exact eq (first_char (by simpa using split))
      | cons c b' => exact nz c (by simp) ((first_char (rest := b' ++ q.val :: rest) (by simpa using split)).symm.trans z)
    · obtain ⟨inside, hd⟩ := drop_nonzero z
      obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
      obtain ⟨r, hr, sound, complete⟩ := literal_end_spec cs i1 q hq0
      refine ⟨r, by simp [eq, z, hi1, hr], ?_, ?_⟩
      · intro j e
        obtain ⟨body, split, notin, hj⟩ := sound j e
        refine ⟨charAt cs i.val :: body, by rw [hd, ← hi1v, split]; simp, ?_, by rw [hj, hi1v]; simp; omega⟩
        simp only [List.mem_cons, not_or]; exact ⟨fun h => eq h.symm, notin⟩
      · intro body rest split notin nz
        cases body with
        | nil => exact absurd (first_char (by simpa using split)) eq
        | cons c b' =>
          rw [hd] at split; simp at split
          exact complete b' rest (by rw [hi1v]; exact split.2) (fun m => notin (by simp [m]))
            (fun d hd' => nz d (by simp [hd']))
termination_by cs.val.length - i.val
decreasing_by omega

theorem system_literal_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.system_literal cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ l, (word cs).drop i.val = l ++ (word cs).drop j.val ∧ SystemLiteral l ∧
        j.val = i.val + l.length) ∧
      (∀ l rest, (word cs).drop i.val = l ++ rest → SystemLiteral l → (∀ c ∈ l, c ≠ 0) →
        ∃ j, r = .Ok j ∧ j.val = i.val + l.length) := by
  unfold xml.system_literal
  simp only [at_eq, bind_ok, quote_eq, atU_val]
  by_cases hq : Quote (charAt cs i.val)
  · obtain ⟨inside, hd⟩ := drop_nonzero (quote_ne_zero hq)
    obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
    have qv : (atU cs i.val).val = charAt cs i.val := atU_val cs i.val
    obtain ⟨r, hr, sound, complete⟩ := literal_end_spec cs i1 (atU cs i.val) (by rw [qv]; exact quote_ne_zero hq)
    rw [qv] at sound complete
    refine ⟨r, by simp [hq, hi1, hr], ?_, ?_⟩
    · intro j e
      obtain ⟨body, split, notin, hj⟩ := sound j e
      refine ⟨charAt cs i.val :: body ++ [charAt cs i.val], ?_, ⟨_, body, hq, rfl, notin⟩, by rw [hj, hi1v]; simp; omega⟩
      rw [hd, ← hi1v, split]; simp
    · intro l rest split hl nz
      obtain ⟨q, body, hq', rfl, notin⟩ := hl
      have cq : charAt cs i.val = q := first_char (rest := body ++ [q] ++ rest) (by rw [split]; simp)
      subst cq
      have d1 : (word cs).drop i1.val = body ++ charAt cs i.val :: rest := by
        rw [hd] at split; simp at split; rw [hi1v]; exact split
      obtain ⟨j, hj⟩ := complete body rest d1 notin (fun c hc => nz c (by simp [hc]))
      refine ⟨j, hj, ?_⟩
      obtain ⟨body', split', notin', hjv⟩ := sound j hj
      have bb : body' = body := quoted_unique (fun c hc e => notin' (by rw [← e]; exact hc))
        (fun c hc e => notin (by rw [← e]; exact hc)) (split'.symm.trans d1)
      subst bb
      rw [hjv, hi1v]; simp; omega
  · refine ⟨.Err ⟨.Syntax, i⟩, by simp [hq, xml.fail], by simp, ?_⟩
    intro l rest split hl _
    obtain ⟨q, body, hq', rfl, _⟩ := hl
    exact absurd (by rw [first_char (c := q) (rest := body ++ [q] ++ rest) (by rw [split]; simp)]; exact hq') hq

theorem lit_pubid_punct :
    lit "-'()+,./:=?;!*#@$_%" = [45, 39, 40, 41, 43, 44, 46, 47, 58, 61, 63, 59, 33, 42, 35, 64, 36, 95, 37] := by
  decide

theorem pubid_char_eq (c : U32) : xml.pubid_char c = .ok (decide (PubidChar c.val)) := by
  simp only [xml.pubid_char, ascii_letter_eq, digit_eq, bind_ok]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [PubidChar, lit_pubid_punct, AsciiLetter, IsDigit, List.mem_cons, List.not_mem_nil, or_false,
    Bool.or_eq_true, decide_eq_true_eq, UScalar.eq_equiv]
  constructor <;> intro h <;> simp at h ⊢ <;> omega

theorem pubid_not_zero : ¬ PubidChar 0 := by
  simp [PubidChar, lit_pubid_punct, IsDigit]

theorem pubid_end_spec (cs : alloc.vec.Vec U32) (i : Usize) (q : U32) (hq0 : q.val ≠ 0) :
    ∃ r, xml.pubid_end cs i q = .ok r ∧
      (∀ j, r = .Ok j → ∃ body, (word cs).drop i.val = body ++ q.val :: (word cs).drop j.val ∧
        (∀ c ∈ body, PubidChar c ∧ c ≠ q.val) ∧ j.val = i.val + body.length + 1) ∧
      (∀ body rest, (word cs).drop i.val = body ++ q.val :: rest → (∀ c ∈ body, PubidChar c ∧ c ≠ q.val) →
        ∃ j, r = .Ok j) := by
  rw [xml.pubid_end]
  simp only [at_eq, bind_ok, atU_eq_iff, pubid_char_eq, atU_val]
  by_cases eq : charAt cs i.val = q.val
  · obtain ⟨inside, hd⟩ := drop_nonzero (by rw [eq]; exact hq0)
    obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
    refine ⟨.Ok i1, by simp [eq, hi1], ?_, fun _ _ _ _ => ⟨i1, rfl⟩⟩
    intro j e; simp at e; subst e
    exact ⟨[], by rw [hd, eq, hi1v]; simp, by simp, by simp [hi1v]⟩
  · by_cases pc : PubidChar (charAt cs i.val)
    · have nz : charAt cs i.val ≠ 0 := fun z => pubid_not_zero (z ▸ pc)
      obtain ⟨inside, hd⟩ := drop_nonzero nz
      obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
      obtain ⟨r, hr, sound, complete⟩ := pubid_end_spec cs i1 q hq0
      refine ⟨r, by simp [eq, pc, hi1, hr], ?_, ?_⟩
      · intro j e
        obtain ⟨body, split, all, hj⟩ := sound j e
        refine ⟨charAt cs i.val :: body, by rw [hd, ← hi1v, split]; simp, ?_, by rw [hj, hi1v]; simp; omega⟩
        intro c hc; simp at hc; rcases hc with rfl | m
        · exact ⟨pc, eq⟩
        · exact all c m
      · intro body rest split all
        cases body with
        | nil => exact absurd (first_char (by simpa using split)) eq
        | cons c b' =>
          rw [hd] at split; simp at split
          exact complete b' rest (by rw [hi1v]; exact split.2) (fun d hd' => all d (by simp [hd']))
    · refine ⟨.Err ⟨.Syntax, i⟩, by simp [eq, pc, xml.fail], by simp, ?_⟩
      intro body rest split all
      exfalso
      cases body with
      | nil => exact eq (first_char (by simpa using split))
      | cons c b' =>
        have := first_char (rest := b' ++ q.val :: rest) (by simpa using split)
        exact pc (by rw [this]; exact (all c (by simp)).1)
termination_by cs.val.length - i.val
decreasing_by omega

theorem pubid_literal_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.pubid_literal cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ l, (word cs).drop i.val = l ++ (word cs).drop j.val ∧ PubidLiteral l ∧
        j.val = i.val + l.length) ∧
      (∀ l rest, (word cs).drop i.val = l ++ rest → PubidLiteral l → ∃ j, r = .Ok j ∧ j.val = i.val + l.length) := by
  unfold xml.pubid_literal
  simp only [at_eq, bind_ok, quote_eq, atU_val]
  by_cases hq : Quote (charAt cs i.val)
  · obtain ⟨inside, hd⟩ := drop_nonzero (quote_ne_zero hq)
    obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
    have qv : (atU cs i.val).val = charAt cs i.val := atU_val cs i.val
    obtain ⟨r, hr, sound, complete⟩ := pubid_end_spec cs i1 (atU cs i.val) (by rw [qv]; exact quote_ne_zero hq)
    rw [qv] at sound complete
    refine ⟨r, by simp [hq, hi1, hr], ?_, ?_⟩
    · intro j e
      obtain ⟨body, split, all, hj⟩ := sound j e
      refine ⟨charAt cs i.val :: body ++ [charAt cs i.val], ?_, ⟨_, body, hq, rfl, all⟩, by rw [hj, hi1v]; simp; omega⟩
      rw [hd, ← hi1v, split]; simp
    · intro l rest split hl
      obtain ⟨q, body, hq', rfl, all⟩ := hl
      have cq : charAt cs i.val = q := first_char (rest := body ++ [q] ++ rest) (by rw [split]; simp)
      subst cq
      have d1 : (word cs).drop i1.val = body ++ charAt cs i.val :: rest := by
        rw [hd] at split; simp at split; rw [hi1v]; exact split
      obtain ⟨j, hj⟩ := complete body rest d1 all
      refine ⟨j, hj, ?_⟩
      obtain ⟨body', split', all', hjv⟩ := sound j hj
      have bb : body' = body := quoted_unique (fun c hc => (all' c hc).2) (fun c hc => (all c hc).2)
        (split'.symm.trans d1)
      subst bb
      rw [hjv, hi1v]; simp; omega
  · refine ⟨.Err ⟨.Syntax, i⟩, by simp [hq, xml.fail], by simp, ?_⟩
    intro l rest split hl
    obtain ⟨q, body, hq', rfl, _⟩ := hl
    exact absurd (by rw [first_char (c := q) (rest := body ++ [q] ++ rest) (by rw [split]; simp)]; exact hq') hq

/-! ## White space that must be there -/

theorem spaces_sound (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.spaces cs i = .ok r ∧
      ∀ j, r = .Ok j → ∃ s, (word cs).drop i.val = s ++ (word cs).drop j.val ∧ S s ∧ j.val = i.val + s.length := by
  obtain ⟨r, hr, c⟩ := spaces_spec cs i
  refine ⟨r, hr, ?_⟩
  intro j e; subst e
  obtain ⟨sp, hj⟩ := c
  have split := drop_run IsSpace cs i.val
  rw [← hj] at split
  refine ⟨_, split, ⟨?_, run_all⟩, hj⟩
  have := (run_step cs i.val sp not_space_zero).2
  intro e; rw [e] at this; simp at this

theorem spaces_complete (cs : alloc.vec.Vec U32) (i : Usize) {s rest : Word} (split : (word cs).drop i.val = s ++ rest)
    (hs : S s) (stop : ∀ c m, rest = c :: m → ¬ IsSpace c) :
    ∃ j, xml.spaces cs i = .ok (.Ok j) ∧ j.val = i.val + s.length := by
  obtain ⟨r, hr, c⟩ := spaces_spec cs i
  obtain ⟨c0, s', hs'⟩ := List.exists_cons_of_ne_nil hs.1
  have first : charAt cs i.val = c0 := first_char (rest := s' ++ rest) (by rw [split, hs']; simp)
  have sp0 : IsSpace (charAt cs i.val) := by rw [first]; exact hs.2 c0 (by rw [hs']; simp)
  cases r with
  | Err err => exact absurd sp0 c
  | Ok j =>
    refine ⟨j, hr, ?_⟩
    rw [c.2, split, run_unique hs.2 stop]

theorem system_not_public {w : Word} (h1 : lit "SYSTEM" <+: w) (h2 : lit "PUBLIC" <+: w) : False := by
  obtain ⟨t1, e1⟩ := h1; obtain ⟨t2, e2⟩ := h2
  rw [← e2, lit_system, lit_public] at e1; simp at e1

theorem external_head {e : Word} (h : ExternalID e) : lit "SYSTEM" <+: e ∨ lit "PUBLIC" <+: e := by
  rcases h with ⟨s, l, rfl, _⟩ | ⟨s1, p, s2, l, rfl, _⟩
  · left; exact ⟨s ++ l, by simp⟩
  · right; exact ⟨s1 ++ p ++ s2 ++ l, by simp⟩

theorem systemLiteral_head {l : Word} (h : SystemLiteral l) : ∀ c m, l = c :: m → ¬ IsSpace c := by
  obtain ⟨q, body, hq, rfl, _⟩ := h
  intro c m e; simp at e; rw [← e.1]; exact quote_not_space hq

theorem pubidLiteral_head {l : Word} (h : PubidLiteral l) : ∀ c m, l = c :: m → ¬ IsSpace c := by
  obtain ⟨q, body, hq, rfl, _⟩ := h
  intro c m e; simp at e; rw [← e.1]; exact quote_not_space hq

theorem head_append {l rest : Word} (h : ∀ c m, l = c :: m → ¬ IsSpace c) (hne : l ≠ []) :
    ∀ c m, l ++ rest = c :: m → ¬ IsSpace c := by
  intro c m e
  obtain ⟨c0, l', rfl⟩ := List.exists_cons_of_ne_nil hne
  simp at e; rw [← e.1]; exact h c0 l' rfl

theorem systemLiteral_ne {l : Word} (h : SystemLiteral l) : l ≠ [] := by
  obtain ⟨q, body, _, rfl, _⟩ := h; simp

theorem pubidLiteral_ne {l : Word} (h : PubidLiteral l) : l ≠ [] := by
  obtain ⟨q, body, _, rfl, _⟩ := h; simp

/-- A step that fails cannot also succeed. -/
theorem ok_ne_err {α : Type} {f : Result (core.result.Result α xml.XmlError)} {a : α} {err : xml.XmlError}
    (h1 : f = .ok (.Err err)) (h2 : f = .ok (.Ok a)) : False := by
  rw [h1] at h2; simp at h2

theorem ok_inj {α : Type} {f : Result (core.result.Result α xml.XmlError)} {a b : α}
    (h1 : f = .ok (.Ok a)) (h2 : f = .ok (.Ok b)) : a = b := by
  rw [h1] at h2; simpa using h2

theorem external_id_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.external_id cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ e, (word cs).drop i.val = e ++ (word cs).drop j.val ∧ ExternalID e ∧
        j.val = i.val + e.length) ∧
      (∀ e rest, (word cs).drop i.val = e ++ rest → ExternalID e → (∀ c ∈ e, c ≠ 0) →
        ∃ j, r = .Ok j ∧ j.val = i.val + e.length) := by
  unfold xml.external_id
  simp only [lift, bind_ok, starts_eq, bytes_make, map_system, map_public, decide_eq_true_eq]
  by_cases sys : lit "SYSTEM" <+: (word cs).drop i.val
  · rw [if_pos sys]
    obtain ⟨d6, fit6⟩ := prefix_split sys (by rw [lit_system]; simp)
    have l6 : (lit "SYSTEM").length = 6 := by rw [lit_system]; rfl
    rw [l6] at d6 fit6
    obtain ⟨i6, hi6, hi6v⟩ := skip_spec (cs := cs) (i := i) (c := 6#usize) (by simp; omega)
    have i6v : i6.val = i.val + 6 := by simpa using hi6v
    rw [← i6v] at d6
    obtain ⟨r1, h1, s1⟩ := spaces_sound cs i6
    -- what a complete reading gives after `SYSTEM`
    have parts : ∀ e rest, (word cs).drop i.val = e ++ rest → ExternalID e → ∃ s l,
        (word cs).drop i6.val = s ++ (l ++ rest) ∧ S s ∧ SystemLiteral l ∧ e = lit "SYSTEM" ++ s ++ l := by
      intro e rest split he
      rcases he with ⟨s, l, rfl, hs, hl⟩ | ⟨s1, p, s2, l, rfl, _⟩
      · refine ⟨s, l, ?_, hs, hl, rfl⟩
        rw [i6v]; have := drop_after (cs := cs) (i := i.val) (w := lit "SYSTEM") (rest := s ++ (l ++ rest))
          (by rw [split]; simp)
        rw [l6] at this; exact this
      · exfalso; exact system_not_public sys (by rw [split]; exact ⟨s1 ++ p ++ s2 ++ l ++ rest, by simp⟩)
    have afterS : ∀ e rest, (word cs).drop i.val = e ++ rest → ExternalID e → ∃ s l j',
        xml.spaces cs i6 = .ok (.Ok j') ∧ j'.val = i6.val + s.length ∧ (word cs).drop j'.val = l ++ rest ∧
        SystemLiteral l ∧ e = lit "SYSTEM" ++ s ++ l := by
      intro e rest split he
      obtain ⟨s, l, d, hs, hl, he'⟩ := parts e rest split he
      obtain ⟨j', hj', hj'v⟩ := spaces_complete cs i6 d hs (head_append (systemLiteral_head hl) (systemLiteral_ne hl))
      refine ⟨s, l, j', hj', hj'v, ?_, hl, he'⟩
      rw [hj'v]; exact drop_after d
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [hi6, h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
      intro e rest split he nz
      obtain ⟨s, l, j', hj', _⟩ := afterS e rest split he
      exact (ok_ne_err h1 hj').elim
    | Ok j1 =>
      obtain ⟨sp, ssplit, hsp, hj1⟩ := s1 j1 rfl
      obtain ⟨r2, h2, s2, c2⟩ := system_literal_spec cs j1
      refine ⟨r2, by simp [hi6, h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_, ?_⟩
      · intro j e
        obtain ⟨l, lsplit, hl, hj⟩ := s2 j e
        refine ⟨lit "SYSTEM" ++ sp ++ l, by rw [d6, ssplit, lsplit]; simp, Or.inl ⟨sp, l, rfl, hsp, hl⟩, ?_⟩
        rw [hj, hj1, i6v]; simp [lit_system]; omega
      · intro e rest split he nz
        obtain ⟨s, l, j', hj', hj'v, dl, hl, rfl⟩ := afterS e rest split he
        have := ok_inj h1 hj'
        subst this
        obtain ⟨j, hj, hjv⟩ := c2 l rest dl hl (fun c hc => nz c (by simp [hc]))
        refine ⟨j, hj, ?_⟩
        rw [hjv, hj'v, i6v]; simp [lit_system]; omega
  · rw [if_neg sys]
    by_cases pub : lit "PUBLIC" <+: (word cs).drop i.val
    · rw [if_pos pub]
      obtain ⟨d6, fit6⟩ := prefix_split pub (by rw [lit_public]; simp)
      have l6 : (lit "PUBLIC").length = 6 := by rw [lit_public]; rfl
      rw [l6] at d6 fit6
      obtain ⟨i6, hi6, hi6v⟩ := skip_spec (cs := cs) (i := i) (c := 6#usize) (by simp; omega)
      have i6v : i6.val = i.val + 6 := by simpa using hi6v
      rw [← i6v] at d6
      have parts : ∀ e rest, (word cs).drop i.val = e ++ rest → ExternalID e → ∃ s1 p s2 l,
          (word cs).drop i6.val = s1 ++ (p ++ (s2 ++ (l ++ rest))) ∧ S s1 ∧ PubidLiteral p ∧ S s2 ∧
          SystemLiteral l ∧ e = lit "PUBLIC" ++ s1 ++ p ++ s2 ++ l := by
        intro e rest split he
        rcases he with ⟨s, l, rfl, _⟩ | ⟨s1, p, s2, l, rfl, hs1, hp, hs2, hl⟩
        · exfalso; exact sys (by rw [split]; exact ⟨s ++ l ++ rest, by simp⟩)
        · refine ⟨s1, p, s2, l, ?_, hs1, hp, hs2, hl, rfl⟩
          rw [i6v]; have := drop_after (cs := cs) (i := i.val) (w := lit "PUBLIC")
            (rest := s1 ++ (p ++ (s2 ++ (l ++ rest)))) (by rw [split]; simp)
          rw [l6] at this; exact this
      obtain ⟨r1, h1, s1⟩ := spaces_sound cs i6
      cases r1 with
      | Err err =>
        refine ⟨.Err err, by simp [hi6, h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
        intro e rest split he nz
        obtain ⟨s1, p, s2, l, d, hs1, hp, _, _, _⟩ := parts e rest split he
        obtain ⟨j', hj', _⟩ := spaces_complete cs i6 d hs1 (head_append (pubidLiteral_head hp) (pubidLiteral_ne hp))
        exact (ok_ne_err h1 hj').elim
      | Ok j1 =>
        obtain ⟨sp, ssplit, hsp, hj1⟩ := s1 j1 rfl
        have at1 : ∀ e rest, (word cs).drop i.val = e ++ rest → ExternalID e → ∃ s1 p s2 l,
            (word cs).drop j1.val = p ++ (s2 ++ (l ++ rest)) ∧ PubidLiteral p ∧ S s2 ∧ SystemLiteral l ∧
            e = lit "PUBLIC" ++ s1 ++ p ++ s2 ++ l ∧ j1.val = i6.val + s1.length := by
          intro e rest split he
          obtain ⟨s1, p, s2, l, d, hs1, hp, hs2, hl, he'⟩ := parts e rest split he
          obtain ⟨j', hj', hj'v⟩ := spaces_complete cs i6 d hs1
            (head_append (pubidLiteral_head hp) (pubidLiteral_ne hp))
          have := ok_inj h1 hj'; subst this
          exact ⟨s1, p, s2, l, by rw [hj'v]; exact drop_after d, hp, hs2, hl, he', hj'v⟩
        obtain ⟨r2, h2, s2', c2⟩ := pubid_literal_spec cs j1
        cases r2 with
        | Err err =>
          refine ⟨.Err err, by simp [hi6, h1, h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
            by simp, ?_⟩
          intro e rest split he nz
          obtain ⟨s1, p, s2, l, d1, hp, _, _, _, _⟩ := at1 e rest split he
          obtain ⟨k, hk, _⟩ := c2 p _ d1 hp
          cases hk
        | Ok k1 =>
          obtain ⟨pl, psplit, hpl, hk1⟩ := s2' k1 rfl
          have at2 : ∀ e rest, (word cs).drop i.val = e ++ rest → ExternalID e → ∃ s1 p s2 l,
              (word cs).drop k1.val = s2 ++ (l ++ rest) ∧ S s2 ∧ SystemLiteral l ∧
              e = lit "PUBLIC" ++ s1 ++ p ++ s2 ++ l ∧ k1.val = i6.val + s1.length + p.length := by
            intro e rest split he
            obtain ⟨s1, p, s2, l, d1, hp, hs2, hl, he', hj1'⟩ := at1 e rest split he
            obtain ⟨k, hk, hkv⟩ := c2 p _ d1 hp
            simp only [core.result.Result.Ok.injEq] at hk; subst hk
            refine ⟨s1, p, s2, l, ?_, hs2, hl, he', by omega⟩
            rw [hkv]; exact drop_after d1
          obtain ⟨r3, h3, s3⟩ := spaces_sound cs k1
          cases r3 with
          | Err err =>
            refine ⟨.Err err, by simp [hi6, h1, h2, h3, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
              by simp, ?_⟩
            intro e rest split he nz
            obtain ⟨s1, p, s2, l, d2, hs2, hl, _, _⟩ := at2 e rest split he
            obtain ⟨m, hm, _⟩ := spaces_complete cs k1 d2 hs2 (head_append (systemLiteral_head hl) (systemLiteral_ne hl))
            exact (ok_ne_err h3 hm).elim
          | Ok m1 =>
            obtain ⟨sp2, s2split, hsp2, hm1⟩ := s3 m1 rfl
            obtain ⟨r4, h4, s4, c4⟩ := system_literal_spec cs m1
            refine ⟨r4, by simp [hi6, h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch], ?_, ?_⟩
            · intro j e
              obtain ⟨l, lsplit, hl, hj⟩ := s4 j e
              refine ⟨lit "PUBLIC" ++ sp ++ pl ++ sp2 ++ l, by rw [d6, ssplit, psplit, s2split, lsplit]; simp,
                Or.inr ⟨sp, pl, sp2, l, rfl, hsp, hpl, hsp2, hl⟩, ?_⟩
              rw [hj, hm1, hk1, hj1, i6v]; simp [lit_public]; omega
            · intro e rest split he nz
              obtain ⟨s1, p, s2, l, d2, hs2, hl, rfl, hk1'⟩ := at2 e rest split he
              obtain ⟨m, hm, hmv⟩ := spaces_complete cs k1 d2 hs2
                (head_append (systemLiteral_head hl) (systemLiteral_ne hl))
              have em := ok_inj h3 hm
              rw [← em] at hmv
              have dl : (word cs).drop m1.val = l ++ rest := by rw [hmv]; exact drop_after d2
              obtain ⟨j, hj, hjv⟩ := c4 l rest dl hl (fun c hc => nz c (by simp [hc]))
              refine ⟨j, hj, ?_⟩
              rw [hjv, hmv, hk1', i6v]; simp [lit_public]; omega
    · rw [if_neg pub]
      refine ⟨.Err ⟨.Syntax, i⟩, by simp [xml.fail], by simp, ?_⟩
      intro e rest split he _
      exfalso
      rcases external_head he with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact sys (by rw [split, ← ht]; exact ⟨t ++ rest, by simp⟩)
      · exact pub (by rw [split, ← ht]; exact ⟨t ++ rest, by simp⟩)

end Rowl.XmlLiterals
