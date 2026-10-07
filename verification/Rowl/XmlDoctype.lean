import Rowl.XmlEntityDecls

/-!
# Entity declarations, the internal subset and the document type declaration

`entity_definition`, `general_declaration` and `parameter_declaration` read
the grammar's `EntityDef`, `GEDecl` and `PEDecl`; `internal_subset` reads
`intSubset` with the general entities it declares, and `doctype` reads
`doctypedecl`.
-/

namespace Rowl.XmlDoctype
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs Rowl.XmlEntities Rowl.XmlAttributes Rowl.XmlTags Rowl.XmlNamespaces Rowl.XmlContent Rowl.XmlElements Rowl.XmlComplete Rowl.XmlDecl Rowl.XmlLiterals Rowl.XmlEntityDecls
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

theorem lit_ndata : lit "NDATA" = [78, 68, 65, 84, 65] := by decide
theorem map_ndata : ([78#u8, 68#u8, 65#u8, 84#u8, 65#u8] : List U8).map (·.val) = lit "NDATA" := by decide

theorem ncname_sound (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.ncname cs i = .ok r ∧
      ∀ e, r = .Ok e → ∃ n, (word cs).drop i.val = n ++ (word cs).drop e.val ∧ NCName n ∧ e.val = i.val + n.length := by
  obtain ⟨r, hr, sound, _⟩ := ncname_spec cs i
  refine ⟨r, hr, fun e he => ?_⟩
  obtain ⟨he', ncn⟩ := sound e he
  exact ⟨nameRun cs i.val, by rw [he']; exact nameRun_split cs i.val, ncn, he'⟩

theorem ncname_complete (cs : alloc.vec.Vec U32) (i : Usize) {n rest : Word} (split : (word cs).drop i.val = n ++ rest)
    (hn : NCName n) (stop : ∀ c m, rest = c :: m → ¬ NameChar c) :
    ∃ e, xml.ncname cs i = .ok (.Ok e) ∧ e.val = i.val + n.length := by
  obtain ⟨r, hr, sound, complete⟩ := ncname_spec cs i
  have nr : nameRun cs i.val = n := nameRun_eq split (name_all hn.1) stop
  rw [nr] at sound complete
  obtain ⟨e, he⟩ := complete hn
  subst he
  exact ⟨e, hr, (sound e rfl).1⟩

theorem not_name_space {c : Nat} (h : IsSpace c) : ¬ NameChar c := space_not_name h
theorem not_name_gt : ¬ NameChar 62 := by simp [NameChar, NameStartChar]

theorem declaration_close_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.declaration_close cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ s, (word cs).drop i.val = s ++ 62 :: (word cs).drop j.val ∧ OptS s ∧
        j.val = i.val + s.length + 1) ∧
      (∀ s rest, (word cs).drop i.val = s ++ 62 :: rest → OptS s → ∃ j, r = .Ok j ∧ j.val = i.val + s.length + 1) := by
  unfold xml.declaration_close
  obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
  have split0 := drop_run IsSpace cs i.val
  rw [← h0v] at split0
  have all0 : ∀ c ∈ run IsSpace ((word cs).drop i.val), IsSpace c := run_all
  generalize hr0 : run IsSpace ((word cs).drop i.val) = sp at split0 h0v all0
  have reads : ∀ s rest, (word cs).drop i.val = s ++ 62 :: rest → OptS s → s = sp := by
    intro s rest split hs
    rw [← hr0, split]; exact (run_unique hs (head_not_space (q := 62) (by simp [IsSpace]))).symm
  simp only [h0, bind_ok, at_eq, atU_eq_iff]
  by_cases gt : charAt cs j0.val = 62
  · obtain ⟨inside, d1⟩ := drop_nonzero (by rw [gt]; decide : charAt cs j0.val ≠ 0)
    obtain ⟨j1, hj1, hj1v⟩ := next_spec inside
    refine ⟨.Ok j1, by simp [gt, hj1], ?_, ?_⟩
    · intro j e; simp at e; subst e
      exact ⟨sp, by rw [split0, d1, gt, hj1v], all0, by rw [hj1v, h0v]⟩
    · intro s rest split hs
      have := reads s rest split hs; subst this
      exact ⟨j1, rfl, by rw [hj1v, h0v]⟩
  · refine ⟨.Err ⟨.Syntax, j0⟩, by simp [gt, xml.fail], by simp, ?_⟩
    intro s rest split hs
    have := reads s rest split hs; subst this
    exfalso; apply gt
    rw [h0v]; have := charAt_after (rest := 62 :: rest) split; simpa using this

theorem ndata_follows_eq (cs : alloc.vec.Vec U32) (i j : Usize) :
    xml.ndata_follows cs i j = .ok (decide (i.val < j.val ∧ lit "NDATA" <+: (word cs).drop j.val)) := by
  simp [xml.ndata_follows, lift, starts_eq, bytes_make, map_ndata, UScalar.lt_equiv, lit_ndata]

theorem name_not_space {n : Word} (h : NCName n) : ∀ c m, n = c :: m → ¬ IsSpace c := by
  intro c m e
  obtain ⟨c0, r0, e0, hc0, _⟩ := h.1
  rw [e0] at e; simp at e; rw [← e.1]
  intro sp; exact space_not_name sp (Or.inl hc0)

theorem external_rest_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.external_rest cs i = .ok r ∧
      (∀ kind j, r = .Ok (kind, j) → (kind = .External ∧ j = i) ∨
        (kind = .Unparsed ∧ ∃ s1 s2 n, (word cs).drop i.val = s1 ++ lit "NDATA" ++ s2 ++ n ++ (word cs).drop j.val ∧
          S s1 ∧ S s2 ∧ NCName n ∧ j.val = i.val + s1.length + 5 + s2.length + n.length)) ∧
      (∀ s3 more, (word cs).drop i.val = s3 ++ 62 :: more → OptS s3 → r = .Ok (.External, i)) ∧
      (∀ s1 s2 n s3 more, (word cs).drop i.val = s1 ++ lit "NDATA" ++ s2 ++ n ++ s3 ++ 62 :: more → S s1 → S s2 →
        NCName n → OptS s3 → ∃ j, r = .Ok (.Unparsed, j) ∧ j.val = i.val + s1.length + 5 + s2.length + n.length) := by
  unfold xml.external_rest
  obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
  have split0 := drop_run IsSpace cs i.val
  rw [← h0v] at split0
  have all0 : ∀ c ∈ run IsSpace ((word cs).drop i.val), IsSpace c := run_all
  generalize hr0 : run IsSpace ((word cs).drop i.val) = sp at split0 h0v all0
  have kwHead : ∀ c t, lit "NDATA" = c :: t → ¬ IsSpace c := by
    rw [lit_ndata]; intro c t e; simp at e; rw [e.1]; simp [IsSpace]
  have reads := spaces_reading hr0 kwHead (by rw [lit_ndata]; simp)
  simp only [h0, bind_ok, ndata_follows_eq, decide_eq_true_eq]
  by_cases nd : i.val < j0.val ∧ lit "NDATA" <+: (word cs).drop j0.val
  · rw [if_pos nd]
    obtain ⟨d5, fit5⟩ := prefix_split nd.2 (by rw [lit_ndata]; simp)
    have l5 : (lit "NDATA").length = 5 := by rw [lit_ndata]; rfl
    rw [l5] at d5 fit5
    obtain ⟨k, hk, hkv⟩ := skip_spec (cs := cs) (i := j0) (c := 5#usize) (by simp; omega)
    have kv : k.val = j0.val + 5 := by simpa using hkv
    rw [← kv] at d5
    have spne : sp ≠ [] := by intro e; rw [e] at h0v; simp at h0v; omega
    have notExt : ∀ s3 more, (word cs).drop i.val = s3 ++ 62 :: more → OptS s3 → False := by
      intro s3 more split hs3
      have ss : s3 = sp := by
        rw [← hr0, split]; exact (run_unique hs3 (head_not_space (q := 62) (by simp [IsSpace]))).symm
      subst ss
      have dj : (word cs).drop j0.val = 62 :: more := by rw [h0v]; exact drop_after split
      rw [dj, lit_ndata] at nd; obtain ⟨_, ⟨t, ht⟩⟩ := nd; simp at ht
    -- what a complete reading gives after `NDATA`
    have atK : ∀ s1 s2 n s3 more, (word cs).drop i.val = s1 ++ lit "NDATA" ++ s2 ++ n ++ s3 ++ 62 :: more →
        S s1 → (word cs).drop k.val = s2 ++ (n ++ (s3 ++ 62 :: more)) ∧ s1 = sp := by
      intro s1 s2 n s3 more split hs1
      have ss : s1 = sp := reads s1 (s2 ++ n ++ s3 ++ 62 :: more) (by rw [split]; simp) hs1.2
      subst ss
      refine ⟨?_, rfl⟩
      rw [kv, h0v]
      have := drop_after (cs := cs) (i := i.val) (w := s1 ++ lit "NDATA") (rest := s2 ++ (n ++ (s3 ++ 62 :: more)))
        (by rw [split]; simp)
      simpa [l5, Nat.add_assoc] using this
    obtain ⟨r1, h1, s1'⟩ := spaces_sound cs k
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [hk, h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp,
        fun s3 more split hs3 => (notExt s3 more split hs3).elim, ?_⟩
      intro s1 s2 n s3 more split hs1 hs2 hn hs3
      obtain ⟨dk, _⟩ := atK s1 s2 n s3 more split hs1
      obtain ⟨m, hm, _⟩ := spaces_complete cs k dk hs2 (head_append (name_not_space hn) (by
        obtain ⟨c0, r0, e0, _⟩ := hn.1; rw [e0]; simp))
      exact (ok_ne_err h1 hm).elim
    | Ok m =>
      obtain ⟨sp2, s2split, hsp2, hm⟩ := s1' m rfl
      obtain ⟨r2, h2, s2'⟩ := ncname_sound cs m
      cases r2 with
      | Err err =>
        refine ⟨.Err err, by simp [hk, h1, h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp,
          fun s3 more split hs3 => (notExt s3 more split hs3).elim, ?_⟩
        intro s1 s2 n s3 more split hs1 hs2 hn hs3
        obtain ⟨dk, _⟩ := atK s1 s2 n s3 more split hs1
        obtain ⟨m', hm', hm'v⟩ := spaces_complete cs k dk hs2 (head_append (name_not_space hn) (by
          obtain ⟨c0, r0, e0, _⟩ := hn.1; rw [e0]; simp))
        have em := ok_inj h1 hm'
        rw [← em] at hm'v
        have dn : (word cs).drop m.val = n ++ (s3 ++ 62 :: more) := by rw [hm'v]; exact drop_after dk
        obtain ⟨e, he, _⟩ := ncname_complete cs m dn hn (by
          intro c t et
          cases s3 with
          | nil => simp at et; rw [et.1]; exact not_name_gt
          | cons c3 s3' => simp at et; rw [← et.1]; exact not_name_space (hs3 c3 (by simp)))
        exact (ok_ne_err h2 he).elim
      | Ok e =>
        obtain ⟨nm, nsplit, hnm, he⟩ := s2' e rfl
        refine ⟨.Ok (.Unparsed, e), by simp [hk, h1, h2, core.result.Result.Insts.CoreOpsTry.branch], ?_,
          fun s3 more split hs3 => (notExt s3 more split hs3).elim, ?_⟩
        · intro kind j eq; simp at eq; obtain ⟨rfl, rfl⟩ := eq
          refine Or.inr ⟨rfl, sp, sp2, nm, ?_, ⟨spne, all0⟩, hsp2, hnm, ?_⟩
          · rw [split0, d5, s2split, nsplit, lit_ndata]; simp
          · rw [he, hm, kv, h0v]
        · intro s1 s2 n s3 more split hs1 hs2 hn hs3
          obtain ⟨dk, rfl⟩ := atK s1 s2 n s3 more split hs1
          obtain ⟨m', hm', hm'v⟩ := spaces_complete cs k dk hs2 (head_append (name_not_space hn) (by
            obtain ⟨c0, r0, e0, _⟩ := hn.1; rw [e0]; simp))
          have em := ok_inj h1 hm'
          rw [← em] at hm'v
          have dn : (word cs).drop m.val = n ++ (s3 ++ 62 :: more) := by rw [hm'v]; exact drop_after dk
          obtain ⟨e', he', he'v⟩ := ncname_complete cs m dn hn (by
            intro c t et
            cases s3 with
            | nil => simp at et; rw [et.1]; exact not_name_gt
            | cons c3 s3' => simp at et; rw [← et.1]; exact not_name_space (hs3 c3 (by simp)))
          have ee := ok_inj h2 he'
          rw [← ee] at he'v
          refine ⟨e, rfl, ?_⟩
          rw [he'v, hm'v, kv, h0v]
  · rw [if_neg nd]
    refine ⟨.Ok (.External, i), rfl, ?_, fun _ _ _ _ => rfl, ?_⟩
    · intro kind j eq; simp at eq; obtain ⟨rfl, rfl⟩ := eq; exact Or.inl ⟨rfl, rfl⟩
    · intro s1 s2 n s3 more split hs1 _ _ _
      exfalso; apply nd
      have ss : s1 = sp := reads s1 (s2 ++ n ++ s3 ++ 62 :: more) (by rw [split]; simp) hs1.2
      subst ss
      refine ⟨by rw [h0v]; have := List.length_pos_of_ne_nil hs1.1; omega, ?_⟩
      rw [h0v]; have := drop_after (cs := cs) (i := i.val) (w := s1) (rest := lit "NDATA" ++ (s2 ++ n ++ s3 ++ 62 :: more))
        (by rw [split]; simp)
      rw [this]; exact ⟨_, rfl⟩

/-- The definition a declared kind and replacement text give. -/
def defOfKind (kind : xml.EntityKind) (t : alloc.vec.Vec U32) : Def :=
  match kind with
  | .Internal => .internal (word t)
  | .External => .external
  | .Unparsed => .unparsed

theorem defOf_eq (e : xml.Entity) : defOf e = defOfKind e.kind e.text := by
  unfold defOf defOfKind; cases e.kind <;> rfl

theorem valueText_nz {q : Nat} {body out : Word} (h : ValueText q body out) (nz : ∀ c ∈ body, c ≠ 0) :
    ∀ c ∈ out, c ≠ 0 := by
  induction h with
  | nil => simp
  | char _ _ _ _ ih =>
    intro c hc; simp at hc
    rcases hc with rfl | m
    · exact nz _ (by simp)
    · exact ih (fun d hd => nz d (by simp [hd])) c m
  | charRef _ hx _ ih =>
    intro c hc; simp at hc
    rcases hc with rfl | m
    · exact xml_char_ne_zero hx
    · exact ih (fun d hd => nz d (by simp [hd])) c m
  | entityRef _ _ ih =>
    intro c hc; simp at hc
    rcases hc with m | m
    · exact nz c (by simp [m])
    · exact ih (fun d hd => nz d (by simp [hd])) c m

theorem external_not_quote {e : Word} (h : ExternalID e) : ∀ c m, e = c :: m → ¬ Quote c := by
  intro c m em hq
  rcases external_head h with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [em, lit_system] at ht; simp at ht; rcases hq with h | h <;> omega
  · rw [em, lit_public] at ht; simp at ht; rcases hq with h | h <;> omega

theorem external_ne {e : Word} (h : ExternalID e) : e ≠ [] := by
  rcases external_head h with ⟨t, ht⟩ | ⟨t, ht⟩ <;> intro em <;> rw [em] at ht <;> simp [lit_system, lit_public] at ht

theorem drop_length_le {cs : alloc.vec.Vec U32} {i : Nat} {w rest : Word} (h : (word cs).drop i = w ++ rest) :
    w.length ≤ cs.val.length := by
  have := congrArg List.length h
  simp [word_length] at this; omega

theorem entity_definition_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.entity_definition cs i = .ok r ∧
      (∀ kind t j, r = .Ok (kind, t, j) → ∃ d, (word cs).drop i.val = d ++ (word cs).drop j.val ∧
        j.val = i.val + d.length ∧ EntityDef d (defOfKind kind t) ∧ (NoZero cs → NoZero t)) ∧
      (∀ d df s3 more, (word cs).drop i.val = d ++ s3 ++ 62 :: more → EntityDef d df → OptS s3 →
        (∀ c ∈ d, c ≠ 0) → ∃ kind t j, r = .Ok (kind, t, j) ∧ j.val = i.val + d.length ∧ defOfKind kind t = df) := by
  unfold xml.entity_definition
  simp only [at_eq, bind_ok, quote_eq, atU_val]
  have csmax : cs.val.length ≤ Usize.max := cs.property
  by_cases hq : Quote (charAt cs i.val)
  · obtain ⟨inside, hd⟩ := drop_nonzero (quote_ne_zero hq)
    obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
    have qv : (atU cs i.val).val = charAt cs i.val := atU_val cs i.val
    simp only [hq, decide_true, ite_true, hi1, bind_ok]
    obtain ⟨r1, h1, sound1, complete1⟩ := entity_value_spec cs i1 (atU cs i.val) (by rw [qv]; exact hq)
      (alloc.vec.Vec.new U32)
    rw [qv] at sound1 complete1
    simp only [word_new, List.nil_append] at sound1 complete1
    -- a complete reading is an entity value
    have internalOf : ∀ d df s3 more, (word cs).drop i.val = d ++ s3 ++ 62 :: more → EntityDef d df →
        ∃ body t, d = charAt cs i.val :: body ++ [charAt cs i.val] ∧ df = .internal t ∧
          ValueText (charAt cs i.val) body t ∧
          (word cs).drop i1.val = body ++ charAt cs i.val :: (s3 ++ 62 :: more) := by
      intro d df s3 more split hdf
      cases hdf with
      | @internal w text hv =>
        obtain ⟨q, body, _, rfl, hvt⟩ := hv
        have cq : charAt cs i.val = q := first_char (rest := body ++ [q] ++ s3 ++ 62 :: more) (by rw [split]; simp)
        subst cq
        refine ⟨body, text, rfl, rfl, hvt, ?_⟩
        rw [hd] at split; simp at split; rw [hi1v]; exact split
      | external he =>
        exfalso
        obtain ⟨c0, e', rfl⟩ := List.exists_cons_of_ne_nil (external_ne he)
        have := first_char (c := c0) (rest := e' ++ s3 ++ 62 :: more) (by rw [split]; simp)
        exact external_not_quote he c0 e' rfl (this ▸ hq)
      | @unparsed e s1 s2 n he _ _ _ =>
        exfalso
        obtain ⟨c0, e', rfl⟩ := List.exists_cons_of_ne_nil (external_ne he)
        have := first_char (c := c0) (rest := e' ++ s1 ++ lit "NDATA" ++ s2 ++ n ++ s3 ++ 62 :: more)
          (by rw [split]; simp)
        exact external_not_quote he c0 e' rfl (this ▸ hq)
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
      intro d df s3 more split hdf _ nz
      obtain ⟨body, t, rfl, rfl, hvt, d1⟩ := internalOf d df s3 more split hdf
      have bl := drop_length_le d1
      obtain ⟨t', j', h', _⟩ := complete1 body t (s3 ++ 62 :: more) d1 hvt (fun c hc => nz c (by simp [hc]))
        (by simp; omega)
      cases h'
    | Ok pair =>
      obtain ⟨t, j⟩ := pair
      obtain ⟨body, out, bsplit, hjq, hj, hvt, ht⟩ := sound1 t j rfl
      obtain ⟨insideJ, dJ⟩ := drop_nonzero (by rw [hjq]; exact quote_ne_zero hq)
      obtain ⟨j1, hj1, hj1v⟩ := next_spec insideJ
      refine ⟨.Ok (.Internal, t, j1), by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, hj1], ?_, ?_⟩
      · intro kind t' j' e; simp at e; obtain ⟨rfl, rfl, rfl⟩ := e
        refine ⟨charAt cs i.val :: body ++ [charAt cs i.val], ?_, by rw [hj1v, hj, hi1v]; simp; omega, ?_, ?_⟩
        · rw [hd, ← hi1v, bsplit, dJ, hjq, ← hj1v]; simp
        · simp only [defOfKind]
          rw [ht]; exact EntityDef.internal ⟨charAt cs i.val, body, hq, rfl, hvt⟩
        · intro nz c hc
          rw [ht] at hc
          have bnz : ∀ c' ∈ body, c' ≠ 0 := nz_of_drop nz bsplit
          exact valueText_nz hvt bnz c hc
      · intro d df s3 more split hdf _ nz
        obtain ⟨body', t', rfl, rfl, hvt', d1⟩ := internalOf d df s3 more split hdf
        have bl := drop_length_le d1
        obtain ⟨t2, j2, h2, ht2, hj2⟩ := complete1 body' t' (s3 ++ 62 :: more) d1 hvt'
          (fun c hc => nz c (by simp [hc])) (by simp; omega)
        simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        refine ⟨.Internal, t, j1, rfl, by rw [hj1v, hj2, hi1v]; simp; omega, ?_⟩
        simp only [defOfKind]; rw [ht2]
  · simp only [hq, decide_false, Bool.false_eq_true, ite_false]
    obtain ⟨r1, h1, sound1, complete1⟩ := external_id_spec cs i
    have externalOf : ∀ d df s3 more, (word cs).drop i.val = d ++ s3 ++ 62 :: more → EntityDef d df →
        (df = .external ∧ ExternalID d) ∨
        (∃ e s1 s2 n, d = e ++ s1 ++ lit "NDATA" ++ s2 ++ n ∧ df = .unparsed ∧ ExternalID e ∧ S s1 ∧ S s2 ∧
          NCName n) := by
      intro d df s3 more split hdf
      cases hdf with
      | @internal w text hv =>
        exfalso; obtain ⟨q, body, hq', rfl, _⟩ := hv
        exact hq (by rw [first_char (c := q) (rest := body ++ [q] ++ s3 ++ 62 :: more) (by rw [split]; simp)]; exact hq')
      | external he => exact Or.inl ⟨rfl, he⟩
      | @unparsed e s1 s2 n he hs1 hs2 hn => exact Or.inr ⟨e, s1, s2, n, rfl, rfl, he, hs1, hs2, hn⟩
    -- the position after the external identifier of a complete reading
    have afterId : ∀ e rest, (word cs).drop i.val = e ++ rest → ExternalID e → (∀ c ∈ e, c ≠ 0) →
        ∃ j, r1 = .Ok j ∧ j.val = i.val + e.length ∧ (word cs).drop j.val = rest := by
      intro e rest split he nz
      obtain ⟨j, hj, hjv⟩ := complete1 e rest split he nz
      exact ⟨j, hj, hjv, by rw [hjv]; exact drop_after split⟩
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
      intro d df s3 more split hdf _ nz
      rcases externalOf d df s3 more split hdf with ⟨rfl, he⟩ | ⟨e, s1, s2, n, rfl, rfl, he, _⟩
      · obtain ⟨j, hj, _⟩ := afterId d (s3 ++ 62 :: more) (by rw [split]; simp) he nz
        cases hj
      · obtain ⟨j, hj, _⟩ := afterId e (s1 ++ lit "NDATA" ++ s2 ++ n ++ s3 ++ 62 :: more) (by rw [split]; simp) he
          (fun c hc => nz c (by simp [hc]))
        cases hj
    | Ok j =>
      obtain ⟨e, esplit, he, hj⟩ := sound1 j rfl
      obtain ⟨r2, h2, s2, c2a, c2b⟩ := external_rest_spec cs j
      cases r2 with
      | Err err =>
        refine ⟨.Err err, by simp [h1, h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
        intro d df s3 more split hdf hs3 nz
        rcases externalOf d df s3 more split hdf with ⟨rfl, he'⟩ | ⟨e', s1, s2', n, rfl, rfl, he', hs1, hs2, hn⟩
        · obtain ⟨j', hj', _, dj⟩ := afterId d (s3 ++ 62 :: more) (by rw [split]; simp) he' nz
          simp only [core.result.Result.Ok.injEq] at hj'; subst hj'
          have := c2a s3 more dj hs3
          cases this
        · obtain ⟨j', hj', _, dj⟩ := afterId e' (s1 ++ lit "NDATA" ++ s2' ++ n ++ s3 ++ 62 :: more)
            (by rw [split]; simp) he' (fun c hc => nz c (by simp [hc]))
          simp only [core.result.Result.Ok.injEq] at hj'; subst hj'
          obtain ⟨k, hk, _⟩ := c2b s1 s2' n s3 more dj hs1 hs2 hn hs3
          cases hk
      | Ok pair =>
        obtain ⟨kind, k⟩ := pair
        refine ⟨.Ok (kind, alloc.vec.Vec.new U32, k), by simp [h1, h2, core.result.Result.Insts.CoreOpsTry.branch],
          ?_, ?_⟩
        · intro kind' t' j' eq; simp at eq; obtain ⟨rfl, rfl, rfl⟩ := eq
          rcases s2 kind k rfl with ⟨rfl, rfl⟩ | ⟨rfl, s1, s2', n, nsplit, hs1, hs2, hn, hk⟩
          · exact ⟨e, esplit, hj, EntityDef.external he, fun _ => by simp [NoZero, word_new]⟩
          · refine ⟨e ++ s1 ++ lit "NDATA" ++ s2' ++ n, by rw [esplit, nsplit]; simp, ?_,
              EntityDef.unparsed he hs1 hs2 hn, fun _ => by simp [NoZero, word_new]⟩
            rw [hk, hj]; simp [lit_ndata]; omega
        · intro d df s3 more split hdf hs3 nz
          rcases externalOf d df s3 more split hdf with ⟨rfl, he'⟩ | ⟨e', s1, s2', n, rfl, rfl, he', hs1, hs2, hn⟩
          · obtain ⟨j', hj', hj'v, dj⟩ := afterId d (s3 ++ 62 :: more) (by rw [split]; simp) he' nz
            simp only [core.result.Result.Ok.injEq] at hj'; subst hj'
            have := c2a s3 more dj hs3
            simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at this
            obtain ⟨rfl, rfl⟩ := this
            exact ⟨.External, _, _, rfl, hj'v, rfl⟩
          · obtain ⟨j', hj', hj'v, dj⟩ := afterId e' (s1 ++ lit "NDATA" ++ s2' ++ n ++ s3 ++ 62 :: more)
              (by rw [split]; simp) he' (fun c hc => nz c (by simp [hc]))
            simp only [core.result.Result.Ok.injEq] at hj'; subst hj'
            obtain ⟨k', hk', hk'v⟩ := c2b s1 s2' n s3 more dj hs1 hs2 hn hs3
            simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at hk'
            obtain ⟨rfl, rfl⟩ := hk'
            refine ⟨.Unparsed, _, _, rfl, ?_, rfl⟩
            rw [hk'v, hj'v]; simp [lit_ndata]; omega

theorem entityValue_head {d t : Word} (h : EntityValue d t) : ∃ q m, d = q :: m ∧ Quote q := by
  obtain ⟨q, body, hq, rfl, _⟩ := h; exact ⟨q, _, rfl, hq⟩

theorem parameter_definition_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.parameter_definition cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ d, (word cs).drop i.val = d ++ (word cs).drop j.val ∧ j.val = i.val + d.length ∧
        ((∃ t, EntityValue d t) ∨ ExternalID d)) ∧
      (∀ d rest, (word cs).drop i.val = d ++ rest → ((∃ t, EntityValue d t) ∨ ExternalID d) → (∀ c ∈ d, c ≠ 0) →
        ∃ j, r = .Ok j ∧ j.val = i.val + d.length) := by
  unfold xml.parameter_definition
  simp only [at_eq, bind_ok, quote_eq, atU_val]
  have csmax : cs.val.length ≤ Usize.max := cs.property
  by_cases hq : Quote (charAt cs i.val)
  · obtain ⟨inside, hd⟩ := drop_nonzero (quote_ne_zero hq)
    obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
    have qv : (atU cs i.val).val = charAt cs i.val := atU_val cs i.val
    simp only [hq, decide_true, ite_true, hi1, bind_ok]
    obtain ⟨r1, h1, sound1, complete1⟩ := entity_value_spec cs i1 (atU cs i.val) (by rw [qv]; exact hq)
      (alloc.vec.Vec.new U32)
    rw [qv] at sound1 complete1
    have valueOf : ∀ d rest, (word cs).drop i.val = d ++ rest → ((∃ t, EntityValue d t) ∨ ExternalID d) →
        ∃ body t, d = charAt cs i.val :: body ++ [charAt cs i.val] ∧ ValueText (charAt cs i.val) body t ∧
          (word cs).drop i1.val = body ++ charAt cs i.val :: rest := by
      intro d rest split hd'
      rcases hd' with ⟨t, q, body, _, rfl, hvt⟩ | he
      · have cq : charAt cs i.val = q := first_char (rest := body ++ [q] ++ rest) (by rw [split]; simp)
        subst cq
        refine ⟨body, t, rfl, hvt, ?_⟩
        rw [hd] at split; simp at split; rw [hi1v]; exact split
      · exfalso
        obtain ⟨c0, e', rfl⟩ := List.exists_cons_of_ne_nil (external_ne he)
        have := first_char (c := c0) (rest := e' ++ rest) (by rw [split]; simp)
        exact external_not_quote he c0 e' rfl (this ▸ hq)
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
      intro d rest split hd' nz
      obtain ⟨body, t, rfl, hvt, d1⟩ := valueOf d rest split hd'
      have bl := drop_length_le d1
      obtain ⟨t', j', h', _⟩ := complete1 body t rest d1 hvt (fun c hc => nz c (by simp [hc])) (by simp; omega)
      cases h'
    | Ok pair =>
      obtain ⟨t, j⟩ := pair
      obtain ⟨body, out, bsplit, hjq, hj, hvt, _⟩ := sound1 t j rfl
      obtain ⟨insideJ, dJ⟩ := drop_nonzero (by rw [hjq]; exact quote_ne_zero hq)
      obtain ⟨j1, hj1, hj1v⟩ := next_spec insideJ
      refine ⟨.Ok j1, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, hj1], ?_, ?_⟩
      · intro j' e; simp at e; subst e
        refine ⟨charAt cs i.val :: body ++ [charAt cs i.val], ?_, by rw [hj1v, hj, hi1v]; simp; omega,
          Or.inl ⟨out, charAt cs i.val, body, hq, rfl, hvt⟩⟩
        rw [hd, ← hi1v, bsplit, dJ, hjq, ← hj1v]; simp
      · intro d rest split hd' nz
        obtain ⟨body', t', rfl, hvt', d1⟩ := valueOf d rest split hd'
        have bl := drop_length_le d1
        obtain ⟨t2, j2, h2, _, hj2⟩ := complete1 body' t' rest d1 hvt' (fun c hc => nz c (by simp [hc]))
          (by simp; omega)
        simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨j1, rfl, by rw [hj1v, hj2, hi1v]; simp; omega⟩
  · simp only [hq, decide_false, Bool.false_eq_true, ite_false]
    obtain ⟨r1, h1, sound1, complete1⟩ := external_id_spec cs i
    refine ⟨r1, h1, ?_, ?_⟩
    · intro j e
      obtain ⟨d, split, he, hj⟩ := sound1 j e
      exact ⟨d, split, hj, Or.inr he⟩
    · intro d rest split hd' nz
      rcases hd' with ⟨t, hv⟩ | he
      · exfalso
        obtain ⟨q, m, rfl, hq'⟩ := entityValue_head hv
        exact hq (by rw [first_char (c := q) (rest := m ++ rest) (by rw [split]; simp)]; exact hq')
      · exact complete1 d rest split he nz

theorem name_ne {n : Word} (h : NCName n) : n ≠ [] := by
  obtain ⟨c0, r0, e0, _⟩ := h.1; rw [e0]; simp

theorem def_not_space {d : Word} (h : (∃ t, EntityValue d t) ∨ ExternalID d) : ∀ c m, d = c :: m → ¬ IsSpace c := by
  intro c m e
  rcases h with ⟨t, hv⟩ | he
  · obtain ⟨q, m', rfl, hq⟩ := entityValue_head hv
    simp at e; rw [← e.1]; exact quote_not_space hq
  · rcases external_head he with ⟨t, ht⟩ | ⟨t, ht⟩
    · rw [e, lit_system] at ht; simp at ht; rw [ht.1]; simp [IsSpace]
    · rw [e, lit_public] at ht; simp at ht; rw [ht.1]; simp [IsSpace]

theorem def_ne {d : Word} (h : (∃ t, EntityValue d t) ∨ ExternalID d) : d ≠ [] := by
  rcases h with ⟨t, hv⟩ | he
  · obtain ⟨q, m', rfl, _⟩ := entityValue_head hv; simp
  · exact external_ne he

theorem spaces_head_not_name {s rest : Word} (hs : S s) : ∀ c m, s ++ rest = c :: m → ¬ NameChar c := by
  intro c m e
  obtain ⟨c0, r0, e0⟩ := List.exists_cons_of_ne_nil hs.1
  rw [e0] at e; simp at e; rw [← e.1]; exact not_name_space (hs.2 c0 (by rw [e0]; simp))

theorem parameter_declaration_spec (cs : alloc.vec.Vec U32) (j : Usize) (pct : charAt cs j.val = 37) :
    ∃ r, xml.parameter_declaration cs j = .ok r ∧
      (∀ k, r = .Ok k → ∃ s2 n s3 d s4, (word cs).drop j.val = [37] ++ s2 ++ n ++ s3 ++ d ++ s4 ++ 62 ::
        (word cs).drop k.val ∧ S s2 ∧ NCName n ∧ S s3 ∧ ((∃ t, EntityValue d t) ∨ ExternalID d) ∧ OptS s4 ∧
        k.val = j.val + 1 + s2.length + n.length + s3.length + d.length + s4.length + 1) ∧
      (∀ s2 n s3 d s4 rest, (word cs).drop j.val = [37] ++ s2 ++ n ++ s3 ++ d ++ s4 ++ 62 :: rest → S s2 →
        NCName n → S s3 → ((∃ t, EntityValue d t) ∨ ExternalID d) → OptS s4 → (∀ c ∈ d, c ≠ 0) →
        ∃ k, r = .Ok k ∧ k.val = j.val + 1 + s2.length + n.length + s3.length + d.length + s4.length + 1) := by
  unfold xml.parameter_declaration
  obtain ⟨inside, hd⟩ := drop_nonzero (by rw [pct]; decide : charAt cs j.val ≠ 0)
  obtain ⟨j1, hj1, hj1v⟩ := next_spec inside
  simp only [hj1, bind_ok]
  have d1of : ∀ s2 n s3 d s4 rest, (word cs).drop j.val = [37] ++ s2 ++ n ++ s3 ++ d ++ s4 ++ 62 :: rest →
      (word cs).drop j1.val = s2 ++ (n ++ (s3 ++ (d ++ (s4 ++ 62 :: rest)))) := by
    intro s2 n s3 d s4 rest split
    rw [hd] at split; simp at split; rw [hj1v]; exact split.2
  obtain ⟨r1, h1, s1⟩ := spaces_sound cs j1
  cases r1 with
  | Err err =>
    refine ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
    intro s2 n s3 d s4 rest split hs2 hn _ _ _ _
    obtain ⟨m, hm, _⟩ := spaces_complete cs j1 (d1of s2 n s3 d s4 rest split) hs2
      (head_append (name_not_space hn) (name_ne hn))
    exact (ok_ne_err h1 hm).elim
  | Ok m1 =>
    obtain ⟨sp2, sp2split, hsp2, hm1⟩ := s1 m1 rfl
    have d2of : ∀ s2 n s3 d s4 rest, (word cs).drop j.val = [37] ++ s2 ++ n ++ s3 ++ d ++ s4 ++ 62 :: rest →
        S s2 → NCName n → (word cs).drop m1.val = n ++ (s3 ++ (d ++ (s4 ++ 62 :: rest))) ∧
        m1.val = j1.val + s2.length := by
      intro s2 n s3 d s4 rest split hs2 hn
      have d1 := d1of s2 n s3 d s4 rest split
      obtain ⟨m, hm, hmv⟩ := spaces_complete cs j1 d1 hs2 (head_append (name_not_space hn) (name_ne hn))
      have e := ok_inj h1 hm; rw [← e] at hmv
      exact ⟨by rw [hmv]; exact drop_after d1, hmv⟩
    obtain ⟨r2, h2, s2'⟩ := ncname_sound cs m1
    cases r2 with
    | Err err =>
      refine ⟨.Err err, by simp [h1, h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
      intro s2 n s3 d s4 rest split hs2 hn hs3 _ _ _
      obtain ⟨d2, _⟩ := d2of s2 n s3 d s4 rest split hs2 hn
      obtain ⟨e, he, _⟩ := ncname_complete cs m1 d2 hn (spaces_head_not_name hs3)
      exact (ok_ne_err h2 he).elim
    | Ok e1 =>
      obtain ⟨nm, nsplit, hnm, he1⟩ := s2' e1 rfl
      have d3of : ∀ s2 n s3 d s4 rest, (word cs).drop j.val = [37] ++ s2 ++ n ++ s3 ++ d ++ s4 ++ 62 :: rest →
          S s2 → NCName n → S s3 → (word cs).drop e1.val = s3 ++ (d ++ (s4 ++ 62 :: rest)) ∧
          e1.val = j1.val + s2.length + n.length := by
        intro s2 n s3 d s4 rest split hs2 hn hs3
        obtain ⟨d2, hm1'⟩ := d2of s2 n s3 d s4 rest split hs2 hn
        obtain ⟨e, he, hev⟩ := ncname_complete cs m1 d2 hn (spaces_head_not_name hs3)
        have ee := ok_inj h2 he; rw [← ee] at hev
        exact ⟨by rw [hev]; exact drop_after d2, by omega⟩
      obtain ⟨r3, h3, s3'⟩ := spaces_sound cs e1
      cases r3 with
      | Err err =>
        refine ⟨.Err err, by simp [h1, h2, h3, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
        intro s2 n s3 d s4 rest split hs2 hn hs3 hd' _ _
        obtain ⟨d3, _⟩ := d3of s2 n s3 d s4 rest split hs2 hn hs3
        obtain ⟨m, hm, _⟩ := spaces_complete cs e1 d3 hs3 (head_append (def_not_space hd') (def_ne hd'))
        exact (ok_ne_err h3 hm).elim
      | Ok m2 =>
        obtain ⟨sp3, sp3split, hsp3, hm2⟩ := s3' m2 rfl
        have d4of : ∀ s2 n s3 d s4 rest, (word cs).drop j.val = [37] ++ s2 ++ n ++ s3 ++ d ++ s4 ++ 62 :: rest →
            S s2 → NCName n → S s3 → ((∃ t, EntityValue d t) ∨ ExternalID d) →
            (word cs).drop m2.val = d ++ (s4 ++ 62 :: rest) ∧ m2.val = j1.val + s2.length + n.length + s3.length := by
          intro s2 n s3 d s4 rest split hs2 hn hs3 hd'
          obtain ⟨d3, he1'⟩ := d3of s2 n s3 d s4 rest split hs2 hn hs3
          obtain ⟨m, hm, hmv⟩ := spaces_complete cs e1 d3 hs3 (head_append (def_not_space hd') (def_ne hd'))
          have e := ok_inj h3 hm; rw [← e] at hmv
          exact ⟨by rw [hmv]; exact drop_after d3, by omega⟩
        obtain ⟨r4, h4, s4', c4⟩ := parameter_definition_spec cs m2
        cases r4 with
        | Err err =>
          refine ⟨.Err err, by simp [h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
            by simp, ?_⟩
          intro s2 n s3 d s4 rest split hs2 hn hs3 hd' _ nz
          obtain ⟨d4, _⟩ := d4of s2 n s3 d s4 rest split hs2 hn hs3 hd'
          obtain ⟨k, hk, _⟩ := c4 d (s4 ++ 62 :: rest) d4 hd' nz
          cases hk
        | Ok k1 =>
          obtain ⟨dw, dsplit, hk1, hdw⟩ := s4' k1 rfl
          obtain ⟨r5, h5, s5, c5⟩ := declaration_close_spec cs k1
          refine ⟨r5, by simp [h1, h2, h3, h4, h5, core.result.Result.Insts.CoreOpsTry.branch], ?_, ?_⟩
          · intro k e
            obtain ⟨sp4, csplit, hsp4, hk⟩ := s5 k e
            refine ⟨sp2, nm, sp3, dw, sp4, ?_, hsp2, hnm, hsp3, hdw, hsp4, ?_⟩
            · rw [hd, pct, ← hj1v, sp2split, nsplit, sp3split, dsplit, csplit]; simp
            · rw [hk, hk1, hm2, he1, hm1, hj1v]
          · intro s2 n s3 d s4 rest split hs2 hn hs3 hd' hs4 nz
            obtain ⟨d4, hm2'⟩ := d4of s2 n s3 d s4 rest split hs2 hn hs3 hd'
            obtain ⟨k, hk, hkv⟩ := c4 d (s4 ++ 62 :: rest) d4 hd' nz
            simp only [core.result.Result.Ok.injEq] at hk; subst hk
            obtain ⟨k', hk', hk'v⟩ := c5 s4 rest (by rw [hkv]; exact drop_after d4) hs4
            exact ⟨k', hk', by rw [hk'v, hkv, hm2', hj1v]⟩

theorem push_entity_sound (env : alloc.vec.Vec xml.Entity) (e : xml.Entity) (offset : Usize) :
    ∃ r, xml.push_entity env e offset = .ok r ∧ (∀ v, r = .Ok v → v.val = env.val ++ [e]) ∧
      (env.val.length < Usize.max → ∃ v, r = .Ok v) := by
  by_cases h : env.val.length < Usize.max
  · obtain ⟨v, hv, hvv⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec env e h)
    exact ⟨.Ok v, by simp [xml.push_entity, alloc.vec.Vec.len_val, core.num.Usize.MAX, h, hv],
      fun v' e' => by simp at e'; subst e'; exact hvv, fun _ => ⟨v, rfl⟩⟩
  · exact ⟨.Err ⟨.ResourceLimit, offset⟩, by simp [xml.push_entity, alloc.vec.Vec.len_val, core.num.Usize.MAX, h,
      xml.fail], by simp, fun h' => absurd h' h⟩

theorem entityDef_not_space {d : Word} {df : Def} (h : EntityDef d df) : ∀ c m, d = c :: m → ¬ IsSpace c := by
  cases h with
  | internal hv => exact def_not_space (Or.inl ⟨_, hv⟩)
  | external he => exact def_not_space (Or.inr he)
  | @unparsed e s1 s2 n he _ _ _ =>
    intro c m em
    obtain ⟨c0, e', rfl⟩ := List.exists_cons_of_ne_nil (external_ne he)
    simp at em; rw [← em.1]
    exact def_not_space (Or.inr he) c0 e' rfl

theorem entityDef_ne {d : Word} {df : Def} (h : EntityDef d df) : d ≠ [] := by
  cases h with
  | internal hv => exact def_ne (Or.inl ⟨_, hv⟩)
  | external he => exact external_ne he
  | unparsed he _ _ _ => have := external_ne he; simp [this]

theorem general_declaration_spec (cs : alloc.vec.Vec U32) (i j : Usize) (env : alloc.vec.Vec xml.Entity) :
    ∃ r, xml.general_declaration cs i j env = .ok r ∧
      (∀ env' k, r = .Ok (env', k) → ∃ n s2 d df s3, (word cs).drop j.val = n ++ s2 ++ d ++ s3 ++ 62 ::
        (word cs).drop k.val ∧ NCName n ∧ S s2 ∧ EntityDef d df ∧ OptS s3 ∧
        k.val = j.val + n.length + s2.length + d.length + s3.length + 1 ∧
        envView env' = envView env ++ [(n, df)] ∧ (EnvOk env → NoZero cs → EnvOk env')) ∧
      (∀ n s2 d df s3 rest, (word cs).drop j.val = n ++ s2 ++ d ++ s3 ++ 62 :: rest → NCName n → S s2 →
        EntityDef d df → OptS s3 → (∀ c ∈ d, c ≠ 0) → env.val.length < Usize.max →
        ∃ env' k, r = .Ok (env', k) ∧ k.val = j.val + n.length + s2.length + d.length + s3.length + 1 ∧
          envView env' = envView env ++ [(n, df)]) := by
  unfold xml.general_declaration
  obtain ⟨r1, h1, s1⟩ := ncname_sound cs j
  have n1of : ∀ (n s2 d s3 rest : Word), (word cs).drop j.val = n ++ s2 ++ d ++ s3 ++ 62 :: rest → NCName n →
      S s2 → ∃ e, xml.ncname cs j = .ok (.Ok e) ∧ e.val = j.val + n.length := by
    intro n s2 d s3 rest split hn hs2
    exact ncname_complete cs j (rest := s2 ++ (d ++ s3 ++ 62 :: rest)) (by rw [split]; simp) hn
      (spaces_head_not_name hs2)
  cases r1 with
  | Err err =>
    refine ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
    intro n s2 d df s3 rest split hn hs2 _ _ _ _
    obtain ⟨e, he, _⟩ := n1of n s2 d s3 rest split hn hs2
    exact (ok_ne_err h1 he).elim
  | Ok e1 =>
    obtain ⟨nm, nsplit, hnm, he1⟩ := s1 e1 rfl
    have at1 : ∀ (n s2 d s3 rest : Word), (word cs).drop j.val = n ++ s2 ++ d ++ s3 ++ 62 :: rest → NCName n →
        S s2 → n = nm ∧ (word cs).drop e1.val = s2 ++ (d ++ (s3 ++ 62 :: rest)) := by
      intro n s2 d s3 rest split hn hs2
      obtain ⟨e, he, hev⟩ := n1of n s2 d s3 rest split hn hs2
      have ee := ok_inj h1 he; rw [← ee] at hev
      have nn : n = nm := same_consumed (by rw [split]; simp : (word cs).drop j.val = n ++ (s2 ++ d ++ s3 ++ 62 :: rest))
        nsplit (by omega)
      refine ⟨nn, ?_⟩
      rw [hev]; have := drop_after (cs := cs) (i := j.val) (w := n) (rest := s2 ++ (d ++ (s3 ++ 62 :: rest)))
        (by rw [split]; simp)
      exact this
    obtain ⟨r2, h2, s2'⟩ := spaces_sound cs e1
    cases r2 with
    | Err err =>
      refine ⟨.Err err, by simp [h1, h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
      intro n s2 d df s3 rest split hn hs2 hd' _ _ _
      obtain ⟨_, d1⟩ := at1 n s2 d s3 rest split hn hs2
      obtain ⟨m, hm, _⟩ := spaces_complete cs e1 d1 hs2 (head_append (entityDef_not_space hd') (entityDef_ne hd'))
      exact (ok_ne_err h2 hm).elim
    | Ok m1 =>
      obtain ⟨sp2, sp2split, hsp2, hm1⟩ := s2' m1 rfl
      have at2 : ∀ n s2 d df s3 rest, (word cs).drop j.val = n ++ s2 ++ d ++ s3 ++ 62 :: rest → NCName n → S s2 →
          EntityDef d df → (word cs).drop m1.val = d ++ s3 ++ 62 :: rest ∧ m1.val = e1.val + s2.length := by
        intro n s2 d df s3 rest split hn hs2 hd'
        obtain ⟨_, d1⟩ := at1 n s2 d s3 rest split hn hs2
        obtain ⟨m, hm, hmv⟩ := spaces_complete cs e1 d1 hs2 (head_append (entityDef_not_space hd') (entityDef_ne hd'))
        have em := ok_inj h2 hm; rw [← em] at hmv
        exact ⟨by rw [hmv, drop_after d1]; simp, hmv⟩
      obtain ⟨r3, h3, s3', c3⟩ := entity_definition_spec cs m1
      cases r3 with
      | Err err =>
        refine ⟨.Err err, by simp [h1, h2, h3, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
        intro n s2 d df s3 rest split hn hs2 hd' hs3 nz _
        obtain ⟨d2, _⟩ := at2 n s2 d df s3 rest split hn hs2 hd'
        obtain ⟨kind, t, k, hk, _⟩ := c3 d df s3 rest d2 hd' hs3 nz
        cases hk
      | Ok triple =>
        obtain ⟨kind, text, n1⟩ := triple
        obtain ⟨dw, dsplit, hn1, hdw, hnz⟩ := s3' kind text n1 rfl
        obtain ⟨r4, h4, s4, c4⟩ := declaration_close_spec cs n1
        have at3 : ∀ n s2 d df s3 rest, (word cs).drop j.val = n ++ s2 ++ d ++ s3 ++ 62 :: rest → NCName n → S s2 →
            EntityDef d df → OptS s3 → (∀ c ∈ d, c ≠ 0) →
            (word cs).drop n1.val = s3 ++ 62 :: rest ∧ n1.val = m1.val + d.length ∧ defOfKind kind text = df := by
          intro n s2 d df s3 rest split hn hs2 hd' hs3 nz
          obtain ⟨d2, _⟩ := at2 n s2 d df s3 rest split hn hs2 hd'
          obtain ⟨kind', t', k', hk', hk'v, hdf⟩ := c3 d df s3 rest d2 hd' hs3 nz
          simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at hk'
          obtain ⟨rfl, rfl, rfl⟩ := hk'
          refine ⟨?_, hk'v, hdf⟩
          rw [hk'v]; have := drop_after (cs := cs) (i := m1.val) (w := d) (rest := s3 ++ 62 :: rest) (by rw [d2]; simp)
          exact this
        cases r4 with
        | Err err =>
          refine ⟨.Err err, by simp [h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
            by simp, ?_⟩
          intro n s2 d df s3 rest split hn hs2 hd' hs3 nz _
          obtain ⟨d3, _⟩ := at3 n s2 d df s3 rest split hn hs2 hd' hs3 nz
          obtain ⟨k, hk, _⟩ := c4 s3 rest d3 hs3
          cases hk
        | Ok close =>
          obtain ⟨sp3, csplit, hsp3, hclose⟩ := s4 close rfl
          obtain ⟨nmv, hname, hnamew⟩ := copy_span_spec cs j e1 nsplit he1
          obtain ⟨r5, h5, s5, c5⟩ := push_entity_sound env ⟨nmv, kind, text⟩ i
          cases r5 with
          | Err err =>
            refine ⟨.Err err, by simp [h1, h2, h3, h4, hname, h5, core.result.Result.Insts.CoreOpsTry.branch,
              same_residual], by simp, ?_⟩
            intro n s2 d df s3 rest split hn hs2 hd' hs3 nz room
            obtain ⟨v, hv⟩ := c5 room
            cases hv
          | Ok env' =>
            have hev := s5 env' rfl
            refine ⟨.Ok (env', close), by simp [h1, h2, h3, h4, hname, h5, core.result.Result.Insts.CoreOpsTry.branch],
              ?_, ?_⟩
            · intro env'' k eq; simp at eq; obtain ⟨rfl, rfl⟩ := eq
              refine ⟨nm, sp2, dw, defOfKind kind text, sp3, ?_, hnm, hsp2, hdw, hsp3, ?_, ?_, ?_⟩
              · rw [nsplit, sp2split, dsplit, csplit]; simp
              · rw [hclose, hn1, hm1, he1]
              · simp [envView, hev, hnamew, defOf_eq]
              · intro henv nz e he
                rw [hev] at he
                simp only [List.mem_append, List.mem_singleton] at he
                rcases he with m | rfl
                · exact henv e m
                · exact hnz nz
            · intro n s2 d df s3 rest split hn hs2 hd' hs3 nz room
              obtain ⟨nn, _⟩ := at1 n s2 d s3 rest split hn hs2
              subst nn
              obtain ⟨_, hm1'⟩ := at2 n s2 d df s3 rest split hn hs2 hd'
              obtain ⟨d3, hn1', hdf⟩ := at3 n s2 d df s3 rest split hn hs2 hd' hs3 nz
              obtain ⟨k, hk, hkv⟩ := c4 s3 rest d3 hs3
              simp only [core.result.Result.Ok.injEq] at hk; subst hk
              refine ⟨env', _, rfl, by rw [hkv, hn1', hm1', he1], ?_⟩
              simp [envView, hev, hnamew, defOf_eq, hdf]

end Rowl.XmlDoctype
