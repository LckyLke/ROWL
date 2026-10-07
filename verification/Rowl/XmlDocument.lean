import Rowl.XmlSubset

/-!
# The document type declaration and the document

`doctype` reads the grammar's `doctypedecl` with the general entities of its
internal subset, and `document` reads a `document`.
-/

namespace Rowl.XmlDocument
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs Rowl.XmlEntities Rowl.XmlAttributes Rowl.XmlTags Rowl.XmlNamespaces Rowl.XmlContent Rowl.XmlElements Rowl.XmlComplete Rowl.XmlDecl Rowl.XmlLiterals Rowl.XmlEntityDecls Rowl.XmlDoctype Rowl.XmlSubset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

theorem lit_doctype : lit "<!DOCTYPE" = [60, 33, 68, 79, 67, 84, 89, 80, 69] := by decide
theorem map_doctype : ([60#u8, 33#u8, 68#u8, 79#u8, 67#u8, 84#u8, 89#u8, 80#u8, 69#u8] : List U8).map (·.val) =
    lit "<!DOCTYPE" := by decide

theorem external_follows_eq (cs : alloc.vec.Vec U32) (i j : Usize) :
    xml.external_follows cs i j = .ok (decide (i.val < j.val ∧
      (lit "SYSTEM" <+: (word cs).drop j.val ∨ lit "PUBLIC" <+: (word cs).drop j.val))) := by
  simp [xml.external_follows, lift, starts_eq, bytes_make, map_system, map_public, UScalar.lt_equiv, lit_system,
    lit_public]

theorem external_space_head {e : Word} (he : ExternalID e) : ∀ c m, e = c :: m → ¬ IsSpace c :=
  def_not_space (Or.inr he)

theorem doctype_external_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.doctype_external cs i = .ok r ∧
      (∀ j, r = .Ok j → j = i ∨ ∃ s e, (word cs).drop i.val = s ++ e ++ (word cs).drop j.val ∧ S s ∧
        ExternalID e ∧ j.val = i.val + s.length + e.length) ∧
      (∀ s2 c more, (word cs).drop i.val = s2 ++ c :: more → OptS s2 → (c = 62 ∨ c = 91) → r = .Ok i) ∧
      (∀ s e rest, (word cs).drop i.val = s ++ e ++ rest → S s → ExternalID e → (∀ c ∈ e, c ≠ 0) →
        ∃ j, r = .Ok j ∧ j.val = i.val + s.length + e.length) := by
  unfold xml.doctype_external
  obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
  have split0 := drop_run IsSpace cs i.val
  rw [← h0v] at split0
  have all0 : ∀ c ∈ run IsSpace ((word cs).drop i.val), IsSpace c := run_all
  generalize hr0 : run IsSpace ((word cs).drop i.val) = sp at split0 h0v all0
  simp only [h0, bind_ok, external_follows_eq, decide_eq_true_eq]
  -- a complete reading of an external identifier reads the spaces `sp`
  have reads : ∀ s e rest, (word cs).drop i.val = s ++ e ++ rest → S s → ExternalID e →
      s = sp ∧ (word cs).drop j0.val = e ++ rest := by
    intro s e rest split hs he
    have ss : s = sp := by
      rw [← hr0, split]; simpa using (run_unique hs.2 (head_append (external_space_head he) (external_ne he))).symm
    subst ss
    exact ⟨rfl, by rw [h0v]; simpa using drop_after (rest := e ++ rest) (by rw [split]; simp)⟩
  by_cases ext : i.val < j0.val ∧ (lit "SYSTEM" <+: (word cs).drop j0.val ∨ lit "PUBLIC" <+: (word cs).drop j0.val)
  · rw [if_pos ext]
    obtain ⟨r1, h1, s1, c1⟩ := external_id_spec cs j0
    refine ⟨r1, h1, ?_, ?_, ?_⟩
    · intro j e
      obtain ⟨ew, esplit, he, hj⟩ := s1 j e
      right
      refine ⟨sp, ew, by rw [split0, esplit]; simp, ⟨?_, all0⟩, he, by rw [hj, h0v]⟩
      intro e'; rw [e'] at h0v; simp at h0v; omega
    · intro s2 c more split hs2 hc
      exfalso
      have ss : s2 = sp := by
        rw [← hr0, split]; refine (run_unique hs2 (head_not_space ?_)).symm
        rcases hc with rfl | rfl <;> simp [IsSpace]
      subst ss
      have dj : (word cs).drop j0.val = c :: more := by rw [h0v]; exact drop_after split
      rw [dj] at ext
      rcases ext.2 with ⟨t, ht⟩ | ⟨t, ht⟩ <;> [rw [lit_system] at ht; rw [lit_public] at ht] <;> simp at ht <;>
        rcases hc with rfl | rfl <;> simp at ht
    · intro s e rest split hs he nz
      obtain ⟨rfl, dj⟩ := reads s e rest split hs he
      obtain ⟨j, hj, hjv⟩ := c1 e rest dj he nz
      exact ⟨j, hj, by rw [hjv, h0v]⟩
  · rw [if_neg ext]
    refine ⟨.Ok i, rfl, fun j e => by simp at e; exact Or.inl e.symm, fun _ _ _ _ _ _ => rfl, ?_⟩
    intro s e rest split hs he _
    exfalso; apply ext
    obtain ⟨rfl, dj⟩ := reads s e rest split hs he
    refine ⟨by rw [h0v]; have := List.length_pos_of_ne_nil hs.1; omega, ?_⟩
    rw [dj]
    rcases external_head he with ⟨t, ht⟩ | ⟨t, ht⟩
    · left; rw [← ht]; exact ⟨t ++ rest, by simp⟩
    · right; rw [← ht]; exact ⟨t ++ rest, by simp⟩

/-- The rest of a document type declaration after its name and external identifier. -/
def DoctypeRest (rest : Word) (envs : Env) : Prop :=
  (rest = [62] ∧ envs = []) ∨ ∃ body s3, rest = [91] ++ body ++ [93] ++ s3 ++ [62] ∧ IntSubset body envs ∧ OptS s3

theorem doctype_rest_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.doctype_rest cs i = .ok r ∧
      (∀ env j, r = .Ok (env, j) → ∃ s2 rest envs, (word cs).drop i.val = s2 ++ rest ++ (word cs).drop j.val ∧
        OptS s2 ∧ DoctypeRest rest envs ∧ envView env = envs ∧ (NoZero cs → EnvOk env) ∧
        j.val = i.val + s2.length + rest.length) ∧
      (∀ s2 rest envs more, (word cs).drop i.val = s2 ++ rest ++ more → OptS s2 → DoctypeRest rest envs →
        NoZero cs → ∃ env j, r = .Ok (env, j) ∧ envView env = envs ∧ j.val = i.val + s2.length + rest.length) := by
  unfold xml.doctype_rest
  obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
  have split0 := drop_run IsSpace cs i.val
  rw [← h0v] at split0
  have all0 : ∀ c ∈ run IsSpace ((word cs).drop i.val), IsSpace c := run_all
  generalize hr0 : run IsSpace ((word cs).drop i.val) = sp at split0 h0v all0
  have reads : ∀ s2 rest envs more, (word cs).drop i.val = s2 ++ rest ++ more → OptS s2 → DoctypeRest rest envs →
      s2 = sp ∧ (word cs).drop j0.val = rest ++ more := by
    intro s2 rest envs more split hs2 hrest
    have ss : s2 = sp := by
      rw [← hr0, split]
      rcases hrest with ⟨rfl, _⟩ | ⟨body, s3, rfl, _⟩
      · have h := run_unique (rest := 62 :: more) hs2 (head_not_space (q := 62) (by simp [IsSpace]))
        rw [List.append_assoc]; exact h.symm
      · have h := run_unique (rest := 91 :: (body ++ [93] ++ s3 ++ [62] ++ more)) hs2
          (head_not_space (q := 91) (by simp [IsSpace]))
        have e : s2 ++ ([91] ++ body ++ [93] ++ s3 ++ [62]) ++ more =
            s2 ++ 91 :: (body ++ [93] ++ s3 ++ [62] ++ more) := by simp
        rw [e]; exact h.symm
    subst ss
    exact ⟨rfl, by rw [h0v]; simpa using drop_after (rest := rest ++ more) (by rw [split]; simp)⟩
  simp only [h0, bind_ok, at_eq, atU_eq_iff]
  by_cases open_ : charAt cs j0.val = 91
  · rw [if_pos (by simpa using open_)]
    obtain ⟨inside, dJ⟩ := drop_nonzero (by rw [open_]; decide : charAt cs j0.val ≠ 0)
    obtain ⟨j1, hj1, hj1v⟩ := next_spec inside
    obtain ⟨r1, h1, s1⟩ := internal_subset_sound cs j1 (alloc.vec.Vec.new _)
    have envView_new : envView (alloc.vec.Vec.new xml.Entity) = [] := by simp [envView]
    -- what a complete reading of an internal subset gives
    have subsetOf : ∀ s2 rest envs more, (word cs).drop i.val = s2 ++ rest ++ more → OptS s2 →
        DoctypeRest rest envs → NoZero cs → ∃ body s3, rest = [91] ++ body ++ [93] ++ s3 ++ [62] ∧
        IntSubset body envs ∧ OptS s3 ∧ (word cs).drop j1.val = [] ++ body ++ 93 :: (s3 ++ [62] ++ more) := by
      intro s2 rest envs more split hs2 hrest nz
      obtain ⟨rfl, dj⟩ := reads s2 rest envs more split hs2 hrest
      rcases hrest with ⟨rfl, _⟩ | ⟨body, s3, rfl, hb, hs3⟩
      · exfalso; rw [dJ, open_] at dj; simp at dj
      · refine ⟨body, s3, rfl, hb, hs3, ?_⟩
        rw [dJ, open_] at dj; simp at dj; rw [hj1v]; simpa using dj
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [hj1, h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
      intro s2 rest envs more split hs2 hrest nz
      obtain ⟨body, s3, rfl, hb, hs3, d1⟩ := subsetOf s2 rest envs more split hs2 hrest nz
      obtain ⟨env', j, hj, _⟩ := internal_subset_complete hb cs j1 (alloc.vec.Vec.new _) [] (s3 ++ [62] ++ more) d1
        (by simp [OptS]) nz (by simp; have := cs.property; omega)
      exact (ok_ne_err h1 hj).elim
    | Ok pair =>
      obtain ⟨env, k⟩ := pair
      obtain ⟨body, envs, bsplit, hk93, hb, hview, hok⟩ := s1 env k rfl
      obtain ⟨insideK, dK⟩ := drop_nonzero (by rw [hk93]; decide : charAt cs k.val ≠ 0)
      obtain ⟨k1, hk1, hk1v⟩ := next_spec insideK
      obtain ⟨r2, h2, s2', c2⟩ := declaration_close_spec cs k1
      -- where a complete reading continues after the subset
      have afterSubset : ∀ s2 rest envs' more, (word cs).drop i.val = s2 ++ rest ++ more → OptS s2 →
          DoctypeRest rest envs' → NoZero cs → ∃ body' s3, rest = [91] ++ body' ++ [93] ++ s3 ++ [62] ∧ OptS s3 ∧
          envs' = envs ∧ (word cs).drop k1.val = s3 ++ 62 :: more ∧ k.val = j1.val + body'.length := by
        intro s2 rest envs' more split hs2 hrest nz
        obtain ⟨body', s3, rfl, hb', hs3, d1⟩ := subsetOf s2 rest envs' more split hs2 hrest nz
        obtain ⟨env', j, hj, hjv, hview'⟩ := internal_subset_complete hb' cs j1 (alloc.vec.Vec.new _) []
          (s3 ++ [62] ++ more) d1 (by simp [OptS]) nz (by simp; have := cs.property; omega)
        have ee := ok_inj h1 hj
        simp only [Prod.mk.injEq] at ee; obtain ⟨rfl, rfl⟩ := ee
        have kv : k.val = j1.val + body'.length := by simpa using hjv
        refine ⟨body', s3, rfl, hs3, ?_, ?_, kv⟩
        · rw [hview, envView_new] at hview'; simpa using hview'.symm
        · have := drop_after (cs := cs) (i := j1.val) (w := body') (rest := 93 :: (s3 ++ [62] ++ more))
            (by simpa using d1)
          rw [← kv, dK] at this; simp at this; rw [hk1v]; exact this.2
      cases r2 with
      | Err err =>
        refine ⟨.Err err, by simp [hj1, h1, core.result.Result.Insts.CoreOpsTry.branch, hk1, h2, same_residual],
          by simp, ?_⟩
        intro s2 rest envs' more split hs2 hrest nz
        obtain ⟨body', s3, rfl, hs3, _, dk1, _⟩ := afterSubset s2 rest envs' more split hs2 hrest nz
        obtain ⟨c, hc, _⟩ := c2 s3 more dk1 hs3
        cases hc
      | Ok close =>
        refine ⟨.Ok (env, close), by simp [hj1, h1, core.result.Result.Insts.CoreOpsTry.branch, hk1, h2], ?_, ?_⟩
        · intro env' j e; simp at e; obtain ⟨rfl, rfl⟩ := e
          obtain ⟨s3, csplit, hs3, hclose⟩ := s2' close rfl
          have hblen : k.val = j1.val + body.length := by
            have := congrArg List.length bsplit; simp [word_length] at this
            have := charAt_inside (cs := cs) (i := k.val) (by rw [hk93]; decide); omega
          refine ⟨sp, [91] ++ body ++ [93] ++ s3 ++ [62], envs, ?_, all0, Or.inr ⟨body, s3, rfl, hb, hs3⟩,
            by rw [hview, envView_new]; simp, fun nz => hok (by intro e he; simp at he) nz, ?_⟩
          · rw [split0, dJ, open_, ← hj1v, bsplit, dK, hk93, ← hk1v, csplit]; simp
          · rw [hclose, hk1v, hblen, hj1v, h0v]; simp; omega
        · intro s2 rest envs' more split hs2 hrest nz
          obtain ⟨body', s3, rfl, hs3, henv, dk1, kv⟩ := afterSubset s2 rest envs' more split hs2 hrest nz
          obtain ⟨c, hc, hcv⟩ := c2 s3 more dk1 hs3
          simp only [core.result.Result.Ok.injEq] at hc; subst hc
          obtain ⟨rfl, _⟩ := reads s2 _ envs' more split hs2 hrest
          refine ⟨env, close, rfl, by rw [hview, envView_new, henv]; simp, ?_⟩
          rw [hcv, hk1v, kv, hj1v, h0v]; simp; omega
  · rw [if_neg (by simpa using open_)]
    by_cases gt : charAt cs j0.val = 62
    · rw [if_pos (by simpa using gt)]
      obtain ⟨inside, dJ⟩ := drop_nonzero (by rw [gt]; decide : charAt cs j0.val ≠ 0)
      obtain ⟨j1, hj1, hj1v⟩ := next_spec inside
      refine ⟨.Ok (alloc.vec.Vec.new _, j1), by simp [hj1], ?_, ?_⟩
      · intro env j e; simp at e; obtain ⟨rfl, rfl⟩ := e
        refine ⟨sp, [62], [], by rw [split0, dJ, gt, hj1v]; simp, all0, Or.inl ⟨rfl, rfl⟩, by simp [envView],
          fun _ => by intro e he; simp at he, by rw [hj1v, h0v]; simp⟩
      · intro s2 rest envs more split hs2 hrest nz
        obtain ⟨rfl, dj⟩ := reads s2 rest envs more split hs2 hrest
        rcases hrest with ⟨rfl, rfl⟩ | ⟨body, s3, rfl, _⟩
        · exact ⟨_, j1, rfl, by simp [envView], by rw [hj1v, h0v]; simp⟩
        · exfalso; rw [dJ, gt] at dj; simp at dj
    · rw [if_neg (by simpa using gt)]
      refine ⟨.Err ⟨.Syntax, j0⟩, by simp [xml.fail], by simp, ?_⟩
      intro s2 rest envs more split hs2 hrest nz
      exfalso
      obtain ⟨rfl, dj⟩ := reads s2 rest envs more split hs2 hrest
      rcases hrest with ⟨rfl, _⟩ | ⟨body, s3, rfl, _⟩
      · exact gt (first_char (c := 62) (rest := more) (by rw [dj]; simp))
      · exact open_ (first_char (c := 91) (rest := body ++ [93] ++ s3 ++ [62] ++ more) (by rw [dj]; simp))

theorem doctypeRest_head {rest : Word} {envs : Env} (h : DoctypeRest rest envs) :
    ∃ c m, rest = c :: m ∧ (c = 62 ∨ c = 91) := by
  rcases h with ⟨rfl, _⟩ | ⟨body, s3, rfl, _⟩
  · exact ⟨62, [], rfl, Or.inl rfl⟩
  · exact ⟨91, _, rfl, Or.inr rfl⟩

theorem doctype_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.doctype cs i = .ok r ∧
      (∀ env j, r = .Ok (env, j) → (j = i ∧ env.val = []) ∨
        (∃ dt envs, (word cs).drop i.val = dt ++ (word cs).drop j.val ∧ Doctype dt envs ∧ envView env = envs ∧
          (NoZero cs → EnvOk env))) ∧
      (¬ lit "<!DOCTYPE" <+: (word cs).drop i.val → r = .Ok (alloc.vec.Vec.new _, i)) ∧
      (∀ dt envs rest, (word cs).drop i.val = dt ++ rest → Doctype dt envs → NoZero cs →
        ∃ env j, r = .Ok (env, j) ∧ envView env = envs ∧ j.val = i.val + dt.length) := by
  unfold xml.doctype
  simp only [lift, bind_ok, starts_eq, bytes_make, map_doctype, decide_eq_true_eq]
  by_cases dd : lit "<!DOCTYPE" <+: (word cs).drop i.val
  · rw [if_pos dd]
    obtain ⟨d9, fit9⟩ := prefix_split dd (by rw [lit_doctype]; simp)
    have l9 : (lit "<!DOCTYPE").length = 9 := by rw [lit_doctype]; rfl
    rw [l9] at d9 fit9
    obtain ⟨i9, hi9, hi9v⟩ := skip_spec (cs := cs) (i := i) (c := 9#usize) (by simp; omega)
    have i9v : i9.val = i.val + 9 := by simpa using hi9v
    rw [← i9v] at d9
    simp only [hi9, bind_ok]
    -- the parts of a complete reading
    have parts : ∀ dt envs rest, (word cs).drop i.val = dt ++ rest → Doctype dt envs → ∃ s1 n p l ext s2 rest',
        (word cs).drop i9.val = s1 ++ (n ++ (ext ++ (s2 ++ (rest' ++ rest)))) ∧ S s1 ∧ QName n p l ∧
        (ext = [] ∨ ∃ s e, ext = s ++ e ∧ S s ∧ ExternalID e) ∧ OptS s2 ∧ DoctypeRest rest' envs ∧
        dt = lit "<!DOCTYPE" ++ s1 ++ n ++ ext ++ s2 ++ rest' := by
      intro dt envs rest split hdt
      obtain ⟨s1, n, p, l, ext, s2, rest', rfl, hs1, hq, hext, hs2, hrest⟩ := hdt
      refine ⟨s1, n, p, l, ext, s2, rest', ?_, hs1, hq, hext, hs2, hrest, rfl⟩
      rw [i9v]; have := drop_after (cs := cs) (i := i.val) (w := lit "<!DOCTYPE")
        (rest := s1 ++ (n ++ (ext ++ (s2 ++ (rest' ++ rest))))) (by rw [split]; simp)
      rw [l9] at this; exact this
    -- what follows the name is no name character
    have afterName : ∀ ext s2 rest' envs rest, (ext = [] ∨ ∃ s e, ext = s ++ e ∧ S s ∧ ExternalID e) →
        OptS s2 → DoctypeRest rest' envs → ∀ c m, ext ++ (s2 ++ (rest' ++ rest)) = c :: m → ¬ NameChar c := by
      intro ext s2 rest' envs rest hext hs2 hrest c m e
      rcases hext with rfl | ⟨s, e', rfl, hs, _⟩
      · cases s2 with
        | nil =>
          obtain ⟨c0, m0, rfl, hc0⟩ := doctypeRest_head hrest
          simp at e; rw [← e.1]; rcases hc0 with rfl | rfl <;> simp [NameChar, NameStartChar]
        | cons c2 s2' => simp at e; rw [← e.1]; exact not_name_space (hs2 c2 (by simp))
      · exact spaces_head_not_name (rest := e' ++ (s2 ++ (rest' ++ rest))) hs c m (by rw [← e]; simp)
    obtain ⟨r1, h1, s1⟩ := spaces_sound cs i9
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp,
        fun h => absurd dd h, ?_⟩
      intro dt envs rest split hdt nz
      obtain ⟨s1', n, p, l, ext, s2, rest', d1, hs1, hq, _⟩ := parts dt envs rest split hdt
      obtain ⟨c0, r0, e0, hc0, _⟩ := qname_name hq
      obtain ⟨m, hm, _⟩ := spaces_complete cs i9 d1 hs1 (by
        intro c m' e; rw [e0] at e; simp at e; rw [← e.1]; intro sp; exact not_name_space sp (Or.inl hc0))
      exact (ok_ne_err h1 hm).elim
    | Ok j =>
      obtain ⟨sp1, sp1split, hsp1, hj⟩ := s1 j rfl
      have atJ : ∀ dt envs rest, (word cs).drop i.val = dt ++ rest → Doctype dt envs → ∃ n p l ext s2 rest',
          (word cs).drop j.val = n ++ (ext ++ (s2 ++ (rest' ++ rest))) ∧ QName n p l ∧
          (ext = [] ∨ ∃ s e, ext = s ++ e ∧ S s ∧ ExternalID e) ∧ OptS s2 ∧ DoctypeRest rest' envs ∧
          dt.length = j.val - i.val + n.length + ext.length + s2.length + rest'.length := by
        intro dt envs rest split hdt
        obtain ⟨s1', n, p, l, ext, s2, rest', d1, hs1, hq, hext, hs2, hrest, rfl⟩ := parts dt envs rest split hdt
        obtain ⟨c0, r0, e0, hc0, _⟩ := qname_name hq
        obtain ⟨m, hm, hmv⟩ := spaces_complete cs i9 d1 hs1 (by
          intro c m' e; rw [e0] at e; simp at e; rw [← e.1]; intro sp; exact not_name_space sp (Or.inl hc0))
        have em := ok_inj h1 hm; rw [← em] at hmv
        refine ⟨n, p, l, ext, s2, rest', by rw [hmv]; exact drop_after d1, hq, hext, hs2, hrest, ?_⟩
        simp [lit_doctype]; omega
      obtain ⟨r2, h2, s2', c2⟩ := qname_spec cs j
      cases r2 with
      | Err err =>
        refine ⟨.Err err, by simp [h1, h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp,
          fun h => absurd dd h, ?_⟩
        intro dt envs rest split hdt nz
        obtain ⟨n, p, l, ext, s2, rest', dj, hq, hext, hs2, hrest, _⟩ := atJ dt envs rest split hdt
        have nr : nameRun cs j.val = n :=
          nameRun_eq dj (name_all (qname_name hq)) (afterName ext s2 rest' envs rest hext hs2 hrest)
        obtain ⟨stop, mark, hsm⟩ := c2 p l (by rw [nr]; exact hq)
        cases hsm
      | Ok pair =>
        obtain ⟨nend, mark⟩ := pair
        obtain ⟨hne, p, l, hq, _⟩ := s2' nend mark rfl
        have nsplit := nameRun_split cs j.val
        rw [← hne] at nsplit
        obtain ⟨r3, h3, s3, c3a, c3b⟩ := doctype_external_spec cs nend
        have atEnd : ∀ dt envs rest, (word cs).drop i.val = dt ++ rest → Doctype dt envs → ∃ ext s2 rest',
            (word cs).drop nend.val = ext ++ (s2 ++ (rest' ++ rest)) ∧
            (ext = [] ∨ ∃ s e, ext = s ++ e ∧ S s ∧ ExternalID e) ∧ OptS s2 ∧ DoctypeRest rest' envs ∧
            dt.length = nend.val - i.val + ext.length + s2.length + rest'.length := by
          intro dt envs rest split hdt
          obtain ⟨n, p', l', ext, s2, rest', dj, hq', hext, hs2, hrest, hlen⟩ := atJ dt envs rest split hdt
          have nr : nameRun cs j.val = n :=
            nameRun_eq dj (name_all (qname_name hq')) (afterName ext s2 rest' envs rest hext hs2 hrest)
          rw [nr] at hne
          refine ⟨ext, s2, rest', by rw [hne]; exact drop_after dj, hext, hs2, hrest, by omega⟩
        cases r3 with
        | Err err =>
          refine ⟨.Err err, by simp [h1, h2, h3, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
            by simp, fun h => absurd dd h, ?_⟩
          intro dt envs rest split hdt nz
          obtain ⟨ext, s2, rest', de, hext, hs2, hrest, _⟩ := atEnd dt envs rest split hdt
          obtain ⟨c0, m0, e0, hc0⟩ := doctypeRest_head hrest
          rcases hext with rfl | ⟨s, e', rfl, hs, he'⟩
          · have := c3a s2 c0 (m0 ++ rest) (by rw [de, e0]; simp) hs2 hc0
            cases this
          · obtain ⟨k, hk, _⟩ := c3b s e' (s2 ++ (rest' ++ rest)) (by rw [de]) hs he'
              (nz_of_drop nz (rest := s2 ++ (rest' ++ rest)) (i := nend.val + s.length) (by
                have := drop_after (cs := cs) (i := nend.val) (w := s) (rest := e' ++ (s2 ++ (rest' ++ rest)))
                  (by rw [de]; simp)
                rw [this]))
            cases hk
        | Ok k =>
          obtain ⟨r4, h4, s4, c4⟩ := doctype_rest_spec cs k
          refine ⟨r4, by simp [h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch], ?_,
            fun h => absurd dd h, ?_⟩
          · intro env close e
            obtain ⟨s2, rest', envs, rsplit, hs2, hrest, hview, hok, _⟩ := s4 env close e
            right
            rcases s3 k rfl with rfl | ⟨s, e', esplit, hs, he', hk⟩
            · refine ⟨lit "<!DOCTYPE" ++ sp1 ++ nameRun cs j.val ++ [] ++ s2 ++ rest', envs, ?_, ?_, hview, hok⟩
              · rw [d9, sp1split, nsplit, rsplit]; simp
              · obtain ⟨c0, m0, e0, hc0⟩ := doctypeRest_head hrest
                exact ⟨sp1, nameRun cs j.val, p, l, [], s2, rest', rfl, hsp1, hq, Or.inl rfl, hs2, hrest⟩
            · refine ⟨lit "<!DOCTYPE" ++ sp1 ++ nameRun cs j.val ++ (s ++ e') ++ s2 ++ rest', envs, ?_, ?_, hview, hok⟩
              · rw [d9, sp1split, nsplit, esplit, rsplit]; simp
              · exact ⟨sp1, nameRun cs j.val, p, l, s ++ e', s2, rest', rfl, hsp1, hq, Or.inr ⟨s, e', rfl, hs, he'⟩,
                  hs2, hrest⟩
          · intro dt envs rest split hdt nz
            obtain ⟨ext, s2, rest', de, hext, hs2, hrest, hlen⟩ := atEnd dt envs rest split hdt
            have atK : (word cs).drop k.val = s2 ++ rest' ++ rest ∧ k.val = nend.val + ext.length := by
              obtain ⟨c0, m0, e0, hc0⟩ := doctypeRest_head hrest
              rcases hext with rfl | ⟨s, e', rfl, hs, he'⟩
              · have := c3a s2 c0 (m0 ++ rest) (by rw [de, e0]; simp) hs2 hc0
                simp only [core.result.Result.Ok.injEq] at this; subst this
                exact ⟨by simpa using de, by simp⟩
              · obtain ⟨k', hk', hk'v⟩ := c3b s e' (s2 ++ (rest' ++ rest)) (by rw [de]) hs he'
                  (nz_of_drop nz (rest := s2 ++ (rest' ++ rest)) (i := nend.val + s.length) (by
                    have := drop_after (cs := cs) (i := nend.val) (w := s) (rest := e' ++ (s2 ++ (rest' ++ rest)))
                      (by rw [de]; simp)
                    rw [this]))
                simp only [core.result.Result.Ok.injEq] at hk'; subst hk'
                refine ⟨?_, by rw [hk'v]; simp; omega⟩
                rw [hk'v]; have := drop_after (cs := cs) (i := nend.val) (w := s ++ e') (rest := s2 ++ (rest' ++ rest))
                  (by rw [de])
                simpa [Nat.add_assoc] using this
            obtain ⟨dk, hkv⟩ := atK
            obtain ⟨env, close, hr, hview, hclose⟩ := c4 s2 rest' envs rest dk hs2 hrest nz
            refine ⟨env, close, hr, hview, ?_⟩
            omega
  · rw [if_neg dd]
    refine ⟨.Ok (alloc.vec.Vec.new _, i), rfl, ?_, fun _ => rfl, ?_⟩
    · intro env j e; simp at e; obtain ⟨rfl, rfl⟩ := e; exact Or.inl ⟨rfl, rfl⟩
    · intro dt envs rest split hdt _
      exfalso; apply dd
      obtain ⟨s1, n, p, l, ext, s2, rest', rfl, _⟩ := hdt
      rw [split]; exact ⟨s1 ++ n ++ ext ++ s2 ++ rest' ++ rest, by simp⟩

end Rowl.XmlDocument
