import Rowl.XmlDoctype

/-!
# The internal subset

`entity_declaration` reads a `GEDecl` or a `PEDecl`, and `internal_subset`
reads the grammar's `intSubset` (entity declarations, comments, processing
instructions and white space) with the general entities it declares.
-/

namespace Rowl.XmlSubset
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs Rowl.XmlEntities Rowl.XmlAttributes Rowl.XmlTags Rowl.XmlNamespaces Rowl.XmlContent Rowl.XmlElements Rowl.XmlComplete Rowl.XmlDecl Rowl.XmlLiterals Rowl.XmlEntityDecls Rowl.XmlDoctype
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

theorem lit_entity : lit "<!ENTITY" = [60, 33, 69, 78, 84, 73, 84, 89] := by decide
theorem map_entity : ([60#u8, 33#u8, 69#u8, 78#u8, 84#u8, 73#u8, 84#u8, 89#u8] : List U8).map (·.val) =
    lit "<!ENTITY" := by decide

theorem name_start_ne_37 {n : Word} (h : NCName n) : ∀ c m, n = c :: m → c ≠ 37 := by
  intro c m e hc
  obtain ⟨c0, r0, e0, h0, _⟩ := h.1
  rw [e0] at e; simp at e; rw [e.1, hc] at h0; simp [NameStartChar] at h0

theorem entity_declaration_spec (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity)
    (start : lit "<!ENTITY" <+: (word cs).drop i.val) :
    ∃ r, xml.entity_declaration cs i env = .ok r ∧
      (∀ env' k, r = .Ok (env', k) → ∃ d, (word cs).drop i.val = d ++ (word cs).drop k.val ∧
        k.val = i.val + d.length ∧
        ((∃ decl, GEDecl d decl ∧ envView env' = envView env ++ [decl]) ∨ (PEDecl d ∧ env' = env)) ∧
        (EnvOk env → NoZero cs → EnvOk env')) ∧
      (∀ d rest, (word cs).drop i.val = d ++ rest → NoZero cs → env.val.length < Usize.max →
        (∀ decl, GEDecl d decl → ∃ env' k, r = .Ok (env', k) ∧ k.val = i.val + d.length ∧
          envView env' = envView env ++ [decl]) ∧
        (PEDecl d → ∃ k, r = .Ok (env, k) ∧ k.val = i.val + d.length)) := by
  unfold xml.entity_declaration
  obtain ⟨d8, fit8⟩ := prefix_split start (by rw [lit_entity]; simp)
  have l8 : (lit "<!ENTITY").length = 8 := by rw [lit_entity]; rfl
  rw [l8] at d8 fit8
  obtain ⟨i8, hi8, hi8v⟩ := skip_spec (cs := cs) (i := i) (c := 8#usize) (by simp; omega)
  have i8v : i8.val = i.val + 8 := by simpa using hi8v
  rw [← i8v] at d8
  simp only [hi8, bind_ok]
  -- the parts of complete readings after `<!ENTITY`
  have geParts : ∀ d rest decl, (word cs).drop i.val = d ++ rest → GEDecl d decl → ∃ s1 n s2 d' df s3,
      (word cs).drop i8.val = s1 ++ (n ++ s2 ++ d' ++ s3 ++ 62 :: rest) ∧ S s1 ∧ NCName n ∧ S s2 ∧
      EntityDef d' df ∧ OptS s3 ∧ decl = (n, df) ∧ d = lit "<!ENTITY" ++ s1 ++ n ++ s2 ++ d' ++ s3 ++ [62] := by
    intro d rest decl split hd
    obtain ⟨s1, n, s2, d', df, s3, rfl, hs1, hn, hs2, hd', hs3, rfl⟩ := hd
    refine ⟨s1, n, s2, d', df, s3, ?_, hs1, hn, hs2, hd', hs3, rfl, rfl⟩
    rw [i8v]; have := drop_after (cs := cs) (i := i.val) (w := lit "<!ENTITY")
      (rest := s1 ++ (n ++ s2 ++ d' ++ s3 ++ 62 :: rest)) (by rw [split]; simp)
    rw [l8] at this; exact this
  have peParts : ∀ d rest, (word cs).drop i.val = d ++ rest → PEDecl d → ∃ s1 s2 n s3 d' s4,
      (word cs).drop i8.val = s1 ++ ([37] ++ s2 ++ n ++ s3 ++ d' ++ s4 ++ 62 :: rest) ∧ S s1 ∧ S s2 ∧ NCName n ∧
      S s3 ∧ ((∃ t, EntityValue d' t) ∨ ExternalID d') ∧ OptS s4 ∧
      d = lit "<!ENTITY" ++ s1 ++ [37] ++ s2 ++ n ++ s3 ++ d' ++ s4 ++ [62] := by
    intro d rest split hd
    obtain ⟨s1, s2, n, s3, d', s4, rfl, hs1, hs2, hn, hs3, hd', hs4⟩ := hd
    refine ⟨s1, s2, n, s3, d', s4, ?_, hs1, hs2, hn, hs3, hd', hs4, rfl⟩
    rw [i8v]; have := drop_after (cs := cs) (i := i.val) (w := lit "<!ENTITY")
      (rest := s1 ++ ([37] ++ s2 ++ n ++ s3 ++ d' ++ s4 ++ 62 :: rest)) (by rw [split]; simp)
    rw [l8] at this; exact this
  obtain ⟨r1, h1, s1⟩ := spaces_sound cs i8
  cases r1 with
  | Err err =>
    refine ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
    intro d rest split nz room
    refine ⟨fun decl hd => ?_, fun hd => ?_⟩
    · obtain ⟨s1, n, s2, d', df, s3, d1, hs1, hn, _⟩ := geParts d rest decl split hd
      obtain ⟨m, hm, _⟩ := spaces_complete cs i8 d1 hs1
        (by have := head_append (rest := s2 ++ d' ++ s3 ++ 62 :: rest) (name_not_space hn) (name_ne hn)
            simpa using this)
      exact (ok_ne_err h1 hm).elim
    · obtain ⟨s1, s2, n, s3, d', s4, d1, hs1, _⟩ := peParts d rest split hd
      obtain ⟨m, hm, _⟩ := spaces_complete cs i8 d1 hs1 (by intro c m e; simp at e; rw [e.1]; simp [IsSpace])
      exact (ok_ne_err h1 hm).elim
  | Ok j =>
    obtain ⟨sp1, sp1split, hsp1, hj⟩ := s1 j rfl
    -- where complete readings continue
    have geAt : ∀ d rest decl, (word cs).drop i.val = d ++ rest → GEDecl d decl → ∃ n s2 d' df s3,
        (word cs).drop j.val = n ++ s2 ++ d' ++ s3 ++ 62 :: rest ∧ NCName n ∧ S s2 ∧ EntityDef d' df ∧ OptS s3 ∧
        decl = (n, df) ∧ d.length = j.val - i.val + n.length + s2.length + d'.length + s3.length + 1 := by
      intro d rest decl split hd
      obtain ⟨s1', n, s2, d', df, s3, d1, hs1, hn, hs2, hd', hs3, hdecl, rfl⟩ := geParts d rest decl split hd
      obtain ⟨m, hm, hmv⟩ := spaces_complete cs i8 d1 hs1
        (by have := head_append (rest := s2 ++ d' ++ s3 ++ 62 :: rest) (name_not_space hn) (name_ne hn)
            simpa using this)
      have em := ok_inj h1 hm; rw [← em] at hmv
      refine ⟨n, s2, d', df, s3, by rw [hmv]; simpa using drop_after d1, hn, hs2, hd', hs3, hdecl, ?_⟩
      simp [lit_entity]; omega
    have peAt : ∀ d rest, (word cs).drop i.val = d ++ rest → PEDecl d → ∃ s2 n s3 d' s4,
        (word cs).drop j.val = [37] ++ s2 ++ n ++ s3 ++ d' ++ s4 ++ 62 :: rest ∧ S s2 ∧ NCName n ∧ S s3 ∧
        ((∃ t, EntityValue d' t) ∨ ExternalID d') ∧ OptS s4 ∧
        d.length = j.val - i.val + 1 + s2.length + n.length + s3.length + d'.length + s4.length + 1 := by
      intro d rest split hd
      obtain ⟨s1', s2, n, s3, d', s4, d1, hs1, hs2, hn, hs3, hd', hs4, rfl⟩ := peParts d rest split hd
      obtain ⟨m, hm, hmv⟩ := spaces_complete cs i8 d1 hs1 (by intro c m e; simp at e; rw [e.1]; simp [IsSpace])
      have em := ok_inj h1 hm; rw [← em] at hmv
      refine ⟨s2, n, s3, d', s4, by rw [hmv]; simpa using drop_after d1, hs2, hn, hs3, hd', hs4, ?_⟩
      simp [lit_entity]; omega
    have geFirst : ∀ d rest decl, (word cs).drop i.val = d ++ rest → GEDecl d decl → charAt cs j.val ≠ 37 := by
      intro d rest decl split hd
      obtain ⟨n, s2', d', df, s3, dj, hn, _⟩ := geAt d rest decl split hd
      obtain ⟨c0, r0, e0⟩ := List.exists_cons_of_ne_nil (name_ne hn)
      rw [first_char (c := c0) (rest := r0 ++ s2' ++ d' ++ s3 ++ 62 :: rest) (by rw [dj, e0]; simp)]
      exact name_start_ne_37 hn c0 r0 e0
    have peFirst : ∀ d rest, (word cs).drop i.val = d ++ rest → PEDecl d → charAt cs j.val = 37 := by
      intro d rest split hd
      obtain ⟨s2', n, s3, d', s4, dj, _⟩ := peAt d rest split hd
      exact first_char (rest := s2' ++ n ++ s3 ++ d' ++ s4 ++ 62 :: rest) (by rw [dj]; simp)
    have dsplit : (word cs).drop i.val = lit "<!ENTITY" ++ sp1 ++ (word cs).drop j.val := by
      rw [d8, sp1split]; simp
    have jlen : j.val = i.val + 8 + sp1.length := by omega
    simp only [h1, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, at_eq, atU_eq_iff]
    by_cases pct : charAt cs j.val = 37
    · rw [if_pos (by simpa using pct)]
      obtain ⟨r2, h2, s2, c2⟩ := parameter_declaration_spec cs j pct
      cases r2 with
      | Err err =>
        refine ⟨.Err err, by simp [h2, same_residual], by simp, ?_⟩
        intro d rest split nz room
        refine ⟨fun decl hd => absurd pct (geFirst d rest decl split hd), fun hd => ?_⟩
        obtain ⟨s2', n, s3, d', s4, dj, hs2, hn, hs3, hd', hs4, _⟩ := peAt d rest split hd
        obtain ⟨k, hk, _⟩ := c2 s2' n s3 d' s4 rest dj hs2 hn hs3 hd' hs4
          (nz_of_drop nz (rest := s4 ++ 62 :: rest) (i := j.val + ([37] ++ s2' ++ n ++ s3).length) (by
            have := drop_after (cs := cs) (i := j.val) (w := [37] ++ s2' ++ n ++ s3) (rest := d' ++ s4 ++ 62 :: rest)
              (by rw [dj]; simp)
            rw [this]; simp))
        cases hk
      | Ok k =>
        refine ⟨.Ok (env, k), by simp [h2], ?_, ?_⟩
        · intro env' k' e; simp at e; obtain ⟨rfl, rfl⟩ := e
          obtain ⟨s2', n, s3, d', s4, ksplit, hs2, hn, hs3, hd', hs4, hk⟩ := s2 k rfl
          refine ⟨lit "<!ENTITY" ++ sp1 ++ [37] ++ s2' ++ n ++ s3 ++ d' ++ s4 ++ [62], ?_, ?_,
            Or.inr ⟨⟨sp1, s2', n, s3, d', s4, rfl, hsp1, hs2, hn, hs3, hd', hs4⟩, rfl⟩, fun h _ => h⟩
          · rw [dsplit, ksplit]; simp
          · rw [hk, jlen]; simp [lit_entity]; omega
        · intro d rest split nz room
          refine ⟨fun decl hd => absurd pct (geFirst d rest decl split hd), fun hd => ?_⟩
          obtain ⟨s2', n, s3, d', s4, dj, hs2, hn, hs3, hd', hs4, dlen⟩ := peAt d rest split hd
          obtain ⟨k', hk', hk'v⟩ := c2 s2' n s3 d' s4 rest dj hs2 hn hs3 hd' hs4
            (nz_of_drop nz (rest := s4 ++ 62 :: rest) (i := j.val + ([37] ++ s2' ++ n ++ s3).length) (by
              have := drop_after (cs := cs) (i := j.val) (w := [37] ++ s2' ++ n ++ s3) (rest := d' ++ s4 ++ 62 :: rest)
                (by rw [dj]; simp)
              rw [this]; simp))
          simp only [core.result.Result.Ok.injEq] at hk'; subst hk'
          exact ⟨_, rfl, by rw [hk'v, dlen]; omega⟩
    · rw [if_neg (by simpa using pct)]
      obtain ⟨r2, h2, s2, c2⟩ := general_declaration_spec cs i j env
      refine ⟨r2, h2, ?_, ?_⟩
      · intro env' k e
        obtain ⟨n, s2', d', df, s3, ksplit, hn, hs2, hd', hs3, hk, hview, hok⟩ := s2 env' k e
        refine ⟨lit "<!ENTITY" ++ sp1 ++ n ++ s2' ++ d' ++ s3 ++ [62], ?_, ?_,
          Or.inl ⟨(n, df), ⟨sp1, n, s2', d', df, s3, rfl, hsp1, hn, hs2, hd', hs3, rfl⟩, hview⟩, hok⟩
        · rw [dsplit, ksplit]; simp
        · rw [hk, jlen]; simp [lit_entity]; omega
      · intro d rest split nz room
        refine ⟨fun decl hd => ?_, fun hd => absurd (peFirst d rest split hd) pct⟩
        obtain ⟨n, s2', d', df, s3, dj, hn, hs2, hd', hs3, rfl, dlen⟩ := geAt d rest decl split hd
        obtain ⟨env', k, hk, hkv, hview⟩ := c2 n s2' d' df s3 rest dj hn hs2 hd' hs3
          (nz_of_drop nz (rest := s3 ++ 62 :: rest) (i := j.val + (n ++ s2').length) (by
            have := drop_after (cs := cs) (i := j.val) (w := n ++ s2') (rest := d' ++ s3 ++ 62 :: rest)
              (by rw [dj]; simp)
            rw [this]; simp)) room
        exact ⟨env', k, hk, by rw [hkv, dlen]; omega, hview⟩

/-! ## The internal subset -/

theorem map_element_decl : ([60#u8, 33#u8, 69#u8, 76#u8, 69#u8, 77#u8, 69#u8, 78#u8, 84#u8] : List U8).map (·.val) =
    lit "<!ELEMENT" := by decide
theorem map_attlist : ([60#u8, 33#u8, 65#u8, 84#u8, 84#u8, 76#u8, 73#u8, 83#u8, 84#u8] : List U8).map (·.val) =
    lit "<!ATTLIST" := by decide
theorem map_notation :
    ([60#u8, 33#u8, 78#u8, 79#u8, 84#u8, 65#u8, 84#u8, 73#u8, 79#u8, 78#u8] : List U8).map (·.val) =
      lit "<!NOTATION" := by decide

/-- What begins at a position in the internal subset. -/
def subsetRuleOf (cs : alloc.vec.Vec U32) (i : Nat) : xml.SubsetRule :=
  if charAt cs i = 93 then .Close
  else if charAt cs i = 37 then .Unsupported
  else if lit "<!ENTITY" <+: (word cs).drop i then .Entity
  else if lit "<!--" <+: (word cs).drop i then .Comment
  else if lit "<?" <+: (word cs).drop i then .Pi
  else if lit "<!ELEMENT" <+: (word cs).drop i ∨ lit "<!ATTLIST" <+: (word cs).drop i ∨
    lit "<!NOTATION" <+: (word cs).drop i then .Unsupported
  else .Invalid

theorem subset_rule_eq (cs : alloc.vec.Vec U32) (i : Usize) : xml.subset_rule cs i = .ok (subsetRuleOf cs i.val) := by
  unfold xml.subset_rule xml.declaration_rule xml.other_declaration subsetRuleOf
  simp only [at_eq, atU_eq_iff, bind_ok, lift, starts_eq, bytes_make, map_entity, map_comment_bytes, map_pi_start,
    map_element_decl, map_attlist, map_notation, decide_eq_true_eq]
  by_cases a : charAt cs i.val = 93
  · simp [a]
  · by_cases b : charAt cs i.val = 37
    · simp [b]
    · have a' : ¬ charAt cs i.val = (93#u32 : U32).val := by simpa using a
      have b' : ¬ charAt cs i.val = (37#u32 : U32).val := by simpa using b
      rw [if_neg a', if_neg a, if_neg b', if_neg b]
      split_ifs <;> simp_all

theorem intSubset_spaces {sp body : Word} {envs : Env} (hsp : OptS sp) (h : IntSubset body envs) :
    IntSubset (sp ++ body) envs := by
  by_cases e : sp = []
  · subst e; simpa using h
  · exact IntSubset.space ⟨e, hsp⟩ h

theorem internal_subset_sound (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity) :
    ∃ r, xml.internal_subset cs i env = .ok r ∧
      ∀ env' j, r = .Ok (env', j) → ∃ body envs, (word cs).drop i.val = body ++ (word cs).drop j.val ∧
        charAt cs j.val = 93 ∧ IntSubset body envs ∧ envView env' = envView env ++ envs ∧
        (EnvOk env → NoZero cs → EnvOk env') := by
  rw [xml.internal_subset]
  obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
  have split0 := drop_run IsSpace cs i.val
  rw [← h0v] at split0
  have all0 : ∀ c ∈ run IsSpace ((word cs).drop i.val), IsSpace c := run_all
  generalize hr0 : run IsSpace ((word cs).drop i.val) = sp at split0 h0v all0
  simp only [h0, bind_ok, subset_rule_eq]
  unfold subsetRuleOf
  by_cases close : charAt cs j0.val = 93
  · simp only [close, ite_true]
    refine ⟨.Ok (env, j0), rfl, ?_⟩
    intro env' j e; simp at e; obtain ⟨rfl, rfl⟩ := e
    exact ⟨sp, [], split0, close, by simpa using intSubset_spaces all0 IntSubset.nil, by simp, fun h _ => h⟩
  · rw [if_neg close]
    by_cases pct : charAt cs j0.val = 37
    · rw [if_pos pct]
      exact ⟨.Err ⟨.UnsupportedDeclaration, j0⟩, by simp [xml.fail], by simp⟩
    · rw [if_neg pct]
      by_cases ent : lit "<!ENTITY" <+: (word cs).drop j0.val
      · rw [if_pos ent]
        obtain ⟨r1, h1, s1, _⟩ := entity_declaration_spec cs j0 env ent
        cases r1 with
        | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
        | Ok pair =>
          obtain ⟨env1, k⟩ := pair
          obtain ⟨d, dsplit, hk, hdecl, hok⟩ := s1 env1 k rfl
          have dne : d ≠ [] := by
            rcases hdecl with ⟨decl, ⟨s1', n, s2, d', df, s3, rfl, _⟩, _⟩ | ⟨⟨s1', s2, n, s3, d', s4, rfl, _⟩, _⟩ <;>
              simp [lit_entity]
          have progress : cs.val.length - k.val < cs.val.length - i.val := by
            apply drop_lt (w := sp ++ d) _ (by simp [dne]); rw [split0, dsplit]; simp
          obtain ⟨r2, h2, s2⟩ := internal_subset_sound cs k env1
          refine ⟨r2, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_⟩
          intro env' j e
          obtain ⟨body, envs, bsplit, hj93, hbody, hview, hok2⟩ := s2 env' j e
          rcases hdecl with ⟨decl, hd, hv1⟩ | ⟨hd, rfl⟩
          · refine ⟨sp ++ (d ++ body), decl :: envs, by rw [split0, dsplit, bsplit]; simp, hj93,
              intSubset_spaces all0 (IntSubset.general hd hbody), by rw [hview, hv1]; simp,
              fun h nz => hok2 (hok h nz) nz⟩
          · refine ⟨sp ++ (d ++ body), envs, by rw [split0, dsplit, bsplit]; simp, hj93,
              intSubset_spaces all0 (IntSubset.parameter hd hbody), hview, hok2⟩
      · rw [if_neg ent]
        by_cases com : lit "<!--" <+: (word cs).drop j0.val
        · rw [if_pos com]
          obtain ⟨r1, h1, s1, _⟩ := comment_spec cs j0 com
          cases r1 with
          | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
          | Ok k =>
            obtain ⟨cw, csplit, hcw⟩ := s1 k rfl
            have cne : cw ≠ [] := by obtain ⟨body, rfl, _⟩ := hcw; simp [lit]
            have progress : cs.val.length - k.val < cs.val.length - i.val := by
              apply drop_lt (w := sp ++ cw) _ (by simp [cne]); rw [split0, csplit]; simp
            obtain ⟨r2, h2, s2⟩ := internal_subset_sound cs k env
            refine ⟨r2, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_⟩
            intro env' j e
            obtain ⟨body, envs, bsplit, hj93, hbody, hview, hok2⟩ := s2 env' j e
            exact ⟨sp ++ (cw ++ body), envs, by rw [split0, csplit, bsplit]; simp, hj93,
              intSubset_spaces all0 (IntSubset.comment hcw hbody), hview, hok2⟩
        · rw [if_neg com]
          by_cases hpi : lit "<?" <+: (word cs).drop j0.val
          · rw [if_pos hpi]
            obtain ⟨r1, h1, s1, _⟩ := pi_spec cs j0 hpi
            cases r1 with
            | Err err =>
              exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
            | Ok k =>
              obtain ⟨cw, csplit, hcw⟩ := s1 k rfl
              have cne : cw ≠ [] := by obtain ⟨t, rest', rfl, _, _⟩ := hcw; simp [lit]
              have progress : cs.val.length - k.val < cs.val.length - i.val := by
                apply drop_lt (w := sp ++ cw) _ (by simp [cne]); rw [split0, csplit]; simp
              obtain ⟨r2, h2, s2⟩ := internal_subset_sound cs k env
              refine ⟨r2, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_⟩
              intro env' j e
              obtain ⟨body, envs, bsplit, hj93, hbody, hview, hok2⟩ := s2 env' j e
              exact ⟨sp ++ (cw ++ body), envs, by rw [split0, csplit, bsplit]; simp, hj93,
                intSubset_spaces all0 (IntSubset.pi hcw hbody), hview, hok2⟩
          · rw [if_neg hpi]
            split_ifs
            · exact ⟨.Err ⟨.UnsupportedDeclaration, j0⟩, by simp [xml.fail], by simp⟩
            · exact ⟨.Err ⟨.Syntax, j0⟩, by simp [xml.fail], by simp⟩
termination_by cs.val.length - i.val
decreasing_by all_goals omega

theorem geDecl_head {d : Word} {decl : Word × Def} (h : GEDecl d decl) : lit "<!ENTITY" <+: d := by
  obtain ⟨s1, n, s2, d', df, s3, rfl, _⟩ := h; exact ⟨s1 ++ n ++ s2 ++ d' ++ s3 ++ [62], by simp⟩

theorem peDecl_head {d : Word} (h : PEDecl d) : lit "<!ENTITY" <+: d := by
  obtain ⟨s1, s2, n, s3, d', s4, rfl, _⟩ := h; exact ⟨s1 ++ [37] ++ s2 ++ n ++ s3 ++ d' ++ s4 ++ [62], by simp⟩

/-- Reading at a position the internal subset continues with `d`. -/
theorem subset_step {cs : alloc.vec.Vec U32} {i : Usize} {sp d more : Word}
    (split : (word cs).drop i.val = sp ++ d ++ more) (hsp : OptS sp) (hd : lit "<" <+: d) :
    ∃ j0, xml.skip_spaces cs i = .ok j0 ∧ j0.val = i.val + sp.length ∧ (word cs).drop j0.val = d ++ more := by
  obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
  obtain ⟨t, rfl⟩ := hd
  have rs : run IsSpace ((word cs).drop i.val) = sp := by
    rw [split]; have := run_unique (rest := lit "<" ++ t ++ more) hsp (head_not_space (q := 60) (x := t ++ more)
      (by simp [IsSpace])); simpa [lit] using this
  rw [rs] at h0v
  have da := drop_after (cs := cs) (i := i.val) (w := sp) (rest := lit "<" ++ t ++ more) (by rw [split]; simp)
  exact ⟨j0, h0, h0v, by rw [h0v, da]⟩

theorem internal_subset_complete {body : Word} {envs : Env} (h : IntSubset body envs) :
    ∀ (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity) (sp rest : Word),
      (word cs).drop i.val = sp ++ body ++ 93 :: rest → OptS sp → NoZero cs →
      env.val.length + (cs.val.length - i.val) ≤ Usize.max →
      ∃ env' j, xml.internal_subset cs i env = .ok (.Ok (env', j)) ∧ j.val = i.val + sp.length + body.length ∧
        envView env' = envView env ++ envs := by
  induction h with
  | nil =>
    intro cs i env sp rest split hsp nz room
    rw [xml.internal_subset]
    obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
    have rs : run IsSpace ((word cs).drop i.val) = sp := by
      rw [split]; have := run_unique (rest := 93 :: rest) hsp (head_not_space (q := 93) (by simp [IsSpace]))
      simpa using this
    rw [rs] at h0v
    have c93 : charAt cs j0.val = 93 := by
      rw [h0v]; have := charAt_after (rest := 93 :: rest) (by rw [split]; simp : (word cs).drop i.val = sp ++ 93 :: rest)
      simpa using this
    refine ⟨env, j0, ?_, by simp [h0v], by simp⟩
    simp only [h0, bind_ok, subset_rule_eq]; unfold subsetRuleOf; simp [c93]
  | @general d rest' decl envs' hd hrest ih =>
    intro cs i env sp rest split hsp nz room
    rw [xml.internal_subset]
    obtain ⟨j0, h0, h0v, d0⟩ := subset_step (d := d) (more := rest' ++ 93 :: rest) (by rw [split]; simp) hsp
      (by obtain ⟨t, ht⟩ := geDecl_head hd; rw [← ht, lit_entity]; exact ⟨_, rfl⟩)
    have ent : lit "<!ENTITY" <+: (word cs).drop j0.val := by
      obtain ⟨t, ht⟩ := geDecl_head hd; rw [d0, ← ht]; exact ⟨t ++ (rest' ++ 93 :: rest), by simp⟩
    have c60 : charAt cs j0.val = 60 := by
      obtain ⟨t, ht⟩ := ent; rw [lit_entity] at ht; exact first_char (by rw [← ht]; rfl)
    have dne : d ≠ [] := by obtain ⟨t, ht⟩ := geDecl_head hd; rw [← ht, lit_entity]; simp
    have dlen := List.length_pos_of_ne_nil dne
    obtain ⟨r1, h1, _, c1⟩ := entity_declaration_spec cs j0 env ent
    have fit := drop_length_le (rest := rest' ++ 93 :: rest) d0
    obtain ⟨env1, k, hk, hkv, hview⟩ := (c1 d (rest' ++ 93 :: rest) d0 nz (by
      have := consumed_le split (by simp [dne]); simp at this; omega)).1 decl hd
    subst hk
    have dk : (word cs).drop k.val = [] ++ rest' ++ 93 :: rest := by rw [hkv]; simpa using drop_after d0
    obtain ⟨env', j, hj, hjv, hview'⟩ := ih cs k env1 [] rest dk (by simp [OptS]) nz (by
      have := congrArg List.length hview; simp [envView_length] at this
      have := consumed_le split (by simp [dne]); simp at this; omega)
    refine ⟨env', j, ?_, by rw [hjv, hkv, h0v]; simp; omega, by rw [hview', hview]; simp⟩
    simp only [h0, bind_ok, subset_rule_eq]; unfold subsetRuleOf
    simp only [c60, show (60 : Nat) ≠ 93 by decide, show (60 : Nat) ≠ 37 by decide, ite_false, if_pos ent, h1,
      core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    simpa using hj
  | @parameter d rest' envs' hd hrest ih =>
    intro cs i env sp rest split hsp nz room
    rw [xml.internal_subset]
    obtain ⟨j0, h0, h0v, d0⟩ := subset_step (d := d) (more := rest' ++ 93 :: rest) (by rw [split]; simp) hsp
      (by obtain ⟨t, ht⟩ := peDecl_head hd; rw [← ht, lit_entity]; exact ⟨_, rfl⟩)
    have ent : lit "<!ENTITY" <+: (word cs).drop j0.val := by
      obtain ⟨t, ht⟩ := peDecl_head hd; rw [d0, ← ht]; exact ⟨t ++ (rest' ++ 93 :: rest), by simp⟩
    have c60 : charAt cs j0.val = 60 := by
      obtain ⟨t, ht⟩ := ent; rw [lit_entity] at ht; exact first_char (by rw [← ht]; rfl)
    have dne : d ≠ [] := by obtain ⟨t, ht⟩ := peDecl_head hd; rw [← ht, lit_entity]; simp
    have dlen := List.length_pos_of_ne_nil dne
    obtain ⟨r1, h1, _, c1⟩ := entity_declaration_spec cs j0 env ent
    obtain ⟨k, hk, hkv⟩ := (c1 d (rest' ++ 93 :: rest) d0 nz (by
      have := consumed_le split (by simp [dne]); simp at this; omega)).2 hd
    subst hk
    have dk : (word cs).drop k.val = [] ++ rest' ++ 93 :: rest := by rw [hkv]; simpa using drop_after d0
    obtain ⟨env', j, hj, hjv, hview'⟩ := ih cs k env [] rest dk (by simp [OptS]) nz (by
      have := consumed_le split (by simp [dne]); simp at this; omega)
    refine ⟨env', j, ?_, by rw [hjv, hkv, h0v]; simp; omega, hview'⟩
    simp only [h0, bind_ok, subset_rule_eq]; unfold subsetRuleOf
    simp only [c60, show (60 : Nat) ≠ 93 by decide, show (60 : Nat) ≠ 37 by decide, ite_false, if_pos ent, h1,
      core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    simpa using hj
  | @comment d rest' envs' hd hrest ih =>
    intro cs i env sp rest split hsp nz room
    rw [xml.internal_subset]
    obtain ⟨body, hdb, _⟩ := id hd
    obtain ⟨j0, h0, h0v, d0⟩ := subset_step (d := d) (more := rest' ++ 93 :: rest) (by rw [split]; simp) hsp
      (by rw [hdb, lit_comment]; exact ⟨_, rfl⟩)
    have com : lit "<!--" <+: (word cs).drop j0.val := by rw [d0, hdb]; exact ⟨body ++ lit "-->" ++ rest' ++ 93 :: rest, by simp⟩
    have c60 : charAt cs j0.val = 60 := by
      obtain ⟨t, ht⟩ := com; rw [lit_comment] at ht; exact first_char (by rw [← ht]; rfl)
    have notEnt : ¬ lit "<!ENTITY" <+: (word cs).drop j0.val := by
      rw [d0, hdb, lit_comment, lit_entity]; rintro ⟨t, ht⟩; simp at ht
    have dne : d ≠ [] := by rw [hdb]; simp [lit]
    have dlen := List.length_pos_of_ne_nil dne
    obtain ⟨r1, h1, _, c1⟩ := comment_spec cs j0 com
    obtain ⟨k, hk, hkv⟩ := c1 d (rest' ++ 93 :: rest) d0 hd (nz_of_drop nz d0)
    subst hk
    have dk : (word cs).drop k.val = [] ++ rest' ++ 93 :: rest := by rw [hkv]; simpa using drop_after d0
    obtain ⟨env', j, hj, hjv, hview'⟩ := ih cs k env [] rest dk (by simp [OptS]) nz (by
      have := consumed_le split (by simp [dne]); simp at this; omega)
    refine ⟨env', j, ?_, by rw [hjv, hkv, h0v]; simp; omega, hview'⟩
    simp only [h0, bind_ok, subset_rule_eq]; unfold subsetRuleOf
    simp only [c60, show (60 : Nat) ≠ 93 by decide, show (60 : Nat) ≠ 37 by decide, ite_false, if_neg notEnt,
      if_pos com, h1, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hj]
  | @pi d rest' envs' hd hrest ih =>
    intro cs i env sp rest split hsp nz room
    rw [xml.internal_subset]
    obtain ⟨t, rp, hdp, _, _⟩ := id hd
    obtain ⟨j0, h0, h0v, d0⟩ := subset_step (d := d) (more := rest' ++ 93 :: rest) (by rw [split]; simp) hsp
      (by rw [hdp, lit_pi]; exact ⟨_, rfl⟩)
    have hpi : lit "<?" <+: (word cs).drop j0.val := by rw [d0, hdp]; exact ⟨t ++ rp ++ lit "?>" ++ rest' ++ 93 :: rest, by simp⟩
    have c60 : charAt cs j0.val = 60 := by
      obtain ⟨u, hu⟩ := hpi; rw [lit_pi] at hu; exact first_char (by rw [← hu]; rfl)
    have notEnt : ¬ lit "<!ENTITY" <+: (word cs).drop j0.val := by
      rw [d0, hdp, lit_pi, lit_entity]; rintro ⟨u, hu⟩; simp at hu
    have notCom : ¬ lit "<!--" <+: (word cs).drop j0.val := by
      rw [d0, hdp, lit_pi, lit_comment]; rintro ⟨u, hu⟩; simp at hu
    have dne : d ≠ [] := by rw [hdp]; simp [lit]
    have dlen := List.length_pos_of_ne_nil dne
    obtain ⟨r1, h1, _, c1⟩ := pi_spec cs j0 hpi
    obtain ⟨k, hk, hkv⟩ := c1 d (rest' ++ 93 :: rest) d0 hd (nz_of_drop nz d0)
    subst hk
    have dk : (word cs).drop k.val = [] ++ rest' ++ 93 :: rest := by rw [hkv]; simpa using drop_after d0
    obtain ⟨env', j, hj, hjv, hview'⟩ := ih cs k env [] rest dk (by simp [OptS]) nz (by
      have := consumed_le split (by simp [dne]); simp at this; omega)
    refine ⟨env', j, ?_, by rw [hjv, hkv, h0v]; simp; omega, hview'⟩
    simp only [h0, bind_ok, subset_rule_eq]; unfold subsetRuleOf
    simp only [c60, show (60 : Nat) ≠ 93 by decide, show (60 : Nat) ≠ 37 by decide, ite_false, if_neg notEnt,
      if_neg notCom, if_pos hpi, h1, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hj]
  | @space d rest' envs' hd hrest ih =>
    intro cs i env sp rest split hsp nz room
    obtain ⟨env', j, hj, hjv, hview⟩ := ih cs i env (sp ++ d) rest (by rw [split]; simp)
      (fun c hc => by simp at hc; rcases hc with h | h; exact hsp c h; exact hd.2 c h) nz room
    exact ⟨env', j, hj, by rw [hjv]; simp; omega, hview⟩

end Rowl.XmlSubset
