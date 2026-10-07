import Rowl.XmlAttributes

/-!
# Attribute specifications in start tags

`eq`, `attribute` and `attributes` read the grammar's `(S Attribute)*`, and
`unique_names` checks [WFC: Unique Att Spec].
-/

namespace Rowl.XmlTags
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs Rowl.XmlEntities Rowl.XmlAttributes
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

theorem nz_of_drop {cs : alloc.vec.Vec U32} (nz : NoZero cs) {i : Nat} {w rest : Word}
    (split : (word cs).drop i = w ++ rest) : ∀ c ∈ w, c ≠ 0 := by
  intro c hc
  apply nz c
  apply List.mem_of_mem_drop (i := i)
  rw [split]; exact List.mem_append_left _ hc

theorem run_spaces_eq {cs : alloc.vec.Vec U32} {i : Nat} {a rest : Word} (split : (word cs).drop i = a ++ rest)
    (sp : OptS a) (stop : ∀ c m, rest = c :: m → ¬ IsSpace c) : run IsSpace ((word cs).drop i) = a := by
  rw [split]; exact run_unique sp stop

theorem eq_spec (cs : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, xml.eq cs i = .ok r ∧
      (∀ j, r = .Ok j → ∃ e, (word cs).drop i.val = e ++ (word cs).drop j.val ∧ j.val = i.val + e.length ∧
        Eq e ∧ ¬ IsSpace (charAt cs j.val)) ∧
      (∀ e rest, (word cs).drop i.val = e ++ rest → Eq e → (∀ c m, rest = c :: m → ¬ IsSpace c) →
        ∃ j, r = .Ok j ∧ j.val = i.val + e.length) := by
  unfold xml.eq
  obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
  have split0 := drop_run IsSpace cs i.val
  rw [← h0v] at split0
  have all0 : ∀ c ∈ run IsSpace ((word cs).drop i.val), IsSpace c := run_all
  generalize hr0 : run IsSpace ((word cs).drop i.val) = r0 at split0 h0v all0
  -- every reading of `Eq` from `i` begins with the spaces `r0`
  have firstSpaces : ∀ a b rest, (word cs).drop i.val = a ++ 61 :: b ++ rest → OptS a → a = r0 := by
    intro a b rest split ha
    rw [← hr0]
    exact (run_spaces_eq (rest := 61 :: b ++ rest) (by rw [split]; simp) ha
      (by intro c m e; simp at e; rw [e.1]; simp [IsSpace])).symm
  by_cases eqc : charAt cs j0.val = 61
  · obtain ⟨inside, hd⟩ := drop_nonzero (by rw [eqc]; decide : charAt cs j0.val ≠ 0)
    obtain ⟨j1, h1, h1v⟩ := next_spec inside
    obtain ⟨j, hj, hjv⟩ := skip_spaces_eq cs j1
    have split1 := drop_run IsSpace cs j1.val
    rw [← hjv] at split1
    have all1 : ∀ c ∈ run IsSpace ((word cs).drop j1.val), IsSpace c := run_all
    have follow : ¬ IsSpace (charAt cs j.val) := by rw [hjv]; exact run_follow cs j1.val not_space_zero
    generalize hr1 : run IsSpace ((word cs).drop j1.val) = r1 at split1 hjv all1
    refine ⟨.Ok j, by simp [h0, at_eq, atU_eq (c := 61#u32) (by simpa using eqc), h1, hj], ?_, ?_⟩
    · intro j' e
      simp at e; subst e
      refine ⟨r0 ++ 61 :: r1, ?_, ?_, ⟨r0, r1, rfl, all0, all1⟩, follow⟩
      · rw [split0, hd, eqc, ← h1v, split1]; simp
      · rw [hjv, h1v, h0v]; simp; omega
    · intro e rest split he stop
      obtain ⟨a, b, rfl, ha, hb⟩ := he
      have ra := firstSpaces a b rest split ha
      subst ra
      have d1 : (word cs).drop j1.val = b ++ rest := by
        rw [h1v, h0v]
        have := drop_after (cs := cs) (i := i.val) (w := a ++ [61]) (rest := b ++ rest) (by rw [split]; simp)
        simpa [Nat.add_assoc] using this
      have rb : r1 = b := by
        rw [← hr1]; exact run_spaces_eq d1 hb stop
      subst rb
      refine ⟨j, rfl, ?_⟩
      rw [hjv, h1v, h0v]; simp; omega
  · refine ⟨.Err ⟨.Syntax, j0⟩, by simp [h0, at_eq, atU_ne (c := 61#u32) (by simpa using eqc), xml.fail],
      by simp, ?_⟩
    intro e rest split he _
    obtain ⟨a, b, rfl, ha, hb⟩ := he
    have ra := firstSpaces a b rest split ha
    subst ra
    exfalso; apply eqc
    rw [h0v]
    have := charAt_after (cs := cs) (i := i.val) (w := a) (rest := 61 :: b ++ rest) (by rw [split]; simp)
    simpa using this

/-- A raw attribute specification read as the specification `spec`: a QName
    with its colon and a normalized value. -/
def RawOk (cs : alloc.vec.Vec U32) (raw : xml.Raw) (spec : Word × Word) : Prop :=
  (∃ p l, QName spec.1 p l ∧ raw.mark.val = markOf raw.start.val spec.1 p) ∧
  (word cs).drop raw.start.val = spec.1 ++ (word cs).drop raw.stop.val ∧
  raw.stop.val = raw.start.val + spec.1.length ∧ word raw.value = spec.2

theorem word_new : word (alloc.vec.Vec.new U32) = [] := by simp [word]

theorem quote_eq (c : U32) : xml.quote c = .ok (decide (Quote c.val)) := by
  simp [xml.quote, Quote, UScalar.eq_equiv]

theorem quoteOpt_of {q : U32} (h : Quote q.val) : quoteOpt q = some q.val := by
  unfold quoteOpt; rcases h with h | h <;> simp [h]

theorem quote_ok {q : U32} (h : Quote q.val) : QuoteOk q := by
  rcases h with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem attribute_sound (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity)
    (stack : alloc.vec.Vec Usize) (budget : Usize) {names : List Word} (henv : EnvOk env)
    (hstack : StackOk env stack names) :
    ∃ r, xml.attribute cs i env stack budget = .ok r ∧
      ∀ raw k b', r = .Ok (raw, k, b') → ∃ n e v value kc,
        (word cs).drop i.val = n ++ e ++ v ++ (word cs).drop k.val ∧
        k.val = i.val + n.length + e.length + v.length ∧ Eq e ∧ AttValue (envView env) names v value kc ∧
        raw.start = i ∧ RawOk cs raw (n, value) ∧ b'.val + kc = budget.val := by
  unfold xml.attribute
  obtain ⟨r1, h1, sound1, _⟩ := qname_spec cs i
  cases r1 with
  | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
  | Ok pair =>
    obtain ⟨stop, mark⟩ := pair
    obtain ⟨hstop, p, l, hq, hmark⟩ := sound1 stop mark rfl
    have nsplit : (word cs).drop i.val = nameRun cs i.val ++ (word cs).drop stop.val := by
      rw [hstop]; exact nameRun_split cs i.val
    obtain ⟨r2, h2, sound2, _⟩ := eq_spec cs stop
    cases r2 with
    | Err err => exact ⟨.Err err, by simp [h1, h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
        by simp⟩
    | Ok j =>
      obtain ⟨e, esplit, hj, he, _⟩ := sound2 j rfl
      by_cases hq' : Quote (charAt cs j.val)
      · have qv : Quote (atU cs j.val).val := by rw [atU_val]; exact hq'
        obtain ⟨inside, hd⟩ := drop_nonzero (by rcases hq' with h | h <;> rw [h] <;> decide : charAt cs j.val ≠ 0)
        obtain ⟨j1, hj1, hj1v⟩ := next_spec inside
        obtain ⟨r3, h3, sound3⟩ := att_text_sound cs j1 (atU cs j.val) env stack budget (alloc.vec.Vec.new U32)
          henv hstack
        cases r3 with
        | Err err =>
          exact ⟨.Err err, by simp [h1, h2, core.result.Result.Insts.CoreOpsTry.branch, at_eq, quote_eq, qv,
            hj1, h3, same_residual], by simp⟩
        | Ok triple =>
          obtain ⟨value, kk, b1⟩ := triple
          obtain ⟨body, val, kc, bsplit, hat, hval, hb, hstopq⟩ := sound3 value kk b1 rfl
          obtain ⟨insideK, hdK⟩ := drop_nonzero (by
            rw [hstopq, atU_val]; rcases hq' with h | h <;> rw [h] <;> decide : charAt cs kk.val ≠ 0)
          obtain ⟨k1, hk1, hk1v⟩ := next_spec insideK
          refine ⟨.Ok (⟨i, mark, stop, value⟩, k1, b1), by simp [h1, h2, core.result.Result.Insts.CoreOpsTry.branch,
            at_eq, quote_eq, qv, hj1, h3, hk1], ?_⟩
          intro raw k b' eq
          simp at eq; obtain ⟨rfl, rfl, rfl⟩ := eq
          have hbody : (word cs).drop j1.val = body ++ (word cs).drop kk.val := bsplit
          have kkv : kk.val = j1.val + body.length := by
            have := congrArg List.length bsplit
            have l2 := congrArg List.length hdK
            simp [word_length] at this l2
            omega
          refine ⟨nameRun cs i.val, e, charAt cs j.val :: body ++ [charAt cs j.val], val, kc, ?_, ?_, he,
            ⟨charAt cs j.val, body, hq', rfl, ?_⟩, rfl, ⟨⟨p, l, hq, hmark⟩, nsplit, hstop, by simp [hval, word_new]⟩, by
              simpa using hb⟩
          · rw [nsplit, esplit, hd, ← hj1v, bsplit, hdK, hstopq, atU_val, ← hk1v]; simp
          · rw [hk1v, kkv, hj1v, hj, hstop]; simp; omega
          · rw [quoteOpt_of qv, atU_val] at hat; exact hat
      · exact ⟨.Err ⟨.Syntax, j⟩, by simp [h1, h2, core.result.Result.Insts.CoreOpsTry.branch, at_eq, quote_eq,
          atU_val, hq', xml.fail], by simp⟩

theorem eq_ne {e : Word} (h : Eq e) : e ≠ [] := by
  obtain ⟨a, b, rfl, _, _⟩ := h; simp

/-- The first character of an `Eq` is white space or `=`. -/
theorem eq_head {e : Word} (h : Eq e) : ∀ c m, e = c :: m → IsSpace c ∨ c = 61 := by
  obtain ⟨a, b, rfl, ha, _⟩ := h
  intro c m em
  cases a with
  | nil => simp at em; exact Or.inr em.1
  | cons d a' => simp at em; rw [← em.1]; exact Or.inl (ha d (by simp))

theorem attribute_complete (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity)
    (stack : alloc.vec.Vec Usize) (budget : Usize) {names : List Word} {n e v value rest : Word}
    {p : Option Word} {l : Word} {kc : Nat}
    (henv : EnvOk env) (hstack : StackOk env stack names) (nz : NoZero cs)
    (split : (word cs).drop i.val = n ++ e ++ v ++ rest) (hq : QName n p l) (he : Eq e)
    (hv : AttValue (envView env) names v value kc) (kb : kc ≤ budget.val) (vlen : value.length ≤ Usize.max) :
    ∃ raw k b', xml.attribute cs i env stack budget = .ok (.Ok (raw, k, b')) ∧
      k.val = i.val + n.length + e.length + v.length ∧ b'.val + kc = budget.val ∧ RawOk cs raw (n, value) := by
  obtain ⟨q, body, hquote, rfl, hat⟩ := hv
  have nrun : nameRun cs i.val = n := by
    apply nameRun_eq (more := e ++ q :: body ++ [q] ++ rest) (by rw [split]; simp) (name_all (qname_name hq))
    intro c m em
    cases e with
    | nil => exact absurd rfl (eq_ne he)
    | cons d e' =>
      simp at em
      rw [← em.1]
      rcases eq_head he d e' rfl with sp | eq61
      · exact space_not_name sp
      · rw [eq61]; simp [NameChar, NameStartChar]
  unfold xml.attribute
  obtain ⟨r1, h1, sound1, complete1⟩ := qname_spec cs i
  rw [nrun] at sound1 complete1
  obtain ⟨stop, mark, hr1⟩ := complete1 p l hq
  subst hr1
  obtain ⟨hstop, hmk⟩ := sound1 stop mark rfl
  have dstop : (word cs).drop stop.val = e ++ (q :: body ++ [q] ++ rest) := by
    rw [hstop]; have := drop_after (cs := cs) (i := i.val) (w := n) (rest := e ++ q :: body ++ [q] ++ rest)
      (by rw [split]; simp)
    rw [this]; simp
  have nsplit : (word cs).drop i.val = n ++ (word cs).drop stop.val := by rw [dstop, split]; simp
  obtain ⟨r2, h2, _, complete2⟩ := eq_spec cs stop
  obtain ⟨j, hr2, hjv⟩ := complete2 e (q :: body ++ [q] ++ rest) dstop he (by
    intro c m em; simp at em; rw [← em.1]
    rcases hquote with h | h <;> rw [h] <;> simp [IsSpace])
  subst hr2
  have dj : (word cs).drop j.val = q :: (body ++ q :: rest) := by
    rw [hjv]; have := drop_after (cs := cs) (i := stop.val) (w := e) (rest := q :: body ++ [q] ++ rest)
      (by rw [dstop]); rw [this]; simp
  have cq : charAt cs j.val = q := first_char dj
  have qv : Quote (atU cs j.val).val := by rw [atU_val, cq]; exact hquote
  obtain ⟨inside, hd⟩ := drop_nonzero (by rw [cq]; rcases hquote with h | h <;> rw [h] <;> decide :
    charAt cs j.val ≠ 0)
  obtain ⟨j1, hj1, hj1v⟩ := next_spec inside
  have d1 : (word cs).drop j1.val = body ++ q :: rest := by
    rw [hj1v]; rw [hd] at dj; simp at dj; exact dj.2
  obtain ⟨o, kk, b', run3, hout, hkk, hb⟩ := att_text_complete hat cs j1 (atU cs j.val) env stack budget
    (alloc.vec.Vec.new U32) (q :: rest) rfl henv hstack (by rw [quoteOpt_of qv, atU_val, cq]) (quote_ok qv) d1
    (by rw [atU_val, cq]; have := charAt_after (rest := q :: rest) d1; simpa using this)
    (nz_of_drop nz d1) kb (by simpa using vlen)
  obtain ⟨insideK, _⟩ := drop_nonzero (by
    have := charAt_after (rest := q :: rest) d1
    rw [← hkk] at this; rw [this]; simp; rcases hquote with h | h <;> rw [h] <;> decide :
    charAt cs kk.val ≠ 0)
  obtain ⟨k1, hk1, hk1v⟩ := next_spec insideK
  refine ⟨⟨i, mark, stop, o⟩, k1, b', by simp [h1, h2, core.result.Result.Insts.CoreOpsTry.branch, at_eq,
    quote_eq, qv, hj1, run3, hk1], ?_, hb, hmk, nsplit, hstop, by simp [hout, word_new]⟩
  rw [hk1v, hkk, hj1v, hjv, hstop]; simp; omega

theorem attribute_follows_eq (cs : alloc.vec.Vec U32) (i j : Usize) :
    xml.attribute_follows cs i j = .ok (decide (i.val < j.val ∧ NameStartChar (charAt cs j.val))) := by
  simp [xml.attribute_follows, at_eq, name_start_eq, atU_val]

theorem push_raw_eq (raws : alloc.vec.Vec xml.Raw) (raw : xml.Raw) (offset : Usize)
    (h : raws.val.length < Usize.max) :
    ∃ v, xml.push_raw raws raw offset = .ok (.Ok v) ∧ v.val = raws.val ++ [raw] := by
  obtain ⟨v, hv, hvv⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec raws raw h)
  exact ⟨v, by simp [xml.push_raw, alloc.vec.Vec.len_val, core.num.Usize.MAX, h, hv], hvv⟩

theorem attributes_sound (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity)
    (stack : alloc.vec.Vec Usize) (budget : Usize) (raws : alloc.vec.Vec xml.Raw) {names : List Word}
    (henv : EnvOk env) (hstack : StackOk env stack names) :
    ∃ r, xml.attributes cs i env stack budget raws = .ok r ∧
      ∀ raws' j b', r = .Ok (raws', j, b') → ∃ w specs k new,
        (word cs).drop i.val = w ++ (word cs).drop j.val ∧ j.val = i.val + w.length ∧
        Specs (envView env) names w specs k ∧ raws'.val = raws.val ++ new ∧ List.Forall₂ (RawOk cs) new specs ∧
        b'.val + k = budget.val := by
  rw [xml.attributes]
  obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
  have split0 := drop_run IsSpace cs i.val
  rw [← h0v] at split0
  have all0 : ∀ c ∈ run IsSpace ((word cs).drop i.val), IsSpace c := run_all
  generalize hr0 : run IsSpace ((word cs).drop i.val) = r0 at split0 h0v all0
  by_cases follows : i.val < j0.val ∧ NameStartChar (charAt cs j0.val)
  · have j0len : j0.val < cs.val.length :=
      charAt_inside (fun z => not_name_start_zero (z ▸ follows.2))
    obtain ⟨r1, h1, sound1⟩ := attribute_sound cs j0 env stack budget henv hstack
    cases r1 with
    | Err err =>
      exact ⟨.Err err, by simp [h0, attribute_follows_eq, follows, h1, core.result.Result.Insts.CoreOpsTry.branch,
        same_residual], by simp⟩
    | Ok triple =>
      obtain ⟨raw, k1, b1⟩ := triple
      obtain ⟨n, e, v, value, kc, s1, hk1, he, hv, hstart, hraw, hb1⟩ := sound1 raw k1 b1 rfl
      have npos : 0 < n.length := by
        obtain ⟨_, _, hq', _⟩ := hraw.1
        obtain ⟨c, rest, e1, _, _⟩ := qname_name hq'
        have e2 : n = c :: rest := e1
        rw [e2]; simp
      have progress : cs.val.length - k1.val < cs.val.length - i.val := by omega
      by_cases room : raws.val.length < Usize.max
      · obtain ⟨raws1, hp, hpv⟩ := push_raw_eq raws raw j0 room
        obtain ⟨r2, h2, sound2⟩ := attributes_sound cs k1 env stack b1 raws1 henv hstack
        refine ⟨r2, by simp [h0, attribute_follows_eq, follows, h1, core.result.Result.Insts.CoreOpsTry.branch,
          hp, h2], ?_⟩
        intro raws' j b' e2
        obtain ⟨w, specs, k, new, s2, hj, hspecs, hraws', hall, hb⟩ := sound2 raws' j b' e2
        obtain ⟨p, l, hq, _⟩ := hraw.1
        refine ⟨r0 ++ n ++ e ++ v ++ w, (n, value) :: specs, kc + k, raw :: new,
          ?_, ?_, ?_, by rw [hraws', hpv]; simp, List.Forall₂.cons hraw hall, by omega⟩
        · rw [split0, s1, s2]; simp
        · rw [hj, hk1, h0v]; simp; omega
        · refine Specs.cons ⟨?_, all0⟩ hq he hv hspecs
          intro e0
          rw [e0] at h0v; simp at h0v; omega
      · exact ⟨.Err ⟨.ResourceLimit, j0⟩, by simp [h0, attribute_follows_eq, follows, h1,
          core.result.Result.Insts.CoreOpsTry.branch, xml.push_raw, alloc.vec.Vec.len_val, core.num.Usize.MAX,
          room, xml.fail, same_residual], by simp⟩
  · refine ⟨.Ok (raws, i, budget), by simp [h0, attribute_follows_eq, follows], ?_⟩
    intro raws' j b' e
    simp at e; obtain ⟨rfl, rfl, rfl⟩ := e
    exact ⟨[], [], 0, [], by simp, by simp, Specs.nil, by simp, List.Forall₂.nil, by simp⟩
termination_by cs.val.length - i.val
decreasing_by omega

theorem attributes_complete {E : Env} {names : List Word} {w : Word} {specs : List (Word × Word)} {k : Nat}
    (h : Specs E names w specs k) :
    ∀ (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity) (stack : alloc.vec.Vec Usize)
      (budget : Usize) (raws : alloc.vec.Vec xml.Raw) (rest : Word),
      E = envView env → EnvOk env → StackOk env stack names → NoZero cs →
      (word cs).drop i.val = w ++ rest → (∃ s c more, rest = s ++ c :: more ∧ OptS s ∧ (c = 62 ∨ c = 47)) →
      k ≤ budget.val → (∀ sp ∈ specs, sp.2.length ≤ Usize.max) → raws.val.length + specs.length ≤ Usize.max →
      ∃ raws' j b', xml.attributes cs i env stack budget raws = .ok (.Ok (raws', j, b')) ∧
        j.val = i.val + w.length ∧ b'.val + k = budget.val ∧
        ∃ new, raws'.val = raws.val ++ new ∧ List.Forall₂ (RawOk cs) new specs := by
  induction h with
  | nil =>
    intro cs i env stack budget raws rest hE henv hstack nz split follow kb vals room
    obtain ⟨s, c, more, rfl, hs, hc⟩ := follow
    obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
    have rs : run IsSpace ((word cs).drop i.val) = s :=
      run_spaces_eq (rest := c :: more) (by rw [split]; simp) hs
        (fun d m e => by simp at e; rw [← e.1]; rcases hc with h | h <;> rw [h] <;> simp [IsSpace])
    have cj : charAt cs j0.val = c := by
      rw [h0v, rs]; have := charAt_after (rest := c :: more) (by rw [split]; simp : (word cs).drop i.val = s ++ c :: more)
      simpa using this
    have nf : ¬ (i.val < j0.val ∧ NameStartChar (charAt cs j0.val)) := by
      rintro ⟨_, ns⟩; rw [cj] at ns; rcases hc with h | h <;> rw [h] at ns <;> simp [NameStartChar] at ns
    refine ⟨raws, i, budget, ?_, by simp, by simp, [], by simp, List.Forall₂.nil⟩
    rw [xml.attributes]
    simp [h0, attribute_follows_eq, nf]
  | @cons s n e v value rest' p l specs k1 k2 hs hq he hv hrest ih =>
    intro cs i env stack budget raws rest hE henv hstack nz split follow kb vals room
    obtain ⟨c0, n', en, hc0, hn'⟩ := qname_name hq
    obtain ⟨j0, h0, h0v⟩ := skip_spaces_eq cs i
    have rs : run IsSpace ((word cs).drop i.val) = s :=
      run_spaces_eq (rest := n ++ e ++ v ++ rest' ++ rest) (by rw [split]; simp) hs.2
        (fun d m e2 => by rw [en] at e2; simp at e2; rw [← e2.1]; intro sp; exact space_not_name sp (Or.inl hc0))
    have sne : 0 < s.length := List.length_pos_of_ne_nil hs.1
    have dj0 : (word cs).drop j0.val = n ++ e ++ v ++ (rest' ++ rest) := by
      rw [h0v, rs]
      have := drop_after (cs := cs) (i := i.val) (w := s) (rest := n ++ e ++ v ++ rest' ++ rest)
        (by rw [split]; simp)
      rw [this]; simp
    have cj : charAt cs j0.val = c0 := first_char (rest := n' ++ e ++ v ++ (rest' ++ rest)) (by rw [dj0, en]; simp)
    have fl : i.val < j0.val ∧ NameStartChar (charAt cs j0.val) := ⟨by rw [h0v, rs]; omega, by rw [cj]; exact hc0⟩
    obtain ⟨raw, k1', b1, run1, hk1, hb1, hraw⟩ := attribute_complete cs j0 env stack budget henv hstack nz dj0 hq he
      (hE ▸ hv) (by omega) (vals (n, value) (by simp))
    have roomR : raws.val.length < Usize.max := by simp at room; omega
    obtain ⟨raws1, hp, hpv⟩ := push_raw_eq raws raw j0 roomR
    have dk1 : (word cs).drop k1'.val = rest' ++ rest := by
      rw [hk1]
      have := drop_after (cs := cs) (i := j0.val) (w := n ++ e ++ v) (rest := rest' ++ rest) dj0
      simpa [Nat.add_assoc] using this
    obtain ⟨raws', j, b', run2, hj, hb2, new, hnew, hall⟩ := ih cs k1' env stack b1 raws1 rest hE henv hstack nz
      dk1 follow (by omega) (fun sp hsp => vals sp (by simp [hsp])) (by rw [hpv]; simp at room ⊢; omega)
    refine ⟨raws', j, b', ?_, by rw [hj, hk1, h0v, rs]; simp; omega, by omega, raw :: new,
      by rw [hnew, hpv]; simp, List.Forall₂.cons hraw hall⟩
    rw [xml.attributes]
    simp [h0, attribute_follows_eq, fl, run1, core.result.Result.Insts.CoreOpsTry.branch, hp, run2]

theorem raw_at {cs : alloc.vec.Vec U32} {raws : alloc.vec.Vec xml.Raw} {specs : List (Word × Word)}
    (h : List.Forall₂ (RawOk cs) raws.val specs) {t : Nat} (ht : t < raws.val.length) :
    ∃ hs : t < specs.length, RawOk cs raws.val[t] specs[t] :=
  ⟨by rw [← h.length_eq]; exact ht, List.Forall₂.get h ht (by rw [← h.length_eq]; exact ht)⟩

theorem distinct_from_eq (cs : alloc.vec.Vec U32) (raws : alloc.vec.Vec xml.Raw) (k m : Usize)
    {specs : List (Word × Word)} (h : List.Forall₂ (RawOk cs) raws.val specs) (hk : k.val < raws.val.length) :
    xml.distinct_from cs raws k m = .ok (decide (∀ t, m.val ≤ t → (ht : t < raws.val.length) →
      (specs[t]'(by rw [← h.length_eq]; exact ht)).1 ≠ (specs[k.val]'(by rw [← h.length_eq]; exact hk)).1)) := by
  rw [xml.distinct_from]
  have lk : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice xml.Raw) raws k = .ok raws.val[k.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hk]
  obtain ⟨hsk, rk⟩ := raw_at h hk
  by_cases more : m.val < raws.val.length
  · have lm : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice xml.Raw) raws m = .ok raws.val[m.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨hsm, rm⟩ := raw_at h more
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_true, lk, lm, bind_ok]
    rw [same_span_eq cs _ _ _ _ rk.2.1 rk.2.2.1 rm.2.1 rm.2.2.1]
    simp only [bind_ok]
    by_cases same : specs[k.val].1 = specs[m.val].1
    · rw [if_pos (decide_eq_true same)]
      congr 1
      exact (decide_eq_false (fun all => all m.val (le_refl _) more same.symm)).symm
    · rw [if_neg (by simpa using same)]
      obtain ⟨m1, hm1, hm1v⟩ := vec_next more
      rw [hm1, bind_ok, distinct_from_eq cs raws k m1 h hk]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · intro all t lo ht
        by_cases e : t = m.val
        · subst e; exact fun x => same x.symm
        · exact all t (by omega) ht
      · intro all t lo ht; exact all t (by omega) ht
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_false]
    congr 1
    refine (decide_eq_true ?_).symm
    intro t lo ht; omega
termination_by raws.val.length - m.val
decreasing_by omega

theorem unique_names_spec (cs : alloc.vec.Vec U32) (raws : alloc.vec.Vec xml.Raw) (k : Usize)
    {specs : List (Word × Word)} (h : List.Forall₂ (RawOk cs) raws.val specs) :
    ∃ r, xml.unique_names cs raws k = .ok r ∧
      (r = .Ok () ↔ ∀ a b (ha : a < specs.length) (hb : b < specs.length), k.val ≤ a → a < b →
        specs[a].1 ≠ specs[b].1) := by
  rw [xml.unique_names]
  have hl := h.length_eq
  by_cases more : k.val < raws.val.length
  · obtain ⟨k1, hk1, hk1v⟩ := vec_next more
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_true, hk1, bind_ok]
    rw [distinct_from_eq cs raws k k1 h more]
    simp only [bind_ok]
    by_cases dist : ∀ t, k1.val ≤ t → (ht : t < raws.val.length) →
        (specs[t]'(by rw [← hl]; exact ht)).1 ≠ (specs[k.val]'(by rw [← hl]; exact more)).1
    · rw [if_pos (decide_eq_true dist)]
      obtain ⟨r, hr, spec⟩ := unique_names_spec cs raws k1 h
      refine ⟨r, hr, ?_⟩
      rw [spec]
      constructor
      · intro all a b ha hb lo lt
        by_cases e : a = k.val
        · subst e
          have := dist b (by omega) (by omega)
          exact fun x => this x.symm
        · exact all a b ha hb (by omega) lt
      · intro all a b ha hb lo lt; exact all a b ha hb (by omega) lt
    · rw [if_neg (by simpa using dist)]
      have lk : alloc.vec.Vec.index_usize raws k = .ok raws.val[k.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
      refine ⟨.Err ⟨.DuplicateAttribute, raws.val[k.val].start⟩, by simp [lk, xml.fail], ?_⟩
      simp only [reduceCtorEq, false_iff]
      intro all
      apply dist
      intro t lo ht e
      exact all k.val t (by omega) (by omega) (le_refl _) (by omega) e.symm
  · refine ⟨.Ok (), by simp [alloc.vec.Vec.len_val, more], ?_⟩
    simp only [true_iff]
    intro a b ha hb lo lt; omega
termination_by raws.val.length - k.val
decreasing_by omega

theorem nodup_names {specs : List (Word × Word)} :
    (specs.map (·.1)).Nodup ↔ ∀ a b (ha : a < specs.length) (hb : b < specs.length), 0 ≤ a → a < b →
      specs[a].1 ≠ specs[b].1 := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  simp

end Rowl.XmlTags
