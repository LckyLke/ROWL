import Rowl.XmlContent

/-!
# Reading elements and content is sound

`element` and `content` (with `content_reference` and `element_in`) only
return what the grammar's `Element` and `Content` derive: the element tree of
the word read, the items of the content read, and the budget left after the
expansions the derivation counts.
-/

namespace Rowl.XmlElements
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs Rowl.XmlEntities Rowl.XmlAttributes Rowl.XmlTags Rowl.XmlNamespaces Rowl.XmlContent
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ## Shapes of derivations -/

theorem element_head {E : Env} {names : List Word} {scope : Scope} {w : Word} {e : xml.Element} {k : Nat}
    (h : Element E names scope w e k) : ∃ rest, w = 60 :: rest := by
  cases h <;> exact ⟨_, rfl⟩

theorem markup_head {E : Env} {names : List Word} {scope : Scope} {w : Word} {x : List Item} {k : Nat}
    (h : Markup E names scope w x k) : ∃ c rest, w = c :: rest ∧ (c = 60 ∨ c = 38) := by
  cases h with
  | element he => obtain ⟨rest, rfl⟩ := element_head he; exact ⟨60, rest, rfl, Or.inl rfl⟩
  | charRef hr _ => obtain ⟨t, rfl⟩ := charRef_head hr; exact ⟨38, t, rfl, Or.inr rfl⟩
  | predefined hr _ => obtain ⟨t, rfl⟩ := entityRef_head hr; exact ⟨38, t, rfl, Or.inr rfl⟩
  | entity hr _ _ _ _ => obtain ⟨t, rfl⟩ := entityRef_head hr; exact ⟨38, t, rfl, Or.inr rfl⟩
  | cdata hc => rw [hc.1, lit_cdata]; exact ⟨60, _, rfl, Or.inl rfl⟩
  | pi hp => obtain ⟨t, rest, rfl, _, _⟩ := hp; rw [lit_pi]; exact ⟨60, _, rfl, Or.inl rfl⟩
  | comment hc => obtain ⟨body, rfl, _⟩ := hc; rw [lit_comment]; exact ⟨60, _, rfl, Or.inl rfl⟩

theorem markup_ne_nil {E : Env} {names : List Word} {scope : Scope} {w : Word} {x : List Item} {k : Nat}
    (h : Markup E names scope w x k) : w ≠ [] := by
  obtain ⟨c, rest, rfl, _⟩ := markup_head h; simp

/-- Character data before content that does not begin with character data. -/
theorem content_prepend {E : Env} {names : List Word} {scope : Scope} {cd w : Word} {items : List Item} {k : Nat}
    (hne : cd ≠ []) (hcd : CharData cd) (h : Content E names scope w items k)
    (start : w = [] ∨ ∃ c rest, w = c :: rest ∧ (c = 60 ∨ c = 38)) :
    Content E names scope (cd ++ w) (chars cd ++ items) k := by
  cases h with
  | nil => simpa [chars] using Content.last (env := E) (stack := names) (scope := scope) hne hcd
  | last hne' hcd' =>
    exfalso
    rcases start with e | ⟨c, rest, e, hc⟩
    · exact hne' e
    · have := hcd'.1 c (by rw [e]; simp)
      rcases hc with rfl | rfl <;> simp at this
  | data hne' hcd' hm hrest =>
    exfalso
    rcases start with e | ⟨c, rest, e, hc⟩
    · simp at e; exact hne' e.1
    · obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hne'
      simp only [List.cons_append, List.cons.injEq] at e
      have := hcd'.1 d (by simp)
      rw [e.1] at this
      rcases hc with rfl | rfl <;> simp at this
  | markup hm hrest =>
    have := Content.data hne hcd hm hrest
    simpa [chars, List.append_assoc] using this

/-- A nonempty word consumed from a position leaves less to read. -/
theorem drop_lt {cs : alloc.vec.Vec U32} {i j : Nat} {w : Word}
    (split : (word cs).drop i = w ++ (word cs).drop j) (hw : w ≠ []) : cs.val.length - j < cs.val.length - i := by
  have := congrArg List.length split
  simp only [List.length_drop, List.length_append, word_length] at this
  have : 0 < w.length := List.length_pos_of_ne_nil hw
  omega

/-! ## What reading content returns -/

/-- What content read from `i` returned: the word read, the items and cost
    the grammar gives it, the budget left and the children so far. -/
def ContentOut (cs : alloc.vec.Vec U32) (i : Usize) (E : Env) (names : List Word) (scope : Scope) (budget : Usize)
    (nodes : alloc.vec.Vec xml.Node) (text : alloc.vec.Vec U32)
    (out : alloc.vec.Vec xml.Node × alloc.vec.Vec U32 × Usize × Usize) : Prop :=
  ∃ w items k, (word cs).drop i.val = w ++ (word cs).drop out.2.2.1.val ∧
    Content E names scope w items k ∧ out.2.2.2.val + k = budget.val ∧
    (charAt cs i.val = 0 → w = []) ∧ Rel nodes text out.1 out.2.1 items

/-- Reading content from `i` either fails or returns what the grammar derives. -/
def ContentSound (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity) (stack : alloc.vec.Vec Usize)
    (ctx : alloc.vec.Vec xml.Binding) (budget : Usize) (nodes : alloc.vec.Vec xml.Node) (text : alloc.vec.Vec U32)
    (names : List Word) : Prop :=
  ∃ r, xml.content cs i env stack ctx budget nodes text = .ok r ∧
    ∀ out, r = .Ok out → ContentOut cs i (envView env) names (scopeView ctx) budget nodes text out

/-! ## Elements -/

theorem element_in_sound_of (cs : alloc.vec.Vec U32) (i name_end mark after : Usize) (empty : Bool)
    (env : alloc.vec.Vec xml.Entity) (stack : alloc.vec.Vec Usize) (ctx : alloc.vec.Vec xml.Binding)
    (raws : alloc.vec.Vec xml.Raw) (decls : alloc.vec.Vec xml.Binding) (budget : Usize) {names : List Word}
    {n : Word} {p : Option Word} {l : Word} {specs : List (Word × Word)}
    (lt : charAt cs i.val = 60)
    (nsplit : (word cs).drop (i.val + 1) = n ++ (word cs).drop name_end.val)
    (hne : name_end.val = i.val + 1 + n.length)
    (hq : QName n p l) (hmark : mark.val = markOf (i.val + 1) n p)
    (hraws : List.Forall₂ (RawOk cs) raws.val specs)
    (ih : empty = false →
      ContentSound cs after env stack ctx budget (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) names) :
    ∃ r, xml.element_in cs i name_end mark after empty env stack ctx raws decls budget = .ok r ∧
      ∀ e j b', r = .Ok (e, j, b') →
        e.declarations = decls ∧
        ElementName (scopeView ctx) n (optWord e.ns_prefix) (optWord e.ns_name) (word e.local_name) ∧
        List.Forall₂ (AttOk (scopeView ctx)) (plain specs) e.attributes.val ∧
        (e.attributes.val.map expandedView).Nodup ∧
        ((empty = true ∧ e.children.val = [] ∧ j = after ∧ b' = budget) ∨
         (empty = false ∧ ∃ body s2 items k,
           (word cs).drop after.val = body ++ lit "</" ++ n ++ s2 ++ [62] ++ (word cs).drop j.val ∧
           Content (envView env) names (scopeView ctx) body items k ∧ OptS s2 ∧
           e.children.val.map nodeView = runs items ∧ b'.val + k = budget.val)) := by
  have inside : i.val < cs.val.length := charAt_inside (by rw [lt]; decide)
  obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
  have nsplit' : (word cs).drop i1.val = n ++ (word cs).drop name_end.val := by rw [hi1v]; exact nsplit
  have hne' : name_end.val = i1.val + n.length := by omega
  have hmark' : mark.val = markOf i1.val n p := by rw [hmark, hi1v]
  unfold xml.element_in
  simp only [hi1, bind_ok]
  obtain ⟨r1, h1, s1, _⟩ := element_namespace_spec cs i1 mark name_end nsplit' hne' hq hmark' ctx
  cases r1 with
  | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
  | Ok pn =>
    obtain ⟨pre, ns⟩ := pn
    have hname := s1 pre ns rfl
    have markle : mark.val ≤ name_end.val := by
      rw [hmark', hne']
      cases p with
      | none => simp [markOf]
      | some p' => obtain ⟨e, _, _⟩ := qname_some hq; subst e; simp [markOf]
    obtain ⟨ls, hls, hlsv⟩ := local_start_eq i1 mark name_end markle
    have lsplit : (word cs).drop ls.val = l ++ (word cs).drop name_end.val ∧ name_end.val = ls.val + l.length := by
      cases p with
      | none =>
        obtain ⟨e, _⟩ := qname_none hq
        have me : mark.val = name_end.val := by rw [hmark', hne']; simp [markOf]
        rw [hlsv, if_pos me, ← e]; exact ⟨nsplit', hne'⟩
      | some p' =>
        obtain ⟨e, _, _⟩ := qname_some hq
        subst e
        have me : ¬ mark.val = name_end.val := by rw [hmark', hne']; simp [markOf]
        rw [hlsv, if_neg me, hmark']
        simp only [markOf]
        constructor
        · have := drop_after (cs := cs) (i := i1.val) (w := p' ++ [58]) (rest := l ++ (word cs).drop name_end.val)
            (by rw [nsplit']; simp)
          simpa [Nat.add_assoc] using this
        · rw [hne']; simp; omega
    obtain ⟨lv, hlv, hlw⟩ := copy_span_spec cs ls name_end lsplit.1 lsplit.2
    obtain ⟨r2, h2, s2, _⟩ := resolve_attributes_spec cs raws hraws 0#usize ctx (alloc.vec.Vec.new _)
      (by simp)
    cases r2 with
    | Err err =>
      exact ⟨.Err err, by simp [h1, hls, hlv, h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
        by simp⟩
    | Ok attrs =>
      obtain ⟨new, hnew, hall⟩ := s2 attrs rfl
      have hall' : List.Forall₂ (AttOk (scopeView ctx)) (plain specs) attrs.val := by
        rw [hnew]; simpa using hall
      obtain ⟨r3, h3, c3⟩ := unique_expanded_spec attrs 0#usize i
      cases r3 with
      | Err err =>
        exact ⟨.Err err, by simp [h1, hls, hlv, h2, h3, core.result.Result.Insts.CoreOpsTry.branch,
          same_residual], by simp⟩
      | Ok u =>
        have distinct : (attrs.val.map expandedView).Nodup := by
          rw [nodup_expanded]; intro a b ha hb _ lt'; exact (c3.mp rfl) a b ha hb (by simp) lt'
        cases empty with
        | true =>
          refine ⟨.Ok (⟨pre, ns, lv, attrs, decls, alloc.vec.Vec.new _⟩, after, budget),
            by simp [h1, hls, hlv, h2, h3, core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
          intro e j b' eq
          simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at eq
          obtain ⟨rfl, rfl, rfl⟩ := eq
          exact ⟨by simp, by simpa [hlw] using hname, by simpa using hall', by simpa using distinct,
            Or.inl ⟨rfl, by simp, rfl, rfl⟩⟩
        | false =>
          obtain ⟨r4, h4, s4⟩ := ih rfl
          cases r4 with
          | Err err =>
            exact ⟨.Err err, by simp [h1, hls, hlv, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch,
              same_residual], by simp⟩
          | Ok out =>
            obtain ⟨nodes, text, stop, budget1⟩ := out
            obtain ⟨body, items, k, bsplit, hcontent, hb, _, rel⟩ := s4 _ rfl
            obtain ⟨r5, h5, s5⟩ := flush_sound nodes text stop
            cases r5 with
            | Err err =>
              exact ⟨.Err err, by simp [h1, hls, hlv, h2, h3, h4, h5, core.result.Result.Insts.CoreOpsTry.branch,
                same_residual], by simp⟩
            | Ok children =>
              have hch := children_of rel (s5 children rfl)
              obtain ⟨r6, h6, s6, _⟩ := end_tag_spec cs stop i1 name_end nsplit' hne'
              cases r6 with
              | Err err =>
                exact ⟨.Err err, by simp [h1, hls, hlv, h2, h3, h4, h5, h6,
                  core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
              | Ok fin =>
                obtain ⟨s2', esplit, hs2', _⟩ := s6 fin rfl
                refine ⟨.Ok (⟨pre, ns, lv, attrs, decls, children⟩, fin, budget1),
                  by simp [h1, hls, hlv, h2, h3, h4, h5, h6, core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
                intro e j b' eq
                simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at eq
                obtain ⟨rfl, rfl, rfl⟩ := eq
                refine ⟨by simp, by simpa [hlw] using hname, by simpa using hall', by simpa using distinct,
                  Or.inr ⟨rfl, body, s2', items, k, ?_, hcontent, hs2', by simpa using hch, by simpa using hb⟩⟩
                rw [bsplit, esplit]; simp

/-- The element a start tag and what follows it make. -/
theorem element_finish {cs : alloc.vec.Vec U32} {i j2 after j' : Usize} {E : Env} {names : List Word}
    {scope : Scope} {n attrs sp : Word} {p : Option Word} {l : Word} {specs : List (Word × Word)} {k1 : Nat}
    {budget budget1 b' : Usize} {empty : Bool} {e : xml.Element}
    (tsplit : (word cs).drop i.val = 60 :: n ++ attrs ++ sp ++ (word cs).drop j2.val)
    (hq : QName n p l) (hspecs : Specs E names attrs specs k1) (hsp : OptS sp)
    (htag : (empty = false ∧ charAt cs j2.val = 62 ∧ after.val = j2.val + 1) ∨
      (empty = true ∧ charAt cs j2.val = 47 ∧ charAt cs (j2.val + 1) = 62 ∧ after.val = j2.val + 2))
    (uniq : (specs.map (·.1)).Nodup) (allowed : ∀ d ∈ declarations specs, DeclarationOk d)
    (hb1 : budget1.val + k1 = budget.val)
    (hdecl : e.declarations.val.map bindingView = declarations specs)
    (hname : ElementName (scope ++ declarations specs) n (optWord e.ns_prefix) (optWord e.ns_name)
      (word e.local_name))
    (hatts : List.Forall₂ (AttOk (scope ++ declarations specs)) (plain specs) e.attributes.val)
    (hdist : (e.attributes.val.map expandedView).Nodup)
    (hrest : (empty = true ∧ e.children.val = [] ∧ j' = after ∧ b' = budget1) ∨
      (empty = false ∧ ∃ body s2 items k,
        (word cs).drop after.val = body ++ lit "</" ++ n ++ s2 ++ [62] ++ (word cs).drop j'.val ∧
        Content E names (scope ++ declarations specs) body items k ∧ OptS s2 ∧
        e.children.val.map nodeView = runs items ∧ b'.val + k = budget1.val)) :
    ∃ w k, (word cs).drop i.val = w ++ (word cs).drop j'.val ∧ Element E names scope w e k ∧
      b'.val + k = budget.val := by
  have tag : StartTag scope n specs e := ⟨uniq, allowed, hdecl, hname, hatts, hdist⟩
  rcases hrest with ⟨rfl, hch, rfl, rfl⟩ | ⟨rfl, body, s2, items, k, bsplit, hcontent, hs2, hch, hb⟩
  · rcases htag with ⟨h, _⟩ | ⟨_, sl, gt, hafter⟩
    · cases h
    · obtain ⟨inside, d1⟩ := drop_nonzero (by rw [sl]; decide : charAt cs j2.val ≠ 0)
      obtain ⟨_, d2⟩ := drop_nonzero (by rw [gt]; decide : charAt cs (j2.val + 1) ≠ 0)
      refine ⟨60 :: n ++ attrs ++ sp ++ lit "/>", k1, ?_, Element.empty hq hspecs hsp tag hch, by omega⟩
      rw [tsplit, d1, sl, d2, gt, hafter]
      simp [lit, Nat.add_assoc]
  · rcases htag with ⟨_, gt, hafter⟩ | ⟨h, _⟩
    · obtain ⟨inside, d1⟩ := drop_nonzero (by rw [gt]; decide : charAt cs j2.val ≠ 0)
      refine ⟨60 :: n ++ attrs ++ sp ++ [62] ++ body ++ lit "</" ++ n ++ s2 ++ [62], k1 + k, ?_,
        Element.full hq hspecs hsp tag hcontent hs2 hch, by omega⟩
      rw [tsplit, d1, gt, ← hafter, bsplit]
      simp
    · cases h

theorem copy_bindings_sound (ctx : alloc.vec.Vec xml.Binding) (i : Usize) (out : alloc.vec.Vec xml.Binding) :
    ∃ r, xml.copy_bindings ctx i out = .ok r ∧ ∀ v, r = .Ok v → v.val = out.val ++ ctx.val.drop i.val := by
  rw [xml.copy_bindings]
  by_cases more : i.val < ctx.val.length
  · have lk : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice xml.Binding) ctx i =
        .ok ctx.val[i.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨i1, hi1, hi1v⟩ := vec_next more
    by_cases r1 : out.val.length < Usize.max
    · obtain ⟨o1, ho1, ho1v⟩ := push_binding_eq out ⟨ctx.val[i.val].ns_prefix, ctx.val[i.val].value⟩ 0#usize r1
      obtain ⟨r, hr, hv⟩ := copy_bindings_sound ctx i1 o1
      refine ⟨r, ?_, ?_⟩
      · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lk, copy_option_eq, copy_all_eq,
          core.result.Result.Insts.CoreOpsTry.branch, ho1, hi1, hr]
      · intro v e
        rw [hv v e, ho1v, hi1v]
        simp only [List.append_assoc, List.singleton_append]
        rw [List.drop_eq_getElem_cons (i := i.val) more]
    · refine ⟨.Err ⟨.ResourceLimit, 0#usize⟩, ?_, by simp⟩
      simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lk, copy_option_eq, copy_all_eq,
        core.result.Result.Insts.CoreOpsTry.branch, xml.push_binding, core.num.Usize.MAX, r1, xml.fail,
        same_residual]
  · refine ⟨.Ok out, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], ?_⟩
    intro v e; simp at e; subst e
    simp [List.drop_eq_nil_of_le (show ctx.val.length ≤ i.val by omega)]
termination_by ctx.val.length - i.val
decreasing_by omega

theorem extend_sound (ctx decls : alloc.vec.Vec xml.Binding) :
    ∃ r, xml.extend ctx decls = .ok r ∧ ∀ v, r = .Ok v → v.val = ctx.val ++ decls.val := by
  unfold xml.extend
  obtain ⟨r1, h1, s1⟩ := copy_bindings_sound ctx 0#usize (alloc.vec.Vec.new xml.Binding)
  cases r1 with
  | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
  | Ok o =>
    obtain ⟨r2, h2, s2⟩ := copy_bindings_sound decls 0#usize o
    refine ⟨r2, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_⟩
    intro v e
    rw [s2 v e, s1 o rfl]; simp

theorem element_sound_of (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity)
    (stack : alloc.vec.Vec Usize) (ctx : alloc.vec.Vec xml.Binding) (budget : Usize) {names : List Word}
    (henv : EnvOk env) (hstack : StackOk env stack names) (lt : charAt cs i.val = 60)
    (ih : ∀ (ctx' : alloc.vec.Vec xml.Binding) (j b : Usize), cs.val.length - j.val < cs.val.length - i.val →
      b.val ≤ budget.val →
      ContentSound cs j env stack ctx' b (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) names) :
    ∃ r, xml.element cs i env stack ctx budget = .ok r ∧
      ∀ e j b', r = .Ok (e, j, b') → ∃ w k, (word cs).drop i.val = w ++ (word cs).drop j.val ∧
        Element (envView env) names (scopeView ctx) w e k ∧ b'.val + k = budget.val := by
  have inside : i.val < cs.val.length := charAt_inside (by rw [lt]; decide)
  obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
  have d0 : (word cs).drop i.val = 60 :: (word cs).drop (i.val + 1) := by rw [← lt]; exact drop_charAt inside
  unfold xml.element
  simp only [hi1, bind_ok]
  obtain ⟨r1, h1, sound1, _⟩ := qname_spec cs i1
  cases r1 with
  | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
  | Ok pair =>
    obtain ⟨name_end, mark⟩ := pair
    obtain ⟨hne, p, l, hq, hmark⟩ := sound1 name_end mark rfl
    have nsplit : (word cs).drop (i.val + 1) = nameRun cs i1.val ++ (word cs).drop name_end.val := by
      rw [← hi1v, hne]; exact nameRun_split cs i1.val
    generalize hn : nameRun cs i1.val = n at hne hq hmark nsplit
    have hne' : name_end.val = i.val + 1 + n.length := by omega
    have hmark' : mark.val = markOf (i.val + 1) n p := by rw [hmark, hi1v]
    obtain ⟨r2, h2, sound2⟩ := attributes_sound cs name_end env stack budget (alloc.vec.Vec.new _) henv hstack
    cases r2 with
    | Err err =>
      exact ⟨.Err err, by simp [h1, h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
    | Ok triple =>
      obtain ⟨raws, j, budget1⟩ := triple
      obtain ⟨attrs, specs, k1, new, asplit, hj, hspecs, hraws, hall, hb1⟩ := sound2 raws j budget1 rfl
      have hraws' : List.Forall₂ (RawOk cs) raws.val specs := by rw [hraws]; simpa using hall
      obtain ⟨j2, hj2, hj2v⟩ := skip_spaces_eq cs j
      have split2 := drop_run IsSpace cs j.val
      rw [← hj2v] at split2
      have all2 : ∀ c ∈ run IsSpace ((word cs).drop j.val), IsSpace c := run_all
      generalize hsp : run IsSpace ((word cs).drop j.val) = sp at split2 hj2v all2
      have tsplit : (word cs).drop i.val = 60 :: n ++ attrs ++ sp ++ (word cs).drop j2.val := by
        rw [d0, nsplit, asplit, split2]; simp
      obtain ⟨r3, h3, c3⟩ := tag_end_spec cs j2
      cases r3 with
      | Err err =>
        exact ⟨.Err err, by simp [h1, h2, hj2, h3, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
          by simp⟩
      | Ok ea =>
        obtain ⟨empty, after⟩ := ea
        have progress : cs.val.length - after.val < cs.val.length - i.val := by
          rcases c3 with ⟨_, gt, hafter⟩ | ⟨_, sl, gt, hafter⟩
          · obtain ⟨_, d1⟩ := drop_nonzero (by rw [gt]; decide : charAt cs j2.val ≠ 0)
            apply drop_lt (w := 60 :: n ++ attrs ++ sp ++ [62]) _ (by simp)
            rw [tsplit, d1, gt, ← hafter]; simp
          · obtain ⟨_, d1⟩ := drop_nonzero (by rw [sl]; decide : charAt cs j2.val ≠ 0)
            obtain ⟨_, d2⟩ := drop_nonzero (by rw [gt]; decide : charAt cs (j2.val + 1) ≠ 0)
            apply drop_lt (w := 60 :: n ++ attrs ++ sp ++ [47, 62]) _ (by simp)
            rw [tsplit, d1, sl, d2, gt, hafter]; simp [Nat.add_assoc]
        obtain ⟨r4, h4, c4⟩ := unique_names_spec cs raws 0#usize hraws'
        cases r4 with
        | Err err =>
          exact ⟨.Err err, by simp [h1, h2, hj2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch,
            same_residual], by simp⟩
        | Ok u =>
          have uniq : (specs.map (·.1)).Nodup := by
            rw [nodup_names]; intro a b ha hb _ lt'; exact (c4.mp rfl) a b ha hb (by simp) lt'
          obtain ⟨r5, h5, c5⟩ := declarations_spec cs raws hraws' 0#usize (alloc.vec.Vec.new _) (by simp)
          cases r5 with
          | Err err =>
            exact ⟨.Err err, by simp [h1, h2, hj2, h3, h4, h5, core.result.Result.Insts.CoreOpsTry.branch,
              same_residual], by simp⟩
          | Ok decls =>
            obtain ⟨allowed, hdecls⟩ := c5
            have z0 : (0#usize : Usize).val = 0 := rfl
            simp only [z0, List.drop_zero] at allowed hdecls
            have hdecls' : decls.val.map bindingView = declarations specs := by simpa using hdecls
            by_cases dz : decls.val.length = 0
            · have dzero : alloc.vec.Vec.len decls = 0#usize :=
                UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len_val, dz])
              have dnil : declarations specs = [] := by
                rw [← hdecls', List.length_eq_zero_iff.mp dz]; simp
              obtain ⟨r6, h6, c6⟩ := element_in_sound_of cs i name_end mark after empty env stack ctx raws decls
                budget1 lt nsplit hne' hq hmark' hraws' (fun _ => ih ctx after budget1 progress (by omega))
              refine ⟨r6, by simp [h1, h2, hj2, h3, h4, h5, dzero, h6, core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
              intro e j' b' e6
              obtain ⟨hd, hname, hatts, hdist, hrest⟩ := c6 e j' b' e6
              exact element_finish tsplit hq hspecs all2 c3 uniq allowed hb1 (by rw [hd]; exact hdecls')
                (by rw [dnil, List.append_nil]; exact hname) (by rw [dnil, List.append_nil]; exact hatts) hdist
                (by rw [dnil, List.append_nil]; exact hrest)
            · have dzero : ¬ alloc.vec.Vec.len decls = 0#usize := by
                intro h; apply dz; have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len_val] using this
              obtain ⟨r6, h6, c6⟩ := extend_sound ctx decls
              cases r6 with
              | Err err =>
                exact ⟨.Err err, by simp [h1, h2, hj2, h3, h4, h5, dzero, h6,
                  core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
              | Ok inner =>
                have hscope : scopeView inner = scopeView ctx ++ declarations specs := by
                  simp [scopeView, c6 inner rfl, ← hdecls']
                obtain ⟨r7, h7, c7⟩ := element_in_sound_of cs i name_end mark after empty env stack inner raws decls
                  budget1 lt nsplit hne' hq hmark' hraws' (fun _ => ih inner after budget1 progress (by omega))
                refine ⟨r7, by simp [h1, h2, hj2, h3, h4, h5, dzero, h6, h7,
                  core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
                intro e j' b' e7
                obtain ⟨hd, hname, hatts, hdist, hrest⟩ := c7 e j' b' e7
                rw [hscope] at hname hatts hrest
                exact element_finish tsplit hq hspecs all2 c3 uniq allowed hb1 (by rw [hd]; exact hdecls') hname hatts
                  hdist hrest

/-! ## References in content -/

/-- What a reference read in content stands for. -/
def RefOut (cs : alloc.vec.Vec U32) (i : Usize) (E : Env) (names : List Word) (scope : Scope) (budget : Usize)
    (nodes : alloc.vec.Vec xml.Node) (text : alloc.vec.Vec U32)
    (out : alloc.vec.Vec xml.Node × alloc.vec.Vec U32 × Usize × Usize) : Prop :=
  ∃ w x k, (word cs).drop i.val = w ++ (word cs).drop out.2.2.1.val ∧ w ≠ [] ∧
    Markup E names scope w x k ∧ out.2.2.2.val + k = budget.val ∧ Rel nodes text out.1 out.2.1 x

theorem content_reference_sound_of (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity)
    (stack : alloc.vec.Vec Usize) (ctx : alloc.vec.Vec xml.Binding) (budget : Usize)
    (nodes : alloc.vec.Vec xml.Node) (text : alloc.vec.Vec U32) {names : List Word}
    (hstack : StackOk env stack names) (amp : charAt cs i.val = 38)
    (ih : ∀ (t : alloc.vec.Vec U32) (stack' : alloc.vec.Vec Usize) (names' : List Word) (b : Usize),
      b.val < budget.val → StackOk env stack' names' → ContentSound t 0#usize env stack' ctx b nodes text names') :
    ∃ r, xml.content_reference cs i env stack ctx budget nodes text = .ok r ∧
      ∀ out, r = .Ok out → RefOut cs i (envView env) names (scopeView ctx) budget nodes text out := by
  unfold xml.content_reference
  obtain ⟨inside, hd⟩ := drop_nonzero (by rw [amp]; decide : charAt cs i.val ≠ 0)
  obtain ⟨r1, h1, sound1, _⟩ := reference_spec cs i amp
  cases r1 with
  | Err e => exact ⟨.Err e, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
  | Ok pair =>
    obtain ⟨ref, j1⟩ := pair
    obtain ⟨w, split1, j1v, meaning⟩ := sound1 ref j1 rfl
    have wne : w ≠ [] := List.ne_nil_of_length_pos (refMeaning_len meaning)
    cases ref with
    | Character c =>
      by_cases room : text.val.length < Usize.max
      · refine ⟨.Ok (nodes, alloc.vec.Vec.from (text.val ++ [c]) (by simp; omega), j1, budget),
          by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, push_char_eq, room], ?_⟩
        intro out e; simp only [core.result.Result.Ok.injEq] at e; subst e
        refine ⟨w, [.char c.val], 0, split1, wne, ?_, by simp,
          rel_chars nodes text (alloc.vec.Vec.from (text.val ++ [c]) (by simp; omega)) (word_push text c _)⟩
        rcases meaning with ⟨hr, xc⟩ | ⟨nm, hn, hp⟩
        · exact Markup.charRef hr xc
        · exact Markup.predefined hn hp
      · exact ⟨.Err ⟨.ResourceLimit, i⟩, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, push_char_eq,
          room, same_residual], by simp⟩
    | Entity s e =>
      obtain ⟨nm, ⟨rfl, ncn⟩, pre, sv, ev⟩ := meaning
      have nmSplit : (word cs).drop s.val = nm ++ (59 :: (word cs).drop j1.val) := by
        rw [sv]; have := split1; rw [hd] at this; simp at this; exact this.2
      obtain ⟨r3, h3, sound3, _⟩ := expandable_spec cs s e env stack i hstack nmSplit (by rw [ev, sv])
      cases r3 with
      | Err err =>
        exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h3, same_residual], by simp⟩
      | Ok k =>
        obtain ⟨ent, hent, first, hname, look, notIn⟩ := sound3 k rfl
        have kin : k.val < env.val.length := first.1
        have ek : env.val[k.val] = ent := by
          rw [List.getElem?_eq_getElem kin] at hent; exact Option.some.inj hent
        obtain ⟨r4, h4, c4⟩ := spend_spec env k budget i kin
        cases r4 with
        | Err err =>
          exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h3, h4, same_residual],
            by simp⟩
        | Ok b1 =>
          obtain ⟨costOk, b1v⟩ := c4
          rw [ek] at costOk b1v
          have room : stack.val.length < Usize.max := by
            refine stack_room hstack first (fun x hx e2 => ?_)
            apply notIn
            exact (hstack.2.2 _).mpr ⟨x, hx, by rw [e2]; simp [nameAt, hent, hname]⟩
          obtain ⟨stack', h5, hs5⟩ := pushed_spec stack k i room
          have hstack' : StackOk env stack' (word ent.«name» :: names) :=
            stack_push hstack first (by simp [nameAt, hent]) (by rw [hname]; exact notIn) hs5
          obtain ⟨r6, h6, sound6⟩ := ih ent.text stack' _ b1 (by omega) hstack'
          cases r6 with
          | Err err =>
            exact ⟨.Err ⟨err.kind, i⟩, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h3, h4, h5,
              alloc.vec.Vec.index_usize, List.getElem?_eq_getElem kin, ek, h6, xml.fail], by simp⟩
          | Ok out1 =>
            obtain ⟨nodes1, text1, stop, left⟩ := out1
            by_cases full : stop.val = ent.text.val.length
            · have fullU : stop = alloc.vec.Vec.len ent.text :=
                UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len_val, full])
              refine ⟨.Ok (nodes1, text1, j1, left), by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h3, h4,
                h5, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem kin, ek, h6, fullU], ?_⟩
              intro out eq; simp only [core.result.Result.Ok.injEq] at eq; subst eq
              obtain ⟨w1, items1, k1, split6, hc6, hb6, _, rel6⟩ := sound6 _ rfl
              have w1e : w1 = word ent.text := by
                have d : (word ent.text).drop stop.val = [] := List.drop_eq_nil_of_le (by rw [word_length]; omega)
                simp only at split6
                rw [d] at split6; simpa using split6.symm
              rw [w1e] at hc6
              refine ⟨38 :: nm ++ [59], items1, (word ent.text).length + 1 + k1, split1, by simp, ?_, ?_, rel6⟩
              · rw [← hname] at pre look notIn ⊢
                exact Markup.entity ⟨rfl, hname ▸ ncn⟩ pre look notIn hc6
              · simp only at hb6 ⊢; rw [word_length]; omega
            · have fullU : ¬ stop = alloc.vec.Vec.len ent.text := by
                intro h; apply full; rw [h]; simp [alloc.vec.Vec.len_val]
              exact ⟨.Err ⟨.EntityBoundary, i⟩, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h3, h4, h5,
                alloc.vec.Vec.index_usize, List.getElem?_eq_getElem kin, ek, h6, fullU, xml.fail], by simp⟩

/-! ## Content -/

theorem ruleOf_nonzero {cs : alloc.vec.Vec U32} {i : Nat} (h : ruleOf cs i ≠ .End) : charAt cs i ≠ 0 := by
  intro z; apply h; unfold ruleOf; simp [z]

theorem content_sound (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity)
    (stack : alloc.vec.Vec Usize) (ctx : alloc.vec.Vec xml.Binding) (budget : Usize)
    (nodes : alloc.vec.Vec xml.Node) (text : alloc.vec.Vec U32) {names : List Word}
    (henv : EnvOk env) (hstack : StackOk env stack names) :
    ContentSound cs i env stack ctx budget nodes text names := by
  unfold ContentSound
  rw [xml.content, content_rule_eq]
  simp only [bind_ok]
  cases hr : ruleOf cs i.val with
  | End =>
    refine ⟨.Ok (nodes, text, i, budget), rfl, ?_⟩
    intro out e; simp only [core.result.Result.Ok.injEq] at e; subst e
    exact ⟨[], [], 0, by simp, Content.nil, by simp, fun _ => rfl, rel_refl _ _⟩
  | Stop =>
    refine ⟨.Ok (nodes, text, i, budget), rfl, ?_⟩
    intro out e; simp only [core.result.Result.Ok.injEq] at e; subst e
    exact ⟨[], [], 0, by simp, Content.nil, by simp, fun _ => rfl, rel_refl _ _⟩
  | Chars =>
    have dc := ruleOf_chars hr
    obtain ⟨r1, h1, sound1, _⟩ := char_data_spec cs i text
    cases r1 with
    | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
    | Ok pair =>
      obtain ⟨text1, j⟩ := pair
      obtain ⟨hj, ht, nc⟩ := sound1 text1 j rfl
      have follow : ¬ DataChar (charAt cs j.val) := by rw [hj]; exact run_follow cs i.val (by simp [DataChar])
      have cdsplit := drop_run DataChar cs i.val
      rw [← hj] at cdsplit
      have allcd : ∀ c ∈ run DataChar ((word cs).drop i.val), DataChar c := run_all
      generalize hcd : run DataChar ((word cs).drop i.val) = cd at cdsplit hj ht nc allcd
      have cdne : cd ≠ [] := by
        intro e; rw [e] at hj; simp at hj
        rw [show j.val = i.val by omega] at follow; exact follow dc
      have progress := drop_lt cdsplit cdne
      obtain ⟨r2, h2, sound2⟩ := content_sound cs j env stack ctx budget nodes text1 henv hstack
      refine ⟨r2, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_⟩
      intro out e
      obtain ⟨w, items, k, wsplit, hc, hb, zero, rel⟩ := sound2 out e
      have start : w = [] ∨ ∃ c rest, w = c :: rest ∧ (c = 60 ∨ c = 38) := by
        rcases w with _ | ⟨c, rest⟩
        · left; rfl
        · right
          have cj : charAt cs j.val = c := first_char (rest := rest ++ (word cs).drop out.2.2.1.val)
            (by rw [wsplit]; simp)
          refine ⟨c, rest, rfl, ?_⟩
          by_cases z : c = 0
          · exfalso; have := zero (by rw [cj, z]); simp at this
          · simp only [DataChar] at follow
            rw [cj] at follow
            omega
      have hcd' : CharData cd := ⟨fun c hc => ⟨(allcd c hc).2.1, (allcd c hc).2.2⟩, nc⟩
      exact ⟨cd ++ w, chars cd ++ items, k, by rw [cdsplit, wsplit]; simp, content_prepend cdne hcd' hc start, hb,
        fun z => absurd z dc.1, rel_trans (rel_chars nodes text text1 ht) rel⟩
  | Comment =>
    have start := ruleOf_comment hr
    have nz := ruleOf_nonzero (by rw [hr]; simp)
    obtain ⟨r1, h1, sound1, _⟩ := comment_spec cs i start
    cases r1 with
    | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
    | Ok j =>
      obtain ⟨cw, csplit, hcw⟩ := sound1 j rfl
      have cwne : cw ≠ [] := by obtain ⟨body, rfl, _⟩ := hcw; simp [lit]
      have progress := drop_lt csplit cwne
      obtain ⟨r2, h2, sound2⟩ := content_sound cs j env stack ctx budget nodes text henv hstack
      refine ⟨r2, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_⟩
      intro out e
      obtain ⟨w, items, k, wsplit, hc, hb, _, rel⟩ := sound2 out e
      exact ⟨cw ++ w, [] ++ items, 0 + k, by rw [csplit, wsplit]; simp, Content.markup (Markup.comment hcw) hc,
        by simpa using hb, fun z => absurd z nz, by simpa using rel⟩
  | CData =>
    have start := ruleOf_cdata hr
    have nz := ruleOf_nonzero (by rw [hr]; simp)
    obtain ⟨r1, h1, sound1, _⟩ := cdata_spec cs i text start
    cases r1 with
    | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
    | Ok pair =>
      obtain ⟨text1, j⟩ := pair
      obtain ⟨cw, data, csplit, hcw, ht⟩ := sound1 text1 j rfl
      have cwne : cw ≠ [] := by rw [hcw.1, lit_cdata]; simp
      have progress := drop_lt csplit cwne
      obtain ⟨r2, h2, sound2⟩ := content_sound cs j env stack ctx budget nodes text1 henv hstack
      refine ⟨r2, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_⟩
      intro out e
      obtain ⟨w, items, k, wsplit, hc, hb, _, rel⟩ := sound2 out e
      exact ⟨cw ++ w, chars data ++ items, 0 + k, by rw [csplit, wsplit]; simp,
        Content.markup (Markup.cdata hcw) hc, by simpa using hb, fun z => absurd z nz,
        rel_trans (rel_chars nodes text text1 ht) rel⟩
  | Pi =>
    have start := pi_start (ruleOf_pi hr)
    have nz := ruleOf_nonzero (by rw [hr]; simp)
    obtain ⟨r1, h1, sound1, _⟩ := pi_spec cs i start
    cases r1 with
    | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
    | Ok j =>
      obtain ⟨cw, csplit, hcw⟩ := sound1 j rfl
      have cwne : cw ≠ [] := by obtain ⟨t, rest, rfl, _, _⟩ := hcw; simp [lit]
      have progress := drop_lt csplit cwne
      obtain ⟨r2, h2, sound2⟩ := content_sound cs j env stack ctx budget nodes text henv hstack
      refine ⟨r2, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_⟩
      intro out e
      obtain ⟨w, items, k, wsplit, hc, hb, _, rel⟩ := sound2 out e
      exact ⟨cw ++ w, [] ++ items, 0 + k, by rw [csplit, wsplit]; simp, Content.markup (Markup.pi hcw) hc,
        by simpa using hb, fun z => absurd z nz, by simpa using rel⟩
  | Reference =>
    have amp := ruleOf_reference hr
    have nz := ruleOf_nonzero (by rw [hr]; simp)
    obtain ⟨r1, h1, sound1⟩ := content_reference_sound_of cs i env stack ctx budget nodes text hstack amp
      (fun t stack' names' b hb hs => content_sound t 0#usize env stack' ctx b nodes text henv hs)
    cases r1 with
    | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
    | Ok out1 =>
      obtain ⟨nodes1, text1, j, budget1⟩ := out1
      obtain ⟨rw', x, k1, rsplit, rne, hm, hb1, rel1⟩ := sound1 _ rfl
      simp only at rsplit hb1 rel1
      have progress := drop_lt rsplit rne
      have spent : budget1.val ≤ budget.val := by omega
      obtain ⟨r2, h2, sound2⟩ := content_sound cs j env stack ctx budget1 nodes1 text1 henv hstack
      refine ⟨r2, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2], ?_⟩
      intro out e
      obtain ⟨w, items, k, wsplit, hc, hb, _, rel⟩ := sound2 out e
      exact ⟨rw' ++ w, x ++ items, k1 + k, by rw [rsplit, wsplit]; simp, Content.markup hm hc, by omega,
        fun z => absurd z nz, rel_trans rel1 rel⟩
  | Element =>
    have lt := (ruleOf_element hr).1
    have nz := ruleOf_nonzero (by rw [hr]; simp)
    obtain ⟨r1, h1, sound1⟩ := element_sound_of cs i env stack ctx budget henv hstack lt
      (fun ctx' j b hj hb => content_sound cs j env stack ctx' b (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) henv
        hstack)
    cases r1 with
    | Err err => exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
    | Ok triple =>
      obtain ⟨e, j, budget1⟩ := triple
      obtain ⟨we, ke, esplit, he, hb1⟩ := sound1 e j budget1 rfl
      have wne : we ≠ [] := by obtain ⟨rest, rfl⟩ := element_head he; simp
      have progress := drop_lt esplit wne
      obtain ⟨r2, h2, s2⟩ := flush_sound nodes text i
      cases r2 with
      | Err err =>
        exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2, same_residual], by simp⟩
      | Ok nodes1 =>
        obtain ⟨r3, h3, s3⟩ := push_node_sound nodes1 (.Element e) i
        cases r3 with
        | Err err =>
          exact ⟨.Err err, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2, h3, same_residual],
            by simp⟩
        | Ok nodes2 =>
          have rel1 := rel_element text e (s2 nodes1 rfl) (s3 nodes2 rfl)
          obtain ⟨r4, h4, sound4⟩ := content_sound cs j env stack ctx budget1 nodes2 (alloc.vec.Vec.new _) henv
            hstack
          refine ⟨r4, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h2, h3, h4], ?_⟩
          intro out eq
          obtain ⟨w, items, k, wsplit, hc, hb, _, rel⟩ := sound4 out eq
          exact ⟨we ++ w, [.elem e] ++ items, ke + k, by rw [esplit, wsplit]; simp,
            Content.markup (Markup.element he) hc, by omega, fun z => absurd z nz, rel_trans rel1 rel⟩
  | Invalid =>
    exact ⟨.Err ⟨.Syntax, i⟩, by simp [xml.fail], by simp⟩
termination_by (budget.val, cs.val.length - i.val)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; omega)
    | (simp only [Prod.lex_def]; omega)

end Rowl.XmlElements
