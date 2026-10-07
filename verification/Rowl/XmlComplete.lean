import Rowl.XmlElements

/-!
# Reading elements and content is complete

Every element and content the grammar derives, within the budget and with
room for the buffers, is read by `element` and `content`, which return
exactly the element of the derivation and the items of the content.
-/

namespace Rowl.XmlComplete
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs Rowl.XmlEntities Rowl.XmlAttributes Rowl.XmlTags Rowl.XmlNamespaces Rowl.XmlContent Rowl.XmlElements
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ## Values are determined by their views -/

theorem optWord_inj {a b : Option (alloc.vec.Vec U32)} (h : optWord a = optWord b) : a = b := by
  cases a <;> cases b <;> simp [optWord] at h ⊢
  exact word_inj h

theorem bindingView_inj {a b : xml.Binding} (h : bindingView a = bindingView b) : a = b := by
  obtain ⟨p, v⟩ := a
  obtain ⟨p', v'⟩ := b
  simp only [bindingView, Prod.mk.injEq] at h
  rw [optWord_inj h.1, word_inj h.2]

theorem nodeView_inj {a b : xml.Node} (h : nodeView a = nodeView b) : a = b := by
  cases a <;> cases b <;> simp [nodeView] at h ⊢
  · exact h
  · exact word_inj h

theorem map_inj_of {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l1 l2 : List α}, l1.map f = l2.map f → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l1, b :: l2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf a b h.1, map_inj_of hf h.2]

theorem elementName_unique_of {scope : Scope} {n n' : Word} {p1 p2 ns1 ns2 : Option Word} {l1 l2 : Word}
    (h1 : ElementName scope n p1 ns1 l1) (h2 : ElementName scope n' p2 ns2 l2) (same : n = n') :
    p1 = p2 ∧ ns1 = ns2 ∧ l1 = l2 := by
  cases h1 with
  | unprefixed ncn =>
    cases h2 with
    | unprefixed _ => exact ⟨rfl, rfl, same⟩
    | prefixed _ _ _ _ => exact absurd (by rw [same]; simp) ncn.2
  | prefixed hp hl hx hv =>
    cases h2 with
    | unprefixed ncn => exact absurd (by rw [← same]; simp) ncn.2
    | prefixed hp' hl' hx' hv' =>
      obtain ⟨e1, e2⟩ := colon_split_unique hp.2 hp'.2 same
      subst e1; subst e2
      rw [hv] at hv'
      exact ⟨rfl, by simpa using hv', rfl⟩

theorem attributeName_unique_of {scope : Scope} {n n' : Word} {p1 p2 ns1 ns2 : Option Word} {l1 l2 : Word}
    (h1 : AttributeName scope n p1 ns1 l1) (h2 : AttributeName scope n' p2 ns2 l2) (same : n = n') :
    p1 = p2 ∧ ns1 = ns2 ∧ l1 = l2 := by
  cases h1 with
  | unprefixed ncn =>
    cases h2 with
    | unprefixed _ => exact ⟨rfl, rfl, same⟩
    | prefixed _ _ _ => exact absurd (by rw [same]; simp) ncn.2
  | prefixed hp hl hv =>
    cases h2 with
    | unprefixed ncn => exact absurd (by rw [← same]; simp) ncn.2
    | prefixed hp' hl' hv' =>
      obtain ⟨e1, e2⟩ := colon_split_unique hp.2 hp'.2 same
      subst e1; subst e2
      rw [hv] at hv'
      exact ⟨rfl, by simpa using hv', rfl⟩

theorem attOk_unique {scope : Scope} :
    ∀ {specs : List (Word × Word)} {xs ys : List xml.Attribute},
      List.Forall₂ (AttOk scope) specs xs → List.Forall₂ (AttOk scope) specs ys → xs = ys
  | [], [], [], _, _ => rfl
  | _ :: _, a :: xs, b :: ys, .cons ha hrest, .cons hb hrest' => by
    obtain ⟨na, va⟩ := ha
    obtain ⟨nb, vb⟩ := hb
    obtain ⟨e1, e2, e3⟩ := attributeName_unique_of na nb rfl
    have : a = b := by
      obtain ⟨p, ns, l, v⟩ := a
      obtain ⟨p', ns', l', v'⟩ := b
      simp only at e1 e2 e3 va vb
      rw [optWord_inj e1, optWord_inj e2, word_inj e3, word_inj (va.trans vb.symm)]
    rw [this, attOk_unique hrest hrest']

/-- The element whose fields have the views of `e`'s is `e`. -/
theorem element_eq {e : xml.Element} {pre ns : Option (alloc.vec.Vec U32)} {lv : alloc.vec.Vec U32}
    {attrs : alloc.vec.Vec xml.Attribute} {decls : alloc.vec.Vec xml.Binding} {children : alloc.vec.Vec xml.Node}
    (h1 : optWord pre = optWord e.ns_prefix) (h2 : optWord ns = optWord e.ns_name) (h3 : word lv = word e.local_name)
    (h4 : attrs = e.attributes) (h5 : decls.val.map bindingView = e.declarations.val.map bindingView)
    (h6 : children.val.map nodeView = e.children.val.map nodeView) :
    xml.Element.mk pre ns lv attrs decls children = e := by
  obtain ⟨p', ns', lv', attrs', decls', children'⟩ := e
  simp only [xml.Element.ns_prefix._simpLemma_, xml.Element.ns_name._simpLemma_,
    xml.Element.local_name._simpLemma_, xml.Element.attributes._simpLemma_,
    xml.Element.declarations._simpLemma_, xml.Element.children._simpLemma_] at h1 h2 h3 h4 h5 h6
  have d : decls = decls' := by apply alloc.vec.Vec.ext; exact map_inj_of (fun _ _ => bindingView_inj) h5
  have c : children = children' := by apply alloc.vec.Vec.ext; exact map_inj_of (fun _ _ => nodeView_inj) h6
  rw [optWord_inj h1, optWord_inj h2, word_inj h3, h4, d, c]

/-! ## What completeness states -/

/-- Reading an element the grammar derives returns it. -/
def ElementGoal (E : Env) (names : List Word) (scope : Scope) (w : Word) (e : xml.Element) (k : Nat) : Prop :=
  ∀ (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity) (stack : alloc.vec.Vec Usize)
    (ctx : alloc.vec.Vec xml.Binding) (budget : Usize) (rest : Word),
    E = envView env → EnvOk env → StackOk env stack names → NoZero cs → scope = scopeView ctx →
    (word cs).drop i.val = w ++ rest → k ≤ budget.val → ctx.val.length + w.length + k ≤ Usize.max →
    ∃ j b', xml.element cs i env stack ctx budget = .ok (.Ok (e, j, b')) ∧ j.val = i.val + w.length ∧
      b'.val + k = budget.val

/-- Reading content the grammar derives, up to the end or an end tag,
    returns its items. -/
def ContentGoal (E : Env) (names : List Word) (scope : Scope) (w : Word) (items : List Item) (k : Nat) : Prop :=
  ∀ (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity) (stack : alloc.vec.Vec Usize)
    (ctx : alloc.vec.Vec xml.Binding) (budget : Usize) (nodes : alloc.vec.Vec xml.Node) (text : alloc.vec.Vec U32)
    (rest : Word),
    E = envView env → EnvOk env → StackOk env stack names → NoZero cs → scope = scopeView ctx →
    (word cs).drop i.val = w ++ rest → (rest = [] ∨ ∃ more, rest = 60 :: 47 :: more) → k ≤ budget.val →
    ctx.val.length + nodes.val.length + text.val.length + w.length + k ≤ Usize.max →
    ∃ nodes' text' j b', xml.content cs i env stack ctx budget nodes text = .ok (.Ok (nodes', text', j, b')) ∧
      j.val = i.val + w.length ∧ b'.val + k = budget.val ∧ Rel nodes text nodes' text' items ∧
      nodes'.val.length + text'.val.length ≤ nodes.val.length + text.val.length + w.length + k

/-- Reading one item of markup the grammar derives continues reading
    content after it with its items added. -/
def MarkupGoal (E : Env) (names : List Word) (scope : Scope) (m : Word) (x : List Item) (k : Nat) : Prop :=
  ∀ (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity) (stack : alloc.vec.Vec Usize)
    (ctx : alloc.vec.Vec xml.Binding) (budget : Usize) (nodes : alloc.vec.Vec xml.Node) (text : alloc.vec.Vec U32)
    (rest : Word),
    E = envView env → EnvOk env → StackOk env stack names → NoZero cs → scope = scopeView ctx →
    (word cs).drop i.val = m ++ rest → k ≤ budget.val →
    ctx.val.length + nodes.val.length + text.val.length + m.length + k ≤ Usize.max →
    ∃ nodes1 text1 j b1, xml.content cs i env stack ctx budget nodes text =
        xml.content cs j env stack ctx b1 nodes1 text1 ∧
      j.val = i.val + m.length ∧ b1.val + k = budget.val ∧ Rel nodes text nodes1 text1 x ∧
      nodes1.val.length + text1.val.length ≤ nodes.val.length + text.val.length + m.length + k

/-! ## What content begins with, from the grammar -/

theorem ruleOf_of_end {cs : alloc.vec.Vec U32} {i : Nat} (h : charAt cs i = 0) : ruleOf cs i = .End := by
  simp [ruleOf, h]

theorem ruleOf_of_stop {cs : alloc.vec.Vec U32} {i : Nat} (h1 : charAt cs i = 60) (h2 : charAt cs (i + 1) = 47) :
    ruleOf cs i = .Stop := by
  simp [ruleOf, h1, h2]

theorem ruleOf_of_chars {cs : alloc.vec.Vec U32} {i : Nat} (h : DataChar (charAt cs i)) :
    ruleOf cs i = .Chars := by
  obtain ⟨a, b, c⟩ := h; simp [ruleOf, a, b, c]

theorem ruleOf_of_comment {cs : alloc.vec.Vec U32} {i : Nat} (h : lit "<!--" <+: (word cs).drop i) :
    ruleOf cs i = .Comment := by
  obtain ⟨t, ht⟩ := h
  have d : (word cs).drop i = 60 :: 33 :: (45 :: 45 :: t) := by rw [← ht, lit_comment]; rfl
  obtain ⟨a, b⟩ := two_chars d
  have pre : lit "<!--" <+: (word cs).drop i := ⟨t, ht⟩
  simp [ruleOf, a, b, pre]

theorem ruleOf_of_cdata {cs : alloc.vec.Vec U32} {i : Nat} (h : lit "<![CDATA[" <+: (word cs).drop i) :
    ruleOf cs i = .CData := by
  obtain ⟨t, ht⟩ := h
  have d : (word cs).drop i = 60 :: 33 :: (91 :: 67 :: 68 :: 65 :: 84 :: 65 :: 91 :: t) := by
    rw [← ht, lit_cdata]; rfl
  obtain ⟨a, b⟩ := two_chars d
  have pre : lit "<![CDATA[" <+: (word cs).drop i := ⟨t, ht⟩
  have npre : ¬ lit "<!--" <+: (word cs).drop i := by
    rintro ⟨t', ht'⟩; rw [lit_comment, d] at ht'; simp at ht'
  simp [ruleOf, a, b, pre, npre]

theorem ruleOf_of_pi {cs : alloc.vec.Vec U32} {i : Nat} (h1 : charAt cs i = 60) (h2 : charAt cs (i + 1) = 63) :
    ruleOf cs i = .Pi := by
  simp [ruleOf, h1, h2]

theorem ruleOf_of_reference {cs : alloc.vec.Vec U32} {i : Nat} (h : charAt cs i = 38) :
    ruleOf cs i = .Reference := by
  simp [ruleOf, h]

theorem ruleOf_of_element {cs : alloc.vec.Vec U32} {i : Nat} (h1 : charAt cs i = 60)
    (h2 : NameStartChar (charAt cs (i + 1))) : ruleOf cs i = .Element := by
  have a : charAt cs (i + 1) ≠ 47 := fun e => by rw [e] at h2; simp [NameStartChar] at h2
  have b : charAt cs (i + 1) ≠ 33 := fun e => by rw [e] at h2; simp [NameStartChar] at h2
  have c : charAt cs (i + 1) ≠ 63 := fun e => by rw [e] at h2; simp [NameStartChar] at h2
  simp [ruleOf, h1, a, b, c]

/-! ## Character data and the end of content -/

/-- Character data in content: read into the pending characters. -/
theorem content_chars_step (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity)
    (stack : alloc.vec.Vec Usize) (ctx : alloc.vec.Vec xml.Binding) (budget : Usize)
    (nodes : alloc.vec.Vec xml.Node) (text : alloc.vec.Vec U32) {cd more : Word}
    (split : (word cs).drop i.val = cd ++ more) (hne : cd ≠ []) (hcd : CharData cd) (nz : ∀ c ∈ cd, c ≠ 0)
    (stop : ∀ c m, more = c :: m → ¬ DataChar c) (room : text.val.length + cd.length ≤ Usize.max) :
    ∃ text1 j, xml.content cs i env stack ctx budget nodes text =
        xml.content cs j env stack ctx budget nodes text1 ∧
      word text1 = word text ++ cd ∧ j.val = i.val + cd.length := by
  have alld : ∀ c ∈ cd, DataChar c := fun c hc => ⟨nz c hc, (hcd.1 c hc).1, (hcd.1 c hc).2⟩
  have runcd : run DataChar ((word cs).drop i.val) = cd := by rw [split]; exact run_unique alld stop
  obtain ⟨c0, cs0, hc0⟩ := List.exists_cons_of_ne_nil hne
  have first : charAt cs i.val = c0 := first_char (rest := cs0 ++ more) (by rw [split, hc0]; simp)
  have dc : DataChar (charAt cs i.val) := by rw [first]; exact alld c0 (by rw [hc0]; simp)
  obtain ⟨r1, h1, sound1, complete1⟩ := char_data_spec cs i text
  rw [runcd] at sound1 complete1
  obtain ⟨t, j, hr⟩ := complete1 hcd.2 room
  subst hr
  obtain ⟨hj, ht, _⟩ := sound1 t j rfl
  refine ⟨t, j, ?_, ht, hj⟩
  conv => lhs; rw [xml.content]
  rw [content_rule_eq, ruleOf_of_chars dc]
  simp [h1, core.result.Result.Insts.CoreOpsTry.branch]

theorem content_nil_goal {E : Env} {names : List Word} {scope : Scope} : ContentGoal E names scope [] [] 0 := by
  intro cs i env stack ctx budget nodes text rest hE henv hstack nz hscope split follow kb room
  refine ⟨nodes, text, i, budget, ?_, by simp, by simp, rel_refl _ _, by simp⟩
  rw [xml.content, content_rule_eq]
  simp only [List.nil_append] at split
  rcases follow with rfl | ⟨more, rfl⟩
  · have z : charAt cs i.val = 0 := by
      have := charAt_after (cs := cs) (i := i.val) (w := []) (rest := []) (by simpa using split)
      simpa using this
    rw [ruleOf_of_end z]; simp
  · obtain ⟨a, b⟩ := two_chars split
    rw [ruleOf_of_stop a b]; simp

theorem stop_of_follow {rest : Word} (follow : rest = [] ∨ ∃ more, rest = 60 :: 47 :: more) :
    ∀ c m, rest = c :: m → ¬ DataChar c := by
  intro c m e
  rcases follow with rfl | ⟨more, rfl⟩
  · simp at e
  · simp at e; rw [e.1]; simp [DataChar]

theorem content_last_goal {E : Env} {names : List Word} {scope : Scope} {cd : Word} (hne : cd ≠ [])
    (hcd : CharData cd) : ContentGoal E names scope cd (cd.map .char) 0 := by
  intro cs i env stack ctx budget nodes text rest hE henv hstack nz hscope split follow kb room
  obtain ⟨text1, j, eq, ht, hj⟩ := content_chars_step cs i env stack ctx budget nodes text split hne hcd
    (nz_of_drop nz split) (stop_of_follow follow) (by omega)
  have dj : (word cs).drop j.val = [] ++ rest := by rw [hj]; simpa using drop_after split
  have tl : text1.val.length = text.val.length + cd.length := by
    rw [← word_length, ht, ← word_length text]; simp
  obtain ⟨nodes', text', j', b', run, hj', hb', rel, size⟩ := content_nil_goal cs j env stack ctx budget nodes
    text1 rest hE henv hstack nz hscope dj follow (by simp) (by simp; omega)
  simp only [List.length_nil] at size hj'
  refine ⟨nodes', text', j', b', by rw [eq, run], by rw [hj', hj]; simp, by simpa using hb', ?_, by omega⟩
  have := rel_trans (rel_chars nodes text text1 ht) rel
  simpa [chars] using this

theorem content_data_goal {E : Env} {names : List Word} {scope : Scope} {cd m rest : Word} {x items : List Item}
    {k1 k2 : Nat} (hne : cd ≠ []) (hcd : CharData cd) (mhead : ∃ c t, m = c :: t ∧ (c = 60 ∨ c = 38))
    (hm : MarkupGoal E names scope m x k1) (hr : ContentGoal E names scope rest items k2) :
    ContentGoal E names scope (cd ++ m ++ rest) (cd.map .char ++ x ++ items) (k1 + k2) := by
  intro cs i env stack ctx budget nodes text tail hE henv hstack nz hscope split follow kb room
  obtain ⟨c, t, hmc, hc⟩ := mhead
  have split' : (word cs).drop i.val = cd ++ (m ++ rest ++ tail) := by rw [split]; simp
  obtain ⟨text1, j, eq1, ht, hj⟩ := content_chars_step cs i env stack ctx budget nodes text split' hne hcd
    (nz_of_drop nz split') (by
      intro c' m' e; rw [hmc] at e; simp at e; rw [← e.1]
      rcases hc with rfl | rfl <;> simp [DataChar])
    (by simp at room; omega)
  have dj : (word cs).drop j.val = m ++ (rest ++ tail) := by rw [hj]; simpa using drop_after split'
  have tl : text1.val.length = text.val.length + cd.length := by
    rw [← word_length, ht, ← word_length text]; simp
  simp only [List.length_append] at room
  obtain ⟨nodes1, text2, j2, b1, eq2, hj2, hb1, rel1, size1⟩ := hm cs j env stack ctx budget nodes text1
    (rest ++ tail) hE henv hstack nz hscope dj (by omega) (by omega)
  have dj2 : (word cs).drop j2.val = rest ++ tail := by rw [hj2]; exact drop_after dj
  obtain ⟨nodes', text', j', b', run, hj', hb', rel2, size2⟩ := hr cs j2 env stack ctx b1 nodes1 text2 tail hE
    henv hstack nz hscope dj2 follow (by omega) (by omega)
  refine ⟨nodes', text', j', b', by rw [eq1, eq2, run], by rw [hj', hj2, hj]; simp; omega, by omega, ?_,
    by simp; omega⟩
  have := rel_trans (rel_trans (rel_chars nodes text text1 ht) rel1) rel2
  simpa [chars, List.append_assoc] using this

theorem content_markup_goal {E : Env} {names : List Word} {scope : Scope} {m rest : Word} {x items : List Item}
    {k1 k2 : Nat} (hm : MarkupGoal E names scope m x k1) (hr : ContentGoal E names scope rest items k2) :
    ContentGoal E names scope (m ++ rest) (x ++ items) (k1 + k2) := by
  intro cs i env stack ctx budget nodes text tail hE henv hstack nz hscope split follow kb room
  have split' : (word cs).drop i.val = m ++ (rest ++ tail) := by rw [split]; simp
  simp only [List.length_append] at room
  obtain ⟨nodes1, text1, j, b1, eq1, hj, hb1, rel1, size1⟩ := hm cs i env stack ctx budget nodes text
    (rest ++ tail) hE henv hstack nz hscope split' (by omega) (by omega)
  have dj : (word cs).drop j.val = rest ++ tail := by rw [hj]; exact drop_after split'
  obtain ⟨nodes', text', j', b', run, hj', hb', rel2, size2⟩ := hr cs j env stack ctx b1 nodes1 text1 tail hE
    henv hstack nz hscope dj follow (by omega) (by omega)
  exact ⟨nodes', text', j', b', by rw [eq1, run], by rw [hj', hj]; simp; omega, by omega, rel_trans rel1 rel2,
    by simp; omega⟩

/-! ## Markup -/

theorem markup_comment_goal {E : Env} {names : List Word} {scope : Scope} {w : Word} (hc : Comment w) :
    MarkupGoal E names scope w [] 0 := by
  intro cs i env stack ctx budget nodes text rest hE henv hstack nz hscope split kb room
  have start : lit "<!--" <+: (word cs).drop i.val := by
    obtain ⟨body, rfl, _⟩ := hc; rw [split]; exact ⟨body ++ lit "-->" ++ rest, by simp⟩
  obtain ⟨r, hr, _, complete⟩ := comment_spec cs i start
  obtain ⟨j, hj, hjv⟩ := complete w rest split hc (nz_of_drop nz split)
  subst hj
  refine ⟨nodes, text, j, budget, ?_, hjv, by simp, rel_refl _ _, by omega⟩
  conv => lhs; rw [xml.content]
  rw [content_rule_eq, ruleOf_of_comment start]
  simp [hr, core.result.Result.Insts.CoreOpsTry.branch]

theorem markup_pi_goal {E : Env} {names : List Word} {scope : Scope} {w : Word} (hp : PI w) :
    MarkupGoal E names scope w [] 0 := by
  intro cs i env stack ctx budget nodes text rest hE henv hstack nz hscope split kb room
  obtain ⟨t, rest', hw, _, _⟩ := id hp
  have start : lit "<?" <+: (word cs).drop i.val := by
    rw [split, hw]; exact ⟨t ++ rest' ++ lit "?>" ++ rest, by simp⟩
  have ab : charAt cs i.val = 60 ∧ charAt cs (i.val + 1) = 63 :=
    two_chars (rest := t ++ rest' ++ lit "?>" ++ rest) (by rw [split, hw, lit_pi]; simp)
  obtain ⟨r, hr, _, complete⟩ := pi_spec cs i start
  obtain ⟨j, hj, hjv⟩ := complete w rest split hp (nz_of_drop nz split)
  subst hj
  refine ⟨nodes, text, j, budget, ?_, hjv, by simp, rel_refl _ _, by omega⟩
  conv => lhs; rw [xml.content]
  rw [content_rule_eq, ruleOf_of_pi ab.1 ab.2]
  simp [hr, core.result.Result.Insts.CoreOpsTry.branch]

theorem markup_cdata_goal {E : Env} {names : List Word} {scope : Scope} {w data : Word} (hc : CDSect w data) :
    MarkupGoal E names scope w (data.map .char) 0 := by
  intro cs i env stack ctx budget nodes text rest hE henv hstack nz hscope split kb room
  have start : lit "<![CDATA[" <+: (word cs).drop i.val := by
    rw [split, hc.1]; exact ⟨data ++ lit "]]>" ++ rest, by simp⟩
  have dlen : data.length ≤ w.length := by rw [hc.1]; simp; omega
  obtain ⟨r, hr, sound, complete⟩ := cdata_spec cs i text start
  obtain ⟨t, j, hj, hjv⟩ := complete w data rest split hc (nz_of_drop nz split) (by omega)
  subst hj
  obtain ⟨w', data', split', hc', ht⟩ := sound t j rfl
  have dj : (word cs).drop j.val = rest := by rw [hjv]; exact drop_after split
  have ww : w' = w := by rw [dj] at split'; exact List.append_cancel_right (split'.symm.trans split)
  subst ww
  have dd : data' = data := by
    have := hc'.1.symm.trans hc.1
    simpa [List.append_assoc] using this
  subst dd
  have tl : t.val.length = text.val.length + data'.length := by
    rw [← word_length, ht, ← word_length text]; simp
  refine ⟨nodes, t, j, budget, ?_, hjv, by simp, rel_chars nodes text t ht, by omega⟩
  conv => lhs; rw [xml.content]
  rw [content_rule_eq, ruleOf_of_cdata start]
  simp [hr, core.result.Result.Insts.CoreOpsTry.branch]

theorem markup_charRef_goal {E : Env} {names : List Word} {scope : Scope} {w : Word} {v : Nat}
    (hr : CharRef w v) (hx : Rowl.Unicode.XmlChar v) : MarkupGoal E names scope w [.char v] 0 := by
  intro cs i env stack ctx budget nodes text rest hE henv hstack nz hscope split kb room
  obtain ⟨t, ht⟩ := charRef_head hr
  have amp : charAt cs i.val = 38 := first_char (rest := t ++ rest) (by rw [split, ht]; rfl)
  have wpos : 0 < w.length := charRef_len hr
  obtain ⟨r1, h1, sound1, complete1⟩ := reference_spec cs i amp
  obtain ⟨ref, j, hr1, hj⟩ := complete1 w rest split (Or.inl ⟨v, hr, hx⟩)
  subst hr1
  obtain ⟨w', split', hj', meaning⟩ := sound1 ref j rfl
  have ww : w' = w := same_consumed split' split (by omega)
  subst ww
  cases ref with
  | Entity s e => exfalso; obtain ⟨nm, hn, _⟩ := meaning; exact charRef_not_entity hr hn
  | Character c =>
    have cv : c.val = v := by
      rcases meaning with ⟨hr', _⟩ | ⟨nm, hn, _⟩
      · exact charRef_unique hr' hr
      · exact (charRef_not_entity hr hn).elim
    have roomT : text.val.length < Usize.max := by omega
    refine ⟨nodes, alloc.vec.Vec.from (text.val ++ [c]) (by simp; omega), j, budget, ?_, hj, by simp, ?_,
      by simp; omega⟩
    · conv => lhs; rw [xml.content]
      rw [content_rule_eq, ruleOf_of_reference amp]
      simp only [bind_ok]
      rw [xml.content_reference]
      simp [h1, core.result.Result.Insts.CoreOpsTry.branch, push_char_eq, roomT]
    · have := rel_chars nodes text (alloc.vec.Vec.from (text.val ++ [c]) (by simp; omega)) (word_push text c _)
      simpa [chars, cv] using this

theorem markup_predefined_goal {E : Env} {names : List Word} {scope : Scope} {w ename : Word} {v : Nat}
    (hr : EntityRef w ename) (hp : predefinedChar ename = some v) : MarkupGoal E names scope w [.char v] 0 := by
  intro cs i env stack ctx budget nodes text rest hE henv hstack nz hscope split kb room
  obtain ⟨t, ht⟩ := entityRef_head hr
  have amp : charAt cs i.val = 38 := first_char (rest := t ++ rest) (by rw [split, ht]; rfl)
  have wpos : 0 < w.length := by rw [ht]; simp
  obtain ⟨r1, h1, sound1, complete1⟩ := reference_spec cs i amp
  obtain ⟨ref, j, hr1, hj⟩ := complete1 w rest split (Or.inr ⟨ename, hr⟩)
  subst hr1
  obtain ⟨w', split', hj', meaning⟩ := sound1 ref j rfl
  have ww : w' = w := same_consumed split' split (by omega)
  subst ww
  cases ref with
  | Entity s e =>
    exfalso; obtain ⟨nm, hn, hpn, _⟩ := meaning
    rw [entityRef_unique hn hr, hp] at hpn; simp at hpn
  | Character c =>
    have cv : c.val = v := by
      rcases meaning with ⟨hr', _⟩ | ⟨nm, hn, hpn⟩
      · exact (charRef_not_entity hr' hr).elim
      · rw [entityRef_unique hn hr, hp] at hpn; simpa using hpn.symm
    have roomT : text.val.length < Usize.max := by omega
    refine ⟨nodes, alloc.vec.Vec.from (text.val ++ [c]) (by simp; omega), j, budget, ?_, hj, by simp, ?_,
      by simp; omega⟩
    · conv => lhs; rw [xml.content]
      rw [content_rule_eq, ruleOf_of_reference amp]
      simp only [bind_ok]
      rw [xml.content_reference]
      simp [h1, core.result.Result.Insts.CoreOpsTry.branch, push_char_eq, roomT]
    · have := rel_chars nodes text (alloc.vec.Vec.from (text.val ++ [c]) (by simp; omega)) (word_push text c _)
      simpa [chars, cv] using this

theorem markup_entity_goal {E : Env} {names : List Word} {scope : Scope} {w ename text : Word} {items : List Item}
    {k : Nat} (hr : EntityRef w ename) (hp : predefinedChar ename = none)
    (hl : lookup E ename = some (.internal text)) (hn : ename ∉ names)
    (hc : ContentGoal E (ename :: names) scope text items k) :
    MarkupGoal E names scope w items (text.length + 1 + k) := by
  intro cs i env stack ctx budget nodes textb rest hE henv hstack nz hscope split kb room
  subst hE
  obtain ⟨t, ht⟩ := entityRef_head hr
  have amp : charAt cs i.val = 38 := first_char (rest := t ++ rest) (by rw [split, ht]; rfl)
  obtain ⟨inside, hd⟩ := drop_nonzero (by rw [amp]; decide : charAt cs i.val ≠ 0)
  have wpos : 0 < w.length := by rw [ht]; simp
  obtain ⟨r1, h1, sound1, complete1⟩ := reference_spec cs i amp
  obtain ⟨ref, j, hr1, hj⟩ := complete1 w rest split (Or.inr ⟨ename, hr⟩)
  subst hr1
  obtain ⟨w', split', hj', meaning⟩ := sound1 ref j rfl
  have ww : w' = w := same_consumed split' split (by omega)
  subst ww
  cases ref with
  | Character c =>
    exfalso
    rcases meaning with ⟨hr', _⟩ | ⟨nm, hn', hpn⟩
    · exact charRef_not_entity hr' hr
    · rw [entityRef_unique hn' hr, hp] at hpn; simp at hpn
  | Entity s e =>
    obtain ⟨nm, hnm, _, sv, ev⟩ := meaning
    have nme : nm = ename := entityRef_unique hnm hr
    subst nme
    obtain ⟨wsplit, _⟩ := hr
    have nmSplit : (word cs).drop s.val = nm ++ (59 :: rest) := by
      rw [sv]; have := split; rw [hd, wsplit] at this; simp at this; exact this.2
    obtain ⟨r3, h3, sound3, complete3⟩ := expandable_spec cs s e env stack i hstack nmSplit (by rw [ev, sv])
    obtain ⟨k', hk'⟩ := complete3 text hl hn
    subst hk'
    obtain ⟨ent, hent, first, hname, look, _⟩ := sound3 k' rfl
    have tx : word ent.text = text := by rw [hl] at look; simpa using look.symm
    have kin : k'.val < env.val.length := first.1
    have ek : env.val[k'.val] = ent := by rw [List.getElem?_eq_getElem kin] at hent; exact Option.some.inj hent
    have tl : ent.text.val.length = text.length := by rw [← word_length, tx]
    obtain ⟨r4, h4, c4⟩ := spend_spec env k' budget i kin
    cases r4 with
    | Err err => exfalso; simp only [ek] at c4; omega
    | Ok b1 =>
      obtain ⟨costOk, b1v⟩ := c4
      rw [ek] at costOk b1v
      have room' : stack.val.length < Usize.max := by
        refine stack_room hstack first (fun x hx e2 => ?_)
        apply hn
        exact (hstack.2.2 _).mpr ⟨x, hx, by rw [e2]; simp [nameAt, hent, hname]⟩
      obtain ⟨stack', h5, hs5⟩ := pushed_spec stack k' i room'
      have hstack' : StackOk env stack' (nm :: names) :=
        stack_push hstack first (by simp [nameAt, hent, hname]) hn hs5
      obtain ⟨nodes', text', j', b', run, hj'', hb', rel, size⟩ := hc ent.text 0#usize env stack' ctx b1 nodes
        textb [] rfl henv hstack' (henv ent (by rw [← ek]; exact List.getElem_mem kin)) hscope (by simp [tx])
        (Or.inl rfl) (by omega) (by omega)
      have full : j' = alloc.vec.Vec.len ent.text :=
        UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len_val] at hj'' ⊢; omega)
      refine ⟨nodes', text', j, b', ?_, hj, by omega, rel, by omega⟩
      conv => lhs; rw [xml.content]
      rw [content_rule_eq, ruleOf_of_reference amp]
      simp only [bind_ok]
      rw [xml.content_reference]
      simp [h1, core.result.Result.Insts.CoreOpsTry.branch, h3, h4, h5, alloc.vec.Vec.index_usize,
        List.getElem?_eq_getElem kin, ek, run, full]

theorem markup_element_goal {E : Env} {names : List Word} {scope : Scope} {w : Word} {e : xml.Element} {k : Nat}
    (hw : ∃ c rest, w = 60 :: c :: rest ∧ NameStartChar c) (he : ElementGoal E names scope w e k) :
    MarkupGoal E names scope w [.elem e] k := by
  intro cs i env stack ctx budget nodes text rest hE henv hstack nz hscope split kb room
  obtain ⟨c, more, hwc, hc⟩ := hw
  have wl : 2 ≤ w.length := by rw [hwc]; simp
  have ab : charAt cs i.val = 60 ∧ charAt cs (i.val + 1) = c :=
    two_chars (rest := more ++ rest) (by rw [split, hwc]; simp)
  obtain ⟨j, b1, run, hj, hb1⟩ := he cs i env stack ctx budget rest hE henv hstack nz hscope split kb (by omega)
  obtain ⟨nodes1, h2, v2, l2⟩ := flush_eq nodes text i (by omega)
  obtain ⟨nodes2, h3, v3⟩ := push_node_eq nodes1 (.Element e) i (by omega)
  refine ⟨nodes2, alloc.vec.Vec.new _, j, b1, ?_, hj, hb1, rel_element text e v2 v3, ?_⟩
  · conv => lhs; rw [xml.content]
    rw [content_rule_eq, ruleOf_of_element ab.1 (by rw [ab.2]; exact hc)]
    simp [run, core.result.Result.Insts.CoreOpsTry.branch, h2, h3]
  · rw [v3]; simp; omega

/-! ## Start tags -/

theorem attText_length {E : Env} {names : List Word} {q : Option Nat} {body value : Word} {k : Nat}
    (h : AttText E names q body value k) : value.length ≤ body.length + k := by
  induction h with
  | nil => simp
  | char _ _ _ _ ih => simp; omega
  | charRef hr _ _ ih => have := charRef_len hr; simp; omega
  | predefined hr _ _ ih => obtain ⟨t, rfl⟩ := entityRef_head hr; simp; omega
  | entity hr _ _ _ _ _ ih1 ih2 => obtain ⟨t, rfl⟩ := entityRef_head hr; simp; omega

theorem specs_bound {E : Env} {names : List Word} {attrs : Word} {specs : List (Word × Word)} {k : Nat}
    (h : Specs E names attrs specs k) :
    (∀ sp ∈ specs, sp.2.length ≤ attrs.length + k) ∧ specs.length ≤ attrs.length := by
  induction h with
  | nil => simp
  | cons hs hq he hv hrest ih =>
    obtain ⟨q, body, _, rfl, hat⟩ := hv
    have := attText_length hat
    have sne : 0 < _ := List.length_pos_of_ne_nil hs.1
    refine ⟨?_, ?_⟩
    · intro sp hsp
      simp only [List.mem_cons] at hsp
      rcases hsp with rfl | m
      · simp; omega
      · have := ih.1 sp m; simp; omega
    · have := ih.2; simp; omega

theorem specs_head {E : Env} {names : List Word} {attrs : Word} {specs : List (Word × Word)} {k : Nat}
    (h : Specs E names attrs specs k) : attrs = [] ∨ ∃ c t, attrs = c :: t ∧ IsSpace c := by
  cases h with
  | nil => left; rfl
  | @cons s n e v value rest p l specs k1 k2 hs _ _ _ _ =>
    right
    obtain ⟨hne, hall⟩ := hs
    obtain ⟨c, t, ht⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨c, t ++ n ++ e ++ v ++ rest, by rw [ht]; simp, hall c (by rw [ht]; simp)⟩

theorem forall2_left {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ a ∈ l1, ∃ b, R a b
  | [], [], _, a, h => by simp at h
  | _ :: _, b :: _, .cons hr hrest, a, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | m
    · exact ⟨b, hr⟩
    · exact forall2_left hrest a m

theorem elementName_qname {scope : Scope} {n : Word} {pre ns : Option Word} {l : Word}
    (h : ElementName scope n pre ns l) : QName n pre l := by
  cases h with
  | unprefixed ncn => exact QName.unprefixed ncn
  | prefixed hp hl _ _ => exact QName.prefixed hp hl

theorem start_tag_complete {E : Env} {names : List Word} {scope : Scope} {n attrs s tail : Word}
    {p : Option Word} {l : Word} {specs : List (Word × Word)} {k1 : Nat} {e : xml.Element}
    (hq : QName n p l) (hspecs : Specs E names attrs specs k1) (hs : OptS s) (htag : StartTag scope n specs e)
    (htail : tail = [62] ∨ tail = [47, 62])
    (cs : alloc.vec.Vec U32) (i : Usize) (env : alloc.vec.Vec xml.Entity) (stack : alloc.vec.Vec Usize)
    (ctx : alloc.vec.Vec xml.Binding) (budget : Usize) (more : Word)
    (hE : E = envView env) (henv : EnvOk env) (hstack : StackOk env stack names) (nz : NoZero cs)
    (hscope : scope = scopeView ctx)
    (split : (word cs).drop i.val = 60 :: n ++ attrs ++ s ++ tail ++ more)
    (kb : k1 ≤ budget.val) (room : ctx.val.length + attrs.length + k1 ≤ Usize.max) :
    ∃ name_end mark after raws decls ctx' b1,
      xml.element cs i env stack ctx budget =
        xml.element_in cs i name_end mark after (decide (tail = [47, 62])) env stack ctx' raws decls b1 ∧
      after.val = i.val + 1 + n.length + attrs.length + s.length + tail.length ∧
      (word cs).drop (i.val + 1) = n ++ (word cs).drop name_end.val ∧ name_end.val = i.val + 1 + n.length ∧
      mark.val = markOf (i.val + 1) n p ∧ List.Forall₂ (RawOk cs) raws.val specs ∧
      decls = e.declarations ∧ scopeView ctx' = scope ++ declarations specs ∧
      ctx'.val.length ≤ ctx.val.length + attrs.length ∧ b1.val + k1 = budget.val := by
  have lt : charAt cs i.val = 60 := first_char (rest := n ++ attrs ++ s ++ tail ++ more) (by rw [split]; simp)
  have inside : i.val < cs.val.length := charAt_inside (by rw [lt]; decide)
  obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
  have d1 : (word cs).drop i1.val = n ++ (attrs ++ s ++ tail ++ more) := by
    rw [hi1v]
    have := drop_after (cs := cs) (i := i.val) (w := [60]) (rest := n ++ (attrs ++ s ++ tail ++ more))
      (by rw [split]; simp)
    simpa using this
  have nrun : nameRun cs i1.val = n := by
    apply nameRun_eq d1 (name_all (qname_name hq))
    intro c m em
    rcases specs_head hspecs with ha | ⟨c', t', ha, hc'⟩
    · subst ha
      cases s with
      | nil =>
        rcases htail with rfl | rfl <;> simp at em <;> rw [em.1] <;> simp [NameChar, NameStartChar]
      | cons c0 s' => simp at em; rw [← em.1]; exact space_not_name (hs c0 (by simp))
    · rw [ha] at em; simp at em; rw [← em.1]; exact space_not_name hc'
  obtain ⟨r1, h1, sound1, complete1⟩ := qname_spec cs i1
  rw [nrun] at sound1 complete1
  obtain ⟨name_end, mark, hr1⟩ := complete1 p l hq
  subst hr1
  obtain ⟨hne, p', l', hq', hmark⟩ := sound1 name_end mark rfl
  obtain ⟨rfl, rfl⟩ := qname_unique hq' hq
  have dname : (word cs).drop name_end.val = attrs ++ (s ++ tail ++ more) := by
    rw [hne]; have := drop_after d1; simpa using this
  obtain ⟨vals, nspecs⟩ := specs_bound hspecs
  obtain ⟨raws, j, b1, h2, hj, hb1, new, hraws, hall⟩ := attributes_complete hspecs cs name_end env stack budget
    (alloc.vec.Vec.new _) (s ++ tail ++ more) hE henv hstack nz dname
    (by rcases htail with rfl | rfl
        · exact ⟨s, 62, more, by simp, hs, Or.inl rfl⟩
        · exact ⟨s, 47, 62 :: more, by simp, hs, Or.inr rfl⟩)
    kb (fun sp hsp => by have := vals sp hsp; omega) (by simp; omega)
  have hraws' : List.Forall₂ (RawOk cs) raws.val specs := by rw [hraws]; simpa using hall
  have dj : (word cs).drop j.val = s ++ (tail ++ more) := by rw [hj]; simpa using drop_after dname
  obtain ⟨j2, hj2, hj2v⟩ := skip_spaces_eq cs j
  have rs : run IsSpace ((word cs).drop j.val) = s := by
    apply run_spaces_eq dj hs
    intro c m em
    rcases htail with rfl | rfl <;> simp at em <;> rw [em.1] <;> simp [IsSpace]
  rw [rs] at hj2v
  have tj2 : (word cs).drop j2.val = tail ++ more := by rw [hj2v]; exact drop_after dj
  obtain ⟨r3, h3, c3⟩ := tag_end_spec cs j2
  have tagOk : ∃ after, r3 = .Ok (decide (tail = [47, 62]), after) ∧ after.val = j2.val + tail.length := by
    cases r3 with
    | Err err =>
      exfalso; apply c3
      rcases htail with rfl | rfl
      · exact Or.inl (first_char (by simpa using tj2))
      · exact Or.inr (two_chars (by simpa using tj2))
    | Ok ea =>
      obtain ⟨empty, after⟩ := ea
      rcases htail with rfl | rfl
      · rcases c3 with ⟨he, _, ha⟩ | ⟨_, sl, _, _⟩
        · exact ⟨after, by simp [he], by simpa using ha⟩
        · have := first_char (by simpa using tj2 : (word cs).drop j2.val = 62 :: more); omega
      · rcases c3 with ⟨_, gt, _⟩ | ⟨he, _, _, ha⟩
        · have := first_char (by simpa using tj2 : (word cs).drop j2.val = 47 :: 62 :: more); omega
        · exact ⟨after, by simp [he], by simpa using ha⟩
  obtain ⟨after, hr3, hafter⟩ := tagOk
  subst hr3
  obtain ⟨r4, h4, c4⟩ := unique_names_spec cs raws 0#usize hraws'
  have u4 : r4 = .Ok () := c4.mpr (by
    intro a b ha hb _ lt'; exact (nodup_names.mp htag.unique) a b ha hb (by omega) lt')
  subst u4
  obtain ⟨r5, h5, c5⟩ := declarations_spec cs raws hraws' 0#usize (alloc.vec.Vec.new _)
    (by simp)
  have z0 : (0#usize : Usize).val = 0 := rfl
  cases r5 with
  | Err err => exfalso; apply c5; rw [z0, List.drop_zero]; exact htag.allowed
  | Ok decls =>
    obtain ⟨_, hdecls⟩ := c5
    rw [z0, List.drop_zero] at hdecls
    have hdecls' : decls.val.map bindingView = declarations specs := by simpa using hdecls
    have deq : decls = e.declarations := by
      apply alloc.vec.Vec.ext
      exact map_inj_of (fun _ _ => bindingView_inj) (hdecls'.trans htag.declared.symm)
    have dlen : decls.val.length ≤ attrs.length := by
      have := congrArg List.length hdecls'
      simp only [List.length_map] at this
      have := List.length_filterMap_le declaration specs
      simp only [declarations] at *
      omega
    by_cases dz : decls.val.length = 0
    · have dzero : alloc.vec.Vec.len decls = 0#usize :=
        UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len_val, dz])
      have dnil : declarations specs = [] := by rw [← hdecls', List.length_eq_zero_iff.mp dz]; simp
      refine ⟨name_end, mark, after, raws, decls, ctx, b1, ?_, by omega, by rw [← hi1v, hne, drop_after d1]; exact d1,
        by omega, by rw [hmark, hi1v], hraws', deq, by rw [dnil, hscope]; simp, by omega, hb1⟩
      unfold xml.element
      simp [hi1, h1, h2, hj2, h3, h4, h5, dzero, core.result.Result.Insts.CoreOpsTry.branch]
    · have dzero : ¬ alloc.vec.Vec.len decls = 0#usize := by
        intro h; apply dz; have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len_val] using this
      obtain ⟨inner, h6, hinner⟩ := extend_spec ctx decls (by omega)
      refine ⟨name_end, mark, after, raws, decls, inner, b1, ?_, by omega,
        by rw [← hi1v, hne, drop_after d1]; exact d1, by omega, by rw [hmark, hi1v], hraws', deq,
        by rw [hscope]; simp [scopeView, hinner, ← hdecls'], by rw [hinner]; simp; omega, hb1⟩
      unfold xml.element
      simp [hi1, h1, h2, hj2, h3, h4, h5, dzero, h6, core.result.Result.Insts.CoreOpsTry.branch]

/-! ## Elements -/

theorem element_in_head (cs : alloc.vec.Vec U32) (i name_end mark : Usize) (ctx : alloc.vec.Vec xml.Binding)
    (raws : alloc.vec.Vec xml.Raw) {scope : Scope} {n : Word} {p : Option Word} {l : Word}
    {specs : List (Word × Word)} {e : xml.Element}
    (lt : charAt cs i.val = 60)
    (nsplit : (word cs).drop (i.val + 1) = n ++ (word cs).drop name_end.val)
    (hne : name_end.val = i.val + 1 + n.length)
    (hq : QName n p l) (hmark : mark.val = markOf (i.val + 1) n p)
    (hraws : List.Forall₂ (RawOk cs) raws.val specs)
    (htag : StartTag scope n specs e) (hscope : scopeView ctx = scope ++ declarations specs) :
    ∃ i1 ls, (i + 1#usize : Result Usize) = .ok i1 ∧ i1.val = i.val + 1 ∧
      xml.element_namespace cs i1 mark name_end ctx = .ok (.Ok (e.ns_prefix, e.ns_name)) ∧
      xml.local_start i1 mark name_end = .ok ls ∧ xml.copy_span cs ls name_end = .ok (.Ok e.local_name) ∧
      xml.resolve_attributes cs raws 0#usize ctx (alloc.vec.Vec.new _) = .ok (.Ok e.attributes) ∧
      xml.unique_expanded e.attributes 0#usize i = .ok (.Ok ()) := by
  have inside : i.val < cs.val.length := charAt_inside (by rw [lt]; decide)
  obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
  have nsplit' : (word cs).drop i1.val = n ++ (word cs).drop name_end.val := by rw [hi1v]; exact nsplit
  have hne' : name_end.val = i1.val + n.length := by omega
  have hmark' : mark.val = markOf i1.val n p := by rw [hmark, hi1v]
  have named := htag.named
  rw [← hscope] at named
  have qn := qname_unique (elementName_qname named) hq
  have named' : ElementName (scopeView ctx) n (optWord e.ns_prefix) (optWord e.ns_name) l := by
    rw [← qn.2]; exact named
  obtain ⟨r1, h1, s1, c1⟩ := element_namespace_spec cs i1 mark name_end nsplit' hne' hq hmark' ctx
  obtain ⟨v1, hv1⟩ := c1 ⟨_, _, named'⟩
  subst hv1
  obtain ⟨pre, ns⟩ := v1
  obtain ⟨e1, e2, _⟩ := elementName_unique_of (s1 pre ns rfl) named' rfl
  rw [optWord_inj e1, optWord_inj e2] at h1
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
  rw [← qn.2] at hlw
  rw [word_inj hlw] at hlv
  have atts : List.Forall₂ (AttOk (scopeView ctx)) (plain specs) e.attributes.val := by
    rw [hscope]; exact htag.attributes
  obtain ⟨r2, h2, s2, c2⟩ := resolve_attributes_spec cs raws hraws 0#usize ctx (alloc.vec.Vec.new _) (by simp)
  have z0 : (0#usize : Usize).val = 0 := rfl
  rw [z0, List.drop_zero] at s2 c2
  obtain ⟨v2, hv2⟩ := c2 (fun sp hsp => by
    obtain ⟨a, ha, _⟩ := forall2_left atts sp hsp
    exact ⟨_, _, _, ha⟩)
  subst hv2
  obtain ⟨new, hnew, hall⟩ := s2 v2 rfl
  have ve : v2 = e.attributes := by
    apply alloc.vec.Vec.ext
    rw [hnew]; simpa using attOk_unique hall atts
  rw [ve] at h2
  obtain ⟨r3, h3, c3⟩ := unique_expanded_spec e.attributes 0#usize i
  have u3 : r3 = .Ok () := c3.mpr (by
    intro a b ha hb _ lt'; exact (nodup_expanded.mp htag.distinct) a b ha hb (by omega) lt')
  subst u3
  exact ⟨i1, ls, hi1, hi1v, h1, hls, hlv, h2, h3⟩

theorem element_empty_goal {E : Env} {names : List Word} {scope : Scope} {n attrs s : Word} {p : Option Word}
    {l : Word} {specs : List (Word × Word)} {k : Nat} {e : xml.Element}
    (hq : QName n p l) (hspecs : Specs E names attrs specs k) (hs : OptS s) (htag : StartTag scope n specs e)
    (hch : e.children.val = []) :
    ElementGoal E names scope (60 :: n ++ attrs ++ s ++ lit "/>") e k := by
  intro cs i env stack ctx budget rest hE henv hstack nz hscope split kb room
  have lslash : lit "/>" = [47, 62] := by decide
  obtain ⟨name_end, mark, after, raws, decls, ctx', b1, eq, hafter, nsplit, hne, hmark, hraws, hdecls, hscope',
    _, hb1⟩ := start_tag_complete hq hspecs hs htag (Or.inr rfl) cs i env stack ctx budget rest hE henv hstack nz
      hscope (by rw [split, lslash]) kb (by simp at room ⊢; omega)
  have lt : charAt cs i.val = 60 := first_char (rest := n ++ attrs ++ s ++ lit "/>" ++ rest) (by rw [split]; simp)
  obtain ⟨i1, ls, hi1, hi1v, h1, h2, h3, h4, h5⟩ :=
    element_in_head cs i name_end mark ctx' raws lt nsplit hne hq hmark hraws htag hscope'
  refine ⟨after, b1, ?_, by rw [hafter, lslash]; simp; omega, hb1⟩
  rw [eq]
  unfold xml.element_in
  simp only [hi1, h1, h2, h3, h4, h5, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  have ee : xml.Element.mk e.ns_prefix e.ns_name e.local_name e.attributes decls (alloc.vec.Vec.new _) = e :=
    element_eq rfl rfl rfl rfl (by rw [hdecls]) (by simp [hch])
  simp [ee]

/-- Spaces before `>` are read alike. -/
theorem spaces_before_gt {a b x y : Word} (ha : OptS a) (hb : OptS b) (h : a ++ 62 :: x = b ++ 62 :: y) :
    a = b := by
  have r1 : run IsSpace (a ++ 62 :: x) = a :=
    run_unique ha (fun c m e => by simp at e; rw [e.1]; simp [IsSpace])
  have r2 : run IsSpace (b ++ 62 :: y) = b :=
    run_unique hb (fun c m e => by simp at e; rw [e.1]; simp [IsSpace])
  rw [← r1, ← r2, h]

theorem element_full_goal {E : Env} {names : List Word} {scope : Scope} {n attrs s body s2 : Word}
    {p : Option Word} {l : Word} {specs : List (Word × Word)} {k1 k2 : Nat} {items : List Item} {e : xml.Element}
    (hq : QName n p l) (hspecs : Specs E names attrs specs k1) (hs : OptS s) (htag : StartTag scope n specs e)
    (hc : ContentGoal E names (scope ++ declarations specs) body items k2) (hs2 : OptS s2)
    (hch : e.children.val.map nodeView = runs items) :
    ElementGoal E names scope (60 :: n ++ attrs ++ s ++ [62] ++ body ++ lit "</" ++ n ++ s2 ++ [62]) e
      (k1 + k2) := by
  intro cs i env stack ctx budget rest hE henv hstack nz hscope split kb room
  have lend : lit "</" = [60, 47] := by decide
  simp only [List.length_append, List.length_cons] at room
  obtain ⟨name_end, mark, after, raws, decls, ctx', b1, eq, hafter, nsplit, hne, hmark, hraws, hdecls, hscope',
    hctx', hb1⟩ := start_tag_complete hq hspecs hs htag (Or.inl rfl) cs i env stack ctx budget
      (body ++ lit "</" ++ n ++ s2 ++ [62] ++ rest) hE henv hstack nz hscope (by rw [split]; simp) (by omega)
      (by omega)
  have lt : charAt cs i.val = 60 := first_char (rest := n ++ attrs ++ s ++ [62] ++ body ++ lit "</" ++ n ++ s2 ++
    [62] ++ rest) (by rw [split]; simp)
  obtain ⟨i1, ls, hi1, hi1v, h1, h2, h3, h4, h5⟩ :=
    element_in_head cs i name_end mark ctx' raws lt nsplit hne hq hmark hraws htag hscope'
  have dafter : (word cs).drop after.val = body ++ (lit "</" ++ n ++ s2 ++ [62] ++ rest) := by
    have := drop_after (cs := cs) (i := i.val) (w := 60 :: n ++ attrs ++ s ++ [62])
      (rest := body ++ (lit "</" ++ n ++ s2 ++ [62] ++ rest)) (by rw [split]; simp)
    have ea : after.val = i.val + (60 :: n ++ attrs ++ s ++ [62]).length := by rw [hafter]; simp; omega
    rw [ea]; exact this
  obtain ⟨nodes, text, stop, b2, h6, hstop, hb2, rel, size⟩ := hc cs after env stack ctx' b1
    (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) (lit "</" ++ n ++ s2 ++ [62] ++ rest) hE henv hstack nz hscope'.symm
    dafter (Or.inr ⟨n ++ s2 ++ [62] ++ rest, by rw [lend]; simp⟩) (by omega) (by simp; omega)
  simp only [alloc.vec.Vec.new, List.length_nil] at size
  obtain ⟨children, h7, hch7, _⟩ := flush_eq nodes text stop (by simp at size; omega)
  have chEq : children.val.map nodeView = e.children.val.map nodeView := by rw [children_of rel hch7, hch]
  have dstop : (word cs).drop stop.val = lit "</" ++ n ++ s2 ++ [62] ++ rest := by
    rw [hstop]; have := drop_after dafter; simpa using this
  have nsplit' : (word cs).drop i1.val = n ++ (word cs).drop name_end.val := by rw [hi1v]; exact nsplit
  obtain ⟨r8, h8, s8, c8⟩ := end_tag_spec cs stop i1 name_end nsplit' (by omega)
  obtain ⟨fin, hfin⟩ := c8 s2 rest dstop hs2
  subst hfin
  obtain ⟨s2', esplit, hs2', hfinv⟩ := s8 fin rfl
  have s2e : s2' = s2 := by
    have e1 := esplit.symm.trans dstop
    simp only [List.append_assoc, List.append_cancel_left_eq, List.singleton_append] at e1
    exact spaces_before_gt hs2' hs2 e1
  subst s2e
  refine ⟨fin, b2, ?_, ?_, by omega⟩
  · rw [eq]
    unfold xml.element_in
    have ee : xml.Element.mk e.ns_prefix e.ns_name e.local_name e.attributes decls children = e :=
      element_eq rfl rfl rfl rfl (by rw [hdecls]) chEq
    have : decide ([62] = [47, 62]) = false := by decide
    simp [hi1, h1, h2, h3, h4, h5, h6, h7, h8, core.result.Result.Insts.CoreOpsTry.branch, this, ee]
  · rw [hfinv, hstop, hafter]; simp [lend]; omega

theorem element_name_start {E : Env} {names : List Word} {scope : Scope} {w : Word} {e : xml.Element} {k : Nat}
    (h : Element E names scope w e k) : ∃ c rest, w = 60 :: c :: rest ∧ NameStartChar c := by
  cases h with
  | empty hq _ _ _ _ =>
    obtain ⟨c, r, rfl, hc, _⟩ := qname_name hq
    exact ⟨c, _, rfl, hc⟩
  | full hq _ _ _ _ _ _ =>
    obtain ⟨c, r, rfl, hc, _⟩ := qname_name hq
    exact ⟨c, _, rfl, hc⟩

/-! ## Completeness -/

mutual

theorem element_complete {E : Env} : ∀ {names : List Word} {scope : Scope} {w : Word} {e : xml.Element} {k : Nat},
    Element E names scope w e k → ElementGoal E names scope w e k
  | _, _, _, _, _, .empty hq hspecs hs htag hch => element_empty_goal hq hspecs hs htag hch
  | _, _, _, _, _, .full hq hspecs hs htag hc hs2 hch =>
    element_full_goal hq hspecs hs htag (content_complete hc) hs2 hch

theorem content_complete {E : Env} :
    ∀ {names : List Word} {scope : Scope} {w : Word} {items : List Item} {k : Nat},
    Content E names scope w items k → ContentGoal E names scope w items k
  | _, _, _, _, _, .nil => content_nil_goal
  | _, _, _, _, _, .last hne hcd => content_last_goal hne hcd
  | _, _, _, _, _, .data hne hcd hm hr =>
    content_data_goal hne hcd (markup_head hm) (markup_complete hm) (content_complete hr)
  | _, _, _, _, _, .markup hm hr => content_markup_goal (markup_complete hm) (content_complete hr)

theorem markup_complete {E : Env} : ∀ {names : List Word} {scope : Scope} {w : Word} {x : List Item} {k : Nat},
    Markup E names scope w x k → MarkupGoal E names scope w x k
  | _, _, _, _, _, .element he => markup_element_goal (element_name_start he) (element_complete he)
  | _, _, _, _, _, .charRef hr hx => markup_charRef_goal hr hx
  | _, _, _, _, _, .predefined hr hp => markup_predefined_goal hr hp
  | _, _, _, _, _, .entity hr hp hl hn hc => markup_entity_goal hr hp hl hn (content_complete hc)
  | _, _, _, _, _, .cdata hc => markup_cdata_goal hc
  | _, _, _, _, _, .pi hp => markup_pi_goal hp
  | _, _, _, _, _, .comment hc => markup_comment_goal hc

end

end Rowl.XmlComplete
