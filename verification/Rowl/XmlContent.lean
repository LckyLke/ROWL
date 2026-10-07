import Rowl.XmlNamespaces

/-!
# Content and elements: dispatch, tags and children

What `content_rule` dispatches on, the ends of start tags and end tags, and
how the children read so far (`nodes` and the pending characters `text`)
stand for the items of the grammar's content.
-/

namespace Rowl.XmlContent
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs Rowl.XmlEntities Rowl.XmlAttributes Rowl.XmlTags Rowl.XmlNamespaces
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

theorem atU_eq_iff (cs : alloc.vec.Vec U32) (i : Nat) (c : U32) : atU cs i = c ↔ charAt cs i = c.val := by
  constructor
  · intro h; rw [← atU_val, h]
  · intro h; exact atU_eq h

theorem map_comment_bytes : ([60#u8, 33#u8, 45#u8, 45#u8] : List U8).map (·.val) = lit "<!--" := by decide
theorem map_cdata_bytes :
    ([60#u8, 33#u8, 91#u8, 67#u8, 68#u8, 65#u8, 84#u8, 65#u8, 91#u8] : List U8).map (·.val) = lit "<![CDATA[" := by
  decide
theorem map_end_bytes : ([60#u8, 47#u8] : List U8).map (·.val) = lit "</" := by decide

/-! ## What content begins with -/

/-- What begins at a position in content. -/
def ruleOf (cs : alloc.vec.Vec U32) (i : Nat) : xml.Rule :=
  if charAt cs i = 0 then .End
  else if charAt cs i = 60 then
    if charAt cs (i + 1) = 47 then .Stop
    else if charAt cs (i + 1) = 33 then
      (if lit "<!--" <+: (word cs).drop i then .Comment
       else if lit "<![CDATA[" <+: (word cs).drop i then .CData else .Invalid)
    else if charAt cs (i + 1) = 63 then .Pi else .Element
  else if charAt cs i = 38 then .Reference else .Chars

theorem content_rule_eq (cs : alloc.vec.Vec U32) (i : Usize) : xml.content_rule cs i = .ok (ruleOf cs i.val) := by
  unfold xml.content_rule ruleOf
  simp only [at_eq, bind_ok, atU_eq_iff]
  by_cases z : charAt cs i.val = 0
  · simp [z]
  · have z' : ¬ charAt cs i.val = (0#u32 : U32).val := by simpa using z
    rw [if_neg z', if_neg z]
    by_cases lt : charAt cs i.val = 60
    · have lt' : charAt cs i.val = (60#u32 : U32).val := by simpa using lt
      rw [if_pos lt', if_pos lt]
      obtain ⟨inside, _⟩ := drop_nonzero z
      obtain ⟨i1, hi1, hi1v⟩ := next_spec inside
      unfold xml.markup_rule
      simp only [hi1, at_eq, bind_ok, atU_eq_iff, hi1v]
      by_cases sl : charAt cs (i.val + 1) = 47
      · simp [sl]
      · by_cases bang : charAt cs (i.val + 1) = 33
        · simp only [sl, bang]
          unfold xml.bang_rule
          simp [lift, starts_eq, bytes_make, lit_comment, lit_cdata]
          split_ifs <;> rfl
        · by_cases q : charAt cs (i.val + 1) = 63
          · simp [sl, bang, q]
          · simp [sl, bang, q]
    · have lt' : ¬ charAt cs i.val = (60#u32 : U32).val := by simpa using lt
      rw [if_neg lt', if_neg lt]
      by_cases amp : charAt cs i.val = 38
      · simp [amp]
      · simp [amp]

theorem ruleOf_end {cs : alloc.vec.Vec U32} {i : Nat} (h : ruleOf cs i = .End) : charAt cs i = 0 := by
  revert h; unfold ruleOf; split_ifs <;> simp_all

theorem ruleOf_stop {cs : alloc.vec.Vec U32} {i : Nat} (h : ruleOf cs i = .Stop) :
    charAt cs i = 60 ∧ charAt cs (i + 1) = 47 := by
  revert h; unfold ruleOf; split_ifs <;> simp_all

theorem ruleOf_chars {cs : alloc.vec.Vec U32} {i : Nat} (h : ruleOf cs i = .Chars) : DataChar (charAt cs i) := by
  revert h; unfold ruleOf; split_ifs <;> simp_all [DataChar]

theorem ruleOf_comment {cs : alloc.vec.Vec U32} {i : Nat} (h : ruleOf cs i = .Comment) :
    lit "<!--" <+: (word cs).drop i := by
  revert h; unfold ruleOf; split_ifs <;> simp_all

theorem ruleOf_cdata {cs : alloc.vec.Vec U32} {i : Nat} (h : ruleOf cs i = .CData) :
    lit "<![CDATA[" <+: (word cs).drop i := by
  revert h; unfold ruleOf; split_ifs <;> simp_all

theorem ruleOf_pi {cs : alloc.vec.Vec U32} {i : Nat} (h : ruleOf cs i = .Pi) :
    charAt cs i = 60 ∧ charAt cs (i + 1) = 63 := by
  revert h; unfold ruleOf; split_ifs <;> simp_all

theorem ruleOf_reference {cs : alloc.vec.Vec U32} {i : Nat} (h : ruleOf cs i = .Reference) :
    charAt cs i = 38 := by
  revert h; unfold ruleOf; split_ifs <;> simp_all

theorem ruleOf_element {cs : alloc.vec.Vec U32} {i : Nat} (h : ruleOf cs i = .Element) :
    charAt cs i = 60 ∧ charAt cs (i + 1) ≠ 47 ∧ charAt cs (i + 1) ≠ 33 ∧ charAt cs (i + 1) ≠ 63 := by
  revert h; unfold ruleOf; split_ifs <;> simp_all

/-- Two code points from a position. -/
theorem two_chars {cs : alloc.vec.Vec U32} {i : Nat} {a b : Nat} {rest : Word}
    (split : (word cs).drop i = a :: b :: rest) : charAt cs i = a ∧ charAt cs (i + 1) = b := by
  constructor
  · exact first_char split
  · have := charAt_of_drop (w := [a, b]) (rest := rest) (by rw [split]; simp) (t := 1) (by simp)
    simpa using this

theorem pi_start {cs : alloc.vec.Vec U32} {i : Nat} (h : charAt cs i = 60 ∧ charAt cs (i + 1) = 63) :
    lit "<?" <+: (word cs).drop i := by
  obtain ⟨a, b⟩ := h
  have inside : i < cs.val.length := charAt_inside (by rw [a]; decide)
  have inside1 : i + 1 < cs.val.length := charAt_inside (by rw [b]; decide)
  rw [drop_charAt inside, drop_charAt inside1, a, b, lit_pi]
  exact ⟨_, rfl⟩

/-! ## Children -/

theorem push_node_eq (nodes : alloc.vec.Vec xml.Node) (node : xml.Node) (offset : Usize)
    (h : nodes.val.length < Usize.max) :
    ∃ v, xml.push_node nodes node offset = .ok (.Ok v) ∧ v.val = nodes.val ++ [node] := by
  obtain ⟨v, hv, hvv⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec nodes node h)
  exact ⟨v, by simp [xml.push_node, alloc.vec.Vec.len_val, core.num.Usize.MAX, h, hv], hvv⟩

theorem push_node_sound (nodes : alloc.vec.Vec xml.Node) (node : xml.Node) (offset : Usize) :
    ∃ r, xml.push_node nodes node offset = .ok r ∧ ∀ v, r = .Ok v → v.val = nodes.val ++ [node] := by
  by_cases h : nodes.val.length < Usize.max
  · obtain ⟨v, hv, hvv⟩ := push_node_eq nodes node offset h
    exact ⟨_, hv, fun v' e => by simp at e; subst e; exact hvv⟩
  · exact ⟨.Err ⟨.ResourceLimit, offset⟩, by simp [xml.push_node, alloc.vec.Vec.len_val, core.num.Usize.MAX, h,
      xml.fail], by simp⟩

/-- What a buffer of pending characters adds to the children: nothing when
    it is empty, a text node otherwise. -/
def textPart (t : Word) : List (Word ⊕ xml.Element) := if t = [] then [] else [.inl t]

theorem flush_sound (nodes : alloc.vec.Vec xml.Node) (text : alloc.vec.Vec U32) (offset : Usize) :
    ∃ r, xml.flush nodes text offset = .ok r ∧
      ∀ v, r = .Ok v → v.val.map nodeView = nodes.val.map nodeView ++ textPart (word text) := by
  unfold xml.flush
  by_cases e : text.val.length = 0
  · have le : alloc.vec.Vec.len text = 0#usize := UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len_val, e])
    have ew : word text = [] := by rw [← List.length_eq_zero_iff, word_length]; exact e
    refine ⟨.Ok nodes, by simp [le], ?_⟩
    intro v h; simp at h; subst h; simp [textPart, ew]
  · have le : ¬ alloc.vec.Vec.len text = 0#usize := by
      intro h; apply e; have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len_val] using this
    have ew : word text ≠ [] := by rw [ne_eq, ← List.length_eq_zero_iff, word_length]; exact e
    obtain ⟨r, hr, hv⟩ := push_node_sound nodes (.Text text) offset
    refine ⟨r, by simp [le, hr], ?_⟩
    intro v h; rw [hv v h]; simp [textPart, ew, nodeView]

theorem flush_eq (nodes : alloc.vec.Vec xml.Node) (text : alloc.vec.Vec U32) (offset : Usize)
    (room : nodes.val.length < Usize.max) :
    ∃ v, xml.flush nodes text offset = .ok (.Ok v) ∧
      v.val.map nodeView = nodes.val.map nodeView ++ textPart (word text) ∧
      v.val.length ≤ nodes.val.length + 1 := by
  unfold xml.flush
  by_cases e : text.val.length = 0
  · have le : alloc.vec.Vec.len text = 0#usize := UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len_val, e])
    have ew : word text = [] := by rw [← List.length_eq_zero_iff, word_length]; exact e
    exact ⟨nodes, by simp [le], by simp [textPart, ew], by omega⟩
  · have le : ¬ alloc.vec.Vec.len text = 0#usize := by
      intro h; apply e; have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len_val] using this
    have ew : word text ≠ [] := by rw [ne_eq, ← List.length_eq_zero_iff, word_length]; exact e
    obtain ⟨v, hv, hvv⟩ := push_node_eq nodes (.Text text) offset room
    exact ⟨v, by simp [le, hv], by rw [hvv]; simp [textPart, ew, nodeView], by rw [hvv]; simp⟩

/-! ## Items and runs -/

/-- The items of characters. -/
def chars (t : Word) : List Item := t.map Item.char

/-- Items ending with an element, or none. -/
def Closed (xs : List Item) : Prop := ∀ c, xs.getLast? ≠ some (Item.char c)

/-- Children standing for the items `xs`. -/
def NodesOk (nodes : alloc.vec.Vec xml.Node) (xs : List Item) : Prop :=
  nodes.val.map nodeView = runs xs ∧ Closed xs

/-- Reading from the state `nodes`, `text` to `nodes'`, `text'` adds the items `items`. -/
def Rel (nodes : alloc.vec.Vec xml.Node) (text : alloc.vec.Vec U32) (nodes' : alloc.vec.Vec xml.Node)
    (text' : alloc.vec.Vec U32) (items : List Item) : Prop :=
  ∀ xs, NodesOk nodes xs → ∃ xs', NodesOk nodes' xs' ∧ xs' ++ chars (word text') = xs ++ chars (word text) ++ items

/-- A character joins the first run, when it is one. -/
def merge (c : Nat) : List (Word ⊕ xml.Element) → List (Word ⊕ xml.Element)
  | .inl t :: more => .inl (c :: t) :: more
  | more => .inl [c] :: more

theorem runs_char (c : Nat) (xs : List Item) : runs (.char c :: xs) = merge c (runs xs) := by
  simp only [runs]
  rcases runs xs with _ | ⟨a, more⟩
  · rfl
  · cases a <;> rfl

theorem runs_ne_nil {xs : List Item} (h : xs ≠ []) : runs xs ≠ [] := by
  cases xs with
  | nil => exact absurd rfl h
  | cons x rest =>
    cases x with
    | elem e => simp [runs]
    | char c =>
      rw [runs_char]
      unfold merge
      split <;> simp

/-- Merging a character into runs looks only at the first run. -/
theorem merge_append (c : Nat) (L M : List (Word ⊕ xml.Element)) (h : L ≠ []) :
    merge c (L ++ M) = merge c L ++ M := by
  cases L with
  | nil => exact absurd rfl h
  | cons a L' => cases a <;> rfl

theorem closed_tail {x : Item} {xs : List Item} (h : Closed (x :: xs)) (ne : xs ≠ []) : Closed xs := by
  intro c e
  apply h c
  have : (x :: xs).getLast? = xs.getLast? := by
    cases xs with
    | nil => exact absurd rfl ne
    | cons y ys => simp [List.getLast?_cons_cons]
  rw [this]; exact e

theorem runs_append_closed (xs ys : List Item) (h : Closed xs) : runs (xs ++ ys) = runs xs ++ runs ys := by
  induction xs with
  | nil => simp [runs]
  | cons x rest ih =>
    cases x with
    | elem e =>
      by_cases ne : rest = []
      · subst ne; simp [runs]
      · simp only [List.cons_append, runs]
        rw [ih (closed_tail h ne)]
    | char c =>
      have ne : rest ≠ [] := by
        intro e; subst e; exact h c (by simp)
      simp only [List.cons_append]
      rw [runs_char, runs_char, ih (closed_tail h ne)]
      exact merge_append c _ _ (runs_ne_nil ne)

theorem runs_chars_append (t : Word) (ys : List Item) (h : ∀ c, ys.head? ≠ some (Item.char c)) :
    runs (chars t ++ ys) = textPart t ++ runs ys := by
  induction t with
  | nil => simp [chars, textPart]
  | cons c t ih =>
    simp only [chars, List.map_cons, List.cons_append]
    rw [runs_char]
    have ih' : runs (List.map Item.char t ++ ys) = textPart t ++ runs ys := ih
    rw [ih']
    by_cases e : t = []
    · subst e
      simp only [textPart, ite_true, List.nil_append]
      cases ys with
      | nil => simp [runs, merge]
      | cons y more =>
        cases y with
        | char d => exact absurd (by simp) (h d)
        | elem e => simp [runs, textPart, merge]
    · simp [textPart, e, merge]

theorem runs_chars (t : Word) : runs (chars t) = textPart t := by
  have := runs_chars_append t [] (by simp)
  simpa [runs] using this

theorem closed_nil : Closed [] := by intro c; simp

theorem closed_elem (xs : List Item) (e : xml.Element) : Closed (xs ++ [.elem e]) := by
  intro c; simp

theorem nodesOk_new : NodesOk (alloc.vec.Vec.new xml.Node) [] := ⟨by simp [runs], closed_nil⟩

theorem rel_refl (nodes : alloc.vec.Vec xml.Node) (text : alloc.vec.Vec U32) : Rel nodes text nodes text [] := by
  intro xs h; exact ⟨xs, h, by simp⟩

theorem rel_trans {n0 n1 n2 : alloc.vec.Vec xml.Node} {t0 t1 t2 : alloc.vec.Vec U32} {i1 i2 : List Item}
    (h1 : Rel n0 t0 n1 t1 i1) (h2 : Rel n1 t1 n2 t2 i2) : Rel n0 t0 n2 t2 (i1 ++ i2) := by
  intro xs h
  obtain ⟨xs1, h1', e1⟩ := h1 xs h
  obtain ⟨xs2, h2', e2⟩ := h2 xs1 h1'
  refine ⟨xs2, h2', ?_⟩
  rw [e2, e1]; simp

/-- Pending characters grow by a word. -/
theorem rel_chars (nodes : alloc.vec.Vec xml.Node) (text text' : alloc.vec.Vec U32) {w : Word}
    (h : word text' = word text ++ w) : Rel nodes text nodes text' (chars w) := by
  intro xs hx; exact ⟨xs, hx, by rw [h]; simp [chars]⟩

/-- An element closes the pending characters into a text node. -/
theorem rel_element {nodes nodes1 nodes2 : alloc.vec.Vec xml.Node} (text : alloc.vec.Vec U32) (e : xml.Element)
    (h1 : nodes1.val.map nodeView = nodes.val.map nodeView ++ textPart (word text))
    (h2 : nodes2.val = nodes1.val ++ [.Element e]) :
    Rel nodes text nodes2 (alloc.vec.Vec.new U32) [.elem e] := by
  intro xs ⟨hx, cx⟩
  refine ⟨xs ++ chars (word text) ++ [.elem e], ⟨?_, closed_elem _ e⟩, by simp [word_new, chars]⟩
  have : runs (xs ++ chars (word text) ++ [.elem e]) = runs xs ++ (textPart (word text) ++ [.inr e]) := by
    rw [List.append_assoc, runs_append_closed xs _ cx, runs_chars_append (word text) [.elem e] (by simp)]
    simp [runs]
  rw [h2, List.map_append, h1, hx, this]; simp [nodeView]

/-- The children of an element: what was read, then the pending characters. -/
theorem children_of {nodes children : alloc.vec.Vec xml.Node} {text : alloc.vec.Vec U32} {items : List Item}
    (rel : Rel (alloc.vec.Vec.new xml.Node) (alloc.vec.Vec.new U32) nodes text items)
    (h : children.val.map nodeView = nodes.val.map nodeView ++ textPart (word text)) :
    children.val.map nodeView = runs items := by
  obtain ⟨xs', ⟨hn, cx⟩, e⟩ := rel [] nodesOk_new
  rw [h, hn, ← runs_chars, ← runs_append_closed xs' _ cx, e]
  simp [word_new, chars]

/-! ## Ends of tags -/

theorem tag_end_spec (cs : alloc.vec.Vec U32) (j : Usize) :
    ∃ r, xml.tag_end cs j = .ok r ∧
      match r with
      | .Ok (empty, after) => (empty = false ∧ charAt cs j.val = 62 ∧ after.val = j.val + 1) ∨
          (empty = true ∧ charAt cs j.val = 47 ∧ charAt cs (j.val + 1) = 62 ∧ after.val = j.val + 2)
      | .Err _ => ¬ (charAt cs j.val = 62 ∨ (charAt cs j.val = 47 ∧ charAt cs (j.val + 1) = 62)) := by
  unfold xml.tag_end
  simp only [at_eq, bind_ok, atU_eq_iff]
  by_cases gt : charAt cs j.val = 62
  · obtain ⟨inside, _⟩ := drop_nonzero (by rw [gt]; decide : charAt cs j.val ≠ 0)
    obtain ⟨j1, hj1, hj1v⟩ := next_spec inside
    refine ⟨.Ok (false, j1), by simp [gt, hj1], Or.inl ⟨rfl, gt, hj1v⟩⟩
  · by_cases sl : charAt cs j.val = 47
    · obtain ⟨inside, _⟩ := drop_nonzero (by rw [sl]; decide : charAt cs j.val ≠ 0)
      obtain ⟨j1, hj1, hj1v⟩ := next_spec inside
      by_cases gt1 : charAt cs (j.val + 1) = 62
      · have inside1 : j.val + 1 < cs.val.length := charAt_inside (by rw [gt1]; decide)
        obtain ⟨j2, hj2, hj2v⟩ := skip_spec (cs := cs) (i := j) (c := 2#usize) (by simp; omega)
        refine ⟨.Ok (true, j2), by simp [gt, sl, hj1, hj1v, gt1, hj2], Or.inr ⟨rfl, sl, gt1, by simpa using hj2v⟩⟩
      · refine ⟨.Err ⟨.Syntax, j⟩, by simp [gt, sl, hj1, hj1v, gt1, xml.fail], ?_⟩
        rintro (h | ⟨_, h⟩) <;> contradiction
    · refine ⟨.Err ⟨.Syntax, j⟩, by simp [gt, sl, xml.fail], ?_⟩
      rintro (h | ⟨h, _⟩) <;> contradiction

theorem fits_eq (cs : alloc.vec.Vec U32) (i n : Usize) (h : i.val ≤ cs.val.length) :
    xml.fits cs i n = .ok (decide (n.val ≤ cs.val.length - i.val)) := by
  unfold xml.fits
  obtain ⟨d, hd, hdv⟩ := sub_eq (x := alloc.vec.Vec.len cs) (y := i) (by simp [alloc.vec.Vec.len_val]; exact h)
  simp only [hd, bind_ok]
  congr 1
  simp [UScalar.le_equiv, hdv, alloc.vec.Vec.len_val]

theorem local_start_eq (start mark stop : Usize) (h : mark.val ≤ stop.val) :
    ∃ v : Usize, xml.local_start start mark stop = .ok v ∧
      v.val = if mark.val = stop.val then start.val else mark.val + 1 := by
  unfold xml.local_start
  by_cases e : mark = stop
  · exact ⟨start, by simp [e], by simp [e]⟩
  · have e' : ¬ mark.val = stop.val := fun x => e (UScalar.eq_of_val_eq x)
    obtain ⟨m1, hm1, hm1v⟩ := succ_spec (x := mark) (y := stop) (by omega)
    exact ⟨m1, by simp [e, hm1], by simp [e', hm1v]⟩

/-- A word read character by character from a position. -/
theorem drop_of_chars {cs : alloc.vec.Vec U32} {a : Nat} {w : Word} (fit : a + w.length ≤ cs.val.length)
    (h : ∀ t (ht : t < w.length), charAt cs (a + t) = w[t]) :
    (word cs).drop a = w ++ (word cs).drop (a + w.length) := by
  have e1 : (word cs).drop a = ((word cs).drop a).take w.length ++ ((word cs).drop a).drop w.length :=
    (List.take_append_drop _ _).symm
  rw [List.drop_drop] at e1
  rw [e1]
  congr 1
  apply List.ext_getElem
  · simp [word_length]; omega
  · intro t h1 h2
    rw [List.getElem_take, List.getElem_drop]
    have hc := charAt_getElem (cs := cs) (i := a + t) (by omega)
    rw [List.getElem?_eq_getElem (by rw [word_length]; omega)] at hc
    rw [Option.some.inj hc, h t h2]

theorem end_tag_spec (cs : alloc.vec.Vec U32) (i start stop : Usize) {n rest0 : Word}
    (nsplit : (word cs).drop start.val = n ++ rest0) (hs : stop.val = start.val + n.length) :
    ∃ r, xml.end_tag cs i start stop = .ok r ∧
      (∀ j, r = .Ok j → ∃ s2, (word cs).drop i.val = lit "</" ++ n ++ s2 ++ [62] ++ (word cs).drop j.val ∧
        OptS s2 ∧ j.val = i.val + 3 + n.length + s2.length) ∧
      (∀ s2 more, (word cs).drop i.val = lit "</" ++ n ++ s2 ++ [62] ++ more → OptS s2 → ∃ j, r = .Ok j) := by
  unfold xml.end_tag
  simp only [lift, bind_ok, starts_eq, bytes_make, map_end_bytes, decide_eq_true_eq]
  have nchars : ∀ t (ht : t < n.length), charAt cs (start.val + t) = n[t] := fun t ht => charAt_of_drop nsplit ht
  have lend : lit "</" = [60, 47] := by decide
  by_cases st : lit "</" <+: (word cs).drop i.val
  · rw [if_pos st]
    obtain ⟨d2, inside2⟩ := prefix_split st (by rw [lend]; simp)
    rw [lend] at d2 inside2
    simp only [List.length_cons, List.length_nil] at d2 inside2
    obtain ⟨i1, hi1, hi1v⟩ := skip_spec (cs := cs) (i := i) (c := 2#usize) (by simp; omega)
    have i1v : i1.val = i.val + 2 := by simpa using hi1v
    obtain ⟨d, hd, hdv⟩ := sub_eq (x := stop) (y := start) (by omega)
    have dn : d.val = n.length := by omega
    simp only [hi1, hd, bind_ok, fits_eq cs i1 d (by omega), decide_eq_true_eq]
    by_cases fit : d.val ≤ cs.val.length - i1.val
    · rw [if_pos fit]
      obtain ⟨i3, hi3, hi3v⟩ := skip_spec (cs := cs) (i := i1) (c := d) (by omega)
      simp only [hi3, bind_ok]
      unfold xml.end_name
      simp only [hi1, hd, bind_ok]
      have maxc : cs.val.length ≤ Usize.max := cs.property
      rw [same_from_eq cs i1 start d 0#usize (by omega) (by have := usize_le_max stop; omega)]
      simp only [bind_ok, decide_eq_true_eq]
      by_cases same : ∀ t, (0#usize : Usize).val ≤ t → t < d.val → charAt cs (i1.val + t) = charAt cs (start.val + t)
      · rw [if_pos same]
        have nd : (word cs).drop i1.val = n ++ (word cs).drop (i1.val + n.length) := by
          apply drop_of_chars (by omega)
          intro t ht; rw [same t (by simp) (by omega), nchars t ht]
        obtain ⟨j, hj, hjv⟩ := skip_spaces_eq cs i3
        have split3 := drop_run IsSpace cs i3.val
        rw [← hjv] at split3
        have all3 : ∀ c ∈ run IsSpace ((word cs).drop i3.val), IsSpace c := run_all
        generalize hr3 : run IsSpace ((word cs).drop i3.val) = r3 at split3 hjv all3
        simp only [hj, bind_ok, at_eq, atU_eq_iff]
        have i3v : i3.val = i1.val + n.length := by omega
        by_cases gt : charAt cs j.val = 62
        · obtain ⟨insideJ, dJ⟩ := drop_nonzero (by rw [gt]; decide : charAt cs j.val ≠ 0)
          obtain ⟨j1, hj1, hj1v⟩ := next_spec insideJ
          refine ⟨.Ok j1, by simp [gt, hj1], ?_, fun _ _ _ _ => ⟨j1, rfl⟩⟩
          intro j' e; simp at e; subst e
          refine ⟨r3, ?_, all3, by omega⟩
          rw [d2, ← i1v, nd, ← i3v, split3, dJ, gt, hj1v]; simp [lend]
        · refine ⟨.Err ⟨.MismatchedEndTag, i⟩, by simp [gt, xml.fail], by simp, ?_⟩
          intro s2 more split hs2
          have d3 : (word cs).drop i3.val = s2 ++ 62 :: more := by
            have e3 : i3.val = i.val + (lit "</" ++ n).length := by rw [lend]; simp; omega
            rw [e3]
            exact drop_after (cs := cs) (i := i.val) (w := lit "</" ++ n) (rest := s2 ++ 62 :: more)
              (by rw [split]; simp)
          have rs : r3 = s2 := by
            rw [← hr3]; exact run_spaces_eq d3 hs2 (fun c m e => by simp at e; rw [e.1]; simp [IsSpace])
          exfalso; apply gt
          rw [hjv, rs]
          have := charAt_after (cs := cs) (i := i3.val) (w := s2) (rest := 62 :: more) d3
          simpa using this
      · rw [if_neg same]
        refine ⟨.Err ⟨.MismatchedEndTag, i⟩, by simp [xml.fail], by simp, ?_⟩
        intro s2 more split hs2
        exfalso; apply same
        intro t _ ht
        have d1 : (word cs).drop i1.val = n ++ (s2 ++ 62 :: more) := by
          rw [i1v]
          have := drop_after (cs := cs) (i := i.val) (w := lit "</") (rest := n ++ (s2 ++ 62 :: more))
            (by rw [split]; simp)
          rw [lend] at this; simpa using this
        rw [charAt_of_drop d1 (by omega), nchars t (by omega)]
    · rw [if_neg fit]
      refine ⟨.Err ⟨.MismatchedEndTag, i⟩, by simp [xml.fail], by simp, ?_⟩
      intro s2 more split hs2
      exfalso; apply fit
      have := consumed_le split (by rw [lend]; simp)
      simp [lend] at this
      omega
  · rw [if_neg st]
    refine ⟨.Err ⟨.UnexpectedEnd, i⟩, by simp [xml.fail], by simp, ?_⟩
    intro s2 more split hs2
    exfalso; apply st; rw [split]; exact ⟨n ++ s2 ++ [62] ++ more, by simp⟩

end Rowl.XmlContent
