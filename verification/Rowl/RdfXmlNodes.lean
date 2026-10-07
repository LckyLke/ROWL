import Rowl.RdfXmlProps

/-!
# Node and property elements

Correctness of the mutually recursive functions of `rdfxml.rs`: node
elements, property element lists, property elements and their productions,
and collections, against the relations of `RdfXmlGrammar`.
-/

namespace Rowl.RdfXmlNodes
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar Rowl.RdfXmlGrammar Rowl.RdfXmlSpell Rowl.RdfXmlTerms
open Rowl.RdfXmlEvents Rowl.RdfXmlProps
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-! ## Result specifications -/

/-- What a function returning a subject and a state with new triples computes. -/
def NodeSpec (r : core.result.Result (rdf.Subject × rdfxml.State) rdfxml.ErrorKind) (state : rdfxml.State)
    (limits : rdfxml.Limits) (R : Term → List Statement → St → Prop) : Prop :=
  (∀ s s', r = .Ok (s, s') → ∃ ts, R (subjectTerm s) ts (stOf s') ∧ stmts s' = stmts state ++ ts ∧
    Fits limits s') ∧
  (∀ t ts st', R t ts st' → (stmts state ++ ts).length ≤ limits.items.val → st'.blanks ≤ limits.items.val →
    st'.ids.length ≤ limits.items.val →
    ∃ s s', r = .Ok (s, s') ∧ subjectTerm s = t ∧ stmts s' = stmts state ++ ts ∧ stOf s' = st')

/-- What a function returning an rdf:li counter and a state computes. -/
def LiSpec (r : core.result.Result (Usize × rdfxml.State) rdfxml.ErrorKind) (state : rdfxml.State)
    (limits : rdfxml.Limits) (R : Nat → List Statement → St → Prop) : Prop :=
  (∀ n s', r = .Ok (n, s') → ∃ ts, R n.val ts (stOf s') ∧ stmts s' = stmts state ++ ts ∧ Fits limits s') ∧
  (∀ n ts st', R n ts st' → (stmts state ++ ts).length ≤ limits.items.val → st'.blanks ≤ limits.items.val →
    st'.ids.length ≤ limits.items.val →
    ∃ n' s', r = .Ok (n', s') ∧ n'.val = n ∧ stmts s' = stmts state ++ ts ∧ stOf s' = st')

/-! ## Bodies of the productions -/

/-- A node element after its element event. -/
def NodeBody (c : Ctx) (evs : List (Word × Word)) (u : Word) (e : xml.Element) (st : St) (s : Term)
    (ts : List Statement) (st' : St) : Prop :=
  NodeAttributes evs ∧ ∃ st1 ts1 ts2 ts3, SubjectOf c evs st s st1 ∧ TypeTriple c s u ts1 ∧
    PropAttrs c s evs ts2 ∧ PropertyElts c s e.children.val 1 st1 ts3 st' ∧ ts = ts1 ++ ts2 ++ ts3

theorem nodeElement_iff (c : Ctx) (e : xml.Element) (st : St) (s : Term) (ts : List Statement) (st' : St) :
    NodeElement c e st s ts st' ↔ ∃ c' evs u, Prepared c e c' evs ∧ ElementUri c.termLimit e u ∧
      NodeElementUri u ∧ NodeBody c' evs u e st s ts st' := by
  constructor
  · intro h; cases h with
    | mk pr eu nu na so tt pa pe => exact ⟨_, _, _, pr, eu, nu, na, _, _, _, _, so, tt, pa, pe, rfl⟩
  · rintro ⟨c', evs, u, pr, eu, nu, na, st1, ts1, ts2, ts3, so, tt, pa, pe, rfl⟩
    exact .mk pr eu nu na so tt pa pe

/-- resourcePropertyElt after its element event and predicate. -/
def ResourceEltBody (c : Ctx) (evs : List (Word × Word)) (e : xml.Element) (s : Term) (p : List U8) (st : St)
    (ts : List Statement) (st' : St) : Prop :=
  Only evs [rdfName "ID"] ∧ ∃ pre n post sn tsn st1 ts2, e.children.val = pre ++ [.Element n] ++ post ∧
    AllWs pre ∧ AllWs post ∧ NodeElement c n st sn tsn st1 ∧ Stated c evs ⟨s, p, sn⟩ st1 ts2 st' ∧
    ts = tsn ++ ts2

/-- parseTypeResourcePropertyElt after its element event and predicate. -/
def ParseResourceBody (c : Ctx) (evs : List (Word × Word)) (e : xml.Element) (s : Term) (p : List U8)
    (st : St) (ts : List Statement) (st' : St) : Prop :=
  Only evs [rdfName "ID", rdfName "parseType"] ∧ ∃ ts1 st2 tsc,
    Stated c evs ⟨s, p, (fresh c st).1⟩ (fresh c st).2 ts1 st2 ∧
    PropertyElts c (fresh c st).1 e.children.val 1 st2 tsc st' ∧ ts = ts1 ++ tsc

/-- parseTypeCollectionPropertyElt after its element event and predicate. -/
def CollectionBody (c : Ctx) (evs : List (Word × Word)) (e : xml.Element) (s : Term) (p : List U8)
    (st : St) (ts : List Statement) (st' : St) : Prop :=
  Only evs [rdfName "ID", rdfName "parseType"] ∧ ∃ h tsl st1 ts2,
    NodeList c e.children.val st h tsl st1 ∧ Stated c evs ⟨s, p, h⟩ st1 ts2 st' ∧ ts = tsl ++ ts2

/-- A property element after its element event and predicate. -/
def PropBody (c : Ctx) (evs : List (Word × Word)) (e : xml.Element) (s : Term) (p : List U8) (st : St)
    (ts : List Statement) (st' : St) : Prop :=
  (attrValue (rdfName "parseType") evs = some (lit "Resource") ∧ ParseResourceBody c evs e s p st ts st') ∨
  (attrValue (rdfName "parseType") evs = some (lit "Collection") ∧ CollectionBody c evs e s p st ts st') ∨
  (attrValue (rdfName "parseType") evs = none ∧ e.children.val = [] ∧ EmptyBody c evs s p st ts st') ∨
  (attrValue (rdfName "parseType") evs = none ∧ ResourceEltBody c evs e s p st ts st') ∨
  (attrValue (rdfName "parseType") evs = none ∧ LiteralBody c evs e s p st ts st')

theorem propertyElt_iff (c : Ctx) (s : Term) (e : xml.Element) (li n : Nat) (st : St) (ts : List Statement)
    (st' : St) :
    PropertyElt c s e li n st ts st' ↔ ∃ c' evs p, Prepared c e c' evs ∧ Predicate c e li p n ∧
      PropBody c' evs e s p st ts st' := by
  constructor
  · intro h; cases h with
    | resource pr pd pt on ch wp wq ne sd =>
      exact ⟨_, _, _, pr, pd, .inr (.inr (.inr (.inl ⟨pt, on, _, _, _, _, _, _, _, ch, wp, wq, ne, sd, rfl⟩)))⟩
    | literal pr pd pt on ch tob sd =>
      exact ⟨_, _, _, pr, pd, .inr (.inr (.inr (.inr ⟨pt, on, _, _, ch, tob, sd⟩)))⟩
    | parseResource pr pd pt on sd pe =>
      exact ⟨_, _, _, pr, pd, .inl ⟨pt, on, _, _, _, sd, pe, rfl⟩⟩
    | collection pr pd pt on nl sd =>
      exact ⟨_, _, _, pr, pd, .inr (.inl ⟨pt, on, _, _, _, _, nl, sd, rfl⟩)⟩
    | emptyLiteral pr pd pt ch on lo sd =>
      exact ⟨_, _, _, pr, pd, .inr (.inr (.inl ⟨pt, ch, .inl ⟨on, _, lo, sd⟩⟩))⟩
    | emptyTyped pr pd pt ch on hd ty sd =>
      exact ⟨_, _, _, pr, pd, .inr (.inr (.inl ⟨pt, ch, .inr (.inl ⟨on, _, _, hd, ty, sd⟩)⟩))⟩
    | emptyResource pr pd pt ch no nd ea eo pa sd =>
      exact ⟨_, _, _, pr, pd, .inr (.inr (.inl ⟨pt, ch, .inr (.inr ⟨no, nd, ea, _, _, _, _, eo, pa, sd, rfl⟩)⟩))⟩
  · rintro ⟨c', evs, p, pr, pd, body⟩
    rcases body with ⟨pt, on, ts1, st2, tsc, sd, pe, rfl⟩ | ⟨pt, on, h, tsl, st1, ts2, nl, sd, rfl⟩ |
      ⟨pt, ch, ⟨on, o, lo, sd⟩ | ⟨on, d, o, hd, ty, sd⟩ | ⟨no, nd, ea, r, st1, tsa, ts2, eo, pa, sd, rfl⟩⟩ |
      ⟨pt, on, pre, n, post, sn, tsn, st1, ts2, ch, wp, wq, ne, sd, rfl⟩ | ⟨pt, on, t, o, ch, tob, sd⟩
    · exact .parseResource pr pd pt on sd pe
    · exact .collection pr pd pt on nl sd
    · exact .emptyLiteral pr pd pt ch on lo sd
    · exact .emptyTyped pr pd pt ch on hd ty sd
    · exact .emptyResource pr pd pt ch no nd ea eo pa sd
    · exact .resource pr pd pt on ch wp wq ne sd
    · exact .literal pr pd pt on ch tob sd

theorem propertyElts_nil_iff (c : Ctx) (s : Term) (li : Nat) (st : St) (ts : List Statement) (st' : St) :
    PropertyElts c s [] li st ts st' ↔ ts = [] ∧ st' = st := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .nil

theorem propertyElts_cons_iff (c : Ctx) (s : Term) (x : xml.Node) (rest : List xml.Node) (li : Nat) (st : St)
    (ts : List Statement) (st' : St) :
    PropertyElts c s (x :: rest) li st ts st' ↔
      (∃ t, x = .Text t ∧ Ws (word t) ∧ PropertyElts c s rest li st ts st') ∨
      (∃ e li' st1 ts1 ts2, x = .Element e ∧ PropertyElt c s e li li' st ts1 st1 ∧
        PropertyElts c s rest li' st1 ts2 st' ∧ ts = ts1 ++ ts2) := by
  constructor
  · intro h; cases h with
    | space w r => exact .inl ⟨_, rfl, w, r⟩
    | elt pe r => exact .inr ⟨_, _, _, _, _, rfl, pe, r, rfl⟩
  · rintro (⟨t, rfl, w, r⟩ | ⟨e, li', st1, ts1, ts2, rfl, pe, r, rfl⟩)
    · exact .space w r
    · exact .elt pe r

theorem nodeList_nil_iff (c : Ctx) (st : St) (h : Term) (ts : List Statement) (st' : St) :
    NodeList c [] st h ts st' ↔ h = .iri (rdfBytes "nil") ∧ ts = [] ∧ st' = st := by
  constructor
  · intro hl; cases hl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; exact .nil

theorem nodeList_cons_iff (c : Ctx) (x : xml.Node) (rest : List xml.Node) (st : St) (h : Term)
    (ts : List Statement) (st' : St) :
    NodeList c (x :: rest) st h ts st' ↔
      (∃ t, x = .Text t ∧ Ws (word t) ∧ NodeList c rest st h ts st') ∨
      (∃ f sf tsf st2 hr tsr, x = .Element f ∧ NodeElement c f (fresh c st).2 sf tsf st2 ∧
        NodeList c rest st2 hr tsr st' ∧ h = (fresh c st).1 ∧
        ts = tsf ++ tsr ++ [⟨(fresh c st).1, rdfBytes "first", sf⟩, ⟨(fresh c st).1, rdfBytes "rest", hr⟩]) := by
  constructor
  · intro hl; cases hl with
    | space w r => exact .inl ⟨_, rfl, w, r⟩
    | member ne r => exact .inr ⟨_, _, _, _, _, _, rfl, ne, r, rfl, rfl⟩
  · rintro (⟨t, rfl, w, r⟩ | ⟨f, sf, tsf, st2, hr, tsr, rfl, ne, r, rfl, rfl⟩)
    · exact .space w r
    · exact .member ne r

/-! ## States only grow -/

/-- The generated blank nodes and rdf:ID values of `st'` include those of `st`. -/
def Grows (st st' : St) : Prop := st.blanks ≤ st'.blanks ∧ st.ids.length ≤ st'.ids.length

theorem grows_refl (st : St) : Grows st st := ⟨le_refl _, le_refl _⟩

theorem grows_trans {a b d : St} (h1 : Grows a b) (h2 : Grows b d) : Grows a d :=
  ⟨Nat.le_trans h1.1 h2.1, Nat.le_trans h1.2 h2.2⟩

theorem grows_fresh (c : Ctx) (st : St) : Grows st (fresh c st).2 := by
  simp [Grows, fresh]

theorem grows_idIri {c : Ctx} {v : Word} {st : St} {i : List U8} {st' : St} (h : IdIri c v st i st') :
    Grows st st' := by
  obtain ⟨b, l⟩ := idIri_blanks h; exact ⟨by omega, by omega⟩

theorem grows_stated {c : Ctx} {evs : List (Word × Word)} {t : Statement} {st : St} {ts : List Statement}
    {st' : St} (h : Stated c evs t st ts st') : Grows st st' := by
  obtain ⟨b, l⟩ := stated_mono h; exact ⟨by omega, l⟩

theorem grows_subjectOf {c : Ctx} {evs : List (Word × Word)} {st : St} {t : Term} {st' : St}
    (h : SubjectOf c evs st t st') : Grows st st' := by
  rcases (subjectOf_iff ..).mp h with ⟨v, i, -, ii, -⟩ | ⟨-, -, -, -, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩ |
    ⟨-, -, -, -, rfl⟩
  · exact grows_idIri ii
  · exact grows_refl _
  · exact grows_refl _
  · exact grows_fresh c st

theorem grows_emptyObject {c : Ctx} {evs : List (Word × Word)} {st : St} {t : Term} {st' : St}
    (h : EmptyObject c evs st t st') : Grows st st' := by
  rcases (emptyObject_iff ..).mp h with ⟨-, -, -, -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
  · exact grows_refl _
  · exact grows_refl _
  · exact grows_fresh c st

mutual
theorem grows_nodeElement : ∀ {c : Ctx} {e : xml.Element} {st : St} {s : Term} {ts : List Statement} {st' : St},
    NodeElement c e st s ts st' → Grows st st'
  | _, _, _, _, _, _, .mk _ _ _ _ so _ _ pe => grows_trans (grows_subjectOf so) (grows_propertyElts pe)

theorem grows_propertyElts : ∀ {c : Ctx} {s : Term} {nodes : List xml.Node} {li : Nat} {st : St}
    {ts : List Statement} {st' : St}, PropertyElts c s nodes li st ts st' → Grows st st'
  | _, _, _, _, _, _, _, .nil => grows_refl _
  | _, _, _, _, _, _, _, .space _ r => grows_propertyElts r
  | _, _, _, _, _, _, _, .elt pe r => grows_trans (grows_propertyElt pe) (grows_propertyElts r)

theorem grows_propertyElt : ∀ {c : Ctx} {s : Term} {e : xml.Element} {li li' : Nat} {st : St}
    {ts : List Statement} {st' : St}, PropertyElt c s e li li' st ts st' → Grows st st'
  | _, _, _, _, _, _, _, _, .resource _ _ _ _ _ _ _ ne sd => grows_trans (grows_nodeElement ne) (grows_stated sd)
  | _, _, _, _, _, _, _, _, .literal _ _ _ _ _ _ sd => grows_stated sd
  | _, _, _, _, _, _, _, _, .parseResource _ _ _ _ sd pe =>
    grows_trans (grows_fresh _ _) (grows_trans (grows_stated sd) (grows_propertyElts pe))
  | _, _, _, _, _, _, _, _, .collection _ _ _ _ nl sd => grows_trans (grows_nodeList nl) (grows_stated sd)
  | _, _, _, _, _, _, _, _, .emptyLiteral _ _ _ _ _ _ sd => grows_stated sd
  | _, _, _, _, _, _, _, _, .emptyTyped _ _ _ _ _ _ _ sd => grows_stated sd
  | _, _, _, _, _, _, _, _, .emptyResource _ _ _ _ _ _ _ eo _ sd =>
    grows_trans (grows_emptyObject eo) (grows_stated sd)

theorem grows_nodeList : ∀ {c : Ctx} {nodes : List xml.Node} {st : St} {h : Term} {ts : List Statement}
    {st' : St}, NodeList c nodes st h ts st' → Grows st st'
  | _, _, _, _, _, _, .nil => grows_refl _
  | _, _, _, _, _, _, .space _ r => grows_nodeList r
  | _, _, _, _, _, _, .member ne r =>
    grows_trans (grows_fresh _ _) (grows_trans (grows_nodeElement ne) (grows_nodeList r))
end

/-! ## Sizes of element trees -/

theorem listN_sizeOf_mem {α : Type} [SizeOf α] {n : Nat} (l : Aeneas.Data.ListN.ListN α n) {x : α}
    (h : x ∈ l.toList) : sizeOf x < sizeOf l := by
  induction l with
  | nil => simp [Aeneas.Data.ListN.ListN.toList] at h
  | cons a t ih =>
    simp only [Aeneas.Data.ListN.ListN.toList, List.mem_cons] at h
    simp only [Aeneas.Data.ListN.ListN.cons.sizeOf_spec]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

theorem vec_sizeOf_mem {α : Type} [SizeOf α] (v : alloc.vec.Vec α) {x : α} (h : x ∈ v.val) :
    sizeOf x < sizeOf v := by
  obtain ⟨⟨n, l, b⟩⟩ := v
  have := listN_sizeOf_mem l (by simpa [alloc.vec.Vec.val, Slice.val] using h)
  simp only [alloc.vec.Vec.mk.sizeOf_spec, Slice.mk.sizeOf_spec]
  omega

theorem sizeOf_children_lt (e : xml.Element) : sizeOf e.children < sizeOf e := by
  cases e with
  | mk p n l a d cs =>
    simp only [xml.Element.children, xml.Element.mk.sizeOf_spec]
    omega

theorem sizeOf_node_lt {cs : alloc.vec.Vec xml.Node} {f : xml.Element} (h : xml.Node.Element f ∈ cs.val) :
    sizeOf f < sizeOf cs := by
  have h1 := vec_sizeOf_mem cs h
  simp only [xml.Node.Element.sizeOf_spec] at h1
  omega

theorem sizeOf_child_lt {e f : xml.Element} (h : xml.Node.Element f ∈ e.children.val) : sizeOf f < sizeOf e :=
  Nat.lt_trans (sizeOf_node_lt h) (sizeOf_children_lt e)

/-! ## Productions of property elements -/

theorem stateSpec_congr {r : core.result.Result rdfxml.State rdfxml.ErrorKind} {state : rdfxml.State}
    {limits : rdfxml.Limits} {R R' : List Statement → St → Prop} (h : ∀ ts st', R ts st' ↔ R' ts st') :
    StateSpec r state limits R ↔ StateSpec r state limits R' := by
  unfold StateSpec
  simp only [h]

theorem productionOf_le (evs : List (Word × Word)) (children : List xml.Node) : productionOf evs children ≤ 5 := by
  unfold productionOf
  split <;> split_ifs <;> omega

theorem productionOf_some {evs : List (Word × Word)} {children : List xml.Node} {v : Word}
    (h : attrValue (rdfName "parseType") evs = some v) :
    productionOf evs children = if v = lit "Resource" then 0 else if v = lit "Collection" then 1 else 2 := by
  unfold productionOf; rw [h]

theorem productionOf_none {evs : List (Word × Word)} {children : List xml.Node}
    (h : attrValue (rdfName "parseType") evs = none) :
    productionOf evs children = if children = [] then 3 else if (∃ f, xml.Node.Element f ∈ children) then 4 else 5 := by
  unfold productionOf; rw [h]

theorem resource_ne_collection : lit "Resource" ≠ lit "Collection" := by decide

theorem none_not_small {children : List xml.Node} {k : Nat} (hk : k ≤ 2)
    (h : (if children = [] then 3 else if (∃ f, xml.Node.Element f ∈ children) then 4 else 5) = k) : False := by
  split_ifs at h <;> omega

theorem some_not_big {v : Word} {k : Nat} (hk : 3 ≤ k)
    (h : (if v = lit "Resource" then 0 else if v = lit "Collection" then 1 else 2) = k) : False := by
  split_ifs at h <;> omega

theorem prop_body_0 {c : Ctx} {evs : List (Word × Word)} {e : xml.Element} {s : Term} {p : List U8} {st : St}
    (h : productionOf evs e.children.val = 0) (ts : List Statement) (st' : St) :
    PropBody c evs e s p st ts st' ↔ ParseResourceBody c evs e s p st ts st' := by
  cases hv : attrValue (rdfName "parseType") evs with
  | none => rw [productionOf_none hv] at h; exact (none_not_small (by omega) h).elim
  | some v =>
    rw [productionOf_some hv] at h
    by_cases h1 : v = lit "Resource"
    · subst h1
      unfold PropBody; rw [hv]
      simp [resource_ne_collection]
    · rw [if_neg h1] at h; split_ifs at h <;> omega

theorem prop_body_1 {c : Ctx} {evs : List (Word × Word)} {e : xml.Element} {s : Term} {p : List U8} {st : St}
    (h : productionOf evs e.children.val = 1) (ts : List Statement) (st' : St) :
    PropBody c evs e s p st ts st' ↔ CollectionBody c evs e s p st ts st' := by
  cases hv : attrValue (rdfName "parseType") evs with
  | none => rw [productionOf_none hv] at h; exact (none_not_small (by omega) h).elim
  | some v =>
    rw [productionOf_some hv] at h
    by_cases h1 : v = lit "Resource"
    · rw [if_pos h1] at h; omega
    · rw [if_neg h1] at h
      by_cases h2 : v = lit "Collection"
      · subst h2
        unfold PropBody; rw [hv]
        simp [resource_ne_collection.symm]
      · rw [if_neg h2] at h; omega

theorem prop_body_2 {c : Ctx} {evs : List (Word × Word)} {e : xml.Element} {s : Term} {p : List U8} {st : St}
    (h : productionOf evs e.children.val = 2) (ts : List Statement) (st' : St) :
    ¬ PropBody c evs e s p st ts st' := by
  cases hv : attrValue (rdfName "parseType") evs with
  | none => rw [productionOf_none hv] at h; exact (none_not_small (by omega) h).elim
  | some v =>
    rw [productionOf_some hv] at h
    by_cases h1 : v = lit "Resource"
    · rw [if_pos h1] at h; omega
    · rw [if_neg h1] at h
      by_cases h2 : v = lit "Collection"
      · rw [if_pos h2] at h; omega
      · unfold PropBody; rw [hv]
        simp only [Option.some.injEq, reduceCtorEq, false_and, or_false, not_or, not_and]
        exact ⟨fun e => (h1 e).elim, fun e => (h2 e).elim⟩

theorem prop_body_3 {c : Ctx} {evs : List (Word × Word)} {e : xml.Element} {s : Term} {p : List U8} {st : St}
    (h : productionOf evs e.children.val = 3) (ts : List Statement) (st' : St) :
    PropBody c evs e s p st ts st' ↔ EmptyBody c evs s p st ts st' := by
  cases hv : attrValue (rdfName "parseType") evs with
  | some v => rw [productionOf_some hv] at h; exact (some_not_big (by omega) h).elim
  | none =>
    rw [productionOf_none hv] at h
    by_cases h1 : e.children.val = []
    · unfold PropBody ResourceEltBody LiteralBody; rw [hv, h1]
      simp
    · rw [if_neg h1] at h; split_ifs at h <;> omega

theorem prop_body_4 {c : Ctx} {evs : List (Word × Word)} {e : xml.Element} {s : Term} {p : List U8} {st : St}
    (h : productionOf evs e.children.val = 4) (ts : List Statement) (st' : St) :
    PropBody c evs e s p st ts st' ↔ ResourceEltBody c evs e s p st ts st' := by
  cases hv : attrValue (rdfName "parseType") evs with
  | some v => rw [productionOf_some hv] at h; exact (some_not_big (by omega) h).elim
  | none =>
    rw [productionOf_none hv] at h
    by_cases h1 : e.children.val = []
    · rw [if_pos h1] at h; omega
    · rw [if_neg h1] at h
      by_cases h2 : ∃ f, xml.Node.Element f ∈ e.children.val
      · unfold PropBody LiteralBody; rw [hv]
        simp only [reduceCtorEq, false_and, false_or, h1, true_and]
        constructor
        · rintro (rb | ⟨-, t, o, ch, -⟩)
          · exact rb
          · obtain ⟨f, hf⟩ := h2; rw [ch] at hf; simp at hf
        · intro rb; exact .inl rb
      · rw [if_neg h2] at h; omega

theorem prop_body_5 {c : Ctx} {evs : List (Word × Word)} {e : xml.Element} {s : Term} {p : List U8} {st : St}
    (h : productionOf evs e.children.val = 5) (ts : List Statement) (st' : St) :
    PropBody c evs e s p st ts st' ↔ LiteralBody c evs e s p st ts st' := by
  cases hv : attrValue (rdfName "parseType") evs with
  | some v => rw [productionOf_some hv] at h; exact (some_not_big (by omega) h).elim
  | none =>
    rw [productionOf_none hv] at h
    by_cases h1 : e.children.val = []
    · rw [if_pos h1] at h; omega
    · rw [if_neg h1] at h
      by_cases h2 : ∃ f, xml.Node.Element f ∈ e.children.val
      · rw [if_pos h2] at h; omega
      · unfold PropBody ResourceEltBody; rw [hv]
        simp only [reduceCtorEq, false_and, false_or, h1, true_and]
        constructor
        · rintro (⟨-, pre, n, post, -, -, -, -, ch, -⟩ | lb)
          · exact (h2 ⟨n, by rw [ch]; simp⟩).elim
          · exact lb
        · intro lb; exact .inr lb

theorem one_element_unique : ∀ (m m' post post' : List xml.Node) (n n' : xml.Element),
    m ++ [.Element n] ++ post = m' ++ [.Element n'] ++ post' → AllWs m → AllWs m' → m = m' ∧ n = n' ∧ post = post'
  | [], [], _, _, _, _, h, _, _ => by simp at h; exact ⟨rfl, h.1, h.2⟩
  | [], x :: m', _, _, _, _, h, _, w' => by
    simp at h; obtain ⟨rfl, -⟩ := h
    obtain ⟨⟨t, ht, -⟩, -⟩ := (allWs_cons _ _).mp w'; cases ht
  | x :: m, [], _, _, _, _, h, w, _ => by
    simp at h; obtain ⟨rfl, -⟩ := h
    obtain ⟨⟨t, ht, -⟩, -⟩ := (allWs_cons _ _).mp w; cases ht
  | x :: m, y :: m', post, post', n, n', h, w, w' => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨e1, e2, e3⟩ := one_element_unique m m' post post' n n' (by simpa using h)
      ((allWs_cons _ _).mp w).2 ((allWs_cons _ _).mp w').2
    exact ⟨by rw [e1], e2, e3⟩

theorem usize_of (n : Nat) (h : n ≤ Usize.max) : ∃ k : Usize, k.val = n :=
  ⟨Usize.ofNatCore n (by
    cases platform : System.Platform.numBits_eq <;> simp_all [Usize.max, Usize.numBits] <;> omega), by simp⟩

/-! ## The mutually recursive functions -/

theorem agrees_prep {c : Ctx} {base : alloc.vec.Vec U8} {lang : alloc.vec.Vec U32} {scope : alloc.vec.Vec U8}
    {limits : rdfxml.Limits} (ag : Agrees c base lang scope limits) (p : rdfxml.Prepared)
    (pb : p.base.val.length ≤ limits.term_bytes.val) : Agrees (prepCtx c p) p.base p.lang scope limits :=
  ⟨rfl, rfl, ag.hscope, ag.hterm, ag.hitems, pb, ag.hsmall, ag.hpos⟩

theorem stmts_triples {s1 s2 : rdfxml.State} (h : s1.triples = s2.triples) : stmts s1 = stmts s2 := by
  simp [stmts, h]

theorem usize_one_val : (1#usize : Usize).val = 1 := by simp

theorem fits_fresh {c : Ctx} {limits : rdfxml.Limits} {state s1 : rdfxml.State} (fits : Fits limits state)
    (fl : state.blanks.val < limits.items.val) (hst : stOf s1 = (fresh c (stOf state)).2)
    (htr : s1.triples = state.triples) (hids : s1.ids = state.ids) : Fits limits s1 := by
  have hb := congrArg St.blanks hst
  simp only [stOf, fresh] at hb
  exact ⟨by rw [htr]; exact fits.1, by omega, by rw [hids]; exact fits.2.2⟩

theorem fits_of_stOf {limits : rdfxml.Limits} {s s' : rdfxml.State} (h : stOf s' = stOf s) (f : Fits limits s)
    (ht : s'.triples.val.length ≤ limits.items.val) : Fits limits s' := by
  have hb := congrArg St.blanks h
  have hi := congrArg (fun x => x.ids.length) h
  simp only [stOf, List.length_map] at hb hi
  exact ⟨ht, by rw [hb]; exact f.2.1, by rw [hi]; exact f.2.2⟩

mutual

theorem node_element_spec (c : Ctx) (e : xml.Element) (base : alloc.vec.Vec U8) (lang : alloc.vec.Vec U32)
    (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ag : Agrees c base lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.node_element e base lang scope limits state = .ok r ∧
      NodeSpec r state limits (fun t ts st' => NodeElement c e (stOf state) t ts st') := by
  rw [rdfxml.node_element]
  obtain ⟨r1, hr1, s1, c1⟩ := prepare_spec c e base lang limits ag.hbase ag.hlang ag.hterm ag.hfits ag.hsmall
  rw [hr1]; simp only [bind_ok]
  cases r1 with
  | Err err =>
    refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
    intro t ts st' h _ _ _
    obtain ⟨c', evs, u, pr, -⟩ := (nodeElement_iff ..).mp h
    obtain ⟨p, hp, -⟩ := c1 c' evs pr
    cases hp
  | Ok p =>
    obtain ⟨pr, pb⟩ := s1 p rfl
    obtain ⟨r2, hr2, s2, c2⟩ := element_uri_spec e limits
    rw [hr2]
    cases r2 with
    | Err err =>
      refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
      intro t ts st' h _ _ _
      obtain ⟨c', evs, u, -, eu, -⟩ := (nodeElement_iff ..).mp h
      obtain ⟨v, hv, -⟩ := c2 u (by rw [← ag.hterm]; exact eu)
      cases hv
    | Ok uri =>
      have eu : ElementUri c.termLimit e (word uri) := by rw [ag.hterm]; exact s2 uri rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      rw [node_uri_eq]
      simp only [bind_ok, decide_eq_true_eq]
      by_cases nu : NodeElementUri (word uri)
      · rw [if_pos nu]
        have hsize : sizeOf e < sizeOf e + 1 := Nat.lt_succ_self _
        obtain ⟨r, hr, sound, complete⟩ := node_body_spec (prepCtx c p) e p uri scope limits state
          (agrees_prep ag p pb) fits
        refine ⟨r, hr, fun s s' er => ?_, fun t ts st' h hl hb hi => ?_⟩
        · obtain ⟨ts, nb, hs, hf⟩ := sound s s' er
          exact ⟨ts, (nodeElement_iff ..).mpr ⟨_, _, _, pr, eu, nu, nb⟩, hs, hf⟩
        · obtain ⟨c', evs, u, pr2, eu2, nu2, nb⟩ := (nodeElement_iff ..).mp h
          obtain ⟨p2, hp2, hc2, he2⟩ := c1 c' evs pr2
          simp only [core.result.Result.Ok.injEq] at hp2
          subst hp2
          have hu : u = word uri := elementUri_unique eu2 eu
          subst hc2 he2 hu
          exact complete t ts st' nb hl hb hi
      · rw [if_neg nu]
        refine ⟨.Err .InvalidName, rfl, by simp, ?_⟩
        intro t ts st' h _ _ _
        obtain ⟨c', evs, u, -, eu2, nu2, -⟩ := (nodeElement_iff ..).mp h
        rw [elementUri_unique eu2 eu] at nu2
        exact (nu nu2).elim
termination_by (sizeOf e, 5, 0)
decreasing_by
  all_goals try simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals omega

theorem node_body_spec (c : Ctx) (e : xml.Element) (p : rdfxml.Prepared) (uri : alloc.vec.Vec U32)
    (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ag : Agrees c p.base p.lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.node_body e p uri scope limits state = .ok r ∧
      NodeSpec r state limits (fun t ts st' => NodeBody c (evsOf p.events) (word uri) e (stOf state) t ts st') := by
  rw [rdfxml.node_body, node_attributes_eq]
  simp only [bind_ok, decide_eq_true_eq]
  by_cases na : NodeAttributes (evsOf p.events)
  swap
  · rw [if_neg na]
    refine ⟨.Err .InvalidAttributes, rfl, by simp, ?_⟩
    rintro t ts st' ⟨na', -⟩ _ _ _; exact (na na').elim
  rw [if_pos na]
  obtain ⟨r1, hr1, s1, c1⟩ := subject_of_spec c p scope limits state ag fits
  rw [hr1]
  cases r1 with
  | Err err =>
    refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
    rintro t ts st' ⟨-, st1, ts1, ts2, ts3, so, -, -, pe, -⟩ _ hb hi
    have g := grows_propertyElts pe
    obtain ⟨_, _, he, -⟩ := c1 t st1 so (by have := g.1; omega) (by have := g.2; omega)
    cases he
  | Ok pair =>
    obtain ⟨subject, state1⟩ := pair
    obtain ⟨so, htr1, fits1⟩ := s1 subject state1 rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
    -- the derivation fixes the subject and the state after it
    have first : ∀ t st1, SubjectOf c (evsOf p.events) (stOf state) t st1 → st1.blanks ≤ limits.items.val →
        st1.ids.length ≤ limits.items.val → t = subjectTerm subject ∧ st1 = stOf state1 := by
      intro t st1 so2 hb hi
      obtain ⟨s', st1', he, ht', hst', -⟩ := c1 t st1 so2 hb hi
      simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨ht'.symm, hst'.symm⟩
    obtain ⟨r2, hr2, s2, c2⟩ := type_triple_spec c subject uri limits state1 ag.hterm fits1
    rw [hr2]
    cases r2 with
    | Err err =>
      refine ⟨.Err err, by simp [residual], by simp, ?_⟩
      rintro t ts st' ⟨-, st1, ts1, ts2, ts3, so2, tt, -, pe, rfl⟩ hl hb hi
      have g := grows_propertyElts pe
      obtain ⟨rfl, rfl⟩ := first t st1 so2 (by have := g.1; omega) (by have := g.2; omega)
      obtain ⟨_, he2, -⟩ := c2 ts1 (stOf state1) ⟨tt, rfl⟩
        (by rw [stmts_triples htr1]; simp at hl ⊢; omega) (by have := g.1; omega) (by have := g.2; omega)
      cases he2
    | Ok state2 =>
      obtain ⟨ts1, ⟨tt, hst2⟩, hs2, fits2⟩ := s2 state2 rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨r3, hr3, s3, c3⟩ := attribute_triples_spec c subject p.events 0#usize p.base p.lang scope limits
        state2 ag fits2
      rw [usize_zero_val, List.drop_zero] at s3 c3
      rw [hr3]
      cases r3 with
      | Err err =>
        refine ⟨.Err err, by simp [residual], by simp, ?_⟩
        rintro t ts st' ⟨-, st1, ts1', ts2, ts3, so2, tt2, pa, pe, rfl⟩ hl hb hi
        have g := grows_propertyElts pe
        obtain ⟨rfl, rfl⟩ := first t st1 so2 (by have := g.1; omega) (by have := g.2; omega)
        obtain ⟨s2', he2, hs2', -⟩ := c2 ts1' (stOf state1) ⟨tt2, rfl⟩
          (by rw [stmts_triples htr1]; simp at hl ⊢; omega) (by have := g.1; omega) (by have := g.2; omega)
        simp only [core.result.Result.Ok.injEq] at he2; subst he2
        have : ts1' = ts1 := by have := hs2'.symm.trans hs2; simpa using this
        subst this
        obtain ⟨_, he3, -⟩ := c3 ts2 (stOf state2) ⟨pa, rfl⟩
          (by rw [hs2, stmts_triples htr1]; simp at hl ⊢; omega) (by rw [hst2]; have := g.1; omega)
          (by rw [hst2]; have := g.2; omega)
        cases he3
      | Ok state3 =>
        obtain ⟨ts2, ⟨pa, hst3⟩, hs3, fits3⟩ := s3 state3 rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        have hsize := sizeOf_children_lt e
        obtain ⟨r4, hr4, s4, c4⟩ := property_elements_spec c e.children 0#usize subject p.base p.lang scope limits
          1#usize state3 ag fits3
        rw [usize_zero_val, List.drop_zero] at s4 c4
        rw [hr4]
        cases r4 with
        | Err err =>
          refine ⟨.Err err, by simp [residual], by simp, ?_⟩
          rintro t ts st' ⟨-, st1, ts1', ts2', ts3, so2, tt2, pa2, pe, rfl⟩ hl hb hi
          have g := grows_propertyElts pe
          obtain ⟨rfl, rfl⟩ := first t st1 so2 (by have := g.1; omega) (by have := g.2; omega)
          obtain ⟨s2', he2, hs2', -⟩ := c2 ts1' (stOf state1) ⟨tt2, rfl⟩
            (by rw [stmts_triples htr1]; simp at hl ⊢; omega) (by have := g.1; omega) (by have := g.2; omega)
          simp only [core.result.Result.Ok.injEq] at he2; subst he2
          have : ts1' = ts1 := by have := hs2'.symm.trans hs2; simpa using this
          subst this
          obtain ⟨s3', he3, hs3', -⟩ := c3 ts2' (stOf state2) ⟨pa2, rfl⟩
            (by rw [hs2, stmts_triples htr1]; simp at hl ⊢; omega) (by rw [hst2]; have := g.1; omega)
            (by rw [hst2]; have := g.2; omega)
          simp only [core.result.Result.Ok.injEq] at he3; subst he3
          have : ts2' = ts2 := by have := hs3'.symm.trans hs3; simpa using this
          subst this
          obtain ⟨_, he4, -⟩ := c4 ts3 st' (by rw [hst3, hst2]; exact pe)
            (by rw [hs3, hs2, stmts_triples htr1]; simpa [List.append_assoc] using hl) hb hi
          cases he4
        | Ok state4 =>
          obtain ⟨ts3, pe, hs4, fits4⟩ := s4 state4 rfl
          refine ⟨.Ok (subject, state4), by simp, fun s s' er => ?_, fun t ts st' h hl hb hi => ?_⟩
          · simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at er
            obtain ⟨rfl, rfl⟩ := er
            refine ⟨ts1 ++ ts2 ++ ts3, ⟨na, stOf state1, ts1, ts2, ts3, so, tt, pa, ?_, rfl⟩, ?_, fits4⟩
            · rw [hst3, hst2] at pe; exact pe
            · rw [hs4, hs3, hs2, stmts_triples htr1]; simp only [List.append_assoc]
          · obtain ⟨-, st1, ts1', ts2', ts3', so2, tt2, pa2, pe2, rfl⟩ := h
            have g := grows_propertyElts pe2
            obtain ⟨rfl, rfl⟩ := first t st1 so2 (by have := g.1; omega) (by have := g.2; omega)
            obtain ⟨s2', he2, hs2', -⟩ := c2 ts1' (stOf state1) ⟨tt2, rfl⟩
              (by rw [stmts_triples htr1]; simp at hl ⊢; omega) (by have := g.1; omega) (by have := g.2; omega)
            simp only [core.result.Result.Ok.injEq] at he2; subst he2
            have : ts1' = ts1 := by have := hs2'.symm.trans hs2; simpa using this
            subst this
            obtain ⟨s3', he3, hs3', -⟩ := c3 ts2' (stOf state2) ⟨pa2, rfl⟩
              (by rw [hs2, stmts_triples htr1]; simp at hl ⊢; omega) (by rw [hst2]; have := g.1; omega)
              (by rw [hst2]; have := g.2; omega)
            simp only [core.result.Result.Ok.injEq] at he3; subst he3
            have : ts2' = ts2 := by have := hs3'.symm.trans hs3; simpa using this
            subst this
            obtain ⟨s4', he4, hs4', hst4'⟩ := c4 ts3' st' (by rw [hst3, hst2]; exact pe2)
              (by rw [hs3, hs2, stmts_triples htr1]; simpa [List.append_assoc] using hl) hb hi
            simp only [core.result.Result.Ok.injEq] at he4; subst he4
            refine ⟨subject, state4, rfl, rfl, ?_, hst4'⟩
            rw [hs4', hs3, hs2, stmts_triples htr1]; simp only [List.append_assoc]
termination_by (sizeOf e, 4, 0)
decreasing_by
  all_goals try simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals omega

theorem property_elements_spec (c : Ctx) (children : alloc.vec.Vec xml.Node) (i : Usize) (subject : rdf.Subject)
    (base : alloc.vec.Vec U8) (lang : alloc.vec.Vec U32) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (li : Usize) (state : rdfxml.State) (ag : Agrees c base lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.property_elements children i subject base lang scope limits li state = .ok r ∧
      StateSpec r state limits (fun ts st' =>
        PropertyElts c (subjectTerm subject) (children.val.drop i.val) li.val (stOf state) ts st') := by
  rw [rdfxml.property_elements]
  by_cases lt : i.val < children.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len children) (by simpa using lt)
    have d : children.val.drop i.val = children.val[i.val] :: children.val.drop i1.val := by
      rw [hi1v, List.drop_eq_getElem_cons lt]
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq children i lt]
    rw [d]
    have mem : children.val[i.val] ∈ children.val := List.getElem_mem lt
    cases h : children.val[i.val] with
    | Element e =>
      rw [h] at mem
      have hsize := sizeOf_node_lt mem
      simp only
      obtain ⟨r1, hr1, s1, c1⟩ := property_element_spec c e subject base lang scope limits li state ag fits
      rw [hr1]
      cases r1 with
      | Err err =>
        refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
        intro ts st' hp hl hb hi
        rcases (propertyElts_cons_iff ..).mp hp with ⟨t, ht, -⟩ | ⟨e', li', st1, ts1, ts2, he, pe, pr, rfl⟩
        · cases ht
        · simp only [xml.Node.Element.injEq] at he; subst he
          have g := grows_propertyElts pr
          obtain ⟨_, _, he1, -⟩ := c1 li' ts1 st1 pe (by simp at hl ⊢; omega) (by have := g.1; omega)
            (by have := g.2; omega)
          cases he1
      | Ok pair =>
        obtain ⟨li1, state1⟩ := pair
        obtain ⟨ts1, pe, hs1, fits1⟩ := s1 li1 state1 rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair, hi1]
        obtain ⟨r2, hr2, s2, c2⟩ := property_elements_spec c children i1 subject base lang scope limits li1 state1
          ag fits1
        refine ⟨r2, hr2, fun s' e2 => ?_, fun ts st' hp hl hb hi => ?_⟩
        · obtain ⟨ts2, pr, hs2, fits2⟩ := s2 s' e2
          refine ⟨ts1 ++ ts2, (propertyElts_cons_iff ..).mpr (.inr ⟨e, li1.val, stOf state1, ts1, ts2, rfl, pe, pr, rfl⟩),
            by rw [hs2, hs1, List.append_assoc], fits2⟩
        · rcases (propertyElts_cons_iff ..).mp hp with ⟨t, ht, -⟩ | ⟨e', li', st1, ts1', ts2, he, pe2, pr, rfl⟩
          · cases ht
          · simp only [xml.Node.Element.injEq] at he; subst he
            have g := grows_propertyElts pr
            obtain ⟨n', s1', he1, hn', hs1', hst1'⟩ := c1 li' ts1' st1 pe2 (by simp at hl ⊢; omega)
              (by have := g.1; omega) (by have := g.2; omega)
            simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at he1
            obtain ⟨rfl, rfl⟩ := he1
            have : ts1' = ts1 := by have := hs1'.symm.trans hs1; simpa using this
            subst this
            rw [← hn', ← hst1'] at pr
            obtain ⟨s2', he2, hs2', hst2'⟩ := c2 ts2 st' pr (by rw [hs1]; simpa [List.append_assoc] using hl) hb hi
            exact ⟨s2', he2, by rw [hs2', hs1, List.append_assoc], hst2'⟩
    | Text text =>
      simp only [spaces_from_eq, usize_zero_val, List.drop_zero, bind_ok, decide_eq_true_eq]
      by_cases ws : Ws (word text)
      · rw [if_pos ws]; simp only [hi1, bind_ok]
        obtain ⟨r2, hr2, s2, c2⟩ := property_elements_spec c children i1 subject base lang scope limits li state
          ag fits
        refine ⟨r2, hr2, fun s' e2 => ?_, fun ts st' hp hl hb hi => ?_⟩
        · obtain ⟨ts, pr, hs, hf⟩ := s2 s' e2
          exact ⟨ts, (propertyElts_cons_iff ..).mpr (.inl ⟨text, rfl, ws, pr⟩), hs, hf⟩
        · rcases (propertyElts_cons_iff ..).mp hp with ⟨t, ht, -, pr⟩ | ⟨e', -, -, -, -, he, -⟩
          · exact c2 ts st' pr hl hb hi
          · cases he
      · rw [if_neg ws]
        refine ⟨.Err .InvalidContent, rfl, by simp, ?_⟩
        intro ts st' hp _ _ _
        rcases (propertyElts_cons_iff ..).mp hp with ⟨t, ht, w, -⟩ | ⟨e', -, -, -, -, he, -⟩
        · simp only [xml.Node.Text.injEq] at ht; subst ht; exact (ws w).elim
        · cases he
  · have e : children.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨.Ok state, by simp [UScalar.lt_equiv, lt], fun s' h => ?_, fun ts st' hp _ _ _ => ?_⟩
    · simp at h; subst h
      exact ⟨[], by rw [e]; exact (propertyElts_nil_iff ..).mpr ⟨rfl, rfl⟩, by simp, fits⟩
    · rw [e, propertyElts_nil_iff] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨state, rfl, by simp, rfl⟩
termination_by (sizeOf children, 3, children.val.length - i.val)
decreasing_by
  all_goals try simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals omega

theorem property_element_spec (c : Ctx) (e : xml.Element) (subject : rdf.Subject) (base : alloc.vec.Vec U8)
    (lang : alloc.vec.Vec U32) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (li : Usize)
    (state : rdfxml.State) (ag : Agrees c base lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.property_element e subject base lang scope limits li state = .ok r ∧
      LiSpec r state limits (fun n ts st' => PropertyElt c (subjectTerm subject) e li.val n (stOf state) ts st') := by
  rw [rdfxml.property_element]
  obtain ⟨r1, hr1, s1, c1⟩ := prepare_spec c e base lang limits ag.hbase ag.hlang ag.hterm ag.hfits ag.hsmall
  rw [hr1]
  cases r1 with
  | Err err =>
    refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
    intro n ts st' h _ _ _
    obtain ⟨c', evs, p, pr, -⟩ := (propertyElt_iff ..).mp h
    obtain ⟨q, hq, -⟩ := c1 c' evs pr
    cases hq
  | Ok q =>
    obtain ⟨pr, qb⟩ := s1 q rfl
    obtain ⟨r2, hr2, s2, c2⟩ := predicate_of_spec c e li limits ag.hterm ag.hitems
    rw [hr2]
    cases r2 with
    | Err err =>
      refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
      intro n ts st' h _ _ _
      obtain ⟨c', evs, p, -, pd, -⟩ := (propertyElt_iff ..).mp h
      obtain ⟨_, _, he, -⟩ := c2 p n pd
      cases he
    | Ok pair =>
      obtain ⟨predicate, li1⟩ := pair
      have pd := s2 predicate li1 rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
      have hsize : sizeOf e < sizeOf e + 1 := Nat.lt_succ_self _
      obtain ⟨r3, hr3, s3, c3⟩ := property_body_spec (prepCtx c q) e q subject predicate scope limits state
        (agrees_prep ag q qb) fits
      rw [hr3]
      cases r3 with
      | Err err =>
        refine ⟨.Err err, by simp [residual], by simp, ?_⟩
        intro n ts st' h hl hb hi
        obtain ⟨c', evs, p, pr2, pd2, body⟩ := (propertyElt_iff ..).mp h
        obtain ⟨q2, hq2, hc2, he2⟩ := c1 c' evs pr2
        simp only [core.result.Result.Ok.injEq] at hq2; subst hq2 hc2 he2
        obtain ⟨i2, n2, he3, hi2, hn2⟩ := c2 p n pd2
        simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at he3
        obtain ⟨rfl, rfl⟩ := he3
        rw [← hi2] at body
        obtain ⟨_, he4, -⟩ := c3 ts st' body hl hb hi
        cases he4
      | Ok state1 =>
        obtain ⟨ts, body, hs, fits1⟩ := s3 state1 rfl
        refine ⟨.Ok (li1, state1), by simp, fun n s' e1 => ?_, fun n ts' st' h hl hb hi => ?_⟩
        · simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at e1
          obtain ⟨rfl, rfl⟩ := e1
          exact ⟨ts, (propertyElt_iff ..).mpr ⟨_, _, _, pr, pd, body⟩, hs, fits1⟩
        · obtain ⟨c', evs, p, pr2, pd2, body2⟩ := (propertyElt_iff ..).mp h
          obtain ⟨q2, hq2, hc2, he2⟩ := c1 c' evs pr2
          simp only [core.result.Result.Ok.injEq] at hq2; subst hq2 hc2 he2
          obtain ⟨i2, n2, he3, hi2, hn2⟩ := c2 p n pd2
          simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at he3
          obtain ⟨rfl, rfl⟩ := he3
          rw [← hi2] at body2
          obtain ⟨s4, he4, hs4, hst4⟩ := c3 ts' st' body2 hl hb hi
          simp only [core.result.Result.Ok.injEq] at he4; subst he4
          exact ⟨li1, state1, rfl, hn2, hs4, hst4⟩
termination_by (sizeOf e, 2, 0)
decreasing_by
  all_goals try simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals omega

theorem property_body_spec (c : Ctx) (e : xml.Element) (p : rdfxml.Prepared) (subject : rdf.Subject)
    (predicate : rdf.RdfIri) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ag : Agrees c p.base p.lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.property_body e p subject predicate scope limits state = .ok r ∧
      StateSpec r state limits
        (PropBody c (evsOf p.events) e (subjectTerm subject) predicate.spelling.val (stOf state)) := by
  rw [rdfxml.property_body]
  obtain ⟨k, hk, hkv⟩ := production_eq e p
  rw [hk]; simp only [bind_ok]
  have hsize : sizeOf e < sizeOf e + 1 := Nat.lt_succ_self _
  split
  · have h0 : productionOf (evsOf p.events) e.children.val = 0 := by rw [← hkv]; rfl
    obtain ⟨r, hr, spec⟩ := parse_resource_spec c e p subject predicate scope limits state ag fits
    exact ⟨r, hr, (stateSpec_congr (prop_body_0 h0)).mpr spec⟩
  · have h1 : productionOf (evsOf p.events) e.children.val = 1 := by rw [← hkv]; rfl
    obtain ⟨r, hr, spec⟩ := parse_collection_spec c e p subject predicate scope limits state ag fits
    exact ⟨r, hr, (stateSpec_congr (prop_body_1 h1)).mpr spec⟩
  · have h2 : productionOf (evsOf p.events) e.children.val = 2 := by rw [← hkv]; rfl
    refine ⟨.Err .UnsupportedParseType, rfl, by simp, fun ts st' h _ _ _ => ?_⟩
    exact (prop_body_2 h2 ts st' h).elim
  · have h3 : productionOf (evsOf p.events) e.children.val = 3 := by rw [← hkv]; rfl
    obtain ⟨r, hr, spec⟩ := empty_property_spec c p subject predicate scope limits state ag fits
    exact ⟨r, hr, (stateSpec_congr (prop_body_3 h3)).mpr spec⟩
  · have h4 : productionOf (evsOf p.events) e.children.val = 4 := by rw [← hkv]; rfl
    obtain ⟨r, hr, spec⟩ := resource_property_spec c e p subject predicate scope limits state ag fits
    exact ⟨r, hr, (stateSpec_congr (prop_body_4 h4)).mpr spec⟩
  · next _ n0 n1 n2 n3 n4 =>
    have le := productionOf_le (evsOf p.events) e.children.val
    have h5 : productionOf (evsOf p.events) e.children.val = 5 := by
      rw [← hkv] at le ⊢
      have a0 : k.val ≠ 0 := fun h => n0 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      have a1 : k.val ≠ 1 := fun h => n1 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      have a2 : k.val ≠ 2 := fun h => n2 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      have a3 : k.val ≠ 3 := fun h => n3 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      have a4 : k.val ≠ 4 := fun h => n4 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      omega
    obtain ⟨r, hr, spec⟩ := literal_property_spec c e p subject predicate scope limits state ag fits
    exact ⟨r, hr, (stateSpec_congr (prop_body_5 h5)).mpr spec⟩
termination_by (sizeOf e, 1, 0)
decreasing_by
  all_goals try simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals omega

theorem resource_property_spec (c : Ctx) (e : xml.Element) (p : rdfxml.Prepared) (subject : rdf.Subject)
    (predicate : rdf.RdfIri) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ag : Agrees c p.base p.lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.resource_property e p subject predicate scope limits state = .ok r ∧
      StateSpec r state limits
        (ResourceEltBody c (evsOf p.events) e (subjectTerm subject) predicate.spelling.val (stOf state)) := by
  rw [rdfxml.resource_property, only_0]
  simp only [bind_ok, decide_eq_true_eq]
  by_cases o0 : Only (evsOf p.events) [rdfName "ID"]
  swap
  · rw [if_neg o0]
    refine ⟨.Err .InvalidAttributes, rfl, by simp, ?_⟩
    rintro ts st' ⟨o, -⟩ _ _ _; exact (o0 o).elim
  rw [if_pos o0]
  obtain ⟨r1, hr1, hc1⟩ := single_none e.children 0#usize
  rw [usize_zero_val, List.drop_zero] at hc1
  rw [hr1]
  cases r1 with
  | Err err =>
    refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
    rintro ts st' ⟨-, pre, n, post, sn, tsn, st1, ts2, ch, wp, wq, -⟩ _ _ _
    have bound : pre.length ≤ Usize.max := by
      have h1 := congrArg List.length ch; have h2 := e.children.property; simp at h1; omega
    obtain ⟨k, hk⟩ := usize_of pre.length bound
    have := (hc1 k).mpr ⟨pre, n, post, ch, wp, wq, by rw [hk]; simp⟩
    simp at this
  | Ok k =>
    obtain ⟨m, n, post, ch, wm, wpost, hk⟩ := (hc1 k).mp rfl
    simp only [usize_zero_val, Nat.zero_add] at hk
    have kin : k.val < e.children.val.length := by rw [ch]; simp; omega
    have getk : e.children.val[k.val]'kin = .Element n := by
      simp only [ch, hk]; simp
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, index_eq e.children k kin, getk]
    have mem : xml.Node.Element n ∈ e.children.val := by rw [ch]; simp
    have hsize := sizeOf_child_lt mem
    obtain ⟨r2, hr2, s2, c2⟩ := node_element_spec c n p.base p.lang scope limits state ag fits
    rw [hr2]
    have unique : ∀ pre n' post', e.children.val = pre ++ [.Element n'] ++ post' → AllWs pre → AllWs post' →
        n' = n := by
      intro pre n' post' ch2 w1 w2
      exact (one_element_unique pre m post' post n' n (ch2.symm.trans ch) w1 wm).2.1
    cases r2 with
    | Err err =>
      refine ⟨.Err err, by simp [residual], by simp, ?_⟩
      rintro ts st' ⟨-, pre, n', post', sn, tsn, st1, ts2, ch2, w1, w2, ne, sd, rfl⟩ hl hb hi
      have := unique pre n' post' ch2 w1 w2
      subst this
      have g := grows_stated sd
      obtain ⟨_, _, he, -⟩ := c2 sn tsn st1 ne (by simp at hl ⊢; omega) (by have := g.1; omega) (by have := g.2; omega)
      cases he
    | Ok pair =>
      obtain ⟨object, state1⟩ := pair
      obtain ⟨tsn, ne, hs1, fits1⟩ := s2 object state1 rfl
      simp only [uncurry_apply_pair, object_of_eq, bind_ok]
      obtain ⟨r3, hr3, s3, c3⟩ := stated_spec c subject predicate (asObject object) p scope limits state1 ag fits1
      refine ⟨r3, hr3, fun s' e3 => ?_, fun ts st' h hl hb hi => ?_⟩
      · obtain ⟨ts2, sd, hs', fits'⟩ := s3 s' e3
        refine ⟨tsn ++ ts2, ⟨o0, m, n, post, subjectTerm object, tsn, stOf state1, ts2, ch, wm, wpost, ne,
          by simpa [objectTerm_asObject] using sd, rfl⟩, by rw [hs', hs1, List.append_assoc], fits'⟩
      · obtain ⟨-, pre, n', post', sn, tsn', st1, ts2, ch2, w1, w2, ne2, sd, rfl⟩ := h
        have := unique pre n' post' ch2 w1 w2
        subst this
        have g := grows_stated sd
        obtain ⟨o2, s2', he, hsn, hs2', hst2'⟩ := c2 sn tsn' st1 ne2 (by simp at hl ⊢; omega)
          (by have := g.1; omega) (by have := g.2; omega)
        simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have : tsn' = tsn := by have := hs2'.symm.trans hs1; simpa using this
        subst this
        obtain ⟨s4, he4, hs4, hst4⟩ := c3 ts2 st' (by rw [hst2']; simpa [objectTerm_asObject, hsn] using sd)
          (by rw [hs1]; simpa [List.append_assoc] using hl) hb hi
        exact ⟨s4, he4, by rw [hs4, hs1, List.append_assoc], hst4⟩
termination_by (sizeOf e, 0, 0)
decreasing_by
  all_goals try simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals omega

theorem parse_resource_spec (c : Ctx) (e : xml.Element) (p : rdfxml.Prepared) (subject : rdf.Subject)
    (predicate : rdf.RdfIri) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ag : Agrees c p.base p.lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.parse_resource e p subject predicate scope limits state = .ok r ∧
      StateSpec r state limits
        (ParseResourceBody c (evsOf p.events) e (subjectTerm subject) predicate.spelling.val (stOf state)) := by
  rw [rdfxml.parse_resource, only_2]
  simp only [bind_ok, decide_eq_true_eq]
  by_cases o2 : Only (evsOf p.events) [rdfName "ID", rdfName "parseType"]
  swap
  · rw [if_neg o2]
    refine ⟨.Err .InvalidAttributes, rfl, by simp, ?_⟩
    rintro ts st' ⟨o, -⟩ _ _ _; exact (o2 o).elim
  rw [if_pos o2]
  by_cases fl : state.blanks.val < limits.items.val
  swap
  · rw [fresh_err scope limits state fl]
    refine ⟨.Err .ResourceLimit, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
    rintro ts st' ⟨-, ts1, st2, tsc, sd, pe, rfl⟩ _ hb _
    have g := grows_trans (grows_stated sd) (grows_propertyElts pe)
    simp only [Grows, fresh, stOf] at g
    omega
  obtain ⟨node, s1, hf, ht, hst, htr, hids⟩ := fresh_ok c scope limits state ag.hscope fl
  rw [hf]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair, object_of_eq]
  have fits1 : Fits limits s1 := fits_fresh fits fl hst htr hids
  have ho : objectTerm (asObject (.Blank node)) = (fresh c (stOf state)).1 := by rw [objectTerm_asObject, ht]
  obtain ⟨r2, hr2, s2, c2⟩ := stated_spec c subject predicate (asObject (.Blank node)) p scope limits s1 ag fits1
  rw [ho, hst] at s2 c2
  rw [stmts_triples htr] at s2 c2
  rw [hr2]
  cases r2 with
  | Err err =>
    refine ⟨.Err err, by simp [residual], by simp, ?_⟩
    rintro ts st' ⟨-, ts1, st2, tsc, sd, pe, rfl⟩ hl hb hi
    have g := grows_propertyElts pe
    obtain ⟨_, he, -⟩ := c2 ts1 st2 sd (by simp at hl ⊢; omega) (by have := g.1; omega) (by have := g.2; omega)
    cases he
  | Ok state2 =>
    obtain ⟨ts1, sd, hs2, fits2⟩ := s2 state2 rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have hsize := sizeOf_children_lt e
    obtain ⟨r3, hr3, s3, c3⟩ := property_elements_spec c e.children 0#usize (.Blank node) p.base p.lang scope limits
      1#usize state2 ag fits2
    rw [usize_zero_val, List.drop_zero, usize_one_val, ht] at s3 c3
    refine ⟨r3, hr3, fun s' e3 => ?_, fun ts st' h hl hb hi => ?_⟩
    · obtain ⟨tsc, pe, hs3, fits3⟩ := s3 s' e3
      exact ⟨ts1 ++ tsc, ⟨o2, ts1, stOf state2, tsc, sd, pe, rfl⟩, by rw [hs3, hs2, List.append_assoc], fits3⟩
    · obtain ⟨-, ts1', st2, tsc, sd2, pe, rfl⟩ := h
      have g := grows_propertyElts pe
      obtain ⟨s2', he, hs2', hst2'⟩ := c2 ts1' st2 sd2 (by simp at hl ⊢; omega) (by have := g.1; omega)
        (by have := g.2; omega)
      simp only [core.result.Result.Ok.injEq] at he
      subst he
      have : ts1' = ts1 := by have := hs2'.symm.trans hs2; simpa using this
      subst this
      obtain ⟨s4, he4, hs4, hst4⟩ := c3 tsc st' (by rw [hst2']; exact pe)
        (by rw [hs2]; simpa [List.append_assoc] using hl) hb hi
      exact ⟨s4, he4, by rw [hs4, hs2, List.append_assoc], hst4⟩
termination_by (sizeOf e, 0, 0)
decreasing_by
  all_goals try simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals omega

theorem parse_collection_spec (c : Ctx) (e : xml.Element) (p : rdfxml.Prepared) (subject : rdf.Subject)
    (predicate : rdf.RdfIri) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ag : Agrees c p.base p.lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.parse_collection e p subject predicate scope limits state = .ok r ∧
      StateSpec r state limits
        (CollectionBody c (evsOf p.events) e (subjectTerm subject) predicate.spelling.val (stOf state)) := by
  rw [rdfxml.parse_collection, only_2]
  simp only [bind_ok, decide_eq_true_eq]
  by_cases o2 : Only (evsOf p.events) [rdfName "ID", rdfName "parseType"]
  swap
  · rw [if_neg o2]
    refine ⟨.Err .InvalidAttributes, rfl, by simp, ?_⟩
    rintro ts st' ⟨o, -⟩ _ _ _; exact (o2 o).elim
  rw [if_pos o2]
  have hsize := sizeOf_children_lt e
  obtain ⟨r1, hr1, s1, c1⟩ := node_list_spec c e.children 0#usize p.base p.lang scope limits state ag fits
  rw [usize_zero_val, List.drop_zero] at s1 c1
  rw [hr1]
  cases r1 with
  | Err err =>
    refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
    rintro ts st' ⟨-, h, tsl, st1, ts2, nl, sd, rfl⟩ hl hb hi
    have g := grows_stated sd
    obtain ⟨_, _, he, -⟩ := c1 h tsl st1 nl (by simp at hl ⊢; omega) (by have := g.1; omega) (by have := g.2; omega)
    cases he
  | Ok pair =>
    obtain ⟨head, state1⟩ := pair
    obtain ⟨tsl, nl, hs1, fits1⟩ := s1 head state1 rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair, object_of_eq]
    obtain ⟨r2, hr2, s2, c2⟩ := stated_spec c subject predicate (asObject head) p scope limits state1 ag fits1
    refine ⟨r2, hr2, fun s' e2 => ?_, fun ts st' h hl hb hi => ?_⟩
    · obtain ⟨ts2, sd, hs', fits'⟩ := s2 s' e2
      refine ⟨tsl ++ ts2, ⟨o2, subjectTerm head, tsl, stOf state1, ts2, nl,
        by simpa [objectTerm_asObject] using sd, rfl⟩, by rw [hs', hs1, List.append_assoc], fits'⟩
    · obtain ⟨-, h', tsl', st1, ts2, nl2, sd, rfl⟩ := h
      have g := grows_stated sd
      obtain ⟨h2, s2', he, hh2, hs2', hst2'⟩ := c1 h' tsl' st1 nl2 (by simp at hl ⊢; omega)
        (by have := g.1; omega) (by have := g.2; omega)
      simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have : tsl' = tsl := by have := hs2'.symm.trans hs1; simpa using this
      subst this
      obtain ⟨s4, he4, hs4, hst4⟩ := c2 ts2 st' (by rw [hst2']; simpa [objectTerm_asObject, hh2] using sd)
        (by rw [hs1]; simpa [List.append_assoc] using hl) hb hi
      exact ⟨s4, he4, by rw [hs4, hs1, List.append_assoc], hst4⟩
termination_by (sizeOf e, 0, 0)
decreasing_by
  all_goals try simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals omega

theorem node_list_spec (c : Ctx) (children : alloc.vec.Vec xml.Node) (i : Usize) (base : alloc.vec.Vec U8)
    (lang : alloc.vec.Vec U32) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ag : Agrees c base lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.node_list children i base lang scope limits state = .ok r ∧
      NodeSpec r state limits (fun h ts st' => NodeList c (children.val.drop i.val) (stOf state) h ts st') := by
  rw [rdfxml.node_list]
  by_cases lt : i.val < children.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len children) (by simpa using lt)
    have d : children.val.drop i.val = children.val[i.val] :: children.val.drop i1.val := by
      rw [hi1v, List.drop_eq_getElem_cons lt]
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq children i lt]
    rw [d]
    have mem : children.val[i.val] ∈ children.val := List.getElem_mem lt
    cases h : children.val[i.val] with
    | Element f =>
      rw [h] at mem
      have hsize := sizeOf_node_lt mem
      simp only
      by_cases fl : state.blanks.val < limits.items.val
      swap
      · rw [fresh_err scope limits state fl]
        refine ⟨.Err .ResourceLimit, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
        intro hd ts st' hp _ hb _
        rcases (nodeList_cons_iff ..).mp hp with ⟨t, ht, -⟩ | ⟨f', sf, tsf, st2, hr, tsr, he, ne, nl, rfl, rfl⟩
        · cases ht
        · have g := grows_trans (grows_nodeElement ne) (grows_nodeList nl)
          simp only [Grows, fresh, stOf] at g
          omega
      obtain ⟨node, s1, hf, ht, hst, htr, hids⟩ := fresh_ok c scope limits state ag.hscope fl
      rw [hf]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
      have fits1 : Fits limits s1 := fits_fresh fits fl hst htr hids
      obtain ⟨r2, hr2, s2, c2⟩ := node_element_spec c f base lang scope limits s1 ag fits1
      rw [hst, stmts_triples htr] at s2 c2
      rw [hr2]
      cases r2 with
      | Err err =>
        refine ⟨.Err err, by simp [residual], by simp, ?_⟩
        intro hd ts st' hp hl hb hi
        rcases (nodeList_cons_iff ..).mp hp with ⟨t, ht', -⟩ | ⟨f', sf, tsf, st2, hr, tsr, he, ne, nl, rfl, rfl⟩
        · cases ht'
        · simp only [xml.Node.Element.injEq] at he; subst he
          have g := grows_nodeList nl
          obtain ⟨_, _, he2, -⟩ := c2 sf tsf st2 ne (by simp at hl ⊢; omega) (by have := g.1; omega)
            (by have := g.2; omega)
          cases he2
      | Ok pair =>
        obtain ⟨member, state2⟩ := pair
        obtain ⟨tsf, ne, hs2, fits2⟩ := s2 member state2 rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair, hi1]
        obtain ⟨r3, hr3, s3, c3⟩ := node_list_spec c children i1 base lang scope limits state2 ag fits2
        rw [hr3]
        -- the derivation fixes the member, its state and its triples
        have first : ∀ sf tsf' st2, NodeElement c f (fresh c (stOf state)).2 sf tsf' st2 →
            (stmts state ++ tsf').length ≤ limits.items.val → st2.blanks ≤ limits.items.val →
            st2.ids.length ≤ limits.items.val → sf = subjectTerm member ∧ tsf' = tsf ∧ st2 = stOf state2 := by
          intro sf tsf' st2 ne2 hl hb hi
          obtain ⟨m2, s2', he2, hm2, hs2', hst2'⟩ := c2 sf tsf' st2 ne2 hl hb hi
          simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at he2
          obtain ⟨rfl, rfl⟩ := he2
          exact ⟨hm2.symm, by have := hs2'.symm.trans hs2; simpa using this, hst2'.symm⟩
        cases r3 with
        | Err err =>
          refine ⟨.Err err, by simp [residual], by simp, ?_⟩
          intro hd ts st' hp hl hb hi
          rcases (nodeList_cons_iff ..).mp hp with ⟨t, ht', -⟩ | ⟨f', sf, tsf', st2, hr, tsr, he, ne2, nl, rfl, rfl⟩
          · cases ht'
          · simp only [xml.Node.Element.injEq] at he; subst he
            have g := grows_nodeList nl
            obtain ⟨-, rfl, rfl⟩ := first sf tsf' st2 ne2 (by simp at hl ⊢; omega) (by have := g.1; omega)
              (by have := g.2; omega)
            obtain ⟨_, _, he3, -⟩ := c3 hr tsr st' nl (by rw [hs2]; simp at hl ⊢; omega) hb hi
            cases he3
        | Ok pair3 =>
          obtain ⟨rest, state3⟩ := pair3
          obtain ⟨tsr, nl, hs3, fits3⟩ := s3 rest state3 rfl
          have key : ∀ hd ts st', NodeList c (xml.Node.Element f :: children.val.drop i1.val) (stOf state) hd ts st' →
              (stmts state ++ ts).length ≤ limits.items.val → st'.blanks ≤ limits.items.val →
              st'.ids.length ≤ limits.items.val →
              hd = (fresh c (stOf state)).1 ∧ st' = stOf state3 ∧
              ts = tsf ++ tsr ++ [⟨(fresh c (stOf state)).1, rdfBytes "first", subjectTerm member⟩,
                ⟨(fresh c (stOf state)).1, rdfBytes "rest", subjectTerm rest⟩] := by
            intro hd ts st' hp hl hb hi
            rcases (nodeList_cons_iff ..).mp hp with ⟨t, ht', -⟩ | ⟨f', sf, tsf', st2, hr, tsr', he, ne2, nl2, rfl, rfl⟩
            · cases ht'
            · simp only [xml.Node.Element.injEq] at he; subst he
              have g := grows_nodeList nl2
              obtain ⟨rfl, rfl, rfl⟩ := first sf tsf' st2 ne2 (by simp at hl ⊢; omega) (by have := g.1; omega)
                (by have := g.2; omega)
              obtain ⟨r', s3', he3, hr3', hs3', hst3'⟩ := c3 hr tsr' st' nl2 (by rw [hs2]; simp at hl ⊢; omega) hb hi
              simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at he3
              obtain ⟨rfl, rfl⟩ := he3
              have : tsr' = tsr := by have := hs3'.symm.trans hs3; simpa using this
              subst this
              exact ⟨rfl, hst3'.symm, by rw [hr3']⟩
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair, lift, object_of_eq,
            rdf_triple_eq]
          generalize hsa : Array.to_slice (Array.make 48#usize _ _) = sla
          generalize hsb : Array.to_slice (Array.make 47#usize _ _) = slb
          have sva : sla.val = rdfBytes "first" := by rw [← hsa, slice_val, rdfBytes_first]
          have svb : slb.val = rdfBytes "rest" := by rw [← hsb, slice_val, rdfBytes_rest]
          have hlen3 : state3.triples.val.length = (stmts state).length + tsf.length + tsr.length := by
            rw [← stmts_length, hs3, hs2]; simp only [List.length_append]
          by_cases room : state3.triples.val.length + 2 ≤ limits.items.val
          · obtain ⟨s4, h4, hs4, hl4, hv4⟩ := emit_ok state3
              ⟨.Blank node, ⟨alloc.vec.Vec.from sla.val sla.property⟩, asObject member⟩ limits (by omega)
            obtain ⟨s5, h5, hs5, hl5, hv5⟩ := emit_ok s4
              ⟨.Blank node, ⟨alloc.vec.Vec.from slb.val slb.property⟩, asObject rest⟩ limits (by omega)
            have stm : stmts s5 = stmts state ++ (tsf ++ tsr ++
                [⟨(fresh c (stOf state)).1, rdfBytes "first", subjectTerm member⟩,
                 ⟨(fresh c (stOf state)).1, rdfBytes "rest", subjectTerm rest⟩]) := by
              rw [hs5, hs4, hs3, hs2]
              simp [statementOf, objectTerm_asObject, sva, svb, ← ht]
            refine ⟨.Ok (.Blank node, s5), by simp [h4, h5], fun s s' e5 => ?_, fun hd ts st' hp hl hb hi => ?_⟩
            · simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at e5
              obtain ⟨rfl, rfl⟩ := e5
              refine ⟨_, (nodeList_cons_iff ..).mpr (.inr ⟨f, subjectTerm member, tsf, stOf state2, subjectTerm rest,
                tsr, rfl, ne, ?_, ht, rfl⟩), stm, fits_of_stOf (hv5.trans hv4) fits3 (by omega)⟩
              rw [hv5, hv4]; exact nl
            · obtain ⟨rfl, rfl, rfl⟩ := key hd ts st' hp hl hb hi
              exact ⟨.Blank node, s5, rfl, ht, stm, hv5.trans hv4⟩
          · refine ⟨.Err .ResourceLimit, ?_, by simp, fun hd ts st' hp hl hb hi => ?_⟩
            · by_cases a1 : state3.triples.val.length < limits.items.val
              · obtain ⟨s4, h4, hs4, hl4, hv4⟩ := emit_ok state3
                  ⟨.Blank node, ⟨alloc.vec.Vec.from sla.val sla.property⟩, asObject member⟩ limits a1
                simp [h4, emit_err s4 _ limits (by omega), residual]
              · simp [emit_err state3 _ limits a1, residual]
            · obtain ⟨rfl, rfl, rfl⟩ := key hd ts st' hp hl hb hi
              simp at hl
              omega
    | Text text =>
      simp only [spaces_from_eq, usize_zero_val, List.drop_zero, bind_ok, decide_eq_true_eq]
      by_cases ws : Ws (word text)
      · rw [if_pos ws]; simp only [hi1, bind_ok]
        obtain ⟨r2, hr2, s2, c2⟩ := node_list_spec c children i1 base lang scope limits state ag fits
        refine ⟨r2, hr2, fun s s' e2 => ?_, fun hd ts st' hp hl hb hi => ?_⟩
        · obtain ⟨ts, pr, hs, hf⟩ := s2 s s' e2
          exact ⟨ts, (nodeList_cons_iff ..).mpr (.inl ⟨text, rfl, ws, pr⟩), hs, hf⟩
        · rcases (nodeList_cons_iff ..).mp hp with ⟨t, ht, -, pr⟩ | ⟨f', -, -, -, -, -, he, -⟩
          · exact c2 hd ts st' pr hl hb hi
          · cases he
      · rw [if_neg ws]
        refine ⟨.Err .InvalidContent, rfl, by simp, ?_⟩
        intro hd ts st' hp _ _ _
        rcases (nodeList_cons_iff ..).mp hp with ⟨t, ht, w, -⟩ | ⟨f', -, -, -, -, -, he, -⟩
        · simp only [xml.Node.Text.injEq] at ht; subst ht; exact (ws w).elim
        · cases he
  · have e : children.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_false, lift, bind_ok, rdf_iri_val]
    generalize hs : Array.to_slice (Array.make 46#usize _ _) = sl
    have sv : sl.val = rdfBytes "nil" := by rw [← hs, slice_val, rdfBytes_nil]
    refine ⟨_, rfl, fun s s' h => ?_, fun hd ts st' hp _ _ _ => ?_⟩
    · simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[], ?_, by simp, fits⟩
      rw [e]
      exact (nodeList_nil_iff ..).mpr ⟨by simp [subjectTerm, sv], rfl, rfl⟩
    · rw [e, nodeList_nil_iff] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      exact ⟨_, state, rfl, by simp [subjectTerm, sv], by simp, rfl⟩
termination_by (sizeOf children, 3, children.val.length - i.val)
decreasing_by
  all_goals try simp_wf
  all_goals try simp only [Prod.lex_def]
  all_goals omega

end

end Rowl.RdfXmlNodes
