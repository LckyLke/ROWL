import Rowl.RdfXmlNodes
import Rowl.Xml

/-!
# The RDF/XML reader

`rdfxml::graph` computes exactly the triples that RDF 1.1 XML Syntax section 7
generates for an element tree (`RdfXmlGrammar.Graph`), and
`rdfxml::read_with_limits` exactly those of the element tree that
`XmlGrammar.Read` reads from the bytes: it returns a graph if and only if the
XML reader accepts the document and its element tree is RDF/XML within the
limits, and the graph is the one the grammar determines (`graph_unique`).
-/

namespace Rowl.RdfXml
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar Rowl.RdfXmlGrammar Rowl.RdfXmlSpell Rowl.RdfXmlTerms
open Rowl.RdfXmlEvents Rowl.RdfXmlProps Rowl.RdfXmlNodes
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ## Node element lists -/

theorem nodeElements_nil_iff (c : Ctx) (st : St) (ts : List Statement) (st' : St) :
    NodeElements c [] st ts st' ↔ ts = [] ∧ st' = st := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .nil

theorem nodeElements_cons_iff (c : Ctx) (x : xml.Node) (rest : List xml.Node) (st : St) (ts : List Statement)
    (st' : St) :
    NodeElements c (x :: rest) st ts st' ↔
      (∃ t, x = .Text t ∧ Ws (word t) ∧ NodeElements c rest st ts st') ∨
      (∃ n sn tsn st1 ts2, x = .Element n ∧ NodeElement c n st sn tsn st1 ∧ NodeElements c rest st1 ts2 st' ∧
        ts = tsn ++ ts2) := by
  constructor
  · intro h; cases h with
    | space w r => exact .inl ⟨_, rfl, w, r⟩
    | node ne r => exact .inr ⟨_, _, _, _, _, rfl, ne, r, rfl⟩
  · rintro (⟨t, rfl, w, r⟩ | ⟨n, sn, tsn, st1, ts2, rfl, ne, r, rfl⟩)
    · exact .space w r
    · exact .node ne r

theorem grows_nodeElements {c : Ctx} {nodes : List xml.Node} {st : St} {ts : List Statement} {st' : St}
    (h : NodeElements c nodes st ts st') : Grows st st' := by
  induction h with
  | nil => exact grows_refl _
  | space _ _ ih => exact ih
  | node ne _ ih => exact grows_trans (grows_nodeElement ne) ih

theorem node_elements_spec (c : Ctx) (children : alloc.vec.Vec xml.Node) (i : Usize) (base : alloc.vec.Vec U8)
    (lang : alloc.vec.Vec U32) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ag : Agrees c base lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.node_elements children i base lang scope limits state = .ok r ∧
      StateSpec r state limits (fun ts st' => NodeElements c (children.val.drop i.val) (stOf state) ts st') := by
  rw [rdfxml.node_elements]
  by_cases lt : i.val < children.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len children) (by simpa using lt)
    have d : children.val.drop i.val = children.val[i.val] :: children.val.drop i1.val := by
      rw [hi1v, List.drop_eq_getElem_cons lt]
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq children i lt]
    rw [d]
    cases h : children.val[i.val] with
    | Element n =>
      simp only
      obtain ⟨r1, hr1, s1, c1⟩ := node_element_spec c n base lang scope limits state ag fits
      rw [hr1]
      cases r1 with
      | Err err =>
        refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
        intro ts st' hp hl hb hi
        rcases (nodeElements_cons_iff ..).mp hp with ⟨t, ht, -⟩ | ⟨n', sn, tsn, st1, ts2, he, ne, nr, rfl⟩
        · cases ht
        · simp only [xml.Node.Element.injEq] at he; subst he
          have g := grows_nodeElements nr
          obtain ⟨_, _, he1, -⟩ := c1 sn tsn st1 ne (by simp at hl ⊢; omega) (by have := g.1; omega)
            (by have := g.2; omega)
          cases he1
      | Ok pair =>
        obtain ⟨subject, state1⟩ := pair
        obtain ⟨tsn, ne, hs1, fits1⟩ := s1 subject state1 rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair, hi1]
        obtain ⟨r2, hr2, s2, c2⟩ := node_elements_spec c children i1 base lang scope limits state1 ag fits1
        refine ⟨r2, hr2, fun s' e2 => ?_, fun ts st' hp hl hb hi => ?_⟩
        · obtain ⟨ts2, nr, hs2, fits2⟩ := s2 s' e2
          exact ⟨tsn ++ ts2, (nodeElements_cons_iff ..).mpr
            (.inr ⟨n, subjectTerm subject, tsn, stOf state1, ts2, rfl, ne, nr, rfl⟩),
            by rw [hs2, hs1, List.append_assoc], fits2⟩
        · rcases (nodeElements_cons_iff ..).mp hp with ⟨t, ht, -⟩ | ⟨n', sn, tsn', st1, ts2, he, ne2, nr, rfl⟩
          · cases ht
          · simp only [xml.Node.Element.injEq] at he; subst he
            have g := grows_nodeElements nr
            obtain ⟨s1', st1', he1, hsn, hs1', hst1'⟩ := c1 sn tsn' st1 ne2 (by simp at hl ⊢; omega)
              (by have := g.1; omega) (by have := g.2; omega)
            simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at he1
            obtain ⟨rfl, rfl⟩ := he1
            have : tsn' = tsn := by have := hs1'.symm.trans hs1; simpa using this
            subst this
            rw [← hst1'] at nr
            obtain ⟨s2', he2, hs2', hst2'⟩ := c2 ts2 st' nr (by rw [hs1]; simpa [List.append_assoc] using hl) hb hi
            exact ⟨s2', he2, by rw [hs2', hs1, List.append_assoc], hst2'⟩
    | Text text =>
      simp only [spaces_from_eq, usize_zero_val, List.drop_zero, bind_ok, decide_eq_true_eq]
      by_cases ws : Ws (word text)
      · rw [if_pos ws]; simp only [hi1, bind_ok]
        obtain ⟨r2, hr2, s2, c2⟩ := node_elements_spec c children i1 base lang scope limits state ag fits
        refine ⟨r2, hr2, fun s' e2 => ?_, fun ts st' hp hl hb hi => ?_⟩
        · obtain ⟨ts, nr, hs, hf⟩ := s2 s' e2
          exact ⟨ts, (nodeElements_cons_iff ..).mpr (.inl ⟨text, rfl, ws, nr⟩), hs, hf⟩
        · rcases (nodeElements_cons_iff ..).mp hp with ⟨t, ht, -, nr⟩ | ⟨n', -, -, -, -, he, -⟩
          · exact c2 ts st' nr hl hb hi
          · cases he
      · rw [if_neg ws]
        refine ⟨.Err .InvalidContent, rfl, by simp, ?_⟩
        intro ts st' hp _ _ _
        rcases (nodeElements_cons_iff ..).mp hp with ⟨t, ht, w, -⟩ | ⟨n', -, -, -, -, he, -⟩
        · simp only [xml.Node.Text.injEq] at ht; subst ht; exact (ws w).elim
        · cases he
  · have e : children.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨.Ok state, by simp [UScalar.lt_equiv, lt], fun s' h => ?_, fun ts st' hp _ _ _ => ?_⟩
    · simp at h; subst h
      exact ⟨[], by rw [e]; exact (nodeElements_nil_iff ..).mpr ⟨rfl, rfl⟩, by simp, fits⟩
    · rw [e, nodeElements_nil_iff] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨state, rfl, by simp, rfl⟩
termination_by children.val.length - i.val
decreasing_by all_goals omega

/-! ## The root element -/

theorem rdf_root_spec (c : Ctx) (e : xml.Element) (base scope : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (state : rdfxml.State) (ag : Agrees c base (alloc.vec.Vec.new U32) scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.rdf_root e base scope limits state = .ok r ∧
      StateSpec r state limits (fun ts st' =>
        ∃ c' evs, Prepared c e c' evs ∧ evs = [] ∧ NodeElements c' e.children.val (stOf state) ts st') := by
  rw [rdfxml.rdf_root]
  obtain ⟨r1, hr1, s1, c1⟩ := prepare_spec c e base (alloc.vec.Vec.new U32) limits ag.hbase ag.hlang ag.hterm
    ag.hfits ag.hsmall
  rw [hr1]
  cases r1 with
  | Err err =>
    refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
    rintro ts st' ⟨c', evs, pr, -⟩ _ _ _
    obtain ⟨p, hp, -⟩ := c1 c' evs pr
    cases hp
  | Ok p =>
    obtain ⟨pr, pb⟩ := s1 p rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    by_cases ev : evsOf p.events = []
    · have hz : alloc.vec.Vec.len p.events = 0#usize := by
        apply UScalar.eq_of_val_eq
        simp only [evsOf, List.map_eq_nil_iff] at ev
        simp [ev]
      rw [if_pos hz]
      obtain ⟨r2, hr2, s2, c2⟩ := node_elements_spec (prepCtx c p) e.children 0#usize p.base p.lang scope limits
        state (agrees_prep ag p pb) fits
      rw [usize_zero_val, List.drop_zero] at s2 c2
      refine ⟨r2, hr2, fun s' e2 => ?_, fun ts st' h hl hb hi => ?_⟩
      · obtain ⟨ts, ne, hs, hf⟩ := s2 s' e2
        exact ⟨ts, ⟨_, _, pr, ev, ne⟩, hs, hf⟩
      · obtain ⟨c', evs, pr2, rfl, ne⟩ := h
        obtain ⟨p2, hp2, hc2, -⟩ := c1 c' [] pr2
        simp only [core.result.Result.Ok.injEq] at hp2; subst hp2 hc2
        exact c2 ts st' ne hl hb hi
    · have hz : ¬ alloc.vec.Vec.len p.events = 0#usize := fun h => ev (by
        have := congrArg UScalar.val h
        simp only [alloc.vec.Vec.len_val, usize_zero_val, List.length_eq_zero_iff] at this
        simp [evsOf, this])
      rw [if_neg hz]
      refine ⟨.Err .InvalidAttributes, rfl, by simp, ?_⟩
      rintro ts st' ⟨c', evs, pr2, rfl, -⟩ _ _ _
      obtain ⟨p2, hp2, -, he2⟩ := c1 c' [] pr2
      simp only [core.result.Result.Ok.injEq] at hp2; subst hp2
      exact (ev he2).elim

/-! ## The graph of an element tree -/

/-- The statements of the triples of a raw graph. -/
def graphStatements (g : rdf.RawGraph) : List Statement := g.triples.val.map statementOf

theorem rdf_not_node {c : Ctx} {e : xml.Element} {st : St} {s : Term} {ts : List Statement} {st' : St}
    (eu : ElementUri c.termLimit e (rdfName "RDF")) (h : NodeElement c e st s ts st') : False := by
  obtain ⟨c', evs, u, -, eu2, nu, -⟩ := (nodeElement_iff ..).mp h
  rw [elementUri_unique eu2 eu] at nu
  exact not_node_of_core ((core_mem _).mpr (.inl rfl)) nu

/-- The state before the root element. -/
def initial : rdfxml.State := ⟨alloc.vec.Vec.new rdf.Triple, 0#usize, alloc.vec.Vec.new rdfxml.Id⟩

theorem initial_fits (limits : rdfxml.Limits) : Fits limits initial := by simp [Fits, initial]

theorem stOf_initial : stOf initial = ⟨0, []⟩ := by simp [stOf, initial]

theorem stmts_initial : stmts initial = [] := by simp [stmts, initial]

theorem graph_correct (root : xml.Element) (base scope : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (small : limits.term_bytes.val < Usize.max / 8) (pos : 0 < limits.term_bytes.val) :
    ∃ r, rdfxml.graph root base scope limits = .ok r ∧
      (∀ g, r = .Ok g →
        Graph base.val scope.val limits.term_bytes.val limits.items.val root (graphStatements g)) ∧
      (∀ ts, Graph base.val scope.val limits.term_bytes.val limits.items.val root ts →
        ∃ g, r = .Ok g ∧ graphStatements g = ts) := by
  rw [rdfxml.graph]
  by_cases hb : base.val.length ≤ limits.term_bytes.val
  swap
  · have hle : ¬ alloc.vec.Vec.len base ≤ limits.term_bytes := by simpa [UScalar.le_equiv] using hb
    refine ⟨.Err .ResourceLimit, by simp [hle], by simp, ?_⟩
    rintro ts ⟨hb', -⟩
    exact (hb hb').elim
  have hle : alloc.vec.Vec.len base ≤ limits.term_bytes := by simpa [UScalar.le_equiv] using hb
  simp only [hle, ite_true, bind_ok]
  have ag : Agrees ⟨base.val, [], scope.val, limits.term_bytes.val, limits.items.val⟩ base
      (alloc.vec.Vec.new U32) scope limits :=
    ⟨rfl, by simp [word_new], rfl, rfl, rfl, hb, small, pos⟩
  have init : (⟨alloc.vec.Vec.new rdf.Triple, 0#usize, alloc.vec.Vec.new rdfxml.Id⟩ : rdfxml.State) = initial := rfl
  obtain ⟨r1, hr1, s1, c1⟩ := element_uri_spec root limits
  rw [hr1]
  cases r1 with
  | Err err =>
    refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
    rintro ts ⟨-, st, doc, -⟩
    cases doc with
    | rdf pr ev eu ne =>
      obtain ⟨v, hv, -⟩ := c1 _ eu
      cases hv
    | node ne =>
      obtain ⟨c', evs, u, -, eu, -⟩ := (nodeElement_iff ..).mp ne
      obtain ⟨v, hv, -⟩ := c1 u eu
      cases hv
  | Ok uri =>
    have eu : ElementUri limits.term_bytes.val root (word uri) := s1 uri rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, is_rdf_RDF, decide_eq_true_eq, init]
    by_cases isr : word uri = rdfName "RDF"
    · rw [if_pos isr]
      rw [isr] at eu
      obtain ⟨r2, hr2, s2, c2⟩ := rdf_root_spec _ root base scope limits initial ag (initial_fits limits)
      simp only [stOf_initial, stmts_initial, List.nil_append] at s2 c2
      rw [hr2]
      cases r2 with
      | Err err =>
        refine ⟨.Err err, by simp [residual], by simp, ?_⟩
        rintro ts ⟨-, st, doc, hl, hb2, hi⟩
        cases doc with
        | rdf pr ev eu2 ne =>
          obtain ⟨_, he, -⟩ := c2 ts st ⟨_, _, pr, ev, ne⟩ hl hb2 hi
          cases he
        | node ne => exact (rdf_not_node eu ne).elim
      | Ok s' =>
        obtain ⟨ts, ⟨c', evs, pr, ev, ne⟩, hs, hf⟩ := s2 s' rfl
        refine ⟨.Ok ⟨s'.triples⟩, by simp, fun g hg => ?_, fun ts' h => ?_⟩
        · simp only [core.result.Result.Ok.injEq] at hg; subst hg
          have : graphStatements ⟨s'.triples⟩ = ts := hs
          rw [this]
          refine ⟨hb, stOf s', .rdf pr ev eu ne, ?_, hf.2.1, by rw [stOf_ids_length]; exact hf.2.2⟩
          rw [← hs, stmts_length]; exact hf.1
        · obtain ⟨-, st, doc, hl, hb2, hi⟩ := h
          cases doc with
          | rdf pr2 ev2 eu2 ne2 =>
            obtain ⟨s'', he, hs'', -⟩ := c2 ts' st ⟨_, _, pr2, ev2, ne2⟩ hl hb2 hi
            simp only [core.result.Result.Ok.injEq] at he; subst he
            exact ⟨_, rfl, hs''⟩
          | node ne2 => exact (rdf_not_node eu ne2).elim
    · rw [if_neg isr]
      obtain ⟨r2, hr2, s2, c2⟩ := node_element_spec _ root base (alloc.vec.Vec.new U32) scope limits initial ag
        (initial_fits limits)
      simp only [stOf_initial, stmts_initial, List.nil_append] at s2 c2
      rw [hr2]
      have notRdf : ∀ c' evs ts st', ¬ (Prepared ⟨base.val, [], scope.val, limits.term_bytes.val,
          limits.items.val⟩ root c' evs ∧ evs = [] ∧
          ElementUri limits.term_bytes.val root (rdfName "RDF") ∧ NodeElements c' root.children.val ⟨0, []⟩ ts st') :=
        fun c' evs ts st' ⟨_, _, eu2, _⟩ => isr (elementUri_unique eu eu2)
      cases r2 with
      | Err err =>
        refine ⟨.Err err, by simp [residual], by simp, ?_⟩
        rintro ts ⟨-, st, doc, hl, hb2, hi⟩
        cases doc with
        | rdf pr ev eu2 ne => exact (notRdf _ _ _ _ ⟨pr, ev, eu2, ne⟩).elim
        | node ne =>
          obtain ⟨_, _, he, -⟩ := c2 _ ts st ne hl hb2 hi
          cases he
      | Ok pair =>
        obtain ⟨subject, s'⟩ := pair
        obtain ⟨ts, ne, hs, hf⟩ := s2 subject s' rfl
        refine ⟨.Ok ⟨s'.triples⟩, by simp, fun g hg => ?_, fun ts' h => ?_⟩
        · simp only [core.result.Result.Ok.injEq] at hg; subst hg
          have : graphStatements ⟨s'.triples⟩ = ts := hs
          rw [this]
          refine ⟨hb, stOf s', .node ne, ?_, hf.2.1, by rw [stOf_ids_length]; exact hf.2.2⟩
          rw [← hs, stmts_length]; exact hf.1
        · obtain ⟨-, st, doc, hl, hb2, hi⟩ := h
          cases doc with
          | rdf pr ev eu2 ne2 => exact (notRdf _ _ _ _ ⟨pr, ev, eu2, ne2⟩).elim
          | node ne2 =>
            obtain ⟨s2', s'', he, -, hs'', -⟩ := c2 _ ts' st ne2 hl hb2 hi
            simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact ⟨_, rfl, hs''⟩

/-- The RDF/XML grammar determines the triples of an element tree. -/
theorem graph_unique (root : xml.Element) (base scope : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (small : limits.term_bytes.val < Usize.max / 8) (pos : 0 < limits.term_bytes.val) {ts1 ts2 : List Statement}
    (h1 : Graph base.val scope.val limits.term_bytes.val limits.items.val root ts1)
    (h2 : Graph base.val scope.val limits.term_bytes.val limits.items.val root ts2) : ts1 = ts2 := by
  obtain ⟨r, -, -, complete⟩ := graph_correct root base scope limits small pos
  obtain ⟨g1, e1, s1⟩ := complete ts1 h1
  obtain ⟨g2, e2, s2⟩ := complete ts2 h2
  rw [e1] at e2
  simp only [core.result.Result.Ok.injEq] at e2
  rw [← s1, ← s2, e2]

/-! ## Reading documents -/

theorem read_total (bytes base scope : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (small : limits.term_bytes.val < Usize.max / 8) (pos : 0 < limits.term_bytes.val) :
    ∃ r, rdfxml.read_with_limits bytes base scope limits = .ok r := by
  unfold rdfxml.read_with_limits
  obtain ⟨rr, hrr⟩ := Rowl.Xml.read_total bytes ⟨limits.expansion⟩
  rw [hrr]
  cases rr with
  | Error e => simp only [bind_ok]; exact ⟨_, rfl⟩
  | Document d =>
    obtain ⟨r, hr, -⟩ := graph_correct d.root base scope limits small pos
    simp only [bind_ok, hr]
    cases r <;> exact ⟨_, rfl⟩

/-- When the byte length plus the expansion budget fits in `usize` and the
    term limit is positive and below `usize::MAX / 8`, the reader returns a
    graph exactly for the documents that `XmlGrammar.Read` accepts and whose
    element tree has a graph within the limits, and that graph has the triples
    the grammar determines; it reports an XML error exactly for the documents
    that `XmlGrammar.Read` does not accept, and an RDF/XML error exactly for the
    accepted documents whose element tree has no graph within the limits. -/
theorem read_correct (bytes base scope : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (room : bytes.val.length + limits.expansion.val ≤ Usize.max)
    (small : limits.term_bytes.val < Usize.max / 8) (pos : 0 < limits.term_bytes.val) :
    (∀ g, rdfxml.read_with_limits bytes base scope limits = .ok (.Graph g) →
      ∃ root, Read bytes.val limits.expansion.val root ∧
        Graph base.val scope.val limits.term_bytes.val limits.items.val root (graphStatements g)) ∧
    (∀ root ts, Read bytes.val limits.expansion.val root →
      Graph base.val scope.val limits.term_bytes.val limits.items.val root ts →
      ∃ g, rdfxml.read_with_limits bytes base scope limits = .ok (.Graph g) ∧ graphStatements g = ts) ∧
    ((∃ e, rdfxml.read_with_limits bytes base scope limits = .ok (.XmlError e)) ↔
      ∀ root, ¬ Read bytes.val limits.expansion.val root) ∧
    ((∃ k, rdfxml.read_with_limits bytes base scope limits = .ok (.Error k)) ↔
      ∃ root, Read bytes.val limits.expansion.val root ∧
        ∀ ts, ¬ Graph base.val scope.val limits.term_bytes.val limits.items.val root ts) := by
  have xroom : bytes.val.length + (xml.Limits.mk limits.expansion).expansion.val ≤ Usize.max := room
  unfold rdfxml.read_with_limits
  obtain ⟨rr, hrr⟩ := Rowl.Xml.read_total bytes ⟨limits.expansion⟩
  rw [hrr]
  cases rr with
  | Error e =>
    have none : ∀ root, ¬ Read bytes.val limits.expansion.val root := fun root hr => by
      have := Rowl.Xml.read_complete bytes ⟨limits.expansion⟩ hr xroom
      rw [hrr] at this
      cases Result.ok_injective this
    simp only [bind_ok]
    refine ⟨fun g hg => (by cases Result.ok_injective hg), fun root ts hr _ => (none root hr).elim,
      ⟨fun _ => none, fun _ => ⟨e, rfl⟩⟩, ⟨fun ⟨k, hk⟩ => (by cases Result.ok_injective hk), ?_⟩⟩
    rintro ⟨root, hr, -⟩
    exact (none root hr).elim
  | Document d =>
    have hd : Read bytes.val limits.expansion.val d.root := Rowl.Xml.read_sound bytes ⟨limits.expansion⟩ hrr
    have uniq : ∀ root, Read bytes.val limits.expansion.val root → root = d.root := fun root hr =>
      Rowl.Xml.read_unique bytes ⟨limits.expansion⟩ hr hd xroom
    obtain ⟨r, hr, sound, complete⟩ := graph_correct d.root base scope limits small pos
    simp only [bind_ok, hr]
    have notXml : ¬ ∀ root, ¬ Read bytes.val limits.expansion.val root := fun h => h d.root hd
    cases r with
    | Ok g =>
      refine ⟨fun g' hg => ?_, fun root ts hroot hg => ?_, ⟨fun ⟨e, he⟩ => (by cases Result.ok_injective he),
        fun h => (notXml h).elim⟩, ⟨fun ⟨k, hk⟩ => (by cases Result.ok_injective hk), ?_⟩⟩
      · have e1 := Result.ok_injective hg
        injection e1 with e2
        subst e2
        exact ⟨d.root, hd, sound g rfl⟩
      · rw [uniq root hroot] at hg
        obtain ⟨g', he, hs⟩ := complete ts hg
        simp only [core.result.Result.Ok.injEq] at he; subst he
        exact ⟨g, rfl, hs⟩
      · rintro ⟨root, hroot, hno⟩
        rw [uniq root hroot] at hno
        exact (hno _ (sound g rfl)).elim
    | Err k =>
      refine ⟨fun g' hg => (by cases Result.ok_injective hg), fun root ts hroot hg => ?_,
        ⟨fun ⟨e, he⟩ => (by cases Result.ok_injective he), fun h => (notXml h).elim⟩,
        ⟨fun _ => ⟨d.root, hd, fun ts hg => ?_⟩, fun _ => ⟨k, rfl⟩⟩⟩
      · rw [uniq root hroot] at hg
        obtain ⟨g', he, -⟩ := complete ts hg
        cases he
      · obtain ⟨g', he, -⟩ := complete ts hg
        cases he

end Rowl.RdfXml
