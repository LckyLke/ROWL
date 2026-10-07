import Rowl.RdfXmlEvents

/-!
# Subjects, objects and statements

Correctness of the functions of `rdfxml.rs` that compute subjects, the
objects of empty and literal property elements, statements with their
reification, and the triples of property attributes.
-/

namespace Rowl.RdfXmlProps
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar Rowl.RdfXmlGrammar Rowl.RdfXmlSpell Rowl.RdfXmlTerms
open Rowl.RdfXmlEvents
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-- A specification context agrees with the reader's base IRI, language, blank
    node scope and limits. -/
structure Agrees (c : Ctx) (base : alloc.vec.Vec U8) (lang : alloc.vec.Vec U32) (scope : alloc.vec.Vec U8)
    (limits : rdfxml.Limits) : Prop where
  hbase : c.base = base.val
  hlang : c.lang = word lang
  hscope : c.scope = scope.val
  hterm : c.termLimit = limits.term_bytes.val
  hitems : c.itemLimit = limits.items.val
  hfits : base.val.length ≤ limits.term_bytes.val
  hsmall : limits.term_bytes.val < Usize.max / 8
  hpos : 0 < limits.term_bytes.val

/-- The counts of a state are within the item limit. -/
def Fits (limits : rdfxml.Limits) (s : rdfxml.State) : Prop :=
  s.triples.val.length ≤ limits.items.val ∧ s.blanks.val ≤ limits.items.val ∧ s.ids.val.length ≤ limits.items.val

theorem stOf_ids_length (s : rdfxml.State) : (stOf s).ids.length = s.ids.val.length := by simp [stOf]

theorem stmts_length (s : rdfxml.State) : (stmts s).length = s.triples.val.length := by simp [stmts]

/-! ## Subjects of node elements -/

theorem subjectOf_iff (c : Ctx) (evs : List (Word × Word)) (st : St) (t : Term) (st' : St) :
    SubjectOf c evs st t st' ↔
      (∃ v i, attrValue (rdfName "ID") evs = some v ∧ IdIri c v st i st' ∧ t = .iri i) ∨
      (∃ v, attrValue (rdfName "ID") evs = none ∧ attrValue (rdfName "nodeID") evs = some v ∧ NodeIdOf c v t ∧
        st' = st) ∨
      (∃ v i, attrValue (rdfName "ID") evs = none ∧ attrValue (rdfName "nodeID") evs = none ∧
        attrValue (rdfName "about") evs = some v ∧ Resolved c v i ∧ t = .iri i ∧ st' = st) ∨
      (attrValue (rdfName "ID") evs = none ∧ attrValue (rdfName "nodeID") evs = none ∧
        attrValue (rdfName "about") evs = none ∧ t = (fresh c st).1 ∧ st' = (fresh c st).2) := by
  constructor
  · intro h; cases h with
    | id a i => exact .inl ⟨_, _, a, i, rfl⟩
    | nodeId a b n => exact .inr (.inl ⟨_, a, b, n, rfl⟩)
    | about a b d r => exact .inr (.inr (.inl ⟨_, _, a, b, d, r, rfl, rfl⟩))
    | fresh a b d => exact .inr (.inr (.inr ⟨a, b, d, rfl, rfl⟩))
  · rintro (⟨v, i, a, i', rfl⟩ | ⟨v, a, b, n, rfl⟩ | ⟨v, i, a, b, d, r, rfl, rfl⟩ | ⟨a, b, d, rfl, rfl⟩)
    · exact .id a i'
    · exact .nodeId a b n
    · exact .about a b d r
    · exact .fresh a b d

theorem class_names_ID : ∀ u, classOf u = (1#u8 : U8).val ↔ u = rdfName "ID" := fun u => by
  simpa using classOf_ID u
theorem class_names_nodeID : ∀ u, classOf u = (2#u8 : U8).val ↔ u = rdfName "nodeID" := fun u => by
  simpa using classOf_nodeID u
theorem class_names_about : ∀ u, classOf u = (3#u8 : U8).val ↔ u = rdfName "about" := fun u => by
  simpa using classOf_about u
theorem class_names_resource : ∀ u, classOf u = (4#u8 : U8).val ↔ u = rdfName "resource" := fun u => by
  simpa using classOf_resource u
theorem class_names_parseType : ∀ u, classOf u = (5#u8 : U8).val ↔ u = rdfName "parseType" := fun u => by
  simpa using classOf_parseType u
theorem class_names_datatype : ∀ u, classOf u = (6#u8 : U8).val ↔ u = rdfName "datatype" := fun u => by
  simpa using classOf_datatype u

/-- The value of the event with class `k` of the prepared element. -/
theorem find_value (p : rdfxml.Prepared) (k : U8) (nm : Word) (hk : ∀ u, classOf u = k.val ↔ u = nm) :
    ∃ o, rdfxml.find_class p.events k 0#usize = .ok o ∧
      (o = none → attrValue nm (evsOf p.events) = none) ∧
      (∀ j, o = some j → ∃ h : j.val < p.events.val.length,
        attrValue nm (evsOf p.events) = some (word (p.events.val[j.val]).value)) := by
  obtain ⟨o, ho, n, s⟩ := find_class_lookup p.events k nm hk 0#usize
  rw [usize_zero_val, List.drop_zero] at n s
  exact ⟨o, ho, n, s⟩

/-- What a function returning a subject and a state computes: exactly the
    terms and states related by `R`, within the limits. -/
def SubjSpec (r : core.result.Result (rdf.Subject × rdfxml.State) rdfxml.ErrorKind) (state : rdfxml.State)
    (limits : rdfxml.Limits) (R : Term → St → Prop) : Prop :=
  (∀ s s', r = .Ok (s, s') → R (subjectTerm s) (stOf s') ∧ s'.triples = state.triples ∧ Fits limits s') ∧
  (∀ t st', R t st' → st'.blanks ≤ limits.items.val → st'.ids.length ≤ limits.items.val →
    ∃ s s', r = .Ok (s, s') ∧ subjectTerm s = t ∧ stOf s' = st' ∧ s'.triples = state.triples)

theorem fresh_spec (c : Ctx) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (hs : c.scope = scope.val) (fits : Fits limits state) :
    ∃ r, (do
        let r ← rdfxml.fresh scope limits state
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let (node, state1) := val
          Result.ok (core.result.Result.Ok (rdf.Subject.Blank node, state1))
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (rdf.Subject × rdfxml.State) (core.convert.FromSame rdfxml.ErrorKind) residual) = .ok r ∧
      SubjSpec r state limits (fun t st' => t = (fresh c (stOf state)).1 ∧ st' = (fresh c (stOf state)).2) := by
  by_cases lt : state.blanks.val < limits.items.val
  · obtain ⟨n, s', h, ht, hst, htr, hids⟩ := fresh_ok c scope limits state hs lt
    refine ⟨.Ok (.Blank n, s'), by simp [h, core.result.Result.Insts.CoreOpsTry.branch], ?_, ?_⟩
    · intro s s2 e
      simp at e; obtain ⟨rfl, rfl⟩ := e
      refine ⟨⟨ht, hst⟩, htr, ?_⟩
      have hb : s'.blanks.val = state.blanks.val + 1 := by
        have := congrArg St.blanks hst; simpa [stOf, fresh] using this
      refine ⟨by rw [htr]; exact fits.1, by omega, by rw [hids]; exact fits.2.2⟩
    · rintro t st' ⟨rfl, rfl⟩ _ _
      exact ⟨_, _, rfl, ht, hst, htr⟩
  · refine ⟨.Err .ResourceLimit, by simp [fresh_err scope limits state lt, core.result.Result.Insts.CoreOpsTry.branch,
      residual], by simp, ?_⟩
    rintro t st' ⟨-, rfl⟩ hb _
    simp [fresh, stOf] at hb
    omega

theorem subject_about_spec (c : Ctx) (p : rdfxml.Prepared) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (state : rdfxml.State) (ag : Agrees c p.base p.lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.subject_about p scope limits state = .ok r ∧
      SubjSpec r state limits (fun t st' =>
        (∃ v i, attrValue (rdfName "about") (evsOf p.events) = some v ∧ Resolved c v i ∧ t = .iri i ∧
          st' = stOf state) ∨
        (attrValue (rdfName "about") (evsOf p.events) = none ∧ t = (fresh c (stOf state)).1 ∧
          st' = (fresh c (stOf state)).2)) := by
  unfold rdfxml.subject_about
  obtain ⟨o, ho, n, sm⟩ := find_value p 3#u8 _ class_names_about
  rw [ho]; simp only [bind_ok]
  cases o with
  | none =>
    have hv := n rfl
    obtain ⟨r, hr, sound, complete⟩ := fresh_spec c scope limits state ag.hscope fits
    refine ⟨r, hr, fun s s' e => ?_, fun t st' h hb hi => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := sound s s' e
      exact ⟨.inr ⟨hv, h1⟩, h2, h3⟩
    · rcases h with ⟨v, i, e, -⟩ | ⟨-, h⟩
      · rw [hv] at e; cases e
      · exact complete t st' h hb hi
  | some k =>
    obtain ⟨kin, hv⟩ := sm k rfl
    simp only [index_eq p.events k kin, bind_ok]
    obtain ⟨r, hr, hc⟩ := resolved_eq c p.base (p.events.val[k.val]).value limits ag.hbase ag.hterm ag.hfits ag.hsmall
    rw [hr]; simp only [bind_ok]
    cases r with
    | Err e =>
      refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
      rintro t st' (⟨v, i, e1, rs, -, -⟩ | ⟨e1, -⟩) _ _
      · rw [hv] at e1; simp only [Option.some.injEq] at e1; subst e1
        have bound : i.length ≤ Usize.max := by
          have := rs.1; obtain ⟨_, _, _, _, l⟩ := this
          have := Rowl.XmlScan.usize_le_max limits.term_bytes; rw [ag.hterm] at l; omega
        have := (hc ⟨alloc.vec.Vec.from i bound⟩).mpr (by simpa using rs)
        simp at this
      · rw [hv] at e1; cases e1
    | Ok iri =>
      have rs := (hc iri).mp rfl
      refine ⟨.Ok (.Iri iri, state), by simp [core.result.Result.Insts.CoreOpsTry.branch], ?_, ?_⟩
      · intro s s' e
        simp at e; obtain ⟨rfl, rfl⟩ := e
        exact ⟨.inl ⟨_, _, hv, rs, rfl, rfl⟩, rfl, fits⟩
      · rintro t st' (⟨v, i, e1, rs2, rfl, rfl⟩ | ⟨e1, -⟩) _ _
        · rw [hv] at e1; simp only [Option.some.injEq] at e1; subst e1
          have : iri.spelling.val = i := by
            have h1 := rs.1; have h2 := rs2.1
            obtain ⟨r1, sp1, -, res1, -⟩ := h1
            obtain ⟨r2, sp2, -, res2, -⟩ := h2
            rw [spelled_unique sp1 sp2] at res1
            exact bytes_word_inj (Option.some.inj (res1.symm.trans res2))
          exact ⟨_, _, rfl, by simp [subjectTerm, this], rfl, rfl⟩
        · rw [hv] at e1; cases e1

theorem subject_node_spec (c : Ctx) (p : rdfxml.Prepared) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (state : rdfxml.State) (ag : Agrees c p.base p.lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.subject_node p scope limits state = .ok r ∧
      SubjSpec r state limits (fun t st' =>
        (∃ v, attrValue (rdfName "nodeID") (evsOf p.events) = some v ∧ NodeIdOf c v t ∧ st' = stOf state) ∨
        (attrValue (rdfName "nodeID") (evsOf p.events) = none ∧
          ((∃ v i, attrValue (rdfName "about") (evsOf p.events) = some v ∧ Resolved c v i ∧ t = .iri i ∧
            st' = stOf state) ∨
          (attrValue (rdfName "about") (evsOf p.events) = none ∧ t = (fresh c (stOf state)).1 ∧
            st' = (fresh c (stOf state)).2)))) := by
  unfold rdfxml.subject_node
  obtain ⟨o, ho, n, sm⟩ := find_value p 2#u8 _ class_names_nodeID
  rw [ho]; simp only [bind_ok]
  cases o with
  | none =>
    have hv := n rfl
    obtain ⟨r, hr, sound, complete⟩ := subject_about_spec c p scope limits state ag fits
    refine ⟨r, hr, fun s s' e => ?_, fun t st' h hb hi => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := sound s s' e
      exact ⟨.inr ⟨hv, h1⟩, h2, h3⟩
    · rcases h with ⟨v, e, -⟩ | ⟨-, h⟩
      · rw [hv] at e; cases e
      · exact complete t st' h hb hi
  | some k =>
    obtain ⟨kin, hv⟩ := sm k rfl
    simp only [index_eq p.events k kin, bind_ok]
    obtain ⟨r, hr, hc⟩ := node_id_eq c (p.events.val[k.val]).value scope limits ag.hscope ag.hterm
    rw [hr]; simp only [bind_ok]
    cases r with
    | Err e =>
      refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
      rintro t st' (⟨v, e1, ni, -⟩ | ⟨e1, -⟩) _ _
      · rw [hv] at e1; simp only [Option.some.injEq] at e1; subst e1
        obtain ⟨nc, b, sp, rfl⟩ := (nodeIdOf_iff _ _ _).mp ni
        have bound : b.length ≤ Usize.max := by
          have h1 := sp.2.2; have := Rowl.XmlScan.usize_le_max limits.term_bytes; rw [ag.hterm] at h1; omega
        have := (hc ⟨scope, alloc.vec.Vec.from b bound⟩).mpr
          ((nodeIdOf_iff _ _ _).mpr ⟨nc, b, sp, by simp [subjectTerm, ag.hscope]⟩)
        simp at this
      · rw [hv] at e1; cases e1
    | Ok node =>
      have ni := (hc node).mp rfl
      refine ⟨.Ok (.Blank node, state), by simp [core.result.Result.Insts.CoreOpsTry.branch], ?_, ?_⟩
      · intro s s' e
        simp at e; obtain ⟨rfl, rfl⟩ := e
        exact ⟨.inl ⟨_, hv, ni, rfl⟩, rfl, fits⟩
      · rintro t st' (⟨v, e1, ni2, rfl⟩ | ⟨e1, -⟩) _ _
        · rw [hv] at e1; simp only [Option.some.injEq] at e1; subst e1
          obtain ⟨-, b1, sp1, e1⟩ := (nodeIdOf_iff _ _ _).mp ni
          obtain ⟨-, b2, sp2, e2⟩ := (nodeIdOf_iff _ _ _).mp ni2
          exact ⟨_, _, rfl, by rw [e1, e2, spelled_unique sp1 sp2], rfl, rfl⟩
        · rw [hv] at e1; cases e1

theorem subject_of_spec (c : Ctx) (p : rdfxml.Prepared) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (state : rdfxml.State) (ag : Agrees c p.base p.lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.subject_of p scope limits state = .ok r ∧
      SubjSpec r state limits (fun t st' => SubjectOf c (evsOf p.events) (stOf state) t st') := by
  unfold rdfxml.subject_of
  obtain ⟨o, ho, n, sm⟩ := find_value p 1#u8 _ class_names_ID
  rw [ho]; simp only [bind_ok]
  cases o with
  | none =>
    have hv := n rfl
    obtain ⟨r, hr, sound, complete⟩ := subject_node_spec c p scope limits state ag fits
    refine ⟨r, hr, fun s s' e => ?_, fun t st' h hb hi => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := sound s s' e
      refine ⟨(subjectOf_iff _ _ _ _ _).mpr ?_, h2, h3⟩
      rcases h1 with ⟨v, a, b, e0⟩ | ⟨a, ⟨v, i, b, d, e1, e2⟩ | ⟨b, e1, e2⟩⟩
      · exact .inr (.inl ⟨v, hv, a, b, e0⟩)
      · exact .inr (.inr (.inl ⟨v, i, hv, a, b, d, e1, e2⟩))
      · exact .inr (.inr (.inr ⟨hv, a, b, e1, e2⟩))
    · rcases (subjectOf_iff _ _ _ _ _).mp h with ⟨v, i, e1, -⟩ | ⟨v, -, a, b, rfl⟩ |
          ⟨v, i, -, a, b, d, e1, e2⟩ | ⟨-, a, b, e1, e2⟩
      · rw [hv] at e1; cases e1
      · exact complete t _ (.inl ⟨v, a, b, rfl⟩) hb hi
      · exact complete t st' (.inr ⟨a, .inl ⟨v, i, b, d, e1, e2⟩⟩) hb hi
      · exact complete t st' (.inr ⟨a, .inr ⟨b, e1, e2⟩⟩) hb hi
  | some k =>
    obtain ⟨kin, hv⟩ := sm k rfl
    simp only [index_eq p.events k kin, bind_ok]
    obtain ⟨r, hr, sound, complete⟩ := id_iri_spec c (p.events.val[k.val]).value p.base limits state
      ag.hbase ag.hterm ag.hfits ag.hsmall ag.hpos
    rw [hr]; simp only [bind_ok]
    cases r with
    | Err e =>
      refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
      intro t st' h _ hi
      rcases (subjectOf_iff _ _ _ _ _).mp h with ⟨v, i, e1, ii, -⟩ | ⟨v, e1, -⟩ | ⟨v, i, e1, -⟩ | ⟨e1, -⟩
      · rw [hv] at e1; simp only [Option.some.injEq] at e1; subst e1
        obtain ⟨ri, s', he, -⟩ := complete i st' ii hi
        cases he
      all_goals (rw [hv] at e1; cases e1)
    | Ok pair =>
      obtain ⟨iri, s'⟩ := pair
      obtain ⟨ii, htr, hl⟩ := sound iri s' rfl
      refine ⟨.Ok (.Iri iri, s'), by simp [core.result.Result.Insts.CoreOpsTry.branch], ?_, ?_⟩
      · intro s s2 e
        simp at e; obtain ⟨rfl, rfl⟩ := e
        refine ⟨(subjectOf_iff _ _ _ _ _).mpr (.inl ⟨_, _, hv, ii, rfl⟩), htr, ?_⟩
        refine ⟨by rw [htr]; exact fits.1, ?_, hl⟩
        have := (idIri_iff _ _ _ _ _).mp ii
        have hb := congrArg St.blanks this.2.2.2
        simp [stOf] at hb; rw [hb]; exact fits.2.1
      · intro t st' h _ hi
        rcases (subjectOf_iff _ _ _ _ _).mp h with ⟨v, i, e1, ii2, rfl⟩ | ⟨v, e1, -⟩ | ⟨v, i, e1, -⟩ | ⟨e1, -⟩
        · rw [hv] at e1; simp only [Option.some.injEq] at e1; subst e1
          obtain ⟨ri, s3, he, hri, hs3, htr3⟩ := complete i st' ii2 hi
          simp at he; obtain ⟨rfl, rfl⟩ := he
          exact ⟨_, _, rfl, by simp [subjectTerm, hri], hs3, htr3⟩
        all_goals (rw [hv] at e1; cases e1)

/-- What a function returning a state computes: exactly the triples and
    states related by `R`, within the limits. -/
def StateSpec (r : core.result.Result rdfxml.State rdfxml.ErrorKind) (state : rdfxml.State)
    (limits : rdfxml.Limits) (R : List Statement → St → Prop) : Prop :=
  (∀ s', r = .Ok s' → ∃ ts, R ts (stOf s') ∧ stmts s' = stmts state ++ ts ∧ Fits limits s') ∧
  (∀ ts st', R ts st' → (stmts state ++ ts).length ≤ limits.items.val → st'.blanks ≤ limits.items.val →
    st'.ids.length ≤ limits.items.val → ∃ s', r = .Ok s' ∧ stmts s' = stmts state ++ ts ∧ stOf s' = st')

theorem emit_one (state : rdfxml.State) (t : rdf.Triple) (limits : rdfxml.Limits) (fits : Fits limits state) :
    ∃ r, rdfxml.emit state t limits = .ok r ∧
      StateSpec r state limits (fun ts st' => ts = [statementOf t] ∧ st' = stOf state) := by
  by_cases lt : state.triples.val.length < limits.items.val
  · obtain ⟨s', h, hst, hl, hv⟩ := emit_ok state t limits lt
    refine ⟨.Ok s', h, fun s2 e => ?_, fun ts st' hr _ _ _ => ?_⟩
    · simp at e; subst e
      refine ⟨_, ⟨rfl, hv⟩, hst, ?_⟩
      have := congrArg St.blanks hv; have h2 := congrArg (fun x => x.ids.length) hv
      simp [stOf] at this h2
      exact ⟨by omega, by rw [this]; exact fits.2.1, by rw [h2]; exact fits.2.2⟩
    · obtain ⟨rfl, rfl⟩ := hr
      exact ⟨s', rfl, hst, hv⟩
  · refine ⟨.Err .ResourceLimit, emit_err state t limits lt, by simp, ?_⟩
    rintro ts st' ⟨rfl, -⟩ hl _ _
    simp [stmts_length] at hl; omega

theorem typeTriple_iff (c : Ctx) (s : Term) (u : Word) (ts : List Statement) :
    TypeTriple c s u ts ↔ (u = rdfName "Description" ∧ ts = []) ∨
      (u ≠ rdfName "Description" ∧ ∃ i, IriOf c u i ∧ ts = [⟨s, rdfBytes "type", .iri i⟩]) := by
  constructor
  · intro h; cases h with
    | description d => exact .inl ⟨d, rfl⟩
    | typed d io => exact .inr ⟨d, _, io, rfl⟩
  · rintro (⟨d, rfl⟩ | ⟨d, i, io, rfl⟩)
    · exact .description d
    · exact .typed d io

theorem rdf_type_slice (l : List U8) (h : l.length = (47#usize).val)
    (e : l = (rdfBytes "type")) : (Array.to_slice (Array.make 47#usize l h)).val = rdfBytes "type" := by
  rw [slice_val, e]

theorem type_triple_spec (c : Ctx) (subject : rdf.Subject) (uri : alloc.vec.Vec U32) (limits : rdfxml.Limits)
    (state : rdfxml.State) (ht : c.termLimit = limits.term_bytes.val) (fits : Fits limits state) :
    ∃ r, rdfxml.type_triple subject uri limits state = .ok r ∧
      StateSpec r state limits (fun ts st' => TypeTriple c (subjectTerm subject) (word uri) ts ∧ st' = stOf state) := by
  unfold rdfxml.type_triple
  simp only [lift, bind_ok, is_rdf_Description, decide_eq_true_eq]
  by_cases d : word uri = rdfName "Description"
  · rw [if_pos d]
    refine ⟨.Ok state, rfl, fun s' e => ?_, fun ts st' hr _ _ _ => ?_⟩
    · simp at e; subst e
      exact ⟨[], ⟨(typeTriple_iff ..).mpr (.inl ⟨d, rfl⟩), rfl⟩, by simp, fits⟩
    · obtain ⟨h, rfl⟩ := hr
      rcases (typeTriple_iff ..).mp h with ⟨-, rfl⟩ | ⟨nd, -⟩
      · exact ⟨state, rfl, by simp, rfl⟩
      · exact absurd d nd
  · rw [if_neg d]
    obtain ⟨r1, hr1, hc1⟩ := iri_of_eq uri limits
    rw [hr1]; simp only [bind_ok]
    cases r1 with
    | Err e =>
      refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
      rintro ts st' ⟨h, -⟩ _ _ _
      rcases (typeTriple_iff ..).mp h with ⟨d2, -⟩ | ⟨-, i, io, -⟩
      · exact absurd d2 d
      · have bound : i.length ≤ Usize.max := by
          have h1 := io.1.2.2; have := Rowl.XmlScan.usize_le_max limits.term_bytes; rw [ht] at h1; omega
        have := (hc1 ⟨alloc.vec.Vec.from i bound⟩).mpr (by
          rw [← ht]; simpa using (show Spelled c.termLimit (word uri) i ∧ Rowl.NTriples.AbsoluteIri i from io))
        simp at this
    | Ok iri =>
      have io := (hc1 iri).mp rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, rdf_triple_eq]
      obtain ⟨r, hr, sound, complete⟩ := emit_one state _ limits fits
      refine ⟨r, hr, fun s' e => ?_, fun ts st' h hl hb hi => ?_⟩
      · obtain ⟨ts, ⟨rfl, hst⟩, hs, hf⟩ := sound s' e
        refine ⟨_, ⟨(typeTriple_iff ..).mpr (.inr ⟨d, iri.spelling.val, by unfold IriOf; rw [ht]; exact io, ?_⟩),
          hst⟩, hs, hf⟩
        simp [statementOf, objectTerm, slice_val, rdfBytes_type]
      · obtain ⟨h, rfl⟩ := h
        rcases (typeTriple_iff ..).mp h with ⟨d2, -⟩ | ⟨-, i, io2, rfl⟩
        · exact absurd d2 d
        · have : iri.spelling.val = i := spelled_unique (by rw [ht]; exact io.1) io2.1
          apply complete _ _ ⟨?_, rfl⟩ hl hb hi
          simp [statementOf, objectTerm, slice_val, rdfBytes_type, this]

/-! ## Property attributes -/

theorem type_property : PropertyAttributeUri (rdfName "type") := by
  unfold PropertyAttributeUri; rw [core_mem, old_mem]; decide

/-- The triple of one property attribute. -/
def AttrTriple (c : Ctx) (s : Term) (ev : Word × Word) (ts : List Statement) : Prop :=
  (ev.1 = rdfName "type" ∧ ∃ i, Resolved c ev.2 i ∧ ts = [⟨s, rdfBytes "type", .iri i⟩]) ∨
  (ev.1 ≠ rdfName "type" ∧ ∃ p o, IriOf c ev.1 p ∧ LiteralOf c ev.2 o ∧ ts = [⟨s, p, o⟩])

theorem propAttrs_nil_iff (c : Ctx) (s : Term) (ts : List Statement) : PropAttrs c s [] ts ↔ ts = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

theorem propAttrs_cons_iff (c : Ctx) (s : Term) (u v : Word) (evs : List (Word × Word)) (ts : List Statement) :
    PropAttrs c s ((u, v) :: evs) ts ↔ (¬ PropertyAttributeUri u ∧ PropAttrs c s evs ts) ∨
      (PropertyAttributeUri u ∧ ∃ t1 ts', AttrTriple c s (u, v) t1 ∧ PropAttrs c s evs ts' ∧ ts = t1 ++ ts') := by
  constructor
  · intro h
    cases h with
    | skip n r => exact .inl ⟨n, r⟩
    | type rs r => exact .inr ⟨type_property, _, _, .inl ⟨rfl, _, rs, rfl⟩, r, rfl⟩
    | literal pa nt io lo r => exact .inr ⟨pa, _, _, .inr ⟨nt, _, _, io, lo, rfl⟩, r, rfl⟩
  · rintro (⟨n, r⟩ | ⟨pa, t1, ts', at1, r, rfl⟩)
    · exact .skip n r
    · rcases at1 with ⟨e, i, rs, rfl⟩ | ⟨nt, p, o, io, lo, rfl⟩
      · simp only at e; subst e; exact .type rs r
      · exact .literal pa nt io lo r

theorem attribute_triple_spec (c : Ctx) (subject : rdf.Subject) (event : rdfxml.Event) (base : alloc.vec.Vec U8)
    (lang : alloc.vec.Vec U32) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ag : Agrees c base lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.attribute_triple subject event base lang limits state = .ok r ∧
      StateSpec r state limits (fun ts st' =>
        AttrTriple c (subjectTerm subject) (eventView event) ts ∧ st' = stOf state) := by
  unfold rdfxml.attribute_triple
  simp only [lift, bind_ok, is_rdf_type, decide_eq_true_eq]
  have lim := Rowl.XmlScan.usize_le_max limits.term_bytes
  by_cases ty : word event.uri = rdfName "type"
  · rw [if_pos ty]
    obtain ⟨r1, hr1, hc1⟩ := resolved_eq c base event.value limits ag.hbase ag.hterm ag.hfits ag.hsmall
    rw [hr1]; simp only [bind_ok]
    cases r1 with
    | Err e =>
      refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
      rintro ts st' ⟨⟨-, i, rs, -⟩ | ⟨nt, -⟩, -⟩ _ _ _
      · have bound : i.length ≤ Usize.max := by
          obtain ⟨_, _, _, _, l⟩ := rs.1; rw [ag.hterm] at l; omega
        have := (hc1 ⟨alloc.vec.Vec.from i bound⟩).mpr (by simpa [eventView] using rs)
        simp at this
      · exact absurd ty nt
    | Ok iri =>
      have rs := (hc1 iri).mp rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, rdf_triple_eq]
      obtain ⟨r, hr, sound, complete⟩ := emit_one state _ limits fits
      refine ⟨r, hr, fun s' e => ?_, fun ts st' h hl hb hi => ?_⟩
      · obtain ⟨ts, ⟨rfl, hst⟩, hs, hf⟩ := sound s' e
        refine ⟨_, ⟨.inl ⟨ty, iri.spelling.val, rs, ?_⟩, hst⟩, hs, hf⟩
        simp [statementOf, objectTerm, slice_val, rdfBytes_type]
      · obtain ⟨⟨-, i, rs2, rfl⟩ | ⟨nt, -⟩, rfl⟩ := h
        · have : iri.spelling.val = i := by
            obtain ⟨r1, sp1, -, res1, -⟩ := rs.1
            obtain ⟨r2, sp2, -, res2, -⟩ := rs2.1
            rw [spelled_unique sp1 sp2] at res1
            exact bytes_word_inj (Option.some.inj (res1.symm.trans res2))
          apply complete _ _ ⟨?_, rfl⟩ hl hb hi
          simp [statementOf, objectTerm, slice_val, rdfBytes_type, this]
        · exact absurd ty nt
  · rw [if_neg ty]
    obtain ⟨r1, hr1, hc1⟩ := iri_of_eq event.uri limits
    rw [hr1]; simp only [bind_ok]
    cases r1 with
    | Err e =>
      refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
      rintro ts st' ⟨⟨t1, -⟩ | ⟨-, p, o, io, -⟩, -⟩ _ _ _
      · exact absurd t1 ty
      · have bound : p.length ≤ Usize.max := by
          have l := io.1.2.2; rw [ag.hterm] at l; omega
        have := (hc1 ⟨alloc.vec.Vec.from p bound⟩).mpr (by
          rw [← ag.hterm]; simpa [eventView] using (show Spelled c.termLimit (word event.uri) p ∧
            Rowl.NTriples.AbsoluteIri p from io))
        simp at this
    | Ok pred =>
      have io := (hc1 pred).mp rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨r2, hr2, hc2⟩ := literal_of_eq c event.value lang limits ag.hlang ag.hterm
      rw [hr2]; simp only [bind_ok]
      cases r2 with
      | Err e =>
        refine ⟨.Err e, by simp [residual], by simp, ?_⟩
        rintro ts st' ⟨⟨t1, -⟩ | ⟨-, p, o, -, lo, -⟩, -⟩ _ _ _
        · exact absurd t1 ty
        · obtain ⟨lit, hlit⟩ : ∃ l : rdf.RdfLiteral, literalTerm l = o := by
            rcases (literalOf_iff _ _ _).mp lo with ⟨-, b, sp, rfl⟩ | ⟨-, b, g, sp, sg, -, rfl⟩
            · have bound : b.length ≤ Usize.max := by have l := sp.2.2; rw [ag.hterm] at l; omega
              have bx : xsdString.length ≤ Usize.max := by rw [xsdString_eq]; simp; scalar_tac
              exact ⟨⟨alloc.vec.Vec.from b bound, .Datatype ⟨alloc.vec.Vec.from xsdString bx⟩⟩, by simp [literalTerm]⟩
            · have bound : b.length ≤ Usize.max := by have l := sp.2.2; rw [ag.hterm] at l; omega
              have bg : g.length ≤ Usize.max := by have l := sg.2.2; rw [ag.hterm] at l; omega
              exact ⟨⟨alloc.vec.Vec.from b bound, .Language (alloc.vec.Vec.from g bg)⟩, by simp [literalTerm]⟩
          have := (hc2 lit).mpr (by rw [hlit]; simpa [eventView] using lo)
          simp at this
      | Ok lit =>
        have lo := (hc2 lit).mp rfl
        simp only [copy_subject_eq, bind_ok]
        obtain ⟨r, hr, sound, complete⟩ := emit_one state ⟨subject, pred, .Literal lit⟩ limits fits
        refine ⟨r, hr, fun s' e => ?_, fun ts st' h hl hb hi => ?_⟩
        · obtain ⟨ts, ⟨rfl, hst⟩, hs, hf⟩ := sound s' e
          refine ⟨_, ⟨.inr ⟨ty, pred.spelling.val, literalTerm lit, by unfold IriOf; rw [ag.hterm]; exact io,
            by simpa [eventView] using lo, rfl⟩, hst⟩, hs, hf⟩
        · obtain ⟨⟨t1, -⟩ | ⟨-, p, o, io2, lo2, rfl⟩, rfl⟩ := h
          · exact absurd t1 ty
          · have e1 : pred.spelling.val = p := spelled_unique (by rw [ag.hterm]; exact io.1) io2.1
            have e2 : literalTerm lit = o := by
              rcases (literalOf_iff _ _ _).mp lo with ⟨h0, b, sp, e⟩ | ⟨h0, b, g, sp, sg, tg, e⟩ <;>
              rcases (literalOf_iff _ _ _).mp lo2 with ⟨h0', b', sp', e'⟩ | ⟨h0', b', g', sp', sg', tg', e'⟩
              · rw [e, e', spelled_unique sp sp']
              · exact absurd h0 h0'
              · exact absurd h0' h0
              · rw [e, e', spelled_unique sp sp', spelled_unique sg sg']
            apply complete _ _ ⟨?_, rfl⟩ hl hb hi
            simp [statementOf, objectTerm, e1, e2]

theorem stmts_append_assoc (a b d : List Statement) : a ++ b ++ d = a ++ (b ++ d) := List.append_assoc _ _ _

theorem attribute_triples_spec (c : Ctx) (subject : rdf.Subject) (events : alloc.vec.Vec rdfxml.Event)
    (i : Usize) (base : alloc.vec.Vec U8) (lang : alloc.vec.Vec U32) (scope : alloc.vec.Vec U8)
    (limits : rdfxml.Limits) (state : rdfxml.State) (ag : Agrees c base lang scope limits)
    (fits : Fits limits state) :
    ∃ r, rdfxml.attribute_triples subject events i base lang limits state = .ok r ∧
      StateSpec r state limits (fun ts st' =>
        PropAttrs c (subjectTerm subject) ((evsOf events).drop i.val) ts ∧ st' = stOf state) := by
  rw [rdfxml.attribute_triples]
  by_cases lt : i.val < events.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len events) (by simpa using lt)
    obtain ⟨cl, hcl, hclv⟩ := class_of_eq (events.val[i.val]).uri
    have lt' : i.val < (evsOf events).length := by simpa [evsOf] using lt
    have d : (evsOf events).drop i.val = eventView events.val[i.val] :: (evsOf events).drop i1.val := by
      rw [hi1v, List.drop_eq_getElem_cons lt']; simp [evsOf]
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq events i lt, hcl]
    rw [d]
    have ev : eventView events.val[i.val] = (word (events.val[i.val]).uri, word (events.val[i.val]).value) := rfl
    rw [ev]
    by_cases zero : cl = 0#u8
    · have pa : PropertyAttributeUri (word (events.val[i.val]).uri) := by
        rw [← classOf_zero, ← hclv, zero]; rfl
      simp only [zero, ite_true]
      obtain ⟨r1, hr1, s1, c1⟩ := attribute_triple_spec c subject events.val[i.val] base lang scope limits state
        ag fits
      rw [hr1]; simp only [bind_ok]
      cases r1 with
      | Err e =>
        refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
        rintro ts st' ⟨h, rfl⟩ hl hb hi
        rcases (propAttrs_cons_iff ..).mp h with ⟨n, -⟩ | ⟨-, t1, ts', at1, -, rfl⟩
        · exact absurd pa n
        · obtain ⟨s', he, -⟩ := c1 t1 (stOf state) ⟨at1, rfl⟩ (by simp at hl ⊢; omega) hb hi
          cases he
      | Ok s1' =>
        obtain ⟨t1, ⟨at1, hst1⟩, hs1, hf1⟩ := s1 s1' rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hi1]
        obtain ⟨r, hr, sound, complete⟩ := attribute_triples_spec c subject events i1 base lang scope limits s1'
          ag hf1
        refine ⟨r, hr, fun s' e => ?_, fun ts st' h hl hb hi => ?_⟩
        · obtain ⟨ts', ⟨h', hst'⟩, hs', hf'⟩ := sound s' e
          refine ⟨t1 ++ ts', ⟨(propAttrs_cons_iff ..).mpr (.inr ⟨pa, t1, ts', at1, h', rfl⟩), by rw [hst', hst1]⟩,
            by rw [hs', hs1, List.append_assoc], hf'⟩
        · obtain ⟨h, rfl⟩ := h
          rcases (propAttrs_cons_iff ..).mp h with ⟨n, -⟩ | ⟨-, t2, ts', at2, h', rfl⟩
          · exact absurd pa n
          · obtain ⟨s2, he, hs2, hst2⟩ := c1 t2 (stOf state) ⟨at2, rfl⟩ (by simp at hl ⊢; omega) hb hi
            simp only [core.result.Result.Ok.injEq] at he; subst he
            have ht : t1 = t2 := by
              have := hs1.symm.trans hs2; simpa using this
            subst ht
            obtain ⟨s3, he3, hs3, hst3⟩ := complete ts' (stOf state) ⟨h', hst1.symm⟩
              (by rw [hs1]; simpa [List.append_assoc] using hl) hb hi
            exact ⟨s3, he3, by rw [hs3, hs1, List.append_assoc], hst3⟩
    · have npa : ¬ PropertyAttributeUri (word (events.val[i.val]).uri) := by
        rw [← classOf_zero, ← hclv]; intro h; exact zero (UScalar.eq_of_val_eq (by simpa using h))
      simp only [zero, ite_false, hi1, bind_ok]
      obtain ⟨r, hr, sound, complete⟩ := attribute_triples_spec c subject events i1 base lang scope limits state
        ag fits
      refine ⟨r, hr, fun s' e => ?_, fun ts st' h hl hb hi => ?_⟩
      · obtain ⟨ts, ⟨h', hst⟩, hs, hf⟩ := sound s' e
        exact ⟨ts, ⟨(propAttrs_cons_iff ..).mpr (.inl ⟨npa, h'⟩), hst⟩, hs, hf⟩
      · obtain ⟨h, rfl⟩ := h
        rcases (propAttrs_cons_iff ..).mp h with ⟨-, h'⟩ | ⟨pa, -⟩
        · exact complete ts _ ⟨h', rfl⟩ hl hb hi
        · exact absurd pa npa
  · have e : (evsOf events).drop i.val = [] := List.drop_eq_nil_of_le (by simp [evsOf]; omega)
    refine ⟨.Ok state, by simp [UScalar.lt_equiv, lt], fun s' h => ?_, fun ts st' h _ _ _ => ?_⟩
    · simp at h; subst h
      exact ⟨[], ⟨by rw [e]; exact .nil, rfl⟩, by simp, fits⟩
    · obtain ⟨h, rfl⟩ := h
      rw [e, propAttrs_nil_iff] at h; subst h
      exact ⟨state, rfl, by simp, rfl⟩
termination_by events.val.length - i.val
decreasing_by all_goals omega

/-! ## Statements and their reification -/

theorem stated_iff (c : Ctx) (evs : List (Word × Word)) (t : Statement) (st : St) (ts : List Statement) (st' : St) :
    Stated c evs t st ts st' ↔ (attrValue (rdfName "ID") evs = none ∧ ts = [t] ∧ st' = st) ∨
      (∃ v i, attrValue (rdfName "ID") evs = some v ∧ IdIri c v st i st' ∧ ts = t :: reification i t) := by
  constructor
  · intro h; cases h with
    | plain a => exact .inl ⟨a, rfl, rfl⟩
    | reified a ii => exact .inr ⟨_, _, a, ii, rfl⟩
  · rintro (⟨a, rfl, rfl⟩ | ⟨v, i, a, ii, rfl⟩)
    · exact .plain a
    · exact .reified a ii

theorem idIri_blanks {c : Ctx} {v : Word} {st : St} {i : List U8} {st' : St} (h : IdIri c v st i st') :
    st'.blanks = st.blanks ∧ st'.ids.length = st.ids.length + 1 := by
  obtain ⟨-, -, -, rfl⟩ := (idIri_iff ..).mp h
  simp

theorem stated_spec (c : Ctx) (subject : rdf.Subject) (predicate : rdf.RdfIri) (object : rdf.Object)
    (p : rdfxml.Prepared) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ag : Agrees c p.base p.lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.stated subject predicate object p limits state = .ok r ∧
      StateSpec r state limits (Stated c (evsOf p.events)
        ⟨subjectTerm subject, predicate.spelling.val, objectTerm object⟩ (stOf state)) := by
  unfold rdfxml.stated
  obtain ⟨o, ho, n, sm⟩ := find_value p 1#u8 _ class_names_ID
  rw [ho]; simp only [bind_ok]
  cases o with
  | none =>
    have hv := n rfl
    simp only [copy_subject_eq, bind_ok]
    obtain ⟨r, hr, sound, complete⟩ := emit_one state ⟨subject, predicate, object⟩ limits fits
    refine ⟨r, hr, fun s' e => ?_, fun ts st' h hl hb hi => ?_⟩
    · obtain ⟨ts, ⟨rfl, hst⟩, hs, hf⟩ := sound s' e
      exact ⟨_, (stated_iff ..).mpr (.inl ⟨hv, rfl, hst⟩), hs, hf⟩
    · rcases (stated_iff ..).mp h with ⟨-, rfl, rfl⟩ | ⟨v, i, e, -⟩
      · exact complete _ _ ⟨rfl, rfl⟩ hl hb hi
      · rw [hv] at e; cases e
  | some k =>
    obtain ⟨kin, hv⟩ := sm k rfl
    simp only [index_eq p.events k kin, bind_ok]
    obtain ⟨r1, hr1, s1, c1⟩ := id_iri_spec c (p.events.val[k.val]).value p.base limits state
      ag.hbase ag.hterm ag.hfits ag.hsmall ag.hpos
    rw [hr1]; simp only [bind_ok]
    cases r1 with
    | Err e =>
      refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
      intro ts st' h _ _ hi
      rcases (stated_iff ..).mp h with ⟨e1, -⟩ | ⟨v, i, e1, ii, -⟩
      · rw [hv] at e1; cases e1
      · rw [hv] at e1; simp only [Option.some.injEq] at e1; subst e1
        obtain ⟨_, _, he, -⟩ := c1 i st' ii hi
        cases he
    | Ok pair =>
      obtain ⟨iri, s1'⟩ := pair
      obtain ⟨ii, htr1, hl1⟩ := s1 iri s1' rfl
      obtain ⟨hb1, hi1⟩ := idIri_blanks ii
      have fits1 : Fits limits s1' := by
        refine ⟨by rw [htr1]; exact fits.1, ?_, hl1⟩
        simp [stOf] at hb1; rw [hb1]; exact fits.2.1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, copy_subject_eq, copy_iri_eq,
        copy_object_eq]
      have main : statementOf ⟨subject, predicate, object⟩ =
          ⟨subjectTerm subject, predicate.spelling.val, objectTerm object⟩ := rfl
      have contra : ∀ ts st', Stated c (evsOf p.events)
          ⟨subjectTerm subject, predicate.spelling.val, objectTerm object⟩ (stOf state) ts st' →
          (stmts state ++ ts).length ≤ limits.items.val → s1'.triples.val.length + 5 ≤ limits.items.val := by
        intro ts st' h hl
        rcases (stated_iff ..).mp h with ⟨e1, -⟩ | ⟨v, i, e1, ii2, rfl⟩
        · rw [hv] at e1; cases e1
        · simp [stmts_length, reification] at hl
          rw [htr1]; omega
      by_cases room : s1'.triples.val.length + 5 ≤ limits.items.val
      · obtain ⟨s2, h2, hs2, hl2, hv2⟩ := emit_ok s1' ⟨subject, predicate, object⟩ limits (by omega)
        obtain ⟨s3, h3, hs3, hl3, hv3⟩ := reify_ok iri subject predicate object limits s2 (by omega)
        refine ⟨.Ok s3, by simp [h2, h3], fun s' e => ?_, fun ts st' h hl hb hi => ?_⟩
        · simp at e; subst e
          refine ⟨_, by rw [hv3, hv2]; exact (stated_iff ..).mpr (.inr ⟨_, _, hv, ii, rfl⟩), ?_, ?_⟩
          · rw [hs3, hs2, main]
            simp [stmts, htr1]
          · refine ⟨by omega, ?_, ?_⟩
            · have := congrArg St.blanks (hv3.trans hv2); simp [stOf] at this; rw [this]; exact fits1.2.1
            · have := congrArg (fun x => x.ids.length) (hv3.trans hv2); simp [stOf] at this; rw [this]; exact fits1.2.2
        · rcases (stated_iff ..).mp h with ⟨e1, -⟩ | ⟨v, i, e1, ii2, rfl⟩
          · rw [hv] at e1; cases e1
          · rw [hv] at e1; simp only [Option.some.injEq] at e1; subst e1
            obtain ⟨ri, s1'', he, hri, hs1'', -⟩ := c1 i st' ii2 hi
            simp at he; obtain ⟨rfl, rfl⟩ := he
            refine ⟨s3, rfl, ?_, by rw [hv3, hv2, hs1'']⟩
            rw [hs3, hs2, main, ← hri]
            simp [stmts, htr1]
      · by_cases a1 : s1'.triples.val.length < limits.items.val
        · obtain ⟨s2, h2, hs2, hl2, hv2⟩ := emit_ok s1' ⟨subject, predicate, object⟩ limits a1
          obtain ⟨e, he⟩ := reify_err iri subject predicate object limits s2 (by omega)
          refine ⟨.Err e, by simp [h2, he], by simp, fun ts st' h hl _ _ => absurd (contra ts st' h hl) room⟩
        · refine ⟨.Err .ResourceLimit, by simp [emit_err s1' _ limits a1, residual], by simp,
            fun ts st' h hl _ _ => absurd (contra ts st' h hl) room⟩

/-! ## Objects of empty and literal property elements -/

theorem emptyObject_iff (c : Ctx) (evs : List (Word × Word)) (st : St) (t : Term) (st' : St) :
    EmptyObject c evs st t st' ↔
      (∃ v i, attrValue (rdfName "resource") evs = some v ∧ Resolved c v i ∧ t = .iri i ∧ st' = st) ∨
      (∃ v, attrValue (rdfName "resource") evs = none ∧ attrValue (rdfName "nodeID") evs = some v ∧
        NodeIdOf c v t ∧ st' = st) ∨
      (attrValue (rdfName "resource") evs = none ∧ attrValue (rdfName "nodeID") evs = none ∧
        t = (fresh c st).1 ∧ st' = (fresh c st).2) := by
  constructor
  · intro h; cases h with
    | resource a r => exact .inl ⟨_, _, a, r, rfl, rfl⟩
    | nodeId a b n => exact .inr (.inl ⟨_, a, b, n, rfl⟩)
    | fresh a b => exact .inr (.inr ⟨a, b, rfl, rfl⟩)
  · rintro (⟨v, i, a, r, rfl, rfl⟩ | ⟨v, a, b, n, rfl⟩ | ⟨a, b, rfl, rfl⟩)
    · exact .resource a r
    · exact .nodeId a b n
    · exact .fresh a b

theorem empty_object_spec (c : Ctx) (p : rdfxml.Prepared) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (state : rdfxml.State) (ag : Agrees c p.base p.lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.empty_object p scope limits state = .ok r ∧
      SubjSpec r state limits (fun t st' => EmptyObject c (evsOf p.events) (stOf state) t st') := by
  unfold rdfxml.empty_object
  have lim := Rowl.XmlScan.usize_le_max limits.term_bytes
  obtain ⟨o, ho, n, sm⟩ := find_value p 4#u8 _ class_names_resource
  rw [ho]; simp only [bind_ok]
  cases o with
  | none =>
    have hres := n rfl
    obtain ⟨o2, ho2, n2, sm2⟩ := find_value p 2#u8 _ class_names_nodeID
    rw [ho2]; simp only [bind_ok]
    cases o2 with
    | none =>
      have hnode := n2 rfl
      obtain ⟨r, hr, sound, complete⟩ := fresh_spec c scope limits state ag.hscope fits
      refine ⟨r, hr, fun s s' e => ?_, fun t st' h hb hi => ?_⟩
      · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := sound s s' e
        exact ⟨(emptyObject_iff ..).mpr (.inr (.inr ⟨hres, hnode, h1, h2⟩)), h3, h4⟩
      · rcases (emptyObject_iff ..).mp h with ⟨v, i, e1, -⟩ | ⟨v, -, e1, -⟩ | ⟨-, -, e1, e2⟩
        · rw [hres] at e1; cases e1
        · rw [hnode] at e1; cases e1
        · exact complete t st' ⟨e1, e2⟩ hb hi
    | some k =>
      obtain ⟨kin, hv⟩ := sm2 k rfl
      simp only [index_eq p.events k kin, bind_ok]
      obtain ⟨r, hr, hc⟩ := node_id_eq c (p.events.val[k.val]).value scope limits ag.hscope ag.hterm
      rw [hr]; simp only [bind_ok]
      cases r with
      | Err e =>
        refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
        intro t st' h _ _
        rcases (emptyObject_iff ..).mp h with ⟨v, i, e1, -⟩ | ⟨v, -, e1, ni, -⟩ | ⟨-, e1, -⟩
        · rw [hres] at e1; cases e1
        · rw [hv] at e1; simp only [Option.some.injEq] at e1; subst e1
          obtain ⟨nc, b, sp, rfl⟩ := (nodeIdOf_iff _ _ _).mp ni
          have bound : b.length ≤ Usize.max := by
            have h1 := sp.2.2; rw [ag.hterm] at h1; omega
          have := (hc ⟨scope, alloc.vec.Vec.from b bound⟩).mpr
            ((nodeIdOf_iff _ _ _).mpr ⟨nc, b, sp, by simp [subjectTerm, ag.hscope]⟩)
          simp at this
        · rw [hv] at e1; cases e1
      | Ok node =>
        have ni := (hc node).mp rfl
        refine ⟨.Ok (.Blank node, state), by simp [core.result.Result.Insts.CoreOpsTry.branch], ?_, ?_⟩
        · intro s s' e
          simp at e; obtain ⟨rfl, rfl⟩ := e
          exact ⟨(emptyObject_iff ..).mpr (.inr (.inl ⟨_, hres, hv, ni, rfl⟩)), rfl, fits⟩
        · intro t st' h _ _
          rcases (emptyObject_iff ..).mp h with ⟨v, i, e1, -⟩ | ⟨v, -, e1, ni2, rfl⟩ | ⟨-, e1, -⟩
          · rw [hres] at e1; cases e1
          · rw [hv] at e1; simp only [Option.some.injEq] at e1; subst e1
            obtain ⟨-, b1, sp1, e1⟩ := (nodeIdOf_iff _ _ _).mp ni
            obtain ⟨-, b2, sp2, e2⟩ := (nodeIdOf_iff _ _ _).mp ni2
            exact ⟨_, _, rfl, by rw [e1, e2, spelled_unique sp1 sp2], rfl, rfl⟩
          · rw [hv] at e1; cases e1
  | some k =>
    obtain ⟨kin, hv⟩ := sm k rfl
    simp only [index_eq p.events k kin, bind_ok]
    obtain ⟨r, hr, hc⟩ := resolved_eq c p.base (p.events.val[k.val]).value limits ag.hbase ag.hterm ag.hfits ag.hsmall
    rw [hr]; simp only [bind_ok]
    cases r with
    | Err e =>
      refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
      intro t st' h _ _
      rcases (emptyObject_iff ..).mp h with ⟨v, i, e1, rs, -⟩ | ⟨v, e1, -⟩ | ⟨e1, -⟩
      · rw [hv] at e1; simp only [Option.some.injEq] at e1; subst e1
        have bound : i.length ≤ Usize.max := by
          obtain ⟨_, _, _, _, l⟩ := rs.1; rw [ag.hterm] at l; omega
        have := (hc ⟨alloc.vec.Vec.from i bound⟩).mpr (by simpa using rs)
        simp at this
      all_goals (rw [hv] at e1; cases e1)
    | Ok iri =>
      have rs := (hc iri).mp rfl
      refine ⟨.Ok (.Iri iri, state), by simp [core.result.Result.Insts.CoreOpsTry.branch], ?_, ?_⟩
      · intro s s' e
        simp at e; obtain ⟨rfl, rfl⟩ := e
        exact ⟨(emptyObject_iff ..).mpr (.inl ⟨_, _, hv, rs, rfl, rfl⟩), rfl, fits⟩
      · intro t st' h _ _
        rcases (emptyObject_iff ..).mp h with ⟨v, i, e1, rs2, rfl, rfl⟩ | ⟨v, e1, -⟩ | ⟨e1, -⟩
        · rw [hv] at e1; simp only [Option.some.injEq] at e1; subst e1
          have : iri.spelling.val = i := by
            obtain ⟨r1, sp1, -, res1, -⟩ := rs.1
            obtain ⟨r2, sp2, -, res2, -⟩ := rs2.1
            rw [spelled_unique sp1 sp2] at res1
            exact bytes_word_inj (Option.some.inj (res1.symm.trans res2))
          exact ⟨_, _, rfl, by simp [subjectTerm, this], rfl, rfl⟩
        all_goals (rw [hv] at e1; cases e1)

theorem textObject_iff (c : Ctx) (evs : List (Word × Word)) (v : Word) (o : Term) :
    TextObject c evs v o ↔ (∃ d, attrValue (rdfName "datatype") evs = some d ∧ TypedOf c v d o) ∨
      (attrValue (rdfName "datatype") evs = none ∧ LiteralOf c v o) := by
  constructor
  · intro h; cases h with
    | typed a t => exact .inl ⟨_, a, t⟩
    | plain a l => exact .inr ⟨a, l⟩
  · rintro (⟨d, a, t⟩ | ⟨a, l⟩)
    · exact .typed a t
    · exact .plain a l

theorem text_literal_spec (c : Ctx) (text : alloc.vec.Vec U32) (p : rdfxml.Prepared) (scope : alloc.vec.Vec U8)
    (limits : rdfxml.Limits) (ag : Agrees c p.base p.lang scope limits) :
    ∃ r, rdfxml.text_literal text p limits = .ok r ∧
      ∀ l, r = .Ok l ↔ TextObject c (evsOf p.events) (word text) (literalTerm l) := by
  unfold rdfxml.text_literal
  obtain ⟨o, ho, n, sm⟩ := find_value p 6#u8 _ class_names_datatype
  rw [ho]; simp only [bind_ok]
  cases o with
  | none =>
    have hd := n rfl
    obtain ⟨r, hr, hc⟩ := literal_of_eq c text p.lang limits ag.hlang ag.hterm
    refine ⟨r, hr, fun l => ?_⟩
    rw [hc l, textObject_iff]
    simp [hd]
  | some k =>
    obtain ⟨kin, hv⟩ := sm k rfl
    simp only [index_eq p.events k kin, bind_ok]
    obtain ⟨r, hr, hc⟩ := typed_of_eq c text (p.events.val[k.val]).value limits ag.hterm
    refine ⟨r, hr, fun l => ?_⟩
    rw [hc l, textObject_iff]
    simp [hv]

/-- The triples of a literal property element without rdf:parseType. -/
def LiteralBody (c : Ctx) (evs : List (Word × Word)) (e : xml.Element) (s : Term) (p : List U8) (st : St)
    (ts : List Statement) (st' : St) : Prop :=
  Only evs [rdfName "ID", rdfName "datatype"] ∧
  ∃ t o, e.children.val = [.Text t] ∧ TextObject c evs (word t) o ∧ Stated c evs ⟨s, p, o⟩ st ts st'

theorem within_only (events : alloc.vec.Vec rdfxml.Event) (set : U8) (P : Nat → Prop) (us : List Word)
    (hP : ∀ c : U8, rdfxml.allows set c = .ok (decide (P c.val)))
    (hu : ∀ u, P (classOf u) ↔ u ∈ us) :
    rdfxml.within events set 0#usize = .ok (decide (Only (evsOf events) us)) := by
  rw [within_eq events set P hP 0#usize, usize_zero_val, List.drop_zero]
  congr 1
  apply decide_eq_decide.mpr
  exact classes_mem _ _ _ hu

theorem only_ID : ∀ u, (fun c => c = 1) (classOf u) ↔ u ∈ [rdfName "ID"] := fun u => by
  simp [classOf_ID]

theorem only_ID_datatype : ∀ u, (fun c => c = 1 ∨ c = 6) (classOf u) ↔ u ∈ [rdfName "ID", rdfName "datatype"] :=
  fun u => by simp [classOf_ID, classOf_datatype]

theorem only_ID_parseType : ∀ u, (fun c => c = 1 ∨ c = 5) (classOf u) ↔ u ∈ [rdfName "ID", rdfName "parseType"] :=
  fun u => by simp [classOf_ID, classOf_parseType]

theorem only_0 (events : alloc.vec.Vec rdfxml.Event) :
    rdfxml.within events 0#u8 0#usize = .ok (decide (Only (evsOf events) [rdfName "ID"])) :=
  within_only events 0#u8 (fun c => c = 1) _
    (fun c => by rw [allows_0]; exact congrArg _ (decide_eq_decide.mpr Iff.rfl)) only_ID

theorem only_1 (events : alloc.vec.Vec rdfxml.Event) :
    rdfxml.within events 1#u8 0#usize = .ok (decide (Only (evsOf events) [rdfName "ID", rdfName "datatype"])) :=
  within_only events 1#u8 (fun c => c = 1 ∨ c = 6) _
    (fun c => by rw [allows_1]; exact congrArg _ (decide_eq_decide.mpr Iff.rfl)) only_ID_datatype

theorem only_2 (events : alloc.vec.Vec rdfxml.Event) :
    rdfxml.within events 2#u8 0#usize = .ok (decide (Only (evsOf events) [rdfName "ID", rdfName "parseType"])) :=
  within_only events 2#u8 (fun c => c = 1 ∨ c = 5) _
    (fun c => by rw [allows_2]; exact congrArg _ (decide_eq_decide.mpr Iff.rfl)) only_ID_parseType

theorem literal_witness (c : Ctx) (evs : List (Word × Word)) (v : Word) (o : Term) (h : TextObject c evs v o)
    (lim : c.termLimit ≤ Usize.max) : ∃ l : rdf.RdfLiteral, literalTerm l = o := by
  rcases (textObject_iff _ _ _ _).mp h with ⟨d, -, t⟩ | ⟨-, lo⟩
  · obtain ⟨b, i, sp, io, -, rfl⟩ := (typedOf_iff _ _ _ _).mp t
    have bb : b.length ≤ Usize.max := by have := sp.2.2; omega
    have bi : i.length ≤ Usize.max := by have := io.1.2.2; omega
    exact ⟨⟨alloc.vec.Vec.from b bb, .Datatype ⟨alloc.vec.Vec.from i bi⟩⟩, by simp [literalTerm]⟩
  · rcases (literalOf_iff _ _ _).mp lo with ⟨-, b, sp, rfl⟩ | ⟨-, b, g, sp, sg, -, rfl⟩
    · have bb : b.length ≤ Usize.max := by have := sp.2.2; omega
      have bx : xsdString.length ≤ Usize.max := by rw [xsdString_eq]; simp; scalar_tac
      exact ⟨⟨alloc.vec.Vec.from b bb, .Datatype ⟨alloc.vec.Vec.from xsdString bx⟩⟩, by simp [literalTerm]⟩
    · have bb : b.length ≤ Usize.max := by have := sp.2.2; omega
      have bg : g.length ≤ Usize.max := by have := sg.2.2; omega
      exact ⟨⟨alloc.vec.Vec.from b bb, .Language (alloc.vec.Vec.from g bg)⟩, by simp [literalTerm]⟩

theorem objectTerm_literal (l : rdf.RdfLiteral) : objectTerm (.Literal l) = literalTerm l := rfl

theorem literal_property_spec (c : Ctx) (e : xml.Element) (p : rdfxml.Prepared) (subject : rdf.Subject)
    (predicate : rdf.RdfIri) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ag : Agrees c p.base p.lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.literal_property e p subject predicate limits state = .ok r ∧
      StateSpec r state limits
        (LiteralBody c (evsOf p.events) e (subjectTerm subject) predicate.spelling.val (stOf state)) := by
  unfold rdfxml.literal_property
  rw [only_1]
  have lim : c.termLimit ≤ Usize.max := by rw [ag.hterm]; exact Rowl.XmlScan.usize_le_max _
  by_cases onl : Only (evsOf p.events) [rdfName "ID", rdfName "datatype"]
  · simp only [onl, decide_true, ite_true, bind_ok]
    by_cases one : e.children.val.length = 1
    · have one' : alloc.vec.Vec.len e.children = 1#usize := UScalar.eq_of_val_eq (by simpa using one)
      have z : (0#usize).val < e.children.val.length := by simp; omega
      simp only [one', ite_true, index_eq e.children 0#usize z, bind_ok]
      obtain ⟨node, hnode⟩ : ∃ n, e.children.val = [n] := by
        match h : e.children.val, one with
        | [n], _ => exact ⟨n, rfl⟩
      have g0 : e.children.val[(0#usize).val]'z = node := by simp [hnode]
      rw [g0]
      cases node with
      | Element _ =>
        refine ⟨.Err .InvalidContent, rfl, by simp, ?_⟩
        rintro ts st' ⟨-, t, o, ch, -⟩ _ _ _
        rw [hnode] at ch; simp at ch
      | Text t =>
        simp only
        obtain ⟨r1, hr1, hc1⟩ := text_literal_spec c t p scope limits ag
        rw [hr1]; simp only [bind_ok]
        cases r1 with
        | Err err =>
          refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
          rintro ts st' ⟨-, t', o, ch, tob, -⟩ _ _ _
          rw [hnode] at ch; simp at ch; subst ch
          obtain ⟨l, hl⟩ := literal_witness _ _ _ _ tob lim
          have := (hc1 l).mpr (by rw [hl]; exact tob)
          simp at this
        | Ok lit =>
          have tob := (hc1 lit).mp rfl
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          obtain ⟨r, hr, sound, complete⟩ := stated_spec c subject predicate (.Literal lit) p scope limits state ag fits
          refine ⟨r, hr, fun s' e' => ?_, fun ts st' h hl hb hi => ?_⟩
          · obtain ⟨ts, h1, h2, h3⟩ := sound s' e'
            exact ⟨ts, ⟨onl, t, _, hnode, tob, by simpa [objectTerm_literal] using h1⟩, h2, h3⟩
          · obtain ⟨-, t', o, ch, tob2, st2⟩ := h
            rw [hnode] at ch; simp at ch; subst ch
            have : literalTerm lit = o := by
              rcases (textObject_iff _ _ _ _).mp tob with ⟨d, a, t1⟩ | ⟨a, l1⟩ <;>
              rcases (textObject_iff _ _ _ _).mp tob2 with ⟨d', a', t2⟩ | ⟨a', l2⟩
              · rw [a] at a'; simp only [Option.some.injEq] at a'; subst a'
                obtain ⟨b, i, sp, io, -, e1⟩ := (typedOf_iff _ _ _ _).mp t1
                obtain ⟨b', i', sp', io', -, e2⟩ := (typedOf_iff _ _ _ _).mp t2
                rw [e1, e2, spelled_unique sp sp', spelled_unique io.1 io'.1]
              · rw [a] at a'; cases a'
              · rw [a] at a'; cases a'
              · rcases (literalOf_iff _ _ _).mp l1 with ⟨h0, b, sp, e1⟩ | ⟨h0, b, g, sp, sg, -, e1⟩ <;>
                rcases (literalOf_iff _ _ _).mp l2 with ⟨h0', b', sp', e2⟩ | ⟨h0', b', g', sp', sg', -, e2⟩
                · rw [e1, e2, spelled_unique sp sp']
                · exact absurd h0 h0'
                · exact absurd h0' h0
                · rw [e1, e2, spelled_unique sp sp', spelled_unique sg sg']
            exact complete ts st' (by simpa [objectTerm_literal, this] using st2) hl hb hi
    · have one' : ¬ alloc.vec.Vec.len e.children = 1#usize := fun h => one (by simpa using congrArg UScalar.val h)
      simp only [one', ite_false]
      refine ⟨.Err .InvalidContent, rfl, by simp, ?_⟩
      rintro ts st' ⟨-, t, o, ch, -⟩ _ _ _
      rw [ch] at one; simp at one
  · simp only [onl, decide_false, Bool.false_eq_true, ite_false, bind_ok]
    refine ⟨.Err .InvalidAttributes, rfl, by simp, ?_⟩
    rintro ts st' ⟨o, -⟩ _ _ _
    exact absurd o onl

/-! ## Empty property elements -/

theorem stated_mono {c : Ctx} {evs : List (Word × Word)} {t : Statement} {st : St} {ts : List Statement} {st' : St}
    (h : Stated c evs t st ts st') : st.blanks = st'.blanks ∧ st.ids.length ≤ st'.ids.length := by
  rcases (stated_iff ..).mp h with ⟨-, -, rfl⟩ | ⟨v, i, -, ii, -⟩
  · exact ⟨rfl, le_refl _⟩
  · obtain ⟨b, l⟩ := idIri_blanks ii; exact ⟨b.symm, by omega⟩

/-- The triples of an empty property element with an object resource. -/
def ResourceBody (c : Ctx) (evs : List (Word × Word)) (s : Term) (p : List U8) (st : St) (ts : List Statement)
    (st' : St) : Prop :=
  ¬ Only evs [rdfName "ID"] ∧ attrValue (rdfName "datatype") evs = none ∧ EmptyAttributes evs ∧
  ∃ r st1 tsa ts2, EmptyObject c evs st r st1 ∧ PropAttrs c r evs tsa ∧ Stated c evs ⟨s, p, r⟩ st1 ts2 st' ∧
    ts = tsa ++ ts2

/-- The triples of an empty property element without rdf:parseType. -/
def EmptyBody (c : Ctx) (evs : List (Word × Word)) (s : Term) (p : List U8) (st : St) (ts : List Statement)
    (st' : St) : Prop :=
  (Only evs [rdfName "ID"] ∧ ∃ o, LiteralOf c [] o ∧ Stated c evs ⟨s, p, o⟩ st ts st') ∨
  (Only evs [rdfName "ID", rdfName "datatype"] ∧ ∃ d o, attrValue (rdfName "datatype") evs = some d ∧
    TypedOf c [] d o ∧ Stated c evs ⟨s, p, o⟩ st ts st') ∨
  ResourceBody c evs s p st ts st'

theorem has_none (evs : List (Word × Word)) (u : Word) : ¬ Has evs u ↔ attrValue u evs = none := by
  rw [has_iff]; simp

theorem only_has (evs : List (Word × Word)) (us : List Word) (u : Word) (h : Only evs us) (hu : u ∉ us) :
    ¬ Has evs u := by
  rintro ⟨v, hv⟩; exact hu (by simpa using h _ hv)

theorem emptyAttributes_iff (events : alloc.vec.Vec rdfxml.Event) :
    EmptyAttributes (evsOf events) ↔ (∀ ev ∈ evsOf events, classOf ev.1 = 0 ∨ classOf ev.1 = 1 ∨
      classOf ev.1 = 2 ∨ classOf ev.1 = 4) ∧
      ¬ (Has (evsOf events) (rdfName "nodeID") ∧ Has (evsOf events) (rdfName "resource")) := by
  unfold EmptyAttributes
  rw [classes_mem (evsOf events) (fun c => c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 4)
    (fun u => u = rdfName "ID" ∨ u = rdfName "resource" ∨ u = rdfName "nodeID" ∨ PropertyAttributeUri u)
    (fun u => by rw [classOf_zero, classOf_ID, classOf_nodeID, classOf_resource]; tauto)]
  constructor
  · rintro ⟨a, b⟩; exact ⟨a, fun ⟨x, y⟩ => b ⟨y, x⟩⟩
  · rintro ⟨a, b⟩; exact ⟨a, fun ⟨x, y⟩ => b ⟨y, x⟩⟩

theorem empty_resource_spec (c : Ctx) (p : rdfxml.Prepared) (subject : rdf.Subject) (predicate : rdf.RdfIri)
    (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ag : Agrees c p.base p.lang scope limits) (fits : Fits limits state)
    (notId : ¬ Only (evsOf p.events) [rdfName "ID"]) :
    ∃ r, rdfxml.empty_resource p subject predicate scope limits state = .ok r ∧
      StateSpec r state limits
        (ResourceBody c (evsOf p.events) (subjectTerm subject) predicate.spelling.val (stOf state)) := by
  unfold rdfxml.empty_resource
  rw [lacks_eq p.events 6#u8 _ class_names_datatype]
  by_cases dt : Has (evsOf p.events) (rdfName "datatype")
  · simp only [dt, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false, bind_ok]
    refine ⟨.Err .UnsupportedDatatype, rfl, by simp, ?_⟩
    rintro ts st' ⟨-, nd, -⟩ _ _ _
    exact absurd ((has_none _ _).mpr nd) (not_not.mpr dt)
  · simp only [dt, not_false_eq_true, decide_true, ite_true, bind_ok]
    have hd : attrValue (rdfName "datatype") (evsOf p.events) = none := (has_none _ _).mp dt
    rw [within_eq p.events 3#u8 (fun c => c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 4)
      (fun c => by rw [allows_3]; exact congrArg _ (decide_eq_decide.mpr Iff.rfl)) 0#usize,
      usize_zero_val, List.drop_zero]
    simp only [bind_ok, decide_eq_true_eq]
    by_cases w : ∀ ev ∈ evsOf p.events, classOf ev.1 = 0 ∨ classOf ev.1 = 1 ∨ classOf ev.1 = 2 ∨ classOf ev.1 = 4
    · rw [if_pos w]
      rw [not_both_eq p.events 2#u8 4#u8 _ _ class_names_nodeID class_names_resource]
      simp only [bind_ok, decide_eq_true_eq]
      by_cases nb : ¬ (Has (evsOf p.events) (rdfName "nodeID") ∧ Has (evsOf p.events) (rdfName "resource"))
      · rw [if_pos nb]
        have ea : EmptyAttributes (evsOf p.events) := (emptyAttributes_iff p.events).mpr ⟨w, nb⟩
        obtain ⟨r1, hr1, s1, c1⟩ := empty_object_spec c p scope limits state ag fits
        rw [hr1]; simp only [bind_ok]
        cases r1 with
        | Err e =>
          refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
          rintro ts st' ⟨-, -, -, r, st1, tsa, ts2, eo, pa, sd, rfl⟩ hl hb hi
          obtain ⟨mb, mi⟩ := stated_mono sd
          obtain ⟨_, _, he, -⟩ := c1 r st1 eo (by omega) (by omega)
          cases he
        | Ok pair =>
          obtain ⟨object, state1⟩ := pair
          obtain ⟨eo, htr1, fits1⟩ := s1 object state1 rfl
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          obtain ⟨r2, hr2, s2, c2⟩ := attribute_triples_spec c object p.events 0#usize p.base p.lang scope limits
            state1 ag fits1
          rw [usize_zero_val, List.drop_zero] at s2 c2
          have run1 := hr2
          cases r2 with
          | Err e =>
            refine ⟨.Err e, by simp [hr2, residual], by simp, ?_⟩
            rintro ts st' ⟨-, -, -, r, st1, tsa, ts2, eo2, pa, sd, rfl⟩ hl hb hi
            obtain ⟨mb, mi⟩ := stated_mono sd
            obtain ⟨o2, s2', he, ht2, hs2, htr2⟩ := c1 r st1 eo2 (by omega) (by omega)
            simp at he; obtain ⟨rfl, rfl⟩ := he
            obtain ⟨_, he3, -⟩ := c2 tsa (stOf state1) ⟨by rw [ht2]; exact pa, rfl⟩
              (by rw [stmts, htr1, ← stmts]; simp at hl ⊢; omega) (by rw [hs2]; omega) (by rw [hs2]; omega)
            cases he3
          | Ok state2 =>
            obtain ⟨tsa, ⟨pa, hst2⟩, hs2, fits2⟩ := s2 state2 rfl
            obtain ⟨r3, hr3, s3, c3⟩ := stated_spec c subject predicate (asObject object) p scope limits state2 ag fits2
            refine ⟨r3, by simp [hr2, object_of_eq, hr3], fun s' e => ?_, fun ts st' h hl hb hi => ?_⟩
            · obtain ⟨ts2, sd, hs', fits'⟩ := s3 s' e
              refine ⟨tsa ++ ts2, ⟨notId, hd, ea, subjectTerm object, stOf state1, tsa, ts2, eo, pa, ?_, rfl⟩,
                ?_, fits'⟩
              · rw [← hst2]; simpa [objectTerm_asObject] using sd
              · rw [hs', hs2, stmts, htr1, ← stmts, List.append_assoc]
            · obtain ⟨-, -, -, r, st1, tsa', ts2, eo2, pa2, sd2, rfl⟩ := h
              obtain ⟨mb, mi⟩ := stated_mono sd2
              obtain ⟨o2, s2', he, ht2, hs2', htr2⟩ := c1 r st1 eo2 (by omega) (by omega)
              simp at he; obtain ⟨rfl, rfl⟩ := he
              obtain ⟨s3', he3, hs3, hst3⟩ := c2 tsa' (stOf state1) ⟨by rw [ht2]; exact pa2, rfl⟩
                (by rw [stmts, htr1, ← stmts]; simp at hl ⊢; omega) (by rw [hs2']; omega) (by rw [hs2']; omega)
              simp at he3; subst he3
              have htsa : tsa = tsa' := by
                have := hs2.symm.trans hs3; simpa using this
              subst htsa
              obtain ⟨s4, he4, hs4, hst4⟩ := c3 ts2 st' (by rw [hst2, hs2']; simpa [objectTerm_asObject, ht2] using sd2)
                (by rw [hs2, stmts, htr1, ← stmts]; simpa [List.append_assoc] using hl) hb hi
              exact ⟨s4, he4, by rw [hs4, hs2, stmts, htr1, ← stmts, List.append_assoc], hst4⟩
      · rw [if_neg nb]
        refine ⟨.Err .InvalidAttributes, rfl, by simp, ?_⟩
        rintro ts st' ⟨-, -, ea, -⟩ _ _ _
        exact (nb ((emptyAttributes_iff p.events).mp ea).2).elim
    · rw [if_neg w]
      refine ⟨.Err .InvalidAttributes, rfl, by simp, ?_⟩
      rintro ts st' ⟨-, -, ea, -⟩ _ _ _
      exact (w ((emptyAttributes_iff p.events).mp ea).1).elim

theorem word_new : word (alloc.vec.Vec.new U32) = [] := by simp [word]

theorem only_sub (evs : List (Word × Word)) (h : Only evs [rdfName "ID"]) :
    Only evs [rdfName "ID", rdfName "datatype"] := by
  intro ev m; have := h ev m; simp at this ⊢; exact .inl this

theorem empty_property_spec (c : Ctx) (p : rdfxml.Prepared) (subject : rdf.Subject) (predicate : rdf.RdfIri)
    (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ag : Agrees c p.base p.lang scope limits) (fits : Fits limits state) :
    ∃ r, rdfxml.empty_property p subject predicate scope limits state = .ok r ∧
      StateSpec r state limits
        (EmptyBody c (evsOf p.events) (subjectTerm subject) predicate.spelling.val (stOf state)) := by
  unfold rdfxml.empty_property
  have lim : c.termLimit ≤ Usize.max := by rw [ag.hterm]; exact Rowl.XmlScan.usize_le_max _
  rw [only_0]
  simp only [bind_ok, decide_eq_true_eq]
  by_cases o0 : Only (evsOf p.events) [rdfName "ID"]
  · rw [if_pos o0]
    obtain ⟨r1, hr1, hc1⟩ := literal_of_eq c (alloc.vec.Vec.new U32) p.lang limits ag.hlang ag.hterm
    rw [word_new] at hc1
    rw [hr1]; simp only [bind_ok]
    cases r1 with
    | Err e =>
      refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
      rintro ts st' (⟨-, o, lo, -⟩ | ⟨-, d, o, hd, -⟩ | ⟨n0, -⟩) _ _ _
      · obtain ⟨l, hl⟩ := literal_witness c [] [] o (.plain rfl lo) lim
        have := (hc1 l).mpr (by rw [hl]; exact lo)
        simp at this
      · have := (has_none _ _).mp (only_has _ _ (rdfName "datatype") o0 (by decide))
        rw [this] at hd; cases hd
      · exact absurd o0 n0
    | Ok lit =>
      have lo := (hc1 lit).mp rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨r, hr, sound, complete⟩ := stated_spec c subject predicate (.Literal lit) p scope limits state ag fits
      refine ⟨r, hr, fun s' e => ?_, fun ts st' h hl hb hi => ?_⟩
      · obtain ⟨ts, sd, hs, hf⟩ := sound s' e
        exact ⟨ts, .inl ⟨o0, _, lo, by simpa [objectTerm_literal] using sd⟩, hs, hf⟩
      · rcases h with ⟨-, o, lo2, sd⟩ | ⟨-, d, o, hd, -⟩ | ⟨n0, -⟩
        · have : literalTerm lit = o := by
            rcases (literalOf_iff _ _ _).mp lo with ⟨h0, b, sp, e1⟩ | ⟨h0, b, g, sp, sg, -, e1⟩ <;>
            rcases (literalOf_iff _ _ _).mp lo2 with ⟨h0', b', sp', e2⟩ | ⟨h0', b', g', sp', sg', -, e2⟩
            · rw [e1, e2, spelled_unique sp sp']
            · exact absurd h0 h0'
            · exact absurd h0' h0
            · rw [e1, e2, spelled_unique sp sp', spelled_unique sg sg']
          exact complete ts st' (by simpa [objectTerm_literal, this] using sd) hl hb hi
        · have := (has_none _ _).mp (only_has _ _ (rdfName "datatype") o0 (by decide))
          rw [this] at hd; cases hd
        · exact absurd o0 n0
  · rw [if_neg o0, only_1]
    simp only [bind_ok, decide_eq_true_eq]
    by_cases o1 : Only (evsOf p.events) [rdfName "ID", rdfName "datatype"]
    · rw [if_pos o1]
      have hdt : ∃ d, attrValue (rdfName "datatype") (evsOf p.events) = some d := by
        by_contra none_
        apply o0
        intro ev m
        have h1 := o1 ev m
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 ⊢
        rcases h1 with h1 | h1
        · exact h1
        · exfalso; apply none_
          have : attrValue (rdfName "datatype") (evsOf p.events) ≠ none := by
            rw [← has_iff]; exact ⟨ev.2, by rw [← h1]; exact m⟩
          obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp this
          exact ⟨d, hd⟩
      obtain ⟨d, hd⟩ := hdt
      obtain ⟨r1, hr1, hc1⟩ := text_literal_spec c (alloc.vec.Vec.new U32) p scope limits ag
      rw [word_new] at hc1
      rw [hr1]; simp only [bind_ok]
      cases r1 with
      | Err e =>
        refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
        rintro ts st' (⟨o0', -⟩ | ⟨-, d', o, hd', ty, -⟩ | ⟨-, nd, -⟩) _ _ _
        · exact absurd o0' o0
        · obtain ⟨l, hl⟩ := literal_witness c (evsOf p.events) [] o (.typed hd' ty) lim
          have := (hc1 l).mpr (by rw [hl]; exact .typed hd' ty)
          simp at this
        · rw [hd] at nd; cases nd
      | Ok lit =>
        have tob := (hc1 lit).mp rfl
        have ty : TypedOf c [] d (literalTerm lit) := by
          rcases (textObject_iff _ _ _ _).mp tob with ⟨d', hd', t⟩ | ⟨nd, -⟩
          · rw [hd] at hd'; simp only [Option.some.injEq] at hd'; subst hd'; exact t
          · rw [hd] at nd; cases nd
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        obtain ⟨r, hr, sound, complete⟩ := stated_spec c subject predicate (.Literal lit) p scope limits state ag fits
        refine ⟨r, hr, fun s' e => ?_, fun ts st' h hl hb hi => ?_⟩
        · obtain ⟨ts, sd, hs, hf⟩ := sound s' e
          exact ⟨ts, .inr (.inl ⟨o1, d, _, hd, ty, by simpa [objectTerm_literal] using sd⟩), hs, hf⟩
        · rcases h with ⟨o0', -⟩ | ⟨-, d', o, hd', ty2, sd⟩ | ⟨-, nd, -⟩
          · exact absurd o0' o0
          · rw [hd] at hd'; simp only [Option.some.injEq] at hd'; subst hd'
            have : literalTerm lit = o := by
              obtain ⟨b, i, sp, io, -, e1⟩ := (typedOf_iff _ _ _ _).mp ty
              obtain ⟨b', i', sp', io', -, e2⟩ := (typedOf_iff _ _ _ _).mp ty2
              rw [e1, e2, spelled_unique sp sp', spelled_unique io.1 io'.1]
            exact complete ts st' (by simpa [objectTerm_literal, this] using sd) hl hb hi
          · rw [hd] at nd; cases nd
    · rw [if_neg o1]
      obtain ⟨r, hr, sound, complete⟩ := empty_resource_spec c p subject predicate scope limits state ag fits o0
      refine ⟨r, hr, fun s' e => ?_, fun ts st' h hl hb hi => ?_⟩
      · obtain ⟨ts, rb, hs, hf⟩ := sound s' e
        exact ⟨ts, .inr (.inr rb), hs, hf⟩
      · rcases h with ⟨o0', -⟩ | ⟨o1', -⟩ | rb
        · exact absurd o0' o0
        · exact absurd o1' o1
        · exact complete ts st' rb hl hb hi

/-! ## Names of node and property elements -/

theorem classOf_seven (u : Word) (h : classOf u = 7) :
    u = rdfName "RDF" ∨ u = rdfName "Description" ∨ u = rdfName "li" ∨ u ∈ oldTerms := by
  unfold classOf at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 <;> first | omega | assumption

theorem classOf_core (u : Word) (h1 : classOf u ≠ 0) (h7 : classOf u ≠ 7) : u ∈ coreSyntaxTerms := by
  rw [core_mem]
  unfold classOf at h1 h7
  split_ifs at h1 h7 with a1 a2 a3 a4 a5 a6 a7 <;> simp_all

theorem description_node : NodeElementUri (rdfName "Description") := by
  unfold NodeElementUri; rw [core_mem, old_mem]; decide

theorem not_node_of_core {u : Word} (h : u ∈ coreSyntaxTerms) : ¬ NodeElementUri u := fun n => n.1 h

theorem node_uri_eq (uri : alloc.vec.Vec U32) : rdfxml.node_uri uri = .ok (decide (NodeElementUri (word uri))) := by
  unfold rdfxml.node_uri
  obtain ⟨k, hk, hkv⟩ := class_of_eq uri
  rw [hk]; simp only [bind_ok]
  split
  · have c0 : classOf (word uri) = 0 := by rw [← hkv]; rfl
    have pa := (classOf_zero _).mp c0
    have : NodeElementUri (word uri) := ⟨pa.1, pa.2.2.1, pa.2.2.2⟩
    simp [this]
  · have c7 : classOf (word uri) = 7 := by rw [← hkv]; rfl
    unfold rdfxml.node_syntax
    simp only [lift, bind_ok, is_rdf_Description]
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · intro e; rw [e]; exact description_node
    · intro n
      rcases classOf_seven _ c7 with e | e | e | e
      · exact absurd (by rw [e, core_mem]; simp) n.1
      · exact e
      · exact absurd e n.2.1
      · exact absurd e n.2.2
  · next _ h0 h7 =>
    have c0 : classOf (word uri) ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq (by rw [hkv, e]; rfl))
    have c7 : classOf (word uri) ≠ 7 := fun e => h7 (UScalar.eq_of_val_eq (by rw [hkv, e]; rfl))
    have := not_node_of_core (classOf_core _ c0 c7)
    simp [this]

theorem property_uri_eq (uri : alloc.vec.Vec U32) (nl : word uri ≠ rdfName "li") :
    rdfxml.property_uri uri = .ok (decide (PropertyElementUri (word uri))) := by
  unfold rdfxml.property_uri
  obtain ⟨k, hk, hkv⟩ := class_of_eq uri
  rw [hk]; simp only [bind_ok]
  split
  · have c0 : classOf (word uri) = 0 := by rw [← hkv]; rfl
    have pa := (classOf_zero _).mp c0
    have : PropertyElementUri (word uri) := ⟨pa.1, pa.2.1, pa.2.2.2⟩
    simp [this]
  · have c7 : classOf (word uri) = 7 := by rw [← hkv]; rfl
    unfold rdfxml.property_syntax
    simp only [lift, bind_ok, is_rdf_li]
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · intro e; exact absurd e nl
    · intro n
      rcases classOf_seven _ c7 with e | e | e | e
      · exact absurd (by rw [e, core_mem]; simp) n.1
      · exact absurd e n.2.1
      · exact e
      · exact absurd e n.2.2
  · next _ h0 h7 =>
    have c0 : classOf (word uri) ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq (by rw [hkv, e]; rfl))
    have c7 : classOf (word uri) ≠ 7 := fun e => h7 (UScalar.eq_of_val_eq (by rw [hkv, e]; rfl))
    have : ¬ PropertyElementUri (word uri) := fun n => n.1 (classOf_core _ c0 c7)
    simp [this]

theorem predicate_iff (c : Ctx) (e : xml.Element) (li : Nat) (p : List U8) (n : Nat) :
    Predicate c e li p n ↔
      (ElementUri c.termLimit e (rdfName "li") ∧ li < c.itemLimit ∧ IriOf c (memberUri li) p ∧ n = li + 1) ∨
      (∃ u, ElementUri c.termLimit e u ∧ u ≠ rdfName "li" ∧ PropertyElementUri u ∧ IriOf c u p ∧ n = li) := by
  constructor
  · intro h; cases h with
    | member a b d => exact .inl ⟨a, b, d, rfl⟩
    | named a b d f => exact .inr ⟨_, a, b, d, f, rfl⟩
  · rintro (⟨a, b, d, rfl⟩ | ⟨u, a, b, d, f, rfl⟩)
    · exact .member a b d
    · exact .named a b d f

theorem iri_bound (c : Ctx) (u : Word) (p : List U8) (h : IriOf c u p) (lim : c.termLimit ≤ Usize.max) :
    p.length ≤ Usize.max := by have := h.1.2.2; omega

theorem predicate_of_spec (c : Ctx) (e : xml.Element) (li : Usize) (limits : rdfxml.Limits)
    (ht : c.termLimit = limits.term_bytes.val) (hi : c.itemLimit = limits.items.val) :
    ∃ r, rdfxml.predicate_of e li limits = .ok r ∧
      (∀ i n, r = .Ok (i, n) → Predicate c e li.val i.spelling.val n.val) ∧
      (∀ p n, Predicate c e li.val p n → ∃ i n', r = .Ok (i, n') ∧ i.spelling.val = p ∧ n'.val = n) := by
  unfold rdfxml.predicate_of
  have lim : c.termLimit ≤ Usize.max := by rw [ht]; exact Rowl.XmlScan.usize_le_max _
  obtain ⟨r1, hr1, s1, c1⟩ := element_uri_spec e limits
  rw [hr1]; simp only [bind_ok]
  cases r1 with
  | Err err =>
    refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
    intro p n h
    rcases (predicate_iff ..).mp h with ⟨eu, -⟩ | ⟨u, eu, -⟩
    · obtain ⟨v, hv, -⟩ := c1 _ (by rw [← ht]; exact eu); cases hv
    · obtain ⟨v, hv, -⟩ := c1 _ (by rw [← ht]; exact eu); cases hv
  | Ok uri =>
    have eu := s1 uri rfl
    rw [← ht] at eu
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, is_rdf_li, decide_eq_true_eq]
    by_cases isli : word uri = rdfName "li"
    · rw [if_pos isli]
      by_cases lt : li.val < limits.items.val
      · have lt' : li < limits.items := by simpa [UScalar.lt_equiv] using lt
        rw [if_pos lt']
        generalize hs : Array.to_slice (Array.make 44#usize _ _) = sl
        have sv : sl.val.map (·.val) = rdfName "_" := by rw [← hs, slice_val]; decide
        obtain ⟨v, hv, hw⟩ := ascii_word_eq sl
        have vl : v.val.length + 20 ≤ Usize.max := by
          have := congrArg List.length hw; rw [sv] at this
          have h44 : (rdfName "_").length = 44 := by decide
          simp [word] at this; rw [h44] at this; scalar_tac
        obtain ⟨member, hm, hmw⟩ := digit_points_eq li v vl
        rw [hw, sv] at hmw
        have hmw' : word member = memberUri li.val := hmw
        rw [hv]; simp only [bind_ok, hm]
        obtain ⟨r2, hr2, hc2⟩ := iri_of_eq member limits
        rw [hr2]; simp only [bind_ok]
        cases r2 with
        | Err err =>
          refine ⟨.Err err, by simp [residual], by simp, ?_⟩
          intro p n h
          rcases (predicate_iff ..).mp h with ⟨-, -, io, -⟩ | ⟨u, eu2, nl, -⟩
          · have := (hc2 ⟨alloc.vec.Vec.from p (iri_bound _ _ _ io lim)⟩).mpr (by
              rw [hmw', ← ht]; simpa using (show Spelled c.termLimit (memberUri li.val) p ∧
                Rowl.NTriples.AbsoluteIri p from io))
            simp at this
          · exact absurd ((elementUri_unique eu2 eu).trans isli) nl
        | Ok iri =>
          have io := (hc2 iri).mp rfl
          rw [hmw'] at io
          obtain ⟨n1, hn1, hn1v⟩ := Rowl.XmlScan.succ_spec lt
          refine ⟨.Ok (iri, n1), by simp [hn1], fun i n e1 => ?_, fun p n h => ?_⟩
          · simp at e1; obtain ⟨rfl, rfl⟩ := e1
            refine (predicate_iff ..).mpr (.inl ⟨by rw [← isli]; exact eu, by rw [hi]; exact lt, ?_, hn1v⟩)
            unfold IriOf; rw [ht]; exact io
          · rcases (predicate_iff ..).mp h with ⟨-, -, io2, rfl⟩ | ⟨u, eu2, nl, -⟩
            · exact ⟨iri, n1, rfl, spelled_unique (by rw [ht]; exact io.1) io2.1, hn1v⟩
            · exact absurd ((elementUri_unique eu2 eu).trans isli) nl
      · have lt' : ¬ li < limits.items := by simpa [UScalar.lt_equiv] using lt
        rw [if_neg lt']
        refine ⟨.Err .ResourceLimit, rfl, by simp, ?_⟩
        intro p n h
        rcases (predicate_iff ..).mp h with ⟨-, l, -⟩ | ⟨u, eu2, nl, -⟩
        · rw [hi] at l; exact absurd l lt
        · exact absurd ((elementUri_unique eu2 eu).trans isli) nl
    · rw [if_neg isli, property_uri_eq uri isli]
      simp only [bind_ok, decide_eq_true_eq]
      by_cases pe : PropertyElementUri (word uri)
      · rw [if_pos pe]
        obtain ⟨r2, hr2, hc2⟩ := iri_of_eq uri limits
        rw [hr2]; simp only [bind_ok]
        cases r2 with
        | Err err =>
          refine ⟨.Err err, by simp [residual], by simp, ?_⟩
          intro p n h
          rcases (predicate_iff ..).mp h with ⟨eu2, -⟩ | ⟨u, eu2, -, -, io, -⟩
          · exact absurd (elementUri_unique eu eu2) isli
          · have hu := elementUri_unique eu2 eu
            subst hu
            have := (hc2 ⟨alloc.vec.Vec.from p (iri_bound _ _ _ io lim)⟩).mpr (by
              rw [← ht]; simpa using (show Spelled c.termLimit (word uri) p ∧ Rowl.NTriples.AbsoluteIri p from io))
            simp at this
        | Ok iri =>
          have io := (hc2 iri).mp rfl
          refine ⟨.Ok (iri, li), by simp, fun i n e1 => ?_, fun p n h => ?_⟩
          · simp at e1; obtain ⟨rfl, rfl⟩ := e1
            exact (predicate_iff ..).mpr (.inr ⟨_, eu, isli, pe, by unfold IriOf; rw [ht]; exact io, rfl⟩)
          · rcases (predicate_iff ..).mp h with ⟨eu2, -⟩ | ⟨u, eu2, -, -, io2, rfl⟩
            · exact absurd (elementUri_unique eu eu2) isli
            · have hu := elementUri_unique eu2 eu
              subst hu
              exact ⟨iri, li, rfl, spelled_unique (by rw [ht]; exact io.1) io2.1, rfl⟩
      · rw [if_neg pe]
        refine ⟨.Err .InvalidName, rfl, by simp, ?_⟩
        intro p n h
        rcases (predicate_iff ..).mp h with ⟨eu2, -⟩ | ⟨u, eu2, -, pe2, -⟩
        · exact absurd (elementUri_unique eu eu2) isli
        · exact absurd (by rw [← elementUri_unique eu2 eu]; exact pe2) pe

/-! ## The production of a property element -/

/-- The production of a property element as `production` numbers it. -/
noncomputable def productionOf (evs : List (Word × Word)) (children : List xml.Node) : Nat :=
  match attrValue (rdfName "parseType") evs with
  | some v => if v = lit "Resource" then 0 else if v = lit "Collection" then 1 else 2
  | none => if children = [] then 3 else if (∃ f, xml.Node.Element f ∈ children) then 4 else 5

theorem parse_kind_eq (value : alloc.vec.Vec U32) :
    ∃ k, rdfxml.parse_kind value = .ok k ∧
      k.val = if word value = lit "Resource" then 0 else if word value = lit "Collection" then 1 else 2 := by
  unfold rdfxml.parse_kind
  simp only [lift, bind_ok, is_ascii_lit, lit_Resource, lit_Collection, decide_eq_true_eq]
  by_cases a : word value = lit "Resource"
  · rw [if_pos a, if_pos a]; exact ⟨_, rfl, rfl⟩
  · rw [if_neg a, if_neg a]
    by_cases b : word value = lit "Collection"
    · rw [if_pos b, if_pos b]; exact ⟨_, rfl, rfl⟩
    · rw [if_neg b, if_neg b]; exact ⟨_, rfl, rfl⟩

theorem has_element_eq (children : alloc.vec.Vec xml.Node) (i : Usize) :
    rdfxml.has_element children i = .ok (decide (∃ f, xml.Node.Element f ∈ children.val.drop i.val)) := by
  rw [rdfxml.has_element]
  by_cases lt : i.val < children.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len children) (by simpa using lt)
    have d : children.val.drop i.val = children.val[i.val] :: children.val.drop i1.val := by
      rw [hi1v, List.drop_eq_getElem_cons lt]
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq children i lt]
    rw [d]
    cases h : children.val[i.val] with
    | Element f => simp only; exact congrArg _ (by simp)
    | Text t =>
      simp only [hi1, bind_ok]
      rw [has_element_eq children i1]
      simp
  · have e : children.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    simp [UScalar.lt_equiv, lt, e]
termination_by children.val.length - i.val
decreasing_by omega

theorem content_kind_eq (children : alloc.vec.Vec xml.Node) :
    ∃ k, rdfxml.content_kind children = .ok k ∧
      k.val = if children.val = [] then 3 else if (∃ f, xml.Node.Element f ∈ children.val) then 4 else 5 := by
  unfold rdfxml.content_kind
  by_cases em : children.val = []
  · have : alloc.vec.Vec.len children = 0#usize := UScalar.eq_of_val_eq (by simp [em])
    rw [if_pos this, if_pos em]; exact ⟨_, rfl, rfl⟩
  · have : ¬ alloc.vec.Vec.len children = 0#usize := fun h => em (by
      have := congrArg UScalar.val h; simpa using this)
    rw [if_neg this, if_neg em, has_element_eq, usize_zero_val, List.drop_zero]
    simp only [bind_ok, decide_eq_true_eq]
    by_cases he : ∃ f, xml.Node.Element f ∈ children.val
    · rw [if_pos he, if_pos he]; exact ⟨_, rfl, rfl⟩
    · rw [if_neg he, if_neg he]; exact ⟨_, rfl, rfl⟩

theorem production_eq (e : xml.Element) (p : rdfxml.Prepared) :
    ∃ k, rdfxml.production e p.events = .ok k ∧ k.val = productionOf (evsOf p.events) e.children.val := by
  unfold rdfxml.production productionOf
  obtain ⟨o, ho, n, sm⟩ := find_value p 5#u8 _ class_names_parseType
  rw [ho]; simp only [bind_ok]
  cases o with
  | none =>
    rw [n rfl]
    exact content_kind_eq e.children
  | some j =>
    obtain ⟨jin, hv⟩ := sm j rfl
    rw [hv]
    simp only [index_eq p.events j jin, bind_ok]
    exact parse_kind_eq _

/-! ## The single node element of a resource property element -/

theorem allWs_cons (x : xml.Node) (l : List xml.Node) : AllWs (x :: l) ↔ (∃ t, x = .Text t ∧ Ws (word t)) ∧ AllWs l := by
  simp [AllWs]

theorem allWs_nil : AllWs [] := by simp [AllWs]

theorem single_found (children : alloc.vec.Vec xml.Node) (i j : Usize) :
    ∃ r, rdfxml.single_element children i (some j) = .ok r ∧
      ∀ k, r = .Ok k ↔ (AllWs (children.val.drop i.val) ∧ k = j) := by
  rw [rdfxml.single_element]
  by_cases lt : i.val < children.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len children) (by simpa using lt)
    have d : children.val.drop i.val = children.val[i.val] :: children.val.drop i1.val := by
      rw [hi1v, List.drop_eq_getElem_cons lt]
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq children i lt]
    rw [d]
    cases h : children.val[i.val] with
    | Element f =>
      refine ⟨.Err .InvalidContent, rfl, fun k => ?_⟩
      simp [allWs_cons]
    | Text t =>
      simp only [spaces_from_eq, usize_zero_val, List.drop_zero, bind_ok, decide_eq_true_eq]
      by_cases ws : Ws (word t)
      · rw [if_pos ws]; simp only [hi1, bind_ok]
        obtain ⟨r, hr, hc⟩ := single_found children i1 j
        refine ⟨r, hr, fun k => ?_⟩
        rw [hc k, allWs_cons]
        simp [ws]
      · rw [if_neg ws]
        refine ⟨.Err .InvalidContent, rfl, fun k => ?_⟩
        simp [allWs_cons, ws]
  · have e : children.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨.Ok j, by simp [UScalar.lt_equiv, lt], fun k => ?_⟩
    rw [e]
    simp [allWs_nil, eq_comm]
termination_by children.val.length - i.val
decreasing_by omega

theorem single_none (children : alloc.vec.Vec xml.Node) (i : Usize) :
    ∃ r, rdfxml.single_element children i none = .ok r ∧
      ∀ k, r = .Ok k ↔ ∃ m n post, children.val.drop i.val = m ++ [.Element n] ++ post ∧ AllWs m ∧
        AllWs post ∧ k.val = i.val + m.length := by
  rw [rdfxml.single_element]
  by_cases lt : i.val < children.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len children) (by simpa using lt)
    have d : children.val.drop i.val = children.val[i.val] :: children.val.drop i1.val := by
      rw [hi1v, List.drop_eq_getElem_cons lt]
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq children i lt]
    rw [d]
    cases h : children.val[i.val] with
    | Element f =>
      simp only [hi1, bind_ok]
      obtain ⟨r, hr, hc⟩ := single_found children i1 i
      refine ⟨r, hr, fun k => ?_⟩
      rw [hc k]
      constructor
      · rintro ⟨ws, rfl⟩
        exact ⟨[], f, _, rfl, allWs_nil, ws, by simp⟩
      · rintro ⟨m, n, post, e, wm, wp, hk⟩
        cases m with
        | nil =>
          simp at e; obtain ⟨rfl, rfl⟩ := e
          exact ⟨wp, UScalar.eq_of_val_eq (by simpa using hk)⟩
        | cons x m' =>
          simp at e; obtain ⟨rfl, -⟩ := e
          obtain ⟨⟨t, ht, -⟩, -⟩ := (allWs_cons _ _).mp wm
          cases ht
    | Text t =>
      simp only [spaces_from_eq, usize_zero_val, List.drop_zero, bind_ok, decide_eq_true_eq]
      by_cases ws : Ws (word t)
      · rw [if_pos ws]; simp only [hi1, bind_ok]
        obtain ⟨r, hr, hc⟩ := single_none children i1
        refine ⟨r, hr, fun k => ?_⟩
        rw [hc k]
        constructor
        · rintro ⟨m, n, post, e, wm, wp, hk⟩
          exact ⟨.Text t :: m, n, post, by rw [e]; simp, (allWs_cons _ _).mpr ⟨⟨t, rfl, ws⟩, wm⟩, wp,
            by simp; omega⟩
        · rintro ⟨m, n, post, e, wm, wp, hk⟩
          cases m with
          | nil => simp at e
          | cons x m' =>
            simp at e; obtain ⟨rfl, e⟩ := e
            exact ⟨m', n, post, by simpa using e, ((allWs_cons _ _).mp wm).2, wp, by simp at hk; omega⟩
      · rw [if_neg ws]
        refine ⟨.Err .InvalidContent, rfl, fun k => ?_⟩
        simp only [reduceCtorEq, false_iff, not_exists, not_and]
        intro m n post e wm _ _
        cases m with
        | nil => simp at e
        | cons x m' =>
          simp at e; obtain ⟨rfl, -⟩ := e
          obtain ⟨⟨t', ht, w⟩, -⟩ := (allWs_cons _ _).mp wm
          simp at ht; subst ht; exact ws w
  · have e : children.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨.Err .InvalidContent, by simp [UScalar.lt_equiv, lt], fun k => ?_⟩
    rw [e]
    simp
termination_by children.val.length - i.val
decreasing_by omega

end Rowl.RdfXmlProps
