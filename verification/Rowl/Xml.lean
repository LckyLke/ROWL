import Rowl.XmlDocument
import Rowl.XmlDecode

/-!
# Reading XML documents

`xml::read` returns the element tree of a document exactly when the bytes
are a supported document (`XmlGrammar.Read`): it is sound (a returned tree is
the root of a derivation of the decoded characters within the budget),
complete (every such derivation's root is returned, when the input length
plus the budget fits in a machine word) and total. Since `read` is a
function, every supported document has a single parse.
-/

namespace Rowl.Xml
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs Rowl.XmlEntities Rowl.XmlAttributes Rowl.XmlTags Rowl.XmlNamespaces Rowl.XmlContent Rowl.XmlElements Rowl.XmlComplete Rowl.XmlDecl Rowl.XmlLiterals Rowl.XmlEntityDecls Rowl.XmlDoctype Rowl.XmlSubset Rowl.XmlDocument Rowl.XmlDecode
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

theorem miscs_append {a b : Word} (ha : Miscs a) (hb : Miscs b) : Miscs (a ++ b) := by
  induction ha with
  | nil => simpa using hb
  | comment hc _ ih => simpa [List.append_assoc] using Miscs.comment hc ih
  | pi hp _ ih => simpa [List.append_assoc] using Miscs.pi hp ih
  | space hs _ ih => simpa [List.append_assoc] using Miscs.space hs ih

theorem stackOk_empty (env : alloc.vec.Vec xml.Entity) : StackOk env (alloc.vec.Vec.new Usize) [] := by
  refine ⟨by simp, by simp, by simp⟩

theorem scopeView_new : scopeView (alloc.vec.Vec.new xml.Binding) = [] := by simp [scopeView]

theorem document_sound (cs : alloc.vec.Vec U32) (budget : Usize) (nz : NoZero cs) :
    ∃ r, xml.document cs budget = .ok r ∧
      ∀ d, r = .Ok d → ∃ cost, Document (word cs) d.root cost ∧ cost ≤ budget.val := by
  unfold xml.document
  obtain ⟨r1, h1, s1, _, _⟩ := xml_declaration_spec cs
  cases r1 with
  | Err e => exact ⟨.Err e, by simp [h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
  | Ok i1 =>
    obtain ⟨dcl, dsplit, hdcl, _⟩ := s1 i1 rfl
    obtain ⟨r2, h2, s2⟩ := misc_sound cs i1
    cases r2 with
    | Err e =>
      exact ⟨.Err e, by simp [h1, h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
    | Ok i2 =>
      obtain ⟨m, msplit, hm⟩ := s2 i2 rfl
      obtain ⟨r3, h3, s3, _, _⟩ := doctype_spec cs i2
      cases r3 with
      | Err e =>
        exact ⟨.Err e, by simp [h1, h2, h3, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp⟩
      | Ok pair =>
        obtain ⟨env, i3⟩ := pair
        have hdt := s3 env i3 rfl
        -- the prolog read so far, and the entities it declares
        have prolog : ∃ pro, (∀ m2 more, Miscs m2 → (word cs).drop i3.val = m2 ++ more →
            word cs = pro ++ m2 ++ more ∧ Prolog (pro ++ m2) (envView env)) ∧ EnvOk env := by
          rcases hdt with ⟨rfl, he⟩ | ⟨dt, envs, dtsplit, hdtd, hview, hok⟩
          · refine ⟨dcl ++ m, fun m2 more hm2 d3 => ⟨by rw [dsplit, msplit, d3]; simp, ?_⟩, ?_⟩
            · refine ⟨dcl, m ++ m2, [], by simp, hdcl, miscs_append hm hm2, Or.inl ⟨rfl, ?_⟩⟩
              simp [envView, he]
            · intro e' he'; rw [he] at he'; simp at he'
          · refine ⟨dcl ++ m ++ dt, fun m2 more hm2 d3 => ⟨by rw [dsplit, msplit, dtsplit, d3]; simp, ?_⟩, hok nz⟩
            refine ⟨dcl, m, dt ++ m2, by simp, hdcl, hm, Or.inr ⟨dt, m2, rfl, ?_, hm2⟩⟩
            rw [hview]; exact hdtd
        obtain ⟨pro, hpro, henv⟩ := prolog
        obtain ⟨r4, h4, s4⟩ := misc_sound cs i3
        cases r4 with
        | Err e =>
          exact ⟨.Err e, by simp [h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch, same_residual],
            by simp⟩
        | Ok i4 =>
          obtain ⟨m2, m2split, hm2⟩ := s4 i4 rfl
          obtain ⟨wcs, hpro2⟩ := hpro m2 ((word cs).drop i4.val) hm2 m2split
          by_cases lt : charAt cs i4.val = 60
          · have lt' : atU cs i4.val = 60#u32 := atU_eq (by simpa using lt)
            obtain ⟨r5, h5, s5⟩ := element_sound_of cs i4 env (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) budget
              henv (stackOk_empty env) lt (fun ctx' j b _ _ => content_sound cs j env (alloc.vec.Vec.new _) ctx' b
                (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) henv (stackOk_empty env))
            cases r5 with
            | Err e =>
              exact ⟨.Err e, by simp [h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch, at_eq, lt', h5,
                same_residual], by simp⟩
            | Ok triple =>
              obtain ⟨root, j, b'⟩ := triple
              obtain ⟨body, k, bsplit, hel, hb⟩ := s5 root j b' rfl
              obtain ⟨r6, h6, s6⟩ := misc_sound cs j
              cases r6 with
              | Err e =>
                exact ⟨.Err e, by simp [h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch, at_eq, lt', h5, h6,
                  same_residual], by simp⟩
              | Ok j2 =>
                obtain ⟨tail, tsplit, htail⟩ := s6 j2 rfl
                by_cases fin : j2 = alloc.vec.Vec.len cs
                · refine ⟨.Ok ⟨root⟩, by simp [h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch, at_eq, lt',
                    h5, h6, fin], ?_⟩
                  intro d e; simp at e; subst e
                  have dend : (word cs).drop j2.val = [] := by
                    apply List.drop_eq_nil_of_le; rw [fin]; simp [word_length, alloc.vec.Vec.len_val]
                  refine ⟨k, ⟨pro ++ m2, envView env, body, tail, ?_, hpro2, by simpa [scopeView_new] using hel, htail⟩,
                    by omega⟩
                  rw [wcs, bsplit, tsplit, dend]; simp
                · exact ⟨.Err ⟨.Syntax, j2⟩, by simp [h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch, at_eq,
                    lt', h5, h6, fin, xml.fail], by simp⟩
          · have lt' : ¬ atU cs i4.val = 60#u32 := atU_ne (by simpa using lt)
            have lt'' : ¬ (atU cs i4.val).val = 60 := by rw [atU_val]; exact lt
            exact ⟨.Err ⟨.Syntax, i4⟩, by simp [h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch, at_eq, lt',
              lt'', xml.fail], by simp⟩

/-! ## No XML declaration where the grammar has none -/

/-- What may follow a PI target: its data after white space, or `?>`. -/
theorem pi_rest_head {r y : Word} (hr : r = [] ∨ ∃ s d, r = s ++ d ∧ S s ∧ ¬ Contains (lit "?>") d) :
    ∀ c m, r ++ (lit "?>" ++ y) = c :: m → c = 63 ∨ IsSpace c := by
  intro c m e
  rcases hr with rfl | ⟨s, d, rfl, hs, _⟩
  · rw [lit_pi_end] at e; simp at e; left; exact e.1
  · obtain ⟨s0, s', rfl⟩ := List.exists_cons_of_ne_nil hs.1
    simp at e; rw [← e.1]; right; exact hs.2 s0 (by simp)

theorem pi_no_decl {c y z : Word} {sp : Nat} (hc : PI c) (hsp : IsSpace sp)
    (e : c ++ y = lit "<?xml" ++ sp :: z) : False := by
  obtain ⟨t, r, rfl, ⟨⟨⟨c0, tr, ht, hc0, htr⟩, _⟩, notxml⟩, hr⟩ := hc
  have hr' := pi_rest_head (y := y) hr
  rw [lit_pi, lit_xmlDecl] at e
  simp only [List.cons_append, List.append_assoc, List.cons.injEq, List.nil_append, true_and] at e
  -- e : t ++ (r ++ (lit "?>" ++ y)) = 120 :: 109 :: 108 :: sp :: z
  subst ht
  simp only [List.cons_append, List.cons.injEq] at e
  obtain ⟨rfl, e⟩ := e
  rcases tr with _ | ⟨b, _ | ⟨c, _ | ⟨d, tr'⟩⟩⟩
  · simp at e
    rcases hr' _ _ e with h | h <;> simp [IsSpace] at h
  · simp at e
    obtain ⟨rfl, e⟩ := e
    rcases hr' _ _ e with h | h <;> simp [IsSpace] at h
  · simp at e
    obtain ⟨rfl, rfl, e⟩ := e
    exact notxml ⟨120, 109, 108, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  · simp at e
    obtain ⟨rfl, rfl, rfl, _⟩ := e
    exact space_not_name hsp (htr _ (by simp))

theorem no_xml_decl {cs : alloc.vec.Vec U32} {m rest body more : Word} {envs : Env} {E : Env} {root : xml.Element}
    {k : Nat} (split : word cs = m ++ rest ++ body ++ more) (hm : Miscs m)
    (hrest : (rest = [] ∧ envs = []) ∨ ∃ dt m2, rest = dt ++ m2 ∧ Doctype dt envs ∧ Miscs m2)
    (hel : Element E [] [] body root k) :
    ¬ (lit "<?xml" <+: word cs ∧ IsSpace (charAt cs 5)) := by
  rintro ⟨⟨t, ht⟩, sp5⟩
  have w5 : ∃ z, word cs = lit "<?xml" ++ charAt cs 5 :: z := by
    cases t with
    | nil =>
      exfalso
      have c5 : charAt cs 5 = 0 := by
        have := charAt_after (cs := cs) (i := 0) (w := lit "<?xml") (rest := []) (by rw [List.drop_zero, ← ht])
        simpa [lit_xmlDecl] using this
      rw [c5] at sp5; simp [IsSpace] at sp5
    | cons c t' =>
      have c5 : charAt cs 5 = c := by
        have := charAt_after (cs := cs) (i := 0) (w := lit "<?xml") (rest := c :: t') (by rw [List.drop_zero, ← ht])
        simpa [lit_xmlDecl] using this
      exact ⟨t', by rw [c5, ← ht]⟩
  obtain ⟨z, hz⟩ := w5
  rw [split] at hz
  cases hm with
  | nil =>
    rcases hrest with ⟨rfl, _⟩ | ⟨dt, m2, rfl, ⟨s1, n, p, l, ext, s2, rest', rfl, _⟩, _⟩
    · obtain ⟨c, more', rfl, hc⟩ := element_name_start hel
      rw [lit_xmlDecl] at hz; simp at hz
      rw [hz.1] at hc; simp [NameStartChar] at hc
    · rw [lit_xmlDecl, lit_doctype] at hz; simp at hz
  | @comment c m' hc _ =>
    obtain ⟨b, rfl, _⟩ := hc
    rw [lit_xmlDecl, lit_comment] at hz; simp at hz
  | @pi c m' hc _ =>
    exact pi_no_decl (y := m' ++ rest ++ body ++ more) (z := z) hc sp5 (by rw [← hz]; simp)
  | @space c m' hc _ =>
    obtain ⟨c0, c', rfl⟩ := List.exists_cons_of_ne_nil hc.1
    rw [lit_xmlDecl] at hz; simp at hz
    have := hc.2 c0 (by simp); rw [hz.1] at this; simp [IsSpace] at this

/-! ## Completeness of `document` -/

theorem element_misc_end {E : Env} {names : List Word} {scope : Scope} {w : Word} {e : xml.Element} {k : Nat}
    (h : Element E names scope w e k) (more : Word) : MiscEnd (w ++ more) := by
  obtain ⟨c, rest, rfl, hc⟩ := element_name_start h
  refine ⟨?_, ?_, ?_⟩
  · intro c' m e; simp at e; rw [e.1]; simp [IsSpace]
  · rintro ⟨t, ht⟩; rw [lit_comment] at ht; simp at ht; rw [ht.1] at hc; simp [NameStartChar] at hc
  · rintro ⟨t, ht⟩; rw [lit_pi] at ht; simp at ht; rw [ht.1] at hc; simp [NameStartChar] at hc

theorem doctype_misc_end {dt : Word} {envs : Env} (h : Doctype dt envs) (more : Word) : MiscEnd (dt ++ more) := by
  obtain ⟨s1, n, p, l, ext, s2, rest, rfl, _⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro c m e; rw [lit_doctype] at e; simp at e; rw [e.1]; simp [IsSpace]
  · rintro ⟨t, ht⟩; rw [lit_comment, lit_doctype] at ht; simp at ht
  · rintro ⟨t, ht⟩; rw [lit_pi, lit_doctype] at ht; simp at ht

theorem miscEnd_nil : MiscEnd [] := ⟨by simp, by rintro ⟨t, ht⟩; simp [lit] at ht, by rintro ⟨t, ht⟩; simp [lit] at ht⟩

theorem document_complete (cs : alloc.vec.Vec U32) (budget : Usize) {root : xml.Element} {cost : Nat}
    (h : Document (word cs) root cost) (kb : cost ≤ budget.val) (nz : NoZero cs)
    (room : cs.val.length + cost ≤ Usize.max) :
    xml.document cs budget = .ok (.Ok ⟨root⟩) := by
  obtain ⟨pro, env, body, tail, split, ⟨dcl, m, rest, rfl, hdcl, hm, hrest⟩, hel, htail⟩ := h
  unfold xml.document
  obtain ⟨r1, h1, _, c1, d1⟩ := xml_declaration_spec cs
  have hr1 : ∃ i1 : Usize, r1 = .Ok i1 ∧ i1.val = dcl.length := by
    rcases hdcl with rfl | hd
    · exact ⟨0#usize, d1 (no_xml_decl (more := tail) (by rw [split]; simp) hm hrest hel), rfl⟩
    · exact c1 dcl (m ++ rest ++ body ++ tail) (by rw [split]; simp) hd
  obtain ⟨i1, rfl, hi1⟩ := hr1
  have d1' : (word cs).drop i1.val = m ++ (rest ++ body ++ tail) := by
    rw [hi1]; have := drop_after (cs := cs) (i := 0) (w := dcl) (rest := m ++ (rest ++ body ++ tail))
      (by rw [List.drop_zero, split]; simp)
    simpa using this
  have mend : MiscEnd (rest ++ body ++ tail) := by
    rcases hrest with ⟨rfl, _⟩ | ⟨dt, m2, rfl, hdt, _⟩
    · simpa using element_misc_end hel tail
    · simpa using doctype_misc_end hdt (m2 ++ body ++ tail)
  obtain ⟨i2, h2, hi2⟩ := misc_complete hm cs i1 [] (rest ++ body ++ tail) (by rw [d1']; simp) (by simp [OptS])
    mend nz
  have d2 : (word cs).drop i2.val = rest ++ (body ++ tail) := by
    rw [hi2]; have := drop_after (cs := cs) (i := i1.val) (w := m) (rest := rest ++ (body ++ tail))
      (by rw [d1']; simp)
    simpa using this
  obtain ⟨r3, h3, s3, c3a, c3b⟩ := doctype_spec cs i2
  have step3 : ∃ env' i3 m2, r3 = .Ok (env', i3) ∧ envView env' = env ∧
      (word cs).drop i3.val = m2 ++ (body ++ tail) ∧ Miscs m2 ∧ EnvOk env' ∧
      i3.val + m2.length = i2.val + rest.length := by
    rcases hrest with ⟨rfl, rfl⟩ | ⟨dt, m2, rfl, hdt, hm2⟩
    · have nd : ¬ lit "<!DOCTYPE" <+: (word cs).drop i2.val := by
        obtain ⟨c, more', rfl, hc⟩ := element_name_start hel
        rw [d2, lit_doctype]; rintro ⟨t, ht⟩; simp at ht; rw [ht.1] at hc; simp [NameStartChar] at hc
      refine ⟨_, i2, [], c3a nd, by simp [envView], by simpa using d2, Miscs.nil, by intro e he; simp at he, by simp⟩
    · obtain ⟨env', i3, hr, hview, hi3⟩ := c3b dt env (m2 ++ (body ++ tail)) (by rw [d2]; simp) hdt nz
      have hok : EnvOk env' := by
        rcases s3 env' i3 hr with ⟨_, he⟩ | ⟨_, _, _, _, _, hok⟩
        · intro e he'; rw [he] at he'; simp at he'
        · exact hok nz
      refine ⟨env', i3, m2, hr, hview, ?_, hm2, hok, by rw [hi3]; simp; omega⟩
      rw [hi3]; have := drop_after (cs := cs) (i := i2.val) (w := dt) (rest := m2 ++ (body ++ tail)) (by rw [d2]; simp)
      exact this
  obtain ⟨env', i3, m2, rfl, hview, d3, hm2, hok, hi3⟩ := step3
  obtain ⟨i4, h4, hi4⟩ := misc_complete hm2 cs i3 [] (body ++ tail) (by rw [d3]; simp) (by simp [OptS])
    (element_misc_end hel tail) nz
  have d4 : (word cs).drop i4.val = body ++ tail := by
    rw [hi4]; have := drop_after (cs := cs) (i := i3.val) (w := m2) (rest := body ++ tail) (by rw [d3])
    simpa using this
  have lt : charAt cs i4.val = 60 := by
    obtain ⟨c, more', rfl, _⟩ := element_name_start hel
    exact first_char (rest := c :: more' ++ tail) (by rw [d4]; simp)
  have lt' : atU cs i4.val = 60#u32 := atU_eq (by simpa using lt)
  have blen : body.length ≤ cs.val.length := drop_length_le d4
  obtain ⟨j, b', he, hj, _⟩ := element_complete hel cs i4 env' (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) budget
    tail hview.symm hok (stackOk_empty env') nz scopeView_new.symm d4 kb (by simp; omega)
  have dj : (word cs).drop j.val = [] ++ tail ++ [] := by
    rw [hj]; have := drop_after (cs := cs) (i := i4.val) (w := body) (rest := tail) d4
    simpa using this
  obtain ⟨j2, h6, hj2⟩ := misc_complete htail cs j [] [] dj (by simp [OptS]) miscEnd_nil nz
  have fin : j2 = alloc.vec.Vec.len cs := by
    apply UScalar.eq_of_val_eq
    have total := congrArg List.length split
    simp [word_length] at total
    simp only [alloc.vec.Vec.len_val]
    simp at hj2 hi4 hi2
    change j2.val = cs.val.length
    omega
  simp [h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch, at_eq, lt', he, h6, fin]

/-! ## Reading bytes -/

/-- `read` never fails at the machine level: it returns a tree or a typed error. -/
theorem read_total (bytes : alloc.vec.Vec U8) (limits : xml.Limits) : ∃ r, xml.read bytes limits = .ok r := by
  unfold xml.read
  obtain ⟨r, hr, sound, _⟩ := decode_spec bytes
  rw [hr]; simp only [bind_ok]
  cases r with
  | Err e => exact ⟨_, rfl⟩
  | Ok cs =>
    have nz : NoZero cs := decoded_no_zero (sound cs rfl)
    obtain ⟨r1, h1, _⟩ := document_sound cs limits.expansion nz
    simp only [h1, bind_ok]
    cases r1 with
    | Ok d => exact ⟨_, rfl⟩
    | Err e =>
      obtain ⟨o, ho⟩ := byte_offset_total bytes e.offset
      simp [ho, xml.fail]

/-- Soundness: a returned tree is the root of a supported document of the
    bytes whose expansions fit the budget. -/
theorem read_sound (bytes : alloc.vec.Vec U8) (limits : xml.Limits) {d : xml.Document}
    (h : xml.read bytes limits = .ok (.Document d)) : Read bytes.val limits.expansion.val d.root := by
  unfold xml.read at h
  obtain ⟨r, hr, sound, _⟩ := decode_spec bytes
  rw [hr] at h; simp only [bind_ok] at h
  cases r with
  | Err e => simp at h
  | Ok cs =>
    have dec := sound cs rfl
    have nz : NoZero cs := decoded_no_zero dec
    obtain ⟨r1, h1, s1⟩ := document_sound cs limits.expansion nz
    simp only [h1, bind_ok] at h
    cases r1 with
    | Ok d' =>
      simp at h; subst h
      obtain ⟨cost, hdoc, kb⟩ := s1 d' rfl
      exact ⟨word cs, cost, dec, hdoc, kb⟩
    | Err e =>
      obtain ⟨o, ho⟩ := byte_offset_total bytes e.offset
      simp [ho, xml.fail] at h

/-- Completeness: the root of every supported document within the budget is
    returned, when the input length plus the budget fits in a machine word. -/
theorem read_complete (bytes : alloc.vec.Vec U8) (limits : xml.Limits) {root : xml.Element}
    (h : Read bytes.val limits.expansion.val root) (room : bytes.val.length + limits.expansion.val ≤ Usize.max) :
    xml.read bytes limits = .ok (.Document ⟨root⟩) := by
  obtain ⟨w, cost, dec, hdoc, kb⟩ := h
  unfold xml.read
  obtain ⟨r, hr, sound, complete⟩ := decode_spec bytes
  obtain ⟨cs, rfl, hw⟩ := complete w dec
  subst hw
  have nz : NoZero cs := decoded_no_zero dec
  have len := decoded_length dec
  rw [word_length] at len
  have hd := document_complete cs limits.expansion hdoc kb nz (by omega)
  simp [hr, hd]

/-- The tree of a supported document is unique. -/
theorem read_unique (bytes : alloc.vec.Vec U8) (limits : xml.Limits) {r1 r2 : xml.Element}
    (h1 : Read bytes.val limits.expansion.val r1) (h2 : Read bytes.val limits.expansion.val r2)
    (room : bytes.val.length + limits.expansion.val ≤ Usize.max) : r1 = r2 := by
  have e1 := read_complete bytes limits h1 room
  have e2 := read_complete bytes limits h2 room
  rw [e1] at e2
  simp at e2
  exact e2

/-- `read` returns exactly the supported documents' trees, and a typed error
    exactly when the bytes are no supported document within the budget. -/
theorem read_correct (bytes : alloc.vec.Vec U8) (limits : xml.Limits)
    (room : bytes.val.length + limits.expansion.val ≤ Usize.max) :
    (∀ root, xml.read bytes limits = .ok (.Document ⟨root⟩) ↔ Read bytes.val limits.expansion.val root) ∧
    ((∃ e, xml.read bytes limits = .ok (.Error e)) ↔ ∀ root, ¬ Read bytes.val limits.expansion.val root) := by
  refine ⟨fun root => ⟨fun h => read_sound bytes limits h, fun h => read_complete bytes limits h room⟩, ?_, ?_⟩
  · rintro ⟨e, he⟩ root hr
    rw [read_complete bytes limits hr room] at he
    simp at he
  · intro none
    obtain ⟨r, hr⟩ := read_total bytes limits
    cases r with
    | Error e => exact ⟨e, hr⟩
    | Document d => exact absurd (read_sound bytes limits hr) (none d.root)

end Rowl.Xml
