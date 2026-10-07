import Rowl.XmlTags

/-!
# Namespace declarations and expanded names

`declarations`, `extend`, `element_namespace`, `resolve_attributes` and
`unique_expanded` compute what the grammar's `StartTag` states: the namespace
declarations of a start tag, the scope inside its element, the element's
name and its attributes.
-/

namespace Rowl.XmlNamespaces
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs Rowl.XmlEntities Rowl.XmlAttributes Rowl.XmlTags
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- The bindings of a buffer as the grammar's scope. -/
def scopeView (ctx : alloc.vec.Vec xml.Binding) : Scope := ctx.val.map bindingView

theorem lit_xmlns : lit "xmlns" = [120, 109, 108, 110, 115] := by decide
theorem lit_xml : lit "xml" = [120, 109, 108] := by decide
theorem lit_xmlns_colon : lit "xmlns:" = [120, 109, 108, 110, 115, 58] := by decide

theorem xml_namespace_bytes : bytes xml.XML_NAMESPACE = xmlNamespace := by
  unfold xml.XML_NAMESPACE xmlNamespace
  rw [bytes_make]
  decide

theorem xmlns_namespace_bytes : bytes xml.XMLNS_NAMESPACE = xmlnsNamespace := by
  unfold xml.XMLNS_NAMESPACE xmlnsNamespace
  rw [bytes_make]
  decide

theorem xml_namespace_length : xml.XML_NAMESPACE.val.length = 36 := by
  have := congrArg List.length xml_namespace_bytes
  simp only [bytes, List.length_map] at this
  rw [this]; decide

/-! ## Comparing buffers with ASCII words -/

theorem word_eq_from_eq (v : alloc.vec.Vec U32) (text : Slice U8) (k : Usize) :
    xml.word_eq_from v text k = .ok (decide ((word v).drop k.val <+: (bytes text).drop k.val)) := by
  rw [xml.word_eq_from]
  by_cases hk : k.val < v.val.length
  · have hv : (word v).drop k.val = v.val[k.val].val :: (word v).drop (k.val + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [word_length]; exact hk)]; simp [word]
    by_cases ht : k.val < text.val.length
    · have ht' : (bytes text).drop k.val = text.val[k.val].val :: (bytes text).drop (k.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simp [bytes]; exact ht)]; simp [bytes]
      have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) v k = .ok v.val[k.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hk]
      have plookup : Slice.index_usize text k = .ok text.val[k.val] := by
        simp [Slice.index_usize, List.getElem?_eq_getElem ht]
      obtain ⟨k1, hk1, hk1v⟩ := vec_next hk
      by_cases eq : v.val[k.val].val = text.val[k.val].val
      · have same : v.val[k.val] = core.convert.num.FromU32U8.from text.val[k.val] := by
          apply UScalar.eq_of_val_eq; rw [core.convert.num.FromU32U8.from_val_eq]; exact eq
        simp only [Slice.len, alloc.vec.Vec.len_val, UScalar.lt_equiv, hk, ht, lookup, plookup, lift, bind_ok,
          same, hk1, ite_true, Slice.len_val, word_eq_from_eq v text k1]
        rw [hv, ht', hk1v, eq]; simp [List.cons_prefix_cons]
      · have differ : ¬ v.val[k.val] = core.convert.num.FromU32U8.from text.val[k.val] := by
          intro e; apply eq; rw [e, core.convert.num.FromU32U8.from_val_eq]
        simp only [Slice.len, alloc.vec.Vec.len_val, UScalar.lt_equiv, hk, ht, lookup, plookup, lift, bind_ok,
          differ, ite_true, ite_false, Slice.len_val]
        rw [hv, ht']
        simp only [List.cons_prefix_cons]
        congr 1
        exact (decide_eq_false (fun h => eq h.1)).symm
    · have empty : (bytes text).drop k.val = [] := by apply List.drop_eq_nil_of_le; simp [bytes]; omega
      simp [Slice.len_val, alloc.vec.Vec.len_val, UScalar.lt_equiv, hk, ht, hv, empty]
  · have empty : (word v).drop k.val = [] := by apply List.drop_eq_nil_of_le; rw [word_length]; omega
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, hk, empty]
termination_by v.val.length - k.val
decreasing_by omega

theorem word_eq_eq (v : alloc.vec.Vec U32) (text : Slice U8) :
    xml.word_eq v text = .ok (decide (word v = bytes text)) := by
  unfold xml.word_eq
  simp only [word_eq_from_eq, bind_ok]
  congr 1
  by_cases hl : v.val.length = text.val.length
  · have e1 : alloc.vec.Vec.len v = Slice.len text := by
      apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len_val, Slice.len_val, hl]
    simp only [e1, decide_true, Bool.true_and]
    apply decide_eq_decide.mpr
    rw [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, List.drop_zero]
    constructor
    · intro p; exact p.eq_of_length (by rw [word_length]; simp [bytes, hl])
    · intro e; rw [e]
  · have e1 : ¬ alloc.vec.Vec.len v = Slice.len text := by
      intro e; apply hl; have := congrArg UScalar.val e; simpa [alloc.vec.Vec.len_val, Slice.len_val] using this
    simp only [e1, decide_false, Bool.false_and]
    symm; apply decide_eq_false
    intro e; apply hl; have := congrArg List.length e; simpa [word, bytes] using this

theorem reserved_value_eq (v : alloc.vec.Vec U32) :
    xml.reserved_value v = .ok (decide (word v = xmlNamespace ∨ word v = xmlnsNamespace)) := by
  unfold xml.reserved_value
  simp only [word_eq_eq, xml_namespace_bytes, xmlns_namespace_bytes, bind_ok]
  congr 1
  simp

theorem ascii_word_spec (text : Slice U8) (k : Usize) (out : alloc.vec.Vec U32)
    (room : out.val.length + (text.val.length - k.val) ≤ Usize.max) :
    ∃ v, xml.ascii_word text k out = .ok (.Ok v) ∧ word v = word out ++ (bytes text).drop k.val := by
  rw [xml.ascii_word]
  by_cases hk : k.val < text.val.length
  · have plookup : Slice.index_usize text k = .ok text.val[k.val] := by
      simp [Slice.index_usize, List.getElem?_eq_getElem hk]
    have r1 : out.val.length < Usize.max := by omega
    obtain ⟨k1, hk1, hk1v⟩ := succ_spec (y := Slice.len text) (by simp [Slice.len_val]; exact hk)
    obtain ⟨v, hv, hw⟩ := ascii_word_spec text k1
      (alloc.vec.Vec.from (out.val ++ [core.convert.num.FromU32U8.from text.val[k.val]]) (by simp; omega))
      (by simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp only [Slice.len_val, UScalar.lt_equiv, hk, ite_true, plookup, lift, bind_ok, push_char_eq, r1,
        _root_.dite_true, core.result.Result.Insts.CoreOpsTry.branch, hk1, hv]
    · rw [hw, word_push, hk1v, List.drop_eq_getElem_cons (i := k.val) (by simp [bytes]; exact hk)]
      simp [bytes, core.convert.num.FromU32U8.from_val_eq]
  · refine ⟨out, by simp [Slice.len_val, UScalar.lt_equiv, hk], ?_⟩
    have : (bytes text).drop k.val = [] := by apply List.drop_eq_nil_of_le; simp [bytes]; omega
    simp [this]
termination_by text.val.length - k.val
decreasing_by omega

theorem small_le_max {n : Nat} (h : n ≤ 4294967295) : n ≤ Usize.max := by
  rcases Usize.bounds_eq with e | e <;> rw [e] <;> simp [U32.max_eq, U64.max_eq] <;> omega

theorem xml_namespace_word :
    ∃ v, xml.ascii_word xml.XML_NAMESPACE 0#usize (alloc.vec.Vec.new U32) = .ok (.Ok v) ∧
      word v = xmlNamespace := by
  obtain ⟨v, hv, hw⟩ := ascii_word_spec xml.XML_NAMESPACE 0#usize (alloc.vec.Vec.new U32)
    (by simp [xml_namespace_length]; exact small_le_max (by omega))
  exact ⟨v, hv, by rw [hw]; simp [word_new, xml_namespace_bytes]⟩

/-! ## The kind of an attribute specification -/

/-- What kind of namespace declaration an attribute name makes. -/
def kindOf (n : Word) : xml.NsKind :=
  if n = lit "xmlns" then .Default else if lit "xmlns:" <+: n then .Prefixed else .Plain

theorem qname_prefixed_parts {p l : Word} {p' : Option Word} {l' : Word} (hp : 58 ∉ p)
    (h : QName (p ++ 58 :: l) p' l') : p' = some p ∧ l' = l ∧ NCName p ∧ NCName l := by
  generalize hn : p ++ 58 :: l = n at h
  cases h with
  | unprefixed ncn => exact absurd (by rw [← hn]; simp) ncn.2
  | @prefixed a _ ha hb =>
    have ia := colonIndex_append (l := l') ha.2
    have ip := colonIndex_append (l := l) hp
    rw [hn] at ip
    have lens : p.length = a.length := by rw [← ia, ← ip]
    obtain ⟨e1, h2⟩ := List.append_inj hn lens
    simp at h2
    subst e1
    exact ⟨rfl, h2.symm, ha, h2 ▸ hb⟩

theorem xmlns_colon_prefix {p l : Word} (hp : 58 ∉ p) :
    lit "xmlns:" <+: p ++ 58 :: l ↔ p = lit "xmlns" := by
  constructor
  · rintro ⟨t, ht⟩
    have c1 := colonIndex_append (l := l) hp
    rw [← ht, lit_xmlns_colon] at c1
    simp [colonIndex] at c1
    have e : (p ++ 58 :: l).take p.length = p := by simp
    rw [← ht, c1, lit_xmlns_colon] at e
    rw [← e, lit_xmlns]; simp
  · rintro rfl; exact ⟨l, by rw [lit_xmlns_colon, lit_xmlns]; simp⟩

theorem qname_none {n l : Word} (h : QName n none l) : n = l ∧ NCName n := by
  generalize hp : (none : Option Word) = p at h
  cases h with
  | unprefixed ncn => exact ⟨rfl, ncn⟩
  | prefixed _ _ => simp at hp

theorem qname_some {n p l : Word} (h : QName n (some p) l) : n = p ++ 58 :: l ∧ NCName p ∧ NCName l := by
  generalize hp : some p = q at h
  cases h with
  | unprefixed _ => simp at hp
  | prefixed hp' hl => simp at hp; subst hp; exact ⟨rfl, hp', hl⟩

theorem ns_kind_eq (cs : alloc.vec.Vec U32) (raw : xml.Raw) {n value : Word} (h : RawOk cs raw (n, value)) :
    xml.ns_kind cs raw = .ok (kindOf n) := by
  obtain ⟨⟨p, l, hq, hmark⟩, split, hstop, _⟩ := h
  simp only at split hstop hmark hq
  unfold xml.ns_kind
  cases p with
  | none =>
    obtain ⟨_, ncn⟩ := qname_none hq
    have me : raw.mark = raw.stop := UScalar.eq_of_val_eq (by rw [hmark, hstop]; rfl)
    simp only [me, ite_true, lift, bind_ok, span_is_eq cs raw.start raw.stop _ split hstop, bytes_make]
    unfold kindOf
    by_cases e : n = lit "xmlns"
    · rw [lit_xmlns] at e; simp [e, lit_xmlns]
    · have np : ¬ lit "xmlns:" <+: n := by
        rintro ⟨t, ht⟩; apply ncn.2; rw [← ht, lit_xmlns_colon]; simp
      rw [lit_xmlns] at e; simp [e, np, lit_xmlns]
  | some p' =>
    obtain ⟨en, hp, hl⟩ := qname_some hq
    subst en
    have mne : ¬ raw.mark = raw.stop := by
      intro e; have := congrArg UScalar.val e; rw [hmark, hstop] at this; simp [markOf] at this
    have split' : (word cs).drop raw.start.val = p' ++ (58 :: l ++ (word cs).drop raw.stop.val) := by
      rw [split]; simp
    simp only [mne, ite_false, lift, bind_ok, span_is_eq cs raw.start raw.mark _ split' (by rw [hmark]; rfl),
      bytes_make]
    unfold kindOf
    have ne5 : p' ++ 58 :: l ≠ lit "xmlns" := by
      intro e; have : (58 : Nat) ∈ lit "xmlns" := by rw [← e]; simp
      rw [lit_xmlns] at this; simp at this
    have pre := xmlns_colon_prefix (l := l) hp.2
    have b5 : ([120#u8, 109#u8, 108#u8, 110#u8, 115#u8] : List U8).map (·.val) = lit "xmlns" := by decide
    rw [b5]
    by_cases e : p' = lit "xmlns"
    · have pe : lit "xmlns:" <+: p' ++ 58 :: l := pre.mpr e
      subst e
      simp [ne5, pe]
    · have pe : ¬ lit "xmlns:" <+: p' ++ 58 :: l := fun x => e (pre.mp x)
      simp [e, ne5, pe]

/-- The declaration a specification of each kind makes. -/
theorem declaration_default {n value : Word} (h : kindOf n = .Default) :
    declaration (n, value) = some (none, value) := by
  unfold kindOf at h
  by_cases e : n = lit "xmlns"
  · simp [declaration, e]
  · by_cases f : lit "xmlns:" <+: n <;> simp [e, f] at h

theorem declaration_prefixed {n value : Word} (h : kindOf n = .Prefixed) :
    ∃ l, n = lit "xmlns" ++ 58 :: l ∧ declaration (n, value) = some (some l, value) := by
  unfold kindOf at h
  by_cases e : n = lit "xmlns"
  · simp [e] at h
  · by_cases f : lit "xmlns:" <+: n
    · obtain ⟨t, rfl⟩ := f
      refine ⟨t, by rw [lit_xmlns_colon, lit_xmlns]; simp, ?_⟩
      simp [declaration, lit_xmlns_colon, lit_xmlns]
    · simp [e, f] at h

theorem declaration_plain {n value : Word} (h : kindOf n = .Plain) : declaration (n, value) = none := by
  unfold kindOf at h
  by_cases e : n = lit "xmlns"
  · simp [e] at h
  · by_cases f : lit "xmlns:" <+: n
    · simp [e, f] at h
    · simp [declaration, e, f]

/-! ## Declarations -/

theorem push_binding_eq (decls : alloc.vec.Vec xml.Binding) (b : xml.Binding) (offset : Usize)
    (h : decls.val.length < Usize.max) :
    ∃ v, xml.push_binding decls b offset = .ok (.Ok v) ∧ v.val = decls.val ++ [b] := by
  obtain ⟨v, hv, hvv⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec decls b h)
  exact ⟨v, by simp [xml.push_binding, alloc.vec.Vec.len_val, core.num.Usize.MAX, h, hv], hvv⟩

theorem default_declaration_spec (raw : xml.Raw) (decls : alloc.vec.Vec xml.Binding)
    (room : decls.val.length < Usize.max) :
    ∃ r, xml.default_declaration raw decls = .ok r ∧
      match r with
      | .Ok v => DeclarationOk (none, word raw.value) ∧ v.val = decls.val ++ [⟨none, raw.value⟩]
      | .Err _ => ¬ DeclarationOk (none, word raw.value) := by
  unfold xml.default_declaration
  rw [reserved_value_eq]
  simp only [bind_ok]
  by_cases res : word raw.value = xmlNamespace ∨ word raw.value = xmlnsNamespace
  · refine ⟨.Err ⟨.ReservedNamespace, raw.start⟩, by simp [res, xml.fail], ?_⟩
    simp only [DeclarationOk]; tauto
  · obtain ⟨v, hv, hvv⟩ := push_binding_eq decls ⟨none, raw.value⟩ raw.start room
    refine ⟨.Ok v, by simp [res, copy_all_eq, core.result.Result.Insts.CoreOpsTry.branch, hv], ?_, hvv⟩
    simp only [DeclarationOk]; exact not_or.mp res

theorem prefix_allowed_eq (cs : alloc.vec.Vec U32) (raw : xml.Raw) {l value : Word}
    (h : RawOk cs raw (lit "xmlns" ++ 58 :: l, value)) :
    xml.prefix_allowed cs raw = .ok (decide (DeclarationOk (some l, value))) := by
  obtain ⟨⟨p, l0, hq, hmark⟩, split, hstop, hval⟩ := h
  simp only at split hstop hmark hq hval
  rw [(qname_prefixed_parts (by rw [lit_xmlns]; decide) hq).1] at hmark
  unfold xml.prefix_allowed
  have mk : raw.mark.val = raw.start.val + 5 := by rw [hmark]; simp [markOf, lit_xmlns]
  obtain ⟨m1, hm1, hm1v⟩ := succ_spec (x := raw.mark) (y := raw.stop)
    (by rw [mk, hstop]; simp [lit_xmlns])
  have lsplit : (word cs).drop m1.val = l ++ (word cs).drop raw.stop.val := by
    rw [hm1v, mk]
    have := drop_after (cs := cs) (i := raw.start.val) (w := lit "xmlns" ++ [58])
      (rest := l ++ (word cs).drop raw.stop.val) (by rw [split]; simp)
    simpa [lit_xmlns, Nat.add_assoc] using this
  have ls : raw.stop.val = m1.val + l.length := by rw [hstop, hm1v, mk]; simp [lit_xmlns]; omega
  simp only [hm1, lift, bind_ok, span_is_eq cs m1 raw.stop _ lsplit ls, bytes_make]
  have b5 : ([120#u8, 109#u8, 108#u8, 110#u8, 115#u8] : List U8).map (·.val) = lit "xmlns" := by decide
  have b3 : ([120#u8, 109#u8, 108#u8] : List U8).map (·.val) = lit "xml" := by decide
  rw [b5, b3]
  by_cases e1 : l = lit "xmlns"
  · subst e1
    simp [DeclarationOk]
  · by_cases e2 : l = lit "xml"
    · subst e2
      rw [word_eq_eq, xml_namespace_bytes, hval]
      have ne : lit "xml" ≠ lit "xmlns" := by decide
      simp [DeclarationOk, ne]
    · rw [reserved_value_eq, hval]
      have lenv : (0 < raw.value.val.length) ↔ value ≠ [] := by
        rw [← hval, ← word_length]; exact List.length_pos_iff
      simp only [e1, e2, decide_false, Bool.false_eq_true, ite_false, bind_ok]
      congr 1
      have z : (0#usize : Usize).val = 0 := rfl
      simp only [DeclarationOk, ne_eq, e1, e2, not_false_eq_true, true_and, false_implies, forall_const,
        UScalar.lt_equiv, alloc.vec.Vec.len_val, z, lenv]
      by_cases zz : value = []
      · simp [zz]
      · simp [zz]

theorem prefixed_declaration_spec (cs : alloc.vec.Vec U32) (raw : xml.Raw) {l value : Word}
    (h : RawOk cs raw (lit "xmlns" ++ 58 :: l, value)) (decls : alloc.vec.Vec xml.Binding)
    (room : decls.val.length < Usize.max) :
    ∃ r, xml.prefixed_declaration cs raw decls = .ok r ∧
      match r with
      | .Ok v => DeclarationOk (some l, value) ∧
          v.val.map bindingView = decls.val.map bindingView ++ [(some l, value)]
      | .Err _ => ¬ DeclarationOk (some l, value) := by
  unfold xml.prefixed_declaration
  rw [prefix_allowed_eq cs raw h]
  simp only [bind_ok]
  by_cases ok : DeclarationOk (some l, value)
  · obtain ⟨⟨p, l0, hq, hmark⟩, split, hstop, hval⟩ := h
    simp only at split hstop hmark hq hval
    rw [(qname_prefixed_parts (by rw [lit_xmlns]; decide) hq).1] at hmark
    have mk : raw.mark.val = raw.start.val + 5 := by rw [hmark]; simp [markOf, lit_xmlns]
    obtain ⟨m1, hm1, hm1v⟩ := succ_spec (x := raw.mark) (y := raw.stop) (by rw [mk, hstop]; simp [lit_xmlns])
    have lsplit : (word cs).drop m1.val = l ++ (word cs).drop raw.stop.val := by
      rw [hm1v, mk]
      have := drop_after (cs := cs) (i := raw.start.val) (w := lit "xmlns" ++ [58])
        (rest := l ++ (word cs).drop raw.stop.val) (by rw [split]; simp)
      simpa [lit_xmlns, Nat.add_assoc] using this
    have ls : raw.stop.val = m1.val + l.length := by rw [hstop, hm1v, mk]; simp [lit_xmlns]; omega
    obtain ⟨pv, hpv, hpw⟩ := copy_span_spec cs m1 raw.stop lsplit ls
    obtain ⟨v, hv, hvv⟩ := push_binding_eq decls ⟨some pv, raw.value⟩ raw.start room
    refine ⟨.Ok v, by simp [ok, hm1, hpv, copy_all_eq, core.result.Result.Insts.CoreOpsTry.branch, hv], ok, ?_⟩
    rw [hvv]; simp [bindingView, optWord, hpw, hval]
  · exact ⟨.Err ⟨.ReservedNamespace, raw.start⟩, by simp [ok, xml.fail], ok⟩

theorem declarations_spec (cs : alloc.vec.Vec U32) (raws : alloc.vec.Vec xml.Raw) {specs : List (Word × Word)}
    (h : List.Forall₂ (RawOk cs) raws.val specs) (k : Usize) (decls : alloc.vec.Vec xml.Binding)
    (room : decls.val.length + (raws.val.length - k.val) ≤ Usize.max) :
    ∃ r, xml.declarations cs raws k decls = .ok r ∧
      match r with
      | .Ok v => (∀ d ∈ declarations (specs.drop k.val), DeclarationOk d) ∧
          v.val.map bindingView = decls.val.map bindingView ++ declarations (specs.drop k.val)
      | .Err _ => ¬ ∀ d ∈ declarations (specs.drop k.val), DeclarationOk d := by
  rw [xml.declarations]
  have hl := h.length_eq
  by_cases more : k.val < raws.val.length
  · obtain ⟨hsk, rk⟩ := raw_at h more
    have lk : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice xml.Raw) raws k = .ok raws.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have dk : specs.drop k.val = specs[k.val] :: specs.drop (k.val + 1) := List.drop_eq_getElem_cons hsk
    obtain ⟨k1, hk1, hk1v⟩ := vec_next more
    have rkn : RawOk cs raws.val[k.val] (specs[k.val].1, specs[k.val].2) := rk
    have r1 : decls.val.length < Usize.max := by omega
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_true, lk, bind_ok, ns_kind_eq cs _ rkn]
    rw [dk]
    simp only [declarations, List.filterMap_cons]
    cases hkind : kindOf specs[k.val].1 with
    | Default =>
      have dd := declaration_default (value := specs[k.val].2) hkind
      simp only [dd]
      obtain ⟨r2, h2, c2⟩ := default_declaration_spec raws.val[k.val] decls r1
      have vw : word raws.val[k.val].value = specs[k.val].2 := rk.2.2.2
      rw [vw] at c2
      cases r2 with
      | Err err =>
        refine ⟨.Err err, by simp [h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual], ?_⟩
        intro all; exact c2 (all _ (by simp))
      | Ok v =>
        obtain ⟨ok, hv⟩ := c2
        obtain ⟨r3, h3, c3⟩ := declarations_spec cs raws h k1 v (by rw [hv, hk1v]; simp; omega)
        refine ⟨r3, by simp [h2, core.result.Result.Insts.CoreOpsTry.branch, hk1, h3], ?_⟩
        rw [hk1v] at c3
        cases r3 with
        | Ok v' =>
          obtain ⟨all, hv'⟩ := c3
          refine ⟨?_, ?_⟩
          · intro d hd
            simp at hd
            rcases hd with rfl | hd
            · exact ok
            · exact all d (by simpa [declarations] using hd)
          · rw [hv', hv]; simp [bindingView, optWord, vw, declarations]
        | Err _ =>
          intro all; apply c3
          intro d hd; exact all d (by simp [declarations] at hd ⊢; exact Or.inr hd)
    | Prefixed =>
      obtain ⟨l, hn, dd⟩ := declaration_prefixed (value := specs[k.val].2) hkind
      simp only [dd]
      have rk' : RawOk cs raws.val[k.val] (lit "xmlns" ++ 58 :: l, specs[k.val].2) := by rw [← hn]; exact rk
      obtain ⟨r2, h2, c2⟩ := prefixed_declaration_spec cs raws.val[k.val] rk' decls r1
      cases r2 with
      | Err err =>
        refine ⟨.Err err, by simp [h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual], ?_⟩
        intro all; exact c2 (all _ (by simp))
      | Ok v =>
        obtain ⟨ok, hv⟩ := c2
        have vlen : v.val.length = decls.val.length + 1 := by
          have := congrArg List.length hv; simpa using this
        obtain ⟨r3, h3, c3⟩ := declarations_spec cs raws h k1 v (by rw [vlen, hk1v]; omega)
        refine ⟨r3, by simp [h2, core.result.Result.Insts.CoreOpsTry.branch, hk1, h3], ?_⟩
        rw [hk1v] at c3
        cases r3 with
        | Ok v' =>
          obtain ⟨all, hv'⟩ := c3
          refine ⟨?_, ?_⟩
          · intro d hd
            simp at hd
            rcases hd with rfl | hd
            · exact ok
            · exact all d (by simpa [declarations] using hd)
          · rw [hv', hv]; simp [declarations]
        | Err _ =>
          intro all; apply c3
          intro d hd; exact all d (by simp [declarations] at hd ⊢; exact Or.inr hd)
    | Plain =>
      have dd := declaration_plain (value := specs[k.val].2) hkind
      simp only [dd]
      obtain ⟨r3, h3, c3⟩ := declarations_spec cs raws h k1 decls (by rw [hk1v]; omega)
      refine ⟨r3, by simp [hk1, h3], ?_⟩
      rw [hk1v] at c3
      simpa [declarations] using c3
  · have dk : specs.drop k.val = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨.Ok decls, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], ?_, ?_⟩
    · rw [dk]; simp [declarations]
    · rw [dk]; simp [declarations]
termination_by raws.val.length - k.val
decreasing_by all_goals omega

/-! ## The scope inside an element -/

theorem copy_option_eq (w : Option (alloc.vec.Vec U32)) : xml.copy_option w = .ok (.Ok w) := by
  cases w <;> simp [xml.copy_option, copy_all_eq, core.result.Result.Insts.CoreOpsTry.branch]

theorem copy_bindings_spec (ctx : alloc.vec.Vec xml.Binding) (i : Usize) (out : alloc.vec.Vec xml.Binding)
    (room : out.val.length + (ctx.val.length - i.val) ≤ Usize.max) :
    ∃ v, xml.copy_bindings ctx i out = .ok (.Ok v) ∧ v.val = out.val ++ ctx.val.drop i.val := by
  rw [xml.copy_bindings]
  by_cases more : i.val < ctx.val.length
  · have lk : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice xml.Binding) ctx i =
        .ok ctx.val[i.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨i1, hi1, hi1v⟩ := vec_next more
    have r1 : out.val.length < Usize.max := by omega
    obtain ⟨o1, ho1, ho1v⟩ := push_binding_eq out ⟨ctx.val[i.val].ns_prefix, ctx.val[i.val].value⟩ 0#usize r1
    obtain ⟨v, hv, hvv⟩ := copy_bindings_spec ctx i1 o1 (by rw [ho1v, hi1v]; simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lk, copy_option_eq, copy_all_eq,
        core.result.Result.Insts.CoreOpsTry.branch, ho1, hi1, hv]
    · rw [hvv, ho1v, hi1v]
      simp only [List.append_assoc, List.singleton_append]
      rw [List.drop_eq_getElem_cons (i := i.val) more]
  · refine ⟨out, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], ?_⟩
    simp [List.drop_eq_nil_of_le (show ctx.val.length ≤ i.val by omega)]
termination_by ctx.val.length - i.val
decreasing_by omega

theorem extend_spec (ctx decls : alloc.vec.Vec xml.Binding) (room : ctx.val.length + decls.val.length ≤ Usize.max) :
    ∃ v, xml.extend ctx decls = .ok (.Ok v) ∧ v.val = ctx.val ++ decls.val := by
  unfold xml.extend
  obtain ⟨o, ho, hov⟩ := copy_bindings_spec ctx 0#usize (alloc.vec.Vec.new xml.Binding)
    (by simp)
  obtain ⟨v, hv, hvv⟩ := copy_bindings_spec decls 0#usize o (by rw [hov]; simp; omega)
  refine ⟨v, by simp [ho, core.result.Result.Insts.CoreOpsTry.branch, hv], ?_⟩
  rw [hvv, hov]; simp

/-! ## Looking up namespace names -/

theorem map_xml_bytes : ([120#u8, 109#u8, 108#u8] : List U8).map (·.val) = lit "xml" := by decide
theorem map_xmlns_bytes : ([120#u8, 109#u8, 108#u8, 110#u8, 115#u8] : List U8).map (·.val) = lit "xmlns" := by
  decide

theorem binds_eq (b : xml.Binding) (cs : alloc.vec.Vec U32) (start stop : Usize) {w rest : Word}
    (split : (word cs).drop start.val = w ++ rest) (hs : stop.val = start.val + w.length) :
    xml.binds b cs start stop = .ok (decide ((bindingView b).1 = some w)) := by
  unfold xml.binds
  cases hb : b.ns_prefix with
  | none => simp [bindingView, optWord, hb]
  | some p => simp [word_is_eq p cs start stop split hs, bindingView, optWord, hb]

theorem take_last {α : Type} {l : List α} {i : Nat} (h : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]] := by
  rw [List.take_add_one]; simp [List.getElem?_eq_getElem h]

theorem lookupPrefix_snoc (scope : Scope) (b : Binding) (w : Word) :
    lookupPrefix (scope ++ [b]) w = if b.1 = some w then some b.2 else lookupPrefix scope w := by
  unfold lookupPrefix
  by_cases h : b.1 = some w <;> simp [List.reverse_append, List.find?_cons, h]

theorem defaultNamespace_snoc (scope : Scope) (b : Binding) :
    defaultNamespace (scope ++ [b]) =
      if b.1 = none then (if b.2 = [] then none else some b.2) else defaultNamespace scope := by
  unfold defaultNamespace
  by_cases h : b.1 = none
  · obtain ⟨p, v⟩ := b
    simp at h; subst h
    simp [List.reverse_append, List.find?_cons]
  · simp [List.reverse_append, List.find?_cons, h]

theorem lookup_prefix_spec (ctx : alloc.vec.Vec xml.Binding) (cs : alloc.vec.Vec U32) (start stop : Usize)
    {w rest : Word} (split : (word cs).drop start.val = w ++ rest) (hs : stop.val = start.val + w.length)
    (k : Usize) (hk : k.val ≤ ctx.val.length) :
    ∃ o, xml.lookup_prefix ctx cs start stop k = .ok (.Ok o) ∧
      optWord o = lookupPrefix ((ctx.val.take k.val).map bindingView) w := by
  rw [xml.lookup_prefix]
  by_cases pos : 0 < k.val
  · obtain ⟨i, hi, hiv⟩ := sub_eq (x := k) (y := 1#usize) (by simp; omega)
    have kv : k.val = i.val + 1 := by simp at hiv; omega
    have ilt : i.val < ctx.val.length := by omega
    have lk : alloc.vec.Vec.index_usize ctx i = .ok ctx.val[i.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem ilt]
    have tk : ctx.val.take k.val = ctx.val.take i.val ++ [ctx.val[i.val]] := by rw [kv, take_last ilt]
    by_cases bnd : (bindingView ctx.val[i.val]).1 = some w
    · refine ⟨some ctx.val[i.val].value, ?_, ?_⟩
      · simp [UScalar.lt_equiv, pos, hi, lk, binds_eq _ cs start stop split hs, bnd, copy_all_eq,
          core.result.Result.Insts.CoreOpsTry.branch]
      · rw [tk, List.map_append, List.map_singleton, lookupPrefix_snoc, if_pos bnd]
        simp [optWord, bindingView]
    · obtain ⟨o, ho, hov⟩ := lookup_prefix_spec ctx cs start stop split hs i (by omega)
      refine ⟨o, ?_, ?_⟩
      · simp [UScalar.lt_equiv, pos, hi, lk, binds_eq _ cs start stop split hs, bnd, ho]
      · rw [hov, tk, List.map_append, List.map_singleton, lookupPrefix_snoc, if_neg bnd]
  · have k0 : k.val = 0 := by omega
    refine ⟨none, ?_, ?_⟩
    · simp [UScalar.lt_equiv, k0]
    · simp [k0, lookupPrefix, optWord]
termination_by k.val
decreasing_by omega

theorem lookup_default_spec (ctx : alloc.vec.Vec xml.Binding) (k : Usize) (hk : k.val ≤ ctx.val.length) :
    ∃ o, xml.lookup_default ctx k = .ok (.Ok o) ∧
      optWord o = defaultNamespace ((ctx.val.take k.val).map bindingView) := by
  rw [xml.lookup_default]
  by_cases pos : 0 < k.val
  · obtain ⟨i, hi, hiv⟩ := sub_eq (x := k) (y := 1#usize) (by simp; omega)
    have kv : k.val = i.val + 1 := by simp at hiv; omega
    have ilt : i.val < ctx.val.length := by omega
    have lk : alloc.vec.Vec.index_usize ctx i = .ok ctx.val[i.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem ilt]
    have tk : ctx.val.take k.val = ctx.val.take i.val ++ [ctx.val[i.val]] := by rw [kv, take_last ilt]
    by_cases dflt : ctx.val[i.val].ns_prefix = none
    · have isd : xml.is_default ctx.val[i.val] = .ok true := by simp [xml.is_default, dflt]
      have view : (bindingView ctx.val[i.val]).1 = none := by simp [bindingView, optWord, dflt]
      by_cases empty : ctx.val[i.val].value.val.length = 0
      · have le : alloc.vec.Vec.len ctx.val[i.val].value = 0#usize := by
          apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len_val, empty]
        refine ⟨none, by simp [UScalar.lt_equiv, pos, hi, lk, isd, le], ?_⟩
        rw [tk, List.map_append, List.map_singleton, defaultNamespace_snoc, if_pos view]
        have ew : word ctx.val[i.val].value = [] := by rw [← List.length_eq_zero_iff, word_length]; exact empty
        simp [optWord, bindingView, ew]
      · have le : ¬ alloc.vec.Vec.len ctx.val[i.val].value = 0#usize := by
          intro e; apply empty; have := congrArg UScalar.val e; simpa [alloc.vec.Vec.len_val] using this
        refine ⟨some ctx.val[i.val].value, by simp [UScalar.lt_equiv, pos, hi, lk, isd, le, copy_all_eq,
          core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
        rw [tk, List.map_append, List.map_singleton, defaultNamespace_snoc, if_pos view]
        have ew : word ctx.val[i.val].value ≠ [] := by
          rw [ne_eq, ← List.length_eq_zero_iff, word_length]; exact empty
        simp [optWord, bindingView, ew]
    · have isd : xml.is_default ctx.val[i.val] = .ok false := by
        cases h : ctx.val[i.val].ns_prefix with
        | none => exact absurd h dflt
        | some p => simp [xml.is_default, h]
      have view : (bindingView ctx.val[i.val]).1 ≠ none := by
        cases h : ctx.val[i.val].ns_prefix with
        | none => exact absurd h dflt
        | some p => simp [bindingView, optWord, h]
      obtain ⟨o, ho, hov⟩ := lookup_default_spec ctx i (by omega)
      refine ⟨o, by simp [UScalar.lt_equiv, pos, hi, lk, isd, ho], ?_⟩
      rw [hov, tk, List.map_append, List.map_singleton, defaultNamespace_snoc, if_neg view]
  · have k0 : k.val = 0 := by omega
    refine ⟨none, ?_, ?_⟩
    · simp [UScalar.lt_equiv, k0]
    · simp [k0, defaultNamespace, optWord]
termination_by k.val
decreasing_by omega

theorem prefix_namespace_spec (cs : alloc.vec.Vec U32) (start stop : Usize) {w rest : Word}
    (split : (word cs).drop start.val = w ++ rest) (hs : stop.val = start.val + w.length)
    (ctx : alloc.vec.Vec xml.Binding) :
    ∃ r, xml.prefix_namespace cs start stop ctx = .ok r ∧
      match r with
      | .Ok v => prefixNamespace (scopeView ctx) w = some (word v)
      | .Err _ => prefixNamespace (scopeView ctx) w = none := by
  unfold xml.prefix_namespace
  simp only [lift, bind_ok, span_is_eq cs start stop _ split hs, bytes_make, map_xml_bytes]
  by_cases x : w = lit "xml"
  · obtain ⟨v, hv, hw⟩ := xml_namespace_word
    refine ⟨.Ok v, by simp [x, hv], ?_⟩
    simp [prefixNamespace, x, hw]
  · obtain ⟨o, ho, hov⟩ := lookup_prefix_spec ctx cs start stop split hs (alloc.vec.Vec.len ctx)
      (by simp [alloc.vec.Vec.len_val])
    have full : (ctx.val.take (alloc.vec.Vec.len ctx).val).map bindingView = scopeView ctx := by
      simp [alloc.vec.Vec.len_val, scopeView]
    rw [full] at hov
    cases o with
    | none =>
      refine ⟨.Err ⟨.UndeclaredPrefix, start⟩, by simp [x, ho, core.result.Result.Insts.CoreOpsTry.branch,
        xml.fail], ?_⟩
      simp [prefixNamespace, x, ← hov, optWord]
    | some v =>
      refine ⟨.Ok v, by simp [x, ho, core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
      simp [prefixNamespace, x, ← hov, optWord]

theorem colon_split_unique {a b c d : Word} (ha : 58 ∉ a) (hc : 58 ∉ c) (h : a ++ 58 :: b = c ++ 58 :: d) :
    a = c ∧ b = d := by
  have ia := colonIndex_append (l := b) ha
  have ic := colonIndex_append (l := d) hc
  rw [h] at ia
  have lens : a.length = c.length := by rw [← ia, ← ic]
  obtain ⟨e1, e2⟩ := List.append_inj h lens
  simp at e2
  exact ⟨e1, e2⟩

theorem elementName_prefixed {scope : Scope} {p l : Word} {pre ns : Option Word} {l' : Word} (hp : 58 ∉ p)
    (h : ElementName scope (p ++ 58 :: l) pre ns l') :
    pre = some p ∧ l' = l ∧ p ≠ lit "xmlns" ∧ ∃ v, ns = some v ∧ prefixNamespace scope p = some v := by
  generalize hn : p ++ 58 :: l = n at h
  cases h with
  | unprefixed ncn => exact absurd (by rw [← hn]; simp) ncn.2
  | @prefixed a b v ha hb hx hv =>
    obtain ⟨e1, e2⟩ := colon_split_unique hp ha.2 hn
    subst e1; subst e2
    exact ⟨rfl, rfl, hx, v, rfl, hv⟩

theorem attributeName_prefixed {scope : Scope} {p l : Word} {pre ns : Option Word} {l' : Word} (hp : 58 ∉ p)
    (h : AttributeName scope (p ++ 58 :: l) pre ns l') :
    pre = some p ∧ l' = l ∧ ∃ v, ns = some v ∧ prefixNamespace scope p = some v := by
  generalize hn : p ++ 58 :: l = n at h
  cases h with
  | unprefixed ncn => exact absurd (by rw [← hn]; simp) ncn.2
  | @prefixed a b v ha hb hv =>
    obtain ⟨e1, e2⟩ := colon_split_unique hp ha.2 hn
    subst e1; subst e2
    exact ⟨rfl, rfl, v, rfl, hv⟩

theorem element_namespace_spec (cs : alloc.vec.Vec U32) (start mark stop : Usize) {n rest : Word}
    {p : Option Word} {l : Word} (split : (word cs).drop start.val = n ++ rest) (hs : stop.val = start.val + n.length)
    (hq : QName n p l) (hmark : mark.val = markOf start.val n p) (ctx : alloc.vec.Vec xml.Binding) :
    ∃ r, xml.element_namespace cs start mark stop ctx = .ok r ∧
      (∀ pre ns, r = .Ok (pre, ns) → ElementName (scopeView ctx) n (optWord pre) (optWord ns) l) ∧
      ((∃ pre ns, ElementName (scopeView ctx) n pre ns l) → ∃ v, r = .Ok v) := by
  unfold xml.element_namespace
  cases p with
  | none =>
    obtain ⟨enl, ncn⟩ := qname_none hq
    have me : mark = stop := UScalar.eq_of_val_eq (by rw [hmark, hs]; rfl)
    obtain ⟨o, ho, hov⟩ := lookup_default_spec ctx (alloc.vec.Vec.len ctx) (by simp [alloc.vec.Vec.len_val])
    refine ⟨.Ok (none, o), by simp [me, ho, core.result.Result.Insts.CoreOpsTry.branch], ?_, fun _ => ⟨_, rfl⟩⟩
    intro pre ns e
    simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    rw [← e1, ← e2]
    have dn : optWord o = defaultNamespace (scopeView ctx) := by
      rw [hov]; simp [scopeView, alloc.vec.Vec.len_val]
    rw [dn, ← enl]
    exact ElementName.unprefixed ncn
  | some p' =>
    obtain ⟨en, hp, hl⟩ := qname_some hq
    subst en
    have mne : ¬ mark = stop := by
      intro e; have := congrArg UScalar.val e; rw [hmark, hs] at this; simp [markOf] at this
    have split' : (word cs).drop start.val = p' ++ (58 :: l ++ rest) := by rw [split]; simp
    have hm : mark.val = start.val + p'.length := hmark
    simp only [mne, ite_false, lift, bind_ok, span_is_eq cs start mark _ split' hm, bytes_make, map_xmlns_bytes]
    by_cases x : p' = lit "xmlns"
    · refine ⟨.Err ⟨.ReservedNamespace, start⟩, by simp [x, xml.fail], by simp, ?_⟩
      rintro ⟨pre, ns, h⟩
      exact ((elementName_prefixed hp.2 h).2.2.1 x).elim
    · obtain ⟨r1, h1, c1⟩ := prefix_namespace_spec cs start mark split' hm ctx
      cases r1 with
      | Err err =>
        refine ⟨.Err err, by simp [x, h1, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
        rintro ⟨pre, ns, h⟩
        obtain ⟨_, _, _, v, _, hv⟩ := elementName_prefixed hp.2 h
        simp only at c1
        rw [c1] at hv; simp at hv
      | Ok v =>
        obtain ⟨pv, hpv, hpw⟩ := copy_span_spec cs start mark split' hm
        refine ⟨.Ok (some pv, some v), by simp [x, h1, core.result.Result.Insts.CoreOpsTry.branch, hpv], ?_,
          fun _ => ⟨_, rfl⟩⟩
        intro pre ns e
        simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at e
        obtain ⟨e1, e2⟩ := e
        rw [← e1, ← e2]
        simp only [optWord, Option.map_some, hpw]
        exact ElementName.prefixed hp hl x c1

/-! ## Attributes -/

theorem push_attribute_eq (out : alloc.vec.Vec xml.Attribute) (a : xml.Attribute) (offset : Usize)
    (h : out.val.length < Usize.max) :
    ∃ v, xml.push_attribute out a offset = .ok (.Ok v) ∧ v.val = out.val ++ [a] := by
  obtain ⟨v, hv, hvv⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out a h)
  exact ⟨v, by simp [xml.push_attribute, alloc.vec.Vec.len_val, core.num.Usize.MAX, h, hv], hvv⟩

theorem resolved_attribute_spec (cs : alloc.vec.Vec U32) (raw : xml.Raw) {n value : Word}
    (h : RawOk cs raw (n, value)) (ctx : alloc.vec.Vec xml.Binding) :
    ∃ r, xml.resolved_attribute cs raw ctx = .ok r ∧
      (∀ a, r = .Ok a → AttributeName (scopeView ctx) n (optWord a.ns_prefix) (optWord a.ns_name)
        (word a.local_name) ∧ word a.value = value) ∧
      ((∃ pre ns l, AttributeName (scopeView ctx) n pre ns l) → ∃ a, r = .Ok a) := by
  obtain ⟨⟨p, l, hq, hmark⟩, split, hstop, hval⟩ := h
  simp only at split hstop hmark hq hval
  unfold xml.resolved_attribute
  simp only [copy_all_eq, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  cases p with
  | none =>
    obtain ⟨_, ncn⟩ := qname_none hq
    have me : raw.mark = raw.stop := UScalar.eq_of_val_eq (by rw [hmark, hstop]; rfl)
    obtain ⟨lv, hlv, hlw⟩ := copy_span_spec cs raw.start raw.stop split hstop
    refine ⟨.Ok ⟨none, none, lv, raw.value⟩, by simp [me, hlv], ?_, fun _ => ⟨_, rfl⟩⟩
    intro a e; simp at e; subst e
    refine ⟨?_, hval⟩
    simp only [optWord, Option.map_none, hlw]
    exact AttributeName.unprefixed ncn
  | some p' =>
    obtain ⟨en, hp, hl⟩ := qname_some hq
    subst en
    have mne : ¬ raw.mark = raw.stop := by
      intro e; have := congrArg UScalar.val e; rw [hmark, hstop] at this; simp [markOf] at this
    have split' : (word cs).drop raw.start.val = p' ++ (58 :: l ++ (word cs).drop raw.stop.val) := by
      rw [split]; simp
    have hm : raw.mark.val = raw.start.val + p'.length := hmark
    obtain ⟨r1, h1, c1⟩ := prefix_namespace_spec cs raw.start raw.mark split' hm ctx
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [mne, h1, same_residual], by simp, ?_⟩
      rintro ⟨pre, ns, l2, h⟩
      obtain ⟨_, _, v, _, hv⟩ := attributeName_prefixed hp.2 h
      simp only at c1
      rw [c1] at hv; simp at hv
    | Ok nsv =>
      obtain ⟨pv, hpv, hpw⟩ := copy_span_spec cs raw.start raw.mark split' hm
      obtain ⟨m1, hm1, hm1v⟩ := succ_spec (x := raw.mark) (y := raw.stop) (by rw [hm, hstop]; simp)
      have lsplit : (word cs).drop m1.val = l ++ (word cs).drop raw.stop.val := by
        rw [hm1v, hm]
        have := drop_after (cs := cs) (i := raw.start.val) (w := p' ++ [58])
          (rest := l ++ (word cs).drop raw.stop.val) (by rw [split]; simp)
        simpa [Nat.add_assoc] using this
      have ls : raw.stop.val = m1.val + l.length := by rw [hstop, hm1v, hm]; simp; omega
      obtain ⟨lv, hlv, hlw⟩ := copy_span_spec cs m1 raw.stop lsplit ls
      refine ⟨.Ok ⟨some pv, some nsv, lv, raw.value⟩, by simp [mne, h1, hpv, hm1, hlv], ?_, fun _ => ⟨_, rfl⟩⟩
      intro a e; simp at e; subst e
      refine ⟨?_, hval⟩
      simp only [optWord, Option.map_some, hpw, hlw]
      exact AttributeName.prefixed hp hl c1

/-- An attribute as the grammar states it for a specification. -/
def AttOk (scope : Scope) (s : Word × Word) (a : xml.Attribute) : Prop :=
  AttributeName scope s.1 (optWord a.ns_prefix) (optWord a.ns_name) (word a.local_name) ∧ word a.value = s.2

theorem plain_cons (s : Word × Word) (rest : List (Word × Word)) :
    plain (s :: rest) = if declaration s = none then s :: plain rest else plain rest := by
  by_cases h : declaration s = none <;> simp [plain, List.filter_cons, h]

theorem resolve_attributes_spec (cs : alloc.vec.Vec U32) (raws : alloc.vec.Vec xml.Raw)
    {specs : List (Word × Word)} (h : List.Forall₂ (RawOk cs) raws.val specs) (k : Usize)
    (ctx : alloc.vec.Vec xml.Binding) (out : alloc.vec.Vec xml.Attribute)
    (room : out.val.length + (raws.val.length - k.val) ≤ Usize.max) :
    ∃ r, xml.resolve_attributes cs raws k ctx out = .ok r ∧
      (∀ v, r = .Ok v → ∃ new, v.val = out.val ++ new ∧
        List.Forall₂ (AttOk (scopeView ctx)) (plain (specs.drop k.val)) new) ∧
      ((∀ s ∈ plain (specs.drop k.val), ∃ pre ns l, AttributeName (scopeView ctx) s.1 pre ns l) →
        ∃ v, r = .Ok v) := by
  rw [xml.resolve_attributes]
  have hl := h.length_eq
  by_cases more : k.val < raws.val.length
  · obtain ⟨hsk, rk⟩ := raw_at h more
    have lk : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice xml.Raw) raws k = .ok raws.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have dk : specs.drop k.val = specs[k.val] :: specs.drop (k.val + 1) := List.drop_eq_getElem_cons hsk
    obtain ⟨k1, hk1, hk1v⟩ := vec_next more
    have rkn : RawOk cs raws.val[k.val] (specs[k.val].1, specs[k.val].2) := rk
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_true, lk, bind_ok, ns_kind_eq cs _ rkn]
    rw [dk, plain_cons]
    cases hkind : kindOf specs[k.val].1 with
    | Default =>
      have dd := declaration_default (value := specs[k.val].2) hkind
      have dd' : declaration specs[k.val] ≠ none := by
        have : declaration specs[k.val] = declaration (specs[k.val].1, specs[k.val].2) := rfl
        rw [this, dd]; simp
      rw [if_neg dd']
      obtain ⟨r3, h3, c3, d3⟩ := resolve_attributes_spec cs raws h k1 ctx out (by rw [hk1v]; omega)
      rw [hk1v] at c3 d3
      exact ⟨r3, by simp [hk1, h3], c3, d3⟩
    | Prefixed =>
      obtain ⟨l, hn, dd⟩ := declaration_prefixed (value := specs[k.val].2) hkind
      have dd' : declaration specs[k.val] ≠ none := by
        have : declaration specs[k.val] = declaration (specs[k.val].1, specs[k.val].2) := rfl
        rw [this, dd]; simp
      rw [if_neg dd']
      obtain ⟨r3, h3, c3, d3⟩ := resolve_attributes_spec cs raws h k1 ctx out (by rw [hk1v]; omega)
      rw [hk1v] at c3 d3
      exact ⟨r3, by simp [hk1, h3], c3, d3⟩
    | Plain =>
      have dd' : declaration specs[k.val] = none := declaration_plain hkind
      rw [if_pos dd']
      obtain ⟨r2, h2, c2, d2⟩ := resolved_attribute_spec cs raws.val[k.val] rkn ctx
      cases r2 with
      | Err err =>
        refine ⟨.Err err, by simp [h2, core.result.Result.Insts.CoreOpsTry.branch, same_residual], by simp, ?_⟩
        intro all
        obtain ⟨pre, ns, l, hn⟩ := all specs[k.val] (by simp)
        obtain ⟨a, ha⟩ := d2 ⟨pre, ns, l, hn⟩
        cases ha
      | Ok a =>
        have r1 : out.val.length < Usize.max := by omega
        obtain ⟨o1, ho1, ho1v⟩ := push_attribute_eq out a raws.val[k.val].start r1
        obtain ⟨r3, h3, c3, d3⟩ := resolve_attributes_spec cs raws h k1 ctx o1 (by rw [ho1v, hk1v]; simp; omega)
        rw [hk1v] at c3 d3
        refine ⟨r3, by simp [h2, core.result.Result.Insts.CoreOpsTry.branch, ho1, hk1, h3], ?_, ?_⟩
        · intro v e
          obtain ⟨new, hv, hall⟩ := c3 v e
          refine ⟨a :: new, by rw [hv, ho1v]; simp, List.Forall₂.cons (c2 a rfl) hall⟩
        · intro all
          exact d3 (fun s hs => all s (by simp [hs]))
  · have dk : specs.drop k.val = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨.Ok out, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], ?_, fun _ => ⟨out, rfl⟩⟩
    intro v e; simp at e; subst e
    exact ⟨[], by simp, by rw [dk]; simp [plain]⟩
termination_by raws.val.length - k.val
decreasing_by all_goals omega

/-! ## Expanded names -/

theorem same_word_from_eq (a b : alloc.vec.Vec U32) (k : Usize) (hl : a.val.length = b.val.length) :
    xml.same_word_from a b k = .ok (decide ((word a).drop k.val = (word b).drop k.val)) := by
  rw [xml.same_word_from]
  by_cases more : k.val < a.val.length
  · have la : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) a k = .ok a.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have morb : k.val < b.val.length := by omega
    have lb : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) b k = .ok b.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem morb]
    have da : (word a).drop k.val = a.val[k.val].val :: (word a).drop (k.val + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [word_length]; exact more)]; simp [word]
    have db : (word b).drop k.val = b.val[k.val].val :: (word b).drop (k.val + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [word_length]; exact morb)]; simp [word]
    obtain ⟨k1, hk1, hk1v⟩ := vec_next more
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_true, la, lb, bind_ok]
    by_cases eq : a.val[k.val] = b.val[k.val]
    · rw [if_pos eq]
      simp only [hk1, bind_ok, same_word_from_eq a b k1 hl]
      rw [da, db, hk1v, eq]
      simp
    · rw [if_neg eq, da, db]
      congr 1; symm; apply decide_eq_false
      intro e; apply eq; simp at e; exact UScalar.eq_of_val_eq e.1
  · have ea : (word a).drop k.val = [] := List.drop_eq_nil_of_le (by rw [word_length]; omega)
    have eb : (word b).drop k.val = [] := List.drop_eq_nil_of_le (by rw [word_length]; omega)
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ea, eb]
termination_by a.val.length - k.val
decreasing_by omega

theorem same_word_eq (a b : alloc.vec.Vec U32) : xml.same_word a b = .ok (decide (word a = word b)) := by
  unfold xml.same_word
  by_cases hl : a.val.length = b.val.length
  · have e : alloc.vec.Vec.len a = alloc.vec.Vec.len b :=
      UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len_val, hl])
    rw [if_pos e, same_word_from_eq a b 0#usize hl, show (0#usize : Usize).val = 0 from rfl]
    simp
  · have e : ¬ alloc.vec.Vec.len a = alloc.vec.Vec.len b := by
      intro e; apply hl; have := congrArg UScalar.val e; simpa [alloc.vec.Vec.len_val] using this
    rw [if_neg e]
    congr 1; symm; apply decide_eq_false
    intro e2; apply hl; rw [← word_length, e2, word_length]

theorem same_option_eq (a b : Option (alloc.vec.Vec U32)) :
    xml.same_option a b = .ok (decide (optWord a = optWord b)) := by
  unfold xml.same_option
  cases a <;> cases b <;> simp [optWord, same_word_eq]

/-- The expanded name of an attribute: namespace name and local name. -/
def expandedView (a : xml.Attribute) : Option Word × Word := (optWord a.ns_name, word a.local_name)

theorem same_expanded_eq (a b : xml.Attribute) :
    xml.same_expanded a b = .ok (decide (expandedView a = expandedView b)) := by
  unfold xml.same_expanded
  simp [same_option_eq, same_word_eq, expandedView]

theorem expanded_distinct_from_eq (attrs : alloc.vec.Vec xml.Attribute) (k m : Usize)
    (hk : k.val < attrs.val.length) :
    xml.expanded_distinct_from attrs k m = .ok (decide (∀ t, m.val ≤ t → (ht : t < attrs.val.length) →
      expandedView attrs.val[t] ≠ expandedView attrs.val[k.val])) := by
  rw [xml.expanded_distinct_from]
  have lk : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice xml.Attribute) attrs k =
      .ok attrs.val[k.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hk]
  by_cases more : m.val < attrs.val.length
  · have lm : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice xml.Attribute) attrs m =
        .ok attrs.val[m.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_true, lk, lm, bind_ok, same_expanded_eq]
    by_cases same : expandedView attrs.val[k.val] = expandedView attrs.val[m.val]
    · rw [if_pos (decide_eq_true same)]
      congr 1
      exact (decide_eq_false (fun all => all m.val (le_refl _) more same.symm)).symm
    · rw [if_neg (by simpa using same)]
      obtain ⟨m1, hm1, hm1v⟩ := vec_next more
      rw [hm1, bind_ok, expanded_distinct_from_eq attrs k m1 hk]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · intro h t lo ht
        by_cases e : t = m.val
        · subst e; exact fun x => same x.symm
        · exact h t (by omega) ht
      · intro h t lo ht; exact h t (by omega) ht
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_false]
    congr 1
    refine (decide_eq_true ?_).symm
    intro t lo ht; omega
termination_by attrs.val.length - m.val
decreasing_by omega

theorem unique_expanded_spec (attrs : alloc.vec.Vec xml.Attribute) (k origin : Usize) :
    ∃ r, xml.unique_expanded attrs k origin = .ok r ∧
      (r = .Ok () ↔ ∀ a b (ha : a < attrs.val.length) (hb : b < attrs.val.length), k.val ≤ a → a < b →
        expandedView attrs.val[a] ≠ expandedView attrs.val[b]) := by
  rw [xml.unique_expanded]
  by_cases more : k.val < attrs.val.length
  · obtain ⟨k1, hk1, hk1v⟩ := vec_next more
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_true, hk1, bind_ok]
    rw [expanded_distinct_from_eq attrs k k1 more]
    simp only [bind_ok]
    by_cases dist : ∀ t, k1.val ≤ t → (ht : t < attrs.val.length) →
        expandedView attrs.val[t] ≠ expandedView attrs.val[k.val]
    · rw [if_pos (decide_eq_true dist)]
      obtain ⟨r, hr, spec⟩ := unique_expanded_spec attrs k1 origin
      refine ⟨r, hr, ?_⟩
      rw [spec]
      constructor
      · intro all a b ha hb lo lt
        by_cases e : a = k.val
        · subst e
          have := dist b (by omega) hb
          exact fun x => this x.symm
        · exact all a b ha hb (by omega) lt
      · intro all a b ha hb lo lt; exact all a b ha hb (by omega) lt
    · rw [if_neg (by simpa using dist)]
      refine ⟨.Err ⟨.DuplicateAttribute, origin⟩, by simp [xml.fail], ?_⟩
      simp only [reduceCtorEq, false_iff]
      intro all
      apply dist
      intro t lo ht e
      exact all k.val t more ht (le_refl _) (by omega) e.symm
  · refine ⟨.Ok (), by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], ?_⟩
    simp only [true_iff]
    intro a b ha hb lo lt; omega
termination_by attrs.val.length - k.val
decreasing_by omega

theorem nodup_expanded {attrs : List xml.Attribute} :
    (attrs.map expandedView).Nodup ↔ ∀ a b (ha : a < attrs.length) (hb : b < attrs.length), 0 ≤ a → a < b →
      expandedView attrs[a] ≠ expandedView attrs[b] := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  simp

end Rowl.XmlNamespaces
