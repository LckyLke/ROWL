import Rowl.RdfXmlSpell
import Rowl.XmlScan
import Rowl.Iri
import Rowl.LangTag

/-!
# The terms of RDF/XML events

Correctness of the small functions of `rdfxml.rs`: copies, comparisons of
words with ASCII constants, UTF-8 spellings, IRIs, resolution, literals and
blank nodes.
-/

namespace Rowl.RdfXmlTerms
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar Rowl.RdfXmlGrammar Rowl.RdfXmlSpell
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ## Vectors and slices -/

theorem residual {T : Type} (e : rdfxml.ErrorKind) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame rdfxml.ErrorKind) (.Err e) = .ok (.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]

theorem push_eq {α : Type} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) :
    alloc.vec.Vec.push v x = .ok (alloc.vec.Vec.from (v.val ++ [x]) (by simp; omega)) := by
  unfold alloc.vec.Vec.push
  rw [dif_pos (by simp; omega)]
  simp [List.concat_eq_append]

theorem index_eq {α : Type} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = .ok v.val[i.val] := by
  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]

theorem slice_index_eq {α : Type} (s : Slice α) (i : Usize) (h : i.val < s.val.length) :
    Slice.index_usize s i = .ok s.val[i.val] := by
  simp [Slice.index_usize, List.getElem?_eq_getElem h]

theorem new_val (α : Type) : (alloc.vec.Vec.new α).val = [] := by simp

theorem map_drop_cons {α β : Type} (f : α → β) (l : List α) {i : Nat} (h : i < l.length) :
    f l[i] :: (l.map f).drop (i + 1) = (l.map f).drop i := by
  rw [List.drop_eq_getElem_cons (by simpa using h : i < (l.map f).length)]
  simp

/-! ## Copies -/

theorem copy_bytes_from_eq (values : alloc.vec.Vec U8) (i : Usize) (out : alloc.vec.Vec U8)
    (hi : i.val ≤ values.val.length) (room : out.val.length + (values.val.length - i.val) ≤ Usize.max) :
    ∃ v, rdfxml.copy_bytes_from values i out = .ok v ∧ v.val = out.val ++ values.val.drop i.val := by
  rw [rdfxml.copy_bytes_from]
  by_cases lt : i.val < values.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len values) (by simpa using lt)
    obtain ⟨v, hv, hval⟩ := copy_bytes_from_eq values i1
      (alloc.vec.Vec.from (out.val ++ [values.val[i.val]]) (by simp; omega)) (by omega) (by simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp [UScalar.lt_equiv, lt, index_eq values i lt, push_eq out _ (by omega), hi1, hv]
    · rw [hval, List.drop_eq_getElem_cons lt]; simp [hi1v]
  · have : values.val.length ≤ i.val := by omega
    exact ⟨out, by simp [UScalar.lt_equiv, lt], by simp [List.drop_eq_nil_of_le this]⟩
termination_by values.val.length - i.val
decreasing_by omega

theorem copy_bytes_eq (values : alloc.vec.Vec U8) : rdfxml.copy_bytes values = .ok values := by
  obtain ⟨v, hv, hval⟩ := copy_bytes_from_eq values 0#usize (alloc.vec.Vec.new U8) (by simp)
    (by simp)
  have e : v = values := alloc.vec.Vec.ext _ _ (by simpa using hval)
  rw [rdfxml.copy_bytes, hv, e]

theorem copy_word_from_eq (values : alloc.vec.Vec U32) (i : Usize) (out : alloc.vec.Vec U32)
    (hi : i.val ≤ values.val.length) (room : out.val.length + (values.val.length - i.val) ≤ Usize.max) :
    ∃ v, rdfxml.copy_word_from values i out = .ok v ∧ v.val = out.val ++ values.val.drop i.val := by
  rw [rdfxml.copy_word_from]
  by_cases lt : i.val < values.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len values) (by simpa using lt)
    obtain ⟨v, hv, hval⟩ := copy_word_from_eq values i1
      (alloc.vec.Vec.from (out.val ++ [values.val[i.val]]) (by simp; omega)) (by omega) (by simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp [UScalar.lt_equiv, lt, index_eq values i lt, push_eq out _ (by omega), hi1, hv]
    · rw [hval, List.drop_eq_getElem_cons lt]; simp [hi1v]
  · have : values.val.length ≤ i.val := by omega
    exact ⟨out, by simp [UScalar.lt_equiv, lt], by simp [List.drop_eq_nil_of_le this]⟩
termination_by values.val.length - i.val
decreasing_by omega

theorem copy_word_eq (values : alloc.vec.Vec U32) : rdfxml.copy_word values = .ok values := by
  obtain ⟨v, hv, hval⟩ := copy_word_from_eq values 0#usize (alloc.vec.Vec.new U32) (by simp)
    (by simp)
  have e : v = values := alloc.vec.Vec.ext _ _ (by simpa using hval)
  rw [rdfxml.copy_word, hv, e]

theorem constant_from_eq (values : Slice U8) (i : Usize) (out : alloc.vec.Vec U8)
    (hi : i.val ≤ values.val.length) (room : out.val.length + (values.val.length - i.val) ≤ Usize.max) :
    ∃ v, rdfxml.constant_from values i out = .ok v ∧ v.val = out.val ++ values.val.drop i.val := by
  rw [rdfxml.constant_from]
  by_cases lt : i.val < values.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := Slice.len values) (by simpa using lt)
    obtain ⟨v, hv, hval⟩ := constant_from_eq values i1
      (alloc.vec.Vec.from (out.val ++ [values.val[i.val]]) (by simp; omega)) (by omega) (by simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp [UScalar.lt_equiv, lt, slice_index_eq values i lt, push_eq out _ (by omega), hi1, hv]
    · rw [hval, List.drop_eq_getElem_cons lt]; simp [hi1v]
  · have : values.val.length ≤ i.val := by omega
    exact ⟨out, by simp [UScalar.lt_equiv, lt], by simp [List.drop_eq_nil_of_le this]⟩
termination_by values.val.length - i.val
decreasing_by omega

theorem constant_eq (values : Slice U8) :
    ∃ v, rdfxml.constant values = .ok v ∧ v.val = values.val := by
  obtain ⟨v, hv, hval⟩ := constant_from_eq values 0#usize (alloc.vec.Vec.new U8) (by simp)
    (by simp)
  exact ⟨v, by rw [rdfxml.constant, hv], by simpa using hval⟩

theorem ascii_word_from_eq (values : Slice U8) (i : Usize) (out : alloc.vec.Vec U32)
    (hi : i.val ≤ values.val.length) (room : out.val.length + (values.val.length - i.val) ≤ Usize.max) :
    ∃ v, rdfxml.ascii_word_from values i out = .ok v ∧
      word v = word out ++ (values.val.drop i.val).map (·.val) := by
  rw [rdfxml.ascii_word_from]
  by_cases lt : i.val < values.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := Slice.len values) (by simpa using lt)
    have cast : (UScalar.cast .U32 values.val[i.val]).val = values.val[i.val].val :=
      U8.cast_U32_val_eq _
    obtain ⟨v, hv, hval⟩ := ascii_word_from_eq values i1
      (alloc.vec.Vec.from (out.val ++ [UScalar.cast .U32 values.val[i.val]]) (by simp; omega)) (by omega)
      (by simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp [UScalar.lt_equiv, lt, slice_index_eq values i lt, push_eq out _ (by omega), hi1, hv, lift]
    · rw [hval]; simp [word, hi1v, cast]
      exact map_drop_cons _ _ lt
  · have : values.val.length ≤ i.val := by omega
    exact ⟨out, by simp [UScalar.lt_equiv, lt], by simp [List.drop_eq_nil_of_le this]⟩
termination_by values.val.length - i.val
decreasing_by omega

theorem ascii_word_eq (values : Slice U8) :
    ∃ v, rdfxml.ascii_word values = .ok v ∧ word v = values.val.map (·.val) := by
  obtain ⟨v, hv, hval⟩ := ascii_word_from_eq values 0#usize (alloc.vec.Vec.new U32) (by simp) (by simp)
  exact ⟨v, by rw [rdfxml.ascii_word, hv], by simpa [word] using hval⟩

theorem rdf_iri_eq (spelling : Slice U8) :
    ∃ i, rdfxml.rdf_iri spelling = .ok i ∧ i.spelling.val = spelling.val := by
  obtain ⟨v, hv, hval⟩ := constant_eq spelling
  exact ⟨⟨v⟩, by simp [rdfxml.rdf_iri, hv], hval⟩

theorem copy_iri_eq (i : rdf.RdfIri) : rdfxml.copy_iri i = .ok i := by
  simp [rdfxml.copy_iri, copy_bytes_eq]

theorem copy_blank_eq (b : rdf.BlankNode) : rdfxml.copy_blank b = .ok b := by
  simp [rdfxml.copy_blank, copy_bytes_eq]

theorem copy_subject_eq (s : rdf.Subject) : rdfxml.copy_subject s = .ok s := by
  cases s <;> simp [rdfxml.copy_subject, copy_iri_eq, copy_blank_eq]

theorem copy_kind_eq (k : rdf.LiteralKind) : rdfxml.copy_kind k = .ok k := by
  cases k <;> simp [rdfxml.copy_kind, copy_iri_eq, copy_bytes_eq]

theorem copy_object_eq (o : rdf.Object) : rdfxml.copy_object o = .ok o := by
  cases o <;> simp [rdfxml.copy_object, copy_iri_eq, copy_blank_eq, copy_bytes_eq, copy_kind_eq]

/-- The object with the term of a subject. -/
def asObject : rdf.Subject → rdf.Object
  | .Iri i => .Iri i
  | .Blank b => .Blank b

theorem object_of_eq (s : rdf.Subject) : rdfxml.object_of s = .ok (asObject s) := by
  cases s <;> simp [rdfxml.object_of, asObject, copy_iri_eq, copy_blank_eq]

/-! ## Comparisons -/

theorem same_word_from_eq (w v : alloc.vec.Vec U32) (i : Usize) (len : w.val.length = v.val.length) :
    rdfxml.same_word_from w v i = .ok (decide ((word w).drop i.val = (word v).drop i.val)) := by
  rw [rdfxml.same_word_from]
  by_cases lt : i.val < w.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len w) (by simpa using lt)
    have lv : i.val < v.val.length := by omega
    have dw : (word w).drop i.val = w.val[i.val].val :: (word w).drop i1.val := by
      rw [hi1v]; simp only [word]; exact (map_drop_cons _ _ lt).symm
    have dv : (word v).drop i.val = v.val[i.val].val :: (word v).drop i1.val := by
      rw [hi1v]; simp only [word]; exact (map_drop_cons _ _ lv).symm
    by_cases same : w.val[i.val] = v.val[i.val]
    · simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq w i lt,
        index_eq v i lv, same, hi1]
      rw [same_word_from_eq w v i1 len, dw, dv, same]
      simp
    · simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq w i lt,
        index_eq v i lv, same, ite_false]
      rw [dw, dv]
      have : w.val[i.val].val ≠ v.val[i.val].val := fun e => same (UScalar.eq_of_val_eq e)
      simp [this]
  · have : w.val.length ≤ i.val := by omega
    have e1 : (word w).drop i.val = [] := List.drop_eq_nil_of_le (by simp [word]; omega)
    have e2 : (word v).drop i.val = [] := List.drop_eq_nil_of_le (by simp [word]; omega)
    simp [UScalar.lt_equiv, lt, e1, e2]
termination_by w.val.length - i.val
decreasing_by omega

theorem same_word_eq (w v : alloc.vec.Vec U32) : rdfxml.same_word w v = .ok (decide (word w = word v)) := by
  rw [rdfxml.same_word]
  by_cases len : w.val.length = v.val.length
  · have : alloc.vec.Vec.len w = alloc.vec.Vec.len v := UScalar.eq_of_val_eq (by simpa using len)
    simp only [this, ite_true]
    rw [same_word_from_eq w v 0#usize len]
    simp
  · have : ¬ alloc.vec.Vec.len w = alloc.vec.Vec.len v := fun e => len (by simpa using congrArg UScalar.val e)
    simp only [this, ite_false]
    have : word w ≠ word v := fun e => len (by simpa [word] using congrArg List.length e)
    simp [this]

theorem same_bytes_from_eq (w v : alloc.vec.Vec U8) (i : Usize) (len : w.val.length = v.val.length) :
    rdfxml.same_bytes_from w v i = .ok (decide (w.val.drop i.val = v.val.drop i.val)) := by
  rw [rdfxml.same_bytes_from]
  by_cases lt : i.val < w.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len w) (by simpa using lt)
    have lv : i.val < v.val.length := by omega
    have dw : w.val.drop i.val = w.val[i.val] :: w.val.drop i1.val := by
      rw [hi1v, List.drop_eq_getElem_cons lt]
    have dv : v.val.drop i.val = v.val[i.val] :: v.val.drop i1.val := by
      rw [hi1v, List.drop_eq_getElem_cons lv]
    by_cases same : w.val[i.val] = v.val[i.val]
    · simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq w i lt,
        index_eq v i lv, same, hi1]
      rw [same_bytes_from_eq w v i1 len, dw, dv, same]
      simp
    · simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq w i lt,
        index_eq v i lv, same, ite_false]
      rw [dw, dv]
      simp [same]
  · have : w.val.length ≤ i.val := by omega
    simp [UScalar.lt_equiv, lt, List.drop_eq_nil_of_le this, List.drop_eq_nil_of_le (show v.val.length ≤ i.val by omega)]
termination_by w.val.length - i.val
decreasing_by omega

theorem same_bytes_eq (w v : alloc.vec.Vec U8) : rdfxml.same_bytes w v = .ok (decide (w.val = v.val)) := by
  rw [rdfxml.same_bytes]
  by_cases len : w.val.length = v.val.length
  · have : alloc.vec.Vec.len w = alloc.vec.Vec.len v := UScalar.eq_of_val_eq (by simpa using len)
    simp only [this, ite_true]
    rw [same_bytes_from_eq w v 0#usize len]
    simp
  · have : ¬ alloc.vec.Vec.len w = alloc.vec.Vec.len v := fun e => len (by simpa using congrArg UScalar.val e)
    simp only [this, ite_false]
    have : w.val ≠ v.val := fun e => len (by rw [e])
    simp [this]

/-! ## ASCII constants -/

theorem slice_val (n : Usize) (l : List U8) (h : l.length = n.val) :
    (Array.to_slice (Array.make n l h)).val = l := by
  simp [Array.to_slice]

theorem ascii_at_eq (w : alloc.vec.Vec U32) (start : Usize) (pattern : Slice U8) (i : Usize)
    (fits : start.val + pattern.val.length ≤ w.val.length) (hi : i.val ≤ pattern.val.length) :
    rdfxml.ascii_at w start pattern i =
      .ok (decide (((word w).drop (start.val + i.val)).take (pattern.val.length - i.val) =
        (pattern.val.drop i.val).map (·.val))) := by
  rw [rdfxml.ascii_at]
  by_cases lt : i.val < pattern.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := Slice.len pattern) (by simpa using lt)
    have inside : start.val + i.val < w.val.length := by omega
    obtain ⟨k, hk, hkv⟩ := Rowl.XmlScan.usize_add_le (x := start) (c := i) (y := alloc.vec.Vec.len w)
      (by simp; omega)
    have kin : k.val < w.val.length := by omega
    have dw : (word w).drop (start.val + i.val) = w.val[k.val].val :: (word w).drop (start.val + i1.val) := by
      rw [show start.val + i1.val = k.val + 1 by omega, ← hkv]; simp only [word]; exact (map_drop_cons _ _ kin).symm
    have dp : (pattern.val.drop i.val).map (·.val) =
        pattern.val[i.val].val :: (pattern.val.drop i1.val).map (·.val) := by
      rw [hi1v, List.map_drop, List.map_drop]; exact (map_drop_cons _ _ lt).symm
    have cast : (UScalar.cast .U32 pattern.val[i.val]).val = pattern.val[i.val].val := U8.cast_U32_val_eq _
    have take : ∀ (x : Nat) (rest : Word), (x :: rest).take (pattern.val.length - i.val) =
        x :: rest.take (pattern.val.length - i1.val) := by
      intro x rest
      rw [show pattern.val.length - i.val = (pattern.val.length - i1.val) + 1 by omega]; rfl
    by_cases same : w.val[k.val].val = pattern.val[i.val].val
    · have same' : w.val[k.val] = UScalar.cast .U32 pattern.val[i.val] := UScalar.eq_of_val_eq (by rw [cast]; exact same)
      simp only [Slice.len_val, UScalar.lt_equiv, lt, ite_true, bind_ok, hk, index_eq w k kin,
        slice_index_eq pattern i lt, lift, same', hi1]
      rw [ascii_at_eq w start pattern i1 fits (by omega), dw, dp, take, same]
      simp
    · have same' : ¬ w.val[k.val] = UScalar.cast .U32 pattern.val[i.val] := fun e => same (by rw [e, cast])
      simp only [Slice.len_val, UScalar.lt_equiv, lt, ite_true, bind_ok, hk, index_eq w k kin,
        slice_index_eq pattern i lt, lift, same', ite_false]
      rw [dw, dp, take]
      simp [same]
  · have : pattern.val.length - i.val = 0 := by omega
    have e : pattern.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    simp [UScalar.lt_equiv, lt, this, e]
termination_by pattern.val.length - i.val
decreasing_by omega

theorem is_ascii_eq (w : alloc.vec.Vec U32) (pattern : Slice U8) :
    rdfxml.is_ascii w pattern = .ok (decide (word w = pattern.val.map (·.val))) := by
  rw [rdfxml.is_ascii]
  by_cases len : w.val.length = pattern.val.length
  · have : alloc.vec.Vec.len w = Slice.len pattern := UScalar.eq_of_val_eq (by simpa using len)
    simp only [this, ite_true]
    rw [ascii_at_eq w 0#usize pattern 0#usize (by simp; omega) (by simp)]
    have : (word w).take pattern.val.length = word w := List.take_of_length_le (by simp [word]; omega)
    simp [this]
  · have : ¬ alloc.vec.Vec.len w = Slice.len pattern := fun e => len (by simpa using congrArg UScalar.val e)
    simp only [this, ite_false]
    have : word w ≠ pattern.val.map (·.val) := fun e => len (by simpa [word] using congrArg List.length e)
    simp [this]

theorem rdf_length_val : rdfxml.RDF_LENGTH.val = 43 := by
  unfold rdfxml.RDF_LENGTH; rfl

/-- The 43 bytes of the RDF namespace name. -/
def rdfNsBytes : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8,
  119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8,
  49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8,
  45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8,
  97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8]

theorem rdfNsBytes_val : rdfNsBytes.map (·.val) = rdfNs := by decide

theorem split_eq {α : Type} (w a b : List α) (h : w.length = a.length + b.length) :
    w = a ++ b ↔ w.take a.length = a ∧ w.drop a.length = b := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h1, h2⟩; rw [← List.take_append_drop a.length w, h1, h2]

theorem rdf_slice (l : List U8) (hl : l.length = (43#usize).val) (e : l = rdfNsBytes) :
    (Array.to_slice (Array.make 43#usize l hl)).val.map (·.val) = rdfNs := by
  rw [slice_val, e, rdfNsBytes_val]

theorem usize_zero_val : (0#usize : Usize).val = 0 := by simp

theorem is_rdf_eq (w : alloc.vec.Vec U32) (nm : Slice U8) (small : nm.val.length ≤ 1000) :
    rdfxml.is_rdf w nm = .ok (decide (word w = rdfNs ++ nm.val.map (·.val))) := by
  rw [rdfxml.is_rdf]
  obtain ⟨n, hn, hnv⟩ := Rowl.XmlScan.usize_add_le (x := rdfxml.RDF_LENGTH) (c := Slice.len nm)
    (y := 2000#usize) (by simp [rdf_length_val]; omega)
  have hnv' : n.val = 43 + nm.val.length := by simpa [rdf_length_val] using hnv
  simp only [hn, bind_ok, lift]
  have rl : rdfNs.length = 43 := by decide
  by_cases len : w.val.length = 43 + nm.val.length
  · have : alloc.vec.Vec.len w = n := UScalar.eq_of_val_eq (by simp; omega)
    simp only [this, ite_true]
    generalize hs : Array.to_slice (Array.make 43#usize _ _) = s
    have sv : s.val.map (·.val) = rdfNs := by rw [← hs]; exact rdf_slice _ _ rfl
    have sl : s.val.length = 43 := by simpa [rl] using congrArg List.length sv
    rw [ascii_at_eq w 0#usize s 0#usize (by simp; omega) (by simp)]
    rw [usize_zero_val, Nat.add_zero, List.drop_zero, Nat.sub_zero, List.drop_zero, sl, sv]
    rw [ascii_at_eq w rdfxml.RDF_LENGTH nm 0#usize (by rw [rdf_length_val]; omega) (by simp)]
    rw [usize_zero_val, rdf_length_val, Nat.add_zero, Nat.sub_zero, List.drop_zero]
    rw [List.take_of_length_le (show ((word w).drop 43).length ≤ nm.val.length by simp [word]; omega)]
    have wl : (word w).length = rdfNs.length + (nm.val.map (·.val)).length := by simp [word, rl]; omega
    have key := split_eq (word w) rdfNs (nm.val.map (·.val)) wl
    rw [rl] at key
    by_cases first : (word w).take 43 = rdfNs <;> simp [first, key]
  · have : ¬ alloc.vec.Vec.len w = n := fun e => len (by have := congrArg UScalar.val e; simp at this; omega)
    simp only [this, ite_false]
    have : word w ≠ rdfNs ++ nm.val.map (·.val) := fun e => len (by
      have := congrArg List.length e; simp [word, rl] at this; omega)
    simp [this]

theorem rdf_extension_eq (w : alloc.vec.Vec U32) :
    rdfxml.rdf_extension w = .ok (decide (rdfNs <+: word w ∧ word w ≠ rdfNs)) := by
  rw [rdfxml.rdf_extension]
  have rl : rdfNs.length = 43 := by decide
  by_cases lt : 43 < w.val.length
  · have : rdfxml.RDF_LENGTH < alloc.vec.Vec.len w := by simp [UScalar.lt_equiv, rdf_length_val]; omega
    simp only [this, ite_true, lift, bind_ok]
    generalize hs : Array.to_slice (Array.make 43#usize _ _) = s
    have sv : s.val.map (·.val) = rdfNs := by rw [← hs]; exact rdf_slice _ _ rfl
    have sl : s.val.length = 43 := by simpa [rl] using congrArg List.length sv
    rw [ascii_at_eq w 0#usize s 0#usize (by simp; omega) (by simp)]
    rw [usize_zero_val, Nat.add_zero, List.drop_zero, Nat.sub_zero, List.drop_zero, sl, sv]
    have ne : word w ≠ rdfNs := fun e => by have := congrArg List.length e; simp [word, rl] at this; omega
    have pre : rdfNs <+: word w ↔ (word w).take 43 = rdfNs := by
      rw [List.prefix_iff_eq_take, rl, eq_comm]
    simp [pre, ne]
  · have : ¬ rdfxml.RDF_LENGTH < alloc.vec.Vec.len w := by simp [UScalar.lt_equiv, rdf_length_val]; omega
    simp only [this, ite_false]
    have : ¬ (rdfNs <+: word w ∧ word w ≠ rdfNs) := by
      rintro ⟨p, ne⟩
      have := p.length_le
      simp [word, rl] at this
      have eq : word w = rdfNs := (p.eq_of_length (by simp [word, rl]; omega)).symm
      exact ne eq
    simp [this]

theorem space_eq (c : U32) : rdfxml.space c = .ok (decide (IsSpace c.val)) := by
  simp only [rdfxml.space, IsSpace]
  by_cases h32 : c = 32#u32
  · simp [h32]
  · by_cases h9 : c = 9#u32
    · simp [h9]
    · by_cases h13 : c = 13#u32
      · simp [h13]
      · have n32 : c.val ≠ 32 := fun e => h32 (UScalar.eq_of_val_eq (by simpa using e))
        have n9 : c.val ≠ 9 := fun e => h9 (UScalar.eq_of_val_eq (by simpa using e))
        have n13 : c.val ≠ 13 := fun e => h13 (UScalar.eq_of_val_eq (by simpa using e))
        simp [h32, h9, h13, n32, n9, n13, UScalar.eq_equiv]

theorem spaces_from_eq (w : alloc.vec.Vec U32) (i : Usize) :
    rdfxml.spaces_from w i = .ok (decide (Ws ((word w).drop i.val))) := by
  rw [rdfxml.spaces_from]
  by_cases lt : i.val < w.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len w) (by simpa using lt)
    have dw : (word w).drop i.val = w.val[i.val].val :: (word w).drop i1.val := by
      rw [hi1v]; simp only [word]; exact (map_drop_cons _ _ lt).symm
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq w i lt, space_eq]
    rw [dw]
    by_cases sp : IsSpace w.val[i.val].val
    · simp only [sp, decide_true, ite_true, hi1, bind_ok]
      rw [spaces_from_eq w i1]
      simp [Ws, sp]
    · simp [Ws, sp]
  · have e : (word w).drop i.val = [] := List.drop_eq_nil_of_le (by simp [word]; omega)
    simp [UScalar.lt_equiv, lt, e, Ws]
termination_by w.val.length - i.val
decreasing_by omega

theorem nc_start_eq (c : U32) : rdfxml.nc_start c = .ok (decide (NameStartChar c.val ∧ c.val ≠ 58)) := by
  unfold rdfxml.nc_start
  by_cases h : c = 58#u32
  · subst h; simp
  · have : c.val ≠ 58 := fun e => h (UScalar.eq_of_val_eq (by simpa using e))
    simp [h, this, Rowl.XmlScan.name_start_eq]

theorem nc_char_eq (c : U32) : rdfxml.nc_char c = .ok (decide (NameChar c.val ∧ c.val ≠ 58)) := by
  unfold rdfxml.nc_char
  by_cases h : c = 58#u32
  · subst h; simp
  · have : c.val ≠ 58 := fun e => h (UScalar.eq_of_val_eq (by simpa using e))
    simp [h, this, Rowl.XmlScan.name_char_eq]

theorem nc_rest_eq (w : alloc.vec.Vec U32) (i : Usize) :
    rdfxml.nc_rest w i = .ok (decide (∀ d ∈ (word w).drop i.val, NameChar d ∧ d ≠ 58)) := by
  rw [rdfxml.nc_rest]
  by_cases lt : i.val < w.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len w) (by simpa using lt)
    have dw : (word w).drop i.val = w.val[i.val].val :: (word w).drop i1.val := by
      rw [hi1v]; simp only [word]; exact (map_drop_cons _ _ lt).symm
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq w i lt, nc_char_eq]
    rw [dw]
    by_cases ok : NameChar w.val[i.val].val ∧ w.val[i.val].val ≠ 58
    · simp only [ok, decide_true, ite_true, hi1, bind_ok]
      rw [nc_rest_eq w i1]
      simp [ok]
    · simp only [ok, decide_false, Bool.false_eq_true, ite_false]
      simp only [List.mem_cons, forall_eq_or_imp]
      simp [ok]
  · have e : (word w).drop i.val = [] := List.drop_eq_nil_of_le (by simp [word]; omega)
    simp [UScalar.lt_equiv, lt, e]
termination_by w.val.length - i.val
decreasing_by omega

theorem ncname_cons (a : Nat) (rest : Word) :
    NCName (a :: rest) ↔ (NameStartChar a ∧ a ≠ 58) ∧ ∀ d ∈ rest, NameChar d ∧ d ≠ 58 := by
  simp only [NCName, Name]
  constructor
  · rintro ⟨⟨c, r, e, hc, hr⟩, n58⟩
    simp only [List.cons.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    simp only [List.mem_cons, not_or] at n58
    exact ⟨⟨hc, fun h => n58.1 h.symm⟩, fun d hd => ⟨hr d hd, fun h => n58.2 (h ▸ hd)⟩⟩
  · rintro ⟨⟨hc, c58⟩, hr⟩
    refine ⟨⟨a, rest, rfl, hc, fun d hd => (hr d hd).1⟩, ?_⟩
    simp only [List.mem_cons, not_or]
    exact ⟨fun h => c58 h.symm, fun h => (hr 58 h).2 rfl⟩

theorem word_cons_of_pos (w : alloc.vec.Vec U32) (pos : 0 < w.val.length) :
    word w = w.val[0].val :: (word w).drop 1 := by
  have := map_drop_cons (·.val) w.val pos
  simp only [List.drop_zero] at this
  simpa [word] using this.symm

theorem ncname_eq (w : alloc.vec.Vec U32) : rdfxml.ncname w = .ok (decide (NCName (word w))) := by
  unfold rdfxml.ncname
  obtain ⟨l, hl⟩ : ∃ l, w.val = l := ⟨_, rfl⟩
  cases l with
  | nil =>
    have e : word w = [] := by simp [word, hl]
    have : ¬ (0#usize) < alloc.vec.Vec.len w := by
      intro h; rw [UScalar.lt_equiv] at h; simp [hl] at h
    simp only [this, ite_false, e]
    simp [NCName, Name]
  | cons c rest =>
    have z : (0#usize).val < w.val.length := by simp [hl]
    have p' : (0#usize) < alloc.vec.Vec.len w := by rw [UScalar.lt_equiv]; simpa using z
    have get : w.val[(0#usize).val]'z = c := by simp [hl]
    simp only [p', ite_true, bind_ok, index_eq w 0#usize z, get, nc_start_eq]
    have ww : word w = c.val :: (word w).drop 1 := by simp [word, hl]
    have nc : NCName (word w) ↔ (NameStartChar c.val ∧ c.val ≠ 58) ∧
        ∀ d ∈ (word w).drop 1, NameChar d ∧ d ≠ 58 := by
      conv_lhs => rw [ww]
      exact ncname_cons _ _
    by_cases first : NameStartChar c.val ∧ c.val ≠ 58
    · rw [if_pos (by simpa using first), nc_rest_eq w 1#usize]
      simp [nc, first]
    · rw [if_neg (by simpa using first)]
      simp [nc, first]

theorem word_inj {u v : alloc.vec.Vec U32} (h : word u = word v) : u = v := by
  apply alloc.vec.Vec.ext
  have := List.map_injective_iff.mpr (fun (x y : U32) (e : x.val = y.val) => UScalar.eq_of_val_eq e) h
  exact this

theorem concat_eq (a b : alloc.vec.Vec U32) (limit : Usize) :
    ∃ r, rdfxml.concat a b limit = .ok r ∧
      ∀ v, r = .Ok v ↔ (word a ++ word b).length ≤ limit.val ∧ word v = word a ++ word b := by
  unfold rdfxml.concat
  by_cases la : a.val.length ≤ limit.val
  · have la' : alloc.vec.Vec.len a ≤ limit := by simpa [UScalar.le_equiv] using la
    obtain ⟨d, hd, hdv⟩ := WP.spec_imp_exists (Usize.sub_spec (x := limit) (y := alloc.vec.Vec.len a)
      (by simpa using la))
    have hdv' : d.val = limit.val - a.val.length := by simp at hdv; exact hdv.1
    simp only [la', ite_true, hd, bind_ok, copy_word_eq]
    by_cases lb : b.val.length ≤ d.val
    · have lb' : alloc.vec.Vec.len b ≤ d := by simpa [UScalar.le_equiv] using lb
      have lim := limit.hBounds
      obtain ⟨v, hv, hval⟩ := copy_word_from_eq b 0#usize a (by simp)
        (by simp; have := Rowl.XmlScan.usize_le_max limit; omega)
      refine ⟨.Ok v, by simp [lb', hv], fun v' => ?_⟩
      have wv : word v = word a ++ word b := by simp [word, hval]
      constructor
      · intro e
        simp only [core.result.Result.Ok.injEq] at e
        subst e
        exact ⟨by simp [word]; omega, wv⟩
      · rintro ⟨-, e⟩
        rw [word_inj (e.trans wv.symm)]
    · have lb' : ¬ alloc.vec.Vec.len b ≤ d := by simpa [UScalar.le_equiv] using lb
      refine ⟨.Err .ResourceLimit, by simp [lb'], fun v' => ?_⟩
      simp [word]; omega
  · have la' : ¬ alloc.vec.Vec.len a ≤ limit := by simpa [UScalar.le_equiv] using la
    refine ⟨.Err .ResourceLimit, by simp [la'], fun v' => ?_⟩
    simp [word]; omega

/-! ## UTF-8 spellings, IRIs and resolution -/

theorem utf8Bytes_length_cons (c : Nat) (w : Word) :
    (utf8Bytes (c :: w)).length = (Rowl.IriResolution.utf8 c).length + (utf8Bytes w).length := by
  simp [utf8Bytes]

theorem encode_scalar (cp : U32) (e : encoding.Encoded) (h : encoding.encode cp = .ok (some e)) :
    Rowl.Encoding.Scalar cp.val := by
  by_contra ns
  have := (Rowl.Encoding.encode_none_iff cp).mpr ns
  rw [h] at this
  simp at this

theorem utf8_from_eq (w : alloc.vec.Vec U32) (i : Usize) (out : alloc.vec.Vec U8) (limit : Usize)
    (ho : out.val.length ≤ limit.val) :
    ∃ r, rdfxml.utf8_from w i out limit = .ok r ∧
      ∀ v, r = .Ok v ↔ ((∀ c ∈ (word w).drop i.val, Rowl.Encoding.Scalar c) ∧
        (out.val ++ utf8Bytes ((word w).drop i.val)).length ≤ limit.val ∧
        v.val = out.val ++ utf8Bytes ((word w).drop i.val)) := by
  rw [rdfxml.utf8_from]
  by_cases lt : i.val < w.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len w) (by simpa using lt)
    have dw : (word w).drop i.val = w.val[i.val].val :: (word w).drop i1.val := by
      rw [hi1v]; simp only [word]; exact (map_drop_cons _ _ lt).symm
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq w i lt]
    rw [dw]
    obtain ⟨o, ho', hoc⟩ := Rowl.Encoding.encode_total_correct w.val[i.val]
    rw [ho']
    cases o with
    | none =>
      have ns : ¬ Rowl.Encoding.Scalar w.val[i.val].val := hoc
      refine ⟨.Err .InvalidCharacter, by simp, fun v => ?_⟩
      simp [ns]
    | some e =>
      have eb := encode_bytes w.val[i.val] e ho'
      have sc := encode_scalar w.val[i.val] e ho'
      obtain ⟨acc, after, ha, hb⟩ := Rowl.NTriples.append_encoded_total_correct out e limit ho
      obtain ⟨hacc, hafter, hlen⟩ := hb
      rw [eb] at hacc hafter
      simp only [ha, bind_ok]
      have cons_len : (out.val ++ utf8Bytes (w.val[i.val].val :: (word w).drop i1.val)).length =
          out.val.length + ((Rowl.IriResolution.utf8 w.val[i.val].val).map byte).length +
            (utf8Bytes ((word w).drop i1.val)).length := by
        simp [utf8Bytes_cons]; omega
      cases acc with
      | false =>
        refine ⟨.Err .ResourceLimit, by simp, fun v => ?_⟩
        simp only [decide_eq_false_iff_not, Bool.false_eq] at hacc
        simp only [reduceCtorEq, false_iff, not_and]
        intro _ hl
        rw [cons_len] at hl
        exact absurd (by omega) hacc
      | true =>
        have fits : out.val.length + ((Rowl.IriResolution.utf8 w.val[i.val].val).map byte).length ≤ limit.val := by
          simpa using hacc.symm
        have av : after.val = out.val ++ (Rowl.IriResolution.utf8 w.val[i.val].val).map byte := by
          rw [hafter, List.take_of_length_le (by omega)]
        obtain ⟨r, hr, hrc⟩ := utf8_from_eq w i1 after limit hlen
        refine ⟨r, by simp [hi1, hr], fun v => ?_⟩
        rw [hrc v, av]
        simp only [List.mem_cons, forall_eq_or_imp, utf8Bytes_cons, List.append_assoc]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨sc, h1⟩, h2, h3⟩
        · rintro ⟨⟨_, h1⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
  · have e : (word w).drop i.val = [] := List.drop_eq_nil_of_le (by simp [word]; omega)
    refine ⟨.Ok out, by simp [UScalar.lt_equiv, lt], fun v => ?_⟩
    simp only [e, utf8Bytes_nil, List.append_nil, List.not_mem_nil, false_imp_iff, implies_true, true_and]
    constructor
    · intro h; simp at h; subst h; exact ⟨ho, rfl⟩
    · rintro ⟨-, h⟩; simp; exact (alloc.vec.Vec.ext _ _ h).symm
termination_by w.val.length - i.val
decreasing_by omega

theorem utf8_eq (w : alloc.vec.Vec U32) (limits : rdfxml.Limits) :
    ∃ r, rdfxml.utf8 w limits = .ok r ∧ ∀ v, r = .Ok v ↔ Spelled limits.term_bytes.val (word w) v.val := by
  obtain ⟨r, hr, hc⟩ := utf8_from_eq w 0#usize (alloc.vec.Vec.new U8) limits.term_bytes (by simp)
  refine ⟨r, by rw [rdfxml.utf8, hr], fun v => ?_⟩
  rw [hc v]
  simp only [usize_zero_val, List.drop_zero, new_val, List.nil_append, Spelled]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a, c, c ▸ b⟩
  · rintro ⟨a, b, c⟩; exact ⟨a, b ▸ c, b⟩

theorem valid_iri_eq (bytes : alloc.vec.Vec U8) :
    rdfxml.valid_iri bytes = .ok (decide (Rowl.NTriples.AbsoluteIri bytes.val)) := by
  by_cases valid : Rowl.NTriples.AbsoluteIri bytes.val
  · have recognized := (Rowl.Iri.validate_iri_accepted_iff bytes).mpr valid
    simp [rdfxml.valid_iri, recognized, valid]
  · obtain ⟨result, run, _⟩ := Rowl.Iri.validate_iri_total_correct bytes
    have notTrue : result ≠ .Matched true := by
      intro e; subst e; exact valid ((Rowl.Iri.validate_iri_accepted_iff bytes).mp run)
    cases result with
    | Matched b =>
      cases b with
      | true => exact absurd rfl notTrue
      | false => simp [rdfxml.valid_iri, run, valid]
    | MalformedUtf8 _ => simp [rdfxml.valid_iri, run, valid]

theorem iri_of_eq (w : alloc.vec.Vec U32) (limits : rdfxml.Limits) :
    ∃ r, rdfxml.iri_of w limits = .ok r ∧ ∀ i, r = .Ok i ↔
      Spelled limits.term_bytes.val (word w) i.spelling.val ∧ Rowl.NTriples.AbsoluteIri i.spelling.val := by
  obtain ⟨r, hr, hc⟩ := utf8_eq w limits
  rw [rdfxml.iri_of, hr]
  simp only [bind_ok]
  cases r with
  | Err e =>
    refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], fun i => ?_⟩
    simp only [reduceCtorEq, false_iff, not_and]
    intro sp _
    exact absurd ((hc i.spelling).mpr sp) (by simp)
  | Ok v =>
    have hv := (hc v).mp rfl
    by_cases valid : Rowl.NTriples.AbsoluteIri v.val
    · refine ⟨.Ok ⟨v⟩, by simp [core.result.Result.Insts.CoreOpsTry.branch, valid_iri_eq, valid], fun i => ?_⟩
      constructor
      · intro e; simp at e; subst e; exact ⟨hv, valid⟩
      · rintro ⟨sp, _⟩
        have : i.spelling = v := alloc.vec.Vec.ext _ _ (sp.2.1.trans hv.2.1.symm)
        cases i; simp at this; subst this; rfl
    · refine ⟨.Err .InvalidIri, by simp [core.result.Result.Insts.CoreOpsTry.branch, valid_iri_eq, valid], fun i => ?_⟩
      simp only [reduceCtorEq, false_iff, not_and]
      intro sp av
      have : i.spelling.val = v.val := sp.2.1.trans hv.2.1.symm
      exact valid (this ▸ av)

theorem bytes_word_inj {a b : List U8} (h : Rowl.References.Word a = Rowl.References.Word b) : a = b :=
  List.map_injective_iff.mpr (fun (x y : U8) (e : x.val = y.val) => UScalar.eq_of_val_eq e) h

theorem resolved_bytes_eq (base reference : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (hb : base.val.length ≤ limits.term_bytes.val) (hr : reference.val.length ≤ limits.term_bytes.val)
    (small : limits.term_bytes.val < Usize.max / 8) :
    ∃ r, rdfxml.resolved_bytes base reference limits = .ok r ∧ ∀ t, r = .Ok t ↔
      (IriReference reference.val ∧
        Rowl.IriResolution.resolve (Rowl.References.Word base.val) (Rowl.References.Word reference.val) =
          some (Rowl.References.Word t.val) ∧ t.val.length ≤ limits.term_bytes.val) := by
  unfold rdfxml.resolved_bytes
  obtain ⟨b, hbr, hbc⟩ := Rowl.References.is_reference_total_correct reference
  rw [hbr]; simp only [bind_ok]
  cases b with
  | false =>
    refine ⟨.Err .InvalidIri, by simp, fun t => ?_⟩
    have : ¬ IriReference reference.val := fun h => by simpa using hbc.mpr h
    simp [this]
  | true =>
    have isref : IriReference reference.val := hbc.mp rfl
    obtain ⟨res, hres, hresv⟩ := Rowl.References.resolve_total_correct base reference
    rw [if_pos ⟨by omega, by omega⟩] at hresv
    simp only [ite_true, hres, bind_ok]
    cases res with
    | none =>
      refine ⟨.Err .InvalidIri, by simp, fun t => ?_⟩
      simp only [Option.map_none] at hresv
      simp [← hresv]
    | some target =>
      simp only [Option.map_some] at hresv
      by_cases fits : target.val.length ≤ limits.term_bytes.val
      · have fits' : alloc.vec.Vec.len target ≤ limits.term_bytes := by simpa [UScalar.le_equiv] using fits
        refine ⟨.Ok target, by simp [fits'], fun t => ?_⟩
        rw [← hresv]
        constructor
        · intro e; simp at e; subst e; exact ⟨isref, rfl, fits⟩
        · rintro ⟨-, e, -⟩
          simp only [Option.some.injEq] at e
          have : target = t := alloc.vec.Vec.ext _ _ (bytes_word_inj e)
          rw [this]
      · have fits' : ¬ alloc.vec.Vec.len target ≤ limits.term_bytes := by simpa [UScalar.le_equiv] using fits
        refine ⟨.Err .ResourceLimit, by simp [fits'], fun t => ?_⟩
        rw [← hresv]
        simp only [reduceCtorEq, false_iff, not_and, Option.some.injEq]
        intro _ e le
        have : target.val = t.val := bytes_word_inj e
        rw [this] at fits; exact fits le

theorem spelled_unique {limit : Nat} {w : Word} {a b : List U8} (ha : Spelled limit w a) (hb : Spelled limit w b) :
    a = b := ha.2.1.trans hb.2.1.symm

/-- What resolving a spelled reference against the base of `c` must give. -/
theorem resolved_ref_iff (c : Ctx) (base ref : alloc.vec.Vec U8) (v : Word) (limits : rdfxml.Limits)
    (hc : c.base = base.val) (ht : c.termLimit = limits.term_bytes.val)
    (sp : Spelled limits.term_bytes.val v ref.val) (t : List U8) :
    ResolvedRef c v t ↔ (IriReference ref.val ∧
      Rowl.IriResolution.resolve (Rowl.References.Word base.val) (Rowl.References.Word ref.val) =
        some (Rowl.References.Word t) ∧ t.length ≤ limits.term_bytes.val) := by
  simp only [ResolvedRef, hc, ht]
  constructor
  · rintro ⟨r, hr, hi, hres, hl⟩
    rw [spelled_unique hr sp] at hi hres
    exact ⟨hi, hres, hl⟩
  · rintro ⟨hi, hres, hl⟩
    exact ⟨ref.val, sp, hi, hres, hl⟩

theorem resolved_tail (c : Ctx) (base ref : alloc.vec.Vec U8) (v : Word) (limits : rdfxml.Limits)
    (hc : c.base = base.val) (ht : c.termLimit = limits.term_bytes.val)
    (hb : base.val.length ≤ limits.term_bytes.val) (small : limits.term_bytes.val < Usize.max / 8)
    (sp : Spelled limits.term_bytes.val v ref.val) :
    ∃ r2, rdfxml.resolved_bytes base ref limits = .ok r2 ∧
      (∀ e, r2 = .Err e → ∀ i : List U8, ¬ Resolved c v i) ∧
      (∀ t, r2 = .Ok t → ((Rowl.NTriples.AbsoluteIri t.val → ∀ i : List U8, Resolved c v i ↔ i = t.val) ∧
        (¬ Rowl.NTriples.AbsoluteIri t.val → ∀ i : List U8, ¬ Resolved c v i))) := by
  obtain ⟨r2, hr2, hc2⟩ := resolved_bytes_eq base ref limits hb sp.2.2 small
  refine ⟨r2, hr2, ?_, ?_⟩
  · rintro e rfl i ⟨h, _⟩
    have bound : i.length ≤ Usize.max := by
      have := ((resolved_ref_iff c base ref v limits hc ht sp i).mp h).2.2
      have := Rowl.XmlScan.usize_le_max limits.term_bytes; omega
    have := (hc2 (alloc.vec.Vec.from i bound)).mpr (by simpa using (resolved_ref_iff c base ref v limits hc ht sp i).mp h)
    simp at this
  · rintro t rfl
    have ht2 := (hc2 t).mp rfl
    have same : ∀ i : List U8, ResolvedRef c v i → i = t.val := by
      intro i h
      have h2 := (resolved_ref_iff c base ref v limits hc ht sp i).mp h
      exact bytes_word_inj (Option.some.inj (h2.2.1.symm.trans ht2.2.1))
    refine ⟨fun valid i => ⟨fun h => same i h.1, fun e => ?_⟩, fun invalid i h => invalid ?_⟩
    · subst e; exact ⟨(resolved_ref_iff c base ref v limits hc ht sp _).mpr ht2, valid⟩
    · rw [← same i h.1]; exact h.2

theorem resolved_eq (c : Ctx) (base : alloc.vec.Vec U8) (v : alloc.vec.Vec U32) (limits : rdfxml.Limits)
    (hc : c.base = base.val) (ht : c.termLimit = limits.term_bytes.val)
    (hb : base.val.length ≤ limits.term_bytes.val) (small : limits.term_bytes.val < Usize.max / 8) :
    ∃ r, rdfxml.resolved base v limits = .ok r ∧ ∀ i, r = .Ok i ↔ Resolved c (word v) i.spelling.val := by
  rw [rdfxml.resolved]
  obtain ⟨r1, hr1, hc1⟩ := utf8_eq v limits
  rw [hr1]; simp only [bind_ok]
  cases r1 with
  | Err e =>
    refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], fun i => ?_⟩
    simp only [reduceCtorEq, false_iff]
    rintro ⟨⟨r, sp, -⟩, -⟩
    have bound : r.length ≤ Usize.max := by
      have := sp.2.2; have := Rowl.XmlScan.usize_le_max limits.term_bytes; omega
    have := (hc1 (alloc.vec.Vec.from r bound)).mpr (by rw [← ht]; simpa using sp)
    simp at this
  | Ok ref =>
    have sp := (hc1 ref).mp rfl
    obtain ⟨r2, hr2, errs, oks⟩ := resolved_tail c base ref (word v) limits hc ht hb small sp
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hr2]
    cases r2 with
    | Err e =>
      refine ⟨.Err e, by simp [residual], fun i => ?_⟩
      simp only [reduceCtorEq, false_iff]
      exact errs e rfl _
    | Ok t =>
      obtain ⟨good, bad⟩ := oks t rfl
      by_cases valid : Rowl.NTriples.AbsoluteIri t.val
      · refine ⟨.Ok ⟨t⟩, by simp [valid_iri_eq, valid], fun i => ?_⟩
        rw [good valid]
        constructor
        · intro e; simp at e; subst e; rfl
        · intro e
          have : i.spelling = t := alloc.vec.Vec.ext _ _ e
          cases i; simp at this; subst this; rfl
      · refine ⟨.Err .InvalidIri, by simp [valid_iri_eq, valid], fun i => ?_⟩
        simp only [reduceCtorEq, false_iff]
        exact bad valid _

theorem scalar_hash : Rowl.Encoding.Scalar 35 := by simp [Rowl.Encoding.Scalar]

theorem utf8Bytes_hash (w : Word) : utf8Bytes (35 :: w) = 35#u8 :: utf8Bytes w := by
  rw [utf8Bytes_cons, utf8_ascii 35 (by omega)]
  simp only [List.map_cons, List.map_nil, List.singleton_append]
  congr 1

theorem resolved_id_eq (c : Ctx) (base : alloc.vec.Vec U8) (v : alloc.vec.Vec U32) (limits : rdfxml.Limits)
    (hc : c.base = base.val) (ht : c.termLimit = limits.term_bytes.val)
    (hb : base.val.length ≤ limits.term_bytes.val) (small : limits.term_bytes.val < Usize.max / 8)
    (pos : 0 < limits.term_bytes.val) :
    ∃ r, rdfxml.resolved_id base v limits = .ok r ∧
      ∀ i, r = .Ok i ↔ Resolved c (35 :: word v) i.spelling.val := by
  rw [rdfxml.resolved_id]
  have one : 1 ≤ Usize.max := by omega
  have hp : alloc.vec.Vec.push (alloc.vec.Vec.new U8) 35#u8 =
      .ok (alloc.vec.Vec.from [35#u8] (by simpa using one)) := by
    rw [push_eq _ _ (by simp; omega)]; simp
  rw [hp]; simp only [bind_ok]
  obtain ⟨r1, hr1, hc1⟩ := utf8_from_eq v 0#usize (alloc.vec.Vec.from [35#u8] (by simpa using one))
    limits.term_bytes (by simp; omega)
  have spell : ∀ b : alloc.vec.Vec U8, r1 = .Ok b ↔ Spelled limits.term_bytes.val (35 :: word v) b.val := by
    intro b
    rw [hc1 b]
    simp only [usize_zero_val, List.drop_zero, alloc.vec.Vec.from_val, Spelled, List.mem_cons,
      forall_eq_or_imp, utf8Bytes_hash, List.singleton_append]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨scalar_hash, h1⟩, h3, h3 ▸ h2⟩
    · rintro ⟨⟨_, h1⟩, h2, h3⟩; exact ⟨h1, h2 ▸ h3, h2⟩
  rw [hr1]; simp only [bind_ok]
  cases r1 with
  | Err e =>
    refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], fun i => ?_⟩
    simp only [reduceCtorEq, false_iff]
    rintro ⟨⟨r, sp, -⟩, -⟩
    have bound : r.length ≤ Usize.max := by
      have := sp.2.2; have := Rowl.XmlScan.usize_le_max limits.term_bytes; omega
    have := (spell (alloc.vec.Vec.from r bound)).mpr (by rw [← ht]; simpa using sp)
    simp at this
  | Ok ref =>
    have sp := (spell ref).mp rfl
    obtain ⟨r2, hr2, errs, oks⟩ := resolved_tail c base ref (35 :: word v) limits hc ht hb small sp
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hr2]
    cases r2 with
    | Err e =>
      refine ⟨.Err e, by simp [residual], fun i => ?_⟩
      simp only [reduceCtorEq, false_iff]
      exact errs e rfl _
    | Ok t =>
      obtain ⟨good, bad⟩ := oks t rfl
      by_cases valid : Rowl.NTriples.AbsoluteIri t.val
      · refine ⟨.Ok ⟨t⟩, by simp [valid_iri_eq, valid], fun i => ?_⟩
        rw [good valid]
        constructor
        · intro e; simp at e; subst e; rfl
        · intro e
          have : i.spelling = t := alloc.vec.Vec.ext _ _ e
          cases i; simp at this; subst this; rfl
      · refine ⟨.Err .InvalidIri, by simp [valid_iri_eq, valid], fun i => ?_⟩
        simp only [reduceCtorEq, false_iff]
        exact bad valid _

/-! ## Literals -/

theorem utf8Bytes_ascii (w : Word) (h : ∀ c ∈ w, c < 128) : utf8Bytes w = w.map byte := by
  induction w with
  | nil => simp [utf8Bytes]
  | cons c rest ih =>
    rw [utf8Bytes_cons, utf8_ascii c (h c List.mem_cons_self), ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    simp

theorem xsdString_eq : xsdString = [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8,
    119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8,
    103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8,
    76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 115#u8,
    116#u8, 114#u8, 105#u8, 110#u8, 103#u8] := by
  rw [xsdString, utf8Bytes_ascii _ (by decide)]
  decide

theorem langString_eq : rdfBytes "langString" = [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8,
    119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8,
    49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8,
    45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8,
    97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 108#u8, 97#u8, 110#u8,
    103#u8, 83#u8, 116#u8, 114#u8, 105#u8, 110#u8, 103#u8] := by
  rw [rdfBytes, utf8Bytes_ascii _ (by decide)]
  decide

theorem iri_ext {a b : rdf.RdfIri} (h : a.spelling.val = b.spelling.val) : a = b := by
  obtain ⟨a⟩ := a; obtain ⟨b⟩ := b
  have : a = b := alloc.vec.Vec.ext _ _ h
  subst this; rfl

theorem literalTerm_inj {a b : rdf.RdfLiteral} (h : literalTerm a = literalTerm b) : a = b := by
  obtain ⟨la, ka⟩ := a
  obtain ⟨lb, kb⟩ := b
  cases ka <;> cases kb <;> simp [literalTerm] at h
  · obtain ⟨h1, h2⟩ := h
    have e1 : la = lb := alloc.vec.Vec.ext _ _ h1
    subst e1; simp [iri_ext h2]
  · obtain ⟨h1, h2⟩ := h
    have e1 : la = lb := alloc.vec.Vec.ext _ _ h1
    have e2 : _ := alloc.vec.Vec.ext _ _ h2
    subst e1; subst e2; rfl

theorem rdf_iri_val (s : Slice U8) : rdfxml.rdf_iri s = .ok ⟨alloc.vec.Vec.from s.val s.property⟩ := by
  obtain ⟨i, hi, hv⟩ := rdf_iri_eq s
  rw [hi]
  congr 1
  apply iri_ext
  simp [hv]

theorem literalOf_iff (c : Ctx) (v : Word) (t : Term) :
    LiteralOf c v t ↔ (c.lang = [] ∧ ∃ b, Spelled c.termLimit v b ∧ t = .literal b (.datatype xsdString)) ∨
      (c.lang ≠ [] ∧ ∃ b g, Spelled c.termLimit v b ∧ Spelled c.termLimit c.lang g ∧
        Rowl.NTriples.LanguageTag g ∧ t = .literal b (.language g)) := by
  constructor
  · intro h
    cases h with
    | plain h0 sp => exact .inl ⟨h0, _, sp, rfl⟩
    | tagged h0 sp sg tag => exact .inr ⟨h0, _, _, sp, sg, tag, rfl⟩
  · rintro (⟨h0, b, sp, rfl⟩ | ⟨h0, b, g, sp, sg, tag, rfl⟩)
    · exact .plain h0 sp
    · exact .tagged h0 sp sg tag

theorem langtag_eq (bytes : alloc.vec.Vec U8) :
    langtag.well_formed bytes = .ok (decide (Rowl.NTriples.LanguageTag bytes.val)) := by
  obtain ⟨accepted, run⟩ := Rowl.LangTag.well_formed_total_correct bytes
  by_cases tag : Rowl.NTriples.LanguageTag bytes.val
  · rw [(Rowl.LangTag.well_formed_accepted_iff bytes).mpr tag]; simp [tag]
  · cases accepted with
    | true => exact absurd ((Rowl.LangTag.well_formed_accepted_iff bytes).mp run) tag
    | false => rw [run]; simp [tag]

theorem vec_of_spelled {limit : Nat} {w : Word} {b : List U8} (sp : Spelled limit w b) (h : limit ≤ Usize.max) :
    b.length ≤ Usize.max := Nat.le_trans sp.2.2 h

theorem literal_of_eq (c : Ctx) (v lang : alloc.vec.Vec U32) (limits : rdfxml.Limits)
    (hl : c.lang = word lang) (ht : c.termLimit = limits.term_bytes.val) :
    ∃ r, rdfxml.literal_of v lang limits = .ok r ∧
      ∀ l, r = .Ok l ↔ LiteralOf c (word v) (literalTerm l) := by
  rw [rdfxml.literal_of]
  have lim := Rowl.XmlScan.usize_le_max limits.term_bytes
  obtain ⟨r1, hr1, hc1⟩ := utf8_eq v limits
  rw [hr1]; simp only [bind_ok]
  cases r1 with
  | Err e =>
    refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], fun l => ?_⟩
    simp only [reduceCtorEq, false_iff, literalOf_iff]
    rintro (⟨_, b, sp, _⟩ | ⟨_, b, g, sp, _⟩) <;>
    · have := (hc1 (alloc.vec.Vec.from b (vec_of_spelled sp (by omega)))).mpr (by rw [← ht]; simpa using sp)
      simp at this
  | Ok lex =>
    have sp := (hc1 lex).mp rfl
    rw [← ht] at sp
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    by_cases empty : lang.val.length = 0
    · have e0 : alloc.vec.Vec.len lang = 0#usize := UScalar.eq_of_val_eq (by simpa using empty)
      have lang0 : c.lang = [] := by
        rw [hl]; simp [word]; exact List.eq_nil_of_length_eq_zero empty
      refine ⟨.Ok ⟨lex, .Datatype ⟨alloc.vec.Vec.from xsdString (by rw [xsdString_eq]; simp; scalar_tac)⟩⟩,
        by simp [e0, lift, rdf_iri_val, xsdString_eq, slice_val], fun l => ?_⟩
      rw [literalOf_iff]
      simp only [lang0, true_and, ne_eq, not_true_eq_false, false_and, or_false]
      constructor
      · intro e; simp at e; subst e
        exact ⟨lex.val, sp, by simp [literalTerm]⟩
      · rintro ⟨b, sp2, e⟩
        congr 1
        apply literalTerm_inj
        rw [e, ← spelled_unique sp sp2]
        simp [literalTerm]
    · have e0 : ¬ alloc.vec.Vec.len lang = 0#usize := fun e => empty (by simpa using congrArg UScalar.val e)
      have lang0 : c.lang ≠ [] := by
        rw [hl]; simp [word]; intro e; exact empty (by simp [e])
      simp only [e0, ite_false]
      obtain ⟨r2, hr2, hc2⟩ := utf8_eq lang limits
      rw [hr2]; simp only [bind_ok]
      cases r2 with
      | Err e =>
        refine ⟨.Err e, by simp [residual], fun l => ?_⟩
        simp only [reduceCtorEq, false_iff, literalOf_iff, lang0, false_and, false_or, ne_eq,
          not_false_eq_true, true_and]
        rintro ⟨b, g, _, sg, _⟩
        rw [hl, ht] at sg
        have := (hc2 (alloc.vec.Vec.from g (vec_of_spelled sg (by omega)))).mpr (by simpa using sg)
        simp at this
      | Ok tag =>
        have sg := (hc2 tag).mp rfl
        rw [← hl, ← ht] at sg
        by_cases wf : Rowl.NTriples.LanguageTag tag.val
        · refine ⟨.Ok ⟨lex, .Language tag⟩, by simp [langtag_eq, wf], fun l => ?_⟩
          rw [literalOf_iff]
          simp only [lang0, false_and, false_or, ne_eq, not_false_eq_true, true_and]
          constructor
          · intro e; simp at e; subst e
            exact ⟨lex.val, tag.val, sp, sg, wf, by simp [literalTerm]⟩
          · rintro ⟨b, g, sp2, sg2, _, e⟩
            congr 1
            apply literalTerm_inj
            rw [e, ← spelled_unique sp sp2, ← spelled_unique sg sg2]
            simp [literalTerm]
        · refine ⟨.Err .InvalidLanguageTag, by simp [langtag_eq, wf], fun l => ?_⟩
          simp only [reduceCtorEq, false_iff, literalOf_iff, lang0, false_and, false_or, ne_eq,
            not_false_eq_true, true_and]
          rintro ⟨b, g, _, sg2, tg, _⟩
          rw [← spelled_unique sg sg2] at tg
          exact wf tg

theorem lang_string_eq (bytes : alloc.vec.Vec U8) :
    rdfxml.lang_string bytes = .ok (decide (bytes.val = rdfBytes "langString")) := by
  unfold rdfxml.lang_string
  simp only [lift, bind_ok]
  obtain ⟨v, hv, hval⟩ := constant_eq (Array.to_slice (Array.make 53#usize _ _))
  rw [hv]; simp only [bind_ok]
  rw [same_bytes_eq, hval, slice_val, langString_eq]

theorem typedOf_iff (c : Ctx) (v d : Word) (t : Term) :
    TypedOf c v d t ↔ ∃ b i, Spelled c.termLimit v b ∧ IriOf c d i ∧ i ≠ rdfBytes "langString" ∧
      t = .literal b (.datatype i) := by
  constructor
  · intro h; cases h with
    | mk sp io ne => exact ⟨_, _, sp, io, ne, rfl⟩
  · rintro ⟨b, i, sp, io, ne, rfl⟩; exact .mk sp io ne

theorem typed_of_eq (c : Ctx) (v d : alloc.vec.Vec U32) (limits : rdfxml.Limits)
    (ht : c.termLimit = limits.term_bytes.val) :
    ∃ r, rdfxml.typed_of v d limits = .ok r ∧ ∀ l, r = .Ok l ↔ TypedOf c (word v) (word d) (literalTerm l) := by
  rw [rdfxml.typed_of]
  have lim := Rowl.XmlScan.usize_le_max limits.term_bytes
  obtain ⟨r1, hr1, hc1⟩ := utf8_eq v limits
  rw [hr1]; simp only [bind_ok]
  cases r1 with
  | Err e =>
    refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], fun l => ?_⟩
    simp only [reduceCtorEq, false_iff, typedOf_iff]
    rintro ⟨b, i, sp, -⟩
    have := (hc1 (alloc.vec.Vec.from b (vec_of_spelled sp (by omega)))).mpr (by rw [← ht]; simpa using sp)
    simp at this
  | Ok lex =>
    have sp := (hc1 lex).mp rfl
    rw [← ht] at sp
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨r2, hr2, hc2⟩ := iri_of_eq d limits
    rw [hr2]; simp only [bind_ok]
    cases r2 with
    | Err e =>
      refine ⟨.Err e, by simp [residual], fun l => ?_⟩
      simp only [reduceCtorEq, false_iff, typedOf_iff]
      rintro ⟨b, i, -, io, -⟩
      have := (hc2 ⟨alloc.vec.Vec.from i (vec_of_spelled io.1 (by omega))⟩).mpr (by
        rw [← ht]; simpa using (show Spelled c.termLimit (word d) i ∧ Rowl.NTriples.AbsoluteIri i from io))
      simp at this
    | Ok dt =>
      have io := (hc2 dt).mp rfl
      rw [← ht] at io
      by_cases ls : dt.spelling.val = rdfBytes "langString"
      · refine ⟨.Err .InvalidDatatype, by simp [lang_string_eq, ls], fun l => ?_⟩
        simp only [reduceCtorEq, false_iff, typedOf_iff]
        rintro ⟨b, i, -, io2, ne, -⟩
        exact ne (by rw [← spelled_unique io.1 io2.1]; exact ls)
      · refine ⟨.Ok ⟨lex, .Datatype dt⟩, by simp [lang_string_eq, ls], fun l => ?_⟩
        rw [typedOf_iff]
        constructor
        · intro e; simp at e; subst e
          exact ⟨lex.val, dt.spelling.val, sp, ⟨io.1, io.2⟩, ls, by simp [literalTerm]⟩
        · rintro ⟨b, i, sp2, io2, _, e⟩
          congr 1
          apply literalTerm_inj
          rw [e, ← spelled_unique sp sp2, ← spelled_unique io.1 io2.1]
          simp [literalTerm]

/-! ## Decimal digits and generated blank nodes -/

theorem digits_length (n k : Nat) (h : n < 10 ^ (k + 1)) : (digits n).length ≤ k + 1 := by
  induction k generalizing n with
  | zero =>
    have : n < 10 := by simpa using h
    rw [digits]; simp [this]
  | succ k ih =>
    rw [digits]
    by_cases small : n < 10
    · simp [small]
    · simp only [small, ite_false, List.length_append, List.length_singleton]
      have := ih (n / 10) (by rw [Nat.pow_succ] at h; omega)
      omega

theorem usize_digits (n : Usize) : (digits n.val).length ≤ 20 := by
  have : n.val < 10 ^ 20 := by
    have := n.hBounds
    have p : 2 ^ UScalarTy.Usize.numBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by
      cases System.Platform.numBits_eq <;> simp [UScalarTy.numBits, *])
    have : (2 : Nat) ^ 64 < 10 ^ 20 := by norm_num
    simp only [UScalar.val] at *
    omega
  exact digits_length n.val 19 this

theorem digits_eq (n : Usize) (out : alloc.vec.Vec U8) (room : out.val.length + 20 ≤ Usize.max) :
    ∃ v, rdfxml.digits n out = .ok v ∧ v.val = out.val ++ (digits n.val).map byte := by
  rw [rdfxml.digits]
  obtain ⟨m, hm, hmv⟩ := WP.spec_imp_exists (Usize.rem_spec n (y := 10#usize) (by simp))
  have hmv' : m.val = n.val % 10 := by simpa using hmv
  have cast : (UScalar.cast .U8 m).val = n.val % 10 := by rw [UScalar.cast_val_eq, hmv']; simp; omega
  obtain ⟨d, hd, hdv⟩ := WP.spec_imp_exists (U8.add_spec (x := 48#u8) (y := UScalar.cast .U8 m)
    (by rw [cast]; have := Nat.mod_lt n.val (show 10 > 0 by omega); scalar_tac))
  have hdv' : d.val = 48 + n.val % 10 := by rw [hdv, cast]; simp
  have dbyte : d = byte (48 + n.val % 10) := UScalar.eq_of_val_eq (by rw [hdv', byte_val_eq _ (by omega)])
  by_cases small : n.val < 10
  · have small' : n < 10#usize := by simpa [UScalar.lt_equiv] using small
    refine ⟨alloc.vec.Vec.from (out.val ++ [d]) (by simp; omega), ?_, ?_⟩
    · simp [small', hm, lift, hd, push_eq out d (by omega)]
    · rw [digits]; simp [small, dbyte]
  · have small' : ¬ n < 10#usize := by simpa [UScalar.lt_equiv] using small
    obtain ⟨q, hq, hqv⟩ := WP.spec_imp_exists (Usize.div_spec n (y := 10#usize) (by simp))
    have hqv' : q.val = n.val / 10 := by simpa using hqv
    obtain ⟨v, hv, hval⟩ := digits_eq q out room
    have dl : (digits q.val).length + 1 ≤ 20 := by
      have := usize_digits n; rw [digits] at this; simp [small, hqv'] at this; rw [hqv']; omega
    have lv : v.val.length < Usize.max := by
      rw [hval]; simp; omega
    refine ⟨alloc.vec.Vec.from (v.val ++ [d]) (by simp; omega), ?_, ?_⟩
    · simp [small', hq, hv, hm, lift, hd, push_eq v d lv]
    · rw [digits]; simp [small, dbyte, hval, hqv']
termination_by n.val
decreasing_by omega

theorem digit_points_eq (n : Usize) (out : alloc.vec.Vec U32) (room : out.val.length + 20 ≤ Usize.max) :
    ∃ v, rdfxml.digit_points n out = .ok v ∧ word v = word out ++ digits n.val := by
  rw [rdfxml.digit_points]
  obtain ⟨m, hm, hmv⟩ := WP.spec_imp_exists (Usize.rem_spec n (y := 10#usize) (by simp))
  have hmv' : m.val = n.val % 10 := by simpa using hmv
  have cast : (UScalar.cast .U32 m).val = n.val % 10 := by rw [UScalar.cast_val_eq, hmv']; simp; omega
  obtain ⟨d, hd, hdv⟩ := WP.spec_imp_exists (U32.add_spec (x := 48#u32) (y := UScalar.cast .U32 m)
    (by rw [cast]; have := Nat.mod_lt n.val (show 10 > 0 by omega); scalar_tac))
  have hdv' : d.val = 48 + n.val % 10 := by rw [hdv, cast]; simp
  by_cases small : n.val < 10
  · have small' : n < 10#usize := by simpa [UScalar.lt_equiv] using small
    refine ⟨alloc.vec.Vec.from (out.val ++ [d]) (by simp; omega), ?_, ?_⟩
    · simp [small', hm, lift, hd, push_eq out d (by omega)]
    · rw [digits]; simp [small, word, hdv']
  · have small' : ¬ n < 10#usize := by simpa [UScalar.lt_equiv] using small
    obtain ⟨q, hq, hqv⟩ := WP.spec_imp_exists (Usize.div_spec n (y := 10#usize) (by simp))
    have hqv' : q.val = n.val / 10 := by simpa using hqv
    obtain ⟨v, hv, hval⟩ := digit_points_eq q out room
    have dl : (digits q.val).length + 1 ≤ 20 := by
      have := usize_digits n; rw [digits] at this; simp [small, hqv'] at this; rw [hqv']; omega
    have lv : v.val.length < Usize.max := by
      have := congrArg List.length hval; simp [word] at this; omega
    refine ⟨alloc.vec.Vec.from (v.val ++ [d]) (by simp; omega), ?_, ?_⟩
    · simp [small', hq, hv, hm, lift, hd, push_eq v d lv]
    · rw [digits]
      have : word (alloc.vec.Vec.from (v.val ++ [d]) (by simp; omega)) = word v ++ [d.val] := by simp [word]
      rw [this, hval, hqv', hdv']; simp [small]
termination_by n.val
decreasing_by omega

/-! ## States -/

/-- An rdf:ID value with its base IRI. -/
def idView (i : rdfxml.Id) : Word × List U8 := (word i.value, i.base.val)

/-- The specification state of a reader state. -/
def stOf (s : rdfxml.State) : St := ⟨s.blanks.val, s.ids.val.map idView⟩

/-- The statements of a reader state's triples. -/
def stmts (s : rdfxml.State) : List Statement := s.triples.val.map statementOf

theorem fresh_ok (c : Ctx) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (hs : c.scope = scope.val) (lt : state.blanks.val < limits.items.val) :
    ∃ n s', rdfxml.fresh scope limits state = .ok (.Ok (n, s')) ∧
      subjectTerm (.Blank n) = (fresh c (stOf state)).1 ∧ stOf s' = (fresh c (stOf state)).2 ∧
      s'.triples = state.triples ∧ s'.ids = state.ids := by
  unfold rdfxml.fresh
  have lt' : state.blanks < limits.items := by simpa [UScalar.lt_equiv] using lt
  have one : 1 ≤ Usize.max := by have := Rowl.XmlScan.usize_le_max limits.items; omega
  have hp : alloc.vec.Vec.push (alloc.vec.Vec.new U8) 255#u8 =
      .ok (alloc.vec.Vec.from [255#u8] (by simpa using one)) := by
    rw [push_eq _ _ (by simp; omega)]; simp
  obtain ⟨label, hl, hlv⟩ := digits_eq state.blanks (alloc.vec.Vec.from [255#u8] (by simpa using one))
    (by simp; have := Rowl.XmlScan.usize_le_max limits.items; scalar_tac)
  obtain ⟨b1, hb1, hb1v⟩ := Rowl.XmlScan.succ_spec lt
  refine ⟨⟨scope, label⟩, { state with blanks := b1 }, ?_, ?_, ?_, rfl, rfl⟩
  · simp [lt', hp, copy_bytes_eq, hl, hb1]
  · simp only [subjectTerm, fresh, hs, hlv, alloc.vec.Vec.from_val, List.cons_append, List.nil_append]
    congr 2
  · simp [stOf, fresh, hb1v]

theorem fresh_err (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits) (state : rdfxml.State)
    (ge : ¬ state.blanks.val < limits.items.val) :
    rdfxml.fresh scope limits state = .ok (.Err .ResourceLimit) := by
  unfold rdfxml.fresh
  have : ¬ state.blanks < limits.items := by simpa [UScalar.lt_equiv] using ge
  simp [this]

theorem emit_ok (state : rdfxml.State) (t : rdf.Triple) (limits : rdfxml.Limits)
    (lt : state.triples.val.length < limits.items.val) :
    ∃ s', rdfxml.emit state t limits = .ok (.Ok s') ∧ stmts s' = stmts state ++ [statementOf t] ∧
      s'.triples.val.length = state.triples.val.length + 1 ∧ stOf s' = stOf state := by
  unfold rdfxml.emit
  have lt' : alloc.vec.Vec.len state.triples < limits.items := by simpa [UScalar.lt_equiv] using lt
  have room : state.triples.val.length < Usize.max := by
    have := Rowl.XmlScan.usize_le_max limits.items; omega
  refine ⟨{ state with triples := alloc.vec.Vec.from (state.triples.val ++ [t]) (by simp; omega) }, ?_, ?_, ?_, ?_⟩
  · simp [lt', push_eq _ _ room]
  · simp [stmts]
  · simp
  · simp [stOf]

theorem emit_err (state : rdfxml.State) (t : rdf.Triple) (limits : rdfxml.Limits)
    (ge : ¬ state.triples.val.length < limits.items.val) :
    rdfxml.emit state t limits = .ok (.Err .ResourceLimit) := by
  unfold rdfxml.emit
  have : ¬ alloc.vec.Vec.len state.triples < limits.items := by simpa [UScalar.lt_equiv] using ge
  simp [this]

theorem rdf_triple_eq (s : rdf.Subject) (nm : Slice U8) (o : rdf.Object) :
    rdfxml.rdf_triple s nm o = .ok ⟨s, ⟨alloc.vec.Vec.from nm.val nm.property⟩, o⟩ := by
  simp [rdfxml.rdf_triple, copy_subject_eq, rdf_iri_val]

theorem nodeIdOf_iff (c : Ctx) (v : Word) (t : Term) :
    NodeIdOf c v t ↔ NCName v ∧ ∃ b, Spelled c.termLimit v b ∧ t = .blank c.scope b := by
  constructor
  · intro h; cases h with
    | mk nc sp => exact ⟨nc, _, sp, rfl⟩
  · rintro ⟨nc, b, sp, rfl⟩; exact .mk nc sp

theorem node_id_eq (c : Ctx) (v : alloc.vec.Vec U32) (scope : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (hs : c.scope = scope.val) (ht : c.termLimit = limits.term_bytes.val) :
    ∃ r, rdfxml.node_id v scope limits = .ok r ∧
      ∀ n, r = .Ok n ↔ NodeIdOf c (word v) (subjectTerm (.Blank n)) := by
  unfold rdfxml.node_id
  have lim := Rowl.XmlScan.usize_le_max limits.term_bytes
  rw [ncname_eq]
  by_cases nc : NCName (word v)
  · simp only [nc, decide_true, ite_true]
    obtain ⟨r1, hr1, hc1⟩ := utf8_eq v limits
    rw [hr1]; simp only [bind_ok]
    cases r1 with
    | Err e =>
      refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], fun n => ?_⟩
      simp only [reduceCtorEq, false_iff, nodeIdOf_iff, not_and, not_exists]
      intro _ b sp _
      have := (hc1 (alloc.vec.Vec.from b (vec_of_spelled sp (by omega)))).mpr (by rw [← ht]; simpa using sp)
      simp at this
    | Ok lab =>
      have sp := (hc1 lab).mp rfl
      rw [← ht] at sp
      refine ⟨.Ok ⟨scope, lab⟩, by simp [core.result.Result.Insts.CoreOpsTry.branch, copy_bytes_eq],
        fun n => ?_⟩
      rw [nodeIdOf_iff]
      constructor
      · intro e; simp at e; subst e
        exact ⟨nc, lab.val, sp, by simp [subjectTerm, hs]⟩
      · rintro ⟨-, b, sp2, e⟩
        obtain ⟨ns, nl⟩ := n
        simp only [subjectTerm, Term.blank.injEq] at e
        obtain ⟨e1, e2⟩ := e
        have : ns = scope := alloc.vec.Vec.ext _ _ (by rw [e1, hs])
        have : nl = lab := alloc.vec.Vec.ext _ _ (by rw [e2, ← spelled_unique sp sp2])
        subst ns; subst nl; rfl
  · refine ⟨.Err .InvalidId, by simp [nc], fun n => ?_⟩
    simp [nodeIdOf_iff, nc]

theorem same_id_eq (i : rdfxml.Id) (v : alloc.vec.Vec U32) (base : alloc.vec.Vec U8) :
    rdfxml.same_id i v base = .ok (decide (idView i = (word v, base.val))) := by
  unfold rdfxml.same_id
  rw [same_word_eq]
  by_cases h : word i.value = word v
  · simp [h, same_bytes_eq, idView]
  · simp [h, idView]

theorem id_absent_eq (ids : alloc.vec.Vec rdfxml.Id) (v : alloc.vec.Vec U32) (base : alloc.vec.Vec U8) (k : Usize) :
    rdfxml.id_absent ids v base k = .ok (decide ((word v, base.val) ∉ (ids.val.drop k.val).map idView)) := by
  rw [rdfxml.id_absent]
  by_cases lt : k.val < ids.val.length
  · obtain ⟨k1, hk1, hk1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len ids) (by simpa using lt)
    have dw : (ids.val.drop k.val).map idView = idView ids.val[k.val] :: (ids.val.drop k1.val).map idView := by
      rw [hk1v, List.map_drop, List.map_drop]; exact (map_drop_cons _ _ lt).symm
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq ids k lt, same_id_eq]
    rw [dw]
    by_cases same : idView ids.val[k.val] = (word v, base.val)
    · simp [same]
    · simp only [same, decide_false, Bool.false_eq_true, ite_false, hk1, bind_ok]
      rw [id_absent_eq ids v base k1]
      simp only [List.mem_cons, not_or]
      simp [Ne.symm same]
  · have e : ids.val.drop k.val = [] := List.drop_eq_nil_of_le (by omega)
    simp [UScalar.lt_equiv, lt, e]
termination_by ids.val.length - k.val
decreasing_by omega

theorem idIri_iff (c : Ctx) (v : Word) (st : St) (i : List U8) (st' : St) :
    IdIri c v st i st' ↔ NCName v ∧ Resolved c (35 :: v) i ∧ (v, c.base) ∉ st.ids ∧
      st' = ⟨st.blanks, st.ids ++ [(v, c.base)]⟩ := by
  constructor
  · intro h; cases h with
    | mk nc rs nm => exact ⟨nc, rs, nm, rfl⟩
  · rintro ⟨nc, rs, nm, rfl⟩; exact .mk nc rs nm

theorem id_iri_spec (c : Ctx) (v : alloc.vec.Vec U32) (base : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (state : rdfxml.State) (hc : c.base = base.val) (ht : c.termLimit = limits.term_bytes.val)
    (hb : base.val.length ≤ limits.term_bytes.val) (small : limits.term_bytes.val < Usize.max / 8)
    (pos : 0 < limits.term_bytes.val) :
    ∃ r, rdfxml.id_iri v base limits state = .ok r ∧
      (∀ i s', r = .Ok (i, s') → IdIri c (word v) (stOf state) i.spelling.val (stOf s') ∧
        s'.triples = state.triples ∧ s'.ids.val.length ≤ limits.items.val) ∧
      (∀ i st', IdIri c (word v) (stOf state) i st' → st'.ids.length ≤ limits.items.val →
        ∃ ri s', r = .Ok (ri, s') ∧ ri.spelling.val = i ∧ stOf s' = st' ∧ s'.triples = state.triples) := by
  unfold rdfxml.id_iri
  rw [ncname_eq]
  by_cases nc : NCName (word v)
  · simp only [nc, decide_true, ite_true]
    obtain ⟨r1, hr1, hc1⟩ := resolved_id_eq c base v limits hc ht hb small pos
    rw [hr1]; simp only [bind_ok]
    cases r1 with
    | Err e =>
      refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
      intro i st' h _
      rw [idIri_iff] at h
      have bound : i.length ≤ Usize.max := by
        have := h.2.1.1; obtain ⟨r, sp, -, -, hl⟩ := this
        have := Rowl.XmlScan.usize_le_max limits.term_bytes; omega
      have := (hc1 ⟨alloc.vec.Vec.from i bound⟩).mpr (by simpa using h.2.1)
      simp at this
    | Ok iri =>
      have rs := (hc1 iri).mp rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, id_absent_eq]
      by_cases fresh : (word v, base.val) ∈ state.ids.val.map idView
      · refine ⟨.Err .DuplicateId, by simp [fresh], by simp, ?_⟩
        intro i st' h _
        rw [idIri_iff] at h
        exact (h.2.2.1 (by simpa [stOf, hc] using fresh)).elim
      · simp only [usize_zero_val, List.drop_zero, fresh, not_false_eq_true, decide_true, ite_true]
        by_cases room : state.ids.val.length < limits.items.val
        · have room' : alloc.vec.Vec.len state.ids < limits.items := by simpa [UScalar.lt_equiv] using room
          have room2 : state.ids.val.length < Usize.max := by
            have := Rowl.XmlScan.usize_le_max limits.items; omega
          let s' : rdfxml.State := { state with ids := alloc.vec.Vec.from (state.ids.val ++ [⟨v, base⟩]) (by simp; omega) }
          have run : (if alloc.vec.Vec.len state.ids < limits.items then do
              let v1 ← rdfxml.copy_word v
              let v2 ← rdfxml.copy_bytes base
              let ids ← alloc.vec.Vec.push state.ids ({ value := v1, base := v2 } : rdfxml.Id)
              Result.ok (core.result.Result.Ok (iri, { state with ids }))
            else Result.ok (core.result.Result.Err rdfxml.ErrorKind.ResourceLimit)) =
              .ok (.Ok (iri, s')) := by
            simp [room', copy_word_eq, copy_bytes_eq, push_eq _ _ room2, s']
          refine ⟨.Ok (iri, s'), run, ?_, ?_⟩
          · intro i s2 e
            simp at e; obtain ⟨rfl, rfl⟩ := e
            refine ⟨(idIri_iff ..).mpr ⟨nc, rs, by simpa [stOf, hc] using fresh, ?_⟩, rfl, by simp [s']; omega⟩
            simp [stOf, s', idView, hc]
          · intro i st' h _
            rw [idIri_iff] at h
            obtain ⟨-, rs2, -, rfl⟩ := h
            refine ⟨iri, s', rfl, ?_, ?_, rfl⟩
            · have := (hc1 ⟨alloc.vec.Vec.from i (by
                have := rs2.1; obtain ⟨r, sp, -, -, hl⟩ := this
                have := Rowl.XmlScan.usize_le_max limits.term_bytes; omega)⟩).mpr (by simpa using rs2)
              simp at this
              rw [this]; simp
            · simp [stOf, s', idView, hc]
        · have room' : ¬ alloc.vec.Vec.len state.ids < limits.items := by simpa [UScalar.lt_equiv] using room
          refine ⟨.Err .ResourceLimit, by simp [room'], by simp, ?_⟩
          intro i st' h hl
          rw [idIri_iff] at h
          obtain ⟨-, -, -, rfl⟩ := h
          simp [stOf] at hl
          omega
  · refine ⟨.Err .InvalidId, by simp [nc], by simp, ?_⟩
    intro i st' h _
    exact (nc ((idIri_iff ..).mp h).1).elim

/-! ## RDF vocabulary bytes and reification -/

theorem rdfBytes_subject : rdfBytes "subject" = [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 115#u8, 117#u8, 98#u8, 106#u8, 101#u8, 99#u8, 116#u8] := by
  rw [rdfBytes, utf8Bytes_ascii _ (by decide)]
  decide

theorem rdfBytes_predicate : rdfBytes "predicate" = [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 112#u8, 114#u8, 101#u8, 100#u8, 105#u8, 99#u8, 97#u8, 116#u8, 101#u8] := by
  rw [rdfBytes, utf8Bytes_ascii _ (by decide)]
  decide

theorem rdfBytes_object : rdfBytes "object" = [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 111#u8, 98#u8, 106#u8, 101#u8, 99#u8, 116#u8] := by
  rw [rdfBytes, utf8Bytes_ascii _ (by decide)]
  decide

theorem rdfBytes_type : rdfBytes "type" = [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 116#u8, 121#u8, 112#u8, 101#u8] := by
  rw [rdfBytes, utf8Bytes_ascii _ (by decide)]
  decide

theorem rdfBytes_Statement : rdfBytes "Statement" = [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 83#u8, 116#u8, 97#u8, 116#u8, 101#u8, 109#u8, 101#u8, 110#u8, 116#u8] := by
  rw [rdfBytes, utf8Bytes_ascii _ (by decide)]
  decide

theorem rdfBytes_first : rdfBytes "first" = [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 102#u8, 105#u8, 114#u8, 115#u8, 116#u8] := by
  rw [rdfBytes, utf8Bytes_ascii _ (by decide)]
  decide

theorem rdfBytes_rest : rdfBytes "rest" = [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 114#u8, 101#u8, 115#u8, 116#u8] := by
  rw [rdfBytes, utf8Bytes_ascii _ (by decide)]
  decide

theorem rdfBytes_nil : rdfBytes "nil" = [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 110#u8, 105#u8, 108#u8] := by
  rw [rdfBytes, utf8Bytes_ascii _ (by decide)]
  decide

theorem objectTerm_asObject (s : rdf.Subject) : objectTerm (asObject s) = subjectTerm s := by
  cases s <;> rfl

theorem statementOf_mk (s : rdf.Subject) (p : rdf.RdfIri) (o : rdf.Object) :
    statementOf ⟨s, p, o⟩ = ⟨subjectTerm s, p.spelling.val, objectTerm o⟩ := rfl

theorem reify_ok (r : rdf.RdfIri) (s : rdf.Subject) (p : rdf.RdfIri) (o : rdf.Object) (limits : rdfxml.Limits)
    (state : rdfxml.State) (room : state.triples.val.length + 4 ≤ limits.items.val) :
    ∃ s', rdfxml.reify r s p o limits state = .ok (.Ok s') ∧
      stmts s' = stmts state ++ reification r.spelling.val ⟨subjectTerm s, p.spelling.val, objectTerm o⟩ ∧
      s'.triples.val.length = state.triples.val.length + 4 ∧ stOf s' = stOf state := by
  unfold rdfxml.reify
  simp only [copy_iri_eq, bind_ok, lift, object_of_eq, rdf_triple_eq, copy_object_eq]
  obtain ⟨s1, h1, st1, l1, v1⟩ := emit_ok state ⟨.Iri r, ⟨alloc.vec.Vec.from _ (Slice.property _)⟩, asObject s⟩
    limits (by omega)
  rw [h1]; simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨s2, h2, st2, l2, v2⟩ := emit_ok s1 ⟨.Iri r, ⟨alloc.vec.Vec.from _ (Slice.property _)⟩, .Iri p⟩
    limits (by omega)
  rw [h2]; simp only [bind_ok]
  obtain ⟨s3, h3, st3, l3, v3⟩ := emit_ok s2 ⟨.Iri r, ⟨alloc.vec.Vec.from _ (Slice.property _)⟩, o⟩
    limits (by omega)
  rw [h3]; simp only [bind_ok, rdf_iri_val]
  obtain ⟨s4, h4, st4, l4, v4⟩ := emit_ok s3 ⟨.Iri r, ⟨alloc.vec.Vec.from _ (Slice.property _)⟩,
    .Iri ⟨alloc.vec.Vec.from _ (Slice.property _)⟩⟩ limits (by omega)
  refine ⟨s4, h4, ?_, by omega, by rw [v4, v3, v2, v1]⟩
  rw [st4, st3, st2, st1]
  simp only [statementOf_mk, reification, objectTerm_asObject,
    alloc.vec.Vec.from_val, slice_val, List.append_assoc, List.cons_append, List.nil_append]
  simp [rdfBytes_subject, rdfBytes_predicate, rdfBytes_object, rdfBytes_type, rdfBytes_Statement, subjectTerm,
    objectTerm]

theorem reify_err (r : rdf.RdfIri) (s : rdf.Subject) (p : rdf.RdfIri) (o : rdf.Object) (limits : rdfxml.Limits)
    (state : rdfxml.State) (room : ¬ state.triples.val.length + 4 ≤ limits.items.val) :
    ∃ e, rdfxml.reify r s p o limits state = .ok (.Err e) := by
  unfold rdfxml.reify
  simp only [copy_iri_eq, bind_ok, lift, object_of_eq, rdf_triple_eq, copy_object_eq, rdf_iri_val]
  by_cases a1 : state.triples.val.length < limits.items.val
  · obtain ⟨s1, h1, -, l1, -⟩ := emit_ok state ⟨.Iri r, ⟨alloc.vec.Vec.from _ (Slice.property _)⟩, asObject s⟩
      limits a1
    rw [h1]; simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    by_cases a2 : s1.triples.val.length < limits.items.val
    · obtain ⟨s2, h2, -, l2, -⟩ := emit_ok s1 ⟨.Iri r, ⟨alloc.vec.Vec.from _ (Slice.property _)⟩, .Iri p⟩
        limits a2
      rw [h2]; simp only [bind_ok]
      by_cases a3 : s2.triples.val.length < limits.items.val
      · obtain ⟨s3, h3, -, l3, -⟩ := emit_ok s2 ⟨.Iri r, ⟨alloc.vec.Vec.from _ (Slice.property _)⟩, o⟩
          limits a3
        rw [h3]; simp only [bind_ok]
        exact ⟨_, emit_err _ _ _ (by omega)⟩
      · rw [emit_err _ _ _ a3]; exact ⟨.ResourceLimit, by simp [residual]⟩
    · rw [emit_err _ _ _ a2]; exact ⟨.ResourceLimit, by simp [residual]⟩
  · rw [emit_err _ _ _ a1]; exact ⟨.ResourceLimit, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual]⟩

end Rowl.RdfXmlTerms
