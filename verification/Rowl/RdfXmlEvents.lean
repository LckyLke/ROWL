import Rowl.RdfXmlTerms

/-!
# Element and attribute events

Correctness of the functions of `rdfxml.rs` that turn an element into its
element event: reserved names, attribute URIs, the base IRI and language, the
classification of URIs and the attribute sets of the productions.
-/

namespace Rowl.RdfXmlEvents
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar Rowl.RdfXmlGrammar Rowl.RdfXmlSpell Rowl.RdfXmlTerms
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-! ## ASCII names -/

theorem lit_ID : ([73#u8, 68#u8] : List U8).map (·.val) = lit "ID" := by decide
theorem lit_nodeID : ([110#u8, 111#u8, 100#u8, 101#u8, 73#u8, 68#u8] : List U8).map (·.val) = lit "nodeID" := by decide
theorem lit_about : ([97#u8, 98#u8, 111#u8, 117#u8, 116#u8] : List U8).map (·.val) = lit "about" := by decide
theorem lit_resource : ([114#u8, 101#u8, 115#u8, 111#u8, 117#u8, 114#u8, 99#u8, 101#u8] : List U8).map (·.val) = lit "resource" := by decide
theorem lit_parseType : ([112#u8, 97#u8, 114#u8, 115#u8, 101#u8, 84#u8, 121#u8, 112#u8, 101#u8] : List U8).map (·.val) = lit "parseType" := by decide
theorem lit_datatype : ([100#u8, 97#u8, 116#u8, 97#u8, 116#u8, 121#u8, 112#u8, 101#u8] : List U8).map (·.val) = lit "datatype" := by decide
theorem lit_RDF : ([82#u8, 68#u8, 70#u8] : List U8).map (·.val) = lit "RDF" := by decide
theorem lit_Description : ([68#u8, 101#u8, 115#u8, 99#u8, 114#u8, 105#u8, 112#u8, 116#u8, 105#u8, 111#u8, 110#u8] : List U8).map (·.val) = lit "Description" := by decide
theorem lit_li : ([108#u8, 105#u8] : List U8).map (·.val) = lit "li" := by decide
theorem lit_aboutEach : ([97#u8, 98#u8, 111#u8, 117#u8, 116#u8, 69#u8, 97#u8, 99#u8, 104#u8] : List U8).map (·.val) = lit "aboutEach" := by decide
theorem lit_aboutEachPrefix : ([97#u8, 98#u8, 111#u8, 117#u8, 116#u8, 69#u8, 97#u8, 99#u8, 104#u8, 80#u8, 114#u8, 101#u8, 102#u8, 105#u8, 120#u8] : List U8).map (·.val) = lit "aboutEachPrefix" := by decide
theorem lit_bagID : ([98#u8, 97#u8, 103#u8, 73#u8, 68#u8] : List U8).map (·.val) = lit "bagID" := by decide
theorem lit_type : ([116#u8, 121#u8, 112#u8, 101#u8] : List U8).map (·.val) = lit "type" := by decide
theorem lit_underscore : ([95#u8] : List U8).map (·.val) = lit "_" := by decide
theorem lit_Resource : ([82#u8, 101#u8, 115#u8, 111#u8, 117#u8, 114#u8, 99#u8, 101#u8] : List U8).map (·.val) = lit "Resource" := by decide
theorem lit_Collection : ([67#u8, 111#u8, 108#u8, 108#u8, 101#u8, 99#u8, 116#u8, 105#u8, 111#u8, 110#u8] : List U8).map (·.val) = lit "Collection" := by decide
theorem lit_base : ([98#u8, 97#u8, 115#u8, 101#u8] : List U8).map (·.val) = lit "base" := by decide
theorem lit_lang : ([108#u8, 97#u8, 110#u8, 103#u8] : List U8).map (·.val) = lit "lang" := by decide

theorem is_rdf_lit (uri : alloc.vec.Vec U32) (n : Usize) (l : List U8) (h : l.length = n.val)
    (small : l.length ≤ 1000) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make n l h)) = .ok (decide (word uri = rdfNs ++ l.map (·.val))) := by
  rw [is_rdf_eq uri _ (by rw [slice_val]; exact small), slice_val]

theorem is_ascii_lit (w : alloc.vec.Vec U32) (n : Usize) (l : List U8) (h : l.length = n.val) :
    rdfxml.is_ascii w (Array.to_slice (Array.make n l h)) = .ok (decide (word w = l.map (·.val))) := by
  rw [is_ascii_eq, slice_val]

/-! ## RDF names -/

theorem is_rdf_ID (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 2#usize [73#u8, 68#u8])) =
      .ok (decide (word uri = rdfName "ID")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_ID]; rfl

theorem is_rdf_nodeID (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 6#usize [110#u8, 111#u8, 100#u8, 101#u8, 73#u8, 68#u8])) =
      .ok (decide (word uri = rdfName "nodeID")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_nodeID]; rfl

theorem is_rdf_about (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 5#usize [97#u8, 98#u8, 111#u8, 117#u8, 116#u8])) =
      .ok (decide (word uri = rdfName "about")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_about]; rfl

theorem is_rdf_resource (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 8#usize [114#u8, 101#u8, 115#u8, 111#u8, 117#u8, 114#u8, 99#u8, 101#u8])) =
      .ok (decide (word uri = rdfName "resource")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_resource]; rfl

theorem is_rdf_parseType (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 9#usize [112#u8, 97#u8, 114#u8, 115#u8, 101#u8, 84#u8, 121#u8, 112#u8, 101#u8])) =
      .ok (decide (word uri = rdfName "parseType")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_parseType]; rfl

theorem is_rdf_datatype (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 8#usize [100#u8, 97#u8, 116#u8, 97#u8, 116#u8, 121#u8, 112#u8, 101#u8])) =
      .ok (decide (word uri = rdfName "datatype")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_datatype]; rfl

theorem is_rdf_RDF (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 3#usize [82#u8, 68#u8, 70#u8])) =
      .ok (decide (word uri = rdfName "RDF")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_RDF]; rfl

theorem is_rdf_Description (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 11#usize [68#u8, 101#u8, 115#u8, 99#u8, 114#u8, 105#u8, 112#u8, 116#u8, 105#u8, 111#u8, 110#u8])) =
      .ok (decide (word uri = rdfName "Description")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_Description]; rfl

theorem is_rdf_li (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 2#usize [108#u8, 105#u8])) =
      .ok (decide (word uri = rdfName "li")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_li]; rfl

theorem is_rdf_aboutEach (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 9#usize [97#u8, 98#u8, 111#u8, 117#u8, 116#u8, 69#u8, 97#u8, 99#u8, 104#u8])) =
      .ok (decide (word uri = rdfName "aboutEach")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_aboutEach]; rfl

theorem is_rdf_aboutEachPrefix (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 15#usize [97#u8, 98#u8, 111#u8, 117#u8, 116#u8, 69#u8, 97#u8, 99#u8, 104#u8, 80#u8, 114#u8, 101#u8, 102#u8, 105#u8, 120#u8])) =
      .ok (decide (word uri = rdfName "aboutEachPrefix")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_aboutEachPrefix]; rfl

theorem is_rdf_bagID (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 5#usize [98#u8, 97#u8, 103#u8, 73#u8, 68#u8])) =
      .ok (decide (word uri = rdfName "bagID")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_bagID]; rfl

theorem is_rdf_type (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 4#usize [116#u8, 121#u8, 112#u8, 101#u8])) =
      .ok (decide (word uri = rdfName "type")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_type]; rfl

theorem is_rdf_underscore (uri : alloc.vec.Vec U32) :
    rdfxml.is_rdf uri (Array.to_slice (Array.make 1#usize [95#u8])) =
      .ok (decide (word uri = rdfName "_")) := by
  rw [is_rdf_lit uri _ _ _ (by decide), lit_underscore]; rfl

/-! ## Classes of URIs -/

/-- The class of an attribute URI as `class_of` numbers it: 0 a property
    attribute, 1 rdf:ID, 2 rdf:nodeID, 3 rdf:about, 4 rdf:resource,
    5 rdf:parseType, 6 rdf:datatype, 7 another syntax or old term. -/
def classOf (u : Word) : Nat :=
  if u = rdfName "ID" then 1 else if u = rdfName "nodeID" then 2 else if u = rdfName "about" then 3
  else if u = rdfName "resource" then 4 else if u = rdfName "parseType" then 5
  else if u = rdfName "datatype" then 6
  else if u = rdfName "RDF" ∨ u = rdfName "Description" ∨ u = rdfName "li" ∨ u ∈ oldTerms then 7 else 0

theorem old_term_eq (uri : alloc.vec.Vec U32) :
    rdfxml.old_term uri = .ok (decide (word uri ∈ oldTerms)) := by
  unfold rdfxml.old_term
  simp only [lift, bind_ok, is_rdf_aboutEach, is_rdf_aboutEachPrefix, is_rdf_bagID]
  have old : word uri ∈ oldTerms ↔ word uri = rdfName "aboutEach" ∨ word uri = rdfName "aboutEachPrefix" ∨
      word uri = rdfName "bagID" := by simp [oldTerms]
  by_cases a : word uri = rdfName "aboutEach"
  · rw [if_pos (decide_eq_true a), decide_eq_true (old.mpr (.inl a))]
  rw [if_neg (by simpa using a)]
  by_cases b : word uri = rdfName "aboutEachPrefix"
  · rw [if_pos (decide_eq_true b), decide_eq_true (old.mpr (.inr (.inl b)))]
  rw [if_neg (by simpa using b)]
  by_cases d : word uri = rdfName "bagID"
  · rw [decide_eq_true d, decide_eq_true (old.mpr (.inr (.inr d)))]
  · rw [decide_eq_false d, decide_eq_false (by rw [old]; tauto)]

theorem other_syntax_eq (uri : alloc.vec.Vec U32) :
    rdfxml.other_syntax uri = .ok (decide (word uri = rdfName "RDF" ∨ word uri = rdfName "Description" ∨
      word uri = rdfName "li" ∨ word uri ∈ oldTerms)) := by
  unfold rdfxml.other_syntax
  simp only [lift, bind_ok, is_rdf_RDF, is_rdf_Description, is_rdf_li, old_term_eq]
  by_cases a : word uri = rdfName "RDF"
  · rw [if_pos (decide_eq_true a), decide_eq_true (.inl a)]
  rw [if_neg (by simpa using a)]
  by_cases b : word uri = rdfName "Description"
  · rw [if_pos (decide_eq_true b), decide_eq_true (.inr (.inl b))]
  rw [if_neg (by simpa using b)]
  by_cases d : word uri = rdfName "li"
  · rw [if_pos (decide_eq_true d), decide_eq_true (.inr (.inr (.inl d)))]
  rw [if_neg (by simpa using d)]
  by_cases o : word uri ∈ oldTerms
  · rw [decide_eq_true o, decide_eq_true (.inr (.inr (.inr o)))]
  · rw [decide_eq_false o, decide_eq_false (by tauto)]

theorem class_of_eq (uri : alloc.vec.Vec U32) :
    ∃ k, rdfxml.class_of uri = .ok k ∧ k.val = classOf (word uri) := by
  unfold rdfxml.class_of
  simp only [lift, bind_ok, is_rdf_ID, is_rdf_nodeID, is_rdf_about, is_rdf_resource, is_rdf_parseType,
    is_rdf_datatype, other_syntax_eq]
  unfold classOf
  by_cases h1 : word uri = rdfName "ID"
  · rw [if_pos (decide_eq_true h1), if_pos h1]; exact ⟨_, rfl, rfl⟩
  rw [if_neg (by simpa using h1), if_neg h1]
  by_cases h2 : word uri = rdfName "nodeID"
  · rw [if_pos (decide_eq_true h2), if_pos h2]; exact ⟨_, rfl, rfl⟩
  rw [if_neg (by simpa using h2), if_neg h2]
  by_cases h3 : word uri = rdfName "about"
  · rw [if_pos (decide_eq_true h3), if_pos h3]; exact ⟨_, rfl, rfl⟩
  rw [if_neg (by simpa using h3), if_neg h3]
  by_cases h4 : word uri = rdfName "resource"
  · rw [if_pos (decide_eq_true h4), if_pos h4]; exact ⟨_, rfl, rfl⟩
  rw [if_neg (by simpa using h4), if_neg h4]
  by_cases h5 : word uri = rdfName "parseType"
  · rw [if_pos (decide_eq_true h5), if_pos h5]; exact ⟨_, rfl, rfl⟩
  rw [if_neg (by simpa using h5), if_neg h5]
  by_cases h6 : word uri = rdfName "datatype"
  · rw [if_pos (decide_eq_true h6), if_pos h6]; exact ⟨_, rfl, rfl⟩
  rw [if_neg (by simpa using h6), if_neg h6]
  by_cases h7 : word uri = rdfName "RDF" ∨ word uri = rdfName "Description" ∨ word uri = rdfName "li" ∨
      word uri ∈ oldTerms
  · rw [if_pos (decide_eq_true h7), if_pos h7]; exact ⟨_, rfl, rfl⟩
  · rw [if_neg (by simpa using h7), if_neg h7]; exact ⟨_, rfl, rfl⟩

theorem core_mem (u : Word) : u ∈ coreSyntaxTerms ↔ u = rdfName "RDF" ∨ u = rdfName "ID" ∨ u = rdfName "about" ∨
    u = rdfName "parseType" ∨ u = rdfName "resource" ∨ u = rdfName "nodeID" ∨ u = rdfName "datatype" := by
  simp [coreSyntaxTerms]

theorem old_mem (u : Word) : u ∈ oldTerms ↔ u = rdfName "aboutEach" ∨ u = rdfName "aboutEachPrefix" ∨
    u = rdfName "bagID" := by
  simp [oldTerms]

theorem classOf_zero (u : Word) : classOf u = 0 ↔ PropertyAttributeUri u := by
  unfold classOf PropertyAttributeUri
  simp only [core_mem, old_mem]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · simp [h1]
  · simp [h2]
  · simp [h3]
  · simp [h4]
  · simp [h5]
  · simp [h6]
  · simp only [OfNat.ofNat_ne_zero, false_iff, not_and, not_not]
    intro _ _ _; rcases h7 with h | h | h | h <;> simp_all
  · simp only [true_iff]
    refine ⟨?_, fun h => h7 (.inr (.inl h)), fun h => h7 (.inr (.inr (.inl h))), fun h => h7 (.inr (.inr (.inr h)))⟩
    rintro (h | h | h | h | h | h | h)
    · exact h7 (.inl h)
    · exact h1 h
    · exact h3 h
    · exact h5 h
    · exact h4 h
    · exact h2 h
    · exact h6 h

theorem classOf_val (u : Word) : classOf u = 1 ∨ classOf u = 2 ∨ classOf u = 3 ∨ classOf u = 4 ∨
    classOf u = 5 ∨ classOf u = 6 ∨ classOf u = 7 ∨ classOf u = 0 := by
  unfold classOf; split_ifs <;> simp


/-! ## Reserved names and attribute URIs -/

theorem letters_xml_eq (a b d : U32) :
    rdfxml.letters_xml a b d = .ok (decide ((a.val = 120 ∨ a.val = 88) ∧ (b.val = 109 ∨ b.val = 77) ∧
      (d.val = 108 ∨ d.val = 76))) := by
  unfold rdfxml.letters_xml
  by_cases a1 : a.val = 120 <;> by_cases a2 : a.val = 88 <;> by_cases b1 : b.val = 109 <;>
    by_cases b2 : b.val = 77 <;> by_cases d1 : d.val = 108 <;> by_cases d2 : d.val = 76 <;>
    simp [UScalar.eq_equiv, a1, a2, b1, b2, d1, d2]

theorem xmlLetters_cons (x y z : Nat) (r : Word) :
    XmlLetters (x :: y :: z :: r) ↔ (x = 120 ∨ x = 88) ∧ (y = 109 ∨ y = 77) ∧ (z = 108 ∨ z = 76) := by
  simp only [XmlLetters, List.cons.injEq]
  constructor
  · rintro ⟨a, b, d, rest, ⟨rfl, rfl, rfl, -⟩, h⟩; exact h
  · intro h; exact ⟨_, _, _, _, ⟨rfl, rfl, rfl, rfl⟩, h⟩

theorem three_cons {α : Type} (l : List α) (h : 3 ≤ l.length) : ∃ a b d rest, l = a :: b :: d :: rest := by
  match l, h with
  | a :: b :: d :: rest, _ => exact ⟨a, b, d, rest, rfl⟩

theorem xml_letters_eq (w : alloc.vec.Vec U32) : rdfxml.xml_letters w = .ok (decide (XmlLetters (word w))) := by
  unfold rdfxml.xml_letters
  by_cases three : 3 ≤ w.val.length
  · obtain ⟨a, b, d, rest, hl⟩ := three_cons w.val three
    have t' : (3#usize) ≤ alloc.vec.Vec.len w := by rw [UScalar.le_equiv]; simpa using three
    have i0 : (0#usize).val < w.val.length := by simp [hl]
    have i1 : (1#usize).val < w.val.length := by simp [hl]
    have i2 : (2#usize).val < w.val.length := by simp [hl]
    simp only [t', ite_true, index_eq w _ i0, index_eq w _ i1, index_eq w _ i2, bind_ok]
    have g0 : w.val[(0#usize).val]'i0 = a := by simp [hl]
    have g1 : w.val[(1#usize).val]'i1 = b := by simp [hl]
    have g2 : w.val[(2#usize).val]'i2 = d := by simp [hl]
    rw [g0, g1, g2, letters_xml_eq]
    have ww : word w = a.val :: b.val :: d.val :: rest.map (·.val) := by simp [word, hl]
    rw [ww]
    congr 1
    exact decide_eq_decide.mpr (xmlLetters_cons _ _ _ _).symm
  · have t' : ¬ (3#usize) ≤ alloc.vec.Vec.len w := by rw [UScalar.le_equiv]; simpa using three
    simp only [t', ite_false]
    congr 1
    rw [eq_comm, decide_eq_false_iff_not]
    simp only [XmlLetters, not_exists, not_and]
    intro a' b' d' rest' e
    have := congrArg List.length e
    simp [word] at this; omega

theorem reserved_eq (a : xml.Attribute) : rdfxml.reserved a = .ok (decide (Reserved a)) := by
  unfold rdfxml.reserved Reserved
  cases a.ns_prefix <;> simp [xml_letters_eq]

theorem lit_type_ascii : ([116#u8, 121#u8, 112#u8, 101#u8] : List U8).map (·.val) = lit "type" := by decide

theorem unqualified_eq (l : alloc.vec.Vec U32) :
    rdfxml.unqualified l = .ok (decide (word l ∈ unqualifiedNames)) := by
  unfold rdfxml.unqualified
  simp only [lift, bind_ok, is_ascii_lit, lit_ID, lit_about, lit_resource, lit_parseType, lit_type]
  have m : word l ∈ unqualifiedNames ↔ word l = lit "ID" ∨ word l = lit "about" ∨ word l = lit "resource" ∨
      word l = lit "parseType" ∨ word l = lit "type" := by simp [unqualifiedNames]
  by_cases a : word l = lit "ID"
  · rw [if_pos (decide_eq_true a), decide_eq_true (m.mpr (.inl a))]
  rw [if_neg (by simpa using a)]
  by_cases b : word l = lit "about"
  · rw [if_pos (decide_eq_true b), decide_eq_true (m.mpr (.inr (.inl b)))]
  rw [if_neg (by simpa using b)]
  by_cases d : word l = lit "resource"
  · rw [if_pos (decide_eq_true d), decide_eq_true (m.mpr (.inr (.inr (.inl d))))]
  rw [if_neg (by simpa using d)]
  by_cases f : word l = lit "parseType"
  · rw [if_pos (decide_eq_true f), decide_eq_true (m.mpr (.inr (.inr (.inr (.inl f)))))]
  rw [if_neg (by simpa using f)]
  by_cases g : word l = lit "type"
  · rw [decide_eq_true g, decide_eq_true (m.mpr (.inr (.inr (.inr (.inr g)))))]
  · rw [decide_eq_false g, decide_eq_false (by rw [m]; tauto)]

theorem named_uri_eq (ns l : alloc.vec.Vec U32) (limits : rdfxml.Limits) :
    ∃ r, rdfxml.named_uri ns l limits = .ok r ∧ ∀ u, r = .Ok u ↔
      (NamespaceAllowed (word ns) ∧ (word ns ++ word l).length ≤ limits.term_bytes.val ∧
        word u = word ns ++ word l) := by
  unfold rdfxml.named_uri
  rw [rdf_extension_eq]
  by_cases ext : rdfNs <+: word ns ∧ word ns ≠ rdfNs
  · refine ⟨.Err .InvalidName, by simp [ext], fun u => ?_⟩
    simp [NamespaceAllowed, ext]
  · simp only [decide_eq_false ext, bind_ok, Bool.false_eq_true, ite_false]
    obtain ⟨r, hr, hc⟩ := concat_eq ns l limits.term_bytes
    refine ⟨r, hr, fun u => ?_⟩
    rw [hc u]
    simp [NamespaceAllowed, ext]

theorem attrUri_iff (limit : Nat) (a : xml.Attribute) (u : Word) :
    AttrUri limit a u ↔ (∃ ns : alloc.vec.Vec U32, a.ns_name = some ns ∧ NamespaceAllowed (word ns) ∧
        (word ns ++ word a.local_name).length ≤ limit ∧ u = word ns ++ word a.local_name) ∨
      (a.ns_name = none ∧ word a.local_name ∈ unqualifiedNames ∧ (rdfNs ++ word a.local_name).length ≤ limit ∧
        u = rdfNs ++ word a.local_name) := by
  constructor
  · intro h; cases h with
    | qualified e na l => exact .inl ⟨_, e, na, l, rfl⟩
    | unqualified e m l => exact .inr ⟨e, m, l, rfl⟩
  · rintro (⟨ns, e, na, l, rfl⟩ | ⟨e, m, l, rfl⟩)
    · exact .qualified e na l
    · exact .unqualified e m l

/-- 43 ASCII bytes of the RDF namespace name as a slice. -/
theorem rdf_ascii_word (l : List U8) (h : l.length = (43#usize).val) (e : l = rdfNsBytes) :
    ∃ v, rdfxml.ascii_word (Array.to_slice (Array.make 43#usize l h)) = .ok v ∧ word v = rdfNs := by
  obtain ⟨v, hv, hw⟩ := ascii_word_eq (Array.to_slice (Array.make 43#usize l h))
  exact ⟨v, hv, by rw [hw, slice_val, e, rdfNsBytes_val]⟩

theorem concat_complete (a b : alloc.vec.Vec U32) (limit : Usize) (l : (word a ++ word b).length ≤ limit.val) :
    ∃ v, rdfxml.concat a b limit = .ok (.Ok v) ∧ word v = word a ++ word b := by
  obtain ⟨r, hr, hc⟩ := concat_eq a b limit
  have lim := Rowl.XmlScan.usize_le_max limit
  have bound : (a.val ++ b.val).length ≤ Usize.max := by simp [word] at l ⊢; omega
  have w : word (alloc.vec.Vec.from (a.val ++ b.val) bound) = word a ++ word b := by simp [word]
  have := (hc _).mpr ⟨l, w⟩
  exact ⟨_, by rw [hr, this], w⟩

theorem attribute_uri_spec (a : xml.Attribute) (limits : rdfxml.Limits) :
    ∃ r, rdfxml.attribute_uri a limits = .ok r ∧
      (∀ u, r = .Ok u → AttrUri limits.term_bytes.val a (word u)) ∧
      (∀ u, AttrUri limits.term_bytes.val a u → ∃ v, r = .Ok v ∧ word v = u) := by
  unfold rdfxml.attribute_uri
  cases hns : a.ns_name with
  | some ns =>
    simp only
    unfold rdfxml.named_uri
    rw [rdf_extension_eq]
    by_cases ext : rdfNs <+: word ns ∧ word ns ≠ rdfNs
    · refine ⟨.Err .InvalidName, by simp [ext], by simp, fun u h => ?_⟩
      rw [attrUri_iff] at h
      rcases h with ⟨ns', e, na, -⟩ | ⟨e, -⟩
      · rw [hns] at e; cases e; exact absurd ext na
      · rw [hns] at e; cases e
    · simp only [decide_eq_false ext, bind_ok, Bool.false_eq_true, ite_false]
      obtain ⟨r, hr, hc⟩ := concat_eq ns a.local_name limits.term_bytes
      refine ⟨r, hr, fun u e => ?_, fun u h => ?_⟩
      · obtain ⟨l, w⟩ := (hc u).mp e
        exact (attrUri_iff _ _ _).mpr (.inl ⟨ns, hns, ext, l, w⟩)
      · rw [attrUri_iff] at h
        rcases h with ⟨ns', e, na, l, rfl⟩ | ⟨e, -⟩
        · rw [hns] at e; cases e
          obtain ⟨v, hv, w⟩ := concat_complete ns a.local_name limits.term_bytes l
          rw [hr] at hv
          have e := Result.ok_injective hv; subst e
          exact ⟨v, rfl, w⟩
        · rw [hns] at e; cases e
  | none =>
    simp only [unqualified_eq]
    by_cases m : word a.local_name ∈ unqualifiedNames
    · simp only [m, decide_true, ite_true, lift, bind_ok]
      generalize hs : Array.to_slice (Array.make 43#usize _ _) = sl
      have sv : sl.val.map (·.val) = rdfNs := by rw [← hs]; exact rdf_slice _ _ rfl
      obtain ⟨v0, hv0, hw0⟩ := ascii_word_eq sl
      have hw : word v0 = rdfNs := hw0.trans sv
      rw [hv0]; simp only [bind_ok]
      obtain ⟨r, hr, hc⟩ := concat_eq v0 a.local_name limits.term_bytes
      refine ⟨r, hr, fun u e => ?_, fun u h => ?_⟩
      · obtain ⟨l, w⟩ := (hc u).mp e
        rw [hw] at l w
        exact (attrUri_iff _ _ _).mpr (.inr ⟨hns, m, l, w⟩)
      · rw [attrUri_iff] at h
        rcases h with ⟨ns', e, -⟩ | ⟨-, -, l, rfl⟩
        · rw [hns] at e; cases e
        · rw [← hw] at l
          obtain ⟨v, hv, w⟩ := concat_complete v0 a.local_name limits.term_bytes l
          rw [hr] at hv
          have e := Result.ok_injective hv; subst e
          exact ⟨v, rfl, by rw [w, hw]⟩
    · refine ⟨.Err .UnqualifiedAttribute, by simp [m], by simp, fun u h => ?_⟩
      rw [attrUri_iff] at h
      rcases h with ⟨ns', e, -⟩ | ⟨-, m', -⟩
      · rw [hns] at e; cases e
      · exact absurd m' m

theorem elementUri_iff (limit : Nat) (e : xml.Element) (u : Word) :
    ElementUri limit e u ↔ ∃ ns : alloc.vec.Vec U32, e.ns_name = some ns ∧ NamespaceAllowed (word ns) ∧
      (word ns ++ word e.local_name).length ≤ limit ∧ u = word ns ++ word e.local_name := by
  constructor
  · intro h; cases h with
    | mk e1 na l => exact ⟨_, e1, na, l, rfl⟩
  · rintro ⟨ns, e1, na, l, rfl⟩; exact .mk e1 na l

theorem element_uri_eq (e : xml.Element) (limits : rdfxml.Limits) :
    ∃ r, rdfxml.element_uri e limits = .ok r ∧ ∀ u, r = .Ok u ↔ ElementUri limits.term_bytes.val e (word u) := by
  unfold rdfxml.element_uri
  cases hns : e.ns_name with
  | some ns =>
    simp only
    obtain ⟨r, hr, hc⟩ := named_uri_eq ns e.local_name limits
    refine ⟨r, hr, fun u => ?_⟩
    rw [hc u, elementUri_iff]
    simp only [hns, Option.some.injEq]
    constructor
    · rintro ⟨na, l, w⟩; exact ⟨ns, rfl, na, l, w⟩
    · rintro ⟨ns', rfl, na, l, w⟩; exact ⟨na, l, w⟩
  | none =>
    refine ⟨.Err .InvalidName, by simp, fun u => ?_⟩
    rw [elementUri_iff]
    simp [hns]

/-! ## Attribute events -/

theorem attrUri_unique {limit : Nat} {a : xml.Attribute} {u1 u2 : Word} (h1 : AttrUri limit a u1)
    (h2 : AttrUri limit a u2) : u1 = u2 := by
  cases h1 with
  | qualified e1 _ _ =>
    cases h2 with
    | qualified e2 _ _ => rw [e1] at e2; cases e2; rfl
    | unqualified e2 _ _ => rw [e1] at e2; cases e2
  | unqualified e1 _ _ =>
    cases h2 with
    | qualified e2 _ _ => rw [e1] at e2; cases e2
    | unqualified e2 _ _ => rfl

/-- An attribute event by its URI and string value. -/
def eventView (e : rdfxml.Event) : Word × Word := (word e.uri, word e.value)

/-- The attribute events of a vector. -/
def evsOf (v : alloc.vec.Vec rdfxml.Event) : List (Word × Word) := v.val.map eventView

theorem events_inv (limit : Nat) (a : xml.Attribute) (rest : List xml.Attribute) (evs : List (Word × Word))
    (h : Events limit (a :: rest) evs) :
    (Reserved a ∧ Events limit rest evs) ∨
      (¬ Reserved a ∧ ∃ u tail, AttrUri limit a u ∧ Events limit rest tail ∧ evs = (u, word a.value) :: tail) := by
  cases h with
  | reserved r e => exact .inl ⟨r, e⟩
  | event nr au e => exact .inr ⟨nr, _, _, au, e, rfl⟩

theorem events_from_eq (attrs : alloc.vec.Vec xml.Attribute) (i : Usize) (out : alloc.vec.Vec rdfxml.Event)
    (limits : rdfxml.Limits) (room : out.val.length ≤ i.val) :
    ∃ r, rdfxml.events_from attrs i out limits = .ok r ∧
      (∀ evs, r = .Ok evs → ∃ tail, Events limits.term_bytes.val (attrs.val.drop i.val) tail ∧
        evsOf evs = evsOf out ++ tail) ∧
      (∀ tail, Events limits.term_bytes.val (attrs.val.drop i.val) tail →
        ∃ evs, r = .Ok evs ∧ evsOf evs = evsOf out ++ tail) := by
  rw [rdfxml.events_from]
  by_cases lt : i.val < attrs.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len attrs) (by simpa using lt)
    have da : attrs.val.drop i.val = attrs.val[i.val] :: attrs.val.drop i1.val := by
      rw [hi1v, List.drop_eq_getElem_cons lt]
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq attrs i lt, reserved_eq]
    rw [da]
    by_cases res : Reserved attrs.val[i.val]
    · simp only [res, decide_true, ite_true, hi1, bind_ok]
      obtain ⟨r, hr, sound, complete⟩ := events_from_eq attrs i1 out limits (by omega)
      refine ⟨r, hr, fun evs e => ?_, fun tail h => ?_⟩
      · obtain ⟨tail, ht, he⟩ := sound evs e
        exact ⟨tail, .reserved res ht, he⟩
      · rcases events_inv _ _ _ _ h with ⟨_, h'⟩ | ⟨nr, -⟩
        · exact complete tail h'
        · exact absurd res nr
    · simp only [res, decide_false, Bool.false_eq_true, ite_false]
      obtain ⟨ru, hru, soundu, completeu⟩ := attribute_uri_spec attrs.val[i.val] limits
      rw [hru]; simp only [bind_ok]
      cases ru with
      | Err e =>
        refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
        intro tail h
        rcases events_inv _ _ _ _ h with ⟨r', -⟩ | ⟨-, u, tl, au, -, -⟩
        · exact absurd r' res
        · obtain ⟨v, hv, -⟩ := completeu u au
          cases hv
      | Ok u =>
        have au := soundu u rfl
        have room2 : out.val.length < Usize.max := by
          have := attrs.property; omega
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, copy_word_eq,
          push_eq out _ room2, hi1]
        obtain ⟨r, hr, sound, complete⟩ := events_from_eq attrs i1
          (alloc.vec.Vec.from (out.val ++ [⟨u, attrs.val[i.val].value⟩]) (by simp; omega)) limits (by simp; omega)
        refine ⟨r, hr, fun evs e => ?_, fun tail h => ?_⟩
        · obtain ⟨tail, ht, he⟩ := sound evs e
          refine ⟨(word u, word attrs.val[i.val].value) :: tail, .event res au ht, ?_⟩
          rw [he]; simp [evsOf, eventView]
        · rcases events_inv _ _ _ _ h with ⟨r', -⟩ | ⟨-, u', tl, au', ht, rfl⟩
          · exact absurd r' res
          · rw [attrUri_unique au' au]
            obtain ⟨evs, he, hv⟩ := complete tl ht
            refine ⟨evs, he, ?_⟩
            rw [hv]; simp [evsOf, eventView]
  · have e : attrs.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨.Ok out, by simp [UScalar.lt_equiv, lt], ?_, ?_⟩
    · intro evs h; simp at h; subst h; exact ⟨[], by rw [e]; exact .nil, by simp⟩
    · intro tail h
      rw [e] at h
      cases h
      exact ⟨out, rfl, by simp⟩
termination_by attrs.val.length - i.val
decreasing_by all_goals omega

theorem element_uri_spec (e : xml.Element) (limits : rdfxml.Limits) :
    ∃ r, rdfxml.element_uri e limits = .ok r ∧
      (∀ u, r = .Ok u → ElementUri limits.term_bytes.val e (word u)) ∧
      (∀ u, ElementUri limits.term_bytes.val e u → ∃ v, r = .Ok v ∧ word v = u) := by
  obtain ⟨r, hr, hc⟩ := element_uri_eq e limits
  refine ⟨r, hr, fun u h => (hc u).mp h, fun u h => ?_⟩
  have h' := h
  rw [elementUri_iff] at h'
  obtain ⟨ns, en, na, l, rfl⟩ := h'
  have lim := Rowl.XmlScan.usize_le_max limits.term_bytes
  have bound : (ns.val ++ e.local_name.val).length ≤ Usize.max := by simp [word] at l ⊢; omega
  have w : word (alloc.vec.Vec.from (ns.val ++ e.local_name.val) bound) = word ns ++ word e.local_name := by
    simp [word]
  exact ⟨_, (hc _).mpr (by rw [w]; exact h), w⟩

theorem elementUri_unique {limit : Nat} {e : xml.Element} {u1 u2 : Word} (h1 : ElementUri limit e u1)
    (h2 : ElementUri limit e u2) : u1 = u2 := by
  cases h1 with
  | mk e1 _ _ =>
    cases h2 with
    | mk e2 _ _ => rw [e1] at e2; cases e2; rfl

/-- The URIs of the events. -/
def urisOf (events : alloc.vec.Vec rdfxml.Event) : List Word := (evsOf events).map Prod.fst

theorem uris_drop (events : alloc.vec.Vec rdfxml.Event) (k : Nat) (lt : k < events.val.length) :
    (urisOf events).drop k = word events.val[k].uri :: (urisOf events).drop (k + 1) := by
  have e1 : urisOf events = events.val.map (fun e => word e.uri) := by
    simp [urisOf, evsOf, eventView, List.map_map]
  rw [e1]
  exact (map_drop_cons (fun e : rdfxml.Event => word e.uri) events.val lt).symm

theorem uri_absent_eq (events : alloc.vec.Vec rdfxml.Event) (uri : alloc.vec.Vec U32) (k : Usize) :
    rdfxml.uri_absent events uri k = .ok (decide (word uri ∉ (urisOf events).drop k.val)) := by
  rw [rdfxml.uri_absent]
  by_cases lt : k.val < events.val.length
  · obtain ⟨k1, hk1, hk1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len events) (by simpa using lt)
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq events k lt,
      same_word_eq]
    rw [uris_drop events k.val lt, ← hk1v]
    by_cases same : word events.val[k.val].uri = word uri
    · simp [same]
    · simp only [same, decide_false, Bool.false_eq_true, ite_false, hk1, bind_ok]
      rw [uri_absent_eq events uri k1]
      simp [Ne.symm same]
  · have e : (urisOf events).drop k.val = [] := List.drop_eq_nil_of_le (by simp [urisOf, evsOf]; omega)
    simp [UScalar.lt_equiv, lt, e]
termination_by events.val.length - k.val
decreasing_by omega

theorem distinct_from_eq (events : alloc.vec.Vec rdfxml.Event) (i : Usize) :
    rdfxml.distinct_from events i = .ok (decide (((urisOf events).drop i.val).Nodup)) := by
  rw [rdfxml.distinct_from]
  by_cases lt : i.val < events.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len events) (by simpa using lt)
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq events i lt, hi1,
      uri_absent_eq]
    rw [uris_drop events i.val lt, ← hi1v]
    by_cases fresh : word events.val[i.val].uri ∈ (urisOf events).drop i1.val
    · simp [fresh]
    · simp only [fresh, not_false_eq_true, decide_true, ite_true]
      rw [distinct_from_eq events i1]
      simp [fresh]
  · have e : (urisOf events).drop i.val = [] := List.drop_eq_nil_of_le (by simp [urisOf, evsOf]; omega)
    simp [UScalar.lt_equiv, lt, e]
termination_by events.val.length - i.val
decreasing_by omega

/-! ## The base IRI and the language of an element -/

theorem lit_xmlns : ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 88#u8, 77#u8, 76#u8, 47#u8, 49#u8, 57#u8, 57#u8, 56#u8, 47#u8, 110#u8, 97#u8, 109#u8, 101#u8, 115#u8, 112#u8, 97#u8, 99#u8, 101#u8] : List U8).map (·.val) = xmlNamespace := by decide

theorem xml_named_eq (ns nm : alloc.vec.Vec U32) (l : Slice U8) :
    rdfxml.xml_named ns nm l = .ok (decide (word ns = xmlNamespace ∧ word nm = l.val.map (·.val))) := by
  unfold rdfxml.xml_named
  simp only [lift, bind_ok, is_ascii_lit, lit_xmlns]
  by_cases a : word ns = xmlNamespace
  · simp [a, is_ascii_eq]
  · simp [a]

theorem xml_attribute_eq (a : xml.Attribute) (l : Slice U8) :
    rdfxml.xml_attribute a l = .ok (decide (optWord a.ns_name = some xmlNamespace ∧
      word a.local_name = l.val.map (·.val))) := by
  unfold rdfxml.xml_attribute
  cases h : a.ns_name <;> simp [xml_named_eq, optWord]

theorem find_xml_eq (attrs : alloc.vec.Vec xml.Attribute) (l : Slice U8) (i : Usize) :
    ∃ o, rdfxml.find_xml attrs l i = .ok o ∧
      (o = none → xmlValue (l.val.map (·.val)) (attrs.val.drop i.val) = none) ∧
      (∀ k, o = some k → ∃ h : k.val < attrs.val.length,
        xmlValue (l.val.map (·.val)) (attrs.val.drop i.val) = some (word (attrs.val[k.val]).value)) := by
  rw [rdfxml.find_xml]
  by_cases lt : i.val < attrs.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len attrs) (by simpa using lt)
    have da : attrs.val.drop i.val = attrs.val[i.val] :: attrs.val.drop i1.val := by
      rw [hi1v, List.drop_eq_getElem_cons lt]
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq attrs i lt,
      xml_attribute_eq]
    rw [da]
    by_cases m : optWord attrs.val[i.val].ns_name = some xmlNamespace ∧
        word attrs.val[i.val].local_name = l.val.map (·.val)
    · refine ⟨some i, by simp [m], by simp, fun k e => ?_⟩
      simp at e; subst e
      exact ⟨lt, by simp [xmlValue, m]⟩
    · simp only [m, decide_false, Bool.false_eq_true, ite_false, hi1, bind_ok]
      obtain ⟨o, ho, none_, some_⟩ := find_xml_eq attrs l i1
      refine ⟨o, ho, fun e => ?_, fun k e => ?_⟩
      · rw [xmlValue, if_neg m]; exact none_ e
      · obtain ⟨h, v⟩ := some_ k e
        exact ⟨h, by rw [xmlValue, if_neg m]; exact v⟩
  · have e : attrs.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
    exact ⟨none, by simp [UScalar.lt_equiv, lt], by simp [e, xmlValue], by simp⟩
termination_by attrs.val.length - i.val
decreasing_by omega

theorem baseOf_iff (c : Ctx) (o : Option Word) (b : List U8) :
    BaseOf c o b ↔ (o = none ∧ b = c.base) ∨ ∃ v, o = some v ∧ ResolvedRef c v b := by
  constructor
  · intro h; cases h with
    | inherited => exact .inl ⟨rfl, rfl⟩
    | given r => exact .inr ⟨_, rfl, r⟩
  · rintro (⟨rfl, rfl⟩ | ⟨v, rfl, r⟩)
    · exact .inherited
    · exact .given r

theorem element_base_spec (c : Ctx) (e : xml.Element) (base : alloc.vec.Vec U8) (limits : rdfxml.Limits)
    (hc : c.base = base.val) (ht : c.termLimit = limits.term_bytes.val)
    (hb : base.val.length ≤ limits.term_bytes.val) (small : limits.term_bytes.val < Usize.max / 8) :
    ∃ r, rdfxml.element_base e base limits = .ok r ∧
      (∀ b, r = .Ok b → BaseOf c (xmlValue (lit "base") e.attributes.val) b.val) ∧
      (∀ b, BaseOf c (xmlValue (lit "base") e.attributes.val) b → ∃ v, r = .Ok v ∧ v.val = b) := by
  unfold rdfxml.element_base
  simp only [lift, bind_ok]
  generalize hs : Array.to_slice (Array.make 4#usize _ _) = sl
  have sv : sl.val.map (·.val) = lit "base" := by rw [← hs, slice_val]; decide
  obtain ⟨o, ho, none_, some_⟩ := find_xml_eq e.attributes sl 0#usize
  rw [sv, usize_zero_val, List.drop_zero] at none_ some_
  rw [ho]; simp only [bind_ok]
  cases o with
  | none =>
    have xv := none_ rfl
    refine ⟨.Ok base, by simp [copy_bytes_eq], fun b eb => ?_, fun b h => ?_⟩
    · simp at eb; subst eb; rw [xv, ← hc]; exact .inherited
    · rw [xv, baseOf_iff] at h
      rcases h with ⟨-, rfl⟩ | ⟨v, e1, -⟩
      · exact ⟨base, rfl, hc.symm⟩
      · cases e1
  | some k =>
    obtain ⟨kin, xv⟩ := some_ k rfl
    simp only [index_eq e.attributes k kin, bind_ok]
    obtain ⟨r1, hr1, hc1⟩ := utf8_eq (e.attributes.val[k.val]).value limits
    rw [hr1]; simp only [bind_ok]
    have lim := Rowl.XmlScan.usize_le_max limits.term_bytes
    cases r1 with
    | Err err =>
      refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, fun b h => ?_⟩
      rw [xv, baseOf_iff] at h
      rcases h with ⟨e1, -⟩ | ⟨v, e1, r, sp, -⟩
      · cases e1
      · simp only [Option.some.injEq] at e1; subst e1
        have := (hc1 (alloc.vec.Vec.from r (vec_of_spelled sp (by omega)))).mpr (by rw [← ht]; simpa using sp)
        simp at this
    | Ok ref =>
      have sp := (hc1 ref).mp rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨r2, hr2, hc2⟩ := resolved_bytes_eq base ref limits hb sp.2.2 small
      refine ⟨r2, hr2, fun b eb => ?_, fun b h => ?_⟩
      · rw [xv]
        exact .given ((resolved_ref_iff c base ref _ limits hc ht sp b.val).mpr ((hc2 b).mp eb))
      · rw [xv, baseOf_iff] at h
        rcases h with ⟨e1, -⟩ | ⟨v, e1, rr⟩
        · cases e1
        · simp only [Option.some.injEq] at e1; subst e1
          have bound : b.length ≤ Usize.max := by
            have := ((resolved_ref_iff c base ref _ limits hc ht sp b).mp rr).2.2; omega
          exact ⟨alloc.vec.Vec.from b bound,
            (hc2 _).mpr (by simpa using (resolved_ref_iff c base ref _ limits hc ht sp b).mp rr), by simp⟩

theorem element_lang_eq (e : xml.Element) (lang : alloc.vec.Vec U32) :
    ∃ v, rdfxml.element_lang e lang = .ok v ∧
      word v = (xmlValue (lit "lang") e.attributes.val).getD (word lang) := by
  unfold rdfxml.element_lang
  simp only [lift, bind_ok]
  generalize hs : Array.to_slice (Array.make 4#usize _ _) = sl
  have sv : sl.val.map (·.val) = lit "lang" := by rw [← hs, slice_val]; decide
  obtain ⟨o, ho, none_, some_⟩ := find_xml_eq e.attributes sl 0#usize
  rw [sv, usize_zero_val, List.drop_zero] at none_ some_
  rw [ho]; simp only [bind_ok]
  cases o with
  | none => exact ⟨lang, by simp [copy_word_eq], by rw [none_ rfl]; rfl⟩
  | some k =>
    obtain ⟨kin, xv⟩ := some_ k rfl
    exact ⟨(e.attributes.val[k.val]).value, by simp [index_eq e.attributes k kin, copy_word_eq], by rw [xv]; rfl⟩

/-! ## Element events -/

theorem events_unique {limit : Nat} {attrs : List xml.Attribute} {e1 e2 : List (Word × Word)}
    (h1 : Events limit attrs e1) (h2 : Events limit attrs e2) : e1 = e2 := by
  induction attrs generalizing e1 e2 with
  | nil => cases h1; cases h2; rfl
  | cons a rest ih =>
    rcases events_inv _ _ _ _ h1 with ⟨r1, t1⟩ | ⟨n1, u1, tl1, au1, t1, rfl⟩ <;>
    rcases events_inv _ _ _ _ h2 with ⟨r2, t2⟩ | ⟨n2, u2, tl2, au2, t2, rfl⟩
    · exact ih t1 t2
    · exact absurd r1 n2
    · exact absurd r2 n1
    · rw [attrUri_unique au1 au2, ih t1 t2]

/-- The context of a prepared element event. -/
def prepCtx (c : Ctx) (p : rdfxml.Prepared) : Ctx := { c with base := p.base.val, lang := word p.lang }

theorem scoped_iff (c : Ctx) (e : xml.Element) (c' : Ctx) :
    Scoped c e c' ↔ ∃ b, BaseOf c (xmlValue (lit "base") e.attributes.val) b ∧
      c' = { c with base := b, lang := (xmlValue (lit "lang") e.attributes.val).getD c.lang } := by
  constructor
  · intro h; cases h with
    | mk hb => exact ⟨_, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩; exact .mk hb

theorem baseOf_length {c : Ctx} {o : Option Word} {b : List U8} (h : BaseOf c o b) (hb : c.base.length ≤ c.termLimit) :
    b.length ≤ c.termLimit := by
  cases h with
  | inherited => exact hb
  | given r => obtain ⟨_, _, _, _, l⟩ := r; exact l

theorem prepare_spec (c : Ctx) (e : xml.Element) (base : alloc.vec.Vec U8) (lang : alloc.vec.Vec U32)
    (limits : rdfxml.Limits) (hc : c.base = base.val) (hl : c.lang = word lang)
    (ht : c.termLimit = limits.term_bytes.val)
    (hb : base.val.length ≤ limits.term_bytes.val) (small : limits.term_bytes.val < Usize.max / 8) :
    ∃ r, rdfxml.prepare e base lang limits = .ok r ∧
      (∀ p, r = .Ok p → Prepared c e (prepCtx c p) (evsOf p.events) ∧ p.base.val.length ≤ limits.term_bytes.val) ∧
      (∀ c' evs, Prepared c e c' evs → ∃ p, r = .Ok p ∧ prepCtx c p = c' ∧ evsOf p.events = evs) := by
  unfold rdfxml.prepare
  obtain ⟨r1, hr1, s1, c1⟩ := element_base_spec c e base limits hc ht hb small
  rw [hr1]; simp only [bind_ok]
  cases r1 with
  | Err err =>
    refine ⟨.Err err, by simp [core.result.Result.Insts.CoreOpsTry.branch, residual], by simp, ?_⟩
    rintro c' evs ⟨sc, -⟩
    obtain ⟨b, hb', -⟩ := (scoped_iff _ _ _).mp sc
    obtain ⟨v, hv, -⟩ := c1 b hb'
    cases hv
  | Ok b =>
    have hbase := s1 b rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨r2, hr2, s2, c2⟩ := events_from_eq e.attributes 0#usize (alloc.vec.Vec.new rdfxml.Event) limits
      (by simp)
    rw [hr2]; simp only [bind_ok]
    cases r2 with
    | Err err =>
      refine ⟨.Err err, by simp [residual], by simp, ?_⟩
      rintro c' evs ⟨-, ev, -⟩
      obtain ⟨v, hv, -⟩ := c2 evs (by rw [usize_zero_val, List.drop_zero, ← ht]; exact ev)
      cases hv
    | Ok events =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨tail, ht2, he⟩ := s2 events rfl
      have evs_eq : evsOf events = tail := by simpa [evsOf] using he
      rw [usize_zero_val, List.drop_zero, ← ht] at ht2
      rw [distinct_from_eq, usize_zero_val, List.drop_zero]
      have nd : (urisOf events).Nodup ↔ ((evsOf events).map Prod.fst).Nodup := by rfl
      by_cases dist : (urisOf events).Nodup
      · obtain ⟨lv, hlv, hlw⟩ := element_lang_eq e lang
        simp only [dist, decide_true, ite_true, hlv, bind_ok]
        refine ⟨.Ok ⟨b, lv, events⟩, rfl, fun p ep => ?_, fun c' evs hp => ?_⟩
        · simp at ep; subst ep
          refine ⟨⟨(scoped_iff _ _ _).mpr ⟨b.val, hbase, ?_⟩, by rw [evs_eq]; exact ht2, nd.mp dist⟩, ?_⟩
          · simp only [prepCtx, hlw, hl]
          · have := baseOf_length hbase (by rw [hc, ht]; exact hb); rw [ht] at this; exact this
        · obtain ⟨sc, ev, -⟩ := hp
          obtain ⟨b', hb', rfl⟩ := (scoped_iff _ _ _).mp sc
          obtain ⟨v, hv, hvb⟩ := c1 b' hb'
          simp only [core.result.Result.Ok.injEq] at hv
          subst hv
          obtain ⟨evs2, he2, hev2⟩ := c2 evs (by rw [usize_zero_val, List.drop_zero, ← ht]; exact ev)
          simp only [core.result.Result.Ok.injEq] at he2
          subst he2
          refine ⟨⟨b, lv, events⟩, rfl, ?_, by simpa [evsOf] using hev2⟩
          simp only [prepCtx, hlw, hl, hvb]
      · refine ⟨.Err .DuplicateAttribute, by simp [dist], by simp, ?_⟩
        rintro c' evs ⟨-, ev, ndv⟩
        have : evs = tail := events_unique ev ht2
        exact absurd (nd.mpr (by rw [evs_eq, ← this]; exact ndv)) dist

/-! ## Classes of events -/

theorem classOf_ID (u : Word) : classOf u = 1 ↔ u = rdfName "ID" := by
  unfold classOf
  split_ifs <;> simp_all <;> decide

theorem classOf_nodeID (u : Word) : classOf u = 2 ↔ u = rdfName "nodeID" := by
  unfold classOf
  split_ifs <;> simp_all <;> decide

theorem classOf_about (u : Word) : classOf u = 3 ↔ u = rdfName "about" := by
  unfold classOf
  split_ifs <;> simp_all <;> decide

theorem classOf_resource (u : Word) : classOf u = 4 ↔ u = rdfName "resource" := by
  unfold classOf
  split_ifs <;> simp_all <;> decide

theorem classOf_parseType (u : Word) : classOf u = 5 ↔ u = rdfName "parseType" := by
  unfold classOf
  split_ifs <;> simp_all <;> decide

theorem classOf_datatype (u : Word) : classOf u = 6 ↔ u = rdfName "datatype" := by
  unfold classOf
  split_ifs <;> simp_all <;> decide

theorem lookup_drop (u : Word) (evs : List (Word × Word)) (i : Nat) (lt : i < evs.length) :
    attrValue u (evs.drop i) = if evs[i].1 = u then some evs[i].2 else attrValue u (evs.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons lt, attrValue]

theorem find_class_lookup (events : alloc.vec.Vec rdfxml.Event) (k : U8) (nm : Word)
    (hk : ∀ u, classOf u = k.val ↔ u = nm) (i : Usize) :
    ∃ o, rdfxml.find_class events k i = .ok o ∧
      (o = none → attrValue nm ((evsOf events).drop i.val) = none) ∧
      (∀ j, o = some j → ∃ h : j.val < events.val.length,
        attrValue nm ((evsOf events).drop i.val) = some (word (events.val[j.val]).value)) := by
  rw [rdfxml.find_class]
  by_cases lt : i.val < events.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len events) (by simpa using lt)
    obtain ⟨c, hc, hcv⟩ := class_of_eq (events.val[i.val]).uri
    have lt' : i.val < (evsOf events).length := by simpa [evsOf] using lt
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq events i lt, hc]
    have ev : (evsOf events)[i.val]'lt' = eventView events.val[i.val] := by simp [evsOf]
    rw [lookup_drop nm _ i.val lt', ev]
    by_cases same : c = k
    · subst same
      have : word (events.val[i.val]).uri = nm := (hk _).mp hcv.symm
      refine ⟨some i, by simp, by simp, fun j e => ?_⟩
      simp at e; subst e
      exact ⟨lt, by simp [eventView, this]⟩
    · have ne : ¬ word (events.val[i.val]).uri = nm := fun h =>
        same (UScalar.eq_of_val_eq (by rw [hcv]; exact (hk _).mpr h))
      simp only [same, ite_false, hi1, bind_ok]
      obtain ⟨o, ho, n1, s1⟩ := find_class_lookup events k nm hk i1
      rw [hi1v] at n1 s1
      refine ⟨o, ho, fun e => by simp [eventView, ne, n1 e], fun j e => ?_⟩
      obtain ⟨h, v⟩ := s1 j e
      exact ⟨h, by simp [eventView, ne, v]⟩
  · have e : (evsOf events).drop i.val = [] := List.drop_eq_nil_of_le (by simp [evsOf]; omega)
    exact ⟨none, by simp [UScalar.lt_equiv, lt], by simp [e, attrValue], by simp⟩
termination_by events.val.length - i.val
decreasing_by omega

theorem allows_0 (c : U8) : rdfxml.allows 0#u8 c = .ok (decide (c.val = 1)) := by
  have : rdfxml.allows 0#u8 c = .ok (c = 1#u8) := by rfl
  rw [this]; simp [UScalar.eq_equiv]

theorem allows_1 (c : U8) : rdfxml.allows 1#u8 c = .ok (decide (c.val = 1 ∨ c.val = 6)) := by
  have : rdfxml.allows 1#u8 c = (if c = 1#u8 then .ok true else .ok (c = 6#u8)) := by rfl
  rw [this]; by_cases c1 : c.val = 1 <;> simp [UScalar.eq_equiv, c1]

theorem allows_2 (c : U8) : rdfxml.allows 2#u8 c = .ok (decide (c.val = 1 ∨ c.val = 5)) := by
  have : rdfxml.allows 2#u8 c = (if c = 1#u8 then .ok true else .ok (c = 5#u8)) := by rfl
  rw [this]; by_cases c1 : c.val = 1 <;> simp [UScalar.eq_equiv, c1]

theorem allows_3 (c : U8) : rdfxml.allows 3#u8 c = .ok (decide (c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ c.val = 4)) := by
  have : rdfxml.allows 3#u8 c = (if c = 0#u8 then .ok true else if c = 1#u8 then .ok true
      else if c = 2#u8 then .ok true else .ok (c = 4#u8)) := by rfl
  rw [this]
  by_cases c0 : c.val = 0 <;> by_cases c1 : c.val = 1 <;> by_cases c2 : c.val = 2 <;>
    simp [UScalar.eq_equiv, c0, c1, c2]

theorem allows_4 (c : U8) : rdfxml.allows 4#u8 c = .ok (decide (c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ c.val = 3)) := by
  have : rdfxml.allows 4#u8 c = (if c = 0#u8 then .ok true else if c = 1#u8 then .ok true
      else if c = 2#u8 then .ok true else .ok (c = 3#u8)) := by rfl
  rw [this]
  by_cases c0 : c.val = 0 <;> by_cases c1 : c.val = 1 <;> by_cases c2 : c.val = 2 <;>
    simp [UScalar.eq_equiv, c0, c1, c2]

theorem within_eq (events : alloc.vec.Vec rdfxml.Event) (set : U8) (P : Nat → Prop)
    (hP : ∀ c : U8, rdfxml.allows set c = .ok (decide (P c.val))) (i : Usize) :
    rdfxml.within events set i = .ok (decide (∀ ev ∈ (evsOf events).drop i.val, P (classOf ev.1))) := by
  rw [rdfxml.within]
  by_cases lt : i.val < events.val.length
  · obtain ⟨i1, hi1, hi1v⟩ := Rowl.XmlScan.succ_spec (y := alloc.vec.Vec.len events) (by simpa using lt)
    obtain ⟨c, hc, hcv⟩ := class_of_eq (events.val[i.val]).uri
    have lt' : i.val < (evsOf events).length := by simpa [evsOf] using lt
    have d : (evsOf events).drop i.val = eventView events.val[i.val] :: (evsOf events).drop i1.val := by
      rw [hi1v, List.drop_eq_getElem_cons lt']; simp [evsOf]
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, lt, ite_true, bind_ok, index_eq events i lt, hc, hP]
    rw [d]
    by_cases ok : P c.val
    · simp only [ok, decide_true, ite_true, hi1, bind_ok]
      rw [within_eq events set P hP i1]
      simp [eventView, ← hcv, ok]
    · simp [eventView, ← hcv, ok]
  · have e : (evsOf events).drop i.val = [] := List.drop_eq_nil_of_le (by simp [evsOf]; omega)
    simp [UScalar.lt_equiv, lt, e]
termination_by events.val.length - i.val
decreasing_by omega

/-! ## Attribute sets -/

theorem attrValue_none_iff (u : Word) (evs : List (Word × Word)) :
    attrValue u evs = none ↔ ∀ ev ∈ evs, ev.1 ≠ u := by
  induction evs with
  | nil => simp [attrValue]
  | cons ev rest ih =>
    rw [attrValue]
    by_cases h : ev.1 = u
    · simp [h]
    · simp [h, ih]

theorem has_iff (evs : List (Word × Word)) (u : Word) : Has evs u ↔ attrValue u evs ≠ none := by
  rw [ne_eq, attrValue_none_iff]
  simp only [Has, not_forall, not_not]
  constructor
  · rintro ⟨v, hv⟩; exact ⟨(u, v), hv, rfl⟩
  · rintro ⟨⟨a, b⟩, hm, rfl⟩; exact ⟨b, hm⟩

theorem lacks_eq (events : alloc.vec.Vec rdfxml.Event) (k : U8) (nm : Word)
    (hk : ∀ u, classOf u = k.val ↔ u = nm) :
    rdfxml.lacks events k = .ok (decide (¬ Has (evsOf events) nm)) := by
  unfold rdfxml.lacks
  obtain ⟨o, ho, n, sm⟩ := find_class_lookup events k nm hk 0#usize
  rw [usize_zero_val, List.drop_zero] at n sm
  rw [ho]; simp only [bind_ok]
  cases o with
  | none => simp [has_iff, n rfl]
  | some j =>
    obtain ⟨_, v⟩ := sm j rfl
    simp [has_iff, v]

theorem not_both_eq (events : alloc.vec.Vec rdfxml.Event) (a b : U8) (na nb : Word)
    (ha : ∀ u, classOf u = a.val ↔ u = na) (hb : ∀ u, classOf u = b.val ↔ u = nb) :
    rdfxml.not_both events a b = .ok (decide (¬ (Has (evsOf events) na ∧ Has (evsOf events) nb))) := by
  unfold rdfxml.not_both
  obtain ⟨o, ho, n, sm⟩ := find_class_lookup events a na ha 0#usize
  rw [usize_zero_val, List.drop_zero] at n sm
  rw [ho]; simp only [bind_ok]
  cases o with
  | none => simp [has_iff, n rfl]
  | some j =>
    obtain ⟨_, v⟩ := sm j rfl
    rw [lacks_eq events b nb hb]
    simp [has_iff, v]

theorem one_identifier_eq (events : alloc.vec.Vec rdfxml.Event) :
    rdfxml.one_identifier events = .ok (decide (
      ¬ (Has (evsOf events) (rdfName "ID") ∧ Has (evsOf events) (rdfName "nodeID")) ∧
      ¬ (Has (evsOf events) (rdfName "ID") ∧ Has (evsOf events) (rdfName "about")) ∧
      ¬ (Has (evsOf events) (rdfName "nodeID") ∧ Has (evsOf events) (rdfName "about")))) := by
  unfold rdfxml.one_identifier
  rw [not_both_eq events 1#u8 2#u8 _ _ (fun u => by simpa using classOf_ID u)
    (fun u => by simpa using classOf_nodeID u)]
  by_cases a : ¬ (Has (evsOf events) (rdfName "ID") ∧ Has (evsOf events) (rdfName "nodeID"))
  · simp only [a, decide_true, ite_true, bind_ok]
    rw [not_both_eq events 1#u8 3#u8 _ _ (fun u => by simpa using classOf_ID u)
      (fun u => by simpa using classOf_about u)]
    by_cases b : ¬ (Has (evsOf events) (rdfName "ID") ∧ Has (evsOf events) (rdfName "about"))
    · simp only [b, decide_true, ite_true]
      rw [not_both_eq events 2#u8 3#u8 _ _ (fun u => by simpa using classOf_nodeID u)
        (fun u => by simpa using classOf_about u)]
      simp [a, b]
    · simp only [b, decide_false, Bool.false_eq_true, ite_false]
      simp [b]
  · simp only [a, decide_false, Bool.false_eq_true, ite_false, bind_ok]
    simp [a]

theorem classes_mem (evs : List (Word × Word)) (P : Nat → Prop) (Q : Word → Prop)
    (h : ∀ u, P (classOf u) ↔ Q u) :
    (∀ ev ∈ evs, P (classOf ev.1)) ↔ ∀ ev ∈ evs, Q ev.1 := by
  constructor
  · intro a ev m; exact (h _).mp (a ev m)
  · intro a ev m; exact (h _).mpr (a ev m)

theorem node_attributes_eq (events : alloc.vec.Vec rdfxml.Event) :
    rdfxml.node_attributes events = .ok (decide (NodeAttributes (evsOf events))) := by
  unfold rdfxml.node_attributes
  rw [within_eq events 4#u8 (fun c => c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3)
    (fun c => by rw [allows_4]; exact congrArg _ (decide_eq_decide.mpr Iff.rfl)) 0#usize]
  rw [usize_zero_val, List.drop_zero]
  simp only [bind_ok]
  rw [one_identifier_eq]
  have key := classes_mem (evsOf events) (fun c => c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3)
    (fun u => u = rdfName "ID" ∨ u = rdfName "nodeID" ∨ u = rdfName "about" ∨ PropertyAttributeUri u)
    (fun u => by
      rw [classOf_zero, classOf_ID, classOf_nodeID, classOf_about]
      tauto)
  simp only [decide_eq_true_eq]
  by_cases w : ∀ ev ∈ evsOf events, classOf ev.1 = 0 ∨ classOf ev.1 = 1 ∨ classOf ev.1 = 2 ∨ classOf ev.1 = 3
  · rw [if_pos w]
    congr 1
    apply decide_eq_decide.mpr
    unfold NodeAttributes
    rw [← key]
    exact ⟨fun h => ⟨w, h⟩, fun h => h.2⟩
  · rw [if_neg w]
    congr 1
    symm
    apply decide_eq_false
    unfold NodeAttributes
    rw [← key]
    exact fun h => w h.1

end Rowl.RdfXmlEvents
