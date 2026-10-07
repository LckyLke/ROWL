import Rowl.DataEncoding

/-!
What the encoding of `data_ontology` means. A data range's encoding holds at a
data node exactly when the range holds of a value that the node stands for
(`encode_range_meaning`): the same datatypes in use, a literal individual
exactly for its literal's value, and, when numbers are ordered, each cut's
class exactly at the reals in the cut (`NodeValue`), so that the subtypes of
`xsd:integer` and the range facets hold as their cuts say (`kind_range_meaning`,
`facet_class_meaning`). A class expression's encoding holds at an
element exactly when the expression holds at the element it stands for, under
any correspondence between an OWL interpretation and an interpretation of the
encoding that agrees on the names, relates the elements that are no data nodes
one to one, and agrees on the data restrictions of the expression
(`encode_class_meaning`); and a guarded expression's encoding holds at no data
node without neighbours (`guarded_meaning`).
-/
namespace Rowl.DataMeaning
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DatatypeMap (Normative)
open Rowl.Datatypes (Canonical valueOf typeOf kindOf InKind)
open Rowl.AlcOntology (RoleOf)
open Rowl.DataEncoding
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe u v w x

variable {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}

/-! ### Data ranges -/

/-- A range facet's values among the reals, for a bound. -/
def FacetReal : datatypes.Facet → ℚ → ℝ → Prop
  | .MinInclusive, c, r => (c : ℝ) ≤ r
  | .MaxInclusive, c, r => r ≤ c
  | .MinExclusive, c, r => (c : ℝ) < r
  | .MaxExclusive, c, r => r < c

/-- What the encoding of a data range needs of a data node `d` of `J` that
    stands for a value `x` of `I`: the same datatypes in use, a literal
    individual exactly at the node of its literal's value, and, when numbers
    are ordered, each cut's class exactly at the nodes of numbers in the cut,
    with `num` the reals among the values of `I`. -/
structure NodeValue (context : data_ontology.Context) (I : Interpretation Object Value)
    (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value) (num : ℝ → Value) (d : Object')
    (x : Value) : Prop where
  kinds : ∀ k, Used context.kinds k = true → (J.classes (kindClass k) d ↔ I.datatypes (typeOf k) x)
  values : ∀ (i : Usize) (h : i.val < context.values.val.length),
    J.namedIndividuals (valueIndividual i) = d ↔ x = lit context.values.val[i.val]
  cuts : context.kinds.ordered = true → ∀ (i : Usize) (h : i.val < context.cuts.val.length),
    (J.classes (cutClass i) d ↔ ∃ r, x = num r ∧ Rowl.Regions.InCut context.cuts.val[i.val] r)

/-- What every data range needs of the two interpretations: `rdfs:Literal` and
    `owl:Thing` hold everywhere, each literal with a value is that value, the
    reals `num` are values one to one, every number is the real it writes, the
    numeric datatypes are the reals of their value spaces, and a range facet
    with a numeric bound holds of the reals on its side of the bound. -/
structure RangeFrame (I : Interpretation Object Value) (J : Interpretation Object' Value')
    (lit : datatypes.DataValue → Value) (num : ℝ → Value) : Prop where
  literal : ∀ x, I.datatypes literalDatatype x
  thing : ∀ d, J.classes thing d
  literals : ∀ lt w, datatypes.literal_value lt = .ok (some w) → I.literals lt = lit w
  injective : Function.Injective num
  numbers : ∀ w, Rowl.Datatypes.IsNumber w → lit w = num (Rowl.Datatypes.numValue w)
  numeric : ∀ k, Rowl.Datatypes.IsNumeric k → ∀ x,
    I.datatypes (typeOf k) x ↔ ∃ r, x = num r ∧ Rowl.Datatypes.RealIn k r
  facets : ∀ (f : FacetRestriction) (F : datatypes.Facet) (w : datatypes.DataValue),
    Rowl.Datatypes.facetOf f.facet = some F → datatypes.literal_value f.value = .ok (some w) →
    Rowl.Datatypes.IsNumber w → ∀ x, I.facets f x ↔ ∃ r, x = num r ∧ FacetReal F (Rowl.Datatypes.numValue w) r

/-- What a data range's encoding means: at every data node standing for a
    value, it holds exactly when the range holds of the value. -/
def RangeMeans (context : data_ontology.Context) (range : DataRange) (c : ClassExpression) : Prop :=
  ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
    (I : Interpretation Object Value) (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value)
    (num : ℝ → Value), RangeFrame I J lit num → ∀ d x, NodeValue context I J lit num d x →
      (dataDenote I range x ↔ classDenote J c d)

theorem literal_individual_meaning (context : data_ontology.Context) (lt : Literal) (a : Individual)
    (run : data_ontology.literal_individual context lt = .ok (some a))
    {I : Interpretation Object Value} {J : Interpretation Object' Value'} {lit : datatypes.DataValue → Value}
    {num : ℝ → Value} (frame : RangeFrame I J lit num) {d : Object'} {x : Value}
    (node : NodeValue context I J lit num d x) :
    individual J a = d ↔ I.literals lt = x := by
  obtain ⟨res, run', facts⟩ := literal_individual_correct context lt
  rw [run] at run'
  obtain ⟨w, i, h, valueRun, at_i, rfl⟩ := facts a (Result.ok_injective run'.symm ▸ rfl)
  rw [individual, node.values i h, at_i, frame.literals lt w valueRun]
  exact eq_comm

theorem encode_range_list_meaning (context : data_ontology.Context) (ranges : alloc.vec.Vec DataRange)
    (index : Usize) (out : alloc.vec.Vec ClassExpression)
    (room : out.val.length + (ranges.val.length - index.val) ≤ Usize.max)
    (each : ∀ e ∈ ranges.val, ∃ res, data_ontology.encode_range context e = .ok res ∧
      ∀ c, res = some c → RangeMeans.{u,v,w,x} context e c) :
    ∃ res, data_ontology.encode_range_list context ranges index out = .ok res ∧
      ∀ v, res = some v → v.val.take out.val.length = out.val ∧
        List.Forall₂ (fun c e => RangeMeans.{u,v,w,x} context e c) (v.val.drop out.val.length) (ranges.val.drop index.val) := by
  rw [data_ontology.encode_range_list]
  by_cases inside : index.val < ranges.val.length
  · have lookup : ranges.index_usize index = .ok ranges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨res, run, means⟩ := each _ (List.getElem_mem inside)
    cases res with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
    | some c =>
      have short : out.val.length < Usize.max := by omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out c short)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := encode_range_list_meaning context ranges next pushed
        (by rw [contents, nextIndex]; simp; omega) each
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, push,
        advance, restRun], fun v hv => ?_⟩
      obtain ⟨prefix', tail⟩ := restFacts v hv
      rw [contents] at prefix' tail
      rw [nextIndex] at tail
      have pushedLength : (out.val ++ [c]).length = out.val.length + 1 := by simp
      rw [pushedLength] at prefix' tail
      have vLength : out.val.length < v.val.length := by
        have := congrArg List.length prefix'
        simp at this; omega
      refine ⟨?_, ?_⟩
      · have := congrArg (List.take out.val.length) prefix'
        simpa [List.take_take] using this
      · rw [split, List.drop_eq_getElem_cons vLength]
        have head : v.val[out.val.length] = c := by
          have := congrArg (fun l => l[out.val.length]?) prefix'
          simp [List.getElem?_take] at this
          rw [List.getElem?_eq_getElem vLength] at this
          simpa using this
        rw [head]
        exact .cons (means c rfl) tail
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun v hv => ?_⟩
    cases hv
    simp [List.drop_eq_nil_iff.mpr (show ranges.val.length ≤ index.val by omega)]
termination_by ranges.val.length - index.val
decreasing_by omega

theorem forall2_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ a ∈ l1, ∃ b ∈ l2, R a b
  | _, _, .nil, _, member => by cases member
  | _, _, .cons head tail, a, member => by
    rcases List.mem_cons.mp member with same | later
    · exact ⟨_, List.mem_cons_self, same ▸ head⟩
    · obtain ⟨b, inside, rel⟩ := forall2_mem_left tail a later
      exact ⟨b, List.mem_cons_of_mem _ inside, rel⟩

theorem forall2_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ b ∈ l2, ∃ a ∈ l1, R a b
  | _, _, .nil, _, member => by cases member
  | _, _, .cons head tail, b, member => by
    rcases List.mem_cons.mp member with same | later
    · exact ⟨_, List.mem_cons_self, same ▸ head⟩
    · obtain ⟨a, inside, rel⟩ := forall2_mem_right tail b later
      exact ⟨a, List.mem_cons_of_mem _ inside, rel⟩

/-- The encodings of the members of a data intersection or union, member by
    member. -/
theorem encode_ranges_meaning (context : data_ontology.Context) (members : AtLeastTwo DataRange)
    (each : ∀ e ∈ members.elements, ∃ res, data_ontology.encode_range context e = .ok res ∧
      ∀ c, res = some c → RangeMeans.{u,v,w,x} context e c) :
    ∃ res, data_ontology.encode_ranges context members = .ok res ∧
      ∀ cs, res = some cs → List.Forall₂ (fun c e => RangeMeans.{u,v,w,x} context e c) cs.elements members.elements := by
  rw [data_ontology.encode_ranges]
  obtain ⟨r1, run1, means1⟩ := each members.first (by simp [AtLeastTwo.elements])
  obtain ⟨r2, run2, means2⟩ := each members.second (by simp [AtLeastTwo.elements])
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some c1 =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some c2 =>
      obtain ⟨r3, run3, means3⟩ := encode_range_list_meaning.{u,v,w,x} context members.rest 0#usize
        (alloc.vec.Vec.new ClassExpression) (by simp [new_val])
        (fun e mem => each e (by simp [AtLeastTwo.elements, mem]))
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
      | some rest =>
        refine ⟨some ⟨c1, c2, rest⟩, by simp [run1, run2, run3], fun cs hcs => ?_⟩
        cases hcs
        obtain ⟨_, tail⟩ := means3 rest rfl
        simp only [new_val, List.length_nil, List.drop_zero, zero_val] at tail
        exact .cons (means1 c1 rfl) (.cons (means2 c2 rfl) tail)

/-! ### Numeric ranges -/

theorem in_closed (v : datatypes.DataValue) (r : ℝ) :
    Rowl.Regions.InCut ⟨v, false⟩ r ↔ (Rowl.Datatypes.numValue v : ℝ) ≤ r := by
  simp [Rowl.Regions.InCut]

theorem in_open (v : datatypes.DataValue) (r : ℝ) :
    Rowl.Regions.InCut ⟨v, true⟩ r ↔ (Rowl.Datatypes.numValue v : ℝ) < r := by
  simp [Rowl.Regions.InCut]

/-- The class of a bound's cut, or `owl:Thing` without a bound. -/
theorem bound_class_correct (context : data_ontology.Context) (bound : Option datatypes.DataValue)
    («open» outside : Bool) :
    ∃ res, data_ontology.bound_class context bound «open» outside = .ok res ∧ ∀ c, res = some c →
      (bound = none ∧ c = .Class thing) ∨ ∃ (v : datatypes.DataValue) (i : Usize)
        (h : i.val < context.cuts.val.length), bound = some v ∧ context.cuts.val[i.val] = ⟨v, «open»⟩ ∧
        c = if outside then .ObjectComplementOf (.Class (cutClass i)) else .Class (cutClass i) := by
  cases bound with
  | none => exact ⟨some (.Class thing), by simp [data_ontology.bound_class, thing_eq], fun c h => .inl ⟨rfl, by
      cases h; rfl⟩⟩
  | some v =>
    obtain ⟨o, run, _, found⟩ := Rowl.Regions.cut_index_correct context.cuts v «open» 0#usize
    cases o with
    | none => exact ⟨none, by simp [data_ontology.bound_class, run], by simp⟩
    | some i =>
      obtain ⟨h, at_i⟩ := found i rfl
      cases outside
      · exact ⟨some (.Class (cutClass i)), by simp [data_ontology.bound_class, run, cut_class_eq],
          fun c hc => .inr ⟨v, i, h, rfl, at_i, by cases hc; simp⟩⟩
      · exact ⟨some (.ObjectComplementOf (.Class (cutClass i))),
          by simp [data_ontology.bound_class, run, cut_class_eq, data_ontology.not],
          fun c hc => .inr ⟨v, i, h, rfl, at_i, by cases hc; simp⟩⟩

theorem realIn_subtype {k : datatypes.Kind} (sub : Rowl.Datatypes.IsSubtype k) (r : ℝ) :
    Rowl.Datatypes.RealIn k r ↔ ∃ z : ℤ, Rowl.DatatypeMap.Bounded (Rowl.Datatypes.lowerOf k)
      (Rowl.Datatypes.upperOf k) z ∧ r = z := by
  cases k <;> simp_all [Rowl.Datatypes.IsSubtype, Rowl.Datatypes.RealIn]

theorem bounded_eq (k : datatypes.Kind) : data_ontology.bounded k = .ok (decide (Rowl.Datatypes.IsSubtype k)) := by
  cases k <;> simp [data_ontology.bounded, Rowl.Datatypes.IsSubtype]

theorem numeric_kind_eq (k : datatypes.Kind) :
    data_ontology.numeric_kind k = .ok (decide (Rowl.Datatypes.IsNumeric k)) := by
  cases k <;> simp [data_ontology.numeric_kind, Rowl.Datatypes.IsNumeric]

theorem and3_eq (a b c : ClassExpression) :
    ∃ rest : alloc.vec.Vec ClassExpression, rest.val = [c] ∧
      data_ontology.and3 a b c = .ok (.ObjectIntersectionOf ⟨a, b, rest⟩) := by
  rw [data_ontology.and3]
  obtain ⟨rest, run, value⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new ClassExpression) c (by simp [new_val]; scalar_tac))
  exact ⟨rest, by rw [value]; simp [new_val], by rw [run]; simp⟩

theorem inter_iff (J : Interpretation Object' Value') (xs : AtLeastTwo ClassExpression) (d : Object') :
    classDenote J (.ObjectIntersectionOf xs) d ↔ ∀ e ∈ xs.elements, classDenote J e d := by
  rw [classDenote]; simp [AtLeastTwo.elements]

theorem and3_iff (J : Interpretation Object' Value') (a b c : ClassExpression) (rest : alloc.vec.Vec ClassExpression)
    (single : rest.val = [c]) (d : Object') :
    classDenote J (.ObjectIntersectionOf ⟨a, b, rest⟩) d ↔
      classDenote J a d ∧ classDenote J b d ∧ classDenote J c d := by
  rw [inter_iff]; simp [AtLeastTwo.elements, single]

/-- What the class of a bound's cut says at a data node standing for a value,
    when numbers are ordered. -/
theorem bound_meaning {context : data_ontology.Context} {I : Interpretation Object Value}
    {J : Interpretation Object' Value'} {lit : datatypes.DataValue → Value} {num : ℝ → Value}
    {d : Object'} {x : Value} (node : NodeValue context I J lit num d x)
    (ordered : context.kinds.ordered = true) {v : datatypes.DataValue} {i : Usize}
    (h : i.val < context.cuts.val.length) («open» : Bool) (at_i : context.cuts.val[i.val] = ⟨v, «open»⟩) :
    J.classes (cutClass i) d ↔ ∃ r, x = num r ∧ Rowl.Regions.InCut ⟨v, «open»⟩ r := by
  rw [node.cuts ordered i h, at_i]

/-- The class expression of a datatype of a kind holds at a data node standing
    for a value exactly when the value is in the datatype. -/
theorem kind_range_meaning (context : data_ontology.Context) (k : datatypes.Kind) :
    ∃ res, data_ontology.kind_range context k = .ok res ∧ ∀ c, res = some c →
      ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
        (I : Interpretation Object Value) (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value)
        (num : ℝ → Value), RangeFrame I J lit num → ∀ d x, NodeValue context I J lit num d x →
          (I.datatypes (typeOf k) x ↔ classDenote J c d) := by
  rw [data_ontology.kind_range, bounded_eq]
  by_cases sub : Rowl.Datatypes.IsSubtype k
  · simp only [sub, decide_true, ↓reduceIte]
    rw [data_ontology.subtype_range, used_eq]
    by_cases ready : Used context.kinds .Integer = true ∧ context.kinds.ordered = true
    · obtain ⟨lo, loRun, loNone, loSome⟩ := Rowl.Datatypes.lower_bound_correct k
      obtain ⟨hi, hiRun, hiNone, hiSome⟩ := Rowl.Datatypes.upper_bound_correct k
      obtain ⟨lc, lcRun, lcFacts⟩ := bound_class_correct context lo false false
      obtain ⟨uc, ucRun, ucFacts⟩ := bound_class_correct context hi true true
      cases lc with
      | none => exact ⟨none, by simp [ready, loRun, lcRun, hiRun, ucRun], by simp⟩
      | some lower =>
        cases uc with
        | none => exact ⟨none, by simp [ready, loRun, lcRun, hiRun, ucRun], by simp⟩
        | some upper =>
          obtain ⟨rest, single, andRun⟩ := and3_eq (.Class (kindClass .Integer)) lower upper
          refine ⟨some (.ObjectIntersectionOf ⟨.Class (kindClass .Integer), lower, rest⟩),
            by simp [ready, loRun, lcRun, hiRun, ucRun, kind_class_eq, andRun], fun c hc => ?_⟩
          cases hc
          intro Object Value Object' Value' I J lit num frame d x node
          rw [and3_iff J _ _ _ rest single, frame.numeric k (by cases k <;> simp_all [Rowl.Datatypes.IsSubtype, Rowl.Datatypes.IsNumeric])]
          simp only [classDenote]
          rw [node.kinds .Integer ready.1, frame.numeric .Integer (by simp [Rowl.Datatypes.IsNumeric])]
          simp only [Rowl.Datatypes.RealIn]
          -- the lower bound
          have lowerIff : classDenote J lower d ↔ ∀ l, Rowl.Datatypes.lowerOf k = some l →
              ∃ r, x = num r ∧ (l : ℝ) ≤ r := by
            rcases lcFacts lower rfl with ⟨none, rfl⟩ | ⟨v, i, h, some, at_i, rfl⟩
            · simp only [classDenote, frame.thing d, true_iff]
              intro l hl
              exact absurd (loNone.mp none) (by simp [hl])
            · simp only [Bool.false_eq_true, ↓reduceIte, classDenote]
              rw [bound_meaning node ready.2 h false at_i]
              obtain ⟨l, hl, bv⟩ := loSome v some
              obtain ⟨_, value, _⟩ := Rowl.Datatypes.bound_number bv
              simp only [in_closed, value, hl, Option.some.injEq, forall_eq']
              push_cast; rfl
          have upperIff : classDenote J upper d ↔ ∀ u, Rowl.Datatypes.upperOf k = some u →
              ¬ ∃ r, x = num r ∧ (u : ℝ) < r := by
            rcases ucFacts upper rfl with ⟨none, rfl⟩ | ⟨v, i, h, some, at_i, rfl⟩
            · simp only [classDenote, frame.thing d, true_iff]
              intro u hu
              exact absurd (hiNone.mp none) (by simp [hu])
            · simp only [↓reduceIte, classDenote]
              rw [bound_meaning node ready.2 h true at_i]
              obtain ⟨u, hu, bv⟩ := hiSome v some
              obtain ⟨_, value, _⟩ := Rowl.Datatypes.bound_number bv
              simp only [in_open, value, hu, Option.some.injEq, forall_eq']
              push_cast; rfl
          rw [lowerIff, upperIff]
          constructor
          · rintro ⟨r, rfl, inside⟩
            obtain ⟨z, ⟨lo', hi'⟩, rfl⟩ := (realIn_subtype sub r).mp inside
            refine ⟨⟨z, rfl, z, rfl⟩, fun l hl => ⟨z, rfl, by exact_mod_cast lo' l hl⟩, fun u hu => ?_⟩
            rintro ⟨r', same, lt⟩
            have := frame.injective same
            subst this
            have : (z : ℝ) ≤ u := by exact_mod_cast hi' u hu
            linarith
          · rintro ⟨⟨r, rfl, z, rfl⟩, lower', upper'⟩
            refine ⟨z, rfl, (realIn_subtype sub _).mpr ⟨z, ⟨fun l hl => ?_, fun u hu => ?_⟩, rfl⟩⟩
            · obtain ⟨r', same, le⟩ := lower' l hl
              have := frame.injective same
              subst this
              exact_mod_cast le
            · by_contra above
              exact upper' u hu ⟨z, rfl, by exact_mod_cast (lt_of_not_ge above)⟩
    · exact ⟨none, by simp [ready], by simp⟩
  · simp only [sub, decide_false, Bool.false_eq_true, ↓reduceIte, used_eq, bind_ok]
    by_cases inUse : Used context.kinds k = true
    · refine ⟨some (.Class (kindClass k)), by simp [inUse, kind_class_eq], fun c hc => ?_⟩
      cases hc
      intro Object Value Object' Value' I J lit num frame d x node
      simp only [classDenote]
      exact (node.kinds k inUse).symm
    · exact ⟨none, by simp [inUse], by simp⟩

/-- The side of a range facet's cut: open for the exclusive lower and the
    inclusive upper bound. -/
def FacetOpen : datatypes.Facet → Bool
  | .MinInclusive => false
  | .MinExclusive => true
  | .MaxInclusive => true
  | .MaxExclusive => false

/-- Whether a range facet's values lie outside its cut: for the upper bounds. -/
def FacetOutside : datatypes.Facet → Bool
  | .MinInclusive => false
  | .MinExclusive => false
  | .MaxInclusive => true
  | .MaxExclusive => true

theorem facet_open_eq (F : datatypes.Facet) : data_ontology.facet_open F = .ok (FacetOpen F) := by
  cases F <;> rfl

theorem facet_outside_eq (F : datatypes.Facet) : data_ontology.facet_outside F = .ok (FacetOutside F) := by
  cases F <;> rfl

/-- The class of a facet restriction holds at a data node standing for a
    number exactly when the facet holds of it, when numbers are ordered. -/
theorem facet_class_meaning (context : data_ontology.Context) (f : FacetRestriction) :
    ∃ res, data_ontology.facet_class context f = .ok res ∧ ∀ c, res = some c →
      ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
        (I : Interpretation Object Value) (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value)
        (num : ℝ → Value), RangeFrame I J lit num → ∀ d x, NodeValue context I J lit num d x →
          context.kinds.ordered = true → (∃ r, x = num r) → (I.facets f x ↔ classDenote J c d) := by
  rw [data_ontology.facet_class, Rowl.Datatypes.facet_of_correct]
  obtain ⟨result, run, someValue, _⟩ := Rowl.Datatypes.literal_value_correct.{0} f.value
  rw [run]
  cases facet : Rowl.Datatypes.facetOf f.facet with
  | none => exact ⟨none, by simp, by simp⟩
  | some F =>
    cases result with
    | none => exact ⟨none, by simp, by simp⟩
    | some w =>
      by_cases number : Rowl.Datatypes.IsNumber w
      · obtain ⟨res, bRun, bFacts⟩ := bound_class_correct context (some w) (FacetOpen F) (FacetOutside F)
        refine ⟨res, by simp [Rowl.Datatypes.numeric_correct, number, facet_open_eq, facet_outside_eq, bRun],
          fun c hc => ?_⟩
        intro Object Value Object' Value' I J lit num frame d x node ordered isNumber
        rcases bFacts c hc with ⟨none, _⟩ | ⟨v, i, h, same, at_i, rfl⟩
        · cases none
        · cases same
          rw [frame.facets f F w facet run number x]
          obtain ⟨r0, rfl⟩ := isNumber
          have one : ∀ P : ℝ → Prop, (∃ r, num r0 = num r ∧ P r) ↔ P r0 := fun P =>
            ⟨fun ⟨r, same, holds⟩ => (frame.injective same) ▸ holds, fun holds => ⟨r0, rfl, holds⟩⟩
          cases F <;> simp only [FacetOpen, FacetOutside, ↓reduceIte, Bool.false_eq_true, classDenote] <;>
            rw [bound_meaning node ordered h _ at_i] <;>
            simp only [one, FacetOpen, in_closed, in_open, FacetReal, not_lt, not_le]
      · exact ⟨none, by simp [Rowl.Datatypes.numeric_correct, number], by simp⟩

/-- The classes of the facet restrictions of a list, member by member. -/
theorem facet_classes_meaning (context : data_ontology.Context) (restrictions : alloc.vec.Vec FacetRestriction)
    (index : Usize) (out : alloc.vec.Vec ClassExpression)
    (room : out.val.length + (restrictions.val.length - index.val) ≤ Usize.max) :
    ∃ res, data_ontology.facet_classes context restrictions index out = .ok res ∧
      ∀ v, res = some v → v.val.take out.val.length = out.val ∧
        List.Forall₂ (fun c f => ∃ res, data_ontology.facet_class context f = .ok (some res) ∧ res = c)
          (v.val.drop out.val.length) (restrictions.val.drop index.val) := by
  rw [data_ontology.facet_classes]
  by_cases inside : index.val < restrictions.val.length
  · have lookup : restrictions.index_usize index = .ok restrictions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨res, run, _⟩ := facet_class_meaning.{0,0,0,0} context restrictions.val[index.val]
    cases res with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
    | some c =>
      have short : out.val.length < Usize.max := by omega
      have notFull : ¬ (alloc.vec.Vec.len out = core.num.Usize.MAX) := fun h => by
        have := congrArg UScalar.val h; simp [core.num.Usize.MAX] at this; omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out c short)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := facet_classes_meaning context restrictions next pushed
        (by rw [contents, nextIndex]; simp; omega)
      refine ⟨rest, ?_, fun v hv => ?_⟩
      · have lt : alloc.vec.Vec.len out < core.num.Usize.MAX := by
          simp [UScalar.lt_equiv, core.num.Usize.MAX]; omega
        simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, lt, push, advance, restRun]
      obtain ⟨prefix', tail⟩ := restFacts v hv
      rw [contents] at prefix' tail
      rw [nextIndex] at tail
      have pushedLength : (out.val ++ [c]).length = out.val.length + 1 := by simp
      rw [pushedLength] at prefix' tail
      have vLength : out.val.length < v.val.length := by
        have := congrArg List.length prefix'
        simp at this; omega
      refine ⟨?_, ?_⟩
      · have := congrArg (List.take out.val.length) prefix'
        simpa [List.take_take] using this
      · rw [split, List.drop_eq_getElem_cons vLength]
        have head : v.val[out.val.length] = c := by
          have := congrArg (fun l => l[out.val.length]?) prefix'
          simp [List.getElem?_take] at this
          rw [List.getElem?_eq_getElem vLength] at this
          simpa using this
        rw [head]
        exact .cons ⟨c, run, rfl⟩ tail
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun v hv => ?_⟩
    cases hv
    simp [List.drop_eq_nil_iff.mpr (show restrictions.val.length ≤ index.val by omega)]
termination_by restrictions.val.length - index.val
decreasing_by omega

/-- The encoding of a data range means it at every data node that stands for a
    value. -/
theorem encode_range_meaning (context : data_ontology.Context) (range : DataRange) :
    ∃ res, data_ontology.encode_range context range = .ok res ∧
      ∀ c, res = some c → RangeMeans.{u,v,w,x} context range c := by
  cases h : range with
  | Datatype dt =>
    rw [data_ontology.encode_range, is_literal_correct]
    by_cases literal : dt = literalDatatype
    · refine ⟨some (.Class thing), by simp [literal, thing_eq], fun c hc => ?_⟩
      cases hc
      intro Object Value Object' Value' I J lit num frame d x _
      subst literal
      simp [dataDenote, classDenote, frame.literal x, frame.thing d]
    · simp only [literal, decide_false, Bool.false_eq_true, ↓reduceIte, Rowl.Datatypes.kind_of_correct, bind_ok]
      cases kind : kindOf dt with
      | none => exact ⟨none, by simp, by simp⟩
      | some k =>
        obtain ⟨res, run, means⟩ := kind_range_meaning.{u,v,w,x} context k
        refine ⟨res, by simp [run], fun c hc => ?_⟩
        intro Object Value Object' Value' I J lit num frame d x node
        rw [Rowl.Datatypes.kindOf_some kind]
        simp only [dataDenote]
        exact means c hc I J lit num frame d x node
  | Intersection members =>
    rw [data_ontology.encode_range]
    have bound : ∀ e ∈ members.elements, sizeOf e < 1 + sizeOf members := by
      intro e mem
      simp only [AtLeastTwo.elements, List.mem_cons] at mem
      rcases mem with rfl | rfl | mem
      · have := first_size members; omega
      · have := second_size members; omega
      · have := member_size members e mem; omega
    obtain ⟨res, run, means⟩ := encode_ranges_meaning.{u,v,w,x} context members (fun e mem => by
      have := bound e mem
      exact encode_range_meaning context e)
    cases res with
    | none => exact ⟨none, by simp [run], by simp⟩
    | some cs =>
      refine ⟨some (.ObjectIntersectionOf cs), by simp [run], fun c hc => ?_⟩
      cases hc
      intro Object Value Object' Value' I J lit num frame d x node
      have pairs := means cs rfl
      have every : (∀ e ∈ members.elements, dataDenote I e x) ↔ ∀ c ∈ cs.elements, classDenote J c d := by
        constructor
        · intro all c member
          obtain ⟨e, inside, rel⟩ := forall2_mem_left pairs c member
          exact (rel I J lit num frame d x node).mp (all e inside)
        · intro all e member
          obtain ⟨c, inside, rel⟩ := forall2_mem_right pairs e member
          exact (rel I J lit num frame d x node).mpr (all c inside)
      rw [dataDenote, classDenote]
      simpa [AtLeastTwo.elements] using every
  | Union members =>
    rw [data_ontology.encode_range]
    have bound : ∀ e ∈ members.elements, sizeOf e < 1 + sizeOf members := by
      intro e mem
      simp only [AtLeastTwo.elements, List.mem_cons] at mem
      rcases mem with rfl | rfl | mem
      · have := first_size members; omega
      · have := second_size members; omega
      · have := member_size members e mem; omega
    obtain ⟨res, run, means⟩ := encode_ranges_meaning.{u,v,w,x} context members (fun e mem => by
      have := bound e mem
      exact encode_range_meaning context e)
    cases res with
    | none => exact ⟨none, by simp [run], by simp⟩
    | some cs =>
      refine ⟨some (.ObjectUnionOf cs), by simp [run], fun c hc => ?_⟩
      cases hc
      intro Object Value Object' Value' I J lit num frame d x node
      have pairs := means cs rfl
      have some' : (∃ e ∈ members.elements, dataDenote I e x) ↔ ∃ c ∈ cs.elements, classDenote J c d := by
        constructor
        · rintro ⟨e, member, holds⟩
          obtain ⟨c, inside, rel⟩ := forall2_mem_right pairs e member
          exact ⟨c, inside, (rel I J lit num frame d x node).mp holds⟩
        · rintro ⟨c, member, holds⟩
          obtain ⟨e, inside, rel⟩ := forall2_mem_left pairs c member
          exact ⟨e, inside, (rel I J lit num frame d x node).mpr holds⟩
      rw [dataDenote, classDenote]
      simpa [AtLeastTwo.elements, or_assoc] using some'
  | Complement inner =>
    rw [data_ontology.encode_range]
    have : sizeOf inner < sizeOf range := by rw [h]; simp
    obtain ⟨res, run, means⟩ := encode_range_meaning context inner
    cases res with
    | none => exact ⟨none, by simp [run], by simp⟩
    | some c =>
      refine ⟨some (.ObjectComplementOf c), by simp [run], fun c' hc => ?_⟩
      cases hc
      intro Object Value Object' Value' I J lit num frame d x node
      rw [dataDenote, classDenote]
      exact not_congr (means c rfl I J lit num frame d x node)
  | OneOf literals =>
    rw [data_ontology.encode_range]
    obtain ⟨first, firstRun, _⟩ := literal_individual_correct context literals.first
    cases first with
    | none => exact ⟨none, by simp [firstRun], by simp⟩
    | some a =>
      obtain ⟨rest, restRun, restFacts⟩ := literal_individuals_correct context literals.rest 0#usize
        (alloc.vec.Vec.new Individual) (by simp [new_val])
      cases rest with
      | none => exact ⟨none, by simp [firstRun, restRun], by simp⟩
      | some others =>
        refine ⟨some (.ObjectOneOf ⟨a, others⟩), by simp [firstRun, restRun], fun c hc => ?_⟩
        cases hc
        intro Object Value Object' Value' I J lit num frame d x node
        obtain ⟨pairs, _⟩ := restFacts others rfl
        simp only [new_val, List.length_nil, List.drop_zero, zero_val] at pairs
        rw [dataDenote, classDenote]
        constructor
        · rintro ⟨lt, member, holds⟩
          simp only [NonEmpty.elements, List.mem_cons] at member
          rcases member with rfl | later
          · exact ⟨a, by simp [NonEmpty.elements], (literal_individual_meaning context _ a firstRun frame node).mpr holds⟩
          · obtain ⟨b, inside, ⟨r, run, rfl⟩⟩ := forall2_mem_right pairs lt later
            exact ⟨r, by simp [NonEmpty.elements, inside], (literal_individual_meaning context lt r run frame node).mpr holds⟩
        · rintro ⟨b, member, holds⟩
          simp only [NonEmpty.elements, List.mem_cons] at member
          rcases member with rfl | later
          · exact ⟨literals.first, by simp [NonEmpty.elements],
              (literal_individual_meaning context _ _ firstRun frame node).mp holds⟩
          · obtain ⟨lt, inside, ⟨r, run, rfl⟩⟩ := forall2_mem_left pairs b later
            exact ⟨lt, by simp [NonEmpty.elements, inside], (literal_individual_meaning context lt r run frame node).mp holds⟩
  | Restriction dt restrictions =>
    rw [data_ontology.encode_range, Rowl.Datatypes.kind_of_correct]
    cases kind : kindOf dt with
    | none => exact ⟨none, by simp, by simp⟩
    | some k =>
      simp only [bind_ok]
      rw [data_ontology.restriction_range, numeric_kind_eq]
      by_cases ready : Rowl.Datatypes.IsNumeric k ∧ context.kinds.ordered = true
      · obtain ⟨b, bRun, bMeans⟩ := kind_range_meaning.{u,v,w,x} context k
        obtain ⟨f, fRun, fMeans⟩ := facet_class_meaning.{u,v,w,x} context restrictions.first
        obtain ⟨fs, fsRun, fsFacts⟩ := facet_classes_meaning context restrictions.rest 0#usize
          (alloc.vec.Vec.new ClassExpression) (by simp [new_val])
        cases b with
        | none => exact ⟨none, by simp [ready, bRun, fRun, fsRun], by simp⟩
        | some base =>
          cases f with
          | none => exact ⟨none, by simp [ready, bRun, fRun, fsRun], by simp⟩
          | some first =>
            cases fs with
            | none => exact ⟨none, by simp [ready, bRun, fRun, fsRun], by simp⟩
            | some rest =>
              refine ⟨some (.ObjectIntersectionOf ⟨base, first, rest⟩), by simp [ready, bRun, fRun, fsRun],
                fun c hc => ?_⟩
              cases hc
              intro Object Value Object' Value' I J lit num frame d x node
              obtain ⟨_, pairs⟩ := fsFacts rest rfl
              simp only [new_val, List.length_nil, List.drop_zero, zero_val] at pairs
              rw [Rowl.Datatypes.kindOf_some kind]
              rw [dataDenote, inter_iff]
              simp only [AtLeastTwo.elements, NonEmpty.elements, List.mem_cons, forall_eq_or_imp]
              rw [← bMeans base rfl I J lit num frame d x node]
              constructor
              · rintro ⟨inType, firstFacet, restFacets⟩
                have isNumber := (frame.numeric k ready.1 x).mp inType
                obtain ⟨r, rfl, _⟩ := isNumber
                refine ⟨inType, (fMeans first rfl I J lit num frame d _ node ready.2 ⟨r, rfl⟩).mp firstFacet,
                  fun c member => ?_⟩
                obtain ⟨e, inside, ⟨res, run', same⟩⟩ := forall2_mem_left pairs c member
                obtain ⟨_, run'', means⟩ := facet_class_meaning.{u,v,w,x} context e
                rw [run''] at run'
                cases Result.ok_injective run'
                subst same
                exact (means res rfl I J lit num frame d _ node ready.2 ⟨r, rfl⟩).mp (restFacets e inside)
              · rintro ⟨inType, firstHolds, restHold⟩
                have isNumber := (frame.numeric k ready.1 x).mp inType
                obtain ⟨r, rfl, _⟩ := isNumber
                refine ⟨inType, (fMeans first rfl I J lit num frame d _ node ready.2 ⟨r, rfl⟩).mpr firstHolds,
                  fun e later => ?_⟩
                obtain ⟨c, inside, ⟨res, run', same⟩⟩ := forall2_mem_right pairs e later
                obtain ⟨_, run'', means⟩ := facet_class_meaning.{u,v,w,x} context e
                rw [run''] at run'
                cases Result.ok_injective run'
                subst same
                exact (means res rfl I J lit num frame d _ node ready.2 ⟨r, rfl⟩).mpr (restHold res inside)
      · exact ⟨none, by simp [ready], by simp⟩
termination_by sizeOf range
decreasing_by all_goals (subst_vars; first | omega | (simp_wf; omega))

/-! ### Class expressions -/

theorem copy_natural_eq (n : probes.Natural) : data_ontology.copy_natural n = .ok n := by
  induction n with
  | Zero => rw [data_ontology.copy_natural]
  | Succ inner ih => rw [data_ontology.copy_natural, ih]; simp

/-- The filler of a data number restriction: every value without one. -/
def RangeHolds (I : Interpretation Object Value) (range : Option DataRange) (y : Value) : Prop :=
  match range with
  | none => True
  | some r => dataDenote I r y

/-- The data restrictions of a class expression as a data property, an optional
    filler and a count: the expression's data restrictions are decided by
    whether an element has at least `count` values along the property in the
    filler. A universal restriction counts the values outside its range, and a
    value restriction its literal. -/
def classAtoms (c : ClassExpression) : List (DataProperty × Option DataRange × Nat) :=
  match c with
  | .Class _ => []
  | .ObjectIntersectionOf xs => classAtoms xs.first ++ classAtoms xs.second ++
      xs.rest.val.attach.flatMap (fun e => classAtoms e.1)
  | .ObjectUnionOf xs => classAtoms xs.first ++ classAtoms xs.second ++
      xs.rest.val.attach.flatMap (fun e => classAtoms e.1)
  | .ObjectComplementOf e => classAtoms e
  | .ObjectOneOf _ => []
  | .ObjectSomeValuesFrom _ e => classAtoms e
  | .ObjectAllValuesFrom _ e => classAtoms e
  | .ObjectHasValue _ _ => []
  | .ObjectHasSelf _ => []
  | .ObjectMinCardinality _ _ none | .ObjectMaxCardinality _ _ none | .ObjectExactCardinality _ _ none => []
  | .ObjectMinCardinality _ _ (some e) | .ObjectMaxCardinality _ _ (some e)
  | .ObjectExactCardinality _ _ (some e) => classAtoms e
  | .DataSomeValuesFrom p r => [(p, some r, 1)]
  | .DataAllValuesFrom p r => [(p, some (.Complement r), 1)]
  | .DataHasValue p lt => [(p, some (.OneOf ⟨lt, alloc.vec.Vec.new Literal⟩), 1)]
  | .DataMinCardinality n p r => [(p, r, Rowl.Probes.naturalValue n)]
  | .DataMaxCardinality n p r => [(p, r, Rowl.Probes.naturalValue n + 1)]
  | .DataExactCardinality n p r => [(p, r, Rowl.Probes.naturalValue n), (p, r, Rowl.Probes.naturalValue n + 1)]
termination_by sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := member_size xs _ e.2; omega)

/-- The individuals of the nominals and value restrictions of a class expression. -/
def classIndividuals (c : ClassExpression) : List Individual :=
  match c with
  | .Class _ => []
  | .ObjectIntersectionOf xs => classIndividuals xs.first ++ classIndividuals xs.second ++
      xs.rest.val.attach.flatMap (fun e => classIndividuals e.1)
  | .ObjectUnionOf xs => classIndividuals xs.first ++ classIndividuals xs.second ++
      xs.rest.val.attach.flatMap (fun e => classIndividuals e.1)
  | .ObjectComplementOf e => classIndividuals e
  | .ObjectOneOf xs => xs.elements
  | .ObjectSomeValuesFrom _ e => classIndividuals e
  | .ObjectAllValuesFrom _ e => classIndividuals e
  | .ObjectHasValue _ a => [a]
  | .ObjectHasSelf _ => []
  | .ObjectMinCardinality _ _ none | .ObjectMaxCardinality _ _ none | .ObjectExactCardinality _ _ none => []
  | .ObjectMinCardinality _ _ (some e) | .ObjectMaxCardinality _ _ (some e)
  | .ObjectExactCardinality _ _ (some e) => classIndividuals e
  | _ => []
termination_by sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := member_size xs _ e.2; omega)

/-- A correspondence between an OWL interpretation `I` and an interpretation
    `J` of the encoding: `obj` places the elements of `I` one to one at the
    elements of `J` that are no data nodes; the names that are not the
    encoding's mean the same; the object properties of the context relate only
    elements that are no data nodes, and the universal role every pair; the
    `known` individuals sit at their places; and for each data restriction of
    `atoms`, an element has at least as many values in its filler as its place
    has neighbours along the property's role in the filler's encoding. -/
structure Simulates (context : data_ontology.Context) (I : Interpretation Object Value)
    (J : Interpretation Object' Value') (obj : Object → Object') (known : Individual → Prop)
    (atoms : List (DataProperty × Option DataRange × Nat)) : Prop where
  injective : Function.Injective obj
  objects : ∀ y, ¬ J.classes dataClass y ↔ ∃ z, obj z = y
  classes : ∀ (c : Class) z, ¬ Reserved c.iri.spelling.val → (I.classes c z ↔ J.classes c (obj z))
  roles : ∀ (r : ObjectProperty) z y, ¬ Reserved r.iri.spelling.val →
    (I.objectProperties r z y ↔ J.objectProperties r (obj z) (obj y))
  closed : ∀ r ∈ context.roles.val, ∀ y y', J.objectProperties r y y' →
    ¬ J.classes dataClass y ∧ ¬ J.classes dataClass y'
  topAll : ∀ y y', J.objectProperties topObject y y'
  individuals : ∀ a, known a → individual J a = obj (individual I a)
  data : ∀ p range n, (p, range, n) ∈ atoms → ∀ role filler,
    data_ontology.data_role context p = .ok (some role) →
    data_ontology.encode_optional_range context range = .ok (some filler) → ∀ z,
      (AtLeast n (fun y => I.dataProperties p z y ∧ RangeHolds I range y) ↔
        AtLeast n (fun y => objectRelation J role (obj z) y ∧ Rowl.Concepts.FillerHolds J filler y))

theorem atLeast_one {α : Type u} (P : α → Prop) : AtLeast 1 P ↔ ∃ y, P y := by
  constructor
  · rintro ⟨f, _, each⟩; exact ⟨f 0, each 0⟩
  · rintro ⟨y, holds⟩; exact ⟨fun _ => y, fun i j _ => Subsingleton.elim i j, fun _ => holds⟩

/-- Counting through a one-to-one placement. -/
theorem atLeast_image {α : Type u} {β : Type w} (n : Nat) (P : α → Prop) (Q : β → Prop) (f : α → β)
    (injective : Function.Injective f) (same : ∀ b, Q b ↔ ∃ a, f a = b ∧ P a) : AtLeast n P ↔ AtLeast n Q := by
  constructor
  · rintro ⟨g, gInjective, each⟩
    exact ⟨f ∘ g, injective.comp gInjective, fun i => (same _).mpr ⟨g i, rfl, each i⟩⟩
  · rintro ⟨g, gInjective, each⟩
    choose h hf hp using fun i => (same (g i)).mp (each i)
    refine ⟨h, fun i j eq => gInjective ?_, hp⟩
    rw [← hf i, ← hf j, eq]

/-- What a class expression's encoding means: under every correspondence that
    covers the expression's data restrictions and individuals, it holds at the
    place of an element exactly when the expression holds at the element. -/
def ClassMeans (context : data_ontology.Context) (c c' : ClassExpression) : Prop :=
  ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
    (I : Interpretation Object Value) (J : Interpretation Object' Value') (obj : Object → Object')
    (known : Individual → Prop) (atoms : List (DataProperty × Option DataRange × Nat)),
    Simulates context I J obj known atoms → (∀ a ∈ classAtoms c, a ∈ atoms) →
    (∀ a ∈ classIndividuals c, known a) → ∀ z, classDenote I c z ↔ classDenote J c' (obj z)

theorem relation_place {context : data_ontology.Context} {I : Interpretation Object Value}
    {J : Interpretation Object' Value'} {obj : Object → Object'} {known : Individual → Prop}
    {atoms : List (DataProperty × Option DataRange × Nat)} (sim : Simulates context I J obj known atoms)
    (r : ObjectPropertyExpression) (plain : ¬ Reserved (RoleOf r).iri.spelling.val) (z y : Object) :
    objectRelation I r z y ↔ objectRelation J r (obj z) (obj y) := by
  cases r with
  | Property a => exact sim.roles a z y plain
  | Inverse a => exact sim.roles a y z plain

theorem successor_place {context : data_ontology.Context} {I : Interpretation Object Value}
    {J : Interpretation Object' Value'} {obj : Object → Object'} {known : Individual → Prop}
    {atoms : List (DataProperty × Option DataRange × Nat)} (sim : Simulates context I J obj known atoms)
    (r : ObjectPropertyExpression) (inContext : RoleOf r ∈ context.roles.val) (z : Object) (y : Object')
    (related : objectRelation J r (obj z) y) : ∃ y0, obj y0 = y := by
  cases r with
  | Property a => exact (sim.objects y).mp (sim.closed a inContext _ _ related).2
  | Inverse a => exact (sim.objects y).mp (sim.closed a inContext _ _ related).1

theorem universal_relation {context : data_ontology.Context} {I : Interpretation Object Value}
    {J : Interpretation Object' Value'} {obj : Object → Object'} {known : Individual → Prop}
    {atoms : List (DataProperty × Option DataRange × Nat)} (sim : Simulates context I J obj known atoms)
    (r : ObjectPropertyExpression) (top : RoleOf r = topObject) (y y' : Object') : objectRelation J r y y' := by
  cases r with
  | Property a => simp only [RoleOf] at top; subst top; exact sim.topAll _ _
  | Inverse a => simp only [RoleOf] at top; subst top; exact sim.topAll _ _

theorem universal_relation_left {context : data_ontology.Context} {I : Interpretation Object Value}
    {J : Interpretation Object' Value'} {obj : Object → Object'} {known : Individual → Prop}
    {atoms : List (DataProperty × Option DataRange × Nat)} (sim : Simulates context I J obj known atoms)
    (r : ObjectPropertyExpression) (top : RoleOf r = topObject) (z y : Object) : objectRelation I r z y := by
  have := universal_relation sim r top (obj z) (obj y)
  have plain : ¬ Reserved (RoleOf r).iri.spelling.val := by rw [top]; exact topObject_plain
  exact (relation_place sim r plain z y).mpr this

theorem class_atoms_members (xs : AtLeastTwo ClassExpression) (e : ClassExpression) (member : e ∈ xs.elements)
    (a : DataProperty × Option DataRange × Nat) (inside : a ∈ classAtoms e) :
    a ∈ classAtoms (.ObjectIntersectionOf xs) ∧ a ∈ classAtoms (.ObjectUnionOf xs) := by
  simp only [AtLeastTwo.elements, List.mem_cons] at member
  rw [classAtoms, classAtoms]
  simp only [List.mem_append, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
  rcases member with rfl | rfl | member
  · exact ⟨.inl (.inl inside), .inl (.inl inside)⟩
  · exact ⟨.inl (.inr inside), .inl (.inr inside)⟩
  · exact ⟨.inr ⟨e, member, inside⟩, .inr ⟨e, member, inside⟩⟩

theorem class_individuals_members (xs : AtLeastTwo ClassExpression) (e : ClassExpression)
    (member : e ∈ xs.elements) (a : Individual) (inside : a ∈ classIndividuals e) :
    a ∈ classIndividuals (.ObjectIntersectionOf xs) ∧ a ∈ classIndividuals (.ObjectUnionOf xs) := by
  simp only [AtLeastTwo.elements, List.mem_cons] at member
  rw [classIndividuals, classIndividuals]
  simp only [List.mem_append, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
  rcases member with rfl | rfl | member
  · exact ⟨.inl (.inl inside), .inl (.inl inside)⟩
  · exact ⟨.inl (.inr inside), .inl (.inr inside)⟩
  · exact ⟨.inr ⟨e, member, inside⟩, .inr ⟨e, member, inside⟩⟩

/-- The encodings of a list of class expressions, member by member, with any
    property of each member's encoding. -/
theorem encode_class_list_spec (context : data_ontology.Context) (P : ClassExpression → ClassExpression → Prop)
    (classes : alloc.vec.Vec ClassExpression) (index : Usize) (out : alloc.vec.Vec ClassExpression)
    (room : out.val.length + (classes.val.length - index.val) ≤ Usize.max)
    (each : ∀ e ∈ classes.val, ∃ res, data_ontology.encode_class context e = .ok res ∧
      ∀ c, res = some c → P e c) :
    ∃ res, data_ontology.encode_class_list context classes index out = .ok res ∧
      ∀ v, res = some v → v.val.take out.val.length = out.val ∧
        List.Forall₂ (fun c e => P e c) (v.val.drop out.val.length) (classes.val.drop index.val) := by
  rw [data_ontology.encode_class_list]
  by_cases inside : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨res, run, means⟩ := each _ (List.getElem_mem inside)
    cases res with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
    | some c =>
      have short : out.val.length < Usize.max := by omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out c short)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := encode_class_list_spec context P classes next pushed
        (by rw [contents, nextIndex]; simp; omega) each
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, push,
        advance, restRun], fun v hv => ?_⟩
      obtain ⟨prefix', tail⟩ := restFacts v hv
      rw [contents] at prefix' tail
      rw [nextIndex] at tail
      have pushedLength : (out.val ++ [c]).length = out.val.length + 1 := by simp
      rw [pushedLength] at prefix' tail
      have vLength : out.val.length < v.val.length := by
        have := congrArg List.length prefix'
        simp at this; omega
      refine ⟨?_, ?_⟩
      · have := congrArg (List.take out.val.length) prefix'
        simpa [List.take_take] using this
      · rw [split, List.drop_eq_getElem_cons vLength]
        have head : v.val[out.val.length] = c := by
          have := congrArg (fun l => l[out.val.length]?) prefix'
          simp [List.getElem?_take] at this
          rw [List.getElem?_eq_getElem vLength] at this
          simpa using this
        rw [head]
        exact .cons (means c rfl) tail
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun v hv => ?_⟩
    cases hv
    simp [List.drop_eq_nil_iff.mpr (show classes.val.length ≤ index.val by omega)]
termination_by classes.val.length - index.val
decreasing_by omega

/-- The encodings of the members of an intersection or union, member by
    member, with any property of each member's encoding. -/
theorem encode_members_spec (context : data_ontology.Context) (P : ClassExpression → ClassExpression → Prop)
    (members : AtLeastTwo ClassExpression)
    (each : ∀ e ∈ members.elements, ∃ res, data_ontology.encode_class context e = .ok res ∧
      ∀ c, res = some c → P e c) :
    ∃ res, data_ontology.encode_members context members = .ok res ∧
      ∀ cs, res = some cs → List.Forall₂ (fun c e => P e c) cs.elements members.elements := by
  rw [data_ontology.encode_members]
  obtain ⟨r1, run1, means1⟩ := each members.first (by simp [AtLeastTwo.elements])
  obtain ⟨r2, run2, means2⟩ := each members.second (by simp [AtLeastTwo.elements])
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some c1 =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some c2 =>
      obtain ⟨r3, run3, means3⟩ := encode_class_list_spec context P members.rest 0#usize
        (alloc.vec.Vec.new ClassExpression) (by simp [new_val])
        (fun e mem => each e (by simp [AtLeastTwo.elements, mem]))
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
      | some rest =>
        refine ⟨some ⟨c1, c2, rest⟩, by simp [run1, run2, run3], fun cs hcs => ?_⟩
        cases hcs
        obtain ⟨_, tail⟩ := means3 rest rfl
        simp only [new_val, List.length_nil, List.drop_zero, zero_val] at tail
        exact .cons (means1 c1 rfl) (.cons (means2 c2 rfl) tail)

theorem intersection_iff (I : Interpretation Object Value) (xs : AtLeastTwo ClassExpression) (z : Object) :
    classDenote I (.ObjectIntersectionOf xs) z ↔ ∀ e ∈ xs.elements, classDenote I e z := by
  rw [classDenote]; simp [AtLeastTwo.elements]

theorem union_iff (I : Interpretation Object Value) (xs : AtLeastTwo ClassExpression) (z : Object) :
    classDenote I (.ObjectUnionOf xs) z ↔ ∃ e ∈ xs.elements, classDenote I e z := by
  rw [classDenote]; simp [AtLeastTwo.elements, or_assoc]

theorem encode_optional_some (context : data_ontology.Context) (range : DataRange) (c : ClassExpression)
    (run : data_ontology.encode_range context range = .ok (some c)) :
    data_ontology.encode_optional_range context (some range) = .ok (some (some c)) := by
  simp [data_ontology.encode_optional_range, run]

theorem encode_complement (context : data_ontology.Context) (range : DataRange) (c : ClassExpression)
    (run : data_ontology.encode_range context range = .ok (some c)) :
    data_ontology.encode_range context (.Complement range) = .ok (some (.ObjectComplementOf c)) := by
  rw [data_ontology.encode_range]; simp [run]

theorem encode_single (context : data_ontology.Context) (lt : Literal) (a : Individual)
    (run : data_ontology.literal_individual context lt = .ok (some a)) :
    data_ontology.encode_range context (.OneOf ⟨lt, alloc.vec.Vec.new Literal⟩) =
      .ok (some (.ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩)) := by
  rw [data_ontology.encode_range]
  simp only [run, bind_ok]
  rw [data_ontology.literal_individuals]
  simp [UScalar.lt_equiv, new_val]


theorem range_holds_some (I : Interpretation Object Value) (r : DataRange) (y : Value) :
    RangeHolds I (some r) y ↔ dataDenote I r y := Iff.rfl

theorem filler_holds_some (J : Interpretation Object' Value') (c : ClassExpression) (y : Object') :
    Rowl.Concepts.FillerHolds J (some c) y ↔ classDenote J c y := Iff.rfl

/-- What a counted filler's encoding means. -/
def FillerMeans (context : data_ontology.Context) : Option ClassExpression → Option ClassExpression → Prop
  | none, none => True
  | some f, some c => ClassMeans.{u,v,w,x} context f c
  | _, _ => False

/-- The encoding of a filler means it at the elements that stand for it. -/
theorem filler_place {context : data_ontology.Context} {I : Interpretation Object Value}
    {J : Interpretation Object' Value'} {obj : Object → Object'} {known : Individual → Prop}
    {atoms : List (DataProperty × Option DataRange × Nat)} (sim : Simulates context I J obj known atoms)
    (filler encoded : Option ClassExpression) (means : FillerMeans.{u,v,w,x} context filler encoded)
    (atomsIn : ∀ f, filler = some f → ∀ a ∈ classAtoms f, a ∈ atoms)
    (indsIn : ∀ f, filler = some f → ∀ a ∈ classIndividuals f, known a) (y : Object) :
    Rowl.Concepts.FillerHolds I filler y ↔ Rowl.Concepts.FillerHolds J encoded (obj y) := by
  cases filler with
  | none => cases encoded with
    | none => simp [Rowl.Concepts.FillerHolds]
    | some _ => exact absurd means (by simp [FillerMeans])
  | some f => cases encoded with
    | none => exact absurd means (by simp [FillerMeans])
    | some c => exact means I J obj known atoms sim (atomsIn f rfl) (indsIn f rfl) y

/-- The encoding of a data number restriction's filler runs. -/
theorem encode_optional_range_ok (context : data_ontology.Context) (range : Option DataRange) :
    ∃ res, data_ontology.encode_optional_range context range = .ok res := by
  cases range with
  | none => exact ⟨some none, rfl⟩
  | some r =>
    obtain ⟨res, run, _⟩ := encode_range_meaning.{0,0,0,0} context r
    cases res with
    | none => exact ⟨none, by simp [data_ontology.encode_optional_range, run]⟩
    | some c => exact ⟨some (some c), by simp [data_ontology.encode_optional_range, run]⟩

/-- The encoding of a class expression means it under every correspondence. -/
theorem encode_class_meaning (context : data_ontology.Context) (c : ClassExpression) :
    ∃ res, data_ontology.encode_class context c = .ok res ∧
      ∀ c', res = some c' → ClassMeans.{u,v,w,x} context c c' := by
  have bound : ∀ (xs : AtLeastTwo ClassExpression), ∀ e ∈ xs.elements, sizeOf e < 1 + sizeOf xs := by
    intro xs e mem
    simp only [AtLeastTwo.elements, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · have := first_size xs; omega
    · have := second_size xs; omega
    · have := member_size xs e mem; omega
  cases h : c with
  | Class k =>
    rw [data_ontology.encode_class, reserved_correct]
    by_cases reserved : Reserved k.iri.spelling.val
    · exact ⟨none, by simp [reserved], by simp⟩
    · refine ⟨some (.Class k), by simp [reserved, Rowl.Nnf.copy_bytes_identity, class_named_correct], ?_⟩
      intro c' hc; cases hc
      intro Object Value Object' Value' I J obj known atoms sim _ _ z
      rw [classDenote, classDenote]
      exact sim.classes k z reserved
  | ObjectIntersectionOf xs =>
    rw [data_ontology.encode_class]
    obtain ⟨res, run, means⟩ := encode_members_spec context (fun e c => ClassMeans.{u,v,w,x} context e c) xs (fun e mem => by
      have := bound xs e mem
      exact encode_class_meaning context e)
    cases res with
    | none => exact ⟨none, by simp [run], by simp⟩
    | some cs =>
      refine ⟨some (.ObjectIntersectionOf cs), by simp [run], ?_⟩
      intro c' hc; cases hc
      intro Object Value Object' Value' I J obj known atoms sim atomsIn indsIn z
      have pairs := means cs rfl
      have each : ∀ e ∈ xs.elements, ∀ c, ClassMeans context e c → (classDenote I e z ↔ classDenote J c (obj z)) :=
        fun e mem c m => m I J obj known atoms sim
          (fun a inside => atomsIn a (class_atoms_members xs e mem a inside).1)
          (fun a inside => indsIn a (class_individuals_members xs e mem a inside).1) z
      rw [intersection_iff, intersection_iff]
      constructor
      · intro all c member
        obtain ⟨e, inside, rel⟩ := forall2_mem_left pairs c member
        exact (each e inside c rel).mp (all e inside)
      · intro all e member
        obtain ⟨c, inside, rel⟩ := forall2_mem_right pairs e member
        exact (each e member c rel).mpr (all c inside)
  | ObjectUnionOf xs =>
    rw [data_ontology.encode_class]
    obtain ⟨res, run, means⟩ := encode_members_spec context (fun e c => ClassMeans.{u,v,w,x} context e c) xs (fun e mem => by
      have := bound xs e mem
      exact encode_class_meaning context e)
    cases res with
    | none => exact ⟨none, by simp [run], by simp⟩
    | some cs =>
      refine ⟨some (.ObjectUnionOf cs), by simp [run], ?_⟩
      intro c' hc; cases hc
      intro Object Value Object' Value' I J obj known atoms sim atomsIn indsIn z
      have pairs := means cs rfl
      have each : ∀ e ∈ xs.elements, ∀ c, ClassMeans context e c → (classDenote I e z ↔ classDenote J c (obj z)) :=
        fun e mem c m => m I J obj known atoms sim
          (fun a inside => atomsIn a (class_atoms_members xs e mem a inside).2)
          (fun a inside => indsIn a (class_individuals_members xs e mem a inside).2) z
      rw [union_iff, union_iff]
      constructor
      · rintro ⟨e, member, holds⟩
        obtain ⟨c, inside, rel⟩ := forall2_mem_right pairs e member
        exact ⟨c, inside, (each e member c rel).mp holds⟩
      · rintro ⟨c, member, holds⟩
        obtain ⟨e, inside, rel⟩ := forall2_mem_left pairs c member
        exact ⟨e, inside, (each e inside c rel).mpr holds⟩
  | ObjectComplementOf inner =>
    rw [data_ontology.encode_class]
    have : sizeOf inner < sizeOf c := by rw [h]; simp
    obtain ⟨res, run, means⟩ := encode_class_meaning context inner
    cases res with
    | none => exact ⟨none, by simp [run], by simp⟩
    | some ci =>
      refine ⟨some (.ObjectComplementOf ci), by simp [run], ?_⟩
      intro c' hc; cases hc
      intro Object Value Object' Value' I J obj known atoms sim atomsIn indsIn z
      rw [classDenote, classDenote]
      exact not_congr (means ci rfl I J obj known atoms sim
        (fun a inside => atomsIn a (by rw [classAtoms]; exact inside))
        (fun a inside => indsIn a (by rw [classIndividuals]; exact inside)) z)
  | ObjectOneOf xs =>
    rw [data_ontology.encode_class]
    obtain ⟨first, firstRun, _⟩ := object_individual_of_correct xs.first
    cases first with
    | none => exact ⟨none, by simp [firstRun], by simp⟩
    | some a =>
      have firstSame := object_individual_of_some firstRun
      obtain ⟨rest, restRun, restFacts⟩ := individuals_from_correct xs.rest 0#usize
        (alloc.vec.Vec.new Individual) (by simp [new_val])
      cases rest with
      | none => exact ⟨none, by simp [firstRun, restRun], by simp⟩
      | some others =>
        obtain ⟨othersSame, _⟩ := restFacts others rfl
        simp only [new_val, List.nil_append, zero_val, List.drop_zero] at othersSame
        have same : (⟨a, others⟩ : NonEmpty Individual) = xs := by
          cases xs; simp only [NonEmpty.mk.injEq]; exact ⟨firstSame.1, by simpa [alloc.vec.Vec.eq_iff] using othersSame⟩
        refine ⟨some (.ObjectOneOf ⟨a, others⟩), by simp [firstRun, restRun], ?_⟩
        intro c' hc; cases hc
        intro Object Value Object' Value' I J obj known atoms sim _ indsIn z
        rw [same, classDenote, classDenote]
        constructor
        · rintro ⟨b, member, rfl⟩
          exact ⟨b, member, sim.individuals b (indsIn b (by rw [classIndividuals]; exact member))⟩
        · rintro ⟨b, member, holds⟩
          refine ⟨b, member, sim.injective ?_⟩
          rw [← holds, sim.individuals b (indsIn b (by rw [classIndividuals]; exact member))]
  | ObjectSomeValuesFrom role filler =>
    rw [data_ontology.encode_class]
    have : sizeOf filler < sizeOf c := by rw [h]; simp
    obtain ⟨roleRes, roleRun, roleFacts⟩ := object_role_correct context role
    obtain ⟨res, run, means⟩ := encode_class_meaning context filler
    cases roleRes with
    | none => exact ⟨none, by simp [roleRun, run], by simp⟩
    | some copy =>
      obtain ⟨same, plain, inContext⟩ := roleFacts copy rfl
      subst copy
      cases res with
      | none => exact ⟨none, by simp [roleRun, run], by simp⟩
      | some f =>
        have fillerMeans : ClassMeans context filler f := means f rfl
        by_cases top : RoleOf role = topObject
        · refine ⟨some (.ObjectSomeValuesFrom role (.ObjectIntersectionOf ⟨f, .ObjectComplementOf (.Class dataClass),
            alloc.vec.Vec.new ClassExpression⟩)), ?_, ?_⟩
          · simp [roleRun, run, universal_correct, top, object_class_eq, data_ontology.and]
          · intro c' hc; cases hc
            intro Object Value Object' Value' I J obj known atoms sim atomsIn indsIn z
            have fm := fun y => fillerMeans I J obj known atoms sim
              (fun a inside => atomsIn a (by rw [classAtoms]; exact inside))
              (fun a inside => indsIn a (by rw [classIndividuals]; exact inside)) y
            rw [classDenote, classDenote]
            constructor
            · rintro ⟨y, _, holds⟩
              refine ⟨obj y, universal_relation sim role top _ _, ?_⟩
              rw [intersection_iff]
              simp only [AtLeastTwo.elements, new_val, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                forall_eq]
              refine ⟨(fm y).mp holds, ?_⟩
              rw [classDenote, classDenote]
              exact (sim.objects (obj y)).mpr ⟨y, rfl⟩
            · rintro ⟨y', _, holds⟩
              rw [intersection_iff] at holds
              simp only [AtLeastTwo.elements, new_val, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                forall_eq] at holds
              have notData : ¬ J.classes dataClass y' := by
                have := holds.2; rw [classDenote, classDenote] at this; exact this
              obtain ⟨y, rfl⟩ := (sim.objects y').mp notData
              exact ⟨y, universal_relation_left sim role top z y, (fm y).mpr holds.1⟩
        · have known' : RoleOf role ∈ context.roles.val := inContext.resolve_left top
          refine ⟨some (.ObjectSomeValuesFrom role f), by simp [roleRun, run, universal_correct, top], ?_⟩
          intro c' hc; cases hc
          intro Object Value Object' Value' I J obj known atoms sim atomsIn indsIn z
          have fm := fun y => fillerMeans I J obj known atoms sim
            (fun a inside => atomsIn a (by rw [classAtoms]; exact inside))
            (fun a inside => indsIn a (by rw [classIndividuals]; exact inside)) y
          rw [classDenote, classDenote]
          constructor
          · rintro ⟨y, related, holds⟩
            exact ⟨obj y, (relation_place sim role plain z y).mp related, (fm y).mp holds⟩
          · rintro ⟨y', related, holds⟩
            obtain ⟨y, rfl⟩ := successor_place sim role known' z y' related
            exact ⟨y, (relation_place sim role plain z y).mpr related, (fm y).mpr holds⟩
  | ObjectAllValuesFrom role filler =>
    rw [data_ontology.encode_class]
    have : sizeOf filler < sizeOf c := by rw [h]; simp
    obtain ⟨roleRes, roleRun, roleFacts⟩ := object_role_correct context role
    obtain ⟨res, run, means⟩ := encode_class_meaning context filler
    cases roleRes with
    | none => exact ⟨none, by simp [roleRun, run], by simp⟩
    | some copy =>
      obtain ⟨same, plain, inContext⟩ := roleFacts copy rfl
      subst copy
      cases res with
      | none => exact ⟨none, by simp [roleRun, run], by simp⟩
      | some f =>
        have fillerMeans : ClassMeans context filler f := means f rfl
        by_cases top : RoleOf role = topObject
        · refine ⟨some (.ObjectAllValuesFrom role (.ObjectUnionOf ⟨f, .Class dataClass,
            alloc.vec.Vec.new ClassExpression⟩)), ?_, ?_⟩
          · simp [roleRun, run, universal_correct, top, data_class_eq, data_ontology.or]
          · intro c' hc; cases hc
            intro Object Value Object' Value' I J obj known atoms sim atomsIn indsIn z
            have fm := fun y => fillerMeans I J obj known atoms sim
              (fun a inside => atomsIn a (by rw [classAtoms]; exact inside))
              (fun a inside => indsIn a (by rw [classIndividuals]; exact inside)) y
            rw [classDenote, classDenote]
            constructor
            · intro all y' _
              rw [union_iff]
              simp only [AtLeastTwo.elements, new_val, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
                exists_eq_left]
              by_cases dataNode : J.classes dataClass y'
              · exact .inr (by rw [classDenote]; exact dataNode)
              · obtain ⟨y, rfl⟩ := (sim.objects y').mp dataNode
                exact .inl ((fm y).mp (all y (universal_relation_left sim role top z y)))
            · intro all y _
              have := all (obj y) (universal_relation sim role top _ _)
              rw [union_iff] at this
              simp only [AtLeastTwo.elements, new_val, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
                exists_eq_left] at this
              rcases this with holds | dataNode
              · exact (fm y).mpr holds
              · rw [classDenote] at dataNode
                exact absurd dataNode ((sim.objects (obj y)).mpr ⟨y, rfl⟩)
        · have known' : RoleOf role ∈ context.roles.val := inContext.resolve_left top
          refine ⟨some (.ObjectAllValuesFrom role f), by simp [roleRun, run, universal_correct, top], ?_⟩
          intro c' hc; cases hc
          intro Object Value Object' Value' I J obj known atoms sim atomsIn indsIn z
          have fm := fun y => fillerMeans I J obj known atoms sim
            (fun a inside => atomsIn a (by rw [classAtoms]; exact inside))
            (fun a inside => indsIn a (by rw [classIndividuals]; exact inside)) y
          rw [classDenote, classDenote]
          constructor
          · intro all y' related
            obtain ⟨y, rfl⟩ := successor_place sim role known' z y' related
            exact (fm y).mp (all y ((relation_place sim role plain z y).mpr related))
          · intro all y related
            exact (fm y).mpr (all (obj y) ((relation_place sim role plain z y).mp related))
  | ObjectHasValue role a =>
    rw [data_ontology.encode_class]
    obtain ⟨roleRes, roleRun, roleFacts⟩ := object_role_correct context role
    obtain ⟨indRes, indRun, _⟩ := object_individual_of_correct a
    cases roleRes with
    | none => exact ⟨none, by simp [roleRun, indRun], by simp⟩
    | some copy =>
      obtain ⟨same, plain, _⟩ := roleFacts copy rfl
      subst copy
      cases indRes with
      | none => exact ⟨none, by simp [roleRun, indRun], by simp⟩
      | some b =>
        obtain ⟨rfl, _⟩ := object_individual_of_some indRun
        refine ⟨some (.ObjectHasValue role b), by simp [roleRun, indRun], ?_⟩
        intro c' hc; cases hc
        intro Object Value Object' Value' I J obj known atoms sim _ indsIn z
        rw [classDenote, classDenote, sim.individuals b (indsIn b (by rw [classIndividuals]; simp))]
        exact relation_place sim role plain z _
  | ObjectHasSelf role =>
    rw [data_ontology.encode_class]
    obtain ⟨roleRes, roleRun, roleFacts⟩ := object_role_correct context role
    cases roleRes with
    | none => exact ⟨none, by simp [roleRun], by simp⟩
    | some copy =>
      obtain ⟨same, plain, _⟩ := roleFacts copy rfl
      subst copy
      refine ⟨some (.ObjectHasSelf role), by simp [roleRun], ?_⟩
      intro c' hc; cases hc
      intro Object Value Object' Value' I J obj known atoms sim _ _ z
      rw [classDenote, classDenote]
      exact relation_place sim role plain z z
  | ObjectMinCardinality count role filler | ObjectMaxCardinality count role filler
  | ObjectExactCardinality count role filler =>
    rw [data_ontology.encode_class]
    have fillerSmall : ∀ f, filler = some f → sizeOf f < sizeOf c := by
      intro f hf; rw [h, hf]; simp; omega
    obtain ⟨counted, countedRun, countedFacts⟩ : ∃ res, data_ontology.encode_counted context role filler = .ok res ∧
        ∀ r f', res = some (r, f') → r = role ∧ ¬ Reserved (RoleOf role).iri.spelling.val ∧
          RoleOf role ∈ context.roles.val ∧ FillerMeans.{u,v,w,x} context filler f' := by
      rw [data_ontology.encode_counted, universal_correct]
      by_cases top : RoleOf role = topObject
      · exact ⟨none, by simp [top], by simp⟩
      · simp only [top, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
        obtain ⟨roleRes, roleRun, roleFacts⟩ := object_role_correct context role
        rw [roleRun, bind_ok]
        cases roleRes with
        | none => exact ⟨none, by simp, by simp⟩
        | some copy =>
          obtain ⟨same, plain, inContext⟩ := roleFacts copy rfl
          subst copy
          cases hf : filler with
          | none => exact ⟨some (role, none), by simp, fun r f' hr => by
              cases hr; exact ⟨rfl, plain, inContext.resolve_left top, trivial⟩⟩
          | some f =>
            have := fillerSmall f hf
            obtain ⟨res, run, means⟩ := encode_class_meaning context f
            cases res with
            | none => exact ⟨none, by simp [run], by simp⟩
            | some c' => exact ⟨some (role, some c'), by simp [run], fun r f' hr => by
                cases hr; exact ⟨rfl, plain, inContext.resolve_left top, means c' rfl⟩⟩
    cases counted with
    | none => exact ⟨none, by simp [countedRun], by simp⟩
    | some pair =>
      obtain ⟨r, f'⟩ := pair
      obtain ⟨same, plain, inContext, fillerMeans⟩ := countedFacts r f' rfl
      subst r
      have counting : ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
          (I : Interpretation Object Value) (J : Interpretation Object' Value') (obj : Object → Object')
          (known : Individual → Prop) (atoms : List (DataProperty × Option DataRange × Nat)),
          Simulates context I J obj known atoms → (∀ f, filler = some f → ∀ a ∈ classAtoms f, a ∈ atoms) →
          (∀ f, filler = some f → ∀ a ∈ classIndividuals f, known a) → ∀ n z,
          AtLeast n (fun y => objectRelation I role z y ∧ Rowl.Concepts.FillerHolds I filler y) ↔
            AtLeast n (fun y => objectRelation J role (obj z) y ∧ Rowl.Concepts.FillerHolds J f' y) := by
        intro Object Value Object' Value' I J obj known atoms sim atomsIn indsIn n z
        apply atLeast_image n _ _ obj sim.injective
        intro y'
        constructor
        · rintro ⟨related, holds⟩
          obtain ⟨y, rfl⟩ := successor_place sim role inContext z y' related
          exact ⟨y, rfl, (relation_place sim role plain z y).mpr related,
            (filler_place sim filler f' fillerMeans atomsIn indsIn y).mpr holds⟩
        · rintro ⟨y, rfl, related, holds⟩
          exact ⟨(relation_place sim role plain z y).mp related,
            (filler_place sim filler f' fillerMeans atomsIn indsIn y).mp holds⟩
      have atomsOf : ∀ (atoms : List (DataProperty × Option DataRange × Nat)), (∀ a ∈ classAtoms c, a ∈ atoms) →
          ∀ f, filler = some f → ∀ a ∈ classAtoms f, a ∈ atoms := by
        intro atoms atomsIn f hf a inside
        apply atomsIn a
        rw [h, hf]; rw [classAtoms]; exact inside
      have indsOf : ∀ (known : Individual → Prop), (∀ a ∈ classIndividuals c, known a) →
          ∀ f, filler = some f → ∀ a ∈ classIndividuals f, known a := by
        intro known indsIn f hf a inside
        apply indsIn a
        rw [h, hf]; rw [classIndividuals]; exact inside
      rw [h] at atomsOf indsOf
      first
      | refine ⟨some (.ObjectMinCardinality count role f'), by simp [countedRun, copy_natural_eq], ?_⟩
        intro c' hc; cases hc
        intro Object Value Object' Value' I J obj known atoms sim atomsIn indsIn z
        rw [classDenote, classDenote]
        exact counting I J obj known atoms sim (atomsOf atoms atomsIn) (indsOf known indsIn) _ z
      | refine ⟨some (.ObjectMaxCardinality count role f'), by simp [countedRun, copy_natural_eq], ?_⟩
        intro c' hc; cases hc
        intro Object Value Object' Value' I J obj known atoms sim atomsIn indsIn z
        simp only [classDenote, AtMost]
        exact not_congr (counting I J obj known atoms sim (atomsOf atoms atomsIn) (indsOf known indsIn) _ z)
      | refine ⟨some (.ObjectExactCardinality count role f'), by simp [countedRun, copy_natural_eq], ?_⟩
        intro c' hc; cases hc
        intro Object Value Object' Value' I J obj known atoms sim atomsIn indsIn z
        simp only [classDenote, Exactly, AtMost]
        exact and_congr (counting I J obj known atoms sim (atomsOf atoms atomsIn) (indsOf known indsIn) _ z)
          (not_congr (counting I J obj known atoms sim (atomsOf atoms atomsIn) (indsOf known indsIn) _ z))
  | DataSomeValuesFrom p range =>
    rw [data_ontology.encode_class]
    obtain ⟨roleRes, roleRun, _⟩ := data_role_correct context p
    obtain ⟨rangeRes, rangeRun, _⟩ := encode_range_meaning.{v,v,x,x} context range
    cases roleRes with
    | none => exact ⟨none, by simp [roleRun, rangeRun], by simp⟩
    | some role =>
      cases rangeRes with
      | none => exact ⟨none, by simp [roleRun, rangeRun], by simp⟩
      | some filler =>
        refine ⟨some (.ObjectSomeValuesFrom role filler), by simp [roleRun, rangeRun], ?_⟩
        intro c' hc; cases hc
        intro Object Value Object' Value' I J obj known atoms sim atomsIn _ z
        have atom := sim.data p (some range) 1 (atomsIn _ (by rw [classAtoms]; simp)) role (some filler) roleRun
          (encode_optional_some context range filler rangeRun) z
        rw [atLeast_one, atLeast_one] at atom
        rw [classDenote, classDenote]
        exact atom
  | DataAllValuesFrom p range =>
    rw [data_ontology.encode_class]
    obtain ⟨roleRes, roleRun, _⟩ := data_role_correct context p
    obtain ⟨rangeRes, rangeRun, _⟩ := encode_range_meaning.{v,v,x,x} context range
    cases roleRes with
    | none => exact ⟨none, by simp [roleRun, rangeRun], by simp⟩
    | some role =>
      cases rangeRes with
      | none => exact ⟨none, by simp [roleRun, rangeRun], by simp⟩
      | some filler =>
        refine ⟨some (.ObjectAllValuesFrom role filler), by simp [roleRun, rangeRun], ?_⟩
        intro c' hc; cases hc
        intro Object Value Object' Value' I J obj known atoms sim atomsIn _ z
        have atom := sim.data p (some (.Complement range)) 1 (atomsIn _ (by rw [classAtoms]; simp)) role
          (some (.ObjectComplementOf filler)) roleRun
          (encode_optional_some context _ _ (encode_complement context range filler rangeRun)) z
        rw [atLeast_one, atLeast_one] at atom
        rw [classDenote, classDenote]
        simp only [RangeHolds, Rowl.Concepts.FillerHolds, dataDenote, classDenote] at atom
        constructor
        · intro all y related
          by_contra outside
          obtain ⟨v, inside, notIn⟩ := atom.mpr ⟨y, related, outside⟩
          exact notIn (all v inside)
        · intro all v inside
          by_contra outside
          obtain ⟨y, related, notIn⟩ := atom.mp ⟨v, inside, outside⟩
          exact notIn (all y related)
  | DataHasValue p lt =>
    rw [data_ontology.encode_class]
    obtain ⟨roleRes, roleRun, _⟩ := data_role_correct context p
    obtain ⟨indRes, indRun, _⟩ := literal_individual_correct context lt
    cases roleRes with
    | none => exact ⟨none, by simp [roleRun, indRun], by simp⟩
    | some role =>
      cases indRes with
      | none => exact ⟨none, by simp [roleRun, indRun], by simp⟩
      | some a =>
        refine ⟨some (.ObjectHasValue role a), by simp [roleRun, indRun], ?_⟩
        intro c' hc; cases hc
        intro Object Value Object' Value' I J obj known atoms sim atomsIn _ z
        have atom := sim.data p (some (.OneOf ⟨lt, alloc.vec.Vec.new Literal⟩)) 1
          (atomsIn _ (by rw [classAtoms]; simp)) role (some (.ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩)) roleRun
          (encode_optional_some context _ _ (encode_single context lt a indRun)) z
        rw [atLeast_one, atLeast_one] at atom
        rw [classDenote, classDenote]
        simp only [RangeHolds, Rowl.Concepts.FillerHolds, dataDenote, classDenote, NonEmpty.elements, new_val,
          List.mem_cons, List.not_mem_nil, or_false, exists_eq_left] at atom
        constructor
        · intro related
          obtain ⟨y, related', same⟩ := atom.mp ⟨_, related, rfl⟩
          rw [same]; exact related'
        · intro related
          obtain ⟨v, related', same⟩ := atom.mpr ⟨_, related, rfl⟩
          rw [same]; exact related'
  | DataMinCardinality count p range =>
    rw [data_ontology.encode_class]
    obtain ⟨roleRes, roleRun, _⟩ := data_role_correct context p
    obtain ⟨fillerRes, fillerRun⟩ := encode_optional_range_ok context range
    rcases roleRes with _ | role
    · exact ⟨none, by simp [roleRun, fillerRun], by simp⟩
    rcases fillerRes with _ | filler
    · exact ⟨none, by simp [roleRun, fillerRun], by simp⟩
    refine ⟨some (.ObjectMinCardinality count role filler), by simp [roleRun, fillerRun, copy_natural_eq], ?_⟩
    intro c' hc; cases hc
    intro Object Value Object' Value' I J obj known atoms sim atomsIn _ z
    rw [classDenote, classDenote]
    exact sim.data p range (Rowl.Probes.naturalValue count) (atomsIn _ (by rw [classAtoms]; simp))
      role filler roleRun fillerRun z
  | DataMaxCardinality count p range =>
    rw [data_ontology.encode_class]
    obtain ⟨roleRes, roleRun, _⟩ := data_role_correct context p
    obtain ⟨fillerRes, fillerRun⟩ := encode_optional_range_ok context range
    rcases roleRes with _ | role
    · exact ⟨none, by simp [roleRun, fillerRun], by simp⟩
    rcases fillerRes with _ | filler
    · exact ⟨none, by simp [roleRun, fillerRun], by simp⟩
    refine ⟨some (.ObjectMaxCardinality count role filler), by simp [roleRun, fillerRun, copy_natural_eq], ?_⟩
    intro c' hc; cases hc
    intro Object Value Object' Value' I J obj known atoms sim atomsIn _ z
    simp only [classDenote, AtMost]
    exact not_congr (sim.data p range (Rowl.Probes.naturalValue count + 1) (atomsIn _ (by rw [classAtoms]; simp))
      role filler roleRun fillerRun z)
  | DataExactCardinality count p range =>
    rw [data_ontology.encode_class]
    obtain ⟨roleRes, roleRun, _⟩ := data_role_correct context p
    obtain ⟨fillerRes, fillerRun⟩ := encode_optional_range_ok context range
    rcases roleRes with _ | role
    · exact ⟨none, by simp [roleRun, fillerRun], by simp⟩
    rcases fillerRes with _ | filler
    · exact ⟨none, by simp [roleRun, fillerRun], by simp⟩
    refine ⟨some (.ObjectExactCardinality count role filler), by simp [roleRun, fillerRun, copy_natural_eq], ?_⟩
    intro c' hc; cases hc
    intro Object Value Object' Value' I J obj known atoms sim atomsIn _ z
    simp only [classDenote, Exactly, AtMost]
    exact and_congr (sim.data p range (Rowl.Probes.naturalValue count) (atomsIn _ (by rw [classAtoms]; simp))
      role filler roleRun fillerRun z)
      (not_congr (sim.data p range (Rowl.Probes.naturalValue count + 1) (atomsIn _ (by rw [classAtoms]; simp))
      role filler roleRun fillerRun z))
termination_by sizeOf c
decreasing_by all_goals (subst_vars; first | omega | (simp_wf; omega))

/-! ### Guarded class expressions -/

/-- What keeps the data nodes of `J` apart: no named class other than
    `owl:Thing` that is not the encoding's holds at a data node, the object
    properties of the context relate no data node, the data properties' roles
    leave no data node, and the known individuals are no data nodes. -/
structure Quiet (context : data_ontology.Context) (J : Interpretation Object' Value')
    (known : Individual → Prop) : Prop where
  classes : ∀ (c : Class) y, ¬ Reserved c.iri.spelling.val → c ≠ thing → J.classes dataClass y →
    ¬ J.classes c y
  roles : ∀ r ∈ context.roles.val, ∀ y y', J.objectProperties r y y' →
    ¬ J.classes dataClass y ∧ ¬ J.classes dataClass y'
  data : ∀ p role, data_ontology.data_role context p = .ok (some role) → ∀ y y', objectRelation J role y y' →
    ¬ J.classes dataClass y
  individuals : ∀ a, known a → ¬ J.classes dataClass (individual J a)

/-- What a guarded class expression's encoding means: it holds at no data node
    of an interpretation that keeps its data nodes apart. -/
def GuardMeans (context : data_ontology.Context) (c c' : ClassExpression) : Prop :=
  ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') (known : Individual → Prop),
    Quiet context J known → (∀ a ∈ classIndividuals c, known a) → ∀ y, J.classes dataClass y →
      ¬ classDenote J c' y

theorem quiet_relation {context : data_ontology.Context} {J : Interpretation Object' Value'}
    {known : Individual → Prop} (quiet : Quiet context J known) (role : ObjectPropertyExpression)
    (inContext : RoleOf role ∈ context.roles.val) (y y' : Object') (related : objectRelation J role y y') :
    ¬ J.classes dataClass y := by
  cases role with
  | Property r => exact (quiet.roles r inContext y y' related).1
  | Inverse r => exact (quiet.roles r inContext y' y related).2

theorem atLeast_some {α : Type u} {n : Nat} {P : α → Prop} (positive : 0 < n) (holds : AtLeast n P) :
    ∃ y, P y := by
  obtain ⟨f, _, each⟩ := holds
  exact ⟨f ⟨0, positive⟩, each _⟩

theorem positive_eq (count : probes.Natural) :
    data_ontology.positive count = .ok (decide (0 < Rowl.Probes.naturalValue count)) := by
  cases count <;> simp [data_ontology.positive, Rowl.Probes.naturalValue]

theorem any_guarded_spec (Q : ClassExpression → Prop) (classes : alloc.vec.Vec ClassExpression) (index : Usize)
    (each : ∀ e ∈ classes.val, ∃ b, data_ontology.guarded e = .ok b ∧ (b = true → Q e)) :
    ∃ b, data_ontology.any_guarded classes index = .ok b ∧
      (b = true → ∃ e ∈ classes.val.drop index.val, Q e) := by
  rw [data_ontology.any_guarded]
  by_cases inside : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨b, run, holds⟩ := each _ (List.getElem_mem inside)
    cases b with
    | true =>
      refine ⟨true, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], fun _ => ?_⟩
      exact ⟨_, by rw [split]; exact List.mem_cons_self, holds rfl⟩
    | false =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b', rest, restHolds⟩ := any_guarded_spec Q classes next each
      refine ⟨b', by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, rest],
        fun yes => ?_⟩
      obtain ⟨e, mem, q⟩ := restHolds yes
      rw [nextIndex] at mem
      exact ⟨e, by rw [split]; exact List.mem_cons_of_mem _ mem, q⟩
  · exact ⟨false, by simp [UScalar.lt_equiv, inside], by simp⟩
termination_by classes.val.length - index.val
decreasing_by omega

theorem all_guarded_spec (Q : ClassExpression → Prop) (classes : alloc.vec.Vec ClassExpression) (index : Usize)
    (each : ∀ e ∈ classes.val, ∃ b, data_ontology.guarded e = .ok b ∧ (b = true → Q e)) :
    ∃ b, data_ontology.all_guarded classes index = .ok b ∧
      (b = true → ∀ e ∈ classes.val.drop index.val, Q e) := by
  rw [data_ontology.all_guarded]
  by_cases inside : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨b, run, holds⟩ := each _ (List.getElem_mem inside)
    cases b with
    | false =>
      exact ⟨false, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
    | true =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b', rest, restHolds⟩ := all_guarded_spec Q classes next each
      refine ⟨b', by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, rest],
        fun yes e mem => ?_⟩
      rw [split] at mem
      rcases List.mem_cons.mp mem with rfl | later
      · exact holds rfl
      · exact restHolds yes e (by rw [nextIndex]; exact later)
  · exact ⟨true, by simp [UScalar.lt_equiv, inside], fun _ e mem => by
      simp [List.drop_eq_nil_iff.mpr (show classes.val.length ≤ index.val by omega)] at mem⟩
termination_by classes.val.length - index.val
decreasing_by omega

theorem encode_class_runs (context : data_ontology.Context) (c : ClassExpression) :
    ∃ res, data_ontology.encode_class context c = .ok res := by
  obtain ⟨res, run, _⟩ := encode_class_meaning.{0,0,0,0} context c
  exact ⟨res, run⟩

theorem encode_counted_some {context : data_ontology.Context} {role : ObjectPropertyExpression}
    {filler : Option ClassExpression} {r : ObjectPropertyExpression} {f' : Option ClassExpression}
    (run : data_ontology.encode_counted context role filler = .ok (some (r, f'))) :
    r = role ∧ RoleOf role ∈ context.roles.val := by
  rw [data_ontology.encode_counted, universal_correct] at run
  by_cases top : RoleOf role = topObject
  · simp [top] at run
  · simp only [top, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok] at run
    obtain ⟨roleRes, roleRun, roleFacts⟩ := object_role_correct context role
    rw [roleRun, bind_ok] at run
    cases roleRes with
    | none => simp at run
    | some copy =>
      obtain ⟨same, _, inContext⟩ := roleFacts copy rfl
      refine ⟨?_, inContext.resolve_left top⟩
      cases filler with
      | none =>
        simp only [Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at run
        rw [← run.1]; exact same
      | some f =>
        obtain ⟨res, encRun⟩ := encode_class_runs context f
        simp only [encRun, bind_ok] at run
        cases res with
        | none => simp at run
        | some _ =>
          simp only [Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at run
          rw [← run.1]; exact same

/-- The encoding of a guarded class expression holds at no data node of an
    interpretation that keeps its data nodes apart. -/
theorem guarded_meaning (context : data_ontology.Context) (c : ClassExpression) :
    ∃ b, data_ontology.guarded c = .ok b ∧
      (b = true → ∀ c', data_ontology.encode_class context c = .ok (some c') → GuardMeans.{w,x} context c c') := by
  have bound : ∀ (xs : AtLeastTwo ClassExpression), ∀ e ∈ xs.elements, sizeOf e < 1 + sizeOf xs := by
    intro xs e mem
    simp only [AtLeastTwo.elements, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · have := first_size xs; omega
    · have := second_size xs; omega
    · have := member_size xs e mem; omega
  have encoded : ∀ (xs : AtLeastTwo ClassExpression), ∃ res, data_ontology.encode_members context xs = .ok res ∧
      ∀ cs, res = some cs → List.Forall₂ (fun c e => data_ontology.encode_class context e = .ok (some c))
        cs.elements xs.elements := fun xs =>
    encode_members_spec context (fun e c => data_ontology.encode_class context e = .ok (some c)) xs
      (fun e _ => by
        obtain ⟨res, run⟩ := encode_class_runs context e
        exact ⟨res, run, fun c hc => by rw [run, hc]⟩)
  cases h : c with
  | Class k =>
    refine ⟨decide (k ≠ thing), by simp [data_ontology.guarded, is_thing_correct], ?_⟩
    by_cases reserved : Reserved k.iri.spelling.val
    · intro _ c' run
      rw [data_ontology.encode_class, reserved_correct] at run
      simp [reserved] at run
    · intro yes c' run
      rw [data_ontology.encode_class, reserved_correct] at run
      simp only [reserved, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok, Rowl.Nnf.copy_bytes_identity,
        class_named_correct, Option.some.injEq, Result.ok.injEq] at run
      subst run
      intro Object' Value' J known quiet _ y dataNode holds
      rw [classDenote] at holds
      exact quiet.classes k y reserved (by simpa using yes) dataNode holds
  | ObjectIntersectionOf xs =>
    obtain ⟨b1, run1, holds1⟩ := have := bound xs xs.first (by simp [AtLeastTwo.elements])
      guarded_meaning context xs.first
    obtain ⟨b2, run2, holds2⟩ := have := bound xs xs.second (by simp [AtLeastTwo.elements])
      guarded_meaning context xs.second
    obtain ⟨b3, run3, holds3⟩ := any_guarded_spec
      (fun e => ∀ c', data_ontology.encode_class context e = .ok (some c') → GuardMeans.{w,x} context e c')
      xs.rest 0#usize (fun e mem => by
        have := bound xs e (by simp [AtLeastTwo.elements, mem])
        exact guarded_meaning context e)
    refine ⟨b1 || b2 || b3, by rw [data_ontology.guarded]; cases b1 <;> cases b2 <;> simp [run1, run2, run3], ?_⟩
    intro yes c' run
    obtain ⟨res, encRun, pairs⟩ := encoded xs
    rw [data_ontology.encode_class, encRun] at run
    cases res with
    | none => simp at run
    | some cs =>
      simp only [bind_ok, Option.some.injEq, Result.ok.injEq] at run
      subst run
      have some_guarded : ∃ e ∈ xs.elements,
          ∀ c', data_ontology.encode_class context e = .ok (some c') → GuardMeans.{w,x} context e c' := by
        cases b1 with
        | true => exact ⟨xs.first, by simp [AtLeastTwo.elements], holds1 rfl⟩
        | false =>
          cases b2 with
          | true => exact ⟨xs.second, by simp [AtLeastTwo.elements], holds2 rfl⟩
          | false =>
            obtain ⟨e, mem, q⟩ := holds3 (by simpa using yes)
            have mem' : e ∈ xs.rest.val := by simpa [zero_val] using mem
            exact ⟨e, by simp [AtLeastTwo.elements, mem'], q⟩
      obtain ⟨e, mem, guard⟩ := some_guarded
      obtain ⟨ce, memC, encE⟩ := forall2_mem_right (pairs cs rfl) e mem
      intro Object' Value' J known quiet indsIn y dataNode holds
      rw [intersection_iff] at holds
      exact guard ce encE J known quiet (fun a inside => indsIn a (class_individuals_members xs e mem a inside).1)
        y dataNode (holds ce memC)
  | ObjectUnionOf xs =>
    obtain ⟨b1, run1, holds1⟩ := have := bound xs xs.first (by simp [AtLeastTwo.elements])
      guarded_meaning context xs.first
    obtain ⟨b2, run2, holds2⟩ := have := bound xs xs.second (by simp [AtLeastTwo.elements])
      guarded_meaning context xs.second
    obtain ⟨b3, run3, holds3⟩ := all_guarded_spec
      (fun e => ∀ c', data_ontology.encode_class context e = .ok (some c') → GuardMeans.{w,x} context e c')
      xs.rest 0#usize (fun e mem => by
        have := bound xs e (by simp [AtLeastTwo.elements, mem])
        exact guarded_meaning context e)
    refine ⟨b1 && b2 && b3, by rw [data_ontology.guarded]; cases b1 <;> cases b2 <;> simp [run1, run2, run3], ?_⟩
    intro yes c' run
    obtain ⟨res, encRun, pairs⟩ := encoded xs
    rw [data_ontology.encode_class, encRun] at run
    cases res with
    | none => simp at run
    | some cs =>
      simp only [bind_ok, Option.some.injEq, Result.ok.injEq] at run
      subst run
      simp only [Bool.and_eq_true] at yes
      obtain ⟨⟨yes1, yes2⟩, yes3⟩ := yes
      have all_guarded : ∀ e ∈ xs.elements,
          ∀ c', data_ontology.encode_class context e = .ok (some c') → GuardMeans.{w,x} context e c' := by
        intro e mem
        simp only [AtLeastTwo.elements, List.mem_cons] at mem
        rcases mem with rfl | rfl | mem
        · exact holds1 yes1
        · exact holds2 yes2
        · exact holds3 yes3 e (by simpa [zero_val] using mem)
      intro Object' Value' J known quiet indsIn y dataNode holds
      rw [union_iff] at holds
      obtain ⟨ce, memC, holdsC⟩ := holds
      obtain ⟨e, mem, encE⟩ := forall2_mem_left (pairs cs rfl) ce memC
      exact all_guarded e mem ce encE J known quiet
        (fun a inside => indsIn a (class_individuals_members xs e mem a inside).2) y dataNode holdsC
  | ObjectComplementOf _ => exact ⟨false, by simp [data_ontology.guarded], by simp⟩
  | ObjectOneOf xs =>
    refine ⟨true, by simp [data_ontology.guarded], fun _ c' run => ?_⟩
    rw [data_ontology.encode_class] at run
    obtain ⟨first, firstRun, _⟩ := object_individual_of_correct xs.first
    cases first with
    | none => simp [firstRun] at run
    | some a =>
      have firstSame := object_individual_of_some firstRun
      obtain ⟨rest, restRun, restFacts⟩ := individuals_from_correct xs.rest 0#usize
        (alloc.vec.Vec.new Individual) (by simp [new_val])
      cases rest with
      | none => simp [firstRun, restRun] at run
      | some others =>
        obtain ⟨othersSame, _⟩ := restFacts others rfl
        simp only [new_val, List.nil_append, zero_val, List.drop_zero] at othersSame
        have same : (⟨a, others⟩ : NonEmpty Individual) = xs := by
          cases xs; simp only [NonEmpty.mk.injEq]
          exact ⟨firstSame.1, by simpa [alloc.vec.Vec.eq_iff] using othersSame⟩
        simp only [firstRun, restRun, bind_ok, Option.some.injEq, Result.ok.injEq] at run
        subst run
        intro Object' Value' J known quiet indsIn y dataNode holds
        rw [same, classDenote] at holds
        obtain ⟨b, member, rfl⟩ := holds
        exact quiet.individuals b (indsIn b (by rw [classIndividuals]; exact member)) dataNode
  | ObjectSomeValuesFrom role filler =>
    refine ⟨decide (RoleOf role ≠ topObject), by simp [data_ontology.guarded, universal_correct], ?_⟩
    intro yes c' run
    have top : RoleOf role ≠ topObject := by simpa using yes
    rw [data_ontology.encode_class] at run
    obtain ⟨roleRes, roleRun, roleFacts⟩ := object_role_correct context role
    obtain ⟨res, encRun⟩ := encode_class_runs context filler
    cases roleRes with
    | none => simp [roleRun, encRun] at run
    | some copy =>
      obtain ⟨same, _, inContext⟩ := roleFacts copy rfl
      subst copy
      cases res with
      | none => simp [roleRun, encRun] at run
      | some f =>
        simp only [roleRun, encRun, bind_ok, universal_correct, top, decide_false, Bool.false_eq_true,
          ↓reduceIte, Option.some.injEq, Result.ok.injEq] at run
        subst run
        intro Object' Value' J known quiet _ y dataNode holds
        rw [classDenote] at holds
        obtain ⟨y', related, _⟩ := holds
        exact quiet_relation quiet role (inContext.resolve_left top) y y' related dataNode
  | ObjectAllValuesFrom _ _ => exact ⟨false, by simp [data_ontology.guarded], by simp⟩
  | ObjectHasValue role a =>
    refine ⟨decide (RoleOf role ≠ topObject), by simp [data_ontology.guarded, universal_correct], ?_⟩
    intro yes c' run
    have top : RoleOf role ≠ topObject := by simpa using yes
    rw [data_ontology.encode_class] at run
    obtain ⟨roleRes, roleRun, roleFacts⟩ := object_role_correct context role
    obtain ⟨indRes, indRun, _⟩ := object_individual_of_correct a
    cases roleRes with
    | none => simp [roleRun, indRun] at run
    | some copy =>
      obtain ⟨same, _, inContext⟩ := roleFacts copy rfl
      subst copy
      cases indRes with
      | none => simp [roleRun, indRun] at run
      | some b =>
        simp only [roleRun, indRun, bind_ok, Option.some.injEq, Result.ok.injEq] at run
        subst run
        intro Object' Value' J known quiet _ y dataNode holds
        rw [classDenote] at holds
        exact quiet_relation quiet role (inContext.resolve_left top) y _ holds dataNode
  | ObjectHasSelf role =>
    refine ⟨decide (RoleOf role ≠ topObject), by simp [data_ontology.guarded, universal_correct], ?_⟩
    intro yes c' run
    have top : RoleOf role ≠ topObject := by simpa using yes
    rw [data_ontology.encode_class] at run
    obtain ⟨roleRes, roleRun, roleFacts⟩ := object_role_correct context role
    cases roleRes with
    | none => simp [roleRun] at run
    | some copy =>
      obtain ⟨same, _, inContext⟩ := roleFacts copy rfl
      subst copy
      simp only [roleRun, bind_ok, Option.some.injEq, Result.ok.injEq] at run
      subst run
      intro Object' Value' J known quiet _ y dataNode holds
      rw [classDenote] at holds
      exact quiet_relation quiet role (inContext.resolve_left top) y y holds dataNode
  | ObjectMinCardinality count role filler =>
    refine ⟨decide (0 < Rowl.Probes.naturalValue count) && decide (RoleOf role ≠ topObject), ?_, ?_⟩
    · rw [data_ontology.guarded, positive_eq]
      by_cases positive : 0 < Rowl.Probes.naturalValue count <;> simp [positive, universal_correct]
    intro yes c' run
    simp only [Bool.and_eq_true, decide_eq_true_eq] at yes
    rw [data_ontology.encode_class] at run
    obtain ⟨counted, countedRun⟩ : ∃ res, data_ontology.encode_counted context role filler = .ok res := by
      rw [data_ontology.encode_counted, universal_correct]
      simp only [yes.2, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
      obtain ⟨roleRes, roleRun, _⟩ := object_role_correct context role
      rw [roleRun, bind_ok]
      cases roleRes with
      | none => exact ⟨none, rfl⟩
      | some copy =>
        cases filler with
        | none => exact ⟨_, rfl⟩
        | some f =>
          obtain ⟨res, encRun⟩ := encode_class_runs context f
          cases res with
          | none => exact ⟨none, by simp [encRun]⟩
          | some v => exact ⟨some (copy, some v), by simp [encRun]⟩
    cases counted with
    | none => simp [countedRun] at run
    | some pair =>
      obtain ⟨r, f'⟩ := pair
      obtain ⟨rfl, inContext⟩ := encode_counted_some countedRun
      simp [countedRun, copy_natural_eq] at run
      subst run
      intro Object' Value' J known quiet _ y dataNode holds
      rw [classDenote] at holds
      obtain ⟨y', related, _⟩ := atLeast_some yes.1 holds
      exact quiet_relation quiet r inContext y y' related dataNode
  | ObjectMaxCardinality _ _ _ => exact ⟨false, by simp [data_ontology.guarded], by simp⟩
  | ObjectExactCardinality count role filler =>
    refine ⟨decide (0 < Rowl.Probes.naturalValue count) && decide (RoleOf role ≠ topObject), ?_, ?_⟩
    · rw [data_ontology.guarded, positive_eq]
      by_cases positive : 0 < Rowl.Probes.naturalValue count <;> simp [positive, universal_correct]
    intro yes c' run
    simp only [Bool.and_eq_true, decide_eq_true_eq] at yes
    rw [data_ontology.encode_class] at run
    obtain ⟨counted, countedRun⟩ : ∃ res, data_ontology.encode_counted context role filler = .ok res := by
      rw [data_ontology.encode_counted, universal_correct]
      simp only [yes.2, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
      obtain ⟨roleRes, roleRun, _⟩ := object_role_correct context role
      rw [roleRun, bind_ok]
      cases roleRes with
      | none => exact ⟨none, rfl⟩
      | some copy =>
        cases filler with
        | none => exact ⟨_, rfl⟩
        | some f =>
          obtain ⟨res, encRun⟩ := encode_class_runs context f
          cases res with
          | none => exact ⟨none, by simp [encRun]⟩
          | some v => exact ⟨some (copy, some v), by simp [encRun]⟩
    cases counted with
    | none => simp [countedRun] at run
    | some pair =>
      obtain ⟨r, f'⟩ := pair
      obtain ⟨rfl, inContext⟩ := encode_counted_some countedRun
      simp [countedRun, copy_natural_eq] at run
      subst run
      intro Object' Value' J known quiet _ y dataNode holds
      rw [classDenote] at holds
      obtain ⟨y', related, _⟩ := atLeast_some yes.1 holds.1
      exact quiet_relation quiet r inContext y y' related dataNode
  | DataSomeValuesFrom p range =>
    refine ⟨true, by simp [data_ontology.guarded], fun _ c' run => ?_⟩
    rw [data_ontology.encode_class] at run
    obtain ⟨roleRes, roleRun, _⟩ := data_role_correct context p
    obtain ⟨rangeRes, rangeRun, _⟩ := encode_range_meaning.{0,0,0,0} context range
    cases roleRes with
    | none => simp [roleRun, rangeRun] at run
    | some role =>
      cases rangeRes with
      | none => simp [roleRun, rangeRun] at run
      | some filler =>
        simp only [roleRun, rangeRun, bind_ok, Option.some.injEq, Result.ok.injEq] at run
        subst run
        intro Object' Value' J known quiet _ y dataNode holds
        rw [classDenote] at holds
        obtain ⟨y', related, _⟩ := holds
        exact quiet.data p role roleRun y y' related dataNode
  | DataAllValuesFrom _ _ => exact ⟨false, by simp [data_ontology.guarded], by simp⟩
  | DataHasValue p lt =>
    refine ⟨true, by simp [data_ontology.guarded], fun _ c' run => ?_⟩
    rw [data_ontology.encode_class] at run
    obtain ⟨roleRes, roleRun, _⟩ := data_role_correct context p
    obtain ⟨indRes, indRun, _⟩ := literal_individual_correct context lt
    cases roleRes with
    | none => simp [roleRun, indRun] at run
    | some role =>
      cases indRes with
      | none => simp [roleRun, indRun] at run
      | some a =>
        simp only [roleRun, indRun, bind_ok, Option.some.injEq, Result.ok.injEq] at run
        subst run
        intro Object' Value' J known quiet _ y dataNode holds
        rw [classDenote] at holds
        exact quiet.data p role roleRun y _ holds dataNode
  | DataMinCardinality count p range =>
    refine ⟨decide (0 < Rowl.Probes.naturalValue count), by simp [data_ontology.guarded, positive_eq], ?_⟩
    intro yes c' run
    simp only [decide_eq_true_eq] at yes
    rw [data_ontology.encode_class] at run
    obtain ⟨roleRes, roleRun, _⟩ := data_role_correct context p
    obtain ⟨fillerRes, fillerRun⟩ := encode_optional_range_ok context range
    cases roleRes with
    | none => simp [roleRun, fillerRun] at run
    | some role =>
      cases fillerRes with
      | none => simp [roleRun, fillerRun] at run
      | some filler =>
        simp only [roleRun, fillerRun, copy_natural_eq, bind_ok, Option.some.injEq, Result.ok.injEq] at run
        subst run
        intro Object' Value' J known quiet _ y dataNode holds
        rw [classDenote] at holds
        obtain ⟨y', related, _⟩ := atLeast_some yes holds
        exact quiet.data p role roleRun y y' related dataNode
  | DataMaxCardinality _ _ _ => exact ⟨false, by simp [data_ontology.guarded], by simp⟩
  | DataExactCardinality count p range =>
    refine ⟨decide (0 < Rowl.Probes.naturalValue count), by simp [data_ontology.guarded, positive_eq], ?_⟩
    intro yes c' run
    simp only [decide_eq_true_eq] at yes
    rw [data_ontology.encode_class] at run
    obtain ⟨roleRes, roleRun, _⟩ := data_role_correct context p
    obtain ⟨fillerRes, fillerRun⟩ := encode_optional_range_ok context range
    cases roleRes with
    | none => simp [roleRun, fillerRun] at run
    | some role =>
      cases fillerRes with
      | none => simp [roleRun, fillerRun] at run
      | some filler =>
        simp only [roleRun, fillerRun, copy_natural_eq, bind_ok, Option.some.injEq, Result.ok.injEq] at run
        subst run
        intro Object' Value' J known quiet _ y dataNode holds
        rw [classDenote] at holds
        obtain ⟨y', related, _⟩ := atLeast_some yes holds.1
        exact quiet.data p role roleRun y y' related dataNode
termination_by sizeOf c
decreasing_by all_goals (subst_vars; first | omega | (simp_wf; omega))

end Rowl.DataMeaning
