import Rowl.DataEncoding

/-!
What the encoding of `data_ontology` means. A data range's encoding holds at a
data node exactly when the range holds of a value that the node stands for
(`encode_range_meaning`): the same datatypes in use, a literal individual
exactly for its literal's value, and, when numbers are ordered, each cut's
class exactly at the reals in the cut (`NodeValue`), so that the subtypes of
`xsd:integer` and the range facets hold as their cuts say (`kind_range_meaning`,
`facet_class_meaning`); a range facet on `xsd:double` or `xsd:float` holds as
the edges of its format say (`binary_facet_class_meaning`), and one with a
time instant as bound as the time cuts of the two time lines say, with and
without a time zone, fourteen hours apart (`time_facet_class_meaning`). A class expression's encoding holds at an
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
open Rowl.Floats (CanonicalBinary binaryOf fmt)
open Rowl.FloatOrder (position FacetHolds)
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

/-- `x` is the value of the canonical kernel value `b` of a floating-point
    format. -/
def FloatAt {Value : Type v} (lit : datatypes.DataValue → Value) (double : Bool) (x : Value)
    (b : datatypes.Binary) : Prop :=
  CanonicalBinary b ∧ (binaryOf b).Valid (fmt double) ∧ x = lit (floatLit double b)

/-- `x` is the value of the time instant `m`, with `mom` the time instants
    among the values. -/
def MomentAt {Value : Type v} (mom : Rowl.DatatypeMap.Moment → Value) (x : Value) (m : Rowl.DatatypeMap.Moment) :
    Prop :=
  m.Valid ∧ x = mom m

/-- Whether a time instant is on the side of a range facet of a bound in the
    order of XML Schema. -/
def MomentFacetHolds : datatypes.Facet → Rowl.DatatypeMap.Moment → Rowl.DatatypeMap.Moment → Prop
  | .MinInclusive, b, y => b.Le y
  | .MaxInclusive, b, y => y.Le b
  | .MinExclusive, b, y => b.Lt y
  | .MaxExclusive, b, y => y.Lt b

/-- A time instant in a time cut: after the cut's instant on the time line, or
    at it when the cut is not open. -/
def InTimeCut (cut : data_ontology.TimeCut) (m : Rowl.DatatypeMap.Moment) : Prop :=
  (Rowl.Moments.momentOf cut.instant).key < m.key ∨
    ((Rowl.Moments.momentOf cut.instant).key = m.key ∧ cut.open = false)

/-- What the encoding of a data range needs of a data node `d` of `J` that
    stands for a value `x` of `I`: the same datatypes in use, a literal
    individual exactly at the node of its literal's value, when numbers are
    ordered, each cut's class exactly at the nodes of numbers in the cut, with
    `num` the reals among the values of `I`, at a node of a value of a
    floating-point format, each edge's class of the format exactly when the
    value's place is at or above the edge, and, at a node of a time instant,
    with `mom` the time instants among the values of `I`, each class of a time
    cut of its line exactly when the instant is in the cut; the time cuts of the
    context are at kernel instants. -/
structure NodeValue (context : data_ontology.Context) (I : Interpretation Object Value)
    (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value) (num : ℝ → Value)
    (mom : Rowl.DatatypeMap.Moment → Value) (d : Object') (x : Value) : Prop where
  kinds : ∀ k, Used context.kinds k = true → (J.classes (kindClass k) d ↔ I.datatypes (typeOf k) x)
  values : ∀ (i : Usize) (h : i.val < context.values.val.length),
    J.namedIndividuals (valueIndividual i) = d ↔ x = lit context.values.val[i.val]
  cuts : context.kinds.ordered = true → ∀ (i : Usize) (h : i.val < context.cuts.val.length),
    (J.classes (cutClass i) d ↔ ∃ r, x = num r ∧ Rowl.Regions.InCut context.cuts.val[i.val] r)
  edges : ∀ (double : Bool) (b : datatypes.Binary), FloatAt lit double x b →
    ∀ (i : Usize) (h : i.val < (edgesOf context double).val.length),
      (J.classes (edgeClass double i) d ↔ (edgesOf context double).val[i.val].val ≤ position (fmt double) (binaryOf b))
  goodTimes : GoodTimes context.times.val ∧ (context.times.val ≠ [] → context.kinds.stamp = true)
  times : ∀ (m : Rowl.DatatypeMap.Moment), MomentAt mom x m → ∀ (i : Usize) (h : i.val < context.times.val.length),
    context.times.val[i.val].zoned = m.zone.isSome →
      (J.classes (timeClass i) d ↔ InTimeCut context.times.val[i.val] m)

/-- What every data range needs of the two interpretations: `rdfs:Literal` and
    `owl:Thing` hold everywhere, each literal with a value is that value, the
    reals `num` are values one to one, every number is the real it writes, the
    numeric datatypes are the reals of their value spaces, a range facet with a
    numeric bound holds of the reals on its side of the bound, the values of
    `xsd:double` and `xsd:float` are their canonical kernel values, with their
    facets in the order of XML Schema, the time instants `mom` are values one to
    one and apart from the numbers, `xsd:dateTime` holds of them and
    `xsd:dateTimeStamp` of those with a time zone, a literal time instant is its
    moment's value, and a range facet with a time instant as bound holds of the
    time instants on its side of the bound in the order of XML Schema. -/
structure RangeFrame (I : Interpretation Object Value) (J : Interpretation Object' Value')
    (lit : datatypes.DataValue → Value) (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value) : Prop where
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
  binaries : ∀ (double : Bool) (x : Value), I.datatypes (typeOf (floatKind double)) x ↔ ∃ b, FloatAt lit double x b
  binaryFacets : ∀ (f : FacetRestriction) (F : datatypes.Facet) (double : Bool) (b : datatypes.Binary),
    Rowl.Datatypes.facetOf f.facet = some F → datatypes.literal_value f.value = .ok (some (floatLit double b)) →
    ∀ x, I.facets f x ↔ ∃ y, FloatAt lit double x y ∧ FacetHolds F (binaryOf b) (binaryOf y)
  binaryReal : ∀ (double : Bool) (b : datatypes.Binary) (x : Value) (r : ℝ), FloatAt lit double x b → x ≠ num r
  binaryApart : ∀ (b b' : datatypes.Binary) (x : Value), FloatAt lit true x b → ¬ FloatAt lit false x b'
  binaryInjective : ∀ (double : Bool) (b b' : datatypes.Binary) (x : Value), FloatAt lit double x b →
    FloatAt lit double x b' → b = b'
  moments : ∀ x, I.datatypes (typeOf .DateTime) x ↔ ∃ m, MomentAt mom x m
  stamps : ∀ x, I.datatypes (typeOf .DateTimeStamp) x ↔ ∃ m, MomentAt mom x m ∧ m.zone.isSome = true
  momentLits : ∀ y, Rowl.Moments.CanonicalMoment y → lit (.Moment y) = mom (Rowl.Moments.momentOf y)
  momentFacets : ∀ (f : FacetRestriction) (F : datatypes.Facet) (b : datatypes.Moment),
    Rowl.Datatypes.facetOf f.facet = some F → datatypes.literal_value f.value = .ok (some (.Moment b)) →
    ∀ x, I.facets f x ↔ ∃ m, MomentAt mom x m ∧ MomentFacetHolds F (Rowl.Moments.momentOf b) m
  momentReal : ∀ (m : Rowl.DatatypeMap.Moment) (x : Value) (r : ℝ), MomentAt mom x m → x ≠ num r
  momentBinary : ∀ (m : Rowl.DatatypeMap.Moment) (double : Bool) (b : datatypes.Binary) (x : Value),
    MomentAt mom x m → ¬ FloatAt lit double x b
  momentInjective : ∀ (m m' : Rowl.DatatypeMap.Moment) (x : Value), MomentAt mom x m → MomentAt mom x m' → m = m'

/-- What a data range's encoding means: at every data node standing for a
    value, it holds exactly when the range holds of the value. -/
def RangeMeans (context : data_ontology.Context) (range : DataRange) (c : ClassExpression) : Prop :=
  ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
    (I : Interpretation Object Value) (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value)
    (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value), RangeFrame I J lit num mom → ∀ d x, NodeValue context I J lit num mom d x →
      (dataDenote I range x ↔ classDenote J c d)

theorem literal_individual_meaning (context : data_ontology.Context) (lt : Literal) (a : Individual)
    (run : data_ontology.literal_individual context lt = .ok (some a))
    {I : Interpretation Object Value} {J : Interpretation Object' Value'} {lit : datatypes.DataValue → Value}
    {num : ℝ → Value} {mom : Rowl.DatatypeMap.Moment → Value} (frame : RangeFrame I J lit num mom) {d : Object'} {x : Value}
    (node : NodeValue context I J lit num mom d x) :
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
    {J : Interpretation Object' Value'} {lit : datatypes.DataValue → Value} {num : ℝ → Value} {mom : Rowl.DatatypeMap.Moment → Value}
    {d : Object'} {x : Value} (node : NodeValue context I J lit num mom d x)
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
        (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value), RangeFrame I J lit num mom → ∀ d x, NodeValue context I J lit num mom d x →
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
          intro Object Value Object' Value' I J lit num mom frame d x node
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
      intro Object Value Object' Value' I J lit num mom frame d x node
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

theorem nothing_eq : data_ontology.nothing = .ok (.ObjectComplementOf (.Class thing)) := by
  simp [data_ontology.nothing, thing_eq, data_ontology.not]

theorem edge_index_correct (edges : alloc.vec.Vec U128) (edge : U128) (index : Usize) :
    ∃ res, data_ontology.edge_index edges edge index = .ok res ∧
      ∀ i, res = some i → ∃ h : i.val < edges.val.length, edges.val[i.val] = edge := by
  rw [data_ontology.edge_index]
  by_cases inside : index.val < edges.val.length
  · have lookup : edges.index_usize index = .ok edges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases same : edges.val[index.val] = edge
    · exact ⟨some index, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, same],
        fun i h => by cases h; exact ⟨inside, same⟩⟩
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨res, run, facts⟩ := edge_index_correct edges edge next
      exact ⟨res, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, same, advance, run],
        facts⟩
  · exact ⟨none, by simp [UScalar.lt_equiv, inside], by simp⟩
termination_by edges.val.length - index.val
decreasing_by omega

theorem edges_run (context : data_ontology.Context) (double : Bool) :
    (if double = true then ok context.double_edges else ok context.float_edges : Result (alloc.vec.Vec U128)) =
      ok (edgesOf context double) := by
  cases double <;> rfl

/-- The class of an edge of the context at a place, when there is one. -/
theorem at_edge_correct (context : data_ontology.Context) (double : Bool) (edge : U128) :
    ∃ res, data_ontology.at_edge context double edge = .ok res ∧ ∀ c, res = some c →
      ∃ (i : Usize) (h : i.val < (edgesOf context double).val.length),
        (edgesOf context double).val[i.val] = edge ∧ c = .Class (edgeClass double i) := by
  obtain ⟨res, run, facts⟩ := edge_index_correct (edgesOf context double) edge 0#usize
  cases res with
  | none => exact ⟨none, by simp [data_ontology.at_edge, edges_run, run], by simp⟩
  | some i =>
    obtain ⟨h, at_i⟩ := facts i rfl
    exact ⟨some (.Class (edgeClass double i)), by simp [data_ontology.at_edge, edges_run, run, edge_class_eq],
      fun c hc => ⟨i, h, at_i, by cases hc; rfl⟩⟩

/-- The class of the values from one edge on and before another. -/
theorem between_edges_correct (context : data_ontology.Context) (double : Bool) (low high : U128) :
    ∃ res, data_ontology.between_edges context double low high = .ok res ∧ ∀ c, res = some c →
      ∃ (i j : Usize) (hi : i.val < (edgesOf context double).val.length)
        (hj : j.val < (edgesOf context double).val.length),
        (edgesOf context double).val[i.val] = low ∧ (edgesOf context double).val[j.val] = high ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') d,
          classDenote J c d ↔ J.classes (edgeClass double i) d ∧ ¬ J.classes (edgeClass double j) d := by
  obtain ⟨r1, run1, f1⟩ := at_edge_correct context double low
  obtain ⟨r2, run2, f2⟩ := at_edge_correct context double high
  cases r1 with
  | none => exact ⟨none, by simp [data_ontology.between_edges, run1, run2], by simp⟩
  | some c1 =>
    cases r2 with
    | none => exact ⟨none, by simp [data_ontology.between_edges, run1, run2], by simp⟩
    | some c2 =>
      obtain ⟨i, hi, at_i, rfl⟩ := f1 c1 rfl
      obtain ⟨j, hj, at_j, rfl⟩ := f2 c2 rfl
      refine ⟨some (.ObjectIntersectionOf ⟨.Class (edgeClass double i),
        .ObjectComplementOf (.Class (edgeClass double j)), alloc.vec.Vec.new ClassExpression⟩),
        by simp [data_ontology.between_edges, run1, run2, data_ontology.not, data_ontology.and], fun c hc => ?_⟩
      cases hc
      refine ⟨i, j, hi, hj, at_i, at_j, fun J d => ?_⟩
      rw [inter_iff]
      simp [AtLeastTwo.elements, classDenote, new_val]

/-- The class of a range facet with a floating-point bound of the format holds
    at a data node standing for a value of the format exactly when the facet
    holds of the value. -/
theorem binary_facet_class_meaning (context : data_ontology.Context) (double : Bool) (F : datatypes.Facet)
    (bound : datatypes.Binary) (cb : CanonicalBinary bound) (vb : (binaryOf bound).Valid (fmt double)) :
    ∃ res, data_ontology.binary_facet_class context double F bound = .ok res ∧ ∀ c, res = some c →
      ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
        (I : Interpretation Object Value) (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value)
        (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value), RangeFrame I J lit num mom → ∀ d x, NodeValue context I J lit num mom d x →
          ∀ y, FloatAt lit double x y → (FacetHolds F (binaryOf bound) (binaryOf y) ↔ classDenote J c d) := by
  have pf := Rowl.FloatOrder.proper_fmt double
  rw [data_ontology.binary_facet_class, Rowl.FloatOrder.is_nan_spec]
  by_cases nan : binaryOf bound = .nan
  · refine ⟨some (.ObjectComplementOf (.Class thing)), by simp [nan, nothing_eq], fun c hc => ?_⟩
    cases hc
    intro Object Value Object' Value' I J lit num mom frame d x node y hy
    have := (Rowl.FloatOrder.facet_holds_iff pf F vb hy.2.1).not
    simp only [classDenote, frame.thing d, not_true_eq_false, iff_false]
    intro holds
    exact (Rowl.FloatOrder.facet_holds_iff pf F vb hy.2.1).mp holds |>.1 nan
  · obtain ⟨low, lowRun, lowVal⟩ := Rowl.FloatOrder.low_position_spec bound double cb vb
    obtain ⟨high, highRun, highVal⟩ := Rowl.FloatOrder.high_position_spec bound double cb vb
    have small := Rowl.FloatOrder.top_small double
    have highLe : high.val ≤ 2 * Rowl.FloatOrder.topPlace (fmt double) + 2 := by
      rw [highVal]
      obtain ⟨_, h, _, _, _, _⟩ := Rowl.FloatOrder.places_of pf vb nan
      have : (Rowl.FloatOrder.highPosition (fmt double) (binaryOf bound) : ℤ) ≤
          2 * Rowl.FloatOrder.topPlace (fmt double) + 2 := by
        rw [h]; unfold Rowl.FloatOrder.highOf; split_ifs <;> omega
      omega
    obtain ⟨h1, h1Run, h1Val⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := high) (y := 1#u128) (by simp [UScalar.max, U128.max_eq]; omega))
    have h1Is : h1.val = Rowl.FloatOrder.highPosition (fmt double) (binaryOf bound) + 1 := by
      rw [h1Val, highVal]; simp
    -- the class of the edge at a place, at the node of a value of the format
    have edgeMeans : ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
        {I : Interpretation Object Value} {J : Interpretation Object' Value'} {lit : datatypes.DataValue → Value}
        {num : ℝ → Value} {mom : Rowl.DatatypeMap.Moment → Value}, RangeFrame I J lit num mom → ∀ {d x}, NodeValue context I J lit num mom d x →
        ∀ {y}, FloatAt lit double x y → ∀ (i : Usize) (hi : i.val < (edgesOf context double).val.length),
          J.classes (edgeClass double i) d ↔ (edgesOf context double).val[i.val].val ≤ position (fmt double) (binaryOf y) := by
      intro Object Value Object' Value' I J lit num mom frame d x node y hy i hi
      exact node.edges double y hy i hi
    have holds : ∀ y, (binaryOf y).Valid (fmt double) → (FacetHolds F (binaryOf bound) (binaryOf y) ↔
        Rowl.FloatOrder.FacetPlaces (fmt double) F (binaryOf bound) (position (fmt double) (binaryOf y))) := by
      intro y vy
      rw [Rowl.FloatOrder.facet_holds_iff pf F vb vy]
      simp [nan]
    cases F with
    | MinInclusive =>
      obtain ⟨res, run, facts⟩ := at_edge_correct context double low
      refine ⟨res, by simp [nan, lowRun, highRun, run], fun c hc => ?_⟩
      obtain ⟨i, hi, at_i, rfl⟩ := facts c hc
      intro Object Value Object' Value' I J lit num mom frame d x node y hy
      rw [holds y hy.2.1, classDenote, edgeMeans frame node hy i hi, at_i, lowVal]
      rfl
    | MinExclusive =>
      obtain ⟨res, run, facts⟩ := at_edge_correct context double h1
      refine ⟨res, by simp [nan, lowRun, highRun, h1Run, run], fun c hc => ?_⟩
      obtain ⟨i, hi, at_i, rfl⟩ := facts c hc
      intro Object Value Object' Value' I J lit num mom frame d x node y hy
      rw [holds y hy.2.1, classDenote, edgeMeans frame node hy i hi, at_i, h1Is]
      rfl
    | MaxInclusive =>
      obtain ⟨res, run, facts⟩ := between_edges_correct context double 1#u128 h1
      refine ⟨res, by simp [nan, lowRun, highRun, h1Run, run], fun c hc => ?_⟩
      obtain ⟨i, j, hi, hj, at_i, at_j, means⟩ := facts c hc
      intro Object Value Object' Value' I J lit num mom frame d x node y hy
      rw [holds y hy.2.1, means J d, edgeMeans frame node hy i hi, edgeMeans frame node hy j hj, at_i, at_j, h1Is]
      rfl
    | MaxExclusive =>
      obtain ⟨res, run, facts⟩ := between_edges_correct context double 1#u128 low
      refine ⟨res, by simp [nan, lowRun, highRun, run], fun c hc => ?_⟩
      obtain ⟨i, j, hi, hj, at_i, at_j, means⟩ := facts c hc
      intro Object Value Object' Value' I J lit num mom frame d x node y hy
      rw [holds y hy.2.1, means J d, edgeMeans frame node hy i hi, edgeMeans frame node hy j hj, at_i, at_j, lowVal]
      rfl

/-! ### Time instants -/

/-- A time instant after a kernel instant on the time line, or at it unless
    `o`. -/
def TimeIn (instant : datatypes.Moment) (o : Bool) (m : Rowl.DatatypeMap.Moment) : Prop :=
  (Rowl.Moments.momentOf instant).key < m.key ∨ ((Rowl.Moments.momentOf instant).key = m.key ∧ o = false)

theorem momentOf_zoned (y : datatypes.Moment) : (Rowl.Moments.momentOf y).zone.isSome = y.zone.isSome := by
  simp [Rowl.Moments.momentOf]

theorem time_line_meaning (zoned : Bool) :
    ∃ c, data_ontology.time_line zoned = .ok c ∧
      ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
        (I : Interpretation Object Value) (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value)
        (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value), RangeFrame I J lit num mom →
          ∀ (context : data_ontology.Context) d x, NodeValue context I J lit num mom d x →
            context.kinds.stamp = true → (classDenote J c d ↔ ∃ m, MomentAt mom x m ∧ m.zone.isSome = zoned) := by
  have used : ∀ (context : data_ontology.Context), context.kinds.stamp = true →
      Used context.kinds .DateTime = true ∧ Used context.kinds .DateTimeStamp = true := by
    intro context stamp; simp [Used, stamp]
  cases zoned with
  | true =>
    refine ⟨.Class (kindClass .DateTimeStamp), by simp [data_ontology.time_line, kind_class_eq], ?_⟩
    intro Object Value Object' Value' I J lit num mom frame context d x node stamp
    rw [classDenote, node.kinds .DateTimeStamp (used context stamp).2, frame.stamps]
  | false =>
    refine ⟨.ObjectIntersectionOf ⟨.Class (kindClass .DateTime), .ObjectComplementOf (.Class (kindClass .DateTimeStamp)),
      alloc.vec.Vec.new ClassExpression⟩,
      by simp [data_ontology.time_line, kind_class_eq, data_ontology.not, data_ontology.and], ?_⟩
    intro Object Value Object' Value' I J lit num mom frame context d x node stamp
    rw [inter_iff]
    simp only [AtLeastTwo.elements, new_val, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, classDenote]
    rw [node.kinds .DateTime (used context stamp).1, node.kinds .DateTimeStamp (used context stamp).2, frame.moments,
      frame.stamps]
    constructor
    · rintro ⟨⟨m, hm⟩, notStamp⟩
      refine ⟨m, hm, ?_⟩
      cases hz : m.zone.isSome
      · rfl
      · exact absurd ⟨m, hm, hz⟩ notStamp
    · rintro ⟨m, hm, zone⟩
      refine ⟨⟨m, hm⟩, ?_⟩
      rintro ⟨m', hm', zone'⟩
      rw [frame.momentInjective m m' x hm hm'] at zone
      rw [zone] at zone'
      cases zone'

/-- The class of a part of a time facet on a line, inside or outside a time
    cut of the context: the time instants of the line after or at the
    instant as the cut's side says, or the others of the line. -/
theorem time_part_meaning (context : data_ontology.Context) (zoned : Bool) (instant : datatypes.Moment)
    (gi : Rowl.TimeOrder.InstantOk instant 0) (o inside : Bool) :
    ∃ res, data_ontology.time_part context zoned instant o inside = .ok res ∧ ∀ c, res = some c →
      ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
        (I : Interpretation Object Value) (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value)
        (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value), RangeFrame I J lit num mom →
          ∀ d x, NodeValue context I J lit num mom d x →
            (classDenote J c d ↔ ∃ m, MomentAt mom x m ∧ m.zone.isSome = zoned ∧ (TimeIn instant o m ↔ inside = true)) := by
  rw [data_ontology.time_part]
  obtain ⟨r, run, found⟩ := time_cut_index_found context.times zoned instant o 0#usize
  obtain ⟨line, lineRun, lineMeans⟩ := time_line_meaning.{u,v,w,x} zoned
  cases r with
  | none => exact ⟨none, by simp [run], by simp⟩
  | some i =>
    obtain ⟨h, same⟩ := found i rfl
    -- the meaning of the found cut at a node
    have cutMeans : ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
        {I : Interpretation Object Value} {J : Interpretation Object' Value'} {lit : datatypes.DataValue → Value}
        {num : ℝ → Value} {mom : Rowl.DatatypeMap.Moment → Value}, RangeFrame I J lit num mom →
        ∀ {d x}, NodeValue context I J lit num mom d x →
          context.kinds.stamp = true ∧ ∀ m, MomentAt mom x m → m.zone.isSome = zoned →
            (J.classes (timeClass i) d ↔ TimeIn instant o m) := by
      intro Object Value Object' Value' I J lit num mom frame d x node
      have nonempty : context.times.val ≠ [] := fun e => by simp [e] at h
      refine ⟨node.goodTimes.2 nonempty, fun m hm zone => ?_⟩
      have gc := node.goodTimes.1 _ (List.getElem_mem h)
      rw [same_time_cut_spec _ ⟨gc.1, gc.2.1, by have := gc.2.2; omega⟩ zoned instant gi o] at same
      have cut : CutAt context.times.val[i.val] zoned instant o := by simpa using same
      obtain ⟨cz, co, ck⟩ := cut
      rw [node.times m hm i h (by rw [cz, zone])]
      unfold InTimeCut TimeIn
      rw [ck, co]
    cases inside with
    | true =>
      refine ⟨some (.ObjectIntersectionOf ⟨line, .Class (timeClass i), alloc.vec.Vec.new ClassExpression⟩),
        by simp [run, lineRun, time_class_eq, data_ontology.and], fun c hc => ?_⟩
      cases hc
      intro Object Value Object' Value' I J lit num mom frame d x node
      obtain ⟨stamp, means⟩ := cutMeans frame node
      rw [inter_iff]
      simp only [AtLeastTwo.elements, new_val, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, classDenote]
      rw [lineMeans I J lit num mom frame context d x node stamp]
      constructor
      · rintro ⟨⟨m, hm, zone⟩, holds⟩
        exact ⟨m, hm, zone, by simpa using (means m hm zone).mp holds⟩
      · rintro ⟨m, hm, zone, iff⟩
        exact ⟨⟨m, hm, zone⟩, (means m hm zone).mpr (by simpa using iff)⟩
    | false =>
      refine ⟨some (.ObjectIntersectionOf ⟨line, .ObjectComplementOf (.Class (timeClass i)),
        alloc.vec.Vec.new ClassExpression⟩),
        by simp [run, lineRun, time_class_eq, data_ontology.not, data_ontology.and], fun c hc => ?_⟩
      cases hc
      intro Object Value Object' Value' I J lit num mom frame d x node
      obtain ⟨stamp, means⟩ := cutMeans frame node
      rw [inter_iff]
      simp only [AtLeastTwo.elements, new_val, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, classDenote]
      rw [lineMeans I J lit num mom frame context d x node stamp]
      constructor
      · rintro ⟨⟨m, hm, zone⟩, holds⟩
        exact ⟨m, hm, zone, by simpa using fun t => holds ((means m hm zone).mpr t)⟩
      · rintro ⟨m, hm, zone, iff⟩
        exact ⟨⟨m, hm, zone⟩, fun t => by simpa using iff.mp ((means m hm zone).mp t)⟩

/-! The order of XML Schema on the places of two time instants. -/

theorem moment_lt_same {b y : Rowl.DatatypeMap.Moment} (h : b.zone.isSome = y.zone.isSome) :
    b.Lt y ↔ b.key < y.key := by
  unfold Rowl.DatatypeMap.Moment.Lt
  constructor
  · rintro (⟨_, lt⟩ | ⟨bz, yz, _⟩ | ⟨bz, yz, _⟩)
    · exact lt
    · rw [yz] at h; simp_all
    · rw [bz] at h; simp_all
  · exact fun lt => .inl ⟨h, lt⟩

theorem moment_lt_cross {b y : Rowl.DatatypeMap.Moment} (h : b.zone.isSome ≠ y.zone.isSome) :
    b.Lt y ↔ b.key + 50400 < y.key := by
  unfold Rowl.DatatypeMap.Moment.Lt
  constructor
  · rintro (⟨e, _⟩ | ⟨_, _, lt⟩ | ⟨_, _, lt⟩)
    · exact absurd e h
    · linarith
    · exact lt
  · intro lt
    cases hb : b.zone.isSome <;> cases hy : y.zone.isSome <;> rw [hb, hy] at h
    · exact absurd rfl h
    · exact .inr (.inr ⟨by simpa using hb, rfl, lt⟩)
    · exact .inr (.inl ⟨rfl, by simpa using hy, by linarith⟩)
    · exact absurd rfl h

theorem moment_same_iff {b y : Rowl.DatatypeMap.Moment} :
    b.Same y ↔ b.zone.isSome = y.zone.isSome ∧ b.key = y.key := Iff.rfl

theorem moment_le_same {b y : Rowl.DatatypeMap.Moment} (h : b.zone.isSome = y.zone.isSome) :
    b.Le y ↔ b.key ≤ y.key := by
  unfold Rowl.DatatypeMap.Moment.Le
  rw [moment_lt_same h, moment_same_iff]
  constructor
  · rintro (lt | ⟨_, e⟩)
    · exact le_of_lt lt
    · exact le_of_eq e
  · intro le
    rcases lt_or_eq_of_le le with lt | e
    · exact .inl lt
    · exact .inr ⟨h, e⟩

theorem moment_le_cross {b y : Rowl.DatatypeMap.Moment} (h : b.zone.isSome ≠ y.zone.isSome) :
    b.Le y ↔ b.key + 50400 < y.key := by
  unfold Rowl.DatatypeMap.Moment.Le
  rw [moment_lt_cross h, moment_same_iff]
  constructor
  · rintro (lt | ⟨e, _⟩)
    · exact lt
    · exact absurd e h
  · exact .inl

theorem bool_other (a b : Bool) : a = decide ¬(b = true) ↔ a ≠ b := by
  cases a <;> cases b <;> simp

/-- The part of a range facet with a time instant as bound on the bound's own
    line holds at the node of a value exactly when the value is a time instant
    of that line on the facet's side of the bound. -/
theorem same_line_part_meaning (context : data_ontology.Context) (F : datatypes.Facet) (bound : datatypes.Moment)
    (cb : Rowl.Moments.CanonicalMoment bound) (small : bound.year.val.length + 2 < Usize.max) :
    ∃ res, data_ontology.same_line_part context F bound = .ok res ∧ ∀ c, res = some c →
      ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
        (I : Interpretation Object Value) (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value)
        (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value), RangeFrame I J lit num mom →
          ∀ d x, NodeValue context I J lit num mom d x →
            (classDenote J c d ↔ ∃ m, MomentAt mom x m ∧ m.zone.isSome = bound.zone.isSome ∧
              MomentFacetHolds F (Rowl.Moments.momentOf bound) m) := by
  obtain ⟨i, iRun, iOk, iKey⟩ := Rowl.TimeOrder.instant_canonical bound cb (room := 0) (by omega)
  have step : ∀ (o inside : Bool), (∀ m : Rowl.DatatypeMap.Moment, m.zone.isSome = bound.zone.isSome →
      ((TimeIn i o m ↔ inside = true) ↔ MomentFacetHolds F (Rowl.Moments.momentOf bound) m)) →
      ∃ res, (do
          let m ← moments.instant bound
          data_ontology.time_part context bound.zone.isSome m o inside : Result (Option ClassExpression)) = .ok res ∧
        ∀ c, res = some c →
        ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
          (I : Interpretation Object Value) (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value)
          (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value), RangeFrame I J lit num mom →
            ∀ d x, NodeValue context I J lit num mom d x →
              (classDenote J c d ↔ ∃ m, MomentAt mom x m ∧ m.zone.isSome = bound.zone.isSome ∧
                MomentFacetHolds F (Rowl.Moments.momentOf bound) m) := by
    intro o inside holds
    obtain ⟨res, run, means⟩ := time_part_meaning.{u,v,w,x} context bound.zone.isSome i iOk o inside
    refine ⟨res, by rw [iRun, bind_ok]; exact run, fun c hc => ?_⟩
    intro Object Value Object' Value' I J lit num mom frame d x node
    rw [means c hc I J lit num mom frame d x node]
    constructor
    · rintro ⟨m, hm, zone, side⟩
      exact ⟨m, hm, zone, (holds m zone).mp side⟩
    · rintro ⟨m, hm, zone, side⟩
      exact ⟨m, hm, zone, (holds m zone).mpr side⟩
  have zoneOf : ∀ m : Rowl.DatatypeMap.Moment, m.zone.isSome = bound.zone.isSome →
      (Rowl.Moments.momentOf bound).zone.isSome = m.zone.isSome := by
    intro m zone; rw [momentOf_zoned, zone]
  rw [data_ontology.same_line_part, Rowl.TimeOrder.zoned_spec, bind_ok]
  cases F with
  | MinInclusive =>
    refine step false true fun m zone => ?_
    rw [MomentFacetHolds, moment_le_same (zoneOf m zone), ← iKey]
    unfold TimeIn
    simp only [and_true, iff_true]
    exact le_iff_lt_or_eq.symm
  | MaxInclusive =>
    refine step true false fun m zone => ?_
    rw [MomentFacetHolds, moment_le_same (zoneOf m zone).symm, ← iKey]
    unfold TimeIn
    simp only [Bool.true_eq_false, and_false, or_false, Bool.false_eq_true, iff_false, not_lt]
  | MinExclusive =>
    refine step true true fun m zone => ?_
    rw [MomentFacetHolds, moment_lt_same (zoneOf m zone), ← iKey]
    unfold TimeIn
    simp only [Bool.true_eq_false, and_false, or_false, iff_true]
  | MaxExclusive =>
    refine step false false fun m zone => ?_
    rw [MomentFacetHolds, moment_lt_same (zoneOf m zone).symm, ← iKey]
    unfold TimeIn
    simp only [and_true, Bool.false_eq_true, iff_false, not_or, not_lt]
    constructor
    · rintro ⟨le, ne⟩
      exact lt_of_le_of_ne le (Ne.symm ne)
    · intro lt
      exact ⟨le_of_lt lt, ne_of_gt lt⟩

/-- The part of a range facet with a time instant as bound on the other line
    holds at the node of a value exactly when the value is a time instant of
    that line on the facet's side of the bound: fourteen hours past it. -/
theorem other_line_part_meaning (context : data_ontology.Context) (F : datatypes.Facet) (bound : datatypes.Moment)
    (cb : Rowl.Moments.CanonicalMoment bound) (small : bound.year.val.length + 4 < Usize.max) :
    ∃ res, data_ontology.other_line_part context F bound = .ok res ∧ ∀ c, res = some c →
      ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
        (I : Interpretation Object Value) (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value)
        (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value), RangeFrame I J lit num mom →
          ∀ d x, NodeValue context I J lit num mom d x →
            (classDenote J c d ↔ ∃ m, MomentAt mom x m ∧ m.zone.isSome ≠ bound.zone.isSome ∧
              MomentFacetHolds F (Rowl.Moments.momentOf bound) m) := by
  obtain ⟨i, iRun, iOk, iKey⟩ := Rowl.TimeOrder.instant_canonical bound cb (room := 2) (by omega)
  have step : ∀ (n : U16), n.val = 840 → ∀ (later o inside : Bool),
      (∀ m : Rowl.DatatypeMap.Moment, m.zone.isSome ≠ bound.zone.isSome → ∀ s : datatypes.Moment,
        (Rowl.Moments.momentOf s).key = (Rowl.Moments.momentOf bound).key + (if later then 50400 else -50400) →
        ((TimeIn s o m ↔ inside = true) ↔ MomentFacetHolds F (Rowl.Moments.momentOf bound) m)) →
      ∃ res, (do
          let m ← moments.instant bound
          let m1 ← moments.shifted m later n
          data_ontology.time_part context (¬ bound.zone.isSome) m1 o inside : Result (Option ClassExpression)) =
          .ok res ∧
        ∀ c, res = some c →
        ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
          (I : Interpretation Object Value) (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value)
          (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value), RangeFrame I J lit num mom →
            ∀ d x, NodeValue context I J lit num mom d x →
              (classDenote J c d ↔ ∃ m, MomentAt mom x m ∧ m.zone.isSome ≠ bound.zone.isSome ∧
                MomentFacetHolds F (Rowl.Moments.momentOf bound) m) := by
    intro n hn later o inside holds
    obtain ⟨s, sRun, sOk, sKey⟩ := Rowl.TimeOrder.shifted_canonical i later n (by omega) iOk
    obtain ⟨res, run, means⟩ := time_part_meaning.{u,v,w,x} context (¬ bound.zone.isSome) s sOk o inside
    refine ⟨res, by rw [iRun, bind_ok, sRun, bind_ok]; exact run, fun c hc => ?_⟩
    have sKey' : (Rowl.Moments.momentOf s).key =
        (Rowl.Moments.momentOf bound).key + (if later then 50400 else -50400) := by
      rw [sKey, iKey, hn]; cases later <;> norm_num
    intro Object Value Object' Value' I J lit num mom frame d x node
    rw [means c hc I J lit num mom frame d x node]
    constructor
    · rintro ⟨m, hm, zone, side⟩
      have zone' := (bool_other _ _).mp zone
      exact ⟨m, hm, zone', (holds m zone' s sKey').mp side⟩
    · rintro ⟨m, hm, zone, side⟩
      exact ⟨m, hm, (bool_other _ _).mpr zone, (holds m zone s sKey').mpr side⟩
  have cross : ∀ m : Rowl.DatatypeMap.Moment, m.zone.isSome ≠ bound.zone.isSome →
      (Rowl.Moments.momentOf bound).zone.isSome ≠ m.zone.isSome := by
    intro m zone; rw [momentOf_zoned]; exact Ne.symm zone
  have e840 : (840#u16).val = 840 := by simp
  rw [data_ontology.other_line_part, Rowl.TimeOrder.zoned_spec, bind_ok]
  cases F with
  | MinInclusive =>
    refine step 840#u16 e840 true true true fun m zone s sKey => ?_
    rw [MomentFacetHolds, moment_le_cross (cross m zone)]
    unfold TimeIn
    rw [sKey]
    simp only [↓reduceIte, Bool.true_eq_false, and_false, or_false, iff_true]
  | MaxInclusive =>
    refine step 840#u16 e840 false false false fun m zone s sKey => ?_
    rw [MomentFacetHolds, moment_le_cross (cross m zone).symm]
    unfold TimeIn
    rw [sKey]
    simp only [Bool.false_eq_true, ↓reduceIte, and_true, iff_false, not_or, not_lt]
    constructor
    · rintro ⟨le, ne⟩
      exact lt_of_le_of_ne (by linarith) (fun e => ne (by linarith))
    · intro lt
      exact ⟨by linarith, fun e => by linarith⟩
  | MinExclusive =>
    refine step 840#u16 e840 true true true fun m zone s sKey => ?_
    rw [MomentFacetHolds, moment_lt_cross (cross m zone)]
    unfold TimeIn
    rw [sKey]
    simp only [↓reduceIte, Bool.true_eq_false, and_false, or_false, iff_true]
  | MaxExclusive =>
    refine step 840#u16 e840 false false false fun m zone s sKey => ?_
    rw [MomentFacetHolds, moment_lt_cross (cross m zone).symm]
    unfold TimeIn
    rw [sKey]
    simp only [Bool.false_eq_true, ↓reduceIte, and_true, iff_false, not_or, not_lt]
    constructor
    · rintro ⟨le, ne⟩
      exact lt_of_le_of_ne (by linarith) (fun e => ne (by linarith))
    · intro lt
      exact ⟨by linarith, fun e => by linarith⟩

theorem or_iff (J : Interpretation Object' Value') (a b : ClassExpression) (d : Object') :
    classDenote J (.ObjectUnionOf ⟨a, b, alloc.vec.Vec.new ClassExpression⟩) d ↔
      classDenote J a d ∨ classDenote J b d := by
  rw [classDenote]; simp [AtLeastTwo.elements, new_val]

/-- The class of a range facet with a time instant as bound holds at the node
    of a time instant exactly when the facet holds of the instant. -/
theorem time_facet_class_meaning (context : data_ontology.Context) (F : datatypes.Facet) (bound : datatypes.Moment)
    (cb : Rowl.Moments.CanonicalMoment bound) :
    ∃ res, data_ontology.time_facet_class context F bound = .ok res ∧ ∀ c, res = some c →
      ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
        (I : Interpretation Object Value) (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value)
        (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value), RangeFrame I J lit num mom →
          ∀ d x, NodeValue context I J lit num mom d x → ∀ m, MomentAt mom x m →
            (MomentFacetHolds F (Rowl.Moments.momentOf bound) m ↔ classDenote J c d) := by
  rw [data_ontology.time_facet_class, bounded_year_eq]
  by_cases small : bound.year.val.length < Usize.max / 16
  · obtain ⟨same, sameRun, sameMeans⟩ := same_line_part_meaning.{u,v,w,x} context F bound cb (by omega)
    obtain ⟨other, otherRun, otherMeans⟩ := other_line_part_meaning.{u,v,w,x} context F bound cb (by omega)
    cases same with
    | none => exact ⟨none, by simp [small, sameRun, otherRun], by simp⟩
    | some s =>
      cases other with
      | none => exact ⟨none, by simp [small, sameRun, otherRun], by simp⟩
      | some t =>
        refine ⟨some (.ObjectUnionOf ⟨s, t, alloc.vec.Vec.new ClassExpression⟩),
          by simp [small, sameRun, otherRun, data_ontology.or], fun c hc => ?_⟩
        cases hc
        intro Object Value Object' Value' I J lit num mom frame d x node m hm
        rw [or_iff, sameMeans s rfl I J lit num mom frame d x node, otherMeans t rfl I J lit num mom frame d x node]
        constructor
        · intro holds
          by_cases zone : m.zone.isSome = bound.zone.isSome
          · exact .inl ⟨m, hm, zone, holds⟩
          · exact .inr ⟨m, hm, zone, holds⟩
        · rintro (⟨m', hm', _, holds⟩ | ⟨m', hm', _, holds⟩) <;>
            rwa [frame.momentInjective m m' x hm hm']
  · exact ⟨none, by simp [small], by simp⟩

theorem float_kind_double : floatKind true = .Double := rfl
theorem float_kind_float : floatKind false = .Float := rfl

set_option maxHeartbeats 8000000 in
/-- The class of a facet restriction holds at a data node standing for a
    value of the restricted kind exactly when the facet holds of it: for a
    numeric kind while numbers are ordered, for `xsd:double` and `xsd:float`,
    and for `xsd:dateTime` and `xsd:dateTimeStamp`. -/
theorem facet_class_meaning (context : data_ontology.Context) (k : datatypes.Kind) (f : FacetRestriction) :
    ∃ res, data_ontology.facet_class context k f = .ok res ∧ ∀ c, res = some c →
      ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
        (I : Interpretation Object Value) (J : Interpretation Object' Value') (lit : datatypes.DataValue → Value)
        (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value), RangeFrame I J lit num mom → ∀ d x, NodeValue context I J lit num mom d x →
          I.datatypes (typeOf k) x →
          (Rowl.Datatypes.IsNumeric k ∧ context.kinds.ordered = true) ∨ k = .Double ∨ k = .Float ∨
            k = .DateTime ∨ k = .DateTimeStamp →
            (I.facets f x ↔ classDenote J c d) := by
  rw [data_ontology.facet_class, Rowl.Datatypes.facet_of_correct]
  obtain ⟨result, run, someValue, _⟩ := Rowl.Datatypes.literal_value_correct.{0} f.value
  rw [run]
  cases facet : Rowl.Datatypes.facetOf f.facet with
  | none => exact ⟨none, by simp, by simp⟩
  | some F =>
    cases result with
    | none => exact ⟨none, by simp, by simp⟩
    | some w =>
      have canonical := (someValue w rfl).1
      -- the empty class, for a bound whose values are not the kind's
      have empty : ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
          {I : Interpretation Object Value} {J : Interpretation Object' Value'} {d : Object'} {x : Value},
          (∀ d, J.classes thing d) → ¬ I.facets f x →
            (I.facets f x ↔ classDenote J (.ObjectComplementOf (.Class thing)) d) := by
        intro Object Value Object' Value' I J d x thing' no
        simp [classDenote, thing' d, no]
      by_cases number : Rowl.Datatypes.IsNumber w
      · have notBinary : (∀ b, w ≠ .Double b) ∧ ∀ b, w ≠ .Float b := by
          constructor <;> intro b h <;> subst h <;> simp [Rowl.Datatypes.IsNumber] at number
        by_cases numericK : Rowl.Datatypes.IsNumeric k
        · obtain ⟨res, bRun, bFacts⟩ := bound_class_correct context (some w) (FacetOpen F) (FacetOutside F)
          refine ⟨res, ?_, fun c hc => ?_⟩
          · cases w <;> simp_all [Rowl.Datatypes.IsNumber, Rowl.Datatypes.numeric_correct, numeric_kind_eq,
              facet_open_eq, facet_outside_eq]
          intro Object Value Object' Value' I J lit num mom frame d x node inType kinds
          have ordered : context.kinds.ordered = true := by
            rcases kinds with ⟨_, o⟩ | rfl | rfl | rfl | rfl
            · exact o
            all_goals simp [Rowl.Datatypes.IsNumeric] at numericK
          have isNumber : ∃ r, x = num r := by
            obtain ⟨r, rfl, _⟩ := (frame.numeric k numericK x).mp inType
            exact ⟨r, rfl⟩
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
        · refine ⟨some (.ObjectComplementOf (.Class thing)), ?_, fun c hc => ?_⟩
          · cases w <;> simp_all [Rowl.Datatypes.IsNumber, Rowl.Datatypes.numeric_correct, numeric_kind_eq, nothing_eq]
          cases hc
          intro Object Value Object' Value' I J lit num mom frame d x node inType kinds
          apply empty frame.thing
          rw [frame.facets f F w facet run number x]
          rintro ⟨r, rfl, _⟩
          rcases kinds with ⟨numeric, _⟩ | rfl | rfl | rfl | rfl
          · exact numericK numeric
          · obtain ⟨y, hy⟩ := (frame.binaries true _).mp inType
            exact frame.binaryReal true y _ r hy rfl
          · obtain ⟨y, hy⟩ := (frame.binaries false _).mp inType
            exact frame.binaryReal false y _ r hy rfl
          · obtain ⟨y, hy⟩ := (frame.moments _).mp inType
            exact frame.momentReal y _ r hy rfl
          · obtain ⟨y, hy, _⟩ := (frame.stamps _).mp inType
            exact frame.momentReal y _ r hy rfl
      · cases w with
        | Double b =>
          by_cases kd : k = .Double
          · subst kd
            obtain ⟨res, bRun, bMeans⟩ := binary_facet_class_meaning context true F b canonical.1 canonical.2
            refine ⟨res, by simp [bRun], fun c hc => ?_⟩
            intro Object Value Object' Value' I J lit num mom frame d x node inType _
            obtain ⟨y, hy⟩ := (frame.binaries true x).mp inType
            rw [frame.binaryFacets f F true b facet run x]
            constructor
            · rintro ⟨y', hy', holds⟩
              exact (bMeans c hc I J lit num mom frame d x node y' hy').mp holds
            · intro holds
              exact ⟨y, hy, (bMeans c hc I J lit num mom frame d x node y hy).mpr holds⟩
          · refine ⟨some (.ObjectComplementOf (.Class thing)), by cases k <;> simp_all [nothing_eq], fun c hc => ?_⟩
            cases hc
            intro Object Value Object' Value' I J lit num mom frame d x node inType kinds
            apply empty frame.thing
            rw [frame.binaryFacets f F true b facet run x]
            rintro ⟨y, hy, _⟩
            rcases kinds with ⟨numeric, _⟩ | rfl | rfl | rfl | rfl
            · obtain ⟨r, rfl, _⟩ := (frame.numeric k numeric x).mp inType
              exact frame.binaryReal true y _ r hy rfl
            · exact kd rfl
            · obtain ⟨y', hy'⟩ := (frame.binaries false x).mp inType
              exact frame.binaryApart y y' x hy hy'
            · obtain ⟨y', hy'⟩ := (frame.moments x).mp inType
              exact frame.momentBinary y' true y x hy' hy
            · obtain ⟨y', hy', _⟩ := (frame.stamps x).mp inType
              exact frame.momentBinary y' true y x hy' hy
        | Float b =>
          by_cases kf : k = .Float
          · subst kf
            obtain ⟨res, bRun, bMeans⟩ := binary_facet_class_meaning context false F b canonical.1 canonical.2
            refine ⟨res, by simp [bRun], fun c hc => ?_⟩
            intro Object Value Object' Value' I J lit num mom frame d x node inType _
            obtain ⟨y, hy⟩ := (frame.binaries false x).mp inType
            rw [frame.binaryFacets f F false b facet run x]
            constructor
            · rintro ⟨y', hy', holds⟩
              exact (bMeans c hc I J lit num mom frame d x node y' hy').mp holds
            · intro holds
              exact ⟨y, hy, (bMeans c hc I J lit num mom frame d x node y hy).mpr holds⟩
          · refine ⟨some (.ObjectComplementOf (.Class thing)), by cases k <;> simp_all [nothing_eq], fun c hc => ?_⟩
            cases hc
            intro Object Value Object' Value' I J lit num mom frame d x node inType kinds
            apply empty frame.thing
            rw [frame.binaryFacets f F false b facet run x]
            rintro ⟨y, hy, _⟩
            rcases kinds with ⟨numeric, _⟩ | rfl | rfl | rfl | rfl
            · obtain ⟨r, rfl, _⟩ := (frame.numeric k numeric x).mp inType
              exact frame.binaryReal false y _ r hy rfl
            · obtain ⟨y', hy'⟩ := (frame.binaries true x).mp inType
              exact frame.binaryApart y' y x hy' hy
            · exact kf rfl
            · obtain ⟨y', hy'⟩ := (frame.moments x).mp inType
              exact frame.momentBinary y' false y x hy' hy
            · obtain ⟨y', hy', _⟩ := (frame.stamps x).mp inType
              exact frame.momentBinary y' false y x hy' hy
        | Moment b =>
          by_cases kt : k = .DateTime ∨ k = .DateTimeStamp
          · obtain ⟨res, tRun, tMeans⟩ := time_facet_class_meaning.{u,v,w,x} context F b canonical
            refine ⟨res, by rcases kt with rfl | rfl <;> simp [tRun], fun c hc => ?_⟩
            intro Object Value Object' Value' I J lit num mom frame d x node inType _
            obtain ⟨y, hy⟩ : ∃ m, MomentAt mom x m := by
              rcases kt with rfl | rfl
              · exact (frame.moments x).mp inType
              · obtain ⟨y, hy, _⟩ := (frame.stamps x).mp inType
                exact ⟨y, hy⟩
            rw [frame.momentFacets f F b facet run x]
            constructor
            · rintro ⟨y', hy', holds⟩
              exact (tMeans c hc I J lit num mom frame d x node y' hy').mp holds
            · intro holds
              exact ⟨y, hy, (tMeans c hc I J lit num mom frame d x node y hy).mpr holds⟩
          · refine ⟨some (.ObjectComplementOf (.Class thing)), by
              cases k <;> first | exact absurd (.inl rfl) kt | exact absurd (.inr rfl) kt | simp [nothing_eq],
              fun c hc => ?_⟩
            cases hc
            intro Object Value Object' Value' I J lit num mom frame d x node inType kinds
            apply empty frame.thing
            rw [frame.momentFacets f F b facet run x]
            rintro ⟨y, hy, _⟩
            rcases kinds with ⟨numeric, _⟩ | rfl | rfl | rfl | rfl
            · obtain ⟨r, rfl, _⟩ := (frame.numeric k numeric x).mp inType
              exact frame.momentReal y _ r hy rfl
            · obtain ⟨y', hy'⟩ := (frame.binaries true x).mp inType
              exact frame.momentBinary y true y' x hy hy'
            · obtain ⟨y', hy'⟩ := (frame.binaries false x).mp inType
              exact frame.momentBinary y false y' x hy hy'
            · exact kt (.inl rfl)
            · exact kt (.inr rfl)
        | _ => exact ⟨none, by simp_all [Rowl.Datatypes.IsNumber, Rowl.Datatypes.numeric_correct], by simp⟩

/-- The classes of the facet restrictions of a list, member by member. -/
theorem facet_classes_meaning (context : data_ontology.Context) (k : datatypes.Kind)
    (restrictions : alloc.vec.Vec FacetRestriction)
    (index : Usize) (out : alloc.vec.Vec ClassExpression)
    (room : out.val.length + (restrictions.val.length - index.val) ≤ Usize.max) :
    ∃ res, data_ontology.facet_classes context k restrictions index out = .ok res ∧
      ∀ v, res = some v → v.val.take out.val.length = out.val ∧
        List.Forall₂ (fun c f => ∃ res, data_ontology.facet_class context k f = .ok (some res) ∧ res = c)
          (v.val.drop out.val.length) (restrictions.val.drop index.val) := by
  rw [data_ontology.facet_classes]
  by_cases inside : index.val < restrictions.val.length
  · have lookup : restrictions.index_usize index = .ok restrictions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨res, run, _⟩ := facet_class_meaning.{0,0,0,0} context k restrictions.val[index.val]
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
      obtain ⟨rest, restRun, restFacts⟩ := facet_classes_meaning context k restrictions next pushed
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
      intro Object Value Object' Value' I J lit num mom frame d x _
      subst literal
      simp [dataDenote, classDenote, frame.literal x, frame.thing d]
    · simp only [literal, decide_false, Bool.false_eq_true, ↓reduceIte, Rowl.Datatypes.kind_of_correct, bind_ok]
      cases kind : kindOf dt with
      | none => exact ⟨none, by simp, by simp⟩
      | some k =>
        obtain ⟨res, run, means⟩ := kind_range_meaning.{u,v,w,x} context k
        refine ⟨res, by simp [run], fun c hc => ?_⟩
        intro Object Value Object' Value' I J lit num mom frame d x node
        rw [Rowl.Datatypes.kindOf_some kind]
        simp only [dataDenote]
        exact means c hc I J lit num mom frame d x node
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
      intro Object Value Object' Value' I J lit num mom frame d x node
      have pairs := means cs rfl
      have every : (∀ e ∈ members.elements, dataDenote I e x) ↔ ∀ c ∈ cs.elements, classDenote J c d := by
        constructor
        · intro all c member
          obtain ⟨e, inside, rel⟩ := forall2_mem_left pairs c member
          exact (rel I J lit num mom frame d x node).mp (all e inside)
        · intro all e member
          obtain ⟨c, inside, rel⟩ := forall2_mem_right pairs e member
          exact (rel I J lit num mom frame d x node).mpr (all c inside)
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
      intro Object Value Object' Value' I J lit num mom frame d x node
      have pairs := means cs rfl
      have some' : (∃ e ∈ members.elements, dataDenote I e x) ↔ ∃ c ∈ cs.elements, classDenote J c d := by
        constructor
        · rintro ⟨e, member, holds⟩
          obtain ⟨c, inside, rel⟩ := forall2_mem_right pairs e member
          exact ⟨c, inside, (rel I J lit num mom frame d x node).mp holds⟩
        · rintro ⟨c, member, holds⟩
          obtain ⟨e, inside, rel⟩ := forall2_mem_left pairs c member
          exact ⟨e, inside, (rel I J lit num mom frame d x node).mpr holds⟩
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
      intro Object Value Object' Value' I J lit num mom frame d x node
      rw [dataDenote, classDenote]
      exact not_congr (means c rfl I J lit num mom frame d x node)
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
        intro Object Value Object' Value' I J lit num mom frame d x node
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
      rw [data_ontology.restriction_range, numeric_kind_eq, binary_kind_eq, time_kind_eq]
      by_cases ready : (Rowl.Datatypes.IsNumeric k ∧ context.kinds.ordered = true) ∨ k = .Double ∨ k = .Float ∨
          k = .DateTime ∨ k = .DateTimeStamp
      · have readyB : (((decide (Rowl.Datatypes.IsNumeric k) && context.kinds.ordered) ||
            decide (k = .Double ∨ k = .Float)) || decide (k = .DateTime ∨ k = .DateTimeStamp)) = true := by
          rcases ready with ⟨n, o⟩ | rfl | rfl | rfl | rfl <;> simp_all
        obtain ⟨b, bRun, bMeans⟩ := kind_range_meaning.{u,v,w,x} context k
        obtain ⟨f, fRun, fMeans⟩ := facet_class_meaning.{u,v,w,x} context k restrictions.first
        obtain ⟨fs, fsRun, fsFacts⟩ := facet_classes_meaning context k restrictions.rest 0#usize
          (alloc.vec.Vec.new ClassExpression) (by simp [new_val])
        cases b with
        | none => exact ⟨none, by simp only [bind_ok]; rw [if_pos readyB]; simp [bRun, fRun, fsRun], by simp⟩
        | some base =>
          cases f with
          | none => exact ⟨none, by simp only [bind_ok]; rw [if_pos readyB]; simp [bRun, fRun, fsRun], by simp⟩
          | some first =>
            cases fs with
            | none => exact ⟨none, by simp only [bind_ok]; rw [if_pos readyB]; simp [bRun, fRun, fsRun], by simp⟩
            | some rest =>
              refine ⟨some (.ObjectIntersectionOf ⟨base, first, rest⟩),
                by simp only [bind_ok]; rw [if_pos readyB]; simp [bRun, fRun, fsRun], fun c hc => ?_⟩
              cases hc
              intro Object Value Object' Value' I J lit num mom frame d x node
              obtain ⟨_, pairs⟩ := fsFacts rest rfl
              simp only [new_val, List.length_nil, List.drop_zero, zero_val] at pairs
              rw [Rowl.Datatypes.kindOf_some kind]
              rw [dataDenote, inter_iff]
              simp only [AtLeastTwo.elements, NonEmpty.elements, List.mem_cons, forall_eq_or_imp]
              rw [← bMeans base rfl I J lit num mom frame d x node]
              constructor
              · rintro ⟨inType, firstFacet, restFacets⟩
                refine ⟨inType, (fMeans first rfl I J lit num mom frame d _ node inType ready).mp firstFacet,
                  fun c member => ?_⟩
                obtain ⟨e, inside, ⟨res, run', same⟩⟩ := forall2_mem_left pairs c member
                obtain ⟨_, run'', means⟩ := facet_class_meaning.{u,v,w,x} context k e
                rw [run''] at run'
                cases Result.ok_injective run'
                subst same
                exact (means res rfl I J lit num mom frame d _ node inType ready).mp (restFacets e inside)
              · rintro ⟨inType, firstHolds, restHold⟩
                refine ⟨inType, (fMeans first rfl I J lit num mom frame d _ node inType ready).mpr firstHolds,
                  fun e later => ?_⟩
                obtain ⟨c, inside, ⟨res, run', same⟩⟩ := forall2_mem_right pairs e later
                obtain ⟨_, run'', means⟩ := facet_class_meaning.{u,v,w,x} context k e
                rw [run''] at run'
                cases Result.ok_injective run'
                subst same
                exact (means res rfl I J lit num mom frame d _ node inType ready).mpr (restHold res inside)
      · have readyB : ¬ (((decide (Rowl.Datatypes.IsNumeric k) && context.kinds.ordered) ||
            decide (k = .Double ∨ k = .Float)) || decide (k = .DateTime ∨ k = .DateTimeStamp)) = true := by
          intro h; apply ready; simpa [or_assoc] using h
        exact ⟨none, by simp only [bind_ok]; rw [if_neg readyB], by simp⟩
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
