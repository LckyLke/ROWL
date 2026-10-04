import Rowl.DataStructure

/-!
Models of `data_ontology`'s encoding made from OWL models. An OWL
interpretation's elements and its data values become the elements and the data
nodes of an interpretation of the encoding (`lifted`): the data properties
become their roles from the elements to the values, each kind's class holds at
the values of its datatype, each literal value's individual is its value with
the bit classes of its index, and every other name keeps its meaning at the
elements. When the OWL interpretation satisfies a closure, the lifted one
satisfies its encoding (`lifted_satisfies`), and every class expression's
encoding holds at an element exactly when the expression does
(`lifted_class`).
-/
namespace Rowl.DataComplete
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DatatypeMap (Normative IsInteger IsDecimal integerType decimalType stringType plainType booleanType)
open Rowl.Datatypes (Canonical valueOf typeOf kindOf InKind)
open Rowl.AlcOntology (RoleOf)
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.DataStructure
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe u v w x

/-! ### The encoding's names -/

theorem usize_bytes (i : Usize) : i.val < 256 ^ 8 := by
  have := i.hBounds
  have bits : UScalarTy.Usize.numBits ≤ 64 := by
    simp only [UScalarTy.numBits]
    cases System.Platform.numBits_eq <;> simp_all
  calc i.val < 2 ^ UScalarTy.Usize.numBits := this
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) bits
    _ = 256 ^ 8 := by norm_num

theorem reserved_data : Reserved dataClass.iri.spelling.val := by simp [Reserved, dataClass_name, dataName]
theorem reserved_kind (k : datatypes.Kind) : Reserved (kindClass k).iri.spelling.val := by
  simp [Reserved, kindClass_name, kindName]
theorem reserved_bit (j : Usize) : Reserved (bitClass j).iri.spelling.val := by
  simp [Reserved, bitClass_name, bitName]
theorem reserved_value (i : Usize) : Reserved (valueIndividual i).iri.spelling.val := by
  simp [Reserved, valueIndividual_name, valueName]
theorem reserved_object : Reserved objectIndividual.iri.spelling.val := by
  simp [Reserved, objectIndividual_name, objectName]
theorem thing_plain : ¬ Reserved thing.iri.spelling.val := by simp [Reserved, thing]
theorem nothing_plain : ¬ Reserved nothing.iri.spelling.val := by simp [Reserved, nothing]
theorem bottom_plain : ¬ Reserved bottomObject.iri.spelling.val := by simp [Reserved, bottomObject]
theorem thing_ne_nothing : thing ≠ nothing := by
  rw [Ne, Rowl.Tableau.class_eq_iff]; simp [thing, nothing]

theorem class_ne_of_reserved {a b : Class} (plain : ¬ Reserved a.iri.spelling.val)
    (reserved : Reserved b.iri.spelling.val) : a ≠ b := by
  rintro rfl; exact plain reserved

theorem kind_class_injective {k k' : datatypes.Kind} (same : kindClass k = kindClass k') : k = k' := by
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp only [kindClass_name, kindName, List.cons.injEq, true_and, and_true] at this
  cases k <;> cases k' <;> first | rfl | (simp [kindByte] at this)

theorem bit_class_injective {j j' : Usize} (same : bitClass j = bitClass j') : j = j' := by
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp only [bitClass_name, bitName, List.cons.injEq, true_and] at this
  exact UScalar.eq_of_val_eq (eightBytes_injective _ _ 8 (usize_bytes j) (usize_bytes j') this)

theorem value_individual_injective {i i' : Usize} (same : valueIndividual i = valueIndividual i') : i = i' := by
  have := congrArg (fun a : NamedIndividual => a.iri.spelling.val) same
  simp only [valueIndividual_name, valueName, List.cons.injEq, true_and] at this
  exact UScalar.eq_of_val_eq (eightBytes_injective _ _ 8 (usize_bytes i) (usize_bytes i') this)

theorem data_ne_kind (k : datatypes.Kind) : dataClass ≠ kindClass k := by
  intro same
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp [dataClass_name, kindClass_name, dataName, kindName] at this

theorem data_ne_bit (j : Usize) : dataClass ≠ bitClass j := by
  intro same
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp [dataClass_name, bitClass_name, dataName, bitName] at this

theorem kind_ne_bit (k : datatypes.Kind) (j : Usize) : kindClass k ≠ bitClass j := by
  intro same
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp [kindClass_name, bitClass_name, kindName, bitName] at this

theorem object_ne_value (i : Usize) : objectIndividual ≠ valueIndividual i := by
  intro same
  have := congrArg (fun a : NamedIndividual => a.iri.spelling.val) same
  simp [objectIndividual_name, valueIndividual_name, objectName, valueName] at this

theorem data_role_reserved {p : DataProperty} {q : ObjectProperty} (h : DataRoleOf p q) :
    Reserved q.iri.spelling.val := by
  simp only [DataRoleOf] at h
  simp [Reserved, h, dataRoleName]

theorem data_role_injective {p p' : DataProperty} {q : ObjectProperty} (h : DataRoleOf p q) (h' : DataRoleOf p' q) :
    p = p' := by
  simp only [DataRoleOf, dataRoleName] at h h'
  rw [h] at h'
  simp only [List.cons.injEq, true_and] at h'
  exact (dataProperty_eq_iff _ _).mpr h'

/-! ### Values under the OWL 2 datatype map -/

section Values
variable {Native : Type w} {D : DatatypeMap Native}

theorem value_datatype (N : Normative D) {x : datatypes.DataValue} (canonical : Canonical x) :
    isDatatypeValue D (valueOf N x) := by
  cases x with
  | Number n wh f => exact ⟨typeOf .Decimal, Rowl.Datatypes.normative_supported N _,
      (Rowl.Datatypes.normative_in_kind N canonical .Decimal).mp (by simp [InKind])⟩
  | Text t => exact ⟨typeOf .String, Rowl.Datatypes.normative_supported N _,
      (Rowl.Datatypes.normative_in_kind N canonical .String).mp (by simp [InKind])⟩
  | Tagged t m => exact ⟨typeOf .Plain, Rowl.Datatypes.normative_supported N _,
      (Rowl.Datatypes.normative_in_kind N canonical .Plain).mp (by simp [InKind])⟩
  | Truth b => exact ⟨typeOf .Boolean, Rowl.Datatypes.normative_supported N _,
      (Rowl.Datatypes.normative_in_kind N canonical .Boolean).mp (by simp [InKind])⟩

theorem integer_decimal (N : Normative D) (y : Native) :
    D.valueSpace integerType y → D.valueSpace decimalType y := by
  rw [N.integer_space, N.decimal_space]
  rintro ⟨q, ⟨z, rfl⟩, rfl⟩
  exact ⟨z, ⟨z, 0, by simp⟩, rfl⟩

theorem string_plain (N : Normative D) (y : Native) : D.valueSpace stringType y → D.valueSpace plainType y := by
  rw [N.string_space, N.plain_space]
  exact .inl

theorem decimal_plain_apart (N : Normative D) (y : Native) :
    ¬ (D.valueSpace decimalType y ∧ D.valueSpace plainType y) := by
  rw [N.decimal_space, N.plain_space]
  rintro ⟨⟨q, _, rfl⟩, ⟨s, xs, same⟩ | ⟨s, l, xs, tl, same⟩⟩
  · exact N.number_text q s xs same
  · exact N.number_tagged q s l xs tl same

theorem decimal_boolean_apart (N : Normative D) (y : Native) :
    ¬ (D.valueSpace decimalType y ∧ D.valueSpace booleanType y) := by
  rw [N.decimal_space, N.boolean_space]
  rintro ⟨⟨q, _, rfl⟩, ⟨b, same⟩⟩
  exact N.number_truth q b same

theorem plain_boolean_apart (N : Normative D) (y : Native) :
    ¬ (D.valueSpace plainType y ∧ D.valueSpace booleanType y) := by
  rw [N.plain_space, N.boolean_space]
  rintro ⟨⟨s, xs, rfl⟩ | ⟨s, l, xs, tl, rfl⟩, ⟨b, same⟩⟩
  · exact N.text_truth s b xs same
  · exact N.tagged_truth s l b xs tl same

/-- The pairs of kinds whose datatypes the encoding keeps apart are apart. -/
theorem kinds_apart (N : Normative D) (y : Native) :
    (¬ (D.valueSpace integerType y ∧ D.valueSpace stringType y)) ∧
    (¬ (D.valueSpace integerType y ∧ D.valueSpace plainType y)) ∧
    (¬ (D.valueSpace integerType y ∧ D.valueSpace booleanType y)) ∧
    (¬ (D.valueSpace decimalType y ∧ D.valueSpace stringType y)) ∧
    (¬ (D.valueSpace decimalType y ∧ D.valueSpace plainType y)) ∧
    (¬ (D.valueSpace decimalType y ∧ D.valueSpace booleanType y)) ∧
    (¬ (D.valueSpace stringType y ∧ D.valueSpace booleanType y)) ∧
    (¬ (D.valueSpace plainType y ∧ D.valueSpace booleanType y)) := by
  have dp := decimal_plain_apart N y
  have db := decimal_boolean_apart N y
  have pb := plain_boolean_apart N y
  have id := integer_decimal N y
  have sp := string_plain N y
  refine ⟨fun h => dp ⟨id h.1, sp h.2⟩, fun h => dp ⟨id h.1, h.2⟩, fun h => db ⟨id h.1, h.2⟩,
    fun h => dp ⟨h.1, sp h.2⟩, dp, db, fun h => pb ⟨sp h.1, h.2⟩, pb⟩

end Values

/-! ### The interpretation of the encoding made from an OWL interpretation -/

section Lifted
variable {Object : Type u} {Value : Type v}

/-- The classes of a data node standing for a value: `owl:Thing`, `D`, the
    kinds' classes of the value's datatypes, and the bit classes of the index
    of its literal value. -/
def NodeClass (context : data_ontology.Context) (I : Interpretation Object Value)
    (lit : datatypes.DataValue → Value) (c : Class) (v : Value) : Prop :=
  c = thing ∨ c = dataClass ∨ (∃ k, c = kindClass k ∧ I.datatypes (typeOf k) v) ∨
    ∃ (j i : Usize) (_ : i.val < context.values.val.length), c = bitClass j ∧
      v = lit context.values.val[i.val] ∧ i.val.testBit j.val = true

/-- The interpretation of the encoding made from an OWL interpretation: its
    elements and its data values as the data nodes. -/
noncomputable def lifted (context : data_ontology.Context) (I : Interpretation Object Value)
    (lit : datatypes.DataValue → Value) (x0 : Object) : Interpretation (Object ⊕ Value) Value where
  objectsNonempty := ⟨.inl x0⟩
  dataNonempty := I.dataNonempty
  classes c y := match y with
    | .inl z => ¬ Reserved c.iri.spelling.val ∧ I.classes c z
    | .inr v => NodeClass context I lit c v
  objectProperties r y y' := match y, y' with
    | .inl z, .inl z' => ¬ Reserved r.iri.spelling.val ∧ I.objectProperties r z z'
    | .inl z, .inr v => r = topObject ∨ ∃ p, DataRoleOf p r ∧ I.dataProperties p z v
    | .inr _, _ => r = topObject
  dataProperties p _ _ := p = topData
  namedIndividuals a :=
    if h : ∃ i : Usize, i.val < context.values.val.length ∧ valueIndividual i = a then
      match context.values.val[(Classical.choose h).val]? with
      | some x => .inr (lit x)
      | none => .inl x0
    else if Reserved a.iri.spelling.val then .inl x0 else .inl (I.namedIndividuals a)
  anonymousIndividuals b := .inl (I.anonymousIndividuals b)
  datatypes := I.datatypes
  literals := I.literals
  facets := I.facets
  named := fun _ => True

variable {context : data_ontology.Context} {I : Interpretation Object Value} {lit : datatypes.DataValue → Value}
  {x0 : Object}

theorem lifted_value (i : Usize) (h : i.val < context.values.val.length) :
    (lifted context I lit x0).namedIndividuals (valueIndividual i) = .inr (lit context.values.val[i.val]) := by
  have ex : ∃ i' : Usize, i'.val < context.values.val.length ∧ valueIndividual i' = valueIndividual i := ⟨i, h, rfl⟩
  have chosen := value_individual_injective (Classical.choose_spec ex).2
  simp only [lifted, dif_pos ex, chosen, List.getElem?_eq_getElem h]

theorem lifted_plain_name {a : NamedIndividual} (plain : ¬ Reserved a.iri.spelling.val) :
    (lifted context I lit x0).namedIndividuals a = .inl (I.namedIndividuals a) := by
  have notValue : ¬ ∃ i : Usize, i.val < context.values.val.length ∧ valueIndividual i = a := by
    rintro ⟨i, _, rfl⟩
    exact plain (reserved_value i)
  simp only [lifted, dif_neg notValue, plain, ↓reduceIte]

theorem lifted_object : (lifted context I lit x0).namedIndividuals objectIndividual = .inl x0 := by
  have notValue : ¬ ∃ i : Usize, i.val < context.values.val.length ∧ valueIndividual i = objectIndividual := by
    rintro ⟨i, _, same⟩
    exact object_ne_value i same.symm
  simp only [lifted, dif_neg notValue, reserved_object, ↓reduceIte]

theorem node_kind (k : datatypes.Kind) (v : Value) :
    NodeClass context I lit (kindClass k) v ↔ I.datatypes (typeOf k) v := by
  constructor
  · rintro (h | h | ⟨k', same, holds⟩ | ⟨j, i, _, same, _⟩)
    · exact absurd h.symm (class_ne_of_reserved thing_plain (reserved_kind k))
    · exact absurd h.symm (data_ne_kind k)
    · rw [kind_class_injective same]; exact holds
    · exact absurd same (kind_ne_bit k j)
  · intro holds
    exact .inr (.inr (.inl ⟨k, rfl, holds⟩))

theorem node_bit (j : Usize) (v : Value) :
    NodeClass context I lit (bitClass j) v ↔ ∃ (i : Usize) (_ : i.val < context.values.val.length),
      v = lit context.values.val[i.val] ∧ i.val.testBit j.val = true := by
  constructor
  · rintro (h | h | ⟨k, same, _⟩ | ⟨j', i, hi, same, holds⟩)
    · exact absurd h.symm (class_ne_of_reserved thing_plain (reserved_bit j))
    · exact absurd h.symm (data_ne_bit j)
    · exact absurd same.symm (kind_ne_bit k j)
    · rw [bit_class_injective same]; exact ⟨i, hi, holds⟩
  · rintro ⟨i, hi, holds⟩
    exact .inr (.inr (.inr ⟨j, i, hi, rfl, holds⟩))

theorem node_plain {c : Class} (plain : ¬ Reserved c.iri.spelling.val) (notThing : c ≠ thing) (v : Value) :
    ¬ NodeClass context I lit c v := by
  rintro (h | h | ⟨k, h, _⟩ | ⟨j, i, _, h, _⟩)
  · exact notThing h
  · exact class_ne_of_reserved plain reserved_data h
  · exact class_ne_of_reserved plain (reserved_kind k) h
  · exact class_ne_of_reserved plain (reserved_bit j) h

theorem lifted_data_role (noBottom : ∀ z z', ¬ I.objectProperties bottomObject z z')
    (noBottomData : ∀ z v, ¬ I.dataProperties bottomData z v) {p : DataProperty} {role : ObjectPropertyExpression}
    (run : data_ontology.data_role context p = .ok (some role)) (z : Object) (y : Object ⊕ Value) :
    objectRelation (lifted context I lit x0) role (.inl z) y ↔ ∃ v, y = .inr v ∧ I.dataProperties p z v := by
  obtain ⟨res, run', facts⟩ := data_role_correct context p
  rw [run] at run'
  cases Result.ok_injective run'
  rcases facts role rfl with ⟨rfl, rfl⟩ | ⟨_, _, _, q, rfl, roleOf⟩
  · cases y with
    | inl z' => simp [objectRelation, lifted, noBottom]
    | inr v =>
      simp only [objectRelation, lifted]
      have notTop : bottomObject ≠ topObject := by
        rw [Ne, Rowl.Tableau.property_eq_iff]; simp [bottomObject, topObject]
      constructor
      · rintro (h | ⟨p', h, _⟩)
        · exact absurd h notTop
        · exact absurd (data_role_reserved h) bottom_plain
      · rintro ⟨v', _, holds⟩
        exact absurd holds (noBottomData z v')
  · have reserved := data_role_reserved roleOf
    cases y with
    | inl z' => simp [objectRelation, lifted, reserved]
    | inr v =>
      simp only [objectRelation, lifted]
      constructor
      · rintro (h | ⟨p', h, holds⟩)
        · exact absurd (h ▸ reserved) (by simp [Reserved, topObject])
        · exact ⟨v, rfl, data_role_injective h roleOf ▸ holds⟩
      · rintro ⟨v', same, holds⟩
        cases same
        exact .inr ⟨p, roleOf, holds⟩

end Lifted

/-! ### The lifted interpretation of an OWL model -/

section Model
variable {Object : Type u} {Value : Type v} {Native : Type w} {D : DatatypeMap Native}
  {embed : ValueEmbedding D Value} {V : Vocabulary} {I : Interpretation Object Value}
  {context : data_ontology.Context}

/-- The value of a literal value under the OWL 2 datatype map. -/
def litOf (N : Normative D) (embed : ValueEmbedding D Value) (x : datatypes.DataValue) : Value :=
  embed (valueOf N x)

theorem lit_kind (N : Normative D) (interp : IsInterpretation D embed V I) {x : datatypes.DataValue}
    (cx : Canonical x) (k : datatypes.Kind) : I.datatypes (typeOf k) (litOf N embed x) ↔ InKind x k := by
  obtain ⟨_, _, _, _, _, _, types, _⟩ := interp
  rw [types (typeOf k) (Rowl.Datatypes.normative_supported N k), Rowl.Datatypes.normative_in_kind N cx k]
  constructor
  · rintro ⟨y, inSpace, same⟩
    have := embed.injectiveValues y (valueOf N x) ⟨typeOf k, Rowl.Datatypes.normative_supported N k, inSpace⟩
      (value_datatype N cx) same
    rw [← this]
    exact inSpace
  · intro inSpace
    exact ⟨_, inSpace, rfl⟩

theorem lit_injective (N : Normative D) {x x' : datatypes.DataValue} (cx : Canonical x) (cx' : Canonical x')
    (same : litOf N embed x = litOf N embed x') : x = x' :=
  Rowl.Datatypes.value_injective N cx cx'
    (embed.injectiveValues _ _ (value_datatype N cx) (value_datatype N cx') same)

theorem lit_literal (N : Normative D) (vocab : IsVocabulary D V) (interp : IsInterpretation D embed V I)
    {lt : Literal} {x : datatypes.DataValue} (run : datatypes.literal_value lt = .ok (some x)) :
    I.literals lt = litOf N embed x := by
  obtain ⟨r, run', facts, _⟩ := Rowl.Datatypes.literal_value_correct lt
  rw [run] at run'
  cases Result.ok_injective run'
  obtain ⟨_, _, _, _, rest⟩ := facts x rfl
  obtain ⟨supported, lexical, value⟩ := rest D N
  obtain ⟨_, _, _, _, _, _, _, _, literals, _⟩ := vocab
  obtain ⟨_, _, _, _, _, _, _, _, values, _⟩ := interp
  rw [values lt ((literals lt).mpr ⟨supported, lexical⟩), value]
  rfl

theorem lifted_node (N : Normative D) (x0 : Object) (v : Value) :
    NodeValue context I (lifted context I (litOf N embed) x0) (litOf N embed) (.inr v) v where
  kinds := fun k _ => node_kind k v
  values := fun i h => by
    rw [lifted_value i h]
    simp [eq_comm]

theorem lifted_range_frame (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) :
    RangeFrame I (lifted context I (litOf N embed) x0) (litOf N embed) where
  literal := interp.2.2.2.2.2.2.2.1
  thing := fun y => by
    cases y with
    | inl z => exact ⟨thing_plain, interp.1 z⟩
    | inr v => exact .inl rfl
  literals := fun _ _ run => lit_literal N vocab interp run

theorem optional_range_meaning (context : data_ontology.Context) (range : Option DataRange)
    (filler : Option ClassExpression) (run : data_ontology.encode_optional_range context range = .ok (some filler)) :
    (range = none ∧ filler = none) ∨
      ∃ r c, range = some r ∧ filler = some c ∧ RangeMeans.{u,v,w,x} context r c := by
  cases range with
  | none =>
    left
    simp only [data_ontology.encode_optional_range, Result.ok.injEq, Option.some.injEq] at run
    exact ⟨rfl, run.symm⟩
  | some r =>
    obtain ⟨res, rangeRun, means⟩ := encode_range_meaning.{u,v,w,x} context r
    simp only [data_ontology.encode_optional_range, rangeRun, bind_ok] at run
    cases res with
    | none => simp at run
    | some c =>
      simp only [Result.ok.injEq, Option.some.injEq] at run
      right
      exact ⟨r, c, rfl, run.symm, means c rfl⟩

theorem lifted_filler (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) {range : Option DataRange} {filler : Option ClassExpression}
    (run : data_ontology.encode_optional_range context range = .ok (some filler)) (v : Value) :
    Rowl.Concepts.FillerHolds (lifted context I (litOf N embed) x0) filler (.inr v) ↔ RangeHolds I range v := by
  rcases optional_range_meaning.{u,v,max u v,v} context range filler run with ⟨rfl, rfl⟩ | ⟨r, c, rfl, rfl, means⟩
  · simp [Rowl.Concepts.FillerHolds, RangeHolds]
  · simp only [Rowl.Concepts.FillerHolds, RangeHolds]
    exact (means I _ _ (lifted_range_frame N x0 vocab interp) (.inr v) v (lifted_node N x0 v)).symm

theorem lifted_simulates (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) (good : Good context) (atoms : List (DataProperty × Option DataRange × Nat)) :
    Simulates context I (lifted context I (litOf N embed) x0) Sum.inl Plain atoms where
  injective := Sum.inl_injective
  objects := fun y => by
    cases y with
    | inl z => simp [lifted, reserved_data]
    | inr v => simp [lifted, NodeClass]
  classes := fun c z plain => by simp [lifted, plain]
  roles := fun r z y plain => by simp [lifted, plain]
  closed := fun r inContext y y' related => by
    obtain ⟨plain, notTop⟩ := good.2.1 r inContext
    cases y with
    | inl z =>
      cases y' with
      | inl z' => simp [lifted, reserved_data]
      | inr v =>
        simp only [lifted] at related
        rcases related with h | ⟨p, h, _⟩
        · exact absurd h notTop
        · exact absurd (data_role_reserved h) plain
    | inr v =>
      cases y' <;> (simp only [lifted] at related; exact absurd related notTop)
  topAll := fun y y' => by
    cases y with
    | inl z =>
      cases y' with
      | inl z' => exact ⟨topObject_plain, interp.2.2.1 z z'⟩
      | inr v => exact .inl rfl
    | inr v => cases y' <;> rfl
  individuals := fun a plain => by
    cases a with
    | Named n => exact lifted_plain_name plain
    | Anonymous b => rfl
  data := fun p range n _ role filler roleRun fillerRun z => by
    apply atLeast_image n _ _ Sum.inr Sum.inr_injective
    intro y
    rw [lifted_data_role interp.2.2.2.1 interp.2.2.2.2.2.1 roleRun z y]
    constructor
    · rintro ⟨⟨v, rfl, holds⟩, fill⟩
      exact ⟨v, rfl, holds, (lifted_filler N x0 vocab interp fillerRun v).mp fill⟩
    · rintro ⟨v, rfl, holds, range⟩
      exact ⟨⟨v, rfl, holds⟩, (lifted_filler N x0 vocab interp fillerRun v).mpr range⟩

theorem lifted_placed (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) :
    Placed context I (lifted context I (litOf N embed) x0) Sum.inl (litOf N embed) (fun _ v d => d = .inr v) where
  functional := fun _ _ _ _ h h' => h.trans h'.symm
  injective := fun _ _ _ _ h h' => Sum.inr_injective (h.symm.trans h')
  nodes := fun _ v d h => h ▸ lifted_node N x0 v
  data := fun p role run z v => by
    constructor
    · intro holds
      exact ⟨.inr v, rfl, (lifted_data_role interp.2.2.2.1 interp.2.2.2.2.2.1 run z _).mpr ⟨v, rfl, holds⟩⟩
    · rintro ⟨d, rfl, related⟩
      obtain ⟨v', same, holds⟩ := (lifted_data_role interp.2.2.2.1 interp.2.2.2.2.2.1 run z _).mp related
      cases same
      exact holds
  literals := fun z lt a run => by
    obtain ⟨res, run', facts⟩ := literal_individual_correct context lt
    rw [run] at run'
    cases Result.ok_injective run'
    obtain ⟨x, i, h, valueRun, at_i, rfl⟩ := facts a rfl
    simp only [individual]
    rw [lifted_value i h, at_i, lit_literal N vocab interp valueRun]
  top := fun z v => interp.2.2.2.2.1 z v

theorem lifted_inert (N : Normative D) (x0 : Object) (interp : IsInterpretation D embed V I) :
    Inert context (lifted context I (litOf N embed) x0) Sum.inl (fun _ v d => d = .inr v) where
  classes := fun c y plain notThing dataNode => by
    cases y with
    | inl z => exact absurd dataNode.1 (by simp [reserved_data])
    | inr v => exact node_plain plain notThing v
  sources := fun p role run y y' related => by
    cases y with
    | inl z => simp [lifted, reserved_data]
    | inr v =>
      exfalso
      obtain ⟨res, run', facts⟩ := data_role_correct context p
      rw [run] at run'
      cases Result.ok_injective run'
      rcases facts role rfl with ⟨_, rfl⟩ | ⟨_, _, _, q, rfl, roleOf⟩
      · have notTop : bottomObject ≠ topObject := by
          rw [Ne, Rowl.Tableau.property_eq_iff]; simp [bottomObject, topObject]
        cases y' <;> exact notTop related
      · have reserved := data_role_reserved roleOf
        have notTop : q ≠ topObject := fun h => by rw [h] at reserved; exact topObject_plain reserved
        cases y' <;> exact notTop related
  placed := fun p role run z d related => by
    obtain ⟨v, same, _⟩ := (lifted_data_role interp.2.2.2.1 interp.2.2.2.2.2.1 run z d).mp related
    exact ⟨v, same⟩

end Model

section Satisfaction
variable {Object : Type u} {Value : Type v} {Native : Type w} {D : DatatypeMap Native}
  {embed : ValueEmbedding D Value} {V : Vocabulary} {I : Interpretation Object Value}
  {context : data_ontology.Context}

theorem lifted_included (N : Normative D) (x0 : Object) (interp : IsInterpretation D embed V I)
    {a b : datatypes.Kind} (sub : ∀ y, D.valueSpace (typeOf a) y → D.valueSpace (typeOf b) y) (y : Object ⊕ Value) :
    (lifted context I (litOf N embed) x0).classes (kindClass a) y →
      (lifted context I (litOf N embed) x0).classes (kindClass b) y := by
  obtain ⟨_, _, _, _, _, _, types, _⟩ := interp
  cases y with
  | inl z => exact fun h => absurd (reserved_kind a) h.1
  | inr v =>
    change NodeClass context I (litOf N embed) (kindClass a) v → NodeClass context I (litOf N embed) (kindClass b) v
    rw [node_kind, node_kind, types _ (Rowl.Datatypes.normative_supported N a),
      types _ (Rowl.Datatypes.normative_supported N b)]
    rintro ⟨y0, inSpace, rfl⟩
    exact ⟨y0, sub y0 inSpace, rfl⟩

theorem lifted_apart (N : Normative D) (x0 : Object) (interp : IsInterpretation D embed V I)
    {a b : datatypes.Kind} (disjoint : ∀ y, ¬ (D.valueSpace (typeOf a) y ∧ D.valueSpace (typeOf b) y))
    (y : Object ⊕ Value) :
    ¬ ((lifted context I (litOf N embed) x0).classes (kindClass a) y ∧
      (lifted context I (litOf N embed) x0).classes (kindClass b) y) := by
  obtain ⟨_, _, _, _, _, _, types, _⟩ := interp
  cases y with
  | inl z => exact fun h => absurd (reserved_kind a) h.1.1
  | inr v =>
    change ¬ (NodeClass context I (litOf N embed) (kindClass a) v ∧ NodeClass context I (litOf N embed) (kindClass b) v)
    rw [node_kind, node_kind, types _ (Rowl.Datatypes.normative_supported N a),
      types _ (Rowl.Datatypes.normative_supported N b)]
    rintro ⟨⟨y1, s1, e1⟩, ⟨y2, s2, e2⟩⟩
    have same := embed.injectiveValues y1 y2 ⟨_, Rowl.Datatypes.normative_supported N a, s1⟩
      ⟨_, Rowl.Datatypes.normative_supported N b, s2⟩ (e1.trans e2.symm)
    subst same
    exact disjoint y1 ⟨s1, s2⟩

theorem lifted_frame (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) (good : Good context) (known : TruthsKnown context) (bits : Usize) :
    Frame context bits (lifted context I (litOf N embed) x0) where
  roles := (lifted_simulates N x0 vocab interp good []).closed
  data := fun p _ role run y y' related => by
    cases y with
    | inl z =>
      obtain ⟨v, rfl, _⟩ := (lifted_data_role interp.2.2.2.1 interp.2.2.2.2.2.1 run z y').mp related
      exact ⟨fun h => absurd reserved_data h.1, .inr (.inl rfl)⟩
    | inr v =>
      exact absurd (show NodeClass context I (litOf N embed) dataClass v from .inr (.inl rfl))
        ((lifted_inert N x0 interp).sources p role run _ _ related)
  kinds := by
    have apart := kinds_apart N
    exact {
      integerDecimal := fun _ _ y => lifted_included N x0 interp (a := .Integer) (b := .Decimal) (integer_decimal N) y
      stringPlain := fun _ _ y => lifted_included N x0 interp (a := .String) (b := .Plain) (string_plain N) y
      integerString := fun _ _ y => lifted_apart N x0 interp (a := .Integer) (b := .String) (fun y => (apart y).1) y
      integerPlain := fun _ _ y => lifted_apart N x0 interp (a := .Integer) (b := .Plain) (fun y => (apart y).2.1) y
      integerBoolean := fun _ _ y => lifted_apart N x0 interp (a := .Integer) (b := .Boolean) (fun y => (apart y).2.2.1) y
      decimalString := fun _ _ y => lifted_apart N x0 interp (a := .Decimal) (b := .String) (fun y => (apart y).2.2.2.1) y
      decimalPlain := fun _ _ y => lifted_apart N x0 interp (a := .Decimal) (b := .Plain) (fun y => (apart y).2.2.2.2.1) y
      decimalBoolean := fun _ _ y => lifted_apart N x0 interp (a := .Decimal) (b := .Boolean) (fun y => (apart y).2.2.2.2.2.1) y
      stringBoolean := fun _ _ y => lifted_apart N x0 interp (a := .String) (b := .Boolean) (fun y => (apart y).2.2.2.2.2.2.1) y
      plainBoolean := fun _ _ y => lifted_apart N x0 interp (a := .Plain) (b := .Boolean) (fun y => (apart y).2.2.2.2.2.2.2) y
      truths := fun boolean y holds => by
        obtain ⟨_, _, _, _, _, _, types, _⟩ := interp
        cases y with
        | inl z => exact absurd (reserved_kind _) holds.1
        | inr v =>
          change NodeClass context I (litOf N embed) (kindClass .Boolean) v at holds
          rw [node_kind, types _ (Rowl.Datatypes.normative_supported N .Boolean)] at holds
          obtain ⟨y0, inSpace, rfl⟩ := holds
          obtain ⟨b, rfl⟩ := (N.boolean_space y0).mp inSpace
          obtain ⟨i, h, at_i⟩ := known boolean b
          refine ⟨i, h, by cases b <;> simp [at_i], ?_⟩
          rw [lifted_value i h, at_i]
          rfl }
  values := fun i h => by
    have canonical := good.1.1 _ (List.getElem_mem h)
    refine ⟨?_, fun k _ => ?_, fun j _ => ?_⟩
    · rw [lifted_value i h]
      exact .inr (.inl rfl)
    · rw [lifted_value i h]
      exact (node_kind k _).trans (lit_kind N interp canonical k)
    · rw [lifted_value i h]
      change NodeClass context I (litOf N embed) (bitClass j) _ ↔ _
      rw [node_bit]
      constructor
      · rintro ⟨i', h', same, bitHolds⟩
        have := lit_injective N canonical (good.1.1 _ (List.getElem_mem h')) same
        have := value_index_unique (hi := h) (hj := h') good this
        subst this
        exact bitHolds
      · intro bitHolds
        exact ⟨i, h, rfl, bitHolds⟩
  object := by
    rw [lifted_object]
    exact fun h => absurd reserved_data h.1

theorem lifted_interpretation (N : Normative D) (x0 : Object) (interp : IsInterpretation D embed V I) :
    IsInterpretation D embed V (lifted context I (litOf N embed) x0) := by
  obtain ⟨hThing, hNothing, hTop, hBottom, hTopData, hBottomData, hTypes, hLiteral, hLiterals, hFacets, _⟩ := interp
  have notTop : bottomObject ≠ topObject := by
    rw [Ne, Rowl.Tableau.property_eq_iff]; simp [bottomObject, topObject]
  have notTopData : bottomData ≠ topData := by
    rw [Ne, dataProperty_eq_iff]; simp [bottomData, topData]
  refine ⟨fun y => ?_, fun y => ?_, fun y y' => ?_, fun y y' => ?_, fun _ _ => rfl, fun _ _ h => notTopData h,
    hTypes, hLiteral, hLiterals, hFacets, fun _ _ => trivial⟩
  · cases y with
    | inl z => exact ⟨thing_plain, hThing z⟩
    | inr v => exact .inl rfl
  · cases y with
    | inl z => exact fun h => hNothing z h.2
    | inr v => exact node_plain nothing_plain thing_ne_nothing.symm v
  · cases y with
    | inl z =>
      cases y' with
      | inl z' => exact ⟨topObject_plain, hTop z z'⟩
      | inr v => exact .inl rfl
    | inr v => cases y' <;> rfl
  · cases y with
    | inl z =>
      cases y' with
      | inl z' => exact fun h => hBottom z z' h.2
      | inr v =>
        rintro (h | ⟨p, h, _⟩)
        · exact notTop h
        · exact bottom_plain (data_role_reserved h)
    | inr v => cases y' <;> exact notTop

/-- An OWL interpretation that satisfies a closure lifts to an interpretation
    of the closure's encoding that satisfies it. -/
theorem lifted_satisfies (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) (good : Good context) (items enc : alloc.vec.Vec AnnotatedAxiom)
    (run : data_ontology.encode context items = .ok (some enc)) (satisfied : satisfiesClosure I items.val) :
    ∀ b ∈ enc.val, satisfies (lifted context I (litOf N embed) x0) b.axiom := by
  obtain ⟨res, run', facts⟩ := encode_meaning.{u,v,max u v,v} context good items
  rw [run] at run'
  cases Result.ok_injective run'
  obtain ⟨new, bits, means, _, _, known, iff⟩ := facts enc rfl
  rw [iff]
  refine ⟨?_, lifted_frame N x0 vocab interp good known bits⟩
  exact (means.1 I _ Sum.inl Plain (items.val.flatMap (fun i => axiomAtoms i.axiom)) (litOf N embed) _
    (lifted_simulates N x0 vocab interp good _) (lifted_placed N x0 vocab interp)
    (lifted_range_frame N x0 vocab interp)
    (fun item mem a inside => List.mem_flatMap.mpr ⟨item, mem, inside⟩) means.2.1).2
    (lifted_inert N x0 interp) satisfied

/-- A class expression's encoding holds at an element of the lifted
    interpretation exactly when the expression holds at it. -/
theorem lifted_class (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) (good : Good context) {c c' : ClassExpression}
    (run : data_ontology.encode_class context c = .ok (some c')) (plain : ∀ a ∈ classIndividuals c, Plain a)
    (z : Object) : classDenote I c z ↔ classDenote (lifted context I (litOf N embed) x0) c' (.inl z) := by
  obtain ⟨res, run', means⟩ := encode_class_meaning.{u,v,max u v,v} context c
  rw [run] at run'
  cases Result.ok_injective run'
  exact means c' rfl I _ Sum.inl Plain (classAtoms c) (lifted_simulates N x0 vocab interp good _)
    (fun _ h => h) plain z

theorem lifted_element (N : Normative D) (x0 : Object) (z : Object) :
    ¬ (lifted context I (litOf N embed) x0).classes dataClass (.inl z) :=
  fun h => absurd reserved_data h.1

end Satisfaction

end Rowl.DataComplete
