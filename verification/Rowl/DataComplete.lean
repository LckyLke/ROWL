import Rowl.DataStructure
import Mathlib.Data.Int.Interval

/-!
Models of `data_ontology`'s encoding made from OWL models. An OWL
interpretation's elements and its data values become the elements and the data
nodes of an interpretation of the encoding (`lifted`): the data properties
become their roles from the elements to the values, each kind's class holds at
the values of its datatype, each literal value's individual is its value with
the bit classes of its index, each cut's class holds at the reals in the cut,
the role `U` relates each element to the values of the context's data
properties at it, and every other name keeps its meaning at the elements
(`lifted_regions` for the axioms of the cuts). When the OWL interpretation
satisfies a closure, the lifted one
satisfies its encoding (`lifted_satisfies`), and every class expression's
encoding holds at an element exactly when the expression does
(`lifted_class`).
-/
namespace Rowl.DataComplete
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DatatypeMap (Normative IsInteger IsDecimal integerType decimalType stringType plainType booleanType
  realType)
open Rowl.Datatypes (Canonical valueOf typeOf kindOf InKind)
open Rowl.AlcOntology (RoleOf)
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.DataStructure
open Rowl.DataRegions
open Rowl.Regions (cutAt Ordered FineCuts InCut firstIn lastOutside)
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

theorem reserved_cut (i : Usize) : Reserved (cutClass i).iri.spelling.val := by
  simp [Reserved, cutClass_name, cutName]

theorem cut_class_injective {i i' : Usize} (same : cutClass i = cutClass i') : i = i' := by
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp only [cutClass_name, cutName, List.cons.injEq, true_and] at this
  exact UScalar.eq_of_val_eq (eightBytes_injective _ _ 8 (usize_bytes i) (usize_bytes i') this)

theorem data_ne_cut (i : Usize) : dataClass ≠ cutClass i := by
  intro same
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp [dataClass_name, cutClass_name, dataName, cutName] at this

theorem kind_ne_cut (k : datatypes.Kind) (i : Usize) : kindClass k ≠ cutClass i := by
  intro same
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp [kindClass_name, cutClass_name, kindName, cutName] at this

theorem bit_ne_cut (j i : Usize) : bitClass j ≠ cutClass i := by
  intro same
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp [bitClass_name, cutClass_name, bitName, cutName] at this

theorem reserved_super : Reserved dataSuper.iri.spelling.val := by simp [Reserved, dataSuper_name, superName]

theorem super_ne_top : dataSuper ≠ topObject := fun same => by
  have := reserved_super; rw [same] at this; exact topObject_plain this

theorem super_ne_bottom : dataSuper ≠ bottomObject := fun same => by
  have := reserved_super; rw [same] at this; exact bottom_plain this

theorem super_ne_role {p : DataProperty} {q : ObjectProperty} (h : DataRoleOf p q) : dataSuper ≠ q := by
  intro same
  have := congrArg (fun r : ObjectProperty => r.iri.spelling.val) same
  simp only [dataSuper_name] at this
  rw [h] at this
  simp [superName, dataRoleName] at this

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
      (Rowl.Datatypes.normative_in_kind N canonical .Decimal).mp (by simp [InKind, Rowl.Datatypes.NumberIn])⟩
  | Fraction n a b => exact ⟨typeOf .Rational, Rowl.Datatypes.normative_supported N _,
      (Rowl.Datatypes.normative_in_kind N canonical .Rational).mp (by simp [InKind])⟩
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

theorem numeric_included (N : Normative D) {a b : datatypes.Kind} (na : Rowl.Datatypes.IsNumeric a)
    (nb : Rowl.Datatypes.IsNumeric b) (sub : ∀ r, Rowl.Datatypes.RealIn a r → Rowl.Datatypes.RealIn b r) (y : Native) :
    D.valueSpace (typeOf a) y → D.valueSpace (typeOf b) y := by
  rw [Rowl.Datatypes.numeric_space N a na, Rowl.Datatypes.numeric_space N b nb]
  rintro ⟨r, rfl, inA⟩
  exact ⟨r, rfl, sub r inA⟩

theorem real_of_numeric (N : Normative D) {a : datatypes.Kind} (na : Rowl.Datatypes.IsNumeric a) {y : Native}
    (inside : D.valueSpace (typeOf a) y) : ∃ r, y = N.real r := by
  obtain ⟨r, rfl, _⟩ := (Rowl.Datatypes.numeric_space N a na y).mp inside
  exact ⟨r, rfl⟩

theorem numeric_apart (N : Normative D) {a : datatypes.Kind} (na : Rowl.Datatypes.IsNumeric a) (y : Native) :
    ¬ (D.valueSpace (typeOf a) y ∧ D.valueSpace stringType y) ∧
    ¬ (D.valueSpace (typeOf a) y ∧ D.valueSpace plainType y) ∧
    ¬ (D.valueSpace (typeOf a) y ∧ D.valueSpace booleanType y) := by
  refine ⟨fun ⟨h, s⟩ => ?_, fun ⟨h, s⟩ => ?_, fun ⟨h, s⟩ => ?_⟩ <;> obtain ⟨r, rfl⟩ := real_of_numeric N na h
  · obtain ⟨t, xs, same⟩ := (N.string_space _).mp s
    exact N.real_text r t xs same
  · rcases (N.plain_space _).mp s with ⟨t, xs, same⟩ | ⟨t, l, xs, tl, same⟩
    · exact N.real_text r t xs same
    · exact N.real_tagged r t l xs tl same
  · obtain ⟨b, same⟩ := (N.boolean_space _).mp s
    exact N.real_truth r b same

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
    (lit : datatypes.DataValue → Value) (num : ℝ → Value) (c : Class) (v : Value) : Prop :=
  c = thing ∨ c = dataClass ∨ (∃ k, c = kindClass k ∧ I.datatypes (typeOf k) v) ∨
    (∃ (j i : Usize) (_ : i.val < context.values.val.length), c = bitClass j ∧
      v = lit context.values.val[i.val] ∧ i.val.testBit j.val = true) ∨
    ∃ (i : Usize) (_ : i.val < context.cuts.val.length), c = cutClass i ∧
      ∃ r, v = num r ∧ InCut context.cuts.val[i.val] r

/-- The interpretation of the encoding made from an OWL interpretation: its
    elements and its data values as the data nodes, with `U` relating each
    element to the values of the context's data properties at it. -/
noncomputable def lifted (context : data_ontology.Context) (I : Interpretation Object Value)
    (lit : datatypes.DataValue → Value) (num : ℝ → Value) (x0 : Object) : Interpretation (Object ⊕ Value) Value where
  objectsNonempty := ⟨.inl x0⟩
  dataNonempty := I.dataNonempty
  classes c y := match y with
    | .inl z => ¬ Reserved c.iri.spelling.val ∧ I.classes c z
    | .inr v => NodeClass context I lit num c v
  objectProperties r y y' := match y, y' with
    | .inl z, .inl z' => ¬ Reserved r.iri.spelling.val ∧ I.objectProperties r z z'
    | .inl z, .inr v => r = topObject ∨ (∃ p, DataRoleOf p r ∧ I.dataProperties p z v) ∨
        (r = dataSuper ∧ ∃ p ∈ context.data.val, I.dataProperties p z v)
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
  {num : ℝ → Value} {x0 : Object}

theorem lifted_value (i : Usize) (h : i.val < context.values.val.length) :
    (lifted context I lit num x0).namedIndividuals (valueIndividual i) = .inr (lit context.values.val[i.val]) := by
  have ex : ∃ i' : Usize, i'.val < context.values.val.length ∧ valueIndividual i' = valueIndividual i := ⟨i, h, rfl⟩
  have chosen := value_individual_injective (Classical.choose_spec ex).2
  simp only [lifted, dif_pos ex, chosen, List.getElem?_eq_getElem h]

theorem lifted_plain_name {a : NamedIndividual} (plain : ¬ Reserved a.iri.spelling.val) :
    (lifted context I lit num x0).namedIndividuals a = .inl (I.namedIndividuals a) := by
  have notValue : ¬ ∃ i : Usize, i.val < context.values.val.length ∧ valueIndividual i = a := by
    rintro ⟨i, _, rfl⟩
    exact plain (reserved_value i)
  simp only [lifted, dif_neg notValue, plain, ↓reduceIte]

theorem lifted_object : (lifted context I lit num x0).namedIndividuals objectIndividual = .inl x0 := by
  have notValue : ¬ ∃ i : Usize, i.val < context.values.val.length ∧ valueIndividual i = objectIndividual := by
    rintro ⟨i, _, same⟩
    exact object_ne_value i same.symm
  simp only [lifted, dif_neg notValue, reserved_object, ↓reduceIte]

theorem node_kind (k : datatypes.Kind) (v : Value) :
    NodeClass context I lit num (kindClass k) v ↔ I.datatypes (typeOf k) v := by
  constructor
  · rintro (h | h | ⟨k', same, holds⟩ | ⟨j, i, _, same, _⟩ | ⟨i, _, same, _⟩)
    · exact absurd h.symm (class_ne_of_reserved thing_plain (reserved_kind k))
    · exact absurd h.symm (data_ne_kind k)
    · rw [kind_class_injective same]; exact holds
    · exact absurd same (kind_ne_bit k j)
    · exact absurd same (kind_ne_cut k i)
  · intro holds
    exact .inr (.inr (.inl ⟨k, rfl, holds⟩))

theorem node_bit (j : Usize) (v : Value) :
    NodeClass context I lit num (bitClass j) v ↔ ∃ (i : Usize) (_ : i.val < context.values.val.length),
      v = lit context.values.val[i.val] ∧ i.val.testBit j.val = true := by
  constructor
  · rintro (h | h | ⟨k, same, _⟩ | ⟨j', i, hi, same, holds⟩ | ⟨i, _, same, _⟩)
    · exact absurd h.symm (class_ne_of_reserved thing_plain (reserved_bit j))
    · exact absurd h.symm (data_ne_bit j)
    · exact absurd same.symm (kind_ne_bit k j)
    · rw [bit_class_injective same]; exact ⟨i, hi, holds⟩
    · exact absurd same (bit_ne_cut j i)
  · rintro ⟨i, hi, holds⟩
    exact .inr (.inr (.inr (.inl ⟨j, i, hi, rfl, holds⟩)))

theorem node_cut (i : Usize) (h : i.val < context.cuts.val.length) (v : Value) :
    NodeClass context I lit num (cutClass i) v ↔ ∃ r, v = num r ∧ InCut context.cuts.val[i.val] r := by
  constructor
  · rintro (h' | h' | ⟨k, same, _⟩ | ⟨j, i', _, same, _⟩ | ⟨i', hi', same, holds⟩)
    · exact absurd h'.symm (class_ne_of_reserved thing_plain (reserved_cut i))
    · exact absurd h'.symm (data_ne_cut i)
    · exact absurd same.symm (kind_ne_cut k i)
    · exact absurd same.symm (bit_ne_cut j i)
    · have := cut_class_injective same
      subst this
      exact holds
  · intro holds
    exact .inr (.inr (.inr (.inr ⟨i, h, rfl, holds⟩)))

theorem node_plain {c : Class} (plain : ¬ Reserved c.iri.spelling.val) (notThing : c ≠ thing) (v : Value) :
    ¬ NodeClass context I lit num c v := by
  rintro (h | h | ⟨k, h, _⟩ | ⟨j, i, _, h, _⟩ | ⟨i, _, h, _⟩)
  · exact notThing h
  · exact class_ne_of_reserved plain reserved_data h
  · exact class_ne_of_reserved plain (reserved_kind k) h
  · exact class_ne_of_reserved plain (reserved_bit j) h
  · exact class_ne_of_reserved plain (reserved_cut i) h

theorem lifted_data_role (noBottom : ∀ z z', ¬ I.objectProperties bottomObject z z')
    (noBottomData : ∀ z v, ¬ I.dataProperties bottomData z v) {p : DataProperty} {role : ObjectPropertyExpression}
    (run : data_ontology.data_role context p = .ok (some role)) (z : Object) (y : Object ⊕ Value) :
    objectRelation (lifted context I lit num x0) role (.inl z) y ↔ ∃ v, y = .inr v ∧ I.dataProperties p z v := by
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
      · rintro (h | ⟨p', h, _⟩ | ⟨h, _⟩)
        · exact absurd h notTop
        · exact absurd (data_role_reserved h) bottom_plain
        · exact absurd h.symm super_ne_bottom
      · rintro ⟨v', _, holds⟩
        exact absurd holds (noBottomData z v')
  · have reserved := data_role_reserved roleOf
    cases y with
    | inl z' => simp [objectRelation, lifted, reserved]
    | inr v =>
      simp only [objectRelation, lifted]
      constructor
      · rintro (h | ⟨p', h, holds⟩ | ⟨h, _⟩)
        · exact absurd (h ▸ reserved) (by simp [Reserved, topObject])
        · exact ⟨v, rfl, data_role_injective h roleOf ▸ holds⟩
        · exact absurd h.symm (super_ne_role roleOf)
      · rintro ⟨v', same, holds⟩
        cases same
        exact .inr (.inl ⟨p, roleOf, holds⟩)

end Lifted

/-! ### The lifted interpretation of an OWL model -/

section Model
variable {Object : Type u} {Value : Type v} {Native : Type w} {D : DatatypeMap Native}
  {embed : ValueEmbedding D Value} {V : Vocabulary} {I : Interpretation Object Value}
  {context : data_ontology.Context}

/-- The value of a literal value under the OWL 2 datatype map. -/
def litOf (N : Normative D) (embed : ValueEmbedding D Value) (x : datatypes.DataValue) : Value :=
  embed (valueOf N x)

/-- The value of a real number under the OWL 2 datatype map. -/
def numOf (N : Normative D) (embed : ValueEmbedding D Value) (r : ℝ) : Value := embed (N.real r)

theorem real_datatype (N : Normative D) (r : ℝ) : isDatatypeValue D (N.real r) :=
  ⟨typeOf .Real, Rowl.Datatypes.normative_supported N _,
    (Rowl.Datatypes.numeric_space N .Real (by simp [Rowl.Datatypes.IsNumeric]) _).mpr
      ⟨r, rfl, by simp [Rowl.Datatypes.RealIn]⟩⟩

theorem num_injective (N : Normative D) : Function.Injective (numOf N embed) := fun a b same =>
  N.real_injective (embed.injectiveValues _ _ (real_datatype N a) (real_datatype N b) same)

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
    NodeValue context I (lifted context I (litOf N embed) (numOf N embed) x0) (litOf N embed) (numOf N embed)
      (.inr v) v where
  kinds := fun k _ => node_kind k v
  values := fun i h => by
    rw [lifted_value i h]
    simp [eq_comm]
  cuts := fun _ i h => node_cut i h v

theorem facetOf_some {iri : Iri} {F : datatypes.Facet} (h : Rowl.Datatypes.facetOf iri = some F) :
    iri = Rowl.Datatypes.facetIri F := by
  unfold Rowl.Datatypes.facetOf at h
  split_ifs at h with h1 h2 h3 h4 <;> cases h <;> assumption

/-- The facet values of a range facet with a real bound, as reals. -/
theorem facet_reals (N : Normative D) (F : datatypes.Facet) (c : ℚ) (y : Native) :
    D.facetValue (Rowl.Datatypes.facetIri F) (N.real c) y ↔ ∃ s, y = N.real s ∧ FacetReal F c s := by
  cases F
  · rw [Rowl.Datatypes.facetIri, N.min_inclusive_value]
    constructor
    · rintro ⟨s, le, rfl⟩; exact ⟨s, rfl, le⟩
    · rintro ⟨s, rfl, le⟩; exact ⟨s, le, rfl⟩
  · rw [Rowl.Datatypes.facetIri, N.max_inclusive_value]
    constructor
    · rintro ⟨s, le, rfl⟩; exact ⟨s, rfl, le⟩
    · rintro ⟨s, rfl, le⟩; exact ⟨s, le, rfl⟩
  · rw [Rowl.Datatypes.facetIri, N.min_exclusive_value]
    constructor
    · rintro ⟨s, le, rfl⟩; exact ⟨s, rfl, le⟩
    · rintro ⟨s, rfl, le⟩; exact ⟨s, le, rfl⟩
  · rw [Rowl.Datatypes.facetIri, N.max_exclusive_value]
    constructor
    · rintro ⟨s, le, rfl⟩; exact ⟨s, rfl, le⟩
    · rintro ⟨s, rfl, le⟩; exact ⟨s, le, rfl⟩

theorem lifted_range_frame (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) :
    RangeFrame I (lifted context I (litOf N embed) (numOf N embed) x0) (litOf N embed) (numOf N embed) where
  literal := interp.2.2.2.2.2.2.2.1
  thing := fun y => by
    cases y with
    | inl z => exact ⟨thing_plain, interp.1 z⟩
    | inr v => exact .inl rfl
  literals := fun _ _ run => lit_literal N vocab interp run
  injective := num_injective N
  numbers := fun w nw => by simp [litOf, numOf, Rowl.Datatypes.valueOf_number N nw]
  numeric := fun k nk x => by
    obtain ⟨_, _, _, _, _, _, types, _⟩ := interp
    rw [types (typeOf k) (Rowl.Datatypes.normative_supported N k)]
    constructor
    · rintro ⟨y, inside, rfl⟩
      obtain ⟨r, rfl, inK⟩ := (Rowl.Datatypes.numeric_space N k nk y).mp inside
      exact ⟨r, rfl, inK⟩
    · rintro ⟨r, rfl, inK⟩
      exact ⟨N.real r, (Rowl.Datatypes.numeric_space N k nk _).mpr ⟨r, rfl, inK⟩, rfl⟩
  facets := fun f F w facet run number x => by
    obtain ⟨r, run', facts, _⟩ := Rowl.Datatypes.literal_value_correct f.value
    rw [run] at run'
    cases Result.ok_injective run'
    obtain ⟨_, _, _, _, rest⟩ := facts w rfl
    obtain ⟨supported, lexical, value⟩ := rest D N
    have lexValue : D.lexicalValue f.value.datatype f.value.lexical.val = N.real (Rowl.Datatypes.numValue w) := by
      rw [value, Rowl.Datatypes.valueOf_number N number]
    have inV : V.facets f := by
      obtain ⟨_, _, _, _, _, _, _, _, literals, facetsV⟩ := vocab
      refine (facetsV f).mpr ⟨(literals _).mpr ⟨supported, lexical⟩, realType, N.real_supported, ?_⟩
      rw [N.real_facets, lexValue, facetOf_some facet]
      exact ⟨Rowl.Datatypes.facetIri_range F, _, rfl⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, facetsI, _⟩ := interp
    rw [facetsI f inV x, lexValue, facetOf_some facet]
    constructor
    · rintro ⟨y, holds, rfl⟩
      obtain ⟨s, rfl, real⟩ := (facet_reals N F _ y).mp holds
      exact ⟨s, rfl, real⟩
    · rintro ⟨s, rfl, real⟩
      exact ⟨N.real s, (facet_reals N F _ _).mpr ⟨s, rfl, real⟩, rfl⟩

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
    Rowl.Concepts.FillerHolds (lifted context I (litOf N embed) (numOf N embed) x0) filler (.inr v) ↔ RangeHolds I range v := by
  rcases optional_range_meaning.{u,v,max u v,v} context range filler run with ⟨rfl, rfl⟩ | ⟨r, c, rfl, rfl, means⟩
  · simp [Rowl.Concepts.FillerHolds, RangeHolds]
  · simp only [Rowl.Concepts.FillerHolds, RangeHolds]
    exact (means I _ _ _ (lifted_range_frame N x0 vocab interp) (.inr v) v (lifted_node N x0 v)).symm

theorem lifted_simulates (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) (good : Good context) (atoms : List (DataProperty × Option DataRange × Nat)) :
    Simulates context I (lifted context I (litOf N embed) (numOf N embed) x0) Sum.inl Plain atoms where
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
        rcases related with h | ⟨p, h, _⟩ | ⟨h, _⟩
        · exact absurd h notTop
        · exact absurd (data_role_reserved h) plain
        · exact absurd (h ▸ reserved_super) plain
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
    Placed context I (lifted context I (litOf N embed) (numOf N embed) x0) Sum.inl (litOf N embed) (numOf N embed)
      (fun _ v d => d = .inr v) where
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
    Inert context (lifted context I (litOf N embed) (numOf N embed) x0) Sum.inl (fun _ v d => d = .inr v) where
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
    (lifted context I (litOf N embed) (numOf N embed) x0).classes (kindClass a) y →
      (lifted context I (litOf N embed) (numOf N embed) x0).classes (kindClass b) y := by
  obtain ⟨_, _, _, _, _, _, types, _⟩ := interp
  cases y with
  | inl z => exact fun h => absurd (reserved_kind a) h.1
  | inr v =>
    change NodeClass context I (litOf N embed) (numOf N embed) (kindClass a) v → NodeClass context I (litOf N embed) (numOf N embed) (kindClass b) v
    rw [node_kind, node_kind, types _ (Rowl.Datatypes.normative_supported N a),
      types _ (Rowl.Datatypes.normative_supported N b)]
    rintro ⟨y0, inSpace, rfl⟩
    exact ⟨y0, sub y0 inSpace, rfl⟩

theorem lifted_apart (N : Normative D) (x0 : Object) (interp : IsInterpretation D embed V I)
    {a b : datatypes.Kind} (disjoint : ∀ y, ¬ (D.valueSpace (typeOf a) y ∧ D.valueSpace (typeOf b) y))
    (y : Object ⊕ Value) :
    ¬ ((lifted context I (litOf N embed) (numOf N embed) x0).classes (kindClass a) y ∧
      (lifted context I (litOf N embed) (numOf N embed) x0).classes (kindClass b) y) := by
  obtain ⟨_, _, _, _, _, _, types, _⟩ := interp
  cases y with
  | inl z => exact fun h => absurd (reserved_kind a) h.1.1
  | inr v =>
    change ¬ (NodeClass context I (litOf N embed) (numOf N embed) (kindClass a) v ∧ NodeClass context I (litOf N embed) (numOf N embed) (kindClass b) v)
    rw [node_kind, node_kind, types _ (Rowl.Datatypes.normative_supported N a),
      types _ (Rowl.Datatypes.normative_supported N b)]
    rintro ⟨⟨y1, s1, e1⟩, ⟨y2, s2, e2⟩⟩
    have same := embed.injectiveValues y1 y2 ⟨_, Rowl.Datatypes.normative_supported N a, s1⟩
      ⟨_, Rowl.Datatypes.normative_supported N b, s2⟩ (e1.trans e2.symm)
    subst same
    exact disjoint y1 ⟨s1, s2⟩

theorem cut_value_number (good : Good context) {i : Nat} (h : i < context.cuts.val.length) :
    Rowl.Datatypes.IsNumber context.cuts.val[i].value :=
  Rowl.Regions.number_of_canonical (good.2.2.2.1.1 _ (List.getElem_mem h))

theorem lifted_cut_node (N : Normative D) (x0 : Object) {i : Usize} (h : i.val < context.cuts.val.length)
    {y : Object ⊕ Value} (holds : (lifted context I (litOf N embed) (numOf N embed) x0).classes (cutClass i) y) :
    ∃ r, y = .inr (numOf N embed r) ∧ InCut context.cuts.val[i.val] r := by
  cases y with
  | inl z => exact absurd (reserved_cut i) holds.1
  | inr v =>
    obtain ⟨r, rfl, inCut⟩ := (node_cut i h v).mp holds
    exact ⟨r, rfl, inCut⟩

/-- The lifted interpretation satisfies the axioms of the ordered numbers. -/
theorem lifted_regions (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) (good : Good context) (capacity : Nat) (order : List Usize)
    (sorted : context.kinds.ordered = true → Ordered context.cuts.val (order.map (·.val))) :
    RegionFacts context capacity order (lifted context I (litOf N embed) (numOf N embed) x0) := by
  intro ordered
  obtain ⟨_, inside, _, chain⟩ := sorted ordered
  have frame := lifted_range_frame (context := context) N x0 vocab interp
  have orderIn : ∀ k ∈ order, k.val < context.cuts.val.length := fun k m =>
    inside k.val (List.mem_map_of_mem m)
  have consecutive : ∀ (p : Nat) (h : p < order.length), 0 < p →
      Rowl.Regions.CutBefore (cutAt context.cuts.val order[p - 1].val) (cutAt context.cuts.val order[p].val) := by
    intro p h pos
    have := (List.isChain_iff_getElem.mp chain) (p - 1) (by simp; omega)
    simpa [show p - 1 + 1 = p by omega] using this
  refine ⟨fun first head y holds => ?_, fun p h _ pos => ?_, fun _ k hk _ role run y y' rel => ?_⟩
  · have firstIn : first.val < context.cuts.val.length := orderIn first (List.mem_of_mem_head? head)
    obtain ⟨r, rfl, _⟩ := lifted_cut_node N x0 firstIn holds
    change NodeClass context I (litOf N embed) (numOf N embed) (kindClass .Real) (numOf N embed r)
    rw [node_kind, frame.numeric .Real (by simp [Rowl.Datatypes.IsNumeric])]
    exact ⟨r, rfl, by simp [Rowl.Datatypes.RealIn]⟩
  · have hl := orderIn _ (List.getElem_mem (show p - 1 < order.length by omega))
    have hh := orderIn _ (List.getElem_mem h)
    have before := consecutive p h pos
    rw [cutAt_val hl, cutAt_val hh] at before
    refine ⟨fun y holds => ?_, ⟨fun same i hi at_i y inLow notHigh => ?_, fun differ integer => ⟨?_, ?_⟩⟩⟩
    · obtain ⟨r, rfl, inHigh⟩ := lifted_cut_node N x0 hh holds
      exact (node_cut _ hl _).mpr ⟨r, rfl, Rowl.Regions.in_cut_mono before r inHigh⟩
    · rw [cutAt_val hl] at at_i same
      rw [cutAt_val hh] at same
      obtain ⟨r, rfl, inLow'⟩ := lifted_cut_node N x0 hl inLow
      have sides : context.cuts.val[order[p - 1].val].open = false ∧ context.cuts.val[order[p].val].open = true := by
        rcases before with lt | ⟨_, lo, hi⟩
        · rw [same] at lt; exact absurd lt (lt_irrefl _)
        · exact ⟨lo, hi⟩
      have notOver : ¬ InCut context.cuts.val[order[p].val] r := fun inHigh =>
        notHigh ((node_cut _ hh _).mpr ⟨r, rfl, inHigh⟩)
      simp only [InCut, sides, ↓reduceIte, Bool.false_eq_true, not_lt] at inLow' notOver
      rw [← same] at notOver
      have eq : r = (Rowl.Datatypes.numValue context.cuts.val[order[p - 1].val].value : ℝ) := le_antisymm notOver inLow'
      rw [lifted_value i hi, at_i, frame.numbers _ (cut_value_number good hl), eq]
    · intro zero y integerY inLow
      by_contra notHigh
      obtain ⟨r, rfl, inLow'⟩ := lifted_cut_node N x0 hl inLow
      change NodeClass context I (litOf N embed) (numOf N embed) (kindClass .Integer) (numOf N embed r) at integerY
      rw [node_kind, frame.numeric .Integer (by simp [Rowl.Datatypes.IsNumeric])] at integerY
      obtain ⟨r', same, z, rfl⟩ := integerY
      have := frame.injective same
      subst this
      have notOver : ¬ InCut context.cuts.val[order[p].val] (z : ℝ) := fun inHigh =>
        notHigh ((node_cut _ hh _).mpr ⟨z, rfl, inHigh⟩)
      have between := (Rowl.Regions.in_cuts_iff _ _ z).mp ⟨inLow', notOver⟩
      rw [cutAt_val hl, cutAt_val hh] at zero
      simp only [runCount] at zero
      omega
    · intro pos' fewer y _ ⟨f, injective, each⟩
      have count := runCount (cutAt context.cuts.val order[p - 1].val) (cutAt context.cuts.val order[p].val)
      have members : ∀ i, ∃ z : ℤ, f i = .inr (numOf N embed z) ∧
          z ∈ Finset.Icc (firstIn context.cuts.val[order[p - 1].val]) (lastOutside context.cuts.val[order[p].val]) := by
        intro i
        obtain ⟨_, integerY, inLow, notHigh⟩ := each i
        obtain ⟨r, same, inLow'⟩ := lifted_cut_node N x0 hl inLow
        rw [same] at integerY notHigh
        change NodeClass context I (litOf N embed) (numOf N embed) (kindClass .Integer) (numOf N embed r) at integerY
        rw [node_kind, frame.numeric .Integer (by simp [Rowl.Datatypes.IsNumeric])] at integerY
        obtain ⟨r', same', z, rfl⟩ := integerY
        have := frame.injective same'
        subst this
        have notOver : ¬ InCut context.cuts.val[order[p].val] (z : ℝ) := fun inHigh =>
          notHigh ((node_cut _ hh _).mpr ⟨z, rfl, inHigh⟩)
        exact ⟨z, same, Finset.mem_Icc.mpr ((Rowl.Regions.in_cuts_iff _ _ z).mp ⟨inLow', notOver⟩)⟩
      choose g gf gin using members
      have gInjective : Function.Injective (fun i => (⟨g i, gin i⟩ : Finset.Icc (firstIn context.cuts.val[order[p - 1].val])
          (lastOutside context.cuts.val[order[p].val]))) := by
        intro i j same
        simp only [Subtype.mk.injEq] at same
        apply injective
        rw [gf i, gf j, same]
      have := Fintype.card_le_of_injective _ gInjective
      simp only [Fintype.card_fin, Finset.coe_sort_coe, Fintype.card_coe, Int.card_Icc] at this
      rw [cutAt_val hl, cutAt_val hh] at this
      simp only [runCount] at this
      have eq : lastOutside context.cuts.val[order[p].val] + 1 - firstIn context.cuts.val[order[p - 1].val] =
          lastOutside context.cuts.val[order[p].val] - firstIn context.cuts.val[order[p - 1].val] + 1 := by ring
      rw [eq] at this
      omega
  · have inData := List.getElem_mem hk
    cases y with
    | inl z =>
      obtain ⟨v, rfl, holds⟩ := (lifted_data_role interp.2.2.2.1 interp.2.2.2.2.2.1 run z y').mp rel
      exact .inr (.inr ⟨rfl, _, inData, holds⟩)
    | inr v =>
      exact absurd (show NodeClass context I (litOf N embed) (numOf N embed) dataClass v from .inr (.inl rfl))
        ((lifted_inert N x0 interp).sources _ role run _ _ rel)

theorem lifted_frame (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) (good : Good context) (known : TruthsKnown context) (capacity : Nat)
    (bits : Usize) (order : List Usize)
    (sorted : context.kinds.ordered = true → Ordered context.cuts.val (order.map (·.val))) :
    Frame context capacity bits order (lifted context I (litOf N embed) (numOf N embed) x0) where
  roles := (lifted_simulates N x0 vocab interp good []).closed
  data := fun p _ role run y y' related => by
    cases y with
    | inl z =>
      obtain ⟨v, rfl, _⟩ := (lifted_data_role interp.2.2.2.1 interp.2.2.2.2.2.1 run z y').mp related
      exact ⟨fun h => absurd reserved_data h.1, .inr (.inl rfl)⟩
    | inr v =>
      exact absurd (show NodeClass context I (litOf N embed) (numOf N embed) dataClass v from .inr (.inl rfl))
        ((lifted_inert N x0 interp).sources p role run _ _ related)
  kinds := by
    have apart := kinds_apart N
    exact {
      integerDecimal := fun _ _ y => lifted_included N x0 interp (a := .Integer) (b := .Decimal) (integer_decimal N) y
      integerRational := fun _ _ y => lifted_included N x0 interp (a := .Integer) (b := .Rational)
        (numeric_included N (by simp [Rowl.Datatypes.IsNumeric]) (by simp [Rowl.Datatypes.IsNumeric])
          (fun r ⟨z, h⟩ => ⟨z, by rw [h]; simp⟩)) y
      integerReal := fun _ _ y => lifted_included N x0 interp (a := .Integer) (b := .Real)
        (numeric_included N (by simp [Rowl.Datatypes.IsNumeric]) (by simp [Rowl.Datatypes.IsNumeric])
          (fun _ _ => trivial)) y
      decimalRational := fun _ _ y => lifted_included N x0 interp (a := .Decimal) (b := .Rational)
        (numeric_included N (by simp [Rowl.Datatypes.IsNumeric]) (by simp [Rowl.Datatypes.IsNumeric])
          (fun r ⟨z, n, h⟩ => ⟨(z : ℚ) / 10 ^ n, by rw [h]; push_cast; rfl⟩)) y
      decimalReal := fun _ _ y => lifted_included N x0 interp (a := .Decimal) (b := .Real)
        (numeric_included N (by simp [Rowl.Datatypes.IsNumeric]) (by simp [Rowl.Datatypes.IsNumeric])
          (fun _ _ => trivial)) y
      rationalReal := fun _ _ y => lifted_included N x0 interp (a := .Rational) (b := .Real)
        (numeric_included N (by simp [Rowl.Datatypes.IsNumeric]) (by simp [Rowl.Datatypes.IsNumeric])
          (fun _ _ => trivial)) y
      stringPlain := fun _ _ y => lifted_included N x0 interp (a := .String) (b := .Plain) (string_plain N) y
      integerString := fun _ _ y => lifted_apart N x0 interp (a := .Integer) (b := .String) (fun y => (apart y).1) y
      integerPlain := fun _ _ y => lifted_apart N x0 interp (a := .Integer) (b := .Plain) (fun y => (apart y).2.1) y
      integerBoolean := fun _ _ y => lifted_apart N x0 interp (a := .Integer) (b := .Boolean) (fun y => (apart y).2.2.1) y
      decimalString := fun _ _ y => lifted_apart N x0 interp (a := .Decimal) (b := .String) (fun y => (apart y).2.2.2.1) y
      decimalPlain := fun _ _ y => lifted_apart N x0 interp (a := .Decimal) (b := .Plain) (fun y => (apart y).2.2.2.2.1) y
      decimalBoolean := fun _ _ y => lifted_apart N x0 interp (a := .Decimal) (b := .Boolean) (fun y => (apart y).2.2.2.2.2.1) y
      rationalString := fun _ _ y => lifted_apart N x0 interp (a := .Rational) (b := .String)
        (fun y => (numeric_apart N (a := .Rational) (by simp [Rowl.Datatypes.IsNumeric]) y).1) y
      rationalPlain := fun _ _ y => lifted_apart N x0 interp (a := .Rational) (b := .Plain)
        (fun y => (numeric_apart N (a := .Rational) (by simp [Rowl.Datatypes.IsNumeric]) y).2.1) y
      rationalBoolean := fun _ _ y => lifted_apart N x0 interp (a := .Rational) (b := .Boolean)
        (fun y => (numeric_apart N (a := .Rational) (by simp [Rowl.Datatypes.IsNumeric]) y).2.2) y
      realString := fun _ _ y => lifted_apart N x0 interp (a := .Real) (b := .String)
        (fun y => (numeric_apart N (a := .Real) (by simp [Rowl.Datatypes.IsNumeric]) y).1) y
      realPlain := fun _ _ y => lifted_apart N x0 interp (a := .Real) (b := .Plain)
        (fun y => (numeric_apart N (a := .Real) (by simp [Rowl.Datatypes.IsNumeric]) y).2.1) y
      realBoolean := fun _ _ y => lifted_apart N x0 interp (a := .Real) (b := .Boolean)
        (fun y => (numeric_apart N (a := .Real) (by simp [Rowl.Datatypes.IsNumeric]) y).2.2) y
      stringBoolean := fun _ _ y => lifted_apart N x0 interp (a := .String) (b := .Boolean) (fun y => (apart y).2.2.2.2.2.2.1) y
      plainBoolean := fun _ _ y => lifted_apart N x0 interp (a := .Plain) (b := .Boolean) (fun y => (apart y).2.2.2.2.2.2.2) y
      truths := fun boolean y holds => by
        obtain ⟨_, _, _, _, _, _, types, _⟩ := interp
        cases y with
        | inl z => exact absurd (reserved_kind _) holds.1
        | inr v =>
          change NodeClass context I (litOf N embed) (numOf N embed) (kindClass .Boolean) v at holds
          rw [node_kind, types _ (Rowl.Datatypes.normative_supported N .Boolean)] at holds
          obtain ⟨y0, inSpace, rfl⟩ := holds
          obtain ⟨b, rfl⟩ := (N.boolean_space y0).mp inSpace
          obtain ⟨i, h, at_i⟩ := known boolean b
          refine ⟨i, h, by cases b <;> simp [at_i], ?_⟩
          rw [lifted_value i h, at_i]
          rfl }
  regions := lifted_regions N x0 vocab interp good capacity order sorted
  values := fun i h => by
    have canonical := good.1.1 _ (List.getElem_mem h)
    refine ⟨?_, fun k _ => ?_, fun j _ => ?_, fun _ number a b ha hb aIs bIs => ?_⟩
    · rw [lifted_value i h]
      exact .inr (.inl rfl)
    · rw [lifted_value i h]
      exact (node_kind k _).trans (lit_kind N interp canonical k)
    · rw [lifted_value i h]
      change NodeClass context I (litOf N embed) (numOf N embed) (bitClass j) _ ↔ _
      rw [node_bit]
      constructor
      · rintro ⟨i', h', same, bitHolds⟩
        have := lit_injective N canonical (good.1.1 _ (List.getElem_mem h')) same
        have := value_index_unique (hi := h) (hj := h') good this
        subst this
        exact bitHolds
      · intro bitHolds
        exact ⟨i, h, rfl, bitHolds⟩
    · have frame := lifted_range_frame (context := context) N x0 vocab interp
      rw [lifted_value i h]
      change NodeClass context I (litOf N embed) (numOf N embed) (cutClass a) _ ∧
        ¬ NodeClass context I (litOf N embed) (numOf N embed) (cutClass b) _
      rw [node_cut a ha, node_cut b hb, aIs, bIs, frame.numbers _ number]
      refine ⟨⟨_, rfl, by simp [InCut]⟩, fun ⟨r, same, over⟩ => ?_⟩
      have := frame.injective same
      subst this
      simp [InCut] at over
  object := by
    rw [lifted_object]
    exact fun h => absurd reserved_data h.1

theorem lifted_interpretation (N : Normative D) (x0 : Object) (interp : IsInterpretation D embed V I) :
    IsInterpretation D embed V (lifted context I (litOf N embed) (numOf N embed) x0) := by
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
        rintro (h | ⟨p, h, _⟩ | ⟨h, _⟩)
        · exact notTop h
        · exact bottom_plain (data_role_reserved h)
        · exact super_ne_bottom h.symm
    | inr v => cases y' <;> exact notTop

/-- An OWL interpretation that satisfies a closure lifts to an interpretation
    of the closure's encoding that satisfies it. -/
theorem lifted_satisfies (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) (good : Good context) (capacity : Usize)
    (capSmall : capacity.val < Usize.max / 16) (items enc : alloc.vec.Vec AnnotatedAxiom)
    (run : data_ontology.encode context capacity items = .ok (some enc)) (satisfied : satisfiesClosure I items.val) :
    ∀ b ∈ enc.val, satisfies (lifted context I (litOf N embed) (numOf N embed) x0) b.axiom := by
  obtain ⟨res, run', facts⟩ := encode_meaning.{u,v,max u v,v} context good capacity capSmall items
  rw [run] at run'
  cases Result.ok_injective run'
  obtain ⟨_, _, new, bits, order, means, _, sorted, _, known, iff⟩ := facts enc rfl
  rw [iff]
  refine ⟨?_, lifted_frame N x0 vocab interp good known capacity.val bits order (fun o => (sorted o).1)⟩
  exact (means.1 I _ Sum.inl Plain (items.val.flatMap (fun i => axiomAtoms i.axiom)) (litOf N embed) (numOf N embed) _
    (lifted_simulates N x0 vocab interp good _) (lifted_placed N x0 vocab interp)
    (lifted_range_frame N x0 vocab interp)
    (fun item mem a inside => List.mem_flatMap.mpr ⟨item, mem, inside⟩) means.2.1).2
    (lifted_inert N x0 interp) satisfied

/-- A class expression's encoding holds at an element of the lifted
    interpretation exactly when the expression holds at it. -/
theorem lifted_class (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) (good : Good context) {c c' : ClassExpression}
    (run : data_ontology.encode_class context c = .ok (some c')) (plain : ∀ a ∈ classIndividuals c, Plain a)
    (z : Object) : classDenote I c z ↔ classDenote (lifted context I (litOf N embed) (numOf N embed) x0) c' (.inl z) := by
  obtain ⟨res, run', means⟩ := encode_class_meaning.{u,v,max u v,v} context c
  rw [run] at run'
  cases Result.ok_injective run'
  exact means c' rfl I _ Sum.inl Plain (classAtoms c) (lifted_simulates N x0 vocab interp good _)
    (fun _ h => h) plain z

theorem lifted_element (N : Normative D) (x0 : Object) (z : Object) :
    ¬ (lifted context I (litOf N embed) (numOf N embed) x0).classes dataClass (.inl z) :=
  fun h => absurd reserved_data h.1

end Satisfaction

end Rowl.DataComplete
