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
  realType Moment dateTimeType dateTimeStampType Binary doubleFormat floatFormat)
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

theorem reserved_edge (double : Bool) (i : Usize) : Reserved (edgeClass double i).iri.spelling.val := by
  simp [Reserved, edgeClass_name, edgeName]

theorem edge_class_injective {d d' : Bool} {i i' : Usize} (same : edgeClass d i = edgeClass d' i') :
    d = d' ∧ i = i' := by
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp only [edgeClass_name, edgeName, List.cons.injEq, true_and] at this
  refine ⟨?_, UScalar.eq_of_val_eq (eightBytes_injective _ _ 8 (usize_bytes i) (usize_bytes i') this.2)⟩
  cases d <;> cases d' <;> simp_all

theorem data_ne_edge (d : Bool) (i : Usize) : dataClass ≠ edgeClass d i := by
  intro same
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp [dataClass_name, edgeClass_name, dataName, edgeName] at this

theorem kind_ne_edge (k : datatypes.Kind) (d : Bool) (i : Usize) : kindClass k ≠ edgeClass d i := by
  intro same
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp [kindClass_name, edgeClass_name, kindName, edgeName] at this

theorem bit_ne_edge (j : Usize) (d : Bool) (i : Usize) : bitClass j ≠ edgeClass d i := by
  intro same
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp [bitClass_name, edgeClass_name, bitName, edgeName] at this

theorem cut_ne_edge (j : Usize) (d : Bool) (i : Usize) : cutClass j ≠ edgeClass d i := by
  intro same
  have := congrArg (fun c : Class => c.iri.spelling.val) same
  simp [cutClass_name, edgeClass_name, cutName, edgeName] at this

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
      (Rowl.Datatypes.normative_in_kind N canonical .String).mp (by simp [InKind, Rowl.Strings.TextIn])⟩
  | Tagged t m => exact ⟨typeOf .Plain, Rowl.Datatypes.normative_supported N _,
      (Rowl.Datatypes.normative_in_kind N canonical .Plain).mp (by simp [InKind])⟩
  | Truth b => exact ⟨typeOf .Boolean, Rowl.Datatypes.normative_supported N _,
      (Rowl.Datatypes.normative_in_kind N canonical .Boolean).mp (by simp [InKind])⟩
  | Uri t => exact ⟨typeOf .AnyUri, Rowl.Datatypes.normative_supported N _,
      (Rowl.Datatypes.normative_in_kind N canonical .AnyUri).mp (by simp [InKind])⟩
  | Hex o => exact ⟨typeOf .HexBinary, Rowl.Datatypes.normative_supported N _,
      (Rowl.Datatypes.normative_in_kind N canonical .HexBinary).mp (by simp [InKind])⟩
  | Base64 o => exact ⟨typeOf .Base64Binary, Rowl.Datatypes.normative_supported N _,
      (Rowl.Datatypes.normative_in_kind N canonical .Base64Binary).mp (by simp [InKind])⟩
  | Moment x => exact ⟨typeOf .DateTime, Rowl.Datatypes.normative_supported N _,
      (Rowl.Datatypes.normative_in_kind N canonical .DateTime).mp (by simp [InKind])⟩
  | Double x => exact ⟨typeOf .Double, Rowl.Datatypes.normative_supported N _,
      (Rowl.Datatypes.normative_in_kind N canonical .Double).mp (by simp [InKind])⟩
  | Float x => exact ⟨typeOf .Float, Rowl.Datatypes.normative_supported N _,
      (Rowl.Datatypes.normative_in_kind N canonical .Float).mp (by simp [InKind])⟩

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

/-- The kinds whose values are IRIs or octet sequences. -/
def IsCoded : datatypes.Kind → Prop
  | .AnyUri | .HexBinary | .Base64Binary => True
  | _ => False

/-- The kind of a `Coded` value. -/
def codedKind : DatatypeMap.Coded → datatypes.Kind
  | .uri _ => .AnyUri
  | .hex _ => .HexBinary
  | .base64 _ => .Base64Binary

/-- The values of a kind of IRIs or octet sequences are `Coded` values proper
    of that kind. -/
theorem coded_of_kind (N : Normative D) {k : datatypes.Kind} (ck : IsCoded k) {y : Native}
    (inside : D.valueSpace (typeOf k) y) : ∃ c : DatatypeMap.Coded, c.Valid ∧ codedKind c = k ∧ y = N.coded c := by
  cases k <;> simp only [IsCoded] at ck
  case AnyUri =>
    obtain ⟨s, xs, rfl⟩ := (N.uri_space _).mp inside
    exact ⟨.uri s, xs, rfl, rfl⟩
  case HexBinary =>
    obtain ⟨o, rfl⟩ := (N.hex_space _).mp inside
    exact ⟨.hex o, trivial, rfl, rfl⟩
  case Base64Binary =>
    obtain ⟨o, rfl⟩ := (N.base64_space _).mp inside
    exact ⟨.base64 o, trivial, rfl, rfl⟩

/-- No value of another kind is a `Coded` value proper. -/
theorem not_coded (N : Normative D) {k : datatypes.Kind} (ck : ¬ IsCoded k) {y : Native}
    (inside : D.valueSpace (typeOf k) y) (c : DatatypeMap.Coded) (valid : c.Valid) : y ≠ N.coded c := by
  by_cases numeric : Rowl.Datatypes.IsNumeric k
  · obtain ⟨r, rfl⟩ := real_of_numeric N numeric inside
    exact N.real_coded r c valid
  · cases k <;> simp only [IsCoded, Rowl.Datatypes.IsNumeric, not_true_eq_false, not_false_eq_true] at ck numeric
    case String =>
      obtain ⟨s, xs, rfl⟩ := (N.string_space _).mp inside
      exact N.text_coded s c xs valid
    case Plain =>
      rcases (N.plain_space _).mp inside with ⟨s, xs, rfl⟩ | ⟨s, l, xs, tl, rfl⟩
      · exact N.text_coded s c xs valid
      · exact N.tagged_coded s l c xs tl valid
    case Boolean =>
      obtain ⟨b, rfl⟩ := (N.boolean_space _).mp inside
      exact N.truth_coded b c valid
    case DateTime =>
      obtain ⟨m, mv, rfl⟩ := (N.datetime_space _).mp inside
      exact fun e => N.coded_moment c m valid mv e.symm
    case DateTimeStamp =>
      obtain ⟨m, mv, _, rfl⟩ := (N.stamp_space _).mp inside
      exact fun e => N.coded_moment c m valid mv e.symm
    case Double =>
      obtain ⟨b, bv, rfl⟩ := (N.double_space _).mp inside
      exact fun e => N.coded_double c b valid bv e.symm
    case Float =>
      obtain ⟨b, bv, rfl⟩ := (N.float_space _).mp inside
      exact fun e => N.coded_float c b valid bv e.symm
    all_goals
      obtain ⟨t, f, rfl⟩ := (Rowl.Datatypes.subtype_space_iff N rfl _).mp inside
      exact N.text_coded t c (Rowl.Strings.form_xml f) valid

/-- The value space of a kind of the chain: the strings of its lexical forms. -/
theorem chain_space (N : Normative D) {i : Nat} (hi : i < 7) (y : Native) :
    D.valueSpace (typeOf (chainKind i)) y ↔ ∃ t, Rowl.Strings.ChainForm i t ∧ y = N.text t := by
  match i, hi with
  | 0, _ => exact N.string_space y
  | 1, _ => exact Rowl.Datatypes.subtype_space_iff N (k := .NormalizedString) rfl y
  | 2, _ => exact Rowl.Datatypes.subtype_space_iff N (k := .Token) rfl y
  | 3, _ => exact Rowl.Datatypes.subtype_space_iff N (k := .NmToken) rfl y
  | 4, _ => exact Rowl.Datatypes.subtype_space_iff N (k := .Name) rfl y
  | 5, _ => exact Rowl.Datatypes.subtype_space_iff N (k := .NcName) rfl y
  | 6, _ => exact Rowl.Datatypes.subtype_space_iff N (k := .Language) rfl y

/-- A kind of the chain is included in the kinds before it. -/
theorem chain_included (N : Normative D) {i j : Nat} (lt : j < i) (hi : i < 7) (y : Native) :
    D.valueSpace (typeOf (chainKind i)) y → D.valueSpace (typeOf (chainKind j)) y := by
  intro inside
  obtain ⟨t, f, rfl⟩ := (chain_space N hi y).mp inside
  exact (chain_space N (by omega) _).mpr ⟨t, Rowl.Strings.chain_form_mono (by omega) f, rfl⟩

/-- A kind of IRIs or octet sequences is apart from every other kind. -/
theorem coded_apart (N : Normative D) {a b : datatypes.Kind} (ca : IsCoded a) (ne : a ≠ b) (y : Native) :
    ¬ (D.valueSpace (typeOf a) y ∧ D.valueSpace (typeOf b) y) := by
  rintro ⟨inA, inB⟩
  obtain ⟨c, valid, kindIs, rfl⟩ := coded_of_kind N ca inA
  by_cases cb : IsCoded b
  · obtain ⟨c', valid', kindIs', same⟩ := coded_of_kind N cb inB
    have := N.coded_injective c c' valid valid' same
    subst this
    exact ne (kindIs.symm.trans kindIs')
  · exact not_coded N cb inB c valid rfl

/-- The kinds whose values are time instants. -/
def IsMomentKind : datatypes.Kind → Prop
  | .DateTime | .DateTimeStamp => True
  | _ => False

/-- The values of a kind of time instants are moments proper. -/
theorem moment_of_kind (N : Normative D) {k : datatypes.Kind} (mk : IsMomentKind k) {y : Native}
    (inside : D.valueSpace (typeOf k) y) : ∃ m : Moment, m.Valid ∧ y = N.moment m := by
  cases k <;> simp only [IsMomentKind] at mk
  case DateTime =>
    obtain ⟨m, mv, rfl⟩ := (N.datetime_space _).mp inside
    exact ⟨m, mv, rfl⟩
  case DateTimeStamp =>
    obtain ⟨m, mv, _, rfl⟩ := (N.stamp_space _).mp inside
    exact ⟨m, mv, rfl⟩

/-- No value of another kind is a moment proper. -/
theorem not_moment (N : Normative D) {k : datatypes.Kind} (mk : ¬ IsMomentKind k) {y : Native}
    (inside : D.valueSpace (typeOf k) y) (m : Moment) (valid : m.Valid) : y ≠ N.moment m := by
  by_cases numeric : Rowl.Datatypes.IsNumeric k
  · obtain ⟨r, rfl⟩ := real_of_numeric N numeric inside
    exact N.real_moment r m valid
  · by_cases ck : IsCoded k
    · obtain ⟨c, cv, _, rfl⟩ := coded_of_kind N ck inside
      exact N.coded_moment c m cv valid
    · cases k <;> simp only [IsMomentKind, IsCoded, Rowl.Datatypes.IsNumeric, not_true_eq_false,
        not_false_eq_true] at mk ck numeric
      case String =>
        obtain ⟨s, xs, rfl⟩ := (N.string_space _).mp inside
        exact N.text_moment s m xs valid
      case Plain =>
        rcases (N.plain_space _).mp inside with ⟨s, xs, rfl⟩ | ⟨s, l, xs, tl, rfl⟩
        · exact N.text_moment s m xs valid
        · exact N.tagged_moment s l m xs tl valid
      case Boolean =>
        obtain ⟨b, rfl⟩ := (N.boolean_space _).mp inside
        exact N.truth_moment b m valid
      case Double =>
        obtain ⟨b, bv, rfl⟩ := (N.double_space _).mp inside
        exact fun e => N.moment_double m b valid bv e.symm
      case Float =>
        obtain ⟨b, bv, rfl⟩ := (N.float_space _).mp inside
        exact fun e => N.moment_float m b valid bv e.symm
      all_goals
        obtain ⟨t, f, rfl⟩ := (Rowl.Datatypes.subtype_space_iff N rfl _).mp inside
        exact N.text_moment t m (Rowl.Strings.form_xml f) valid

/-- A kind of time instants is apart from every other kind. -/
theorem moment_apart (N : Normative D) {a b : datatypes.Kind} (ma : IsMomentKind a) (mb : ¬ IsMomentKind b)
    (y : Native) : ¬ (D.valueSpace (typeOf a) y ∧ D.valueSpace (typeOf b) y) := by
  rintro ⟨inA, inB⟩
  obtain ⟨m, mv, rfl⟩ := moment_of_kind N ma inA
  exact not_moment N mb inB m mv rfl

/-- The time stamps are time instants. -/
theorem stamp_datetime (N : Normative D) (y : Native) :
    D.valueSpace dateTimeStampType y → D.valueSpace dateTimeType y := by
  rw [N.stamp_space, N.datetime_space]
  rintro ⟨m, mv, _, rfl⟩
  exact ⟨m, mv, rfl⟩

/-- No value of another kind is a value of `xsd:double`. -/
theorem not_double (N : Normative D) {k : datatypes.Kind} (ne : k ≠ .Double) {y : Native}
    (inside : D.valueSpace (typeOf k) y) (b : Binary) (valid : b.Valid doubleFormat) : y ≠ N.double b := by
  by_cases numeric : Rowl.Datatypes.IsNumeric k
  · obtain ⟨r, rfl⟩ := real_of_numeric N numeric inside
    exact N.real_double r b valid
  · by_cases ck : IsCoded k
    · obtain ⟨c, cv, _, rfl⟩ := coded_of_kind N ck inside
      exact N.coded_double c b cv valid
    · by_cases mk : IsMomentKind k
      · obtain ⟨m, mv, rfl⟩ := moment_of_kind N mk inside
        exact N.moment_double m b mv valid
      · cases k <;> simp only [IsMomentKind, IsCoded, Rowl.Datatypes.IsNumeric, not_true_eq_false,
          not_false_eq_true, ne_eq, not_true_eq_false] at mk ck numeric ne
        case String =>
          obtain ⟨s, xs, rfl⟩ := (N.string_space _).mp inside
          exact N.text_double s b xs valid
        case Plain =>
          rcases (N.plain_space _).mp inside with ⟨s, xs, rfl⟩ | ⟨s, l, xs, tl, rfl⟩
          · exact N.text_double s b xs valid
          · exact N.tagged_double s l b xs tl valid
        case Boolean =>
          obtain ⟨c, rfl⟩ := (N.boolean_space _).mp inside
          exact N.truth_double c b valid
        case Float =>
          obtain ⟨a, av, rfl⟩ := (N.float_space _).mp inside
          exact fun e => N.double_float b a valid av e.symm
        all_goals
          obtain ⟨t, f, rfl⟩ := (Rowl.Datatypes.subtype_space_iff N rfl _).mp inside
          exact N.text_double t b (Rowl.Strings.form_xml f) valid

/-- No value of another kind is a value of `xsd:float`. -/
theorem not_float (N : Normative D) {k : datatypes.Kind} (ne : k ≠ .Float) {y : Native}
    (inside : D.valueSpace (typeOf k) y) (b : Binary) (valid : b.Valid floatFormat) : y ≠ N.float b := by
  by_cases numeric : Rowl.Datatypes.IsNumeric k
  · obtain ⟨r, rfl⟩ := real_of_numeric N numeric inside
    exact N.real_float r b valid
  · by_cases ck : IsCoded k
    · obtain ⟨c, cv, _, rfl⟩ := coded_of_kind N ck inside
      exact N.coded_float c b cv valid
    · by_cases mk : IsMomentKind k
      · obtain ⟨m, mv, rfl⟩ := moment_of_kind N mk inside
        exact N.moment_float m b mv valid
      · cases k <;> simp only [IsMomentKind, IsCoded, Rowl.Datatypes.IsNumeric, not_true_eq_false,
          not_false_eq_true, ne_eq, not_true_eq_false] at mk ck numeric ne
        case String =>
          obtain ⟨s, xs, rfl⟩ := (N.string_space _).mp inside
          exact N.text_float s b xs valid
        case Plain =>
          rcases (N.plain_space _).mp inside with ⟨s, xs, rfl⟩ | ⟨s, l, xs, tl, rfl⟩
          · exact N.text_float s b xs valid
          · exact N.tagged_float s l b xs tl valid
        case Boolean =>
          obtain ⟨c, rfl⟩ := (N.boolean_space _).mp inside
          exact N.truth_float c b valid
        case Double =>
          obtain ⟨a, av, rfl⟩ := (N.double_space _).mp inside
          exact N.double_float a b av valid
        all_goals
          obtain ⟨t, f, rfl⟩ := (Rowl.Datatypes.subtype_space_iff N rfl _).mp inside
          exact N.text_float t b (Rowl.Strings.form_xml f) valid

/-- `xsd:double` is apart from every other kind. -/
theorem double_apart (N : Normative D) {b : datatypes.Kind} (ne : b ≠ .Double) (y : Native) :
    ¬ (D.valueSpace (typeOf .Double) y ∧ D.valueSpace (typeOf b) y) := by
  rintro ⟨inA, inB⟩
  obtain ⟨a, av, rfl⟩ := (N.double_space _).mp inA
  exact not_double N ne inB a av rfl

/-- `xsd:float` is apart from every other kind. -/
theorem float_apart (N : Normative D) {b : datatypes.Kind} (ne : b ≠ .Float) (y : Native) :
    ¬ (D.valueSpace (typeOf .Float) y ∧ D.valueSpace (typeOf b) y) := by
  rintro ⟨inA, inB⟩
  obtain ⟨a, av, rfl⟩ := (N.float_space _).mp inA
  exact not_float N ne inB a av rfl

end Values

/-! ### The interpretation of the encoding made from an OWL interpretation -/

section Lifted
variable {Object : Type u} {Value : Type v}

/-- The classes of a data node standing for a value: `owl:Thing`, `D`, the
    kinds' classes of the value's datatypes, the bit classes of the index of
    its literal value, the cuts of its number and the edges at or below its
    place as a floating-point value. -/
def NodeClass (context : data_ontology.Context) (I : Interpretation Object Value)
    (lit : datatypes.DataValue → Value) (num : ℝ → Value) (c : Class) (v : Value) : Prop :=
  c = thing ∨ c = dataClass ∨ (∃ k, c = kindClass k ∧ I.datatypes (typeOf k) v) ∨
    (∃ (j i : Usize) (_ : i.val < context.values.val.length), c = bitClass j ∧
      v = lit context.values.val[i.val] ∧ i.val.testBit j.val = true) ∨
    (∃ (i : Usize) (_ : i.val < context.cuts.val.length), c = cutClass i ∧
      ∃ r, v = num r ∧ InCut context.cuts.val[i.val] r) ∨
    ∃ (double : Bool) (i : Usize) (h : i.val < (edgesOf context double).val.length), c = edgeClass double i ∧
      ∃ b, FloatAt lit double v b ∧
        ((edgesOf context double).val[i.val]'h).val ≤ Rowl.FloatOrder.position (Rowl.Floats.fmt double)
          (Rowl.Floats.binaryOf b)

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
  · rintro (h | h | ⟨k', same, holds⟩ | ⟨j, i, _, same, _⟩ | ⟨i, _, same, _⟩ | ⟨d, i, _, same, _⟩)
    · exact absurd h.symm (class_ne_of_reserved thing_plain (reserved_kind k))
    · exact absurd h.symm (data_ne_kind k)
    · rw [kind_class_injective same]; exact holds
    · exact absurd same (kind_ne_bit k j)
    · exact absurd same (kind_ne_cut k i)
    · exact absurd same (kind_ne_edge k d i)
  · intro holds
    exact .inr (.inr (.inl ⟨k, rfl, holds⟩))

theorem node_bit (j : Usize) (v : Value) :
    NodeClass context I lit num (bitClass j) v ↔ ∃ (i : Usize) (_ : i.val < context.values.val.length),
      v = lit context.values.val[i.val] ∧ i.val.testBit j.val = true := by
  constructor
  · rintro (h | h | ⟨k, same, _⟩ | ⟨j', i, hi, same, holds⟩ | ⟨i, _, same, _⟩ | ⟨d, i, _, same, _⟩)
    · exact absurd h.symm (class_ne_of_reserved thing_plain (reserved_bit j))
    · exact absurd h.symm (data_ne_bit j)
    · exact absurd same.symm (kind_ne_bit k j)
    · rw [bit_class_injective same]; exact ⟨i, hi, holds⟩
    · exact absurd same (bit_ne_cut j i)
    · exact absurd same (bit_ne_edge j d i)
  · rintro ⟨i, hi, holds⟩
    exact .inr (.inr (.inr (.inl ⟨j, i, hi, rfl, holds⟩)))

theorem node_cut (i : Usize) (h : i.val < context.cuts.val.length) (v : Value) :
    NodeClass context I lit num (cutClass i) v ↔ ∃ r, v = num r ∧ InCut context.cuts.val[i.val] r := by
  constructor
  · rintro (h' | h' | ⟨k, same, _⟩ | ⟨j, i', _, same, _⟩ | ⟨i', hi', same, holds⟩ | ⟨d, i', _, same, _⟩)
    · exact absurd h'.symm (class_ne_of_reserved thing_plain (reserved_cut i))
    · exact absurd h'.symm (data_ne_cut i)
    · exact absurd same.symm (kind_ne_cut k i)
    · exact absurd same.symm (bit_ne_cut j i)
    · have := cut_class_injective same
      subst this
      exact holds
    · exact absurd same (cut_ne_edge i d i')
  · intro holds
    exact .inr (.inr (.inr (.inr (.inl ⟨i, h, rfl, holds⟩))))

theorem node_edge (double : Bool) (i : Usize) (h : i.val < (edgesOf context double).val.length) (v : Value) :
    NodeClass context I lit num (edgeClass double i) v ↔ ∃ b, FloatAt lit double v b ∧
      ((edgesOf context double).val[i.val]'h).val ≤
        Rowl.FloatOrder.position (Rowl.Floats.fmt double) (Rowl.Floats.binaryOf b) := by
  constructor
  · rintro (h' | h' | ⟨k, same, _⟩ | ⟨j, i', _, same, _⟩ | ⟨i', _, same, _⟩ | ⟨d, i', hi', same, holds⟩)
    · exact absurd h'.symm (class_ne_of_reserved thing_plain (reserved_edge double i))
    · exact absurd h'.symm (data_ne_edge double i)
    · exact absurd same.symm (kind_ne_edge k double i)
    · exact absurd same.symm (bit_ne_edge j double i)
    · exact absurd same.symm (cut_ne_edge i' double i)
    · obtain ⟨rfl, rfl⟩ := edge_class_injective same
      exact holds
  · intro holds
    exact .inr (.inr (.inr (.inr (.inr ⟨double, i, h, rfl, holds⟩))))

theorem node_plain {c : Class} (plain : ¬ Reserved c.iri.spelling.val) (notThing : c ≠ thing) (v : Value) :
    ¬ NodeClass context I lit num c v := by
  rintro (h | h | ⟨k, h, _⟩ | ⟨j, i, _, h, _⟩ | ⟨i, _, h, _⟩ | ⟨d, i, _, h, _⟩)
  · exact notThing h
  · exact class_ne_of_reserved plain reserved_data h
  · exact class_ne_of_reserved plain (reserved_kind k) h
  · exact class_ne_of_reserved plain (reserved_bit j) h
  · exact class_ne_of_reserved plain (reserved_cut i) h
  · exact class_ne_of_reserved plain (reserved_edge d i) h

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
noncomputable def litOf (N : Normative D) (embed : ValueEmbedding D Value) (x : datatypes.DataValue) : Value :=
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

theorem canonical_float_lit {double : Bool} {b : datatypes.Binary} (cb : Rowl.Floats.CanonicalBinary b)
    (vb : (Rowl.Floats.binaryOf b).Valid (Rowl.Floats.fmt double)) : Canonical (floatLit double b) := by
  cases double <;> exact ⟨cb, vb⟩

theorem float_at_unique (N : Normative D) {double : Bool} {x : Value} {b b' : datatypes.Binary}
    (h : FloatAt (litOf N embed) double x b) (h' : FloatAt (litOf N embed) double x b') : b = b' := by
  obtain ⟨cb, vb, rfl⟩ := h
  obtain ⟨cb', vb', same⟩ := h'
  have := lit_injective N (canonical_float_lit cb vb) (canonical_float_lit cb' vb') same
  cases double <;> cases this <;> rfl

theorem lifted_node (N : Normative D) (x0 : Object) (v : Value) :
    NodeValue context I (lifted context I (litOf N embed) (numOf N embed) x0) (litOf N embed) (numOf N embed)
      (.inr v) v where
  kinds := fun k _ => node_kind k v
  values := fun i h => by
    rw [lifted_value i h]
    simp [eq_comm]
  cuts := fun _ i h => node_cut i h v
  edges := fun double b hb i h => (node_edge double i h v).trans
    ⟨fun ⟨_, hb', le⟩ => float_at_unique N hb hb' ▸ le, fun le => ⟨b, hb, le⟩⟩

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

theorem lit_float (N : Normative D) (double : Bool) (b : datatypes.Binary) :
    valueOf N (floatLit double b) = Rowl.Datatypes.binaryValue N double (Rowl.Floats.binaryOf b) := by
  cases double <;> rfl

theorem float_space (N : Normative D) (double : Bool) (y : Native) :
    D.valueSpace (typeOf (floatKind double)) y ↔
      ∃ b, b.Valid (Rowl.Floats.fmt double) ∧ y = Rowl.Datatypes.binaryValue N double b := by
  cases double
  · exact N.float_space y
  · exact N.double_space y

theorem float_facet_space (N : Normative D) (double : Bool) (f : Iri) (v : Native) :
    D.facetSpace (typeOf (floatKind double)) f v ↔ f ∈ Rowl.DatatypeMap.rangeFacets ∧
      ∃ b, b.Valid (Rowl.Floats.fmt double) ∧ v = Rowl.Datatypes.binaryValue N double b := by
  cases double
  · exact N.float_facets f v
  · exact N.double_facets f v

/-- The values of a floating-point format in an OWL model are the values of the
    canonical kernel values of the format. -/
theorem lifted_binaries (N : Normative D) (interp : IsInterpretation D embed V I) (double : Bool) (x : Value) :
    I.datatypes (typeOf (floatKind double)) x ↔ ∃ b, FloatAt (litOf N embed) double x b := by
  obtain ⟨_, _, _, _, _, _, types, _⟩ := interp
  rw [types (typeOf (floatKind double)) (Rowl.Datatypes.normative_supported N _)]
  constructor
  · rintro ⟨y, inside, rfl⟩
    obtain ⟨b', vb', rfl⟩ := (float_space N double y).mp inside
    obtain ⟨b, cb, rfl⟩ := Rowl.FloatOrder.canonical_exists vb'
    exact ⟨b, cb, vb', by simp [litOf, lit_float]⟩
  · rintro ⟨b, cb, vb, rfl⟩
    exact ⟨_, (float_space N double _).mpr ⟨_, vb, lit_float N double b⟩, rfl⟩

theorem lifted_binary_facets (N : Normative D) (vocab : IsVocabulary D V) (interp : IsInterpretation D embed V I)
    (f : FacetRestriction) (F : datatypes.Facet) (double : Bool) (b : datatypes.Binary)
    (facet : Rowl.Datatypes.facetOf f.facet = some F)
    (run : datatypes.literal_value f.value = .ok (some (floatLit double b))) (x : Value) :
    I.facets f x ↔ ∃ y, FloatAt (litOf N embed) double x y ∧
      Rowl.FloatOrder.FacetHolds F (Rowl.Floats.binaryOf b) (Rowl.Floats.binaryOf y) := by
  obtain ⟨r, run', facts, _⟩ := Rowl.Datatypes.literal_value_correct f.value
  rw [run] at run'
  cases Result.ok_injective run'
  obtain ⟨canonical, _, _, _, rest⟩ := facts (floatLit double b) rfl
  obtain ⟨supported, lexical, value⟩ := rest D N
  have cb : Rowl.Floats.CanonicalBinary b ∧ (Rowl.Floats.binaryOf b).Valid (Rowl.Floats.fmt double) := by
    cases double
    · exact canonical
    · exact canonical
  have lexValue : D.lexicalValue f.value.datatype f.value.lexical.val =
      Rowl.Datatypes.binaryValue N double (Rowl.Floats.binaryOf b) := by
    rw [value, lit_float]
  have inV : V.facets f := by
    obtain ⟨_, _, _, _, _, _, _, _, literals, facetsV⟩ := vocab
    refine (facetsV f).mpr ⟨(literals _).mpr ⟨supported, lexical⟩, typeOf (floatKind double),
      Rowl.Datatypes.normative_supported N _, ?_⟩
    rw [float_facet_space N double, lexValue, facetOf_some facet]
    exact ⟨Rowl.Datatypes.facetIri_range F, _, cb.2, rfl⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, facetsI, _⟩ := interp
  rw [facetsI f inV x, lexValue, facetOf_some facet]
  simp only [Rowl.Datatypes.normative_binary_facet N F double cb.2]
  constructor
  · rintro ⟨y0, ⟨x', vx', holds, rfl⟩, rfl⟩
    obtain ⟨y, cy, rfl⟩ := Rowl.FloatOrder.canonical_exists vx'
    exact ⟨y, ⟨cy, vx', by simp [litOf, lit_float]⟩, holds⟩
  · rintro ⟨y, ⟨cy, vy, rfl⟩, holds⟩
    exact ⟨_, ⟨Rowl.Floats.binaryOf y, vy, holds, rfl⟩, by simp [litOf, lit_float]⟩

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
  binaries := fun double x => lifted_binaries N interp double x
  binaryFacets := fun f F double b facet run x => lifted_binary_facets N vocab interp f F double b facet run x
  binaryReal := fun double b x r h same => by
    obtain ⟨cb, vb, rfl⟩ := h
    have := embed.injectiveValues _ _ (value_datatype N (canonical_float_lit cb vb)) (real_datatype N r) same
    rw [lit_float] at this
    cases double
    · exact N.real_float r _ vb this.symm
    · exact N.real_double r _ vb this.symm
  binaryApart := fun b b' x h h' => by
    obtain ⟨cb, vb, rfl⟩ := h
    obtain ⟨cb', vb', same⟩ := h'
    have := lit_injective N (canonical_float_lit (double := true) cb vb) (canonical_float_lit (double := false) cb' vb')
      same
    cases this
  binaryInjective := fun double b b' x h h' => float_at_unique N h h'

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
  refine ⟨fun ordered => ?_, fun _ k hk _ role run y y' rel => ?_⟩
  obtain ⟨_, inside, _, chain⟩ := sorted ordered
  have frame := lifted_range_frame (context := context) N x0 vocab interp
  have orderIn : ∀ k ∈ order, k.val < context.cuts.val.length := fun k m =>
    inside k.val (List.mem_map_of_mem m)
  have consecutive : ∀ (p : Nat) (h : p < order.length), 0 < p →
      Rowl.Regions.CutBefore (cutAt context.cuts.val order[p - 1].val) (cutAt context.cuts.val order[p].val) := by
    intro p h pos
    have := (List.isChain_iff_getElem.mp chain) (p - 1) (by simp; omega)
    simpa [show p - 1 + 1 = p by omega] using this
  refine ⟨fun first head y holds => ?_, fun p h _ pos => ?_⟩
  · have firstIn : first.val < context.cuts.val.length := orderIn first (List.mem_of_mem_head? head)
    obtain ⟨r, rfl, _⟩ := lifted_cut_node N x0 firstIn holds
    change NodeClass context I (litOf N embed) (numOf N embed) (kindClass .Real) (numOf N embed r)
    rw [node_kind, frame.numeric .Real (by simp [Rowl.Datatypes.IsNumeric])]
    exact ⟨r, rfl, by simp [Rowl.Datatypes.RealIn]⟩
  · have hl := orderIn _ (List.getElem_mem (show p - 1 < order.length by omega))
    have hh := orderIn _ (List.getElem_mem h)
    have before := consecutive p h pos
    rw [cutAt_val hl, cutAt_val hh] at before
    refine ⟨fun y holds => ?_, ⟨fun same i hi at_i y inLow notHigh => ?_, fun differ integer => ?_⟩⟩
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
    · have nodup := good.1.2
      have canonical : ∀ v ∈ context.values.val, Rowl.Datatypes.IsNumber v → Rowl.Datatypes.CanonicalNumeric v :=
        fun v m number => canonical_numeric (good.1.1 v m) number
      -- the integer of a node of the run
      have integerOf : ∀ y, InRun (lifted context I (litOf N embed) (numOf N embed) x0) order[p - 1] order[p] y →
          ∃ z : ℤ, y = .inr (numOf N embed z) ∧ z ∈ Finset.Icc (firstIn (cutAt context.cuts.val order[p - 1].val))
            (lastOutside (cutAt context.cuts.val order[p].val)) := by
        intro y ⟨integerY, inLow, notHigh⟩
        obtain ⟨r, rfl, inLow'⟩ := lifted_cut_node N x0 hl inLow
        change NodeClass context I (litOf N embed) (numOf N embed) (kindClass .Integer) (numOf N embed r) at integerY
        rw [node_kind, frame.numeric .Integer (by simp [Rowl.Datatypes.IsNumeric])] at integerY
        obtain ⟨r', same, z, rfl⟩ := integerY
        have := frame.injective same
        subst this
        have notOver : ¬ InCut context.cuts.val[order[p].val] (z : ℝ) := fun inHigh =>
          notHigh ((node_cut _ hh _).mpr ⟨z, rfl, inHigh⟩)
        refine ⟨z, rfl, ?_⟩
        rw [cutAt_val hl, cutAt_val hh]
        exact Finset.mem_Icc.mpr ((Rowl.Regions.in_cuts_iff _ _ z).mp ⟨inLow', notOver⟩)
      -- the node of a literal value of the run
      have namedOf : ∀ z : ℤ, z ∈ namedIntegers context.values.val (cutAt context.cuts.val order[p - 1].val)
          (cutAt context.cuts.val order[p].val) →
          RunNamed context (lifted context I (litOf N embed) (numOf N embed) x0) order[p - 1] order[p]
            (.inr (numOf N embed z)) := by
        intro z mem
        obtain ⟨v, vmem, run, same⟩ := (named_in_run canonical).mp mem
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem vmem
        obtain ⟨j, hj⟩ := usize_of_index context.values i hi
        subst hj
        refine ⟨j, hi, run, ?_⟩
        rw [lifted_value j hi, frame.numbers _ (run_value_number run), same]
        rfl
      refine ⟨fun zero y inRun => ?_, fun pos fewer y _ ⟨f, injective, each⟩ => ?_⟩
      · obtain ⟨z, rfl, inside⟩ := integerOf y inRun
        exact namedOf z (all_named nodup canonical (by rw [← freeCount]; exact zero) inside)
      · have members : ∀ i, ∃ z : ℤ, f i = .inr (numOf N embed z) ∧
            z ∈ freeIntegers context.values.val (cutAt context.cuts.val order[p - 1].val)
              (cutAt context.cuts.val order[p].val) := by
          intro i
          obtain ⟨_, inRun, notNamed⟩ := each i
          obtain ⟨z, same, inside⟩ := integerOf (f i) inRun
          refine ⟨z, same, Finset.mem_sdiff.mpr ⟨inside, fun named => notNamed ?_⟩⟩
          rw [same]
          exact namedOf z named
        choose g gf gin using members
        have gInjective : Function.Injective (fun i => (⟨g i, gin i⟩ : freeIntegers context.values.val
            (cutAt context.cuts.val order[p - 1].val) (cutAt context.cuts.val order[p].val))) := by
          intro i j same
          simp only [Subtype.mk.injEq] at same
          apply injective
          rw [gf i, gf j, same]
        have := Fintype.card_le_of_injective _ gInjective
        simp only [Fintype.card_fin, Finset.coe_sort_coe, Fintype.card_coe] at this
        rw [free_card nodup canonical, ← freeCount] at this
        omega
  · have inData := List.getElem_mem hk
    cases y with
    | inl z =>
      obtain ⟨v, rfl, holds⟩ := (lifted_data_role interp.2.2.2.1 interp.2.2.2.2.2.1 run z y').mp rel
      exact .inr (.inr ⟨rfl, _, inData, holds⟩)
    | inr v =>
      exact absurd (show NodeClass context I (litOf N embed) (numOf N embed) dataClass v from .inr (.inl rfl))
        ((lifted_inert N x0 interp).sources _ role run _ _ rel)

/-- A node of the lifted interpretation in the class of an edge is a value of
    the format at or above the edge. -/
theorem lifted_edge_class (N : Normative D) {double : Bool} {i : Usize} {y : Object ⊕ Value} {x0 : Object}
    (holds : (lifted context I (litOf N embed) (numOf N embed) x0).classes (edgeClass double i) y) :
    ∃ (v : Value) (b : datatypes.Binary) (h : i.val < (edgesOf context double).val.length), y = .inr v ∧
      FloatAt (litOf N embed) double v b ∧
      ((edgesOf context double).val[i.val]'h).val ≤
        Rowl.FloatOrder.position (Rowl.Floats.fmt double) (Rowl.Floats.binaryOf b) := by
  cases y with
  | inl z => exact absurd (reserved_edge double i) holds.1
  | inr v =>
    rcases holds with h' | h' | ⟨k, same, _⟩ | ⟨j, i', _, same, _⟩ | ⟨i', _, same, _⟩ | ⟨d, i', hi', same, b, hb, le⟩
    · exact absurd h'.symm (class_ne_of_reserved thing_plain (reserved_edge double i))
    · exact absurd h' (data_ne_edge double i).symm
    · exact absurd same.symm (kind_ne_edge k double i)
    · exact absurd same.symm (bit_ne_edge j double i)
    · exact absurd same.symm (cut_ne_edge i' double i)
    · obtain ⟨rfl, rfl⟩ := edge_class_injective same
      exact ⟨v, b, hi', rfl, hb, le⟩

/-- A node of the lifted interpretation in the class of a slot of a format is
    a value of the format with its place in the slot. -/
theorem lifted_in_slot (N : Normative D) (interp : IsInterpretation D embed V I) {x0 : Object} {double : Bool}
    {low high : Option Usize} {lo hi : ℕ}
    (lowAt : ∀ i, low = some i → ∀ h : i.val < (edgesOf context double).val.length,
      ((edgesOf context double).val[i.val]'h).val = lo)
    (lowNone : low = none → lo = 0)
    (highAt : ∀ j, high = some j → ∃ h : j.val < (edgesOf context double).val.length,
      ((edgesOf context double).val[j.val]'h).val = hi)
    (highNone : high = none → hi = Rowl.DataEdges.placesEnd double) {y : Object ⊕ Value}
    (inSlot : Rowl.DataEdges.InSlotClass (lifted context I (litOf N embed) (numOf N embed) x0) double low high y) :
    ∃ v b, y = .inr v ∧ FloatAt (litOf N embed) double v b ∧
      Rowl.Floats.binaryOf b ∈ Rowl.FloatOrder.Slot (Rowl.Floats.fmt double)
        (Rowl.DataEdges.clamp double lo) (Rowl.DataEdges.clamp double hi) := by
  obtain ⟨kind, lows, highs⟩ := inSlot
  cases y with
  | inl z => exact absurd (reserved_kind _) kind.1
  | inr v =>
    change NodeClass context I (litOf N embed) (numOf N embed) (kindClass (floatKind double)) v at kind
    rw [node_kind, lifted_binaries N interp] at kind
    obtain ⟨b, hb⟩ := kind
    have below := Rowl.DataEdges.position_lt_end hb.2.1
    have lop : lo ≤ Rowl.FloatOrder.position (Rowl.Floats.fmt double) (Rowl.Floats.binaryOf b) := by
      cases low with
      | none => rw [lowNone rfl]; exact Nat.zero_le _
      | some i =>
        obtain ⟨v', b', h', same, hb', le⟩ := lifted_edge_class N (lows i rfl)
        cases same
        have := float_at_unique N hb hb'
        subst this
        rw [← lowAt i rfl h']; exact le
    have phi : Rowl.FloatOrder.position (Rowl.Floats.fmt double) (Rowl.Floats.binaryOf b) < hi := by
      cases high with
      | none => rw [highNone rfl]; exact below
      | some j =>
        obtain ⟨h', at_j⟩ := highAt j rfl
        by_contra not
        apply highs j rfl
        change NodeClass context I (litOf N embed) (numOf N embed) (edgeClass double j) v
        rw [node_edge double j h']
        exact ⟨b, hb, by rw [at_j]; omega⟩
    exact ⟨v, b, rfl, hb, hb.2.1, by unfold Rowl.DataEdges.clamp; omega, by unfold Rowl.DataEdges.clamp; omega⟩

/-- The axiom on a slot of a format holds in the lifted interpretation: its
    values are the OWL model's values of the format with places in the slot. -/
theorem lifted_slot (N : Normative D) (interp : IsInterpretation D embed V I) (good : Good context)
    (capacity : Nat) {x0 : Object} {double : Bool} {low high : Option Usize} {lo hi : ℕ}
    (lowAt : ∀ i, low = some i → ∀ h : i.val < (edgesOf context double).val.length,
      ((edgesOf context double).val[i.val]'h).val = lo)
    (lowNone : low = none → lo = 0)
    (highAt : ∀ j, high = some j → ∃ h : j.val < (edgesOf context double).val.length,
      ((edgesOf context double).val[j.val]'h).val = hi)
    (highNone : high = none → hi = Rowl.DataEdges.placesEnd double) :
    Rowl.DataEdges.SlotFact context capacity (lifted context I (litOf N embed) (numOf N embed) x0) double
      (Rowl.DataEdges.InSlotClass (lifted context I (litOf N embed) (numOf N embed) x0) double low high) lo hi := by
  have named : ∀ v b, FloatAt (litOf N embed) double v b →
      Rowl.Floats.binaryOf b ∈ Rowl.FloatOrder.Slot (Rowl.Floats.fmt double)
        (Rowl.DataEdges.clamp double lo) (Rowl.DataEdges.clamp double hi) →
      Rowl.Floats.binaryOf b ∈ Rowl.DataEdges.literalBinaries context.values.val double →
      Rowl.DataEdges.SlotNamed context (lifted context I (litOf N embed) (numOf N embed) x0) double
        (Rowl.DataEdges.clamp double lo) (Rowl.DataEdges.clamp double hi) (.inr v) := by
    rintro v b hb ⟨vb, l, u⟩ ⟨b', mem, same⟩
    have cb' := Rowl.DataEdges.canonical_lit (good.1.1 _ mem)
    have := Rowl.Floats.binary_canonical_injective cb'.1 hb.1 same
    subst this
    obtain ⟨k, hk, at_k⟩ := List.getElem_of_mem mem
    obtain ⟨i, rfl⟩ := usize_of_index context.values k hk
    refine ⟨i, hk, ⟨_, by rw [at_k, Rowl.DataEdges.format_place_lit], l, u⟩, ?_⟩
    rw [lifted_value i hk, at_k, hb.2.2]
  constructor
  · intro zero y inSlot
    obtain ⟨v, b, rfl, hb, inS⟩ := lifted_in_slot N interp lowAt lowNone highAt highNone inSlot
    by_cases lit : Rowl.Floats.binaryOf b ∈ Rowl.DataEdges.literalBinaries context.values.val double
    · exact named v b hb inS lit
    · exfalso
      have mem : Rowl.Floats.binaryOf b ∈ Rowl.DataEdges.FreeSlot context.values.val double
          (Rowl.DataEdges.clamp double lo) (Rowl.DataEdges.clamp double hi) := ⟨inS, lit⟩
      have pos := (Set.ncard_pos (Rowl.DataEdges.free_slot_finite _ _ _ _)).mpr ⟨_, mem⟩
      rw [Rowl.DataEdges.slot_free_card good double lo hi, zero] at pos
      omega
  · intro _ _ y _
    rw [← Rowl.DataEdges.slot_free_card good double lo hi]
    apply Rowl.DataEdges.at_most_of_free (Rowl.DataEdges.free_slot_finite _ _ _ _)
      (fun y' x => ∃ v b, y' = .inr v ∧ FloatAt (litOf N embed) double v b ∧ Rowl.Floats.binaryOf b = x)
    · rintro y' ⟨_, inSlot, notNamed⟩
      obtain ⟨v, b, rfl, hb, inS⟩ := lifted_in_slot N interp lowAt lowNone highAt highNone inSlot
      exact ⟨_, ⟨inS, fun lit => notNamed (named v b hb inS lit)⟩, v, b, rfl, hb, rfl⟩
    · rintro a a' x _ _ ⟨v, b, rfl, hb, rfl⟩ ⟨v', b', rfl, hb', same⟩
      have := Rowl.Floats.binary_canonical_injective hb'.1 hb.1 same
      subst this
      rw [hb.2.2, hb'.2.2]

/-- The axioms of the values of a floating-point format hold in the lifted
    interpretation. -/
theorem lifted_edges (N : Normative D) (interp : IsInterpretation D embed V I) (good : Good context)
    (capacity : Nat) (x0 : Object) (double : Bool) :
    Rowl.DataEdges.EdgeFacts context capacity double (lifted context I (litOf N embed) (numOf N embed) x0) := by
  intro _
  refine ⟨fun _ => lifted_slot N interp good capacity (low := none) (high := none) (by simp) (fun _ => rfl)
    (by simp) (fun _ => rfl), fun i => ⟨fun j => ?_, ?_, ?_⟩⟩
  · intro hi hj
    refine ⟨fun _ le y holds => ?_, fun _ _ => lifted_slot N interp good capacity (low := some i) (high := some j)
      (fun i' e h' => by cases e; rfl) (by simp) (fun j' e => by cases e; exact ⟨hj, rfl⟩) (by simp)⟩
    obtain ⟨v, b, h', rfl, hb, le'⟩ := lifted_edge_class N holds
    change NodeClass context I (litOf N embed) (numOf N embed) (edgeClass double j) v
    rw [node_edge double j hj]
    exact ⟨b, hb, le_trans le le'⟩
  · intro hi _
    refine ⟨fun y holds => ?_, lifted_slot N interp good capacity (low := none) (high := some i) (by simp)
      (fun _ => rfl) (fun j' e => by cases e; exact ⟨hi, rfl⟩) (by simp)⟩
    obtain ⟨v, b, h', rfl, hb, _⟩ := lifted_edge_class N holds
    change NodeClass context I (litOf N embed) (numOf N embed) (kindClass (floatKind double)) v
    rw [node_kind, lifted_binaries N interp]
    exact ⟨b, hb⟩
  · intro hi _
    exact lifted_slot N interp good capacity (low := some i) (high := none) (fun i' e h' => by cases e; rfl)
      (by simp) (by simp) (fun _ => rfl)

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
      strings := fun i j lt hi _ _ y => lifted_included N x0 interp (a := chainKind i) (b := chainKind j)
        (chain_included N lt hi) y
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
      sequences := by
        have coded : ∀ {a b : datatypes.Kind}, IsCoded a → a ≠ b →
            Apart context.kinds (lifted context I (litOf N embed) (numOf N embed) x0) a b :=
          fun ca ne _ _ y => lifted_apart N x0 interp (coded_apart N ca ne) y
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
          exact coded trivial (by simp)
      moments := by
        have apartM : ∀ {b : datatypes.Kind}, ¬ IsMomentKind b →
            Apart context.kinds (lifted context I (litOf N embed) (numOf N embed) x0) .DateTime b :=
          fun mb _ _ y => lifted_apart N x0 interp (moment_apart N (a := .DateTime) trivial mb) y
        refine ⟨fun _ _ y => lifted_included N x0 interp (a := .DateTimeStamp) (b := .DateTime) (stamp_datetime N) y,
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> exact apartM (by simp [IsMomentKind])
      floats := by
        have apartD : ∀ {b : datatypes.Kind}, b ≠ .Double →
            Apart context.kinds (lifted context I (litOf N embed) (numOf N embed) x0) .Double b :=
          fun ne _ _ y => lifted_apart N x0 interp (double_apart N ne) y
        have apartF : ∀ {b : datatypes.Kind}, b ≠ .Float →
            Apart context.kinds (lifted context I (litOf N embed) (numOf N embed) x0) .Float b :=
          fun ne _ _ y => lifted_apart N x0 interp (float_apart N ne) y
        refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
        all_goals first
          | exact apartD (fun e => by cases e)
          | exact apartF (fun e => by cases e)
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
    refine ⟨?_, fun k _ => ?_, fun j _ => ?_, fun _ number a ha => ?_, fun double n place e he => ?_⟩
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
      change NodeClass context I (litOf N embed) (numOf N embed) (cutClass a) _ ↔ _
      rw [node_cut a ha, frame.numbers _ number]
      constructor
      · rintro ⟨r, same, inCut⟩
        rw [frame.injective same]
        exact inCut
      · intro inCut
        exact ⟨_, rfl, inCut⟩
    · rw [lifted_value i h]
      change NodeClass context I (litOf N embed) (numOf N embed) (edgeClass double e) _ ↔ _
      rw [node_edge double e he]
      obtain ⟨b, at_i, rfl⟩ := Rowl.DataEdges.format_place_some place
      have cb := Rowl.DataEdges.canonical_lit (at_i ▸ canonical)
      have hb : FloatAt (litOf N embed) double (litOf N embed context.values.val[i.val]) b :=
        ⟨cb.1, cb.2, by rw [at_i]⟩
      constructor
      · rintro ⟨y, hy, le⟩
        rw [float_at_unique N hb hy]; exact le
      · intro le; exact ⟨b, hb, le⟩
  object := by
    rw [lifted_object]
    exact fun h => absurd reserved_data h.1
  edges := fun double => lifted_edges N interp good capacity x0 double

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
