import Rowl.DataComplete

/-!
OWL models made from models of `data_ontology`'s encoding. The elements of an
interpretation of the encoding that are no data nodes become the elements of
an OWL interpretation (`sound`), and each element gets values for finitely many
of its data nodes (`place`): each literal value's individual gets its value,
and each data node that witnesses a data restriction gets a fresh value of the
kinds its classes say, from infinite regions of integers, decimals that are no
integers, strings, tagged strings and values outside every datatype. When the
interpretation of the encoding satisfies a closure's encoding, the OWL
interpretation satisfies the closure (`sound_satisfies`), and every class
expression holds at an element exactly when its encoding does (`sound_class`).
-/
namespace Rowl.DataSound
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DatatypeMap (Normative IsInteger IsDecimal XmlText TagValue integerType decimalType stringType plainType
  booleanType)
open Rowl.Datatypes (Canonical valueOf typeOf kindOf InKind)
open Rowl.AlcOntology (RoleOf)
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.DataStructure
open Rowl.DataComplete
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe u v w x uI vI

/-! ### Infinitely many values of each region -/

/-- The data domain: the datatype map's values and further values outside
    every datatype. -/
abbrev Values (Native : Type w) : Type (max w v) := ULift.{v} (Native ⊕ ℕ)

def embedValue {Native : Type w} (y : Native) : Values.{v,w} Native := ULift.up (.inl y)

theorem embedValue_injective {Native : Type w} : Function.Injective (embedValue.{v,w} (Native := Native)) := by
  intro a b same
  simpa [embedValue] using same

/-- ASCII bytes from the space on are XML text. -/
theorem ascii_text (bs : List U8) (ascii : ∀ b ∈ bs, 32 ≤ b.val ∧ b.val < 128) : XmlText bs := by
  have step : ∀ k, k ≤ bs.length → ∃ text, Rowl.Unicode.TextFrom bs (bs.length - k) text := by
    intro k
    induction k with
    | zero => intro _; exact ⟨[], by simpa using Rowl.Unicode.TextFrom.endOfInput⟩
    | succ k ih =>
      intro hk
      obtain ⟨text, rest⟩ := ih (by omega)
      have inside : bs.length - (k + 1) < bs.length := by omega
      have ha := ascii _ (List.getElem_mem inside)
      refine ⟨(bs[bs.length - (k + 1)].val, bs.length - (k + 1)) :: text,
        .character (width := 1) ?_ ?_ (by decide) (by omega) ?_⟩
      · simp [Rowl.Unicode.Prefix, List.getElem?_eq_getElem inside, ha.2]
      · simp only [Rowl.Unicode.XmlChar]
        right; right; right; left
        omega
      · have : bs.length - (k + 1) + 1 = bs.length - k := by omega
        rw [this]
        exact rest
  obtain ⟨text, h⟩ := step bs.length le_rfl
  exact ⟨text, by simpa using h⟩

/-- The text of `n` letters `a`. -/
def aText (n : ℕ) : List U8 := List.replicate n 97#u8

theorem aText_xml (n : ℕ) : XmlText (aText n) :=
  ascii_text _ (fun b mem => by
    simp only [aText, List.mem_replicate] at mem
    rw [mem.2]
    decide)

theorem aText_injective : Function.Injective aText := by
  intro a b same
  simpa [aText] using congrArg List.length same

/-- The language tag `en`. -/
def enTag : List U8 := [101#u8, 110#u8]

theorem enTag_value : TagValue enTag := by
  refine ⟨enTag, ⟨[101, 110], ?_, Rowl.LangTag.two_letters_well_formed 101 110 (by omega) (by omega)⟩, ?_⟩
  · refine .character (cp := 101) (width := 1) (by simp [Rowl.Unicode.Prefix, enTag]) (by decide) (by simp [enTag]) ?_
    refine .character (cp := 110) (width := 1) (by simp [Rowl.Unicode.Prefix, enTag]) (by decide) (by simp [enTag]) ?_
    exact Rowl.Regular.Utf8From.endOfInput
  · simp [Rowl.DatatypeMap.Lowered, enTag]

/-- The regions of values that data nodes get: integers, decimals that are no
    integers, strings, tagged strings, and values outside every datatype. -/
inductive Region where
  | integer | decimal | string | tagged | other

section Regions
variable {Native : Type w} {D : DatatypeMap Native}

/-- The values of a region. -/
noncomputable def regionValue (N : Normative D) : Region → ℕ → Values.{v,w} Native
  | .integer, n => embedValue (N.number n)
  | .decimal, n => embedValue (N.number (n + 1 / 2))
  | .string, n => embedValue (N.text (aText n))
  | .tagged, n => embedValue (N.tagged (aText n) enTag)
  | .other, n => ULift.up (.inr n)

theorem half_not_integer (n : ℕ) : ¬ IsInteger ((n : ℚ) + 1 / 2) := by
  rintro ⟨z, h⟩
  have h2 : (2 * z : ℚ) = 2 * n + 1 := by linarith
  have h3 : (2 * z : ℤ) = 2 * n + 1 := by exact_mod_cast h2
  omega

theorem half_decimal (n : ℕ) : IsDecimal ((n : ℚ) + 1 / 2) :=
  ⟨10 * n + 5, 1, by push_cast; ring⟩

theorem region_value_injective (N : Normative D) {r r' : Region} {n n' : ℕ}
    (same : regionValue.{v,w} N r n = regionValue N r' n') : r = r' ∧ n = n' := by
  have tag := enTag_value
  cases r <;> cases r' <;> simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq, Sum.inr.injEq,
    reduceCtorEq] at same
  · exact ⟨rfl, by exact_mod_cast N.number_injective same⟩
  · exact absurd ⟨n, (N.number_injective same).symm⟩ (half_not_integer n')
  · exact absurd same (N.number_text _ _ (aText_xml n'))
  · exact absurd same (N.number_tagged _ _ _ (aText_xml n') tag)
  · exact absurd ⟨n', N.number_injective same⟩ (half_not_integer n)
  · exact ⟨rfl, by have := N.number_injective same; exact_mod_cast (by linarith : (n : ℚ) = n')⟩
  · exact absurd same (N.number_text _ _ (aText_xml n'))
  · exact absurd same (N.number_tagged _ _ _ (aText_xml n') tag)
  · exact absurd same.symm (N.number_text _ _ (aText_xml n))
  · exact absurd same.symm (N.number_text _ _ (aText_xml n))
  · exact ⟨rfl, aText_injective (N.text_injective _ _ (aText_xml n) (aText_xml n') same)⟩
  · exact absurd same (N.text_tagged _ _ _ (aText_xml n) (aText_xml n') tag)
  · exact absurd same.symm (N.number_tagged _ _ _ (aText_xml n) tag)
  · exact absurd same.symm (N.number_tagged _ _ _ (aText_xml n) tag)
  · exact absurd same.symm (N.text_tagged _ _ _ (aText_xml n') (aText_xml n) tag)
  · exact ⟨rfl, aText_injective (N.tagged_injective _ _ _ _ (aText_xml n) (aText_xml n') tag tag same).1⟩
  · exact ⟨rfl, same⟩

/-- Beyond some point, a region's values avoid a finite set. -/
theorem region_avoids (N : Normative D) (F : Set (Values.{v,w} Native)) (finite : F.Finite) (r : Region) :
    ∃ M, ∀ n, M ≤ n → regionValue N r n ∉ F := by
  have injective : Function.Injective (regionValue.{v,w} N r) :=
    fun a b same => (region_value_injective N same).2
  obtain ⟨B, bound⟩ := (finite.preimage (injective.injOn)).bddAbove
  exact ⟨B + 1, fun n hn inside => by have := bound inside; omega⟩

/-- The kinds whose datatypes the values of a region are in. -/
def RegionKind : Region → datatypes.Kind → Prop
  | .integer, .Integer => True
  | .integer, .Decimal => True
  | .decimal, .Decimal => True
  | .string, .String => True
  | .string, .Plain => True
  | .tagged, .Plain => True
  | _, _ => False

theorem number_kind (N : Normative D) (q : ℚ) (k : datatypes.Kind) (classic : Classic k) :
    D.valueSpace (typeOf k) (N.number q) ↔ (k = .Integer ∧ IsInteger q) ∨ (k = .Decimal ∧ IsDecimal q) := by
  cases k <;> simp only [Classic] at classic
  · simp only [typeOf, N.integer_space, reduceCtorEq, false_and, or_false, true_and]
    constructor
    · rintro ⟨q', h, e⟩
      rw [N.number_injective e]
      exact h
    · exact fun h => ⟨q, h, rfl⟩
  · simp only [typeOf, N.decimal_space, reduceCtorEq, false_and, false_or, true_and]
    constructor
    · rintro ⟨q', h, e⟩
      rw [N.number_injective e]
      exact h
    · exact fun h => ⟨q, h, rfl⟩
  · simp only [typeOf, N.string_space, reduceCtorEq, false_and, or_self, iff_false, not_exists, not_and]
    exact fun s xs e => N.number_text q s xs e
  · simp only [typeOf, N.plain_space, reduceCtorEq, false_and, or_self, iff_false, not_or, not_exists, not_and]
    exact ⟨fun s xs e => N.number_text q s xs e, fun s l xs tl e => N.number_tagged q s l xs tl e⟩
  · simp only [typeOf, N.boolean_space, reduceCtorEq, false_and, or_self, iff_false, not_exists]
    exact fun b e => N.number_truth q b e

theorem text_kind (N : Normative D) (s : List U8) (xs : XmlText s) (k : datatypes.Kind) (classic : Classic k) :
    D.valueSpace (typeOf k) (N.text s) ↔ k = .String ∨ k = .Plain := by
  cases k <;> simp only [Classic] at classic
  · simp only [typeOf, N.integer_space, reduceCtorEq, or_self, iff_false, not_exists, not_and]
    exact fun q _ e => N.number_text q s xs e.symm
  · simp only [typeOf, N.decimal_space, reduceCtorEq, or_self, iff_false, not_exists, not_and]
    exact fun q _ e => N.number_text q s xs e.symm
  · simp only [typeOf, N.string_space, true_or, iff_true]
    exact ⟨s, xs, rfl⟩
  · simp only [typeOf, N.plain_space, or_true, iff_true]
    exact .inl ⟨s, xs, rfl⟩
  · simp only [typeOf, N.boolean_space, reduceCtorEq, or_self, iff_false, not_exists]
    exact fun b e => N.text_truth s b xs e

theorem tagged_kind (N : Normative D) (s l : List U8) (xs : XmlText s) (tl : TagValue l) (k : datatypes.Kind)
    (classic : Classic k) :
    D.valueSpace (typeOf k) (N.tagged s l) ↔ k = .Plain := by
  cases k <;> simp only [Classic] at classic
  · simp only [typeOf, N.integer_space, reduceCtorEq, iff_false, not_exists, not_and]
    exact fun q _ e => N.number_tagged q s l xs tl e.symm
  · simp only [typeOf, N.decimal_space, reduceCtorEq, iff_false, not_exists, not_and]
    exact fun q _ e => N.number_tagged q s l xs tl e.symm
  · simp only [typeOf, N.string_space, reduceCtorEq, iff_false, not_exists, not_and]
    exact fun t xt e => N.text_tagged t s l xt xs tl e.symm
  · simp only [typeOf, N.plain_space, iff_true]
    exact .inr ⟨s, l, xs, tl, rfl⟩
  · simp only [typeOf, N.boolean_space, reduceCtorEq, iff_false, not_exists]
    exact fun b e => N.tagged_truth s l b xs tl e

theorem region_space (N : Normative D) (r : Region) (n : ℕ) (k : datatypes.Kind) (classic : Classic k) :
    (∃ y, D.valueSpace (typeOf k) y ∧ embedValue.{v,w} y = regionValue N r n) ↔ RegionKind r k := by
  have embedded : ∀ y0 : Native, (∃ y, D.valueSpace (typeOf k) y ∧ embedValue.{v,w} y = embedValue y0) ↔
      D.valueSpace (typeOf k) y0 := fun y0 =>
    ⟨fun ⟨y, inSpace, same⟩ => embedValue_injective same ▸ inSpace, fun inSpace => ⟨y0, inSpace, rfl⟩⟩
  cases r with
  | other =>
    simp only [regionValue, embedValue, ULift.up.injEq, reduceCtorEq, and_false, exists_false, false_iff]
    cases k <;> simp [RegionKind]
  | integer =>
    rw [regionValue, embedded, number_kind N _ k classic]
    cases k <;> simp only [Classic] at classic
    · simp only [RegionKind, true_and, reduceCtorEq, false_and, or_false, iff_true]
      exact ⟨n, by simp⟩
    · simp only [RegionKind, reduceCtorEq, false_and, true_and, false_or, iff_true]
      exact ⟨n, 0, by simp⟩
    all_goals simp [RegionKind]
  | decimal =>
    rw [regionValue, embedded, number_kind N _ k classic]
    cases k <;> simp only [Classic] at classic
    · simp only [RegionKind, true_and, reduceCtorEq, false_and, or_false, iff_false]
      exact half_not_integer n
    · simp only [RegionKind, reduceCtorEq, false_and, true_and, false_or, iff_true]
      exact half_decimal n
    all_goals simp [RegionKind]
  | string =>
    rw [regionValue, embedded, text_kind N _ (aText_xml n) k classic]
    cases k <;> simp [RegionKind]
  | tagged =>
    rw [regionValue, embedded, tagged_kind N _ _ (aText_xml n) enTag_value k classic]
    cases k <;> simp [RegionKind]

end Regions

/-! ### The region of a data node -/

section Profile
variable {Object' : Type u} {Value' : Type x} (context : data_ontology.Context) (J : Interpretation Object' Value')

/-- A kind in use whose class holds at a node. -/
def InUse (k : datatypes.Kind) (d : Object') : Prop := Used context.kinds k = true ∧ J.classes (kindClass k) d

/-- The region of a node's values, by the kinds in use at it. -/
noncomputable def regionOf (d : Object') : Region :=
  if InUse context J .Integer d then .integer
  else if InUse context J .Decimal d then .decimal
  else if InUse context J .String d then .string
  else if InUse context J .Plain d then .tagged
  else .other

theorem region_profile {context : data_ontology.Context} {J : Interpretation Object' Value'}
    (kinds : KindFacts context J) {d : Object'} (notBool : ¬ InUse context J .Boolean d)
    (k : datatypes.Kind) (used : Used context.kinds k = true) :
    J.classes (kindClass k) d ↔ RegionKind (regionOf context J d) k := by
  have classic := used_classic used
  simp only [regionOf]
  by_cases hi : InUse context J .Integer d
  · simp only [hi, ↓reduceIte]
    obtain ⟨ui, ai⟩ := hi
    cases k <;> simp only [Classic] at classic
    · simp [RegionKind, ai]
    · simp only [RegionKind, iff_true]; exact kinds.integerDecimal ui used d ai
    · simp only [RegionKind, iff_false]; exact fun h => kinds.integerString ui used d ⟨ai, h⟩
    · simp only [RegionKind, iff_false]; exact fun h => kinds.integerPlain ui used d ⟨ai, h⟩
    · simp only [RegionKind, iff_false]; exact fun h => kinds.integerBoolean ui used d ⟨ai, h⟩
  have ni : Used context.kinds .Integer = true → ¬ J.classes (kindClass .Integer) d := fun u h => hi ⟨u, h⟩
  simp only [hi, ↓reduceIte]
  by_cases hd : InUse context J .Decimal d
  · simp only [hd, ↓reduceIte]
    obtain ⟨ud, ad⟩ := hd
    cases k <;> simp only [Classic] at classic
    · simp only [RegionKind, iff_false]; exact ni used
    · simp [RegionKind, ad]
    · simp only [RegionKind, iff_false]; exact fun h => kinds.decimalString ud used d ⟨ad, h⟩
    · simp only [RegionKind, iff_false]; exact fun h => kinds.decimalPlain ud used d ⟨ad, h⟩
    · simp only [RegionKind, iff_false]; exact fun h => kinds.decimalBoolean ud used d ⟨ad, h⟩
  have nd : Used context.kinds .Decimal = true → ¬ J.classes (kindClass .Decimal) d := fun u h => hd ⟨u, h⟩
  simp only [hd, ↓reduceIte]
  by_cases hs : InUse context J .String d
  · simp only [hs, ↓reduceIte]
    obtain ⟨us, ast⟩ := hs
    cases k <;> simp only [Classic] at classic
    · simp only [RegionKind, iff_false]; exact ni used
    · simp only [RegionKind, iff_false]; exact nd used
    · simp [RegionKind, ast]
    · simp only [RegionKind, iff_true]; exact kinds.stringPlain us used d ast
    · simp only [RegionKind, iff_false]; exact fun h => kinds.stringBoolean us used d ⟨ast, h⟩
  have ns : Used context.kinds .String = true → ¬ J.classes (kindClass .String) d := fun u h => hs ⟨u, h⟩
  simp only [hs, ↓reduceIte]
  by_cases hp : InUse context J .Plain d
  · simp only [hp, ↓reduceIte]
    obtain ⟨up, ap⟩ := hp
    cases k <;> simp only [Classic] at classic
    · simp only [RegionKind, iff_false]; exact ni used
    · simp only [RegionKind, iff_false]; exact nd used
    · simp only [RegionKind, iff_false]; exact ns used
    · simp [RegionKind, ap]
    · simp only [RegionKind, iff_false]; exact fun h => kinds.plainBoolean up used d ⟨ap, h⟩
  have np : Used context.kinds .Plain = true → ¬ J.classes (kindClass .Plain) d := fun u h => hp ⟨u, h⟩
  simp only [hp, ↓reduceIte]
  cases k <;> simp only [Classic] at classic
  · simp only [RegionKind, iff_false]; exact ni used
  · simp only [RegionKind, iff_false]; exact nd used
  · simp only [RegionKind, iff_false]; exact ns used
  · simp only [RegionKind, iff_false]; exact np used
  · simp only [RegionKind, iff_false]; exact fun h => notBool ⟨used, h⟩

end Profile

/-! ### The OWL interpretation made from an interpretation of the encoding -/

section Model
variable {Object' : Type u} {Value' : Type x} {Native : Type w} {D : DatatypeMap Native}
  (context : data_ontology.Context) (J : Interpretation Object' Value') (N : Normative D)
  (atoms : List (DataProperty × Option DataRange × Nat))

/-- The value of a literal value. -/
noncomputable def litValue (x : datatypes.DataValue) : Values.{v,w} Native := embedValue (valueOf N x)

/-- A data node that is a literal value's individual. -/
def LiteralNode (d : Object') : Prop :=
  ∃ i : Usize, i.val < context.values.val.length ∧ J.namedIndividuals (valueIndividual i) = d

/-- Some data nodes that witness an element's data restriction, when it has
    enough of them. -/
noncomputable def witnesses (z : Object') (atom : DataProperty × Option DataRange × Nat) : List Object' :=
  if h : ∃ f : Fin atom.2.2 → Object', Function.Injective f ∧ ∀ role filler,
      data_ontology.data_role context atom.1 = .ok (some role) →
      data_ontology.encode_optional_range context atom.2.1 = .ok (some filler) →
      ∀ i, objectRelation J role z (f i) ∧ Rowl.Concepts.FillerHolds J filler (f i)
  then List.ofFn (Classical.choose h)
  else []

/-- The data nodes that witness an element's data restrictions. -/
noncomputable def witnessList (z : Object') : List Object' := atoms.flatMap (witnesses context J z)

/-- The values of the literal values. -/
def literalValues : Set (Values.{v,w} Native) := {y | ∃ val ∈ context.values.val, y = litValue N val}

theorem literal_values_finite : (literalValues.{v,w} context N).Finite := by
  apply (context.values.val.finite_toSet.image (litValue.{v,w} N)).subset
  rintro y ⟨val, mem, rfl⟩
  exact ⟨val, mem, rfl⟩

/-- Where each region's values leave the literal values behind. -/
noncomputable def regionStart (r : Region) : ℕ :=
  Classical.choose (region_avoids.{v,w} N (literalValues.{v,w} context N) (literal_values_finite context N) r)

theorem region_start_spec (r : Region) (n : ℕ) (beyond : regionStart.{v,w} context N r ≤ n) :
    regionValue.{v,w} N r n ∉ literalValues.{v,w} context N :=
  Classical.choose_spec (region_avoids.{v,w} N (literalValues.{v,w} context N) (literal_values_finite context N) r) n
    beyond

/-- The value of a data node for an element: a literal value's own value, and
    otherwise a fresh value of its region. -/
noncomputable def nodeValue (z : Object') (d : Object') : Values.{v,w} Native :=
  if h : LiteralNode context J d then
    match context.values.val[(Classical.choose h).val]? with
    | some val => litValue N val
    | none => ULift.up (.inr 0)
  else
    regionValue N (regionOf context J d)
      (regionStart.{v,w} context N (regionOf context J d) + (witnessList context J atoms z).idxOf d)

/-- An element's values at its data nodes. -/
def Place (z : Object') (y : Values.{v,w} Native) (d : Object') : Prop :=
  (LiteralNode context J d ∨ d ∈ witnessList context J atoms z) ∧ nodeValue.{u,v,w,x} context J N atoms z d = y

/-- The elements of the interpretation of the encoding that are no data nodes. -/
def Element : Type u := {y : Object' // ¬ J.classes dataClass y}

/-- The OWL interpretation made from an interpretation of the encoding. -/
noncomputable def sound (o : Element J) : Interpretation (Element J) (Values.{v,w} Native) where
  objectsNonempty := ⟨o⟩
  dataNonempty := ⟨ULift.up (.inr 0)⟩
  classes c z := J.classes c z.1
  objectProperties r z z' := J.objectProperties r z.1 z'.1
  dataProperties p z y := p = topData ∨ ∃ role, data_ontology.data_role context p = .ok (some role) ∧
    ∃ d, Place.{u,v,w,x} context J N atoms z.1 y d ∧ objectRelation J role z.1 d
  namedIndividuals a := if h : ¬ J.classes dataClass (J.namedIndividuals a) then ⟨_, h⟩ else o
  anonymousIndividuals b := if h : ¬ J.classes dataClass (J.anonymousIndividuals b) then ⟨_, h⟩ else o
  datatypes dt y := dt = literalDatatype ∨ ∃ y0, D.valueSpace dt y0 ∧ embedValue y0 = y
  literals lt := embedValue (D.lexicalValue lt.datatype lt.lexical.val)
  facets f y := ∃ y0, D.facetValue f.facet (D.lexicalValue f.value.datatype f.value.lexical.val) y0 ∧
    embedValue y0 = y
  named := fun _ => True

end Model

/-! ### The values at the data nodes -/

section Values
variable {Object' : Type u} {Value' : Type x} {Native : Type w} {D : DatatypeMap Native}
  {context : data_ontology.Context} {J : Interpretation Object' Value'} {N : Normative D}
  {atoms : List (DataProperty × Option DataRange × Nat)} {bits : Usize}

theorem typeOf_not_literal (N : Normative D) (k : datatypes.Kind) : typeOf k ≠ literalDatatype := by
  intro same
  have := Rowl.Datatypes.normative_supported N k
  rw [same] at this
  exact D.excludesLiteral this

theorem litValue_injective (N : Normative D) (good : Good context) {a b : datatypes.DataValue}
    (ma : a ∈ context.values.val) (mb : b ∈ context.values.val)
    (same : litValue.{v,w} N a = litValue N b) : a = b :=
  Rowl.Datatypes.value_injective N (good.1.1 a ma) (good.1.1 b mb) (embedValue_injective same)

theorem literal_node_value (frame : Frame context bits J) (enough : context.values.val.length ≤ 2 ^ bits.val)
    (z : Object') (i : Usize) (h : i.val < context.values.val.length) :
    nodeValue.{u,v,w,x} context J N atoms z (J.namedIndividuals (valueIndividual i)) =
      litValue N context.values.val[i.val] := by
  have literal : LiteralNode context J (J.namedIndividuals (valueIndividual i)) := ⟨i, h, rfl⟩
  have chosen : Classical.choose literal = i := by
    by_contra differ
    have spec := Classical.choose_spec literal
    exact value_individuals_apart frame enough _ _ spec.1 h differ spec.2
  simp only [nodeValue, dif_pos literal, chosen, List.getElem?_eq_getElem h]

theorem region_node_value (z d : Object') (notLiteral : ¬ LiteralNode context J d) :
    nodeValue.{u,v,w,x} context J N atoms z d = regionValue N (regionOf context J d)
      (regionStart.{v,w} context N (regionOf context J d) + (witnessList context J atoms z).idxOf d) := by
  simp only [nodeValue, dif_neg notLiteral]

theorem region_not_literal (z d : Object') (notLiteral : ¬ LiteralNode context J d) (val : datatypes.DataValue)
    (member : val ∈ context.values.val) : nodeValue.{u,v,w,x} context J N atoms z d ≠ litValue N val := by
  rw [region_node_value z d notLiteral]
  intro same
  exact region_start_spec context N _ _ (Nat.le_add_right _ _) ⟨val, member, same⟩

theorem nodeValue_injective (good : Good context) (frame : Frame context bits J)
    (enough : context.values.val.length ≤ 2 ^ bits.val) (z : Object') {d d' : Object'}
    (hd : LiteralNode context J d ∨ d ∈ witnessList context J atoms z)
    (hd' : LiteralNode context J d' ∨ d' ∈ witnessList context J atoms z)
    (same : nodeValue.{u,v,w,x} context J N atoms z d = nodeValue context J N atoms z d') : d = d' := by
  by_cases ld : LiteralNode context J d
  · obtain ⟨i, hi, rfl⟩ := ld
    rw [literal_node_value frame enough z i hi] at same
    by_cases ld' : LiteralNode context J d'
    · obtain ⟨i', hi', rfl⟩ := ld'
      rw [literal_node_value frame enough z i' hi'] at same
      have values := litValue_injective N good (List.getElem_mem hi) (List.getElem_mem hi') same
      rw [value_index_unique (hi := hi) (hj := hi') good values]
    · exact absurd same.symm (region_not_literal z d' ld' _ (List.getElem_mem hi))
  · by_cases ld' : LiteralNode context J d'
    · obtain ⟨i', hi', rfl⟩ := ld'
      rw [literal_node_value frame enough z i' hi'] at same
      exact absurd same (region_not_literal z d ld _ (List.getElem_mem hi'))
    · rw [region_node_value z d ld, region_node_value z d' ld'] at same
      obtain ⟨sameRegion, sameIndex⟩ := region_value_injective N same
      rw [sameRegion] at sameIndex
      have index : (witnessList context J atoms z).idxOf d = (witnessList context J atoms z).idxOf d' := by
        omega
      exact (List.idxOf_inj (hd.resolve_left ld)).mp index

theorem not_boolean_region (frame : Frame context bits J) {d : Object'} (notLiteral : ¬ LiteralNode context J d) :
    ¬ InUse context J .Boolean d := by
  rintro ⟨used, holds⟩
  obtain ⟨i, h, _, same⟩ := frame.kinds.truths used d holds
  exact notLiteral ⟨i, h, same⟩

theorem sound_types (N : Normative D) (o : Element J) (k : datatypes.Kind) (y : Values.{v,w} Native) :
    (sound.{u,v,w,x} context J N atoms o).datatypes (typeOf k) y ↔
      ∃ y0, D.valueSpace (typeOf k) y0 ∧ embedValue y0 = y := by
  simp only [sound, typeOf_not_literal N k, false_or]

/-- Each data node an element has a value at stands for it. -/
theorem place_node (good : Good context) (frame : Frame context bits J)
    (enough : context.values.val.length ≤ 2 ^ bits.val) (o : Element J) (z : Object') {d : Object'} :
    NodeValue context (sound.{u,v,w,x} context J N atoms o) J (litValue N) d
      (nodeValue.{u,v,w,x} context J N atoms z d) where
  kinds := fun k used => by
    rw [sound_types]
    by_cases ld : LiteralNode context J d
    · obtain ⟨i, hi, rfl⟩ := ld
      rw [literal_node_value frame enough z i hi, (frame.values i hi).2.1 k used,
        Rowl.Datatypes.normative_in_kind N (good.1.1 _ (List.getElem_mem hi)) k]
      exact ⟨fun inSpace => ⟨_, inSpace, rfl⟩, fun ⟨y0, inSpace, same⟩ => embedValue_injective same ▸ inSpace⟩
    · rw [region_node_value z d ld, region_space N _ _ k (used_classic used),
      region_profile frame.kinds (not_boolean_region frame ld) k used]
  values := fun i h => by
    by_cases ld : LiteralNode context J d
    · obtain ⟨i0, h0, rfl⟩ := ld
      rw [literal_node_value frame enough z i0 h0]
      constructor
      · intro same
        by_cases differ : i = i0
        · subst differ; rfl
        · exact absurd same (value_individuals_apart frame enough i i0 h h0 differ)
      · intro same
        have values := litValue_injective N good (List.getElem_mem h0) (List.getElem_mem h) same
        rw [value_index_unique (hi := h0) (hj := h) good values]
    · constructor
      · intro same
        exact absurd ⟨i, h, same⟩ ld
      · intro same
        exact absurd same (region_not_literal z d ld _ (List.getElem_mem h))

end Values

/-! ### The correspondence -/

section Correspondence
variable {Object' : Type u} {Value' : Type x} {Native : Type w} {D : DatatypeMap Native}
  {context : data_ontology.Context} {J : Interpretation Object' Value'} {N : Normative D}
  {atoms : List (DataProperty × Option DataRange × Nat)} {bits : Usize}

/-- The individuals that `J` places at elements that are no data nodes. -/
def Known (J : Interpretation Object' Value') (a : Individual) : Prop := ¬ J.classes dataClass (individual J a)

theorem top_ne_bottom_data : topData ≠ bottomData := by
  rw [Ne, dataProperty_eq_iff]; simp [topData, bottomData]

theorem sound_data_role (good : Good context) (o : Element J) {p : DataProperty} {role : ObjectPropertyExpression}
    (run : data_ontology.data_role context p = .ok (some role)) (z : Element J) (y : Values.{v,w} Native) :
    (sound.{u,v,w,x} context J N atoms o).dataProperties p z y ↔
      ∃ d, Place.{u,v,w,x} context J N atoms z.1 y d ∧ objectRelation J role z.1 d := by
  have notTop : p ≠ topData := by
    rintro rfl
    obtain ⟨res, run', facts⟩ := data_role_correct context topData
    rw [run] at run'
    cases Result.ok_injective run'
    rcases facts role rfl with ⟨h, _⟩ | ⟨_, inData, _⟩
    · exact top_ne_bottom_data h
    · exact (good.2.2 topData inData).1 rfl
  simp only [sound, notTop, false_or]
  constructor
  · rintro ⟨role', run', rest⟩
    rw [run] at run'
    cases Result.ok_injective run'
    exact rest
  · intro rest
    exact ⟨role, run, rest⟩

theorem sound_literal (o : Element J) {lt : Literal} {val : datatypes.DataValue}
    (run : datatypes.literal_value lt = .ok (some val)) :
    (sound.{u,v,w,x} context J N atoms o).literals lt = litValue N val := by
  obtain ⟨r, run', facts, _⟩ := Rowl.Datatypes.literal_value_correct lt
  rw [run] at run'
  cases Result.ok_injective run'
  obtain ⟨_, _, _, _, rest⟩ := facts val rfl
  obtain ⟨_, _, value⟩ := rest D N
  simp only [sound, litValue, value]

theorem sound_range_frame (jThing : ∀ d, J.classes thing d) (o : Element J) :
    RangeFrame (sound.{u,v,w,x} context J N atoms o) J (litValue N) where
  literal := fun _ => .inl rfl
  thing := jThing
  literals := fun _ _ run => sound_literal o run

theorem sound_atom (good : Good context) (frame : Frame context bits J)
    (enough : context.values.val.length ≤ 2 ^ bits.val) (jThing : ∀ d, J.classes thing d) (o : Element J)
    {p : DataProperty} {range : Option DataRange} {n : Nat} (member : (p, range, n) ∈ atoms)
    {role : ObjectPropertyExpression} {filler : Option ClassExpression}
    (roleRun : data_ontology.data_role context p = .ok (some role))
    (fillerRun : data_ontology.encode_optional_range context range = .ok (some filler)) (z : Element J) :
    (AtLeast n (fun y => (sound.{u,v,w,x} context J N atoms o).dataProperties p z y ∧
      RangeHolds (sound.{u,v,w,x} context J N atoms o) range y)) ↔
      AtLeast n (fun d => objectRelation J role z.1 d ∧ Rowl.Concepts.FillerHolds J filler d) := by
  have fillerAt : ∀ y d, Place.{u,v,w,x} context J N atoms z.1 y d →
      (RangeHolds (sound.{u,v,w,x} context J N atoms o) range y ↔ Rowl.Concepts.FillerHolds J filler d) := by
    intro y d pl
    obtain ⟨_, rfl⟩ := pl
    rcases optional_range_meaning.{u,max v w,u,x} context range filler fillerRun with
      ⟨rfl, rfl⟩ | ⟨r, c, rfl, rfl, means⟩
    · simp [RangeHolds, Rowl.Concepts.FillerHolds]
    · exact means _ J (litValue N) (sound_range_frame jThing o) d _ (place_node good frame enough o z.1)
  constructor
  · rintro ⟨f, fInj, each⟩
    have pick : ∀ i, ∃ d, Place.{u,v,w,x} context J N atoms z.1 (f i) d ∧ objectRelation J role z.1 d :=
      fun i => (sound_data_role good o roleRun z (f i)).mp (each i).1
    choose g gPlace gRel using pick
    refine ⟨g, fun i j same => fInj ?_, fun i => ⟨gRel i, (fillerAt (f i) (g i) (gPlace i)).mp (each i).2⟩⟩
    rw [← (gPlace i).2, ← (gPlace j).2, same]
  · rintro ⟨g, gInj, each⟩
    have h : ∃ f : Fin (p, range, n).2.2 → Object', Function.Injective f ∧ ∀ role' filler',
        data_ontology.data_role context (p, range, n).1 = .ok (some role') →
        data_ontology.encode_optional_range context (p, range, n).2.1 = .ok (some filler') →
        ∀ i, objectRelation J role' z.1 (f i) ∧ Rowl.Concepts.FillerHolds J filler' (f i) := by
      refine ⟨g, gInj, fun role' filler' roleRun' fillerRun' => ?_⟩
      have r1 : role' = role := Option.some.inj (Result.ok_injective (roleRun'.symm.trans roleRun))
      have f1 : filler' = filler := Option.some.inj (Result.ok_injective (fillerRun'.symm.trans fillerRun))
      subst r1 f1
      exact each
    obtain ⟨fInj, fEach⟩ := Classical.choose_spec h
    have listed : witnesses context J z.1 (p, range, n) = List.ofFn (Classical.choose h) := by
      rw [witnesses, dif_pos h]
    have inList : ∀ i, Classical.choose h i ∈ witnessList context J atoms z.1 := fun i =>
      List.mem_flatMap.mpr ⟨(p, range, n), member, by rw [listed]; exact List.mem_ofFn.mpr ⟨i, rfl⟩⟩
    refine ⟨fun i => nodeValue.{u,v,w,x} context J N atoms z.1 (Classical.choose h i),
      fun i j same => fInj (nodeValue_injective good frame enough z.1 (.inr (inList i)) (.inr (inList j)) same),
      fun i => ?_⟩
    have pl : Place.{u,v,w,x} context J N atoms z.1 _ _ := ⟨.inr (inList i), rfl⟩
    obtain ⟨related, fills⟩ := fEach role filler roleRun fillerRun i
    exact ⟨(sound_data_role good o roleRun z _).mpr ⟨_, pl, related⟩, (fillerAt _ _ pl).mpr fills⟩

theorem sound_simulates (good : Good context) (frame : Frame context bits J)
    (enough : context.values.val.length ≤ 2 ^ bits.val) (jThing : ∀ d, J.classes thing d)
    (jTop : ∀ y y', J.objectProperties topObject y y') (o : Element J) :
    Simulates context (sound.{u,v,w,x} context J N atoms o) J Subtype.val (Known J) atoms where
  injective := Subtype.val_injective
  objects := fun y => ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨z, same⟩ => same ▸ z.2⟩
  classes := fun _ _ _ => Iff.rfl
  roles := fun _ _ _ _ => Iff.rfl
  closed := frame.roles
  topAll := jTop
  individuals := fun a known => by
    cases a with
    | Named n =>
      have known' : ¬ J.classes dataClass (J.namedIndividuals n) := known
      simp only [individual, sound, dif_pos known']
    | Anonymous b =>
      have known' : ¬ J.classes dataClass (J.anonymousIndividuals b) := known
      simp only [individual, sound, dif_pos known']
  data := fun _ _ _ member _ _ roleRun fillerRun z =>
    sound_atom good frame enough jThing o member roleRun fillerRun z

theorem sound_placed (good : Good context) (frame : Frame context bits J)
    (enough : context.values.val.length ≤ 2 ^ bits.val) (o : Element J) :
    Placed context (sound.{u,v,w,x} context J N atoms o) J Subtype.val (litValue N)
      (fun z y d => Place.{u,v,w,x} context J N atoms z.1 y d) where
  functional := fun z _ d d' pl pl' => nodeValue_injective good frame enough z.1 pl.1 pl'.1 (pl.2.trans pl'.2.symm)
  injective := fun _ _ _ _ pl pl' => pl.2.symm.trans pl'.2
  nodes := fun z _ d pl => by
    obtain ⟨_, rfl⟩ := pl
    exact place_node good frame enough o z.1
  data := fun p role run z y => sound_data_role good o run z y
  literals := fun z lt a run => by
    obtain ⟨res, run', facts⟩ := literal_individual_correct context lt
    rw [run] at run'
    cases Result.ok_injective run'
    obtain ⟨val, i, h, valueRun, at_i, rfl⟩ := facts a rfl
    refine ⟨.inl ⟨i, h, rfl⟩, ?_⟩
    simp only [individual]
    rw [literal_node_value frame enough z.1 i h, at_i, sound_literal o valueRun]
  top := fun _ _ => .inl rfl

/-- The OWL interpretation made from an interpretation of the encoding is an
    interpretation for the datatype map. -/
theorem sound_interpretation (V : Vocabulary) (jThing : ∀ d, J.classes thing d)
    (jNothing : ∀ d, ¬ J.classes nothing d) (jTop : ∀ y y', J.objectProperties topObject y y')
    (jBottom : ∀ y y', ¬ J.objectProperties bottomObject y y') (o : Element J) :
    IsInterpretation D (ValueEmbedding.ofEmbedding D ⟨embedValue.{v,w}, embedValue_injective⟩) V
      (sound.{u,v,w,x} context J N atoms o) := by
  refine ⟨fun z => jThing z.1, fun z => jNothing z.1, fun z z' => jTop z.1 z'.1, fun z z' => jBottom z.1 z'.1,
    fun _ _ => .inl rfl, ?_, fun dt supported y => ?_, fun _ => .inl rfl, fun _ _ => rfl, fun _ _ _ => Iff.rfl,
    fun _ _ => trivial⟩
  · intro z y holds
    rcases holds with h | ⟨role, run, d, _, related⟩
    · exact top_ne_bottom_data h.symm
    · obtain ⟨res, run', facts⟩ := data_role_correct context bottomData
      rw [run] at run'
      cases Result.ok_injective run'
      rcases facts role rfl with ⟨_, rfl⟩ | ⟨notBottom, _⟩
      · exact jBottom _ _ related
      · exact notBottom rfl
  · have notLiteral : dt ≠ literalDatatype := fun same => D.excludesLiteral (same ▸ supported)
    simp only [sound, notLiteral, false_or]
    rfl

end Correspondence

/-! ### Satisfaction -/

section Satisfaction
variable {Object' : Type u} {Value' : Type x} {Native : Type w} {D : DatatypeMap Native}

/-- The data restrictions of a closure's axioms. -/
def itemAtoms (items : List AnnotatedAxiom) : List (DataProperty × Option DataRange × Nat) :=
  items.flatMap (fun i => axiomAtoms i.axiom)

/-- An interpretation of a closure's encoding that satisfies it gives an OWL
    interpretation of the closure that satisfies it, for every list of data
    restrictions that covers the closure's. -/
theorem sound_satisfies (N : Normative D) {context : data_ontology.Context} (good : Good context)
    {items enc : alloc.vec.Vec AnnotatedAxiom} (run : data_ontology.encode context items = .ok (some enc))
    {J : Interpretation Object' Value'} (jThing : ∀ d, J.classes thing d)
    (jTop : ∀ y y', J.objectProperties topObject y y') (holds : ∀ b ∈ enc.val, satisfies J b.axiom) :
    ∃ (bits : Usize) (o : Element J), Frame context bits J ∧ context.values.val.length ≤ 2 ^ bits.val ∧
      (∀ item ∈ items.val, ∀ a ∈ axiomIndividuals item.axiom, Known J a) ∧
      ∀ atoms, (∀ a ∈ itemAtoms items.val, a ∈ atoms) →
        satisfiesClosure (sound.{u,v,w,x} context J N atoms o) items.val := by
  obtain ⟨res, run', facts⟩ := encode_meaning.{u,max v w,u,x} context good items
  rw [run] at run'
  cases Result.ok_injective run'
  obtain ⟨new, bits, means, enough, _, _, iff⟩ := facts enc rfl
  obtain ⟨newHolds, frame⟩ := (iff J).mp holds
  let o : Element J := ⟨J.namedIndividuals objectIndividual, frame.object⟩
  have names := means.2.2 J newHolds
  refine ⟨bits, o, frame, enough, names, fun atoms covers => ?_⟩
  exact (means.1 (sound.{u,v,w,x} context J N atoms o) J Subtype.val (Known J) atoms (litValue N) _
    (sound_simulates good frame enough jThing jTop o) (sound_placed good frame enough o)
    (sound_range_frame jThing o)
    (fun item mem a inside => covers a (List.mem_flatMap.mpr ⟨item, mem, inside⟩)) names).1 newHolds

/-- A class expression holds at an element of the OWL interpretation exactly
    when its encoding holds at it. -/
theorem sound_class (N : Normative D) {context : data_ontology.Context} (good : Good context) {bits : Usize}
    {J : Interpretation Object' Value'} (frame : Frame context bits J)
    (enough : context.values.val.length ≤ 2 ^ bits.val) (jThing : ∀ d, J.classes thing d)
    (jTop : ∀ y y', J.objectProperties topObject y y') (o : Element J)
    {atoms : List (DataProperty × Option DataRange × Nat)} {c c' : ClassExpression}
    (run : data_ontology.encode_class context c = .ok (some c')) (atomsIn : ∀ a ∈ classAtoms c, a ∈ atoms)
    (known : ∀ a ∈ classIndividuals c, Known J a) (z : Element J) :
    classDenote (sound.{u,v,w,x} context J N atoms o) c z ↔ classDenote J c' z.1 := by
  obtain ⟨res, run', means⟩ := encode_class_meaning.{u,max v w,u,x} context c
  rw [run] at run'
  cases Result.ok_injective run'
  exact means c' rfl _ J Subtype.val (Known J) atoms (sound_simulates good frame enough jThing jTop o) atomsIn
    known z

end Satisfaction

/-! ### Other anonymous individuals -/

section Anonymous
variable {Object' : Type u} {Value' : Type x} {Native : Type w} {D : DatatypeMap Native}
  {context : data_ontology.Context} {J : Interpretation Object' Value'} {N : Normative D} {bits : Usize}

/-- The fillers of the encoding's data restrictions mean the same when the
    anonymous individuals are reinterpreted. -/
theorem filler_anonymous (N : Normative D) (good : Good context) (g : AnonymousIndividual → Object')
    (frame : Frame context bits (withAnonymous J g)) (enough : context.values.val.length ≤ 2 ^ bits.val)
    (jThing : ∀ d, (withAnonymous J g).classes thing d) (o : Element (withAnonymous J g))
    {range : Option DataRange} {filler : Option ClassExpression}
    (run : data_ontology.encode_optional_range context range = .ok (some filler)) (d : Object') :
    Rowl.Concepts.FillerHolds (withAnonymous J g) filler d ↔ Rowl.Concepts.FillerHolds J filler d := by
  rcases optional_range_meaning.{u,w,u,x} context range filler run with
    ⟨rfl, rfl⟩ | ⟨r, c, rfl, rfl, means⟩
  · simp [Rowl.Concepts.FillerHolds]
  · simp only [Rowl.Concepts.FillerHolds]
    have node := place_node (N := N) (atoms := []) good frame enough o d (d := d)
    have frame0 : RangeFrame (sound.{u,0,w,x} context (withAnonymous J g) N [] o) (withAnonymous J g)
        (litValue N) := sound_range_frame jThing o
    have frameJ : RangeFrame (sound.{u,0,w,x} context (withAnonymous J g) N [] o) J (litValue N) :=
      ⟨frame0.literal, frame0.thing, frame0.literals⟩
    have nodeJ : NodeValue context (sound.{u,0,w,x} context (withAnonymous J g) N [] o) J (litValue N) d
        (nodeValue.{u,0,w,x} context (withAnonymous J g) N [] d d) := ⟨node.kinds, node.values⟩
    exact (means _ _ _ frame0 d _ node).symm.trans (means _ J _ frameJ d _ nodeJ)

/-- A correspondence with an interpretation of the encoding with other
    anonymous individuals is one with the interpretation itself, for the
    individuals placed alike. -/
theorem simulates_anonymous (N : Normative D) (good : Good context) (g : AnonymousIndividual → Object')
    (frame : Frame context bits (withAnonymous J g)) (enough : context.values.val.length ≤ 2 ^ bits.val)
    (jThing : ∀ d, (withAnonymous J g).classes thing d) (o : Element (withAnonymous J g))
    {Object : Type uI} {Value : Type vI} {I : Interpretation Object Value}
    {obj : Object → Object'} {known known' : Individual → Prop}
    {atoms : List (DataProperty × Option DataRange × Nat)}
    (sim : Simulates context I (withAnonymous J g) obj known atoms)
    (individuals : ∀ a, known' a → individual J a = obj (individual I a)) :
    Simulates context I J obj known' atoms where
  injective := sim.injective
  objects := sim.objects
  classes := sim.classes
  roles := sim.roles
  closed := sim.closed
  topAll := sim.topAll
  individuals := individuals
  data := fun p range n member role filler roleRun fillerRun z => by
    rw [sim.data p range n member role filler roleRun fillerRun z]
    have same : ∀ y, (objectRelation (withAnonymous J g) role (obj z) y ∧
        Rowl.Concepts.FillerHolds (withAnonymous J g) filler y) ↔
        (objectRelation J role (obj z) y ∧ Rowl.Concepts.FillerHolds J filler y) := fun y =>
      and_congr Iff.rfl (filler_anonymous N good g frame enough jThing o fillerRun y)
    simp only [same]

end Anonymous

end Rowl.DataSound
