import Rowl.Probes
import Rowl.Unicode

/-!
Independent declarative specification of the 2012 OWL 2 Direct Semantics.
It consumes Aeneas' *actual Rust types*, not a separate hand-written AST.
It neither runs a reasoner nor postulates the correctness of one. Datatype maps
are parameters; constructing the normative OWL map is the M5 obligation.
Inputs here are axiom closures, already standardized apart, not parsed documents.
-/
namespace Rowl.Owl
open Aeneas Aeneas.Std RowlRust.model
universe u v w

def _root_.RowlRust.model.NonEmpty.elements {α : Type} (xs : NonEmpty α) : List α := xs.first :: xs.rest.val
def _root_.RowlRust.model.AtLeastTwo.elements {α : Type} (xs : AtLeastTwo α) : List α :=
  xs.first :: xs.second :: xs.rest.val

theorem nonempty_arity {α : Type} (xs : NonEmpty α) : 1 ≤ xs.elements.length := by
  simp [NonEmpty.elements]
theorem at_least_two_arity {α : Type} (xs : AtLeastTwo α) : 2 ≤ xs.elements.length := by
  simp [AtLeastTwo.elements]

private theorem listN_mem_size {α : Type} [SizeOf α] {n : Nat}
    (xs : Aeneas.Data.ListN.ListN α n) {x : α} (h : x ∈ xs.toList) :
    sizeOf x < sizeOf xs := by
  induction xs with
  | nil => simp [Aeneas.Data.ListN.ListN.toList] at h
  | cons head tail ih =>
    simp only [Aeneas.Data.ListN.ListN.toList, List.mem_cons] at h
    rcases h with rfl | h
    · simp +arith
    · have := ih h
      simp only [Data.ListN.ListN.cons.sizeOf_spec]
      omega

private theorem vec_mem_size {α : Type} [SizeOf α] (xs : alloc.vec.Vec α)
    {x : α} (h : x ∈ xs.val) : sizeOf x < sizeOf xs := by
  have := listN_mem_size xs.slice.list h
  cases xs with | mk slice => cases slice; simp_all [alloc.vec.Vec.val, Slice.val]; omega

private theorem first_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.first < sizeOf xs := by
  cases xs; simp +arith
private theorem second_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.second < sizeOf xs := by
  cases xs; simp +arith
private theorem rest_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.rest < sizeOf xs := by
  cases xs; simp +arith

def thing : Class := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 84#u8, 104#u8, 105#u8, 110#u8, 103#u8] (by simp; scalar_tac)⟩⟩
def nothing : Class := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 78#u8, 111#u8, 116#u8, 104#u8, 105#u8, 110#u8, 103#u8] (by simp; scalar_tac)⟩⟩
def topObject : ObjectProperty := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 116#u8, 111#u8, 112#u8, 79#u8, 98#u8, 106#u8, 101#u8, 99#u8, 116#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8] (by simp; scalar_tac)⟩⟩
def bottomObject : ObjectProperty := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 98#u8, 111#u8, 116#u8, 116#u8, 111#u8, 109#u8, 79#u8, 98#u8, 106#u8, 101#u8, 99#u8, 116#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8] (by simp; scalar_tac)⟩⟩
def topData : DataProperty := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 116#u8, 111#u8, 112#u8, 68#u8, 97#u8, 116#u8, 97#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8] (by simp; scalar_tac)⟩⟩
def bottomData : DataProperty := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 98#u8, 111#u8, 116#u8, 116#u8, 111#u8, 109#u8, 68#u8, 97#u8, 116#u8, 97#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8] (by simp; scalar_tac)⟩⟩
def literalDatatype : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 48#u8, 47#u8, 48#u8, 49#u8, 47#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 76#u8, 105#u8, 116#u8, 101#u8, 114#u8, 97#u8, 108#u8] (by simp; scalar_tac)⟩⟩

/-- Canonical UTF-8 representation of an arbitrary Unicode scalar string. Unlike
    XML source text, a decoded literal may contain the scalar U+0000. -/
inductive Utf8Lexical : List U8 → Prop
  | empty : Utf8Lexical []
  | ascii (a : U8) {rest} : a.val < 128 → Utf8Lexical rest → Utf8Lexical (a::rest)
  | pair (a b : U8) {rest} : Rowl.Unicode.Pair a.val b.val → Utf8Lexical rest →
      Utf8Lexical (a::b::rest)
  | triple (a b c : U8) {rest} : Rowl.Unicode.Triple a.val b.val c.val → Utf8Lexical rest →
      Utf8Lexical (a::b::c::rest)
  | quad (a b c d : U8) {rest} : Rowl.Unicode.Quad a.val b.val c.val d.val → Utf8Lexical rest →
      Utf8Lexical (a::b::c::d::rest)

/-- §2.1: all six components of the datatype map, with their range conditions.
    Functions outside their declared spaces are irrelevant total extensions.
    The facet value of a pair is one set for every datatype whose facet space
    has the pair, and a datatype restriction intersects it with the datatype's
    value space (Table 4). §2.1 also asks the facet value to lie in the value
    space of each such datatype; that condition is not imposed here, because
    read literally it is contradictory for numbers: the pair of
    `xsd:minInclusive` and 0 is in the facet spaces of both `owl:real` and
    `owl:rational` (Structural Specification §4.1, Table 4), so its facet value
    would contain no irrational number, while `owl:real[>= 0]` must contain
    every nonnegative real. With the intersection of Table 4 the restriction
    denotes exactly the per-datatype facet values of §4.1. -/
structure DatatypeMap (Value : Type v) where
  supported : Datatype → Prop
  lexicalSpace : Datatype → List U8 → Prop
  facetSpace : Datatype → Iri → Value → Prop
  valueSpace : Datatype → Value → Prop
  lexicalValue : Datatype → List U8 → Value
  facetValue : Iri → Value → Value → Prop
  excludesLiteral : ¬ supported literalDatatype
  lexicalUtf8 : ∀ dt text, supported dt → lexicalSpace dt text → Utf8Lexical text
  lexicalInSpace : ∀ dt text, supported dt → lexicalSpace dt text →
    valueSpace dt (lexicalValue dt text)

/-- Only actual datatype values must embed injectively into the data domain.
    Unused elements of the map's ambient carrier impose no size restriction.
    In particular an empty map can have a singleton data domain. -/
def isDatatypeValue {Native : Type w} (D : DatatypeMap Native) (x : Native) : Prop :=
  ∃ dt, D.supported dt ∧ D.valueSpace dt x
structure ValueEmbedding {Native : Type w} (D : DatatypeMap Native) (Value : Type v) where
  map : Native → Value
  injectiveValues : ∀ x y, isDatatypeValue D x → isDatatypeValue D y → map x = map y → x = y
instance {Native : Type w} {D : DatatypeMap Native} {Value : Type v} :
    CoeFun (ValueEmbedding D Value) (fun _ => Native → Value) := ⟨ValueEmbedding.map⟩
def ValueEmbedding.ofEmbedding {Native : Type w} (D : DatatypeMap Native) {Value : Type v}
    (embed : Native ↪ Value) : ValueEmbedding D Value :=
  ⟨embed, fun _ _ _ _ h => embed.injective h⟩

structure Vocabulary where
  classes : Class → Prop
  objectProperties : ObjectProperty → Prop
  dataProperties : DataProperty → Prop
  individuals : Individual → Prop
  datatypes : Datatype → Prop
  literals : Literal → Prop
  facets : FacetRestriction → Prop

def IsVocabulary {Value : Type v} (D : DatatypeMap Value) (V : Vocabulary) : Prop :=
  V.classes thing ∧ V.classes nothing ∧
  V.objectProperties topObject ∧ V.objectProperties bottomObject ∧
  V.dataProperties topData ∧ V.dataProperties bottomData ∧
  (∀ dt, D.supported dt → V.datatypes dt) ∧ V.datatypes literalDatatype ∧
  (∀ lt, V.literals lt ↔ D.supported lt.datatype ∧ D.lexicalSpace lt.datatype lt.lexical.val) ∧
  (∀ f, V.facets f ↔ V.literals f.value ∧
    ∃ dt, D.supported dt ∧ D.facetSpace dt f.facet
      (D.lexicalValue f.value.datatype f.value.lexical.val))

/-- A valid vocabulary cannot admit malformed raw literal encodings. This is a
    representation condition, independent of the future normative datatype map. -/
theorem literal_lexical_utf8 {Value : Type v} (D : DatatypeMap Value) (V : Vocabulary)
    (valid : IsVocabulary D V) (literal : Literal) (used : V.literals literal) :
    Utf8Lexical literal.lexical.val := by
  have lexical := (valid.2.2.2.2.2.2.2.2.1 literal).mp used
  exact D.lexicalUtf8 literal.datatype literal.lexical.val lexical.1 lexical.2

/-- §2.2. Object/data domains may be infinite; they are distinct sorts.
    The ambient domain is their disjoint sum. Entity roles have independent maps. -/
structure Interpretation (Object : Type u) (Value : Type v) where
  objectsNonempty : Nonempty Object
  dataNonempty : Nonempty Value
  classes : Class → Object → Prop
  objectProperties : ObjectProperty → Object → Object → Prop
  dataProperties : DataProperty → Object → Value → Prop
  namedIndividuals : NamedIndividual → Object
  anonymousIndividuals : AnonymousIndividual → Object
  datatypes : Datatype → Value → Prop
  literals : Literal → Value
  facets : FacetRestriction → Value → Prop
  named : Object → Prop

theorem domains_disjoint {Object : Type u} {Value : Type v} (x : Object) (y : Value) :
    (Sum.inl x : Sum Object Value) ≠ Sum.inr y := by simp

def IsInterpretation {Object : Type u} {Value : Type v} {Native : Type w}
    (D : DatatypeMap Native) (embed : ValueEmbedding D Value) (V : Vocabulary)
    (I : Interpretation Object Value) : Prop :=
  (∀ x, I.classes thing x) ∧ (∀ x, ¬ I.classes nothing x) ∧
  (∀ x y, I.objectProperties topObject x y) ∧
  (∀ x y, ¬ I.objectProperties bottomObject x y) ∧
  (∀ x y, I.dataProperties topData x y) ∧
  (∀ x y, ¬ I.dataProperties bottomData x y) ∧
  (∀ dt, D.supported dt → ∀ x, I.datatypes dt x ↔ ∃ y, D.valueSpace dt y ∧ embed y = x) ∧
  (∀ x, I.datatypes literalDatatype x) ∧
  (∀ lt, V.literals lt → I.literals lt = embed (D.lexicalValue lt.datatype lt.lexical.val)) ∧
  (∀ f, V.facets f → ∀ x, I.facets f x ↔ ∃ y,
    D.facetValue f.facet (D.lexicalValue f.value.datatype f.value.lexical.val) y ∧ embed y = x) ∧
  (∀ a, V.individuals (.Named a) → I.named (I.namedIndividuals a))

variable {Object : Type u} {Value : Type v}

def individual (I : Interpretation Object Value) : Individual → Object
  | .Named a => I.namedIndividuals a
  | .Anonymous a => I.anonymousIndividuals a

def objectRelation (I : Interpretation Object Value) : ObjectPropertyExpression → Object → Object → Prop
  | .Property p => I.objectProperties p
  | .Inverse p => fun x y => I.objectProperties p y x

/-- Distinct denotations, rather than names or edges; valid for infinite domains.
    A finite injection is exactly the lower cardinality bound. -/
def AtLeast {α : Type u} (n : Nat) (P : α → Prop) : Prop :=
  ∃ f : Fin n → α, Function.Injective f ∧ ∀ i, P (f i)
def AtMost {α : Type u} (n : Nat) (P : α → Prop) : Prop := ¬ AtLeast (n + 1) P
def Exactly {α : Type u} (n : Nat) (P : α → Prop) : Prop := AtLeast n P ∧ AtMost n P

def dataDenote (I : Interpretation Object Value) (range : DataRange) (x : Value) : Prop :=
  match range with
  | .Datatype dt => I.datatypes dt x
  | .Intersection xs => dataDenote I xs.first x ∧ dataDenote I xs.second x ∧
      ∀ e ∈ xs.rest.val, dataDenote I e x
  | .Union xs => dataDenote I xs.first x ∨ dataDenote I xs.second x ∨
      ∃ e, ∃ _ : e ∈ xs.rest.val, dataDenote I e x
  | .Complement e => ¬ dataDenote I e x
  | .OneOf xs => ∃ lt ∈ xs.elements, I.literals lt = x
  | .Restriction dt xs => I.datatypes dt x ∧ ∀ f ∈ xs.elements, I.facets f x
termination_by sizeOf range
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

def classDenote (I : Interpretation Object Value) (expression : ClassExpression) (x : Object) : Prop :=
  match expression with
  | .Class c => I.classes c x
  | .ObjectIntersectionOf xs => classDenote I xs.first x ∧ classDenote I xs.second x ∧
      ∀ e ∈ xs.rest.val, classDenote I e x
  | .ObjectUnionOf xs => classDenote I xs.first x ∨ classDenote I xs.second x ∨
      ∃ e, ∃ _ : e ∈ xs.rest.val, classDenote I e x
  | .ObjectComplementOf e => ¬ classDenote I e x
  | .ObjectOneOf xs => ∃ a ∈ xs.elements, individual I a = x
  | .ObjectSomeValuesFrom p e => ∃ y, objectRelation I p x y ∧ classDenote I e y
  | .ObjectAllValuesFrom p e => ∀ y, objectRelation I p x y → classDenote I e y
  | .ObjectHasValue p a => objectRelation I p x (individual I a)
  | .ObjectHasSelf p => objectRelation I p x x
  | .ObjectMinCardinality n p e => AtLeast (Probes.naturalValue n)
      (fun y => objectRelation I p x y ∧ match e with | none => True | some c => classDenote I c y)
  | .ObjectMaxCardinality n p e => AtMost (Probes.naturalValue n)
      (fun y => objectRelation I p x y ∧ match e with | none => True | some c => classDenote I c y)
  | .ObjectExactCardinality n p e => Exactly (Probes.naturalValue n)
      (fun y => objectRelation I p x y ∧ match e with | none => True | some c => classDenote I c y)
  | .DataSomeValuesFrom p e => ∃ y, I.dataProperties p x y ∧ dataDenote I e y
  | .DataAllValuesFrom p e => ∀ y, I.dataProperties p x y → dataDenote I e y
  | .DataHasValue p lt => I.dataProperties p x (I.literals lt)
  | .DataMinCardinality n p e => AtLeast (Probes.naturalValue n)
      (fun y => I.dataProperties p x y ∧ match e with | none => True | some r => dataDenote I r y)
  | .DataMaxCardinality n p e => AtMost (Probes.naturalValue n)
      (fun y => I.dataProperties p x y ∧ match e with | none => True | some r => dataDenote I r y)
  | .DataExactCardinality n p e => Exactly (Probes.naturalValue n)
      (fun y => I.dataProperties p x y ∧ match e with | none => True | some r => dataDenote I r y)
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

def chainRelation (I : Interpretation Object Value) : List ObjectPropertyExpression → Object → Object → Prop
  | [], x, y => x = y
  | p :: ps, x, y => ∃ z, objectRelation I p x z ∧ chainRelation I ps z y

def subRelation (I : Interpretation Object Value) : SubObjectPropertyExpression → Object → Object → Prop
  | .Single p => objectRelation I p
  | .Chain ps => chainRelation I ps.elements

def allEqual {α : Type} {β : Sort u} (xs : List α) (f : α → β) : Prop :=
  ∀ a ∈ xs, ∀ b ∈ xs, f a = f b
def pairwiseDisjoint {α : Type} {β : Type u} (xs : List α) (f : α → β → Prop) : Prop :=
  xs.Pairwise (fun a b => ∀ x, ¬ (f a x ∧ f b x))

/-- §2.3, Tables 5–10. The match is exhaustive over all 37 Rust axiom variants.
    Disjointness and difference compare *occurrences*, not syntactic inequality.
    Annotation axioms and declarations have no logical satisfaction condition. -/
def satisfies (I : Interpretation Object Value) : Axiom → Prop
  | .Declaration _ => True
  | .SubClassOf a b => ∀ x, classDenote I a x → classDenote I b x
  | .EquivalentClasses xs => allEqual xs.elements (classDenote I)
  | .DisjointClasses xs => pairwiseDisjoint xs.elements (classDenote I)
  | .DisjointUnion c xs =>
      (∀ x, I.classes c x ↔ ∃ e ∈ xs.elements, classDenote I e x) ∧
      pairwiseDisjoint xs.elements (classDenote I)
  | .SubObjectPropertyOf a b => ∀ x y, subRelation I a x y → objectRelation I b x y
  | .EquivalentObjectProperties xs => allEqual xs.elements (objectRelation I)
  | .DisjointObjectProperties xs => pairwiseDisjoint xs.elements
      (fun p (xy : Object × Object) => objectRelation I p xy.1 xy.2)
  | .InverseObjectProperties p q => ∀ x y, objectRelation I p x y ↔ objectRelation I q y x
  | .ObjectPropertyDomain p e => ∀ x y, objectRelation I p x y → classDenote I e x
  | .ObjectPropertyRange p e => ∀ x y, objectRelation I p x y → classDenote I e y
  | .FunctionalObjectProperty p => ∀ x y z, objectRelation I p x y → objectRelation I p x z → y = z
  | .InverseFunctionalObjectProperty p => ∀ x y z, objectRelation I p x z → objectRelation I p y z → x = y
  | .ReflexiveObjectProperty p => ∀ x, objectRelation I p x x
  | .IrreflexiveObjectProperty p => ∀ x, ¬ objectRelation I p x x
  | .SymmetricObjectProperty p => ∀ x y, objectRelation I p x y → objectRelation I p y x
  | .AsymmetricObjectProperty p => ∀ x y, objectRelation I p x y → ¬ objectRelation I p y x
  | .TransitiveObjectProperty p => ∀ x y z, objectRelation I p x y → objectRelation I p y z → objectRelation I p x z
  | .SubDataPropertyOf p q => ∀ x y, I.dataProperties p x y → I.dataProperties q x y
  | .EquivalentDataProperties xs => allEqual xs.elements (I.dataProperties)
  | .DisjointDataProperties xs => pairwiseDisjoint xs.elements (fun p (xy : Object × Value) => I.dataProperties p xy.1 xy.2)
  | .DataPropertyDomain p e => ∀ x y, I.dataProperties p x y → classDenote I e x
  | .DataPropertyRange p r => ∀ x y, I.dataProperties p x y → dataDenote I r y
  | .FunctionalDataProperty p => ∀ x y z, I.dataProperties p x y → I.dataProperties p x z → y = z
  | .DatatypeDefinition dt r => ∀ x, I.datatypes dt x ↔ dataDenote I r x
  | .HasKey e ops dps => ∀ x y, classDenote I e x → I.named x → classDenote I e y → I.named y →
      (∀ p ∈ ops.val, ∃ z, I.named z ∧ objectRelation I p x z ∧ objectRelation I p y z) →
      (∀ p ∈ dps.val, ∃ z, I.dataProperties p x z ∧ I.dataProperties p y z) → x = y
  | .SameIndividual xs => allEqual xs.elements (individual I)
  | .DifferentIndividuals xs => xs.elements.Pairwise (fun a b => individual I a ≠ individual I b)
  | .ClassAssertion e a => classDenote I e (individual I a)
  | .ObjectPropertyAssertion p a b => objectRelation I p (individual I a) (individual I b)
  | .NegativeObjectPropertyAssertion p a b => ¬ objectRelation I p (individual I a) (individual I b)
  | .DataPropertyAssertion p a lt => I.dataProperties p (individual I a) (I.literals lt)
  | .NegativeDataPropertyAssertion p a lt => ¬ I.dataProperties p (individual I a) (I.literals lt)
  | .AnnotationAssertion _ _ _ => True
  | .SubAnnotationPropertyOf _ _ => True
  | .AnnotationPropertyDomain _ _ => True
  | .AnnotationPropertyRange _ _ => True

/-- Imports and standardization apart have already produced this closure.
    Computing it from RawOntology/import bytes is expressly the future M3 task. -/
abbrev AxiomClosure := List AnnotatedAxiom
def satisfiesClosure (I : Interpretation Object Value) (closure : AxiomClosure) : Prop :=
  ∀ a ∈ closure, satisfies I a.axiom

def withAnonymous (I : Interpretation Object Value) (assignment : AnonymousIndividual → Object) :
    Interpretation Object Value := { I with anonymousIndividuals := assignment }

/-- §2.4: a model permits reinterpretation of the anonymous input individuals.
    Named denotations and all other interpretation components stay fixed. -/
def modelsClosure (I : Interpretation Object Value) (closure : AxiomClosure) : Prop :=
  ∃ assignment, satisfiesClosure (withAnonymous I assignment) closure

def Model {Native : Type w} (D : DatatypeMap Native) (embed : ValueEmbedding D Value)
    (V : Vocabulary) (I : Interpretation Object Value)
    (closure : AxiomClosure) : Prop :=
  IsVocabulary D V ∧ IsInterpretation D embed V I ∧ modelsClosure I closure

/-- §2.5; universe-polymorphic model predicates, with no finite-domain restriction. -/
def Consistent {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary) (closure : AxiomClosure) : Prop :=
  ∃ (Object : Type u) (Value : Type v) (embed : ValueEmbedding D Value) (I : Interpretation Object Value),
    Model D embed V I closure
def Entails {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary) (source target : AxiomClosure) : Prop :=
  ∀ (Object : Type u) (Value : Type v) (embed : ValueEmbedding D Value) (I : Interpretation Object Value),
    Model D embed V I source → Model D embed V I target
def ClassSatisfiable {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary) (closure : AxiomClosure)
    (e : ClassExpression) : Prop :=
  ∃ (Object : Type u) (Value : Type v) (embed : ValueEmbedding D Value) (I : Interpretation Object Value),
    Model D embed V I closure ∧ ∃ x, classDenote I e x
def Subsumed {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary) (closure : AxiomClosure)
    (a b : ClassExpression) : Prop :=
  ∀ (Object : Type u) (Value : Type v) (embed : ValueEmbedding D Value) (I : Interpretation Object Value),
    Model D embed V I closure →
    ∀ x, classDenote I a x → classDenote I b x

def Equivalent {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (source target : AxiomClosure) : Prop := Entails.{u,v,w} D V source target ∧ Entails.{u,v,w} D V target source
def Equisatisfiable {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (source target : AxiomClosure) : Prop := Consistent.{u,v,w} D V source ↔ Consistent.{u,v,w} D V target
def InstanceOf {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (closure : AxiomClosure) (a : NamedIndividual) (e : ClassExpression) : Prop :=
  ∀ (Object : Type u) (Value : Type v) (embed : ValueEmbedding D Value) (I : Interpretation Object Value),
    Model D embed V I closure → classDenote I e (I.namedIndividuals a)

/-- The standard's Boolean conjunctive-query definition is specified here for
    completeness; implementing a general graph-query interface is out of scope. -/
inductive ObjectTerm where
  | individual : Individual → ObjectTerm
  | variable : Nat → ObjectTerm
inductive DataTerm where
  | literal : Literal → DataTerm
  | variable : Nat → DataTerm
inductive QueryAtom where
  | classAtom : Class → ObjectTerm → QueryAtom
  | objectAtom : ObjectProperty → ObjectTerm → ObjectTerm → QueryAtom
  | dataAtom : DataProperty → ObjectTerm → DataTerm → QueryAtom
def objectTerm (I : Interpretation Object Value) (assignment : Nat → Object) : ObjectTerm → Object
  | .individual a => individual I a
  | .variable n => assignment n
def dataTerm (I : Interpretation Object Value) (assignment : Nat → Value) : DataTerm → Value
  | .literal lt => I.literals lt
  | .variable n => assignment n
def queryAtom (I : Interpretation Object Value) (objects : Nat → Object) (data : Nat → Value) : QueryAtom → Prop
  | .classAtom c x => I.classes c (objectTerm I objects x)
  | .objectAtom p x y => I.objectProperties p (objectTerm I objects x) (objectTerm I objects y)
  | .dataAtom p x y => I.dataProperties p (objectTerm I objects x) (dataTerm I data y)
def queryHolds (I : Interpretation Object Value) (atoms : List QueryAtom) : Prop :=
  ∃ objects data, ∀ a ∈ atoms, queryAtom I objects data a
def Answers {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (closure : AxiomClosure) (atoms : List QueryAtom) : Prop :=
  ∀ (Object : Type u) (Value : Type v) (embed : ValueEmbedding D Value) (I : Interpretation Object Value),
    Model D embed V I closure → queryHolds I atoms

end Rowl.Owl
