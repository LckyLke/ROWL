import Rowl.DataAxioms
import Rowl.DatatypeMap

/-!
# Taking a model apart along the assertions

When the axioms other than assertions name no individual and use neither top
property, the models of a closure can be combined along the individuals: a
model of one part of the assertions and a model of the rest, which share no
individual, give a model of both, the disjoint union of the two. Its data
domain is the sum of the two data domains, with every datatype value of the
second carried to the first by the embeddings, so literals, datatypes and the
range facets mean the same on both sides.
-/

namespace Rowl.Partition
open Aeneas Aeneas.Std RowlRust.model Rowl.Owl
open Rowl.DataMeaning (classIndividuals)
open Rowl.DataAxioms (axiomIndividuals)

universe u v w

section Sizes
variable {α : Type} [SizeOf α]

private theorem listN_mem_size {n : Nat} (xs : Aeneas.Data.ListN.ListN α n) {x : α} (h : x ∈ xs.toList) :
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

private theorem vec_mem_size (xs : alloc.vec.Vec α) {x : α} (h : x ∈ xs.val) : sizeOf x < sizeOf xs := by
  have := listN_mem_size xs.slice.list h
  cases xs with | mk slice => cases slice; simp_all [alloc.vec.Vec.val, Slice.val]; omega

private theorem first_size (xs : AtLeastTwo α) : sizeOf xs.first < sizeOf xs := by cases xs; simp +arith
private theorem second_size (xs : AtLeastTwo α) : sizeOf xs.second < sizeOf xs := by cases xs; simp +arith
private theorem rest_size (xs : AtLeastTwo α) : sizeOf xs.rest < sizeOf xs := by cases xs; simp +arith

end Sizes

/-! ## What the combination needs of the axioms -/

/-- An assertion: a statement about individuals. -/
def IsAssertion : Axiom → Prop
  | .ClassAssertion _ _ | .ObjectPropertyAssertion _ _ _ | .NegativeObjectPropertyAssertion _ _ _
  | .DataPropertyAssertion _ _ _ | .NegativeDataPropertyAssertion _ _ _
  | .SameIndividual _ | .DifferentIndividuals _ => True
  | _ => False

/-- An axiom without meaning in a model: a declaration or an annotation axiom. -/
def Meaningless : Axiom → Prop
  | .Declaration _ | .AnnotationAssertion _ _ _ | .SubAnnotationPropertyOf _ _
  | .AnnotationPropertyDomain _ _ | .AnnotationPropertyRange _ _ => True
  | _ => False

private theorem meaningless_satisfied {O : Type u} {W : Type v} (I : Interpretation O W) {ax : Axiom}
    (meaningless : Meaningless ax) : satisfies I ax := by
  cases ax <;> simp only [Meaningless] at meaningless <;> trivial

/-- A role that is not the top object property, either way round. -/
def NotTop : ObjectPropertyExpression → Prop
  | .Property p => p ≠ topObject
  | .Inverse p => p ≠ topObject

variable {Native : Type w}

/-- A data range whose meaning the datatype map fixes in every interpretation
    for the vocabulary: its datatypes are supported or `rdfs:Literal`, its
    literals are in the vocabulary, and each of its facets is in the
    vocabulary with a facet value of datatype values only. -/
def Standard (D : DatatypeMap Native) (V : Vocabulary) (r : DataRange) : Prop :=
  match r with
  | .Datatype dt => D.supported dt ∨ dt = literalDatatype
  | .Intersection xs => Standard D V xs.first ∧ Standard D V xs.second ∧ ∀ e ∈ xs.rest.val, Standard D V e
  | .Union xs => Standard D V xs.first ∧ Standard D V xs.second ∧ ∀ e ∈ xs.rest.val, Standard D V e
  | .Complement e => Standard D V e
  | .OneOf xs => ∀ lt ∈ xs.elements, V.literals lt
  | .Restriction dt xs => D.supported dt ∧ ∀ f ∈ xs.elements, V.facets f ∧
      ∀ y, D.facetValue f.facet (D.lexicalValue f.value.datatype f.value.lexical.val) y → isDatatypeValue D y
termination_by sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

/-- A class expression that uses neither top property, whose data ranges and
    literals are standard, and whose individuals satisfy `side`. -/
def Plain (D : DatatypeMap Native) (V : Vocabulary) (side : Individual → Prop) (c : ClassExpression) : Prop :=
  match c with
  | .Class _ => True
  | .ObjectIntersectionOf xs => Plain D V side xs.first ∧ Plain D V side xs.second ∧
      ∀ e ∈ xs.rest.val, Plain D V side e
  | .ObjectUnionOf xs => Plain D V side xs.first ∧ Plain D V side xs.second ∧
      ∀ e ∈ xs.rest.val, Plain D V side e
  | .ObjectComplementOf e => Plain D V side e
  | .ObjectOneOf xs => ∀ a ∈ xs.elements, side a
  | .ObjectSomeValuesFrom p e => NotTop p ∧ Plain D V side e
  | .ObjectAllValuesFrom p e => NotTop p ∧ Plain D V side e
  | .ObjectHasValue p a => NotTop p ∧ side a
  | .ObjectHasSelf p => NotTop p
  | .ObjectMinCardinality _ p none | .ObjectMaxCardinality _ p none | .ObjectExactCardinality _ p none => NotTop p
  | .ObjectMinCardinality _ p (some e) | .ObjectMaxCardinality _ p (some e)
  | .ObjectExactCardinality _ p (some e) => NotTop p ∧ Plain D V side e
  | .DataSomeValuesFrom p r => p ≠ topData ∧ Standard D V r
  | .DataAllValuesFrom p r => p ≠ topData ∧ Standard D V r
  | .DataHasValue p lt => p ≠ topData ∧ V.literals lt
  | .DataMinCardinality _ p none | .DataMaxCardinality _ p none | .DataExactCardinality _ p none => p ≠ topData
  | .DataMinCardinality _ p (some r) | .DataMaxCardinality _ p (some r)
  | .DataExactCardinality _ p (some r) => p ≠ topData ∧ Standard D V r
termination_by sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

/-! ## The combined interpretation -/

section Join
variable {D : DatatypeMap Native} {O1 O2 : Type u} {V1 V2 : Type v}

/-- A value of the second data domain that embeds no datatype value. -/
def Junk (e2 : ValueEmbedding D V2) (x : V2) : Prop := ¬ ∃ n, isDatatypeValue D n ∧ e2 n = x

open Classical in
/-- The second data domain carried into the combined one: the embedding of a
    datatype value to the first embedding of the same value, anything else to
    itself on the right. -/
noncomputable def carry (e1 : ValueEmbedding D V1) (e2 : ValueEmbedding D V2) (x : V2) : V1 ⊕ V2 :=
  if h : ∃ n, isDatatypeValue D n ∧ e2 n = x then .inl (e1 (Classical.choose h)) else .inr x

private theorem carry_value (e1 : ValueEmbedding D V1) (e2 : ValueEmbedding D V2) {n : Native}
    (value : isDatatypeValue D n) : carry e1 e2 (e2 n) = .inl (e1 n) := by
  have h : ∃ m, isDatatypeValue D m ∧ e2 m = e2 n := ⟨n, value, rfl⟩
  rw [carry, dif_pos h]
  obtain ⟨chosen, same⟩ := Classical.choose_spec h
  rw [e2.injectiveValues _ _ chosen value same]

private theorem carry_junk (e1 : ValueEmbedding D V1) (e2 : ValueEmbedding D V2) {x : V2} (junk : Junk e2 x) :
    carry e1 e2 x = .inr x := by
  rw [carry, dif_neg junk]

private theorem carry_cases (e1 : ValueEmbedding D V1) (e2 : ValueEmbedding D V2) (x : V2) :
    (∃ n, isDatatypeValue D n ∧ e2 n = x ∧ carry e1 e2 x = .inl (e1 n)) ∨ (Junk e2 x ∧ carry e1 e2 x = .inr x) := by
  by_cases h : ∃ n, isDatatypeValue D n ∧ e2 n = x
  · obtain ⟨n, value, rfl⟩ := h
    exact .inl ⟨n, value, rfl, carry_value e1 e2 value⟩
  · exact .inr ⟨h, carry_junk e1 e2 h⟩

private theorem carry_injective (e1 : ValueEmbedding D V1) (e2 : ValueEmbedding D V2) :
    Function.Injective (carry e1 e2) := by
  intro x y same
  rcases carry_cases e1 e2 x with ⟨n, vn, rfl, cx⟩ | ⟨jx, cx⟩ <;>
    rcases carry_cases e1 e2 y with ⟨m, vm, rfl, cy⟩ | ⟨jy, cy⟩
  · rw [cx, cy, Sum.inl.injEq] at same
    rw [e1.injectiveValues _ _ vn vm same]
  · rw [cx, cy] at same; cases same
  · rw [cx, cy] at same; cases same
  · rw [cx, cy, Sum.inr.injEq] at same
    exact same

/-- The embedding of the combined data domain: the first one, on the left. -/
def leftEmbedding (e1 : ValueEmbedding D V1) : ValueEmbedding D (V1 ⊕ V2) :=
  ⟨fun n => .inl (e1 n), fun x y vx vy same => e1.injectiveValues x y vx vy (Sum.inl.inj same)⟩

open Classical in
/-- The disjoint union of two interpretations: the individuals that `left`
    holds of in the first, the others in the second. -/
noncomputable def join (e1 : ValueEmbedding D V1) (e2 : ValueEmbedding D V2) (left : Individual → Prop)
    (I1 : Interpretation O1 V1) (I2 : Interpretation O2 V2) : Interpretation (O1 ⊕ O2) (V1 ⊕ V2) where
  objectsNonempty := ⟨.inl (Classical.choice I1.objectsNonempty)⟩
  dataNonempty := ⟨.inl (Classical.choice I1.dataNonempty)⟩
  classes c x := Sum.elim (I1.classes c) (I2.classes c) x
  objectProperties p x y := p = topObject ∨ match x, y with
    | .inl a, .inl b => I1.objectProperties p a b
    | .inr a, .inr b => I2.objectProperties p a b
    | _, _ => False
  dataProperties p x y := p = topData ∨ match x with
    | .inl a => ∃ z, I1.dataProperties p a z ∧ .inl z = y
    | .inr a => ∃ z, I2.dataProperties p a z ∧ carry e1 e2 z = y
  namedIndividuals a := if left (.Named a) then .inl (I1.namedIndividuals a) else .inr (I2.namedIndividuals a)
  anonymousIndividuals a :=
    if left (.Anonymous a) then .inl (I1.anonymousIndividuals a) else .inr (I2.anonymousIndividuals a)
  datatypes dt x := match x with
    | .inl z => I1.datatypes dt z
    | .inr z => dt = literalDatatype ∨ (I2.datatypes dt z ∧ Junk e2 z)
  literals lt := .inl (I1.literals lt)
  facets f x := match x with
    | .inl z => I1.facets f z
    | .inr _ => False
  named x := Sum.elim I1.named I2.named x

private theorem bottom_ne_top : bottomObject ≠ topObject := by
  intro h
  have := congrArg (fun p : ObjectProperty => p.iri.spelling.val) h
  simp [bottomObject, topObject] at this

private theorem bottom_data_ne_top : bottomData ≠ topData := by
  intro h
  have := congrArg (fun p : DataProperty => p.iri.spelling.val) h
  simp [bottomData, topData] at this

/-- The combination is an interpretation for the vocabulary. -/
theorem join_interpretation (V : Vocabulary) (e1 : ValueEmbedding D V1) (e2 : ValueEmbedding D V2)
    (left : Individual → Prop) (I1 : Interpretation O1 V1) (I2 : Interpretation O2 V2)
    (h1 : IsInterpretation D e1 V I1) (h2 : IsInterpretation D e2 V I2) :
    IsInterpretation D (leftEmbedding e1) V (join e1 e2 left I1 I2) := by
  obtain ⟨t1, n1, to1, bo1, td1, bd1, dt1, lit1, lt1, f1, nm1⟩ := h1
  obtain ⟨t2, n2, to2, bo2, td2, bd2, dt2, lit2, lt2, f2, nm2⟩ := h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (x | x)
    · exact t1 x
    · exact t2 x
  · rintro (x | x)
    · exact n1 x
    · exact n2 x
  · intro x y
    exact .inl rfl
  · rintro (x | x) (y | y) (h | h)
    · exact bottom_ne_top h
    · exact bo1 x y h
    · exact bottom_ne_top h
    · exact h
    · exact bottom_ne_top h
    · exact h
    · exact bottom_ne_top h
    · exact bo2 x y h
  · intro x y
    exact .inl rfl
  · rintro (x | x) y (h | ⟨z, rel, -⟩)
    · exact bottom_data_ne_top h
    · exact bd1 x z rel
    · exact bottom_data_ne_top h
    · exact bd2 x z rel
  · intro dt supported x
    rcases x with z | z
    · simp only [join, leftEmbedding]
      rw [dt1 dt supported z]
      simp
    · simp only [join, leftEmbedding, reduceCtorEq, and_false, exists_false, iff_false, not_or, not_and]
      refine ⟨fun same => D.excludesLiteral (same ▸ supported), fun has junk => ?_⟩
      obtain ⟨y, space, rfl⟩ := (dt2 dt supported z).mp has
      exact junk ⟨y, ⟨dt, supported, space⟩, rfl⟩
  · rintro (z | z)
    · exact lit1 z
    · exact .inl rfl
  · intro lt known
    simp only [join, leftEmbedding]
    rw [lt1 lt known]
  · intro f known x
    rcases x with z | z
    · simp only [join, leftEmbedding]
      rw [f1 f known z]
      simp
    · simp [join, leftEmbedding]
  · intro a known
    by_cases side : left (.Named a)
    · simp only [join, side, if_true, Sum.elim_inl]
      exact nm1 a known
    · simp only [join, side, if_false, Sum.elim_inr]
      exact nm2 a known

end Join

/-! ## One side of the combination -/

section Simulation
variable {D : DatatypeMap Native} {V : Vocabulary} {O O' : Type u} {W W' : Type v}

private theorem atLeast_image {α β : Type _} (n : Nat) (P : α → Prop) (Q : β → Prop) (f : α → β)
    (injective : Function.Injective f) (same : ∀ b, Q b ↔ ∃ a, f a = b ∧ P a) : AtLeast n P ↔ AtLeast n Q := by
  constructor
  · rintro ⟨g, gInjective, each⟩
    exact ⟨f ∘ g, injective.comp gInjective, fun i => (same _).mpr ⟨g i, rfl, each i⟩⟩
  · rintro ⟨g, gInjective, each⟩
    choose h hf hp using fun i => (same (g i)).mp (each i)
    refine ⟨h, fun i j eq => gInjective ?_, hp⟩
    rw [← hf i, ← hf j, eq]

private theorem atMost_image {α β : Type _} (n : Nat) (P : α → Prop) (Q : β → Prop) (f : α → β)
    (injective : Function.Injective f) (same : ∀ b, Q b ↔ ∃ a, f a = b ∧ P a) : AtMost n P ↔ AtMost n Q :=
  not_congr (atLeast_image (n + 1) P Q f injective same)

private theorem exactly_image {α β : Type _} (n : Nat) (P : α → Prop) (Q : β → Prop) (f : α → β)
    (injective : Function.Injective f) (same : ∀ b, Q b ↔ ∃ a, f a = b ∧ P a) : Exactly n P ↔ Exactly n Q :=
  and_congr (atLeast_image n P Q f injective same) (atMost_image n P Q f injective same)

/-- How one interpretation sits inside another: its elements and values at
    their images, one to one, with the same classes, every role other than the
    top one relating an image only to images, as the role relates the
    elements, the same for data properties other than the top one and values,
    standard data ranges and literals meaning the same, and the individuals
    that `side` holds of at the images of their elements. -/
structure Side (D : DatatypeMap Native) (V : Vocabulary) (I : Interpretation O W) (U : Interpretation O' W')
    (obj : O → O') (val : W → W') (side : Individual → Prop) : Prop where
  objects : Function.Injective obj
  values : Function.Injective val
  classes : ∀ c x, U.classes c (obj x) ↔ I.classes c x
  roles : ∀ p, NotTop p → ∀ x y, objectRelation U p (obj x) y ↔ ∃ z, obj z = y ∧ objectRelation I p x z
  data : ∀ p, p ≠ topData → ∀ x y, U.dataProperties p (obj x) y ↔ ∃ z, val z = y ∧ I.dataProperties p x z
  ranges : ∀ r, Standard D V r → ∀ y, dataDenote U r (val y) ↔ dataDenote I r y
  literals : ∀ lt, V.literals lt → U.literals lt = val (I.literals lt)
  individuals : ∀ a, side a → individual U a = obj (individual I a)

variable {I : Interpretation O W} {U : Interpretation O' W'} {obj : O → O'} {val : W → W'}
  {side : Individual → Prop}

/-- The filler condition of an object number restriction. -/
def classFiller (I : Interpretation O W) (filler : Option ClassExpression) (y : O) : Prop :=
  match filler with
  | none => True
  | some c => classDenote I c y

/-- The filler condition of a data number restriction. -/
def rangeFiller (I : Interpretation O W) (filler : Option DataRange) (y : W) : Prop :=
  match filler with
  | none => True
  | some r => dataDenote I r y

private theorem side_role (s : Side D V I U obj val side) {p : ObjectPropertyExpression} (np : NotTop p) (x z : O) :
    objectRelation U p (obj x) (obj z) ↔ objectRelation I p x z := by
  rw [s.roles p np x (obj z)]
  constructor
  · rintro ⟨z', same, rel⟩
    rwa [← s.objects same]
  · intro rel
    exact ⟨z, rfl, rel⟩

private theorem side_data (s : Side D V I U obj val side) {p : DataProperty} (np : p ≠ topData) (x : O) (z : W) :
    U.dataProperties p (obj x) (val z) ↔ I.dataProperties p x z := by
  rw [s.data p np x (val z)]
  constructor
  · rintro ⟨z', same, rel⟩
    rwa [← s.values same]
  · intro rel
    exact ⟨z, rfl, rel⟩

private theorem side_range_filler (s : Side D V I U obj val side) (filler : Option DataRange)
    (standard : ∀ r, filler = some r → Standard D V r) (y : W) :
    rangeFiller U filler (val y) ↔ rangeFiller I filler y := by
  cases filler with
  | none => exact Iff.rfl
  | some r => exact s.ranges r (standard r rfl) y

/-- A plain class expression means the same at an element and at its image. -/
theorem side_class (s : Side D V I U obj val side) (c : ClassExpression) :
    Plain D V side c → ∀ x, (classDenote U c (obj x) ↔ classDenote I c x) := by
  cases c with
  | Class c => intro _ x; simp only [classDenote]; exact s.classes c x
  | ObjectIntersectionOf xs =>
    intro plain x
    rw [Plain] at plain
    obtain ⟨pf, ps, pr⟩ := plain
    have first := side_class s xs.first pf x
    have second := side_class s xs.second ps x
    have rest : ∀ e ∈ xs.rest.val, (classDenote U e (obj x) ↔ classDenote I e x) :=
      fun e member => side_class s e (pr e member) x
    simp only [classDenote]
    exact and_congr first (and_congr second (forall₂_congr fun e member => rest e member))
  | ObjectUnionOf xs =>
    intro plain x
    rw [Plain] at plain
    obtain ⟨pf, ps, pr⟩ := plain
    have first := side_class s xs.first pf x
    have second := side_class s xs.second ps x
    have rest : ∀ e ∈ xs.rest.val, (classDenote U e (obj x) ↔ classDenote I e x) :=
      fun e member => side_class s e (pr e member) x
    simp only [classDenote]
    exact or_congr first (or_congr second (exists_congr fun e => exists_congr fun member => rest e member))
  | ObjectComplementOf inner =>
    intro plain x
    rw [Plain] at plain
    simp only [classDenote]
    exact not_congr (side_class s inner plain x)
  | ObjectOneOf xs =>
    intro plain x
    rw [Plain] at plain
    simp only [classDenote]
    constructor
    · rintro ⟨a, member, same⟩
      rw [s.individuals a (plain a member)] at same
      exact ⟨a, member, s.objects same⟩
    · rintro ⟨a, member, same⟩
      exact ⟨a, member, by rw [s.individuals a (plain a member), same]⟩
  | ObjectSomeValuesFrom p inner =>
    intro plain x
    rw [Plain] at plain
    obtain ⟨np, pi⟩ := plain
    simp only [classDenote]
    constructor
    · rintro ⟨y, rel, inner'⟩
      obtain ⟨z, rfl, rel'⟩ := (s.roles p np x y).mp rel
      exact ⟨z, rel', (side_class s inner pi z).mp inner'⟩
    · rintro ⟨z, rel, inner'⟩
      exact ⟨obj z, (side_role s np x z).mpr rel, (side_class s inner pi z).mpr inner'⟩
  | ObjectAllValuesFrom p inner =>
    intro plain x
    rw [Plain] at plain
    obtain ⟨np, pi⟩ := plain
    simp only [classDenote]
    constructor
    · intro all z rel
      exact (side_class s inner pi z).mp (all (obj z) ((side_role s np x z).mpr rel))
    · intro all y rel
      obtain ⟨z, rfl, rel'⟩ := (s.roles p np x y).mp rel
      exact (side_class s inner pi z).mpr (all z rel')
  | ObjectHasValue p a =>
    intro plain x
    rw [Plain] at plain
    obtain ⟨np, sa⟩ := plain
    simp only [classDenote]
    rw [s.individuals a sa]
    exact side_role s np x _
  | ObjectHasSelf p =>
    intro plain x
    rw [Plain] at plain
    simp only [classDenote]
    exact side_role s plain x x
  | ObjectMinCardinality n p filler =>
    intro plain x
    have np : NotTop p := by cases filler <;> (rw [Plain] at plain) <;> first | exact plain | exact plain.1
    have fillers : ∀ z, classFiller U filler (obj z) ↔ classFiller I filler z := by
      intro z
      cases h : filler with
      | none => exact Iff.rfl
      | some c =>
        have : sizeOf c < sizeOf filler := by rw [h]; simp +arith
        rw [h, Plain] at plain
        exact side_class s c plain.2 z
    rw [classDenote.eq_def, classDenote.eq_def]
    change AtLeast (Rowl.Probes.naturalValue n) (fun y => objectRelation U p (obj x) y ∧ classFiller U filler y) ↔
      AtLeast (Rowl.Probes.naturalValue n) (fun y => objectRelation I p x y ∧ classFiller I filler y)
    symm
    apply atLeast_image _ _ _ obj s.objects
    intro y
    constructor
    · rintro ⟨rel, fill⟩
      obtain ⟨z, rfl, rel'⟩ := (s.roles p np x y).mp rel
      exact ⟨z, rfl, rel', (fillers z).mp fill⟩
    · rintro ⟨z, rfl, rel, fill⟩
      exact ⟨(side_role s np x z).mpr rel, (fillers z).mpr fill⟩
  | ObjectMaxCardinality n p filler =>
    intro plain x
    have np : NotTop p := by cases filler <;> (rw [Plain] at plain) <;> first | exact plain | exact plain.1
    have fillers : ∀ z, classFiller U filler (obj z) ↔ classFiller I filler z := by
      intro z
      cases h : filler with
      | none => exact Iff.rfl
      | some c =>
        have : sizeOf c < sizeOf filler := by rw [h]; simp +arith
        rw [h, Plain] at plain
        exact side_class s c plain.2 z
    rw [classDenote.eq_def, classDenote.eq_def]
    change AtMost (Rowl.Probes.naturalValue n) (fun y => objectRelation U p (obj x) y ∧ classFiller U filler y) ↔
      AtMost (Rowl.Probes.naturalValue n) (fun y => objectRelation I p x y ∧ classFiller I filler y)
    symm
    apply atMost_image _ _ _ obj s.objects
    intro y
    constructor
    · rintro ⟨rel, fill⟩
      obtain ⟨z, rfl, rel'⟩ := (s.roles p np x y).mp rel
      exact ⟨z, rfl, rel', (fillers z).mp fill⟩
    · rintro ⟨z, rfl, rel, fill⟩
      exact ⟨(side_role s np x z).mpr rel, (fillers z).mpr fill⟩
  | ObjectExactCardinality n p filler =>
    intro plain x
    have np : NotTop p := by cases filler <;> (rw [Plain] at plain) <;> first | exact plain | exact plain.1
    have fillers : ∀ z, classFiller U filler (obj z) ↔ classFiller I filler z := by
      intro z
      cases h : filler with
      | none => exact Iff.rfl
      | some c =>
        have : sizeOf c < sizeOf filler := by rw [h]; simp +arith
        rw [h, Plain] at plain
        exact side_class s c plain.2 z
    rw [classDenote.eq_def, classDenote.eq_def]
    change Exactly (Rowl.Probes.naturalValue n) (fun y => objectRelation U p (obj x) y ∧ classFiller U filler y) ↔
      Exactly (Rowl.Probes.naturalValue n) (fun y => objectRelation I p x y ∧ classFiller I filler y)
    symm
    apply exactly_image _ _ _ obj s.objects
    intro y
    constructor
    · rintro ⟨rel, fill⟩
      obtain ⟨z, rfl, rel'⟩ := (s.roles p np x y).mp rel
      exact ⟨z, rfl, rel', (fillers z).mp fill⟩
    · rintro ⟨z, rfl, rel, fill⟩
      exact ⟨(side_role s np x z).mpr rel, (fillers z).mpr fill⟩
  | DataSomeValuesFrom p r =>
    intro plain x
    rw [Plain] at plain
    obtain ⟨np, sr⟩ := plain
    simp only [classDenote]
    constructor
    · rintro ⟨y, rel, inR⟩
      obtain ⟨z, rfl, rel'⟩ := (s.data p np x y).mp rel
      exact ⟨z, rel', (s.ranges r sr z).mp inR⟩
    · rintro ⟨z, rel, inR⟩
      exact ⟨val z, (side_data s np x z).mpr rel, (s.ranges r sr z).mpr inR⟩
  | DataAllValuesFrom p r =>
    intro plain x
    rw [Plain] at plain
    obtain ⟨np, sr⟩ := plain
    simp only [classDenote]
    constructor
    · intro all z rel
      exact (s.ranges r sr z).mp (all (val z) ((side_data s np x z).mpr rel))
    · intro all y rel
      obtain ⟨z, rfl, rel'⟩ := (s.data p np x y).mp rel
      exact (s.ranges r sr z).mpr (all z rel')
  | DataHasValue p lt =>
    intro plain x
    rw [Plain] at plain
    obtain ⟨np, known⟩ := plain
    simp only [classDenote]
    rw [s.literals lt known]
    exact side_data s np x _
  | DataMinCardinality n p filler =>
    intro plain x
    have np : p ≠ topData := by cases filler <;> (rw [Plain] at plain) <;> first | exact plain | exact plain.1
    have standard : ∀ r, filler = some r → Standard D V r := by
      rintro r rfl
      rw [Plain] at plain
      exact plain.2
    rw [classDenote.eq_def, classDenote.eq_def]
    change AtLeast (Rowl.Probes.naturalValue n) (fun y => U.dataProperties p (obj x) y ∧ rangeFiller U filler y) ↔
      AtLeast (Rowl.Probes.naturalValue n) (fun y => I.dataProperties p x y ∧ rangeFiller I filler y)
    symm
    apply atLeast_image _ _ _ val s.values
    intro y
    constructor
    · rintro ⟨rel, fill⟩
      obtain ⟨z, rfl, rel'⟩ := (s.data p np x y).mp rel
      exact ⟨z, rfl, rel', (side_range_filler s filler standard z).mp fill⟩
    · rintro ⟨z, rfl, rel, fill⟩
      exact ⟨(side_data s np x z).mpr rel, (side_range_filler s filler standard z).mpr fill⟩
  | DataMaxCardinality n p filler =>
    intro plain x
    have np : p ≠ topData := by cases filler <;> (rw [Plain] at plain) <;> first | exact plain | exact plain.1
    have standard : ∀ r, filler = some r → Standard D V r := by
      rintro r rfl
      rw [Plain] at plain
      exact plain.2
    rw [classDenote.eq_def, classDenote.eq_def]
    change AtMost (Rowl.Probes.naturalValue n) (fun y => U.dataProperties p (obj x) y ∧ rangeFiller U filler y) ↔
      AtMost (Rowl.Probes.naturalValue n) (fun y => I.dataProperties p x y ∧ rangeFiller I filler y)
    symm
    apply atMost_image _ _ _ val s.values
    intro y
    constructor
    · rintro ⟨rel, fill⟩
      obtain ⟨z, rfl, rel'⟩ := (s.data p np x y).mp rel
      exact ⟨z, rfl, rel', (side_range_filler s filler standard z).mp fill⟩
    · rintro ⟨z, rfl, rel, fill⟩
      exact ⟨(side_data s np x z).mpr rel, (side_range_filler s filler standard z).mpr fill⟩
  | DataExactCardinality n p filler =>
    intro plain x
    have np : p ≠ topData := by cases filler <;> (rw [Plain] at plain) <;> first | exact plain | exact plain.1
    have standard : ∀ r, filler = some r → Standard D V r := by
      rintro r rfl
      rw [Plain] at plain
      exact plain.2
    rw [classDenote.eq_def, classDenote.eq_def]
    change Exactly (Rowl.Probes.naturalValue n) (fun y => U.dataProperties p (obj x) y ∧ rangeFiller U filler y) ↔
      Exactly (Rowl.Probes.naturalValue n) (fun y => I.dataProperties p x y ∧ rangeFiller I filler y)
    symm
    apply exactly_image _ _ _ val s.values
    intro y
    constructor
    · rintro ⟨rel, fill⟩
      obtain ⟨z, rfl, rel'⟩ := (s.data p np x y).mp rel
      exact ⟨z, rfl, rel', (side_range_filler s filler standard z).mp fill⟩
    · rintro ⟨z, rfl, rel, fill⟩
      exact ⟨(side_data s np x z).mpr rel, (side_range_filler s filler standard z).mpr fill⟩
termination_by sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

end Simulation

/-! ## The two sides of the combination -/

section Sides
variable {D : DatatypeMap Native} {V : Vocabulary} {O1 O2 : Type u} {V1 V2 : Type v}
variable (e1 : ValueEmbedding D V1) (e2 : ValueEmbedding D V2) (left : Individual → Prop)
  (I1 : Interpretation O1 V1) (I2 : Interpretation O2 V2)

/-- On the left, every data range means what it means in the first interpretation. -/
theorem left_range (r : DataRange) : ∀ y, dataDenote (join e1 e2 left I1 I2) r (.inl y) ↔ dataDenote I1 r y := by
  cases r with
  | Datatype dt => intro y; simp only [dataDenote]; rfl
  | Intersection xs =>
    intro y
    have first := left_range xs.first y
    have second := left_range xs.second y
    have rest : ∀ e ∈ xs.rest.val, (dataDenote (join e1 e2 left I1 I2) e (.inl y) ↔ dataDenote I1 e y) :=
      fun e _ => left_range e y
    simp only [dataDenote]
    exact and_congr first (and_congr second (forall₂_congr fun e member => rest e member))
  | Union xs =>
    intro y
    have first := left_range xs.first y
    have second := left_range xs.second y
    have rest : ∀ e ∈ xs.rest.val, (dataDenote (join e1 e2 left I1 I2) e (.inl y) ↔ dataDenote I1 e y) :=
      fun e _ => left_range e y
    simp only [dataDenote]
    exact or_congr first (or_congr second (exists_congr fun e => exists_congr fun member => rest e member))
  | Complement inner =>
    intro y
    simp only [dataDenote]
    exact not_congr (left_range inner y)
  | OneOf xs =>
    intro y
    simp only [dataDenote]
    exact exists_congr fun lt => and_congr_right fun _ => by simp [join]
  | Restriction dt xs => intro y; simp only [dataDenote]; rfl
termination_by sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

variable {e1 e2 left I1 I2}

/-- A supported datatype holds of the embedding of a datatype value exactly
    when the value is in its value space. -/
private theorem datatype_value {W : Type v} {e : ValueEmbedding D W} {I : Interpretation O1 W} {V : Vocabulary}
    (h : IsInterpretation D e V I) {dt : Datatype} (supported : D.supported dt) {n : Native}
    (value : isDatatypeValue D n) : I.datatypes dt (e n) ↔ D.valueSpace dt n := by
  rw [h.2.2.2.2.2.2.1 dt supported]
  constructor
  · rintro ⟨m, space, same⟩
    rwa [← e.injectiveValues m n ⟨dt, supported, space⟩ value same]
  · intro space
    exact ⟨n, space, rfl⟩

/-- A facet whose facet value has only datatype values holds of the
    embedding of a datatype value exactly when the facet value has it. -/
private theorem facet_value {W : Type v} {e : ValueEmbedding D W} {I : Interpretation O1 W} {V : Vocabulary}
    (h : IsInterpretation D e V I) {f : FacetRestriction} (known : V.facets f)
    (values : ∀ y, D.facetValue f.facet (D.lexicalValue f.value.datatype f.value.lexical.val) y → isDatatypeValue D y)
    {n : Native} (value : isDatatypeValue D n) :
    I.facets f (e n) ↔ D.facetValue f.facet (D.lexicalValue f.value.datatype f.value.lexical.val) n := by
  rw [h.2.2.2.2.2.2.2.2.2.1 f known]
  constructor
  · rintro ⟨m, has, same⟩
    rwa [← e.injectiveValues m n (values m has) value same]
  · intro has
    exact ⟨n, has, rfl⟩

/-- The lexical value of a literal of the vocabulary is a datatype value. -/
private theorem literal_datatype_value (vocab : IsVocabulary D V) {lt : Literal} (known : V.literals lt) :
    isDatatypeValue D (D.lexicalValue lt.datatype lt.lexical.val) := by
  obtain ⟨supported, lexical⟩ := (vocab.2.2.2.2.2.2.2.2.1 lt).mp known
  exact ⟨lt.datatype, supported, D.lexicalInSpace _ _ supported lexical⟩

private theorem carry_eq_left {m : Native} (value : isDatatypeValue D m) (y : V2) :
    Sum.inl (e1 m) = carry e1 e2 y ↔ e2 m = y := by
  constructor
  · intro same
    rcases carry_cases e1 e2 y with ⟨n, vn, rfl, cy⟩ | ⟨_, cy⟩
    · rw [cy, Sum.inl.injEq] at same
      rw [e1.injectiveValues m n value vn same]
    · rw [cy] at same
      cases same
  · rintro rfl
    rw [carry_value e1 e2 value]

/-- On the right, a standard data range means what it means in the second
    interpretation, at the carried values. -/
theorem right_range (vocab : IsVocabulary D V) (h1 : IsInterpretation D e1 V I1) (h2 : IsInterpretation D e2 V I2)
    (r : DataRange) : Standard D V r → ∀ y, (dataDenote (join e1 e2 left I1 I2) r (carry e1 e2 y) ↔ dataDenote I2 r y) := by
  cases r with
  | Datatype dt =>
    intro standard y
    rw [Standard] at standard
    simp only [dataDenote]
    rcases carry_cases e1 e2 y with ⟨n, vn, rfl, cy⟩ | ⟨junk, cy⟩
    · rw [cy]
      change I1.datatypes dt (e1 n) ↔ I2.datatypes dt (e2 n)
      rcases standard with supported | rfl
      · rw [datatype_value h1 supported vn, datatype_value h2 supported vn]
      · exact ⟨fun _ => h2.2.2.2.2.2.2.2.1 _, fun _ => h1.2.2.2.2.2.2.2.1 _⟩
    · rw [cy]
      change dt = literalDatatype ∨ (I2.datatypes dt y ∧ Junk e2 y) ↔ I2.datatypes dt y
      rcases standard with supported | rfl
      · have notLiteral : dt ≠ literalDatatype := fun same => D.excludesLiteral (same ▸ supported)
        simp [notLiteral, junk]
      · exact ⟨fun _ => h2.2.2.2.2.2.2.2.1 _, fun _ => .inl rfl⟩
  | Intersection xs =>
    intro standard y
    rw [Standard] at standard
    obtain ⟨sf, ss, sr⟩ := standard
    have first := right_range vocab h1 h2 xs.first sf y
    have second := right_range vocab h1 h2 xs.second ss y
    have rest : ∀ e ∈ xs.rest.val, (dataDenote (join e1 e2 left I1 I2) e (carry e1 e2 y) ↔ dataDenote I2 e y) :=
      fun e member => right_range vocab h1 h2 e (sr e member) y
    simp only [dataDenote]
    exact and_congr first (and_congr second (forall₂_congr fun e member => rest e member))
  | Union xs =>
    intro standard y
    rw [Standard] at standard
    obtain ⟨sf, ss, sr⟩ := standard
    have first := right_range vocab h1 h2 xs.first sf y
    have second := right_range vocab h1 h2 xs.second ss y
    have rest : ∀ e ∈ xs.rest.val, (dataDenote (join e1 e2 left I1 I2) e (carry e1 e2 y) ↔ dataDenote I2 e y) :=
      fun e member => right_range vocab h1 h2 e (sr e member) y
    simp only [dataDenote]
    exact or_congr first (or_congr second (exists_congr fun e => exists_congr fun member => rest e member))
  | Complement inner =>
    intro standard y
    rw [Standard] at standard
    simp only [dataDenote]
    exact not_congr (right_range vocab h1 h2 inner standard y)
  | OneOf xs =>
    intro standard y
    rw [Standard] at standard
    simp only [dataDenote]
    refine exists_congr fun lt => and_congr_right fun member => ?_
    have value := literal_datatype_value vocab (standard lt member)
    change Sum.inl (I1.literals lt) = carry e1 e2 y ↔ I2.literals lt = y
    rw [h1.2.2.2.2.2.2.2.2.1 lt (standard lt member), h2.2.2.2.2.2.2.2.2.1 lt (standard lt member)]
    exact carry_eq_left value y
  | Restriction dt xs =>
    intro standard y
    rw [Standard] at standard
    obtain ⟨supported, facets⟩ := standard
    simp only [dataDenote]
    rcases carry_cases e1 e2 y with ⟨n, vn, rfl, cy⟩ | ⟨junk, cy⟩
    · rw [cy]
      change I1.datatypes dt (e1 n) ∧ (∀ f ∈ xs.elements, I1.facets f (e1 n)) ↔
        I2.datatypes dt (e2 n) ∧ ∀ f ∈ xs.elements, I2.facets f (e2 n)
      rw [datatype_value h1 supported vn, datatype_value h2 supported vn]
      refine and_congr Iff.rfl (forall₂_congr fun f member => ?_)
      obtain ⟨known, values⟩ := facets f member
      rw [facet_value h1 known values vn, facet_value h2 known values vn]
    · rw [cy]
      change (dt = literalDatatype ∨ (I2.datatypes dt y ∧ Junk e2 y)) ∧ (∀ f ∈ xs.elements, False) ↔
        I2.datatypes dt y ∧ ∀ f ∈ xs.elements, I2.facets f y
      have notLiteral : dt ≠ literalDatatype := fun same => D.excludesLiteral (same ▸ supported)
      have absent : ¬ I2.datatypes dt y := by
        intro has
        obtain ⟨m, space, rfl⟩ := (h2.2.2.2.2.2.2.1 dt supported y).mp has
        exact junk ⟨m, ⟨dt, supported, space⟩, rfl⟩
      simp [notLiteral, absent]
termination_by sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

/-- The first interpretation is the left side of the combination. -/
theorem left_side : Side D V I1 (join e1 e2 left I1 I2) Sum.inl Sum.inl left where
  objects := Sum.inl_injective
  values := Sum.inl_injective
  classes c x := Iff.rfl
  roles p np x y := by
    cases p with
    | Property q =>
      simp only [NotTop] at np
      cases y with
      | inl z => simp [objectRelation, join, np]
      | inr z => simp [objectRelation, join, np]
    | Inverse q =>
      simp only [NotTop] at np
      cases y with
      | inl z => simp [objectRelation, join, np]
      | inr z => simp [objectRelation, join, np]
  data p np x y := by
    simp only [join, np, false_or]
    exact ⟨fun ⟨z, rel, same⟩ => ⟨z, same, rel⟩, fun ⟨z, same, rel⟩ => ⟨z, rel, same⟩⟩
  ranges r _ y := left_range e1 e2 left I1 I2 r y
  literals lt _ := rfl
  individuals a side := by
    cases a with
    | Named a => simp [individual, join, side]
    | Anonymous a => simp [individual, join, side]

/-- The second interpretation is the right side of the combination. -/
theorem right_side (vocab : IsVocabulary D V) (h1 : IsInterpretation D e1 V I1) (h2 : IsInterpretation D e2 V I2) :
    Side D V I2 (join e1 e2 left I1 I2) Sum.inr (carry e1 e2) (fun a => ¬ left a) where
  objects := Sum.inr_injective
  values := carry_injective e1 e2
  classes c x := Iff.rfl
  roles p np x y := by
    cases p with
    | Property q =>
      simp only [NotTop] at np
      cases y with
      | inl z => simp [objectRelation, join, np]
      | inr z => simp [objectRelation, join, np]
    | Inverse q =>
      simp only [NotTop] at np
      cases y with
      | inl z => simp [objectRelation, join, np]
      | inr z => simp [objectRelation, join, np]
  data p np x y := by
    simp only [join, np, false_or]
    exact ⟨fun ⟨z, rel, same⟩ => ⟨z, same, rel⟩, fun ⟨z, same, rel⟩ => ⟨z, rel, same⟩⟩
  ranges r standard y := right_range vocab h1 h2 r standard y
  literals lt known := by
    change Sum.inl (I1.literals lt) = carry e1 e2 (I2.literals lt)
    rw [h1.2.2.2.2.2.2.2.2.1 lt known, h2.2.2.2.2.2.2.2.2.1 lt known]
    exact (carry_eq_left (literal_datatype_value vocab known) _).mpr rfl
  individuals a side := by
    cases a with
    | Named a => simp [individual, join, side]
    | Anonymous a => simp [individual, join, side]

end Sides

/-! ## The axioms the combination satisfies -/

/-- A class expression without individuals, top properties or other than standard data. -/
abbrev Closed (D : DatatypeMap Native) (V : Vocabulary) (c : ClassExpression) : Prop := Plain D V (fun _ => False) c

/-- A role chain or role without the top object property. -/
def SubNotTop : SubObjectPropertyExpression → Prop
  | .Single p => NotTop p
  | .Chain ps => ∀ p ∈ ps.elements, NotTop p

/-- An axiom other than an assertion that a combination of two models of it
    satisfies: it names no individual, uses neither top property, has
    standard data, defines no datatype, and its keys have an object property. -/
def PlainAxiom (D : DatatypeMap Native) (V : Vocabulary) : Axiom → Prop
  | .Declaration _ => True
  | .SubClassOf a b => Closed D V a ∧ Closed D V b
  | .EquivalentClasses xs => ∀ c ∈ xs.elements, Closed D V c
  | .DisjointClasses xs => ∀ c ∈ xs.elements, Closed D V c
  | .DisjointUnion _ xs => ∀ c ∈ xs.elements, Closed D V c
  | .SubObjectPropertyOf s q => SubNotTop s ∧ NotTop q
  | .EquivalentObjectProperties xs => ∀ p ∈ xs.elements, NotTop p
  | .DisjointObjectProperties xs => ∀ p ∈ xs.elements, NotTop p
  | .InverseObjectProperties p q => NotTop p ∧ NotTop q
  | .ObjectPropertyDomain p c => NotTop p ∧ Closed D V c
  | .ObjectPropertyRange p c => NotTop p ∧ Closed D V c
  | .FunctionalObjectProperty p => NotTop p
  | .InverseFunctionalObjectProperty p => NotTop p
  | .ReflexiveObjectProperty p => NotTop p
  | .IrreflexiveObjectProperty p => NotTop p
  | .SymmetricObjectProperty p => NotTop p
  | .AsymmetricObjectProperty p => NotTop p
  | .TransitiveObjectProperty p => NotTop p
  | .SubDataPropertyOf p q => p ≠ topData ∧ q ≠ topData
  | .EquivalentDataProperties xs => ∀ p ∈ xs.elements, p ≠ topData
  | .DisjointDataProperties xs => ∀ p ∈ xs.elements, p ≠ topData
  | .DataPropertyDomain p c => p ≠ topData ∧ Closed D V c
  | .DataPropertyRange p r => p ≠ topData ∧ Standard D V r
  | .FunctionalDataProperty p => p ≠ topData
  | .HasKey c ops dps => Closed D V c ∧ ops.val ≠ [] ∧ (∀ p ∈ ops.val, NotTop p) ∧ ∀ p ∈ dps.val, p ≠ topData
  | .AnnotationAssertion _ _ _ | .SubAnnotationPropertyOf _ _ | .AnnotationPropertyDomain _ _
  | .AnnotationPropertyRange _ _ => True
  | _ => False

/-- An assertion whose class expression uses neither top property, whose data
    are standard and whose literals are in the vocabulary. -/
def PlainAssertion (D : DatatypeMap Native) (V : Vocabulary) : Axiom → Prop
  | .ClassAssertion c _ => Plain D V (fun i => i ∈ classIndividuals c) c
  | .DataPropertyAssertion _ _ lt => V.literals lt
  | .NegativeDataPropertyAssertion _ _ lt => V.literals lt
  | _ => True

theorem plain_mono {D : DatatypeMap Native} {V : Vocabulary} (c : ClassExpression) :
    ∀ {s s' : Individual → Prop}, (∀ a, s a → s' a) → Plain D V s c → Plain D V s' c := by
  cases c with
  | ObjectIntersectionOf xs =>
    intro s s' sub plain
    rw [Plain] at plain ⊢
    obtain ⟨pf, ps, pr⟩ := plain
    exact ⟨plain_mono xs.first sub pf, plain_mono xs.second sub ps, fun e member => plain_mono e sub (pr e member)⟩
  | ObjectUnionOf xs =>
    intro s s' sub plain
    rw [Plain] at plain ⊢
    obtain ⟨pf, ps, pr⟩ := plain
    exact ⟨plain_mono xs.first sub pf, plain_mono xs.second sub ps, fun e member => plain_mono e sub (pr e member)⟩
  | ObjectComplementOf inner =>
    intro s s' sub plain
    rw [Plain] at plain ⊢
    exact plain_mono inner sub plain
  | ObjectOneOf xs =>
    intro s s' sub plain
    rw [Plain] at plain ⊢
    exact fun a member => sub a (plain a member)
  | ObjectSomeValuesFrom p inner =>
    intro s s' sub plain
    rw [Plain] at plain ⊢
    exact ⟨plain.1, plain_mono inner sub plain.2⟩
  | ObjectAllValuesFrom p inner =>
    intro s s' sub plain
    rw [Plain] at plain ⊢
    exact ⟨plain.1, plain_mono inner sub plain.2⟩
  | ObjectHasValue p a =>
    intro s s' sub plain
    rw [Plain] at plain ⊢
    exact ⟨plain.1, sub a plain.2⟩
  | ObjectMinCardinality n p filler =>
    intro s s' sub plain
    cases h : filler with
    | none => rw [h] at plain; rw [Plain] at plain ⊢; exact plain
    | some c =>
      have : sizeOf c < sizeOf filler := by rw [h]; simp +arith
      rw [h] at plain; rw [Plain] at plain ⊢
      exact ⟨plain.1, plain_mono c sub plain.2⟩
  | ObjectMaxCardinality n p filler =>
    intro s s' sub plain
    cases h : filler with
    | none => rw [h] at plain; rw [Plain] at plain ⊢; exact plain
    | some c =>
      have : sizeOf c < sizeOf filler := by rw [h]; simp +arith
      rw [h] at plain; rw [Plain] at plain ⊢
      exact ⟨plain.1, plain_mono c sub plain.2⟩
  | ObjectExactCardinality n p filler =>
    intro s s' sub plain
    cases h : filler with
    | none => rw [h] at plain; rw [Plain] at plain ⊢; exact plain
    | some c =>
      have : sizeOf c < sizeOf filler := by rw [h]; simp +arith
      rw [h] at plain; rw [Plain] at plain ⊢
      exact ⟨plain.1, plain_mono c sub plain.2⟩
  | DataMinCardinality _ _ filler | DataMaxCardinality _ _ filler | DataExactCardinality _ _ filler =>
    intro s s' _ plain
    cases filler <;> (rw [Plain] at plain ⊢) <;> exact plain
  | Class _ | ObjectHasSelf _ | DataSomeValuesFrom _ _ | DataAllValuesFrom _ _ | DataHasValue _ _ =>
    intro s s' _ plain
    rw [Plain] at plain ⊢
    exact plain
termination_by sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

section Axioms
variable {D : DatatypeMap Native} {V : Vocabulary} {O1 O2 : Type u} {V1 V2 : Type v}
  {e1 : ValueEmbedding D V1} {e2 : ValueEmbedding D V2} {left : Individual → Prop}
  {I1 : Interpretation O1 V1} {I2 : Interpretation O2 V2}

private theorem cross_left {p : ObjectPropertyExpression} (np : NotTop p) (x : O1) (y : O2) :
    ¬ objectRelation (join e1 e2 left I1 I2) p (.inl x) (.inr y) := by
  cases p with
  | Property q =>
    simp only [NotTop] at np
    simp [objectRelation, join, np]
  | Inverse q =>
    simp only [NotTop] at np
    simp [objectRelation, join, np]

private theorem cross_right {p : ObjectPropertyExpression} (np : NotTop p) (x : O2) (y : O1) :
    ¬ objectRelation (join e1 e2 left I1 I2) p (.inr x) (.inl y) := by
  cases p with
  | Property q =>
    simp only [NotTop] at np
    simp [objectRelation, join, np]
  | Inverse q =>
    simp only [NotTop] at np
    simp [objectRelation, join, np]

private theorem rel_left {p : ObjectPropertyExpression} (np : NotTop p) (x y : O1) :
    objectRelation (join e1 e2 left I1 I2) p (.inl x) (.inl y) ↔ objectRelation I1 p x y := by
  cases p with
  | Property q =>
    simp only [NotTop] at np
    simp [objectRelation, join, np]
  | Inverse q =>
    simp only [NotTop] at np
    simp [objectRelation, join, np]

private theorem rel_right {p : ObjectPropertyExpression} (np : NotTop p) (x y : O2) :
    objectRelation (join e1 e2 left I1 I2) p (.inr x) (.inr y) ↔ objectRelation I2 p x y := by
  cases p with
  | Property q =>
    simp only [NotTop] at np
    simp [objectRelation, join, np]
  | Inverse q =>
    simp only [NotTop] at np
    simp [objectRelation, join, np]

private theorem chain_left (ps : List ObjectPropertyExpression) (np : ∀ p ∈ ps, NotTop p) (x : O1) (z : O1 ⊕ O2) :
    chainRelation (join e1 e2 left I1 I2) ps (.inl x) z ↔ ∃ y, z = .inl y ∧ chainRelation I1 ps x y := by
  induction ps generalizing x with
  | nil =>
    simp only [chainRelation]
    constructor
    · rintro rfl; exact ⟨x, rfl, rfl⟩
    · rintro ⟨y, rfl, rfl⟩; rfl
  | cons p ps ih =>
    simp only [chainRelation]
    have npp := np p (by simp)
    have nps : ∀ q ∈ ps, NotTop q := fun q m => np q (by simp [m])
    constructor
    · rintro ⟨m, rel, rest⟩
      rcases m with m | m
      · obtain ⟨y, rfl, chain⟩ := (ih nps m).mp rest
        exact ⟨y, rfl, m, (rel_left npp x m).mp rel, chain⟩
      · exact absurd rel (cross_left npp x m)
    · rintro ⟨y, rfl, m, rel, chain⟩
      exact ⟨.inl m, (rel_left npp x m).mpr rel, (ih nps m).mpr ⟨y, rfl, chain⟩⟩

private theorem chain_right (ps : List ObjectPropertyExpression) (np : ∀ p ∈ ps, NotTop p) (x : O2) (z : O1 ⊕ O2) :
    chainRelation (join e1 e2 left I1 I2) ps (.inr x) z ↔ ∃ y, z = .inr y ∧ chainRelation I2 ps x y := by
  induction ps generalizing x with
  | nil =>
    simp only [chainRelation]
    constructor
    · rintro rfl; exact ⟨x, rfl, rfl⟩
    · rintro ⟨y, rfl, rfl⟩; rfl
  | cons p ps ih =>
    simp only [chainRelation]
    have npp := np p (by simp)
    have nps : ∀ q ∈ ps, NotTop q := fun q m => np q (by simp [m])
    constructor
    · rintro ⟨m, rel, rest⟩
      rcases m with m | m
      · exact absurd rel (cross_right npp x m)
      · obtain ⟨y, rfl, chain⟩ := (ih nps m).mp rest
        exact ⟨y, rfl, m, (rel_right npp x m).mp rel, chain⟩
    · rintro ⟨y, rfl, m, rel, chain⟩
      exact ⟨.inr m, (rel_right npp x m).mpr rel, (ih nps m).mpr ⟨y, rfl, chain⟩⟩

private theorem data_left {p : DataProperty} (np : p ≠ topData) (x : O1) (v : V1 ⊕ V2) :
    (join e1 e2 left I1 I2).dataProperties p (.inl x) v ↔ ∃ z, Sum.inl z = v ∧ I1.dataProperties p x z := by
  simp only [join, np, false_or]
  exact ⟨fun ⟨z, rel, same⟩ => ⟨z, same, rel⟩, fun ⟨z, same, rel⟩ => ⟨z, rel, same⟩⟩

private theorem closed_left {c : ClassExpression} (closed : Closed D V c) (x : O1) :
    classDenote (join e1 e2 left I1 I2) c (.inl x) ↔ classDenote I1 c x :=
  side_class (left_side (V := V) (e1 := e1) (e2 := e2) (left := left) (I1 := I1) (I2 := I2)) c
    (plain_mono c (fun _ h => h.elim) closed) x

private theorem data_right {p : DataProperty} (np : p ≠ topData) (x : O2) (v : V1 ⊕ V2) :
    (join e1 e2 left I1 I2).dataProperties p (.inr x) v ↔ ∃ z, carry e1 e2 z = v ∧ I2.dataProperties p x z := by
  simp only [join, np, false_or]
  exact ⟨fun ⟨z, rel, same⟩ => ⟨z, same, rel⟩, fun ⟨z, same, rel⟩ => ⟨z, rel, same⟩⟩

variable (vocab : IsVocabulary D V) (h1 : IsInterpretation D e1 V I1) (h2 : IsInterpretation D e2 V I2)
include vocab h1 h2

private theorem closed_right {c : ClassExpression} (closed : Closed D V c) (x : O2) :
    classDenote (join e1 e2 left I1 I2) c (.inr x) ↔ classDenote I2 c x :=
  side_class (right_side vocab h1 h2) c (plain_mono c (fun _ h => h.elim) closed) x

/-- The combination satisfies every plain axiom that both interpretations satisfy. -/
theorem join_plain (ax : Axiom) (plain : PlainAxiom D V ax) (s1 : satisfies I1 ax) (s2 : satisfies I2 ax) :
    satisfies (join e1 e2 left I1 I2) ax := by
  have R := right_side (left := left) vocab h1 h2
  cases ax with
  | Declaration _ => trivial
  | SubClassOf a b =>
    simp only [PlainAxiom] at plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) h
    · exact (closed_left plain.2 x).mpr (s1 x ((closed_left plain.1 x).mp h))
    · exact (closed_right vocab h1 h2 plain.2 x).mpr (s2 x ((closed_right vocab h1 h2 plain.1 x).mp h))
  | EquivalentClasses xs =>
    simp only [PlainAxiom] at plain
    simp only [satisfies, allEqual] at s1 s2 ⊢
    intro a ma b mb
    funext x
    apply propext
    rcases x with x | x
    · rw [closed_left (plain a ma), closed_left (plain b mb), s1 a ma b mb]
    · rw [closed_right vocab h1 h2 (plain a ma), closed_right vocab h1 h2 (plain b mb), s2 a ma b mb]
  | DisjointClasses xs =>
    simp only [PlainAxiom] at plain
    simp only [satisfies, pairwiseDisjoint] at s1 s2 ⊢
    refine (s1.and s2).imp_of_mem fun {a b} ma mb ⟨d1, d2⟩ x => ?_
    rcases x with x | x
    · rw [closed_left (plain a ma), closed_left (plain b mb)]
      exact d1 x
    · rw [closed_right vocab h1 h2 (plain a ma), closed_right vocab h1 h2 (plain b mb)]
      exact d2 x
  | DisjointUnion c xs =>
    simp only [PlainAxiom] at plain
    simp only [satisfies, pairwiseDisjoint] at s1 s2 ⊢
    refine ⟨?_, (s1.2.and s2.2).imp_of_mem fun {a b} ma mb ⟨d1, d2⟩ x => ?_⟩
    · rintro (x | x)
      · change I1.classes c x ↔ _
        rw [s1.1 x]
        exact exists_congr fun e => and_congr_right fun me => (closed_left (plain e me) x).symm
      · change I2.classes c x ↔ _
        rw [s2.1 x]
        exact exists_congr fun e => and_congr_right fun me => (closed_right vocab h1 h2 (plain e me) x).symm
    · rcases x with x | x
      · rw [closed_left (plain a ma), closed_left (plain b mb)]
        exact d1 x
      · rw [closed_right vocab h1 h2 (plain a ma), closed_right vocab h1 h2 (plain b mb)]
        exact d2 x
  | SubObjectPropertyOf sub q =>
    simp only [PlainAxiom] at plain
    obtain ⟨nsub, nq⟩ := plain
    simp only [satisfies] at s1 s2 ⊢
    cases sub with
    | Single p =>
      simp only [SubNotTop] at nsub
      simp only [subRelation] at s1 s2 ⊢
      rintro (x | x) (y | y) rel
      · exact (rel_left nq x y).mpr (s1 x y ((rel_left nsub x y).mp rel))
      · exact absurd rel (cross_left nsub x y)
      · exact absurd rel (cross_right nsub x y)
      · exact (rel_right nq x y).mpr (s2 x y ((rel_right nsub x y).mp rel))
    | Chain ps =>
      simp only [SubNotTop] at nsub
      simp only [subRelation] at s1 s2 ⊢
      rintro (x | x) z chain
      · obtain ⟨y, rfl, chain'⟩ := (chain_left _ nsub x z).mp chain
        exact (rel_left nq x y).mpr (s1 x y chain')
      · obtain ⟨y, rfl, chain'⟩ := (chain_right _ nsub x z).mp chain
        exact (rel_right nq x y).mpr (s2 x y chain')
  | EquivalentObjectProperties xs =>
    simp only [PlainAxiom] at plain
    simp only [satisfies, allEqual] at s1 s2 ⊢
    intro p mp q mq
    funext x y
    apply propext
    rcases x with x | x <;> rcases y with y | y
    · rw [rel_left (plain p mp), rel_left (plain q mq), s1 p mp q mq]
    · exact ⟨fun h => absurd h (cross_left (plain p mp) x y), fun h => absurd h (cross_left (plain q mq) x y)⟩
    · exact ⟨fun h => absurd h (cross_right (plain p mp) x y), fun h => absurd h (cross_right (plain q mq) x y)⟩
    · rw [rel_right (plain p mp), rel_right (plain q mq), s2 p mp q mq]
  | DisjointObjectProperties xs =>
    simp only [PlainAxiom] at plain
    simp only [satisfies, pairwiseDisjoint] at s1 s2 ⊢
    refine (s1.and s2).imp_of_mem fun {p q} mp mq ⟨d1, d2⟩ => ?_
    rintro ⟨x, y⟩ ⟨hp, hq⟩
    rcases x with x | x <;> rcases y with y | y
    · exact d1 (x, y) ⟨(rel_left (plain p mp) x y).mp hp, (rel_left (plain q mq) x y).mp hq⟩
    · exact cross_left (plain p mp) x y hp
    · exact cross_right (plain p mp) x y hp
    · exact d2 (x, y) ⟨(rel_right (plain p mp) x y).mp hp, (rel_right (plain q mq) x y).mp hq⟩
  | InverseObjectProperties p q =>
    simp only [PlainAxiom] at plain
    obtain ⟨np, nq⟩ := plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) (y | y)
    · rw [rel_left np, rel_left nq]; exact s1 x y
    · exact ⟨fun h => absurd h (cross_left np x y), fun h => absurd h (cross_right nq y x)⟩
    · exact ⟨fun h => absurd h (cross_right np x y), fun h => absurd h (cross_left nq y x)⟩
    · rw [rel_right np, rel_right nq]; exact s2 x y
  | ObjectPropertyDomain p c =>
    simp only [PlainAxiom] at plain
    obtain ⟨np, cc⟩ := plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) (y | y) rel
    · exact (closed_left cc x).mpr (s1 x y ((rel_left np x y).mp rel))
    · exact absurd rel (cross_left np x y)
    · exact absurd rel (cross_right np x y)
    · exact (closed_right vocab h1 h2 cc x).mpr (s2 x y ((rel_right np x y).mp rel))
  | ObjectPropertyRange p c =>
    simp only [PlainAxiom] at plain
    obtain ⟨np, cc⟩ := plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) (y | y) rel
    · exact (closed_left cc y).mpr (s1 x y ((rel_left np x y).mp rel))
    · exact absurd rel (cross_left np x y)
    · exact absurd rel (cross_right np x y)
    · exact (closed_right vocab h1 h2 cc y).mpr (s2 x y ((rel_right np x y).mp rel))
  | FunctionalObjectProperty p =>
    simp only [PlainAxiom] at plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) (y | y) (z | z) ry rz
    · rw [s1 x y z ((rel_left plain x y).mp ry) ((rel_left plain x z).mp rz)]
    · exact absurd rz (cross_left plain x z)
    · exact absurd ry (cross_left plain x y)
    · exact absurd ry (cross_left plain x y)
    · exact absurd ry (cross_right plain x y)
    · exact absurd ry (cross_right plain x y)
    · exact absurd rz (cross_right plain x z)
    · rw [s2 x y z ((rel_right plain x y).mp ry) ((rel_right plain x z).mp rz)]
  | InverseFunctionalObjectProperty p =>
    simp only [PlainAxiom] at plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) (y | y) (z | z) rx ry
    · rw [s1 x y z ((rel_left plain x z).mp rx) ((rel_left plain y z).mp ry)]
    · exact absurd rx (cross_left plain x z)
    · exact absurd ry (cross_right plain y z)
    · exact absurd rx (cross_left plain x z)
    · exact absurd rx (cross_right plain x z)
    · exact absurd ry (cross_left plain y z)
    · exact absurd ry (cross_right plain y z)
    · rw [s2 x y z ((rel_right plain x z).mp rx) ((rel_right plain y z).mp ry)]
  | ReflexiveObjectProperty p =>
    simp only [PlainAxiom] at plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x)
    · exact (rel_left plain x x).mpr (s1 x)
    · exact (rel_right plain x x).mpr (s2 x)
  | IrreflexiveObjectProperty p =>
    simp only [PlainAxiom] at plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) rel
    · exact s1 x ((rel_left plain x x).mp rel)
    · exact s2 x ((rel_right plain x x).mp rel)
  | SymmetricObjectProperty p =>
    simp only [PlainAxiom] at plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) (y | y) rel
    · exact (rel_left plain y x).mpr (s1 x y ((rel_left plain x y).mp rel))
    · exact absurd rel (cross_left plain x y)
    · exact absurd rel (cross_right plain x y)
    · exact (rel_right plain y x).mpr (s2 x y ((rel_right plain x y).mp rel))
  | AsymmetricObjectProperty p =>
    simp only [PlainAxiom] at plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) (y | y) rel back
    · exact s1 x y ((rel_left plain x y).mp rel) ((rel_left plain y x).mp back)
    · exact cross_left plain x y rel
    · exact cross_right plain x y rel
    · exact s2 x y ((rel_right plain x y).mp rel) ((rel_right plain y x).mp back)
  | TransitiveObjectProperty p =>
    simp only [PlainAxiom] at plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) (y | y) (z | z) rxy ryz
    · exact (rel_left plain x z).mpr (s1 x y z ((rel_left plain x y).mp rxy) ((rel_left plain y z).mp ryz))
    · exact absurd ryz (cross_left plain y z)
    · exact absurd rxy (cross_left plain x y)
    · exact absurd rxy (cross_left plain x y)
    · exact absurd rxy (cross_right plain x y)
    · exact absurd rxy (cross_right plain x y)
    · exact absurd ryz (cross_right plain y z)
    · exact (rel_right plain x z).mpr (s2 x y z ((rel_right plain x y).mp rxy) ((rel_right plain y z).mp ryz))
  | SubDataPropertyOf p q =>
    simp only [PlainAxiom] at plain
    obtain ⟨np, nq⟩ := plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) v h
    · obtain ⟨z, rfl, h'⟩ := (data_left np x v).mp h
      exact (data_left nq x _).mpr ⟨z, rfl, s1 x z h'⟩
    · obtain ⟨z, rfl, h'⟩ := (data_right np x v).mp h
      exact (data_right nq x _).mpr ⟨z, rfl, s2 x z h'⟩
  | EquivalentDataProperties xs =>
    simp only [PlainAxiom] at plain
    simp only [satisfies, allEqual] at s1 s2 ⊢
    intro p mp q mq
    funext x v
    apply propext
    rcases x with x | x
    · rw [data_left (plain p mp), data_left (plain q mq), s1 p mp q mq]
    · rw [data_right (plain p mp), data_right (plain q mq), s2 p mp q mq]
  | DisjointDataProperties xs =>
    simp only [PlainAxiom] at plain
    simp only [satisfies, pairwiseDisjoint] at s1 s2 ⊢
    refine (s1.and s2).imp_of_mem fun {p q} mp mq ⟨d1, d2⟩ => ?_
    rintro ⟨x, v⟩ ⟨hp, hq⟩
    rcases x with x | x
    · obtain ⟨z, rfl, hp'⟩ := (data_left (plain p mp) x v).mp hp
      obtain ⟨z', same, hq'⟩ := (data_left (plain q mq) x _).mp hq
      cases same
      exact d1 (x, z) ⟨hp', hq'⟩
    · obtain ⟨z, rfl, hp'⟩ := (data_right (plain p mp) x v).mp hp
      obtain ⟨z', same, hq'⟩ := (data_right (plain q mq) x _).mp hq
      rw [R.values same] at hq'
      exact d2 (x, z) ⟨hp', hq'⟩
  | DataPropertyDomain p c =>
    simp only [PlainAxiom] at plain
    obtain ⟨np, cc⟩ := plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) v h
    · obtain ⟨z, rfl, h'⟩ := (data_left np x v).mp h
      exact (closed_left cc x).mpr (s1 x z h')
    · obtain ⟨z, rfl, h'⟩ := (data_right np x v).mp h
      exact (closed_right vocab h1 h2 cc x).mpr (s2 x z h')
  | DataPropertyRange p r =>
    simp only [PlainAxiom] at plain
    obtain ⟨np, sr⟩ := plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) v h
    · obtain ⟨z, rfl, h'⟩ := (data_left np x v).mp h
      exact ((left_side (V := V) (e1 := e1) (e2 := e2) (left := left) (I1 := I1) (I2 := I2)).ranges r sr z).mpr (s1 x z h')
    · obtain ⟨z, rfl, h'⟩ := (data_right np x v).mp h
      exact (R.ranges r sr z).mpr (s2 x z h')
  | FunctionalDataProperty p =>
    simp only [PlainAxiom] at plain
    simp only [satisfies] at s1 s2 ⊢
    rintro (x | x) v v' h h'
    · obtain ⟨z, rfl, hz⟩ := (data_left plain x v).mp h
      obtain ⟨z', rfl, hz'⟩ := (data_left plain x v').mp h'
      rw [s1 x z z' hz hz']
    · obtain ⟨z, rfl, hz⟩ := (data_right plain x v).mp h
      obtain ⟨z', rfl, hz'⟩ := (data_right plain x v').mp h'
      rw [s2 x z z' hz hz']
  | HasKey c ops dps =>
    simp only [PlainAxiom] at plain
    obtain ⟨cc, nonempty, nops, ndps⟩ := plain
    simp only [satisfies] at s1 s2 ⊢
    obtain ⟨p0, m0⟩ : ∃ p, p ∈ ops.val := List.exists_mem_of_ne_nil _ nonempty
    rintro (x | x) (y | y) cx nx cy ny keysO keysD
    · congr 1
      refine s1 x y ((closed_left cc x).mp cx) nx ((closed_left cc y).mp cy) ny ?_ ?_
      · intro p mp
        obtain ⟨z, nz, rx, ry⟩ := keysO p mp
        rcases z with z | z
        · exact ⟨z, nz, (rel_left (nops p mp) x z).mp rx, (rel_left (nops p mp) y z).mp ry⟩
        · exact absurd rx (cross_left (nops p mp) x z)
      · intro p mp
        obtain ⟨v, vx, vy⟩ := keysD p mp
        obtain ⟨z, rfl, zx⟩ := (data_left (ndps p mp) x v).mp vx
        obtain ⟨z', same, zy⟩ := (data_left (ndps p mp) y _).mp vy
        cases same
        exact ⟨z, zx, zy⟩
    · obtain ⟨z, _, rx, ry⟩ := keysO p0 m0
      rcases z with z | z
      · exact absurd ry (cross_right (nops p0 m0) y z)
      · exact absurd rx (cross_left (nops p0 m0) x z)
    · obtain ⟨z, _, rx, ry⟩ := keysO p0 m0
      rcases z with z | z
      · exact absurd rx (cross_right (nops p0 m0) x z)
      · exact absurd ry (cross_left (nops p0 m0) y z)
    · congr 1
      refine s2 x y ((closed_right vocab h1 h2 cc x).mp cx) nx ((closed_right vocab h1 h2 cc y).mp cy) ny ?_ ?_
      · intro p mp
        obtain ⟨z, nz, rx, ry⟩ := keysO p mp
        rcases z with z | z
        · exact absurd rx (cross_right (nops p mp) x z)
        · exact ⟨z, nz, (rel_right (nops p mp) x z).mp rx, (rel_right (nops p mp) y z).mp ry⟩
      · intro p mp
        obtain ⟨v, vx, vy⟩ := keysD p mp
        obtain ⟨z, rfl, zx⟩ := (data_right (ndps p mp) x v).mp vx
        obtain ⟨z', same, zy⟩ := (data_right (ndps p mp) y _).mp vy
        rw [R.values same] at zy
        exact ⟨z, zx, zy⟩
  | AnnotationAssertion _ _ _ | SubAnnotationPropertyOf _ _ | AnnotationPropertyDomain _ _
  | AnnotationPropertyRange _ _ => trivial
  | DatatypeDefinition _ _ | SameIndividual _ | DifferentIndividuals _ | ClassAssertion _ _
  | ObjectPropertyAssertion _ _ _ | NegativeObjectPropertyAssertion _ _ _ | DataPropertyAssertion _ _ _
  | NegativeDataPropertyAssertion _ _ _ =>
    simp only [PlainAxiom] at plain

end Axioms

section Assertions
variable {D : DatatypeMap Native} {V : Vocabulary} {O1 O2 : Type u} {V1 V2 : Type v}
  {e1 : ValueEmbedding D V1} {e2 : ValueEmbedding D V2} {left : Individual → Prop}
  {I1 : Interpretation O1 V1} {I2 : Interpretation O2 V2}

private theorem rel_left_any (h1 : IsInterpretation D e1 V I1) (p : ObjectPropertyExpression) (x y : O1) :
    objectRelation (join e1 e2 left I1 I2) p (.inl x) (.inl y) ↔ objectRelation I1 p x y := by
  cases p with
  | Property q =>
    by_cases top : q = topObject
    · subst top
      simp only [objectRelation, join, true_or, true_iff]
      exact h1.2.2.1 x y
    · simp [objectRelation, join, top]
  | Inverse q =>
    by_cases top : q = topObject
    · subst top
      simp only [objectRelation, join, true_or, true_iff]
      exact h1.2.2.1 y x
    · simp [objectRelation, join, top]

private theorem rel_right_any (h2 : IsInterpretation D e2 V I2) (p : ObjectPropertyExpression) (x y : O2) :
    objectRelation (join e1 e2 left I1 I2) p (.inr x) (.inr y) ↔ objectRelation I2 p x y := by
  cases p with
  | Property q =>
    by_cases top : q = topObject
    · subst top
      simp only [objectRelation, join, true_or, true_iff]
      exact h2.2.2.1 x y
    · simp [objectRelation, join, top]
  | Inverse q =>
    by_cases top : q = topObject
    · subst top
      simp only [objectRelation, join, true_or, true_iff]
      exact h2.2.2.1 y x
    · simp [objectRelation, join, top]

private theorem data_left_any (h1 : IsInterpretation D e1 V I1) (p : DataProperty) (x : O1) (z : V1) :
    (join e1 e2 left I1 I2).dataProperties p (.inl x) (.inl z) ↔ I1.dataProperties p x z := by
  by_cases top : p = topData
  · subst top
    simp only [join, true_or, true_iff]
    exact h1.2.2.2.2.1 x z
  · rw [data_left top]
    exact ⟨fun ⟨z', same, rel⟩ => Sum.inl.inj same ▸ rel, fun rel => ⟨z, rfl, rel⟩⟩

private theorem data_right_any (h2 : IsInterpretation D e2 V I2) (p : DataProperty) (x : O2) (z : V2) :
    (join e1 e2 left I1 I2).dataProperties p (.inr x) (carry e1 e2 z) ↔ I2.dataProperties p x z := by
  by_cases top : p = topData
  · subst top
    simp only [join, true_or, true_iff]
    exact h2.2.2.2.2.1 x z
  · rw [data_right top]
    exact ⟨fun ⟨z', same, rel⟩ => carry_injective e1 e2 same ▸ rel, fun rel => ⟨z, rfl, rel⟩⟩

private theorem individual_left {i : Individual} (side : left i) :
    individual (join e1 e2 left I1 I2) i = .inl (individual I1 i) := by
  cases i with
  | Named a => simp [individual, join, side]
  | Anonymous a => simp [individual, join, side]

private theorem individual_right {i : Individual} (side : ¬ left i) :
    individual (join e1 e2 left I1 I2) i = .inr (individual I2 i) := by
  cases i with
  | Named a => simp [individual, join, side]
  | Anonymous a => simp [individual, join, side]

/-- The combination satisfies the assertions of the first interpretation about
    individuals on the left. -/
theorem join_left_assertion (h1 : IsInterpretation D e1 V I1) (ax : Axiom) (assertion : IsAssertion ax)
    (onLeft : ∀ i ∈ axiomIndividuals ax, left i) (plain : PlainAssertion D V ax) (s1 : satisfies I1 ax) :
    satisfies (join e1 e2 left I1 I2) ax := by
  cases ax with
  | ClassAssertion c a =>
    simp only [PlainAssertion] at plain
    simp only [axiomIndividuals, List.mem_cons] at onLeft
    simp only [satisfies] at s1 ⊢
    rw [individual_left (onLeft a (.inl rfl))]
    exact (side_class (left_side (V := V) (e1 := e1) (e2 := e2) (left := left) (I1 := I1) (I2 := I2)) c
      (plain_mono c (fun i mi => onLeft i (.inr mi)) plain) _).mpr s1
  | ObjectPropertyAssertion p a b =>
    simp only [axiomIndividuals, List.mem_cons, List.mem_nil_iff, or_false] at onLeft
    simp only [satisfies] at s1 ⊢
    rw [individual_left (onLeft a (.inl rfl)), individual_left (onLeft b (.inr rfl)), rel_left_any h1]
    exact s1
  | NegativeObjectPropertyAssertion p a b =>
    simp only [axiomIndividuals, List.mem_cons, List.mem_nil_iff, or_false] at onLeft
    simp only [satisfies] at s1 ⊢
    rw [individual_left (onLeft a (.inl rfl)), individual_left (onLeft b (.inr rfl)), rel_left_any h1]
    exact s1
  | DataPropertyAssertion p a lt =>
    simp only [axiomIndividuals, List.mem_cons, List.mem_nil_iff, or_false] at onLeft
    simp only [satisfies] at s1 ⊢
    rw [individual_left (onLeft a rfl)]
    exact (data_left_any h1 p _ _).mpr s1
  | NegativeDataPropertyAssertion p a lt =>
    simp only [axiomIndividuals, List.mem_cons, List.mem_nil_iff, or_false] at onLeft
    simp only [satisfies] at s1 ⊢
    rw [individual_left (onLeft a rfl)]
    exact fun h => s1 ((data_left_any h1 p _ _).mp h)
  | SameIndividual xs =>
    simp only [axiomIndividuals] at onLeft
    simp only [satisfies, allEqual] at s1 ⊢
    intro a ma b mb
    rw [individual_left (onLeft a ma), individual_left (onLeft b mb), s1 a ma b mb]
  | DifferentIndividuals xs =>
    simp only [axiomIndividuals] at onLeft
    simp only [satisfies] at s1 ⊢
    refine s1.imp_of_mem fun {a b} ma mb differ same => differ ?_
    rw [individual_left (onLeft a ma), individual_left (onLeft b mb)] at same
    exact Sum.inl.inj same
  | _ => simp only [IsAssertion] at assertion

/-- The combination satisfies the assertions of the second interpretation about
    individuals on the right. -/
theorem join_right_assertion (vocab : IsVocabulary D V) (h1 : IsInterpretation D e1 V I1)
    (h2 : IsInterpretation D e2 V I2) (ax : Axiom) (assertion : IsAssertion ax)
    (onRight : ∀ i ∈ axiomIndividuals ax, ¬ left i) (plain : PlainAssertion D V ax) (s2 : satisfies I2 ax) :
    satisfies (join e1 e2 left I1 I2) ax := by
  have R := right_side (left := left) vocab h1 h2
  cases ax with
  | ClassAssertion c a =>
    simp only [PlainAssertion] at plain
    simp only [axiomIndividuals, List.mem_cons] at onRight
    simp only [satisfies] at s2 ⊢
    rw [individual_right (onRight a (.inl rfl))]
    exact (side_class R c (plain_mono c (fun i mi => onRight i (.inr mi)) plain) _).mpr s2
  | ObjectPropertyAssertion p a b =>
    simp only [axiomIndividuals, List.mem_cons, List.mem_nil_iff, or_false] at onRight
    simp only [satisfies] at s2 ⊢
    rw [individual_right (onRight a (.inl rfl)), individual_right (onRight b (.inr rfl)), rel_right_any h2]
    exact s2
  | NegativeObjectPropertyAssertion p a b =>
    simp only [axiomIndividuals, List.mem_cons, List.mem_nil_iff, or_false] at onRight
    simp only [satisfies] at s2 ⊢
    rw [individual_right (onRight a (.inl rfl)), individual_right (onRight b (.inr rfl)), rel_right_any h2]
    exact s2
  | DataPropertyAssertion p a lt =>
    simp only [PlainAssertion] at plain
    simp only [axiomIndividuals, List.mem_cons, List.mem_nil_iff, or_false] at onRight
    simp only [satisfies] at s2 ⊢
    rw [individual_right (onRight a rfl), R.literals lt plain]
    exact (data_right_any h2 p _ _).mpr s2
  | NegativeDataPropertyAssertion p a lt =>
    simp only [PlainAssertion] at plain
    simp only [axiomIndividuals, List.mem_cons, List.mem_nil_iff, or_false] at onRight
    simp only [satisfies] at s2 ⊢
    rw [individual_right (onRight a rfl), R.literals lt plain]
    exact fun h => s2 ((data_right_any h2 p _ _).mp h)
  | SameIndividual xs =>
    simp only [axiomIndividuals] at onRight
    simp only [satisfies, allEqual] at s2 ⊢
    intro a ma b mb
    rw [individual_right (onRight a ma), individual_right (onRight b mb), s2 a ma b mb]
  | DifferentIndividuals xs =>
    simp only [axiomIndividuals] at onRight
    simp only [satisfies] at s2 ⊢
    refine s2.imp_of_mem fun {a b} ma mb differ same => differ ?_
    rw [individual_right (onRight a ma), individual_right (onRight b mb)] at same
    exact Sum.inr.inj same
  | _ => simp only [IsAssertion] at assertion

end Assertions

/-! ## Instance questions about one part -/

section Main
variable {D : DatatypeMap Native} {V : Vocabulary} {O : Type u} {W : Type v}

private theorem anonymous_range (I : Interpretation O W) (asg : AnonymousIndividual → O) (r : DataRange) :
    ∀ y, dataDenote (withAnonymous I asg) r y ↔ dataDenote I r y := by
  cases r with
  | Datatype dt => intro y; simp only [dataDenote]; rfl
  | Intersection xs =>
    intro y
    have first := anonymous_range I asg xs.first y
    have second := anonymous_range I asg xs.second y
    have rest : ∀ e ∈ xs.rest.val, (dataDenote (withAnonymous I asg) e y ↔ dataDenote I e y) :=
      fun e _ => anonymous_range I asg e y
    simp only [dataDenote]
    exact and_congr first (and_congr second (forall₂_congr fun e member => rest e member))
  | Union xs =>
    intro y
    have first := anonymous_range I asg xs.first y
    have second := anonymous_range I asg xs.second y
    have rest : ∀ e ∈ xs.rest.val, (dataDenote (withAnonymous I asg) e y ↔ dataDenote I e y) :=
      fun e _ => anonymous_range I asg e y
    simp only [dataDenote]
    exact or_congr first (or_congr second (exists_congr fun e => exists_congr fun member => rest e member))
  | Complement inner =>
    intro y
    simp only [dataDenote]
    exact not_congr (anonymous_range I asg inner y)
  | OneOf xs => intro y; simp only [dataDenote]; rfl
  | Restriction dt xs => intro y; simp only [dataDenote]; rfl
termination_by sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

/-- Reassigning the anonymous individuals changes nothing else. -/
private theorem anonymous_side (I : Interpretation O W) (asg : AnonymousIndividual → O) :
    Side D V I (withAnonymous I asg) id id (fun _ => False) where
  objects := Function.injective_id
  values := Function.injective_id
  classes _ _ := Iff.rfl
  roles p _ x y := by
    cases p <;> exact ⟨fun h => ⟨y, rfl, h⟩, fun ⟨z, same, h⟩ => same ▸ h⟩
  data _ _ x y := ⟨fun h => ⟨y, rfl, h⟩, fun ⟨z, same, h⟩ => same ▸ h⟩
  ranges r _ y := anonymous_range I asg r y
  literals _ _ := rfl
  individuals _ no := no.elim

private theorem with_self (I : Interpretation O W) : withAnonymous I I.anonymousIndividuals = I := by
  cases I; rfl

/-- A model of a closure is a model of a part whose axioms are axioms of the closure. -/
private theorem model_part {Native : Type w} {D : DatatypeMap Native} {V : Vocabulary} {O : Type u} {W : Type v}
    {emb : ValueEmbedding D W} {I : Interpretation O W} {items part : List AnnotatedAxiom}
    (inside : ∀ y ∈ part, ∃ x ∈ items, x.axiom = y.axiom) (model : Model D emb V I items) : Model D emb V I part := by
  obtain ⟨vocab', h, asg, sat⟩ := model
  refine ⟨vocab', h, asg, fun y member => ?_⟩
  obtain ⟨x, mx, same⟩ := inside y member
  rw [← same]
  exact sat x mx

/-- When the axioms other than assertions are plain and a closure's assertions
    fall into a part and a rest that share no individual, a model of the part
    and a model of the rest and of the meaningful axioms other than assertions
    combine into a model of the closure, with the model of the part on the
    left. The part may hold copies of the closure's axioms, and the rest may
    also hold axioms without meaning. -/
theorem join_model (vocab : IsVocabulary D V) {items part rest : List AnnotatedAxiom}
    (cover : ∀ x ∈ items, (∃ y ∈ part, y.axiom = x.axiom) ∨ x ∈ rest)
    (plain : ∀ x ∈ items, ¬ IsAssertion x.axiom → PlainAxiom D V x.axiom)
    (asserted : ∀ x ∈ items, IsAssertion x.axiom → PlainAssertion D V x.axiom)
    (restKinds : ∀ x ∈ rest, IsAssertion x.axiom ∨ Meaningless x.axiom)
    (apart : ∀ x ∈ part, IsAssertion x.axiom → ∀ y ∈ rest, ∀ i ∈ axiomIndividuals x.axiom,
      i ∉ axiomIndividuals y.axiom)
    {O1 O2 : Type u} {V1 V2 : Type v} {e1 : ValueEmbedding D V1} {e2 : ValueEmbedding D V2}
    {I1 : Interpretation O1 V1} {I2 : Interpretation O2 V2}
    (h1 : IsInterpretation D e1 V I1) (sat1 : satisfiesClosure I1 part)
    (h2 : IsInterpretation D e2 V I2)
    (sat2 : ∀ x ∈ items, (¬ IsAssertion x.axiom ∧ ¬ Meaningless x.axiom) ∨ x ∈ rest → satisfies I2 x.axiom) :
    Model D (leftEmbedding e1) V (join e1 e2 (fun i => ¬ ∃ y ∈ rest, i ∈ axiomIndividuals y.axiom) I1 I2) items := by
  refine ⟨vocab, join_interpretation V e1 e2 _ _ _ h1 h2,
    (join e1 e2 (fun i => ¬ ∃ y ∈ rest, i ∈ axiomIndividuals y.axiom) I1 I2).anonymousIndividuals, ?_⟩
  rw [with_self]
  intro x member
  by_cases assertion : IsAssertion x.axiom
  · rcases cover x member with ⟨y, inPart, same⟩ | inRest
    · have sy := sat1 y inPart
      rw [same] at sy
      exact join_left_assertion h1 x.axiom assertion
        (fun i mi ⟨z, mz, mi'⟩ => apart y inPart (same ▸ assertion) z mz i (same ▸ mi) mi')
        (asserted x member assertion) sy
    · exact join_right_assertion vocab h1 h2 x.axiom assertion
        (fun i mi other => other ⟨x, inRest, mi⟩) (asserted x member assertion) (sat2 x member (.inr inRest))
  · rcases cover x member with ⟨y, inPart, same⟩ | inRest
    · by_cases meaningless : Meaningless x.axiom
      · exact meaningless_satisfied _ meaningless
      have sy := sat1 y inPart
      rw [same] at sy
      exact join_plain vocab h1 h2 x.axiom (plain x member assertion) sy
        (sat2 x member (.inl ⟨assertion, meaningless⟩))
    · rcases restKinds x inRest with isAssertion | meaningless
      · exact absurd isAssertion assertion
      · exact meaningless_satisfied _ meaningless

/-- A closed class expression means the same at the left image of an element
    as at the element in the uncombined model of the part. -/
private theorem left_class {O1 O2 : Type u} {V1 V2 : Type v} {e1 : ValueEmbedding D V1} {e2 : ValueEmbedding D V2}
    {left : Individual → Prop} {I1 : Interpretation O1 V1} {I2 : Interpretation O2 V2}
    (asg : AnonymousIndividual → O1) {e : ClassExpression} (closed : Closed D V e) (x : O1) :
    classDenote (join e1 e2 left (withAnonymous I1 asg) I2) e (.inl x) ↔ classDenote I1 e x := by
  rw [closed_left closed]
  exact side_class (anonymous_side I1 asg) e (plain_mono e (fun _ h => h.elim) closed) x

/-- When the axioms other than assertions are plain and a closure's assertions
    fall into a part and a rest that share no individual, an instance question
    about an individual that the rest does not name has the same answer for
    the part as for the whole closure, provided the closure has a model. -/
theorem instance_part (vocab : IsVocabulary D V) {items part rest : List AnnotatedAxiom}
    (cover : ∀ x ∈ items, (∃ y ∈ part, y.axiom = x.axiom) ∨ x ∈ rest)
    (inside : ∀ y ∈ part, ∃ x ∈ items, x.axiom = y.axiom)
    (plain : ∀ x ∈ items, ¬ IsAssertion x.axiom → PlainAxiom D V x.axiom)
    (asserted : ∀ x ∈ items, IsAssertion x.axiom → PlainAssertion D V x.axiom)
    (restKinds : ∀ x ∈ rest, IsAssertion x.axiom ∨ Meaningless x.axiom)
    (apart : ∀ x ∈ part, IsAssertion x.axiom → ∀ y ∈ rest, ∀ i ∈ axiomIndividuals x.axiom,
      i ∉ axiomIndividuals y.axiom)
    {a : NamedIndividual} (aApart : ∀ y ∈ rest, Individual.Named a ∉ axiomIndividuals y.axiom)
    {e : ClassExpression} (closed : Closed D V e)
    (consistent : Consistent.{u,v,w} D V items) :
    InstanceOf.{u,v,w} D V items a e ↔ InstanceOf.{u,v,w} D V part a e := by
  constructor
  · intro entailed O1 V1 e1 I1 model1
    obtain ⟨_, h1, asg1, sat1⟩ := model1
    by_contra notIn
    obtain ⟨O2, V2, e2, I2, _, h2, asg2, sat2⟩ := consistent
    have model := join_model vocab cover plain asserted restKinds apart
      (I1 := withAnonymous I1 asg1) (I2 := withAnonymous I2 asg2) h1 sat1 h2 (fun x mx _ => sat2 x mx)
    have holds := entailed (O1 ⊕ O2) (V1 ⊕ V2) (leftEmbedding e1) _ model
    have aLeft : ¬ ∃ y ∈ rest, Individual.Named a ∈ axiomIndividuals y.axiom :=
      fun ⟨y, my, mi⟩ => aApart y my mi
    have place := individual_left (e1 := e1) (e2 := e2) (I1 := withAnonymous I1 asg1)
      (I2 := withAnonymous I2 asg2) (left := fun i => ¬ ∃ y ∈ rest, i ∈ axiomIndividuals y.axiom) aLeft
    simp only [individual] at place
    rw [place, left_class asg1 closed] at holds
    exact notIn holds
  · intro entailed O W emb I model
    exact entailed O W emb I (model_part inside model)

/-- Under the same conditions, a closed class expression is satisfiable for the
    part exactly when it is for the closure. -/
theorem satisfiable_part (vocab : IsVocabulary D V) {items part rest : List AnnotatedAxiom}
    (cover : ∀ x ∈ items, (∃ y ∈ part, y.axiom = x.axiom) ∨ x ∈ rest)
    (inside : ∀ y ∈ part, ∃ x ∈ items, x.axiom = y.axiom)
    (plain : ∀ x ∈ items, ¬ IsAssertion x.axiom → PlainAxiom D V x.axiom)
    (asserted : ∀ x ∈ items, IsAssertion x.axiom → PlainAssertion D V x.axiom)
    (restKinds : ∀ x ∈ rest, IsAssertion x.axiom ∨ Meaningless x.axiom)
    (apart : ∀ x ∈ part, IsAssertion x.axiom → ∀ y ∈ rest, ∀ i ∈ axiomIndividuals x.axiom,
      i ∉ axiomIndividuals y.axiom)
    {e : ClassExpression} (closed : Closed D V e)
    (consistent : Consistent.{u,v,w} D V items) :
    ClassSatisfiable.{u,v,w} D V items e ↔ ClassSatisfiable.{u,v,w} D V part e := by
  constructor
  · rintro ⟨O, W, emb, I, model, x, inside'⟩
    exact ⟨O, W, emb, I, model_part inside model, x, inside'⟩
  · rintro ⟨O1, V1, e1, I1, ⟨_, h1, asg1, sat1⟩, x, member⟩
    obtain ⟨O2, V2, e2, I2, _, h2, asg2, sat2⟩ := consistent
    have model := join_model vocab cover plain asserted restKinds apart
      (I1 := withAnonymous I1 asg1) (I2 := withAnonymous I2 asg2) h1 sat1 h2 (fun x mx _ => sat2 x mx)
    exact ⟨O1 ⊕ O2, V1 ⊕ V2, leftEmbedding e1, _, model, .inl x, (left_class asg1 closed x).mpr member⟩

/-- Under the same conditions, one closed class expression is subsumed by
    another for the part exactly when it is for the closure. -/
theorem subsumed_part (vocab : IsVocabulary D V) {items part rest : List AnnotatedAxiom}
    (cover : ∀ x ∈ items, (∃ y ∈ part, y.axiom = x.axiom) ∨ x ∈ rest)
    (inside : ∀ y ∈ part, ∃ x ∈ items, x.axiom = y.axiom)
    (plain : ∀ x ∈ items, ¬ IsAssertion x.axiom → PlainAxiom D V x.axiom)
    (asserted : ∀ x ∈ items, IsAssertion x.axiom → PlainAssertion D V x.axiom)
    (restKinds : ∀ x ∈ rest, IsAssertion x.axiom ∨ Meaningless x.axiom)
    (apart : ∀ x ∈ part, IsAssertion x.axiom → ∀ y ∈ rest, ∀ i ∈ axiomIndividuals x.axiom,
      i ∉ axiomIndividuals y.axiom)
    {a b : ClassExpression} (closedA : Closed D V a) (closedB : Closed D V b)
    (consistent : Consistent.{u,v,w} D V items) :
    Subsumed.{u,v,w} D V items a b ↔ Subsumed.{u,v,w} D V part a b := by
  constructor
  · intro sub O1 V1 e1 I1 model1 x inA
    obtain ⟨_, h1, asg1, sat1⟩ := model1
    obtain ⟨O2, V2, e2, I2, _, h2, asg2, sat2⟩ := consistent
    have model := join_model vocab cover plain asserted restKinds apart
      (I1 := withAnonymous I1 asg1) (I2 := withAnonymous I2 asg2) h1 sat1 h2 (fun x mx _ => sat2 x mx)
    have inB := sub (O1 ⊕ O2) (V1 ⊕ V2) (leftEmbedding e1) _ model (.inl x) ((left_class asg1 closedA x).mpr inA)
    exact (left_class asg1 closedB x).mp inB
  · intro sub O W emb I model x inA
    exact sub O W emb I (model_part inside model) x inA

/-! ## Consistency part by part -/

/-- A closure with a model gives a model to copies of some of its axioms. -/
theorem consistent_inside {items part : List AnnotatedAxiom}
    (inside : ∀ y ∈ part, ∃ x ∈ items, x.axiom = y.axiom)
    (consistent : Consistent.{u,v,w} D V items) : Consistent.{u,v,w} D V part := by
  obtain ⟨O, W, emb, I, model⟩ := consistent
  exact ⟨O, W, emb, I, model_part inside model⟩

/-- A model of copies of the axioms of a closure that mean something is a
    model of the closure. -/
theorem consistent_cover {items part : List AnnotatedAxiom}
    (cover : ∀ x ∈ items, ¬ Meaningless x.axiom → ∃ y ∈ part, y.axiom = x.axiom)
    (consistent : Consistent.{u,v,w} D V part) : Consistent.{u,v,w} D V items := by
  obtain ⟨O, W, emb, I, vocab', h, asg, sat⟩ := consistent
  refine ⟨O, W, emb, I, vocab', h, asg, fun x member => ?_⟩
  by_cases meaningless : Meaningless x.axiom
  · exact meaningless_satisfied _ meaningless
  · obtain ⟨y, my, same⟩ := cover x member meaningless
    rw [← same]
    exact sat y my

/-- When the axioms other than assertions are plain and a closure's assertions
    fall into a part and a rest that share no individual, the closure has a
    model when the part has one and copies of the rest and of the meaningful
    axioms other than assertions have one. -/
theorem consistent_join (vocab : IsVocabulary D V) {items part rest others : List AnnotatedAxiom}
    (cover : ∀ x ∈ items, (∃ y ∈ part, y.axiom = x.axiom) ∨ x ∈ rest)
    (plain : ∀ x ∈ items, ¬ IsAssertion x.axiom → PlainAxiom D V x.axiom)
    (asserted : ∀ x ∈ items, IsAssertion x.axiom → PlainAssertion D V x.axiom)
    (restKinds : ∀ x ∈ rest, IsAssertion x.axiom ∨ Meaningless x.axiom)
    (apart : ∀ x ∈ part, IsAssertion x.axiom → ∀ y ∈ rest, ∀ i ∈ axiomIndividuals x.axiom,
      i ∉ axiomIndividuals y.axiom)
    (othersCover : ∀ x ∈ items, (¬ IsAssertion x.axiom ∧ ¬ Meaningless x.axiom) ∨ x ∈ rest →
      ∃ y ∈ others, y.axiom = x.axiom)
    (consistentPart : Consistent.{u,v,w} D V part) (consistentOthers : Consistent.{u,v,w} D V others) :
    Consistent.{u,v,w} D V items := by
  obtain ⟨O1, V1, e1, I1, _, h1, asg1, sat1⟩ := consistentPart
  obtain ⟨O2, V2, e2, I2, _, h2, asg2, sat2⟩ := consistentOthers
  refine ⟨O1 ⊕ O2, V1 ⊕ V2, leftEmbedding e1, _, join_model vocab cover plain asserted restKinds apart
    (I1 := withAnonymous I1 asg1) (I2 := withAnonymous I2 asg2) h1 sat1 h2 (fun x mx needed => ?_)⟩
  obtain ⟨y, my, same⟩ := othersCover x mx needed
  rw [← same]
  exact sat2 y my

end Main

end Rowl.Partition
