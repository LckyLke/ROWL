import Rowl.AxiomEquality
import Rowl.OwlLaws
import Rowl.OwlExamples

namespace Rowl.StructuralCongruence
open Aeneas Aeneas.Std RowlRust.model
open Rowl.Owl
open Rowl.RangeEquality (RangeEq RangeSetEq SetEq)
open Rowl.ClassEquality (ClassEq ClassSetEq IsThing IsLiteral OptionalRangeEq)
open Rowl.AxiomEquality (BodyEq AxiomEq)
universe u v w
variable {Object : Type u} {Value : Type v}
attribute [local simp] alloc.vec.Vec.eq_iff
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4000

/-- The exact two interpretation conditions needed for omission-default
    expansion. These are consequences of the full OWL interpretation predicate. -/
def Defaults (I : Interpretation Object Value) : Prop :=
  (∀ x, I.classes thing x) ∧ (∀ x, I.datatypes literalDatatype x)
/-- Mutual structural membership with one oriented comparison relation. -/
def MatchSet {α : Type} (rel : α → α → Prop) (left right : List α) : Prop :=
  (∀ a ∈ left, ∃ b ∈ right, rel a b) ∧ (∀ b ∈ right, ∃ a ∈ left, rel a b)
/-- Exactly the occurrence-distinctness preconditions needed to preserve the
    disjointness and difference meanings; other arity rules remain separate. -/
def DistinctMembers (body : Axiom) : Prop :=
  match body with
  | .DisjointClasses xs | .DisjointUnion _ xs => Rowl.Arity.Unique ClassEq xs.elements
  | .DisjointObjectProperties xs => Rowl.Arity.Unique Eq xs.elements
  | .DisjointDataProperties xs => Rowl.Arity.Unique Eq xs.elements
  | .DifferentIndividuals xs => Rowl.Arity.Unique Eq xs.elements
  | _ => True
/-- Whole supplied, standardized-apart axiom closures as structural sets. -/
def ClosureEq (left right : AxiomClosure) : Prop := MatchSet AxiomEq left right

/-- Optional object filler meaning; omission imposes no additional restriction. -/
def ClassFiller (I : Interpretation Object Value) (value : Option ClassExpression) (x : Object) : Prop :=
  match value with | none => True | some c => classDenote I c x
/-- Optional data filler meaning over the entire data domain. -/
def RangeFiller (I : Interpretation Object Value) (value : Option DataRange) (x : Value) : Prop :=
  match value with | none => True | some r => dataDenote I r x

private theorem listN_mem_size {α : Type} [SizeOf α] {n : Nat}
    (xs : Aeneas.Data.ListN.ListN α n) {x : α} (h : x ∈ xs.toList) :
    sizeOf x < sizeOf xs := by
  induction xs with
  | nil => simp [Aeneas.Data.ListN.ListN.toList] at h
  | cons head tail ih =>
    simp only [Aeneas.Data.ListN.ListN.toList,List.mem_cons] at h
    rcases h with rfl | h
    · simp +arith
    · have := ih h
      simp only [Data.ListN.ListN.cons.sizeOf_spec]; omega
private theorem vec_mem_size {α : Type} [SizeOf α] (xs : alloc.vec.Vec α)
    {x : α} (h : x ∈ xs.val) : sizeOf x < sizeOf xs := by
  have := listN_mem_size xs.slice.list h
  cases xs with | mk slice => cases slice; simp_all [alloc.vec.Vec.val,Slice.val]; omega


private theorem two_member_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) (child : α)
    (member : child ∈ xs.elements) : sizeOf child < sizeOf xs := by
  simp only [AtLeastTwo.elements,List.mem_cons] at member
  rcases member with rfl | rfl | member
  · cases xs; simp +arith
  · cases xs; simp +arith
  · have := vec_mem_size xs.rest member
    cases xs; simp_all; omega
private theorem atomic_matching {α : Type} {xs ys : List α} (equal : SetEq xs ys) : MatchSet Eq xs ys :=
  ⟨fun a mem => ⟨a,(equal a).mp mem,rfl⟩,fun b mem => ⟨b,(equal b).mpr mem,rfl⟩⟩
private theorem range_matching {xs ys : List DataRange} (equal : RangeSetEq xs ys) : MatchSet RangeEq xs ys :=
  ⟨equal.1,fun b mem => by
    obtain ⟨a,ma,ba⟩ := equal.2 b mem
    exact ⟨a,ma,Rowl.RangeEquality.range_eq_symm b a ba⟩⟩
private theorem class_matching {xs ys : List ClassExpression} (equal : ClassSetEq xs ys) : MatchSet ClassEq xs ys :=
  ⟨equal.1,fun b mem => by
    obtain ⟨a,ma,ba⟩ := equal.2 b mem
    exact ⟨a,ma,Rowl.ClassEquality.class_eq_symm b a ba⟩⟩
private theorem forall_matching {α : Type} {rel : α → α → Prop} {xs ys : List α}
    (matching : MatchSet rel xs ys) (P Q : α → Prop)
    (child : ∀ a ∈ xs, ∀ b ∈ ys, rel a b → (P a ↔ Q b)) :
    (∀ a ∈ xs, P a) ↔ ∀ b ∈ ys, Q b := by
  constructor
  · intro all b mb
    obtain ⟨a,ma,ab⟩ := matching.2 b mb
    exact (child a ma b mb ab).mp (all a ma)
  · intro all a ma
    obtain ⟨b,mb,ab⟩ := matching.1 a ma
    exact (child a ma b mb ab).mpr (all b mb)
private theorem exists_matching {α : Type} {rel : α → α → Prop} {xs ys : List α}
    (matching : MatchSet rel xs ys) (P Q : α → Prop)
    (child : ∀ a ∈ xs, ∀ b ∈ ys, rel a b → (P a ↔ Q b)) :
    (∃ a ∈ xs, P a) ↔ ∃ b ∈ ys, Q b := by
  constructor
  · rintro ⟨a,ma,pa⟩
    obtain ⟨b,mb,ab⟩ := matching.1 a ma
    exact ⟨b,mb,(child a ma b mb ab).mp pa⟩
  · rintro ⟨b,mb,qb⟩
    obtain ⟨a,ma,ab⟩ := matching.2 b mb
    exact ⟨a,ma,(child a ma b mb ab).mpr qb⟩

/-- Exact range structure preserves denotation for arbitrary interpretations;
    no finite-domain or datatype-value solver assumption is needed. -/
theorem range_denotation (I : Interpretation Object Value) (left right : DataRange)
    (equal : RangeEq left right) (x : Value) : dataDenote I left x ↔ dataDenote I right x := by
  cases hLeft : left <;> cases hRight : right <;> simp only [hLeft,hRight,RangeEq] at equal
  case Datatype.Datatype a b => cases equal; rfl
  case Intersection.Intersection xs ys =>
    have matching : MatchSet RangeEq xs.elements ys.elements := by
      apply range_matching
      simpa [RangeSetEq,Rowl.RangeEquality.Members,AtLeastTwo.elements] using equal
    have child : ∀ a ∈ xs.elements, ∀ b ∈ ys.elements, RangeEq a b → (dataDenote I a x ↔ dataDenote I b x) := by
      intro a ma b mb ab
      have := two_member_size xs a ma
      have := two_member_size ys b mb
      exact range_denotation I a b ab x
    simpa only [dataDenote,AtLeastTwo.elements,List.forall_mem_cons] using
      forall_matching matching (fun a => dataDenote I a x) (fun b => dataDenote I b x) child
  case Union.Union xs ys =>
    have matching : MatchSet RangeEq xs.elements ys.elements := by
      apply range_matching
      simpa [RangeSetEq,Rowl.RangeEquality.Members,AtLeastTwo.elements] using equal
    have child : ∀ a ∈ xs.elements, ∀ b ∈ ys.elements, RangeEq a b → (dataDenote I a x ↔ dataDenote I b x) := by
      intro a ma b mb ab
      have := two_member_size xs a ma
      have := two_member_size ys b mb
      exact range_denotation I a b ab x
    simpa only [dataDenote,AtLeastTwo.elements,List.mem_cons,exists_eq_or_imp,exists_prop] using
      exists_matching matching (fun a => dataDenote I a x) (fun b => dataDenote I b x) child
  case Complement.Complement a b =>
    have nested := range_denotation I a b equal x
    simpa only [dataDenote] using not_congr nested
  case OneOf.OneOf xs ys =>
    simpa only [dataDenote] using exists_matching (atomic_matching equal) (fun a => I.literals a = x) (fun b => I.literals b = x)
      (fun _ _ _ _ same => by cases same; rfl)
  case Restriction.Restriction a xs b ys =>
    rcases equal with ⟨rfl,facets⟩
    have all := forall_matching (atomic_matching facets) (fun f => I.facets f x) (fun f => I.facets f x)
      (fun _ _ _ _ same => by cases same; rfl)
    simpa only [dataDenote] using and_congr_right (fun _ => all)
termination_by sizeOf left + sizeOf right
decreasing_by
  all_goals simp only [hLeft,hRight,DataRange.Intersection.sizeOf_spec,DataRange.Union.sizeOf_spec,DataRange.Complement.sizeOf_spec]
  all_goals omega

/-- Every full OWL interpretation supplies the normative omission defaults. -/
theorem interpretation_defaults {Native : Type w} (D : DatatypeMap Native)
    (embed : ValueEmbedding D Value) (V : Vocabulary) (I : Interpretation Object Value)
    (valid : IsInterpretation D embed V I) : Defaults I :=
  ⟨valid.1,valid.2.2.2.2.2.2.2.1⟩
/-- Anonymous reassignment does not alter the default class/data denotations. -/
theorem defaults_with_anonymous (I : Interpretation Object Value) (assignment : AnonymousIndividual → Object)
    (valid : Defaults I) : Defaults (withAnonymous I assignment) := valid
private theorem thing_identity (value : ClassExpression) (top : IsThing value) : value = .Class thing := by
  cases value <;> simp only [IsThing] at top; try contradiction
  rename_i c
  cases c with | mk i => cases i with | mk bytes =>
    have equal : bytes = thing.iri.spelling := by
      simpa only [alloc.vec.Vec.eq_iff] using (by
        simpa [thing,Rowl.ClassEquality.ThingBytes] using top)
    simp [equal]
private theorem literal_identity (value : DataRange) (top : IsLiteral value) : value = .Datatype literalDatatype := by
  cases value <;> simp only [IsLiteral] at top; try contradiction
  rename_i d
  cases d with | mk i => cases i with | mk bytes =>
    have equal : bytes = literalDatatype.iri.spelling := by
      simpa only [alloc.vec.Vec.eq_iff] using (by
        simpa [literalDatatype,Rowl.ClassEquality.LiteralBytes] using top)
    simp [equal]
private theorem optional_range_denotation (I : Interpretation Object Value) (valid : Defaults I)
    (left right : Option DataRange) (equal : OptionalRangeEq left right) (x : Value) :
    RangeFiller I left x ↔ RangeFiller I right x := by
  cases left <;> cases right <;> simp only [OptionalRangeEq,RangeFiller] at equal ⊢
  case some.some a b => exact range_denotation I a b equal x
  case none.some b => rw [literal_identity b equal]; simpa only [dataDenote,true_iff] using valid.2 x
  case some.none a => rw [literal_identity a equal]; simpa only [dataDenote,iff_true] using valid.2 x
private theorem lower_congr {α : Type u} (n : Nat) {P Q : α → Prop} (same : ∀ x, P x ↔ Q x) :
    AtLeast n P ↔ AtLeast n Q := by
  have equal : P = Q := funext (fun x => propext (same x))
  rw [equal]
private theorem upper_congr {α : Type u} (n : Nat) {P Q : α → Prop} (same : ∀ x, P x ↔ Q x) :
    AtMost n P ↔ AtMost n Q := not_congr (lower_congr (n+1) same)
private theorem exact_congr {α : Type u} (n : Nat) {P Q : α → Prop} (same : ∀ x, P x ↔ Q x) :
    Exactly n P ↔ Exactly n Q := and_congr (lower_congr n same) (upper_congr n same)

/-- All eighteen class-expression forms preserve their OWL extension under
    structural identity, including both normative cardinality defaults. -/
theorem class_denotation (I : Interpretation Object Value) (valid : Defaults I)
    (left right : ClassExpression) (equal : ClassEq left right) (x : Object) :
    classDenote I left x ↔ classDenote I right x := by
  cases hLeft : left <;> cases hRight : right <;> simp only [hLeft,hRight,ClassEq] at equal
  case Class.Class a b => cases equal; rfl
  case ObjectIntersectionOf.ObjectIntersectionOf xs ys =>
    have matching : MatchSet ClassEq xs.elements ys.elements := by
      apply class_matching
      simpa [ClassSetEq,Rowl.ClassEquality.Members,AtLeastTwo.elements] using equal
    have child : ∀ a ∈ xs.elements, ∀ b ∈ ys.elements, ClassEq a b → (classDenote I a x ↔ classDenote I b x) := by
      intro a ma b mb ab
      have := two_member_size xs a ma
      have := two_member_size ys b mb
      exact class_denotation I valid a b ab x
    simpa only [classDenote,AtLeastTwo.elements,List.forall_mem_cons] using
      forall_matching matching (fun a => classDenote I a x) (fun b => classDenote I b x) child
  case ObjectUnionOf.ObjectUnionOf xs ys =>
    have matching : MatchSet ClassEq xs.elements ys.elements := by
      apply class_matching
      simpa [ClassSetEq,Rowl.ClassEquality.Members,AtLeastTwo.elements] using equal
    have child : ∀ a ∈ xs.elements, ∀ b ∈ ys.elements, ClassEq a b → (classDenote I a x ↔ classDenote I b x) := by
      intro a ma b mb ab
      have := two_member_size xs a ma
      have := two_member_size ys b mb
      exact class_denotation I valid a b ab x
    simpa only [classDenote,AtLeastTwo.elements,List.mem_cons,exists_eq_or_imp,exists_prop] using
      exists_matching matching (fun a => classDenote I a x) (fun b => classDenote I b x) child
  case ObjectComplementOf.ObjectComplementOf a b =>
    have nested := class_denotation I valid a b equal x
    simpa only [classDenote] using not_congr nested
  case ObjectOneOf.ObjectOneOf xs ys =>
    simpa only [classDenote] using exists_matching (atomic_matching equal) (fun a => individual I a = x) (fun b => individual I b = x)
      (fun _ _ _ _ same => by cases same; rfl)
  case ObjectSomeValuesFrom.ObjectSomeValuesFrom p a q b =>
    rcases equal with ⟨rfl,nested⟩
    simpa only [classDenote] using exists_congr (fun y => and_congr_right (fun _ => class_denotation I valid a b nested y))
  case ObjectAllValuesFrom.ObjectAllValuesFrom p a q b =>
    rcases equal with ⟨rfl,nested⟩
    simpa only [classDenote] using forall_congr' (fun y => imp_congr_right (fun _ => class_denotation I valid a b nested y))
  case ObjectHasValue.ObjectHasValue p a q b => rcases equal with ⟨rfl,rfl⟩; rfl
  case ObjectHasSelf.ObjectHasSelf p q => cases equal; rfl
  case ObjectMinCardinality.ObjectMinCardinality n p xs m q ys =>
    rw [ClassEq.eq_def] at equal
    rcases equal with ⟨rfl,rfl,fillers⟩
    have nested : ∀ y, ClassFiller I xs y ↔ ClassFiller I ys y := by
      intro y
      cases hx : xs <;> cases hy : ys <;> simp only [hx,hy,ClassFiller] at fillers ⊢
      case some.some a b =>
        have sa : sizeOf a < sizeOf xs := by rw [hx]; simp +arith
        have sb : sizeOf b < sizeOf ys := by rw [hy]; simp +arith
        exact class_denotation I valid a b fillers y
      case none.some b => rw [thing_identity b fillers]; simpa only [classDenote,true_iff] using valid.1 y
      case some.none a => rw [thing_identity a fillers]; simpa only [classDenote,iff_true] using valid.1 y
    rw [classDenote.eq_def,classDenote.eq_def]
    change AtLeast (Rowl.Probes.naturalValue n) (fun y => objectRelation I p x y ∧ ClassFiller I xs y) ↔
      AtLeast (Rowl.Probes.naturalValue n) (fun y => objectRelation I p x y ∧ ClassFiller I ys y)
    exact lower_congr (Rowl.Probes.naturalValue n) (fun y => and_congr Iff.rfl (nested y))
  case ObjectMaxCardinality.ObjectMaxCardinality n p xs m q ys =>
    rw [ClassEq.eq_def] at equal
    rcases equal with ⟨rfl,rfl,fillers⟩
    have nested : ∀ y, ClassFiller I xs y ↔ ClassFiller I ys y := by
      intro y
      cases hx : xs <;> cases hy : ys <;> simp only [hx,hy,ClassFiller] at fillers ⊢
      case some.some a b =>
        have sa : sizeOf a < sizeOf xs := by rw [hx]; simp +arith
        have sb : sizeOf b < sizeOf ys := by rw [hy]; simp +arith
        exact class_denotation I valid a b fillers y
      case none.some b => rw [thing_identity b fillers]; simpa only [classDenote,true_iff] using valid.1 y
      case some.none a => rw [thing_identity a fillers]; simpa only [classDenote,iff_true] using valid.1 y
    rw [classDenote.eq_def,classDenote.eq_def]
    change AtMost (Rowl.Probes.naturalValue n) (fun y => objectRelation I p x y ∧ ClassFiller I xs y) ↔
      AtMost (Rowl.Probes.naturalValue n) (fun y => objectRelation I p x y ∧ ClassFiller I ys y)
    exact upper_congr (Rowl.Probes.naturalValue n) (fun y => and_congr Iff.rfl (nested y))
  case ObjectExactCardinality.ObjectExactCardinality n p xs m q ys =>
    rw [ClassEq.eq_def] at equal
    rcases equal with ⟨rfl,rfl,fillers⟩
    have nested : ∀ y, ClassFiller I xs y ↔ ClassFiller I ys y := by
      intro y
      cases hx : xs <;> cases hy : ys <;> simp only [hx,hy,ClassFiller] at fillers ⊢
      case some.some a b =>
        have sa : sizeOf a < sizeOf xs := by rw [hx]; simp +arith
        have sb : sizeOf b < sizeOf ys := by rw [hy]; simp +arith
        exact class_denotation I valid a b fillers y
      case none.some b => rw [thing_identity b fillers]; simpa only [classDenote,true_iff] using valid.1 y
      case some.none a => rw [thing_identity a fillers]; simpa only [classDenote,iff_true] using valid.1 y
    rw [classDenote.eq_def,classDenote.eq_def]
    change Exactly (Rowl.Probes.naturalValue n) (fun y => objectRelation I p x y ∧ ClassFiller I xs y) ↔
      Exactly (Rowl.Probes.naturalValue n) (fun y => objectRelation I p x y ∧ ClassFiller I ys y)
    exact exact_congr (Rowl.Probes.naturalValue n) (fun y => and_congr Iff.rfl (nested y))
  case DataSomeValuesFrom.DataSomeValuesFrom p a q b =>
    rcases equal with ⟨rfl,nested⟩
    simpa only [classDenote] using exists_congr (fun y => and_congr_right (fun _ => range_denotation I a b nested y))
  case DataAllValuesFrom.DataAllValuesFrom p a q b =>
    rcases equal with ⟨rfl,nested⟩
    simpa only [classDenote] using forall_congr' (fun y => imp_congr_right (fun _ => range_denotation I a b nested y))
  case DataHasValue.DataHasValue p a q b => rcases equal with ⟨rfl,rfl⟩; rfl
  case DataMinCardinality.DataMinCardinality n p xs m q ys =>
    rcases equal with ⟨rfl,rfl,fillers⟩
    rw [classDenote.eq_def,classDenote.eq_def]
    change AtLeast (Rowl.Probes.naturalValue n) (fun y => I.dataProperties p x y ∧ RangeFiller I xs y) ↔
      AtLeast (Rowl.Probes.naturalValue n) (fun y => I.dataProperties p x y ∧ RangeFiller I ys y)
    exact lower_congr (Rowl.Probes.naturalValue n) (fun y => and_congr Iff.rfl (optional_range_denotation I valid xs ys fillers y))
  case DataMaxCardinality.DataMaxCardinality n p xs m q ys =>
    rcases equal with ⟨rfl,rfl,fillers⟩
    rw [classDenote.eq_def,classDenote.eq_def]
    change AtMost (Rowl.Probes.naturalValue n) (fun y => I.dataProperties p x y ∧ RangeFiller I xs y) ↔
      AtMost (Rowl.Probes.naturalValue n) (fun y => I.dataProperties p x y ∧ RangeFiller I ys y)
    exact upper_congr (Rowl.Probes.naturalValue n) (fun y => and_congr Iff.rfl (optional_range_denotation I valid xs ys fillers y))
  case DataExactCardinality.DataExactCardinality n p xs m q ys =>
    rcases equal with ⟨rfl,rfl,fillers⟩
    rw [classDenote.eq_def,classDenote.eq_def]
    change Exactly (Rowl.Probes.naturalValue n) (fun y => I.dataProperties p x y ∧ RangeFiller I xs y) ↔
      Exactly (Rowl.Probes.naturalValue n) (fun y => I.dataProperties p x y ∧ RangeFiller I ys y)
    exact exact_congr (Rowl.Probes.naturalValue n) (fun y => and_congr Iff.rfl (optional_range_denotation I valid xs ys fillers y))
termination_by sizeOf left + sizeOf right
decreasing_by
  all_goals simp only [hLeft,hRight,ClassExpression.ObjectIntersectionOf.sizeOf_spec,
    ClassExpression.ObjectUnionOf.sizeOf_spec,ClassExpression.ObjectComplementOf.sizeOf_spec,
    ClassExpression.ObjectSomeValuesFrom.sizeOf_spec,ClassExpression.ObjectAllValuesFrom.sizeOf_spec,
    ClassExpression.ObjectMinCardinality.sizeOf_spec,ClassExpression.ObjectMaxCardinality.sizeOf_spec,
    ClassExpression.ObjectExactCardinality.sizeOf_spec]
  all_goals omega


private theorem all_equal_matching {α : Type} {β : Sort w} {rel : α → α → Prop} {xs ys : List α}
    (matching : MatchSet rel xs ys) (f g : α → β)
    (child : ∀ a ∈ xs, ∀ b ∈ ys, rel a b → f a = g b) : allEqual xs f ↔ allEqual ys g := by
  constructor
  · intro all b mb d md
    obtain ⟨a,ma,ab⟩ := matching.2 b mb
    obtain ⟨c,mc,cd⟩ := matching.2 d md
    exact (child a ma b mb ab).symm.trans ((all a ma c mc).trans (child c mc d md cd))
  · intro all a ma c mc
    obtain ⟨b,mb,ab⟩ := matching.1 a ma
    obtain ⟨d,md,cd⟩ := matching.1 c mc
    exact (child a ma b mb ab).trans ((all b mb d md).trans (child c mc d md cd).symm)

private theorem pairwise_distinct_iff {α : Type} (rel S : α → α → Prop)
    (refl : ∀ a, rel a a) (symmetric : ∀ a b, S a b → S b a)
    (xs : List α) (unique : Rowl.Arity.Unique rel xs) :
    xs.Pairwise S ↔ ∀ a ∈ xs, ∀ b ∈ xs, ¬ rel a b → S a b := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [Rowl.Arity.Unique,List.pairwise_cons] at unique
    rw [List.pairwise_cons]
    constructor
    · rintro ⟨head,tail⟩ b mb c mc different
      simp only [List.mem_cons] at mb mc
      rcases mb with rfl | mb <;> rcases mc with rfl | mc
      · exact False.elim (different (refl _))
      · exact head c mc
      · exact symmetric _ _ (head _ mb)
      · exact (ih unique.2).mp tail b mb c mc different
    · intro all
      constructor
      · intro b mb
        exact all a (by simp) b (by simp [mb]) (unique.1 b mb)
      · apply (ih unique.2).mpr
        intro b mb c mc different
        exact all b (by simp [mb]) c (by simp [mc]) different

private theorem pairwise_matching {α : Type} (rel S T : α → α → Prop)
    (refl : ∀ a, rel a a) (symm : ∀ a b, rel a b → rel b a)
    (trans : ∀ a b c, rel a b → rel b c → rel a c)
    (symmS : ∀ a b, S a b → S b a) (symmT : ∀ a b, T a b → T b a)
    {xs ys : List α} (matching : MatchSet rel xs ys)
    (leftUnique : Rowl.Arity.Unique rel xs) (rightUnique : Rowl.Arity.Unique rel ys)
    (child : ∀ a ∈ xs, ∀ b ∈ ys, rel a b → ∀ c ∈ xs, ∀ d ∈ ys, rel c d → (S a c ↔ T b d)) :
    xs.Pairwise S ↔ ys.Pairwise T := by
  rw [pairwise_distinct_iff rel S refl symmS xs leftUnique,
    pairwise_distinct_iff rel T refl symmT ys rightUnique]
  constructor
  · intro all b mb d md different
    obtain ⟨a,ma,ab⟩ := matching.2 b mb
    obtain ⟨c,mc,cd⟩ := matching.2 d md
    have distinct : ¬ rel a c := fun ac =>
      different (trans b c d (trans b a c (symm a b ab) ac) cd)
    exact (child a ma b mb ab c mc d md cd).mp (all a ma c mc distinct)
  · intro all a ma c mc different
    obtain ⟨b,mb,ab⟩ := matching.1 a ma
    obtain ⟨d,md,cd⟩ := matching.1 c mc
    have distinct : ¬ rel b d := fun bd =>
      different (trans a d c (trans a b d ab bd) (symm c d cd))
    exact (child a ma b mb ab c mc d md cd).mpr (all b mb d md distinct)

private theorem atomic_pairwise {α : Type} (S : α → α → Prop)
    (symmetric : ∀ a b, S a b → S b a) {xs ys : List α}
    (equal : SetEq xs ys) (leftUnique : Rowl.Arity.Unique Eq xs)
    (rightUnique : Rowl.Arity.Unique Eq ys) : xs.Pairwise S ↔ ys.Pairwise S :=
  pairwise_matching Eq S S (fun _ => rfl) (fun _ _ eq => eq.symm) (fun _ _ _ a b => a.trans b)
    symmetric symmetric (atomic_matching equal) leftUnique rightUnique
    (fun _ _ _ _ same _ _ _ _ other => by cases same; cases other; rfl)

private theorem class_disjoint_matching (I : Interpretation Object Value) (valid : Defaults I)
    {xs ys : List ClassExpression} (equal : ClassSetEq xs ys)
    (leftUnique : Rowl.Arity.Unique ClassEq xs) (rightUnique : Rowl.Arity.Unique ClassEq ys) :
    pairwiseDisjoint xs (classDenote I) ↔ pairwiseDisjoint ys (classDenote I) := by
  apply pairwise_matching ClassEq (fun a b => ∀ x, ¬ (classDenote I a x ∧ classDenote I b x))
    (fun a b => ∀ x, ¬ (classDenote I a x ∧ classDenote I b x))
    Rowl.ClassEquality.class_eq_refl Rowl.ClassEquality.class_eq_symm Rowl.ClassEquality.class_eq_trans
    (fun a b disjoint x both => disjoint x ⟨both.2,both.1⟩)
    (fun a b disjoint x both => disjoint x ⟨both.2,both.1⟩)
    (class_matching equal) leftUnique rightUnique
  intro a _ b _ ab c _ d _ cd
  exact forall_congr' (fun x => not_congr (and_congr (class_denotation I valid a b ab x) (class_denotation I valid c d cd x)))

/-- Successful arity validation supplies every occurrence-distinctness premise. -/
theorem arity_implies_distinct_members (item : AnnotatedAxiom) (valid : Rowl.Arity.AxiomAllowed item) :
    DistinctMembers item.axiom := by
  cases h : item.axiom <;> simp [Rowl.Arity.AxiomAllowed,DistinctMembers,h] at valid ⊢
  all_goals first | exact valid | exact valid.1

/-- Ordered chain/singleton structural identity preserves relational meaning. -/
theorem subproperty_denotation (I : Interpretation Object Value) (left right : SubObjectPropertyExpression)
    (equal : Rowl.AxiomEquality.SubPropertyEq left right) (x y : Object) :
    subRelation I left x y ↔ subRelation I right x y := by
  cases left <;> cases right <;> simp only [Rowl.AxiomEquality.SubPropertyEq] at equal
  case Single.Single a b => cases equal; rfl
  case Chain.Chain a b => simp only [subRelation]; rw [equal]


/-- Full axiom-body identity preserves satisfaction when original disjoint and
    different associations have passed occurrence-distinctness validation. -/
theorem body_satisfaction (I : Interpretation Object Value) (valid : Defaults I)
    (left right : Axiom) (equal : BodyEq left right)
    (leftUnique : DistinctMembers left) (rightUnique : DistinctMembers right) :
    satisfies I left ↔ satisfies I right := by
  cases left <;> cases right <;> simp only [BodyEq] at equal
  case Declaration.Declaration => rfl
  case SubClassOf.SubClassOf a b c d =>
    rcases equal with ⟨ac,bd⟩
    exact forall_congr' (fun x => imp_congr (class_denotation I valid a c ac x) (class_denotation I valid b d bd x))
  case EquivalentClasses.EquivalentClasses xs ys =>
    exact all_equal_matching (class_matching equal) (classDenote I) (classDenote I)
      (fun a _ b _ ab => funext (fun x => propext (class_denotation I valid a b ab x)))
  case DisjointClasses.DisjointClasses xs ys =>
    exact class_disjoint_matching I valid equal leftUnique rightUnique
  case DisjointUnion.DisjointUnion c xs d ys =>
    rcases equal with ⟨rfl,members⟩
    have union : (∀ x, I.classes c x ↔ ∃ e ∈ xs.elements, classDenote I e x) ↔
        ∀ x, I.classes c x ↔ ∃ e ∈ ys.elements, classDenote I e x :=
      forall_congr' (fun x => iff_congr Iff.rfl
        (exists_matching (class_matching members) (fun e => classDenote I e x) (fun e => classDenote I e x)
          (fun a _ b _ ab => class_denotation I valid a b ab x)))
    exact and_congr union (class_disjoint_matching I valid members leftUnique rightUnique)
  case SubObjectPropertyOf.SubObjectPropertyOf a p b q =>
    rcases equal with ⟨sub,rfl⟩
    exact forall_congr' (fun x => forall_congr' (fun y => imp_congr (subproperty_denotation I a b sub x y) Iff.rfl))
  case EquivalentObjectProperties.EquivalentObjectProperties xs ys =>
    exact all_equal_matching (atomic_matching equal) (objectRelation I) (objectRelation I)
      (fun _ _ _ _ same => by cases same; rfl)
  case DisjointObjectProperties.DisjointObjectProperties xs ys =>
    exact atomic_pairwise (fun p q => ∀ xy : Object × Object, ¬ (objectRelation I p xy.1 xy.2 ∧ objectRelation I q xy.1 xy.2))
      (fun p q disjoint xy both => disjoint xy ⟨both.2,both.1⟩) equal leftUnique rightUnique
  case InverseObjectProperties.InverseObjectProperties p q r s => rcases equal with ⟨rfl,rfl⟩; rfl
  case ObjectPropertyDomain.ObjectPropertyDomain p a q b =>
    rcases equal with ⟨rfl,ab⟩
    exact forall_congr' (fun x => forall_congr' (fun _ => imp_congr Iff.rfl (class_denotation I valid a b ab x)))
  case ObjectPropertyRange.ObjectPropertyRange p a q b =>
    rcases equal with ⟨rfl,ab⟩
    exact forall_congr' (fun _ => forall_congr' (fun y => imp_congr Iff.rfl (class_denotation I valid a b ab y)))
  case FunctionalObjectProperty.FunctionalObjectProperty p q => cases equal; rfl
  case InverseFunctionalObjectProperty.InverseFunctionalObjectProperty p q => cases equal; rfl
  case ReflexiveObjectProperty.ReflexiveObjectProperty p q => cases equal; rfl
  case IrreflexiveObjectProperty.IrreflexiveObjectProperty p q => cases equal; rfl
  case SymmetricObjectProperty.SymmetricObjectProperty p q => cases equal; rfl
  case AsymmetricObjectProperty.AsymmetricObjectProperty p q => cases equal; rfl
  case TransitiveObjectProperty.TransitiveObjectProperty p q => cases equal; rfl
  case SubDataPropertyOf.SubDataPropertyOf p q r s => rcases equal with ⟨rfl,rfl⟩; rfl
  case EquivalentDataProperties.EquivalentDataProperties xs ys =>
    exact all_equal_matching (atomic_matching equal) (I.dataProperties) (I.dataProperties)
      (fun _ _ _ _ same => by cases same; rfl)
  case DisjointDataProperties.DisjointDataProperties xs ys =>
    exact atomic_pairwise (fun p q => ∀ xy : Object × Value, ¬ (I.dataProperties p xy.1 xy.2 ∧ I.dataProperties q xy.1 xy.2))
      (fun p q disjoint xy both => disjoint xy ⟨both.2,both.1⟩) equal leftUnique rightUnique
  case DataPropertyDomain.DataPropertyDomain p a q b =>
    rcases equal with ⟨rfl,ab⟩
    exact forall_congr' (fun x => forall_congr' (fun _ => imp_congr Iff.rfl (class_denotation I valid a b ab x)))
  case DataPropertyRange.DataPropertyRange p a q b =>
    rcases equal with ⟨rfl,ab⟩
    exact forall_congr' (fun _ => forall_congr' (fun y => imp_congr Iff.rfl (range_denotation I a b ab y)))
  case FunctionalDataProperty.FunctionalDataProperty p q => cases equal; rfl
  case DatatypeDefinition.DatatypeDefinition dt a du b =>
    rcases equal with ⟨rfl,ab⟩
    exact forall_congr' (fun x => iff_congr Iff.rfl (range_denotation I a b ab x))
  case HasKey.HasKey a ops dps b otherOps otherDps =>
    rcases equal with ⟨ab,objectKeys,dataKeys⟩
    have objects (x y : Object) :
        (∀ p ∈ ops.val, ∃ z, I.named z ∧ objectRelation I p x z ∧ objectRelation I p y z) ↔
        ∀ p ∈ otherOps.val, ∃ z, I.named z ∧ objectRelation I p x z ∧ objectRelation I p y z :=
      forall_matching (atomic_matching objectKeys) _ _ (fun _ _ _ _ same => by cases same; rfl)
    have data (x y : Object) :
        (∀ p ∈ dps.val, ∃ z, I.dataProperties p x z ∧ I.dataProperties p y z) ↔
        ∀ p ∈ otherDps.val, ∃ z, I.dataProperties p x z ∧ I.dataProperties p y z :=
      forall_matching (atomic_matching dataKeys) _ _ (fun _ _ _ _ same => by cases same; rfl)
    exact forall_congr' (fun x => forall_congr' (fun y =>
      imp_congr (class_denotation I valid a b ab x) (imp_congr Iff.rfl
        (imp_congr (class_denotation I valid a b ab y) (imp_congr Iff.rfl
          (imp_congr (objects x y) (imp_congr (data x y) Iff.rfl)))))))
  case SameIndividual.SameIndividual xs ys =>
    exact all_equal_matching (atomic_matching equal) (individual I) (individual I)
      (fun _ _ _ _ same => by cases same; rfl)
  case DifferentIndividuals.DifferentIndividuals xs ys =>
    exact atomic_pairwise (fun a b => individual I a ≠ individual I b)
      (fun a b different => different.symm) equal leftUnique rightUnique
  case ClassAssertion.ClassAssertion a i b j =>
    rcases equal with ⟨ab,rfl⟩
    exact class_denotation I valid a b ab (individual I i)
  case ObjectPropertyAssertion.ObjectPropertyAssertion p a b q c d => rcases equal with ⟨rfl,rfl,rfl⟩; rfl
  case NegativeObjectPropertyAssertion.NegativeObjectPropertyAssertion p a b q c d => rcases equal with ⟨rfl,rfl,rfl⟩; rfl
  case DataPropertyAssertion.DataPropertyAssertion p a b q c d => rcases equal with ⟨rfl,rfl,rfl⟩; rfl
  case NegativeDataPropertyAssertion.NegativeDataPropertyAssertion p a b q c d => rcases equal with ⟨rfl,rfl,rfl⟩; rfl
  case AnnotationAssertion.AnnotationAssertion => rfl
  case SubAnnotationPropertyOf.SubAnnotationPropertyOf => rfl
  case AnnotationPropertyDomain.AnnotationPropertyDomain => rfl
  case AnnotationPropertyRange.AnnotationPropertyRange => rfl


/-- Structural annotated identity preserves satisfaction after arity checks;
    recursive annotations remain structurally preserved though logically inert. -/
theorem axiom_satisfaction (I : Interpretation Object Value) (valid : Defaults I)
    (left right : AnnotatedAxiom) (equal : AxiomEq left right)
    (leftArity : Rowl.Arity.AxiomAllowed left) (rightArity : Rowl.Arity.AxiomAllowed right) :
    satisfiesAnnotated I left ↔ satisfiesAnnotated I right :=
  body_satisfaction I valid left.axiom right.axiom equal.1
    (arity_implies_distinct_members left leftArity) (arity_implies_distinct_members right rightArity)

/-- The actual Rust Boolean comparison and arity entry points certify the
    semantic consequence; no caller-supplied equality claim is assumed. -/
theorem compared_axioms_satisfaction (I : Interpretation Object Value) (valid : Defaults I)
    (left right : AnnotatedAxiom)
    (same : RowlRust.axiom_equality.same_axiom left right = .ok true)
    (leftArity : RowlRust.arity.axiom_allowed left = .ok true)
    (rightArity : RowlRust.arity.axiom_allowed right = .ok true) :
    satisfiesAnnotated I left ↔ satisfiesAnnotated I right := by
  classical
  rw [Rowl.AxiomEquality.same_axiom_total_correct] at same
  rw [Rowl.Arity.axiom_allowed_total_correct] at leftArity rightArity
  have equal : AxiomEq left right := by simpa using same
  have validLeft : Rowl.Arity.AxiomAllowed left := by simpa using leftArity
  have validRight : Rowl.Arity.AxiomAllowed right := by simpa using rightArity
  exact axiom_satisfaction I valid left right equal validLeft validRight

/-- Reordering/repeating complete axiom copies preserves closure satisfaction,
    provided both original closures pass their full arity stage. -/
theorem closure_satisfaction (I : Interpretation Object Value) (valid : Defaults I)
    (left right : AxiomClosure) (equal : ClosureEq left right)
    (leftArity : Rowl.Arity.ClosureOK left) (rightArity : Rowl.Arity.ClosureOK right) :
    satisfiesClosure I left ↔ satisfiesClosure I right :=
  forall_matching equal (fun a => satisfies I a.axiom) (fun a => satisfies I a.axiom)
    (fun a ma b mb ab => axiom_satisfaction I valid a b ab (leftArity a ma) (rightArity b mb))

/-- The same anonymous assignment witnesses both structurally matching
    standardized-apart closures; no unique-name assumption is introduced. -/
theorem closure_models (I : Interpretation Object Value) (valid : Defaults I)
    (left right : AxiomClosure) (equal : ClosureEq left right)
    (leftArity : Rowl.Arity.ClosureOK left) (rightArity : Rowl.Arity.ClosureOK right) :
    modelsClosure I left ↔ modelsClosure I right :=
  exists_congr (fun assignment => closure_satisfaction (withAnonymous I assignment)
    (defaults_with_anonymous I assignment valid) left right equal leftArity rightArity)

/-- Full model equivalence for each fixed OWL datatype map, embedding and
    vocabulary, allowing arbitrary finite or infinite object and data domains. -/
theorem closure_model {Native : Type w} (D : DatatypeMap Native)
    (embed : ValueEmbedding D Value) (V : Vocabulary) (I : Interpretation Object Value)
    (left right : AxiomClosure) (equal : ClosureEq left right)
    (leftArity : Rowl.Arity.ClosureOK left) (rightArity : Rowl.Arity.ClosureOK right) :
    Model D embed V I left ↔ Model D embed V I right := by
  constructor
  · rintro ⟨vocabulary,interpretation,models⟩
    exact ⟨vocabulary,interpretation,(closure_models I (interpretation_defaults D embed V I interpretation)
      left right equal leftArity rightArity).mp models⟩
  · rintro ⟨vocabulary,interpretation,models⟩
    exact ⟨vocabulary,interpretation,(closure_models I (interpretation_defaults D embed V I interpretation)
      left right equal leftArity rightArity).mpr models⟩

/-- Replacing a closure by structurally matching valid copies preserves existence
    of models across every domain, not merely the finite regression examples. -/
theorem closure_consistency {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (left right : AxiomClosure) (equal : ClosureEq left right)
    (leftArity : Rowl.Arity.ClosureOK left) (rightArity : Rowl.Arity.ClosureOK right) :
    Consistent.{u,v,w} D V left ↔ Consistent.{u,v,w} D V right := by
  constructor
  · rintro ⟨Objects,Values,embed,I,model⟩
    exact ⟨Objects,Values,embed,I,(closure_model D embed V I left right equal leftArity rightArity).mp model⟩
  · rintro ⟨Objects,Values,embed,I,model⟩
    exact ⟨Objects,Values,embed,I,(closure_model D embed V I left right equal leftArity rightArity).mpr model⟩

/-- Source replacement preserves every OWL entailment under the same normative
    map and vocabulary; the theorem does not execute an entailment decision. -/
theorem source_entailment {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (left right target : AxiomClosure) (equal : ClosureEq left right)
    (leftArity : Rowl.Arity.ClosureOK left) (rightArity : Rowl.Arity.ClosureOK right) :
    Entails.{u,v,w} D V left target ↔ Entails.{u,v,w} D V right target := by
  constructor
  · intro entails Objects Values embed I model
    exact entails Objects Values embed I ((closure_model D embed V I left right equal leftArity rightArity).mpr model)
  · intro entails Objects Values embed I model
    exact entails Objects Values embed I ((closure_model D embed V I left right equal leftArity rightArity).mp model)

/-- Target replacement likewise preserves entailment and anonymous assignments. -/
theorem target_entailment {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (source left right : AxiomClosure) (equal : ClosureEq left right)
    (leftArity : Rowl.Arity.ClosureOK left) (rightArity : Rowl.Arity.ClosureOK right) :
    Entails.{u,v,w} D V source left ↔ Entails.{u,v,w} D V source right := by
  constructor
  · intro entails Objects Values embed I model
    exact (closure_model D embed V I left right equal leftArity rightArity).mp (entails Objects Values embed I model)
  · intro entails Objects Values embed I model
    exact (closure_model D embed V I left right equal leftArity rightArity).mpr (entails Objects Values embed I model)


/-- Checked counterexample: raw structural set identity cannot justify erasing
    a repeated disjoint member before the original arity stage. -/
theorem disjoint_duplicates_require_validation :
    ∃ (I : Interpretation Unit Unit) (left right : AnnotatedAxiom), Defaults I ∧
      RowlRust.axiom_equality.same_axiom left right = .ok true ∧
      RowlRust.arity.axiom_allowed left = .ok false ∧
      RowlRust.arity.axiom_allowed right = .ok true ∧
      ¬ satisfiesAnnotated I left ∧ satisfiesAnnotated I right := by
  let empty : alloc.vec.Vec Annotation := alloc.vec.Vec.from [] (by simp)
  let tail : alloc.vec.Vec ClassExpression := alloc.vec.Vec.from [.Class thing] (by simp; scalar_tac)
  let noTail : alloc.vec.Vec ClassExpression := alloc.vec.Vec.from [] (by simp)
  let left : AnnotatedAxiom := ⟨empty,.DisjointClasses ⟨.Class thing,.Class nothing,tail⟩⟩
  let right : AnnotatedAxiom := ⟨empty,.DisjointClasses ⟨.Class thing,.Class nothing,noTail⟩⟩
  refine ⟨Rowl.Owl.Examples.singleton,left,right,?_,?_,?_,?_,?_,?_⟩
  · simp [Defaults,Rowl.Owl.Examples.singleton]
  · rw [Rowl.AxiomEquality.same_axiom_total_correct]
    simp [AxiomEq,BodyEq,ClassSetEq,ClassEq,Rowl.AssertionEquality.AnnotationSetEq,
      left,right,empty,tail,noTail,AtLeastTwo.elements]
  · rw [Rowl.Arity.axiom_allowed_total_correct]
    simp [Rowl.Arity.AxiomAllowed,Rowl.Arity.Unique,Rowl.Arity.ClassAllowed,
      ClassEq,left,empty,tail,AtLeastTwo.elements]
  · rw [Rowl.Arity.axiom_allowed_total_correct]
    simp [Rowl.Arity.AxiomAllowed,Rowl.Arity.Unique,Rowl.Arity.ClassAllowed,
      ClassEq,right,empty,noTail,AtLeastTwo.elements,thing,nothing]
  · simp [satisfiesAnnotated,satisfies,pairwiseDisjoint,left,tail,AtLeastTwo.elements,
      classDenote,Rowl.Owl.Examples.singleton,thing,nothing]
  · simp [satisfiesAnnotated,satisfies,pairwiseDisjoint,right,noTail,AtLeastTwo.elements,
      classDenote,Rowl.Owl.Examples.singleton,thing,nothing]

/-- Checked counterexample: inserting owl:Thing is meaning preserving only
    under the normative interpretation conditions, not arbitrary assignments. -/
theorem object_defaults_require_interpretation :
    ∃ (I : Interpretation Unit Unit) (left right : ClassExpression), ¬ Defaults I ∧
      RowlRust.class_equality.same_class left right = .ok true ∧
      classDenote I left () ∧ ¬ classDenote I right () := by
  let I : Interpretation Unit Unit := { Rowl.Owl.Examples.singleton with classes := fun _ _ => False }
  let n : RowlRust.probes.Natural := .Succ .Zero
  let left : ClassExpression := .ObjectMinCardinality n (.Property topObject) none
  let right : ClassExpression := .ObjectMinCardinality n (.Property topObject) (some (.Class thing))
  refine ⟨I,left,right,?_,?_,?_,?_⟩
  · simp [Defaults,I]
  · rw [Rowl.ClassEquality.same_class_total_correct]
    simp [left,right,ClassEq,IsThing,thing,Rowl.ClassEquality.ThingBytes]
  · simp only [left,n,classDenote,Rowl.Probes.naturalValue]
    change AtLeast 1 (fun y => objectRelation I (.Property topObject) () y ∧ True)
    refine ⟨fun _ => (),?_,?_⟩
    · intro a b _; exact Subsingleton.elim a b
    · intro _; simp [objectRelation,I,Rowl.Owl.Examples.singleton]
  · simp only [right,n,classDenote,dataDenote,Rowl.Probes.naturalValue]
    change ¬ AtLeast 1 (fun y => objectRelation I (.Property topObject) () y ∧ I.classes thing y)
    rintro ⟨f,_,all⟩
    exact (all 0).2

/-- The matching data-default condition is necessary too: the top data range
    must cover every value in the full data domain. -/
theorem data_defaults_require_interpretation :
    ∃ (I : Interpretation Unit Unit) (left right : ClassExpression), ¬ Defaults I ∧
      RowlRust.class_equality.same_class left right = .ok true ∧
      classDenote I left () ∧ ¬ classDenote I right () := by
  let I : Interpretation Unit Unit := { Rowl.Owl.Examples.singleton with datatypes := fun _ _ => False }
  let n : RowlRust.probes.Natural := .Succ .Zero
  let left : ClassExpression := .DataMinCardinality n topData none
  let right : ClassExpression := .DataMinCardinality n topData (some (.Datatype literalDatatype))
  refine ⟨I,left,right,?_,?_,?_,?_⟩
  · simp [Defaults,I]
  · rw [Rowl.ClassEquality.same_class_total_correct]
    simp [left,right,ClassEq,OptionalRangeEq,IsLiteral,literalDatatype,Rowl.ClassEquality.LiteralBytes]
  · simp only [left,n,classDenote,Rowl.Probes.naturalValue]
    change AtLeast 1 (fun y => I.dataProperties topData () y ∧ True)
    refine ⟨fun _ => (),?_,?_⟩
    · intro a b _; exact Subsingleton.elim a b
    · intro _; simp [I,Rowl.Owl.Examples.singleton]
  · simp only [right,n,classDenote,dataDenote,Rowl.Probes.naturalValue]
    change ¬ AtLeast 1 (fun y => I.dataProperties topData () y ∧ I.datatypes literalDatatype y)
    rintro ⟨f,_,all⟩
    exact (all 0).2

end Rowl.StructuralCongruence
