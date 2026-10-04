import Rowl.AlcOntology
import Rowl.Hierarchy

/-!
The class axioms of an axiom closure as the completion graph tableau reads
them, proved against the independent Direct Semantics: a TBox concept that
holds at every element and definitions `A ⊑ C` that hold wherever `A` does.
Every class axiom becomes inclusions. An inclusion whose left side is
absorbable becomes a definition: a named class directly, `∃r.E ⊑ D` as
`E ⊑ ∀r⁻.D`, and `E ⊓ F ⊓ … ⊑ D` as `E ⊑ ¬F ⊔ … ⊔ D`. Every other inclusion
conjoins `¬C ⊔ D` onto the TBox concept, and domains and ranges conjoin
universal restrictions. The parts hold in an interpretation fixing owl:Thing
and owl:Nothing exactly when it satisfies every class axiom of the closure;
they are computed only for supported axioms, and always when every axiom is
supported and the definitions fit in the `usize` range.
-/
namespace Rowl.ShiParts
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation classDenote thing nothing objectRelation)
open Rowl.Nnf (Fixes Polar)
open Rowl.Concepts (denote inv relation_inv Translatable Correct translate_total_correct inverse_correct
  copy_role_identity)
open Rowl.Internalization (Assertion all_equal_iff pairwise_disjoint_iff)
open Rowl.AlcOntology (builtin_class_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v

/-- The axioms the parts support: declarations and annotation axioms, which
    impose nothing; class axioms over translatable class expressions; domains
    and ranges of object property expressions with translatable classes;
    functional, inverse functional, reflexive and irreflexive object property
    expressions, which the TBox concept states; the role axioms and the
    asymmetric and disjoint object properties, which the parts leave to the
    role hierarchy; and assertions, which they leave to the facts and links. -/
def SupportedAxiom : Axiom → Prop
  | .Declaration _ => True
  | .SubClassOf a b => Translatable a ∧ Translatable b
  | .EquivalentClasses xs => ∀ e ∈ xs.elements, Translatable e
  | .DisjointClasses xs => ∀ e ∈ xs.elements, Translatable e
  | .DisjointUnion _ xs => ∀ e ∈ xs.elements, Translatable e
  | .ObjectPropertyDomain _ e => Translatable e
  | .ObjectPropertyRange _ e => Translatable e
  | .FunctionalObjectProperty _ => True
  | .InverseFunctionalObjectProperty _ => True
  | .ReflexiveObjectProperty _ => True
  | .IrreflexiveObjectProperty _ => True
  | .SubObjectPropertyOf (.Single _) _ => True
  | .EquivalentObjectProperties _ => True
  | .InverseObjectProperties _ _ => True
  | .SymmetricObjectProperty _ => True
  | .TransitiveObjectProperty _ => True
  | .AsymmetricObjectProperty _ => True
  | .DisjointObjectProperties _ => True
  | .AnnotationAssertion _ _ _ => True
  | .SubAnnotationPropertyOf _ _ => True
  | .AnnotationPropertyDomain _ _ => True
  | .AnnotationPropertyRange _ _ => True
  | .SameIndividual _ => True
  | .DifferentIndividuals _ => True
  | .ClassAssertion _ _ => True
  | .ObjectPropertyAssertion _ _ _ => True
  | .NegativeObjectPropertyAssertion _ _ _ => True
  | _ => False

/-- The role axioms the role hierarchy reads: inclusions without chains,
    equivalences, inverses, symmetry and transitivity of object property
    expressions. -/
def RoleAxiom : Axiom → Prop
  | .SubObjectPropertyOf (.Single _) _ => True
  | .EquivalentObjectProperties _ => True
  | .InverseObjectProperties _ _ => True
  | .SymmetricObjectProperty _ => True
  | .TransitiveObjectProperty _ => True
  | _ => False

/-- The asymmetric and disjoint object properties, which the role hierarchy
    keeps as disjoint pairs. -/
def ConstraintAxiom : Axiom → Prop
  | .AsymmetricObjectProperty _ => True
  | .DisjointObjectProperties _ => True
  | _ => False

/-- A bound on the definitions an axiom adds: at most one per inclusion it
    becomes. -/
def Inclusions : Axiom → Nat
  | .SubClassOf _ _ => 1
  | .EquivalentClasses xs => 2 * xs.elements.length
  | .DisjointClasses xs => xs.elements.length * xs.elements.length
  | .DisjointUnion _ xs => 1 + xs.elements.length + xs.elements.length * xs.elements.length
  | _ => 0

variable {Object : Type u} {Value : Type v}

/-- The individual equalities and inequalities, which the individuals' nodes
    decide. -/
def Equality : Axiom → Prop
  | .SameIndividual _ => True
  | .DifferentIndividuals _ => True
  | _ => False

/-- What an axiom requires of every element: nothing for an assertion, an
    equality or inequality, a role axiom or an asymmetric or disjoint object
    property, the axiom itself otherwise. -/
def ClassPart (I : Interpretation Object Value) (a : Axiom) : Prop :=
  Assertion a ∨ Equality a ∨ RoleAxiom a ∨ ConstraintAxiom a ∨ Rowl.Owl.satisfies I a

/-- The parts hold: the TBox concept at every element, and every definition
    wherever its class holds. -/
def PartsHold (I : Interpretation Object Value) (parts : shi_ontology.Parts) : Prop :=
  (∀ x, denote I parts.axioms x) ∧
  ∀ d ∈ parts.definitions.val, ∀ x, I.classes d.class x → denote I d.concept x

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

private theorem first_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.first < sizeOf xs := by
  cases xs; simp +arith

theorem copy_iri_class (c : Class) : ({ iri := c.iri } : Class) = c := by
  cases c; rfl

/-- The absorbability test always terminates. -/
theorem absorbable_total (sub : ClassExpression) : ∃ b, shi_ontology.absorbable sub = .ok b := by
  cases h : sub with
  | Class c =>
    refine ⟨decide ¬(c = thing ∨ c = nothing),?_⟩
    rw [shi_ontology.absorbable]
    simp [builtin_class_correct]
  | ObjectIntersectionOf xs =>
    obtain ⟨b,run⟩ := absorbable_total xs.first
    exact ⟨b,by rw [shi_ontology.absorbable]; exact run⟩
  | ObjectSomeValuesFrom r e =>
    obtain ⟨b,run⟩ := absorbable_total e
    exact ⟨b,by rw [shi_ontology.absorbable]; exact run⟩
  | ObjectUnionOf _ | ObjectComplementOf _ | ObjectOneOf _ | ObjectAllValuesFrom _ _ | ObjectHasValue _ _
  | ObjectHasSelf _ | ObjectMinCardinality _ _ _ | ObjectMaxCardinality _ _ _ | ObjectExactCardinality _ _ _
  | DataSomeValuesFrom _ _ | DataAllValuesFrom _ _ | DataHasValue _ _ | DataMinCardinality _ _ _
  | DataMaxCardinality _ _ _ | DataExactCardinality _ _ _ =>
    exact ⟨false,by rw [shi_ontology.absorbable]⟩
termination_by sizeOf sub
decreasing_by
  all_goals simp only [h,ClassExpression.ObjectIntersectionOf.sizeOf_spec,
    ClassExpression.ObjectSomeValuesFrom.sizeOf_spec]
  · have := first_size xs; omega
  · omega

/-- Joining complements: `joined ⊔ ¬values[index] ⊔ …` fails exactly outside
    ALCI and otherwise holds where `joined` does or some class from `index` on
    does not. -/
theorem fail_from_correct (values : alloc.vec.Vec ClassExpression) (index : Usize) (joined : concepts.Concept) :
    ∃ r, shi_ontology.fail_from values index joined = .ok r ∧
      (r.isSome ↔ ∀ e ∈ values.val.drop index.val, Translatable e) ∧
      ∀ c, r = some c → ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
        ∀ x, (denote I c x ↔ denote I joined x ∨ ∃ e ∈ values.val.drop index.val, ¬ classDenote I e x) := by
  rw [shi_ontology.fail_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨t,tRun,tCorrect⟩ := translate_total_correct.{u,v} values.val[index.val] false
    cases t with
    | none =>
      refine ⟨none,by simp [more,lookup,tRun],?_,by simp⟩
      simp only [Correct] at tCorrect
      simp only [Option.isSome_none,Bool.false_eq_true,false_iff]
      intro every
      exact tCorrect (every _ (by rw [split]; exact List.mem_cons_self ..))
    | some outside =>
      obtain ⟨rest,restRun,restSupport,restMeaning⟩ := fail_from_correct values next (.Or joined outside)
      refine ⟨rest,by simp [more,lookup,tRun,advance,restRun],?_,?_⟩
      · rw [restSupport,nextIndex,split,List.forall_mem_cons]
        exact ⟨fun later => ⟨tCorrect.1,later⟩,fun every => every.2⟩
      · intro c same Object Value I fixes x
        rw [restMeaning c same Object Value I fixes x,split,nextIndex]
        have here := tCorrect.2 Object Value I fixes x
        simp only [denote,here,Polar,List.mem_cons,exists_eq_or_imp]
        tauto
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some joined,by simp [more],by simp [empty],?_⟩
    intro c same Object Value I fixes x
    cases same
    simp [empty]
termination_by values.val.length - index.val
decreasing_by all_goals omega

/-- Absorption: the definition holds exactly when the inclusion `sub ⊑ sup`
    does, and for an absorbable `sub` it is computed exactly on ALCI. -/
theorem absorb_correct (sub : ClassExpression) (sup : concepts.Concept) :
    ∃ r, shi_ontology.absorb sub sup = .ok r ∧
      (shi_ontology.absorbable sub = .ok true → (r.isSome ↔ Translatable sub)) ∧
      ∀ d, r = some d → ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
        ((∀ x, I.classes d.class x → denote I d.concept x) ↔ (∀ x, classDenote I sub x → denote I sup x)) := by
  cases h : sub with
  | Class c =>
    refine ⟨some ⟨c,sup⟩,?_,?_,?_⟩
    · rw [shi_ontology.absorb]
      simp [Rowl.Nnf.copy_iri_identity]
    · intro _
      simp [Translatable]
    · intro d same Object Value I fixes
      cases same
      simp [classDenote]
  | ObjectIntersectionOf xs =>
    obtain ⟨second,secondRun,secondCorrect⟩ := translate_total_correct.{u,v} xs.second false
    cases second with
    | none =>
      refine ⟨none,by rw [shi_ontology.absorb]; simp [secondRun],?_,by simp⟩
      intro _
      simp only [Correct] at secondCorrect
      simp [Translatable,secondCorrect]
    | some secondConcept =>
      obtain ⟨others,othersRun,othersSupport,othersMeaning⟩ :=
        fail_from_correct.{u,v} xs.rest 0#usize secondConcept
      cases others with
      | none =>
        refine ⟨none,by rw [shi_ontology.absorb]; simp [secondRun,othersRun],?_,by simp⟩
        intro _
        simp only [Option.isSome_none,Bool.false_eq_true,false_iff] at othersSupport
        simp [Translatable]
        intro _ _
        simpa using othersSupport
      | some othersConcept =>
        obtain ⟨r,run,support,meaning⟩ := absorb_correct xs.first (.Or othersConcept sup)
        refine ⟨r,by rw [shi_ontology.absorb]; simp [secondRun,othersRun,run],?_,?_⟩
        · intro absorbableRun
          have firstRun : shi_ontology.absorbable xs.first = .ok true := by
            rw [shi_ontology.absorbable] at absorbableRun
            exact absorbableRun
          have restIn : ∀ e ∈ xs.rest.val, Translatable e := by simpa using othersSupport.mp rfl
          have fragment : Translatable (.ObjectIntersectionOf xs) ↔ ∀ e ∈ xs.elements, Translatable e := by
            simp [Translatable,AtLeastTwo.elements]
          rw [support firstRun,fragment]
          simp only [AtLeastTwo.elements,List.forall_mem_cons]
          exact ⟨fun first => ⟨first,secondCorrect.1,restIn⟩,fun every => every.1⟩
        · intro d same Object Value I fixes
          rw [meaning d same Object Value I fixes]
          apply forall_congr'
          intro x
          have zero : (0#usize).val = 0 := rfl
          have othersAt := othersMeaning othersConcept rfl Object Value I fixes x
          have secondAt := secondCorrect.2 Object Value I fixes x
          rw [zero,List.drop_zero] at othersAt
          have intersection : classDenote I (.ObjectIntersectionOf xs) x ↔
              classDenote I xs.first x ∧ classDenote I xs.second x ∧ ∀ e ∈ xs.rest.val, classDenote I e x := by
            simp [classDenote]
          have swap : (∃ e ∈ xs.rest.val, ¬ classDenote I e x) ↔ ¬ ∀ e ∈ xs.rest.val, classDenote I e x := by
            simp only [not_forall,Classical.not_imp,exists_prop]
          simp only [denote,othersAt,secondAt,Polar,intersection,swap]
          tauto
  | ObjectSomeValuesFrom r e =>
    obtain ⟨res,run,support,meaning⟩ := absorb_correct e (.Forall (inv r) sup)
    refine ⟨res,by rw [shi_ontology.absorb]; simp [inverse_correct,run],?_,?_⟩
    · intro absorbableRun
      rw [shi_ontology.absorbable] at absorbableRun
      rw [support absorbableRun]
      simp [Translatable]
    · intro d same Object Value I fixes
      rw [meaning d same Object Value I fixes]
      simp only [denote,relation_inv]
      rw [show (∀ x, classDenote I (.ObjectSomeValuesFrom r e) x → denote I sup x) ↔
          (∀ x, (∃ y, objectRelation I r x y ∧ classDenote I e y) → denote I sup x) by
        simp only [classDenote]]
      constructor
      · rintro every x ⟨y,edge,holds⟩
        exact every y holds x edge
      · intro every y holds x edge
        exact every x ⟨y,edge,holds⟩
  | ObjectUnionOf _ | ObjectComplementOf _ | ObjectOneOf _ | ObjectAllValuesFrom _ _ | ObjectHasValue _ _
  | ObjectHasSelf _ | ObjectMinCardinality _ _ _ | ObjectMaxCardinality _ _ _ | ObjectExactCardinality _ _ _
  | DataSomeValuesFrom _ _ | DataAllValuesFrom _ _ | DataHasValue _ _ | DataMinCardinality _ _ _
  | DataMaxCardinality _ _ _ | DataExactCardinality _ _ _ =>
    refine ⟨none,by rw [shi_ontology.absorb],?_,by simp⟩
    intro absorbableRun
    rw [shi_ontology.absorbable] at absorbableRun
    exact absurd (Result.ok_injective absorbableRun) Bool.false_ne_true
termination_by sizeOf sub
decreasing_by
  all_goals simp only [h,ClassExpression.ObjectIntersectionOf.sizeOf_spec,
    ClassExpression.ObjectSomeValuesFrom.sizeOf_spec]
  · have := first_size xs; omega
  · omega

/-- An inclusion `sub ⊑ sup`: afterwards the parts hold exactly when they held
    before and the inclusion holds. It is added exactly on ALCI while the
    definitions fit, and adds at most one definition. -/
theorem include_correct (sub : ClassExpression) (sup : concepts.Concept) (parts : shi_ontology.Parts) :
    ∃ r, shi_ontology.include sub sup parts = .ok r ∧
      (r.isSome → Translatable sub) ∧
      (Translatable sub → parts.definitions.val.length < Usize.max → r.isSome) ∧
      ∀ parts', r = some parts' → parts'.definitions.val.length ≤ parts.definitions.val.length + 1 ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
          (PartsHold I parts' ↔ PartsHold I parts ∧ ∀ x, classDenote I sub x → denote I sup x) := by
  obtain ⟨b,absorbableRun⟩ := absorbable_total sub
  rw [shi_ontology.include]
  cases b with
  | true =>
    obtain ⟨r,run,support,meaning⟩ := absorb_correct.{u,v} sub sup
    have supportIff := support absorbableRun
    cases r with
    | none =>
      refine ⟨none,by simp [absorbableRun,run],by simp,?_,by simp⟩
      intro inside _
      exact absurd (supportIff.mpr inside) (by simp)
    | some d =>
      by_cases fits : parts.definitions.val.length < Usize.max
      · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec parts.definitions d fits)
        refine ⟨some {parts with definitions := appended},by simp [absorbableRun,run,usize_max_val,fits,push],
          fun _ => supportIff.mp rfl,fun _ _ => rfl,?_⟩
        intro parts' same
        cases same
        refine ⟨by simp [contents],?_⟩
        intro Object Value I fixes
        have definition := meaning d rfl Object Value I fixes
        simp only [PartsHold,contents,List.mem_append,List.mem_singleton]
        rw [← definition]
        constructor
        · rintro ⟨tbox,defs⟩
          exact ⟨⟨tbox,fun e member => defs e (.inl member)⟩,defs d (.inr rfl)⟩
        · rintro ⟨⟨tbox,defs⟩,new⟩
          refine ⟨tbox,?_⟩
          rintro e (old | rfl)
          · exact defs e old
          · exact new
      · refine ⟨none,by simp [absorbableRun,run,usize_max_val,fits],by simp,?_,by simp⟩
        intro _ fitsNow
        exact absurd fitsNow fits
  | false =>
    obtain ⟨t,tRun,tCorrect⟩ := translate_total_correct.{u,v} sub false
    cases t with
    | none =>
      refine ⟨none,by simp [absorbableRun,tRun],by simp,?_,by simp⟩
      intro inside _
      simp only [Correct] at tCorrect
      exact absurd inside tCorrect
    | some outside =>
      refine ⟨some {parts with axioms := .And parts.axioms (.Or outside sup)},by simp [absorbableRun,tRun],
        fun _ => tCorrect.1,fun _ _ => rfl,?_⟩
      intro parts' same
      cases same
      refine ⟨by simp,?_⟩
      intro Object Value I fixes
      have meaningOf := tCorrect.2 Object Value I fixes
      simp only [Polar] at meaningOf
      simp only [PartsHold,denote,meaningOf]
      constructor
      · rintro ⟨every,defs⟩
        exact ⟨⟨fun x => (every x).1,defs⟩,fun x holds => (every x).2.resolve_left (not_not.mpr holds)⟩
      · rintro ⟨⟨tbox,defs⟩,inclusion⟩
        refine ⟨fun x => ⟨tbox x,?_⟩,defs⟩
        by_cases holds : classDenote I sub x
        · exact .inr (inclusion x holds)
        · exact .inl holds

/-- Both inclusions between two classes: afterwards the parts hold exactly when
    they held before and the classes are equivalent. -/
theorem include_both_correct (left right : ClassExpression) (parts : shi_ontology.Parts) :
    ∃ r, shi_ontology.include_both left right parts = .ok r ∧
      (r.isSome → Translatable left ∧ Translatable right) ∧
      (Translatable left → Translatable right → parts.definitions.val.length + 2 ≤ Usize.max → r.isSome) ∧
      ∀ parts', r = some parts' → parts'.definitions.val.length ≤ parts.definitions.val.length + 2 ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
          (PartsHold I parts' ↔ PartsHold I parts ∧ ∀ x, (classDenote I left x ↔ classDenote I right x)) := by
  rw [shi_ontology.include_both]
  obtain ⟨forward,forwardRun,forwardCorrect⟩ := translate_total_correct.{u,v} right true
  cases forward with
  | none =>
    refine ⟨none,by simp [forwardRun],by simp,?_,by simp⟩
    intro _ inside _
    simp only [Correct] at forwardCorrect
    exact absurd inside forwardCorrect
  | some forwardConcept =>
    obtain ⟨first,firstRun,firstSupport,firstTotal,firstSpec⟩ := include_correct.{u,v} left forwardConcept parts
    cases first with
    | none =>
      refine ⟨none,by simp [forwardRun,firstRun],by simp,?_,by simp⟩
      intro inside _ fits
      exact absurd (firstTotal inside (by omega)) (by simp)
    | some parts1 =>
      obtain ⟨firstCount,firstMeaning⟩ := firstSpec parts1 rfl
      obtain ⟨backward,backwardRun,backwardCorrect⟩ := translate_total_correct.{u,v} left true
      cases backward with
      | none =>
        simp only [Correct] at backwardCorrect
        exact absurd (firstSupport rfl) backwardCorrect
      | some backwardConcept =>
        obtain ⟨second,secondRun,secondSupport,secondTotal,secondSpec⟩ :=
          include_correct.{u,v} right backwardConcept parts1
        refine ⟨second,by simp [forwardRun,firstRun,backwardRun,secondRun],?_,?_,?_⟩
        · intro some
          exact ⟨firstSupport rfl,secondSupport some⟩
        · intro _ inside fits
          exact secondTotal inside (by omega)
        · intro parts' same
          obtain ⟨secondCount,secondMeaning⟩ := secondSpec parts' same
          refine ⟨by omega,?_⟩
          intro Object Value I fixes
          rw [secondMeaning Object Value I fixes,firstMeaning Object Value I fixes]
          have forwardAt := forwardCorrect.2 Object Value I fixes
          have backwardAt := backwardCorrect.2 Object Value I fixes
          simp only [Polar] at forwardAt backwardAt
          simp only [forwardAt,backwardAt]
          constructor
          · rintro ⟨⟨before,there⟩,back⟩
            exact ⟨before,fun x => ⟨there x,back x⟩⟩
          · rintro ⟨before,same⟩
            exact ⟨⟨before,fun x => (same x).mp⟩,fun x => (same x).mpr⟩

/-- Equivalence with the first member, member by member. -/
theorem equal_from_correct (first : ClassExpression) (values : alloc.vec.Vec ClassExpression) (index : Usize)
    (parts : shi_ontology.Parts) :
    ∃ r, shi_ontology.equal_from first values index parts = .ok r ∧
      (r.isSome → ∀ e ∈ values.val.drop index.val, Translatable first ∧ Translatable e) ∧
      (Translatable first → (∀ e ∈ values.val.drop index.val, Translatable e) →
        parts.definitions.val.length + 2 * (values.val.length - index.val) ≤ Usize.max → r.isSome) ∧
      ∀ parts', r = some parts' →
        parts'.definitions.val.length ≤ parts.definitions.val.length + 2 * (values.val.length - index.val) ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
          (PartsHold I parts' ↔ PartsHold I parts ∧
            ∀ e ∈ values.val.drop index.val, ∀ x, (classDenote I first x ↔ classDenote I e x)) := by
  rw [shi_ontology.equal_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨both,bothRun,bothSupport,bothTotal,bothSpec⟩ :=
      include_both_correct.{u,v} first values.val[index.val] parts
    cases both with
    | none =>
      refine ⟨none,by simp [more,lookup,bothRun],by simp,?_,by simp⟩
      intro inside every fits
      exact absurd (bothTotal inside (every _ (by rw [split]; exact List.mem_cons_self ..)) (by omega)) (by simp)
    | some parts1 =>
      obtain ⟨bothCount,bothMeaning⟩ := bothSpec parts1 rfl
      obtain ⟨rest,restRun,restSupport,restTotal,restSpec⟩ := equal_from_correct first values next parts1
      rw [nextIndex] at restSupport restTotal restSpec
      refine ⟨rest,by simp [more,lookup,bothRun,advance,restRun],?_,?_,?_⟩
      · intro some e member
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · exact bothSupport rfl
        · exact restSupport some e later
      · intro inside every fits
        apply restTotal inside (fun e member => every e (by rw [split]; exact List.mem_cons_of_mem _ member))
        omega
      · intro parts' same
        obtain ⟨restCount,restMeaning⟩ := restSpec parts' same
        refine ⟨by omega,?_⟩
        intro Object Value I fixes
        rw [restMeaning Object Value I fixes,bothMeaning Object Value I fixes,split]
        simp only [List.forall_mem_cons]
        tauto
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some parts,by simp [more],by simp [empty],by simp,?_⟩
    intro parts' same
    cases same
    exact ⟨by omega,fun Object Value I fixes => by simp [empty]⟩
termination_by values.val.length - index.val
decreasing_by all_goals omega

/-- Equivalent classes hold at each element all together or not at all,
    exactly when each member is equivalent to the first. -/
theorem all_equal_star {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (first : ClassExpression) (others : List ClassExpression) :
    Rowl.Owl.allEqual (first :: others) (classDenote I) ↔
      ∀ e ∈ others, ∀ x, (classDenote I first x ↔ classDenote I e x) := by
  rw [all_equal_iff]
  constructor
  · intro split e member x
    rcases split x with every | none
    · exact ⟨fun _ => every e (List.mem_cons_of_mem _ member),fun _ => every first (List.mem_cons_self ..)⟩
    · exact ⟨fun holds => absurd holds (none first (List.mem_cons_self ..)),
        fun holds => absurd holds (none e (List.mem_cons_of_mem _ member))⟩
  · intro same x
    by_cases holds : classDenote I first x
    · left
      intro e member
      rcases List.mem_cons.mp member with rfl | later
      · exact holds
      · exact (same e later x).mp holds
    · right
      intro e member
      rcases List.mem_cons.mp member with rfl | later
      · exact holds
      · exact fun other => holds ((same e later x).mpr other)

/-- Equivalent classes: afterwards the parts hold exactly when they held before
    and the members are equivalent. -/
theorem equivalent_correct (members : AtLeastTwo ClassExpression) (parts : shi_ontology.Parts) :
    ∃ r, shi_ontology.equivalent members parts = .ok r ∧
      (r.isSome → ∀ e ∈ members.elements, Translatable e) ∧
      ((∀ e ∈ members.elements, Translatable e) →
        parts.definitions.val.length + 2 * members.elements.length ≤ Usize.max → r.isSome) ∧
      ∀ parts', r = some parts' →
        parts'.definitions.val.length ≤ parts.definitions.val.length + 2 * members.elements.length ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
          (PartsHold I parts' ↔ PartsHold I parts ∧ Rowl.Owl.allEqual members.elements (classDenote I)) := by
  have zero : (0#usize).val = 0 := rfl
  have length : members.elements.length = members.rest.val.length + 2 := by
    simp [AtLeastTwo.elements]
  rw [shi_ontology.equivalent]
  obtain ⟨both,bothRun,bothSupport,bothTotal,bothSpec⟩ :=
    include_both_correct.{u,v} members.first members.second parts
  cases both with
  | none =>
    refine ⟨none,by simp [bothRun],by simp,?_,by simp⟩
    intro every fits
    exact absurd (bothTotal (every _ (by simp [AtLeastTwo.elements])) (every _ (by simp [AtLeastTwo.elements]))
      (by omega)) (by simp)
  | some parts1 =>
    obtain ⟨bothCount,bothMeaning⟩ := bothSpec parts1 rfl
    obtain ⟨rest,restRun,restSupport,restTotal,restSpec⟩ :=
      equal_from_correct.{u,v} members.first members.rest 0#usize parts1
    rw [zero,List.drop_zero] at restSupport restTotal restSpec
    refine ⟨rest,by simp [bothRun,restRun],?_,?_,?_⟩
    · intro some e member
      simp only [AtLeastTwo.elements,List.mem_cons] at member
      rcases member with rfl | rfl | later
      · exact (bothSupport rfl).1
      · exact (bothSupport rfl).2
      · exact (restSupport some e later).2
    · intro every fits
      apply restTotal (every _ (by simp [AtLeastTwo.elements]))
        (fun e member => every e (by simp [AtLeastTwo.elements,member]))
      omega
    · intro parts' same
      obtain ⟨restCount,restMeaning⟩ := restSpec parts' same
      refine ⟨by omega,?_⟩
      intro Object Value I fixes
      rw [restMeaning Object Value I fixes,bothMeaning Object Value I fixes]
      simp only [AtLeastTwo.elements]
      rw [all_equal_star,List.forall_mem_cons]
      tauto

/-- Disjointness of a member from the classes `values[index..]`. -/
theorem apart_from_correct (member : ClassExpression) (values : alloc.vec.Vec ClassExpression) (index : Usize)
    (parts : shi_ontology.Parts) :
    ∃ r, shi_ontology.apart_from member values index parts = .ok r ∧
      (r.isSome → ∀ e ∈ values.val.drop index.val, Translatable member ∧ Translatable e) ∧
      (Translatable member → (∀ e ∈ values.val.drop index.val, Translatable e) →
        parts.definitions.val.length + (values.val.length - index.val) ≤ Usize.max → r.isSome) ∧
      ∀ parts', r = some parts' →
        parts'.definitions.val.length ≤ parts.definitions.val.length + (values.val.length - index.val) ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
          (PartsHold I parts' ↔ PartsHold I parts ∧
            ∀ e ∈ values.val.drop index.val, ∀ x, ¬ (classDenote I member x ∧ classDenote I e x)) := by
  rw [shi_ontology.apart_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨t,tRun,tCorrect⟩ := translate_total_correct.{u,v} values.val[index.val] false
    cases t with
    | none =>
      refine ⟨none,by simp [more,lookup,tRun],by simp,?_,by simp⟩
      intro _ every _
      simp only [Correct] at tCorrect
      exact absurd (every _ (by rw [split]; exact List.mem_cons_self ..)) tCorrect
    | some outside =>
      obtain ⟨here,hereRun,hereSupport,hereTotal,hereSpec⟩ := include_correct.{u,v} member outside parts
      cases here with
      | none =>
        refine ⟨none,by simp [more,lookup,tRun,hereRun],by simp,?_,by simp⟩
        intro inside _ fits
        exact absurd (hereTotal inside (by omega)) (by simp)
      | some parts1 =>
        obtain ⟨hereCount,hereMeaning⟩ := hereSpec parts1 rfl
        obtain ⟨rest,restRun,restSupport,restTotal,restSpec⟩ := apart_from_correct member values next parts1
        rw [nextIndex] at restSupport restTotal restSpec
        refine ⟨rest,by simp [more,lookup,tRun,hereRun,advance,restRun],?_,?_,?_⟩
        · intro some e found
          rw [split] at found
          rcases List.mem_cons.mp found with rfl | later
          · exact ⟨hereSupport rfl,tCorrect.1⟩
          · exact restSupport some e later
        · intro inside every fits
          apply restTotal inside (fun e found => every e (by rw [split]; exact List.mem_cons_of_mem _ found))
          omega
        · intro parts' same
          obtain ⟨restCount,restMeaning⟩ := restSpec parts' same
          refine ⟨by omega,?_⟩
          intro Object Value I fixes
          have outsideAt := tCorrect.2 Object Value I fixes
          simp only [Polar] at outsideAt
          rw [restMeaning Object Value I fixes,hereMeaning Object Value I fixes,split]
          simp only [List.forall_mem_cons,outsideAt]
          have apart : (∀ x, classDenote I member x → ¬ classDenote I values.val[index.val] x) ↔
              ∀ x, ¬ (classDenote I member x ∧ classDenote I values.val[index.val] x) :=
            forall_congr' fun x => ⟨fun h ⟨a,b⟩ => h a b,fun h a b => h ⟨a,b⟩⟩
          rw [apart]
          tauto
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some parts,by simp [more],by simp [empty],by simp,?_⟩
    intro parts' same
    cases same
    exact ⟨by omega,fun Object Value I fixes => by simp [empty]⟩
termination_by values.val.length - index.val
decreasing_by all_goals omega

/-- Pairwise disjointness of the classes `values[index..]`. -/
theorem pairwise_from_correct (values : alloc.vec.Vec ClassExpression) (index : Usize)
    (parts : shi_ontology.Parts) :
    ∃ r, shi_ontology.pairwise_from values index parts = .ok r ∧
      ((∀ e ∈ values.val.drop index.val, Translatable e) →
        parts.definitions.val.length + (values.val.length - index.val) * (values.val.length - index.val) ≤
          Usize.max → r.isSome) ∧
      ∀ parts', r = some parts' →
        parts'.definitions.val.length ≤
          parts.definitions.val.length + (values.val.length - index.val) * (values.val.length - index.val) ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
          (PartsHold I parts' ↔ PartsHold I parts ∧
            (values.val.drop index.val).Pairwise (fun a b => ∀ x, ¬ (classDenote I a x ∧ classDenote I b x))) := by
  rw [shi_ontology.pairwise_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨here,hereRun,_,hereTotal,hereSpec⟩ := apart_from_correct.{u,v} values.val[index.val] values next parts
    rw [nextIndex] at hereTotal hereSpec
    have square : (values.val.length - (index.val+1)) + (values.val.length - (index.val+1)) *
        (values.val.length - (index.val+1)) ≤ (values.val.length - index.val) * (values.val.length - index.val) := by
      have : values.val.length - index.val = (values.val.length - (index.val+1)) + 1 := by omega
      rw [this]
      nlinarith
    cases here with
    | none =>
      refine ⟨none,by simp [more,lookup,advance,hereRun],?_,by simp⟩
      intro every fits
      rw [split] at every
      exact absurd (hereTotal (every _ (List.mem_cons_self ..)) (fun e member => every e (List.mem_cons_of_mem _ member))
        (by omega)) (by simp)
    | some parts1 =>
      obtain ⟨hereCount,hereMeaning⟩ := hereSpec parts1 rfl
      obtain ⟨rest,restRun,restTotal,restSpec⟩ := pairwise_from_correct values next parts1
      rw [nextIndex] at restTotal restSpec
      refine ⟨rest,by simp [more,lookup,advance,hereRun,restRun],?_,?_⟩
      · intro every fits
        rw [split] at every
        apply restTotal (fun e member => every e (List.mem_cons_of_mem _ member))
        omega
      · intro parts' same
        obtain ⟨restCount,restMeaning⟩ := restSpec parts' same
        refine ⟨by omega,?_⟩
        intro Object Value I fixes
        rw [restMeaning Object Value I fixes,hereMeaning Object Value I fixes,split,List.pairwise_cons]
        tauto
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some parts,by simp [more],by simp,?_⟩
    intro parts' same
    cases same
    exact ⟨by omega,fun Object Value I fixes => by simp [empty]⟩
termination_by values.val.length - index.val
decreasing_by all_goals omega

/-- Disjoint classes: afterwards the parts hold exactly when they held before
    and the members are pairwise disjoint. -/
theorem disjoint_correct (members : AtLeastTwo ClassExpression) (parts : shi_ontology.Parts) :
    ∃ r, shi_ontology.disjoint members parts = .ok r ∧
      (r.isSome → ∀ e ∈ members.elements, Translatable e) ∧
      ((∀ e ∈ members.elements, Translatable e) →
        parts.definitions.val.length + members.elements.length * members.elements.length ≤ Usize.max →
          r.isSome) ∧
      ∀ parts', r = some parts' →
        parts'.definitions.val.length ≤
          parts.definitions.val.length + members.elements.length * members.elements.length ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
          (PartsHold I parts' ↔ PartsHold I parts ∧ Rowl.Owl.pairwiseDisjoint members.elements (classDenote I)) := by
  have zero : (0#usize).val = 0 := rfl
  have length : members.elements.length = members.rest.val.length + 2 := by
    simp [AtLeastTwo.elements]
  have firstIn : members.first ∈ members.elements := by simp [AtLeastTwo.elements]
  have secondIn : members.second ∈ members.elements := by simp [AtLeastTwo.elements]
  have restIn : ∀ e ∈ members.rest.val, e ∈ members.elements := fun e member => by
    simp [AtLeastTwo.elements,member]
  have bound : 1 + members.rest.val.length + members.rest.val.length +
      members.rest.val.length * members.rest.val.length ≤ members.elements.length * members.elements.length := by
    rw [length]
    nlinarith
  rw [shi_ontology.disjoint]
  obtain ⟨second,secondRun,secondCorrect⟩ := translate_total_correct.{u,v} members.second false
  cases second with
  | none =>
    refine ⟨none,by simp [secondRun],by simp,?_,by simp⟩
    intro every _
    simp only [Correct] at secondCorrect
    exact absurd (every _ secondIn) secondCorrect
  | some secondConcept =>
    obtain ⟨one,oneRun,oneSupport,oneTotal,oneSpec⟩ := include_correct.{u,v} members.first secondConcept parts
    cases one with
    | none =>
      refine ⟨none,by simp [secondRun,oneRun],by simp,?_,by simp⟩
      intro every fits
      exact absurd (oneTotal (every _ firstIn) (by omega)) (by simp)
    | some parts1 =>
      obtain ⟨oneCount,oneMeaning⟩ := oneSpec parts1 rfl
      obtain ⟨two,twoRun,twoSupport,twoTotal,twoSpec⟩ :=
        apart_from_correct.{u,v} members.first members.rest 0#usize parts1
      rw [zero,List.drop_zero] at twoSupport twoTotal twoSpec
      cases two with
      | none =>
        refine ⟨none,by simp [secondRun,oneRun,twoRun],by simp,?_,by simp⟩
        intro every fits
        exact absurd (twoTotal (every _ firstIn) (fun e member => every e (restIn e member)) (by omega)) (by simp)
      | some parts2 =>
        obtain ⟨twoCount,twoMeaning⟩ := twoSpec parts2 rfl
        obtain ⟨three,threeRun,threeSupport,threeTotal,threeSpec⟩ :=
          apart_from_correct.{u,v} members.second members.rest 0#usize parts2
        rw [zero,List.drop_zero] at threeSupport threeTotal threeSpec
        cases three with
        | none =>
          refine ⟨none,by simp [secondRun,oneRun,twoRun,threeRun],by simp,?_,by simp⟩
          intro every fits
          exact absurd (threeTotal (every _ secondIn) (fun e member => every e (restIn e member)) (by omega))
            (by simp)
        | some parts3 =>
          obtain ⟨threeCount,threeMeaning⟩ := threeSpec parts3 rfl
          obtain ⟨four,fourRun,fourTotal,fourSpec⟩ := pairwise_from_correct.{u,v} members.rest 0#usize parts3
          rw [zero,List.drop_zero,Nat.sub_zero] at fourTotal fourSpec
          refine ⟨four,by simp [secondRun,oneRun,twoRun,threeRun,fourRun],?_,?_,?_⟩
          · intro _ e member
            simp only [AtLeastTwo.elements,List.mem_cons] at member
            rcases member with rfl | rfl | later
            · exact oneSupport rfl
            · exact secondCorrect.1
            · exact (twoSupport rfl e later).2
          · intro every fits
            apply fourTotal (fun e member => every e (restIn e member))
            omega
          · intro parts' same
            obtain ⟨fourCount,fourMeaning⟩ := fourSpec parts' same
            refine ⟨by omega,?_⟩
            intro Object Value I fixes
            have secondAt := secondCorrect.2 Object Value I fixes
            simp only [Polar] at secondAt
            rw [fourMeaning Object Value I fixes,threeMeaning Object Value I fixes,twoMeaning Object Value I fixes,
              oneMeaning Object Value I fixes]
            unfold Rowl.Owl.pairwiseDisjoint
            simp only [AtLeastTwo.elements,List.pairwise_cons,List.forall_mem_cons,secondAt]
            have apart : (∀ x, classDenote I members.first x → ¬ classDenote I members.second x) ↔
                ∀ x, ¬ (classDenote I members.first x ∧ classDenote I members.second x) :=
              forall_congr' fun x => ⟨fun h ⟨a,b⟩ => h a b,fun h a b => h ⟨a,b⟩⟩
            rw [apart]
            tauto

/-- Joining classes: `joined ⊔ values[index] ⊔ …` fails exactly outside ALCI
    and otherwise holds where `joined` or some class from `index` on does. -/
theorem some_from_correct (values : alloc.vec.Vec ClassExpression) (index : Usize) (joined : concepts.Concept) :
    ∃ r, shi_ontology.some_from values index joined = .ok r ∧
      (r.isSome ↔ ∀ e ∈ values.val.drop index.val, Translatable e) ∧
      ∀ c, r = some c → ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
        ∀ x, (denote I c x ↔ denote I joined x ∨ ∃ e ∈ values.val.drop index.val, classDenote I e x) := by
  rw [shi_ontology.some_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨t,tRun,tCorrect⟩ := translate_total_correct.{u,v} values.val[index.val] true
    cases t with
    | none =>
      refine ⟨none,by simp [more,lookup,tRun],?_,by simp⟩
      simp only [Correct] at tCorrect
      simp only [Option.isSome_none,Bool.false_eq_true,false_iff]
      intro every
      exact tCorrect (every _ (by rw [split]; exact List.mem_cons_self ..))
    | some inside =>
      obtain ⟨rest,restRun,restSupport,restMeaning⟩ := some_from_correct values next (.Or joined inside)
      refine ⟨rest,by simp [more,lookup,tRun,advance,restRun],?_,?_⟩
      · rw [restSupport,nextIndex,split,List.forall_mem_cons]
        exact ⟨fun later => ⟨tCorrect.1,later⟩,fun every => every.2⟩
      · intro c same Object Value I fixes x
        rw [restMeaning c same Object Value I fixes x,split,nextIndex]
        have here := tCorrect.2 Object Value I fixes x
        simp only [denote,here,Polar,List.mem_cons,exists_eq_or_imp]
        tauto
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some joined,by simp [more],by simp [empty],?_⟩
    intro c same Object Value I fixes x
    cases same
    simp [empty]
termination_by values.val.length - index.val
decreasing_by all_goals omega

/-- Inclusion of the classes `values[index..]` in `whole`. -/
theorem within_from_correct (values : alloc.vec.Vec ClassExpression) (index : Usize) (whole : ClassExpression)
    (parts : shi_ontology.Parts) :
    ∃ r, shi_ontology.within_from values index whole parts = .ok r ∧
      (r.isSome → ∀ e ∈ values.val.drop index.val, Translatable e) ∧
      (Translatable whole → (∀ e ∈ values.val.drop index.val, Translatable e) →
        parts.definitions.val.length + (values.val.length - index.val) ≤ Usize.max → r.isSome) ∧
      ∀ parts', r = some parts' →
        parts'.definitions.val.length ≤ parts.definitions.val.length + (values.val.length - index.val) ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
          (PartsHold I parts' ↔ PartsHold I parts ∧
            ∀ e ∈ values.val.drop index.val, ∀ x, classDenote I e x → classDenote I whole x) := by
  rw [shi_ontology.within_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨t,tRun,tCorrect⟩ := translate_total_correct.{u,v} whole true
    cases t with
    | none =>
      refine ⟨none,by simp [more,tRun],by simp,?_,by simp⟩
      intro inside _ _
      simp only [Correct] at tCorrect
      exact absurd inside tCorrect
    | some inside =>
      obtain ⟨here,hereRun,hereSupport,hereTotal,hereSpec⟩ := include_correct.{u,v} values.val[index.val] inside parts
      cases here with
      | none =>
        refine ⟨none,by simp [more,lookup,tRun,hereRun],by simp,?_,by simp⟩
        intro _ every fits
        exact absurd (hereTotal (every _ (by rw [split]; exact List.mem_cons_self ..)) (by omega)) (by simp)
      | some parts1 =>
        obtain ⟨hereCount,hereMeaning⟩ := hereSpec parts1 rfl
        obtain ⟨rest,restRun,restSupport,restTotal,restSpec⟩ := within_from_correct values next whole parts1
        rw [nextIndex] at restSupport restTotal restSpec
        refine ⟨rest,by simp [more,lookup,tRun,hereRun,advance,restRun],?_,?_,?_⟩
        · intro some e found
          rw [split] at found
          rcases List.mem_cons.mp found with rfl | later
          · exact hereSupport rfl
          · exact restSupport some e later
        · intro inWhole every fits
          apply restTotal inWhole (fun e found => every e (by rw [split]; exact List.mem_cons_of_mem _ found))
          omega
        · intro parts' same
          obtain ⟨restCount,restMeaning⟩ := restSpec parts' same
          refine ⟨by omega,?_⟩
          intro Object Value I fixes
          have insideAt := tCorrect.2 Object Value I fixes
          simp only [Polar] at insideAt
          rw [restMeaning Object Value I fixes,hereMeaning Object Value I fixes,split]
          simp only [List.forall_mem_cons,insideAt]
          tauto
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some parts,by simp [more],by simp [empty],by simp,?_⟩
    intro parts' same
    cases same
    exact ⟨by omega,fun Object Value I fixes => by simp [empty]⟩
termination_by values.val.length - index.val
decreasing_by all_goals omega

/-- A disjoint union: afterwards the parts hold exactly when they held before,
    the class is the union of the members, and the members are pairwise
    disjoint. -/
theorem disjoint_union_correct (c : Class) (members : AtLeastTwo ClassExpression) (parts : shi_ontology.Parts) :
    ∃ r, shi_ontology.disjoint_union c members parts = .ok r ∧
      (r.isSome → ∀ e ∈ members.elements, Translatable e) ∧
      ((∀ e ∈ members.elements, Translatable e) →
        parts.definitions.val.length + Inclusions (.DisjointUnion c members) ≤ Usize.max → r.isSome) ∧
      ∀ parts', r = some parts' →
        parts'.definitions.val.length ≤ parts.definitions.val.length + Inclusions (.DisjointUnion c members) ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
          (PartsHold I parts' ↔ PartsHold I parts ∧ Rowl.Owl.satisfies I (.DisjointUnion c members)) := by
  have zero : (0#usize).val = 0 := rfl
  have length : members.elements.length = members.rest.val.length + 2 := by
    simp [AtLeastTwo.elements]
  have firstIn : members.first ∈ members.elements := by simp [AtLeastTwo.elements]
  have secondIn : members.second ∈ members.elements := by simp [AtLeastTwo.elements]
  have restIn : ∀ e ∈ members.rest.val, e ∈ members.elements := fun e member => by
    simp [AtLeastTwo.elements,member]
  have wholeIn : Translatable (.Class c) := by simp [Translatable]
  have count : Inclusions (.DisjointUnion c members) =
      3 + members.rest.val.length + members.elements.length * members.elements.length := by
    simp only [Inclusions]
    omega
  rw [shi_ontology.disjoint_union]
  simp only [Rowl.Nnf.copy_iri_identity,bind_ok]
  obtain ⟨first,firstRun,firstCorrect⟩ := translate_total_correct.{u,v} members.first true
  obtain ⟨second,secondRun,secondCorrect⟩ := translate_total_correct.{u,v} members.second true
  obtain ⟨whole,wholeRun,wholeCorrect⟩ := translate_total_correct.{u,v} (.Class c) true
  cases whole with
  | none => exact absurd wholeIn (by simpa [Correct] using wholeCorrect)
  | some inside =>
  cases first with
  | none =>
    refine ⟨none,by simp [firstRun],by simp,?_,by simp⟩
    intro every _
    simp only [Correct] at firstCorrect
    exact absurd (every _ firstIn) firstCorrect
  | some firstConcept =>
  cases second with
  | none =>
    refine ⟨none,by simp [firstRun,secondRun],by simp,?_,by simp⟩
    intro every _
    simp only [Correct] at secondCorrect
    exact absurd (every _ secondIn) secondCorrect
  | some secondConcept =>
  obtain ⟨union,unionRun,unionSupport,unionMeaning⟩ :=
    some_from_correct.{u,v} members.rest 0#usize (.Or firstConcept secondConcept)
  rw [zero,List.drop_zero] at unionSupport unionMeaning
  cases union with
  | none =>
    refine ⟨none,by simp [firstRun,secondRun,unionRun],by simp,?_,by simp⟩
    intro every _
    simp only [Option.isSome_none,Bool.false_eq_true,false_iff] at unionSupport
    exact absurd (fun e member => every e (restIn e member)) unionSupport
  | some unionConcept =>
  obtain ⟨one,oneRun,oneSupport,oneTotal,oneSpec⟩ := include_correct.{u,v} (.Class c) unionConcept parts
  cases one with
  | none =>
    refine ⟨none,by simp [firstRun,secondRun,unionRun,oneRun],by simp,?_,by simp⟩
    intro _ fits
    exact absurd (oneTotal wholeIn (by omega)) (by simp)
  | some parts1 =>
  obtain ⟨oneCount,oneMeaning⟩ := oneSpec parts1 rfl
  obtain ⟨two,twoRun,twoSupport,twoTotal,twoSpec⟩ := include_correct.{u,v} members.first inside parts1
  cases two with
  | none =>
    refine ⟨none,by simp [firstRun,secondRun,unionRun,oneRun,wholeRun,twoRun],by simp,?_,by simp⟩
    intro every fits
    exact absurd (twoTotal (every _ firstIn) (by omega)) (by simp)
  | some parts2 =>
  obtain ⟨twoCount,twoMeaning⟩ := twoSpec parts2 rfl
  obtain ⟨three,threeRun,threeSupport,threeTotal,threeSpec⟩ := include_correct.{u,v} members.second inside parts2
  cases three with
  | none =>
    refine ⟨none,by simp [firstRun,secondRun,unionRun,oneRun,wholeRun,twoRun,threeRun],by simp,?_,by simp⟩
    intro every fits
    exact absurd (threeTotal (every _ secondIn) (by omega)) (by simp)
  | some parts3 =>
  obtain ⟨threeCount,threeMeaning⟩ := threeSpec parts3 rfl
  obtain ⟨four,fourRun,fourSupport,fourTotal,fourSpec⟩ :=
    within_from_correct.{u,v} members.rest 0#usize (.Class c) parts3
  simp only [zero,List.drop_zero,Nat.sub_zero] at fourSupport fourTotal fourSpec
  cases four with
  | none =>
    refine ⟨none,by simp [firstRun,secondRun,unionRun,oneRun,wholeRun,twoRun,threeRun,fourRun],by simp,?_,by simp⟩
    intro every fits
    exact absurd (fourTotal wholeIn (fun e member => every e (restIn e member)) (by omega)) (by simp)
  | some parts4 =>
  obtain ⟨fourCount,fourMeaning⟩ := fourSpec parts4 rfl
  obtain ⟨five,fiveRun,fiveSupport,fiveTotal,fiveSpec⟩ := disjoint_correct.{u,v} members parts4
  refine ⟨five,by simp [firstRun,secondRun,unionRun,oneRun,wholeRun,twoRun,threeRun,fourRun,fiveRun],?_,?_,?_⟩
  · intro some
    exact fiveSupport some
  · intro every fits
    exact fiveTotal every (by omega)
  · intro parts' same
    obtain ⟨fiveCount,fiveMeaning⟩ := fiveSpec parts' same
    refine ⟨by omega,?_⟩
    intro Object Value I fixes
    have insideAt := wholeCorrect.2 Object Value I fixes
    have firstAt := firstCorrect.2 Object Value I fixes
    have secondAt := secondCorrect.2 Object Value I fixes
    simp only [Polar] at insideAt firstAt secondAt
    rw [fiveMeaning Object Value I fixes,fourMeaning Object Value I fixes,threeMeaning Object Value I fixes,
      twoMeaning Object Value I fixes,oneMeaning Object Value I fixes]
    have unionAt : ∀ x, denote I unionConcept x ↔ ∃ e ∈ members.elements, classDenote I e x := by
      intro x
      rw [unionMeaning unionConcept rfl Object Value I fixes x]
      simp only [denote,firstAt,secondAt,AtLeastTwo.elements,List.mem_cons,exists_eq_or_imp]
      tauto
    simp only [Rowl.Owl.satisfies,insideAt,unionAt]
    have classOf : ∀ x, classDenote I (.Class c) x ↔ I.classes c x := fun x => by simp [classDenote]
    simp only [classOf]
    constructor
    · rintro ⟨⟨⟨⟨⟨before,cover⟩,first⟩,second⟩,rest⟩,apart⟩
      refine ⟨before,fun x => ⟨cover x,?_⟩,apart⟩
      rintro ⟨e,member,holds⟩
      simp only [AtLeastTwo.elements,List.mem_cons] at member
      rcases member with rfl | rfl | later
      · exact first x holds
      · exact second x holds
      · exact rest e later x holds
    · rintro ⟨before,equal,apart⟩
      refine ⟨⟨⟨⟨⟨before,fun x => (equal x).mp⟩,fun x holds => (equal x).mpr ⟨_,firstIn,holds⟩⟩,
        fun x holds => (equal x).mpr ⟨_,secondIn,holds⟩⟩,fun e member x holds => (equal x).mpr ⟨e,restIn e member,holds⟩⟩,
        apart⟩

/-- Conjoining a concept onto the TBox concept. -/
theorem conjoin_correct (parts : shi_ontology.Parts) (concept : concepts.Concept) :
    shi_ontology.conjoin parts concept = .ok {parts with axioms := .And parts.axioms concept} := by
  rw [shi_ontology.conjoin]

/-- An axiom the parts leave unchanged. -/
private theorem unchanged_parts (statement : Axiom) (parts : shi_ontology.Parts)
    (run : shi_ontology.axiom_parts statement parts = .ok (some parts)) (supported : SupportedAxiom statement)
    (part : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), ClassPart I statement) :
    ∃ r, shi_ontology.axiom_parts statement parts = .ok r ∧
      (r.isSome → SupportedAxiom statement) ∧
      (SupportedAxiom statement → parts.definitions.val.length + Inclusions statement ≤ Usize.max → r.isSome) ∧
      ∀ parts', r = some parts' →
        parts'.definitions.val.length ≤ parts.definitions.val.length + Inclusions statement ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
          (PartsHold I parts' ↔ PartsHold I parts ∧ ClassPart I statement) := by
  refine ⟨some parts,run,fun _ => supported,fun _ _ => rfl,?_⟩
  intro parts' same
  cases same
  exact ⟨by omega,fun Object Value I _ => ⟨fun holds => ⟨holds,part Object Value I⟩,fun both => both.1⟩⟩

/-- An axiom the parts do not support. -/
private theorem refused_parts (statement : Axiom) (parts : shi_ontology.Parts)
    (run : shi_ontology.axiom_parts statement parts = .ok none) (unsupported : ¬ SupportedAxiom statement) :
    ∃ r, shi_ontology.axiom_parts statement parts = .ok r ∧
      (r.isSome → SupportedAxiom statement) ∧
      (SupportedAxiom statement → parts.definitions.val.length + Inclusions statement ≤ Usize.max → r.isSome) ∧
      ∀ parts', r = some parts' →
        parts'.definitions.val.length ≤ parts.definitions.val.length + Inclusions statement ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
          (PartsHold I parts' ↔ PartsHold I parts ∧ ClassPart I statement) :=
  ⟨none,run,by simp,fun supported => absurd supported unsupported,by simp⟩

/-- At most one element satisfies the property exactly when any two that do are
    equal. -/
theorem atMost_one_iff {α : Type u} (P : α → Prop) : Rowl.Owl.AtMost 1 P ↔ ∀ y z, P y → P z → y = z := by
  constructor
  · intro atMost y z py pz
    by_contra different
    apply atMost
    refine ⟨fun i => if i.val = 0 then y else z,?_,?_⟩
    · intro i j same
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      by_cases zi : i.val = 0 <;> by_cases zj : j.val = 0 <;> simp only [zi,zj,↓reduceIte] at same
      · omega
      · exact absurd same different
      · exact absurd same.symm different
      · omega
    · intro i
      by_cases zi : i.val = 0 <;> simp only [zi,↓reduceIte]
      · exact py
      · exact pz
  · rintro unique ⟨f,injective,each⟩
    have same := unique (f 0) (f 1) (each 0) (each 1)
    have := injective same
    simp at this

/-- One axiom: afterwards the parts hold exactly when they held before and the
    axiom's class part holds; the axiom is read exactly when it is supported
    and its definitions fit. -/
theorem axiom_parts_correct (statement : Axiom) (parts : shi_ontology.Parts) :
    ∃ r, shi_ontology.axiom_parts statement parts = .ok r ∧
      (r.isSome → SupportedAxiom statement) ∧
      (SupportedAxiom statement → parts.definitions.val.length + Inclusions statement ≤ Usize.max → r.isSome) ∧
      ∀ parts', r = some parts' →
        parts'.definitions.val.length ≤ parts.definitions.val.length + Inclusions statement ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
          (PartsHold I parts' ↔ PartsHold I parts ∧ ClassPart I statement) := by
  cases statement with
  | Declaration _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Rowl.Owl.satisfies])
  | SubClassOf a b =>
    obtain ⟨t,tRun,tCorrect⟩ := translate_total_correct.{u,v} b true
    cases t with
    | none =>
      refine ⟨none,by rw [shi_ontology.axiom_parts]; simp [tRun],by simp,?_,by simp⟩
      intro supported _
      simp only [Correct] at tCorrect
      exact absurd supported.2 tCorrect
    | some inside =>
      obtain ⟨r,run,support,total,spec⟩ := include_correct.{u,v} a inside parts
      refine ⟨r,by rw [shi_ontology.axiom_parts]; simp [tRun,run],fun some => ⟨support some,tCorrect.1⟩,?_,?_⟩
      · intro supported fits
        simp only [Inclusions] at fits
        exact total supported.1 (by omega)
      · intro parts' same
        obtain ⟨count,meaning⟩ := spec parts' same
        refine ⟨by simp only [Inclusions]; omega,?_⟩
        intro Object Value I fixes
        rw [meaning Object Value I fixes]
        have insideAt := tCorrect.2 Object Value I fixes
        simp only [Polar] at insideAt
        simp only [ClassPart,Assertion,Equality,RoleAxiom,ConstraintAxiom,Rowl.Owl.satisfies,insideAt,false_or]
  | EquivalentClasses xs =>
    obtain ⟨r,run,support,total,spec⟩ := equivalent_correct.{u,v} xs parts
    refine ⟨r,by rw [shi_ontology.axiom_parts]; exact run,support,total,?_⟩
    intro parts' same
    obtain ⟨count,meaning⟩ := spec parts' same
    refine ⟨count,?_⟩
    intro Object Value I fixes
    rw [meaning Object Value I fixes]
    simp only [ClassPart,Assertion,Equality,RoleAxiom,ConstraintAxiom,Rowl.Owl.satisfies,false_or]
  | DisjointClasses xs =>
    obtain ⟨r,run,support,total,spec⟩ := disjoint_correct.{u,v} xs parts
    refine ⟨r,by rw [shi_ontology.axiom_parts]; exact run,support,total,?_⟩
    intro parts' same
    obtain ⟨count,meaning⟩ := spec parts' same
    refine ⟨count,?_⟩
    intro Object Value I fixes
    rw [meaning Object Value I fixes]
    simp only [ClassPart,Assertion,Equality,RoleAxiom,ConstraintAxiom,Rowl.Owl.satisfies,false_or]
  | DisjointUnion c xs =>
    obtain ⟨r,run,support,total,spec⟩ := disjoint_union_correct.{u,v} c xs parts
    refine ⟨r,by rw [shi_ontology.axiom_parts]; exact run,support,total,?_⟩
    intro parts' same
    obtain ⟨count,meaning⟩ := spec parts' same
    refine ⟨count,?_⟩
    intro Object Value I fixes
    rw [meaning Object Value I fixes]
    simp only [ClassPart,Assertion,Equality,RoleAxiom,ConstraintAxiom,false_or]
  | SubObjectPropertyOf sub sup =>
    cases sub with
    | Single p =>
      exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
        (fun _ _ _ => by simp [ClassPart,Equality,RoleAxiom,ConstraintAxiom])
    | Chain _ => exact refused_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
  | EquivalentObjectProperties _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Equality,RoleAxiom,ConstraintAxiom])
  | InverseObjectProperties _ _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Equality,RoleAxiom,ConstraintAxiom])
  | SymmetricObjectProperty _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Equality,RoleAxiom,ConstraintAxiom])
  | TransitiveObjectProperty _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Equality,RoleAxiom,ConstraintAxiom])
  | ObjectPropertyDomain p e =>
    obtain ⟨t,tRun,tCorrect⟩ := translate_total_correct.{u,v} e true
    cases t with
    | none =>
      refine ⟨none,by rw [shi_ontology.axiom_parts]; simp [tRun],by simp,?_,by simp⟩
      intro supported _
      simp only [Correct] at tCorrect
      exact absurd supported tCorrect
    | some inside =>
      refine ⟨some {parts with axioms := .And parts.axioms (.Forall (inv p) inside)},
        by rw [shi_ontology.axiom_parts]; simp [tRun,inverse_correct,conjoin_correct],fun _ => tCorrect.1,
        fun _ _ => rfl,?_⟩
      intro parts' same
      cases same
      refine ⟨by simp,?_⟩
      intro Object Value I fixes
      have insideAt := tCorrect.2 Object Value I fixes
      simp only [Polar] at insideAt
      simp only [PartsHold,denote,relation_inv,insideAt,ClassPart,Assertion,Equality,RoleAxiom,ConstraintAxiom,
        Rowl.Owl.satisfies,false_or]
      constructor
      · rintro ⟨every,defs⟩
        exact ⟨⟨fun x => (every x).1,defs⟩,fun x y edge => (every y).2 x edge⟩
      · rintro ⟨⟨tbox,defs⟩,domain⟩
        exact ⟨fun x => ⟨tbox x,fun y edge => domain y x edge⟩,defs⟩
  | ObjectPropertyRange p e =>
    obtain ⟨t,tRun,tCorrect⟩ := translate_total_correct.{u,v} e true
    cases t with
    | none =>
      refine ⟨none,by rw [shi_ontology.axiom_parts]; simp [tRun],by simp,?_,by simp⟩
      intro supported _
      simp only [Correct] at tCorrect
      exact absurd supported tCorrect
    | some inside =>
      refine ⟨some {parts with axioms := .And parts.axioms (.Forall p inside)},
        by rw [shi_ontology.axiom_parts]; simp [tRun,copy_role_identity,conjoin_correct],fun _ => tCorrect.1,
        fun _ _ => rfl,?_⟩
      intro parts' same
      cases same
      refine ⟨by simp,?_⟩
      intro Object Value I fixes
      have insideAt := tCorrect.2 Object Value I fixes
      simp only [Polar] at insideAt
      simp only [PartsHold,denote,insideAt,ClassPart,Assertion,Equality,RoleAxiom,ConstraintAxiom,
        Rowl.Owl.satisfies,false_or]
      constructor
      · rintro ⟨every,defs⟩
        exact ⟨⟨fun x => (every x).1,defs⟩,fun x y edge => (every x).2 y edge⟩
      · rintro ⟨⟨tbox,defs⟩,range⟩
        exact ⟨fun x => ⟨tbox x,fun y edge => range x y edge⟩,defs⟩
  | FunctionalObjectProperty p =>
    refine ⟨some {parts with axioms := .And parts.axioms (.AtMost 1#usize p .Top)},
      by rw [shi_ontology.axiom_parts]; simp [copy_role_identity,conjoin_correct],fun _ => trivial,
      fun _ _ => rfl,?_⟩
    intro parts' same
    cases same
    refine ⟨by simp,?_⟩
    intro Object Value I fixes
    simp only [PartsHold,denote,ClassPart,Assertion,Equality,RoleAxiom,ConstraintAxiom,
      Rowl.Owl.satisfies,false_or,and_true]
    have functional : (∀ x, Rowl.Owl.AtMost (1#usize).val (fun y => objectRelation I p x y)) ↔
        ∀ x y z, objectRelation I p x y → objectRelation I p x z → y = z := by
      refine forall_congr' (fun x => ?_)
      exact atMost_one_iff _
    constructor
    · rintro ⟨every,defs⟩
      exact ⟨⟨fun x => (every x).1,defs⟩,functional.mp (fun x => (every x).2)⟩
    · rintro ⟨⟨tbox,defs⟩,unique⟩
      exact ⟨fun x => ⟨tbox x,functional.mpr unique x⟩,defs⟩
  | InverseFunctionalObjectProperty p =>
    refine ⟨some {parts with axioms := .And parts.axioms (.AtMost 1#usize (inv p) .Top)},
      by rw [shi_ontology.axiom_parts]; simp [inverse_correct,conjoin_correct],fun _ => trivial,
      fun _ _ => rfl,?_⟩
    intro parts' same
    cases same
    refine ⟨by simp,?_⟩
    intro Object Value I fixes
    simp only [PartsHold,denote,ClassPart,Assertion,Equality,RoleAxiom,ConstraintAxiom,
      Rowl.Owl.satisfies,false_or,and_true]
    have functional : (∀ z, Rowl.Owl.AtMost (1#usize).val (fun x => objectRelation I (inv p) z x)) ↔
        ∀ x y z, objectRelation I p x z → objectRelation I p y z → x = y := by
      constructor
      · intro every x y z first second
        exact (atMost_one_iff _).mp (every z) x y ((relation_inv I p z x).mpr first) ((relation_inv I p z y).mpr second)
      · intro unique z
        exact (atMost_one_iff _).mpr (fun x y first second =>
          unique x y z ((relation_inv I p z x).mp first) ((relation_inv I p z y).mp second))
    constructor
    · rintro ⟨every,defs⟩
      exact ⟨⟨fun x => (every x).1,defs⟩,functional.mp (fun x => (every x).2)⟩
    · rintro ⟨⟨tbox,defs⟩,unique⟩
      exact ⟨fun x => ⟨tbox x,functional.mpr unique x⟩,defs⟩
  | ReflexiveObjectProperty p =>
    refine ⟨some {parts with axioms := .And parts.axioms (.HasSelf p)},
      by rw [shi_ontology.axiom_parts]; simp [copy_role_identity,conjoin_correct],fun _ => trivial,
      fun _ _ => rfl,?_⟩
    intro parts' same
    cases same
    refine ⟨by simp,?_⟩
    intro Object Value I fixes
    simp only [PartsHold,denote,ClassPart,Assertion,Equality,RoleAxiom,ConstraintAxiom,Rowl.Owl.satisfies,false_or]
    constructor
    · rintro ⟨every,defs⟩
      exact ⟨⟨fun x => (every x).1,defs⟩,fun x => (every x).2⟩
    · rintro ⟨⟨tbox,defs⟩,reflexive⟩
      exact ⟨fun x => ⟨tbox x,reflexive x⟩,defs⟩
  | IrreflexiveObjectProperty p =>
    refine ⟨some {parts with axioms := .And parts.axioms (.NotSelf p)},
      by rw [shi_ontology.axiom_parts]; simp [copy_role_identity,conjoin_correct],fun _ => trivial,
      fun _ _ => rfl,?_⟩
    intro parts' same
    cases same
    refine ⟨by simp,?_⟩
    intro Object Value I fixes
    simp only [PartsHold,denote,ClassPart,Assertion,Equality,RoleAxiom,ConstraintAxiom,Rowl.Owl.satisfies,false_or]
    constructor
    · rintro ⟨every,defs⟩
      exact ⟨⟨fun x => (every x).1,defs⟩,fun x => (every x).2⟩
    · rintro ⟨⟨tbox,defs⟩,irreflexive⟩
      exact ⟨fun x => ⟨tbox x,irreflexive x⟩,defs⟩
  | SameIndividual _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Equality])
  | DifferentIndividuals _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Equality])
  | ClassAssertion _ _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Assertion])
  | ObjectPropertyAssertion _ _ _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Assertion])
  | NegativeObjectPropertyAssertion _ _ _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Assertion])
  | AnnotationAssertion _ _ _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Rowl.Owl.satisfies])
  | SubAnnotationPropertyOf _ _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Rowl.Owl.satisfies])
  | AnnotationPropertyDomain _ _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Rowl.Owl.satisfies])
  | AnnotationPropertyRange _ _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,Rowl.Owl.satisfies])
  | AsymmetricObjectProperty _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,ConstraintAxiom])
  | DisjointObjectProperties _ =>
    exact unchanged_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])
      (fun _ _ _ => by simp [ClassPart,ConstraintAxiom])
  | SubDataPropertyOf _ _
  | EquivalentDataProperties _ | DisjointDataProperties _ | DataPropertyDomain _ _ | DataPropertyRange _ _
  | FunctionalDataProperty _ | DatatypeDefinition _ _ | HasKey _ _ _
  | DataPropertyAssertion _ _ _ | NegativeDataPropertyAssertion _ _ _ =>
    exact refused_parts _ _ (by rw [shi_ontology.axiom_parts]) (by simp [SupportedAxiom])

/-- The axioms `items[index..]`: afterwards the parts hold exactly when they held
    before and every class part holds; they are read only when every axiom is
    supported, and always when also their definitions fit. -/
theorem parts_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) (parts : shi_ontology.Parts) :
    ∃ r, shi_ontology.parts_from items index parts = .ok r ∧
      (r.isSome → ∀ a ∈ items.val.drop index.val, SupportedAxiom a.axiom) ∧
      ((∀ a ∈ items.val.drop index.val, SupportedAxiom a.axiom) →
        parts.definitions.val.length + ((items.val.drop index.val).map (fun a => Inclusions a.axiom)).sum ≤
          Usize.max → r.isSome) ∧
      ∀ parts', r = some parts' → ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
        (PartsHold I parts' ↔ PartsHold I parts ∧ ∀ a ∈ items.val.drop index.val, ClassPart I a.axiom) := by
  rw [shi_ontology.parts_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨here,hereRun,hereSupport,hereTotal,hereSpec⟩ := axiom_parts_correct.{u,v} items.val[index.val].axiom parts
    cases here with
    | none =>
      refine ⟨none,by simp [more,lookup,hereRun],by simp,?_,by simp⟩
      intro every fits
      rw [split] at every fits
      simp only [List.map_cons,List.sum_cons] at fits
      exact absurd (hereTotal (every _ (List.mem_cons_self ..)) (by omega)) (by simp)
    | some parts1 =>
      obtain ⟨hereCount,hereMeaning⟩ := hereSpec parts1 rfl
      obtain ⟨rest,restRun,restSupport,restTotal,restSpec⟩ := parts_from_correct items next parts1
      rw [nextIndex] at restSupport restTotal restSpec
      refine ⟨rest,by simp [more,lookup,hereRun,advance,restRun],?_,?_,?_⟩
      · intro some a member
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · exact hereSupport rfl
        · exact restSupport some a later
      · intro every fits
        rw [split] at every fits
        simp only [List.map_cons,List.sum_cons] at fits
        exact restTotal (fun a member => every a (List.mem_cons_of_mem _ member)) (by omega)
      · intro parts' same Object Value I fixes
        rw [restSpec parts' same Object Value I fixes,hereMeaning Object Value I fixes,split]
        simp only [List.forall_mem_cons]
        tauto
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some parts,by simp [more],by simp [empty],by simp,?_⟩
    intro parts' same Object Value I fixes
    cases same
    simp [empty]
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- The actual class parts of a closure: they are computed only when every axiom
    is supported, always when also the definitions fit in the `usize` range,
    and they hold in an interpretation fixing owl:Thing and owl:Nothing exactly
    when it satisfies every axiom of the closure that is neither an assertion
    nor a role axiom. -/
theorem class_parts_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ r, shi_ontology.class_parts items = .ok r ∧
      (r.isSome → ∀ a ∈ items.val, SupportedAxiom a.axiom) ∧
      ((∀ a ∈ items.val, SupportedAxiom a.axiom) → (items.val.map (fun a => Inclusions a.axiom)).sum ≤ Usize.max →
        r.isSome) ∧
      ∀ parts, r = some parts → ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
        (PartsHold I parts ↔ ∀ a ∈ items.val, ClassPart I a.axiom) := by
  have zero : (0#usize).val = 0 := rfl
  obtain ⟨r,run,support,total,spec⟩ := parts_from_correct.{u,v} items 0#usize
    ⟨.Top,alloc.vec.Vec.new completion.Definition⟩
  rw [zero,List.drop_zero] at support total spec
  refine ⟨r,by rw [shi_ontology.class_parts]; exact run,support,fun every fits => total every (by simpa using fits),?_⟩
  intro parts same Object Value I fixes
  rw [spec parts same Object Value I fixes]
  simp [PartsHold,denote]

end Rowl.ShiParts
