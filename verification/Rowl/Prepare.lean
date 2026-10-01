import Rowl.OwlLaws

namespace Rowl.Prepare
open Aeneas Aeneas.Std RowlRust.model RowlRust.prepare Rowl.Owl
universe u v

def preparedSatisfies {Object : Type u} {Value : Type v}
    (I : Interpretation Object Value) : PreparedAxiom → Prop
  | .UniversalClass constraint => ∀ x, classDenote I constraint x
  | .Retained a => satisfies I a

/-- Total, idempotent canonicalization of positive and negative inverse assertions.
    Exact satisfaction is preserved for every interpretation, including anonymous names. -/
theorem canonicalize_assertion_total_correct (a : Axiom) :
    ∃ result, canonicalize_assertion a = .ok result ∧
      canonicalize_assertion result = .ok result ∧
      ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value),
        satisfies I result ↔ satisfies I a := by
  cases a <;> try exact ⟨_, rfl, rfl, fun _ => Iff.rfl⟩
  case ObjectPropertyAssertion p a b =>
    cases p <;> exact ⟨_, rfl, rfl, fun _ => Iff.rfl⟩
  case NegativeObjectPropertyAssertion p a b =>
    cases p <;> exact ⟨_, rfl, rfl, fun _ => Iff.rfl⟩

/-- C ⊑ D iff every object satisfies ¬C ∪ D; this does not add a named witness. -/
theorem lower_subclass_total_correct (a : Axiom) :
    ∃ result, lower_subclass a = .ok result ∧
      ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value),
        preparedSatisfies I result ↔ satisfies I a := by
  cases a <;> try exact ⟨_, rfl, fun _ => Iff.rfl⟩
  case SubClassOf sub sup =>
    refine ⟨_, rfl, ?_⟩
    intro Object Value I
    change (∀ x, classDenote I (.ObjectUnionOf
      ⟨.ObjectComplementOf sub, sup, alloc.vec.Vec.new ClassExpression⟩) x) ↔
        ∀ x, classDenote I sub x → classDenote I sup x
    classical
    simp only [classDenote]
    simp
    constructor
    · intro h x hx
      rcases h x with no | yes
      · exact False.elim (no hx)
      · exact yes
    · intro h x
      by_cases hx : classDenote I sub x
      · exact Or.inr (h x hx)
      · exact Or.inl hx

/-- Actual Rust stage composition preserves annotations and exact semantics. -/
theorem prepare_axiom_total_correct (a : AnnotatedAxiom) :
    ∃ result, prepare_axiom a = .ok result ∧ result.annotations = a.annotations ∧
      ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value),
        preparedSatisfies I result.logical ↔ satisfies I a.axiom := by
  obtain ⟨canonical, hc, _, hs⟩ := canonicalize_assertion_total_correct.{u,v} a.axiom
  obtain ⟨logical, hl, hp⟩ := lower_subclass_total_correct.{u,v} canonical
  refine ⟨⟨a.annotations, logical⟩, by simp [prepare_axiom, hc, hl], rfl, ?_⟩
  intro Object Value I
  exact (hp I).trans (hs I)

/-- Lift the pointwise equivalence through the OWL anonymous-assignment model rule.
    Vocabulary/declarations are kept externally; this is not DL validation. -/
theorem preparation_preserves_anonymous_models {Object : Type u} {Value : Type v}
    (I : Interpretation Object Value) (source : List AnnotatedAxiom)
    (prepared : AnnotatedAxiom → PreparedAnnotatedAxiom)
    (checked : ∀ a ∈ source, prepare_axiom a = .ok (prepared a)) :
    modelsClosure I source ↔
      ∃ assignment, ∀ a ∈ source,
        preparedSatisfies (withAnonymous I assignment) (prepared a).logical := by
  have exactMeaning (a : AnnotatedAxiom) (ha : a ∈ source)
      (assignment : AnonymousIndividual → Object) :
      preparedSatisfies (withAnonymous I assignment) (prepared a).logical ↔
        satisfies (withAnonymous I assignment) a.axiom := by
    obtain ⟨result, hr, _, hs⟩ := prepare_axiom_total_correct.{u,v} a
    have same := Result.ok_injective ((checked a ha).symm.trans hr)
    rw [← same] at hs
    exact hs _
  unfold modelsClosure satisfiesClosure
  constructor
  · rintro ⟨assignment, h⟩
    exact ⟨assignment, fun a ha => (exactMeaning a ha assignment).mpr (h a ha)⟩
  · rintro ⟨assignment, h⟩
    exact ⟨assignment, fun a ha => (exactMeaning a ha assignment).mp (h a ha)⟩

end Rowl.Prepare
