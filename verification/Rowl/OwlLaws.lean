import Rowl.OwlSemantics

namespace Rowl.Owl
open Aeneas Aeneas.Std RowlRust.model
universe u v w
variable {Object : Type u} {Value : Type v}

/-- Total correctness and involution of the actual Rust operation. -/
theorem invert_total_correct (p : ObjectPropertyExpression) :
    ∃ q, invert p = .ok q ∧ invert q = .ok p := by cases p <;> simp [invert]
theorem invert_semantics (I : Interpretation Object Value) (p : ObjectPropertyExpression) :
    ∃ q, invert p = .ok q ∧ ∀ x y, objectRelation I q x y ↔ objectRelation I p y x := by
  cases p <;> simp [invert, objectRelation]

theorem at_least_zero {α : Type u} (P : α → Prop) : AtLeast 0 P :=
  ⟨Fin.elim0, by intro x; exact Fin.elim0 x, by intro x; exact Fin.elim0 x⟩
theorem at_most_one_iff {α : Type u} (P : α → Prop) :
    AtMost 1 P ↔ ∀ x y, P x → P y → x = y := by
  constructor
  · intro h x y hx hy
    by_contra hne
    apply h
    refine ⟨(fun i => if i = 0 then x else y), ?_, ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · intro i; fin_cases i <;> simp_all
  · intro h ⟨f, hinj, hp⟩
    have eq := hinj (h (f 0) (f 1) (hp 0) (hp 1))
    exact (by decide : (0 : Fin 2) ≠ 1) eq

theorem exactly_one_singleton {α : Type u} (a : α) : Exactly 1 (fun x => x = a) := by
  constructor
  · refine ⟨(fun _ => a), ?_, by simp⟩
    intro x y _; exact Subsingleton.elim x y
  · apply (at_most_one_iff _).mpr
    intro x y hx hy; exact hx.trans hy.symm

/-- Infinite sets satisfy every finite lower bound, and no finite upper bound. -/
theorem infinite_cardinality (n : Nat) :
    AtLeast n (fun _ : Nat => True) ∧ ¬ AtMost n (fun _ : Nat => True) := by
  have lower (k : Nat) : AtLeast k (fun _ : Nat => True) :=
    ⟨Fin.val, Fin.val_injective, by simp⟩
  exact ⟨lower n, fun h => h (lower (n + 1))⟩

theorem data_complement_entire_domain (I : Interpretation Object Value) (r : DataRange) (x : Value) :
    dataDenote I (.Complement r) x ↔ ¬ dataDenote I r x := by rw [dataDenote]
theorem literal_values_coalesce (I : Interpretation Object Value) (a b : Literal)
    (h : I.literals a = I.literals b) (x : Value) :
    (I.literals a = x ↔ I.literals b = x) := by rw [h]

theorem datatype_embedding_preserves_distinct_values {Native : Type w} (D : DatatypeMap Native)
    (embed : ValueEmbedding D Value) (x y : Native)
    (hx : isDatatypeValue D x) (hy : isDatatypeValue D y) (hne : x ≠ y) : embed x ≠ embed y :=
  fun h => hne (embed.injectiveValues x y hx hy h)

theorem universal_vacuity (I : Interpretation Object Value) (p : ObjectPropertyExpression)
    (e : ClassExpression) (x : Object) (h : ∀ y, ¬ objectRelation I p x y) :
    classDenote I (.ObjectAllValuesFrom p e) x := by
  rw [classDenote]; intro y hy; exact False.elim (h y hy)
theorem existential_without_named_requirement (I : Interpretation Object Value)
    (p : ObjectPropertyExpression) (e : ClassExpression) (x y : Object)
    (edge : objectRelation I p x y) (member : classDenote I e y) :
    classDenote I (.ObjectSomeValuesFrom p e) x := by
  rw [classDenote]; exact ⟨y, edge, member⟩

/-- Two asserted names under a functional relation force equality, not a clash.
    A separately asserted difference then contradicts that equality. -/
theorem functional_forces_equality (I : Interpretation Object Value)
    (p : ObjectPropertyExpression) (a b c : Individual)
    (functional : satisfies I (.FunctionalObjectProperty p))
    (left : satisfies I (.ObjectPropertyAssertion p a b))
    (right : satisfies I (.ObjectPropertyAssertion p a c)) :
    individual I b = individual I c := functional _ _ _ left right
theorem functional_difference_conflict (I : Interpretation Object Value)
    (p : ObjectPropertyExpression) (a b c : Individual)
    (functional : satisfies I (.FunctionalObjectProperty p))
    (left : satisfies I (.ObjectPropertyAssertion p a b))
    (right : satisfies I (.ObjectPropertyAssertion p a c))
    (different : individual I b ≠ individual I c) : False :=
  different (functional_forces_equality I p a b c functional left right)

theorem functionality_counts_denotations (I : Interpretation Object Value)
    (p : ObjectPropertyExpression) (x : Object)
    (h : satisfies I (.FunctionalObjectProperty p)) : AtMost 1 (objectRelation I p x) :=
  (at_most_one_iff _).mpr (h x)

/-- A concrete application rule: a machine with a faulty part needs inspection. -/
theorem maintenance_follows (I : Interpretation Object Value)
    (machine faulty inspection : ClassExpression) (hasPart : ObjectPropertyExpression)
    (a b : Individual)
    (rule : satisfies I (.SubClassOf (.ObjectIntersectionOf
      ⟨machine, .ObjectSomeValuesFrom hasPart faulty, alloc.vec.Vec.from [] (by simp)⟩) inspection))
    (isMachine : satisfies I (.ClassAssertion machine a))
    (part : satisfies I (.ObjectPropertyAssertion hasPart a b))
    (isFaulty : satisfies I (.ClassAssertion faulty b)) :
    satisfies I (.ClassAssertion inspection a) := by
  apply rule
  rw [classDenote]
  exact ⟨isMachine, existential_without_named_requirement I hasPart faulty _ _ part isFaulty, by simp⟩

theorem chain_append (I : Interpretation Object Value) (ps qs : List ObjectPropertyExpression)
    (x y : Object) : chainRelation I (ps ++ qs) x y ↔
      ∃ z, chainRelation I ps x z ∧ chainRelation I qs z y := by
  induction ps generalizing x with
  | nil => simp [chainRelation]
  | cons p ps ih => simp only [List.cons_append, chainRelation, ih]; aesop

theorem key_ignores_unnamed_subjects (I : Interpretation Object Value)
    (e : ClassExpression) (ops : alloc.vec.Vec ObjectPropertyExpression) (dps : alloc.vec.Vec DataProperty)
    (h : ∀ x, ¬ I.named x) : satisfies I (.HasKey e ops dps) := by
  intro x _ _ named; exact False.elim (h x named)
theorem key_requires_named_object_fillers (I : Interpretation Object Value)
    (e : ClassExpression) (p : ObjectPropertyExpression) (dps : alloc.vec.Vec DataProperty)
    (ops : alloc.vec.Vec ObjectPropertyExpression) (hp : p ∈ ops.val)
    (h : ∀ x y, x ≠ y → ∀ z, objectRelation I p x z → objectRelation I p y z → ¬ I.named z) :
    satisfies I (.HasKey e ops dps) := by
  intro x y _ _ _ _ shared _
  by_contra hne
  obtain ⟨z, hn, hx, hy⟩ := shared p hp
  exact h x y hne z hx hy hn

def satisfiesAnnotated (I : Interpretation Object Value) (a : AnnotatedAxiom) : Prop := satisfies I a.axiom
theorem annotations_irrelevant (I : Interpretation Object Value) (a : Axiom)
    (left right : alloc.vec.Vec Annotation) :
    satisfiesAnnotated I ⟨left, a⟩ ↔ satisfiesAnnotated I ⟨right, a⟩ := Iff.rfl
theorem declarations_irrelevant (I : Interpretation Object Value) (e : Entity) :
    satisfies I (.Declaration e) := True.intro

theorem satisfaction_gives_model (I : Interpretation Object Value) (closure : AxiomClosure)
    (h : satisfiesClosure I closure) : modelsClosure I closure :=
  ⟨I.anonymousIndividuals, h⟩
theorem anonymous_reassignment_invariant (I : Interpretation Object Value)
    (assignment : AnonymousIndividual → Object) (closure : AxiomClosure) :
    modelsClosure (withAnonymous I assignment) closure ↔ modelsClosure I closure := Iff.rfl
theorem anonymous_reassignment_preserves_interpretation {Native : Type w}
    (D : DatatypeMap Native) (embed : ValueEmbedding D Value) (V : Vocabulary)
    (I : Interpretation Object Value) (assignment : AnonymousIndividual → Object) :
    IsInterpretation D embed V (withAnonymous I assignment) ↔ IsInterpretation D embed V I := Iff.rfl

theorem inconsistent_entails_everything {Native : Type w} (D : DatatypeMap Native)
    (V : Vocabulary) (source target : AxiomClosure) (h : ¬ Consistent.{u,v,w} D V source) :
    Entails.{u,v,w} D V source target := by
  intro Object Value embed I model
  exact False.elim (h ⟨Object, Value, embed, I, model⟩)

end Rowl.Owl
