import Rowl.Components

/-!
# Entailment of named facts

A closure entails a fact when every model of the closure satisfies it. A
property assertion about named individuals, its negative, and an equality or
inequality of two named individuals each have a negation that is again an
assertion, about the same individuals, that an interpretation satisfies
exactly when it does not satisfy the fact (`Negates`). The closure entails
such a fact exactly when the closure with the negation has no model
(`entails_iff_inconsistent`). `facts::entails_fact` copies the axioms of the
closure that mean something, adds the negation (`negation_spec`,
`meaningful_spec`) and asks the verified consistency procedures, part by part
when the closure falls apart along its assertions
(`consistent_closure_correct`); `entails_fact_correct` composes them.
-/

namespace Rowl.Facts
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model Rowl.Owl Rowl.Partition
open Rowl.DatatypeMap
open Rowl.DataAxioms (axiomIndividuals)
open Rowl.KeyEncoding (NamesKeyed Keyed closureIndividuals IsKey keyIndividuals)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

universe u v w

/-! ## The meaning of a negation -/

/-- `negated` is an assertion that an interpretation satisfies exactly when it
    does not satisfy `fact`, about the same individuals; no reassignment of
    the anonymous individuals changes whether `fact` holds. -/
def Negates (fact negated : Axiom) : Prop :=
  (∀ {O : Type u} {W : Type v} (I : Interpretation O W), satisfies I negated ↔ ¬ satisfies I fact) ∧
  (∀ {O : Type u} {W : Type v} (I : Interpretation O W) (asg : AnonymousIndividual → O),
    satisfies (withAnonymous I asg) fact ↔ satisfies I fact) ∧
  axiomIndividuals negated = axiomIndividuals fact ∧ ¬ IsKey negated ∧ ¬ Meaningless negated

section Meaning
variable {Native : Type w} {D : DatatypeMap Native} {V : Vocabulary}

/-- A closure entails a fact exactly when the closure with its negation has no
    model. -/
theorem entails_iff_inconsistent {items : List AnnotatedAxiom} {fact negated : Axiom}
    (negates : Negates.{u,v} fact negated) (annotations annotations' : alloc.vec.Vec Annotation) :
    Entails.{u,v,w} D V items [⟨annotations, fact⟩] ↔
      ¬ Consistent.{u,v,w} D V (items ++ [⟨annotations', negated⟩]) := by
  obtain ⟨meaning, unchanged, -, -, -⟩ := negates
  constructor
  · rintro entailed ⟨O, W, e, I, vocab, h, asg, sat⟩
    obtain ⟨_, _, asg', satFact⟩ :=
      entailed O W e I ⟨vocab, h, asg, fun x mx => sat x (List.mem_append_left _ mx)⟩
    have holds : satisfies (withAnonymous I asg') fact := satFact _ (List.mem_singleton_self _)
    have denied : satisfies (withAnonymous I asg) negated :=
      sat _ (List.mem_append_right _ (List.mem_singleton_self _))
    exact (meaning _).mp denied ((unchanged I asg).mpr ((unchanged I asg').mp holds))
  · intro inconsistent O W e I model
    obtain ⟨vocab, h, asg, sat⟩ := model
    refine ⟨vocab, h, asg, fun y my => ?_⟩
    rw [List.mem_singleton] at my
    subst my
    by_contra fails
    refine inconsistent ⟨O, W, e, I, vocab, h, asg, fun x mx => ?_⟩
    rcases List.mem_append.mp mx with old | new
    · exact sat x old
    · rw [List.mem_singleton] at new
      subst new
      exact (meaning _).mpr fails
end Meaning

/-! ## The negation the kernel builds -/

private theorem named_eq (i : Individual) : facts.named i = .ok (decide (∃ a, i = .Named a)) := by
  cases i <;> simp [facts.named]

private theorem two_equal {α : Type} {β : Sort _} (a b : α) (f : α → β) :
    allEqual [a, b] f ↔ f a = f b := by
  constructor
  · intro all
    exact all a (by simp) b (by simp)
  · intro same x mx y my
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mx my
    rcases mx with rfl | rfl <;> rcases my with rfl | rfl <;> simp [same]

private theorem two_different {α : Type} {β : Sort _} (a b : α) (f : α → β) :
    [a, b].Pairwise (fun x y => f x ≠ f y) ↔ f a ≠ f b := by
  simp

/-- The kernel's negation of a fact, when there is one, is a negation. -/
theorem negation_spec (fact : Axiom) :
    ∃ r, facts.negation fact = .ok r ∧ ∀ negated, r = some negated → Negates.{u,v} fact negated := by
  rw [facts.negation]
  rcases Rowl.Components.copy_axiom_spec fact with none' | some'
  · exact ⟨none, by simp [none'], by simp⟩
  · simp only [some', bind_ok]
    cases fact
    case SameIndividual xs =>
      obtain ⟨a, b, rest⟩ := xs
      by_cases empty : rest.val = []
      · cases a with
        | Anonymous a => exact ⟨none, by simp [facts.flip, named_eq, alloc.vec.Vec.len_val, empty], by simp⟩
        | Named a =>
          cases b with
          | Anonymous b => exact ⟨none, by simp [facts.flip, named_eq, alloc.vec.Vec.len_val, empty], by simp⟩
          | Named b =>
            refine ⟨some (.DifferentIndividuals ⟨.Named a, .Named b, rest⟩),
              by simp [facts.flip, named_eq, alloc.vec.Vec.len_val, empty], fun negated same => ?_⟩
            simp only [Option.some.injEq] at same
            subst same
            refine ⟨fun I => ?_, fun I asg => ?_, rfl, by simp [IsKey], by simp [Meaningless]⟩
            · simp only [satisfies, AtLeastTwo.elements, empty, two_equal, two_different]
            · simp only [satisfies, AtLeastTwo.elements, empty, two_equal]
              rfl
      · exact ⟨none, by simp [facts.flip, alloc.vec.Vec.len_val, empty], by simp⟩
    case DifferentIndividuals xs =>
      obtain ⟨a, b, rest⟩ := xs
      by_cases empty : rest.val = []
      · cases a with
        | Anonymous a => exact ⟨none, by simp [facts.flip, named_eq, alloc.vec.Vec.len_val, empty], by simp⟩
        | Named a =>
          cases b with
          | Anonymous b => exact ⟨none, by simp [facts.flip, named_eq, alloc.vec.Vec.len_val, empty], by simp⟩
          | Named b =>
            refine ⟨some (.SameIndividual ⟨.Named a, .Named b, rest⟩),
              by simp [facts.flip, named_eq, alloc.vec.Vec.len_val, empty], fun negated same => ?_⟩
            simp only [Option.some.injEq] at same
            subst same
            refine ⟨fun I => ?_, fun I asg => ?_, rfl, by simp [IsKey], by simp [Meaningless]⟩
            · simp only [satisfies, AtLeastTwo.elements, empty, two_equal, two_different, not_not]
            · simp only [satisfies, AtLeastTwo.elements, empty, two_different]
              rfl
      · exact ⟨none, by simp [facts.flip, alloc.vec.Vec.len_val, empty], by simp⟩
    case ObjectPropertyAssertion p a b =>
      cases a with
      | Anonymous a => exact ⟨none, by simp [facts.flip, named_eq], by simp⟩
      | Named a =>
        cases b with
        | Anonymous b => exact ⟨none, by simp [facts.flip, named_eq], by simp⟩
        | Named b =>
          refine ⟨some (.NegativeObjectPropertyAssertion p (.Named a) (.Named b)),
            by simp [facts.flip, named_eq], fun negated same => ?_⟩
          simp only [Option.some.injEq] at same
          subst same
          exact ⟨fun I => Iff.rfl, fun I asg => Iff.rfl, rfl, by simp [IsKey], by simp [Meaningless]⟩
    case NegativeObjectPropertyAssertion p a b =>
      cases a with
      | Anonymous a => exact ⟨none, by simp [facts.flip, named_eq], by simp⟩
      | Named a =>
        cases b with
        | Anonymous b => exact ⟨none, by simp [facts.flip, named_eq], by simp⟩
        | Named b =>
          refine ⟨some (.ObjectPropertyAssertion p (.Named a) (.Named b)),
            by simp [facts.flip, named_eq], fun negated same => ?_⟩
          simp only [Option.some.injEq] at same
          subst same
          exact ⟨fun I => not_not.symm, fun I asg => Iff.rfl, rfl, by simp [IsKey], by simp [Meaningless]⟩
    case DataPropertyAssertion p a lt =>
      cases a with
      | Anonymous a => exact ⟨none, by simp [facts.flip, named_eq], by simp⟩
      | Named a =>
        refine ⟨some (.NegativeDataPropertyAssertion p (.Named a) lt),
          by simp [facts.flip, named_eq], fun negated same => ?_⟩
        simp only [Option.some.injEq] at same
        subst same
        exact ⟨fun I => Iff.rfl, fun I asg => Iff.rfl, rfl, by simp [IsKey], by simp [Meaningless]⟩
    case NegativeDataPropertyAssertion p a lt =>
      cases a with
      | Anonymous a => exact ⟨none, by simp [facts.flip, named_eq], by simp⟩
      | Named a =>
        refine ⟨some (.DataPropertyAssertion p (.Named a) lt),
          by simp [facts.flip, named_eq], fun negated same => ?_⟩
        simp only [Option.some.injEq] at same
        subst same
        exact ⟨fun I => not_not.symm, fun I asg => Iff.rfl, rfl, by simp [IsKey], by simp [Meaningless]⟩
    all_goals exact ⟨none, by simp [facts.flip], by simp⟩

/-! ## The closure with the negation -/

private theorem meaningless_eq (ax : Axiom) : components.meaningless ax = .ok (decide (Meaningless ax)) := by
  cases ax <;> simp [components.meaningless, Meaningless]

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- `meaningful` copies exactly the axioms that mean something. -/
theorem meaningful_spec (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ r, facts.meaningful items index out = .ok r ∧ ∀ v, r = some v →
      (∀ y ∈ v.val, y ∈ out.val ∨ ∃ x ∈ items.val.drop index.val, ¬ Meaningless x.axiom ∧ y.axiom = x.axiom) ∧
      (∀ x ∈ items.val.drop index.val, ¬ Meaningless x.axiom → ∃ y ∈ v.val, y.axiom = x.axiom) ∧
      (∀ y ∈ out.val, y ∈ v.val) := by
  rw [facts.meaningful]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    by_cases meaningless : Meaningless items.val[index.val].axiom
    · obtain ⟨r, run, known⟩ := meaningful_spec items next out
      refine ⟨r, by simp [UScalar.lt_equiv, more, lookup, meaningless_eq, meaningless, advance, run],
        fun v same => ?_⟩
      obtain ⟨sub, sup, keep⟩ := known v same
      rw [nextIs] at sub sup
      refine ⟨fun y my => ?_, fun x mx kx => ?_, keep⟩
      · rcases sub y my with inOut | ⟨x, mx, kx, ax⟩
        · exact .inl inOut
        · exact .inr ⟨x, by rw [split]; exact List.mem_cons_of_mem _ mx, kx, ax⟩
      · rw [split] at mx
        rcases List.mem_cons.mp mx with rfl | later
        · exact absurd meaningless kx
        · exact sup x later kx
    · rcases Rowl.Components.copy_axiom_spec items.val[index.val].axiom with none' | some'
      · exact ⟨none, by simp [UScalar.lt_equiv, more, lookup, meaningless_eq, meaningless, none'], by simp⟩
      · by_cases room : out.val.length < Usize.max
        · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out
            ({ annotations := alloc.vec.Vec.new Annotation, «axiom» := items.val[index.val].axiom } :
              AnnotatedAxiom) room)
          obtain ⟨r, run, known⟩ := meaningful_spec items next pushed
          refine ⟨r, by simp [UScalar.lt_equiv, more, lookup, meaningless_eq, meaningless, some',
            alloc.vec.Vec.len_val, usize_max_val, room, push, advance, run], fun v same => ?_⟩
          obtain ⟨sub, sup, keep⟩ := known v same
          rw [nextIs] at sub sup
          have fresh : ({ annotations := alloc.vec.Vec.new Annotation, «axiom» := items.val[index.val].axiom } :
              AnnotatedAxiom) ∈ v.val := keep _ (by rw [contents]; simp)
          refine ⟨fun y my => ?_, fun x mx kx' => ?_, fun y my => keep y (by rw [contents]; simp [my])⟩
          · rcases sub y my with inPushed | ⟨x, mx, kx', ax⟩
            · rw [contents] at inPushed
              rcases List.mem_append.mp inPushed with inOut | new
              · exact .inl inOut
              · simp only [List.mem_singleton] at new
                subst new
                exact .inr ⟨_, by rw [split]; exact List.mem_cons_self .., meaningless, rfl⟩
            · exact .inr ⟨x, by rw [split]; exact List.mem_cons_of_mem _ mx, kx', ax⟩
          · rw [split] at mx
            rcases List.mem_cons.mp mx with rfl | later
            · exact ⟨_, fresh, rfl⟩
            · exact sup x later kx'
        · exact ⟨none, by simp [UScalar.lt_equiv, more, lookup, meaningless_eq, meaningless, some',
            alloc.vec.Vec.len_val, usize_max_val, room], by simp⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, more], fun v same => ?_⟩
    cases same
    refine ⟨fun y my => .inl my, fun x mx => ?_, fun y my => my⟩
    rw [List.drop_eq_nil_of_le (by omega)] at mx
    cases mx
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- Consistency part by part when the closure falls apart along its
    assertions, and as a whole otherwise. -/
theorem consistent_closure_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, facts.consistent_closure items = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val → (answer = true ↔ Consistent.{u, max w v, w} D V items.val) := by
  rw [facts.consistent_closure]
  obtain ⟨r1, run1, facts1⟩ := Rowl.Components.consistent_by_parts_correct.{u,v,w} items
  cases r1 with
  | none =>
    obtain ⟨r2, run2, facts2⟩ := Rowl.DataOntology.consistent_correct.{u,v,w} items
    exact ⟨r2, by simp [run1, run2], facts2⟩
  | some b => exact ⟨some b, by simp [run1], facts1⟩

private theorem no_key_individuals {ax : Axiom} (notKey : ¬ IsKey ax) : keyIndividuals ax = [] := by
  cases ax <;> simp_all [IsKey, keyIndividuals]

/-- Entailment of a named fact: when `entails_fact` answers, the answer is
    whether the closure entails the fact, under every datatype map that is the
    OWL 2 map on the datatypes of `datatypes` and for every vocabulary that
    names the individuals of a closure with keys and of the fact. -/
theorem entails_fact_correct (items : alloc.vec.Vec AnnotatedAxiom) (fact : Axiom) :
    ∃ result, facts.entails_fact items fact = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val →
        (Keyed items.val → ∀ a : NamedIndividual, Individual.Named a ∈ axiomIndividuals fact →
          V.individuals (.Named a)) →
        ∀ annotations, (answer = true ↔ Entails.{u, max w v, w} D V items.val [⟨annotations, fact⟩]) := by
  rw [facts.entails_fact]
  obtain ⟨r0, run0, negates0⟩ := negation_spec.{u, max w v} fact
  cases r0 with
  | none => exact ⟨none, by simp [run0], by simp⟩
  | some negated =>
    have negates := negates0 negated rfl
    obtain ⟨-, -, sameIndividuals, notKey, -⟩ := negates
    obtain ⟨r1, run1, known⟩ := meaningful_spec items 0#usize (alloc.vec.Vec.new AnnotatedAxiom)
    simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at known
    cases r1 with
    | none => exact ⟨none, by simp [run0, run1], by simp⟩
    | some closure =>
      obtain ⟨sub0, sup, -⟩ := known closure rfl
      have sub : ∀ y ∈ closure.val, ∃ x ∈ items.val, ¬ Meaningless x.axiom ∧ y.axiom = x.axiom := by
        intro y my
        rcases sub0 y my with fresh | found
        · simp at fresh
        · exact found
      by_cases room : closure.val.length < Usize.max
      · obtain ⟨extended, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec closure
          ({ annotations := alloc.vec.Vec.new Annotation, «axiom» := negated } : AnnotatedAxiom) room)
        obtain ⟨r2, run2, decided⟩ := consistent_closure_correct.{u,v,w} extended
        cases r2 with
        | none => exact ⟨none, by simp [run0, run1, alloc.vec.Vec.len_val, usize_max_val, room, push, run2],
            by simp⟩
        | some answer =>
          refine ⟨some (!answer), by simp [run0, run1, alloc.vec.Vec.len_val, usize_max_val, room, push, run2],
            fun result same => ?_⟩
          simp only [Option.some.injEq] at same
          subst same
          intro Native D N V vocab keyed keyedFact annotations
          have keyedExtended : NamesKeyed V extended.val := by
            intro keyedExt a member
            have keyedItems : Keyed items.val := by
              obtain ⟨item, mItem, key⟩ := keyedExt
              rw [contents] at mItem
              rcases List.mem_append.mp mItem with old | new
              · obtain ⟨x, mx, -, ax⟩ := sub item old
                exact ⟨x, mx, by rw [← ax]; exact key⟩
              · simp only [List.mem_singleton] at new
                subst new
                exact absurd key notKey
            simp only [closureIndividuals, List.mem_flatMap] at member
            obtain ⟨z, mz, mi⟩ := member
            rw [contents] at mz
            rcases List.mem_append.mp mz with old | new
            · obtain ⟨x, mx, -, ax⟩ := sub z old
              refine keyed keyedItems a ?_
              simp only [closureIndividuals, List.mem_flatMap]
              exact ⟨x, mx, by rw [← ax]; exact mi⟩
            · simp only [List.mem_singleton] at new
              subst new
              rw [no_key_individuals notKey, List.append_nil] at mi
              rw [sameIndividuals] at mi
              exact keyedFact keyedItems a mi
          have answerIff := decided answer rfl D N V vocab keyedExtended
          have same : Consistent.{u, max w v, w} D V extended.val ↔
              Consistent.{u, max w v, w} D V (items.val ++ [⟨alloc.vec.Vec.new Annotation, negated⟩]) := by
            constructor
            · intro consistent
              refine consistent_cover (fun x mx meaningful => ?_) consistent
              rcases List.mem_append.mp mx with old | new
              · obtain ⟨y, my, ax⟩ := sup x old meaningful
                exact ⟨y, by rw [contents]; exact List.mem_append_left _ my, ax⟩
              · simp only [List.mem_singleton] at new
                subst new
                exact ⟨_, by rw [contents]; simp, rfl⟩
            · intro consistent
              refine consistent_inside (fun y my => ?_) consistent
              rw [contents] at my
              rcases List.mem_append.mp my with old | new
              · obtain ⟨x, mx, -, ax⟩ := sub y old
                exact ⟨x, List.mem_append_left _ mx, ax.symm⟩
              · simp only [List.mem_singleton] at new
                subst new
                exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
          rw [entails_iff_inconsistent (negates0 negated rfl) annotations (alloc.vec.Vec.new Annotation), ← same,
            ← answerIff]
          cases answer <;> simp
      · exact ⟨none, by simp [run0, run1, alloc.vec.Vec.len_val, usize_max_val, room], by simp⟩

end Rowl.Facts
