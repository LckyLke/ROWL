import Rowl.ShiEquality
import Rowl.Concepts

/-!
The nominals of the ontology queries. A concept mentions the individuals of its
nominals; the checks for nominals and for individuals with a node are exact, and
the individuals of the nominals of the class parts and of the class assertions
get nodes. The completion forest also gets the nominal of every individual at
its node, the members of every inequality outside the nominals of the later
members, and, for every negative object property assertion, the universal
restriction of its property to the complement of the target's nominal at the
source's node: each of these facts is proved to be one of them, and every
individual, inequality and negative assertion is proved to have its facts.
-/
namespace Rowl.ShiNominals
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.AlcOntology (PositionOf positionOf_present positionFrom_absent position_of intern_correct)
open Rowl.Concepts (Correct translate_total_correct copy_individual_identity copy_role_identity)
open Rowl.ShiEquality (RepOf node_of_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v

/-- A named individual, which a reinterpretation of the anonymous individuals
    leaves in place. -/
def IsNamed : Individual → Prop
  | .Named _ => True
  | .Anonymous _ => False

/-- The individuals of the nominals of a concept. -/
def Mentions : concepts.Concept → Individual → Prop
  | .One b, a => a = b
  | .NotOne b, a => a = b
  | .And l r, a => Mentions l a ∨ Mentions r a
  | .Or l r, a => Mentions l a ∨ Mentions r a
  | .Exists _ c, a => Mentions c a
  | .Forall _ c, a => Mentions c a
  | .AtLeast _ _ c, a => Mentions c a
  | .AtMost _ _ c, a => Mentions c a
  | _, _ => False

/-- A nominal occurs, which only the completion forest decides. -/
def Nominal : concepts.Concept → Prop
  | .One _ => True
  | .NotOne _ => True
  | .And a b => Nominal a ∨ Nominal b
  | .Or a b => Nominal a ∨ Nominal b
  | .Exists _ c => Nominal c
  | .Forall _ c => Nominal c
  | .AtLeast _ _ c => Nominal c
  | .AtMost _ _ c => Nominal c
  | _ => False

/-- A concept without nominals mentions no individual. -/
theorem not_mentions (c : concepts.Concept) (none : ¬ Nominal c) (a : Individual) : ¬ Mentions c a := by
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ => simp [Mentions]
  | One _ | NotOne _ => exact absurd trivial none
  | And l r ihl ihr =>
    simp only [Nominal,not_or] at none
    rintro (m | m)
    · exact ihl none.1 m
    · exact ihr none.2 m
  | Or l r ihl ihr =>
    simp only [Nominal,not_or] at none
    rintro (m | m)
    · exact ihl none.1 m
    · exact ihr none.2 m
  | Exists _ c ih => exact ih none
  | Forall _ c ih => exact ih none
  | AtLeast _ _ c ih => exact ih none
  | AtMost _ _ c ih => exact ih none

/-- The nominal check is exact. -/
theorem nominal_correct (c : concepts.Concept) : shi_ontology.nominal c = .ok (decide (Nominal c)) := by
  induction c with
  | Top => rw [shi_ontology.nominal]; simp [Nominal]
  | Bottom => rw [shi_ontology.nominal]; simp [Nominal]
  | Atom k => rw [shi_ontology.nominal]; simp [Nominal]
  | NotAtom k => rw [shi_ontology.nominal]; simp [Nominal]
  | One a => rw [shi_ontology.nominal]; simp [Nominal]
  | NotOne a => rw [shi_ontology.nominal]; simp [Nominal]
  | And a b iha ihb =>
    rw [shi_ontology.nominal]
    by_cases left : Nominal a <;> simp [Nominal,iha,ihb,left]
  | Or a b iha ihb =>
    rw [shi_ontology.nominal]
    by_cases left : Nominal a <;> simp [Nominal,iha,ihb,left]
  | Exists r c ih => rw [shi_ontology.nominal]; simp [Nominal,ih]
  | Forall r c ih => rw [shi_ontology.nominal]; simp [Nominal,ih]
  | AtLeast n r c ih => rw [shi_ontology.nominal]; simp [Nominal,ih]
  | AtMost n r c ih => rw [shi_ontology.nominal]; simp [Nominal,ih]

/-- The nominal check over definitions is exact. -/
theorem definitions_nominal_correct (definitions : alloc.vec.Vec completion.Definition) (index : Usize) :
    shi_ontology.definitions_nominal definitions index =
      .ok (decide (∃ d ∈ definitions.val.drop index.val, Nominal d.concept)) := by
  rw [shi_ontology.definitions_nominal]
  by_cases more : index.val < definitions.val.length
  · have lookup : definitions.index_usize index = .ok definitions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : definitions.val.drop index.val = definitions.val[index.val] :: definitions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := definitions_nominal_correct definitions next
    rw [nextIndex] at rest
    by_cases here : Nominal definitions.val[index.val].concept
    · have found : ∃ d ∈ definitions.val.drop index.val, Nominal d.concept :=
        ⟨_,by rw [split]; exact List.mem_cons_self ..,here⟩
      simp [more,lookup,nominal_correct,here,found]
    · have same : (∃ d ∈ definitions.val.drop index.val, Nominal d.concept) ↔
          ∃ d ∈ definitions.val.drop (index.val+1), Nominal d.concept := by
        rw [split]
        constructor
        · rintro ⟨d,member,nominal⟩
          rcases List.mem_cons.mp member with rfl | later
          · exact absurd nominal here
          · exact ⟨d,later,nominal⟩
        · rintro ⟨d,member,nominal⟩
          exact ⟨d,List.mem_cons_of_mem _ member,nominal⟩
      simp [more,lookup,nominal_correct,here,advance,rest,same]
  · have empty : definitions.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [more,empty]
termination_by definitions.val.length - index.val
decreasing_by omega

/-- The nominal check over facts is exact. -/
theorem facts_nominal_correct (facts : alloc.vec.Vec completion.Fact) (index : Usize) :
    shi_ontology.facts_nominal facts index = .ok (decide (∃ q ∈ facts.val.drop index.val, Nominal q.concept)) := by
  rw [shi_ontology.facts_nominal]
  by_cases more : index.val < facts.val.length
  · have lookup : facts.index_usize index = .ok facts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : facts.val.drop index.val = facts.val[index.val] :: facts.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := facts_nominal_correct facts next
    rw [nextIndex] at rest
    by_cases here : Nominal facts.val[index.val].concept
    · have found : ∃ q ∈ facts.val.drop index.val, Nominal q.concept :=
        ⟨_,by rw [split]; exact List.mem_cons_self ..,here⟩
      simp [more,lookup,nominal_correct,here,found]
    · have same : (∃ q ∈ facts.val.drop index.val, Nominal q.concept) ↔
          ∃ q ∈ facts.val.drop (index.val+1), Nominal q.concept := by
        rw [split]
        constructor
        · rintro ⟨q,member,nominal⟩
          rcases List.mem_cons.mp member with rfl | later
          · exact absurd nominal here
          · exact ⟨q,later,nominal⟩
        · rintro ⟨q,member,nominal⟩
          exact ⟨q,List.mem_cons_of_mem _ member,nominal⟩
      simp [more,lookup,nominal_correct,here,advance,rest,same]
  · have empty : facts.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [more,empty]
termination_by facts.val.length - index.val
decreasing_by omega

/-- Whether the TBox concept, a definition or a fact has a nominal, exactly. -/
theorem closure_nominal_correct (parts : shi_ontology.Parts) (facts : alloc.vec.Vec completion.Fact) :
    shi_ontology.closure_nominal parts facts = .ok (decide (Nominal parts.axioms ∨
      (∃ d ∈ parts.definitions.val, Nominal d.concept) ∨ ∃ q ∈ facts.val, Nominal q.concept)) := by
  have definitions := definitions_nominal_correct parts.definitions 0#usize
  have facts' := facts_nominal_correct facts 0#usize
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at definitions facts'
  rw [shi_ontology.closure_nominal]
  by_cases one : Nominal parts.axioms
  · simp [nominal_correct,one]
  · by_cases two : ∃ d ∈ parts.definitions.val, Nominal d.concept
    · simp [nominal_correct,one,definitions,two]
    · simp only [nominal_correct,decide_eq_false one,Bool.false_eq_true,↓reduceIte,bind_ok,definitions,
        decide_eq_false two,facts']
      simp [one,two]

/-- An individual has a node exactly when it is among the nodes. -/
theorem positionOf_ne_zero (nodes : List Individual) (a : Individual) : PositionOf nodes a ≠ 0 ↔ a ∈ nodes := by
  constructor
  · intro nonzero
    by_contra absent
    exact nonzero (by simpa [PositionOf] using positionFrom_absent nodes a 0 absent)
  · intro present
    obtain ⟨_,positive,_⟩ := positionOf_present nodes a present
    omega

private theorem position_known (nodes : alloc.vec.Vec Individual) (b : Individual) :
    (do let i ← alc_ontology.position nodes b 0#usize; ok (i != 0#usize)) =
      (.ok (decide (∀ a, a = b → a ∈ nodes.val)) : Result Bool) := by
  obtain ⟨p,run,value⟩ := position_of nodes b
  have iff : (∀ a, a = b → a ∈ nodes.val) ↔ b ∈ nodes.val := ⟨fun all => all b rfl,fun present a same => same ▸ present⟩
  by_cases present : b ∈ nodes.val
  · have nonzero : p ≠ 0#usize := by
      intro zero
      have := (positionOf_ne_zero nodes.val b).mpr present
      rw [← value,zero] at this
      exact this rfl
    simp [run,nonzero,iff,present]
  · have zero : p = 0#usize := by
      apply UScalar.eq_of_val_eq
      have := (positionOf_ne_zero nodes.val b).not.mpr present
      rw [value]
      simpa using this
    simp [run,zero,iff,present]

/-- The check that the individual of every nominal has a node is exact. -/
theorem known_correct (nodes : alloc.vec.Vec Individual) (c : concepts.Concept) :
    shi_ontology.known nodes c = .ok (decide (∀ a, Mentions c a → a ∈ nodes.val)) := by
  induction c with
  | Top => rw [shi_ontology.known]; simp [Mentions]
  | Bottom => rw [shi_ontology.known]; simp [Mentions]
  | Atom k => rw [shi_ontology.known]; simp [Mentions]
  | NotAtom k => rw [shi_ontology.known]; simp [Mentions]
  | One b => rw [shi_ontology.known]; exact position_known nodes b
  | NotOne b => rw [shi_ontology.known]; exact position_known nodes b
  | And l r ihl ihr =>
    rw [shi_ontology.known]
    have iff : (∀ a, Mentions (.And l r) a → a ∈ nodes.val) ↔
        (∀ a, Mentions l a → a ∈ nodes.val) ∧ ∀ a, Mentions r a → a ∈ nodes.val :=
      ⟨fun all => ⟨fun a m => all a (.inl m),fun a m => all a (.inr m)⟩,
        fun both a m => m.elim (both.1 a) (both.2 a)⟩
    by_cases left : ∀ a, Mentions l a → a ∈ nodes.val
    · simp only [ihl,decide_eq_true left,bind_ok,↓reduceIte,ihr]
      exact congrArg _ (decide_eq_decide.mpr (by rw [iff]; exact ⟨fun right => ⟨left,right⟩,fun both => both.2⟩))
    · simp only [ihl,decide_eq_false left,bind_ok,Bool.false_eq_true,↓reduceIte]
      exact congrArg _ (decide_eq_false (by rw [iff]; exact fun both => left both.1)).symm
  | Or l r ihl ihr =>
    rw [shi_ontology.known]
    have iff : (∀ a, Mentions (.Or l r) a → a ∈ nodes.val) ↔
        (∀ a, Mentions l a → a ∈ nodes.val) ∧ ∀ a, Mentions r a → a ∈ nodes.val :=
      ⟨fun all => ⟨fun a m => all a (.inl m),fun a m => all a (.inr m)⟩,
        fun both a m => m.elim (both.1 a) (both.2 a)⟩
    by_cases left : ∀ a, Mentions l a → a ∈ nodes.val
    · simp only [ihl,decide_eq_true left,bind_ok,↓reduceIte,ihr]
      exact congrArg _ (decide_eq_decide.mpr (by rw [iff]; exact ⟨fun right => ⟨left,right⟩,fun both => both.2⟩))
    · simp only [ihl,decide_eq_false left,bind_ok,Bool.false_eq_true,↓reduceIte]
      exact congrArg _ (decide_eq_false (by rw [iff]; exact fun both => left both.1)).symm
  | Exists r c ih => rw [shi_ontology.known]; exact ih
  | Forall r c ih => rw [shi_ontology.known]; exact ih
  | AtLeast n r c ih => rw [shi_ontology.known]; exact ih
  | AtMost n r c ih => rw [shi_ontology.known]; exact ih

/-- The check over facts that the individual of every nominal has a node is exact. -/
theorem facts_known_correct (nodes : alloc.vec.Vec Individual) (facts : alloc.vec.Vec completion.Fact)
    (index : Usize) :
    shi_ontology.facts_known nodes facts index =
      .ok (decide (∀ q ∈ facts.val.drop index.val, ∀ a, Mentions q.concept a → a ∈ nodes.val)) := by
  rw [shi_ontology.facts_known]
  by_cases more : index.val < facts.val.length
  · have lookup : facts.index_usize index = .ok facts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : facts.val.drop index.val = facts.val[index.val] :: facts.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := facts_known_correct nodes facts next
    rw [nextIndex] at rest
    rw [split]
    simp only [List.forall_mem_cons]
    by_cases here : ∀ a, Mentions facts.val[index.val].concept a → a ∈ nodes.val
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,known_correct,decide_eq_true here,advance,rest]
      exact congrArg _ (decide_eq_decide.mpr ⟨fun later => ⟨here,later⟩,fun both => both.2⟩)
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,known_correct,decide_eq_false here,Bool.false_eq_true]
      exact congrArg _ (decide_eq_decide.mpr ⟨False.elim,fun both => here both.1⟩)
  · have empty : facts.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [more,empty]
termination_by facts.val.length - index.val
decreasing_by omega

/-! ### Nodes for the individuals of nominals -/

/-- Interning the individuals of the nominals of a concept keeps every node,
    adds each of them, and leaves room for one more node. -/
theorem nominal_individuals_correct (c : concepts.Concept) :
    ∀ (nodes : alloc.vec.Vec Individual), nodes.val.length ≤ Usize.max-1 →
      ∃ r, shi_ontology.nominal_individuals nodes c = .ok r ∧ ∀ final, r = some final →
        (∀ b ∈ nodes.val, b ∈ final.val) ∧ (∀ a, Mentions c a → a ∈ final.val) ∧
        final.val.length ≤ Usize.max-1 := by
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ =>
    intro nodes room
    refine ⟨some nodes,by rw [shi_ontology.nominal_individuals],?_⟩
    intro final same
    cases same
    exact ⟨fun b member => member,by simp [Mentions],room⟩
  | One b =>
    intro nodes room
    obtain ⟨r,run,spec⟩ := intern_correct nodes b room
    refine ⟨r,by rw [shi_ontology.nominal_individuals]; exact run,?_⟩
    intro final same
    obtain ⟨kept,added,finalRoom⟩ := spec final same
    refine ⟨kept,?_,finalRoom⟩
    intro a mentioned
    simp only [Mentions] at mentioned
    rw [mentioned]
    exact added
  | NotOne b =>
    intro nodes room
    obtain ⟨r,run,spec⟩ := intern_correct nodes b room
    refine ⟨r,by rw [shi_ontology.nominal_individuals]; exact run,?_⟩
    intro final same
    obtain ⟨kept,added,finalRoom⟩ := spec final same
    refine ⟨kept,?_,finalRoom⟩
    intro a mentioned
    simp only [Mentions] at mentioned
    rw [mentioned]
    exact added
  | And l r ihl ihr =>
    intro nodes room
    obtain ⟨r1,run1,spec1⟩ := ihl nodes room
    cases r1 with
    | none =>
      exact ⟨none,by rw [shi_ontology.nominal_individuals]; simp [run1],by intro final impossible; cases impossible⟩
    | some middle =>
      obtain ⟨kept1,added1,room1⟩ := spec1 middle rfl
      obtain ⟨r2,run2,spec2⟩ := ihr middle room1
      refine ⟨r2,by rw [shi_ontology.nominal_individuals]; simp [run1,run2],?_⟩
      intro final same
      obtain ⟨kept2,added2,room2⟩ := spec2 final same
      refine ⟨fun b member => kept2 b (kept1 b member),?_,room2⟩
      rintro a (mentioned | mentioned)
      · exact kept2 a (added1 a mentioned)
      · exact added2 a mentioned
  | Or l r ihl ihr =>
    intro nodes room
    obtain ⟨r1,run1,spec1⟩ := ihl nodes room
    cases r1 with
    | none =>
      exact ⟨none,by rw [shi_ontology.nominal_individuals]; simp [run1],by intro final impossible; cases impossible⟩
    | some middle =>
      obtain ⟨kept1,added1,room1⟩ := spec1 middle rfl
      obtain ⟨r2,run2,spec2⟩ := ihr middle room1
      refine ⟨r2,by rw [shi_ontology.nominal_individuals]; simp [run1,run2],?_⟩
      intro final same
      obtain ⟨kept2,added2,room2⟩ := spec2 final same
      refine ⟨fun b member => kept2 b (kept1 b member),?_,room2⟩
      rintro a (mentioned | mentioned)
      · exact kept2 a (added1 a mentioned)
      · exact added2 a mentioned
  | Exists _ c ih =>
    intro nodes room
    obtain ⟨r,run,spec⟩ := ih nodes room
    exact ⟨r,by rw [shi_ontology.nominal_individuals]; exact run,spec⟩
  | Forall _ c ih =>
    intro nodes room
    obtain ⟨r,run,spec⟩ := ih nodes room
    exact ⟨r,by rw [shi_ontology.nominal_individuals]; exact run,spec⟩
  | AtLeast _ _ c ih =>
    intro nodes room
    obtain ⟨r,run,spec⟩ := ih nodes room
    exact ⟨r,by rw [shi_ontology.nominal_individuals]; exact run,spec⟩
  | AtMost _ _ c ih =>
    intro nodes room
    obtain ⟨r,run,spec⟩ := ih nodes room
    exact ⟨r,by rw [shi_ontology.nominal_individuals]; exact run,spec⟩

/-- Interning the individuals of the nominals of the definitions keeps every
    node, adds each of them, and leaves room for one more node. -/
theorem definition_individuals_correct (definitions : alloc.vec.Vec completion.Definition) (index : Usize)
    (nodes : alloc.vec.Vec Individual) (room : nodes.val.length ≤ Usize.max-1) :
    ∃ r, shi_ontology.definition_individuals nodes definitions index = .ok r ∧ ∀ final, r = some final →
      (∀ b ∈ nodes.val, b ∈ final.val) ∧
      (∀ d ∈ definitions.val.drop index.val, ∀ a, Mentions d.concept a → a ∈ final.val) ∧
      final.val.length ≤ Usize.max-1 := by
  rw [shi_ontology.definition_individuals]
  by_cases more : index.val < definitions.val.length
  · have lookup : definitions.index_usize index = .ok definitions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : definitions.val.drop index.val = definitions.val[index.val] :: definitions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨r1,run1,spec1⟩ := nominal_individuals_correct definitions.val[index.val].concept nodes room
    cases r1 with
    | none =>
      exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,run1],
        by intro final impossible; cases impossible⟩
    | some middle =>
      obtain ⟨kept1,added1,room1⟩ := spec1 middle rfl
      obtain ⟨r,run,spec⟩ := definition_individuals_correct definitions next middle room1
      refine ⟨r,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,run1,advance,run],?_⟩
      intro final same
      obtain ⟨kept,added,finalRoom⟩ := spec final same
      refine ⟨fun b member => kept b (kept1 b member),?_,finalRoom⟩
      intro d member a mentioned
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact kept a (added1 a mentioned)
      · rw [nextIndex] at added
        exact added d later a mentioned
  · have empty : definitions.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some nodes,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro final same
    cases same
    exact ⟨fun b member => member,by simp [empty],room⟩
termination_by definitions.val.length - index.val
decreasing_by omega

/-- Interning the individuals of the nominals of the concept of a class
    expression keeps every node, adds each of them, and leaves room for one more
    node. -/
theorem class_individuals_correct (nodes : alloc.vec.Vec Individual) (C : ClassExpression)
    (room : nodes.val.length ≤ Usize.max-1) :
    ∃ r, shi_ontology.class_individuals nodes C = .ok r ∧ ∀ final, r = some final →
      (∀ b ∈ nodes.val, b ∈ final.val) ∧
      (∀ concept, concepts.translate C true = .ok (some concept) → ∀ a, Mentions concept a → a ∈ final.val) ∧
      final.val.length ≤ Usize.max-1 := by
  rw [shi_ontology.class_individuals]
  obtain ⟨translated,translatedRead,_⟩ := translate_total_correct.{0,0} C true
  cases translated with
  | none => exact ⟨none,by simp [translatedRead],by intro final impossible; cases impossible⟩
  | some concept =>
    obtain ⟨r,run,spec⟩ := nominal_individuals_correct concept nodes room
    refine ⟨r,by simp [translatedRead,run],?_⟩
    intro final same
    obtain ⟨kept,added,finalRoom⟩ := spec final same
    refine ⟨kept,?_,finalRoom⟩
    intro concept' read a mentioned
    rw [translatedRead] at read
    cases Result.ok_injective read
    exact added a mentioned

/-- Interning the individuals of the nominals of the class assertions keeps every
    node, adds each of them, and leaves room for one more node. -/
theorem assertion_individuals_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize)
    (nodes : alloc.vec.Vec Individual) (room : nodes.val.length ≤ Usize.max-1) :
    ∃ r, shi_ontology.assertion_individuals items index nodes = .ok r ∧ ∀ final, r = some final →
      (∀ b ∈ nodes.val, b ∈ final.val) ∧
      (∀ item ∈ items.val.drop index.val, ∀ C m, item.axiom = .ClassAssertion C m → ∀ concept,
        concepts.translate C true = .ok (some concept) → ∀ a, Mentions concept a → a ∈ final.val) ∧
      final.val.length ≤ Usize.max-1 := by
  rw [shi_ontology.assertion_individuals]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have tail : ∀ middle : alloc.vec.Vec Individual, (∀ b ∈ nodes.val, b ∈ middle.val) →
        (∀ C m, items.val[index.val].axiom = .ClassAssertion C m → ∀ concept,
          concepts.translate C true = .ok (some concept) → ∀ a, Mentions concept a → a ∈ middle.val) →
        middle.val.length ≤ Usize.max-1 →
        ∃ r, shi_ontology.assertion_individuals items next middle = .ok r ∧ ∀ final, r = some final →
          (∀ b ∈ nodes.val, b ∈ final.val) ∧
          (∀ item ∈ items.val.drop index.val, ∀ C m, item.axiom = .ClassAssertion C m → ∀ concept,
            concepts.translate C true = .ok (some concept) → ∀ a, Mentions concept a → a ∈ final.val) ∧
          final.val.length ≤ Usize.max-1 := by
      intro middle kept here middleRoom
      obtain ⟨r,run,spec⟩ := assertion_individuals_correct items next middle middleRoom
      refine ⟨r,run,?_⟩
      intro final same
      obtain ⟨kept',later,finalRoom⟩ := spec final same
      refine ⟨fun b member => kept' b (kept b member),?_,finalRoom⟩
      intro item member C m statement concept read a mentioned
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | rest
      · exact kept' a (here C m statement concept read a mentioned)
      · rw [nextIndex] at later
        exact later item rest C m statement concept read a mentioned
    cases item : items.val[index.val].axiom with
    | ClassAssertion C m =>
      obtain ⟨middle,middleRun,middleSpec⟩ := class_individuals_correct nodes C room
      cases middle with
      | none => exact ⟨none,by simp [more,lookup,item,middleRun],by intro final impossible; cases impossible⟩
      | some middle =>
        obtain ⟨kept,added,middleRoom⟩ := middleSpec middle rfl
        obtain ⟨r,run,spec⟩ := tail middle kept (by
          intro C' m' statement concept read a mentioned
          rw [item] at statement
          simp only [Axiom.ClassAssertion.injEq] at statement
          obtain ⟨rfl,rfl⟩ := statement
          exact added concept read a mentioned) middleRoom
        exact ⟨r,by simp [more,lookup,item,middleRun,advance,run],spec⟩
    | _ =>
      obtain ⟨r,run,spec⟩ := tail nodes (fun b member => member) (by
        intro C m statement
        rw [item] at statement
        cases statement) room
      exact ⟨r,by simp [more,lookup,item,advance,run],spec⟩
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some nodes,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro final same
    cases same
    exact ⟨fun b member => member,by simp [empty],room⟩
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-! ### The facts the completion forest also gets -/

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- Adding a fact appends it when there is room. -/
theorem add_fact_correct (facts : alloc.vec.Vec completion.Fact) (node : Usize) (concept : concepts.Concept) :
    ∃ r, shi_ontology.add_fact facts node concept = .ok r ∧ ∀ final, r = some final →
      final.val = facts.val ++ [⟨node,concept⟩] := by
  rw [shi_ontology.add_fact]
  by_cases fits : facts.val.length < Usize.max
  · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec facts ⟨node,concept⟩ fits)
    refine ⟨some appended,by simp [usize_max_val,fits,push],?_⟩
    intro final same
    cases same
    exact contents
  · exact ⟨none,by simp [usize_max_val,fits],by intro final impossible; cases impossible⟩

/-- The nominal of every individual from `index` on at its node: every fact is
    given or such a nominal, and every such individual has its nominal. -/
theorem named_from_correct (nodes : alloc.vec.Vec Individual) (same : alloc.vec.Vec Usize) (index : Usize)
    (facts : alloc.vec.Vec completion.Fact) :
    ∃ r, shi_ontology.named_from nodes same index facts = .ok r ∧ ∀ final, r = some final →
      (∀ q ∈ final.val, q ∈ facts.val ∨ ∃ a ∈ nodes.val.drop index.val,
        q.node.val = RepOf same.val nodes.val a ∧ q.concept = .One a) ∧
      (∀ q ∈ facts.val, q ∈ final.val) ∧
      (∀ a ∈ nodes.val.drop index.val, ∃ q ∈ final.val,
        q.node.val = RepOf same.val nodes.val a ∧ q.concept = .One a) := by
  rw [shi_ontology.named_from]
  by_cases more : index.val < nodes.val.length
  · have lookup : nodes.index_usize index = .ok nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : nodes.val.drop index.val = nodes.val[index.val] :: nodes.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨node,nodeRun,nodeValue⟩ := node_of_correct nodes same nodes.val[index.val]
    obtain ⟨added,addRun,addSpec⟩ := add_fact_correct facts node (.One nodes.val[index.val])
    cases added with
    | none =>
      exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,nodeRun,copy_individual_identity,
        addRun],by intro final impossible; cases impossible⟩
    | some middle =>
      have middleIs := addSpec middle rfl
      obtain ⟨r,run,spec⟩ := named_from_correct nodes same next middle
      refine ⟨r,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,nodeRun,copy_individual_identity,
        addRun,advance,run],?_⟩
      intro final finalIs
      obtain ⟨origin,kept,covered⟩ := spec final finalIs
      rw [nextIndex] at origin covered
      refine ⟨?_,fun q member => kept q (by rw [middleIs]; exact List.mem_append_left _ member),?_⟩
      · intro q member
        rcases origin q member with fromMiddle | ⟨a,aIn,qNode,qConcept⟩
        · rw [middleIs] at fromMiddle
          rcases List.mem_append.mp fromMiddle with old | new
          · exact .inl old
          · rw [List.mem_singleton] at new
            subst new
            exact .inr ⟨nodes.val[index.val],by rw [split]; exact List.mem_cons_self ..,nodeValue,rfl⟩
        · exact .inr ⟨a,by rw [split]; exact List.mem_cons_of_mem _ aIn,qNode,qConcept⟩
      · intro a member
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨⟨node,.One nodes.val[index.val]⟩,
            kept _ (by rw [middleIs]; exact List.mem_append_right _ (List.mem_singleton_self _)),nodeValue,rfl⟩
        · exact covered a later
  · have empty : nodes.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some facts,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro final same
    cases same
    exact ⟨fun q member => .inl member,fun q member => member,by simp [empty]⟩
termination_by nodes.val.length - index.val
decreasing_by omega

/-- A member outside the nominals of the individuals from `index` on: every fact
    is given or such a complement at the member's node, and every such
    individual has its complement there. -/
theorem apart_rest_correct (nodes : alloc.vec.Vec Individual) (same : alloc.vec.Vec Usize) (member : Individual)
    (rest : alloc.vec.Vec Individual) (index : Usize) (facts : alloc.vec.Vec completion.Fact) :
    ∃ r, shi_ontology.apart_rest nodes same member rest index facts = .ok r ∧ ∀ final, r = some final →
      (∀ q ∈ final.val, q ∈ facts.val ∨ ∃ b ∈ rest.val.drop index.val,
        q.node.val = RepOf same.val nodes.val member ∧ q.concept = .NotOne b) ∧
      (∀ q ∈ facts.val, q ∈ final.val) ∧
      (∀ b ∈ rest.val.drop index.val, ∃ q ∈ final.val,
        q.node.val = RepOf same.val nodes.val member ∧ q.concept = .NotOne b) := by
  rw [shi_ontology.apart_rest]
  by_cases more : index.val < rest.val.length
  · have lookup : rest.index_usize index = .ok rest.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : rest.val.drop index.val = rest.val[index.val] :: rest.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨node,nodeRun,nodeValue⟩ := node_of_correct nodes same member
    obtain ⟨added,addRun,addSpec⟩ := add_fact_correct facts node (.NotOne rest.val[index.val])
    cases added with
    | none =>
      exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,nodeRun,copy_individual_identity,
        addRun],by intro final impossible; cases impossible⟩
    | some middle =>
      have middleIs := addSpec middle rfl
      obtain ⟨r,run,spec⟩ := apart_rest_correct nodes same member rest next middle
      refine ⟨r,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,nodeRun,copy_individual_identity,
        addRun,advance,run],?_⟩
      intro final finalIs
      obtain ⟨origin,kept,covered⟩ := spec final finalIs
      rw [nextIndex] at origin covered
      refine ⟨?_,fun q inFacts => kept q (by rw [middleIs]; exact List.mem_append_left _ inFacts),?_⟩
      · intro q inFinal
        rcases origin q inFinal with fromMiddle | ⟨b,bIn,qNode,qConcept⟩
        · rw [middleIs] at fromMiddle
          rcases List.mem_append.mp fromMiddle with old | new
          · exact .inl old
          · rw [List.mem_singleton] at new
            subst new
            exact .inr ⟨rest.val[index.val],by rw [split]; exact List.mem_cons_self ..,nodeValue,rfl⟩
        · exact .inr ⟨b,by rw [split]; exact List.mem_cons_of_mem _ bIn,qNode,qConcept⟩
      · intro b inRest
        rw [split] at inRest
        rcases List.mem_cons.mp inRest with rfl | later
        · exact ⟨⟨node,.NotOne rest.val[index.val]⟩,
            kept _ (by rw [middleIs]; exact List.mem_append_right _ (List.mem_singleton_self _)),nodeValue,rfl⟩
        · exact covered b later
  · have empty : rest.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some facts,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro final same
    cases same
    exact ⟨fun q inFacts => .inl inFacts,fun q inFacts => inFacts,by simp [empty]⟩
termination_by rest.val.length - index.val
decreasing_by omega

/-- The individuals from `index` on outside the nominals of the later ones: every
    fact is given or such a complement for two of them in order, and every two
    of them in order have their complement. -/
theorem apart_within_correct (nodes : alloc.vec.Vec Individual) (same : alloc.vec.Vec Usize)
    (rest : alloc.vec.Vec Individual) (index : Usize) (facts : alloc.vec.Vec completion.Fact) :
    ∃ r, shi_ontology.apart_within nodes same rest index facts = .ok r ∧ ∀ final, r = some final →
      (∀ q ∈ final.val, q ∈ facts.val ∨ ∃ a b, [a,b].Sublist (rest.val.drop index.val) ∧
        q.node.val = RepOf same.val nodes.val a ∧ q.concept = .NotOne b) ∧
      (∀ q ∈ facts.val, q ∈ final.val) ∧
      (rest.val.drop index.val).Pairwise (fun a b => ∃ q ∈ final.val,
        q.node.val = RepOf same.val nodes.val a ∧ q.concept = .NotOne b) := by
  rw [shi_ontology.apart_within]
  by_cases more : index.val < rest.val.length
  · have lookup : rest.index_usize index = .ok rest.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : rest.val.drop index.val = rest.val[index.val] :: rest.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨r1,run1,spec1⟩ := apart_rest_correct nodes same rest.val[index.val] rest next facts
    rw [nextIndex] at spec1
    cases r1 with
    | none =>
      exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,advance,run1],
        by intro final impossible; cases impossible⟩
    | some middle =>
      obtain ⟨origin1,kept1,covered1⟩ := spec1 middle rfl
      obtain ⟨r,run,spec⟩ := apart_within_correct nodes same rest next middle
      refine ⟨r,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,advance,run1,run],?_⟩
      intro final finalIs
      obtain ⟨origin,kept,covered⟩ := spec final finalIs
      rw [nextIndex] at origin covered
      refine ⟨?_,fun q inFacts => kept q (kept1 q inFacts),?_⟩
      · intro q inFinal
        rcases origin q inFinal with fromMiddle | ⟨a,b,sub,qNode,qConcept⟩
        · rcases origin1 q fromMiddle with old | ⟨b,bIn,qNode,qConcept⟩
          · exact .inl old
          · refine .inr ⟨rest.val[index.val],b,?_,qNode,qConcept⟩
            rw [split]
            exact List.Sublist.cons_cons _ (List.singleton_sublist.mpr bIn)
        · refine .inr ⟨a,b,?_,qNode,qConcept⟩
          rw [split]
          exact List.Sublist.cons _ sub
      · rw [split,List.pairwise_cons]
        refine ⟨?_,covered⟩
        intro b bIn
        obtain ⟨q,qIn,qNode,qConcept⟩ := covered1 b bIn
        exact ⟨q,kept q qIn,qNode,qConcept⟩
  · have empty : rest.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some facts,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro final same
    cases same
    refine ⟨fun q inFacts => .inl inFacts,fun q inFacts => inFacts,?_⟩
    rw [empty]
    exact List.Pairwise.nil
termination_by rest.val.length - index.val
decreasing_by omega

/-- The members of an inequality outside the nominals of the later members:
    every fact is given or such a complement for two members in order, and
    every two members in order have their complement. -/
theorem apart_members_correct (nodes : alloc.vec.Vec Individual) (same : alloc.vec.Vec Usize)
    (xs : AtLeastTwo Individual) (facts : alloc.vec.Vec completion.Fact) :
    ∃ r, shi_ontology.apart_members nodes same xs facts = .ok r ∧ ∀ final, r = some final →
      (∀ q ∈ final.val, q ∈ facts.val ∨ ∃ a b, [a,b].Sublist xs.elements ∧
        q.node.val = RepOf same.val nodes.val a ∧ q.concept = .NotOne b) ∧
      (∀ q ∈ facts.val, q ∈ final.val) ∧
      xs.elements.Pairwise (fun a b => ∃ q ∈ final.val,
        q.node.val = RepOf same.val nodes.val a ∧ q.concept = .NotOne b) := by
  rw [shi_ontology.apart_members]
  have zero : (0#usize).val = 0 := rfl
  obtain ⟨node,nodeRun,nodeValue⟩ := node_of_correct nodes same xs.first
  obtain ⟨added,addRun,addSpec⟩ := add_fact_correct facts node (.NotOne xs.second)
  cases added with
  | none =>
    exact ⟨none,by simp [nodeRun,copy_individual_identity,addRun],by intro final impossible; cases impossible⟩
  | some one =>
  have oneIs := addSpec one rfl
  obtain ⟨r2,run2,spec2⟩ := apart_rest_correct nodes same xs.first xs.rest 0#usize one
  cases r2 with
  | none =>
    exact ⟨none,by simp [nodeRun,copy_individual_identity,addRun,run2],by intro final impossible; cases impossible⟩
  | some two =>
  obtain ⟨origin2,kept2,covered2⟩ := spec2 two rfl
  obtain ⟨r3,run3,spec3⟩ := apart_rest_correct nodes same xs.second xs.rest 0#usize two
  cases r3 with
  | none =>
    exact ⟨none,by simp [nodeRun,copy_individual_identity,addRun,run2,run3],
      by intro final impossible; cases impossible⟩
  | some three =>
  obtain ⟨origin3,kept3,covered3⟩ := spec3 three rfl
  obtain ⟨r4,run4,spec4⟩ := apart_within_correct nodes same xs.rest 0#usize three
  refine ⟨r4,by simp [nodeRun,copy_individual_identity,addRun,run2,run3,run4],?_⟩
  intro final finalIs
  obtain ⟨origin4,kept4,covered4⟩ := spec4 final finalIs
  rw [zero,List.drop_zero] at origin2 covered2 origin3 covered3 origin4 covered4
  have elementsIs : xs.elements = xs.first :: xs.second :: xs.rest.val := rfl
  refine ⟨?_,fun q inFacts => kept4 q (kept3 q (kept2 q (by rw [oneIs]; exact List.mem_append_left _ inFacts))),?_⟩
  · intro q inFinal
    rcases origin4 q inFinal with from3 | ⟨a,b,sub,qNode,qConcept⟩
    · rcases origin3 q from3 with from2 | ⟨b,bIn,qNode,qConcept⟩
      · rcases origin2 q from2 with from1 | ⟨b,bIn,qNode,qConcept⟩
        · rw [oneIs] at from1
          rcases List.mem_append.mp from1 with old | new
          · exact .inl old
          · rw [List.mem_singleton] at new
            subst new
            refine .inr ⟨xs.first,xs.second,?_,nodeValue,rfl⟩
            rw [elementsIs]
            exact List.Sublist.cons_cons _ (List.Sublist.cons_cons _ (List.nil_sublist _))
        · refine .inr ⟨xs.first,b,?_,qNode,qConcept⟩
          rw [elementsIs]
          exact List.Sublist.cons_cons _ (List.Sublist.cons _ (List.singleton_sublist.mpr bIn))
      · refine .inr ⟨xs.second,b,?_,qNode,qConcept⟩
        rw [elementsIs]
        exact List.Sublist.cons _ (List.Sublist.cons_cons _ (List.singleton_sublist.mpr bIn))
    · refine .inr ⟨a,b,?_,qNode,qConcept⟩
      rw [elementsIs]
      exact List.Sublist.cons _ (List.Sublist.cons _ sub)
  · rw [elementsIs,List.pairwise_cons,List.pairwise_cons]
    refine ⟨?_,?_,covered4⟩
    · intro b bIn
      rcases List.mem_cons.mp bIn with rfl | later
      · exact ⟨⟨node,.NotOne xs.second⟩,
          kept4 _ (kept3 _ (kept2 _ (by rw [oneIs]; exact List.mem_append_right _ (List.mem_singleton_self _)))),
          nodeValue,rfl⟩
      · obtain ⟨q,qIn,qNode,qConcept⟩ := covered2 b later
        exact ⟨q,kept4 q (kept3 q qIn),qNode,qConcept⟩
    · intro b bIn
      obtain ⟨q,qIn,qNode,qConcept⟩ := covered3 b bIn
      exact ⟨q,kept4 q qIn,qNode,qConcept⟩

/-- The members of every inequality from `index` on apart: every fact is given
    or such a complement for two members of an inequality in order, and the
    members of every inequality in order have their complements. -/
theorem unequal_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (same : alloc.vec.Vec Usize) (index : Usize) (facts : alloc.vec.Vec completion.Fact) :
    ∃ r, shi_ontology.unequal_from items nodes same index facts = .ok r ∧ ∀ final, r = some final →
      (∀ q ∈ final.val, q ∈ facts.val ∨ ∃ item ∈ items.val.drop index.val, ∃ xs,
        item.axiom = .DifferentIndividuals xs ∧ ∃ a b, [a,b].Sublist xs.elements ∧
          q.node.val = RepOf same.val nodes.val a ∧ q.concept = .NotOne b) ∧
      (∀ q ∈ facts.val, q ∈ final.val) ∧
      (∀ item ∈ items.val.drop index.val, ∀ xs, item.axiom = .DifferentIndividuals xs →
        xs.elements.Pairwise (fun a b => ∃ q ∈ final.val,
          q.node.val = RepOf same.val nodes.val a ∧ q.concept = .NotOne b)) := by
  rw [shi_ontology.unequal_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have tail : ∀ middle : alloc.vec.Vec completion.Fact,
        (∀ q ∈ middle.val, q ∈ facts.val ∨ ∃ xs, items.val[index.val].axiom = .DifferentIndividuals xs ∧
          ∃ a b, [a,b].Sublist xs.elements ∧ q.node.val = RepOf same.val nodes.val a ∧ q.concept = .NotOne b) →
        (∀ q ∈ facts.val, q ∈ middle.val) →
        (∀ xs, items.val[index.val].axiom = .DifferentIndividuals xs →
          xs.elements.Pairwise (fun a b => ∃ q ∈ middle.val,
            q.node.val = RepOf same.val nodes.val a ∧ q.concept = .NotOne b)) →
        ∃ r, shi_ontology.unequal_from items nodes same next middle = .ok r ∧ ∀ final, r = some final →
          (∀ q ∈ final.val, q ∈ facts.val ∨ ∃ item ∈ items.val.drop index.val, ∃ xs,
            item.axiom = .DifferentIndividuals xs ∧ ∃ a b, [a,b].Sublist xs.elements ∧
              q.node.val = RepOf same.val nodes.val a ∧ q.concept = .NotOne b) ∧
          (∀ q ∈ facts.val, q ∈ final.val) ∧
          (∀ item ∈ items.val.drop index.val, ∀ xs, item.axiom = .DifferentIndividuals xs →
            xs.elements.Pairwise (fun a b => ∃ q ∈ final.val,
              q.node.val = RepOf same.val nodes.val a ∧ q.concept = .NotOne b)) := by
      intro middle origin1 kept1 covered1
      obtain ⟨r,run,spec⟩ := unequal_from_correct items nodes same next middle
      refine ⟨r,run,?_⟩
      intro final finalIs
      obtain ⟨origin,kept,covered⟩ := spec final finalIs
      rw [nextIndex] at origin covered
      refine ⟨?_,fun q inFacts => kept q (kept1 q inFacts),?_⟩
      · intro q inFinal
        rcases origin q inFinal with fromMiddle | ⟨item,itemIn,xs,statement,rest⟩
        · rcases origin1 q fromMiddle with old | ⟨xs,statement,rest⟩
          · exact .inl old
          · exact .inr ⟨items.val[index.val],by rw [split]; exact List.mem_cons_self ..,xs,statement,rest⟩
        · exact .inr ⟨item,by rw [split]; exact List.mem_cons_of_mem _ itemIn,xs,statement,rest⟩
      · intro item itemIn xs statement
        rw [split] at itemIn
        rcases List.mem_cons.mp itemIn with rfl | later
        · exact (covered1 xs statement).imp (fun ⟨q,qIn,qNode,qConcept⟩ => ⟨q,kept q qIn,qNode,qConcept⟩)
        · exact covered item later xs statement
    cases item : items.val[index.val].axiom with
    | DifferentIndividuals xs =>
      obtain ⟨middle,middleRun,middleSpec⟩ := apart_members_correct nodes same xs facts
      cases middle with
      | none => exact ⟨none,by simp [more,lookup,item,middleRun],by intro final impossible; cases impossible⟩
      | some middle =>
        obtain ⟨origin,kept,covered⟩ := middleSpec middle rfl
        obtain ⟨r,run,spec⟩ := tail middle
          (fun q inMiddle => (origin q inMiddle).imp_right (fun found => ⟨xs,item,found⟩)) kept
          (fun xs' statement => by
            rw [item] at statement
            cases statement
            exact covered)
        exact ⟨r,by simp [more,lookup,item,middleRun,advance,run],spec⟩
    | _ =>
      obtain ⟨r,run,spec⟩ := tail facts (fun q inFacts => .inl inFacts) (fun q inFacts => inFacts)
        (fun xs statement => by rw [item] at statement; cases statement)
      exact ⟨r,by simp [more,lookup,item,advance,run],spec⟩
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some facts,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro final same
    cases same
    exact ⟨fun q inFacts => .inl inFacts,fun q inFacts => inFacts,by simp [empty]⟩
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- The source of every negative object property assertion from `index` on
    related along its property only outside the target's nominal: every fact is
    given or such a restriction, and every such assertion has its restriction. -/
theorem refused_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (same : alloc.vec.Vec Usize) (index : Usize) (facts : alloc.vec.Vec completion.Fact) :
    ∃ r, shi_ontology.refused_from items nodes same index facts = .ok r ∧ ∀ final, r = some final →
      (∀ q ∈ final.val, q ∈ facts.val ∨ ∃ item ∈ items.val.drop index.val, ∃ p a b,
        item.axiom = .NegativeObjectPropertyAssertion p a b ∧ q.node.val = RepOf same.val nodes.val a ∧
          q.concept = .Forall p (.NotOne b)) ∧
      (∀ q ∈ facts.val, q ∈ final.val) ∧
      (∀ item ∈ items.val.drop index.val, ∀ p a b, item.axiom = .NegativeObjectPropertyAssertion p a b →
        ∃ q ∈ final.val, q.node.val = RepOf same.val nodes.val a ∧ q.concept = .Forall p (.NotOne b)) := by
  rw [shi_ontology.refused_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have tail : ∀ middle : alloc.vec.Vec completion.Fact,
        (∀ q ∈ middle.val, q ∈ facts.val ∨ ∃ p a b, items.val[index.val].axiom =
          .NegativeObjectPropertyAssertion p a b ∧ q.node.val = RepOf same.val nodes.val a ∧
            q.concept = .Forall p (.NotOne b)) →
        (∀ q ∈ facts.val, q ∈ middle.val) →
        (∀ p a b, items.val[index.val].axiom = .NegativeObjectPropertyAssertion p a b →
          ∃ q ∈ middle.val, q.node.val = RepOf same.val nodes.val a ∧ q.concept = .Forall p (.NotOne b)) →
        ∃ r, shi_ontology.refused_from items nodes same next middle = .ok r ∧ ∀ final, r = some final →
          (∀ q ∈ final.val, q ∈ facts.val ∨ ∃ item ∈ items.val.drop index.val, ∃ p a b,
            item.axiom = .NegativeObjectPropertyAssertion p a b ∧ q.node.val = RepOf same.val nodes.val a ∧
              q.concept = .Forall p (.NotOne b)) ∧
          (∀ q ∈ facts.val, q ∈ final.val) ∧
          (∀ item ∈ items.val.drop index.val, ∀ p a b, item.axiom = .NegativeObjectPropertyAssertion p a b →
            ∃ q ∈ final.val, q.node.val = RepOf same.val nodes.val a ∧ q.concept = .Forall p (.NotOne b)) := by
      intro middle origin1 kept1 covered1
      obtain ⟨r,run,spec⟩ := refused_from_correct items nodes same next middle
      refine ⟨r,run,?_⟩
      intro final finalIs
      obtain ⟨origin,kept,covered⟩ := spec final finalIs
      rw [nextIndex] at origin covered
      refine ⟨?_,fun q inFacts => kept q (kept1 q inFacts),?_⟩
      · intro q inFinal
        rcases origin q inFinal with fromMiddle | ⟨item,itemIn,rest⟩
        · rcases origin1 q fromMiddle with old | rest
          · exact .inl old
          · exact .inr ⟨items.val[index.val],by rw [split]; exact List.mem_cons_self ..,rest⟩
        · exact .inr ⟨item,by rw [split]; exact List.mem_cons_of_mem _ itemIn,rest⟩
      · intro item itemIn p a b statement
        rw [split] at itemIn
        rcases List.mem_cons.mp itemIn with rfl | later
        · obtain ⟨q,qIn,qNode,qConcept⟩ := covered1 p a b statement
          exact ⟨q,kept q qIn,qNode,qConcept⟩
        · exact covered item later p a b statement
    cases item : items.val[index.val].axiom with
    | NegativeObjectPropertyAssertion p a b =>
      obtain ⟨node,nodeRun,nodeValue⟩ := node_of_correct nodes same a
      obtain ⟨added,addRun,addSpec⟩ := add_fact_correct facts node (.Forall p (.NotOne b))
      cases added with
      | none =>
        exact ⟨none,by simp [more,lookup,item,nodeRun,copy_role_identity,copy_individual_identity,addRun],
          by intro final impossible; cases impossible⟩
      | some middle =>
        have middleIs := addSpec middle rfl
        obtain ⟨r,run,spec⟩ := tail middle
          (by
            intro q inMiddle
            rw [middleIs] at inMiddle
            rcases List.mem_append.mp inMiddle with old | new
            · exact .inl old
            · rw [List.mem_singleton] at new
              subst new
              exact .inr ⟨p,a,b,item,nodeValue,rfl⟩)
          (fun q inFacts => by rw [middleIs]; exact List.mem_append_left _ inFacts)
          (by
            intro p' a' b' statement
            rw [item] at statement
            simp only [Axiom.NegativeObjectPropertyAssertion.injEq] at statement
            obtain ⟨rfl,rfl,rfl⟩ := statement
            exact ⟨⟨node,.Forall p (.NotOne b)⟩,by rw [middleIs]; exact List.mem_append_right _ (List.mem_singleton_self _),
              nodeValue,rfl⟩)
        exact ⟨r,by simp [more,lookup,item,nodeRun,copy_role_identity,copy_individual_identity,addRun,advance,run],spec⟩
    | _ =>
      obtain ⟨r,run,spec⟩ := tail facts (fun q inFacts => .inl inFacts) (fun q inFacts => inFacts)
        (fun p a b statement => by rw [item] at statement; cases statement)
      exact ⟨r,by simp [more,lookup,item,advance,run],spec⟩
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some facts,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro final same
    cases same
    exact ⟨fun q inFacts => .inl inFacts,fun q inFacts => inFacts,by simp [empty]⟩
termination_by items.val.length - index.val
decreasing_by all_goals omega

end Rowl.ShiNominals
