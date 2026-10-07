import Rowl.DataSound
import Rowl.ShiOntology
import Rowl.KeyModels
import Rowl.Unfolding

/-!
The ontology queries of `data_ontology` with data properties, the literals of
the datatypes of `datatypes`, and data ranges of the numeric datatypes, with
the range facets, and of `xsd:string`, `rdf:PlainLiteral` and `xsd:boolean`:
consistency, class satisfiability, subsumption and instance checking, through
the encoding into the SROIQ queries of `shi_ontology`, for a capacity that
bounds the counts of the data restrictions of the closure and its questions
(`items_count_spec`, `class_count_spec`). Under every datatype map that is the
OWL 2 map on these datatypes (`Normative`), an answer is the answer of the
2012 OWL 2 Direct Semantics (`consistent_correct`, `class_satisfiable_correct`,
`subsumed_correct`, `instance_of_correct`, and their prepared forms): the
encoding of a closure has a model exactly when the closure has one
(`lifted_satisfies`, `sound_satisfies`), and a question's encoding holds at the
same elements as the question. A closure with keys is encoded by
`key_ontology` (`Rowl.KeyModels`), for a capacity that also counts the data
restrictions of its keys' class expressions: its answers hold for every
vocabulary in which the closure's named individuals are named (`NamesKeyed`),
the condition under which keys apply to them; for a closure without keys that
condition asks nothing.
-/
namespace Rowl.DataOntology
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DatatypeMap (Normative)
open Rowl.AlcOntology (RoleOf)
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.DataStructure
open Rowl.DataComplete
open Rowl.DataSound
open Rowl.KeyEncoding (NamesKeyed Keyed closureIndividuals keyAtoms)
open Rowl.KeyModels (keyed_encoded_model keyed_lifted_model)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe u v w

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-! ### The individuals a closure names -/

/-- The individuals that a collection adds to `nodes` are among `xs`. -/
def Adds (nodes final : alloc.vec.Vec Individual) (xs : List Individual) : Prop :=
  ∀ b ∈ final.val, b ∈ nodes.val ∨ b ∈ xs

theorem adds_trans {n1 n2 n3 : alloc.vec.Vec Individual} {xs ys : List Individual} (h1 : Adds n1 n2 xs)
    (h2 : Adds n2 n3 ys) : Adds n1 n3 (xs ++ ys) := by
  intro b m
  rcases h2 b m with old | new
  · rcases h1 b old with o | n
    · exact .inl o
    · exact .inr (List.mem_append_left _ n)
  · exact .inr (List.mem_append_right _ new)

theorem adds_mono {nodes final : alloc.vec.Vec Individual} {xs ys : List Individual} (h : Adds nodes final xs)
    (sub : ∀ b ∈ xs, b ∈ ys) : Adds nodes final ys := fun b m => (h b m).imp id (sub b)

theorem adds_self (nodes : alloc.vec.Vec Individual) (xs : List Individual) : Adds nodes nodes xs :=
  fun _ m => .inl m

theorem intern_spec (nodes : alloc.vec.Vec Individual) (a : Individual) :
    ∃ result, alc_ontology.intern nodes a = .ok result ∧ ∀ final, result = some final → Adds nodes final [a] := by
  obtain ⟨p, run, value⟩ := Rowl.AlcOntology.position_of nodes a
  rw [alc_ontology.intern]
  by_cases present : a ∈ nodes.val
  · have nonzero : ¬ p.val = 0 := by
      intro zero
      obtain ⟨_, positive, _⟩ := Rowl.AlcOntology.positionOf_present nodes.val a present
      rw [← value, zero] at positive
      simp at positive
    exact ⟨some nodes, by simp [run, nonzero], fun final same => by cases same; exact adds_self _ _⟩
  · have zero : p = 0#usize := by
      apply UScalar.eq_of_val_eq
      rw [value]
      simpa [Rowl.AlcOntology.PositionOf] using Rowl.AlcOntology.positionFrom_absent nodes.val a 0 present
    obtain ⟨limit, limitRun, limitValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := core.num.Usize.MAX) (y := 1#usize) (by simp [usize_max_val]; scalar_tac))
    have limitIs : limit.val = Usize.max - 1 := by simp [usize_max_val] at limitValue; exact limitValue.1
    by_cases fits : nodes.val.length < Usize.max - 1
    · obtain ⟨appended, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec nodes a (by omega))
      refine ⟨some appended, by simp [run, zero, limitRun, limitIs, fits,
        Rowl.AlcOntology.copy_individual_identity, push], fun final same => ?_⟩
      cases same
      intro b m
      rw [contents] at m
      rcases List.mem_append.mp m with old | new
      · exact .inl old
      · exact .inr new
    · exact ⟨none, by simp [run, zero, limitRun, limitIs, fits], by simp⟩

theorem list_individuals_spec (nodes individuals : alloc.vec.Vec Individual) (index : Usize) :
    ∃ res, data_ontology.list_individuals nodes individuals index = .ok res ∧ ∀ final, res = some final →
      Adds nodes final (individuals.val.drop index.val) := by
  rw [data_ontology.list_individuals]
  by_cases inside : index.val < individuals.val.length
  · have lookup : individuals.index_usize index = .ok individuals.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, facts1⟩ := intern_spec nodes individuals.val[index.val]
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some n1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := list_individuals_spec n1 individuals next
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance,
        restRun], fun final h => ?_⟩
      have tail := restFacts final h
      rw [nextIndex] at tail
      rw [split]
      exact adds_mono (adds_trans (facts1 n1 rfl) tail) (by simp)
  · exact ⟨some nodes, by simp [UScalar.lt_equiv, inside], fun final h => by cases h; exact adds_self _ _⟩
termination_by individuals.val.length - index.val
decreasing_by omega

theorem classes_individuals_spec (nodes : alloc.vec.Vec Individual) (classes : alloc.vec.Vec ClassExpression)
    (index : Usize)
    (each : ∀ e ∈ classes.val, ∀ nodes, ∃ res, data_ontology.class_individuals nodes e = .ok res ∧
      ∀ final, res = some final → Adds nodes final (classIndividuals e)) :
    ∃ res, data_ontology.classes_individuals nodes classes index = .ok res ∧ ∀ final, res = some final →
      Adds nodes final ((classes.val.drop index.val).flatMap classIndividuals) := by
  rw [data_ontology.classes_individuals]
  by_cases inside : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, facts1⟩ := each _ (List.getElem_mem inside) nodes
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some n1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := classes_individuals_spec n1 classes next each
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance,
        restRun], fun final h => ?_⟩
      have tail := restFacts final h
      rw [nextIndex] at tail
      rw [split, List.flatMap_cons]
      exact adds_trans (facts1 n1 rfl) tail
  · exact ⟨some nodes, by simp [UScalar.lt_equiv, inside], fun final h => by cases h; exact adds_self _ _⟩
termination_by classes.val.length - index.val
decreasing_by omega

theorem members_individuals_spec (nodes : alloc.vec.Vec Individual) (members : AtLeastTwo ClassExpression)
    (each : ∀ e ∈ members.elements, ∀ nodes, ∃ res, data_ontology.class_individuals nodes e = .ok res ∧
      ∀ final, res = some final → Adds nodes final (classIndividuals e)) :
    ∃ res, data_ontology.members_individuals nodes members = .ok res ∧ ∀ final, res = some final →
      Adds nodes final (members.elements.flatMap classIndividuals) := by
  rw [data_ontology.members_individuals]
  obtain ⟨r1, run1, facts1⟩ := each members.first (by simp [AtLeastTwo.elements]) nodes
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some n1 =>
    obtain ⟨r2, run2, facts2⟩ := each members.second (by simp [AtLeastTwo.elements]) n1
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some n2 =>
      obtain ⟨r3, run3, facts3⟩ := classes_individuals_spec n2 members.rest 0#usize
        (fun e mem => each e (by simp [AtLeastTwo.elements, mem]))
      refine ⟨r3, by simp [run1, run2, run3], fun final h => ?_⟩
      have tail := facts3 final h
      simp only [zero_val, List.drop_zero] at tail
      have all := adds_trans (adds_trans (facts1 n1 rfl) (facts2 n2 rfl)) tail
      simpa [AtLeastTwo.elements, List.append_assoc] using all

theorem class_individuals_spec (nodes : alloc.vec.Vec Individual) (c : ClassExpression) :
    ∃ res, data_ontology.class_individuals nodes c = .ok res ∧ ∀ final, res = some final →
      Adds nodes final (classIndividuals c) := by
  have bound : ∀ (xs : AtLeastTwo ClassExpression), ∀ e ∈ xs.elements, sizeOf e < 1 + sizeOf xs := by
    intro xs e mem
    simp only [AtLeastTwo.elements, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · have := first_size xs; omega
    · have := second_size xs; omega
    · have := member_size xs e mem; omega
  have members : ∀ (xs : AtLeastTwo ClassExpression),
      classIndividuals (.ObjectIntersectionOf xs) = xs.elements.flatMap classIndividuals ∧
      classIndividuals (.ObjectUnionOf xs) = xs.elements.flatMap classIndividuals := by
    intro xs
    rw [classIndividuals, classIndividuals]
    simp [AtLeastTwo.elements]
  cases h : c with
  | ObjectIntersectionOf xs =>
    rw [data_ontology.class_individuals, (members xs).1]
    exact members_individuals_spec nodes xs (fun e mem nodes => by
      have := bound xs e mem
      exact class_individuals_spec nodes e)
  | ObjectUnionOf xs =>
    rw [data_ontology.class_individuals, (members xs).2]
    exact members_individuals_spec nodes xs (fun e mem nodes => by
      have := bound xs e mem
      exact class_individuals_spec nodes e)
  | ObjectComplementOf inner =>
    rw [data_ontology.class_individuals, classIndividuals]
    have : sizeOf inner < sizeOf c := by rw [h]; simp
    exact class_individuals_spec nodes inner
  | ObjectOneOf xs =>
    rw [data_ontology.class_individuals, classIndividuals]
    obtain ⟨r1, run1, facts1⟩ := intern_spec nodes xs.first
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some n1 =>
      obtain ⟨r2, run2, facts2⟩ := list_individuals_spec n1 xs.rest 0#usize
      refine ⟨r2, by simp [run1, run2], fun final h => ?_⟩
      have tail := facts2 final h
      simp only [zero_val, List.drop_zero] at tail
      exact adds_mono (adds_trans (facts1 n1 rfl) tail) (by simp [NonEmpty.elements])
  | ObjectSomeValuesFrom _ filler =>
    rw [data_ontology.class_individuals, classIndividuals]
    have : sizeOf filler < sizeOf c := by rw [h]; simp
    exact class_individuals_spec nodes filler
  | ObjectAllValuesFrom _ filler =>
    rw [data_ontology.class_individuals, classIndividuals]
    have : sizeOf filler < sizeOf c := by rw [h]; simp
    exact class_individuals_spec nodes filler
  | ObjectHasValue _ a =>
    rw [data_ontology.class_individuals, classIndividuals]
    exact intern_spec nodes a
  | ObjectMinCardinality _ _ filler | ObjectMaxCardinality _ _ filler | ObjectExactCardinality _ _ filler =>
    cases hf : filler with
    | none =>
      rw [data_ontology.class_individuals, classIndividuals]
      exact ⟨some nodes, rfl, fun final h => by cases h; exact adds_self _ _⟩
    | some e =>
      rw [data_ontology.class_individuals, classIndividuals]
      have : sizeOf e < sizeOf c := by rw [h, hf]; simp; omega
      exact class_individuals_spec nodes e
  | Class _ | ObjectHasSelf _ | DataSomeValuesFrom _ _ | DataAllValuesFrom _ _ | DataHasValue _ _
  | DataMinCardinality _ _ _ | DataMaxCardinality _ _ _ | DataExactCardinality _ _ _ =>
    rw [data_ontology.class_individuals.eq_def]
    exact ⟨some nodes, rfl, fun final h => by cases h; exact adds_self _ _⟩
termination_by sizeOf c
decreasing_by all_goals (subst_vars; first | omega | (simp_wf; omega))

theorem axiom_individuals_spec (nodes : alloc.vec.Vec Individual) (ax : Axiom) :
    ∃ res, data_ontology.axiom_individuals nodes ax = .ok res ∧ ∀ final, res = some final →
      Adds nodes final (axiomIndividuals ax) := by
  have keep : ∃ res, (.ok (some nodes) : Result (Option (alloc.vec.Vec Individual))) = .ok res ∧
      ∀ final, res = some final → Adds nodes final [] := ⟨some nodes, rfl, fun final h => by cases h; exact adds_self _ _⟩
  cases ax with
  | SubClassOf a b =>
    rw [data_ontology.axiom_individuals]
    obtain ⟨r1, run1, facts1⟩ := class_individuals_spec nodes a
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some n1 =>
      obtain ⟨r2, run2, facts2⟩ := class_individuals_spec n1 b
      exact ⟨r2, by simp [run1, run2], fun final h => adds_trans (facts1 n1 rfl) (facts2 final h)⟩
  | EquivalentClasses xs | DisjointClasses xs | DisjointUnion _ xs =>
    rw [data_ontology.axiom_individuals]
    exact members_individuals_spec nodes xs (fun e _ nodes => class_individuals_spec nodes e)
  | ObjectPropertyDomain _ e | ObjectPropertyRange _ e | DataPropertyDomain _ e =>
    rw [data_ontology.axiom_individuals]
    exact class_individuals_spec nodes e
  | SameIndividual xs | DifferentIndividuals xs =>
    rw [data_ontology.axiom_individuals]
    obtain ⟨r1, run1, facts1⟩ := intern_spec nodes xs.first
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some n1 =>
      obtain ⟨r2, run2, facts2⟩ := intern_spec n1 xs.second
      cases r2 with
      | none => exact ⟨none, by simp [run1, run2], by simp⟩
      | some n2 =>
        obtain ⟨r3, run3, facts3⟩ := list_individuals_spec n2 xs.rest 0#usize
        refine ⟨r3, by simp [run1, run2, run3], fun final h => ?_⟩
        have tail := facts3 final h
        simp only [zero_val, List.drop_zero] at tail
        exact adds_mono (adds_trans (adds_trans (facts1 n1 rfl) (facts2 n2 rfl)) tail)
          (by simp [axiomIndividuals, AtLeastTwo.elements])
  | ClassAssertion e a =>
    rw [data_ontology.axiom_individuals]
    obtain ⟨r1, run1, facts1⟩ := intern_spec nodes a
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some n1 =>
      obtain ⟨r2, run2, facts2⟩ := class_individuals_spec n1 e
      exact ⟨r2, by simp [run1, run2], fun final h => adds_mono (adds_trans (facts1 n1 rfl) (facts2 final h))
        (by simp [axiomIndividuals])⟩
  | ObjectPropertyAssertion _ a b | NegativeObjectPropertyAssertion _ a b =>
    rw [data_ontology.axiom_individuals]
    obtain ⟨r1, run1, facts1⟩ := intern_spec nodes a
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some n1 =>
      obtain ⟨r2, run2, facts2⟩ := intern_spec n1 b
      exact ⟨r2, by simp [run1, run2], fun final h => adds_mono (adds_trans (facts1 n1 rfl) (facts2 final h))
        (by simp [axiomIndividuals])⟩
  | DataPropertyAssertion _ a _ | NegativeDataPropertyAssertion _ a _ =>
    rw [data_ontology.axiom_individuals]
    exact intern_spec nodes a
  | Declaration _ | SubObjectPropertyOf _ _ | EquivalentObjectProperties _ | DisjointObjectProperties _
  | InverseObjectProperties _ _ | FunctionalObjectProperty _ | InverseFunctionalObjectProperty _
  | ReflexiveObjectProperty _ | IrreflexiveObjectProperty _ | SymmetricObjectProperty _
  | AsymmetricObjectProperty _ | TransitiveObjectProperty _ | SubDataPropertyOf _ _ | EquivalentDataProperties _
  | DisjointDataProperties _ | DataPropertyRange _ _ | FunctionalDataProperty _ | DatatypeDefinition _ _
  | HasKey _ _ _ | AnnotationAssertion _ _ _ | SubAnnotationPropertyOf _ _ | AnnotationPropertyDomain _ _
  | AnnotationPropertyRange _ _ =>
    rw [data_ontology.axiom_individuals]
    exact keep

/-- The individuals of a closure's axioms. -/
def itemIndividuals (items : List AnnotatedAxiom) : List Individual :=
  items.flatMap (fun i => axiomIndividuals i.axiom)

theorem items_individuals_spec (nodes : alloc.vec.Vec Individual) (items : alloc.vec.Vec AnnotatedAxiom)
    (index : Usize) :
    ∃ res, data_ontology.items_individuals nodes items index = .ok res ∧ ∀ final, res = some final →
      Adds nodes final (itemIndividuals (items.val.drop index.val)) := by
  rw [data_ontology.items_individuals]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, facts1⟩ := axiom_individuals_spec nodes items.val[index.val].axiom
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some n1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := items_individuals_spec n1 items next
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance,
        restRun], fun final h => ?_⟩
      have tail := restFacts final h
      rw [nextIndex] at tail
      rw [split, itemIndividuals, List.flatMap_cons]
      exact adds_trans (facts1 n1 rfl) tail
  · exact ⟨some nodes, by simp [UScalar.lt_equiv, inside], fun final h => by cases h; exact adds_self _ _⟩
termination_by items.val.length - index.val
decreasing_by omega

/-! ### The individuals a question names -/

/-- A named individual among `nodes`. -/
def KnownTo (nodes : alloc.vec.Vec Individual) (a : Individual) : Prop := (∃ n, a = .Named n) ∧ a ∈ nodes.val

theorem individual_known_spec (nodes : alloc.vec.Vec Individual) (a : Individual) :
    ∃ b, data_ontology.individual_known nodes a = .ok b ∧ (b = true → KnownTo nodes a) := by
  cases a with
  | Named n =>
    obtain ⟨p, run, value⟩ := Rowl.AlcOntology.position_of nodes (.Named n)
    refine ⟨p != 0#usize, by simp [data_ontology.individual_known, run], fun yes => ⟨⟨n, rfl⟩, ?_⟩⟩
    by_contra absent
    have zero := Rowl.AlcOntology.positionFrom_absent nodes.val (.Named n) 0 absent
    have : p = 0#usize := UScalar.eq_of_val_eq (by rw [value]; simpa [Rowl.AlcOntology.PositionOf] using zero)
    simp [this] at yes
  | Anonymous _ => exact ⟨false, rfl, by simp⟩

theorem individuals_known_spec (nodes individuals : alloc.vec.Vec Individual) (index : Usize) :
    ∃ b, data_ontology.individuals_known nodes individuals index = .ok b ∧
      (b = true → ∀ a ∈ individuals.val.drop index.val, KnownTo nodes a) := by
  rw [data_ontology.individuals_known]
  by_cases inside : index.val < individuals.val.length
  · have lookup : individuals.index_usize index = .ok individuals.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨b1, run1, facts1⟩ := individual_known_spec nodes individuals.val[index.val]
    cases b1 with
    | false =>
      exact ⟨false, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | true =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b2, run2, facts2⟩ := individuals_known_spec nodes individuals next
      refine ⟨b2, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance, run2],
        fun yes a mem => ?_⟩
      rw [split] at mem
      rcases List.mem_cons.mp mem with rfl | later
      · exact facts1 rfl
      · exact facts2 yes a (by rw [nextIndex]; exact later)
  · exact ⟨true, by simp [UScalar.lt_equiv, inside], fun _ a mem => by
      simp [List.drop_eq_nil_iff.mpr (show individuals.val.length ≤ index.val by omega)] at mem⟩
termination_by individuals.val.length - index.val
decreasing_by omega

theorem classes_known_spec (nodes : alloc.vec.Vec Individual) (classes : alloc.vec.Vec ClassExpression)
    (index : Usize)
    (each : ∀ e ∈ classes.val, ∃ b, data_ontology.class_known nodes e = .ok b ∧
      (b = true → ∀ a ∈ classIndividuals e, KnownTo nodes a)) :
    ∃ b, data_ontology.classes_known nodes classes index = .ok b ∧
      (b = true → ∀ a ∈ (classes.val.drop index.val).flatMap classIndividuals, KnownTo nodes a) := by
  rw [data_ontology.classes_known]
  by_cases inside : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨b1, run1, facts1⟩ := each _ (List.getElem_mem inside)
    cases b1 with
    | false =>
      exact ⟨false, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | true =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b2, run2, facts2⟩ := classes_known_spec nodes classes next each
      refine ⟨b2, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance, run2],
        fun yes a mem => ?_⟩
      rw [split, List.flatMap_cons] at mem
      rcases List.mem_append.mp mem with early | later
      · exact facts1 rfl a early
      · exact facts2 yes a (by rw [nextIndex]; exact later)
  · exact ⟨true, by simp [UScalar.lt_equiv, inside], fun _ a mem => by
      simp [List.drop_eq_nil_iff.mpr (show classes.val.length ≤ index.val by omega)] at mem⟩
termination_by classes.val.length - index.val
decreasing_by omega

theorem class_known_spec (nodes : alloc.vec.Vec Individual) (c : ClassExpression) :
    ∃ b, data_ontology.class_known nodes c = .ok b ∧ (b = true → ∀ a ∈ classIndividuals c, KnownTo nodes a) := by
  have bound : ∀ (xs : AtLeastTwo ClassExpression), ∀ e ∈ xs.elements, sizeOf e < 1 + sizeOf xs := by
    intro xs e mem
    simp only [AtLeastTwo.elements, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · have := first_size xs; omega
    · have := second_size xs; omega
    · have := member_size xs e mem; omega
  have members : ∀ (xs : AtLeastTwo ClassExpression),
      (∀ e ∈ xs.elements, ∃ b, data_ontology.class_known nodes e = .ok b ∧
        (b = true → ∀ a ∈ classIndividuals e, KnownTo nodes a)) →
      ∃ b, (do
          let b ← data_ontology.class_known nodes xs.first
          if b then
            let b1 ← data_ontology.class_known nodes xs.second
            if b1 then data_ontology.classes_known nodes xs.rest 0#usize else ok false
          else ok false) = .ok b ∧
        (b = true → ∀ a ∈ xs.elements.flatMap classIndividuals, KnownTo nodes a) := by
    intro xs each
    obtain ⟨b1, run1, facts1⟩ := each xs.first (by simp [AtLeastTwo.elements])
    obtain ⟨b2, run2, facts2⟩ := each xs.second (by simp [AtLeastTwo.elements])
    obtain ⟨b3, run3, facts3⟩ := classes_known_spec nodes xs.rest 0#usize
      (fun e mem => each e (by simp [AtLeastTwo.elements, mem]))
    cases b1 with
    | false => exact ⟨false, by simp [run1], by simp⟩
    | true =>
      cases b2 with
      | false => exact ⟨false, by simp [run1, run2], by simp⟩
      | true =>
        refine ⟨b3, by simp [run1, run2, run3], fun yes a mem => ?_⟩
        simp only [AtLeastTwo.elements, List.flatMap_cons, List.mem_append] at mem
        rcases mem with first | second | rest
        · exact facts1 rfl a first
        · exact facts2 rfl a second
        · exact facts3 yes a (by simpa using rest)
  have flat : ∀ (xs : AtLeastTwo ClassExpression),
      classIndividuals (.ObjectIntersectionOf xs) = xs.elements.flatMap classIndividuals ∧
      classIndividuals (.ObjectUnionOf xs) = xs.elements.flatMap classIndividuals := by
    intro xs
    rw [classIndividuals, classIndividuals]
    simp [AtLeastTwo.elements]
  cases h : c with
  | ObjectIntersectionOf xs =>
    rw [data_ontology.class_known, (flat xs).1]
    exact members xs (fun e mem => by have := bound xs e mem; exact class_known_spec nodes e)
  | ObjectUnionOf xs =>
    rw [data_ontology.class_known, (flat xs).2]
    exact members xs (fun e mem => by have := bound xs e mem; exact class_known_spec nodes e)
  | ObjectComplementOf inner =>
    rw [data_ontology.class_known, classIndividuals]
    have : sizeOf inner < sizeOf c := by rw [h]; simp
    exact class_known_spec nodes inner
  | ObjectOneOf xs =>
    rw [data_ontology.class_known, classIndividuals]
    obtain ⟨b1, run1, facts1⟩ := individual_known_spec nodes xs.first
    obtain ⟨b2, run2, facts2⟩ := individuals_known_spec nodes xs.rest 0#usize
    cases b1 with
    | false => exact ⟨false, by simp [run1], by simp⟩
    | true =>
      refine ⟨b2, by simp [run1, run2], fun yes a mem => ?_⟩
      simp only [NonEmpty.elements, List.mem_cons] at mem
      rcases mem with rfl | later
      · exact facts1 rfl
      · exact facts2 yes a (by simpa using later)
  | ObjectSomeValuesFrom _ filler =>
    rw [data_ontology.class_known, classIndividuals]
    have : sizeOf filler < sizeOf c := by rw [h]; simp
    exact class_known_spec nodes filler
  | ObjectAllValuesFrom _ filler =>
    rw [data_ontology.class_known, classIndividuals]
    have : sizeOf filler < sizeOf c := by rw [h]; simp
    exact class_known_spec nodes filler
  | ObjectHasValue _ a =>
    rw [data_ontology.class_known, classIndividuals]
    obtain ⟨b, run, facts⟩ := individual_known_spec nodes a
    exact ⟨b, run, fun yes x mem => by simp at mem; subst mem; exact facts yes⟩
  | ObjectMinCardinality _ _ filler | ObjectMaxCardinality _ _ filler | ObjectExactCardinality _ _ filler =>
    cases hf : filler with
    | none =>
      rw [data_ontology.class_known, classIndividuals]
      exact ⟨true, rfl, by simp⟩
    | some e =>
      rw [data_ontology.class_known, classIndividuals]
      have : sizeOf e < sizeOf c := by rw [h, hf]; simp; omega
      exact class_known_spec nodes e
  | Class _ | ObjectHasSelf _ | DataSomeValuesFrom _ _ | DataAllValuesFrom _ _ | DataHasValue _ _
  | DataMinCardinality _ _ _ | DataMaxCardinality _ _ _ | DataExactCardinality _ _ _ =>
    rw [data_ontology.class_known.eq_def]
    exact ⟨true, rfl, by simp [classIndividuals]⟩
termination_by sizeOf c
decreasing_by all_goals (subst_vars; first | omega | (simp_wf; omega))

/-! ### The counts of the data restrictions -/

/-- The cap on the counts of the data restrictions. -/
def limit : Nat := Usize.max / 16

theorem limit_spec : ∃ l : Usize, data_ontology.LIMIT = .ok l ∧ l.val = limit := by
  unfold data_ontology.LIMIT
  obtain ⟨q, qRun, qValue⟩ := WP.spec_imp_exists (Usize.div_spec core.num.Usize.MAX (y := 16#usize) (by simp))
  exact ⟨q, qRun, by rw [qValue]; simp [core.num.Usize.MAX, limit]⟩

theorem limit_room : 2 * limit < Usize.max := by
  have : 16 ≤ Usize.max := by scalar_tac
  unfold limit
  omega

theorem one_val : (1#usize).val = 1 := by simp

theorem add_count_spec (total amount : Usize) :
    ∃ r : Usize, data_ontology.add_count total amount = .ok r ∧ r.val = min (total.val + amount.val) limit := by
  obtain ⟨l, lRun, lIs⟩ := limit_spec
  have small := limit_room
  rw [data_ontology.add_count, lRun, bind_ok]
  by_cases both : total.val < l.val ∧ amount.val < l.val
  · obtain ⟨sum, sumRun, sumValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := total) (y := amount) (by omega))
    have sumIs : sum.val = total.val + amount.val := by simpa using sumValue
    have cond : ((decide (total < l)) && (decide (amount < l))) = true := by
      simp [UScalar.lt_equiv, both.1, both.2]
    rw [if_pos cond, sumRun, bind_ok]
    by_cases fits : sum.val < l.val
    · have fits' : sum < l := by rw [UScalar.lt_equiv]; exact fits
      rw [if_pos fits']
      exact ⟨sum, rfl, by omega⟩
    · have fits' : ¬ sum < l := by rw [UScalar.lt_equiv]; exact fits
      rw [if_neg fits']
      exact ⟨l, rfl, by omega⟩
  · have cond : ¬ ((decide (total < l)) && (decide (amount < l))) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, UScalar.lt_equiv]
      exact both
    rw [if_neg cond]
    exact ⟨l, rfl, by omega⟩

theorem natural_count_spec (value : probes.Natural) (total : Usize) (small : total.val ≤ limit) :
    ∃ r : Usize, data_ontology.natural_count value total = .ok r ∧
      r.val = min (total.val + Rowl.Probes.naturalValue value) limit := by
  cases value with
  | Zero =>
    refine ⟨total, by rw [data_ontology.natural_count], ?_⟩
    simp only [Rowl.Probes.naturalValue]
    omega
  | Succ inner =>
    obtain ⟨t1, run1, is1⟩ := add_count_spec total 1#usize
    obtain ⟨r, run, isR⟩ := natural_count_spec inner t1 (by rw [is1]; omega)
    refine ⟨r, by rw [data_ontology.natural_count]; simp [run1, run], ?_⟩
    rw [isR, is1, one_val]
    simp only [Rowl.Probes.naturalValue]
    omega

theorem atomCount_append (a b : List (DataProperty × Option DataRange × Nat)) :
    atomCount (a ++ b) = atomCount a + atomCount b := by
  simp [atomCount]

theorem atomCount_cons (a : DataProperty × Option DataRange × Nat) (b : List (DataProperty × Option DataRange × Nat)) :
    atomCount (a :: b) = a.2.2 + atomCount b := by
  simp [atomCount]

theorem atomCount_nil : atomCount [] = 0 := rfl

theorem class_atoms_members (xs : AtLeastTwo ClassExpression) :
    classAtoms (.ObjectIntersectionOf xs) = xs.elements.flatMap classAtoms ∧
      classAtoms (.ObjectUnionOf xs) = xs.elements.flatMap classAtoms := by
  rw [classAtoms, classAtoms]
  simp [AtLeastTwo.elements]

/-- What counting a class expression's data restrictions gives. -/
def CountSpec (c : ClassExpression) : Prop :=
  ∀ total : Usize, total.val ≤ limit → ∃ r : Usize, data_ontology.class_count c total = .ok r ∧
    r.val = min (total.val + atomCount (classAtoms c)) limit

theorem classes_count_spec (classes : alloc.vec.Vec ClassExpression) (index total : Usize)
    (small : total.val ≤ limit) (each : ∀ e ∈ classes.val, CountSpec e) :
    ∃ r : Usize, data_ontology.classes_count classes index total = .ok r ∧
      r.val = min (total.val + atomCount ((classes.val.drop index.val).flatMap classAtoms)) limit := by
  rw [data_ontology.classes_count]
  by_cases inside : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨t1, run1, is1⟩ := each _ (List.getElem_mem inside) total small
    obtain ⟨r, run, isR⟩ := classes_count_spec classes next t1 (by rw [is1]; omega) each
    refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, advance, run1, run], ?_⟩
    rw [isR, is1, nextIndex, split, List.flatMap_cons, atomCount_append]
    omega
  · refine ⟨total, by simp [UScalar.lt_equiv, inside], ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp only [List.flatMap_nil, atomCount_nil]
    omega
termination_by classes.val.length - index.val
decreasing_by omega

theorem members_count_spec (members : AtLeastTwo ClassExpression) (total : Usize) (small : total.val ≤ limit)
    (each : ∀ e ∈ members.elements, CountSpec e) :
    ∃ r : Usize, data_ontology.members_count members total = .ok r ∧
      r.val = min (total.val + atomCount (members.elements.flatMap classAtoms)) limit := by
  rw [data_ontology.members_count]
  obtain ⟨t1, run1, is1⟩ := each members.first (by simp [AtLeastTwo.elements]) total small
  obtain ⟨t2, run2, is2⟩ := each members.second (by simp [AtLeastTwo.elements]) t1 (by rw [is1]; omega)
  obtain ⟨r, run3, is3⟩ := classes_count_spec members.rest 0#usize t2 (by rw [is2]; omega)
    (fun e mem => each e (by simp [AtLeastTwo.elements, mem]))
  refine ⟨r, by simp [run1, run2, run3], ?_⟩
  rw [is3, is2, is1]
  simp only [AtLeastTwo.elements, List.flatMap_cons, atomCount_append, zero_val, List.drop_zero]
  omega

/-- Counting a class expression's data restrictions gives the sum of their
    counts, capped. -/
theorem class_count_spec (c : ClassExpression) : CountSpec c := by
  have bound : ∀ (xs : AtLeastTwo ClassExpression), ∀ e ∈ xs.elements, sizeOf e < 1 + sizeOf xs := by
    intro xs e mem
    simp only [AtLeastTwo.elements, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · have := first_size xs; omega
    · have := second_size xs; omega
    · have := member_size xs e mem; omega
  intro total small
  cases h : c with
  | ObjectIntersectionOf xs =>
    rw [data_ontology.class_count, (class_atoms_members xs).1]
    exact members_count_spec xs total small (fun e mem => by have := bound xs e mem; exact class_count_spec e)
  | ObjectUnionOf xs =>
    rw [data_ontology.class_count, (class_atoms_members xs).2]
    exact members_count_spec xs total small (fun e mem => by have := bound xs e mem; exact class_count_spec e)
  | ObjectComplementOf inner =>
    rw [data_ontology.class_count, classAtoms]
    have : sizeOf inner < sizeOf c := by rw [h]; simp
    exact class_count_spec inner total small
  | ObjectSomeValuesFrom _ filler =>
    rw [data_ontology.class_count, classAtoms]
    have : sizeOf filler < sizeOf c := by rw [h]; simp
    exact class_count_spec filler total small
  | ObjectAllValuesFrom _ filler =>
    rw [data_ontology.class_count, classAtoms]
    have : sizeOf filler < sizeOf c := by rw [h]; simp
    exact class_count_spec filler total small
  | ObjectMinCardinality _ _ filler | ObjectMaxCardinality _ _ filler | ObjectExactCardinality _ _ filler =>
    cases hf : filler with
    | none =>
      rw [data_ontology.class_count, classAtoms]
      exact ⟨total, rfl, by simp only [atomCount_nil]; omega⟩
    | some e =>
      rw [data_ontology.class_count, classAtoms]
      have : sizeOf e < sizeOf c := by rw [h, hf]; simp; omega
      exact class_count_spec e total small
  | DataSomeValuesFrom _ _ | DataAllValuesFrom _ _ | DataHasValue _ _ =>
    rw [data_ontology.class_count, classAtoms]
    obtain ⟨r, run, isR⟩ := add_count_spec total 1#usize
    exact ⟨r, run, by rw [isR]; simp [atomCount]⟩
  | DataMinCardinality n _ _ =>
    rw [data_ontology.class_count, classAtoms]
    obtain ⟨r, run, isR⟩ := natural_count_spec n total small
    exact ⟨r, run, by rw [isR]; simp [atomCount]⟩
  | DataMaxCardinality n _ _ =>
    rw [data_ontology.class_count, classAtoms]
    obtain ⟨t1, run1, is1⟩ := add_count_spec total 1#usize
    obtain ⟨r, run, isR⟩ := natural_count_spec n t1 (by rw [is1]; omega)
    refine ⟨r, by simp [run1, run], ?_⟩
    rw [isR, is1, one_val]
    simp only [atomCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  | DataExactCardinality n _ _ =>
    rw [data_ontology.class_count, classAtoms]
    obtain ⟨t1, run1, is1⟩ := add_count_spec total 1#usize
    obtain ⟨t2, run2, is2⟩ := natural_count_spec n t1 (by rw [is1]; omega)
    obtain ⟨r, run, isR⟩ := natural_count_spec n t2 (by rw [is2]; omega)
    refine ⟨r, by simp [run1, run2, run], ?_⟩
    rw [isR, is2, is1, one_val]
    simp only [atomCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  | Class _ | ObjectOneOf _ | ObjectHasValue _ _ | ObjectHasSelf _ =>
    rw [data_ontology.class_count, classAtoms]
    exact ⟨total, rfl, by simp only [atomCount_nil]; omega⟩
termination_by sizeOf c
decreasing_by all_goals (subst_vars; first | omega | (simp_wf; omega))

theorem axiom_count_spec (item : Axiom) (total : Usize) (small : total.val ≤ limit) :
    ∃ r : Usize, data_ontology.axiom_count item total = .ok r ∧
      r.val = min (total.val + atomCount (axiomAtoms item)) limit := by
  cases item with
  | SubClassOf sub sup =>
    obtain ⟨t1, run1, is1⟩ := class_count_spec sub total small
    obtain ⟨r, run, isR⟩ := class_count_spec sup t1 (by rw [is1]; omega)
    refine ⟨r, by simp [data_ontology.axiom_count, run1, run], ?_⟩
    rw [isR, is1, axiomAtoms, atomCount_append]
    omega
  | EquivalentClasses xs | DisjointClasses xs | DisjointUnion _ xs =>
    obtain ⟨r, run, isR⟩ := members_count_spec xs total small (fun e _ => class_count_spec e)
    exact ⟨r, by simp [data_ontology.axiom_count, run], by rw [isR, axiomAtoms]⟩
  | ObjectPropertyDomain _ e | ObjectPropertyRange _ e | DataPropertyDomain _ e | ClassAssertion e _ =>
    obtain ⟨r, run, isR⟩ := class_count_spec e total small
    exact ⟨r, by simp [data_ontology.axiom_count, run], by rw [isR, axiomAtoms]⟩
  | _ => exact ⟨total, by simp [data_ontology.axiom_count], by simp only [axiomAtoms, atomCount_nil]; omega⟩

theorem items_count_spec (items : alloc.vec.Vec AnnotatedAxiom) (index total : Usize) (small : total.val ≤ limit) :
    ∃ r : Usize, data_ontology.items_count items index total = .ok r ∧
      r.val = min (total.val + atomCount (itemAtoms (items.val.drop index.val))) limit := by
  rw [data_ontology.items_count]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨t1, run1, is1⟩ := axiom_count_spec items.val[index.val].axiom total small
    obtain ⟨r, run, isR⟩ := items_count_spec items next t1 (by rw [is1]; omega)
    refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, advance, run1, run], ?_⟩
    rw [isR, is1, nextIndex, split]
    simp only [itemAtoms, List.flatMap_cons, atomCount_append]
    omega
  · refine ⟨total, by simp [UScalar.lt_equiv, inside], ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp only [itemAtoms, List.flatMap_nil, atomCount_nil]
    omega
termination_by items.val.length - index.val
decreasing_by omega

theorem key_count_spec (item : Axiom) (total : Usize) (small : total.val ≤ limit) :
    ∃ r : Usize, key_ontology.key_count item total = .ok r ∧
      r.val = min (total.val + atomCount (keyAtoms item)) limit := by
  cases item with
  | HasKey e ops dps =>
    obtain ⟨r, run, isR⟩ := class_count_spec e total small
    exact ⟨r, by simp [key_ontology.key_count, run], by rw [isR]; rfl⟩
  | _ => exact ⟨total, by simp [key_ontology.key_count], by simp only [keyAtoms, atomCount_nil]; omega⟩

theorem keys_count_spec (items : alloc.vec.Vec AnnotatedAxiom) (index total : Usize) (small : total.val ≤ limit) :
    ∃ r : Usize, key_ontology.keys_count items index total = .ok r ∧
      r.val = min (total.val + atomCount ((items.val.drop index.val).flatMap (fun i => keyAtoms i.axiom))) limit := by
  rw [key_ontology.keys_count]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨t1, run1, is1⟩ := key_count_spec items.val[index.val].axiom total small
    obtain ⟨r, run, isR⟩ := keys_count_spec items next t1 (by rw [is1]; omega)
    refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, advance, run1, run], ?_⟩
    rw [isR, is1, nextIndex, split]
    simp only [List.flatMap_cons, atomCount_append]
    omega
  · refine ⟨total, by simp [UScalar.lt_equiv, inside], ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp only [List.flatMap_nil, atomCount_nil]
    omega
termination_by items.val.length - index.val
decreasing_by omega

/-- The individuals the actual kernel names for a closure with keys are not the
    encoding's. -/
theorem keyed_plain {context : data_ontology.Context} (good : Good context) {capacity : Usize}
    (capSmall : capacity.val < limit) {items : alloc.vec.Vec AnnotatedAxiom}
    {nodes : alloc.vec.Vec Individual} {counting : Bool} {enc : alloc.vec.Vec AnnotatedAxiom}
    (encRun : key_ontology.encode context capacity items nodes counting = .ok (some enc)) {a : Individual}
    (mem : a ∈ nodes.val) : Plain a := by
  obtain ⟨res, run, facts⟩ := Rowl.KeyEncoding.encode_meaning.{0,0,0,0} context good capacity capSmall items nodes
    counting
  rw [encRun] at run
  cases Result.ok_injective run
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, plainNodes, _⟩ := facts enc rfl
  exact plainNodes a mem

theorem named_known_spec (nodes : alloc.vec.Vec Individual) (a : NamedIndividual) :
    ∃ b, data_ontology.named_known nodes a = .ok b ∧
      (b = true → ¬ Reserved a.iri.spelling.val ∧ Individual.Named a ∈ nodes.val) := by
  rw [data_ontology.named_known, reserved_correct]
  by_cases reserved : Reserved a.iri.spelling.val
  · exact ⟨false, by simp [reserved], by simp⟩
  · obtain ⟨p, run, value⟩ := Rowl.AlcOntology.position_of nodes (.Named a)
    have eta : (Individual.Named { iri := { spelling := a.iri.spelling } }) = .Named a := rfl
    refine ⟨p != 0#usize, by simp [reserved, Rowl.Nnf.copy_bytes_identity, eta, run], fun yes => ⟨reserved, ?_⟩⟩
    by_contra absent
    have zero := Rowl.AlcOntology.positionFrom_absent nodes.val (.Named a) 0 absent
    have : p = 0#usize := UScalar.eq_of_val_eq (by rw [value]; simpa [Rowl.AlcOntology.PositionOf] using zero)
    simp [this] at yes

/-! ### Prepared closures -/

/-- What a prepared closure keeps: a closure without data as the SROIQ queries
    prepare it, or a good context, the closure's encoding as the SROIQ queries
    prepare it, for a capacity below the cap that has the room for a
    question's data restrictions besides the closure's, and individuals that
    the closure names; or, for a closure with keys, the same with its key
    encoding, a capacity that also counts its keys' class expressions, and
    exactly the individuals the closure names. -/
def DataPrepared (items : alloc.vec.Vec AnnotatedAxiom) : data_ontology.Prepared → Prop
  | .Plain p => Rowl.ShiOntology.PreparedData items p
  | .Encoded context nodes p room => Good context ∧
      (∃ (capacity : Usize) (enc : alloc.vec.Vec AnnotatedAxiom), capacity.val < limit ∧
        atomCount (itemAtoms items.val) + room.val ≤ capacity.val ∧
        data_ontology.encode context capacity items = .ok (some enc) ∧ Rowl.ShiOntology.PreparedData enc p) ∧
      Adds (alloc.vec.Vec.new Individual) nodes (itemIndividuals items.val)
  | .Keyed context nodes p room => Good context ∧
      (∃ (capacity : Usize) (counting : Bool) (enc : alloc.vec.Vec AnnotatedAxiom), capacity.val < limit ∧
        atomCount (itemAtoms items.val) + atomCount (items.val.flatMap (fun i => keyAtoms i.axiom)) + room.val ≤
          capacity.val ∧
        key_ontology.encode context capacity items nodes counting = .ok (some enc) ∧
        Rowl.ShiOntology.PreparedData enc p) ∧
      (∀ b, b ∈ nodes.val ↔ b ∈ closureIndividuals items.val) ∧ Keyed items.val
  | .Defined defs inner => ∃ unfolded, unfolding.definitions items = .ok defs ∧
      unfolding.unfold_items defs items = .ok (some unfolded) ∧ DataPrepared unfolded inner

theorem data_free_runs (context : data_ontology.Context) : ∃ b, data_ontology.data_free context = .ok b := by
  rw [data_ontology.data_free]
  dsimp only
  split_ifs <;> exact ⟨_, rfl⟩

theorem key_prepare_with_correct (items : alloc.vec.Vec AnnotatedAxiom) (context : data_ontology.Context)
    (good : Good context) (capacity room : Usize) (capSmall : capacity.val < limit)
    (fits : atomCount (itemAtoms items.val) + atomCount (items.val.flatMap (fun i => keyAtoms i.axiom)) + room.val ≤
      capacity.val) (keyed : Keyed items.val) :
    ∃ res, key_ontology.prepare_with items context capacity room = .ok res ∧ ∀ p, res = some p →
      DataPrepared items p := by
  rw [key_ontology.prepare_with]
  obtain ⟨r1, nodesRun, nodesFacts⟩ := Rowl.KeyEncoding.closure_nodes items
  cases r1 with
  | none => exact ⟨none, by simp [nodesRun], by simp⟩
  | some n1 =>
    obtain ⟨r2, keyRun, keyFacts⟩ := nodesFacts n1 rfl
    cases r2 with
    | none => exact ⟨none, by simp [nodesRun, keyRun], by simp⟩
    | some nodes =>
      obtain ⟨b, complexRun⟩ := Rowl.KeyEncoding.complex_roles_runs items 0#usize
      obtain ⟨r3, encRun, _⟩ := Rowl.KeyEncoding.encode_meaning.{0,0,0,0} context good capacity capSmall items nodes
        (!b)
      cases r3 with
      | none => exact ⟨none, by simp [nodesRun, keyRun, complexRun, encRun], by simp⟩
      | some enc =>
        obtain ⟨r4, prepRun, prepFacts⟩ := Rowl.ShiOntology.prepare_correct enc
        cases r4 with
        | none => exact ⟨none, by simp [nodesRun, keyRun, complexRun, encRun, prepRun], by simp⟩
        | some sp =>
          refine ⟨some (.Keyed context nodes sp room), by simp [nodesRun, keyRun, complexRun, encRun, prepRun],
            fun p h => ?_⟩
          cases h
          exact ⟨good, ⟨capacity, _, enc, capSmall, fits, encRun, prepFacts sp rfl⟩, keyFacts nodes rfl, keyed⟩

theorem key_prepare_correct (items : alloc.vec.Vec AnnotatedAxiom) (context : data_ontology.Context)
    (good : Good context) (room : Usize) (keyed : Keyed items.val) :
    ∃ res, key_ontology.prepare items context room = .ok res ∧ ∀ p, res = some p → DataPrepared items p := by
  rw [key_ontology.prepare]
  obtain ⟨c1, run1, good1⟩ := Rowl.KeyEncoding.keys_context_good context items 0#usize good
  obtain ⟨c2, run2, good2⟩ := finished_good c1 good1
  obtain ⟨n, countRun, countIs⟩ := items_count_spec items 0#usize 0#usize (by simp)
  obtain ⟨k, keysRun, keysIs⟩ := keys_count_spec items 0#usize n (by rw [countIs]; omega)
  obtain ⟨capacity, capRun, capIs⟩ := add_count_spec k room
  obtain ⟨l, lRun, lIs⟩ := limit_spec
  by_cases small : capacity.val < l.val
  · have capSmall : capacity.val < limit := by rw [lIs] at small; exact small
    have fits : atomCount (itemAtoms items.val) + atomCount (items.val.flatMap (fun i => keyAtoms i.axiom)) +
        room.val ≤ capacity.val := by
      simp only [zero_val, List.drop_zero, Nat.zero_add] at countIs keysIs
      omega
    obtain ⟨res, run, facts⟩ := key_prepare_with_correct items c2 good2 capacity room capSmall fits keyed
    exact ⟨res, by simp [run1, run2, countRun, keysRun, capRun, lRun, small, run], facts⟩
  · exact ⟨none, by simp [run1, run2, countRun, keysRun, capRun, lRun, small], by simp⟩

theorem prepare_in_correct (items : alloc.vec.Vec AnnotatedAxiom) (context : data_ontology.Context)
    (good : Good context) (room : Usize) :
    ∃ res, data_ontology.prepare_in items context room = .ok res ∧ ∀ p, res = some p → DataPrepared items p := by
  rw [data_ontology.prepare_in]
  obtain ⟨k, keysRun, keysIff⟩ := Rowl.KeyEncoding.has_keys_correct items 0#usize
  cases k with
  | true =>
    obtain ⟨item, mem, key⟩ := keysIff.mp rfl
    obtain ⟨res, run, facts⟩ := key_prepare_correct items context good room ⟨item, by simpa using mem, key⟩
    exact ⟨res, by simp [keysRun, run], facts⟩
  | false =>
  simp only [keysRun, bind_ok, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨b, freeRun⟩ := data_free_runs context
  cases b with
  | true =>
    obtain ⟨r, run, facts⟩ := Rowl.ShiOntology.prepare_correct items
    cases r with
    | none => exact ⟨none, by simp [freeRun, run], by simp⟩
    | some sp => exact ⟨some (.Plain sp), by simp [freeRun, run], fun p h => by cases h; exact facts sp rfl⟩
  | false =>
    obtain ⟨n, countRun, countIs⟩ := items_count_spec items 0#usize 0#usize (by simp)
    obtain ⟨capacity, capRun, capIs⟩ := add_count_spec n room
    obtain ⟨l, lRun, lIs⟩ := limit_spec
    by_cases small : capacity.val < l.val
    · have capSmall : capacity.val < Usize.max / 16 := by rw [lIs] at small; exact small
      have fits : atomCount (itemAtoms items.val) + room.val ≤ capacity.val := by
        simp only [zero_val, List.drop_zero, Nat.zero_add] at countIs
        omega
      obtain ⟨r1, run1, _⟩ := encode_meaning.{0,0,0,0} context good capacity capSmall items
      obtain ⟨r2, run2, facts2⟩ := items_individuals_spec (alloc.vec.Vec.new Individual) items 0#usize
      cases r1 with
      | none => exact ⟨none, by simp [freeRun, countRun, capRun, lRun, small, run1, run2], by simp⟩
      | some enc =>
        cases r2 with
        | none => exact ⟨none, by simp [freeRun, countRun, capRun, lRun, small, run1, run2], by simp⟩
        | some nodes =>
          obtain ⟨r3, run3, facts3⟩ := Rowl.ShiOntology.prepare_correct enc
          cases r3 with
          | none => exact ⟨none, by simp [freeRun, countRun, capRun, lRun, small, run1, run2, run3], by simp⟩
          | some sp =>
            refine ⟨some (.Encoded context nodes sp room), by
              simp [freeRun, countRun, capRun, lRun, small, run1, run2, run3], fun p h => ?_⟩
            cases h
            refine ⟨good, ⟨capacity, enc, by rw [← lIs]; exact small, fits, run1, facts3 sp rfl⟩, ?_⟩
            simpa [zero_val] using facts2 nodes rfl
    · exact ⟨none, by simp [freeRun, countRun, capRun, lRun, small], by simp⟩

/-- Preparing a closure for the queries terminates, and what it prepares keeps
    its closure. -/
theorem prepare_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.prepare items = .ok res ∧ ∀ p, res = some p → DataPrepared items p := by
  obtain ⟨b, hasRun⟩ := Rowl.Unfolding.has_definitions_runs items 0#usize
  cases b with
  | false =>
    obtain ⟨c1, run1, good1⟩ := closure_context_good items
    obtain ⟨c2, run2, good2⟩ := finished_good c1 good1
    obtain ⟨res, run, facts⟩ := prepare_in_correct items c2 good2 data_ontology.QUESTION_ROOM
    exact ⟨res, by simp [data_ontology.prepare, hasRun, run1, run2, run], facts⟩
  | true =>
    obtain ⟨defs, defsRun, _⟩ := Rowl.Unfolding.definitions_spec items
    obtain ⟨res, unfoldRun, _⟩ := Rowl.Unfolding.unfold_items_spec.{0,0} defs items
    cases res with
    | none => exact ⟨none, by simp [data_ontology.prepare, hasRun, defsRun, unfoldRun], by simp⟩
    | some unfolded =>
      obtain ⟨c1, run1, good1⟩ := closure_context_good unfolded
      obtain ⟨c2, run2, good2⟩ := finished_good c1 good1
      obtain ⟨res2, run, facts⟩ := prepare_in_correct unfolded c2 good2 data_ontology.QUESTION_ROOM
      cases res2 with
      | none =>
        exact ⟨none, by simp [data_ontology.prepare, hasRun, defsRun, unfoldRun, run1, run2, run], by simp⟩
      | some inner =>
        refine ⟨some (.Defined defs inner), by simp [data_ontology.prepare, hasRun, defsRun, unfoldRun, run1, run2,
          run], fun p hp => ?_⟩
        cases hp
        exact ⟨unfolded, defsRun, unfoldRun, facts inner rfl⟩

/-- What the definitions of a closure and its unfolding give. -/
theorem defined_facts {items defs unfolded : alloc.vec.Vec AnnotatedAxiom}
    (defsRun : unfolding.definitions items = .ok defs)
    (unfoldRun : unfolding.unfold_items defs items = .ok (some unfolded)) :
    defs.val = Rowl.Unfolding.definitionsOf items.val ∧ Rowl.Unfolding.Proper defs.val ∧
      Rowl.Unfolding.ItemsUnfold.{u,v} defs items.val unfolded.val := by
  obtain ⟨defs', defsRun', hdefs⟩ := Rowl.Unfolding.definitions_spec items
  rw [defsRun] at defsRun'
  cases Result.ok_injective defsRun'
  obtain ⟨res, unfoldRun', facts⟩ := Rowl.Unfolding.unfold_items_spec.{u,v} defs items
  rw [unfoldRun] at unfoldRun'
  cases Result.ok_injective unfoldRun'
  obtain ⟨proper, unfolds⟩ := facts unfolded rfl
  exact ⟨hdefs, proper, unfolds⟩

/-! ### Interpretations with other anonymous individuals -/

section Anonymous
variable {Object : Type u} {Value : Type v}

theorem withAnonymous_self (I : Interpretation Object Value) : withAnonymous I I.anonymousIndividuals = I := by
  cases I; rfl

theorem interpretation_anonymous {Native : Type w} {D : DatatypeMap Native} {embed : ValueEmbedding D Value}
    {V : Vocabulary} {I : Interpretation Object Value} (interp : IsInterpretation D embed V I)
    (g : AnonymousIndividual → Object) : IsInterpretation D embed V (withAnonymous I g) := interp

theorem lifted_anonymous (context : data_ontology.Context) (I : Interpretation Object Value)
    (lit : datatypes.DataValue → Value) (num : ℝ → Value) (x0 : Object) (g : AnonymousIndividual → Object) :
    withAnonymous (lifted context I lit num x0) (Sum.inl ∘ g) = lifted context (withAnonymous I g) lit num x0 := rfl

theorem class_denote_named (J : Interpretation Object Value) (c : Class) (y : Object) :
    classDenote J (.Class c) y ↔ J.classes c y := by
  rw [classDenote]

theorem or_denote (J : Interpretation Object Value) (a b : ClassExpression) (y : Object) :
    classDenote J (.ObjectUnionOf ⟨a, b, alloc.vec.Vec.new ClassExpression⟩) y ↔
      classDenote J a y ∨ classDenote J b y := by
  rw [union_iff]; simp [AtLeastTwo.elements, new_val]

end Anonymous

/-! ### The queries -/

/-- Consistency of a prepared closure: an answer is whether the closure has a
    model, under every datatype map that is the OWL 2 map on the five
    datatypes. -/
theorem prepared_consistent_correct (items : alloc.vec.Vec AnnotatedAxiom) (p : data_ontology.Prepared)
    (data : DataPrepared items p) :
    ∃ result, data_ontology.prepared_consistent p = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val → Rowl.Unfolding.DefinesNew D items.val → (answer = true ↔ Consistent.{u, max w v, w} D V items.val) := by
  cases p with
  | Plain sp =>
    obtain ⟨result, run, facts⟩ := Rowl.ShiOntology.prepared_consistent_correct.{u,v,w} items sp data
    exact ⟨result, by simpa [data_ontology.prepared_consistent] using run,
      fun answer h _ D _ V vocab _ _ => facts answer h D V vocab⟩
  | Defined defs inner =>
    obtain ⟨unfolded, defsRun, unfoldRun, innerData⟩ := data
    obtain ⟨hdefs, proper, unfolds⟩ := defined_facts.{u, max w v} defsRun unfoldRun
    obtain ⟨result, run, facts⟩ := prepared_consistent_correct unfolded inner innerData
    refine ⟨result, by simp [data_ontology.prepared_consistent, run], fun answer h Native D N V vocab names fresh => ?_⟩
    rw [facts answer h D N V vocab (Rowl.Unfolding.names_keyed unfolds names)
      (Rowl.Unfolding.unfolded_defines_new D unfolds)]
    exact (Rowl.Unfolding.unfolded_consistent hdefs proper unfolds fresh).symm
  | Keyed context nodes sp room =>
    obtain ⟨good, ⟨capacity, counting, enc, capSmall, count, encRun, prepData⟩, nodesExact, keyed⟩ := data
    obtain ⟨result, run, encodedSound⟩ := Rowl.ShiOntology.prepared_consistent_correct.{u,v,w} enc sp prepData
    obtain ⟨result', run', encodedComplete⟩ :=
      Rowl.ShiOntology.prepared_consistent_correct.{max u w v,v,w} enc sp prepData
    have same : result' = result := Result.ok_injective (run'.symm.trans run)
    subst same
    refine ⟨result', by simpa [data_ontology.prepared_consistent] using run, fun answer h Native D N V vocab names _ =>
      ⟨fun yes => ?_, fun model => ?_⟩⟩
    · obtain ⟨Object', Value', embed', J, modelJ⟩ := (encodedSound answer h D V vocab).mp yes
      obtain ⟨Object, Value, embed, I, _, modelI, _⟩ :=
        keyed_encoded_model.{u,v,w} N vocab good capSmall encRun nodesExact modelJ [] (by simp)
          (by simp only [List.flatMap_nil, atomCount_nil]; omega)
      exact ⟨Object, Value, embed, I, modelI⟩
    · obtain ⟨Object, Value, embed, I, modelI⟩ := model
      obtain ⟨J, modelJ, _⟩ := keyed_lifted_model.{u,v,w} N vocab good capSmall encRun nodesExact names keyed modelI []
        (by simp)
      exact (encodedComplete answer h D V vocab).mpr ⟨Object ⊕ Value, Value, embed, J, modelJ⟩
  | Encoded context nodes sp room =>
    obtain ⟨good, ⟨capacity, enc, capSmall, count, encRun, prepData⟩, _⟩ := data
    obtain ⟨result, run, encodedSound⟩ := Rowl.ShiOntology.prepared_consistent_correct.{u,v,w} enc sp prepData
    obtain ⟨result', run', encodedComplete⟩ :=
      Rowl.ShiOntology.prepared_consistent_correct.{max u w v,v,w} enc sp prepData
    have same : result' = result := Result.ok_injective (run'.symm.trans run)
    subst same
    refine ⟨result', by simpa [data_ontology.prepared_consistent] using run, fun answer h Native D N V vocab _ _ =>
      ⟨fun yes => ?_, fun model => ?_⟩⟩
    · obtain ⟨Object', Value', embed', J, ⟨_, jInterp, g, jSat⟩⟩ := (encodedSound answer h D V vocab).mp yes
      obtain ⟨bits, order, o, _, names, sat⟩ := sound_satisfies.{u,v,w,max w v} N good capSmall encRun
        (J := withAnonymous J g) jInterp.1 jInterp.2.2.1 jInterp.2.2.2.1 jSat
      let I := sound.{u,v,w,max w v} context (withAnonymous J g) N order (itemAtoms items.val) (fun _ => 0) o
      refine ⟨Element (withAnonymous J g), Values.{v,w} Native,
        ValueEmbedding.ofEmbedding D ⟨embedValue, embedValue_injective⟩, I,
        vocab, sound_interpretation (context := context) (J := withAnonymous J g) (N := N) (order := order)
          (atoms := itemAtoms items.val) (shift := fun _ => 0) V jInterp.1 jInterp.2.1 jInterp.2.2.1 jInterp.2.2.2.1 o,
        I.anonymousIndividuals, ?_⟩
      rw [withAnonymous_self]
      exact sat _ (fun _ h => h) (by omega)
    · obtain ⟨Object, Value, embed, I, ⟨_, interp, g, sat⟩⟩ := model
      obtain ⟨x0⟩ := I.objectsNonempty
      have sat' := lifted_satisfies N x0 vocab (interpretation_anonymous interp g) good capacity capSmall items enc
        encRun sat
      apply (encodedComplete answer h D V vocab).mpr
      exact ⟨Object ⊕ Value, Value, embed, lifted context I (litOf N embed) (numOf N embed) x0, vocab,
        lifted_interpretation N x0 interp, Sum.inl ∘ g, by rw [lifted_anonymous]; exact sat'⟩

/-- The individuals of a question that a prepared closure names are named
    individuals of the closure, which are not the encoding's. -/
theorem known_plain {context : data_ontology.Context} (good : Good context) {capacity : Usize}
    (capSmall : capacity.val < limit) {items enc : alloc.vec.Vec AnnotatedAxiom}
    (encRun : data_ontology.encode context capacity items = .ok (some enc)) {nodes : alloc.vec.Vec Individual}
    (nodesAdd : Adds (alloc.vec.Vec.new Individual) nodes (itemIndividuals items.val)) {a : Individual}
    (known : KnownTo nodes a) : Plain a := by
  obtain ⟨res, run, facts⟩ := encode_meaning.{0,0,0,0} context good capacity capSmall items
  rw [encRun] at run
  cases Result.ok_injective run
  obtain ⟨_, _, new, _, _, means, _⟩ := facts enc rfl
  rcases nodesAdd a known.2 with absurdity | inside
  · simp [new_val] at absurdity
  · obtain ⟨item, mem, inAxiom⟩ := List.mem_flatMap.mp inside
    exact means.2.1 item mem a inAxiom

/-- A model of a closure's encoding gives an OWL model of the closure whose
    elements stand at the model's elements that are no data nodes, and at which
    each question whose individuals the closure names holds exactly when its
    encoding does. -/
theorem encoded_model {Object' : Type u} {Value' : Type (max w v)} {Native : Type w} {D : DatatypeMap Native}
    (N : Normative D) {V : Vocabulary} (vocab : IsVocabulary D V) {context : data_ontology.Context}
    (good : Good context) {capacity : Usize} (capSmall : capacity.val < limit) {items enc : alloc.vec.Vec AnnotatedAxiom}
    (encRun : data_ontology.encode context capacity items = .ok (some enc)) {nodes : alloc.vec.Vec Individual}
    (nodesAdd : Adds (alloc.vec.Vec.new Individual) nodes (itemIndividuals items.val))
    {embed' : ValueEmbedding D Value'} {J : Interpretation Object' Value'} (model : Model D embed' V J enc.val)
    (questions : List ClassExpression) (known : ∀ e ∈ questions, ∀ a ∈ classIndividuals e, KnownTo nodes a)
    (count : atomCount (itemAtoms items.val) + atomCount (questions.flatMap classAtoms) ≤ capacity.val) :
    ∃ (Object : Type u) (Value : Type (max w v)) (embed : ValueEmbedding D Value) (I : Interpretation Object Value)
      (point : Object → Object'), Model D embed V I items.val ∧
      (∀ y, ¬ J.classes dataClass y → ∃ z, point z = y) ∧
      (∀ a : NamedIndividual, ¬ J.classes dataClass (J.namedIndividuals a) →
        point (I.namedIndividuals a) = J.namedIndividuals a) ∧
      ∀ e ∈ questions, ∀ e', data_ontology.encode_class context e = .ok (some e') →
        ∀ z, classDenote I e z ↔ classDenote J e' (point z) := by
  obtain ⟨_, jInterp, g, jSat⟩ := model
  obtain ⟨bits, order, o, setting, names, sat⟩ := sound_satisfies.{u,v,w,max w v} N good capSmall encRun
    (J := withAnonymous J g) jInterp.1 jInterp.2.2.1 jInterp.2.2.2.1 jSat
  let atoms := itemAtoms items.val ++ questions.flatMap classAtoms
  have atomsCount : atomCount atoms ≤ capacity.val := by
    simp only [atoms, atomCount_append]
    exact count
  let I := sound.{u,v,w,max w v} context (withAnonymous J g) N order atoms (fun _ => 0) o
  have sim0 : Simulates context I (withAnonymous J g) Subtype.val (Known (withAnonymous J g)) atoms :=
    sound_simulates.{u,v,w,max w v} setting atomsCount (fun _ _ => rfl) o
  have simQ : Simulates context I J Subtype.val (fun a => ∃ e ∈ questions, a ∈ classIndividuals e) atoms := by
    refine simulates_anonymous N g setting o sim0 (fun a ⟨e, mem, inside⟩ => ?_)
    have knownA := known e mem a inside
    obtain ⟨n, rfl⟩ := knownA.1
    rcases nodesAdd _ knownA.2 with absurdity | inItems
    · simp [new_val] at absurdity
    · obtain ⟨item, itemMem, inAxiom⟩ := List.mem_flatMap.mp inItems
      exact sim0.individuals _ (names item itemMem _ inAxiom)
  refine ⟨Element (withAnonymous J g), Values.{v,w} Native,
    ValueEmbedding.ofEmbedding D ⟨embedValue, embedValue_injective⟩, I, Subtype.val,
    ⟨vocab, sound_interpretation (context := context) (J := withAnonymous J g) (N := N) (order := order)
      (atoms := atoms) (shift := fun _ => 0) V jInterp.1 jInterp.2.1 jInterp.2.2.1 jInterp.2.2.2.1 o, I.anonymousIndividuals, ?_⟩,
    fun y outside => ⟨⟨y, outside⟩, rfl⟩, fun a outside => ?_, fun e mem e' run z => ?_⟩
  · rw [withAnonymous_self]
    exact sat atoms (fun _ h => List.mem_append_left _ h) atomsCount
  · have outside' : ¬ (withAnonymous J g).classes dataClass ((withAnonymous J g).namedIndividuals a) := outside
    simp only [I, sound, dif_pos outside']
    rfl
  · obtain ⟨res, run', means⟩ := encode_class_meaning.{u,max w v,u,max w v} context e
    rw [run] at run'
    cases Result.ok_injective run'
    exact means e' rfl I J Subtype.val _ atoms simQ
      (fun x h => List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, mem, h⟩)) (fun x h => ⟨e, mem, h⟩) z

/-- An OWL model of a closure gives a model of its encoding whose elements
    that are no data nodes are the OWL model's elements, and at which each
    question whose individuals are not the encoding's holds exactly as at
    those elements. -/
theorem lifted_model {Object : Type u} {Value : Type (max w v)} {Native : Type w} {D : DatatypeMap Native}
    (N : Normative D) {V : Vocabulary} (vocab : IsVocabulary D V) {context : data_ontology.Context}
    (good : Good context) {capacity : Usize} (capSmall : capacity.val < limit) {items enc : alloc.vec.Vec AnnotatedAxiom}
    (encRun : data_ontology.encode context capacity items = .ok (some enc)) {embed : ValueEmbedding D Value}
    {I : Interpretation Object Value} (model : Model D embed V I items.val) (questions : List ClassExpression)
    (plain : ∀ e ∈ questions, ∀ a ∈ classIndividuals e, Plain a) :
    ∃ J : Interpretation (Object ⊕ Value) Value, Model D embed V J enc.val ∧
      (∀ z, ¬ J.classes dataClass (.inl z)) ∧
      (∀ a : NamedIndividual, ¬ Reserved a.iri.spelling.val → J.namedIndividuals a = .inl (I.namedIndividuals a)) ∧
      ∀ e ∈ questions, ∀ e', data_ontology.encode_class context e = .ok (some e') →
        ∀ z, classDenote I e z ↔ classDenote J e' (.inl z) := by
  obtain ⟨_, interp, g, sat⟩ := model
  obtain ⟨x0⟩ := I.objectsNonempty
  have sat' := lifted_satisfies N x0 vocab (interpretation_anonymous interp g) good capacity capSmall items enc encRun
    sat
  refine ⟨lifted context I (litOf N embed) (numOf N embed) x0,
    ⟨vocab, lifted_interpretation N x0 interp, Sum.inl ∘ g, ?_⟩,
    fun z => lifted_element N x0 z, fun a plainA => lifted_plain_name plainA,
    fun e mem e' run z => lifted_class N x0 vocab interp good run (plain e mem) z⟩
  rw [lifted_anonymous]
  exact sat'

/-- Class satisfiability with respect to a prepared closure: an answer is
    whether some model of the closure has an instance of the class
    expression, under every datatype map that is the OWL 2 map on the five
    datatypes. -/
theorem prepared_class_satisfiable_correct (items : alloc.vec.Vec AnnotatedAxiom) (p : data_ontology.Prepared)
    (data : DataPrepared items p) (e : ClassExpression) :
    ∃ result, data_ontology.prepared_class_satisfiable p e = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val → Rowl.Unfolding.DefinesNew D items.val → (answer = true ↔ ClassSatisfiable.{u, max w v, w} D V items.val e) := by
  cases p with
  | Plain sp =>
    obtain ⟨result, run, _, facts⟩ := Rowl.ShiOntology.prepared_class_satisfiable_correct.{u,v,w} items sp data e
    exact ⟨result, by simpa [data_ontology.prepared_class_satisfiable] using run,
      fun answer h _ D _ V vocab _ _ => facts answer h D V vocab⟩
  | Defined defs inner =>
    obtain ⟨unfolded, defsRun, unfoldRun, innerData⟩ := data
    obtain ⟨hdefs, proper, unfolds⟩ := defined_facts.{u, max w v} defsRun unfoldRun
    obtain ⟨q, qRun, qFacts⟩ := Rowl.Unfolding.unfold_question_spec.{u, max w v} defs e
    cases q with
    | none => exact ⟨none, by simp [data_ontology.prepared_class_satisfiable, qRun], by simp⟩
    | some e' =>
      obtain ⟨result, run, facts⟩ := prepared_class_satisfiable_correct unfolded inner innerData e'
      refine ⟨result, by simp [data_ontology.prepared_class_satisfiable, qRun, run],
        fun answer h Native D N V vocab names fresh => ?_⟩
      rw [facts answer h D N V vocab (Rowl.Unfolding.names_keyed unfolds names)
        (Rowl.Unfolding.unfolded_defines_new D unfolds)]
      exact (Rowl.Unfolding.unfolded_satisfiable hdefs proper unfolds fresh (qFacts e' rfl)).symm
  | Keyed context nodes sp room =>
    obtain ⟨good, ⟨capacity, counting, enc, capSmall, count, encRun, prepData⟩, nodesExact, keyed⟩ := data
    obtain ⟨b, knownRun, knownFacts⟩ := class_known_spec nodes e
    cases b with
    | false => exact ⟨none, by simp [data_ontology.prepared_class_satisfiable, knownRun], by simp⟩
    | true =>
      obtain ⟨n, countRun, countIs⟩ := class_count_spec e 0#usize (by simp)
      by_cases over : room.val < n.val
      · exact ⟨none, by simp [data_ontology.prepared_class_satisfiable, knownRun, countRun, over], by simp⟩
      have fits : atomCount (itemAtoms items.val) + atomCount (items.val.flatMap (fun i => keyAtoms i.axiom)) +
          atomCount ([e].flatMap classAtoms) ≤ capacity.val := by
        simp only [zero_val, Nat.zero_add] at countIs
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        omega
      obtain ⟨res, classRun⟩ := encode_class_runs context e
      cases res with
      | none =>
        exact ⟨none, by simp [data_ontology.prepared_class_satisfiable, knownRun, countRun, over, classRun], by simp⟩
      | some e' =>
        let query : ClassExpression :=
          .ObjectIntersectionOf ⟨e', .ObjectComplementOf (.Class dataClass), alloc.vec.Vec.new ClassExpression⟩
        obtain ⟨result, run, _, encodedSound⟩ :=
          Rowl.ShiOntology.prepared_class_satisfiable_correct.{u,v,w} enc sp prepData query
        obtain ⟨result', run', _, encodedComplete⟩ :=
          Rowl.ShiOntology.prepared_class_satisfiable_correct.{max u w v,v,w} enc sp prepData query
        have same : result' = result := Result.ok_injective (run'.symm.trans run)
        subst same
        have known : ∀ x ∈ [e], ∀ a ∈ classIndividuals x, KnownTo nodes a := by
          intro x mem
          simp only [List.mem_singleton] at mem
          subst mem
          exact knownFacts rfl
        refine ⟨result', by simp [data_ontology.prepared_class_satisfiable, knownRun, countRun, over, classRun,
          object_class_eq, data_ontology.and, run, query],
          fun answer h Native D N V vocab names _ => ⟨fun yes => ?_, fun holds => ?_⟩⟩
        · obtain ⟨Object', Value', embed', J, model, y, inQuery⟩ := (encodedSound answer h D V vocab).mp yes
          rw [and_denote, object_class_denote] at inQuery
          obtain ⟨Object, Value, embed, I, point, modelI, onto, _, transfer⟩ :=
            keyed_encoded_model.{u,v,w} N vocab good capSmall encRun nodesExact model [e] known fits
          obtain ⟨z, rfl⟩ := onto y inQuery.2
          exact ⟨Object, Value, embed, I, modelI, z, (transfer e (by simp) e' classRun z).mpr inQuery.1⟩
        · obtain ⟨Object, Value, embed, I, model, x, inE⟩ := holds
          obtain ⟨J, modelJ, elements, _, transfer⟩ := keyed_lifted_model.{u,v,w} N vocab good capSmall encRun
            nodesExact names keyed model [e] (fun c mem a inside => keyed_plain good capSmall encRun (known c mem a inside).2)
          apply (encodedComplete answer h D V vocab).mpr
          refine ⟨Object ⊕ Value, Value, embed, J, modelJ, .inl x, ?_⟩
          rw [and_denote, object_class_denote]
          exact ⟨(transfer e (by simp) e' classRun x).mp inE, elements x⟩
  | Encoded context nodes sp room =>
    obtain ⟨good, ⟨capacity, enc, capSmall, count, encRun, prepData⟩, nodesAdd⟩ := data
    obtain ⟨b, knownRun, knownFacts⟩ := class_known_spec nodes e
    cases b with
    | false => exact ⟨none, by simp [data_ontology.prepared_class_satisfiable, knownRun], by simp⟩
    | true =>
      obtain ⟨n, countRun, countIs⟩ := class_count_spec e 0#usize (by simp)
      by_cases over : room.val < n.val
      · exact ⟨none, by simp [data_ontology.prepared_class_satisfiable, knownRun, countRun, over], by simp⟩
      have fits : atomCount (itemAtoms items.val) + atomCount ([e].flatMap classAtoms) ≤ capacity.val := by
        simp only [zero_val, Nat.zero_add] at countIs
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        omega
      obtain ⟨res, classRun⟩ := encode_class_runs context e
      cases res with
      | none =>
        exact ⟨none, by simp [data_ontology.prepared_class_satisfiable, knownRun, countRun, over, classRun], by simp⟩
      | some e' =>
        let query : ClassExpression :=
          .ObjectIntersectionOf ⟨e', .ObjectComplementOf (.Class dataClass), alloc.vec.Vec.new ClassExpression⟩
        obtain ⟨result, run, _, encodedSound⟩ :=
          Rowl.ShiOntology.prepared_class_satisfiable_correct.{u,v,w} enc sp prepData query
        obtain ⟨result', run', _, encodedComplete⟩ :=
          Rowl.ShiOntology.prepared_class_satisfiable_correct.{max u w v,v,w} enc sp prepData query
        have same : result' = result := Result.ok_injective (run'.symm.trans run)
        subst same
        have known : ∀ x ∈ [e], ∀ a ∈ classIndividuals x, KnownTo nodes a := by
          intro x mem
          simp only [List.mem_singleton] at mem
          subst mem
          exact knownFacts rfl
        refine ⟨result', by simp [data_ontology.prepared_class_satisfiable, knownRun, countRun, over, classRun,
          object_class_eq, data_ontology.and, run, query],
          fun answer h Native D N V vocab _ _ => ⟨fun yes => ?_, fun holds => ?_⟩⟩
        · obtain ⟨Object', Value', embed', J, model, y, inQuery⟩ := (encodedSound answer h D V vocab).mp yes
          rw [and_denote, object_class_denote] at inQuery
          obtain ⟨Object, Value, embed, I, point, modelI, onto, _, transfer⟩ :=
            encoded_model.{u,v,w} N vocab good capSmall encRun nodesAdd model [e] known fits
          obtain ⟨z, rfl⟩ := onto y inQuery.2
          exact ⟨Object, Value, embed, I, modelI, z, (transfer e (by simp) e' classRun z).mpr inQuery.1⟩
        · obtain ⟨Object, Value, embed, I, model, x, inE⟩ := holds
          obtain ⟨J, modelJ, elements, _, transfer⟩ := lifted_model.{u,v,w} N vocab good capSmall encRun model [e]
            (fun c mem a inside => known_plain good capSmall encRun nodesAdd (known c mem a inside))
          apply (encodedComplete answer h D V vocab).mpr
          refine ⟨Object ⊕ Value, Value, embed, J, modelJ, .inl x, ?_⟩
          rw [and_denote, object_class_denote]
          exact ⟨(transfer e (by simp) e' classRun x).mp inE, elements x⟩

/-- Subsumption with respect to a prepared closure: an answer is whether every
    instance of `sub` is an instance of `sup` in every model of the closure,
    under every datatype map that is the OWL 2 map on the five datatypes. -/
theorem prepared_subsumed_correct (items : alloc.vec.Vec AnnotatedAxiom) (p : data_ontology.Prepared)
    (data : DataPrepared items p) (sub sup : ClassExpression) :
    ∃ result, data_ontology.prepared_subsumed p sub sup = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val → Rowl.Unfolding.DefinesNew D items.val → (answer = true ↔ Subsumed.{u, max w v, w} D V items.val sub sup) := by
  cases p with
  | Plain sp =>
    obtain ⟨result, run, _, facts⟩ := Rowl.ShiOntology.prepared_subsumed_correct.{u,v,w} items sp data sub sup
    exact ⟨result, by simpa [data_ontology.prepared_subsumed] using run,
      fun answer h _ D _ V vocab _ _ => facts answer h D V vocab⟩
  | Defined defs inner =>
    obtain ⟨unfolded, defsRun, unfoldRun, innerData⟩ := data
    obtain ⟨hdefs, proper, unfolds⟩ := defined_facts.{u, max w v} defsRun unfoldRun
    obtain ⟨q1, q1Run, q1Facts⟩ := Rowl.Unfolding.unfold_question_spec.{u, max w v} defs sub
    obtain ⟨q2, q2Run, q2Facts⟩ := Rowl.Unfolding.unfold_question_spec.{u, max w v} defs sup
    cases q1 with
    | none => exact ⟨none, by simp [data_ontology.prepared_subsumed, q1Run, q2Run], by simp⟩
    | some sub' =>
      cases q2 with
      | none => exact ⟨none, by simp [data_ontology.prepared_subsumed, q1Run, q2Run], by simp⟩
      | some sup' =>
        obtain ⟨result, run, facts⟩ := prepared_subsumed_correct unfolded inner innerData sub' sup'
        refine ⟨result, by simp [data_ontology.prepared_subsumed, q1Run, q2Run, run],
          fun answer h Native D N V vocab names fresh => ?_⟩
        rw [facts answer h D N V vocab (Rowl.Unfolding.names_keyed unfolds names)
          (Rowl.Unfolding.unfolded_defines_new D unfolds)]
        exact (Rowl.Unfolding.unfolded_subsumed hdefs proper unfolds fresh (q1Facts sub' rfl)
          (q2Facts sup' rfl)).symm
  | Keyed context nodes sp room =>
    obtain ⟨good, ⟨capacity, counting, enc, capSmall, count, encRun, prepData⟩, nodesExact, keyed⟩ := data
    obtain ⟨b1, knownRun1, knownFacts1⟩ := class_known_spec nodes sub
    obtain ⟨b2, knownRun2, knownFacts2⟩ := class_known_spec nodes sup
    cases b1 with
    | false => exact ⟨none, by simp [data_ontology.prepared_subsumed, knownRun1], by simp⟩
    | true =>
    cases b2 with
    | false => exact ⟨none, by simp [data_ontology.prepared_subsumed, knownRun1, knownRun2], by simp⟩
    | true =>
    obtain ⟨n1, countRun1, countIs1⟩ := class_count_spec sub 0#usize (by simp)
    obtain ⟨n2, countRun2, countIs2⟩ := class_count_spec sup n1 (by rw [countIs1]; omega)
    by_cases over : room.val < n2.val
    · exact ⟨none, by simp [data_ontology.prepared_subsumed, knownRun1, knownRun2, countRun1, countRun2, over],
        by simp⟩
    have fits : atomCount (itemAtoms items.val) + atomCount (items.val.flatMap (fun i => keyAtoms i.axiom)) +
        atomCount ([sub, sup].flatMap classAtoms) ≤ capacity.val := by
      simp only [zero_val, Nat.zero_add] at countIs1
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, atomCount_append]
      omega
    obtain ⟨r1, classRun1⟩ := encode_class_runs context sub
    obtain ⟨r2, classRun2⟩ := encode_class_runs context sup
    cases r1 with
    | none =>
      exact ⟨none, by simp [data_ontology.prepared_subsumed, knownRun1, knownRun2, countRun1, countRun2, over,
        classRun1, classRun2], by simp⟩
    | some sub' =>
    cases r2 with
    | none =>
      exact ⟨none, by simp [data_ontology.prepared_subsumed, knownRun1, knownRun2, countRun1, countRun2, over,
        classRun1, classRun2], by simp⟩
    | some sup' =>
    let query : ClassExpression :=
      .ObjectIntersectionOf ⟨sub', .ObjectComplementOf (.Class dataClass), alloc.vec.Vec.new ClassExpression⟩
    obtain ⟨result, run, _, encodedSound⟩ :=
      Rowl.ShiOntology.prepared_subsumed_correct.{u,v,w} enc sp prepData query sup'
    obtain ⟨result', run', _, encodedComplete⟩ :=
      Rowl.ShiOntology.prepared_subsumed_correct.{max u w v,v,w} enc sp prepData query sup'
    have same : result' = result := Result.ok_injective (run'.symm.trans run)
    subst same
    have known : ∀ x ∈ [sub, sup], ∀ a ∈ classIndividuals x, KnownTo nodes a := by
      intro x mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact knownFacts1 rfl
      · exact knownFacts2 rfl
    refine ⟨result', by simp [data_ontology.prepared_subsumed, knownRun1, knownRun2, countRun1, countRun2, over,
      classRun1, classRun2, object_class_eq, data_ontology.and, run, query], fun answer h Native D N V vocab names _ =>
        ⟨fun yes => ?_, fun holds => ?_⟩⟩
    · have encodedSubsumed := (encodedComplete answer h D V vocab).mp yes
      intro Object Value embed I model x inSub
      obtain ⟨J, modelJ, elements, _, transfer⟩ := keyed_lifted_model.{u,v,w} N vocab good capSmall encRun nodesExact
        names keyed model [sub, sup] (fun c mem a inside => keyed_plain good capSmall encRun (known c mem a inside).2)
      have inQuery : classDenote J query (.inl x) := by
        rw [and_denote, object_class_denote]
        exact ⟨(transfer sub (by simp) sub' classRun1 x).mp inSub, elements x⟩
      exact (transfer sup (by simp) sup' classRun2 x).mpr (encodedSubsumed _ _ _ J modelJ (.inl x) inQuery)
    · apply (encodedSound answer h D V vocab).mpr
      intro Object' Value' embed' J model y inQuery
      rw [and_denote, object_class_denote] at inQuery
      obtain ⟨Object, Value, embed, I, point, modelI, onto, _, transfer⟩ :=
        keyed_encoded_model.{u,v,w} N vocab good capSmall encRun nodesExact model [sub, sup] known fits
      obtain ⟨z, rfl⟩ := onto y inQuery.2
      exact (transfer sup (by simp) sup' classRun2 z).mp
        (holds Object Value embed I modelI z ((transfer sub (by simp) sub' classRun1 z).mpr inQuery.1))
  | Encoded context nodes sp room =>
    obtain ⟨good, ⟨capacity, enc, capSmall, count, encRun, prepData⟩, nodesAdd⟩ := data
    obtain ⟨b1, knownRun1, knownFacts1⟩ := class_known_spec nodes sub
    obtain ⟨b2, knownRun2, knownFacts2⟩ := class_known_spec nodes sup
    cases b1 with
    | false => exact ⟨none, by simp [data_ontology.prepared_subsumed, knownRun1], by simp⟩
    | true =>
    cases b2 with
    | false => exact ⟨none, by simp [data_ontology.prepared_subsumed, knownRun1, knownRun2], by simp⟩
    | true =>
    obtain ⟨n1, countRun1, countIs1⟩ := class_count_spec sub 0#usize (by simp)
    obtain ⟨n2, countRun2, countIs2⟩ := class_count_spec sup n1 (by rw [countIs1]; omega)
    by_cases over : room.val < n2.val
    · exact ⟨none, by simp [data_ontology.prepared_subsumed, knownRun1, knownRun2, countRun1, countRun2, over],
        by simp⟩
    have fits : atomCount (itemAtoms items.val) + atomCount ([sub, sup].flatMap classAtoms) ≤ capacity.val := by
      simp only [zero_val, Nat.zero_add] at countIs1
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, atomCount_append]
      omega
    obtain ⟨r1, classRun1⟩ := encode_class_runs context sub
    obtain ⟨r2, classRun2⟩ := encode_class_runs context sup
    cases r1 with
    | none =>
      exact ⟨none, by simp [data_ontology.prepared_subsumed, knownRun1, knownRun2, countRun1, countRun2, over,
        classRun1, classRun2], by simp⟩
    | some sub' =>
    cases r2 with
    | none =>
      exact ⟨none, by simp [data_ontology.prepared_subsumed, knownRun1, knownRun2, countRun1, countRun2, over,
        classRun1, classRun2], by simp⟩
    | some sup' =>
    let query : ClassExpression :=
      .ObjectIntersectionOf ⟨sub', .ObjectComplementOf (.Class dataClass), alloc.vec.Vec.new ClassExpression⟩
    obtain ⟨result, run, _, encodedSound⟩ :=
      Rowl.ShiOntology.prepared_subsumed_correct.{u,v,w} enc sp prepData query sup'
    obtain ⟨result', run', _, encodedComplete⟩ :=
      Rowl.ShiOntology.prepared_subsumed_correct.{max u w v,v,w} enc sp prepData query sup'
    have same : result' = result := Result.ok_injective (run'.symm.trans run)
    subst same
    have known : ∀ x ∈ [sub, sup], ∀ a ∈ classIndividuals x, KnownTo nodes a := by
      intro x mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact knownFacts1 rfl
      · exact knownFacts2 rfl
    refine ⟨result', by simp [data_ontology.prepared_subsumed, knownRun1, knownRun2, countRun1, countRun2, over,
      classRun1, classRun2, object_class_eq, data_ontology.and, run, query],
      fun answer h Native D N V vocab _ _ => ⟨fun yes => ?_, fun holds => ?_⟩⟩
    · have encodedSubsumed := (encodedComplete answer h D V vocab).mp yes
      intro Object Value embed I model x inSub
      obtain ⟨J, modelJ, elements, _, transfer⟩ := lifted_model.{u,v,w} N vocab good capSmall encRun model [sub, sup]
        (fun c mem a inside => known_plain good capSmall encRun nodesAdd (known c mem a inside))
      have inQuery : classDenote J query (.inl x) := by
        rw [and_denote, object_class_denote]
        exact ⟨(transfer sub (by simp) sub' classRun1 x).mp inSub, elements x⟩
      exact (transfer sup (by simp) sup' classRun2 x).mpr (encodedSubsumed _ _ _ J modelJ (.inl x) inQuery)
    · apply (encodedSound answer h D V vocab).mpr
      intro Object' Value' embed' J model y inQuery
      rw [and_denote, object_class_denote] at inQuery
      obtain ⟨Object, Value, embed, I, point, modelI, onto, _, transfer⟩ :=
        encoded_model.{u,v,w} N vocab good capSmall encRun nodesAdd model [sub, sup] known fits
      obtain ⟨z, rfl⟩ := onto y inQuery.2
      exact (transfer sup (by simp) sup' classRun2 z).mp
        (holds Object Value embed I modelI z ((transfer sub (by simp) sub' classRun1 z).mpr inQuery.1))

/-- Instance checking with respect to a prepared closure: an answer is
    whether the named individual is an instance of the class expression in
    every model of the closure, under every datatype map that is the OWL 2 map
    on the five datatypes. -/
theorem prepared_instance_of_correct (items : alloc.vec.Vec AnnotatedAxiom) (p : data_ontology.Prepared)
    (data : DataPrepared items p) (a : NamedIndividual) (e : ClassExpression) :
    ∃ result, data_ontology.prepared_instance_of p a e = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val → Rowl.Unfolding.DefinesNew D items.val → (answer = true ↔ InstanceOf.{u, max w v, w} D V items.val a e) := by
  cases p with
  | Plain sp =>
    obtain ⟨result, run, _, facts⟩ := Rowl.ShiOntology.prepared_instance_of_correct.{u,v,w} items sp data a e
    exact ⟨result, by simpa [data_ontology.prepared_instance_of] using run,
      fun answer h _ D _ V vocab _ _ => facts answer h D V vocab⟩
  | Defined defs inner =>
    obtain ⟨unfolded, defsRun, unfoldRun, innerData⟩ := data
    obtain ⟨hdefs, proper, unfolds⟩ := defined_facts.{u, max w v} defsRun unfoldRun
    obtain ⟨q, qRun, qFacts⟩ := Rowl.Unfolding.unfold_question_spec.{u, max w v} defs e
    cases q with
    | none => exact ⟨none, by simp [data_ontology.prepared_instance_of, qRun], by simp⟩
    | some e' =>
      obtain ⟨result, run, facts⟩ := prepared_instance_of_correct unfolded inner innerData a e'
      refine ⟨result, by simp [data_ontology.prepared_instance_of, qRun, run],
        fun answer h Native D N V vocab names fresh => ?_⟩
      rw [facts answer h D N V vocab (Rowl.Unfolding.names_keyed unfolds names)
        (Rowl.Unfolding.unfolded_defines_new D unfolds)]
      exact (Rowl.Unfolding.unfolded_instance hdefs proper unfolds fresh a (qFacts e' rfl)).symm
  | Keyed context nodes sp room =>
    obtain ⟨good, ⟨capacity, counting, enc, capSmall, count, encRun, prepData⟩, nodesExact, keyed⟩ := data
    obtain ⟨k, namedRun, namedFacts⟩ := named_known_spec nodes a
    cases k with
    | false => exact ⟨none, by simp [data_ontology.prepared_instance_of, namedRun], by simp⟩
    | true =>
    obtain ⟨plainA, aIn⟩ := namedFacts rfl
    obtain ⟨b, knownRun, knownFacts⟩ := class_known_spec nodes e
    cases b with
    | false =>
      exact ⟨none, by simp [data_ontology.prepared_instance_of, namedRun, knownRun], by simp⟩
    | true =>
    obtain ⟨n, countRun, countIs⟩ := class_count_spec e 0#usize (by simp)
    by_cases over : room.val < n.val
    · exact ⟨none, by simp [data_ontology.prepared_instance_of, namedRun, knownRun, countRun, over], by simp⟩
    have fits : atomCount (itemAtoms items.val) + atomCount (items.val.flatMap (fun i => keyAtoms i.axiom)) +
        atomCount ([e].flatMap classAtoms) ≤ capacity.val := by
      simp only [zero_val, Nat.zero_add] at countIs
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      omega
    obtain ⟨res, classRun⟩ := encode_class_runs context e
    cases res with
    | none =>
      exact ⟨none, by simp [data_ontology.prepared_instance_of, namedRun, knownRun, countRun, over, classRun], by simp⟩
    | some e' =>
    let query : ClassExpression := .ObjectUnionOf ⟨e', .Class dataClass, alloc.vec.Vec.new ClassExpression⟩
    obtain ⟨result, run, _, encodedSound⟩ :=
      Rowl.ShiOntology.prepared_instance_of_correct.{u,v,w} enc sp prepData a query
    obtain ⟨result', run', _, encodedComplete⟩ :=
      Rowl.ShiOntology.prepared_instance_of_correct.{max u w v,v,w} enc sp prepData a query
    have same : result' = result := Result.ok_injective (run'.symm.trans run)
    subst same
    have known : ∀ x ∈ [e], ∀ b ∈ classIndividuals x, KnownTo nodes b := by
      intro x mem
      simp only [List.mem_singleton] at mem
      subst mem
      exact knownFacts rfl
    refine ⟨result', by simp [data_ontology.prepared_instance_of, namedRun, knownRun, countRun, over, classRun,
      data_class_eq, data_ontology.or, run, query], fun answer h Native D N V vocab names _ =>
        ⟨fun yes => ?_, fun holds => ?_⟩⟩
    · have encodedInstance := (encodedComplete answer h D V vocab).mp yes
      intro Object Value embed I model
      obtain ⟨J, modelJ, elements, namesJ, transfer⟩ := keyed_lifted_model.{u,v,w} N vocab good capSmall encRun
        nodesExact names keyed model [e] (fun c mem b inside => keyed_plain good capSmall encRun (known c mem b inside).2)
      have holdsJ := encodedInstance _ _ _ J modelJ
      rw [or_denote, namesJ a plainA] at holdsJ
      rcases holdsJ with inE | isData
      · exact (transfer e (by simp) e' classRun _).mpr inE
      · exact absurd ((class_denote_named J _ _).mp isData) (elements _)
    · apply (encodedSound answer h D V vocab).mpr
      intro Object' Value' embed' J model
      rw [or_denote]
      by_cases isData : J.classes dataClass (J.namedIndividuals a)
      · exact .inr ((class_denote_named J _ _).mpr isData)
      · obtain ⟨Object, Value, embed, I, point, modelI, _, names', transfer⟩ :=
          keyed_encoded_model.{u,v,w} N vocab good capSmall encRun nodesExact model [e] known fits
        left
        rw [← (names' a aIn).2]
        exact (transfer e (by simp) e' classRun _).mp (holds Object Value embed I modelI)
  | Encoded context nodes sp room =>
    obtain ⟨good, ⟨capacity, enc, capSmall, count, encRun, prepData⟩, nodesAdd⟩ := data
    by_cases reserved : Reserved a.iri.spelling.val
    · exact ⟨none, by simp [data_ontology.prepared_instance_of, reserved_correct, reserved], by simp⟩
    obtain ⟨b, knownRun, knownFacts⟩ := class_known_spec nodes e
    cases b with
    | false =>
      exact ⟨none, by simp [data_ontology.prepared_instance_of, reserved_correct, reserved, knownRun], by simp⟩
    | true =>
    obtain ⟨n, countRun, countIs⟩ := class_count_spec e 0#usize (by simp)
    by_cases over : room.val < n.val
    · exact ⟨none, by simp [data_ontology.prepared_instance_of, reserved_correct, reserved, knownRun, countRun, over],
        by simp⟩
    have fits : atomCount (itemAtoms items.val) + atomCount ([e].flatMap classAtoms) ≤ capacity.val := by
      simp only [zero_val, Nat.zero_add] at countIs
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      omega
    obtain ⟨res, classRun⟩ := encode_class_runs context e
    cases res with
    | none =>
      exact ⟨none, by simp [data_ontology.prepared_instance_of, reserved_correct, reserved, knownRun, countRun, over,
        classRun], by simp⟩
    | some e' =>
    let query : ClassExpression := .ObjectUnionOf ⟨e', .Class dataClass, alloc.vec.Vec.new ClassExpression⟩
    obtain ⟨result, run, _, encodedSound⟩ :=
      Rowl.ShiOntology.prepared_instance_of_correct.{u,v,w} enc sp prepData a query
    obtain ⟨result', run', _, encodedComplete⟩ :=
      Rowl.ShiOntology.prepared_instance_of_correct.{max u w v,v,w} enc sp prepData a query
    have same : result' = result := Result.ok_injective (run'.symm.trans run)
    subst same
    have known : ∀ x ∈ [e], ∀ b ∈ classIndividuals x, KnownTo nodes b := by
      intro x mem
      simp only [List.mem_singleton] at mem
      subst mem
      exact knownFacts rfl
    refine ⟨result', by simp [data_ontology.prepared_instance_of, reserved_correct, reserved, knownRun, countRun,
      over, classRun, data_class_eq, data_ontology.or, run, query],
      fun answer h Native D N V vocab _ _ => ⟨fun yes => ?_, fun holds => ?_⟩⟩
    · have encodedInstance := (encodedComplete answer h D V vocab).mp yes
      intro Object Value embed I model
      obtain ⟨J, modelJ, elements, names, transfer⟩ := lifted_model.{u,v,w} N vocab good capSmall encRun model [e]
        (fun c mem b inside => known_plain good capSmall encRun nodesAdd (known c mem b inside))
      have holdsJ := encodedInstance _ _ _ J modelJ
      rw [or_denote, names a reserved] at holdsJ
      rcases holdsJ with inE | isData
      · exact (transfer e (by simp) e' classRun _).mpr inE
      · exact absurd ((class_denote_named J _ _).mp isData) (elements _)
    · apply (encodedSound answer h D V vocab).mpr
      intro Object' Value' embed' J model
      rw [or_denote]
      by_cases isData : J.classes dataClass (J.namedIndividuals a)
      · exact .inr ((class_denote_named J _ _).mpr isData)
      · obtain ⟨Object, Value, embed, I, point, modelI, _, names, transfer⟩ :=
          encoded_model.{u,v,w} N vocab good capSmall encRun nodesAdd model [e] known fits
        left
        rw [← names a isData]
        exact (transfer e (by simp) e' classRun _).mp (holds Object Value embed I modelI)

/-- Consistency of a closure without datatype definitions. -/
theorem consistent_closure_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, data_ontology.consistent_closure items = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val → Rowl.Unfolding.DefinesNew D items.val → (answer = true ↔ Consistent.{u, max w v, w} D V items.val) := by
  obtain ⟨c1, run1, good1⟩ := closure_context_good items
  obtain ⟨c2, run2, good2⟩ := finished_good c1 good1
  obtain ⟨res, run, facts⟩ := prepare_in_correct items c2 good2 0#usize
  cases res with
  | none => exact ⟨none, by simp [data_ontology.consistent_closure, run1, run2, run], by simp⟩
  | some p =>
    obtain ⟨result, run', facts'⟩ := prepared_consistent_correct.{u,v,w} items p (facts p rfl)
    exact ⟨result, by simp [data_ontology.consistent_closure, run1, run2, run, run'], facts'⟩

/-- Class satisfiability with respect to a closure without datatype definitions. -/
theorem class_satisfiable_closure_correct (items : alloc.vec.Vec AnnotatedAxiom) (e : ClassExpression) :
    ∃ result, data_ontology.class_satisfiable_closure items e = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val → Rowl.Unfolding.DefinesNew D items.val → (answer = true ↔ ClassSatisfiable.{u, max w v, w} D V items.val e) := by
  obtain ⟨c1, run1, good1⟩ := closure_context_good items
  obtain ⟨c2, run2, good2⟩ := class_context_good e c1 good1
  obtain ⟨c3, run3, good3⟩ := finished_good c2 good2
  obtain ⟨n, countRun, _⟩ := class_count_spec e 0#usize (by simp)
  obtain ⟨res, run, facts⟩ := prepare_in_correct items c3 good3 n
  cases res with
  | none => exact ⟨none, by simp [data_ontology.class_satisfiable_closure, run1, run2, run3, countRun, run], by simp⟩
  | some p =>
    obtain ⟨result, run', facts'⟩ := prepared_class_satisfiable_correct.{u,v,w} items p (facts p rfl) e
    exact ⟨result, by simp [data_ontology.class_satisfiable_closure, run1, run2, run3, countRun, run, run'], facts'⟩

/-- Subsumption with respect to a closure without datatype definitions. -/
theorem subsumed_closure_correct (items : alloc.vec.Vec AnnotatedAxiom) (sub sup : ClassExpression) :
    ∃ result, data_ontology.subsumed_closure items sub sup = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val → Rowl.Unfolding.DefinesNew D items.val → (answer = true ↔ Subsumed.{u, max w v, w} D V items.val sub sup) := by
  obtain ⟨c1, run1, good1⟩ := closure_context_good items
  obtain ⟨c2, run2, good2⟩ := class_context_good sub c1 good1
  obtain ⟨c3, run3, good3⟩ := class_context_good sup c2 good2
  obtain ⟨c4, run4, good4⟩ := finished_good c3 good3
  obtain ⟨n1, countRun1, countIs1⟩ := class_count_spec sub 0#usize (by simp)
  obtain ⟨n2, countRun2, _⟩ := class_count_spec sup n1 (by rw [countIs1]; omega)
  obtain ⟨res, run, facts⟩ := prepare_in_correct items c4 good4 n2
  cases res with
  | none =>
    exact ⟨none, by simp [data_ontology.subsumed_closure, run1, run2, run3, run4, countRun1, countRun2, run], by simp⟩
  | some p =>
    obtain ⟨result, run', facts'⟩ := prepared_subsumed_correct.{u,v,w} items p (facts p rfl) sub sup
    exact ⟨result, by simp [data_ontology.subsumed_closure, run1, run2, run3, run4, countRun1, countRun2, run, run'],
      facts'⟩

/-- Instance checking with respect to a closure without datatype definitions. -/
theorem instance_of_closure_correct (items : alloc.vec.Vec AnnotatedAxiom) (a : NamedIndividual) (e : ClassExpression) :
    ∃ result, data_ontology.instance_of_closure items a e = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val → Rowl.Unfolding.DefinesNew D items.val → (answer = true ↔ InstanceOf.{u, max w v, w} D V items.val a e) := by
  obtain ⟨c1, run1, good1⟩ := closure_context_good items
  obtain ⟨c2, run2, good2⟩ := class_context_good e c1 good1
  obtain ⟨c3, run3, good3⟩ := finished_good c2 good2
  obtain ⟨n, countRun, _⟩ := class_count_spec e 0#usize (by simp)
  obtain ⟨res, run, facts⟩ := prepare_in_correct items c3 good3 n
  cases res with
  | none => exact ⟨none, by simp [data_ontology.instance_of_closure, run1, run2, run3, countRun, run], by simp⟩
  | some p =>
    obtain ⟨result, run', facts'⟩ := prepared_instance_of_correct.{u,v,w} items p (facts p rfl) a e
    exact ⟨result, by simp [data_ontology.instance_of_closure, run1, run2, run3, countRun, run, run'], facts'⟩

/-- Consistency of a closure: one with datatype definitions is unfolded
    first (`Rowl.Unfolding.unfolded_consistent`). -/
theorem consistent_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, data_ontology.consistent items = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val → Rowl.Unfolding.DefinesNew D items.val →
          (answer = true ↔ Consistent.{u, max w v, w} D V items.val) := by
  obtain ⟨b, hasRun⟩ := Rowl.Unfolding.has_definitions_runs items 0#usize
  cases b with
  | false =>
    obtain ⟨result, run, facts⟩ := consistent_closure_correct.{u,v,w} items
    exact ⟨result, by simp [data_ontology.consistent, hasRun, run], facts⟩
  | true =>
    obtain ⟨defs, defsRun, _⟩ := Rowl.Unfolding.definitions_spec items
    obtain ⟨res, unfoldRun, _⟩ := Rowl.Unfolding.unfold_items_spec.{0,0} defs items
    cases res with
    | none => exact ⟨none, by simp [data_ontology.consistent, hasRun, defsRun, unfoldRun], by simp⟩
    | some unfolded =>
      obtain ⟨hdefs, proper, unfolds⟩ := defined_facts.{u, max w v} defsRun unfoldRun
      obtain ⟨result, run, facts⟩ := consistent_closure_correct.{u,v,w} unfolded
      refine ⟨result, by simp [data_ontology.consistent, hasRun, defsRun, unfoldRun, run],
        fun answer h Native D N V vocab names fresh => ?_⟩
      rw [facts answer h D N V vocab (Rowl.Unfolding.names_keyed unfolds names)
        (Rowl.Unfolding.unfolded_defines_new D unfolds)]
      exact (Rowl.Unfolding.unfolded_consistent hdefs proper unfolds fresh).symm

/-- Class satisfiability with respect to a closure. -/
theorem class_satisfiable_correct (items : alloc.vec.Vec AnnotatedAxiom) (e : ClassExpression) :
    ∃ result, data_ontology.class_satisfiable items e = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val → Rowl.Unfolding.DefinesNew D items.val →
          (answer = true ↔ ClassSatisfiable.{u, max w v, w} D V items.val e) := by
  obtain ⟨b, hasRun⟩ := Rowl.Unfolding.has_definitions_runs items 0#usize
  cases b with
  | false =>
    obtain ⟨result, run, facts⟩ := class_satisfiable_closure_correct.{u,v,w} items e
    exact ⟨result, by simp [data_ontology.class_satisfiable, hasRun, run], facts⟩
  | true =>
    obtain ⟨defs, defsRun, _⟩ := Rowl.Unfolding.definitions_spec items
    obtain ⟨res, unfoldRun, _⟩ := Rowl.Unfolding.unfold_items_spec.{0,0} defs items
    obtain ⟨q, qRun, qFacts⟩ := Rowl.Unfolding.unfold_question_spec.{u, max w v} defs e
    cases res with
    | none => exact ⟨none, by simp [data_ontology.class_satisfiable, hasRun, defsRun, unfoldRun, qRun], by simp⟩
    | some unfolded =>
      cases q with
      | none =>
        exact ⟨none, by simp [data_ontology.class_satisfiable, hasRun, defsRun, unfoldRun, qRun], by simp⟩
      | some e' =>
        obtain ⟨hdefs, proper, unfolds⟩ := defined_facts.{u, max w v} defsRun unfoldRun
        obtain ⟨result, run, facts⟩ := class_satisfiable_closure_correct.{u,v,w} unfolded e'
        refine ⟨result, by simp [data_ontology.class_satisfiable, hasRun, defsRun, unfoldRun, qRun, run],
          fun answer h Native D N V vocab names fresh => ?_⟩
        rw [facts answer h D N V vocab (Rowl.Unfolding.names_keyed unfolds names)
          (Rowl.Unfolding.unfolded_defines_new D unfolds)]
        exact (Rowl.Unfolding.unfolded_satisfiable hdefs proper unfolds fresh (qFacts e' rfl)).symm

/-- Subsumption with respect to a closure. -/
theorem subsumed_correct (items : alloc.vec.Vec AnnotatedAxiom) (sub sup : ClassExpression) :
    ∃ result, data_ontology.subsumed items sub sup = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val → Rowl.Unfolding.DefinesNew D items.val →
          (answer = true ↔ Subsumed.{u, max w v, w} D V items.val sub sup) := by
  obtain ⟨b, hasRun⟩ := Rowl.Unfolding.has_definitions_runs items 0#usize
  cases b with
  | false =>
    obtain ⟨result, run, facts⟩ := subsumed_closure_correct.{u,v,w} items sub sup
    exact ⟨result, by simp [data_ontology.subsumed, hasRun, run], facts⟩
  | true =>
    obtain ⟨defs, defsRun, _⟩ := Rowl.Unfolding.definitions_spec items
    obtain ⟨res, unfoldRun, _⟩ := Rowl.Unfolding.unfold_items_spec.{0,0} defs items
    obtain ⟨q1, q1Run, q1Facts⟩ := Rowl.Unfolding.unfold_question_spec.{u, max w v} defs sub
    obtain ⟨q2, q2Run, q2Facts⟩ := Rowl.Unfolding.unfold_question_spec.{u, max w v} defs sup
    cases res with
    | none =>
      exact ⟨none, by simp [data_ontology.subsumed, hasRun, defsRun, unfoldRun, q1Run, q2Run], by simp⟩
    | some unfolded =>
      cases q1 with
      | none =>
        exact ⟨none, by simp [data_ontology.subsumed, hasRun, defsRun, unfoldRun, q1Run, q2Run], by simp⟩
      | some sub' =>
        cases q2 with
        | none =>
          exact ⟨none, by simp [data_ontology.subsumed, hasRun, defsRun, unfoldRun, q1Run, q2Run], by simp⟩
        | some sup' =>
          obtain ⟨hdefs, proper, unfolds⟩ := defined_facts.{u, max w v} defsRun unfoldRun
          obtain ⟨result, run, facts⟩ := subsumed_closure_correct.{u,v,w} unfolded sub' sup'
          refine ⟨result, by simp [data_ontology.subsumed, hasRun, defsRun, unfoldRun, q1Run, q2Run, run],
            fun answer h Native D N V vocab names fresh => ?_⟩
          rw [facts answer h D N V vocab (Rowl.Unfolding.names_keyed unfolds names)
            (Rowl.Unfolding.unfolded_defines_new D unfolds)]
          exact (Rowl.Unfolding.unfolded_subsumed hdefs proper unfolds fresh (q1Facts sub' rfl)
            (q2Facts sup' rfl)).symm

/-- Instance checking with respect to a closure. -/
theorem instance_of_correct (items : alloc.vec.Vec AnnotatedAxiom) (a : NamedIndividual) (e : ClassExpression) :
    ∃ result, data_ontology.instance_of items a e = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        NamesKeyed V items.val → Rowl.Unfolding.DefinesNew D items.val →
          (answer = true ↔ InstanceOf.{u, max w v, w} D V items.val a e) := by
  obtain ⟨b, hasRun⟩ := Rowl.Unfolding.has_definitions_runs items 0#usize
  cases b with
  | false =>
    obtain ⟨result, run, facts⟩ := instance_of_closure_correct.{u,v,w} items a e
    exact ⟨result, by simp [data_ontology.instance_of, hasRun, run], facts⟩
  | true =>
    obtain ⟨defs, defsRun, _⟩ := Rowl.Unfolding.definitions_spec items
    obtain ⟨res, unfoldRun, _⟩ := Rowl.Unfolding.unfold_items_spec.{0,0} defs items
    obtain ⟨q, qRun, qFacts⟩ := Rowl.Unfolding.unfold_question_spec.{u, max w v} defs e
    cases res with
    | none => exact ⟨none, by simp [data_ontology.instance_of, hasRun, defsRun, unfoldRun, qRun], by simp⟩
    | some unfolded =>
      cases q with
      | none =>
        exact ⟨none, by simp [data_ontology.instance_of, hasRun, defsRun, unfoldRun, qRun], by simp⟩
      | some e' =>
        obtain ⟨hdefs, proper, unfolds⟩ := defined_facts.{u, max w v} defsRun unfoldRun
        obtain ⟨result, run, facts⟩ := instance_of_closure_correct.{u,v,w} unfolded a e'
        refine ⟨result, by simp [data_ontology.instance_of, hasRun, defsRun, unfoldRun, qRun, run],
          fun answer h Native D N V vocab names fresh => ?_⟩
        rw [facts answer h D N V vocab (Rowl.Unfolding.names_keyed unfolds names)
          (Rowl.Unfolding.unfolded_defines_new D unfolds)]
        exact (Rowl.Unfolding.unfolded_instance hdefs proper unfolds fresh a (qFacts e' rfl)).symm

end Rowl.DataOntology
