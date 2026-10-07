import Rowl.Partition
import Rowl.KeyEncoding
import Rowl.DataEncoding
import Rowl.Datatypes
import Rowl.DataOntology

/-!
# The part of a closure for one individual

`components::component_closure` checks that every axiom of a closure is plain
(`Rowl.Partition.PlainAxiom`), an assertion that is plain
(`Rowl.Partition.PlainAssertion`) or without meaning, finds the component of a
named individual, checks that every assertion that names one of its
individuals names only its individuals, and copies the axioms other than
assertions and declarations and the assertions about the component.
`part_instance_correct` gives the result the conditions of
`Rowl.Partition.instance_part`: when the closure has a model, an instance
question about the individual has the same answer for the part.

`components::closure_parts` finds all components once, each with its part,
and `parts_instance_correct` gives every member of a component the part of
its component, and every other individual the axioms other than assertions.

`components::consistent_by_parts` decides consistency in the same way: it
checks the axioms other than assertions, then the part of each component in
turn, and `consistent_by_parts_correct` proves its answer to be whether the
closure has a model (`Rowl.Partition.consistent_join`).
-/

namespace Rowl.Components
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model Rowl.Owl Rowl.Partition
open Rowl.DatatypeMap
open Rowl.DataMeaning (classIndividuals)
open Rowl.DataAxioms (axiomIndividuals)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

universe u v w

/-! ## Kinds of axioms -/

private theorem assertion_eq (ax : Axiom) : components.assertion ax = .ok (decide (IsAssertion ax)) := by
  cases ax <;> simp [components.assertion, IsAssertion]

private theorem meaningless_eq (ax : Axiom) : components.meaningless ax = .ok (decide (Meaningless ax)) := by
  cases ax <;> simp [components.meaningless, Meaningless]

/-! ## Roles and data properties -/

private theorem plain_role_eq (r : ObjectPropertyExpression) : components.plain_role r = .ok (decide (NotTop r)) := by
  cases r <;> simp [components.plain_role, Rowl.DataEncoding.universal_correct, NotTop,
    Rowl.AlcOntology.RoleOf]

private theorem plain_data_eq (p : DataProperty) : components.plain_data p = .ok (decide (p ≠ topData)) := by
  simp [components.plain_data, Rowl.DataEncoding.is_top_data_correct]

private theorem plain_roles_spec (roles : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) :
    ∃ b, components.plain_roles roles index = .ok b ∧ (b = true → ∀ r ∈ roles.val.drop index.val, NotTop r) := by
  rw [components.plain_roles]
  by_cases more : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    by_cases here : NotTop roles.val[index.val]
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b, run, facts⟩ := plain_roles_spec roles next
      refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, plain_role_eq, here, advance, run], fun yes r member => ?_⟩
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact here
      · exact facts yes r (by rw [nextIs]; exact later)
    · exact ⟨false, by simp [UScalar.lt_equiv, more, lookup, plain_role_eq, here], by simp⟩
  · refine ⟨true, by simp [UScalar.lt_equiv, more], fun _ r member => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)] at member
    cases member
termination_by roles.val.length - index.val
decreasing_by omega

private theorem plain_role_members_spec (roles : AtLeastTwo ObjectPropertyExpression) :
    ∃ b, components.plain_role_members roles = .ok b ∧ (b = true → ∀ r ∈ roles.elements, NotTop r) := by
  rw [components.plain_role_members]
  by_cases first : NotTop roles.first
  · by_cases second : NotTop roles.second
    · obtain ⟨b, run, facts⟩ := plain_roles_spec roles.rest 0#usize
      refine ⟨b, by simp [plain_role_eq, first, second, run], fun yes r member => ?_⟩
      simp only [AtLeastTwo.elements, List.mem_cons] at member
      rcases member with rfl | rfl | rest
      · exact first
      · exact second
      · exact facts yes r (by simpa using rest)
    · exact ⟨false, by simp [plain_role_eq, first, second], by simp⟩
  · exact ⟨false, by simp [plain_role_eq, first], by simp⟩

private theorem plain_data_list_spec (properties : alloc.vec.Vec DataProperty) (index : Usize) :
    ∃ b, components.plain_data_list properties index = .ok b ∧
      (b = true → ∀ p ∈ properties.val.drop index.val, p ≠ topData) := by
  rw [components.plain_data_list]
  by_cases more : index.val < properties.val.length
  · have lookup : properties.index_usize index = .ok properties.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    by_cases here : properties.val[index.val] ≠ topData
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b, run, facts⟩ := plain_data_list_spec properties next
      refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, plain_data_eq, here, advance, run], fun yes p member => ?_⟩
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact here
      · exact facts yes p (by rw [nextIs]; exact later)
    · refine ⟨false, ?_, by simp⟩
      simp only [ne_eq, not_not] at here
      simp [UScalar.lt_equiv, more, lookup, plain_data_eq, here]
  · refine ⟨true, by simp [UScalar.lt_equiv, more], fun _ p member => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)] at member
    cases member
termination_by properties.val.length - index.val
decreasing_by omega

private theorem plain_data_members_spec (properties : AtLeastTwo DataProperty) :
    ∃ b, components.plain_data_members properties = .ok b ∧ (b = true → ∀ p ∈ properties.elements, p ≠ topData) := by
  rw [components.plain_data_members]
  by_cases first : properties.first ≠ topData
  · by_cases second : properties.second ≠ topData
    · obtain ⟨b, run, facts⟩ := plain_data_list_spec properties.rest 0#usize
      refine ⟨b, by simp [plain_data_eq, first, second, run], fun yes p member => ?_⟩
      simp only [AtLeastTwo.elements, List.mem_cons] at member
      rcases member with rfl | rfl | rest
      · exact first
      · exact second
      · exact facts yes p (by simpa using rest)
    · refine ⟨false, ?_, by simp⟩
      simp only [ne_eq, not_not] at second
      simp [plain_data_eq, first, second]
  · refine ⟨false, ?_, by simp⟩
    simp only [ne_eq, not_not] at first
    simp [plain_data_eq, first]

/-! ## Data the queries know -/

/-- A property of a closure that holds under every datatype map that is the
    OWL 2 map on the datatypes of `datatypes`, for every vocabulary. -/
def Normal (P : ∀ {Native : Type w}, DatatypeMap Native → Vocabulary → Prop) : Prop :=
  ∀ {Native : Type w} (D : DatatypeMap Native), Normative D → ∀ V, IsVocabulary D V → P D V

private theorem known_datatype_spec (dt : Datatype) :
    ∃ b, components.known_datatype dt = .ok b ∧
      (b = true → Normal.{w} fun D _ => D.supported dt ∨ dt = literalDatatype) := by
  rw [components.known_datatype, Rowl.Datatypes.kind_of_correct]
  cases kind : Rowl.Datatypes.kindOf dt with
  | none =>
    refine ⟨decide (dt = literalDatatype), by simp [Rowl.DataEncoding.is_literal_correct], ?_⟩
    intro yes _ D _ _ _
    exact .inr (of_decide_eq_true yes)
  | some k =>
    refine ⟨true, by simp, fun _ _ D N _ _ => .inl ?_⟩
    rw [Rowl.Datatypes.kindOf_some kind]
    exact Rowl.Datatypes.normative_supported N k

private theorem known_literal_spec (lt : Literal) :
    ∃ b, components.known_literal lt = .ok b ∧ (b = true → Normal.{w} fun _ V => V.literals lt) := by
  obtain ⟨r, run, some', -⟩ := Rowl.Datatypes.literal_value_correct.{w} lt
  rw [components.known_literal, run]
  cases r with
  | none => exact ⟨false, by simp, by simp⟩
  | some value =>
    refine ⟨true, by simp, fun _ _ D N V vocab => ?_⟩
    obtain ⟨-, k, -, -, facts⟩ := some' value rfl
    obtain ⟨supported, lexical, -⟩ := facts D N
    exact (vocab.2.2.2.2.2.2.2.2.1 lt).mpr ⟨supported, lexical⟩

private theorem known_literals_spec (literals : alloc.vec.Vec Literal) (index : Usize) :
    ∃ b, components.known_literals literals index = .ok b ∧
      (b = true → ∀ lt ∈ literals.val.drop index.val, Normal.{w} fun _ V => V.literals lt) := by
  rw [components.known_literals]
  by_cases more : index.val < literals.val.length
  · have lookup : literals.index_usize index = .ok literals.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    obtain ⟨b1, run1, facts1⟩ := known_literal_spec.{w} literals.val[index.val]
    cases b1 with
    | false => exact ⟨false, by simp [UScalar.lt_equiv, more, lookup, run1], by simp⟩
    | true =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b, run, facts⟩ := known_literals_spec literals next
      refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, run1, advance, run], fun yes lt member => ?_⟩
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact facts1 rfl
      · exact facts yes lt (by rw [nextIs]; exact later)
  · refine ⟨true, by simp [UScalar.lt_equiv, more], fun _ lt member => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)] at member
    cases member
termination_by literals.val.length - index.val
decreasing_by omega

private theorem facetOf_some {iri : Iri} {F : datatypes.Facet} (h : Rowl.Datatypes.facetOf iri = some F) :
    iri ∈ rangeFacets := by
  unfold Rowl.Datatypes.facetOf at h
  split_ifs at h with h1 h2 h3 h4 <;> simp_all [rangeFacets]

private theorem number_real {Native : Type w} {D : DatatypeMap Native} (N : Normative D) (v : datatypes.DataValue)
    (number : Rowl.Datatypes.IsNumber v) : ∃ r, Rowl.Datatypes.valueOf N v = N.real r := by
  cases v with
  | Number n whole fraction => exact ⟨_, Rowl.Datatypes.real_rat N _⟩
  | Fraction n a b => exact ⟨_, Rowl.Datatypes.real_rat N _⟩
  | Text _ | Tagged _ _ | Truth _ | Uri _ | Hex _ | Base64 _ | Moment _ => simp [Rowl.Datatypes.IsNumber] at number

/-- The facet value of a range facet with a real bound has only datatype values. -/
private theorem range_values {Native : Type w} {D : DatatypeMap Native} (N : Normative D) {iri : Iri} (range : iri ∈ rangeFacets)
    (r : ℝ) (y : Native) (has : D.facetValue iri (N.real r) y) : isDatatypeValue D y := by
  have real : ∀ s, isDatatypeValue D (N.real s) := fun s => ⟨realType, N.real_supported, (N.real_space _).mpr ⟨s, rfl⟩⟩
  simp only [rangeFacets, List.mem_cons, List.mem_nil_iff, or_false] at range
  rcases range with rfl | rfl | rfl | rfl
  · obtain ⟨s, -, rfl⟩ := (N.min_inclusive_value r y).mp has; exact real s
  · obtain ⟨s, -, rfl⟩ := (N.max_inclusive_value r y).mp has; exact real s
  · obtain ⟨s, -, rfl⟩ := (N.min_exclusive_value r y).mp has; exact real s
  · obtain ⟨s, -, rfl⟩ := (N.max_exclusive_value r y).mp has; exact real s

private theorem range_facet_spec (f : FacetRestriction) :
    ∃ b, components.range_facet f = .ok b ∧ (b = true → Normal.{w} fun D V => V.facets f ∧
      ∀ y, D.facetValue f.facet (D.lexicalValue f.value.datatype f.value.lexical.val) y → isDatatypeValue D y) := by
  rw [components.range_facet, Rowl.Datatypes.facet_of_correct]
  cases facet : Rowl.Datatypes.facetOf f.facet with
  | none => exact ⟨false, by simp, by simp⟩
  | some F =>
    have range := facetOf_some facet
    obtain ⟨r, run, some', -⟩ := Rowl.Datatypes.literal_value_correct.{w} f.value
    cases r with
    | none => exact ⟨false, by simp [run], by simp⟩
    | some value =>
      refine ⟨decide (Rowl.Datatypes.IsNumber value), by simp [run, Rowl.Datatypes.numeric_correct], ?_⟩
      intro yes _ D N V vocab
      have number := of_decide_eq_true yes
      obtain ⟨-, k, -, -, facts⟩ := some' value rfl
      obtain ⟨supported, lexical, valued⟩ := facts D N
      obtain ⟨q, real⟩ := number_real N value number
      have lexReal : D.lexicalValue f.value.datatype f.value.lexical.val = N.real q := by rw [valued, real]
      refine ⟨(vocab.2.2.2.2.2.2.2.2.2 f).mpr ⟨(vocab.2.2.2.2.2.2.2.2.1 _).mpr ⟨supported, lexical⟩,
        realType, N.real_supported, ?_⟩, fun y has => ?_⟩
      · rw [lexReal, N.real_facets]
        exact ⟨range, q, rfl⟩
      · rw [lexReal] at has
        exact range_values N range q y has

private theorem range_facets_spec (facets : alloc.vec.Vec FacetRestriction) (index : Usize) :
    ∃ b, components.range_facets facets index = .ok b ∧ (b = true → ∀ f ∈ facets.val.drop index.val,
      Normal.{w} fun D V => V.facets f ∧
        ∀ y, D.facetValue f.facet (D.lexicalValue f.value.datatype f.value.lexical.val) y → isDatatypeValue D y) := by
  rw [components.range_facets]
  by_cases more : index.val < facets.val.length
  · have lookup : facets.index_usize index = .ok facets.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    obtain ⟨b1, run1, facts1⟩ := range_facet_spec.{w} facets.val[index.val]
    cases b1 with
    | false => exact ⟨false, by simp [UScalar.lt_equiv, more, lookup, run1], by simp⟩
    | true =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b, run, facts⟩ := range_facets_spec facets next
      refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, run1, advance, run], fun yes f member => ?_⟩
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact facts1 rfl
      · exact facts yes f (by rw [nextIs]; exact later)
  · refine ⟨true, by simp [UScalar.lt_equiv, more], fun _ f member => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)] at member
    cases member
termination_by facets.val.length - index.val
decreasing_by omega

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

/-- A member of a list of at least two is smaller than the list. -/
private theorem elements_size (xs : AtLeastTwo α) {x : α} (h : x ∈ xs.elements) : sizeOf x < sizeOf xs := by
  simp only [AtLeastTwo.elements, List.mem_cons] at h
  cases xs with
  | mk first second rest =>
    rcases h with rfl | rfl | h
    · simp +arith
    · simp +arith
    · have := vec_mem_size rest h
      simp +arith only [AtLeastTwo.mk.sizeOf_spec]
      omega

/-- A member of a list of at least two is smaller than a constructor over the list. -/
private theorem members_bound {α : Type} [SizeOf α] (xs : AtLeastTwo α) (e : α) (h : e ∈ xs.elements) :
    sizeOf e < 1 + sizeOf xs := by
  have := elements_size xs h
  omega

end Sizes

private theorem standard_list_spec (ranges : alloc.vec.Vec DataRange) (index : Usize)
    (each : ∀ r ∈ ranges.val, ∃ b, components.standard_range r = .ok b ∧
      (b = true → Normal.{w} fun D V => Standard D V r)) :
    ∃ b, components.standard_list ranges index = .ok b ∧
      (b = true → ∀ r ∈ ranges.val.drop index.val, Normal.{w} fun D V => Standard D V r) := by
  rw [components.standard_list]
  by_cases more : index.val < ranges.val.length
  · have lookup : ranges.index_usize index = .ok ranges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    obtain ⟨b1, run1, facts1⟩ := each ranges.val[index.val] (List.getElem_mem more)
    cases b1 with
    | false => exact ⟨false, by simp [UScalar.lt_equiv, more, lookup, run1], by simp⟩
    | true =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b, run, facts⟩ := standard_list_spec ranges next each
      refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, run1, advance, run], fun yes r member => ?_⟩
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact facts1 rfl
      · exact facts yes r (by rw [nextIs]; exact later)
  · refine ⟨true, by simp [UScalar.lt_equiv, more], fun _ r member => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)] at member
    cases member
termination_by ranges.val.length - index.val
decreasing_by omega

private theorem standard_members_spec (members : AtLeastTwo DataRange)
    (each : ∀ r ∈ members.elements, ∃ b, components.standard_range r = .ok b ∧
      (b = true → Normal.{w} fun D V => Standard D V r)) :
    ∃ b, components.standard_members members = .ok b ∧
      (b = true → ∀ r ∈ members.elements, Normal.{w} fun D V => Standard D V r) := by
  rw [components.standard_members]
  obtain ⟨b1, run1, facts1⟩ := each members.first (by simp [AtLeastTwo.elements])
  cases b1 with
  | false => exact ⟨false, by simp [run1], by simp⟩
  | true =>
    obtain ⟨b2, run2, facts2⟩ := each members.second (by simp [AtLeastTwo.elements])
    cases b2 with
    | false => exact ⟨false, by simp [run1, run2], by simp⟩
    | true =>
      obtain ⟨b, run, facts⟩ := standard_list_spec members.rest 0#usize
        (fun r member => each r (by simp [AtLeastTwo.elements, member]))
      refine ⟨b, by simp [run1, run2, run], fun yes r member => ?_⟩
      simp only [AtLeastTwo.elements, List.mem_cons] at member
      rcases member with rfl | rfl | rest
      · exact facts1 rfl
      · exact facts2 rfl
      · exact facts yes r (by simpa using rest)

/-- The check of a data range is total, and it accepts only standard ranges. -/
theorem standard_range_spec (r : DataRange) :
    ∃ b, components.standard_range r = .ok b ∧ (b = true → Normal.{w} fun D V => Standard D V r) := by
  cases r with
  | Datatype dt =>
    rw [components.standard_range]
    obtain ⟨b, run, facts⟩ := known_datatype_spec.{w} dt
    refine ⟨b, run, fun yes _ D N V vocab => ?_⟩
    beta_reduce
    rw [Standard]
    exact facts yes D N V vocab
  | Intersection members =>
    rw [components.standard_range]
    obtain ⟨b, run, facts⟩ := standard_members_spec members (fun e member => by
      have := members_bound members e member
      exact standard_range_spec e)
    refine ⟨b, run, fun yes _ D N V vocab => ?_⟩
    beta_reduce
    rw [Standard]
    have each := fun e member => facts yes e member D N V vocab
    exact ⟨each _ (by simp [AtLeastTwo.elements]), each _ (by simp [AtLeastTwo.elements]),
      fun e member => each e (by simp [AtLeastTwo.elements, member])⟩
  | Union members =>
    rw [components.standard_range]
    obtain ⟨b, run, facts⟩ := standard_members_spec members (fun e member => by
      have := members_bound members e member
      exact standard_range_spec e)
    refine ⟨b, run, fun yes _ D N V vocab => ?_⟩
    beta_reduce
    rw [Standard]
    have each := fun e member => facts yes e member D N V vocab
    exact ⟨each _ (by simp [AtLeastTwo.elements]), each _ (by simp [AtLeastTwo.elements]),
      fun e member => each e (by simp [AtLeastTwo.elements, member])⟩
  | Complement inner =>
    rw [components.standard_range]
    obtain ⟨b, run, facts⟩ := standard_range_spec inner
    refine ⟨b, run, fun yes _ D N V vocab => ?_⟩
    beta_reduce
    rw [Standard]
    exact facts yes D N V vocab
  | OneOf literals =>
    rw [components.standard_range]
    obtain ⟨b1, run1, facts1⟩ := known_literal_spec.{w} literals.first
    cases b1 with
    | false => exact ⟨false, by simp [run1], by simp⟩
    | true =>
      obtain ⟨b, run, facts⟩ := known_literals_spec.{w} literals.rest 0#usize
      refine ⟨b, by simp [run1, run], fun yes _ D N V vocab => ?_⟩
      beta_reduce
      rw [Standard]
      intro lt member
      simp only [NonEmpty.elements, List.mem_cons] at member
      rcases member with rfl | rest
      · exact facts1 rfl D N V vocab
      · exact facts yes lt (by simpa using rest) D N V vocab
  | Restriction dt facets =>
    rw [components.standard_range, Rowl.Datatypes.kind_of_correct]
    cases kind : Rowl.Datatypes.kindOf dt with
    | none => exact ⟨false, by simp, by simp⟩
    | some k =>
      obtain ⟨b1, run1, facts1⟩ := range_facet_spec.{w} facets.first
      cases b1 with
      | false => exact ⟨false, by simp [run1], by simp⟩
      | true =>
        obtain ⟨b, run, facts⟩ := range_facets_spec.{w} facets.rest 0#usize
        refine ⟨b, by simp [run1, run], fun yes _ D N V vocab => ?_⟩
        beta_reduce
        rw [Standard]
        refine ⟨by rw [Rowl.Datatypes.kindOf_some kind]; exact Rowl.Datatypes.normative_supported N k, ?_⟩
        intro f member
        simp only [NonEmpty.elements, List.mem_cons] at member
        rcases member with rfl | rest
        · exact facts1 rfl D N V vocab
        · exact facts yes f (by simpa using rest) D N V vocab
termination_by sizeOf r
decreasing_by all_goals (subst_vars; first | omega | (simp_wf <;> omega))

private theorem standard_filler_spec (filler : Option DataRange) :
    ∃ b, components.standard_filler filler = .ok b ∧
      (b = true → ∀ r, filler = some r → Normal.{w} fun D V => Standard D V r) := by
  cases filler with
  | none => exact ⟨true, rfl, by simp⟩
  | some r =>
    obtain ⟨b, run, facts⟩ := standard_range_spec.{w} r
    exact ⟨b, by simp [components.standard_filler, run], fun yes r' same => by cases same; exact facts yes⟩

/-! ## Plain class expressions and axioms -/

/-- What the check of a class expression establishes: with `nominals`, the
    expression is plain for every side that holds of its individuals;
    without, for every side. -/
def ClassOk (nominals : Bool) (c : ClassExpression) : Prop :=
  Normal.{w} fun D V => ∀ side : Individual → Prop, (nominals = true → ∀ i ∈ classIndividuals c, side i) →
    Plain D V side c

private theorem plain_list_spec (classes : alloc.vec.Vec ClassExpression) (index : Usize) (nominals : Bool)
    (each : ∀ c ∈ classes.val, ∃ b, components.plain_class c nominals = .ok b ∧ (b = true → ClassOk.{w} nominals c)) :
    ∃ b, components.plain_list classes index nominals = .ok b ∧
      (b = true → ∀ c ∈ classes.val.drop index.val, ClassOk.{w} nominals c) := by
  rw [components.plain_list]
  by_cases more : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    obtain ⟨b1, run1, facts1⟩ := each classes.val[index.val] (List.getElem_mem more)
    cases b1 with
    | false => exact ⟨false, by simp [UScalar.lt_equiv, more, lookup, run1], by simp⟩
    | true =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b, run, facts⟩ := plain_list_spec classes next nominals each
      refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, run1, advance, run], fun yes c member => ?_⟩
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact facts1 rfl
      · exact facts yes c (by rw [nextIs]; exact later)
  · refine ⟨true, by simp [UScalar.lt_equiv, more], fun _ c member => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)] at member
    cases member
termination_by classes.val.length - index.val
decreasing_by omega

private theorem plain_members_spec (members : AtLeastTwo ClassExpression) (nominals : Bool)
    (each : ∀ c ∈ members.elements, ∃ b, components.plain_class c nominals = .ok b ∧
      (b = true → ClassOk.{w} nominals c)) :
    ∃ b, components.plain_members members nominals = .ok b ∧
      (b = true → ∀ c ∈ members.elements, ClassOk.{w} nominals c) := by
  rw [components.plain_members]
  obtain ⟨b1, run1, facts1⟩ := each members.first (by simp [AtLeastTwo.elements])
  cases b1 with
  | false => exact ⟨false, by simp [run1], by simp⟩
  | true =>
    obtain ⟨b2, run2, facts2⟩ := each members.second (by simp [AtLeastTwo.elements])
    cases b2 with
    | false => exact ⟨false, by simp [run1, run2], by simp⟩
    | true =>
      obtain ⟨b, run, facts⟩ := plain_list_spec members.rest 0#usize nominals
        (fun c member => each c (by simp [AtLeastTwo.elements, member]))
      refine ⟨b, by simp [run1, run2, run], fun yes c member => ?_⟩
      simp only [AtLeastTwo.elements, List.mem_cons] at member
      rcases member with rfl | rfl | rest
      · exact facts1 rfl
      · exact facts2 rfl
      · exact facts yes c (by simpa using rest)

private theorem plain_counted_spec (role : ObjectPropertyExpression) (filler : Option ClassExpression) (nominals : Bool)
    (each : ∀ c, filler = some c → ∃ b, components.plain_class c nominals = .ok b ∧
      (b = true → ClassOk.{w} nominals c)) :
    ∃ b, components.plain_counted role filler nominals = .ok b ∧
      (b = true → NotTop role ∧ ∀ c, filler = some c → ClassOk.{w} nominals c) := by
  unfold components.plain_counted
  by_cases np : NotTop role
  · cases filler with
    | none => exact ⟨true, by simp [plain_role_eq, np], fun _ => ⟨np, by simp⟩⟩
    | some c =>
      obtain ⟨b, run, facts⟩ := each c rfl
      exact ⟨b, by simp [plain_role_eq, np, run], fun yes => ⟨np, fun c' same => by cases same; exact facts yes⟩⟩
  · exact ⟨false, by simp [plain_role_eq, np], by simp⟩

/-- The individuals of a member of an intersection or union are individuals of it. -/
private theorem members_individuals {xs : AtLeastTwo ClassExpression} {e : ClassExpression} (member : e ∈ xs.elements)
    {i : Individual} (inside : i ∈ classIndividuals e) :
    i ∈ classIndividuals (.ObjectIntersectionOf xs) ∧ i ∈ classIndividuals (.ObjectUnionOf xs) :=
  Rowl.DataMeaning.class_individuals_members xs e member i inside

/-- The check of a class expression is total, and it accepts only plain
    expressions; without `nominals`, only expressions without individuals. -/
theorem plain_class_spec (c : ClassExpression) (nominals : Bool) :
    ∃ b, components.plain_class c nominals = .ok b ∧ (b = true → ClassOk.{w} nominals c) := by
  cases c with
  | Class named =>
    refine ⟨true, by simp [components.plain_class], fun _ _ D _ V _ side _ => ?_⟩
    rw [Plain]; trivial
  | ObjectIntersectionOf members =>
    rw [components.plain_class]
    obtain ⟨b, run, facts⟩ := plain_members_spec members nominals (fun e member => by
      have := members_bound members e member
      exact plain_class_spec e nominals)
    refine ⟨b, run, fun yes _ D N V vocab side sides => ?_⟩
    have each : ∀ e ∈ members.elements, Plain D V side e := fun e member =>
      facts yes e member D N V vocab side fun n i inside => sides n i (members_individuals member inside).1
    rw [Plain]
    exact ⟨each _ (by simp [AtLeastTwo.elements]), each _ (by simp [AtLeastTwo.elements]),
      fun e member => each e (by simp [AtLeastTwo.elements, member])⟩
  | ObjectUnionOf members =>
    rw [components.plain_class]
    obtain ⟨b, run, facts⟩ := plain_members_spec members nominals (fun e member => by
      have := members_bound members e member
      exact plain_class_spec e nominals)
    refine ⟨b, run, fun yes _ D N V vocab side sides => ?_⟩
    have each : ∀ e ∈ members.elements, Plain D V side e := fun e member =>
      facts yes e member D N V vocab side fun n i inside => sides n i (members_individuals member inside).2
    rw [Plain]
    exact ⟨each _ (by simp [AtLeastTwo.elements]), each _ (by simp [AtLeastTwo.elements]),
      fun e member => each e (by simp [AtLeastTwo.elements, member])⟩
  | ObjectComplementOf inner =>
    rw [components.plain_class]
    obtain ⟨b, run, facts⟩ := plain_class_spec inner nominals
    refine ⟨b, run, fun yes _ D N V vocab side sides => ?_⟩
    rw [Plain]
    exact facts yes D N V vocab side fun n i inside => sides n i (by rw [classIndividuals]; exact inside)
  | ObjectOneOf individuals =>
    refine ⟨nominals, by simp [components.plain_class], fun yes _ D _ V _ side sides => ?_⟩
    rw [Plain]
    intro a member
    exact sides yes a (by rw [classIndividuals]; exact member)
  | ObjectSomeValuesFrom role filler =>
    rw [components.plain_class]
    by_cases np : NotTop role
    · obtain ⟨b, run, facts⟩ := plain_class_spec filler nominals
      refine ⟨b, by simp [plain_role_eq, np, run], fun yes _ D N V vocab side sides => ?_⟩
      rw [Plain]
      exact ⟨np, facts yes D N V vocab side fun n i inside => sides n i (by rw [classIndividuals]; exact inside)⟩
    · exact ⟨false, by simp [plain_role_eq, np], by simp⟩
  | ObjectAllValuesFrom role filler =>
    rw [components.plain_class]
    by_cases np : NotTop role
    · obtain ⟨b, run, facts⟩ := plain_class_spec filler nominals
      refine ⟨b, by simp [plain_role_eq, np, run], fun yes _ D N V vocab side sides => ?_⟩
      rw [Plain]
      exact ⟨np, facts yes D N V vocab side fun n i inside => sides n i (by rw [classIndividuals]; exact inside)⟩
    · exact ⟨false, by simp [plain_role_eq, np], by simp⟩
  | ObjectHasValue role a =>
    rw [components.plain_class]
    by_cases np : NotTop role
    · refine ⟨nominals, by simp [plain_role_eq, np], fun yes _ D _ V _ side sides => ?_⟩
      rw [Plain]
      exact ⟨np, sides yes a (by rw [classIndividuals]; simp)⟩
    · exact ⟨false, by simp [plain_role_eq, np], by simp⟩
  | ObjectHasSelf role =>
    refine ⟨decide (NotTop role), by simp [components.plain_class, plain_role_eq], fun yes _ D _ V _ side _ => ?_⟩
    rw [Plain]
    exact of_decide_eq_true yes
  | ObjectMinCardinality count role filler =>
    rw [components.plain_class]
    obtain ⟨b, run, facts⟩ := plain_counted_spec role filler nominals (fun e same => by
      have : sizeOf e < sizeOf filler := by rw [same]; simp +arith
      exact plain_class_spec e nominals)
    refine ⟨b, run, fun yes _ D N V vocab side sides => ?_⟩
    obtain ⟨np, fill⟩ := facts yes
    cases filler with
    | none => rw [Plain]; exact np
    | some e =>
      rw [Plain]
      exact ⟨np, fill e rfl D N V vocab side fun n i inside => sides n i (by rw [classIndividuals]; exact inside)⟩
  | ObjectMaxCardinality count role filler =>
    rw [components.plain_class]
    obtain ⟨b, run, facts⟩ := plain_counted_spec role filler nominals (fun e same => by
      have : sizeOf e < sizeOf filler := by rw [same]; simp +arith
      exact plain_class_spec e nominals)
    refine ⟨b, run, fun yes _ D N V vocab side sides => ?_⟩
    obtain ⟨np, fill⟩ := facts yes
    cases filler with
    | none => rw [Plain]; exact np
    | some e =>
      rw [Plain]
      exact ⟨np, fill e rfl D N V vocab side fun n i inside => sides n i (by rw [classIndividuals]; exact inside)⟩
  | ObjectExactCardinality count role filler =>
    rw [components.plain_class]
    obtain ⟨b, run, facts⟩ := plain_counted_spec role filler nominals (fun e same => by
      have : sizeOf e < sizeOf filler := by rw [same]; simp +arith
      exact plain_class_spec e nominals)
    refine ⟨b, run, fun yes _ D N V vocab side sides => ?_⟩
    obtain ⟨np, fill⟩ := facts yes
    cases filler with
    | none => rw [Plain]; exact np
    | some e =>
      rw [Plain]
      exact ⟨np, fill e rfl D N V vocab side fun n i inside => sides n i (by rw [classIndividuals]; exact inside)⟩
  | DataSomeValuesFrom property range =>
    rw [components.plain_class]
    by_cases np : property ≠ topData
    · obtain ⟨b, run, facts⟩ := standard_range_spec.{w} range
      refine ⟨b, by simp [plain_data_eq, np, run], fun yes _ D N V vocab side _ => ?_⟩
      rw [Plain]
      exact ⟨np, facts yes D N V vocab⟩
    · refine ⟨false, ?_, by simp⟩
      simp only [ne_eq, not_not] at np
      simp [plain_data_eq, np]
  | DataAllValuesFrom property range =>
    rw [components.plain_class]
    by_cases np : property ≠ topData
    · obtain ⟨b, run, facts⟩ := standard_range_spec.{w} range
      refine ⟨b, by simp [plain_data_eq, np, run], fun yes _ D N V vocab side _ => ?_⟩
      rw [Plain]
      exact ⟨np, facts yes D N V vocab⟩
    · refine ⟨false, ?_, by simp⟩
      simp only [ne_eq, not_not] at np
      simp [plain_data_eq, np]
  | DataHasValue property literal =>
    rw [components.plain_class]
    by_cases np : property ≠ topData
    · obtain ⟨b, run, facts⟩ := known_literal_spec.{w} literal
      refine ⟨b, by simp [plain_data_eq, np, run], fun yes _ D N V vocab side _ => ?_⟩
      rw [Plain]
      exact ⟨np, facts yes D N V vocab⟩
    · refine ⟨false, ?_, by simp⟩
      simp only [ne_eq, not_not] at np
      simp [plain_data_eq, np]
  | DataMinCardinality count property filler =>
    rw [components.plain_class]
    by_cases np : property ≠ topData
    · obtain ⟨b, run, facts⟩ := standard_filler_spec.{w} filler
      refine ⟨b, by simp [plain_data_eq, np, run], fun yes _ D N V vocab side _ => ?_⟩
      cases filler with
      | none => rw [Plain]; exact np
      | some r => rw [Plain]; exact ⟨np, facts yes r rfl D N V vocab⟩
    · refine ⟨false, ?_, by simp⟩
      simp only [ne_eq, not_not] at np
      simp [plain_data_eq, np]
  | DataMaxCardinality count property filler =>
    rw [components.plain_class]
    by_cases np : property ≠ topData
    · obtain ⟨b, run, facts⟩ := standard_filler_spec.{w} filler
      refine ⟨b, by simp [plain_data_eq, np, run], fun yes _ D N V vocab side _ => ?_⟩
      cases filler with
      | none => rw [Plain]; exact np
      | some r => rw [Plain]; exact ⟨np, facts yes r rfl D N V vocab⟩
    · refine ⟨false, ?_, by simp⟩
      simp only [ne_eq, not_not] at np
      simp [plain_data_eq, np]
  | DataExactCardinality count property filler =>
    rw [components.plain_class]
    by_cases np : property ≠ topData
    · obtain ⟨b, run, facts⟩ := standard_filler_spec.{w} filler
      refine ⟨b, by simp [plain_data_eq, np, run], fun yes _ D N V vocab side _ => ?_⟩
      cases filler with
      | none => rw [Plain]; exact np
      | some r => rw [Plain]; exact ⟨np, facts yes r rfl D N V vocab⟩
    · refine ⟨false, ?_, by simp⟩
      simp only [ne_eq, not_not] at np
      simp [plain_data_eq, np]
termination_by sizeOf c
decreasing_by all_goals (subst_vars; first | omega | (simp_wf <;> omega))

/-- The checks combine as conjunctions. -/
private theorem and_spec {a b : Result Bool} {P Q : Prop} (ha : ∃ x, a = .ok x ∧ (x = true → P))
    (hb : ∃ y, b = .ok y ∧ (y = true → Q)) :
    ∃ z, (do let x ← a; if x then b else ok false) = .ok z ∧ (z = true → P ∧ Q) := by
  obtain ⟨x, rx, fx⟩ := ha
  obtain ⟨y, ry, fy⟩ := hb
  cases x with
  | false => exact ⟨false, by simp [rx], by simp⟩
  | true => exact ⟨y, by simp [rx, ry], fun yes => ⟨fx rfl, fy yes⟩⟩

private theorem closed_of {c : ClassExpression} (ok : ClassOk.{w} false c) : Normal.{w} fun D V => Closed D V c :=
  fun D N V vocab => ok D N V vocab (fun _ => False) (by simp)

private theorem plain_sub_role_spec (sub : SubObjectPropertyExpression) :
    ∃ b, components.plain_sub_role sub = .ok b ∧ (b = true → SubNotTop sub) := by
  cases sub with
  | Single r => exact ⟨decide (NotTop r), by simp [components.plain_sub_role, plain_role_eq],
      fun yes => by simp only [SubNotTop]; exact of_decide_eq_true yes⟩
  | Chain roles =>
    obtain ⟨b, run, facts⟩ := plain_role_members_spec roles
    exact ⟨b, by simp [components.plain_sub_role, run], fun yes => by simp only [SubNotTop]; exact facts yes⟩

private theorem role_spec (r : ObjectPropertyExpression) :
    ∃ b, components.plain_role r = .ok b ∧ (b = true → NotTop r) :=
  ⟨_, plain_role_eq r, of_decide_eq_true⟩

private theorem data_spec (p : DataProperty) :
    ∃ b, components.plain_data p = .ok b ∧ (b = true → p ≠ topData) :=
  ⟨_, plain_data_eq p, of_decide_eq_true⟩

/-- The check of an axiom other than an assertion is total, and it accepts only plain axioms. -/
theorem plain_axiom_spec (ax : Axiom) :
    ∃ b, components.plain_axiom ax = .ok b ∧ (b = true → Normal.{w} fun D V => PlainAxiom D V ax) := by
  cases ax with
  | SubClassOf a b =>
    obtain ⟨z, run, facts⟩ := and_spec (plain_class_spec.{w} a false) (plain_class_spec.{w} b false)
    refine ⟨z, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => ?_⟩
    obtain ⟨ha, hb⟩ := facts yes
    exact ⟨closed_of ha D N V vocab, closed_of hb D N V vocab⟩
  | EquivalentClasses members =>
    obtain ⟨b, run, facts⟩ := plain_members_spec.{w} members false (fun c _ => plain_class_spec.{w} c false)
    exact ⟨b, by simp only [components.plain_axiom]; exact run,
      fun yes _ D N V vocab c member => closed_of (facts yes c member) D N V vocab⟩
  | DisjointClasses members =>
    obtain ⟨b, run, facts⟩ := plain_members_spec.{w} members false (fun c _ => plain_class_spec.{w} c false)
    exact ⟨b, by simp only [components.plain_axiom]; exact run,
      fun yes _ D N V vocab c member => closed_of (facts yes c member) D N V vocab⟩
  | DisjointUnion named members =>
    obtain ⟨b, run, facts⟩ := plain_members_spec.{w} members false (fun c _ => plain_class_spec.{w} c false)
    exact ⟨b, by simp only [components.plain_axiom]; exact run,
      fun yes _ D N V vocab c member => closed_of (facts yes c member) D N V vocab⟩
  | SubObjectPropertyOf sub sup =>
    obtain ⟨z, run, facts⟩ := and_spec (plain_sub_role_spec sub) (role_spec sup)
    exact ⟨z, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | EquivalentObjectProperties roles =>
    obtain ⟨b, run, facts⟩ := plain_role_members_spec roles
    exact ⟨b, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | DisjointObjectProperties roles =>
    obtain ⟨b, run, facts⟩ := plain_role_members_spec roles
    exact ⟨b, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | InverseObjectProperties first second =>
    obtain ⟨z, run, facts⟩ := and_spec (role_spec first) (role_spec second)
    exact ⟨z, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | ObjectPropertyDomain r c =>
    obtain ⟨z, run, facts⟩ := and_spec (role_spec r) (plain_class_spec.{w} c false)
    refine ⟨z, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => ?_⟩
    obtain ⟨hr, hc⟩ := facts yes
    exact ⟨hr, closed_of hc D N V vocab⟩
  | ObjectPropertyRange r c =>
    obtain ⟨z, run, facts⟩ := and_spec (role_spec r) (plain_class_spec.{w} c false)
    refine ⟨z, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => ?_⟩
    obtain ⟨hr, hc⟩ := facts yes
    exact ⟨hr, closed_of hc D N V vocab⟩
  | FunctionalObjectProperty r =>
    obtain ⟨b, run, facts⟩ := role_spec r
    exact ⟨b, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | InverseFunctionalObjectProperty r =>
    obtain ⟨b, run, facts⟩ := role_spec r
    exact ⟨b, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | ReflexiveObjectProperty r =>
    obtain ⟨b, run, facts⟩ := role_spec r
    exact ⟨b, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | IrreflexiveObjectProperty r =>
    obtain ⟨b, run, facts⟩ := role_spec r
    exact ⟨b, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | SymmetricObjectProperty r =>
    obtain ⟨b, run, facts⟩ := role_spec r
    exact ⟨b, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | AsymmetricObjectProperty r =>
    obtain ⟨b, run, facts⟩ := role_spec r
    exact ⟨b, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | TransitiveObjectProperty r =>
    obtain ⟨b, run, facts⟩ := role_spec r
    exact ⟨b, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | SubDataPropertyOf p q =>
    obtain ⟨z, run, facts⟩ := and_spec (data_spec p) (data_spec q)
    exact ⟨z, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | EquivalentDataProperties properties =>
    obtain ⟨b, run, facts⟩ := plain_data_members_spec properties
    exact ⟨b, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | DisjointDataProperties properties =>
    obtain ⟨b, run, facts⟩ := plain_data_members_spec properties
    exact ⟨b, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | DataPropertyDomain p c =>
    obtain ⟨z, run, facts⟩ := and_spec (data_spec p) (plain_class_spec.{w} c false)
    refine ⟨z, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => ?_⟩
    obtain ⟨hp, hc⟩ := facts yes
    exact ⟨hp, closed_of hc D N V vocab⟩
  | DataPropertyRange p r =>
    obtain ⟨z, run, facts⟩ := and_spec (data_spec p) (standard_range_spec.{w} r)
    refine ⟨z, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => ?_⟩
    obtain ⟨hp, hr⟩ := facts yes
    exact ⟨hp, hr D N V vocab⟩
  | FunctionalDataProperty p =>
    obtain ⟨b, run, facts⟩ := data_spec p
    exact ⟨b, by simp only [components.plain_axiom]; exact run, fun yes _ D N V vocab => facts yes⟩
  | HasKey c roles properties =>
    by_cases some : 0 < roles.val.length
    · obtain ⟨z, run, facts⟩ := and_spec (plain_class_spec.{w} c false)
        (and_spec (plain_roles_spec roles 0#usize) (plain_data_list_spec properties 0#usize))
      refine ⟨z, by simp only [components.plain_axiom]; simp [UScalar.lt_equiv, some]; exact run,
        fun yes _ D N V vocab => ?_⟩
      obtain ⟨hc, hr, hp⟩ := facts yes
      exact ⟨closed_of hc D N V vocab, List.ne_nil_of_length_pos some, by simpa using hr, by simpa using hp⟩
    · exact ⟨false, by simp only [components.plain_axiom]; simp [UScalar.lt_equiv, some], by simp⟩
  | Declaration _ | DatatypeDefinition _ _ | SameIndividual _ | DifferentIndividuals _ | ClassAssertion _ _
  | ObjectPropertyAssertion _ _ _ | NegativeObjectPropertyAssertion _ _ _ | DataPropertyAssertion _ _ _
  | NegativeDataPropertyAssertion _ _ _ | AnnotationAssertion _ _ _ | SubAnnotationPropertyOf _ _
  | AnnotationPropertyDomain _ _ | AnnotationPropertyRange _ _ =>
    exact ⟨false, by simp [components.plain_axiom], by simp⟩

/-- The check of an assertion is total, and it accepts only plain assertions. -/
theorem plain_assertion_spec (ax : Axiom) :
    ∃ b, components.plain_assertion ax = .ok b ∧ (b = true → Normal.{w} fun D V => PlainAssertion D V ax) := by
  cases ax with
  | ClassAssertion c a =>
    obtain ⟨b, run, facts⟩ := plain_class_spec.{w} c true
    exact ⟨b, by simp only [components.plain_assertion]; exact run,
      fun yes _ D N V vocab => facts yes D N V vocab (fun i => i ∈ classIndividuals c) (fun _ i m => m)⟩
  | DataPropertyAssertion p a lt =>
    obtain ⟨b, run, facts⟩ := known_literal_spec.{w} lt
    exact ⟨b, by simp only [components.plain_assertion]; exact run, fun yes _ D N V vocab => facts yes D N V vocab⟩
  | NegativeDataPropertyAssertion p a lt =>
    obtain ⟨b, run, facts⟩ := known_literal_spec.{w} lt
    exact ⟨b, by simp only [components.plain_assertion]; exact run, fun yes _ D N V vocab => facts yes D N V vocab⟩
  | _ => exact ⟨true, by simp [components.plain_assertion], fun _ _ D _ V _ => by simp [PlainAssertion]⟩

private theorem meaningless_plain {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary) {ax : Axiom}
    (meaningless : Meaningless ax) : PlainAxiom D V ax := by
  cases ax <;> simp only [Meaningless] at meaningless <;> simp [PlainAxiom]

/-- What the check of a whole closure establishes about each axiom. -/
def ItemOk (x : AnnotatedAxiom) : Prop :=
  Normal.{w} fun D V => (IsAssertion x.axiom → PlainAssertion D V x.axiom) ∧
    (¬ IsAssertion x.axiom → PlainAxiom D V x.axiom)

/-- What the check of one axiom of a closure establishes, given that the rest checks. -/
private theorem item_step (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) (more : index.val < items.val.length)
    (rest : ∀ x ∈ items.val.drop (index.val + 1), ItemOk.{w} x) (here : ItemOk.{w} items.val[index.val]) :
    ∀ x ∈ items.val.drop index.val, ItemOk.{w} x := by
  intro x member
  rw [List.drop_eq_getElem_cons more] at member
  rcases List.mem_cons.mp member with rfl | later
  · exact here
  · exact rest x later

theorem plain_items_spec (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    ∃ b, components.plain_items items index = .ok b ∧ (b = true → ∀ x ∈ items.val.drop index.val, ItemOk.{w} x) := by
  rw [components.plain_items]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨b, run, facts⟩ := plain_items_spec items next
    rw [nextIs] at facts
    by_cases assertion : IsAssertion items.val[index.val].axiom
    · obtain ⟨b1, run1, facts1⟩ := plain_assertion_spec.{w} items.val[index.val].axiom
      cases b1 with
      | false => exact ⟨false, by simp [UScalar.lt_equiv, more, lookup, assertion_eq, assertion, run1], by simp⟩
      | true =>
        refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, assertion_eq, assertion, run1, advance, run],
          fun yes => item_step items index more (facts yes) ?_⟩
        intro _ D N V vocab
        exact ⟨fun _ => facts1 rfl D N V vocab, fun no => absurd assertion no⟩
    · by_cases meaningless : Meaningless items.val[index.val].axiom
      · refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, assertion_eq, assertion, meaningless_eq, meaningless,
          advance, run], fun yes => item_step items index more (facts yes) ?_⟩
        intro _ D N V vocab
        exact ⟨fun yes' => absurd yes' assertion, fun _ => meaningless_plain D V meaningless⟩
      · obtain ⟨b1, run1, facts1⟩ := plain_axiom_spec.{w} items.val[index.val].axiom
        cases b1 with
        | false => exact ⟨false, by simp [UScalar.lt_equiv, more, lookup, assertion_eq, assertion, meaningless_eq,
            meaningless, run1], by simp⟩
        | true =>
          refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, assertion_eq, assertion, meaningless_eq, meaningless,
            run1, advance, run], fun yes => item_step items index more (facts yes) ?_⟩
          intro _ D N V vocab
          exact ⟨fun yes' => absurd yes' assertion, fun _ => facts1 rfl D N V vocab⟩
  · refine ⟨true, by simp [UScalar.lt_equiv, more], fun _ x member => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)] at member
    cases member
termination_by items.val.length - index.val
decreasing_by omega

/-- The check of an instance question's class expression is total, and it
    accepts only plain expressions without individuals. -/
theorem plain_question_spec (e : ClassExpression) :
    ∃ b, components.plain_question e = .ok b ∧ (b = true → Normal.{w} fun D V => Closed D V e) := by
  obtain ⟨b, run, facts⟩ := plain_class_spec.{w} e false
  exact ⟨b, by simp only [components.plain_question]; exact run, fun yes => closed_of (facts yes)⟩

/-! ## Members -/

private theorem position_member (members : alloc.vec.Vec Individual) (a : Individual) :
    ∃ p, alc_ontology.position members a 0#usize = .ok p ∧ (p.val ≠ 0 ↔ a ∈ members.val) := by
  obtain ⟨p, run, value⟩ := Rowl.AlcOntology.position_of members a
  refine ⟨p, run, ?_⟩
  rw [value]
  constructor
  · intro nonzero
    by_contra absent
    exact nonzero (by simpa [Rowl.AlcOntology.PositionOf] using
      Rowl.AlcOntology.positionFrom_absent members.val a 0 absent)
  · intro present
    obtain ⟨_, positive, _⟩ := Rowl.AlcOntology.positionOf_present members.val a present
    omega

theorem any_member_spec (members named : alloc.vec.Vec Individual) (index : Usize) :
    ∃ b, components.any_member members named index = .ok b ∧
      (b = true ↔ ∃ x ∈ named.val.drop index.val, x ∈ members.val) := by
  rw [components.any_member]
  by_cases more : index.val < named.val.length
  · have lookup : named.index_usize index = .ok named.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    obtain ⟨p, run, member⟩ := position_member members named.val[index.val]
    by_cases found : named.val[index.val] ∈ members.val
    · have nonzero : p ≠ 0#usize := fun same => (member.mpr found) (by rw [same]; rfl)
      refine ⟨true, by simp [UScalar.lt_equiv, more, lookup, run, nonzero, member.mpr found], ?_⟩
      simp only [true_iff]
      exact ⟨_, by rw [split]; exact List.mem_cons_self .., found⟩
    · have zero : p = 0#usize := UScalar.eq_of_val_eq (by simpa using mt member.mp found)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b, rest, facts⟩ := any_member_spec members named next
      refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, run, zero, advance, rest], ?_⟩
      rw [facts, split, nextIs]
      constructor
      · rintro ⟨x, mx, inside⟩
        exact ⟨x, List.mem_cons_of_mem _ mx, inside⟩
      · rintro ⟨x, mx, inside⟩
        rcases List.mem_cons.mp mx with rfl | later
        · exact absurd inside found
        · exact ⟨x, later, inside⟩
  · refine ⟨false, by simp [UScalar.lt_equiv, more], ?_⟩
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro x mx
    rw [List.drop_eq_nil_of_le (by omega)] at mx
    cases mx
termination_by named.val.length - index.val
decreasing_by omega

theorem all_members_spec (members named : alloc.vec.Vec Individual) (index : Usize) :
    ∃ b, components.all_members members named index = .ok b ∧
      (b = true ↔ ∀ x ∈ named.val.drop index.val, x ∈ members.val) := by
  rw [components.all_members]
  by_cases more : index.val < named.val.length
  · have lookup : named.index_usize index = .ok named.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    obtain ⟨p, run, member⟩ := position_member members named.val[index.val]
    by_cases found : named.val[index.val] ∈ members.val
    · have nonzero : p ≠ 0#usize := fun same => (member.mpr found) (by rw [same]; rfl)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b, rest, facts⟩ := all_members_spec members named next
      refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, run, nonzero, member.mpr found, advance, rest], ?_⟩
      rw [facts, split, nextIs]
      constructor
      · intro all x mx
        rcases List.mem_cons.mp mx with rfl | later
        · exact found
        · exact all x later
      · intro all x mx
        exact all x (List.mem_cons_of_mem _ mx)
    · have zero : p = 0#usize := UScalar.eq_of_val_eq (by simpa using mt member.mp found)
      refine ⟨false, by simp [UScalar.lt_equiv, more, lookup, run, zero], ?_⟩
      simp only [Bool.false_eq_true, false_iff, not_forall]
      exact ⟨_, by rw [split]; exact List.mem_cons_self .., found⟩
  · refine ⟨true, by simp [UScalar.lt_equiv, more], ?_⟩
    simp only [true_iff]
    intro x mx
    rw [List.drop_eq_nil_of_le (by omega)] at mx
    cases mx
termination_by named.val.length - index.val
decreasing_by omega

/-- The individuals the kernel lists for an axiom are exactly its individuals. -/
private theorem listed_individuals (ax : Axiom) :
    ∃ r, data_ontology.axiom_individuals (alloc.vec.Vec.new Individual) ax = .ok r ∧
      ∀ named, r = some named → ∀ i, i ∈ named.val ↔ i ∈ axiomIndividuals ax := by
  obtain ⟨r, run, facts⟩ := Rowl.KeyEncoding.axiom_individuals_grows (alloc.vec.Vec.new Individual) ax
    (by simp)
  refine ⟨r, run, fun named same i => ?_⟩
  obtain ⟨sub, _, add, _⟩ := facts named same
  constructor
  · intro member
    rcases sub i member with old | new
    · simp at old
    · exact new
  · exact add i

/-! ## The table of individuals -/

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- The entry of the table for an axiom: the individuals of an assertion, and
    none for any other axiom. -/
def Entry (x : AnnotatedAxiom) (named : alloc.vec.Vec Individual) : Prop :=
  (IsAssertion x.axiom → ∀ i, i ∈ named.val ↔ i ∈ axiomIndividuals x.axiom) ∧
    (¬ IsAssertion x.axiom → named.val = [])

/-- The table of a closure: an entry for each of its axioms. -/
def TableOf (items : List AnnotatedAxiom) (table : List (alloc.vec.Vec Individual)) : Prop :=
  table.length = items.length ∧ ∀ (j : Nat) x named, items[j]? = some x → table[j]? = some named → Entry x named

/-- Whether an entry names a member. -/
def Names (named : alloc.vec.Vec Individual) (members : List Individual) : Prop :=
  ∃ i ∈ named.val, i ∈ members

/-- What pushing the entry of the axiom at `index` keeps of the table facts. -/
private theorem table_push {items : List AnnotatedAxiom} {index : Nat}
    {out pushed table : List (alloc.vec.Vec Individual)} {named : alloc.vec.Vec Individual}
    (more : index < items.length) (filled : out.length = index) (contents : pushed = out ++ [named])
    (entry : Entry items[index] named)
    (facts : table.length = items.length ∧ (∀ j : Nat, j < index + 1 → table[j]? = pushed[j]?) ∧
      ∀ (j : Nat) x named, index + 1 ≤ j → items[j]? = some x → table[j]? = some named → Entry x named) :
    table.length = items.length ∧ (∀ j : Nat, j < index → table[j]? = out[j]?) ∧
      ∀ (j : Nat) x named, index ≤ j → items[j]? = some x → table[j]? = some named → Entry x named := by
  obtain ⟨length, early, late⟩ := facts
  refine ⟨length, fun j lj => ?_, fun j x named' lj mx mn => ?_⟩
  · rw [early j (by omega), contents, List.getElem?_append_left (by omega)]
  · rcases Nat.lt_or_ge j (index + 1) with small | large
    · have jIs : j = index := by omega
      rw [jIs] at mx mn
      rw [early index (by omega), contents, List.getElem?_append_right (by omega), filled] at mn
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at mn
      rw [List.getElem?_eq_getElem more] at mx
      simp only [Option.some.injEq] at mx
      rw [← mx, ← mn]
      exact entry
    · exact late j x named' large mx mn

theorem individual_table_spec (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize)
    (out : alloc.vec.Vec (alloc.vec.Vec Individual)) (filled : out.val.length = index.val)
    (bound : index.val ≤ items.val.length) :
    ∃ r, components.individual_table items index out = .ok r ∧ ∀ table, r = some table →
      table.val.length = items.val.length ∧ (∀ j : Nat, j < index.val → table.val[j]? = out.val[j]?) ∧
      ∀ (j : Nat) x named, index.val ≤ j → items.val[j]? = some x → table.val[j]? = some named → Entry x named := by
  rw [components.individual_table]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    by_cases assertion : IsAssertion items.val[index.val].axiom
    · obtain ⟨r1, run1, listed⟩ := listed_individuals items.val[index.val].axiom
      cases r1 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, more, lookup, assertion_eq, assertion, run1], by simp⟩
      | some named =>
        by_cases room : out.val.length < Usize.max
        · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out named room)
          obtain ⟨r, run, facts⟩ := individual_table_spec items next pushed
            (by rw [contents, nextIs]; simp [filled]) (by omega)
          refine ⟨r, by simp [UScalar.lt_equiv, more, lookup, assertion_eq, assertion, run1, alloc.vec.Vec.len_val,
            usize_max_val, room, push, advance, run], fun table same => ?_⟩
          have facts' := facts table same
          rw [nextIs] at facts'
          exact table_push more filled contents ⟨fun _ => listed named rfl, fun no => absurd assertion no⟩ facts'
        · exact ⟨none, by simp [UScalar.lt_equiv, more, lookup, assertion_eq, assertion, run1, alloc.vec.Vec.len_val,
            usize_max_val, room], by simp⟩
    · by_cases room : out.val.length < Usize.max
      · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec out (alloc.vec.Vec.new Individual) room)
        obtain ⟨r, run, facts⟩ := individual_table_spec items next pushed
          (by rw [contents, nextIs]; simp [filled]) (by omega)
        refine ⟨r, by simp [UScalar.lt_equiv, more, lookup, assertion_eq, assertion, alloc.vec.Vec.len_val,
          usize_max_val, room, push, advance, run], fun table same => ?_⟩
        have facts' := facts table same
        rw [nextIs] at facts'
        exact table_push more filled contents ⟨fun yes => absurd yes assertion, fun _ => rfl⟩ facts'
      · exact ⟨none, by simp [UScalar.lt_equiv, more, lookup, assertion_eq, assertion, alloc.vec.Vec.len_val,
          usize_max_val, room], by simp⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, more], fun table same => ?_⟩
    cases same
    refine ⟨by omega, fun j _ => rfl, fun j x named lj mx _ => ?_⟩
    rw [List.getElem?_eq_none (by omega)] at mx
    cases mx
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- The table that `individual_table` builds from an empty one. -/
private theorem table_of {items : alloc.vec.Vec AnnotatedAxiom} {table : alloc.vec.Vec (alloc.vec.Vec Individual)}
    (facts : table.val.length = items.val.length ∧
      (∀ j : Nat, j < (0#usize).val → table.val[j]? = (alloc.vec.Vec.new (alloc.vec.Vec Individual)).val[j]?) ∧
      ∀ (j : Nat) x named, (0#usize).val ≤ j → items.val[j]? = some x → table.val[j]? = some named → Entry x named) :
    TableOf items.val table.val :=
  ⟨facts.1, fun j x named mx mn => facts.2.2 j x named (by simp) mx mn⟩

/-- The entry of an axiom of a closure in its table. -/
private theorem entry_of_get {items : List AnnotatedAxiom} {table : List (alloc.vec.Vec Individual)}
    (tableOk : TableOf items table) {j : Nat} {x : AnnotatedAxiom} (hx : items[j]? = some x) :
    ∃ named, table[j]? = some named ∧ Entry x named := by
  obtain ⟨lj, -⟩ := List.getElem?_eq_some_iff.mp hx
  have lj' : j < table.length := by rw [tableOk.1]; exact lj
  exact ⟨table[j], List.getElem?_eq_getElem lj', tableOk.2 j x table[j] hx (List.getElem?_eq_getElem lj')⟩

theorem names_member_spec (table : alloc.vec.Vec (alloc.vec.Vec Individual)) (index : Usize)
    (members : alloc.vec.Vec Individual) :
    ∃ b, components.names_member table index members = .ok b ∧
      (b = true ↔ ∃ named, table.val[index.val]? = some named ∧ Names named members.val) := by
  rw [components.names_member]
  by_cases more : index.val < table.val.length
  · have lookup : table.index_usize index = .ok table.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨b, run, any⟩ := any_member_spec members table.val[index.val] 0#usize
    simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at any
    refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, run], ?_⟩
    rw [any, List.getElem?_eq_getElem more]
    constructor
    · intro found
      exact ⟨_, rfl, found⟩
    · rintro ⟨named, same, found⟩
      simp only [Option.some.injEq] at same
      rw [same]
      exact found
  · refine ⟨false, by simp [UScalar.lt_equiv, more], ?_⟩
    rw [List.getElem?_eq_none (by omega)]
    simp

/-! ## Finding the component -/

private theorem add_all_total (members named : alloc.vec.Vec Individual) (index : Usize) :
    ∃ r, components.add_all members named index = .ok r := by
  rw [components.add_all]
  by_cases more : index.val < named.val.length
  · have lookup : named.index_usize index = .ok named.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨r1, run1, -⟩ := Rowl.DataOntology.intern_spec members named.val[index.val]
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, more, lookup, run1]⟩
    | some members1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run⟩ := add_all_total members1 named next
      exact ⟨r, by simp [UScalar.lt_equiv, more, lookup, run1, advance, run]⟩
  · exact ⟨some members, by simp [UScalar.lt_equiv, more]⟩
termination_by named.val.length - index.val
decreasing_by omega

private theorem grow_total (table : alloc.vec.Vec (alloc.vec.Vec Individual)) (index : Usize)
    (members : alloc.vec.Vec Individual) :
    ∃ r, components.grow table index members = .ok r := by
  rw [components.grow]
  by_cases more : index.val < table.val.length
  · have lookup : table.index_usize index = .ok table.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨b, runB, -⟩ := any_member_spec members table.val[index.val] 0#usize
    cases b with
    | false =>
      obtain ⟨r, run⟩ := grow_total table next members
      exact ⟨r, by simp [UScalar.lt_equiv, more, lookup, runB, advance, run]⟩
    | true =>
      obtain ⟨r2, run2⟩ := add_all_total members table.val[index.val] 0#usize
      cases r2 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, more, lookup, runB, run2]⟩
      | some members1 =>
        obtain ⟨r, run⟩ := grow_total table next members1
        exact ⟨r, by simp [UScalar.lt_equiv, more, lookup, runB, run2, advance, run]⟩
  · exact ⟨some members, by simp [UScalar.lt_equiv, more]⟩
termination_by table.val.length - index.val
decreasing_by all_goals omega

theorem component_total (table : alloc.vec.Vec (alloc.vec.Vec Individual)) (members : alloc.vec.Vec Individual)
    (rounds : Usize) :
    ∃ r, components.component table members rounds = .ok r := by
  rw [components.component]
  obtain ⟨r1, run1⟩ := grow_total table 0#usize members
  cases r1 with
  | none => exact ⟨none, by simp [run1]⟩
  | some members1 =>
    by_cases same : members1.val.length = members.val.length
    · exact ⟨some members1, by simp [run1, alloc.vec.Vec.len_val, same]⟩
    · by_cases zero : rounds = 0#usize
      · exact ⟨none, by simp [run1, alloc.vec.Vec.len_val, same, zero]⟩
      · by_cases large : components.MEMBERS.val < members1.val.length
        · exact ⟨none, by simp [run1, alloc.vec.Vec.len_val, same, zero, UScalar.lt_equiv, large]⟩
        · have positive : 0 < rounds.val := by
            rcases Nat.eq_zero_or_pos rounds.val with h | h
            · exact absurd (UScalar.eq_of_val_eq (by simpa using h)) zero
            · exact h
          obtain ⟨fewer, sub, fewerValue⟩ := WP.spec_imp_exists
            (Usize.sub_spec (x := rounds) (y := 1#usize) (by simp; omega))
          have fewerIs : fewer.val = rounds.val - 1 := by simp at fewerValue; omega
          obtain ⟨r, run⟩ := component_total table members1 fewer
          exact ⟨r, by simp [run1, alloc.vec.Vec.len_val, same, zero, UScalar.lt_equiv, large, sub, run]⟩
termination_by rounds.val
decreasing_by omega

/-- Every entry that names a member names only members. -/
def ClosedUnder (table : List (alloc.vec.Vec Individual)) (members : List Individual) : Prop :=
  ∀ named ∈ table, Names named members → ∀ i ∈ named.val, i ∈ members

theorem closed_spec (table : alloc.vec.Vec (alloc.vec.Vec Individual)) (index : Usize)
    (members : alloc.vec.Vec Individual) :
    ∃ b, components.closed table index members = .ok b ∧
      (b = true → ClosedUnder (table.val.drop index.val) members.val) := by
  rw [components.closed]
  by_cases more : index.val < table.val.length
  · have lookup : table.index_usize index = .ok table.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨b, run, facts⟩ := closed_spec table next members
    rw [nextIs] at facts
    obtain ⟨b1, run1, any⟩ := any_member_spec members table.val[index.val] 0#usize
    simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at any
    cases b1 with
    | false =>
      refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, run1, advance, run], fun yes named member => ?_⟩
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | later
      · rintro ⟨i, mi, inside⟩
        exact absurd (any.mpr ⟨i, mi, inside⟩) (by simp)
      · exact facts yes named later
    | true =>
      obtain ⟨b2, run2, all⟩ := all_members_spec members table.val[index.val] 0#usize
      simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at all
      cases b2 with
      | false => exact ⟨false, by simp [UScalar.lt_equiv, more, lookup, run1, run2], by simp⟩
      | true =>
        refine ⟨b, by simp [UScalar.lt_equiv, more, lookup, run1, run2, advance, run], fun yes named member => ?_⟩
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · intro _ i mi
          exact all.mp rfl i mi
        · exact facts yes named later
  · refine ⟨true, by simp [UScalar.lt_equiv, more], fun _ named member => ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)] at member
    cases member
termination_by table.val.length - index.val
decreasing_by omega

/-- `members_of` returns a component that holds the start and is closed. -/
theorem members_of_spec (table : alloc.vec.Vec (alloc.vec.Vec Individual)) (start : Individual) :
    ∃ r, components.members_of table start = .ok r ∧ ∀ members, r = some members →
      start ∈ members.val ∧ ClosedUnder table.val members.val := by
  rw [components.members_of]
  obtain ⟨first, pushFirst, -⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec (alloc.vec.Vec.new Individual)
    start (by simp; scalar_tac))
  obtain ⟨r1, run1⟩ := component_total table first components.ROUNDS
  cases r1 with
  | none => exact ⟨none, by simp [Rowl.Concepts.copy_individual_identity, pushFirst, run1], by simp⟩
  | some members =>
    obtain ⟨p, runP, memberP⟩ := position_member members start
    by_cases inMembers : start ∈ members.val
    · have nonzero : p ≠ 0#usize := fun same => (memberP.mpr inMembers) (by rw [same]; rfl)
      have nonzeroVal := memberP.mpr inMembers
      obtain ⟨b, run2, closedFacts⟩ := closed_spec table 0#usize members
      simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at closedFacts
      cases b with
      | false => exact ⟨none, by simp [Rowl.Concepts.copy_individual_identity, pushFirst, run1, runP, nonzero,
          nonzeroVal, run2], by simp⟩
      | true => exact ⟨some members, by simp [Rowl.Concepts.copy_individual_identity, pushFirst, run1, runP,
          nonzero, nonzeroVal, run2], fun m same => by cases same; exact ⟨inMembers, closedFacts rfl⟩⟩
    · have zero : p = 0#usize := UScalar.eq_of_val_eq (by simpa using mt memberP.mp inMembers)
      exact ⟨none, by simp [Rowl.Concepts.copy_individual_identity, pushFirst, run1, runP, zero], by simp⟩

/-- A closed table closes the assertions of the closure. -/
private theorem closed_items {items : List AnnotatedAxiom} {table : List (alloc.vec.Vec Individual)}
    {members : List Individual} (tableOk : TableOf items table) (closed : ClosedUnder table members) :
    ∀ x ∈ items, IsAssertion x.axiom → (∃ i ∈ axiomIndividuals x.axiom, i ∈ members) →
      ∀ i ∈ axiomIndividuals x.axiom, i ∈ members := by
  intro x mx assertion ⟨i, mi, inside⟩ k mk
  obtain ⟨j, hj, same⟩ := List.getElem_of_mem mx
  have hx : items[j]? = some x := by rw [List.getElem?_eq_getElem hj, same]
  obtain ⟨named, atJ, entry⟩ := entry_of_get tableOk hx
  have names := entry.1 assertion
  exact closed named (List.mem_of_getElem? atJ) ⟨i, (names i).mpr mi, inside⟩ k ((names k).mpr mk)

/-! ## Copies -/

private theorem copy_natural_eq (n : probes.Natural) : components.copy_natural n = .ok n := by
  induction n with
  | Zero => rw [components.copy_natural]
  | Succ inner ih => rw [components.copy_natural]; simp [ih]

private theorem copy_class_name_eq (c : Class) : components.copy_class_name c = .ok c := by
  cases c; simp [components.copy_class_name, Rowl.Nnf.copy_iri_identity]

private theorem copy_datatype_eq (dt : Datatype) : components.copy_datatype dt = .ok dt := by
  cases dt; simp [components.copy_datatype, Rowl.Nnf.copy_iri_identity]

private theorem copy_data_property_eq (p : DataProperty) : components.copy_data_property p = .ok p := by
  cases p; simp [components.copy_data_property, Rowl.Nnf.copy_iri_identity]

private theorem copy_literal_eq (lt : Literal) : components.copy_literal lt = .ok lt := by
  cases lt; simp [components.copy_literal, Rowl.Nnf.copy_bytes_identity, copy_datatype_eq]

private theorem copy_facet_eq (f : FacetRestriction) : components.copy_facet f = .ok f := by
  cases f; simp [components.copy_facet, Rowl.Nnf.copy_iri_identity, copy_literal_eq]

private theorem copy_literals_spec (literals : alloc.vec.Vec Literal) (index : Usize) (out : alloc.vec.Vec Literal)
    (room : out.val.length + (literals.val.length - index.val) ≤ Usize.max) :
    ∃ v, components.copy_literals literals index out = .ok v ∧ v.val = out.val ++ literals.val.drop index.val := by
  rw [components.copy_literals]
  by_cases more : index.val < literals.val.length
  · have lookup : literals.index_usize index = .ok literals.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have fits : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out literals.val[index.val] fits)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := copy_literals_spec literals next pushed (by rw [contents, nextIs]; simp; omega)
    refine ⟨v, by simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits, lookup, copy_literal_eq, push,
      advance, run], ?_⟩
    rw [value, contents, nextIs, List.drop_eq_getElem_cons more]
    simp
  · exact ⟨out, by simp [UScalar.lt_equiv, more], by simp [List.drop_eq_nil_of_le (Nat.le_of_not_lt more)]⟩
termination_by literals.val.length - index.val
decreasing_by omega

private theorem copy_literals_eq (literals : alloc.vec.Vec Literal) : components.copy_literals literals 0#usize (alloc.vec.Vec.new Literal) = .ok literals := by
  obtain ⟨v, run, value⟩ := copy_literals_spec literals 0#usize (alloc.vec.Vec.new Literal) (by simp)
  have same : v = _ := (alloc.vec.Vec.eq_iff _ _).mpr (by simpa using value)
  rw [run, same]

private theorem copy_facets_spec (facets : alloc.vec.Vec FacetRestriction) (index : Usize) (out : alloc.vec.Vec FacetRestriction)
    (room : out.val.length + (facets.val.length - index.val) ≤ Usize.max) :
    ∃ v, components.copy_facets facets index out = .ok v ∧ v.val = out.val ++ facets.val.drop index.val := by
  rw [components.copy_facets]
  by_cases more : index.val < facets.val.length
  · have lookup : facets.index_usize index = .ok facets.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have fits : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out facets.val[index.val] fits)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := copy_facets_spec facets next pushed (by rw [contents, nextIs]; simp; omega)
    refine ⟨v, by simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits, lookup, copy_facet_eq, push,
      advance, run], ?_⟩
    rw [value, contents, nextIs, List.drop_eq_getElem_cons more]
    simp
  · exact ⟨out, by simp [UScalar.lt_equiv, more], by simp [List.drop_eq_nil_of_le (Nat.le_of_not_lt more)]⟩
termination_by facets.val.length - index.val
decreasing_by omega

private theorem copy_facets_eq (facets : alloc.vec.Vec FacetRestriction) : components.copy_facets facets 0#usize (alloc.vec.Vec.new FacetRestriction) = .ok facets := by
  obtain ⟨v, run, value⟩ := copy_facets_spec facets 0#usize (alloc.vec.Vec.new FacetRestriction) (by simp)
  have same : v = _ := (alloc.vec.Vec.eq_iff _ _).mpr (by simpa using value)
  rw [run, same]

private theorem copy_individuals_spec (individuals : alloc.vec.Vec Individual) (index : Usize) (out : alloc.vec.Vec Individual)
    (room : out.val.length + (individuals.val.length - index.val) ≤ Usize.max) :
    ∃ v, components.copy_individuals individuals index out = .ok v ∧ v.val = out.val ++ individuals.val.drop index.val := by
  rw [components.copy_individuals]
  by_cases more : index.val < individuals.val.length
  · have lookup : individuals.index_usize index = .ok individuals.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have fits : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out individuals.val[index.val] fits)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := copy_individuals_spec individuals next pushed (by rw [contents, nextIs]; simp; omega)
    refine ⟨v, by simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits, lookup, Rowl.Concepts.copy_individual_identity, push,
      advance, run], ?_⟩
    rw [value, contents, nextIs, List.drop_eq_getElem_cons more]
    simp
  · exact ⟨out, by simp [UScalar.lt_equiv, more], by simp [List.drop_eq_nil_of_le (Nat.le_of_not_lt more)]⟩
termination_by individuals.val.length - index.val
decreasing_by omega

private theorem copy_individuals_eq (individuals : alloc.vec.Vec Individual) : components.copy_individuals individuals 0#usize (alloc.vec.Vec.new Individual) = .ok individuals := by
  obtain ⟨v, run, value⟩ := copy_individuals_spec individuals 0#usize (alloc.vec.Vec.new Individual) (by simp)
  have same : v = _ := (alloc.vec.Vec.eq_iff _ _).mpr (by simpa using value)
  rw [run, same]

private theorem copy_roles_spec (roles : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) (out : alloc.vec.Vec ObjectPropertyExpression)
    (room : out.val.length + (roles.val.length - index.val) ≤ Usize.max) :
    ∃ v, components.copy_roles roles index out = .ok v ∧ v.val = out.val ++ roles.val.drop index.val := by
  rw [components.copy_roles]
  by_cases more : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have fits : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out roles.val[index.val] fits)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := copy_roles_spec roles next pushed (by rw [contents, nextIs]; simp; omega)
    refine ⟨v, by simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits, lookup, Rowl.Concepts.copy_role_identity, push,
      advance, run], ?_⟩
    rw [value, contents, nextIs, List.drop_eq_getElem_cons more]
    simp
  · exact ⟨out, by simp [UScalar.lt_equiv, more], by simp [List.drop_eq_nil_of_le (Nat.le_of_not_lt more)]⟩
termination_by roles.val.length - index.val
decreasing_by omega

private theorem copy_roles_eq (roles : alloc.vec.Vec ObjectPropertyExpression) : components.copy_roles roles 0#usize (alloc.vec.Vec.new ObjectPropertyExpression) = .ok roles := by
  obtain ⟨v, run, value⟩ := copy_roles_spec roles 0#usize (alloc.vec.Vec.new ObjectPropertyExpression) (by simp)
  have same : v = _ := (alloc.vec.Vec.eq_iff _ _).mpr (by simpa using value)
  rw [run, same]

private theorem copy_data_list_spec (properties : alloc.vec.Vec DataProperty) (index : Usize) (out : alloc.vec.Vec DataProperty)
    (room : out.val.length + (properties.val.length - index.val) ≤ Usize.max) :
    ∃ v, components.copy_data_list properties index out = .ok v ∧ v.val = out.val ++ properties.val.drop index.val := by
  rw [components.copy_data_list]
  by_cases more : index.val < properties.val.length
  · have lookup : properties.index_usize index = .ok properties.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have fits : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out properties.val[index.val] fits)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := copy_data_list_spec properties next pushed (by rw [contents, nextIs]; simp; omega)
    refine ⟨v, by simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits, lookup, copy_data_property_eq, push,
      advance, run], ?_⟩
    rw [value, contents, nextIs, List.drop_eq_getElem_cons more]
    simp
  · exact ⟨out, by simp [UScalar.lt_equiv, more], by simp [List.drop_eq_nil_of_le (Nat.le_of_not_lt more)]⟩
termination_by properties.val.length - index.val
decreasing_by omega

private theorem copy_data_list_eq (properties : alloc.vec.Vec DataProperty) : components.copy_data_list properties 0#usize (alloc.vec.Vec.new DataProperty) = .ok properties := by
  obtain ⟨v, run, value⟩ := copy_data_list_spec properties 0#usize (alloc.vec.Vec.new DataProperty) (by simp)
  have same : v = _ := (alloc.vec.Vec.eq_iff _ _).mpr (by simpa using value)
  rw [run, same]

private theorem copy_role_members_eq (roles : AtLeastTwo ObjectPropertyExpression) :
    components.copy_role_members roles = .ok roles := by
  cases roles; simp [components.copy_role_members, Rowl.Concepts.copy_role_identity, copy_roles_eq]

private theorem copy_data_members_eq (properties : AtLeastTwo DataProperty) :
    components.copy_data_members properties = .ok properties := by
  cases properties; simp [components.copy_data_members, copy_data_property_eq, copy_data_list_eq]

private theorem copy_individual_members_eq (individuals : AtLeastTwo Individual) :
    components.copy_individual_members individuals = .ok individuals := by
  cases individuals; simp [components.copy_individual_members, Rowl.Concepts.copy_individual_identity,
    copy_individuals_eq]

private theorem copy_sub_role_eq (sub : SubObjectPropertyExpression) : components.copy_sub_role sub = .ok sub := by
  cases sub <;> simp [components.copy_sub_role, Rowl.Concepts.copy_role_identity, copy_role_members_eq]

private theorem copy_range_list_spec (ranges : alloc.vec.Vec DataRange) (index : Usize) (out : alloc.vec.Vec DataRange)
    (room : out.val.length + (ranges.val.length - index.val) ≤ Usize.max)
    (each : ∀ r ∈ ranges.val, components.copy_range r = .ok r) :
    ∃ v, components.copy_range_list ranges index out = .ok v ∧ v.val = out.val ++ ranges.val.drop index.val := by
  rw [components.copy_range_list]
  by_cases more : index.val < ranges.val.length
  · have lookup : ranges.index_usize index = .ok ranges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have fits : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out ranges.val[index.val] fits)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := copy_range_list_spec ranges next pushed (by rw [contents, nextIs]; simp; omega) each
    refine ⟨v, by simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits, lookup,
      each _ (List.getElem_mem more), push, advance, run], ?_⟩
    rw [value, contents, nextIs, List.drop_eq_getElem_cons more]
    simp
  · exact ⟨out, by simp [UScalar.lt_equiv, more], by simp [List.drop_eq_nil_of_le (Nat.le_of_not_lt more)]⟩
termination_by ranges.val.length - index.val
decreasing_by omega

private theorem copy_range_members_eq (members : AtLeastTwo DataRange)
    (each : ∀ r ∈ members.elements, components.copy_range r = .ok r) :
    components.copy_range_members members = .ok members := by
  obtain ⟨v, run, value⟩ := copy_range_list_spec members.rest 0#usize (alloc.vec.Vec.new DataRange)
    (by simp) (fun r member => each r (by simp [AtLeastTwo.elements, member]))
  have restEq : v = members.rest := (alloc.vec.Vec.eq_iff _ _).mpr (by simpa using value)
  rw [components.copy_range_members]
  simp only [each members.first (by simp [AtLeastTwo.elements]), each members.second (by simp [AtLeastTwo.elements]),
    bind_ok, run, restEq]

theorem copy_range_eq (r : DataRange) : components.copy_range r = .ok r := by
  cases r with
  | Datatype dt => simp [components.copy_range, copy_datatype_eq]
  | Intersection members =>
    rw [components.copy_range]
    rw [copy_range_members_eq members (fun e member => by
      have := members_bound members e member
      exact copy_range_eq e)]
    simp
  | Union members =>
    rw [components.copy_range]
    rw [copy_range_members_eq members (fun e member => by
      have := members_bound members e member
      exact copy_range_eq e)]
    simp
  | Complement inner =>
    rw [components.copy_range, copy_range_eq inner]
    simp
  | OneOf literals =>
    cases literals
    simp [components.copy_range, copy_literal_eq, copy_literals_eq]
  | Restriction dt facets =>
    cases facets
    simp [components.copy_range, copy_datatype_eq, copy_facet_eq, copy_facets_eq]
termination_by sizeOf r
decreasing_by all_goals (subst_vars; first | omega | (simp_wf <;> omega))

private theorem copy_range_filler_eq (filler : Option DataRange) : components.copy_range_filler filler = .ok filler := by
  cases filler <;> simp [components.copy_range_filler, copy_range_eq]

private theorem copy_class_list_spec (classes : alloc.vec.Vec ClassExpression) (index : Usize)
    (out : alloc.vec.Vec ClassExpression) (room : out.val.length + (classes.val.length - index.val) ≤ Usize.max)
    (each : ∀ c ∈ classes.val, components.copy_class c = .ok c) :
    ∃ v, components.copy_class_list classes index out = .ok v ∧ v.val = out.val ++ classes.val.drop index.val := by
  rw [components.copy_class_list]
  by_cases more : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have fits : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out classes.val[index.val] fits)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := copy_class_list_spec classes next pushed (by rw [contents, nextIs]; simp; omega) each
    refine ⟨v, by simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits, lookup,
      each _ (List.getElem_mem more), push, advance, run], ?_⟩
    rw [value, contents, nextIs, List.drop_eq_getElem_cons more]
    simp
  · exact ⟨out, by simp [UScalar.lt_equiv, more], by simp [List.drop_eq_nil_of_le (Nat.le_of_not_lt more)]⟩
termination_by classes.val.length - index.val
decreasing_by omega

private theorem copy_class_members_eq (members : AtLeastTwo ClassExpression)
    (each : ∀ c ∈ members.elements, components.copy_class c = .ok c) :
    components.copy_class_members members = .ok members := by
  obtain ⟨v, run, value⟩ := copy_class_list_spec members.rest 0#usize (alloc.vec.Vec.new ClassExpression)
    (by simp) (fun c member => each c (by simp [AtLeastTwo.elements, member]))
  have restEq : v = members.rest := (alloc.vec.Vec.eq_iff _ _).mpr (by simpa using value)
  rw [components.copy_class_members]
  simp only [each members.first (by simp [AtLeastTwo.elements]), each members.second (by simp [AtLeastTwo.elements]),
    bind_ok, run, restEq]

private theorem copy_class_filler_eq (filler : Option ClassExpression)
    (each : ∀ c, filler = some c → components.copy_class c = .ok c) :
    components.copy_class_filler filler = .ok filler := by
  cases filler with
  | none => rw [components.copy_class_filler]
  | some c => rw [components.copy_class_filler]; simp [each c rfl]

theorem copy_class_eq (c : ClassExpression) : components.copy_class c = .ok c := by
  cases c with
  | Class named => simp [components.copy_class, copy_class_name_eq]
  | ObjectIntersectionOf members =>
    rw [components.copy_class]
    rw [copy_class_members_eq members (fun e member => by
      have := members_bound members e member
      exact copy_class_eq e)]
    simp
  | ObjectUnionOf members =>
    rw [components.copy_class]
    rw [copy_class_members_eq members (fun e member => by
      have := members_bound members e member
      exact copy_class_eq e)]
    simp
  | ObjectComplementOf inner =>
    rw [components.copy_class, copy_class_eq inner]
    simp
  | ObjectOneOf individuals =>
    cases individuals
    simp [components.copy_class, Rowl.Concepts.copy_individual_identity, copy_individuals_eq]
  | ObjectSomeValuesFrom role filler =>
    rw [components.copy_class, Rowl.Concepts.copy_role_identity, copy_class_eq filler]
    simp
  | ObjectAllValuesFrom role filler =>
    rw [components.copy_class, Rowl.Concepts.copy_role_identity, copy_class_eq filler]
    simp
  | ObjectHasValue role a =>
    simp [components.copy_class, Rowl.Concepts.copy_role_identity, Rowl.Concepts.copy_individual_identity]
  | ObjectHasSelf role => simp [components.copy_class, Rowl.Concepts.copy_role_identity]
  | ObjectMinCardinality count role filler =>
    rw [components.copy_class, copy_natural_eq, Rowl.Concepts.copy_role_identity,
      copy_class_filler_eq filler (fun e same => by
        have : sizeOf e < sizeOf filler := by rw [same]; simp +arith
        exact copy_class_eq e)]
    simp
  | ObjectMaxCardinality count role filler =>
    rw [components.copy_class, copy_natural_eq, Rowl.Concepts.copy_role_identity,
      copy_class_filler_eq filler (fun e same => by
        have : sizeOf e < sizeOf filler := by rw [same]; simp +arith
        exact copy_class_eq e)]
    simp
  | ObjectExactCardinality count role filler =>
    rw [components.copy_class, copy_natural_eq, Rowl.Concepts.copy_role_identity,
      copy_class_filler_eq filler (fun e same => by
        have : sizeOf e < sizeOf filler := by rw [same]; simp +arith
        exact copy_class_eq e)]
    simp
  | DataSomeValuesFrom p r => simp [components.copy_class, copy_data_property_eq, copy_range_eq]
  | DataAllValuesFrom p r => simp [components.copy_class, copy_data_property_eq, copy_range_eq]
  | DataHasValue p lt => simp [components.copy_class, copy_data_property_eq, copy_literal_eq]
  | DataMinCardinality count p filler =>
    simp [components.copy_class, copy_natural_eq, copy_data_property_eq, copy_range_filler_eq]
  | DataMaxCardinality count p filler =>
    simp [components.copy_class, copy_natural_eq, copy_data_property_eq, copy_range_filler_eq]
  | DataExactCardinality count p filler =>
    simp [components.copy_class, copy_natural_eq, copy_data_property_eq, copy_range_filler_eq]
termination_by sizeOf c
decreasing_by all_goals (subst_vars; first | omega | (simp_wf <;> omega))

/-- A copy of an axiom, when there is one, is the axiom. -/
theorem copy_axiom_spec (ax : Axiom) :
    components.copy_axiom ax = .ok none ∨ components.copy_axiom ax = .ok (some ax) := by
  cases ax <;> simp [components.copy_axiom, copy_class_eq, copy_class_name_eq, copy_class_members_eq,
    copy_sub_role_eq, Rowl.Concepts.copy_role_identity, copy_role_members_eq, copy_data_property_eq,
    copy_data_members_eq, copy_range_eq, copy_roles_eq, copy_data_list_eq, copy_individual_members_eq,
    Rowl.Concepts.copy_individual_identity, copy_literal_eq]

private theorem copy_range_members_full (members : AtLeastTwo DataRange) : components.copy_range_members members = .ok members :=
  copy_range_members_eq members (fun r _ => copy_range_eq r)

private theorem copy_class_members_full (members : AtLeastTwo ClassExpression) :
    components.copy_class_members members = .ok members :=
  copy_class_members_eq members (fun c _ => copy_class_eq c)

/-! ## The part -/

/-- The part keeps the axioms that mean something and are no assertion, and
    the assertions that name a member. -/
def Kept (members : List Individual) (ax : Axiom) : Prop :=
  (IsAssertion ax ∧ ∃ i ∈ axiomIndividuals ax, i ∈ members) ∨ (¬ IsAssertion ax ∧ ¬ Meaningless ax)

private theorem meaningless_individuals {ax : Axiom} (meaningless : Meaningless ax) : axiomIndividuals ax = [] := by
  cases ax <;> simp only [Meaningless] at meaningless <;> simp [axiomIndividuals]

theorem kept_spec (items : alloc.vec.Vec AnnotatedAxiom) (table : alloc.vec.Vec (alloc.vec.Vec Individual))
    (index : Usize) (members : alloc.vec.Vec Individual) (tableOk : TableOf items.val table.val)
    (more : index.val < items.val.length) :
    ∃ b, components.kept items table index members = .ok b ∧
      (b = true ↔ Kept members.val items.val[index.val].axiom) := by
  rw [components.kept]
  have lookup : items.index_usize index = .ok items.val[index.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
  obtain ⟨named, atIndex, entry⟩ := entry_of_get tableOk (List.getElem?_eq_getElem more)
  by_cases assertion : IsAssertion items.val[index.val].axiom
  · obtain ⟨b, run, names⟩ := names_member_spec table index members
    refine ⟨b, by simp [lookup, assertion_eq, assertion, run], ?_⟩
    rw [names, atIndex]
    constructor
    · rintro ⟨n, same, i, mi, inside⟩
      simp only [Option.some.injEq] at same
      rw [← same] at mi
      exact .inl ⟨assertion, i, (entry.1 assertion i).mp mi, inside⟩
    · rintro (⟨_, i, mi, inside⟩ | ⟨no, _⟩)
      · exact ⟨named, rfl, i, (entry.1 assertion i).mpr mi, inside⟩
      · exact absurd assertion no
  · refine ⟨!decide (Meaningless items.val[index.val].axiom), by simp [lookup, assertion_eq, assertion,
      meaningless_eq], ?_⟩
    simp [Kept, assertion]

theorem select_spec (items : alloc.vec.Vec AnnotatedAxiom) (table : alloc.vec.Vec (alloc.vec.Vec Individual))
    (index : Usize) (members : alloc.vec.Vec Individual) (out : alloc.vec.Vec AnnotatedAxiom)
    (tableOk : TableOf items.val table.val) :
    ∃ r, components.select items table index members out = .ok r ∧ ∀ v, r = some v →
      (∀ y ∈ v.val, y ∈ out.val ∨ ∃ x ∈ items.val.drop index.val, Kept members.val x.axiom ∧ y.axiom = x.axiom) ∧
      (∀ x ∈ items.val.drop index.val, Kept members.val x.axiom → ∃ y ∈ v.val, y.axiom = x.axiom) ∧
      (∀ y ∈ out.val, y ∈ v.val) := by
  rw [components.select]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨b, run1, keptIff⟩ := kept_spec items table index members tableOk more
    cases b with
    | false =>
      obtain ⟨r, run, facts⟩ := select_spec items table next members out tableOk
      refine ⟨r, by simp [UScalar.lt_equiv, more, lookup, run1, advance, run], fun v same => ?_⟩
      obtain ⟨sub, sup, keep⟩ := facts v same
      rw [nextIs] at sub sup
      refine ⟨fun y my => ?_, fun x mx kx => ?_, keep⟩
      · rcases sub y my with inOut | ⟨x, mx, kx, ax⟩
        · exact .inl inOut
        · exact .inr ⟨x, by rw [split]; exact List.mem_cons_of_mem _ mx, kx, ax⟩
      · rw [split] at mx
        rcases List.mem_cons.mp mx with rfl | later
        · exact absurd (keptIff.mpr kx) (by simp)
        · exact sup x later kx
    | true =>
      have kx := keptIff.mp rfl
      rcases copy_axiom_spec items.val[index.val].axiom with none' | some'
      · exact ⟨none, by simp [UScalar.lt_equiv, more, lookup, run1, none'], by simp⟩
      · by_cases room : out.val.length < Usize.max
        · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out
            ({ annotations := alloc.vec.Vec.new Annotation, «axiom» := items.val[index.val].axiom } : AnnotatedAxiom)
            room)
          obtain ⟨r, run, facts⟩ := select_spec items table next members pushed tableOk
          refine ⟨r, by simp [UScalar.lt_equiv, more, lookup, run1, some', alloc.vec.Vec.len_val, usize_max_val,
            room, push, advance, run], fun v same => ?_⟩
          obtain ⟨sub, sup, keep⟩ := facts v same
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
                exact .inr ⟨_, by rw [split]; exact List.mem_cons_self .., kx, rfl⟩
            · exact .inr ⟨x, by rw [split]; exact List.mem_cons_of_mem _ mx, kx', ax⟩
          · rw [split] at mx
            rcases List.mem_cons.mp mx with rfl | later
            · exact ⟨_, fresh, rfl⟩
            · exact sup x later kx'
        · exact ⟨none, by simp [UScalar.lt_equiv, more, lookup, run1, some', alloc.vec.Vec.len_val, usize_max_val,
            room], by simp⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, more], fun v same => ?_⟩
    cases same
    refine ⟨fun y my => .inl my, fun x mx => ?_, fun y my => my⟩
    rw [List.drop_eq_nil_of_le (by omega)] at mx
    cases mx
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- The conditions of `Rowl.Partition.instance_part` for a part of a closure
    and an individual: the rest of the closure is assertions and axioms
    without meaning, the assertions of the part name no individual of the
    rest, and the rest does not name the individual. -/
def PartFor (items part : List AnnotatedAxiom) (a : NamedIndividual) : Prop :=
  ∃ rest : List AnnotatedAxiom,
    (∀ x ∈ items, (∃ y ∈ part, y.axiom = x.axiom) ∨ x ∈ rest) ∧
    (∀ y ∈ part, ∃ x ∈ items, x.axiom = y.axiom) ∧
    (∀ x ∈ rest, IsAssertion x.axiom ∨ Meaningless x.axiom) ∧
    (∀ x ∈ part, IsAssertion x.axiom → ∀ y ∈ rest, ∀ i ∈ axiomIndividuals x.axiom,
      i ∉ axiomIndividuals y.axiom) ∧
    (∀ y ∈ rest, Individual.Named a ∉ axiomIndividuals y.axiom)

/-- The part selected for members that are closed under the table and hold
    the individual meets the conditions of `instance_part`. -/
private theorem part_for_closed {items part : List AnnotatedAxiom} {table : List (alloc.vec.Vec Individual)}
    {members : List Individual} {a : NamedIndividual}
    (tableOk : TableOf items table) (closedTable : ClosedUnder table members)
    (inMembers : Individual.Named a ∈ members)
    (sub : ∀ y ∈ part, ∃ x ∈ items, Kept members x.axiom ∧ y.axiom = x.axiom)
    (sup : ∀ x ∈ items, Kept members x.axiom → ∃ y ∈ part, y.axiom = x.axiom) :
    PartFor items part a := by
  have isClosed := closed_items tableOk closedTable
  classical
  refine ⟨items.filter (fun x => ¬ Kept members x.axiom), ?_, ?_, ?_, ?_, ?_⟩
  · intro x mx
    by_cases kx : Kept members x.axiom
    · exact .inl (sup x mx kx)
    · exact .inr (List.mem_filter.mpr ⟨mx, by simp [kx]⟩)
  · intro y my
    obtain ⟨x, mx, -, ax⟩ := sub y my
    exact ⟨x, mx, ax.symm⟩
  · intro x mx
    have notKept : ¬ Kept members x.axiom := by simpa using (List.mem_filter.mp mx).2
    by_cases assertion : IsAssertion x.axiom
    · exact .inl assertion
    · refine .inr ?_
      by_contra meaningless
      exact notKept (.inr ⟨assertion, meaningless⟩)
  · intro x mx assertion y my i mi mi'
    obtain ⟨x0, mx0, kx0, ax⟩ := sub x mx
    rw [ax] at assertion mi
    have touches : ∃ j ∈ axiomIndividuals x0.axiom, j ∈ members := by
      rcases kx0 with ⟨_, touch⟩ | ⟨no, _⟩
      · exact touch
      · exact absurd assertion no
    have inside := isClosed x0 mx0 assertion touches i mi
    have notKept : ¬ Kept members y.axiom := by simpa using (List.mem_filter.mp my).2
    by_cases yAssertion : IsAssertion y.axiom
    · exact notKept (.inl ⟨yAssertion, i, mi', inside⟩)
    · have meaningless : Meaningless y.axiom := by
        by_contra other
        exact notKept (.inr ⟨yAssertion, other⟩)
      rw [meaningless_individuals meaningless] at mi'
      cases mi'
  · intro y my mi
    have notKept : ¬ Kept members y.axiom := by simpa using (List.mem_filter.mp my).2
    by_cases yAssertion : IsAssertion y.axiom
    · exact notKept (.inl ⟨yAssertion, _, mi, inMembers⟩)
    · have meaningless : Meaningless y.axiom := by
        by_contra other
        exact notKept (.inr ⟨yAssertion, other⟩)
      rw [meaningless_individuals meaningless] at mi
      cases mi

/-- The axioms other than assertions meet the conditions of `instance_part`
    for an individual that no assertion names. -/
private theorem part_for_absent {items part : List AnnotatedAxiom} {a : NamedIndividual}
    (sub : ∀ y ∈ part, ∃ x ∈ items, Kept [] x.axiom ∧ y.axiom = x.axiom)
    (sup : ∀ x ∈ items, Kept [] x.axiom → ∃ y ∈ part, y.axiom = x.axiom)
    (absent : ∀ x ∈ items, IsAssertion x.axiom → Individual.Named a ∉ axiomIndividuals x.axiom) :
    PartFor items part a := by
  classical
  refine ⟨items.filter (fun x => ¬ Kept [] x.axiom), ?_, ?_, ?_, ?_, ?_⟩
  · intro x mx
    by_cases kx : Kept [] x.axiom
    · exact .inl (sup x mx kx)
    · exact .inr (List.mem_filter.mpr ⟨mx, by simp [kx]⟩)
  · intro y my
    obtain ⟨x, mx, -, ax⟩ := sub y my
    exact ⟨x, mx, ax.symm⟩
  · intro x mx
    have notKept : ¬ Kept [] x.axiom := by simpa using (List.mem_filter.mp mx).2
    by_cases assertion : IsAssertion x.axiom
    · exact .inl assertion
    · refine .inr ?_
      by_contra meaningless
      exact notKept (.inr ⟨assertion, meaningless⟩)
  · intro x mx assertion
    obtain ⟨x0, _, kx0, ax⟩ := sub x mx
    rw [ax] at assertion
    rcases kx0 with ⟨_, _, _, none⟩ | ⟨no, _⟩
    · simp at none
    · exact absurd assertion no
  · intro y my mi
    have notKept : ¬ Kept [] y.axiom := by simpa using (List.mem_filter.mp my).2
    by_cases yAssertion : IsAssertion y.axiom
    · exact absent y (List.mem_filter.mp my).1 yAssertion mi
    · have meaningless : Meaningless y.axiom := by
        by_contra other
        exact notKept (.inr ⟨yAssertion, other⟩)
      rw [meaningless_individuals meaningless] at mi
      cases mi

/-- `component_closure` checks the closure and, when it answers, returns copies
    of the axioms that mean something and are no assertion and of the
    assertions of a component of the individual: the rest of the closure is
    assertions and axioms without meaning, and the assertions of the part name
    no individual of the rest, nor does the rest name the individual. -/
theorem component_closure_correct (items : alloc.vec.Vec AnnotatedAxiom) (a : NamedIndividual) :
    ∃ r, components.component_closure items a = .ok r ∧ ∀ part, r = some part →
      (∀ x ∈ items.val, ItemOk.{w} x) ∧ ∃ rest : List AnnotatedAxiom,
        (∀ x ∈ items.val, (∃ y ∈ part.val, y.axiom = x.axiom) ∨ x ∈ rest) ∧
        (∀ y ∈ part.val, ∃ x ∈ items.val, x.axiom = y.axiom) ∧
        (∀ x ∈ rest, IsAssertion x.axiom ∨ Meaningless x.axiom) ∧
        (∀ x ∈ part.val, IsAssertion x.axiom → ∀ y ∈ rest, ∀ i ∈ axiomIndividuals x.axiom,
          i ∉ axiomIndividuals y.axiom) ∧
        (∀ y ∈ rest, Individual.Named a ∉ axiomIndividuals y.axiom) := by
  rw [components.component_closure]
  obtain ⟨b, runItems, itemsOk⟩ := plain_items_spec.{w} items 0#usize
  simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at itemsOk
  cases b with
  | false => exact ⟨none, by simp [runItems], by simp⟩
  | true =>
    obtain ⟨r0, run0, tableFacts⟩ := individual_table_spec items 0#usize
      (alloc.vec.Vec.new (alloc.vec.Vec Individual)) (by simp) (by simp)
    cases r0 with
    | none => exact ⟨none, by simp [runItems, run0], by simp⟩
    | some table =>
      have tableOk := table_of (tableFacts table rfl)
      have named : ({ iri := a.iri } : NamedIndividual) = a := by cases a; rfl
      obtain ⟨r1, run1, memberFacts⟩ := members_of_spec table (Individual.Named { iri := a.iri })
      cases r1 with
      | none => exact ⟨none, by simp [runItems, run0, Rowl.Nnf.copy_iri_identity, run1], by simp⟩
      | some members =>
        obtain ⟨inMembers, closedTable⟩ := memberFacts members rfl
        rw [named] at inMembers
        obtain ⟨r3, run3, selectFacts⟩ := select_spec items table 0#usize members
          (alloc.vec.Vec.new AnnotatedAxiom) tableOk
        simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at selectFacts
        refine ⟨r3, by simp [runItems, run0, Rowl.Nnf.copy_iri_identity, run1, run3], fun part same => ?_⟩
        obtain ⟨sub0, sup, -⟩ := selectFacts part same
        have sub : ∀ y ∈ part.val, ∃ x ∈ items.val, Kept members.val x.axiom ∧ y.axiom = x.axiom := by
          intro y my
          rcases sub0 y my with fresh | found
          · simp at fresh
          · exact found
        exact ⟨itemsOk rfl, part_for_closed tableOk closedTable inMembers sub sup⟩

/-- When `component_closure` returns a part for a named individual and the
    closure has a model, an instance question about the individual with a
    class expression that `plain_question` accepts has the same answer for the
    part as for the closure, under every datatype map that is the OWL 2 map on
    the datatypes of `datatypes` and for every vocabulary. -/
theorem part_instance_correct {items part : alloc.vec.Vec AnnotatedAxiom} {a : NamedIndividual}
    {e : ClassExpression} (split : components.component_closure items a = .ok (some part))
    (question : components.plain_question e = .ok true)
    {Native : Type w} (D : DatatypeMap Native) (N : Normative D) (V : Vocabulary) (vocab : IsVocabulary D V)
    (consistent : Consistent.{u,v,w} D V items.val) :
    InstanceOf.{u,v,w} D V items.val a e ↔ InstanceOf.{u,v,w} D V part.val a e := by
  obtain ⟨r, run, facts⟩ := component_closure_correct.{w} items a
  rw [split] at run
  simp only [Result.ok.injEq] at run
  obtain ⟨itemsOk, rest, cover, inside, kinds, apart, aApart⟩ := facts part run.symm
  obtain ⟨b, runQ, closedQ⟩ := plain_question_spec.{w} e
  rw [question] at runQ
  simp only [Result.ok.injEq] at runQ
  subst runQ
  exact instance_part vocab cover inside (fun x mx na => (itemsOk x mx D N V vocab).2 na)
    (fun x mx ia => (itemsOk x mx D N V vocab).1 ia) kinds apart aApart (closedQ rfl D N V vocab) consistent

/-! ## The axioms other than assertions -/

/-- `tbox_closure` checks the closure and, when it answers, returns copies of
    the axioms that mean something and are no assertion; the rest of the
    closure is assertions and axioms without meaning. -/
theorem tbox_closure_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ r, components.tbox_closure items = .ok r ∧ ∀ part, r = some part →
      (∀ x ∈ items.val, ItemOk.{w} x) ∧ ∃ rest : List AnnotatedAxiom,
        (∀ x ∈ items.val, (∃ y ∈ part.val, y.axiom = x.axiom) ∨ x ∈ rest) ∧
        (∀ y ∈ part.val, ∃ x ∈ items.val, x.axiom = y.axiom) ∧
        (∀ x ∈ rest, IsAssertion x.axiom ∨ Meaningless x.axiom) ∧
        (∀ x ∈ part.val, ¬ IsAssertion x.axiom) := by
  rw [components.tbox_closure]
  obtain ⟨b, runItems, itemsOk⟩ := plain_items_spec.{w} items 0#usize
  simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at itemsOk
  cases b with
  | false => exact ⟨none, by simp [runItems], by simp⟩
  | true =>
    obtain ⟨r0, run0, tableFacts⟩ := individual_table_spec items 0#usize
      (alloc.vec.Vec.new (alloc.vec.Vec Individual)) (by simp) (by simp)
    cases r0 with
    | none => exact ⟨none, by simp [runItems, run0], by simp⟩
    | some table =>
      have tableOk := table_of (tableFacts table rfl)
      obtain ⟨r, run, selectFacts⟩ := select_spec items table 0#usize (alloc.vec.Vec.new Individual)
        (alloc.vec.Vec.new AnnotatedAxiom) tableOk
      simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at selectFacts
      refine ⟨r, by simp [runItems, run0, run], fun part same => ?_⟩
      obtain ⟨sub, sup, -⟩ := selectFacts part same
      have empty : (alloc.vec.Vec.new Individual).val = [] := rfl
      rw [empty] at sub sup
      classical
      refine ⟨itemsOk rfl, items.val.filter (fun x => ¬ Kept [] x.axiom), ?_, ?_, ?_, ?_⟩
      · intro x mx
        by_cases kx : Kept [] x.axiom
        · exact .inl (sup x mx kx)
        · exact .inr (List.mem_filter.mpr ⟨mx, by simp [kx]⟩)
      · intro y my
        rcases sub y my with fresh | ⟨x, mx, -, ax⟩
        · simp at fresh
        · exact ⟨x, mx, ax.symm⟩
      · intro x mx
        have notKept : ¬ Kept [] x.axiom := by simpa using (List.mem_filter.mp mx).2
        by_cases assertion : IsAssertion x.axiom
        · exact .inl assertion
        · refine .inr ?_
          by_contra meaningless
          exact notKept (.inr ⟨assertion, meaningless⟩)
      · intro x mx assertion
        rcases sub x mx with fresh | ⟨x0, _, kx0, ax⟩
        · simp at fresh
        · rw [ax] at assertion
          rcases kx0 with ⟨_, _, _, none⟩ | ⟨no, _⟩
          · simp at none
          · exact no assertion

/-- When `tbox_closure` returns the axioms other than assertions and the
    closure has a model, a class expression that `plain_question` accepts is
    satisfiable for them exactly when it is for the closure. -/
theorem part_satisfiable_correct {items part : alloc.vec.Vec AnnotatedAxiom} {e : ClassExpression}
    (split : components.tbox_closure items = .ok (some part))
    (question : components.plain_question e = .ok true)
    {Native : Type w} (D : DatatypeMap Native) (N : Normative D) (V : Vocabulary) (vocab : IsVocabulary D V)
    (consistent : Consistent.{u,v,w} D V items.val) :
    ClassSatisfiable.{u,v,w} D V items.val e ↔ ClassSatisfiable.{u,v,w} D V part.val e := by
  obtain ⟨r, run, facts⟩ := tbox_closure_correct.{w} items
  rw [split] at run
  simp only [Result.ok.injEq] at run
  obtain ⟨itemsOk, rest, cover, inside, kinds, plainPart⟩ := facts part run.symm
  obtain ⟨b, runQ, closedQ⟩ := plain_question_spec.{w} e
  rw [question] at runQ
  simp only [Result.ok.injEq] at runQ
  subst runQ
  exact satisfiable_part vocab cover inside (fun x mx na => (itemsOk x mx D N V vocab).2 na)
    (fun x mx ia => (itemsOk x mx D N V vocab).1 ia) kinds (fun x mx ia => absurd ia (plainPart x mx))
    (closedQ rfl D N V vocab) consistent

/-- When `tbox_closure` returns the axioms other than assertions and the
    closure has a model, one class expression that `plain_question` accepts is
    subsumed by another for them exactly when it is for the closure. -/
theorem part_subsumed_correct {items part : alloc.vec.Vec AnnotatedAxiom} {a b : ClassExpression}
    (split : components.tbox_closure items = .ok (some part))
    (questionA : components.plain_question a = .ok true) (questionB : components.plain_question b = .ok true)
    {Native : Type w} (D : DatatypeMap Native) (N : Normative D) (V : Vocabulary) (vocab : IsVocabulary D V)
    (consistent : Consistent.{u,v,w} D V items.val) :
    Subsumed.{u,v,w} D V items.val a b ↔ Subsumed.{u,v,w} D V part.val a b := by
  obtain ⟨r, run, facts⟩ := tbox_closure_correct.{w} items
  rw [split] at run
  simp only [Result.ok.injEq] at run
  obtain ⟨itemsOk, rest, cover, inside, kinds, plainPart⟩ := facts part run.symm
  obtain ⟨ba, runA, closedA⟩ := plain_question_spec.{w} a
  rw [questionA] at runA
  simp only [Result.ok.injEq] at runA
  subst runA
  obtain ⟨bb, runB, closedB⟩ := plain_question_spec.{w} b
  rw [questionB] at runB
  simp only [Result.ok.injEq] at runB
  subst runB
  exact subsumed_part vocab cover inside (fun x mx na => (itemsOk x mx D N V vocab).2 na)
    (fun x mx ia => (itemsOk x mx D N V vocab).1 ia) kinds (fun x mx ia => absurd ia (plainPart x mx))
    (closedA rfl D N V vocab) (closedB rfl D N V vocab) consistent

/-! ## Consistency part by part -/

/-- A vocabulary that names the individuals of a closure with keys names those
    of copies of some of its axioms. -/
private theorem keyed_inside {V : Vocabulary} {items part : List AnnotatedAxiom}
    (inside : ∀ y ∈ part, ∃ x ∈ items, x.axiom = y.axiom)
    (keyed : Rowl.KeyEncoding.NamesKeyed V items) : Rowl.KeyEncoding.NamesKeyed V part := by
  intro keyedPart a member
  obtain ⟨y, my, key⟩ := keyedPart
  obtain ⟨x, mx, same⟩ := inside y my
  have keyedItems : Rowl.KeyEncoding.Keyed items := ⟨x, mx, by rw [same]; exact key⟩
  refine keyed keyedItems a ?_
  simp only [Rowl.KeyEncoding.closureIndividuals, List.mem_flatMap] at member ⊢
  obtain ⟨z, mz, mi⟩ := member
  obtain ⟨x', mx', same'⟩ := inside z mz
  exact ⟨x', mx', by rw [same']; exact mi⟩

/-- Every assertion names an individual. -/
private theorem assertion_names {ax : Axiom} (assertion : IsAssertion ax) : ∃ i, i ∈ axiomIndividuals ax := by
  cases ax <;> simp only [IsAssertion] at assertion <;> simp [axiomIndividuals, AtLeastTwo.elements]

/-- Whether the parts checked so far hold the axiom at an index: an axiom that
    means something and is no assertion, or an assertion that is done. -/
def Checked (done : List Bool) (j : Nat) (x : AnnotatedAxiom) : Prop :=
  (¬ IsAssertion x.axiom ∧ ¬ Meaningless x.axiom) ∨ (IsAssertion x.axiom ∧ done[j]? = some true)

/-- The axioms of a closure that the parts checked so far hold. -/
noncomputable def checked (items : List AnnotatedAxiom) (done : List Bool) : List AnnotatedAxiom :=
  (List.range items.length).filterMap fun j =>
    match items[j]? with
    | some x => if Checked done j x then some x else none
    | none => none

private theorem mem_checked {items : List AnnotatedAxiom} {done : List Bool} {x : AnnotatedAxiom} :
    x ∈ checked items done ↔ ∃ j, items[j]? = some x ∧ Checked done j x := by
  simp only [checked, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨j, -, h⟩
    cases hx : items[j]? with
    | none => simp [hx] at h
    | some y =>
      simp only [hx] at h
      by_cases c : Checked done j y
      · simp only [c, if_true, Option.some.injEq] at h
        subst h
        exact ⟨j, hx, c⟩
      · simp [c] at h
  · rintro ⟨j, hx, c⟩
    obtain ⟨lj, -⟩ := List.getElem?_eq_some_iff.mp hx
    exact ⟨j, lj, by simp [hx, c]⟩

theorem falses_spec (count : Usize) (out : alloc.vec.Vec Bool) :
    ∃ v, components.falses count out = .ok v ∧ ∀ j : Nat, v.val[j]? = some true → out.val[j]? = some true := by
  rw [components.falses]
  by_cases positive : 0 < count.val
  · by_cases room : out.val.length < Usize.max
    · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out false room)
      obtain ⟨fewer, sub, fewerValue⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := count) (y := 1#usize) (by simp; omega))
      have fewerIs : fewer.val = count.val - 1 := by simp at fewerValue; omega
      obtain ⟨v, run, facts⟩ := falses_spec fewer pushed
      refine ⟨v, by simp [UScalar.lt_equiv, positive, alloc.vec.Vec.len_val, usize_max_val, room, push, sub, run],
        fun j t => ?_⟩
      have t' := facts j t
      rw [contents] at t'
      by_cases lj : j < out.val.length
      · rwa [List.getElem?_append_left lj] at t'
      · rw [List.getElem?_append_right (by omega)] at t'
        rcases Nat.eq_zero_or_pos (j - out.val.length) with zero | pos
        · rw [zero] at t'
          simp at t'
        · rw [List.getElem?_eq_none (by simp; omega)] at t'
          cases t'
    · exact ⟨out, by simp [UScalar.lt_equiv, positive, alloc.vec.Vec.len_val, usize_max_val, room], fun j t => t⟩
  · exact ⟨out, by simp [UScalar.lt_equiv, positive], fun j t => t⟩
termination_by count.val
decreasing_by omega

theorem open_from_spec (table : alloc.vec.Vec (alloc.vec.Vec Individual)) (index : Usize)
    (done : alloc.vec.Vec Bool) :
    ∃ r, components.open_from table index done = .ok r ∧
      (r = none → ∀ (j : Nat) named, index.val ≤ j → table.val[j]? = some named → named.val ≠ [] →
        done.val[j]? = some true) ∧
      (∀ o, r = some o → ∃ named, table.val[o.val]? = some named ∧ named.val ≠ []) := by
  rw [components.open_from]
  by_cases more : index.val < table.val.length
  · have lookup : table.index_usize index = .ok table.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    by_cases empty : table.val[index.val].val = []
    · obtain ⟨r, run, noneFacts, someFacts⟩ := open_from_spec table next done
      rw [nextIs] at noneFacts
      refine ⟨r, by simp [UScalar.lt_equiv, more, lookup, alloc.vec.Vec.len_val, empty, advance, run],
        fun none' j named lj mj ne => ?_, someFacts⟩
      rcases Nat.lt_or_ge j (index.val + 1) with small | large
      · have jIs : j = index.val := by omega
        rw [jIs, List.getElem?_eq_getElem more] at mj
        simp only [Option.some.injEq] at mj
        rw [← mj] at ne
        exact absurd empty ne
      · exact noneFacts none' j named large mj ne
    · by_cases inDone : index.val < done.val.length
      · have lookupD : done.index_usize index = .ok done.val[index.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inDone]
        cases flag : done.val[index.val] with
        | true =>
          obtain ⟨r, run, noneFacts, someFacts⟩ := open_from_spec table next done
          rw [nextIs] at noneFacts
          refine ⟨r, by simp [UScalar.lt_equiv, more, lookup, alloc.vec.Vec.len_val, empty, inDone, lookupD, flag,
            advance, run], fun none' j named lj mj ne => ?_, someFacts⟩
          rcases Nat.lt_or_ge j (index.val + 1) with small | large
          · have jIs : j = index.val := by omega
            rw [jIs, List.getElem?_eq_getElem inDone, flag]
          · exact noneFacts none' j named large mj ne
        | false =>
          refine ⟨some index, by simp [UScalar.lt_equiv, more, lookup, alloc.vec.Vec.len_val, empty, inDone,
            lookupD, flag], by simp, fun o same => ?_⟩
          simp only [Option.some.injEq] at same
          rw [← same]
          exact ⟨_, List.getElem?_eq_getElem more, empty⟩
      · refine ⟨some index, by simp [UScalar.lt_equiv, more, lookup, alloc.vec.Vec.len_val, empty, inDone],
          by simp, fun o same => ?_⟩
        simp only [Option.some.injEq] at same
        rw [← same]
        exact ⟨_, List.getElem?_eq_getElem more, empty⟩
  · refine ⟨none, by simp [UScalar.lt_equiv, more], fun _ j named lj mj _ => ?_, by simp⟩
    rw [List.getElem?_eq_none (by omega)] at mj
    cases mj
termination_by table.val.length - index.val
decreasing_by all_goals omega

theorem mark_spec (table : alloc.vec.Vec (alloc.vec.Vec Individual)) (index : Usize)
    (members : alloc.vec.Vec Individual) (done : alloc.vec.Vec Bool) :
    ∃ r, components.mark table index members done = .ok r ∧ ∀ done', r = some done' →
      (∀ j : Nat, done'.val[j]? = some true → done.val[j]? = some true ∨
        ∃ named, table.val[j]? = some named ∧ Names named members.val) ∧
      (∀ (j : Nat) named, index.val ≤ j → table.val[j]? = some named → Names named members.val →
        done.val[j]? ≠ some true) := by
  rw [components.mark]
  by_cases more : index.val < table.val.length
  · have lookup : table.index_usize index = .ok table.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨b, runB, any⟩ := any_member_spec members table.val[index.val] 0#usize
    simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at any
    cases b with
    | false =>
      obtain ⟨r, run, facts⟩ := mark_spec table next members done
      refine ⟨r, by simp [UScalar.lt_equiv, more, lookup, runB, advance, run], fun done' same => ?_⟩
      obtain ⟨grown, fresh⟩ := facts done' same
      rw [nextIs] at fresh
      refine ⟨grown, fun j named lj mj names => ?_⟩
      rcases Nat.lt_or_ge j (index.val + 1) with small | large
      · have jIs : j = index.val := by omega
        rw [jIs, List.getElem?_eq_getElem more] at mj
        simp only [Option.some.injEq] at mj
        rw [← mj] at names
        obtain ⟨i, mi, inside⟩ := names
        exact absurd (any.mpr ⟨i, mi, inside⟩) (by simp)
      · exact fresh j named large mj names
    | true =>
      by_cases inDone : index.val < done.val.length
      · have lookupD : done.index_usize index = .ok done.val[index.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inDone]
        cases flag : done.val[index.val] with
        | true => exact ⟨none, by simp [UScalar.lt_equiv, more, lookup, runB, alloc.vec.Vec.len_val, inDone,
            lookupD, flag], by simp⟩
        | false =>
          obtain ⟨r, run, facts⟩ := mark_spec table next members (done.set index true)
          refine ⟨r, by simp [UScalar.lt_equiv, more, lookup, runB, alloc.vec.Vec.len_val, inDone, lookupD, flag,
            alloc.vec.Vec.index_mut_usize, advance, run], fun done' same => ?_⟩
          obtain ⟨grown, fresh⟩ := facts done' same
          rw [nextIs] at fresh
          refine ⟨fun j t => ?_, fun j named lj mj names => ?_⟩
          · rcases grown j t with old | touched
            · rw [alloc.vec.Vec.set_val_eq, List.getElem?_set] at old
              by_cases same : index.val = j
              · right
                rw [← same, List.getElem?_eq_getElem more]
                exact ⟨_, rfl, any.mp rfl⟩
              · left
                simpa [same] using old
            · exact .inr touched
          · rcases Nat.lt_or_ge j (index.val + 1) with small | large
            · have jIs : j = index.val := by omega
              rw [jIs, List.getElem?_eq_getElem inDone, flag]
              simp
            · have notDone := fresh j named large mj names
              rw [alloc.vec.Vec.set_val_eq, List.getElem?_set] at notDone
              have ne : index.val ≠ j := by omega
              simpa [ne] using notDone
      · obtain ⟨r, run, facts⟩ := mark_spec table next members done
        refine ⟨r, by simp [UScalar.lt_equiv, more, lookup, runB, alloc.vec.Vec.len_val, inDone, advance, run],
          fun done' same => ?_⟩
        obtain ⟨grown, fresh⟩ := facts done' same
        rw [nextIs] at fresh
        refine ⟨grown, fun j named lj mj names => ?_⟩
        rcases Nat.lt_or_ge j (index.val + 1) with small | large
        · have jIs : j = index.val := by omega
          rw [jIs, List.getElem?_eq_none (by omega)]
          simp
        · exact fresh j named large mj names
  · refine ⟨some done, by simp [UScalar.lt_equiv, more], fun done' same => ?_⟩
    simp only [Option.some.injEq] at same
    subst same
    refine ⟨fun j t => .inl t, fun j named lj mj _ => ?_⟩
    rw [List.getElem?_eq_none (by omega)] at mj
    cases mj
termination_by table.val.length - index.val
decreasing_by all_goals omega

/-- One step of `parts_from`: a model of the checked axioms and a model of the
    part of a closed component combine into a model of the checked axioms with
    the assertions of the component done, provided that none of them was done
    before. -/
private theorem checked_step {Native : Type w} {D : DatatypeMap Native} (N : Normative D) {V : Vocabulary}
    (vocab : IsVocabulary D V) {items part : List AnnotatedAxiom} {table : List (alloc.vec.Vec Individual)}
    {members : List Individual} {done done' : List Bool}
    (tableOk : TableOf items table) (itemsOk : ∀ x ∈ items, ItemOk.{w} x)
    (closed : ClosedUnder table members)
    (sub : ∀ y ∈ part, ∃ x ∈ items, Kept members x.axiom ∧ y.axiom = x.axiom)
    (sup : ∀ x ∈ items, Kept members x.axiom → ∃ y ∈ part, y.axiom = x.axiom)
    (grown : ∀ j : Nat, done'[j]? = some true → done[j]? = some true ∨
      ∃ named, table[j]? = some named ∧ Names named members)
    (fresh : ∀ (j : Nat) named, table[j]? = some named → Names named members → done[j]? ≠ some true)
    (consistentPart : Consistent.{u, max w v, w} D V part)
    (consistentDone : Consistent.{u, max w v, w} D V (checked items done)) :
    Consistent.{u, max w v, w} D V (checked items done') := by
  have isClosed := closed_items tableOk closed
  have inItems : ∀ x ∈ checked items done', x ∈ items := fun x mx => by
    obtain ⟨j, hx, -⟩ := mem_checked.mp mx
    exact List.mem_of_getElem? hx
  classical
  refine consistent_join vocab (rest := (checked items done).filter (fun x => IsAssertion x.axiom))
    (others := checked items done) ?cover
    (fun x mx na => (itemsOk x (inItems x mx) D N V vocab).2 na)
    (fun x mx ia => (itemsOk x (inItems x mx) D N V vocab).1 ia) ?kinds ?apart ?othersCover
    consistentPart consistentDone
  case cover =>
    intro x mx
    obtain ⟨j, hx, c⟩ := mem_checked.mp mx
    rcases c with ⟨na, nm⟩ | ⟨ia, t⟩
    · exact .inl (sup x (List.mem_of_getElem? hx) (.inr ⟨na, nm⟩))
    · rcases grown j t with old | ⟨named, atJ, names⟩
      · exact .inr (List.mem_filter.mpr ⟨mem_checked.mpr ⟨j, hx, .inr ⟨ia, old⟩⟩, by simp [ia]⟩)
      · refine .inl (sup x (List.mem_of_getElem? hx) (.inl ⟨ia, ?_⟩))
        have entry := tableOk.2 j x named hx atJ
        obtain ⟨i, mi, inside⟩ := names
        exact ⟨i, (entry.1 ia i).mp mi, inside⟩
  case kinds =>
    intro x mx
    exact .inl (by simpa using (List.mem_filter.mp mx).2)
  case apart =>
    intro x mx ia y my i mi mi'
    obtain ⟨x0, mx0, kx0, ax⟩ := sub x mx
    rw [ax] at ia mi
    have touches : ∃ k ∈ axiomIndividuals x0.axiom, k ∈ members := by
      rcases kx0 with ⟨_, touch⟩ | ⟨no, _⟩
      · exact touch
      · exact absurd ia no
    have inside := isClosed x0 mx0 ia touches i mi
    obtain ⟨inDone, yAssertion⟩ := List.mem_filter.mp my
    have yAssertion' : IsAssertion y.axiom := by simpa using yAssertion
    obtain ⟨j, hy, c⟩ := mem_checked.mp inDone
    have t : done[j]? = some true := by
      rcases c with ⟨na, _⟩ | ⟨_, t⟩
      · exact absurd yAssertion' na
      · exact t
    obtain ⟨named, atJ, entry⟩ := entry_of_get tableOk hy
    exact fresh j named atJ ⟨i, (entry.1 yAssertion' i).mpr mi', inside⟩ t
  case othersCover =>
    intro x mx needed
    rcases needed with ⟨na, nm⟩ | inRest
    · obtain ⟨j, hx, -⟩ := mem_checked.mp mx
      exact ⟨x, mem_checked.mpr ⟨j, hx, .inl ⟨na, nm⟩⟩, rfl⟩
    · exact ⟨x, (List.mem_filter.mp inRest).1, rfl⟩

/-- `parts_from` answers whether a closure of plain axioms, plain assertions
    and axioms without meaning has a model, given that the axioms it has
    checked so far have one: each part it checks holds copies of axioms of the
    closure, and the parts of disjoint components combine. -/
theorem parts_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (table : alloc.vec.Vec (alloc.vec.Vec Individual))
    (done : alloc.vec.Vec Bool) (rounds : Usize) (tableOk : TableOf items.val table.val) :
    ∃ r, components.parts_from items table done rounds = .ok r ∧ ∀ answer, r = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native), Normative D → ∀ (V : Vocabulary), IsVocabulary D V →
        Rowl.KeyEncoding.NamesKeyed V items.val → (∀ x ∈ items.val, ItemOk.{w} x) →
        Consistent.{u, max w v, w} D V (checked items.val done.val) →
        (answer = true ↔ Consistent.{u, max w v, w} D V items.val) := by
  rw [components.parts_from]
  obtain ⟨o, runOpen, noneFacts, someFacts⟩ := open_from_spec table 0#usize done
  cases o with
  | none =>
    refine ⟨some true, by simp [runOpen], fun answer same => ?_⟩
    simp only [Option.some.injEq] at same
    subst same
    intro Native D N V vocab keyed itemsOk consistent
    simp only [true_iff]
    refine consistent_cover (fun x mx meaningful => ⟨x, mem_checked.mpr ?_, rfl⟩) consistent
    obtain ⟨j, hj, same⟩ := List.getElem_of_mem mx
    have hx : items.val[j]? = some x := by rw [List.getElem?_eq_getElem hj, same]
    refine ⟨j, hx, ?_⟩
    by_cases assertion : IsAssertion x.axiom
    · obtain ⟨named, atJ, entry⟩ := entry_of_get tableOk hx
      obtain ⟨i, mi⟩ := assertion_names assertion
      refine .inr ⟨assertion, noneFacts rfl j named (by simp) atJ ?_⟩
      intro empty
      have := (entry.1 assertion i).mpr mi
      rw [empty] at this
      cases this
    · exact .inl ⟨assertion, meaningful⟩
  | some opened =>
    obtain ⟨named, atOpen, nonempty⟩ := someFacts opened rfl
    have pos : 0 < named.val.length := List.length_pos_of_ne_nil nonempty
    have lookupT : table.index_usize opened = .ok named := by
      simp [alloc.vec.Vec.index_usize, atOpen]
    have lookupS : named.index_usize 0#usize = .ok named.val[0] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem pos]
    obtain ⟨r1, run1, memberFacts⟩ := members_of_spec table named.val[0]
    cases r1 with
    | none => exact ⟨none, by simp [runOpen, lookupT, lookupS, run1], by simp⟩
    | some members =>
      obtain ⟨-, closed⟩ := memberFacts members rfl
      obtain ⟨r2, run2, selectFacts⟩ := select_spec items table 0#usize members
        (alloc.vec.Vec.new AnnotatedAxiom) tableOk
      simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at selectFacts
      cases r2 with
      | none => exact ⟨none, by simp [runOpen, lookupT, lookupS, run1, run2], by simp⟩
      | some part =>
        obtain ⟨sub0, sup, -⟩ := selectFacts part rfl
        have sub : ∀ y ∈ part.val, ∃ x ∈ items.val, Kept members.val x.axiom ∧ y.axiom = x.axiom := by
          intro y my
          rcases sub0 y my with fresh | found
          · simp at fresh
          · exact found
        have inside : ∀ y ∈ part.val, ∃ x ∈ items.val, x.axiom = y.axiom := fun y my => by
          obtain ⟨x, mx, -, ax⟩ := sub y my
          exact ⟨x, mx, ax.symm⟩
        obtain ⟨r3, run3, consistentFacts⟩ := Rowl.DataOntology.consistent_correct.{u,v,w} part
        cases r3 with
        | none => exact ⟨none, by simp [runOpen, lookupT, lookupS, run1, run2, run3], by simp⟩
        | some b =>
          cases b with
          | false =>
            refine ⟨some false, by simp [runOpen, lookupT, lookupS, run1, run2, run3], fun answer same => ?_⟩
            simp only [Option.some.injEq] at same
            subst same
            intro Native D N V vocab keyed _ _
            simp only [Bool.false_eq_true, false_iff]
            intro whole
            have := (consistentFacts false rfl D N V vocab (keyed_inside inside keyed)).mpr
              (consistent_inside inside whole)
            cases this
          | true =>
            by_cases positive : 0 < rounds.val
            · obtain ⟨r4, run4, markFacts⟩ := mark_spec table 0#usize members done
              cases r4 with
              | none => exact ⟨none, by simp [runOpen, lookupT, lookupS, run1, run2, run3, UScalar.lt_equiv,
                  positive, run4], by simp⟩
              | some done' =>
                obtain ⟨grown, fresh⟩ := markFacts done' rfl
                obtain ⟨fewer, subRun, fewerValue⟩ := WP.spec_imp_exists
                  (Usize.sub_spec (x := rounds) (y := 1#usize) (by simp; omega))
                have fewerIs : fewer.val = rounds.val - 1 := by simp at fewerValue; omega
                obtain ⟨r, run, facts⟩ := parts_from_correct items table done' fewer tableOk
                refine ⟨r, by simp [runOpen, lookupT, lookupS, run1, run2, run3, UScalar.lt_equiv, positive, run4,
                  subRun, run], fun answer same => ?_⟩
                intro Native D N V vocab keyed itemsOk consistent
                refine facts answer same D N V vocab keyed itemsOk ?_
                have consistentPart := (consistentFacts true rfl D N V vocab (keyed_inside inside keyed)).mp rfl
                exact checked_step N vocab tableOk itemsOk closed sub sup grown
                  (fun j named mj names => fresh j named (by simp) mj names) consistentPart consistent
            · exact ⟨none, by simp [runOpen, lookupT, lookupS, run1, run2, run3, UScalar.lt_equiv, positive],
                by simp⟩
termination_by rounds.val
decreasing_by omega

/-- Consistency decided part by part: when `consistent_by_parts` answers, the
    answer is whether the closure has a model, under every datatype map that
    is the OWL 2 map on the datatypes of `datatypes` and for every vocabulary
    that names the individuals of a closure with keys. -/
theorem consistent_by_parts_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, components.consistent_by_parts items = .ok result ∧ ∀ answer, result = some answer →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        Rowl.KeyEncoding.NamesKeyed V items.val → (answer = true ↔ Consistent.{u, max w v, w} D V items.val) := by
  rw [components.consistent_by_parts]
  obtain ⟨b, runItems, itemsOk⟩ := plain_items_spec.{w} items 0#usize
  simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at itemsOk
  cases b with
  | false => exact ⟨none, by simp [runItems], by simp⟩
  | true =>
    obtain ⟨r0, run0, tableFacts⟩ := individual_table_spec items 0#usize
      (alloc.vec.Vec.new (alloc.vec.Vec Individual)) (by simp) (by simp)
    cases r0 with
    | none => exact ⟨none, by simp [runItems, run0], by simp⟩
    | some table =>
      have tableOk := table_of (tableFacts table rfl)
      obtain ⟨r1, run1, selectFacts⟩ := select_spec items table 0#usize (alloc.vec.Vec.new Individual)
        (alloc.vec.Vec.new AnnotatedAxiom) tableOk
      simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at selectFacts
      cases r1 with
      | none => exact ⟨none, by simp [runItems, run0, run1], by simp⟩
      | some tbox =>
        obtain ⟨sub0, sup, -⟩ := selectFacts tbox rfl
        have inside : ∀ y ∈ tbox.val, ∃ x ∈ items.val, x.axiom = y.axiom := fun y my => by
          rcases sub0 y my with fresh | ⟨x, mx, -, ax⟩
          · simp at fresh
          · exact ⟨x, mx, ax.symm⟩
        obtain ⟨r2, run2, consistentFacts⟩ := Rowl.DataOntology.consistent_correct.{u,v,w} tbox
        cases r2 with
        | none => exact ⟨none, by simp [runItems, run0, run1, run2], by simp⟩
        | some c =>
          cases c with
          | false =>
            refine ⟨some false, by simp [runItems, run0, run1, run2], fun answer same => ?_⟩
            simp only [Option.some.injEq] at same
            subst same
            intro Native D N V vocab keyed
            simp only [Bool.false_eq_true, false_iff]
            intro whole
            have := (consistentFacts false rfl D N V vocab (keyed_inside inside keyed)).mpr
              (consistent_inside inside whole)
            cases this
          | true =>
            obtain ⟨flags, runFlags, noTrue⟩ := falses_spec (alloc.vec.Vec.len items) (alloc.vec.Vec.new Bool)
            obtain ⟨r, run, facts⟩ := parts_from_correct.{u,v,w} items table flags (alloc.vec.Vec.len items)
              tableOk
            refine ⟨r, by simp [runItems, run0, run1, run2, runFlags, run], fun answer same => ?_⟩
            intro Native D N V vocab keyed
            refine facts answer same D N V vocab keyed (fun x mx => itemsOk rfl x mx) ?_
            have tboxConsistent := (consistentFacts true rfl D N V vocab (keyed_inside inside keyed)).mp rfl
            refine consistent_inside (fun y my => ?_) tboxConsistent
            obtain ⟨j, hy, c⟩ := mem_checked.mp my
            rcases c with ⟨na, nm⟩ | ⟨_, t⟩
            · exact sup y (List.mem_of_getElem? hy) (.inr ⟨na, nm⟩)
            · have := noTrue j t
              simp at this

/-! ## The parts of a closure, found once -/

/-- What `closure_parts` establishes of one component: its members are closed
    under the table, and its part holds copies of exactly the axioms that a
    part for them keeps. -/
def ComponentOk (items : List AnnotatedAxiom) (table : List (alloc.vec.Vec Individual))
    (c : components.Component) : Prop :=
  ClosedUnder table c.members.val ∧
    (∀ y ∈ c.part.val, ∃ x ∈ items, Kept c.members.val x.axiom ∧ y.axiom = x.axiom) ∧
    (∀ x ∈ items, Kept c.members.val x.axiom → ∃ y ∈ c.part.val, y.axiom = x.axiom)

/-- `components_from` adds components that are closed with their parts, and
    every assertion that is done, or that it finds, names a member of one. -/
theorem components_from_spec (items : alloc.vec.Vec AnnotatedAxiom)
    (table : alloc.vec.Vec (alloc.vec.Vec Individual)) (done : alloc.vec.Vec Bool) (rounds : Usize)
    (out : alloc.vec.Vec components.Component) (tableOk : TableOf items.val table.val)
    (outOk : ∀ c ∈ out.val, ComponentOk items.val table.val c)
    (doneIn : ∀ (j : Nat), done.val[j]? = some true →
      ∃ c ∈ out.val, ∃ named, table.val[j]? = some named ∧ Names named c.members.val) :
    ∃ r, components.components_from items table done rounds out = .ok r ∧ ∀ v, r = some v →
      (∀ c ∈ v.val, ComponentOk items.val table.val c) ∧
      (∀ (j : Nat) named, table.val[j]? = some named → named.val ≠ [] →
        ∃ c ∈ v.val, Names named c.members.val) := by
  rw [components.components_from]
  obtain ⟨o, runOpen, noneFacts, someFacts⟩ := open_from_spec table 0#usize done
  cases o with
  | none =>
    refine ⟨some out, by simp [runOpen], fun v same => ?_⟩
    simp only [Option.some.injEq] at same
    subst same
    refine ⟨outOk, fun j named mj ne => ?_⟩
    obtain ⟨c, mc, named', mj', names⟩ := doneIn j (noneFacts rfl j named (by simp) mj ne)
    rw [mj] at mj'
    simp only [Option.some.injEq] at mj'
    rw [mj']
    exact ⟨c, mc, names⟩
  | some opened =>
    by_cases positive : 0 < rounds.val
    · obtain ⟨named, atOpen, nonempty⟩ := someFacts opened rfl
      have pos : 0 < named.val.length := List.length_pos_of_ne_nil nonempty
      have lookupT : table.index_usize opened = .ok named := by
        simp [alloc.vec.Vec.index_usize, atOpen]
      have lookupS : named.index_usize 0#usize = .ok named.val[0] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem pos]
      obtain ⟨r1, run1, memberFacts⟩ := members_of_spec table named.val[0]
      cases r1 with
      | none => exact ⟨none, by simp [runOpen, UScalar.lt_equiv, positive, lookupT, lookupS, run1], by simp⟩
      | some members =>
        obtain ⟨-, closed⟩ := memberFacts members rfl
        obtain ⟨r2, run2, selectFacts⟩ := select_spec items table 0#usize members
          (alloc.vec.Vec.new AnnotatedAxiom) tableOk
        simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at selectFacts
        cases r2 with
        | none => exact ⟨none, by simp [runOpen, UScalar.lt_equiv, positive, lookupT, lookupS, run1, run2],
            by simp⟩
        | some part =>
          obtain ⟨sub0, sup, -⟩ := selectFacts part rfl
          have sub : ∀ y ∈ part.val, ∃ x ∈ items.val, Kept members.val x.axiom ∧ y.axiom = x.axiom := by
            intro y my
            rcases sub0 y my with fresh | found
            · simp at fresh
            · exact found
          obtain ⟨r3, run3, markFacts⟩ := mark_spec table 0#usize members done
          cases r3 with
          | none => exact ⟨none, by simp [runOpen, UScalar.lt_equiv, positive, lookupT, lookupS, run1, run2,
              run3], by simp⟩
          | some done' =>
            obtain ⟨grown, -⟩ := markFacts done' rfl
            by_cases room : out.val.length < Usize.max
            · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out
                ({ members := members, part := part } : components.Component) room)
              obtain ⟨fewer, subRun, fewerValue⟩ := WP.spec_imp_exists
                (Usize.sub_spec (x := rounds) (y := 1#usize) (by simp; omega))
              have fewerIs : fewer.val = rounds.val - 1 := by simp at fewerValue; omega
              have componentOk : ComponentOk items.val table.val
                  ({ members := members, part := part } : components.Component) := ⟨closed, sub, sup⟩
              obtain ⟨r, run, facts⟩ := components_from_spec items table done' fewer pushed tableOk
                (fun c mc => by
                  rw [contents] at mc
                  rcases List.mem_append.mp mc with old | new
                  · exact outOk c old
                  · simp only [List.mem_singleton] at new
                    rw [new]
                    exact componentOk)
                (fun j t => by
                  rcases grown j t with old | ⟨named', atJ, names⟩
                  · obtain ⟨c, mc, rest⟩ := doneIn j old
                    exact ⟨c, by rw [contents]; exact List.mem_append_left _ mc, rest⟩
                  · exact ⟨({ members := members, part := part } : components.Component),
                      by rw [contents]; simp, named', atJ, names⟩)
              exact ⟨r, by simp [runOpen, UScalar.lt_equiv, positive, lookupT, lookupS, run1, run2, run3,
                alloc.vec.Vec.len_val, usize_max_val, room, push, subRun, run], facts⟩
            · exact ⟨none, by simp [runOpen, UScalar.lt_equiv, positive, lookupT, lookupS, run1, run2, run3,
                alloc.vec.Vec.len_val, usize_max_val, room], by simp⟩
    · exact ⟨none, by simp [runOpen, UScalar.lt_equiv, positive], by simp⟩
termination_by rounds.val
decreasing_by omega

/-- `closure_parts` checks the closure and, when it answers, returns its axioms
    other than assertions and its components with their parts: the part of a
    component meets the conditions of `instance_part` for each member, and the
    axioms other than assertions meet them for an individual that no
    component holds. -/
theorem closure_parts_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ r, components.closure_parts items = .ok r ∧ ∀ parts, r = some parts →
      (∀ x ∈ items.val, ItemOk.{w} x) ∧
      (∀ c ∈ parts.components.val, ∀ a, Individual.Named a ∈ c.members.val →
        PartFor items.val c.part.val a) ∧
      (∀ a, (∀ c ∈ parts.components.val, Individual.Named a ∉ c.members.val) →
        PartFor items.val parts.tbox.val a) := by
  rw [components.closure_parts]
  obtain ⟨b, runItems, itemsOk⟩ := plain_items_spec.{w} items 0#usize
  simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at itemsOk
  cases b with
  | false => exact ⟨none, by simp [runItems], by simp⟩
  | true =>
    obtain ⟨r0, run0, tableFacts⟩ := individual_table_spec items 0#usize
      (alloc.vec.Vec.new (alloc.vec.Vec Individual)) (by simp) (by simp)
    cases r0 with
    | none => exact ⟨none, by simp [runItems, run0], by simp⟩
    | some table =>
      have tableOk := table_of (tableFacts table rfl)
      obtain ⟨r1, run1, selectFacts⟩ := select_spec items table 0#usize (alloc.vec.Vec.new Individual)
        (alloc.vec.Vec.new AnnotatedAxiom) tableOk
      simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at selectFacts
      cases r1 with
      | none => exact ⟨none, by simp [runItems, run0, run1], by simp⟩
      | some tbox =>
        obtain ⟨sub0, sup, -⟩ := selectFacts tbox rfl
        have empty : (alloc.vec.Vec.new Individual).val = [] := rfl
        rw [empty] at sub0 sup
        have sub : ∀ y ∈ tbox.val, ∃ x ∈ items.val, Kept [] x.axiom ∧ y.axiom = x.axiom := by
          intro y my
          rcases sub0 y my with fresh | found
          · simp at fresh
          · exact found
        obtain ⟨flags, runFlags, noTrue⟩ := falses_spec (alloc.vec.Vec.len items) (alloc.vec.Vec.new Bool)
        obtain ⟨r2, run2, facts⟩ := components_from_spec items table flags (alloc.vec.Vec.len items)
          (alloc.vec.Vec.new components.Component) tableOk (fun c mc => by simp at mc)
          (fun j t => by have := noTrue j t; simp at this)
        cases r2 with
        | none => exact ⟨none, by simp [runItems, run0, run1, runFlags, run2], by simp⟩
        | some found =>
          obtain ⟨foundOk, covered⟩ := facts found rfl
          refine ⟨some ⟨tbox, found⟩, by simp [runItems, run0, run1, runFlags, run2], fun parts same => ?_⟩
          simp only [Option.some.injEq] at same
          subst same
          refine ⟨itemsOk rfl, fun c mc a inMembers => ?_, fun a absentAll => ?_⟩
          · obtain ⟨closed, subC, supC⟩ := foundOk c mc
            exact part_for_closed tableOk closed inMembers subC supC
          · refine part_for_absent sub sup (fun x mx assertion mi => ?_)
            obtain ⟨j, hj, same⟩ := List.getElem_of_mem mx
            have hx : items.val[j]? = some x := by rw [List.getElem?_eq_getElem hj, same]
            obtain ⟨named, atJ, entry⟩ := entry_of_get tableOk hx
            obtain ⟨i, mi'⟩ := assertion_names assertion
            have nonempty : named.val ≠ [] := by
              intro emptyEntry
              have := (entry.1 assertion i).mpr mi'
              rw [emptyEntry] at this
              cases this
            obtain ⟨c, mc, names⟩ := covered j named atJ nonempty
            obtain ⟨closed, -, -⟩ := foundOk c mc
            exact absentAll c mc (closed named (List.mem_of_getElem? atJ) names _
              ((entry.1 assertion _).mpr mi))

/-- When `closure_parts` returns the parts of a closure that has a model, an
    instance question with a class expression that `plain_question` accepts
    has the same answer for the part of the component of the individual as
    for the closure, and for the axioms other than assertions when no
    component holds the individual, under every datatype map that is the OWL 2
    map on the datatypes of `datatypes` and for every vocabulary. -/
theorem parts_instance_correct {items : alloc.vec.Vec AnnotatedAxiom} {parts : components.Parts}
    {e : ClassExpression} (split : components.closure_parts items = .ok (some parts))
    (question : components.plain_question e = .ok true)
    {Native : Type w} (D : DatatypeMap Native) (N : Normative D) (V : Vocabulary) (vocab : IsVocabulary D V)
    (consistent : Consistent.{u,v,w} D V items.val) (a : NamedIndividual) :
    (∀ c ∈ parts.components.val, Individual.Named a ∈ c.members.val →
      (InstanceOf.{u,v,w} D V items.val a e ↔ InstanceOf.{u,v,w} D V c.part.val a e)) ∧
    ((∀ c ∈ parts.components.val, Individual.Named a ∉ c.members.val) →
      (InstanceOf.{u,v,w} D V items.val a e ↔ InstanceOf.{u,v,w} D V parts.tbox.val a e)) := by
  obtain ⟨r, run, facts⟩ := closure_parts_correct.{w} items
  rw [split] at run
  simp only [Result.ok.injEq] at run
  obtain ⟨itemsOk, inComponent, inNone⟩ := facts parts run.symm
  obtain ⟨b, runQ, closedQ⟩ := plain_question_spec.{w} e
  rw [question] at runQ
  simp only [Result.ok.injEq] at runQ
  subst runQ
  refine ⟨fun c mc inMembers => ?_, fun absent => ?_⟩
  · obtain ⟨rest, cover, inside, kinds, apart, aApart⟩ := inComponent c mc a inMembers
    exact instance_part vocab cover inside (fun x mx na => (itemsOk x mx D N V vocab).2 na)
      (fun x mx ia => (itemsOk x mx D N V vocab).1 ia) kinds apart aApart (closedQ rfl D N V vocab) consistent
  · obtain ⟨rest, cover, inside, kinds, apart, aApart⟩ := inNone a absent
    exact instance_part vocab cover inside (fun x mx na => (itemsOk x mx D N V vocab).2 na)
      (fun x mx ia => (itemsOk x mx D N V vocab).1 ia) kinds apart aApart (closedQ rfl D N V vocab) consistent

end Rowl.Components
