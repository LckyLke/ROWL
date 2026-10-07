import Rowl.Concepts

/-!
# Copies of syntax

The kernel copies the parts of axioms with the `components::copy_*`
functions, which the part of a closure for one individual (`Rowl.Components`)
and the unfolding of datatype definitions (`Rowl.Unfolding`) use. Each copy
is the value it copies: `copy_range_eq`, `copy_class_eq`, and `copy_axiom_spec`
for whole axioms, which have no copy when they are declarations, annotation
axioms or datatype definitions.
-/

namespace Rowl.Copies
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model Rowl.Owl
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

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

private theorem members_bound (xs : AtLeastTwo α) (e : α) (h : e ∈ xs.elements) :
    sizeOf e < 1 + sizeOf xs := by
  have := elements_size xs h
  omega

end Sizes

theorem copy_natural_eq (n : probes.Natural) : components.copy_natural n = .ok n := by
  induction n with
  | Zero => rw [components.copy_natural]
  | Succ inner ih => rw [components.copy_natural]; simp [ih]

theorem copy_class_name_eq (c : Class) : components.copy_class_name c = .ok c := by
  cases c; simp [components.copy_class_name, Rowl.Nnf.copy_iri_identity]

theorem copy_datatype_eq (dt : Datatype) : components.copy_datatype dt = .ok dt := by
  cases dt; simp [components.copy_datatype, Rowl.Nnf.copy_iri_identity]

theorem copy_data_property_eq (p : DataProperty) : components.copy_data_property p = .ok p := by
  cases p; simp [components.copy_data_property, Rowl.Nnf.copy_iri_identity]

theorem copy_literal_eq (lt : Literal) : components.copy_literal lt = .ok lt := by
  cases lt; simp [components.copy_literal, Rowl.Nnf.copy_bytes_identity, copy_datatype_eq]

theorem copy_facet_eq (f : FacetRestriction) : components.copy_facet f = .ok f := by
  cases f; simp [components.copy_facet, Rowl.Nnf.copy_iri_identity, copy_literal_eq]

theorem copy_literals_spec (literals : alloc.vec.Vec Literal) (index : Usize) (out : alloc.vec.Vec Literal)
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

theorem copy_literals_eq (literals : alloc.vec.Vec Literal) : components.copy_literals literals 0#usize (alloc.vec.Vec.new Literal) = .ok literals := by
  obtain ⟨v, run, value⟩ := copy_literals_spec literals 0#usize (alloc.vec.Vec.new Literal) (by simp)
  have same : v = _ := (alloc.vec.Vec.eq_iff _ _).mpr (by simpa using value)
  rw [run, same]

theorem copy_facets_spec (facets : alloc.vec.Vec FacetRestriction) (index : Usize) (out : alloc.vec.Vec FacetRestriction)
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

theorem copy_facets_eq (facets : alloc.vec.Vec FacetRestriction) : components.copy_facets facets 0#usize (alloc.vec.Vec.new FacetRestriction) = .ok facets := by
  obtain ⟨v, run, value⟩ := copy_facets_spec facets 0#usize (alloc.vec.Vec.new FacetRestriction) (by simp)
  have same : v = _ := (alloc.vec.Vec.eq_iff _ _).mpr (by simpa using value)
  rw [run, same]

theorem copy_individuals_spec (individuals : alloc.vec.Vec Individual) (index : Usize) (out : alloc.vec.Vec Individual)
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

theorem copy_individuals_eq (individuals : alloc.vec.Vec Individual) : components.copy_individuals individuals 0#usize (alloc.vec.Vec.new Individual) = .ok individuals := by
  obtain ⟨v, run, value⟩ := copy_individuals_spec individuals 0#usize (alloc.vec.Vec.new Individual) (by simp)
  have same : v = _ := (alloc.vec.Vec.eq_iff _ _).mpr (by simpa using value)
  rw [run, same]

theorem copy_roles_spec (roles : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) (out : alloc.vec.Vec ObjectPropertyExpression)
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

theorem copy_roles_eq (roles : alloc.vec.Vec ObjectPropertyExpression) : components.copy_roles roles 0#usize (alloc.vec.Vec.new ObjectPropertyExpression) = .ok roles := by
  obtain ⟨v, run, value⟩ := copy_roles_spec roles 0#usize (alloc.vec.Vec.new ObjectPropertyExpression) (by simp)
  have same : v = _ := (alloc.vec.Vec.eq_iff _ _).mpr (by simpa using value)
  rw [run, same]

theorem copy_data_list_spec (properties : alloc.vec.Vec DataProperty) (index : Usize) (out : alloc.vec.Vec DataProperty)
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

theorem copy_data_list_eq (properties : alloc.vec.Vec DataProperty) : components.copy_data_list properties 0#usize (alloc.vec.Vec.new DataProperty) = .ok properties := by
  obtain ⟨v, run, value⟩ := copy_data_list_spec properties 0#usize (alloc.vec.Vec.new DataProperty) (by simp)
  have same : v = _ := (alloc.vec.Vec.eq_iff _ _).mpr (by simpa using value)
  rw [run, same]

theorem copy_role_members_eq (roles : AtLeastTwo ObjectPropertyExpression) :
    components.copy_role_members roles = .ok roles := by
  cases roles; simp [components.copy_role_members, Rowl.Concepts.copy_role_identity, copy_roles_eq]

theorem copy_data_members_eq (properties : AtLeastTwo DataProperty) :
    components.copy_data_members properties = .ok properties := by
  cases properties; simp [components.copy_data_members, copy_data_property_eq, copy_data_list_eq]

theorem copy_individual_members_eq (individuals : AtLeastTwo Individual) :
    components.copy_individual_members individuals = .ok individuals := by
  cases individuals; simp [components.copy_individual_members, Rowl.Concepts.copy_individual_identity,
    copy_individuals_eq]

theorem copy_sub_role_eq (sub : SubObjectPropertyExpression) : components.copy_sub_role sub = .ok sub := by
  cases sub <;> simp [components.copy_sub_role, Rowl.Concepts.copy_role_identity, copy_role_members_eq]

theorem copy_range_list_spec (ranges : alloc.vec.Vec DataRange) (index : Usize) (out : alloc.vec.Vec DataRange)
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

theorem copy_range_members_eq (members : AtLeastTwo DataRange)
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

theorem copy_range_filler_eq (filler : Option DataRange) : components.copy_range_filler filler = .ok filler := by
  cases filler <;> simp [components.copy_range_filler, copy_range_eq]

theorem copy_class_list_spec (classes : alloc.vec.Vec ClassExpression) (index : Usize)
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

theorem copy_class_members_eq (members : AtLeastTwo ClassExpression)
    (each : ∀ c ∈ members.elements, components.copy_class c = .ok c) :
    components.copy_class_members members = .ok members := by
  obtain ⟨v, run, value⟩ := copy_class_list_spec members.rest 0#usize (alloc.vec.Vec.new ClassExpression)
    (by simp) (fun c member => each c (by simp [AtLeastTwo.elements, member]))
  have restEq : v = members.rest := (alloc.vec.Vec.eq_iff _ _).mpr (by simpa using value)
  rw [components.copy_class_members]
  simp only [each members.first (by simp [AtLeastTwo.elements]), each members.second (by simp [AtLeastTwo.elements]),
    bind_ok, run, restEq]

theorem copy_class_filler_eq (filler : Option ClassExpression)
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

theorem copy_range_members_full (members : AtLeastTwo DataRange) : components.copy_range_members members = .ok members :=
  copy_range_members_eq members (fun r _ => copy_range_eq r)

theorem copy_class_members_full (members : AtLeastTwo ClassExpression) :
    components.copy_class_members members = .ok members :=
  copy_class_members_eq members (fun c _ => copy_class_eq c)

end Rowl.Copies
