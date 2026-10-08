import Rowl.DataMeaning

/-!
What the axioms of `data_ontology`'s encoding mean. Each axiom of a closure
becomes axioms on classes, object properties and individuals, together with
the assertions that the individuals it names are no data nodes
(`encode_axiom_meaning`). Under a correspondence between an OWL interpretation
and an interpretation of the encoding (`Simulates`) that also places the
values of the data properties at data nodes (`Placed`), the OWL interpretation
satisfies the axiom when the encoding's interpretation satisfies what it
becomes, and conversely when the data nodes keep apart from the names and every
data property's neighbour stands for a value (`Inert`), as in an interpretation
of the encoding made from an OWL model.
-/
namespace Rowl.DataAxioms
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.AlcOntology (RoleOf)
open Rowl.DataEncoding
open Rowl.DataMeaning
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe u v w x

variable {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-! ### Assertions that individuals are no data nodes -/

/-- The assertions that the individuals are no data nodes. -/
noncomputable def objectFacts (individuals : List Individual) : List AnnotatedAxiom :=
  individuals.map (fun a => ⟨alloc.vec.Vec.new Annotation, .ClassAssertion (.ObjectComplementOf (.Class dataClass)) a⟩)

theorem object_facts_hold (J : Interpretation Object' Value') (individuals : List Individual) :
    (∀ b ∈ objectFacts individuals, satisfies J b.axiom) ↔
      ∀ a ∈ individuals, ¬ J.classes dataClass (individual J a) := by
  simp [objectFacts, satisfies, classDenote]

theorem object_facts_append (xs ys : List Individual) : objectFacts (xs ++ ys) = objectFacts xs ++ objectFacts ys := by
  simp [objectFacts]

theorem push_spec (out : alloc.vec.Vec AnnotatedAxiom) (ax : Axiom) :
    ∃ res, data_ontology.push out ax = .ok res ∧
      ∀ out', res = some out' → out'.val = out.val ++ [⟨alloc.vec.Vec.new Annotation, ax⟩] := by
  rw [data_ontology.push]
  by_cases room : out.val.length < Usize.max
  · have room' : alloc.vec.Vec.len out < core.num.Usize.MAX := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out
      ({ annotations := alloc.vec.Vec.new Annotation, «axiom» := ax } : AnnotatedAxiom) room)
    exact ⟨some pushed, by simp [room', push], fun out' h => by cases h; exact contents⟩
  · have full : ¬ alloc.vec.Vec.len out < core.num.Usize.MAX := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
    exact ⟨none, by simp [full], by simp⟩

theorem object_assertion_spec (a : Individual) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.object_assertion a out = .ok res ∧
      ∀ out', res = some out' → out'.val = out.val ++ objectFacts [a] ∧ Plain a := by
  rw [data_ontology.object_assertion]
  obtain ⟨res, run, _⟩ := object_individual_of_correct a
  cases res with
  | none => exact ⟨none, by simp [run], by simp⟩
  | some a' =>
    have same := object_individual_of_some run
    obtain ⟨pushed, pushRun, contents⟩ := push_spec out (.ClassAssertion (.ObjectComplementOf (.Class dataClass)) a')
    refine ⟨pushed, by simp [run, object_class_eq, pushRun], fun out' h => ?_⟩
    rw [contents out' h, same.1]
    exact ⟨by simp [objectFacts], same.2⟩

theorem object_assertions_spec (individuals : alloc.vec.Vec Individual) (index : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.object_assertions individuals index out = .ok res ∧
      ∀ out', res = some out' → out'.val = out.val ++ objectFacts (individuals.val.drop index.val) ∧
        ∀ a ∈ individuals.val.drop index.val, Plain a := by
  rw [data_ontology.object_assertions]
  by_cases inside : index.val < individuals.val.length
  · have lookup : individuals.index_usize index = .ok individuals.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨res, run, facts⟩ := object_assertion_spec individuals.val[index.val] out
    cases res with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
    | some out1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := object_assertions_spec individuals next out1
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance,
        restRun], fun out' h => ?_⟩
      obtain ⟨contents, plain⟩ := restFacts out' h
      obtain ⟨contents1, plain1⟩ := facts out1 rfl
      rw [nextIndex] at contents plain
      refine ⟨by rw [contents, contents1, split]; simp only [objectFacts, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append], ?_⟩
      rw [split]
      intro a mem
      rcases List.mem_cons.mp mem with rfl | later
      · exact plain1
      · exact plain a later
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ?_⟩
    cases h
    simp [List.drop_eq_nil_iff.mpr (show individuals.val.length ≤ index.val by omega), objectFacts]
termination_by individuals.val.length - index.val
decreasing_by omega

/-- What the assertions about the individuals of a class expression add. -/
def NominalsAdd (c : ClassExpression) (out out' : alloc.vec.Vec AnnotatedAxiom) : Prop :=
  out'.val = out.val ++ objectFacts (classIndividuals c) ∧ ∀ a ∈ classIndividuals c, Plain a

theorem nominal_list_spec (classes : alloc.vec.Vec ClassExpression) (index : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom)
    (each : ∀ e ∈ classes.val, ∀ out, ∃ res, data_ontology.nominal_objects e out = .ok res ∧
      ∀ out', res = some out' → NominalsAdd e out out') :
    ∃ res, data_ontology.nominal_list classes index out = .ok res ∧
      ∀ out', res = some out' → out'.val = out.val ++ objectFacts ((classes.val.drop index.val).flatMap classIndividuals) ∧
        ∀ a ∈ (classes.val.drop index.val).flatMap classIndividuals, Plain a := by
  rw [data_ontology.nominal_list]
  by_cases inside : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨res, run, facts⟩ := each _ (List.getElem_mem inside) out
    cases res with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
    | some out1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := nominal_list_spec classes next out1 each
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance,
        restRun], fun out' h => ?_⟩
      obtain ⟨contents, plain⟩ := restFacts out' h
      obtain ⟨contents1, plain1⟩ := facts out1 rfl
      rw [nextIndex] at contents plain
      refine ⟨by rw [contents, contents1, split]; simp only [objectFacts, List.flatMap_cons, List.map_append,
        List.append_assoc], ?_⟩
      rw [split]
      intro a mem
      rcases List.mem_append.mp (List.flatMap_cons ▸ mem) with early | later
      · exact plain1 a early
      · exact plain a later
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ?_⟩
    cases h
    simp [List.drop_eq_nil_iff.mpr (show classes.val.length ≤ index.val by omega), objectFacts]
termination_by classes.val.length - index.val
decreasing_by omega

theorem nominal_members_spec (members : AtLeastTwo ClassExpression) (out : alloc.vec.Vec AnnotatedAxiom)
    (each : ∀ e ∈ members.elements, ∀ out, ∃ res, data_ontology.nominal_objects e out = .ok res ∧
      ∀ out', res = some out' → NominalsAdd e out out') :
    ∃ res, data_ontology.nominal_members members out = .ok res ∧
      ∀ out', res = some out' → out'.val = out.val ++ objectFacts (members.elements.flatMap classIndividuals) ∧
        ∀ a ∈ members.elements.flatMap classIndividuals, Plain a := by
  rw [data_ontology.nominal_members]
  obtain ⟨r1, run1, facts1⟩ := each members.first (by simp [AtLeastTwo.elements]) out
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some out1 =>
    obtain ⟨r2, run2, facts2⟩ := each members.second (by simp [AtLeastTwo.elements]) out1
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some out2 =>
      obtain ⟨r3, run3, facts3⟩ := nominal_list_spec members.rest 0#usize out2
        (fun e mem => each e (by simp [AtLeastTwo.elements, mem]))
      refine ⟨r3, by simp [run1, run2, run3], fun out' h => ?_⟩
      obtain ⟨contents3, plain3⟩ := facts3 out' h
      obtain ⟨contents1, plain1⟩ := facts1 out1 rfl
      obtain ⟨contents2, plain2⟩ := facts2 out2 rfl
      simp only [zero_val, List.drop_zero] at contents3 plain3
      refine ⟨by rw [contents3, contents2, contents1]; simp [AtLeastTwo.elements, objectFacts], ?_⟩
      intro a mem
      simp only [AtLeastTwo.elements, List.flatMap_cons, List.mem_append] at mem
      rcases mem with early | middle | later
      · exact plain1 a early
      · exact plain2 a middle
      · exact plain3 a later

theorem nominal_objects_spec (c : ClassExpression) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.nominal_objects c out = .ok res ∧ ∀ out', res = some out' → NominalsAdd c out out' := by
  have bound : ∀ (xs : AtLeastTwo ClassExpression), ∀ e ∈ xs.elements, sizeOf e < 1 + sizeOf xs := by
    intro xs e mem
    simp only [AtLeastTwo.elements, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · have := first_size xs; omega
    · have := second_size xs; omega
    · have := member_size xs e mem; omega
  have members : ∀ (xs : AtLeastTwo ClassExpression), (∀ e ∈ xs.elements, sizeOf e < sizeOf c) →
      classIndividuals (.ObjectIntersectionOf xs) = xs.elements.flatMap classIndividuals ∧
      classIndividuals (.ObjectUnionOf xs) = xs.elements.flatMap classIndividuals := by
    intro xs _
    rw [classIndividuals, classIndividuals]
    simp [AtLeastTwo.elements]
  cases h : c with
  | ObjectIntersectionOf xs =>
    rw [data_ontology.nominal_objects]
    obtain ⟨res, run, facts⟩ := nominal_members_spec xs out (fun e mem out => by
      have := bound xs e mem
      exact nominal_objects_spec e out)
    refine ⟨res, run, fun out' hr => ?_⟩
    rw [NominalsAdd, (members xs (fun e mem => by have := bound xs e mem; rw [h]; simp; omega)).1]
    exact facts out' hr
  | ObjectUnionOf xs =>
    rw [data_ontology.nominal_objects]
    obtain ⟨res, run, facts⟩ := nominal_members_spec xs out (fun e mem out => by
      have := bound xs e mem
      exact nominal_objects_spec e out)
    refine ⟨res, run, fun out' hr => ?_⟩
    rw [NominalsAdd, (members xs (fun e mem => by have := bound xs e mem; rw [h]; simp; omega)).2]
    exact facts out' hr
  | ObjectComplementOf inner =>
    rw [data_ontology.nominal_objects]
    have : sizeOf inner < sizeOf c := by rw [h]; simp
    obtain ⟨res, run, facts⟩ := nominal_objects_spec inner out
    refine ⟨res, run, fun out' hr => ?_⟩
    rw [NominalsAdd, classIndividuals]
    exact facts out' hr
  | ObjectOneOf xs =>
    rw [data_ontology.nominal_objects]
    obtain ⟨r1, run1, facts1⟩ := object_assertion_spec xs.first out
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some out1 =>
      obtain ⟨r2, run2, facts2⟩ := object_assertions_spec xs.rest 0#usize out1
      refine ⟨r2, by simp [run1, run2], fun out' hr => ?_⟩
      obtain ⟨contents2, plain2⟩ := facts2 out' hr
      obtain ⟨contents1, plain1⟩ := facts1 out1 rfl
      simp only [zero_val, List.drop_zero] at contents2 plain2
      rw [NominalsAdd, classIndividuals]
      refine ⟨by rw [contents2, contents1]; simp [NonEmpty.elements, objectFacts], ?_⟩
      intro a mem
      simp only [NonEmpty.elements, List.mem_cons] at mem
      rcases mem with rfl | later
      · exact plain1
      · exact plain2 a later
  | ObjectSomeValuesFrom _ filler =>
    rw [data_ontology.nominal_objects]
    have : sizeOf filler < sizeOf c := by rw [h]; simp
    obtain ⟨res, run, facts⟩ := nominal_objects_spec filler out
    refine ⟨res, run, fun out' hr => ?_⟩
    rw [NominalsAdd, classIndividuals]
    exact facts out' hr
  | ObjectAllValuesFrom _ filler =>
    rw [data_ontology.nominal_objects]
    have : sizeOf filler < sizeOf c := by rw [h]; simp
    obtain ⟨res, run, facts⟩ := nominal_objects_spec filler out
    refine ⟨res, run, fun out' hr => ?_⟩
    rw [NominalsAdd, classIndividuals]
    exact facts out' hr
  | ObjectHasValue _ a =>
    rw [data_ontology.nominal_objects]
    obtain ⟨res, run, facts⟩ := object_assertion_spec a out
    refine ⟨res, run, fun out' hr => ?_⟩
    rw [NominalsAdd, classIndividuals]
    obtain ⟨contents, plain⟩ := facts out' hr
    exact ⟨contents, by simpa using plain⟩
  | ObjectMinCardinality _ _ filler | ObjectMaxCardinality _ _ filler | ObjectExactCardinality _ _ filler =>
    cases hf : filler with
    | none =>
      rw [data_ontology.nominal_objects]
      exact ⟨some out, rfl, fun out' hr => by cases hr; simp [NominalsAdd, classIndividuals, objectFacts]⟩
    | some e =>
      rw [data_ontology.nominal_objects]
      have : sizeOf e < sizeOf c := by rw [h, hf]; simp; omega
      obtain ⟨res, run, facts⟩ := nominal_objects_spec e out
      refine ⟨res, run, fun out' hr => ?_⟩
      rw [NominalsAdd, classIndividuals]
      exact facts out' hr
  | Class _ | ObjectHasSelf _ | DataSomeValuesFrom _ _ | DataAllValuesFrom _ _ | DataHasValue _ _
  | DataMinCardinality _ _ _ | DataMaxCardinality _ _ _ | DataExactCardinality _ _ _ =>
    rw [data_ontology.nominal_objects.eq_def]
    exact ⟨some out, rfl, fun out' hr => by cases hr; simp [NominalsAdd, classIndividuals, objectFacts]⟩
termination_by sizeOf c
decreasing_by all_goals (subst_vars; first | omega | (simp_wf; omega))

theorem member_objects_spec (xs : AtLeastTwo Individual) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.member_objects xs out = .ok res ∧
      ∀ out', res = some out' → out'.val = out.val ++ objectFacts xs.elements ∧ ∀ a ∈ xs.elements, Plain a := by
  rw [data_ontology.member_objects]
  obtain ⟨r1, run1, facts1⟩ := object_assertion_spec xs.first out
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some out1 =>
    obtain ⟨r2, run2, facts2⟩ := object_assertion_spec xs.second out1
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some out2 =>
      obtain ⟨r3, run3, facts3⟩ := object_assertions_spec xs.rest 0#usize out2
      refine ⟨r3, by simp [run1, run2, run3], fun out' h => ?_⟩
      obtain ⟨contents3, plain3⟩ := facts3 out' h
      obtain ⟨contents1, plain1⟩ := facts1 out1 rfl
      obtain ⟨contents2, plain2⟩ := facts2 out2 rfl
      simp only [zero_val, List.drop_zero] at contents3 plain3
      refine ⟨by rw [contents3, contents2, contents1]; simp [AtLeastTwo.elements, objectFacts], ?_⟩
      intro a mem
      simp only [AtLeastTwo.elements, List.mem_cons] at mem
      rcases mem with rfl | rfl | later
      · exact plain1
      · exact plain2
      · exact plain3 a later

theorem with_nominals_spec (out : alloc.vec.Vec AnnotatedAxiom) (ax : Axiom) (members : AtLeastTwo ClassExpression) :
    ∃ res, data_ontology.with_nominals out ax members = .ok res ∧
      ∀ out', res = some out' → out'.val = out.val ++ [⟨alloc.vec.Vec.new Annotation, ax⟩] ++
        objectFacts (members.elements.flatMap classIndividuals) ∧ ∀ a ∈ members.elements.flatMap classIndividuals, Plain a := by
  rw [data_ontology.with_nominals]
  obtain ⟨r1, run1, contents1⟩ := push_spec out ax
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some out1 =>
    obtain ⟨r2, run2, facts2⟩ := nominal_members_spec members out1
      (fun e _ out => nominal_objects_spec e out)
    refine ⟨r2, by simp [run1, run2], fun out' h => ?_⟩
    obtain ⟨contents2, plain2⟩ := facts2 out' h
    exact ⟨by rw [contents2, contents1 out1 rfl], plain2⟩

/-! ### Copies of roles and individuals -/

/-- A role the encoding copies: not the encoding's, and the universal role or
    one of the context. -/
def RoleIn (context : data_ontology.Context) (r : ObjectPropertyExpression) : Prop :=
  ¬ Reserved (RoleOf r).iri.spelling.val ∧ (RoleOf r = topObject ∨ RoleOf r ∈ context.roles.val)

theorem object_roles_from_spec (context : data_ontology.Context) (roles : alloc.vec.Vec ObjectPropertyExpression)
    (index : Usize) (out : alloc.vec.Vec ObjectPropertyExpression)
    (room : out.val.length + (roles.val.length - index.val) ≤ Usize.max) :
    ∃ res, data_ontology.object_roles_from context roles index out = .ok res ∧
      ∀ v, res = some v → v.val = out.val ++ roles.val.drop index.val ∧
        ∀ r ∈ roles.val.drop index.val, RoleIn context r := by
  rw [data_ontology.object_roles_from]
  by_cases inside : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨res, run, facts⟩ := object_role_correct context roles.val[index.val]
    cases res with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
    | some copy =>
      obtain ⟨same, plain, inContext⟩ := facts copy rfl
      have short : out.val.length < Usize.max := by omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out copy short)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := object_roles_from_spec context roles next pushed
        (by rw [contents, nextIndex]; simp; omega)
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, push,
        advance, restRun], fun v hv => ?_⟩
      obtain ⟨value, inside'⟩ := restFacts v hv
      rw [nextIndex] at value inside'
      refine ⟨by rw [value, contents, split, same]; simp, ?_⟩
      rw [split]
      intro r mem
      rcases List.mem_cons.mp mem with rfl | later
      · exact ⟨plain, inContext⟩
      · exact inside' r later
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun v hv => ?_⟩
    cases hv
    simp [List.drop_eq_nil_iff.mpr (show roles.val.length ≤ index.val by omega)]
termination_by roles.val.length - index.val
decreasing_by omega

theorem object_members_spec (context : data_ontology.Context) (roles : AtLeastTwo ObjectPropertyExpression) :
    ∃ res, data_ontology.object_members context roles = .ok res ∧
      ∀ roles', res = some roles' → roles' = roles ∧ ∀ r ∈ roles.elements, RoleIn context r := by
  rw [data_ontology.object_members]
  obtain ⟨r1, run1, facts1⟩ := object_role_correct context roles.first
  obtain ⟨r2, run2, facts2⟩ := object_role_correct context roles.second
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some first =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some second =>
      obtain ⟨r3, run3, facts3⟩ := object_roles_from_spec context roles.rest 0#usize
        (alloc.vec.Vec.new ObjectPropertyExpression) (by simp [new_val])
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
      | some rest =>
        refine ⟨some ⟨first, second, rest⟩, by simp [run1, run2, run3], fun roles' h => ?_⟩
        cases h
        obtain ⟨same1, plain1, in1⟩ := facts1 first rfl
        obtain ⟨same2, plain2, in2⟩ := facts2 second rfl
        obtain ⟨value3, in3⟩ := facts3 rest rfl
        simp only [new_val, List.nil_append, zero_val, List.drop_zero] at value3 in3
        refine ⟨?_, ?_⟩
        · cases roles; simp only [AtLeastTwo.mk.injEq]
          exact ⟨same1, same2, by simpa [alloc.vec.Vec.eq_iff] using value3⟩
        · intro r mem
          simp only [AtLeastTwo.elements, List.mem_cons] at mem
          rcases mem with rfl | rfl | later
          · exact ⟨plain1, in1⟩
          · exact ⟨plain2, in2⟩
          · exact in3 r later

theorem data_roles_from_spec (context : data_ontology.Context) (data : alloc.vec.Vec DataProperty)
    (index : Usize) (out : alloc.vec.Vec ObjectPropertyExpression)
    (room : out.val.length + (data.val.length - index.val) ≤ Usize.max) :
    ∃ res, data_ontology.data_roles_from context data index out = .ok res ∧
      ∀ v, res = some v → ∃ rs, v.val = out.val ++ rs ∧
        List.Forall₂ (fun r p => data_ontology.data_role context p = .ok (some r)) rs (data.val.drop index.val) := by
  rw [data_ontology.data_roles_from]
  by_cases inside : index.val < data.val.length
  · have lookup : data.index_usize index = .ok data.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨res, run, _⟩ := data_role_correct context data.val[index.val]
    cases res with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
    | some role =>
      have short : out.val.length < Usize.max := by omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out role short)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := data_roles_from_spec context data next pushed
        (by rw [contents, nextIndex]; simp; omega)
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, push,
        advance, restRun], fun v hv => ?_⟩
      obtain ⟨rs, value, pairs⟩ := restFacts v hv
      rw [nextIndex] at pairs
      refine ⟨role :: rs, by rw [value, contents]; simp, ?_⟩
      rw [split]
      exact .cons run pairs
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun v hv => ⟨[], ?_⟩⟩
    cases hv
    simp [List.drop_eq_nil_iff.mpr (show data.val.length ≤ index.val by omega)]
termination_by data.val.length - index.val
decreasing_by omega

theorem data_members_spec (context : data_ontology.Context) (data : AtLeastTwo DataProperty) :
    ∃ res, data_ontology.data_members context data = .ok res ∧
      ∀ roles, res = some roles →
        List.Forall₂ (fun r p => data_ontology.data_role context p = .ok (some r)) roles.elements data.elements := by
  rw [data_ontology.data_members]
  obtain ⟨r1, run1, _⟩ := data_role_correct context data.first
  obtain ⟨r2, run2, _⟩ := data_role_correct context data.second
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some first =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some second =>
      obtain ⟨r3, run3, facts3⟩ := data_roles_from_spec context data.rest 0#usize
        (alloc.vec.Vec.new ObjectPropertyExpression) (by simp [new_val])
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
      | some rest =>
        refine ⟨some ⟨first, second, rest⟩, by simp [run1, run2, run3], fun roles h => ?_⟩
        cases h
        obtain ⟨rs, value, pairs⟩ := facts3 rest rfl
        simp only [new_val, List.nil_append, zero_val, List.drop_zero] at value pairs
        simp only [AtLeastTwo.elements, value]
        exact .cons run1 (.cons run2 pairs)

theorem individual_members_spec (xs : AtLeastTwo Individual) :
    ∃ res, data_ontology.individual_members xs = .ok res ∧
      ∀ xs', res = some xs' → xs' = xs ∧ ∀ a ∈ xs.elements, Plain a := by
  rw [data_ontology.individual_members]
  obtain ⟨r1, run1, _⟩ := object_individual_of_correct xs.first
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some first =>
    have same1 := object_individual_of_some run1
    obtain ⟨r2, run2, _⟩ := object_individual_of_correct xs.second
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some second =>
      have same2 := object_individual_of_some run2
      obtain ⟨r3, run3, facts3⟩ := individuals_from_correct xs.rest 0#usize
        (alloc.vec.Vec.new Individual) (by simp [new_val])
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
      | some rest =>
        refine ⟨some ⟨first, second, rest⟩, by simp [run1, run2, run3], fun xs' h => ?_⟩
        cases h
        obtain ⟨value3, plain3⟩ := facts3 rest rfl
        simp only [new_val, List.nil_append, zero_val, List.drop_zero] at value3 plain3
        refine ⟨?_, ?_⟩
        · cases xs; simp only [AtLeastTwo.mk.injEq]
          exact ⟨same1.1, same2.1, by simpa [alloc.vec.Vec.eq_iff] using value3⟩
        · intro a mem
          simp only [AtLeastTwo.elements, List.mem_cons] at mem
          rcases mem with rfl | rfl | later
          · exact same1.2
          · exact same2.2
          · exact plain3 a later

/-- The roles of a role or role chain. -/
def subRoles : SubObjectPropertyExpression → List ObjectPropertyExpression
  | .Single r => [r]
  | .Chain rs => rs.elements

theorem encode_sub_spec (context : data_ontology.Context) (sub : SubObjectPropertyExpression) :
    ∃ res, data_ontology.encode_sub context sub = .ok res ∧
      ∀ sub', res = some sub' → sub' = sub ∧ ∀ r ∈ subRoles sub, RoleIn context r := by
  cases sub with
  | Single r =>
    rw [data_ontology.encode_sub]
    obtain ⟨res, run, facts⟩ := object_role_correct context r
    cases res with
    | none => exact ⟨none, by simp [run], by simp⟩
    | some copy =>
      obtain ⟨same, plain, inContext⟩ := facts copy rfl
      refine ⟨some (.Single copy), by simp [run], fun sub' h => ?_⟩
      cases h
      exact ⟨by rw [same], by simp [subRoles]; exact ⟨plain, inContext⟩⟩
  | Chain rs =>
    rw [data_ontology.encode_sub]
    obtain ⟨res, run, facts⟩ := object_members_spec context rs
    cases res with
    | none => exact ⟨none, by simp [run], by simp⟩
    | some rs' =>
      obtain ⟨same, inside⟩ := facts rs' rfl
      refine ⟨some (.Chain rs'), by simp [run], fun sub' h => ?_⟩
      cases h
      exact ⟨by rw [same], inside⟩

/-! ### Class expressions that no data node may satisfy -/

/-- What the encoding of a class expression on the left of an inclusion, or in
    a list of equivalent or disjoint classes, means: the expression at the
    elements that stand for elements of `I`, and nothing at the data nodes of an
    interpretation that keeps them apart. -/
def ObjectMeans (context : data_ontology.Context) (c c'' : ClassExpression) : Prop :=
  ClassMeans.{u,v,w,x} context c c'' ∧ GuardMeans.{w,x} context c c''

theorem and_denote (J : Interpretation Object' Value') (a b : ClassExpression) (y : Object') :
    classDenote J (.ObjectIntersectionOf ⟨a, b, alloc.vec.Vec.new ClassExpression⟩) y ↔
      classDenote J a y ∧ classDenote J b y := by
  rw [intersection_iff]; simp [AtLeastTwo.elements, new_val]

theorem object_class_denote (J : Interpretation Object' Value') (y : Object') :
    classDenote J (.ObjectComplementOf (.Class dataClass)) y ↔ ¬ J.classes dataClass y := by
  simp [classDenote]

theorem encode_object_spec (context : data_ontology.Context) (c : ClassExpression) :
    ∃ res, data_ontology.encode_object context c = .ok res ∧
      ∀ c'', res = some c'' → ObjectMeans.{u,v,w,x} context c c'' := by
  rw [data_ontology.encode_object]
  obtain ⟨res, run, means⟩ := encode_class_meaning.{u,v,w,x} context c
  obtain ⟨b, guardRun, guard⟩ := guarded_meaning.{w,x} context c
  cases res with
  | none => exact ⟨none, by simp [run], by simp⟩
  | some c' =>
    cases b with
    | true =>
      exact ⟨some c', by simp [run, guardRun], fun c'' h => by cases h; exact ⟨means c' rfl, guard rfl c' run⟩⟩
    | false =>
      refine ⟨some (.ObjectIntersectionOf ⟨c', .ObjectComplementOf (.Class dataClass),
        alloc.vec.Vec.new ClassExpression⟩), by simp [run, guardRun, object_class_eq, data_ontology.and], ?_⟩
      intro c'' h
      cases h
      refine ⟨?_, ?_⟩
      · intro Object Value Object' Value' I J obj known atoms sim atomsIn indsIn z
        rw [and_denote, object_class_denote]
        have same := means c' rfl I J obj known atoms sim atomsIn indsIn z
        have nonData : ¬ J.classes dataClass (obj z) := (sim.objects (obj z)).mpr ⟨z, rfl⟩
        exact ⟨fun holds => ⟨same.mp holds, nonData⟩, fun holds => same.mpr holds.1⟩
      · intro Object' Value' J known _ _ y dataNode holds
        rw [and_denote, object_class_denote] at holds
        exact holds.2 dataNode

theorem encode_object_list_spec (context : data_ontology.Context) (P : ClassExpression → ClassExpression → Prop)
    (classes : alloc.vec.Vec ClassExpression) (index : Usize) (out : alloc.vec.Vec ClassExpression)
    (room : out.val.length + (classes.val.length - index.val) ≤ Usize.max)
    (each : ∀ e ∈ classes.val, ∃ res, data_ontology.encode_object context e = .ok res ∧
      ∀ c, res = some c → P e c) :
    ∃ res, data_ontology.encode_object_list context classes index out = .ok res ∧
      ∀ v, res = some v → ∃ cs, v.val = out.val ++ cs ∧
        List.Forall₂ (fun c e => P e c) cs (classes.val.drop index.val) := by
  rw [data_ontology.encode_object_list]
  by_cases inside : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨res, run, means⟩ := each _ (List.getElem_mem inside)
    cases res with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
    | some c =>
      have short : out.val.length < Usize.max := by omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out c short)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := encode_object_list_spec context P classes next pushed
        (by rw [contents, nextIndex]; simp; omega) each
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, push,
        advance, restRun], fun v hv => ?_⟩
      obtain ⟨cs, value, pairs⟩ := restFacts v hv
      rw [nextIndex] at pairs
      refine ⟨c :: cs, by rw [value, contents]; simp, ?_⟩
      rw [split]
      exact .cons (means c rfl) pairs
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun v hv => ⟨[], ?_⟩⟩
    cases hv
    simp [List.drop_eq_nil_iff.mpr (show classes.val.length ≤ index.val by omega)]
termination_by classes.val.length - index.val
decreasing_by omega

theorem encode_object_members_spec (context : data_ontology.Context) (members : AtLeastTwo ClassExpression) :
    ∃ res, data_ontology.encode_object_members context members = .ok res ∧
      ∀ cs, res = some cs →
        List.Forall₂ (fun c e => ObjectMeans.{u,v,w,x} context e c) cs.elements members.elements := by
  rw [data_ontology.encode_object_members]
  obtain ⟨r1, run1, means1⟩ := encode_object_spec.{u,v,w,x} context members.first
  obtain ⟨r2, run2, means2⟩ := encode_object_spec.{u,v,w,x} context members.second
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some c1 =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some c2 =>
      obtain ⟨r3, run3, means3⟩ := encode_object_list_spec context (fun e c => ObjectMeans.{u,v,w,x} context e c)
        members.rest 0#usize (alloc.vec.Vec.new ClassExpression) (by simp [new_val])
        (fun e _ => encode_object_spec.{u,v,w,x} context e)
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
      | some rest =>
        refine ⟨some ⟨c1, c2, rest⟩, by simp [run1, run2, run3], fun cs hcs => ?_⟩
        cases hcs
        obtain ⟨cs, value, pairs⟩ := means3 rest rfl
        simp only [new_val, List.nil_append, zero_val, List.drop_zero] at value pairs
        simp only [AtLeastTwo.elements, value]
        exact .cons (means1 c1 rfl) (.cons (means2 c2 rfl) pairs)

/-! ### The correspondence for axioms -/

/-- How the values of `I`'s data properties sit at data nodes of `J`, element
    by element: `place z v d` relates values and data nodes one to one, each
    node stands for its value, an element's values along a data property with a
    role are the role's neighbours that stand for them, a literal's value stands
    at its individual, and `owl:topDataProperty` relates everything. -/
structure Placed (context : data_ontology.Context) (I : Interpretation Object Value)
    (J : Interpretation Object' Value') (obj : Object → Object') (lit : datatypes.DataValue → Value)
    (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value) (size : Value → ℕ → Prop) (place : Object → Value → Object' → Prop) : Prop where
  functional : ∀ z v d d', place z v d → place z v d' → d = d'
  injective : ∀ z v v' d, place z v d → place z v' d → v = v'
  nodes : ∀ z v d, place z v d → NodeValue context I J lit num mom size d v
  data : ∀ p role, data_ontology.data_role context p = .ok (some role) → ∀ z v,
    (I.dataProperties p z v ↔ ∃ d, place z v d ∧ objectRelation J role (obj z) d)
  literals : ∀ z lt a, data_ontology.literal_individual context lt = .ok (some a) →
    place z (I.literals lt) (individual J a)
  top : ∀ z v, I.dataProperties topData z v

/-- What an interpretation of the encoding made from an OWL model has besides
    the correspondence: its data nodes keep apart from the names, the data
    properties' roles leave no data node, and every neighbour along a data
    property's role stands for a value. -/
structure Inert (context : data_ontology.Context) (J : Interpretation Object' Value') (obj : Object → Object')
    (place : Object → Value → Object' → Prop) : Prop where
  classes : ∀ (c : Class) y, ¬ Reserved c.iri.spelling.val → c ≠ thing → J.classes dataClass y →
    ¬ J.classes c y
  sources : ∀ p role, data_ontology.data_role context p = .ok (some role) → ∀ y y', objectRelation J role y y' →
    ¬ J.classes dataClass y
  placed : ∀ p role, data_ontology.data_role context p = .ok (some role) → ∀ z d,
    objectRelation J role (obj z) d → ∃ v, place z v d

/-- The data restrictions of an axiom's class expressions. -/
def axiomAtoms : Axiom → List (DataProperty × Option DataRange × Nat)
  | .SubClassOf a b => classAtoms a ++ classAtoms b
  | .EquivalentClasses xs => xs.elements.flatMap classAtoms
  | .DisjointClasses xs => xs.elements.flatMap classAtoms
  | .DisjointUnion _ xs => xs.elements.flatMap classAtoms
  | .ObjectPropertyDomain _ e => classAtoms e
  | .ObjectPropertyRange _ e => classAtoms e
  | .DataPropertyDomain _ e => classAtoms e
  | .ClassAssertion e _ => classAtoms e
  | _ => []

/-- The individuals an axiom names. -/
def axiomIndividuals : Axiom → List Individual
  | .SubClassOf a b => classIndividuals a ++ classIndividuals b
  | .EquivalentClasses xs => xs.elements.flatMap classIndividuals
  | .DisjointClasses xs => xs.elements.flatMap classIndividuals
  | .DisjointUnion _ xs => xs.elements.flatMap classIndividuals
  | .ObjectPropertyDomain _ e => classIndividuals e
  | .ObjectPropertyRange _ e => classIndividuals e
  | .DataPropertyDomain _ e => classIndividuals e
  | .SameIndividual xs => xs.elements
  | .DifferentIndividuals xs => xs.elements
  | .ClassAssertion e a => a :: classIndividuals e
  | .ObjectPropertyAssertion _ a b => [a, b]
  | .NegativeObjectPropertyAssertion _ a b => [a, b]
  | .DataPropertyAssertion _ a _ => [a]
  | .NegativeDataPropertyAssertion _ a _ => [a]
  | _ => []

theorem forall2_strengthen {α β : Type} {R S : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → (∀ a b, b ∈ l2 → R a b → S a b) → List.Forall₂ S l1 l2
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, h => .cons (h _ _ List.mem_cons_self head)
      (forall2_strengthen tail (fun a b mem r => h a b (List.mem_cons_of_mem _ mem) r))

theorem pairwise_forall2 {α β : Type} {S : β → α → Prop} {R : α → α → Prop} {R' : β → β → Prop}
    {l' : List β} {l : List α} (pairs : List.Forall₂ S l' l)
    (step : ∀ a' b' a b, S a' a → S b' b → R a b → R' a' b') (holds : l.Pairwise R) : l'.Pairwise R' := by
  induction pairs with
  | nil => exact .nil
  | cons head tail ih =>
    rw [List.pairwise_cons] at holds ⊢
    refine ⟨fun b' mem => ?_, ih holds.2⟩
    obtain ⟨b, memB, rel⟩ := forall2_mem_left tail b' mem
    exact step _ _ _ _ head rel (holds.1 b memB)

theorem pairwise_forall2_back {α β : Type} {S : β → α → Prop} {R : α → α → Prop} {R' : β → β → Prop}
    {l' : List β} {l : List α} (pairs : List.Forall₂ S l' l)
    (step : ∀ a' b' a b, S a' a → S b' b → R' a' b' → R a b) (holds : l'.Pairwise R') : l.Pairwise R := by
  induction pairs with
  | nil => exact .nil
  | cons head tail ih =>
    rw [List.pairwise_cons] at holds ⊢
    refine ⟨fun b mem => ?_, ih holds.2⟩
    obtain ⟨b', memB', rel⟩ := forall2_mem_right tail b mem
    exact step _ _ _ _ head rel (holds.1 b' memB')

section Semantics
variable {context : data_ontology.Context} {I : Interpretation Object Value} {J : Interpretation Object' Value'}
  {obj : Object → Object'} {known : Individual → Prop} {atoms : List (DataProperty × Option DataRange × Nat)}

theorem quiet_of {place : Object → Value → Object' → Prop} (sim : Simulates context I J obj known atoms)
    (inert : Inert context J obj place) : Quiet context J known where
  classes := inert.classes
  roles := sim.closed
  data := inert.sources
  individuals := fun a k dataNode => by
    rw [sim.individuals a k] at dataNode
    exact (sim.objects _).mpr ⟨_, rfl⟩ dataNode

theorem object_place (sim : Simulates context I J obj known atoms) (z : Object) :
    ¬ J.classes dataClass (obj z) :=
  (sim.objects (obj z)).mpr ⟨z, rfl⟩

theorem facts_known (sim : Simulates context I J obj known atoms) (inds : List Individual)
    (allKnown : ∀ a ∈ inds, known a) : ∀ b ∈ objectFacts inds, satisfies J b.axiom := by
  rw [object_facts_hold]
  intro a mem
  rw [sim.individuals a (allKnown a mem)]
  exact object_place sim _

theorem context_relation (sim : Simulates context I J obj known atoms) (r : ObjectPropertyExpression)
    (inside : RoleIn context r) (notTop : RoleOf r ≠ topObject) (y y' : Object') :
    objectRelation J r y y' ↔ ∃ z z', y = obj z ∧ y' = obj z' ∧ objectRelation I r z z' := by
  have inContext := inside.2.resolve_left notTop
  constructor
  · intro related
    have ends : ¬ J.classes dataClass y ∧ ¬ J.classes dataClass y' := by
      cases r with
      | Property a => exact sim.closed a inContext y y' related
      | Inverse a => exact (sim.closed a inContext y' y related).symm
    obtain ⟨z, rfl⟩ := (sim.objects y).mp ends.1
    obtain ⟨z', rfl⟩ := (sim.objects y').mp ends.2
    exact ⟨z, z', rfl, rfl, (relation_place sim r inside.1 z z').mpr related⟩
  · rintro ⟨z, z', rfl, rfl, related⟩
    exact (relation_place sim r inside.1 z z').mp related

/-- A role the encoding copies relates all pairs on both sides, or is a role of
    the context. -/
theorem relation_split (sim : Simulates context I J obj known atoms) (r : ObjectPropertyExpression)
    (inside : RoleIn context r) :
    (RoleOf r = topObject ∧ (∀ z z', objectRelation I r z z') ∧ ∀ y y', objectRelation J r y y') ∨
    (RoleOf r ≠ topObject ∧
      ∀ y y', objectRelation J r y y' ↔ ∃ z z', y = obj z ∧ y' = obj z' ∧ objectRelation I r z z') := by
  by_cases top : RoleOf r = topObject
  · exact .inl ⟨top, universal_relation_left sim r top, universal_relation sim r top⟩
  · exact .inr ⟨top, context_relation sim r inside top⟩

theorem chain_place (sim : Simulates context I J obj known atoms) (rs : List ObjectPropertyExpression)
    (inside : ∀ r ∈ rs, RoleIn context r ∧ RoleOf r ≠ topObject) (z : Object) (y' : Object') :
    chainRelation J rs (obj z) y' ↔ ∃ z', y' = obj z' ∧ chainRelation I rs z z' := by
  induction rs generalizing z with
  | nil =>
    simp only [chainRelation]
    constructor
    · rintro rfl; exact ⟨z, rfl, rfl⟩
    · rintro ⟨z', rfl, rfl⟩; rfl
  | cons r rs ih =>
    have here := inside r List.mem_cons_self
    have rest := fun s mem => inside s (List.mem_cons_of_mem r mem)
    simp only [chainRelation]
    constructor
    · rintro ⟨m, related, tail⟩
      obtain ⟨z1, z2, same, rfl, relatedI⟩ := (context_relation sim r here.1 here.2 _ _).mp related
      have := sim.injective same
      subst this
      obtain ⟨z', rfl, tailI⟩ := (ih rest z2).mp tail
      exact ⟨z', rfl, z2, relatedI, tailI⟩
    · rintro ⟨z', rfl, m, relatedI, tailI⟩
      exact ⟨obj m, (relation_place sim r here.1.1 z m).mp relatedI, (ih rest m).mpr ⟨z', rfl, tailI⟩⟩

theorem chain_start (sim : Simulates context I J obj known atoms) (rs : List ObjectPropertyExpression)
    (nonempty : rs ≠ []) (inside : ∀ s ∈ rs, RoleIn context s ∧ RoleOf s ≠ topObject)
    (y y' : Object') (related : chainRelation J rs y y') : ∃ z, y = obj z := by
  cases rs with
  | nil => exact absurd rfl nonempty
  | cons r rs =>
    obtain ⟨m, first, _⟩ := related
    have here := inside r List.mem_cons_self
    obtain ⟨z, _, rfl, _, _⟩ := (context_relation sim r here.1 here.2 _ _).mp first
    exact ⟨z, rfl⟩

theorem sub_place (sim : Simulates context I J obj known atoms) (sub : SubObjectPropertyExpression)
    (inside : ∀ r ∈ subRoles sub, RoleIn context r ∧ RoleOf r ≠ topObject) (y y' : Object') :
    subRelation J sub y y' ↔ ∃ z z', y = obj z ∧ y' = obj z' ∧ subRelation I sub z z' := by
  cases sub with
  | Single r =>
    have here := inside r (by simp [subRoles])
    exact context_relation sim r here.1 here.2 y y'
  | Chain rs =>
    simp only [subRelation, subRoles] at inside ⊢
    constructor
    · intro related
      obtain ⟨z, rfl⟩ := chain_start sim rs.elements (by simp [AtLeastTwo.elements]) inside y y' related
      obtain ⟨z', rfl, chainI⟩ := (chain_place sim rs.elements inside z y').mp related
      exact ⟨z, z', rfl, rfl, chainI⟩
    · rintro ⟨z, z', rfl, rfl, chainI⟩
      exact (chain_place sim rs.elements inside z (obj z')).mpr ⟨z', rfl, chainI⟩

/-! #### Class axioms -/

theorem sub_class_means (sim : Simulates context I J obj known atoms) {sub sup sub'' sup' : ClassExpression}
    (subMeans : ObjectMeans.{u,v,w,x} context sub sub'') (supMeans : ClassMeans.{u,v,w,x} context sup sup')
    (atomsIn : ∀ a ∈ classAtoms sub ++ classAtoms sup, a ∈ atoms)
    (indsIn : ∀ a ∈ classIndividuals sub ++ classIndividuals sup, known a) :
    (satisfies J (.SubClassOf sub'' sup') → satisfies I (.SubClassOf sub sup)) ∧
    (Quiet context J known → satisfies I (.SubClassOf sub sup) → satisfies J (.SubClassOf sub'' sup')) := by
  have subAt := subMeans.1 I J obj known atoms sim (fun a h => atomsIn a (List.mem_append_left _ h))
    (fun a h => indsIn a (List.mem_append_left _ h))
  have supAt := supMeans I J obj known atoms sim (fun a h => atomsIn a (List.mem_append_right _ h))
    (fun a h => indsIn a (List.mem_append_right _ h))
  simp only [satisfies]
  refine ⟨fun holds z inside => (supAt z).mpr (holds _ ((subAt z).mp inside)), fun quiet holds y inside => ?_⟩
  by_cases dataNode : J.classes dataClass y
  · exact absurd inside (subMeans.2 J known quiet (fun a h => indsIn a (List.mem_append_left _ h)) y dataNode)
  · obtain ⟨z, rfl⟩ := (sim.objects y).mp dataNode
    exact (supAt z).mp (holds z ((subAt z).mpr inside))

/-- The members of a list of class expressions and their encodings, with what
    each encoding means. -/
theorem members_means (sim : Simulates context I J obj known atoms) {xs xs'' : AtLeastTwo ClassExpression}
    (pairs : List.Forall₂ (fun c e => ObjectMeans.{u,v,w,x} context e c) xs''.elements xs.elements)
    (atomsIn : ∀ a ∈ xs.elements.flatMap classAtoms, a ∈ atoms)
    (indsIn : ∀ a ∈ xs.elements.flatMap classIndividuals, known a) :
    List.Forall₂ (fun c e => (∀ z, classDenote I e z ↔ classDenote J c (obj z)) ∧
      (Quiet context J known → ∀ y, J.classes dataClass y → ¬ classDenote J c y)) xs''.elements xs.elements :=
  forall2_strengthen pairs (fun _ e mem m =>
    ⟨m.1 I J obj known atoms sim (fun a h => atomsIn a (List.mem_flatMap.mpr ⟨e, mem, h⟩))
      (fun a h => indsIn a (List.mem_flatMap.mpr ⟨e, mem, h⟩)),
     fun quiet => m.2 J known quiet (fun a h => indsIn a (List.mem_flatMap.mpr ⟨e, mem, h⟩))⟩)

theorem equivalent_classes_means (sim : Simulates context I J obj known atoms) {xs xs'' : AtLeastTwo ClassExpression}
    (pairs : List.Forall₂ (fun c e => ObjectMeans.{u,v,w,x} context e c) xs''.elements xs.elements)
    (atomsIn : ∀ a ∈ xs.elements.flatMap classAtoms, a ∈ atoms)
    (indsIn : ∀ a ∈ xs.elements.flatMap classIndividuals, known a) :
    (satisfies J (.EquivalentClasses xs'') → satisfies I (.EquivalentClasses xs)) ∧
    (Quiet context J known → satisfies I (.EquivalentClasses xs) → satisfies J (.EquivalentClasses xs'')) := by
  have means := members_means sim pairs atomsIn indsIn
  simp only [satisfies, allEqual]
  constructor
  · intro same a memA b memB
    obtain ⟨a'', memA'', relA⟩ := forall2_mem_right means a memA
    obtain ⟨b'', memB'', relB⟩ := forall2_mem_right means b memB
    funext z
    apply propext
    rw [relA.1 z, relB.1 z, same a'' memA'' b'' memB'']
  · intro quiet same a'' memA'' b'' memB''
    obtain ⟨a, memA, relA⟩ := forall2_mem_left means a'' memA''
    obtain ⟨b, memB, relB⟩ := forall2_mem_left means b'' memB''
    funext y
    apply propext
    by_cases dataNode : J.classes dataClass y
    · exact iff_of_false (relA.2 quiet y dataNode) (relB.2 quiet y dataNode)
    · obtain ⟨z, rfl⟩ := (sim.objects y).mp dataNode
      rw [← relA.1 z, ← relB.1 z, same a memA b memB]

theorem disjoint_classes_means (sim : Simulates context I J obj known atoms) {xs xs'' : AtLeastTwo ClassExpression}
    (pairs : List.Forall₂ (fun c e => ObjectMeans.{u,v,w,x} context e c) xs''.elements xs.elements)
    (atomsIn : ∀ a ∈ xs.elements.flatMap classAtoms, a ∈ atoms)
    (indsIn : ∀ a ∈ xs.elements.flatMap classIndividuals, known a) :
    (satisfies J (.DisjointClasses xs'') → satisfies I (.DisjointClasses xs)) ∧
    (Quiet context J known → satisfies I (.DisjointClasses xs) → satisfies J (.DisjointClasses xs'')) := by
  have means := members_means sim pairs atomsIn indsIn
  simp only [satisfies, pairwiseDisjoint]
  constructor
  · intro holds
    refine pairwise_forall2_back means (fun a'' b'' a b relA relB apart z both => ?_) holds
    exact apart (obj z) ⟨(relA.1 z).mp both.1, (relB.1 z).mp both.2⟩
  · intro quiet holds
    refine pairwise_forall2 means (fun a'' b'' a b relA relB apart y both => ?_) holds
    by_cases dataNode : J.classes dataClass y
    · exact relA.2 quiet y dataNode both.1
    · obtain ⟨z, rfl⟩ := (sim.objects y).mp dataNode
      exact apart z ⟨(relA.1 z).mpr both.1, (relB.1 z).mpr both.2⟩

theorem disjoint_union_means (sim : Simulates context I J obj known atoms) {c : Class}
    (plain : ¬ Reserved c.iri.spelling.val) (notThing : c ≠ thing) {xs xs'' : AtLeastTwo ClassExpression}
    (pairs : List.Forall₂ (fun c e => ObjectMeans.{u,v,w,x} context e c) xs''.elements xs.elements)
    (atomsIn : ∀ a ∈ xs.elements.flatMap classAtoms, a ∈ atoms)
    (indsIn : ∀ a ∈ xs.elements.flatMap classIndividuals, known a) :
    (satisfies J (.DisjointUnion c xs'') → satisfies I (.DisjointUnion c xs)) ∧
    (Quiet context J known → satisfies I (.DisjointUnion c xs) → satisfies J (.DisjointUnion c xs'')) := by
  have means := members_means sim pairs atomsIn indsIn
  have disjoint := disjoint_classes_means sim pairs atomsIn indsIn
  simp only [satisfies, pairwiseDisjoint] at disjoint ⊢
  constructor
  · rintro ⟨union, apart⟩
    refine ⟨fun z => ?_, disjoint.1 apart⟩
    rw [sim.classes c z plain, union (obj z)]
    constructor
    · rintro ⟨e'', mem'', holds⟩
      obtain ⟨e, mem, rel⟩ := forall2_mem_left means e'' mem''
      exact ⟨e, mem, (rel.1 z).mpr holds⟩
    · rintro ⟨e, mem, holds⟩
      obtain ⟨e'', mem'', rel⟩ := forall2_mem_right means e mem
      exact ⟨e'', mem'', (rel.1 z).mp holds⟩
  · rintro quiet ⟨union, apart⟩
    refine ⟨fun y => ?_, disjoint.2 quiet apart⟩
    by_cases dataNode : J.classes dataClass y
    · refine iff_of_false (quiet.classes c y plain notThing dataNode) ?_
      rintro ⟨e'', mem'', holds⟩
      obtain ⟨e, _, rel⟩ := forall2_mem_left means e'' mem''
      exact rel.2 quiet y dataNode holds
    · obtain ⟨z, rfl⟩ := (sim.objects y).mp dataNode
      rw [← sim.classes c z plain, union z]
      constructor
      · rintro ⟨e, mem, holds⟩
        obtain ⟨e'', mem'', rel⟩ := forall2_mem_right means e mem
        exact ⟨e'', mem'', (rel.1 z).mp holds⟩
      · rintro ⟨e'', mem'', holds⟩
        obtain ⟨e, mem, rel⟩ := forall2_mem_left means e'' mem''
        exact ⟨e, mem, (rel.1 z).mpr holds⟩

/-! #### Role axioms -/

theorem sub_property_means (sim : Simulates context I J obj known atoms) {sub : SubObjectPropertyExpression}
    {sup : ObjectPropertyExpression} (subIn : ∀ r ∈ subRoles sub, RoleIn context r) (supIn : RoleIn context sup)
    (guard : (∃ r ∈ subRoles sub, RoleOf r = topObject) → RoleOf sup = topObject) :
    satisfies J (.SubObjectPropertyOf sub sup) ↔ satisfies I (.SubObjectPropertyOf sub sup) := by
  simp only [satisfies]
  by_cases top : RoleOf sup = topObject
  · exact iff_of_true (fun y y' _ => universal_relation sim sup top y y')
      (fun z z' _ => universal_relation_left sim sup top z z')
  · have inside : ∀ r ∈ subRoles sub, RoleIn context r ∧ RoleOf r ≠ topObject :=
      fun r mem => ⟨subIn r mem, fun rt => top (guard ⟨r, mem, rt⟩)⟩
    constructor
    · intro holds z z' related
      have := holds (obj z) (obj z') ((sub_place sim sub inside _ _).mpr ⟨z, z', rfl, rfl, related⟩)
      exact (relation_place sim sup supIn.1 z z').mpr this
    · intro holds y y' related
      obtain ⟨z, z', rfl, rfl, relatedI⟩ := (sub_place sim sub inside y y').mp related
      exact (relation_place sim sup supIn.1 z z').mp (holds z z' relatedI)

theorem equivalent_properties_means (sim : Simulates context I J obj known atoms)
    {roles : AtLeastTwo ObjectPropertyExpression}
    (inside : ∀ r ∈ roles.elements, RoleIn context r ∧ RoleOf r ≠ topObject) :
    satisfies J (.EquivalentObjectProperties roles) ↔ satisfies I (.EquivalentObjectProperties roles) := by
  simp only [satisfies, allEqual]
  constructor
  · intro same r memR s memS
    funext z z'
    apply propext
    rw [relation_place sim r (inside r memR).1.1 z z', relation_place sim s (inside s memS).1.1 z z',
      same r memR s memS]
  · intro same r memR s memS
    funext y y'
    apply propext
    rw [context_relation sim r (inside r memR).1 (inside r memR).2,
      context_relation sim s (inside s memS).1 (inside s memS).2, same r memR s memS]

theorem disjoint_properties_means (sim : Simulates context I J obj known atoms)
    {roles : AtLeastTwo ObjectPropertyExpression} (inside : ∀ r ∈ roles.elements, RoleIn context r) :
    satisfies J (.DisjointObjectProperties roles) ↔ satisfies I (.DisjointObjectProperties roles) := by
  simp only [satisfies, pairwiseDisjoint]
  have pair : ∀ r ∈ roles.elements, ∀ s ∈ roles.elements,
      ((∀ yy : Object' × Object', ¬ (objectRelation J r yy.1 yy.2 ∧ objectRelation J s yy.1 yy.2)) ↔
       (∀ zz : Object × Object, ¬ (objectRelation I r zz.1 zz.2 ∧ objectRelation I s zz.1 zz.2))) := by
    intro r memR s memS
    obtain ⟨y0⟩ := J.objectsNonempty
    obtain ⟨z0⟩ := I.objectsNonempty
    rcases relation_split sim r (inside r memR) with ⟨_, allI, allJ⟩ | ⟨_, splitR⟩ <;>
      rcases relation_split sim s (inside s memS) with ⟨_, allI', allJ'⟩ | ⟨_, splitS⟩
    · exact iff_of_false (fun h => h (y0, y0) ⟨allJ _ _, allJ' _ _⟩) (fun h => h (z0, z0) ⟨allI _ _, allI' _ _⟩)
    · constructor
      · rintro h ⟨z, z'⟩ ⟨_, relS⟩
        exact h (obj z, obj z') ⟨allJ _ _, (splitS _ _).mpr ⟨z, z', rfl, rfl, relS⟩⟩
      · rintro h ⟨y, y'⟩ ⟨_, relS⟩
        obtain ⟨z, z', rfl, rfl, relSI⟩ := (splitS _ _).mp relS
        exact h (z, z') ⟨allI _ _, relSI⟩
    · constructor
      · rintro h ⟨z, z'⟩ ⟨relR, _⟩
        exact h (obj z, obj z') ⟨(splitR _ _).mpr ⟨z, z', rfl, rfl, relR⟩, allJ' _ _⟩
      · rintro h ⟨y, y'⟩ ⟨relR, _⟩
        obtain ⟨z, z', rfl, rfl, relRI⟩ := (splitR _ _).mp relR
        exact h (z, z') ⟨relRI, allI' _ _⟩
    · constructor
      · rintro h ⟨z, z'⟩ ⟨relR, relS⟩
        exact h (obj z, obj z') ⟨(splitR _ _).mpr ⟨z, z', rfl, rfl, relR⟩, (splitS _ _).mpr ⟨z, z', rfl, rfl, relS⟩⟩
      · rintro h ⟨y, y'⟩ ⟨relR, relS⟩
        obtain ⟨z, z', rfl, rfl, relRI⟩ := (splitR _ _).mp relR
        obtain ⟨z1, z1', same, same', relSI⟩ := (splitS _ _).mp relS
        have e1 := sim.injective same
        have e2 := sim.injective same'
        subst e1 e2
        exact h (z, z') ⟨relRI, relSI⟩
  constructor
  · exact fun holds => holds.imp_of_mem (fun memR memS h => (pair _ memR _ memS).mp h)
  · exact fun holds => holds.imp_of_mem (fun memR memS h => (pair _ memR _ memS).mpr h)

theorem inverse_properties_means (sim : Simulates context I J obj known atoms) {p q : ObjectPropertyExpression}
    (pIn : RoleIn context p ∧ RoleOf p ≠ topObject) (qIn : RoleIn context q ∧ RoleOf q ≠ topObject) :
    satisfies J (.InverseObjectProperties p q) ↔ satisfies I (.InverseObjectProperties p q) := by
  simp only [satisfies]
  constructor
  · intro h z z'
    rw [relation_place sim p pIn.1.1 z z', relation_place sim q qIn.1.1 z' z]
    exact h _ _
  · intro h y y'
    rw [context_relation sim p pIn.1 pIn.2, context_relation sim q qIn.1 qIn.2]
    constructor
    · rintro ⟨z, z', rfl, rfl, rel⟩
      exact ⟨z', z, rfl, rfl, (h z z').mp rel⟩
    · rintro ⟨z', z, rfl, rfl, rel⟩
      exact ⟨z, z', rfl, rfl, (h z z').mpr rel⟩

theorem domain_means (sim : Simulates context I J obj known atoms) {role : ObjectPropertyExpression}
    (inside : RoleIn context role) {e e' : ClassExpression} (means : ClassMeans.{u,v,w,x} context e e')
    (atomsIn : ∀ a ∈ classAtoms e, a ∈ atoms) (indsIn : ∀ a ∈ classIndividuals e, known a) :
    (RoleOf role = topObject → (satisfies J (.SubClassOf (.ObjectComplementOf (.Class dataClass)) e') ↔
      satisfies I (.ObjectPropertyDomain role e))) ∧
    (RoleOf role ≠ topObject → (satisfies J (.ObjectPropertyDomain role e') ↔
      satisfies I (.ObjectPropertyDomain role e))) ∧
    (RoleOf role = topObject → (satisfies J (.SubClassOf (.ObjectComplementOf (.Class dataClass)) e') ↔
      satisfies I (.ObjectPropertyRange role e))) ∧
    (RoleOf role ≠ topObject → (satisfies J (.ObjectPropertyRange role e') ↔
      satisfies I (.ObjectPropertyRange role e))) := by
  have at_ := means I J obj known atoms sim atomsIn indsIn
  simp only [satisfies]
  refine ⟨fun top => ?_, fun top => ?_, fun top => ?_, fun top => ?_⟩
  · constructor
    · intro holds z _ _
      exact (at_ z).mpr (holds (obj z) ((object_class_denote J _).mpr (object_place sim z)))
    · intro holds y outside
      obtain ⟨z, rfl⟩ := (sim.objects y).mp ((object_class_denote J _).mp outside)
      exact (at_ z).mp (holds z z (universal_relation_left sim role top z z))
  · constructor
    · intro holds z z' related
      exact (at_ z).mpr (holds (obj z) (obj z') ((relation_place sim role inside.1 z z').mp related))
    · intro holds y y' related
      obtain ⟨z, z', rfl, rfl, relatedI⟩ := (context_relation sim role inside top y y').mp related
      exact (at_ z).mp (holds z z' relatedI)
  · constructor
    · intro holds _ z' _
      exact (at_ z').mpr (holds (obj z') ((object_class_denote J _).mpr (object_place sim z')))
    · intro holds y outside
      obtain ⟨z, rfl⟩ := (sim.objects y).mp ((object_class_denote J _).mp outside)
      exact (at_ z).mp (holds z z (universal_relation_left sim role top z z))
  · constructor
    · intro holds z z' related
      exact (at_ z').mpr (holds (obj z) (obj z') ((relation_place sim role inside.1 z z').mp related))
    · intro holds y y' related
      obtain ⟨z, z', rfl, rfl, relatedI⟩ := (context_relation sim role inside top y y').mp related
      exact (at_ z').mp (holds z z' relatedI)

theorem reflexive_means (sim : Simulates context I J obj known atoms) {role : ObjectPropertyExpression}
    (inside : RoleIn context role) :
    (RoleOf role = topObject → (satisfies J (.ReflexiveObjectProperty role) ↔
      satisfies I (.ReflexiveObjectProperty role))) ∧
    (RoleOf role ≠ topObject → (satisfies J (.SubClassOf (.ObjectComplementOf (.Class dataClass))
      (.ObjectHasSelf role)) ↔ satisfies I (.ReflexiveObjectProperty role))) := by
  simp only [satisfies]
  refine ⟨fun top => iff_of_true (fun y => universal_relation sim role top y y)
    (fun z => universal_relation_left sim role top z z), fun top => ?_⟩
  constructor
  · intro holds z
    have := holds (obj z) ((object_class_denote J _).mpr (object_place sim z))
    rw [classDenote] at this
    exact (relation_place sim role inside.1 z z).mpr this
  · intro holds y outside
    obtain ⟨z, rfl⟩ := (sim.objects y).mp ((object_class_denote J _).mp outside)
    rw [classDenote]
    exact (relation_place sim role inside.1 z z).mp (holds z)

theorem characteristic_means (sim : Simulates context I J obj known atoms) {role : ObjectPropertyExpression}
    (inside : RoleIn context role) :
    (RoleOf role ≠ topObject → (satisfies J (.FunctionalObjectProperty role) ↔
      satisfies I (.FunctionalObjectProperty role))) ∧
    (RoleOf role ≠ topObject → (satisfies J (.InverseFunctionalObjectProperty role) ↔
      satisfies I (.InverseFunctionalObjectProperty role))) ∧
    (satisfies J (.IrreflexiveObjectProperty role) ↔ satisfies I (.IrreflexiveObjectProperty role)) ∧
    (satisfies J (.SymmetricObjectProperty role) ↔ satisfies I (.SymmetricObjectProperty role)) ∧
    (satisfies J (.AsymmetricObjectProperty role) ↔ satisfies I (.AsymmetricObjectProperty role)) ∧
    (satisfies J (.TransitiveObjectProperty role) ↔ satisfies I (.TransitiveObjectProperty role)) := by
  simp only [satisfies]
  obtain ⟨y0⟩ := J.objectsNonempty
  obtain ⟨z0⟩ := I.objectsNonempty
  have place := relation_place sim role inside.1
  refine ⟨fun top => ?_, fun top => ?_, ?_, ?_, ?_, ?_⟩
  · have image := context_relation sim role inside top
    constructor
    · intro holds z a b ra rb
      exact sim.injective (holds _ _ _ ((place z a).mp ra) ((place z b).mp rb))
    · intro holds y a b ra rb
      obtain ⟨z1, z2, rfl, rfl, r1⟩ := (image _ _).mp ra
      obtain ⟨z3, z4, same, rfl, r2⟩ := (image _ _).mp rb
      have := sim.injective same
      subst this
      rw [holds z1 z2 z4 r1 r2]
  · have image := context_relation sim role inside top
    constructor
    · intro holds a b z ra rb
      exact sim.injective (holds _ _ _ ((place a z).mp ra) ((place b z).mp rb))
    · intro holds a b y ra rb
      obtain ⟨z1, z2, rfl, rfl, r1⟩ := (image _ _).mp ra
      obtain ⟨z3, z4, rfl, same, r2⟩ := (image _ _).mp rb
      have := sim.injective same
      subst this
      rw [holds z1 z3 z2 r1 r2]
  · rcases relation_split sim role inside with ⟨_, allI, allJ⟩ | ⟨_, image⟩
    · exact iff_of_false (fun h => h y0 (allJ _ _)) (fun h => h z0 (allI _ _))
    · constructor
      · intro holds z related
        exact holds (obj z) ((place z z).mp related)
      · intro holds y related
        obtain ⟨z1, z2, rfl, same, r⟩ := (image _ _).mp related
        have := sim.injective same
        subst this
        exact holds z1 r
  · rcases relation_split sim role inside with ⟨_, allI, allJ⟩ | ⟨_, image⟩
    · exact iff_of_true (fun _ _ _ => allJ _ _) (fun _ _ _ => allI _ _)
    · constructor
      · intro holds z z' related
        exact (place z' z).mpr (holds _ _ ((place z z').mp related))
      · intro holds y y' related
        obtain ⟨z, z', rfl, rfl, r⟩ := (image _ _).mp related
        exact (place z' z).mp (holds z z' r)
  · rcases relation_split sim role inside with ⟨_, allI, allJ⟩ | ⟨_, image⟩
    · exact iff_of_false (fun h => h y0 y0 (allJ _ _) (allJ _ _)) (fun h => h z0 z0 (allI _ _) (allI _ _))
    · constructor
      · intro holds z z' related back
        exact holds _ _ ((place z z').mp related) ((place z' z).mp back)
      · intro holds y y' related back
        obtain ⟨z, z', rfl, rfl, r⟩ := (image _ _).mp related
        exact holds z z' r ((place z' z).mpr back)
  · rcases relation_split sim role inside with ⟨_, allI, allJ⟩ | ⟨_, image⟩
    · exact iff_of_true (fun _ _ _ _ _ => allJ _ _) (fun _ _ _ _ _ => allI _ _)
    · constructor
      · intro holds a b c rab rbc
        exact (place a c).mpr (holds _ _ _ ((place a b).mp rab) ((place b c).mp rbc))
      · intro holds a b c rab rbc
        obtain ⟨z1, z2, rfl, rfl, r1⟩ := (image _ _).mp rab
        obtain ⟨z3, z4, same, rfl, r2⟩ := (image _ _).mp rbc
        have := sim.injective same
        subst this
        exact (place z1 z4).mp (holds z1 z2 z4 r1 r2)

/-! #### Data property axioms -/

section Data
variable {lit : datatypes.DataValue → Value} {num : ℝ → Value} {mom : Rowl.DatatypeMap.Moment → Value} {size : Value → ℕ → Prop} {place : Object → Value → Object' → Prop}

theorem data_edge (sim : Simulates context I J obj known atoms) (placed : Placed context I J obj lit num mom size place)
    (inert : Inert context J obj place) {p : DataProperty} {role : ObjectPropertyExpression}
    (roleRun : data_ontology.data_role context p = .ok (some role)) {y d : Object'}
    (related : objectRelation J role y d) : ∃ z v, y = obj z ∧ place z v d ∧ I.dataProperties p z v := by
  obtain ⟨z, rfl⟩ := (sim.objects y).mp (inert.sources p role roleRun y d related)
  obtain ⟨v, pl⟩ := inert.placed p role roleRun z d related
  exact ⟨z, v, rfl, pl, (placed.data p role roleRun z v).mpr ⟨d, pl, related⟩⟩

theorem sub_data_means (sim : Simulates context I J obj known atoms) (placed : Placed context I J obj lit num mom size place)
    {p q : DataProperty} {rp rq : ObjectPropertyExpression}
    (pRun : data_ontology.data_role context p = .ok (some rp)) (qRun : data_ontology.data_role context q = .ok (some rq)) :
    (satisfies J (.SubObjectPropertyOf (.Single rp) rq) → satisfies I (.SubDataPropertyOf p q)) ∧
    (Inert context J obj place → satisfies I (.SubDataPropertyOf p q) →
      satisfies J (.SubObjectPropertyOf (.Single rp) rq)) := by
  simp only [satisfies, subRelation]
  constructor
  · intro holds z v hp
    obtain ⟨d, pl, rel⟩ := (placed.data p rp pRun z v).mp hp
    exact (placed.data q rq qRun z v).mpr ⟨d, pl, holds _ _ rel⟩
  · intro inert holds y d rel
    obtain ⟨z, v, rfl, pl, hp⟩ := data_edge sim placed inert pRun rel
    obtain ⟨d', pl', rel'⟩ := (placed.data q rq qRun z v).mp (holds z v hp)
    rw [placed.functional z v d d' pl pl']
    exact rel'

theorem equivalent_data_means (sim : Simulates context I J obj known atoms) (placed : Placed context I J obj lit num mom size place)
    {ps : AtLeastTwo DataProperty} {roles : AtLeastTwo ObjectPropertyExpression}
    (pairs : List.Forall₂ (fun r p => data_ontology.data_role context p = .ok (some r)) roles.elements ps.elements) :
    (satisfies J (.EquivalentObjectProperties roles) → satisfies I (.EquivalentDataProperties ps)) ∧
    (Inert context J obj place → satisfies I (.EquivalentDataProperties ps) →
      satisfies J (.EquivalentObjectProperties roles)) := by
  simp only [satisfies, allEqual]
  constructor
  · intro same p memP q memQ
    obtain ⟨rp, memRp, pRun⟩ := forall2_mem_right pairs p memP
    obtain ⟨rq, memRq, qRun⟩ := forall2_mem_right pairs q memQ
    funext z v
    apply propext
    rw [placed.data p rp pRun z v, placed.data q rq qRun z v, same rp memRp rq memRq]
  · intro inert same rp memRp rq memRq
    obtain ⟨p, memP, pRun⟩ := forall2_mem_left pairs rp memRp
    obtain ⟨q, memQ, qRun⟩ := forall2_mem_left pairs rq memRq
    have one : ∀ {p q : DataProperty} {rp rq : ObjectPropertyExpression},
        data_ontology.data_role context p = .ok (some rp) → data_ontology.data_role context q = .ok (some rq) →
        I.dataProperties p = I.dataProperties q → ∀ y d, objectRelation J rp y d → objectRelation J rq y d := by
      intro p q rp rq pRun qRun same y d rel
      obtain ⟨z, v, rfl, pl, hp⟩ := data_edge sim placed inert pRun rel
      rw [same] at hp
      obtain ⟨d', pl', rel'⟩ := (placed.data q rq qRun z v).mp hp
      rw [placed.functional z v d d' pl pl']
      exact rel'
    funext y d
    apply propext
    exact ⟨one pRun qRun (same p memP q memQ) y d, one qRun pRun (same q memQ p memP) y d⟩

theorem disjoint_data_means (sim : Simulates context I J obj known atoms) (placed : Placed context I J obj lit num mom size place)
    {ps : AtLeastTwo DataProperty} {roles : AtLeastTwo ObjectPropertyExpression}
    (pairs : List.Forall₂ (fun r p => data_ontology.data_role context p = .ok (some r)) roles.elements ps.elements) :
    (satisfies J (.DisjointObjectProperties roles) → satisfies I (.DisjointDataProperties ps)) ∧
    (Inert context J obj place → satisfies I (.DisjointDataProperties ps) →
      satisfies J (.DisjointObjectProperties roles)) := by
  simp only [satisfies, pairwiseDisjoint]
  constructor
  · intro holds
    refine pairwise_forall2_back pairs (fun rp rq p q pRun qRun apart zv both => ?_) holds
    obtain ⟨d, pl, rel⟩ := (placed.data p rp pRun zv.1 zv.2).mp both.1
    obtain ⟨d', pl', rel'⟩ := (placed.data q rq qRun zv.1 zv.2).mp both.2
    rw [placed.functional _ _ d d' pl pl'] at rel
    exact apart (obj zv.1, d') ⟨rel, rel'⟩
  · intro inert holds
    refine pairwise_forall2 pairs (fun rp rq p q pRun qRun apart yd both => ?_) holds
    obtain ⟨z, v, same, pl, hp⟩ := data_edge sim placed inert pRun both.1
    have rel' := both.2
    rw [same] at rel'
    exact apart (z, v) ⟨hp, (placed.data q rq qRun z v).mpr ⟨yd.2, pl, rel'⟩⟩

theorem data_domain_means (sim : Simulates context I J obj known atoms) (placed : Placed context I J obj lit num mom size place)
    {p : DataProperty} {rp : ObjectPropertyExpression} (pRun : data_ontology.data_role context p = .ok (some rp))
    {e e' : ClassExpression} (means : ClassMeans.{u,v,w,x} context e e')
    (atomsIn : ∀ a ∈ classAtoms e, a ∈ atoms) (indsIn : ∀ a ∈ classIndividuals e, known a) :
    (satisfies J (.ObjectPropertyDomain rp e') → satisfies I (.DataPropertyDomain p e)) ∧
    (Inert context J obj place → satisfies I (.DataPropertyDomain p e) →
      satisfies J (.ObjectPropertyDomain rp e')) := by
  have at_ := means I J obj known atoms sim atomsIn indsIn
  simp only [satisfies]
  constructor
  · intro holds z v hp
    obtain ⟨d, _, rel⟩ := (placed.data p rp pRun z v).mp hp
    exact (at_ z).mpr (holds _ _ rel)
  · intro inert holds y d rel
    obtain ⟨z, v, rfl, _, hp⟩ := data_edge sim placed inert pRun rel
    exact (at_ z).mp (holds z v hp)

theorem data_range_means (sim : Simulates context I J obj known atoms) (placed : Placed context I J obj lit num mom size place)
    (frame : RangeFrame I J lit num mom size) {p : DataProperty} {rp : ObjectPropertyExpression}
    (pRun : data_ontology.data_role context p = .ok (some rp)) {r : DataRange} {r' : ClassExpression}
    (means : RangeMeans.{u,v,w,x} context r r') :
    (satisfies J (.ObjectPropertyRange rp r') → satisfies I (.DataPropertyRange p r)) ∧
    (Inert context J obj place → satisfies I (.DataPropertyRange p r) →
      satisfies J (.ObjectPropertyRange rp r')) := by
  simp only [satisfies]
  constructor
  · intro holds z v hp
    obtain ⟨d, pl, rel⟩ := (placed.data p rp pRun z v).mp hp
    exact (means I J lit num mom size frame d v (placed.nodes z v d pl)).mpr (holds _ _ rel)
  · intro inert holds y d rel
    obtain ⟨z, v, rfl, pl, hp⟩ := data_edge sim placed inert pRun rel
    exact (means I J lit num mom size frame d v (placed.nodes z v d pl)).mp (holds z v hp)

theorem functional_data_means (sim : Simulates context I J obj known atoms) (placed : Placed context I J obj lit num mom size place)
    {p : DataProperty} {rp : ObjectPropertyExpression} (pRun : data_ontology.data_role context p = .ok (some rp)) :
    (satisfies J (.FunctionalObjectProperty rp) → satisfies I (.FunctionalDataProperty p)) ∧
    (Inert context J obj place → satisfies I (.FunctionalDataProperty p) →
      satisfies J (.FunctionalObjectProperty rp)) := by
  simp only [satisfies]
  constructor
  · intro holds z v1 v2 h1 h2
    obtain ⟨d1, pl1, rel1⟩ := (placed.data p rp pRun z v1).mp h1
    obtain ⟨d2, pl2, rel2⟩ := (placed.data p rp pRun z v2).mp h2
    have := holds _ _ _ rel1 rel2
    subst this
    exact placed.injective z v1 v2 d1 pl1 pl2
  · intro inert holds y d1 d2 rel1 rel2
    obtain ⟨z, v1, rfl, pl1, h1⟩ := data_edge sim placed inert pRun rel1
    obtain ⟨z', v2, same, pl2, h2⟩ := data_edge sim placed inert pRun rel2
    have := sim.injective same
    subst this
    have := holds z v1 v2 h1 h2
    subst this
    exact placed.functional z v1 d1 d2 pl1 pl2

theorem data_assertion_means (sim : Simulates context I J obj known atoms) (placed : Placed context I J obj lit num mom size place)
    {p : DataProperty} {rp : ObjectPropertyExpression} (pRun : data_ontology.data_role context p = .ok (some rp))
    {lt : Literal} {lv : Individual} (litRun : data_ontology.literal_individual context lt = .ok (some lv))
    {a : Individual} (knownA : known a) :
    (satisfies J (.ObjectPropertyAssertion rp a lv) ↔ satisfies I (.DataPropertyAssertion p a lt)) ∧
    (satisfies J (.NegativeObjectPropertyAssertion rp a lv) ↔ satisfies I (.NegativeDataPropertyAssertion p a lt)) := by
  simp only [satisfies]
  have key : objectRelation J rp (individual J a) (individual J lv) ↔
      I.dataProperties p (individual I a) (I.literals lt) := by
    rw [sim.individuals a knownA, placed.data p rp pRun]
    have pl := placed.literals (individual I a) lt lv litRun
    constructor
    · intro rel
      exact ⟨_, pl, rel⟩
    · rintro ⟨d, pl', rel⟩
      rw [placed.functional _ _ _ _ pl pl']
      exact rel
  exact ⟨key, not_congr key⟩

end Data

/-! #### Assertions -/

theorem same_individuals_means (sim : Simulates context I J obj known atoms) {xs : AtLeastTwo Individual}
    (indsIn : ∀ a ∈ xs.elements, known a) :
    (satisfies J (.SameIndividual xs) ↔ satisfies I (.SameIndividual xs)) ∧
    (satisfies J (.DifferentIndividuals xs) ↔ satisfies I (.DifferentIndividuals xs)) := by
  simp only [satisfies, allEqual]
  refine ⟨⟨fun same a memA b memB => sim.injective ?_, fun same a memA b memB => ?_⟩,
    ⟨fun holds => holds.imp_of_mem (fun memA memB apart same => apart ?_),
     fun holds => holds.imp_of_mem (fun memA memB apart same => apart ?_)⟩⟩
  · rw [← sim.individuals a (indsIn a memA), ← sim.individuals b (indsIn b memB)]
    exact same a memA b memB
  · rw [sim.individuals a (indsIn a memA), sim.individuals b (indsIn b memB), same a memA b memB]
  · rw [sim.individuals _ (indsIn _ memA), sim.individuals _ (indsIn _ memB), same]
  · apply sim.injective
    rw [← sim.individuals _ (indsIn _ memA), ← sim.individuals _ (indsIn _ memB)]
    exact same

theorem class_assertion_means (sim : Simulates context I J obj known atoms) {e e' : ClassExpression}
    {a : Individual} (means : ClassMeans.{u,v,w,x} context e e')
    (atomsIn : ∀ b ∈ classAtoms e, b ∈ atoms) (indsIn : ∀ b ∈ classIndividuals e, known b) (knownA : known a) :
    satisfies J (.ClassAssertion (.ObjectIntersectionOf ⟨e', .ObjectComplementOf (.Class dataClass),
      alloc.vec.Vec.new ClassExpression⟩) a) ↔ satisfies I (.ClassAssertion e a) := by
  simp only [satisfies]
  rw [and_denote, object_class_denote, sim.individuals a knownA,
    ← means I J obj known atoms sim atomsIn indsIn]
  exact ⟨fun h => h.1, fun h => ⟨h, object_place sim _⟩⟩

theorem object_assertion_means (sim : Simulates context I J obj known atoms) {role : ObjectPropertyExpression}
    (inside : RoleIn context role) {a b : Individual} (knownA : known a) (knownB : known b) :
    (satisfies J (.ObjectPropertyAssertion role a b) ↔ satisfies I (.ObjectPropertyAssertion role a b)) ∧
    (satisfies J (.NegativeObjectPropertyAssertion role a b) ↔
      satisfies I (.NegativeObjectPropertyAssertion role a b)) := by
  simp only [satisfies]
  rw [sim.individuals a knownA, sim.individuals b knownB, ← relation_place sim role inside.1]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Semantics

/-! ### What each axiom becomes -/

/-- What the axioms an axiom becomes mean: under every correspondence that
    covers the axiom's data restrictions and individuals, the OWL interpretation
    satisfies the axiom when the encoding's interpretation satisfies them, and
    conversely when the data nodes keep apart. -/
def AxiomMeans (context : data_ontology.Context) (ax : Axiom) (new : List AnnotatedAxiom) : Prop :=
  ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
    (I : Interpretation Object Value) (J : Interpretation Object' Value') (obj : Object → Object')
    (known : Individual → Prop) (atoms : List (DataProperty × Option DataRange × Nat))
    (lit : datatypes.DataValue → Value) (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value) (size : Value → ℕ → Prop) (place : Object → Value → Object' → Prop),
    Simulates context I J obj known atoms → Placed context I J obj lit num mom size place → RangeFrame I J lit num mom size →
    (∀ a ∈ axiomAtoms ax, a ∈ atoms) → (∀ a ∈ axiomIndividuals ax, known a) →
      ((∀ b ∈ new, satisfies J b.axiom) → satisfies I ax) ∧
      (Inert context J obj place → satisfies I ax → ∀ b ∈ new, satisfies J b.axiom)

/-- What the encoding of an axiom does: it runs, and when it answers, it adds
    the axioms the axiom becomes, which mean the axiom, after checking that its
    individuals are not the encoding's; and every model of them keeps the
    axiom's individuals off the data nodes. -/
def AxiomSpec (context : data_ontology.Context) (ax : Axiom) (out : alloc.vec.Vec AnnotatedAxiom) : Prop :=
  ∃ res, data_ontology.encode_axiom context ax out = .ok res ∧ ∀ out', res = some out' →
    ∃ new, out'.val = out.val ++ new ∧ AxiomMeans.{u,v,w,x} context ax new ∧
      (∀ a ∈ axiomIndividuals ax, Plain a) ∧
      ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'), (∀ b ∈ new, satisfies J b.axiom) →
        ∀ a ∈ axiomIndividuals ax, ¬ J.classes dataClass (individual J a)

/-- The annotated axiom the encoding pushes. -/
def bare (ax : Axiom) : AnnotatedAxiom := ⟨alloc.vec.Vec.new Annotation, ax⟩

theorem means_of_single {context : data_ontology.Context} {ax ax' : Axiom} {new : List AnnotatedAxiom}
    {inds : List Individual} (cover : ∀ b ∈ new, b = bare ax' ∨ b ∈ objectFacts inds) (mainIn : bare ax' ∈ new)
    (indsSub : ∀ a ∈ inds, a ∈ axiomIndividuals ax)
    (core : ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
      (I : Interpretation Object Value) (J : Interpretation Object' Value') (obj : Object → Object')
      (known : Individual → Prop) (atoms : List (DataProperty × Option DataRange × Nat))
      (lit : datatypes.DataValue → Value) (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value) (size : Value → ℕ → Prop) (place : Object → Value → Object' → Prop),
      Simulates context I J obj known atoms → Placed context I J obj lit num mom size place → RangeFrame I J lit num mom size →
      (∀ a ∈ axiomAtoms ax, a ∈ atoms) → (∀ a ∈ axiomIndividuals ax, known a) →
        (satisfies J ax' → satisfies I ax) ∧ (Inert context J obj place → satisfies I ax → satisfies J ax')) :
    AxiomMeans.{u,v,w,x} context ax new := by
  intro Object Value Object' Value' I J obj known atoms lit num mom size place sim placed frame atomsIn indsIn
  obtain ⟨sound, complete⟩ := core I J obj known atoms lit num mom size place sim placed frame atomsIn indsIn
  refine ⟨fun holds => sound (holds _ mainIn), fun inert holds b mem => ?_⟩
  rcases cover b mem with rfl | f
  · exact complete inert holds
  · exact facts_known sim inds (fun a m => indsIn a (indsSub a m)) b f

theorem names_of_facts {ax : Axiom} {new : List AnnotatedAxiom} {inds : List Individual}
    (sub : ∀ a ∈ axiomIndividuals ax, a ∈ inds) (factsIn : ∀ b ∈ objectFacts inds, b ∈ new)
    {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') (holds : ∀ b ∈ new, satisfies J b.axiom) :
    ∀ a ∈ axiomIndividuals ax, ¬ J.classes dataClass (individual J a) := fun a mem =>
  (object_facts_hold J inds).mp (fun b m => holds b (factsIn b m)) a (sub a mem)

theorem keep_spec (context : data_ontology.Context) (ax : Axiom) (out : alloc.vec.Vec AnnotatedAxiom)
    (run : data_ontology.encode_axiom context ax out = .ok (some out)) (noInds : axiomIndividuals ax = [])
    (holds : ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
      (I : Interpretation Object Value) (J : Interpretation Object' Value') (obj : Object → Object')
      (lit : datatypes.DataValue → Value) (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value) (size : Value → ℕ → Prop) (place : Object → Value → Object' → Prop),
      Placed context I J obj lit num mom size place → satisfies I ax) :
    AxiomSpec.{u,v,w,x} context ax out := by
  refine ⟨some out, run, fun out' h => ?_⟩
  cases h
  refine ⟨[], by simp, ?_, by simp [noInds], fun J _ => by simp [noInds]⟩
  intro Object Value Object' Value' I J obj known atoms lit num mom size place _ placed _ _ _
  exact ⟨fun _ => holds I J obj lit num mom size place placed, fun _ _ b mem => by simp at mem⟩

theorem sub_class_spec (context : data_ontology.Context) (sub sup : ClassExpression)
    (out : alloc.vec.Vec AnnotatedAxiom) : AxiomSpec.{u,v,w,x} context (.SubClassOf sub sup) out := by
  rw [AxiomSpec, data_ontology.encode_axiom]
  obtain ⟨r1, run1, means1⟩ := encode_object_spec.{u,v,w,x} context sub
  obtain ⟨r2, run2, means2⟩ := encode_class_meaning.{u,v,w,x} context sup
  cases r1 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some left =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some right =>
      obtain ⟨r3, run3, contents3⟩ := push_spec out (.SubClassOf left right)
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
      | some out1 =>
        obtain ⟨r4, run4, facts4⟩ := nominal_objects_spec sub out1
        cases r4 with
        | none => exact ⟨none, by simp [run1, run2, run3, run4], by simp⟩
        | some out2 =>
          obtain ⟨r5, run5, facts5⟩ := nominal_objects_spec sup out2
          refine ⟨r5, by simp [run1, run2, run3, run4, run5], fun out' h => ?_⟩
          obtain ⟨c5, p5⟩ := facts5 out' h
          obtain ⟨c4, p4⟩ := facts4 out2 rfl
          have c3 := contents3 out1 rfl
          have inds : axiomIndividuals (.SubClassOf sub sup) = classIndividuals sub ++ classIndividuals sup := rfl
          refine ⟨bare (.SubClassOf left right) :: objectFacts (classIndividuals sub ++ classIndividuals sup),
            by rw [c5, c4, c3, object_facts_append]; simp [bare], ?_, ?_, ?_⟩
          · refine means_of_single (inds := classIndividuals sub ++ classIndividuals sup)
              (by intro b mem; simpa using mem) (by simp) (fun a m => by rw [inds]; exact m) ?_
            intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ atomsIn indsIn
            obtain ⟨sound, complete⟩ := sub_class_means sim (means1 left rfl) (means2 right rfl) atomsIn indsIn
            exact ⟨sound, fun inert => complete (quiet_of sim inert)⟩
          · rw [inds]
            intro a mem
            rcases List.mem_append.mp mem with m | m
            · exact p4 a m
            · exact p5 a m
          · exact fun J => names_of_facts (fun a m => by rw [inds] at m; exact m) (fun b m => by simp [m]) J

theorem classes_spec (context : data_ontology.Context) (xs : AtLeastTwo ClassExpression)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    AxiomSpec.{u,v,w,x} context (.EquivalentClasses xs) out ∧ AxiomSpec.{u,v,w,x} context (.DisjointClasses xs) out := by
  obtain ⟨r1, run1, pairs⟩ := encode_object_members_spec.{u,v,w,x} context xs
  have inds : ∀ ax, ax = Axiom.EquivalentClasses xs ∨ ax = Axiom.DisjointClasses xs →
      axiomIndividuals ax = xs.elements.flatMap classIndividuals := by
    rintro ax (rfl | rfl) <;> rfl
  constructor
  · rw [AxiomSpec, data_ontology.encode_axiom]
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some xs'' =>
      obtain ⟨r2, run2, facts2⟩ := with_nominals_spec out (.EquivalentClasses xs'') xs
      refine ⟨r2, by simp [run1, run2], fun out' h => ?_⟩
      obtain ⟨c2, p2⟩ := facts2 out' h
      refine ⟨bare (.EquivalentClasses xs'') :: objectFacts (xs.elements.flatMap classIndividuals),
        by rw [c2]; simp [bare], ?_, by rw [inds _ (.inl rfl)]; exact p2, ?_⟩
      · refine means_of_single (inds := xs.elements.flatMap classIndividuals)
          (by intro b mem; simpa using mem) (by simp) (fun a m => by rw [inds _ (.inl rfl)]; exact m) ?_
        intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ atomsIn indsIn
        obtain ⟨sound, complete⟩ := equivalent_classes_means sim (pairs xs'' rfl) atomsIn indsIn
        exact ⟨sound, fun inert => complete (quiet_of sim inert)⟩
      · exact fun J => names_of_facts (fun a m => by rw [inds _ (.inl rfl)] at m; exact m) (fun b m => by simp [m]) J
  · rw [AxiomSpec, data_ontology.encode_axiom]
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some xs'' =>
      obtain ⟨r2, run2, facts2⟩ := with_nominals_spec out (.DisjointClasses xs'') xs
      refine ⟨r2, by simp [run1, run2], fun out' h => ?_⟩
      obtain ⟨c2, p2⟩ := facts2 out' h
      refine ⟨bare (.DisjointClasses xs'') :: objectFacts (xs.elements.flatMap classIndividuals),
        by rw [c2]; simp [bare], ?_, by rw [inds _ (.inr rfl)]; exact p2, ?_⟩
      · refine means_of_single (inds := xs.elements.flatMap classIndividuals)
          (by intro b mem; simpa using mem) (by simp) (fun a m => by rw [inds _ (.inr rfl)]; exact m) ?_
        intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ atomsIn indsIn
        obtain ⟨sound, complete⟩ := disjoint_classes_means sim (pairs xs'' rfl) atomsIn indsIn
        exact ⟨sound, fun inert => complete (quiet_of sim inert)⟩
      · exact fun J => names_of_facts (fun a m => by rw [inds _ (.inr rfl)] at m; exact m) (fun b m => by simp [m]) J

theorem disjoint_union_spec (context : data_ontology.Context) (c : Class) (xs : AtLeastTwo ClassExpression)
    (out : alloc.vec.Vec AnnotatedAxiom) : AxiomSpec.{u,v,w,x} context (.DisjointUnion c xs) out := by
  rw [AxiomSpec, data_ontology.encode_axiom, is_thing_correct]
  by_cases notThing : c = thing
  · exact ⟨none, by simp [notThing], by simp⟩
  simp only [notThing, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok, reserved_correct]
  by_cases reserved : Reserved c.iri.spelling.val
  · exact ⟨none, by simp [reserved], by simp⟩
  simp only [reserved, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
  obtain ⟨r1, run1, pairs⟩ := encode_object_members_spec.{u,v,w,x} context xs
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some xs'' =>
    obtain ⟨r2, run2, facts2⟩ := with_nominals_spec out (.DisjointUnion c xs'') xs
    have copy : ({ iri := { spelling := c.iri.spelling } } : Class) = c := rfl
    refine ⟨r2, by simp [run1, Rowl.Nnf.copy_bytes_identity, copy, run2], fun out' h => ?_⟩
    obtain ⟨c2, p2⟩ := facts2 out' h
    have inds : axiomIndividuals (.DisjointUnion c xs) = xs.elements.flatMap classIndividuals := rfl
    refine ⟨bare (.DisjointUnion c xs'') :: objectFacts (xs.elements.flatMap classIndividuals),
      by rw [c2]; simp [bare], ?_, by rw [inds]; exact p2, ?_⟩
    · refine means_of_single (inds := xs.elements.flatMap classIndividuals)
        (by intro b mem; simpa using mem) (by simp) (fun a m => by rw [inds]; exact m) ?_
      intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ atomsIn indsIn
      obtain ⟨sound, complete⟩ := disjoint_union_means sim reserved notThing (pairs xs'' rfl) atomsIn indsIn
      exact ⟨sound, fun inert => complete (quiet_of sim inert)⟩
    · exact fun J => names_of_facts (fun a m => by rw [inds] at m; exact m) (fun b m => by simp [m]) J

theorem push_means {context : data_ontology.Context} {ax ax' : Axiom} {out out' : alloc.vec.Vec AnnotatedAxiom}
    (contents : out'.val = out.val ++ [bare ax']) (noInds : axiomIndividuals ax = [])
    (core : ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
      (I : Interpretation Object Value) (J : Interpretation Object' Value') (obj : Object → Object')
      (known : Individual → Prop) (atoms : List (DataProperty × Option DataRange × Nat))
      (lit : datatypes.DataValue → Value) (num : ℝ → Value) (mom : Rowl.DatatypeMap.Moment → Value) (size : Value → ℕ → Prop) (place : Object → Value → Object' → Prop),
      Simulates context I J obj known atoms → Placed context I J obj lit num mom size place → RangeFrame I J lit num mom size →
      (∀ a ∈ axiomAtoms ax, a ∈ atoms) → (∀ a ∈ axiomIndividuals ax, known a) →
        (satisfies J ax' → satisfies I ax) ∧ (Inert context J obj place → satisfies I ax → satisfies J ax')) :
    ∃ new, out'.val = out.val ++ new ∧ AxiomMeans.{u,v,w,x} context ax new ∧
      (∀ a ∈ axiomIndividuals ax, Plain a) ∧
      ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'), (∀ b ∈ new, satisfies J b.axiom) →
        ∀ a ∈ axiomIndividuals ax, ¬ J.classes dataClass (individual J a) :=
  ⟨[bare ax'], contents, means_of_single (inds := []) (by simp) (by simp) (by simp) core, by simp [noInds],
    fun _ _ => by simp [noInds]⟩

theorem any_universal_correct (roles : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) :
    data_ontology.any_universal roles index =
      .ok (decide (∃ r ∈ roles.val.drop index.val, RoleOf r = topObject)) := by
  rw [data_ontology.any_universal]
  by_cases inside : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    by_cases top : RoleOf roles.val[index.val] = topObject
    · have found : ∃ r ∈ roles.val.drop index.val, RoleOf r = topObject :=
        ⟨roles.val[index.val], by rw [split]; exact List.mem_cons_self, top⟩
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, universal_correct, top, found]
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have rest := any_universal_correct roles next
      rw [nextIndex] at rest
      have same : (∃ r ∈ roles.val.drop index.val, RoleOf r = topObject) ↔
          ∃ r ∈ roles.val.drop (index.val + 1), RoleOf r = topObject := by
        rw [split]
        constructor
        · rintro ⟨r, mem, isTop⟩
          rcases List.mem_cons.mp mem with rfl | later
          · exact absurd isTop top
          · exact ⟨r, later, isTop⟩
        · rintro ⟨r, mem, isTop⟩
          exact ⟨r, List.mem_cons_of_mem _ mem, isTop⟩
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, universal_correct, top, advance,
        rest, same]
  · simp [UScalar.lt_equiv, inside, List.drop_eq_nil_iff.mpr (show roles.val.length ≤ index.val by omega)]
termination_by roles.val.length - index.val
decreasing_by omega

theorem members_universal_correct (roles : AtLeastTwo ObjectPropertyExpression) :
    data_ontology.members_universal roles = .ok (decide (∃ r ∈ roles.elements, RoleOf r = topObject)) := by
  have elements : roles.elements = roles.first :: roles.second :: roles.rest.val := rfl
  by_cases t1 : RoleOf roles.first = topObject
  · have found : ∃ r ∈ roles.elements, RoleOf r = topObject := ⟨roles.first, by simp [elements], t1⟩
    simp [data_ontology.members_universal, universal_correct, t1, found]
  · by_cases t2 : RoleOf roles.second = topObject
    · have found : ∃ r ∈ roles.elements, RoleOf r = topObject := ⟨roles.second, by simp [elements], t2⟩
      simp [data_ontology.members_universal, universal_correct, t1, t2, found]
    · have same : (∃ r ∈ roles.elements, RoleOf r = topObject) ↔ ∃ r ∈ roles.rest.val, RoleOf r = topObject := by
        rw [elements]
        constructor
        · rintro ⟨r, mem, isTop⟩
          rcases List.mem_cons.mp mem with rfl | mem
          · exact absurd isTop t1
          rcases List.mem_cons.mp mem with rfl | later
          · exact absurd isTop t2
          · exact ⟨r, later, isTop⟩
        · rintro ⟨r, mem, isTop⟩
          exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem), isTop⟩
      simp [data_ontology.members_universal, universal_correct, t1, t2, any_universal_correct, zero_val, same]

theorem sub_universal_correct (sub : SubObjectPropertyExpression) :
    data_ontology.sub_universal sub = .ok (decide (∃ r ∈ subRoles sub, RoleOf r = topObject)) := by
  cases sub with
  | Single r => simp [data_ontology.sub_universal, universal_correct, subRoles]
  | Chain rs => simp [data_ontology.sub_universal, members_universal_correct, subRoles]

theorem sub_property_spec (context : data_ontology.Context) (sub : SubObjectPropertyExpression)
    (sup : ObjectPropertyExpression) (out : alloc.vec.Vec AnnotatedAxiom) :
    AxiomSpec.{u,v,w,x} context (.SubObjectPropertyOf sub sup) out := by
  obtain ⟨r1, run1, facts1⟩ := encode_sub_spec context sub
  obtain ⟨r2, run2, facts2⟩ := object_role_correct context sup
  rw [AxiomSpec, data_ontology.encode_axiom, sub_universal_correct]
  by_cases blocked : (∃ r ∈ subRoles sub, RoleOf r = topObject) ∧ RoleOf sup ≠ topObject
  · exact ⟨none, by simp [blocked.1, universal_correct, blocked.2], by simp⟩
  have guard : (∃ r ∈ subRoles sub, RoleOf r = topObject) → RoleOf sup = topObject := fun h => by
    by_contra h'
    exact blocked ⟨h, h'⟩
  cases r1 with
  | none =>
    refine ⟨none, ?_, by simp⟩
    rcases em (∃ r ∈ subRoles sub, RoleOf r = topObject) with t | t
    · simp [t, guard t, universal_correct, run1, run2]
    · simp [t, universal_correct, run1, run2]
  | some sub' =>
    cases r2 with
    | none =>
      refine ⟨none, ?_, by simp⟩
      rcases em (∃ r ∈ subRoles sub, RoleOf r = topObject) with t | t
      · simp [t, guard t, universal_correct, run1, run2]
      · simp [t, universal_correct, run1, run2]
    | some sup' =>
      obtain ⟨subSame, subIn⟩ := facts1 sub' rfl
      obtain ⟨supSame, supPlain, supCtx⟩ := facts2 sup' rfl
      subst sub' sup'
      obtain ⟨r3, run3, contents3⟩ := push_spec out (.SubObjectPropertyOf sub sup)
      refine ⟨r3, ?_, fun out' h => ?_⟩
      · rcases em (∃ r ∈ subRoles sub, RoleOf r = topObject) with t | t
        · simp [t, guard t, universal_correct, run1, run2, run3]
        · simp [t, universal_correct, run1, run2, run3]
      · refine push_means (contents3 out' h) rfl ?_
        intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ _ _
        have equal := sub_property_means sim subIn ⟨supPlain, supCtx⟩ guard
        exact ⟨equal.mp, fun _ => equal.mpr⟩

theorem equivalent_properties_spec (context : data_ontology.Context) (roles : AtLeastTwo ObjectPropertyExpression)
    (out : alloc.vec.Vec AnnotatedAxiom) : AxiomSpec.{u,v,w,x} context (.EquivalentObjectProperties roles) out := by
  rw [AxiomSpec, data_ontology.encode_axiom, members_universal_correct]
  by_cases anyTop : ∃ r ∈ roles.elements, RoleOf r = topObject
  · exact ⟨none, by simp [anyTop], by simp⟩
  obtain ⟨r1, run1, facts1⟩ := object_members_spec context roles
  cases r1 with
  | none => exact ⟨none, by simp [anyTop, run1], by simp⟩
  | some roles' =>
    obtain ⟨same, inside⟩ := facts1 roles' rfl
    subst roles'
    obtain ⟨r2, run2, contents2⟩ := push_spec out (.EquivalentObjectProperties roles)
    refine ⟨r2, by simp [anyTop, run1, run2], fun out' h => push_means (contents2 out' h) rfl ?_⟩
    intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ _ _
    have equal := equivalent_properties_means sim (fun r mem => ⟨inside r mem, fun t => anyTop ⟨r, mem, t⟩⟩)
    exact ⟨equal.mp, fun _ => equal.mpr⟩

theorem disjoint_properties_spec (context : data_ontology.Context) (roles : AtLeastTwo ObjectPropertyExpression)
    (out : alloc.vec.Vec AnnotatedAxiom) : AxiomSpec.{u,v,w,x} context (.DisjointObjectProperties roles) out := by
  rw [AxiomSpec, data_ontology.encode_axiom]
  obtain ⟨r1, run1, facts1⟩ := object_members_spec context roles
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some roles' =>
    obtain ⟨same, inside⟩ := facts1 roles' rfl
    subst roles'
    obtain ⟨r2, run2, contents2⟩ := push_spec out (.DisjointObjectProperties roles)
    refine ⟨r2, by simp [run1, run2], fun out' h => push_means (contents2 out' h) rfl ?_⟩
    intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ _ _
    have equal := disjoint_properties_means sim inside
    exact ⟨equal.mp, fun _ => equal.mpr⟩

theorem inverse_properties_spec (context : data_ontology.Context) (p q : ObjectPropertyExpression)
    (out : alloc.vec.Vec AnnotatedAxiom) : AxiomSpec.{u,v,w,x} context (.InverseObjectProperties p q) out := by
  rw [AxiomSpec, data_ontology.encode_axiom, universal_correct]
  by_cases pTop : RoleOf p = topObject
  · exact ⟨none, by simp [pTop], by simp⟩
  simp only [pTop, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok, universal_correct]
  by_cases qTop : RoleOf q = topObject
  · exact ⟨none, by simp [qTop], by simp⟩
  simp only [qTop, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
  obtain ⟨r1, run1, facts1⟩ := object_role_correct context p
  obtain ⟨r2, run2, facts2⟩ := object_role_correct context q
  cases r1 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some p' =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some q' =>
      obtain ⟨pSame, pPlain, pCtx⟩ := facts1 p' rfl
      obtain ⟨qSame, qPlain, qCtx⟩ := facts2 q' rfl
      subst p' q'
      obtain ⟨r3, run3, contents3⟩ := push_spec out (.InverseObjectProperties p q)
      refine ⟨r3, by simp [run1, run2, run3], fun out' h => push_means (contents3 out' h) rfl ?_⟩
      intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ _ _
      have equal := inverse_properties_means sim ⟨⟨pPlain, pCtx⟩, pTop⟩ ⟨⟨qPlain, qCtx⟩, qTop⟩
      exact ⟨equal.mp, fun _ => equal.mpr⟩

theorem domain_or_range_spec (context : data_ontology.Context) (role : ObjectPropertyExpression)
    (e : ClassExpression) (domain : Bool) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.domain_or_range context role e domain out = .ok res ∧ ∀ out', res = some out' →
      ∃ e', ClassMeans.{u,v,w,x} context e e' ∧ RoleIn context role ∧ (∀ a ∈ classIndividuals e, Plain a) ∧
        out'.val = out.val ++ objectFacts (classIndividuals e) ++
          [bare (if RoleOf role = topObject then .SubClassOf (.ObjectComplementOf (.Class dataClass)) e'
            else if domain then .ObjectPropertyDomain role e' else .ObjectPropertyRange role e')] := by
  rw [data_ontology.domain_or_range]
  obtain ⟨r1, run1, facts1⟩ := object_role_correct context role
  obtain ⟨r2, run2, means2⟩ := encode_class_meaning.{u,v,w,x} context e
  cases r1 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some copy =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some e' =>
      obtain ⟨same, plain, ctx⟩ := facts1 copy rfl
      subst copy
      obtain ⟨r3, run3, facts3⟩ := nominal_objects_spec e out
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
      | some out1 =>
        obtain ⟨c3, p3⟩ := facts3 out1 rfl
        by_cases top : RoleOf role = topObject
        · obtain ⟨r4, run4, contents4⟩ := push_spec out1 (.SubClassOf (.ObjectComplementOf (.Class dataClass)) e')
          refine ⟨r4, by simp [run1, run2, run3, universal_correct, top, object_class_eq, run4], fun out' h => ?_⟩
          refine ⟨e', means2 e' rfl, ⟨plain, ctx⟩, p3, ?_⟩
          rw [contents4 out' h, c3]
          simp [top, bare]
        · cases domain with
          | true =>
            obtain ⟨r4, run4, contents4⟩ := push_spec out1 (.ObjectPropertyDomain role e')
            refine ⟨r4, by simp [run1, run2, run3, universal_correct, top, run4], fun out' h => ?_⟩
            refine ⟨e', means2 e' rfl, ⟨plain, ctx⟩, p3, ?_⟩
            rw [contents4 out' h, c3]
            simp [top, bare]
          | false =>
            obtain ⟨r4, run4, contents4⟩ := push_spec out1 (.ObjectPropertyRange role e')
            refine ⟨r4, by simp [run1, run2, run3, universal_correct, top, run4], fun out' h => ?_⟩
            refine ⟨e', means2 e' rfl, ⟨plain, ctx⟩, p3, ?_⟩
            rw [contents4 out' h, c3]
            simp [top, bare]

theorem domain_spec (context : data_ontology.Context) (role : ObjectPropertyExpression) (e : ClassExpression)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    AxiomSpec.{u,v,w,x} context (.ObjectPropertyDomain role e) out ∧
      AxiomSpec.{u,v,w,x} context (.ObjectPropertyRange role e) out := by
  constructor
  · rw [AxiomSpec, data_ontology.encode_axiom]
    obtain ⟨res, run, facts⟩ := domain_or_range_spec.{u,v,w,x} context role e true out
    refine ⟨res, run, fun out' h => ?_⟩
    obtain ⟨e', means, inside, plain, contents⟩ := facts out' h
    have inds : axiomIndividuals (.ObjectPropertyDomain role e) = classIndividuals e := rfl
    refine ⟨_, by rw [contents, List.append_assoc], ?_, by rw [inds]; exact plain,
      fun J => names_of_facts (fun a m => by rw [inds] at m; exact m) (fun b m => by simp [m]) J⟩
    refine means_of_single (inds := classIndividuals e) (by intro b mem; simp at mem; tauto) (by simp)
      (fun a m => by rw [inds]; exact m) ?_
    intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ atomsIn indsIn
    have equal := domain_means sim inside means atomsIn indsIn
    by_cases top : RoleOf role = topObject
    · simp only [top, ↓reduceIte]
      exact ⟨(equal.1 top).mp, fun _ => (equal.1 top).mpr⟩
    · simp only [top, ↓reduceIte]
      exact ⟨(equal.2.1 top).mp, fun _ => (equal.2.1 top).mpr⟩
  · rw [AxiomSpec, data_ontology.encode_axiom]
    obtain ⟨res, run, facts⟩ := domain_or_range_spec.{u,v,w,x} context role e false out
    refine ⟨res, run, fun out' h => ?_⟩
    obtain ⟨e', means, inside, plain, contents⟩ := facts out' h
    have inds : axiomIndividuals (.ObjectPropertyRange role e) = classIndividuals e := rfl
    refine ⟨_, by rw [contents, List.append_assoc], ?_, by rw [inds]; exact plain,
      fun J => names_of_facts (fun a m => by rw [inds] at m; exact m) (fun b m => by simp [m]) J⟩
    refine means_of_single (inds := classIndividuals e) (by intro b mem; simp at mem; tauto) (by simp)
      (fun a m => by rw [inds]; exact m) ?_
    intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ atomsIn indsIn
    have equal := domain_means sim inside means atomsIn indsIn
    by_cases top : RoleOf role = topObject
    · simp only [top, ↓reduceIte]
      exact ⟨(equal.2.2.1 top).mp, fun _ => (equal.2.2.1 top).mpr⟩
    · simp only [top, ↓reduceIte, Bool.false_eq_true]
      exact ⟨(equal.2.2.2 top).mp, fun _ => (equal.2.2.2 top).mpr⟩

theorem role_axiom_eq (context : data_ontology.Context) (role copy : ObjectPropertyExpression) (kind : U8)
    (out : alloc.vec.Vec AnnotatedAxiom) (run : data_ontology.object_role context role = .ok (some copy)) :
    data_ontology.role_axiom context role kind out = data_ontology.push out
      (if kind = 0#u8 then .FunctionalObjectProperty copy
       else if kind = 1#u8 then .InverseFunctionalObjectProperty copy
       else if kind = 2#u8 then .IrreflexiveObjectProperty copy
       else if kind = 3#u8 then .SymmetricObjectProperty copy
       else if kind = 4#u8 then .AsymmetricObjectProperty copy
       else .TransitiveObjectProperty copy) := by
  rw [data_ontology.role_axiom, run]
  simp only [bind_ok]
  split_ifs <;> simp only [bind_ok]

/-- The encoding of a role characteristic that is pushed as it is. -/
theorem characteristic_spec (context : data_ontology.Context) (role : ObjectPropertyExpression)
    (kind : U8) (ax : Axiom) (out : alloc.vec.Vec AnnotatedAxiom)
    (encoded : ∀ out, data_ontology.encode_axiom context ax out = data_ontology.role_axiom context role kind out)
    (chosen : (if kind = 0#u8 then Axiom.FunctionalObjectProperty role
       else if kind = 1#u8 then .InverseFunctionalObjectProperty role
       else if kind = 2#u8 then .IrreflexiveObjectProperty role
       else if kind = 3#u8 then .SymmetricObjectProperty role
       else if kind = 4#u8 then .AsymmetricObjectProperty role
       else .TransitiveObjectProperty role) = ax)
    (noInds : axiomIndividuals ax = [])
    (equal : ∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
      (I : Interpretation Object Value) (J : Interpretation Object' Value') (obj : Object → Object')
      (known : Individual → Prop) (atoms : List (DataProperty × Option DataRange × Nat)),
      Simulates context I J obj known atoms → RoleIn context role → (satisfies J ax ↔ satisfies I ax)) :
    AxiomSpec.{u,v,w,x} context ax out := by
  rw [AxiomSpec, encoded]
  obtain ⟨r1, run1, facts1⟩ := object_role_correct context role
  cases r1 with
  | none => exact ⟨none, by rw [data_ontology.role_axiom, run1]; simp, by simp⟩
  | some copy =>
    obtain ⟨same, plain, ctx⟩ := facts1 copy rfl
    subst copy
    obtain ⟨r2, run2, contents2⟩ := push_spec out ax
    refine ⟨r2, by rw [role_axiom_eq context role role kind out run1, chosen]; exact run2,
      fun out' h => push_means (contents2 out' h) noInds ?_⟩
    intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ _ _
    have e := equal I J obj known atoms sim ⟨plain, ctx⟩
    exact ⟨e.mp, fun _ => e.mpr⟩

theorem characteristics_spec (context : data_ontology.Context) (role : ObjectPropertyExpression)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    AxiomSpec.{u,v,w,x} context (.FunctionalObjectProperty role) out ∧
    AxiomSpec.{u,v,w,x} context (.InverseFunctionalObjectProperty role) out ∧
    AxiomSpec.{u,v,w,x} context (.IrreflexiveObjectProperty role) out ∧
    AxiomSpec.{u,v,w,x} context (.SymmetricObjectProperty role) out ∧
    AxiomSpec.{u,v,w,x} context (.AsymmetricObjectProperty role) out ∧
    AxiomSpec.{u,v,w,x} context (.TransitiveObjectProperty role) out := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases top : RoleOf role = topObject
    · exact ⟨none, by rw [data_ontology.encode_axiom, universal_correct]; simp [top], by simp⟩
    · refine characteristic_spec context role 0#u8 _ out (fun out => by
        rw [data_ontology.encode_axiom, universal_correct]; simp [top]) (by simp) rfl ?_
      intro Object Value Object' Value' I J obj known atoms sim inside
      exact (characteristic_means sim inside).1 top
  · by_cases top : RoleOf role = topObject
    · exact ⟨none, by rw [data_ontology.encode_axiom, universal_correct]; simp [top], by simp⟩
    · refine characteristic_spec context role 1#u8 _ out (fun out => by
        rw [data_ontology.encode_axiom, universal_correct]; simp [top]) (by simp) rfl ?_
      intro Object Value Object' Value' I J obj known atoms sim inside
      exact (characteristic_means sim inside).2.1 top
  · refine characteristic_spec context role 2#u8 _ out (fun out => by rw [data_ontology.encode_axiom])
      (by simp) rfl ?_
    intro Object Value Object' Value' I J obj known atoms sim inside
    exact (characteristic_means sim inside).2.2.1
  · refine characteristic_spec context role 3#u8 _ out (fun out => by rw [data_ontology.encode_axiom])
      (by simp) rfl ?_
    intro Object Value Object' Value' I J obj known atoms sim inside
    exact (characteristic_means sim inside).2.2.2.1
  · refine characteristic_spec context role 4#u8 _ out (fun out => by rw [data_ontology.encode_axiom])
      (by simp) rfl ?_
    intro Object Value Object' Value' I J obj known atoms sim inside
    exact (characteristic_means sim inside).2.2.2.2.1
  · refine characteristic_spec context role 5#u8 _ out (fun out => by rw [data_ontology.encode_axiom])
      (by simp) rfl ?_
    intro Object Value Object' Value' I J obj known atoms sim inside
    exact (characteristic_means sim inside).2.2.2.2.2

theorem reflexive_spec (context : data_ontology.Context) (role : ObjectPropertyExpression)
    (out : alloc.vec.Vec AnnotatedAxiom) : AxiomSpec.{u,v,w,x} context (.ReflexiveObjectProperty role) out := by
  rw [AxiomSpec, data_ontology.encode_axiom]
  obtain ⟨r1, run1, facts1⟩ := object_role_correct context role
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some copy =>
    obtain ⟨same, plain, ctx⟩ := facts1 copy rfl
    subst copy
    by_cases top : RoleOf role = topObject
    · obtain ⟨r2, run2, contents2⟩ := push_spec out (.ReflexiveObjectProperty role)
      refine ⟨r2, by simp [run1, universal_correct, top, run2], fun out' h => push_means (contents2 out' h) rfl ?_⟩
      intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ _ _
      have e := (reflexive_means sim ⟨plain, ctx⟩).1 top
      exact ⟨e.mp, fun _ => e.mpr⟩
    · obtain ⟨r2, run2, contents2⟩ := push_spec out
        (.SubClassOf (.ObjectComplementOf (.Class dataClass)) (.ObjectHasSelf role))
      refine ⟨r2, by simp [run1, universal_correct, top, object_class_eq, run2],
        fun out' h => push_means (contents2 out' h) rfl ?_⟩
      intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ _ _
      have e := (reflexive_means sim ⟨plain, ctx⟩).2 top
      exact ⟨e.mp, fun _ => e.mpr⟩

theorem sub_data_spec (context : data_ontology.Context) (p q : DataProperty) (out : alloc.vec.Vec AnnotatedAxiom) :
    AxiomSpec.{u,v,w,x} context (.SubDataPropertyOf p q) out := by
  by_cases top : q = topData
  · subst top
    rw [AxiomSpec]
    by_cases reserved : Reserved p.iri.spelling.val
    · exact ⟨none, by rw [data_ontology.encode_axiom, is_top_data_correct]; simp [reserved_correct, reserved], by simp⟩
    · have run : data_ontology.encode_axiom context (.SubDataPropertyOf p topData) out = .ok (some out) := by
        rw [data_ontology.encode_axiom, is_top_data_correct]; simp [reserved_correct, reserved]
      refine keep_spec context _ out run rfl ?_
      intro Object Value Object' Value' I J obj lit num mom size place placed
      simp only [satisfies]
      exact fun z v _ => placed.top z v
  rw [AxiomSpec, data_ontology.encode_axiom, is_top_data_correct]
  simp only [top, decide_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨r1, run1, _⟩ := data_role_correct context p
  obtain ⟨r2, run2, _⟩ := data_role_correct context q
  cases r1 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some rp =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some rq =>
      obtain ⟨r3, run3, contents3⟩ := push_spec out (.SubObjectPropertyOf (.Single rp) rq)
      refine ⟨r3, by simp [run1, run2, run3], fun out' h => push_means (contents3 out' h) rfl ?_⟩
      intro Object Value Object' Value' I J obj known atoms lit num mom size place sim placed _ _ _
      exact sub_data_means sim placed run1 run2

theorem data_lists_spec (context : data_ontology.Context) (ps : AtLeastTwo DataProperty)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    AxiomSpec.{u,v,w,x} context (.EquivalentDataProperties ps) out ∧
      AxiomSpec.{u,v,w,x} context (.DisjointDataProperties ps) out := by
  obtain ⟨r1, run1, pairs⟩ := data_members_spec context ps
  constructor
  · rw [AxiomSpec, data_ontology.encode_axiom]
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some roles =>
      obtain ⟨r2, run2, contents2⟩ := push_spec out (.EquivalentObjectProperties roles)
      refine ⟨r2, by simp [run1, run2], fun out' h => push_means (contents2 out' h) rfl ?_⟩
      intro Object Value Object' Value' I J obj known atoms lit num mom size place sim placed _ _ _
      exact equivalent_data_means sim placed (pairs roles rfl)
  · rw [AxiomSpec, data_ontology.encode_axiom]
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some roles =>
      obtain ⟨r2, run2, contents2⟩ := push_spec out (.DisjointObjectProperties roles)
      refine ⟨r2, by simp [run1, run2], fun out' h => push_means (contents2 out' h) rfl ?_⟩
      intro Object Value Object' Value' I J obj known atoms lit num mom size place sim placed _ _ _
      exact disjoint_data_means sim placed (pairs roles rfl)

theorem data_domain_spec (context : data_ontology.Context) (p : DataProperty) (e : ClassExpression)
    (out : alloc.vec.Vec AnnotatedAxiom) : AxiomSpec.{u,v,w,x} context (.DataPropertyDomain p e) out := by
  rw [AxiomSpec, data_ontology.encode_axiom]
  obtain ⟨r1, run1, _⟩ := data_role_correct context p
  obtain ⟨r2, run2, means2⟩ := encode_class_meaning.{u,v,w,x} context e
  cases r1 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some rp =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some e' =>
      obtain ⟨r3, run3, facts3⟩ := nominal_objects_spec e out
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
      | some out1 =>
        obtain ⟨c3, p3⟩ := facts3 out1 rfl
        obtain ⟨r4, run4, contents4⟩ := push_spec out1 (.ObjectPropertyDomain rp e')
        refine ⟨r4, by simp [run1, run2, run3, run4], fun out' h => ?_⟩
        have inds : axiomIndividuals (.DataPropertyDomain p e) = classIndividuals e := rfl
        refine ⟨objectFacts (classIndividuals e) ++ [bare (.ObjectPropertyDomain rp e')],
          by rw [contents4 out' h, c3, List.append_assoc]; rfl, ?_, by rw [inds]; exact p3,
          fun J => names_of_facts (fun a m => by rw [inds] at m; exact m) (fun b m => by simp [m]) J⟩
        refine means_of_single (inds := classIndividuals e) (by intro b mem; simp at mem; tauto) (by simp)
          (fun a m => by rw [inds]; exact m) ?_
        intro Object Value Object' Value' I J obj known atoms lit num mom size place sim placed _ atomsIn indsIn
        exact data_domain_means sim placed run1 (means2 e' rfl) atomsIn indsIn

theorem data_range_spec (context : data_ontology.Context) (p : DataProperty) (r : DataRange)
    (out : alloc.vec.Vec AnnotatedAxiom) : AxiomSpec.{u,v,w,x} context (.DataPropertyRange p r) out := by
  rw [AxiomSpec, data_ontology.encode_axiom]
  obtain ⟨r1, run1, _⟩ := data_role_correct context p
  obtain ⟨r2, run2, means2⟩ := encode_range_meaning.{u,v,w,x} context r
  cases r1 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some rp =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some r' =>
      obtain ⟨r3, run3, contents3⟩ := push_spec out (.ObjectPropertyRange rp r')
      refine ⟨r3, by simp [run1, run2, run3], fun out' h => push_means (contents3 out' h) rfl ?_⟩
      intro Object Value Object' Value' I J obj known atoms lit num mom size place sim placed frame _ _
      exact data_range_means sim placed frame run1 (means2 r' rfl)

theorem functional_data_spec (context : data_ontology.Context) (p : DataProperty)
    (out : alloc.vec.Vec AnnotatedAxiom) : AxiomSpec.{u,v,w,x} context (.FunctionalDataProperty p) out := by
  rw [AxiomSpec, data_ontology.encode_axiom]
  obtain ⟨r1, run1, _⟩ := data_role_correct context p
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some rp =>
    obtain ⟨r2, run2, contents2⟩ := push_spec out (.FunctionalObjectProperty rp)
    refine ⟨r2, by simp [run1, run2], fun out' h => push_means (contents2 out' h) rfl ?_⟩
    intro Object Value Object' Value' I J obj known atoms lit num mom size place sim placed _ _ _
    exact functional_data_means sim placed run1

theorem individuals_spec (context : data_ontology.Context) (xs : AtLeastTwo Individual)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    AxiomSpec.{u,v,w,x} context (.SameIndividual xs) out ∧
      AxiomSpec.{u,v,w,x} context (.DifferentIndividuals xs) out := by
  obtain ⟨r1, run1, facts1⟩ := individual_members_spec xs
  constructor
  · rw [AxiomSpec, data_ontology.encode_axiom]
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some xs' =>
      obtain ⟨same, plain⟩ := facts1 xs' rfl
      subst xs'
      obtain ⟨r2, run2, contents2⟩ := push_spec out (.SameIndividual xs)
      cases r2 with
      | none => exact ⟨none, by simp [run1, run2], by simp⟩
      | some out1 =>
        obtain ⟨r3, run3, facts3⟩ := member_objects_spec xs out1
        refine ⟨r3, by simp [run1, run2, run3], fun out' h => ?_⟩
        obtain ⟨c3, _⟩ := facts3 out' h
        have inds : axiomIndividuals (.SameIndividual xs) = xs.elements := rfl
        refine ⟨bare (.SameIndividual xs) :: objectFacts xs.elements,
          by rw [c3, contents2 out1 rfl]; simp [bare], ?_, by rw [inds]; exact plain,
          fun J => names_of_facts (fun a m => by rw [inds] at m; exact m) (fun b m => by simp [m]) J⟩
        refine means_of_single (inds := xs.elements) (by intro b mem; simpa using mem) (by simp)
          (fun a m => by rw [inds]; exact m) ?_
        intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ _ indsIn
        have e := (same_individuals_means sim indsIn).1
        exact ⟨e.mp, fun _ => e.mpr⟩
  · rw [AxiomSpec, data_ontology.encode_axiom]
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some xs' =>
      obtain ⟨same, plain⟩ := facts1 xs' rfl
      subst xs'
      obtain ⟨r2, run2, contents2⟩ := push_spec out (.DifferentIndividuals xs)
      cases r2 with
      | none => exact ⟨none, by simp [run1, run2], by simp⟩
      | some out1 =>
        obtain ⟨r3, run3, facts3⟩ := member_objects_spec xs out1
        refine ⟨r3, by simp [run1, run2, run3], fun out' h => ?_⟩
        obtain ⟨c3, _⟩ := facts3 out' h
        have inds : axiomIndividuals (.DifferentIndividuals xs) = xs.elements := rfl
        refine ⟨bare (.DifferentIndividuals xs) :: objectFacts xs.elements,
          by rw [c3, contents2 out1 rfl]; simp [bare], ?_, by rw [inds]; exact plain,
          fun J => names_of_facts (fun a m => by rw [inds] at m; exact m) (fun b m => by simp [m]) J⟩
        refine means_of_single (inds := xs.elements) (by intro b mem; simpa using mem) (by simp)
          (fun a m => by rw [inds]; exact m) ?_
        intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ _ indsIn
        have e := (same_individuals_means sim indsIn).2
        exact ⟨e.mp, fun _ => e.mpr⟩

theorem class_assertion_spec (context : data_ontology.Context) (e : ClassExpression) (a : Individual)
    (out : alloc.vec.Vec AnnotatedAxiom) : AxiomSpec.{u,v,w,x} context (.ClassAssertion e a) out := by
  rw [AxiomSpec, data_ontology.encode_axiom]
  obtain ⟨r1, run1, means1⟩ := encode_class_meaning.{u,v,w,x} context e
  obtain ⟨r2, run2, _⟩ := object_individual_of_correct a
  cases r1 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some e' =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some a' =>
      obtain ⟨same, plainA⟩ := object_individual_of_some run2
      subst a'
      obtain ⟨r3, run3, facts3⟩ := nominal_objects_spec e out
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
      | some out1 =>
        obtain ⟨c3, p3⟩ := facts3 out1 rfl
        let main : Axiom := .ClassAssertion (.ObjectIntersectionOf ⟨e', .ObjectComplementOf (.Class dataClass),
          alloc.vec.Vec.new ClassExpression⟩) a
        obtain ⟨r4, run4, contents4⟩ := push_spec out1 main
        refine ⟨r4, by simp [run1, run2, run3, object_class_eq, data_ontology.and, run4, main], fun out' h => ?_⟩
        have inds : axiomIndividuals (.ClassAssertion e a) = a :: classIndividuals e := rfl
        refine ⟨objectFacts (classIndividuals e) ++ [bare main], by rw [contents4 out' h, c3, List.append_assoc]; rfl,
          ?_, ?_, ?_⟩
        · refine means_of_single (inds := classIndividuals e) (by intro b mem; simp at mem; tauto) (by simp)
            (fun b m => by rw [inds]; exact List.mem_cons_of_mem _ m) ?_
          intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ atomsIn indsIn
          have e := class_assertion_means sim (means1 e' rfl) atomsIn
            (fun b m => indsIn b (by rw [inds]; exact List.mem_cons_of_mem _ m)) (indsIn a (by rw [inds]; simp))
          exact ⟨e.mp, fun _ => e.mpr⟩
        · rw [inds]
          intro b mem
          rcases List.mem_cons.mp mem with rfl | later
          · exact plainA
          · exact p3 b later
        · intro Object' Value' J holds
          rw [inds]
          intro b mem
          rcases List.mem_cons.mp mem with rfl | later
          · have := holds (bare main) (by simp)
            simp only [bare, main, satisfies] at this
            rw [and_denote, object_class_denote] at this
            exact this.2
          · exact (object_facts_hold J _).mp (fun f m => holds f (by simp [m])) b later

theorem related_spec (role : ObjectPropertyExpression) (a b : Individual) (negative : Bool)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.related role a b negative out = .ok res ∧ ∀ out', res = some out' →
      Plain a ∧ Plain b ∧ out'.val = out.val ++ objectFacts [a, b] ++
        [bare (if negative then .NegativeObjectPropertyAssertion role a b else .ObjectPropertyAssertion role a b)] := by
  rw [data_ontology.related]
  obtain ⟨r1, run1, _⟩ := object_individual_of_correct a
  obtain ⟨r2, run2, _⟩ := object_individual_of_correct b
  cases r1 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some a' =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some b' =>
      obtain ⟨sameA, plainA⟩ := object_individual_of_some run1
      obtain ⟨sameB, plainB⟩ := object_individual_of_some run2
      subst a' b'
      obtain ⟨r3, run3, facts3⟩ := object_assertion_spec a out
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
      | some out1 =>
        obtain ⟨r4, run4, facts4⟩ := object_assertion_spec b out1
        cases r4 with
        | none => exact ⟨none, by simp [run1, run2, run3, run4], by simp⟩
        | some out2 =>
          obtain ⟨c3, _⟩ := facts3 out1 rfl
          obtain ⟨c4, _⟩ := facts4 out2 rfl
          cases negative with
          | true =>
            obtain ⟨r5, run5, contents5⟩ := push_spec out2 (.NegativeObjectPropertyAssertion role a b)
            refine ⟨r5, by simp [run1, run2, run3, run4, run5], fun out' h => ⟨plainA, plainB, ?_⟩⟩
            rw [contents5 out' h, c4, c3]
            simp [objectFacts, bare]
          | false =>
            obtain ⟨r5, run5, contents5⟩ := push_spec out2 (.ObjectPropertyAssertion role a b)
            refine ⟨r5, by simp [run1, run2, run3, run4, run5], fun out' h => ⟨plainA, plainB, ?_⟩⟩
            rw [contents5 out' h, c4, c3]
            simp [objectFacts, bare]

theorem object_assertions_axiom_spec (context : data_ontology.Context) (role : ObjectPropertyExpression)
    (a b : Individual) (out : alloc.vec.Vec AnnotatedAxiom) :
    AxiomSpec.{u,v,w,x} context (.ObjectPropertyAssertion role a b) out ∧
      AxiomSpec.{u,v,w,x} context (.NegativeObjectPropertyAssertion role a b) out := by
  obtain ⟨r1, run1, facts1⟩ := object_role_correct context role
  constructor
  · rw [AxiomSpec, data_ontology.encode_axiom]
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some copy =>
      obtain ⟨same, plain, ctx⟩ := facts1 copy rfl
      subst copy
      obtain ⟨r2, run2, facts2⟩ := related_spec role a b false out
      refine ⟨r2, by simp [run1, run2], fun out' h => ?_⟩
      obtain ⟨plainA, plainB, contents⟩ := facts2 out' h
      have inds : axiomIndividuals (.ObjectPropertyAssertion role a b) = [a, b] := rfl
      refine ⟨objectFacts [a, b] ++ [bare (.ObjectPropertyAssertion role a b)],
        by rw [contents, List.append_assoc]; rfl, ?_, by rw [inds]; simp [plainA, plainB],
        fun J => names_of_facts (fun c m => by rw [inds] at m; exact m) (fun f m => by simp [m]) J⟩
      refine means_of_single (inds := [a, b]) (by intro f mem; simp at mem; tauto) (by simp)
        (fun c m => by rw [inds]; exact m) ?_
      intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ _ indsIn
      have e := (object_assertion_means sim ⟨plain, ctx⟩ (indsIn a (by rw [inds]; simp))
        (indsIn b (by rw [inds]; simp))).1
      exact ⟨e.mp, fun _ => e.mpr⟩
  · rw [AxiomSpec, data_ontology.encode_axiom]
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some copy =>
      obtain ⟨same, plain, ctx⟩ := facts1 copy rfl
      subst copy
      obtain ⟨r2, run2, facts2⟩ := related_spec role a b true out
      refine ⟨r2, by simp [run1, run2], fun out' h => ?_⟩
      obtain ⟨plainA, plainB, contents⟩ := facts2 out' h
      have inds : axiomIndividuals (.NegativeObjectPropertyAssertion role a b) = [a, b] := rfl
      refine ⟨objectFacts [a, b] ++ [bare (.NegativeObjectPropertyAssertion role a b)],
        by rw [contents, List.append_assoc]; rfl, ?_, by rw [inds]; simp [plainA, plainB],
        fun J => names_of_facts (fun c m => by rw [inds] at m; exact m) (fun f m => by simp [m]) J⟩
      refine means_of_single (inds := [a, b]) (by intro f mem; simp at mem; tauto) (by simp)
        (fun c m => by rw [inds]; exact m) ?_
      intro Object Value Object' Value' I J obj known atoms lit num mom size place sim _ _ _ indsIn
      have e := (object_assertion_means sim ⟨plain, ctx⟩ (indsIn a (by rw [inds]; simp))
        (indsIn b (by rw [inds]; simp))).2
      exact ⟨e.mp, fun _ => e.mpr⟩

theorem valued_spec (role : ObjectPropertyExpression) (a value : Individual) (negative : Bool)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.valued role a value negative out = .ok res ∧ ∀ out', res = some out' →
      Plain a ∧ out'.val = out.val ++ objectFacts [a] ++
        [bare (if negative then .NegativeObjectPropertyAssertion role a value
          else .ObjectPropertyAssertion role a value)] := by
  rw [data_ontology.valued]
  obtain ⟨r1, run1, _⟩ := object_individual_of_correct a
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some a' =>
    obtain ⟨sameA, plainA⟩ := object_individual_of_some run1
    subst a'
    obtain ⟨r2, run2, facts2⟩ := object_assertion_spec a out
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some out1 =>
      obtain ⟨c2, _⟩ := facts2 out1 rfl
      cases negative with
      | true =>
        obtain ⟨r3, run3, contents3⟩ := push_spec out1 (.NegativeObjectPropertyAssertion role a value)
        refine ⟨r3, by simp [run1, run2, run3], fun out' h => ⟨plainA, ?_⟩⟩
        rw [contents3 out' h, c2]
        simp [bare]
      | false =>
        obtain ⟨r3, run3, contents3⟩ := push_spec out1 (.ObjectPropertyAssertion role a value)
        refine ⟨r3, by simp [run1, run2, run3], fun out' h => ⟨plainA, ?_⟩⟩
        rw [contents3 out' h, c2]
        simp [bare]

theorem data_assertions_spec (context : data_ontology.Context) (p : DataProperty) (a : Individual) (lt : Literal)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    AxiomSpec.{u,v,w,x} context (.DataPropertyAssertion p a lt) out ∧
      AxiomSpec.{u,v,w,x} context (.NegativeDataPropertyAssertion p a lt) out := by
  obtain ⟨r1, run1, _⟩ := data_role_correct context p
  obtain ⟨r2, run2, _⟩ := literal_individual_correct context lt
  constructor
  · rw [AxiomSpec, data_ontology.encode_axiom]
    cases r1 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some rp =>
      cases r2 with
      | none => exact ⟨none, by simp [run1, run2], by simp⟩
      | some lv =>
        obtain ⟨r3, run3, facts3⟩ := valued_spec rp a lv false out
        refine ⟨r3, by simp [run1, run2, run3], fun out' h => ?_⟩
        obtain ⟨plainA, contents⟩ := facts3 out' h
        have inds : axiomIndividuals (.DataPropertyAssertion p a lt) = [a] := rfl
        refine ⟨objectFacts [a] ++ [bare (.ObjectPropertyAssertion rp a lv)],
          by rw [contents, List.append_assoc]; rfl, ?_, by rw [inds]; simp [plainA],
          fun J => names_of_facts (fun c m => by rw [inds] at m; exact m) (fun f m => by simp [m]) J⟩
        refine means_of_single (inds := [a]) (by intro f mem; simp at mem; tauto) (by simp)
          (fun c m => by rw [inds]; exact m) ?_
        intro Object Value Object' Value' I J obj known atoms lit num mom size place sim placed _ _ indsIn
        have e := (data_assertion_means sim placed run1 run2 (indsIn a (by rw [inds]; simp))).1
        exact ⟨e.mp, fun _ => e.mpr⟩
  · rw [AxiomSpec, data_ontology.encode_axiom]
    cases r1 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some rp =>
      cases r2 with
      | none => exact ⟨none, by simp [run1, run2], by simp⟩
      | some lv =>
        obtain ⟨r3, run3, facts3⟩ := valued_spec rp a lv true out
        refine ⟨r3, by simp [run1, run2, run3], fun out' h => ?_⟩
        obtain ⟨plainA, contents⟩ := facts3 out' h
        have inds : axiomIndividuals (.NegativeDataPropertyAssertion p a lt) = [a] := rfl
        refine ⟨objectFacts [a] ++ [bare (.NegativeObjectPropertyAssertion rp a lv)],
          by rw [contents, List.append_assoc]; rfl, ?_, by rw [inds]; simp [plainA],
          fun J => names_of_facts (fun c m => by rw [inds] at m; exact m) (fun f m => by simp [m]) J⟩
        refine means_of_single (inds := [a]) (by intro f mem; simp at mem; tauto) (by simp)
          (fun c m => by rw [inds]; exact m) ?_
        intro Object Value Object' Value' I J obj known atoms lit num mom size place sim placed _ _ indsIn
        have e := (data_assertion_means sim placed run1 run2 (indsIn a (by rw [inds]; simp))).2
        exact ⟨e.mp, fun _ => e.mpr⟩

/-- The encoding of every axiom runs, and when it answers, it adds axioms that
    mean the axiom. -/
theorem encode_axiom_meaning (context : data_ontology.Context) (ax : Axiom) (out : alloc.vec.Vec AnnotatedAxiom) :
    AxiomSpec.{u,v,w,x} context ax out := by
  cases ax with
  | Declaration d =>
    exact keep_spec context _ out (by rw [data_ontology.encode_axiom]) rfl (fun _ _ _ _ _ _ _ _ _ => trivial)
  | SubClassOf sub sup => exact sub_class_spec context sub sup out
  | EquivalentClasses xs => exact (classes_spec context xs out).1
  | DisjointClasses xs => exact (classes_spec context xs out).2
  | DisjointUnion c xs => exact disjoint_union_spec context c xs out
  | SubObjectPropertyOf sub sup => exact sub_property_spec context sub sup out
  | EquivalentObjectProperties roles => exact equivalent_properties_spec context roles out
  | DisjointObjectProperties roles => exact disjoint_properties_spec context roles out
  | InverseObjectProperties p q => exact inverse_properties_spec context p q out
  | ObjectPropertyDomain role e => exact (domain_spec context role e out).1
  | ObjectPropertyRange role e => exact (domain_spec context role e out).2
  | FunctionalObjectProperty role => exact (characteristics_spec context role out).1
  | InverseFunctionalObjectProperty role => exact (characteristics_spec context role out).2.1
  | ReflexiveObjectProperty role => exact reflexive_spec context role out
  | IrreflexiveObjectProperty role => exact (characteristics_spec context role out).2.2.1
  | SymmetricObjectProperty role => exact (characteristics_spec context role out).2.2.2.1
  | AsymmetricObjectProperty role => exact (characteristics_spec context role out).2.2.2.2.1
  | TransitiveObjectProperty role => exact (characteristics_spec context role out).2.2.2.2.2
  | SubDataPropertyOf p q => exact sub_data_spec context p q out
  | EquivalentDataProperties ps => exact (data_lists_spec context ps out).1
  | DisjointDataProperties ps => exact (data_lists_spec context ps out).2
  | DataPropertyDomain p e => exact data_domain_spec context p e out
  | DataPropertyRange p r => exact data_range_spec context p r out
  | FunctionalDataProperty p => exact functional_data_spec context p out
  | DatatypeDefinition _ _ => exact ⟨none, by rw [data_ontology.encode_axiom], by simp⟩
  | HasKey _ _ _ => exact ⟨none, by rw [data_ontology.encode_axiom], by simp⟩
  | SameIndividual xs => exact (individuals_spec context xs out).1
  | DifferentIndividuals xs => exact (individuals_spec context xs out).2
  | ClassAssertion e a => exact class_assertion_spec context e a out
  | ObjectPropertyAssertion role a b => exact (object_assertions_axiom_spec context role a b out).1
  | NegativeObjectPropertyAssertion role a b => exact (object_assertions_axiom_spec context role a b out).2
  | DataPropertyAssertion p a lt => exact (data_assertions_spec context p a lt out).1
  | NegativeDataPropertyAssertion p a lt => exact (data_assertions_spec context p a lt out).2
  | AnnotationAssertion _ _ _ =>
    exact keep_spec context _ out (by rw [data_ontology.encode_axiom]) rfl (fun _ _ _ _ _ _ _ _ _ => trivial)
  | SubAnnotationPropertyOf _ _ =>
    exact keep_spec context _ out (by rw [data_ontology.encode_axiom]) rfl (fun _ _ _ _ _ _ _ _ _ => trivial)
  | AnnotationPropertyDomain _ _ =>
    exact keep_spec context _ out (by rw [data_ontology.encode_axiom]) rfl (fun _ _ _ _ _ _ _ _ _ => trivial)
  | AnnotationPropertyRange _ _ =>
    exact keep_spec context _ out (by rw [data_ontology.encode_axiom]) rfl (fun _ _ _ _ _ _ _ _ _ => trivial)

end Rowl.DataAxioms
