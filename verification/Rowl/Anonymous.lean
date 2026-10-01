import Rowl.OwlSemantics

namespace Rowl.Anonymous
open Aeneas Aeneas.Std RowlRust.model RowlRust.anonymous
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-- Named input individuals, independent of their IRI spelling or denotation. -/
def Named : Individual → Prop
  | .Named _ => True
  | .Anonymous _ => False

private theorem listN_mem_size {α : Type} [SizeOf α] {n : Nat}
    (xs : Aeneas.Data.ListN.ListN α n) {x : α} (h : x ∈ xs.toList) :
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
private theorem vec_mem_size {α : Type} [SizeOf α] (xs : alloc.vec.Vec α)
    {x : α} (h : x ∈ xs.val) : sizeOf x < sizeOf xs := by
  have := listN_mem_size xs.slice.list h
  cases xs with | mk slice => cases slice; simp_all [alloc.vec.Vec.val, Slice.val]; omega
private theorem first_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.first < sizeOf xs := by
  cases xs; simp +arith
private theorem second_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.second < sizeOf xs := by
  cases xs; simp +arith
private theorem rest_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.rest < sizeOf xs := by
  cases xs; simp +arith


/-- Positional restriction on every nested class expression (§11.2). -/
def ClassAllowed (expression : ClassExpression) : Prop :=
  match expression with
  | .Class _ => True
  | .ObjectIntersectionOf xs => ClassAllowed xs.first ∧ ClassAllowed xs.second ∧
      ∀ e : {e // e ∈ xs.rest.val}, ClassAllowed e.val
  | .ObjectUnionOf xs => ClassAllowed xs.first ∧ ClassAllowed xs.second ∧
      ∀ e : {e // e ∈ xs.rest.val}, ClassAllowed e.val
  | .ObjectComplementOf inner => ClassAllowed inner
  | .ObjectOneOf xs => ∀ i ∈ xs.elements, Named i
  | .ObjectSomeValuesFrom _ inner => ClassAllowed inner
  | .ObjectAllValuesFrom _ inner => ClassAllowed inner
  | .ObjectHasValue _ i => Named i
  | .ObjectHasSelf _ => True
  | .ObjectMinCardinality _ _ filler => ∀ inner ∈ filler, ClassAllowed inner
  | .ObjectMaxCardinality _ _ filler => ∀ inner ∈ filler, ClassAllowed inner
  | .ObjectExactCardinality _ _ filler => ∀ inner ∈ filler, ClassAllowed inner
  | .DataSomeValuesFrom _ _ => True
  | .DataAllValuesFrom _ _ => True
  | .DataHasValue _ _ => True
  | .DataMinCardinality _ _ _ => True
  | .DataMaxCardinality _ _ _ => True
  | .DataExactCardinality _ _ _ => True
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest e.property; have := rest_size xs; omega) |
    (cases filler <;> simp_all +arith)

/-- Logical-body positions; enclosing annotations are checked separately below. -/
def AxiomAllowed : Axiom → Prop
  | .Declaration _ => True
  | .SubClassOf a b => ClassAllowed a ∧ ClassAllowed b
  | .EquivalentClasses xs => ∀ e ∈ xs.elements, ClassAllowed e
  | .DisjointClasses xs => ∀ e ∈ xs.elements, ClassAllowed e
  | .DisjointUnion _ xs => ∀ e ∈ xs.elements, ClassAllowed e
  | .SubObjectPropertyOf _ _ => True
  | .EquivalentObjectProperties _ => True
  | .DisjointObjectProperties _ => True
  | .InverseObjectProperties _ _ => True
  | .ObjectPropertyDomain _ e => ClassAllowed e
  | .ObjectPropertyRange _ e => ClassAllowed e
  | .FunctionalObjectProperty _ => True
  | .InverseFunctionalObjectProperty _ => True
  | .ReflexiveObjectProperty _ => True
  | .IrreflexiveObjectProperty _ => True
  | .SymmetricObjectProperty _ => True
  | .AsymmetricObjectProperty _ => True
  | .TransitiveObjectProperty _ => True
  | .SubDataPropertyOf _ _ => True
  | .EquivalentDataProperties _ => True
  | .DisjointDataProperties _ => True
  | .DataPropertyDomain _ e => ClassAllowed e
  | .DataPropertyRange _ _ => True
  | .FunctionalDataProperty _ => True
  | .DatatypeDefinition _ _ => True
  | .HasKey e _ _ => ClassAllowed e
  | .SameIndividual xs => ∀ i ∈ xs.elements, Named i
  | .DifferentIndividuals xs => ∀ i ∈ xs.elements, Named i
  | .ClassAssertion e _ => ClassAllowed e
  | .ObjectPropertyAssertion _ _ _ => True
  | .NegativeObjectPropertyAssertion _ a b => Named a ∧ Named b
  | .DataPropertyAssertion _ _ _ => True
  | .NegativeDataPropertyAssertion _ i _ => Named i
  | .AnnotationAssertion _ _ _ => True
  | .SubAnnotationPropertyOf _ _ => True
  | .AnnotationPropertyDomain _ _ => True
  | .AnnotationPropertyRange _ _ => True

private theorem named_total (i : Individual) : named i = .ok (decide (Named i)) := by
  cases i <;> simp [named, Named]

private theorem vector_total {α : Type} (values : alloc.vec.Vec α)
    (visit : α → Result Bool) (allowed : α → Prop) (loop : Usize → Result Bool)
    (equation : ∀ index, loop index = do
      if index < values.len then
        let item ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) values index
        let accepted ← visit item
        if accepted then
          let next ← index + 1#usize
          loop next
        else .ok false
      else .ok true)
    (child : ∀ item ∈ values.val, visit item = .ok (decide (allowed item)))
    (index : Usize) :
    loop index = .ok (decide (∀ item ∈ values.val.drop index.val, allowed item)) := by
  rw [equation]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have accepted := child values.val[index.val] (List.getElem_mem inside)
    simp only [inside, alloc.vec.Vec.len_val, ↓reduceIte,
      alloc.vec.Vec.index_slice_index, lookup, bind_ok, accepted]
    by_cases head : allowed values.val[index.val]
    · simp only [head, decide_true, ↓reduceIte]
      obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have recurse := vector_total values visit allowed loop equation child next
      simp only [hn, bind_ok, recurse]
      simp [nextval, inside]
      have splitting : (∀ item ∈ values.val.drop index.val, allowed item) ↔
          allowed values.val[index.val] ∧ ∀ item ∈ values.val.drop (index.val + 1), allowed item := by
        rw [List.drop_eq_getElem_cons inside]
        exact List.forall_mem_cons
      rw [splitting]
      simp only [head, true_and]
    · simp [head, inside]
      refine ⟨values.val[index.val], ?_, head⟩
      rw [List.drop_eq_getElem_cons inside]
      exact List.mem_cons_self
  · have drop : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside, drop]
termination_by values.val.length - index.val
decreasing_by omega

private theorem individuals_total (values : alloc.vec.Vec Individual) (index : Usize) :
    individuals_from values index = .ok (decide (∀ i ∈ values.val.drop index.val, Named i)) :=
  vector_total values named Named (individuals_from values)
    (fun i => by rw [individuals_from]) (fun i _ => named_total i) index

private theorem classes_total_of (values : alloc.vec.Vec ClassExpression)
    (child : ∀ e ∈ values.val, class_positions_allowed e = .ok (decide (ClassAllowed e)))
    (index : Usize) :
    classes_from values index = .ok (decide (∀ e ∈ values.val.drop index.val, ClassAllowed e)) :=
  vector_total values class_positions_allowed ClassAllowed (classes_from values)
    (fun i => by rw [classes_from]) child index

private theorem subtype_forall {α : Type} (xs : List α) (p : α → Prop) :
    (∀ e : {e // e ∈ xs}, p e.val) ↔ ∀ e ∈ xs, p e := by
  constructor
  · intro all e mem; exact all ⟨e, mem⟩
  · intro all e; exact all e.val e.property

/-- No forbidden nested nominal/value position is missed by the Rust traversal. -/
theorem class_positions_total_correct (expression : ClassExpression) :
    class_positions_allowed expression = .ok (decide (ClassAllowed expression)) := by
  cases expression with
  | Class c => simp [class_positions_allowed, ClassAllowed]
  | ObjectHasSelf p => simp [class_positions_allowed, ClassAllowed]
  | DataSomeValuesFrom p r => simp [class_positions_allowed, ClassAllowed]
  | DataAllValuesFrom p r => simp [class_positions_allowed, ClassAllowed]
  | DataHasValue p l => simp [class_positions_allowed, ClassAllowed]
  | DataMinCardinality n p r => simp [class_positions_allowed, ClassAllowed]
  | DataMaxCardinality n p r => simp [class_positions_allowed, ClassAllowed]
  | DataExactCardinality n p r => simp [class_positions_allowed, ClassAllowed]
  | ObjectIntersectionOf xs | ObjectUnionOf xs =>
    have first := class_positions_total_correct xs.first
    have second := class_positions_total_correct xs.second
    have rest := classes_total_of xs.rest (fun e _ => class_positions_total_correct e) 0#usize
    by_cases f : ClassAllowed xs.first <;> by_cases g : ClassAllowed xs.second <;>
      simp [class_positions_allowed, ClassAllowed, first, second, rest, f, g, subtype_forall]
  | ObjectComplementOf e | ObjectSomeValuesFrom _ e | ObjectAllValuesFrom _ e =>
    simpa [class_positions_allowed, ClassAllowed] using class_positions_total_correct e
  | ObjectOneOf xs =>
    by_cases h : Named xs.first <;>
      simp [class_positions_allowed, ClassAllowed, NonEmpty.elements, named_total, individuals_total, h]
  | ObjectHasValue _ i => simp [class_positions_allowed, ClassAllowed, named_total]
  | ObjectMinCardinality n p filler | ObjectMaxCardinality n p filler | ObjectExactCardinality n p filler =>
    cases filler with
    | none => simp [class_positions_allowed, ClassAllowed]
    | some e => simpa [class_positions_allowed, ClassAllowed] using class_positions_total_correct e
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

private theorem classes_total (values : alloc.vec.Vec ClassExpression) (index : Usize) :
    classes_from values index = .ok (decide (∀ e ∈ values.val.drop index.val, ClassAllowed e)) :=
  classes_total_of values (fun e _ => class_positions_total_correct e) index

/-- Exact positional restrictions for every axiom form, including nested classes. -/
theorem axiom_positions_total_correct (item : Axiom) :
    axiom_positions_allowed item = .ok (decide (AxiomAllowed item)) := by
  cases item <;> simp [axiom_positions_allowed, AxiomAllowed,
    class_positions_total_correct, named_total, individuals_total, classes_total, AtLeastTwo.elements]
  all_goals repeat' split <;> simp_all

/-- Every anonymous value in the entire recursive annotation tree is excluded. -/
def NoAnonymousAnnotation (item : Annotation) : Prop :=
  match item with
  | .mk children _ value =>
    (match value with | .Anonymous _ => False | _ => True) ∧
    ∀ nested : {nested // nested ∈ children.val}, NoAnonymousAnnotation nested.val
termination_by sizeOf item
decreasing_by
  have := vec_mem_size children nested.property
  simp_wf
  omega

private theorem annotations_total_of (values : alloc.vec.Vec Annotation)
    (child : ∀ item ∈ values.val,
      annotation_has_no_anonymous item = .ok (decide (NoAnonymousAnnotation item)))
    (index : Usize) :
    annotations_from values index =
      .ok (decide (∀ item ∈ values.val.drop index.val, NoAnonymousAnnotation item)) :=
  vector_total values annotation_has_no_anonymous NoAnonymousAnnotation (annotations_from values)
    (fun i => by rw [annotations_from]) child index

/-- The recursive annotation scan terminates and misses no nested value. -/
theorem annotation_has_no_anonymous_total_correct (item : Annotation) :
    annotation_has_no_anonymous item = .ok (decide (NoAnonymousAnnotation item)) := by
  cases item with
  | mk children property value =>
    have nested := annotations_total_of children
      (fun a _ => annotation_has_no_anonymous_total_correct a) 0#usize
    cases value <;>
      simp [annotation_has_no_anonymous, NoAnonymousAnnotation, nested, subtype_forall]
termination_by sizeOf item
decreasing_by
  have := vec_mem_size children ‹_ ∈ _›
  simp_wf
  omega

/-- The four forbidden axiom types prohibit occurrences also in annotations. -/
def AnnotationPositionsAllowed (body : Axiom) (annotations : List Annotation) : Prop :=
  match body with
  | .SameIndividual _ | .DifferentIndividuals _
  | .NegativeObjectPropertyAssertion _ _ _ | .NegativeDataPropertyAssertion _ _ _ =>
    ∀ item ∈ annotations, NoAnonymousAnnotation item
  | _ => True

/-- Full §11.2 positional restriction on a supplied annotated axiom. -/
def AnnotatedAllowed (item : AnnotatedAxiom) : Prop :=
  AxiomAllowed item.axiom ∧ AnnotationPositionsAllowed item.axiom item.annotations.val

/-- Logical arguments and all relevant enclosing annotations are checked. -/
theorem annotated_axiom_positions_total_correct (item : AnnotatedAxiom) :
    annotated_axiom_positions_allowed item = .ok (decide (AnnotatedAllowed item)) := by
  have nested := annotations_total_of item.annotations
    (fun a _ => annotation_has_no_anonymous_total_correct a) 0#usize
  cases h : item.axiom <;>
    simp [annotated_axiom_positions_allowed, AnnotatedAllowed, AnnotationPositionsAllowed,
      h, axiom_positions_total_correct, nested]
  all_goals repeat' split <;> simp_all

/-- Every supplied closure axiom satisfies the anonymous positional rules. -/
def PositionsOK (axioms : List AnnotatedAxiom) : Prop :=
  ∀ item ∈ axioms, AnnotatedAllowed item

/-- First offending occurrence, preserving the complete annotated input axiom. -/
def FirstForbidden (axioms : List AnnotatedAxiom) (item : AnnotatedAxiom) : Prop :=
  ¬ AnnotatedAllowed item ∧ ∃ before after, axioms = before ++ item :: after ∧ PositionsOK before

private noncomputable def forbidden (item : AnnotatedAxiom) : Bool := decide (¬ AnnotatedAllowed item)

private theorem axioms_from_total (values : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    axioms_from values index = .ok ((values.val.drop index.val).find? forbidden) := by
  rw [axioms_from]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have foundStep : (values.val.drop index.val).find? forbidden =
        if AnnotatedAllowed values.val[index.val] then
          (values.val.drop (index.val + 1)).find? forbidden else some values.val[index.val] := by
      rw [List.drop_eq_getElem_cons inside]
      by_cases accepted : AnnotatedAllowed values.val[index.val] <;>
        simp only [List.find?_cons, forbidden, accepted, not_true_eq_false, not_false_eq_true,
          decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
    by_cases accepted : AnnotatedAllowed values.val[index.val]
    · obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have recurse := axioms_from_total values next
      simp [inside, alloc.vec.Vec.index_slice_index, lookup, annotated_axiom_positions_total_correct,
        accepted, hn, recurse, foundStep, nextval]
    · simp [inside, alloc.vec.Vec.index_slice_index, lookup, annotated_axiom_positions_total_correct,
        accepted, foundStep]
  · have drop : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside, drop]
termination_by values.val.length - index.val
decreasing_by omega

/-- The complete closure scan terminates and returns its exact first forbidden
    occurrence; annotations are carried through without modification. -/
theorem check_positions_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, check_positions axioms = .ok result ∧
      match result with
      | none => PositionsOK axioms.val
      | some item => FirstForbidden axioms.val item := by
  have total : check_positions axioms = .ok (axioms.val.find? forbidden) := by
    simpa [check_positions] using axioms_from_total axioms 0#usize
  refine ⟨axioms.val.find? forbidden, total, ?_⟩
  cases h : axioms.val.find? forbidden with
  | none =>
    simpa [PositionsOK, forbidden] using List.find?_eq_none.mp h
  | some item =>
    simpa [FirstForbidden, PositionsOK, forbidden] using List.find?_eq_some_iff_append.mp h

/-- No false acceptance or rejection of the specified positional restriction. -/
theorem check_positions_valid_iff (axioms : alloc.vec.Vec AnnotatedAxiom) :
    check_positions axioms = .ok none ↔ PositionsOK axioms.val := by
  have total : check_positions axioms = .ok (axioms.val.find? forbidden) := by
    simpa [check_positions] using axioms_from_total axioms 0#usize
  simp [total, List.find?_eq_none, forbidden, PositionsOK]

end Rowl.Anonymous
