import Rowl.OwlSemantics

/-! Independent ordered entity-occurrence specification. Only explicit entity
    positions count. This excludes headers, untyped annotation IRIs, facet IRIs
    and anonymous identifiers. IRI validation, interning, built-ins and DL
    validity are separate obligations. -/
namespace Rowl.Collection
open Aeneas Aeneas.Std RowlRust.model RowlRust.typing RowlRust.collection
abbrev Row := Iri × EntityKind

def rows : EntityUses → List Row
  | .Empty => []
  | .Entry iri kind next => (iri, kind) :: rows next
private def prepend : List Row → EntityUses → EntityUses
  | [], tail => tail
  | (iri, kind) :: xs, tail => .Entry iri kind (prepend xs tail)
private theorem prepend_append (xs ys : List Row) (tail : EntityUses) :
    prepend xs (prepend ys tail) = prepend (xs ++ ys) tail := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp [prepend, ih]
private theorem rows_prepend (xs : List Row) (tail : EntityUses) :
    rows (prepend xs tail) = xs ++ rows tail := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp [prepend, rows, ih]

def entityUses : Entity → List Row
  | .Class c => [(c.iri, .Class)]
  | .Datatype d => [(d.iri, .Datatype)]
  | .ObjectProperty p => [(p.iri, .ObjectProperty)]
  | .DataProperty p => [(p.iri, .DataProperty)]
  | .AnnotationProperty p => [(p.iri, .AnnotationProperty)]
  | .NamedIndividual i => [(i.iri, .NamedIndividual)]
def objectUses : ObjectPropertyExpression → List Row
  | .Property p | .Inverse p => [(p.iri, .ObjectProperty)]
def dataUses (p : DataProperty) : List Row := [(p.iri, .DataProperty)]
def individualUses : Individual → List Row
  | .Named i => [(i.iri, .NamedIndividual)]
  | .Anonymous _ => []
def literalUses (l : Literal) : List Row := [(l.datatype.iri, .Datatype)]
def facetUses (f : FacetRestriction) : List Row := literalUses f.value
def valueUses : AnnotationValue → List Row
  | .Literal l => literalUses l
  | .Iri _ | .Anonymous _ => []

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

def rangeUses (range : DataRange) : List Row :=
  match range with
  | .Datatype d => [(d.iri, .Datatype)]
  | .Intersection xs => rangeUses xs.first ++ rangeUses xs.second ++ xs.rest.val.attach.flatMap (fun e => rangeUses e.val)
  | .Union xs => rangeUses xs.first ++ rangeUses xs.second ++ xs.rest.val.attach.flatMap (fun e => rangeUses e.val)
  | .Complement e => rangeUses e
  | .OneOf xs => xs.elements.flatMap literalUses
  | .Restriction d xs => (d.iri, .Datatype) :: xs.elements.flatMap facetUses
termination_by sizeOf range
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest e.property; have := rest_size xs; omega)

def classUses (expression : ClassExpression) : List Row :=
  match expression with
  | .Class c => [(c.iri, .Class)]
  | .ObjectIntersectionOf xs => classUses xs.first ++ classUses xs.second ++ xs.rest.val.attach.flatMap (fun e => classUses e.val)
  | .ObjectUnionOf xs => classUses xs.first ++ classUses xs.second ++ xs.rest.val.attach.flatMap (fun e => classUses e.val)
  | .ObjectComplementOf e => classUses e
  | .ObjectOneOf xs => xs.elements.flatMap individualUses
  | .ObjectSomeValuesFrom p e => objectUses p ++ classUses e
  | .ObjectAllValuesFrom p e => objectUses p ++ classUses e
  | .ObjectHasValue p i => objectUses p ++ individualUses i
  | .ObjectHasSelf p => objectUses p
  | .ObjectMinCardinality _ p e => objectUses p ++ (match e with | none => [] | some c => classUses c)
  | .ObjectMaxCardinality _ p e => objectUses p ++ (match e with | none => [] | some c => classUses c)
  | .ObjectExactCardinality _ p e => objectUses p ++ (match e with | none => [] | some c => classUses c)
  | .DataSomeValuesFrom p r => dataUses p ++ rangeUses r
  | .DataAllValuesFrom p r => dataUses p ++ rangeUses r
  | .DataHasValue p l => dataUses p ++ literalUses l
  | .DataMinCardinality _ p r => dataUses p ++ (match r with | none => [] | some d => rangeUses d)
  | .DataMaxCardinality _ p r => dataUses p ++ (match r with | none => [] | some d => rangeUses d)
  | .DataExactCardinality _ p r => dataUses p ++ (match r with | none => [] | some d => rangeUses d)
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest e.property; have := rest_size xs; omega)

def annotationUses (annotation : Annotation) : List Row :=
  match annotation with
  | .mk nested property value => nested.val.attach.flatMap (fun e => annotationUses e.val) ++
      [(property.iri, .AnnotationProperty)] ++ valueUses value
termination_by sizeOf annotation
decreasing_by
  have := vec_mem_size nested e.property
  simp_wf
  omega

def subObjectUses : SubObjectPropertyExpression → List Row
  | .Single p => objectUses p
  | .Chain xs => xs.elements.flatMap objectUses

def axiomUses : Axiom → List Row
  | .Declaration e => entityUses e
  | .SubClassOf a b => classUses a ++ classUses b
  | .EquivalentClasses xs => xs.elements.flatMap classUses
  | .DisjointClasses xs => xs.elements.flatMap classUses
  | .DisjointUnion c xs => (c.iri, .Class) :: xs.elements.flatMap classUses
  | .SubObjectPropertyOf a b => subObjectUses a ++ objectUses b
  | .EquivalentObjectProperties xs => xs.elements.flatMap objectUses
  | .DisjointObjectProperties xs => xs.elements.flatMap objectUses
  | .InverseObjectProperties a b => objectUses a ++ objectUses b
  | .ObjectPropertyDomain p c => objectUses p ++ classUses c
  | .ObjectPropertyRange p c => objectUses p ++ classUses c
  | .FunctionalObjectProperty p => objectUses p
  | .InverseFunctionalObjectProperty p => objectUses p
  | .ReflexiveObjectProperty p => objectUses p
  | .IrreflexiveObjectProperty p => objectUses p
  | .SymmetricObjectProperty p => objectUses p
  | .AsymmetricObjectProperty p => objectUses p
  | .TransitiveObjectProperty p => objectUses p
  | .SubDataPropertyOf a b => dataUses a ++ dataUses b
  | .EquivalentDataProperties xs => xs.elements.flatMap dataUses
  | .DisjointDataProperties xs => xs.elements.flatMap dataUses
  | .DataPropertyDomain p c => dataUses p ++ classUses c
  | .DataPropertyRange p r => dataUses p ++ rangeUses r
  | .FunctionalDataProperty p => dataUses p
  | .DatatypeDefinition d r => (d.iri, .Datatype) :: rangeUses r
  | .HasKey c objects datas => classUses c ++ objects.val.flatMap objectUses ++ datas.val.flatMap dataUses
  | .SameIndividual xs => xs.elements.flatMap individualUses
  | .DifferentIndividuals xs => xs.elements.flatMap individualUses
  | .ClassAssertion c i => classUses c ++ individualUses i
  | .ObjectPropertyAssertion p a b => objectUses p ++ individualUses a ++ individualUses b
  | .NegativeObjectPropertyAssertion p a b => objectUses p ++ individualUses a ++ individualUses b
  | .DataPropertyAssertion p i l => dataUses p ++ individualUses i ++ literalUses l
  | .NegativeDataPropertyAssertion p i l => dataUses p ++ individualUses i ++ literalUses l
  | .AnnotationAssertion p _ v => (p.iri, .AnnotationProperty) :: valueUses v
  | .SubAnnotationPropertyOf a b => [(a.iri, .AnnotationProperty), (b.iri, .AnnotationProperty)]
  | .AnnotationPropertyDomain p _ => [(p.iri, .AnnotationProperty)]
  | .AnnotationPropertyRange p _ => [(p.iri, .AnnotationProperty)]

def annotatedUses (item : AnnotatedAxiom) : List Row :=
  item.annotations.val.flatMap annotationUses ++ axiomUses item.axiom

def declarationUses (item : AnnotatedAxiom) : List Row :=
  match item.axiom with | .Declaration e => entityUses e | _ => []

def Correct (ontology : RawOntology) (result : CollectedEntities) : Prop :=
  rows result.declarations = ontology.axioms.val.flatMap declarationUses ∧
  rows result.uses = ontology.annotations.val.flatMap annotationUses ++
    ontology.axioms.val.flatMap annotatedUses

private theorem entity_correct (e : Entity) (tail : EntityUses) :
    visit_entity e tail = .ok (prepend (entityUses e) tail) := by cases e <;> rfl
private theorem object_correct (p : ObjectPropertyExpression) (tail : EntityUses) :
    visit_object p tail = .ok (prepend (objectUses p) tail) := by cases p <;> simp [visit_object, entry, objectUses, prepend]
private theorem data_correct (p : DataProperty) (tail : EntityUses) :
    visit_data p tail = .ok (prepend (dataUses p) tail) := rfl
private theorem individual_correct (i : Individual) (tail : EntityUses) :
    visit_individual i tail = .ok (prepend (individualUses i) tail) := by cases i <;> rfl
private theorem literal_correct (l : Literal) (tail : EntityUses) :
    visit_literal l tail = .ok (prepend (literalUses l) tail) := rfl
private theorem facet_correct (f : FacetRestriction) (tail : EntityUses) :
    visit_facet f tail = .ok (prepend (facetUses f) tail) := rfl
private theorem value_correct (v : AnnotationValue) (tail : EntityUses) :
    visit_value v tail = .ok (prepend (valueUses v) tail) := by cases v <;> rfl

private theorem vector_correct {α : Type} (values : alloc.vec.Vec α)
    (visit : α → EntityUses → Result EntityUses) (uses : α → List Row)
    (loop : Usize → EntityUses → Result EntityUses)
    (equation : ∀ index tail, loop index tail = do
      if index < values.len then
        let next ← index + 1#usize
        let rest ← loop next tail
        let item ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) values index
        visit item rest
      else .ok tail)
    (child : ∀ item ∈ values.val, ∀ tail, visit item tail = .ok (prepend (uses item) tail))
    (index : Usize) (tail : EntityUses) :
    loop index tail = .ok (prepend ((values.val.drop index.val).flatMap uses) tail) := by
  rw [equation]
  by_cases h : index.val < values.val.length
  · have bound := values.property
    have addSpec := Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac)
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists addSpec
    have hi : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    have nextval : next.val = index.val + 1 := by simpa using hv
    have recurse := vector_correct values visit uses loop equation child next tail
    have head := child values.val[index.val] (List.getElem_mem h)
    simp [h, hn, recurse, alloc.vec.Vec.index_slice_index, hi, head, prepend_append]
    rw [List.drop_eq_getElem_cons h]
    simp only [nextval, List.flatMap_cons]
  · have drop : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [h, drop, prepend]
termination_by values.val.length - index.val
decreasing_by omega

private theorem objects_correct (values : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) (tail : EntityUses) :
    visit_objects values index tail = .ok (prepend ((values.val.drop index.val).flatMap objectUses) tail) := by
  exact vector_correct values visit_object objectUses (visit_objects values)
    (fun i t => by rw [visit_objects]) (fun x _ t => object_correct x t) index tail

private theorem datas_correct (values : alloc.vec.Vec DataProperty) (index : Usize) (tail : EntityUses) :
    visit_datas values index tail = .ok (prepend ((values.val.drop index.val).flatMap dataUses) tail) := by
  exact vector_correct values visit_data dataUses (visit_datas values)
    (fun i t => by rw [visit_datas]) (fun x _ t => data_correct x t) index tail

private theorem individuals_correct (values : alloc.vec.Vec Individual) (index : Usize) (tail : EntityUses) :
    visit_individuals values index tail = .ok (prepend ((values.val.drop index.val).flatMap individualUses) tail) := by
  exact vector_correct values visit_individual individualUses (visit_individuals values)
    (fun i t => by rw [visit_individuals]) (fun x _ t => individual_correct x t) index tail

private theorem literals_correct (values : alloc.vec.Vec Literal) (index : Usize) (tail : EntityUses) :
    visit_literals values index tail = .ok (prepend ((values.val.drop index.val).flatMap literalUses) tail) := by
  exact vector_correct values visit_literal literalUses (visit_literals values)
    (fun i t => by rw [visit_literals]) (fun x _ t => literal_correct x t) index tail

private theorem facets_correct (values : alloc.vec.Vec FacetRestriction) (index : Usize) (tail : EntityUses) :
    visit_facets values index tail = .ok (prepend ((values.val.drop index.val).flatMap facetUses) tail) := by
  exact vector_correct values visit_facet facetUses (visit_facets values)
    (fun i t => by rw [visit_facets]) (fun x _ t => facet_correct x t) index tail

private theorem ranges_correct_of (values : alloc.vec.Vec DataRange)
    (child : ∀ item ∈ values.val, ∀ tail, visit_range item tail = .ok (prepend (rangeUses item) tail))
    (index : Usize) (tail : EntityUses) :
    visit_ranges values index tail = .ok (prepend ((values.val.drop index.val).flatMap rangeUses) tail) := by
  exact vector_correct values visit_range rangeUses (visit_ranges values)
    (fun i t => by rw [visit_ranges]) child index tail

private theorem classes_correct_of (values : alloc.vec.Vec ClassExpression)
    (child : ∀ item ∈ values.val, ∀ tail, visit_class item tail = .ok (prepend (classUses item) tail))
    (index : Usize) (tail : EntityUses) :
    visit_classes values index tail = .ok (prepend ((values.val.drop index.val).flatMap classUses) tail) := by
  exact vector_correct values visit_class classUses (visit_classes values)
    (fun i t => by rw [visit_classes]) child index tail

private theorem annotations_correct_of (values : alloc.vec.Vec Annotation)
    (child : ∀ item ∈ values.val, ∀ tail, visit_annotation item tail = .ok (prepend (annotationUses item) tail))
    (index : Usize) (tail : EntityUses) :
    visit_annotations values index tail = .ok (prepend ((values.val.drop index.val).flatMap annotationUses) tail) := by
  exact vector_correct values visit_annotation annotationUses (visit_annotations values)
    (fun i t => by rw [visit_annotations]) child index tail

private theorem attached_flatMap {α : Type} (xs : List α) (f : α → List Row) :
    xs.attach.flatMap (fun e => f e.val) = xs.flatMap f := by
  simp

set_option linter.unusedSimpArgs false in
private theorem range_correct (range : DataRange) (tail : EntityUses) :
    visit_range range tail = .ok (prepend (rangeUses range) tail) := by
  cases range with
  | Datatype d => simp [visit_range, entry, rangeUses, prepend]
  | Intersection xs | Union xs =>
    have rest := ranges_correct_of xs.rest (fun item _ t => range_correct item t) 0#usize tail
    have first := range_correct xs.first
    have second := range_correct xs.second
    rw [visit_range]
    simp [rest, first, second, rangeUses, attached_flatMap, prepend_append]
  | Complement e =>
    rw [visit_range]
    simpa only [rangeUses] using range_correct e tail
  | OneOf xs =>
    rw [visit_range]
    simp [literals_correct, literal_correct, rangeUses, NonEmpty.elements, prepend_append]
  | Restriction d xs =>
    rw [visit_range]
    simp [facets_correct, facet_correct, entry, rangeUses, NonEmpty.elements, prepend, prepend_append]
termination_by sizeOf range
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

private theorem ranges_correct (values : alloc.vec.Vec DataRange) (index : Usize) (tail : EntityUses) :
    visit_ranges values index tail = .ok (prepend ((values.val.drop index.val).flatMap rangeUses) tail) :=
  ranges_correct_of values (fun item _ t => range_correct item t) index tail

set_option linter.unusedSimpArgs false in
private theorem class_correct (expression : ClassExpression) (tail : EntityUses) :
    visit_class expression tail = .ok (prepend (classUses expression) tail) := by
  cases expression with
  | Class c => simp [visit_class, entry, classUses, prepend]
  | ObjectIntersectionOf xs | ObjectUnionOf xs =>
    have rest := classes_correct_of xs.rest (fun item _ t => class_correct item t) 0#usize tail
    have first := class_correct xs.first
    have second := class_correct xs.second
    rw [visit_class]
    simp [rest, first, second, classUses, attached_flatMap, prepend_append]
  | ObjectComplementOf e =>
    rw [visit_class]
    simpa only [classUses] using class_correct e tail
  | ObjectOneOf xs =>
    rw [visit_class]
    simp [individuals_correct, individual_correct, classUses, NonEmpty.elements, prepend_append]
  | ObjectSomeValuesFrom p e | ObjectAllValuesFrom p e =>
    have child := class_correct e tail
    rw [visit_class]
    simp [child, object_correct, classUses, prepend_append]
  | ObjectHasValue p i =>
    rw [visit_class]
    simp [individual_correct, object_correct, classUses, prepend_append]
  | ObjectHasSelf p =>
    rw [visit_class]
    simpa only [classUses] using object_correct p tail
  | ObjectMinCardinality n p e | ObjectMaxCardinality n p e | ObjectExactCardinality n p e =>
    cases e with
    | none => rw [visit_class]; simp [object_correct, classUses, prepend]
    | some child =>
      have hc := class_correct child tail
      rw [visit_class]
      simp [hc, object_correct, classUses, prepend_append]
  | DataSomeValuesFrom p r | DataAllValuesFrom p r =>
    rw [visit_class]
    simp [range_correct, data_correct, classUses, prepend_append]
  | DataHasValue p l =>
    rw [visit_class]
    simp [literal_correct, data_correct, classUses, prepend_append]
  | DataMinCardinality n p r | DataMaxCardinality n p r | DataExactCardinality n p r =>
    cases r <;> rw [visit_class] <;>
      simp [range_correct, data_correct, classUses, prepend_append, prepend]
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

private theorem classes_correct (values : alloc.vec.Vec ClassExpression) (index : Usize) (tail : EntityUses) :
    visit_classes values index tail = .ok (prepend ((values.val.drop index.val).flatMap classUses) tail) :=
  classes_correct_of values (fun item _ t => class_correct item t) index tail

set_option linter.unusedSimpArgs false in
private theorem annotation_correct (annotation : Annotation) (tail : EntityUses) :
    visit_annotation annotation tail = .ok (prepend (annotationUses annotation) tail) := by
  cases annotation with
  | mk nested property value =>
    have rest := annotations_correct_of nested (fun item _ t => annotation_correct item t)
    rw [visit_annotation]
    simp [value_correct, entry, rest, annotationUses, attached_flatMap, prepend, prepend_append]
    rw [← prepend_append]
    rfl
termination_by sizeOf annotation
decreasing_by
  have := vec_mem_size nested ‹_ ∈ _›
  simp_wf
  omega

private theorem annotations_correct (values : alloc.vec.Vec Annotation) (index : Usize) (tail : EntityUses) :
    visit_annotations values index tail = .ok (prepend ((values.val.drop index.val).flatMap annotationUses) tail) :=
  annotations_correct_of values (fun item _ t => annotation_correct item t) index tail

set_option linter.unusedSimpArgs false in
private theorem sub_object_correct (sub : SubObjectPropertyExpression) (tail : EntityUses) :
    visit_sub_object sub tail = .ok (prepend (subObjectUses sub) tail) := by
  cases sub with
  | Single p => simpa only [visit_sub_object, subObjectUses] using object_correct p tail
  | Chain xs =>
    simp [visit_sub_object, objects_correct, object_correct, subObjectUses,
      AtLeastTwo.elements, prepend_append]

set_option linter.unusedSimpArgs false in
private theorem axiom_correct (item : Axiom) (tail : EntityUses) :
    visit_axiom item tail = .ok (prepend (axiomUses item) tail) := by
  cases item <;> rw [visit_axiom] <;>
    simp [entity_correct, class_correct, classes_correct, object_correct, objects_correct,
      sub_object_correct, data_correct, datas_correct, range_correct,
      individual_correct, individuals_correct, literal_correct, value_correct,
      entry, axiomUses, AtLeastTwo.elements, prepend_append, prepend]

private theorem annotated_correct (item : AnnotatedAxiom) (tail : EntityUses) :
    visit_annotated item tail = .ok (prepend (annotatedUses item) tail) := by
  simp [visit_annotated, axiom_correct, annotations_correct, annotatedUses, prepend_append]

private theorem axioms_correct (values : alloc.vec.Vec AnnotatedAxiom) (index : Usize) (tail : EntityUses) :
    visit_axioms values index tail = .ok (prepend ((values.val.drop index.val).flatMap annotatedUses) tail) := by
  exact vector_correct values visit_annotated annotatedUses (visit_axioms values)
    (fun i t => by rw [visit_axioms]) (fun x _ t => annotated_correct x t) index tail

private theorem declarations_correct (values : alloc.vec.Vec AnnotatedAxiom) (index : Usize) (tail : EntityUses) :
    visit_declarations values index tail = .ok (prepend ((values.val.drop index.val).flatMap declarationUses) tail) := by
  let visit := fun (item : AnnotatedAxiom) (t : EntityUses) =>
    match item.axiom with | .Declaration e => visit_entity e t | _ => .ok t
  apply vector_correct values visit declarationUses (visit_declarations values)
  · intro i t
    rw [visit_declarations]
    simp only [visit]
    split
    · congr 1
      funext next
      congr 1
      funext rest
      congr 1
      funext item
      cases item.axiom <;> rfl
    · rfl
  · intro item _ t
    cases h : item.axiom <;> simp [visit, declarationUses, h, entity_correct, prepend]

/-- Exact occurrence sequence, including duplicates and literal datatype roles. -/
theorem class_entities_total_correct (expression : ClassExpression) :
    ∃ result, class_entities expression = .ok result ∧ rows result = classUses expression := by
  exact ⟨prepend (classUses expression) .Empty, class_correct expression .Empty,
    by simp [rows_prepend, rows]⟩

theorem range_entities_total_correct (range : DataRange) :
    ∃ result, range_entities range = .ok result ∧ rows result = rangeUses range := by
  exact ⟨prepend (rangeUses range) .Empty, range_correct range .Empty,
    by simp [rows_prepend, rows]⟩

theorem entity_entities_total_correct (entity : Entity) :
    ∃ result, entity_entities entity = .ok result ∧ rows result = entityUses entity := by
  exact ⟨prepend (entityUses entity) .Empty, entity_correct entity .Empty,
    by simp [rows_prepend, rows]⟩

theorem annotation_entities_total_correct (annotation : Annotation) :
    ∃ result, annotation_entities annotation = .ok result ∧ rows result = annotationUses annotation := by
  exact ⟨prepend (annotationUses annotation) .Empty, annotation_correct annotation .Empty,
    by simp [rows_prepend, rows]⟩

theorem axiom_entities_total_correct (item : AnnotatedAxiom) :
    ∃ result, axiom_entities item = .ok result ∧ rows result = annotatedUses item := by
  exact ⟨prepend (annotatedUses item) .Empty, annotated_correct item .Empty,
    by simp [rows_prepend, rows]⟩

/-- Both tables match the raw ontology exactly; headers/import IRIs contribute
    neither declarations nor uses. Totality includes finite cyclic import tags,
    since this operation traverses only the supplied finite syntax tree. -/
theorem ontology_entities_total_correct (ontology : RawOntology) :
    ∃ result, ontology_entities ontology = .ok result ∧ Correct ontology result := by
  refine ⟨{
      declarations := prepend (ontology.axioms.val.flatMap declarationUses) .Empty,
      uses := prepend (ontology.annotations.val.flatMap annotationUses ++
        ontology.axioms.val.flatMap annotatedUses) .Empty }, ?_, ?_⟩
  · simp [ontology_entities, axioms_correct, annotations_correct, declarations_correct, prepend_append]
  · simp [Correct, rows_prepend, rows]

def AxiomClosureCorrect (ontology : RawOntology) (result : CollectedEntities) : Prop :=
  rows result.declarations = ontology.axioms.val.flatMap declarationUses ∧
  rows result.uses = ontology.axioms.val.flatMap annotatedUses

/-- The typing input includes axiom annotations, excludes ontology annotations,
    and preserves every explicit occurrence in the supplied axiom list. -/
theorem axiom_closure_entities_total_correct (ontology : RawOntology) :
    ∃ result, axiom_closure_entities ontology = .ok result ∧ AxiomClosureCorrect ontology result := by
  refine ⟨{
      declarations := prepend (ontology.axioms.val.flatMap declarationUses) .Empty,
      uses := prepend (ontology.axioms.val.flatMap annotatedUses) .Empty }, ?_, ?_⟩
  · simp [axiom_closure_entities, axioms_correct, declarations_correct]
  · simp [AxiomClosureCorrect, rows_prepend, rows]

end Rowl.Collection
