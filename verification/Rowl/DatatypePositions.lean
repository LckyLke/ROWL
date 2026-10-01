import Rowl.DatatypeDefinitions

namespace Rowl.DatatypePositions
open Aeneas Aeneas.Std RowlRust.model RowlRust.datatype_positions
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- Actual defined datatype names in the complete supplied raw closure. -/
def Defined (axioms : List AnnotatedAxiom) (datatype : Iri) : Prop :=
  ∃ item ∈ axioms, Rowl.DatatypeDefinitions.Defines item datatype

/-- Defined datatypes have empty lexical spaces, so cannot type literals. -/
def LiteralAllowed (axioms : List AnnotatedAxiom) (literal : Literal) : Prop :=
  ¬ Defined axioms literal.datatype.iri

def FacetAllowed (axioms : List AnnotatedAxiom) (facet : FacetRestriction) : Prop :=
  LiteralAllowed axioms facet.value

def ValueAllowed (axioms : List AnnotatedAxiom) : AnnotationValue → Prop
  | .Literal literal => LiteralAllowed axioms literal
  | .Iri _ | .Anonymous _ => True

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


/-- Defined datatypes may be named ranges, but cannot be restriction bases.
    Enumeration and facet literals, and every nested range member, are checked. -/
def RangeAllowed (axioms : List AnnotatedAxiom) (range : DataRange) : Prop :=
  match range with
  | .Datatype _ => True
  | .Intersection xs | .Union xs => RangeAllowed axioms xs.first ∧ RangeAllowed axioms xs.second ∧
      ∀ e : {e // e ∈ xs.rest.val}, RangeAllowed axioms e.val
  | .Complement inner => RangeAllowed axioms inner
  | .OneOf xs => ∀ literal ∈ xs.elements, LiteralAllowed axioms literal
  | .Restriction datatype xs => ¬ Defined axioms datatype.iri ∧
      ∀ facet ∈ xs.elements, FacetAllowed axioms facet
termination_by sizeOf range
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest e.property; have := rest_size xs; omega)

def ClassAllowed (axioms : List AnnotatedAxiom) (expression : ClassExpression) : Prop :=
  match expression with
  | .Class _ => True
  | .ObjectIntersectionOf xs => ClassAllowed axioms xs.first ∧ ClassAllowed axioms xs.second ∧
      ∀ e : {e // e ∈ xs.rest.val}, ClassAllowed axioms e.val
  | .ObjectUnionOf xs => ClassAllowed axioms xs.first ∧ ClassAllowed axioms xs.second ∧
      ∀ e : {e // e ∈ xs.rest.val}, ClassAllowed axioms e.val
  | .ObjectComplementOf inner => ClassAllowed axioms inner
  | .ObjectOneOf _ => True
  | .ObjectSomeValuesFrom _ inner => ClassAllowed axioms inner
  | .ObjectAllValuesFrom _ inner => ClassAllowed axioms inner
  | .ObjectHasValue _ _ => True
  | .ObjectHasSelf _ => True
  | .ObjectMinCardinality _ _ filler => ∀ inner ∈ filler, ClassAllowed axioms inner
  | .ObjectMaxCardinality _ _ filler => ∀ inner ∈ filler, ClassAllowed axioms inner
  | .ObjectExactCardinality _ _ filler => ∀ inner ∈ filler, ClassAllowed axioms inner
  | .DataSomeValuesFrom _ range => RangeAllowed axioms range
  | .DataAllValuesFrom _ range => RangeAllowed axioms range
  | .DataHasValue _ literal => LiteralAllowed axioms literal
  | .DataMinCardinality _ _ filler => ∀ range ∈ filler, RangeAllowed axioms range
  | .DataMaxCardinality _ _ filler => ∀ range ∈ filler, RangeAllowed axioms range
  | .DataExactCardinality _ _ filler => ∀ range ∈ filler, RangeAllowed axioms range
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest e.property; have := rest_size xs; omega) |
    (cases filler <;> simp_all +arith)

/-- Recursive annotation literals are covered, including enclosing metadata. -/
def AnnotationAllowed (axioms : List AnnotatedAxiom) (item : Annotation) : Prop :=
  match item with
  | .mk children _ value => ValueAllowed axioms value ∧
      ∀ nested : {nested // nested ∈ children.val}, AnnotationAllowed axioms nested.val
termination_by sizeOf item
decreasing_by
  have := vec_mem_size children nested.property
  simp_wf
  omega

def BodyAllowed (axioms : List AnnotatedAxiom) : Axiom → Prop
  | .Declaration _ => True
  | .SubClassOf a b => ClassAllowed axioms a ∧ ClassAllowed axioms b
  | .EquivalentClasses xs => ∀ e ∈ xs.elements, ClassAllowed axioms e
  | .DisjointClasses xs => ∀ e ∈ xs.elements, ClassAllowed axioms e
  | .DisjointUnion _ xs => ∀ e ∈ xs.elements, ClassAllowed axioms e
  | .SubObjectPropertyOf _ _ => True
  | .EquivalentObjectProperties _ => True
  | .DisjointObjectProperties _ => True
  | .InverseObjectProperties _ _ => True
  | .ObjectPropertyDomain _ e => ClassAllowed axioms e
  | .ObjectPropertyRange _ e => ClassAllowed axioms e
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
  | .DataPropertyDomain _ e => ClassAllowed axioms e
  | .DataPropertyRange _ range => RangeAllowed axioms range
  | .FunctionalDataProperty _ => True
  | .DatatypeDefinition _ range => RangeAllowed axioms range
  | .HasKey e _ _ => ClassAllowed axioms e
  | .SameIndividual _ => True
  | .DifferentIndividuals _ => True
  | .ClassAssertion e _ => ClassAllowed axioms e
  | .ObjectPropertyAssertion _ _ _ => True
  | .NegativeObjectPropertyAssertion _ _ _ => True
  | .DataPropertyAssertion _ _ literal => LiteralAllowed axioms literal
  | .NegativeDataPropertyAssertion _ _ literal => LiteralAllowed axioms literal
  | .AnnotationAssertion _ _ value => ValueAllowed axioms value
  | .SubAnnotationPropertyOf _ _ => True
  | .AnnotationPropertyDomain _ _ => True
  | .AnnotationPropertyRange _ _ => True

def AnnotatedAllowed (axioms : List AnnotatedAxiom) (item : AnnotatedAxiom) : Prop :=
  BodyAllowed axioms item.axiom ∧ ∀ annotation ∈ item.annotations.val, AnnotationAllowed axioms annotation

def ClosureOK (axioms : List AnnotatedAxiom) : Prop := ∀ item ∈ axioms, AnnotatedAllowed axioms item

def FirstForbidden (axioms : List AnnotatedAxiom) (item : AnnotatedAxiom) : Prop :=
  ¬ AnnotatedAllowed axioms item ∧ ∃ before after, axioms = before ++ item :: after ∧
    ∀ prior ∈ before, AnnotatedAllowed axioms prior

def FirstAnnotation (axioms : List AnnotatedAxiom) (annotations : List Annotation) (item : Annotation) : Prop :=
  ¬ AnnotationAllowed axioms item ∧ ∃ before after, annotations = before ++ item :: after ∧
    ∀ prior ∈ before, AnnotationAllowed axioms prior

def OntologyOK (ontology : RawOntology) : Prop :=
  (∀ annotation ∈ ontology.annotations.val, AnnotationAllowed ontology.axioms.val annotation) ∧
    ClosureOK ontology.axioms.val

def Correct (ontology : RawOntology) : PositionCheck → Prop
  | .Allowed => OntologyOK ontology
  | .OntologyAnnotation item => FirstAnnotation ontology.axioms.val ontology.annotations.val item ∧ ¬ OntologyOK ontology
  | .Axiom item => (∀ annotation ∈ ontology.annotations.val, AnnotationAllowed ontology.axioms.val annotation) ∧
      FirstForbidden ontology.axioms.val item ∧ ¬ OntologyOK ontology

private theorem defined_from_total (axioms : alloc.vec.Vec AnnotatedAxiom) (datatype : Iri) (index : Usize) :
    defined_from axioms datatype index = .ok (decide (Defined (axioms.val.drop index.val) datatype)) := by
  rw [defined_from]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have split : Defined (axioms.val.drop index.val) datatype ↔
        Rowl.DatatypeDefinitions.Defines axioms.val[index.val] datatype ∨
        Defined (axioms.val.drop (index.val+1)) datatype := by
      rw [List.drop_eq_getElem_cons inside]
      constructor
      · rintro ⟨item,member,defined⟩
        rcases List.mem_cons.mp member with rfl | member
        · exact Or.inl defined
        · exact Or.inr ⟨item,member,defined⟩
      · rintro (defined | ⟨item,member,defined⟩)
        · exact ⟨_,List.mem_cons_self,defined⟩
        · exact ⟨item,List.mem_cons_of_mem _ member,defined⟩
    have splitBool : decide (Defined (axioms.val.drop index.val) datatype) =
        decide (Rowl.DatatypeDefinitions.Defines axioms.val[index.val] datatype ∨
          Defined (axioms.val.drop (index.val+1)) datatype) := decide_eq_decide.mpr split
    rw [splitBool]
    by_cases head : Rowl.DatatypeDefinitions.Defines axioms.val[index.val] datatype
    · simp [inside,alloc.vec.Vec.index_slice_index,lookup,Rowl.DatatypeDefinitions.defines_total_correct,head]
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using nextval
      have recursive := defined_from_total axioms datatype next
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,Rowl.DatatypeDefinitions.defines_total_correct,head,advance,recursive,nv]
  · have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty,Defined]
termination_by axioms.val.length - index.val
decreasing_by omega

/-- Defined datatype recognition is total and exact on original raw axiom names. -/
theorem defined_datatype_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) (datatype : Iri) :
    defined_datatype axioms datatype = .ok (decide (Defined axioms.val datatype)) := by
  simpa [defined_datatype] using defined_from_total axioms datatype 0#usize

/-- Literal typing excludes exactly the datatypes with actual defining axioms. -/
theorem literal_allowed_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) (literal : Literal) :
    literal_allowed axioms literal = .ok (decide (LiteralAllowed axioms.val literal)) := by
  by_cases defined : Defined axioms.val literal.datatype.iri <;>
    simp [literal_allowed,LiteralAllowed,defined_datatype_total_correct,defined]

private theorem facet_total (axioms : alloc.vec.Vec AnnotatedAxiom) (facet : FacetRestriction) :
    facet_allowed axioms facet = .ok (decide (FacetAllowed axioms.val facet)) := by
  simp [facet_allowed,FacetAllowed,literal_allowed_total_correct]

private theorem value_total (axioms : alloc.vec.Vec AnnotatedAxiom) (value : AnnotationValue) :
    value_allowed axioms value = .ok (decide (ValueAllowed axioms.val value)) := by
  cases value <;> simp [value_allowed,ValueAllowed,literal_allowed_total_correct]

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

private theorem subtype_forall {α : Type} (xs : List α) (p : α → Prop) :
    (∀ e : {e // e ∈ xs}, p e.val) ↔ ∀ e ∈ xs, p e := by
  constructor
  · intro all e mem; exact all ⟨e, mem⟩
  · intro all e; exact all e.val e.property

private theorem literals_total (axioms : alloc.vec.Vec AnnotatedAxiom) (values : alloc.vec.Vec Literal) (index : Usize) :
    literals_from axioms values index = .ok (decide (∀ item ∈ values.val.drop index.val, LiteralAllowed axioms.val item)) :=
  vector_total values (literal_allowed axioms) (LiteralAllowed axioms.val) (literals_from axioms values)
    (fun i => by rw [literals_from]) (fun item _ => literal_allowed_total_correct axioms item) index

private theorem facets_total (axioms : alloc.vec.Vec AnnotatedAxiom) (values : alloc.vec.Vec FacetRestriction) (index : Usize) :
    facets_from axioms values index = .ok (decide (∀ item ∈ values.val.drop index.val, FacetAllowed axioms.val item)) :=
  vector_total values (facet_allowed axioms) (FacetAllowed axioms.val) (facets_from axioms values)
    (fun i => by rw [facets_from]) (fun item _ => facet_total axioms item) index

private theorem ranges_total_of (axioms : alloc.vec.Vec AnnotatedAxiom) (values : alloc.vec.Vec DataRange)
    (child : ∀ item ∈ values.val, range_allowed axioms item = .ok (decide (RangeAllowed axioms.val item))) (index : Usize) :
    ranges_from axioms values index = .ok (decide (∀ item ∈ values.val.drop index.val, RangeAllowed axioms.val item)) :=
  vector_total values (range_allowed axioms) (RangeAllowed axioms.val) (ranges_from axioms values)
    (fun i => by rw [ranges_from]) child index

private theorem classes_total_of (axioms : alloc.vec.Vec AnnotatedAxiom) (values : alloc.vec.Vec ClassExpression)
    (child : ∀ item ∈ values.val, class_allowed axioms item = .ok (decide (ClassAllowed axioms.val item))) (index : Usize) :
    classes_from axioms values index = .ok (decide (∀ item ∈ values.val.drop index.val, ClassAllowed axioms.val item)) :=
  vector_total values (class_allowed axioms) (ClassAllowed axioms.val) (classes_from axioms values)
    (fun i => by rw [classes_from]) child index

private theorem annotations_total_of (axioms : alloc.vec.Vec AnnotatedAxiom) (values : alloc.vec.Vec Annotation)
    (child : ∀ item ∈ values.val, annotation_allowed axioms item = .ok (decide (AnnotationAllowed axioms.val item))) (index : Usize) :
    annotations_from axioms values index = .ok (decide (∀ item ∈ values.val.drop index.val, AnnotationAllowed axioms.val item)) :=
  vector_total values (annotation_allowed axioms) (AnnotationAllowed axioms.val) (annotations_from axioms values)
    (fun i => by rw [annotations_from]) child index

/-- Every range constructor and nested literal/base position is checked exactly. -/
theorem range_allowed_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) (range : DataRange) :
    range_allowed axioms range = .ok (decide (RangeAllowed axioms.val range)) := by
  cases range with
  | Datatype _ => simp [range_allowed,RangeAllowed]
  | Intersection xs | Union xs =>
    have first := range_allowed_total_correct axioms xs.first
    have second := range_allowed_total_correct axioms xs.second
    have rest := ranges_total_of axioms xs.rest (fun e _ => range_allowed_total_correct axioms e) 0#usize
    by_cases f : RangeAllowed axioms.val xs.first <;> by_cases g : RangeAllowed axioms.val xs.second <;>
      simp [range_allowed,RangeAllowed,first,second,rest,f,g,subtype_forall]
  | Complement inner => simpa [range_allowed,RangeAllowed] using range_allowed_total_correct axioms inner
  | OneOf xs =>
    by_cases f : LiteralAllowed axioms.val xs.first <;>
      simp [range_allowed,RangeAllowed,NonEmpty.elements,literal_allowed_total_correct,literals_total,f]
  | Restriction datatype xs =>
    by_cases d : Defined axioms.val datatype.iri <;> by_cases f : FacetAllowed axioms.val xs.first <;>
      simp [range_allowed,RangeAllowed,NonEmpty.elements,defined_datatype_total_correct,facet_total,facets_total,d,f]
termination_by sizeOf range
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

/-- Exact custom-datatype positions in all class forms and optional fillers. -/
theorem class_allowed_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) (expression : ClassExpression) :
    class_allowed axioms expression = .ok (decide (ClassAllowed axioms.val expression)) := by
  cases expression with
  | Class c => simp [class_allowed, ClassAllowed]
  | ObjectHasSelf p => simp [class_allowed, ClassAllowed]
  | DataSomeValuesFrom p r => simp [class_allowed, ClassAllowed,range_allowed_total_correct]
  | DataAllValuesFrom p r => simp [class_allowed, ClassAllowed,range_allowed_total_correct]
  | DataHasValue p l => simp [class_allowed, ClassAllowed,literal_allowed_total_correct]
  | DataMinCardinality n p r => cases r <;> simp [class_allowed,ClassAllowed,range_allowed_total_correct]
  | DataMaxCardinality n p r => cases r <;> simp [class_allowed,ClassAllowed,range_allowed_total_correct]
  | DataExactCardinality n p r => cases r <;> simp [class_allowed,ClassAllowed,range_allowed_total_correct]
  | ObjectIntersectionOf xs | ObjectUnionOf xs =>
    have first := class_allowed_total_correct axioms xs.first
    have second := class_allowed_total_correct axioms xs.second
    have rest := classes_total_of axioms xs.rest (fun e _ => class_allowed_total_correct axioms e) 0#usize
    by_cases f : ClassAllowed axioms.val xs.first <;> by_cases g : ClassAllowed axioms.val xs.second <;>
      simp [class_allowed, ClassAllowed, first, second, rest, f, g, subtype_forall]
  | ObjectComplementOf e | ObjectSomeValuesFrom _ e | ObjectAllValuesFrom _ e =>
    simpa [class_allowed, ClassAllowed] using class_allowed_total_correct axioms e
  | ObjectOneOf _ | ObjectHasValue _ _ => simp [class_allowed,ClassAllowed]
  | ObjectMinCardinality n p filler | ObjectMaxCardinality n p filler | ObjectExactCardinality n p filler =>
    cases filler with
    | none => simp [class_allowed, ClassAllowed]
    | some e => simpa [class_allowed, ClassAllowed] using class_allowed_total_correct axioms e
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

private theorem classes_total (axioms : alloc.vec.Vec AnnotatedAxiom) (values : alloc.vec.Vec ClassExpression) (index : Usize) :
    classes_from axioms values index = .ok (decide (∀ item ∈ values.val.drop index.val, ClassAllowed axioms.val item)) :=
  classes_total_of axioms values (fun item _ => class_allowed_total_correct axioms item) index

/-- Nested annotations have no omitted literal positions. -/
theorem annotation_allowed_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) (item : Annotation) :
    annotation_allowed axioms item = .ok (decide (AnnotationAllowed axioms.val item)) := by
  cases item with
  | mk children property value =>
    have nested := annotations_total_of axioms children (fun a _ => annotation_allowed_total_correct axioms a) 0#usize
    by_cases head : ValueAllowed axioms.val value <;>
      simp [annotation_allowed,AnnotationAllowed,nested,value_total,head,subtype_forall]
termination_by sizeOf item
decreasing_by
  have := vec_mem_size children ‹_ ∈ _›
  simp_wf
  omega

private theorem annotations_total (axioms : alloc.vec.Vec AnnotatedAxiom) (values : alloc.vec.Vec Annotation) (index : Usize) :
    annotations_from axioms values index = .ok (decide (∀ item ∈ values.val.drop index.val, AnnotationAllowed axioms.val item)) :=
  annotations_total_of axioms values (fun item _ => annotation_allowed_total_correct axioms item) index

/-- Every axiom constructor is covered, including data/negative/annotation assertions. -/
theorem body_allowed_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) (body : Axiom) :
    body_allowed axioms body = .ok (decide (BodyAllowed axioms.val body)) := by
  cases body <;> simp [body_allowed,BodyAllowed,class_allowed_total_correct,range_allowed_total_correct,
    literal_allowed_total_correct,value_total,classes_total,AtLeastTwo.elements]
  all_goals repeat' split <;> simp_all

/-- Logical body and all enclosing annotation literals are checked together. -/
theorem axiom_allowed_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) (item : AnnotatedAxiom) :
    axiom_allowed axioms item = .ok (decide (AnnotatedAllowed axioms.val item)) := by
  by_cases body : BodyAllowed axioms.val item.axiom <;>
    simp [axiom_allowed,AnnotatedAllowed,body_allowed_total_correct,annotations_total,body]


private theorem first_total {α : Type} (values : alloc.vec.Vec α)
    (visit : α → Result Bool) (allowed : α → Prop) (loop : Usize → Result (Option α))
    (equation : ∀ index, loop index = do
      if index < values.len then
        let item ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) values index
        let accepted ← visit item
        if accepted then
          let next ← index + 1#usize
          loop next
        else .ok (some item)
      else .ok none)
    (child : ∀ item ∈ values.val, visit item = .ok (decide (allowed item)))
    (index : Usize) :
    loop index = .ok ((values.val.drop index.val).find? (fun item => decide (¬ allowed item))) := by
  rw [equation]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have foundStep : (values.val.drop index.val).find? (fun item => decide (¬ allowed item)) =
        if allowed values.val[index.val] then
          (values.val.drop (index.val + 1)).find? (fun item => decide (¬ allowed item)) else some values.val[index.val] := by
      rw [List.drop_eq_getElem_cons inside]
      by_cases accepted : allowed values.val[index.val] <;>
        simp only [List.find?_cons,  accepted, not_true_eq_false, not_false_eq_true,
          decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
    rw [foundStep]
    by_cases accepted : allowed values.val[index.val]
    · obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have recurse := first_total values visit allowed loop equation child next
      simp [inside, alloc.vec.Vec.index_slice_index, lookup, child _ (List.getElem_mem inside),
        accepted, hn, recurse, foundStep, nextval]
    · simp [inside, alloc.vec.Vec.index_slice_index, lookup, child _ (List.getElem_mem inside),
        accepted, foundStep]
  · have drop : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside, drop]
termination_by values.val.length - index.val
decreasing_by omega

private noncomputable def forbidden (axioms : List AnnotatedAxiom) (item : AnnotatedAxiom) : Bool :=
  decide (¬ AnnotatedAllowed axioms item)
private noncomputable def bad_annotation (axioms : List AnnotatedAxiom) (item : Annotation) : Bool :=
  decide (¬ AnnotationAllowed axioms item)

private theorem axioms_total (axioms : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    axioms_from axioms index = .ok ((axioms.val.drop index.val).find? (forbidden axioms.val)) := by
  exact first_total axioms (axiom_allowed axioms) (AnnotatedAllowed axioms.val) (axioms_from axioms)
    (fun i => by rw [axioms_from]) (fun item _ => axiom_allowed_total_correct axioms item) index

private theorem first_annotation_total (axioms : alloc.vec.Vec AnnotatedAxiom)
    (annotations : alloc.vec.Vec Annotation) (index : Usize) :
    first_annotation axioms annotations index =
      .ok ((annotations.val.drop index.val).find? (bad_annotation axioms.val)) := by
  exact first_total annotations (annotation_allowed axioms) (AnnotationAllowed axioms.val)
    (first_annotation axioms annotations) (fun i => by rw [first_annotation])
    (fun item _ => annotation_allowed_total_correct axioms item) index

/-- Whole-closure scanning is total and returns the exact original first
    forbidden annotated axiom; definitions can occur after their uses. -/
theorem check_positions_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, check_positions axioms = .ok result ∧
      match result with
      | none => ClosureOK axioms.val
      | some item => FirstForbidden axioms.val item := by
  have total : check_positions axioms = .ok (axioms.val.find? (forbidden axioms.val)) := by
    simpa [check_positions] using axioms_total axioms 0#usize
  refine ⟨axioms.val.find? (forbidden axioms.val),total,?_⟩
  cases found : axioms.val.find? (forbidden axioms.val) with
  | none => simpa [ClosureOK,forbidden] using List.find?_eq_none.mp found
  | some item => simpa [FirstForbidden,forbidden] using List.find?_eq_some_iff_append.mp found

/-- Complete acceptance of the defined-datatype positions on the supplied closure. -/
theorem check_positions_valid_iff (axioms : alloc.vec.Vec AnnotatedAxiom) :
    check_positions axioms = .ok none ↔ ClosureOK axioms.val := by
  have total : check_positions axioms = .ok (axioms.val.find? (forbidden axioms.val)) := by
    simpa [check_positions] using axioms_total axioms 0#usize
  simp [total,List.find?_eq_none,forbidden,ClosureOK]

/-- The actual ontology operation checks all supplied ontology annotations before
    axiom positions, retaining exact original first failures and proving rejection. -/
theorem check_ontology_positions_total_correct (ontology : RawOntology) :
    ∃ result, check_ontology_positions ontology = .ok result ∧ Correct ontology result := by
  have annotationsChecked : first_annotation ontology.axioms ontology.annotations 0#usize =
      .ok (ontology.annotations.val.find? (bad_annotation ontology.axioms.val)) := by
    simpa using first_annotation_total ontology.axioms ontology.annotations 0#usize
  cases found : ontology.annotations.val.find? (bad_annotation ontology.axioms.val) with
  | some item =>
    have first : FirstAnnotation ontology.axioms.val ontology.annotations.val item := by
      simpa [FirstAnnotation,bad_annotation] using List.find?_eq_some_iff_append.mp found
    refine ⟨.OntologyAnnotation item,by simp [check_ontology_positions,annotationsChecked,found],first,?_⟩
    intro valid
    obtain ⟨bad,before,after,sequence,_⟩ := first
    exact bad (valid.1 item (by simp [sequence]))
  | none =>
    have annotationsOK : ∀ item ∈ ontology.annotations.val, AnnotationAllowed ontology.axioms.val item := by
      simpa [bad_annotation] using List.find?_eq_none.mp found
    obtain ⟨result,executed,correct⟩ := check_positions_total_correct ontology.axioms
    cases result with
    | none => exact ⟨.Allowed,by simp [check_ontology_positions,annotationsChecked,found,executed],annotationsOK,correct⟩
    | some item =>
      refine ⟨.Axiom item,by simp [check_ontology_positions,annotationsChecked,found,executed],annotationsOK,correct,?_⟩
      intro valid
      obtain ⟨bad,before,after,sequence,_⟩ := correct
      exact bad (valid.2 item (by simp [sequence]))

/-- Exact acceptance on supplied ontology annotations and the complete raw closure.
    Other datatype and DL validation conditions remain separate. -/
theorem check_ontology_positions_valid_iff (ontology : RawOntology) :
    check_ontology_positions ontology = .ok .Allowed ↔ OntologyOK ontology := by
  obtain ⟨result,executed,correct⟩ := check_ontology_positions_total_correct ontology
  rw [executed]
  cases result with
  | Allowed => simp [Correct] at correct; simp [correct]
  | OntologyAnnotation item => simp [Correct] at correct; simp [correct.2]
  | Axiom item => simp [Correct] at correct; simp [correct.2.2]

end Rowl.DatatypePositions
