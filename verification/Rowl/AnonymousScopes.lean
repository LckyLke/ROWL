import Rowl.OwlSemantics
import Rowl.DlValidity

/-!
Anonymous individuals of one scope, and why scopes keep documents apart.

An import closure reads every document with a scope of its own (OWL 2
Structural Specification §5.6.2). `ScopedClass`, `ScopedAxiom`,
`ScopedAnnotation` and `ScopedOntology` say that every anonymous individual of a
class expression, axiom, annotation (nested ones included) or ontology has a
given scope; the checks of `anonymous_scopes.rs` decide them exactly
(`scoped_class_correct`, `scoped_axiom_correct`, `scoped_annotation_correct`,
`scoped_ontology_correct`).

The Direct Semantics interprets anonymous individuals by an assignment that a
model may choose (§2.4, `Rowl.Owl.modelsClosure`). `class_coincide` and
`axiom_coincide` prove that the meaning of a scoped class expression or axiom
depends only on what the assignment gives the anonymous individuals of the
scope. Hence `models_parts`: for axiom lists whose anonymous individuals have
pairwise distinct scopes, an interpretation is a model of their concatenation
exactly when it is a model of each list, each with an assignment of its own.
This is the meaning of standardizing anonymous individuals apart (§3.4).
-/
namespace Rowl.AnonymousScopes
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model RowlRust.anonymous_scopes
open Rowl.Owl (Interpretation individual objectRelation classDenote dataDenote satisfies satisfiesClosure
  modelsClosure withAnonymous allEqual pairwiseDisjoint AtLeast AtMost Exactly chainRelation subRelation)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v

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

/-! ## Scoped syntax -/

/-- A named individual, or an anonymous individual of the scope. -/
def ScopedIndividual (s : List U8) : Individual → Prop
  | .Named _ => True
  | .Anonymous a => a.scope.val = s

/-- Every individual of an enumeration or value restriction in the class
    expression, nested ones included, is named or of the scope. -/
def ScopedClass (s : List U8) (expression : ClassExpression) : Prop :=
  match expression with
  | .Class _ => True
  | .ObjectIntersectionOf xs => ScopedClass s xs.first ∧ ScopedClass s xs.second ∧
      ∀ e : {e // e ∈ xs.rest.val}, ScopedClass s e.val
  | .ObjectUnionOf xs => ScopedClass s xs.first ∧ ScopedClass s xs.second ∧
      ∀ e : {e // e ∈ xs.rest.val}, ScopedClass s e.val
  | .ObjectComplementOf inner => ScopedClass s inner
  | .ObjectOneOf xs => ∀ i ∈ xs.elements, ScopedIndividual s i
  | .ObjectSomeValuesFrom _ inner => ScopedClass s inner
  | .ObjectAllValuesFrom _ inner => ScopedClass s inner
  | .ObjectHasValue _ i => ScopedIndividual s i
  | .ObjectHasSelf _ => True
  | .ObjectMinCardinality _ _ filler => ∀ inner ∈ filler, ScopedClass s inner
  | .ObjectMaxCardinality _ _ filler => ∀ inner ∈ filler, ScopedClass s inner
  | .ObjectExactCardinality _ _ filler => ∀ inner ∈ filler, ScopedClass s inner
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

/-- An IRI, a literal or an anonymous individual of the scope. -/
def ScopedValue (s : List U8) : AnnotationValue → Prop
  | .Anonymous a => a.scope.val = s
  | _ => True

/-- An IRI or an anonymous individual of the scope. -/
def ScopedSubject (s : List U8) : AnnotationSubject → Prop
  | .Anonymous a => a.scope.val = s
  | .Iri _ => True

/-- The annotation's value and those of its nested annotations are IRIs,
    literals or anonymous individuals of the scope. -/
def ScopedAnnotation (s : List U8) (item : Annotation) : Prop :=
  match item with
  | .mk children _ value =>
    ScopedValue s value ∧ ∀ nested : {nested // nested ∈ children.val}, ScopedAnnotation s nested.val
termination_by sizeOf item
decreasing_by
  have := vec_mem_size children nested.property
  simp_wf
  omega

/-- Every individual of the axiom is named or of the scope. -/
def ScopedAxiom (s : List U8) : Axiom → Prop
  | .Declaration _ => True
  | .SubClassOf a b => ScopedClass s a ∧ ScopedClass s b
  | .EquivalentClasses xs => ∀ e ∈ xs.elements, ScopedClass s e
  | .DisjointClasses xs => ∀ e ∈ xs.elements, ScopedClass s e
  | .DisjointUnion _ xs => ∀ e ∈ xs.elements, ScopedClass s e
  | .SubObjectPropertyOf _ _ => True
  | .EquivalentObjectProperties _ => True
  | .DisjointObjectProperties _ => True
  | .InverseObjectProperties _ _ => True
  | .ObjectPropertyDomain _ e => ScopedClass s e
  | .ObjectPropertyRange _ e => ScopedClass s e
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
  | .DataPropertyDomain _ e => ScopedClass s e
  | .DataPropertyRange _ _ => True
  | .FunctionalDataProperty _ => True
  | .DatatypeDefinition _ _ => True
  | .HasKey e _ _ => ScopedClass s e
  | .SameIndividual xs => ∀ i ∈ xs.elements, ScopedIndividual s i
  | .DifferentIndividuals xs => ∀ i ∈ xs.elements, ScopedIndividual s i
  | .ClassAssertion e i => ScopedClass s e ∧ ScopedIndividual s i
  | .ObjectPropertyAssertion _ a b => ScopedIndividual s a ∧ ScopedIndividual s b
  | .NegativeObjectPropertyAssertion _ a b => ScopedIndividual s a ∧ ScopedIndividual s b
  | .DataPropertyAssertion _ a _ => ScopedIndividual s a
  | .NegativeDataPropertyAssertion _ a _ => ScopedIndividual s a
  | .AnnotationAssertion _ subject value => ScopedSubject s subject ∧ ScopedValue s value
  | .SubAnnotationPropertyOf _ _ => True
  | .AnnotationPropertyDomain _ _ => True
  | .AnnotationPropertyRange _ _ => True

/-- The axiom and its annotations are scoped. -/
def ScopedAnnotated (s : List U8) (item : AnnotatedAxiom) : Prop :=
  (∀ a ∈ item.annotations.val, ScopedAnnotation s a) ∧ ScopedAxiom s item.axiom

/-- Every anonymous individual of the ontology's annotations and axioms has the
    scope. -/
def ScopedOntology (s : List U8) (o : RawOntology) : Prop :=
  (∀ a ∈ o.annotations.val, ScopedAnnotation s a) ∧ ∀ item ∈ o.axioms.val, ScopedAnnotated s item

/-! ## The checks decide them -/

private theorem anonymous_total (scope : alloc.vec.Vec U8) (a : AnonymousIndividual) :
    scoped_anonymous scope a = .ok (decide (a.scope.val = scope.val)) := by
  simp [scoped_anonymous, Rowl.DlValidity.same_bytes_spec]

private theorem individual_total (scope : alloc.vec.Vec U8) (i : Individual) :
    scoped_individual scope i = .ok (decide (ScopedIndividual scope.val i)) := by
  cases i <;> simp [scoped_individual, ScopedIndividual, anonymous_total]

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

private theorem individuals_total (scope : alloc.vec.Vec U8) (values : alloc.vec.Vec Individual) (index : Usize) :
    individuals_from scope values index =
      .ok (decide (∀ i ∈ values.val.drop index.val, ScopedIndividual scope.val i)) :=
  vector_total values (scoped_individual scope) (ScopedIndividual scope.val) (individuals_from scope values)
    (fun i => by rw [individuals_from]) (fun i _ => individual_total scope i) index

private theorem classes_total_of (scope : alloc.vec.Vec U8) (values : alloc.vec.Vec ClassExpression)
    (child : ∀ e ∈ values.val, scoped_class scope e = .ok (decide (ScopedClass scope.val e)))
    (index : Usize) :
    classes_from scope values index = .ok (decide (∀ e ∈ values.val.drop index.val, ScopedClass scope.val e)) :=
  vector_total values (scoped_class scope) (ScopedClass scope.val) (classes_from scope values)
    (fun i => by rw [classes_from]) child index

private theorem subtype_forall {α : Type} (xs : List α) (p : α → Prop) :
    (∀ e : {e // e ∈ xs}, p e.val) ↔ ∀ e ∈ xs, p e := by
  constructor
  · intro all e mem; exact all ⟨e, mem⟩
  · intro all e; exact all e.val e.property

/-- The class check visits every nested enumeration and value restriction. -/
theorem scoped_class_correct (scope : alloc.vec.Vec U8) (expression : ClassExpression) :
    scoped_class scope expression = .ok (decide (ScopedClass scope.val expression)) := by
  cases expression with
  | Class c => simp [scoped_class, ScopedClass]
  | ObjectHasSelf p => simp [scoped_class, ScopedClass]
  | DataSomeValuesFrom p r => simp [scoped_class, ScopedClass]
  | DataAllValuesFrom p r => simp [scoped_class, ScopedClass]
  | DataHasValue p l => simp [scoped_class, ScopedClass]
  | DataMinCardinality n p r => simp [scoped_class, ScopedClass]
  | DataMaxCardinality n p r => simp [scoped_class, ScopedClass]
  | DataExactCardinality n p r => simp [scoped_class, ScopedClass]
  | ObjectIntersectionOf xs | ObjectUnionOf xs =>
    have first := scoped_class_correct scope xs.first
    have second := scoped_class_correct scope xs.second
    have rest := classes_total_of scope xs.rest (fun e _ => scoped_class_correct scope e) 0#usize
    by_cases f : ScopedClass scope.val xs.first <;> by_cases g : ScopedClass scope.val xs.second <;>
      simp [scoped_class, ScopedClass, first, second, rest, f, g, subtype_forall]
  | ObjectComplementOf e | ObjectSomeValuesFrom _ e | ObjectAllValuesFrom _ e =>
    simpa [scoped_class, ScopedClass] using scoped_class_correct scope e
  | ObjectOneOf xs =>
    by_cases h : ScopedIndividual scope.val xs.first <;>
      simp [scoped_class, ScopedClass, NonEmpty.elements, individual_total, individuals_total, h]
  | ObjectHasValue _ i => simp [scoped_class, ScopedClass, individual_total]
  | ObjectMinCardinality n p filler | ObjectMaxCardinality n p filler | ObjectExactCardinality n p filler =>
    cases filler with
    | none => simp [scoped_class, ScopedClass]
    | some e => simpa [scoped_class, ScopedClass] using scoped_class_correct scope e
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

private theorem classes_total (scope : alloc.vec.Vec U8) (values : alloc.vec.Vec ClassExpression) (index : Usize) :
    classes_from scope values index = .ok (decide (∀ e ∈ values.val.drop index.val, ScopedClass scope.val e)) :=
  classes_total_of scope values (fun e _ => scoped_class_correct scope e) index

private theorem value_total (scope : alloc.vec.Vec U8) (value : AnnotationValue) :
    scoped_value scope value = .ok (decide (ScopedValue scope.val value)) := by
  cases value <;> simp [scoped_value, ScopedValue, anonymous_total]

private theorem subject_total (scope : alloc.vec.Vec U8) (subject : AnnotationSubject) :
    scoped_subject scope subject = .ok (decide (ScopedSubject scope.val subject)) := by
  cases subject <;> simp [scoped_subject, ScopedSubject, anonymous_total]

private theorem annotations_total_of (scope : alloc.vec.Vec U8) (values : alloc.vec.Vec Annotation)
    (child : ∀ item ∈ values.val, scoped_annotation scope item = .ok (decide (ScopedAnnotation scope.val item)))
    (index : Usize) :
    annotations_from scope values index =
      .ok (decide (∀ item ∈ values.val.drop index.val, ScopedAnnotation scope.val item)) :=
  vector_total values (scoped_annotation scope) (ScopedAnnotation scope.val) (annotations_from scope values)
    (fun i => by rw [annotations_from]) child index

/-- The annotation check visits every nested annotation. -/
theorem scoped_annotation_correct (scope : alloc.vec.Vec U8) (item : Annotation) :
    scoped_annotation scope item = .ok (decide (ScopedAnnotation scope.val item)) := by
  cases item with
  | mk children property value =>
    have nested := annotations_total_of scope children
      (fun a _ => scoped_annotation_correct scope a) 0#usize
    rw [scoped_annotation]
    by_cases v : ScopedValue scope.val value
    · simp [value_total, v, nested, ScopedAnnotation, subtype_forall]
    · simp [value_total, v, ScopedAnnotation]
termination_by sizeOf item
decreasing_by
  have := vec_mem_size children ‹_ ∈ _›
  simp_wf
  omega

private theorem annotations_total (scope : alloc.vec.Vec U8) (values : alloc.vec.Vec Annotation) (index : Usize) :
    annotations_from scope values index =
      .ok (decide (∀ item ∈ values.val.drop index.val, ScopedAnnotation scope.val item)) :=
  annotations_total_of scope values (fun a _ => scoped_annotation_correct scope a) index

/-- The axiom check visits every individual of every axiom form. -/
theorem scoped_axiom_correct (scope : alloc.vec.Vec U8) (item : Axiom) :
    scoped_axiom scope item = .ok (decide (ScopedAxiom scope.val item)) := by
  cases item <;> simp [scoped_axiom, ScopedAxiom, scoped_class_correct, individual_total, individuals_total,
    classes_total, value_total, subject_total, AtLeastTwo.elements]
  all_goals repeat' split <;> simp_all

/-- The annotated-axiom check visits the axiom and its annotations. -/
theorem scoped_annotated_correct (scope : alloc.vec.Vec U8) (item : AnnotatedAxiom) :
    scoped_annotated scope item = .ok (decide (ScopedAnnotated scope.val item)) := by
  rw [scoped_annotated]
  have nested := annotations_total scope item.annotations 0#usize
  simp only [show (0#usize : Usize).val = 0 by simp, List.drop_zero] at nested
  rw [nested]
  by_cases a : ∀ x ∈ item.annotations.val, ScopedAnnotation scope.val x
  · simp only [bind_ok, decide_eq_true a, ↓reduceIte, scoped_axiom_correct]
    exact congrArg Result.ok (decide_eq_decide.mpr ⟨fun h => ⟨a, h⟩, fun h => h.2⟩)
  · simp only [bind_ok, decide_eq_false a, Bool.false_eq_true, ↓reduceIte]
    exact congrArg Result.ok (decide_eq_false (fun h : ScopedAnnotated scope.val item => a h.1)).symm

private theorem axioms_total (scope : alloc.vec.Vec U8) (values : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    axioms_from scope values index =
      .ok (decide (∀ item ∈ values.val.drop index.val, ScopedAnnotated scope.val item)) :=
  vector_total values (scoped_annotated scope) (ScopedAnnotated scope.val) (axioms_from scope values)
    (fun i => by rw [axioms_from]) (fun item _ => scoped_annotated_correct scope item) index

/-- The ontology check visits the ontology annotations and every axiom. -/
theorem scoped_ontology_correct (scope : alloc.vec.Vec U8) (o : RawOntology) :
    scoped_ontology scope o = .ok (decide (ScopedOntology scope.val o)) := by
  rw [scoped_ontology]
  have nested := annotations_total scope o.annotations 0#usize
  have axioms := axioms_total scope o.axioms 0#usize
  simp only [show (0#usize : Usize).val = 0 by simp, List.drop_zero] at nested axioms
  rw [nested]
  by_cases a : ∀ x ∈ o.annotations.val, ScopedAnnotation scope.val x
  · simp only [bind_ok, decide_eq_true a, ↓reduceIte, axioms]
    exact congrArg Result.ok (decide_eq_decide.mpr ⟨fun h => ⟨a, h⟩, fun h => h.2⟩)
  · simp only [bind_ok, decide_eq_false a, Bool.false_eq_true, ↓reduceIte]
    exact congrArg Result.ok (decide_eq_false (fun h : ScopedOntology scope.val o => a h.1)).symm

/-! ## Meaning depends only on the scope's anonymous individuals -/

variable {Object : Type u} {Value : Type v}

/-- Two assignments agree on the anonymous individuals of the scope. -/
def Agree (s : List U8) (A B : AnonymousIndividual → Object) : Prop :=
  ∀ a : AnonymousIndividual, a.scope.val = s → A a = B a

private theorem individual_coincide (I : Interpretation Object Value) {s : List U8}
    {A B : AnonymousIndividual → Object} (agree : Agree s A B) (i : Individual) (inScope : ScopedIndividual s i) :
    individual (withAnonymous I A) i = individual (withAnonymous I B) i := by
  cases i with
  | Named a => rfl
  | Anonymous a => exact agree a inScope

private theorem relation_same (I : Interpretation Object Value) (A B : AnonymousIndividual → Object)
    (p : ObjectPropertyExpression) :
    objectRelation (withAnonymous I A) p = objectRelation (withAnonymous I B) p := by
  cases p <;> rfl

private theorem data_same (I : Interpretation Object Value) (A B : AnonymousIndividual → Object)
    (r : DataRange) (y : Value) :
    dataDenote (withAnonymous I A) r y ↔ dataDenote (withAnonymous I B) r y := by
  cases r with
  | Datatype dt => simp only [dataDenote]; rfl
  | Intersection xs =>
    have first := data_same I A B xs.first y
    have second := data_same I A B xs.second y
    have rest : ∀ e ∈ xs.rest.val, (dataDenote (withAnonymous I A) e y ↔ dataDenote (withAnonymous I B) e y) :=
      fun e member => data_same I A B e y
    simp only [dataDenote]
    exact and_congr first (and_congr second (forall₂_congr fun e member => rest e member))
  | Union xs =>
    have first := data_same I A B xs.first y
    have second := data_same I A B xs.second y
    have rest : ∀ e ∈ xs.rest.val, (dataDenote (withAnonymous I A) e y ↔ dataDenote (withAnonymous I B) e y) :=
      fun e member => data_same I A B e y
    simp only [dataDenote]
    exact or_congr first (or_congr second (exists_congr fun e => exists_congr fun member => rest e member))
  | Complement e =>
    simp only [dataDenote]
    exact not_congr (data_same I A B e y)
  | OneOf xs => simp only [dataDenote]; rfl
  | Restriction dt xs => simp only [dataDenote]; rfl
termination_by sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

private theorem lower_congr {α : Type u} (n : Nat) {P Q : α → Prop} (same : ∀ x, P x ↔ Q x) :
    AtLeast n P ↔ AtLeast n Q := by
  have equal : P = Q := funext fun x => propext (same x)
  rw [equal]

private theorem upper_congr {α : Type u} (n : Nat) {P Q : α → Prop} (same : ∀ x, P x ↔ Q x) :
    AtMost n P ↔ AtMost n Q := by
  have equal : P = Q := funext fun x => propext (same x)
  rw [equal]

private theorem exact_congr {α : Type u} (n : Nat) {P Q : α → Prop} (same : ∀ x, P x ↔ Q x) :
    Exactly n P ↔ Exactly n Q := by
  have equal : P = Q := funext fun x => propext (same x)
  rw [equal]

/-- The filler condition of an object number restriction. -/
private def classFiller (I : Interpretation Object Value) (filler : Option ClassExpression) (y : Object) : Prop :=
  match filler with
  | none => True
  | some c => classDenote I c y

/-- The filler condition of a data number restriction. -/
private def rangeFiller (I : Interpretation Object Value) (filler : Option DataRange) (y : Value) : Prop :=
  match filler with
  | none => True
  | some r => dataDenote I r y

private theorem range_filler_same (I : Interpretation Object Value) (A B : AnonymousIndividual → Object)
    (filler : Option DataRange) (y : Value) :
    rangeFiller (withAnonymous I A) filler y ↔ rangeFiller (withAnonymous I B) filler y := by
  cases filler with
  | none => exact Iff.rfl
  | some r => exact data_same I A B r y

/-- The extension of a scoped class expression depends only on the anonymous
    individuals of the scope. -/
theorem class_coincide (I : Interpretation Object Value) {s : List U8} {A B : AnonymousIndividual → Object}
    (agree : Agree s A B) (e : ClassExpression) :
    ScopedClass s e → ∀ x, (classDenote (withAnonymous I A) e x ↔ classDenote (withAnonymous I B) e x) := by
  cases e with
  | Class c => intro _ x; simp only [classDenote]; rfl
  | ObjectIntersectionOf xs =>
    intro inScope x
    rw [ScopedClass] at inScope
    obtain ⟨sf, ss, sr⟩ := inScope
    have first := class_coincide I agree xs.first sf x
    have second := class_coincide I agree xs.second ss x
    have rest : ∀ e ∈ xs.rest.val,
        (classDenote (withAnonymous I A) e x ↔ classDenote (withAnonymous I B) e x) :=
      fun e member => class_coincide I agree e (sr ⟨e, member⟩) x
    simp only [classDenote]
    exact and_congr first (and_congr second (forall₂_congr fun e member => rest e member))
  | ObjectUnionOf xs =>
    intro inScope x
    rw [ScopedClass] at inScope
    obtain ⟨sf, ss, sr⟩ := inScope
    have first := class_coincide I agree xs.first sf x
    have second := class_coincide I agree xs.second ss x
    have rest : ∀ e ∈ xs.rest.val,
        (classDenote (withAnonymous I A) e x ↔ classDenote (withAnonymous I B) e x) :=
      fun e member => class_coincide I agree e (sr ⟨e, member⟩) x
    simp only [classDenote]
    exact or_congr first (or_congr second (exists_congr fun e => exists_congr fun member => rest e member))
  | ObjectComplementOf inner =>
    intro inScope x
    rw [ScopedClass] at inScope
    simp only [classDenote]
    exact not_congr (class_coincide I agree inner inScope x)
  | ObjectOneOf xs =>
    intro inScope x
    rw [ScopedClass] at inScope
    simp only [classDenote]
    exact exists_congr fun a => and_congr_right fun member => by
      rw [individual_coincide I agree a (inScope a member)]
  | ObjectSomeValuesFrom p inner =>
    intro inScope x
    rw [ScopedClass] at inScope
    simp only [classDenote]
    rw [relation_same I A B p]
    exact exists_congr fun y => and_congr_right fun _ => class_coincide I agree inner inScope y
  | ObjectAllValuesFrom p inner =>
    intro inScope x
    rw [ScopedClass] at inScope
    simp only [classDenote]
    rw [relation_same I A B p]
    exact forall_congr' fun y => imp_congr_right fun _ => class_coincide I agree inner inScope y
  | ObjectHasValue p i =>
    intro inScope x
    rw [ScopedClass] at inScope
    simp only [classDenote]
    rw [relation_same I A B p, individual_coincide I agree i inScope]
  | ObjectHasSelf p =>
    intro _ x
    simp only [classDenote]
    rw [relation_same I A B p]
  | ObjectMinCardinality n p filler =>
    intro inScope x
    rw [ScopedClass] at inScope
    have fillers : ∀ y, classFiller (withAnonymous I A) filler y ↔ classFiller (withAnonymous I B) filler y := by
      intro y
      cases h : filler with
      | none => exact Iff.rfl
      | some c =>
        have : sizeOf c < sizeOf filler := by rw [h]; simp +arith
        exact class_coincide I agree c (inScope c (by simp [h])) y
    rw [classDenote.eq_def, classDenote.eq_def]
    change AtLeast (Rowl.Probes.naturalValue n)
        (fun y => objectRelation (withAnonymous I A) p x y ∧ classFiller (withAnonymous I A) filler y) ↔
      AtLeast (Rowl.Probes.naturalValue n)
        (fun y => objectRelation (withAnonymous I B) p x y ∧ classFiller (withAnonymous I B) filler y)
    rw [relation_same I A B p]
    exact lower_congr _ fun y => and_congr Iff.rfl (fillers y)
  | ObjectMaxCardinality n p filler =>
    intro inScope x
    rw [ScopedClass] at inScope
    have fillers : ∀ y, classFiller (withAnonymous I A) filler y ↔ classFiller (withAnonymous I B) filler y := by
      intro y
      cases h : filler with
      | none => exact Iff.rfl
      | some c =>
        have : sizeOf c < sizeOf filler := by rw [h]; simp +arith
        exact class_coincide I agree c (inScope c (by simp [h])) y
    rw [classDenote.eq_def, classDenote.eq_def]
    change AtMost (Rowl.Probes.naturalValue n)
        (fun y => objectRelation (withAnonymous I A) p x y ∧ classFiller (withAnonymous I A) filler y) ↔
      AtMost (Rowl.Probes.naturalValue n)
        (fun y => objectRelation (withAnonymous I B) p x y ∧ classFiller (withAnonymous I B) filler y)
    rw [relation_same I A B p]
    exact upper_congr _ fun y => and_congr Iff.rfl (fillers y)
  | ObjectExactCardinality n p filler =>
    intro inScope x
    rw [ScopedClass] at inScope
    have fillers : ∀ y, classFiller (withAnonymous I A) filler y ↔ classFiller (withAnonymous I B) filler y := by
      intro y
      cases h : filler with
      | none => exact Iff.rfl
      | some c =>
        have : sizeOf c < sizeOf filler := by rw [h]; simp +arith
        exact class_coincide I agree c (inScope c (by simp [h])) y
    rw [classDenote.eq_def, classDenote.eq_def]
    change Exactly (Rowl.Probes.naturalValue n)
        (fun y => objectRelation (withAnonymous I A) p x y ∧ classFiller (withAnonymous I A) filler y) ↔
      Exactly (Rowl.Probes.naturalValue n)
        (fun y => objectRelation (withAnonymous I B) p x y ∧ classFiller (withAnonymous I B) filler y)
    rw [relation_same I A B p]
    exact exact_congr _ fun y => and_congr Iff.rfl (fillers y)
  | DataSomeValuesFrom p r =>
    intro _ x
    simp only [classDenote]
    exact exists_congr fun y => and_congr Iff.rfl (data_same I A B r y)
  | DataAllValuesFrom p r =>
    intro _ x
    simp only [classDenote]
    exact forall_congr' fun y => imp_congr Iff.rfl (data_same I A B r y)
  | DataHasValue p l => intro _ x; simp only [classDenote]; rfl
  | DataMinCardinality n p r =>
    intro _ x
    rw [classDenote.eq_def, classDenote.eq_def]
    change AtLeast (Rowl.Probes.naturalValue n)
        (fun y => (withAnonymous I A).dataProperties p x y ∧ rangeFiller (withAnonymous I A) r y) ↔
      AtLeast (Rowl.Probes.naturalValue n)
        (fun y => (withAnonymous I B).dataProperties p x y ∧ rangeFiller (withAnonymous I B) r y)
    exact lower_congr _ fun y => and_congr Iff.rfl (range_filler_same I A B r y)
  | DataMaxCardinality n p r =>
    intro _ x
    rw [classDenote.eq_def, classDenote.eq_def]
    change AtMost (Rowl.Probes.naturalValue n)
        (fun y => (withAnonymous I A).dataProperties p x y ∧ rangeFiller (withAnonymous I A) r y) ↔
      AtMost (Rowl.Probes.naturalValue n)
        (fun y => (withAnonymous I B).dataProperties p x y ∧ rangeFiller (withAnonymous I B) r y)
    exact upper_congr _ fun y => and_congr Iff.rfl (range_filler_same I A B r y)
  | DataExactCardinality n p r =>
    intro _ x
    rw [classDenote.eq_def, classDenote.eq_def]
    change Exactly (Rowl.Probes.naturalValue n)
        (fun y => (withAnonymous I A).dataProperties p x y ∧ rangeFiller (withAnonymous I A) r y) ↔
      Exactly (Rowl.Probes.naturalValue n)
        (fun y => (withAnonymous I B).dataProperties p x y ∧ rangeFiller (withAnonymous I B) r y)
    exact exact_congr _ fun y => and_congr Iff.rfl (range_filler_same I A B r y)
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

private theorem denote_eq (I : Interpretation Object Value) {s : List U8} {A B : AnonymousIndividual → Object}
    (agree : Agree s A B) (e : ClassExpression) (inScope : ScopedClass s e) :
    classDenote (withAnonymous I A) e = classDenote (withAnonymous I B) e :=
  funext fun x => propext (class_coincide I agree e inScope x)

private theorem all_equal_congr {α : Type} {γ : Sort u} (xs : List α) (f g : α → γ)
    (same : ∀ a ∈ xs, f a = g a) : allEqual xs f ↔ allEqual xs g := by
  unfold allEqual
  constructor
  · intro h a ma b mb; rw [← same a ma, ← same b mb]; exact h a ma b mb
  · intro h a ma b mb; rw [same a ma, same b mb]; exact h a ma b mb

private theorem disjoint_congr {α : Type} {β : Type u} (xs : List α) (f g : α → β → Prop)
    (same : ∀ a ∈ xs, f a = g a) : pairwiseDisjoint xs f ↔ pairwiseDisjoint xs g := by
  unfold pairwiseDisjoint
  apply List.Pairwise.iff_of_mem
  intro a b ma mb
  rw [same a ma, same b mb]

private theorem chain_same (I : Interpretation Object Value) (A B : AnonymousIndividual → Object)
    (ps : List ObjectPropertyExpression) :
    chainRelation (withAnonymous I A) ps = chainRelation (withAnonymous I B) ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    funext x y
    simp only [chainRelation, relation_same I A B p, ih]

private theorem sub_same (I : Interpretation Object Value) (A B : AnonymousIndividual → Object)
    (p : SubObjectPropertyExpression) :
    subRelation (withAnonymous I A) p = subRelation (withAnonymous I B) p := by
  cases p with
  | Single p => simp only [subRelation, relation_same I A B p]
  | Chain ps => simp only [subRelation, chain_same I A B]

private theorem with_classes (I : Interpretation Object Value) (A : AnonymousIndividual → Object) :
    (withAnonymous I A).classes = I.classes := rfl
private theorem with_data (I : Interpretation Object Value) (A : AnonymousIndividual → Object) :
    (withAnonymous I A).dataProperties = I.dataProperties := rfl
private theorem with_datatypes (I : Interpretation Object Value) (A : AnonymousIndividual → Object) :
    (withAnonymous I A).datatypes = I.datatypes := rfl
private theorem with_named (I : Interpretation Object Value) (A : AnonymousIndividual → Object) :
    (withAnonymous I A).named = I.named := rfl
private theorem with_literals (I : Interpretation Object Value) (A : AnonymousIndividual → Object) :
    (withAnonymous I A).literals = I.literals := rfl

/-- Whether an interpretation satisfies a scoped axiom depends only on the
    anonymous individuals of the scope. -/
theorem axiom_coincide (I : Interpretation Object Value) {s : List U8} {A B : AnonymousIndividual → Object}
    (agree : Agree s A B) (ax : Axiom) (inScope : ScopedAxiom s ax) :
    satisfies (withAnonymous I A) ax ↔ satisfies (withAnonymous I B) ax := by
  have ind := individual_coincide I agree
  have den := denote_eq I agree
  have relAll : objectRelation (withAnonymous I A) = objectRelation (withAnonymous I B) :=
    funext (relation_same I A B)
  have subAll : subRelation (withAnonymous I A) = subRelation (withAnonymous I B) :=
    funext (sub_same I A B)
  have dataAll : ∀ r y, dataDenote (withAnonymous I A) r y = dataDenote (withAnonymous I B) r y :=
    fun r y => propext (data_same I A B r y)
  cases ax with
  | Declaration _ => exact Iff.rfl
  | SubClassOf a b =>
    obtain ⟨sa, sb⟩ := inScope
    simp only [satisfies, den a sa, den b sb]
  | EquivalentClasses xs =>
    simp only [satisfies]
    exact all_equal_congr _ _ _ fun e member => den e (inScope e member)
  | DisjointClasses xs =>
    simp only [satisfies]
    exact disjoint_congr _ _ _ fun e member => den e (inScope e member)
  | DisjointUnion c xs =>
    simp only [satisfies]
    refine and_congr ?_ (disjoint_congr _ _ _ fun e member => den e (inScope e member))
    exact forall_congr' fun x => iff_congr Iff.rfl (exists_congr fun e => and_congr_right fun member => by
      rw [den e (inScope e member)])
  | SubObjectPropertyOf a b => simp only [satisfies, subAll, relAll]
  | EquivalentObjectProperties xs => simp only [satisfies, relAll]
  | DisjointObjectProperties xs => simp only [satisfies, relAll]
  | InverseObjectProperties p q => simp only [satisfies, relAll]
  | ObjectPropertyDomain p e => simp only [satisfies, relAll, den e inScope]
  | ObjectPropertyRange p e => simp only [satisfies, relAll, den e inScope]
  | FunctionalObjectProperty p => simp only [satisfies, relAll]
  | InverseFunctionalObjectProperty p => simp only [satisfies, relAll]
  | ReflexiveObjectProperty p => simp only [satisfies, relAll]
  | IrreflexiveObjectProperty p => simp only [satisfies, relAll]
  | SymmetricObjectProperty p => simp only [satisfies, relAll]
  | AsymmetricObjectProperty p => simp only [satisfies, relAll]
  | TransitiveObjectProperty p => simp only [satisfies, relAll]
  | SubDataPropertyOf p q => exact Iff.rfl
  | EquivalentDataProperties xs => exact Iff.rfl
  | DisjointDataProperties xs => exact Iff.rfl
  | DataPropertyDomain p e => simp only [satisfies, den e inScope, with_data]
  | DataPropertyRange p r => simp only [satisfies, dataAll, with_data]
  | FunctionalDataProperty p => exact Iff.rfl
  | DatatypeDefinition dt r => simp only [satisfies, dataAll, with_datatypes]
  | HasKey e ops dps => simp only [satisfies, den e inScope, relAll, with_named, with_data]
  | SameIndividual xs =>
    simp only [satisfies]
    exact all_equal_congr _ _ _ fun i member => ind i (inScope i member)
  | DifferentIndividuals xs =>
    simp only [satisfies]
    apply List.Pairwise.iff_of_mem
    intro a b ma mb
    rw [ind a (inScope a ma), ind b (inScope b mb)]
  | ClassAssertion e i =>
    obtain ⟨se, si⟩ := inScope
    simp only [satisfies, den e se, ind i si]
  | ObjectPropertyAssertion p a b =>
    obtain ⟨sa, sb⟩ := inScope
    simp only [satisfies, relAll, ind a sa, ind b sb]
  | NegativeObjectPropertyAssertion p a b =>
    obtain ⟨sa, sb⟩ := inScope
    simp only [satisfies, relAll, ind a sa, ind b sb]
  | DataPropertyAssertion p a l =>
    simp only [satisfies, ind a inScope]
    exact Iff.rfl
  | NegativeDataPropertyAssertion p a l =>
    simp only [satisfies, ind a inScope]
    exact Iff.rfl
  | AnnotationAssertion _ _ _ => exact Iff.rfl
  | SubAnnotationPropertyOf _ _ => exact Iff.rfl
  | AnnotationPropertyDomain _ _ => exact Iff.rfl
  | AnnotationPropertyRange _ _ => exact Iff.rfl

/-! ## Standardizing apart -/

/-- Axiom lists, each with a scope that every anonymous individual of its axioms has. -/
def ScopedParts (parts : List (List U8 × List AnnotatedAxiom)) : Prop :=
  ∀ part ∈ parts, ∀ item ∈ part.2, ScopedAxiom part.1 item.axiom

/-- For axiom lists whose anonymous individuals have pairwise distinct scopes,
    an interpretation is a model of their concatenation exactly when it is a
    model of each list, each with an assignment of its own: the lists are
    standardized apart. -/
theorem models_parts (I : Interpretation Object Value) (parts : List (List U8 × List AnnotatedAxiom))
    (inScope : ScopedParts parts) (distinct : (parts.map Prod.fst).Nodup) :
    modelsClosure I (parts.flatMap Prod.snd) ↔ ∀ part ∈ parts, modelsClosure I part.2 := by
  constructor
  · rintro ⟨A, all⟩ part member
    exact ⟨A, fun item inside => all item (List.mem_flatMap.mpr ⟨part, member, inside⟩)⟩
  · intro each
    have choice : ∀ part : List U8 × List AnnotatedAxiom, ∃ A : AnonymousIndividual → Object,
        part ∈ parts → satisfiesClosure (withAnonymous I A) part.2 := by
      intro part
      by_cases member : part ∈ parts
      · obtain ⟨A, holds⟩ := each part member
        exact ⟨A, fun _ => holds⟩
      · exact ⟨I.anonymousIndividuals, fun inside => absurd inside member⟩
    choose F hF using choice
    let A : AnonymousIndividual → Object := fun a =>
      if h : ∃ part ∈ parts, part.1 = a.scope.val then F (Classical.choose h) a else I.anonymousIndividuals a
    refine ⟨A, ?_⟩
    intro item inside
    obtain ⟨part, member, within⟩ := List.mem_flatMap.mp inside
    have agree : Agree part.1 A (F part) := by
      intro a same
      have h : ∃ q ∈ parts, q.1 = a.scope.val := ⟨part, member, same.symm⟩
      obtain ⟨qMember, qScope⟩ := Classical.choose_spec h
      have unique : Classical.choose h = part :=
        List.inj_on_of_nodup_map distinct qMember member (by rw [qScope, same])
      show (if h : ∃ part ∈ parts, part.1 = a.scope.val then F (Classical.choose h) a
        else I.anonymousIndividuals a) = F part a
      rw [dif_pos h, unique]
    exact (axiom_coincide I agree item.axiom (inScope part member item within)).mpr (hF part member item within)

end Rowl.AnonymousScopes
