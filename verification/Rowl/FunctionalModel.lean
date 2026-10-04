import Rowl.FunctionalDocument

/-!
The kernel's raw OWL model of a read Functional Syntax document, proved against
an independent structural correspondence. Every mapping terminates; whenever it
succeeds, each model value corresponds to its source record: exact IRI and
literal bytes, node IDs as anonymous individuals of the caller's scope, and
nested annotations, member lists, individual lists and axioms in source order.
The mapping declines only a member list, property chain or individual list with
fewer than two members or an enumeration without members, and every axiom the
independent document grammar accepts has at least that many members in each, so
every read document maps.
-/
namespace Rowl.FunctionalModel
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional_model
open RowlRust.functional_annotations (SourceAnnotation SourceAnnotationValue)
open RowlRust.functional_annotation_axioms (SourceAnnotationAxiomBody SourceAnnotationSubject)
open RowlRust.functional_assertions (SourceAssertionBody)
open RowlRust.functional_individuals (SourceIndividual)
open RowlRust.functional_classes (SourceClass SourceObjectProperty)
open RowlRust.functional_class_axioms (SourceClassAxiomBody)
open RowlRust.functional_property_axioms (SourcePropertyAxiomBody SourceSubProperty PropertyCharacteristic)
open RowlRust.functional_declarations (SourceDeclaration SourceEntity SourceEntityKind)
open RowlRust.functional_document (SourceAxiom SourceDocument SourceDocumentTail)
open RowlRust.functional_header (HeaderIri ImportReference SourceOntologyIdentity)
open RowlRust.functional_literals (SourceLiteral)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The model IRI of a resolved source IRI: exactly its bytes. -/
def IriOf (iri : HeaderIri) : model.Iri := ⟨iri.value⟩
/-- A node ID as an anonymous individual of the caller's scope. -/
def AnonymousOf (scope label : alloc.vec.Vec U8) : model.AnonymousIndividual := ⟨scope,label⟩
/-- A literal with its exact lexical bytes and datatype IRI. -/
def LiteralOf (literal : SourceLiteral) : model.Literal := ⟨literal.lexical,⟨⟨literal.datatype⟩⟩⟩
def ValueOf (scope : alloc.vec.Vec U8) : SourceAnnotationValue → model.AnnotationValue
  | .Iri iri => .Iri (IriOf iri)
  | .Anonymous _ label => .Anonymous (AnonymousOf scope label)
  | .Literal literal => .Literal (LiteralOf literal)
def SubjectOf (scope : alloc.vec.Vec U8) : SourceAnnotationSubject → model.AnnotationSubject
  | .Iri iri => .Iri (IriOf iri)
  | .Anonymous _ label => .Anonymous (AnonymousOf scope label)
/-- A named individual's exact IRI, or a node ID as an anonymous individual of
    the caller's scope. -/
def IndividualOf (scope : alloc.vec.Vec U8) : SourceIndividual → model.Individual
  | .Named iri => .Named ⟨IriOf iri⟩
  | .Anonymous _ label => .Anonymous (AnonymousOf scope label)
/-- A model enumeration corresponds to a source individual list: its first and
    remaining members are the models of the source individuals, in order. -/
def EnumerationModel (scope : alloc.vec.Vec U8) (members : List SourceIndividual)
    (target : model.NonEmpty model.Individual) : Prop :=
  target.first :: target.rest.val = members.map (IndividualOf scope)
/-- A model individual list corresponds to a source individual list: its first,
    second and remaining members are the models of the source individuals, in
    order. -/
def IndividualMembersModel (scope : alloc.vec.Vec U8) (members : List SourceIndividual)
    (target : model.AtLeastTwo model.Individual) : Prop :=
  target.first :: target.second :: target.rest.val = members.map (IndividualOf scope)
def PropertyOf : SourceObjectProperty → model.ObjectPropertyExpression
  | .Named iri => .Property ⟨IriOf iri⟩
  | .Inverse _ iri => .Inverse ⟨IriOf iri⟩
/-- The unary natural number of a natural number. -/
def NaturalOf : Nat → probes.Natural
  | 0 => .Zero
  | n+1 => .Succ (NaturalOf n)
/-- The model number restriction of a bound. -/
def CardinalityOf : functional_classes.Bound → probes.Natural → model.ObjectPropertyExpression →
    Option model.ClassExpression → model.ClassExpression
  | .Min, value, property, filler => .ObjectMinCardinality value property filler
  | .Max, value, property, filler => .ObjectMaxCardinality value property filler
  | .Exact, value, property, filler => .ObjectExactCardinality value property filler
def EntityOf (entity : SourceEntity) : model.Entity :=
  match entity.kind with
  | .Class => .Class ⟨IriOf entity.iri⟩
  | .Datatype => .Datatype ⟨IriOf entity.iri⟩
  | .ObjectProperty => .ObjectProperty ⟨IriOf entity.iri⟩
  | .DataProperty => .DataProperty ⟨IriOf entity.iri⟩
  | .AnnotationProperty => .AnnotationProperty ⟨IriOf entity.iri⟩
  | .NamedIndividual => .NamedIndividual ⟨IriOf entity.iri⟩
def AnnotationAxiomOf (scope : alloc.vec.Vec U8) : SourceAnnotationAxiomBody → model.Axiom
  | .Assertion property subject value =>
    .AnnotationAssertion ⟨IriOf property⟩ (SubjectOf scope subject) (ValueOf scope value)
  | .SubProperty sub sup => .SubAnnotationPropertyOf ⟨IriOf sub⟩ ⟨IriOf sup⟩
  | .Domain property domain => .AnnotationPropertyDomain ⟨IriOf property⟩ (IriOf domain)
  | .Range property range => .AnnotationPropertyRange ⟨IriOf property⟩ (IriOf range)
def IdentityOf : SourceOntologyIdentity → model.OntologyIdentity
  | .Anonymous => .Anonymous
  | .Named ontology version => .Named (IriOf ontology) (version.map IriOf)

mutual
/-- A model annotation corresponds to a source annotation: the exact property
    IRI and value, and the models of its nested annotations in order. -/
inductive AnnotationModel (scope : alloc.vec.Vec U8) : SourceAnnotation → model.Annotation → Prop
  | mk {keyword : functional.Token} {nested : alloc.vec.Vec SourceAnnotation} {property : HeaderIri}
      {value : SourceAnnotationValue} {models : alloc.vec.Vec model.Annotation}
      (inner : AnnotationsModel scope nested.val models.val) :
      AnnotationModel scope (.mk keyword nested property value) (.mk models ⟨IriOf property⟩ (ValueOf scope value))
/-- Annotation sequences correspond element by element, in order. -/
inductive AnnotationsModel (scope : alloc.vec.Vec U8) : List SourceAnnotation → List model.Annotation → Prop
  | nil : AnnotationsModel scope [] []
  | cons {source : SourceAnnotation} {sources : List SourceAnnotation} {target : model.Annotation}
      {targets : List model.Annotation}
      (head : AnnotationModel scope source target) (tail : AnnotationsModel scope sources targets) :
      AnnotationsModel scope (source :: sources) (target :: targets)
end

mutual
/-- A model class expression corresponds to a source class expression with the
    same constructor, exact IRIs, the models of its individuals in the caller's
    scope, the numbers of its number restrictions and corresponding operands. -/
inductive ClassModel (scope : alloc.vec.Vec U8) : SourceClass → model.ClassExpression → Prop
  | named {iri : HeaderIri} : ClassModel scope (.Named iri) (.Class ⟨IriOf iri⟩)
  | intersection {keyword : functional.Token} {members : alloc.vec.Vec SourceClass}
      {target : model.AtLeastTwo model.ClassExpression}
      (inner : MembersModel scope members.val target) :
      ClassModel scope (.IntersectionOf keyword members) (.ObjectIntersectionOf target)
  | union {keyword : functional.Token} {members : alloc.vec.Vec SourceClass}
      {target : model.AtLeastTwo model.ClassExpression}
      (inner : MembersModel scope members.val target) :
      ClassModel scope (.UnionOf keyword members) (.ObjectUnionOf target)
  | complement {keyword : functional.Token} {operand : SourceClass} {target : model.ClassExpression}
      (inner : ClassModel scope operand target) :
      ClassModel scope (.ComplementOf keyword operand) (.ObjectComplementOf target)
  | some {keyword : functional.Token} {property : SourceObjectProperty} {filler : SourceClass}
      {target : model.ClassExpression} (inner : ClassModel scope filler target) :
      ClassModel scope (.SomeValuesFrom keyword property filler) (.ObjectSomeValuesFrom (PropertyOf property) target)
  | all {keyword : functional.Token} {property : SourceObjectProperty} {filler : SourceClass}
      {target : model.ClassExpression} (inner : ClassModel scope filler target) :
      ClassModel scope (.AllValuesFrom keyword property filler) (.ObjectAllValuesFrom (PropertyOf property) target)
  | oneOf {keyword : functional.Token} {members : alloc.vec.Vec SourceIndividual}
      {target : model.NonEmpty model.Individual} (inner : EnumerationModel scope members.val target) :
      ClassModel scope (.OneOf keyword members) (.ObjectOneOf target)
  | value {keyword : functional.Token} {property : SourceObjectProperty} {individual : SourceIndividual} :
      ClassModel scope (.HasValue keyword property individual)
        (.ObjectHasValue (PropertyOf property) (IndividualOf scope individual))
  | self {keyword : functional.Token} {property : SourceObjectProperty} :
      ClassModel scope (.HasSelf keyword property) (.ObjectHasSelf (PropertyOf property))
  | cardinality {keyword number : functional.Token} {bound : functional_classes.Bound} {value : Usize}
      {property : SourceObjectProperty} :
      ClassModel scope (.Cardinality keyword bound number value property none)
        (CardinalityOf bound (NaturalOf value.val) (PropertyOf property) none)
  | qualified {keyword number : functional.Token} {bound : functional_classes.Bound} {value : Usize}
      {property : SourceObjectProperty} {filler : SourceClass} {target : model.ClassExpression}
      (inner : ClassModel scope filler target) :
      ClassModel scope (.Cardinality keyword bound number value property (some filler))
        (CardinalityOf bound (NaturalOf value.val) (PropertyOf property) (some target))
/-- A member list of at least two expressions corresponds to the model's first,
    second and remaining members, in order. -/
inductive MembersModel (scope : alloc.vec.Vec U8) : List SourceClass → model.AtLeastTwo model.ClassExpression → Prop
  | mk {first second : SourceClass} {rest : List SourceClass} {firstTarget secondTarget : model.ClassExpression}
      {restTargets : alloc.vec.Vec model.ClassExpression}
      (one : ClassModel scope first firstTarget) (two : ClassModel scope second secondTarget)
      (others : RestModel scope rest restTargets.val) :
      MembersModel scope (first :: second :: rest) ⟨firstTarget,secondTarget,restTargets⟩
/-- Remaining members correspond element by element, in order. -/
inductive RestModel (scope : alloc.vec.Vec U8) : List SourceClass → List model.ClassExpression → Prop
  | nil : RestModel scope [] []
  | cons {source : SourceClass} {sources : List SourceClass} {target : model.ClassExpression}
      {targets : List model.ClassExpression}
      (head : ClassModel scope source target) (tail : RestModel scope sources targets) :
      RestModel scope (source :: sources) (target :: targets)
end

/-- A model class axiom corresponds to a source class axiom with the same form. -/
inductive ClassAxiomModel (scope : alloc.vec.Vec U8) : SourceClassAxiomBody → model.Axiom → Prop
  | subClassOf {sub sup : SourceClass} {subTarget supTarget : model.ClassExpression}
      (one : ClassModel scope sub subTarget) (two : ClassModel scope sup supTarget) :
      ClassAxiomModel scope (.SubClassOf sub sup) (.SubClassOf subTarget supTarget)
  | equivalent {members : alloc.vec.Vec SourceClass} {target : model.AtLeastTwo model.ClassExpression}
      (inner : MembersModel scope members.val target) :
      ClassAxiomModel scope (.EquivalentClasses members) (.EquivalentClasses target)
  | disjoint {members : alloc.vec.Vec SourceClass} {target : model.AtLeastTwo model.ClassExpression}
      (inner : MembersModel scope members.val target) :
      ClassAxiomModel scope (.DisjointClasses members) (.DisjointClasses target)
  | disjointUnion {named : HeaderIri} {members : alloc.vec.Vec SourceClass}
      {target : model.AtLeastTwo model.ClassExpression} (inner : MembersModel scope members.val target) :
      ClassAxiomModel scope (.DisjointUnion named members) (.DisjointUnion ⟨IriOf named⟩ target)
  | domain {property : SourceObjectProperty} {domain : SourceClass} {target : model.ClassExpression}
      (inner : ClassModel scope domain target) :
      ClassAxiomModel scope (.ObjectPropertyDomain property domain)
        (.ObjectPropertyDomain (PropertyOf property) target)
  | range {property : SourceObjectProperty} {range : SourceClass} {target : model.ClassExpression}
      (inner : ClassModel scope range target) :
      ClassAxiomModel scope (.ObjectPropertyRange property range) (.ObjectPropertyRange (PropertyOf property) target)
/-- A model assertion corresponds to a source assertion of the same form, with
    the models of its individuals, class expression or property. -/
inductive AssertionModel (scope : alloc.vec.Vec U8) : SourceAssertionBody → model.Axiom → Prop
  | same {members : alloc.vec.Vec SourceIndividual} {target : model.AtLeastTwo model.Individual}
      (inner : IndividualMembersModel scope members.val target) :
      AssertionModel scope (.SameIndividual members) (.SameIndividual target)
  | different {members : alloc.vec.Vec SourceIndividual} {target : model.AtLeastTwo model.Individual}
      (inner : IndividualMembersModel scope members.val target) :
      AssertionModel scope (.DifferentIndividuals members) (.DifferentIndividuals target)
  | classAssertion {expression : SourceClass} {member : SourceIndividual} {target : model.ClassExpression}
      (inner : ClassModel scope expression target) :
      AssertionModel scope (.ClassAssertion expression member) (.ClassAssertion target (IndividualOf scope member))
  | propertyAssertion {property : SourceObjectProperty} {subject object : SourceIndividual} :
      AssertionModel scope (.ObjectPropertyAssertion property subject object)
        (.ObjectPropertyAssertion (PropertyOf property) (IndividualOf scope subject) (IndividualOf scope object))
  | negativeAssertion {property : SourceObjectProperty} {subject object : SourceIndividual} :
      AssertionModel scope (.NegativeObjectPropertyAssertion property subject object)
        (.NegativeObjectPropertyAssertion (PropertyOf property) (IndividualOf scope subject)
          (IndividualOf scope object))
/-- A model member list corresponds to a source list of at least two object
    property expressions: their models, in source order. -/
inductive PropertyMembersModel : List SourceObjectProperty → model.AtLeastTwo model.ObjectPropertyExpression → Prop
  | members {first second : SourceObjectProperty} {rest : List SourceObjectProperty}
      {target : model.AtLeastTwo model.ObjectPropertyExpression}
      (firstIs : target.first = PropertyOf first) (secondIs : target.second = PropertyOf second)
      (restIs : target.rest.val = rest.map PropertyOf) :
      PropertyMembersModel (first :: second :: rest) target
/-- The model of a sub-property: one property, or the chain of its members. -/
inductive SubPropertyModel : SourceSubProperty → model.SubObjectPropertyExpression → Prop
  | single {property : SourceObjectProperty} : SubPropertyModel (.Single property) (.Single (PropertyOf property))
  | chain {keyword : functional.Token} {members : alloc.vec.Vec SourceObjectProperty}
      {target : model.AtLeastTwo model.ObjectPropertyExpression} (inner : PropertyMembersModel members.val target) :
      SubPropertyModel (.Chain keyword members) (.Chain target)
/-- The model axiom of a property characteristic. -/
def CharacteristicOf : PropertyCharacteristic → model.ObjectPropertyExpression → model.Axiom
  | .Functional, property => .FunctionalObjectProperty property
  | .InverseFunctional, property => .InverseFunctionalObjectProperty property
  | .Reflexive, property => .ReflexiveObjectProperty property
  | .Irreflexive, property => .IrreflexiveObjectProperty property
  | .Symmetric, property => .SymmetricObjectProperty property
  | .Asymmetric, property => .AsymmetricObjectProperty property
  | .Transitive, property => .TransitiveObjectProperty property
/-- A model property axiom corresponds to a source property axiom of the same
    form, with the models of its properties in source order. -/
inductive PropertyAxiomModel : SourcePropertyAxiomBody → model.Axiom → Prop
  | sub {sub : SourceSubProperty} {sup : SourceObjectProperty} {target : model.SubObjectPropertyExpression}
      (inner : SubPropertyModel sub target) :
      PropertyAxiomModel (.SubObjectPropertyOf sub sup) (.SubObjectPropertyOf target (PropertyOf sup))
  | equivalent {members : alloc.vec.Vec SourceObjectProperty} {target : model.AtLeastTwo model.ObjectPropertyExpression}
      (inner : PropertyMembersModel members.val target) :
      PropertyAxiomModel (.EquivalentObjectProperties members) (.EquivalentObjectProperties target)
  | disjoint {members : alloc.vec.Vec SourceObjectProperty} {target : model.AtLeastTwo model.ObjectPropertyExpression}
      (inner : PropertyMembersModel members.val target) :
      PropertyAxiomModel (.DisjointObjectProperties members) (.DisjointObjectProperties target)
  | inverse {first second : SourceObjectProperty} :
      PropertyAxiomModel (.InverseObjectProperties first second)
        (.InverseObjectProperties (PropertyOf first) (PropertyOf second))
  | characteristic {characteristic : PropertyCharacteristic} {property : SourceObjectProperty} :
      PropertyAxiomModel (.Characteristic characteristic property) (CharacteristicOf characteristic (PropertyOf property))
/-- A model axiom corresponds to a source axiom: the same axiom and the models
    of its axiom annotations in order. -/
inductive AxiomModel (scope : alloc.vec.Vec U8) : SourceAxiom → model.AnnotatedAxiom → Prop
  | declaration {record : SourceDeclaration} {annotations : alloc.vec.Vec model.Annotation}
      (inner : AnnotationsModel scope record.annotations.val annotations.val) :
      AxiomModel scope (.Declaration record) ⟨annotations,.Declaration (EntityOf record.entity)⟩
  | annotation {record : functional_annotation_axioms.SourceAnnotationAxiom}
      {annotations : alloc.vec.Vec model.Annotation}
      (inner : AnnotationsModel scope record.annotations.val annotations.val) :
      AxiomModel scope (.Annotation record) ⟨annotations,AnnotationAxiomOf scope record.body⟩
  | «class» {record : functional_class_axioms.SourceClassAxiom} {annotations : alloc.vec.Vec model.Annotation}
      {target : model.Axiom}
      (inner : AnnotationsModel scope record.annotations.val annotations.val)
      (body : ClassAxiomModel scope record.body target) :
      AxiomModel scope (.Class record) ⟨annotations,target⟩
  | property {record : functional_property_axioms.SourcePropertyAxiom} {annotations : alloc.vec.Vec model.Annotation}
      {target : model.Axiom}
      (inner : AnnotationsModel scope record.annotations.val annotations.val)
      (body : PropertyAxiomModel record.body target) :
      AxiomModel scope (.Property record) ⟨annotations,target⟩
  | assertion {record : functional_assertions.SourceAssertion} {annotations : alloc.vec.Vec model.Annotation}
      {target : model.Axiom}
      (inner : AnnotationsModel scope record.annotations.val annotations.val)
      (body : AssertionModel scope record.body target) :
      AxiomModel scope (.Assertion record) ⟨annotations,target⟩
/-- The model of a document tail: the same identity, the import targets, the
    ontology annotations and the axioms, each in source order. -/
def OntologyModel (scope : alloc.vec.Vec U8) (tail : SourceDocumentTail) (ontology : model.RawOntology) : Prop :=
  ontology.identity = IdentityOf tail.identity ∧
  ontology.imports.val = tail.imports.val.map (fun reference => IriOf reference.target) ∧
  AnnotationsModel scope tail.annotations.val ontology.annotations.val ∧
  List.Forall₂ (AxiomModel scope) tail.axioms.val ontology.axioms.val

/-- Every intersection and union in a class expression has at least two
    members and every enumeration at least one, also inside fillers: the shape
    the class grammar accepts and model member lists need. -/
inductive Shaped : SourceClass → Prop
  | named {iri : HeaderIri} : Shaped (.Named iri)
  | intersection {keyword : functional.Token} {members : alloc.vec.Vec SourceClass}
      (enough : 2 ≤ members.val.length) (each : ∀ member ∈ members.val, Shaped member) :
      Shaped (.IntersectionOf keyword members)
  | union {keyword : functional.Token} {members : alloc.vec.Vec SourceClass}
      (enough : 2 ≤ members.val.length) (each : ∀ member ∈ members.val, Shaped member) :
      Shaped (.UnionOf keyword members)
  | complement {keyword : functional.Token} {operand : SourceClass} (inner : Shaped operand) :
      Shaped (.ComplementOf keyword operand)
  | some {keyword : functional.Token} {property : SourceObjectProperty} {filler : SourceClass}
      (inner : Shaped filler) : Shaped (.SomeValuesFrom keyword property filler)
  | all {keyword : functional.Token} {property : SourceObjectProperty} {filler : SourceClass}
      (inner : Shaped filler) : Shaped (.AllValuesFrom keyword property filler)
  | oneOf {keyword : functional.Token} {members : alloc.vec.Vec SourceIndividual}
      (enough : 1 ≤ members.val.length) : Shaped (.OneOf keyword members)
  | value {keyword : functional.Token} {property : SourceObjectProperty} {individual : SourceIndividual} :
      Shaped (.HasValue keyword property individual)
  | self {keyword : functional.Token} {property : SourceObjectProperty} : Shaped (.HasSelf keyword property)
  | cardinality {keyword number : functional.Token} {bound : functional_classes.Bound} {value : Usize}
      {property : SourceObjectProperty} : Shaped (.Cardinality keyword bound number value property none)
  | qualified {keyword number : functional.Token} {bound : functional_classes.Bound} {value : Usize}
      {property : SourceObjectProperty} {filler : SourceClass} (inner : Shaped filler) :
      Shaped (.Cardinality keyword bound number value property (some filler))
/-- A class axiom whose member lists have at least two members and whose class
    expressions are shaped. -/
def ShapedAxiom : SourceClassAxiomBody → Prop
  | .SubClassOf sub sup => Shaped sub ∧ Shaped sup
  | .EquivalentClasses members => 2 ≤ members.val.length ∧ ∀ member ∈ members.val, Shaped member
  | .DisjointClasses members => 2 ≤ members.val.length ∧ ∀ member ∈ members.val, Shaped member
  | .DisjointUnion _ members => 2 ≤ members.val.length ∧ ∀ member ∈ members.val, Shaped member
  | .ObjectPropertyDomain _ domain => Shaped domain
  | .ObjectPropertyRange _ range => Shaped range
/-- An assertion whose individual list has at least two members and whose class
    expression is shaped. -/
def ShapedAssertion : SourceAssertionBody → Prop
  | .SameIndividual members => 2 ≤ members.val.length
  | .DifferentIndividuals members => 2 ≤ members.val.length
  | .ClassAssertion expression _ => Shaped expression
  | _ => True
/-- A sub-property whose chain, if any, has at least two members. -/
def ShapedSub : SourceSubProperty → Prop
  | .Single _ => True
  | .Chain _ members => 2 ≤ members.val.length
/-- A property axiom whose member lists and chains have at least two members. -/
def ShapedProperty : SourcePropertyAxiomBody → Prop
  | .SubObjectPropertyOf sub _ => ShapedSub sub
  | .EquivalentObjectProperties members => 2 ≤ members.val.length
  | .DisjointObjectProperties members => 2 ≤ members.val.length
  | _ => True
/-- A source axiom of the shape the document grammar accepts. -/
def ShapedSource : SourceAxiom → Prop
  | .Class record => ShapedAxiom record.body
  | .Property record => ShapedProperty record.body
  | .Assertion record => ShapedAssertion record.body
  | _ => True

private theorem listN_mem_size {α : Type} [SizeOf α] {n : Nat}
    (xs : Aeneas.Data.ListN.ListN α n) {x : α} (h : x ∈ xs.toList) : sizeOf x < sizeOf xs := by
  induction xs with
  | nil => simp [Aeneas.Data.ListN.ListN.toList] at h
  | cons head tail ih =>
    simp only [Aeneas.Data.ListN.ListN.toList,List.mem_cons] at h
    rcases h with rfl | h
    · simp +arith
    · have := ih h
      simp only [Data.ListN.ListN.cons.sizeOf_spec]
      omega
private theorem vec_mem_size {α : Type} [SizeOf α] (xs : alloc.vec.Vec α) {x : α} (h : x ∈ xs.val) :
    sizeOf x < sizeOf xs := by
  have := listN_mem_size xs.slice.list h
  cases xs with | mk slice => cases slice; simp_all [alloc.vec.Vec.val,Slice.val]; omega

private theorem copy_from_correct (source : alloc.vec.Vec U8) (index : Usize) (target : alloc.vec.Vec U8)
    (copied : target.val = source.val.take index.val) (inside : index.val ≤ source.val.length) :
    functional_model.copy_from source index target = .ok source := by
  rw [functional_model.copy_from]
  by_cases more : index.val < source.val.length
  · have lookup : source.index_usize index = .ok source.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have shorter : target.val.length < source.val.length := by
      rw [copied]; simp; omega
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec target source.val[index.val] (by scalar_tac))
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have recursive := copy_from_correct source next appended
      (by rw [contents,copied,nextIndex,List.take_succ_eq_append_getElem more])
      (by omega)
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
      lookup,bind_ok,push,advance,recursive]
  · have full : index.val = source.val.length := by omega
    have same : target = source := by
      apply (alloc.vec.Vec.eq_iff target source).mpr
      rw [copied,full,List.take_length]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,same]
termination_by source.val.length - index.val
decreasing_by omega
/-- Copying bytes reproduces them exactly. -/
theorem copy_bytes_correct (source : alloc.vec.Vec U8) : copy_bytes source = .ok source := by
  rw [copy_bytes]
  exact copy_from_correct source 0#usize (alloc.vec.Vec.new U8) (by simp) (by simp)

theorem iri_correct (source : HeaderIri) : functional_model.iri source = .ok (IriOf source) := by
  simp [functional_model.iri,copy_bytes_correct,IriOf]
theorem anonymous_correct (label scope : alloc.vec.Vec U8) :
    functional_model.anonymous label scope = .ok (AnonymousOf scope label) := by
  simp [functional_model.anonymous,copy_bytes_correct,AnonymousOf]
theorem literal_correct (source : SourceLiteral) : functional_model.literal source = .ok (LiteralOf source) := by
  simp [functional_model.literal,copy_bytes_correct,LiteralOf]
theorem annotation_value_correct (source : SourceAnnotationValue) (scope : alloc.vec.Vec U8) :
    annotation_value source scope = .ok (ValueOf scope source) := by
  cases source <;> simp [annotation_value,iri_correct,anonymous_correct,literal_correct,ValueOf]
theorem subject_correct (source : SourceAnnotationSubject) (scope : alloc.vec.Vec U8) :
    subject source scope = .ok (SubjectOf scope source) := by
  cases source <;> simp [subject,iri_correct,anonymous_correct,SubjectOf]
theorem property_correct (source : SourceObjectProperty) : property source = .ok (PropertyOf source) := by
  cases source <;> simp [property,iri_correct,PropertyOf]
theorem individual_correct (source : SourceIndividual) (scope : alloc.vec.Vec U8) :
    individual source scope = .ok (IndividualOf scope source) := by
  cases source <;> simp [individual,iri_correct,anonymous_correct,IndividualOf]
theorem entity_correct (source : SourceEntity) : entity source = .ok (EntityOf source) := by
  obtain ⟨kind,keyword,named⟩ := source
  cases kind <;> simp [entity,iri_correct,EntityOf]
theorem annotation_axiom_correct (source : SourceAnnotationAxiomBody) (scope : alloc.vec.Vec U8) :
    annotation_axiom source scope = .ok (AnnotationAxiomOf scope source) := by
  cases source <;> simp [annotation_axiom,iri_correct,subject_correct,annotation_value_correct,AnnotationAxiomOf]
theorem identity_correct (source : SourceOntologyIdentity) : identity source = .ok (IdentityOf source) := by
  cases source with
  | Anonymous => rfl
  | Named ontology version => cases version <;> simp [identity,iri_correct,IdentityOf]

private theorem annotations_length {scope : alloc.vec.Vec U8} :
    ∀ {sources : List SourceAnnotation} {targets : List model.Annotation},
      AnnotationsModel scope sources targets → targets.length = sources.length
  | [], _, relation => by cases relation; rfl
  | _ :: _, _, relation => by
    cases relation with
    | cons head tail => simp [annotations_length tail]
private theorem annotations_snoc {scope : alloc.vec.Vec U8} {source : SourceAnnotation} {target : model.Annotation}
    (last : AnnotationModel scope source target) :
    ∀ {sources : List SourceAnnotation} {targets : List model.Annotation},
      AnnotationsModel scope sources targets → AnnotationsModel scope (sources++[source]) (targets++[target])
  | [], _, relation => by cases relation; exact .cons last .nil
  | _ :: _, _, relation => by
    cases relation with
    | cons head tail => exact .cons head (annotations_snoc last tail)

mutual
/-- Every source annotation maps to its corresponding model annotation. -/
theorem annotation_correct (source : SourceAnnotation) (scope : alloc.vec.Vec U8) :
    ∃ target, annotation source scope = .ok target ∧ AnnotationModel scope source target := by
  obtain ⟨keyword,nested,key,value⟩ := source
  obtain ⟨targets,targetsRead,targetsModel⟩ :=
    annotations_from_correct nested 0#usize (alloc.vec.Vec.new model.Annotation) scope (by simpa using .nil)
      (by simp)
  refine ⟨.mk targets ⟨IriOf key⟩ (ValueOf scope value),?_,.mk targetsModel⟩
  rw [annotation.eq_def]
  simp [targetsRead,iri_correct,annotation_value_correct]
termination_by (sizeOf source,0)
decreasing_by
  all_goals
    simp_wf
    try rw [Prod.lex_def]
    try simp +arith
    try omega
/-- Every annotation sequence maps element by element, extending the models
    already collected. -/
theorem annotations_from_correct (values : alloc.vec.Vec SourceAnnotation) (index : Usize)
    (out : alloc.vec.Vec model.Annotation) (scope : alloc.vec.Vec U8)
    (collected : AnnotationsModel scope (values.val.take index.val) out.val) (inside : index.val ≤ values.val.length) :
    ∃ targets, annotations_from values index out scope = .ok targets ∧ AnnotationsModel scope values.val targets.val := by
  rw [annotations_from.eq_def]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have member : values.val[index.val] ∈ values.val := List.getElem_mem more
    have smaller := vec_mem_size values member
    obtain ⟨target,targetRead,targetModel⟩ := annotation_correct values.val[index.val] scope
    have length := annotations_length collected
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out target (by simp at length; scalar_tac))
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨targets,targetsRead,targetsModel⟩ := annotations_from_correct values next appended scope
      (by rw [contents,nextIndex,List.take_succ_eq_append_getElem more]; exact annotations_snoc targetModel collected)
      (by omega)
    exact ⟨targets,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
      alloc.vec.Vec.index_slice_index,lookup,bind_ok,targetRead,push,advance,targetsRead],targetsModel⟩
  · have full : values.val.take index.val = values.val := List.take_of_length_le (by omega)
    rw [full] at collected
    exact ⟨out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],collected⟩
termination_by (sizeOf values,values.val.length-index.val+1)
decreasing_by
  all_goals
    simp_wf
    try rw [Prod.lex_def]
    try simp +arith
    try omega
end

private theorem two_shape {α : Type} : ∀ {values : List α} (enough : 2 ≤ values.length),
    values = values[0] :: values[1] :: values.drop 2
  | [], enough => by simp at enough
  | [_], enough => by simp at enough
  | _ :: _ :: _, _ => rfl
private theorem rest_snoc {scope : alloc.vec.Vec U8} {source : SourceClass} {target : model.ClassExpression}
    (last : ClassModel scope source target) :
    ∀ {sources : List SourceClass} {targets : List model.ClassExpression},
      RestModel scope sources targets → RestModel scope (sources++[source]) (targets++[target])
  | [], _, relation => by cases relation; exact .cons last .nil
  | _ :: _, _, relation => by
    cases relation with
    | cons head tail => exact .cons head (rest_snoc last tail)
private theorem rest_length {scope : alloc.vec.Vec U8} :
    ∀ {sources : List SourceClass} {targets : List model.ClassExpression},
      RestModel scope sources targets → targets.length = sources.length
  | [], _, relation => by cases relation; rfl
  | _ :: _, _, relation => by
    cases relation with
    | cons head tail => simp [rest_length tail]

/-- The remaining individuals of a list map one by one after the models already
    collected. -/
theorem individuals_from_correct (values : alloc.vec.Vec SourceIndividual) (index : Usize)
    (out : alloc.vec.Vec model.Individual) (scope : alloc.vec.Vec U8) (start : Nat) (first : start ≤ index.val)
    (collected : out.val = ((values.val.drop start).take (index.val-start)).map (IndividualOf scope))
    (inside : index.val ≤ values.val.length) :
    ∃ result, individuals_from values index out scope = .ok result ∧
      result.val = (values.val.drop start).map (IndividualOf scope) := by
  rw [individuals_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have length : out.val.length = index.val-start := by
      rw [collected]; simp; omega
    have room : out.val.length < values.val.length := by omega
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (IndividualOf scope values.val[index.val]) (by scalar_tac))
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have step : (values.val.drop start).take (next.val-start) =
        (values.val.drop start).take (index.val-start) ++ [values.val[index.val]] := by
      rw [nextIndex,show index.val+1-start = (index.val-start)+1 by omega]
      have bound : index.val-start < (values.val.drop start).length := by simp; omega
      rw [List.take_succ_eq_append_getElem bound]
      simp [List.getElem_drop,show start+(index.val-start) = index.val by omega]
    obtain ⟨final,finalRead,finalList⟩ := individuals_from_correct values next appended scope start (by omega)
      (by rw [step,contents,collected]; simp) (by omega)
    exact ⟨final,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,room,↓reduceIte,
      alloc.vec.Vec.index_slice_index,lookup,bind_ok,individual_correct,push,advance,finalRead],finalList⟩
  · have full : (values.val.drop start).take (index.val-start) = values.val.drop start :=
      List.take_of_length_le (by simp; omega)
    rw [full] at collected
    exact ⟨out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],collected⟩
termination_by values.val.length-index.val
decreasing_by omega
/-- An enumeration maps exactly when it has a member, to the models of its
    individuals in order. -/
theorem enumeration_correct (values : alloc.vec.Vec SourceIndividual) (scope : alloc.vec.Vec U8) :
    ∃ result, enumeration values scope = .ok result ∧
      (∀ target, result = some target → EnumerationModel scope values.val target) ∧
      (1 ≤ values.val.length → result.isSome) := by
  rw [enumeration]
  by_cases few : values.val.length < 1
  · exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,few],
      (by intro target impossible; cases impossible),fun enough => absurd enough (by omega)⟩
  · have zero : 0 < values.val.length := by omega
    have first : values.index_usize 0#usize = .ok values.val[0] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem zero]
    obtain ⟨rest,restRead,restList⟩ := individuals_from_correct values 1#usize
      (alloc.vec.Vec.new model.Individual) scope 1 (by simp) (by simp) (by simp; omega)
    refine ⟨some ⟨IndividualOf scope values.val[0],rest⟩,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,few,
      first,individual_correct,restRead],?_,fun _ => rfl⟩
    intro target same
    cases same
    obtain ⟨a,r,shape⟩ : ∃ a r, values.val = a :: r := by
      rcases hv : values.val with _ | ⟨a,r⟩
      · rw [hv] at zero; simp at zero
      · exact ⟨a,r,rfl⟩
    unfold EnumerationModel
    rw [restList]
    simp [shape]
/-- An individual list maps exactly when it has two members, to the models of
    its individuals in order. -/
theorem individual_members_correct (values : alloc.vec.Vec SourceIndividual) (scope : alloc.vec.Vec U8) :
    ∃ result, individual_members values scope = .ok result ∧
      (∀ target, result = some target → IndividualMembersModel scope values.val target) ∧
      (2 ≤ values.val.length → result.isSome) := by
  rw [individual_members]
  by_cases few : values.val.length < 2
  · exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,few,Nat.lt_succ_iff.mp few],
      (by intro target impossible; cases impossible),fun enough => absurd enough (by omega)⟩
  · have enough : 2 ≤ values.val.length := by omega
    have zero : 0 < values.val.length := by omega
    have one : 1 < values.val.length := by omega
    have first : values.index_usize 0#usize = .ok values.val[0] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem zero]
    have second : values.index_usize 1#usize = .ok values.val[1] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem one]
    obtain ⟨rest,restRead,restList⟩ := individuals_from_correct values 2#usize
      (alloc.vec.Vec.new model.Individual) scope 2 (by simp) (by simp) (by simpa using enough)
    refine ⟨some ⟨IndividualOf scope values.val[0],IndividualOf scope values.val[1],rest⟩,
      by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,Nat.not_lt.mpr enough,Nat.not_le.mpr enough,first,second,
        individual_correct,restRead],?_,fun _ => rfl⟩
    intro target same
    cases same
    obtain ⟨a,b,r,shape⟩ : ∃ a b r, values.val = a :: b :: r := by
      rcases hv : values.val with _ | ⟨a,_ | ⟨b,r⟩⟩
      · rw [hv] at enough; simp at enough
      · rw [hv] at enough; simp at enough
      · exact ⟨a,b,r,rfl⟩
    unfold IndividualMembersModel
    rw [restList]
    simp [shape]

/-- A machine integer maps to its unary natural number. -/
theorem natural_correct (value : Usize) : functional_model.natural value = .ok (NaturalOf value.val) := by
  rw [functional_model.natural]
  by_cases zero : value.val = 0
  · simp [UScalar.eq_equiv,show (0#usize).val = 0 from rfl,zero,NaturalOf]
  · obtain ⟨previous,subRun,subValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := value) (y := 1#usize) (by scalar_tac))
    have previousIs : previous.val = value.val-1 := by
      have : (1#usize).val = 1 := rfl
      omega
    have recursive := natural_correct previous
    obtain ⟨n,valueIs⟩ : ∃ n, value.val = n+1 := ⟨value.val-1,by omega⟩
    simp only [UScalar.eq_equiv,show (0#usize).val = 0 from rfl,zero,↓reduceIte,subRun,bind_ok,recursive,
      previousIs,valueIs,Nat.add_sub_cancel,Nat.add_one_ne_zero,NaturalOf]
termination_by value.val
decreasing_by
  have : (1#usize).val = 1 := rfl
  omega
/-- The unary natural number of a number has that value. -/
theorem natural_of_value (n : Nat) : Rowl.Probes.naturalValue (NaturalOf n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [NaturalOf,Rowl.Probes.naturalValue,ih]
theorem cardinality_correct (bound : functional_classes.Bound) (value : probes.Natural)
    (property : model.ObjectPropertyExpression) (filler : Option model.ClassExpression) :
    functional_model.cardinality bound value property filler = .ok (CardinalityOf bound value property filler) := by
  cases bound <;> rfl

mutual
/-- Every source class expression maps, when it maps, to its corresponding
    model class expression; every shaped expression maps. -/
theorem class_correct (source : SourceClass) (scope : alloc.vec.Vec U8) :
    ∃ result, functional_model.class source scope = .ok result ∧
      (∀ target, result = some target → ClassModel scope source target) ∧ (Shaped source → result.isSome) := by
  rw [functional_model.class.eq_def]
  cases source with
  | Named named =>
    exact ⟨some (.Class ⟨IriOf named⟩),by simp [iri_correct],(by intro target same; cases same; exact .named),
      fun _ => rfl⟩
  | IntersectionOf keyword members =>
    obtain ⟨result,read,correct,total⟩ := members_of_correct members scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        by intro shaped; cases shaped with | intersection enough each => exact absurd (total enough each) (by simp)⟩
    | some target =>
      exact ⟨some (.ObjectIntersectionOf target),by simp [read],
        (by intro target' same; cases same; exact .intersection (correct target rfl)),fun _ => rfl⟩
  | UnionOf keyword members =>
    obtain ⟨result,read,correct,total⟩ := members_of_correct members scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        by intro shaped; cases shaped with | union enough each => exact absurd (total enough each) (by simp)⟩
    | some target =>
      exact ⟨some (.ObjectUnionOf target),by simp [read],
        (by intro target' same; cases same; exact .union (correct target rfl)),fun _ => rfl⟩
  | ComplementOf keyword operand =>
    obtain ⟨result,read,correct,total⟩ := class_correct operand scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        by intro shaped; cases shaped with | complement inner => exact absurd (total inner) (by simp)⟩
    | some target =>
      exact ⟨some (.ObjectComplementOf target),by simp [read],
        (by intro target' same; cases same; exact .complement (correct target rfl)),fun _ => rfl⟩
  | SomeValuesFrom keyword property filler =>
    obtain ⟨result,read,correct,total⟩ := class_correct filler scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        by intro shaped; cases shaped with | some inner => exact absurd (total inner) (by simp)⟩
    | some target =>
      exact ⟨some (.ObjectSomeValuesFrom (PropertyOf property) target),by simp [read,property_correct],
        (by intro target' same; cases same; exact .some (correct target rfl)),fun _ => rfl⟩
  | AllValuesFrom keyword property filler =>
    obtain ⟨result,read,correct,total⟩ := class_correct filler scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        by intro shaped; cases shaped with | all inner => exact absurd (total inner) (by simp)⟩
    | some target =>
      exact ⟨some (.ObjectAllValuesFrom (PropertyOf property) target),by simp [read,property_correct],
        (by intro target' same; cases same; exact .all (correct target rfl)),fun _ => rfl⟩
  | OneOf keyword members =>
    obtain ⟨result,read,correct,total⟩ := enumeration_correct members scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        by intro shaped; cases shaped with | oneOf enough => exact absurd (total enough) (by simp)⟩
    | some target =>
      exact ⟨some (.ObjectOneOf target),by simp [read],
        (by intro target' same; cases same; exact .oneOf (correct target rfl)),fun _ => rfl⟩
  | HasValue keyword property value =>
    exact ⟨some (.ObjectHasValue (PropertyOf property) (IndividualOf scope value)),
      by simp [property_correct,individual_correct],(by intro target same; cases same; exact .value),fun _ => rfl⟩
  | HasSelf keyword property =>
    exact ⟨some (.ObjectHasSelf (PropertyOf property)),by simp [property_correct],
      (by intro target same; cases same; exact .self),fun _ => rfl⟩
  | Cardinality keyword bound number value property filler =>
    cases filler with
    | none =>
      exact ⟨some (CardinalityOf bound (NaturalOf value.val) (PropertyOf property) none),
        by simp [natural_correct,property_correct,cardinality_correct],
        (by intro target same; cases same; exact .cardinality),fun _ => rfl⟩
    | some filler =>
      obtain ⟨result,read,correct,total⟩ := class_correct filler scope
      cases result with
      | none =>
        exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
          by intro shaped; cases shaped with | qualified inner => exact absurd (total inner) (by simp)⟩
      | some target =>
        exact ⟨some (CardinalityOf bound (NaturalOf value.val) (PropertyOf property) (some target)),
          by simp [read,natural_correct,property_correct,cardinality_correct],
          (by intro target' same; cases same; exact .qualified (correct target rfl)),fun _ => rfl⟩
termination_by (sizeOf source,0)
decreasing_by
  all_goals
    simp_wf
    try rw [Prod.lex_def]
    try simp +arith
    try omega
/-- Remaining members map element by element, extending the models already
    collected; they all map when every member is shaped. -/
theorem rest_from_correct (values : alloc.vec.Vec SourceClass) (index : Usize) (out : alloc.vec.Vec model.ClassExpression)
    (scope : alloc.vec.Vec U8) (start : 2 ≤ index.val)
    (collected : RestModel scope ((values.val.drop 2).take (index.val-2)) out.val)
    (inside : index.val ≤ values.val.length) :
    ∃ result, rest_from values index out scope = .ok result ∧
      (∀ targets, result = some targets → RestModel scope (values.val.drop 2) targets.val) ∧
      ((∀ member ∈ values.val, Shaped member) → result.isSome) := by
  rw [rest_from.eq_def]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have member : values.val[index.val] ∈ values.val := List.getElem_mem more
    have smaller := vec_mem_size values member
    obtain ⟨result,read,correct,total⟩ := class_correct values.val[index.val] scope
    cases result with
    | none =>
      exact ⟨none,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,read],(by intro targets impossible; cases impossible),
        fun all => absurd (total (all _ member)) (by simp)⟩
    | some target =>
      have length := rest_length collected
      obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out target (by simp at length; scalar_tac))
      obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val+1 := by simpa using nextValue
      have step : (values.val.drop 2).take (next.val-2) = (values.val.drop 2).take (index.val-2) ++ [values.val[index.val]] := by
        rw [nextIndex,show index.val+1-2 = (index.val-2)+1 by omega]
        have bound : index.val-2 < (values.val.drop 2).length := by simp; omega
        rw [List.take_succ_eq_append_getElem bound]
        simp [List.getElem_drop,show 2+(index.val-2) = index.val by omega]
      obtain ⟨final,finalRead,finalCorrect,finalTotal⟩ := rest_from_correct values next appended scope (by omega)
        (by rw [step,contents]; exact rest_snoc (correct target rfl) collected) (by omega)
      exact ⟨final,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,read,push,advance,finalRead],finalCorrect,finalTotal⟩
  · have full : (values.val.drop 2).take (index.val-2) = values.val.drop 2 :=
      List.take_of_length_le (by simp; omega)
    rw [full] at collected
    exact ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],
      (by intro targets same; cases same; exact collected),fun _ => rfl⟩
termination_by (sizeOf values,values.val.length-index.val+1)
decreasing_by
  all_goals
    simp_wf
    try rw [Prod.lex_def]
    try simp +arith
    try omega
/-- A member list maps exactly when it has two members whose expressions map and
    whose remaining members map; the result corresponds to the list, and a list
    of at least two shaped members maps. -/
theorem members_of_correct (values : alloc.vec.Vec SourceClass) (scope : alloc.vec.Vec U8) :
    ∃ result, members_of values scope = .ok result ∧
      (∀ target, result = some target → MembersModel scope values.val target) ∧
      (2 ≤ values.val.length → (∀ member ∈ values.val, Shaped member) → result.isSome) := by
  rw [members_of.eq_def]
  by_cases few : values.val.length < 2
  · exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,few,Nat.lt_succ_iff.mp few],
      (by intro target impossible; cases impossible),fun enough _ => absurd enough (by omega)⟩
  · have enough : 2 ≤ values.val.length := by omega
    have zero : 0 < values.val.length := by omega
    have one : 1 < values.val.length := by omega
    have first : values.index_usize 0#usize = .ok values.val[0] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem zero]
    have second : values.index_usize 1#usize = .ok values.val[1] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem one]
    have firstSmaller := vec_mem_size values (List.getElem_mem zero)
    have secondSmaller := vec_mem_size values (List.getElem_mem one)
    obtain ⟨firstResult,firstRead,firstCorrect,firstTotal⟩ := class_correct values.val[0] scope
    cases firstResult with
    | none =>
      exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,Nat.not_lt.mpr enough,Nat.not_le.mpr enough,first,
        firstRead],(by intro target impossible; cases impossible),
        fun _ all => absurd (firstTotal (all _ (List.getElem_mem zero))) (by simp)⟩
    | some firstTarget =>
      obtain ⟨secondResult,secondRead,secondCorrect,secondTotal⟩ := class_correct values.val[1] scope
      cases secondResult with
      | none =>
        exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,Nat.not_lt.mpr enough,Nat.not_le.mpr enough,
          first,firstRead,second,secondRead],(by intro target impossible; cases impossible),
          fun _ all => absurd (secondTotal (all _ (List.getElem_mem one))) (by simp)⟩
      | some secondTarget =>
        obtain ⟨restResult,restRead,restCorrect,restTotal⟩ := rest_from_correct values 2#usize
          (alloc.vec.Vec.new model.ClassExpression) scope (by simp) (by simpa using .nil) (by simpa using enough)
        cases restResult with
        | none =>
          exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,Nat.not_lt.mpr enough,Nat.not_le.mpr enough,
            first,firstRead,second,secondRead,restRead],(by intro target impossible; cases impossible),
            fun _ all => absurd (restTotal all) (by simp)⟩
        | some rest =>
          refine ⟨some ⟨firstTarget,secondTarget,rest⟩,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,
            Nat.not_lt.mpr enough,Nat.not_le.mpr enough,first,firstRead,second,secondRead,restRead],?_,
            fun _ _ => rfl⟩
          intro target same
          cases same
          rw [two_shape enough]
          exact .mk (firstCorrect firstTarget rfl) (secondCorrect secondTarget rfl) (restCorrect rest rfl)
termination_by (sizeOf values,values.val.length+2)
decreasing_by
  all_goals
    simp_wf
    try rw [Prod.lex_def]
    try simp +arith
    try omega
end

/-- Every class axiom maps, when it maps, to its corresponding model axiom;
    every shaped class axiom maps. -/
theorem class_axiom_correct (source : SourceClassAxiomBody) (scope : alloc.vec.Vec U8) :
    ∃ result, class_axiom source scope = .ok result ∧
      (∀ target, result = some target → ClassAxiomModel scope source target) ∧
      (ShapedAxiom source → result.isSome) := by
  rw [class_axiom.eq_def]
  cases source with
  | SubClassOf sub sup =>
    obtain ⟨subResult,subRead,subCorrect,subTotal⟩ := class_correct sub scope
    cases subResult with
    | none =>
      exact ⟨none,by simp [subRead],(by intro target impossible; cases impossible),
        fun shaped => absurd (subTotal shaped.1) (by simp)⟩
    | some subTarget =>
      obtain ⟨supResult,supRead,supCorrect,supTotal⟩ := class_correct sup scope
      cases supResult with
      | none =>
        exact ⟨none,by simp [subRead,supRead],(by intro target impossible; cases impossible),
          fun shaped => absurd (supTotal shaped.2) (by simp)⟩
      | some supTarget =>
        exact ⟨some (.SubClassOf subTarget supTarget),by simp [subRead,supRead],
          (by intro target same; cases same; exact .subClassOf (subCorrect _ rfl) (supCorrect _ rfl)),fun _ => rfl⟩
  | EquivalentClasses members =>
    obtain ⟨result,read,correct,total⟩ := members_of_correct members scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped.1 shaped.2) (by simp)⟩
    | some target =>
      exact ⟨some (.EquivalentClasses target),by simp [read],
        (by intro target' same; cases same; exact .equivalent (correct _ rfl)),fun _ => rfl⟩
  | DisjointClasses members =>
    obtain ⟨result,read,correct,total⟩ := members_of_correct members scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped.1 shaped.2) (by simp)⟩
    | some target =>
      exact ⟨some (.DisjointClasses target),by simp [read],
        (by intro target' same; cases same; exact .disjoint (correct _ rfl)),fun _ => rfl⟩
  | DisjointUnion named members =>
    obtain ⟨result,read,correct,total⟩ := members_of_correct members scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped.1 shaped.2) (by simp)⟩
    | some target =>
      exact ⟨some (.DisjointUnion ⟨IriOf named⟩ target),by simp [read,iri_correct],
        (by intro target' same; cases same; exact .disjointUnion (correct _ rfl)),fun _ => rfl⟩
  | ObjectPropertyDomain property domain =>
    obtain ⟨result,read,correct,total⟩ := class_correct domain scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped) (by simp)⟩
    | some target =>
      exact ⟨some (.ObjectPropertyDomain (PropertyOf property) target),by simp [read,property_correct],
        (by intro target' same; cases same; exact .domain (correct _ rfl)),fun _ => rfl⟩
  | ObjectPropertyRange property range =>
    obtain ⟨result,read,correct,total⟩ := class_correct range scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped) (by simp)⟩
    | some target =>
      exact ⟨some (.ObjectPropertyRange (PropertyOf property) target),by simp [read,property_correct],
        (by intro target' same; cases same; exact .range (correct _ rfl)),fun _ => rfl⟩

/-- Every assertion maps, when it maps, to its corresponding model assertion;
    every shaped assertion maps. -/
theorem assertion_correct (source : SourceAssertionBody) (scope : alloc.vec.Vec U8) :
    ∃ result, assertion source scope = .ok result ∧
      (∀ target, result = some target → AssertionModel scope source target) ∧
      (ShapedAssertion source → result.isSome) := by
  rw [assertion.eq_def]
  cases source with
  | SameIndividual members =>
    obtain ⟨result,read,correct,total⟩ := individual_members_correct members scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped) (by simp)⟩
    | some target =>
      exact ⟨some (.SameIndividual target),by simp [read],
        (by intro target' same; cases same; exact .same (correct target rfl)),fun _ => rfl⟩
  | DifferentIndividuals members =>
    obtain ⟨result,read,correct,total⟩ := individual_members_correct members scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped) (by simp)⟩
    | some target =>
      exact ⟨some (.DifferentIndividuals target),by simp [read],
        (by intro target' same; cases same; exact .different (correct target rfl)),fun _ => rfl⟩
  | ClassAssertion expression member =>
    obtain ⟨result,read,correct,total⟩ := class_correct expression scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped) (by simp)⟩
    | some target =>
      exact ⟨some (.ClassAssertion target (IndividualOf scope member)),by simp [read,individual_correct],
        (by intro target' same; cases same; exact .classAssertion (correct target rfl)),fun _ => rfl⟩
  | ObjectPropertyAssertion role subject object =>
    exact ⟨some (.ObjectPropertyAssertion (PropertyOf role) (IndividualOf scope subject) (IndividualOf scope object)),
      by simp [property_correct,individual_correct],(by intro target same; cases same; exact .propertyAssertion),
      fun _ => rfl⟩
  | NegativeObjectPropertyAssertion role subject object =>
    exact ⟨some (.NegativeObjectPropertyAssertion (PropertyOf role) (IndividualOf scope subject)
      (IndividualOf scope object)),by simp [property_correct,individual_correct],
      (by intro target same; cases same; exact .negativeAssertion),fun _ => rfl⟩

/-- The remaining members of a property list map one by one after the models
    already collected. -/
theorem properties_from_correct (values : alloc.vec.Vec SourceObjectProperty) (index : Usize)
    (out : alloc.vec.Vec model.ObjectPropertyExpression) (start : 2 ≤ index.val)
    (collected : out.val = ((values.val.drop 2).take (index.val-2)).map PropertyOf)
    (inside : index.val ≤ values.val.length) :
    ∃ result, properties_from values index out = .ok result ∧ result.val = (values.val.drop 2).map PropertyOf := by
  rw [properties_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have length : out.val.length = index.val-2 := by
      rw [collected]; simp; omega
    have room : out.val.length < values.val.length := by omega
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (PropertyOf values.val[index.val]) (by scalar_tac))
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have step : (values.val.drop 2).take (next.val-2) =
        (values.val.drop 2).take (index.val-2) ++ [values.val[index.val]] := by
      rw [nextIndex,show index.val+1-2 = (index.val-2)+1 by omega]
      have bound : index.val-2 < (values.val.drop 2).length := by simp; omega
      rw [List.take_succ_eq_append_getElem bound]
      simp [List.getElem_drop,show 2+(index.val-2) = index.val by omega]
    obtain ⟨final,finalRead,finalList⟩ := properties_from_correct values next appended (by omega)
      (by rw [step,contents,collected]; simp) (by omega)
    exact ⟨final,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,room,↓reduceIte,
      alloc.vec.Vec.index_slice_index,lookup,bind_ok,property_correct,push,advance,finalRead],finalList⟩
  · have full : (values.val.drop 2).take (index.val-2) = values.val.drop 2 :=
      List.take_of_length_le (by simp; omega)
    rw [full] at collected
    exact ⟨out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],collected⟩
termination_by values.val.length-index.val
decreasing_by omega
/-- A property list maps exactly when it has two members, to its
    corresponding model member list. -/
theorem property_members_correct (values : alloc.vec.Vec SourceObjectProperty) :
    ∃ result, property_members values = .ok result ∧
      (∀ target, result = some target → PropertyMembersModel values.val target) ∧
      (2 ≤ values.val.length → result.isSome) := by
  rw [property_members]
  by_cases few : values.val.length < 2
  · exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,few,Nat.lt_succ_iff.mp few],
      (by intro target impossible; cases impossible),fun enough => absurd enough (by omega)⟩
  · have enough : 2 ≤ values.val.length := by omega
    have zero : 0 < values.val.length := by omega
    have one : 1 < values.val.length := by omega
    have first : values.index_usize 0#usize = .ok values.val[0] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem zero]
    have second : values.index_usize 1#usize = .ok values.val[1] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem one]
    obtain ⟨rest,restRead,restList⟩ := properties_from_correct values 2#usize
      (alloc.vec.Vec.new model.ObjectPropertyExpression) (by simp) (by simp) (by simpa using enough)
    refine ⟨some ⟨PropertyOf values.val[0],PropertyOf values.val[1],rest⟩,by simp [alloc.vec.Vec.len_val,
      UScalar.lt_equiv,Nat.not_lt.mpr enough,Nat.not_le.mpr enough,first,second,property_correct,restRead],?_,
      fun _ => rfl⟩
    intro target same
    cases same
    obtain ⟨a,b,r,shape⟩ : ∃ a b r, values.val = a :: b :: r := by
      rcases hv : values.val with _ | ⟨a,_ | ⟨b,r⟩⟩
      · rw [hv] at enough; simp at enough
      · rw [hv] at enough; simp at enough
      · exact ⟨a,b,r,rfl⟩
    have e0 : values.val[0] = a := by simp [shape]
    have e1 : values.val[1] = b := by simp [shape]
    have member : PropertyMembersModel (a :: b :: r) ⟨PropertyOf values.val[0],PropertyOf values.val[1],rest⟩ :=
      .members (by simp [e0]) (by simp [e1]) (by simpa [shape] using restList)
    rw [← shape] at member
    exact member
/-- A sub-property maps, when it maps, to its corresponding model; a chain maps
    when it has two members. -/
theorem sub_property_correct (source : SourceSubProperty) :
    ∃ result, sub_property source = .ok result ∧
      (∀ target, result = some target → SubPropertyModel source target) ∧ (ShapedSub source → result.isSome) := by
  rw [sub_property.eq_def]
  cases source with
  | Single value =>
    exact ⟨some (.Single (PropertyOf value)),by simp [property_correct],
      (by intro target same; cases same; exact .single),fun _ => rfl⟩
  | Chain keyword members =>
    obtain ⟨result,read,correct,total⟩ := property_members_correct members
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped) (by simp)⟩
    | some target =>
      exact ⟨some (.Chain target),by simp [read],(by intro target' same; cases same; exact .chain (correct target rfl)),
        fun _ => rfl⟩
theorem characteristic_axiom_correct (characteristic : PropertyCharacteristic) (value : model.ObjectPropertyExpression) :
    characteristic_axiom characteristic value = .ok (CharacteristicOf characteristic value) := by
  cases characteristic <;> rfl
/-- Every property axiom maps, when it maps, to its corresponding model axiom;
    every shaped property axiom maps. -/
theorem property_axiom_correct (source : SourcePropertyAxiomBody) :
    ∃ result, property_axiom source = .ok result ∧
      (∀ target, result = some target → PropertyAxiomModel source target) ∧ (ShapedProperty source → result.isSome) := by
  rw [property_axiom.eq_def]
  cases source with
  | SubObjectPropertyOf sub sup =>
    obtain ⟨result,read,correct,total⟩ := sub_property_correct sub
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped) (by simp)⟩
    | some target =>
      exact ⟨some (.SubObjectPropertyOf target (PropertyOf sup)),by simp [read,property_correct],
        (by intro target' same; cases same; exact .sub (correct target rfl)),fun _ => rfl⟩
  | EquivalentObjectProperties members =>
    obtain ⟨result,read,correct,total⟩ := property_members_correct members
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped) (by simp)⟩
    | some target =>
      exact ⟨some (.EquivalentObjectProperties target),by simp [read],
        (by intro target' same; cases same; exact .equivalent (correct target rfl)),fun _ => rfl⟩
  | DisjointObjectProperties members =>
    obtain ⟨result,read,correct,total⟩ := property_members_correct members
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped) (by simp)⟩
    | some target =>
      exact ⟨some (.DisjointObjectProperties target),by simp [read],
        (by intro target' same; cases same; exact .disjoint (correct target rfl)),fun _ => rfl⟩
  | InverseObjectProperties first second =>
    exact ⟨some (.InverseObjectProperties (PropertyOf first) (PropertyOf second)),by simp [property_correct],
      (by intro target same; cases same; exact .inverse),fun _ => rfl⟩
  | Characteristic characteristic value =>
    exact ⟨some (CharacteristicOf characteristic (PropertyOf value)),
      by simp [property_correct,characteristic_axiom_correct],
      (by intro target same; cases same; exact .characteristic),fun _ => rfl⟩

private theorem axiom_annotations (values : alloc.vec.Vec SourceAnnotation) (scope : alloc.vec.Vec U8) :
    ∃ targets, annotations_from values 0#usize (alloc.vec.Vec.new model.Annotation) scope = .ok targets ∧
      AnnotationsModel scope values.val targets.val :=
  annotations_from_correct values 0#usize (alloc.vec.Vec.new model.Annotation) scope (by simpa using .nil) (by simp)

/-- Every source axiom maps, when it maps, to its corresponding model axiom;
    every shaped source axiom maps. -/
theorem axiom_correct (source : SourceAxiom) (scope : alloc.vec.Vec U8) :
    ∃ result, functional_model.axiom source scope = .ok result ∧
      (∀ target, result = some target → AxiomModel scope source target) ∧ (ShapedSource source → result.isSome) := by
  rw [functional_model.axiom.eq_def]
  cases source with
  | Declaration record =>
    obtain ⟨annotations,annotationsRead,annotationsModel⟩ := axiom_annotations record.annotations scope
    exact ⟨some ⟨annotations,.Declaration (EntityOf record.entity)⟩,by simp [annotationsRead,entity_correct],
      (by intro target same; cases same; exact .declaration annotationsModel),fun _ => rfl⟩
  | Annotation record =>
    obtain ⟨annotations,annotationsRead,annotationsModel⟩ := axiom_annotations record.annotations scope
    exact ⟨some ⟨annotations,AnnotationAxiomOf scope record.body⟩,by simp [annotationsRead,annotation_axiom_correct],
      (by intro target same; cases same; exact .annotation annotationsModel),fun _ => rfl⟩
  | Class record =>
    obtain ⟨result,read,correct,total⟩ := class_axiom_correct record.body scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped) (by simp)⟩
    | some body =>
      obtain ⟨annotations,annotationsRead,annotationsModel⟩ := axiom_annotations record.annotations scope
      exact ⟨some ⟨annotations,body⟩,by simp [read,annotationsRead],
        (by intro target same; cases same; exact .«class» annotationsModel (correct body rfl)),fun _ => rfl⟩
  | Property record =>
    obtain ⟨result,read,correct,total⟩ := property_axiom_correct record.body
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped) (by simp)⟩
    | some body =>
      obtain ⟨annotations,annotationsRead,annotationsModel⟩ := axiom_annotations record.annotations scope
      exact ⟨some ⟨annotations,body⟩,by simp [read,annotationsRead],
        (by intro target same; cases same; exact .property annotationsModel (correct body rfl)),fun _ => rfl⟩
  | Assertion record =>
    obtain ⟨result,read,correct,total⟩ := assertion_correct record.body scope
    cases result with
    | none =>
      exact ⟨none,by simp [read],(by intro target impossible; cases impossible),
        fun shaped => absurd (total shaped) (by simp)⟩
    | some body =>
      obtain ⟨annotations,annotationsRead,annotationsModel⟩ := axiom_annotations record.annotations scope
      exact ⟨some ⟨annotations,body⟩,by simp [read,annotationsRead],
        (by intro target same; cases same; exact .assertion annotationsModel (correct body rfl)),fun _ => rfl⟩

private theorem forall₂_snoc {source : SourceAxiom} {target : model.AnnotatedAxiom} {scope : alloc.vec.Vec U8}
    (last : AxiomModel scope source target) {sources : List SourceAxiom} {targets : List model.AnnotatedAxiom}
    (collected : List.Forall₂ (AxiomModel scope) sources targets) :
    List.Forall₂ (AxiomModel scope) (sources++[source]) (targets++[target]) :=
  List.rel_append collected (List.Forall₂.cons last List.Forall₂.nil)

/-- Axioms map element by element, extending the models already collected;
    they all map when every axiom is shaped. -/
theorem axioms_from_correct (values : alloc.vec.Vec SourceAxiom) (index : Usize)
    (out : alloc.vec.Vec model.AnnotatedAxiom) (scope : alloc.vec.Vec U8)
    (collected : List.Forall₂ (AxiomModel scope) (values.val.take index.val) out.val)
    (inside : index.val ≤ values.val.length) :
    ∃ result, axioms_from values index out scope = .ok result ∧
      (∀ targets, result = some targets → List.Forall₂ (AxiomModel scope) values.val targets.val) ∧
      ((∀ item ∈ values.val, ShapedSource item) → result.isSome) := by
  rw [axioms_from.eq_def]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨result,read,correct,total⟩ := axiom_correct values.val[index.val] scope
    cases result with
    | none =>
      exact ⟨none,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,read],(by intro targets impossible; cases impossible),
        fun all => absurd (total (all _ (List.getElem_mem more))) (by simp)⟩
    | some target =>
      have length := collected.length_eq
      obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out target (by simp at length; scalar_tac))
      obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val+1 := by simpa using nextValue
      obtain ⟨final,finalRead,finalCorrect,finalTotal⟩ := axioms_from_correct values next appended scope
        (by rw [contents,nextIndex,List.take_succ_eq_append_getElem more]; exact forall₂_snoc (correct target rfl) collected)
        (by omega)
      exact ⟨final,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,read,push,advance,finalRead],finalCorrect,finalTotal⟩
  · have full : values.val.take index.val = values.val := List.take_of_length_le (by omega)
    rw [full] at collected
    exact ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],
      (by intro targets same; cases same; exact collected),fun _ => rfl⟩
termination_by values.val.length-index.val
decreasing_by omega

/-- Import targets map to their exact IRIs in order. -/
theorem imports_from_correct (values : alloc.vec.Vec ImportReference) (index : Usize) (out : alloc.vec.Vec model.Iri)
    (collected : out.val = (values.val.take index.val).map (fun reference => IriOf reference.target))
    (inside : index.val ≤ values.val.length) :
    ∃ targets, imports_from values index out = .ok targets ∧
      targets.val = values.val.map (fun reference => IriOf reference.target) := by
  rw [imports_from.eq_def]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have length : out.val.length = index.val := by
      rw [collected]; simp; omega
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (IriOf values.val[index.val].target) (by scalar_tac))
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨targets,targetsRead,targetsCorrect⟩ := imports_from_correct values next appended
      (by rw [contents,nextIndex,List.take_succ_eq_append_getElem more,collected,List.map_append]; rfl)
      (by omega)
    exact ⟨targets,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
      alloc.vec.Vec.index_slice_index,lookup,bind_ok,iri_correct,push,advance,targetsRead],targetsCorrect⟩
  · have full : values.val.take index.val = values.val := List.take_of_length_le (by omega)
    rw [full] at collected
    exact ⟨out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],collected⟩
termination_by values.val.length-index.val
decreasing_by omega

/-- The model of a document: whenever the mapping succeeds, the raw ontology
    corresponds to the document tail, and it succeeds whenever every axiom is
    shaped. -/
theorem document_ontology_correct (document : SourceDocument) (scope : alloc.vec.Vec U8) :
    ∃ result, document_ontology document scope = .ok result ∧
      (∀ ontology, result = some ontology → OntologyModel scope document.tail ontology) ∧
      ((∀ item ∈ document.tail.axioms.val, ShapedSource item) → result.isSome) := by
  rw [document_ontology]
  obtain ⟨axioms,axiomsRead,axiomsCorrect,axiomsTotal⟩ := axioms_from_correct document.tail.axioms 0#usize
    (alloc.vec.Vec.new model.AnnotatedAxiom) scope (by simp) (by simp)
  cases axioms with
  | none =>
    exact ⟨none,by simp [axiomsRead],(by intro ontology impossible; cases impossible),
      fun all => absurd (axiomsTotal all) (by simp)⟩
  | some axioms =>
    obtain ⟨imports,importsRead,importsCorrect⟩ := imports_from_correct document.tail.imports 0#usize
      (alloc.vec.Vec.new model.Iri) (by simp) (by simp)
    obtain ⟨annotations,annotationsRead,annotationsModel⟩ := axiom_annotations document.tail.annotations scope
    refine ⟨some ⟨IdentityOf document.tail.identity,imports,annotations,axioms⟩,
      by simp [axiomsRead,identity_correct,importsRead,annotationsRead],?_,fun _ => rfl⟩
    intro ontology same
    cases same
    exact ⟨rfl,importsCorrect,annotationsModel,axiomsCorrect axioms rfl⟩

section Grammar
open RowlRust.functional_lexer (Tokens)
open RowlRust.functional_classes (ClassError ClassForm)
open RowlRust.functional_class_axioms (ClassAxiomError AxiomForm)
open RowlRust.functional_document (DocumentError)
open Rowl.FunctionalClasses (ClassRun ConnectiveRun MembersRun FillerRun)
open Rowl.FunctionalClassAxioms (ClassStep ListRun BodyRun)
open RowlRust.functional_document (AxiomFamily)
open Rowl.FunctionalDocument (AxiomStep AxiomsRun TailRun)
variable {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}

/-- A number restriction is shaped when its filler, if any, is. -/
private theorem shaped_cardinality {keyword number : functional.Token} {bound : functional_classes.Bound}
    {value : Usize} {property : SourceObjectProperty} {filler : Option SourceClass}
    (inner : ∀ f, filler = some f → Shaped f) : Shaped (.Cardinality keyword bound number value property filler) := by
  cases filler with
  | none => exact .cardinality
  | some f => exact .qualified (inner f rfl)

mutual
/-- Every class expression the independent class grammar accepts is shaped. -/
theorem class_run_shaped {count limit : Nat} :
    ∀ {depth : Nat} {tokens : Tokens} {result : core.result.Result (SourceClass × Tokens) ClassError},
      ClassRun rows source eof count limit depth tokens result →
      ∀ {value : SourceClass} {rest : Tokens}, result = .Ok (value,rest) → Shaped value
  | _, _, _, .empty, _, _, same => by cases same
  | _, _, _, .namedError _ _, _, _, same => by cases same
  | _, _, _, .named _ _, _, _, same => by cases same; exact .named
  | _, _, _, .unsupported _, _, _, same => by cases same
  | _, _, _, .depthLimit _, _, _, same => by cases same
  | _, _, _, .openError _ _, _, _, same => by cases same
  | _, _, _, .connective _ _ body, _, _, same => connective_run_shaped body same
/-- Every connective body the independent class grammar accepts is shaped. -/
theorem connective_run_shaped {count limit : Nat} :
    ∀ {depth : Nat} {keyword : functional.Token} {form : ClassForm} {tokens : Tokens}
      {result : core.result.Result (SourceClass × Tokens) ClassError},
      ConnectiveRun rows source eof count limit depth keyword form tokens result →
      ∀ {value : SourceClass} {rest : Tokens}, result = .Ok (value,rest) → Shaped value
  | _, _, _, _, _, .membersError _, _, _, same => by cases same
  | _, _, _, _, _, .tooFew _ _, _, _, same => by cases same
  | _, _, _, _, _, .junctionCloseError _ _ _, _, _, same => by cases same
  | _, _, .Junction conjunctive, _, _, .junction members enough _, _, _, same => by
    cases same
    have each := members_run_shaped members (by simp) rfl
    cases conjunctive
    · exact .union enough each
    · exact .intersection enough each
  | _, _, _, _, _, .operandError _, _, _, same => by cases same
  | _, _, _, _, _, .complementCloseError _ _, _, _, same => by cases same
  | _, _, _, _, _, .complement operandRun _, _, _, same => by
    cases same
    exact .complement (class_run_shaped operandRun rfl)
  | _, _, _, _, _, .propertyError _, _, _, same => by cases same
  | _, _, _, _, _, .fillerError _ _, _, _, same => by cases same
  | _, _, _, _, _, .restrictionCloseError _ _ _, _, _, same => by cases same
  | _, _, .Restriction existential, _, _, .restriction _ fillerRun _, _, _, same => by
    cases same
    have inner := class_run_shaped fillerRun rfl
    cases existential
    · exact .all inner
    · exact .some inner
  | _, _, _, _, _, .oneOfError _, _, _, same => by cases same
  | _, _, _, _, _, .oneOfCloseError _ _, _, _, same => by cases same
  | _, _, _, _, _, .oneOf list _, _, _, same => by
    cases same
    cases list with
    | ok _ enough => exact .oneOf enough
  | _, _, _, _, _, .valuePropertyError _, _, _, same => by cases same
  | _, _, _, _, _, .valueError _ _, _, _, same => by cases same
  | _, _, _, _, _, .valueCloseError _ _ _, _, _, same => by cases same
  | _, _, _, _, _, .hasValue _ _ _, _, _, same => by cases same; exact .value
  | _, _, _, _, _, .selfPropertyError _, _, _, same => by cases same
  | _, _, _, _, _, .selfCloseError _ _, _, _, same => by cases same
  | _, _, _, _, _, .hasSelf _ _, _, _, same => by cases same; exact .self
  | _, _, _, _, _, .numberError _, _, _, same => by cases same
  | _, _, _, _, _, .countError _ _, _, _, same => by cases same
  | _, _, _, _, _, .countPropertyError _ _ _, _, _, same => by cases same
  | _, _, _, _, _, .countFillerError _ _ _ _, _, _, same => by cases same
  | _, _, _, _, _, .countCloseError _ _ _ _ _, _, _, same => by cases same
  | _, _, _, _, _, .cardinality _ _ _ fillerRun _, _, _, same => by
    cases same
    exact shaped_cardinality (filler_run_shaped fillerRun rfl)
/-- Every member sequence the independent class grammar accepts extends the
    shaped members before it with shaped members. -/
theorem members_run_shaped {count limit : Nat} :
    ∀ {depth : Nat} {prior : List SourceClass} {tokens : Tokens}
      {result : core.result.Result (alloc.vec.Vec SourceClass × Tokens) ClassError},
      MembersRun rows source eof count limit depth prior tokens result → (∀ member ∈ prior, Shaped member) →
      ∀ {records : alloc.vec.Vec SourceClass} {rest : Tokens}, result = .Ok (records,rest) →
        ∀ member ∈ records.val, Shaped member
  | _, _, _, _, .empty contents, earlier, _, _, same => by
    cases same
    rw [contents]
    exact earlier
  | _, _, _, _, .stop _ contents, earlier, _, _, same => by
    cases same
    rw [contents]
    exact earlier
  | _, _, _, _, .countLimit _ _, _, _, _, same => by cases same
  | _, _, _, _, .memberError _ _ _, _, _, _, same => by cases same
  | _, _, _, _, .member _ _ memberRun later, earlier, _, _, same =>
    members_run_shaped later (by
      intro member inside
      rcases List.mem_append.mp inside with old | new
      · exact earlier member old
      · rw [List.mem_singleton.mp new]
        exact class_run_shaped memberRun rfl) same
/-- Every filler the independent class grammar accepts is shaped. -/
theorem filler_run_shaped {count limit : Nat} :
    ∀ {depth : Nat} {tokens : Tokens} {result : core.result.Result (Option SourceClass × Tokens) ClassError},
      FillerRun rows source eof count limit depth tokens result →
      ∀ {filler : Option SourceClass} {rest : Tokens}, result = .Ok (filler,rest) →
        ∀ value, filler = some value → Shaped value
  | _, _, _, .empty, _, _, same, _, isSome => by cases same; cases isSome
  | _, _, _, .stop _, _, _, same, _, isSome => by cases same; cases isSome
  | _, _, _, .fillerError _ _, _, _, same, _, _ => by cases same
  | _, _, _, .filler _ fillerRun, _, _, same, _, isSome => by
    cases same
    cases isSome
    exact class_run_shaped fillerRun rfl
end

/-- Every class expression the class axiom grammar accepts is shaped. -/
theorem class_step_shaped {count limit depth : Nat} {tokens rest : Tokens} {value : SourceClass}
    {result : core.result.Result (SourceClass × Tokens) ClassAxiomError}
    (run : ClassStep rows source eof count limit depth tokens result) (same : result = .Ok (value,rest)) :
    Shaped value := by
  cases run with
  | error _ => cases same
  | ok run => cases same; exact class_run_shaped run rfl
/-- Every class expression list the class axiom grammar accepts has at least two
    shaped members. -/
theorem list_run_shaped {count limit depth : Nat} {tokens rest : Tokens} {list : alloc.vec.Vec SourceClass}
    {result : core.result.Result (alloc.vec.Vec SourceClass × Tokens) ClassAxiomError}
    (run : ListRun rows source eof count limit depth tokens result) (same : result = .Ok (list,rest)) :
    2 ≤ list.val.length ∧ ∀ member ∈ list.val, Shaped member := by
  cases run with
  | error _ => cases same
  | tooFew _ _ => cases same
  | ok run enough => cases same; exact ⟨enough,members_run_shaped run (by simp) rfl⟩
/-- Every class axiom body the class axiom grammar accepts is shaped. -/
theorem body_run_shaped {count limit depth : Nat} {form : AxiomForm} {tokens rest : Tokens}
    {body : SourceClassAxiomBody} {result : core.result.Result (SourceClassAxiomBody × Tokens) ClassAxiomError}
    (run : BodyRun rows source eof count limit depth form tokens result) (same : result = .Ok (body,rest)) :
    ShapedAxiom body := by
  cases run with
  | subClassOf subRun supRun =>
    cases same; exact And.intro (class_step_shaped subRun rfl) (class_step_shaped supRun rfl)
  | equivalent list => cases same; exact list_run_shaped list rfl
  | disjoint list => cases same; exact list_run_shaped list rfl
  | disjointUnion _ list => cases same; exact list_run_shaped list rfl
  | domain _ domainRun => cases same; exact class_step_shaped domainRun rfl
  | range _ rangeRun => cases same; exact class_step_shaped rangeRun rfl
  | _ => cases same
/-- Every class axiom the class axiom grammar accepts is shaped. -/
theorem class_axiom_run_shaped {annotationCount annotationIri annotationLexical annotationDepth classCount classIri
      classDepth : Nat} {tokens rest : Tokens} {record : functional_class_axioms.SourceClassAxiom}
    {result : core.result.Result (functional_class_axioms.SourceClassAxiom × Tokens) ClassAxiomError}
    (run : Rowl.FunctionalClassAxioms.AxiomRun rows source eof annotationCount annotationIri annotationLexical
      annotationDepth classCount classIri classDepth tokens result) (same : result = .Ok (record,rest)) :
    ShapedAxiom record.body := by
  cases run with
  | ready _ _ _ bodyRun _ => cases same; exact body_run_shaped bodyRun rfl
  | _ => cases same
/-- Every assertion body the assertion grammar accepts is shaped. -/
theorem assertion_body_run_shaped {count limit depth : Nat} {form : functional_assertions.AssertionForm}
    {tokens rest : Tokens} {body : SourceAssertionBody}
    {result : core.result.Result (SourceAssertionBody × Tokens) functional_assertions.AssertionError}
    (run : Rowl.FunctionalAssertions.BodyRun rows source eof count limit depth form tokens result)
    (same : result = .Ok (body,rest)) : ShapedAssertion body := by
  cases run with
  | same membersRun =>
    cases same
    cases membersRun with
    | ok list =>
      cases list with
      | ok _ enough => exact enough
  | different membersRun =>
    cases same
    cases membersRun with
    | ok list =>
      cases list with
      | ok _ enough => exact enough
  | classAssertion classRun _ =>
    cases same
    cases classRun with
    | ok classRun => exact class_run_shaped classRun rfl
  | propertyAssertion _ => cases same; exact trivial
  | negativeAssertion _ => cases same; exact trivial
  | _ => cases same
/-- Every assertion the assertion grammar accepts is shaped. -/
theorem assertion_run_shaped {annotationCount annotationIri annotationLexical annotationDepth classCount classIri
      classDepth : Nat} {tokens rest : Tokens} {record : functional_assertions.SourceAssertion}
    {result : core.result.Result (functional_assertions.SourceAssertion × Tokens) functional_assertions.AssertionError}
    (run : Rowl.FunctionalAssertions.AxiomRun rows source eof annotationCount annotationIri annotationLexical
      annotationDepth classCount classIri classDepth tokens result) (same : result = .Ok (record,rest)) :
    ShapedAssertion record.body := by
  cases run with
  | ready _ _ _ bodyRun _ => cases same; exact assertion_body_run_shaped bodyRun rfl
  | _ => cases same
/-- Every property axiom body the property axiom grammar accepts is shaped. -/
theorem property_body_run_shaped {count limit : Nat} {form : functional_property_axioms.AxiomForm}
    {tokens rest : Tokens} {body : SourcePropertyAxiomBody}
    {result : core.result.Result (SourcePropertyAxiomBody × Tokens) functional_property_axioms.PropertyAxiomError}
    (run : Rowl.FunctionalPropertyAxioms.BodyRun rows source eof count limit form tokens result)
    (same : result = .Ok (body,rest)) : ShapedProperty body := by
  cases run with
  | subProperty subRun _ =>
    cases same
    cases subRun with
    | single _ _ => exact trivial
    | chain _ _ listRun _ =>
      cases listRun with
      | ok _ enough => exact enough
  | equivalent listRun =>
    cases same
    cases listRun with
    | ok _ enough => exact enough
  | disjoint listRun =>
    cases same
    cases listRun with
    | ok _ enough => exact enough
  | inverse _ _ => cases same; exact trivial
  | characteristic _ => cases same; exact trivial
  | _ => cases same
/-- Every property axiom the property axiom grammar accepts is shaped. -/
theorem property_axiom_run_shaped {annotationCount annotationIri annotationLexical annotationDepth classCount
      classIri : Nat} {tokens rest : Tokens} {record : functional_property_axioms.SourcePropertyAxiom}
    {result : core.result.Result (functional_property_axioms.SourcePropertyAxiom × Tokens)
      functional_property_axioms.PropertyAxiomError}
    (run : Rowl.FunctionalPropertyAxioms.AxiomRun rows source eof annotationCount annotationIri annotationLexical
      annotationDepth classCount classIri tokens result) (same : result = .Ok (record,rest)) :
    ShapedProperty record.body := by
  cases run with
  | ready _ _ _ bodyRun _ => cases same; exact property_body_run_shaped bodyRun rfl
  | _ => cases same
/-- Every axiom the document grammar reads is shaped. -/
theorem axiom_step_shaped {annotationCount annotationIri annotationLexical annotationDepth classCount classIri
      classDepth : Nat} {family : AxiomFamily} {tokens rest : Tokens} {offset : Usize} {item : SourceAxiom}
    {result : core.result.Result (SourceAxiom × Tokens) DocumentError}
    (run : AxiomStep rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount
      classIri classDepth family tokens offset result) (same : result = .Ok (item,rest)) :
    ShapedSource item := by
  cases run with
  | declaration _ => cases same; exact trivial
  | annotation _ => cases same; exact trivial
  | «class» run => cases same; exact class_axiom_run_shaped run rfl
  | property run => cases same; exact property_axiom_run_shaped run rfl
  | assertion run => cases same; exact assertion_run_shaped run rfl
  | _ => cases same
/-- Every axiom sequence the document grammar reads extends the shaped axioms
    before it with shaped axioms. -/
theorem axioms_run_shaped {annotationCount annotationIri annotationLexical annotationDepth classCount classIri
      classDepth axiomCount : Nat} :
    ∀ {prior : List SourceAxiom} {tokens : Tokens}
      {result : core.result.Result (alloc.vec.Vec SourceAxiom × Tokens) DocumentError},
      AxiomsRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth axiomCount prior tokens result → (∀ item ∈ prior, ShapedSource item) →
      ∀ {records : alloc.vec.Vec SourceAxiom} {rest : Tokens}, result = .Ok (records,rest) →
        ∀ item ∈ records.val, ShapedSource item
  | _, _, _, .empty, _, _, _, same => by cases same
  | _, _, _, .stop _ contents, earlier, _, _, same => by
    cases same
    rw [contents]
    exact earlier
  | _, _, _, .other _ _, _, _, _, same => by cases same
  | _, _, _, .limit _ _ _, _, _, _, same => by cases same
  | _, _, _, .stepError _ _ _ _, _, _, _, same => by cases same
  | _, _, _, .step _ _ _ stepRun later, earlier, _, _, same =>
    axioms_run_shaped later (by
      intro item inside
      rcases List.mem_append.mp inside with old | new
      · exact earlier item old
      · rw [List.mem_singleton.mp new]
        exact axiom_step_shaped stepRun rfl) same
/-- Every axiom of a document tail the document grammar reads is shaped. -/
theorem tail_run_shaped {importCount iriLimit annotationCount annotationIri annotationLexical annotationDepth
      classCount classIri classDepth axiomCount : Nat} {tokens : Tokens} {tail : SourceDocumentTail}
    {result : core.result.Result SourceDocumentTail DocumentError}
    (run : TailRun rows source eof importCount iriLimit annotationCount annotationIri annotationLexical annotationDepth
      classCount classIri classDepth axiomCount tokens result) (same : result = .Ok tail) :
    ∀ item ∈ tail.axioms.val, ShapedSource item := by
  cases run with
  | ready _ _ axiomsRun => cases same; exact axioms_run_shaped axiomsRun (by simp) rfl
  | _ => cases same
end Grammar
end Rowl.FunctionalModel
