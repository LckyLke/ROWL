import Rowl.TboxTableau

/-!
TBox internalization of an axiom closure, proved against the independent
Direct Semantics. Every supported axiom becomes a negation-normal-form concept
that holds at every element exactly when the axiom holds, in every
interpretation fixing owl:Thing and owl:Nothing; assertions about individuals
become the top concept, since they constrain individuals rather than every
element. The closure's concept is the conjunction. The internalization succeeds
exactly when every axiom is supported.
-/
namespace Rowl.Internalization
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation classDenote)
open Rowl.Nnf (conceptDenote InAlc Polar Fixes Correct Every nnf_total_correct nnf_meaning connect_correct
  copy_iri_identity)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v

/-- The supported axioms: declarations and annotation axioms, which impose
    nothing, class, domain and range axioms over ALC class expressions and named
    object properties, inclusions and equivalences between named object
    properties and transitivity of a named object property, which the TBox
    concept leaves to the role box, and assertions, which it leaves to the
    completion for individuals. -/
def SupportedAxiom : Axiom → Prop
  | .Declaration _ => True
  | .SubClassOf a b => InAlc a ∧ InAlc b
  | .EquivalentClasses xs => ∀ e ∈ xs.elements, InAlc e
  | .DisjointClasses xs => ∀ e ∈ xs.elements, InAlc e
  | .DisjointUnion _ xs => ∀ e ∈ xs.elements, InAlc e
  | .ObjectPropertyDomain p e => (∃ q, p = .Property q) ∧ InAlc e
  | .ObjectPropertyRange p e => (∃ q, p = .Property q) ∧ InAlc e
  | .SubObjectPropertyOf (.Single (.Property _)) (.Property _) => True
  | .EquivalentObjectProperties xs => ∀ p ∈ xs.elements, ∃ q, p = .Property q
  | .TransitiveObjectProperty (.Property _) => True
  | .AnnotationAssertion _ _ _ => True
  | .SubAnnotationPropertyOf _ _ => True
  | .AnnotationPropertyDomain _ _ => True
  | .AnnotationPropertyRange _ _ => True
  | .ClassAssertion _ _ => True
  | .ObjectPropertyAssertion _ _ _ => True
  | .NegativeObjectPropertyAssertion _ _ _ => True
  | _ => False
/-- Class assertions and positive and negative object property assertions:
    they constrain individuals, not every element. -/
def Assertion : Axiom → Prop
  | .ClassAssertion _ _ => True
  | .ObjectPropertyAssertion _ _ _ => True
  | .NegativeObjectPropertyAssertion _ _ _ => True
  | _ => False

/-- The role axioms the role box reads: inclusions and equivalences between
    named object properties and transitivity of a named object property. -/
def RoleAxiom : Axiom → Prop
  | .SubObjectPropertyOf (.Single (.Property _)) (.Property _) => True
  | .EquivalentObjectProperties xs => ∀ p ∈ xs.elements, ∃ q, p = .Property q
  | .TransitiveObjectProperty (.Property _) => True
  | _ => False

variable {Object : Type u} {Value : Type v}

/-- What an axiom requires of every element: nothing for an assertion or a role
    axiom, the axiom itself otherwise. -/
def TBoxPart (I : Interpretation Object Value) (a : Axiom) : Prop :=
  Assertion a ∨ RoleAxiom a ∨ Rowl.Owl.satisfies I a

/-- Equivalent classes hold at each element all together or not at all. -/
theorem all_equal_iff (I : Interpretation Object Value) (xs : List ClassExpression) :
    Rowl.Owl.allEqual xs (classDenote I) ↔
      ∀ x, (∀ e ∈ xs, classDenote I e x) ∨ (∀ e ∈ xs, ¬ classDenote I e x) := by
  unfold Rowl.Owl.allEqual
  constructor
  · intro same x
    by_cases found : ∃ e ∈ xs, classDenote I e x
    · obtain ⟨e,member,holds⟩ := found
      left
      intro d dmem
      rw [congrFun (same d dmem e member) x]
      exact holds
    · right
      intro d dmem holds
      exact found ⟨d,dmem,holds⟩
  · intro split a amem b bmem
    funext x
    apply propext
    rcases split x with every | none
    · exact ⟨fun _ => every b bmem,fun _ => every a amem⟩
    · exact ⟨fun h => absurd h (none a amem),fun h => absurd h (none b bmem)⟩
/-- Pairwise disjointness of denotations, read one element at a time. -/
theorem pairwise_disjoint_iff (I : Interpretation Object Value) (xs : List ClassExpression) :
    Rowl.Owl.pairwiseDisjoint xs (classDenote I) ↔
      ∀ x, xs.Pairwise (fun a b => ¬ (classDenote I a x ∧ classDenote I b x)) := by
  unfold Rowl.Owl.pairwiseDisjoint
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.pairwise_cons,ih]
    constructor
    · rintro ⟨head,tail⟩ x
      exact ⟨fun b member => head b member x,tail x⟩
    · intro every
      exact ⟨fun b member x => (every x).1 b member,fun x => (every x).2⟩

/-- A translation fails exactly outside ALC and otherwise means the expression
    under the polarity. -/
private theorem translate (e : ClassExpression) (positive : Bool) :
    ∃ result, nnf.nnf e positive = .ok result ∧ (result.isSome ↔ InAlc e) ∧
      ∀ concept, result = some concept → ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        Fixes I → ∀ x, conceptDenote I concept x ↔ Polar positive (classDenote I e x) := by
  obtain ⟨result,executed,correct⟩ := nnf_total_correct.{u,v} e positive
  refine ⟨result,executed,?_,?_⟩
  · cases result with
    | none => simpa [Correct] using correct
    | some concept => exact ⟨fun _ => correct.1,fun _ => rfl⟩
  · intro concept same
    subst same
    exact correct.2

private theorem apart_from_correct (member : ClassExpression) (values : alloc.vec.Vec ClassExpression)
    (index : Usize) (joined : nnf.NnfConcept) :
    ∃ result, alc_ontology.apart_from member values index joined = .ok result ∧
      (result.isSome ↔ (values.val.drop index.val = [] ∨ InAlc member) ∧ ∀ e ∈ values.val.drop index.val, InAlc e) ∧
      ∀ concept, result = some concept → ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        Fixes I → ∀ x, (conceptDenote I concept x ↔ conceptDenote I joined x ∧
          ∀ e ∈ values.val.drop index.val, ¬ (classDenote I member x ∧ classDenote I e x)) := by
  rw [alc_ontology.apart_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨head,headRead,headSupport,headMeaning⟩ := translate.{u,v} member false
    cases head with
    | none =>
      refine ⟨none,?_,?_,by intro concept impossible; cases impossible⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,headRead,bind_ok]
      · have outside : ¬ InAlc member := by simpa using headSupport
        have nonempty : values.val.drop index.val ≠ [] := by rw [split]; exact List.cons_ne_nil _ _
        simp only [Option.isSome_none,Bool.false_eq_true,false_iff,not_and]
        intro located
        exact absurd (located.resolve_left nonempty) outside
    | some left =>
      obtain ⟨element,elementRead,elementSupport,elementMeaning⟩ := translate.{u,v} values.val[index.val] false
      cases element with
      | none =>
        refine ⟨none,?_,?_,by intro concept impossible; cases impossible⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,headRead,elementRead]
        · have outside : ¬ InAlc values.val[index.val] := by simpa using elementSupport
          simp only [Option.isSome_none,Bool.false_eq_true,false_iff,not_and]
          intro _ every
          exact outside (every _ (by rw [split]; exact List.mem_cons_self ..))
      | some right =>
        obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIndex : next.val = index.val+1 := by simpa using nextValue
        obtain ⟨result,executed,support,meaning⟩ := apart_from_correct member values next
          (.And joined (.Or left right))
        refine ⟨result,?_,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,headRead,elementRead,advance,executed]
        · have memberIn : InAlc member := headSupport.mp rfl
          have elementIn : InAlc values.val[index.val] := elementSupport.mp rfl
          rw [support,nextIndex,split]
          simp only [memberIn,or_true,true_and,List.forall_mem_cons,elementIn]
        · intro concept same Object Value I fixes x
          rw [meaning concept same Object Value I fixes x,split,nextIndex]
          have one := headMeaning left rfl Object Value I fixes x
          have two := elementMeaning right rfl Object Value I fixes x
          simp only [conceptDenote,one,two,Polar,List.forall_mem_cons]
          tauto
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some joined,?_,?_,?_⟩
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more]
    · simp [empty]
    · intro concept same Object Value I fixes x
      cases same
      simp [empty]
termination_by values.val.length - index.val
decreasing_by omega

private theorem pairwise_from_correct (values : alloc.vec.Vec ClassExpression) (supported : ∀ e ∈ values.val, InAlc e)
    (index : Usize) (joined : nnf.NnfConcept) :
    ∃ concept, alc_ontology.pairwise_from values index joined = .ok (some concept) ∧
      ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I → ∀ x,
        (conceptDenote I concept x ↔ conceptDenote I joined x ∧
          (values.val.drop index.val).Pairwise (fun a b => ¬ (classDenote I a x ∧ classDenote I b x))) := by
  rw [alc_ontology.pairwise_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨apart,apartRead,apartSupport,apartMeaning⟩ := apart_from_correct.{u,v} values.val[index.val] values next joined
    have later : ∀ e ∈ values.val.drop next.val, InAlc e := fun e member => supported e (List.mem_of_mem_drop member)
    obtain ⟨step,rfl⟩ : ∃ step, apart = some step :=
      Option.isSome_iff_exists.mp (apartSupport.mpr ⟨.inr (supported _ (List.getElem_mem more)),later⟩)
    obtain ⟨concept,executed,meaning⟩ := pairwise_from_correct values supported next step
    refine ⟨concept,?_,?_⟩
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,advance,apartRead,executed]
    · intro Object Value I fixes x
      rw [meaning Object Value I fixes x,apartMeaning step rfl Object Value I fixes x,split,nextIndex,
        List.pairwise_cons]
      tauto
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨joined,?_,?_⟩
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more]
    · intro Object Value I fixes x
      simp [empty]
termination_by values.val.length - index.val
decreasing_by omega

/-- Pairwise disjointness of all member occurrences: exact support, and meaning. -/
theorem pairwise_correct (members : AtLeastTwo ClassExpression) :
    ∃ result, alc_ontology.pairwise members = .ok result ∧
      (result.isSome ↔ ∀ e ∈ members.elements, InAlc e) ∧
      ∀ concept, result = some concept → ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        Fixes I → ∀ x, (conceptDenote I concept x ↔
          members.elements.Pairwise (fun a b => ¬ (classDenote I a x ∧ classDenote I b x))) := by
  rw [alc_ontology.pairwise]
  obtain ⟨first,firstRead,firstSupport,firstMeaning⟩ := translate.{u,v} members.first false
  cases first with
  | none =>
    refine ⟨none,by simp only [firstRead,bind_ok],?_,by intro concept impossible; cases impossible⟩
    have outside : ¬ InAlc members.first := by simpa using firstSupport
    simp [AtLeastTwo.elements,outside]
  | some first =>
    obtain ⟨second,secondRead,secondSupport,secondMeaning⟩ := translate.{u,v} members.second false
    cases second with
    | none =>
      refine ⟨none,by simp only [firstRead,secondRead,bind_ok],?_,by intro concept impossible; cases impossible⟩
      have outside : ¬ InAlc members.second := by simpa using secondSupport
      simp [AtLeastTwo.elements,outside]
    | some second =>
      have firstIn : InAlc members.first := firstSupport.mp rfl
      have secondIn : InAlc members.second := secondSupport.mp rfl
      have zero : (0#usize).val = 0 := rfl
      obtain ⟨one,oneRead,oneSupport,oneMeaning⟩ := apart_from_correct.{u,v} members.first members.rest 0#usize
        (.Or first second)
      cases one with
      | none =>
        refine ⟨none,by simp only [firstRead,secondRead,bind_ok,oneRead],?_,
          by intro concept impossible; cases impossible⟩
        have outside : ¬ ∀ e ∈ members.rest.val, InAlc e := by simpa [zero,firstIn] using oneSupport
        simp only [Option.isSome_none,Bool.false_eq_true,false_iff,AtLeastTwo.elements,List.forall_mem_cons,
          not_and]
        intro _ _
        exact outside
      | some one =>
        have restIn : ∀ e ∈ members.rest.val, InAlc e := by
          have := oneSupport.mp rfl
          simpa [zero] using this.2
        obtain ⟨two,twoRead,twoSupport,twoMeaning⟩ := apart_from_correct.{u,v} members.second members.rest 0#usize one
        obtain ⟨two,rfl⟩ : ∃ two', two = some two' :=
          Option.isSome_iff_exists.mp (twoSupport.mpr ⟨.inr secondIn,by simpa [zero] using restIn⟩)
        obtain ⟨concept,executed,meaning⟩ := pairwise_from_correct.{u,v} members.rest restIn 0#usize two
        refine ⟨some concept,by simp only [firstRead,secondRead,bind_ok,oneRead,twoRead,executed],?_,?_⟩
        · refine ⟨fun _ => ?_,fun _ => rfl⟩
          simp only [AtLeastTwo.elements,List.forall_mem_cons]
          exact ⟨firstIn,secondIn,restIn⟩
        · intro concept' same Object Value I fixes x
          cases same
          rw [meaning Object Value I fixes x,twoMeaning two rfl Object Value I fixes x,
            oneMeaning one rfl Object Value I fixes x]
          have negatedFirst := firstMeaning first rfl Object Value I fixes x
          have negatedSecond := secondMeaning second rfl Object Value I fixes x
          simp only [AtLeastTwo.elements,List.pairwise_cons,List.forall_mem_cons,conceptDenote,negatedFirst,
            negatedSecond,Polar,zero,List.drop_zero]
          tauto

/-- One axiom: support exactly as specified, and a concept holding at every
    element exactly when the axiom holds. -/
theorem is_named_correct (p : ObjectPropertyExpression) :
    alc_ontology.is_named p = .ok (decide (∃ q, p = .Property q)) := by
  cases p <;> simp [alc_ontology.is_named]
private theorem named_from_correct (values : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) :
    alc_ontology.named_from values index = .ok (decide (∀ p ∈ values.val.drop index.val, ∃ q, p = .Property q)) := by
  rw [alc_ontology.named_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := named_from_correct values next
    rw [nextIndex] at rest
    rw [split]
    by_cases here : ∃ q, values.val[index.val] = .Property q
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,is_named_correct,here,decide_true,advance,rest,List.forall_mem_cons,true_and]
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,is_named_correct,here,decide_false,Bool.false_eq_true,List.forall_mem_cons,false_and]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by values.val.length - index.val
decreasing_by omega
/-- The member check of an equivalence decides whether every member is a named
    object property. -/
theorem named_members_correct (members : AtLeastTwo ObjectPropertyExpression) :
    alc_ontology.named_members members =
      .ok (decide (∀ p ∈ members.elements, ∃ q, p = .Property q)) := by
  rw [alc_ontology.named_members]
  have rest := named_from_correct members.rest 0#usize
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at rest
  by_cases first : ∃ q, members.first = .Property q
  · by_cases second : ∃ q, members.second = .Property q
    · simp [is_named_correct,first,second,rest,AtLeastTwo.elements]
    · simp [is_named_correct,first,second,AtLeastTwo.elements]
  · simp [is_named_correct,first,AtLeastTwo.elements]

theorem axiom_concept_correct (statement : Axiom) :
    ∃ result, alc_ontology.axiom_concept statement = .ok result ∧
      (result.isSome ↔ SupportedAxiom statement) ∧
      ∀ concept, result = some concept → ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        Fixes I → (TBoxPart I statement ↔ ∀ x, conceptDenote I concept x) := by
  have child : ∀ members : AtLeastTwo ClassExpression, ∀ e ∈ members.elements, ∀ polarity,
      ∃ result, nnf.nnf e polarity = .ok result ∧ Correct.{u,v} e polarity result :=
    fun _ e _ polarity => nnf_total_correct e polarity
  cases statement with
  | Declaration _ =>
    refine ⟨some .Top,by simp [alc_ontology.axiom_concept],by simp [SupportedAxiom],?_⟩
    intro concept same Object Value I fixes
    simp only [TBoxPart,Assertion,RoleAxiom,false_or]
    cases same
    simp [Rowl.Owl.satisfies,conceptDenote]
  | SubClassOf a b =>
    obtain ⟨outside,outsideRead,outsideSupport,outsideMeaning⟩ := translate.{u,v} a false
    obtain ⟨inside,insideRead,insideSupport,insideMeaning⟩ := translate.{u,v} b true
    cases outside with
    | none =>
      refine ⟨none,by simp [alc_ontology.axiom_concept,outsideRead],?_,by simp⟩
      have absent : ¬ InAlc a := by simpa using outsideSupport
      simp [SupportedAxiom,absent]
    | some outside =>
      cases inside with
      | none =>
        refine ⟨none,by simp [alc_ontology.axiom_concept,outsideRead,insideRead],?_,by simp⟩
        have absent : ¬ InAlc b := by simpa using insideSupport
        simp [SupportedAxiom,absent]
      | some inside =>
        refine ⟨some (.Or outside inside),by simp [alc_ontology.axiom_concept,outsideRead,insideRead],?_,?_⟩
        · simp [SupportedAxiom,outsideSupport.mp rfl,insideSupport.mp rfl]
        · intro concept same Object Value I fixes
          simp only [TBoxPart,Assertion,RoleAxiom,false_or]
          cases same
          simp only [Rowl.Owl.satisfies,conceptDenote,outsideMeaning outside rfl Object Value I fixes,
            insideMeaning inside rfl Object Value I fixes,Polar]
          constructor
          · intro holds x
            by_cases inA : classDenote I a x
            · exact .inr (holds x inA)
            · exact .inl inA
          · intro holds x inA
            exact (holds x).resolve_left (not_not_intro inA)
  | EquivalentClasses xs =>
    obtain ⟨every,everyRead,everySupport,everyMeaning⟩ := connect_correct.{u,v} xs true true (child xs)
    obtain ⟨absent,absentRead,absentSupport,absentMeaning⟩ := connect_correct.{u,v} xs false true (child xs)
    cases every with
    | none =>
      refine ⟨none,by simp [alc_ontology.axiom_concept,everyRead],?_,by simp⟩
      simpa [SupportedAxiom] using everySupport
    | some every =>
      cases absent with
      | none =>
        refine ⟨none,by simp [alc_ontology.axiom_concept,everyRead,absentRead],?_,by simp⟩
        simpa [SupportedAxiom] using absentSupport
      | some absent =>
        refine ⟨some (.Or every absent),by simp [alc_ontology.axiom_concept,everyRead,absentRead],?_,?_⟩
        · simpa [SupportedAxiom] using everySupport
        · intro concept same Object Value I fixes
          simp only [TBoxPart,Assertion,RoleAxiom,false_or]
          cases same
          simp only [Rowl.Owl.satisfies]
          rw [all_equal_iff]
          simp only [conceptDenote,everyMeaning every rfl Object Value I fixes,
            absentMeaning absent rfl Object Value I fixes,Every,Polar]
  | DisjointClasses xs =>
    obtain ⟨result,executed,support,meaning⟩ := pairwise_correct.{u,v} xs
    refine ⟨result,by simp only [alc_ontology.axiom_concept]; exact executed,
      by simpa [SupportedAxiom] using support,?_⟩
    intro concept same Object Value I fixes
    simp only [TBoxPart,Assertion,RoleAxiom,false_or]
    simp only [Rowl.Owl.satisfies]
    rw [pairwise_disjoint_iff]
    exact forall_congr' fun x => (meaning concept same Object Value I fixes x).symm
  | DisjointUnion c xs =>
    obtain ⟨ci⟩ := c
    have named : ∀ positive, ∃ concept, nnf.nnf (.Class ⟨ci⟩) positive = .ok (some concept) := by
      intro positive
      obtain ⟨result,read,support,_⟩ := translate.{u,v} (.Class ⟨ci⟩) positive
      cases result with
      | none => simp [InAlc] at support
      | some concept => exact ⟨concept,read⟩
    obtain ⟨outside,outsideRead⟩ := named false
    obtain ⟨inside,insideRead⟩ := named true
    obtain ⟨found,foundRead,foundSupport,foundMeaning⟩ := connect_correct.{u,v} xs true false (child xs)
    obtain ⟨absent,absentRead,absentSupport,absentMeaning⟩ := connect_correct.{u,v} xs false true (child xs)
    obtain ⟨disjoint,disjointRead,disjointSupport,disjointMeaning⟩ := pairwise_correct.{u,v} xs
    cases found with
    | none =>
      refine ⟨none,by simp [alc_ontology.axiom_concept,copy_iri_identity,outsideRead,insideRead,foundRead],?_,
        by simp⟩
      simpa [SupportedAxiom] using foundSupport
    | some found =>
      cases absent with
      | none =>
        refine ⟨none,by simp [alc_ontology.axiom_concept,copy_iri_identity,outsideRead,insideRead,foundRead,
          absentRead],?_,by simp⟩
        simpa [SupportedAxiom] using absentSupport
      | some absent =>
        cases disjoint with
        | none =>
          refine ⟨none,by simp [alc_ontology.axiom_concept,copy_iri_identity,outsideRead,insideRead,foundRead,
            absentRead,disjointRead],?_,by simp⟩
          simpa [SupportedAxiom] using disjointSupport
        | some disjoint =>
          refine ⟨some (.And (.And (.Or outside found) (.Or inside absent)) disjoint),
            by simp [alc_ontology.axiom_concept,copy_iri_identity,outsideRead,insideRead,foundRead,absentRead,
              disjointRead],by simpa [SupportedAxiom] using foundSupport,?_⟩
          intro concept same Object Value I fixes
          simp only [TBoxPart,Assertion,RoleAxiom,false_or]
          cases same
          have outsideMeaning := nnf_meaning (.Class ⟨ci⟩) false outside outsideRead I fixes
          have insideMeaning := nnf_meaning (.Class ⟨ci⟩) true inside insideRead I fixes
          simp only [Rowl.Owl.satisfies]
          rw [pairwise_disjoint_iff]
          simp only [conceptDenote,outsideMeaning,insideMeaning,foundMeaning found rfl Object Value I fixes,
            absentMeaning absent rfl Object Value I fixes,disjointMeaning disjoint rfl Object Value I fixes,
            Every,Polar,classDenote]
          have negated : ∀ x, (∀ e ∈ xs.elements, ¬ classDenote I e x) ↔ ¬ ∃ e ∈ xs.elements, classDenote I e x := by
            intro x; simp
          simp only [negated]
          constructor
          · rintro ⟨same,separate⟩ x
            refine ⟨?_,separate x⟩
            by_cases member : I.classes ⟨ci⟩ x
            · exact ⟨.inr ((same x).mp member),.inl member⟩
            · exact ⟨.inl member,.inr fun found => member ((same x).mpr found)⟩
          · intro holds
            refine ⟨fun x => ⟨fun member => (holds x).1.1.resolve_left (not_not_intro member),
              fun found => (holds x).1.2.resolve_right (not_not_intro found)⟩,fun x => (holds x).2⟩
  | ObjectPropertyDomain p e =>
    cases p with
    | Inverse _ =>
      exact ⟨none,by simp [alc_ontology.axiom_concept],by simp [SupportedAxiom],by simp⟩
    | Property r =>
      obtain ⟨ri⟩ := r
      obtain ⟨inside,insideRead,insideSupport,insideMeaning⟩ := translate.{u,v} e true
      cases inside with
      | none =>
        refine ⟨none,by simp [alc_ontology.axiom_concept,insideRead],?_,by simp⟩
        have absent : ¬ InAlc e := by simpa using insideSupport
        simp [SupportedAxiom,absent]
      | some inside =>
        refine ⟨some (.Or (.Forall ⟨ri⟩ .Bottom) inside),
          by simp [alc_ontology.axiom_concept,insideRead,copy_iri_identity],?_,?_⟩
        · simp [SupportedAxiom,insideSupport.mp rfl]
        · intro concept same Object Value I fixes
          simp only [TBoxPart,Assertion,RoleAxiom,false_or]
          cases same
          simp only [Rowl.Owl.satisfies,Rowl.Owl.objectRelation,conceptDenote,
            insideMeaning inside rfl Object Value I fixes,Polar]
          constructor
          · intro holds x
            by_cases inside : classDenote I e x
            · exact .inr inside
            · exact .inl fun y edge => inside (holds x y edge)
          · intro holds x y edge
            exact (holds x).resolve_left fun none => none y edge
  | ObjectPropertyRange p e =>
    cases p with
    | Inverse _ =>
      exact ⟨none,by simp [alc_ontology.axiom_concept],by simp [SupportedAxiom],by simp⟩
    | Property r =>
      obtain ⟨ri⟩ := r
      obtain ⟨inside,insideRead,insideSupport,insideMeaning⟩ := translate.{u,v} e true
      cases inside with
      | none =>
        refine ⟨none,by simp [alc_ontology.axiom_concept,insideRead],?_,by simp⟩
        have absent : ¬ InAlc e := by simpa using insideSupport
        simp [SupportedAxiom,absent]
      | some inside =>
        refine ⟨some (.Forall ⟨ri⟩ inside),by simp [alc_ontology.axiom_concept,insideRead,copy_iri_identity],?_,?_⟩
        · simp [SupportedAxiom,insideSupport.mp rfl]
        · intro concept same Object Value I fixes
          simp only [TBoxPart,Assertion,RoleAxiom,false_or]
          cases same
          simp only [Rowl.Owl.satisfies,Rowl.Owl.objectRelation,conceptDenote,
            insideMeaning inside rfl Object Value I fixes,Polar]
  | AnnotationAssertion _ _ _ | SubAnnotationPropertyOf _ _ | AnnotationPropertyDomain _ _
  | AnnotationPropertyRange _ _ =>
    refine ⟨some .Top,by simp [alc_ontology.axiom_concept],by simp [SupportedAxiom],?_⟩
    intro concept same Object Value I fixes
    simp only [TBoxPart,Assertion,RoleAxiom,false_or]
    cases same
    simp [Rowl.Owl.satisfies,conceptDenote]
  | ClassAssertion _ _ | ObjectPropertyAssertion _ _ _ | NegativeObjectPropertyAssertion _ _ _ =>
    refine ⟨some .Top,by simp [alc_ontology.axiom_concept],by simp [SupportedAxiom],?_⟩
    intro concept same Object Value I fixes
    cases same
    simp [TBoxPart,Assertion,conceptDenote]
  | SubObjectPropertyOf sub sup =>
    cases sub with
    | Single p =>
      cases p with
      | Property r =>
        cases sup with
        | Property q =>
          refine ⟨some .Top,by simp [alc_ontology.axiom_concept],by simp [SupportedAxiom],?_⟩
          intro concept same Object Value I fixes
          cases same
          simp [TBoxPart,RoleAxiom,conceptDenote]
        | Inverse q => exact ⟨none,by simp [alc_ontology.axiom_concept],by simp [SupportedAxiom],by simp⟩
      | Inverse r =>
        cases sup <;> exact ⟨none,by simp [alc_ontology.axiom_concept],by simp [SupportedAxiom],by simp⟩
    | Chain c => exact ⟨none,by simp [alc_ontology.axiom_concept],by simp [SupportedAxiom],by simp⟩
  | EquivalentObjectProperties members =>
    by_cases named : ∀ p ∈ members.elements, ∃ q, p = .Property q
    · have decided : decide (∀ p ∈ members.elements, ∃ q, p = .Property q) = true := decide_eq_true named
      refine ⟨some .Top,by simp only [alc_ontology.axiom_concept,named_members_correct,decided,bind_ok,↓reduceIte],
        by simp only [SupportedAxiom,Option.isSome_some,true_iff]; exact named,?_⟩
      intro concept same Object Value I fixes
      cases same
      simp only [TBoxPart,Assertion,RoleAxiom,false_or,conceptDenote]
      exact iff_of_true (.inl named) (fun _ => trivial)
    · exact ⟨none,by simp [alc_ontology.axiom_concept,named_members_correct,named],by simp [SupportedAxiom,named],
        by simp⟩
  | TransitiveObjectProperty p =>
    cases p with
    | Property r =>
      refine ⟨some .Top,by simp [alc_ontology.axiom_concept],by simp [SupportedAxiom],?_⟩
      intro concept same Object Value I fixes
      cases same
      simp [TBoxPart,RoleAxiom,conceptDenote]
    | Inverse r => exact ⟨none,by simp [alc_ontology.axiom_concept],by simp [SupportedAxiom],by simp⟩
  | _ => exact ⟨none,by simp [alc_ontology.axiom_concept],by simp [SupportedAxiom],by simp⟩

private theorem internalize_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize)
    (joined : nnf.NnfConcept) :
    ∃ result, alc_ontology.internalize_from items index joined = .ok result ∧
      (result.isSome ↔ ∀ a ∈ items.val.drop index.val, SupportedAxiom a.axiom) ∧
      ∀ concept, result = some concept → ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        Fixes I → ((∀ x, conceptDenote I concept x) ↔
          (∀ x, conceptDenote I joined x) ∧ ∀ a ∈ items.val.drop index.val, TBoxPart I a.axiom) := by
  rw [alc_ontology.internalize_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨head,headRead,headSupport,headMeaning⟩ := axiom_concept_correct.{u,v} items.val[index.val].axiom
    cases head with
    | none =>
      refine ⟨none,?_,?_,by intro concept impossible; cases impossible⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,headRead]
      · have absent : ¬ SupportedAxiom items.val[index.val].axiom := by simpa using headSupport
        simp only [Option.isSome_none,Bool.false_eq_true,false_iff]
        intro every
        exact absent (every _ (by rw [split]; exact List.mem_cons_self ..))
    | some next =>
      obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val+1 := by simpa using indexValue
      obtain ⟨result,executed,support,meaning⟩ := internalize_from_correct items index' (.And joined next)
      refine ⟨result,?_,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,headRead,advance,executed]
      · rw [support,nextIndex,split]
        simp only [List.forall_mem_cons,headSupport.mp rfl,true_and]
      · intro concept same Object Value I fixes
        rw [meaning concept same Object Value I fixes,split,nextIndex]
        have axiomMeaning := headMeaning next rfl Object Value I fixes
        simp only [conceptDenote,forall_and,List.forall_mem_cons,axiomMeaning]
        tauto
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some joined,?_,?_,?_⟩
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more]
    · simp [empty]
    · intro concept same Object Value I fixes
      cases same
      simp [empty]
termination_by items.val.length - index.val
decreasing_by omega

/-- The actual internalization terminates on every axiom closure, succeeds
    exactly when every axiom is supported, and its concept holds at every
    element exactly when the interpretation satisfies every axiom of the closure
    that is not an assertion. -/
theorem internalize_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, alc_ontology.internalize items = .ok result ∧
      (result.isSome ↔ ∀ a ∈ items.val, SupportedAxiom a.axiom) ∧
      ∀ axioms, result = some axioms → ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        Fixes I → ((∀ a ∈ items.val, TBoxPart I a.axiom) ↔ ∀ x, conceptDenote I axioms x) := by
  have zero : (0#usize).val = 0 := rfl
  obtain ⟨result,executed,support,meaning⟩ := internalize_from_correct.{u,v} items 0#usize .Top
  refine ⟨result,by rw [alc_ontology.internalize]; exact executed,by simpa [zero] using support,?_⟩
  intro axioms same Object Value I fixes
  rw [meaning axioms same Object Value I fixes]
  simp [conceptDenote,zero]
end Rowl.Internalization
