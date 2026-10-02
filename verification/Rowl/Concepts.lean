import Rowl.Tableau

/-!
Concepts with inverse roles for the completion graph tableau, and their
translation from class expressions, proved against the independent OWL 2 Direct
Semantics. Roles are object property expressions read with `objectRelation`, so
an inverse role relates the pairs of its property in reverse. The translation
keeps the meaning of every supported class expression (or of its complement) in
every interpretation that gives owl:Thing and owl:Nothing their fixed OWL
meaning.
-/
namespace Rowl.Concepts
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation classDenote objectRelation thing nothing)
open Rowl.ClassEquality (IsThing IsNothing ThingBytes NothingBytes is_thing_total_correct is_nothing_total_correct)
open Rowl.Nnf (Polar Fixes Every Gather Quantified copy_iri_identity)
open Rowl.Tableau (property_eq_iff)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v w

variable {Object : Type u} {Value : Type v}

/-- Meaning of a concept in an OWL interpretation; roles are read with
    `objectRelation`, so an inverse role relates its property's pairs reversed. -/
def denote (I : Interpretation Object Value) : concepts.Concept → Object → Prop
  | .Top, _ => True
  | .Bottom, _ => False
  | .Atom c, x => I.classes c x
  | .NotAtom c, x => ¬ I.classes c x
  | .And a b, x => denote I a x ∧ denote I b x
  | .Or a b, x => denote I a x ∨ denote I b x
  | .Exists r c, x => ∃ y, objectRelation I r x y ∧ denote I c y
  | .Forall r c, x => ∀ y, objectRelation I r x y → denote I c y

/-- The inverse of an object property expression. -/
def inv : ObjectPropertyExpression → ObjectPropertyExpression
  | .Property p => .Inverse p
  | .Inverse p => .Property p

theorem inv_inv (r : ObjectPropertyExpression) : inv (inv r) = r := by
  cases r <;> rfl
/-- An inverse role relates exactly the reversed pairs. -/
theorem relation_inv (I : Interpretation Object Value) (r : ObjectPropertyExpression) (x y : Object) :
    objectRelation I (inv r) x y ↔ objectRelation I r y x := by
  cases r <;> rfl

/-- Copying a role reproduces it exactly. -/
theorem copy_role_identity (r : ObjectPropertyExpression) : concepts.copy_role r = .ok r := by
  cases r with
  | Property p => cases p; simp [concepts.copy_role,copy_iri_identity]
  | Inverse p => cases p; simp [concepts.copy_role,copy_iri_identity]
/-- The actual inverse is `inv`. -/
theorem inverse_correct (r : ObjectPropertyExpression) : concepts.inverse r = .ok (inv r) := by
  cases r with
  | Property p => cases p; simp [concepts.inverse,copy_iri_identity,inv]
  | Inverse p => cases p; simp [concepts.inverse,copy_iri_identity,inv]
/-- The actual role comparison decides equality: the same orientation and the
    same exact spelling. -/
theorem same_role_correct (left right : ObjectPropertyExpression) :
    concepts.same_role left right = .ok (decide (left = right)) := by
  cases left with
  | Property a =>
    cases right with
    | Property b =>
      rw [concepts.same_role,Rowl.Symbols.same_spelling_total_correct]
      have same : (ObjectPropertyExpression.Property a = .Property b) ↔ a.iri.spelling.val = b.iri.spelling.val := by
        rw [ObjectPropertyExpression.Property.injEq,property_eq_iff]
      simp only [same]
    | Inverse b => simp [concepts.same_role]
  | Inverse a =>
    cases right with
    | Property b => simp [concepts.same_role]
    | Inverse b =>
      rw [concepts.same_role,Rowl.Symbols.same_spelling_total_correct]
      have same : (ObjectPropertyExpression.Inverse a = .Inverse b) ↔ a.iri.spelling.val = b.iri.spelling.val := by
        rw [ObjectPropertyExpression.Inverse.injEq,property_eq_iff]
      simp only [same]

private theorem listN_mem_size {α : Type} [SizeOf α] {n : Nat}
    (xs : Aeneas.Data.ListN.ListN α n) {x : α} (h : x ∈ xs.toList) : sizeOf x < sizeOf xs := by
  induction xs with
  | nil => simp [Aeneas.Data.ListN.ListN.toList] at h
  | cons head tail ih =>
    simp only [Aeneas.Data.ListN.ListN.toList, List.mem_cons] at h
    rcases h with rfl | h
    · simp +arith
    · have := ih h
      simp only [Data.ListN.ListN.cons.sizeOf_spec]
      omega
private theorem vec_mem_size {α : Type} [SizeOf α] (xs : alloc.vec.Vec α) {x : α} (h : x ∈ xs.val) :
    sizeOf x < sizeOf xs := by
  have := listN_mem_size xs.slice.list h
  cases xs with | mk slice => cases slice; simp_all [alloc.vec.Vec.val, Slice.val]; omega
private theorem first_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.first < sizeOf xs := by
  cases xs; simp +arith
private theorem second_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.second < sizeOf xs := by
  cases xs; simp +arith
private theorem rest_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.rest < sizeOf xs := by
  cases xs; simp +arith
private theorem member_size (xs : AtLeastTwo ClassExpression) (child : ClassExpression)
    (member : child ∈ xs.elements) : sizeOf child < sizeOf xs := by
  simp only [AtLeastTwo.elements, List.mem_cons] at member
  rcases member with rfl | rfl | member
  · exact first_size xs
  · exact second_size xs
  · have := vec_mem_size xs.rest member
    have := rest_size xs
    omega

/-- The supported ALCI fragment: named classes, intersections, unions,
    complements, and existential/universal restrictions on object property
    expressions, named or inverse. -/
def InAlci (expression : ClassExpression) : Prop :=
  match expression with
  | .Class _ => True
  | .ObjectIntersectionOf xs => InAlci xs.first ∧ InAlci xs.second ∧ ∀ e ∈ xs.rest.val, InAlci e
  | .ObjectUnionOf xs => InAlci xs.first ∧ InAlci xs.second ∧ ∀ e ∈ xs.rest.val, InAlci e
  | .ObjectComplementOf e => InAlci e
  | .ObjectSomeValuesFrom _ e => InAlci e
  | .ObjectAllValuesFrom _ e => InAlci e
  | _ => False
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

/-- The concept means the expression (or its complement) in every interpretation
    that fixes owl:Thing and owl:Nothing. -/
def Agrees (expression : ClassExpression) (positive : Bool) (concept : concepts.Concept) : Prop :=
  ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
    ∀ x, denote I concept x ↔ Polar positive (classDenote I expression x)
/-- Independent translation contract: outside the fragment there is no result;
    inside it, the result agrees with the expression under the polarity. -/
def Correct (expression : ClassExpression) (positive : Bool) : Option concepts.Concept → Prop
  | none => ¬ InAlci expression
  | some concept => InAlci expression ∧ Agrees.{u,v} expression positive concept

private theorem thing_identity (c : Class) (top : IsThing (.Class c)) : c = thing := by
  cases c with | mk i => cases i with | mk bytes =>
    have equal : bytes = thing.iri.spelling := by
      simpa only [alloc.vec.Vec.eq_iff] using (by simpa [IsThing,thing,ThingBytes] using top)
    simp [equal]
private theorem nothing_identity (c : Class) (bottom : IsNothing (.Class c)) : c = nothing := by
  cases c with | mk i => cases i with | mk bytes =>
    have equal : bytes = nothing.iri.spelling := by
      simpa only [alloc.vec.Vec.eq_iff] using (by simpa [IsNothing,nothing,NothingBytes] using bottom)
    simp [equal]

private theorem named_correct (c : Class) (positive : Bool) :
    ∃ concept, concepts.named (.Class c) c positive = .ok concept ∧
      ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
        ∀ x, denote I concept x ↔ Polar positive (I.classes c x) := by
  by_cases top : IsThing (.Class c)
  · have same := thing_identity c top
    refine ⟨if positive then .Top else .Bottom,
      by cases positive <;> simp [concepts.named,is_thing_total_correct,top],?_⟩
    intro Object Value I fixes x
    subst same
    have full := fixes.1 x
    cases positive <;> simp [denote,Polar,full]
  · by_cases bottom : IsNothing (.Class c)
    · have same := nothing_identity c bottom
      refine ⟨if positive then .Bottom else .Top,
        by cases positive <;> simp [concepts.named,is_thing_total_correct,is_nothing_total_correct,top,bottom],?_⟩
      intro Object Value I fixes x
      subst same
      have empty := fixes.2 x
      cases positive <;> simp [denote,Polar,empty]
    · have copied := copy_iri_identity c.iri
      refine ⟨if positive then .Atom c else .NotAtom c,?_,?_⟩
      · cases c
        cases positive <;> simp_all [concepts.named,is_thing_total_correct,is_nothing_total_correct]
      · intro Object Value I fixes x
        cases positive <;> simp [denote,Polar]

private theorem join_correct (conjunctive : Bool) (left right : concepts.Concept) :
    concepts.join conjunctive left right = .ok (if conjunctive then .And left right else .Or left right) := by
  cases conjunctive <;> rfl
private theorem join_denote (I : Interpretation Object Value) (conjunctive : Bool) (left right : concepts.Concept)
    (x : Object) :
    denote I (if conjunctive then .And left right else .Or left right) x ↔
      match conjunctive with
      | true => denote I left x ∧ denote I right x
      | false => denote I left x ∨ denote I right x := by
  cases conjunctive <;> rfl

private theorem fold_from_correct (values : alloc.vec.Vec ClassExpression) (positive conjunctive : Bool)
    (child : ∀ e ∈ values.val, ∀ polarity, ∃ result, concepts.translate e polarity = .ok result ∧
      Correct.{u,v} e polarity result)
    (index : Usize) (joined : concepts.Concept) :
    ∃ result, concepts.fold_from values index positive conjunctive joined = .ok result ∧
      (result.isSome ↔ ∀ e ∈ values.val.drop index.val, InAlci e) ∧
      ∀ concept, result = some concept →
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I → ∀ x,
          (denote I concept x ↔ Gather conjunctive (denote I joined x) (values.val.drop index.val)
            (fun e => Polar positive (classDenote I e x))) := by
  rw [concepts.fold_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨head,headRead,headCorrect⟩ := child values.val[index.val] (List.getElem_mem more) positive
    cases head with
    | none =>
      refine ⟨none,?_,?_,by intro concept impossible; cases impossible⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,headRead]
      · rw [split]
        simp only [Option.isSome_none,Bool.false_eq_true,false_iff,List.forall_mem_cons,not_and]
        intro supported
        exact absurd supported headCorrect
    | some next =>
      obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val+1 := by simpa using indexValue
      obtain ⟨result,executed,support,meaning⟩ := fold_from_correct values positive conjunctive child index'
        (if conjunctive then .And joined next else .Or joined next)
      refine ⟨result,?_,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,headRead,advance,join_correct,executed]
      · rw [split,support,nextIndex]
        simp only [List.forall_mem_cons,headCorrect.1,true_and]
      · intro concept same Object Value I fixes x
        rw [meaning concept same Object Value I fixes x,split,join_denote,nextIndex]
        have agrees := headCorrect.2 Object Value I fixes x
        cases conjunctive with
        | true =>
          simp only [Gather,agrees,List.forall_mem_cons]
          tauto
        | false =>
          simp only [Gather,agrees,List.mem_cons,exists_eq_or_imp]
          tauto
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some joined,?_,?_,?_⟩
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more]
    · simp [empty]
    · intro concept same Object Value I fixes x
      cases same
      rw [empty]
      cases conjunctive <;> simp [Gather]
termination_by values.val.length - index.val
decreasing_by omega

private theorem connect_correct (members : AtLeastTwo ClassExpression) (positive conjunctive : Bool)
    (child : ∀ e ∈ members.elements, ∀ polarity, ∃ result, concepts.translate e polarity = .ok result ∧
      Correct.{u,v} e polarity result) :
    ∃ result, concepts.connect members positive conjunctive = .ok result ∧
      (result.isSome ↔ ∀ e ∈ members.elements, InAlci e) ∧
      ∀ concept, result = some concept →
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I → ∀ x,
          (denote I concept x ↔ Every conjunctive members.elements (fun e => Polar positive (classDenote I e x))) := by
  rw [concepts.connect]
  obtain ⟨first,firstRead,firstCorrect⟩ := child members.first (by simp [AtLeastTwo.elements]) positive
  cases first with
  | none =>
    refine ⟨none,by simp only [firstRead,bind_ok],?_,by intro concept impossible; cases impossible⟩
    simp only [Option.isSome_none,Bool.false_eq_true,false_iff,AtLeastTwo.elements,List.forall_mem_cons,not_and]
    intro supported
    exact absurd supported firstCorrect
  | some first =>
    obtain ⟨second,secondRead,secondCorrect⟩ := child members.second (by simp [AtLeastTwo.elements]) positive
    cases second with
    | none =>
      refine ⟨none,by simp only [firstRead,secondRead,bind_ok],?_,by intro concept impossible; cases impossible⟩
      simp only [Option.isSome_none,Bool.false_eq_true,false_iff,AtLeastTwo.elements,List.forall_mem_cons,not_and]
      intro _ supported
      exact absurd supported secondCorrect
    | some second =>
      obtain ⟨result,executed,support,meaning⟩ := fold_from_correct members.rest positive conjunctive
        (fun e mem => child e (by simp only [AtLeastTwo.elements,List.mem_cons]; exact .inr (.inr mem)))
        0#usize (if conjunctive then .And first second else .Or first second)
      refine ⟨result,by simp only [firstRead,secondRead,bind_ok,join_correct,executed],?_,?_⟩
      · rw [support]
        simp [AtLeastTwo.elements,firstCorrect.1,secondCorrect.1,show (0#usize).val = 0 from rfl]
      · intro concept same Object Value I fixes x
        rw [meaning concept same Object Value I fixes x,join_denote]
        have one := firstCorrect.2 Object Value I fixes x
        have two := secondCorrect.2 Object Value I fixes x
        cases conjunctive with
        | true =>
          simp only [Gather,Every,one,two,AtLeastTwo.elements,List.forall_mem_cons,
            show (0#usize).val = 0 from rfl,List.drop_zero]
          tauto
        | false =>
          simp only [Gather,Every,one,two,AtLeastTwo.elements,List.mem_cons,exists_eq_or_imp,
            show (0#usize).val = 0 from rfl,List.drop_zero]
          tauto

private theorem restriction_correct (property : ObjectPropertyExpression) (filler : ClassExpression)
    (positive existential : Bool)
    (child : ∀ polarity, ∃ result, concepts.translate filler polarity = .ok result ∧ Correct.{u,v} filler polarity result) :
    ∃ result, concepts.restriction property filler positive existential = .ok result ∧
      (result.isSome ↔ InAlci filler) ∧
      ∀ concept, result = some concept →
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I → ∀ x,
          (denote I concept x ↔ Quantified existential (objectRelation I property x)
            (fun y => Polar positive (classDenote I filler y))) := by
  obtain ⟨inner,innerRead,innerCorrect⟩ := child positive
  cases inner with
  | none =>
    refine ⟨none,by simp [concepts.restriction,innerRead],?_,by intro concept impossible; cases impossible⟩
    simp only [Option.isSome_none,Bool.false_eq_true,false_iff]
    exact innerCorrect
  | some inner =>
    refine ⟨some (if existential then .Exists property inner else .Forall property inner),?_,?_,?_⟩
    · cases existential <;> simp [concepts.restriction,copy_role_identity,innerRead]
    · simp [innerCorrect.1]
    · intro concept same Object Value I fixes x
      cases same
      have agrees := fun y => innerCorrect.2 Object Value I fixes y
      cases existential <;> simp [denote,Quantified,agrees]

private theorem intersection_every (I : Interpretation Object Value) (xs : AtLeastTwo ClassExpression) (x : Object) :
    Every true xs.elements (fun e => classDenote I e x) ↔ classDenote I (.ObjectIntersectionOf xs) x := by
  simp [Every,classDenote,AtLeastTwo.elements]
private theorem union_every (I : Interpretation Object Value) (xs : AtLeastTwo ClassExpression) (x : Object) :
    Every false xs.elements (fun e => classDenote I e x) ↔ classDenote I (.ObjectUnionOf xs) x := by
  simp [Every,classDenote,AtLeastTwo.elements]
private theorem every_true_not (members : List ClassExpression) (holds : ClassExpression → Prop) :
    Every true members (fun e => ¬ holds e) ↔ ¬ Every false members holds := by
  simp [Every]
private theorem every_false_not (members : List ClassExpression) (holds : ClassExpression → Prop) :
    Every false members (fun e => ¬ holds e) ↔ ¬ Every true members holds := by
  simp [Every]

/-- The actual translation terminates on every class expression; outside the
    ALCI fragment it returns `None`, and inside it the result means exactly the
    expression (positive polarity) or its complement (negative polarity). -/
theorem translate_total_correct (expression : ClassExpression) (positive : Bool) :
    ∃ result, concepts.translate expression positive = .ok result ∧ Correct.{u,v} expression positive result := by
  cases h : expression with
  | Class c =>
    obtain ⟨concept,executed,meaning⟩ := named_correct.{u,v} c positive
    refine ⟨some concept,by rw [concepts.translate]; simp [executed],by simp [InAlci],?_⟩
    intro Object Value I fixes x
    rw [meaning Object Value I fixes x]
    simp [classDenote]
  | ObjectIntersectionOf xs =>
    obtain ⟨result,executed,support,meaning⟩ := connect_correct.{u,v} xs positive positive
      (fun e mem polarity =>
        have := member_size xs e mem
        translate_total_correct e polarity)
    refine ⟨result,by rw [concepts.translate]; exact executed,?_⟩
    have fragment : InAlci (.ObjectIntersectionOf xs) ↔ ∀ e ∈ xs.elements, InAlci e := by
      simp [InAlci,AtLeastTwo.elements]
    cases result with
    | none => simpa [Correct,fragment] using support
    | some concept =>
      refine ⟨fragment.mpr (support.mp rfl),?_⟩
      intro Object Value I fixes x
      rw [meaning concept rfl Object Value I fixes x]
      cases positive with
      | true => exact intersection_every I xs x
      | false =>
        show Every false xs.elements (fun e => ¬ classDenote I e x) ↔ ¬ classDenote I (.ObjectIntersectionOf xs) x
        exact (every_false_not _ _).trans (not_congr (intersection_every I xs x))
  | ObjectUnionOf xs =>
    obtain ⟨result,executed,support,meaning⟩ := connect_correct.{u,v} xs positive (decide ¬ positive = true)
      (fun e mem polarity =>
        have := member_size xs e mem
        translate_total_correct e polarity)
    refine ⟨result,by rw [concepts.translate]; exact executed,?_⟩
    have fragment : InAlci (.ObjectUnionOf xs) ↔ ∀ e ∈ xs.elements, InAlci e := by
      simp [InAlci,AtLeastTwo.elements]
    cases result with
    | none => simpa [Correct,fragment] using support
    | some concept =>
      refine ⟨fragment.mpr (support.mp rfl),?_⟩
      intro Object Value I fixes x
      rw [meaning concept rfl Object Value I fixes x]
      cases positive with
      | true => exact union_every I xs x
      | false =>
        show Every true xs.elements (fun e => ¬ classDenote I e x) ↔ ¬ classDenote I (.ObjectUnionOf xs) x
        exact (every_true_not _ _).trans (not_congr (union_every I xs x))
  | ObjectComplementOf inner =>
    obtain ⟨result,executed,correct⟩ := translate_total_correct inner (decide ¬ positive = true)
    refine ⟨result,by rw [concepts.translate]; exact executed,?_⟩
    cases result with
    | none => simpa [Correct,InAlci] using correct
    | some concept =>
      refine ⟨by simpa [InAlci] using correct.1,?_⟩
      intro Object Value I fixes x
      rw [correct.2 Object Value I fixes x]
      cases positive <;> simp [Polar,classDenote]
  | ObjectSomeValuesFrom property filler =>
    obtain ⟨result,executed,support,meaning⟩ := restriction_correct.{u,v} property filler positive positive
      (fun polarity => translate_total_correct filler polarity)
    refine ⟨result,by rw [concepts.translate]; exact executed,?_⟩
    cases result with
    | none => simpa [Correct,InAlci] using support
    | some concept =>
      refine ⟨by simpa [InAlci] using support,?_⟩
      intro Object Value I fixes x
      rw [meaning concept rfl Object Value I fixes x]
      cases positive <;> simp [Quantified,Polar,classDenote]
  | ObjectAllValuesFrom property filler =>
    obtain ⟨result,executed,support,meaning⟩ := restriction_correct.{u,v} property filler positive
      (decide ¬ positive = true) (fun polarity => translate_total_correct filler polarity)
    refine ⟨result,by rw [concepts.translate]; exact executed,?_⟩
    cases result with
    | none => simpa [Correct,InAlci] using support
    | some concept =>
      refine ⟨by simpa [InAlci] using support,?_⟩
      intro Object Value I fixes x
      rw [meaning concept rfl Object Value I fixes x]
      cases positive <;> simp [Quantified,Polar,classDenote]
  | ObjectOneOf _ | ObjectHasValue _ _ | ObjectHasSelf _ | ObjectMinCardinality _ _ _
  | ObjectMaxCardinality _ _ _ | ObjectExactCardinality _ _ _ | DataSomeValuesFrom _ _
  | DataAllValuesFrom _ _ | DataHasValue _ _ | DataMinCardinality _ _ _ | DataMaxCardinality _ _ _
  | DataExactCardinality _ _ _ =>
    exact ⟨none,by rw [concepts.translate],by simp [Correct,InAlci]⟩
termination_by sizeOf expression
decreasing_by
  all_goals simp only [h,ClassExpression.ObjectIntersectionOf.sizeOf_spec,ClassExpression.ObjectUnionOf.sizeOf_spec,
    ClassExpression.ObjectComplementOf.sizeOf_spec,ClassExpression.ObjectSomeValuesFrom.sizeOf_spec,
    ClassExpression.ObjectAllValuesFrom.sizeOf_spec]
  all_goals omega

/-- The translation succeeds exactly on the ALCI fragment. -/
theorem translate_supported_iff (expression : ClassExpression) (positive : Bool) :
    (∃ concept, concepts.translate expression positive = .ok (some concept)) ↔ InAlci expression := by
  obtain ⟨result,executed,correct⟩ := translate_total_correct.{0,0} expression positive
  rw [executed]
  cases result with
  | none => simpa [Correct] using correct
  | some concept => exact ⟨fun _ => correct.1,fun _ => ⟨concept,rfl⟩⟩

/-- A translated concept means exactly the expression (positive polarity) or its
    complement (negative polarity) in every interpretation fixing owl:Thing and
    owl:Nothing, hence in every OWL interpretation. -/
theorem translate_meaning (expression : ClassExpression) (positive : Bool) (concept : concepts.Concept)
    (translated : concepts.translate expression positive = .ok (some concept)) (I : Interpretation Object Value)
    (fixes : Fixes I) (x : Object) :
    denote I concept x ↔ Polar positive (classDenote I expression x) := by
  obtain ⟨result,executed,correct⟩ := translate_total_correct.{u,v} expression positive
  rw [translated] at executed
  cases Result.ok_injective executed
  exact correct.2 Object Value I fixes x
end Rowl.Concepts
