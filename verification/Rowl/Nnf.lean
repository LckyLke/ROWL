import Rowl.ClassEquality

/-!
Negation normal form for the tableau's ALC fragment, proved against the
independent OWL 2 Direct Semantics. The translation keeps the meaning of every
supported class expression (or of its complement) in every interpretation that
gives owl:Thing and owl:Nothing their fixed OWL meaning.
-/
namespace Rowl.Nnf
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation classDenote objectRelation thing nothing)
open Rowl.ClassEquality (IsThing IsNothing ThingBytes NothingBytes is_thing_total_correct is_nothing_total_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v w

variable {Object : Type u} {Value : Type v}

/-- Meaning of an NNF concept in an OWL interpretation. -/
def conceptDenote (I : Interpretation Object Value) : nnf.NnfConcept → Object → Prop
  | .Top, _ => True
  | .Bottom, _ => False
  | .Atom c, x => I.classes c x
  | .NotAtom c, x => ¬ I.classes c x
  | .And a b, x => conceptDenote I a x ∧ conceptDenote I b x
  | .Or a b, x => conceptDenote I a x ∨ conceptDenote I b x
  | .Exists p c, x => ∃ y, I.objectProperties p x y ∧ conceptDenote I c y
  | .Forall p c, x => ∀ y, I.objectProperties p x y → conceptDenote I c y

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

/-- The supported ALC fragment: named classes, intersections, unions,
    complements, and existential/universal restrictions on named properties. -/
def InAlc (expression : ClassExpression) : Prop :=
  match expression with
  | .Class _ => True
  | .ObjectIntersectionOf xs => InAlc xs.first ∧ InAlc xs.second ∧ ∀ e ∈ xs.rest.val, InAlc e
  | .ObjectUnionOf xs => InAlc xs.first ∧ InAlc xs.second ∧ ∀ e ∈ xs.rest.val, InAlc e
  | .ObjectComplementOf e => InAlc e
  | .ObjectSomeValuesFrom p e => (∃ q, p = .Property q) ∧ InAlc e
  | .ObjectAllValuesFrom p e => (∃ q, p = .Property q) ∧ InAlc e
  | _ => False
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

/-- A proposition (`positive`) or its negation (`!positive`). -/
def Polar (positive : Bool) (p : Prop) : Prop :=
  match positive with
  | true => p
  | false => ¬ p
/-- OWL fixes owl:Thing as the whole object domain and owl:Nothing as empty;
    every OWL interpretation satisfies this. -/
def Fixes (I : Interpretation Object Value) : Prop :=
  (∀ x, I.classes thing x) ∧ (∀ x, ¬ I.classes nothing x)
/-- The concept means the expression (or its complement) in every interpretation
    that fixes owl:Thing and owl:Nothing. -/
def Agrees (expression : ClassExpression) (positive : Bool) (concept : nnf.NnfConcept) : Prop :=
  ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
    ∀ x, conceptDenote I concept x ↔ Polar positive (classDenote I expression x)
/-- Independent translation contract: outside the fragment there is no result;
    inside it, the result agrees with the expression under the polarity. -/
def Correct (expression : ClassExpression) (positive : Bool) : Option nnf.NnfConcept → Prop
  | none => ¬ InAlc expression
  | some concept => InAlc expression ∧ Agrees.{u,v} expression positive concept
/-- One connective over member conditions: all of them, or at least one. -/
def Every (conjunctive : Bool) (members : List ClassExpression) (holds : ClassExpression → Prop) : Prop :=
  match conjunctive with
  | true => ∀ e ∈ members, holds e
  | false => ∃ e ∈ members, holds e

/-- Every OWL interpretation fixes owl:Thing and owl:Nothing. -/
theorem fixes_of_interpretation {Native : Type w} {D : Rowl.Owl.DatatypeMap Native}
    {embed : Rowl.Owl.ValueEmbedding D Value} {V : Rowl.Owl.Vocabulary} {I : Interpretation Object Value}
    (valid : Rowl.Owl.IsInterpretation D embed V I) : Fixes I :=
  ⟨valid.1,valid.2.1⟩

private theorem copy_from_correct (source : alloc.vec.Vec U8) (index : Usize) (target : alloc.vec.Vec U8)
    (copied : target.val = source.val.take index.val) (inside : index.val ≤ source.val.length) :
    nnf.copy_from source index target = .ok source := by
  rw [nnf.copy_from]
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
theorem copy_bytes_identity (bytes : alloc.vec.Vec U8) : nnf.copy_bytes bytes = .ok bytes := by
  rw [nnf.copy_bytes]
  exact copy_from_correct bytes 0#usize (alloc.vec.Vec.new U8) (by simp) (by simp)
/-- Copying an IRI reproduces it exactly. -/
theorem copy_iri_identity (iri : Iri) : nnf.copy_iri iri = .ok iri := by
  cases iri with
  | mk spelling => simp [nnf.copy_iri,copy_bytes_identity]

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
    ∃ concept, nnf.named (.Class c) c positive = .ok concept ∧
      ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I →
        ∀ x, conceptDenote I concept x ↔ Polar positive (I.classes c x) := by
  by_cases top : IsThing (.Class c)
  · have same := thing_identity c top
    refine ⟨if positive then .Top else .Bottom,
      by cases positive <;> simp [nnf.named,is_thing_total_correct,top],?_⟩
    intro Object Value I fixes x
    subst same
    have full := fixes.1 x
    cases positive <;> simp [conceptDenote,Polar,full]
  · by_cases bottom : IsNothing (.Class c)
    · have same := nothing_identity c bottom
      refine ⟨if positive then .Bottom else .Top,
        by cases positive <;> simp [nnf.named,is_thing_total_correct,is_nothing_total_correct,top,bottom],?_⟩
      intro Object Value I fixes x
      subst same
      have empty := fixes.2 x
      cases positive <;> simp [conceptDenote,Polar,empty]
    · have copied := copy_iri_identity c.iri
      refine ⟨if positive then .Atom c else .NotAtom c,?_,?_⟩
      · cases c
        cases positive <;> simp_all [nnf.named,is_thing_total_correct,is_nothing_total_correct]
      · intro Object Value I fixes x
        cases positive <;> simp [conceptDenote,Polar]

private theorem join_correct (conjunctive : Bool) (left right : nnf.NnfConcept) :
    nnf.join conjunctive left right = .ok (if conjunctive then .And left right else .Or left right) := by
  cases conjunctive <;> rfl
private theorem join_denote (I : Interpretation Object Value) (conjunctive : Bool) (left right : nnf.NnfConcept)
    (x : Object) :
    conceptDenote I (if conjunctive then .And left right else .Or left right) x ↔
      match conjunctive with
      | true => conceptDenote I left x ∧ conceptDenote I right x
      | false => conceptDenote I left x ∨ conceptDenote I right x := by
  cases conjunctive <;> rfl

/-- One connective applied to a base condition and every remaining member. -/
def Gather (conjunctive : Bool) (base : Prop) (members : List ClassExpression)
    (holds : ClassExpression → Prop) : Prop :=
  match conjunctive with
  | true => base ∧ ∀ e ∈ members, holds e
  | false => base ∨ ∃ e ∈ members, holds e

private theorem fold_from_correct (values : alloc.vec.Vec ClassExpression) (positive conjunctive : Bool)
    (child : ∀ e ∈ values.val, ∀ polarity, ∃ result, nnf.nnf e polarity = .ok result ∧
      Correct.{u,v} e polarity result)
    (index : Usize) (joined : nnf.NnfConcept) :
    ∃ result, nnf.fold_from values index positive conjunctive joined = .ok result ∧
      (result.isSome ↔ ∀ e ∈ values.val.drop index.val, InAlc e) ∧
      ∀ concept, result = some concept →
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I → ∀ x,
          (conceptDenote I concept x ↔ Gather conjunctive (conceptDenote I joined x) (values.val.drop index.val)
            (fun e => Polar positive (classDenote I e x))) := by
  rw [nnf.fold_from]
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

/-- Joining the translations of all members with one connective means the
    connective applied to the members' polarities. -/
theorem connect_correct (members : AtLeastTwo ClassExpression) (positive conjunctive : Bool)
    (child : ∀ e ∈ members.elements, ∀ polarity, ∃ result, nnf.nnf e polarity = .ok result ∧
      Correct.{u,v} e polarity result) :
    ∃ result, nnf.connect members positive conjunctive = .ok result ∧
      (result.isSome ↔ ∀ e ∈ members.elements, InAlc e) ∧
      ∀ concept, result = some concept →
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I → ∀ x,
          (conceptDenote I concept x ↔ Every conjunctive members.elements (fun e => Polar positive (classDenote I e x))) := by
  rw [nnf.connect]
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

/-- One quantifier over the role successors: some, or all. -/
def Quantified (existential : Bool) (related holds : Object → Prop) : Prop :=
  match existential with
  | true => ∃ y, related y ∧ holds y
  | false => ∀ y, related y → holds y

private theorem restriction_correct (property : ObjectPropertyExpression) (filler : ClassExpression)
    (positive existential : Bool)
    (child : ∀ polarity, ∃ result, nnf.nnf filler polarity = .ok result ∧ Correct.{u,v} filler polarity result) :
    ∃ result, nnf.restriction property filler positive existential = .ok result ∧
      (result.isSome ↔ (∃ q, property = .Property q) ∧ InAlc filler) ∧
      ∀ concept, result = some concept →
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I → ∀ x,
          (conceptDenote I concept x ↔ Quantified existential (objectRelation I property x)
            (fun y => Polar positive (classDenote I filler y))) := by
  cases property with
  | Inverse p =>
    refine ⟨none,by rw [nnf.restriction],by simp,by intro concept impossible; cases impossible⟩
  | Property p =>
    obtain ⟨inner,innerRead,innerCorrect⟩ := child positive
    cases inner with
    | none =>
      refine ⟨none,by simp [nnf.restriction,copy_iri_identity,innerRead],?_,by intro concept impossible; cases impossible⟩
      simp only [Option.isSome_none,Bool.false_eq_true,false_iff,not_and]
      intro _
      exact innerCorrect
    | some inner =>
      refine ⟨some (if existential then .Exists p inner else .Forall p inner),?_,?_,?_⟩
      · cases p
        cases existential <;> simp [nnf.restriction,copy_iri_identity,innerRead]
      · simp [innerCorrect.1]
      · intro concept same Object Value I fixes x
        cases same
        have agrees := fun y => innerCorrect.2 Object Value I fixes y
        cases existential <;> simp [conceptDenote,Quantified,objectRelation,agrees]

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
    ALC fragment it returns `None`, and inside it the result means exactly the
    expression (positive polarity) or its complement (negative polarity). -/
theorem nnf_total_correct (expression : ClassExpression) (positive : Bool) :
    ∃ result, nnf.nnf expression positive = .ok result ∧ Correct.{u,v} expression positive result := by
  cases h : expression with
  | Class c =>
    obtain ⟨concept,executed,meaning⟩ := named_correct.{u,v} c positive
    refine ⟨some concept,by rw [nnf.nnf]; simp [executed],by simp [InAlc],?_⟩
    intro Object Value I fixes x
    rw [meaning Object Value I fixes x]
    simp [classDenote]
  | ObjectIntersectionOf xs =>
    obtain ⟨result,executed,support,meaning⟩ := connect_correct.{u,v} xs positive positive
      (fun e mem polarity =>
        have := member_size xs e mem
        nnf_total_correct e polarity)
    refine ⟨result,by rw [nnf.nnf]; exact executed,?_⟩
    have fragment : InAlc (.ObjectIntersectionOf xs) ↔ ∀ e ∈ xs.elements, InAlc e := by
      simp [InAlc,AtLeastTwo.elements]
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
        nnf_total_correct e polarity)
    refine ⟨result,by rw [nnf.nnf]; exact executed,?_⟩
    have fragment : InAlc (.ObjectUnionOf xs) ↔ ∀ e ∈ xs.elements, InAlc e := by
      simp [InAlc,AtLeastTwo.elements]
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
    obtain ⟨result,executed,correct⟩ := nnf_total_correct inner (decide ¬ positive = true)
    refine ⟨result,by rw [nnf.nnf]; exact executed,?_⟩
    cases result with
    | none => simpa [Correct,InAlc] using correct
    | some concept =>
      refine ⟨by simpa [InAlc] using correct.1,?_⟩
      intro Object Value I fixes x
      rw [correct.2 Object Value I fixes x]
      cases positive <;> simp [Polar,classDenote]
  | ObjectSomeValuesFrom property filler =>
    obtain ⟨result,executed,support,meaning⟩ := restriction_correct.{u,v} property filler positive positive
      (fun polarity => nnf_total_correct filler polarity)
    refine ⟨result,by rw [nnf.nnf]; exact executed,?_⟩
    cases result with
    | none => simpa [Correct,InAlc] using support
    | some concept =>
      refine ⟨by simpa [InAlc] using support,?_⟩
      intro Object Value I fixes x
      rw [meaning concept rfl Object Value I fixes x]
      cases positive <;> simp [Quantified,Polar,classDenote]
  | ObjectAllValuesFrom property filler =>
    obtain ⟨result,executed,support,meaning⟩ := restriction_correct.{u,v} property filler positive
      (decide ¬ positive = true) (fun polarity => nnf_total_correct filler polarity)
    refine ⟨result,by rw [nnf.nnf]; exact executed,?_⟩
    cases result with
    | none => simpa [Correct,InAlc] using support
    | some concept =>
      refine ⟨by simpa [InAlc] using support,?_⟩
      intro Object Value I fixes x
      rw [meaning concept rfl Object Value I fixes x]
      cases positive <;> simp [Quantified,Polar,classDenote]
  | ObjectOneOf _ | ObjectHasValue _ _ | ObjectHasSelf _ | ObjectMinCardinality _ _ _
  | ObjectMaxCardinality _ _ _ | ObjectExactCardinality _ _ _ | DataSomeValuesFrom _ _
  | DataAllValuesFrom _ _ | DataHasValue _ _ | DataMinCardinality _ _ _ | DataMaxCardinality _ _ _
  | DataExactCardinality _ _ _ =>
    exact ⟨none,by rw [nnf.nnf],by simp [Correct,InAlc]⟩
termination_by sizeOf expression
decreasing_by
  all_goals simp only [h,ClassExpression.ObjectIntersectionOf.sizeOf_spec,ClassExpression.ObjectUnionOf.sizeOf_spec,
    ClassExpression.ObjectComplementOf.sizeOf_spec,ClassExpression.ObjectSomeValuesFrom.sizeOf_spec,
    ClassExpression.ObjectAllValuesFrom.sizeOf_spec]
  all_goals omega

/-- The translation succeeds exactly on the ALC fragment. -/
theorem nnf_supported_iff (expression : ClassExpression) (positive : Bool) :
    (∃ concept, nnf.nnf expression positive = .ok (some concept)) ↔ InAlc expression := by
  obtain ⟨result,executed,correct⟩ := nnf_total_correct.{0,0} expression positive
  rw [executed]
  cases result with
  | none => simpa [Correct] using correct
  | some concept => exact ⟨fun _ => correct.1,fun _ => ⟨concept,rfl⟩⟩

/-- A translated concept means exactly the expression (positive polarity) or its
    complement (negative polarity) in every interpretation fixing owl:Thing and
    owl:Nothing, hence in every OWL interpretation. -/
theorem nnf_meaning (expression : ClassExpression) (positive : Bool) (concept : nnf.NnfConcept)
    (translated : nnf.nnf expression positive = .ok (some concept)) (I : Interpretation Object Value)
    (fixes : Fixes I) (x : Object) :
    conceptDenote I concept x ↔ Polar positive (classDenote I expression x) := by
  obtain ⟨result,executed,correct⟩ := nnf_total_correct.{u,v} expression positive
  rw [translated] at executed
  cases Result.ok_injective executed
  exact correct.2 Object Value I fixes x

/-- A translated concept has an instance exactly when the expression does, so
    concept satisfiability decides OWL class satisfiability for the fragment. -/
theorem nnf_instances (expression : ClassExpression) (concept : nnf.NnfConcept)
    (translated : nnf.nnf expression true = .ok (some concept)) (I : Interpretation Object Value)
    (fixes : Fixes I) : (∃ x, conceptDenote I concept x) ↔ ∃ x, classDenote I expression x := by
  constructor
  · rintro ⟨x,holds⟩
    exact ⟨x,(nnf_meaning expression true concept translated I fixes x).mp holds⟩
  · rintro ⟨x,holds⟩
    exact ⟨x,(nnf_meaning expression true concept translated I fixes x).mpr holds⟩
end Rowl.Nnf
