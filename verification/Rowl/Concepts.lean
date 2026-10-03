import Rowl.Tableau

/-!
Concepts with inverse roles, nominals and cardinality restrictions for the
tableaux, and their translation from class expressions, proved against the
independent OWL 2 Direct Semantics. Roles are object property expressions read
with `objectRelation`, so an inverse role relates the pairs of its property in
reverse, a nominal `{a}` holds exactly at the individual, and cardinality
restrictions count with the OWL definitions `AtLeast` and `AtMost`. The
translation keeps the meaning of every supported class expression (or of its
complement) in every interpretation that gives owl:Thing and owl:Nothing their
fixed OWL meaning, and `negate` builds the complement of a concept.
-/
namespace Rowl.Concepts
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation classDenote objectRelation thing nothing AtLeast AtMost)
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
  | .One a, x => Rowl.Owl.individual I a = x
  | .NotOne a, x => Rowl.Owl.individual I a ≠ x
  | .And a b, x => denote I a x ∧ denote I b x
  | .Or a b, x => denote I a x ∨ denote I b x
  | .Exists r c, x => ∃ y, objectRelation I r x y ∧ denote I c y
  | .Forall r c, x => ∀ y, objectRelation I r x y → denote I c y
  | .AtLeast n r c, x => AtLeast n.val (fun y => objectRelation I r x y ∧ denote I c y)
  | .AtMost n r c, x => AtMost n.val (fun y => objectRelation I r x y ∧ denote I c y)

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

/-- Copying an individual reproduces it exactly. -/
theorem copy_individual_identity (a : Individual) : concepts.copy_individual a = .ok a := by
  cases a with
  | Named named => cases named; simp [concepts.copy_individual,copy_iri_identity]
  | Anonymous anonymous => cases anonymous; simp [concepts.copy_individual,Rowl.Nnf.copy_bytes_identity]

/-- Copying a concept reproduces it exactly. -/
theorem copy_concept_identity (c : concepts.Concept) : concepts.copy_concept c = .ok c := by
  induction c with
  | Top | Bottom => rw [concepts.copy_concept]
  | Atom k | NotAtom k => cases k; rw [concepts.copy_concept]; simp [copy_iri_identity]
  | One a | NotOne a => rw [concepts.copy_concept]; simp [copy_individual_identity]
  | And a b ihA ihB | Or a b ihA ihB => rw [concepts.copy_concept]; simp [ihA,ihB]
  | Exists r c ih | Forall r c ih | AtLeast n r c ih | AtMost n r c ih =>
    rw [concepts.copy_concept]; simp [copy_role_identity,ih]

/-- Zero neighbours always exist. -/
theorem atLeast_zero {α : Type u} (P : α → Prop) : AtLeast 0 P :=
  ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0⟩

/-- The count only depends on what the property says. -/
theorem atLeast_congr {α : Type u} (n : Nat) {P Q : α → Prop} (same : ∀ y, P y ↔ Q y) :
    AtLeast n P ↔ AtLeast n Q := by
  rw [show P = Q from funext (fun y => propext (same y))]

/-- The actual complement terminates; a result means exactly the complement of
    the concept in every interpretation. No result means that a maximum
    restriction has the bound `usize::MAX`. -/
theorem negate_correct (c : concepts.Concept) :
    ∃ r, concepts.negate c = .ok r ∧ ∀ c', r = some c' →
      ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) x,
        denote I c' x ↔ ¬ denote I c x := by
  induction c with
  | Top => exact ⟨some .Bottom,by rw [concepts.negate],by intro c' same; cases same; simp [denote]⟩
  | Bottom => exact ⟨some .Top,by rw [concepts.negate],by intro c' same; cases same; simp [denote]⟩
  | Atom k =>
    exact ⟨some (.NotAtom k),by rw [concepts.negate]; cases k; simp [copy_iri_identity],
      by intro c' same; cases same; simp [denote]⟩
  | NotAtom k =>
    exact ⟨some (.Atom k),by rw [concepts.negate]; cases k; simp [copy_iri_identity],
      by intro c' same; cases same; simp [denote]⟩
  | One a =>
    exact ⟨some (.NotOne a),by rw [concepts.negate]; simp [copy_individual_identity],
      by intro c' same; cases same; simp [denote]⟩
  | NotOne a =>
    exact ⟨some (.One a),by rw [concepts.negate]; simp [copy_individual_identity],
      by intro c' same; cases same; simp [denote]⟩
  | And a b ihA ihB | Or a b ihA ihB =>
    obtain ⟨ra,runA,meanA⟩ := ihA
    obtain ⟨rb,runB,meanB⟩ := ihB
    cases ra with
    | none => exact ⟨none,by rw [concepts.negate,concepts.negate_pair]; simp [runA],by simp⟩
    | some a' =>
      cases rb with
      | none => exact ⟨none,by rw [concepts.negate,concepts.negate_pair]; simp [runA,runB],by simp⟩
      | some b' =>
        first
        | exact ⟨some (.Or a' b'),by rw [concepts.negate,concepts.negate_pair]; simp [runA,runB,concepts.join],
            by
              intro c' same Object Value I x
              cases same
              simp only [denote,meanA a' rfl Object Value I x,meanB b' rfl Object Value I x]
              tauto⟩
        | exact ⟨some (.And a' b'),by rw [concepts.negate,concepts.negate_pair]; simp [runA,runB,concepts.join],
            by
              intro c' same Object Value I x
              cases same
              simp only [denote,meanA a' rfl Object Value I x,meanB b' rfl Object Value I x]
              tauto⟩
  | Exists r c ih =>
    obtain ⟨rc,runC,meanC⟩ := ih
    cases rc with
    | none => exact ⟨none,by rw [concepts.negate]; simp [runC],by simp⟩
    | some c' =>
      refine ⟨some (.Forall r c'),by rw [concepts.negate]; simp [runC,copy_role_identity],?_⟩
      intro d same Object Value I x
      cases same
      simp only [denote,meanC c' rfl Object Value I]
      constructor
      · rintro all ⟨y,related,holds⟩
        exact all y related holds
      · intro none y related holds
        exact none ⟨y,related,holds⟩
  | Forall r c ih =>
    obtain ⟨rc,runC,meanC⟩ := ih
    cases rc with
    | none => exact ⟨none,by rw [concepts.negate]; simp [runC],by simp⟩
    | some c' =>
      refine ⟨some (.Exists r c'),by rw [concepts.negate]; simp [runC,copy_role_identity],?_⟩
      intro d same Object Value I x
      cases same
      simp only [denote,meanC c' rfl Object Value I]
      constructor
      · rintro ⟨y,related,fails⟩ all
        exact fails (all y related)
      · intro notAll
        by_contra none
        apply notAll
        intro y related
        by_contra fails
        exact none ⟨y,related,fails⟩
  | AtLeast n r c _ =>
    by_cases zero : n = 0#usize
    · refine ⟨some .Bottom,by rw [concepts.negate]; simp [zero],?_⟩
      intro d same Object Value I x
      cases same
      subst zero
      have value : (0#usize).val = 0 := rfl
      simp only [denote,value,false_iff,not_not]
      exact atLeast_zero _
    · have positive : 0 < n.val := by
        have : n.val ≠ 0 := fun same => zero (UScalar.eq_of_val_eq (by simpa using same))
        omega
      obtain ⟨m,lower,lowerValue⟩ := WP.spec_imp_exists (Usize.sub_spec (x := n) (y := 1#usize) (by scalar_tac))
      refine ⟨some (.AtMost m r c),by rw [concepts.negate]; simp [zero,lower,copy_role_identity,
        copy_concept_identity],?_⟩
      intro d same Object Value I x
      cases same
      have succ : m.val + 1 = n.val := by simp at lowerValue; omega
      simp only [denote,AtMost,succ]
  | AtMost n r c _ =>
    by_cases room : n.val < Usize.max
    · obtain ⟨m,higher,higherValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := n) (y := 1#usize) (by scalar_tac))
      have less : n < core.num.Usize.MAX := by
        rw [UScalar.lt_equiv]; simpa [core.num.Usize.MAX] using room
      refine ⟨some (.AtLeast m r c),by rw [concepts.negate]; simp [less,higher,copy_role_identity,
        copy_concept_identity],?_⟩
      intro d same Object Value I x
      cases same
      have succ : m.val = n.val + 1 := by simpa using higherValue
      simp only [denote,AtMost,succ,not_not]
    · have notLess : ¬ n < core.num.Usize.MAX := by
        rw [UScalar.lt_equiv]; simpa [core.num.Usize.MAX] using room
      exact ⟨none,by rw [concepts.negate]; simp [notLess],by simp⟩

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

/-- The supported ALCIQO fragment: named classes, intersections, unions,
    complements, enumerations of individuals, existential/universal
    restrictions, individual value restrictions, and minimum, maximum and exact
    cardinality restrictions with cardinalities below `usize::MAX`, on object
    property expressions, named or inverse. -/
def Translatable (expression : ClassExpression) : Prop :=
  match expression with
  | .Class _ => True
  | .ObjectIntersectionOf xs => Translatable xs.first ∧ Translatable xs.second ∧ ∀ e ∈ xs.rest.val, Translatable e
  | .ObjectUnionOf xs => Translatable xs.first ∧ Translatable xs.second ∧ ∀ e ∈ xs.rest.val, Translatable e
  | .ObjectComplementOf e => Translatable e
  | .ObjectOneOf _ => True
  | .ObjectHasValue _ _ => True
  | .ObjectSomeValuesFrom _ e => Translatable e
  | .ObjectAllValuesFrom _ e => Translatable e
  | .ObjectMinCardinality n _ none | .ObjectMaxCardinality n _ none | .ObjectExactCardinality n _ none =>
    Rowl.Probes.naturalValue n < Usize.max
  | .ObjectMinCardinality n _ (some e) | .ObjectMaxCardinality n _ (some e)
  | .ObjectExactCardinality n _ (some e) => Rowl.Probes.naturalValue n < Usize.max ∧ Translatable e
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
  | none => ¬ Translatable expression
  | some concept => Translatable expression ∧ Agrees.{u,v} expression positive concept

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
      (result.isSome ↔ ∀ e ∈ values.val.drop index.val, Translatable e) ∧
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
      (result.isSome ↔ ∀ e ∈ members.elements, Translatable e) ∧
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
      (result.isSome ↔ Translatable filler) ∧
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

private theorem nominal_correct (a : Individual) (positive : Bool) :
    concepts.nominal a positive = .ok (if positive then .One a else .NotOne a) := by
  cases positive <;> simp [concepts.nominal,copy_individual_identity]
private theorem nominal_denote (I : Interpretation Object Value) (a : Individual) (positive : Bool) (x : Object) :
    denote I (if positive then .One a else .NotOne a) x ↔ Polar positive (Rowl.Owl.individual I a = x) := by
  cases positive <;> simp [denote,Polar]

/-- The nominals of the remaining individuals joined onto `joined`: a union, or
    the intersection of their complements. -/
private theorem nominals_from_correct (values : alloc.vec.Vec Individual) (positive : Bool) (index : Usize)
    (joined : concepts.Concept) :
    ∃ concept, concepts.nominals_from values index positive joined = .ok concept ∧
      ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) x,
        (denote I concept x ↔ match positive with
          | true => denote I joined x ∨ ∃ a ∈ values.val.drop index.val, Rowl.Owl.individual I a = x
          | false => denote I joined x ∧ ∀ a ∈ values.val.drop index.val, Rowl.Owl.individual I a ≠ x) := by
  rw [concepts.nominals_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    let next : concepts.Concept := if positive then .One values.val[index.val] else .NotOne values.val[index.val]
    obtain ⟨concept,executed,meaning⟩ := nominals_from_correct values positive index'
      (if decide ¬ positive = true then .And joined next else .Or joined next)
    refine ⟨concept,?_,?_⟩
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,nominal_correct,advance,join_correct]
      exact executed
    · intro Object Value I x
      rw [meaning Object Value I x,nextIndex,split]
      cases positive with
      | true =>
        simp only [next,decide_not,decide_true,decide_false,Bool.not_true,Bool.not_false,Bool.false_eq_true,
          ↓reduceIte,denote,List.mem_cons,exists_eq_or_imp]
        tauto
      | false =>
        simp only [next,decide_not,decide_true,decide_false,Bool.not_true,Bool.not_false,Bool.false_eq_true,
          ↓reduceIte,denote,List.forall_mem_cons]
        tauto
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨joined,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro Object Value I x
    rw [empty]
    cases positive <;> simp
termination_by values.val.length - index.val
decreasing_by omega

/-- An enumeration means that the element is one of its individuals. -/
private theorem one_of_correct (members : NonEmpty Individual) (positive : Bool) :
    ∃ concept, concepts.one_of members positive = .ok concept ∧
      ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) x,
        (denote I concept x ↔ Polar positive (classDenote I (.ObjectOneOf members) x)) := by
  obtain ⟨concept,executed,meaning⟩ := nominals_from_correct.{u,v} members.rest positive 0#usize
    (if positive then .One members.first else .NotOne members.first)
  refine ⟨concept,by rw [concepts.one_of]; simp only [nominal_correct,bind_ok]; exact executed,?_⟩
  intro Object Value I x
  rw [meaning Object Value I x]
  have zero : (0#usize).val = 0 := rfl
  rw [zero,List.drop_zero]
  cases positive with
  | true =>
    simp only [↓reduceIte,denote,Polar,classDenote,NonEmpty.elements,List.mem_cons,exists_eq_or_imp]
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,denote,Polar,classDenote,NonEmpty.elements,List.mem_cons,
      exists_eq_or_imp,not_or,not_exists,not_and]

/-- A value restriction means that the element is related to the individual. -/
private theorem has_value_correct (property : ObjectPropertyExpression) (value : Individual) (positive : Bool) :
    ∃ concept, concepts.has_value property value positive = .ok concept ∧
      ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) x,
        (denote I concept x ↔ Polar positive (classDenote I (.ObjectHasValue property value) x)) := by
  refine ⟨if positive then .Exists property (.One value) else .Forall property (.NotOne value),?_,?_⟩
  · cases positive <;> simp [concepts.has_value,nominal_correct,copy_role_identity]
  · intro Object Value I x
    cases positive with
    | true =>
      simp only [↓reduceIte,denote,Polar,classDenote]
      constructor
      · rintro ⟨y,related,same⟩
        rw [same]
        exact related
      · intro related
        exact ⟨_,related,rfl⟩
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte,denote,Polar,classDenote]
      constructor
      · intro every related
        exact every _ related rfl
      · intro unrelated y related same
        rw [← same] at related
        exact unrelated related

private theorem bound_correct (n : probes.Natural) :
    ∃ r, concepts.bound n = .ok r ∧ (r.isSome ↔ Rowl.Probes.naturalValue n < Usize.max) ∧
      ∀ k, r = some k → k.val = Rowl.Probes.naturalValue n := by
  induction n with
  | Zero =>
    refine ⟨some 0#usize,by rw [concepts.bound],?_,?_⟩
    · simp [Rowl.Probes.naturalValue]; scalar_tac
    · intro k same; cases same; rfl
  | Succ m ih =>
    obtain ⟨r,run,support,value⟩ := ih
    obtain ⟨d,limit,dValue⟩ := WP.spec_imp_exists (Usize.sub_spec (x := core.num.Usize.MAX) (y := 1#usize)
      (by simp [core.num.Usize.MAX]; scalar_tac))
    have dIs : d.val = Usize.max - 1 := by simp [core.num.Usize.MAX] at dValue; omega
    cases r with
    | none =>
      refine ⟨none,by rw [concepts.bound]; simp [run],?_,by simp⟩
      simp only [Option.isSome_none,Bool.false_eq_true,false_iff,Rowl.Probes.naturalValue,not_lt]
      have := support.not.mp (by simp)
      omega
    | some v =>
      have vValue := value v rfl
      by_cases fits : v.val < Usize.max - 1
      · obtain ⟨w,add,wValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := v) (y := 1#usize) (by scalar_tac))
        have less : v.val < d.val := by omega
        refine ⟨some w,by rw [concepts.bound]; simp [run,limit,less,add],?_,?_⟩
        · simp [Rowl.Probes.naturalValue]; omega
        · intro k same; cases same; simp [Rowl.Probes.naturalValue] at wValue ⊢; omega
      · have notLess : ¬ v.val < d.val := by omega
        refine ⟨none,by rw [concepts.bound]; simp [run,limit,notLess],?_,by simp⟩
        simp [Rowl.Probes.naturalValue]; omega

/-- An element satisfies the filler of a cardinality restriction: any element
    when there is none. -/
def FillerHolds (I : Interpretation Object Value) (filler : Option ClassExpression) (y : Object) : Prop :=
  match filler with
  | none => True
  | some c => classDenote I c y

/-- What a cardinality restriction counts: neighbours along the property that
    satisfy the filler. -/
def Counted (I : Interpretation Object Value) (property : ObjectPropertyExpression)
    (filler : Option ClassExpression) (x y : Object) : Prop :=
  objectRelation I property x y ∧ FillerHolds I filler y

private theorem counted_none (I : Interpretation Object Value) (property : ObjectPropertyExpression) (x : Object) :
    Counted I property none x = fun y => objectRelation I property x y := by
  funext y; simp [Counted,FillerHolds]
private theorem counted_some (I : Interpretation Object Value) (property : ObjectPropertyExpression)
    (c : ClassExpression) (x : Object) :
    Counted I property (some c) x = fun y => objectRelation I property x y ∧ classDenote I c y := by
  funext y; simp [Counted,FillerHolds]

/-- A lower (`minimum`) or upper bound on the counted neighbours. -/
def Bounded (minimum : Bool) (n : Nat) {α : Type u} (P : α → Prop) : Prop :=
  if minimum then AtLeast n P else AtMost n P

private theorem cardinality_filler_correct (filler : Option ClassExpression)
    (child : ∀ inner, filler = some inner →
      ∃ result, concepts.translate inner true = .ok result ∧ Correct.{u,v} inner true result) :
    ∃ result, concepts.cardinality_filler filler = .ok result ∧
      (result.isSome ↔ ∀ inner, filler = some inner → Translatable inner) ∧
      ∀ concept, result = some concept →
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I → ∀ y,
          (denote I concept y ↔ FillerHolds I filler y) := by
  cases filler with
  | none =>
    refine ⟨some .Top,by rw [concepts.cardinality_filler],by simp,?_⟩
    intro concept same Object Value I fixes y
    cases same
    simp [denote,FillerHolds]
  | some inner =>
    obtain ⟨result,run,correct⟩ := child inner rfl
    refine ⟨result,by rw [concepts.cardinality_filler]; exact run,?_,?_⟩
    · cases result with
      | none => simpa [Correct] using correct
      | some _ => simpa using correct.1
    · intro concept same Object Value I fixes y
      subst same
      simpa [Polar,FillerHolds] using correct.2 Object Value I fixes y

private theorem cardinality_correct (n : probes.Natural) (property : ObjectPropertyExpression)
    (filler : Option ClassExpression) (positive minimum : Bool)
    (child : ∀ inner, filler = some inner →
      ∃ result, concepts.translate inner true = .ok result ∧ Correct.{u,v} inner true result) :
    ∃ result, concepts.cardinality n property filler positive minimum = .ok result ∧
      (result.isSome ↔ Rowl.Probes.naturalValue n < Usize.max ∧ ∀ inner, filler = some inner → Translatable inner) ∧
      ∀ concept, result = some concept →
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I → ∀ x,
          (denote I concept x ↔
            Polar positive (Bounded minimum (Rowl.Probes.naturalValue n) (Counted I property filler x))) := by
  obtain ⟨bounded,boundRun,boundSupport,boundValue⟩ := bound_correct n
  obtain ⟨inner,innerRun,innerSupport,innerMeaning⟩ := cardinality_filler_correct.{u,v} filler child
  cases bounded with
  | none =>
    refine ⟨none,by rw [concepts.cardinality]; simp [boundRun],?_,by simp⟩
    simp only [Option.isSome_none,Bool.false_eq_true,false_iff,not_and]
    intro fits
    exact absurd (boundSupport.mpr fits) (by simp)
  | some k =>
    have kValue := boundValue k rfl
    have fits : k.val < Usize.max := by rw [kValue]; exact boundSupport.mp rfl
    cases inner with
    | none =>
      refine ⟨none,by rw [concepts.cardinality]; simp [boundRun,innerRun],?_,by simp⟩
      simp only [Option.isSome_none,Bool.false_eq_true,false_iff,not_and]
      intro _ supported
      exact absurd (innerSupport.mpr supported) (by simp)
    | some concept =>
      have support : Rowl.Probes.naturalValue n < Usize.max ∧ ∀ inner, filler = some inner → Translatable inner :=
        ⟨by rw [← kValue]; exact fits,innerSupport.mp rfl⟩
      have counted : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I → ∀ x y,
          (objectRelation I property x y ∧ denote I concept y) ↔ Counted I property filler x y := by
        intro Object Value I fixes x y
        rw [innerMeaning concept rfl Object Value I fixes y]
        rfl
      cases minimum with
      | true =>
        cases positive with
        | true =>
          refine ⟨some (.AtLeast k property concept),by rw [concepts.cardinality]; simp [boundRun,innerRun,
            copy_role_identity],by simpa using support,?_⟩
          intro c same Object Value I fixes x
          cases same
          simp only [denote,Polar,Bounded,if_pos,kValue]
          exact atLeast_congr _ (counted Object Value I fixes x)
        | false =>
          by_cases zero : k = 0#usize
          · refine ⟨some .Bottom,by rw [concepts.cardinality]; simp [boundRun,innerRun,zero],by simpa using support,?_⟩
            intro c same Object Value I fixes x
            cases same
            have : Rowl.Probes.naturalValue n = 0 := by rw [← kValue,zero]; rfl
            simp only [denote,Polar,Bounded,if_pos,this,false_iff,not_not]
            exact atLeast_zero _
          · obtain ⟨m,lower,lowerValue⟩ := WP.spec_imp_exists (Usize.sub_spec (x := k) (y := 1#usize) (by
              have : k.val ≠ 0 := fun same => zero (UScalar.eq_of_val_eq (by simpa using same))
              scalar_tac))
            refine ⟨some (.AtMost m property concept),by rw [concepts.cardinality]; simp [boundRun,innerRun,zero,
              lower,copy_role_identity],by simpa using support,?_⟩
            intro c same Object Value I fixes x
            cases same
            have succ : m.val + 1 = Rowl.Probes.naturalValue n := by
              have : k.val ≠ 0 := fun same => zero (UScalar.eq_of_val_eq (by simpa using same))
              simp at lowerValue; omega
            simp only [denote,Polar,Bounded,if_pos,AtMost,succ]
            exact not_congr (atLeast_congr _ (counted Object Value I fixes x))
      | false =>
        cases positive with
        | true =>
          refine ⟨some (.AtMost k property concept),by rw [concepts.cardinality]; simp [boundRun,innerRun,
            copy_role_identity],by simpa using support,?_⟩
          intro c same Object Value I fixes x
          cases same
          simp only [denote,Polar,Bounded,Bool.false_eq_true,if_false,AtMost,kValue]
          exact not_congr (atLeast_congr _ (counted Object Value I fixes x))
        | false =>
          have less : k < core.num.Usize.MAX := by
            rw [UScalar.lt_equiv]; simpa [core.num.Usize.MAX] using fits
          obtain ⟨m,higher,higherValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
          refine ⟨some (.AtLeast m property concept),by rw [concepts.cardinality]; simp [boundRun,innerRun,less,
            higher,copy_role_identity,fits],by simpa using support,?_⟩
          intro c same Object Value I fixes x
          cases same
          have succ : m.val = Rowl.Probes.naturalValue n + 1 := by simp at higherValue; omega
          simp only [denote,Polar,Bounded,Bool.false_eq_true,if_false,AtMost,succ,not_not]
          exact atLeast_congr _ (counted Object Value I fixes x)

private theorem exactly_correct (n : probes.Natural) (property : ObjectPropertyExpression)
    (filler : Option ClassExpression) (positive : Bool)
    (child : ∀ inner, filler = some inner →
      ∃ result, concepts.translate inner true = .ok result ∧ Correct.{u,v} inner true result) :
    ∃ result, concepts.exactly n property filler positive = .ok result ∧
      (result.isSome ↔ Rowl.Probes.naturalValue n < Usize.max ∧ ∀ inner, filler = some inner → Translatable inner) ∧
      ∀ concept, result = some concept →
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Fixes I → ∀ x,
          (denote I concept x ↔
            Polar positive (Rowl.Owl.Exactly (Rowl.Probes.naturalValue n) (Counted I property filler x))) := by
  obtain ⟨low,lowRun,lowSupport,lowMeaning⟩ := cardinality_correct.{u,v} n property filler positive true child
  obtain ⟨high,highRun,highSupport,highMeaning⟩ := cardinality_correct.{u,v} n property filler positive false child
  cases low with
  | none => exact ⟨none,by rw [concepts.exactly]; simp [lowRun],by simpa using lowSupport,by simp⟩
  | some low =>
    cases high with
    | none => exact ⟨none,by rw [concepts.exactly]; simp [lowRun,highRun],by simpa using highSupport,by simp⟩
    | some high =>
      refine ⟨some (if positive then .And low high else .Or low high),by rw [concepts.exactly]; simp [lowRun,
        highRun,join_correct],by simpa using lowSupport,?_⟩
      intro concept same Object Value I fixes x
      cases same
      rw [join_denote,lowMeaning low rfl Object Value I fixes x,highMeaning high rfl Object Value I fixes x]
      cases positive with
      | true =>
        simp only [Polar,Bounded,Rowl.Owl.Exactly,if_pos]
        tauto
      | false =>
        simp only [Polar,Bounded,Rowl.Owl.Exactly,if_pos,Bool.false_eq_true,if_false]
        tauto

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
    ALCIQO fragment it returns `None`, and inside it the result means exactly the
    expression (positive polarity) or its complement (negative polarity). -/
theorem translate_total_correct (expression : ClassExpression) (positive : Bool) :
    ∃ result, concepts.translate expression positive = .ok result ∧ Correct.{u,v} expression positive result := by
  cases h : expression with
  | Class c =>
    obtain ⟨concept,executed,meaning⟩ := named_correct.{u,v} c positive
    refine ⟨some concept,by rw [concepts.translate]; simp [executed],by simp [Translatable],?_⟩
    intro Object Value I fixes x
    rw [meaning Object Value I fixes x]
    simp [classDenote]
  | ObjectIntersectionOf xs =>
    obtain ⟨result,executed,support,meaning⟩ := connect_correct.{u,v} xs positive positive
      (fun e mem polarity =>
        have := member_size xs e mem
        translate_total_correct e polarity)
    refine ⟨result,by rw [concepts.translate]; exact executed,?_⟩
    have fragment : Translatable (.ObjectIntersectionOf xs) ↔ ∀ e ∈ xs.elements, Translatable e := by
      simp [Translatable,AtLeastTwo.elements]
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
    have fragment : Translatable (.ObjectUnionOf xs) ↔ ∀ e ∈ xs.elements, Translatable e := by
      simp [Translatable,AtLeastTwo.elements]
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
    | none => simpa [Correct,Translatable] using correct
    | some concept =>
      refine ⟨by simpa [Translatable] using correct.1,?_⟩
      intro Object Value I fixes x
      rw [correct.2 Object Value I fixes x]
      cases positive <;> simp [Polar,classDenote]
  | ObjectSomeValuesFrom property filler =>
    obtain ⟨result,executed,support,meaning⟩ := restriction_correct.{u,v} property filler positive positive
      (fun polarity => translate_total_correct filler polarity)
    refine ⟨result,by rw [concepts.translate]; exact executed,?_⟩
    cases result with
    | none => simpa [Correct,Translatable] using support
    | some concept =>
      refine ⟨by simpa [Translatable] using support,?_⟩
      intro Object Value I fixes x
      rw [meaning concept rfl Object Value I fixes x]
      cases positive <;> simp [Quantified,Polar,classDenote]
  | ObjectAllValuesFrom property filler =>
    obtain ⟨result,executed,support,meaning⟩ := restriction_correct.{u,v} property filler positive
      (decide ¬ positive = true) (fun polarity => translate_total_correct filler polarity)
    refine ⟨result,by rw [concepts.translate]; exact executed,?_⟩
    cases result with
    | none => simpa [Correct,Translatable] using support
    | some concept =>
      refine ⟨by simpa [Translatable] using support,?_⟩
      intro Object Value I fixes x
      rw [meaning concept rfl Object Value I fixes x]
      cases positive <;> simp [Quantified,Polar,classDenote]
  | ObjectMinCardinality n property filler =>
    have child : ∀ inner, filler = some inner →
        ∃ result, concepts.translate inner true = .ok result ∧ Correct.{u,v} inner true result := by
      cases filler with
      | none => intro inner impossible; cases impossible
      | some inner => intro other same; cases same; exact translate_total_correct inner true
    obtain ⟨result,executed,support,meaning⟩ := cardinality_correct.{u,v} n property filler positive true child
    refine ⟨result,by rw [concepts.translate]; exact executed,?_⟩
    have fragment : Translatable (.ObjectMinCardinality n property filler) ↔
        Rowl.Probes.naturalValue n < Usize.max ∧ ∀ inner, filler = some inner → Translatable inner := by
      cases filler <;> simp [Translatable]
    cases result with
    | none => simpa [Correct,fragment] using support
    | some concept =>
      refine ⟨fragment.mpr (support.mp rfl),?_⟩
      intro Object Value I fixes x
      rw [meaning concept rfl Object Value I fixes x]
      cases filler <;> simp [Bounded,counted_none,counted_some,classDenote]
  | ObjectMaxCardinality n property filler =>
    have child : ∀ inner, filler = some inner →
        ∃ result, concepts.translate inner true = .ok result ∧ Correct.{u,v} inner true result := by
      cases filler with
      | none => intro inner impossible; cases impossible
      | some inner => intro other same; cases same; exact translate_total_correct inner true
    obtain ⟨result,executed,support,meaning⟩ := cardinality_correct.{u,v} n property filler positive false child
    refine ⟨result,by rw [concepts.translate]; exact executed,?_⟩
    have fragment : Translatable (.ObjectMaxCardinality n property filler) ↔
        Rowl.Probes.naturalValue n < Usize.max ∧ ∀ inner, filler = some inner → Translatable inner := by
      cases filler <;> simp [Translatable]
    cases result with
    | none => simpa [Correct,fragment] using support
    | some concept =>
      refine ⟨fragment.mpr (support.mp rfl),?_⟩
      intro Object Value I fixes x
      rw [meaning concept rfl Object Value I fixes x]
      cases filler <;> simp [Bounded,counted_none,counted_some,classDenote]
  | ObjectExactCardinality n property filler =>
    have child : ∀ inner, filler = some inner →
        ∃ result, concepts.translate inner true = .ok result ∧ Correct.{u,v} inner true result := by
      cases filler with
      | none => intro inner impossible; cases impossible
      | some inner => intro other same; cases same; exact translate_total_correct inner true
    obtain ⟨result,executed,support,meaning⟩ := exactly_correct.{u,v} n property filler positive child
    refine ⟨result,by rw [concepts.translate]; exact executed,?_⟩
    have fragment : Translatable (.ObjectExactCardinality n property filler) ↔
        Rowl.Probes.naturalValue n < Usize.max ∧ ∀ inner, filler = some inner → Translatable inner := by
      cases filler <;> simp [Translatable]
    cases result with
    | none => simpa [Correct,fragment] using support
    | some concept =>
      refine ⟨fragment.mpr (support.mp rfl),?_⟩
      intro Object Value I fixes x
      rw [meaning concept rfl Object Value I fixes x]
      cases filler <;> simp [counted_none,counted_some,classDenote]
  | ObjectOneOf members =>
    obtain ⟨concept,executed,meaning⟩ := one_of_correct.{u,v} members positive
    refine ⟨some concept,by rw [concepts.translate]; simp [executed],by simp [Translatable],?_⟩
    intro Object Value I _ x
    exact meaning Object Value I x
  | ObjectHasValue property value =>
    obtain ⟨concept,executed,meaning⟩ := has_value_correct.{u,v} property value positive
    refine ⟨some concept,by rw [concepts.translate]; simp [executed],by simp [Translatable],?_⟩
    intro Object Value I _ x
    exact meaning Object Value I x
  | ObjectHasSelf _ | DataSomeValuesFrom _ _ | DataAllValuesFrom _ _ | DataHasValue _ _
  | DataMinCardinality _ _ _ | DataMaxCardinality _ _ _ | DataExactCardinality _ _ _ =>
    exact ⟨none,by rw [concepts.translate],by simp [Correct,Translatable]⟩
termination_by sizeOf expression
decreasing_by
  all_goals simp only [h,ClassExpression.ObjectIntersectionOf.sizeOf_spec,ClassExpression.ObjectUnionOf.sizeOf_spec,
    ClassExpression.ObjectComplementOf.sizeOf_spec,ClassExpression.ObjectSomeValuesFrom.sizeOf_spec,
    ClassExpression.ObjectAllValuesFrom.sizeOf_spec,ClassExpression.ObjectMinCardinality.sizeOf_spec,
    ClassExpression.ObjectMaxCardinality.sizeOf_spec,ClassExpression.ObjectExactCardinality.sizeOf_spec,
    Option.some.sizeOf_spec]
  all_goals omega

/-- The translation succeeds exactly on the ALCIQO fragment. -/
theorem translate_supported_iff (expression : ClassExpression) (positive : Bool) :
    (∃ concept, concepts.translate expression positive = .ok (some concept)) ↔ Translatable expression := by
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
