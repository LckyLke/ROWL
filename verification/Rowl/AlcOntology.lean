import Rowl.OntologyRoles
import Rowl.AboxTableau

/-!
Ontology-level answers for ALC axiom closures with role axioms and assertions
about individuals, proved against the independent Direct Semantics:
consistency, class satisfiability, subsumption and instance checking. The class
axioms become the TBox concept, the inclusions, equivalences and transitivity of
named object properties become the role box, the assertions become the facts and
edges of the completion for named individuals, and every answer the kernel
gives is exact for the OWL
definitions: an acceptance comes with an actual OWL model of the closure (built
from the completion's model, with every individual at its node, the built-in
classes and properties and the datatype map fixed as OWL requires), and every
OWL model, in any universe, forces acceptance.
-/
namespace Rowl.AlcOntology
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation classDenote thing nothing topObject bottomObject topData bottomData
  literalDatatype DatatypeMap ValueEmbedding Vocabulary IsVocabulary IsInterpretation Model Consistent
  ClassSatisfiable Subsumed InstanceOf withAnonymous)
open Rowl.Nnf (conceptDenote Fixes Polar nnf_total_correct nnf_meaning fixes_of_interpretation)
open Rowl.Internalization (internalize_correct TBoxPart Assertion RoleAxiom)
open Rowl.AboxTableau (factsList edgesList AboxModel ExactEdges RoleModel EntailedEdges Entailed EdgeStep
  abox_satisfiable_with_correct)
open Rowl.RoleBox (Respects transitives inclusionList)
open Rowl.OntologyRoles (RolesHold role_box_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
universe u v w

/-- No built-in class occurs as a named class and no built-in object property
    as a role, so the tableau's reading of every name is an ordinary one. -/
def Proper : nnf.NnfConcept → Prop
  | .Top => True
  | .Bottom => True
  | .Atom c => c ≠ thing ∧ c ≠ nothing
  | .NotAtom c => c ≠ thing ∧ c ≠ nothing
  | .And a b => Proper a ∧ Proper b
  | .Or a b => Proper a ∧ Proper b
  | .Exists r c => r ≠ topObject ∧ r ≠ bottomObject ∧ Proper c
  | .Forall r c => r ≠ topObject ∧ r ≠ bottomObject ∧ Proper c

private theorem equal_total (key : alloc.vec.Vec U8) (pattern : Slice U8)
    (equalLength : key.val.length = pattern.val.length) (index : Usize) :
    alc_ontology.equal_from key pattern index =
      .ok (decide (key.val.drop index.val = pattern.val.drop index.val)) := by
  rw [alc_ontology.equal_from]
  by_cases h : index.val < key.val.length
  · have hr : index.val < pattern.val.length := by omega
    have hkIndex : key.index_usize index = .ok key.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem h]
    have hpIndex : pattern.index_usize index = .ok pattern.val[index.val] := by
      simp [Slice.index_usize,List.getElem?_eq_getElem hr]
    by_cases heads : key.val[index.val] = pattern.val[index.val]
    · obtain ⟨next,hn,hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have ih := equal_total key pattern equalLength next
      simp [h,hkIndex,hpIndex,heads,hn,ih]
      rw [List.drop_eq_getElem_cons h,List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq,heads,true_and,nextval]
    · simp [h,hkIndex,hpIndex,heads]
      rw [List.drop_eq_getElem_cons h,List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq,heads,false_and,not_false_eq_true]
  · have hk : key.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hp : pattern.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [h,hk,hp]
termination_by key.val.length - index.val
decreasing_by omega
theorem same_pattern_total (key : alloc.vec.Vec U8) (pattern : Slice U8) :
    alc_ontology.same_pattern key pattern = .ok (decide (key.val = pattern.val)) := by
  rw [alc_ontology.same_pattern]
  by_cases h : key.val.length = pattern.val.length
  · simpa [h] using equal_total key pattern h 0#usize
  · have unequal : key.val ≠ pattern.val := fun same => h (congrArg List.length same)
    simp [h,unequal]

/-- Exact recognition of the two built-in classes. -/
theorem builtin_class_correct (c : Class) :
    alc_ontology.builtin_class c = .ok (decide (c = thing ∨ c = nothing)) := by
  rw [alc_ontology.builtin_class]
  simp only [Rowl.Tableau.class_eq_iff c thing,Rowl.Tableau.class_eq_iff c nothing]
  by_cases top : c.iri.spelling.val = thing.iri.spelling.val <;>
    simp_all [same_pattern_total,Array.to_slice,Array.make,lift,thing,nothing]
/-- Exact recognition of the two built-in object properties. -/
theorem builtin_role_correct (r : ObjectProperty) :
    alc_ontology.builtin_role r = .ok (decide (r = topObject ∨ r = bottomObject)) := by
  rw [alc_ontology.builtin_role]
  simp only [Rowl.Tableau.property_eq_iff r topObject,Rowl.Tableau.property_eq_iff r bottomObject]
  by_cases top : r.iri.spelling.val = topObject.iri.spelling.val <;>
    simp_all [same_pattern_total,Array.to_slice,Array.make,lift,topObject,bottomObject]
/-- The kernel's check decides `Proper` exactly. -/
theorem proper_correct (c : nnf.NnfConcept) : alc_ontology.proper c = .ok (decide (Proper c)) := by
  induction c with
  | Top => rw [alc_ontology.proper]; simp [Proper]
  | Bottom => rw [alc_ontology.proper]; simp [Proper]
  | Atom k => rw [alc_ontology.proper]; simp [Proper,builtin_class_correct]
  | NotAtom k => rw [alc_ontology.proper]; simp [Proper,builtin_class_correct]
  | And a b iha ihb =>
    rw [alc_ontology.proper]
    by_cases left : Proper a <;> simp [Proper,iha,ihb,left]
  | Or a b iha ihb =>
    rw [alc_ontology.proper]
    by_cases left : Proper a <;> simp [Proper,iha,ihb,left]
  | Exists r c ih =>
    rw [alc_ontology.proper]
    by_cases top : r = topObject <;> by_cases bottom : r = bottomObject <;>
      simp [Proper,builtin_role_correct,ih,top,bottom]
  | Forall r c ih =>
    rw [alc_ontology.proper]
    by_cases top : r = topObject <;> by_cases bottom : r = bottomObject <;>
      simp [Proper,builtin_role_correct,ih,top,bottom]

/-- Reinterpreting anonymous individuals leaves every concept's meaning unchanged. -/
theorem concept_with_anonymous {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (assignment : AnonymousIndividual → Object) :
    ∀ c x, conceptDenote (withAnonymous I assignment) c x ↔ conceptDenote I c x := by
  intro c
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ => intro x; exact Iff.rfl
  | And a b iha ihb => intro x; simp only [conceptDenote,iha x,ihb x]
  | Or a b iha ihb => intro x; simp only [conceptDenote,iha x,ihb x]
  | Exists r c ih => intro x; simp only [conceptDenote,ih]; exact Iff.rfl
  | Forall r c ih => intro x; simp only [conceptDenote,ih]; exact Iff.rfl

/-- Native datatype values become distinct data values. -/
def embedding {Native : Type w} (D : DatatypeMap Native) : ValueEmbedding D (ULift.{v} (Option Native)) :=
  ⟨fun n => ULift.up (some n),fun _ _ _ _ same => by simpa using same⟩
/-- The OWL interpretation of a tableau model: the built-in classes and object
    and data properties get their fixed meaning, every other class and object
    property keeps the tableau's reading, individuals sit where `place` puts
    them, and data values, datatypes, literals and facets come from the datatype
    map. -/
def owlModel {Object : Type} (J : Interpretation Object Unit) (root : Object) (place : Individual → Object)
    {Native : Type w} (D : DatatypeMap Native) : Interpretation (ULift.{u} Object) (ULift.{v} (Option Native)) where
  objectsNonempty := ⟨ULift.up root⟩
  dataNonempty := ⟨ULift.up none⟩
  classes k x := if k = thing then True else if k = nothing then False else J.classes k x.down
  objectProperties r x y :=
    if r = topObject then True else if r = bottomObject then False else J.objectProperties r x.down y.down
  dataProperties p _ _ := p = topData
  namedIndividuals a := ULift.up (place (.Named a))
  anonymousIndividuals a := ULift.up (place (.Anonymous a))
  datatypes dt x := if dt = literalDatatype then True else ∃ y, D.valueSpace dt y ∧ ULift.up (some y) = x
  literals lt := ULift.up (some (D.lexicalValue lt.datatype lt.lexical.val))
  facets f x := ∃ y, D.facetValue f.facet (D.lexicalValue f.value.datatype f.value.lexical.val) y ∧
    ULift.up (some y) = x
  named _ := True

/-- The constructed interpretation satisfies every condition OWL places on an
    interpretation. -/
theorem owl_model_valid {Object : Type} (J : Interpretation Object Unit) (root : Object) (place : Individual → Object)
    {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary) :
    IsInterpretation D (embedding.{v,w} D) V (owlModel.{u,v,w} J root place D) := by
  have classes : nothing ≠ thing := by
    intro same
    have := congrArg (fun c : Class => c.iri.spelling.val) same
    simp [thing,nothing] at this
  have roles : bottomObject ≠ topObject := by
    intro same
    have := congrArg (fun r : ObjectProperty => r.iri.spelling.val) same
    simp [topObject,bottomObject] at this
  have data : bottomData ≠ topData := by
    intro same
    have := congrArg (fun p : DataProperty => p.iri.spelling.val) same
    simp [topData,bottomData] at this
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x; simp [owlModel]
  · intro x; simp [owlModel,classes]
  · intro x y; simp [owlModel]
  · intro x y; simp [owlModel,roles]
  · intro x y; simp [owlModel]
  · intro x y; simp [owlModel,data]
  · intro dt supported x
    have notLiteral : dt ≠ literalDatatype := fun same => D.excludesLiteral (same ▸ supported)
    simp [owlModel,notLiteral,embedding]
  · intro x; simp [owlModel]
  · intro lt _; rfl
  · intro f _ x; exact Iff.rfl
  · intro a _; trivial
/-- On proper concepts the constructed interpretation agrees with the tableau model. -/
theorem owl_model_agrees {Object : Type} (J : Interpretation Object Unit) (root : Object) (place : Individual → Object)
    {Native : Type w} (D : DatatypeMap Native) :
    ∀ c, Proper c → ∀ x, conceptDenote (owlModel.{u,v,w} J root place D) c x ↔ conceptDenote J c x.down := by
  intro c
  induction c with
  | Top => intro _ x; simp [conceptDenote]
  | Bottom => intro _ x; simp [conceptDenote]
  | Atom k => intro proper x; simp [conceptDenote,owlModel,proper.1,proper.2]
  | NotAtom k => intro proper x; simp [conceptDenote,owlModel,proper.1,proper.2]
  | And a b iha ihb => intro proper x; simp only [conceptDenote,iha proper.1 x,ihb proper.2 x]
  | Or a b iha ihb => intro proper x; simp only [conceptDenote,iha proper.1 x,ihb proper.2 x]
  | Exists r c ih =>
    intro proper x
    simp only [conceptDenote,owlModel,proper.1,proper.2.1,↓reduceIte]
    constructor
    · rintro ⟨y,edge,inner⟩
      exact ⟨y.down,edge,(ih proper.2.2 y).mp inner⟩
    · rintro ⟨y,edge,inner⟩
      exact ⟨ULift.up y,edge,(ih proper.2.2 (ULift.up y)).mpr inner⟩
  | Forall r c ih =>
    intro proper x
    simp only [conceptDenote,owlModel,proper.1,proper.2.1,↓reduceIte]
    constructor
    · intro every y edge
      exact (ih proper.2.2 (ULift.up y)).mp (every (ULift.up y) edge)
    · intro every y edge
      exact (ih proper.2.2 y).mpr (every y.down edge)


/-- The individuals an assertion mentions. -/
def IndividualsOf : Axiom → List Individual
  | .ClassAssertion _ m => [m]
  | .ObjectPropertyAssertion _ s t => [s,t]
  | .NegativeObjectPropertyAssertion _ s t => [s,t]
  | _ => []
/-- The first position of an individual in a list from a starting count, plus
    one, or 0 when it is absent. -/
noncomputable def PositionFrom : List Individual → Individual → Nat → Nat
  | [], _, _ => 0
  | b :: rest, a, k => if b = a then k+1 else PositionFrom rest a (k+1)
/-- The node of an individual: its first position among the nodes plus one, or
    0 when it is absent. -/
noncomputable def PositionOf (nodes : List Individual) (a : Individual) : Nat := PositionFrom nodes a 0

theorem positionFrom_le : ∀ (l : List Individual) (a : Individual) (k : Nat), PositionFrom l a k ≤ k+l.length
  | [], _, _ => by simp [PositionFrom]
  | b :: rest, a, k => by
    have := positionFrom_le rest a (k+1)
    by_cases same : b = a
    · simp [PositionFrom,same]
    · simp only [PositionFrom,same,if_false,List.length_cons]; omega
theorem positionFrom_absent : ∀ (l : List Individual) (a : Individual) (k : Nat), a ∉ l → PositionFrom l a k = 0
  | [], _, _, _ => rfl
  | b :: rest, a, k, absent => by
    have different : b ≠ a := fun same => absent (same ▸ List.mem_cons_self ..)
    simp only [PositionFrom,different,if_false]
    exact positionFrom_absent rest a (k+1) (fun inRest => absent (List.mem_cons_of_mem _ inRest))
theorem positionFrom_present : ∀ (l : List Individual) (a : Individual) (k : Nat), a ∈ l →
    ∃ i, ∃ bound : i < l.length, l[i] = a ∧ PositionFrom l a k = k+i+1
  | b :: rest, a, k, present => by
    by_cases same : b = a
    · exact ⟨0,by simp,by simp [same],by simp [PositionFrom,same]⟩
    · have inRest : a ∈ rest := by
        rcases List.mem_cons.mp present with equal | later
        · exact absurd equal.symm same
        · exact later
      obtain ⟨i,bound,at_i,value⟩ := positionFrom_present rest a (k+1) inRest
      exact ⟨i+1,by simpa using bound,by simpa using at_i,by simp only [PositionFrom,same,if_false,value]; omega⟩
theorem positionOf_le (nodes : List Individual) (a : Individual) : PositionOf nodes a ≤ nodes.length := by
  simpa [PositionOf] using positionFrom_le nodes a 0
/-- A present individual sits at its node. -/
theorem positionOf_present (nodes : List Individual) (a : Individual) (present : a ∈ nodes) :
    ∃ bound : PositionOf nodes a - 1 < nodes.length, 0 < PositionOf nodes a ∧ nodes[PositionOf nodes a - 1] = a := by
  obtain ⟨i,bound,at_i,value⟩ := positionFrom_present nodes a 0 present
  have value' : PositionOf nodes a = i+1 := by simpa [PositionOf] using value
  refine ⟨by rw [value']; simpa using bound,by omega,?_⟩
  simp only [value',Nat.add_sub_cancel]
  exact at_i

/-- Copying an individual reproduces it exactly. -/
theorem copy_individual_identity (a : Individual) : alc_ontology.copy_individual a = .ok a := by
  cases a with
  | Named named => cases named; simp [alc_ontology.copy_individual,Rowl.Nnf.copy_iri_identity]
  | Anonymous anonymous => cases anonymous; simp [alc_ontology.copy_individual,Rowl.Nnf.copy_bytes_identity]

/-- The actual node search finds the first position from the index. -/
theorem position_correct (nodes : alloc.vec.Vec Individual) (a : Individual) (index : Usize)
    (inside : index.val ≤ nodes.val.length) :
    ∃ p, alc_ontology.position nodes a index = .ok p ∧ p.val = PositionFrom (nodes.val.drop index.val) a index.val := by
  rw [alc_ontology.position]
  by_cases more : index.val < nodes.val.length
  · have lookup : nodes.index_usize index = .ok nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : nodes.val.drop index.val = nodes.val[index.val] :: nodes.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    by_cases same : nodes.val[index.val] = a
    · refine ⟨next,by simp [more,lookup,Rowl.AssertionEquality.same_individual_value_total_correct,same,advance],?_⟩
      rw [split,nextIndex]
      simp [PositionFrom,same]
    · obtain ⟨p,run,value⟩ := position_correct nodes a next (by omega)
      refine ⟨p,by simp [more,lookup,Rowl.AssertionEquality.same_individual_value_total_correct,same,advance,run],?_⟩
      rw [value,split,nextIndex]
      simp [PositionFrom,same]
  · refine ⟨0#usize,by simp [more],?_⟩
    have empty : nodes.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [empty,PositionFrom]
termination_by nodes.val.length - index.val
decreasing_by omega
theorem position_of (nodes : alloc.vec.Vec Individual) (a : Individual) :
    ∃ p, alc_ontology.position nodes a 0#usize = .ok p ∧ p.val = PositionOf nodes.val a := by
  obtain ⟨p,run,value⟩ := position_correct nodes a 0#usize (by simp)
  exact ⟨p,run,by simpa [PositionOf] using value⟩

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- Interning keeps every node, adds the individual when it is new, and keeps
    the node count small enough for one more node. -/
theorem intern_correct (nodes : alloc.vec.Vec Individual) (a : Individual)
    (room : nodes.val.length ≤ Usize.max-1) :
    ∃ result, alc_ontology.intern nodes a = .ok result ∧ ∀ final, result = some final →
      (∀ b ∈ nodes.val, b ∈ final.val) ∧ a ∈ final.val ∧ final.val.length ≤ Usize.max-1 := by
  obtain ⟨p,run,value⟩ := position_of nodes a
  rw [alc_ontology.intern]
  by_cases present : a ∈ nodes.val
  · have nonzero : p ≠ 0#usize := by
      intro zero
      obtain ⟨_,positive,_⟩ := positionOf_present nodes.val a present
      rw [← value,zero] at positive
      simp at positive
    have nonzero' : ¬ p.val = 0 := fun h => nonzero (UScalar.eq_of_val_eq (by simpa using h))
    refine ⟨some nodes,by simp [run,nonzero'],?_⟩
    intro final same
    cases same
    exact ⟨fun b member => member,present,room⟩
  · have zero : p = 0#usize := by
      apply UScalar.eq_of_val_eq
      rw [value]
      simpa [PositionOf] using positionFrom_absent nodes.val a 0 present
    obtain ⟨limit,limitRun,limitValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := core.num.Usize.MAX) (y := 1#usize) (by simp [usize_max_val]; scalar_tac))
    have limitIs : limit.val = Usize.max-1 := by simp [usize_max_val] at limitValue; exact limitValue.1
    by_cases fits : nodes.val.length < Usize.max-1
    · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec nodes a (by omega))
      refine ⟨some appended,?_,?_⟩
      · simp [run,zero,limitRun,limitIs,fits,copy_individual_identity,push]
      · intro final same
        cases same
        rw [contents]
        refine ⟨fun b member => List.mem_append_left _ member,List.mem_append_right _ (List.mem_singleton_self _),?_⟩
        simp; omega
    · refine ⟨none,?_,by intro final impossible; cases impossible⟩
      simp [run,zero,limitRun,limitIs,fits]
theorem intern_pair_correct (nodes : alloc.vec.Vec Individual) (a b : Individual)
    (room : nodes.val.length ≤ Usize.max-1) :
    ∃ result, alc_ontology.intern_pair nodes a b = .ok result ∧ ∀ final, result = some final →
      (∀ c ∈ nodes.val, c ∈ final.val) ∧ a ∈ final.val ∧ b ∈ final.val ∧ final.val.length ≤ Usize.max-1 := by
  obtain ⟨first,firstRun,firstSpec⟩ := intern_correct nodes a room
  rw [alc_ontology.intern_pair]
  cases first with
  | none => exact ⟨none,by simp [firstRun],by intro final impossible; cases impossible⟩
  | some middle =>
    obtain ⟨kept,hasA,middleRoom⟩ := firstSpec middle rfl
    obtain ⟨second,secondRun,secondSpec⟩ := intern_correct middle b middleRoom
    refine ⟨second,by simp [firstRun,secondRun],?_⟩
    intro final same
    obtain ⟨kept',hasB,finalRoom⟩ := secondSpec final same
    exact ⟨fun c member => kept' c (kept c member),kept' a hasA,hasB,finalRoom⟩

/-- Interning the individuals of the assertions keeps every node, adds every
    individual an assertion mentions, and leaves room for one more node. -/
theorem individuals_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize)
    (nodes : alloc.vec.Vec Individual) (room : nodes.val.length ≤ Usize.max-1) :
    ∃ result, alc_ontology.individuals_from items index nodes = .ok result ∧ ∀ final, result = some final →
      (∀ b ∈ nodes.val, b ∈ final.val) ∧
      (∀ item ∈ items.val.drop index.val, ∀ a ∈ IndividualsOf item.axiom, a ∈ final.val) ∧
      final.val.length ≤ Usize.max-1 := by
  rw [alc_ontology.individuals_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have tail : ∀ middle : alloc.vec.Vec Individual, (∀ b ∈ nodes.val, b ∈ middle.val) →
        (∀ a ∈ IndividualsOf items.val[index.val].axiom, a ∈ middle.val) → middle.val.length ≤ Usize.max-1 →
        ∃ result, alc_ontology.individuals_from items next middle = .ok result ∧ ∀ final, result = some final →
          (∀ b ∈ nodes.val, b ∈ final.val) ∧
          (∀ item ∈ items.val.drop index.val, ∀ a ∈ IndividualsOf item.axiom, a ∈ final.val) ∧
          final.val.length ≤ Usize.max-1 := by
      intro middle kept here middleRoom
      obtain ⟨result,run,spec⟩ := individuals_from_correct items next middle middleRoom
      refine ⟨result,run,?_⟩
      intro final same
      obtain ⟨kept',later,finalRoom⟩ := spec final same
      refine ⟨fun b member => kept' b (kept b member),?_,finalRoom⟩
      intro item member a mentioned
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | rest
      · exact kept' a (here a mentioned)
      · rw [nextIndex] at later
        exact later item rest a mentioned
    cases item : items.val[index.val].axiom with
    | ClassAssertion C m =>
      obtain ⟨middle,middleRun,middleSpec⟩ := intern_correct nodes m room
      cases middle with
      | none => exact ⟨none,by simp [more,lookup,item,middleRun],by intro final impossible; cases impossible⟩
      | some middle =>
        obtain ⟨kept,hasM,middleRoom⟩ := middleSpec middle rfl
        obtain ⟨result,run,spec⟩ := tail middle kept (by simp [item,IndividualsOf,hasM]) middleRoom
        exact ⟨result,by simp [more,lookup,item,middleRun,advance,run],spec⟩
    | ObjectPropertyAssertion p a b =>
      obtain ⟨middle,middleRun,middleSpec⟩ := intern_pair_correct nodes a b room
      cases middle with
      | none => exact ⟨none,by simp [more,lookup,item,middleRun],by intro final impossible; cases impossible⟩
      | some middle =>
        obtain ⟨kept,hasA,hasB,middleRoom⟩ := middleSpec middle rfl
        obtain ⟨result,run,spec⟩ := tail middle kept (by simp [item,IndividualsOf,hasA,hasB]) middleRoom
        exact ⟨result,by simp [more,lookup,item,middleRun,advance,run],spec⟩
    | NegativeObjectPropertyAssertion p a b =>
      obtain ⟨middle,middleRun,middleSpec⟩ := intern_pair_correct nodes a b room
      cases middle with
      | none => exact ⟨none,by simp [more,lookup,item,middleRun],by intro final impossible; cases impossible⟩
      | some middle =>
        obtain ⟨kept,hasA,hasB,middleRoom⟩ := middleSpec middle rfl
        obtain ⟨result,run,spec⟩ := tail middle kept (by simp [item,IndividualsOf,hasA,hasB]) middleRoom
        exact ⟨result,by simp [more,lookup,item,middleRun,advance,run],spec⟩
    | _ =>
      obtain ⟨result,run,spec⟩ := tail nodes (fun b member => member) (by simp [item,IndividualsOf]) room
      exact ⟨result,by simp [more,lookup,item,advance,run],spec⟩
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some nodes,by simp [more],?_⟩
    intro final same
    cases same
    exact ⟨fun b member => member,by simp [empty],room⟩
termination_by items.val.length - index.val
decreasing_by omega

/-- The concepts placed for the class assertions: each comes from the given
    concepts or from a class assertion at its individual's node, and every class
    assertion is placed. -/
theorem assertions_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (index : Usize) (placed : alloc.vec.Vec alc_ontology.Placed) :
    ∃ result, alc_ontology.assertions_from items nodes index placed = .ok result ∧ ∀ final, result = some final →
      (∀ q ∈ final.val, q ∈ placed.val ∨ ∃ item ∈ items.val.drop index.val, ∃ C m,
        item.axiom = .ClassAssertion C m ∧ q.node.val = PositionOf nodes.val m ∧
        nnf.nnf C true = .ok (some q.concept)) ∧
      (∀ q ∈ placed.val, q ∈ final.val) ∧
      (∀ item ∈ items.val.drop index.val, ∀ C m, item.axiom = .ClassAssertion C m →
        ∃ q ∈ final.val, q.node.val = PositionOf nodes.val m ∧ nnf.nnf C true = .ok (some q.concept)) := by
  rw [alc_ontology.assertions_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    cases item : items.val[index.val].axiom with
    | ClassAssertion C m =>
      obtain ⟨translated,translatedRead,_⟩ := nnf_total_correct.{0,0} C true
      cases translated with
      | none => exact ⟨none,by simp [more,lookup,item,translatedRead],by intro final impossible; cases impossible⟩
      | some concept =>
        obtain ⟨node,nodeRun,nodeValue⟩ := position_of nodes m
        by_cases fits : placed.val.length < Usize.max
        · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec placed ⟨node,concept⟩ fits)
          obtain ⟨result,run,spec⟩ := assertions_from_correct items nodes next appended
          refine ⟨result,by simp [more,lookup,item,translatedRead,usize_max_val,fits,nodeRun,push,advance,run],?_⟩
          intro final same
          obtain ⟨origin,kept,covered⟩ := spec final same
          refine ⟨?_,fun q member => kept q (by rw [contents]; exact List.mem_append_left _ member),?_⟩
          · intro q member
            rcases origin q member with fromAppended | later
            · rw [contents] at fromAppended
              rcases List.mem_append.mp fromAppended with old | here
              · exact .inl old
              · rw [List.mem_singleton] at here
                subst here
                exact .inr ⟨items.val[index.val],by rw [split]; exact List.mem_cons_self ..,C,m,item,nodeValue,
                  translatedRead⟩
            · obtain ⟨other,otherIn,D,k,otherItem,otherNode,otherRead⟩ := later
              rw [nextIndex] at otherIn
              exact .inr ⟨other,by rw [split]; exact List.mem_cons_of_mem _ otherIn,D,k,otherItem,otherNode,otherRead⟩
          · intro other member D k otherItem
            rw [split] at member
            rcases List.mem_cons.mp member with rfl | later
            · rw [item] at otherItem
              cases otherItem
              exact ⟨⟨node,concept⟩,kept _ (by rw [contents]; exact List.mem_append_right _ (List.mem_singleton_self _)),
                nodeValue,translatedRead⟩
            · rw [nextIndex] at covered
              exact covered other later D k otherItem
        · exact ⟨none,by simp [more,lookup,item,translatedRead,usize_max_val,fits],
            by intro final impossible; cases impossible⟩
    | _ =>
      obtain ⟨result,run,spec⟩ := assertions_from_correct items nodes next placed
      refine ⟨result,by simp [more,lookup,item,advance,run],?_⟩
      intro final same
      obtain ⟨origin,kept,covered⟩ := spec final same
      refine ⟨?_,kept,?_⟩
      · intro q member
        rcases origin q member with old | ⟨other,otherIn,D,k,otherItem,otherNode,otherRead⟩
        · exact .inl old
        · rw [nextIndex] at otherIn
          exact .inr ⟨other,by rw [split]; exact List.mem_cons_of_mem _ otherIn,D,k,otherItem,otherNode,otherRead⟩
      · intro other member D k otherItem
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · rw [item] at otherItem
          cases otherItem
        · rw [nextIndex] at covered
          exact covered other later D k otherItem
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some placed,by simp [more],?_⟩
    intro final same
    cases same
    exact ⟨fun q member => .inl member,fun q member => member,by simp [empty]⟩
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- The properness check over placed concepts is exact. -/
theorem placed_proper_correct (placed : alloc.vec.Vec alc_ontology.Placed) (index : Usize) :
    alc_ontology.placed_proper placed index = .ok (decide (∀ q ∈ placed.val.drop index.val, Proper q.concept)) := by
  rw [alc_ontology.placed_proper]
  by_cases more : index.val < placed.val.length
  · have lookup : placed.index_usize index = .ok placed.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : placed.val.drop index.val = placed.val[index.val] :: placed.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := placed_proper_correct placed next
    rw [nextIndex] at rest
    rw [split]
    simp only [List.forall_mem_cons]
    by_cases here : Proper placed.val[index.val].concept
    · simp [more,lookup,proper_correct,here,advance,rest]
    · simp [more,lookup,proper_correct,here]
  · have empty : placed.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [more,empty]
termination_by placed.val.length - index.val
decreasing_by omega

/-- The named object property of an object property expression. -/
def RoleOf : ObjectPropertyExpression → ObjectProperty
  | .Property r => r
  | .Inverse r => r
/-- An object property assertion or role axiom that does not use a built-in
    object property. -/
def RoleProper : Axiom → Prop
  | .ObjectPropertyAssertion p _ _ => RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject
  | .NegativeObjectPropertyAssertion p _ _ => RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject
  | .SubObjectPropertyOf (.Single sub) sup => (RoleOf sub ≠ topObject ∧ RoleOf sub ≠ bottomObject) ∧
      (RoleOf sup ≠ topObject ∧ RoleOf sup ≠ bottomObject)
  | .EquivalentObjectProperties xs => ∀ p ∈ xs.elements, RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject
  | .TransitiveObjectProperty p => RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject
  | _ => True
theorem named_property_correct (p : ObjectPropertyExpression) : alc_ontology.named_property p = .ok (RoleOf p) := by
  cases p <;> rfl
theorem role_proper_correct (p : ObjectPropertyExpression) :
    alc_ontology.role_proper p = .ok (decide (RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject)) := by
  rw [alc_ontology.role_proper]
  by_cases top : RoleOf p = topObject <;> by_cases bottom : RoleOf p = bottomObject <;>
    simp [named_property_correct,builtin_role_correct,top,bottom]
private theorem rest_proper_correct (values : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) :
    alc_ontology.rest_proper values index =
      .ok (decide (∀ p ∈ values.val.drop index.val, RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject)) := by
  rw [alc_ontology.rest_proper]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := rest_proper_correct values next
    rw [nextIndex] at rest
    rw [split]
    by_cases here : RoleOf values.val[index.val] ≠ topObject ∧ RoleOf values.val[index.val] ≠ bottomObject
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,role_proper_correct,advance,rest,List.forall_mem_cons]
      rw [decide_eq_true here]
      simp only [↓reduceIte]
      congr 1
      exact decide_eq_decide.mpr ⟨fun later => ⟨here,later⟩,fun both => both.2⟩
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,role_proper_correct,List.forall_mem_cons]
      rw [decide_eq_false here]
      simp [here]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by values.val.length - index.val
decreasing_by omega
theorem members_proper_correct (members : AtLeastTwo ObjectPropertyExpression) :
    alc_ontology.members_proper members =
      .ok (decide (∀ p ∈ members.elements, RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject)) := by
  rw [alc_ontology.members_proper]
  have rest := rest_proper_correct members.rest 0#usize
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at rest
  by_cases first : RoleOf members.first ≠ topObject ∧ RoleOf members.first ≠ bottomObject
  · by_cases second : RoleOf members.second ≠ topObject ∧ RoleOf members.second ≠ bottomObject
    · simp only [role_proper_correct,bind_ok]
      rw [decide_eq_true first,decide_eq_true second]
      simp only [↓reduceIte,rest,AtLeastTwo.elements,List.forall_mem_cons]
      simp [first,second]
    · simp only [role_proper_correct,bind_ok]
      rw [decide_eq_true first,decide_eq_false second]
      simp only [↓reduceIte,Bool.false_eq_true,AtLeastTwo.elements,List.forall_mem_cons]
      simp [second]
  · simp only [role_proper_correct,bind_ok]
    rw [decide_eq_false first]
    simp only [↓reduceIte,Bool.false_eq_true,AtLeastTwo.elements,List.forall_mem_cons]
    simp [first]
theorem pair_proper_correct (sub sup : ObjectPropertyExpression) :
    alc_ontology.pair_proper sub sup = .ok (decide ((RoleOf sub ≠ topObject ∧ RoleOf sub ≠ bottomObject) ∧
      (RoleOf sup ≠ topObject ∧ RoleOf sup ≠ bottomObject))) := by
  rw [alc_ontology.pair_proper]
  by_cases first : RoleOf sub ≠ topObject ∧ RoleOf sub ≠ bottomObject
  · simp only [role_proper_correct,bind_ok]
    rw [decide_eq_true first]
    simp [first]
  · simp only [role_proper_correct,bind_ok]
    rw [decide_eq_false first]
    simp [first]
/-- The role check over the assertions is exact. -/
theorem roles_proper_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    alc_ontology.roles_proper items index = .ok (decide (∀ item ∈ items.val.drop index.val, RoleProper item.axiom)) := by
  rw [alc_ontology.roles_proper]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := roles_proper_correct items next
    rw [nextIndex] at rest
    rw [split]
    simp only [List.forall_mem_cons]
    cases item : items.val[index.val].axiom with
    | ObjectPropertyAssertion p a b =>
      by_cases top : RoleOf p = topObject
      · simp [more,lookup,item,named_property_correct,builtin_role_correct,top,RoleProper]
      · by_cases bottom : RoleOf p = bottomObject
        · simp [more,lookup,item,named_property_correct,builtin_role_correct,top,bottom,RoleProper]
        · simp [more,lookup,item,named_property_correct,builtin_role_correct,top,bottom,RoleProper,advance,rest]
    | NegativeObjectPropertyAssertion p a b =>
      by_cases top : RoleOf p = topObject
      · simp [more,lookup,item,named_property_correct,builtin_role_correct,top,RoleProper]
      · by_cases bottom : RoleOf p = bottomObject
        · simp [more,lookup,item,named_property_correct,builtin_role_correct,top,bottom,RoleProper]
        · simp [more,lookup,item,named_property_correct,builtin_role_correct,top,bottom,RoleProper,advance,rest]
    | SubObjectPropertyOf sub sup =>
      cases sub with
      | Single p =>
        by_cases both : (RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject) ∧
            (RoleOf sup ≠ topObject ∧ RoleOf sup ≠ bottomObject)
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
            bind_ok,item,pair_proper_correct]
          rw [decide_eq_true both]
          simp [RoleProper,both,advance,rest]
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
            bind_ok,item,pair_proper_correct]
          rw [decide_eq_false both]
          simp only [RoleProper]
          simp [both]
      | Chain c => simp [more,lookup,item,RoleProper,advance,rest]
    | EquivalentObjectProperties members =>
      by_cases all : ∀ p ∈ members.elements, RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject
      · have proper : RoleProper (.EquivalentObjectProperties members) := all
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,item,members_proper_correct]
        rw [decide_eq_true all]
        simp only [↓reduceIte,advance,rest,bind_ok]
        congr 1
        exact decide_eq_decide.mpr ⟨fun later => ⟨proper,later⟩,fun both => both.2⟩
      · have improper : ¬ RoleProper (.EquivalentObjectProperties members) := all
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,item,members_proper_correct]
        rw [decide_eq_false all]
        simp only [Bool.false_eq_true,↓reduceIte]
        rw [decide_eq_false (fun both => improper both.1)]
    | TransitiveObjectProperty p =>
      by_cases here : RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,item,role_proper_correct]
        rw [decide_eq_true here]
        simp [RoleProper,here,advance,rest]
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,item,role_proper_correct]
        rw [decide_eq_false here]
        simp only [RoleProper]
        simp [here]
    | _ => simp [more,lookup,item,RoleProper,advance,rest]
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [more,empty]
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- A negative object property assertion. -/
def Negative : Axiom → Prop
  | .NegativeObjectPropertyAssertion _ _ _ => True
  | _ => False
/-- The check for negative object property assertions is exact. -/
theorem has_negative_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    alc_ontology.has_negative items index = .ok (decide (∃ item ∈ items.val.drop index.val, Negative item.axiom)) := by
  rw [alc_ontology.has_negative]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := has_negative_correct items next
    rw [nextIndex] at rest
    have unfold : (∃ item ∈ items.val.drop index.val, Negative item.axiom) ↔
        Negative items.val[index.val].axiom ∨ ∃ item ∈ items.val.drop (index.val+1), Negative item.axiom := by
      rw [split]
      constructor
      · rintro ⟨item,member,negative⟩
        rcases List.mem_cons.mp member with rfl | later
        · exact .inl negative
        · exact .inr ⟨item,later,negative⟩
      · rintro (negative | ⟨item,later,negative⟩)
        · exact ⟨_,List.mem_cons_self ..,negative⟩
        · exact ⟨item,List.mem_cons_of_mem _ later,negative⟩
    simp only [unfold]
    cases item : items.val[index.val].axiom with
    | NegativeObjectPropertyAssertion p a b => simp [more,lookup,item,Negative]
    | _ => simp [more,lookup,item,Negative,advance,rest]
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [more,empty]
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- The facts of the placed concepts, before the given facts. -/
theorem facts_from_correct (placed : alloc.vec.Vec alc_ontology.Placed) (index : Usize) (facts : abox.Facts) :
    ∃ result, alc_ontology.facts_from placed index facts = .ok result ∧
      ∀ p, p ∈ factsList result ↔ p ∈ factsList facts ∨ ∃ q ∈ placed.val.drop index.val, p = (q.node.val,q.concept) := by
  rw [alc_ontology.facts_from]
  by_cases more : index.val < placed.val.length
  · have lookup : placed.index_usize index = .ok placed.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : placed.val.drop index.val = placed.val[index.val] :: placed.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨result,run,spec⟩ := facts_from_correct placed next
      (.Entry placed.val[index.val].node placed.val[index.val].concept facts)
    refine ⟨result,by simp [more,lookup,advance,run],?_⟩
    intro p
    rw [spec,split,nextIndex]
    simp only [factsList,List.mem_cons]
    constructor
    · rintro ((rfl | old) | ⟨q,member,rfl⟩)
      · exact .inr ⟨placed.val[index.val],.inl rfl,rfl⟩
      · exact .inl old
      · exact .inr ⟨q,.inr member,rfl⟩
    · rintro (old | ⟨q,(rfl | member),rfl⟩)
      · exact .inl (.inr old)
      · exact .inl (.inl rfl)
      · exact .inr ⟨q,member,rfl⟩
  · have empty : placed.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    exact ⟨facts,by simp [more],by simp [empty]⟩
termination_by placed.val.length - index.val
decreasing_by omega

/-- The edge of a positive object property assertion, oriented along its named
    property: the role, the source node and the target node. -/
noncomputable def EdgeOf (nodes : List Individual) : Axiom → Option (ObjectProperty × Nat × Nat)
  | .ObjectPropertyAssertion (.Property r) s t => some (r,PositionOf nodes s,PositionOf nodes t)
  | .ObjectPropertyAssertion (.Inverse r) s t => some (r,PositionOf nodes t,PositionOf nodes s)
  | _ => none
/-- The edge a negative object property assertion denies, oriented the same way. -/
noncomputable def DeniedOf (nodes : List Individual) : Axiom → Option (ObjectProperty × Nat × Nat)
  | .NegativeObjectPropertyAssertion (.Property r) s t => some (r,PositionOf nodes s,PositionOf nodes t)
  | .NegativeObjectPropertyAssertion (.Inverse r) s t => some (r,PositionOf nodes t,PositionOf nodes s)
  | _ => none

/-- The edges of the positive object property assertions, before the given edges. -/
theorem edges_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (index : Usize) (edges : abox.Edges) :
    ∃ result, alc_ontology.edges_from items nodes index edges = .ok result ∧
      ∀ e, e ∈ edgesList result ↔ e ∈ edgesList edges ∨
        ∃ item ∈ items.val.drop index.val, EdgeOf nodes.val item.axiom = some e := by
  rw [alc_ontology.edges_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have tail : ∀ (extended : abox.Edges), (∀ e, e ∈ edgesList extended ↔ e ∈ edgesList edges ∨
        EdgeOf nodes.val items.val[index.val].axiom = some e) →
        ∃ result, alc_ontology.edges_from items nodes next extended = .ok result ∧
          ∀ e, e ∈ edgesList result ↔ e ∈ edgesList edges ∨
            ∃ item ∈ items.val.drop index.val, EdgeOf nodes.val item.axiom = some e := by
      intro extended extendedSpec
      obtain ⟨result,run,spec⟩ := edges_from_correct items nodes next extended
      refine ⟨result,run,fun e => ?_⟩
      rw [spec,extendedSpec,split,nextIndex]
      simp only [List.mem_cons,exists_eq_or_imp]
      constructor
      · rintro ((old | here) | ⟨item,member,found⟩)
        · exact .inl old
        · exact .inr (.inl here)
        · exact .inr (.inr ⟨item,member,found⟩)
      · rintro (old | here | ⟨item,member,found⟩)
        · exact .inl (.inl old)
        · exact .inl (.inr here)
        · exact .inr ⟨item,member,found⟩
    cases item : items.val[index.val].axiom with
    | ObjectPropertyAssertion p a b =>
      obtain ⟨pa,paRun,paValue⟩ := position_of nodes a
      obtain ⟨pb,pbRun,pbValue⟩ := position_of nodes b
      cases p with
      | Property r =>
        obtain ⟨result,run,spec⟩ := tail (.Entry r pa pb edges) (by
          intro e
          simp [edgesList,item,EdgeOf,paValue,pbValue,or_comm,eq_comm])
        exact ⟨result,by simp [more,lookup,item,paRun,pbRun,advance,run],spec⟩
      | Inverse r =>
        obtain ⟨result,run,spec⟩ := tail (.Entry r pb pa edges) (by
          intro e
          simp [edgesList,item,EdgeOf,paValue,pbValue,or_comm,eq_comm])
        exact ⟨result,by simp [more,lookup,item,paRun,pbRun,advance,run],spec⟩
    | _ =>
      obtain ⟨result,run,spec⟩ := tail edges (by simp [item,EdgeOf])
      exact ⟨result,by simp [more,lookup,item,advance,run],spec⟩
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    exact ⟨edges,by simp [more],by simp [empty]⟩
termination_by items.val.length - index.val
decreasing_by omega

/-- Edge membership is decided exactly; the edges are handed back. -/
theorem has_edge_correct (edges : abox.Edges) (r : ObjectProperty) (source target : Usize) :
    alc_ontology.has_edge edges r source target = .ok (decide ((r,source.val,target.val) ∈ edgesList edges),edges) := by
  induction edges with
  | Empty => rw [alc_ontology.has_edge.eq_def]; simp [edgesList]
  | Entry other s t next ih =>
    rw [alc_ontology.has_edge.eq_def]
    by_cases fromHere : s = source
    · subst fromHere
      by_cases toHere : t = target
      · subst toHere
        by_cases same : other = r
        · subst same; simp [ih,edgesList,Rowl.Symbols.same_spelling_total_correct]
        · have different : ¬ other.iri.spelling.val = r.iri.spelling.val :=
            fun h => same ((Rowl.Tableau.property_eq_iff other r).mpr h)
          have same' : ¬ r = other := fun h => same h.symm
          simp [ih,edgesList,Rowl.Symbols.same_spelling_total_correct,different,same']
      · have different : ¬ target.val = t.val := fun h => toHere (UScalar.eq_of_val_eq h.symm)
        simp [ih,edgesList,toHere,different]
    · have different : ¬ source.val = s.val := fun h => fromHere (UScalar.eq_of_val_eq h.symm)
      simp [ih,edgesList,fromHere,different]

/-- The denial check is exact: some negative object property assertion denies
    an edge among the given edges; the edges are handed back. -/
theorem denied_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (index : Usize) (edges : abox.Edges) :
    ∃ denied, alc_ontology.denied_from items nodes index edges = .ok (denied,edges) ∧
      (denied = true ↔ ∃ item ∈ items.val.drop index.val, ∃ e, DeniedOf nodes.val item.axiom = some e ∧
        e ∈ edgesList edges) := by
  rw [alc_ontology.denied_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨later,laterRun,laterSpec⟩ := denied_from_correct items nodes next edges
    rw [nextIndex] at laterSpec
    have combine : ∀ here : Bool, (here = true ↔ ∃ e, DeniedOf nodes.val items.val[index.val].axiom = some e ∧
        e ∈ edgesList edges) → ((here || later) = true ↔ ∃ item ∈ items.val.drop index.val, ∃ e,
          DeniedOf nodes.val item.axiom = some e ∧ e ∈ edgesList edges) := by
      intro here hereSpec
      rw [Bool.or_eq_true,hereSpec,laterSpec,split]
      constructor
      · rintro (⟨e,found,member⟩ | ⟨item,inRest,e,found,member⟩)
        · exact ⟨items.val[index.val],List.mem_cons_self ..,e,found,member⟩
        · exact ⟨item,List.mem_cons_of_mem _ inRest,e,found,member⟩
      · rintro ⟨item,inList,e,found,member⟩
        rcases List.mem_cons.mp inList with rfl | inRest
        · exact .inl ⟨e,found,member⟩
        · exact .inr ⟨item,inRest,e,found,member⟩
    cases item : items.val[index.val].axiom with
    | NegativeObjectPropertyAssertion p a b =>
      obtain ⟨pa,paRun,paValue⟩ := position_of nodes a
      obtain ⟨pb,pbRun,pbValue⟩ := position_of nodes b
      cases p with
      | Property r =>
        refine ⟨decide ((r,pa.val,pb.val) ∈ edgesList edges) || later,?_,combine _ (by simp [item,DeniedOf,paValue,pbValue])⟩
        simp [more,lookup,item,paRun,pbRun,has_edge_correct,advance,laterRun]
        cases later <;> by_cases present : (r,pa.val,pb.val) ∈ edgesList edges <;> simp [present]
      | Inverse r =>
        refine ⟨decide ((r,pb.val,pa.val) ∈ edgesList edges) || later,?_,combine _ (by simp [item,DeniedOf,paValue,pbValue])⟩
        simp [more,lookup,item,paRun,pbRun,has_edge_correct,advance,laterRun]
        cases later <;> by_cases present : (r,pb.val,pa.val) ∈ edgesList edges <;> simp [present]
    | _ =>
      refine ⟨false || later,by simp [more,lookup,item,advance,laterRun],combine _ (by simp [item,DeniedOf])⟩
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    exact ⟨false,by simp [more],by simp [empty]⟩
termination_by items.val.length - index.val
decreasing_by omega

/-- A positive object property assertion holds exactly when its oriented edge
    relates the elements at its nodes. -/
theorem edge_meaning {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (nodes : List Individual) (f : Nat → Object) (statement : Axiom) (e : ObjectProperty × Nat × Nat)
    (edge : EdgeOf nodes statement = some e)
    (placedAt : ∀ a ∈ IndividualsOf statement, f (PositionOf nodes a) = Rowl.Owl.individual I a) :
    Rowl.Owl.satisfies I statement ↔ I.objectProperties e.1 (f e.2.1) (f e.2.2) := by
  cases statement with
  | ObjectPropertyAssertion p s t =>
    cases p with
    | Property r =>
      simp only [EdgeOf,Option.some.injEq] at edge
      subst edge
      simp only [IndividualsOf,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at placedAt
      simp [Rowl.Owl.satisfies,Rowl.Owl.objectRelation,placedAt.1,placedAt.2]
    | Inverse r =>
      simp only [EdgeOf,Option.some.injEq] at edge
      subst edge
      simp only [IndividualsOf,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at placedAt
      simp [Rowl.Owl.satisfies,Rowl.Owl.objectRelation,placedAt.1,placedAt.2]
  | _ => simp [EdgeOf] at edge
/-- A negative object property assertion holds exactly when its oriented edge
    does not relate the elements at its nodes. -/
theorem denied_meaning {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (nodes : List Individual) (f : Nat → Object) (statement : Axiom) (e : ObjectProperty × Nat × Nat)
    (edge : DeniedOf nodes statement = some e)
    (placedAt : ∀ a ∈ IndividualsOf statement, f (PositionOf nodes a) = Rowl.Owl.individual I a) :
    Rowl.Owl.satisfies I statement ↔ ¬ I.objectProperties e.1 (f e.2.1) (f e.2.2) := by
  cases statement with
  | NegativeObjectPropertyAssertion p s t =>
    cases p with
    | Property r =>
      simp only [DeniedOf,Option.some.injEq] at edge
      subst edge
      simp only [IndividualsOf,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at placedAt
      simp [Rowl.Owl.satisfies,Rowl.Owl.objectRelation,placedAt.1,placedAt.2]
    | Inverse r =>
      simp only [DeniedOf,Option.some.injEq] at edge
      subst edge
      simp only [IndividualsOf,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at placedAt
      simp [Rowl.Owl.satisfies,Rowl.Owl.objectRelation,placedAt.1,placedAt.2]
  | _ => simp [DeniedOf] at edge
theorem edge_individuals {nodes : List Individual} {statement : Axiom} {e : ObjectProperty × Nat × Nat}
    (edge : EdgeOf nodes statement = some e) : e.2.1 ≤ nodes.length ∧ e.2.2 ≤ nodes.length := by
  cases statement with
  | ObjectPropertyAssertion p s t =>
    cases p <;> simp only [EdgeOf,Option.some.injEq] at edge <;> subst edge <;>
      exact ⟨positionOf_le _ _,positionOf_le _ _⟩
  | _ => simp [EdgeOf] at edge
theorem denied_individuals {nodes : List Individual} {statement : Axiom} {e : ObjectProperty × Nat × Nat}
    (edge : DeniedOf nodes statement = some e) : e.2.1 ≤ nodes.length ∧ e.2.2 ≤ nodes.length := by
  cases statement with
  | NegativeObjectPropertyAssertion p s t =>
    cases p <;> simp only [DeniedOf,Option.some.injEq] at edge <;> subst edge <;>
      exact ⟨positionOf_le _ _,positionOf_le _ _⟩
  | _ => simp [DeniedOf] at edge
/-- Assertions are the axioms with individuals; every other axiom mentions none. -/
theorem assertion_of_individual {statement : Axiom} {a : Individual} (mentioned : a ∈ IndividualsOf statement) :
    Assertion statement := by
  cases statement <;> simp_all [IndividualsOf,Assertion]

/-- The closure is answerable: its internalization and placed concepts succeed,
    and every translated concept and asserted object property is proper. -/
def Answerable (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (extra : alloc.vec.Vec alc_ontology.Placed) : Prop :=
  ∃ axioms placed rb, alc_ontology.internalize items = .ok (some axioms) ∧
    alc_ontology.assertions_from items nodes 0#usize extra = .ok (some placed) ∧
    alc_ontology.role_box items = .ok (some rb) ∧
    Proper axioms ∧ (∀ q ∈ placed.val, Proper q.concept) ∧ (∀ item ∈ items.val, RoleProper item.axiom) ∧
    ((∃ item ∈ items.val, Negative item.axiom) → rb.inclusions.val = [] ∧ rb.transitive.val = [])

/-- Every node the facts and edges use is a node of the closure check. -/
private theorem nodes_below (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (extra placed : alloc.vec.Vec alc_ontology.Placed) (extraIn : ∀ q ∈ extra.val, q.node.val ≤ nodes.val.length)
    (origin : ∀ q ∈ placed.val, q ∈ extra.val ∨ ∃ item ∈ items.val.drop (0#usize).val, ∃ C m,
      item.axiom = .ClassAssertion C m ∧ q.node.val = PositionOf nodes.val m ∧ nnf.nnf C true = .ok (some q.concept)) :
    ∀ q ∈ placed.val, q.node.val ≤ nodes.val.length := by
  intro q member
  rcases origin q member with given | ⟨_,_,_,m,_,node,_⟩
  · exact extraIn q given
  · rw [node]; exact positionOf_le _ _

/-- Without listed inclusions or transitive properties, the edges and role
    axioms entail exactly the asserted edges. -/
theorem entailed_of_empty (rb : role_box.RoleBox) (noInclusions : rb.inclusions.val = [])
    (noTransitive : rb.transitive.val = []) (edges : List (ObjectProperty × Nat × Nat)) (r : ObjectProperty)
    (n m : Nat) (entailed : Entailed rb edges r n m) : (r,n,m) ∈ edges := by
  rcases entailed with ⟨s,below,edge⟩ | ⟨t,transitive,_,_⟩
  · rcases below with rfl | listed
    · exact edge
    · simp [inclusionList,noInclusions] at listed
  · simp [transitives,noTransitive] at transitive

/-- In the answerable case the closure check is the denial check followed by
    the completion over the placed facts, the asserted edges and the role box. -/
private theorem closure_answer (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (extra placed : alloc.vec.Vec alc_ontology.Placed) (axioms : nnf.NnfConcept) (rb : role_box.RoleBox)
    (room : nodes.val.length ≤ Usize.max-1)
    (internalRead : alc_ontology.internalize items = .ok (some axioms))
    (assertionsRun : alc_ontology.assertions_from items nodes 0#usize extra = .ok (some placed))
    (rolesRun : alc_ontology.role_box items = .ok (some rb))
    (properAxioms : Proper axioms) (properPlaced : ∀ q ∈ placed.val, Proper q.concept)
    (properRoles : ∀ item ∈ items.val, RoleProper item.axiom)
    (negativeOk : (∃ item ∈ items.val, Negative item.axiom) → rb.inclusions.val = [] ∧ rb.transitive.val = []) :
    ∃ (edges : abox.Edges) (denied : Bool) (count : Usize) (facts : abox.Facts),
      (∀ e, e ∈ edgesList edges ↔ ∃ item ∈ items.val, EdgeOf nodes.val item.axiom = some e) ∧
      (denied = true ↔ ∃ item ∈ items.val, ∃ e, DeniedOf nodes.val item.axiom = some e ∧ e ∈ edgesList edges) ∧
      count.val = nodes.val.length+1 ∧
      (∀ p, p ∈ factsList facts ↔ ∃ q ∈ placed.val, p = (q.node.val,q.concept)) ∧
      (denied = true → alc_ontology.closure_satisfiable items nodes extra = .ok (some false)) ∧
      (denied = false → ∀ b, abox.abox_satisfiable_with count facts edges axioms rb = .ok b →
        alc_ontology.closure_satisfiable items nodes extra = .ok (some b)) := by
  have zero : (0#usize).val = 0 := rfl
  have placedProper := placed_proper_correct placed 0#usize
  have rolesProper := roles_proper_correct items 0#usize
  have negativeCheck := has_negative_correct items 0#usize
  rw [zero,List.drop_zero] at placedProper rolesProper negativeCheck
  have checkAxioms : alc_ontology.proper axioms = .ok true := by rw [proper_correct,decide_eq_true properAxioms]
  have checkPlaced : alc_ontology.placed_proper placed 0#usize = .ok true := by
    rw [placedProper,decide_eq_true properPlaced]
  have checkRoles : alc_ontology.roles_proper items 0#usize = .ok true := by
    rw [rolesProper,decide_eq_true properRoles]
  obtain ⟨edges,edgesRun,edgesSpec⟩ := edges_from_correct items nodes 0#usize .Empty
  obtain ⟨denied,deniedRun,deniedSpec⟩ := denied_from_correct items nodes 0#usize edges
  obtain ⟨count,countRun,countValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := nodes.len) (y := 1#usize) (by have := room; scalar_tac))
  have countIs : count.val = nodes.val.length+1 := by simpa using countValue
  obtain ⟨facts,factsRun,factsSpec⟩ := facts_from_correct placed 0#usize .Empty
  -- The checks in front of the edges pass, whether or not there are negative assertions.
  have passes : ∀ (rest : Result (Option Bool)),
      alc_ontology.closure_satisfiable items nodes extra = rest ↔
        (do
          let edges ← alc_ontology.edges_from items nodes 0#usize abox.Edges.Empty
          let (denied,edges1) ← alc_ontology.denied_from items nodes 0#usize edges
          if denied then ok (some false)
          else
            let i ← alloc.vec.Vec.len nodes + 1#usize
            let f ← alc_ontology.facts_from placed 0#usize abox.Facts.Empty
            let b4 ← abox.abox_satisfiable_with i f edges1 axioms rb
            ok (some b4)) = rest := by
    intro rest
    rw [alc_ontology.closure_satisfiable]
    by_cases negative : ∃ item ∈ items.val, Negative item.axiom
    · obtain ⟨noInclusions,noTransitive⟩ := negativeOk negative
      have inclusionsLen : alloc.vec.Vec.len rb.inclusions = 0#usize := UScalar.eq_of_val_eq (by simp [noInclusions])
      have transitiveLen : alloc.vec.Vec.len rb.transitive = 0#usize := UScalar.eq_of_val_eq (by simp [noTransitive])
      have checkNegative : alc_ontology.has_negative items 0#usize = .ok true := by
        rw [negativeCheck,decide_eq_true negative]
      simp only [internalRead,assertionsRun,rolesRun,bind_ok,checkAxioms,checkPlaced,checkRoles,checkNegative,
        inclusionsLen,transitiveLen,↓reduceIte]
    · have checkNegative : alc_ontology.has_negative items 0#usize = .ok false := by
        rw [negativeCheck,decide_eq_false negative]
      simp only [internalRead,assertionsRun,rolesRun,bind_ok,checkAxioms,checkPlaced,checkRoles,checkNegative,
        Bool.false_eq_true,↓reduceIte]
  refine ⟨edges,denied,count,facts,?_,?_,countIs,?_,?_,?_⟩
  · intro e
    rw [edgesSpec,zero,List.drop_zero]
    simp [edgesList]
  · rw [deniedSpec,zero,List.drop_zero]
  · intro p
    rw [factsSpec,zero,List.drop_zero]
    simp [factsList]
  · intro deniedTrue
    subst deniedTrue
    rw [passes]
    simp [edgesRun,deniedRun]
  · intro deniedFalse b acceptedRun
    subst deniedFalse
    rw [passes]
    simp [edgesRun,deniedRun,countRun,factsRun,acceptedRun]

/-- The closure check terminates and answers exactly when the closure is answerable. -/
theorem closure_satisfiable_total (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (extra : alloc.vec.Vec alc_ontology.Placed) (room : nodes.val.length ≤ Usize.max-1)
    (extraIn : ∀ q ∈ extra.val, q.node.val ≤ nodes.val.length) :
    ∃ result, alc_ontology.closure_satisfiable items nodes extra = .ok result ∧
      (result.isSome ↔ Answerable items nodes extra) := by
  obtain ⟨internal,internalRead,_,_⟩ := internalize_correct.{0,0} items
  cases internal with
  | none =>
    refine ⟨none,by rw [alc_ontology.closure_satisfiable]; simp [internalRead],?_⟩
    simp [Answerable,internalRead]
  | some axioms =>
    obtain ⟨assertions,assertionsRun,assertionsSpec⟩ := assertions_from_correct items nodes 0#usize extra
    cases assertions with
    | none =>
      refine ⟨none,by rw [alc_ontology.closure_satisfiable]; simp [internalRead,assertionsRun],?_⟩
      simp [Answerable,internalRead,assertionsRun]
    | some placed =>
      obtain ⟨roles,rolesRun,_⟩ := role_box_correct.{0,0} items
      cases roles with
      | none =>
        refine ⟨none,by rw [alc_ontology.closure_satisfiable]; simp [internalRead,assertionsRun,rolesRun],?_⟩
        simp [Answerable,internalRead,assertionsRun,rolesRun]
      | some rb =>
        obtain ⟨origin,_,_⟩ := assertionsSpec placed rfl
        have zero : (0#usize).val = 0 := rfl
        have placedProper := placed_proper_correct placed 0#usize
        have rolesProper := roles_proper_correct items 0#usize
        have negativeCheck := has_negative_correct items 0#usize
        rw [zero,List.drop_zero] at placedProper rolesProper negativeCheck
        have unanswerable : ¬ (Proper axioms ∧ (∀ q ∈ placed.val, Proper q.concept) ∧
            (∀ item ∈ items.val, RoleProper item.axiom) ∧
            ((∃ item ∈ items.val, Negative item.axiom) → rb.inclusions.val = [] ∧ rb.transitive.val = [])) →
            ¬ Answerable items nodes extra := by
          rintro failed ⟨axioms',placed',rb',internalRead',assertionsRun',rolesRun',rest⟩
          rw [internalRead] at internalRead'
          rw [assertionsRun] at assertionsRun'
          rw [rolesRun] at rolesRun'
          cases Result.ok_injective internalRead'
          cases Result.ok_injective assertionsRun'
          cases Result.ok_injective rolesRun'
          exact failed rest
        by_cases properAxioms : Proper axioms
        · by_cases properPlaced : ∀ q ∈ placed.val, Proper q.concept
          · by_cases properRoles : ∀ item ∈ items.val, RoleProper item.axiom
            · by_cases negativeOk : (∃ item ∈ items.val, Negative item.axiom) →
                  rb.inclusions.val = [] ∧ rb.transitive.val = []
              · have answerable : Answerable items nodes extra :=
                  ⟨axioms,placed,rb,internalRead,assertionsRun,rolesRun,properAxioms,properPlaced,properRoles,negativeOk⟩
                obtain ⟨edges,denied,count,facts,edgesSpec,_,countIs,factsSpec,whenDenied,whenAllowed⟩ :=
                  closure_answer items nodes extra placed axioms rb room internalRead assertionsRun rolesRun
                    properAxioms properPlaced properRoles negativeOk
                cases denied with
                | true => exact ⟨some false,whenDenied rfl,by simpa using answerable⟩
                | false =>
                  have below := nodes_below items nodes extra placed extraIn (by simpa using origin)
                  obtain ⟨accepted,acceptedRun,_,_⟩ :=
                    abox_satisfiable_with_correct.{0,0} count (by omega) facts edges axioms rb
                      (by
                        intro p member
                        obtain ⟨q,qIn,rfl⟩ := (factsSpec p).mp member
                        have := below q qIn; simp only; omega)
                      (by
                        intro e member
                        obtain ⟨item,_,edge⟩ := (edgesSpec e).mp member
                        have := edge_individuals edge; omega)
                  exact ⟨some accepted,whenAllowed rfl accepted acceptedRun,by simpa using answerable⟩
              · refine ⟨none,?_,by simpa using unanswerable (fun ⟨_,_,_,ok⟩ => negativeOk ok)⟩
                obtain ⟨negative,nonempty⟩ : (∃ item ∈ items.val, Negative item.axiom) ∧
                    ¬ (rb.inclusions.val = [] ∧ rb.transitive.val = []) := by
                  by_contra contrary
                  apply negativeOk
                  intro negative
                  by_contra empty
                  exact contrary ⟨negative,empty⟩
                have checkNegative : alc_ontology.has_negative items 0#usize = .ok true := by
                  rw [negativeCheck,decide_eq_true negative]
                rw [alc_ontology.closure_satisfiable]
                simp only [internalRead,assertionsRun,rolesRun,bind_ok,proper_correct,decide_eq_true properAxioms,
                  placedProper,decide_eq_true properPlaced,rolesProper,decide_eq_true properRoles,checkNegative,
                  ↓reduceIte]
                by_cases noInclusions : rb.inclusions.val = []
                · have transitiveNonempty : rb.transitive.val ≠ [] := fun empty => nonempty ⟨noInclusions,empty⟩
                  have inclusionsLen : alloc.vec.Vec.len rb.inclusions = 0#usize :=
                    UScalar.eq_of_val_eq (by simp [noInclusions])
                  have transitiveLen : ¬ alloc.vec.Vec.len rb.transitive = 0#usize := by
                    intro same
                    have := congrArg UScalar.val same
                    simp at this
                    exact transitiveNonempty this
                  simp [inclusionsLen,transitiveLen]
                · have inclusionsLen : ¬ alloc.vec.Vec.len rb.inclusions = 0#usize := by
                    intro same
                    have := congrArg UScalar.val same
                    simp at this
                    exact noInclusions this
                  simp [inclusionsLen]
            · refine ⟨none,?_,by simpa using unanswerable (fun ⟨_,_,roles,_⟩ => properRoles roles)⟩
              rw [alc_ontology.closure_satisfiable]
              simp only [internalRead,assertionsRun,rolesRun,bind_ok,proper_correct,decide_eq_true properAxioms,
                placedProper,decide_eq_true properPlaced,rolesProper,decide_eq_false properRoles,Bool.false_eq_true,
                ↓reduceIte]
          · refine ⟨none,?_,by simpa using unanswerable (fun ⟨_,placedOk,_⟩ => properPlaced placedOk)⟩
            rw [alc_ontology.closure_satisfiable]
            simp only [internalRead,assertionsRun,rolesRun,bind_ok,proper_correct,decide_eq_true properAxioms,
              placedProper,decide_eq_false properPlaced,Bool.false_eq_true,↓reduceIte]
        · refine ⟨none,?_,by simpa using unanswerable (fun ⟨axiomsOk,_⟩ => properAxioms axiomsOk)⟩
          rw [alc_ontology.closure_satisfiable]
          simp only [internalRead,assertionsRun,rolesRun,bind_ok,proper_correct,decide_eq_false properAxioms,
            Bool.false_eq_true,↓reduceIte]

private theorem individual_owl_model {Object : Type} (J : Interpretation Object Unit) (root : Object)
    (place : Individual → Object) {Native : Type w} (D : DatatypeMap Native) (a : Individual) :
    Rowl.Owl.individual (owlModel.{u,v,w} J root place D) a = ULift.up (place a) := by
  cases a <;> rfl
private theorem with_own_anonymous {Object : Type u} {Value : Type v} (I : Interpretation Object Value) :
    withAnonymous I I.anonymousIndividuals = I := by
  cases I; rfl
private theorem edge_role {nodes : List Individual} {p : ObjectPropertyExpression} {s t : Individual}
    {e : ObjectProperty × Nat × Nat} (edge : EdgeOf nodes (.ObjectPropertyAssertion p s t) = some e) :
    e.1 = RoleOf p := by
  cases p <;> simp only [EdgeOf,Option.some.injEq] at edge <;> subst edge <;> rfl
private theorem denied_role {nodes : List Individual} {p : ObjectPropertyExpression} {s t : Individual}
    {e : ObjectProperty × Nat × Nat} (edge : DeniedOf nodes (.NegativeObjectPropertyAssertion p s t) = some e) :
    e.1 = RoleOf p := by
  cases p <;> simp only [DeniedOf,Option.some.injEq] at edge <;> subst edge <;> rfl
private theorem edge_exists (nodes : List Individual) (p : ObjectPropertyExpression) (s t : Individual) :
    ∃ e, EdgeOf nodes (.ObjectPropertyAssertion p s t) = some e := by
  cases p <;> exact ⟨_,rfl⟩
private theorem denied_exists (nodes : List Individual) (p : ObjectPropertyExpression) (s t : Individual) :
    ∃ e, DeniedOf nodes (.NegativeObjectPropertyAssertion p s t) = some e := by
  cases p <;> exact ⟨_,rfl⟩

/-- A role axiom without built-in properties that holds in the tableau model
    holds in its OWL interpretation, which reads every other property the same
    way. -/
private theorem owl_model_role_axiom {Object : Type} (J : Interpretation Object Unit) (root : Object)
    (place : Individual → Object) {Native : Type w} (D : DatatypeMap Native) (a : Axiom) (role : RoleAxiom a)
    (proper : RoleProper a) (holds : Rowl.Owl.satisfies J a) :
    Rowl.Owl.satisfies (owlModel.{u,v,w} J root place D) a := by
  have relation : ∀ r x y, r ≠ topObject → r ≠ bottomObject →
      ((owlModel.{u,v,w} J root place D).objectProperties r x y ↔ J.objectProperties r x.down y.down) := by
    intro r x y top bottom
    simp [owlModel,top,bottom]
  cases a with
  | SubObjectPropertyOf sub sup =>
    cases sub with
    | Single p =>
      cases p with
      | Property s =>
        cases sup with
        | Property r =>
          simp only [RoleProper,RoleOf] at proper
          simp only [Rowl.Owl.satisfies,Rowl.Owl.subRelation,Rowl.Owl.objectRelation] at holds ⊢
          intro x y edge
          exact (relation r x y proper.2.1 proper.2.2).mpr
            (holds x.down y.down ((relation s x y proper.1.1 proper.1.2).mp edge))
        | Inverse r => simp [RoleAxiom] at role
      | Inverse s => cases sup <;> simp [RoleAxiom] at role
    | Chain c => simp [RoleAxiom] at role
  | EquivalentObjectProperties members =>
    simp only [RoleAxiom] at role
    simp only [RoleProper] at proper
    simp only [Rowl.Owl.satisfies,Rowl.Owl.allEqual] at holds ⊢
    intro a aIn b bIn
    obtain ⟨p,rfl⟩ := role a aIn
    obtain ⟨q,rfl⟩ := role b bIn
    have pProper := proper _ aIn
    have qProper := proper _ bIn
    simp only [RoleOf] at pProper qProper
    have equal := holds _ aIn _ bIn
    simp only [Rowl.Owl.objectRelation] at equal ⊢
    funext x y
    rw [propext (relation p x y pProper.1 pProper.2),propext (relation q x y qProper.1 qProper.2),equal]
  | TransitiveObjectProperty p =>
    cases p with
    | Property r =>
      simp only [RoleProper,RoleOf] at proper
      simp only [Rowl.Owl.satisfies,Rowl.Owl.objectRelation] at holds ⊢
      intro x y z first second
      exact (relation r x z proper.1 proper.2).mpr (holds x.down y.down z.down
        ((relation r x y proper.1 proper.2).mp first) ((relation r y z proper.1 proper.2).mp second))
    | Inverse r => simp [RoleAxiom] at role
  | _ => simp [RoleAxiom] at role

/-- An accepting closure check yields an OWL model of the closure in which every
    individual sits at the element of its node and every extra concept holds at
    the element of its node. -/
theorem closure_satisfiable_sound (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (extra : alloc.vec.Vec alc_ontology.Placed) (room : nodes.val.length ≤ Usize.max-1)
    (extraIn : ∀ q ∈ extra.val, q.node.val ≤ nodes.val.length)
    (accepted : alc_ontology.closure_satisfiable items nodes extra = .ok (some true))
    {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary) (vocabulary : IsVocabulary D V) :
    ∃ (Object : Type u) (I : Interpretation Object (ULift.{v} (Option Native))) (f : Nat → Object),
      Model D (embedding.{v,w} D) V I items.val ∧ (∀ a, Rowl.Owl.individual I a = f (PositionOf nodes.val a)) ∧
      ∀ q ∈ extra.val, conceptDenote I q.concept (f q.node.val) := by
  obtain ⟨result,run,answerIff⟩ := closure_satisfiable_total items nodes extra room extraIn
  rw [accepted] at run
  cases Result.ok_injective run
  obtain ⟨axioms,placed,rb,internalRead,assertionsRun,rolesRun,properAxioms,properPlaced,properRoles,negativeOk⟩ :=
    answerIff.mp rfl
  obtain ⟨assertions,assertionsExecuted,assertionsSpec⟩ := assertions_from_correct items nodes 0#usize extra
  rw [assertionsRun] at assertionsExecuted
  cases Result.ok_injective assertionsExecuted
  obtain ⟨origin,kept,covered⟩ := assertionsSpec placed rfl
  have below := nodes_below items nodes extra placed extraIn origin
  obtain ⟨roleResult,roleRun,roleSpec⟩ := role_box_correct.{0,0} items
  rw [rolesRun] at roleRun
  cases Result.ok_injective roleRun
  obtain ⟨closed,respectsIff⟩ := roleSpec rb rfl
  obtain ⟨edges,denied,count,facts,edgesSpec,deniedSpec,countIs,factsSpec,whenDenied,whenAllowed⟩ :=
    closure_answer items nodes extra placed axioms rb room internalRead assertionsRun rolesRun properAxioms properPlaced
      properRoles negativeOk
  cases denied with
  | true =>
    rw [whenDenied rfl] at accepted
    cases Result.ok_injective accepted
  | false =>
    obtain ⟨answer,answerRun,sound,_⟩ := abox_satisfiable_with_correct.{0,0} count (by omega) facts edges axioms rb
      (by
        intro p member
        obtain ⟨q,qIn,rfl⟩ := (factsSpec p).mp member
        have := below q qIn; simp only; omega)
      (by
        intro e member
        obtain ⟨item,_,edge⟩ := (edgesSpec e).mp member
        have := edge_individuals edge; omega)
    rw [whenAllowed rfl answer answerRun] at accepted
    have answerTrue : answer = true := by simpa using Result.ok_injective accepted
    obtain ⟨Obj,J,f,⟨respects,model⟩,entailed⟩ := sound answerTrue closed
    have rolesHold := (respectsIff Obj Unit J).mp respects
    let place := fun a => f (PositionOf nodes.val a)
    have valid := owl_model_valid.{u,v,w} J (f 0) place D V
    have fixes := fixes_of_interpretation valid
    have agrees := owl_model_agrees.{u,v,w} J (f 0) place D
    have individualAt := individual_owl_model.{u,v,w} J (f 0) place D
    have relation : ∀ r x y, r ≠ topObject → r ≠ bottomObject →
        ((owlModel.{u,v,w} J (f 0) place D).objectProperties r x y ↔ J.objectProperties r x.down y.down) := by
      intro r x y top bottom
      simp [owlModel,top,bottom]
    obtain ⟨internal,internalExecuted,_,meaning⟩ := internalize_correct.{u, max w v} items
    rw [internalRead] at internalExecuted
    cases Result.ok_injective internalExecuted
    have tbox := (meaning axioms rfl _ _ (owlModel.{u,v,w} J (f 0) place D) fixes).mpr
      (fun x => (agrees axioms properAxioms x).mpr (model.1 x.down))
    have placedAt : ∀ (statement : Axiom), ∀ a ∈ IndividualsOf statement,
        (fun n => ULift.up (f n)) (PositionOf nodes.val a) =
          Rowl.Owl.individual (owlModel.{u,v,w} J (f 0) place D) a := by
      intro statement a _
      rw [individualAt]
    refine ⟨ULift.{u} Obj,owlModel.{u,v,w} J (f 0) place D,fun n => ULift.up (f n),
      ⟨vocabulary,valid,(owlModel.{u,v,w} J (f 0) place D).anonymousIndividuals,?_⟩,fun a => individualAt a,?_⟩
    · rw [with_own_anonymous]
      intro item member
      by_cases assertion : Assertion item.axiom
      · cases statement : item.axiom with
        | ClassAssertion C m =>
          obtain ⟨q,qIn,qNode,qRead⟩ := covered item (by simpa using member) C m statement
          have holds := model.2.1 (q.node.val,q.concept) ((factsSpec _).mpr ⟨q,qIn,rfl⟩)
          have lifted := (agrees q.concept (properPlaced q qIn) (ULift.up (f q.node.val))).mpr holds
          have meaningOf := (nnf_meaning C true q.concept qRead _ fixes (ULift.up (f q.node.val))).mp lifted
          simp only [Rowl.Owl.satisfies,individualAt,place]
          rw [← qNode]
          exact meaningOf
        | ObjectPropertyAssertion p a b =>
          obtain ⟨e,edge⟩ := edge_exists nodes.val p a b
          have inEdges := (edgesSpec e).mpr ⟨item,member,by rw [statement]; exact edge⟩
          have holds := model.2.2 e inEdges
          have role := edge_role edge
          have proper := properRoles item member
          rw [statement] at proper
          simp only [RoleProper] at proper
          rw [← role] at proper
          apply (edge_meaning _ nodes.val (fun n => ULift.up (f n)) _ e edge (placedAt _)).mpr
          exact (relation e.1 _ _ proper.1 proper.2).mpr holds
        | NegativeObjectPropertyAssertion p a b =>
          obtain ⟨e,edge⟩ := denied_exists nodes.val p a b
          have role := denied_role edge
          have proper := properRoles item member
          rw [statement] at proper
          simp only [RoleProper] at proper
          rw [← role] at proper
          obtain ⟨noInclusions,noTransitive⟩ := negativeOk ⟨item,member,by rw [statement]; trivial⟩
          apply (denied_meaning _ nodes.val (fun n => ULift.up (f n)) _ e edge (placedAt _)).mpr
          intro related
          have inJ := (relation e.1 _ _ proper.1 proper.2).mp related
          have bounds := denied_individuals edge
          have inEdges := entailed_of_empty rb noInclusions noTransitive _ e.1 e.2.1 e.2.2
            (entailed e.1 e.2.1 e.2.2 (by omega) (by omega) inJ)
          have deniedTrue := deniedSpec.mpr ⟨item,member,e,by rw [statement]; exact edge,inEdges⟩
          cases deniedTrue
        | _ => simp [statement,Assertion] at assertion
      · by_cases role : RoleAxiom item.axiom
        · exact owl_model_role_axiom J (f 0) place D item.axiom role (properRoles item member)
            (rolesHold item member role)
        · exact ((tbox item member).resolve_left assertion).resolve_left role
    · intro q member
      have holds := model.2.1 (q.node.val,q.concept) ((factsSpec _).mpr ⟨q,kept q member,rfl⟩)
      exact (agrees q.concept (properPlaced q (kept q member)) (ULift.up (f q.node.val))).mpr holds

/-- Any OWL model of the closure, in any universes, with an element for every
    node at which its individual sits and at which the extra concepts hold, makes
    the closure check accept. -/
theorem closure_satisfiable_complete (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (extra : alloc.vec.Vec alc_ontology.Placed) (room : nodes.val.length ≤ Usize.max-1)
    (extraIn : ∀ q ∈ extra.val, q.node.val ≤ nodes.val.length)
    (mentioned : ∀ item ∈ items.val, ∀ a ∈ IndividualsOf item.axiom, a ∈ nodes.val) (answer : Bool)
    (answered : alc_ontology.closure_satisfiable items nodes extra = .ok (some answer))
    {Native : Type w} {D : DatatypeMap Native} {V : Vocabulary} {Object : Type u} {Value : Type v}
    {embed : ValueEmbedding D Value} {I : Interpretation Object Value} (valid : IsInterpretation D embed V I)
    (g : AnonymousIndividual → Object) (satisfied : Rowl.Owl.satisfiesClosure (withAnonymous I g) items.val)
    (f : Nat → Object)
    (placedAt : ∀ a ∈ nodes.val, f (PositionOf nodes.val a) = Rowl.Owl.individual (withAnonymous I g) a)
    (extraHolds : ∀ q ∈ extra.val, conceptDenote (withAnonymous I g) q.concept (f q.node.val)) : answer = true := by
  obtain ⟨result,run,answerIff⟩ := closure_satisfiable_total items nodes extra room extraIn
  rw [answered] at run
  cases Result.ok_injective run
  obtain ⟨axioms,placed,rb,internalRead,assertionsRun,rolesRun,properAxioms,properPlaced,properRoles,negativeOk⟩ :=
    answerIff.mp rfl
  obtain ⟨assertions,assertionsExecuted,assertionsSpec⟩ := assertions_from_correct items nodes 0#usize extra
  rw [assertionsRun] at assertionsExecuted
  cases Result.ok_injective assertionsExecuted
  obtain ⟨origin,_,_⟩ := assertionsSpec placed rfl
  have below := nodes_below items nodes extra placed extraIn origin
  obtain ⟨roleResult,roleRun,roleSpec⟩ := role_box_correct.{u,v} items
  rw [rolesRun] at roleRun
  cases Result.ok_injective roleRun
  obtain ⟨_,respectsIff⟩ := roleSpec rb rfl
  obtain ⟨edges,denied,count,facts,edgesSpec,deniedSpec,countIs,factsSpec,whenDenied,whenAllowed⟩ :=
    closure_answer items nodes extra placed axioms rb room internalRead assertionsRun rolesRun properAxioms properPlaced
      properRoles negativeOk
  have fixes : Fixes (withAnonymous I g) := fixes_of_interpretation valid
  have mentionedAt : ∀ item ∈ items.val, ∀ a ∈ IndividualsOf item.axiom,
      f (PositionOf nodes.val a) = Rowl.Owl.individual (withAnonymous I g) a :=
    fun item member a inItem => placedAt a (mentioned item member a inItem)
  have edgeHolds : ∀ e ∈ edgesList edges, (withAnonymous I g).objectProperties e.1 (f e.2.1) (f e.2.2) := by
    intro e member
    obtain ⟨item,itemIn,edge⟩ := (edgesSpec e).mp member
    exact (edge_meaning _ nodes.val f _ e edge (mentionedAt item itemIn)).mp (satisfied item itemIn)
  cases denied with
  | true =>
    obtain ⟨item,itemIn,e,edge,inEdges⟩ := deniedSpec.mp rfl
    exact absurd (edgeHolds e inEdges)
      ((denied_meaning _ nodes.val f _ e edge (mentionedAt item itemIn)).mp (satisfied item itemIn))
  | false =>
    obtain ⟨accepted,acceptedRun,_,complete⟩ :=
      abox_satisfiable_with_correct.{u,v} count (by omega) facts edges axioms rb
        (by
          intro p member
          obtain ⟨q,qIn,rfl⟩ := (factsSpec p).mp member
          have := below q qIn; simp only; omega)
        (by
          intro e member
          obtain ⟨item,_,edge⟩ := (edgesSpec e).mp member
          have := edge_individuals edge; omega)
    rw [whenAllowed rfl accepted acceptedRun] at answered
    have same : accepted = answer := by simpa using Result.ok_injective answered
    rw [← same]
    apply complete
    obtain ⟨internal,internalExecuted,_,meaning⟩ := internalize_correct.{u,v} items
    rw [internalRead] at internalExecuted
    cases Result.ok_injective internalExecuted
    refine ⟨Object,Value,withAnonymous I g,f,
      (respectsIff Object Value (withAnonymous I g)).mpr (fun item member _ => satisfied item member),?_,?_,edgeHolds⟩
    · exact (meaning axioms rfl _ _ _ fixes).mp (fun item member => .inr (.inr (satisfied item member)))
    · intro p member
      obtain ⟨q,qIn,rfl⟩ := (factsSpec p).mp member
      rcases origin q qIn with given | ⟨item,itemIn,C,m,statement,qNode,qRead⟩
      · exact extraHolds q given
      · have itemIn' : item ∈ items.val := by simpa using itemIn
        have holds := satisfied item itemIn'
        rw [statement] at holds
        have at_m := mentionedAt item itemIn' m (by simp [statement,IndividualsOf])
        simp only [Rowl.Owl.satisfies] at holds
        rw [← at_m,← qNode] at holds
        exact (nnf_meaning C true q.concept qRead _ fixes _).mpr holds

/-- The nodes of the closure: every individual an assertion mentions, with room
    for one more node. -/
private theorem nodes_of (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, alc_ontology.individuals_from items 0#usize (alloc.vec.Vec.new Individual) = .ok result ∧
      ∀ nodes, result = some nodes →
        (∀ item ∈ items.val, ∀ a ∈ IndividualsOf item.axiom, a ∈ nodes.val) ∧ nodes.val.length ≤ Usize.max-1 := by
  obtain ⟨result,run,spec⟩ := individuals_from_correct items 0#usize (alloc.vec.Vec.new Individual) (by simp)
  refine ⟨result,run,fun nodes same => ?_⟩
  obtain ⟨_,mentioned,room⟩ := spec nodes same
  exact ⟨by simpa using mentioned,room⟩

/-- An element for every node: node `i + 1` holds the element of the individual
    `nodes[i]`, and node 0 holds `x`. -/
noncomputable def Placement {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (nodes : List Individual) (x : Object) (n : Nat) : Object :=
  if h : 0 < n ∧ n-1 < nodes.length then Rowl.Owl.individual I nodes[n-1] else x
theorem placement_zero {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (nodes : List Individual) (x : Object) : Placement I nodes x 0 = x := by
  simp [Placement]
theorem placement_at {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (nodes : List Individual) (x : Object) (a : Individual) (present : a ∈ nodes) :
    Placement I nodes x (PositionOf nodes a) = Rowl.Owl.individual I a := by
  obtain ⟨bound,positive,at_a⟩ := positionOf_present nodes a present
  simp only [Placement,positive,bound,and_self,↓reduceDIte,at_a]
/-- A translated expression means the same with any reinterpretation of the
    anonymous individuals. -/
theorem translated_meaning {Object : Type u} {Value : Type v} {I : Interpretation Object Value} (fixes : Fixes I)
    (g : AnonymousIndividual → Object) (e : ClassExpression) (positive : Bool) (concept : nnf.NnfConcept)
    (read : nnf.nnf e positive = .ok (some concept)) (x : Object) :
    conceptDenote (withAnonymous I g) concept x ↔ Polar positive (classDenote I e x) :=
  (concept_with_anonymous I g concept x).trans (nnf_meaning e positive concept read I fixes x)
private theorem single_placed (concept : nnf.NnfConcept) (node : Usize) :
    ∃ extra, alloc.vec.Vec.push (alloc.vec.Vec.new alc_ontology.Placed) ⟨node,concept⟩ = .ok extra ∧
      extra.val = [⟨node,concept⟩] := by
  obtain ⟨extra,run,value⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new alc_ontology.Placed) ⟨node,concept⟩ (by simp; scalar_tac))
  exact ⟨extra,run,by simpa using value⟩

/-- Consistency of an ALC axiom closure with assertions: the kernel answers
    exactly when the closure is answerable, and then the answer is whether the
    closure has an OWL model. -/
theorem consistent_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, alc_ontology.consistent items = .ok result ∧
      (result.isSome ↔ ∃ nodes, alc_ontology.individuals_from items 0#usize (alloc.vec.Vec.new Individual) =
        .ok (some nodes) ∧ Answerable items nodes (alloc.vec.Vec.new alc_ontology.Placed)) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ Consistent.{u, max w v, w} D V items.val) := by
  obtain ⟨individuals,individualsRun,individualsSpec⟩ := nodes_of items
  rw [alc_ontology.consistent]
  cases individuals with
  | none => exact ⟨none,by simp [individualsRun],by simp [individualsRun],by simp⟩
  | some nodes =>
    obtain ⟨mentioned,room⟩ := individualsSpec nodes rfl
    obtain ⟨result,run,answerIff⟩ := closure_satisfiable_total items nodes (alloc.vec.Vec.new _) room (by simp)
    refine ⟨result,by simp [individualsRun,run],by simp [individualsRun,answerIff],?_⟩
    intro answer same Native D V vocabulary
    subst same
    constructor
    · intro yes
      subst yes
      obtain ⟨Object,I,f,model,_,_⟩ := closure_satisfiable_sound.{u,v,w} items nodes _ room (by simp) run D V vocabulary
      exact ⟨Object,_,_,I,model⟩
    · rintro ⟨Object,Value,embed,I,_,valid,g,satisfied⟩
      obtain ⟨x⟩ := I.objectsNonempty
      exact closure_satisfiable_complete.{u, max w v, w} items nodes _ room (by simp) mentioned answer run valid g
        satisfied (Placement (withAnonymous I g) nodes.val x)
        (fun a present => placement_at _ nodes.val x a present) (by simp)

/-- Class satisfiability with respect to an ALC axiom closure with assertions:
    the kernel answers exactly when the expression translates and the closure
    with the expression at a further node is answerable, and then the answer is
    whether some OWL model of the closure has an instance of the expression. -/
theorem class_satisfiable_correct (items : alloc.vec.Vec AnnotatedAxiom) (e : ClassExpression) :
    ∃ result, alc_ontology.class_satisfiable items e = .ok result ∧
      (result.isSome ↔ ∃ concept nodes extra, nnf.nnf e true = .ok (some concept) ∧
        alc_ontology.individuals_from items 0#usize (alloc.vec.Vec.new Individual) = .ok (some nodes) ∧
        extra.val = [⟨0#usize,concept⟩] ∧ Answerable items nodes extra) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ ClassSatisfiable.{u, max w v, w} D V items.val e) := by
  obtain ⟨translated,translatedRead,_⟩ := nnf_total_correct.{0,0} e true
  rw [alc_ontology.class_satisfiable]
  cases translated with
  | none => exact ⟨none,by simp [translatedRead],by simp [translatedRead],by simp⟩
  | some concept =>
    obtain ⟨individuals,individualsRun,individualsSpec⟩ := nodes_of items
    cases individuals with
    | none => exact ⟨none,by simp [translatedRead,individualsRun],by simp [translatedRead,individualsRun],by simp⟩
    | some nodes =>
      obtain ⟨mentioned,room⟩ := individualsSpec nodes rfl
      obtain ⟨extra,extraRun,extraValue⟩ := single_placed concept 0#usize
      have extraIn : ∀ q ∈ extra.val, q.node.val ≤ nodes.val.length := by simp [extraValue]
      obtain ⟨result,run,answerIff⟩ := closure_satisfiable_total items nodes extra room extraIn
      refine ⟨result,by simp [translatedRead,individualsRun,extraRun,run],?_,?_⟩
      · rw [answerIff]
        constructor
        · intro answerable; exact ⟨concept,nodes,extra,translatedRead,individualsRun,extraValue,answerable⟩
        · rintro ⟨concept',nodes',extra',translated',individuals',extraValue',answerable⟩
          rw [translatedRead] at translated'
          cases Result.ok_injective translated'
          rw [individualsRun] at individuals'
          cases Result.ok_injective individuals'
          have same : extra' = extra := alloc.vec.Vec.eq_iff extra' extra |>.mpr (by rw [extraValue,extraValue'])
          rw [← same]
          exact answerable
      · intro answer same Native D V vocabulary
        subst same
        constructor
        · intro yes
          subst yes
          obtain ⟨Object,I,f,model,_,holds⟩ := closure_satisfiable_sound.{u,v,w} items nodes extra room extraIn run D V
            vocabulary
          have fixes := fixes_of_interpretation model.2.1
          have member := holds ⟨0#usize,concept⟩ (by simp [extraValue])
          exact ⟨Object,_,_,I,model,f 0,(nnf_meaning e true concept translatedRead I fixes (f 0)).mp member⟩
        · rintro ⟨Object,Value,embed,I,⟨_,valid,g,satisfied⟩,x,member⟩
          have fixes := fixes_of_interpretation valid
          exact closure_satisfiable_complete.{u, max w v, w} items nodes extra room extraIn mentioned answer run valid g
            satisfied (Placement (withAnonymous I g) nodes.val x)
            (fun a present => placement_at _ nodes.val x a present)
            (by
              intro q qIn
              simp only [extraValue,List.mem_singleton] at qIn
              subst qIn
              simp only [placement_zero]
              exact (translated_meaning fixes g e true concept translatedRead x).mpr member)

private theorem pair_placed (first second : nnf.NnfConcept) :
    ∃ one extra, alloc.vec.Vec.push (alloc.vec.Vec.new alc_ontology.Placed) ⟨0#usize,first⟩ = .ok one ∧
      alloc.vec.Vec.push one ⟨0#usize,second⟩ = .ok extra ∧ extra.val = [⟨0#usize,first⟩,⟨0#usize,second⟩] := by
  obtain ⟨one,oneRun,oneValue⟩ := single_placed first 0#usize
  obtain ⟨two,twoRun,twoValue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec one ⟨0#usize,second⟩ (by rw [oneValue]; simp; scalar_tac))
  exact ⟨one,two,oneRun,twoRun,by rw [twoValue,oneValue]; rfl⟩

/-- Subsumption with respect to an ALC axiom closure with assertions: the kernel
    answers exactly when both expressions translate and the closure with both at
    a further node is answerable, and then the answer is whether every instance of
    `sub` is an instance of `sup` in every OWL model of the closure. -/
theorem subsumed_correct (items : alloc.vec.Vec AnnotatedAxiom) (sub sup : ClassExpression) :
    ∃ result, alc_ontology.subsumed items sub sup = .ok result ∧
      (result.isSome ↔ ∃ inside outside nodes extra, nnf.nnf sub true = .ok (some inside) ∧
        nnf.nnf sup false = .ok (some outside) ∧
        alc_ontology.individuals_from items 0#usize (alloc.vec.Vec.new Individual) = .ok (some nodes) ∧
        extra.val = [⟨0#usize,inside⟩,⟨0#usize,outside⟩] ∧ Answerable items nodes extra) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ Subsumed.{u, max w v, w} D V items.val sub sup) := by
  obtain ⟨insideResult,insideRead,_⟩ := nnf_total_correct.{0,0} sub true
  obtain ⟨outsideResult,outsideRead,_⟩ := nnf_total_correct.{0,0} sup false
  rw [alc_ontology.subsumed]
  cases insideResult with
  | none => exact ⟨none,by simp [insideRead],by simp [insideRead],by simp⟩
  | some inside =>
    cases outsideResult with
    | none => exact ⟨none,by simp [insideRead,outsideRead],by simp [insideRead,outsideRead],by simp⟩
    | some outside =>
      obtain ⟨individuals,individualsRun,individualsSpec⟩ := nodes_of items
      cases individuals with
      | none =>
        exact ⟨none,by simp [insideRead,outsideRead,individualsRun],by simp [insideRead,outsideRead,individualsRun],
          by simp⟩
      | some nodes =>
        obtain ⟨mentioned,room⟩ := individualsSpec nodes rfl
        obtain ⟨one,extra,oneRun,extraRun,extraValue⟩ := pair_placed inside outside
        have extraIn : ∀ q ∈ extra.val, q.node.val ≤ nodes.val.length := by
          intro q member; rw [extraValue] at member; simp at member; rcases member with rfl | rfl <;> simp
        obtain ⟨result,run,answerIff⟩ := closure_satisfiable_total items nodes extra room extraIn
        refine ⟨result.map (fun satisfiable => decide ¬ satisfiable = true),?_,?_,?_⟩
        · simp only [insideRead,outsideRead,individualsRun,bind_ok,oneRun,extraRun,run]
          cases result <;> rfl
        · rw [Option.isSome_map,answerIff]
          constructor
          · intro answerable
            exact ⟨inside,outside,nodes,extra,insideRead,outsideRead,individualsRun,extraValue,answerable⟩
          · rintro ⟨inside',outside',nodes',extra',insideRead',outsideRead',individuals',extraValue',answerable⟩
            rw [insideRead] at insideRead'
            cases Result.ok_injective insideRead'
            rw [outsideRead] at outsideRead'
            cases Result.ok_injective outsideRead'
            rw [individualsRun] at individuals'
            cases Result.ok_injective individuals'
            have same : extra' = extra := alloc.vec.Vec.eq_iff extra' extra |>.mpr (by rw [extraValue,extraValue'])
            rw [← same]
            exact answerable
        · intro answer same Native D V vocabulary
          cases result with
          | none => cases same
          | some satisfiable =>
            simp only [Option.map_some,Option.some.injEq] at same
            subst same
            constructor
            · intro yes Object Value embed I model x member
              obtain ⟨_,valid,g,satisfied⟩ := model
              have fixes := fixes_of_interpretation valid
              by_contra outsideSup
              have accepted := closure_satisfiable_complete.{u, max w v, w} items nodes extra room extraIn mentioned
                satisfiable run valid g satisfied (Placement (withAnonymous I g) nodes.val x)
                (fun a present => placement_at _ nodes.val x a present)
                (by
                  intro q qIn
                  rw [extraValue] at qIn
                  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at qIn
                  rcases qIn with rfl | rfl
                  · simp only [placement_zero]
                    exact (translated_meaning fixes g sub true inside insideRead x).mpr member
                  · simp only [placement_zero]
                    exact (translated_meaning fixes g sup false outside outsideRead x).mpr outsideSup)
              simp [accepted] at yes
            · intro subsumed
              cases satisfiable with
              | false => rfl
              | true =>
                exfalso
                obtain ⟨Object,I,f,model,_,holds⟩ := closure_satisfiable_sound.{u,v,w} items nodes extra room extraIn run
                  D V vocabulary
                have fixes := fixes_of_interpretation model.2.1
                have inSub := (nnf_meaning sub true inside insideRead I fixes (f 0)).mp
                  (holds ⟨0#usize,inside⟩ (by simp [extraValue]))
                have notSup := (nnf_meaning sup false outside outsideRead I fixes (f 0)).mp
                  (holds ⟨0#usize,outside⟩ (by simp [extraValue]))
                exact notSup (subsumed _ _ _ _ model _ inSub)

/-- Instance checking with respect to an ALC axiom closure with assertions: the
    kernel answers exactly when the expression's complement translates and the
    closure with it at the individual's node is answerable, and then the answer is
    whether the named individual is an instance of the expression in every OWL
    model of the closure. -/
theorem instance_of_correct (items : alloc.vec.Vec AnnotatedAxiom) (a : NamedIndividual) (e : ClassExpression) :
    ∃ result, alc_ontology.instance_of items a e = .ok result ∧
      (result.isSome ↔ ∃ (outside : nnf.NnfConcept) (nodes : alloc.vec.Vec Individual)
        (extra : alloc.vec.Vec alc_ontology.Placed) (node : Usize), nnf.nnf e false = .ok (some outside) ∧
        alc_ontology.individuals_from items 0#usize (alloc.vec.Vec.new Individual) = .ok (some nodes) ∧
        node.val = PositionOf nodes.val (.Named a) ∧ extra.val = [⟨node,outside⟩] ∧ Answerable items nodes extra) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ InstanceOf.{u, max w v, w} D V items.val a e) := by
  obtain ⟨translated,translatedRead,_⟩ := nnf_total_correct.{0,0} e false
  rw [alc_ontology.instance_of]
  cases translated with
  | none => exact ⟨none,by simp [translatedRead],by simp [translatedRead],by simp⟩
  | some outside =>
    obtain ⟨individuals,individualsRun,individualsSpec⟩ := nodes_of items
    cases individuals with
    | none => exact ⟨none,by simp [translatedRead,individualsRun],by simp [translatedRead,individualsRun],by simp⟩
    | some nodes =>
      obtain ⟨mentioned,room⟩ := individualsSpec nodes rfl
      obtain ⟨node,nodeRun,nodeValue⟩ := position_of nodes (.Named a)
      have named : (Individual.Named { iri := a.iri } : Individual) = .Named a := by cases a; rfl
      obtain ⟨extra,extraRun,extraValue⟩ := single_placed outside node
      have extraIn : ∀ q ∈ extra.val, q.node.val ≤ nodes.val.length := by
        intro q member
        rw [extraValue,List.mem_singleton] at member
        subst member
        rw [nodeValue]
        exact positionOf_le _ _
      obtain ⟨result,run,answerIff⟩ := closure_satisfiable_total items nodes extra room extraIn
      refine ⟨result.map (fun satisfiable => decide ¬ satisfiable = true),?_,?_,?_⟩
      · simp only [translatedRead,individualsRun,bind_ok,Rowl.Nnf.copy_iri_identity,named,nodeRun,extraRun,run]
        cases result <;> rfl
      · rw [Option.isSome_map,answerIff]
        constructor
        · intro answerable
          exact ⟨outside,nodes,extra,node,translatedRead,individualsRun,nodeValue,extraValue,answerable⟩
        · rintro ⟨outside',nodes',extra',node',translated',individuals',nodeValue',extraValue',answerable⟩
          rw [translatedRead] at translated'
          cases Result.ok_injective translated'
          rw [individualsRun] at individuals'
          cases Result.ok_injective individuals'
          have sameNode : node' = node := UScalar.eq_of_val_eq (by rw [nodeValue,nodeValue'])
          subst sameNode
          have same : extra' = extra := alloc.vec.Vec.eq_iff extra' extra |>.mpr (by rw [extraValue,extraValue'])
          rw [← same]
          exact answerable
      · intro answer same Native D V vocabulary
        cases result with
        | none => cases same
        | some satisfiable =>
          simp only [Option.map_some,Option.some.injEq] at same
          subst same
          constructor
          · intro yes Object Value embed I model
            obtain ⟨_,valid,g,satisfied⟩ := model
            have fixes := fixes_of_interpretation valid
            by_contra outsideClass
            have located : Placement (withAnonymous I g) nodes.val (I.namedIndividuals a)
                (PositionOf nodes.val (.Named a)) = I.namedIndividuals a := by
              by_cases present : Individual.Named a ∈ nodes.val
              · rw [placement_at _ nodes.val _ _ present]; rfl
              · rw [show PositionOf nodes.val (.Named a) = 0 from positionFrom_absent nodes.val _ 0 present,
                  placement_zero]
            have accepted := closure_satisfiable_complete.{u, max w v, w} items nodes extra room extraIn mentioned
              satisfiable run valid g satisfied (Placement (withAnonymous I g) nodes.val (I.namedIndividuals a))
              (fun b present => placement_at _ nodes.val _ b present)
              (by
                intro q qIn
                rw [extraValue,List.mem_singleton] at qIn
                subst qIn
                simp only [nodeValue,located]
                exact (translated_meaning fixes g e false outside translatedRead _).mpr outsideClass)
            simp [accepted] at yes
          · intro instance'
            cases satisfiable with
            | false => rfl
            | true =>
              exfalso
              obtain ⟨Object,I,f,model,placed,holds⟩ := closure_satisfiable_sound.{u,v,w} items nodes extra room extraIn
                run D V vocabulary
              have fixes := fixes_of_interpretation model.2.1
              have notIn := (nnf_meaning e false outside translatedRead I fixes (f node.val)).mp
                (holds ⟨node,outside⟩ (by simp [extraValue]))
              have at_a : f node.val = I.namedIndividuals a := by
                rw [nodeValue,← placed (.Named a)]
                rfl
              rw [at_a] at notIn
              exact notIn (instance' _ _ _ _ model)

/-- Any OWL model of the closure, in any universes and for any vocabulary, makes
    a consistency answer positive. -/
theorem consistent_complete (items : alloc.vec.Vec AnnotatedAxiom) (answer : Bool)
    (answered : alc_ontology.consistent items = .ok (some answer)) {Native : Type w} (D : DatatypeMap Native)
    (V : Vocabulary) (consistent : Consistent.{u,v,w} D V items.val) : answer = true := by
  obtain ⟨individuals,individualsRun,individualsSpec⟩ := nodes_of items
  rw [alc_ontology.consistent] at answered
  cases individuals with
  | none => simp [individualsRun] at answered
  | some nodes =>
    obtain ⟨mentioned,room⟩ := individualsSpec nodes rfl
    simp only [individualsRun,bind_ok] at answered
    obtain ⟨Object,Value,embed,I,_,valid,g,satisfied⟩ := consistent
    obtain ⟨x⟩ := I.objectsNonempty
    exact closure_satisfiable_complete.{u,v,w} items nodes _ room (by simp) mentioned answer answered valid g
      satisfied (Placement (withAnonymous I g) nodes.val x) (fun a present => placement_at _ nodes.val x a present)
      (by simp)
/-- An instance of the expression in any OWL model of the closure, in any
    universes and for any vocabulary, makes a satisfiability answer positive. -/
theorem class_satisfiable_complete (items : alloc.vec.Vec AnnotatedAxiom) (e : ClassExpression) (answer : Bool)
    (answered : alc_ontology.class_satisfiable items e = .ok (some answer)) {Native : Type w}
    (D : DatatypeMap Native) (V : Vocabulary) (satisfiable : ClassSatisfiable.{u,v,w} D V items.val e) :
    answer = true := by
  obtain ⟨translated,translatedRead,_⟩ := nnf_total_correct.{0,0} e true
  rw [alc_ontology.class_satisfiable] at answered
  cases translated with
  | none => simp [translatedRead] at answered
  | some concept =>
    obtain ⟨individuals,individualsRun,individualsSpec⟩ := nodes_of items
    cases individuals with
    | none => simp [translatedRead,individualsRun] at answered
    | some nodes =>
      obtain ⟨mentioned,room⟩ := individualsSpec nodes rfl
      obtain ⟨extra,extraRun,extraValue⟩ := single_placed concept 0#usize
      simp only [translatedRead,individualsRun,extraRun,bind_ok] at answered
      obtain ⟨Object,Value,embed,I,⟨_,valid,g,satisfied⟩,x,member⟩ := satisfiable
      have fixes := fixes_of_interpretation valid
      exact closure_satisfiable_complete.{u,v,w} items nodes extra room (by simp [extraValue]) mentioned answer answered
        valid g satisfied (Placement (withAnonymous I g) nodes.val x)
        (fun a present => placement_at _ nodes.val x a present)
        (by
          intro q qIn
          simp only [extraValue,List.mem_singleton] at qIn
          subst qIn
          simp only [placement_zero]
          exact (translated_meaning fixes g e true concept translatedRead x).mpr member)
/-- A positive subsumption answer holds in every OWL model of the closure, in
    any universes and for any vocabulary. -/
theorem subsumed_sound (items : alloc.vec.Vec AnnotatedAxiom) (sub sup : ClassExpression)
    (answered : alc_ontology.subsumed items sub sup = .ok (some true)) {Native : Type w} (D : DatatypeMap Native)
    (V : Vocabulary) : Subsumed.{u,v,w} D V items.val sub sup := by
  obtain ⟨insideResult,insideRead,_⟩ := nnf_total_correct.{0,0} sub true
  obtain ⟨outsideResult,outsideRead,_⟩ := nnf_total_correct.{0,0} sup false
  rw [alc_ontology.subsumed] at answered
  cases insideResult with
  | none => simp [insideRead] at answered
  | some inside =>
    cases outsideResult with
    | none => simp [insideRead,outsideRead] at answered
    | some outside =>
      obtain ⟨individuals,individualsRun,individualsSpec⟩ := nodes_of items
      cases individuals with
      | none => simp [insideRead,outsideRead,individualsRun] at answered
      | some nodes =>
        obtain ⟨mentioned,room⟩ := individualsSpec nodes rfl
        obtain ⟨one,extra,oneRun,extraRun,extraValue⟩ := pair_placed inside outside
        have extraIn : ∀ q ∈ extra.val, q.node.val ≤ nodes.val.length := by
          intro q member; rw [extraValue] at member; simp at member; rcases member with rfl | rfl <;> simp
        obtain ⟨result,run,_⟩ := closure_satisfiable_total items nodes extra room extraIn
        simp only [insideRead,outsideRead,individualsRun,oneRun,extraRun,run,bind_ok] at answered
        cases result with
        | none => simp at answered
        | some satisfiable =>
          have notSatisfiable : satisfiable = false := by simpa using answered
          subst notSatisfiable
          intro Object Value embed I model x member
          obtain ⟨_,valid,g,satisfied⟩ := model
          have fixes := fixes_of_interpretation valid
          by_contra outsideSup
          have accepted := closure_satisfiable_complete.{u,v,w} items nodes extra room extraIn mentioned false run
            valid g satisfied (Placement (withAnonymous I g) nodes.val x)
            (fun a present => placement_at _ nodes.val x a present)
            (by
              intro q qIn
              rw [extraValue] at qIn
              simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at qIn
              rcases qIn with rfl | rfl
              · simp only [placement_zero]
                exact (translated_meaning fixes g sub true inside insideRead x).mpr member
              · simp only [placement_zero]
                exact (translated_meaning fixes g sup false outside outsideRead x).mpr outsideSup)
          cases accepted
/-- A positive instance answer holds in every OWL model of the closure, in any
    universes and for any vocabulary. -/
theorem instance_of_sound (items : alloc.vec.Vec AnnotatedAxiom) (a : NamedIndividual) (e : ClassExpression)
    (answered : alc_ontology.instance_of items a e = .ok (some true)) {Native : Type w} (D : DatatypeMap Native)
    (V : Vocabulary) : InstanceOf.{u,v,w} D V items.val a e := by
  obtain ⟨translated,translatedRead,_⟩ := nnf_total_correct.{0,0} e false
  rw [alc_ontology.instance_of] at answered
  cases translated with
  | none => simp [translatedRead] at answered
  | some outside =>
    obtain ⟨individuals,individualsRun,individualsSpec⟩ := nodes_of items
    cases individuals with
    | none => simp [translatedRead,individualsRun] at answered
    | some nodes =>
      obtain ⟨mentioned,room⟩ := individualsSpec nodes rfl
      obtain ⟨node,nodeRun,nodeValue⟩ := position_of nodes (.Named a)
      have named : (Individual.Named { iri := a.iri } : Individual) = .Named a := by cases a; rfl
      obtain ⟨extra,extraRun,extraValue⟩ := single_placed outside node
      have extraIn : ∀ q ∈ extra.val, q.node.val ≤ nodes.val.length := by
        intro q member
        rw [extraValue,List.mem_singleton] at member
        subst member
        rw [nodeValue]
        exact positionOf_le _ _
      obtain ⟨result,run,_⟩ := closure_satisfiable_total items nodes extra room extraIn
      simp only [translatedRead,individualsRun,bind_ok,Rowl.Nnf.copy_iri_identity,named,nodeRun,extraRun,run] at answered
      cases result with
      | none => simp at answered
      | some satisfiable =>
        have notSatisfiable : satisfiable = false := by simpa using answered
        subst notSatisfiable
        intro Object Value embed I model
        obtain ⟨_,valid,g,satisfied⟩ := model
        have fixes := fixes_of_interpretation valid
        by_contra outsideClass
        have located : Placement (withAnonymous I g) nodes.val (I.namedIndividuals a)
            (PositionOf nodes.val (.Named a)) = I.namedIndividuals a := by
          by_cases present : Individual.Named a ∈ nodes.val
          · rw [placement_at _ nodes.val _ _ present]; rfl
          · rw [show PositionOf nodes.val (.Named a) = 0 from positionFrom_absent nodes.val _ 0 present,
              placement_zero]
        have accepted := closure_satisfiable_complete.{u,v,w} items nodes extra room extraIn mentioned false run
          valid g satisfied (Placement (withAnonymous I g) nodes.val (I.namedIndividuals a))
          (fun b present => placement_at _ nodes.val _ b present)
          (by
            intro q qIn
            rw [extraValue,List.mem_singleton] at qIn
            subst qIn
            simp only [nodeValue,located]
            exact (translated_meaning fixes g e false outside translatedRead _).mpr outsideClass)
        cases accepted
end Rowl.AlcOntology
