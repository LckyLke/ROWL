import Rowl.ShiRoles
import Rowl.Completion
import Rowl.ForestModel
import Rowl.ShiEquality
import Rowl.ShiNominals

/-!
Ontology-level answers for axiom closures with assertions, proved against the
independent Direct Semantics: consistency, class satisfiability, subsumption and
instance checking. The class axioms become the TBox concept and the
definitions (`ShiParts`), the role axioms the role hierarchy (`ShiRoles`), and
the assertions the facts and links of the named individuals, which equal
individuals place at one node (`ShiEquality`). A question whose concepts have
no number restriction, self restriction or nominal, about a closure without
negative assertions next to role axioms and without asymmetric or disjoint
object properties, goes to the completion graph tableau, whose models keep
different nodes apart; every other question goes to the completion forest,
which handles self restrictions, number restrictions, complements of self
restrictions and disjoint pairs on simple roles, and nominals of named
individuals, with the nominal of every individual at its node and the
inequalities and negative assertions as facts (`ShiNominals`); every answer
the kernel gives is exact for the OWL definitions.
An acceptance comes with an actual OWL model of the closure, built from the
tableau's model with every individual at its node and the built-in classes,
properties and the datatype map fixed as OWL requires, and every OWL model, in
any universes, forces acceptance.
-/
namespace Rowl.ShiOntology
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation classDenote objectRelation thing nothing topObject bottomObject DatatypeMap
  ValueEmbedding Vocabulary IsVocabulary IsInterpretation Model Consistent ClassSatisfiable Subsumed InstanceOf
  withAnonymous)
open Rowl.Nnf (Fixes Polar fixes_of_interpretation)
open Rowl.Concepts (denote inv relation_inv Translatable Correct translate_total_correct translate_meaning inverse_correct
  copy_role_identity same_role_correct)
open Rowl.Hierarchy (Below Closed Respects Constrained)
open Rowl.Internalization (Assertion)
open Rowl.AlcOntology (builtin_class_correct role_proper_correct RoleOf IndividualsOf PositionOf PositionFrom
  positionOf_le positionOf_present positionFrom_absent position_of individuals_from_correct has_negative_correct
  Negative owlModel owl_model_valid embedding Placement placement_zero placement_at assertion_of_individual)
open Rowl.ShiParts (SupportedAxiom RoleAxiom ConstraintAxiom Equality ClassPart PartsHold class_parts_correct)
open Rowl.ShiEquality (MembersOf Equal Representative RepOf Joins Clashes members_from_correct joins_of
  node_of_correct representative_value repOf_le clash_from_correct)
open Rowl.ShiNominals (IsNamed Mentions Nominal not_mentions nominal_correct facts_nominal_correct
  closure_nominal_correct facts_known_correct nominal_individuals_correct definition_individuals_correct
  assertion_individuals_correct named_from_correct unequal_from_correct refused_from_correct)
open Rowl.ShiRoles (RolesHold role_hierarchy_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
universe u v w

/-- No built-in class occurs as a named class, no built-in object property as a
    role and no anonymous individual in a nominal, so the tableaux's reading of
    every name is an ordinary one. -/
def Proper : concepts.Concept → Prop
  | .Top => True
  | .Bottom => True
  | .Atom c => c ≠ thing ∧ c ≠ nothing
  | .NotAtom c => c ≠ thing ∧ c ≠ nothing
  | .One a => IsNamed a
  | .NotOne a => IsNamed a
  | .HasSelf r => RoleOf r ≠ topObject ∧ RoleOf r ≠ bottomObject
  | .NotSelf r => RoleOf r ≠ topObject ∧ RoleOf r ≠ bottomObject
  | .And a b => Proper a ∧ Proper b
  | .Or a b => Proper a ∧ Proper b
  | .Exists r c => (RoleOf r ≠ topObject ∧ RoleOf r ≠ bottomObject) ∧ Proper c
  | .Forall r c => (RoleOf r ≠ topObject ∧ RoleOf r ≠ bottomObject) ∧ Proper c
  | .AtLeast _ r c => (RoleOf r ≠ topObject ∧ RoleOf r ≠ bottomObject) ∧ Proper c
  | .AtMost _ r c => (RoleOf r ≠ topObject ∧ RoleOf r ≠ bottomObject) ∧ Proper c

/-- A number restriction or a self restriction occurs, which only the
    completion forest decides. -/
def Counts : concepts.Concept → Prop
  | .And a b => Counts a ∨ Counts b
  | .Or a b => Counts a ∨ Counts b
  | .Exists _ c => Counts c
  | .Forall _ c => Counts c
  | .AtLeast _ _ _ => True
  | .AtMost _ _ _ => True
  | .HasSelf _ => True
  | .NotSelf _ => True
  | _ => False

/-- A definition of an ordinary class by a proper concept. -/
def DefinitionProper (d : completion.Definition) : Prop :=
  (d.class ≠ thing ∧ d.class ≠ nothing) ∧ Proper d.concept

/-- An object property assertion or role axiom that does not use a built-in
    object property. -/
def RoleProper : Axiom → Prop
  | .ObjectPropertyAssertion p _ _ => RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject
  | .NegativeObjectPropertyAssertion p _ _ => RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject
  | .SubObjectPropertyOf (.Single sub) sup => (RoleOf sub ≠ topObject ∧ RoleOf sub ≠ bottomObject) ∧
      (RoleOf sup ≠ topObject ∧ RoleOf sup ≠ bottomObject)
  | .EquivalentObjectProperties xs => ∀ p ∈ xs.elements, RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject
  | .InverseObjectProperties p q => (RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject) ∧
      (RoleOf q ≠ topObject ∧ RoleOf q ≠ bottomObject)
  | .SymmetricObjectProperty p => RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject
  | .TransitiveObjectProperty p => RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject
  | .AsymmetricObjectProperty p => RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject
  | .DisjointObjectProperties xs => ∀ p ∈ xs.elements, RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject
  | _ => True

/-- A negative object property assertion whose individuals' nodes some link
    relates along its property, in either orientation. -/
noncomputable def Denies (same : List Usize) (nodes : List Individual) (links : List completion.Link) :
    Axiom → Prop
  | .NegativeObjectPropertyAssertion p s t => ∃ l ∈ links,
      (l.from.val = RepOf same nodes s ∧ l.to.val = RepOf same nodes t ∧ l.role = p) ∨
      (l.from.val = RepOf same nodes t ∧ l.to.val = RepOf same nodes s ∧ l.role = inv p)
  | _ => False

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- The properness check is exact. -/
theorem proper_correct (c : concepts.Concept) : shi_ontology.proper c = .ok (decide (Proper c)) := by
  induction c with
  | Top => rw [shi_ontology.proper]; simp [Proper]
  | Bottom => rw [shi_ontology.proper]; simp [Proper]
  | Atom k => rw [shi_ontology.proper]; simp [Proper,builtin_class_correct]
  | NotAtom k => rw [shi_ontology.proper]; simp [Proper,builtin_class_correct]
  | One a => rw [shi_ontology.proper]; cases a <;> simp [Proper,IsNamed,shi_ontology.named_individual]
  | NotOne a => rw [shi_ontology.proper]; cases a <;> simp [Proper,IsNamed,shi_ontology.named_individual]
  | HasSelf r | NotSelf r =>
    rw [shi_ontology.proper,role_proper_correct]
    simp only [Proper]
    exact congrArg _ (decide_eq_decide.mpr Iff.rfl)
  | And a b iha ihb =>
    rw [shi_ontology.proper]
    by_cases left : Proper a <;> simp [Proper,iha,ihb,left]
  | Or a b iha ihb =>
    rw [shi_ontology.proper]
    by_cases left : Proper a <;> simp [Proper,iha,ihb,left]
  | Exists r c ih =>
    rw [shi_ontology.proper]
    by_cases role : RoleOf r ≠ topObject ∧ RoleOf r ≠ bottomObject
    · simp only [role_proper_correct,bind_ok]
      rw [decide_eq_true role]
      simp [Proper,ih,role]
    · simp only [role_proper_correct,bind_ok]
      rw [decide_eq_false role]
      simp only [Bool.false_eq_true,↓reduceIte,Proper]
      simp [role]
  | Forall r c ih =>
    rw [shi_ontology.proper]
    by_cases role : RoleOf r ≠ topObject ∧ RoleOf r ≠ bottomObject
    · simp only [role_proper_correct,bind_ok]
      rw [decide_eq_true role]
      simp [Proper,ih,role]
    · simp only [role_proper_correct,bind_ok]
      rw [decide_eq_false role]
      simp only [Bool.false_eq_true,↓reduceIte,Proper]
      simp [role]
  | AtLeast n r c ih =>
    rw [shi_ontology.proper]
    by_cases role : RoleOf r ≠ topObject ∧ RoleOf r ≠ bottomObject
    · simp only [role_proper_correct,bind_ok]
      rw [decide_eq_true role]
      simp [Proper,ih,role]
    · simp only [role_proper_correct,bind_ok]
      rw [decide_eq_false role]
      simp only [Bool.false_eq_true,↓reduceIte,Proper]
      simp [role]
  | AtMost n r c ih =>
    rw [shi_ontology.proper]
    by_cases role : RoleOf r ≠ topObject ∧ RoleOf r ≠ bottomObject
    · simp only [role_proper_correct,bind_ok]
      rw [decide_eq_true role]
      simp [Proper,ih,role]
    · simp only [role_proper_correct,bind_ok]
      rw [decide_eq_false role]
      simp only [Bool.false_eq_true,↓reduceIte,Proper]
      simp [role]

/-- The counting check is exact. -/
theorem counts_correct (c : concepts.Concept) : shi_ontology.counts c = .ok (decide (Counts c)) := by
  induction c with
  | Top => rw [shi_ontology.counts]; simp [Counts]
  | Bottom => rw [shi_ontology.counts]; simp [Counts]
  | Atom k => rw [shi_ontology.counts]; simp [Counts]
  | NotAtom k => rw [shi_ontology.counts]; simp [Counts]
  | One a => rw [shi_ontology.counts]; simp [Counts]
  | NotOne a => rw [shi_ontology.counts]; simp [Counts]
  | HasSelf r | NotSelf r => rw [shi_ontology.counts]; simp [Counts]
  | And a b iha ihb =>
    rw [shi_ontology.counts]
    by_cases left : Counts a <;> simp [Counts,iha,ihb,left]
  | Or a b iha ihb =>
    rw [shi_ontology.counts]
    by_cases left : Counts a <;> simp [Counts,iha,ihb,left]
  | Exists r c ih => rw [shi_ontology.counts]; simp [Counts,ih]
  | Forall r c ih => rw [shi_ontology.counts]; simp [Counts,ih]
  | AtLeast n r c _ => rw [shi_ontology.counts]; simp [Counts]
  | AtMost n r c _ => rw [shi_ontology.counts]; simp [Counts]

/-- The counting check over definitions is exact. -/
theorem definitions_count_correct (definitions : alloc.vec.Vec completion.Definition) (index : Usize) :
    shi_ontology.definitions_count definitions index =
      .ok (decide (∃ d ∈ definitions.val.drop index.val, Counts d.concept)) := by
  rw [shi_ontology.definitions_count]
  by_cases more : index.val < definitions.val.length
  · have lookup : definitions.index_usize index = .ok definitions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : definitions.val.drop index.val = definitions.val[index.val] :: definitions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := definitions_count_correct definitions next
    rw [nextIndex] at rest
    by_cases here : Counts definitions.val[index.val].concept
    · have found : ∃ d ∈ definitions.val.drop index.val, Counts d.concept :=
        ⟨_,by rw [split]; exact List.mem_cons_self ..,here⟩
      simp [more,lookup,counts_correct,here,found]
    · have same : (∃ d ∈ definitions.val.drop index.val, Counts d.concept) ↔
          ∃ d ∈ definitions.val.drop (index.val+1), Counts d.concept := by
        rw [split]
        constructor
        · rintro ⟨d,member,counts⟩
          rcases List.mem_cons.mp member with rfl | later
          · exact absurd counts here
          · exact ⟨d,later,counts⟩
        · rintro ⟨d,member,counts⟩
          exact ⟨d,List.mem_cons_of_mem _ member,counts⟩
      simp [more,lookup,counts_correct,here,advance,rest,same]
  · have empty : definitions.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [more,empty]
termination_by definitions.val.length - index.val
decreasing_by omega

/-- The counting check over facts is exact. -/
theorem facts_count_correct (facts : alloc.vec.Vec completion.Fact) (index : Usize) :
    shi_ontology.facts_count facts index = .ok (decide (∃ q ∈ facts.val.drop index.val, Counts q.concept)) := by
  rw [shi_ontology.facts_count]
  by_cases more : index.val < facts.val.length
  · have lookup : facts.index_usize index = .ok facts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : facts.val.drop index.val = facts.val[index.val] :: facts.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := facts_count_correct facts next
    rw [nextIndex] at rest
    by_cases here : Counts facts.val[index.val].concept
    · have found : ∃ q ∈ facts.val.drop index.val, Counts q.concept :=
        ⟨_,by rw [split]; exact List.mem_cons_self ..,here⟩
      simp [more,lookup,counts_correct,here,found]
    · have same : (∃ q ∈ facts.val.drop index.val, Counts q.concept) ↔
          ∃ q ∈ facts.val.drop (index.val+1), Counts q.concept := by
        rw [split]
        constructor
        · rintro ⟨q,member,counts⟩
          rcases List.mem_cons.mp member with rfl | later
          · exact absurd counts here
          · exact ⟨q,later,counts⟩
        · rintro ⟨q,member,counts⟩
          exact ⟨q,List.mem_cons_of_mem _ member,counts⟩
      simp [more,lookup,counts_correct,here,advance,rest,same]
  · have empty : facts.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [more,empty]
termination_by facts.val.length - index.val
decreasing_by omega

/-- Whether the TBox concept, a definition or a fact counts, exactly. -/
theorem closure_counts_correct (parts : shi_ontology.Parts) (facts : alloc.vec.Vec completion.Fact) :
    shi_ontology.closure_counts parts facts = .ok (decide (Counts parts.axioms ∨
      (∃ d ∈ parts.definitions.val, Counts d.concept) ∨ ∃ q ∈ facts.val, Counts q.concept)) := by
  have definitions := definitions_count_correct parts.definitions 0#usize
  have facts' := facts_count_correct facts 0#usize
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at definitions facts'
  rw [shi_ontology.closure_counts]
  by_cases one : Counts parts.axioms
  · simp [counts_correct,one]
  · by_cases two : ∃ d ∈ parts.definitions.val, Counts d.concept
    · simp [counts_correct,one,definitions,two]
    · simp only [counts_correct,decide_eq_false one,Bool.false_eq_true,↓reduceIte,bind_ok,definitions,
        decide_eq_false two,facts']
      simp [one,two]

/-- Whether a prepared question goes to the completion forest, exactly. -/
theorem question_forest_correct (p : shi_ontology.Prepared) (extra : alloc.vec.Vec completion.Fact) :
    shi_ontology.question_forest p extra = .ok (decide (p.forest = true ∨ (∃ q ∈ extra.val, Counts q.concept) ∨
      ∃ q ∈ extra.val, Nominal q.concept)) := by
  have counting := facts_count_correct extra 0#usize
  have nominal := facts_nominal_correct extra 0#usize
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at counting nominal
  rw [shi_ontology.question_forest]
  cases forestIs : p.forest
  · by_cases counts : ∃ q ∈ extra.val, Counts q.concept
    · simp [counting,counts]
    · simp [counting,counts,nominal]
  · simp

/-- The properness check over definitions is exact. -/
theorem definitions_proper_correct (definitions : alloc.vec.Vec completion.Definition) (index : Usize) :
    shi_ontology.definitions_proper definitions index =
      .ok (decide (∀ d ∈ definitions.val.drop index.val, DefinitionProper d)) := by
  rw [shi_ontology.definitions_proper]
  by_cases more : index.val < definitions.val.length
  · have lookup : definitions.index_usize index = .ok definitions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : definitions.val.drop index.val = definitions.val[index.val] :: definitions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := definitions_proper_correct definitions next
    rw [nextIndex] at rest
    rw [split]
    simp only [List.forall_mem_cons]
    by_cases here : DefinitionProper definitions.val[index.val]
    · have ordinary := here.1
      simp [more,lookup,builtin_class_correct,ordinary,proper_correct,here.2,advance,rest,here]
    · by_cases ordinary : definitions.val[index.val].class ≠ thing ∧ definitions.val[index.val].class ≠ nothing
      · have improper : ¬ Proper definitions.val[index.val].concept := fun proper => here ⟨ordinary,proper⟩
        simp [more,lookup,builtin_class_correct,ordinary,proper_correct,improper,here]
      · have builtin : definitions.val[index.val].class = thing ∨ definitions.val[index.val].class = nothing := by
          by_contra neither
          exact ordinary ⟨fun same => neither (.inl same),fun same => neither (.inr same)⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,builtin_class_correct]
        rw [decide_eq_true builtin]
        simp [here]
  · have empty : definitions.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [more,empty]
termination_by definitions.val.length - index.val
decreasing_by omega

/-- The properness check over facts is exact. -/
theorem facts_proper_correct (facts : alloc.vec.Vec completion.Fact) (index : Usize) :
    shi_ontology.facts_proper facts index = .ok (decide (∀ q ∈ facts.val.drop index.val, Proper q.concept)) := by
  rw [shi_ontology.facts_proper]
  by_cases more : index.val < facts.val.length
  · have lookup : facts.index_usize index = .ok facts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : facts.val.drop index.val = facts.val[index.val] :: facts.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := facts_proper_correct facts next
    rw [nextIndex] at rest
    rw [split]
    simp only [List.forall_mem_cons]
    by_cases here : Proper facts.val[index.val].concept
    · simp [more,lookup,proper_correct,here,advance,rest]
    · simp [more,lookup,proper_correct,here]
  · have empty : facts.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [more,empty]
termination_by facts.val.length - index.val
decreasing_by omega

private theorem rest_proper_correct (values : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) :
    shi_ontology.rest_proper values index =
      .ok (decide (∀ p ∈ values.val.drop index.val, RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject)) := by
  rw [shi_ontology.rest_proper]
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
    shi_ontology.members_proper members =
      .ok (decide (∀ p ∈ members.elements, RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject)) := by
  rw [shi_ontology.members_proper]
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
    shi_ontology.pair_proper sub sup = .ok (decide ((RoleOf sub ≠ topObject ∧ RoleOf sub ≠ bottomObject) ∧
      (RoleOf sup ≠ topObject ∧ RoleOf sup ≠ bottomObject))) := by
  rw [shi_ontology.pair_proper]
  by_cases first : RoleOf sub ≠ topObject ∧ RoleOf sub ≠ bottomObject
  · simp only [role_proper_correct,bind_ok]
    rw [decide_eq_true first]
    simp [first]
  · simp only [role_proper_correct,bind_ok]
    rw [decide_eq_false first]
    simp [first]

/-- The role check over the assertions and role axioms is exact. -/
theorem roles_proper_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    shi_ontology.roles_proper items index = .ok (decide (∀ item ∈ items.val.drop index.val, RoleProper item.axiom)) := by
  rw [shi_ontology.roles_proper]
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
    -- Each case: the check of this axiom decides `RoleProper`, then the rest follows.
    have finish : ∀ (b : Bool), (b = true ↔ RoleProper items.val[index.val].axiom) →
        (do
          if b then
            let i1 ← index + 1#usize
            shi_ontology.roles_proper items i1
          else ok false : Result Bool) =
          .ok (decide (RoleProper items.val[index.val].axiom ∧
            ∀ item ∈ items.val.drop (index.val+1), RoleProper item.axiom)) := by
      intro b decided
      cases b with
      | true =>
        have proper := decided.mp rfl
        simp only [↓reduceIte,advance,bind_ok,rest]
        congr 1
        exact decide_eq_decide.mpr ⟨fun later => ⟨proper,later⟩,fun both => both.2⟩
      | false =>
        have improper : ¬ RoleProper items.val[index.val].axiom := fun proper => by simpa using decided.mpr proper
        simp only [Bool.false_eq_true,↓reduceIte]
        congr 1
        simp [improper]
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,bind_ok]
    cases item : items.val[index.val].axiom with
    | ObjectPropertyAssertion p a b =>
      simp only [role_proper_correct,bind_ok]
      have := finish (decide (RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject)) (by simp [item,RoleProper])
      simpa [item] using this
    | NegativeObjectPropertyAssertion p a b =>
      simp only [role_proper_correct,bind_ok]
      have := finish (decide (RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject)) (by simp [item,RoleProper])
      simpa [item] using this
    | SubObjectPropertyOf sub sup =>
      cases sub with
      | Single p =>
        simp only [pair_proper_correct,bind_ok]
        have := finish (decide ((RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject) ∧
          (RoleOf sup ≠ topObject ∧ RoleOf sup ≠ bottomObject))) (by simp [item,RoleProper])
        simpa [item] using this
      | Chain c =>
        simp only [bind_ok]
        have := finish true (by simp [item,RoleProper])
        simpa [item] using this
    | EquivalentObjectProperties members =>
      simp only [members_proper_correct,bind_ok]
      have := finish (decide (∀ p ∈ members.elements, RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject))
        (by simp [item,RoleProper])
      simpa [item] using this
    | InverseObjectProperties p q =>
      simp only [pair_proper_correct,bind_ok]
      have := finish (decide ((RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject) ∧
        (RoleOf q ≠ topObject ∧ RoleOf q ≠ bottomObject))) (by simp [item,RoleProper])
      simpa [item] using this
    | SymmetricObjectProperty p =>
      simp only [role_proper_correct,bind_ok]
      have := finish (decide (RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject)) (by simp [item,RoleProper])
      simpa [item] using this
    | TransitiveObjectProperty p =>
      simp only [role_proper_correct,bind_ok]
      have := finish (decide (RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject)) (by simp [item,RoleProper])
      simpa [item] using this
    | AsymmetricObjectProperty p =>
      simp only [role_proper_correct,bind_ok]
      have := finish (decide (RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject)) (by simp [item,RoleProper])
      simpa [item] using this
    | DisjointObjectProperties members =>
      simp only [members_proper_correct,bind_ok]
      have := finish (decide (∀ p ∈ members.elements, RoleOf p ≠ topObject ∧ RoleOf p ≠ bottomObject))
        (by simp [item,RoleProper])
      simpa [item] using this
    | _ =>
      simp only [bind_ok]
      have := finish true (by simp [item,RoleProper])
      simpa [item] using this
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [more,empty]
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- The facts of the class assertions: every fact is given or is the
    translation of a class assertion at its individual's node, and every class
    assertion has its fact. -/
theorem assertions_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (same : alloc.vec.Vec Usize) (index : Usize) (facts : alloc.vec.Vec completion.Fact) :
    ∃ result, shi_ontology.assertions_from items nodes same index facts = .ok result ∧ ∀ final, result = some final →
      (∀ q ∈ final.val, q ∈ facts.val ∨ ∃ item ∈ items.val.drop index.val, ∃ C m,
        item.axiom = .ClassAssertion C m ∧ q.node.val = RepOf same.val nodes.val m ∧
        concepts.translate C true = .ok (some q.concept)) ∧
      (∀ q ∈ facts.val, q ∈ final.val) ∧
      (∀ item ∈ items.val.drop index.val, ∀ C m, item.axiom = .ClassAssertion C m →
        ∃ q ∈ final.val, q.node.val = RepOf same.val nodes.val m ∧
          concepts.translate C true = .ok (some q.concept)) := by
  rw [shi_ontology.assertions_from]
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
      obtain ⟨translated,translatedRead,_⟩ := translate_total_correct.{0,0} C true
      cases translated with
      | none => exact ⟨none,by simp [more,lookup,item,translatedRead],by intro final impossible; cases impossible⟩
      | some concept =>
        obtain ⟨node,nodeRun,nodeValue⟩ := node_of_correct nodes same m
        by_cases fits : facts.val.length < Usize.max
        · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec facts ⟨node,concept⟩ fits)
          obtain ⟨result,run,spec⟩ := assertions_from_correct items nodes same next appended
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
      obtain ⟨result,run,spec⟩ := assertions_from_correct items nodes same next facts
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
    refine ⟨some facts,by simp [more],?_⟩
    intro final same
    cases same
    exact ⟨fun q member => .inl member,fun q member => member,by simp [empty]⟩
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- The links of the object property assertions: every link is given or is an
    object property assertion between its individuals' nodes, and every object
    property assertion has its link. -/
theorem links_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (same : alloc.vec.Vec Usize) (index : Usize) (links : alloc.vec.Vec completion.Link) :
    ∃ result, shi_ontology.links_from items nodes same index links = .ok result ∧ ∀ final, result = some final →
      (∀ l ∈ final.val, l ∈ links.val ∨ ∃ item ∈ items.val.drop index.val, ∃ p s t,
        item.axiom = .ObjectPropertyAssertion p s t ∧ l.role = p ∧ l.from.val = RepOf same.val nodes.val s ∧
        l.to.val = RepOf same.val nodes.val t) ∧
      (∀ l ∈ links.val, l ∈ final.val) ∧
      (∀ item ∈ items.val.drop index.val, ∀ p s t, item.axiom = .ObjectPropertyAssertion p s t →
        ∃ l ∈ final.val, l.role = p ∧ l.from.val = RepOf same.val nodes.val s ∧
          l.to.val = RepOf same.val nodes.val t) := by
  rw [shi_ontology.links_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    cases item : items.val[index.val].axiom with
    | ObjectPropertyAssertion p a b =>
      obtain ⟨pa,paRun,paValue⟩ := node_of_correct nodes same a
      obtain ⟨pb,pbRun,pbValue⟩ := node_of_correct nodes same b
      by_cases fits : links.val.length < Usize.max
      · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec links ⟨p,pa,pb⟩ fits)
        obtain ⟨result,run,spec⟩ := links_from_correct items nodes same next appended
        refine ⟨result,by simp [more,lookup,item,usize_max_val,fits,copy_role_identity,paRun,pbRun,push,advance,run],?_⟩
        intro final same
        obtain ⟨origin,kept,covered⟩ := spec final same
        refine ⟨?_,fun l member => kept l (by rw [contents]; exact List.mem_append_left _ member),?_⟩
        · intro l member
          rcases origin l member with fromAppended | later
          · rw [contents] at fromAppended
            rcases List.mem_append.mp fromAppended with old | here
            · exact .inl old
            · rw [List.mem_singleton] at here
              subst here
              exact .inr ⟨items.val[index.val],by rw [split]; exact List.mem_cons_self ..,p,a,b,item,rfl,paValue,
                pbValue⟩
          · obtain ⟨other,otherIn,q,s,t,otherItem,role,source,target⟩ := later
            rw [nextIndex] at otherIn
            exact .inr ⟨other,by rw [split]; exact List.mem_cons_of_mem _ otherIn,q,s,t,otherItem,role,source,target⟩
        · intro other member q s t otherItem
          rw [split] at member
          rcases List.mem_cons.mp member with rfl | later
          · rw [item] at otherItem
            cases otherItem
            exact ⟨⟨p,pa,pb⟩,kept _ (by rw [contents]; exact List.mem_append_right _ (List.mem_singleton_self _)),
              rfl,paValue,pbValue⟩
          · rw [nextIndex] at covered
            exact covered other later q s t otherItem
      · exact ⟨none,by simp [more,lookup,item,usize_max_val,fits],by intro final impossible; cases impossible⟩
    | _ =>
      obtain ⟨result,run,spec⟩ := links_from_correct items nodes same next links
      refine ⟨result,by simp [more,lookup,item,advance,run],?_⟩
      intro final same
      obtain ⟨origin,kept,covered⟩ := spec final same
      refine ⟨?_,kept,?_⟩
      · intro l member
        rcases origin l member with old | ⟨other,otherIn,q,s,t,otherItem,role,source,target⟩
        · exact .inl old
        · rw [nextIndex] at otherIn
          exact .inr ⟨other,by rw [split]; exact List.mem_cons_of_mem _ otherIn,q,s,t,otherItem,role,source,target⟩
      · intro other member q s t otherItem
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · rw [item] at otherItem
          cases otherItem
        · rw [nextIndex] at covered
          exact covered other later q s t otherItem
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some links,by simp [more],?_⟩
    intro final same
    cases same
    exact ⟨fun l member => .inl member,fun l member => member,by simp [empty]⟩
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- The link test is exact. -/
theorem link_is_correct (l : completion.Link) (role : ObjectPropertyExpression) (source target : Usize) :
    shi_ontology.link_is l role source target =
      .ok (decide (l.from.val = source.val ∧ l.to.val = target.val ∧ l.role = role)) := by
  rw [shi_ontology.link_is]
  by_cases first : l.from = source
  · by_cases second : l.to = target
    · simp [first,second,same_role_correct]
    · have different : ¬ l.to.val = target.val := fun same => second (UScalar.eq_of_val_eq same)
      simp [first,second,different]
  · have different : ¬ l.from.val = source.val := fun same => first (UScalar.eq_of_val_eq same)
    simp [first,different]

/-- The search for a link relating two nodes along a role, in either
    orientation, is exact. -/
theorem linked_from_correct (links : alloc.vec.Vec completion.Link) (index : Usize)
    (role flipped : ObjectPropertyExpression) (source target : Usize) :
    shi_ontology.linked_from links index role flipped source target =
      .ok (decide (∃ l ∈ links.val.drop index.val,
        (l.from.val = source.val ∧ l.to.val = target.val ∧ l.role = role) ∨
        (l.from.val = target.val ∧ l.to.val = source.val ∧ l.role = flipped))) := by
  rw [shi_ontology.linked_from]
  by_cases more : index.val < links.val.length
  · have lookup : links.index_usize index = .ok links.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : links.val.drop index.val = links.val[index.val] :: links.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := linked_from_correct links next role flipped source target
    rw [nextIndex] at rest
    rw [split]
    simp only [List.mem_cons,exists_eq_or_imp]
    by_cases forward : links.val[index.val].from.val = source.val ∧ links.val[index.val].to.val = target.val ∧
        links.val[index.val].role = role
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,link_is_correct]
      rw [decide_eq_true forward]
      simp [forward]
    · by_cases backward : links.val[index.val].from.val = target.val ∧ links.val[index.val].to.val = source.val ∧
          links.val[index.val].role = flipped
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,link_is_correct]
        rw [decide_eq_false forward,decide_eq_true backward]
        simp [backward]
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,link_is_correct]
        rw [decide_eq_false forward,decide_eq_false backward]
        simp only [Bool.false_eq_true,↓reduceIte,advance,bind_ok,rest]
        congr 1
        apply decide_eq_decide.mpr
        constructor
        · intro later
          exact .inr later
        · rintro ((first | first) | later)
          · exact absurd first forward
          · exact absurd first backward
          · exact later
  · have empty : links.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by links.val.length - index.val
decreasing_by omega

/-- The denial check is exact: some negative object property assertion denies a
    link. -/
theorem denied_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (same : alloc.vec.Vec Usize) (links : alloc.vec.Vec completion.Link) (index : Usize) :
    shi_ontology.denied_from items nodes same links index =
      .ok (decide (∃ item ∈ items.val.drop index.val, Denies same.val nodes.val links.val item.axiom)) := by
  rw [shi_ontology.denied_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := denied_from_correct items nodes same links next
    rw [nextIndex] at rest
    rw [split]
    simp only [List.mem_cons,exists_eq_or_imp]
    cases item : items.val[index.val].axiom with
    | NegativeObjectPropertyAssertion p a b =>
      obtain ⟨pa,paRun,paValue⟩ := node_of_correct nodes same a
      obtain ⟨pb,pbRun,pbValue⟩ := node_of_correct nodes same b
      have zero : (0#usize).val = 0 := rfl
      have found := linked_from_correct links 0#usize p (inv p) pa pb
      rw [zero,List.drop_zero] at found
      by_cases here : Denies same.val nodes.val links.val (.NegativeObjectPropertyAssertion p a b)
      · have linked : ∃ l ∈ links.val, (l.from.val = pa.val ∧ l.to.val = pb.val ∧ l.role = p) ∨
            (l.from.val = pb.val ∧ l.to.val = pa.val ∧ l.role = inv p) := by
          simpa [Denies,paValue,pbValue] using here
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,item,inverse_correct,paRun,pbRun,found]
        rw [decide_eq_true linked]
        simp [here]
      · have unlinked : ¬ ∃ l ∈ links.val, (l.from.val = pa.val ∧ l.to.val = pb.val ∧ l.role = p) ∨
            (l.from.val = pb.val ∧ l.to.val = pa.val ∧ l.role = inv p) := by
          simpa [Denies,paValue,pbValue] using here
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,item,inverse_correct,paRun,pbRun,found]
        rw [decide_eq_false unlinked]
        simp only [Bool.false_eq_true,↓reduceIte,advance,bind_ok,rest]
        congr 1
        exact decide_eq_decide.mpr ⟨fun later => .inr later,fun both => both.resolve_left here⟩
    | _ =>
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,item,advance,rest]
      congr 1
      exact decide_eq_decide.mpr ⟨fun later => .inr later,fun both => both.resolve_left (by simp [Denies])⟩
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- Reinterpreting anonymous individuals leaves the meaning of every proper
    concept unchanged. -/
theorem denote_with_anonymous {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (assignment : AnonymousIndividual → Object) :
    ∀ c, Proper c → ∀ x, denote (withAnonymous I assignment) c x ↔ denote I c x := by
  intro c
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ | HasSelf _ | NotSelf _ => intro _ x; exact Iff.rfl
  | One a =>
    intro proper x
    cases a with
    | Named _ => exact Iff.rfl
    | Anonymous _ => exact proper.elim
  | NotOne a =>
    intro proper x
    cases a with
    | Named _ => exact Iff.rfl
    | Anonymous _ => exact proper.elim
  | And a b iha ihb => intro proper x; simp only [denote,iha proper.1 x,ihb proper.2 x]
  | Or a b iha ihb => intro proper x; simp only [denote,iha proper.1 x,ihb proper.2 x]
  | Exists r c ih => intro proper x; simp only [denote,ih proper.2]; exact Iff.rfl
  | Forall r c ih => intro proper x; simp only [denote,ih proper.2]; exact Iff.rfl
  | AtLeast n r c ih => intro proper x; simp only [denote,ih proper.2]; exact Iff.rfl
  | AtMost n r c ih => intro proper x; simp only [denote,ih proper.2]; exact Iff.rfl

/-- The OWL interpretation of a tableau model relates along every object
    property expression without a built-in property as the tableau model does. -/
theorem owl_model_relation {Object : Type} (J : Interpretation Object Unit) (root : Object)
    (place : Individual → Object) {Native : Type w} (D : DatatypeMap Native) (r : ObjectPropertyExpression)
    (top : RoleOf r ≠ topObject) (bottom : RoleOf r ≠ bottomObject) (x y : ULift.{u} Object) :
    objectRelation (owlModel.{u,v,w} J root place D) r x y ↔ objectRelation J r x.down y.down := by
  cases r with
  | Property p =>
    simp only [RoleOf] at top bottom
    simp [objectRelation,owlModel,top,bottom]
  | Inverse p =>
    simp only [RoleOf] at top bottom
    simp [objectRelation,owlModel,top,bottom]

/-- Counting lifted elements counts the elements they lift. -/
theorem atLeast_lift {Object : Type} (n : Nat) (P : ULift.{u} Object → Prop) (Q : Object → Prop)
    (same : ∀ y, P y ↔ Q y.down) : Rowl.Owl.AtLeast n P ↔ Rowl.Owl.AtLeast n Q := by
  constructor
  · rintro ⟨f,injective,each⟩
    refine ⟨fun i => (f i).down,?_,fun i => (same (f i)).mp (each i)⟩
    intro i j equal
    exact injective (ULift.ext _ _ equal)
  · rintro ⟨f,injective,each⟩
    refine ⟨fun i => ULift.up (f i),?_,fun i => (same (ULift.up (f i))).mpr (each i)⟩
    intro i j equal
    exact injective (congrArg ULift.down equal)

private theorem individual_owl_model {Object : Type} (J : Interpretation Object Unit) (root : Object)
    (place : Individual → Object) {Native : Type w} (D : DatatypeMap Native) (a : Individual) :
    Rowl.Owl.individual (owlModel.{u,v,w} J root place D) a = ULift.up (place a) := by
  cases a <;> rfl

/-- On proper concepts whose nominals' individuals the tableau model places
    where `place` does, the constructed interpretation agrees with the tableau
    model. -/
theorem owl_model_agrees {Object : Type} (J : Interpretation Object Unit) (root : Object) (place : Individual → Object)
    {Native : Type w} (D : DatatypeMap Native) :
    ∀ c, Proper c → (∀ a, Mentions c a → Rowl.Owl.individual J a = place a) →
      ∀ x, denote (owlModel.{u,v,w} J root place D) c x ↔ denote J c x.down := by
  intro c
  induction c with
  | Top => intro _ _ x; simp [denote]
  | Bottom => intro _ _ x; simp [denote]
  | Atom k => intro proper _ x; simp [denote,owlModel,proper.1,proper.2]
  | NotAtom k => intro proper _ x; simp [denote,owlModel,proper.1,proper.2]
  | HasSelf r =>
    intro proper _ x
    simp only [denote]
    exact owl_model_relation J root place D r proper.1 proper.2 x x
  | NotSelf r =>
    intro proper _ x
    simp only [denote]
    exact not_congr (owl_model_relation J root place D r proper.1 proper.2 x x)
  | One a =>
    intro _ agree x
    simp only [denote,individual_owl_model,agree a rfl]
    exact ⟨fun same => by rw [← same],fun same => by rw [same]⟩
  | NotOne a =>
    intro _ agree x
    simp only [denote,individual_owl_model,agree a rfl]
    exact not_congr ⟨fun same => by rw [← same],fun same => by rw [same]⟩
  | And a b iha ihb =>
    intro proper agree x
    simp only [denote,iha proper.1 (fun c m => agree c (.inl m)) x,ihb proper.2 (fun c m => agree c (.inr m)) x]
  | Or a b iha ihb =>
    intro proper agree x
    simp only [denote,iha proper.1 (fun c m => agree c (.inl m)) x,ihb proper.2 (fun c m => agree c (.inr m)) x]
  | Exists r c ih =>
    intro proper agree x
    simp only [denote]
    constructor
    · rintro ⟨y,edge,inner⟩
      exact ⟨y.down,(owl_model_relation J root place D r proper.1.1 proper.1.2 x y).mp edge,
        (ih proper.2 agree y).mp inner⟩
    · rintro ⟨y,edge,inner⟩
      exact ⟨ULift.up y,(owl_model_relation J root place D r proper.1.1 proper.1.2 x (ULift.up y)).mpr edge,
        (ih proper.2 agree (ULift.up y)).mpr inner⟩
  | Forall r c ih =>
    intro proper agree x
    simp only [denote]
    constructor
    · intro every y edge
      exact (ih proper.2 agree (ULift.up y)).mp
        (every (ULift.up y) ((owl_model_relation J root place D r proper.1.1 proper.1.2 x (ULift.up y)).mpr edge))
    · intro every y edge
      exact (ih proper.2 agree y).mpr
        (every y.down ((owl_model_relation J root place D r proper.1.1 proper.1.2 x y).mp edge))
  | AtLeast n r c ih =>
    intro proper agree x
    simp only [denote]
    exact atLeast_lift n.val _ _ (fun y =>
      and_congr (owl_model_relation J root place D r proper.1.1 proper.1.2 x y) (ih proper.2 agree y))
  | AtMost n r c ih =>
    intro proper agree x
    simp only [denote,Rowl.Owl.AtMost]
    exact not_congr (atLeast_lift (n.val + 1) _ _ (fun y =>
      and_congr (owl_model_relation J root place D r proper.1.1 proper.1.2 x y) (ih proper.2 agree y)))

private theorem with_own_anonymous {Object : Type u} {Value : Type v} (I : Interpretation Object Value) :
    withAnonymous I I.anonymousIndividuals = I := by
  cases I; rfl

/-- A role axiom without built-in properties that holds in the tableau model
    holds in its OWL interpretation. -/
private theorem owl_model_role_axiom {Object : Type} (J : Interpretation Object Unit) (root : Object)
    (place : Individual → Object) {Native : Type w} (D : DatatypeMap Native) (a : Axiom) (role : RoleAxiom a)
    (proper : RoleProper a) (holds : Rowl.Owl.satisfies J a) :
    Rowl.Owl.satisfies (owlModel.{u,v,w} J root place D) a := by
  have relation := owl_model_relation.{u,v,w} J root place D
  cases a with
  | SubObjectPropertyOf sub sup =>
    cases sub with
    | Single p =>
      simp only [RoleProper] at proper
      simp only [Rowl.Owl.satisfies,Rowl.Owl.subRelation] at holds ⊢
      intro x y edge
      exact (relation sup proper.2.1 proper.2.2 x y).mpr
        (holds x.down y.down ((relation p proper.1.1 proper.1.2 x y).mp edge))
    | Chain _ => simp [RoleAxiom] at role
  | EquivalentObjectProperties members =>
    simp only [RoleProper] at proper
    simp only [Rowl.Owl.satisfies,Rowl.Owl.allEqual] at holds ⊢
    intro a aIn b bIn
    have equal := holds a aIn b bIn
    funext x y
    rw [propext (relation a (proper a aIn).1 (proper a aIn).2 x y),
      propext (relation b (proper b bIn).1 (proper b bIn).2 x y),equal]
  | InverseObjectProperties p q =>
    simp only [RoleProper] at proper
    simp only [Rowl.Owl.satisfies] at holds ⊢
    intro x y
    rw [relation p proper.1.1 proper.1.2 x y,relation q proper.2.1 proper.2.2 y x]
    exact holds x.down y.down
  | SymmetricObjectProperty p =>
    simp only [RoleProper] at proper
    simp only [Rowl.Owl.satisfies] at holds ⊢
    intro x y edge
    exact (relation p proper.1 proper.2 y x).mpr (holds x.down y.down ((relation p proper.1 proper.2 x y).mp edge))
  | TransitiveObjectProperty p =>
    simp only [RoleProper] at proper
    simp only [Rowl.Owl.satisfies] at holds ⊢
    intro x y z first second
    exact (relation p proper.1 proper.2 x z).mpr (holds x.down y.down z.down
      ((relation p proper.1 proper.2 x y).mp first) ((relation p proper.1 proper.2 y z).mp second))
  | _ => simp [RoleAxiom] at role

/-- An asymmetric or disjoint object property without built-in properties that
    holds in the tableau model holds in its OWL interpretation. -/
private theorem owl_model_constraint_axiom {Object : Type} (J : Interpretation Object Unit) (root : Object)
    (place : Individual → Object) {Native : Type w} (D : DatatypeMap Native) (a : Axiom)
    (constraint : ConstraintAxiom a) (proper : RoleProper a) (holds : Rowl.Owl.satisfies J a) :
    Rowl.Owl.satisfies (owlModel.{u,v,w} J root place D) a := by
  have relation := owl_model_relation.{u,v,w} J root place D
  cases a with
  | AsymmetricObjectProperty p =>
    simp only [RoleProper] at proper
    simp only [Rowl.Owl.satisfies] at holds ⊢
    intro x y forward backward
    exact holds x.down y.down ((relation p proper.1 proper.2 x y).mp forward)
      ((relation p proper.1 proper.2 y x).mp backward)
  | DisjointObjectProperties members =>
    simp only [RoleProper] at proper
    simp only [Rowl.Owl.satisfies,Rowl.Owl.pairwiseDisjoint] at holds ⊢
    refine holds.imp_of_mem ?_
    intro a b aIn bIn apart xy both
    exact apart (xy.1.down,xy.2.down) ⟨(relation a (proper a aIn).1 (proper a aIn).2 xy.1 xy.2).mp both.1,
      (relation b (proper b bIn).1 (proper b bIn).2 xy.1 xy.2).mp both.2⟩
  | _ => simp [ConstraintAxiom] at constraint

/-- What `prepare` computes from a closure: its individuals, including those of
    the nominals of its class parts and assertions, with room for one more node,
    the representatives of its equalities, its class parts, the facts of its
    class assertions, the facts the completion forest also gets, its role
    hierarchy and links at the representatives' nodes, every name ordinary,
    whether a negative assertion denies a link, whether every question goes to
    the completion forest, and whether an inequality has two members at one
    node. -/
structure PreparedData (items : alloc.vec.Vec AnnotatedAxiom) (p : shi_ontology.Prepared) : Prop where
  individuals : ∀ item ∈ items.val, ∀ a ∈ IndividualsOf item.axiom, a ∈ p.nodes.val
  members : ∀ item ∈ items.val, ∀ a ∈ MembersOf item.axiom, a ∈ p.nodes.val
  nominals : ∀ a, (Mentions p.parts.axioms a ∨ (∃ d ∈ p.parts.definitions.val, Mentions d.concept a) ∨
    ∃ q ∈ p.facts.val, Mentions q.concept a) → a ∈ p.nodes.val
  room : p.nodes.val.length ≤ Usize.max-1
  joins : Joins items.val p.nodes.val p.same.val
  parts : shi_ontology.class_parts items = .ok (some p.parts)
  facts : shi_ontology.assertions_from items p.nodes p.same 0#usize (alloc.vec.Vec.new completion.Fact) =
    .ok (some p.facts)
  boundOrigin : ∀ q ∈ p.bound.val, q ∈ p.facts.val ∨
    (∃ a ∈ p.nodes.val, q.node.val = RepOf p.same.val p.nodes.val a ∧ q.concept = .One a) ∨
    (∃ item ∈ items.val, ∃ xs, item.axiom = .DifferentIndividuals xs ∧ ∃ a b, [a,b].Sublist xs.elements ∧
      q.node.val = RepOf p.same.val p.nodes.val a ∧ q.concept = .NotOne b) ∨
    (∃ item ∈ items.val, ∃ r a b, item.axiom = .NegativeObjectPropertyAssertion r a b ∧
      q.node.val = RepOf p.same.val p.nodes.val a ∧ q.concept = .Forall r (.NotOne b))
  boundFacts : ∀ q ∈ p.facts.val, q ∈ p.bound.val
  boundNamed : ∀ a ∈ p.nodes.val, ∃ q ∈ p.bound.val,
    q.node.val = RepOf p.same.val p.nodes.val a ∧ q.concept = .One a
  boundApart : ∀ item ∈ items.val, ∀ xs, item.axiom = .DifferentIndividuals xs →
    xs.elements.Pairwise (fun a b => ∃ q ∈ p.bound.val,
      q.node.val = RepOf p.same.val p.nodes.val a ∧ q.concept = .NotOne b)
  boundRefused : ∀ item ∈ items.val, ∀ r a b, item.axiom = .NegativeObjectPropertyAssertion r a b →
    ∃ q ∈ p.bound.val, q.node.val = RepOf p.same.val p.nodes.val a ∧ q.concept = .Forall r (.NotOne b)
  roles : shi_ontology.role_hierarchy items = .ok (some p.roles)
  links : shi_ontology.links_from items p.nodes p.same 0#usize (alloc.vec.Vec.new completion.Link) =
    .ok (some p.links)
  axiomsProper : Proper p.parts.axioms
  definitionsProper : ∀ d ∈ p.parts.definitions.val, DefinitionProper d
  factsProper : ∀ q ∈ p.facts.val, Proper q.concept
  rolesProper : ∀ item ∈ items.val, RoleProper item.axiom
  denied : p.denied = true ↔ ∃ item ∈ items.val, Denies p.same.val p.nodes.val p.links.val item.axiom
  forest : p.forest = true ↔ (Counts p.parts.axioms ∨ (∃ d ∈ p.parts.definitions.val, Counts d.concept) ∨
    ∃ q ∈ p.facts.val, Counts q.concept) ∨ (Nominal p.parts.axioms ∨
      (∃ d ∈ p.parts.definitions.val, Nominal d.concept) ∨ ∃ q ∈ p.facts.val, Nominal q.concept) ∨
    ((∃ item ∈ items.val, Negative item.axiom) ∧ ¬ (p.roles.inclusions.val = [] ∧ p.roles.transitive.val = [])) ∨
    p.roles.disjoint.val ≠ []
  clash : p.clash = true ↔ ∃ item ∈ items.val, Clashes p.same.val p.nodes.val item.axiom

/-- The check for disjoint pairs, which only the completion forest decides, is
    exact. -/
theorem constrained_correct (h : hierarchy.RoleHierarchy) :
    shi_ontology.constrained h = .ok (decide (h.disjoint.val ≠ [])) := by
  rw [shi_ontology.constrained]
  have lenIff : alloc.vec.Vec.len h.disjoint = 0#usize ↔ h.disjoint.val = [] := by
    constructor
    · intro same
      have := congrArg UScalar.val same
      simpa using this
    · intro empty
      exact UScalar.eq_of_val_eq (by simp [empty])
  by_cases empty : h.disjoint.val = []
  · rw [lenIff.mpr empty]
    simp [empty]
  · have notZero : ¬ alloc.vec.Vec.len h.disjoint = 0#usize := fun zero => empty (lenIff.mp zero)
    simp [notZero,empty]

/-- The check for negative assertions next to role axioms is exact. -/
theorem tangled_correct (items : alloc.vec.Vec AnnotatedAxiom) (h : hierarchy.RoleHierarchy) :
    shi_ontology.tangled items h = .ok (decide ((∃ item ∈ items.val, Negative item.axiom) ∧
      ¬ (h.inclusions.val = [] ∧ h.transitive.val = []))) := by
  have negative := has_negative_correct items 0#usize
  rw [show (0#usize).val = 0 from rfl,List.drop_zero] at negative
  have inclusionsLen : alloc.vec.Vec.len h.inclusions = 0#usize ↔ h.inclusions.val = [] := by
    constructor
    · intro same
      have := congrArg UScalar.val same
      simpa using this
    · intro empty
      exact UScalar.eq_of_val_eq (by simp [empty])
  have transitiveLen : alloc.vec.Vec.len h.transitive = 0#usize ↔ h.transitive.val = [] := by
    constructor
    · intro same
      have := congrArg UScalar.val same
      simpa using this
    · intro empty
      exact UScalar.eq_of_val_eq (by simp [empty])
  rw [shi_ontology.tangled]
  by_cases yes : ∃ item ∈ items.val, Negative item.axiom
  · by_cases noInclusions : h.inclusions.val = []
    · by_cases noTransitive : h.transitive.val = []
      · simp only [negative,decide_eq_true yes,bind_ok,↓reduceIte,inclusionsLen.mpr noInclusions,
          transitiveLen.mpr noTransitive]
        simp [yes,noInclusions,noTransitive]
      · have notZero : ¬ alloc.vec.Vec.len h.transitive = 0#usize := fun zero => noTransitive (transitiveLen.mp zero)
        simp only [negative,decide_eq_true yes,bind_ok,↓reduceIte,inclusionsLen.mpr noInclusions,notZero]
        simp [yes,noTransitive]
    · have notZero : ¬ alloc.vec.Vec.len h.inclusions = 0#usize := fun zero => noInclusions (inclusionsLen.mp zero)
      simp only [negative,decide_eq_true yes,bind_ok,↓reduceIte,notZero]
      simp [yes,noInclusions]
  · simp [negative,yes]

/-- The preparation terminates, and a prepared closure is what `PreparedData` says. -/
theorem prepare_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ r, shi_ontology.prepare items = .ok r ∧ ∀ p, r = some p → PreparedData items p := by
  have zero : (0#usize).val = 0 := rfl
  obtain ⟨nodesResult,nodesRun,nodesSpec⟩ := individuals_from_correct items 0#usize (alloc.vec.Vec.new Individual)
    (by simp)
  rw [shi_ontology.prepare]
  cases nodesResult with
  | none => exact ⟨none,by simp [nodesRun],by simp⟩
  | some nodes0 =>
  obtain ⟨_,individualsIn,room0⟩ := nodesSpec nodes0 rfl
  obtain ⟨membersResult,membersRun,membersSpec⟩ := members_from_correct items 0#usize nodes0 room0
  cases membersResult with
  | none => exact ⟨none,by simp [nodesRun,membersRun],by simp⟩
  | some nodes1 =>
  obtain ⟨kept1,membersIn,room1⟩ := membersSpec nodes1 rfl
  rw [zero,List.drop_zero] at individualsIn membersIn
  obtain ⟨partsResult,partsRun,_,_,_⟩ := class_parts_correct.{0,0} items
  cases partsResult with
  | none => exact ⟨none,by simp [nodesRun,membersRun,partsRun],by simp⟩
  | some parts =>
  obtain ⟨r2,run2,spec2⟩ := nominal_individuals_correct parts.axioms nodes1 room1
  cases r2 with
  | none => exact ⟨none,by simp [nodesRun,membersRun,partsRun,run2],by simp⟩
  | some nodes2 =>
  obtain ⟨kept2,axiomsIn,room2⟩ := spec2 nodes2 rfl
  obtain ⟨r3,run3,spec3⟩ := definition_individuals_correct parts.definitions 0#usize nodes2 room2
  cases r3 with
  | none => exact ⟨none,by simp [nodesRun,membersRun,partsRun,run2,run3],by simp⟩
  | some nodes3 =>
  obtain ⟨kept3,definitionsIn,room3⟩ := spec3 nodes3 rfl
  obtain ⟨r4,run4,spec4⟩ := assertion_individuals_correct items 0#usize nodes3 room3
  cases r4 with
  | none => exact ⟨none,by simp [nodesRun,membersRun,partsRun,run2,run3,run4],by simp⟩
  | some nodes =>
  obtain ⟨kept4,assertionsIn,room⟩ := spec4 nodes rfl
  rw [zero,List.drop_zero] at definitionsIn assertionsIn
  have kept : ∀ b ∈ nodes1.val, b ∈ nodes.val := fun b member => kept4 b (kept3 b (kept2 b member))
  obtain ⟨count,countRun,countValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := nodes.len) (y := 1#usize) (by scalar_tac))
  have countIs : count.val = nodes.val.length + 1 := by simpa using countValue
  obtain ⟨start,same,startRun,sameRun,joins⟩ := joins_of items nodes count countIs
  obtain ⟨assertResult,assertRun,assertSpec⟩ := assertions_from_correct items nodes same 0#usize
    (alloc.vec.Vec.new _)
  cases assertResult with
  | none =>
    exact ⟨none,by simp [nodesRun,membersRun,partsRun,run2,run3,run4,countRun,startRun,sameRun,assertRun],
      by simp⟩
  | some facts =>
  obtain ⟨factsOrigin,_,_⟩ := assertSpec facts rfl
  obtain ⟨roleResult,roleRun,_⟩ := role_hierarchy_correct.{0,0} items
  cases roleResult with
  | none =>
    exact ⟨none,by simp [nodesRun,membersRun,partsRun,run2,run3,run4,countRun,startRun,sameRun,assertRun,
      roleRun],by simp⟩
  | some h =>
  have p2 := definitions_proper_correct parts.definitions 0#usize
  have p3 := facts_proper_correct facts 0#usize
  have p4 := roles_proper_correct items 0#usize
  rw [zero,List.drop_zero] at p2 p3 p4
  simp only [nodesRun,membersRun,partsRun,run2,run3,run4,countRun,startRun,sameRun,assertRun,roleRun,bind_ok]
  by_cases c1 : Proper parts.axioms
  swap
  · exact ⟨none,by simp [proper_correct,c1],by simp⟩
  by_cases c2 : ∀ d ∈ parts.definitions.val, DefinitionProper d
  swap
  · rw [decide_eq_false c2] at p2
    exact ⟨none,by simp [proper_correct,c1,p2],by simp⟩
  rw [decide_eq_true c2] at p2
  by_cases c3 : ∀ q ∈ facts.val, Proper q.concept
  swap
  · rw [decide_eq_false c3] at p3
    exact ⟨none,by simp [proper_correct,c1,p2,p3],by simp⟩
  rw [decide_eq_true c3] at p3
  by_cases c4 : ∀ item ∈ items.val, RoleProper item.axiom
  swap
  · rw [decide_eq_false c4] at p4
    exact ⟨none,by simp [proper_correct,c1,p2,p3,p4],by simp⟩
  rw [decide_eq_true c4] at p4
  simp only [proper_correct,decide_eq_true c1,p2,p3,p4,↓reduceIte,bind_ok]
  obtain ⟨linksResult,linksRun,_⟩ := links_from_correct items nodes same 0#usize (alloc.vec.Vec.new completion.Link)
  cases linksResult with
  | none => exact ⟨none,by simp [linksRun],by simp⟩
  | some links =>
  obtain ⟨r9,run9,spec9⟩ := named_from_correct nodes same 0#usize facts
  cases r9 with
  | none => exact ⟨none,by simp [linksRun,run9],by simp⟩
  | some bound1 =>
  obtain ⟨origin9,kept9,covered9⟩ := spec9 bound1 rfl
  obtain ⟨r10,run10,spec10⟩ := unequal_from_correct items nodes same 0#usize bound1
  cases r10 with
  | none => exact ⟨none,by simp [linksRun,run9,run10],by simp⟩
  | some bound2 =>
  obtain ⟨origin10,kept10,covered10⟩ := spec10 bound2 rfl
  obtain ⟨r11,run11,spec11⟩ := refused_from_correct items nodes same 0#usize bound2
  cases r11 with
  | none => exact ⟨none,by simp [linksRun,run9,run10,run11],by simp⟩
  | some bound =>
  obtain ⟨origin11,kept11,covered11⟩ := spec11 bound rfl
  rw [zero,List.drop_zero] at origin9 covered9 origin10 covered10 origin11 covered11
  have denial := denied_from_correct items nodes same links 0#usize
  have clashing := clash_from_correct items nodes same 0#usize
  rw [zero,List.drop_zero] at denial clashing
  simp only [linksRun,run9,run10,run11,bind_ok,denial,tangled_correct,constrained_correct,closure_counts_correct,
    closure_nominal_correct,clashing]
  refine ⟨some ⟨nodes,same,parts,facts,bound,h,links,
    decide (∃ item ∈ items.val, Denies same.val nodes.val links.val item.axiom),
    decide ((Counts parts.axioms ∨ (∃ d ∈ parts.definitions.val, Counts d.concept) ∨
      ∃ q ∈ facts.val, Counts q.concept) ∨ (Nominal parts.axioms ∨
        (∃ d ∈ parts.definitions.val, Nominal d.concept) ∨ ∃ q ∈ facts.val, Nominal q.concept) ∨
      ((∃ item ∈ items.val, Negative item.axiom) ∧ ¬ (h.inclusions.val = [] ∧ h.transitive.val = [])) ∨
      h.disjoint.val ≠ []),
    decide (∃ item ∈ items.val, Clashes same.val nodes.val item.axiom)⟩,?_,?_⟩
  · by_cases counting : Counts parts.axioms ∨ (∃ d ∈ parts.definitions.val, Counts d.concept) ∨
        ∃ q ∈ facts.val, Counts q.concept
    · simp [counting]
    · by_cases nominal : Nominal parts.axioms ∨ (∃ d ∈ parts.definitions.val, Nominal d.concept) ∨
          ∃ q ∈ facts.val, Nominal q.concept
      · simp [counting,nominal]
      · simp only [counting,nominal,false_or,decide_false,Bool.false_eq_true,↓reduceIte]
        split
        · rename_i isTangled
          rw [decide_eq_true_eq] at isTangled
          simp [isTangled]
        · rename_i notTangled
          rw [decide_eq_true_eq] at notTangled
          have same : decide (h.disjoint.val ≠ []) = decide ((∃ item ∈ items.val, Negative item.axiom) ∧
              ¬ (h.inclusions.val = [] ∧ h.transitive.val = []) ∨ h.disjoint.val ≠ []) :=
            decide_eq_decide.mpr ⟨fun nonempty => .inr nonempty,fun either => either.resolve_left notTangled⟩
          rw [same]
          simp only [bind_ok]
  intro p same'
  cases same'
  have factsKept : ∀ q ∈ facts.val, q ∈ bound.val := fun q member => kept11 q (kept10 q (kept9 q member))
  exact {
    individuals := fun item member a mentioned => kept a (kept1 a (individualsIn item member a mentioned)),
    members := fun item member a mentioned => kept a (membersIn item member a mentioned),
    nominals := by
      rintro a (inAxioms | ⟨d,dIn,inDefinition⟩ | ⟨q,qIn,inFact⟩)
      · exact kept4 a (kept3 a (axiomsIn a inAxioms))
      · exact kept4 a (definitionsIn d dIn a inDefinition)
      · rcases factsOrigin q qIn with impossible | ⟨item,itemIn,C,m,statement,_,read⟩
        · simp at impossible
        · rw [zero,List.drop_zero] at itemIn
          exact assertionsIn item itemIn C m statement q.concept read a inFact,
    room := room, joins := joins, parts := partsRun, facts := assertRun,
    boundOrigin := by
      intro q qIn
      rcases origin11 q qIn with in2 | refused
      · rcases origin10 q in2 with in1 | apart
        · rcases origin9 q in1 with old | named
          · exact .inl old
          · exact .inr (.inl named)
        · exact .inr (.inr (.inl apart))
      · exact .inr (.inr (.inr refused)),
    boundFacts := factsKept,
    boundNamed := fun a member => by
      obtain ⟨q,qIn,qNode,qConcept⟩ := covered9 a member
      exact ⟨q,kept11 q (kept10 q qIn),qNode,qConcept⟩,
    boundApart := fun item member xs statement =>
      (covered10 item member xs statement).imp (fun ⟨q,qIn,qNode,qConcept⟩ => ⟨q,kept11 q qIn,qNode,qConcept⟩),
    boundRefused := covered11,
    roles := roleRun, links := linksRun, axiomsProper := c1, definitionsProper := c2,
    factsProper := c3, rolesProper := c4, denied := by simp, forest := decide_eq_true_iff, clash := by simp }

/-- A prepared closure has supported axioms only. -/
theorem prepared_supported {items : alloc.vec.Vec AnnotatedAxiom} {p : shi_ontology.Prepared}
    (data : PreparedData items p) : ∀ a ∈ items.val, SupportedAxiom a.axiom := by
  obtain ⟨result,run,support,_,_⟩ := class_parts_correct.{0,0} items
  rw [data.parts] at run
  cases Result.ok_injective run
  exact support rfl

/-- The individuals of a prepared closure: every individual an assertion
    mentions, with room for one more node. -/
private theorem prepared_nodes {items : alloc.vec.Vec AnnotatedAxiom} {p : shi_ontology.Prepared}
    (data : PreparedData items p) :
    (∀ item ∈ items.val, ∀ a ∈ IndividualsOf item.axiom, a ∈ p.nodes.val) ∧ p.nodes.val.length ≤ Usize.max-1 :=
  ⟨data.individuals,data.room⟩

/-- The nodes of the facts, of the facts the completion forest also gets, and of
    the links of a prepared closure are its nodes. -/
private theorem prepared_in {items : alloc.vec.Vec AnnotatedAxiom} {p : shi_ontology.Prepared}
    (data : PreparedData items p) :
    (∀ q ∈ p.facts.val, q.node.val ≤ p.nodes.val.length) ∧
    (∀ q ∈ p.bound.val, q.node.val ≤ p.nodes.val.length) ∧
    (∀ l ∈ p.links.val, l.from.val ≤ p.nodes.val.length ∧ l.to.val ≤ p.nodes.val.length) := by
  obtain ⟨assertResult,assertRun',assertSpec⟩ :=
    assertions_from_correct items p.nodes p.same 0#usize (alloc.vec.Vec.new _)
  rw [data.facts] at assertRun'
  cases Result.ok_injective assertRun'
  obtain ⟨origin,_,_⟩ := assertSpec p.facts rfl
  obtain ⟨linksResult,linksRun',linksSpec⟩ := links_from_correct items p.nodes p.same 0#usize (alloc.vec.Vec.new _)
  rw [data.links] at linksRun'
  cases Result.ok_injective linksRun'
  obtain ⟨linkOrigin,_,_⟩ := linksSpec p.links rfl
  have factsIn : ∀ q ∈ p.facts.val, q.node.val ≤ p.nodes.val.length := by
    intro q member
    rcases origin q member with given | ⟨_,_,_,m,_,node,_⟩
    · simp at given
    · rw [node]; exact repOf_le data.joins m
  refine ⟨factsIn,?_,?_⟩
  · intro q member
    rcases data.boundOrigin q member with old | ⟨a,_,node,_⟩ | ⟨_,_,_,_,a,_,_,node,_⟩ | ⟨_,_,_,a,_,_,node,_⟩
    · exact factsIn q old
    · rw [node]; exact repOf_le data.joins a
    · rw [node]; exact repOf_le data.joins a
    · rw [node]; exact repOf_le data.joins a
  · intro l member
    rcases linkOrigin l member with given | ⟨_,_,_,s,t,_,_,source,target⟩
    · simp at given
    · rw [source,target]
      exact ⟨repOf_le data.joins s,repOf_le data.joins t⟩

/-- Under a placement of the individuals of an OWL model of the closure, every
    node and its representative are one element. -/
theorem placement_representative {items : alloc.vec.Vec AnnotatedAxiom} {p : shi_ontology.Prepared}
    (data : PreparedData items p) {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (satisfied : Rowl.Owl.satisfiesClosure I items.val) (f : Nat → Object)
    (placedAt : ∀ a ∈ p.nodes.val, f (PositionOf p.nodes.val a) = Rowl.Owl.individual I a) (n : Nat) :
    f (Representative p.same.val n) = f n := by
  apply representative_value data.joins f
  rintro i j ⟨item,itemIn,xs,statement,a,aIn,b,bIn,rfl,rfl⟩
  have holds := satisfied item itemIn
  rw [statement] at holds
  simp only [Rowl.Owl.satisfies,Rowl.Owl.allEqual] at holds
  rw [placedAt a (data.members item itemIn a (by simpa [statement,MembersOf] using aIn)),
    placedAt b (data.members item itemIn b (by simpa [statement,MembersOf] using bIn))]
  exact holds a aIn b bIn

/-- The check of a prepared closure with extra facts terminates and answers only
    on proper extra facts whose nominals are of individuals with nodes; an
    answer is `false` for an inequality with two members at one node, the
    completion forest's answer on the extra facts and the facts it also gets
    for a question that goes to it, and otherwise `false` for a denied link or
    the completion graph's answer, on the links, the TBox concept, the
    definitions and the roles. -/
private theorem prepared_correct (items : alloc.vec.Vec AnnotatedAxiom) (p : shi_ontology.Prepared)
    (data : PreparedData items p) (extra : alloc.vec.Vec completion.Fact)
    (extraIn : ∀ q ∈ extra.val, q.node.val ≤ p.nodes.val.length) :
    ∃ r, shi_ontology.prepared_satisfiable p extra = .ok r ∧ ∀ b, r = some b →
      (∀ q ∈ extra.val, Proper q.concept) ∧ (∀ q ∈ extra.val, ∀ a, Mentions q.concept a → a ∈ p.nodes.val) ∧
      ∃ count : Usize, count.val = p.nodes.val.length + 1 ∧
        ((p.clash = true ∧ b = false) ∨
          (p.clash = false ∧
            (p.forest = true ∨ (∃ q ∈ extra.val, Counts q.concept) ∨ ∃ q ∈ extra.val, Nominal q.concept) ∧
            forest.satisfiable count extra p.bound p.links p.parts.axioms p.parts.definitions p.roles =
              .ok (some b)) ∨
          (p.clash = false ∧ p.forest = false ∧ (∀ q ∈ extra.val, ¬ Counts q.concept) ∧
            (∀ q ∈ extra.val, ¬ Nominal q.concept) ∧
            ((p.denied = true ∧ b = false) ∨ (p.denied = false ∧
              completion.satisfiable count extra p.facts p.links p.parts.axioms p.parts.definitions p.roles =
                .ok (some b))))) := by
  have zero : (0#usize).val = 0 := rfl
  have room := data.room
  obtain ⟨factsIn,boundIn,linksIn⟩ := prepared_in data
  obtain ⟨roleResult,roleRun',roleSpec⟩ := role_hierarchy_correct.{0,0} items
  rw [data.roles] at roleRun'
  cases Result.ok_injective roleRun'
  obtain ⟨closed,_⟩ := roleSpec p.roles rfl
  have properCheck := facts_proper_correct extra 0#usize
  have knownCheck := facts_known_correct p.nodes extra 0#usize
  rw [zero,List.drop_zero] at properCheck knownCheck
  rw [shi_ontology.prepared_satisfiable]
  by_cases proper : ∀ q ∈ extra.val, Proper q.concept
  swap
  · rw [decide_eq_false proper] at properCheck
    exact ⟨none,by simp [properCheck],by simp⟩
  rw [decide_eq_true proper] at properCheck
  by_cases known : ∀ q ∈ extra.val, ∀ a, Mentions q.concept a → a ∈ p.nodes.val
  swap
  · rw [decide_eq_false known] at knownCheck
    exact ⟨none,by simp [properCheck,knownCheck],by simp⟩
  rw [decide_eq_true known] at knownCheck
  obtain ⟨count,countRun,countValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := p.nodes.len) (y := 1#usize) (by have := room; scalar_tac))
  have countIs : count.val = p.nodes.val.length + 1 := by simpa using countValue
  cases clashIs : p.clash with
  | true =>
    refine ⟨some false,by simp [properCheck,knownCheck,clashIs],?_⟩
    intro b same
    cases same
    exact ⟨proper,known,count,countIs,.inl ⟨rfl,rfl⟩⟩
  | false =>
  have linksIn' : ∀ l ∈ p.links.val, l.from.val < count.val ∧ l.to.val < count.val := by
    intro l member
    have := linksIn l member
    omega
  by_cases toForest : p.forest = true ∨ (∃ q ∈ extra.val, Counts q.concept) ∨ ∃ q ∈ extra.val, Nominal q.concept
  · have boundIn' : ∀ q ∈ extra.val ++ p.bound.val, q.node.val < count.val := by
      intro q member
      rcases List.mem_append.mp member with given | old
      · have := extraIn q given; omega
      · have := boundIn q old; omega
    obtain ⟨answer,answerRun,_,_⟩ := Rowl.ForestModel.satisfiable_correct.{0,0} count extra p.bound p.links
      p.parts.axioms p.parts.definitions p.roles closed (by omega) boundIn' linksIn'
    refine ⟨answer,by simp [properCheck,knownCheck,clashIs,question_forest_correct,toForest,countRun,answerRun],?_⟩
    intro b same
    exact ⟨proper,known,count,countIs,.inr (.inl ⟨rfl,toForest,by rw [answerRun,same]⟩)⟩
  · have notForest : p.forest = false := by
      cases forestIs : p.forest with
      | false => rfl
      | true => exact absurd (.inl forestIs) toForest
    have noCounts : ∀ q ∈ extra.val, ¬ Counts q.concept := fun q member counts =>
      toForest (.inr (.inl ⟨q,member,counts⟩))
    have noNominal : ∀ q ∈ extra.val, ¬ Nominal q.concept := fun q member nominal =>
      toForest (.inr (.inr ⟨q,member,nominal⟩))
    have factsIn' : ∀ q ∈ extra.val ++ p.facts.val, q.node.val < count.val := by
      intro q member
      rcases List.mem_append.mp member with given | old
      · have := extraIn q given; omega
      · have := factsIn q old; omega
    cases deniedIs : p.denied with
    | true =>
      refine ⟨some false,by simp [properCheck,knownCheck,clashIs,question_forest_correct,toForest,deniedIs],?_⟩
      intro b same
      cases same
      exact ⟨proper,known,count,countIs,.inr (.inr ⟨rfl,notForest,noCounts,noNominal,.inl ⟨rfl,rfl⟩⟩)⟩
    | false =>
      obtain ⟨answer,answerRun,_,_⟩ := Rowl.Completion.satisfiable_correct.{0,0} count extra p.facts p.links
        p.parts.axioms p.parts.definitions p.roles closed (by omega) factsIn' linksIn'
      refine ⟨answer,by simp [properCheck,knownCheck,clashIs,question_forest_correct,toForest,deniedIs,countRun,
        answerRun],?_⟩
      intro b same
      exact ⟨proper,known,count,countIs,.inr (.inr ⟨rfl,notForest,noCounts,noNominal,.inr ⟨rfl,by rw [answerRun,same]⟩⟩)⟩

/-- An accepting check of a prepared closure yields an OWL model of the closure
    in which every individual sits at the element of its node and every extra
    fact holds at the element of its node. -/
theorem prepared_sound (items : alloc.vec.Vec AnnotatedAxiom) (p : shi_ontology.Prepared)
    (data : PreparedData items p) (extra : alloc.vec.Vec completion.Fact)
    (extraIn : ∀ q ∈ extra.val, q.node.val ≤ p.nodes.val.length)
    (accepted : shi_ontology.prepared_satisfiable p extra = .ok (some true))
    {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary) (vocabulary : IsVocabulary D V) :
    ∃ (Object : Type u) (I : Interpretation Object (ULift.{v} (Option Native))) (f : Nat → Object),
      Model D (embedding.{v,w} D) V I items.val ∧
      (∀ a, Rowl.Owl.individual I a = f (RepOf p.same.val p.nodes.val a)) ∧
      ∀ q ∈ extra.val, denote I q.concept (f q.node.val) := by
  obtain ⟨result,run,spec⟩ := prepared_correct items p data extra extraIn
  rw [accepted] at run
  cases Result.ok_injective run
  obtain ⟨properExtra,knownExtra,count,countIs,outcome⟩ := spec true rfl
  obtain ⟨factsIn,boundIn,linksIn⟩ := prepared_in data
  obtain ⟨assertResult,assertRun',assertSpec⟩ :=
    assertions_from_correct items p.nodes p.same 0#usize (alloc.vec.Vec.new _)
  rw [data.facts] at assertRun'
  cases Result.ok_injective assertRun'
  obtain ⟨_,_,covered⟩ := assertSpec p.facts rfl
  obtain ⟨linksResult,linksRun',linksSpec⟩ := links_from_correct items p.nodes p.same 0#usize (alloc.vec.Vec.new _)
  rw [data.links] at linksRun'
  cases Result.ok_injective linksRun'
  obtain ⟨_,_,linkCovered⟩ := linksSpec p.links rfl
  obtain ⟨roleResult,roleRun',roleSpec⟩ := role_hierarchy_correct.{0,0} items
  rw [data.roles] at roleRun'
  cases Result.ok_injective roleRun'
  obtain ⟨closed,respectsIff⟩ := roleSpec p.roles rfl
  have factsIn' : ∀ q ∈ extra.val ++ p.facts.val, q.node.val < count.val := by
    intro q member
    rcases List.mem_append.mp member with given | old
    · have := extraIn q given; omega
    · have := factsIn q old; omega
  have boundIn' : ∀ q ∈ extra.val ++ p.bound.val, q.node.val < count.val := by
    intro q member
    rcases List.mem_append.mp member with given | old
    · have := extraIn q given; omega
    · have := boundIn q old; omega
  have linksIn' : ∀ l ∈ p.links.val, l.from.val < count.val ∧ l.to.val < count.val := by
    intro l member
    have := linksIn l member
    omega
  have repIn : ∀ a, RepOf p.same.val p.nodes.val a < count.val := fun a => by
    have := repOf_le data.joins a
    omega
  -- The individual of every nominal of the closure or the question has a node.
  have mentionedIn : ∀ a, (Mentions p.parts.axioms a ∨ (∃ d ∈ p.parts.definitions.val, Mentions d.concept a) ∨
      ∃ q ∈ extra.val ++ p.facts.val, Mentions q.concept a) → a ∈ p.nodes.val := by
    rintro a (inAxioms | inDefinition | ⟨q,qIn,inFact⟩)
    · exact data.nominals a (.inl inAxioms)
    · exact data.nominals a (.inr (.inl inDefinition))
    · rcases List.mem_append.mp qIn with given | old
      · exact knownExtra q given a inFact
      · exact data.nominals a (.inr (.inr ⟨q,old,inFact⟩))
  -- A model in `Type` from the tableau that answered, where no negative
  -- assertion relates its individuals, the members of every inequality are
  -- apart, and the individual of every nominal sits at its node.
  obtain ⟨Obj,J,π,respects,constrained,tbox,defs,factsHold,linksHold,negatives,apart,agree⟩ : ∃ (Obj : Type)
      (J : Interpretation Obj Unit) (π : Nat → Obj), Respects J p.roles ∧ Constrained J p.roles ∧
      (∀ y, denote J p.parts.axioms y) ∧
      (∀ d ∈ p.parts.definitions.val, ∀ y, J.classes d.class y → denote J d.concept y) ∧
      (∀ f ∈ extra.val ++ p.facts.val, denote J f.concept (π f.node.val)) ∧
      (∀ l ∈ p.links.val, objectRelation J l.role (π l.from.val) (π l.to.val)) ∧
      (∀ item ∈ items.val, ∀ r a b, item.axiom = .NegativeObjectPropertyAssertion r a b →
        ¬ objectRelation J r (π (RepOf p.same.val p.nodes.val a)) (π (RepOf p.same.val p.nodes.val b))) ∧
      (∀ item ∈ items.val, ∀ xs, item.axiom = .DifferentIndividuals xs →
        xs.elements.Pairwise (fun a b => π (RepOf p.same.val p.nodes.val a) ≠ π (RepOf p.same.val p.nodes.val b))) ∧
      (∀ a, (Mentions p.parts.axioms a ∨ (∃ d ∈ p.parts.definitions.val, Mentions d.concept a) ∨
        ∃ q ∈ extra.val ++ p.facts.val, Mentions q.concept a) →
          Rowl.Owl.individual J a = π (RepOf p.same.val p.nodes.val a)) := by
    rcases outcome with ⟨_,impossible⟩ | ⟨_,_,forestRun⟩ |
      ⟨notClash,notForest,_,noNominal,⟨_,impossible⟩ | ⟨notDenied,tableauRun⟩⟩
    · cases impossible
    · obtain ⟨forestResult,forestRun',sound,_⟩ := Rowl.ForestModel.satisfiable_correct.{0,0} count extra p.bound
        p.links p.parts.axioms p.parts.definitions p.roles closed (by omega) boundIn' linksIn'
      rw [forestRun] at forestRun'
      cases Result.ok_injective forestRun'
      obtain ⟨Obj,J,π,respects,constrained,tbox,defs,boundHold,linksHold⟩ := sound rfl
      -- Every individual sits where its nominal is.
      have named : ∀ a ∈ p.nodes.val, Rowl.Owl.individual J a = π (RepOf p.same.val p.nodes.val a) := by
        intro a member
        obtain ⟨q,qIn,qNode,qConcept⟩ := data.boundNamed a member
        have holds := boundHold q (List.mem_append_right _ qIn)
        rw [qConcept,qNode] at holds
        exact holds
      refine ⟨Obj,J,π,respects,constrained,tbox,defs,?_,linksHold,?_,?_,
        fun a mentioned => named a (mentionedIn a mentioned)⟩
      · intro f member
        rcases List.mem_append.mp member with given | old
        · exact boundHold f (List.mem_append_left _ given)
        · exact boundHold f (List.mem_append_right _ (data.boundFacts f old))
      · intro item member r a b statement related
        obtain ⟨q,qIn,qNode,qConcept⟩ := data.boundRefused item member r a b statement
        have holds := boundHold q (List.mem_append_right _ qIn)
        rw [qConcept,qNode] at holds
        have bIn : b ∈ p.nodes.val := data.individuals item member b (by simp [statement,IndividualsOf])
        exact holds _ related (named b bIn)
      · intro item member xs statement
        refine (data.boundApart item member xs statement).imp_of_mem ?_
        intro a b aIn bIn ⟨q,qIn,qNode,qConcept⟩ equal
        have holds := boundHold q (List.mem_append_right _ qIn)
        rw [qConcept,qNode] at holds
        have bNode : b ∈ p.nodes.val := data.members item member b (by simpa [statement,MembersOf] using bIn)
        apply holds
        rw [named b bNode,equal]
    · cases impossible
    · obtain ⟨tableau,tableauRun',sound,_⟩ := Rowl.Completion.satisfiable_correct.{0,0} count extra p.facts p.links
        p.parts.axioms p.parts.definitions p.roles closed (by omega) factsIn' linksIn'
      rw [tableauRun] at tableauRun'
      cases Result.ok_injective tableauRun'
      obtain ⟨Obj,J,π,respects,tbox,defs,factsHold,linksHold,exactLinks,injective⟩ := sound rfl
      -- No nominal reaches the completion graph tableau.
      have plain : ¬ (Nominal p.parts.axioms ∨ (∃ d ∈ p.parts.definitions.val, Nominal d.concept) ∨
          ∃ q ∈ p.facts.val, Nominal q.concept) := fun nominal => by
        have := data.forest.mpr (.inr (.inl nominal))
        rw [notForest] at this
        cases this
      -- No disjoint pair reaches the completion graph tableau.
      have noPairs : p.roles.disjoint.val = [] := by
        by_contra pairs
        have := data.forest.mpr (.inr (.inr (.inr pairs)))
        rw [notForest] at this
        cases this
      refine ⟨Obj,J,π,respects,Rowl.Hierarchy.constrained_of_empty J p.roles noPairs,tbox,defs,factsHold,linksHold,
        ?_,?_,?_⟩
      · intro item member r a b statement related
        have alone : p.roles.inclusions.val = [] ∧ p.roles.transitive.val = [] := by
          by_contra roles
          have := data.forest.mpr (.inr (.inr (.inl ⟨⟨item,member,by rw [statement]; trivial⟩,roles⟩)))
          rw [notForest] at this
          cases this
        obtain ⟨l,lIn,found⟩ := exactLinks alone.1 alone.2 r (RepOf p.same.val p.nodes.val a)
          (RepOf p.same.val p.nodes.val b) (repIn a) (repIn b) related
        have denies : ∃ item ∈ items.val, Denies p.same.val p.nodes.val p.links.val item.axiom := by
          refine ⟨item,member,?_⟩
          rw [statement]
          simp only [Denies]
          rcases found with ⟨fromIs,toIs,roleIs⟩ | ⟨toIs,fromIs,roleIs⟩
          · exact ⟨l,lIn,.inl ⟨fromIs,toIs,roleIs⟩⟩
          · refine ⟨l,lIn,.inr ⟨fromIs,toIs,?_⟩⟩
            rw [← roleIs,Rowl.Concepts.inv_inv]
        rw [data.denied.mpr denies] at notDenied
        cases notDenied
      · intro item member xs statement
        have whole : xs.elements.Pairwise
            (fun a b => RepOf p.same.val p.nodes.val a ≠ RepOf p.same.val p.nodes.val b) := by
          by_contra broken
          have clashes : ∃ item ∈ items.val, Clashes p.same.val p.nodes.val item.axiom :=
            ⟨item,member,by rw [statement]; exact broken⟩
          rw [data.clash.mpr clashes] at notClash
          cases notClash
        exact whole.imp (fun {a b} different equal => different (injective _ _ (repIn a) (repIn b) equal))
      · rintro a (inAxioms | ⟨d,dIn,inDefinition⟩ | ⟨q,qIn,inFact⟩)
        · exact absurd inAxioms (not_mentions _ (fun nominal => plain (.inl nominal)) a)
        · exact absurd inDefinition (not_mentions _ (fun nominal => plain (.inr (.inl ⟨d,dIn,nominal⟩))) a)
        · rcases List.mem_append.mp qIn with given | old
          · exact absurd inFact (not_mentions _ (noNominal q given) a)
          · exact absurd inFact (not_mentions _ (fun nominal => plain (.inr (.inr ⟨q,old,nominal⟩))) a)
  have properFacts : ∀ q ∈ extra.val ++ p.facts.val, Proper q.concept := by
    intro q member
    rcases List.mem_append.mp member with given | old
    · exact properExtra q given
    · exact data.factsProper q old
  let place := fun a => π (RepOf p.same.val p.nodes.val a)
  have valid := owl_model_valid.{u,v,w} J (π 0) place D V
  have fixes := fixes_of_interpretation valid
  have agrees := owl_model_agrees.{u,v,w} J (π 0) place D
  have individualAt := individual_owl_model.{u,v,w} J (π 0) place D
  have relation := owl_model_relation.{u,v,w} J (π 0) place D
  obtain ⟨partsResult,partsRun',_,_,partsMeaning⟩ := class_parts_correct.{u, max w v} items
  rw [data.parts] at partsRun'
  cases Result.ok_injective partsRun'
  have partsHold : PartsHold (owlModel.{u,v,w} J (π 0) place D) p.parts := by
    refine ⟨fun x => (agrees p.parts.axioms data.axiomsProper (fun a m => agree a (.inl m)) x).mpr (tbox x.down),?_⟩
    intro d member x classes
    have proper := data.definitionsProper d member
    have classesJ : J.classes d.class x.down := by
      simpa [owlModel,proper.1.1,proper.1.2] using classes
    exact (agrees d.concept proper.2 (fun a m => agree a (.inr (.inl ⟨d,member,m⟩))) x).mpr
      (defs d member x.down classesJ)
  have classParts := (partsMeaning p.parts rfl _ _ (owlModel.{u,v,w} J (π 0) place D) fixes).mp partsHold
  have rolesHold := (respectsIff Obj Unit J).1.mp respects
  have constraintsHold := (respectsIff Obj Unit J).2.mp constrained
  refine ⟨ULift.{u} Obj,owlModel.{u,v,w} J (π 0) place D,fun n => ULift.up (π n),
    ⟨vocabulary,valid,(owlModel.{u,v,w} J (π 0) place D).anonymousIndividuals,?_⟩,fun a => individualAt a,?_⟩
  · rw [with_own_anonymous]
    intro item member
    by_cases assertion : Assertion item.axiom
    · cases statement : item.axiom with
      | ClassAssertion C m =>
        obtain ⟨q,qIn,qNode,qRead⟩ := covered item (by simpa using member) C m statement
        have inBoth : q ∈ extra.val ++ p.facts.val := List.mem_append_right _ qIn
        have holds := factsHold q inBoth
        have lifted := (agrees q.concept (properFacts q inBoth) (fun a m => agree a (.inr (.inr ⟨q,inBoth,m⟩)))
          (ULift.up (π q.node.val))).mpr holds
        have meaningOf := (translate_meaning C true q.concept qRead _ fixes (ULift.up (π q.node.val))).mp lifted
        simp only [Rowl.Owl.satisfies,individualAt,place]
        rw [← qNode]
        exact meaningOf
      | ObjectPropertyAssertion r a b =>
        obtain ⟨l,lIn,role,source,target⟩ := linkCovered item (by simpa using member) r a b statement
        have holds := linksHold l lIn
        have proper := data.rolesProper item member
        rw [statement] at proper
        simp only [RoleProper] at proper
        simp only [Rowl.Owl.satisfies,individualAt,place]
        rw [relation r proper.1 proper.2]
        rw [role,source,target] at holds
        exact holds
      | NegativeObjectPropertyAssertion r a b =>
        have proper := data.rolesProper item member
        rw [statement] at proper
        simp only [RoleProper] at proper
        simp only [Rowl.Owl.satisfies,individualAt,place]
        rw [relation r proper.1 proper.2]
        exact negatives item member r a b statement
      | _ => simp [statement,Assertion] at assertion
    · by_cases equality : Equality item.axiom
      · cases statement : item.axiom with
        | SameIndividual xs =>
          simp only [Rowl.Owl.satisfies,Rowl.Owl.allEqual,individualAt,place]
          intro a aIn b bIn
          rw [data.joins.equal item member xs statement a aIn b bIn]
        | DifferentIndividuals xs =>
          simp only [Rowl.Owl.satisfies,individualAt,place]
          exact (apart item member xs statement).imp
            (fun {a b} different equal => different (congrArg ULift.down equal))
        | _ => simp [statement,Equality] at equality
      · by_cases role : RoleAxiom item.axiom
        · exact owl_model_role_axiom J (π 0) place D item.axiom role (data.rolesProper item member)
            (rolesHold item member role)
        · by_cases constraint : ConstraintAxiom item.axiom
          · exact owl_model_constraint_axiom J (π 0) place D item.axiom constraint (data.rolesProper item member)
              (constraintsHold item member constraint)
          · rcases classParts item member with assertion' | equality' | role' | constraint' | holds
            · exact absurd assertion' assertion
            · exact absurd equality' equality
            · exact absurd role' role
            · exact absurd constraint' constraint
            · exact holds
  · intro q member
    have inBoth : q ∈ extra.val ++ p.facts.val := List.mem_append_left _ member
    exact (agrees q.concept (properFacts q inBoth) (fun a m => agree a (.inr (.inr ⟨q,inBoth,m⟩)))
      (ULift.up (π q.node.val))).mpr (factsHold q inBoth)

/-- Any OWL model of the closure, in any universes, with an element for every
    node at which its individual sits and at which the extra facts hold, makes
    the check of the prepared closure accept. -/
theorem prepared_complete (items : alloc.vec.Vec AnnotatedAxiom) (p : shi_ontology.Prepared)
    (data : PreparedData items p) (extra : alloc.vec.Vec completion.Fact)
    (extraIn : ∀ q ∈ extra.val, q.node.val ≤ p.nodes.val.length) (answer : Bool)
    (answered : shi_ontology.prepared_satisfiable p extra = .ok (some answer))
    {Native : Type w} {D : DatatypeMap Native} {V : Vocabulary} {Object : Type u} {Value : Type v}
    {embed : ValueEmbedding D Value} {I : Interpretation Object Value} (valid : IsInterpretation D embed V I)
    (g : AnonymousIndividual → Object) (satisfied : Rowl.Owl.satisfiesClosure (withAnonymous I g) items.val)
    (f : Nat → Object)
    (placedAt : ∀ a ∈ p.nodes.val, f (PositionOf p.nodes.val a) = Rowl.Owl.individual (withAnonymous I g) a)
    (extraHolds : ∀ q ∈ extra.val, denote I q.concept (f q.node.val)) : answer = true := by
  obtain ⟨result,run,spec⟩ := prepared_correct items p data extra extraIn
  rw [answered] at run
  cases Result.ok_injective run
  obtain ⟨properExtra,_,count,countIs,outcome⟩ := spec answer rfl
  obtain ⟨factsIn,boundIn,linksIn⟩ := prepared_in data
  obtain ⟨assertResult,assertRun',assertSpec⟩ :=
    assertions_from_correct items p.nodes p.same 0#usize (alloc.vec.Vec.new _)
  rw [data.facts] at assertRun'
  cases Result.ok_injective assertRun'
  obtain ⟨origin,_,_⟩ := assertSpec p.facts rfl
  obtain ⟨linksResult,linksRun',linksSpec⟩ := links_from_correct items p.nodes p.same 0#usize (alloc.vec.Vec.new _)
  rw [data.links] at linksRun'
  cases Result.ok_injective linksRun'
  obtain ⟨linkOrigin,_,_⟩ := linksSpec p.links rfl
  have fixes : Fixes (withAnonymous I g) := fixes_of_interpretation valid
  have atRep : ∀ a ∈ p.nodes.val,
      f (RepOf p.same.val p.nodes.val a) = Rowl.Owl.individual (withAnonymous I g) a := by
    intro a present
    rw [RepOf,placement_representative data (withAnonymous I g) satisfied f placedAt]
    exact placedAt a present
  have mentionedAt : ∀ item ∈ items.val, ∀ a ∈ IndividualsOf item.axiom,
      f (RepOf p.same.val p.nodes.val a) = Rowl.Owl.individual (withAnonymous I g) a :=
    fun item member a inItem => atRep a (data.individuals item member a inItem)
  have zero : (0#usize).val = 0 := rfl
  have linkHolds : ∀ l ∈ p.links.val, objectRelation (withAnonymous I g) l.role (f l.from.val) (f l.to.val) := by
    intro l member
    rcases linkOrigin l member with given | ⟨item,itemIn,r,s,t,statement,role,source,target⟩
    · simp at given
    · rw [zero,List.drop_zero] at itemIn
      have holds := satisfied item itemIn
      rw [statement] at holds
      simp only [Rowl.Owl.satisfies] at holds
      rw [role,source,target,mentionedAt item itemIn s (by simp [statement,IndividualsOf]),
        mentionedAt item itemIn t (by simp [statement,IndividualsOf])]
      exact holds
  -- The facts of the class assertions and the extra facts hold.
  have factHolds : ∀ q ∈ p.facts.val, denote (withAnonymous I g) q.concept (f q.node.val) := by
    intro q old
    rcases origin q old with impossible | ⟨item,itemIn,C,m,statement,qNode,qRead⟩
    · simp at impossible
    · rw [zero,List.drop_zero] at itemIn
      have holds := satisfied item itemIn
      rw [statement] at holds
      have at_m := mentionedAt item itemIn m (by simp [statement,IndividualsOf])
      simp only [Rowl.Owl.satisfies] at holds
      rw [← at_m,← qNode] at holds
      exact (translate_meaning C true q.concept qRead _ fixes _).mpr holds
  have extraHolds' : ∀ q ∈ extra.val, denote (withAnonymous I g) q.concept (f q.node.val) :=
    fun q given => (denote_with_anonymous I g q.concept (properExtra q given) _).mpr (extraHolds q given)
  -- So do the facts the completion forest also gets.
  have boundHolds : ∀ q ∈ p.bound.val, denote (withAnonymous I g) q.concept (f q.node.val) := by
    intro q member
    rcases data.boundOrigin q member with old | ⟨a,aIn,qNode,qConcept⟩ |
      ⟨item,itemIn,xs,statement,a,b,sub,qNode,qConcept⟩ | ⟨item,itemIn,r,a,b,statement,qNode,qConcept⟩
    · exact factHolds q old
    · rw [qConcept,qNode]
      exact (atRep a aIn).symm
    · rw [qConcept,qNode]
      have holds := satisfied item itemIn
      rw [statement] at holds
      simp only [Rowl.Owl.satisfies] at holds
      have different := List.pairwise_pair.mp (holds.sublist sub)
      have aIn : a ∈ p.nodes.val := data.members item itemIn a (by
        rw [statement]
        exact sub.subset (List.mem_cons_self ..))
      intro equal
      rw [atRep a aIn] at equal
      exact different equal.symm
    · rw [qConcept,qNode]
      have holds := satisfied item itemIn
      rw [statement] at holds
      simp only [Rowl.Owl.satisfies] at holds
      intro y related equal
      apply holds
      rw [← mentionedAt item itemIn a (by simp [statement,IndividualsOf]),equal]
      exact related
  have factsIn' : ∀ q ∈ extra.val ++ p.facts.val, q.node.val < count.val := by
    intro q member
    rcases List.mem_append.mp member with given | old
    · have := extraIn q given; omega
    · have := factsIn q old; omega
  have boundIn' : ∀ q ∈ extra.val ++ p.bound.val, q.node.val < count.val := by
    intro q member
    rcases List.mem_append.mp member with given | old
    · have := extraIn q given; omega
    · have := boundIn q old; omega
  have linksIn' : ∀ l ∈ p.links.val, l.from.val < count.val ∧ l.to.val < count.val := by
    intro l member
    have := linksIn l member
    omega
  obtain ⟨roleResult,roleRun',roleSpec⟩ := role_hierarchy_correct.{u,v} items
  rw [data.roles] at roleRun'
  cases Result.ok_injective roleRun'
  obtain ⟨closed,respectsIff⟩ := roleSpec p.roles rfl
  obtain ⟨partsResult,partsRun',_,_,partsMeaning⟩ := class_parts_correct.{u,v} items
  rw [data.parts] at partsRun'
  cases Result.ok_injective partsRun'
  have partsHold := (partsMeaning p.parts rfl _ _ (withAnonymous I g) fixes).mpr
    (fun item member => .inr (.inr (.inr (.inr (satisfied item member)))))
  have respects := (respectsIff Object Value (withAnonymous I g)).1.mpr (fun item member _ => satisfied item member)
  have constrained := (respectsIff Object Value (withAnonymous I g)).2.mpr
    (fun item member _ => satisfied item member)
  rcases outcome with ⟨clashTrue,rfl⟩ | ⟨_,_,forestRun⟩ | ⟨_,_,_,_,⟨deniedTrue,rfl⟩ | ⟨_,tableauRun⟩⟩
  · exfalso
    obtain ⟨item,itemIn,clashes⟩ := data.clash.mp clashTrue
    cases statement : item.axiom with
    | DifferentIndividuals xs =>
      rw [statement] at clashes
      simp only [Clashes] at clashes
      apply clashes
      have holds := satisfied item itemIn
      rw [statement] at holds
      simp only [Rowl.Owl.satisfies] at holds
      refine holds.imp_of_mem ?_
      intro a b aIn bIn different equal
      apply different
      rw [← atRep a (data.members item itemIn a (by simpa [statement,MembersOf] using aIn)),
        ← atRep b (data.members item itemIn b (by simpa [statement,MembersOf] using bIn)),equal]
    | _ =>
      rw [statement] at clashes
      simp [Clashes] at clashes
  · obtain ⟨forestResult,forestRun',_,complete⟩ := Rowl.ForestModel.satisfiable_correct.{u,v} count extra p.bound
      p.links p.parts.axioms p.parts.definitions p.roles closed (by omega) boundIn' linksIn'
    rw [forestRun] at forestRun'
    cases Result.ok_injective forestRun'
    cases answer with
    | true => rfl
    | false =>
      refine absurd ⟨Object,Value,withAnonymous I g,f,respects,constrained,partsHold.1,partsHold.2,?_,linkHolds⟩
        (complete rfl)
      intro q member
      rcases List.mem_append.mp member with given | old
      · exact extraHolds' q given
      · exact boundHolds q old
  · exfalso
    obtain ⟨item,itemIn,denies⟩ := data.denied.mp deniedTrue
    cases statement : item.axiom with
    | NegativeObjectPropertyAssertion r s t =>
      rw [statement] at denies
      simp only [Denies] at denies
      obtain ⟨l,lIn,found⟩ := denies
      have holds := satisfied item itemIn
      rw [statement] at holds
      simp only [Rowl.Owl.satisfies] at holds
      have edge := linkHolds l lIn
      apply holds
      rw [← mentionedAt item itemIn s (by simp [statement,IndividualsOf]),
        ← mentionedAt item itemIn t (by simp [statement,IndividualsOf])]
      rcases found with ⟨fromIs,toIs,roleIs⟩ | ⟨fromIs,toIs,roleIs⟩
      · rw [roleIs,fromIs,toIs] at edge
        exact edge
      · rw [roleIs,fromIs,toIs,relation_inv] at edge
        exact edge
    | _ =>
      rw [statement] at denies
      simp [Denies] at denies
  · obtain ⟨tableau,tableauRun',_,complete⟩ := Rowl.Completion.satisfiable_correct.{u,v} count extra p.facts
      p.links p.parts.axioms p.parts.definitions p.roles closed (by omega) factsIn' linksIn'
    rw [tableauRun] at tableauRun'
    cases Result.ok_injective tableauRun'
    cases answer with
    | true => rfl
    | false =>
      refine absurd ⟨Object,Value,withAnonymous I g,f,respects,partsHold.1,partsHold.2,?_,linkHolds⟩ (complete rfl)
      intro q member
      rcases List.mem_append.mp member with given | old
      · exact extraHolds' q given
      · exact factHolds q old

private theorem single_fact (concept : concepts.Concept) (node : Usize) :
    ∃ extra, alloc.vec.Vec.push (alloc.vec.Vec.new completion.Fact) ⟨node,concept⟩ = .ok extra ∧
      extra.val = [⟨node,concept⟩] := by
  obtain ⟨extra,run,value⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new completion.Fact) ⟨node,concept⟩ (by simp; scalar_tac))
  exact ⟨extra,run,by simpa using value⟩

private theorem pair_facts (first second : concepts.Concept) :
    ∃ one extra, alloc.vec.Vec.push (alloc.vec.Vec.new completion.Fact) ⟨0#usize,first⟩ = .ok one ∧
      alloc.vec.Vec.push one ⟨0#usize,second⟩ = .ok extra ∧ extra.val = [⟨0#usize,first⟩,⟨0#usize,second⟩] := by
  obtain ⟨one,oneRun,oneValue⟩ := single_fact first 0#usize
  obtain ⟨two,twoRun,twoValue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec one ⟨0#usize,second⟩ (by rw [oneValue]; simp; scalar_tac))
  exact ⟨one,two,oneRun,twoRun,by rw [twoValue,oneValue]; rfl⟩

/-- Consistency of a prepared closure: the query terminates, and an answer is
    whether the closure has an OWL model. -/
theorem prepared_consistent_correct (items : alloc.vec.Vec AnnotatedAxiom) (p : shi_ontology.Prepared)
    (data : PreparedData items p) :
    ∃ result, shi_ontology.prepared_consistent p = .ok result ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ Consistent.{u, max w v, w} D V items.val) := by
  obtain ⟨_,room⟩ := prepared_nodes data
  obtain ⟨result,run,_⟩ := prepared_correct items p data (alloc.vec.Vec.new _) (by simp)
  refine ⟨result,by rw [shi_ontology.prepared_consistent]; exact run,?_⟩
  intro answer same Native D V vocabulary
  subst same
  constructor
  · intro yes
    subst yes
    obtain ⟨Object,I,f,model,_,_⟩ := prepared_sound.{u,v,w} items p data _ (by simp) run D V vocabulary
    exact ⟨Object,_,_,I,model⟩
  · rintro ⟨Object,Value,embed,I,_,valid,g,satisfied⟩
    obtain ⟨x⟩ := I.objectsNonempty
    exact prepared_complete.{u, max w v, w} items p data _ (by simp) answer run valid g satisfied
      (Placement (withAnonymous I g) p.nodes.val x) (fun a present => placement_at _ p.nodes.val x a present)
      (by simp)

/-- Class satisfiability with respect to a prepared closure: the query
    terminates, it answers only on translatable expressions, and an answer is whether
    some OWL model of the closure has an instance of the expression. -/
theorem prepared_class_satisfiable_correct (items : alloc.vec.Vec AnnotatedAxiom) (p : shi_ontology.Prepared)
    (data : PreparedData items p) (e : ClassExpression) :
    ∃ result, shi_ontology.prepared_class_satisfiable p e = .ok result ∧ (result.isSome → Translatable e) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ ClassSatisfiable.{u, max w v, w} D V items.val e) := by
  obtain ⟨translated,translatedRead,translatedCorrect⟩ := translate_total_correct.{0,0} e true
  rw [shi_ontology.prepared_class_satisfiable]
  cases translated with
  | none => exact ⟨none,by simp [translatedRead],by simp,by simp⟩
  | some concept =>
    obtain ⟨extra,extraRun,extraValue⟩ := single_fact concept 0#usize
    have extraIn : ∀ q ∈ extra.val, q.node.val ≤ p.nodes.val.length := by simp [extraValue]
    obtain ⟨result,run,_⟩ := prepared_correct items p data extra extraIn
    refine ⟨result,by simp [translatedRead,extraRun,run],fun _ => translatedCorrect.1,?_⟩
    intro answer same Native D V vocabulary
    subst same
    constructor
    · intro yes
      subst yes
      obtain ⟨Object,I,f,model,_,holds⟩ := prepared_sound.{u,v,w} items p data extra extraIn run D V vocabulary
      have fixes := fixes_of_interpretation model.2.1
      have member := holds ⟨0#usize,concept⟩ (by simp [extraValue])
      exact ⟨Object,_,_,I,model,f 0,(translate_meaning e true concept translatedRead I fixes (f 0)).mp member⟩
    · rintro ⟨Object,Value,embed,I,⟨_,valid,g,satisfied⟩,x,member⟩
      have fixes := fixes_of_interpretation valid
      exact prepared_complete.{u, max w v, w} items p data extra extraIn answer run valid g satisfied
        (Placement (withAnonymous I g) p.nodes.val x) (fun a present => placement_at _ p.nodes.val x a present)
        (by
          intro q qIn
          simp only [extraValue,List.mem_singleton] at qIn
          subst qIn
          simp only [placement_zero]
          exact (translate_meaning e true concept translatedRead I fixes x).mpr member)

/-- Subsumption with respect to a prepared closure: the query terminates, it
    answers only on translatable expressions, and an answer is whether every instance of
    `sub` is an instance of `sup` in every OWL model of the closure. -/
theorem prepared_subsumed_correct (items : alloc.vec.Vec AnnotatedAxiom) (p : shi_ontology.Prepared)
    (data : PreparedData items p) (sub sup : ClassExpression) :
    ∃ result, shi_ontology.prepared_subsumed p sub sup = .ok result ∧ (result.isSome → Translatable sub ∧ Translatable sup) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ Subsumed.{u, max w v, w} D V items.val sub sup) := by
  obtain ⟨insideResult,insideRead,insideCorrect⟩ := translate_total_correct.{0,0} sub true
  obtain ⟨outsideResult,outsideRead,outsideCorrect⟩ := translate_total_correct.{0,0} sup false
  rw [shi_ontology.prepared_subsumed]
  cases insideResult with
  | none => exact ⟨none,by simp [insideRead],by simp,by simp⟩
  | some inside =>
    cases outsideResult with
    | none => exact ⟨none,by simp [insideRead,outsideRead],by simp,by simp⟩
    | some outside =>
      obtain ⟨one,extra,oneRun,extraRun,extraValue⟩ := pair_facts inside outside
      have extraIn : ∀ q ∈ extra.val, q.node.val ≤ p.nodes.val.length := by
        intro q member; rw [extraValue] at member; simp at member; rcases member with rfl | rfl <;> simp
      obtain ⟨result,run,_⟩ := prepared_correct items p data extra extraIn
      refine ⟨result.map (fun satisfiable => decide ¬ satisfiable = true),?_,
        fun _ => ⟨insideCorrect.1,outsideCorrect.1⟩,?_⟩
      · simp only [insideRead,outsideRead,bind_ok,oneRun,extraRun,run]
        cases result <;> rfl
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
            have accepted := prepared_complete.{u, max w v, w} items p data extra extraIn satisfiable run valid g
              satisfied (Placement (withAnonymous I g) p.nodes.val x)
              (fun a present => placement_at _ p.nodes.val x a present)
              (by
                intro q qIn
                rw [extraValue] at qIn
                simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at qIn
                rcases qIn with rfl | rfl
                · simp only [placement_zero]
                  exact (translate_meaning sub true inside insideRead I fixes x).mpr member
                · simp only [placement_zero]
                  exact (translate_meaning sup false outside outsideRead I fixes x).mpr outsideSup)
            simp [accepted] at yes
          · intro subsumed
            cases satisfiable with
            | false => rfl
            | true =>
              exfalso
              obtain ⟨Object,I,f,model,_,holds⟩ := prepared_sound.{u,v,w} items p data extra extraIn run D V
                vocabulary
              have fixes := fixes_of_interpretation model.2.1
              have inSub := (translate_meaning sub true inside insideRead I fixes (f 0)).mp
                (holds ⟨0#usize,inside⟩ (by simp [extraValue]))
              have notSup := (translate_meaning sup false outside outsideRead I fixes (f 0)).mp
                (holds ⟨0#usize,outside⟩ (by simp [extraValue]))
              exact notSup (subsumed _ _ _ _ model _ inSub)

/-- Instance checking with respect to a prepared closure: the query terminates,
    it answers only on translatable expressions, and an answer is whether the named
    individual is an instance of the expression in every OWL model of the
    closure. -/
theorem prepared_instance_of_correct (items : alloc.vec.Vec AnnotatedAxiom) (p : shi_ontology.Prepared)
    (data : PreparedData items p) (a : NamedIndividual) (e : ClassExpression) :
    ∃ result, shi_ontology.prepared_instance_of p a e = .ok result ∧ (result.isSome → Translatable e) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ InstanceOf.{u, max w v, w} D V items.val a e) := by
  obtain ⟨translated,translatedRead,translatedCorrect⟩ := translate_total_correct.{0,0} e false
  rw [shi_ontology.prepared_instance_of]
  cases translated with
  | none => exact ⟨none,by simp [translatedRead],by simp,by simp⟩
  | some outside =>
    obtain ⟨node,nodeRun,nodeValue⟩ := node_of_correct p.nodes p.same (.Named a)
    have named : (Individual.Named { iri := a.iri } : Individual) = .Named a := by cases a; rfl
    obtain ⟨extra,extraRun,extraValue⟩ := single_fact outside node
    have extraIn : ∀ q ∈ extra.val, q.node.val ≤ p.nodes.val.length := by
      intro q member
      rw [extraValue,List.mem_singleton] at member
      subst member
      rw [nodeValue]
      exact repOf_le data.joins _
    obtain ⟨result,run,_⟩ := prepared_correct items p data extra extraIn
    refine ⟨result.map (fun satisfiable => decide ¬ satisfiable = true),?_,fun _ => translatedCorrect.1,?_⟩
    · simp only [translatedRead,bind_ok,Rowl.Nnf.copy_iri_identity,named,nodeRun,extraRun,run]
      cases result <;> rfl
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
          have located : Placement (withAnonymous I g) p.nodes.val (I.namedIndividuals a)
              (RepOf p.same.val p.nodes.val (.Named a)) = I.namedIndividuals a := by
            rw [RepOf,placement_representative data (withAnonymous I g) satisfied _
              (fun b present => placement_at _ p.nodes.val _ b present)]
            by_cases present : Individual.Named a ∈ p.nodes.val
            · rw [placement_at _ p.nodes.val _ _ present]; rfl
            · rw [show PositionOf p.nodes.val (.Named a) = 0 from positionFrom_absent p.nodes.val _ 0 present,
                placement_zero]
          have accepted := prepared_complete.{u, max w v, w} items p data extra extraIn satisfiable run valid g
            satisfied (Placement (withAnonymous I g) p.nodes.val (I.namedIndividuals a))
            (fun b present => placement_at _ p.nodes.val _ b present)
            (by
              intro q qIn
              rw [extraValue,List.mem_singleton] at qIn
              subst qIn
              simp only [nodeValue,located]
              exact (translate_meaning e false outside translatedRead I fixes _).mpr outsideClass)
          simp [accepted] at yes
        · intro instance'
          cases satisfiable with
          | false => rfl
          | true =>
            exfalso
            obtain ⟨Object,I,f,model,placed,holds⟩ := prepared_sound.{u,v,w} items p data extra extraIn run D V
              vocabulary
            have fixes := fixes_of_interpretation model.2.1
            have notIn := (translate_meaning e false outside translatedRead I fixes (f node.val)).mp
              (holds ⟨node,outside⟩ (by simp [extraValue]))
            have at_a : f node.val = I.namedIndividuals a := by
              rw [nodeValue,← placed (.Named a)]
              rfl
            rw [at_a] at notIn
            exact notIn (instance' _ _ _ _ model)

/-- Any OWL model of the closure, in any universes and for any vocabulary, makes
    a consistency answer of the prepared closure positive. -/
theorem prepared_consistent_complete (items : alloc.vec.Vec AnnotatedAxiom) (p : shi_ontology.Prepared)
    (data : PreparedData items p) (answer : Bool) (answered : shi_ontology.prepared_consistent p = .ok (some answer))
    {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary) (consistent : Consistent.{u,v,w} D V items.val) :
    answer = true := by
  rw [shi_ontology.prepared_consistent] at answered
  obtain ⟨Object,Value,embed,I,_,valid,g,satisfied⟩ := consistent
  obtain ⟨x⟩ := I.objectsNonempty
  exact prepared_complete.{u,v,w} items p data _ (by simp) answer answered valid g satisfied
    (Placement (withAnonymous I g) p.nodes.val x) (fun a present => placement_at _ p.nodes.val x a present) (by simp)

/-- An instance of the expression in any OWL model of the closure, in any
    universes and for any vocabulary, makes a satisfiability answer of the
    prepared closure positive. -/
theorem prepared_class_satisfiable_complete (items : alloc.vec.Vec AnnotatedAxiom) (p : shi_ontology.Prepared)
    (data : PreparedData items p) (e : ClassExpression) (answer : Bool)
    (answered : shi_ontology.prepared_class_satisfiable p e = .ok (some answer)) {Native : Type w}
    (D : DatatypeMap Native) (V : Vocabulary) (satisfiable : ClassSatisfiable.{u,v,w} D V items.val e) :
    answer = true := by
  obtain ⟨translated,translatedRead,_⟩ := translate_total_correct.{0,0} e true
  rw [shi_ontology.prepared_class_satisfiable] at answered
  cases translated with
  | none => simp [translatedRead] at answered
  | some concept =>
    obtain ⟨extra,extraRun,extraValue⟩ := single_fact concept 0#usize
    simp only [translatedRead,extraRun,bind_ok] at answered
    obtain ⟨Object,Value,embed,I,⟨_,valid,g,satisfied⟩,x,member⟩ := satisfiable
    have fixes := fixes_of_interpretation valid
    exact prepared_complete.{u,v,w} items p data extra (by simp [extraValue]) answer answered valid g satisfied
      (Placement (withAnonymous I g) p.nodes.val x) (fun a present => placement_at _ p.nodes.val x a present)
      (by
        intro q qIn
        simp only [extraValue,List.mem_singleton] at qIn
        subst qIn
        simp only [placement_zero]
        exact (translate_meaning e true concept translatedRead I fixes x).mpr member)

/-- A positive subsumption answer of a prepared closure holds in every OWL model
    of the closure, in any universes and for any vocabulary. -/
theorem prepared_subsumed_sound (items : alloc.vec.Vec AnnotatedAxiom) (p : shi_ontology.Prepared)
    (data : PreparedData items p) (sub sup : ClassExpression)
    (answered : shi_ontology.prepared_subsumed p sub sup = .ok (some true)) {Native : Type w} (D : DatatypeMap Native)
    (V : Vocabulary) : Subsumed.{u,v,w} D V items.val sub sup := by
  obtain ⟨insideResult,insideRead,_⟩ := translate_total_correct.{0,0} sub true
  obtain ⟨outsideResult,outsideRead,_⟩ := translate_total_correct.{0,0} sup false
  rw [shi_ontology.prepared_subsumed] at answered
  cases insideResult with
  | none => simp [insideRead] at answered
  | some inside =>
    cases outsideResult with
    | none => simp [insideRead,outsideRead] at answered
    | some outside =>
      obtain ⟨one,extra,oneRun,extraRun,extraValue⟩ := pair_facts inside outside
      have extraIn : ∀ q ∈ extra.val, q.node.val ≤ p.nodes.val.length := by
        intro q member; rw [extraValue] at member; simp at member; rcases member with rfl | rfl <;> simp
      obtain ⟨result,run,_⟩ := prepared_correct items p data extra extraIn
      simp only [insideRead,outsideRead,oneRun,extraRun,run,bind_ok] at answered
      cases result with
      | none => simp at answered
      | some satisfiable =>
        have notSatisfiable : satisfiable = false := by simpa using answered
        subst notSatisfiable
        intro Object Value embed I model x member
        obtain ⟨_,valid,g,satisfied⟩ := model
        have fixes := fixes_of_interpretation valid
        by_contra outsideSup
        have accepted := prepared_complete.{u,v,w} items p data extra extraIn false run valid g satisfied
          (Placement (withAnonymous I g) p.nodes.val x) (fun a present => placement_at _ p.nodes.val x a present)
          (by
            intro q qIn
            rw [extraValue] at qIn
            simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at qIn
            rcases qIn with rfl | rfl
            · simp only [placement_zero]
              exact (translate_meaning sub true inside insideRead I fixes x).mpr member
            · simp only [placement_zero]
              exact (translate_meaning sup false outside outsideRead I fixes x).mpr outsideSup)
        cases accepted

/-- A positive instance answer of a prepared closure holds in every OWL model of
    the closure, in any universes and for any vocabulary. -/
theorem prepared_instance_of_sound (items : alloc.vec.Vec AnnotatedAxiom) (p : shi_ontology.Prepared)
    (data : PreparedData items p) (a : NamedIndividual) (e : ClassExpression)
    (answered : shi_ontology.prepared_instance_of p a e = .ok (some true)) {Native : Type w} (D : DatatypeMap Native)
    (V : Vocabulary) : InstanceOf.{u,v,w} D V items.val a e := by
  obtain ⟨translated,translatedRead,_⟩ := translate_total_correct.{0,0} e false
  rw [shi_ontology.prepared_instance_of] at answered
  cases translated with
  | none => simp [translatedRead] at answered
  | some outside =>
    obtain ⟨node,nodeRun,nodeValue⟩ := node_of_correct p.nodes p.same (.Named a)
    have named : (Individual.Named { iri := a.iri } : Individual) = .Named a := by cases a; rfl
    obtain ⟨extra,extraRun,extraValue⟩ := single_fact outside node
    have extraIn : ∀ q ∈ extra.val, q.node.val ≤ p.nodes.val.length := by
      intro q member
      rw [extraValue,List.mem_singleton] at member
      subst member
      rw [nodeValue]
      exact repOf_le data.joins _
    obtain ⟨result,run,_⟩ := prepared_correct items p data extra extraIn
    simp only [translatedRead,bind_ok,Rowl.Nnf.copy_iri_identity,named,nodeRun,extraRun,run] at answered
    cases result with
    | none => simp at answered
    | some satisfiable =>
      have notSatisfiable : satisfiable = false := by simpa using answered
      subst notSatisfiable
      intro Object Value embed I model
      obtain ⟨_,valid,g,satisfied⟩ := model
      have fixes := fixes_of_interpretation valid
      by_contra outsideClass
      have located : Placement (withAnonymous I g) p.nodes.val (I.namedIndividuals a)
          (RepOf p.same.val p.nodes.val (.Named a)) = I.namedIndividuals a := by
        rw [RepOf,placement_representative data (withAnonymous I g) satisfied _
          (fun b present => placement_at _ p.nodes.val _ b present)]
        by_cases present : Individual.Named a ∈ p.nodes.val
        · rw [placement_at _ p.nodes.val _ _ present]; rfl
        · rw [show PositionOf p.nodes.val (.Named a) = 0 from positionFrom_absent p.nodes.val _ 0 present,
            placement_zero]
      have accepted := prepared_complete.{u,v,w} items p data extra extraIn false run valid g satisfied
        (Placement (withAnonymous I g) p.nodes.val (I.namedIndividuals a))
        (fun b present => placement_at _ p.nodes.val _ b present)
        (by
          intro q qIn
          rw [extraValue,List.mem_singleton] at qIn
          subst qIn
          simp only [nodeValue,located]
          exact (translate_meaning e false outside translatedRead I fixes _).mpr outsideClass)
      cases accepted

/-- Consistency of a SHOIQ axiom closure with assertions: the query terminates, it
    answers only when every axiom is supported, and an answer is whether the
    closure has an OWL model. -/
theorem consistent_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, shi_ontology.consistent items = .ok result ∧
      (result.isSome → ∀ a ∈ items.val, SupportedAxiom a.axiom) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ Consistent.{u, max w v, w} D V items.val) := by
  obtain ⟨prepared,prepareRun,prepareSpec⟩ := prepare_correct items
  rw [shi_ontology.consistent]
  cases prepared with
  | none => exact ⟨none,by simp [prepareRun],by simp,by simp⟩
  | some p =>
    have data := prepareSpec p rfl
    obtain ⟨result,run,semantic⟩ := prepared_consistent_correct.{u,v,w} items p data
    exact ⟨result,by simp [prepareRun,run],fun _ => prepared_supported data,semantic⟩

/-- Class satisfiability with respect to a SHOIQ axiom closure with assertions:
    the query terminates, it answers only when the expression is translatable and
    every axiom is supported, and an answer is whether some OWL model of the
    closure has an instance of the expression. -/
theorem class_satisfiable_correct (items : alloc.vec.Vec AnnotatedAxiom) (e : ClassExpression) :
    ∃ result, shi_ontology.class_satisfiable items e = .ok result ∧
      (result.isSome → Translatable e ∧ ∀ a ∈ items.val, SupportedAxiom a.axiom) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ ClassSatisfiable.{u, max w v, w} D V items.val e) := by
  obtain ⟨prepared,prepareRun,prepareSpec⟩ := prepare_correct items
  rw [shi_ontology.class_satisfiable]
  cases prepared with
  | none => exact ⟨none,by simp [prepareRun],by simp,by simp⟩
  | some p =>
    have data := prepareSpec p rfl
    obtain ⟨result,run,support,semantic⟩ := prepared_class_satisfiable_correct.{u,v,w} items p data e
    exact ⟨result,by simp [prepareRun,run],fun some => ⟨support some,prepared_supported data⟩,semantic⟩

/-- Subsumption with respect to a SHOIQ axiom closure with assertions: the query
    terminates, it answers only when both expressions are translatable and every
    axiom is supported, and an answer is whether every instance of `sub` is an
    instance of `sup` in every OWL model of the closure. -/
theorem subsumed_correct (items : alloc.vec.Vec AnnotatedAxiom) (sub sup : ClassExpression) :
    ∃ result, shi_ontology.subsumed items sub sup = .ok result ∧
      (result.isSome → Translatable sub ∧ Translatable sup ∧ ∀ a ∈ items.val, SupportedAxiom a.axiom) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ Subsumed.{u, max w v, w} D V items.val sub sup) := by
  obtain ⟨prepared,prepareRun,prepareSpec⟩ := prepare_correct items
  rw [shi_ontology.subsumed]
  cases prepared with
  | none => exact ⟨none,by simp [prepareRun],by simp,by simp⟩
  | some p =>
    have data := prepareSpec p rfl
    obtain ⟨result,run,support,semantic⟩ := prepared_subsumed_correct.{u,v,w} items p data sub sup
    exact ⟨result,by simp [prepareRun,run],
      fun some => ⟨(support some).1,(support some).2,prepared_supported data⟩,semantic⟩

/-- Instance checking with respect to a SHOIQ axiom closure with assertions: the
    query terminates, it answers only when the expression is translatable and every
    axiom is supported, and an answer is whether the named individual is an
    instance of the expression in every OWL model of the closure. -/
theorem instance_of_correct (items : alloc.vec.Vec AnnotatedAxiom) (a : NamedIndividual) (e : ClassExpression) :
    ∃ result, shi_ontology.instance_of items a e = .ok result ∧
      (result.isSome → Translatable e ∧ ∀ item ∈ items.val, SupportedAxiom item.axiom) ∧
      ∀ answer, result = some answer → ∀ {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary),
        IsVocabulary D V → (answer = true ↔ InstanceOf.{u, max w v, w} D V items.val a e) := by
  obtain ⟨prepared,prepareRun,prepareSpec⟩ := prepare_correct items
  rw [shi_ontology.instance_of]
  cases prepared with
  | none => exact ⟨none,by simp [prepareRun],by simp,by simp⟩
  | some p =>
    have data := prepareSpec p rfl
    obtain ⟨result,run,support,semantic⟩ := prepared_instance_of_correct.{u,v,w} items p data a e
    exact ⟨result,by simp [prepareRun,run],fun some => ⟨support some,prepared_supported data⟩,semantic⟩

/-- Any OWL model of the closure, in any universes and for any vocabulary, makes
    a consistency answer positive. -/
theorem consistent_complete (items : alloc.vec.Vec AnnotatedAxiom) (answer : Bool)
    (answered : shi_ontology.consistent items = .ok (some answer)) {Native : Type w} (D : DatatypeMap Native)
    (V : Vocabulary) (consistent : Consistent.{u,v,w} D V items.val) : answer = true := by
  obtain ⟨prepared,prepareRun,prepareSpec⟩ := prepare_correct items
  rw [shi_ontology.consistent] at answered
  cases prepared with
  | none => simp [prepareRun] at answered
  | some p =>
    simp only [prepareRun,bind_ok] at answered
    exact prepared_consistent_complete.{u,v,w} items p (prepareSpec p rfl) answer answered D V consistent

/-- An instance of the expression in any OWL model of the closure, in any
    universes and for any vocabulary, makes a satisfiability answer positive. -/
theorem class_satisfiable_complete (items : alloc.vec.Vec AnnotatedAxiom) (e : ClassExpression) (answer : Bool)
    (answered : shi_ontology.class_satisfiable items e = .ok (some answer)) {Native : Type w}
    (D : DatatypeMap Native) (V : Vocabulary) (satisfiable : ClassSatisfiable.{u,v,w} D V items.val e) :
    answer = true := by
  obtain ⟨prepared,prepareRun,prepareSpec⟩ := prepare_correct items
  rw [shi_ontology.class_satisfiable] at answered
  cases prepared with
  | none => simp [prepareRun] at answered
  | some p =>
    simp only [prepareRun,bind_ok] at answered
    exact prepared_class_satisfiable_complete.{u,v,w} items p (prepareSpec p rfl) e answer answered D V satisfiable

/-- A positive subsumption answer holds in every OWL model of the closure, in
    any universes and for any vocabulary. -/
theorem subsumed_sound (items : alloc.vec.Vec AnnotatedAxiom) (sub sup : ClassExpression)
    (answered : shi_ontology.subsumed items sub sup = .ok (some true)) {Native : Type w} (D : DatatypeMap Native)
    (V : Vocabulary) : Subsumed.{u,v,w} D V items.val sub sup := by
  obtain ⟨prepared,prepareRun,prepareSpec⟩ := prepare_correct items
  rw [shi_ontology.subsumed] at answered
  cases prepared with
  | none => simp [prepareRun] at answered
  | some p =>
    simp only [prepareRun,bind_ok] at answered
    exact prepared_subsumed_sound.{u,v,w} items p (prepareSpec p rfl) sub sup answered D V

/-- A positive instance answer holds in every OWL model of the closure, in any
    universes and for any vocabulary. -/
theorem instance_of_sound (items : alloc.vec.Vec AnnotatedAxiom) (a : NamedIndividual) (e : ClassExpression)
    (answered : shi_ontology.instance_of items a e = .ok (some true)) {Native : Type w} (D : DatatypeMap Native)
    (V : Vocabulary) : InstanceOf.{u,v,w} D V items.val a e := by
  obtain ⟨prepared,prepareRun,prepareSpec⟩ := prepare_correct items
  rw [shi_ontology.instance_of] at answered
  cases prepared with
  | none => simp [prepareRun] at answered
  | some p =>
    simp only [prepareRun,bind_ok] at answered
    exact prepared_instance_of_sound.{u,v,w} items p (prepareSpec p rfl) a e answered D V

end Rowl.ShiOntology
