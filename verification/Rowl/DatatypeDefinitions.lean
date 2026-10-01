import Rowl.RangeEquality
import Rowl.Builtins
import Rowl.Collection

namespace Rowl.DatatypeDefinitions
open Aeneas Aeneas.Std RowlRust.model RowlRust.typing RowlRust.datatype_definitions
open Rowl.RangeEquality
attribute [local instance] Classical.propDecidable
attribute [local simp] alloc.vec.Vec.eq_iff
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- The fixed reviewed OWL 2 datatype vocabulary, including rdfs:Literal.
    This identifies names only; it does not specify lexical or value spaces. -/
def Predefined (datatype : Iri) : Prop := Rowl.Builtins.role datatype.spelling.val = some .Datatype

/-- Exact defined-datatype identity in an actual datatype-definition axiom. -/
def Defines (item : AnnotatedAxiom) (datatype : Iri) : Prop :=
  match item.axiom with
  | .DatatypeDefinition defined _ => defined.iri = datatype
  | _ => False

/-- One nonempty equivalence class of annotated structural defining axioms. -/
def SingleDefinition (axioms : List AnnotatedAxiom) (datatype : Iri) : Prop :=
  (∃ item ∈ axioms, Defines item datatype) ∧
  (∀ left ∈ axioms, ∀ right ∈ axioms, Defines left datatype → Defines right datatype →
    DefinitionEq left right)

/-- Predefined datatypes have no redefining axiom; custom datatypes have exactly
    one structurally distinct defining axiom. Acyclicity is a separate condition. -/
def Available (axioms : List AnnotatedAxiom) (datatype : Iri) : Prop :=
  if Predefined datatype then ∀ item ∈ axioms, ¬ Defines item datatype
  else SingleDefinition axioms datatype

/-- Availability for every explicit datatype occurrence in the supplied rows. -/
def RowRestriction (axioms : List AnnotatedAxiom) (uses : List Rowl.Collection.Row) : Prop :=
  ∀ datatype, (datatype,EntityKind.Datatype) ∈ uses → Available axioms datatype

/-- Availability on the actual complete raw axiom closure, including recursive
    axiom annotations and literal/facet datatypes, excluding ontology annotations. -/
def Restriction (ontology : RawOntology) : Prop :=
  RowRestriction ontology.axioms.val (ontology.axioms.val.flatMap Rowl.Collection.annotatedUses)

/-- A local rejection identifies original axioms or the missing datatype and
    establishes that this datatype's availability condition is false. -/
def AtCorrect (axioms : List AnnotatedAxiom) (datatype : Iri) : DefinitionCheck → Prop
  | .Allowed => Available axioms datatype
  | .MissingDefinition missing => missing = datatype ∧ ¬ Predefined datatype ∧
      (∀ item ∈ axioms, ¬ Defines item datatype) ∧ ¬ Available axioms datatype
  | .PredefinedRedefined item => item ∈ axioms ∧ Predefined datatype ∧ Defines item datatype ∧
      ¬ Available axioms datatype
  | .MultipleDefinitions first second => first ∈ axioms ∧ second ∈ axioms ∧ ¬ Predefined datatype ∧
      Defines first datatype ∧ Defines second datatype ∧ ¬ DefinitionEq first second ∧
      ¬ Available axioms datatype

/-- Exact acceptance or an original witnessed failure at an actually occurring
    datatype. No caller-provided occurrence summary is assumed correct. -/
def Correct (axioms : List AnnotatedAxiom) (uses : List Rowl.Collection.Row) : DefinitionCheck → Prop
  | .Allowed => RowRestriction axioms uses
  | failure => (∃ datatype, (datatype,EntityKind.Datatype) ∈ uses ∧ AtCorrect axioms datatype failure) ∧
      ¬ RowRestriction axioms uses

/-- Recognition of the reviewed predefined vocabulary is total and exact. -/
theorem predefined_total_correct (datatype : Iri) :
    predefined datatype = .ok (decide (Predefined datatype)) := by
  cases found : Rowl.Builtins.role datatype.spelling.val with
  | none => simp [predefined,Rowl.Builtins.builtin_kind_total_correct,Predefined,found]
  | some kind => cases kind <;>
      simp [predefined,Rowl.Builtins.builtin_kind_total_correct,Predefined,found]

private theorem iri_eq (left right : Iri) : left.spelling.val = right.spelling.val ↔ left = right := by
  cases left; cases right; simp

/-- The actual predicate recognizes exactly the datatype defined by an axiom. -/
theorem defines_total_correct (item : AnnotatedAxiom) (datatype : Iri) :
    defines item datatype = .ok (decide (Defines item datatype)) := by
  cases h : item.axiom <;>
    simp [defines,Defines,h,Rowl.Symbols.same_spelling_total_correct,iri_eq]

private theorem first_total (axioms : alloc.vec.Vec AnnotatedAxiom) (datatype : Iri) (index : Usize) :
    first_from axioms datatype index =
      .ok ((axioms.val.drop index.val).find? (fun item => decide (Defines item datatype))) := by
  rw [first_from]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    rw [List.drop_eq_getElem_cons inside,List.find?_cons]
    by_cases defined : Defines axioms.val[index.val] datatype
    · simp [inside,alloc.vec.Vec.index_slice_index,lookup,defines_total_correct,defined]
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using nextval
      have recursive := first_total axioms datatype next
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,defines_total_correct,defined,advance,recursive,nv]
  · have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty]
termination_by axioms.val.length - index.val
decreasing_by omega

private def Conflict (datatype : Iri) (first item : AnnotatedAxiom) : Prop :=
  Defines item datatype ∧ ¬ DefinitionEq first item

private theorem distinct_total (axioms : alloc.vec.Vec AnnotatedAxiom) (datatype : Iri)
    (first : AnnotatedAxiom) (index : Usize) :
    distinct_from axioms datatype first index = .ok ((axioms.val.drop index.val).find?
      (fun item => decide (Conflict datatype first item))) := by
  rw [distinct_from]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    rw [List.drop_eq_getElem_cons inside,List.find?_cons]
    obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nv : next.val = index.val + 1 := by simpa using nextval
    have recursive := distinct_total axioms datatype first next
    by_cases defined : Defines axioms.val[index.val] datatype <;>
      by_cases equal : DefinitionEq first axioms.val[index.val] <;>
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,defines_total_correct,
        same_definition_total_correct,Conflict,defined,equal,advance,recursive,nv]
  · have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty]
termination_by axioms.val.length - index.val
decreasing_by omega

private theorem find_none {α : Type} (xs : List α) (p : α → Prop) :
    xs.find? (fun item => decide (p item)) = none ↔ ∀ item ∈ xs, ¬ p item := by
  induction xs with
  | nil => simp
  | cons head tail ih => by_cases h : p head <;> simp [List.find?_cons,h,ih]

private theorem find_some {α : Type} (xs : List α) (p : α → Prop) (item : α)
    (found : xs.find? (fun item => decide (p item)) = some item) : item ∈ xs ∧ p item := by
  induction xs with
  | nil => simp at found
  | cons head tail ih =>
    by_cases h : p head
    · simp [List.find?_cons,h] at found
      subst item; exact ⟨List.mem_cons_self,h⟩
    · have remaining : tail.find? (fun item => decide (p item)) = some item := by
        simpa [List.find?_cons,h] using found
      obtain ⟨member,holds⟩ := ih remaining
      exact ⟨List.mem_cons_of_mem head member,holds⟩

private theorem single_of_representative (axioms : List AnnotatedAxiom) (datatype : Iri)
    (first : AnnotatedAxiom) (member : first ∈ axioms) (defined : Defines first datatype)
    (equal : ∀ item ∈ axioms, Defines item datatype → DefinitionEq first item) :
    SingleDefinition axioms datatype := by
  refine ⟨⟨first,member,defined⟩,?_⟩
  intro left leftMem right rightMem leftDefined rightDefined
  exact definition_eq_trans left first right
    (definition_eq_symm first left (equal left leftMem leftDefined))
    (equal right rightMem rightDefined)

private theorem check_one_total (axioms : alloc.vec.Vec AnnotatedAxiom) (datatype : Iri) :
    ∃ result, check_one axioms datatype = .ok result ∧ AtCorrect axioms.val datatype result := by
  cases found : axioms.val.find? (fun item => decide (Defines item datatype)) with
  | none =>
    have absent := (find_none axioms.val (fun item => Defines item datatype)).mp found
    by_cases builtIn : Predefined datatype
    · refine ⟨.Allowed,by simp [check_one,predefined_total_correct,first_total,found,builtIn],?_⟩
      simpa [AtCorrect,Available,builtIn] using absent
    · refine ⟨.MissingDefinition datatype,
        by simp [check_one,predefined_total_correct,first_total,found,builtIn],rfl,builtIn,absent,?_⟩
      intro valid
      have single : SingleDefinition axioms.val datatype := by simpa [Available,builtIn] using valid
      obtain ⟨item,member,defined⟩ := single.1
      exact absent item member defined
  | some first =>
    obtain ⟨firstMem,firstDefined⟩ := find_some axioms.val (fun item => Defines item datatype) first found
    by_cases builtIn : Predefined datatype
    · refine ⟨.PredefinedRedefined first,
        by simp [check_one,predefined_total_correct,first_total,found,builtIn],firstMem,builtIn,firstDefined,?_⟩
      intro valid
      have absent : ∀ item ∈ axioms.val, ¬ Defines item datatype := by simpa [Available,builtIn] using valid
      exact absent first firstMem firstDefined
    · cases conflict : axioms.val.find?
        (fun item => decide (Conflict datatype first item)) with
      | none =>
        have allSame := (find_none axioms.val
          (fun item => Conflict datatype first item)).mp conflict
        have single : SingleDefinition axioms.val datatype :=
          single_of_representative axioms.val datatype first firstMem firstDefined
            (fun item member defined => by
              by_contra different; exact allSame item member ⟨defined,different⟩)
        refine ⟨.Allowed,
          by simp [check_one,predefined_total_correct,first_total,distinct_total,found,builtIn,conflict],?_⟩
        simpa [AtCorrect,Available,builtIn] using single
      | some second =>
        obtain ⟨secondMem,secondDefined,different⟩ := find_some axioms.val
          (fun item => Conflict datatype first item) second conflict
        refine ⟨.MultipleDefinitions first second,
          by simp [check_one,predefined_total_correct,first_total,distinct_total,found,builtIn,conflict],
          firstMem,secondMem,builtIn,firstDefined,secondDefined,different,?_⟩
        intro valid
        have single : SingleDefinition axioms.val datatype := by simpa [Available,builtIn] using valid
        exact different (single.2 first firstMem second secondMem firstDefined secondDefined)

private theorem at_reject (axioms : List AnnotatedAxiom) (datatype : Iri) (result : DefinitionCheck)
    (failure : result ≠ .Allowed) (correct : AtCorrect axioms datatype result) :
    ¬ Available axioms datatype := by
  cases result with
  | Allowed => exact False.elim (failure rfl)
  | MissingDefinition missing => exact correct.2.2.2
  | PredefinedRedefined item => exact correct.2.2.2
  | MultipleDefinitions first second => exact correct.2.2.2.2.2.2

private theorem correct_witness (axioms : List AnnotatedAxiom) (uses : List Rowl.Collection.Row)
    (datatype : Iri) (result : DefinitionCheck) (failure : result ≠ .Allowed)
    (member : (datatype,EntityKind.Datatype) ∈ uses) (correct : AtCorrect axioms datatype result) :
    Correct axioms uses result := by
  have rejected : ¬ RowRestriction axioms uses :=
    fun valid => at_reject axioms datatype result failure correct (valid datatype member)
  cases result with
  | Allowed => exact False.elim (failure rfl)
  | MissingDefinition _ | PredefinedRedefined _ | MultipleDefinitions _ _ =>
    all_goals exact ⟨⟨datatype,member,correct⟩,rejected⟩

private theorem correct_cons (axioms : List AnnotatedAxiom) (uses : List Rowl.Collection.Row)
    (iri : Iri) (kind : EntityKind) (result : DefinitionCheck)
    (tailCorrect : Correct axioms uses result) (head : kind = .Datatype → Available axioms iri) :
    Correct axioms ((iri,kind)::uses) result := by
  by_cases allowed : result = .Allowed
  · subst result
    intro datatype member
    rcases List.mem_cons.mp member with equal | member
    · have eqs : datatype = iri ∧ EntityKind.Datatype = kind := Prod.mk.inj equal
      rcases eqs with ⟨rfl,kindEq⟩
      exact head kindEq.symm
    · exact tailCorrect datatype member
  · have witness : ∃ datatype, (datatype,EntityKind.Datatype) ∈ uses ∧ AtCorrect axioms datatype result := by
      cases result with
      | Allowed => exact False.elim (allowed rfl)
      | MissingDefinition _ | PredefinedRedefined _ | MultipleDefinitions _ _ =>
        all_goals exact tailCorrect.1
    obtain ⟨datatype,member,localCorrect⟩ := witness
    exact correct_witness axioms ((iri,kind)::uses) datatype result allowed
      (List.mem_cons_of_mem _ member) localCorrect

private theorem check_uses_total (axioms : alloc.vec.Vec AnnotatedAxiom)
    (uses : RowlRust.collection.EntityUses) :
    ∃ result, check_uses axioms uses = .ok result ∧ Correct axioms.val (Rowl.Collection.rows uses) result := by
  rw [check_uses.eq_def]
  cases uses with
  | Empty => exact ⟨.Allowed,rfl,by simp [Correct,RowRestriction,Rowl.Collection.rows]⟩
  | Entry iri kind next =>
    obtain ⟨tailResult,tailExecuted,tailCorrect⟩ := check_uses_total axioms next
    cases kind with
    | Datatype =>
      obtain ⟨result,executed,correct⟩ := check_one_total axioms iri
      cases result with
      | Allowed =>
        exact ⟨tailResult,by simp [executed,tailExecuted],
          correct_cons axioms.val (Rowl.Collection.rows next) iri .Datatype tailResult tailCorrect (fun _ => correct)⟩
      | MissingDefinition missing =>
        exact ⟨.MissingDefinition missing,by simp [executed],
          correct_witness axioms.val (Rowl.Collection.rows (.Entry iri .Datatype next)) iri
            (.MissingDefinition missing) (by simp) (by simp [Rowl.Collection.rows]) correct⟩
      | PredefinedRedefined item =>
        exact ⟨.PredefinedRedefined item,by simp [executed],
          correct_witness axioms.val (Rowl.Collection.rows (.Entry iri .Datatype next)) iri
            (.PredefinedRedefined item) (by simp) (by simp [Rowl.Collection.rows]) correct⟩
      | MultipleDefinitions first second =>
        exact ⟨.MultipleDefinitions first second,by simp [executed],
          correct_witness axioms.val (Rowl.Collection.rows (.Entry iri .Datatype next)) iri
            (.MultipleDefinitions first second) (by simp) (by simp [Rowl.Collection.rows]) correct⟩
    | Class | ObjectProperty | DataProperty | AnnotationProperty | NamedIndividual =>
      all_goals refine ⟨tailResult,by simp [tailExecuted],?_⟩
      all_goals exact correct_cons axioms.val (Rowl.Collection.rows next) iri _ tailResult tailCorrect (by simp)
termination_by sizeOf uses
decreasing_by all_goals simp_wf

/-- The actual Rust closure operation terminates and has exact acceptance or an
    original witnessed rejection for every explicit datatype occurrence. -/
theorem check_definitions_total_correct (ontology : RawOntology) :
    ∃ result, check_definitions ontology = .ok result ∧
      Correct ontology.axioms.val (ontology.axioms.val.flatMap Rowl.Collection.annotatedUses) result := by
  obtain ⟨collected,collectExecuted,collectCorrect⟩ := Rowl.Collection.axiom_closure_entities_total_correct ontology
  obtain ⟨result,executed,correct⟩ := check_uses_total ontology.axioms collected.uses
  refine ⟨result,by simp [check_definitions,collectExecuted,executed],?_⟩
  simpa only [collectCorrect.2] using correct

/-- No false acceptance or rejection for definition availability and uniqueness.
    This theorem does not establish datatype-definition acyclicity or value spaces. -/
theorem check_definitions_accepted_iff (ontology : RawOntology) :
    check_definitions ontology = .ok .Allowed ↔ Restriction ontology := by
  obtain ⟨result,executed,correct⟩ := check_definitions_total_correct ontology
  rw [executed]
  cases result with
  | Allowed => simp [Correct,Restriction] at correct ⊢; exact correct
  | MissingDefinition missing => simp [Correct] at correct; simp [Restriction,correct.2]
  | PredefinedRedefined item => simp [Correct] at correct; simp [Restriction,correct.2]
  | MultipleDefinitions first second => simp [Correct] at correct; simp [Restriction,correct.2]

end Rowl.DatatypeDefinitions
