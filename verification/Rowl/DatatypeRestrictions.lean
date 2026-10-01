import Rowl.DatatypeDefinitions
import Rowl.DatatypeOrder
import Rowl.DatatypePositions

namespace Rowl.DatatypeRestrictions
open Aeneas Aeneas.Std RowlRust.model RowlRust.datatype_restrictions
set_option linter.unusedSimpArgs false

/-- Both normative §11.2 datatype-definition conditions on the supplied complete
    raw closure. Lexical/facet/value spaces and custom positions are separate. -/
def Restriction (ontology : RawOntology) : Prop :=
  Rowl.DatatypeDefinitions.Restriction ontology ∧ Rowl.DatatypeOrder.Restriction ontology.axioms.val

/-- Original evidence and rejection of the conjunction. A cycle additionally
    establishes successful availability/uniqueness; that stage has priority. -/
def Correct (ontology : RawOntology) : DatatypeDefinitionCheck → Prop
  | .Allowed => Restriction ontology
  | .MissingDefinition value =>
      Rowl.DatatypeDefinitions.Correct ontology.axioms.val
        (ontology.axioms.val.flatMap Rowl.Collection.annotatedUses) (.MissingDefinition value) ∧ ¬ Restriction ontology
  | .PredefinedRedefined item =>
      Rowl.DatatypeDefinitions.Correct ontology.axioms.val
        (ontology.axioms.val.flatMap Rowl.Collection.annotatedUses) (.PredefinedRedefined item) ∧ ¬ Restriction ontology
  | .MultipleDefinitions first second =>
      Rowl.DatatypeDefinitions.Correct ontology.axioms.val
        (ontology.axioms.val.flatMap Rowl.Collection.annotatedUses) (.MultipleDefinitions first second) ∧ ¬ Restriction ontology
  | .Cycle smaller larger => Rowl.DatatypeDefinitions.Restriction ontology ∧
      Rowl.DatatypeOrder.Correct (Rowl.DatatypeOrder.closureEdges ontology.axioms.val) (.Cycle smaller larger) ∧
      ¬ Restriction ontology

/-- The actual composite operation terminates, accepts exactly the conjunction
    and preserves original diagnostics with availability-before-order priority. -/
theorem check_definition_rules_total_correct (ontology : RawOntology) :
    ∃ result, check_definition_rules ontology = .ok result ∧ Correct ontology result := by
  obtain ⟨availability,availableExecuted,availableCorrect⟩ :=
    Rowl.DatatypeDefinitions.check_definitions_total_correct ontology
  cases availability with
  | MissingDefinition value =>
    refine ⟨.MissingDefinition value,by simp [check_definition_rules,availableExecuted],availableCorrect,?_⟩
    intro valid; exact availableCorrect.2 valid.1
  | PredefinedRedefined item =>
    refine ⟨.PredefinedRedefined item,by simp [check_definition_rules,availableExecuted],availableCorrect,?_⟩
    intro valid; exact availableCorrect.2 valid.1
  | MultipleDefinitions first second =>
    refine ⟨.MultipleDefinitions first second,by simp [check_definition_rules,availableExecuted],availableCorrect,?_⟩
    intro valid; exact availableCorrect.2 valid.1
  | Allowed =>
    obtain ⟨order,orderExecuted,orderCorrect⟩ := Rowl.DatatypeOrder.check_acyclic_total_correct ontology.axioms
    have carrier := Rowl.DatatypeOrder.order_on_iff_order (Rowl.DatatypeOrder.DatatypeNodes ontology.axioms.val)
      (Rowl.DatatypeOrder.closureEdges ontology.axioms.val) (Rowl.DatatypeOrder.dependency_support ontology.axioms.val)
    cases order with
    | Acyclic =>
      exact ⟨.Allowed,by simp [check_definition_rules,availableExecuted,orderExecuted],availableCorrect,carrier.mpr orderCorrect⟩
    | Cycle smaller larger =>
      refine ⟨.Cycle smaller larger,by simp [check_definition_rules,availableExecuted,orderExecuted],
        availableCorrect,orderCorrect,?_⟩
      intro valid; exact orderCorrect.2.2 (carrier.mp valid.2)

/-- Exact complete acceptance of availability, uniqueness, predefined protection
    and datatype-definition dependency order from the original supplied closure. -/
theorem check_definition_rules_accepted_iff (ontology : RawOntology) :
    check_definition_rules ontology = .ok .Allowed ↔ Restriction ontology := by
  obtain ⟨result,executed,correct⟩ := check_definition_rules_total_correct ontology
  rw [executed]
  cases result with
  | Allowed => simp [Correct] at correct; simp [correct]
  | MissingDefinition value => simp [Correct] at correct; simp [correct.2]
  | PredefinedRedefined item => simp [Correct] at correct; simp [correct.2]
  | MultipleDefinitions first second => simp [Correct] at correct; simp [correct.2]
  | Cycle smaller larger => simp [Correct] at correct; simp [correct.2.2]

/-- Definition availability, dependency order and all defined-datatype positions
    in the supplied closure and ontology annotations. Lexical/facet validity is separate. -/
def StructuralRestriction (ontology : RawOntology) : Prop :=
  Restriction ontology ∧ Rowl.DatatypePositions.OntologyOK ontology

/-- Every rejection retains original stage evidence and establishes earlier
    stages, in definition/ordering/ontology-annotation/axiom-position priority. -/
def StructuralCorrect (ontology : RawOntology) : StructuralDatatypeCheck → Prop
  | .Allowed => StructuralRestriction ontology
  | .MissingDefinition value => Correct ontology (.MissingDefinition value) ∧ ¬ StructuralRestriction ontology
  | .PredefinedRedefined item => Correct ontology (.PredefinedRedefined item) ∧ ¬ StructuralRestriction ontology
  | .MultipleDefinitions first second => Correct ontology (.MultipleDefinitions first second) ∧ ¬ StructuralRestriction ontology
  | .Cycle smaller larger => Correct ontology (.Cycle smaller larger) ∧ ¬ StructuralRestriction ontology
  | .ForbiddenOntologyAnnotation item => Restriction ontology ∧
      Rowl.DatatypePositions.Correct ontology (.OntologyAnnotation item) ∧ ¬ StructuralRestriction ontology
  | .ForbiddenAxiomPosition item => Restriction ontology ∧
      Rowl.DatatypePositions.Correct ontology (.Axiom item) ∧ ¬ StructuralRestriction ontology

/-- Actual source-linked composition is total with exact conjunction acceptance,
    original diagnostics and checked priority through every datatype structural stage. -/
theorem check_structural_datatypes_total_correct (ontology : RawOntology) :
    ∃ result, check_structural_datatypes ontology = .ok result ∧ StructuralCorrect ontology result := by
  obtain ⟨definitions,executed,correct⟩ := check_definition_rules_total_correct ontology
  cases definitions with
  | MissingDefinition value =>
    refine ⟨.MissingDefinition value,by simp [check_structural_datatypes,executed],correct,?_⟩
    intro valid; exact correct.2 valid.1
  | PredefinedRedefined item =>
    refine ⟨.PredefinedRedefined item,by simp [check_structural_datatypes,executed],correct,?_⟩
    intro valid; exact correct.2 valid.1
  | MultipleDefinitions first second =>
    refine ⟨.MultipleDefinitions first second,by simp [check_structural_datatypes,executed],correct,?_⟩
    intro valid; exact correct.2 valid.1
  | Cycle smaller larger =>
    refine ⟨.Cycle smaller larger,by simp [check_structural_datatypes,executed],correct,?_⟩
    intro valid; exact correct.2.2 valid.1
  | Allowed =>
    obtain ⟨positions,posExecuted,posCorrect⟩ := Rowl.DatatypePositions.check_ontology_positions_total_correct ontology
    cases positions with
    | Allowed => exact ⟨.Allowed,by simp [check_structural_datatypes,executed,posExecuted],correct,posCorrect⟩
    | OntologyAnnotation item =>
      refine ⟨.ForbiddenOntologyAnnotation item,by simp [check_structural_datatypes,executed,posExecuted],correct,posCorrect,?_⟩
      intro valid; exact posCorrect.2 valid.2
    | Axiom item =>
      refine ⟨.ForbiddenAxiomPosition item,by simp [check_structural_datatypes,executed,posExecuted],correct,posCorrect,?_⟩
      intro valid; exact posCorrect.2.2 valid.2

/-- No false acceptance or rejection for the combined independent structural
    datatype conditions; other DL and concrete datatype validation stay separate. -/
theorem check_structural_datatypes_accepted_iff (ontology : RawOntology) :
    check_structural_datatypes ontology = .ok .Allowed ↔ StructuralRestriction ontology := by
  obtain ⟨result,executed,correct⟩ := check_structural_datatypes_total_correct ontology
  rw [executed]
  cases result with
  | Allowed => simp [StructuralCorrect] at correct; simp [correct]
  | MissingDefinition value => simp [StructuralCorrect] at correct; simp [correct.2]
  | PredefinedRedefined item => simp [StructuralCorrect] at correct; simp [correct.2]
  | MultipleDefinitions first second => simp [StructuralCorrect] at correct; simp [correct.2]
  | Cycle smaller larger => simp [StructuralCorrect] at correct; simp [correct.2]
  | ForbiddenOntologyAnnotation item => simp [StructuralCorrect] at correct; simp [correct.2.2]
  | ForbiddenAxiomPosition item => simp [StructuralCorrect] at correct; simp [correct.2.2]

end Rowl.DatatypeRestrictions
