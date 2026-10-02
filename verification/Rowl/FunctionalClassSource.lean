import Rowl.FunctionalClassAxioms
import Rowl.FunctionalPrefixResolution

/-!
Class expressions and class axioms read against the namespace rows actually
parsed from the same original bytes and accepted by the normative table checker.
-/
namespace Rowl.FunctionalClassSource
open Aeneas Aeneas.Std RowlRust
open RowlRust.functional_classes RowlRust.functional_class_axioms RowlRust.functional_prefixes
open RowlRust.functional_annotations (AnnotationLimits)
open RowlRust.functional_lexer

/-- Class-expression results use precisely the namespace rows parsed from the
    same original bytes. The caller still supplies the position. -/
theorem source_prefix_class_result_iff (bytes : alloc.vec.Vec U8) (tokenLimit prefixCount prefixValue : Usize)
    (opening : PrefixHeader) (table : prefixes.PrefixTable) (tokens : Tokens) (limits : ClassLimits)
    (result : core.result.Result (SourceClass × Tokens) ClassError)
    (parsed : read_prefix_header bytes tokenLimit prefixCount prefixValue = .ok (.Ok opening))
    (checked : prefixes.check opening.declarations = .ok (.Ready table)) :
    read_class_expression table bytes tokens limits = .ok result ↔
      Rowl.FunctionalClasses.ClassRun opening.declarations.val bytes.val bytes.len limits.count.val limits.iri.val
        limits.depth.val tokens result := by
  have same := (Rowl.FunctionalPrefixes.checked_source_prefix_table
    bytes tokenLimit prefixCount prefixValue opening table parsed checked).1
  simpa [same] using Rowl.FunctionalClasses.read_class_expression_result_iff table bytes tokens limits result
/-- Class-axiom results use precisely the namespace rows parsed from the same
    original bytes; every result and first error has its independent derivation.
    The caller still supplies the axiom position, so no complete axiom sequence or
    ontology is asserted. -/
theorem source_prefix_class_axiom_result_iff (bytes : alloc.vec.Vec U8) (tokenLimit prefixCount prefixValue : Usize)
    (opening : PrefixHeader) (table : prefixes.PrefixTable) (tokens : Tokens) (annotations : AnnotationLimits)
    (classes : ClassLimits) (result : core.result.Result (SourceClassAxiom × Tokens) ClassAxiomError)
    (parsed : read_prefix_header bytes tokenLimit prefixCount prefixValue = .ok (.Ok opening))
    (checked : prefixes.check opening.declarations = .ok (.Ready table)) :
    read_class_axiom table bytes tokens annotations classes = .ok result ↔
      Rowl.FunctionalClassAxioms.AxiomRun opening.declarations.val bytes.val bytes.len annotations.count.val
        annotations.iri.val annotations.lexical.val annotations.depth.val classes.count.val classes.iri.val
        classes.depth.val tokens result := by
  have same := (Rowl.FunctionalPrefixes.checked_source_prefix_table
    bytes tokenLimit prefixCount prefixValue opening table parsed checked).1
  simpa [same] using Rowl.FunctionalClassAxioms.read_class_axiom_result_iff table bytes tokens annotations classes result
end Rowl.FunctionalClassSource
