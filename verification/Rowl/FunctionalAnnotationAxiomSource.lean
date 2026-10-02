import Rowl.FunctionalAnnotationAxioms
import Rowl.FunctionalPrefixResolution

namespace Rowl.FunctionalAnnotationAxiomSource
open Aeneas Aeneas.Std RowlRust
open RowlRust.functional_annotation_axioms RowlRust.functional_prefixes
open RowlRust.functional_annotations (AnnotationLimits)
open RowlRust.functional_lexer

/-- Annotation-axiom results use precisely the namespace rows actually parsed from
    the same original bytes and accepted by the normative table checker. Every
    result and first error has its independent derivation; the caller still
    supplies the axiom position, so no complete axiom sequence is asserted. -/
theorem source_prefix_annotation_axiom_result_iff (bytes : alloc.vec.Vec U8)
    (tokenLimit prefixCount prefixValue : Usize) (opening : PrefixHeader) (table : prefixes.PrefixTable)
    (tokens : Tokens) (limits : AnnotationLimits)
    (result : core.result.Result (SourceAnnotationAxiom × Tokens) AnnotationAxiomError)
    (parsed : read_prefix_header bytes tokenLimit prefixCount prefixValue = .ok (.Ok opening))
    (checked : prefixes.check opening.declarations = .ok (.Ready table)) :
    read_annotation_axiom table bytes tokens limits = .ok result ↔
      Rowl.FunctionalAnnotationAxioms.AxiomRun opening.declarations.val bytes.val bytes.len limits.count.val
        limits.iri.val limits.lexical.val limits.depth.val tokens result := by
  have same := (Rowl.FunctionalPrefixes.checked_source_prefix_table
    bytes tokenLimit prefixCount prefixValue opening table parsed checked).1
  simpa [same] using Rowl.FunctionalAnnotationAxioms.read_annotation_axiom_result_iff table bytes tokens limits result
end Rowl.FunctionalAnnotationAxiomSource
