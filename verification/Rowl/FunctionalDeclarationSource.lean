import Rowl.FunctionalDeclarations
import Rowl.FunctionalPrefixResolution

namespace Rowl.FunctionalDeclarationSource
open Aeneas Aeneas.Std RowlFrontendRust
open RowlFrontendRust.functional_declarations RowlFrontendRust.functional_prefixes
open RowlFrontendRust.functional_annotations (AnnotationLimits)
open RowlFrontendRust.functional_lexer

/-- Declaration results use precisely the namespace rows actually parsed from the
    same original bytes and accepted by the normative table checker. Every result
    and first error has its independent derivation; the caller still supplies the
    axiom position, so no complete axiom sequence or ontology is asserted. -/
theorem source_prefix_declaration_result_iff (bytes : alloc.vec.Vec U8) (tokenLimit prefixCount prefixValue : Usize)
    (opening : PrefixHeader) (table : prefixes.PrefixTable) (tokens : Tokens) (limits : AnnotationLimits)
    (result : core.result.Result (SourceDeclaration × Tokens) DeclarationError)
    (parsed : read_prefix_header bytes tokenLimit prefixCount prefixValue = .ok (.Ok opening))
    (checked : prefixes.check opening.declarations = .ok (.Ready table)) :
    read_declaration table bytes tokens limits = .ok result ↔
      Rowl.FunctionalDeclarations.DeclarationRun opening.declarations.val bytes.val bytes.len limits.count.val
        limits.iri.val limits.lexical.val limits.depth.val tokens result := by
  have same := (Rowl.FunctionalPrefixes.checked_source_prefix_table
    bytes tokenLimit prefixCount prefixValue opening table parsed checked).1
  simpa [same] using Rowl.FunctionalDeclarations.read_declaration_result_iff table bytes tokens limits result
end Rowl.FunctionalDeclarationSource
