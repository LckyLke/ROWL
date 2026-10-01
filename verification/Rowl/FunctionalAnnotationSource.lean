import Rowl.FunctionalAnnotations
import Rowl.FunctionalHeaderSource

namespace Rowl.FunctionalAnnotationSource
open Aeneas Aeneas.Std RowlFrontendRust
open RowlFrontendRust.functional_annotations RowlFrontendRust.functional_prefixes
open RowlFrontendRust.functional_lexer RowlFrontendRust.functional
open RowlFrontendRust.functional_header (HeaderTail read_header_tail)

/-- Annotation results use precisely the namespace rows actually parsed from the
    same original bytes and accepted by the normative table checker. Every
    result and first error has its independent sequence derivation. -/
theorem source_prefix_annotations_result_iff (bytes : alloc.vec.Vec U8) (tokenLimit prefixCount prefixValue : Usize)
    (opening : PrefixHeader) (table : prefixes.PrefixTable) (tokens : Tokens) (limits : AnnotationLimits)
    (result : core.result.Result SourceAnnotations AnnotationError)
    (parsed : read_prefix_header bytes tokenLimit prefixCount prefixValue = .ok (.Ok opening))
    (checked : prefixes.check opening.declarations = .ok (.Ready table)) :
    read_annotations table bytes tokens limits = .ok result ↔
      Rowl.FunctionalAnnotations.ScanRun opening.declarations.val bytes.val bytes.len limits.count.val
        limits.iri.val limits.lexical.val limits.depth.val tokens [] result := by
  have same := (Rowl.FunctionalPrefixes.checked_source_prefix_table
    bytes tokenLimit prefixCount prefixValue opening table parsed checked).1
  simpa [same] using Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes tokens limits result

/-- Whole-source prefix lexing/parsing, normative table checking, ontology header
    reading and ontology-annotation reading compose on the same original bytes.
    The annotations form exactly the maximal independent section after the
    header, within the count and nesting limits, and the remaining stream starts
    at the first non-`Annotation` token. Axioms and the closing token remain
    unparsed, so this partial stage does not establish a complete ontology. -/
theorem source_ontology_annotations (bytes : alloc.vec.Vec U8) (tokenLimit prefixCount prefixValue : Usize)
    (opening : PrefixHeader) (table : prefixes.PrefixTable) (importCount headerLimit : Usize) (header : HeaderTail)
    (limits : AnnotationLimits) (output : SourceAnnotations)
    (parsed : read_prefix_header bytes tokenLimit prefixCount prefixValue = .ok (.Ok opening))
    (checked : prefixes.check opening.declarations = .ok (.Ready table))
    (headerRead : read_header_tail table bytes opening.remaining importCount headerLimit = .ok (.Ok header))
    (read : read_annotations table bytes header.remaining limits = .ok (.Ok output)) :
    Rowl.Prefixes.WellFormed table ∧
    (∃ stream, Rowl.FunctionalLexer.Correct bytes.val tokenLimit.val (.Tokens stream) ∧
      Rowl.FunctionalPrefixes.Section bytes.val bytes.len prefixValue.val stream
        opening.declarations.val opening.ontology opening.opening opening.remaining) ∧
    Rowl.FunctionalHeader.TailRun opening.declarations.val bytes.val bytes.len importCount.val headerLimit.val
      opening.remaining (.Ok header) ∧
    Rowl.FunctionalAnnotations.Section opening.declarations.val bytes.val bytes.len limits.count.val
      limits.iri.val limits.lexical.val limits.depth.val header.remaining output.annotations.val output.remaining ∧
    output.annotations.val.length ≤ limits.count.val ∧
    (output.remaining = .Empty ∨
      ∃ token tail, output.remaining = .Cons token tail ∧ token.terminal ≠ .Keyword .Annotation) := by
  obtain ⟨same,valid,source⟩ := Rowl.FunctionalPrefixes.checked_source_prefix_table
    bytes tokenLimit prefixCount prefixValue opening table parsed checked
  have headerRun := (Rowl.FunctionalHeaderSource.source_header_result_iff bytes tokenLimit prefixCount prefixValue
    opening table importCount headerLimit (.Ok header) parsed checked).mp headerRead
  have accepted := (Rowl.FunctionalAnnotations.read_annotations_accepted_iff table bytes header.remaining limits output).mp read
  rw [same] at accepted
  exact ⟨valid,by simpa [same] using source,headerRun,accepted.1,accepted.2,
    Rowl.FunctionalAnnotations.section_maximal accepted.1⟩
end Rowl.FunctionalAnnotationSource
