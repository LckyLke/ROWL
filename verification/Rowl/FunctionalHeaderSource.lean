import Rowl.FunctionalHeader
import Rowl.FunctionalPrefixResolution

namespace Rowl.FunctionalHeaderSource
open Aeneas Aeneas.Std RowlFrontendRust
open RowlFrontendRust.functional_header RowlFrontendRust.functional_prefixes RowlFrontendRust.functional

/-- Exact header identity/import values and every first error are equivalent to
    the independent source contract using only the namespace rows actually read
    from these bytes and accepted by the normative table constructor. -/
theorem source_header_result_iff (bytes : alloc.vec.Vec U8) (tokenLimit prefixCount prefixValue : Usize)
    (opening : PrefixHeader) (table : prefixes.PrefixTable) (importCount iriLimit : Usize)
    (result : core.result.Result HeaderTail HeaderError)
    (parsed : read_prefix_header bytes tokenLimit prefixCount prefixValue = .ok (.Ok opening))
    (checked : prefixes.check opening.declarations = .ok (.Ready table)) :
    read_header_tail table bytes opening.remaining importCount iriLimit = .ok result ↔
      Rowl.FunctionalHeader.TailRun opening.declarations.val bytes.val bytes.len importCount.val iriLimit.val opening.remaining result := by
  have same := (Rowl.FunctionalPrefixes.checked_source_prefix_table
    bytes tokenLimit prefixCount prefixValue opening table parsed checked).1
  simpa [same] using Rowl.FunctionalHeader.read_header_tail_result_iff table bytes opening.remaining importCount iriLimit result

/-- Whole-source prefix lexing/parsing, normative namespace checking and actual
    header reading compose with exact identity/import source values, original
    reference tokens, bounded count and the unchanged remaining ontology stream.
    This does not assert validity of the still-unparsed annotation/axiom body. -/
theorem source_header_values (bytes : alloc.vec.Vec U8) (tokenLimit prefixCount prefixValue : Usize)
    (opening : PrefixHeader) (table : prefixes.PrefixTable) (importCount iriLimit : Usize) (header : HeaderTail)
    (parsed : read_prefix_header bytes tokenLimit prefixCount prefixValue = .ok (.Ok opening))
    (checked : prefixes.check opening.declarations = .ok (.Ready table))
    (read : read_header_tail table bytes opening.remaining importCount iriLimit = .ok (.Ok header)) :
    Rowl.Prefixes.WellFormed table ∧
    (∃ tokens, Rowl.FunctionalLexer.Correct bytes.val tokenLimit.val (.Tokens tokens) ∧
      Rowl.FunctionalPrefixes.Section bytes.val bytes.len prefixValue.val tokens
        opening.declarations.val opening.ontology opening.opening opening.remaining) ∧
    Rowl.FunctionalHeaderIdentity.IdentityValues opening.declarations.val bytes.val iriLimit.val header.identity ∧
    header.imports.val.length ≤ importCount.val ∧
    (∀ reference ∈ header.imports.val, reference.keyword.terminal = .Keyword .Import ∧
      Rowl.FunctionalHeaderIdentity.IriValue opening.declarations.val bytes.val iriLimit.val reference.target) ∧
    ∃ middle, Rowl.FunctionalHeaderIdentity.IdentityRun opening.declarations.val bytes.val iriLimit.val
      opening.remaining (.Ok (header.identity,middle)) ∧
      Rowl.FunctionalHeader.ImportSection opening.declarations.val bytes.val bytes.len iriLimit.val
        middle header.imports.val header.remaining := by
  obtain ⟨same,valid,source⟩ := Rowl.FunctionalPrefixes.checked_source_prefix_table
    bytes tokenLimit prefixCount prefixValue opening table parsed checked
  have values := Rowl.FunctionalHeader.header_source_values table bytes opening.remaining importCount iriLimit header read
  exact ⟨valid,by simpa [same] using source,by simpa [same] using values⟩

end Rowl.FunctionalHeaderSource
