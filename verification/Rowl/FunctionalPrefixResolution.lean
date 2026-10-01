import Rowl.FunctionalPrefixes
import Rowl.FunctionalIris

namespace Rowl.FunctionalPrefixResolution
open Aeneas Aeneas.Std RowlFrontendRust
open RowlFrontendRust.functional_prefixes RowlFrontendRust.functional_iris

/-- Source prefix parsing, normative table checking and actual IRI resolution
    compose without caller-supplied namespace metadata. Ontology contents remain
    unparsed; the resolved span is revalidated by the source IRI reader itself. -/
theorem source_iri_correct (bytes : alloc.vec.Vec U8) (tokenLimit countLimit valueLimit : Usize)
    (header : PrefixHeader) (table : prefixes.PrefixTable) (kind : SourceIriKind)
    (start finish limit : Usize) (value : alloc.vec.Vec U8)
    (parsed : read_prefix_header bytes tokenLimit countLimit valueLimit = .ok (.Ok header))
    (checked : prefixes.check header.declarations = .ok (.Ready table))
    (resolved : resolve_span table kind bytes start finish limit = .ok (.Ok value)) :
    table.declarations = header.declarations ∧ Rowl.Prefixes.WellFormed table ∧
    (∃ tokens, Rowl.FunctionalLexer.Correct bytes.val tokenLimit.val (.Tokens tokens) ∧
      Rowl.FunctionalPrefixes.Section bytes.val bytes.len valueLimit.val tokens
        header.declarations.val header.ontology header.opening header.remaining) ∧
    Rowl.FunctionalIris.Success header.declarations.val kind bytes.val start.val finish.val limit.val value ∧
    Rowl.Prefixes.IriAccepted value.val := by
  obtain ⟨same,valid,source⟩ := Rowl.FunctionalPrefixes.checked_source_prefix_table
    bytes tokenLimit countLimit valueLimit header table parsed checked
  have spelling := (Rowl.FunctionalIris.resolve_span_value_iff table kind bytes start finish limit value).mp resolved
  exact ⟨same,valid,by simpa [same] using source,by simpa [same] using spelling,
    Rowl.FunctionalIris.resolved_iri_grammar table kind bytes start finish limit value resolved⟩

/-- Exact actual IRI values are equivalent to the source/namespace/grammar/budget
    specification using precisely the declaration rows parsed from these bytes. -/
theorem source_iri_value_iff (bytes : alloc.vec.Vec U8) (tokenLimit countLimit valueLimit : Usize)
    (header : PrefixHeader) (table : prefixes.PrefixTable) (kind : SourceIriKind)
    (start finish limit : Usize) (value : alloc.vec.Vec U8)
    (parsed : read_prefix_header bytes tokenLimit countLimit valueLimit = .ok (.Ok header))
    (checked : prefixes.check header.declarations = .ok (.Ready table)) :
    resolve_span table kind bytes start finish limit = .ok (.Ok value) ↔
      Rowl.FunctionalIris.Success header.declarations.val kind bytes.val start.val finish.val limit.val value := by
  have same := (Rowl.FunctionalPrefixes.checked_source_prefix_table
    bytes tokenLimit countLimit valueLimit header table parsed checked).1
  simpa [same] using Rowl.FunctionalIris.resolve_span_value_iff table kind bytes start finish limit value

/-- Every IRI error and original offset is likewise equivalent to its independent
    specification with the original source-derived declarations, after the
    complete prefix syntax and normative table checks have succeeded. -/
theorem source_iri_error_iff (bytes : alloc.vec.Vec U8) (tokenLimit countLimit valueLimit : Usize)
    (header : PrefixHeader) (table : prefixes.PrefixTable) (kind : SourceIriKind)
    (start finish limit : Usize) (error : SourceIriError)
    (parsed : read_prefix_header bytes tokenLimit countLimit valueLimit = .ok (.Ok header))
    (checked : prefixes.check header.declarations = .ok (.Ready table)) :
    resolve_span table kind bytes start finish limit = .ok (.Err error) ↔
      Rowl.FunctionalIris.ErrorCorrect header.declarations.val kind bytes.val start.val finish.val limit.val error := by
  have same := (Rowl.FunctionalPrefixes.checked_source_prefix_table
    bytes tokenLimit countLimit valueLimit header table parsed checked).1
  simpa [same] using Rowl.FunctionalIris.resolve_span_error_iff table kind bytes start finish limit error

end Rowl.FunctionalPrefixResolution
