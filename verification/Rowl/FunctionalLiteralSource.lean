import Rowl.FunctionalLiterals
import Rowl.FunctionalPrefixResolution

namespace Rowl.FunctionalLiteralSource
open Aeneas Aeneas.Std RowlRust
open functional_literals functional_lexer functional_prefixes

/-- Literal results use precisely the namespace rows actually parsed from the
    same original byte document and accepted by the normative table checker.
    The caller still supplies the literal's position in the token stream. -/
theorem source_prefix_literal_result_iff (bytes : alloc.vec.Vec U8) (tokenLimit prefixCount prefixValue : Usize)
    (opening : PrefixHeader) (table : prefixes.PrefixTable) (tokens : Tokens) (lexLimit datatypeLimit : Usize)
    (result : core.result.Result (SourceLiteral × Tokens) SourceLiteralError)
    (parsed : read_prefix_header bytes tokenLimit prefixCount prefixValue = .ok (.Ok opening))
    (checked : prefixes.check opening.declarations = .ok (.Ready table)) :
    read_literal table bytes tokens lexLimit datatypeLimit = .ok result ↔
      Rowl.FunctionalLiterals.Run opening.declarations.val bytes.val bytes.len lexLimit.val datatypeLimit.val tokens result := by
  have same := (Rowl.FunctionalPrefixes.checked_source_prefix_table
    bytes tokenLimit prefixCount prefixValue opening table parsed checked).1
  simpa [same] using Rowl.FunctionalLiterals.read_literal_result_iff table bytes tokens lexLimit datatypeLimit result

/-- Whole-byte prefix lexing/parsing and normative table checking compose with
    exact literal source derivations. This does not assert validity of the
    still-unparsed ontology annotations, axioms or selected literal position. -/
theorem source_prefix_literal_derivation (bytes : alloc.vec.Vec U8) (tokenLimit prefixCount prefixValue : Usize)
    (opening : PrefixHeader) (table : prefixes.PrefixTable) (tokens : Tokens) (lexLimit datatypeLimit : Usize)
    (result : core.result.Result (SourceLiteral × Tokens) SourceLiteralError)
    (parsed : read_prefix_header bytes tokenLimit prefixCount prefixValue = .ok (.Ok opening))
    (checked : prefixes.check opening.declarations = .ok (.Ready table))
    (read : read_literal table bytes tokens lexLimit datatypeLimit = .ok result) :
    Rowl.Prefixes.WellFormed table ∧
    (∃ stream, Rowl.FunctionalLexer.Correct bytes.val tokenLimit.val (.Tokens stream) ∧
      Rowl.FunctionalPrefixes.Section bytes.val bytes.len prefixValue.val stream
        opening.declarations.val opening.ontology opening.opening opening.remaining) ∧
    Rowl.FunctionalLiterals.Run opening.declarations.val bytes.val bytes.len lexLimit.val datatypeLimit.val tokens result := by
  obtain ⟨same,valid,source⟩ := Rowl.FunctionalPrefixes.checked_source_prefix_table
    bytes tokenLimit prefixCount prefixValue opening table parsed checked
  exact ⟨valid,by simpa [same] using source,(source_prefix_literal_result_iff bytes tokenLimit prefixCount prefixValue
    opening table tokens lexLimit datatypeLimit result parsed checked).mp read⟩
end Rowl.FunctionalLiteralSource
