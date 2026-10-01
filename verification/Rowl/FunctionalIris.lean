import Rowl.FunctionalIriParts

namespace Rowl.FunctionalIris
open Aeneas Aeneas.Std Aeneas.Std.Result RowlFrontendRust RowlFrontendRust.functional_iris
open Rowl.FunctionalIriParts Rowl.Prefixes
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- Exact original full-IRI bytes, or the namespace concatenated with the unique
    source-derived local spelling. The expanded result must itself be an IRI. -/
def Success (rows : List prefixes.Declaration) (kind : SourceIriKind) (source : List U8)
    (start finish limit : Nat) (value : alloc.vec.Vec U8) : Prop :=
  match kind with
  | .Full => Rowl.FunctionalNames.Correct .FullIri source start finish limit (.Ok value)
  | .Abbreviated => ∃ parts, PartsValue source start finish parts ∧
      ExpansionCorrect rows parts.prefix.val parts.local.val limit (.Expanded value)
/-- All actual error phases in independent source/lookup/grammar/budget terms.
    Abbreviation expansion errors retain the original entire token start. -/
def ErrorCorrect (rows : List prefixes.Declaration) (kind : SourceIriKind) (source : List U8)
    (start finish limit : Nat) (error : SourceIriError) : Prop :=
  match kind, error with
  | .Full, .Name error => Rowl.FunctionalNames.ErrorCorrect .FullIri source start finish limit error
  | .Abbreviated, .Name error => SplitError source start finish (.Name error)
  | .Abbreviated, .UndeclaredPrefix offset => offset.val = start ∧ ∃ parts,
      PartsValue source start finish parts ∧ ExpansionCorrect rows parts.prefix.val parts.local.val limit .UndeclaredPrefix
  | .Abbreviated, .ResourceLimit offset => offset.val = start ∧ ∃ parts,
      PartsValue source start finish parts ∧ ExpansionCorrect rows parts.prefix.val parts.local.val limit .ResourceLimit
  | .Abbreviated, .InvalidExpandedIri offset => offset.val = start ∧ ∃ parts,
      PartsValue source start finish parts ∧ ExpansionCorrect rows parts.prefix.val parts.local.val limit .InvalidExpandedIri
  | _, _ => False
/-- Total byte-to-absolute-IRI contract for the public Rust source resolver. -/
def Correct (rows : List prefixes.Declaration) (kind : SourceIriKind) (source : List U8)
    (start finish limit : Nat) : core.result.Result (alloc.vec.Vec U8) SourceIriError → Prop
  | .Ok value => Success rows kind source start finish limit value
  | .Err error => ErrorCorrect rows kind source start finish limit error
/-- Complete independent admissibility. The byte limit counts only the final
    returned IRI, independently of the length of its original abbreviation. -/
def Admissible (rows : List prefixes.Declaration) (kind : SourceIriKind) (source : List U8)
    (start finish limit : Nat) : Prop :=
  match kind with
  | .Full => Rowl.FunctionalNames.Token .FullIri source start finish ∧
      (Rowl.FunctionalNames.Payload .FullIri source start finish).length ≤ limit
  | .Abbreviated => ∃ parts, PartsValue source start finish parts ∧ ∃ ns,
      Lookup rows parts.prefix.val = some ns ∧ ns.length+parts.local.val.length ≤ limit ∧
      IriAccepted (ns++parts.local.val)

private theorem expansion_unique (rows : List prefixes.Declaration) (label member : List U8) (limit : Nat)
    (one two : prefixes.Expansion) (first : ExpansionCorrect rows label member limit one)
    (second : ExpansionCorrect rows label member limit two) : one = two := by
  cases one <;> cases two <;> simp only [ExpansionCorrect] at first second <;>
    grind [alloc.vec.Vec.eq_iff]
private theorem expansion_actual_iff (table : prefixes.PrefixTable) (label member : alloc.vec.Vec U8)
    (limit : Usize) (result : prefixes.Expansion) :
    prefixes.expand_parts table label member limit = .ok result ↔
      ExpansionCorrect table.declarations.val label.val member.val limit.val result := by
  obtain ⟨actual,executed,correct⟩ := expand_parts_total_correct table label member limit
  constructor
  · intro output
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro intended
    have same := expansion_unique _ _ _ _ actual result correct intended
    simpa [same] using executed

/-- The original source reader and checked prefix expansion compose into a
    total exact absolute-IRI resolver, including every diagnostic phase. -/
theorem resolve_span_total_correct (table : prefixes.PrefixTable) (kind : SourceIriKind)
    (bytes : alloc.vec.Vec U8) (start finish limit : Usize) :
    ∃ result, resolve_span table kind bytes start finish limit = .ok result ∧
      Correct table.declarations.val kind bytes.val start.val finish.val limit.val result := by
  cases kind with
  | Full =>
    obtain ⟨result,executed,correct⟩ := Rowl.FunctionalNames.read_span_total_correct .FullIri bytes start finish limit
    cases result with
    | Ok value => exact ⟨.Ok value,by simp only [resolve_span,executed,bind_ok],correct⟩
    | Err error => exact ⟨.Err (.Name error),by simp only [resolve_span,executed,bind_ok],correct⟩
  | Abbreviated =>
    obtain ⟨result,executed,correct⟩ := split_abbreviated_total_correct bytes start finish
    cases result with
    | Err error =>
      cases error with
      | Name error => exact ⟨.Err (.Name error),by simp only [resolve_span,executed,bind_ok],correct⟩
      | InvalidParts _ | UndeclaredPrefix _ | ResourceLimit _ | InvalidExpandedIri _ => exact False.elim correct
    | Ok parts =>
      have grammars := partition_values correct.2
      obtain ⟨expansion,expanded,expansionCorrect⟩ := expand_parts_total_correct table parts.prefix parts.local limit
      cases expansion with
      | InvalidPrefix => exact False.elim (expansionCorrect grammars.1)
      | InvalidLocal => exact False.elim (expansionCorrect.2 grammars.2.1)
      | Expanded value => exact ⟨.Ok value,by simp only [resolve_span,executed,bind_ok,expanded],parts,correct,expansionCorrect⟩
      | UndeclaredPrefix => exact ⟨.Err (.UndeclaredPrefix start),by simp only [resolve_span,executed,bind_ok,expanded],rfl,parts,correct,expansionCorrect⟩
      | ResourceLimit => exact ⟨.Err (.ResourceLimit start),by simp only [resolve_span,executed,bind_ok,expanded],rfl,parts,correct,expansionCorrect⟩
      | InvalidExpandedIri => exact ⟨.Err (.InvalidExpandedIri start),by simp only [resolve_span,executed,bind_ok,expanded],rfl,parts,correct,expansionCorrect⟩

/-- Every exact successful result is equivalent to its independent source,
    namespace lookup, grammar and final-byte-budget specification. -/
theorem resolve_span_value_iff (table : prefixes.PrefixTable) (kind : SourceIriKind)
    (bytes : alloc.vec.Vec U8) (start finish limit : Usize) (value : alloc.vec.Vec U8) :
    resolve_span table kind bytes start finish limit = .ok (.Ok value) ↔
      Success table.declarations.val kind bytes.val start.val finish.val limit.val value := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := resolve_span_total_correct table kind bytes start finish limit
    have same := Result.ok_injective (executed.symm.trans accepted)
    subst result
    exact correct
  · intro source
    cases kind with
    | Full =>
      have read := (Rowl.FunctionalNames.read_span_accepted_iff .FullIri bytes start finish limit value).mpr source
      simp only [resolve_span,read,bind_ok]
    | Abbreviated =>
      obtain ⟨parts,input,expansion⟩ := source
      have split := (split_abbreviated_value_iff bytes start finish parts).mpr input
      have expand := (expansion_actual_iff table parts.prefix parts.local limit (.Expanded value)).mpr expansion
      simp only [resolve_span,split,bind_ok,expand]

/-- All and only source tokens with a declared, fitting, grammar-valid final IRI
    succeed, including full IRIs and independently derived abbreviation parts. -/
theorem resolve_span_accepts_iff (table : prefixes.PrefixTable) (kind : SourceIriKind)
    (bytes : alloc.vec.Vec U8) (start finish limit : Usize) :
    (∃ value, resolve_span table kind bytes start finish limit = .ok (.Ok value)) ↔
      Admissible table.declarations.val kind bytes.val start.val finish.val limit.val := by
  constructor
  · rintro ⟨value,accepted⟩
    have source := (resolve_span_value_iff table kind bytes start finish limit value).mp accepted
    cases kind with
    | Full => exact ⟨source.1,source.2.1⟩
    | Abbreviated =>
      obtain ⟨parts,input,_,_,ns,lookedUp,fits,contents,iri⟩ := source
      exact ⟨parts,input,ns,lookedUp,fits,by simpa [contents] using iri⟩
  · intro admissible
    cases kind with
    | Full =>
      obtain ⟨value,read⟩ := (Rowl.FunctionalNames.read_span_accepts_iff .FullIri bytes start finish limit).mpr admissible
      exact ⟨value,by simp only [resolve_span,read,bind_ok]⟩
    | Abbreviated =>
      obtain ⟨parts,input,ns,lookedUp,fits,iri⟩ := admissible
      have grammars := partition_values input.2
      obtain ⟨value,expanded⟩ := (expand_parts_accepts_iff table parts.prefix parts.local limit).mpr
        ⟨grammars.1,grammars.2.1,ns,lookedUp,fits,iri⟩
      have split := (split_abbreviated_value_iff bytes start finish parts).mpr input
      exact ⟨value,by simp only [resolve_span,split,bind_ok,expanded]⟩

/-- Every diagnostic predicate holds exactly when the actual resolver returns
    its error, including unchanged original token offsets and phase priority. -/
theorem resolve_span_error_iff (table : prefixes.PrefixTable) (kind : SourceIriKind)
    (bytes : alloc.vec.Vec U8) (start finish limit : Usize) (error : SourceIriError) :
    resolve_span table kind bytes start finish limit = .ok (.Err error) ↔
      ErrorCorrect table.declarations.val kind bytes.val start.val finish.val limit.val error := by
  constructor
  · intro rejected
    obtain ⟨result,executed,correct⟩ := resolve_span_total_correct table kind bytes start finish limit
    have same := Result.ok_injective (executed.symm.trans rejected)
    subst result
    exact correct
  · intro source
    cases kind with
    | Full =>
      cases error with
      | Name error =>
        have read := (Rowl.FunctionalNames.read_span_error_iff .FullIri bytes start finish limit error).mpr source
        simp only [resolve_span,read,bind_ok]
      | InvalidParts _ | UndeclaredPrefix _ | ResourceLimit _ | InvalidExpandedIri _ => exact False.elim source
    | Abbreviated =>
      cases error with
      | Name error =>
        have split := (split_abbreviated_error_iff bytes start finish (.Name error)).mpr source
        simp only [resolve_span,split,bind_ok]
      | InvalidParts _ => exact False.elim source
      | UndeclaredPrefix offset =>
        obtain ⟨same,parts,input,expansion⟩ := source
        have offsetSame : offset = start := UScalar.eq_of_val_eq same
        have split := (split_abbreviated_value_iff bytes start finish parts).mpr input
        have expand := (expansion_actual_iff table parts.prefix parts.local limit .UndeclaredPrefix).mpr expansion
        simp only [resolve_span,split,bind_ok,expand,offsetSame]
      | ResourceLimit offset =>
        obtain ⟨same,parts,input,expansion⟩ := source
        have offsetSame : offset = start := UScalar.eq_of_val_eq same
        have split := (split_abbreviated_value_iff bytes start finish parts).mpr input
        have expand := (expansion_actual_iff table parts.prefix parts.local limit .ResourceLimit).mpr expansion
        simp only [resolve_span,split,bind_ok,expand,offsetSame]
      | InvalidExpandedIri offset =>
        obtain ⟨same,parts,input,expansion⟩ := source
        have offsetSame : offset = start := UScalar.eq_of_val_eq same
        have split := (split_abbreviated_value_iff bytes start finish parts).mpr input
        have expand := (expansion_actual_iff table parts.prefix parts.local limit .InvalidExpandedIri).mpr expansion
        simp only [resolve_span,split,bind_ok,expand,offsetSame]

/-- Every actual returned value is a complete absolute IRI in the independently
    specified RFC 3987 grammar; namespace/local validity alone is insufficient. -/
theorem resolved_iri_grammar (table : prefixes.PrefixTable) (kind : SourceIriKind)
    (bytes : alloc.vec.Vec U8) (start finish limit : Usize) (value : alloc.vec.Vec U8)
    (accepted : resolve_span table kind bytes start finish limit = .ok (.Ok value)) : IriAccepted value.val := by
  have source := (resolve_span_value_iff table kind bytes start finish limit value).mp accepted
  cases kind with
  | Full =>
    obtain ⟨word,text,legal⟩ := Rowl.FunctionalNames.payload_grammar source.1
    exact ⟨word,by simpa [source.2.2] using text,legal⟩
  | Abbreviated =>
    obtain ⟨parts,_,_,_,_,_,_,_,iri⟩ := source
    exact iri

/-- Internal fallback errors cannot occur at the public source resolver. -/
theorem internal_parts_error_unreachable (table : prefixes.PrefixTable) (kind : SourceIriKind)
    (bytes : alloc.vec.Vec U8) (start finish limit offset : Usize) :
    resolve_span table kind bytes start finish limit ≠ .ok (.Err (.InvalidParts offset)) := by
  intro rejected
  have impossible := (resolve_span_error_iff table kind bytes start finish limit (.InvalidParts offset)).mp rejected
  cases kind <;> exact impossible

end Rowl.FunctionalIris
