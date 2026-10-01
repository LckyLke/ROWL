import Rowl.FunctionalPayload
import Rowl.Prefixes

namespace Rowl.FunctionalLiteralValues
open Aeneas Aeneas.Std Aeneas.Std.Result RowlFrontendRust
open functional_literals functional
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- Exact decoded quote payload at the caller's original source endpoints. -/
def StringValue (source : List U8) (token : Token) (limit : Nat) (value : alloc.vec.Vec U8) : Prop :=
  Rowl.FunctionalPayload.QuotedToken source token.start value.val token.end ∧ value.val.length ≤ limit
/-- Range validation precedes quote decoding; a decoded endpoint must match
    the entire supplied span before its payload can be exposed. -/
inductive SpanError (source : List U8) (token : Token) (limit : Nat) : SourceLiteralError → Prop
  | bounds (bad : token.end.val < token.start.val ∨ source.length < token.end.val) :
      SpanError source token limit (.InvalidSpan token.start)
  | quoted {error : ntriples.ReadError} (range : token.start.val ≤ token.end.val ∧ token.end.val ≤ source.length)
      (failure : Rowl.FunctionalPayload.QuotedError source token.start limit error) :
      SpanError source token limit (.Quoted error)
  | endpoint {value : alloc.vec.Vec U8} {stop : Usize}
      (range : token.start.val ≤ token.end.val ∧ token.end.val ≤ source.length)
      (decoded : Rowl.FunctionalPayload.QuotedToken source token.start value.val stop)
      (fits : value.val.length ≤ limit) (different : stop ≠ token.end) :
      SpanError source token limit (.InvalidSpan token.start)
def SpanCorrect (source : List U8) (token : Token) (limit : Nat) :
    core.result.Result (alloc.vec.Vec U8) SourceLiteralError → Prop
  | .Ok value => StringValue source token limit value
  | .Err error => SpanError source token limit error

/-- Arbitrary supplied quote spans are revalidated against the original bytes. -/
theorem string_span_total_correct (bytes : alloc.vec.Vec U8) (token : Token) (limit : Usize) :
    ∃ result, string_span bytes token limit = .ok result ∧ SpanCorrect bytes.val token limit.val result := by
  rw [string_span]
  by_cases reversed : token.end.val < token.start.val
  · exact ⟨.Err (.InvalidSpan token.start),by simp [UScalar.lt_equiv,reversed],.bounds (.inl reversed)⟩
  · simp only [UScalar.lt_equiv,reversed,↓reduceIte]
    by_cases beyond : bytes.val.length < token.end.val
    · exact ⟨.Err (.InvalidSpan token.start),by simp [alloc.vec.Vec.len_val,beyond],.bounds (.inr beyond)⟩
    · simp only [alloc.vec.Vec.len_val,beyond,↓reduceIte]
      have range : token.start.val ≤ token.end.val ∧ token.end.val ≤ bytes.val.length := by omega
      obtain ⟨decoded,executed,correct⟩ := Rowl.FunctionalPayload.read_quoted_total_correct bytes token.start limit
      rw [executed,bind_ok]
      cases decoded with
      | Err error => exact ⟨.Err (.Quoted error),rfl,.quoted range correct⟩
      | Ok pair =>
        obtain ⟨value,stop⟩ := pair
        simp only [uncurry_apply_pair]
        by_cases equal : stop = token.end
        · subst stop; exact ⟨.Ok value,by simp,correct⟩
        · exact ⟨.Err (.InvalidSpan token.start),by simp [equal],.endpoint range correct.1 correct.2 equal⟩

/-- Exact payload acceptance is equivalent to source quote grammar and budget. -/
theorem string_span_value_iff (bytes : alloc.vec.Vec U8) (token : Token) (limit : Usize) (value : alloc.vec.Vec U8) :
    string_span bytes token limit = .ok (.Ok value) ↔ StringValue bytes.val token limit.val value := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := string_span_total_correct bytes token limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same,SpanCorrect] using correct
  · intro source
    have progress := Rowl.FunctionalPayload.quoted_token_progress source.1
    have notReversed : ¬ token.end.val < token.start.val := by omega
    have notBeyond : ¬ bytes.val.length < token.end.val := by omega
    have decoded := (Rowl.FunctionalPayload.read_quoted_accepted_iff bytes token.start token.end limit value).mpr source
    simp [string_span,UScalar.lt_equiv,alloc.vec.Vec.len_val,notReversed,notBeyond,decoded]

/-- Every span, decoding or endpoint diagnostic has an exact source derivation. -/
theorem string_span_error_iff (bytes : alloc.vec.Vec U8) (token : Token) (limit : Usize) (error : SourceLiteralError) :
    string_span bytes token limit = .ok (.Err error) ↔ SpanError bytes.val token limit.val error := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := string_span_total_correct bytes token limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same,SpanCorrect] using correct
  · intro source
    cases source with
    | bounds bad =>
      rcases bad with reversed | beyond
      · simp [string_span,UScalar.lt_equiv,reversed]
      · by_cases reversed : token.end.val < token.start.val <;>
          simp [string_span,UScalar.lt_equiv,alloc.vec.Vec.len_val,reversed,beyond]
    | quoted range failure =>
      have notReversed : ¬ token.end.val < token.start.val := by omega
      have notBeyond : ¬ bytes.val.length < token.end.val := by omega
      have decoded := (Rowl.FunctionalPayload.read_quoted_error_iff bytes token.start limit _).mpr failure
      simp [string_span,UScalar.lt_equiv,alloc.vec.Vec.len_val,notReversed,notBeyond,decoded]
    | endpoint range decoded fits different =>
      have notReversed : ¬ token.end.val < token.start.val := by omega
      have notBeyond : ¬ bytes.val.length < token.end.val := by omega
      have executed := (Rowl.FunctionalPayload.read_quoted_accepted_iff bytes token.start _ limit _).mpr ⟨decoded,fits⟩
      simp [string_span,UScalar.lt_equiv,alloc.vec.Vec.len_val,notReversed,notBeyond,executed,different]

/-- The exact normative OWL 2 rdf:PlainLiteral datatype spelling. -/
def PlainDatatype : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,49#u8,57#u8,57#u8,57#u8,47#u8,48#u8,50#u8,47#u8,50#u8,50#u8,45#u8,114#u8,100#u8,102#u8,45#u8,115#u8,121#u8,110#u8,116#u8,97#u8,120#u8,45#u8,110#u8,115#u8,35#u8,80#u8,108#u8,97#u8,105#u8,110#u8,76#u8,105#u8,116#u8,101#u8,114#u8,97#u8,108#u8]
/-- Required structural lexical spelling of both plain-string shortcuts. -/
def PlainLexical (payload language : List U8) : List U8 := payload ++ [64#u8] ++ language
/-- Exact constant datatype or its first budget diagnostic. -/
def DatatypeCorrect (limit : Nat) (offset : Usize) : core.result.Result (alloc.vec.Vec U8) SourceLiteralError → Prop
  | .Ok value => value.val = PlainDatatype ∧ PlainDatatype.length ≤ limit
  | .Err (.DatatypeLimit actual) => actual = offset ∧ limit < PlainDatatype.length
  | .Err _ => False

/-- Plain-literal expansion terminates, retains exact text/tag case, and counts
    the required '@' separator in the final lexical budget. -/
theorem plain_lexical_total_correct (payload language : alloc.vec.Vec U8) (limit : Usize) :
    ∃ result, plain_lexical payload language limit = .ok result ∧
      Rowl.Prefixes.Joined (payload.val ++ [64#u8]) language.val limit.val result := by
  rw [plain_lexical]
  simp only [lift,bind_ok]
  obtain ⟨separator,copied,copiedBytes⟩ := Rowl.Prefixes.copy_total_correct (Array.to_slice (Array.make 1#usize [64#u8]))
  have spelling : separator.val = [64#u8] := by simpa [Array.to_slice] using copiedBytes
  rw [copied,bind_ok]
  obtain ⟨first,firstRead,firstCorrect⟩ := Rowl.Prefixes.join_total_correct payload separator limit
  rw [firstRead,bind_ok]
  cases first with
  | none => refine ⟨none,rfl,?_⟩; change limit.val < _ at firstCorrect ⊢; simp [spelling] at *; omega
  | some value =>
    obtain ⟨second,secondRead,secondCorrect⟩ := Rowl.Prefixes.join_total_correct value language limit
    exact ⟨second,secondRead,by simpa [firstCorrect.2,spelling] using secondCorrect⟩

private theorem joined_unique {left right : List U8} {limit : Nat} {one two : Option (alloc.vec.Vec U8)}
    (first : Rowl.Prefixes.Joined left right limit one) (second : Rowl.Prefixes.Joined left right limit two) : one = two := by
  cases one with
  | none => cases two with
    | none => rfl
    | some value => change limit < left.length + right.length at first
                    change left.length + right.length ≤ limit ∧ _ at second
                    omega
  | some value => cases two with
    | none => change limit < left.length + right.length at second
              change left.length + right.length ≤ limit ∧ _ at first
              omega
    | some other => have same := (alloc.vec.Vec.eq_iff value other).mpr (first.2.trans second.2.symm); simp [same]
/-- Every exact success or limit rejection is equivalent to the full expansion. -/
theorem plain_lexical_result_iff (payload language : alloc.vec.Vec U8) (limit : Usize)
    (result : Option (alloc.vec.Vec U8)) :
    plain_lexical payload language limit = .ok result ↔
      Rowl.Prefixes.Joined (payload.val ++ [64#u8]) language.val limit.val result := by
  obtain ⟨actual,executed,correct⟩ := plain_lexical_total_correct payload language limit
  constructor
  · intro output; have same := Result.ok_injective (executed.symm.trans output); simpa [same] using correct
  · intro wanted; have same := joined_unique correct wanted; simpa [same] using executed

/-- The datatype constant is copied exactly and its whole output budget is checked. -/
theorem plain_datatype_total_correct (limit offset : Usize) :
    ∃ result, plain_datatype limit offset = .ok result ∧ DatatypeCorrect limit.val offset result := by
  rw [plain_datatype]
  simp only [lift,bind_ok]
  obtain ⟨value,copied,copiedBytes⟩ := Rowl.Prefixes.copy_total_correct
    (Array.to_slice (Array.make 55#usize PlainDatatype (by simp [PlainDatatype])))
  have spelling : value.val = PlainDatatype := by simpa [Array.to_slice] using copiedBytes
  have copiedExact := copied
  simp only [PlainDatatype] at copiedExact
  rw [copiedExact,bind_ok]
  by_cases tooLarge : limit.val < PlainDatatype.length
  · exact ⟨.Err (.DatatypeLimit offset),by simp [alloc.vec.Vec.len_val,spelling,tooLarge],rfl,tooLarge⟩
  · exact ⟨.Ok value,by simp [alloc.vec.Vec.len_val,spelling,tooLarge],spelling,by omega⟩
private theorem datatype_unique {limit : Nat} {offset : Usize}
    {one two : core.result.Result (alloc.vec.Vec U8) SourceLiteralError}
    (first : DatatypeCorrect limit offset one) (second : DatatypeCorrect limit offset two) : one = two := by
  cases one with
  | Ok value => cases two with
    | Ok other => have same := (alloc.vec.Vec.eq_iff value other).mpr (first.1.trans second.1.symm); simp [same]
    | Err error => cases error <;> simp only [DatatypeCorrect] at second; try contradiction
                   have := first.2; omega
  | Err error => cases error <;> simp only [DatatypeCorrect] at first; try contradiction
                 cases two with
                 | Ok value => have := second.2; omega
                 | Err other => cases other <;> simp only [DatatypeCorrect] at second; try contradiction
                                simp [first.1,second.1]
/-- Every exact datatype result or budget diagnostic is characterized independently. -/
theorem plain_datatype_result_iff (limit offset : Usize)
    (result : core.result.Result (alloc.vec.Vec U8) SourceLiteralError) :
    plain_datatype limit offset = .ok result ↔ DatatypeCorrect limit.val offset result := by
  obtain ⟨actual,executed,correct⟩ := plain_datatype_total_correct limit offset
  constructor
  · intro output; have same := Result.ok_injective (executed.symm.trans output); simpa [same] using correct
  · intro wanted; have same := datatype_unique correct wanted; simpa [same] using executed
end Rowl.FunctionalLiteralValues
