import Rowl.Probes

namespace Rowl.Decimal
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.decimal
open Rowl.Probes
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- Exactly the ASCII decimal digit interval; no Unicode/sign normalization. -/
def Digit (byte : U8) : Prop := 48 ≤ byte.val ∧ byte.val ≤ 57
/-- Every original byte in this finite word is a decimal digit. -/
def Digits (bytes : List U8) : Prop := ∀ byte ∈ bytes, Digit byte
/-- Decimal positional interpretation, independent of unary Rust construction. -/
def Numeric (bytes : List U8) (initial : Nat) : Nat :=
  bytes.foldl (fun previous byte => 10*previous+(byte.val-48)) initial
/-- The exact unchanged source bytes between two mathematical offsets. -/
def Slice (bytes : List U8) (start finish : Nat) : List U8 := (bytes.take finish).drop start
/-- First invalid byte in a bounded original span; all preceding bytes are valid. -/
def BadDigit (bytes : List U8) (start finish : Nat) (offset : Usize) : Prop :=
  start ≤ offset.val ∧ offset.val < finish ∧ Digits (Slice bytes start offset.val) ∧
    ∃ byte, bytes[offset.val]? = some byte ∧ ¬ Digit byte
/-- Successful scanning has the full exact positional value; invalid-digit
    rejection is the first source failure, without a successful partial value. -/
def ScanCorrect (bytes : List U8) (start finish initial : Nat) :
    core.result.Result probes.Natural ReadError → Prop
  | .Ok value => Digits (Slice bytes start finish) ∧ naturalValue value = Numeric (Slice bytes start finish) initial
  | .Err (.InvalidDigit offset) => BadDigit bytes start finish offset
  | .Err _ => False
/-- Exact phase/offset diagnostics of the public bounded-span entry point. -/
def ErrorCorrect (bytes : List U8) (start finish : Nat) : ReadError → Prop
  | .InvalidSpan offset => offset.val = start ∧ (finish < start ∨ bytes.length < finish)
  | .Empty offset => offset.val = start ∧ start = finish ∧ finish ≤ bytes.length
  | .InvalidDigit offset => start < finish ∧ finish ≤ bytes.length ∧ BadDigit bytes start finish offset
/-- Complete nonempty decimal-span interpretation; range, grammar and numeric
    value are specifications rather than caller-provided facts. -/
def Correct (bytes : List U8) (start finish : Nat) :
    core.result.Result probes.Natural ReadError → Prop
  | .Ok value => start < finish ∧ finish ≤ bytes.length ∧ Digits (Slice bytes start finish) ∧
      naturalValue value = Numeric (Slice bytes start finish) 0
  | .Err error => ErrorCorrect bytes start finish error

/-- The actual finite-byte digit constructor terminates and has its exact value. -/
theorem small_value_total_correct (count : U8) :
    ∃ value, small_value count = .ok value ∧ naturalValue value = count.val := by
  rw [small_value]
  by_cases zero : count.val = 0
  · exact ⟨.Zero,by simp [UScalar.eq_equiv,zero],by simpa [naturalValue] using zero.symm⟩
  · simp only [UScalar.eq_equiv,show (0#u8).val = 0 from rfl,zero,↓reduceIte]
    obtain ⟨previous,subExecuted,subValue⟩ := WP.spec_imp_exists
      (U8.sub_spec (x := count) (y := 1#u8) (by scalar_tac))
    obtain ⟨value,executed,valueCorrect⟩ := small_value_total_correct previous
    refine ⟨.Succ value,by simp [subExecuted,executed],?_⟩
    simp only [naturalValue,valueCorrect]
    have before := subValue.1
    norm_num at before
    omega
termination_by count.val
decreasing_by have := subValue.1; norm_num at *; omega

@[local step] private theorem add_spec (left right : probes.Natural) :
    probes.add left right ⦃ result => naturalValue result = naturalValue left+naturalValue right ⦄ := by
  obtain ⟨result,executed,correct⟩ := add_total_correct left right
  simp [executed,correct]
/-- Ten actual exact additions implement mathematical multiplication by ten. -/
theorem times_ten_total_correct (value : probes.Natural) :
    ∃ result, times_ten value = .ok result ∧ naturalValue result = 10*naturalValue value := by
  apply WP.spec_imp_exists
  unfold times_ten
  step*
  simp_all [naturalValue]
  omega

private theorem slice_empty (bytes : List U8) (position : Nat) : Slice bytes position position = [] := by
  simp [Slice,List.drop_take]
private theorem slice_step (bytes : List U8) (start finish : Nat)
    (before : start < finish) (fits : finish ≤ bytes.length) :
    Slice bytes start finish = bytes[start]'(by omega) :: Slice bytes (start+1) finish := by
  have inside : start < (bytes.take finish).length := by simp; omega
  rw [Slice,List.drop_eq_getElem_cons inside]
  simp only [List.getElem_take]
  rfl
private theorem digits_cons (head : U8) (tail : List U8) : Digits (head::tail) ↔ Digit head ∧ Digits tail := by
  simp [Digits]

private theorem scan_total (bytes : alloc.vec.Vec U8) (position finish : Usize) (previous : probes.Natural)
    (range : position.val ≤ finish.val ∧ finish.val ≤ bytes.val.length) :
    ∃ result, scan bytes position finish previous = .ok result ∧
      ScanCorrect bytes.val position.val finish.val (naturalValue previous) result := by
  rw [scan]
  by_cases atEnd : position.val = finish.val
  · exact ⟨.Ok previous,by simp [UScalar.eq_equiv,atEnd],by simp [ScanCorrect,atEnd,slice_empty,Digits,Numeric]⟩
  · have inside : position.val < bytes.val.length := by omega
    have before : position.val < finish.val := by omega
    have indexed : bytes.index_usize position = .ok bytes.val[position.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    simp only [UScalar.eq_equiv,atEnd,↓reduceIte,alloc.vec.Vec.index_slice_index,indexed,bind_ok]
    obtain ⟨digit,digitExecuted,digitCorrect⟩ := decimal_digit_total_correct bytes.val[position.val]
    rw [digitExecuted,bind_ok]
    cases digit with
    | none =>
      refine ⟨.Err (.InvalidDigit position),rfl,le_rfl,before,?_,bytes.val[position.val],?_,digitCorrect⟩
      · simp [slice_empty,Digits]
      · exact List.getElem?_eq_getElem inside
    | some digit =>
      obtain ⟨tens,tensExecuted,tensValue⟩ := times_ten_total_correct previous
      obtain ⟨small,smallExecuted,smallValue⟩ := small_value_total_correct digit
      obtain ⟨value,valueExecuted,valueValue⟩ := add_total_correct tens small
      have size := bytes.property
      obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := position) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = position.val+1 := by simpa using nextValue
      have nextRange : next.val ≤ finish.val ∧ finish.val ≤ bytes.val.length := by omega
      obtain ⟨result,executed,correct⟩ := scan_total bytes next finish value nextRange
      refine ⟨result,?_,?_⟩
      · simp [tensExecuted,smallExecuted,valueExecuted,advance,executed]
      · have headDigit : Digit bytes.val[position.val] := by unfold Digit; have := digitCorrect.2; have := digitCorrect.1; omega
        have headValue : bytes.val[position.val].val-48 = digit.val := by have := digitCorrect.2; omega
        cases result with
        | Ok output =>
          refine ⟨?_,?_⟩
          · rw [slice_step _ _ _ before range.2,digits_cons]
            exact ⟨headDigit,by simpa [nextIs] using correct.1⟩
          · rw [slice_step _ _ _ before range.2]
            change naturalValue output = Numeric (Slice bytes.val (position.val+1) finish.val)
              (10*naturalValue previous+(bytes.val[position.val].val-48))
            simpa [nextIs,valueValue,tensValue,smallValue,headValue] using correct.2
        | Err error =>
          cases error with
          | InvalidSpan _ | Empty _ => exact correct
          | InvalidDigit offset =>
            refine ⟨by have := correct.1; omega,correct.2.1,?_,correct.2.2.2⟩
            have offsetAfter : position.val < offset.val := by have := correct.1; omega
            have offsetFits : offset.val ≤ bytes.val.length := by have := correct.2.1; omega
            rw [slice_step _ _ _ offsetAfter offsetFits,digits_cons]
            exact ⟨headDigit,by simpa [nextIs] using correct.2.2.1⟩
termination_by finish.val-position.val
decreasing_by omega

/-- Exact decimal reading from any original byte span, with totality, bounds,
    complete numeric value and the first phase-specific source error. -/
theorem read_span_total_correct (bytes : alloc.vec.Vec U8) (start finish : Usize) :
    ∃ result, read_span bytes start finish = .ok result ∧ Correct bytes.val start.val finish.val result := by
  rw [read_span]
  by_cases reversed : finish.val < start.val
  · exact ⟨.Err (.InvalidSpan start),by simp [UScalar.lt_equiv,reversed],rfl,Or.inl reversed⟩
  · simp only [UScalar.lt_equiv,reversed,↓reduceIte]
    by_cases beyond : bytes.val.length < finish.val
    · exact ⟨.Err (.InvalidSpan start),by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,beyond],rfl,Or.inr beyond⟩
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,beyond,↓reduceIte]
      by_cases empty : start.val = finish.val
      · exact ⟨.Err (.Empty start),by simp [UScalar.eq_equiv,empty],rfl,empty,by omega⟩
      · simp only [UScalar.eq_equiv,empty,↓reduceIte]
        obtain ⟨result,executed,correct⟩ := scan_total bytes start finish .Zero ⟨by omega,by omega⟩
        refine ⟨result,executed,?_⟩
        cases result with
        | Ok value => exact ⟨by omega,by omega,correct⟩
        | Err error =>
          cases error with
          | InvalidSpan _ | Empty _ => exact False.elim correct
          | InvalidDigit _ => exact ⟨by omega,by omega,correct⟩

/-- The public complete-byte reader has the same exact source/decimal contract. -/
theorem read_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ result, decimal.read bytes = .ok result ∧ Correct bytes.val 0 bytes.val.length result := by
  simpa [decimal.read,alloc.vec.Vec.len_val] using read_span_total_correct bytes 0#usize (alloc.vec.Vec.len bytes)


private theorem value_injective (one : probes.Natural) :
    ∀ two, naturalValue one = naturalValue two → one = two := by
  induction one with
  | Zero =>
    intro two same
    cases two with
    | Zero => rfl
    | Succ previous => simp [naturalValue] at same
  | Succ previous ih =>
    intro two same
    cases two with
    | Zero => simp [naturalValue] at same
    | Succ other =>
      have equal : naturalValue previous = naturalValue other := by simpa [naturalValue] using same
      exact congrArg _ (ih other equal)
private theorem bad_excludes_digits (bytes : List U8) (start finish : Nat) (offset : Usize)
    (fits : finish ≤ bytes.length) (bad : BadDigit bytes start finish offset)
    (digits : Digits (Slice bytes start finish)) : False := by
  obtain ⟨afterStart,beforeEnd,earlier,byte,lookup,notDigit⟩ := bad
  have inside : offset.val < bytes.length := by omega
  have same : byte = bytes[offset.val] := Option.some.inj (lookup.symm.trans (List.getElem?_eq_getElem inside))
  have included : byte ∈ Slice bytes start finish := by
    rw [same,Slice]
    have takeInside : offset.val < (bytes.take finish).length := by simp; omega
    have dropInside : offset.val-start < ((bytes.take finish).drop start).length := by simp; omega
    have chosen := List.getElem_mem dropInside
    simpa [List.getElem_drop,List.getElem_take,show start+(offset.val-start) = offset.val from by omega] using chosen
  exact notDigit (digits byte included)

/-- Both directions of exact original-span acceptance, including the unique
    mathematical natural value rather than merely syntactic recognition. -/
theorem read_span_accepted_iff (bytes : alloc.vec.Vec U8) (start finish : Usize) (value : probes.Natural) :
    read_span bytes start finish = .ok (.Ok value) ↔
      start.val < finish.val ∧ finish.val ≤ bytes.val.length ∧ Digits (Slice bytes.val start.val finish.val) ∧
      naturalValue value = Numeric (Slice bytes.val start.val finish.val) 0 := by
  obtain ⟨result,executed,correct⟩ := read_span_total_correct bytes start finish
  constructor
  · intro accepted
    have same := Result.ok_injective (executed.symm.trans accepted)
    simpa [same,Correct] using correct
  · rintro ⟨nonempty,fits,digits,valueCorrect⟩
    cases result with
    | Ok actual =>
      have same := value_injective actual value (correct.2.2.2.trans valueCorrect.symm)
      simpa [same] using executed
    | Err error =>
      cases error with
      | InvalidSpan offset => rcases correct.2 with reversed | beyond; omega; omega
      | Empty offset => have := correct.2.1; omega
      | InvalidDigit offset => exact False.elim (bad_excludes_digits _ _ _ _ fits correct.2.2 digits)

/-- Whole-byte acceptance is exactly a nonempty ASCII decimal word with its
    positional value, allowing arbitrary leading zeroes and no numeric cap. -/
theorem read_accepted_iff (bytes : alloc.vec.Vec U8) (value : probes.Natural) :
    decimal.read bytes = .ok (.Ok value) ↔
      bytes.val ≠ [] ∧ Digits bytes.val ∧ naturalValue value = Numeric bytes.val 0 := by
  have span := read_span_accepted_iff bytes 0#usize (alloc.vec.Vec.len bytes) value
  simpa [decimal.read,alloc.vec.Vec.len_val,Slice,List.length_pos_iff_ne_nil] using span

/-- Range and empty-input fallback diagnoses cannot occur on a nonempty bounded
    span. Any rejection there is an exact first invalid-digit source offset. -/
theorem read_span_error_is_first_digit (bytes : alloc.vec.Vec U8) (start finish : Usize) (error : ReadError)
    (range : start.val < finish.val ∧ finish.val ≤ bytes.val.length)
    (rejected : read_span bytes start finish = .ok (.Err error)) :
    ∃ offset, error = .InvalidDigit offset ∧ BadDigit bytes.val start.val finish.val offset := by
  obtain ⟨result,executed,correct⟩ := read_span_total_correct bytes start finish
  have same := Result.ok_injective (executed.symm.trans rejected)
  subst result
  cases error with
  | InvalidSpan offset => rcases correct.2 with reversed | beyond; omega; omega
  | Empty offset => have := correct.2.1; omega
  | InvalidDigit offset => exact ⟨offset,rfl,correct.2.2⟩

/-- There is a successful exact value precisely for a bounded nonempty digit
    span. Existence follows from actual execution, not a numeric-size assumption. -/
theorem read_span_accepts_iff (bytes : alloc.vec.Vec U8) (start finish : Usize) :
    (∃ value, read_span bytes start finish = .ok (.Ok value)) ↔
      start.val < finish.val ∧ finish.val ≤ bytes.val.length ∧
      Digits (Slice bytes.val start.val finish.val) := by
  constructor
  · rintro ⟨value,executed⟩
    have correct := (read_span_accepted_iff bytes start finish value).mp executed
    exact ⟨correct.1,correct.2.1,correct.2.2.1⟩
  · rintro ⟨nonempty,fits,digits⟩
    obtain ⟨result,executed,correct⟩ := read_span_total_correct bytes start finish
    cases result with
    | Ok value => exact ⟨value,executed⟩
    | Err error =>
      cases error with
      | InvalidSpan offset => rcases correct.2 with reversed | beyond; omega; omega
      | Empty offset => have := correct.2.1; omega
      | InvalidDigit offset => exact False.elim (bad_excludes_digits _ _ _ _ fits correct.2.2 digits)

end Rowl.Decimal
