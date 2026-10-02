import Rowl.Regular

namespace Rowl.Longest
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.longest Rowl.Regular
open scoped Computability
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- A finite canonical UTF-8 segment with exact source byte endpoints. -/
inductive Utf8Span (bs : List U8) : Nat → Nat → List Nat → Prop
  | empty {position} : position ≤ bs.length → Utf8Span bs position position []
  | character {position cp width endpoint tail} :
      Rowl.Unicode.Prefix bs position = some (cp, width) → 0 < width →
      position + width ≤ bs.length → Utf8Span bs (position + width) endpoint tail →
      Utf8Span bs position endpoint (cp :: tail)

/-- Independent candidate endpoints: some finite segment matches the language. -/
def Candidate (bs : List U8) (position : Nat) (language : Language Nat) (endpoint : Nat) : Prop :=
  ∃ word, Utf8Span bs position endpoint word ∧ word ∈ language
/-- Mathematical greatest-element specification, distinguishing absence from
    an accepted zero-width prefix. -/
def Maximal (eligible : Nat → Prop) : Option Usize → Prop
  | none => ∀ endpoint, ¬ eligible endpoint
  | some endpoint => eligible endpoint.val ∧ ∀ other, eligible other → other ≤ endpoint.val
/-- Only actual accepted segments enter the public maximum specification.
    Malformed UTF-8 has the same first-unit evidence as the whole-word scanner. -/
def Correct (language : Language Nat) (bs : List U8) (position : Nat) : PrefixResult → Prop
  | .Matched endpoint => (∃ word, Utf8From bs position word) ∧ Maximal (Candidate bs position language) endpoint
  | .MalformedUtf8 error => Utf8Failure bs position error

private def Eligible (bs : List U8) (position : Nat) (language : Language Nat)
    (previous : Option Usize) (endpoint : Nat) : Prop :=
  (∃ earlier, previous = some earlier ∧ endpoint = earlier.val) ∨ Candidate bs position language endpoint
private def LastBound (previous : Option Usize) (position : Nat) : Prop :=
  ∀ earlier, previous = some earlier → earlier.val ≤ position
private def ScanCorrect (language : Language Nat) (bs : List U8) (position : Nat)
    (previous : Option Usize) : PrefixResult → Prop
  | .Matched endpoint => (∃ word, Utf8From bs position word) ∧ Maximal (Eligible bs position language previous) endpoint
  | .MalformedUtf8 error => Utf8Failure bs position error

private theorem span_bounds {bs : List U8} {start finish : Nat} {word : List Nat}
    (span : Utf8Span bs start finish word) : start ≤ finish ∧ finish ≤ bs.length := by
  induction span with
  | empty bound => exact ⟨le_rfl, bound⟩
  | character _ positive _ _ ih => constructor <;> omega

private theorem span_at_end (bs : List U8) (finish : Nat) (word : List Nat)
    (span : Utf8Span bs bs.length finish word) : finish = bs.length ∧ word = [] := by
  cases span with
  | empty _ => exact ⟨rfl, rfl⟩
  | character _ positive fits _ => omega

private theorem candidate_at_end (bs : List U8) (language : Language Nat) (finish : Nat) :
    Candidate bs bs.length language finish ↔ finish = bs.length ∧ [] ∈ language := by
  constructor
  · rintro ⟨word, span, accepted⟩
    obtain ⟨endpoint, empty⟩ := span_at_end bs finish word span
    exact ⟨endpoint, by simpa [empty] using accepted⟩
  · rintro ⟨rfl, accepted⟩
    exact ⟨[], .empty (by omega), accepted⟩

private theorem candidate_step (bs : List U8) (position cp width : Nat)
    (unit : Rowl.Unicode.Prefix bs position = some (cp, width))
    (positive : 0 < width) (fits : position + width ≤ bs.length)
    (before after : Language Nat) (derived : ∀ word, word ∈ after ↔ cp :: word ∈ before)
    (endpoint : Nat) :
    Candidate bs position before endpoint ↔
      (endpoint = position ∧ [] ∈ before) ∨ Candidate bs (position + width) after endpoint := by
  constructor
  · rintro ⟨word, span, accepted⟩
    cases span with
    | empty _ => exact Or.inl ⟨rfl, accepted⟩
    | @character _ otherCp otherWidth _ tail otherUnit _ _ rest =>
      have equal := Prod.mk.inj (Option.some.inj (unit.symm.trans otherUnit))
      rcases equal with ⟨rfl, rfl⟩
      exact Or.inr ⟨tail, rest, (derived tail).mpr accepted⟩
  · rintro (⟨rfl, accepted⟩ | ⟨word, span, accepted⟩)
    · exact ⟨[], .empty (by omega), accepted⟩
    · exact ⟨cp :: word, .character unit positive fits span, (derived word).mp accepted⟩

private theorem transfer_maximum (before after : Nat → Prop)
    (cover : (∀ point, before point → ∃ larger, after larger ∧ point ≤ larger) ∧
      (∀ point, after point → before point))
    (result : Option Usize) (maximum : Maximal after result) : Maximal before result := by
  cases result with
  | none =>
    intro point eligible
    obtain ⟨larger, included, _⟩ := cover.1 point eligible
    exact maximum larger included
  | some endpoint =>
    refine ⟨cover.2 endpoint.val maximum.1, ?_⟩
    intro point eligible
    obtain ⟨larger, included, bound⟩ := cover.1 point eligible
    exact bound.trans (maximum.2 larger included)

private theorem eligible_step (bs : List U8) (position : Usize) (next : Nat)
    (before after : Language Nat) (previous : Option Usize)
    (oldBound : LastBound previous position.val)
    (step : ∀ endpoint, Candidate bs position.val before endpoint ↔
      (endpoint = position.val ∧ [] ∈ before) ∨ Candidate bs next after endpoint) :
    let latest := if [] ∈ before then some position else previous
    (∀ point, Eligible bs position.val before previous point →
      ∃ larger, Eligible bs next after latest larger ∧ point ≤ larger) ∧
    (∀ point, Eligible bs next after latest point → Eligible bs position.val before previous point) := by
  dsimp only
  by_cases empty : [] ∈ before
  · simp only [empty, ↓reduceIte]
    constructor
    · intro point eligible
      cases eligible with
      | inl old =>
        obtain ⟨earlier, found, equal⟩ := old
        exact ⟨position.val, Or.inl ⟨position, rfl, rfl⟩, by simpa [equal] using oldBound earlier found⟩
      | inr candidate =>
        cases (step point).mp candidate with
        | inl current => exact ⟨position.val, Or.inl ⟨position, rfl, rfl⟩, by omega⟩
        | inr later => exact ⟨point, Or.inr later, le_rfl⟩
    · intro point eligible
      cases eligible with
      | inl old =>
        obtain ⟨earlier, found, equal⟩ := old
        have same : earlier = position := (Option.some.inj found).symm
        exact Or.inr ((step point).mpr (Or.inl ⟨by simpa [same] using equal, empty⟩))
      | inr later => exact Or.inr ((step point).mpr (Or.inr later))
  · simp only [empty, ↓reduceIte]
    have exactCandidates : ∀ point, Candidate bs position.val before point ↔ Candidate bs next after point := by
      intro point
      simpa [empty] using step point
    constructor
    · intro point eligible
      refine ⟨point, ?_, le_rfl⟩
      simpa only [Eligible, exactCandidates] using eligible
    · intro point eligible
      simpa only [Eligible, exactCandidates] using eligible

private theorem end_maximum (bs : List U8) (position : Usize) (language : Language Nat)
    (previous : Option Usize) (oldBound : LastBound previous position.val)
    (atEnd : position.val = bs.length) :
    Maximal (Eligible bs position.val language previous)
      (if [] ∈ language then some position else previous) := by
  by_cases empty : [] ∈ language
  · simp only [empty, ↓reduceIte]
    refine ⟨Or.inr ⟨[], .empty (by omega), empty⟩, ?_⟩
    intro point eligible
    cases eligible with
    | inl old =>
      obtain ⟨earlier, found, equal⟩ := old
      simpa [equal] using oldBound earlier found
    | inr candidate =>
      have endpoint := ((candidate_at_end bs language point).mp (by simpa [atEnd] using candidate)).1
      omega
  · simp only [empty, ↓reduceIte]
    cases previous with
    | none =>
      intro point eligible
      cases eligible with
      | inl old => obtain ⟨_, found, _⟩ := old; cases found
      | inr candidate =>
        exact empty (((candidate_at_end bs language point).mp (by simpa [atEnd] using candidate)).2)
    | some earlier =>
      refine ⟨Or.inl ⟨earlier, rfl, rfl⟩, ?_⟩
      intro point eligible
      cases eligible with
      | inl old =>
        obtain ⟨other, found, equal⟩ := old
        have same : earlier = other := Option.some.inj found
        simpa [same] using le_of_eq equal
      | inr candidate =>
        exact False.elim (empty (((candidate_at_end bs language point).mp (by simpa [atEnd] using candidate)).2))

private theorem scan_total (expression : regular.Expression) (bytes : alloc.vec.Vec U8)
    (position : Usize) (previous : Option Usize) (oldBound : LastBound previous position.val) :
    ∃ result, scan expression bytes position previous = .ok result ∧
      ScanCorrect (Denotes expression) bytes.val position.val previous result := by
  let latest := if [] ∈ Denotes expression then some position else previous
  have picked : (if decide ([] ∈ Denotes expression) then .ok (some position) else .ok previous : Result (Option Usize)) = .ok latest := by
    by_cases empty : [] ∈ Denotes expression <;> simp [latest, empty]
  obtain ⟨decoded, executed, correct⟩ := Rowl.Unicode.decode_next_total_correct bytes position
  rw [scan, nullable_total_correct, bind_ok, picked, bind_ok, executed, bind_ok]
  cases decoded with
  | End =>
    refine ⟨.Matched latest, rfl, ⟨[], ?_⟩, ?_⟩
    · rw [correct]; exact .endOfInput
    · exact end_maximum bytes.val position (Denotes expression) previous oldBound correct
  | Error error =>
    refine ⟨.MalformedUtf8 error, rfl, ?_⟩
    cases error with
    | InvalidPosition address => exact .position (congrArg UScalar.val correct.1) correct.2
    | InvalidUtf8 address => exact .utf8 (congrArg UScalar.val correct.1) correct.2.1 correct.2.2
    | NonXmlCharacter _ _ => exact False.elim correct
  | Scalar cp next =>
    obtain ⟨advance, bound, unit⟩ := correct
    have positive : 0 < next.val - position.val := by omega
    have sameNext : position.val + (next.val - position.val) = next.val := by omega
    obtain ⟨derived, computed, language⟩ := derivative_total_correct expression cp
    dsimp only
    rw [computed, bind_ok]
    have nextBound : LastBound latest next.val := by
      intro earlier found
      by_cases empty : [] ∈ Denotes expression
      · have same : position = earlier := by simpa [latest, empty] using found
        simp [← same]; omega
      · have old : previous = some earlier := by simpa [latest, empty] using found
        exact (oldBound earlier old).trans (by omega)
    obtain ⟨result, recursed, invariant⟩ := scan_total derived bytes next latest nextBound
    refine ⟨result, by simp [recursed], ?_⟩
    cases result with
    | MalformedUtf8 error =>
      exact .later unit positive (by omega) (by simpa [sameNext, ScanCorrect] using invariant)
    | Matched endpoint =>
      obtain ⟨⟨word, utf8⟩, maximum⟩ := invariant
      refine ⟨⟨cp.val :: word, .character unit positive (by omega) (by simpa [sameNext] using utf8)⟩, ?_⟩
      have step := candidate_step bytes.val position.val cp.val (next.val - position.val)
        unit positive (by omega) (Denotes expression) (Denotes derived) language
      simp only [sameNext] at step
      exact transfer_maximum _ _ (eligible_step bytes.val position next.val _ _ previous oldBound step) endpoint maximum
termination_by bytes.val.length - position.val
decreasing_by omega

/-- Actual greedy matching terminates with the greatest accepted byte endpoint,
    no match, or exact evidence of the first malformed suffix unit. -/
theorem longest_prefix_total_correct (expression : regular.Expression) (bytes : alloc.vec.Vec U8)
    (position : Usize) :
    ∃ result, longest_prefix expression bytes position = .ok result ∧
      Correct (Denotes expression) bytes.val position.val result := by
  obtain ⟨result, executed, correct⟩ := scan_total expression bytes position none (by simp [LastBound])
  refine ⟨result, by simpa [longest_prefix] using executed, ?_⟩
  have neutral : Eligible bytes.val position.val (Denotes expression) none = Candidate bytes.val position.val (Denotes expression) := by
    funext endpoint
    simp [Eligible]
  cases result <;> simpa [ScanCorrect, Correct, neutral] using correct

private theorem maximum_unique (eligible : Nat → Prop) (one two : Option Usize)
    (first : Maximal eligible one) (second : Maximal eligible two) : one = two := by
  cases one with
  | none =>
    cases two with
    | none => rfl
    | some other => exact False.elim (first other.val second.1)
  | some endpoint =>
    cases two with
    | none => exact False.elim (second endpoint.val first.1)
    | some other =>
      have equal : endpoint.val = other.val := Nat.le_antisymm (second.2 _ first.1) (first.2 _ second.1)
      exact congrArg some (UScalar.eq_of_val_eq equal)

private theorem failure_excludes_utf8 (bs : List U8) (position : Nat) (error : unicode.TextError)
    (failed : Utf8Failure bs position error) : ∀ word, ¬ Utf8From bs position word := by
  induction failed with
  | position same beyond =>
    intro word accepted
    cases accepted with
    | endOfInput => omega
    | character _ positive fits _ => omega
  | utf8 same inside invalid =>
    intro word accepted
    cases accepted with
    | endOfInput => omega
    | character unit _ _ _ => rw [invalid] at unit; cases unit
  | later unit positive fits failed ih =>
    intro word accepted
    cases accepted with
    | endOfInput => omega
    | character otherUnit _ _ tail =>
      have same := (Prod.mk.inj (Option.some.inj (unit.symm.trans otherUnit))).2
      subst same
      exact ih _ tail

/-- Complete acceptance for each exact endpoint, including the distinct None
    outcome and accepted zero-width prefixes. -/
theorem longest_prefix_matched_iff (expression : regular.Expression) (bytes : alloc.vec.Vec U8)
    (position : Usize) (endpoint : Option Usize) :
    longest_prefix expression bytes position = .ok (.Matched endpoint) ↔
      (∃ word, Utf8From bytes.val position.val word) ∧ Maximal (Candidate bytes.val position.val (Denotes expression)) endpoint := by
  obtain ⟨result, executed, correct⟩ := longest_prefix_total_correct expression bytes position
  constructor
  · intro success
    have same := Result.ok_injective (executed.symm.trans success)
    simpa [same, Correct] using correct
  · rintro ⟨utf8, maximum⟩
    cases result with
    | Matched other =>
      have equal := maximum_unique _ other endpoint correct.2 maximum
      simpa [equal] using executed
    | MalformedUtf8 error =>
      obtain ⟨word, accepted⟩ := utf8
      exact False.elim (failure_excludes_utf8 _ _ _ correct word accepted)

/-- Successful endpoints are actual source boundaries within the input. -/
theorem longest_prefix_endpoint_bounds (expression : regular.Expression) (bytes : alloc.vec.Vec U8)
    (position endpoint : Usize)
    (success : longest_prefix expression bytes position = .ok (.Matched (some endpoint))) :
    position.val ≤ endpoint.val ∧ endpoint.val ≤ bytes.val.length := by
  have correct := (longest_prefix_matched_iff expression bytes position (some endpoint)).mp success
  obtain ⟨word, span, _⟩ := correct.2.1
  exact span_bounds span

end Rowl.Longest
