import Rowl.Encoding
import Rowl.LangTag
import Rowl.Iri

namespace Rowl.NTriples
open Aeneas Aeneas.Std RowlFrontendRust
open ntriples Rowl.Unicode
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

abbrev Parsed := core.result.Result
/-- A strictly decoded RFC 3629 unit at an exact original byte position. -/
def UnitAt (bs : List U8) (start : Nat) (cp : U32) (next : Usize) : Prop :=
  start < next.val ∧ next.val ≤ bs.length ∧ Prefix bs start = some (cp.val, next.val-start)
/-- Private unit readers also diagnose positions past the source; public whole-
    document parsing starts at zero and must preserve bounded positions. -/
def MalformedAt (bs : List U8) (start : Nat) : Prop :=
  bs.length < start ∨ (start < bs.length ∧ Prefix bs start = none)
def MalformedError (bs : List U8) (start : Nat) (e : ReadError) : Prop :=
  e.kind = .MalformedUtf8 ∧ e.offset.val = start ∧ MalformedAt bs start

def AtCorrect (bs : List U8) (start : Nat) : Parsed (Option (U32 × Usize)) ReadError → Prop
  | .Ok none => start = bs.length
  | .Ok (some (cp,next)) => UnitAt bs start cp next
  | .Err e => MalformedError bs start e

theorem at_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ result, ntriples.at bytes position = .ok result ∧ AtCorrect bytes.val position.val result := by
  obtain ⟨decoded, hd, hc⟩ := decode_next_total_correct bytes position
  cases decoded with
  | End => exact ⟨.Ok none, by simp [ntriples.at, hd], hc⟩
  | Scalar cp next => exact ⟨.Ok (some (cp,next)), by simp [ntriples.at, hd], hc⟩
  | Error error =>
    refine ⟨.Err ⟨.MalformedUtf8,position⟩, by simp [ntriples.at, hd, ntriples.error], ?_⟩
    cases error <;> simp_all [AtCorrect, MalformedError, MalformedAt, StepCorrect]

def RequiredError (bs : List U8) (start : Nat) (e : ReadError) : Prop :=
  MalformedError bs start e ∨ (e.kind = .UnexpectedEnd ∧ e.offset.val = start ∧ start = bs.length)
def RequiredCorrect (bs : List U8) (start : Nat) : Parsed (U32 × Usize) ReadError → Prop
  | .Ok (cp,next) => UnitAt bs start cp next
  | .Err e => RequiredError bs start e

private theorem same_residual {T : Type} (e : ReadError) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      T (core.convert.FromSame ReadError) (.Err e) = .ok (.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame]

theorem required_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ result, required bytes position = .ok result ∧ RequiredCorrect bytes.val position.val result := by
  obtain ⟨unit, hu, hc⟩ := at_total_correct bytes position
  cases unit with
  | Ok value =>
    cases value with
    | none =>
      refine ⟨.Err ⟨.UnexpectedEnd, position⟩, ?_, ?_⟩
      · simp [required, hu, core.result.Result.Insts.CoreOpsTry.branch, ntriples.error]
      · exact Or.inr ⟨rfl, rfl, hc⟩
    | some pair =>
      obtain ⟨cp,next⟩ := pair
      exact ⟨.Ok (cp,next), by simp [required, hu, core.result.Result.Insts.CoreOpsTry.branch], hc⟩
  | Err e =>
    refine ⟨.Err e, ?_, Or.inl hc⟩
    simp [required, hu, core.result.Result.Insts.CoreOpsTry.branch, same_residual]

def ExpectCorrect (bs : List U8) (start : Nat) (wanted : U32) (kind : ErrorKind) :
    Parsed Usize ReadError → Prop
  | .Ok next => UnitAt bs start wanted next
  | .Err e => RequiredError bs start e ∨
      (e.kind = kind ∧ e.offset.val = start ∧ ∃ cp next, UnitAt bs start cp next ∧ cp ≠ wanted)

theorem expect_total_correct (bytes : alloc.vec.Vec U8) (position : Usize)
    (wanted : U32) (kind : ErrorKind) :
    ∃ result, expect bytes position wanted kind = .ok result ∧
      ExpectCorrect bytes.val position.val wanted kind result := by
  obtain ⟨unit, hu, hc⟩ := required_total_correct bytes position
  cases unit with
  | Ok pair =>
    obtain ⟨cp,next⟩ := pair
    by_cases equal : cp = wanted
    · subst cp
      exact ⟨.Ok next, by simp [expect, hu, core.result.Result.Insts.CoreOpsTry.branch], hc⟩
    · refine ⟨.Err ⟨kind,position⟩, ?_, Or.inr ⟨rfl,rfl,cp,next,hc,equal⟩⟩
      simp [expect, hu, core.result.Result.Insts.CoreOpsTry.branch, equal, ntriples.error]
  | Err e =>
    refine ⟨.Err e, ?_, Or.inl hc⟩
    simp [expect, hu, core.result.Result.Insts.CoreOpsTry.branch, same_residual]


private theorem unit_unique {bs : List U8} {start : Nat} {cp other : U32} {next finish : Usize}
    (one : UnitAt bs start cp next) (two : UnitAt bs start other finish) :
    cp = other ∧ next = finish := by
  have pair := Prod.mk.inj (Option.some.inj (one.2.2.symm.trans two.2.2))
  constructor
  · exact UScalar.eq_of_val_eq pair.1
  · apply UScalar.eq_of_val_eq
    have := one.1
    have := two.1
    omega

private theorem malformed_excludes_unit {bs : List U8} {start : Nat} {e : ReadError}
    {cp : U32} {next : Usize} (bad : MalformedError bs start e)
    (unit : UnitAt bs start cp next) : False := by
  rcases bad.2.2 with outside | ⟨inside, invalid⟩
  · have := unit.1; have := unit.2.1; omega
  · rw [unit.2.2] at invalid
    contradiction

private theorem malformed_excludes_eof {bs : List U8} {e : ReadError}
    (bad : MalformedError bs bs.length e) : False := by
  rcases bad.2.2 with outside | ⟨inside, invalid⟩ <;> omega

private theorem unit_actual {bytes : alloc.vec.Vec U8} {position : Usize}
    {cp : U32} {next : Usize} (unit : UnitAt bytes.val position.val cp next) :
    ntriples.at bytes position = .ok (.Ok (some (cp,next))) := by
  obtain ⟨result, hr, hc⟩ := at_total_correct bytes position
  cases result with
  | Ok value =>
    cases value with
    | none => have := unit.1; have := unit.2.1; change position.val = bytes.val.length at hc; omega
    | some pair =>
      obtain ⟨other,finish⟩ := pair
      obtain ⟨rfl,rfl⟩ := unit_unique hc unit
      exact hr
  | Err e => exact False.elim (malformed_excludes_unit hc unit)

private theorem eof_actual {bytes : alloc.vec.Vec U8} {position : Usize}
    (eof : position.val = bytes.val.length) :
    ntriples.at bytes position = .ok (.Ok none) := by
  obtain ⟨result, hr, hc⟩ := at_total_correct bytes position
  cases result with
  | Ok value =>
    cases value with
    | none => exact hr
    | some pair =>
      obtain ⟨cp,next⟩ := pair
      change UnitAt bytes.val position.val cp next at hc
      have := hc.1; have := hc.2.1; omega
  | Err e =>
    change MalformedError bytes.val position.val e at hc
    rw [eof] at hc
    exact False.elim (malformed_excludes_eof hc)

/-- N-Triples §7 horizontal whitespace and EOL productions. -/
def Horizontal (cp : Nat) : Prop := cp = 9 ∨ cp = 32
def EndLine (cp : Nat) : Prop := cp = 10 ∨ cp = 13
private theorem horizontal_total (cp : U32) : horizontal cp = .ok (decide (Horizontal cp.val)) := by
  simp [horizontal, Horizontal, UScalar.eq_equiv]
  split <;> simp_all
private theorem eol_total (cp : U32) : eol cp = .ok (decide (EndLine cp.val)) := by
  simp [eol, EndLine, UScalar.eq_equiv]
  split <;> simp_all

/-- Independent maximal comment body: stop before EOL, or exactly at EOF. -/
inductive CommentRuns (bs : List U8) : Nat → Nat → Prop
  | eof : CommentRuns bs bs.length bs.length
  | eol {start cp next} : UnitAt bs start cp next → EndLine cp.val → CommentRuns bs start start
  | character {start cp next stop} : UnitAt bs start cp next → ¬ EndLine cp.val →
      CommentRuns bs next.val stop → CommentRuns bs start stop
/-- An invalid unit preceded solely by non-EOL comment characters. -/
inductive CommentFails (bs : List U8) : Nat → ReadError → Prop
  | invalid {start error} : MalformedError bs start error → CommentFails bs start error
  | character {start cp next error} : UnitAt bs start cp next → ¬ EndLine cp.val →
      CommentFails bs next.val error → CommentFails bs start error

def CommentCorrect (bs : List U8) (start : Nat) : Parsed Usize ReadError → Prop
  | .Ok stop => CommentRuns bs start stop.val
  | .Err error => CommentFails bs start error

private theorem comment_bounds {bs : List U8} {start stop : Nat}
    (parsed : CommentRuns bs start stop) : start ≤ stop ∧ stop ≤ bs.length := by
  induction parsed with
  | eof => exact ⟨Nat.le_refl _,Nat.le_refl _⟩
  | eol unit ending => unfold UnitAt at unit; omega
  | character unit ending tail ih => unfold UnitAt at unit; omega

/-- Actual byte comment scanning terminates, stops exactly before EOL/at EOF,
    and reports the first malformed UTF-8 unit without skipping over it. -/
theorem skip_comment_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ result, skip_comment bytes position = .ok result ∧ CommentCorrect bytes.val position.val result := by
  obtain ⟨unit, hu, hc⟩ := at_total_correct bytes position
  cases unit with
  | Ok value =>
    cases value with
    | none =>
      refine ⟨.Ok position, ?_, ?_⟩
      · rw [skip_comment]
        simp [hu, core.result.Result.Insts.CoreOpsTry.branch]
      · change CommentRuns bytes.val position.val position.val
        rw [show position.val = bytes.val.length from hc]
        exact CommentRuns.eof
    | some pair =>
      obtain ⟨cp,next⟩ := pair
      by_cases ending : EndLine cp.val
      · refine ⟨.Ok position, ?_, CommentRuns.eol hc ending⟩
        rw [skip_comment]
        simp [hu, core.result.Result.Insts.CoreOpsTry.branch, eol_total, ending]
      · obtain ⟨result, hr, correct⟩ := skip_comment_total_correct bytes next
        refine ⟨result, ?_, ?_⟩
        · rw [skip_comment]
          simp [hu, core.result.Result.Insts.CoreOpsTry.branch, eol_total, ending, hr]
        · cases result with
          | Ok stop => exact CommentRuns.character hc ending correct
          | Err error => exact CommentFails.character hc ending correct
  | Err error =>
    refine ⟨.Err error, ?_, CommentFails.invalid hc⟩
    rw [skip_comment]
    simp [hu, core.result.Result.Insts.CoreOpsTry.branch, same_residual]
termination_by bytes.val.length-position.val
decreasing_by unfold AtCorrect UnitAt at hc; omega


private theorem comment_actual {bytes : alloc.vec.Vec U8} {start stop : Nat}
    (parsed : CommentRuns bytes.val start stop) :
    ∀ (position target : Usize), position.val = start → target.val = stop →
      skip_comment bytes position = .ok (.Ok target) := by
  induction parsed with
  | eof =>
    intro position target hp ht
    have equal : position = target := UScalar.eq_of_val_eq (hp.trans ht.symm)
    subst target
    rw [skip_comment]
    simp [eof_actual hp, core.result.Result.Insts.CoreOpsTry.branch]
  | eol unit ending =>
    intro position target hp ht
    have equal : position = target := UScalar.eq_of_val_eq (hp.trans ht.symm)
    subst target
    have current := unit_actual (hp ▸ unit)
    rw [skip_comment]
    simp [current, core.result.Result.Insts.CoreOpsTry.branch, eol_total, ending]
  | @character start cp next stop unit ending tail ih =>
    intro position target hp ht
    have current := unit_actual (hp ▸ unit)
    have rest := ih next target rfl ht
    rw [skip_comment]
    simp [current, core.result.Result.Insts.CoreOpsTry.branch, eol_total, ending, rest]

/-- Acceptance is exactly the independent maximal comment relation, including
    its stopping offset; valid comments cannot produce a parser diagnostic. -/
theorem skip_comment_accepted_iff (bytes : alloc.vec.Vec U8) (position stop : Usize) :
    skip_comment bytes position = .ok (.Ok stop) ↔ CommentRuns bytes.val position.val stop.val := by
  constructor
  · intro success
    obtain ⟨result, hr, hc⟩ := skip_comment_total_correct bytes position
    have equal := Result.ok_injective (hr.symm.trans success)
    subst result
    exact hc
  · intro valid
    exact comment_actual valid position stop rfl rfl

/-- Optional EOL skipping is enabled only between statements, not inside
    the line-based triple production. Comments are whitespace in either mode. -/
def Spacing (lines : Bool) (cp : Nat) : Prop := Horizontal cp ∨ (lines = true ∧ EndLine cp)

inductive TriviaRuns (bs : List U8) (lines : Bool) : Nat → Nat → Prop
  | eof : TriviaRuns bs lines bs.length bs.length
  | token {start cp next} : UnitAt bs start cp next → ¬ Spacing lines cp.val → cp.val ≠ 35 →
      TriviaRuns bs lines start start
  | space {start cp next stop} : UnitAt bs start cp next → Spacing lines cp.val →
      TriviaRuns bs lines next.val stop → TriviaRuns bs lines start stop
  | commentLine {start cp next stop} : lines = false → UnitAt bs start cp next → cp.val = 35 →
      CommentRuns bs next.val stop → TriviaRuns bs lines start stop
  | commentLines {start cp next stop tailStop} : lines = true → UnitAt bs start cp next → cp.val = 35 →
      CommentRuns bs next.val stop → TriviaRuns bs lines stop tailStop → TriviaRuns bs lines start tailStop

inductive TriviaFails (bs : List U8) (lines : Bool) : Nat → ReadError → Prop
  | invalid {start error} : MalformedError bs start error → TriviaFails bs lines start error
  | space {start cp next error} : UnitAt bs start cp next → Spacing lines cp.val →
      TriviaFails bs lines next.val error → TriviaFails bs lines start error
  | commentBody {start cp next error} : UnitAt bs start cp next → cp.val = 35 →
      CommentFails bs next.val error → TriviaFails bs lines start error
  | afterComment {start cp next stop error} : lines = true → UnitAt bs start cp next → cp.val = 35 →
      CommentRuns bs next.val stop → TriviaFails bs lines stop error → TriviaFails bs lines start error

def TriviaCorrect (bs : List U8) (start : Nat) (lines : Bool) : Parsed Usize ReadError → Prop
  | .Ok stop => TriviaRuns bs lines start stop.val
  | .Err error => TriviaFails bs lines start error

private theorem trivia_bounds {bs : List U8} {start stop : Nat} {lines : Bool}
    (parsed : TriviaRuns bs lines start stop) : start ≤ stop ∧ stop ≤ bs.length := by
  induction parsed with
  | eof => omega
  | token unit spacing marker => unfold UnitAt at unit; omega
  | space unit spacing tail ih => unfold UnitAt at unit; omega
  | commentLine mode unit marker comments =>
    have bounds := comment_bounds comments
    unfold UnitAt at unit
    omega
  | commentLines mode unit marker comments tail ih =>
    have bounds := comment_bounds comments
    unfold UnitAt at unit
    omega

/-- Total, maximal whitespace/comment scanning in both line modes, preserving
    exact source offsets and the first malformed-unit diagnostic. -/
theorem skip_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) (lines : Bool) :
    ∃ result, skip bytes position lines = .ok result ∧ TriviaCorrect bytes.val position.val lines result := by
  obtain ⟨unit, hu, hc⟩ := at_total_correct bytes position
  cases unit with
  | Ok value =>
    cases value with
    | none =>
      refine ⟨.Ok position, ?_, ?_⟩
      · rw [skip]
        simp [hu, core.result.Result.Insts.CoreOpsTry.branch]
      · change TriviaRuns bytes.val lines position.val position.val
        rw [show position.val = bytes.val.length from hc]
        exact TriviaRuns.eof
    | some pair =>
      obtain ⟨cp,next⟩ := pair
      by_cases spacing : Spacing lines cp.val
      · obtain ⟨result, hr, correct⟩ := skip_total_correct bytes next lines
        refine ⟨result, ?_, ?_⟩
        · rw [skip]
          rcases spacing with h | ⟨mode,h⟩
          · simp [hu, core.result.Result.Insts.CoreOpsTry.branch, horizontal_total, h, hr]
          · subst lines
            by_cases horizontalSpace : Horizontal cp.val
            · simp [hu, core.result.Result.Insts.CoreOpsTry.branch, horizontal_total, horizontalSpace, hr]
            · simp [hu, core.result.Result.Insts.CoreOpsTry.branch, horizontal_total, horizontalSpace, eol_total, h, hr]
        · cases result with
          | Ok stop => exact TriviaRuns.space hc spacing correct
          | Err error => exact TriviaFails.space hc spacing correct
      · have notHorizontal : ¬ Horizontal cp.val := by exact fun h => spacing (Or.inl h)
        have notEol : lines = true → ¬ EndLine cp.val := by
          intro mode ending
          exact spacing (Or.inr ⟨mode,ending⟩)
        by_cases marker : cp.val = 35
        · have cpMarker : cp = 35#u32 := by scalar_tac
          obtain ⟨comment, hr, comments⟩ := skip_comment_total_correct bytes next
          cases comment with
          | Err error =>
            refine ⟨.Err error, ?_, TriviaFails.commentBody hc marker comments⟩
            rw [skip]
            cases lines <;> simp [hu, core.result.Result.Insts.CoreOpsTry.branch, horizontal_total,
              notHorizontal, eol_total, notEol, cpMarker, hr, same_residual, Horizontal, EndLine]
          | Ok stop =>
            have bounds := comment_bounds comments
            cases lines with
            | false =>
              refine ⟨.Ok stop, ?_, TriviaRuns.commentLine rfl hc marker comments⟩
              rw [skip]
              simp [hu, core.result.Result.Insts.CoreOpsTry.branch, horizontal_total,
                notHorizontal, cpMarker, hr, Horizontal, EndLine]
            | true =>
              obtain ⟨result, ht, correct⟩ := skip_total_correct bytes stop true
              refine ⟨result, ?_, ?_⟩
              · rw [skip]
                simp [hu, core.result.Result.Insts.CoreOpsTry.branch, horizontal_total,
                  notHorizontal, eol_total, notEol, cpMarker, hr, ht, Horizontal, EndLine]
              · cases result with
                | Ok finalPosition => exact TriviaRuns.commentLines rfl hc marker comments correct
                | Err error => exact TriviaFails.afterComment rfl hc marker comments correct
        · have notMarker : cp ≠ 35#u32 := by scalar_tac
          refine ⟨.Ok position, ?_, TriviaRuns.token hc spacing marker⟩
          rw [skip]
          cases lines <;> simp [hu, core.result.Result.Insts.CoreOpsTry.branch, horizontal_total,
            notHorizontal, eol_total, notEol, notMarker]
  | Err error =>
    refine ⟨.Err error, ?_, TriviaFails.invalid hc⟩
    rw [skip]
    simp [hu, core.result.Result.Insts.CoreOpsTry.branch, same_residual]
termination_by bytes.val.length-position.val
decreasing_by all_goals unfold AtCorrect UnitAt at hc; omega


private theorem trivia_actual {bytes : alloc.vec.Vec U8} {start stop : Nat} {lines : Bool}
    (parsed : TriviaRuns bytes.val lines start stop) :
    ∀ (position target : Usize), position.val = start → target.val = stop →
      skip bytes position lines = .ok (.Ok target) := by
  induction parsed with
  | eof =>
    intro position target hp ht
    have equal : position = target := UScalar.eq_of_val_eq (hp.trans ht.symm)
    subst target
    rw [skip]
    simp [eof_actual hp, core.result.Result.Insts.CoreOpsTry.branch]
  | @token start cp next unit spacing marker =>
    intro position target hp ht
    have equal : position = target := UScalar.eq_of_val_eq (hp.trans ht.symm)
    subst target
    have current := unit_actual (hp ▸ unit)
    have notHorizontal : ¬ Horizontal cp.val := fun h => spacing (Or.inl h)
    have notEol : lines = true → ¬ EndLine cp.val := fun h e => spacing (Or.inr ⟨h,e⟩)
    have notMarker : cp ≠ 35#u32 := by scalar_tac
    rw [skip]
    cases lines <;> simp [current, core.result.Result.Insts.CoreOpsTry.branch,
      horizontal_total, notHorizontal, eol_total, notEol, notMarker]
  | @space start cp next stop unit spacing tail ih =>
    intro position target hp ht
    have current := unit_actual (hp ▸ unit)
    have rest := ih next target rfl ht
    rw [skip]
    rcases spacing with h | ⟨mode,h⟩
    · simp [current, core.result.Result.Insts.CoreOpsTry.branch, horizontal_total, h, rest]
    · subst lines
      by_cases horizontalSpace : Horizontal cp.val
      · simp [current, core.result.Result.Insts.CoreOpsTry.branch, horizontal_total, horizontalSpace, rest]
      · simp [current, core.result.Result.Insts.CoreOpsTry.branch, horizontal_total, horizontalSpace, eol_total, h, rest]
  | @commentLine start cp next stop mode unit marker comments =>
    intro position target hp ht
    subst lines
    have current := unit_actual (hp ▸ unit)
    have body := comment_actual comments next target rfl ht
    have cpMarker : cp = 35#u32 := by scalar_tac
    rw [skip]
    simp [current, core.result.Result.Insts.CoreOpsTry.branch, horizontal_total,
      Horizontal, cpMarker, body]
  | @commentLines start cp next stop tailStop mode unit marker comments tail ih =>
    intro position target hp ht
    subst lines
    have bounds := comment_bounds comments
    have size := bytes.property
    let boundary : Usize := Usize.ofNatCore stop (by
      have bound : stop ≤ Usize.max := Nat.le_trans bounds.2 size
      cases platform : System.Platform.numBits_eq <;>
        simp_all [Usize.max, Usize.numBits] <;> omega)
    have boundaryValue : boundary.val = stop := by simp [boundary]
    have current := unit_actual (hp ▸ unit)
    have body := comment_actual comments next boundary rfl boundaryValue
    have rest := ih boundary target boundaryValue ht
    have cpMarker : cp = 35#u32 := by scalar_tac
    rw [skip]
    simp [current, core.result.Result.Insts.CoreOpsTry.branch, horizontal_total,
      Horizontal, eol_total, EndLine, cpMarker, body, rest]

/-- Both whitespace modes accept exactly their independent relation. The
    successful stopping byte is unique, and valid trivia cannot be rejected. -/
theorem skip_accepted_iff (bytes : alloc.vec.Vec U8) (position stop : Usize) (lines : Bool) :
    skip bytes position lines = .ok (.Ok stop) ↔ TriviaRuns bytes.val lines position.val stop.val := by
  constructor
  · intro success
    obtain ⟨result, hr, hc⟩ := skip_total_correct bytes position lines
    have equal := Result.ok_injective (hr.symm.trans success)
    subst result
    exact hc
  · intro valid
    exact trivia_actual valid position stop rfl rfl


/-- A term builder returns the exact prefix fitting its byte budget; a failed
    private append may hold a prefix, which the enclosing reader discards. -/
def BufferAppend (before more : List U8) (limit : Nat) (accepted : Bool)
    (after : List U8) : Prop :=
  accepted = decide (before.length + more.length ≤ limit) ∧
  after = before ++ more.take (limit-before.length) ∧ after.length ≤ limit

@[local step] private theorem push_spec (output : alloc.vec.Vec U8) (byte : U8) (limit : Usize)
    (bounded : output.val.length ≤ limit.val) :
    ntriples.push output byte limit ⦃ pair =>
      pair.1 = decide (output.val.length < limit.val) ∧
      pair.2.val = (if output.val.length < limit.val then output.val ++ [byte] else output.val) ∧
      pair.2.val.length ≤ limit.val ⦄ := by
  unfold ntriples.push
  by_cases room : output.val.length < limit.val
  · have bound : output.val.length < Usize.max := by scalar_tac
    simp [room, Nat.not_le.mpr room]
    step as ⟨after, contents⟩
    simp [contents]
    omega
  · simp [room, show limit.val ≤ output.val.length from by omega, bounded]

/-- Appending a decoded canonical unit is total and accounts exactly for one
    through four output bytes, including the partial-prefix limit outcome. -/
theorem append_encoded_total_correct (output : alloc.vec.Vec U8)
    (value : encoding.Encoded) (limit : Usize) (bounded : output.val.length ≤ limit.val) :
    ∃ accepted after, append_encoded output value limit = .ok (accepted,after) ∧
      BufferAppend output.val (Rowl.Encoding.Bytes value) limit.val accepted after.val := by
  suffices spec : append_encoded output value limit ⦃ pair =>
      BufferAppend output.val (Rowl.Encoding.Bytes value) limit.val pair.1 pair.2.val ⦄ by
    obtain ⟨⟨accepted,after⟩,hr,hc⟩ := WP.spec_imp_exists spec
    exact ⟨accepted,after,hr,hc⟩
  cases value <;> simp only [append_encoded] <;> step* <;>
    simp_all [BufferAppend, Rowl.Encoding.Bytes]
  all_goals try omega
  all_goals
    have capacities : limit.val-output.val.length = 0 ∨ limit.val-output.val.length = 1 ∨
        limit.val-output.val.length = 2 ∨ limit.val-output.val.length = 3 ∨
        4 ≤ limit.val-output.val.length := by omega
    rcases capacities with h | h | h | h | h
    all_goals try simp_all [List.take_succ_cons]
    all_goals try omega
    all_goals
      have inequalities : output.val.length < limit.val ∧ output.val.length+1 < limit.val ∧
          output.val.length+2 < limit.val ∧ output.val.length+3 < limit.val := by omega
      simp_all [List.take_of_length_le] <;> omega


/-- Hex digit values, without machine subtraction. -/
def HexValue (cp : Nat) : Option Nat :=
  if 48 ≤ cp ∧ cp ≤ 57 then some (cp-48)
  else if 65 ≤ cp ∧ cp ≤ 70 then some (cp-55)
  else if 97 ≤ cp ∧ cp ≤ 102 then some (cp-87) else none

theorem hex_total_correct (cp : U32) :
    ∃ digit, hex cp = .ok digit ∧ digit.map UScalar.val = HexValue cp.val := by
  apply WP.spec_imp_exists
  unfold hex
  step* <;> simp_all [HexValue]
  all_goals split_ifs <;> (try simp_all) <;> scalar_tac

/-- N-Triples §7 IRIREF excludes these raw characters; UCHAR escapes have
    their own production and are validated as scalars separately. -/
def IriCharacter (cp : Nat) : Prop :=
  32 < cp ∧ cp ≠ 60 ∧ cp ≠ 62 ∧ cp ≠ 34 ∧ cp ≠ 123 ∧ cp ≠ 125 ∧
    cp ≠ 124 ∧ cp ≠ 94 ∧ cp ≠ 96 ∧ cp ≠ 92
/-- The complete fourteen PN_CHARS_BASE intervals from the Recommendation. -/
def PnBase (cp : Nat) : Prop :=
  (65 ≤ cp ∧ cp ≤ 90) ∨ (97 ≤ cp ∧ cp ≤ 122) ∨ (192 ≤ cp ∧ cp ≤ 214) ∨
  (216 ≤ cp ∧ cp ≤ 246) ∨ (248 ≤ cp ∧ cp ≤ 767) ∨ (880 ≤ cp ∧ cp ≤ 893) ∨
  (895 ≤ cp ∧ cp ≤ 8191) ∨ (8204 ≤ cp ∧ cp ≤ 8205) ∨ (8304 ≤ cp ∧ cp ≤ 8591) ∨
  (11264 ≤ cp ∧ cp ≤ 12271) ∨ (12289 ≤ cp ∧ cp ≤ 55295) ∨
  (63744 ≤ cp ∧ cp ≤ 64975) ∨ (65008 ≤ cp ∧ cp ≤ 65533) ∨
  (65536 ≤ cp ∧ cp ≤ 983039)
def PnU (cp : Nat) : Prop := PnBase cp ∨ cp = 95 ∨ cp = 58
def AsciiDigit (cp : Nat) : Prop := 48 ≤ cp ∧ cp ≤ 57
def AsciiAlpha (cp : Nat) : Prop := (65 ≤ cp ∧ cp ≤ 90) ∨ (97 ≤ cp ∧ cp ≤ 122)
def Pn (cp : Nat) : Prop := PnU cp ∨ cp = 45 ∨ AsciiDigit cp ∨ cp = 183 ∨
  (768 ≤ cp ∧ cp ≤ 879) ∨ (8255 ≤ cp ∧ cp ≤ 8256)

private theorem in_range_total (cp lower upper : U32) :
    in_range cp lower upper = .ok (decide (lower.val ≤ cp.val ∧ cp.val ≤ upper.val)) := by
  simp [in_range]
  split <;> simp_all

private theorem iri_character_total (cp : U32) :
    iri_character cp = .ok (decide (IriCharacter cp.val)) := by
  simp [iri_character, IriCharacter, bne, beq_eq_decide, UScalar.eq_equiv]
  repeat' (split <;> simp_all)

private theorem true_choice (condition tail : Bool) :
    (if condition = true then (Result.ok true : Result Bool) else Result.ok tail) =
      Result.ok (condition || tail) := by cases condition <;> rfl
private theorem pn_base_total (cp : U32) : pn_base cp = .ok (decide (PnBase cp.val)) := by
  simp only [pn_base, in_range_total, bind_ok, true_choice]
  simp [PnBase]
private theorem pn_u_total (cp : U32) : pn_u cp = .ok (decide (PnU cp.val)) := by
  simp [pn_u, pn_base_total, PnU, UScalar.eq_equiv]
  repeat' split <;> simp_all
private theorem ascii_digit_total (cp : U32) : ascii_digit cp = .ok (decide (AsciiDigit cp.val)) := by
  simp [ascii_digit, AsciiDigit]
  split <;> simp_all
private theorem ascii_alpha_total (cp : U32) : ascii_alpha cp = .ok (decide (AsciiAlpha cp.val)) := by
  simp [ascii_alpha, AsciiAlpha]
  repeat' split <;> simp_all
private theorem pn_total (cp : U32) : pn cp = .ok (decide (Pn cp.val)) := by
  simp [pn, pn_u_total, ascii_digit_total, Pn, UScalar.eq_equiv]
  repeat' split <;> simp_all

/-- Every u32 is classified exactly by the normative token predicates. -/
theorem token_classes_total_correct (cp : U32) :
    iri_character cp = .ok (decide (IriCharacter cp.val)) ∧
    pn_base cp = .ok (decide (PnBase cp.val)) ∧ pn_u cp = .ok (decide (PnU cp.val)) ∧
    pn cp = .ok (decide (Pn cp.val)) ∧ ascii_digit cp = .ok (decide (AsciiDigit cp.val)) ∧
    ascii_alpha cp = .ok (decide (AsciiAlpha cp.val)) :=
  ⟨iri_character_total cp, pn_base_total cp, pn_u_total cp, pn_total cp,
    ascii_digit_total cp, ascii_alpha_total cp⟩


/-- Maximal blank-label suffix, remembering the last non-dot byte. Dots may
    occur internally, but trailing dots belong to the surrounding statement. -/
inductive BlankTail (bs : List U8) : Nat → Nat → Nat → Prop
  | eof {accepted} : BlankTail bs bs.length accepted accepted
  | delimiter {start cp next accepted} : UnitAt bs start cp next → ¬ Pn cp.val → cp.val ≠ 46 →
      BlankTail bs start accepted accepted
  | character {start cp next accepted stop} : UnitAt bs start cp next → Pn cp.val →
      BlankTail bs next.val next.val stop → BlankTail bs start accepted stop
  | period {start cp next accepted stop} : UnitAt bs start cp next → cp.val = 46 →
      BlankTail bs next.val accepted stop → BlankTail bs start accepted stop
inductive BlankTailFailure (bs : List U8) : Nat → ReadError → Prop
  | invalid {start error} : MalformedError bs start error → BlankTailFailure bs start error
  | character {start cp next error} : UnitAt bs start cp next → Pn cp.val →
      BlankTailFailure bs next.val error → BlankTailFailure bs start error
  | period {start cp next error} : UnitAt bs start cp next → cp.val = 46 →
      BlankTailFailure bs next.val error → BlankTailFailure bs start error

def BlankTailCorrect (bs : List U8) (start accepted : Nat) : Parsed Usize ReadError → Prop
  | .Ok stop => BlankTail bs start accepted stop.val
  | .Err e => BlankTailFailure bs start e

private theorem period_not_pn : ¬ Pn 46 := by simp [Pn, PnU, PnBase, AsciiDigit]

/-- Scanning is total, recognizes every PN_CHARS interval, backtracks precisely
    over trailing dots, and diagnoses the first malformed unit. -/
theorem blank_end_total_correct (bytes : alloc.vec.Vec U8) (position accepted : Usize) :
    ∃ result, blank_end bytes position accepted = .ok result ∧
      BlankTailCorrect bytes.val position.val accepted.val result := by
  obtain ⟨unit, hu, hc⟩ := at_total_correct bytes position
  cases unit with
  | Ok value =>
    cases value with
    | none =>
      refine ⟨.Ok accepted, ?_, ?_⟩
      · rw [blank_end]
        simp [hu, core.result.Result.Insts.CoreOpsTry.branch]
      · change BlankTail bytes.val position.val accepted.val accepted.val
        rw [show position.val = bytes.val.length from hc]
        exact BlankTail.eof
    | some pair =>
      obtain ⟨cp,next⟩ := pair
      by_cases allowed : Pn cp.val
      · obtain ⟨result, hr, correct⟩ := blank_end_total_correct bytes next next
        refine ⟨result, ?_, ?_⟩
        · rw [blank_end]
          simp [hu, core.result.Result.Insts.CoreOpsTry.branch, pn_total, allowed, hr]
        · cases result with
          | Ok stop => exact BlankTail.character hc allowed correct
          | Err e => exact BlankTailFailure.character hc allowed correct
      · by_cases period : cp.val = 46
        · have cpPeriod : cp = 46#u32 := by scalar_tac
          obtain ⟨result, hr, correct⟩ := blank_end_total_correct bytes next accepted
          refine ⟨result, ?_, ?_⟩
          · rw [blank_end]
            simp [hu, core.result.Result.Insts.CoreOpsTry.branch, pn_total, cpPeriod, period_not_pn, hr]
          · cases result with
            | Ok stop => exact BlankTail.period hc period correct
            | Err e => exact BlankTailFailure.period hc period correct
        · have notPeriod : cp ≠ 46#u32 := by scalar_tac
          refine ⟨.Ok accepted, ?_, BlankTail.delimiter hc allowed period⟩
          rw [blank_end]
          simp [hu, core.result.Result.Insts.CoreOpsTry.branch, pn_total, allowed, notPeriod]
  | Err e =>
    refine ⟨.Err e, ?_, BlankTailFailure.invalid hc⟩
    rw [blank_end]
    simp [hu, core.result.Result.Insts.CoreOpsTry.branch, same_residual]
termination_by bytes.val.length-position.val
decreasing_by all_goals unfold AtCorrect UnitAt at hc; omega

private theorem blank_tail_actual {bytes : alloc.vec.Vec U8} {start accepted stop : Nat}
    (parsed : BlankTail bytes.val start accepted stop) :
    ∀ (position previous target : Usize), position.val = start → previous.val = accepted →
      target.val = stop → blank_end bytes position previous = .ok (.Ok target) := by
  induction parsed with
  | eof =>
    intro position previous target hp ha ht
    have equal : previous = target := UScalar.eq_of_val_eq (ha.trans ht.symm)
    subst target
    rw [blank_end]
    simp [eof_actual hp, core.result.Result.Insts.CoreOpsTry.branch]
  | @delimiter start cp next accepted unit allowed period =>
    intro position previous target hp ha ht
    have equal : previous = target := UScalar.eq_of_val_eq (ha.trans ht.symm)
    subst target
    have current := unit_actual (hp ▸ unit)
    have notPeriod : cp ≠ 46#u32 := by scalar_tac
    rw [blank_end]
    simp [current, core.result.Result.Insts.CoreOpsTry.branch, pn_total, allowed, notPeriod]
  | @character start cp next accepted stop unit allowed tail ih =>
    intro position previous target hp ha ht
    have current := unit_actual (hp ▸ unit)
    have rest := ih next next target rfl rfl ht
    rw [blank_end]
    simp [current, core.result.Result.Insts.CoreOpsTry.branch, pn_total, allowed, rest]
  | @period start cp next accepted stop unit period tail ih =>
    intro position previous target hp ha ht
    have current := unit_actual (hp ▸ unit)
    have rest := ih next previous target rfl ha ht
    have cpPeriod : cp = 46#u32 := by scalar_tac
    rw [blank_end]
    simp [current, core.result.Result.Insts.CoreOpsTry.branch, pn_total, cpPeriod, period_not_pn, rest]

theorem blank_end_accepted_iff (bytes : alloc.vec.Vec U8) (position previous stop : Usize) :
    blank_end bytes position previous = .ok (.Ok stop) ↔
      BlankTail bytes.val position.val previous.val stop.val := by
  constructor
  · intro success
    obtain ⟨result, hr, hc⟩ := blank_end_total_correct bytes position previous
    have equal := Result.ok_injective (hr.symm.trans success)
    subst result
    exact hc
  · intro valid
    exact blank_tail_actual valid position previous stop rfl rfl rfl

/-- A bounded scan never produces an earlier label boundary or an out-of-source
    one, even when it explores and backtracks over arbitrarily many dots. -/
theorem blank_tail_bounds {bs : List U8} {start accepted stop : Nat}
    (parsed : BlankTail bs start accepted stop) (initial : accepted ≤ start ∧ start ≤ bs.length) :
    accepted ≤ stop ∧ stop ≤ bs.length := by
  induction parsed with
  | eof => omega
  | delimiter unit allowed period => omega
  | character unit allowed tail ih =>
    have rest := ih ⟨Nat.le_refl _,unit.2.1⟩
    have := unit.1
    omega
  | period unit period tail ih =>
    have rest := ih ⟨by have := unit.1; omega,unit.2.1⟩
    exact rest


private theorem copy_term_loop_total (bytes : alloc.vec.Vec U8) (finish : Usize)
    (output : alloc.vec.Vec U8) (position : Usize)
    (range : position.val ≤ finish.val ∧ finish.val ≤ bytes.val.length)
    (prefixBound : output.val.length ≤ position.val) :
    ∃ after, copy_term_loop bytes finish output position = .ok after ∧
      after.val = output.val ++ (bytes.val.drop position.val).take (finish.val-position.val) := by
  rw [copy_term_loop]
  by_cases more : position.val < finish.val
  · have indexBound : position.val < bytes.val.length := by omega
    have element : bytes.index (core.slice.index.SliceIndexUsizeSlice U8) position =
        .ok bytes.val[position.val] := by simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem indexBound]
    have size := bytes.property
    have outputBound : output.val.length < Usize.max := by omega
    obtain ⟨appended, hp, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec output bytes.val[position.val] outputBound)
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := position) (y := 1#usize) (by scalar_tac))
    have nextValue : next.val = position.val+1 := by simpa using hv
    have newBound : appended.val.length ≤ next.val := by simp [contents, nextValue]; omega
    obtain ⟨after, hr, copied⟩ := copy_term_loop_total bytes finish appended next
      ⟨by omega,range.2⟩ newBound
    refine ⟨after, by simp [more, element, hp, hn, hr], ?_⟩
    rw [copied, contents, nextValue, List.drop_eq_getElem_cons indexBound]
    have count : finish.val-position.val = (finish.val-(position.val+1))+1 := by omega
    rw [count]
    simp only [List.take_succ_cons, List.append_assoc, List.singleton_append]
  · have equal : position.val = finish.val := by omega
    exact ⟨output, by simp [more], by simp [equal]⟩
termination_by finish.val-position.val
decreasing_by omega

/-- Copying a parsed span preserves the exact source bytes. Its budget error is
    equivalent to an oversized span and contains the original starting byte. -/
def CopyCorrect (bs : List U8) (start finish limit : Nat) :
    Parsed (alloc.vec.Vec U8) ReadError → Prop
  | .Ok value => finish-start ≤ limit ∧ value.val = (bs.drop start).take (finish-start)
  | .Err error => limit < finish-start ∧ error.kind = .ResourceLimit ∧ error.offset.val = start

theorem copy_term_total_correct (bytes : alloc.vec.Vec U8) (start finish limit : Usize)
    (range : start.val ≤ finish.val ∧ finish.val ≤ bytes.val.length) :
    ∃ result, copy_term bytes start finish limit = .ok result ∧
      CopyCorrect bytes.val start.val finish.val limit.val result := by
  obtain ⟨count, hn, hc⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := finish) (y := start) (by scalar_tac))
  have countValue : count.val = finish.val-start.val := hc.1
  by_cases over : limit.val < finish.val-start.val
  · exact ⟨.Err ⟨.ResourceLimit,start⟩, by simp [copy_term, hn, countValue, over, ntriples.error], over,rfl,rfl⟩
  · obtain ⟨value, hv, copied⟩ := copy_term_loop_total bytes finish (alloc.vec.Vec.new U8) start
      range (by simp)
    exact ⟨.Ok value, by simp [copy_term, hn, countValue, over, hv],
      by simpa [CopyCorrect] using And.intro (show finish.val-start.val ≤ limit.val by omega) copied⟩


private theorem copy_vec_loop_matches (bytes output : alloc.vec.Vec U8) (position : Usize)
    (prefixBound : output.val.length ≤ position.val) :
    copy_vec_loop bytes output position = copy_term_loop bytes bytes.len output position := by
  rw [copy_vec_loop, copy_term_loop]
  by_cases more : position.val < bytes.val.length
  · have element : bytes.index (core.slice.index.SliceIndexUsizeSlice U8) position =
        .ok bytes.val[position.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have size := bytes.property
    have outputBound : output.val.length < Usize.max := by omega
    obtain ⟨appended, hp, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec output bytes.val[position.val] outputBound)
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := position) (y := 1#usize) (by scalar_tac))
    have nextValue : next.val = position.val+1 := by simpa using hv
    have newBound : appended.val.length ≤ next.val := by simp [contents, nextValue]; omega
    have rest := copy_vec_loop_matches bytes appended next newBound
    simp [more, element, hp, hn, rest]
  · simp [more]
termination_by bytes.val.length-position.val
decreasing_by omega

private theorem copy_vec_total (bytes : alloc.vec.Vec U8) : copy_vec bytes = .ok bytes := by
  rw [copy_vec, copy_vec_loop_matches bytes (alloc.vec.Vec.new U8) 0#usize (by simp)]
  obtain ⟨after, hr, contents⟩ := copy_term_loop_total bytes bytes.len (alloc.vec.Vec.new U8) 0#usize
    (by simp) (by simp)
  have equal : after = bytes := (alloc.vec.Vec.eq_iff after bytes).mpr (by simpa using contents)
  simpa [equal] using hr

private theorem required_actual {bytes : alloc.vec.Vec U8} {position : Usize}
    {cp : U32} {next : Usize} (unit : UnitAt bytes.val position.val cp next) :
    required bytes position = .ok (.Ok (cp,next)) := by
  simp [required, unit_actual unit, core.result.Result.Insts.CoreOpsTry.branch]
private theorem expect_actual {bytes : alloc.vec.Vec U8} {position : Usize}
    {wanted : U32} {next : Usize} {kind : ErrorKind} (unit : UnitAt bytes.val position.val wanted next) :
    expect bytes position wanted kind = .ok (.Ok next) := by
  simp [expect, required_actual unit, core.result.Result.Insts.CoreOpsTry.branch]

/-- Successful full BLANK_NODE_LABEL token: `_:` and a legal first character,
    the maximal suffix ending at a non-dot, exact lexical bytes and caller scope. -/
def BlankToken (bs scope : List U8) (start limit : Nat) (node : rdf.BlankNode) (stop : Usize) : Prop :=
  ∃ colon begin : Usize, ∃ first : U32, ∃ next : Usize,
    UnitAt bs start 95#u32 colon ∧ UnitAt bs colon.val 58#u32 begin ∧
    UnitAt bs begin.val first next ∧ (PnU first.val ∨ AsciiDigit first.val) ∧
    BlankTail bs next.val next.val stop.val ∧ stop.val-begin.val ≤ limit ∧
    node.scope.val = scope ∧ node.label.val = (bs.drop begin.val).take (stop.val-begin.val)

/-- Every rejection is at a specific grammar/decoding/budget stage. No unknown
    failure or partial blank identity is admitted by this relation. -/
inductive BlankError (bs : List U8) (start limit : Nat) : ReadError → Prop
  | opening {e} : ExpectCorrect bs start 95#u32 .InvalidBlankLabel (.Err e) → BlankError bs start limit e
  | colon {after e} : UnitAt bs start 95#u32 after →
      ExpectCorrect bs after.val 58#u32 .InvalidBlankLabel (.Err e) → BlankError bs start limit e
  | first {after begin e} : UnitAt bs start 95#u32 after → UnitAt bs after.val 58#u32 begin →
      RequiredError bs begin.val e → BlankError bs start limit e
  | character {after begin cp next} : UnitAt bs start 95#u32 after → UnitAt bs after.val 58#u32 begin →
      UnitAt bs begin.val cp next → ¬ (PnU cp.val ∨ AsciiDigit cp.val) →
      BlankError bs start limit ⟨.InvalidBlankLabel,begin⟩
  | tail {after begin cp next e} : UnitAt bs start 95#u32 after → UnitAt bs after.val 58#u32 begin →
      UnitAt bs begin.val cp next → (PnU cp.val ∨ AsciiDigit cp.val) →
      BlankTailFailure bs next.val e → BlankError bs start limit e
  | budget {after begin cp next e} {stop : Usize} : UnitAt bs start 95#u32 after → UnitAt bs after.val 58#u32 begin →
      UnitAt bs begin.val cp next → (PnU cp.val ∨ AsciiDigit cp.val) →
      BlankTail bs next.val next.val stop.val → CopyCorrect bs begin.val stop.val limit (.Err e) →
      BlankError bs start limit e

def BlankCorrect (bs scope : List U8) (start limit : Nat) :
    Parsed (rdf.BlankNode × Usize) ReadError → Prop
  | .Ok (node,stop) => BlankToken bs scope start limit node stop
  | .Err error => BlankError bs start limit error

/-- Complete byte-to-blank-token composition, including strict decoding,
    punctuation, all Unicode ranges, exact scope/label and resource diagnostics. -/
theorem blank_total_correct (bytes scope : alloc.vec.Vec U8) (start limit : Usize) :
    ∃ result, blank bytes start scope limit = .ok result ∧
      BlankCorrect bytes.val scope.val start.val limit.val result := by
  obtain ⟨opening, ho, openingCorrect⟩ := expect_total_correct bytes start 95#u32 .InvalidBlankLabel
  cases opening with
  | Err e =>
    refine ⟨.Err e, ?_, BlankError.opening openingCorrect⟩
    simp [blank, ho, core.result.Result.Insts.CoreOpsTry.branch, same_residual]
  | Ok after =>
    obtain ⟨colon, hc, colonCorrect⟩ := expect_total_correct bytes after 58#u32 .InvalidBlankLabel
    cases colon with
    | Err e =>
      refine ⟨.Err e, ?_, BlankError.colon openingCorrect colonCorrect⟩
      simp [blank, ho, hc, core.result.Result.Insts.CoreOpsTry.branch, same_residual]
    | Ok begin =>
      obtain ⟨unit, hu, unitCorrect⟩ := required_total_correct bytes begin
      cases unit with
      | Err e =>
        refine ⟨.Err e, ?_, BlankError.first openingCorrect colonCorrect unitCorrect⟩
        simp [blank, ho, hc, hu, core.result.Result.Insts.CoreOpsTry.branch, same_residual]
      | Ok pair =>
        obtain ⟨cp,next⟩ := pair
        by_cases allowed : PnU cp.val ∨ AsciiDigit cp.val
        · obtain ⟨tail, ht, tailCorrect⟩ := blank_end_total_correct bytes next next
          cases tail with
          | Err e =>
            refine ⟨.Err e, ?_, BlankError.tail openingCorrect colonCorrect unitCorrect allowed tailCorrect⟩
            rcases allowed with h | h <;>
              simp [blank, ho, hc, hu, pn_u_total, ascii_digit_total, h, ht,
                core.result.Result.Insts.CoreOpsTry.branch, same_residual]
          | Ok stop =>
            have bounds := blank_tail_bounds tailCorrect ⟨Nat.le_refl _,unitCorrect.2.1⟩
            have range : begin.val ≤ stop.val ∧ stop.val ≤ bytes.val.length := by
              have := unitCorrect.1
              omega
            obtain ⟨copied, hl, copiedCorrect⟩ := copy_term_total_correct bytes begin stop limit range
            cases copied with
            | Err e =>
              refine ⟨.Err e, ?_, BlankError.budget openingCorrect colonCorrect unitCorrect allowed tailCorrect copiedCorrect⟩
              rcases allowed with h | h <;>
                simp [blank, ho, hc, hu, pn_u_total, ascii_digit_total, h, ht, hl,
                  core.result.Result.Insts.CoreOpsTry.branch, same_residual]
            | Ok label =>
              refine ⟨.Ok (⟨scope,label⟩,stop), ?_, ?_⟩
              · rcases allowed with h | h <;>
                  simp [blank, ho, hc, hu, pn_u_total, ascii_digit_total, h, ht, hl, copy_vec_total,
                    core.result.Result.Insts.CoreOpsTry.branch]
              · exact ⟨after,begin,cp,next,openingCorrect,colonCorrect,unitCorrect,allowed,
                  tailCorrect,copiedCorrect.1,rfl,copiedCorrect.2⟩
        · refine ⟨.Err ⟨.InvalidBlankLabel,begin⟩, ?_, BlankError.character openingCorrect colonCorrect unitCorrect allowed⟩
          have badU : ¬ PnU cp.val := fun h => allowed (Or.inl h)
          have badDigit : ¬ AsciiDigit cp.val := fun h => allowed (Or.inr h)
          simp [blank, ho, hc, hu, pn_u_total, ascii_digit_total, badU, badDigit, ntriples.error,
            core.result.Result.Insts.CoreOpsTry.branch]


/-- Soundness and completeness of the whole blank-token reader, with exact
    returned identity and stopping offset rather than only syntax acceptance. -/
theorem blank_accepted_iff (bytes scope : alloc.vec.Vec U8) (start limit : Usize)
    (node : rdf.BlankNode) (stop : Usize) :
    blank bytes start scope limit = .ok (.Ok (node,stop)) ↔
      BlankToken bytes.val scope.val start.val limit.val node stop := by
  constructor
  · intro success
    obtain ⟨result, hr, hc⟩ := blank_total_correct bytes scope start limit
    have equal := Result.ok_injective (hr.symm.trans success)
    subst result
    exact hc
  · rintro ⟨after,begin,cp,next,opening,colon,unit,allowed,tail,size,scopeBytes,labelBytes⟩
    have ho := expect_actual (kind := ErrorKind.InvalidBlankLabel) opening
    have hc := expect_actual (kind := ErrorKind.InvalidBlankLabel) colon
    have hu := required_actual unit
    have ht := (blank_end_accepted_iff bytes next next stop).mpr tail
    have bounds := blank_tail_bounds tail ⟨Nat.le_refl _,unit.2.1⟩
    have range : begin.val ≤ stop.val ∧ stop.val ≤ bytes.val.length := by have := unit.1; omega
    obtain ⟨copied, hl, copiedCorrect⟩ := copy_term_total_correct bytes begin stop limit range
    cases copied with
    | Err e =>
      have over := copiedCorrect.1
      omega
    | Ok label =>
      have nodeEqual : node = ⟨scope,label⟩ := by
        cases node with
        | mk oldScope oldLabel =>
          have scopeEqual : oldScope = scope := (alloc.vec.Vec.eq_iff oldScope scope).mpr scopeBytes
          have labelEqual : oldLabel = label := (alloc.vec.Vec.eq_iff oldLabel label).mpr (labelBytes.trans copiedCorrect.2.symm)
          subst oldScope
          subst oldLabel
          rfl
      rw [nodeEqual]
      rcases allowed with h | h <;>
        simp [blank, ho, hc, hu, pn_u_total, ascii_digit_total, h, ht, hl, copy_vec_total,
          core.result.Result.Insts.CoreOpsTry.branch]


/-- Independent fixed-length hexadecimal production and left-to-right numeric
    value. It uses unbounded naturals, not the Rust accumulator or arithmetic. -/
inductive HexDigits (bs : List U8) : Nat → Nat → Nat → Nat → Nat → Prop
  | empty {start value} : HexDigits bs start 0 value value start
  | digit {start cp next count value d result stop} : UnitAt bs start cp next →
      HexValue cp.val = some d → HexDigits bs next.val count (value*16+d) result stop →
      HexDigits bs start (count+1) value result stop

inductive HexError (bs : List U8) (slash : Usize) : Nat → Nat → Nat → ReadError → Prop
  | required {start count value e} : RequiredError bs start e → HexError bs slash start (count+1) value e
  | invalidDigit {start cp next count value} : UnitAt bs start cp next → HexValue cp.val = none →
      HexError bs slash start (count+1) value ⟨.InvalidEscape,slash⟩
  | digit {start cp next count value d e} : UnitAt bs start cp next → HexValue cp.val = some d →
      HexError bs slash next.val count (value*16+d) e → HexError bs slash start (count+1) value e
  | invalidScalar {start value} : ¬ Rowl.Encoding.Scalar value →
      HexError bs slash start 0 value ⟨.InvalidEscape,slash⟩

def DigitsCorrect (bs : List U8) (slash : Usize) (start count initial : Nat) :
    Parsed (U32 × Usize) ReadError → Prop
  | .Ok (cp,stop) => Rowl.Encoding.Scalar cp.val ∧ HexDigits bs start count initial cp.val stop.val
  | .Err e => HexError bs slash start count initial e

private theorem hex_value_bound {cp d : Nat} (digit : HexValue cp = some d) : d < 16 := by
  unfold HexValue at digit
  split_ifs at digit <;> simp_all <;> omega

/-- All accumulator steps fit even on 32-bit targets: eight hex digits need
    at most 32 value bits, while the implementation accumulates in u64. -/
private theorem hex_accumulator_step (value : U64) (i count : Usize) (d : U32)
    (bounds : i.val < count.val ∧ count.val ≤ 8) (accBound : value.val < 16^i.val) (digit : d.val < 16) :
    value.val*16+d.val < 16^(i.val+1) ∧ value.val*16+d.val < 4294967296 := by
  have powStep := Nat.pow_succ 16 i.val
  have powBound : 16^(i.val+1) ≤ 16^8 := Nat.pow_le_pow_right (by decide) (by omega)
  have small : value.val*16+d.val < 16^(i.val+1) := by rw [powStep]; omega
  constructor
  · exact small
  · have bound : 16^(i.val+1) ≤ 4294967296 := by simpa using powBound
    omega

private theorem unicode_escape_loop_total (bytes : alloc.vec.Vec U8) (slash position count : Usize)
    (value : U64) (i : Usize) (bounds : i.val ≤ count.val ∧ count.val ≤ 8)
    (accBound : value.val < 16^i.val) :
    ∃ result, unicode_escape_loop bytes slash position count value i = .ok result ∧
      DigitsCorrect bytes.val slash position.val (count.val-i.val) value.val result := by
  by_cases more : i.val < count.val
  · obtain ⟨unit, hu, hc⟩ := required_total_correct bytes position
    have remaining : count.val-i.val = (count.val-(i.val+1))+1 := by omega
    cases unit with
    | Err e =>
      refine ⟨.Err e, ?_, ?_⟩
      · rw [unicode_escape_loop]
        simp [more, hu, core.result.Result.Insts.CoreOpsTry.branch, same_residual]
      · change HexError bytes.val slash position.val (count.val-i.val) value.val e
        rw [remaining]
        exact HexError.required hc
    | Ok pair =>
      obtain ⟨cp,next⟩ := pair
      obtain ⟨digit, hd, digitCorrect⟩ := hex_total_correct cp
      cases digit with
      | none =>
        refine ⟨.Err ⟨.InvalidEscape,slash⟩, ?_, ?_⟩
        · rw [unicode_escape_loop]
          simp [more, hu, core.result.Result.Insts.CoreOpsTry.branch, hd, ntriples.error]
        · change HexError bytes.val slash position.val (count.val-i.val) value.val _
          rw [remaining]
          exact HexError.invalidDigit hc digitCorrect.symm
      | some d =>
        have hexValue : HexValue cp.val = some d.val := by simpa using digitCorrect.symm
        have digitBound := hex_value_bound hexValue
        have accumulator := hex_accumulator_step value i count d ⟨more,bounds.2⟩ accBound digitBound
        obtain ⟨product, hp, productValue⟩ := WP.spec_imp_exists
          (U64.mul_spec (x := value) (y := 16#u64) (by scalar_tac))
        have productNat : product.val = value.val*16 := by simpa using productValue
        let converted := core.convert.num.FromU64U32.from d
        have convertedValue : converted.val = d.val := by simp [converted]
        obtain ⟨acc, ha, accValue⟩ := WP.spec_imp_exists
          (U64.add_spec (x := product) (y := converted) (by scalar_tac))
        have accNat : acc.val = value.val*16+d.val := by simpa [productNat, convertedValue] using accValue
        obtain ⟨j, hj, jValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
        have jNat : j.val = i.val+1 := by simpa using jValue
        obtain ⟨result, hr, correct⟩ := unicode_escape_loop_total bytes slash next count acc j
          ⟨by omega,bounds.2⟩ (by simpa [jNat,accNat] using accumulator.1)
        refine ⟨result, ?_, ?_⟩
        · rw [unicode_escape_loop]
          simp [more,hu,core.result.Result.Insts.CoreOpsTry.branch,hd,hp,hj,lift]
          change (do let nextValue ← product + converted
                     unicode_escape_loop bytes slash next count nextValue j) = .ok result
          simp [ha,hr]
        · rw [remaining]
          cases result with
          | Ok pair =>
            obtain ⟨resultCp,stop⟩ := pair
            exact ⟨correct.1, HexDigits.digit hc hexValue (by simpa [jNat,accNat] using correct.2)⟩
          | Err e => exact HexError.digit hc hexValue (by simpa [DigitsCorrect,jNat,accNat] using correct)
  · have done : i.val = count.val := by omega
    have remaining : count.val-i.val = 0 := by omega
    by_cases valid : Rowl.Encoding.Scalar value.val
    · let cp := UScalar.cast .U32 value
      have cpValue : cp.val = value.val := by
        have result := UScalar.cast_inBounds_spec .U32 value (by unfold Rowl.Encoding.Scalar at valid; scalar_tac)
        simpa [cp,lift] using result
      refine ⟨.Ok (cp,position), ?_, ?_⟩
      · have upper : value.val ≤ 1114111 := valid.1
        have noSurrogate := valid.2
        rw [unicode_escape_loop]
        by_cases low : 55296 ≤ value.val
        · have high : ¬ value.val ≤ 57343 := by intro h; exact noSurrogate ⟨low,h⟩
          simp [more, show ¬ 1114111 < value.val from by omega, low, high, cp, lift]
        · simp [more, show ¬ 1114111 < value.val from by omega, low, cp, lift]
      · exact ⟨by simpa [cpValue] using valid, by simpa [remaining,cpValue] using (HexDigits.empty (bs := bytes.val) (start := position.val) (value := value.val))⟩
    · refine ⟨.Err ⟨.InvalidEscape,slash⟩, ?_, ?_⟩
      · rw [unicode_escape_loop]
        by_cases over : 1114111 < value.val
        · simp [more,over,ntriples.error]
        · have low : 55296 ≤ value.val := by unfold Rowl.Encoding.Scalar at valid; omega
          have high : value.val ≤ 57343 := by unfold Rowl.Encoding.Scalar at valid; omega
          simp [more,over,low,high,ntriples.error]
      · simpa [DigitsCorrect,remaining] using (HexError.invalidScalar (bs := bytes.val) (slash := slash) (start := position.val) valid)
termination_by count.val-i.val
decreasing_by omega

/-- Total exact hexadecimal UCHAR payload decoding, for the bounded counts
    used by the two normative escape productions. -/
theorem unicode_escape_total_correct (bytes : alloc.vec.Vec U8) (slash position count : Usize)
    (bounded : count.val ≤ 8) :
    ∃ result, unicode_escape bytes slash position count = .ok result ∧
      DigitsCorrect bytes.val slash position.val count.val 0 result := by
  obtain ⟨result, hr, correct⟩ := unicode_escape_loop_total bytes slash position count 0#u64 0#usize
    ⟨by simp,bounded⟩ (by simp)
  exact ⟨result,hr,by simpa using correct⟩


private theorem required_error_excludes_unit {bs : List U8} {start : Nat} {e : ReadError}
    {cp : U32} {next : Usize} (bad : RequiredError bs start e)
    (unit : UnitAt bs start cp next) : False := by
  rcases bad with malformed | ⟨kind,offset,eof⟩
  · exact malformed_excludes_unit malformed unit
  · have := unit.1; have := unit.2.1; omega

private theorem hex_error_excludes_digits {bs : List U8} {slash : Usize}
    {start count initial : Nat} {e : ReadError}
    (bad : HexError bs slash start count initial e) :
    ∀ {result stop}, HexDigits bs start count initial result stop →
      Rowl.Encoding.Scalar result → False := by
  induction bad with
  | required error =>
    intro result stop valid scalar
    cases valid with
    | digit unit hex tail => exact required_error_excludes_unit error unit
  | invalidDigit unit invalid =>
    intro result stop valid scalar
    cases valid with
    | digit otherUnit hex tail =>
      obtain ⟨rfl,rfl⟩ := unit_unique unit otherUnit
      rw [hex] at invalid
      contradiction
  | digit unit hex bad ih =>
    intro result stop valid scalar
    cases valid with
    | digit otherUnit otherHex tail =>
      obtain ⟨rfl,rfl⟩ := unit_unique unit otherUnit
      have equal := Option.some.inj (hex.symm.trans otherHex)
      cases equal
      exact ih tail scalar
  | invalidScalar invalid =>
    intro result stop valid scalar
    cases valid
    exact invalid scalar

private theorem hex_digits_unique {bs : List U8} {start count initial result stop : Nat}
    (one : HexDigits bs start count initial result stop) :
    ∀ {other finish}, HexDigits bs start count initial other finish → result = other ∧ stop = finish := by
  induction one with
  | empty =>
    intro other finish two
    cases two
    exact ⟨rfl,rfl⟩
  | digit unit hex tail ih =>
    intro other finish two
    cases two with
    | digit otherUnit otherHex rest =>
      obtain ⟨rfl,rfl⟩ := unit_unique unit otherUnit
      have equal := Option.some.inj (hex.symm.trans otherHex)
      cases equal
      exact ih rest

/-- A valid fixed-length scalar escape cannot be rejected or decoded to a
    different value/offset. This is exact semantic completeness. -/
theorem unicode_escape_accepted_iff (bytes : alloc.vec.Vec U8) (slash position count : Usize)
    (bounded : count.val ≤ 8) (cp : U32) (stop : Usize) :
    unicode_escape bytes slash position count = .ok (.Ok (cp,stop)) ↔
      Rowl.Encoding.Scalar cp.val ∧ HexDigits bytes.val position.val count.val 0 cp.val stop.val := by
  constructor
  · intro success
    obtain ⟨result, hr, hc⟩ := unicode_escape_total_correct bytes slash position count bounded
    have equal := Result.ok_injective (hr.symm.trans success)
    subst result
    exact hc
  · intro valid
    obtain ⟨result, hr, hc⟩ := unicode_escape_total_correct bytes slash position count bounded
    cases result with
    | Err e => exact False.elim (hex_error_excludes_digits hc valid.2 valid.1)
    | Ok pair =>
      obtain ⟨other,finish⟩ := pair
      obtain ⟨cpEqual,stopEqual⟩ := hex_digits_unique hc.2 valid.2
      have cpSame : other = cp := UScalar.eq_of_val_eq cpEqual
      have stopSame : finish = stop := UScalar.eq_of_val_eq stopEqual
      simpa [cpSame,stopSame] using hr

theorem hex_digits_progress {bs : List U8} {start count initial result stop : Nat}
    (parsed : HexDigits bs start count initial result stop) :
    (count = 0 ∧ stop = start) ∨ (0 < count ∧ start < stop ∧ stop ≤ bs.length) := by
  induction parsed with
  | empty => exact Or.inl ⟨rfl,rfl⟩
  | digit unit hex tail ih =>
    apply Or.inr
    rcases ih with ⟨zero,same⟩ | ⟨positive,advanced,bounded⟩
    · have := unit.1; have := unit.2.1; omega
    · have := unit.1; omega


/-- The eight ECHAR spellings and their exact decoded values (§7 grammar). -/
def EcharValue (cp : Nat) : Option Nat :=
  if cp = 116 then some 9 else if cp = 98 then some 8 else if cp = 110 then some 10
  else if cp = 114 then some 13 else if cp = 102 then some 12 else if cp = 34 then some 34
  else if cp = 39 then some 39 else if cp = 92 then some 92 else none

/-- Escape payload immediately after a caller-decoded backslash. IRI tokens
    admit UCHAR only; string tokens admit UCHAR and ECHAR. -/
inductive EscapeValue (bs : List U8) (iri : Bool) : Nat → U32 → Usize → Prop
  | four {start next cp stop} : UnitAt bs start 117#u32 next → Rowl.Encoding.Scalar cp.val →
      HexDigits bs next.val 4 0 cp.val stop.val → EscapeValue bs iri start cp stop
  | eight {start next cp stop} : UnitAt bs start 85#u32 next → Rowl.Encoding.Scalar cp.val →
      HexDigits bs next.val 8 0 cp.val stop.val → EscapeValue bs iri start cp stop
  | character {start marker next cp} : iri = false → UnitAt bs start marker next →
      EcharValue marker.val = some cp.val → EscapeValue bs iri start cp next

inductive EscapeError (bs : List U8) (slash : Usize) (iri : Bool) : Nat → ReadError → Prop
  | required {start error} : RequiredError bs start error → EscapeError bs slash iri start error
  | four {start next error} : UnitAt bs start 117#u32 next →
      HexError bs slash next.val 4 0 error → EscapeError bs slash iri start error
  | eight {start next error} : UnitAt bs start 85#u32 next →
      HexError bs slash next.val 8 0 error → EscapeError bs slash iri start error
  | forbidden {start marker next} : iri = true → UnitAt bs start marker next →
      marker.val ≠ 117 → marker.val ≠ 85 → EscapeError bs slash iri start ⟨.InvalidEscape,slash⟩
  | character {start marker next} : iri = false → UnitAt bs start marker next →
      marker.val ≠ 117 → marker.val ≠ 85 → EcharValue marker.val = none →
      EscapeError bs slash iri start ⟨.InvalidEscape,slash⟩

def EscapeCorrect (bs : List U8) (slash : Usize) (start : Nat) (iri : Bool) :
    Parsed (U32 × Usize) ReadError → Prop
  | .Ok (cp,stop) => EscapeValue bs iri start cp stop
  | .Err error => EscapeError bs slash iri start error

@[local simp] private theorem marker_116_value : (116#32#uscalar : U32).val = 116 := rfl
@[local simp] private theorem marker_98_value : (98#32#uscalar : U32).val = 98 := rfl
@[local simp] private theorem marker_110_value : (110#32#uscalar : U32).val = 110 := rfl
@[local simp] private theorem marker_114_value : (114#32#uscalar : U32).val = 114 := rfl
@[local simp] private theorem marker_102_value : (102#32#uscalar : U32).val = 102 := rfl
@[local simp] private theorem marker_34_value : (34#32#uscalar : U32).val = 34 := rfl
@[local simp] private theorem marker_39_value : (39#32#uscalar : U32).val = 39 := rfl
@[local simp] private theorem marker_92_value : (92#32#uscalar : U32).val = 92 := rfl

/-- Exact total escape-payload recognition. The source backslash itself is
    established by the quoted-token caller, not assumed read by this function. -/
theorem escape_total_correct (bytes : alloc.vec.Vec U8) (slash position : Usize) (iri : Bool) :
    ∃ result, escape bytes slash position iri = .ok result ∧
      EscapeCorrect bytes.val slash position.val iri result := by
  obtain ⟨unit, hu, hc⟩ := required_total_correct bytes position
  cases unit with
  | Err error =>
    refine ⟨.Err error, ?_, EscapeError.required hc⟩
    simp [escape, hu, core.result.Result.Insts.CoreOpsTry.branch, same_residual]
  | Ok pair =>
    obtain ⟨marker,next⟩ := pair
    by_cases four : marker = 117#u32
    · subst marker
      obtain ⟨result, hr, correct⟩ := unicode_escape_total_correct bytes slash next 4#usize (by simp)
      refine ⟨result, by simp [escape, hu, core.result.Result.Insts.CoreOpsTry.branch, hr], ?_⟩
      cases result with
      | Ok pair => obtain ⟨cp,stop⟩ := pair; exact EscapeValue.four hc correct.1 (by simpa using correct.2)
      | Err error => exact EscapeError.four hc (by simpa [DigitsCorrect] using correct)
    · by_cases eight : marker = 85#u32
      · subst marker
        obtain ⟨result, hr, correct⟩ := unicode_escape_total_correct bytes slash next 8#usize (by simp)
        refine ⟨result, by simp [escape, hu, core.result.Result.Insts.CoreOpsTry.branch, hr], ?_⟩
        cases result with
        | Ok pair => obtain ⟨cp,stop⟩ := pair; exact EscapeValue.eight hc correct.1 (by simpa using correct.2)
        | Err error => exact EscapeError.eight hc (by simpa [DigitsCorrect] using correct)
      · have notFour : marker.val ≠ 117 := by simpa [UScalar.eq_equiv] using four
        have notEight : marker.val ≠ 85 := by simpa [UScalar.eq_equiv] using eight
        cases iri with
        | true =>
          refine ⟨.Err ⟨.InvalidEscape,slash⟩, ?_, EscapeError.forbidden rfl hc notFour notEight⟩
          simp [escape, hu, core.result.Result.Insts.CoreOpsTry.branch, four, eight, ntriples.error]
        | false =>
          suffices spec : escape bytes slash position false ⦃ result =>
              EscapeCorrect bytes.val slash position.val false result ⦄ by
            obtain ⟨result, hr, correct⟩ := WP.spec_imp_exists spec
            exact ⟨result, hr, correct⟩
          simp [escape, hu, core.result.Result.Insts.CoreOpsTry.branch, four, eight, ntriples.error]
          split
          all_goals simp only [WP.spec_ok, EscapeCorrect]
          all_goals first
            | exact EscapeValue.character rfl hc (by rfl)
            | exact EscapeError.character rfl hc notFour notEight (by
                simp_all [EcharValue, UScalar.eq_equiv])


private theorem echar_codes (marker cp : U32) : EcharValue marker.val = some cp.val ↔
    (marker = 116#u32 ∧ cp = 9#u32) ∨ (marker = 98#u32 ∧ cp = 8#u32) ∨
    (marker = 110#u32 ∧ cp = 10#u32) ∨ (marker = 114#u32 ∧ cp = 13#u32) ∨
    (marker = 102#u32 ∧ cp = 12#u32) ∨ (marker = 34#u32 ∧ cp = 34#u32) ∨
    (marker = 39#u32 ∧ cp = 39#u32) ∨ (marker = 92#u32 ∧ cp = 92#u32) := by
  simp only [EcharValue, UScalar.eq_equiv]
  split_ifs <;> simp_all

theorem escape_accepted_iff (bytes : alloc.vec.Vec U8) (slash position : Usize) (iri : Bool)
    (cp : U32) (stop : Usize) :
    escape bytes slash position iri = .ok (.Ok (cp,stop)) ↔
      EscapeValue bytes.val iri position.val cp stop := by
  constructor
  · intro success
    obtain ⟨result, hr, hc⟩ := escape_total_correct bytes slash position iri
    have equal := Result.ok_injective (hr.symm.trans success)
    subst result
    exact hc
  · intro valid
    cases valid with
    | four unit scalar digits =>
      have readMarker := required_actual unit
      have readDigits := (unicode_escape_accepted_iff bytes slash _ 4#usize (by simp) cp stop).mpr ⟨scalar,digits⟩
      simp [escape, readMarker, core.result.Result.Insts.CoreOpsTry.branch, readDigits]
    | eight unit scalar digits =>
      have readMarker := required_actual unit
      have readDigits := (unicode_escape_accepted_iff bytes slash _ 8#usize (by simp) cp stop).mpr ⟨scalar,digits⟩
      simp [escape, readMarker, core.result.Result.Insts.CoreOpsTry.branch, readDigits]
    | character mode unit decoded =>
      subst iri
      have readMarker := required_actual unit
      rcases (echar_codes _ _).mp decoded with
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        simp [escape, readMarker, core.result.Result.Insts.CoreOpsTry.branch, UScalar.ofNat, UScalar.ofNatCore]

/-- Every accepted payload yields a valid scalar and consumes strictly more
    original bytes, with its final offset still inside the source. -/
theorem escape_value_progress {bs : List U8} {iri : Bool} {start : Nat} {cp : U32} {stop : Usize}
    (valid : EscapeValue bs iri start cp stop) :
    Rowl.Encoding.Scalar cp.val ∧ start < stop.val ∧ stop.val ≤ bs.length := by
  cases valid with
  | four unit scalar digits =>
    have progress := hex_digits_progress digits
    constructor
    · exact scalar
    · have := unit.1; omega
  | eight unit scalar digits =>
    have progress := hex_digits_progress digits
    constructor
    · exact scalar
    · have := unit.1; omega
  | character mode unit decoded =>
    constructor
    · rcases (echar_codes _ _).mp decoded with
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        simp [Rowl.Encoding.Scalar]
    · exact ⟨unit.1,unit.2.1⟩


/-- Strict byte recognition excludes every non-scalar code point, independently
    of the encoder; this connects ordinary quoted characters to scalar encoding. -/
private theorem prefix_scalar {bs : List U8} {start cp width : Nat}
    (unit : Prefix bs start = some (cp,width)) : Rowl.Encoding.Scalar cp := by
  unfold Prefix at unit
  cases first : bs[start]? with
  | none => simp [first] at unit
  | some a =>
    simp only [first,Option.bind_some,Option.bind_eq_bind] at unit
    by_cases ascii : a.val < 128
    · simp [ascii] at unit
      unfold Rowl.Encoding.Scalar
      omega
    · simp only [ascii,↓reduceIte] at unit
      by_cases pair : a.val < 224
      · simp only [pair,↓reduceIte] at unit
        cases second : bs[start+1]? with
        | none => simp [second] at unit
        | some b =>
          simp only [second,Option.bind_some,Option.bind_eq_bind] at unit
          by_cases grammar : Pair a.val b.val
          · simp [grammar] at unit
            have bounds := (byte_grammar_scalar_ranges a.val b.val 0 0).1 grammar
            unfold Rowl.Encoding.Scalar
            omega
          · simp [grammar] at unit
      · simp only [pair,↓reduceIte] at unit
        by_cases triple : a.val < 240
        · simp only [triple,↓reduceIte] at unit
          cases second : bs[start+1]? with
          | none => simp [second] at unit
          | some b =>
            simp only [second,Option.bind_some,Option.bind_eq_bind] at unit
            cases third : bs[start+2]? with
            | none => simp [third] at unit
            | some c =>
              simp only [third,Option.bind_some,Option.bind_eq_bind] at unit
              by_cases grammar : Triple a.val b.val c.val
              · simp [grammar] at unit
                have bounds := (byte_grammar_scalar_ranges a.val b.val c.val 0).2.1 grammar
                unfold Rowl.Encoding.Scalar
                omega
              · simp [grammar] at unit
        · simp only [triple,↓reduceIte] at unit
          cases second : bs[start+1]? with
          | none => simp [second] at unit
          | some b =>
            simp only [second,Option.bind_some,Option.bind_eq_bind] at unit
            cases third : bs[start+2]? with
            | none => simp [third] at unit
            | some c =>
              simp only [third,Option.bind_some,Option.bind_eq_bind] at unit
              cases fourth : bs[start+3]? with
              | none => simp [fourth] at unit
              | some d =>
                simp only [fourth,Option.bind_some,Option.bind_eq_bind] at unit
                by_cases grammar : Quad a.val b.val c.val d.val
                · simp [grammar] at unit
                  have bounds := (byte_grammar_scalar_ranges a.val b.val c.val d.val).2.2 grammar
                  unfold Rowl.Encoding.Scalar
                  omega
                · simp [grammar] at unit

private theorem unit_scalar {bs : List U8} {start : Nat} {cp : U32} {next : Usize}
    (unit : UnitAt bs start cp next) : Rowl.Encoding.Scalar cp.val := prefix_scalar unit.2.2

/-- Raw-character rules inside IRIREF and STRING_LITERAL_QUOTE. The caller
    handles the closing delimiter before asking for an item. -/
def RawAllowed (iri : Bool) (cp : Nat) : Prop :=
  if iri then IriCharacter cp else ¬ EndLine cp

/-- One source character or complete escape, including the actual backslash
    in the source. Returned values are decoded scalars, not source spellings. -/
inductive QuotedItem (bs : List U8) (iri : Bool) : Nat → U32 → Usize → Prop
  | raw {start cp next} : UnitAt bs start cp next → cp ≠ 92#u32 →
      RawAllowed iri cp.val → QuotedItem bs iri start cp next
  | escaped {start next cp stop} : UnitAt bs start 92#u32 next →
      EscapeValue bs iri next.val cp stop → QuotedItem bs iri start cp stop

inductive ItemError (bs : List U8) (position : Usize) (iri : Bool) : ReadError → Prop
  | raw {cp next} : UnitAt bs position.val cp next → cp ≠ 92#u32 →
      ¬ RawAllowed iri cp.val → ItemError bs position iri ⟨.InvalidCharacter,position⟩
  | escaped {next error} : UnitAt bs position.val 92#u32 next →
      EscapeError bs position iri next.val error → ItemError bs position iri error

def ItemCorrect (bs : List U8) (position : Usize) (iri : Bool) :
    Parsed (U32 × Usize) ReadError → Prop
  | .Ok (cp,stop) => QuotedItem bs iri position.val cp stop
  | .Err error => ItemError bs position iri error

/-- This theorem connects the checked escape payload to its source backslash
    and establishes all raw-character exclusions in the actual Rust helper. -/
theorem quoted_item_total_correct (bytes : alloc.vec.Vec U8) (position : Usize)
    (cp : U32) (next : Usize) (iri : Bool) (unit : UnitAt bytes.val position.val cp next) :
    ∃ result, quoted_item bytes position cp next iri = .ok result ∧
      ItemCorrect bytes.val position iri result := by
  by_cases slash : cp = 92#u32
  · subst cp
    obtain ⟨result, executed, correct⟩ := escape_total_correct bytes position next iri
    refine ⟨result, by simp [quoted_item,executed], ?_⟩
    cases result with
    | Ok pair => obtain ⟨value,stop⟩ := pair; exact QuotedItem.escaped unit correct
    | Err error => exact ItemError.escaped unit correct
  · by_cases allowed : RawAllowed iri cp.val
    · refine ⟨.Ok (cp,next), ?_, QuotedItem.raw unit slash allowed⟩
      cases iri <;> simp_all [quoted_item,RawAllowed,iri_character_total,eol_total]
    · refine ⟨.Err ⟨.InvalidCharacter,position⟩, ?_, ItemError.raw unit slash allowed⟩
      cases iri <;> simp_all [quoted_item,RawAllowed,iri_character_total,eol_total,ntriples.error]

theorem quoted_item_progress {bs : List U8} {iri : Bool} {start : Nat}
    {cp : U32} {stop : Usize} (item : QuotedItem bs iri start cp stop) :
    Rowl.Encoding.Scalar cp.val ∧ start < stop.val ∧ stop.val ≤ bs.length := by
  cases item with
  | raw unit slash allowed => exact ⟨unit_scalar unit,unit.1,unit.2.1⟩
  | escaped unit payload =>
    obtain ⟨scalar,advanced,bounded⟩ := escape_value_progress payload
    exact ⟨scalar,by have := unit.1; omega,bounded⟩

private theorem quoted_item_actual {bytes : alloc.vec.Vec U8} {position : Usize}
    {cp value : U32} {next stop : Usize} {iri : Bool}
    (unit : UnitAt bytes.val position.val cp next)
    (item : QuotedItem bytes.val iri position.val value stop) :
    quoted_item bytes position cp next iri = .ok (.Ok (value,stop)) := by
  cases item with
  | raw other slash allowed =>
    obtain ⟨rfl,rfl⟩ := unit_unique unit other
    cases iri <;> simp_all [quoted_item,RawAllowed,iri_character_total,eol_total]
  | escaped other payload =>
    obtain ⟨rfl,rfl⟩ := unit_unique unit other
    have accepted := (escape_accepted_iff bytes position next iri value stop).mpr payload
    simp [quoted_item,accepted]

/-- For a supplied strict source unit, the helper accepts exactly the raw or
    escaped item grammar, with its exact decoded value and stopping offset. -/
theorem quoted_item_accepted_iff (bytes : alloc.vec.Vec U8) (position : Usize)
    (cp value : U32) (next stop : Usize) (iri : Bool)
    (unit : UnitAt bytes.val position.val cp next) :
    quoted_item bytes position cp next iri = .ok (.Ok (value,stop)) ↔
      QuotedItem bytes.val iri position.val value stop := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := quoted_item_total_correct bytes position cp next iri unit
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,ItemCorrect] using correct
  · exact quoted_item_actual unit

def Opening (iri : Bool) : U32 := if iri then 60#u32 else 34#u32
def Closing (iri : Bool) : U32 := if iri then 62#u32 else 34#u32
def OpeningErrorKind (iri : Bool) : ErrorKind := if iri then .ExpectedIri else .ExpectedObject

/-- Delimited body grammar. Raw characters and escaped characters are encoded
    by the independent canonical RFC 3629 production before concatenation.
    The first unescaped closing delimiter ends the token. -/
inductive QuotedBody (bs : List U8) (iri : Bool) : Usize → List U8 → Usize → Prop
  | close {start stop} : UnitAt bs start.val (Closing iri) stop →
      QuotedBody bs iri start [] stop
  | item {start cp next value finish encoded word stop} :
      UnitAt bs start.val cp next → cp ≠ Closing iri →
      QuotedItem bs iri start.val value finish →
      Rowl.Encoding.EncodeCorrect value.val (some encoded) →
      QuotedBody bs iri finish word stop →
      QuotedBody bs iri start (Rowl.Encoding.Bytes encoded ++ word) stop

/-- Exact first failure of a quoted body. A limit failure occurs at the
    original source unit, including the backslash of an escaped unit. -/
inductive BodyError (bs : List U8) (iri : Bool) (limit : Nat) :
    Nat → Usize → ReadError → Prop
  | required {before start error} : RequiredError bs start.val error →
      BodyError bs iri limit before start error
  | item {before start cp next error} : UnitAt bs start.val cp next → cp ≠ Closing iri →
      ItemError bs start iri error → BodyError bs iri limit before start error
  | limit {before start cp next value finish encoded} : UnitAt bs start.val cp next →
      cp ≠ Closing iri → QuotedItem bs iri start.val value finish →
      Rowl.Encoding.EncodeCorrect value.val (some encoded) →
      limit < before + (Rowl.Encoding.Bytes encoded).length →
      BodyError bs iri limit before start ⟨.ResourceLimit,start⟩
  | afterItem {before start cp next value finish encoded error} :
      UnitAt bs start.val cp next → cp ≠ Closing iri →
      QuotedItem bs iri start.val value finish →
      Rowl.Encoding.EncodeCorrect value.val (some encoded) →
      before + (Rowl.Encoding.Bytes encoded).length ≤ limit →
      BodyError bs iri limit (before + (Rowl.Encoding.Bytes encoded).length) finish error →
      BodyError bs iri limit before start error

def BodyCorrect (bs : List U8) (iri : Bool) (limit : Nat) (start : Usize)
    (before : List U8) : Parsed (alloc.vec.Vec U8 × Usize) ReadError → Prop
  | .Ok (output,stop) => ∃ word, QuotedBody bs iri start word stop ∧
      output.val = before ++ word ∧ output.val.length ≤ limit
  | .Err error => BodyError bs iri limit before.length start error

private theorem append_success {before after : List U8} {encoded : encoding.Encoded} {limit : Nat}
    (correct : BufferAppend before (Rowl.Encoding.Bytes encoded) limit true after) :
    before.length + (Rowl.Encoding.Bytes encoded).length ≤ limit ∧
      after = before ++ Rowl.Encoding.Bytes encoded ∧ after.length ≤ limit := by
  obtain ⟨accepted,contents,bounded⟩ := correct
  have room : before.length + (Rowl.Encoding.Bytes encoded).length ≤ limit := by
    simpa using accepted.symm
  have capacity : (Rowl.Encoding.Bytes encoded).length ≤ limit-before.length := by omega
  exact ⟨room,by simpa [List.take_of_length_le capacity] using contents,bounded⟩

private theorem quoted_loop_total (bytes : alloc.vec.Vec U8) (iri : Bool) (limit position : Usize)
    (output : alloc.vec.Vec U8) (bounded : output.val.length ≤ limit.val) :
    ∃ result, quoted_loop bytes iri limit (Closing iri) position output = .ok result ∧
      BodyCorrect bytes.val iri limit.val position output.val result := by
  obtain ⟨unit,readUnit,unitCorrect⟩ := required_total_correct bytes position
  cases unit with
  | Err error =>
    refine ⟨.Err error, ?_, BodyError.required unitCorrect⟩
    rw [quoted_loop]
    simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok pair =>
    obtain ⟨cp,next⟩ := pair
    by_cases close : cp = Closing iri
    · subst cp
      refine ⟨.Ok (output,next), ?_, [], QuotedBody.close unitCorrect, by simp, bounded⟩
      rw [quoted_loop]
      simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch]
    · obtain ⟨item,readItem,itemCorrect⟩ := quoted_item_total_correct bytes position cp next iri unitCorrect
      cases item with
      | Err error =>
        refine ⟨.Err error, ?_, BodyError.item unitCorrect close itemCorrect⟩
        rw [quoted_loop]
        simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,close,readItem,same_residual]
      | Ok pair =>
        obtain ⟨value,finish⟩ := pair
        have progress := quoted_item_progress itemCorrect
        obtain ⟨encoded,encodeUnit,encodingCorrect⟩ := Rowl.Encoding.encode_total_correct value
        cases encoded with
        | none => exact False.elim (encodingCorrect progress.1)
        | some encoded =>
          obtain ⟨accepted,after,appendUnit,appendCorrect⟩ := append_encoded_total_correct output encoded limit bounded
          cases accepted with
          | false =>
            have full : limit.val < output.val.length + (Rowl.Encoding.Bytes encoded).length := by
              have := appendCorrect.1
              simpa using this.symm
            refine ⟨.Err ⟨.ResourceLimit,position⟩, ?_,
              BodyError.limit unitCorrect close itemCorrect encodingCorrect full⟩
            rw [quoted_loop]
            simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,close,readItem,encodeUnit,
              appendUnit,ntriples.error]
          | true =>
            obtain ⟨room,contents,afterBound⟩ := append_success appendCorrect
            obtain ⟨result,tail,tailCorrect⟩ := quoted_loop_total bytes iri limit finish after afterBound
            refine ⟨result, ?_, ?_⟩
            · rw [quoted_loop]
              simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,close,readItem,encodeUnit,
                appendUnit,tail]
            · cases result with
              | Err error =>
                apply BodyError.afterItem unitCorrect close itemCorrect encodingCorrect room
                simpa [BodyCorrect,contents] using tailCorrect
              | Ok pair =>
                obtain ⟨final,stop⟩ := pair
                obtain ⟨word,body,resultBytes,resultBound⟩ := tailCorrect
                exact ⟨Rowl.Encoding.Bytes encoded ++ word,
                  QuotedBody.item unitCorrect close itemCorrect encodingCorrect body,
                  by simpa [contents,List.append_assoc] using resultBytes,resultBound⟩
termination_by bytes.val.length-position.val
decreasing_by have := progress.2.1; have := progress.2.2; omega

private theorem quoted_loop_actual {bytes : alloc.vec.Vec U8} {iri : Bool} {limit : Usize}
    {position stop : Usize} {word : List U8} (body : QuotedBody bytes.val iri position word stop) :
    ∀ output : alloc.vec.Vec U8, output.val.length + word.length ≤ limit.val →
      ∃ final, quoted_loop bytes iri limit (Closing iri) position output = .ok (.Ok (final,stop)) ∧
        final.val = output.val ++ word := by
  induction body with
  | close unit =>
    intro output fits
    refine ⟨output, ?_, by simp⟩
    rw [quoted_loop]
    simp [required_actual unit,core.result.Result.Insts.CoreOpsTry.branch]
  | @item position cp next value finish encoded word stop unit notClose item encodedCorrect tail ih =>
    intro output fits
    have beforeBound : output.val.length ≤ limit.val := by omega
    obtain ⟨accepted,after,appendUnit,appendCorrect⟩ := append_encoded_total_correct output encoded limit beforeBound
    have room : output.val.length + (Rowl.Encoding.Bytes encoded).length ≤ limit.val := by
      simp only [List.length_append] at fits
      omega
    have acceptedTrue : accepted = true := by simpa [room] using appendCorrect.1
    subst accepted
    obtain ⟨actualRoom,contents,afterBound⟩ := append_success appendCorrect
    have tailFits : after.val.length + word.length ≤ limit.val := by
      simpa [contents,List.length_append,Nat.add_assoc] using fits
    obtain ⟨final,rest,resultBytes⟩ := ih after tailFits
    refine ⟨final, ?_, by simpa [contents,List.append_assoc] using resultBytes⟩
    rw [quoted_loop]
    simp [required_actual unit,core.result.Result.Insts.CoreOpsTry.branch,notClose,
      quoted_item_actual unit item,(Rowl.Encoding.encode_some_iff value encoded).mpr encodedCorrect,
      appendUnit,rest]

def QuotedToken (bs : List U8) (start : Usize) (iri : Bool) (word : List U8) (stop : Usize) : Prop :=
  ∃ next, UnitAt bs start.val (Opening iri) next ∧ QuotedBody bs iri next word stop

inductive QuotedError (bs : List U8) (start : Usize) (iri : Bool) (limit : Nat) : ReadError → Prop
  | opening {error} : ExpectCorrect bs start.val (Opening iri) (OpeningErrorKind iri) (.Err error) →
      QuotedError bs start iri limit error
  | body {next error} : UnitAt bs start.val (Opening iri) next →
      BodyError bs iri limit 0 next error → QuotedError bs start iri limit error

def QuotedCorrect (bs : List U8) (start : Usize) (iri : Bool) (limit : Nat) :
    Parsed (alloc.vec.Vec U8 × Usize) ReadError → Prop
  | .Ok (output,stop) => QuotedToken bs start iri output.val stop ∧ output.val.length ≤ limit
  | .Err error => QuotedError bs start iri limit error

/-- Whole quoted-token recognition is total: opening/closing delimiters,
    raw Unicode, complete escapes, exact decoded bytes and first diagnostic.
    No malformed scalar can reach the encoder's failure branch. -/
theorem quoted_total_correct (bytes : alloc.vec.Vec U8) (start : Usize) (iri : Bool) (limit : Usize) :
    ∃ result, quoted bytes start iri limit = .ok result ∧
      QuotedCorrect bytes.val start iri limit.val result := by
  obtain ⟨opening,readOpening,openingCorrect⟩ := expect_total_correct bytes start (Opening iri) (OpeningErrorKind iri)
  cases opening with
  | Err error =>
    refine ⟨.Err error, ?_, QuotedError.opening openingCorrect⟩
    cases iri <;> simp only [Opening,OpeningErrorKind,Bool.false_eq_true,↓reduceIte] at readOpening <;>
      simp [quoted,readOpening,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok next =>
    obtain ⟨result,readBody,bodyCorrect⟩ := quoted_loop_total bytes iri limit next (alloc.vec.Vec.new U8) (by simp)
    refine ⟨result, ?_, ?_⟩
    · cases iri <;> simp only [Opening,Closing,OpeningErrorKind,Bool.false_eq_true,↓reduceIte] at readOpening readBody <;>
        simp [quoted,readOpening,readBody,core.result.Result.Insts.CoreOpsTry.branch]
    · cases result with
      | Err error => exact QuotedError.body openingCorrect (by simpa [BodyCorrect] using bodyCorrect)
      | Ok pair =>
        obtain ⟨output,stop⟩ := pair
        obtain ⟨word,body,contents,bounded⟩ := bodyCorrect
        have same : output.val = word := by simpa using contents
        exact ⟨⟨next,openingCorrect,by simpa [same] using body⟩,bounded⟩

/-- Every and only grammar-legal token within the caller's byte budget is
    accepted, with exact spelling after unescaping and exact source offset. -/
theorem quoted_accepted_iff (bytes : alloc.vec.Vec U8) (start stop : Usize) (iri : Bool)
    (limit : Usize) (output : alloc.vec.Vec U8) :
    quoted bytes start iri limit = .ok (.Ok (output,stop)) ↔
      QuotedToken bytes.val start iri output.val stop ∧ output.val.length ≤ limit.val := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := quoted_total_correct bytes start iri limit
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,QuotedCorrect] using correct
  · rintro ⟨⟨next,opening,body⟩,fits⟩
    have readOpening := expect_actual (kind := OpeningErrorKind iri) opening
    obtain ⟨final,readBody,contents⟩ := quoted_loop_actual body (alloc.vec.Vec.new U8) (by simpa using fits)
    have same : final = output := (alloc.vec.Vec.eq_iff final output).mpr (by simpa using contents)
    cases iri <;> simp_all [quoted,Opening,Closing,OpeningErrorKind,core.result.Result.Insts.CoreOpsTry.branch]

theorem quoted_token_progress {bs : List U8} {start stop : Usize} {iri : Bool} {word : List U8}
    (token : QuotedToken bs start iri word stop) : start.val < stop.val ∧ stop.val ≤ bs.length := by
  obtain ⟨next,opening,body⟩ := token
  have bodyBounds : next.val < stop.val ∧ stop.val ≤ bs.length := by
    clear opening
    induction body with
    | close unit => exact ⟨unit.1,unit.2.1⟩
    | item unit close item encoded tail ih =>
      have progress := quoted_item_progress item
      exact ⟨by omega,ih.2⟩
  have := opening.1
  omega

/-- RDF IRIs have a strict UTF-8 spelling denoting an absolute RFC 3987 IRI.
    This does not normalize or resolve the spelling. -/
def AbsoluteIri (spelling : List U8) : Prop :=
  ∃ word, Rowl.Regular.Utf8From spelling 0 word ∧ word ∈ Rowl.Iri.IriLanguage

inductive IriError (bs : List U8) (start : Usize) (limit : Nat) : ReadError → Prop
  | quoted {error} : QuotedError bs start true limit error → IriError bs start limit error
  | invalid {spelling stop} : QuotedToken bs start true spelling stop → spelling.length ≤ limit →
      ¬ AbsoluteIri spelling → IriError bs start limit ⟨.InvalidIri,start⟩

def IriCorrect (bs : List U8) (start : Usize) (limit : Nat) :
    Parsed (rdf.RdfIri × Usize) ReadError → Prop
  | .Ok (value,stop) => QuotedToken bs start true value.spelling.val stop ∧
      value.spelling.val.length ≤ limit ∧ AbsoluteIri value.spelling.val
  | .Err error => IriError bs start limit error

/-- Complete IRIREF parsing composes the delimited-token proof with the
    checked RFC 3987 byte recognizer; accepted spelling remains exact. -/
theorem read_iri_total_correct (bytes : alloc.vec.Vec U8) (start limit : Usize) :
    ∃ result, read_iri bytes start limit = .ok result ∧
      IriCorrect bytes.val start limit.val result := by
  obtain ⟨token,readToken,tokenCorrect⟩ := quoted_total_correct bytes start true limit
  cases token with
  | Err error =>
    refine ⟨.Err error, ?_, IriError.quoted tokenCorrect⟩
    simp [read_iri,readToken,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok pair =>
    obtain ⟨spelling,stop⟩ := pair
    by_cases valid : AbsoluteIri spelling.val
    · have recognized := (Rowl.Iri.validate_iri_accepted_iff spelling).mpr valid
      refine ⟨.Ok (⟨spelling⟩,stop), ?_, tokenCorrect.1,tokenCorrect.2,valid⟩
      simp [read_iri,readToken,core.result.Result.Insts.CoreOpsTry.branch,recognized]
    · obtain ⟨recognized,checkIri,checkCorrect⟩ := Rowl.Iri.validate_iri_total_correct spelling
      have notTrue : recognized ≠ .Matched true := by
        intro equal
        subst recognized
        exact valid ((Rowl.Iri.validate_iri_accepted_iff spelling).mp checkIri)
      refine ⟨.Err ⟨.InvalidIri,start⟩, ?_, IriError.invalid tokenCorrect.1 tokenCorrect.2 valid⟩
      cases recognized with
      | Matched accepted =>
        cases accepted with
        | true => exact False.elim (notTrue rfl)
        | false => simp [read_iri,readToken,core.result.Result.Insts.CoreOpsTry.branch,checkIri,ntriples.error]
      | MalformedUtf8 error =>
        simp [read_iri,readToken,core.result.Result.Insts.CoreOpsTry.branch,checkIri,ntriples.error]

/-- All and only well-formed IRIREF tokens with absolute decoded IRIs and
    fitting byte length are accepted, including exact token stopping offsets. -/
theorem read_iri_accepted_iff (bytes : alloc.vec.Vec U8) (start stop limit : Usize) (value : rdf.RdfIri) :
    read_iri bytes start limit = .ok (.Ok (value,stop)) ↔
      QuotedToken bytes.val start true value.spelling.val stop ∧
      value.spelling.val.length ≤ limit.val ∧ AbsoluteIri value.spelling.val := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := read_iri_total_correct bytes start limit
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,IriCorrect] using correct
  · rintro ⟨token,bounded,valid⟩
    have readToken := (quoted_accepted_iff bytes start stop true limit value.spelling).mpr ⟨token,bounded⟩
    have recognized := (Rowl.Iri.validate_iri_accepted_iff value.spelling).mpr valid
    cases value
    simp [read_iri,readToken,core.result.Result.Insts.CoreOpsTry.branch,recognized]

def SubjectToken (bs scope : List U8) (start : Usize) (limit : Nat) : rdf.Subject → Usize → Prop
  | .Iri value, stop => QuotedToken bs start true value.spelling.val stop ∧
      value.spelling.val.length ≤ limit ∧ AbsoluteIri value.spelling.val
  | .Blank node, stop => BlankToken bs scope start.val limit node stop

inductive SubjectError (bs : List U8) (start : Usize) (limit : Nat) : ReadError → Prop
  | required {error} : RequiredError bs start.val error → SubjectError bs start limit error
  | iri {next error} : UnitAt bs start.val 60#u32 next → IriError bs start limit error →
      SubjectError bs start limit error
  | blank {next error} : UnitAt bs start.val 95#u32 next → BlankError bs start.val limit error →
      SubjectError bs start limit error
  | invalid {cp next} : UnitAt bs start.val cp next → cp ≠ 60#u32 → cp ≠ 95#u32 →
      SubjectError bs start limit ⟨.ExpectedSubject,start⟩

def SubjectCorrect (bs scope : List U8) (start : Usize) (limit : Nat) :
    Parsed (rdf.Subject × Usize) ReadError → Prop
  | .Ok (value,stop) => SubjectToken bs scope start limit value stop
  | .Err error => SubjectError bs start limit error

@[local simp] private theorem marker_60_value : (60#32#uscalar : U32).val = 60 := rfl
@[local simp] private theorem marker_95_value : (95#32#uscalar : U32).val = 95 := rfl

/-- RDF subject construction is total for every source: it accepts complete
    IRIREF/blank tokens and preserves the caller's exact blank-node scope. -/
theorem subject_total_correct (bytes scope : alloc.vec.Vec U8) (start limit : Usize) :
    ∃ result, subject bytes start scope limit = .ok result ∧
      SubjectCorrect bytes.val scope.val start limit.val result := by
  obtain ⟨unit,readUnit,unitCorrect⟩ := required_total_correct bytes start
  cases unit with
  | Err error =>
    refine ⟨.Err error, ?_, SubjectError.required unitCorrect⟩
    simp [subject,readUnit,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok pair =>
    obtain ⟨cp,next⟩ := pair
    by_cases iriMarker : cp = 60#u32
    · subst cp
      obtain ⟨result,readIri,iriCorrect⟩ := read_iri_total_correct bytes start limit
      cases result with
      | Err error =>
        refine ⟨.Err error, ?_, SubjectError.iri unitCorrect iriCorrect⟩
        simp [subject,readUnit,core.result.Result.Insts.CoreOpsTry.branch,readIri,same_residual]; rfl
      | Ok pair =>
        obtain ⟨value,stop⟩ := pair
        refine ⟨.Ok (.Iri value,stop), ?_, iriCorrect⟩
        simp [subject,readUnit,core.result.Result.Insts.CoreOpsTry.branch,readIri]; rfl
    · by_cases blankMarker : cp = 95#u32
      · subst cp
        obtain ⟨result,readBlank,blankCorrect⟩ := blank_total_correct bytes scope start limit
        cases result with
        | Err error =>
          refine ⟨.Err error, ?_, SubjectError.blank unitCorrect blankCorrect⟩
          simp [subject,readUnit,core.result.Result.Insts.CoreOpsTry.branch,readBlank,same_residual]; rfl
        | Ok pair =>
          obtain ⟨value,stop⟩ := pair
          refine ⟨.Ok (.Blank value,stop), ?_, blankCorrect⟩
          simp [subject,readUnit,core.result.Result.Insts.CoreOpsTry.branch,readBlank]; rfl
      · refine ⟨.Err ⟨.ExpectedSubject,start⟩, ?_, SubjectError.invalid unitCorrect iriMarker blankMarker⟩
        simp [subject,readUnit,core.result.Result.Insts.CoreOpsTry.branch,iriMarker,blankMarker,ntriples.error,
          UScalar.ofNat,UScalar.ofNatCore]
        split <;> simp_all [UScalar.eq_equiv]

/-- Subject recognition is sound and complete against the independent token
    relations; a literal cannot occupy a subject position. -/
theorem subject_accepted_iff (bytes scope : alloc.vec.Vec U8) (start stop limit : Usize) (value : rdf.Subject) :
    subject bytes start scope limit = .ok (.Ok (value,stop)) ↔
      SubjectToken bytes.val scope.val start limit.val value stop := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := subject_total_correct bytes scope start limit
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,SubjectCorrect] using correct
  · intro valid
    cases value with
    | Iri value =>
      have readIri := (read_iri_accepted_iff bytes start stop limit value).mpr valid
      obtain ⟨⟨next,opening,body⟩,bound,absolute⟩ := valid
      have readUnit := required_actual (show UnitAt bytes.val start.val 60#u32 next by simpa [Opening] using opening)
      simp [subject,readUnit,core.result.Result.Insts.CoreOpsTry.branch,readIri]; rfl
    | Blank node =>
      have readBlank := (blank_accepted_iff bytes scope start limit node stop).mpr valid
      obtain ⟨colon,begin,first,next,opening,rest⟩ := valid
      simp [subject,required_actual opening,core.result.Result.Insts.CoreOpsTry.branch,readBlank]; rfl

def TagCharacter (letters : Bool) (cp : Nat) : Prop :=
  AsciiAlpha cp ∨ (letters = false ∧ AsciiDigit cp)

/-- Maximal ASCII letters/alphanumerics, with the first nonmatching unit left
    unconsumed. The head and subtag modes have distinct character classes. -/
inductive TagWord (bs : List U8) (letters : Bool) : Usize → Usize → Prop
  | eof {position} : position.val = bs.length → TagWord bs letters position position
  | stop {position cp next} : UnitAt bs position.val cp next → ¬ TagCharacter letters cp.val →
      TagWord bs letters position position
  | character {position cp next finish} : UnitAt bs position.val cp next → TagCharacter letters cp.val →
      TagWord bs letters next finish → TagWord bs letters position finish

inductive TagWordError (bs : List U8) (letters : Bool) : Usize → ReadError → Prop
  | invalid {position error} : MalformedError bs position.val error → TagWordError bs letters position error
  | character {position cp next error} : UnitAt bs position.val cp next → TagCharacter letters cp.val →
      TagWordError bs letters next error → TagWordError bs letters position error

def TagWordCorrect (bs : List U8) (position : Usize) (letters : Bool) : Parsed Usize ReadError → Prop
  | .Ok stop => TagWord bs letters position stop
  | .Err error => TagWordError bs letters position error

private theorem tag_word_total (bytes : alloc.vec.Vec U8) (position : Usize) (letters : Bool) :
    ∃ result, tag_word bytes position letters = .ok result ∧
      TagWordCorrect bytes.val position letters result := by
  obtain ⟨unit,readUnit,unitCorrect⟩ := at_total_correct bytes position
  cases unit with
  | Err error =>
    refine ⟨.Err error, ?_, TagWordError.invalid unitCorrect⟩
    rw [tag_word]
    simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok optional =>
    cases optional with
    | none =>
      refine ⟨.Ok position, ?_, TagWord.eof unitCorrect⟩
      rw [tag_word]
      simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch]
    | some pair =>
      obtain ⟨cp,next⟩ := pair
      by_cases allowed : TagCharacter letters cp.val
      · obtain ⟨result,readTail,tailCorrect⟩ := tag_word_total bytes next letters
        refine ⟨result, ?_, ?_⟩
        · rw [tag_word]
          cases letters with
          | false =>
            have allowed' : AsciiAlpha cp.val ∨ AsciiDigit cp.val := by simpa [TagCharacter] using allowed
            rcases allowed' with alpha | digit
            · simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,ascii_alpha_total,alpha,readTail]
            · by_cases alpha : AsciiAlpha cp.val <;>
                simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,ascii_alpha_total,
                  ascii_digit_total,alpha,digit,readTail]
          | true =>
            have alpha : AsciiAlpha cp.val := by simpa [TagCharacter] using allowed
            simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,ascii_alpha_total,alpha,readTail]
        · cases result with
          | Ok finish => exact TagWord.character unitCorrect allowed tailCorrect
          | Err error => exact TagWordError.character unitCorrect allowed tailCorrect
      · refine ⟨.Ok position, ?_, TagWord.stop unitCorrect allowed⟩
        rw [tag_word]
        cases letters <;> simp_all [readUnit,core.result.Result.Insts.CoreOpsTry.branch,
          ascii_alpha_total,ascii_digit_total,TagCharacter]
termination_by bytes.val.length-position.val
decreasing_by have := unitCorrect.1; have := unitCorrect.2.1; omega

private theorem tag_word_actual {bytes : alloc.vec.Vec U8} {position stop : Usize} {letters : Bool}
    (word : TagWord bytes.val letters position stop) : tag_word bytes position letters = .ok (.Ok stop) := by
  induction word with
  | eof endSource =>
    rw [tag_word]
    simp [eof_actual endSource,core.result.Result.Insts.CoreOpsTry.branch]
  | stop unit forbidden =>
    rw [tag_word]
    cases letters <;> simp_all [unit_actual unit,core.result.Result.Insts.CoreOpsTry.branch,
      ascii_alpha_total,ascii_digit_total,TagCharacter]
  | @character position cp next finish unit allowed tail ih =>
    rw [tag_word]
    cases letters with
    | false =>
      have allowed' : AsciiAlpha cp.val ∨ AsciiDigit cp.val := by simpa [TagCharacter] using allowed
      rcases allowed' with alpha | digit
      · simp [unit_actual unit,core.result.Result.Insts.CoreOpsTry.branch,ascii_alpha_total,alpha,ih]
      · by_cases alpha : AsciiAlpha cp.val <;>
          simp [unit_actual unit,core.result.Result.Insts.CoreOpsTry.branch,ascii_alpha_total,
            ascii_digit_total,alpha,digit,ih]
    | true =>
      have alpha : AsciiAlpha cp.val := by simpa [TagCharacter] using allowed
      simp [unit_actual unit,core.result.Result.Insts.CoreOpsTry.branch,ascii_alpha_total,alpha,ih]

theorem tag_word_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) (letters : Bool) :
    ∃ result, tag_word bytes position letters = .ok result ∧
      TagWordCorrect bytes.val position letters result := tag_word_total bytes position letters

theorem tag_word_accepted_iff (bytes : alloc.vec.Vec U8) (position stop : Usize) (letters : Bool) :
    tag_word bytes position letters = .ok (.Ok stop) ↔ TagWord bytes.val letters position stop := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := tag_word_total bytes position letters
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,TagWordCorrect] using correct
  · exact tag_word_actual

private theorem tag_word_bounds {bs : List U8} {letters : Bool} {position stop : Usize}
    (word : TagWord bs letters position stop) : position.val ≤ stop.val ∧ stop.val ≤ bs.length := by
  induction word with
  | eof endSource => omega
  | stop unit forbidden => have := unit.1; have := unit.2.1; omega
  | character unit allowed tail ih => have := unit.1; omega

/-- Maximal sequence of nonempty hyphen-prefixed alphanumeric subtags. -/
inductive TagSuffix (bs : List U8) : Usize → Usize → Prop
  | eof {position} : position.val = bs.length → TagSuffix bs position position
  | stop {position cp next} : UnitAt bs position.val cp next → cp ≠ 45#u32 → TagSuffix bs position position
  | subtag {position next middle stop} : UnitAt bs position.val 45#u32 next →
      TagWord bs false next middle → next ≠ middle → TagSuffix bs middle stop → TagSuffix bs position stop

inductive TagSuffixError (bs : List U8) (origin : Usize) : Usize → ReadError → Prop
  | invalid {position error} : MalformedError bs position.val error → TagSuffixError bs origin position error
  | word {position next error} : UnitAt bs position.val 45#u32 next → TagWordError bs false next error →
      TagSuffixError bs origin position error
  | empty {position next} : UnitAt bs position.val 45#u32 next → TagWord bs false next next →
      TagSuffixError bs origin position ⟨.InvalidLanguageTag,origin⟩
  | subtag {position next middle error} : UnitAt bs position.val 45#u32 next →
      TagWord bs false next middle → next ≠ middle → TagSuffixError bs origin middle error →
      TagSuffixError bs origin position error

def TagSuffixCorrect (bs : List U8) (position origin : Usize) : Parsed Usize ReadError → Prop
  | .Ok stop => TagSuffix bs position stop
  | .Err error => TagSuffixError bs origin position error

@[local simp] private theorem marker_45_value : (45#32#uscalar : U32).val = 45 := rfl

private theorem tag_tail_total (bytes : alloc.vec.Vec U8) (position origin : Usize) :
    ∃ result, tag_tail bytes position origin = .ok result ∧
      TagSuffixCorrect bytes.val position origin result := by
  obtain ⟨unit,readUnit,unitCorrect⟩ := at_total_correct bytes position
  cases unit with
  | Err error =>
    refine ⟨.Err error, ?_, TagSuffixError.invalid unitCorrect⟩
    rw [tag_tail]
    simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok optional =>
    cases optional with
    | none =>
      refine ⟨.Ok position, ?_, TagSuffix.eof unitCorrect⟩
      rw [tag_tail]
      simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch]
    | some pair =>
      obtain ⟨cp,next⟩ := pair
      by_cases hyphen : cp = 45#u32
      · subst cp
        obtain ⟨word,readWord,wordCorrect⟩ := tag_word_total bytes next false
        cases word with
        | Err error =>
          refine ⟨.Err error, ?_, TagSuffixError.word unitCorrect wordCorrect⟩
          rw [tag_tail]
          simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,readWord,same_residual]; rfl
        | Ok middle =>
          by_cases empty : middle = next
          · subst middle
            refine ⟨.Err ⟨.InvalidLanguageTag,origin⟩, ?_, TagSuffixError.empty unitCorrect wordCorrect⟩
            rw [tag_tail]
            simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,readWord,ntriples.error]; rfl
          · have progress := tag_word_bounds wordCorrect
            obtain ⟨result,readTail,tailCorrect⟩ := tag_tail_total bytes middle origin
            refine ⟨result, ?_, ?_⟩
            · rw [tag_tail]
              simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,readWord,empty,readTail]; rfl
            · cases result with
              | Ok stop => exact TagSuffix.subtag unitCorrect wordCorrect (Ne.symm empty) tailCorrect
              | Err error => exact TagSuffixError.subtag unitCorrect wordCorrect (Ne.symm empty) tailCorrect
      · refine ⟨.Ok position, ?_, TagSuffix.stop unitCorrect hyphen⟩
        rw [tag_tail]
        simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch]
        split <;> simp_all [UScalar.eq_equiv]
termination_by bytes.val.length-position.val
decreasing_by have := unitCorrect.1; have := progress.1; have := progress.2; omega

private theorem tag_tail_actual {bytes : alloc.vec.Vec U8} {position stop : Usize}
    (suffix : TagSuffix bytes.val position stop) (origin : Usize) :
    tag_tail bytes position origin = .ok (.Ok stop) := by
  induction suffix with
  | eof endSource =>
    rw [tag_tail]
    simp [eof_actual endSource,core.result.Result.Insts.CoreOpsTry.branch]
  | stop unit notHyphen =>
    rw [tag_tail]
    simp [unit_actual unit,core.result.Result.Insts.CoreOpsTry.branch]
    split <;> simp_all [UScalar.eq_equiv]
  | subtag unit word nonempty tail ih =>
    rw [tag_tail]
    have different := Ne.symm nonempty
    simp [unit_actual unit,core.result.Result.Insts.CoreOpsTry.branch,tag_word_actual word,different,ih]; rfl

theorem tag_tail_total_correct (bytes : alloc.vec.Vec U8) (position origin : Usize) :
    ∃ result, tag_tail bytes position origin = .ok result ∧
      TagSuffixCorrect bytes.val position origin result := tag_tail_total bytes position origin

theorem tag_tail_accepted_iff (bytes : alloc.vec.Vec U8) (position stop origin : Usize) :
    tag_tail bytes position origin = .ok (.Ok stop) ↔ TagSuffix bytes.val position stop := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := tag_tail_total bytes position origin
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,TagSuffixCorrect] using correct
  · exact fun suffix => tag_tail_actual suffix origin

private theorem tag_suffix_bounds {bs : List U8} {position stop : Usize}
    (suffix : TagSuffix bs position stop) : position.val ≤ stop.val ∧ stop.val ≤ bs.length := by
  induction suffix with
  | eof endSource => omega
  | stop unit notHyphen => have := unit.1; have := unit.2.1; omega
  | subtag unit word nonempty tail ih =>
    have bounds := tag_word_bounds word
    have := unit.1
    omega

/-- RFC 5646 ABNF well-formedness; registry validity is a separate notion. -/
def LanguageTag (bs : List U8) : Prop :=
  ∃ word, Rowl.Regular.Utf8From bs 0 word ∧ word ∈ Rowl.LangTag.WellFormedLanguage

def TagToken (bs : List U8) (start : Usize) (limit : Nat) (value : alloc.vec.Vec U8) (stop : Usize) : Prop :=
  ∃ begin head, UnitAt bs start.val 64#u32 begin ∧ TagWord bs true begin head ∧ begin ≠ head ∧
    TagSuffix bs head stop ∧ CopyCorrect bs begin.val stop.val limit (.Ok value) ∧ LanguageTag value.val

inductive TagError (bs : List U8) (start : Usize) (limit : Nat) : ReadError → Prop
  | opening {error} : ExpectCorrect bs start.val 64#u32 .InvalidLanguageTag (.Err error) → TagError bs start limit error
  | head {begin error} : UnitAt bs start.val 64#u32 begin → TagWordError bs true begin error → TagError bs start limit error
  | empty {begin} : UnitAt bs start.val 64#u32 begin → TagWord bs true begin begin →
      TagError bs start limit ⟨.InvalidLanguageTag,start⟩
  | suffix {begin head error} : UnitAt bs start.val 64#u32 begin → TagWord bs true begin head → begin ≠ head →
      TagSuffixError bs start head error → TagError bs start limit error
  | budget {begin head stop error} : UnitAt bs start.val 64#u32 begin → TagWord bs true begin head → begin ≠ head →
      TagSuffix bs head stop → CopyCorrect bs begin.val stop.val limit (.Err error) → TagError bs start limit error
  | grammar {begin head stop value} : UnitAt bs start.val 64#u32 begin → TagWord bs true begin head → begin ≠ head →
      TagSuffix bs head stop → CopyCorrect bs begin.val stop.val limit (.Ok value) → ¬ LanguageTag value.val →
      TagError bs start limit ⟨.InvalidLanguageTag,start⟩

def TagCorrect (bs : List U8) (start : Usize) (limit : Nat) :
    Parsed (alloc.vec.Vec U8 × Usize) ReadError → Prop
  | .Ok (value,stop) => TagToken bs start limit value stop
  | .Err error => TagError bs start limit error

/-- Full LANGTAG recognition composes maximal scanning, exact bounded span
    copying and the independent checked RFC 5646 grammar. Original case is
    preserved, and each error identifies its actual source stage. -/
theorem tag_total_correct (bytes : alloc.vec.Vec U8) (start limit : Usize) :
    ∃ result, tag bytes start limit = .ok result ∧ TagCorrect bytes.val start limit.val result := by
  obtain ⟨opening,readOpening,openingCorrect⟩ := expect_total_correct bytes start 64#u32 .InvalidLanguageTag
  cases opening with
  | Err error =>
    refine ⟨.Err error, ?_, TagError.opening openingCorrect⟩
    simp [tag,readOpening,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok begin =>
    obtain ⟨head,readHead,headCorrect⟩ := tag_word_total bytes begin true
    cases head with
    | Err error =>
      refine ⟨.Err error, ?_, TagError.head openingCorrect headCorrect⟩
      simp [tag,readOpening,readHead,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
    | Ok head =>
      by_cases empty : begin = head
      · subst head
        refine ⟨.Err ⟨.InvalidLanguageTag,start⟩, ?_, TagError.empty openingCorrect headCorrect⟩
        simp [tag,readOpening,readHead,core.result.Result.Insts.CoreOpsTry.branch,ntriples.error]
      · obtain ⟨tail,readTail,tailCorrect⟩ := tag_tail_total bytes head start
        cases tail with
        | Err error =>
          refine ⟨.Err error, ?_, TagError.suffix openingCorrect headCorrect empty tailCorrect⟩
          simp [tag,readOpening,readHead,empty,readTail,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
        | Ok stop =>
          have headBounds := tag_word_bounds headCorrect
          have tailBounds := tag_suffix_bounds tailCorrect
          have range : begin.val ≤ stop.val ∧ stop.val ≤ bytes.val.length := by omega
          obtain ⟨copied,readCopy,copyCorrect⟩ := copy_term_total_correct bytes begin stop limit range
          cases copied with
          | Err error =>
            refine ⟨.Err error, ?_, TagError.budget openingCorrect headCorrect empty tailCorrect copyCorrect⟩
            simp [tag,readOpening,readHead,empty,readTail,readCopy,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
          | Ok value =>
            obtain ⟨accepted,checkTag⟩ := Rowl.LangTag.well_formed_total_correct value
            cases accepted with
            | true =>
              have valid : LanguageTag value.val := (Rowl.LangTag.well_formed_accepted_iff value).mp checkTag
              refine ⟨.Ok (value,stop), ?_, begin,head,openingCorrect,headCorrect,empty,tailCorrect,copyCorrect,valid⟩
              simp [tag,readOpening,readHead,empty,readTail,readCopy,core.result.Result.Insts.CoreOpsTry.branch,checkTag]
            | false =>
              have invalid : ¬ LanguageTag value.val := by
                intro valid
                have shouldAccept := (Rowl.LangTag.well_formed_accepted_iff value).mpr valid
                have equal := Result.ok_injective (checkTag.symm.trans shouldAccept)
                contradiction
              refine ⟨.Err ⟨.InvalidLanguageTag,start⟩, ?_,
                TagError.grammar openingCorrect headCorrect empty tailCorrect copyCorrect invalid⟩
              simp [tag,readOpening,readHead,empty,readTail,readCopy,core.result.Result.Insts.CoreOpsTry.branch,
                checkTag,ntriples.error]

private theorem copy_term_actual {bytes : alloc.vec.Vec U8} {start stop limit : Usize} {value : alloc.vec.Vec U8}
    (range : start.val ≤ stop.val ∧ stop.val ≤ bytes.val.length)
    (valid : CopyCorrect bytes.val start.val stop.val limit.val (.Ok value)) :
    copy_term bytes start stop limit = .ok (.Ok value) := by
  obtain ⟨result,executed,correct⟩ := copy_term_total_correct bytes start stop limit range
  cases result with
  | Err error => exact False.elim (by have := valid.1; have := correct.1; omega)
  | Ok other =>
    have equal : other = value := (alloc.vec.Vec.eq_iff other value).mpr (correct.2.trans valid.2.symm)
    simpa [equal] using executed

/-- Exactly the independent maximal LANGTAG spelling and RFC well-formedness
    relation is accepted, within the caller's byte budget. -/
theorem tag_accepted_iff (bytes : alloc.vec.Vec U8) (start stop limit : Usize) (value : alloc.vec.Vec U8) :
    tag bytes start limit = .ok (.Ok (value,stop)) ↔ TagToken bytes.val start limit.val value stop := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := tag_total_correct bytes start limit
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,TagCorrect] using correct
  · rintro ⟨begin,head,opening,headWord,nonempty,suffix,contents,wellFormed⟩
    have headBounds := tag_word_bounds headWord
    have tailBounds := tag_suffix_bounds suffix
    have range : begin.val ≤ stop.val ∧ stop.val ≤ bytes.val.length := by omega
    have readOpening := expect_actual (kind := .InvalidLanguageTag) opening
    have readHead := tag_word_actual headWord
    have readTail := tag_tail_actual suffix start
    have readCopy := copy_term_actual range contents
    have checkTag := (Rowl.LangTag.well_formed_accepted_iff value).mpr wellFormed
    simp [tag,readOpening,readHead,nonempty,readTail,readCopy,core.result.Result.Insts.CoreOpsTry.branch,checkTag]

theorem tag_token_progress {bs : List U8} {start stop : Usize} {limit : Nat} {value : alloc.vec.Vec U8}
    (token : TagToken bs start limit value stop) : start.val < stop.val ∧ stop.val ≤ bs.length := by
  obtain ⟨begin,head,opening,headWord,nonempty,suffix,contents,wellFormed⟩ := token
  have headBounds := tag_word_bounds headWord
  have tailBounds := tag_suffix_bounds suffix
  have := opening.1
  omega

private theorem copy_slice_loop_total (bytes : Slice U8) (output : alloc.vec.Vec U8) (position : Usize)
    (prefixBound : output.val.length ≤ position.val) :
    ∃ after, copy_loop bytes output position = .ok after ∧ after.val = output.val ++ bytes.val.drop position.val := by
  rw [copy_loop]
  by_cases more : position.val < bytes.val.length
  · have element : bytes.index_usize position = .ok bytes.val[position.val] := by
      simp [Slice.index_usize,List.getElem?_eq_getElem more]
    have size := bytes.property
    have outputBound : output.val.length < Usize.max := by omega
    obtain ⟨appended,pushByte,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec output bytes.val[position.val] outputBound)
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := position) (y := 1#usize) (by scalar_tac))
    have advanced : next.val = position.val+1 := by simpa using nextValue
    have afterBound : appended.val.length ≤ next.val := by simp [contents,advanced]; omega
    obtain ⟨after,tail,copied⟩ := copy_slice_loop_total bytes appended next afterBound
    refine ⟨after,by simp [more,element,pushByte,advance,tail], ?_⟩
    rw [copied,contents,advanced,List.drop_eq_getElem_cons more]
    simp only [List.append_assoc,List.singleton_append]
  · have empty : bytes.val.drop position.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    exact ⟨output,by simp [more],by simp [empty]⟩
termination_by bytes.val.length-position.val
decreasing_by omega

@[local step] private theorem copy_slice_spec (bytes : Slice U8) :
    ntriples.copy bytes ⦃ output => output.val = bytes.val ⦄ := by
  obtain ⟨output,executed,correct⟩ := copy_slice_loop_total bytes (alloc.vec.Vec.new U8) 0#usize (by simp)
  simp [ntriples.copy,executed,correct]

private theorem same_literal_loop_total (key : alloc.vec.Vec U8) (pattern : Slice U8)
    (equalLength : key.val.length = pattern.val.length) (index : Usize) :
    same_literal_bytes_loop key pattern index = .ok (decide (key.val.drop index.val = pattern.val.drop index.val)) := by
  rw [same_literal_bytes_loop]
  by_cases inside : index.val < key.val.length
  · have patternInside : index.val < pattern.val.length := by omega
    have keyByte : key.index_usize index = .ok key.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have patternByte : pattern.index_usize index = .ok pattern.val[index.val] := by
      simp [Slice.index_usize,List.getElem?_eq_getElem patternInside]
    by_cases heads : key.val[index.val] = pattern.val[index.val]
    · have size := key.property
      obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have advanced : next.val = index.val+1 := by simpa using nextValue
      have tail := same_literal_loop_total key pattern equalLength next
      simp [inside,alloc.vec.Vec.index_slice_index,keyByte,patternByte,heads,advance,tail]
      rw [List.drop_eq_getElem_cons inside,List.drop_eq_getElem_cons patternInside]
      simp only [List.cons.injEq,heads,true_and,advanced]
    · have differentValues : key.val[index.val].val ≠ pattern.val[index.val].val :=
        fun equal => heads (UScalar.eq_of_val_eq equal)
      simp [inside,alloc.vec.Vec.index_slice_index,keyByte,patternByte,heads,differentValues]
      rw [List.drop_eq_getElem_cons inside,List.drop_eq_getElem_cons patternInside]
      simp only [List.cons.injEq,heads,false_and,not_false_eq_true]
  · have keyEmpty : key.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have patternEmpty : pattern.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,keyEmpty,patternEmpty]
termination_by key.val.length-index.val
decreasing_by omega

private theorem same_literal_total (key : alloc.vec.Vec U8) (pattern : Slice U8) :
    same_literal_bytes key pattern = .ok (decide (key.val = pattern.val)) := by
  rw [same_literal_bytes]
  by_cases equalLength : key.val.length = pattern.val.length
  · have tail := same_literal_loop_total key pattern equalLength 0#usize
    simpa [equalLength] using tail
  · have different : key.val ≠ pattern.val := fun equal => equalLength (congrArg List.length equal)
    simp [equalLength,different]

/-- Exact RDF built-in literal kind spellings, without normalization. -/
def XsdStringBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,49#u8,47#u8,88#u8,77#u8,76#u8,83#u8,99#u8,104#u8,101#u8,109#u8,97#u8,35#u8,115#u8,116#u8,114#u8,105#u8,110#u8,103#u8]
def LangStringBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,49#u8,57#u8,57#u8,57#u8,47#u8,48#u8,50#u8,47#u8,50#u8,50#u8,45#u8,114#u8,100#u8,102#u8,45#u8,115#u8,121#u8,110#u8,116#u8,97#u8,120#u8,45#u8,110#u8,115#u8,35#u8,108#u8,97#u8,110#u8,103#u8,83#u8,116#u8,114#u8,105#u8,110#u8,103#u8]

/-- A simple literal leaves a non-suffix unit or EOF unconsumed. -/
inductive NoKindSuffix (bs : List U8) (position : Usize) : Prop
  | eof : position.val = bs.length → NoKindSuffix bs position
  | other {cp next} : UnitAt bs position.val cp next → cp ≠ 64#u32 → cp ≠ 94#u32 → NoKindSuffix bs position

inductive KindToken (bs : List U8) (position : Usize) (limit : Nat) : rdf.LiteralKind → Usize → Prop
  | simple {datatype} : NoKindSuffix bs position → datatype.spelling.val = XsdStringBytes →
      KindToken bs position limit (.Datatype datatype) position
  | language {next value stop} : UnitAt bs position.val 64#u32 next → TagToken bs position limit value stop →
      KindToken bs position limit (.Language value) stop
  | datatype {next after before value stop} : UnitAt bs position.val 94#u32 next → UnitAt bs next.val 94#u32 after →
      TriviaRuns bs false after.val before.val → IriCorrect bs before limit (.Ok (value,stop)) →
      value.spelling.val ≠ LangStringBytes → KindToken bs position limit (.Datatype value) stop

inductive KindError (bs : List U8) (position : Usize) (limit : Nat) : ReadError → Prop
  | invalid {error} : MalformedError bs position.val error → KindError bs position limit error
  | language {next error} : UnitAt bs position.val 64#u32 next → TagError bs position limit error →
      KindError bs position limit error
  | caret {next error} : UnitAt bs position.val 94#u32 next → ExpectCorrect bs next.val 94#u32 .InvalidLiteralKind (.Err error) →
      KindError bs position limit error
  | trivia {next after error} : UnitAt bs position.val 94#u32 next → UnitAt bs next.val 94#u32 after →
      TriviaFails bs false after.val error → KindError bs position limit error
  | iri {next after before error} : UnitAt bs position.val 94#u32 next → UnitAt bs next.val 94#u32 after →
      TriviaRuns bs false after.val before.val → IriError bs before limit error → KindError bs position limit error
  | langString {next after before value stop} : UnitAt bs position.val 94#u32 next → UnitAt bs next.val 94#u32 after →
      TriviaRuns bs false after.val before.val → IriCorrect bs before limit (.Ok (value,stop)) →
      value.spelling.val = LangStringBytes → KindError bs position limit ⟨.InvalidLiteralKind,position⟩

def KindCorrect (bs : List U8) (position : Usize) (limit : Nat) : Parsed (rdf.LiteralKind × Usize) ReadError → Prop
  | .Ok (kind,stop) => KindToken bs position limit kind stop
  | .Err error => KindError bs position limit error

@[local simp] private theorem marker_64_value : (64#32#uscalar : U32).val = 64 := rfl
@[local simp] private theorem marker_94_value : (94#32#uscalar : U32).val = 94 := rfl

private theorem literal_kind_simple (bytes : alloc.vec.Vec U8) (position limit : Usize)
    (simple : NoKindSuffix bytes.val position) :
    ∃ datatype, literal_kind bytes position limit = .ok (.Ok (.Datatype datatype,position)) ∧
      datatype.spelling.val = XsdStringBytes := by
  suffices total : literal_kind bytes position limit ⦃ result => ∃ datatype,
      result = .Ok (.Datatype datatype,position) ∧ datatype.spelling.val = XsdStringBytes ⦄ by
    obtain ⟨result,executed,datatype,equal,spelling⟩ := WP.spec_imp_exists total
    subst result
    exact ⟨datatype,executed,spelling⟩
  cases simple with
  | eof ended =>
    simp [literal_kind,eof_actual ended,core.result.Result.Insts.CoreOpsTry.branch]
    step as ⟨slice,source⟩
    step as ⟨copied,contents⟩
    refine ⟨({spelling := copied} : rdf.RdfIri),rfl,?_⟩
    simpa [source,XsdStringBytes,Array.to_slice,Array.make] using contents
  | other unit notLanguage notCaret =>
    simp [literal_kind,unit_actual unit,core.result.Result.Insts.CoreOpsTry.branch]
    split
    · simp_all [UScalar.eq_equiv]
    · simp_all [UScalar.eq_equiv]
    · step as ⟨slice,source⟩
      step as ⟨copied,contents⟩
      refine ⟨({spelling := copied} : rdf.RdfIri),rfl,?_⟩
      simpa [source,XsdStringBytes,Array.to_slice,Array.make] using contents

/-- Literal suffix recognition is total, with only its grammar/UTF-8/budget
    diagnostics. No suffix creates xsd:string; a typed rdf:langString is
    rejected because that RDF kind requires a language tag. -/
theorem literal_kind_total_correct (bytes : alloc.vec.Vec U8) (position limit : Usize) :
    ∃ result, literal_kind bytes position limit = .ok result ∧ KindCorrect bytes.val position limit.val result := by
  obtain ⟨unit,readUnit,unitCorrect⟩ := at_total_correct bytes position
  cases unit with
  | Err error =>
    refine ⟨.Err error, ?_, KindError.invalid unitCorrect⟩
    simp [literal_kind,readUnit,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok optional =>
    cases optional with
    | none =>
      have simple := NoKindSuffix.eof unitCorrect
      obtain ⟨datatype,readKind,spelling⟩ := literal_kind_simple bytes position limit simple
      exact ⟨.Ok (.Datatype datatype,position),readKind,KindToken.simple simple spelling⟩
    | some pair =>
      obtain ⟨cp,next⟩ := pair
      by_cases language : cp = 64#u32
      · subst cp
        obtain ⟨result,readTag,tagCorrect⟩ := tag_total_correct bytes position limit
        cases result with
        | Err error =>
          refine ⟨.Err error, ?_, KindError.language unitCorrect tagCorrect⟩
          simp [literal_kind,readUnit,readTag,core.result.Result.Insts.CoreOpsTry.branch,same_residual]; rfl
        | Ok pair =>
          obtain ⟨value,stop⟩ := pair
          refine ⟨.Ok (.Language value,stop), ?_, KindToken.language unitCorrect tagCorrect⟩
          simp [literal_kind,readUnit,readTag,core.result.Result.Insts.CoreOpsTry.branch]; rfl
      · by_cases caret : cp = 94#u32
        · subst cp
          obtain ⟨after,readCaret,caretCorrect⟩ := expect_total_correct bytes next 94#u32 .InvalidLiteralKind
          cases after with
          | Err error =>
            refine ⟨.Err error, ?_, KindError.caret unitCorrect caretCorrect⟩
            simp [literal_kind,readUnit,readCaret,core.result.Result.Insts.CoreOpsTry.branch,same_residual]; rfl
          | Ok after =>
            obtain ⟨before,readTrivia,triviaCorrect⟩ := skip_total_correct bytes after false
            cases before with
            | Err error =>
              refine ⟨.Err error, ?_, KindError.trivia unitCorrect caretCorrect triviaCorrect⟩
              simp [literal_kind,readUnit,readCaret,readTrivia,core.result.Result.Insts.CoreOpsTry.branch,same_residual]; rfl
            | Ok before =>
              obtain ⟨datatype,readIri,iriCorrect⟩ := read_iri_total_correct bytes before limit
              cases datatype with
              | Err error =>
                refine ⟨.Err error, ?_, KindError.iri unitCorrect caretCorrect triviaCorrect iriCorrect⟩
                simp [literal_kind,readUnit,readCaret,readTrivia,readIri,core.result.Result.Insts.CoreOpsTry.branch,same_residual]; rfl
              | Ok pair =>
                obtain ⟨value,stop⟩ := pair
                by_cases langString : value.spelling.val = LangStringBytes
                · refine ⟨.Err ⟨.InvalidLiteralKind,position⟩, ?_,
                    KindError.langString unitCorrect caretCorrect triviaCorrect iriCorrect langString⟩
                  simp [literal_kind,readUnit,readCaret,readTrivia,readIri,core.result.Result.Insts.CoreOpsTry.branch]
                  have hLang := langString
                  simp only [LangStringBytes] at hLang
                  simp [same_literal_total,Array.to_slice,Array.make,lift,hLang,ntriples.error]
                  rfl
                · refine ⟨.Ok (.Datatype value,stop), ?_,
                    KindToken.datatype unitCorrect caretCorrect triviaCorrect iriCorrect langString⟩
                  simp [literal_kind,readUnit,readCaret,readTrivia,readIri,core.result.Result.Insts.CoreOpsTry.branch]
                  have hLang := langString
                  simp only [LangStringBytes] at hLang
                  simp [same_literal_total,Array.to_slice,Array.make,lift,hLang]
                  rfl
        · have simple := NoKindSuffix.other unitCorrect language caret
          obtain ⟨datatype,readKind,spelling⟩ := literal_kind_simple bytes position limit simple
          exact ⟨.Ok (.Datatype datatype,position),readKind,KindToken.simple simple spelling⟩

private theorem kind_token_actual {bytes : alloc.vec.Vec U8} {position stop limit : Usize} {kind : rdf.LiteralKind}
    (token : KindToken bytes.val position limit.val kind stop) :
    literal_kind bytes position limit = .ok (.Ok (kind,stop)) := by
  cases token with
  | @simple datatype noSuffix spelling =>
    obtain ⟨actual,executed,actualSpelling⟩ := literal_kind_simple bytes position limit noSuffix
    have equal : actual = datatype := by
      cases actual
      cases datatype
      congr 1
      apply (alloc.vec.Vec.eq_iff _ _).mpr
      exact actualSpelling.trans spelling.symm
    simpa [equal] using executed
  | @language next value stop unit tagToken =>
    have accepted := (tag_accepted_iff bytes position stop limit value).mpr tagToken
    simp [literal_kind,unit_actual unit,accepted,core.result.Result.Insts.CoreOpsTry.branch]; rfl
  | @datatype next after before value stop unit caret gap iriToken forbidden =>
    have caretRead := expect_actual (kind := .InvalidLiteralKind) caret
    have gapRead := trivia_actual gap after before rfl rfl
    have iriRead := (read_iri_accepted_iff bytes before stop limit value).mpr iriToken
    simp [literal_kind,unit_actual unit,caretRead,gapRead,iriRead,core.result.Result.Insts.CoreOpsTry.branch]
    have hForbidden := forbidden
    simp only [LangStringBytes] at hForbidden
    simp [same_literal_total,Array.to_slice,Array.make,lift,hForbidden]
    rfl

theorem literal_kind_accepted_iff (bytes : alloc.vec.Vec U8) (position stop limit : Usize) (kind : rdf.LiteralKind) :
    literal_kind bytes position limit = .ok (.Ok (kind,stop)) ↔ KindToken bytes.val position limit.val kind stop := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := literal_kind_total_correct bytes position limit
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,KindCorrect] using correct
  · exact kind_token_actual

def LiteralToken (bs : List U8) (start : Usize) (limit : Nat) (value : rdf.RdfLiteral) (stop : Usize) : Prop :=
  ∃ ending position, QuotedToken bs start false value.lexical.val ending ∧ value.lexical.val.length ≤ limit ∧
    TriviaRuns bs false ending.val position.val ∧ KindToken bs position limit value.kind stop

inductive LiteralError (bs : List U8) (start : Usize) (limit : Nat) : ReadError → Prop
  | quoted {error} : QuotedError bs start false limit error → LiteralError bs start limit error
  | trivia {lexical ending error} : QuotedToken bs start false lexical ending → lexical.length ≤ limit →
      TriviaFails bs false ending.val error → LiteralError bs start limit error
  | kind {lexical ending position error} : QuotedToken bs start false lexical ending → lexical.length ≤ limit →
      TriviaRuns bs false ending.val position.val → KindError bs position limit error → LiteralError bs start limit error

def LiteralCorrect (bs : List U8) (start : Usize) (limit : Nat) : Parsed (rdf.RdfLiteral × Usize) ReadError → Prop
  | .Ok (value,stop) => LiteralToken bs start limit value stop
  | .Err error => LiteralError bs start limit error

/-- Full byte-to-literal construction, including exact decoded lexical text,
    original language case, explicit/implicit datatype and first diagnostics.
    Datatype lexical membership is intentionally not an RDF parsing condition. -/
theorem literal_total_correct (bytes : alloc.vec.Vec U8) (start limit : Usize) :
    ∃ result, literal bytes start limit = .ok result ∧ LiteralCorrect bytes.val start limit.val result := by
  obtain ⟨quoted,readQuoted,quotedCorrect⟩ := quoted_total_correct bytes start false limit
  cases quoted with
  | Err error =>
    refine ⟨.Err error, ?_, LiteralError.quoted quotedCorrect⟩
    simp [literal,readQuoted,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok pair =>
    obtain ⟨lexical,ending⟩ := pair
    obtain ⟨trivia,readTrivia,triviaCorrect⟩ := skip_total_correct bytes ending false
    cases trivia with
    | Err error =>
      refine ⟨.Err error, ?_, LiteralError.trivia quotedCorrect.1 quotedCorrect.2 triviaCorrect⟩
      simp [literal,readQuoted,readTrivia,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
    | Ok position =>
      obtain ⟨kind,readKind,kindCorrect⟩ := literal_kind_total_correct bytes position limit
      cases kind with
      | Err error =>
        refine ⟨.Err error, ?_, LiteralError.kind quotedCorrect.1 quotedCorrect.2 triviaCorrect kindCorrect⟩
        simp [literal,readQuoted,readTrivia,readKind,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
      | Ok pair =>
        obtain ⟨kind,stop⟩ := pair
        refine ⟨.Ok (⟨lexical,kind⟩,stop), ?_,ending,position,quotedCorrect.1,quotedCorrect.2,triviaCorrect,kindCorrect⟩
        simp [literal,readQuoted,readTrivia,readKind,core.result.Result.Insts.CoreOpsTry.branch]

theorem literal_accepted_iff (bytes : alloc.vec.Vec U8) (start stop limit : Usize) (value : rdf.RdfLiteral) :
    literal bytes start limit = .ok (.Ok (value,stop)) ↔ LiteralToken bytes.val start limit.val value stop := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := literal_total_correct bytes start limit
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,LiteralCorrect] using correct
  · rintro ⟨ending,position,quoted,bounded,gap,kind⟩
    have readQuoted := (quoted_accepted_iff bytes start ending false limit value.lexical).mpr ⟨quoted,bounded⟩
    have readTrivia := trivia_actual gap ending position rfl rfl
    have readKind := kind_token_actual kind
    cases value
    simp [literal,readQuoted,readTrivia,readKind,core.result.Result.Insts.CoreOpsTry.branch]

private theorem kind_token_bounds {bs : List U8} {position stop : Usize} {limit : Nat} {kind : rdf.LiteralKind}
    (token : KindToken bs position limit kind stop) : position.val ≤ stop.val ∧ stop.val ≤ bs.length := by
  cases token with
  | simple noSuffix spelling =>
    cases noSuffix with
    | eof ended => omega
    | other unit notLanguage notCaret => have := unit.1; have := unit.2.1; omega
  | language unit tagToken =>
    have bounds := tag_token_progress tagToken
    omega
  | datatype unit caret gap iriToken forbidden =>
    have gapBounds := trivia_bounds gap
    have iriBounds := quoted_token_progress iriToken.1
    have := unit.1
    have := caret.1
    omega

theorem literal_token_progress {bs : List U8} {start stop : Usize} {limit : Nat} {value : rdf.RdfLiteral}
    (token : LiteralToken bs start limit value stop) : start.val < stop.val ∧ stop.val ≤ bs.length := by
  obtain ⟨ending,position,quoted,bounded,gap,kind⟩ := token
  have quoteBounds := quoted_token_progress quoted
  have gapBounds := trivia_bounds gap
  have kindBounds := kind_token_bounds kind
  omega

def ObjectToken (bs scope : List U8) (start : Usize) (limit : Nat) : rdf.Object → Usize → Prop
  | .Iri value, stop => QuotedToken bs start true value.spelling.val stop ∧
      value.spelling.val.length ≤ limit ∧ AbsoluteIri value.spelling.val
  | .Blank node, stop => BlankToken bs scope start.val limit node stop
  | .Literal value, stop => LiteralToken bs start limit value stop

inductive ObjectError (bs : List U8) (start : Usize) (limit : Nat) : ReadError → Prop
  | required {error} : RequiredError bs start.val error → ObjectError bs start limit error
  | iri {next error} : UnitAt bs start.val 60#u32 next → IriError bs start limit error → ObjectError bs start limit error
  | blank {next error} : UnitAt bs start.val 95#u32 next → BlankError bs start.val limit error → ObjectError bs start limit error
  | literal {next error} : UnitAt bs start.val 34#u32 next → LiteralError bs start limit error → ObjectError bs start limit error
  | invalid {cp next} : UnitAt bs start.val cp next → cp ≠ 60#u32 → cp ≠ 95#u32 → cp ≠ 34#u32 →
      ObjectError bs start limit ⟨.ExpectedObject,start⟩

def ObjectCorrect (bs scope : List U8) (start : Usize) (limit : Nat) : Parsed (rdf.Object × Usize) ReadError → Prop
  | .Ok (value,stop) => ObjectToken bs scope start limit value stop
  | .Err error => ObjectError bs start limit error

theorem object_total_correct (bytes scope : alloc.vec.Vec U8) (start limit : Usize) :
    ∃ result, object bytes start scope limit = .ok result ∧ ObjectCorrect bytes.val scope.val start limit.val result := by
  obtain ⟨unit,readUnit,unitCorrect⟩ := required_total_correct bytes start
  cases unit with
  | Err error =>
    refine ⟨.Err error, ?_, ObjectError.required unitCorrect⟩
    simp [object,readUnit,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok pair =>
    obtain ⟨cp,next⟩ := pair
    by_cases iriMarker : cp = 60#u32
    · subst cp
      obtain ⟨result,readIri,iriCorrect⟩ := read_iri_total_correct bytes start limit
      cases result with
      | Err error =>
        refine ⟨.Err error, ?_, ObjectError.iri unitCorrect iriCorrect⟩
        simp [object,readUnit,core.result.Result.Insts.CoreOpsTry.branch,readIri,same_residual]; rfl
      | Ok pair =>
        obtain ⟨value,stop⟩ := pair
        refine ⟨.Ok (.Iri value,stop), ?_, iriCorrect⟩
        simp [object,readUnit,core.result.Result.Insts.CoreOpsTry.branch,readIri]; rfl
    · by_cases blankMarker : cp = 95#u32
      · subst cp
        obtain ⟨result,readBlank,blankCorrect⟩ := blank_total_correct bytes scope start limit
        cases result with
        | Err error =>
          refine ⟨.Err error, ?_, ObjectError.blank unitCorrect blankCorrect⟩
          simp [object,readUnit,core.result.Result.Insts.CoreOpsTry.branch,readBlank,same_residual]; rfl
        | Ok pair =>
          obtain ⟨value,stop⟩ := pair
          refine ⟨.Ok (.Blank value,stop), ?_, blankCorrect⟩
          simp [object,readUnit,core.result.Result.Insts.CoreOpsTry.branch,readBlank]; rfl
      · by_cases literalMarker : cp = 34#u32
        · subst cp
          obtain ⟨result,readLiteral,literalCorrect⟩ := literal_total_correct bytes start limit
          cases result with
          | Err error =>
            refine ⟨.Err error, ?_, ObjectError.literal unitCorrect literalCorrect⟩
            simp [object,readUnit,core.result.Result.Insts.CoreOpsTry.branch,readLiteral,same_residual]; rfl
          | Ok pair =>
            obtain ⟨value,stop⟩ := pair
            refine ⟨.Ok (.Literal value,stop), ?_, literalCorrect⟩
            simp [object,readUnit,core.result.Result.Insts.CoreOpsTry.branch,readLiteral]; rfl
        · refine ⟨.Err ⟨.ExpectedObject,start⟩, ?_,ObjectError.invalid unitCorrect iriMarker blankMarker literalMarker⟩
          simp [object,readUnit,core.result.Result.Insts.CoreOpsTry.branch,ntriples.error]
          split <;> simp_all [UScalar.eq_equiv]

theorem object_accepted_iff (bytes scope : alloc.vec.Vec U8) (start stop limit : Usize) (value : rdf.Object) :
    object bytes start scope limit = .ok (.Ok (value,stop)) ↔ ObjectToken bytes.val scope.val start limit.val value stop := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := object_total_correct bytes scope start limit
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,ObjectCorrect] using correct
  · intro token
    cases value with
    | Iri value =>
      have readIri := (read_iri_accepted_iff bytes start stop limit value).mpr token
      obtain ⟨⟨next,opening,body⟩,bounded,absolute⟩ := token
      have readUnit := required_actual (show UnitAt bytes.val start.val 60#u32 next by simpa [Opening] using opening)
      simp [object,readUnit,core.result.Result.Insts.CoreOpsTry.branch,readIri]; rfl
    | Blank node =>
      have readBlank := (blank_accepted_iff bytes scope start limit node stop).mpr token
      obtain ⟨colon,begin,first,next,opening,rest⟩ := token
      simp [object,required_actual opening,core.result.Result.Insts.CoreOpsTry.branch,readBlank]; rfl
    | Literal value =>
      have readLiteral := (literal_accepted_iff bytes start stop limit value).mpr token
      obtain ⟨ending,position,⟨next,opening,body⟩,bounded,gap,kind⟩ := token
      have readUnit := required_actual (show UnitAt bytes.val start.val 34#u32 next by simpa [Opening] using opening)
      simp [object,readUnit,core.result.Result.Insts.CoreOpsTry.branch,readLiteral]; rfl

private theorem blank_token_progress {bs scope : List U8} {start limit : Nat} {node : rdf.BlankNode} {stop : Usize}
    (token : BlankToken bs scope start limit node stop) : start < stop.val ∧ stop.val ≤ bs.length := by
  obtain ⟨colon,begin,first,next,opening,colonUnit,firstUnit,allowed,tail,budget,nodeScope,label⟩ := token
  have bounds := blank_tail_bounds tail ⟨Nat.le_refl _,firstUnit.2.1⟩
  have := opening.1
  have := colonUnit.1
  have := firstUnit.1
  omega

theorem subject_token_progress {bs scope : List U8} {start stop : Usize} {limit : Nat} {value : rdf.Subject}
    (token : SubjectToken bs scope start limit value stop) : start.val < stop.val ∧ stop.val ≤ bs.length := by
  cases value with
  | Iri value => exact quoted_token_progress token.1
  | Blank node => exact blank_token_progress token

theorem object_token_progress {bs scope : List U8} {start stop : Usize} {limit : Nat} {value : rdf.Object}
    (token : ObjectToken bs scope start limit value stop) : start.val < stop.val ∧ stop.val ≤ bs.length := by
  cases value with
  | Iri value => exact quoted_token_progress token.1
  | Blank node => exact blank_token_progress token
  | Literal value => exact literal_token_progress token

/-- End of a triple's line, before consuming an EOL or exactly at EOF. -/
inductive LineBoundary (bs : List U8) (position : Usize) : Prop
  | eof : position.val = bs.length → LineBoundary bs position
  | eol {cp next} : UnitAt bs position.val cp next → EndLine cp.val → LineBoundary bs position

inductive LineError (bs : List U8) (position : Usize) : ReadError → Prop
  | invalid {error} : MalformedError bs position.val error → LineError bs position error
  | extra {cp next} : UnitAt bs position.val cp next → ¬ EndLine cp.val →
      LineError bs position ⟨.ExpectedLineEnd,position⟩

def LineCorrect (bs : List U8) (position : Usize) : Parsed Unit ReadError → Prop
  | .Ok () => LineBoundary bs position
  | .Err error => LineError bs position error

theorem line_end_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ result, line_end bytes position = .ok result ∧ LineCorrect bytes.val position result := by
  obtain ⟨unit,readUnit,unitCorrect⟩ := at_total_correct bytes position
  cases unit with
  | Err error =>
    refine ⟨.Err error, ?_, LineError.invalid unitCorrect⟩
    simp [line_end,readUnit,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok optional =>
    cases optional with
    | none =>
      exact ⟨.Ok (),by simp [line_end,readUnit,core.result.Result.Insts.CoreOpsTry.branch],LineBoundary.eof unitCorrect⟩
    | some pair =>
      obtain ⟨cp,next⟩ := pair
      by_cases ending : EndLine cp.val
      · exact ⟨.Ok (),by simp [line_end,readUnit,core.result.Result.Insts.CoreOpsTry.branch,eol_total,ending],LineBoundary.eol unitCorrect ending⟩
      · exact ⟨.Err ⟨.ExpectedLineEnd,position⟩,
          by simp [line_end,readUnit,core.result.Result.Insts.CoreOpsTry.branch,eol_total,ending,ntriples.error],
          LineError.extra unitCorrect ending⟩

theorem line_end_accepted_iff (bytes : alloc.vec.Vec U8) (position : Usize) :
    line_end bytes position = .ok (.Ok ()) ↔ LineBoundary bytes.val position := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := line_end_total_correct bytes position
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,LineCorrect] using correct
  · intro boundary
    cases boundary with
    | eof ended => simp [line_end,eof_actual ended,core.result.Result.Insts.CoreOpsTry.branch]
    | eol unit ending => simp [line_end,unit_actual unit,core.result.Result.Insts.CoreOpsTry.branch,eol_total,ending]

/-- A recognized subject and predicate, with their maximal separating trivia. -/
def TriplePredicate (bs scope : List U8) (start : Usize) (limit : Nat)
    (subject : rdf.Subject) (predicate : rdf.RdfIri) (stop : Usize) : Prop :=
  ∃ subjectEnd predicateStart, SubjectToken bs scope start limit subject subjectEnd ∧
    TriviaRuns bs false subjectEnd.val predicateStart.val ∧ IriCorrect bs predicateStart limit (.Ok (predicate,stop))

/-- All three recognized RDF terms, preserving their precise values. -/
def TripleObject (bs scope : List U8) (start : Usize) (limit : Nat) (value : rdf.Triple) (stop : Usize) : Prop :=
  ∃ predicateEnd objectStart, TriplePredicate bs scope start limit value.subject value.predicate predicateEnd ∧
    TriviaRuns bs false predicateEnd.val objectStart.val ∧ ObjectToken bs scope objectStart limit value.object stop

/-- The period and maximal trailing horizontal trivia/comment are consumed. -/
def TripleTerminated (bs scope : List U8) (start : Usize) (limit : Nat) (value : rdf.Triple) (stop : Usize) : Prop :=
  ∃ (objectEnd periodStart periodEnd : Usize), TripleObject bs scope start limit value objectEnd ∧
    TriviaRuns bs false objectEnd.val periodStart.val ∧ UnitAt bs periodStart.val 46#u32 periodEnd ∧
    TriviaRuns bs false periodEnd.val stop.val

def TripleToken (bs scope : List U8) (start : Usize) (limit : Nat) (value : rdf.Triple) (stop : Usize) : Prop :=
  TripleTerminated bs scope start limit value stop ∧ LineBoundary bs stop

inductive TripleError (bs scope : List U8) (start : Usize) (limit : Nat) : ReadError → Prop
  | subject {error} : SubjectError bs start limit error → TripleError bs scope start limit error
  | afterSubject {subject subjectEnd error} : SubjectToken bs scope start limit subject subjectEnd →
      TriviaFails bs false subjectEnd.val error → TripleError bs scope start limit error
  | predicate {subject subjectEnd predicateStart error} : SubjectToken bs scope start limit subject subjectEnd →
      TriviaRuns bs false subjectEnd.val predicateStart.val → IriError bs predicateStart limit error →
      TripleError bs scope start limit error
  | afterPredicate {subject predicate predicateEnd error} : TriplePredicate bs scope start limit subject predicate predicateEnd →
      TriviaFails bs false predicateEnd.val error → TripleError bs scope start limit error
  | object {subject predicate predicateEnd objectStart error} : TriplePredicate bs scope start limit subject predicate predicateEnd →
      TriviaRuns bs false predicateEnd.val objectStart.val → ObjectError bs objectStart limit error →
      TripleError bs scope start limit error
  | afterObject {value objectEnd error} : TripleObject bs scope start limit value objectEnd →
      TriviaFails bs false objectEnd.val error → TripleError bs scope start limit error
  | period {value objectEnd error} {periodStart : Usize} : TripleObject bs scope start limit value objectEnd →
      TriviaRuns bs false objectEnd.val periodStart.val → ExpectCorrect bs periodStart.val 46#u32 .ExpectedPeriod (.Err error) →
      TripleError bs scope start limit error
  | afterPeriod {value objectEnd periodEnd error} {periodStart : Usize} : TripleObject bs scope start limit value objectEnd →
      TriviaRuns bs false objectEnd.val periodStart.val → UnitAt bs periodStart.val 46#u32 periodEnd →
      TriviaFails bs false periodEnd.val error → TripleError bs scope start limit error
  | line {value stop error} : TripleTerminated bs scope start limit value stop → LineError bs stop error →
      TripleError bs scope start limit error

def TripleCorrect (bs scope : List U8) (start : Usize) (limit : Nat) : Parsed (rdf.Triple × Usize) ReadError → Prop
  | .Ok (value,stop) => TripleToken bs scope start limit value stop
  | .Err error => TripleError bs scope start limit error

/-- Complete triple recognition: totality, exact RDF term construction, and
    the first stage-specific diagnostic at its original byte offset. -/
theorem read_triple_total_correct (bytes scope : alloc.vec.Vec U8) (start limit : Usize) :
    ∃ result, read_triple bytes start scope limit = .ok result ∧
      TripleCorrect bytes.val scope.val start limit.val result := by
  obtain ⟨subjectResult,read_subject,subjectCorrect⟩ := subject_total_correct bytes scope start limit
  cases subjectResult with
  | Err error =>
    refine ⟨.Err error, ?_, TripleError.subject subjectCorrect⟩
    simp [read_triple,read_subject,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok pair =>
    obtain ⟨subjectValue,subjectEnd⟩ := pair
    obtain ⟨gap0Result,read_gap0,gap0Correct⟩ := skip_total_correct bytes subjectEnd false
    cases gap0Result with
    | Err error =>
      refine ⟨.Err error, ?_, TripleError.afterSubject subjectCorrect gap0Correct⟩
      simp [read_triple,read_subject,read_gap0,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
    | Ok predicateStart =>
      obtain ⟨predicateResult,read_predicate,predicateCorrect⟩ := read_iri_total_correct bytes predicateStart limit
      cases predicateResult with
      | Err error =>
        refine ⟨.Err error, ?_, TripleError.predicate subjectCorrect gap0Correct predicateCorrect⟩
        simp [read_triple,read_subject,read_gap0,read_predicate,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
      | Ok pair =>
        obtain ⟨predicateValue,predicateEnd⟩ := pair
        have predPrefix : TriplePredicate bytes.val scope.val start limit.val subjectValue predicateValue predicateEnd :=
          ⟨subjectEnd,predicateStart,subjectCorrect,gap0Correct,predicateCorrect⟩
        obtain ⟨gap1Result,read_gap1,gap1Correct⟩ := skip_total_correct bytes predicateEnd false
        cases gap1Result with
        | Err error =>
          refine ⟨.Err error, ?_, TripleError.afterPredicate predPrefix gap1Correct⟩
          simp [read_triple,read_subject,read_gap0,read_predicate,read_gap1,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
        | Ok objectStart =>
          obtain ⟨objectResult,read_object,objectCorrect⟩ := object_total_correct bytes scope objectStart limit
          cases objectResult with
          | Err error =>
            refine ⟨.Err error, ?_, TripleError.object predPrefix gap1Correct objectCorrect⟩
            simp [read_triple,read_subject,read_gap0,read_predicate,read_gap1,read_object,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
          | Ok pair =>
            obtain ⟨objectValue,objectEnd⟩ := pair
            let value : rdf.Triple := ⟨subjectValue,predicateValue,objectValue⟩
            have objectPrefix : TripleObject bytes.val scope.val start limit.val value objectEnd :=
              ⟨predicateEnd,objectStart,predPrefix,gap1Correct,objectCorrect⟩
            obtain ⟨gap2Result,read_gap2,gap2Correct⟩ := skip_total_correct bytes objectEnd false
            cases gap2Result with
            | Err error =>
              refine ⟨.Err error, ?_, TripleError.afterObject objectPrefix gap2Correct⟩
              simp [read_triple,read_subject,read_gap0,read_predicate,read_gap1,read_object,read_gap2,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
            | Ok periodStart =>
              obtain ⟨periodResult,read_period,periodCorrect⟩ := expect_total_correct bytes periodStart 46#u32 .ExpectedPeriod
              cases periodResult with
              | Err error =>
                refine ⟨.Err error, ?_, TripleError.period objectPrefix gap2Correct periodCorrect⟩
                simp [read_triple,read_subject,read_gap0,read_predicate,read_gap1,read_object,read_gap2,read_period,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
              | Ok periodEnd =>
                obtain ⟨gap3Result,read_gap3,gap3Correct⟩ := skip_total_correct bytes periodEnd false
                cases gap3Result with
                | Err error =>
                  refine ⟨.Err error, ?_, TripleError.afterPeriod objectPrefix gap2Correct periodCorrect gap3Correct⟩
                  simp [read_triple,read_subject,read_gap0,read_predicate,read_gap1,read_object,read_gap2,read_period,read_gap3,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
                | Ok stop =>
                  have terminated : TripleTerminated bytes.val scope.val start limit.val value stop :=
                    ⟨objectEnd,periodStart,periodEnd,objectPrefix,gap2Correct,periodCorrect,gap3Correct⟩
                  obtain ⟨lineResult,read_line,lineCorrect⟩ := line_end_total_correct bytes stop
                  cases lineResult with
                  | Err error =>
                    refine ⟨.Err error, ?_, TripleError.line terminated lineCorrect⟩
                    simp [read_triple,read_subject,read_gap0,read_predicate,read_gap1,read_object,read_gap2,read_period,read_gap3,read_line,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
                  | Ok lastUnit =>
                    cases lastUnit
                    refine ⟨.Ok (value,stop), ?_,terminated,lineCorrect⟩
                    simp [read_triple,read_subject,read_gap0,read_predicate,read_gap1,read_object,read_gap2,read_period,read_gap3,read_line,core.result.Result.Insts.CoreOpsTry.branch,value]
theorem read_triple_accepted_iff (bytes scope : alloc.vec.Vec U8) (start stop limit : Usize) (value : rdf.Triple) :
    read_triple bytes start scope limit = .ok (.Ok (value,stop)) ↔
      TripleToken bytes.val scope.val start limit.val value stop := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := read_triple_total_correct bytes scope start limit
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,TripleCorrect] using correct
  · intro token
    obtain ⟨⟨objectEnd,periodStart,periodEnd,⟨predicateEnd,objectStart,
      ⟨subjectEnd,predicateStart,subjectToken,gap0,predicateToken⟩,gap1,objectToken⟩,
      gap2,period,gap3⟩,ending⟩ := token
    have subjectRead := (subject_accepted_iff bytes scope start subjectEnd limit value.subject).mpr subjectToken
    have predicateRead := (read_iri_accepted_iff bytes predicateStart predicateEnd limit value.predicate).mpr predicateToken
    have objectRead := (object_accepted_iff bytes scope objectStart objectEnd limit value.object).mpr objectToken
    have gap0Read := trivia_actual gap0 subjectEnd predicateStart rfl rfl
    have gap1Read := trivia_actual gap1 predicateEnd objectStart rfl rfl
    have gap2Read := trivia_actual gap2 objectEnd periodStart rfl rfl
    have gap3Read := trivia_actual gap3 periodEnd stop rfl rfl
    have periodRead := expect_actual (kind := .ExpectedPeriod) period
    have endingRead := (line_end_accepted_iff bytes stop).mpr ending
    cases value
    simp [read_triple,subjectRead,predicateRead,objectRead,gap0Read,gap1Read,gap2Read,gap3Read,
      periodRead,endingRead,core.result.Result.Insts.CoreOpsTry.branch]

private theorem triple_predicate_bounds {bs scope : List U8} {start stop : Usize} {limit : Nat}
    {subject : rdf.Subject} {predicate : rdf.RdfIri}
    (token : TriplePredicate bs scope start limit subject predicate stop) : start.val < stop.val ∧ stop.val ≤ bs.length := by
  obtain ⟨subjectEnd,predicateStart,subjectToken,gap,predicateToken⟩ := token
  have := subject_token_progress subjectToken
  have := trivia_bounds gap
  have := quoted_token_progress predicateToken.1
  omega

private theorem triple_object_bounds {bs scope : List U8} {start stop : Usize} {limit : Nat} {value : rdf.Triple}
    (token : TripleObject bs scope start limit value stop) : start.val < stop.val ∧ stop.val ≤ bs.length := by
  obtain ⟨predicateEnd,objectStart,predicateToken,gap,objectToken⟩ := token
  have := triple_predicate_bounds predicateToken
  have := trivia_bounds gap
  have := object_token_progress objectToken
  omega

theorem read_triple_token_progress {bs scope : List U8} {start stop : Usize} {limit : Nat} {value : rdf.Triple}
    (token : TripleToken bs scope start limit value stop) : start.val < stop.val ∧ stop.val ≤ bs.length := by
  obtain ⟨⟨objectEnd,periodStart,periodEnd,objects,gap0,period,gap1⟩,ending⟩ := token
  have := triple_object_bounds objects
  have := trivia_bounds gap0
  have := period.1
  have := trivia_bounds gap1
  omega

/-- Ordered whole-document occurrences; repeated triples remain repeated.
    Every term obeys the supplied byte budget and every occurrence the count
    budget. These limits are explicit; no physical memory guarantee is assumed. -/
inductive DocumentTail (bs scope : List U8) (termLimit tripleLimit : Nat) : Usize → Nat → List rdf.Triple → Prop
  | eof {position count} : position.val = bs.length → DocumentTail bs scope termLimit tripleLimit position count []
  | triple {position count value stop next tail} : TripleToken bs scope position termLimit value stop →
      count < tripleLimit → TriviaRuns bs true stop.val next.val →
      DocumentTail bs scope termLimit tripleLimit next (count+1) tail →
      DocumentTail bs scope termLimit tripleLimit position count (value::tail)

inductive DocumentTailError (bs scope : List U8) (termLimit tripleLimit : Nat) : Usize → Nat → ReadError → Prop
  | triple {position count error} : position.val < bs.length → TripleError bs scope position termLimit error →
      DocumentTailError bs scope termLimit tripleLimit position count error
  | limit {position count value stop} : TripleToken bs scope position termLimit value stop → tripleLimit ≤ count →
      DocumentTailError bs scope termLimit tripleLimit position count ⟨.ResourceLimit,position⟩
  | trivia {position count value stop error} : TripleToken bs scope position termLimit value stop →
      count < tripleLimit → TriviaFails bs true stop.val error →
      DocumentTailError bs scope termLimit tripleLimit position count error
  | later {position count value stop next error} : TripleToken bs scope position termLimit value stop →
      count < tripleLimit → TriviaRuns bs true stop.val next.val →
      DocumentTailError bs scope termLimit tripleLimit next (count+1) error →
      DocumentTailError bs scope termLimit tripleLimit position count error

def DocumentTailCorrect (bs scope : List U8) (termLimit tripleLimit : Nat) (position : Usize) (initial : List rdf.Triple) :
    Parsed rdf.RawGraph ReadError → Prop
  | .Ok graph => ∃ tail, DocumentTail bs scope termLimit tripleLimit position initial.length tail ∧
      graph.triples.val = initial ++ tail
  | .Err error => DocumentTailError bs scope termLimit tripleLimit position initial.length error

def Document (bs scope : List U8) (termLimit tripleLimit : Nat) (triples : List rdf.Triple) : Prop :=
  ∃ (position : Usize), TriviaRuns bs true 0 position.val ∧ DocumentTail bs scope termLimit tripleLimit position 0 triples

inductive DocumentError (bs scope : List U8) (termLimit tripleLimit : Nat) : ReadError → Prop
  | leading {error} : TriviaFails bs true 0 error → DocumentError bs scope termLimit tripleLimit error
  | tail {position error} : TriviaRuns bs true 0 position.val →
      DocumentTailError bs scope termLimit tripleLimit position 0 error → DocumentError bs scope termLimit tripleLimit error

def DocumentCorrect (bs scope : List U8) (termLimit tripleLimit : Nat) : Parsed rdf.RawGraph ReadError → Prop
  | .Ok graph => Document bs scope termLimit tripleLimit graph.triples.val
  | .Err error => DocumentError bs scope termLimit tripleLimit error

def ReadCorrect (bs scope : List U8) (termLimit tripleLimit : Nat) : ReadResult → Prop
  | .Graph graph => Document bs scope termLimit tripleLimit graph.triples.val
  | .Error error => DocumentError bs scope termLimit tripleLimit error

private theorem read_from_total (bytes scope : alloc.vec.Vec U8) (limits : Limits) (position : Usize)
    (initial : alloc.vec.Vec rdf.Triple) (positionBound : position.val ≤ bytes.val.length)
    (prefixBound : initial.val.length ≤ position.val) :
    ∃ result, read_from bytes scope limits position initial = .ok result ∧
      DocumentTailCorrect bytes.val scope.val limits.max_term_bytes.val limits.max_triples.val position initial.val result := by
  rw [read_from]
  by_cases more : position.val < bytes.val.length
  · obtain ⟨tripleResult,readTriple,tripleCorrect⟩ := read_triple_total_correct bytes scope position limits.max_term_bytes
    cases tripleResult with
    | Err error =>
      refine ⟨.Err error, ?_,DocumentTailError.triple more tripleCorrect⟩
      simp [alloc.vec.Vec.len_val,more,readTriple,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
    | Ok pair =>
      obtain ⟨value,stop⟩ := pair
      have progress := read_triple_token_progress tripleCorrect
      by_cases full : limits.max_triples.val ≤ initial.val.length
      · refine ⟨.Err ⟨.ResourceLimit,position⟩, ?_,DocumentTailError.limit tripleCorrect full⟩
        simp [alloc.vec.Vec.len_val,more,readTriple,core.result.Result.Insts.CoreOpsTry.branch,full,ntriples.error]
      · have room : initial.val.length < Usize.max := by have := bytes.property; omega
        obtain ⟨appended,pushTriple,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec initial value room)
        obtain ⟨spacingResult,readSpacing,spacingCorrect⟩ := skip_total_correct bytes stop true
        cases spacingResult with
        | Err error =>
          refine ⟨.Err error, ?_,DocumentTailError.trivia tripleCorrect (by omega) spacingCorrect⟩
          simp [alloc.vec.Vec.len_val,more,readTriple,core.result.Result.Insts.CoreOpsTry.branch,full,pushTriple,
            readSpacing,same_residual]
        | Ok next =>
          have nextBounds := trivia_bounds spacingCorrect
          have appendedBound : appended.val.length ≤ next.val := by simp [contents]; omega
          obtain ⟨result,readTail,tailCorrect⟩ := read_from_total bytes scope limits next appended nextBounds.2 appendedBound
          refine ⟨result, ?_, ?_⟩
          · simp [alloc.vec.Vec.len_val,more,readTriple,core.result.Result.Insts.CoreOpsTry.branch,full,pushTriple,
              readSpacing,readTail]
          · cases result with
            | Err error =>
              exact DocumentTailError.later tripleCorrect (by omega) spacingCorrect (by
                simpa [DocumentTailCorrect,contents] using tailCorrect)
            | Ok graph =>
              obtain ⟨tail,tailSpec,tailValues⟩ := tailCorrect
              refine ⟨value::tail,DocumentTail.triple tripleCorrect (by omega) spacingCorrect ?_, ?_⟩
              · simpa [contents] using tailSpec
              · simpa [contents,List.append_assoc] using tailValues
  · have ended : position.val = bytes.val.length := by omega
    exact ⟨.Ok ⟨initial⟩,by simp [alloc.vec.Vec.len_val,more],[],DocumentTail.eof ended,by simp⟩
termination_by bytes.val.length-position.val
decreasing_by have := progress.1; omega

private theorem read_impl_total (bytes scope : alloc.vec.Vec U8) (limits : Limits) :
    ∃ result, read_impl bytes scope limits = .ok result ∧
      DocumentCorrect bytes.val scope.val limits.max_term_bytes.val limits.max_triples.val result := by
  obtain ⟨leading,readLeading,leadingCorrect⟩ := skip_total_correct bytes 0#usize true
  cases leading with
  | Err error =>
    exact ⟨.Err error,by simp [read_impl,readLeading,core.result.Result.Insts.CoreOpsTry.branch,same_residual],
      DocumentError.leading leadingCorrect⟩
  | Ok position =>
    have bounds := trivia_bounds leadingCorrect
    obtain ⟨result,readTail,tailCorrect⟩ := read_from_total bytes scope limits position (alloc.vec.Vec.new rdf.Triple)
      bounds.2 (by simp)
    refine ⟨result,by simp [read_impl,readLeading,core.result.Result.Insts.CoreOpsTry.branch,readTail], ?_⟩
    cases result with
    | Err error => exact DocumentError.tail leadingCorrect tailCorrect
    | Ok graph =>
      obtain ⟨tail,tailSpec,tailValues⟩ := tailCorrect
      have equal : graph.triples.val = tail := by simpa using tailValues
      exact ⟨position,leadingCorrect,by simpa [equal] using tailSpec⟩

/-- Byte-to-graph construction is total in the pinned translation model;
    success preserves all and only the specified ordered triple occurrences.
    Errors retain their first original offset and never expose a partial graph. -/
theorem read_with_limits_total_correct (bytes scope : alloc.vec.Vec U8) (limits : Limits) :
    ∃ result, read_with_limits bytes scope limits = .ok result ∧
      ReadCorrect bytes.val scope.val limits.max_term_bytes.val limits.max_triples.val result := by
  obtain ⟨result,executed,correct⟩ := read_impl_total bytes scope limits
  cases result with
  | Err error => exact ⟨.Error error,by simp [read_with_limits,executed],correct⟩
  | Ok graph => exact ⟨.Graph graph,by simp [read_with_limits,executed],correct⟩

theorem read_total_correct (bytes scope : alloc.vec.Vec U8) :
    ∃ result, ntriples.read bytes scope = .ok result ∧
      ReadCorrect bytes.val scope.val bytes.val.length bytes.val.length result := by
  simpa [ntriples.read,alloc.vec.Vec.len_val] using
    read_with_limits_total_correct bytes scope ⟨alloc.vec.Vec.len bytes,alloc.vec.Vec.len bytes⟩

private theorem read_from_actual {bytes scope : alloc.vec.Vec U8} {limits : Limits} {position : Usize}
    {count : Nat} {tail : List rdf.Triple}
    (document : DocumentTail bytes.val scope.val limits.max_term_bytes.val limits.max_triples.val position count tail) :
    ∀ (initial : alloc.vec.Vec rdf.Triple), initial.val.length = count → initial.val.length ≤ position.val →
      ∃ graph, read_from bytes scope limits position initial = .ok (.Ok graph) ∧ graph.triples.val = initial.val ++ tail := by
  induction document with
  | eof ended =>
    intro initial prefixCount prefixBound
    rw [read_from]
    exact ⟨⟨initial⟩,by simp [alloc.vec.Vec.len_val,ended],by simp⟩
  | @triple position count value stop next tail token room spacing document ih =>
    intro initial prefixCount prefixBound
    have progress := read_triple_token_progress token
    have spacingBounds := trivia_bounds spacing
    have more : position.val < bytes.val.length := by omega
    have capacity : initial.val.length < Usize.max := by have := bytes.property; omega
    obtain ⟨appended,pushTriple,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec initial value capacity)
    have appendedCount : appended.val.length = count+1 := by simp [contents,prefixCount]
    have appendedBound : appended.val.length ≤ next.val := by simp [contents]; omega
    obtain ⟨graph,readTail,tailValues⟩ := ih appended appendedCount appendedBound
    have readTriple := (read_triple_accepted_iff bytes scope position stop limits.max_term_bytes value).mpr token
    have readSpacing := trivia_actual spacing stop next rfl rfl
    refine ⟨graph, ?_, ?_⟩
    · rw [read_from]
      have notFull : ¬ limits.max_triples.val ≤ initial.val.length := by omega
      simp [alloc.vec.Vec.len_val,more,readTriple,core.result.Result.Insts.CoreOpsTry.branch,notFull,pushTriple,readSpacing,readTail]
    · simpa [contents,List.append_assoc] using tailValues

private theorem graph_equal {first second : rdf.RawGraph} (same : first.triples.val = second.triples.val) : first = second := by
  cases first with
  | mk a =>
    cases second with
    | mk b => congr 1; exact (alloc.vec.Vec.eq_iff a b).mpr same

/-- Complete acceptance for the public byte-to-graph API under its explicit
    term/count budgets, including leading/trailing comments and empty input. -/
theorem read_with_limits_accepted_iff (bytes scope : alloc.vec.Vec U8) (limits : Limits) (graph : rdf.RawGraph) :
    read_with_limits bytes scope limits = .ok (.Graph graph) ↔
      Document bytes.val scope.val limits.max_term_bytes.val limits.max_triples.val graph.triples.val := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := read_with_limits_total_correct bytes scope limits
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,ReadCorrect] using correct
  · rintro ⟨position,leading,document⟩
    have bounds := trivia_bounds leading
    obtain ⟨actual,readTail,contents⟩ := read_from_actual document (alloc.vec.Vec.new rdf.Triple) (by simp) (by simp)
    have equal : actual = graph := graph_equal (by simpa using contents)
    subst actual
    have readLeading := trivia_actual leading 0#usize position rfl rfl
    simp [read_with_limits,read_impl,readLeading,core.result.Result.Insts.CoreOpsTry.branch,readTail]

theorem read_accepted_iff (bytes scope : alloc.vec.Vec U8) (graph : rdf.RawGraph) :
    ntriples.read bytes scope = .ok (.Graph graph) ↔
      Document bytes.val scope.val bytes.val.length bytes.val.length graph.triples.val := by
  simpa [ntriples.read,alloc.vec.Vec.len_val] using
    read_with_limits_accepted_iff bytes scope ⟨alloc.vec.Vec.len bytes,alloc.vec.Vec.len bytes⟩ graph

private theorem document_tail_count {bs scope : List U8} {termLimit tripleLimit count : Nat} {position : Usize}
    {tail : List rdf.Triple} (valid : DocumentTail bs scope termLimit tripleLimit position count tail) :
    count ≤ tripleLimit → count+tail.length ≤ tripleLimit := by
  induction valid with
  | eof ended => simp
  | triple token room spacing document ih =>
    intro countBound
    have bound := ih (by omega)
    simp only [List.length_cons]
    omega

theorem document_count_bounded {bs scope : List U8} {termLimit tripleLimit : Nat} {triples : List rdf.Triple}
    (valid : Document bs scope termLimit tripleLimit triples) : triples.length ≤ tripleLimit := by
  obtain ⟨position,leading,document⟩ := valid
  simpa using document_tail_count document (Nat.zero_le tripleLimit)

end Rowl.NTriples
