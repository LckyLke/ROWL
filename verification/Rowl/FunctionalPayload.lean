import Rowl.NTriples
import Rowl.Functional

namespace Rowl.FunctionalPayload
open Aeneas Aeneas.Std RowlFrontendRust RowlFrontendRust.functional_payload
open scoped Computability
open Rowl.NTriples Rowl.Unicode
open RowlFrontendRust.ntriples (ReadError ErrorKind)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- Exactly the two escape markers permitted by Functional Syntax. -/
def EscapeMarker (cp : Nat) : Prop := cp = 34 ∨ cp = 92
/-- Raw XML text, excluding the two syntactic characters. Newlines are allowed. -/
def RawAllowed (cp : Nat) : Prop := XmlChar cp ∧ cp ≠ 34 ∧ cp ≠ 92
/-- An escape has one decoded marker unit; its source backslash is supplied
    separately by the complete item relation. -/
def EscapeValue (bs : List U8) (start : Nat) (cp : U32) (stop : Usize) : Prop :=
  UnitAt bs start cp stop ∧ EscapeMarker cp.val
inductive EscapeError (bs : List U8) (slash : Usize) (start : Nat) : ReadError → Prop
  | required {error} : RequiredError bs start error → EscapeError bs slash start error
  | marker {cp next} : UnitAt bs start cp next → ¬ EscapeMarker cp.val →
      EscapeError bs slash start ⟨.InvalidEscape,slash⟩
def EscapeCorrect (bs : List U8) (slash : Usize) (start : Nat) :
    Parsed (U32 × Usize) ReadError → Prop
  | .Ok (cp,stop) => EscapeValue bs start cp stop
  | .Err error => EscapeError bs slash start error

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

private theorem same_residual {T : Type} (e : ReadError) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      T (core.convert.FromSame ReadError) (.Err e) = .ok (.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame]


private theorem required_actual {bytes : alloc.vec.Vec U8} {position : Usize}
    {cp : U32} {next : Usize} (unit : UnitAt bytes.val position.val cp next) :
    ntriples.required bytes position = .ok (.Ok (cp,next)) := by
  obtain ⟨result,executed,correct⟩ := required_total_correct bytes position
  cases result with
  | Ok pair =>
    obtain ⟨other,finish⟩ := pair
    obtain ⟨rfl,rfl⟩ := unit_unique correct unit
    exact executed
  | Err error =>
    rcases correct with bad | ⟨kind,offset,eof⟩
    · rcases bad.2.2 with outside | ⟨inside,invalid⟩
      · have := unit.1; have := unit.2.1; omega
      · rw [unit.2.2] at invalid; contradiction
    · have := unit.1; have := unit.2.1; omega
private theorem expect_actual {bytes : alloc.vec.Vec U8} {position : Usize}
    {cp : U32} {next : Usize} (unit : UnitAt bytes.val position.val cp next) :
    ntriples.expect bytes position cp .InvalidCharacter = .ok (.Ok next) := by
  simp [ntriples.expect, required_actual unit, core.result.Result.Insts.CoreOpsTry.branch]

theorem escape_total_correct (bytes : alloc.vec.Vec U8) (slash position : Usize) :
    ∃ result, escape bytes slash position = .ok result ∧
      EscapeCorrect bytes.val slash position.val result := by
  obtain ⟨unit,executed,correct⟩ := required_total_correct bytes position
  cases unit with
  | Err error =>
    exact ⟨.Err error, by simp [escape,executed,core.result.Result.Insts.CoreOpsTry.branch,same_residual],
      EscapeError.required correct⟩
  | Ok pair =>
    obtain ⟨cp,next⟩ := pair
    by_cases allowed : EscapeMarker cp.val
    · refine ⟨.Ok (cp,next), ?_, correct,allowed⟩
      simp [escape,executed,core.result.Result.Insts.CoreOpsTry.branch,EscapeMarker,UScalar.eq_equiv] at *
      rcases allowed with yes | yes <;> simp_all
    · refine ⟨.Err ⟨.InvalidEscape,slash⟩, ?_, EscapeError.marker correct allowed⟩
      simp [escape,executed,core.result.Result.Insts.CoreOpsTry.branch,EscapeMarker,UScalar.eq_equiv,
        functional_payload.error] at *
      simp_all
private theorem escape_actual {bytes : alloc.vec.Vec U8} {slash position stop : Usize} {cp : U32}
    (value : EscapeValue bytes.val position.val cp stop) :
    escape bytes slash position = .ok (.Ok (cp,stop)) := by
  have marker : cp = 34#u32 ∨ cp = 92#u32 := by simpa [EscapeMarker,UScalar.eq_equiv] using value.2
  rcases marker with yes | yes <;>
    simp [escape,required_actual value.1,core.result.Result.Insts.CoreOpsTry.branch,yes]

inductive QuotedItem (bs : List U8) : Nat → U32 → Usize → Prop
  | raw {start cp next} : UnitAt bs start cp next → RawAllowed cp.val →
      QuotedItem bs start cp next
  | escaped {start next cp stop} : UnitAt bs start 92#u32 next →
      EscapeValue bs next.val cp stop → QuotedItem bs start cp stop
inductive ItemError (bs : List U8) (position : Usize) : ReadError → Prop
  | raw {cp next} : UnitAt bs position.val cp next → cp ≠ 92#u32 →
      ¬ RawAllowed cp.val → ItemError bs position ⟨.InvalidCharacter,position⟩
  | escaped {next error} : UnitAt bs position.val 92#u32 next →
      EscapeError bs position next.val error → ItemError bs position error
def ItemCorrect (bs : List U8) (position : Usize) : Parsed (U32 × Usize) ReadError → Prop
  | .Ok (cp,stop) => QuotedItem bs position.val cp stop
  | .Err error => ItemError bs position error

theorem quoted_item_total_correct (bytes : alloc.vec.Vec U8) (position : Usize)
    (cp : U32) (next : Usize) (unit : UnitAt bytes.val position.val cp next) :
    ∃ result, quoted_item bytes position cp next = .ok result ∧ ItemCorrect bytes.val position result := by
  by_cases slash : cp = 92#u32
  · subst cp
    obtain ⟨result,executed,correct⟩ := escape_total_correct bytes position next
    refine ⟨result, by simp [quoted_item,executed], ?_⟩
    cases result with
    | Ok pair => obtain ⟨value,stop⟩ := pair; exact QuotedItem.escaped unit correct
    | Err error => exact ItemError.escaped unit correct
  · by_cases allowed : RawAllowed cp.val
    · refine ⟨.Ok (cp,next), ?_, QuotedItem.raw unit allowed⟩
      have quote : cp ≠ 34#u32 := by simpa [UScalar.eq_equiv] using allowed.2.1
      simp [quoted_item,slash,quote,xml_character_total_correct,allowed.1]
    · refine ⟨.Err ⟨.InvalidCharacter,position⟩, ?_, ItemError.raw unit slash allowed⟩
      have noSlash : cp.val ≠ 92 := by simpa [UScalar.eq_equiv] using slash
      have bad : cp = 34#u32 ∨ ¬ XmlChar cp.val := by
        by_cases quote : cp.val = 34
        · exact Or.inl (by simpa [UScalar.eq_equiv] using quote)
        · exact Or.inr (fun xml => allowed ⟨xml,quote,noSlash⟩)
      rcases bad with bad | bad <;>
        simp [quoted_item,slash,bad,xml_character_total_correct,functional_payload.error]

theorem quoted_item_progress {bs : List U8} {start : Nat} {cp : U32} {stop : Usize}
    (item : QuotedItem bs start cp stop) :
    Rowl.Encoding.Scalar cp.val ∧ start < stop.val ∧ stop.val ≤ bs.length := by
  cases item with
  | raw unit allowed =>
    refine ⟨?_,unit.1,unit.2.1⟩
    simp only [RawAllowed,XmlChar,Rowl.Encoding.Scalar] at *
    omega
  | escaped unit payload =>
    refine ⟨?_,by have := unit.1; have := payload.1.1; omega,payload.1.2.1⟩
    simp only [EscapeMarker,Rowl.Encoding.Scalar] at *
    rcases payload.2 with h | h <;> omega
private theorem quoted_item_actual {bytes : alloc.vec.Vec U8} {position : Usize}
    {cp value : U32} {next stop : Usize} (unit : UnitAt bytes.val position.val cp next)
    (item : QuotedItem bytes.val position.val value stop) :
    quoted_item bytes position cp next = .ok (.Ok (value,stop)) := by
  cases item with
  | raw other allowed =>
    obtain ⟨rfl,rfl⟩ := unit_unique unit other
    have slash : cp ≠ 92#u32 := by simpa [UScalar.eq_equiv] using allowed.2.2
    have quote : cp ≠ 34#u32 := by simpa [UScalar.eq_equiv] using allowed.2.1
    simp [quoted_item,slash,quote,xml_character_total_correct,allowed.1]
  | escaped other payload =>
    obtain ⟨rfl,rfl⟩ := unit_unique unit other
    simp [quoted_item,escape_actual (slash := position) payload]

theorem quoted_item_accepted_iff (bytes : alloc.vec.Vec U8) (position : Usize)
    (cp value : U32) (next stop : Usize) (unit : UnitAt bytes.val position.val cp next) :
    quoted_item bytes position cp next = .ok (.Ok (value,stop)) ↔ QuotedItem bytes.val position.val value stop := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := quoted_item_total_correct bytes position cp next unit
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,ItemCorrect] using correct
  · exact quoted_item_actual unit

/-- Delimited body grammar. Raw characters and escaped characters are encoded
    by the independent canonical RFC 3629 production before concatenation.
    The first unescaped closing delimiter ends the token. -/
inductive QuotedBody (bs : List U8) : Usize → List U8 → Usize → Prop
  | close {start stop} : UnitAt bs start.val 34#u32 stop →
      QuotedBody bs start [] stop
  | item {start cp next value finish encoded word stop} :
      UnitAt bs start.val cp next → cp ≠ 34#u32 →
      QuotedItem bs start.val value finish →
      Rowl.Encoding.EncodeCorrect value.val (some encoded) →
      QuotedBody bs finish word stop →
      QuotedBody bs start (Rowl.Encoding.Bytes encoded ++ word) stop

/-- Exact first failure of a quoted body. A limit failure occurs at the
    original source unit, including the backslash of an escaped unit. -/
inductive BodyError (bs : List U8) (limit : Nat) :
    Nat → Usize → ReadError → Prop
  | required {before start error} : RequiredError bs start.val error →
      BodyError bs limit before start error
  | item {before start cp next error} : UnitAt bs start.val cp next → cp ≠ 34#u32 →
      ItemError bs start error → BodyError bs limit before start error
  | limit {before start cp next value finish encoded} : UnitAt bs start.val cp next →
      cp ≠ 34#u32 → QuotedItem bs start.val value finish →
      Rowl.Encoding.EncodeCorrect value.val (some encoded) →
      limit < before + (Rowl.Encoding.Bytes encoded).length →
      BodyError bs limit before start ⟨.ResourceLimit,start⟩
  | afterItem {before start cp next value finish encoded error} :
      UnitAt bs start.val cp next → cp ≠ 34#u32 →
      QuotedItem bs start.val value finish →
      Rowl.Encoding.EncodeCorrect value.val (some encoded) →
      before + (Rowl.Encoding.Bytes encoded).length ≤ limit →
      BodyError bs limit (before + (Rowl.Encoding.Bytes encoded).length) finish error →
      BodyError bs limit before start error

def BodyCorrect (bs : List U8) (limit : Nat) (start : Usize)
    (before : List U8) : Parsed (alloc.vec.Vec U8 × Usize) ReadError → Prop
  | .Ok (output,stop) => ∃ word, QuotedBody bs start word stop ∧
      output.val = before ++ word ∧ output.val.length ≤ limit
  | .Err error => BodyError bs limit before.length start error

private theorem append_success {before after : List U8} {encoded : encoding.Encoded} {limit : Nat}
    (correct : BufferAppend before (Rowl.Encoding.Bytes encoded) limit true after) :
    before.length + (Rowl.Encoding.Bytes encoded).length ≤ limit ∧
      after = before ++ Rowl.Encoding.Bytes encoded ∧ after.length ≤ limit := by
  obtain ⟨accepted,contents,bounded⟩ := correct
  have room : before.length + (Rowl.Encoding.Bytes encoded).length ≤ limit := by
    simpa using accepted.symm
  have capacity : (Rowl.Encoding.Bytes encoded).length ≤ limit-before.length := by omega
  exact ⟨room,by simpa [List.take_of_length_le capacity] using contents,bounded⟩

private theorem read_quoted_loop_total (bytes : alloc.vec.Vec U8) (limit position : Usize)
    (output : alloc.vec.Vec U8) (bounded : output.val.length ≤ limit.val) :
    ∃ result, read_quoted_loop bytes limit position output = .ok result ∧
      BodyCorrect bytes.val limit.val position output.val result := by
  obtain ⟨unit,readUnit,unitCorrect⟩ := required_total_correct bytes position
  cases unit with
  | Err error =>
    refine ⟨.Err error, ?_, BodyError.required unitCorrect⟩
    rw [read_quoted_loop]
    simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok pair =>
    obtain ⟨cp,next⟩ := pair
    by_cases close : cp = 34#u32
    · subst cp
      refine ⟨.Ok (output,next), ?_, [], QuotedBody.close unitCorrect, by simp, bounded⟩
      rw [read_quoted_loop]
      simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch]
    · obtain ⟨item,readItem,itemCorrect⟩ := quoted_item_total_correct bytes position cp next unitCorrect
      cases item with
      | Err error =>
        refine ⟨.Err error, ?_, BodyError.item unitCorrect close itemCorrect⟩
        rw [read_quoted_loop]
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
            rw [read_quoted_loop]
            simp [readUnit,core.result.Result.Insts.CoreOpsTry.branch,close,readItem,encodeUnit,
              appendUnit,functional_payload.error]
          | true =>
            obtain ⟨room,contents,afterBound⟩ := append_success appendCorrect
            obtain ⟨result,tail,tailCorrect⟩ := read_quoted_loop_total bytes limit finish after afterBound
            refine ⟨result, ?_, ?_⟩
            · rw [read_quoted_loop]
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

private theorem read_quoted_loop_actual {bytes : alloc.vec.Vec U8} {limit : Usize}
    {position stop : Usize} {word : List U8} (body : QuotedBody bytes.val position word stop) :
    ∀ output : alloc.vec.Vec U8, output.val.length + word.length ≤ limit.val →
      ∃ final, read_quoted_loop bytes limit position output = .ok (.Ok (final,stop)) ∧
        final.val = output.val ++ word := by
  induction body with
  | close unit =>
    intro output fits
    refine ⟨output, ?_, by simp⟩
    rw [read_quoted_loop]
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
    rw [read_quoted_loop]
    simp [required_actual unit,core.result.Result.Insts.CoreOpsTry.branch,notClose,
      quoted_item_actual unit item,(Rowl.Encoding.encode_some_iff value encoded).mpr encodedCorrect,
      appendUnit,rest]

def QuotedToken (bs : List U8) (start : Usize) (word : List U8) (stop : Usize) : Prop :=
  ∃ next, UnitAt bs start.val 34#u32 next ∧ QuotedBody bs next word stop

inductive QuotedError (bs : List U8) (start : Usize) (limit : Nat) : ReadError → Prop
  | opening {error} : ExpectCorrect bs start.val 34#u32 .InvalidCharacter (.Err error) →
      QuotedError bs start limit error
  | body {next error} : UnitAt bs start.val 34#u32 next →
      BodyError bs limit 0 next error → QuotedError bs start limit error

def QuotedCorrect (bs : List U8) (start : Usize) (limit : Nat) :
    Parsed (alloc.vec.Vec U8 × Usize) ReadError → Prop
  | .Ok (output,stop) => QuotedToken bs start output.val stop ∧ output.val.length ≤ limit
  | .Err error => QuotedError bs start limit error

/-- Whole quoted-token recognition is total: opening/closing delimiters,
    raw Unicode, complete escapes, exact decoded bytes and first diagnostic.
    No malformed scalar can reach the encoder's failure branch. -/
theorem read_quoted_total_correct (bytes : alloc.vec.Vec U8) (start : Usize) (limit : Usize) :
    ∃ result, read_quoted bytes start limit = .ok result ∧
      QuotedCorrect bytes.val start limit.val result := by
  obtain ⟨opening,readOpening,openingCorrect⟩ := Rowl.NTriples.expect_total_correct bytes start 34#u32 .InvalidCharacter
  cases opening with
  | Err error =>
    refine ⟨.Err error, ?_, QuotedError.opening openingCorrect⟩
    simp [read_quoted,readOpening,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | Ok next =>
    obtain ⟨result,readBody,bodyCorrect⟩ := read_quoted_loop_total bytes limit next (alloc.vec.Vec.new U8) (by simp)
    refine ⟨result, ?_, ?_⟩
    · simp [read_quoted,readOpening,readBody,core.result.Result.Insts.CoreOpsTry.branch]
    · cases result with
      | Err error => exact QuotedError.body openingCorrect (by simpa [BodyCorrect] using bodyCorrect)
      | Ok pair =>
        obtain ⟨output,stop⟩ := pair
        obtain ⟨word,body,contents,bounded⟩ := bodyCorrect
        have same : output.val = word := by simpa using contents
        exact ⟨⟨next,openingCorrect,by simpa [same] using body⟩,bounded⟩

/-- Every and only grammar-legal token within the caller's byte budget is
    accepted, with exact spelling after unescaping and exact source offset. -/
theorem read_quoted_accepted_iff (bytes : alloc.vec.Vec U8) (start stop : Usize)
    (limit : Usize) (output : alloc.vec.Vec U8) :
    read_quoted bytes start limit = .ok (.Ok (output,stop)) ↔
      QuotedToken bytes.val start output.val stop ∧ output.val.length ≤ limit.val := by
  constructor
  · intro accepted
    obtain ⟨result,executed,correct⟩ := read_quoted_total_correct bytes start limit
    have equal := Result.ok_injective (executed.symm.trans accepted)
    simpa [equal,QuotedCorrect] using correct
  · rintro ⟨⟨next,opening,body⟩,fits⟩
    have readOpening := expect_actual opening
    obtain ⟨final,readBody,contents⟩ := read_quoted_loop_actual body (alloc.vec.Vec.new U8) (by simpa using fits)
    have same : final = output := (alloc.vec.Vec.eq_iff final output).mpr (by simpa using contents)
    simp_all [read_quoted,core.result.Result.Insts.CoreOpsTry.branch]

theorem quoted_token_progress {bs : List U8} {start stop : Usize} {word : List U8}
    (token : QuotedToken bs start word stop) : start.val < stop.val ∧ stop.val ≤ bs.length := by
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

private theorem unit_cons {bs : List U8} {start endpoint : Nat} {cp : U32} {next : Usize} {word : List Nat}
    (unit : UnitAt bs start cp next) (tail : Rowl.Longest.Utf8Span bs next.val endpoint word) :
    Rowl.Longest.Utf8Span bs start endpoint (cp.val :: word) := by
  have endpoint : start + (next.val-start) = next.val := by have := unit.1; omega
  refine .character unit.2.2 (by have := unit.1; omega) ?_ ?_
  · simpa [endpoint] using unit.2.1
  · simpa [endpoint] using tail

private theorem span_append {bs : List U8} {start middle finish : Nat} {left right : List Nat}
    (one : Rowl.Longest.Utf8Span bs start middle left) (two : Rowl.Longest.Utf8Span bs middle finish right) :
    Rowl.Longest.Utf8Span bs start finish (left ++ right) := by
  induction one with
  | empty bounded => simpa using two
  | character unit positive fits tail ih => exact .character unit positive fits (ih two)

private theorem item_source {bs : List U8} {start : Nat} {value : U32} {stop : Usize}
    (item : QuotedItem bs start value stop) :
    ∃ word, Rowl.Longest.Utf8Span bs start stop.val word ∧ word ∈ Rowl.Functional.QuotedBody := by
  cases item with
  | raw unit allowed =>
    refine ⟨[value.val],unit_cons unit (.empty unit.2.1),?_⟩
    exact Or.inl ⟨value.val,rfl,allowed⟩
  | escaped unit payload =>
    refine ⟨[92,value.val],unit_cons unit (unit_cons payload.1 (.empty payload.1.2.1)),?_⟩
    apply Or.inr
    apply Language.mem_mul.mpr
    refine ⟨[92],⟨92,rfl,by omega,by omega⟩,[value.val],?_,rfl⟩
    rcases payload.2 with quote | slash
    · exact Or.inl ⟨value.val,rfl,by omega,by omega⟩
    · exact Or.inr ⟨value.val,rfl,by omega,by omega⟩

private theorem body_language_cons (head tail : List Nat)
    (headLegal : head ∈ Rowl.Functional.QuotedBody)
    (tailLegal : tail ∈ Rowl.Functional.QuotedBody∗ * Rowl.Iri.Range 34 34) :
    head ++ tail ∈ Rowl.Functional.QuotedBody∗ * Rowl.Iri.Range 34 34 := by
  obtain ⟨parts,partsLegal,closing,closingLegal,rfl⟩ := Language.mem_mul.mp tailLegal
  obtain ⟨words,rfl,wordsLegal⟩ := Language.mem_kstar.mp partsLegal
  have prefixed : head ++ words.flatten ∈ Rowl.Functional.QuotedBody∗ := by
    refine ⟨head::words,rfl,?_⟩
    intro word member
    rcases List.mem_cons.mp member with rfl | member
    · exact headLegal
    · exact wordsLegal word member
  exact Language.mem_mul.mpr ⟨head ++ words.flatten,prefixed,closing,closingLegal,by simp [List.append_assoc]⟩

private theorem body_source {bs : List U8} {start stop : Usize} {payload : List U8}
    (body : QuotedBody bs start payload stop) :
    ∃ word, Rowl.Longest.Utf8Span bs start.val stop.val word ∧
      word ∈ Rowl.Functional.QuotedBody∗ * Rowl.Iri.Range 34 34 := by
  induction body with
  | close unit =>
    refine ⟨[34],unit_cons unit (.empty unit.2.1),?_⟩
    exact Language.mem_mul.mpr ⟨[],Language.nil_mem_kstar _,[34],⟨34,rfl,by omega,by omega⟩,rfl⟩
  | item unit notClose item encoded tail ih =>
    obtain ⟨head,headSpan,headLegal⟩ := item_source item
    obtain ⟨rest,restSpan,restLegal⟩ := ih
    exact ⟨head++rest,span_append headSpan restSpan,body_language_cons head rest headLegal restLegal⟩

/-- Successful decoded payloads retain an actual source segment in the previously
    verified complete Functional Syntax quoted-string terminal language. -/
theorem quoted_token_source {bs : List U8} {start stop : Usize} {payload : List U8}
    (token : QuotedToken bs start payload stop) :
    Rowl.Longest.Candidate bs start.val (Rowl.Functional.TerminalLanguage .QuotedString) stop.val := by
  obtain ⟨next,opening,body⟩ := token
  obtain ⟨word,span,legal⟩ := body_source body
  refine ⟨34::word,unit_cons opening span,?_⟩
  exact Language.mem_mul.mpr ⟨[34],⟨34,rfl,by omega,by omega⟩,word,legal,rfl⟩
private theorem span_head (bytes : alloc.vec.Vec U8) (start : Usize) (finish cp : Nat) (tail : List Nat)
    (span : Rowl.Longest.Utf8Span bytes.val start.val finish (cp::tail)) :
    ∃ value next, UnitAt bytes.val start.val value next ∧ value.val = cp ∧
      Rowl.Longest.Utf8Span bytes.val next.val finish tail := by
  cases span with
  | @character _ _ width _ _ unitPrefix positive fits rest =>
    obtain ⟨result,executed,correct⟩ := decode_next_total_correct bytes start
    cases result with
    | End => have eof : start.val = bytes.val.length := correct; omega
    | Error error =>
      cases error with
      | InvalidPosition offset => have := correct.2; omega
      | InvalidUtf8 offset =>
        have invalid := correct.2.2
        rw [unitPrefix] at invalid
        contradiction
      | NonXmlCharacter _ _ => exact False.elim correct
    | Scalar value next =>
      obtain ⟨advanced,bounded,unit⟩ := correct
      have same := Prod.mk.inj (Option.some.inj (unitPrefix.symm.trans unit))
      have endpoint : next.val = start.val + width := by omega
      exact ⟨value,next,⟨advanced,bounded,unit⟩,same.1.symm,by simpa [endpoint] using rest⟩

private theorem span_empty {bs : List U8} {start finish : Nat}
    (span : Rowl.Longest.Utf8Span bs start finish []) : start = finish := by
  cases span with
  | empty bound => rfl

private theorem body_prepend {bs : List U8} {start next finish stop : Usize} {cp value : U32} {payload : List U8}
    (unit : UnitAt bs start.val cp next) (notClose : cp ≠ 34#u32)
    (item : QuotedItem bs start.val value finish) (tail : QuotedBody bs finish payload stop) :
    ∃ output, QuotedBody bs start output stop := by
  obtain ⟨encoded,executed,correct⟩ := Rowl.Encoding.encode_total_correct value
  cases encoded with
  | none => exact False.elim (correct (quoted_item_progress item).1)
  | some encoded => exact ⟨Rowl.Encoding.Bytes encoded ++ payload,QuotedBody.item unit notClose item correct tail⟩

private theorem range_word {word : List Nat} {cp : Nat} (member : word ∈ Rowl.Iri.Range cp cp) : word = [cp] := by
  obtain ⟨value,rfl,lower,upper⟩ := member
  have : value = cp := by omega
  simp [this]

private theorem marker_word {word : List Nat}
    (member : word ∈ Rowl.Iri.Range 34 34 + Rowl.Iri.Range 92 92) :
    ∃ cp, word = [cp] ∧ EscapeMarker cp := by
  rcases member with quote | slash
  · exact ⟨34,range_word quote,Or.inl rfl⟩
  · exact ⟨92,range_word slash,Or.inr rfl⟩

private theorem body_from_parts (bytes : alloc.vec.Vec U8) (parts : List (List Nat)) (start stop : Usize)
    (members : ∀ word ∈ parts, word ∈ Rowl.Functional.QuotedBody)
    (span : Rowl.Longest.Utf8Span bytes.val start.val stop.val (parts.flatten ++ [34])) :
    ∃ payload, QuotedBody bytes.val start payload stop := by
  induction parts generalizing start with
  | nil =>
    obtain ⟨cp,next,unit,equal,rest⟩ := span_head bytes start stop.val 34 [] (by simpa using span)
    have cpEqual : cp = 34#u32 := by simpa [UScalar.eq_equiv] using equal
    have nextEqual : next = stop := UScalar.eq_of_val_eq (span_empty rest)
    subst cp
    subst next
    exact ⟨[],QuotedBody.close unit⟩
  | cons part parts ih =>
    have head : part ∈ Rowl.Functional.QuotedBody := members part (by simp)
    have remaining : ∀ word ∈ parts, word ∈ Rowl.Functional.QuotedBody := by
      intro word member
      exact members word (by simp [member])
    rcases head with raw | escaped
    · obtain ⟨sourceCp,rfl,xml,notQuote,notSlash⟩ := raw
      obtain ⟨cp,next,unit,equal,rest⟩ := span_head bytes start stop.val sourceCp (parts.flatten ++ [34]) (by simpa using span)
      have allowed : RawAllowed cp.val := by simpa [RawAllowed,equal] using And.intro xml (And.intro notQuote notSlash)
      have notClose : cp ≠ 34#u32 := by simpa [UScalar.eq_equiv] using allowed.2.1
      obtain ⟨payload,tail⟩ := ih next remaining rest
      exact body_prepend unit notClose (QuotedItem.raw unit allowed) tail
    · obtain ⟨slash,slashLegal,marker,markerLegal,word⟩ := Language.mem_mul.mp escaped
      have slashWord := range_word slashLegal
      obtain ⟨sourceCp,markerWord,allowed⟩ := marker_word markerLegal
      subst slash
      subst marker
      have partWord : part = [92,sourceCp] := word.symm
      rw [partWord] at span
      obtain ⟨cp,next,unit,cpValue,rest⟩ := span_head bytes start stop.val 92 (sourceCp::(parts.flatten ++ [34])) (by simpa using span)
      have cpEqual : cp = 92#u32 := by simpa [UScalar.eq_equiv] using cpValue
      subst cp
      obtain ⟨value,finish,markerUnit,markerValue,tailSpan⟩ := span_head bytes next stop.val sourceCp (parts.flatten ++ [34]) rest
      have markerAllowed : EscapeMarker value.val := by simpa [markerValue] using allowed
      obtain ⟨payload,tail⟩ := ih finish remaining tailSpan
      exact body_prepend unit (by decide) (QuotedItem.escaped unit ⟨markerUnit,markerAllowed⟩) tail

private theorem body_from_language (bytes : alloc.vec.Vec U8) (start stop : Usize) (word : List Nat)
    (span : Rowl.Longest.Utf8Span bytes.val start.val stop.val word)
    (legal : word ∈ Rowl.Functional.QuotedBody∗ * Rowl.Iri.Range 34 34) :
    ∃ payload, QuotedBody bytes.val start payload stop := by
  obtain ⟨body,bodyLegal,closing,closingLegal,rfl⟩ := Language.mem_mul.mp legal
  obtain ⟨parts,rfl,members⟩ := Language.mem_kstar.mp bodyLegal
  have closingWord := range_word closingLegal
  subst closing
  exact body_from_parts bytes parts start stop members span

/-- The byte-segment terminal grammar and the independent decoded-payload
    grammar describe exactly the same source strings in both directions. -/
theorem quoted_token_source_iff (bytes : alloc.vec.Vec U8) (start stop : Usize) :
    Rowl.Longest.Candidate bytes.val start.val (Rowl.Functional.TerminalLanguage .QuotedString) stop.val ↔
      ∃ payload, QuotedToken bytes.val start payload stop := by
  constructor
  · rintro ⟨word,span,legal⟩
    obtain ⟨opening,openingLegal,body,bodyLegal,rfl⟩ := Language.mem_mul.mp legal
    have openingWord := range_word openingLegal
    subst opening
    obtain ⟨cp,next,unit,equal,rest⟩ := span_head bytes start stop.val 34 body span
    have cpEqual : cp = 34#u32 := by simpa [UScalar.eq_equiv] using equal
    subst cp
    obtain ⟨payload,decoded⟩ := body_from_language bytes next stop body rest bodyLegal
    exact ⟨payload,next,unit,decoded⟩
  · rintro ⟨payload,token⟩
    exact quoted_token_source token

/-- Every recognized source segment has its decoded payload; a fitting caller
    byte budget is sufficient for the actual reader to return that exact value. -/
theorem read_quoted_source_complete (bytes : alloc.vec.Vec U8) (start stop limit : Usize)
    (source : Rowl.Longest.Candidate bytes.val start.val (Rowl.Functional.TerminalLanguage .QuotedString) stop.val) :
    ∃ payload, QuotedToken bytes.val start payload stop ∧
      (payload.length ≤ limit.val → ∃ output, read_quoted bytes start limit = .ok (.Ok (output,stop)) ∧ output.val = payload) := by
  obtain ⟨payload,token⟩ := (quoted_token_source_iff bytes start stop).mp source
  refine ⟨payload,token,?_⟩
  intro fits
  have bounded : payload.length ≤ Usize.max := by scalar_tac
  let output : alloc.vec.Vec U8 := .from payload bounded
  have value : output.val = payload := by simp [output]
  exact ⟨output,(read_quoted_accepted_iff bytes start stop limit output).mpr
    ⟨by simpa [value] using token,by simpa [value] using fits⟩,value⟩
private theorem required_error_excludes_unit {bs : List U8} {start : Nat} {error : ReadError}
    {cp : U32} {next : Usize} (failure : RequiredError bs start error)
    (unit : UnitAt bs start cp next) : False := by
  rcases failure with bad | ⟨_,_,eof⟩
  · rcases bad.2.2 with outside | ⟨_,invalid⟩
    · have := unit.1; have := unit.2.1; omega
    · rw [unit.2.2] at invalid; contradiction
  · have := unit.1; have := unit.2.1; omega
private theorem required_error_unique {bs : List U8} {start : Nat} {one two : ReadError}
    (first : RequiredError bs start one) (second : RequiredError bs start two) : one = two := by
  have fields : one.kind = two.kind ∧ one.offset = two.offset := by
    rcases first with bad | ⟨kind,offset,eof⟩ <;>
      rcases second with other | ⟨otherKind,otherOffset,otherEof⟩
    · exact ⟨bad.1.trans other.1.symm,UScalar.eq_of_val_eq (bad.2.1.trans other.2.1.symm)⟩
    · rcases bad.2.2 with outside | ⟨inside,_⟩ <;> omega
    · rcases other.2.2 with outside | ⟨inside,_⟩ <;> omega
    · exact ⟨kind.trans otherKind.symm,UScalar.eq_of_val_eq (offset.trans otherOffset.symm)⟩
  cases one; cases two; simp_all
private theorem required_error_actual {bytes : alloc.vec.Vec U8} {position : Usize} {error : ReadError}
    (failure : RequiredError bytes.val position.val error) :
    ntriples.required bytes position = .ok (.Err error) := by
  obtain ⟨result,executed,correct⟩ := required_total_correct bytes position
  cases result with
  | Ok pair => exact False.elim (required_error_excludes_unit failure correct)
  | Err other => have same := required_error_unique correct failure; simpa [same] using executed
private theorem expect_error_actual {bytes : alloc.vec.Vec U8} {position : Usize} {error : ReadError}
    (failure : ExpectCorrect bytes.val position.val 34#u32 .InvalidCharacter (.Err error)) :
    ntriples.expect bytes position 34#u32 .InvalidCharacter = .ok (.Err error) := by
  rcases failure with requiredFailure | ⟨kind,offset,cp,next,unit,different⟩
  · simp [ntriples.expect,required_error_actual requiredFailure,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  · have errorValue : error = ⟨.InvalidCharacter,position⟩ := by
      have offsetEqual := UScalar.eq_of_val_eq offset
      cases error; simp_all
    simp [ntriples.expect,required_actual unit,core.result.Result.Insts.CoreOpsTry.branch,
      different,ntriples.error,errorValue]
private theorem escape_error_actual {bytes : alloc.vec.Vec U8} {slash position : Usize} {error : ReadError}
    (failure : EscapeError bytes.val slash position.val error) :
    escape bytes slash position = .ok (.Err error) := by
  cases failure with
  | required failure =>
    simp [escape,required_error_actual failure,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | marker unit invalid =>
    simp [escape,required_actual unit,core.result.Result.Insts.CoreOpsTry.branch,
      EscapeMarker,UScalar.eq_equiv,functional_payload.error] at *
    simp_all
private theorem item_error_actual {bytes : alloc.vec.Vec U8} {position : Usize}
    {cp : U32} {next : Usize} {error : ReadError} (unit : UnitAt bytes.val position.val cp next)
    (failure : ItemError bytes.val position error) :
    quoted_item bytes position cp next = .ok (.Err error) := by
  cases failure with
  | raw other noSlash invalid =>
    obtain ⟨rfl,rfl⟩ := unit_unique unit other
    have noSlashValue : cp.val ≠ 92 := by simpa [UScalar.eq_equiv] using noSlash
    have bad : cp = 34#u32 ∨ ¬ XmlChar cp.val := by
      by_cases quote : cp.val = 34
      · exact Or.inl (by simpa [UScalar.eq_equiv] using quote)
      · exact Or.inr (fun xml => invalid ⟨xml,quote,noSlashValue⟩)
    rcases bad with bad | bad <;>
      simp [quoted_item,noSlash,bad,xml_character_total_correct,functional_payload.error]
  | escaped other failure =>
    obtain ⟨rfl,rfl⟩ := unit_unique unit other
    simp [quoted_item,escape_error_actual failure]
private theorem body_error_actual {bytes : alloc.vec.Vec U8} {limit : Usize}
    {before : Nat} {position : Usize} {error : ReadError}
    (failure : BodyError bytes.val limit.val before position error) :
    ∀ output : alloc.vec.Vec U8, output.val.length = before → before ≤ limit.val →
      read_quoted_loop bytes limit position output = .ok (.Err error) := by
  induction failure with
  | required failure =>
    intro output _ _
    rw [read_quoted_loop]
    simp [required_error_actual failure,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
  | item unit notClose failure =>
    intro output _ _
    rw [read_quoted_loop]
    simp [required_actual unit,core.result.Result.Insts.CoreOpsTry.branch,notClose,
      item_error_actual unit failure,same_residual]
  | @limit before start cp next value finish encoded unit notClose item encodingCorrect tooLarge =>
    intro output size bounded
    obtain ⟨accepted,after,appendUnit,appendCorrect⟩ := append_encoded_total_correct output encoded limit (by omega)
    have acceptedFalse : accepted = false := by
      have notFits : ¬ output.val.length + (Rowl.Encoding.Bytes encoded).length ≤ limit.val := by omega
      simpa [notFits] using appendCorrect.1
    subst accepted
    rw [read_quoted_loop]
    simp [required_actual unit,core.result.Result.Insts.CoreOpsTry.branch,notClose,
      quoted_item_actual unit item,(Rowl.Encoding.encode_some_iff _ _).mpr encodingCorrect,
      appendUnit,functional_payload.error]
  | @afterItem before start cp next value finish encoded error unit notClose item encodingCorrect fits tail ih =>
    intro output size bounded
    obtain ⟨accepted,after,appendUnit,appendCorrect⟩ := append_encoded_total_correct output encoded limit (by omega)
    have acceptedTrue : accepted = true := by simpa [size,fits] using appendCorrect.1
    subst accepted
    obtain ⟨_,contents,afterBound⟩ := append_success appendCorrect
    have afterSize : after.val.length = before + (Rowl.Encoding.Bytes encoded).length := by simp [contents,size]
    have executed := ih after afterSize fits
    rw [read_quoted_loop]
    simp [required_actual unit,core.result.Result.Insts.CoreOpsTry.branch,notClose,
      quoted_item_actual unit item,(Rowl.Encoding.encode_some_iff _ _).mpr encodingCorrect,appendUnit,executed]

/-- Every first quoted-string error occurs if and only if its independent
    original-source diagnostic derivation holds, including bounded-output errors. -/
theorem read_quoted_error_iff (bytes : alloc.vec.Vec U8) (start limit : Usize) (error : ReadError) :
    read_quoted bytes start limit = .ok (.Err error) ↔ QuotedError bytes.val start limit.val error := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_quoted_total_correct bytes start limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same,QuotedCorrect] using correct
  · intro failure
    cases failure with
    | opening failure =>
      simp [read_quoted,expect_error_actual failure,core.result.Result.Insts.CoreOpsTry.branch,same_residual]
    | body opening failure =>
      have executed := body_error_actual failure (alloc.vec.Vec.new U8) (by simp) (by omega)
      simp [read_quoted,expect_actual opening,core.result.Result.Insts.CoreOpsTry.branch,executed]
end Rowl.FunctionalPayload
