import Rowl.FunctionalNames

namespace Rowl.FunctionalIriParts
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.functional_iris
open Rowl.Names Rowl.NTriples Rowl.Unicode RowlRust.unicode
open scoped Computability
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- Independent grammatical partition of the complete original token copy.
    The prefix ends at the syntax colon and both returned byte fields are exact. -/
def Partition (raw : List U8) (parts : AbbreviatedParts) : Prop :=
  ∃ cut bodyWord localWord,
    bodyWord ∈ (1 + PrefixWord) ∧ localWord ∈ Local ∧
    Rowl.Longest.Utf8Span raw 0 cut (bodyWord ++ [58]) ∧
    Rowl.Longest.Utf8Span raw cut raw.length localWord ∧
    parts.prefix.val = Rowl.SourceSpans.Bytes raw 0 cut ∧
    parts.local.val = Rowl.SourceSpans.Bytes raw cut raw.length
/-- The accepted original source span and its source-derived lexical parts. -/
def PartsValue (source : List U8) (start finish : Nat) (parts : AbbreviatedParts) : Prop :=
  Rowl.FunctionalNames.Token .AbbreviatedIri source start finish ∧
    Partition (Rowl.SourceSpans.Bytes source start finish) parts
/-- Complete source rejection phases. Internal splitting fallbacks are impossible. -/
def SplitError (source : List U8) (start finish : Nat) : SourceIriError → Prop
  | .Name (.InvalidSpan offset) => offset.val = start ∧ (finish < start ∨ source.length < finish)
  | .Name (.InvalidToken offset) => offset.val = start ∧ start ≤ finish ∧ finish ≤ source.length ∧
      ¬ Rowl.FunctionalNames.Token .AbbreviatedIri source start finish
  | _ => False
/-- Actual splitting is total, exact on success, and has only source-input errors. -/
def SplitCorrect (source : List U8) (start finish : Nat) :
    core.result.Result AbbreviatedParts SourceIriError → Prop
  | .Ok parts => PartsValue source start finish parts
  | .Err error => SplitError source start finish error

private theorem bounds {bs : List U8} {start finish : Nat} {word : List Nat}
    (span : Rowl.Longest.Utf8Span bs start finish word) : start ≤ finish ∧ finish ≤ bs.length := by
  induction span with
  | empty bounded => exact ⟨le_rfl,bounded⟩
  | character _ positive _ _ ih => constructor <;> omega
private theorem all_mul (a b : Language Nat) (predicate : Nat → Prop)
    (first : ∀ word ∈ a, ∀ cp ∈ word, predicate cp)
    (second : ∀ word ∈ b, ∀ cp ∈ word, predicate cp) :
    ∀ word ∈ a*b, ∀ cp ∈ word, predicate cp := by
  rintro word ⟨left,leftLegal,right,rightLegal,rfl⟩ cp member
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact first left leftLegal cp leftMember
  · exact second right rightLegal cp rightMember
private theorem all_star (a : Language Nat) (predicate : Nat → Prop)
    (part : ∀ word ∈ a, ∀ cp ∈ word, predicate cp) : ∀ word ∈ a∗, ∀ cp ∈ word, predicate cp := by
  rintro word ⟨parts,rfl,legal⟩ cp member
  obtain ⟨item,included,contained⟩ := List.mem_flatten.mp member
  exact part item (legal item included) cp contained
private theorem chars_no_colon : ∀ word ∈ Chars, ∀ cp ∈ word, cp ≠ 58 := by
  intro word legal cp member
  simp only [Chars,CharsU,Language.mem_add] at legal
  rcases legal with ((base | underscore) | (dash | (digit | (middle | (combining | connector)))))
  · obtain ⟨value,rfl,base⟩ := base
    have same : cp = value := by simpa using member
    subst cp
    simp only [BaseCode] at base
    omega
  all_goals
    obtain ⟨value,rfl,lower,upper⟩ := ‹word ∈ Rowl.Iri.Range _ _›
    have same : cp = value := by simpa using member
    subst cp
    omega
private theorem ending_no_colon : ∀ word ∈ Ending, ∀ cp ∈ word, cp ≠ 58 := by
  intro word legal cp member
  rcases (Language.mem_add _ _ word).mp legal with empty | ending
  · have same : word = [] := empty
    simp [same] at member
  · apply all_mul _ _ (fun value => value ≠ 58) ?_ chars_no_colon word ending cp member
    apply all_star
    intro word legal cp member
    rcases (Language.mem_add _ _ word).mp legal with nameChars | dot
    · exact chars_no_colon word nameChars cp member
    · obtain ⟨value,rfl,lower,upper⟩ := dot
      have same : cp = value := by simpa using member
      subst cp
      omega
private theorem body_no_colon : ∀ word ∈ (1 + PrefixWord), ∀ cp ∈ word, cp ≠ 58 := by
  intro word legal cp member
  rcases (Language.mem_add _ _ word).mp legal with empty | named
  · have same : word = [] := empty
    simp [same] at member
  · apply all_mul _ _ (fun value => value ≠ 58) ?_ ending_no_colon word named cp member
    intro word base cp member
    obtain ⟨value,rfl,legal⟩ := base
    have same : cp = value := by simpa using member
    subst cp
    simp only [BaseCode] at legal
    omega
private theorem range_word {word : List Nat} {cp : Nat}
    (member : word ∈ Rowl.Iri.Range cp cp) : word = [cp] := by
  obtain ⟨value,rfl,lower,upper⟩ := member
  have same : value = cp := by omega
  simp [same]
private theorem span_head (bytes : alloc.vec.Vec U8) (start : Usize) (finish cp : Nat) (tail : List Nat)
    (span : Rowl.Longest.Utf8Span bytes.val start.val finish (cp::tail)) :
    ∃ value next, decode_next bytes start = .ok (.Scalar value next) ∧
      UnitAt bytes.val start.val value next ∧ value.val = cp ∧
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
      exact ⟨value,next,executed,⟨advanced,bounded,unit⟩,same.1.symm,by simpa [endpoint] using rest⟩
private theorem span_cons {bs : List U8} {start : Nat} {cp : U32} {next : Usize}
    {finish : Nat} {tail : List Nat} (unit : UnitAt bs start cp next)
    (rest : Rowl.Longest.Utf8Span bs next.val finish tail) :
    Rowl.Longest.Utf8Span bs start finish (cp.val::tail) := by
  obtain ⟨advanced,bounded,decoded⟩ := unit
  have equal : start+(next.val-start) = next.val := by omega
  rw [← equal] at rest
  exact .character decoded (by omega) (by omega) rest
private theorem span_empty {bs : List U8} {start finish : Nat}
    (span : Rowl.Longest.Utf8Span bs start finish []) : start = finish := by
  cases span with
  | empty _ => rfl

private theorem colon_on_prefix (bytes : alloc.vec.Vec U8) (position : Usize) (finish : Nat)
    (bodyWord localWord : List Nat)
    (span : Rowl.Longest.Utf8Span bytes.val position.val finish (bodyWord++58::localWord))
    (noColon : ∀ cp ∈ bodyWord, cp ≠ 58) :
    ∃ separator, colon_from bytes position = .ok (some separator) ∧
      Rowl.Longest.Utf8Span bytes.val position.val separator.val (bodyWord++[58]) ∧
      Rowl.Longest.Utf8Span bytes.val separator.val finish localWord := by
  induction bodyWord generalizing position with
  | nil =>
    obtain ⟨cp,next,executed,unit,same,rest⟩ := span_head bytes position finish 58 localWord span
    have cpEq : cp = 58#u32 := UScalar.eq_of_val_eq (by simpa using same)
    refine ⟨next,?_,?_,rest⟩
    · rw [colon_from,executed,bind_ok]
      simp only [cpEq,↓reduceIte]
    · simpa [same] using span_cons unit (Rowl.Longest.Utf8Span.empty unit.2.1)
  | cons head tail ih =>
    obtain ⟨cp,next,executed,unit,same,rest⟩ := span_head bytes position finish head (tail++58::localWord) span
    have notColon : cp ≠ 58#u32 := by intro equal; have := noColon head (by simp); simp [equal] at same; omega
    obtain ⟨separator,found,headSpan,tailSpan⟩ := ih next rest (by intro value member; exact noColon value (by simp [member]))
    refine ⟨separator,?_,?_,tailSpan⟩
    · rw [colon_from,executed,bind_ok]
      simpa only [notColon,↓reduceIte] using found
    · simpa [same] using span_cons unit headSpan

/-- Every independent partition obeys the complete prefix and local grammars,
    and concatenating its exact byte fields restores the original token copy. -/
theorem partition_values {raw : List U8} {parts : AbbreviatedParts} (partition : Partition raw parts) :
    Rowl.Prefixes.PrefixAccepted parts.prefix.val ∧ Rowl.Prefixes.LocalAccepted parts.local.val ∧
      parts.prefix.val++parts.local.val = raw := by
  obtain ⟨cut,bodyWord,localWord,bodyLegal,localLegal,headSpan,tailSpan,headBytes,tailBytes⟩ := partition
  have headText := (Rowl.SourceSpans.utf8_source_iff raw 0 cut _ (bounds headSpan)).mp headSpan
  have tailText := (Rowl.SourceSpans.utf8_source_iff raw cut raw.length _ (bounds tailSpan)).mp tailSpan
  refine ⟨⟨bodyWord++[58],?_,?_⟩,⟨localWord,?_,localLegal⟩,?_⟩
  · simpa [headBytes] using headText
  · exact Language.mem_mul.mpr ⟨bodyWord,bodyLegal,[58],⟨58,rfl,le_rfl,le_rfl⟩,rfl⟩
  · simpa [tailBytes] using tailText
  · have range := bounds headSpan
    rw [headBytes,tailBytes]
    simp only [Rowl.SourceSpans.Bytes,List.drop_zero,Nat.sub_zero]
    rw [show raw.length-cut = (raw.drop cut).length by simp,List.take_length]
    exact List.take_append_drop cut raw

private theorem split_token (raw : alloc.vec.Vec U8)
    (grammar : ∃ word, Rowl.Regular.Utf8From raw.val 0 word ∧ word ∈ Abbreviated) :
    ∃ separator prefixBytes localBytes,
      colon_from raw 0#usize = .ok (some separator) ∧
      ntriples.copy_term raw 0#usize separator raw.len = .ok (.Ok prefixBytes) ∧
      ntriples.copy_term raw separator raw.len raw.len = .ok (.Ok localBytes) ∧
      Partition raw.val ⟨prefixBytes,localBytes⟩ := by
  obtain ⟨word,text,legal⟩ := grammar
  obtain ⟨prefixWord,prefixLegal,localWord,localLegal,rfl⟩ := Language.mem_mul.mp legal
  obtain ⟨bodyWord,bodyLegal,colonWord,colonLegal,rfl⟩ := Language.mem_mul.mp prefixLegal
  rw [range_word colonLegal] at text
  have span : Rowl.Longest.Utf8Span raw.val 0 raw.val.length (bodyWord++58::localWord) := by
    apply (Rowl.SourceSpans.utf8_source_iff raw.val 0 raw.val.length _ (by simp)).mpr
    simpa [Rowl.SourceSpans.Bytes,List.append_assoc] using text
  obtain ⟨separator,found,headSpan,tailSpan⟩ := colon_on_prefix raw 0#usize raw.val.length bodyWord localWord span
    (body_no_colon bodyWord bodyLegal)
  have cutBound := bounds headSpan
  obtain ⟨left,leftRead,leftCorrect⟩ := copy_term_total_correct raw 0#usize separator raw.len (by simpa using cutBound)
  obtain ⟨right,rightRead,rightCorrect⟩ := copy_term_total_correct raw separator raw.len raw.len (by simp [alloc.vec.Vec.len_val]; omega)
  cases left with
  | Err error => have tooSmall := leftCorrect.1; simp [alloc.vec.Vec.len_val] at tooSmall; omega
  | Ok prefixBytes =>
    cases right with
    | Err error => have tooSmall := rightCorrect.1; simp [alloc.vec.Vec.len_val] at tooSmall; omega
    | Ok localBytes =>
      refine ⟨separator,prefixBytes,localBytes,found,leftRead,rightRead,separator.val,bodyWord,localWord,bodyLegal,localLegal,headSpan,tailSpan,?_,?_⟩
      · simpa [Rowl.SourceSpans.Bytes] using leftCorrect.2
      · simpa [Rowl.SourceSpans.Bytes,alloc.vec.Vec.len_val] using rightCorrect.2

/-- Actual byte-derived splitting terminates for every input. Successful tokens
    have the unique grammatical partition; all internal fallback errors are absent. -/
theorem split_abbreviated_total_correct (bytes : alloc.vec.Vec U8) (start finish : Usize) :
    ∃ result, split_abbreviated bytes start finish = .ok result ∧
      SplitCorrect bytes.val start.val finish.val result := by
  rw [split_abbreviated]
  by_cases reversed : finish.val < start.val
  · exact ⟨.Err (.Name (.InvalidSpan start)),by simp [UScalar.lt_equiv,reversed],rfl,Or.inl reversed⟩
  · simp only [UScalar.lt_equiv,reversed,↓reduceIte]
    by_cases beyond : bytes.val.length < finish.val
    · exact ⟨.Err (.Name (.InvalidSpan start)),by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,beyond],rfl,Or.inr beyond⟩
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,beyond,↓reduceIte]
      have range : start.val ≤ finish.val ∧ finish.val ≤ bytes.val.length := by omega
      obtain ⟨count,countRead,countCorrect⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := finish) (y := start) (by scalar_tac))
      have countValue : count.val = finish.val-start.val := countCorrect.1
      obtain ⟨result,nameRead,nameCorrect⟩ := Rowl.FunctionalNames.read_span_total_correct .AbbreviatedIri bytes start finish count
      rw [countRead,bind_ok,nameRead,bind_ok]
      cases result with
      | Ok raw =>
        have grammar := Rowl.FunctionalNames.read_value_grammar .AbbreviatedIri bytes start finish count raw nameRead
        obtain ⟨separator,prefixBytes,localBytes,found,leftRead,rightRead,partition⟩ := split_token raw grammar
        refine ⟨.Ok ⟨prefixBytes,localBytes⟩,?_,nameCorrect.1,?_⟩
        · simp only [found,bind_ok,leftRead,rightRead]
        · have same : raw.val = Rowl.SourceSpans.Bytes bytes.val start.val finish.val := by
            simpa [Rowl.FunctionalNames.Payload,Rowl.FunctionalNames.Leading,Rowl.FunctionalNames.Trailing] using nameCorrect.2.2
          simpa [same] using partition
      | Err error =>
        cases error with
        | InvalidSpan offset => exact ⟨.Err (.Name (.InvalidSpan offset)),rfl,nameCorrect⟩
        | InvalidToken offset => exact ⟨.Err (.Name (.InvalidToken offset)),rfl,nameCorrect⟩
        | ResourceLimit offset =>
          have size : (Rowl.FunctionalNames.Payload .AbbreviatedIri bytes.val start.val finish.val).length = finish.val-start.val := by
            simp [Rowl.FunctionalNames.Payload,Rowl.FunctionalNames.Leading,Rowl.FunctionalNames.Trailing,Rowl.SourceSpans.Bytes]
            omega
          have tooSmall := nameCorrect.2.2
          rw [size,countValue] at tooSmall
          omega

private theorem excludes_error {source : List U8} {start finish : Nat}
    (token : Rowl.FunctionalNames.Token .AbbreviatedIri source start finish)
    (error : SourceIriError) (rejected : SplitError source start finish error) : False := by
  obtain ⟨word,span,_⟩ := token
  have range := bounds span
  cases error with
  | Name error =>
    cases error with
    | InvalidSpan offset => rcases rejected.2 with reversed | beyond <;> omega
    | InvalidToken offset => exact rejected.2.2.2 ⟨word,span,by assumption⟩
    | ResourceLimit _ => exact rejected
  | InvalidParts _ | UndeclaredPrefix _ | ResourceLimit _ | InvalidExpandedIri _ => exact rejected

/-- All and only complete standard abbreviated-IRI source spans are accepted;
    splitting has no final expanded-IRI budget and cannot reject a valid span. -/
theorem split_abbreviated_accepts_iff (bytes : alloc.vec.Vec U8) (start finish : Usize) :
    (∃ parts, split_abbreviated bytes start finish = .ok (.Ok parts)) ↔
      Rowl.FunctionalNames.Token .AbbreviatedIri bytes.val start.val finish.val := by
  obtain ⟨result,executed,correct⟩ := split_abbreviated_total_correct bytes start finish
  constructor
  · rintro ⟨parts,accepted⟩
    have same := Result.ok_injective (executed.symm.trans accepted)
    subst result
    exact correct.1
  · intro token
    cases result with
    | Ok parts => exact ⟨parts,executed⟩
    | Err error => exact False.elim (excludes_error token error correct)

/-- Exact actual prefix/local values retain their original spelling and satisfy
    the independent complete standard name grammars. -/
theorem split_source_values (bytes : alloc.vec.Vec U8) (start finish : Usize) (parts : AbbreviatedParts)
    (accepted : split_abbreviated bytes start finish = .ok (.Ok parts)) :
    PartsValue bytes.val start.val finish.val parts ∧
      Rowl.Prefixes.PrefixAccepted parts.prefix.val ∧ Rowl.Prefixes.LocalAccepted parts.local.val ∧
      parts.prefix.val++parts.local.val = Rowl.SourceSpans.Bytes bytes.val start.val finish.val := by
  obtain ⟨result,executed,correct⟩ := split_abbreviated_total_correct bytes start finish
  have same := Result.ok_injective (executed.symm.trans accepted)
  subst result
  exact ⟨correct,partition_values correct.2⟩

private theorem partition_unique (raw : alloc.vec.Vec U8) (one two : AbbreviatedParts)
    (first : Partition raw.val one) (second : Partition raw.val two) : one = two := by
  obtain ⟨cut,bodyWord,localWord,bodyLegal,localLegal,headSpan,tailSpan,headBytes,tailBytes⟩ := first
  obtain ⟨otherCut,otherBody,otherLocal,otherBodyLegal,otherLocalLegal,otherHead,otherTail,otherHeadBytes,otherTailBytes⟩ := second
  obtain ⟨separator,found,_,ending⟩ := colon_on_prefix raw 0#usize cut bodyWord [] headSpan
    (body_no_colon bodyWord bodyLegal)
  obtain ⟨otherSeparator,otherFound,_,otherEnding⟩ := colon_on_prefix raw 0#usize otherCut otherBody [] otherHead
    (body_no_colon otherBody otherBodyLegal)
  have same : separator = otherSeparator := Option.some.inj (Result.ok_injective (found.symm.trans otherFound))
  have cutSame : cut = otherCut := by
    have := span_empty ending
    have := span_empty otherEnding
    rw [same] at *
    omega
  have prefixSame : one.prefix = two.prefix := (alloc.vec.Vec.eq_iff _ _).mpr (by rw [headBytes,otherHeadBytes,cutSame])
  have localSame : one.local = two.local := (alloc.vec.Vec.eq_iff _ _).mpr (by rw [tailBytes,otherTailBytes,cutSame])
  cases one
  cases two
  cases prefixSame
  cases localSame
  rfl

/-- The independent source contract uniquely determines both returned byte
    fields. No alternative prefix/local partition can change expansion semantics. -/
theorem parts_value_unique (bytes : alloc.vec.Vec U8) (start finish : Usize) (one two : AbbreviatedParts)
    (first : PartsValue bytes.val start.val finish.val one)
    (second : PartsValue bytes.val start.val finish.val two) : one = two := by
  obtain ⟨word,span,_⟩ := first.1
  have range := bounds span
  have size : (Rowl.SourceSpans.Bytes bytes.val start.val finish.val).length ≤ bytes.val.length := by
    simp [Rowl.SourceSpans.Bytes]
  let raw := alloc.vec.Vec.from (Rowl.SourceSpans.Bytes bytes.val start.val finish.val) (size.trans bytes.property)
  exact partition_unique raw one two (by simpa [raw] using first.2) (by simpa [raw] using second.2)

private theorem split_error_unique (source : List U8) (start finish : Nat) (one two : SourceIriError)
    (first : SplitError source start finish one) (second : SplitError source start finish two) : one = two := by
  cases one with
  | Name one =>
    cases two with
    | Name two =>
      cases one with
      | InvalidSpan offset =>
        cases two with
        | InvalidSpan other => have same := UScalar.eq_of_val_eq (first.1.trans second.1.symm); simp [same]
        | InvalidToken other => rcases first.2 with reversed | beyond <;> have := second.2.1 <;> have := second.2.2.1 <;> omega
        | ResourceLimit _ => exact False.elim second
      | InvalidToken offset =>
        cases two with
        | InvalidSpan other => rcases second.2 with reversed | beyond <;> have := first.2.1 <;> have := first.2.2.1 <;> omega
        | InvalidToken other => have same := UScalar.eq_of_val_eq (first.1.trans second.1.symm); simp [same]
        | ResourceLimit _ => exact False.elim second
      | ResourceLimit _ => exact False.elim first
    | InvalidParts _ | UndeclaredPrefix _ | ResourceLimit _ | InvalidExpandedIri _ => exact False.elim second
  | InvalidParts _ | UndeclaredPrefix _ | ResourceLimit _ | InvalidExpandedIri _ => exact False.elim first

/-- Every source error predicate and original diagnostic offset holds exactly
    when the actual splitter returns that error, in both directions. -/
theorem split_abbreviated_error_iff (bytes : alloc.vec.Vec U8) (start finish : Usize) (error : SourceIriError) :
    split_abbreviated bytes start finish = .ok (.Err error) ↔ SplitError bytes.val start.val finish.val error := by
  obtain ⟨result,executed,correct⟩ := split_abbreviated_total_correct bytes start finish
  constructor
  · intro rejected
    have same := Result.ok_injective (executed.symm.trans rejected)
    subst result
    exact correct
  · intro sourceError
    cases result with
    | Ok parts => exact False.elim (excludes_error correct.1 error sourceError)
    | Err actual =>
      have same := split_error_unique _ _ _ actual error correct sourceError
      simpa [same] using executed

/-- Exact successful parts are equivalent to the independent source partition,
    not merely to an existential acceptance predicate. -/
theorem split_abbreviated_value_iff (bytes : alloc.vec.Vec U8) (start finish : Usize) (parts : AbbreviatedParts) :
    split_abbreviated bytes start finish = .ok (.Ok parts) ↔ PartsValue bytes.val start.val finish.val parts := by
  constructor
  · intro accepted
    exact (split_source_values bytes start finish parts accepted).1
  · intro source
    obtain ⟨actual,accepted⟩ := (split_abbreviated_accepts_iff bytes start finish).mpr source.1
    have same := parts_value_unique bytes start finish actual parts (split_source_values bytes start finish actual accepted).1 source
    simpa [same] using accepted

end Rowl.FunctionalIriParts
