import Rowl.Longest

namespace Rowl.SourceSpans
open Aeneas Aeneas.Std RowlRust
open Rowl.Unicode Rowl.Longest
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- Exact unchanged source bytes between bounded original endpoints. -/
def Bytes (source : List U8) (start finish : Nat) : List U8 :=
  (source.drop start).take (finish-start)

private theorem prefix_transfer {one two : List U8} {start position cp width : Nat}
    (unit : Prefix one start = some (cp,width))
    (same : ∀ k, k < width → one[start+k]? = two[position+k]?) :
    Prefix two position = some (cp,width) := by
  unfold Prefix at unit
  cases first : one[start]? with
  | none => simp [first,Option.bind_eq_bind] at unit
  | some a =>
    simp only [first,Option.bind_eq_bind,Option.bind_some] at unit
    by_cases small : a.val < 128
    · simp only [small,↓reduceIte] at unit
      have values := Prod.mk.inj (Option.some.inj unit)
      have widthIs : width = 1 := values.2.symm
      have otherFirst : two[position]? = some a := by
        simpa using (same 0 (by omega)).symm.trans (by simpa using first)
      simpa [Prefix,otherFirst,small] using unit
    · simp only [small,↓reduceIte] at unit
      by_cases pairLead : a.val < 224
      · simp only [pairLead,↓reduceIte] at unit
        cases second : one[start+1]? with
        | none => simp [second,Option.bind_eq_bind] at unit
        | some b =>
          simp only [second,Option.bind_eq_bind,Option.bind_some] at unit
          by_cases legal : Pair a.val b.val
          · simp only [legal,↓reduceIte] at unit
            have values := Prod.mk.inj (Option.some.inj unit)
            have widthIs : width = 2 := values.2.symm
            have otherFirst : two[position]? = some a := by
              simpa using (same 0 (by omega)).symm.trans (by simpa using first)
            have otherSecond : two[position+1]? = some b := (same 1 (by omega)).symm.trans second
            simpa [Prefix,otherFirst,otherSecond,small,pairLead,legal] using unit
          · simp [legal] at unit
      · simp only [pairLead,↓reduceIte] at unit
        by_cases tripleLead : a.val < 240
        · simp only [tripleLead,↓reduceIte] at unit
          cases second : one[start+1]? with
          | none => simp [second,Option.bind_eq_bind] at unit
          | some b =>
            simp only [second,Option.bind_eq_bind,Option.bind_some] at unit
            cases third : one[start+2]? with
            | none => simp [third,Option.bind_eq_bind] at unit
            | some c =>
              simp only [third,Option.bind_eq_bind,Option.bind_some] at unit
              by_cases legal : Triple a.val b.val c.val
              · simp only [legal,↓reduceIte] at unit
                have values := Prod.mk.inj (Option.some.inj unit)
                have widthIs : width = 3 := values.2.symm
                have otherFirst : two[position]? = some a := by
                  simpa using (same 0 (by omega)).symm.trans (by simpa using first)
                have otherSecond : two[position+1]? = some b := (same 1 (by omega)).symm.trans second
                have otherThird : two[position+2]? = some c := (same 2 (by omega)).symm.trans third
                simpa [Prefix,otherFirst,otherSecond,otherThird,small,pairLead,tripleLead,legal] using unit
              · simp [legal] at unit
        · simp only [tripleLead,↓reduceIte] at unit
          cases second : one[start+1]? with
          | none => simp [second,Option.bind_eq_bind] at unit
          | some b =>
            simp only [second,Option.bind_eq_bind,Option.bind_some] at unit
            cases third : one[start+2]? with
            | none => simp [third,Option.bind_eq_bind] at unit
            | some c =>
              simp only [third,Option.bind_eq_bind,Option.bind_some] at unit
              cases fourth : one[start+3]? with
              | none => simp [fourth,Option.bind_eq_bind] at unit
              | some d =>
                simp only [fourth,Option.bind_eq_bind,Option.bind_some] at unit
                by_cases legal : Quad a.val b.val c.val d.val
                · simp only [legal,↓reduceIte] at unit
                  have values := Prod.mk.inj (Option.some.inj unit)
                  have widthIs : width = 4 := values.2.symm
                  have otherFirst : two[position]? = some a := by
                    simpa using (same 0 (by omega)).symm.trans (by simpa using first)
                  have otherSecond : two[position+1]? = some b := (same 1 (by omega)).symm.trans second
                  have otherThird : two[position+2]? = some c := (same 2 (by omega)).symm.trans third
                  have otherFourth : two[position+3]? = some d := (same 3 (by omega)).symm.trans fourth
                  simpa [Prefix,otherFirst,otherSecond,otherThird,otherFourth,small,pairLead,tripleLead,legal] using unit
                · simp [legal] at unit

private theorem bounds {bs : List U8} {start finish : Nat} {word : List Nat}
    (span : Utf8Span bs start finish word) : start ≤ finish ∧ finish ≤ bs.length := by
  induction span with
  | empty bounded => exact ⟨le_rfl,bounded⟩
  | character _ positive _ _ ih => constructor <;> omega
private theorem byte_lookup (source : List U8) (start finish index : Nat)
    (inside : index < finish-start) :
    (Bytes source start finish)[index]? = source[start+index]? := by
  simp only [Bytes,List.getElem?_take_of_lt inside,List.getElem?_drop]

/-- Copying a bounded source segment preserves every complete canonical UTF-8
    unit at its rebased offset; an interior split unit cannot justify this law. -/
theorem source_unit {source : List U8} {base start finish cp width : Nat}
    (unit : Prefix source start = some (cp,width)) (afterBase : base ≤ start)
    (fits : start+width ≤ finish) :
    Prefix (Bytes source base finish) (start-base) = some (cp,width) := by
  apply prefix_transfer unit
  intro k before
  rw [byte_lookup _ _ _ _ (by omega)]
  congr 1
  omega

private theorem rebase {source : List U8} {start finish : Nat} {word : List Nat}
    (span : Utf8Span source start finish word) (base : Nat) (afterBase : base ≤ start) :
    Rowl.Regular.Utf8From (Bytes source base finish) (start-base) word := by
  induction span with
  | @empty position bounded =>
    have size : (Bytes source base position).length = position-base := by
      simp [Bytes]; omega
    rw [← size]
    exact .endOfInput
  | @character position cp width finish tail unit positive bounded rest ih =>
    have restBounds := bounds rest
    have rebased := source_unit (finish := finish) unit afterBase (by omega)
    have size : (Bytes source base finish).length = finish-base := by
      simp [Bytes]; omega
    have tail := ih (by omega)
    have next : position+width-base = (position-base)+width := by omega
    rw [next] at tail
    exact .character rebased positive (by rw [size]; omega) tail

private theorem unbase (source : List U8) (base finish : Nat)
    (range : base ≤ finish ∧ finish ≤ source.length) (position : Nat) (word : List Nat)
    (text : Rowl.Regular.Utf8From (Bytes source base finish) position word) :
    Utf8Span source (base+position) finish word := by
  have size : (Bytes source base finish).length = finish-base := by simp [Bytes]; omega
  induction text with
  | endOfInput =>
    have same : base+(Bytes source base finish).length = finish := by omega
    rw [same]
    exact .empty range.2
  | @character position cp width tail unit positive fits rest ih =>
    have originalUnit : Prefix source (base+position) = some (cp,width) := by
      apply prefix_transfer unit
      intro k before
      rw [byte_lookup _ _ _ _ (by omega)]
      congr 1
      omega
    have next : base+(position+width) = base+position+width := by omega
    rw [next] at ih
    exact .character originalUnit positive (by omega) ih

/-- Exact source-segment/copy equivalence in both directions for every Unicode
    word, including empty spans. Bytes outside the selected segment are separate. -/
theorem utf8_source_iff (source : List U8) (start finish : Nat) (word : List Nat)
    (range : start ≤ finish ∧ finish ≤ source.length) :
    Utf8Span source start finish word ↔ Rowl.Regular.Utf8From (Bytes source start finish) 0 word := by
  constructor
  · intro span
    simpa using rebase span start le_rfl
  · intro text
    simpa using unbase source start finish range 0 word text

/-- Canonical source bytes need at least one byte per decoded Unicode scalar. -/
theorem source_length {source : List U8} {start finish : Nat} {word : List Nat}
    (span : Utf8Span source start finish word) : word.length ≤ finish-start := by
  induction span with
  | empty bounded => simp
  | character _ positive _ rest ih =>
    have := bounds rest
    simp only [List.length_cons]
    omega

/-- Concatenated source words split at a canonical original byte boundary. -/
theorem source_split {source : List U8} {start finish : Nat} (left right : List Nat)
    (span : Utf8Span source start finish (left++right)) :
    ∃ middle, Utf8Span source start middle left ∧ Utf8Span source middle finish right := by
  induction left generalizing start with
  | nil => exact ⟨start,.empty ((bounds span).1.trans (bounds span).2),span⟩
  | cons head tail ih =>
    cases span with
    | character unit positive fits rest =>
      obtain ⟨middle,first,last⟩ := ih rest
      exact ⟨middle,.character unit positive fits first,last⟩

end Rowl.SourceSpans
