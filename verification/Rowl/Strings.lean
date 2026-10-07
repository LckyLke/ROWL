import Rowl.Numbers

/-!
The actual kernel checks of the six subtypes of `xsd:string`: no tab, line feed
or carriage return (`unbroken`), every space followed by a character other
than a space (`spaced_once`, `tokenized`), language tags (`subtags_from`), and
the XML 1.1 name productions over the decoded characters (`name_characters`,
`name_token`, `xml_name`). `text_in_kind` decides exactly whether XML text is in
the value space of a kind's datatype (`text_in_kind_correct`), and the six
subtypes are nested: language tags are NCNames, NCNames names, names name
tokens, name tokens tokens and tokens normalized strings (`form_chain`).
-/
namespace Rowl.Strings
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.DatatypeMap
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- The subtype of `xsd:string` that is a kind's datatype. -/
def subtypeOf : datatypes.Kind → Option StringSubtype
  | .NormalizedString => some .normalized
  | .Token => some .token
  | .Language => some .language
  | .NmToken => some .nmtoken
  | .Name => some .name
  | .NcName => some .ncname
  | _ => none

/-- Whether a string is in the value space of a kind's datatype: always for
    `xsd:string` and `rdf:PlainLiteral`, and for a subtype of `xsd:string` when
    it is one of the subtype's lexical forms. -/
def TextIn (k : datatypes.Kind) (t : List U8) : Prop :=
  k = .String ∨ k = .Plain ∨ ∃ s, subtypeOf k = some s ∧ s.Form t

/-! ### Normalized strings and tokens -/

/-- No tab, line feed or carriage return. -/
def Unbroken (t : List U8) : Prop := 9#u8 ∉ t ∧ 10#u8 ∉ t ∧ 13#u8 ∉ t

private theorem eq_32 (b : U8) : b = 32#u8 ↔ b.val = 32 := by rw [UScalar.eq_equiv]; simp
private theorem eq_45 (b : U8) : b = 45#u8 ↔ b.val = 45 := by rw [UScalar.eq_equiv]; simp

private theorem unbroken_cons (b : U8) (l : List U8) :
    Unbroken (b :: l) ↔ (b.val ≠ 9 ∧ b.val ≠ 10 ∧ b.val ≠ 13) ∧ Unbroken l := by
  have e9 : (9#u8 = b) ↔ b.val = 9 := by rw [eq_comm, UScalar.eq_equiv]; simp
  have e10 : (10#u8 = b) ↔ b.val = 10 := by rw [eq_comm, UScalar.eq_equiv]; simp
  have e13 : (13#u8 = b) ↔ b.val = 13 := by rw [eq_comm, UScalar.eq_equiv]; simp
  simp only [Unbroken, List.mem_cons, not_or, e9, e10, e13]
  tauto

theorem unbroken_correct (text : alloc.vec.Vec U8) (index : Usize) :
    datatypes.unbroken text index = .ok (decide (Unbroken (text.val.drop index.val))) := by
  rw [datatypes.unbroken]
  by_cases inside : index.val < text.val.length
  · have lookup : text.index_usize index = .ok text.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have stepIff : Unbroken (text.val.drop index.val) ↔
        (text.val[index.val].val ≠ 9 ∧ text.val[index.val].val ≠ 10 ∧ text.val[index.val].val ≠ 13) ∧
          Unbroken (text.val.drop (index.val + 1)) := by
      rw [List.drop_eq_getElem_cons inside]; exact unbroken_cons _ _
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have ih := unbroken_correct text next
    rw [nextIs] at ih
    by_cases good : text.val[index.val].val ≠ 9 ∧ text.val[index.val].val ≠ 10 ∧ text.val[index.val].val ≠ 13
    · rw [show decide (Unbroken (text.val.drop index.val)) = decide (Unbroken (text.val.drop (index.val + 1))) by
        rw [decide_eq_decide, stepIff]; simp [good]]
      obtain ⟨g9, g10, g13⟩ := good
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, g9, g10, g13, advance, ih]
    · rw [show decide (Unbroken (text.val.drop index.val)) = false by simp [stepIff, good]]
      have bad : text.val[index.val].val = 9 ∨ text.val[index.val].val = 10 ∨ text.val[index.val].val = 13 := by
        by_contra h; simp only [not_or] at h; exact good h
      rcases bad with e | e | e <;> simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, e]
  · have empty : text.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [UScalar.lt_equiv, inside, empty, Unbroken]
termination_by text.val.length - index.val
decreasing_by omega

/-- Every space at or after `index` is followed by a byte that is no space. -/
def SpacedOnce (t : List U8) (index : Nat) : Prop :=
  ∀ i, index ≤ i → t[i]? = some 32#u8 → ∃ b, t[i + 1]? = some b ∧ b ≠ 32#u8

private theorem spaced_once_step (t : List U8) (index : Nat) (inside : index < t.length) :
    SpacedOnce t index ↔ (t[index].val = 32 → ∃ b, t[index + 1]? = some b ∧ b.val ≠ 32) ∧
      SpacedOnce t (index + 1) := by
  have e : ∀ b : U8, b = 32#u8 ↔ b.val = 32 := eq_32
  constructor
  · intro all
    refine ⟨fun space => ?_, fun i low => all i (by omega)⟩
    obtain ⟨b, hb, nb⟩ := all index le_rfl (by rw [List.getElem?_eq_getElem inside, Option.some_inj, e]; exact space)
    exact ⟨b, hb, fun h => nb ((e b).mpr h)⟩
  · rintro ⟨here, later⟩ i low at_i
    rcases Nat.eq_or_lt_of_le low with same | after
    · subst same
      rw [List.getElem?_eq_getElem inside, Option.some_inj, e] at at_i
      obtain ⟨b, hb, nb⟩ := here at_i
      exact ⟨b, hb, fun h => nb ((e b).mp h)⟩
    · exact later i (by omega) at_i

theorem spaced_once_correct (text : alloc.vec.Vec U8) (index : Usize) :
    datatypes.spaced_once text index = .ok (decide (SpacedOnce text.val index.val)) := by
  rw [datatypes.spaced_once]
  by_cases inside : index.val < text.val.length
  · have lookup : text.index_usize index = .ok text.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have ih := spaced_once_correct text next
    rw [nextIs] at ih
    have step := spaced_once_step text.val index.val inside
    by_cases space : text.val[index.val].val = 32
    · by_cases more : index.val + 1 < text.val.length
      · have lookup' : text.index_usize next = .ok text.val[index.val + 1] := by
          simp [alloc.vec.Vec.index_usize, nextIs, List.getElem?_eq_getElem more]
        by_cases double : text.val[index.val + 1].val = 32
        · rw [show decide (SpacedOnce text.val index.val) = false by
            simp only [decide_eq_false_iff_not, step, not_and]
            intro here
            obtain ⟨b, hb, nb⟩ := here space
            rw [List.getElem?_eq_getElem more, Option.some_inj] at hb
            exact absurd (hb ▸ double) nb]
          simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, space, advance, nextIs, more,
            lookup', double]
        · rw [show decide (SpacedOnce text.val index.val) = decide (SpacedOnce text.val (index.val + 1)) by
            rw [decide_eq_decide, step]
            exact and_iff_right fun _ => ⟨_, List.getElem?_eq_getElem more, double⟩]
          simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, space, advance, nextIs, more,
            lookup', double, ih]
      · rw [show decide (SpacedOnce text.val index.val) = false by
          simp only [decide_eq_false_iff_not, step, not_and]
          intro here
          obtain ⟨b, hb, _⟩ := here space
          rw [List.getElem?_eq_none (by omega)] at hb
          cases hb]
        simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, space, advance, nextIs, more]
    · rw [show decide (SpacedOnce text.val index.val) = decide (SpacedOnce text.val (index.val + 1)) by
        rw [decide_eq_decide, step]
        exact and_iff_right fun h => absurd h space]
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, space, advance, ih]
  · have yes : SpacedOnce text.val index.val := fun i low at_i => by
      rw [List.getElem?_eq_none (by omega)] at at_i
      cases at_i
    simp [UScalar.lt_equiv, inside, yes]
termination_by text.val.length - index.val
decreasing_by all_goals omega

/-- Every space is followed by a byte that is no space exactly when no space
    is last and no two spaces follow each other. -/
theorem spaced_once_iff (t : List U8) :
    SpacedOnce t 0 ↔ t.getLast? ≠ some 32#u8 ∧ ∀ i, t[i]? = some 32#u8 → t[i + 1]? ≠ some 32#u8 := by
  constructor
  · intro all
    refine ⟨fun last => ?_, fun i at_i next => ?_⟩
    · rw [List.getLast?_eq_getElem?] at last
      have positive : 0 < t.length := by
        by_contra zero
        rw [List.getElem?_eq_none (by omega)] at last
        cases last
      obtain ⟨b, hb, _⟩ := all (t.length - 1) (Nat.zero_le _) last
      rw [List.getElem?_eq_none (by omega)] at hb
      cases hb
    · obtain ⟨b, hb, nb⟩ := all i (Nat.zero_le _) at_i
      rw [hb] at next
      cases next
      exact nb rfl
  · rintro ⟨last, double⟩ i _ at_i
    have inside : i < t.length := by
      by_contra outside
      rw [List.getElem?_eq_none (by omega)] at at_i
      cases at_i
    by_cases more : i + 1 < t.length
    · refine ⟨t[i + 1], List.getElem?_eq_getElem more, fun e => double i at_i ?_⟩
      rw [List.getElem?_eq_getElem more, e]
    · have : i = t.length - 1 := by omega
      subst this
      exact absurd (by rw [List.getLast?_eq_getElem?]; exact at_i) last

theorem tokenized_correct (text : alloc.vec.Vec U8) :
    datatypes.tokenized text =
      .ok (decide (Unbroken text.val ∧ text.val.head? ≠ some 32#u8 ∧ SpacedOnce text.val 0)) := by
  rw [datatypes.tokenized, unbroken_correct]
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero]
  by_cases unbroken : Unbroken text.val
  · by_cases empty : text.val.length = 0
    · have zero : alloc.vec.Vec.len text = 0#usize := by
        apply UScalar.eq_of_val_eq; simpa using empty
      have nil : text.val = [] := List.eq_nil_of_length_eq_zero empty
      rw [show decide (Unbroken text.val ∧ text.val.head? ≠ some 32#u8 ∧ SpacedOnce text.val 0) =
        decide (SpacedOnce text.val 0) by rw [decide_eq_decide, nil]; simp [Unbroken]]
      simp [unbroken, zero, spaced_once_correct]
    · have positive : 0 < text.val.length := by omega
      have notZero : ¬ alloc.vec.Vec.len text = 0#usize := by
        intro h; apply empty; simpa using congrArg UScalar.val h
      have lookup : text.index_usize 0#usize = .ok text.val[0] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem positive]
      have head : text.val.head? = some text.val[0] := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem positive]
      by_cases first : text.val[0].val = 32
      · rw [show decide (Unbroken text.val ∧ text.val.head? ≠ some 32#u8 ∧ SpacedOnce text.val 0) = false by
          simp only [decide_eq_false_iff_not, head, ne_eq, Option.some_inj, eq_32, first]
          simp]
        simp [unbroken, notZero, alloc.vec.Vec.index_slice_index, lookup, first]
      · rw [show decide (Unbroken text.val ∧ text.val.head? ≠ some 32#u8 ∧ SpacedOnce text.val 0) =
          decide (SpacedOnce text.val 0) by
          rw [decide_eq_decide]
          simp only [head, ne_eq, Option.some_inj, eq_32, first]
          simp [unbroken]]
        simp [unbroken, notZero, alloc.vec.Vec.index_slice_index, lookup, first, spaced_once_correct]
  · rw [show decide (Unbroken text.val ∧ text.val.head? ≠ some 32#u8 ∧ SpacedOnce text.val 0) = false by
      simp [unbroken]]
    simp [unbroken]

/-- The kernel's token test is the lexical space of `xsd:token` on XML text. -/
theorem token_form_iff (t : List U8) (xml : XmlText t) :
    StringSubtype.token.Form t ↔ Unbroken t ∧ t.head? ≠ some 32#u8 ∧ SpacedOnce t 0 := by
  simp only [StringSubtype.Form, spaced_once_iff, Unbroken]
  constructor
  · rintro ⟨⟨_, n9, n10, n13⟩, head, last, double⟩
    exact ⟨⟨n9, n10, n13⟩, head, last, double⟩
  · rintro ⟨⟨n9, n10, n13⟩, head, last, double⟩
    exact ⟨⟨xml, n9, n10, n13⟩, head, last, double⟩

/-! ### Language tags -/

/-- A byte that may continue the current subtag: a letter, or a digit after
    the first subtag. -/
def SubtagByte (first : Bool) (byte : U8) : Prop := Letter byte ∨ (first = false ∧ 48 ≤ byte.val ∧ byte.val ≤ 57)

/-- `bytes` end a language tag `[a-zA-Z]{1,8}(-[a-zA-Z0-9]{1,8})*` whose current
    subtag already has `count` characters. -/
def SubtagsRest : List U8 → Nat → Bool → Prop
  | [], count, _ => 0 < count
  | byte :: rest, count, first =>
    if byte = 45#u8 then 0 < count ∧ SubtagsRest rest 0 false
    else count < 8 ∧ SubtagByte first byte ∧ SubtagsRest rest (count + 1) first

theorem is_letter_correct (byte : U8) : datatypes.is_letter byte = .ok (decide (Letter byte)) := by
  simp [datatypes.is_letter, Letter, UScalar.le_equiv]

private theorem is_digit_correct' (byte : U8) :
    datatypes.is_digit byte = .ok (decide (48 ≤ byte.val ∧ byte.val ≤ 57)) := by
  simp [datatypes.is_digit, UScalar.le_equiv]

theorem subtags_from_correct (text : alloc.vec.Vec U8) (index count : Usize) (first : Bool)
    (small : count.val ≤ 8) :
    datatypes.subtags_from text index count first =
      .ok (decide (SubtagsRest (text.val.drop index.val) count.val first)) := by
  rw [datatypes.subtags_from]
  by_cases inside : index.val < text.val.length
  · have lookup : text.index_usize index = .ok text.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have cons := List.drop_eq_getElem_cons inside
    by_cases dash : text.val[index.val].val = 45
    · have dash' : text.val[index.val] = 45#u8 := (eq_45 _).mpr dash
      have ih := subtags_from_correct text next 0#usize false (by simp)
      rw [nextIs] at ih
      by_cases positive : 0 < count.val
      · rw [show decide (SubtagsRest (text.val.drop index.val) count.val first) =
            decide (SubtagsRest (text.val.drop (index.val + 1)) 0 false) by
          rw [decide_eq_decide, cons]; simp only [SubtagsRest, dash', ↓reduceIte, positive, true_and]]
        have positive' : (0#usize) < count := by simp only [UScalar.lt_equiv]; simpa using positive
        simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, dash, positive', advance, ih]
      · rw [show decide (SubtagsRest (text.val.drop index.val) count.val first) = false by
          rw [cons]; simp [SubtagsRest, dash', positive]]
        have notPositive : ¬ (0#usize) < count := by simp only [UScalar.lt_equiv]; simpa using positive
        simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, dash, notPositive]
    · have dash' : text.val[index.val] ≠ 45#u8 := fun e => dash ((eq_45 _).mp e)
      by_cases room : count.val < 8
      · obtain ⟨more, step, moreValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := count) (y := 1#usize) (by scalar_tac))
        have moreIs : more.val = count.val + 1 := by simpa using moreValue
        have ih := subtags_from_correct text next more first (by omega)
        rw [nextIs, moreIs] at ih
        have room' : count < (8#usize) := by simp only [UScalar.lt_equiv]; simpa using room
        by_cases ok : SubtagByte first text.val[index.val]
        · rw [show decide (SubtagsRest (text.val.drop index.val) count.val first) =
              decide (SubtagsRest (text.val.drop (index.val + 1)) (count.val + 1) first) by
            rw [decide_eq_decide, cons]; simp only [SubtagsRest, dash', ↓reduceIte, room, ok, true_and]]
          rcases ok with letter | ⟨rfl, d1, d2⟩
          · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, dash, is_letter_correct,
              is_digit_correct', room', letter, advance, step, ih]
          · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, dash, is_letter_correct,
              is_digit_correct', room', d1, d2, advance, step, ih]
        · rw [show decide (SubtagsRest (text.val.drop index.val) count.val first) = false by
            rw [cons]; simp only [SubtagsRest, dash', ↓reduceIte, ok, false_and, and_false, decide_false]]
          simp only [SubtagByte, not_or, not_and] at ok
          obtain ⟨notLetter, notDigit⟩ := ok
          cases first with
          | true =>
            simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, dash, is_letter_correct,
              is_digit_correct', room', notLetter]
          | false =>
            have outside : ¬ (48 ≤ text.val[index.val].val ∧ text.val[index.val].val ≤ 57) :=
              fun ⟨d1, d2⟩ => notDigit rfl d1 d2
            simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, dash, is_letter_correct,
              is_digit_correct', room', notLetter, outside]
      · rw [show decide (SubtagsRest (text.val.drop index.val) count.val first) = false by
          rw [cons]; simp [SubtagsRest, dash', room]]
        have room' : ¬ count < (8#usize) := by simp only [UScalar.lt_equiv]; simpa using room
        simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, dash, is_letter_correct,
          is_digit_correct', room']
  · have empty : text.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [UScalar.lt_equiv, inside, empty, SubtagsRest]
termination_by text.val.length - index.val
decreasing_by all_goals omega

/-- A subtag byte is no dash. -/
private theorem subtag_byte_ne {first : Bool} {b : U8} (h : SubtagByte first b) : b ≠ 45#u8 := by
  intro e
  subst e
  rcases h with (⟨h, _⟩ | ⟨h, _⟩) | ⟨_, h, _⟩ <;> simp at h

private theorem flatten_dashes (rest : List (List U8)) :
    (rest.map (45#u8 :: ·)).flatten = [] ∧ rest = [] ∨
      ∃ s rest', rest = s :: rest' ∧ (rest.map (45#u8 :: ·)).flatten = 45#u8 :: (s ++ (rest'.map (45#u8 :: ·)).flatten) := by
  cases rest with
  | nil => exact .inl ⟨rfl, rfl⟩
  | cons s rest' => exact .inr ⟨s, rest', rfl, by simp⟩

/-- `SubtagsRest` reads the grammar of `xsd:language` on, after a current
    subtag `p` of subtag bytes. -/
theorem subtags_rest_iff (t : List U8) : ∀ (p : List U8) (first : Bool), p.length ≤ 8 →
    (∀ b ∈ p, SubtagByte first b) →
    (SubtagsRest t p.length first ↔ ∃ (cur : List U8) (rest : List (List U8)), Subtag first (p ++ cur) ∧
      (∀ s ∈ rest, Subtag false s) ∧ t = cur ++ (rest.map (45#u8 :: ·)).flatten) := by
  induction t with
  | nil =>
    intro p first len chars
    simp only [SubtagsRest]
    constructor
    · intro positive
      exact ⟨[], [], ⟨by simp; omega, by simpa using len, by simpa [SubtagByte] using chars⟩,
        by simp, by simp⟩
    · rintro ⟨cur, rest, sub, _, same⟩
      have : cur = [] := (List.append_eq_nil_iff.mp same.symm).1
      subst this
      have := sub.1
      simp at this
      omega
  | cons b t ih =>
    intro p first len chars
    by_cases dash : b = 45#u8
    · subst dash
      simp only [SubtagsRest, ↓reduceIte]
      have ih' := ih [] false (by simp) (by simp)
      simp only [List.length_nil, List.nil_append] at ih'
      rw [ih']
      constructor
      · rintro ⟨positive, cur, rest, sub, all, same⟩
        refine ⟨[], cur :: rest, ⟨by simp; omega, by simpa using len, by simpa [SubtagByte] using chars⟩,
          ?_, by simp [same]⟩
        intro s mem
        rcases List.mem_cons.mp mem with rfl | later
        · exact sub
        · exact all s later
      · rintro ⟨cur, rest, sub, all, same⟩
        cases cur with
        | cons c cur' =>
          have hc : c = 45#u8 := (List.cons.inj same).1.symm
          exact absurd hc (subtag_byte_ne (sub.2.2 c (by simp)))
        | nil =>
          rcases flatten_dashes rest with ⟨empty, _⟩ | ⟨s, rest', rfl, split⟩
          · simp [empty] at same
          · rw [List.nil_append, split] at same
            refine ⟨by have := sub.1; simp at this; omega, s, rest', all s (by simp),
              fun s' m => all s' (by simp [m]), ?_⟩
            exact (List.cons.inj same).2
    · simp only [SubtagsRest, dash, ↓reduceIte]
      constructor
      · rintro ⟨room, byte, later⟩
        have ih' := ih (p ++ [b]) first (by simp; omega)
          (fun x mem => by rcases List.mem_append.mp mem with m | m; exact chars x m; simp at m; exact m ▸ byte)
        simp only [List.length_append, List.length_singleton] at ih'
        obtain ⟨cur, rest, sub, all, same⟩ := ih'.mp later
        exact ⟨b :: cur, rest, by simpa using sub, all, by simp [same]⟩
      · rintro ⟨cur, rest, sub, all, same⟩
        cases cur with
        | nil =>
          rcases flatten_dashes rest with ⟨empty, _⟩ | ⟨s, rest', rfl, split⟩
          · simp [empty] at same
          · rw [List.nil_append, split] at same
            exact absurd (List.cons.inj same).1 dash
        | cons c cur' =>
          obtain ⟨hc, rest_eq⟩ := List.cons.inj same
          subst hc
          have long : p.length < 8 := by have := sub.2.1; simp at this; omega
          have byte : SubtagByte first b := sub.2.2 b (by simp)
          refine ⟨long, byte, ?_⟩
          have ih' := ih (p ++ [b]) first (by simp; omega)
            (fun x mem => by rcases List.mem_append.mp mem with m | m; exact chars x m; simp at m; exact m ▸ byte)
          simp only [List.length_append, List.length_singleton] at ih'
          exact ih'.mpr ⟨cur', rest, by simpa using sub, all, rest_eq⟩

/-- The kernel's language test is the lexical space of `xsd:language`. -/
theorem language_form_iff (t : List U8) : LanguageForm t ↔ SubtagsRest t 0 true := by
  have := subtags_rest_iff t [] true (by simp) (by simp)
  simp only [List.length_nil, List.nil_append] at this
  rw [this]
  rfl

/-! ### Names -/

/-- XML text has one decoding. -/
theorem text_from_unique {bs : List U8} {offset : Nat} {t1 t2 : List (Nat × Nat)}
    (h1 : Rowl.Unicode.TextFrom bs offset t1) (h2 : Rowl.Unicode.TextFrom bs offset t2) : t1 = t2 := by
  induction h1 generalizing t2 with
  | endOfInput =>
    cases h2 with
    | endOfInput => rfl
    | character pre _ _ _ _ => simp [Rowl.Unicode.Prefix] at pre
  | character pre _ _ _ _ ih =>
    cases h2 with
    | endOfInput => simp [Rowl.Unicode.Prefix] at pre
    | character pre' _ _ _ rest' =>
      rw [pre] at pre'
      cases pre'
      rw [ih rest']

/-- The characters of the text the kernel decoded. -/
theorem text_chars_iff {bytes : List U8} {scalars : unicode.Scalars}
    (scan : Rowl.Unicode.TextFrom bytes 0 (Rowl.Unicode.scalarValues scalars)) (cps : List Nat) :
    TextChars bytes cps ↔ cps = (Rowl.Unicode.scalarValues scalars).map Prod.fst := by
  constructor
  · rintro ⟨text, h, rfl⟩
    rw [text_from_unique h scan]
  · rintro rfl
    exact ⟨_, scan, rfl⟩

theorem name_start_correct (cp : U32) : datatypes.name_start cp = .ok (decide (NameStartChar cp.val)) := by
  simp only [datatypes.name_start, NameStartChar, UScalar.le_equiv, UScalar.eq_equiv]
  simp [Bool.or_assoc]

theorem name_character_correct (cp : U32) : datatypes.name_character cp = .ok (decide (NameChar cp.val)) := by
  simp only [datatypes.name_character, name_start_correct, NameChar, UScalar.le_equiv, UScalar.eq_equiv, bind_ok]
  simp [Bool.or_assoc]

theorem name_characters_correct (scalars : unicode.Scalars) :
    datatypes.name_characters scalars =
      .ok (decide (∀ c ∈ (Rowl.Unicode.scalarValues scalars).map Prod.fst, NameChar c)) := by
  induction scalars with
  | Empty => rw [datatypes.name_characters]; simp [Rowl.Unicode.scalarValues]
  | Cons cp offset next ih =>
    rw [datatypes.name_characters]
    by_cases h : NameChar cp.val
    · simp [name_character_correct, h, ih, Rowl.Unicode.scalarValues]
    · simp [name_character_correct, h, Rowl.Unicode.scalarValues]

/-- A name: a name start character and name characters. -/
def NameText (t : List U8) : Prop :=
  ∃ c cps, TextChars t (c :: cps) ∧ NameStartChar c ∧ ∀ c' ∈ cps, NameChar c'

/-- A name token: one or more name characters. -/
def TokenText (t : List U8) : Prop := ∃ cps, TextChars t cps ∧ cps ≠ [] ∧ ∀ c ∈ cps, NameChar c

theorem xml_name_correct (text : alloc.vec.Vec U8) :
    datatypes.xml_name text = .ok (decide (NameText text.val)) := by
  obtain ⟨result, run, scan⟩ := Rowl.Unicode.read_text_total_correct text
  rw [datatypes.xml_name, run]
  cases result with
  | Invalid error =>
    have no : ¬ NameText text.val := fun ⟨_, _, ⟨t, h, _⟩, _⟩ =>
      Rowl.Unicode.rejected_excludes_text _ _ _ scan t h
    simp [no]
  | Valid scalars =>
    have chars := text_chars_iff (bytes := text.val) (scalars := scalars) scan
    cases scalars with
    | Empty =>
      have no : ¬ NameText text.val := fun ⟨c, cps, h, _⟩ => by
        rw [chars] at h; simp [Rowl.Unicode.scalarValues] at h
      simp [no]
    | Cons cp offset next =>
      have iff : NameText text.val ↔ NameStartChar cp.val ∧
          ∀ c ∈ (Rowl.Unicode.scalarValues next).map Prod.fst, NameChar c := by
        simp only [NameText, chars, Rowl.Unicode.scalarValues, List.map_cons, List.cons.injEq]
        constructor
        · rintro ⟨c, cps, ⟨rfl, rfl⟩, start, rest⟩
          exact ⟨start, rest⟩
        · rintro ⟨start, rest⟩
          exact ⟨_, _, ⟨rfl, rfl⟩, start, rest⟩
      by_cases start : NameStartChar cp.val
      · simp [name_start_correct, start, name_characters_correct, iff]
      · simp [name_start_correct, start, iff]

theorem name_token_correct (text : alloc.vec.Vec U8) :
    datatypes.name_token text = .ok (decide (TokenText text.val)) := by
  obtain ⟨result, run, scan⟩ := Rowl.Unicode.read_text_total_correct text
  rw [datatypes.name_token, run]
  cases result with
  | Invalid error =>
    have no : ¬ TokenText text.val := fun ⟨_, ⟨t, h, _⟩, _⟩ =>
      Rowl.Unicode.rejected_excludes_text _ _ _ scan t h
    simp [no]
  | Valid scalars =>
    have chars := text_chars_iff (bytes := text.val) (scalars := scalars) scan
    cases scalars with
    | Empty =>
      have no : ¬ TokenText text.val := fun ⟨cps, h, nonempty, _⟩ => by
        rw [chars] at h; simp [Rowl.Unicode.scalarValues] at h; exact nonempty h
      simp [no]
    | Cons cp offset next =>
      have iff : TokenText text.val ↔ NameChar cp.val ∧
          ∀ c ∈ (Rowl.Unicode.scalarValues next).map Prod.fst, NameChar c := by
        simp only [TokenText, chars, Rowl.Unicode.scalarValues, List.map_cons]
        constructor
        · rintro ⟨cps, rfl, _, all⟩
          exact ⟨all _ (by simp), fun c m => all c (by simp [m])⟩
        · rintro ⟨first, rest⟩
          refine ⟨_, rfl, by simp, fun c m => ?_⟩
          rcases List.mem_cons.mp m with rfl | later
          · exact first
          · exact rest c later
      by_cases first : NameChar cp.val
      · simp [name_character_correct, first, name_characters_correct, iff]
      · simp [name_character_correct, first, iff]

/-- `find_byte` reaches the end exactly when the byte does not occur from the
    index on. -/
theorem find_byte_end (bytes : alloc.vec.Vec U8) (byte : U8) (index : Usize) :
    ∃ r, datatypes.find_byte bytes byte index = .ok r ∧
      (r = alloc.vec.Vec.len bytes ↔ byte ∉ bytes.val.drop index.val) := by
  rw [datatypes.find_byte]
  by_cases inside : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have cons := List.drop_eq_getElem_cons inside
    by_cases found : bytes.val[index.val] = byte
    · refine ⟨index, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, found], ?_⟩
      rw [cons, ← found]
      constructor
      · intro same
        have := congrArg UScalar.val same
        simp at this
        omega
      · intro absent
        exact absurd List.mem_cons_self absent
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, iff⟩ := find_byte_end bytes byte next
      refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, found, advance, run], ?_⟩
      rw [iff, nextIs, cons]
      simp only [List.mem_cons, not_or]
      exact ⟨fun h => ⟨fun e => found e.symm, h⟩, fun h => h.2⟩
  · refine ⟨alloc.vec.Vec.len bytes, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show bytes.val.length ≤ index.val by omega)]
termination_by bytes.val.length - index.val
decreasing_by omega

/-! ### Membership of XML text -/

/-- The kernel decides exactly whether XML text is in the value space of a
    kind's datatype. -/
theorem text_in_kind_correct (text : alloc.vec.Vec U8) (xml : XmlText text.val) (k : datatypes.Kind) :
    datatypes.text_in_kind text k = .ok (decide (TextIn k text.val)) := by
  have zero : (0#usize : Usize).val = 0 := rfl
  cases k
  case NormalizedString =>
    have iff : Unbroken (text.val.drop (0#usize : Usize).val) ↔ TextIn .NormalizedString text.val := by
      simp [TextIn, subtypeOf, StringSubtype.Form, Unbroken, xml]
    rw [datatypes.text_in_kind, unbroken_correct, decide_eq_decide.mpr iff]
  case Token =>
    have iff : (Unbroken text.val ∧ text.val.head? ≠ some 32#u8 ∧ SpacedOnce text.val 0) ↔
        TextIn .Token text.val := by
      rw [← token_form_iff _ xml]
      simp [TextIn, subtypeOf]
    rw [datatypes.text_in_kind, tokenized_correct, decide_eq_decide.mpr iff]
  case Language =>
    have iff : SubtagsRest (text.val.drop (0#usize : Usize).val) (0#usize : Usize).val true ↔
        TextIn .Language text.val := by
      rw [zero, List.drop_zero, ← language_form_iff]
      simp [TextIn, subtypeOf, StringSubtype.Form]
    rw [datatypes.text_in_kind, subtags_from_correct _ _ _ _ (by simp), decide_eq_decide.mpr iff]
  case NmToken =>
    have iff : TokenText text.val ↔ TextIn .NmToken text.val := by
      simp [TextIn, subtypeOf, StringSubtype.Form, TokenText]
    rw [datatypes.text_in_kind, name_token_correct, decide_eq_decide.mpr iff]
  case Name =>
    have iff : NameText text.val ↔ TextIn .Name text.val := by
      simp [TextIn, subtypeOf, StringSubtype.Form, NameText]
    rw [datatypes.text_in_kind, xml_name_correct, decide_eq_decide.mpr iff]
  case NcName =>
    obtain ⟨r, run, iff⟩ := find_byte_end text 58#u8 0#usize
    rw [zero, List.drop_zero] at iff
    have spec : TextIn .NcName text.val ↔ NameText text.val ∧ 58#u8 ∉ text.val := by
      simp [TextIn, subtypeOf, StringSubtype.Form, NameText]
    rw [datatypes.text_in_kind, xml_name_correct]
    by_cases isName : NameText text.val
    · by_cases colon : 58#u8 ∈ text.val
      · have differ : r ≠ alloc.vec.Vec.len text := fun h => iff.mp h colon
        simp [isName, run, differ, spec, colon]
      · simp [isName, run, iff.mpr colon, spec, colon]
    · simp [isName, spec]
  all_goals simp [datatypes.text_in_kind, TextIn, subtypeOf]

/-! ### The subtypes are nested -/

/-- The bytes of a multi-byte character are no ASCII bytes. -/
private theorem prefix_high {bs : List U8} {offset cp width : Nat}
    (pre : Rowl.Unicode.Prefix bs offset = some (cp, width)) {i : Nat} (low : offset < i) (high : i < offset + width)
    (inside : i < bs.length) : 128 ≤ bs[i].val := by
  unfold Rowl.Unicode.Prefix at pre
  cases ha : bs[offset]? with
  | none => simp [ha] at pre
  | some a =>
    simp only [ha, Option.bind_eq_bind, Option.bind_some] at pre
    split_ifs at pre with h1 h2 h3
    · simp at pre; omega
    · cases hb : bs[offset + 1]? with
      | none => simp [hb] at pre
      | some b =>
        simp only [hb, Option.bind_eq_bind, Option.bind_some] at pre
        split_ifs at pre with hp
        simp at pre
        have : i = offset + 1 := by omega
        subst this
        rw [List.getElem?_eq_getElem inside, Option.some_inj] at hb
        rw [hb]; exact hp.2.2.1
    · cases hb : bs[offset + 1]? with
      | none => simp [hb] at pre
      | some b =>
      cases hc : bs[offset + 2]? with
      | none => simp [hb, hc] at pre
      | some c =>
        simp only [hb, hc, Option.bind_eq_bind, Option.bind_some] at pre
        split_ifs at pre with ht
        simp at pre
        unfold Rowl.Unicode.Triple Rowl.Unicode.Tail at ht
        rcases (by omega : i = offset + 1 ∨ i = offset + 2) with e | e <;> subst e
        · rw [List.getElem?_eq_getElem inside, Option.some_inj] at hb; rw [hb]; omega
        · rw [List.getElem?_eq_getElem inside, Option.some_inj] at hc; rw [hc]; omega
    · cases hb : bs[offset + 1]? with
      | none => simp [hb] at pre
      | some b =>
      cases hc : bs[offset + 2]? with
      | none => simp [hb, hc] at pre
      | some c =>
      cases hd : bs[offset + 3]? with
      | none => simp [hb, hc, hd] at pre
      | some d =>
        simp only [hb, hc, hd, Option.bind_eq_bind, Option.bind_some] at pre
        split_ifs at pre with hq
        simp at pre
        unfold Rowl.Unicode.Quad Rowl.Unicode.Tail at hq
        rcases (by omega : i = offset + 1 ∨ i = offset + 2 ∨ i = offset + 3) with e | e | e <;> subst e
        · rw [List.getElem?_eq_getElem inside, Option.some_inj] at hb; rw [hb]; omega
        · rw [List.getElem?_eq_getElem inside, Option.some_inj] at hc; rw [hc]; omega
        · rw [List.getElem?_eq_getElem inside, Option.some_inj] at hd; rw [hd]; omega

/-- An ASCII byte of XML text is a character of its own. -/
theorem ascii_char {bs : List U8} {offset : Nat} {text : List (Nat × Nat)}
    (h : Rowl.Unicode.TextFrom bs offset text) {i : Nat} (low : offset ≤ i) (inside : i < bs.length)
    (ascii : bs[i].val < 128) : bs[i].val ∈ text.map Prod.fst := by
  induction h with
  | endOfInput => omega
  | @character offset cp width tail pre _ positive _ _ ih =>
    rcases Nat.eq_or_lt_of_le low with same | after
    · subst same
      unfold Rowl.Unicode.Prefix at pre
      simp only [List.getElem?_eq_getElem inside, Option.bind_eq_bind, Option.bind_some, ascii, ↓reduceIte,
        Option.some.injEq, Prod.mk.injEq] at pre
      simp [pre.1]
    · by_cases within : i < offset + width
      · exact absurd ascii (by have := prefix_high pre after within inside; omega)
      · exact List.mem_cons_of_mem _ (ih (by omega))

/-- Name characters are no tab, line feed, carriage return or space. -/
theorem name_char_breaks {c : Nat} (h : NameChar c) : c ≠ 9 ∧ c ≠ 10 ∧ c ≠ 13 ∧ c ≠ 32 := by
  unfold NameChar NameStartChar at h
  omega

/-- A byte of a name token is no tab, line feed, carriage return or space. -/
private theorem token_text_bytes {t : List U8} (h : TokenText t) {b : U8} (mem : b ∈ t) :
    b.val ≠ 9 ∧ b.val ≠ 10 ∧ b.val ≠ 13 ∧ b.val ≠ 32 := by
  obtain ⟨cps, ⟨text, from0, rfl⟩, _, all⟩ := h
  obtain ⟨i, inside, rfl⟩ := List.getElem_of_mem mem
  by_cases ascii : t[i].val < 128
  · exact name_char_breaks (all _ (ascii_char from0 (Nat.zero_le _) inside ascii))
  · omega

private theorem not_mem_of_val {t : List U8} {n : Nat} (h : ∀ b ∈ t, b.val ≠ n) (m : U8) (hm : m.val = n) :
    m ∉ t := fun mem => h m mem hm

/-- Name tokens are tokens. -/
theorem token_of_nmtoken {t : List U8} (h : StringSubtype.nmtoken.Form t) : StringSubtype.token.Form t := by
  have bytes : ∀ {b : U8}, b ∈ t → b.val ≠ 9 ∧ b.val ≠ 10 ∧ b.val ≠ 13 ∧ b.val ≠ 32 :=
    fun mem => token_text_bytes h mem
  obtain ⟨cps, ⟨text, from0, _⟩, _, _⟩ := h
  have no : ∀ n, (n = 9 ∨ n = 10 ∨ n = 13 ∨ n = 32) → ∀ m : U8, m.val = n → m ∉ t := by
    intro n hn m hm mem
    have := bytes mem
    omega
  have n32 : (32#u8) ∉ t := no 32 (by omega) _ rfl
  refine ⟨⟨⟨text, from0⟩, no 9 (by omega) _ rfl, no 10 (by omega) _ rfl, no 13 (by omega) _ rfl⟩, ?_, ?_, ?_⟩
  · intro head
    exact n32 (List.mem_of_mem_head? head)
  · intro last
    exact n32 (List.mem_of_mem_getLast? last)
  · intro i at_i
    exact absurd (List.mem_of_getElem? at_i) n32

/-- Names are name tokens. -/
theorem nmtoken_of_name {t : List U8} (h : StringSubtype.name.Form t) : StringSubtype.nmtoken.Form t := by
  obtain ⟨c, cps, chars, start, rest⟩ := h
  refine ⟨c :: cps, chars, by simp, fun c' mem => ?_⟩
  rcases List.mem_cons.mp mem with rfl | later
  · exact .inl start
  · exact rest c' later

/-- An ASCII string of XML characters is XML text of those characters. -/
theorem xml_ascii_chars (bs : List U8) (ascii : ∀ b ∈ bs, Rowl.Unicode.XmlChar b.val ∧ b.val < 128) :
    TextChars bs (bs.map (·.val)) := by
  have step : ∀ k o, o + k = bs.length →
      ∃ text, Rowl.Unicode.TextFrom bs o text ∧ text.map Prod.fst = (bs.drop o).map (·.val) := by
    intro k
    induction k with
    | zero =>
      intro o h
      have : o = bs.length := by omega
      subst this
      exact ⟨[], Rowl.Unicode.TextFrom.endOfInput, by simp⟩
    | succ k ih =>
      intro o h
      have inside : o < bs.length := by omega
      obtain ⟨text, from', same⟩ := ih (o + 1) (by omega)
      have ha := ascii _ (List.getElem_mem inside)
      refine ⟨(bs[o].val, o) :: text, .character (width := 1) ?_ ?_ (by decide) (by omega) from', ?_⟩
      · simp [Rowl.Unicode.Prefix, List.getElem?_eq_getElem inside, ha.2]
      · exact ha.1
      · rw [List.drop_eq_getElem_cons inside]
        simp only [List.map_cons, same]
  obtain ⟨text, from0, same⟩ := step bs.length 0 (by simp)
  exact ⟨text, from0, by simpa using same⟩

/-- An ASCII string of characters from the space on is XML text of those
    characters. -/
theorem ascii_chars (bs : List U8) (ascii : ∀ b ∈ bs, 32 ≤ b.val ∧ b.val < 128) :
    TextChars bs (bs.map (·.val)) :=
  xml_ascii_chars bs fun b mem => ⟨by unfold Rowl.Unicode.XmlChar; have := ascii b mem; omega, (ascii b mem).2⟩

/-- An ASCII name: a name start character and name characters. -/
theorem ascii_name (bs : List U8) (ascii : ∀ b ∈ bs, 32 ≤ b.val ∧ b.val < 128) :
    NameText bs ↔ ∃ b rest, bs = b :: rest ∧ NameStartChar b.val ∧ ∀ c ∈ rest, NameChar c.val := by
  have chars := ascii_chars bs ascii
  constructor
  · rintro ⟨c, cps, ⟨text, from0, same⟩, start, rest⟩
    obtain ⟨text', from0', same'⟩ := chars
    rw [text_from_unique from0 from0', same'] at same
    cases bs with
    | nil => simp at same
    | cons b rest' =>
      simp only [List.map_cons, List.cons.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨b, rest', rfl, start, fun c' mem => rest _ (List.mem_map_of_mem mem)⟩
  · rintro ⟨b, rest, rfl, start, all⟩
    refine ⟨b.val, rest.map (·.val), by simpa using chars, start, fun c mem => ?_⟩
    obtain ⟨c', mem', rfl⟩ := List.mem_map.mp mem
    exact all c' mem'

/-- An ASCII name token: name characters, at least one. -/
theorem ascii_token (bs : List U8) (ascii : ∀ b ∈ bs, 32 ≤ b.val ∧ b.val < 128) :
    TokenText bs ↔ bs ≠ [] ∧ ∀ c ∈ bs, NameChar c.val := by
  have chars := ascii_chars bs ascii
  constructor
  · rintro ⟨cps, ⟨text, from0, same⟩, nonempty, all⟩
    obtain ⟨text', from0', same'⟩ := chars
    rw [text_from_unique from0 from0', same'] at same
    subst same
    exact ⟨by simpa using nonempty, fun c mem => all _ (List.mem_map_of_mem mem)⟩
  · rintro ⟨nonempty, all⟩
    refine ⟨_, chars, by simpa using nonempty, fun c mem => ?_⟩
    obtain ⟨c', mem', rfl⟩ := List.mem_map.mp mem
    exact all c' mem'

/-- Language tags are NCNames. -/
theorem ncname_of_language {t : List U8} (h : StringSubtype.language.Form t) : StringSubtype.ncname.Form t := by
  obtain ⟨first, rest, subFirst, subRest, rfl⟩ := h
  have bytes : ∀ b ∈ first ++ (rest.map (45#u8 :: ·)).flatten, Letter b ∨ (48 ≤ b.val ∧ b.val ≤ 57) ∨ b = 45#u8 := by
    intro b mem
    rcases List.mem_append.mp mem with m | m
    · rcases subFirst.2.2 b m with l | ⟨f, _⟩
      · exact .inl l
      · cases f
    · obtain ⟨l, ml, mb⟩ := List.mem_flatten.mp m
      obtain ⟨s, ms, rfl⟩ := List.mem_map.mp ml
      rcases List.mem_cons.mp mb with rfl | ms'
      · exact .inr (.inr rfl)
      · rcases (subRest s ms).2.2 b ms' with l | ⟨_, d1, d2⟩
        · exact .inl l
        · exact .inr (.inl ⟨d1, d2⟩)
  have ascii : ∀ b ∈ first ++ (rest.map (45#u8 :: ·)).flatten, 32 ≤ b.val ∧ b.val < 128 := by
    intro b mem
    rcases bytes b mem with (⟨l1, l2⟩ | ⟨l1, l2⟩) | ⟨d1, d2⟩ | rfl
    all_goals first | omega | simp
  obtain ⟨one, _, firstBytes⟩ := subFirst
  obtain ⟨b, first', rfl⟩ : ∃ b first', first = b :: first' := by
    cases first with
    | nil => simp at one
    | cons b first' => exact ⟨b, first', rfl⟩
  refine ⟨(ascii_name _ ascii).mpr ⟨b, _, rfl, ?_, fun c mem => ?_⟩, fun mem => ?_⟩
  · rcases firstBytes b (by simp) with l | ⟨f, _⟩
    · unfold Letter at l; unfold NameStartChar; omega
    · cases f
  · rcases bytes c (List.mem_cons_of_mem b mem) with l | ⟨d1, d2⟩ | rfl
    · unfold Letter at l; unfold NameChar NameStartChar; omega
    · unfold NameChar; omega
    · unfold NameChar; simp
  · rcases bytes _ mem with l | ⟨d1, d2⟩ | e
    · unfold Letter at l; simp at l
    · simp at d1 d2
    · simp at e

/-- The nesting of the subtypes of `xsd:string`, and each form is XML text. -/
theorem form_xml {s : StringSubtype} {t : List U8} (h : s.Form t) : XmlText t := by
  cases s with
  | normalized => exact h.1
  | token => exact h.1.1
  | language => obtain ⟨⟨_, _, ⟨text, from0, _⟩, _⟩, _⟩ := ncname_of_language h; exact ⟨text, from0⟩
  | nmtoken => obtain ⟨_, ⟨text, from0, _⟩, _⟩ := h; exact ⟨text, from0⟩
  | «name» => obtain ⟨_, _, ⟨text, from0, _⟩, _⟩ := h; exact ⟨text, from0⟩
  | ncname => obtain ⟨⟨_, _, ⟨text, from0, _⟩, _⟩, _⟩ := h; exact ⟨text, from0⟩

/-! ### The chain of the subtypes -/

/-- The lexical forms of the kinds of the chain of `xsd:string` by rank. -/
def ChainForm : Nat → List U8 → Prop
  | 0, t => XmlText t
  | 1, t => StringSubtype.normalized.Form t
  | 2, t => StringSubtype.token.Form t
  | 3, t => StringSubtype.nmtoken.Form t
  | 4, t => StringSubtype.name.Form t
  | 5, t => StringSubtype.ncname.Form t
  | _, t => StringSubtype.language.Form t

theorem chain_form_step (i : Nat) (t : List U8) (h : ChainForm (i + 1) t) : ChainForm i t := by
  match i with
  | 0 => exact h.1
  | 1 => exact h.1
  | 2 => exact token_of_nmtoken h
  | 3 => exact nmtoken_of_name h
  | 4 => exact h.1
  | 5 => exact ncname_of_language h
  | _ + 6 => exact h

/-- The kinds of the chain are nested. -/
theorem chain_form_mono {i j : Nat} (le : j ≤ i) {t : List U8} (h : ChainForm i t) : ChainForm j t := by
  induction i with
  | zero =>
    have : j = 0 := by omega
    subst this; exact h
  | succ i ih =>
    rcases Nat.eq_or_lt_of_le le with e | lt
    · subst e; exact h
    · exact ih (by omega) (chain_form_step i t h)

/-! ### Strings of each level of the chain -/

/-- `n` letters `a`. -/
def letters (n : Nat) : List U8 := List.replicate n 97#u8

/-- `n` dashes, each followed by the letter `a`. -/
def dashes : Nat → List U8
  | 0 => []
  | n + 1 => 45#u8 :: 97#u8 :: dashes n

/-- Strings of each level of the chain, which are in exactly the kinds of the
    chain up to the level: a tab first; a space first; a space between
    letters; a digit first; a colon first; an underscore first; and language
    tags of one-letter subtags. -/
def stringAt : Nat → Nat → List U8
  | 0, n => 9#u8 :: letters n
  | 1, n => 32#u8 :: letters n
  | 2, n => 97#u8 :: 32#u8 :: 97#u8 :: letters n
  | 3, n => 49#u8 :: letters n
  | 4, n => 58#u8 :: letters n
  | 5, n => 95#u8 :: letters n
  | _, n => 97#u8 :: dashes n

private theorem letters_val {n : Nat} {b : U8} (h : b ∈ letters n) : b.val = 97 := by
  rw [(List.mem_replicate.mp h).2]; rfl

private theorem dashes_val {n : Nat} {b : U8} (h : b ∈ dashes n) : b.val = 45 ∨ b.val = 97 := by
  induction n with
  | zero => simp [dashes] at h
  | succ n ih =>
    simp only [dashes, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact .inl rfl
    · exact .inr rfl
    · exact ih h

/-- The bytes of the strings of the levels. -/
theorem stringAt_vals {ℓ : Nat} (h : ℓ < 7) (n : Nat) {b : U8} (mem : b ∈ stringAt ℓ n) :
    b.val = 9 ∨ b.val = 32 ∨ b.val = 45 ∨ b.val = 49 ∨ b.val = 58 ∨ b.val = 95 ∨ b.val = 97 := by
  match ℓ, h with
  | 0, _ =>
    rcases List.mem_cons.mp mem with rfl | m
    · exact .inl rfl
    · have := letters_val m; omega
  | 1, _ =>
    rcases List.mem_cons.mp mem with rfl | m
    · exact .inr (.inl rfl)
    · have := letters_val m; omega
  | 2, _ =>
    simp only [stringAt, List.mem_cons] at mem
    rcases mem with rfl | rfl | rfl | m
    · right; right; right; right; right; right; rfl
    · exact .inr (.inl rfl)
    · right; right; right; right; right; right; rfl
    · have := letters_val m; omega
  | 3, _ =>
    rcases List.mem_cons.mp mem with rfl | m
    · right; right; right; left; rfl
    · have := letters_val m; omega
  | 4, _ =>
    rcases List.mem_cons.mp mem with rfl | m
    · right; right; right; right; left; rfl
    · have := letters_val m; omega
  | 5, _ =>
    rcases List.mem_cons.mp mem with rfl | m
    · right; right; right; right; right; left; rfl
    · have := letters_val m; omega
  | 6, _ =>
    rcases List.mem_cons.mp mem with rfl | m
    · right; right; right; right; right; right; rfl
    · have := dashes_val m; omega

theorem stringAt_ascii {ℓ : Nat} (h : ℓ < 7) (n : Nat) :
    ∀ b ∈ stringAt ℓ n, Rowl.Unicode.XmlChar b.val ∧ b.val < 128 := by
  intro b mem
  have := stringAt_vals h n mem
  unfold Rowl.Unicode.XmlChar
  omega

theorem stringAt_xml {ℓ : Nat} (h : ℓ < 7) (n : Nat) : XmlText (stringAt ℓ n) := by
  obtain ⟨text, from0, _⟩ := xml_ascii_chars _ (stringAt_ascii h n)
  exact ⟨text, from0⟩

/-- The level and the count of a string of a level. -/
def levelCount : List U8 → Nat × Nat
  | [] => (7, 0)
  | b :: rest =>
    if b.val = 9 then (0, rest.length)
    else if b.val = 32 then (1, rest.length)
    else if b.val = 49 then (3, rest.length)
    else if b.val = 58 then (4, rest.length)
    else if b.val = 95 then (5, rest.length)
    else if (rest.head?.map (·.val)) = some 32 then (2, rest.length - 2)
    else (6, rest.length / 2)

private theorem dashes_length (n : Nat) : (dashes n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [dashes, List.length_cons, ih]; omega

private theorem dashes_head (n : Nat) : (dashes n).head?.map (·.val) ≠ some 32 := by
  cases n <;> simp [dashes]

theorem levelCount_stringAt {ℓ : Nat} (h : ℓ < 7) (n : Nat) : levelCount (stringAt ℓ n) = (ℓ, n) := by
  match ℓ, h with
  | 0, _ => simp [stringAt, levelCount, letters]
  | 1, _ => simp [stringAt, levelCount, letters]
  | 2, _ => simp [stringAt, levelCount, letters]
  | 3, _ => simp [stringAt, levelCount, letters]
  | 4, _ => simp [stringAt, levelCount, letters]
  | 5, _ => simp [stringAt, levelCount, letters]
  | 6, _ =>
    have := dashes_head n
    simp only [stringAt, levelCount, dashes_length]
    simp [this]

theorem stringAt_injective {ℓ ℓ' n n' : Nat} (h : ℓ < 7) (h' : ℓ' < 7) (same : stringAt ℓ n = stringAt ℓ' n') :
    ℓ = ℓ' ∧ n = n' := by
  have := congrArg levelCount same
  rw [levelCount_stringAt h, levelCount_stringAt h'] at this
  simpa using this

/-- A language tag starts with a letter. -/
theorem language_head {t : List U8} (h : StringSubtype.language.Form t) : ∃ b rest, t = b :: rest ∧ Letter b := by
  obtain ⟨first, rest, ⟨one, _, bytes⟩, _, rfl⟩ := h
  cases first with
  | nil => simp at one
  | cons b first' =>
    refine ⟨b, _, rfl, ?_⟩
    rcases bytes b (by simp) with l | ⟨f, _⟩
    · exact l
    · cases f

private theorem dashes_flatten (n : Nat) :
    dashes n = ((List.replicate n [97#u8]).map (45#u8 :: ·)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp [dashes, List.replicate_succ, ih]

private theorem not_mem_val {l : List U8} {m : U8} (h : ∀ b ∈ l, b.val ≠ m.val) : m ∉ l := fun mem => h m mem rfl

private theorem letters_ne {n : Nat} {b : U8} (m : b ∈ 97#u8 :: letters n) (v : b.val ≠ 97) : False := by
  rcases List.mem_cons.mp m with rfl | m'
  · exact v rfl
  · exact v (letters_val m')

/-- Each string of a level is in the kind of the chain at the level. -/
theorem stringAt_in {ℓ : Nat} (h : ℓ < 7) (n : Nat) : ChainForm ℓ (stringAt ℓ n) := by
  match ℓ, h with
  | 0, _ => exact stringAt_xml (ℓ := 0) (by omega) n
  | 1, _ =>
    refine ⟨stringAt_xml (ℓ := 1) (by omega) n, not_mem_val fun b m => ?_, not_mem_val fun b m => ?_,
      not_mem_val fun b m => ?_⟩ <;>
    · rcases List.mem_cons.mp m with rfl | m'
      · simp
      · rw [letters_val m']; simp
  | 2, _ =>
    have bytes : ∀ b ∈ stringAt 2 n, b.val = 97 ∨ b.val = 32 := by
      intro b m
      simp only [stringAt, List.mem_cons] at m
      rcases m with rfl | rfl | rfl | m'
      · exact .inl rfl
      · exact .inr rfl
      · exact .inl rfl
      · exact .inl (letters_val m')
    refine ⟨⟨stringAt_xml (ℓ := 2) (by omega) n, not_mem_val fun b m => ?_, not_mem_val fun b m => ?_,
      not_mem_val fun b m => ?_⟩, by simp [stringAt], ?_, ?_⟩
    · rcases bytes b m with e | e <;> rw [e] <;> simp
    · rcases bytes b m with e | e <;> rw [e] <;> simp
    · rcases bytes b m with e | e <;> rw [e] <;> simp
    · simp only [stringAt, letters]
      rw [show 97#u8 :: 32#u8 :: 97#u8 :: List.replicate n 97#u8 = [97#u8, 32#u8] ++ List.replicate (n + 1) 97#u8 by
        simp [List.replicate_succ]]
      rw [List.getLast?_append, List.getLast?_replicate]
      simp
    · intro i at_i next
      simp only [stringAt] at at_i next
      match i with
      | 0 => simp at at_i
      | 1 => simp at next
      | j + 2 =>
        simp only [List.getElem?_cons_succ] at at_i
        exact letters_ne (List.mem_of_getElem? at_i) (by simp)
  | 3, _ =>
    refine (ascii_token (stringAt 3 n) fun b m => ?_).mpr ⟨by simp [stringAt], fun c m => ?_⟩
    · rcases List.mem_cons.mp m with rfl | m'
      · simp
      · have := letters_val m'; omega
    · rcases List.mem_cons.mp m with rfl | m'
      · simp [NameChar]
      · rw [letters_val m']; simp [NameChar, NameStartChar]
  | 4, _ =>
    refine (ascii_name (stringAt 4 n) fun b m => ?_).mpr ⟨_, _, rfl, by simp [NameStartChar], fun c m => ?_⟩
    · rcases List.mem_cons.mp m with rfl | m'
      · simp
      · have := letters_val m'; omega
    · rw [letters_val m]; simp [NameChar, NameStartChar]
  | 5, _ =>
    refine ⟨(ascii_name (stringAt 5 n) fun b m => ?_).mpr ⟨_, _, rfl, by simp [NameStartChar], fun c m => ?_⟩,
      not_mem_val fun b m => ?_⟩
    · rcases List.mem_cons.mp m with rfl | m'
      · simp
      · have := letters_val m'; omega
    · rw [letters_val m]; simp [NameChar, NameStartChar]
    · rcases List.mem_cons.mp m with rfl | m'
      · simp
      · rw [letters_val m']; simp
  | 6, _ =>
    refine ⟨[97#u8], List.replicate n [97#u8], ⟨by simp, by simp, fun b m => ?_⟩, fun s m => ?_, ?_⟩
    · simp only [List.mem_singleton] at m; subst m; left; unfold Letter; simp
    · rw [(List.mem_replicate.mp m).2]
      exact ⟨by simp, by simp, fun b m' => by
        simp only [List.mem_singleton] at m'; subst m'; left; unfold Letter; simp⟩
    · show 97#u8 :: dashes n = _
      rw [dashes_flatten]
      rfl

/-- Each string of a level below the last is not in the kind of the chain
    after the level. -/
theorem stringAt_not {ℓ : Nat} (h : ℓ < 6) (n : Nat) : ¬ ChainForm (ℓ + 1) (stringAt ℓ n) := by
  match ℓ, h with
  | 0, _ => exact fun ⟨_, n9, _⟩ => n9 List.mem_cons_self
  | 1, _ => exact fun ⟨_, head, _⟩ => head rfl
  | 2, _ =>
    intro form
    have := token_text_bytes (t := stringAt 2 n) form (b := 32#u8) (by simp [stringAt])
    simp at this
  | 3, _ =>
    intro form
    have ascii : ∀ b ∈ stringAt 3 n, 32 ≤ b.val ∧ b.val < 128 := fun b m => by
      rcases List.mem_cons.mp m with rfl | m'
      · simp
      · have := letters_val m'; omega
    obtain ⟨b, rest, same, start, _⟩ := (ascii_name (stringAt 3 n) ascii).mp form
    obtain ⟨rfl, -⟩ := List.cons.inj same.symm
    simp [NameStartChar] at start
  | 4, _ => exact fun ⟨_, colon⟩ => colon List.mem_cons_self
  | 5, _ =>
    intro form
    obtain ⟨b, rest, same, letter⟩ := language_head form
    obtain ⟨rfl, -⟩ := List.cons.inj same.symm
    simp [Letter] at letter

/-- The strings of a level are in exactly the kinds of the chain up to the
    level. -/
theorem stringAt_form {ℓ r : Nat} (hℓ : ℓ < 7) (hr : r < 7) (n : Nat) : ChainForm r (stringAt ℓ n) ↔ r ≤ ℓ := by
  constructor
  · intro form
    by_contra above
    exact stringAt_not (ℓ := ℓ) (by omega) n (chain_form_mono (by omega) form)
  · intro le
    exact chain_form_mono le (stringAt_in hℓ n)

end Rowl.Strings
