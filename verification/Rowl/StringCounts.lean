import Rowl.WordCounts
import Rowl.Strings
import Rowl.IriResolution
import Mathlib.Order.Interval.Finset.Nat

/-!
How many strings, IRIs and octet sequences have each length, as the length
facets count them (XML Schema 1.1 Part 2 §4.3.1: characters for strings and
IRIs, octets for binary data). The XML characters fall into nine atoms
(`atomRanges`, `atomOf`): tab, line feed and carriage return; the space; `:`;
the ASCII letters; the ASCII digits; `-`; the other name start characters;
the other name characters; and the other XML characters, of the sizes
`atomSize`. The automaton of `lengths::next_text` reads a string by the atoms
of its characters, as five automata side by side (`textNext`), and the rank
of its state (`textRank`) is the deepest subtype of `xsd:string` that the
string is in (`chain_rank`: `Rowl.Strings.ChainForm k` holds exactly for the
ranks `k` up to it). So the strings of a length whose deepest subtype has a
rank from `first` on and before `last` are as many as the words of that
length that the automaton `textDfa first last` takes to such a state
(`text_count`), and the octet sequences of a length are as many as the words
of the automaton `octetDfa` (`octet_count`), `256 ^ ℓ`.
-/
namespace Rowl.StringCounts
open Aeneas Aeneas.Std Rowl.DatatypeMap Rowl.WordCounts
attribute [local instance low] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-! ### Intervals -/

/-- `c` lies in one of the intervals `[a, b]` of the list. -/
def InRanges (rs : List (ℕ × ℕ)) (c : ℕ) : Prop := ∃ r ∈ rs, r.1 ≤ c ∧ c ≤ r.2

/-- The members of the intervals of a list. -/
def rangeSet : List (ℕ × ℕ) → Finset ℕ
  | [] => ∅
  | r :: rs => Finset.Icc r.1 r.2 ∪ rangeSet rs

theorem mem_rangeSet (rs : List (ℕ × ℕ)) (c : ℕ) : c ∈ rangeSet rs ↔ InRanges rs c := by
  induction rs with
  | nil => simp [rangeSet, InRanges]
  | cons r rs ih => simp [rangeSet, InRanges, ih]

/-- Nonempty intervals in increasing order, each after the one before it. -/
def Ascending : List (ℕ × ℕ) → Bool
  | [] => true
  | [r] => decide (r.1 ≤ r.2)
  | r :: s :: rs => decide (r.1 ≤ r.2) && decide (r.2 < s.1) && Ascending (s :: rs)

/-- The number of the members of the intervals of a list. -/
def rangeSize (rs : List (ℕ × ℕ)) : ℕ := (rs.map fun r => r.2 + 1 - r.1).sum

theorem ascending_tail {r : ℕ × ℕ} {rs : List (ℕ × ℕ)} (h : Ascending (r :: rs) = true) : Ascending rs = true := by
  cases rs with
  | nil => rfl
  | cons s rs => simp [Ascending] at h; exact h.2.2

theorem ascending_head {r : ℕ × ℕ} {rs : List (ℕ × ℕ)} (h : Ascending (r :: rs) = true) : r.1 ≤ r.2 := by
  cases rs with
  | nil => simpa [Ascending] using h
  | cons s rs => simp only [Ascending, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1

theorem ascending_above {r : ℕ × ℕ} {rs : List (ℕ × ℕ)} (h : Ascending (r :: rs) = true) {c : ℕ}
    (mem : c ∈ rangeSet rs) : r.2 < c := by
  induction rs generalizing r with
  | nil => simp [rangeSet] at mem
  | cons s rs ih =>
    have hs := ascending_head (ascending_tail h)
    simp only [Ascending, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [rangeSet, Finset.mem_union, Finset.mem_Icc] at mem
    rcases mem with ⟨lo, _⟩ | later
    · omega
    · have := ih h.2 later
      omega

theorem card_rangeSet {rs : List (ℕ × ℕ)} (h : Ascending rs = true) : (rangeSet rs).card = rangeSize rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [rangeSet, Finset.card_union_of_disjoint, Nat.card_Icc, ih (ascending_tail h)]
    · simp [rangeSize]
    · rw [Finset.disjoint_left]
      intro c inR inRest
      have := ascending_above h inRest
      simp only [Finset.mem_Icc] at inR
      omega

/-! ### The atoms of the XML characters -/

/-- The intervals of the atoms: tab, line feed and carriage return; the space;
    `:`; the ASCII letters; the ASCII digits; `-`; the other name start
    characters; the other name characters; and the other XML characters. -/
def atomRanges : ℕ → List (ℕ × ℕ)
  | 0 => [(9, 10), (13, 13)]
  | 1 => [(32, 32)]
  | 2 => [(58, 58)]
  | 3 => [(65, 90), (97, 122)]
  | 4 => [(48, 57)]
  | 5 => [(45, 45)]
  | 6 => [(0x5F, 0x5F), (0xC0, 0xD6), (0xD8, 0xF6), (0xF8, 0x2FF), (0x370, 0x37D), (0x37F, 0x1FFF),
      (0x200C, 0x200D), (0x2070, 0x218F), (0x2C00, 0x2FEF), (0x3001, 0xD7FF), (0xF900, 0xFDCF), (0xFDF0, 0xFFFD),
      (0x10000, 0xEFFFF)]
  | 7 => [(0x2E, 0x2E), (0xB7, 0xB7), (0x300, 0x36F), (0x203F, 0x2040)]
  | _ => [(0x21, 0x2C), (0x2F, 0x2F), (0x3B, 0x40), (0x5B, 0x5E), (0x60, 0x60), (0x7B, 0xB6), (0xB8, 0xBF),
      (0xD7, 0xD7), (0xF7, 0xF7), (0x37E, 0x37E), (0x2000, 0x200B), (0x200E, 0x203E), (0x2041, 0x206F),
      (0x2190, 0x2BFF), (0x2FF0, 0x3000), (0xE000, 0xF8FF), (0xFDD0, 0xFDEF), (0xF0000, 0x10FFFF)]

/-- The sizes of the atoms. -/
def atomSize : ℕ → ℕ
  | 0 => 3
  | 1 => 1
  | 2 => 1
  | 3 => 52
  | 4 => 10
  | 5 => 1
  | 6 => 971453
  | 7 => 116
  | _ => 140396

theorem atom_card (a : ℕ) : (rangeSet (atomRanges a)).card = atomSize a := by
  match a with
  | 0 => rw [card_rangeSet (by decide)]; rfl
  | 1 => rw [card_rangeSet (by decide)]; rfl
  | 2 => rw [card_rangeSet (by decide)]; rfl
  | 3 => rw [card_rangeSet (by decide)]; rfl
  | 4 => rw [card_rangeSet (by decide)]; rfl
  | 5 => rw [card_rangeSet (by decide)]; rfl
  | 6 => rw [card_rangeSet (by decide)]; rfl
  | 7 => rw [card_rangeSet (by decide)]; rfl
  | n + 8 =>
    rw [show atomRanges (n + 8) = atomRanges 8 from rfl, show atomSize (n + 8) = atomSize 8 from rfl,
      card_rangeSet (by decide)]
    rfl

/-- The atom of a character. -/
noncomputable def atomOf (c : ℕ) : ℕ :=
  if c = 9 ∨ c = 10 ∨ c = 13 then 0
  else if c = 32 then 1
  else if c = 58 then 2
  else if (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) then 3
  else if 48 ≤ c ∧ c ≤ 57 then 4
  else if c = 45 then 5
  else if NameStartChar c then 6
  else if NameChar c then 7
  else 8

theorem atomOf_lt (c : ℕ) : atomOf c < 9 := by
  unfold atomOf; split_ifs <;> (try simp only [NameChar, NameStartChar, iff_false, iff_true, false_iff, true_iff, true_or, or_true, false_or, or_false] at *) <;> omega

set_option maxHeartbeats 8000000 in
/-- A character of an atom is an XML character. -/
theorem atom_xml {a c : ℕ} (h : InRanges (atomRanges a) c) : Rowl.Unicode.XmlChar c := by
  match a with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | _ + 8 =>
    simp only [InRanges, atomRanges, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left] at h
    unfold Rowl.Unicode.XmlChar
    omega

set_option maxHeartbeats 8000000 in
/-- An XML character is in exactly the atom `atomOf` names. -/
theorem atom_iff {c : ℕ} (xml : Rowl.Unicode.XmlChar c) (a : ℕ) (ha : a < 9) :
    InRanges (atomRanges a) c ↔ atomOf c = a := by
  unfold Rowl.Unicode.XmlChar at xml
  unfold atomOf
  match a with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 =>
    simp only [InRanges, atomRanges, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left]
    split_ifs <;> (try simp only [NameChar, NameStartChar, iff_false, iff_true, false_iff, true_iff, true_or, or_true, false_or, or_false] at *) <;> omega

theorem atomOf_spec {c : ℕ} (xml : Rowl.Unicode.XmlChar c) : InRanges (atomRanges (atomOf c)) c :=
  (atom_iff xml (atomOf c) (atomOf_lt c)).mpr rfl

/-! ### What the atoms tell -/

theorem atom_zero {c : ℕ} : atomOf c = 0 ↔ c = 9 ∨ c = 10 ∨ c = 13 := by
  unfold atomOf; split_ifs <;> (try simp only [NameChar, NameStartChar, iff_false, iff_true, false_iff, true_iff, true_or, or_true, false_or, or_false] at *) <;> omega

theorem atom_one {c : ℕ} : atomOf c = 1 ↔ c = 32 := by
  unfold atomOf; split_ifs <;> (try simp only [NameChar, NameStartChar, iff_false, iff_true, false_iff, true_iff, true_or, or_true, false_or, or_false] at *) <;> omega

theorem atom_two {c : ℕ} : atomOf c = 2 ↔ c = 58 := by
  unfold atomOf; split_ifs <;> (try simp only [NameChar, NameStartChar, iff_false, iff_true, false_iff, true_iff, true_or, or_true, false_or, or_false] at *) <;> omega

theorem atom_three {c : ℕ} : atomOf c = 3 ↔ (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) := by
  unfold atomOf; split_ifs <;> (try simp only [NameChar, NameStartChar, iff_false, iff_true, false_iff, true_iff, true_or, or_true, false_or, or_false] at *) <;> omega

theorem atom_four {c : ℕ} : atomOf c = 4 ↔ 48 ≤ c ∧ c ≤ 57 := by
  unfold atomOf; split_ifs <;> (try simp only [NameChar, NameStartChar, iff_false, iff_true, false_iff, true_iff, true_or, or_true, false_or, or_false] at *) <;> omega

theorem atom_five {c : ℕ} : atomOf c = 5 ↔ c = 45 := by
  unfold atomOf; split_ifs <;> (try simp only [NameChar, NameStartChar, iff_false, iff_true, false_iff, true_iff, true_or, or_true, false_or, or_false] at *) <;> omega

set_option maxHeartbeats 8000000 in
/-- The name characters are the characters of the atoms from 2 to 7. -/
theorem atom_name {c : ℕ} : NameChar c ↔ 2 ≤ atomOf c ∧ atomOf c ≤ 7 := by
  unfold atomOf; split_ifs <;> (try simp only [NameChar, NameStartChar, iff_false, iff_true, false_iff, true_iff, true_or, or_true, false_or, or_false] at *) <;> omega

set_option maxHeartbeats 8000000 in
/-- The name start characters are the characters of the atoms 2, 3 and 6. -/
theorem atom_start {c : ℕ} : NameStartChar c ↔ atomOf c = 2 ∨ atomOf c = 3 ∨ atomOf c = 6 := by
  unfold atomOf; split_ifs <;> (try simp only [NameChar, NameStartChar, iff_false, iff_true, false_iff, true_iff, true_or, or_true, false_or, or_false] at *) <;> omega

/-! ### The automaton of the strings -/

/-- Breaks: 0 without a tab, line feed or carriage return, 1 with one. -/
def nextBreaks (s a : ℕ) : ℕ := if a = 0 then 1 else s

/-- Spaces: 0 for the empty string, 1 after a character other than a space, 2
    after a space, and 3 once a space came first or two spaces in a row. -/
def nextSpaces (s a : ℕ) : ℕ := if s = 3 then 3 else if a = 1 then (if s = 1 then 2 else 3) else 1

/-- Names: 0 for the empty string, 1 for name characters after a first one
    that does not start a name, 2 for name characters after a first one that
    does, and 3 once another character came. -/
def nextNames (s a : ℕ) : ℕ :=
  if ¬ (2 ≤ a ∧ a ≤ 7) then 3 else if s = 0 then (if a = 2 ∨ a = 3 ∨ a = 6 then 2 else 1) else s

/-- Colons: 0 without `:`, 1 with one. -/
def nextColons (s a : ℕ) : ℕ := if a = 2 then 1 else s

/-- The language tag: from 0 to 8 the characters of the first subtag, from 9
    to 17 nine more than those of a later subtag after `-`, and 18 once it is
    no language tag. -/
def nextTag (s a : ℕ) : ℕ :=
  if 18 ≤ s then 18
  else if a = 5 then (if s = 0 ∨ s = 9 then 18 else 9)
  else if a = 3 ∨ (a = 4 ∧ 9 ≤ s) then (if s = 8 ∨ s = 17 then 18 else s + 1)
  else 18

/-- The state of the strings with the five states of breaks, spaces, names,
    colons and the language tag. -/
def joinState (b s n c t : ℕ) : ℕ := (((b * 4 + s) * 4 + n) * 2 + c) * 19 + t

/-- The state after an atom (`lengths::next_text`). -/
def textNext (q a : ℕ) : ℕ :=
  joinState (nextBreaks (q / 19 / 2 / 4 / 4) a) (nextSpaces (q / 19 / 2 / 4 % 4) a) (nextNames (q / 19 / 2 % 4) a)
    (nextColons (q / 19 % 2) a) (nextTag (q % 19) a)

/-- The rank of a state (`lengths::rank`). -/
def textRank (q : ℕ) : ℕ :=
  if q / 19 / 2 / 4 / 4 ≠ 0 then 0
  else if 1 < q / 19 / 2 / 4 % 4 then 1
  else if q / 19 / 2 % 4 = 0 ∨ q / 19 / 2 % 4 = 3 then 2
  else if q / 19 / 2 % 4 = 1 then 3
  else if q / 19 % 2 ≠ 0 then 4
  else if q % 19 = 0 ∨ q % 19 = 9 ∨ q % 19 = 18 then 5
  else 6

theorem textRank_le (q : ℕ) : textRank q ≤ 6 := by
  unfold textRank; split_ifs <;> omega

/-- The parts of a state of the strings. -/
theorem join_parts {b s n c t : ℕ} (hs : s < 4) (hn : n < 4) (hc : c < 2) (ht : t < 19) :
    joinState b s n c t / 19 / 2 / 4 / 4 = b ∧ joinState b s n c t / 19 / 2 / 4 % 4 = s ∧
      joinState b s n c t / 19 / 2 % 4 = n ∧ joinState b s n c t / 19 % 2 = c ∧ joinState b s n c t % 19 = t := by
  unfold joinState
  omega

theorem join_lt {b s n c t : ℕ} (hb : b < 2) (hs : s < 4) (hn : n < 4) (hc : c < 2) (ht : t < 19) :
    joinState b s n c t < 1216 := by
  unfold joinState
  omega

theorem next_bounds (b s n c t a : ℕ) (hb : b < 2) (hn : n < 4) (hc : c < 2) (ht : t < 19) :
    nextBreaks b a < 2 ∧ nextSpaces s a < 4 ∧ nextNames n a < 4 ∧ nextColons c a < 2 ∧ nextTag t a < 19 := by
  unfold nextBreaks nextSpaces nextNames nextColons nextTag
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega

theorem textNext_join {b s n c t : ℕ} (a : ℕ) (hs : s < 4) (hn : n < 4) (hc : c < 2) (ht : t < 19) :
    textNext (joinState b s n c t) a =
      joinState (nextBreaks b a) (nextSpaces s a) (nextNames n a) (nextColons c a) (nextTag t a) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := join_parts hs hn hc ht
  rw [textNext, e1, e2, e3, e4, e5]

theorem textNext_lt (q a : ℕ) (hq : q < 1216) : textNext q a < 1216 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := next_bounds (q / 19 / 2 / 4 / 4) (q / 19 / 2 / 4 % 4) (q / 19 / 2 % 4)
    (q / 19 % 2) (q % 19) a (by omega) (by omega) (by omega) (by omega)
  exact join_lt h1 h2 h3 h4 h5

/-- The state after reading a word of characters by their atoms. -/
noncomputable def runWith (next : ℕ → ℕ → ℕ) : ℕ → List ℕ → ℕ
  | s, [] => s
  | s, c :: w => runWith next (next s (atomOf c)) w

theorem run_join (w : List ℕ) {b s n c t : ℕ} (hb : b < 2) (hs : s < 4) (hn : n < 4) (hc : c < 2) (ht : t < 19) :
    runWith textNext (joinState b s n c t) w = joinState (runWith nextBreaks b w) (runWith nextSpaces s w)
      (runWith nextNames n w) (runWith nextColons c w) (runWith nextTag t w) := by
  induction w generalizing b s n c t with
  | nil => rfl
  | cons x w ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := next_bounds b s n c t (atomOf x) hb hn hc ht
    simp only [runWith, textNext_join _ hs hn hc ht]
    exact ih h1 h2 h3 h4 h5

/-! ### The automata -/

/-- The automaton of the strings, counting the words that end in a state of a
    rank from `first` on and before `last`. -/
def textDfa (first last : ℕ) : Dfa where
  atoms := 9
  atom a := rangeSet (atomRanges a)
  next q a := some (textNext q a)
  accept q := decide (first ≤ textRank q ∧ textRank q < last)

theorem text_disjoint (first last : ℕ) : (textDfa first last).Disjoint := by
  intro a b c ha hb ina inb
  simp only [textDfa, mem_rangeSet] at ina inb ha hb
  have xml := atom_xml ina
  rw [atom_iff xml a ha] at ina
  rw [atom_iff xml b hb] at inb
  omega

/-- The automaton takes a word from a state exactly when its letters are XML
    characters and it ends in a state of a rank from `first` on and before
    `last`. -/
theorem text_accepts (first last : ℕ) (q : ℕ) (w : List ℕ) :
    (textDfa first last).Accepts q w ↔ (∀ c ∈ w, Rowl.Unicode.XmlChar c) ∧
      first ≤ textRank (runWith textNext q w) ∧ textRank (runWith textNext q w) < last := by
  induction w generalizing q with
  | nil => simp [Dfa.Accepts, textDfa, runWith]
  | cons x w ih =>
    simp only [Dfa.Accepts, textDfa, mem_rangeSet, Option.some.injEq, exists_eq_left', List.mem_cons,
      forall_eq_or_imp, runWith]
    constructor
    · rintro ⟨a, ha, inA, acc⟩
      have xml := atom_xml inA
      have e := (atom_iff xml a ha).mp inA
      subst e
      have := (ih _).mp acc
      exact ⟨⟨xml, this.1⟩, this.2⟩
    · rintro ⟨⟨xml, rest⟩, ranks⟩
      exact ⟨atomOf x, atomOf_lt x, atomOf_spec xml, (ih _).mpr ⟨rest, ranks⟩⟩

/-- The automaton of the octet sequences. -/
def octetDfa : Dfa where
  atoms := 1
  atom _ := Finset.range 256
  next _ _ := some 0
  accept _ := true

theorem octet_disjoint : octetDfa.Disjoint := by
  intro a b c ha hb _ _
  simp only [octetDfa] at ha hb
  omega

theorem octet_accepts (q : ℕ) (w : List ℕ) : octetDfa.Accepts q w ↔ ∀ c ∈ w, c < 256 := by
  induction w generalizing q with
  | nil => simp [Dfa.Accepts, octetDfa]
  | cons x w ih =>
    simp only [Dfa.Accepts, octetDfa, Finset.mem_range, Option.some.injEq, exists_eq_left', List.mem_cons,
      forall_eq_or_imp]
    constructor
    · rintro ⟨a, ha, hx, acc⟩
      exact ⟨hx, (ih 0).mp acc⟩
    · rintro ⟨hx, rest⟩
      exact ⟨0, by omega, hx, (ih 0).mpr rest⟩

theorem octet_count (ℓ : ℕ) : octetDfa.count 0 ℓ = 256 ^ ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [Dfa.count]
    simp only [show octetDfa.atoms = 1 from rfl, show ∀ a, octetDfa.atom a = Finset.range 256 from fun _ => rfl,
      show ∀ q a, octetDfa.next q a = some 0 from fun _ _ => rfl, ih]
    simp [pow_succ, mul_comm]


/-! ### UTF-8 -/

open Rowl.IriResolution (utf8)

/-- The byte of a number below 256. -/
def toByte (n : ℕ) : U8 := ⟨BitVec.ofNat 8 n⟩

theorem toByte_val {n : ℕ} (h : n < 256) : (toByte n).val = n := by
  show (BitVec.ofNat 8 n).toNat = n
  rw [BitVec.toNat_ofNat]
  omega

theorem toByte_of_val (b : U8) : toByte b.val = b := by
  apply UScalar.eq_of_val_eq
  exact toByte_val b.hBounds

theorem toByte_inj {m n : ℕ} (hm : m < 256) (hn : n < 256) : toByte m = toByte n ↔ m = n := by
  constructor
  · intro e
    have := congrArg UScalar.val e
    rwa [toByte_val hm, toByte_val hn] at this
  · rintro rfl; rfl

/-- The UTF-8 bytes of a word of characters. -/
def encodeText (w : List ℕ) : List U8 := (w.flatMap utf8).map toByte

theorem encodeText_nil : encodeText [] = [] := rfl

theorem encodeText_cons (c : ℕ) (w : List ℕ) : encodeText (c :: w) = (utf8 c).map toByte ++ encodeText w := by
  simp [encodeText]

theorem encodeText_append (u v : List ℕ) : encodeText (u ++ v) = encodeText u ++ encodeText v := by
  simp [encodeText]

theorem utf8_ascii {c : ℕ} (h : c < 128) : utf8 c = [c] := by
  simp [utf8, h]

/-- The bytes of a character from 128 on: each from 128 on and below 256, the
    first from 192 on and the last below 192. -/
theorem utf8_high {c : ℕ} (low : 128 ≤ c) (high : c ≤ 1114111) :
    ∃ b rest, utf8 c = b :: rest ∧ 192 ≤ b ∧ b < 256 ∧ (∀ x ∈ rest, 128 ≤ x ∧ x < 192) ∧
      ((utf8 c).getLast?).all (fun x => 128 ≤ x ∧ x < 192) := by
  unfold utf8
  rw [if_neg (by omega)]
  split_ifs with h2 h3
  · refine ⟨_, _, rfl, by omega, by omega, ?_, ?_⟩
    · simp only [List.mem_singleton]; omega
    · simp; omega
  · refine ⟨_, _, rfl, by omega, by omega, ?_, ?_⟩
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]; omega
    · simp; omega
  · refine ⟨_, _, rfl, by omega, by omega, ?_, ?_⟩
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]; omega
    · simp; omega

theorem utf8_lt {c : ℕ} (high : c ≤ 1114111) : ∀ x ∈ utf8 c, x < 256 := by
  by_cases ascii : c < 128
  · rw [utf8_ascii ascii]; simp; omega
  · obtain ⟨b, rest, e, _, hb, hr, _⟩ := utf8_high (by omega) high
    rw [e]
    intro x mem
    rcases List.mem_cons.mp mem with rfl | m
    · exact hb
    · exact (hr x m).2.trans (by omega)

theorem xml_high {c : ℕ} (h : Rowl.Unicode.XmlChar c) : c ≤ 1114111 := by
  unfold Rowl.Unicode.XmlChar at h; omega

theorem xml_scalar {c : ℕ} (h : Rowl.Unicode.XmlChar c) : Rowl.Encoding.Scalar c := by
  unfold Rowl.Unicode.XmlChar at h; unfold Rowl.Encoding.Scalar; omega

theorem encodeText_vals {w : List ℕ} (high : ∀ c ∈ w, c ≤ 1114111) :
    (encodeText w).map (·.val) = w.flatMap utf8 := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [encodeText_cons, List.map_append, ih (fun d m => high d (List.mem_cons_of_mem c m)), List.flatMap_cons]
    congr 1
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (utf8 c)]
    apply List.map_congr_left
    intro x mem
    exact toByte_val (utf8_lt (high c (by simp)) x mem)

private theorem text_utf8 {bs : List U8} {position : Nat} {text : List (Nat × Nat)}
    (valid : Rowl.Unicode.TextFrom bs position text) : Rowl.Regular.Utf8From bs position (text.map Prod.fst) := by
  induction valid with
  | endOfInput => exact .endOfInput
  | character unit _ positive fits _ ih => exact .character unit positive fits ih

private theorem text_xml {bs : List U8} {position : Nat} {text : List (Nat × Nat)}
    (valid : Rowl.Unicode.TextFrom bs position text) : ∀ c ∈ text.map Prod.fst, Rowl.Unicode.XmlChar c := by
  induction valid with
  | endOfInput => simp
  | character _ xml _ _ _ ih =>
    intro c mem
    simp only [List.map_cons, List.mem_cons] at mem
    rcases mem with rfl | m
    · exact xml
    · exact ih c m

private theorem utf8_text {bs : List U8} {position : Nat} {w : List ℕ} (valid : Rowl.Regular.Utf8From bs position w)
    (xml : ∀ c ∈ w, Rowl.Unicode.XmlChar c) :
    ∃ text, Rowl.Unicode.TextFrom bs position text ∧ text.map Prod.fst = w := by
  induction valid with
  | endOfInput => exact ⟨[], .endOfInput, rfl⟩
  | @character offset cp width tail unit positive fits _ ih =>
    obtain ⟨text, from', same⟩ := ih (fun c m => xml c (List.mem_cons_of_mem cp m))
    exact ⟨(cp, offset) :: text, .character unit (xml cp (by simp)) positive fits from', by simp [same]⟩

/-- The UTF-8 bytes of XML characters are XML text of those characters. -/
theorem encode_chars {w : List ℕ} (xml : ∀ c ∈ w, Rowl.Unicode.XmlChar c) : TextChars (encodeText w) w := by
  have valid := Rowl.IriResolution.utf8_encoded (fun c m => xml_scalar (xml c m))
    (encodeText_vals (fun c m => xml_high (xml c m)))
  obtain ⟨text, from0, same⟩ := utf8_text valid xml
  exact ⟨text, from0, same⟩

/-- XML text is the UTF-8 bytes of its characters, which are XML characters. -/
theorem chars_encode {t : List U8} {w : List ℕ} (h : TextChars t w) :
    (∀ c ∈ w, Rowl.Unicode.XmlChar c) ∧ t = encodeText w := by
  obtain ⟨text, from0, rfl⟩ := h
  refine ⟨text_xml from0, ?_⟩
  have decoded := (Rowl.IriResolution.utf8_decoded (text_utf8 from0)).1
  rw [List.drop_zero] at decoded
  calc t = (t.map (·.val)).map toByte := by rw [List.map_map]; conv_lhs => rw [← List.map_id t]
                                            exact (List.map_congr_left fun b _ => (toByte_of_val b).symm)
    _ = encodeText (text.map Prod.fst) := by rw [decoded]; rfl

/-- XML text has one sequence of characters. -/
theorem chars_unique {t : List U8} {v w : List ℕ} (hv : TextChars t v) (hw : TextChars t w) : v = w := by
  obtain ⟨t1, f1, rfl⟩ := hv
  obtain ⟨t2, f2, rfl⟩ := hw
  rw [Rowl.Strings.text_from_unique f1 f2]

theorem encodeText_injective {v w : List ℕ} (xv : ∀ c ∈ v, Rowl.Unicode.XmlChar c)
    (xw : ∀ c ∈ w, Rowl.Unicode.XmlChar c) (same : encodeText v = encodeText w) : v = w :=
  chars_unique (encode_chars xv) (same ▸ encode_chars xw)

/-- An ASCII byte is among the bytes of a character exactly when it is the
    character. -/
theorem ascii_in_utf8 {c n : ℕ} (high : c ≤ 1114111) (ascii : n < 128) :
    toByte n ∈ (utf8 c).map toByte ↔ n = c := by
  by_cases small : c < 128
  · rw [utf8_ascii small]
    simp only [List.map_cons, List.map_nil, List.mem_singleton]
    rw [toByte_inj (by omega) (by omega)]
  · obtain ⟨b, rest, e, hb1, hb2, hr, _⟩ := utf8_high (by omega) high
    rw [e]
    constructor
    · intro mem
      obtain ⟨x, mx, same⟩ := List.mem_map.mp mem
      have lt : x < 256 := by
        rcases List.mem_cons.mp mx with rfl | m
        · exact hb2
        · exact (hr x m).2.trans (by omega)
      have big : 128 ≤ x := by
        rcases List.mem_cons.mp mx with rfl | m
        · omega
        · exact (hr x m).1
      rw [toByte_inj lt (by omega)] at same
      omega
    · intro e'; omega

/-- An ASCII byte is in the UTF-8 bytes of characters exactly when its
    character is among them. -/
theorem ascii_mem {w : List ℕ} (high : ∀ c ∈ w, c ≤ 1114111) {n : ℕ} (ascii : n < 128) :
    toByte n ∈ encodeText w ↔ n ∈ w := by
  induction w with
  | nil => simp [encodeText_nil]
  | cons c w ih =>
    rw [encodeText_cons, List.mem_append, ih (fun d m => high d (List.mem_cons_of_mem c m)), List.mem_cons,
      ascii_in_utf8 (high c (by simp)) ascii]

/-- The first byte is a space exactly when the first character is. -/
theorem head_space {w : List ℕ} (high : ∀ c ∈ w, c ≤ 1114111) :
    (encodeText w).head? = some (toByte 32) ↔ w.head? = some 32 := by
  cases w with
  | nil => simp [encodeText_nil]
  | cons c w =>
    rw [encodeText_cons]
    by_cases small : c < 128
    · rw [utf8_ascii small]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.head?_cons,
        Option.some.injEq]
      rw [toByte_inj (by omega) (by omega)]
    · obtain ⟨b, rest, e, hb1, hb2, _, _⟩ := utf8_high (by omega) (high c (by simp))
      rw [e]
      simp only [List.map_cons, List.cons_append, List.head?_cons, Option.some.injEq]
      rw [toByte_inj hb2 (by omega)]
      omega

/-- The last byte of a character: the character itself below 128, and a
    continuation byte otherwise. -/
theorem utf8_last {c : ℕ} (high : c ≤ 1114111) :
    ∃ x, (utf8 c).getLast? = some x ∧ x < 256 ∧ (c < 128 → x = c) ∧ (128 ≤ c → 128 ≤ x ∧ x < 192) := by
  by_cases small : c < 128
  · exact ⟨c, by rw [utf8_ascii small]; rfl, by omega, fun _ => rfl, fun h => absurd h (by omega)⟩
  · obtain ⟨b, rest, e, _, _, _, last⟩ := utf8_high (by omega) high
    cases hl : (utf8 c).getLast? with
    | none => rw [e] at hl; simp at hl
    | some x =>
      rw [hl] at last
      simp only [Option.all_some, decide_eq_true_eq] at last
      exact ⟨x, rfl, by omega, fun h => absurd h small, fun _ => last⟩

/-- The last byte is a space exactly when the last character is. -/
theorem last_space {w : List ℕ} (high : ∀ c ∈ w, c ≤ 1114111) :
    (encodeText w).getLast? = some (toByte 32) ↔ w.getLast? = some 32 := by
  induction w using List.reverseRecOn with
  | nil => simp [encodeText_nil]
  | append_singleton w c _ =>
    have hc := high c (by simp)
    have encoded : encodeText [c] = (utf8 c).map toByte := by simp [encodeText]
    obtain ⟨x, hx, lt, low, big⟩ := utf8_last hc
    rw [encodeText_append, encoded, List.getLast?_append, List.getLast?_append, List.getLast?_map, hx]
    simp only [List.getLast?_singleton, Option.map_some, Option.some_or, Option.some.injEq]
    rw [toByte_inj lt (by omega)]
    by_cases small : c < 128
    · rw [low small]
    · have := big (by omega)
      omega

/-- `x` twice in a row. -/
def Twice {α : Type} (x : α) : List α → Prop
  | [] => False
  | a :: l => (a = x ∧ l.head? = some x) ∨ Twice x l

theorem twice_iff {α : Type} (x : α) (l : List α) : Twice x l ↔ ∃ i, l[i]? = some x ∧ l[i + 1]? = some x := by
  induction l with
  | nil => simp [Twice]
  | cons a l ih =>
    rw [Twice, ih]
    constructor
    · rintro (⟨rfl, h⟩ | ⟨i, h1, h2⟩)
      · refine ⟨0, rfl, ?_⟩
        simpa [List.head?_eq_getElem?] using h
      · exact ⟨i + 1, by simpa using h1, by simpa using h2⟩
    · rintro ⟨i, h1, h2⟩
      cases i with
      | zero =>
        left
        refine ⟨by simpa using h1, ?_⟩
        simpa [List.head?_eq_getElem?] using h2
      | succ i => exact .inr ⟨i, by simpa using h1, by simpa using h2⟩

theorem twice_append_free {α : Type} {x : α} {pre : List α} (free : x ∉ pre) (l : List α) :
    Twice x (pre ++ l) ↔ Twice x l := by
  induction pre with
  | nil => rfl
  | cons a pre ih =>
    simp only [List.mem_cons, not_or] at free
    rw [List.cons_append, Twice, ih free.2]
    constructor
    · rintro (⟨e, _⟩ | h)
      · exact absurd e.symm free.1
      · exact h
    · exact .inr

/-- Two spaces in a row among the bytes exactly when among the characters. -/
theorem twice_space {w : List ℕ} (high : ∀ c ∈ w, c ≤ 1114111) :
    Twice (toByte 32) (encodeText w) ↔ Twice 32 w := by
  induction w with
  | nil => simp [encodeText_nil, Twice]
  | cons c w ih =>
    have hw : ∀ d ∈ w, d ≤ 1114111 := fun d m => high d (List.mem_cons_of_mem c m)
    rw [encodeText_cons, Twice]
    by_cases small : c < 128
    · rw [utf8_ascii small]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Twice]
      rw [toByte_inj (by omega) (by omega), head_space hw, ih hw]
    · obtain ⟨b, rest, e, hb1, hb2, hr, _⟩ := utf8_high (by omega) (high c (by simp))
      rw [twice_append_free, ih hw]
      · constructor
        · exact .inr
        · rintro (⟨e', _⟩ | h)
          · omega
          · exact h
      · rw [e]
        intro mem
        obtain ⟨y, my, same⟩ := List.mem_map.mp mem
        have lt : y < 256 := by
          rcases List.mem_cons.mp my with rfl | m
          · exact hb2
          · exact (hr y m).2.trans (by omega)
        have big : 128 ≤ y := by
          rcases List.mem_cons.mp my with rfl | m
          · omega
          · exact (hr y m).1
        rw [toByte_inj lt (by omega)] at same
        omega


/-! ### The five automata on characters -/

theorem run_breaks (w : List ℕ) (b : ℕ) :
    runWith nextBreaks b w = if ∃ c ∈ w, atomOf c = 0 then 1 else b := by
  induction w generalizing b with
  | nil => simp [runWith]
  | cons c w ih =>
    rw [runWith, ih]
    by_cases h : atomOf c = 0 <;> simp [nextBreaks, h]

theorem run_colons (w : List ℕ) (s : ℕ) :
    runWith nextColons s w = if ∃ c ∈ w, atomOf c = 2 then 1 else s := by
  induction w generalizing s with
  | nil => simp [runWith]
  | cons c w ih =>
    rw [runWith, ih]
    by_cases h : atomOf c = 2 <;> simp [nextColons, h]

theorem run_names_stay (w : List ℕ) {n : ℕ} (hn : n = 1 ∨ n = 2 ∨ n = 3) :
    runWith nextNames n w = if ∀ c ∈ w, 2 ≤ atomOf c ∧ atomOf c ≤ 7 then n else 3 := by
  induction w generalizing n with
  | nil => simp [runWith]
  | cons c w ih =>
    rw [runWith]
    by_cases h : 2 ≤ atomOf c ∧ atomOf c ≤ 7
    · have e : nextNames n (atomOf c) = n := by
        unfold nextNames; rw [if_neg (not_not.mpr h), if_neg (by omega)]
      rw [e, ih hn]
      simp [h]
    · have e : nextNames n (atomOf c) = 3 := by unfold nextNames; rw [if_pos h]
      rw [e, ih (by omega)]
      simp only [List.mem_cons, forall_eq_or_imp, h, false_and, if_false]
      split_ifs <;> rfl

/-- The names state of a string: 0 when empty, 3 with a character that is no
    name character, and otherwise 2 when the first starts a name and 1 when
    not. -/
theorem run_names (w : List ℕ) :
    runWith nextNames 0 w = if w = [] then 0 else if ∀ c ∈ w, 2 ≤ atomOf c ∧ atomOf c ≤ 7 then
      (if w.head? = some 58 ∨ (∃ c, w.head? = some c ∧ (atomOf c = 3 ∨ atomOf c = 6)) then 2 else 1) else 3 := by
  cases w with
  | nil => simp [runWith]
  | cons c w =>
    rw [runWith]
    simp only [reduceCtorEq, if_false, List.head?_cons, Option.some.injEq, exists_eq_left']
    by_cases isName : 2 ≤ atomOf c ∧ atomOf c ≤ 7
    · by_cases start : atomOf c = 2 ∨ atomOf c = 3 ∨ atomOf c = 6
      · have e : nextNames 0 (atomOf c) = 2 := by
          unfold nextNames; rw [if_neg (not_not.mpr isName), if_pos rfl, if_pos start]
        rw [e, run_names_stay w (by omega)]
        have start' : c = 58 ∨ atomOf c = 3 ∨ atomOf c = 6 := by rw [← atom_two]; exact start
        simp only [List.mem_cons, forall_eq_or_imp, isName, true_and, start', if_true]
      · have e : nextNames 0 (atomOf c) = 1 := by
          unfold nextNames; rw [if_neg (not_not.mpr isName), if_pos rfl, if_neg start]
        rw [e, run_names_stay w (by omega)]
        have start' : ¬ (c = 58 ∨ atomOf c = 3 ∨ atomOf c = 6) := by rw [← atom_two]; exact start
        simp only [List.mem_cons, forall_eq_or_imp, isName, true_and, start', if_false]
    · have e : nextNames 0 (atomOf c) = 3 := by unfold nextNames; rw [if_pos isName]
      rw [e, run_names_stay w (by omega)]
      simp only [List.mem_cons, forall_eq_or_imp, isName, false_and, if_false, ite_self]

/-- Where spaces may come in the rest of a string after the spaces state:
    nothing read yet (0), a character other than a space last (1), a space
    last (2); never after a space first or two spaces in a row. -/
def SpacesFrom : ℕ → List ℕ → Prop
  | 0, w => w.head? ≠ some 32 ∧ w.getLast? ≠ some 32 ∧ ¬ Twice 32 w
  | 1, w => w.getLast? ≠ some 32 ∧ ¬ Twice 32 w
  | 2, w => w ≠ [] ∧ w.head? ≠ some 32 ∧ w.getLast? ≠ some 32 ∧ ¬ Twice 32 w
  | _, _ => False

theorem last_cons (c : ℕ) (w : List ℕ) : (c :: w).getLast? = if w = [] then some c else w.getLast? := by
  cases w with
  | nil => rfl
  | cons d w => simp [List.getLast?_cons]

theorem run_spaces (w : List ℕ) (s : ℕ) (hs : s < 4) : runWith nextSpaces s w ≤ 1 ↔ SpacesFrom s w := by
  induction w generalizing s with
  | nil =>
    simp only [runWith]
    match s, hs with
    | 0, _ => simp [SpacesFrom, Twice]
    | 1, _ => simp [SpacesFrom, Twice]
    | 2, _ => simp [SpacesFrom]
    | 3, _ => simp [SpacesFrom]
  | cons c w ih =>
    rw [runWith, ih _ (by unfold nextSpaces; split_ifs <;> omega)]
    by_cases space : c = 32
    · have a1 : atomOf c = 1 := atom_one.mpr space
      subst space
      match s, hs with
      | 0, _ =>
        have e : nextSpaces 0 (atomOf 32) = 3 := by rw [a1]; rfl
        rw [e]; simp [SpacesFrom]
      | 1, _ =>
        have e : nextSpaces 1 (atomOf 32) = 2 := by rw [a1]; rfl
        rw [e]
        simp only [SpacesFrom, Twice, last_cons]
        cases w with
        | nil => simp
        | cons d w =>
          simp only [reduceCtorEq, if_false, List.head?_cons, Option.some.injEq, true_and, ne_eq,
            not_false_eq_true, not_or]
          tauto
      | 2, _ =>
        have e : nextSpaces 2 (atomOf 32) = 3 := by rw [a1]; rfl
        rw [e]; simp [SpacesFrom]
      | 3, _ =>
        have e : nextSpaces 3 (atomOf 32) = 3 := rfl
        rw [e]; simp [SpacesFrom]
    · have a1 : atomOf c ≠ 1 := fun h => space (atom_one.mp h)
      have e : s ≠ 3 → nextSpaces s (atomOf c) = 1 := by
        intro h; unfold nextSpaces; rw [if_neg h, if_neg a1]
      match s, hs with
      | 0, _ =>
        rw [e (by omega)]
        simp only [SpacesFrom, Twice, last_cons, List.head?_cons, Option.some.injEq, space, false_and, false_or]
        cases w with
        | nil => simp [space]
        | cons d w => simp [space]
      | 1, _ =>
        rw [e (by omega)]
        simp only [SpacesFrom, Twice, last_cons, space, false_and, false_or]
        cases w with
        | nil => simp [space]
        | cons d w => simp
      | 2, _ =>
        rw [e (by omega)]
        simp only [SpacesFrom, Twice, last_cons, List.head?_cons, Option.some.injEq, space, false_and, false_or]
        cases w with
        | nil => simp [space]
        | cons d w => simp [space]
      | 3, _ =>
        have e3 : nextSpaces 3 (atomOf c) = 3 := rfl
        rw [e3]; simp [SpacesFrom]

/-- The characters of a language tag after a subtag of `count` characters so
    far, the first subtag while `first` (`Rowl.Strings.SubtagsRest` on
    characters). -/
def TagRest : List ℕ → ℕ → Bool → Prop
  | [], count, _ => 0 < count
  | c :: rest, count, first =>
    if c = 45 then 0 < count ∧ TagRest rest 0 false
    else count < 8 ∧ ((65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ (first = false ∧ 48 ≤ c ∧ c ≤ 57)) ∧
      TagRest rest (count + 1) first

/-- The states of a language tag. -/
def TagOk (t : ℕ) : Prop := (1 ≤ t ∧ t ≤ 8) ∨ (10 ≤ t ∧ t ≤ 17)

/-- A character that may continue a subtag: a letter, or a digit after the
    first subtag. -/
def TagChar (first : Bool) (c : ℕ) : Prop :=
  (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ (first = false ∧ 48 ≤ c ∧ c ≤ 57)

theorem tagRest_cons (c : ℕ) (rest : List ℕ) (count : ℕ) (first : Bool) :
    TagRest (c :: rest) count first ↔ if c = 45 then 0 < count ∧ TagRest rest 0 false
      else count < 8 ∧ TagChar first c ∧ TagRest rest (count + 1) first := by
  rfl

theorem run_tag (w : List ℕ) (t : ℕ) (ht : t ≤ 18) :
    TagOk (runWith nextTag t w) ↔ t < 18 ∧ TagRest w (if t < 9 then t else t - 9) (decide (t < 9)) := by
  induction w generalizing t with
  | nil =>
    simp only [runWith, TagOk, TagRest]
    split_ifs <;> omega
  | cons c w ih =>
    rw [runWith]
    rcases Nat.lt_or_ge t 18 with lt | ge
    swap
    · have e : t = 18 := by omega
      subst e
      have stay : nextTag 18 (atomOf c) = 18 := by simp [nextTag]
      rw [stay, ih 18 le_rfl]
      simp
    · rw [tagRest_cons]
      by_cases dash : c = 45
      · have e : nextTag t (atomOf c) = if t = 0 ∨ t = 9 then 18 else 9 := by
          rw [atom_five.mpr dash]; unfold nextTag; rw [if_neg (by omega), if_pos rfl]
        rw [e, if_pos dash]
        by_cases z : t = 0 ∨ t = 9
        · rw [if_pos z, ih 18 le_rfl]
          simp only [lt_irrefl, false_and, false_iff, not_and]
          intro _ pos
          rcases z with rfl | rfl <;> simp at pos
        · rw [if_neg z, ih 9 (by omega)]
          simp only [show (9 : ℕ) < 18 from by omega, true_and, show ¬ (9 : ℕ) < 9 from by omega, if_false,
            Nat.sub_self, decide_false]
          constructor
          · intro h; exact ⟨lt, by split_ifs <;> omega, h⟩
          · intro h; exact h.2.2
      · rw [if_neg dash]
        have a5 : atomOf c ≠ 5 := fun h => dash (atom_five.mp h)
        have tagChar : (atomOf c = 3 ∨ (atomOf c = 4 ∧ 9 ≤ t)) ↔ TagChar (decide (t < 9)) c := by
          rw [atom_three, atom_four]
          unfold TagChar
          by_cases small : t < 9
          · simp only [small, decide_true, Bool.true_eq_false, false_and, or_false]
            omega
          · simp only [small, decide_false, true_and]
            omega
        have e : nextTag t (atomOf c) =
            if atomOf c = 3 ∨ (atomOf c = 4 ∧ 9 ≤ t) then (if t = 8 ∨ t = 17 then 18 else t + 1) else 18 := by
          unfold nextTag; rw [if_neg (by omega), if_neg a5]
        rw [e]
        by_cases ok : atomOf c = 3 ∨ (atomOf c = 4 ∧ 9 ≤ t)
        · rw [if_pos ok]
          by_cases full : t = 8 ∨ t = 17
          · rw [if_pos full, ih 18 le_rfl]
            simp only [lt_irrefl, false_and, false_iff, not_and]
            intro _ small
            rcases full with rfl | rfl <;> simp at small
          · rw [if_neg full, ih (t + 1) (by omega)]
            have h1 : (if t + 1 < 9 then t + 1 else t + 1 - 9) = (if t < 9 then t else t - 9) + 1 := by
              split_ifs <;> omega
            have h2 : decide (t + 1 < 9) = decide (t < 9) := by
              rcases Nat.lt_or_ge t 8 with h | h
              · simp [show t + 1 < 9 by omega, show t < 9 by omega]
              · simp [show ¬ t + 1 < 9 by omega, show ¬ t < 9 by omega]
            rw [h1, h2]
            constructor
            · rintro ⟨_, rest⟩
              exact ⟨lt, by split_ifs <;> omega, tagChar.mp ok, rest⟩
            · rintro ⟨_, _, _, rest⟩
              exact ⟨by omega, rest⟩
        · rw [if_neg ok, ih 18 le_rfl]
          simp only [lt_irrefl, false_and, false_iff, not_and]
          intro _ _ ch
          exact absurd (tagChar.mpr ch) ok

/-! ### The rank of a string -/

theorem textRank_join {b s n c t : ℕ} (hs : s < 4) (hn : n < 4) (hc : c < 2) (ht : t < 19) :
    textRank (joinState b s n c t) = if b ≠ 0 then 0 else if 1 < s then 1 else if n = 0 ∨ n = 3 then 2
      else if n = 1 then 3 else if c ≠ 0 then 4 else if t = 0 ∨ t = 9 ∨ t = 18 then 5 else 6 := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := join_parts (b := b) hs hn hc ht
  rw [textRank, e1, e2, e3, e4, e5]

/-- The rank of the string of characters `w`: the rank of the state the
    automaton reads it to. -/
noncomputable def rankOf (w : List ℕ) : ℕ := textRank (runWith textNext 0 w)

theorem rankOf_eq (w : List ℕ) : rankOf w =
    textRank (joinState (runWith nextBreaks 0 w) (runWith nextSpaces 0 w) (runWith nextNames 0 w)
      (runWith nextColons 0 w) (runWith nextTag 0 w)) := by
  rw [rankOf, show (0 : ℕ) = joinState 0 0 0 0 0 from rfl, run_join w (by omega) (by omega) (by omega) (by omega)
    (by omega)]
  rfl


theorem run_spaces_lt (w : List ℕ) (s : ℕ) (hs : s < 4) : runWith nextSpaces s w < 4 := by
  induction w generalizing s with
  | nil => exact hs
  | cons c w ih => exact ih _ (by unfold nextSpaces; split_ifs <;> omega)

theorem run_tag_le (w : List ℕ) (t : ℕ) (ht : t ≤ 18) : runWith nextTag t w ≤ 18 := by
  induction w generalizing t with
  | nil => exact ht
  | cons c w ih => exact ih _ (by unfold nextTag; split_ifs <;> omega)

section Ranks
variable {b s n c t : ℕ} (hs : s < 4) (hn : n < 4) (hc : c < 2) (ht : t < 19)
include hs hn hc ht

theorem rank_one : 1 ≤ textRank (joinState b s n c t) ↔ b = 0 := by
  rw [textRank_join hs hn hc ht]; split_ifs <;> omega

theorem rank_two : 2 ≤ textRank (joinState b s n c t) ↔ b = 0 ∧ s ≤ 1 := by
  rw [textRank_join hs hn hc ht]; split_ifs <;> omega

theorem rank_three : 3 ≤ textRank (joinState b s n c t) ↔ b = 0 ∧ s ≤ 1 ∧ (n = 1 ∨ n = 2) := by
  rw [textRank_join hs hn hc ht]; split_ifs <;> omega

theorem rank_four : 4 ≤ textRank (joinState b s n c t) ↔ b = 0 ∧ s ≤ 1 ∧ n = 2 := by
  rw [textRank_join hs hn hc ht]; split_ifs <;> omega

theorem rank_five : 5 ≤ textRank (joinState b s n c t) ↔ b = 0 ∧ s ≤ 1 ∧ n = 2 ∧ c = 0 := by
  rw [textRank_join hs hn hc ht]; split_ifs <;> omega

theorem rank_six : 6 ≤ textRank (joinState b s n c t) ↔
    b = 0 ∧ s ≤ 1 ∧ n = 2 ∧ c = 0 ∧ t ≠ 0 ∧ t ≠ 9 ∧ t ≠ 18 := by
  rw [textRank_join hs hn hc ht]; split_ifs <;> omega

end Ranks

/-! ### The subtypes of `xsd:string` on characters -/

section Chain
open Rowl.Strings (ChainForm)

theorem ascii_byte {n : ℕ} (h : n < 256) (b : U8) (hb : b.val = n) : b = toByte n := by
  apply UScalar.eq_of_val_eq
  rw [toByte_val h, hb]

variable {w : List ℕ} (xml : ∀ c ∈ w, Rowl.Unicode.XmlChar c)
include xml

theorem xml_bound : ∀ c ∈ w, c ≤ 1114111 := fun c m => xml_high (xml c m)

theorem chain_zero : ChainForm 0 (encodeText w) := by
  obtain ⟨text, from0, _⟩ := encode_chars xml
  exact ⟨text, from0⟩

theorem chain_one : ChainForm 1 (encodeText w) ↔ ¬ ∃ c ∈ w, atomOf c = 0 := by
  show (XmlText (encodeText w) ∧ 9#u8 ∉ encodeText w ∧ 10#u8 ∉ encodeText w ∧ 13#u8 ∉ encodeText w) ↔ _
  rw [ascii_byte (n := 9) (by omega) 9#u8 rfl, ascii_byte (n := 10) (by omega) 10#u8 rfl,
    ascii_byte (n := 13) (by omega) 13#u8 rfl, ascii_mem (xml_bound xml) (by omega), ascii_mem (xml_bound xml) (by omega),
    ascii_mem (xml_bound xml) (by omega)]
  have x0 : XmlText (encodeText w) := chain_zero xml
  simp only [atom_zero, x0, true_and]
  constructor
  · rintro ⟨n9, n10, n13⟩ ⟨c, mem, rfl | rfl | rfl⟩ <;> contradiction
  · intro none
    exact ⟨fun m => none ⟨9, m, by simp⟩, fun m => none ⟨10, m, by simp⟩, fun m => none ⟨13, m, by simp⟩⟩

theorem chain_two : ChainForm 2 (encodeText w) ↔ ChainForm 1 (encodeText w) ∧ SpacesFrom 0 w := by
  show (ChainForm 1 (encodeText w) ∧ (encodeText w).head? ≠ some 32#u8 ∧ (encodeText w).getLast? ≠ some 32#u8 ∧
    ∀ i, (encodeText w)[i]? = some 32#u8 → (encodeText w)[i + 1]? ≠ some 32#u8) ↔ _
  have double : (∀ i, (encodeText w)[i]? = some 32#u8 → (encodeText w)[i + 1]? ≠ some 32#u8) ↔
      ¬ Twice 32 w := by
    rw [← twice_space (xml_bound xml), twice_iff, ← ascii_byte (n := 32) (by omega) 32#u8 rfl]
    simp only [not_exists, not_and, ne_eq]
  rw [double, ascii_byte (n := 32) (by omega) 32#u8 rfl]
  simp only [ne_eq]
  rw [head_space (xml_bound xml), last_space (xml_bound xml)]
  rfl

theorem chain_three : ChainForm 3 (encodeText w) ↔
    ChainForm 2 (encodeText w) ∧ w ≠ [] ∧ ∀ c ∈ w, NameChar c := by
  constructor
  · intro h
    refine ⟨Rowl.Strings.chain_form_step 2 _ h, ?_⟩
    obtain ⟨cps, chars, nonempty, all⟩ := h
    rw [chars_unique chars (encode_chars xml)] at nonempty all
    exact ⟨nonempty, all⟩
  · rintro ⟨_, nonempty, all⟩
    exact ⟨w, encode_chars xml, nonempty, all⟩

theorem chain_four : ChainForm 4 (encodeText w) ↔
    ChainForm 3 (encodeText w) ∧ ∃ c rest, w = c :: rest ∧ NameStartChar c := by
  constructor
  · intro h
    refine ⟨Rowl.Strings.chain_form_step 3 _ h, ?_⟩
    obtain ⟨c, cps, chars, start, _⟩ := h
    exact ⟨c, cps, (chars_unique chars (encode_chars xml)).symm, start⟩
  · rintro ⟨three, c, rest, rfl, start⟩
    obtain ⟨_, _, all⟩ := (chain_three xml).mp three
    exact ⟨c, rest, encode_chars xml, start, fun c' m => all c' (List.mem_cons_of_mem c m)⟩

theorem chain_five : ChainForm 5 (encodeText w) ↔ ChainForm 4 (encodeText w) ∧ 58 ∉ w := by
  show (ChainForm 4 (encodeText w) ∧ 58#u8 ∉ encodeText w) ↔ _
  rw [ascii_byte (n := 58) (by omega) 58#u8 rfl, ascii_mem (xml_bound xml) (by omega)]

theorem subtags_encode (count : ℕ) (first : Bool) :
    Rowl.Strings.SubtagsRest (encodeText w) count first ↔ TagRest w count first := by
  induction w generalizing count first with
  | nil => rfl
  | cons c w ih =>
    have hw : ∀ d ∈ w, Rowl.Unicode.XmlChar d := fun d m => xml d (List.mem_cons_of_mem c m)
    have hc := xml_high (xml c (by simp))
    rw [encodeText_cons, tagRest_cons]
    by_cases small : c < 128
    · rw [utf8_ascii small]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Rowl.Strings.SubtagsRest,
        ih hw]
      have dash : toByte c = 45#u8 ↔ c = 45 := by
        rw [ascii_byte (n := 45) (by omega) 45#u8 rfl, toByte_inj (by omega) (by omega)]
      have v : (toByte c).val = c := toByte_val (by omega)
      simp only [dash, Rowl.Strings.SubtagByte, Letter, v, TagChar, or_assoc]
    · obtain ⟨b, rest, e, hb1, hb2, _, _⟩ := utf8_high (by omega) hc
      rw [e]
      simp only [List.map_cons, List.cons_append, Rowl.Strings.SubtagsRest]
      have v : (toByte b).val = b := toByte_val hb2
      have dash : toByte b ≠ 45#u8 := by
        rw [ascii_byte (n := 45) (by omega) 45#u8 rfl, Ne, toByte_inj hb2 (by omega)]; omega
      rw [if_neg dash, if_neg (by omega)]
      simp only [Rowl.Strings.SubtagByte, Letter, v, TagChar]
      constructor
      · rintro ⟨_, bad, _⟩; omega
      · rintro ⟨_, bad, _⟩; omega

theorem chain_six : ChainForm 6 (encodeText w) ↔ ChainForm 5 (encodeText w) ∧ TagRest w 0 true := by
  have lang : ChainForm 6 (encodeText w) ↔ TagRest w 0 true := by
    show LanguageForm (encodeText w) ↔ _
    rw [Rowl.Strings.language_form_iff, subtags_encode xml]
  constructor
  · intro h
    exact ⟨Rowl.Strings.chain_form_step 5 _ h, lang.mp h⟩
  · exact fun h => lang.mpr h.2


/-- The rank of a string of XML characters is the deepest subtype of
    `xsd:string` it is in: it is in the subtypes of the ranks up to it. -/
theorem chain_rank {k : ℕ} (hk : k ≤ 6) : ChainForm k (encodeText w) ↔ k ≤ rankOf w := by
  rw [rankOf_eq]
  have hs : runWith nextSpaces 0 w < 4 := run_spaces_lt w 0 (by omega)
  have hn : runWith nextNames 0 w < 4 := by rw [run_names]; split_ifs <;> omega
  have hc : runWith nextColons 0 w < 2 := by rw [run_colons]; split_ifs <;> omega
  have ht : runWith nextTag 0 w < 19 := by
    have := run_tag_le w 0 (by omega)
    omega
  have lb : runWith nextBreaks 0 w = 0 ↔ ¬ ∃ c ∈ w, atomOf c = 0 := by
    rw [run_breaks]; split_ifs with h <;> simp [h]
  have ls : runWith nextSpaces 0 w ≤ 1 ↔ SpacesFrom 0 w := run_spaces w 0 (by omega)
  have ln12 : (runWith nextNames 0 w = 1 ∨ runWith nextNames 0 w = 2) ↔
      w ≠ [] ∧ ∀ c ∈ w, 2 ≤ atomOf c ∧ atomOf c ≤ 7 := by
    rw [run_names]; split_ifs with h1 h2 h3 <;> simp_all
  have ln2 : runWith nextNames 0 w = 2 ↔ w ≠ [] ∧ (∀ c ∈ w, 2 ≤ atomOf c ∧ atomOf c ≤ 7) ∧
      (w.head? = some 58 ∨ ∃ c, w.head? = some c ∧ (atomOf c = 3 ∨ atomOf c = 6)) := by
    rw [run_names]; split_ifs with h1 h2 h3 <;> simp_all
  have lc : runWith nextColons 0 w = 0 ↔ 58 ∉ w := by
    rw [run_colons]
    split_ifs with h
    · obtain ⟨c, mem, e⟩ := h
      rw [atom_two] at e
      subst e
      simp [mem]
    · simp only [not_exists, not_and, atom_two] at h
      simp only [true_iff]
      exact fun mem => h 58 mem rfl
  have lt : (runWith nextTag 0 w ≠ 0 ∧ runWith nextTag 0 w ≠ 9 ∧ runWith nextTag 0 w ≠ 18) ↔ TagRest w 0 true := by
    have tag := run_tag w 0 (by omega)
    simp only [show (0 : ℕ) < 9 from by omega, if_true, decide_true, show (0 : ℕ) < 18 from by omega,
      true_and, TagOk] at tag
    rw [← tag]
    omega
  have allNames : (∀ c ∈ w, NameChar c) ↔ ∀ c ∈ w, 2 ≤ atomOf c ∧ atomOf c ≤ 7 :=
    forall₂_congr fun c _ => atom_name
  have startHead : (∃ c rest, w = c :: rest ∧ NameStartChar c) ↔
      w ≠ [] ∧ (w.head? = some 58 ∨ ∃ c, w.head? = some c ∧ (atomOf c = 3 ∨ atomOf c = 6)) := by
    cases w with
    | nil => simp
    | cons c rest =>
      have first : (∃ c' rest', c :: rest = c' :: rest' ∧ NameStartChar c') ↔ NameStartChar c := by
        constructor
        · rintro ⟨c', rest', e, h⟩
          obtain ⟨rfl, rfl⟩ := List.cons.inj e
          exact h
        · intro h
          exact ⟨c, rest, rfl, h⟩
      rw [first, atom_start, atom_two]
      simp
  have c1 := chain_one xml
  have c2 := chain_two xml
  have c3 := chain_three xml
  have c4 := chain_four xml
  have c5 := chain_five xml
  have c6 := chain_six xml
  match k, hk with
  | 0, _ => exact ⟨fun _ => Nat.zero_le _, fun _ => chain_zero xml⟩
  | 1, _ => rw [rank_one hs hn hc ht, c1, lb]
  | 2, _ => rw [rank_two hs hn hc ht, c2, c1, lb, ls]
  | 3, _ =>
    rw [rank_three hs hn hc ht, c3, c2, c1, lb, ls, ln12, allNames]
    exact and_assoc
  | 4, _ =>
    rw [rank_four hs hn hc ht, c4, c3, c2, c1, lb, ls, ln2, allNames, startHead]
    constructor
    · rintro ⟨⟨⟨a, b⟩, c, d⟩, _, f⟩
      exact ⟨a, b, c, d, f⟩
    · rintro ⟨a, b, c, d, f⟩
      exact ⟨⟨⟨a, b⟩, c, d⟩, c, f⟩
  | 5, _ =>
    rw [rank_five hs hn hc ht, c5, c4, c3, c2, c1, lb, ls, ln2, allNames, startHead, lc]
    constructor
    · rintro ⟨⟨⟨⟨a, b⟩, c, d⟩, _, f⟩, g⟩
      exact ⟨a, b, ⟨c, d, f⟩, g⟩
    · rintro ⟨a, b, ⟨c, d, f⟩, g⟩
      exact ⟨⟨⟨⟨a, b⟩, c, d⟩, c, f⟩, g⟩
  | 6, _ =>
    rw [rank_six hs hn hc ht, c6, c5, c4, c3, c2, c1, lb, ls, ln2, allNames, startHead, lc, ← lt]
    constructor
    · rintro ⟨⟨⟨⟨⟨a, b⟩, c, d⟩, _, f⟩, g⟩, h⟩
      exact ⟨a, b, ⟨c, d, f⟩, g, h⟩
    · rintro ⟨a, b, ⟨c, d, f⟩, g, h⟩
      exact ⟨⟨⟨⟨⟨a, b⟩, c, d⟩, c, f⟩, g⟩, h⟩

end Chain


/-! ### Counting -/

theorem rankOf_le (w : List ℕ) : rankOf w ≤ 6 := textRank_le _

/-- The strings of a length whose deepest subtype of `xsd:string` has a rank
    from `first` on and before `last` (`xsd:string` itself for 7). -/
def RankedTexts (first last ℓ : ℕ) : Set (List U8) :=
  {t | TextLength t ℓ ∧ Rowl.Strings.ChainForm first t ∧ (last < 7 → ¬ Rowl.Strings.ChainForm last t)}

/-- The words the automaton of the strings counts are the characters of those
    strings. -/
theorem ranked_image {first last : ℕ} (hf : first ≤ 6) (hl : last ≤ 7) (ℓ : ℕ) :
    encodeText '' {w | w.length = ℓ ∧ (textDfa first last).Accepts 0 w} = RankedTexts first last ℓ := by
  ext t
  simp only [Set.mem_image, Set.mem_setOf_eq, text_accepts, RankedTexts]
  constructor
  · rintro ⟨w, ⟨len, xml, low, high⟩, rfl⟩
    refine ⟨⟨w, encode_chars xml, len⟩, (chain_rank xml hf).mpr low, fun lt => ?_⟩
    rw [chain_rank xml (by omega)]
    exact Nat.not_le.mpr high
  · rintro ⟨⟨w, chars, len⟩, inFirst, notLast⟩
    obtain ⟨xml, rfl⟩ := chars_encode chars
    refine ⟨w, ⟨len, xml, (chain_rank xml hf).mp inFirst, ?_⟩, rfl⟩
    rcases Nat.lt_or_ge last 7 with lt | ge
    · have := notLast lt
      rw [chain_rank xml (by omega)] at this
      exact Nat.lt_of_not_le this
    · have := rankOf_le w
      unfold rankOf at this
      omega

theorem ranked_injOn (first last ℓ : ℕ) :
    Set.InjOn encodeText {w | w.length = ℓ ∧ (textDfa first last).Accepts 0 w} := by
  intro v hv w hw same
  simp only [Set.mem_setOf_eq, text_accepts] at hv hw
  exact encodeText_injective hv.2.1 hw.2.1 same

/-- The strings of a length of the ranks from `first` on and before `last`
    are as many as the words the automaton of the strings counts. -/
theorem text_count {first last : ℕ} (hf : first ≤ 6) (hl : last ≤ 7) (ℓ : ℕ) :
    (RankedTexts first last ℓ).ncard = (textDfa first last).count 0 ℓ := by
  rw [← ranked_image hf hl ℓ, (ranked_injOn first last ℓ).ncard_image,
    Rowl.WordCounts.accepted_ncard _ (text_disjoint first last)]

theorem ranked_finite {first last : ℕ} (hf : first ≤ 6) (hl : last ≤ 7) (ℓ : ℕ) :
    (RankedTexts first last ℓ).Finite := by
  rw [← ranked_image hf hl ℓ]
  exact (Rowl.WordCounts.accepted_finite _ 0 ℓ).image _

/-- The octet sequences of a length. -/
def Octets (ℓ : ℕ) : Set (List U8) := {o | o.length = ℓ}

theorem octets_image (ℓ : ℕ) : (fun w : List ℕ => w.map toByte) '' {w | w.length = ℓ ∧ octetDfa.Accepts 0 w} =
    Octets ℓ := by
  ext o
  simp only [Set.mem_image, Set.mem_setOf_eq, octet_accepts, Octets]
  constructor
  · rintro ⟨w, ⟨len, _⟩, rfl⟩
    simpa using len
  · intro len
    refine ⟨o.map (·.val), ⟨by simpa using len, fun c mem => ?_⟩, ?_⟩
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp mem
      exact b.hBounds
    · rw [List.map_map]
      conv_rhs => rw [← List.map_id o]
      exact List.map_congr_left fun b _ => toByte_of_val b

theorem octets_injOn (ℓ : ℕ) :
    Set.InjOn (fun w : List ℕ => w.map toByte) {w | w.length = ℓ ∧ octetDfa.Accepts 0 w} := by
  intro v hv w hw same
  simp only [Set.mem_setOf_eq, octet_accepts] at hv hw same
  apply List.ext_getElem (by rw [hv.1, hw.1])
  intro i hi hi'
  have := congrArg (fun l => l[i]?) same
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi', Option.map_some,
    Option.some.injEq] at this
  exact (toByte_inj (hv.2 _ (List.getElem_mem hi)) (hw.2 _ (List.getElem_mem hi'))).mp this

/-- The octet sequences of a length are as many as the words the automaton of
    the octets counts: `256 ^ ℓ`. -/
theorem octets_count (ℓ : ℕ) : (Octets ℓ).ncard = octetDfa.count 0 ℓ := by
  rw [← octets_image ℓ, (octets_injOn ℓ).ncard_image, Rowl.WordCounts.accepted_ncard _ octet_disjoint]

theorem octets_finite (ℓ : ℕ) : (Octets ℓ).Finite := by
  rw [← octets_image ℓ]
  exact (Rowl.WordCounts.accepted_finite _ 0 ℓ).image _

/-! ### Lengths from `low` on and before `high` -/

/-- The members of the sets of the lengths from `low` on and before `high`. -/
def Between (S : ℕ → Set (List U8)) (low high : ℕ) : Set (List U8) := {t | ∃ ℓ, low ≤ ℓ ∧ ℓ < high ∧ t ∈ S ℓ}

/-- Finitely many members, one length each: as many as the sum of their
    numbers. -/
theorem between_ncard (S : ℕ → Set (List U8)) (finite : ∀ ℓ, (S ℓ).Finite)
    (apart : ∀ ℓ ℓ' t, t ∈ S ℓ → t ∈ S ℓ' → ℓ = ℓ') (low high : ℕ) :
    (Between S low high).Finite ∧ (Between S low high).ncard = ∑ ℓ ∈ Finset.Ico low high, (S ℓ).ncard := by
  induction high with
  | zero =>
    have : Between S low 0 = ∅ := by
      ext t; simp [Between]
    simp [this]
  | succ high ih =>
    by_cases le : low ≤ high
    · have split : Between S low (high + 1) = Between S low high ∪ S high := by
        ext t
        simp only [Between, Set.mem_setOf_eq, Set.mem_union]
        constructor
        · rintro ⟨ℓ, lo, hi, mem⟩
          rcases Nat.lt_or_ge ℓ high with lt | ge
          · exact .inl ⟨ℓ, lo, lt, mem⟩
          · have : ℓ = high := by omega
            subst this
            exact .inr mem
        · rintro (⟨ℓ, lo, hi, mem⟩ | mem)
          · exact ⟨ℓ, lo, by omega, mem⟩
          · exact ⟨high, le, by omega, mem⟩
      have disjoint : Disjoint (Between S low high) (S high) := by
        rw [Set.disjoint_left]
        rintro t ⟨ℓ, _, hi, mem⟩ mem'
        have := apart _ _ t mem mem'
        omega
      rw [split, Finset.sum_Ico_succ_top le, ← ih.2]
      exact ⟨ih.1.union (finite high), Set.ncard_union_eq disjoint ih.1 (finite high)⟩
    · have : Between S low (high + 1) = ∅ := by
        ext t
        simp only [Between, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
        intro ℓ lo hi
        omega
      rw [this, Finset.Ico_eq_empty (by omega)]
      simp

theorem text_length_unique {t : List U8} {ℓ ℓ' : ℕ} (h : TextLength t ℓ) (h' : TextLength t ℓ') : ℓ = ℓ' := by
  obtain ⟨w, chars, rfl⟩ := h
  obtain ⟨w', chars', rfl⟩ := h'
  rw [chars_unique chars chars']

/-- The strings with lengths from `low` on and before `high` of the ranks from
    `first` on and before `last`: finitely many, as many as the automaton of
    the strings counts. -/
theorem ranked_between {first last : ℕ} (hf : first ≤ 6) (hl : last ≤ 7) (low high : ℕ) :
    (Between (RankedTexts first last) low high).Finite ∧
      (Between (RankedTexts first last) low high).ncard =
        ∑ ℓ ∈ Finset.Ico low high, (textDfa first last).count 0 ℓ := by
  obtain ⟨finite, card⟩ := between_ncard (RankedTexts first last) (ranked_finite hf hl)
    (fun ℓ ℓ' t m m' => text_length_unique m.1 m'.1) low high
  exact ⟨finite, card.trans (Finset.sum_congr rfl fun ℓ _ => text_count hf hl ℓ)⟩

/-- The octet sequences with lengths from `low` on and before `high`. -/
theorem octets_between (low high : ℕ) :
    (Between Octets low high).Finite ∧
      (Between Octets low high).ncard = ∑ ℓ ∈ Finset.Ico low high, octetDfa.count 0 ℓ := by
  obtain ⟨finite, card⟩ := between_ncard Octets octets_finite
    (fun ℓ ℓ' t m m' => by simp only [Octets, Set.mem_setOf_eq] at m m'; omega) low high
  exact ⟨finite, card.trans (Finset.sum_congr rfl fun ℓ _ => octets_count ℓ)⟩

end Rowl.StringCounts
