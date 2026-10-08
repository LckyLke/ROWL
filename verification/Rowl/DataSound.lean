import Rowl.DataComplete
import Rowl.DataReals
import Mathlib.Data.Nat.Nth

/-!
OWL models made from models of `data_ontology`'s encoding. The elements of an
interpretation of the encoding that are no data nodes become the elements of
an OWL interpretation (`sound`), and each element gets values for finitely many
of its data nodes (`Place`): each literal value's individual gets its value,
and each data node that witnesses a data restriction gets a value of its own
region. A numeric data node's region is the interval between neighbouring cuts
that its cut classes place it in, at the level its numeric datatypes say:
integers, decimals that are no integers, rationals that are no decimals, or
irrational numbers (`regionOf`), without the numbers of the literal values.
Every such region but a bounded run of integers is infinite; a bounded run's
integers that are no literal values have room for the node's distinct
neighbours, by the axiom on the run or because the counts of the data
restrictions are at most their number. Strings serve the string nodes, at the
level of the deepest subtype of `xsd:string` whose class holds there
(`Rowl.Strings.stringAt`: strings in exactly the subtypes up to the level);
tagged strings, IRIs of letters a, octet sequences of zeros and values outside
every datatype serve the other data nodes. When the
interpretation of the encoding satisfies a closure's encoding, the OWL
interpretation satisfies the closure (`sound_satisfies`), and every class
expression holds at an element exactly when its encoding does (`sound_class`).
-/
namespace Rowl.DataSound
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DatatypeMap (Normative IsInteger IsDecimal XmlText TagValue integerType decimalType stringType plainType
  booleanType)
open Rowl.Datatypes (Canonical valueOf typeOf kindOf InKind RealIn)
open Rowl.AlcOntology (RoleOf)
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.DataRegions
open Rowl.DataStructure
open Rowl.DataComplete
open Rowl.DataReals (AtLevel)
open Rowl.Regions (cutAt Ordered FineCuts InCut CutBefore)
open Rowl.DataEdges (placesEnd clamp InSlotClass SlotFact SlotNamed slotFree literalBinaries FreeSlot)
open Rowl.FloatOrder (position)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe u v w x uI vI

/-! ### Values -/

/-- The data domain: the datatype map's values and further values outside
    every datatype. -/
abbrev Values (Native : Type w) : Type (max w v) := ULift.{v} (Native ⊕ ℕ)

def embedValue {Native : Type w} (y : Native) : Values.{v,w} Native := ULift.up (.inl y)

theorem embedValue_injective {Native : Type w} : Function.Injective (embedValue.{v,w} (Native := Native)) := by
  intro a b same
  simpa [embedValue] using same

/-- ASCII bytes from the space on are XML text. -/
theorem ascii_text (bs : List U8) (ascii : ∀ b ∈ bs, 32 ≤ b.val ∧ b.val < 128) : XmlText bs := by
  have step : ∀ k, k ≤ bs.length → ∃ text, Rowl.Unicode.TextFrom bs (bs.length - k) text := by
    intro k
    induction k with
    | zero => intro _; exact ⟨[], by simpa using Rowl.Unicode.TextFrom.endOfInput⟩
    | succ k ih =>
      intro hk
      obtain ⟨text, rest⟩ := ih (by omega)
      have inside : bs.length - (k + 1) < bs.length := by omega
      have ha := ascii _ (List.getElem_mem inside)
      refine ⟨(bs[bs.length - (k + 1)].val, bs.length - (k + 1)) :: text,
        .character (width := 1) ?_ ?_ (by decide) (by omega) ?_⟩
      · simp [Rowl.Unicode.Prefix, List.getElem?_eq_getElem inside, ha.2]
      · simp only [Rowl.Unicode.XmlChar]
        right; right; right; left
        omega
      · have : bs.length - (k + 1) + 1 = bs.length - k := by omega
        rw [this]
        exact rest
  obtain ⟨text, h⟩ := step bs.length le_rfl
  exact ⟨text, by simpa using h⟩

/-- The text of `n` letters `a`. -/
def aText (n : ℕ) : List U8 := List.replicate n 97#u8

theorem aText_xml (n : ℕ) : XmlText (aText n) :=
  ascii_text _ (fun b mem => by
    simp only [aText, List.mem_replicate] at mem
    rw [mem.2]
    decide)

theorem aText_injective : Function.Injective aText := by
  intro a b same
  simpa [aText] using congrArg List.length same

/-- The language tag `en`. -/
def enTag : List U8 := [101#u8, 110#u8]

theorem enTag_value : TagValue enTag := by
  refine ⟨enTag, ⟨[101, 110], ?_, Rowl.LangTag.two_letters_well_formed 101 110 (by omega) (by omega)⟩, ?_⟩
  · refine .character (cp := 101) (width := 1) (by simp [Rowl.Unicode.Prefix, enTag]) (by decide) (by simp [enTag]) ?_
    refine .character (cp := 110) (width := 1) (by simp [Rowl.Unicode.Prefix, enTag]) (by decide) (by simp [enTag]) ?_
    exact Rowl.Regular.Utf8From.endOfInput
  · simp [Rowl.DatatypeMap.Lowered, enTag]

/-! ### Regions of numbers -/

/-- The reals of the interval at a position of a list of cuts: in the cut
    before it, if there is one, and outside the cut at it, if there is one. -/
def InInterval (cs : List regions.Cut) (p : Nat) (r : ℝ) : Prop :=
  (0 < p → InCut (cutAt cs (p - 1)) r) ∧ (p < cs.length → ¬ InCut (cutAt cs p) r)

/-- The reals of a level in the interval at a position that are not in `lits`. -/
def regionSet (cs : List regions.Cut) (lits : Set ℝ) (p ℓ : Nat) : Set ℝ :=
  {r | InInterval cs p r ∧ AtLevel ℓ r ∧ r ∉ lits}

/-- The members of a set of reals one after the other: one to one for every
    index while the set has members left. -/
noncomputable def enumerate (S : Set ℝ) (n : ℕ) : ℝ :=
  if h : S.Infinite then (h.natEmbedding S n : ℝ) else ((Set.not_infinite.mp h).toFinset.toList).getD n 0

theorem enumerate_mem (S : Set ℝ) (n : ℕ) (valid : S.Infinite ∨ n < S.ncard) : enumerate S n ∈ S := by
  unfold enumerate
  by_cases h : S.Infinite
  · simp only [dif_pos h]; exact (h.natEmbedding S n).2
  · simp only [dif_neg h]
    have finite := Set.not_infinite.mp h
    have small : n < finite.toFinset.toList.length := by
      rw [Finset.length_toList, ← Set.ncard_eq_toFinset_card S finite]
      exact valid.resolve_left h
    rw [List.getD_eq_getElem _ _ small]
    have member := List.getElem_mem small
    rw [Finset.mem_toList, Set.Finite.mem_toFinset] at member
    exact member

theorem enumerate_injective (S : Set ℝ) {m n : ℕ} (vm : S.Infinite ∨ m < S.ncard) (vn : S.Infinite ∨ n < S.ncard)
    (same : enumerate S m = enumerate S n) : m = n := by
  unfold enumerate at same
  by_cases h : S.Infinite
  · simp only [dif_pos h] at same
    exact (h.natEmbedding S).injective (Subtype.ext same)
  · simp only [dif_neg h] at same
    have finite := Set.not_infinite.mp h
    have card : S.ncard = finite.toFinset.toList.length := by
      rw [Finset.length_toList, ← Set.ncard_eq_toFinset_card S finite]
    have sm : m < finite.toFinset.toList.length := card ▸ vm.resolve_left h
    have sn : n < finite.toFinset.toList.length := card ▸ vn.resolve_left h
    rw [List.getD_eq_getElem _ _ sm, List.getD_eq_getElem _ _ sn] at same
    exact (List.Nodup.getElem_inj_iff (Finset.nodup_toList _)).mp same

/-- The kinds of IRIs and of octet sequences, as regions of values. -/
inductive Sequence where
  | uri | hex | base64

/-- The values of a `Sequence` region: IRIs of letters a, and octet
    sequences of zeros. -/
def codedAt : Sequence → ℕ → DatatypeMap.Coded
  | .uri, n => .uri (aText n)
  | .hex, n => .hex (List.replicate n 0#u8)
  | .base64, n => .base64 (List.replicate n 0#u8)

/-- The kind of a `Sequence` region. -/
def sequenceKind : Sequence → datatypes.Kind
  | .uri => .AnyUri
  | .hex => .HexBinary
  | .base64 => .Base64Binary

theorem sequence_valid (s : Sequence) (n : ℕ) : (codedAt s n).Valid := by
  cases s
  · exact aText_xml n
  · trivial
  · trivial

theorem sequence_injective {s s' : Sequence} {n n' : ℕ} (same : codedAt s n = codedAt s' n') : s = s' ∧ n = n' := by
  cases s <;> cases s' <;> simp only [codedAt, reduceCtorEq, DatatypeMap.Coded.uri.injEq,
    DatatypeMap.Coded.hex.injEq, DatatypeMap.Coded.base64.injEq] at same
  · exact ⟨rfl, aText_injective same⟩
  · exact ⟨rfl, by simpa using congrArg List.length same⟩
  · exact ⟨rfl, by simpa using congrArg List.length same⟩

theorem sequence_kind (s : Sequence) (n : ℕ) : codedKind (codedAt s n) = sequenceKind s := by
  cases s <;> rfl

/-- The values of a region of time instants: midnight on the first of January
    of a year, at offset zero in the region of the time stamps. -/
def momentAt (stamped : Bool) (n : ℕ) : DatatypeMap.Moment :=
  ⟨n, 1, 1, 0, 0, 0, if stamped then some 0 else none⟩

theorem momentAt_valid (stamped : Bool) (n : ℕ) : (momentAt stamped n).Valid := by
  refine ⟨le_rfl, by simp [momentAt], le_rfl, by simp [momentAt, DatatypeMap.daysIn], by simp [momentAt],
    by simp [momentAt], le_rfl, by simp [momentAt], ⟨0, 0, by simp [momentAt]⟩, fun z hz => ?_⟩
  cases stamped <;> simp [momentAt] at hz
  omega

theorem momentAt_injective {s s' : Bool} {n n' : ℕ} (same : momentAt s n = momentAt s' n') : s = s' ∧ n = n' := by
  simp only [momentAt, DatatypeMap.Moment.mk.injEq, Nat.cast_inj, true_and] at same
  refine ⟨?_, same.1⟩
  cases s <;> cases s' <;> simp_all

/-- The values of a format whose places run from `lo` to before `hi`, as the
    kernel clamps them, and that are not in `avoid`. -/
def slotSet (dbl : Bool) (avoid : Set DatatypeMap.Binary) (lo hi : ℕ) : Set DatatypeMap.Binary :=
  Rowl.FloatOrder.Slot (Rowl.Floats.fmt dbl) (Rowl.DataEdges.clamp dbl lo) (Rowl.DataEdges.clamp dbl hi) \ avoid

theorem slotSet_finite (dbl : Bool) (avoid : Set DatatypeMap.Binary) (lo hi : ℕ) :
    (slotSet dbl avoid lo hi).Finite :=
  (Rowl.FloatOrder.slot_finite _ (Rowl.FloatOrder.proper_fmt dbl) _ _).subset Set.sdiff_subset

/-- The values of a region of floating-point numbers: the values of its slot
    one after the other, and NaN past them. -/
noncomputable def binaryAt (dbl : Bool) (avoid : Set DatatypeMap.Binary) (lo hi n : ℕ) : DatatypeMap.Binary :=
  ((slotSet_finite dbl avoid lo hi).toFinset.toList).getD n .nan

theorem slotSet_length (dbl : Bool) (avoid : Set DatatypeMap.Binary) (lo hi : ℕ) :
    (slotSet dbl avoid lo hi).ncard = ((slotSet_finite dbl avoid lo hi).toFinset.toList).length := by
  rw [Finset.length_toList, ← Set.ncard_eq_toFinset_card _ (slotSet_finite dbl avoid lo hi)]

theorem binaryAt_mem {dbl : Bool} {avoid : Set DatatypeMap.Binary} {lo hi n : ℕ}
    (valid : n < (slotSet dbl avoid lo hi).ncard) : binaryAt dbl avoid lo hi n ∈ slotSet dbl avoid lo hi := by
  rw [slotSet_length] at valid
  unfold binaryAt
  rw [List.getD_eq_getElem _ _ valid]
  have member := List.getElem_mem valid
  rw [Finset.mem_toList, Set.Finite.mem_toFinset] at member
  exact member

/-- The values of a region of floating-point numbers are values of its
    format. -/
theorem binaryAt_valid (dbl : Bool) (avoid : Set DatatypeMap.Binary) (lo hi n : ℕ) :
    (binaryAt dbl avoid lo hi n).Valid (Rowl.Floats.fmt dbl) := by
  by_cases valid : n < (slotSet dbl avoid lo hi).ncard
  · exact (binaryAt_mem valid).1.1
  · rw [slotSet_length] at valid
    unfold binaryAt
    rw [List.getD_eq_default _ _ (by omega)]
    exact trivial

theorem binaryAt_injective {dbl : Bool} {avoid : Set DatatypeMap.Binary} {lo hi m n : ℕ}
    (vm : m < (slotSet dbl avoid lo hi).ncard) (vn : n < (slotSet dbl avoid lo hi).ncard)
    (same : binaryAt dbl avoid lo hi m = binaryAt dbl avoid lo hi n) : m = n := by
  rw [slotSet_length] at vm vn
  unfold binaryAt at same
  rw [List.getD_eq_getElem _ _ vm, List.getD_eq_getElem _ _ vn] at same
  exact (List.Nodup.getElem_inj_iff (Finset.nodup_toList _)).mp same

/-- The regions of values that data nodes get: the reals of a level in the
    interval at a position of the cuts, strings of the letter a, tagged
    strings, IRIs and octet sequences, time instants without and with a time
    zone, the values of a format in a slot of places, and values outside every
    datatype. -/
inductive Region where
  | number (position level : Nat) | string (level : Fin 7) | tagged | coded (s : Sequence) | moment (stamped : Bool)
  | binary (double : Bool) (avoid : Set DatatypeMap.Binary) (lo hi : ℕ) | other

/-- Which indices of a region have values of their own. -/
def Valid (cs : List regions.Cut) (lits : Set ℝ) : Region → ℕ → Prop
  | .number p ℓ, n => ℓ ≤ 3 ∧ ((regionSet cs lits p ℓ).Infinite ∨ n < (regionSet cs lits p ℓ).ncard)
  | .binary dbl avoid lo hi, n => n < (slotSet dbl avoid lo hi).ncard
  | _, _ => True

/-- Whether a region has a value for every index. -/
def RegionInfinite (cs : List regions.Cut) (lits : Set ℝ) : Region → Prop
  | .number p ℓ => ℓ ≤ 3 ∧ (regionSet cs lits p ℓ).Infinite
  | .binary _ _ _ _ => False
  | _ => True

theorem valid_of_infinite {cs : List regions.Cut} {lits : Set ℝ} {r : Region} (h : RegionInfinite cs lits r) (n : ℕ) :
    Valid cs lits r n := by
  cases r <;> simp_all [RegionInfinite, Valid]

section Regions
variable {Native : Type w} {D : DatatypeMap Native}

/-- A value of `xsd:double` (`double`) or of `xsd:float`. -/
def formatValue (N : Normative D) : Bool → DatatypeMap.Binary → Native
  | true, b => N.double b
  | false, b => N.float b

/-- The values of a region. -/
noncomputable def regionValue (N : Normative D) (cs : List regions.Cut) (lits : Set ℝ) :
    Region → ℕ → Values.{v,w} Native
  | .number p ℓ, n => embedValue (N.real (enumerate (regionSet cs lits p ℓ) n))
  | .string ℓ, n => embedValue (N.text (Rowl.Strings.stringAt ℓ.val n))
  | .tagged, n => embedValue (N.tagged (aText n) enTag)
  | .coded s, n => embedValue (N.coded (codedAt s n))
  | .moment st, n => embedValue (N.moment (momentAt st n))
  | .binary dbl avoid lo hi, n => embedValue (formatValue N dbl (binaryAt dbl avoid lo hi n))
  | .other, n => ULift.up (.inr n)

/-- A real number is no floating-point number. -/
theorem real_format (N : Normative D) (r : ℝ) (dbl : Bool) {b : DatatypeMap.Binary}
    (vb : b.Valid (Rowl.Floats.fmt dbl)) : N.real r ≠ formatValue N dbl b := by
  cases dbl
  · exact N.real_float r _ vb
  · exact N.real_double r _ vb

theorem text_format (N : Normative D) (t : List U8) (xt : XmlText t) (dbl : Bool) {b : DatatypeMap.Binary}
    (vb : b.Valid (Rowl.Floats.fmt dbl)) : N.text t ≠ formatValue N dbl b := by
  cases dbl
  · exact N.text_float t _ xt vb
  · exact N.text_double t _ xt vb

theorem tagged_format (N : Normative D) (t l : List U8) (xt : XmlText t) (tl : TagValue l) (dbl : Bool)
    {b : DatatypeMap.Binary} (vb : b.Valid (Rowl.Floats.fmt dbl)) : N.tagged t l ≠ formatValue N dbl b := by
  cases dbl
  · exact N.tagged_float t l _ xt tl vb
  · exact N.tagged_double t l _ xt tl vb

theorem coded_format (N : Normative D) (c : DatatypeMap.Coded) (cv : c.Valid) (dbl : Bool)
    {b : DatatypeMap.Binary} (vb : b.Valid (Rowl.Floats.fmt dbl)) : N.coded c ≠ formatValue N dbl b := by
  cases dbl
  · exact N.coded_float c _ cv vb
  · exact N.coded_double c _ cv vb

theorem moment_format (N : Normative D) (m : DatatypeMap.Moment) (mv : m.Valid) (dbl : Bool)
    {b : DatatypeMap.Binary} (vb : b.Valid (Rowl.Floats.fmt dbl)) : N.moment m ≠ formatValue N dbl b := by
  cases dbl
  · exact N.moment_float m _ mv vb
  · exact N.moment_double m _ mv vb

theorem format_injective (N : Normative D) {dbl dbl' : Bool} {b b' : DatatypeMap.Binary}
    (vb : b.Valid (Rowl.Floats.fmt dbl)) (vb' : b'.Valid (Rowl.Floats.fmt dbl'))
    (same : formatValue N dbl b = formatValue N dbl' b') : dbl = dbl' ∧ b = b' := by
  cases dbl <;> cases dbl'
  · exact ⟨rfl, N.float_injective _ _ vb vb' same⟩
  · exact absurd same.symm (N.double_float _ _ vb' vb)
  · exact absurd same (N.double_float _ _ vb vb')
  · exact ⟨rfl, N.double_injective _ _ vb vb' same⟩

theorem format_value_eq (N : Normative D) (dbl : Bool) (b : DatatypeMap.Binary) :
    formatValue N dbl b = Rowl.Datatypes.binaryValue N dbl b := by
  cases dbl <;> rfl

theorem level_unique {ℓ ℓ' : Nat} (h : ℓ ≤ 3) (h' : ℓ' ≤ 3) {r : ℝ} (a : AtLevel ℓ r) (a' : AtLevel ℓ' r) :
    ℓ = ℓ' := by
  have id := @Rowl.DataReals.integer_decimal
  have dr := @Rowl.DataReals.decimal_rational
  interval_cases ℓ <;> interval_cases ℓ' <;> simp only [AtLevel] at a a' <;> first | rfl | tauto

theorem interval_unique {cs : List regions.Cut} (sorted : cs.Pairwise CutBefore) {p p' : Nat}
    (hp : p ≤ cs.length) (hp' : p' ≤ cs.length) {r : ℝ} (a : InInterval cs p r) (a' : InInterval cs p' r) :
    p = p' := by
  by_contra differ
  have key : ∀ {p p' : Nat}, p < p' → p' ≤ cs.length → InInterval cs p r → InInterval cs p' r → False := by
    intro p p' lt hp' a a'
    have outside := a.2 (by omega)
    have inside := a'.1 (by omega)
    by_cases same : p = p' - 1
    · subst same; exact outside inside
    · have before : CutBefore (cutAt cs p) (cutAt cs (p' - 1)) := by
        rw [Rowl.Regions.cutAt_eq _ _ (by omega), Rowl.Regions.cutAt_eq _ _ (by omega)]
        exact List.pairwise_iff_getElem.mp sorted _ _ (by omega) (by omega) (by omega)
      exact outside (Rowl.Regions.in_cut_mono before r inside)
  rcases Nat.lt_or_gt_of_ne differ with lt | gt
  · exact key lt hp' a a'
  · exact key gt hp a' a

/-- Values of regions are apart, and one to one within a region. -/
theorem region_value_injective (N : Normative D) {cs : List regions.Cut} {lits : Set ℝ}
    (sorted : cs.Pairwise CutBefore) {r r' : Region} {n n' : ℕ} (vr : Valid cs lits r n) (vr' : Valid cs lits r' n')
    (bounded : ∀ p ℓ, r = .number p ℓ → p ≤ cs.length) (bounded' : ∀ p ℓ, r' = .number p ℓ → p ≤ cs.length)
    (coherent : ∀ dbl A lo hi A' lo' hi', r = .binary dbl A lo hi → r' = .binary dbl A' lo' hi' →
      ∀ b, b ∈ slotSet dbl A lo hi → b ∈ slotSet dbl A' lo' hi' → A = A' ∧ lo = lo' ∧ hi = hi')
    (same : regionValue.{v,w} N cs lits r n = regionValue N cs lits r' n') : r = r' ∧ n = n' := by
  have tag := enTag_value
  cases r with
  | number p ℓ =>
    cases r' with
    | number p' ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      have values := N.real_injective same
      have m := enumerate_mem _ _ vr.2
      have m' := enumerate_mem _ _ vr'.2
      rw [values] at m
      have levels := level_unique vr.1 vr'.1 m.2.1 m'.2.1
      have positions := interval_unique sorted (bounded p ℓ rfl) (bounded' p' ℓ' rfl) m.1 m'.1
      subst levels positions
      exact ⟨rfl, enumerate_injective _ vr.2 vr'.2 values⟩
    | string ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.real_text _ _ (Rowl.Strings.stringAt_xml ℓ'.isLt n'))
    | tagged =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.real_tagged _ _ _ (aText_xml n') tag)
    | coded s' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.real_coded _ _ (sequence_valid s' n'))
    | moment st' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.real_moment _ _ (momentAt_valid st' n'))
    | binary dbl' A' lo' hi' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (real_format N _ dbl' (binaryAt_valid dbl' A' lo' hi' n'))
    | other => simp [regionValue, embedValue] at same
  | string ℓ =>
    cases r' with
    | number p' ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.real_text _ _ (Rowl.Strings.stringAt_xml ℓ.isLt n))
    | string ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      obtain ⟨levels, counts⟩ := Rowl.Strings.stringAt_injective ℓ.isLt ℓ'.isLt
        (N.text_injective _ _ (Rowl.Strings.stringAt_xml ℓ.isLt n) (Rowl.Strings.stringAt_xml ℓ'.isLt n') same)
      exact ⟨by rw [Fin.ext levels], counts⟩
    | tagged =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.text_tagged _ _ _ (Rowl.Strings.stringAt_xml ℓ.isLt n) (aText_xml n') tag)
    | coded s' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.text_coded _ _ (Rowl.Strings.stringAt_xml ℓ.isLt n) (sequence_valid s' n'))
    | moment st' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.text_moment _ _ (Rowl.Strings.stringAt_xml ℓ.isLt n) (momentAt_valid st' n'))
    | binary dbl' A' lo' hi' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (text_format N _ (Rowl.Strings.stringAt_xml ℓ.isLt n) dbl' (binaryAt_valid dbl' A' lo' hi' n'))
    | other => simp [regionValue, embedValue] at same
  | tagged =>
    cases r' with
    | number p' ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.real_tagged _ _ _ (aText_xml n) tag)
    | string ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.text_tagged _ _ _ (Rowl.Strings.stringAt_xml ℓ'.isLt n') (aText_xml n) tag)
    | tagged =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact ⟨rfl, aText_injective (N.tagged_injective _ _ _ _ (aText_xml n) (aText_xml n') tag tag same).1⟩
    | coded s' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.tagged_coded _ _ _ (aText_xml n) tag (sequence_valid s' n'))
    | moment st' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.tagged_moment _ _ _ (aText_xml n) tag (momentAt_valid st' n'))
    | binary dbl' A' lo' hi' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (tagged_format N _ _ (aText_xml n) tag dbl' (binaryAt_valid dbl' A' lo' hi' n'))
    | other => simp [regionValue, embedValue] at same
  | coded s =>
    cases r' with
    | number p' ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.real_coded _ _ (sequence_valid s n))
    | string ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.text_coded _ _ (Rowl.Strings.stringAt_xml ℓ'.isLt n') (sequence_valid s n))
    | tagged =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.tagged_coded _ _ _ (aText_xml n') tag (sequence_valid s n))
    | coded s' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      obtain ⟨rfl, rfl⟩ := sequence_injective (N.coded_injective _ _ (sequence_valid s n) (sequence_valid s' n') same)
      exact ⟨rfl, rfl⟩
    | moment st' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.coded_moment _ _ (sequence_valid s n) (momentAt_valid st' n'))
    | binary dbl' A' lo' hi' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (coded_format N _ (sequence_valid s n) dbl' (binaryAt_valid dbl' A' lo' hi' n'))
    | other => simp [regionValue, embedValue] at same
  | moment st =>
    cases r' with
    | number p' ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.real_moment _ _ (momentAt_valid st n))
    | string ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.text_moment _ _ (Rowl.Strings.stringAt_xml ℓ'.isLt n') (momentAt_valid st n))
    | tagged =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.tagged_moment _ _ _ (aText_xml n') tag (momentAt_valid st n))
    | coded s' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.coded_moment _ _ (sequence_valid s' n') (momentAt_valid st n))
    | moment st' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      obtain ⟨rfl, rfl⟩ :=
        momentAt_injective (N.moment_injective _ _ (momentAt_valid st n) (momentAt_valid st' n') same)
      exact ⟨rfl, rfl⟩
    | binary dbl' A' lo' hi' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (moment_format N _ (momentAt_valid st n) dbl' (binaryAt_valid dbl' A' lo' hi' n'))
    | other => simp [regionValue, embedValue] at same
  | binary dbl A lo hi =>
    have vb := binaryAt_valid dbl A lo hi n
    cases r' with
    | number p' ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (real_format N _ dbl vb)
    | string ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (text_format N _ (Rowl.Strings.stringAt_xml ℓ'.isLt n') dbl vb)
    | tagged =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (tagged_format N _ _ (aText_xml n') tag dbl vb)
    | coded s' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (coded_format N _ (sequence_valid s' n') dbl vb)
    | moment st' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (moment_format N _ (momentAt_valid st' n') dbl vb)
    | binary dbl' A' lo' hi' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      obtain ⟨rfl, values⟩ := format_injective N vb (binaryAt_valid dbl' A' lo' hi' n') same
      have member := binaryAt_mem (dbl := dbl) vr
      rw [values] at member
      obtain ⟨rfl, rfl, rfl⟩ := coherent dbl A lo hi A' lo' hi' rfl rfl _ member (binaryAt_mem vr')
      exact ⟨rfl, binaryAt_injective vr vr' values⟩
    | other => simp [regionValue, embedValue] at same
  | other =>
    cases r' with
    | number p' ℓ' => simp [regionValue, embedValue] at same
    | string ℓ' => simp [regionValue, embedValue] at same
    | tagged => simp [regionValue, embedValue] at same
    | coded s' => simp [regionValue, embedValue] at same
    | moment st' => simp [regionValue, embedValue] at same
    | binary dbl' A' lo' hi' => simp [regionValue, embedValue] at same
    | other =>
      simp only [regionValue, ULift.up.injEq, Sum.inr.injEq] at same
      exact ⟨rfl, same⟩

/-- The values of a region with a value for every index are one to one. -/
theorem region_value_inj (N : Normative D) {cs : List regions.Cut} {lits : Set ℝ} {r : Region}
    (infinite : RegionInfinite cs lits r) : Function.Injective (regionValue.{v,w} N cs lits r) := by
  intro a b same
  cases r with
  | number p ℓ =>
    simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
    exact enumerate_injective _ (.inl infinite.2) (.inl infinite.2) (N.real_injective same)
  | string ℓ =>
    simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
    exact (Rowl.Strings.stringAt_injective ℓ.isLt ℓ.isLt
      (N.text_injective _ _ (Rowl.Strings.stringAt_xml ℓ.isLt a) (Rowl.Strings.stringAt_xml ℓ.isLt b) same)).2
  | tagged =>
    simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
    exact aText_injective (N.tagged_injective _ _ _ _ (aText_xml a) (aText_xml b) enTag_value enTag_value same).1
  | coded s =>
    simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
    exact (sequence_injective (N.coded_injective _ _ (sequence_valid s a) (sequence_valid s b) same)).2
  | moment st =>
    simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
    exact (momentAt_injective (N.moment_injective _ _ (momentAt_valid st a) (momentAt_valid st b) same)).2
  | binary dbl A lo hi => exact absurd infinite id
  | other =>
    simpa [regionValue] using same

/-- Beyond some point, the values of a region with a value for every index
    avoid a finite set. -/
theorem region_avoids (N : Normative D) {cs : List regions.Cut} {lits : Set ℝ}
    (F : Set (Values.{v,w} Native)) (finite : F.Finite) (r : Region) (infinite : RegionInfinite cs lits r) :
    ∃ M, ∀ n, M ≤ n → regionValue N cs lits r n ∉ F := by
  have injective := region_value_inj N infinite
  obtain ⟨B, bound⟩ := (finite.preimage (injective.injOn)).bddAbove
  exact ⟨B + 1, fun n hn inside => by have := bound inside; omega⟩

end Regions

/-! ### Which datatypes the values of a region are in -/

section Spaces
variable {Native : Type w} {D : DatatypeMap Native}

/-- The kind of `xsd:double` (`double`) or of `xsd:float`. -/
def formatKind : Bool → datatypes.Kind
  | true => .Double
  | false => .Float

/-- The kinds whose datatypes a region's value at an index is in. -/
def RegionIn (cs : List regions.Cut) (lits : Set ℝ) : Region → ℕ → datatypes.Kind → Prop
  | .number p ℓ, n, k => Rowl.Datatypes.IsNumeric k ∧ RealIn k (enumerate (regionSet cs lits p ℓ) n)
  | .string ℓ, n, k => Rowl.Strings.TextIn k (Rowl.Strings.stringAt ℓ.val n)
  | .tagged, _, k => k = .Plain
  | .coded s, _, k => k = sequenceKind s
  | .moment st, _, k => k = .DateTime ∨ (k = .DateTimeStamp ∧ st = true)
  | .binary dbl _ _ _, _, k => k = formatKind dbl
  | .other, _, _ => False

theorem embedded_space {k : datatypes.Kind} (y0 : Native) :
    (∃ y, D.valueSpace (typeOf k) y ∧ embedValue.{v,w} y = embedValue y0) ↔ D.valueSpace (typeOf k) y0 :=
  ⟨fun ⟨_, inSpace, same⟩ => embedValue_injective same ▸ inSpace, fun inSpace => ⟨y0, inSpace, rfl⟩⟩

theorem real_space (N : Normative D) (r : ℝ) (k : datatypes.Kind) :
    D.valueSpace (typeOf k) (N.real r) ↔ Rowl.Datatypes.IsNumeric k ∧ RealIn k r := by
  by_cases numeric : Rowl.Datatypes.IsNumeric k
  · rw [Rowl.Datatypes.numeric_space N k numeric]
    constructor
    · rintro ⟨r', same, inK⟩; rw [N.real_injective same]; exact ⟨numeric, inK⟩
    · rintro ⟨_, inK⟩; exact ⟨r, rfl, inK⟩
  · simp only [numeric, false_and, iff_false]
    by_cases ck : IsCoded k
    · intro inside
      obtain ⟨c, valid, _, same⟩ := coded_of_kind N ck inside
      exact N.real_coded r c valid same
    by_cases sub : ∃ s, Rowl.Strings.subtypeOf k = some s
    · obtain ⟨s, hs⟩ := sub
      rw [Rowl.Datatypes.subtype_space_iff N hs]
      rintro ⟨t, f, same⟩
      exact N.real_text r t (Rowl.Strings.form_xml f) same
    by_cases mk : IsMomentKind k
    · intro inside
      obtain ⟨m, mv, same⟩ := moment_of_kind N mk inside
      exact N.real_moment r m mv same
    by_cases fk : k = .Double ∨ k = .Float
    · rcases fk with rfl | rfl
      · rw [typeOf, N.double_space]; rintro ⟨b, bv, same⟩; exact N.real_double r b bv same
      · rw [typeOf, N.float_space]; rintro ⟨b, bv, same⟩; exact N.real_float r b bv same
    cases k <;> simp only [Rowl.Datatypes.IsNumeric, IsCoded, IsMomentKind, not_true_eq_false] at numeric ck mk <;>
      (try simp only [Rowl.Strings.subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
      (try simp only [true_or, or_true, not_true_eq_false] at fk)
    · rw [typeOf, N.string_space]
      rintro ⟨s, xs, same⟩
      exact N.real_text r s xs same
    · rw [typeOf, N.plain_space]
      rintro (⟨s, xs, same⟩ | ⟨s, l, xs, tl, same⟩)
      · exact N.real_text r s xs same
      · exact N.real_tagged r s l xs tl same
    · rw [typeOf, N.boolean_space]
      rintro ⟨b, same⟩
      exact N.real_truth r b same

theorem text_space (N : Normative D) (t : List U8) (xs : XmlText t) (k : datatypes.Kind) :
    D.valueSpace (typeOf k) (N.text t) ↔ Rowl.Strings.TextIn k t := by
  by_cases sub : ∃ s, Rowl.Strings.subtypeOf k = some s
  · obtain ⟨s, hs⟩ := sub
    rw [Rowl.Datatypes.subtype_space_iff N hs]
    have others : k ≠ .String ∧ k ≠ .Plain := by cases k <;> simp [Rowl.Strings.subtypeOf] at hs ⊢
    simp only [Rowl.Strings.TextIn, others.1, others.2, false_or, hs, Option.some.injEq, exists_eq_left']
    constructor
    · rintro ⟨t', f, same⟩; rw [N.text_injective _ _ xs (Rowl.Strings.form_xml f) same]; exact f
    · intro f; exact ⟨t, f, rfl⟩
  have classic : Rowl.Strings.TextIn k t ↔ k = .String ∨ k = .Plain := by
    simp only [Rowl.Strings.TextIn]
    constructor
    · rintro (h | h | ⟨s, hs, _⟩)
      exacts [.inl h, .inr h, absurd ⟨s, hs⟩ sub]
    · rintro (h | h)
      exacts [.inl h, .inr (.inl h)]
  rw [classic]
  by_cases numeric : Rowl.Datatypes.IsNumeric k
  · rw [Rowl.Datatypes.numeric_space N k numeric]
    constructor
    · rintro ⟨r, same, _⟩; exact absurd same.symm (N.real_text r t xs)
    · rintro (rfl | rfl) <;> simp [Rowl.Datatypes.IsNumeric] at numeric
  · by_cases ck : IsCoded k
    · constructor
      · intro inside
        obtain ⟨c, valid, _, same⟩ := coded_of_kind N ck inside
        exact absurd same (N.text_coded t c xs valid)
      · rintro (rfl | rfl) <;> simp [IsCoded] at ck
    by_cases mk : IsMomentKind k
    · constructor
      · intro inside
        obtain ⟨m, mv, same⟩ := moment_of_kind N mk inside
        exact absurd same (N.text_moment t m xs mv)
      · rintro (rfl | rfl) <;> simp [IsMomentKind] at mk
    by_cases fk : k = .Double ∨ k = .Float
    · rcases fk with rfl | rfl
      · constructor
        · rw [typeOf, N.double_space]; rintro ⟨b, bv, same⟩; exact absurd same (N.text_double t b xs bv)
        · rintro (h | h) <;> cases h
      · constructor
        · rw [typeOf, N.float_space]; rintro ⟨b, bv, same⟩; exact absurd same (N.text_float t b xs bv)
        · rintro (h | h) <;> cases h
    cases k <;> simp only [Rowl.Datatypes.IsNumeric, IsCoded, IsMomentKind, not_true_eq_false] at numeric ck mk <;>
      (try simp only [Rowl.Strings.subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
      (try simp only [true_or, or_true, not_true_eq_false] at fk)
    · simp only [typeOf, N.string_space, true_or, iff_true]
      exact ⟨t, xs, rfl⟩
    · simp only [typeOf, N.plain_space, or_true, iff_true]
      exact .inl ⟨t, xs, rfl⟩
    · simp only [typeOf, N.boolean_space, reduceCtorEq, or_self, iff_false, not_exists]
      exact fun b e => N.text_truth t b xs e

theorem tagged_space (N : Normative D) (t l : List U8) (xs : XmlText t) (tl : TagValue l) (k : datatypes.Kind) :
    D.valueSpace (typeOf k) (N.tagged t l) ↔ k = .Plain := by
  by_cases sub : ∃ s, Rowl.Strings.subtypeOf k = some s
  · obtain ⟨s, hs⟩ := sub
    rw [Rowl.Datatypes.subtype_space_iff N hs]
    have notPlain : k ≠ .Plain := by cases k <;> simp [Rowl.Strings.subtypeOf] at hs ⊢
    simp only [notPlain, iff_false, not_exists, not_and]
    exact fun t' f same => N.text_tagged t' t l (Rowl.Strings.form_xml f) xs tl same.symm
  by_cases numeric : Rowl.Datatypes.IsNumeric k
  · rw [Rowl.Datatypes.numeric_space N k numeric]
    constructor
    · rintro ⟨r, same, _⟩; exact absurd same.symm (N.real_tagged r t l xs tl)
    · rintro rfl; simp [Rowl.Datatypes.IsNumeric] at numeric
  · by_cases ck : IsCoded k
    · constructor
      · intro inside
        obtain ⟨c, valid, _, same⟩ := coded_of_kind N ck inside
        exact absurd same (N.tagged_coded t l c xs tl valid)
      · rintro rfl; simp [IsCoded] at ck
    by_cases mk : IsMomentKind k
    · constructor
      · intro inside
        obtain ⟨m, mv, same⟩ := moment_of_kind N mk inside
        exact absurd same (N.tagged_moment t l m xs tl mv)
      · rintro rfl; simp [IsMomentKind] at mk
    by_cases fk : k = .Double ∨ k = .Float
    · rcases fk with rfl | rfl
      · constructor
        · rw [typeOf, N.double_space]; rintro ⟨b, bv, same⟩; exact absurd same (N.tagged_double t l b xs tl bv)
        · intro h; cases h
      · constructor
        · rw [typeOf, N.float_space]; rintro ⟨b, bv, same⟩; exact absurd same (N.tagged_float t l b xs tl bv)
        · intro h; cases h
    cases k <;> simp only [Rowl.Datatypes.IsNumeric, IsCoded, IsMomentKind, not_true_eq_false] at numeric ck mk <;>
      (try simp only [Rowl.Strings.subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
      (try simp only [true_or, or_true, not_true_eq_false] at fk)
    · simp only [typeOf, N.string_space, reduceCtorEq, iff_false, not_exists, not_and]
      exact fun s xs' e => N.text_tagged s t l xs' xs tl e.symm
    · simp only [typeOf, N.plain_space, iff_true]
      exact .inr ⟨t, l, xs, tl, rfl⟩
    · simp only [typeOf, N.boolean_space, reduceCtorEq, iff_false, not_exists]
      exact fun b e => N.tagged_truth t l b xs tl e

/-- An IRI or octet sequence is in the datatype of its own kind only. -/
theorem coded_space (N : Normative D) (s : Sequence) (n : ℕ) (k : datatypes.Kind) :
    D.valueSpace (typeOf k) (N.coded (codedAt s n)) ↔ k = sequenceKind s := by
  by_cases ck : IsCoded k
  · constructor
    · intro inside
      obtain ⟨c, valid, kindIs, same⟩ := coded_of_kind N ck inside
      have := N.coded_injective _ _ (sequence_valid s n) valid same
      subst this
      rw [← kindIs, sequence_kind]
    · rintro rfl
      cases s
      · exact (N.uri_space _).mpr ⟨_, aText_xml n, rfl⟩
      · exact (N.hex_space _).mpr ⟨_, rfl⟩
      · exact (N.base64_space _).mpr ⟨_, rfl⟩
  · constructor
    · intro inside
      exact absurd rfl (not_coded N ck inside _ (sequence_valid s n))
    · rintro rfl
      exact absurd (by cases s <;> trivial) ck

/-- A time instant of a region is in `xsd:dateTime`, and in
    `xsd:dateTimeStamp` when it has a time zone. -/
theorem moment_space (N : Normative D) (st : Bool) (n : ℕ) (k : datatypes.Kind) :
    D.valueSpace (typeOf k) (N.moment (momentAt st n)) ↔ k = .DateTime ∨ (k = .DateTimeStamp ∧ st = true) := by
  have valid := momentAt_valid st n
  by_cases mk : IsMomentKind k
  · cases k <;> simp only [IsMomentKind] at mk
    case DateTime =>
      simp only [true_or, iff_true]
      exact (N.datetime_space _).mpr ⟨_, valid, rfl⟩
    case DateTimeStamp =>
      simp only [reduceCtorEq, true_and, false_or]
      constructor
      · intro inside
        obtain ⟨m, mv, zone, same⟩ := (N.stamp_space _).mp inside
        have := N.moment_injective _ _ valid mv same
        subst this
        cases st
        · simp [momentAt] at zone
        · rfl
      · rintro rfl
        exact (N.stamp_space _).mpr ⟨_, valid, by simp [momentAt], rfl⟩
  · constructor
    · intro inside
      exact absurd rfl (not_moment N mk inside _ valid)
    · rintro (rfl | ⟨rfl, _⟩) <;> exact absurd trivial mk

/-- A floating-point number is in the datatype of its format only. -/
theorem binary_space (N : Normative D) (dbl : Bool) {b : DatatypeMap.Binary} (vb : b.Valid (Rowl.Floats.fmt dbl))
    (k : datatypes.Kind) : D.valueSpace (typeOf k) (formatValue N dbl b) ↔ k = formatKind dbl := by
  cases dbl
  · constructor
    · intro inside
      by_contra ne
      exact Rowl.DataComplete.not_float N ne inside _ vb rfl
    · rintro rfl; exact (N.float_space _).mpr ⟨_, vb, rfl⟩
  · constructor
    · intro inside
      by_contra ne
      exact Rowl.DataComplete.not_double N ne inside _ vb rfl
    · rintro rfl; exact (N.double_space _).mpr ⟨_, vb, rfl⟩

/-- A region's values are in the datatypes of the kinds `RegionIn` names. -/
theorem region_space (N : Normative D) (cs : List regions.Cut) (lits : Set ℝ) (r : Region) (n : ℕ)
    (k : datatypes.Kind) :
    (∃ y, D.valueSpace (typeOf k) y ∧ embedValue.{v,w} y = regionValue N cs lits r n) ↔ RegionIn cs lits r n k := by
  cases r with
  | number p ℓ => rw [regionValue, embedded_space, real_space N]; rfl
  | string ℓ => rw [regionValue, embedded_space, text_space N _ (Rowl.Strings.stringAt_xml ℓ.isLt n)]; rfl
  | tagged => rw [regionValue, embedded_space, tagged_space N _ _ (aText_xml n) enTag_value]; rfl
  | coded s => rw [regionValue, embedded_space, coded_space N s n]; rfl
  | moment st => rw [regionValue, embedded_space, moment_space N st n]; rfl
  | binary dbl A lo hi => rw [regionValue, embedded_space, binary_space N dbl (binaryAt_valid dbl A lo hi n)]; rfl
  | other =>
    simp only [regionValue, embedValue, ULift.up.injEq, reduceCtorEq, and_false, exists_false, false_iff]
    exact id

end Spaces

/-! ### The region of a data node -/

section Profile
variable {Object' : Type u} {Value' : Type x} (context : data_ontology.Context) (J : Interpretation Object' Value')
  (order : List Usize)

/-- A kind in use whose class holds at a node. -/
def InUse (k : datatypes.Kind) (d : Object') : Prop := Used context.kinds k = true ∧ J.classes (kindClass k) d

/-- A node in the class of a numeric datatype in use. -/
def NumericNode (d : Object') : Prop :=
  InUse context J .Integer d ∨ InUse context J .Decimal d ∨ InUse context J .Rational d ∨ InUse context J .Real d

/-- The level of a numeric node: the least of the integers, the decimals and
    the rationals whose class in use holds at it, and the irrational numbers
    otherwise. -/
noncomputable def levelOf (d : Object') : Nat :=
  if InUse context J .Integer d then 0
  else if InUse context J .Decimal d then 1
  else if InUse context J .Rational d then 2
  else 3

/-- The cuts in order, when numbers are ordered. -/
def orderedCuts : List regions.Cut :=
  if context.kinds.ordered then order.map (fun k => cutAt context.cuts.val k.val) else []

/-- The position of a node among the cuts in order: the number of cuts whose
    classes hold at it. -/
noncomputable def positionOf (d : Object') : Nat :=
  if h : ∃ k, k < (orderedCuts context order).length ∧ ¬ J.classes (cutClass (order.getD k 0#usize)) d then
    Nat.find h
  else (orderedCuts context order).length

/-- The level of a string node: the rank of the deepest subtype of
    `xsd:string` in use whose class holds at it, and 0 for none. -/
noncomputable def stringLevel (d : Object') : Fin 7 :=
  if InUse context J (chainKind 6) d then 6
  else if InUse context J (chainKind 5) d then 5
  else if InUse context J (chainKind 4) d then 4
  else if InUse context J (chainKind 3) d then 3
  else if InUse context J (chainKind 2) d then 2
  else if InUse context J (chainKind 1) d then 1
  else 0

/-- The places of the edges of a format whose classes hold at a node. -/
def HeldEdges (dbl : Bool) (d : Object') : Set ℕ :=
  {e | ∃ (i : Usize) (h : i.val < (edgesOf context dbl).val.length),
    ((edgesOf context dbl).val[i.val]'h).val = e ∧ J.classes (edgeClass dbl i) d}

/-- The places of the edges of a format whose classes do not hold at a node. -/
def FailedEdges (dbl : Bool) (d : Object') : Set ℕ :=
  {e | ∃ (i : Usize) (h : i.val < (edgesOf context dbl).val.length),
    ((edgesOf context dbl).val[i.val]'h).val = e ∧ ¬ J.classes (edgeClass dbl i) d}

/-- Where the slot of a node of a format begins: at the highest edge whose
    class holds there, or at the first place. -/
noncomputable def slotLow (dbl : Bool) (d : Object') : ℕ := sSup (insert 0 (HeldEdges context J dbl d))

/-- Where the slot of a node of a format ends: at the lowest edge whose class
    does not hold there, or at the end. -/
noncomputable def slotHigh (dbl : Bool) (d : Object') : ℕ :=
  sInf (insert (placesEnd dbl) (FailedEdges context J dbl d))

/-- The region of a node's values. -/
noncomputable def regionOf (d : Object') : Region :=
  if NumericNode context J d then .number (positionOf context J order d) (levelOf context J d)
  else if InUse context J .String d then .string (stringLevel context J d)
  else if InUse context J .Plain d then .tagged
  else if InUse context J .AnyUri d then .coded .uri
  else if InUse context J .HexBinary d then .coded .hex
  else if InUse context J .Base64Binary d then .coded .base64
  else if InUse context J .DateTime d then .moment (decide (InUse context J .DateTimeStamp d))
  else if InUse context J .Double d then
    .binary true (literalBinaries context.values.val true) (slotLow context J true d) (slotHigh context J true d)
  else if InUse context J .Float d then
    .binary false (literalBinaries context.values.val false) (slotLow context J false d)
      (slotHigh context J false d)
  else .other

theorem level_le (d : Object') : levelOf context J d ≤ 3 := by
  unfold levelOf; split_ifs <;> omega

theorem position_le (d : Object') : positionOf context J order d ≤ (orderedCuts context order).length := by
  unfold positionOf
  split_ifs with h
  · exact le_of_lt (Nat.find_spec h).1
  · exact le_rfl

/-! ### The slot of a node of a floating-point format -/

theorem edge_values_finite (dbl : Bool) :
    {e : ℕ | ∃ u ∈ (edgesOf context dbl).val, u.val = e}.Finite :=
  ((edgesOf context dbl).val.finite_toSet.image (fun u : U128 => u.val)).subset fun _ ⟨u, m, h⟩ => ⟨u, m, h⟩

theorem held_finite (dbl : Bool) (d : Object') : (HeldEdges context J dbl d).Finite := by
  apply (edge_values_finite context dbl).subset
  rintro e ⟨i, h, rfl, _⟩
  exact ⟨_, List.getElem_mem h, rfl⟩

theorem held_bdd (dbl : Bool) (d : Object') : BddAbove (insert 0 (HeldEdges context J dbl d)) :=
  ((held_finite context J dbl d).insert 0).bddAbove

variable {context J}

/-- Every edge whose class holds at a node is at or below the beginning of its
    slot. -/
theorem held_le {dbl : Bool} {d : Object'} {e : ℕ} (held : e ∈ HeldEdges context J dbl d) :
    e ≤ slotLow context J dbl d :=
  le_csSup (held_bdd context J dbl d) (Set.mem_insert_of_mem _ held)

/-- Every edge whose class does not hold at a node is at or above the end of
    its slot. -/
theorem failed_ge {dbl : Bool} {d : Object'} {e : ℕ} (failed : e ∈ FailedEdges context J dbl d) :
    slotHigh context J dbl d ≤ e :=
  Nat.sInf_le (Set.mem_insert_of_mem _ failed)

theorem slot_high_le (dbl : Bool) (d : Object') : slotHigh context J dbl d ≤ placesEnd dbl :=
  Nat.sInf_le (Set.mem_insert _ _)

/-- Without an edge whose class holds, a slot begins at the first place. -/
theorem slot_low_empty {dbl : Bool} {d : Object'} (empty : HeldEdges context J dbl d = ∅) :
    slotLow context J dbl d = 0 := by
  rw [slotLow, empty, insert_empty_eq, csSup_singleton]

/-- Without an edge whose class does not hold, a slot ends at the end. -/
theorem slot_high_empty {dbl : Bool} {d : Object'} (empty : FailedEdges context J dbl d = ∅) :
    slotHigh context J dbl d = placesEnd dbl := by
  rw [slotHigh, empty, insert_empty_eq, csInf_singleton]

/-- With an edge whose class holds, a slot begins at the highest such edge. -/
theorem slot_low_edge {dbl : Bool} {d : Object'} (some : (HeldEdges context J dbl d).Nonempty) :
    slotLow context J dbl d ∈ HeldEdges context J dbl d := by
  have mem : slotLow context J dbl d ∈ insert 0 (HeldEdges context J dbl d) :=
    Nat.sSup_mem ⟨0, Set.mem_insert _ _⟩ (held_bdd context J dbl d)
  rcases Set.mem_insert_iff.mp mem with zero | held
  · obtain ⟨e, he⟩ := some
    have := held_le he
    have : e = 0 := by omega
    rw [zero, ← this]
    exact he
  · exact held

/-- With an edge whose class does not hold, a slot ends at the lowest such
    edge or at the end, whichever comes first. -/
theorem slot_high_edge {dbl : Bool} {d : Object'} (some : (FailedEdges context J dbl d).Nonempty) :
    sInf (FailedEdges context J dbl d) ∈ FailedEdges context J dbl d ∧
      clamp dbl (sInf (FailedEdges context J dbl d)) = clamp dbl (slotHigh context J dbl d) := by
  have mem := Nat.sInf_mem some
  refine ⟨mem, ?_⟩
  have le := failed_ge mem
  have atEnd := slot_high_le (context := context) (J := J) dbl d
  rcases Set.mem_insert_iff.mp (Nat.sInf_mem (s := insert (placesEnd dbl) (FailedEdges context J dbl d))
      ⟨_, Set.mem_insert _ _⟩) with high | failed
  · change slotHigh context J dbl d = placesEnd dbl at high
    unfold clamp; omega
  · have := Nat.sInf_le failed
    change sInf (FailedEdges context J dbl d) ≤ slotHigh context J dbl d at this
    have same : sInf (FailedEdges context J dbl d) = slotHigh context J dbl d := le_antisymm this le
    rw [same]

/-- The class of an edge holds at a node whose slot has the place `p` exactly
    when the edge is at or below `p`. -/
theorem edge_at_place {dbl : Bool} {d : Object'} {p : ℕ} (low : slotLow context J dbl d ≤ p)
    (high : p < slotHigh context J dbl d) (i : Usize) (h : i.val < (edgesOf context dbl).val.length) :
    J.classes (edgeClass dbl i) d ↔ ((edgesOf context dbl).val[i.val]'h).val ≤ p := by
  constructor
  · intro holds
    exact le_trans (held_le ⟨i, h, rfl, holds⟩) low
  · intro le
    by_contra fails
    have := failed_ge ⟨i, h, rfl, fails⟩
    omega

/-- A place of a value of a format in the clamped slot of a node is in its
    slot. -/
theorem place_in_slot {dbl : Bool} {d : Object'} {b : DatatypeMap.Binary}
    (inSlot : b ∈ Rowl.FloatOrder.Slot (Rowl.Floats.fmt dbl) (clamp dbl (slotLow context J dbl d))
      (clamp dbl (slotHigh context J dbl d))) :
    slotLow context J dbl d ≤ position (Rowl.Floats.fmt dbl) b ∧
      position (Rowl.Floats.fmt dbl) b < slotHigh context J dbl d := by
  obtain ⟨vb, l, u⟩ := inSlot
  have below := Rowl.DataEdges.position_lt_end vb
  unfold clamp at l u
  omega

/-- Two nodes of a format whose slots share a place are in the classes of the
    same edges, and so have the same slot. -/
theorem same_slot {dbl : Bool} {d d' : Object'} {p : ℕ} (low : slotLow context J dbl d ≤ p)
    (high : p < slotHigh context J dbl d) (low' : slotLow context J dbl d' ≤ p)
    (high' : p < slotHigh context J dbl d') :
    (∀ (i : Usize), i.val < (edgesOf context dbl).val.length →
      (J.classes (edgeClass dbl i) d ↔ J.classes (edgeClass dbl i) d')) ∧
    slotLow context J dbl d = slotLow context J dbl d' ∧ slotHigh context J dbl d = slotHigh context J dbl d' := by
  have edges : ∀ (i : Usize) (h : i.val < (edgesOf context dbl).val.length),
      J.classes (edgeClass dbl i) d ↔ J.classes (edgeClass dbl i) d' := fun i h =>
    (edge_at_place low high i h).trans (edge_at_place low' high' i h).symm
  have held : HeldEdges context J dbl d = HeldEdges context J dbl d' := by
    ext e
    constructor
    · rintro ⟨i, h, rfl, holds⟩; exact ⟨i, h, rfl, (edges i h).mp holds⟩
    · rintro ⟨i, h, rfl, holds⟩; exact ⟨i, h, rfl, (edges i h).mpr holds⟩
  have failed : FailedEdges context J dbl d = FailedEdges context J dbl d' := by
    ext e
    constructor
    · rintro ⟨i, h, rfl, fails⟩; exact ⟨i, h, rfl, fun holds => fails ((edges i h).mpr holds)⟩
    · rintro ⟨i, h, rfl, fails⟩; exact ⟨i, h, rfl, fun holds => fails ((edges i h).mp holds)⟩
  exact ⟨edges, by rw [slotLow, slotLow, held], by rw [slotHigh, slotHigh, failed]⟩

variable (context J)

variable {context J}

/-- A subtype of `xsd:string` is a kind of the chain after `xsd:string`. -/
theorem chain_rank {k : datatypes.Kind} {s : DatatypeMap.StringSubtype} (hs : Rowl.Strings.subtypeOf k = some s) :
    ∃ r, chainKind r = k ∧ 1 ≤ r ∧ r < 7 := by
  cases k <;> simp [Rowl.Strings.subtypeOf] at hs
  exacts [⟨1, rfl, by omega, by omega⟩, ⟨2, rfl, by omega, by omega⟩, ⟨6, rfl, by omega, by omega⟩,
    ⟨3, rfl, by omega, by omega⟩, ⟨4, rfl, by omega, by omega⟩, ⟨5, rfl, by omega, by omega⟩]

/-- A subtype of `xsd:string` in use puts `xsd:string` in use. -/
theorem used_string {kinds : data_ontology.Kinds} {k : datatypes.Kind} {s : DatatypeMap.StringSubtype}
    (hs : Rowl.Strings.subtypeOf k = some s) (used : Used kinds k = true) : Used kinds .String = true := by
  cases k <;> simp [Rowl.Strings.subtypeOf] at hs <;> simp_all [Used]

/-- The class of a subtype of `xsd:string` in use lies in the class of
    `xsd:string`. -/
theorem subtype_in_string (kinds : KindFacts context J) {k : datatypes.Kind} {s : DatatypeMap.StringSubtype}
    (hs : Rowl.Strings.subtypeOf k = some s) (used : Used context.kinds k = true) {y : Object'}
    (h : J.classes (kindClass k) y) : J.classes (kindClass .String) y := by
  obtain ⟨r, rfl, lo, hi⟩ := chain_rank hs
  exact kinds.strings r 0 lo hi used (used_string hs used) y h

/-- A node in the class of a subtype of `xsd:string` in use is in the class
    of `xsd:string`, which is in use. -/
theorem subtype_string (kinds : KindFacts context J) {k : datatypes.Kind} {y : Object'}
    (h : J.classes (kindClass k) y) {s : DatatypeMap.StringSubtype} (hs : Rowl.Strings.subtypeOf k = some s)
    (used : Used context.kinds k = true) : Used context.kinds .String = true ∧ J.classes (kindClass .String) y :=
  ⟨used_string hs used, subtype_in_string kinds hs used h⟩

/-- A node in the class of `xsd:dateTimeStamp` in use is in the class of
    `xsd:dateTime`, which is in use. -/
theorem stamp_in_datetime (kinds : KindFacts context J) {y : Object'}
    (used : Used context.kinds .DateTimeStamp = true) (h : J.classes (kindClass .DateTimeStamp) y) :
    Used context.kinds .DateTime = true ∧ J.classes (kindClass .DateTime) y := by
  have usedT : Used context.kinds .DateTime = true := by simp_all [Used]
  exact ⟨usedT, kinds.moments.1 used usedT y h⟩

/-- A node in the class of a kind of time instants in use is in the class of
    no other kind in use. -/
theorem moment_alone (kinds : KindFacts context J) {k k' : datatypes.Kind} (mk : IsMomentKind k)
    (mk' : ¬ IsMomentKind k') (used : Used context.kinds k = true) (used' : Used context.kinds k' = true)
    {y : Object'} (h : J.classes (kindClass k) y) : ¬ J.classes (kindClass k') y := by
  obtain ⟨usedT, inT⟩ : Used context.kinds .DateTime = true ∧ J.classes (kindClass .DateTime) y := by
    cases k <;> simp only [IsMomentKind] at mk
    · exact ⟨used, h⟩
    · exact stamp_in_datetime kinds used h
  have facts := kinds.moments.2.1
  intro h'
  cases k' <;> simp only [Used, Bool.false_eq_true, IsMomentKind, not_true_eq_false] at used' mk'
  · exact facts.1 usedT used' y ⟨inT, h'⟩
  · exact facts.2.1 usedT used' y ⟨inT, h'⟩
  · exact facts.2.2.2.2.1 usedT used' y ⟨inT, h'⟩
  · exact facts.2.2.2.2.2.1 usedT used' y ⟨inT, h'⟩
  · exact facts.2.2.2.2.2.2 usedT used' y ⟨inT, h'⟩
  · exact facts.2.2.2.1 usedT used' y ⟨inT, h'⟩
  · exact facts.2.2.1 usedT used' y ⟨inT, h'⟩
  · exact kinds.moments.2.2.1 usedT used' y ⟨inT, h'⟩
  · exact kinds.moments.2.2.2.1 usedT used' y ⟨inT, h'⟩
  · exact kinds.moments.2.2.2.2 usedT used' y ⟨inT, h'⟩
  case Double => exact kinds.floats.1.2.2.2.2 used' usedT y ⟨h', inT⟩
  case Float => exact kinds.floats.2.1.2.2.2.2 used' usedT y ⟨h', inT⟩
  all_goals
    obtain ⟨usedString, inString⟩ := subtype_string kinds h' rfl used'
    exact facts.2.2.2.2.1 usedT usedString y ⟨inT, inString⟩

/-- A node in the class of a kind of floating-point numbers in use is in the
    class of no other kind in use. -/
theorem float_alone (kinds : KindFacts context J) {k k' : datatypes.Kind} (fk : k = .Double ∨ k = .Float)
    (ne : k' ≠ k) (used : Used context.kinds k = true) (used' : Used context.kinds k' = true)
    {y : Object'} (h : J.classes (kindClass k) y) : ¬ J.classes (kindClass k') y := by
  have apart : FloatApart context.kinds J k := by
    rcases fk with rfl | rfl
    exacts [kinds.floats.1, kinds.floats.2.1]
  obtain ⟨⟨ai, ad, aq, ar, aS, ap, ab⟩, au, ah, a64, adt⟩ := apart
  intro h'
  cases k' <;> simp only [Used, Bool.false_eq_true] at used'
  case Integer => exact ai used used' y ⟨h, h'⟩
  case Decimal => exact ad used used' y ⟨h, h'⟩
  case Rational => exact aq used used' y ⟨h, h'⟩
  case Real => exact ar used used' y ⟨h, h'⟩
  case String => exact aS used used' y ⟨h, h'⟩
  case Plain => exact ap used used' y ⟨h, h'⟩
  case Boolean => exact ab used used' y ⟨h, h'⟩
  case AnyUri => exact au used used' y ⟨h, h'⟩
  case HexBinary => exact ah used used' y ⟨h, h'⟩
  case Base64Binary => exact a64 used used' y ⟨h, h'⟩
  case DateTime => exact adt used used' y ⟨h, h'⟩
  case DateTimeStamp =>
    obtain ⟨usedT, inT⟩ := stamp_in_datetime kinds used' h'
    exact adt used usedT y ⟨h, inT⟩
  case Double =>
    rcases fk with rfl | rfl
    · exact ne rfl
    · exact kinds.floats.2.2 used' used y ⟨h', h⟩
  case Float =>
    rcases fk with rfl | rfl
    · exact kinds.floats.2.2 used used' y ⟨h, h'⟩
    · exact ne rfl
  all_goals
    obtain ⟨usedString, inString⟩ := subtype_string kinds h' rfl used'
    exact aS used usedString y ⟨h, inString⟩

/-- The kinds of the chain after `xsd:string` hold a string exactly as its
    forms. -/
theorem chain_textIn {r : Nat} (lo : 1 ≤ r) (hi : r < 7) (t : List U8) :
    Rowl.Strings.TextIn (chainKind r) t ↔ Rowl.Strings.ChainForm r t := by
  interval_cases r <;> simp [Rowl.Strings.TextIn, Rowl.Strings.subtypeOf, chainKind, Rowl.Strings.ChainForm]

/-- A class of the chain after `xsd:string` that holds at a node in use is
    at most the node's level. -/
theorem le_stringLevel {d : Object'} {i : Nat} (lo : 1 ≤ i) (hi : i < 7) (h : InUse context J (chainKind i) d) :
    i ≤ (stringLevel context J d).val := by
  unfold stringLevel
  interval_cases i <;> split_ifs <;> simp_all

/-- The class of the chain at the level of a string node holds there. -/
theorem stringLevel_holds {d : Object'} (string : InUse context J .String d) :
    InUse context J (chainKind (stringLevel context J d).val) d := by
  unfold stringLevel
  split_ifs <;> assumption

/-- At a string node, a class of the chain in use holds exactly up to the
    node's level. -/
theorem chain_profile (kinds : KindFacts context J) {d : Object'} (string : InUse context J .String d) {i : Nat}
    (hi : i < 7) (used : Used context.kinds (chainKind i) = true) :
    J.classes (kindClass (chainKind i)) d ↔ i ≤ (stringLevel context J d).val := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos i with rfl | pos
    · exact Nat.zero_le _
    · exact le_stringLevel pos hi ⟨used, h⟩
  · intro le
    obtain ⟨usedAt, holdsAt⟩ := stringLevel_holds string
    rcases Nat.eq_or_lt_of_le le with same | lt
    · rw [same]; exact holdsAt
    · exact kinds.strings _ i lt (stringLevel context J d).isLt usedAt used d holdsAt

/-- A numeric node's classes of numeric datatypes in use hold exactly as
    the datatypes contain a real of its level. -/
theorem number_profile (kinds : KindFacts context J) {d : Object'} (numeric : NumericNode context J d)
    {r : ℝ} (atLevel : AtLevel (levelOf context J d) r) (k : datatypes.Kind) (used : Used context.kinds k = true) :
    J.classes (kindClass k) d ↔ Rowl.Datatypes.IsNumeric k ∧ RealIn k r := by
  have notIn : ∀ k', ¬ InUse context J k' d → Used context.kinds k' = true → ¬ J.classes (kindClass k') d :=
    fun k' h u c => h ⟨u, c⟩
  unfold levelOf at atLevel
  by_cases hi : InUse context J .Integer d
  · simp only [hi, ↓reduceIte, AtLevel] at atLevel
    obtain ⟨ui, ai⟩ := hi
    have dec := Rowl.DataReals.integer_decimal atLevel
    have rat := Rowl.DataReals.decimal_rational dec
    cases k <;> simp only [Used, Bool.false_eq_true] at used <;>
      simp only [Rowl.Datatypes.IsNumeric, RealIn, true_and, false_and, iff_false, not_true_eq_false]
    · exact ⟨fun _ => atLevel, fun _ => ai⟩
    · exact ⟨fun _ => dec, fun _ => kinds.integerDecimal ui used d ai⟩
    · exact fun h => kinds.integerString ui used d ⟨ai, h⟩
    · exact fun h => kinds.integerPlain ui used d ⟨ai, h⟩
    · exact fun h => kinds.integerBoolean ui used d ⟨ai, h⟩
    · exact ⟨fun _ => trivial, fun _ => kinds.integerReal ui used d ai⟩
    · exact ⟨fun _ => rat, fun _ => kinds.integerRational ui used d ai⟩
    · exact fun h => kinds.sequences.1.1 used ui d ⟨h, ai⟩
    · exact fun h => kinds.sequences.2.1.1 used ui d ⟨h, ai⟩
    · exact fun h => kinds.sequences.2.2.1.1 used ui d ⟨h, ai⟩
    case DateTime => exact fun h => moment_alone kinds (k := .DateTime) trivial (by simp [IsMomentKind]) used ui h ai
    case DateTimeStamp =>
      exact fun h => moment_alone kinds (k := .DateTimeStamp) trivial (by simp [IsMomentKind]) used ui h ai
    case Double => exact fun h => float_alone kinds (k := .Double) (.inl rfl) (fun e => by cases e) used ui h ai
    case Float => exact fun h => float_alone kinds (k := .Float) (.inr rfl) (fun e => by cases e) used ui h ai
    all_goals
      intro h
      obtain ⟨usedString, inString⟩ := subtype_string kinds h rfl used
      exact kinds.integerString ui usedString d ⟨ai, inString⟩
  by_cases hd : InUse context J .Decimal d
  · simp only [hi, hd, ↓reduceIte, AtLevel] at atLevel
    obtain ⟨ud, ad⟩ := hd
    have rat := Rowl.DataReals.decimal_rational atLevel.1
    cases k <;> simp only [Used, Bool.false_eq_true] at used <;>
      simp only [Rowl.Datatypes.IsNumeric, RealIn, true_and, false_and, iff_false, not_true_eq_false]
    · exact ⟨fun h => absurd h (notIn _ hi used), fun h => absurd h atLevel.2⟩
    · exact ⟨fun _ => atLevel.1, fun _ => ad⟩
    · exact fun h => kinds.decimalString ud used d ⟨ad, h⟩
    · exact fun h => kinds.decimalPlain ud used d ⟨ad, h⟩
    · exact fun h => kinds.decimalBoolean ud used d ⟨ad, h⟩
    · exact ⟨fun _ => trivial, fun _ => kinds.decimalReal ud used d ad⟩
    · exact ⟨fun _ => rat, fun _ => kinds.decimalRational ud used d ad⟩
    · exact fun h => kinds.sequences.1.2.1 used ud d ⟨h, ad⟩
    · exact fun h => kinds.sequences.2.1.2.1 used ud d ⟨h, ad⟩
    · exact fun h => kinds.sequences.2.2.1.2.1 used ud d ⟨h, ad⟩
    case DateTime => exact fun h => moment_alone kinds (k := .DateTime) trivial (by simp [IsMomentKind]) used ud h ad
    case DateTimeStamp =>
      exact fun h => moment_alone kinds (k := .DateTimeStamp) trivial (by simp [IsMomentKind]) used ud h ad
    case Double => exact fun h => float_alone kinds (k := .Double) (.inl rfl) (fun e => by cases e) used ud h ad
    case Float => exact fun h => float_alone kinds (k := .Float) (.inr rfl) (fun e => by cases e) used ud h ad
    all_goals
      intro h
      obtain ⟨usedString, inString⟩ := subtype_string kinds h rfl used
      exact kinds.decimalString ud usedString d ⟨ad, inString⟩
  by_cases hq : InUse context J .Rational d
  · simp only [hi, hd, hq, ↓reduceIte, AtLevel] at atLevel
    obtain ⟨uq, aq⟩ := hq
    have notInt : ¬ RealIn .Integer r := fun h => atLevel.2 (Rowl.DataReals.integer_decimal h)
    cases k <;> simp only [Used, Bool.false_eq_true] at used <;>
      simp only [Rowl.Datatypes.IsNumeric, RealIn, true_and, false_and, iff_false, not_true_eq_false]
    · exact ⟨fun h => absurd h (notIn _ hi used), fun h => absurd h notInt⟩
    · exact ⟨fun h => absurd h (notIn _ hd used), fun h => absurd h atLevel.2⟩
    · exact fun h => kinds.rationalString uq used d ⟨aq, h⟩
    · exact fun h => kinds.rationalPlain uq used d ⟨aq, h⟩
    · exact fun h => kinds.rationalBoolean uq used d ⟨aq, h⟩
    · exact ⟨fun _ => trivial, fun _ => kinds.rationalReal uq used d aq⟩
    · exact ⟨fun _ => atLevel.1, fun _ => aq⟩
    · exact fun h => kinds.sequences.1.2.2.1 used uq d ⟨h, aq⟩
    · exact fun h => kinds.sequences.2.1.2.2.1 used uq d ⟨h, aq⟩
    · exact fun h => kinds.sequences.2.2.1.2.2.1 used uq d ⟨h, aq⟩
    case DateTime => exact fun h => moment_alone kinds (k := .DateTime) trivial (by simp [IsMomentKind]) used uq h aq
    case DateTimeStamp =>
      exact fun h => moment_alone kinds (k := .DateTimeStamp) trivial (by simp [IsMomentKind]) used uq h aq
    case Double => exact fun h => float_alone kinds (k := .Double) (.inl rfl) (fun e => by cases e) used uq h aq
    case Float => exact fun h => float_alone kinds (k := .Float) (.inr rfl) (fun e => by cases e) used uq h aq
    all_goals
      intro h
      obtain ⟨usedString, inString⟩ := subtype_string kinds h rfl used
      exact kinds.rationalString uq usedString d ⟨aq, inString⟩
  have hr : InUse context J .Real d := by
    rcases numeric with h | h | h | h
    · exact absurd h hi
    · exact absurd h hd
    · exact absurd h hq
    · exact h
  simp only [hi, hd, hq, ↓reduceIte, AtLevel] at atLevel
  obtain ⟨ur, ar⟩ := hr
  have notDec : ¬ RealIn .Decimal r := fun h => atLevel (Rowl.DataReals.decimal_rational h)
  have notInt : ¬ RealIn .Integer r := fun h => notDec (Rowl.DataReals.integer_decimal h)
  cases k <;> simp only [Used, Bool.false_eq_true] at used <;>
    simp only [Rowl.Datatypes.IsNumeric, RealIn, true_and, false_and, iff_false, not_true_eq_false]
  · exact ⟨fun h => absurd h (notIn _ hi used), fun h => absurd h notInt⟩
  · exact ⟨fun h => absurd h (notIn _ hd used), fun h => absurd h notDec⟩
  · exact fun h => kinds.realString ur used d ⟨ar, h⟩
  · exact fun h => kinds.realPlain ur used d ⟨ar, h⟩
  · exact fun h => kinds.realBoolean ur used d ⟨ar, h⟩
  · exact ⟨fun _ => trivial, fun _ => ar⟩
  · exact ⟨fun h => absurd h (notIn _ hq used), fun h => absurd h atLevel⟩
  · exact fun h => kinds.sequences.1.2.2.2.1 used ur d ⟨h, ar⟩
  · exact fun h => kinds.sequences.2.1.2.2.2.1 used ur d ⟨h, ar⟩
  · exact fun h => kinds.sequences.2.2.1.2.2.2.1 used ur d ⟨h, ar⟩
  case DateTime => exact fun h => moment_alone kinds (k := .DateTime) trivial (by simp [IsMomentKind]) used ur h ar
  case DateTimeStamp =>
    exact fun h => moment_alone kinds (k := .DateTimeStamp) trivial (by simp [IsMomentKind]) used ur h ar
  case Double => exact fun h => float_alone kinds (k := .Double) (.inl rfl) (fun e => by cases e) used ur h ar
  case Float => exact fun h => float_alone kinds (k := .Float) (.inr rfl) (fun e => by cases e) used ur h ar
  all_goals
    intro h
    obtain ⟨usedString, inString⟩ := subtype_string kinds h rfl used
    exact kinds.realString ur usedString d ⟨ar, inString⟩

/-- A node that is no number has the classes of the strings, the plain
    literals and the values outside every datatype as its region says. -/
theorem text_profile (kinds : KindFacts context J) {d : Object'} (notNumeric : ¬ NumericNode context J d)
    (notBool : ¬ InUse context J .Boolean d) (cs : List regions.Cut) (lits : Set ℝ) (n : ℕ) (k : datatypes.Kind)
    (used : Used context.kinds k = true) :
    J.classes (kindClass k) d ↔ RegionIn cs lits (regionOf context J order d) n k := by
  have notIn : ∀ k', ¬ InUse context J k' d → Used context.kinds k' = true → ¬ J.classes (kindClass k') d :=
    fun k' h u c => h ⟨u, c⟩
  have ni : ¬ InUse context J .Integer d := fun h => notNumeric (.inl h)
  have nd : ¬ InUse context J .Decimal d := fun h => notNumeric (.inr (.inl h))
  have nq : ¬ InUse context J .Rational d := fun h => notNumeric (.inr (.inr (.inl h)))
  have nr : ¬ InUse context J .Real d := fun h => notNumeric (.inr (.inr (.inr h)))
  unfold regionOf
  simp only [notNumeric, ↓reduceIte]
  by_cases hs : InUse context J .String d
  · simp only [hs, ↓reduceIte, RegionIn]
    have string := hs
    obtain ⟨us, ast⟩ := hs
    have level := (stringLevel context J d).isLt
    by_cases sub : ∃ s, Rowl.Strings.subtypeOf k = some s
    · obtain ⟨s, hsub⟩ := sub
      obtain ⟨r, rfl, lo, hi⟩ := chain_rank hsub
      rw [chain_profile kinds string hi used, chain_textIn lo hi, Rowl.Strings.stringAt_form level hi]
    have classic : ∀ t, Rowl.Strings.TextIn k t ↔ k = .String ∨ k = .Plain := by
      intro t
      simp only [Rowl.Strings.TextIn]
      constructor
      · rintro (h | h | ⟨s, hs, _⟩)
        exacts [.inl h, .inr h, absurd ⟨s, hs⟩ sub]
      · rintro (h | h)
        exacts [.inl h, .inr (.inl h)]
    rw [classic]
    cases k <;> simp only [Used, Bool.false_eq_true] at used <;>
      (try simp only [Rowl.Strings.subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
      simp only [reduceCtorEq, or_false, false_or, or_self, iff_true, iff_false, true_or, or_true]
    · exact notIn _ ni used
    · exact notIn _ nd used
    · exact ast
    · exact kinds.stringPlain us used d ast
    · exact fun h => kinds.stringBoolean us used d ⟨ast, h⟩
    · exact notIn _ nr used
    · exact notIn _ nq used
    · exact fun h => kinds.sequences.1.2.2.2.2.1 used us d ⟨h, ast⟩
    · exact fun h => kinds.sequences.2.1.2.2.2.2.1 used us d ⟨h, ast⟩
    · exact fun h => kinds.sequences.2.2.1.2.2.2.2.1 used us d ⟨h, ast⟩
    · exact fun h => moment_alone kinds (k := .DateTime) trivial (by simp [IsMomentKind]) used us h ast
    · exact fun h => moment_alone kinds (k := .DateTimeStamp) trivial (by simp [IsMomentKind]) used us h ast
    · exact fun h => float_alone kinds (k := .Double) (.inl rfl) (fun e => by cases e) used us h ast
    · exact fun h => float_alone kinds (k := .Float) (.inr rfl) (fun e => by cases e) used us h ast
  have notSub : ∀ {k' : datatypes.Kind}, J.classes (kindClass k') d → ∀ {s : DatatypeMap.StringSubtype},
      Rowl.Strings.subtypeOf k' = some s → Used context.kinds k' = true → False :=
    fun {_} h {_} hsub used => hs (subtype_string kinds h hsub used)
  by_cases hp : InUse context J .Plain d
  · simp only [hs, hp, ↓reduceIte, RegionIn]
    obtain ⟨up, ap⟩ := hp
    cases k <;> simp only [Used, Bool.false_eq_true] at used <;> simp only [reduceCtorEq, iff_true, iff_false]
    · exact notIn _ ni used
    · exact notIn _ nd used
    · exact notIn _ hs used
    · exact ap
    · exact fun h => kinds.plainBoolean up used d ⟨ap, h⟩
    · exact notIn _ nr used
    · exact notIn _ nq used
    · exact fun h => kinds.sequences.1.2.2.2.2.2.1 used up d ⟨h, ap⟩
    · exact fun h => kinds.sequences.2.1.2.2.2.2.2.1 used up d ⟨h, ap⟩
    · exact fun h => kinds.sequences.2.2.1.2.2.2.2.2.1 used up d ⟨h, ap⟩
    case DateTime => exact fun h => moment_alone kinds (k := .DateTime) trivial (by simp [IsMomentKind]) used up h ap
    case DateTimeStamp =>
      exact fun h => moment_alone kinds (k := .DateTimeStamp) trivial (by simp [IsMomentKind]) used up h ap
    case Double => exact fun h => float_alone kinds (k := .Double) (.inl rfl) (fun e => by cases e) used up h ap
    case Float => exact fun h => float_alone kinds (k := .Float) (.inr rfl) (fun e => by cases e) used up h ap
    all_goals exact fun h => notSub h rfl used
  by_cases hu : InUse context J .AnyUri d
  · simp only [hs, hp, hu, ↓reduceIte, RegionIn, sequenceKind]
    obtain ⟨uu, au⟩ := hu
    cases k <;> simp only [Used, Bool.false_eq_true] at used <;>
      simp only [reduceCtorEq, iff_false, iff_true]
    · exact notIn _ ni used
    · exact notIn _ nd used
    · exact notIn _ hs used
    · exact notIn _ hp used
    · exact notIn _ notBool used
    · exact notIn _ nr used
    · exact notIn _ nq used
    · exact au
    · exact fun h => kinds.sequences.2.2.2.1 uu used d ⟨au, h⟩
    · exact fun h => kinds.sequences.2.2.2.2.1 uu used d ⟨au, h⟩
    case DateTime => exact fun h => moment_alone kinds (k := .DateTime) trivial (by simp [IsMomentKind]) used uu h au
    case DateTimeStamp =>
      exact fun h => moment_alone kinds (k := .DateTimeStamp) trivial (by simp [IsMomentKind]) used uu h au
    case Double => exact fun h => float_alone kinds (k := .Double) (.inl rfl) (fun e => by cases e) used uu h au
    case Float => exact fun h => float_alone kinds (k := .Float) (.inr rfl) (fun e => by cases e) used uu h au
    all_goals exact fun h => notSub h rfl used
  by_cases hh : InUse context J .HexBinary d
  · simp only [hs, hp, hu, hh, ↓reduceIte, RegionIn, sequenceKind]
    obtain ⟨uh, ah⟩ := hh
    cases k <;> simp only [Used, Bool.false_eq_true] at used <;>
      simp only [reduceCtorEq, iff_false, iff_true]
    · exact notIn _ ni used
    · exact notIn _ nd used
    · exact notIn _ hs used
    · exact notIn _ hp used
    · exact notIn _ notBool used
    · exact notIn _ nr used
    · exact notIn _ nq used
    · exact notIn _ hu used
    · exact ah
    · exact fun h => kinds.sequences.2.2.2.2.2 uh used d ⟨ah, h⟩
    case DateTime => exact fun h => moment_alone kinds (k := .DateTime) trivial (by simp [IsMomentKind]) used uh h ah
    case DateTimeStamp =>
      exact fun h => moment_alone kinds (k := .DateTimeStamp) trivial (by simp [IsMomentKind]) used uh h ah
    case Double => exact fun h => float_alone kinds (k := .Double) (.inl rfl) (fun e => by cases e) used uh h ah
    case Float => exact fun h => float_alone kinds (k := .Float) (.inr rfl) (fun e => by cases e) used uh h ah
    all_goals exact fun h => notSub h rfl used
  by_cases hb : InUse context J .Base64Binary d
  · simp only [hs, hp, hu, hh, hb, ↓reduceIte, RegionIn, sequenceKind]
    obtain ⟨ub, ab⟩ := hb
    cases k <;> simp only [Used, Bool.false_eq_true] at used <;>
      simp only [reduceCtorEq, iff_false, iff_true]
    · exact notIn _ ni used
    · exact notIn _ nd used
    · exact notIn _ hs used
    · exact notIn _ hp used
    · exact notIn _ notBool used
    · exact notIn _ nr used
    · exact notIn _ nq used
    · exact notIn _ hu used
    · exact notIn _ hh used
    · exact ab
    case DateTime => exact fun h => moment_alone kinds (k := .DateTime) trivial (by simp [IsMomentKind]) used ub h ab
    case DateTimeStamp =>
      exact fun h => moment_alone kinds (k := .DateTimeStamp) trivial (by simp [IsMomentKind]) used ub h ab
    case Double => exact fun h => float_alone kinds (k := .Double) (.inl rfl) (fun e => by cases e) used ub h ab
    case Float => exact fun h => float_alone kinds (k := .Float) (.inr rfl) (fun e => by cases e) used ub h ab
    all_goals exact fun h => notSub h rfl used
  by_cases hm : InUse context J .DateTime d
  · simp only [hs, hp, hu, hh, hb, hm, ↓reduceIte, RegionIn, decide_eq_true_eq]
    obtain ⟨um, am⟩ := hm
    cases k <;> simp only [Used, Bool.false_eq_true] at used <;>
      simp only [reduceCtorEq, eq_self_iff_true, iff_false, iff_true, false_or, or_false, false_and, true_and,
        true_or]
    · exact notIn _ ni used
    · exact notIn _ nd used
    · exact notIn _ hs used
    · exact notIn _ hp used
    · exact notIn _ notBool used
    · exact notIn _ nr used
    · exact notIn _ nq used
    · exact notIn _ hu used
    · exact notIn _ hh used
    · exact notIn _ hb used
    case DateTime => exact am
    case DateTimeStamp => exact ⟨fun h => ⟨used, h⟩, fun h => h.2⟩
    case Double => exact fun h => float_alone kinds (k := .Double) (.inl rfl) (fun e => by cases e) used um h am
    case Float => exact fun h => float_alone kinds (k := .Float) (.inr rfl) (fun e => by cases e) used um h am
    all_goals exact fun h => notSub h rfl used
  by_cases hdb : InUse context J .Double d
  · simp only [hs, hp, hu, hh, hb, hm, hdb, ↓reduceIte, RegionIn, formatKind]
    obtain ⟨udb, adb⟩ := hdb
    cases k <;> simp only [Used, Bool.false_eq_true] at used <;>
      simp only [reduceCtorEq, iff_false, iff_true]
    · exact notIn _ ni used
    · exact notIn _ nd used
    · exact notIn _ hs used
    · exact notIn _ hp used
    · exact notIn _ notBool used
    · exact notIn _ nr used
    · exact notIn _ nq used
    · exact notIn _ hu used
    · exact notIn _ hh used
    · exact notIn _ hb used
    case DateTime => exact notIn _ hm used
    case DateTimeStamp => exact fun h => hm (stamp_in_datetime kinds used h)
    case Double => exact adb
    case Float => exact float_alone kinds (k := .Double) (k' := .Float) (.inl rfl) (fun e => by cases e) udb used adb
    all_goals exact fun h => notSub h rfl used
  by_cases hfl : InUse context J .Float d
  · simp only [hs, hp, hu, hh, hb, hm, hdb, hfl, ↓reduceIte, RegionIn, formatKind]
    obtain ⟨ufl, afl⟩ := hfl
    cases k <;> simp only [Used, Bool.false_eq_true] at used <;>
      simp only [reduceCtorEq, iff_false, iff_true]
    · exact notIn _ ni used
    · exact notIn _ nd used
    · exact notIn _ hs used
    · exact notIn _ hp used
    · exact notIn _ notBool used
    · exact notIn _ nr used
    · exact notIn _ nq used
    · exact notIn _ hu used
    · exact notIn _ hh used
    · exact notIn _ hb used
    case DateTime => exact notIn _ hm used
    case DateTimeStamp => exact fun h => hm (stamp_in_datetime kinds used h)
    case Double => exact notIn _ hdb used
    case Float => exact afl
    all_goals exact fun h => notSub h rfl used
  · simp only [hs, hp, hu, hh, hb, hm, hdb, hfl, ↓reduceIte, RegionIn, iff_false]
    cases k <;> simp only [Used, Bool.false_eq_true] at used
    · exact notIn _ ni used
    · exact notIn _ nd used
    · exact notIn _ hs used
    · exact notIn _ hp used
    · exact notIn _ notBool used
    · exact notIn _ nr used
    · exact notIn _ nq used
    · exact notIn _ hu used
    · exact notIn _ hh used
    · exact notIn _ hb used
    case DateTime => exact notIn _ hm used
    case DateTimeStamp => exact fun h => hm (stamp_in_datetime kinds used h)
    case Double => exact notIn _ hdb used
    case Float => exact notIn _ hfl used
    all_goals exact fun h => notSub h rfl used

end Profile

/-! ### The cuts in order at a model of the encoding -/

section Order
variable {Object' : Type u} {Value' : Type x}

/-- What a model of the encoding brings for an OWL model to be made from it:
    the context's facts from the encoding, the encoding's own axioms, and the
    built-in meanings of `owl:Thing`, `owl:topObjectProperty` and
    `owl:bottomObjectProperty`. -/
structure Setting (context : data_ontology.Context) (capacity : Nat) (bits : Usize) (order : List Usize)
    (J : Interpretation Object' Value') : Prop where
  good : Good context
  frame : Frame context capacity bits order J
  enough : context.values.val.length ≤ 2 ^ bits.val
  sorted : context.kinds.ordered = true → Ordered context.cuts.val (order.map (·.val)) ∧ PointsNamed context order 1
  fine : FineCuts context.cuts.val
  valuesFit : ValuesFit context
  thing : ∀ d, J.classes thing d
  top : ∀ y y', J.objectProperties topObject y y'
  bottom : ∀ y y', ¬ J.objectProperties bottomObject y y'

variable {context : data_ontology.Context} {capacity : Nat} {bits : Usize} {order : List Usize}
  {J : Interpretation Object' Value'}

theorem order_in (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    {k : Nat} (hk : k < order.length) : order[k].val < context.cuts.val.length :=
  (setting.sorted ordered).1.2.1 _ (List.mem_map_of_mem (List.getElem_mem hk))

theorem cuts_length (ordered : context.kinds.ordered = true) :
    (orderedCuts context order).length = order.length := by
  simp [orderedCuts, ordered]

theorem cuts_empty (unordered : ¬ context.kinds.ordered = true) : orderedCuts context order = [] := by
  simp [orderedCuts, unordered]

theorem cuts_at (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    {k : Nat} (hk : k < order.length) :
    cutAt (orderedCuts context order) k = context.cuts.val[order[k].val]'(order_in setting ordered hk) := by
  have hk' : k < (orderedCuts context order).length := by rw [cuts_length ordered]; exact hk
  rw [Rowl.Regions.cutAt_eq _ _ hk']
  simp only [orderedCuts, ordered, ↓reduceIte, List.getElem_map]
  exact Rowl.Regions.cutAt_eq _ _ _

theorem cuts_sorted (setting : Setting context capacity bits order J) :
    (orderedCuts context order).Pairwise CutBefore := by
  unfold orderedCuts
  split_ifs with ordered
  · have := Rowl.Regions.ordered_pairwise (setting.sorted ordered).1
    rw [List.pairwise_map] at this ⊢
    exact this
  · exact List.Pairwise.nil

theorem cuts_fit (setting : Setting context capacity bits order J) {k : Nat}
    (hk : k < (orderedCuts context order).length) : Rowl.Regions.Fit (cutAt (orderedCuts context order) k) := by
  by_cases ordered : context.kinds.ordered = true
  · rw [cuts_length ordered] at hk
    rw [cuts_at setting ordered hk]
    exact setting.fine.1 _ (List.getElem_mem _)
  · rw [cuts_empty ordered] at hk; simp at hk

theorem before_iff (setting : Setting context capacity bits order J) {k k' : Nat}
    (hk : k < (orderedCuts context order).length) (hk' : k' < (orderedCuts context order).length) :
    CutBefore (cutAt (orderedCuts context order) k) (cutAt (orderedCuts context order) k') ↔ k < k' := by
  have sorted := cuts_sorted setting
  rw [Rowl.Regions.cutAt_eq _ _ hk, Rowl.Regions.cutAt_eq _ _ hk']
  constructor
  · intro before
    by_contra ge
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt ge) with gt | eq
    · exact Rowl.Regions.cutBefore_asymm before (List.pairwise_iff_getElem.mp sorted _ _ hk' hk gt)
    · subst eq; exact Rowl.Regions.cutBefore_irrefl _ before
  · intro lt
    exact List.pairwise_iff_getElem.mp sorted _ _ hk hk' lt

theorem cutBefore_le {a b : regions.Cut} (before : CutBefore a b) :
    Rowl.Datatypes.numValue a.value ≤ Rowl.Datatypes.numValue b.value := by
  rcases before with lt | ⟨same, _, _⟩
  · exact le_of_lt lt
  · rw [same]

/-- The classes of the cuts hold at a node for the cuts up to some point of
    the order and for no later one. -/
theorem cuts_down (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    {y : Object'} : ∀ {k : Nat} (hk : k < order.length), J.classes (cutClass order[k]) y →
      ∀ {j : Nat} (hj : j ≤ k), J.classes (cutClass (order[j]'(by omega))) y := by
  intro k
  induction k with
  | zero =>
    intro hk inK j hj
    have : j = 0 := by omega
    subst this
    exact inK
  | succ k ih =>
    intro hk inK j hj
    by_cases same : j = k + 1
    · subst same; exact inK
    · have step := ((setting.frame.regions.1 ordered).2 (k + 1) hk (by omega) (by omega)).1 y inK
      have eq : order[k + 1 - 1]'(by omega) = order[k]'(by omega) := by simp
      rw [eq] at step
      exact ih (by omega) step (by omega)

theorem position_cut (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    (y : Object') {k : Nat} (hk : k < order.length) :
    J.classes (cutClass order[k]) y ↔ k < positionOf context J order y := by
  have len := cuts_length (context := context) (order := order) ordered
  have getD : ∀ k (h : k < order.length), order.getD k 0#usize = order[k] := fun k h => by
    rw [List.getD_eq_getElem]
  unfold positionOf
  split_ifs with h
  · constructor
    · intro inK
      by_contra ge
      have spec := Nat.find_spec h
      have specLt : Nat.find h < order.length := by rw [← len]; exact spec.1
      apply spec.2
      rw [getD _ specLt]
      exact cuts_down setting ordered hk inK (by omega)
    · intro lt
      by_contra notIn
      exact Nat.find_min h lt ⟨by rw [len]; exact hk, by rw [getD _ hk]; exact notIn⟩
  · rw [len]
    constructor
    · exact fun _ => hk
    · intro _
      by_contra notIn
      exact h ⟨k, by rw [len]; exact hk, by rw [getD _ hk]; exact notIn⟩

/-- Every cut has a place in the order. -/
theorem cut_place (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    (i : Nat) (hi : i < context.cuts.val.length) : ∃ (k : Nat) (hk : k < order.length), order[k].val = i := by
  have member := (setting.sorted ordered).1.2.2.1 i hi
  obtain ⟨a, inOrder, rfl⟩ := List.mem_map.mp member
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem inOrder
  exact ⟨k, hk, rfl⟩

/-- A data node that is a literal value's individual. -/
def LiteralNode (context : data_ontology.Context) (J : Interpretation Object' Value') (d : Object') : Prop :=
  ∃ i : Usize, i.val < context.values.val.length ∧ J.namedIndividuals (valueIndividual i) = d

/-- A numeric literal value's individual is in the classes of exactly the
    cuts that contain its value. -/
theorem literal_cut (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    {i : Usize} (hi : i.val < context.values.val.length) (number : Rowl.Datatypes.IsNumber context.values.val[i.val])
    {k : Nat} (hk : k < order.length) :
    J.classes (cutClass order[k]) (J.namedIndividuals (valueIndividual i)) ↔
      InCut (cutAt (orderedCuts context order) k) (Rowl.Datatypes.numValue context.values.val[i.val]) := by
  rw [cuts_at setting ordered hk]
  exact (setting.frame.values i hi).2.2.2.1 ordered number order[k] (order_in setting ordered hk)

theorem real_used (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true) :
    Used context.kinds .Real = true :=
  setting.good.2.2.2.2 ordered

/-- Only numbers are in the classes of cuts. -/
theorem cut_real (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    {y : Object'} {k : Nat} (hk : k < order.length) (inK : J.classes (cutClass order[k]) y) :
    J.classes (kindClass .Real) y := by
  have first := cuts_down setting ordered hk inK (j := 0) (by omega)
  have head : order.head? = some (order[0]'(by omega)) := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem]
  exact (setting.frame.regions.1 ordered).1 _ head y first

/-- A literal value that is no number has its individual in no cut's class. -/
theorem literal_no_cut (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    {i : Usize} (hi : i.val < context.values.val.length)
    (notNumber : ¬ Rowl.Datatypes.IsNumber context.values.val[i.val]) {k : Nat} (hk : k < order.length) :
    ¬ J.classes (cutClass order[k]) (J.namedIndividuals (valueIndividual i)) := by
  intro inK
  have real := ((setting.frame.values i hi).2.1 .Real (real_used setting ordered)).mp (cut_real setting ordered hk inK)
  revert notNumber real
  cases context.values.val[i.val] <;> simp [InKind, Rowl.Datatypes.IsNumber, Rowl.Strings.TextIn,
    Rowl.Strings.subtypeOf]

theorem usize_index {α : Type} (l : alloc.vec.Vec α) (j : Nat) (h : j < l.val.length) : ∃ i : Usize, i.val = j := by
  have bound := l.property
  have lt : j < 2 ^ UScalarTy.Usize.numBits := by
    have := Usize.max_def
    have pos : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
    simp only [Usize.numBits] at this
    have : l.val.length ≤ Usize.max := bound
    omega
  exact ⟨Usize.ofNatCore j lt, UScalar.ofNatCore_val_eq lt⟩

/-- A node that is no literal value's individual is between two cuts of
    different numbers, or beyond all cuts. -/
theorem not_point (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    {d : Object'} (notLiteral : ¬ LiteralNode context J d) (pos : 0 < positionOf context J order d)
    (inside : positionOf context J order d < order.length) :
    (cutAt (orderedCuts context order) (positionOf context J order d - 1)).value ≠
      (cutAt (orderedCuts context order) (positionOf context J order d)).value := by
  intro same
  have hp1 : positionOf context J order d - 1 < order.length := by omega
  rw [cuts_at setting ordered hp1, cuts_at setting ordered inside] at same
  have same' : (cutAt context.cuts.val order[positionOf context J order d - 1].val).value =
      (cutAt context.cuts.val order[positionOf context J order d].val).value := by
    rw [Rowl.Regions.cutAt_eq _ _ (order_in setting ordered hp1), Rowl.Regions.cutAt_eq _ _ (order_in setting ordered inside)]
    exact same
  have named := (setting.sorted ordered).2 _ inside (by omega) pos same'
  obtain ⟨j, hj, at_j⟩ := List.getElem_of_mem named
  obtain ⟨i, rfl⟩ := usize_index context.values j hj
  have between := ((setting.frame.regions.1 ordered).2 _ inside (by omega) pos).2.1 same' i hj at_j d
    ((position_cut setting ordered d hp1).mpr (by omega)) (fun h => by
      have := (position_cut setting ordered d inside).mp h; omega)
  exact notLiteral ⟨i, hj, between⟩

end Order

/-! ### Which regions are infinite -/

section Sizes
variable {cs : List regions.Cut}

theorem interval_empty (r : ℝ) : InInterval [] 0 r :=
  ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h (by simp)⟩

theorem interval_below (r : ℝ) (lt : r < Rowl.Datatypes.numValue (cutAt cs 0).value) : InInterval cs 0 r := by
  refine ⟨fun h => absurd h (lt_irrefl 0), fun _ inCut => ?_⟩
  unfold InCut at inCut
  split_ifs at inCut <;> linarith

theorem interval_above (r : ℝ)
    (gt : (Rowl.Datatypes.numValue (cutAt cs (cs.length - 1)).value : ℝ) < r) : InInterval cs cs.length r := by
  refine ⟨fun _ => ?_, fun h => absurd h (lt_irrefl _)⟩
  unfold InCut
  split_ifs <;> linarith

theorem interval_between {p : Nat} (r : ℝ) (lo : (Rowl.Datatypes.numValue (cutAt cs (p - 1)).value : ℝ) < r)
    (hi : r < Rowl.Datatypes.numValue (cutAt cs p).value) : InInterval cs p r := by
  refine ⟨fun _ => ?_, fun _ inCut => ?_⟩
  · unfold InCut; split_ifs <;> linarith
  · unfold InCut at inCut; split_ifs at inCut <;> linarith

theorem dense_region {lits : Set ℝ} (hl : lits.Finite) {p ℓ : Nat} (level : 1 ≤ ℓ) {a b : ℝ} (lt : a < b)
    (sub : ∀ r, a < r → r < b → InInterval cs p r) : (regionSet cs lits p ℓ).Infinite := by
  refine Set.Infinite.mono ?_ ((Rowl.DataReals.level_infinite lt ℓ level).sdiff hl)
  rintro r ⟨⟨atL, lo, hi⟩, notLit⟩
  exact ⟨sub r lo hi, atL, notLit⟩

/-- Every region of a node that is no literal value's individual is
    infinite but a bounded run of integers. -/
theorem region_cases (sorted : cs.Pairwise CutBefore) {lits : Set ℝ} (hl : lits.Finite) {p ℓ : Nat}
    (hp : p ≤ cs.length)
    (notPoint : 0 < p → p < cs.length → (cutAt cs (p - 1)).value ≠ (cutAt cs p).value) :
    (regionSet cs lits p ℓ).Infinite ∨ (ℓ = 0 ∧ 0 < p ∧ p < cs.length) := by
  by_cases zero : ℓ = 0
  · subst zero
    by_cases bounded : 0 < p ∧ p < cs.length
    · exact .inr ⟨rfl, bounded⟩
    · left
      by_cases empty : cs.length = 0
      · have : p = 0 := by omega
        subst this
        refine Set.Infinite.mono ?_ ((Rowl.DataReals.integers_above 0).sdiff hl)
        rintro r ⟨⟨atL, _⟩, notLit⟩
        refine ⟨?_, atL, notLit⟩
        rw [List.eq_nil_of_length_eq_zero empty]; exact interval_empty r
      · by_cases low : p = 0
        · subst low
          refine Set.Infinite.mono ?_
            ((Rowl.DataReals.integers_below (Rowl.Datatypes.numValue (cutAt cs 0).value)).sdiff hl)
          rintro r ⟨⟨atL, lt⟩, notLit⟩
          exact ⟨interval_below r lt, atL, notLit⟩
        · have top : p = cs.length := by omega
          subst top
          refine Set.Infinite.mono ?_
            ((Rowl.DataReals.integers_above (Rowl.Datatypes.numValue (cutAt cs (cs.length - 1)).value)).sdiff hl)
          rintro r ⟨⟨atL, gt⟩, notLit⟩
          exact ⟨interval_above r gt, atL, notLit⟩
  · left
    have level : 1 ≤ ℓ := by omega
    by_cases empty : cs.length = 0
    · have : p = 0 := by omega
      subst this
      exact dense_region hl level (zero_lt_one' ℝ) (fun r _ _ => by
        rw [List.eq_nil_of_length_eq_zero empty]; exact interval_empty r)
    · by_cases low : p = 0
      · subst low
        set c : ℝ := ((Rowl.Datatypes.numValue (cutAt cs 0).value : ℚ) : ℝ)
        exact dense_region hl level (show c - 1 < c by linarith) (fun r _ hi => interval_below r hi)
      · by_cases top : p = cs.length
        · subst top
          set c : ℝ := ((Rowl.Datatypes.numValue (cutAt cs (cs.length - 1)).value : ℚ) : ℝ)
          exact dense_region hl level (show c < c + 1 by linarith) (fun r lo _ => interval_above r lo)
        · have differ := notPoint (by omega) (by omega)
          have before : CutBefore (cutAt cs (p - 1)) (cutAt cs p) := by
            rw [Rowl.Regions.cutAt_eq _ _ (by omega), Rowl.Regions.cutAt_eq _ _ (by omega)]
            exact List.pairwise_iff_getElem.mp sorted _ _ (by omega) (by omega) (by omega)
          have lt : (Rowl.Datatypes.numValue (cutAt cs (p - 1)).value : ℝ) <
              Rowl.Datatypes.numValue (cutAt cs p).value := by
            rcases before with lt | ⟨same, _, _⟩
            · exact_mod_cast lt
            · exact absurd same differ
          exact dense_region hl level lt (fun r lo hi => interval_between r lo hi)

/-- The integers of a bounded run that are no literal values. -/
theorem run_set {values : List datatypes.DataValue}
    (canonical : ∀ v ∈ values, Rowl.Datatypes.IsNumber v → Rowl.Datatypes.CanonicalNumeric v) {p : Nat}
    (pos : 0 < p) (inside : p < cs.length) :
    regionSet cs (literalReals values) p 0 =
      (fun z : ℤ => (z : ℝ)) '' (freeIntegers values (cutAt cs (p - 1)) (cutAt cs p) : Set ℤ) := by
  rw [← free_reals canonical]
  ext r
  simp only [regionSet, InInterval, AtLevel, RealIn, Set.mem_setOf_eq, pos, inside, true_implies]

end Sizes

/-! ### The OWL interpretation made from an interpretation of the encoding -/

section Model
variable {Object' : Type u} {Value' : Type x} {Native : Type w} {D : DatatypeMap Native}
  (context : data_ontology.Context) (J : Interpretation Object' Value') (N : Normative D) (order : List Usize)
  (atoms : List (DataProperty × Option DataRange × Nat)) (shift : Object' → ℕ)

/-- The value of a literal value. -/
noncomputable def litValue (val : datatypes.DataValue) : Values.{v,w} Native := embedValue (valueOf N val)

/-- The value of a real number. -/
noncomputable def realValue (r : ℝ) : Values.{v,w} Native := embedValue (N.real r)

/-- Some data nodes that witness an element's data restriction, when it has
    enough of them. -/
noncomputable def witnesses (z : Object') (atom : DataProperty × Option DataRange × Nat) : List Object' :=
  if h : ∃ f : Fin atom.2.2 → Object', Function.Injective f ∧ ∀ role filler,
      data_ontology.data_role context atom.1 = .ok (some role) →
      data_ontology.encode_optional_range context atom.2.1 = .ok (some filler) →
      ∀ i, objectRelation J role z (f i) ∧ Rowl.Concepts.FillerHolds J filler (f i)
  then List.ofFn (Classical.choose h)
  else []

/-- The data nodes that witness an element's data restrictions. -/
noncomputable def witnessList (z : Object') : List Object' := atoms.flatMap (witnesses context J z)

/-- A node along the role of a data property from an element. -/
def Successor (z e : Object') : Prop :=
  ∃ p role, data_ontology.data_role context p = .ok (some role) ∧ objectRelation J role z e

/-- The values of the literal values. -/
def literalValues : Set (Values.{v,w} Native) := {y | ∃ val ∈ context.values.val, y = litValue N val}

theorem literal_values_finite : (literalValues.{v,w} context N).Finite := by
  apply (context.values.val.finite_toSet.image (litValue.{v,w} N)).subset
  rintro y ⟨val, mem, rfl⟩
  exact ⟨val, mem, rfl⟩

/-- Where a region with a value for every index leaves the literal values
    behind. -/
noncomputable def regionStart (r : Region) : ℕ :=
  if h : RegionInfinite (orderedCuts context order) (literalReals context.values.val) r then
    Classical.choose (region_avoids.{v,w} N (literalValues.{v,w} context N) (literal_values_finite context N) r h)
  else 0

theorem region_start_spec (r : Region) (h : RegionInfinite (orderedCuts context order) (literalReals context.values.val) r) (n : ℕ)
    (beyond : regionStart.{v,w} context N order r ≤ n) :
    regionValue.{v,w} N (orderedCuts context order) (literalReals context.values.val) r n ∉ literalValues.{v,w} context N := by
  unfold regionStart at beyond
  rw [dif_pos h] at beyond
  exact Classical.choose_spec
    (region_avoids.{v,w} N (literalValues.{v,w} context N) (literal_values_finite context N) r h) n beyond

theorem region_start_finite (r : Region) (h : ¬ RegionInfinite (orderedCuts context order) (literalReals context.values.val) r) :
    regionStart.{v,w} context N order r = 0 := by
  unfold regionStart
  rw [dif_neg h]

/-- The value of a data node at an index: a literal value's own value, and
    otherwise its region's value at the index, after the literal values. -/
noncomputable def valueAt (d : Object') (n : ℕ) : Values.{v,w} Native :=
  if h : LiteralNode context J d then
    match context.values.val[(Classical.choose h).val]? with
    | some val => litValue N val
    | none => ULift.up (.inr 0)
  else
    regionValue N (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
      (regionStart.{v,w} context N order (regionOf context J order d) + n)

/-- The data nodes of an element that need values of their own in the region
    of `d`: its successors among its witnesses that are no literal values'
    individuals, each once. -/
noncomputable def peers (z d : Object') : List Object' :=
  ((witnessList context J atoms z).filter (fun e => decide (Successor context J z e ∧ ¬ LiteralNode context J e ∧
    regionOf context J order e = regionOf context J order d))).dedup

/-- The value of a data node for an element: its value at its place among
    its peers, after the element's shift. -/
noncomputable def nodeValue (z d : Object') : Values.{v,w} Native :=
  valueAt.{u,v,w,x} context J N order d (shift z + (peers context J order atoms z d).idxOf d)

/-- The data nodes that have values for an element: the literal values'
    individuals and its successors among its witnesses. -/
def ValuedNode (z d : Object') : Prop :=
  LiteralNode context J d ∨ (d ∈ witnessList context J atoms z ∧ Successor context J z d)

/-- An element's values at its data nodes. -/
def Place (z : Object') (y : Values.{v,w} Native) (d : Object') : Prop :=
  ValuedNode context J atoms z d ∧ nodeValue.{u,v,w,x} context J N order atoms shift z d = y

/-- The elements of the interpretation of the encoding that are no data nodes. -/
def Element : Type u := {y : Object' // ¬ J.classes dataClass y}

/-- The OWL interpretation made from an interpretation of the encoding. -/
noncomputable def sound (o : Element J) : Interpretation (Element J) (Values.{v,w} Native) where
  objectsNonempty := ⟨o⟩
  dataNonempty := ⟨ULift.up (.inr 0)⟩
  classes c z := J.classes c z.1
  objectProperties r z z' := J.objectProperties r z.1 z'.1
  dataProperties p z y := p = topData ∨ ∃ role, data_ontology.data_role context p = .ok (some role) ∧
    ∃ d, Place.{u,v,w,x} context J N order atoms shift z.1 y d ∧ objectRelation J role z.1 d
  namedIndividuals a := if h : ¬ J.classes dataClass (J.namedIndividuals a) then ⟨_, h⟩ else o
  anonymousIndividuals b := if h : ¬ J.classes dataClass (J.anonymousIndividuals b) then ⟨_, h⟩ else o
  datatypes dt y := dt = literalDatatype ∨ ∃ y0, D.valueSpace dt y0 ∧ embedValue y0 = y
  literals lt := embedValue (D.lexicalValue lt.datatype lt.lexical.val)
  facets f y := ∃ y0, D.facetValue f.facet (D.lexicalValue f.value.datatype f.value.lexical.val) y0 ∧
    embedValue y0 = y
  named := fun _ => True

end Model

/-! ### The values at the data nodes -/

section Values
variable {Object' : Type u} {Value' : Type x} {Native : Type w} {D : DatatypeMap Native}
  {context : data_ontology.Context} {J : Interpretation Object' Value'} {N : Normative D}
  {atoms : List (DataProperty × Option DataRange × Nat)} {capacity : Nat} {bits : Usize} {order : List Usize}
  {shift : Object' → ℕ}

/-- A shift of the indices of the elements' values that is none while numbers
    are ordered or floating-point numbers are in use, so that the bounded runs
    of integers and the floating-point numbers keep their room. -/
def ShiftOk (context : data_ontology.Context) (shift : Object' → ℕ) : Prop :=
  (context.kinds.ordered = true ∨ context.kinds.double = true ∨ context.kinds.float = true) → ∀ z, shift z = 0

theorem typeOf_not_literal (N : Normative D) (k : datatypes.Kind) : typeOf k ≠ literalDatatype := by
  intro same
  have := Rowl.Datatypes.normative_supported N k
  rw [same] at this
  exact D.excludesLiteral this

theorem litValue_injective (N : Normative D) (good : Good context) {a b : datatypes.DataValue}
    (ma : a ∈ context.values.val) (mb : b ∈ context.values.val)
    (same : litValue.{v,w} N a = litValue N b) : a = b :=
  Rowl.Datatypes.value_injective N (good.1.1 a ma) (good.1.1 b mb) (embedValue_injective same)

/-- A literal value that is no number is no real. -/
theorem real_ne_value (N : Normative D) {val : datatypes.DataValue} (canonical : Canonical val)
    (notNumber : ¬ Rowl.Datatypes.IsNumber val) (r : ℝ) : N.real r ≠ valueOf N val := by
  cases val with
  | Number _ _ _ => exact absurd trivial notNumber
  | Fraction _ _ _ => exact absurd trivial notNumber
  | Text t => exact N.real_text r _ canonical
  | Tagged t m => exact N.real_tagged r _ _ canonical.1 canonical.2
  | Truth b => exact N.real_truth r b
  | Uri t => exact N.real_coded r _ canonical
  | Hex o => exact N.real_coded r _ trivial
  | Base64 o => exact N.real_coded r _ trivial
  | Moment x => exact N.real_moment r _ (canonical : Rowl.Moments.CanonicalMoment x).2.2.2.2.2.2
  | Double x => exact N.real_double r _ canonical.2
  | Float x => exact N.real_float r _ canonical.2

theorem literal_value_at (setting : Setting context capacity bits order J) (i : Usize)
    (h : i.val < context.values.val.length) (n : ℕ) :
    valueAt.{u,v,w,x} context J N order (J.namedIndividuals (valueIndividual i)) n =
      litValue N context.values.val[i.val] := by
  have literal : LiteralNode context J (J.namedIndividuals (valueIndividual i)) := ⟨i, h, rfl⟩
  have chosen : Classical.choose literal = i := by
    by_contra differ
    have spec := Classical.choose_spec literal
    exact value_individuals_apart setting.frame setting.enough _ _ spec.1 h differ spec.2
  simp only [valueAt, dif_pos literal, chosen, List.getElem?_eq_getElem h]

theorem region_value_at (d : Object') (notLiteral : ¬ LiteralNode context J d) (n : ℕ) :
    valueAt.{u,v,w,x} context J N order d n = regionValue N (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
      (regionStart.{v,w} context N order (regionOf context J order d) + n) := by
  simp only [valueAt, dif_neg notLiteral]

theorem region_number {d : Object'} {p ℓ : Nat} (h : regionOf context J order d = .number p ℓ) :
    NumericNode context J d ∧ positionOf context J order d = p ∧ levelOf context J d = ℓ := by
  unfold regionOf at h
  split_ifs at h with numeric
  · cases h; exact ⟨numeric, rfl, rfl⟩

theorem region_numeric {d : Object'} (numeric : NumericNode context J d) :
    regionOf context J order d = .number (positionOf context J order d) (levelOf context J d) := by
  simp [regionOf, numeric]

theorem region_binary {d : Object'} {dbl : Bool} {A : Set DatatypeMap.Binary} {lo hi : ℕ}
    (h : regionOf context J order d = .binary dbl A lo hi) :
    InUse context J (floatKind dbl) d ∧ A = literalBinaries context.values.val dbl ∧
      lo = slotLow context J dbl d ∧ hi = slotHigh context J dbl d := by
  unfold regionOf at h
  split_ifs at h <;> simp only [reduceCtorEq, Region.binary.injEq] at h
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨by assumption, rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨by assumption, rfl, rfl, rfl⟩

/-- Two nodes whose slots of a format share a value have one region. -/
theorem binary_coherent {d d' : Object'} :
    ∀ dbl A lo hi A' lo' hi', regionOf context J order d = .binary dbl A lo hi →
      regionOf context J order d' = .binary dbl A' lo' hi' → ∀ b, b ∈ slotSet dbl A lo hi →
        b ∈ slotSet dbl A' lo' hi' → A = A' ∧ lo = lo' ∧ hi = hi' := by
  intro dbl A lo hi A' lo' hi' h h' b inS inS'
  obtain ⟨_, rfl, rfl, rfl⟩ := region_binary h
  obtain ⟨_, rfl, rfl, rfl⟩ := region_binary h'
  obtain ⟨low, high⟩ := place_in_slot inS.1
  obtain ⟨low', high'⟩ := place_in_slot inS'.1
  obtain ⟨_, sameLow, sameHigh⟩ := same_slot low high low' high'
  exact ⟨rfl, sameLow, sameHigh⟩

/-- A format in use puts floating-point numbers in use. -/
theorem float_used {dbl : Bool} {d : Object'} (h : InUse context J (floatKind dbl) d) :
    context.kinds.double = true ∨ context.kinds.float = true := by
  cases dbl
  · exact .inr (by simpa [Used, floatKind] using h.1)
  · exact .inl (by simpa [Used, floatKind] using h.1)

theorem level_zero {d : Object'} (zero : levelOf context J d = 0) : InUse context J .Integer d := by
  unfold levelOf at zero
  split_ifs at zero with h
  exact h

theorem not_boolean_region (setting : Setting context capacity bits order J) {d : Object'}
    (notLiteral : ¬ LiteralNode context J d) : ¬ InUse context J .Boolean d := by
  rintro ⟨used, holds⟩
  have used' : context.kinds.boolean = true := by simpa [Used] using used
  obtain ⟨i, h, _, same⟩ := setting.frame.kinds.truths used' d holds
  exact notLiteral ⟨i, h, same⟩

/-- A node that is no literal value's individual and whose region has no
    value for every index is an integer between two cuts of different
    numbers. -/
theorem finite_run (setting : Setting context capacity bits order J) {d : Object'}
    (notLiteral : ¬ LiteralNode context J d) (numeric : NumericNode context J d)
    (finite : ¬ RegionInfinite (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)) :
    context.kinds.ordered = true ∧ NumericNode context J d ∧ levelOf context J d = 0 ∧
      0 < positionOf context J order d ∧ positionOf context J order d < order.length := by
  · rw [region_numeric numeric] at finite
    have notInf : ¬ (regionSet (orderedCuts context order) (literalReals context.values.val) (positionOf context J order d)
        (levelOf context J d)).Infinite := fun h => finite ⟨level_le context J d, h⟩
    by_cases ordered : context.kinds.ordered = true
    · have len := cuts_length (context := context) (order := order) ordered
      rcases region_cases (cuts_sorted setting) (literal_reals_finite context.values.val)
          (position_le context J order d)
          (fun pos inside => not_point setting ordered notLiteral pos (by rw [← len]; exact inside)) with
        inf | ⟨l0, pos, inside⟩
      · exact absurd inf notInf
      · exact ⟨ordered, numeric, l0, pos, by rw [← len]; exact inside⟩
    · exfalso
      have empty := cuts_empty (context := context) (order := order) ordered
      rcases region_cases (cs := orderedCuts context order) (cuts_sorted setting)
          (literal_reals_finite context.values.val) (position_le context J order d)
          (fun _ inside => by rw [empty] at inside; simp at inside) with inf | ⟨_, _, inside⟩
      · exact notInf inf
      · rw [empty] at inside; simp at inside

/-- The region of a node that is no number: values for every index, or the
    values of a format in use in the node's slot, without the literal
    values. -/
theorem other_region {d : Object'} (numeric : ¬ NumericNode context J d) :
    RegionInfinite (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d) ∨
      ∃ dbl, regionOf context J order d = .binary dbl (literalBinaries context.values.val dbl)
        (slotLow context J dbl d) (slotHigh context J dbl d) ∧ InUse context J (floatKind dbl) d := by
  unfold regionOf
  simp only [numeric, ↓reduceIte]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact .inl trivial
  · exact .inl trivial
  · exact .inl trivial
  · exact .inl trivial
  · exact .inl trivial
  · exact .inl trivial
  · exact .inr ⟨true, rfl, h7⟩
  · exact .inr ⟨false, rfl, h8⟩
  · exact .inl trivial

/-- The cuts around a run, among the context's cuts. -/
theorem run_cuts (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    {p : Nat} (pos : 0 < p) (inside : p < order.length) :
    cutAt (orderedCuts context order) (p - 1) = cutAt context.cuts.val (order[p - 1]'(by omega)).val ∧
      cutAt (orderedCuts context order) p = cutAt context.cuts.val (order[p]'inside).val := by
  constructor
  · rw [cuts_at setting ordered (by omega : p - 1 < order.length),
      Rowl.Regions.cutAt_eq _ _ (order_in setting ordered _)]
  · rw [cuts_at setting ordered inside, Rowl.Regions.cutAt_eq _ _ (order_in setting ordered _)]

/-- The axiom on the integers between two neighbouring cuts of different
    numbers. -/
theorem run_gap (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    {p : Nat} (pos : 0 < p) (inside : p < order.length)
    (differ : (cutAt (orderedCuts context order) (p - 1)).value ≠ (cutAt (orderedCuts context order) p).value)
    (integer : Used context.kinds .Integer = true) :
    GapFact context capacity J (order[p - 1]'(by omega)) (order[p]'inside) := by
  obtain ⟨c1, c2⟩ := run_cuts setting ordered pos inside
  rw [c1, c2] at differ
  exact (((setting.frame.regions.1 ordered).2 p inside (by omega) pos).2).2 differ integer

/-- The integers of a bounded run that are no literal values, counted. -/
theorem run_count (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    {p : Nat} (pos : 0 < p) (inside : p < order.length) :
    (regionSet (orderedCuts context order) (literalReals context.values.val) p 0).ncard =
      freeCount context (order[p - 1]'(by omega)) (order[p]'inside) := by
  have len := cuts_length (context := context) (order := order) ordered
  have canonical : ∀ v ∈ context.values.val, Rowl.Datatypes.IsNumber v → Rowl.Datatypes.CanonicalNumeric v :=
    fun v m number => canonical_numeric (setting.good.1.1 v m) number
  rw [run_set canonical pos (by rw [len]; exact inside), Set.ncard_image_of_injective _ Int.cast_injective,
    Set.ncard_coe_finset, free_card setting.good.1.2 canonical, freeCount]
  obtain ⟨c1, c2⟩ := run_cuts setting ordered pos inside
  rw [c1, c2]

theorem run_member (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    {e : Object'} (level : levelOf context J e = 0) {p : Nat} (pos : 0 < p) (inside : p < order.length)
    (at_p : positionOf context J order e = p) :
    InRun J (order[p - 1]'(by omega)) (order[p]'inside) e := by
  refine ⟨(level_zero level).2, ?_, ?_⟩
  · exact (position_cut setting ordered e (by omega)).mpr (by omega)
  · intro h
    have := (position_cut setting ordered e inside).mp h
    omega

/-- Every successor of an element along a data property's role is one along
    `U`, when the encoding bounds the data nodes along it. -/
theorem successor_super (setting : Setting context capacity bits order J) (runs : BoundsRuns context.kinds)
    {z e : Object'} (succ : Successor context J z e) : J.objectProperties dataSuper z e := by
  obtain ⟨p, role, run, rel⟩ := succ
  obtain ⟨res, run', facts⟩ := data_role_correct context p
  rw [run] at run'
  cases Result.ok_injective run'
  rcases facts role rfl with ⟨_, rfl⟩ | ⟨_, inData, _, q, rfl, _⟩
  · exact absurd rel (setting.bottom z e)
  · obtain ⟨k, hk, at_k⟩ := List.getElem_of_mem inData
    exact setting.frame.regions.2 runs k hk (Nat.zero_le _) (.Property q) (by rw [at_k]; exact run) z e rel

/-- The sum of the counts of a list of data restrictions. -/
def atomCount (atoms : List (DataProperty × Option DataRange × Nat)) : Nat := (atoms.map (·.2.2)).sum

theorem witnesses_length (z : Object') (atom : DataProperty × Option DataRange × Nat) :
    (witnesses context J z atom).length ≤ atom.2.2 := by
  unfold witnesses
  split_ifs <;> simp

theorem witness_list_length (z : Object') : (witnessList context J atoms z).length ≤ atomCount atoms := by
  induction atoms with
  | nil => simp [witnessList, atomCount]
  | cons a rest ih =>
    have := witnesses_length (context := context) (J := J) z a
    simp only [witnessList, List.flatMap_cons, List.length_append, atomCount, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem mem_peers {z d e : Object'} : e ∈ peers context J order atoms z d ↔
    e ∈ witnessList context J atoms z ∧ Successor context J z e ∧ ¬ LiteralNode context J e ∧
      regionOf context J order e = regionOf context J order d := by
  simp [peers, List.mem_dedup, List.mem_filter]

theorem peers_length (z d : Object') :
    (peers context J order atoms z d).length ≤ (witnessList context J atoms z).length :=
  (List.dedup_sublist _).length_le.trans (List.filter_sublist).length_le

theorem atMost_length {α : Type u} {n : Nat} {P : α → Prop} (most : AtMost n P) {l : List α} (nodup : l.Nodup)
    (each : ∀ e ∈ l, P e) : l.length ≤ n := by
  by_contra more
  apply most
  refine ⟨fun i => l[i.val]'(by omega), fun i j same => ?_, fun i => each _ (List.getElem_mem _)⟩
  exact Fin.ext ((List.Nodup.getElem_inj_iff nodup).mp same)

/-- The peers of a node in a bounded run of integers fit in the run: by the
    axiom on the run when it has fewer integers than the capacity, and
    otherwise because the witnesses are at most the capacity. -/
theorem peers_bound (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    {z d : Object'} (notLiteral : ¬ LiteralNode context J d) (numericNode : NumericNode context J d)
    (finite : ¬ RegionInfinite (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)) :
    (peers context J order atoms z d).length ≤
      (regionSet (orderedCuts context order) (literalReals context.values.val) (positionOf context J order d) 0).ncard := by
  obtain ⟨ordered, numeric, level, pos, inside⟩ := finite_run setting notLiteral numericNode finite
  have integer : Used context.kinds .Integer = true := (level_zero level).1
  have differ := not_point setting ordered notLiteral pos inside
  have gap := run_gap setting ordered pos inside differ integer
  rw [run_count setting ordered pos inside]
  have inRun : ∀ e ∈ peers context J order atoms z d, J.objectProperties dataSuper z e ∧
      InRun J (order[positionOf context J order d - 1]'(by omega)) (order[positionOf context J order d]'inside) e ∧
      ¬ RunNamed context J (order[positionOf context J order d - 1]'(by omega))
        (order[positionOf context J order d]'inside) e := by
    intro e mem
    obtain ⟨_, succ, notLit, region⟩ := mem_peers.mp mem
    rw [region_numeric numeric, level] at region
    obtain ⟨_, at_p, level_e⟩ := region_number region
    exact ⟨successor_super setting (.inl ⟨ordered, by simpa [Used] using integer⟩) succ,
      run_member setting ordered level_e pos inside at_p,
      fun ⟨i, hi, _, same⟩ => notLit ⟨i, hi, same⟩⟩
  by_cases small : freeCount context (order[positionOf context J order d - 1]'(by omega))
      (order[positionOf context J order d]'inside) < capacity
  · by_cases zero : freeCount context (order[positionOf context J order d - 1]'(by omega))
        (order[positionOf context J order d]'inside) = 0
    · have empty : peers context J order atoms z d = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro e mem
        obtain ⟨_, inR, notNamed⟩ := inRun e mem
        exact notNamed (gap.1 zero e inR)
      rw [empty]
      simp
    · exact atMost_length (gap.2 (by omega) small z (setting.thing z)) (List.nodup_dedup _) inRun
  · have := peers_length (context := context) (J := J) (order := order) (atoms := atoms) z d
    have := witness_list_length (context := context) (J := J) (atoms := atoms) z
    omega

/-- The axiom on a slot depends on its places only as the kernel clamps
    them. -/
theorem slot_fact_congr {S : Object' → Prop} {dbl : Bool} {lo hi lo' hi' : ℕ} (l : clamp dbl lo = clamp dbl lo')
    (h : clamp dbl hi = clamp dbl hi') (fact : SlotFact context capacity J dbl S lo hi) :
    SlotFact context capacity J dbl S lo' hi' := by
  have free : slotFree context dbl lo hi = slotFree context dbl lo' hi' := by
    simp only [slotFree, l, h]
  unfold SlotFact at fact ⊢
  rw [← free, ← l, ← h]
  exact fact

/-- A node of a format in use is in the class of its slot, between edges of
    the format, and the axiom on that slot holds. -/
theorem node_slot (setting : Setting context capacity bits order J) {dbl : Bool} {d : Object'}
    (inUse : InUse context J (floatKind dbl) d) :
    ∃ low high, (∀ i, low = some i → i.val < (edgesOf context dbl).val.length) ∧
      (∀ j, high = some j → j.val < (edgesOf context dbl).val.length) ∧ InSlotClass J dbl low high d ∧
      SlotFact context capacity J dbl (InSlotClass J dbl low high) (slotLow context J dbl d)
        (slotHigh context J dbl d) := by
  obtain ⟨noEdges, each⟩ := setting.frame.edges dbl inUse.1
  have split : ∀ (k : Usize) (hk : k.val < (edgesOf context dbl).val.length),
      ((edgesOf context dbl).val[k.val]'hk).val ∈ HeldEdges context J dbl d ∨
        ((edgesOf context dbl).val[k.val]'hk).val ∈ FailedEdges context J dbl d := by
    intro k hk
    by_cases holds : J.classes (edgeClass dbl k) d
    · exact .inl ⟨k, hk, rfl, holds⟩
    · exact .inr ⟨k, hk, rfl, holds⟩
  have indexed : ∀ e ∈ (edgesOf context dbl).val, ∃ (k : Usize) (hk : k.val < (edgesOf context dbl).val.length),
      (edgesOf context dbl).val[k.val]'hk = e := by
    intro e mem
    obtain ⟨j, hj, at_j⟩ := List.getElem_of_mem mem
    obtain ⟨k, rfl⟩ := usize_of_index (edgesOf context dbl) j hj
    exact ⟨k, hj, at_j⟩
  by_cases someHeld : (HeldEdges context J dbl d).Nonempty
  · obtain ⟨i, hi, lowIs, heldI⟩ := slot_low_edge someHeld
    by_cases someFailed : (FailedEdges context J dbl d).Nonempty
    · obtain ⟨⟨j, hj, highIs, failedJ⟩, clampIs⟩ := slot_high_edge someFailed
      have pair := (each i).1 j hi hj
      simp only [Rowl.DataEdges.edgeAt] at pair
      have lt : ((edgesOf context dbl).val[i.val]'hi).val < ((edgesOf context dbl).val[j.val]'hj).val := by
        by_contra ge
        have ne : i ≠ j := fun e => by subst e; exact failedJ heldI
        exact failedJ (pair.1 ne (by omega) d heldI)
      have between : ∀ e ∈ (edgesOf context dbl).val, ¬ (((edgesOf context dbl).val[i.val]'hi).val < e.val ∧
          e.val < ((edgesOf context dbl).val[j.val]'hj).val) := by
        rintro e mem ⟨l, u⟩
        obtain ⟨k, hk, rfl⟩ := indexed e mem
        rcases split k hk with held | failed
        · have := held_le held
          omega
        · have := Nat.sInf_le failed
          omega
      refine ⟨some i, some j, (fun i' e => by cases e; exact hi), (fun j' e => by cases e; exact hj),
        ⟨inUse.2, (fun i' e => by cases e; exact heldI), (fun j' e => by cases e; exact failedJ)⟩, slot_fact_congr (by rw [lowIs]) (by rw [highIs]; exact clampIs) (pair.2 lt between)⟩
    · have empty := Set.not_nonempty_iff_eq_empty.mp someFailed
      have top : ∀ e ∈ (edgesOf context dbl).val, ¬ ((edgesOf context dbl).val[i.val]'hi).val < e.val := by
        intro e mem
        obtain ⟨k, hk, rfl⟩ := indexed e mem
        rcases split k hk with held | failed
        · have := held_le held
          omega
        · rw [empty] at failed; exact failed.elim
      refine ⟨some i, none, (fun i' e => by cases e; exact hi), (fun j' e => by cases e),
        ⟨inUse.2, (fun i' e => by cases e; exact heldI), (fun j' e => by cases e)⟩, ?_⟩
      have fact := (each i).2.2 hi top
      simp only [Rowl.DataEdges.edgeAt] at fact
      exact slot_fact_congr (by rw [lowIs]) (by rw [slot_high_empty empty]) fact
  · have heldEmpty := Set.not_nonempty_iff_eq_empty.mp someHeld
    by_cases someFailed : (FailedEdges context J dbl d).Nonempty
    · obtain ⟨⟨j, hj, highIs, failedJ⟩, clampIs⟩ := slot_high_edge someFailed
      have bottom : ∀ e ∈ (edgesOf context dbl).val, ¬ e.val < ((edgesOf context dbl).val[j.val]'hj).val := by
        intro e mem
        obtain ⟨k, hk, rfl⟩ := indexed e mem
        rcases split k hk with held | failed
        · rw [heldEmpty] at held; exact held.elim
        · have := Nat.sInf_le failed
          omega
      refine ⟨none, some j, (fun i' e => by cases e), (fun j' e => by cases e; exact hj),
        ⟨inUse.2, (fun i' e => by cases e), (fun j' e => by cases e; exact failedJ)⟩, ?_⟩
      have fact := ((each j).2.1 hj bottom).2
      simp only [Rowl.DataEdges.edgeAt] at fact
      exact slot_fact_congr (by rw [slot_low_empty heldEmpty]) (by rw [highIs]; exact clampIs) fact
    · have failedEmpty := Set.not_nonempty_iff_eq_empty.mp someFailed
      have noEdge : (edgesOf context dbl).val = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro e mem
        obtain ⟨k, hk, rfl⟩ := indexed e mem
        rcases split k hk with held | failed
        · rw [heldEmpty] at held; exact held
        · rw [failedEmpty] at failed; exact failed
      refine ⟨none, none, (fun i' e => by cases e), (fun j' e => by cases e),
        ⟨inUse.2, (fun i' e => by cases e), (fun j' e => by cases e)⟩, ?_⟩
      exact slot_fact_congr (by rw [slot_low_empty heldEmpty]) (by rw [slot_high_empty failedEmpty]) (noEdges noEdge)

/-- The values of the slot of a node of a format that are no literal values
    are counted by the kernel's count of its slot. -/
theorem slot_set_card (setting : Setting context capacity bits order J) (dbl : Bool) (lo hi : ℕ) :
    (slotSet dbl (literalBinaries context.values.val dbl) lo hi).ncard = slotFree context dbl lo hi :=
  Rowl.DataEdges.slot_free_card setting.good dbl lo hi

/-- A node of a format in use that is no literal value's individual has values
    of its own in its slot. -/
theorem slot_free_pos (setting : Setting context capacity bits order J) {dbl : Bool} {d : Object'}
    (notLiteral : ¬ LiteralNode context J d) (inUse : InUse context J (floatKind dbl) d) :
    0 < slotFree context dbl (slotLow context J dbl d) (slotHigh context J dbl d) := by
  obtain ⟨low, high, _, _, inSlot, fact⟩ := node_slot setting inUse
  by_contra zero
  obtain ⟨i, hi, _, same⟩ := fact.1 (by omega) d inSlot
  exact notLiteral ⟨i, hi, same⟩

/-- The peers of a node of a format fit in its slot: by the axiom on the slot
    when it has fewer values than the capacity, and otherwise because the
    witnesses are at most the capacity. -/
theorem binary_peers_bound (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    {z d : Object'} {dbl : Bool} (notLiteral : ¬ LiteralNode context J d)
    (inUse : InUse context J (floatKind dbl) d)
    (region : regionOf context J order d = .binary dbl (literalBinaries context.values.val dbl)
      (slotLow context J dbl d) (slotHigh context J dbl d)) :
    (peers context J order atoms z d).length ≤
      slotFree context dbl (slotLow context J dbl d) (slotHigh context J dbl d) := by
  obtain ⟨low, high, lowIn, highIn, inSlot, fact⟩ := node_slot setting inUse
  have pos := slot_free_pos setting notLiteral inUse
  by_cases small : slotFree context dbl (slotLow context J dbl d) (slotHigh context J dbl d) < capacity
  · have nonempty : (slotSet dbl (literalBinaries context.values.val dbl) (slotLow context J dbl d)
        (slotHigh context J dbl d)).Nonempty := by
      rw [← Set.ncard_pos (slotSet_finite _ _ _ _), slot_set_card setting]
      exact pos
    obtain ⟨b, inS, _⟩ := nonempty
    obtain ⟨low', high'⟩ := place_in_slot inS
    have each : ∀ e ∈ peers context J order atoms z d, J.objectProperties dataSuper z e ∧
        InSlotClass J dbl low high e ∧ ¬ SlotNamed context J dbl (clamp dbl (slotLow context J dbl d))
          (clamp dbl (slotHigh context J dbl d)) e := by
      intro e mem
      obtain ⟨_, succ, notLit, regionE⟩ := mem_peers.mp mem
      rw [region] at regionE
      obtain ⟨inUseE, _, lowE, highE⟩ := region_binary regionE
      refine ⟨successor_super setting (.inr (float_used inUse)) succ, ?_,
        fun ⟨i, hi, _, same⟩ => notLit ⟨i, hi, same⟩⟩
      have lowE' : slotLow context J dbl e ≤ position (Rowl.Floats.fmt dbl) b := by rw [← lowE]; exact low'
      have highE' : position (Rowl.Floats.fmt dbl) b < slotHigh context J dbl e := by rw [← highE]; exact high'
      obtain ⟨kind, lows, highs⟩ := inSlot
      refine ⟨inUseE.2, fun i hi => ?_, fun j hj holds => ?_⟩
      · exact (edge_at_place lowE' highE' i (lowIn i hi)).mpr ((edge_at_place low' high' i (lowIn i hi)).mp (lows i hi))
      · exact highs j hj ((edge_at_place low' high' j (highIn j hj)).mpr
          ((edge_at_place lowE' highE' j (highIn j hj)).mp holds))
    exact atMost_length (fact.2 pos small z (setting.thing z)) (List.nodup_dedup _) each
  · have := peers_length (context := context) (J := J) (order := order) (atoms := atoms) z d
    have := witness_list_length (context := context) (J := J) (atoms := atoms) z
    omega

/-- The index of the value of a node that is placed for an element is one its
    region has a value for. -/
theorem placed_valid (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    (shiftOk : ShiftOk context shift) {z d : Object'} (notLiteral : ¬ LiteralNode context J d)
    (inList : d ∈ witnessList context J atoms z) (succ : Successor context J z d) :
    Valid (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
      (regionStart.{v,w} context N order (regionOf context J order d) +
        (shift z + (peers context J order atoms z d).idxOf d)) := by
  by_cases infinite : RegionInfinite (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
  · exact valid_of_infinite infinite _
  · rw [region_start_finite context N order _ infinite, zero_add]
    have mem : d ∈ peers context J order atoms z d := mem_peers.mpr ⟨inList, succ, notLiteral, rfl⟩
    have idx := List.idxOf_lt_length_of_mem mem
    by_cases numericNode : NumericNode context J d
    · obtain ⟨ordered, numeric, level, _, _⟩ := finite_run setting notLiteral numericNode infinite
      rw [shiftOk (.inl ordered) z, zero_add]
      have bound := peers_bound setting count notLiteral numericNode infinite (z := z)
      rw [region_numeric numeric, level]
      exact ⟨Nat.zero_le _, .inr (lt_of_lt_of_le idx bound)⟩
    · rcases other_region (context := context) (J := J) (order := order) numericNode with inf | ⟨dbl, region, inUse⟩
      · exact absurd inf infinite
      · have bound := binary_peers_bound setting count notLiteral inUse region (z := z)
        rw [shiftOk (.inr (float_used inUse)) z, zero_add, region]
        show _ < _
        rw [slot_set_card setting]
        omega

/-- The first index of a node's region is one it has a value for. -/
theorem alone_valid (setting : Setting context capacity bits order J) {d : Object'}
    (notLiteral : ¬ LiteralNode context J d) :
    Valid (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
      (regionStart.{v,w} context N order (regionOf context J order d) + 0) := by
  by_cases infinite : RegionInfinite (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
  · exact valid_of_infinite infinite _
  · rw [region_start_finite context N order _ infinite, zero_add]
    by_cases numericNode : NumericNode context J d
    swap
    · rcases other_region (context := context) (J := J) (order := order) numericNode with inf | ⟨dbl, region, inUse⟩
      · exact absurd inf infinite
      · rw [region]
        show 0 < _
        rw [slot_set_card setting]
        exact slot_free_pos setting notLiteral inUse
    obtain ⟨ordered, numeric, level, pos, inside⟩ := finite_run setting notLiteral numericNode infinite
    have integer : Used context.kinds .Integer = true := (level_zero level).1
    have gap := run_gap setting ordered pos inside (not_point setting ordered notLiteral pos inside) integer
    have member := run_member setting ordered level pos inside rfl
    rw [region_numeric numeric, level]
    refine ⟨Nat.zero_le _, .inr ?_⟩
    rw [run_count setting ordered pos inside]
    by_contra zero
    obtain ⟨i, hi, _, same⟩ := gap.1 (by omega) d member
    exact notLiteral ⟨i, hi, same⟩

/-- A value of a format that is a literal value's value is among the values
    of the literal values of the format. -/
theorem format_literal (N : Normative D) {values : List datatypes.DataValue} {val : datatypes.DataValue}
    (member : val ∈ values) (canonical : Canonical val) (dbl : Bool) {b : DatatypeMap.Binary}
    (vb : b.Valid (Rowl.Floats.fmt dbl)) (same : formatValue N dbl b = valueOf N val) :
    b ∈ literalBinaries values dbl := by
  cases val with
  | Number n' w f =>
    simp only [valueOf, Rowl.Datatypes.real_rat] at same
    exact absurd same.symm (real_format N _ dbl vb)
  | Fraction n' a c =>
    simp only [valueOf, Rowl.Datatypes.real_rat] at same
    exact absurd same.symm (real_format N _ dbl vb)
  | Text t => exact absurd same.symm (text_format N _ canonical dbl vb)
  | Tagged t m => exact absurd same.symm (tagged_format N _ _ canonical.1 canonical.2 dbl vb)
  | Truth x =>
    cases dbl
    · exact absurd same.symm (N.truth_float x _ vb)
    · exact absurd same.symm (N.truth_double x _ vb)
  | Uri t => exact absurd same.symm (coded_format N (.uri t.val) canonical dbl vb)
  | Hex o => exact absurd same.symm (coded_format N (.hex o.val) trivial dbl vb)
  | Base64 o => exact absurd same.symm (coded_format N (.base64 o.val) trivial dbl vb)
  | Moment x =>
    exact absurd same.symm (moment_format N _ (canonical : Rowl.Moments.CanonicalMoment x).2.2.2.2.2.2 dbl vb)
  | Double x =>
    cases dbl
    · exact absurd same (fun e => N.double_float _ _ canonical.2 vb e.symm)
    · exact ⟨x, member, (N.double_injective _ _ vb canonical.2 same).symm⟩
  | Float x =>
    cases dbl
    · exact ⟨x, member, (N.float_injective _ _ vb canonical.2 same).symm⟩
    · exact absurd same (N.double_float _ _ vb canonical.2)

/-- The values of a node that is no literal value's individual are no
    literal values: a number region leaves the numbers of the literal values
    out, and the other regions start past the literal values. -/
theorem region_not_literal (setting : Setting context capacity bits order J) {d : Object'}
    (notLiteral : ¬ LiteralNode context J d) {n : ℕ}
    (valid : Valid (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
      (regionStart.{v,w} context N order (regionOf context J order d) + n))
    {val : datatypes.DataValue} (member : val ∈ context.values.val) :
    valueAt.{u,v,w,x} context J N order d n ≠ litValue N val := by
  rw [region_value_at d notLiteral]
  by_cases numeric : NumericNode context J d
  · rw [region_numeric numeric] at valid ⊢
    intro same
    simp only [regionValue, litValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
    have mem := enumerate_mem _ _ valid.2
    by_cases number : Rowl.Datatypes.IsNumber val
    · rw [Rowl.Datatypes.valueOf_number N number] at same
      exact mem.2.2 ⟨val, member, number, N.real_injective same⟩
    · exact real_ne_value N (setting.good.1.1 val member) number _ same
  · rcases other_region (context := context) (J := J) (order := order) numeric with infinite | ⟨dbl, region, inUse⟩
    · intro same
      exact region_start_spec context N order _ infinite _ (Nat.le_add_right _ _) ⟨val, member, same⟩
    · have finite : ¬ RegionInfinite (orderedCuts context order) (literalReals context.values.val)
          (regionOf context J order d) := by rw [region]; exact id
      rw [region_start_finite context N order _ finite, zero_add, region] at valid
      rw [region_start_finite context N order _ finite, zero_add, region]
      intro same
      simp only [regionValue, litValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact (binaryAt_mem valid).2
        (format_literal N member (setting.good.1.1 val member) dbl (binaryAt_valid _ _ _ _ _) same)

/-- Whether a real of an interval is in a cut: exactly for the cuts before the
    interval. -/
theorem interval_cut {cs : List regions.Cut} (sorted : cs.Pairwise CutBefore) {p : Nat} (hp : p ≤ cs.length)
    {r : ℝ} (inside : InInterval cs p r) {k : Nat} (hk : k < cs.length) : InCut (cutAt cs k) r ↔ k < p := by
  constructor
  · intro inK
    by_contra ge
    have pl : p < cs.length := by omega
    apply inside.2 pl
    rcases Nat.lt_or_eq_of_le (show p ≤ k by omega) with lt | eq
    · have before : CutBefore (cutAt cs p) (cutAt cs k) := by
        rw [Rowl.Regions.cutAt_eq _ _ pl, Rowl.Regions.cutAt_eq _ _ hk]
        exact List.pairwise_iff_getElem.mp sorted _ _ pl hk lt
      exact Rowl.Regions.in_cut_mono before r inK
    · rw [eq]; exact inK
  · intro lt
    have low := inside.1 (by omega)
    rcases Nat.lt_or_eq_of_le (show k ≤ p - 1 by omega) with lt' | eq
    · have before : CutBefore (cutAt cs k) (cutAt cs (p - 1)) := by
        rw [Rowl.Regions.cutAt_eq _ _ hk, Rowl.Regions.cutAt_eq _ _ (by omega)]
        exact List.pairwise_iff_getElem.mp sorted _ _ hk (by omega) lt'
      exact Rowl.Regions.in_cut_mono before r low
    · rw [eq]; exact low

theorem sound_types (N : Normative D) (o : Element J) (k : datatypes.Kind) (y : Values.{v,w} Native) :
    (sound.{u,v,w,x} context J N order atoms shift o).datatypes (typeOf k) y ↔
      ∃ y0, D.valueSpace (typeOf k) y0 ∧ embedValue y0 = y := by
  simp only [sound, typeOf_not_literal N k, false_or]

theorem realValue_injective (N : Normative D) : Function.Injective (realValue.{v,w} N) := fun _ _ same =>
  N.real_injective (embedValue_injective same)

/-- A data node's value at an index its region has a value for stands for
    it. -/
theorem value_node (setting : Setting context capacity bits order J) (o : Element J) {d : Object'} {n : ℕ}
    (valid : ¬ LiteralNode context J d → Valid (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
      (regionStart.{v,w} context N order (regionOf context J order d) + n)) :
    NodeValue context (sound.{u,v,w,x} context J N order atoms shift o) J (litValue N) (realValue N) d
      (valueAt.{u,v,w,x} context J N order d n) where
  kinds := fun k used => by
    rw [sound_types]
    by_cases ld : LiteralNode context J d
    · obtain ⟨i, hi, rfl⟩ := ld
      rw [literal_value_at setting i hi n, (setting.frame.values i hi).2.1 k used,
        Rowl.Datatypes.normative_in_kind N (setting.good.1.1 _ (List.getElem_mem hi)) k]
      exact ⟨fun inSpace => ⟨_, inSpace, rfl⟩, fun ⟨y0, inSpace, same⟩ => embedValue_injective same ▸ inSpace⟩
    · have v := valid ld
      rw [region_value_at d ld, region_space N]
      by_cases numeric : NumericNode context J d
      · rw [region_numeric numeric] at v ⊢
        exact number_profile setting.frame.kinds numeric (enumerate_mem _ _ v.2).2.1 k used
      · exact text_profile order setting.frame.kinds numeric (not_boolean_region setting ld) _ _ _ k used
  values := fun i h => by
    by_cases ld : LiteralNode context J d
    · obtain ⟨i0, h0, rfl⟩ := ld
      rw [literal_value_at setting i0 h0 n]
      constructor
      · intro same
        by_cases differ : i = i0
        · subst differ; rfl
        · exact absurd same (value_individuals_apart setting.frame setting.enough i i0 h h0 differ)
      · intro same
        have values := litValue_injective N setting.good (List.getElem_mem h0) (List.getElem_mem h) same
        rw [value_index_unique (hi := h0) (hj := h) setting.good values]
    · constructor
      · intro same
        exact absurd ⟨i, h, same⟩ ld
      · intro same
        exact absurd same (region_not_literal setting ld (valid ld) (List.getElem_mem h))
  cuts := fun ordered i h => by
    obtain ⟨k, hk, at_k⟩ := cut_place setting ordered i.val h
    have ik : order[k] = i := UScalar.eq_of_val_eq at_k
    subst ik
    have len := cuts_length (context := context) (order := order) ordered
    have cutIs := cuts_at setting ordered hk
    by_cases ld : LiteralNode context J d
    · obtain ⟨i0, h0, rfl⟩ := ld
      rw [literal_value_at setting i0 h0 n]
      by_cases number : Rowl.Datatypes.IsNumber context.values.val[i0.val]
      · rw [literal_cut setting ordered h0 number hk, cutIs]
        have litIs : litValue.{v,w} N context.values.val[i0.val] =
            realValue N (Rowl.Datatypes.numValue context.values.val[i0.val]) := by
          simp only [litValue, realValue, Rowl.Datatypes.valueOf_number N number]
        rw [litIs]
        constructor
        · intro inCut
          exact ⟨_, rfl, inCut⟩
        · rintro ⟨r, same, inCut⟩
          rw [realValue_injective N same]
          exact inCut
      · constructor
        · intro inK
          exact absurd inK (literal_no_cut setting ordered h0 number hk)
        · rintro ⟨r, same, _⟩
          simp only [litValue, realValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
          exact absurd same.symm (real_ne_value N (setting.good.1.1 _ (List.getElem_mem h0)) number r)
    · have v := valid ld
      rw [region_value_at d ld]
      by_cases numeric : NumericNode context J d
      · rw [region_numeric numeric] at v ⊢
        have mem := enumerate_mem _ _ v.2
        rw [position_cut setting ordered d hk]
        simp only [regionValue]
        have hk' : k < (orderedCuts context order).length := by rw [len]; exact hk
        rw [← interval_cut (cuts_sorted setting) (position_le context J order d) mem.1 hk', cutIs]
        constructor
        · intro inCut
          exact ⟨_, rfl, inCut⟩
        · rintro ⟨r, same, inCut⟩
          rw [← realValue_injective N same] at inCut
          exact inCut
      · constructor
        · intro inK
          exact absurd (Or.inr (Or.inr (Or.inr ⟨real_used setting ordered, cut_real setting ordered hk inK⟩)))
            numeric
        · rintro ⟨r, same, _⟩
          unfold regionOf at same
          simp only [numeric, ↓reduceIte] at same
          split_ifs at same <;> simp only [regionValue, realValue, embedValue, ULift.up.injEq, Sum.inl.injEq,
            reduceCtorEq] at same
          · exact absurd same.symm (N.real_text r _ (Rowl.Strings.stringAt_xml (stringLevel context J d).isLt _))
          · exact absurd same.symm (N.real_tagged r _ _ (aText_xml _) enTag_value)
          all_goals first
            | exact absurd same.symm (N.real_coded r _ (sequence_valid _ _))
            | exact absurd same.symm (N.real_moment r _ (momentAt_valid _ _))
            | exact absurd same.symm (real_format N r _ (binaryAt_valid _ _ _ _ _))
  edges := fun double b hb e he => by
    obtain ⟨cb, vb, same⟩ := hb
    by_cases ld : LiteralNode context J d
    · obtain ⟨i0, h0, rfl⟩ := ld
      rw [literal_value_at setting i0 h0 n] at same
      have values : context.values.val[i0.val] = floatLit double b :=
        Rowl.Datatypes.value_injective N (setting.good.1.1 _ (List.getElem_mem h0))
          (Rowl.DataComplete.canonical_float_lit cb vb) (embedValue_injective same)
      have edgeFact := (setting.frame.values i0 h0).2.2.2.2 double
      rw [values, Rowl.DataEdges.format_place_lit] at edgeFact
      exact edgeFact _ rfl e he
    · have v := valid ld
      rw [region_value_at d ld] at same
      have inKind : RegionIn (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
          (regionStart.{v,w} context N order (regionOf context J order d) + n) (floatKind double) := by
        rw [← region_space N, same]
        exact ⟨_, (Rowl.DataComplete.float_space N double _).mpr ⟨_, vb, Rowl.DataComplete.lit_float N double b⟩,
          rfl⟩
      cases hr : regionOf context J order d with
      | binary dbl A lo hi =>
        rw [hr] at inKind same v
        have dd : double = dbl := by
          cases double <;> cases dbl <;> simp_all [RegionIn, floatKind, formatKind]
        subst dd
        obtain ⟨_, rfl, rfl, rfl⟩ := region_binary hr
        have finite : ¬ RegionInfinite (orderedCuts context order) (literalReals context.values.val)
            (.binary double (literalBinaries context.values.val double) (slotLow context J double d)
              (slotHigh context J double d)) := id
        rw [region_start_finite context N order _ finite, zero_add] at same v
        simp only [regionValue, litValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
        rw [Rowl.DataComplete.lit_float, ← format_value_eq] at same
        have values := (format_injective N (binaryAt_valid _ _ _ _ _) vb same).2
        obtain ⟨low, high⟩ := place_in_slot (binaryAt_mem v).1
        rw [values] at low high
        exact edge_at_place low high e he
      | number p ℓ =>
        rw [hr] at inKind
        cases double <;> simp [RegionIn, floatKind, Rowl.Datatypes.IsNumeric] at inKind
      | string ℓ =>
        rw [hr] at inKind
        cases double <;> simp [RegionIn, floatKind, Rowl.Strings.TextIn, Rowl.Strings.subtypeOf] at inKind
      | tagged =>
        rw [hr] at inKind
        cases double <;> simp [RegionIn, floatKind] at inKind
      | coded s' =>
        rw [hr] at inKind
        cases double <;> cases s' <;> simp [RegionIn, floatKind, sequenceKind] at inKind
      | moment st =>
        rw [hr] at inKind
        cases double <;> simp [RegionIn, floatKind] at inKind
      | other =>
        rw [hr] at inKind
        exact inKind.elim

theorem peers_same {z d d' : Object'} (same : regionOf context J order d = regionOf context J order d') :
    peers context J order atoms z d = peers context J order atoms z d' := by
  simp only [peers, same]

/-- Distinct data nodes that have values for an element have distinct
    values. -/
theorem nodeValue_injective (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    (shiftOk : ShiftOk context shift) (z : Object') {d d' : Object'} (hd : ValuedNode context J atoms z d) (hd' : ValuedNode context J atoms z d')
    (same : nodeValue.{u,v,w,x} context J N order atoms shift z d = nodeValue context J N order atoms shift z d') : d = d' := by
  unfold nodeValue at same
  by_cases ld : LiteralNode context J d
  · obtain ⟨i, hi, rfl⟩ := ld
    rw [literal_value_at setting i hi] at same
    by_cases ld' : LiteralNode context J d'
    · obtain ⟨i', hi', rfl⟩ := ld'
      rw [literal_value_at setting i' hi'] at same
      have values := litValue_injective N setting.good (List.getElem_mem hi) (List.getElem_mem hi') same
      rw [value_index_unique (hi := hi) (hj := hi') setting.good values]
    · have placed := hd'.resolve_left ld'
      exact absurd same.symm (region_not_literal setting ld' (placed_valid setting count shiftOk ld' placed.1 placed.2)
        (List.getElem_mem hi))
  · have placed := hd.resolve_left ld
    have valid := placed_valid (N := N) setting count shiftOk ld placed.1 placed.2
    by_cases ld' : LiteralNode context J d'
    · obtain ⟨i', hi', rfl⟩ := ld'
      rw [literal_value_at setting i' hi'] at same
      exact absurd same (region_not_literal setting ld valid (List.getElem_mem hi'))
    · have placed' := hd'.resolve_left ld'
      have valid' := placed_valid (N := N) setting count shiftOk ld' placed'.1 placed'.2
      rw [region_value_at d ld, region_value_at d' ld'] at same
      have len := position_le context J order
      obtain ⟨sameRegion, sameIndex⟩ := region_value_injective N (cuts_sorted setting) valid valid'
        (fun p ℓ h => by obtain ⟨_, rfl, _⟩ := region_number h; exact len d)
        (fun p ℓ h => by obtain ⟨_, rfl, _⟩ := region_number h; exact len d')
        binary_coherent same
      rw [sameRegion] at sameIndex
      rw [peers_same sameRegion] at sameIndex
      have index : (peers context J order atoms z d').idxOf d = (peers context J order atoms z d').idxOf d' := by
        omega
      have mem : d ∈ peers context J order atoms z d' :=
        mem_peers.mpr ⟨placed.1, placed.2, ld, sameRegion⟩
      exact (List.idxOf_inj mem).mp index

/-- The place of a node among an element's peers is below the count of the
    data restrictions. -/
theorem peers_index (z d : Object') : (peers context J order atoms z d).idxOf d ≤ atomCount atoms := by
  have := List.idxOf_le_length (a := d) (l := peers context J order atoms z d)
  have := peers_length (context := context) (J := J) (order := order) (atoms := atoms) z d
  have := witness_list_length (context := context) (J := J) (atoms := atoms) z
  omega

/-- Two elements whose shifted places of two data nodes differ have one value
    at the two nodes only when the nodes are one: a literal value's own value,
    or a region's value at one index. -/
theorem nodeValue_shared (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    (shiftOk : ShiftOk context shift) {z z' d d' : Object'} (hd : ValuedNode context J atoms z d)
    (hd' : ValuedNode context J atoms z' d')
    (distinct : shift z + (peers context J order atoms z d).idxOf d ≠
      shift z' + (peers context J order atoms z' d').idxOf d')
    (same : nodeValue.{u,v,w,x} context J N order atoms shift z d = nodeValue context J N order atoms shift z' d') :
    d = d' := by
  unfold nodeValue at same
  by_cases ld : LiteralNode context J d
  · obtain ⟨i, hi, rfl⟩ := ld
    rw [literal_value_at setting i hi] at same
    by_cases ld' : LiteralNode context J d'
    · obtain ⟨i', hi', rfl⟩ := ld'
      rw [literal_value_at setting i' hi'] at same
      have values := litValue_injective N setting.good (List.getElem_mem hi) (List.getElem_mem hi') same
      rw [value_index_unique (hi := hi) (hj := hi') setting.good values]
    · have placed := hd'.resolve_left ld'
      exact absurd same.symm (region_not_literal setting ld' (placed_valid setting count shiftOk ld' placed.1 placed.2)
        (List.getElem_mem hi))
  · have placed := hd.resolve_left ld
    have valid := placed_valid (N := N) setting count shiftOk ld placed.1 placed.2
    by_cases ld' : LiteralNode context J d'
    · obtain ⟨i', hi', rfl⟩ := ld'
      rw [literal_value_at setting i' hi'] at same
      exact absurd same (region_not_literal setting ld valid (List.getElem_mem hi'))
    · have placed' := hd'.resolve_left ld'
      have valid' := placed_valid (N := N) setting count shiftOk ld' placed'.1 placed'.2
      rw [region_value_at d ld, region_value_at d' ld'] at same
      have len := position_le context J order
      obtain ⟨sameRegion, sameIndex⟩ := region_value_injective N (cuts_sorted setting) valid valid'
        (fun p ℓ h => by obtain ⟨_, rfl, _⟩ := region_number h; exact len d)
        (fun p ℓ h => by obtain ⟨_, rfl, _⟩ := region_number h; exact len d')
        binary_coherent same
      rw [sameRegion] at sameIndex
      exact absurd (by omega) distinct

/-- Each data node an element has a value at stands for it. -/
theorem place_node (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    (shiftOk : ShiftOk context shift) (o : Element J) {z d : Object'} (placed : ValuedNode context J atoms z d) :
    NodeValue context (sound.{u,v,w,x} context J N order atoms shift o) J (litValue N) (realValue N) d
      (nodeValue.{u,v,w,x} context J N order atoms shift z d) :=
  value_node setting o (fun ld => placed_valid setting count shiftOk ld (placed.resolve_left ld).1
    (placed.resolve_left ld).2)

end Values

/-! ### The correspondence -/

section Correspondence
variable {Object' : Type u} {Value' : Type x} {Native : Type w} {D : DatatypeMap Native}
  {context : data_ontology.Context} {J : Interpretation Object' Value'} {N : Normative D}
  {atoms : List (DataProperty × Option DataRange × Nat)} {capacity : Nat} {bits : Usize} {order : List Usize}
  {shift : Object' → ℕ}

/-- The individuals that `J` places at elements that are no data nodes. -/
def Known (J : Interpretation Object' Value') (a : Individual) : Prop := ¬ J.classes dataClass (individual J a)

theorem top_ne_bottom_data : topData ≠ bottomData := by
  rw [Ne, dataProperty_eq_iff]; simp [topData, bottomData]

theorem sound_data_role (good : Good context) (o : Element J) {p : DataProperty} {role : ObjectPropertyExpression}
    (run : data_ontology.data_role context p = .ok (some role)) (z : Element J) (y : Values.{v,w} Native) :
    (sound.{u,v,w,x} context J N order atoms shift o).dataProperties p z y ↔
      ∃ d, Place.{u,v,w,x} context J N order atoms shift z.1 y d ∧ objectRelation J role z.1 d := by
  have notTop : p ≠ topData := by
    rintro rfl
    obtain ⟨res, run', facts⟩ := data_role_correct context topData
    rw [run] at run'
    cases Result.ok_injective run'
    rcases facts role rfl with ⟨h, _⟩ | ⟨_, inData, _⟩
    · exact top_ne_bottom_data h
    · exact (good.2.2.1 topData inData).1 rfl
  simp only [sound, notTop, false_or]
  constructor
  · rintro ⟨role', run', rest⟩
    rw [run] at run'
    cases Result.ok_injective run'
    exact rest
  · intro rest
    exact ⟨role, run, rest⟩

theorem sound_literal (o : Element J) {lt : Literal} {val : datatypes.DataValue}
    (run : datatypes.literal_value lt = .ok (some val)) :
    (sound.{u,v,w,x} context J N order atoms shift o).literals lt = litValue N val := by
  obtain ⟨r, run', facts, _⟩ := Rowl.Datatypes.literal_value_correct lt
  rw [run] at run'
  cases Result.ok_injective run'
  obtain ⟨_, _, _, _, rest⟩ := facts val rfl
  obtain ⟨_, _, value⟩ := rest D N
  simp only [sound, litValue, value]

theorem sound_range_frame (setting : Setting context capacity bits order J) (o : Element J) :
    RangeFrame (sound.{u,v,w,x} context J N order atoms shift o) J (litValue N) (realValue N) where
  literal := fun _ => .inl rfl
  thing := setting.thing
  literals := fun _ _ run => sound_literal o run
  injective := realValue_injective N
  numbers := fun w nw => by simp [litValue, realValue, Rowl.Datatypes.valueOf_number N nw]
  numeric := fun k nk x => by
    rw [sound_types]
    constructor
    · rintro ⟨y, inside, rfl⟩
      obtain ⟨r, rfl, inK⟩ := (Rowl.Datatypes.numeric_space N k nk y).mp inside
      exact ⟨r, rfl, inK⟩
    · rintro ⟨r, rfl, inK⟩
      exact ⟨N.real r, (Rowl.Datatypes.numeric_space N k nk _).mpr ⟨r, rfl, inK⟩, rfl⟩
  facets := fun f F w facet run number x => by
    obtain ⟨r, run', facts, _⟩ := Rowl.Datatypes.literal_value_correct f.value
    rw [run] at run'
    cases Result.ok_injective run'
    obtain ⟨_, _, _, _, rest⟩ := facts w rfl
    obtain ⟨_, _, value⟩ := rest D N
    simp only [sound]
    rw [value, Rowl.Datatypes.valueOf_number N number, facetOf_some facet]
    constructor
    · rintro ⟨y, holds, rfl⟩
      obtain ⟨s, rfl, real⟩ := (facet_reals N F _ y).mp holds
      exact ⟨s, rfl, real⟩
    · rintro ⟨s, rfl, real⟩
      exact ⟨N.real s, (facet_reals N F _ _).mpr ⟨s, rfl, real⟩, rfl⟩
  binaries := fun double x => by
    rw [sound_types]
    constructor
    · rintro ⟨y, inside, rfl⟩
      obtain ⟨b', vb', rfl⟩ := (Rowl.DataComplete.float_space N double y).mp inside
      obtain ⟨b, cb, rfl⟩ := Rowl.FloatOrder.canonical_exists vb'
      exact ⟨b, cb, vb', by simp [litValue, Rowl.DataComplete.lit_float]⟩
    · rintro ⟨b, cb, vb, rfl⟩
      exact ⟨_, (Rowl.DataComplete.float_space N double _).mpr ⟨_, vb, Rowl.DataComplete.lit_float N double b⟩, rfl⟩
  binaryFacets := fun f F double b facet run x => by
    obtain ⟨r, run', facts, _⟩ := Rowl.Datatypes.literal_value_correct f.value
    rw [run] at run'
    cases Result.ok_injective run'
    obtain ⟨canonical, _, _, _, rest⟩ := facts (floatLit double b) rfl
    obtain ⟨_, _, value⟩ := rest D N
    have vb : (Rowl.Floats.binaryOf b).Valid (Rowl.Floats.fmt double) := by
      cases double
      · exact canonical.2
      · exact canonical.2
    simp only [sound]
    rw [value, Rowl.DataComplete.lit_float, facetOf_some facet]
    simp only [Rowl.Datatypes.normative_binary_facet N F double vb]
    constructor
    · rintro ⟨y0, ⟨x', vx', holds, rfl⟩, rfl⟩
      obtain ⟨y, cy, rfl⟩ := Rowl.FloatOrder.canonical_exists vx'
      exact ⟨y, ⟨cy, vx', by simp [litValue, Rowl.DataComplete.lit_float]⟩, holds⟩
    · rintro ⟨y, ⟨cy, vy, rfl⟩, holds⟩
      exact ⟨_, ⟨Rowl.Floats.binaryOf y, vy, holds, rfl⟩, by simp [litValue, Rowl.DataComplete.lit_float]⟩
  binaryReal := fun double b x r h same => by
    obtain ⟨cb, vb, rfl⟩ := h
    simp only [litValue, realValue, embedValue, ULift.up.injEq, Sum.inl.injEq, Rowl.DataComplete.lit_float] at same
    cases double
    · exact N.real_float r _ vb same.symm
    · exact N.real_double r _ vb same.symm
  binaryApart := fun b b' x h h' => by
    obtain ⟨cb, vb, rfl⟩ := h
    obtain ⟨cb', vb', same⟩ := h'
    have := Rowl.Datatypes.value_injective N (Rowl.DataComplete.canonical_float_lit (double := true) cb vb)
      (Rowl.DataComplete.canonical_float_lit (double := false) cb' vb') (embedValue_injective same)
    cases this
  binaryInjective := fun double b b' x h h' => by
    obtain ⟨cb, vb, rfl⟩ := h
    obtain ⟨cb', vb', same⟩ := h'
    have := Rowl.Datatypes.value_injective N (Rowl.DataComplete.canonical_float_lit cb vb)
      (Rowl.DataComplete.canonical_float_lit cb' vb') (embedValue_injective same)
    cases double <;> cases this <;> rfl

theorem sound_atom (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    (shiftOk : ShiftOk context shift) (o : Element J) {p : DataProperty} {range : Option DataRange} {n : Nat} (member : (p, range, n) ∈ atoms)
    {role : ObjectPropertyExpression} {filler : Option ClassExpression}
    (roleRun : data_ontology.data_role context p = .ok (some role))
    (fillerRun : data_ontology.encode_optional_range context range = .ok (some filler)) (z : Element J) :
    (AtLeast n (fun y => (sound.{u,v,w,x} context J N order atoms shift o).dataProperties p z y ∧
      RangeHolds (sound.{u,v,w,x} context J N order atoms shift o) range y)) ↔
      AtLeast n (fun d => objectRelation J role z.1 d ∧ Rowl.Concepts.FillerHolds J filler d) := by
  have fillerAt : ∀ y d, Place.{u,v,w,x} context J N order atoms shift z.1 y d →
      (RangeHolds (sound.{u,v,w,x} context J N order atoms shift o) range y ↔ Rowl.Concepts.FillerHolds J filler d) := by
    intro y d pl
    obtain ⟨placed, rfl⟩ := pl
    rcases optional_range_meaning.{u,max v w,u,x} context range filler fillerRun with
      ⟨rfl, rfl⟩ | ⟨r, c, rfl, rfl, means⟩
    · simp [RangeHolds, Rowl.Concepts.FillerHolds]
    · exact means _ J (litValue N) (realValue N) (sound_range_frame setting o) d _
        (place_node setting count shiftOk o placed)
  constructor
  · rintro ⟨f, fInj, each⟩
    have pick : ∀ i, ∃ d, Place.{u,v,w,x} context J N order atoms shift z.1 (f i) d ∧ objectRelation J role z.1 d :=
      fun i => (sound_data_role setting.good o roleRun z (f i)).mp (each i).1
    choose g gPlace gRel using pick
    refine ⟨g, fun i j same => fInj ?_, fun i => ⟨gRel i, (fillerAt (f i) (g i) (gPlace i)).mp (each i).2⟩⟩
    rw [← (gPlace i).2, ← (gPlace j).2, same]
  · rintro ⟨g, gInj, each⟩
    have h : ∃ f : Fin (p, range, n).2.2 → Object', Function.Injective f ∧ ∀ role' filler',
        data_ontology.data_role context (p, range, n).1 = .ok (some role') →
        data_ontology.encode_optional_range context (p, range, n).2.1 = .ok (some filler') →
        ∀ i, objectRelation J role' z.1 (f i) ∧ Rowl.Concepts.FillerHolds J filler' (f i) := by
      refine ⟨g, gInj, fun role' filler' roleRun' fillerRun' => ?_⟩
      have r1 : role' = role := Option.some.inj (Result.ok_injective (roleRun'.symm.trans roleRun))
      have f1 : filler' = filler := Option.some.inj (Result.ok_injective (fillerRun'.symm.trans fillerRun))
      subst r1 f1
      exact each
    obtain ⟨fInj, fEach⟩ := Classical.choose_spec h
    have listed : witnesses context J z.1 (p, range, n) = List.ofFn (Classical.choose h) := by
      rw [witnesses, dif_pos h]
    have inList : ∀ i, Classical.choose h i ∈ witnessList context J atoms z.1 := fun i =>
      List.mem_flatMap.mpr ⟨(p, range, n), member, by rw [listed]; exact List.mem_ofFn.mpr ⟨i, rfl⟩⟩
    have placed : ∀ i, ValuedNode context J atoms z.1 (Classical.choose h i) := fun i =>
      .inr ⟨inList i, p, role, roleRun, (fEach role filler roleRun fillerRun i).1⟩
    refine ⟨fun i => nodeValue.{u,v,w,x} context J N order atoms shift z.1 (Classical.choose h i),
      fun i j same => fInj (nodeValue_injective setting count shiftOk z.1 (placed i) (placed j) same), fun i => ?_⟩
    have pl : Place.{u,v,w,x} context J N order atoms shift z.1 _ _ := ⟨placed i, rfl⟩
    obtain ⟨related, fills⟩ := fEach role filler roleRun fillerRun i
    exact ⟨(sound_data_role setting.good o roleRun z _).mpr ⟨_, pl, related⟩, (fillerAt _ _ pl).mpr fills⟩

theorem sound_simulates (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    (shiftOk : ShiftOk context shift) (o : Element J) :
    Simulates context (sound.{u,v,w,x} context J N order atoms shift o) J Subtype.val (Known J) atoms where
  injective := Subtype.val_injective
  objects := fun y => ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨z, same⟩ => same ▸ z.2⟩
  classes := fun _ _ _ => Iff.rfl
  roles := fun _ _ _ _ => Iff.rfl
  closed := setting.frame.roles
  topAll := setting.top
  individuals := fun a known => by
    cases a with
    | Named n =>
      have known' : ¬ J.classes dataClass (J.namedIndividuals n) := known
      simp only [individual, sound, dif_pos known']
    | Anonymous b =>
      have known' : ¬ J.classes dataClass (J.anonymousIndividuals b) := known
      simp only [individual, sound, dif_pos known']
  data := fun _ _ _ member _ _ roleRun fillerRun z =>
    sound_atom setting count shiftOk o member roleRun fillerRun z

theorem sound_placed (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    (shiftOk : ShiftOk context shift) (o : Element J) :
    Placed context (sound.{u,v,w,x} context J N order atoms shift o) J Subtype.val (litValue N) (realValue N)
      (fun z y d => Place.{u,v,w,x} context J N order atoms shift z.1 y d) where
  functional := fun z _ d d' pl pl' =>
    nodeValue_injective setting count shiftOk z.1 pl.1 pl'.1 (pl.2.trans pl'.2.symm)
  injective := fun _ _ _ _ pl pl' => pl.2.symm.trans pl'.2
  nodes := fun z _ d pl => by
    obtain ⟨placed, rfl⟩ := pl
    exact place_node setting count shiftOk o placed
  data := fun p role run z y => sound_data_role setting.good o run z y
  literals := fun z lt a run => by
    obtain ⟨res, run', facts⟩ := literal_individual_correct context lt
    rw [run] at run'
    cases Result.ok_injective run'
    obtain ⟨val, i, h, valueRun, at_i, rfl⟩ := facts a rfl
    refine ⟨.inl ⟨i, h, rfl⟩, ?_⟩
    simp only [individual, nodeValue]
    rw [literal_value_at setting i h, at_i, sound_literal o valueRun]
  top := fun _ _ => .inl rfl

/-- The OWL interpretation made from an interpretation of the encoding is an
    interpretation for the datatype map. -/
theorem sound_interpretation (V : Vocabulary) (jThing : ∀ d, J.classes thing d)
    (jNothing : ∀ d, ¬ J.classes nothing d) (jTop : ∀ y y', J.objectProperties topObject y y')
    (jBottom : ∀ y y', ¬ J.objectProperties bottomObject y y') (o : Element J) :
    IsInterpretation D (ValueEmbedding.ofEmbedding D ⟨embedValue.{v,w}, embedValue_injective⟩) V
      (sound.{u,v,w,x} context J N order atoms shift o) := by
  refine ⟨fun z => jThing z.1, fun z => jNothing z.1, fun z z' => jTop z.1 z'.1, fun z z' => jBottom z.1 z'.1,
    fun _ _ => .inl rfl, ?_, fun dt supported y => ?_, fun _ => .inl rfl, fun _ _ => rfl, fun _ _ _ => Iff.rfl,
    fun _ _ => trivial⟩
  · intro z y holds
    rcases holds with h | ⟨role, run, d, _, related⟩
    · exact top_ne_bottom_data h.symm
    · obtain ⟨res, run', facts⟩ := data_role_correct context bottomData
      rw [run] at run'
      cases Result.ok_injective run'
      rcases facts role rfl with ⟨_, rfl⟩ | ⟨notBottom, _⟩
      · exact jBottom _ _ related
      · exact notBottom rfl
  · have notLiteral : dt ≠ literalDatatype := fun same => D.excludesLiteral (same ▸ supported)
    simp only [sound, notLiteral, false_or]
    rfl

end Correspondence

/-! ### Satisfaction -/

section Satisfaction
variable {Object' : Type u} {Value' : Type x} {Native : Type w} {D : DatatypeMap Native}

/-- The data restrictions of a closure's axioms. -/
def itemAtoms (items : List AnnotatedAxiom) : List (DataProperty × Option DataRange × Nat) :=
  items.flatMap (fun i => axiomAtoms i.axiom)

/-- An interpretation of a closure's encoding for a capacity that satisfies it
    gives an OWL interpretation of the closure that satisfies it, for every
    list of data restrictions that covers the closure's and counts at most the
    capacity. -/
theorem sound_satisfies (N : Normative D) {context : data_ontology.Context} (good : Good context)
    {capacity : Usize} (capSmall : capacity.val < Usize.max / 16)
    {items enc : alloc.vec.Vec AnnotatedAxiom} (run : data_ontology.encode context capacity items = .ok (some enc))
    {J : Interpretation Object' Value'} (jThing : ∀ d, J.classes thing d)
    (jTop : ∀ y y', J.objectProperties topObject y y') (jBottom : ∀ y y', ¬ J.objectProperties bottomObject y y')
    (holds : ∀ b ∈ enc.val, satisfies J b.axiom) :
    ∃ (bits : Usize) (order : List Usize) (o : Element J), Setting context capacity.val bits order J ∧
      (∀ item ∈ items.val, ∀ a ∈ axiomIndividuals item.axiom, Known J a) ∧
      ∀ atoms, (∀ a ∈ itemAtoms items.val, a ∈ atoms) → atomCount atoms ≤ capacity.val →
        satisfiesClosure (sound.{u,v,w,x} context J N order atoms (fun _ => 0) o) items.val := by
  obtain ⟨res, run', facts⟩ := encode_meaning.{u,max v w,u,x} context good capacity capSmall items
  rw [run] at run'
  cases Result.ok_injective run'
  obtain ⟨fine, valuesCut, new, bits, order, means, enough, sorted, _, _, iff⟩ := facts enc rfl
  obtain ⟨newHolds, frame⟩ := (iff J).mp holds
  let o : Element J := ⟨J.namedIndividuals objectIndividual, frame.object⟩
  have names := means.2.2 J newHolds
  have setting : Setting context capacity.val bits order J :=
    ⟨good, frame, enough, sorted, fine, valuesCut, jThing, jTop, jBottom⟩
  refine ⟨bits, order, o, setting, names, fun atoms covers count => ?_⟩
  exact (means.1 (sound.{u,v,w,x} context J N order atoms (fun _ => 0) o) J Subtype.val (Known J) atoms (litValue N)
    (realValue N) _ (sound_simulates setting count (fun _ _ => rfl) o) (sound_placed setting count (fun _ _ => rfl) o)
    (sound_range_frame setting o)
    (fun item mem a inside => covers a (List.mem_flatMap.mpr ⟨item, mem, inside⟩)) names).1 newHolds

/-- A class expression holds at an element of the OWL interpretation exactly
    when its encoding holds at it. -/
theorem sound_class (N : Normative D) {context : data_ontology.Context} {capacity : Nat} {bits : Usize}
    {order : List Usize} {J : Interpretation Object' Value'} (setting : Setting context capacity bits order J)
    (o : Element J) {atoms : List (DataProperty × Option DataRange × Nat)} (count : atomCount atoms ≤ capacity)
    {shift : Object' → ℕ} (shiftOk : ShiftOk context shift)
    {c c' : ClassExpression} (run : data_ontology.encode_class context c = .ok (some c'))
    (atomsIn : ∀ a ∈ classAtoms c, a ∈ atoms) (known : ∀ a ∈ classIndividuals c, Known J a) (z : Element J) :
    classDenote (sound.{u,v,w,x} context J N order atoms shift o) c z ↔ classDenote J c' z.1 := by
  obtain ⟨res, run', means⟩ := encode_class_meaning.{u,max v w,u,x} context c
  rw [run] at run'
  cases Result.ok_injective run'
  exact means c' rfl _ J Subtype.val (Known J) atoms (sound_simulates setting count shiftOk o) atomsIn known z

end Satisfaction

/-! ### Other anonymous individuals -/

section Anonymous
variable {Object' : Type u} {Value' : Type x} {Native : Type w} {D : DatatypeMap Native}
  {context : data_ontology.Context} {J : Interpretation Object' Value'} {capacity : Nat} {bits : Usize}
  {order : List Usize}

/-- The fillers of the encoding's data restrictions mean the same when the
    anonymous individuals are reinterpreted. -/
theorem filler_anonymous (N : Normative D) (g : AnonymousIndividual → Object')
    (setting : Setting context capacity bits order (withAnonymous J g)) (o : Element (withAnonymous J g))
    {range : Option DataRange} {filler : Option ClassExpression}
    (run : data_ontology.encode_optional_range context range = .ok (some filler)) (d : Object') :
    Rowl.Concepts.FillerHolds (withAnonymous J g) filler d ↔ Rowl.Concepts.FillerHolds J filler d := by
  rcases optional_range_meaning.{u,w,u,x} context range filler run with
    ⟨rfl, rfl⟩ | ⟨r, c, rfl, rfl, means⟩
  · simp [Rowl.Concepts.FillerHolds]
  · simp only [Rowl.Concepts.FillerHolds]
    have node := value_node (N := N) (atoms := []) (shift := fun _ => 0) (n := 0) setting o (d := d)
      (fun ld => alone_valid setting ld)
    have frame0 : RangeFrame (sound.{u,0,w,x} context (withAnonymous J g) N order [] (fun _ => 0) o) (withAnonymous J g)
        (litValue N) (realValue N) := sound_range_frame (shift := fun _ => 0) setting o
    have frameJ : RangeFrame (sound.{u,0,w,x} context (withAnonymous J g) N order [] (fun _ => 0) o) J (litValue N)
        (realValue N) :=
      ⟨frame0.literal, frame0.thing, frame0.literals, frame0.injective, frame0.numbers, frame0.numeric,
        frame0.facets, frame0.binaries, frame0.binaryFacets, frame0.binaryReal, frame0.binaryApart,
        frame0.binaryInjective⟩
    have nodeJ : NodeValue context (sound.{u,0,w,x} context (withAnonymous J g) N order [] (fun _ => 0) o) J (litValue N)
        (realValue N) d (valueAt.{u,0,w,x} context (withAnonymous J g) N order d 0) :=
      ⟨node.kinds, node.values, node.cuts, node.edges⟩
    exact (means _ _ _ _ frame0 d _ node).symm.trans (means _ J _ _ frameJ d _ nodeJ)

/-- A correspondence with an interpretation of the encoding with other
    anonymous individuals is one with the interpretation itself, for the
    individuals placed alike. -/
theorem simulates_anonymous (N : Normative D) (g : AnonymousIndividual → Object')
    (setting : Setting context capacity bits order (withAnonymous J g)) (o : Element (withAnonymous J g))
    {Object : Type uI} {Value : Type vI} {I : Interpretation Object Value}
    {obj : Object → Object'} {known known' : Individual → Prop}
    {atoms : List (DataProperty × Option DataRange × Nat)}
    (sim : Simulates context I (withAnonymous J g) obj known atoms)
    (individuals : ∀ a, known' a → individual J a = obj (individual I a)) :
    Simulates context I J obj known' atoms where
  injective := sim.injective
  objects := sim.objects
  classes := sim.classes
  roles := sim.roles
  closed := sim.closed
  topAll := sim.topAll
  individuals := individuals
  data := fun p range n member role filler roleRun fillerRun z => by
    rw [sim.data p range n member role filler roleRun fillerRun z]
    have same : ∀ y, (objectRelation (withAnonymous J g) role (obj z) y ∧
        Rowl.Concepts.FillerHolds (withAnonymous J g) filler y) ↔
        (objectRelation J role (obj z) y ∧ Rowl.Concepts.FillerHolds J filler y) := fun y =>
      and_congr Iff.rfl (filler_anonymous N g setting o fillerRun y)
    simp only [same]

end Anonymous

end Rowl.DataSound
