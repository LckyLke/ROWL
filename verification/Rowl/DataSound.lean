import Rowl.DataComplete
import Rowl.DataReals

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
restrictions are at most their number. Strings of the letter a, tagged strings,
IRIs of letters a, octet sequences of zeros and values outside every datatype
serve the other data nodes. When the
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

/-- The regions of values that data nodes get: the reals of a level in the
    interval at a position of the cuts, strings of the letter a, tagged
    strings, IRIs and octet sequences, and values outside every datatype. -/
inductive Region where
  | number (position level : Nat) | string | tagged | coded (s : Sequence) | other

/-- Which indices of a region have values of their own. -/
def Valid (cs : List regions.Cut) (lits : Set ℝ) : Region → ℕ → Prop
  | .number p ℓ, n => ℓ ≤ 3 ∧ ((regionSet cs lits p ℓ).Infinite ∨ n < (regionSet cs lits p ℓ).ncard)
  | _, _ => True

/-- Whether a region has a value for every index. -/
def RegionInfinite (cs : List regions.Cut) (lits : Set ℝ) : Region → Prop
  | .number p ℓ => ℓ ≤ 3 ∧ (regionSet cs lits p ℓ).Infinite
  | _ => True

theorem valid_of_infinite {cs : List regions.Cut} {lits : Set ℝ} {r : Region} (h : RegionInfinite cs lits r) (n : ℕ) :
    Valid cs lits r n := by
  cases r <;> simp_all [RegionInfinite, Valid]

section Regions
variable {Native : Type w} {D : DatatypeMap Native}

/-- The values of a region. -/
noncomputable def regionValue (N : Normative D) (cs : List regions.Cut) (lits : Set ℝ) :
    Region → ℕ → Values.{v,w} Native
  | .number p ℓ, n => embedValue (N.real (enumerate (regionSet cs lits p ℓ) n))
  | .string, n => embedValue (N.text (aText n))
  | .tagged, n => embedValue (N.tagged (aText n) enTag)
  | .coded s, n => embedValue (N.coded (codedAt s n))
  | .other, n => ULift.up (.inr n)

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
    | string =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.real_text _ _ (aText_xml n'))
    | tagged =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.real_tagged _ _ _ (aText_xml n') tag)
    | coded s' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.real_coded _ _ (sequence_valid s' n'))
    | other => simp [regionValue, embedValue] at same
  | string =>
    cases r' with
    | number p' ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.real_text _ _ (aText_xml n))
    | string =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact ⟨rfl, aText_injective (N.text_injective _ _ (aText_xml n) (aText_xml n') same)⟩
    | tagged =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.text_tagged _ _ _ (aText_xml n) (aText_xml n') tag)
    | coded s' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.text_coded _ _ (aText_xml n) (sequence_valid s' n'))
    | other => simp [regionValue, embedValue] at same
  | tagged =>
    cases r' with
    | number p' ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.real_tagged _ _ _ (aText_xml n) tag)
    | string =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.text_tagged _ _ _ (aText_xml n') (aText_xml n) tag)
    | tagged =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact ⟨rfl, aText_injective (N.tagged_injective _ _ _ _ (aText_xml n) (aText_xml n') tag tag same).1⟩
    | coded s' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same (N.tagged_coded _ _ _ (aText_xml n) tag (sequence_valid s' n'))
    | other => simp [regionValue, embedValue] at same
  | coded s =>
    cases r' with
    | number p' ℓ' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.real_coded _ _ (sequence_valid s n))
    | string =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.text_coded _ _ (aText_xml n') (sequence_valid s n))
    | tagged =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      exact absurd same.symm (N.tagged_coded _ _ _ (aText_xml n') tag (sequence_valid s n))
    | coded s' =>
      simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
      obtain ⟨rfl, rfl⟩ := sequence_injective (N.coded_injective _ _ (sequence_valid s n) (sequence_valid s' n') same)
      exact ⟨rfl, rfl⟩
    | other => simp [regionValue, embedValue] at same
  | other =>
    cases r' with
    | number p' ℓ' => simp [regionValue, embedValue] at same
    | string => simp [regionValue, embedValue] at same
    | tagged => simp [regionValue, embedValue] at same
    | coded s' => simp [regionValue, embedValue] at same
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
  | string =>
    simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
    exact aText_injective (N.text_injective _ _ (aText_xml a) (aText_xml b) same)
  | tagged =>
    simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
    exact aText_injective (N.tagged_injective _ _ _ _ (aText_xml a) (aText_xml b) enTag_value enTag_value same).1
  | coded s =>
    simp only [regionValue, embedValue, ULift.up.injEq, Sum.inl.injEq] at same
    exact (sequence_injective (N.coded_injective _ _ (sequence_valid s a) (sequence_valid s b) same)).2
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

/-- The kinds whose datatypes a region's value at an index is in. -/
def RegionIn (cs : List regions.Cut) (lits : Set ℝ) : Region → ℕ → datatypes.Kind → Prop
  | .number p ℓ, n, k => Rowl.Datatypes.IsNumeric k ∧ RealIn k (enumerate (regionSet cs lits p ℓ) n)
  | .string, _, k => k = .String ∨ k = .Plain
  | .tagged, _, k => k = .Plain
  | .coded s, _, k => k = sequenceKind s
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
    cases k <;> simp only [Rowl.Datatypes.IsNumeric, IsCoded, not_true_eq_false] at numeric ck
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
    D.valueSpace (typeOf k) (N.text t) ↔ k = .String ∨ k = .Plain := by
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
    cases k <;> simp only [Rowl.Datatypes.IsNumeric, IsCoded, not_true_eq_false] at numeric ck
    · simp only [typeOf, N.string_space, true_or, iff_true]
      exact ⟨t, xs, rfl⟩
    · simp only [typeOf, N.plain_space, or_true, iff_true]
      exact .inl ⟨t, xs, rfl⟩
    · simp only [typeOf, N.boolean_space, reduceCtorEq, or_self, iff_false, not_exists]
      exact fun b e => N.text_truth t b xs e

theorem tagged_space (N : Normative D) (t l : List U8) (xs : XmlText t) (tl : TagValue l) (k : datatypes.Kind) :
    D.valueSpace (typeOf k) (N.tagged t l) ↔ k = .Plain := by
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
    cases k <;> simp only [Rowl.Datatypes.IsNumeric, IsCoded, not_true_eq_false] at numeric ck
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

/-- A region's values are in the datatypes of the kinds `RegionIn` names. -/
theorem region_space (N : Normative D) (cs : List regions.Cut) (lits : Set ℝ) (r : Region) (n : ℕ)
    (k : datatypes.Kind) :
    (∃ y, D.valueSpace (typeOf k) y ∧ embedValue.{v,w} y = regionValue N cs lits r n) ↔ RegionIn cs lits r n k := by
  cases r with
  | number p ℓ => rw [regionValue, embedded_space, real_space N]; rfl
  | string => rw [regionValue, embedded_space, text_space N _ (aText_xml n)]; rfl
  | tagged => rw [regionValue, embedded_space, tagged_space N _ _ (aText_xml n) enTag_value]; rfl
  | coded s => rw [regionValue, embedded_space, coded_space N s n]; rfl
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

/-- The region of a node's values. -/
noncomputable def regionOf (d : Object') : Region :=
  if NumericNode context J d then .number (positionOf context J order d) (levelOf context J d)
  else if InUse context J .String d then .string
  else if InUse context J .Plain d then .tagged
  else if InUse context J .AnyUri d then .coded .uri
  else if InUse context J .HexBinary d then .coded .hex
  else if InUse context J .Base64Binary d then .coded .base64
  else .other

theorem level_le (d : Object') : levelOf context J d ≤ 3 := by
  unfold levelOf; split_ifs <;> omega

theorem position_le (d : Object') : positionOf context J order d ≤ (orderedCuts context order).length := by
  unfold positionOf
  split_ifs with h
  · exact le_of_lt (Nat.find_spec h).1
  · exact le_rfl

variable {context J}

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
    obtain ⟨us, ast⟩ := hs
    cases k <;> simp only [Used, Bool.false_eq_true] at used <;> simp only [reduceCtorEq, or_false, false_or, or_self, iff_true,
      iff_false, true_or, or_true]
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
  · simp only [hs, hp, hu, hh, hb, ↓reduceIte, RegionIn, iff_false]
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
    · have step := ((setting.frame.regions ordered).2.1 (k + 1) hk (by omega) (by omega)).1 y inK
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
  exact (setting.frame.values i hi).2.2.2 ordered number order[k] (order_in setting ordered hk)

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
  exact (setting.frame.regions ordered).1 _ head y first

/-- A literal value that is no number has its individual in no cut's class. -/
theorem literal_no_cut (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    {i : Usize} (hi : i.val < context.values.val.length)
    (notNumber : ¬ Rowl.Datatypes.IsNumber context.values.val[i.val]) {k : Nat} (hk : k < order.length) :
    ¬ J.classes (cutClass order[k]) (J.namedIndividuals (valueIndividual i)) := by
  intro inK
  have real := ((setting.frame.values i hi).2.1 .Real (real_used setting ordered)).mp (cut_real setting ordered hk inK)
  revert notNumber real
  cases context.values.val[i.val] <;> simp [InKind, Rowl.Datatypes.IsNumber]

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
  have between := ((setting.frame.regions ordered).2.1 _ inside (by omega) pos).2.1 same' i hj at_j d
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
  (atoms : List (DataProperty × Option DataRange × Nat))

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
    its peers. -/
noncomputable def nodeValue (z d : Object') : Values.{v,w} Native :=
  valueAt.{u,v,w,x} context J N order d ((peers context J order atoms z d).idxOf d)

/-- The data nodes that have values for an element: the literal values'
    individuals and its successors among its witnesses. -/
def ValuedNode (z d : Object') : Prop :=
  LiteralNode context J d ∨ (d ∈ witnessList context J atoms z ∧ Successor context J z d)

/-- An element's values at its data nodes. -/
def Place (z : Object') (y : Values.{v,w} Native) (d : Object') : Prop :=
  ValuedNode context J atoms z d ∧ nodeValue.{u,v,w,x} context J N order atoms z d = y

/-- The elements of the interpretation of the encoding that are no data nodes. -/
def Element : Type u := {y : Object' // ¬ J.classes dataClass y}

/-- The OWL interpretation made from an interpretation of the encoding. -/
noncomputable def sound (o : Element J) : Interpretation (Element J) (Values.{v,w} Native) where
  objectsNonempty := ⟨o⟩
  dataNonempty := ⟨ULift.up (.inr 0)⟩
  classes c z := J.classes c z.1
  objectProperties r z z' := J.objectProperties r z.1 z'.1
  dataProperties p z y := p = topData ∨ ∃ role, data_ontology.data_role context p = .ok (some role) ∧
    ∃ d, Place.{u,v,w,x} context J N order atoms z.1 y d ∧ objectRelation J role z.1 d
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
    (notLiteral : ¬ LiteralNode context J d)
    (finite : ¬ RegionInfinite (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)) :
    context.kinds.ordered = true ∧ NumericNode context J d ∧ levelOf context J d = 0 ∧
      0 < positionOf context J order d ∧ positionOf context J order d < order.length := by
  by_cases numeric : NumericNode context J d
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
  · exfalso
    apply finite
    unfold regionOf
    simp only [numeric, ↓reduceIte]
    split_ifs <;> trivial

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
  exact (((setting.frame.regions ordered).2.1 p inside (by omega) pos).2).2 differ integer

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
    `U`, when the integers are in use. -/
theorem successor_super (setting : Setting context capacity bits order J) (ordered : context.kinds.ordered = true)
    (integer : Used context.kinds .Integer = true) {z e : Object'} (succ : Successor context J z e) :
    J.objectProperties dataSuper z e := by
  obtain ⟨p, role, run, rel⟩ := succ
  obtain ⟨res, run', facts⟩ := data_role_correct context p
  rw [run] at run'
  cases Result.ok_injective run'
  rcases facts role rfl with ⟨_, rfl⟩ | ⟨_, inData, _, q, rfl, _⟩
  · exact absurd rel (setting.bottom z e)
  · obtain ⟨k, hk, at_k⟩ := List.getElem_of_mem inData
    exact (setting.frame.regions ordered).2.2 integer k hk (Nat.zero_le _) (.Property q) (by rw [at_k]; exact run) z e
      rel

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
    {z d : Object'} (notLiteral : ¬ LiteralNode context J d)
    (finite : ¬ RegionInfinite (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)) :
    (peers context J order atoms z d).length ≤
      (regionSet (orderedCuts context order) (literalReals context.values.val) (positionOf context J order d) 0).ncard := by
  obtain ⟨ordered, numeric, level, pos, inside⟩ := finite_run setting notLiteral finite
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
    exact ⟨successor_super setting ordered integer succ, run_member setting ordered level_e pos inside at_p,
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

/-- The index of the value of a node that is placed for an element is one its
    region has a value for. -/
theorem placed_valid (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    {z d : Object'} (notLiteral : ¬ LiteralNode context J d) (inList : d ∈ witnessList context J atoms z)
    (succ : Successor context J z d) :
    Valid (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
      (regionStart.{v,w} context N order (regionOf context J order d) + (peers context J order atoms z d).idxOf d) := by
  by_cases infinite : RegionInfinite (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
  · exact valid_of_infinite infinite _
  · rw [region_start_finite context N order _ infinite, zero_add]
    obtain ⟨_, numeric, level, _, _⟩ := finite_run setting notLiteral infinite
    have bound := peers_bound setting count notLiteral infinite (z := z)
    have mem : d ∈ peers context J order atoms z d := mem_peers.mpr ⟨inList, succ, notLiteral, rfl⟩
    have idx := List.idxOf_lt_length_of_mem mem
    rw [region_numeric numeric, level]
    exact ⟨Nat.zero_le _, .inr (lt_of_lt_of_le idx bound)⟩

/-- The first index of a node's region is one it has a value for. -/
theorem alone_valid (setting : Setting context capacity bits order J) {d : Object'}
    (notLiteral : ¬ LiteralNode context J d) :
    Valid (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
      (regionStart.{v,w} context N order (regionOf context J order d) + 0) := by
  by_cases infinite : RegionInfinite (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
  · exact valid_of_infinite infinite _
  · rw [region_start_finite context N order _ infinite, zero_add]
    obtain ⟨ordered, numeric, level, pos, inside⟩ := finite_run setting notLiteral infinite
    have integer : Used context.kinds .Integer = true := (level_zero level).1
    have gap := run_gap setting ordered pos inside (not_point setting ordered notLiteral pos inside) integer
    have member := run_member setting ordered level pos inside rfl
    rw [region_numeric numeric, level]
    refine ⟨Nat.zero_le _, .inr ?_⟩
    rw [run_count setting ordered pos inside]
    by_contra zero
    obtain ⟨i, hi, _, same⟩ := gap.1 (by omega) d member
    exact notLiteral ⟨i, hi, same⟩

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
  · have infinite : RegionInfinite (orderedCuts context order) (literalReals context.values.val)
        (regionOf context J order d) := by
      unfold regionOf
      simp only [numeric, ↓reduceIte]
      split_ifs <;> trivial
    intro same
    exact region_start_spec context N order _ infinite _ (Nat.le_add_right _ _) ⟨val, member, same⟩

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
    (sound.{u,v,w,x} context J N order atoms o).datatypes (typeOf k) y ↔
      ∃ y0, D.valueSpace (typeOf k) y0 ∧ embedValue y0 = y := by
  simp only [sound, typeOf_not_literal N k, false_or]

theorem realValue_injective (N : Normative D) : Function.Injective (realValue.{v,w} N) := fun _ _ same =>
  N.real_injective (embedValue_injective same)

/-- A data node's value at an index its region has a value for stands for
    it. -/
theorem value_node (setting : Setting context capacity bits order J) (o : Element J) {d : Object'} {n : ℕ}
    (valid : ¬ LiteralNode context J d → Valid (orderedCuts context order) (literalReals context.values.val) (regionOf context J order d)
      (regionStart.{v,w} context N order (regionOf context J order d) + n)) :
    NodeValue context (sound.{u,v,w,x} context J N order atoms o) J (litValue N) (realValue N) d
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
          · exact absurd same.symm (N.real_text r _ (aText_xml _))
          · exact absurd same.symm (N.real_tagged r _ _ (aText_xml _) enTag_value)
          all_goals exact absurd same.symm (N.real_coded r _ (sequence_valid _ _))

theorem peers_same {z d d' : Object'} (same : regionOf context J order d = regionOf context J order d') :
    peers context J order atoms z d = peers context J order atoms z d' := by
  simp only [peers, same]

/-- Distinct data nodes that have values for an element have distinct
    values. -/
theorem nodeValue_injective (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    (z : Object') {d d' : Object'} (hd : ValuedNode context J atoms z d) (hd' : ValuedNode context J atoms z d')
    (same : nodeValue.{u,v,w,x} context J N order atoms z d = nodeValue context J N order atoms z d') : d = d' := by
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
      exact absurd same.symm (region_not_literal setting ld' (placed_valid setting count ld' placed.1 placed.2)
        (List.getElem_mem hi))
  · have placed := hd.resolve_left ld
    have valid := placed_valid (N := N) setting count ld placed.1 placed.2
    by_cases ld' : LiteralNode context J d'
    · obtain ⟨i', hi', rfl⟩ := ld'
      rw [literal_value_at setting i' hi'] at same
      exact absurd same (region_not_literal setting ld valid (List.getElem_mem hi'))
    · have placed' := hd'.resolve_left ld'
      have valid' := placed_valid (N := N) setting count ld' placed'.1 placed'.2
      rw [region_value_at d ld, region_value_at d' ld'] at same
      have len := position_le context J order
      obtain ⟨sameRegion, sameIndex⟩ := region_value_injective N (cuts_sorted setting) valid valid'
        (fun p ℓ h => by obtain ⟨_, rfl, _⟩ := region_number h; exact len d)
        (fun p ℓ h => by obtain ⟨_, rfl, _⟩ := region_number h; exact len d') same
      rw [sameRegion] at sameIndex
      rw [peers_same sameRegion] at sameIndex
      have index : (peers context J order atoms z d').idxOf d = (peers context J order atoms z d').idxOf d' := by
        omega
      have mem : d ∈ peers context J order atoms z d' :=
        mem_peers.mpr ⟨placed.1, placed.2, ld, sameRegion⟩
      exact (List.idxOf_inj mem).mp index

/-- Each data node an element has a value at stands for it. -/
theorem place_node (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    (o : Element J) {z d : Object'} (placed : ValuedNode context J atoms z d) :
    NodeValue context (sound.{u,v,w,x} context J N order atoms o) J (litValue N) (realValue N) d
      (nodeValue.{u,v,w,x} context J N order atoms z d) :=
  value_node setting o (fun ld => placed_valid setting count ld (placed.resolve_left ld).1 (placed.resolve_left ld).2)

end Values

/-! ### The correspondence -/

section Correspondence
variable {Object' : Type u} {Value' : Type x} {Native : Type w} {D : DatatypeMap Native}
  {context : data_ontology.Context} {J : Interpretation Object' Value'} {N : Normative D}
  {atoms : List (DataProperty × Option DataRange × Nat)} {capacity : Nat} {bits : Usize} {order : List Usize}

/-- The individuals that `J` places at elements that are no data nodes. -/
def Known (J : Interpretation Object' Value') (a : Individual) : Prop := ¬ J.classes dataClass (individual J a)

theorem top_ne_bottom_data : topData ≠ bottomData := by
  rw [Ne, dataProperty_eq_iff]; simp [topData, bottomData]

theorem sound_data_role (good : Good context) (o : Element J) {p : DataProperty} {role : ObjectPropertyExpression}
    (run : data_ontology.data_role context p = .ok (some role)) (z : Element J) (y : Values.{v,w} Native) :
    (sound.{u,v,w,x} context J N order atoms o).dataProperties p z y ↔
      ∃ d, Place.{u,v,w,x} context J N order atoms z.1 y d ∧ objectRelation J role z.1 d := by
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
    (sound.{u,v,w,x} context J N order atoms o).literals lt = litValue N val := by
  obtain ⟨r, run', facts, _⟩ := Rowl.Datatypes.literal_value_correct lt
  rw [run] at run'
  cases Result.ok_injective run'
  obtain ⟨_, _, _, _, rest⟩ := facts val rfl
  obtain ⟨_, _, value⟩ := rest D N
  simp only [sound, litValue, value]

theorem sound_range_frame (setting : Setting context capacity bits order J) (o : Element J) :
    RangeFrame (sound.{u,v,w,x} context J N order atoms o) J (litValue N) (realValue N) where
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

theorem sound_atom (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    (o : Element J) {p : DataProperty} {range : Option DataRange} {n : Nat} (member : (p, range, n) ∈ atoms)
    {role : ObjectPropertyExpression} {filler : Option ClassExpression}
    (roleRun : data_ontology.data_role context p = .ok (some role))
    (fillerRun : data_ontology.encode_optional_range context range = .ok (some filler)) (z : Element J) :
    (AtLeast n (fun y => (sound.{u,v,w,x} context J N order atoms o).dataProperties p z y ∧
      RangeHolds (sound.{u,v,w,x} context J N order atoms o) range y)) ↔
      AtLeast n (fun d => objectRelation J role z.1 d ∧ Rowl.Concepts.FillerHolds J filler d) := by
  have fillerAt : ∀ y d, Place.{u,v,w,x} context J N order atoms z.1 y d →
      (RangeHolds (sound.{u,v,w,x} context J N order atoms o) range y ↔ Rowl.Concepts.FillerHolds J filler d) := by
    intro y d pl
    obtain ⟨placed, rfl⟩ := pl
    rcases optional_range_meaning.{u,max v w,u,x} context range filler fillerRun with
      ⟨rfl, rfl⟩ | ⟨r, c, rfl, rfl, means⟩
    · simp [RangeHolds, Rowl.Concepts.FillerHolds]
    · exact means _ J (litValue N) (realValue N) (sound_range_frame setting o) d _
        (place_node setting count o placed)
  constructor
  · rintro ⟨f, fInj, each⟩
    have pick : ∀ i, ∃ d, Place.{u,v,w,x} context J N order atoms z.1 (f i) d ∧ objectRelation J role z.1 d :=
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
    refine ⟨fun i => nodeValue.{u,v,w,x} context J N order atoms z.1 (Classical.choose h i),
      fun i j same => fInj (nodeValue_injective setting count z.1 (placed i) (placed j) same), fun i => ?_⟩
    have pl : Place.{u,v,w,x} context J N order atoms z.1 _ _ := ⟨placed i, rfl⟩
    obtain ⟨related, fills⟩ := fEach role filler roleRun fillerRun i
    exact ⟨(sound_data_role setting.good o roleRun z _).mpr ⟨_, pl, related⟩, (fillerAt _ _ pl).mpr fills⟩

theorem sound_simulates (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    (o : Element J) :
    Simulates context (sound.{u,v,w,x} context J N order atoms o) J Subtype.val (Known J) atoms where
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
    sound_atom setting count o member roleRun fillerRun z

theorem sound_placed (setting : Setting context capacity bits order J) (count : atomCount atoms ≤ capacity)
    (o : Element J) :
    Placed context (sound.{u,v,w,x} context J N order atoms o) J Subtype.val (litValue N) (realValue N)
      (fun z y d => Place.{u,v,w,x} context J N order atoms z.1 y d) where
  functional := fun z _ d d' pl pl' =>
    nodeValue_injective setting count z.1 pl.1 pl'.1 (pl.2.trans pl'.2.symm)
  injective := fun _ _ _ _ pl pl' => pl.2.symm.trans pl'.2
  nodes := fun z _ d pl => by
    obtain ⟨placed, rfl⟩ := pl
    exact place_node setting count o placed
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
      (sound.{u,v,w,x} context J N order atoms o) := by
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
        satisfiesClosure (sound.{u,v,w,x} context J N order atoms o) items.val := by
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
  exact (means.1 (sound.{u,v,w,x} context J N order atoms o) J Subtype.val (Known J) atoms (litValue N)
    (realValue N) _ (sound_simulates setting count o) (sound_placed setting count o) (sound_range_frame setting o)
    (fun item mem a inside => covers a (List.mem_flatMap.mpr ⟨item, mem, inside⟩)) names).1 newHolds

/-- A class expression holds at an element of the OWL interpretation exactly
    when its encoding holds at it. -/
theorem sound_class (N : Normative D) {context : data_ontology.Context} {capacity : Nat} {bits : Usize}
    {order : List Usize} {J : Interpretation Object' Value'} (setting : Setting context capacity bits order J)
    (o : Element J) {atoms : List (DataProperty × Option DataRange × Nat)} (count : atomCount atoms ≤ capacity)
    {c c' : ClassExpression} (run : data_ontology.encode_class context c = .ok (some c'))
    (atomsIn : ∀ a ∈ classAtoms c, a ∈ atoms) (known : ∀ a ∈ classIndividuals c, Known J a) (z : Element J) :
    classDenote (sound.{u,v,w,x} context J N order atoms o) c z ↔ classDenote J c' z.1 := by
  obtain ⟨res, run', means⟩ := encode_class_meaning.{u,max v w,u,x} context c
  rw [run] at run'
  cases Result.ok_injective run'
  exact means c' rfl _ J Subtype.val (Known J) atoms (sound_simulates setting count o) atomsIn known z

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
    have node := value_node (N := N) (atoms := []) (n := 0) setting o (d := d) (fun ld => alone_valid setting ld)
    have frame0 : RangeFrame (sound.{u,0,w,x} context (withAnonymous J g) N order [] o) (withAnonymous J g)
        (litValue N) (realValue N) := sound_range_frame setting o
    have frameJ : RangeFrame (sound.{u,0,w,x} context (withAnonymous J g) N order [] o) J (litValue N)
        (realValue N) :=
      ⟨frame0.literal, frame0.thing, frame0.literals, frame0.injective, frame0.numbers, frame0.numeric,
        frame0.facets⟩
    have nodeJ : NodeValue context (sound.{u,0,w,x} context (withAnonymous J g) N order [] o) J (litValue N)
        (realValue N) d (valueAt.{u,0,w,x} context (withAnonymous J g) N order d 0) :=
      ⟨node.kinds, node.values, node.cuts⟩
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
