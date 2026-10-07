import Rowl.DataAxioms
import Mathlib.Data.Int.Interval

/-!
The axioms that `data_ontology` adds for ordered numbers. When a datatype
restriction or a subtype of `xsd:integer` is in use, every cut of the context
(the bounds of its facets and subtypes) gets a class; the kernel lists the cuts
in order (`Rowl.Regions.cut_order_spec`) and adds: the first cut's class inside
the reals, each cut's class inside the one before it, the two cuts of a number
leaving only its literal value's individual, and, when the integers are in use,
for two neighbouring cuts of different numbers, the integers between them that
are no literal values (`freeCount`): none at all, or at most their number at
any element along a role `U` above every data property's role when there are
fewer of them than the counts of the data restrictions together
(`region_axioms_spec`, `RegionFacts`). The literal values of a run are counted
exactly (`named_card`, `free_card`).
-/
namespace Rowl.DataRegions
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.Regions (cutAt Ordered FineCuts firstIn lastOutside InCut Fit)
open Rowl.Datatypes (InKind CanonicalNumeric IsNumber numValue digitWidth)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe w x

variable {Object' : Type w} {Value' : Type x}

/-- The number of integers in the cut `low` and outside the cut `high`. -/
noncomputable def runCount (low high : regions.Cut) : Nat :=
  (lastOutside high - firstIn low + 1).toNat

/-- A data node of a run: an integer in the cut at `low` and outside the cut
    at `high`. -/
def InRun (J : Interpretation Object' Value') (low high : Usize) (y : Object') : Prop :=
  J.classes (kindClass .Integer) y ∧ J.classes (cutClass low) y ∧ ¬ J.classes (cutClass high) y

/-- A literal value of a run: an integer in the cut `low` and outside the cut
    `high`. -/
def RunValue (low high : regions.Cut) (v : datatypes.DataValue) : Prop :=
  InKind v .Integer ∧ InCut low (numValue v) ∧ ¬ InCut high (numValue v)

/-- The number of the literal values of a run. -/
noncomputable def namedCount (values : List datatypes.DataValue) (low high : regions.Cut) : Nat :=
  (values.filter (fun v => decide (RunValue low high v))).length

/-- The number of the integers between the cuts at `low` and `high` that are no
    literal values. -/
noncomputable def freeCount (context : data_ontology.Context) (low high : Usize) : Nat :=
  runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) -
    namedCount context.values.val (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val)

/-- A node that is the individual of a literal value of the run between the
    cuts at `low` and `high`. -/
def RunNamed (context : data_ontology.Context) (J : Interpretation Object' Value') (low high : Usize)
    (y : Object') : Prop :=
  ∃ (i : Usize) (_ : i.val < context.values.val.length),
    RunValue (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) context.values.val[i.val] ∧
    J.namedIndividuals (valueIndividual i) = y

/-- What the axiom on the integers between two neighbouring cuts of different
    numbers says: when every one of them is a literal value, the integer nodes
    there are those literal values' individuals, and when fewer than the
    capacity of them are no literal values, at most that many other integer
    nodes are there at any element along `U`. -/
def GapFact (context : data_ontology.Context) (capacity : Nat) (J : Interpretation Object' Value')
    (low high : Usize) : Prop :=
  (freeCount context low high = 0 → ∀ y, InRun J low high y → RunNamed context J low high y) ∧
  (0 < freeCount context low high → freeCount context low high < capacity →
    ∀ y, J.classes thing y → AtMost (freeCount context low high)
      (fun y' => J.objectProperties dataSuper y y' ∧ InRun J low high y' ∧ ¬ RunNamed context J low high y'))

/-- What the axiom between two neighbouring cuts says: the two cuts of a
    number leave only its literal value's individual, and between cuts of
    different numbers the integers get their axiom when they are in use. -/
def BetweenFact (context : data_ontology.Context) (capacity : Nat) (J : Interpretation Object' Value')
    (low high : Usize) : Prop :=
  ((cutAt context.cuts.val low.val).value = (cutAt context.cuts.val high.val).value →
    ∀ (i : Usize) (h : i.val < context.values.val.length),
      context.values.val[i.val] = (cutAt context.cuts.val low.val).value →
      ∀ y, J.classes (cutClass low) y → ¬ J.classes (cutClass high) y →
        J.namedIndividuals (valueIndividual i) = y) ∧
  ((cutAt context.cuts.val low.val).value ≠ (cutAt context.cuts.val high.val).value →
    Used context.kinds .Integer = true → GapFact context capacity J low high)

/-- What the axioms of the chain of cuts from `position` on say. -/
def ChainFacts (context : data_ontology.Context) (capacity : Nat) (order : List Usize) (position : Nat)
    (J : Interpretation Object' Value') : Prop :=
  ∀ (p : Nat) (h : p < order.length), position ≤ p → 0 < p →
    (∀ y, J.classes (cutClass order[p]) y → J.classes (cutClass order[p - 1]) y) ∧
      BetweenFact context capacity J order[p - 1] order[p]

/-- What the axioms of every data property below `U` say. -/
def SuperFacts (context : data_ontology.Context) (index : Nat) (J : Interpretation Object' Value') : Prop :=
  ∀ (k : Nat) (h : k < context.data.val.length), index ≤ k → ∀ role,
    data_ontology.data_role context context.data.val[k] = .ok (some role) →
      ∀ y y', objectRelation J role y y' → J.objectProperties dataSuper y y'

/-- The numbers of two neighbouring cuts of the same number from `position`
    on are literal values. -/
def PointsNamed (context : data_ontology.Context) (order : List Usize) (position : Nat) : Prop :=
  ∀ (p : Nat) (h : p < order.length), position ≤ p → 0 < p →
    (cutAt context.cuts.val order[p - 1].val).value = (cutAt context.cuts.val order[p].val).value →
    (cutAt context.cuts.val order[p - 1].val).value ∈ context.values.val

/-- What the axioms of the ordered numbers say, for the kernel's order of the
    cuts. -/
def RegionFacts (context : data_ontology.Context) (capacity : Nat) (order : List Usize)
    (J : Interpretation Object' Value') : Prop :=
  context.kinds.ordered = true →
    (∀ first, order.head? = some first → ∀ y, J.classes (cutClass first) y → J.classes (kindClass .Real) y) ∧
    ChainFacts context capacity order 1 J ∧ (Used context.kinds .Integer = true → SuperFacts context 0 J)

/-! ### The literal values of a run -/

theorem integer_kind {v : datatypes.DataValue} (c : CanonicalNumeric v) :
    InKind v .Integer ↔ ∃ z : ℤ, numValue v = z := by
  cases v with
  | Number n w f =>
    simp only [InKind, Rowl.Datatypes.NumberIn, numValue]
    rw [← Rowl.Datatypes.numberOf_integer c]
    rfl
  | Fraction n a b =>
    simp only [InKind, numValue, reduceCtorEq, or_self, false_iff, not_exists]
    intro z same
    exact Rowl.Datatypes.fraction_not_decimal (negative := n) c ⟨z, 0, by rw [same]; simp⟩
  | Text t => simp [CanonicalNumeric] at c
  | Tagged t m => simp [CanonicalNumeric] at c
  | Truth b => simp [CanonicalNumeric] at c
  | Uri _ => simp [CanonicalNumeric] at c
  | Hex _ => simp [CanonicalNumeric] at c
  | Base64 _ => simp [CanonicalNumeric] at c

theorem run_value_number {low high : regions.Cut} {v : datatypes.DataValue} (run : RunValue low high v) :
    IsNumber v := by
  have := run.1
  revert this
  cases v <;> simp [InKind, IsNumber, Rowl.Strings.TextIn, Rowl.Strings.subtypeOf]

theorem run_value_integer {low high : regions.Cut} {v : datatypes.DataValue} (c : CanonicalNumeric v)
    (run : RunValue low high v) : numValue v = (⌊numValue v⌋ : ℚ) := by
  obtain ⟨z, hz⟩ := (integer_kind c).mp run.1
  rw [hz]; simp

/-- The integers of the literal values of a run. -/
noncomputable def namedIntegers (values : List datatypes.DataValue) (low high : regions.Cut) : Finset ℤ :=
  ((values.filter (fun v => decide (RunValue low high v))).map (fun v => ⌊numValue v⌋)).toFinset

/-- The integers of a run that are no literal values. -/
noncomputable def freeIntegers (values : List datatypes.DataValue) (low high : regions.Cut) : Finset ℤ :=
  Finset.Icc (firstIn low) (lastOutside high) \ namedIntegers values low high

theorem named_in_run {values : List datatypes.DataValue} (canonical : ∀ v ∈ values, IsNumber v → CanonicalNumeric v)
    {low high : regions.Cut} {z : ℤ} :
    z ∈ namedIntegers values low high ↔ ∃ v ∈ values, RunValue low high v ∧ numValue v = z := by
  simp only [namedIntegers, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨v, ⟨mem, run⟩, rfl⟩
    exact ⟨v, mem, run, run_value_integer (canonical v mem (run_value_number run)) run⟩
  · rintro ⟨v, mem, run, same⟩
    exact ⟨v, ⟨mem, run⟩, by rw [same]; simp⟩

theorem named_subset {values : List datatypes.DataValue} (canonical : ∀ v ∈ values, IsNumber v → CanonicalNumeric v)
    {low high : regions.Cut} :
    namedIntegers values low high ⊆ Finset.Icc (firstIn low) (lastOutside high) := by
  intro z mem
  obtain ⟨v, _, run, same⟩ := (named_in_run canonical).mp mem
  have zIs : ((numValue v : ℚ) : ℝ) = (z : ℝ) := by exact_mod_cast same
  rw [Finset.mem_Icc, ← Rowl.Regions.in_cuts_iff, ← zIs]
  exact ⟨run.2.1, run.2.2⟩

/-- The literal values of a run have distinct integers. -/
theorem named_card {values : List datatypes.DataValue} (nodup : values.Nodup)
    (canonical : ∀ v ∈ values, IsNumber v → CanonicalNumeric v) {low high : regions.Cut} :
    (namedIntegers values low high).card = namedCount values low high := by
  unfold namedIntegers namedCount
  rw [List.toFinset_card_of_nodup]
  · simp
  · apply List.Nodup.map_on _ (nodup.filter _)
    intro a ma b mb same
    simp only [List.mem_filter, decide_eq_true_eq] at ma mb
    have ca := canonical a ma.1 (run_value_number ma.2)
    have cb := canonical b mb.1 (run_value_number mb.2)
    apply Rowl.Regions.numValue_injective ca cb
    rw [run_value_integer ca ma.2, run_value_integer cb mb.2, same]

/-- The integers of a run that are no literal values, counted. -/
theorem free_card {values : List datatypes.DataValue} (nodup : values.Nodup)
    (canonical : ∀ v ∈ values, IsNumber v → CanonicalNumeric v) (low high : regions.Cut) :
    (freeIntegers values low high).card = runCount low high - namedCount values low high := by
  unfold freeIntegers
  rw [Finset.card_sdiff_of_subset (named_subset canonical), Int.card_Icc, named_card nodup canonical, runCount]
  congr 1
  omega

/-- When no integer of a run is free, every integer of the run is a literal
    value of the run. -/
theorem all_named {values : List datatypes.DataValue} (nodup : values.Nodup)
    (canonical : ∀ v ∈ values, IsNumber v → CanonicalNumeric v) {low high : regions.Cut}
    (none : runCount low high - namedCount values low high = 0) {z : ℤ}
    (inside : z ∈ Finset.Icc (firstIn low) (lastOutside high)) : z ∈ namedIntegers values low high := by
  have card := free_card nodup canonical low high
  rw [none, Finset.card_eq_zero] at card
  by_contra outside
  have : z ∈ freeIntegers values low high := Finset.mem_sdiff.mpr ⟨inside, outside⟩
  rw [card] at this
  exact absurd this (Finset.notMem_empty z)

/-- The reals of the numeric literal values. -/
def literalReals (values : List datatypes.DataValue) : Set ℝ :=
  {r | ∃ v ∈ values, IsNumber v ∧ r = numValue v}

theorem literal_reals_finite (values : List datatypes.DataValue) : (literalReals values).Finite := by
  apply (values.finite_toSet.image (fun v => ((numValue v : ℚ) : ℝ))).subset
  rintro r ⟨v, mem, _, rfl⟩
  exact ⟨v, mem, rfl⟩

/-- The integers of a run that are no literal values, as reals. -/
theorem free_reals {values : List datatypes.DataValue} (canonical : ∀ v ∈ values, IsNumber v → CanonicalNumeric v)
    (low high : regions.Cut) :
    {r : ℝ | (InCut low r ∧ ¬ InCut high r) ∧ (∃ z : ℤ, r = z) ∧ r ∉ literalReals values} =
      (fun z : ℤ => (z : ℝ)) '' (freeIntegers values low high : Set ℤ) := by
  ext r
  constructor
  · rintro ⟨inRun, ⟨z, rfl⟩, notLit⟩
    refine ⟨z, ?_, rfl⟩
    simp only [freeIntegers, Finset.coe_sdiff, Finset.coe_Icc, Set.mem_sdiff, Set.mem_Icc, Finset.mem_coe]
    refine ⟨(Rowl.Regions.in_cuts_iff low high z).mp inRun, fun named => notLit ?_⟩
    obtain ⟨v, mem, run, same⟩ := (named_in_run canonical).mp named
    exact ⟨v, mem, run_value_number run, by rw [same]; simp⟩
  · rintro ⟨z, mem, rfl⟩
    simp only [freeIntegers, Finset.coe_sdiff, Finset.coe_Icc, Set.mem_sdiff, Set.mem_Icc, Finset.mem_coe] at mem
    refine ⟨(Rowl.Regions.in_cuts_iff low high z).mpr mem.1, ⟨z, rfl⟩, fun ⟨v, vmem, number, same⟩ => mem.2 ?_⟩
    have cv := canonical v vmem number
    have sameR : ((numValue v : ℚ) : ℝ) = (z : ℝ) := same.symm
    have sameQ : numValue v = (z : ℚ) := by exact_mod_cast sameR
    have inRun := (Rowl.Regions.in_cuts_iff low high z).mpr mem.1
    rw [← sameR] at inRun
    exact (named_in_run canonical).mpr ⟨v, vmem, ⟨(integer_kind cv).mpr ⟨z, sameQ⟩, inRun.1, inRun.2⟩, sameQ⟩

/-! ### The kernel's region axioms -/

theorem natural_of_spec (count : Usize) :
    ∃ n, data_ontology.natural_of count = .ok n ∧ Rowl.Probes.naturalValue n = count.val := by
  rw [data_ontology.natural_of]
  by_cases zero : count = 0#usize
  · subst zero; exact ⟨.Zero, by simp, rfl⟩
  · have positive : count.val ≠ 0 := fun h => zero (UScalar.eq_of_val_eq (by simpa using h))
    obtain ⟨prev, prevRun, prevValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := count) (y := 1#usize) (by simp; omega))
    have prevIs : prev.val = count.val - 1 := by simp at prevValue; exact prevValue.1
    obtain ⟨n, run, value⟩ := natural_of_spec prev
    exact ⟨.Succ n, by simp [zero, prevRun, run], by simp [Rowl.Probes.naturalValue, value, prevIs]; omega⟩
termination_by count.val
decreasing_by simp at prevValue; omega

/-- Every index of a vector is a `Usize`. -/
theorem usize_of_index {α : Type} (l : alloc.vec.Vec α) (j : Nat) (h : j < l.val.length) : ∃ i : Usize, i.val = j := by
  have bound := l.property
  have lt : j < 2 ^ UScalarTy.Usize.numBits := by
    have := Usize.max_def
    have pos : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
    simp only [Usize.numBits] at this
    have : l.val.length ≤ Usize.max := bound
    omega
  exact ⟨Usize.ofNatCore j lt, UScalar.ofNatCore_val_eq lt⟩

theorem cutAt_val {cuts : alloc.vec.Vec regions.Cut} {i : Usize} (h : i.val < cuts.val.length) :
    cutAt cuts.val i.val = cuts.val[i.val] := Rowl.Regions.cutAt_eq _ _ h

theorem fit_widths {a b : regions.Cut} (fa : Rowl.Regions.Fit a) (fb : Rowl.Regions.Fit b) :
    Rowl.Datatypes.digitWidth a.value + Rowl.Datatypes.digitWidth b.value + 32 < Usize.max := by
  have := fa.2; have := fb.2
  have : 64 ≤ Usize.max := by scalar_tac
  omega

/-- Every number among the literal values is short enough to compare. -/
def ValuesFit (context : data_ontology.Context) : Prop :=
  ∀ v ∈ context.values.val, IsNumber v → digitWidth v < Usize.max / 8

/-- Whether a literal value is of a run. -/
theorem in_run_spec (low high : regions.Cut) (fl : Fit low) (fh : Fit high) (v : datatypes.DataValue)
    (cv : Rowl.Datatypes.Canonical v) (wv : IsNumber v → digitWidth v < Usize.max / 8) :
    data_ontology.in_run low high v = .ok (decide (RunValue low high v)) := by
  rw [data_ontology.in_run, Rowl.Datatypes.in_kind_correct v cv .Integer]
  by_cases number : IsNumber v
  · have cn := canonical_numeric cv number
    rw [Rowl.Regions.in_cut_correct low fl v cn (wv number), Rowl.Regions.in_cut_correct high fh v cn (wv number)]
    simp [RunValue, Bool.and_assoc]
  · obtain ⟨b1, run1⟩ := Rowl.Regions.in_cut_ok low fl v (fun h => absurd h number)
    obtain ⟨b2, run2⟩ := Rowl.Regions.in_cut_ok high fh v (fun h => absurd h number)
    have notInt : ¬ InKind v .Integer := by
      revert number; cases v <;> simp [InKind, IsNumber, Rowl.Strings.TextIn, Rowl.Strings.subtypeOf]
    simp [run1, run2, notInt, RunValue]

/-- The individuals of an optional list. -/
def namedList : Option (NonEmpty Individual) → List Individual
  | none => []
  | some list => list.elements

theorem add_named_spec (found : Option (NonEmpty Individual)) (a : Individual)
    (room : (namedList found).length ≤ Usize.max) :
    ∃ r, data_ontology.add_named found a = .ok r ∧ namedList r = namedList found ++ [a] := by
  unfold data_ontology.add_named
  cases found with
  | none => exact ⟨_, rfl, by simp [namedList, NonEmpty.elements, new_val]⟩
  | some list =>
    have short : list.rest.val.length < Usize.max := by
      simp [namedList, NonEmpty.elements] at room; omega
    have short' : alloc.vec.Vec.len list.rest < core.num.Usize.MAX := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]
      simpa [core.num.Usize.MAX] using short
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec list.rest a short)
    refine ⟨some { list with rest := pushed }, by simp [short', push], ?_⟩
    simp [namedList, NonEmpty.elements, contents]

/-- The individuals of the literal values of a run, from `index` on. -/
theorem run_literals_spec (context : data_ontology.Context) (good : Good context) (fit : ValuesFit context)
    (low high : regions.Cut) (fl : Fit low) (fh : Fit high) (index : Usize) (found : Option (NonEmpty Individual))
    (room : (namedList found).length ≤ index.val) :
    ∃ res, data_ontology.run_literals context low high index found = .ok res ∧ ∀ a, a ∈ namedList res ↔
      a ∈ namedList found ∨ ∃ (i : Usize) (_ : i.val < context.values.val.length), index.val ≤ i.val ∧
        RunValue low high context.values.val[i.val] ∧ a = .Named (valueIndividual i) := by
  rw [data_ontology.run_literals]
  by_cases inside : index.val < context.values.val.length
  · have lookup : context.values.index_usize index = .ok context.values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have member := List.getElem_mem inside
    have runIs := in_run_spec low high fl fh context.values.val[index.val] (good.1.1 _ member) (fit _ member)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    by_cases hit : RunValue low high context.values.val[index.val]
    · have bound : context.values.val.length ≤ Usize.max := context.values.property
      obtain ⟨o, addRun, addList⟩ := add_named_spec found (.Named (valueIndividual index)) (by omega)
      obtain ⟨res, run, members⟩ := run_literals_spec context good fit low high fl fh next o
        (by rw [addList, nextIndex]; simp; omega)
      refine ⟨res, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, runIs, hit, advance,
        value_individual_eq, addRun, run], fun a => ?_⟩
      rw [members a, addList, nextIndex]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ((old | rfl) | ⟨i, hi, later, runI, rfl⟩)
        · exact .inl old
        · exact .inr ⟨index, inside, le_rfl, hit, rfl⟩
        · exact .inr ⟨i, hi, by omega, runI, rfl⟩
      · rintro (old | ⟨i, hi, later, runI, rfl⟩)
        · exact .inl (.inl old)
        · by_cases same : i = index
          · subst same; exact .inl (.inr rfl)
          · have : i.val ≠ index.val := fun h => same (UScalar.eq_of_val_eq h)
            exact .inr ⟨i, hi, by omega, runI, rfl⟩
    · obtain ⟨res, run, members⟩ := run_literals_spec context good fit low high fl fh next found
        (by rw [nextIndex]; omega)
      refine ⟨res, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, runIs, hit, advance,
        run], fun a => ?_⟩
      rw [members a, nextIndex]
      constructor
      · rintro (old | ⟨i, hi, later, runI, rfl⟩)
        · exact .inl old
        · exact .inr ⟨i, hi, by omega, runI, rfl⟩
      · rintro (old | ⟨i, hi, later, runI, rfl⟩)
        · exact .inl old
        · by_cases same : i = index
          · subst same; exact absurd runI hit
          · have : i.val ≠ index.val := fun h => same (UScalar.eq_of_val_eq h)
            exact .inr ⟨i, hi, by omega, runI, rfl⟩
  · refine ⟨found, by simp [UScalar.lt_equiv, inside], fun a => ?_⟩
    constructor
    · exact .inl
    · rintro (old | ⟨i, hi, later, _, _⟩)
      · exact old
      · omega
termination_by context.values.val.length - index.val
decreasing_by all_goals (simp at nextValue; omega)

/-- The number of the literal values of a run, from `index` on. -/
theorem run_count_spec (context : data_ontology.Context) (good : Good context) (fit : ValuesFit context)
    (low high : regions.Cut) (fl : Fit low) (fh : Fit high) (index count : Usize)
    (room : count.val + (context.values.val.length - index.val) ≤ Usize.max) :
    ∃ r : Usize, data_ontology.run_count context low high index count = .ok r ∧
      r.val = count.val + ((context.values.val.drop index.val).filter (fun v => decide (RunValue low high v))).length := by
  rw [data_ontology.run_count]
  by_cases inside : index.val < context.values.val.length
  · have lookup : context.values.index_usize index = .ok context.values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have member := List.getElem_mem inside
    have runIs := in_run_spec low high fl fh context.values.val[index.val] (good.1.1 _ member) (fit _ member)
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    have countLt : count.val < Usize.max := by omega
    have countLt' : count < core.num.Usize.MAX := by
      simp only [UScalar.lt_equiv]; simpa [core.num.Usize.MAX] using countLt
    by_cases hit : RunValue low high context.values.val[index.val]
    · obtain ⟨more, moreRun, moreValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := count) (y := 1#usize) (by scalar_tac))
      have moreIs : more.val = count.val + 1 := by simpa using moreValue
      obtain ⟨r, run, value⟩ := run_count_spec context good fit low high fl fh next more
        (by rw [moreIs, nextIndex]; omega)
      refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, runIs, hit, countLt',
        advance, moreRun, run], ?_⟩
      rw [value, moreIs, nextIndex, split, List.filter_cons_of_pos (by simpa using hit)]
      simp only [List.length_cons]
      omega
    · obtain ⟨r, run, value⟩ := run_count_spec context good fit low high fl fh next count
        (by rw [nextIndex]; omega)
      refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, runIs, hit,
        advance, run], ?_⟩
      rw [value, nextIndex, split, List.filter_cons_of_neg (by simpa using hit)]
  · refine ⟨count, by simp [UScalar.lt_equiv, inside], ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by context.values.val.length - index.val
decreasing_by all_goals (simp at nextValue; omega)

/-- The literal values' individuals of a run, from the kernel's list. -/
theorem run_named_iff {context : data_ontology.Context} {J : Interpretation Object' Value'} {low high : Usize}
    {found : Option (NonEmpty Individual)}
    (members : ∀ a, a ∈ namedList found ↔ ∃ (i : Usize) (_ : i.val < context.values.val.length),
      RunValue (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) context.values.val[i.val] ∧
        a = .Named (valueIndividual i)) (y : Object') :
    (∃ a ∈ namedList found, individual J a = y) ↔ RunNamed context J low high y := by
  constructor
  · rintro ⟨a, mem, same⟩
    obtain ⟨i, hi, runI, rfl⟩ := (members a).mp mem
    exact ⟨i, hi, runI, same⟩
  · rintro ⟨i, hi, runI, same⟩
    exact ⟨_, (members _).mpr ⟨i, hi, runI, rfl⟩, same⟩

/-- The axiom on a run of integers that are all literal values. -/
theorem no_free_integers_spec (context : data_ontology.Context) (low high : Usize)
    (found : Option (NonEmpty Individual))
    (members : ∀ a, a ∈ namedList found ↔ ∃ (i : Usize) (_ : i.val < context.values.val.length),
      RunValue (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) context.values.val[i.val] ∧
        a = .Named (valueIndividual i)) :
    ∃ ax, data_ontology.no_free_integers low high found = .ok ax ∧
      ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        (satisfies J ax ↔ ∀ y, InRun J low high y → RunNamed context J low high y) := by
  unfold data_ontology.no_free_integers
  cases found with
  | none =>
    refine ⟨.SubClassOf (.ObjectIntersectionOf ⟨.Class (kindClass .Integer), .Class (cutClass low),
      alloc.vec.Vec.new ClassExpression⟩) (.Class (cutClass high)),
      by simp [kind_class_eq, cut_class_eq, data_ontology.and], fun J => ?_⟩
    have nothing : ∀ y, ¬ RunNamed context J low high y := fun y named =>
      by simpa [namedList] using (run_named_iff members y).mpr named
    simp only [satisfies, classDenote, new_val, AtLeastTwo.elements, InRun]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    constructor
    · intro holds y ⟨i, l, h⟩
      exact absurd (holds y ⟨i, l, by simp⟩) h
    · intro holds y ⟨i, l, _⟩
      by_contra h
      exact nothing y (holds y ⟨i, l, h⟩)
  | some list =>
    obtain ⟨rest, single, andRun⟩ := and3_eq (.Class (kindClass .Integer)) (.Class (cutClass low))
      (.ObjectComplementOf (.Class (cutClass high)))
    refine ⟨.SubClassOf (.ObjectIntersectionOf ⟨.Class (kindClass .Integer), .Class (cutClass low), rest⟩)
      (.ObjectOneOf list), by simp [kind_class_eq, cut_class_eq, data_ontology.not, andRun], fun J => ?_⟩
    have iff := run_named_iff (J := J) members
    simp only [namedList] at iff
    simp only [satisfies, classDenote, AtLeastTwo.elements, single, InRun]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp only [classDenote]
    constructor
    · intro holds y ⟨i, l, h⟩
      exact (iff y).mp (holds y ⟨i, l, h⟩)
    · intro holds y ⟨i, l, h⟩
      exact (iff y).mpr (holds y ⟨i, l, h⟩)

/-- The integers of a run that are no literal values. -/
theorem free_integers_spec (context : data_ontology.Context) (low high : Usize)
    (found : Option (NonEmpty Individual))
    (members : ∀ a, a ∈ namedList found ↔ ∃ (i : Usize) (_ : i.val < context.values.val.length),
      RunValue (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) context.values.val[i.val] ∧
        a = .Named (valueIndividual i)) :
    ∃ c, data_ontology.free_integers low high found = .ok c ∧
      ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') (y : Object'),
        (classDenote J c y ↔ InRun J low high y ∧ ¬ RunNamed context J low high y) := by
  unfold data_ontology.free_integers
  obtain ⟨rest, single, andRun⟩ := and3_eq (.Class (kindClass .Integer)) (.Class (cutClass low))
    (.ObjectComplementOf (.Class (cutClass high)))
  cases found with
  | none =>
    refine ⟨.ObjectIntersectionOf ⟨.Class (kindClass .Integer), .Class (cutClass low), rest⟩,
      by simp [kind_class_eq, cut_class_eq, data_ontology.not, andRun], fun J y => ?_⟩
    have nothing : ¬ RunNamed context J low high y := fun named =>
      by simpa [namedList] using (run_named_iff members y).mpr named
    simp [classDenote, AtLeastTwo.elements, single, InRun, nothing]
  | some list =>
    refine ⟨.ObjectIntersectionOf ⟨.ObjectIntersectionOf ⟨.Class (kindClass .Integer), .Class (cutClass low), rest⟩,
      .ObjectComplementOf (.ObjectOneOf list), alloc.vec.Vec.new ClassExpression⟩,
      by simp [kind_class_eq, cut_class_eq, data_ontology.not, andRun, data_ontology.and], fun J y => ?_⟩
    have iff := run_named_iff (J := J) members y
    simp only [namedList] at iff
    simp only [classDenote, AtLeastTwo.elements, single, new_val, InRun, ← iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.forall_mem_cons,
      List.forall_mem_nil, and_true, classDenote]
    tauto

/-- The axiom on the integers between two neighbouring cuts of different
    numbers. -/
theorem gap_axiom_spec (context : data_ontology.Context) (good : Good context) (fine : FineCuts context.cuts.val)
    (fit : ValuesFit context) (low high : Usize)
    (hl : low.val < context.cuts.val.length) (hh : high.val < context.cuts.val.length) (capacity : Usize)
    (capSmall : capacity.val < Usize.max / 16) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.gap_axiom context low high capacity out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ GapFact context capacity.val J low high) := by
  rw [data_ontology.gap_axiom]
  have lookupL : context.cuts.index_usize low = .ok context.cuts.val[low.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hl]
  have lookupH : context.cuts.index_usize high = .ok context.cuts.val[high.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hh]
  have fl := Rowl.Regions.fine_at fine hl
  have fh := Rowl.Regions.fine_at fine hh
  rw [cutAt_val hl] at fl
  rw [cutAt_val hh] at fh
  obtain ⟨q, qRun, qValue⟩ := WP.spec_imp_exists (Usize.div_spec core.num.Usize.MAX (y := 16#usize) (by simp))
  have qIs : q.val = Usize.max / 16 := by rw [qValue]; simp [core.num.Usize.MAX]
  have capLtVal : capacity.val < q.val := by rw [qIs]; exact capSmall
  have bound : context.values.val.length ≤ Usize.max := context.values.property
  obtain ⟨named, namedRun, namedValue⟩ := run_count_spec context good fit context.cuts.val[low.val]
    context.cuts.val[high.val] fl fh 0#usize 0#usize (by simp only [zero_val, Nat.zero_add, Nat.sub_zero]; exact bound)
  have namedIs : named.val = namedCount context.values.val (cutAt context.cuts.val low.val)
      (cutAt context.cuts.val high.val) := by
    rw [namedValue, cutAt_val hl, cutAt_val hh]; simp [namedCount]
  have freeIs : freeCount context low high =
      runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) - named.val := by
    rw [freeCount, namedIs]
  obtain ⟨room, roomRun, roomValue⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := q) (y := capacity) (by omega))
  have roomIs : room.val = q.val - capacity.val := by simpa using roomValue.1
  by_cases namedSmall : named.val < room.val
  · obtain ⟨cap1, capRun, capValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := capacity) (y := 1#usize) (by have := Usize.max_def; scalar_tac))
    have cap1Is : cap1.val = capacity.val + 1 := by simpa using capValue
    have sixteen : 16 ≤ Usize.max := by scalar_tac
    obtain ⟨cap2, cap2Run, cap2Value⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := cap1) (y := named) (by rw [cap1Is]; omega))
    have cap2Is : cap2.val = capacity.val + 1 + named.val := by rw [← cap1Is]; simpa using cap2Value
    obtain ⟨size, sizeRun, sizeValue⟩ := Rowl.Regions.run_size_spec context.cuts.val[low.val]
      context.cuts.val[high.val] fl.1 fh.1 (fit_widths fl fh) cap2 (by rw [cap2Is]; omega)
    have sizeIs : size.val = min (runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val))
        (capacity.val + 1 + named.val) := by
      rw [sizeValue, cutAt_val hl, cutAt_val hh, cap2Is]; rfl
    by_cases enough : named.val ≤ size.val
    · obtain ⟨free, freeRun, freeValue⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := size) (y := named) (by scalar_tac))
      have freeVal : free.val = size.val - named.val := by simpa using freeValue.1
      obtain ⟨found, foundRun, members0⟩ := run_literals_spec context good fit context.cuts.val[low.val]
        context.cuts.val[high.val] fl fh 0#usize none (by simp [namedList])
      have members : ∀ a, a ∈ namedList found ↔ ∃ (i : Usize) (_ : i.val < context.values.val.length),
          RunValue (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) context.values.val[i.val] ∧
            a = .Named (valueIndividual i) := by
        intro a
        rw [members0 a, cutAt_val hl, cutAt_val hh]
        simp [namedList]
      by_cases zero : free.val = 0
      · have zero' : free = 0#usize := UScalar.eq_of_val_eq (by simpa using zero)
        have none : freeCount context low high = 0 := by rw [freeIs]; omega
        obtain ⟨ax, axRun, axMeans⟩ := no_free_integers_spec context low high found members
        obtain ⟨r, run, contents⟩ := push_spec out ax
        refine ⟨r, by simp [UScalar.lt_equiv, UScalar.le_equiv, alloc.vec.Vec.len_val, hl, hh, qRun, capLtVal,
          alloc.vec.Vec.index_slice_index, lookupL, lookupH, namedRun, roomRun, namedSmall, capRun, cap2Run,
          sizeRun, enough, freeRun, foundRun, zero', axRun, run], fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
        simp only [List.mem_singleton, forall_eq, GapFact, none, lt_irrefl, false_imp_iff, implies_true,
          and_true, true_implies]
        exact axMeans J
      · have zero' : free ≠ 0#usize := fun h => zero (by rw [h]; rfl)
        by_cases fewer : free.val < capacity.val
        · have exact : freeCount context low high = free.val := by rw [freeIs]; omega
          obtain ⟨n, nRun, nValue⟩ := natural_of_spec free
          obtain ⟨ce, ceRun, ceMeans⟩ := free_integers_spec context low high found members
          obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.Class thing)
            (.ObjectMaxCardinality n (.Property dataSuper) (some ce)))
          refine ⟨r, by simp [UScalar.lt_equiv, UScalar.le_equiv, alloc.vec.Vec.len_val, hl, hh, qRun, capLtVal,
            alloc.vec.Vec.index_slice_index, lookupL, lookupH, namedRun, roomRun, namedSmall, capRun, cap2Run,
            sizeRun, enough, freeRun, foundRun, zero', fewer, thing_eq, nRun, data_super_eq, ceRun, run],
            fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
          rw [GapFact, exact]
          simp only [List.mem_singleton, forall_eq, satisfies, zero, false_imp_iff, true_and, fewer,
            Nat.pos_of_ne_zero zero, true_implies]
          have eq : ∀ y y', (J.objectProperties dataSuper y y' ∧ classDenote J ce y') ↔
              (J.objectProperties dataSuper y y' ∧ InRun J low high y' ∧ ¬ RunNamed context J low high y') :=
            fun y y' => and_congr Iff.rfl (ceMeans J y')
          simp only [classDenote, objectRelation, nValue, eq]
        · refine ⟨some out, by simp [UScalar.lt_equiv, UScalar.le_equiv, alloc.vec.Vec.len_val, hl, hh, qRun,
            capLtVal, alloc.vec.Vec.index_slice_index, lookupL, lookupH, namedRun, roomRun, namedSmall, capRun,
            cap2Run, sizeRun, enough, freeRun, foundRun, zero', fewer], fun out' h => ⟨[], by cases h; simp,
            fun J => ?_⟩⟩
          have many : capacity.val ≤ freeCount context low high := by rw [freeIs]; omega
          have notZero : freeCount context low high ≠ 0 := by omega
          simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, GapFact, notZero, false_imp_iff,
            true_and]
          intro _ lt
          omega
    · exact ⟨none, by simp [UScalar.lt_equiv, UScalar.le_equiv, alloc.vec.Vec.len_val, hl, hh, qRun, capLtVal,
        alloc.vec.Vec.index_slice_index, lookupL, lookupH, namedRun, roomRun, namedSmall, capRun, cap2Run, sizeRun,
        enough], by simp⟩
  · exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, hl, hh, qRun, capLtVal,
      alloc.vec.Vec.index_slice_index, lookupL, lookupH, namedRun, roomRun, namedSmall], by simp⟩

theorem index_unique {values : List datatypes.DataValue} (nodup : values.Nodup) {i j : Nat}
    (hi : i < values.length) (hj : j < values.length) (same : values[i] = values[j]) : i = j :=
  (List.Nodup.getElem_inj_iff nodup).mp same

/-- The axiom between two neighbouring cuts. -/
theorem between_axiom_spec (context : data_ontology.Context) (good : Good context) (fine : FineCuts context.cuts.val)
    (fit : ValuesFit context) (low high : Usize) (hl : low.val < context.cuts.val.length) (hh : high.val < context.cuts.val.length)
    (capacity : Usize) (capSmall : capacity.val < Usize.max / 16) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.between_axiom context low high capacity out = .ok res ∧ ∀ out', res = some out' →
      ((cutAt context.cuts.val low.val).value = (cutAt context.cuts.val high.val).value →
        (cutAt context.cuts.val low.val).value ∈ context.values.val) ∧
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ BetweenFact context capacity.val J low high) := by
  rw [data_ontology.between_axiom]
  have lookupL : context.cuts.index_usize low = .ok context.cuts.val[low.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hl]
  have lookupH : context.cuts.index_usize high = .ok context.cuts.val[high.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hh]
  have cl := cutAt_val hl
  have ch := cutAt_val hh
  by_cases same : context.cuts.val[low.val].value = context.cuts.val[high.val].value
  · obtain ⟨o, oRun, absent, found⟩ := value_index_correct context.values context.cuts.val[high.val].value 0#usize
    cases o with
    | none =>
      exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, hl, hh, alloc.vec.Vec.index_slice_index,
        lookupL, lookupH, Rowl.Datatypes.same_value_correct, same, oRun], by simp⟩
    | some i =>
      obtain ⟨hi, at_i⟩ := found i rfl
      obtain ⟨a, aRun, aName⟩ := value_individual_correct i
      obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.ObjectIntersectionOf ⟨.Class (cutClass low),
        .ObjectComplementOf (.Class (cutClass high)), alloc.vec.Vec.new ClassExpression⟩)
        (.ObjectOneOf ⟨.Named (valueIndividual i), alloc.vec.Vec.new Individual⟩))
      have member : context.cuts.val[high.val].value ∈ context.values.val := at_i ▸ List.getElem_mem hi
      refine ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, hl, hh, alloc.vec.Vec.index_slice_index,
        lookupL, lookupH, Rowl.Datatypes.same_value_correct, same, oRun, cut_class_eq, data_ontology.not,
        data_ontology.and, value_individual_eq, run], fun out' h =>
        ⟨fun _ => by rw [cl, same]; exact member, _, contents out' h, fun J => ?_⟩⟩
      simp only [List.mem_singleton, forall_eq, satisfies, classDenote, new_val, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, BetweenFact, cl, ch, same, ne_eq, not_true_eq_false, false_imp_iff, and_true,
        true_implies, NonEmpty.elements, List.mem_cons, exists_eq_or_imp, exists_eq_left, List.not_mem_nil,
        or_false, individual]
      constructor
      · intro holds i' hi' at_i' y inLow notHigh
        have : i' = i := UScalar.eq_of_val_eq (index_unique good.1.2 hi' hi (at_i'.trans at_i.symm))
        subst this
        exact holds y ⟨inLow, notHigh⟩
      · intro holds y ⟨inLow, notHigh⟩
        exact holds i hi at_i y inLow notHigh
  · have differ : ¬ (cutAt context.cuts.val low.val).value = (cutAt context.cuts.val high.val).value := by
      rw [cl, ch]; exact same
    by_cases integer : context.kinds.integer = true
    · obtain ⟨r, run, facts⟩ := gap_axiom_spec context good fine fit low high hl hh capacity capSmall out
      refine ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, hl, hh, alloc.vec.Vec.index_slice_index,
        lookupL, lookupH, Rowl.Datatypes.same_value_correct, same, integer, run], fun out' h => ?_⟩
      obtain ⟨new, c, m⟩ := facts out' h
      refine ⟨fun e => absurd e differ, new, c, fun J => ?_⟩
      rw [m J]
      simp [BetweenFact, differ, Used, integer]
    · refine ⟨some out, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, hl, hh, alloc.vec.Vec.index_slice_index,
        lookupL, lookupH, Rowl.Datatypes.same_value_correct, same, integer], fun out' h =>
        ⟨fun e => absurd e differ, [], by cases h; simp, fun J => ?_⟩⟩
      simp [BetweenFact, differ, Used, integer]

/-- The axioms of the chain of cuts from `position` on. -/
theorem chain_axioms_spec (context : data_ontology.Context) (good : Good context) (fine : FineCuts context.cuts.val)
    (fit : ValuesFit context) (order : alloc.vec.Vec Usize) (orderIn : ∀ k ∈ order.val, k.val < context.cuts.val.length) (position : Usize)
    (positive : 0 < position.val) (capacity : Usize) (capSmall : capacity.val < Usize.max / 16)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.chain_axioms context order position capacity out = .ok res ∧ ∀ out', res = some out' →
      PointsNamed context order.val position.val ∧
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ ChainFacts context capacity.val order.val position.val J) := by
  rw [data_ontology.chain_axioms]
  by_cases inside : position.val < order.val.length
  · obtain ⟨prev, prevRun, prevValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := position) (y := 1#usize) (by simp; omega))
    have prevIs : prev.val = position.val - 1 := by simp at prevValue; exact prevValue.1
    have prevIn : prev.val < order.val.length := by omega
    have lookupP : order.index_usize prev = .ok order.val[prev.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem prevIn]
    have lookupH : order.index_usize position = .ok order.val[position.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have hl := orderIn _ (List.getElem_mem prevIn)
    have hh := orderIn _ (List.getElem_mem inside)
    obtain ⟨r1, run1, contents1⟩ := push_spec out (.SubClassOf (.Class (cutClass order.val[position.val]))
      (.Class (cutClass order.val[prev.val])))
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, positive, inside, prevRun,
        alloc.vec.Vec.index_slice_index, lookupP, lookupH, cut_class_eq, run1], by simp⟩
    | some o1 =>
      obtain ⟨r2, run2, facts2⟩ := between_axiom_spec context good fine fit order.val[prev.val] order.val[position.val]
        hl hh capacity capSmall o1
      cases r2 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, positive, inside, prevRun,
          alloc.vec.Vec.index_slice_index, lookupP, lookupH, cut_class_eq, run1, run2], by simp⟩
      | some o2 =>
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := position) (y := 1#usize) (by scalar_tac))
        have nextIndex : next.val = position.val + 1 := by simpa using nextValue
        obtain ⟨r3, run3, facts3⟩ := chain_axioms_spec context good fine fit order orderIn next (by omega) capacity
          capSmall o2
        refine ⟨r3, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, positive, inside, prevRun,
          alloc.vec.Vec.index_slice_index, lookupP, lookupH, cut_class_eq, run1, run2, advance, run3],
          fun out' h => ?_⟩
        obtain ⟨named2, n2, c2, m2⟩ := facts2 o2 rfl
        obtain ⟨named3, n3, c3, m3⟩ := facts3 out' h
        have prevEq' : order.val[position.val - 1] = order.val[prev.val] := by simp [prevIs]
        refine ⟨fun p hp low pos same => ?_, bare (.SubClassOf (.Class (cutClass order.val[position.val]))
          (.Class (cutClass order.val[prev.val]))) :: (n2 ++ n3), by rw [c3, c2, contents1 o1 rfl]; simp [bare],
          fun J => ?_⟩
        · by_cases here : p = position.val
          · subst here
            rw [prevEq'] at same ⊢
            exact named2 same
          · exact named3 p hp (by omega) pos same
        simp only [List.mem_cons, forall_eq_or_imp, List.forall_mem_append]
        rw [m2 J, m3 J, nextIndex]
        simp only [bare, satisfies, classDenote]
        have prevEq : order.val[position.val - 1] = order.val[prev.val] := by simp [prevIs]
        constructor
        · rintro ⟨sub, between, rest⟩ p hp low pos
          by_cases here : p = position.val
          · subst here
            rw [prevEq]
            exact ⟨sub, between⟩
          · exact rest p hp (by omega) pos
        · intro all
          have here := all position.val inside le_rfl positive
          rw [prevEq] at here
          exact ⟨here.1, here.2, fun p hp low pos => all p hp (by omega) pos⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, positive, inside], fun out' h =>
      ⟨fun p hp low => by omega, [], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    intro p hp low
    omega
termination_by order.val.length - position.val
decreasing_by omega

/-- The axioms of the data properties of `context.data[index..]` below `U`. -/
theorem super_axioms_spec (context : data_ontology.Context) (index : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.super_axioms context index out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ SuperFacts context index.val J) := by
  rw [data_ontology.super_axioms]
  by_cases inside : index.val < context.data.val.length
  · have lookup : context.data.index_usize index = .ok context.data.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨role, roleRun, _⟩ := data_role_correct context context.data.val[index.val]
    cases role with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, roleRun], by
        simp⟩
    | some role =>
      obtain ⟨r1, run1, contents1⟩ := push_spec out (.SubObjectPropertyOf (.Single role) (.Property dataSuper))
      cases r1 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, roleRun,
          data_super_eq, run1], by simp⟩
      | some o1 =>
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIndex : next.val = index.val + 1 := by simpa using nextValue
        obtain ⟨r2, run2, facts2⟩ := super_axioms_spec context next o1
        refine ⟨r2, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, roleRun,
          data_super_eq, run1, advance, run2], fun out' h => ?_⟩
        obtain ⟨n2, c2, m2⟩ := facts2 out' h
        refine ⟨bare (.SubObjectPropertyOf (.Single role) (.Property dataSuper)) :: n2,
          by rw [c2, contents1 o1 rfl]; simp [bare], fun J => ?_⟩
        simp only [List.mem_cons, forall_eq_or_imp]
        rw [m2 J, nextIndex]
        simp only [bare, satisfies, subRelation, objectRelation]
        constructor
        · rintro ⟨here, rest⟩ k hk low role' run' y y' rel
          by_cases same : k = index.val
          · subst same
            rw [roleRun] at run'
            cases Result.ok_injective run'
            exact here y y' rel
          · exact rest k hk (by omega) role' run' y y' rel
        · intro all
          exact ⟨fun y y' rel => all index.val inside le_rfl role roleRun y y' rel,
            fun k hk low role' run' y y' rel => all k hk (by omega) role' run' y y' rel⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    intro k hk low
    omega
termination_by context.data.val.length - index.val
decreasing_by omega

/-- The axiom of the first cut. -/
theorem least_axiom_spec (order : alloc.vec.Vec Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.least_axiom order out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ first, order.val.head? = some first → ∀ y,
          J.classes (cutClass first) y → J.classes (kindClass .Real) y) := by
  rw [data_ontology.least_axiom]
  by_cases nonempty : 0 < order.val.length
  · have lookup : order.index_usize 0#usize = .ok order.val[0] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem nonempty]
    obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.Class (cutClass order.val[0]))
      (.Class (kindClass .Real)))
    refine ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, nonempty, alloc.vec.Vec.index_slice_index, lookup,
      cut_class_eq, kind_class_eq, run], fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
    simp only [List.mem_singleton, forall_eq, satisfies, classDenote]
    have head : order.val.head? = some order.val[0] := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem nonempty]
    rw [head]
    simp
  · refine ⟨some out, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, nonempty], fun out' h =>
      ⟨[], by cases h; simp, fun J => ?_⟩⟩
    have : order.val = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [this]

/-- Whether a literal value is no number or a number short enough to compare. -/
theorem value_fits_spec (v : datatypes.DataValue) (cv : IsNumber v → CanonicalNumeric v) :
    ∃ b, data_ontology.value_fits v = .ok b ∧ (b = true → IsNumber v → digitWidth v < Usize.max / 8) := by
  rw [data_ontology.value_fits, Rowl.Datatypes.numeric_correct]
  by_cases number : IsNumber v
  · obtain ⟨b, run, facts⟩ := Rowl.Regions.fits_spec v cv
    exact ⟨b, by simp [number, run], fun h _ => (facts h).2⟩
  · exact ⟨true, by simp [number], fun _ h => absurd h number⟩

theorem values_fit_spec (context : data_ontology.Context) (good : Good context) (index : Usize) :
    ∃ b, data_ontology.values_fit context index = .ok b ∧ (b = true → ∀ (i : Nat) (h : i < context.values.val.length),
      index.val ≤ i → IsNumber context.values.val[i] → digitWidth context.values.val[i] < Usize.max / 8) := by
  rw [data_ontology.values_fit]
  by_cases inside : index.val < context.values.val.length
  · have lookup : context.values.index_usize index = .ok context.values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨rest, restRun, restFacts⟩ := values_fit_spec context good next
    obtain ⟨b, run, facts⟩ := value_fits_spec context.values.val[index.val]
      (fun number => canonical_numeric (good.1.1 _ (List.getElem_mem inside)) number)
    cases b with
    | false => exact ⟨false, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run],
        by simp⟩
    | true =>
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance,
        restRun], fun hr i hi low number => ?_⟩
      by_cases here : i = index.val
      · subst here; exact facts rfl number
      · exact restFacts hr i hi (by omega) number
  · exact ⟨true, by simp [UScalar.lt_equiv, inside], fun _ i hi low => by omega⟩
termination_by context.values.val.length - index.val
decreasing_by omega

/-- When the kernel finds the context encodable, its cuts can be ordered and
    every number among its literal values can be compared. -/
theorem encodable_spec (context : data_ontology.Context) (good : Good context) :
    ∃ b, data_ontology.encodable context = .ok b ∧ (b = true → FineCuts context.cuts.val ∧ ValuesFit context) := by
  rw [data_ontology.encodable]
  obtain ⟨f, fRun, fFacts⟩ := Rowl.Regions.cuts_fit_spec context.cuts 0#usize
    (fun c m _ => good.2.2.2.1.1 c m)
  obtain ⟨v, vRun, vFacts⟩ := values_fit_spec context good 0#usize
  refine ⟨f && v, by simp [fRun, vRun], fun both => ?_⟩
  simp only [Bool.and_eq_true] at both
  refine ⟨⟨fun c m => ?_, good.2.2.2.1.2⟩, fun w m number => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem m
    exact fFacts both.1 j (by simp) hj
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem m
    exact vFacts both.2 i hi (by simp) number

/-- The axioms of the ordered numbers: when numbers are ordered, the kernel
    lists the cuts in order and adds the axioms of `RegionFacts` for that
    order. -/
theorem region_axioms_spec (context : data_ontology.Context) (good : Good context)
    (fine : FineCuts context.cuts.val) (fit : ValuesFit context) (capacity : Usize) (capSmall : capacity.val < Usize.max / 16)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.region_axioms context capacity out = .ok res ∧ ∀ out', res = some out' →
      ∃ order : List Usize, (context.kinds.ordered = true → Ordered context.cuts.val (order.map (·.val)) ∧
          PointsNamed context order 1) ∧
        ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ RegionFacts context capacity.val order J) := by
  rw [data_ontology.region_axioms]
  by_cases ordered : context.kinds.ordered = true
  · obtain ⟨order, orderRun, sorted⟩ := Rowl.Regions.cut_order_spec context.cuts fine
    have orderIn : ∀ k ∈ order.val, k.val < context.cuts.val.length := fun k m =>
      sorted.2.1 k.val (List.mem_map_of_mem m)
    obtain ⟨r1, run1, facts1⟩ := least_axiom_spec order out
    cases r1 with
    | none => exact ⟨none, by simp [ordered, orderRun, run1], by simp⟩
    | some o1 =>
      obtain ⟨r2, run2, facts2⟩ := chain_axioms_spec context good fine fit order orderIn 1#usize (by simp) capacity
        capSmall o1
      cases r2 with
      | none => exact ⟨none, by simp [ordered, orderRun, run1, run2], by simp⟩
      | some o2 =>
        obtain ⟨n1, c1, m1⟩ := facts1 o1 rfl
        obtain ⟨named, n2, c2, m2⟩ := facts2 o2 rfl
        by_cases integer : context.kinds.integer = true
        · obtain ⟨r3, run3, facts3⟩ := super_axioms_spec context 0#usize o2
          refine ⟨r3, by simp [ordered, orderRun, run1, run2, integer, run3], fun out' h => ?_⟩
          obtain ⟨n3, c3, m3⟩ := facts3 out' h
          refine ⟨order.val, fun _ => ⟨sorted, named⟩, n1 ++ n2 ++ n3, by rw [c3, c2, c1]; simp, fun J => ?_⟩
          simp only [List.forall_mem_append]
          rw [m1 J, m2 J, m3 J]
          simp [RegionFacts, ordered, Used, integer, and_assoc]
        · refine ⟨some o2, by simp [ordered, orderRun, run1, run2, integer], fun out' h => ?_⟩
          cases h
          refine ⟨order.val, fun _ => ⟨sorted, named⟩, n1 ++ n2, by rw [c2, c1]; simp, fun J => ?_⟩
          simp only [List.forall_mem_append]
          rw [m1 J, m2 J]
          simp [RegionFacts, ordered, Used, integer]
  · refine ⟨some out, by simp [ordered], fun out' h => ⟨[], by simp [ordered], [], by cases h; simp, fun J => ?_⟩⟩
    simp [RegionFacts, ordered]

end Rowl.DataRegions
