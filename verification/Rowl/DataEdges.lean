import Rowl.DataRegions

/-!
The axioms that `data_ontology` adds for the values of `xsd:double` and
`xsd:float` in use (`binary_axioms`, `edge_memberships`). The places of the
values of a format (`Rowl.FloatOrder.position`) where the range facets of the
context begin or end are its edges, each with a class of the values at or above
it. The kernel puts the class of each edge inside the class of every other edge
at or below it, the class of a lowest edge inside the format's class, every
literal value of the format in the classes of the edges at or below its place
and outside the others (`EdgeFact`), and, for each slot of places between two
neighbouring edges, below the lowest edge and from the highest on, the values
of the format there that are no literal values (`slotFree`, counted exactly):
none at all, or at most their number at any element along `U` when there are
fewer of them than the capacity (`SlotFact`, `EdgeFacts`). A format in use
without edges is a single slot. Places past the last value count as the end.
-/
namespace Rowl.DataEdges
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.DataRegions (namedList add_named_spec natural_of_spec)
open Rowl.Datatypes (Canonical)
open Rowl.Floats (CanonicalBinary binaryOf fmt)
open Rowl.FloatOrder (position topPlace)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe w x

variable {Object' : Type w} {Value' : Type x}

/-! ### Places of literal values -/

/-- The place of a literal value of a format, if it is one. -/
noncomputable def formatPlace (v : datatypes.DataValue) (double : Bool) : Option ℕ :=
  match v, double with
  | .Double b, true => some (position (fmt true) (binaryOf b))
  | .Float b, false => some (position (fmt false) (binaryOf b))
  | _, _ => none

theorem format_place_spec (v : datatypes.DataValue) (double : Bool) (c : Canonical v) :
    ∃ r, data_ontology.format_place v double = .ok r ∧ r.map (·.val) = formatPlace v double := by
  cases v with
  | Double b =>
    cases double
    · exact ⟨none, by simp [data_ontology.format_place], rfl⟩
    · obtain ⟨p, run, value⟩ := Rowl.FloatOrder.position_spec b true c.1 c.2
      exact ⟨some p, by simp [data_ontology.format_place, run], by simp [formatPlace, value]⟩
  | Float b =>
    cases double
    · obtain ⟨p, run, value⟩ := Rowl.FloatOrder.position_spec b false c.1 c.2
      exact ⟨some p, by simp [data_ontology.format_place, run], by simp [formatPlace, value]⟩
    · exact ⟨none, by simp [data_ontology.format_place], rfl⟩
  | _ => exact ⟨none, by simp [data_ontology.format_place], by cases double <;> rfl⟩

theorem format_place_lit (double : Bool) (b : datatypes.Binary) :
    formatPlace (floatLit double b) double = some (position (fmt double) (binaryOf b)) := by
  cases double <;> rfl

theorem format_place_some {v : datatypes.DataValue} {double : Bool} {n : ℕ} (h : formatPlace v double = some n) :
    ∃ b, v = floatLit double b ∧ n = position (fmt double) (binaryOf b) := by
  cases v <;> cases double <;> simp_all [formatPlace, floatLit]

/-- A literal value of the format with its place from `lo` on and before
    `hi`. -/
def InSlot (double : Bool) (lo hi : ℕ) (v : datatypes.DataValue) : Prop :=
  ∃ n, formatPlace v double = some n ∧ lo ≤ n ∧ n < hi

theorem in_slot_spec (v : datatypes.DataValue) (double : Bool) (c : Canonical v) (lo hi : U128) :
    data_ontology.in_slot v double lo hi = .ok (decide (InSlot double lo.val hi.val v)) := by
  obtain ⟨r, run, value⟩ := format_place_spec v double c
  rw [data_ontology.in_slot, run]
  cases r with
  | none =>
    simp only [Option.map_none] at value
    simp [InSlot, ← value]
  | some p =>
    simp only [Option.map_some] at value
    simp [InSlot, ← value, UScalar.le_equiv, UScalar.lt_equiv]

/-- The number of the literal values of a format in a slot. -/
noncomputable def slotNamedCount (values : List datatypes.DataValue) (double : Bool) (lo hi : ℕ) : ℕ :=
  (values.filter (fun v => decide (InSlot double lo hi v))).length

theorem slot_count_spec (context : data_ontology.Context) (good : Good context) (double : Bool) (lo hi : U128)
    (index : Usize) (count : U128) (room : count.val + (context.values.val.length - index.val) < 2 ^ 128 - 1) :
    ∃ r : U128, data_ontology.slot_count context double lo hi index count = .ok r ∧
      r.val = count.val + slotNamedCount (context.values.val.drop index.val) double lo.val hi.val := by
  rw [data_ontology.slot_count]
  by_cases inside : index.val < context.values.val.length
  · have lookup : context.values.index_usize index = .ok context.values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have member := List.getElem_mem inside
    have slotIs := in_slot_spec context.values.val[index.val] double (good.1.1 _ member) lo hi
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    have countLt : count < core.num.U128.MAX := by
      rw [UScalar.lt_equiv, Rowl.Floats.u128_max_val]; omega
    by_cases hit : InSlot double lo.val hi.val context.values.val[index.val]
    · obtain ⟨c1, c1Run, c1Val⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := count) (y := 1#u128) (by simp [UScalar.max, U128.max_eq]; omega))
      have c1Is : c1.val = count.val + 1 := by simpa using c1Val
      obtain ⟨r, run, value⟩ := slot_count_spec context good double lo hi next c1 (by rw [c1Is, nextIndex]; omega)
      refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, slotIs, hit, countLt,
        advance, c1Run, run], ?_⟩
      rw [value, c1Is, nextIndex, split]
      simp only [slotNamedCount, List.filter_cons, hit, decide_true, ↓reduceIte, List.length_cons]
      omega
    · obtain ⟨r, run, value⟩ := slot_count_spec context good double lo hi next count (by rw [nextIndex]; omega)
      refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, slotIs, hit, advance,
        run], ?_⟩
      rw [value, nextIndex, split]
      simp only [slotNamedCount, List.filter_cons, hit, decide_false, Bool.false_eq_true, ↓reduceIte]
  · refine ⟨count, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show context.values.val.length ≤ index.val by omega), slotNamedCount]
termination_by context.values.val.length - index.val
decreasing_by all_goals (simp at nextValue; omega)

/-- A node that is the individual of a literal value of the format in a
    slot. -/
def SlotNamed (context : data_ontology.Context) (J : Interpretation Object' Value') (double : Bool) (lo hi : ℕ)
    (y : Object') : Prop :=
  ∃ (i : Usize) (_ : i.val < context.values.val.length), InSlot double lo hi context.values.val[i.val] ∧
    J.namedIndividuals (valueIndividual i) = y

/-- The individuals of the literal values of a slot, from `index` on. -/
theorem slot_literals_spec (context : data_ontology.Context) (good : Good context) (double : Bool) (lo hi : U128)
    (index : Usize) (found : Option (NonEmpty Individual)) (room : (namedList found).length ≤ index.val) :
    ∃ res, data_ontology.slot_literals context double lo hi index found = .ok res ∧ ∀ a, a ∈ namedList res ↔
      a ∈ namedList found ∨ ∃ (i : Usize) (_ : i.val < context.values.val.length), index.val ≤ i.val ∧
        InSlot double lo.val hi.val context.values.val[i.val] ∧ a = .Named (valueIndividual i) := by
  rw [data_ontology.slot_literals]
  by_cases inside : index.val < context.values.val.length
  · have lookup : context.values.index_usize index = .ok context.values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have member := List.getElem_mem inside
    have slotIs := in_slot_spec context.values.val[index.val] double (good.1.1 _ member) lo hi
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    by_cases hit : InSlot double lo.val hi.val context.values.val[index.val]
    · have bound : context.values.val.length ≤ Usize.max := context.values.property
      obtain ⟨o, addRun, addList⟩ := add_named_spec found (.Named (valueIndividual index)) (by omega)
      obtain ⟨res, run, members⟩ := slot_literals_spec context good double lo hi next o
        (by rw [addList, nextIndex]; simp; omega)
      refine ⟨res, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, slotIs, hit, advance,
        value_individual_eq, addRun, run], fun a => ?_⟩
      rw [members a, addList, nextIndex]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ((old | rfl) | ⟨i, hi, later, slotI, rfl⟩)
        · exact .inl old
        · exact .inr ⟨index, inside, le_rfl, hit, rfl⟩
        · exact .inr ⟨i, hi, by omega, slotI, rfl⟩
      · rintro (old | ⟨i, hi, later, slotI, rfl⟩)
        · exact .inl (.inl old)
        · by_cases same : i = index
          · subst same; exact .inl (.inr rfl)
          · have : i.val ≠ index.val := fun h => same (UScalar.eq_of_val_eq h)
            exact .inr ⟨i, hi, by omega, slotI, rfl⟩
    · obtain ⟨res, run, members⟩ := slot_literals_spec context good double lo hi next found
        (by rw [nextIndex]; omega)
      refine ⟨res, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, slotIs, hit, advance,
        run], fun a => ?_⟩
      rw [members a, nextIndex]
      constructor
      · rintro (old | ⟨i, hi, later, slotI, rfl⟩)
        · exact .inl old
        · exact .inr ⟨i, hi, by omega, slotI, rfl⟩
      · rintro (old | ⟨i, hi, later, slotI, rfl⟩)
        · exact .inl old
        · by_cases same : i = index
          · subst same; exact absurd slotI hit
          · have : i.val ≠ index.val := fun h => same (UScalar.eq_of_val_eq h)
            exact .inr ⟨i, hi, by omega, slotI, rfl⟩
  · refine ⟨found, by simp [UScalar.lt_equiv, inside], fun a => ?_⟩
    constructor
    · exact .inl
    · rintro (old | ⟨i, hi, later, _, _⟩)
      · exact old
      · omega
termination_by context.values.val.length - index.val
decreasing_by all_goals (simp at nextValue; omega)

theorem slot_named_iff {context : data_ontology.Context} {J : Interpretation Object' Value'} {double : Bool}
    {lo hi : ℕ} {found : Option (NonEmpty Individual)}
    (members : ∀ a, a ∈ namedList found ↔ ∃ (i : Usize) (_ : i.val < context.values.val.length),
      InSlot double lo hi context.values.val[i.val] ∧ a = .Named (valueIndividual i)) (y : Object') :
    (∃ a ∈ namedList found, individual J a = y) ↔ SlotNamed context J double lo hi y := by
  constructor
  · rintro ⟨a, mem, same⟩
    obtain ⟨i, hi, slotI, rfl⟩ := (members a).mp mem
    exact ⟨i, hi, slotI, same⟩
  · rintro ⟨i, hi, slotI, same⟩
    exact ⟨_, (members _).mpr ⟨i, hi, slotI, rfl⟩, same⟩

/-! ### The axiom on a slot -/

/-- One place past the last value of a format. -/
def placesEnd (double : Bool) : ℕ := 2 * topPlace (fmt double) + 3

/-- A place, or the end when it is past the last value. -/
def clamp (double : Bool) (n : ℕ) : ℕ := min n (placesEnd double)

/-- The values of the format from the place `lo` on and before `hi` that are no
    literal values, counted as the kernel counts them. -/
noncomputable def slotFree (context : data_ontology.Context) (double : Bool) (lo hi : ℕ) : ℕ :=
  (clamp double hi - clamp double lo) -
    slotNamedCount context.values.val double (clamp double lo) (clamp double hi)

/-- What the axiom on a slot of the format says, for the nodes `inSlot` of the
    slot's class: when every value there is a literal value, the nodes are those
    literal values' individuals, and when fewer than the capacity of them are no
    literal values, at most that many other nodes are there at any element
    along `U`. -/
def SlotFact (context : data_ontology.Context) (capacity : Nat) (J : Interpretation Object' Value') (double : Bool)
    (inSlot : Object' → Prop) (lo hi : ℕ) : Prop :=
  (slotFree context double lo hi = 0 → ∀ y, inSlot y →
    SlotNamed context J double (clamp double lo) (clamp double hi) y) ∧
  (0 < slotFree context double lo hi → slotFree context double lo hi < capacity → ∀ y, J.classes thing y →
    AtMost (slotFree context double lo hi) (fun y' => J.objectProperties dataSuper y y' ∧ inSlot y' ∧
      ¬ SlotNamed context J double (clamp double lo) (clamp double hi) y'))

theorem places_end_spec (double : Bool) :
    ∃ r, floats.places double = .ok r ∧ r.val = placesEnd double := Rowl.FloatOrder.places_spec double

theorem places_end_small (double : Bool) : placesEnd double ≤ 7 * 2 ^ 62 := by
  have := Rowl.FloatOrder.top_small double
  unfold placesEnd; omega

theorem format_kind_eq (double : Bool) : data_ontology.format_kind double = .ok (floatKind double) := by
  cases double <;> rfl

/-- The nodes of the slot of the format between the edges `low` and `high`: in
    the format's class, in the class of `low` when there is one, and outside
    the class of `high` when there is one. -/
def InSlotClass (J : Interpretation Object' Value') (double : Bool) (low high : Option Usize) (y : Object') : Prop :=
  J.classes (kindClass (floatKind double)) y ∧ (∀ i, low = some i → J.classes (edgeClass double i) y) ∧
    (∀ j, high = some j → ¬ J.classes (edgeClass double j) y)

theorem slot_class_spec (double : Bool) (low high : Option Usize) :
    ∃ c, data_ontology.slot_class double low high = .ok c ∧
      ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') (y : Object'),
        classDenote J c y ↔ InSlotClass J double low high y := by
  simp only [data_ontology.slot_class, format_kind_eq, bind_ok, kind_class_eq]
  cases low with
  | none =>
    cases high with
    | none => exact ⟨.Class (kindClass (floatKind double)), by simp, fun J y => by simp [InSlotClass, classDenote]⟩
    | some j =>
      refine ⟨.ObjectIntersectionOf ⟨.Class (kindClass (floatKind double)),
        .ObjectComplementOf (.Class (edgeClass double j)), alloc.vec.Vec.new ClassExpression⟩,
        by simp [edge_class_eq, data_ontology.not, data_ontology.and], fun J y => ?_⟩
      rw [inter_iff]
      simp [InSlotClass, classDenote, AtLeastTwo.elements, new_val]
  | some i =>
    cases high with
    | none =>
      refine ⟨.ObjectIntersectionOf ⟨.Class (kindClass (floatKind double)), .Class (edgeClass double i),
        alloc.vec.Vec.new ClassExpression⟩, by simp [edge_class_eq, data_ontology.and], fun J y => ?_⟩
      rw [inter_iff]
      simp [InSlotClass, classDenote, AtLeastTwo.elements, new_val]
    | some j =>
      refine ⟨.ObjectIntersectionOf ⟨.ObjectIntersectionOf ⟨.Class (kindClass (floatKind double)),
        .Class (edgeClass double i), alloc.vec.Vec.new ClassExpression⟩,
        .ObjectComplementOf (.Class (edgeClass double j)), alloc.vec.Vec.new ClassExpression⟩,
        by simp [edge_class_eq, data_ontology.not, data_ontology.and], fun J y => ?_⟩
      simp [inter_iff, InSlotClass, classDenote, AtLeastTwo.elements, new_val, and_assoc]

theorem usize_max_lt : Usize.max < 2 ^ 64 := by
  have := Usize.max_def
  rcases System.Platform.numBits_eq with e | e <;> simp_all [Usize.numBits]

theorem slot_axiom_spec (context : data_ontology.Context) (good : Good context) (double : Bool)
    (low high : Option Usize) (lo hi : U128) (capacity : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.slot_axiom context double low high lo hi capacity out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔
          SlotFact context capacity.val J double (InSlotClass J double low high) lo.val hi.val) := by
  rw [data_ontology.slot_axiom]
  obtain ⟨e, eRun, eVal⟩ := places_end_spec double
  have small := places_end_small double
  obtain ⟨c, cRun, cMeans⟩ := slot_class_spec.{w,x} double low high
  -- the clamped bounds
  obtain ⟨lo1, lo1Run, lo1Val⟩ : ∃ l : U128, (if lo.val < e.val then ok lo else ok e : Result U128) = .ok l ∧
      l.val = clamp double lo.val := by
    by_cases h : lo.val < placesEnd double
    · exact ⟨lo, by simp [eVal, h], by simp [clamp]; omega⟩
    · exact ⟨e, by simp [eVal, h], by simp [clamp, eVal]; omega⟩
  obtain ⟨hi1, hi1Run, hi1Val⟩ : ∃ l : U128, (if hi.val < e.val then ok hi else ok e : Result U128) = .ok l ∧
      l.val = clamp double hi.val := by
    by_cases h : hi.val < placesEnd double
    · exact ⟨hi, by simp [eVal, h], by simp [clamp]; omega⟩
    · exact ⟨e, by simp [eVal, h], by simp [clamp, eVal]; omega⟩
  obtain ⟨size, sizeRun, sizeVal⟩ : ∃ s : U128,
      (if lo1.val ≤ hi1.val then hi1 - lo1 else ok 0#u128 : Result U128) = .ok s ∧
      s.val = clamp double hi.val - clamp double lo.val := by
    by_cases h : lo1.val ≤ hi1.val
    · obtain ⟨d, dRun, dVal⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := hi1) (y := lo1) h)
      exact ⟨d, by simp [h, dRun], by rw [dVal.1, lo1Val, hi1Val]⟩
    · exact ⟨0#u128, by simp [h], by simp; omega⟩
  have bound : context.values.val.length ≤ Usize.max := context.values.property
  have umax : Usize.max < 2 ^ 64 := usize_max_lt
  obtain ⟨named, namedRun, namedVal⟩ := slot_count_spec context good double lo1 hi1 0#usize 0#u128
    (by simp; omega)
  have namedIs : named.val = slotNamedCount context.values.val double (clamp double lo.val) (clamp double hi.val) := by
    rw [namedVal, lo1Val, hi1Val]; simp
  obtain ⟨free, freeRun, freeVal⟩ : ∃ f : U128,
      (if named.val ≤ size.val then size - named else ok 0#u128 : Result U128) =
      .ok f ∧ f.val = slotFree context double lo.val hi.val := by
    by_cases h : named.val ≤ size.val
    · obtain ⟨d, dRun, dVal⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := size) (y := named) h)
      exact ⟨d, by simp [h, dRun], by rw [dVal.1, sizeVal, namedIs]; rfl⟩
    · exact ⟨0#u128, by simp [h], by
        simp only [slotFree]; rw [← namedIs, ← sizeVal]; simp; omega⟩
  obtain ⟨found, foundRun, members0⟩ := slot_literals_spec context good double lo1 hi1 0#usize none
    (by simp [namedList])
  have members : ∀ a, a ∈ namedList found ↔ ∃ (i : Usize) (_ : i.val < context.values.val.length),
      InSlot double (clamp double lo.val) (clamp double hi.val) context.values.val[i.val] ∧
        a = .Named (valueIndividual i) := by
    intro a
    rw [members0 a, lo1Val, hi1Val]
    simp [namedList]
  by_cases zero : free.val = 0
  · have zero' : free = 0#u128 := UScalar.eq_of_val_eq (by simpa using zero)
    have none' : slotFree context double lo.val hi.val = 0 := by rw [← freeVal]; exact zero
    cases found with
    | none =>
      obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf c (.ObjectComplementOf c))
      refine ⟨r, by simp [eRun, lo1Run, hi1Run, sizeRun, namedRun, freeRun, foundRun, zero', cRun,
        data_ontology.not, run], fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
      have nothing : ∀ y, ¬ SlotNamed context J double (clamp double lo.val) (clamp double hi.val) y :=
        fun y named => by simpa [namedList] using (slot_named_iff members y).mpr named
      simp only [List.mem_singleton, forall_eq, SlotFact, none', lt_irrefl, false_imp_iff, implies_true, and_true,
        true_implies, satisfies, classDenote, cMeans]
      constructor
      · intro holds y inS
        exact absurd inS (holds y inS)
      · intro holds y inS
        exact absurd (holds y inS) (nothing y)
    | some list =>
      obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf c (.ObjectOneOf list))
      refine ⟨r, by simp [eRun, lo1Run, hi1Run, sizeRun, namedRun, freeRun, foundRun, zero', cRun, run],
        fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
      have iff := slot_named_iff (J := J) members
      simp only [namedList] at iff
      simp only [List.mem_singleton, forall_eq, SlotFact, none', lt_irrefl, false_imp_iff, implies_true, and_true,
        true_implies, satisfies, classDenote, cMeans]
      constructor
      · intro holds y inS
        exact (iff y).mp (holds y inS)
      · intro holds y inS
        exact (iff y).mpr (holds y inS)
  · have zero' : free ≠ 0#u128 := fun h => zero (by rw [h]; rfl)
    have capIs := Rowl.FloatOrder.cast_usize_u128 capacity
    have capMod : capacity.val % 340282366920938463463374607431768211456 = capacity.val := by
      have : capacity.val < 2 ^ 64 := lt_of_le_of_lt (by scalar_tac) usize_max_lt
      exact Nat.mod_eq_of_lt (by omega)
    by_cases fewer : free.val < capacity.val
    · have fewer' : free.val < (UScalar.cast .U128 capacity).val := by rw [capIs]; exact fewer
      have capLe : capacity.val ≤ Usize.max := by scalar_tac
      have castIs : (UScalar.cast .Usize free).val = free.val := by
        rw [UScalar.cast_val_eq]
        have h1 : capacity.val ≤ Usize.max := by scalar_tac
        have h2 := Usize.max_def
        have h3 : (2 : ℕ) ^ Usize.numBits = 2 ^ System.Platform.numBits := by
          simp [Usize.numBits, UScalarTy.numBits]
        have pos : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
        have : free.val < 2 ^ System.Platform.numBits := by omega
        simp [Nat.mod_eq_of_lt this]
      obtain ⟨n, nRun, nValue⟩ := natural_of_spec (UScalar.cast .Usize free)
      have exact : slotFree context double lo.val hi.val = free.val := freeVal.symm
      -- the axiom on the slot's nodes that are no literal individuals, for a filler of their class
      have tail : ∀ filler : ClassExpression, (∀ {Object' : Type w} {Value' : Type x}
          (J : Interpretation Object' Value') (y : Object'), classDenote J filler y ↔
            InSlotClass J double low high y ∧ ¬ SlotNamed context J double (clamp double lo.val) (clamp double hi.val) y) →
          ∃ new, ([⟨alloc.vec.Vec.new Annotation, Axiom.SubClassOf (.Class thing)
              (.ObjectMaxCardinality n (.Property dataSuper) (some filler))⟩] : List AnnotatedAxiom) = new ∧
            ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
              ((∀ b ∈ new, satisfies J b.axiom) ↔
                SlotFact context capacity.val J double (InSlotClass J double low high) lo.val hi.val) := by
        intro filler fillerMeans
        refine ⟨_, rfl, fun J => ?_⟩
        rw [SlotFact, exact]
        simp only [List.mem_singleton, forall_eq, satisfies, zero, false_imp_iff, true_and, fewer,
          Nat.pos_of_ne_zero zero, true_implies]
        have eq : ∀ y y', (J.objectProperties dataSuper y y' ∧ classDenote J filler y') ↔
            (J.objectProperties dataSuper y y' ∧ InSlotClass J double low high y' ∧
              ¬ SlotNamed context J double (clamp double lo.val) (clamp double hi.val) y') :=
          fun y y' => and_congr Iff.rfl (fillerMeans J y')
        simp only [classDenote, objectRelation, nValue, castIs, eq]
      cases found with
      | none =>
        have fillerMeans : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') (y : Object'),
            classDenote J c y ↔ InSlotClass J double low high y ∧
              ¬ SlotNamed context J double (clamp double lo.val) (clamp double hi.val) y := by
          intro Object' Value' J y
          have nothing : ¬ SlotNamed context J double (clamp double lo.val) (clamp double hi.val) y :=
            fun named => by simpa [namedList] using (slot_named_iff members y).mpr named
          simp [cMeans, nothing]
        obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.Class thing)
          (.ObjectMaxCardinality n (.Property dataSuper) (some c)))
        refine ⟨r, by simp [eRun, lo1Run, hi1Run, sizeRun, namedRun, freeRun, foundRun, zero', capMod, fewer, lift,
          cRun, thing_eq, nRun, data_super_eq, run], fun out' h => ?_⟩
        obtain ⟨new, same, means⟩ := tail c fillerMeans
        exact ⟨new, by rw [contents out' h, same], means⟩
      | some list =>
        have fillerMeans : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') (y : Object'),
            classDenote J (.ObjectIntersectionOf ⟨c, .ObjectComplementOf (.ObjectOneOf list),
              alloc.vec.Vec.new ClassExpression⟩) y ↔ InSlotClass J double low high y ∧
              ¬ SlotNamed context J double (clamp double lo.val) (clamp double hi.val) y := by
          intro Object' Value' J y
          have iff := slot_named_iff (J := J) members y
          simp only [namedList] at iff
          rw [inter_iff]
          simp only [AtLeastTwo.elements, new_val, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
            forall_eq, classDenote, cMeans, ← iff]
        obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.Class thing)
          (.ObjectMaxCardinality n (.Property dataSuper) (some (.ObjectIntersectionOf ⟨c,
            .ObjectComplementOf (.ObjectOneOf list), alloc.vec.Vec.new ClassExpression⟩))))
        refine ⟨r, by simp [eRun, lo1Run, hi1Run, sizeRun, namedRun, freeRun, foundRun, zero', capMod, fewer, lift,
          cRun, data_ontology.not, data_ontology.and, thing_eq, nRun, data_super_eq, run], fun out' h => ?_⟩
        obtain ⟨new, same, means⟩ := tail _ fillerMeans
        exact ⟨new, by rw [contents out' h, same], means⟩
    · refine ⟨some out, by simp [eRun, lo1Run, hi1Run, sizeRun, namedRun, freeRun, foundRun, zero', lift,
        capMod, fewer], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
      have many : capacity.val ≤ slotFree context double lo.val hi.val := by rw [← freeVal]; omega
      have notZero : slotFree context double lo.val hi.val ≠ 0 := by rw [← freeVal]; exact zero
      simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, SlotFact, notZero, false_imp_iff,
        true_and]
      intro _ lt
      omega

/-! ### The edges -/

theorem edge_between_correct (edges : alloc.vec.Vec U128) (low high : U128) (index : Usize) :
    data_ontology.edge_between edges low high index =
      .ok (decide (∃ e ∈ edges.val.drop index.val, low.val < e.val ∧ e.val < high.val)) := by
  rw [data_ontology.edge_between]
  by_cases inside : index.val < edges.val.length
  · have lookup : edges.index_usize index = .ok edges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    have rest := edge_between_correct edges low high next
    rw [nextIndex] at rest
    have member : (∃ e ∈ edges.val.drop index.val, low.val < e.val ∧ e.val < high.val) ↔
        (low.val < edges.val[index.val].val ∧ edges.val[index.val].val < high.val) ∨
          ∃ e ∈ edges.val.drop (index.val + 1), low.val < e.val ∧ e.val < high.val := by
      rw [split]; simp only [List.mem_cons, exists_eq_or_imp]
    simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, advance, rest, member]
  · simp [UScalar.lt_equiv, inside, List.drop_eq_nil_iff.mpr (show edges.val.length ≤ index.val by omega)]
termination_by edges.val.length - index.val
decreasing_by omega

theorem edge_below_correct (edges : alloc.vec.Vec U128) (edge : U128) (index : Usize) :
    data_ontology.edge_below edges edge index = .ok (decide (∃ e ∈ edges.val.drop index.val, e.val < edge.val)) := by
  rw [data_ontology.edge_below]
  by_cases inside : index.val < edges.val.length
  · have lookup : edges.index_usize index = .ok edges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    have rest := edge_below_correct edges edge next
    rw [nextIndex] at rest
    have member : (∃ e ∈ edges.val.drop index.val, e.val < edge.val) ↔
        edges.val[index.val].val < edge.val ∨ ∃ e ∈ edges.val.drop (index.val + 1), e.val < edge.val := by
      rw [split]; simp only [List.mem_cons, exists_eq_or_imp]
    simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, advance, rest, member]
  · simp [UScalar.lt_equiv, inside, List.drop_eq_nil_iff.mpr (show edges.val.length ≤ index.val by omega)]
termination_by edges.val.length - index.val
decreasing_by omega

theorem edge_above_correct (edges : alloc.vec.Vec U128) (edge : U128) (index : Usize) :
    data_ontology.edge_above edges edge index = .ok (decide (∃ e ∈ edges.val.drop index.val, edge.val < e.val)) := by
  rw [data_ontology.edge_above]
  by_cases inside : index.val < edges.val.length
  · have lookup : edges.index_usize index = .ok edges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    have rest := edge_above_correct edges edge next
    rw [nextIndex] at rest
    have member : (∃ e ∈ edges.val.drop index.val, edge.val < e.val) ↔
        edge.val < edges.val[index.val].val ∨ ∃ e ∈ edges.val.drop (index.val + 1), edge.val < e.val := by
      rw [split]; simp only [List.mem_cons, exists_eq_or_imp]
    simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, advance, rest, member]
  · simp [UScalar.lt_equiv, inside, List.drop_eq_nil_iff.mpr (show edges.val.length ≤ index.val by omega)]
termination_by edges.val.length - index.val
decreasing_by omega

section Facts
variable (context : data_ontology.Context) (capacity : Nat) (double : Bool) (J : Interpretation Object' Value')

/-- The `k`-th edge of the format. -/
def edgeAt (k : Usize) (h : k.val < (edgesOf context double).val.length) : ℕ :=
  ((edgesOf context double).val[k.val]'h).val

/-- What the axioms between the edges at `i` and `j` say: the class of `i`
    inside the class of `j` when that is another edge at or below it, and the
    axiom on the slot between them when `j` is the next edge above `i`. -/
def PairFact (i j : Usize) : Prop :=
  ∀ (hi : i.val < (edgesOf context double).val.length) (hj : j.val < (edgesOf context double).val.length),
    (i ≠ j → edgeAt context double j hj ≤ edgeAt context double i hi →
      ∀ y, J.classes (edgeClass double i) y → J.classes (edgeClass double j) y) ∧
    (edgeAt context double i hi < edgeAt context double j hj →
      (∀ e ∈ (edgesOf context double).val, ¬ (edgeAt context double i hi < e.val ∧ e.val < edgeAt context double j hj)) →
      SlotFact context capacity J double (InSlotClass J double (some i) (some j)) (edgeAt context double i hi)
        (edgeAt context double j hj))

/-- What the axioms of a lowest edge say: its class inside the format's class,
    and the axiom on the slot below it. -/
def LowestFact (i : Usize) : Prop :=
  ∀ (hi : i.val < (edgesOf context double).val.length),
    (∀ e ∈ (edgesOf context double).val, ¬ e.val < edgeAt context double i hi) →
    (∀ y, J.classes (edgeClass double i) y → J.classes (kindClass (floatKind double)) y) ∧
    SlotFact context capacity J double (InSlotClass J double none (some i)) 0 (edgeAt context double i hi)

/-- What the axiom of a highest edge says: the axiom on the slot from it to the
    end. -/
def HighestFact (i : Usize) : Prop :=
  ∀ (hi : i.val < (edgesOf context double).val.length),
    (∀ e ∈ (edgesOf context double).val, ¬ edgeAt context double i hi < e.val) →
    SlotFact context capacity J double (InSlotClass J double (some i) none) (edgeAt context double i hi)
      (placesEnd double)

/-- What the axioms of the values of a format in use say: its edges' facts, or
    the axiom on all its values when it has no edges. -/
def EdgeFacts : Prop :=
  Used context.kinds (floatKind double) = true →
    ((edgesOf context double).val = [] →
      SlotFact context capacity J double (InSlotClass J double none none) 0 (placesEnd double)) ∧
    ∀ i : Usize, (∀ j : Usize, PairFact context capacity double J i j) ∧ LowestFact context capacity double J i ∧
      HighestFact context capacity double J i

end Facts

theorem inclusion_axiom_spec (context : data_ontology.Context) (double : Bool) (first second : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.inclusion_axiom context double first second out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔
          ∀ (hi : first.val < (edgesOf context double).val.length)
            (hj : second.val < (edgesOf context double).val.length),
            first ≠ second → edgeAt context double second hj ≤ edgeAt context double first hi →
              ∀ y, J.classes (edgeClass double first) y → J.classes (edgeClass double second) y) := by
  rw [data_ontology.inclusion_axiom, edges_run]
  by_cases inside : first.val < (edgesOf context double).val.length ∧ second.val < (edgesOf context double).val.length
  · have l1 : (edgesOf context double).index_usize first = .ok (edgesOf context double).val[first.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside.1]
    have l2 : (edgesOf context double).index_usize second = .ok (edgesOf context double).val[second.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside.2]
    by_cases cond : first ≠ second ∧ edgeAt context double second inside.2 ≤ edgeAt context double first inside.1
    · obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.Class (edgeClass double first))
        (.Class (edgeClass double second)))
      refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, l1, l2, UScalar.le_equiv,
        cond.1, show (edgesOf context double).val[second.val].val ≤ (edgesOf context double).val[first.val].val from
          cond.2, edge_class_eq, run], fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
      simp only [List.mem_singleton, forall_eq, satisfies, classDenote]
      constructor
      · intro holds _ _ _ _; exact holds
      · intro holds; exact holds inside.1 inside.2 cond.1 cond.2
    · refine ⟨some out, ?_, fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
      · simp only [not_and_or, not_not, ne_eq] at cond
        rcases cond with same | above
        · subst same; simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, l1, l2]
        · have : ¬ (edgesOf context double).val[second.val].val ≤ (edgesOf context double).val[first.val].val :=
            above
          simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, l1, l2, UScalar.le_equiv, this]
      · simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
        intro hi hj ne le
        exact absurd ⟨ne, le⟩ cond
  · refine ⟨some out, ?_, fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    · simp only [not_and_or] at inside
      rcases inside with a | b
      · simp [UScalar.lt_equiv, a]
      · simp [UScalar.lt_equiv, b]
    · simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
      intro hi hj
      exact absurd ⟨hi, hj⟩ inside

theorem neighbour_axiom_spec (context : data_ontology.Context) (good : Good context) (double : Bool)
    (capacity : Usize) (first second : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.neighbour_axiom context double capacity first second out = .ok res ∧
      ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔
          ∀ (hi : first.val < (edgesOf context double).val.length)
            (hj : second.val < (edgesOf context double).val.length),
            edgeAt context double first hi < edgeAt context double second hj →
            (∀ e ∈ (edgesOf context double).val,
              ¬ (edgeAt context double first hi < e.val ∧ e.val < edgeAt context double second hj)) →
            SlotFact context capacity.val J double (InSlotClass J double (some first) (some second))
              (edgeAt context double first hi) (edgeAt context double second hj)) := by
  rw [data_ontology.neighbour_axiom, edges_run]
  by_cases inside : first.val < (edgesOf context double).val.length ∧ second.val < (edgesOf context double).val.length
  · have l1 : (edgesOf context double).index_usize first = .ok (edgesOf context double).val[first.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside.1]
    have l2 : (edgesOf context double).index_usize second = .ok (edgesOf context double).val[second.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside.2]
    have between := edge_between_correct (edgesOf context double) (edgesOf context double).val[first.val]
      (edgesOf context double).val[second.val] 0#usize
    by_cases cond : edgeAt context double first inside.1 < edgeAt context double second inside.2 ∧
        ¬ ∃ e ∈ (edgesOf context double).val, edgeAt context double first inside.1 < e.val ∧
          e.val < edgeAt context double second inside.2
    · obtain ⟨r, run, facts⟩ := slot_axiom_spec context good double (some first) (some second)
        (edgesOf context double).val[first.val] (edgesOf context double).val[second.val] capacity out
      refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, l1, l2, between,
        show (edgesOf context double).val[first.val].val < (edgesOf context double).val[second.val].val from cond.1,
        show ¬ ∃ e ∈ (edgesOf context double).val, (edgesOf context double).val[first.val].val < e.val ∧
          e.val < (edgesOf context double).val[second.val].val from cond.2, run], fun out' h => ?_⟩
      obtain ⟨new, c, means⟩ := facts out' h
      refine ⟨new, c, fun J => ?_⟩
      rw [means J]
      constructor
      · intro fact _ _ _ _; exact fact
      · intro fact
        exact fact inside.1 inside.2 cond.1 (fun e m ⟨a, b⟩ => cond.2 ⟨e, m, a, b⟩)
    · refine ⟨some out, ?_, fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
      · simp only [not_and_or, not_not] at cond
        rcases cond with notLt | some'
        · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, l1, l2, between,
            show ¬ (edgesOf context double).val[first.val].val < (edgesOf context double).val[second.val].val from
              notLt]
        · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, l1, l2, between,
            show ∃ e ∈ (edgesOf context double).val, (edgesOf context double).val[first.val].val < e.val ∧
              e.val < (edgesOf context double).val[second.val].val from some']
      · simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
        intro hi hj lt none
        exact absurd ⟨lt, fun ⟨e, m, a, b⟩ => none e m ⟨a, b⟩⟩ cond
  · refine ⟨some out, ?_, fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    · simp only [not_and_or] at inside
      rcases inside with a | b
      · simp [UScalar.lt_equiv, a]
      · simp [UScalar.lt_equiv, b]
    · simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
      intro hi hj
      exact absurd ⟨hi, hj⟩ inside

theorem pair_axioms_spec (context : data_ontology.Context) (good : Good context) (double : Bool)
    (capacity : Usize) (first second : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.pair_axioms context double capacity first second out = .ok res ∧
      ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔
          ∀ j : Usize, second.val ≤ j.val → PairFact context capacity.val double J first j) := by
  rw [data_ontology.pair_axioms, edges_run]
  by_cases inside : second.val < (edgesOf context double).val.length
  · obtain ⟨r1, run1, f1⟩ := inclusion_axiom_spec context double first second out
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, run1], by simp⟩
    | some o1 =>
      obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
      obtain ⟨r2, run2, f2⟩ := neighbour_axiom_spec context good double capacity first second o1
      cases r2 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, run1, run2], by simp⟩
      | some o2 =>
        obtain ⟨n2, c2, m2⟩ := f2 o2 rfl
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := second) (y := 1#usize) (by scalar_tac))
        have nextIndex : next.val = second.val + 1 := by simpa using nextValue
        obtain ⟨r3, run3, f3⟩ := pair_axioms_spec context good double capacity first next o2
        refine ⟨r3, by simp [UScalar.lt_equiv, inside, run1, run2, advance, run3], fun out' h => ?_⟩
        obtain ⟨n3, c3, m3⟩ := f3 out' h
        refine ⟨n1 ++ n2 ++ n3, by rw [c3, c2, c1]; simp, fun J => ?_⟩
        simp only [List.forall_mem_append]
        rw [m1 J, m2 J, m3 J, nextIndex]
        constructor
        · rintro ⟨⟨incl, nb⟩, rest⟩ j le hi hj
          by_cases same : j = second
          · subst same; exact ⟨incl hi hj, nb hi hj⟩
          · have : j.val ≠ second.val := fun h => same (UScalar.eq_of_val_eq h)
            exact rest j (by omega) hi hj
        · intro all
          exact ⟨⟨fun hi hj => (all second le_rfl hi hj).1, fun hi hj => (all second le_rfl hi hj).2⟩,
            fun j le => all j (by omega)⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    intro j le hi hj
    omega
termination_by (edgesOf context double).val.length - second.val
decreasing_by omega

theorem lowest_axioms_spec (context : data_ontology.Context) (good : Good context) (double : Bool)
    (capacity : Usize) (index : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.lowest_axioms context double capacity index out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ LowestFact context capacity.val double J index) := by
  rw [data_ontology.lowest_axioms, edges_run]
  by_cases inside : index.val < (edgesOf context double).val.length
  · have lookup : (edgesOf context double).index_usize index = .ok (edgesOf context double).val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have below := edge_below_correct (edgesOf context double) (edgesOf context double).val[index.val] 0#usize
    by_cases lowest : ∃ e ∈ (edgesOf context double).val, e.val < (edgesOf context double).val[index.val].val
    · refine ⟨some out, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, below, lowest],
        fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
      simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, LowestFact]
      intro hi none
      obtain ⟨e, m, lt⟩ := lowest
      exact absurd lt (none e m)
    · obtain ⟨r1, run1, c1⟩ := push_spec out (.SubClassOf (.Class (edgeClass double index))
        (.Class (kindClass (floatKind double))))
      cases r1 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, below,
          lowest, format_kind_eq, edge_class_eq, kind_class_eq, run1], by simp⟩
      | some o1 =>
        obtain ⟨r2, run2, f2⟩ := slot_axiom_spec context good double none (some index) 0#u128
          (edgesOf context double).val[index.val] capacity o1
        refine ⟨r2, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, below, lowest,
          format_kind_eq, edge_class_eq, kind_class_eq, run1, run2], fun out' h => ?_⟩
        obtain ⟨n2, c2, m2⟩ := f2 out' h
        refine ⟨⟨alloc.vec.Vec.new Annotation, .SubClassOf (.Class (edgeClass double index))
          (.Class (kindClass (floatKind double)))⟩ :: n2, by rw [c2, c1 o1 rfl]; simp, fun J => ?_⟩
        simp only [List.forall_mem_cons]
        rw [m2 J]
        simp only [satisfies, classDenote, LowestFact]
        constructor
        · rintro ⟨incl, slot⟩ hi _
          exact ⟨incl, by simpa [edgeAt] using slot⟩
        · intro fact
          obtain ⟨incl, slot⟩ := fact inside (fun e m lt => lowest ⟨e, m, lt⟩)
          exact ⟨incl, by simpa [edgeAt] using slot⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, LowestFact]
    intro hi
    exact absurd hi inside

theorem highest_axiom_spec (context : data_ontology.Context) (good : Good context) (double : Bool)
    (capacity : Usize) (index : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.highest_axiom context double capacity index out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ HighestFact context capacity.val double J index) := by
  rw [data_ontology.highest_axiom, edges_run]
  by_cases inside : index.val < (edgesOf context double).val.length
  · have lookup : (edgesOf context double).index_usize index = .ok (edgesOf context double).val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have above := edge_above_correct (edgesOf context double) (edgesOf context double).val[index.val] 0#usize
    by_cases highest : ∃ e ∈ (edgesOf context double).val, (edgesOf context double).val[index.val].val < e.val
    · refine ⟨some out, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, above, highest],
        fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
      simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, HighestFact]
      intro hi none
      obtain ⟨e, m, lt⟩ := highest
      exact absurd lt (none e m)
    · obtain ⟨e, eRun, eVal⟩ := places_end_spec double
      obtain ⟨r2, run2, f2⟩ := slot_axiom_spec context good double (some index) none
        (edgesOf context double).val[index.val] e capacity out
      refine ⟨r2, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, above, highest, eRun,
        run2], fun out' h => ?_⟩
      obtain ⟨n2, c2, m2⟩ := f2 out' h
      refine ⟨n2, c2, fun J => ?_⟩
      rw [m2 J, eVal]
      simp only [HighestFact]
      constructor
      · intro slot hi _
        simpa [edgeAt] using slot
      · intro fact
        simpa [edgeAt] using fact inside (fun e m lt => highest ⟨e, m, lt⟩)
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, HighestFact]
    intro hi
    exact absurd hi inside

/-- The facts of the edges from `index` on. -/
def EdgesFrom (context : data_ontology.Context) (capacity : Nat) (double : Bool) (J : Interpretation Object' Value')
    (index : Nat) : Prop :=
  ∀ i : Usize, index ≤ i.val → (∀ j : Usize, PairFact context capacity double J i j) ∧
    LowestFact context capacity double J i ∧ HighestFact context capacity double J i

theorem edges_from_end {context : data_ontology.Context} {capacity : Nat} {double : Bool}
    {J : Interpretation Object' Value'} {index : Nat} (past : (edgesOf context double).val.length ≤ index) :
    EdgesFrom context capacity double J index := by
  intro i le
  refine ⟨fun j hi => by omega, fun hi => by omega, fun hi => by omega⟩

theorem edge_axioms_spec (context : data_ontology.Context) (good : Good context) (double : Bool)
    (capacity : Usize) (index : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.edge_axioms context double capacity index out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ EdgesFrom context capacity.val double J index.val) := by
  rw [data_ontology.edge_axioms, edges_run]
  by_cases inside : index.val < (edgesOf context double).val.length
  · obtain ⟨r1, run1, f1⟩ := pair_axioms_spec context good double capacity index 0#usize out
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, run1], by simp⟩
    | some o1 =>
      obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
      obtain ⟨r2, run2, f2⟩ := lowest_axioms_spec context good double capacity index o1
      cases r2 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, run1, run2], by simp⟩
      | some o2 =>
        obtain ⟨n2, c2, m2⟩ := f2 o2 rfl
        obtain ⟨r3, run3, f3⟩ := highest_axiom_spec context good double capacity index o2
        cases r3 with
        | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, run1, run2, run3], by simp⟩
        | some o3 =>
          obtain ⟨n3, c3, m3⟩ := f3 o3 rfl
          obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
          have nextIndex : next.val = index.val + 1 := by simpa using nextValue
          obtain ⟨r4, run4, f4⟩ := edge_axioms_spec context good double capacity next o3
          refine ⟨r4, by simp [UScalar.lt_equiv, inside, run1, run2, run3, advance, run4], fun out' h => ?_⟩
          obtain ⟨n4, c4, m4⟩ := f4 out' h
          refine ⟨n1 ++ n2 ++ n3 ++ n4, by rw [c4, c3, c2, c1]; simp, fun J => ?_⟩
          simp only [List.forall_mem_append]
          rw [m1 J, m2 J, m3 J, m4 J, nextIndex]
          constructor
          · rintro ⟨⟨⟨pairs, low⟩, high⟩, rest⟩ i le
            by_cases same : i = index
            · subst same; exact ⟨fun j => pairs j (by simp), low, high⟩
            · have : i.val ≠ index.val := fun h => same (UScalar.eq_of_val_eq h)
              exact rest i (by omega)
          · intro all
            obtain ⟨pairs, low, high⟩ := all index le_rfl
            exact ⟨⟨⟨fun j _ => pairs j, low⟩, high⟩, fun i le => all i (by omega)⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    exact edges_from_end (by omega)
termination_by (edgesOf context double).val.length - index.val
decreasing_by omega

theorem binary_axioms_spec (context : data_ontology.Context) (good : Good context) (double : Bool)
    (capacity : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.binary_axioms context double capacity out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ EdgeFacts context capacity.val double J) := by
  simp only [data_ontology.binary_axioms, format_kind_eq, edges_run, bind_ok, used_eq]
  by_cases used : Used context.kinds (floatKind double) = true
  · by_cases empty : (edgesOf context double).val = []
    · have lenZero : alloc.vec.Vec.len (edgesOf context double) = 0#usize := by
        apply UScalar.eq_of_val_eq; simp [empty]
      obtain ⟨e, eRun, eVal⟩ := places_end_spec double
      obtain ⟨r, run, f⟩ := slot_axiom_spec context good double none none 0#u128 e capacity out
      refine ⟨r, by simp [used, lenZero, eRun, run], fun out' h => ?_⟩
      obtain ⟨n, c, m⟩ := f out' h
      refine ⟨n, c, fun J => ?_⟩
      rw [m J, eVal]
      constructor
      · intro slot _
        refine ⟨fun _ => by simpa using slot, fun i => ?_⟩
        have none : ¬ i.val < (edgesOf context double).val.length := by simp [empty]
        exact edges_from_end (index := i.val) (by omega) i le_rfl
      · intro facts
        simpa using (facts used).1 empty
    · have lenNot : alloc.vec.Vec.len (edgesOf context double) ≠ 0#usize := by
        intro h; apply empty; have := congrArg UScalar.val h; simpa using this
      obtain ⟨r, run, f⟩ := edge_axioms_spec context good double capacity 0#usize out
      refine ⟨r, by simp [used, lenNot, run], fun out' h => ?_⟩
      obtain ⟨n, c, m⟩ := f out' h
      refine ⟨n, c, fun J => ?_⟩
      rw [m J]
      constructor
      · intro all _
        exact ⟨fun e => absurd e empty, fun i => all i (by simp)⟩
      · intro facts i _
        exact (facts used).2 i
  · refine ⟨some out, by simp [used], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, EdgeFacts]
    intro u
    exact absurd u used

/-! ### The values of a slot -/

/-- The value of a kernel value of a floating-point format. -/
noncomputable def binaryValueOf : datatypes.DataValue → Rowl.DatatypeMap.Binary
  | .Double b => binaryOf b
  | .Float b => binaryOf b
  | _ => .nan

/-- The values of the literal values of a format. -/
def literalBinaries (values : List datatypes.DataValue) (double : Bool) : Set Rowl.DatatypeMap.Binary :=
  {x | ∃ b, floatLit double b ∈ values ∧ binaryOf b = x}

/-- The values of a format in a slot that are no literal values. -/
def FreeSlot (values : List datatypes.DataValue) (double : Bool) (lo hi : ℕ) : Set Rowl.DatatypeMap.Binary :=
  Rowl.FloatOrder.Slot (fmt double) lo hi \ literalBinaries values double

theorem binary_value_lit (double : Bool) (b : datatypes.Binary) : binaryValueOf (floatLit double b) = binaryOf b := by
  cases double <;> rfl

theorem canonical_lit {double : Bool} {b : datatypes.Binary} (c : Canonical (floatLit double b)) :
    CanonicalBinary b ∧ (binaryOf b).Valid (fmt double) := by
  cases double
  · exact c
  · exact c

theorem slot_lits_eq (values : List datatypes.DataValue) (double : Bool) (lo hi : ℕ)
    (canonical : ∀ v ∈ values, Canonical v) :
    Rowl.FloatOrder.Slot (fmt double) lo hi ∩ literalBinaries values double =
      binaryValueOf '' {v | v ∈ values.filter (fun v => decide (InSlot double lo hi v))} := by
  ext x
  constructor
  · rintro ⟨⟨vx, l, u⟩, b, mem, rfl⟩
    refine ⟨floatLit double b, ?_, binary_value_lit double b⟩
    simp only [Set.mem_setOf_eq, List.mem_filter, decide_eq_true_eq]
    exact ⟨mem, _, format_place_lit double b, l, u⟩
  · rintro ⟨v, mem, rfl⟩
    simp only [Set.mem_setOf_eq, List.mem_filter, decide_eq_true_eq] at mem
    obtain ⟨inValues, n, place, l, u⟩ := mem
    obtain ⟨b, rfl, rfl⟩ := format_place_some place
    have cb := canonical_lit (canonical _ inValues)
    rw [binary_value_lit]
    exact ⟨⟨cb.2, l, u⟩, b, inValues, rfl⟩

theorem slot_lits_card {values : List datatypes.DataValue} (good : GoodValues values) (double : Bool) (lo hi : ℕ) :
    (Rowl.FloatOrder.Slot (fmt double) lo hi ∩ literalBinaries values double).ncard =
      slotNamedCount values double lo hi := by
  rw [slot_lits_eq values double lo hi good.1, Set.InjOn.ncard_image]
  · rw [show {v | v ∈ values.filter (fun v => decide (InSlot double lo hi v))} =
        ↑(values.filter (fun v => decide (InSlot double lo hi v))).toFinset by ext; simp,
      Set.ncard_coe_finset, List.toFinset_card_of_nodup (good.2.filter _)]
    rfl
  · intro v hv v' hv' same
    simp only [Set.mem_setOf_eq, List.mem_filter, decide_eq_true_eq] at hv hv'
    obtain ⟨m, n, place, _, _⟩ := hv
    obtain ⟨m', n', place', _, _⟩ := hv'
    obtain ⟨b, rfl, rfl⟩ := format_place_some place
    obtain ⟨b', rfl, rfl⟩ := format_place_some place'
    rw [binary_value_lit, binary_value_lit] at same
    rw [Rowl.Floats.binary_canonical_injective (canonical_lit (good.1 _ m)).1 (canonical_lit (good.1 _ m')).1 same]

theorem literal_binaries_finite (values : List datatypes.DataValue) (double : Bool) :
    (literalBinaries values double).Finite := by
  apply (values.finite_toSet.image binaryValueOf).subset
  rintro x ⟨b, mem, rfl⟩
  exact ⟨_, mem, binary_value_lit double b⟩

/-- The values of a format in a slot that are no literal values are counted
    exactly by the places of the slot less its literal values. -/
theorem free_slot_card {values : List datatypes.DataValue} (good : GoodValues values) (double : Bool) (lo hi : ℕ)
    (end' : hi ≤ placesEnd double) :
    (FreeSlot values double lo hi).ncard = (hi - lo) - slotNamedCount values double lo hi := by
  have pf := Rowl.FloatOrder.proper_fmt double
  have finite := Rowl.FloatOrder.slot_finite (fmt double) pf lo hi
  unfold FreeSlot
  rw [← Set.sdiff_self_inter, Set.ncard_sdiff Set.inter_subset_left (finite.subset Set.inter_subset_left),
    slot_lits_card good double lo hi]
  by_cases order : lo ≤ hi
  · rw [Rowl.FloatOrder.slot_card pf lo hi (by unfold placesEnd at end'; exact end')]
  · have empty : Rowl.FloatOrder.Slot (fmt double) lo hi = ∅ := by
      ext x; simp only [Rowl.FloatOrder.Slot, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, l, u⟩; omega
    rw [empty]; simp; omega

theorem clamp_le (double : Bool) (n : ℕ) : clamp double n ≤ placesEnd double := min_le_right _ _

/-- The kernel's count of the free values of a slot is their number. -/
theorem slot_free_card {context : data_ontology.Context} (good : Good context) (double : Bool) (lo hi : ℕ) :
    (FreeSlot context.values.val double (clamp double lo) (clamp double hi)).ncard =
      slotFree context double lo hi := by
  rw [free_slot_card good.1 double _ _ (clamp_le double hi)]
  rfl

theorem free_slot_finite (values : List datatypes.DataValue) (double : Bool) (lo hi : ℕ) :
    (FreeSlot values double lo hi).Finite :=
  (Rowl.FloatOrder.slot_finite (fmt double) (Rowl.FloatOrder.proper_fmt double) lo hi).subset Set.sdiff_subset

/-- Every place of a value of the format is before the end. -/
theorem position_lt_end {double : Bool} {x : Rowl.DatatypeMap.Binary} (v : x.Valid (fmt double)) :
    position (fmt double) x < placesEnd double := by
  have := Rowl.FloatOrder.position_le (Rowl.FloatOrder.proper_fmt double) v
  unfold placesEnd; omega

/-- At most as many elements meet `P` as there are values in `S` when each of
    them stands for a value of `S` that no other stands for. -/
theorem at_most_of_free {α : Type*} {P : α → Prop} {S : Set Rowl.DatatypeMap.Binary} (finite : S.Finite)
    (R : α → Rowl.DatatypeMap.Binary → Prop) (exists' : ∀ a, P a → ∃ x ∈ S, R a x)
    (unique : ∀ a a' x, P a → P a' → R a x → R a' x → a = a') : AtMost S.ncard P := by
  rintro ⟨f, finj, fP⟩
  choose g hg using fun k => exists' (f k) (fP k)
  have ginj : Function.Injective g := by
    intro k k' same
    apply finj
    exact unique _ _ _ (fP k) (fP k') (hg k).2 (same ▸ (hg k').2)
  have sub : Set.range g ⊆ S := by rintro _ ⟨k, rfl⟩; exact (hg k).1
  have card : (Set.range g).ncard = S.ncard + 1 := by
    rw [Set.ncard_range_of_injective ginj]; simp
  have := Set.ncard_le_ncard sub finite
  omega

end Rowl.DataEdges
