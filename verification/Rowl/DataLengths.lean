import Rowl.DataTimes

/-!
The axioms that `data_ontology` adds for the lengths of the context
(`length_axioms`). The lengths are those at which the values of the length
facets begin or end, each with a class of the values at least that long
(`Rowl.DataMeaning.NodeValue`). The kernel puts the class of each length inside
the class of every shorter length (`LengthFacts`), and, for each kind in use
with the length facets but `rdf:PlainLiteral` (whose values with a language
tag are infinitely many at every length), on the values of the kind with a
length from a length on and before the next length above it, or before the
least length, that are no literal values: the strings by the rank of their
deepest subtype of `xsd:string` in use, up to the next rank in use. Those values
are counted by the automata of `lengths.rs` (`sizedTotal`): none of them, or at
most their number at any element along `U` when there are at most the
capacity of them (`SizedFact`, `SlotFacts`).
-/
namespace Rowl.DataLengths
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.DataRegions (namedList add_named_spec natural_of_spec ValuesFit)
open Rowl.Datatypes (Canonical InKind)
open Rowl.LengthCounts (ValueLength lengthDfa)
open Rowl.WordCounts (capAt)
attribute [local instance low] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe w x

variable {Object' : Type w} {Value' : Type x}

/-! ### Literal values of a kind and a slot of lengths -/

/-- A literal value of `kind` and not of `below`, if any, with a length from
    `low` on and before `high`. -/
def SizedValue (kind : datatypes.Kind) (below : Option datatypes.Kind) (low high : ℕ)
    (v : datatypes.DataValue) : Prop :=
  ∃ m, ValueLength v m ∧ InKind v kind ∧ (∀ b, below = some b → ¬ InKind v b) ∧ low ≤ m ∧ m < high

theorem in_sized_spec (v : datatypes.DataValue) (cv : Canonical v) (kind : datatypes.Kind)
    (below : Option datatypes.Kind) (low high : Usize) :
    data_ontology.in_sized v kind below low high = .ok (decide (SizedValue kind below low.val high.val v)) := by
  unfold data_ontology.in_sized
  obtain ⟨r, run, means⟩ := Rowl.LengthCounts.value_length_spec v cv
  rw [run]
  cases r with
  | none =>
    have none : ∀ m, ¬ ValueLength v m := fun m h => by
      obtain ⟨_, e, _⟩ := (means m).mp h
      cases e
    simp only [bind_ok]
    rw [show decide (SizedValue kind below low.val high.val v) = false by
      simp only [decide_eq_false_iff_not, SizedValue, not_exists, not_and]
      exact fun m h => absurd h (none m)]
  | some length =>
    have here : ∀ m, ValueLength v m ↔ m = length.val := fun m => by
      rw [means m]
      constructor
      · rintro ⟨n, e, rfl⟩; cases e; rfl
      · rintro rfl; exact ⟨length, rfl, rfl⟩
    have sized : SizedValue kind below low.val high.val v ↔ InKind v kind ∧ (∀ b, below = some b → ¬ InKind v b) ∧
        low.val ≤ length.val ∧ length.val < high.val := by
      simp only [SizedValue, here, exists_eq_left]
    simp only [bind_ok]
    cases below with
    | none =>
      simp only [Rowl.Datatypes.in_kind_correct v cv, bind_ok, Bool.and_true, sized, reduceCtorEq, false_imp_iff,
        implies_true, true_and, UScalar.le_equiv, UScalar.lt_equiv]
      by_cases a : InKind v kind <;> by_cases b : low.val ≤ length.val <;> by_cases c : length.val < high.val <;>
        simp [a, b, c]
    | some other =>
      simp only [Rowl.Datatypes.in_kind_correct v cv, bind_ok, sized, Option.some.injEq, forall_eq',
        UScalar.le_equiv, UScalar.lt_equiv]
      by_cases a : InKind v kind <;> by_cases o : InKind v other <;> by_cases b : low.val ≤ length.val <;>
        by_cases c : length.val < high.val <;> simp [a, o, b, c]

/-- The number of the literal values of a kind and a slot of lengths. -/
noncomputable def sizedNamedCount (values : List datatypes.DataValue) (kind : datatypes.Kind)
    (below : Option datatypes.Kind) (low high : ℕ) : ℕ :=
  (values.filter (fun v => decide (SizedValue kind below low high v))).length

theorem sized_count_spec (context : data_ontology.Context) (good : Good context) (kind : datatypes.Kind)
    (below : Option datatypes.Kind) (low high index count : Usize)
    (room : count.val + (context.values.val.length - index.val) ≤ Usize.max) :
    ∃ r : Usize, data_ontology.sized_count context kind below low high index count = .ok r ∧
      r.val = count.val + sizedNamedCount (context.values.val.drop index.val) kind below low.val high.val := by
  rw [data_ontology.sized_count]
  by_cases inside : index.val < context.values.val.length
  · have lookup : context.values.index_usize index = .ok context.values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have member := List.getElem_mem inside
    have isIt := in_sized_spec context.values.val[index.val] (good.1.1 _ member) kind below low high
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    have countLt : count < core.num.Usize.MAX := by
      simp only [UScalar.lt_equiv, Rowl.LengthCounts.usize_max_val]; omega
    by_cases hit : SizedValue kind below low.val high.val context.values.val[index.val]
    · obtain ⟨c1, c1Run, c1Val⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := count) (y := 1#usize) (by scalar_tac))
      have c1Is : c1.val = count.val + 1 := by simpa using c1Val
      obtain ⟨r, run, value⟩ := sized_count_spec context good kind below low high next c1
        (by rw [c1Is, nextIndex]; omega)
      refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, isIt, hit, countLt,
        advance, c1Run, run], ?_⟩
      rw [value, c1Is, nextIndex, split]
      simp only [sizedNamedCount, List.filter_cons, hit, decide_true, ↓reduceIte, List.length_cons]
      omega
    · obtain ⟨r, run, value⟩ := sized_count_spec context good kind below low high next count
        (by rw [nextIndex]; omega)
      refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, isIt, hit, advance,
        run], ?_⟩
      rw [value, nextIndex, split]
      simp only [sizedNamedCount, List.filter_cons, hit, decide_false, Bool.false_eq_true, ↓reduceIte]
  · refine ⟨count, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show context.values.val.length ≤ index.val by omega), sizedNamedCount]
termination_by context.values.val.length - index.val
decreasing_by all_goals (simp at nextValue; omega)

/-- A node that is the individual of a literal value of a kind and a slot of
    lengths. -/
def SizedNamed (context : data_ontology.Context) (J : Interpretation Object' Value') (kind : datatypes.Kind)
    (below : Option datatypes.Kind) (low high : ℕ) (y : Object') : Prop :=
  ∃ (i : Usize) (_ : i.val < context.values.val.length), SizedValue kind below low high context.values.val[i.val] ∧
    J.namedIndividuals (valueIndividual i) = y

theorem sized_literals_spec (context : data_ontology.Context) (good : Good context) (kind : datatypes.Kind)
    (below : Option datatypes.Kind) (low high index : Usize) (found : Option (NonEmpty Individual))
    (room : (namedList found).length ≤ index.val) :
    ∃ res, data_ontology.sized_literals context kind below low high index found = .ok res ∧ ∀ a, a ∈ namedList res ↔
      a ∈ namedList found ∨ ∃ (i : Usize) (_ : i.val < context.values.val.length), index.val ≤ i.val ∧
        SizedValue kind below low.val high.val context.values.val[i.val] ∧ a = .Named (valueIndividual i) := by
  rw [data_ontology.sized_literals]
  by_cases inside : index.val < context.values.val.length
  · have lookup : context.values.index_usize index = .ok context.values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have member := List.getElem_mem inside
    have isIt := in_sized_spec context.values.val[index.val] (good.1.1 _ member) kind below low high
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    by_cases hit : SizedValue kind below low.val high.val context.values.val[index.val]
    · have bound : context.values.val.length ≤ Usize.max := context.values.property
      obtain ⟨o, addRun, addList⟩ := add_named_spec found (.Named (valueIndividual index)) (by omega)
      obtain ⟨res, run, members⟩ := sized_literals_spec context good kind below low high next o
        (by rw [addList, nextIndex]; simp; omega)
      refine ⟨res, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, isIt, hit, advance,
        value_individual_eq, addRun, run], fun a => ?_⟩
      rw [members a, addList, nextIndex]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ((old | rfl) | ⟨i, hi, later, atI, rfl⟩)
        · exact .inl old
        · exact .inr ⟨index, inside, le_rfl, hit, rfl⟩
        · exact .inr ⟨i, hi, by omega, atI, rfl⟩
      · rintro (old | ⟨i, hi, later, atI, rfl⟩)
        · exact .inl (.inl old)
        · by_cases same : i = index
          · subst same; exact .inl (.inr rfl)
          · have : i.val ≠ index.val := fun h => same (UScalar.eq_of_val_eq h)
            exact .inr ⟨i, hi, by omega, atI, rfl⟩
    · obtain ⟨res, run, members⟩ := sized_literals_spec context good kind below low high next found
        (by rw [nextIndex]; omega)
      refine ⟨res, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, isIt, hit, advance,
        run], fun a => ?_⟩
      rw [members a, nextIndex]
      constructor
      · rintro (old | ⟨i, hi, later, atI, rfl⟩)
        · exact .inl old
        · exact .inr ⟨i, hi, by omega, atI, rfl⟩
      · rintro (old | ⟨i, hi, later, atI, rfl⟩)
        · exact .inl old
        · by_cases same : i = index
          · subst same; exact absurd atI hit
          · have : i.val ≠ index.val := fun h => same (UScalar.eq_of_val_eq h)
            exact .inr ⟨i, hi, by omega, atI, rfl⟩
  · refine ⟨found, by simp [UScalar.lt_equiv, inside], fun a => ?_⟩
    constructor
    · exact .inl
    · rintro (old | ⟨i, hi, later, _, _⟩)
      · exact old
      · omega
termination_by context.values.val.length - index.val
decreasing_by all_goals (simp at nextValue; omega)

theorem sized_named_iff {context : data_ontology.Context} {J : Interpretation Object' Value'}
    {kind : datatypes.Kind} {below : Option datatypes.Kind} {low high : ℕ} {found : Option (NonEmpty Individual)}
    (members : ∀ a, a ∈ namedList found ↔ ∃ (i : Usize) (_ : i.val < context.values.val.length),
      SizedValue kind below low high context.values.val[i.val] ∧ a = .Named (valueIndividual i)) (y : Object') :
    (∃ a ∈ namedList found, individual J a = y) ↔ SizedNamed context J kind below low high y := by
  constructor
  · rintro ⟨a, mem, same⟩
    obtain ⟨i, hi, atI, rfl⟩ := (members a).mp mem
    exact ⟨i, hi, atI, same⟩
  · rintro ⟨i, hi, atI, same⟩
    exact ⟨_, (members _).mpr ⟨i, hi, atI, rfl⟩, same⟩

/-! ### The class of a kind and a slot of lengths -/

/-- A node in the class of the values of `kind` and not of `below`, if any,
    with at least the length at `low`, if any, and less than the length at
    `high`, if any. -/
def InSized (J : Interpretation Object' Value') (kind : datatypes.Kind) (below : Option datatypes.Kind)
    (low high : Option Usize) (y : Object') : Prop :=
  J.classes (kindClass kind) y ∧ (∀ b, below = some b → ¬ J.classes (kindClass b) y) ∧
    (∀ i, low = some i → J.classes (lengthClass i) y) ∧ (∀ j, high = some j → ¬ J.classes (lengthClass j) y)

theorem and_class_iff (J : Interpretation Object' Value') (a b : ClassExpression) (y : Object') :
    classDenote J (.ObjectIntersectionOf ⟨a, b, alloc.vec.Vec.new ClassExpression⟩) y ↔
      classDenote J a y ∧ classDenote J b y := by
  rw [inter_iff]
  simp [AtLeastTwo.elements, new_val]

/-- The class of a kind and a slot of lengths (`data_ontology::sized_class`). -/
noncomputable def sizedClass (kind : datatypes.Kind) (below : Option datatypes.Kind) (low high : Option Usize) :
    ClassExpression :=
  let base : ClassExpression := match below with
    | none => .Class (kindClass kind)
    | some b => .ObjectIntersectionOf ⟨.Class (kindClass kind), .ObjectComplementOf (.Class (kindClass b)),
        alloc.vec.Vec.new ClassExpression⟩
  let from1 : ClassExpression := match low with
    | none => base
    | some i => .ObjectIntersectionOf ⟨base, .Class (lengthClass i), alloc.vec.Vec.new ClassExpression⟩
  match high with
  | none => from1
  | some j => .ObjectIntersectionOf ⟨from1, .ObjectComplementOf (.Class (lengthClass j)),
      alloc.vec.Vec.new ClassExpression⟩

theorem sized_class_spec (kind : datatypes.Kind) (below : Option datatypes.Kind) (low high : Option Usize) :
    data_ontology.sized_class kind below low high = .ok (sizedClass kind below low high) ∧
      ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') (y : Object'),
        classDenote J (sizedClass kind below low high) y ↔ InSized J kind below low high y := by
  refine ⟨?_, fun J y => ?_⟩
  · cases below <;> cases low <;> cases high <;>
      simp [data_ontology.sized_class, sizedClass, kind_class_eq, length_class_eq, data_ontology.not,
        data_ontology.and]
  · cases below <;> cases low <;> cases high <;>
      simp [sizedClass, InSized, and_class_iff, classDenote, and_assoc]


/-! ### The axiom on a kind and a slot of lengths -/

/-- The values of a kind and a slot of lengths, as the automaton of the
    octets (`octets`) or of the strings of the ranks from `first` on and before
    `last` counts them. -/
noncomputable def sizedTotal (octets : Bool) (first last low high : ℕ) : ℕ :=
  ∑ ℓ ∈ Finset.Ico low high, (lengthDfa octets first last).count 0 ℓ

/-- The values of a kind and a slot of lengths that are no literal values,
    counted as the kernel counts them. -/
noncomputable def sizedFree (context : data_ontology.Context) (kind : datatypes.Kind)
    (below : Option datatypes.Kind) (octets : Bool) (first last low high : ℕ) : ℕ :=
  sizedTotal octets first last low high - sizedNamedCount context.values.val kind below low high

/-- What the axiom on the values of a kind and a slot of lengths that are no
    literal values says when there are at most the capacity of them, beside
    the literal values: when there are none, the nodes of their class are the
    individuals of literal values, and otherwise at most their number of other
    nodes are there at any element along `U`. -/
def SizedFact (context : data_ontology.Context) (capacity : ℕ) (J : Interpretation Object' Value')
    (kind : datatypes.Kind) (below : Option datatypes.Kind) (octets : Bool) (first last : ℕ)
    (lowIndex highIndex : Option Usize) (low high : ℕ) : Prop :=
  sizedTotal octets first last low high ≤ capacity + sizedNamedCount context.values.val kind below low high →
    (sizedFree context kind below octets first last low high = 0 →
      ∀ y, InSized J kind below lowIndex highIndex y → SizedNamed context J kind below low high y) ∧
    (0 < sizedFree context kind below octets first last low high → ∀ y, J.classes thing y →
      AtMost (sizedFree context kind below octets first last low high) (fun y' =>
        J.objectProperties dataSuper y y' ∧ InSized J kind below lowIndex highIndex y' ∧
          ¬ SizedNamed context J kind below low high y'))

theorem sized_axiom_spec (context : data_ontology.Context) (good : Good context) (kind : datatypes.Kind)
    (below : Option datatypes.Kind) (octets : Bool) (first last : U8) (lowIndex highIndex : Option Usize)
    (low high capacity : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.sized_axiom context kind below octets first last lowIndex highIndex low high capacity out =
        .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔
          SizedFact context capacity.val J kind below octets first.val last.val lowIndex highIndex low.val high.val) := by
  rw [data_ontology.sized_axiom]
  have bound : context.values.val.length ≤ Usize.max := context.values.property
  obtain ⟨named, namedRun, namedVal⟩ := sized_count_spec context good kind below low high 0#usize 0#usize
    (by simp [bound])
  have namedIs : named.val = sizedNamedCount context.values.val kind below low.val high.val := by
    rw [namedVal]; simp
  have namedLe : named.val ≤ Usize.max := by scalar_tac
  obtain ⟨room, roomRun, roomVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := core.num.Usize.MAX) (y := named)
    (by rw [Rowl.LengthCounts.usize_max_val]; exact namedLe))
  have roomIs : room.val = Usize.max - named.val := by
    rw [roomVal.1, Rowl.LengthCounts.usize_max_val]
  by_cases fits : capacity.val < room.val
  · have fits' : capacity < room := by rw [UScalar.lt_equiv]; exact fits
    obtain ⟨sum, sumRun, sumVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := capacity) (y := named) (by omega))
    have sumIs : sum.val = capacity.val + named.val := by simpa using sumVal
    obtain ⟨cap, capRun, capVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := sum) (y := 1#usize) (by scalar_tac))
    have capIs : cap.val = capacity.val + named.val + 1 := by rw [← sumIs]; simpa using capVal
    obtain ⟨res, resRun, resVal⟩ := Rowl.LengthCounts.slot_size_spec octets first last low high cap
    cases res with
    | none =>
      exact ⟨none, by simp [namedRun, roomRun, fits, fits', sumRun, capRun, resRun], fun out' h => nomatch h⟩
    | some size =>
      have sizeIs := resVal size rfl
      by_cases under : size.val < cap.val
      · have under' : size < cap := by rw [UScalar.lt_equiv]; exact under
        have total : sizedTotal octets first.val last.val low.val high.val = size.val := by
          unfold sizedTotal
          rw [sizeIs] at under ⊢
          unfold capAt at under ⊢
          omega
        obtain ⟨free, freeRun, freeVal⟩ : ∃ f : Usize,
            (if named.val ≤ size.val then size - named else ok 0#usize : Result Usize) = .ok f ∧
            f.val = sizedFree context kind below octets first.val last.val low.val high.val := by
          by_cases h : named.val ≤ size.val
          · obtain ⟨d, dRun, dVal⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := size) (y := named) h)
            exact ⟨d, by simp [h, dRun], by rw [dVal.1, sizedFree, total, namedIs]⟩
          · exact ⟨0#usize, by simp [h], by
              simp only [sizedFree]; rw [total, ← namedIs]; simp; omega⟩
        have freeKernel : (if named <= size then size - named else ok 0#usize : Result Usize) = .ok free := by
          simpa [UScalar.le_equiv] using freeRun
        have fewer : sizedTotal octets first.val last.val low.val high.val ≤
            capacity.val + sizedNamedCount context.values.val kind below low.val high.val := by
          rw [total, ← namedIs]
          omega
        obtain ⟨found, foundRun, members0⟩ := sized_literals_spec context good kind below low high 0#usize none
          (by simp [namedList])
        have members : ∀ a, a ∈ namedList found ↔ ∃ (i : Usize) (_ : i.val < context.values.val.length),
            SizedValue kind below low.val high.val context.values.val[i.val] ∧ a = .Named (valueIndividual i) := by
          intro a
          rw [members0 a]
          simp [namedList]
        obtain ⟨scRun, scMeans⟩ := sized_class_spec.{w,x} kind below lowIndex highIndex
        generalize sizedClass kind below lowIndex highIndex = sc at scRun scMeans
        by_cases zero : free.val = 0
        · have zero' : free = 0#usize := UScalar.eq_of_val_eq (by simpa using zero)
          have none' : sizedFree context kind below octets first.val last.val low.val high.val = 0 := by
            rw [← freeVal]; exact zero
          cases found with
          | none =>
            obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf sc (.ObjectComplementOf sc))
            refine ⟨r, by simp [namedRun, roomRun, fits, fits', sumRun, capRun, resRun, under, under', freeKernel, foundRun, zero',
              scRun, data_ontology.not, run, freeRun], fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
            have nothing : ∀ y, ¬ SizedNamed context J kind below low.val high.val y :=
              fun y named => by simpa [namedList] using (sized_named_iff members y).mpr named
            simp only [List.mem_singleton, forall_eq, satisfies, classDenote, scMeans]
            constructor
            · intro holds _
              exact ⟨fun _ y inS => absurd inS (holds y inS), fun pos => absurd none' (by omega)⟩
            · intro holds y inS
              exact (nothing y ((holds fewer).1 none' y inS)).elim
          | some list =>
            obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf sc (.ObjectOneOf list))
            refine ⟨r, by simp [namedRun, roomRun, fits, fits', sumRun, capRun, resRun, under, under', freeKernel, foundRun, zero',
              scRun, run, freeRun], fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
            have iff := sized_named_iff (J := J) members
            simp only [namedList] at iff
            simp only [List.mem_singleton, forall_eq, satisfies, classDenote, scMeans]
            constructor
            · intro holds _
              exact ⟨fun _ y inS => (iff y).mp (holds y inS), fun pos => absurd none' (by omega)⟩
            · intro holds y inS
              exact (iff y).mpr ((holds fewer).1 none' y inS)
        · have zero' : free ≠ 0#usize := fun h => zero (by rw [h]; rfl)
          obtain ⟨n, nRun, nValue⟩ := natural_of_spec free
          have exact : sizedFree context kind below octets first.val last.val low.val high.val = free.val :=
            freeVal.symm
          have tail : ∀ filler : ClassExpression, (∀ {Object' : Type w} {Value' : Type x}
              (J : Interpretation Object' Value') (y : Object'), classDenote J filler y ↔
                InSized J kind below lowIndex highIndex y ∧ ¬ SizedNamed context J kind below low.val high.val y) →
              ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
                ((∀ b ∈ ([⟨alloc.vec.Vec.new Annotation, Axiom.SubClassOf (.Class thing)
                  (.ObjectMaxCardinality n (.Property dataSuper) (some filler))⟩] : List AnnotatedAxiom),
                    satisfies J b.axiom) ↔
                  SizedFact context capacity.val J kind below octets first.val last.val lowIndex highIndex low.val
                    high.val) := by
            intro filler fillerMeans Object' Value' J
            have eq : ∀ y y', (J.objectProperties dataSuper y y' ∧ classDenote J filler y') ↔
                (J.objectProperties dataSuper y y' ∧ InSized J kind below lowIndex highIndex y' ∧
                  ¬ SizedNamed context J kind below low.val high.val y') :=
              fun y y' => and_congr Iff.rfl (fillerMeans J y')
            simp only [List.mem_singleton, forall_eq, satisfies, classDenote, objectRelation, nValue]
            constructor
            · intro holds _
              refine ⟨fun z => absurd (exact ▸ z) zero, fun _ y thing' => ?_⟩
              rw [exact]
              have := holds y thing'
              simp only [eq] at this
              exact this
            · intro holds y thing'
              have fact := (holds fewer).2 (by omega) y thing'
              rw [exact] at fact
              simp only [eq]
              exact fact
          cases found with
          | none =>
            have fillerMeans : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value')
                (y : Object'), classDenote J sc y ↔ InSized J kind below lowIndex highIndex y ∧
                  ¬ SizedNamed context J kind below low.val high.val y := by
              intro Object' Value' J y
              have nothing : ¬ SizedNamed context J kind below low.val high.val y :=
                fun named => by simpa [namedList] using (sized_named_iff members y).mpr named
              simp [scMeans, nothing]
            obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.Class thing)
              (.ObjectMaxCardinality n (.Property dataSuper) (some sc)))
            refine ⟨r, by simp [namedRun, roomRun, fits, fits', sumRun, capRun, resRun, under, under', freeKernel, foundRun, zero',
              scRun, thing_eq, nRun, data_super_eq, run, freeRun], fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
            exact tail sc fillerMeans J
          | some list =>
            have fillerMeans : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value')
                (y : Object'), classDenote J (.ObjectIntersectionOf ⟨sc, .ObjectComplementOf (.ObjectOneOf list),
                  alloc.vec.Vec.new ClassExpression⟩) y ↔ InSized J kind below lowIndex highIndex y ∧
                  ¬ SizedNamed context J kind below low.val high.val y := by
              intro Object' Value' J y
              have iff := sized_named_iff (J := J) members y
              simp only [namedList] at iff
              rw [and_class_iff]
              simp only [classDenote, scMeans, ← iff]
            obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.Class thing)
              (.ObjectMaxCardinality n (.Property dataSuper) (some (.ObjectIntersectionOf ⟨sc,
                .ObjectComplementOf (.ObjectOneOf list), alloc.vec.Vec.new ClassExpression⟩))))
            refine ⟨r, by simp [namedRun, roomRun, fits, fits', sumRun, capRun, resRun, under, under', freeKernel, foundRun, zero',
              scRun, data_ontology.not, data_ontology.and, thing_eq, nRun, data_super_eq, run, freeRun],
              fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
            exact tail _ fillerMeans J
      · have under' : ¬ size < cap := by rw [UScalar.lt_equiv]; exact under
        refine ⟨some out, by simp [namedRun, roomRun, fits, fits', sumRun, capRun, resRun, under, under'],
          fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
        simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
        intro lt
        rw [← namedIs] at lt
        have : capacity.val + named.val + 1 ≤ sizedTotal octets first.val last.val low.val high.val := by
          unfold sizedTotal
          rw [sizeIs, capIs] at under
          unfold capAt at under
          omega
        omega
  · have fits' : ¬ capacity < room := by rw [UScalar.lt_equiv]; exact fits
    exact ⟨none, by simp [namedRun, roomRun, fits, fits'], fun out' h => nomatch h⟩

/-! ### The strings by rank -/

/-- The kinds of the chain of `xsd:string` by rank (`data_ontology::chain_kind`):
    `xsd:string`, `xsd:normalizedString`, `xsd:token`, `xsd:NMTOKEN`,
    `xsd:Name`, `xsd:NCName` and `xsd:language`. -/
def rankKind : ℕ → datatypes.Kind
  | 0 => .String
  | 1 => .NormalizedString
  | 2 => .Token
  | 3 => .NmToken
  | 4 => .Name
  | 5 => .NcName
  | _ => .Language

theorem rank_kind_eq (rank : U8) (h : rank.val < 7) : data_ontology.chain_kind rank = .ok (rankKind rank.val) := by
  obtain ⟨⟨⟨n, hn⟩⟩⟩ := rank
  have hv : n < 7 := h
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6) with e | e | e | e | e | e | e <;>
    subst e <;> rfl

/-- The first rank from `rank` on whose kind is in use, or 7. -/
def nextRank (kinds : data_ontology.Kinds) (rank : ℕ) : ℕ :=
  if rank < 7 then (if Used kinds (rankKind rank) = true then rank else nextRank kinds (rank + 1)) else 7
termination_by 7 - rank

theorem next_rank_spec (kinds : data_ontology.Kinds) (rank : U8) (h : rank.val ≤ 7) :
    ∃ r : U8, data_ontology.next_rank kinds rank = .ok r ∧ r.val = nextRank kinds rank.val := by
  rw [data_ontology.next_rank, nextRank]
  by_cases inside : rank.val < 7
  · have inside' : rank < 7#u8 := by rw [UScalar.lt_equiv]; simpa using inside
    by_cases use : Used kinds (rankKind rank.val) = true
    · exact ⟨rank, by simp [inside', rank_kind_eq rank inside, used_eq, use], by simp [inside, use]⟩
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (U8.add_spec (x := rank) (y := 1#u8) (by scalar_tac))
      have nextIs : next.val = rank.val + 1 := by simpa using nextValue
      obtain ⟨r, run, val⟩ := next_rank_spec kinds next (by omega)
      refine ⟨r, by simp [inside', rank_kind_eq rank inside, used_eq, use, advance, run], ?_⟩
      rw [val, nextIs]
      simp [inside, use]
  · have inside' : ¬ rank < 7#u8 := by rw [UScalar.lt_equiv]; simpa using inside
    exact ⟨7#u8, by simp [inside'], by simp [inside]⟩
termination_by 7 - rank.val
decreasing_by simp at nextValue; omega

theorem nextRank_ge (kinds : data_ontology.Kinds) (rank : ℕ) : rank ≤ nextRank kinds rank ∨ nextRank kinds rank = 7 := by
  rw [nextRank]
  split_ifs with h1 h2
  · exact .inl le_rfl
  · rcases nextRank_ge kinds (rank + 1) with h | h
    · exact .inl (by omega)
    · exact .inr h
  · exact .inr rfl
termination_by 7 - rank

theorem nextRank_le (kinds : data_ontology.Kinds) (rank : ℕ) : nextRank kinds rank ≤ 7 := by
  rw [nextRank]
  split_ifs with h1 h2
  · omega
  · exact nextRank_le kinds (rank + 1)
  · exact le_rfl
termination_by 7 - rank

theorem nextRank_used (kinds : data_ontology.Kinds) (rank : ℕ) (h : nextRank kinds rank < 7) :
    Used kinds (rankKind (nextRank kinds rank)) = true := by
  rw [nextRank] at h ⊢
  split_ifs at h ⊢ with h1 h2
  · exact h2
  · exact nextRank_used kinds (rank + 1) h
  · omega
termination_by 7 - rank

theorem nextRank_skips (kinds : data_ontology.Kinds) (rank r : ℕ) (low : rank ≤ r) (high : r < nextRank kinds rank) :
    Used kinds (rankKind r) = false := by
  rw [nextRank] at high
  split_ifs at high with h1 h2
  · omega
  · rcases Nat.eq_or_lt_of_le low with same | after
    · subst same; simpa using h2
    · exact nextRank_skips kinds (rank + 1) r (by omega) high
  · have := nextRank_le kinds rank
    omega
termination_by 7 - rank

/-- The kind of the next rank in use after a rank, if any. -/
def belowKind (kinds : data_ontology.Kinds) (rank : ℕ) : Option datatypes.Kind :=
  if nextRank kinds (rank + 1) < 7 then some (rankKind (nextRank kinds (rank + 1))) else none

/-- What the axioms on the strings of each rank in use from `rank` on, up to
    the next rank in use, with a slot of lengths, say. -/
def RankFacts (context : data_ontology.Context) (capacity : ℕ) (J : Interpretation Object' Value') (rank : ℕ)
    (lowIndex highIndex : Option Usize) (low high : ℕ) : Prop :=
  ∀ r, rank ≤ r → r < 7 → Used context.kinds (rankKind r) = true →
    SizedFact context capacity J (rankKind r) (belowKind context.kinds r) false r (nextRank context.kinds (r + 1))
      lowIndex highIndex low high

theorem rank_axioms_spec (context : data_ontology.Context) (good : Good context) (rank : U8) (h : rank.val ≤ 7)
    (lowIndex highIndex : Option Usize) (low high capacity : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.rank_axioms context rank lowIndex highIndex low high capacity out = .ok res ∧
      ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔
            RankFacts context capacity.val J rank.val lowIndex highIndex low.val high.val) := by
  rw [data_ontology.rank_axioms]
  by_cases inside : rank.val < 7
  · have inside' : rank < 7#u8 := by rw [UScalar.lt_equiv]; simpa using inside
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (U8.add_spec (x := rank) (y := 1#u8) (by scalar_tac))
    have nextIs : next.val = rank.val + 1 := by simpa using nextValue
    by_cases use : Used context.kinds (rankKind rank.val) = true
    · obtain ⟨last, lastRun, lastVal⟩ := next_rank_spec context.kinds next (by omega)
      have lastLe := nextRank_le context.kinds next.val
      obtain ⟨below, belowRun, belowIs⟩ : ∃ below : Option datatypes.Kind,
          (if last < 7#u8 then (do let k1 ← data_ontology.chain_kind last; ok (some k1)) else ok none :
            Result (Option datatypes.Kind)) = .ok below ∧ below = belowKind context.kinds rank.val := by
        by_cases small : last.val < 7
        · have small' : last < 7#u8 := by rw [UScalar.lt_equiv]; simpa using small
          refine ⟨some (rankKind last.val), by simp [small', rank_kind_eq last small], ?_⟩
          rw [belowKind, ← nextIs, ← lastVal, if_pos small]
        · have small' : ¬ last < 7#u8 := by rw [UScalar.lt_equiv]; simpa using small
          refine ⟨none, by simp [small'], ?_⟩
          rw [belowKind, ← nextIs, ← lastVal, if_neg small]
      have lastIs : last.val = nextRank context.kinds (rank.val + 1) := by rw [lastVal, nextIs]
      obtain ⟨r1, run1, f1⟩ := sized_axiom_spec context good (rankKind rank.val) below false rank last lowIndex
        highIndex low high capacity out
      have start : (data_ontology.chain_kind rank : Result datatypes.Kind) = .ok (rankKind rank.val) :=
        rank_kind_eq rank inside
      cases r1 with
      | none =>
        refine ⟨none, ?_, fun out' h => nomatch h⟩
        simp only [inside', ↓reduceIte, start, bind_ok, used_eq, use, advance, lastRun]
        rw [belowRun]
        simp only [bind_ok, run1]
      | some o1 =>
        obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
        obtain ⟨r2, run2, f2⟩ := rank_axioms_spec context good next (by omega) lowIndex highIndex low high
          capacity o1
        refine ⟨r2, ?_, fun out' h => ?_⟩
        · simp only [inside', ↓reduceIte, start, bind_ok, used_eq, use, advance, lastRun]
          rw [belowRun]
          simp only [bind_ok, run1, run2]
        obtain ⟨n2, c2, m2⟩ := f2 out' h
        refine ⟨n1 ++ n2, by rw [c2, c1]; simp, fun J => ?_⟩
        rw [List.forall_mem_append, m1 J, m2 J, nextIs, belowIs, lastIs]
        constructor
        · rintro ⟨here, later⟩ r low' high' used'
          rcases Nat.eq_or_lt_of_le low' with same | after
          · subst same; exact here
          · exact later r (by omega) high' used'
        · intro all
          exact ⟨all rank.val le_rfl inside use, fun r low' high' used' => all r (by omega) high' used'⟩
    · obtain ⟨r2, run2, f2⟩ := rank_axioms_spec context good next (by omega) lowIndex highIndex low high
        capacity out
      have use' : Used context.kinds (rankKind rank.val) = false := by simpa using use
      refine ⟨r2, by simp [inside', rank_kind_eq rank inside, used_eq, use', advance, run2], fun out' h => ?_⟩
      obtain ⟨n2, c2, m2⟩ := f2 out' h
      refine ⟨n2, c2, fun J => ?_⟩
      rw [m2 J, nextIs]
      constructor
      · intro later r low' high' used'
        rcases Nat.eq_or_lt_of_le low' with same | after
        · subst same; rw [use'] at used'; cases used'
        · exact later r (by omega) high' used'
      · intro all r low' high' used'
        exact all r (by omega) high' used'
  · have inside' : ¬ rank < 7#u8 := by rw [UScalar.lt_equiv]; simpa using inside
    refine ⟨some out, by simp [inside'], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    intro r low' high'
    omega
termination_by 7 - rank.val
decreasing_by all_goals (simp at nextValue; omega)

/-! ### The axioms of a slot of lengths -/

/-- What the axioms on the values of each kind in use with the length facets
    but `rdf:PlainLiteral` with a slot of lengths say: the strings by rank, the
    IRIs as strings of every rank, and the octet sequences. -/
def SlotFacts (context : data_ontology.Context) (capacity : ℕ) (J : Interpretation Object' Value')
    (lowIndex highIndex : Option Usize) (low high : ℕ) : Prop :=
  RankFacts context capacity J 0 lowIndex highIndex low high ∧
  (Used context.kinds .AnyUri = true →
    SizedFact context capacity J .AnyUri none false 0 7 lowIndex highIndex low high) ∧
  (Used context.kinds .HexBinary = true →
    SizedFact context capacity J .HexBinary none true 0 0 lowIndex highIndex low high) ∧
  (Used context.kinds .Base64Binary = true →
    SizedFact context capacity J .Base64Binary none true 0 0 lowIndex highIndex low high)

theorem kind_axiom_spec (context : data_ontology.Context) (good : Good context) (kind : datatypes.Kind)
    (octets : Bool) (first last : U8) (lowIndex highIndex : Option Usize) (low high capacity : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.kind_axiom context kind octets first last lowIndex highIndex low high capacity out = .ok res ∧
      ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ (Used context.kinds kind = true →
            SizedFact context capacity.val J kind none octets first.val last.val lowIndex highIndex low.val high.val)) := by
  rw [data_ontology.kind_axiom, used_eq]
  by_cases use : Used context.kinds kind = true
  · obtain ⟨r, run, f⟩ := sized_axiom_spec context good kind none octets first last lowIndex highIndex low high
      capacity out
    refine ⟨r, by simp [use, run], fun out' h => ?_⟩
    obtain ⟨n, c, m⟩ := f out' h
    exact ⟨n, c, fun J => by rw [m J]; simp [use]⟩
  · have use' : Used context.kinds kind = false := by simpa using use
    refine ⟨some out, by simp [use'], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp [use']

theorem slot_axioms_spec (context : data_ontology.Context) (good : Good context) (lowIndex highIndex : Option Usize)
    (low high capacity : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.slot_axioms context lowIndex highIndex low high capacity out = .ok res ∧
      ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ SlotFacts context capacity.val J lowIndex highIndex low.val high.val) := by
  rw [data_ontology.slot_axioms]
  obtain ⟨r1, run1, f1⟩ := rank_axioms_spec context good 0#u8 (by simp) lowIndex highIndex low high capacity out
  cases r1 with
  | none => exact ⟨none, by simp [run1], fun out' h => nomatch h⟩
  | some o1 =>
    obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
    obtain ⟨r2, run2, f2⟩ := kind_axiom_spec context good .AnyUri false 0#u8 7#u8 lowIndex highIndex low high
      capacity o1
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], fun out' h => nomatch h⟩
    | some o2 =>
      obtain ⟨n2, c2, m2⟩ := f2 o2 rfl
      obtain ⟨r3, run3, f3⟩ := kind_axiom_spec context good .HexBinary true 0#u8 0#u8 lowIndex highIndex low high
        capacity o2
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], fun out' h => nomatch h⟩
      | some o3 =>
        obtain ⟨n3, c3, m3⟩ := f3 o3 rfl
        obtain ⟨r4, run4, f4⟩ := kind_axiom_spec context good .Base64Binary true 0#u8 0#u8 lowIndex highIndex low
          high capacity o3
        refine ⟨r4, by simp [run1, run2, run3, run4], fun out' h => ?_⟩
        obtain ⟨n4, c4, m4⟩ := f4 out' h
        refine ⟨n1 ++ n2 ++ n3 ++ n4, by rw [c4, c3, c2, c1]; simp, fun J => ?_⟩
        simp only [List.forall_mem_append, and_assoc]
        rw [m1 J, m2 J, m3 J, m4 J]
        exact Iff.rfl

/-! ### The lengths -/

theorem length_between_spec (lengths : alloc.vec.Vec Usize) (low high index : Usize) :
    data_ontology.length_between lengths low high index =
      .ok (decide (∃ t ∈ lengths.val.drop index.val, low.val < t.val ∧ t.val < high.val)) := by
  rw [data_ontology.length_between]
  by_cases inside : index.val < lengths.val.length
  · have lookup : lengths.index_usize index = .ok lengths.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have ih := length_between_spec lengths low high next
    rw [nextIs] at ih
    have split : (∃ t ∈ lengths.val.drop index.val, low.val < t.val ∧ t.val < high.val) ↔
        (low.val < lengths.val[index.val].val ∧ lengths.val[index.val].val < high.val) ∨
          ∃ t ∈ lengths.val.drop (index.val + 1), low.val < t.val ∧ t.val < high.val := by
      rw [List.drop_eq_getElem_cons inside]
      simp only [List.mem_cons, exists_eq_or_imp]
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
      bind_ok, advance, ih]
    simp only [split]
    by_cases here : low.val < lengths.val[index.val].val ∧ lengths.val[index.val].val < high.val <;> simp [here]
  · simp [UScalar.lt_equiv, inside, List.drop_eq_nil_iff.mpr (show lengths.val.length ≤ index.val by omega)]
termination_by lengths.val.length - index.val
decreasing_by simp at nextValue; omega

theorem length_below_spec (lengths : alloc.vec.Vec Usize) (length index : Usize) :
    data_ontology.length_below lengths length index =
      .ok (decide (∃ t ∈ lengths.val.drop index.val, t.val < length.val)) := by
  rw [data_ontology.length_below]
  by_cases inside : index.val < lengths.val.length
  · have lookup : lengths.index_usize index = .ok lengths.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have ih := length_below_spec lengths length next
    rw [nextIs] at ih
    have split : (∃ t ∈ lengths.val.drop index.val, t.val < length.val) ↔
        lengths.val[index.val].val < length.val ∨ ∃ t ∈ lengths.val.drop (index.val + 1), t.val < length.val := by
      rw [List.drop_eq_getElem_cons inside]
      simp only [List.mem_cons, exists_eq_or_imp]
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
      bind_ok, advance, ih]
    simp only [split]
    by_cases here : lengths.val[index.val].val < length.val <;> simp [here]
  · simp [UScalar.lt_equiv, inside, List.drop_eq_nil_iff.mpr (show lengths.val.length ≤ index.val by omega)]
termination_by lengths.val.length - index.val
decreasing_by simp at nextValue; omega

/-- The class of the length at `first` inside the class of the length at
    `second` when that is shorter. -/
def InclusionFact (context : data_ontology.Context) (J : Interpretation Object' Value') (first second : Usize) :
    Prop :=
  ∀ (h1 : first.val < context.lengths.val.length) (h2 : second.val < context.lengths.val.length),
    (context.lengths.val[second.val]'h2).val < (context.lengths.val[first.val]'h1).val →
      ∀ y, J.classes (lengthClass first) y → J.classes (lengthClass second) y

/-- The axioms on the values from the length at `first` on and before the
    length at `second`, when that is the next length above it. -/
def NeighbourFact (context : data_ontology.Context) (capacity : ℕ) (J : Interpretation Object' Value')
    (first second : Usize) : Prop :=
  ∀ (h1 : first.val < context.lengths.val.length) (h2 : second.val < context.lengths.val.length),
    (context.lengths.val[first.val]'h1).val < (context.lengths.val[second.val]'h2).val →
    (¬ ∃ t ∈ context.lengths.val, (context.lengths.val[first.val]'h1).val < t.val ∧
      t.val < (context.lengths.val[second.val]'h2).val) →
    SlotFacts context capacity J (some first) (some second) (context.lengths.val[first.val]'h1).val
      (context.lengths.val[second.val]'h2).val

/-- The axioms on the values shorter than the least length, the length at
    `index`, when that is not zero. -/
def LowestFact (context : data_ontology.Context) (capacity : ℕ) (J : Interpretation Object' Value') (index : Usize) :
    Prop :=
  ∀ (h : index.val < context.lengths.val.length), 0 < (context.lengths.val[index.val]'h).val →
    (¬ ∃ t ∈ context.lengths.val, t.val < (context.lengths.val[index.val]'h).val) →
    SlotFacts context capacity J none (some index) 0 (context.lengths.val[index.val]'h).val

/-- What the axioms of the lengths say. -/
def LengthFacts (context : data_ontology.Context) (capacity : ℕ) (J : Interpretation Object' Value') : Prop :=
  ∀ first : Usize, first.val < context.lengths.val.length →
    (∀ second : Usize, second.val < context.lengths.val.length →
      InclusionFact context J first second ∧ NeighbourFact context capacity J first second) ∧
    LowestFact context capacity J first

theorem length_inclusion_spec (context : data_ontology.Context) (first second : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.length_inclusion context first second out = .ok res ∧
      ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ InclusionFact context J first second) := by
  rw [data_ontology.length_inclusion]
  by_cases inside : first.val < context.lengths.val.length ∧ second.val < context.lengths.val.length
  · obtain ⟨h1, h2⟩ := inside
    have look1 : context.lengths.index_usize first = .ok context.lengths.val[first.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h1]
    have look2 : context.lengths.index_usize second = .ok context.lengths.val[second.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h2]
    by_cases shorter : context.lengths.val[second.val].val < context.lengths.val[first.val].val
    · obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.Class (lengthClass first)) (.Class (lengthClass second)))
      refine ⟨r, by simp [UScalar.lt_equiv, h1, h2, alloc.vec.Vec.index_slice_index, look1, look2, shorter,
        length_class_eq, run], fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
      simp only [List.mem_singleton, forall_eq, satisfies, classDenote, InclusionFact]
      constructor
      · intro holds _ _ _ y inFirst
        exact holds y inFirst
      · intro holds y inFirst
        exact holds h1 h2 shorter y inFirst
    · refine ⟨some out, by simp [UScalar.lt_equiv, h1, h2, alloc.vec.Vec.index_slice_index, look1, look2, shorter],
        fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
      simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, InclusionFact]
      intro _ _ lt
      exact absurd lt shorter
  · refine ⟨some out, by simp only [not_and_or] at inside; rcases inside with h | h <;> simp [UScalar.lt_equiv, h],
      fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, InclusionFact]
    intro h1 h2
    exact absurd ⟨h1, h2⟩ inside

theorem length_neighbours_spec (context : data_ontology.Context) (good : Good context) (capacity first second : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.length_neighbours context capacity first second out = .ok res ∧
      ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ NeighbourFact context capacity.val J first second) := by
  rw [data_ontology.length_neighbours]
  by_cases inside : first.val < context.lengths.val.length ∧ second.val < context.lengths.val.length
  · obtain ⟨h1, h2⟩ := inside
    have look1 : context.lengths.index_usize first = .ok context.lengths.val[first.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h1]
    have look2 : context.lengths.index_usize second = .ok context.lengths.val[second.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h2]
    have between := length_between_spec context.lengths context.lengths.val[first.val]
      context.lengths.val[second.val] 0#usize
    simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at between
    by_cases next : context.lengths.val[first.val].val < context.lengths.val[second.val].val ∧
        ¬ ∃ t ∈ context.lengths.val, context.lengths.val[first.val].val < t.val ∧
          t.val < context.lengths.val[second.val].val
    · obtain ⟨r, run, f⟩ := slot_axioms_spec context good (some first) (some second) context.lengths.val[first.val]
        context.lengths.val[second.val] capacity out
      refine ⟨r, by simp [UScalar.lt_equiv, h1, h2, alloc.vec.Vec.index_slice_index, look1, look2, between, next.1,
        next.2, run], fun out' h => ?_⟩
      obtain ⟨n, c, m⟩ := f out' h
      refine ⟨n, c, fun J => ?_⟩
      rw [m J, NeighbourFact]
      exact ⟨fun holds _ _ _ _ => holds, fun holds => holds h1 h2 next.1 next.2⟩
    · refine ⟨some out, ?_, fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
      · simp only [not_and_or, not_not] at next
        rcases next with n1 | n2
        · simp [UScalar.lt_equiv, h1, h2, alloc.vec.Vec.index_slice_index, look1, look2, between, n1]
        · simp [UScalar.lt_equiv, h1, h2, alloc.vec.Vec.index_slice_index, look1, look2, between, n2]
      · simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, NeighbourFact]
        intro _ _ lt none
        exact absurd ⟨lt, none⟩ next
  · refine ⟨some out, by simp only [not_and_or] at inside; rcases inside with h | h <;> simp [UScalar.lt_equiv, h],
      fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, NeighbourFact]
    intro h1 h2
    exact absurd ⟨h1, h2⟩ inside

theorem length_pairs_spec (context : data_ontology.Context) (good : Good context) (capacity first second : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.length_pairs context capacity first second out = .ok res ∧
      ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ s : Usize, second.val ≤ s.val → s.val < context.lengths.val.length →
            InclusionFact context J first s ∧ NeighbourFact context capacity.val J first s) := by
  rw [data_ontology.length_pairs]
  by_cases inside : second.val < context.lengths.val.length
  · obtain ⟨r1, run1, f1⟩ := length_inclusion_spec context first second out
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, run1], fun out' h => nomatch h⟩
    | some o1 =>
      obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
      obtain ⟨r2, run2, f2⟩ := length_neighbours_spec context good capacity first second o1
      cases r2 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, run1, run2], fun out' h => nomatch h⟩
      | some o2 =>
        obtain ⟨n2, c2, m2⟩ := f2 o2 rfl
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := second) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = second.val + 1 := by simpa using nextValue
        obtain ⟨r3, run3, f3⟩ := length_pairs_spec context good capacity first next o2
        refine ⟨r3, by simp [UScalar.lt_equiv, inside, run1, run2, advance, run3], fun out' h => ?_⟩
        obtain ⟨n3, c3, m3⟩ := f3 out' h
        refine ⟨n1 ++ n2 ++ n3, by rw [c3, c2, c1]; simp, fun J => ?_⟩
        simp only [List.forall_mem_append]
        rw [m1 J, m2 J, m3 J, nextIs]
        constructor
        · rintro ⟨⟨incl, neigh⟩, later⟩ s low' high'
          by_cases same : s = second
          · subst same; exact ⟨incl, neigh⟩
          · have : s.val ≠ second.val := fun e => same (UScalar.eq_of_val_eq e)
            exact later s (by omega) high'
        · intro all
          exact ⟨⟨(all second le_rfl inside).1, (all second le_rfl inside).2⟩,
            fun s low' high' => all s (by omega) high'⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    intro s low' high'
    omega
termination_by context.lengths.val.length - second.val
decreasing_by simp at nextValue; omega

theorem length_lowest_spec (context : data_ontology.Context) (good : Good context) (capacity index : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.length_lowest context capacity index out = .ok res ∧
      ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ LowestFact context capacity.val J index) := by
  rw [data_ontology.length_lowest]
  by_cases inside : index.val < context.lengths.val.length
  · have look : context.lengths.index_usize index = .ok context.lengths.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have below := length_below_spec context.lengths context.lengths.val[index.val] 0#usize
    simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at below
    by_cases least : 0 < context.lengths.val[index.val].val ∧
        ¬ ∃ t ∈ context.lengths.val, t.val < context.lengths.val[index.val].val
    · obtain ⟨r, run, f⟩ := slot_axioms_spec context good none (some index) 0#usize context.lengths.val[index.val]
        capacity out
      refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, look, below, least.1, least.2,
        run], fun out' h => ?_⟩
      obtain ⟨n, c, m⟩ := f out' h
      refine ⟨n, c, fun J => ?_⟩
      rw [m J, LowestFact]
      simp only [show (0#usize : Usize).val = 0 from rfl]
      exact ⟨fun holds _ _ _ => holds, fun holds => holds inside least.1 least.2⟩
    · refine ⟨some out, ?_, fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
      · simp only [not_and_or, not_not] at least
        rcases least with n1 | n2
        · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, look, below, n1]
        · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, look, below, n2]
      · simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, LowestFact]
        intro _ pos none
        exact absurd ⟨pos, none⟩ least
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, LowestFact]
    intro h
    exact absurd h inside

theorem length_axioms_spec (context : data_ontology.Context) (good : Good context) (capacity index : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.length_axioms context capacity index out = .ok res ∧
      ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ first : Usize, index.val ≤ first.val →
            first.val < context.lengths.val.length →
            (∀ second : Usize, second.val < context.lengths.val.length →
              InclusionFact context J first second ∧ NeighbourFact context capacity.val J first second) ∧
            LowestFact context capacity.val J first) := by
  rw [data_ontology.length_axioms]
  by_cases inside : index.val < context.lengths.val.length
  · obtain ⟨r1, run1, f1⟩ := length_pairs_spec context good capacity index 0#usize out
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, run1], fun out' h => nomatch h⟩
    | some o1 =>
      obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
      obtain ⟨r2, run2, f2⟩ := length_lowest_spec context good capacity index o1
      cases r2 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, run1, run2], fun out' h => nomatch h⟩
      | some o2 =>
        obtain ⟨n2, c2, m2⟩ := f2 o2 rfl
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = index.val + 1 := by simpa using nextValue
        obtain ⟨r3, run3, f3⟩ := length_axioms_spec context good capacity next o2
        refine ⟨r3, by simp [UScalar.lt_equiv, inside, run1, run2, advance, run3], fun out' h => ?_⟩
        obtain ⟨n3, c3, m3⟩ := f3 out' h
        refine ⟨n1 ++ n2 ++ n3, by rw [c3, c2, c1]; simp, fun J => ?_⟩
        simp only [List.forall_mem_append]
        rw [m1 J, m2 J, m3 J, nextIs]
        simp only [show (0#usize : Usize).val = 0 from rfl, Nat.zero_le, true_implies]
        constructor
        · rintro ⟨⟨pairs, lowest⟩, later⟩ first low' high'
          by_cases same : first = index
          · subst same; exact ⟨pairs, lowest⟩
          · have : first.val ≠ index.val := fun e => same (UScalar.eq_of_val_eq e)
            exact later first (by omega) high'
        · intro all
          exact ⟨⟨(all index le_rfl inside).1, (all index le_rfl inside).2⟩,
            fun first low' high' => all first (by omega) high'⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    intro first low' high'
    omega
termination_by context.lengths.val.length - index.val
decreasing_by simp at nextValue; omega

/-- The axioms of the lengths: their classes inside each other as the lengths
    are ordered, and the axioms on the values of each slot of lengths. -/
theorem length_facts_spec (context : data_ontology.Context) (good : Good context) (capacity : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.length_axioms context capacity 0#usize out = .ok res ∧
      ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ LengthFacts context capacity.val J) := by
  obtain ⟨r, run, f⟩ := length_axioms_spec context good capacity 0#usize out
  refine ⟨r, run, fun out' h => ?_⟩
  obtain ⟨n, c, m⟩ := f out' h
  refine ⟨n, c, fun J => ?_⟩
  rw [m J, LengthFacts]
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.zero_le, true_implies]

end Rowl.DataLengths
