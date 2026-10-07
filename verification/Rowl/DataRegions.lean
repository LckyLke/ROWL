import Rowl.DataAxioms

/-!
The axioms that `data_ontology` adds for ordered numbers. When a datatype
restriction or a subtype of `xsd:integer` is in use, every cut of the context
gets a class; the kernel lists the cuts in order (`Rowl.Regions.cut_order_spec`)
and adds: the first cut's class inside the reals, each cut's class inside the
one before it, the two cuts of a number leaving only its literal value's
individual, and, when the integers are in use, the integers between two
neighbouring cuts of different numbers none at all, or at most their number at
any element along a role `U` above every data property's role when there are
fewer of them than the counts of the data restrictions together
(`region_axioms_spec`, `RegionFacts`).
-/
namespace Rowl.DataRegions
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.Regions (cutAt Ordered FineCuts firstIn lastOutside)
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

/-- What the axiom on the integers between two neighbouring cuts of different
    numbers says: none of them when there are none, and at most their number
    at any element along `U` when there are fewer than the capacity. -/
def GapFact (context : data_ontology.Context) (capacity : Nat) (J : Interpretation Object' Value')
    (low high : Usize) : Prop :=
  (runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) = 0 →
    ∀ y, J.classes (kindClass .Integer) y → J.classes (cutClass low) y → J.classes (cutClass high) y) ∧
  (0 < runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) →
    runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) < capacity →
    ∀ y, J.classes thing y → AtMost (runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val))
      (fun y' => J.objectProperties dataSuper y y' ∧ InRun J low high y'))

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

theorem cutAt_val {cuts : alloc.vec.Vec regions.Cut} {i : Usize} (h : i.val < cuts.val.length) :
    cutAt cuts.val i.val = cuts.val[i.val] := Rowl.Regions.cutAt_eq _ _ h

theorem fit_widths {a b : regions.Cut} (fa : Rowl.Regions.Fit a) (fb : Rowl.Regions.Fit b) :
    Rowl.Datatypes.digitWidth a.value + Rowl.Datatypes.digitWidth b.value + 32 < Usize.max := by
  have := fa.2; have := fb.2
  have : 64 ≤ Usize.max := by scalar_tac
  omega

/-- The axiom on the integers between two neighbouring cuts. -/
theorem gap_axiom_spec (context : data_ontology.Context) (fine : FineCuts context.cuts.val) (low high : Usize)
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
  obtain ⟨cap1, capRun, capValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := capacity) (y := 1#usize) (by have := Usize.max_def; scalar_tac))
  have cap1Is : cap1.val = capacity.val + 1 := by simpa using capValue
  obtain ⟨size, sizeRun, sizeValue⟩ := Rowl.Regions.run_size_spec context.cuts.val[low.val]
    context.cuts.val[high.val] fl.1 fh.1 (fit_widths fl fh) cap1 (by rw [cap1Is]; omega)
  have sizeIs : size.val = min (runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val))
      (capacity.val + 1) := by
    rw [sizeValue, cutAt_val hl, cutAt_val hh, cap1Is]; rfl
  have capLt : capacity < q := by simp [UScalar.lt_equiv]; rw [qIs]; exact capSmall
  have capLtVal : capacity.val < q.val := by rw [qIs]; exact capSmall
  by_cases zero : size = 0#usize
  · subst zero
    have zeroCount : runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) = 0 := by
      have := sizeIs; simp at this; omega
    obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.ObjectIntersectionOf ⟨.Class (kindClass .Integer),
      .Class (cutClass low), alloc.vec.Vec.new ClassExpression⟩) (.Class (cutClass high)))
    refine ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, hl, hh, qRun, capLt, capLtVal,
      alloc.vec.Vec.index_slice_index, lookupL, lookupH, capRun, sizeRun, kind_class_eq, cut_class_eq,
      data_ontology.and, run], fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
    simp only [List.mem_singleton, forall_eq, satisfies, classDenote, new_val, List.not_mem_nil, false_imp_iff,
      implies_true, and_true, GapFact, zeroCount, lt_irrefl, false_imp_iff, imp_true_iff, true_implies]
    constructor
    · intro holds y a b; exact holds y ⟨a, b⟩
    · intro holds y ⟨a, b⟩; exact holds y a b
  · have nonzero : size.val ≠ 0 := fun h => zero (UScalar.eq_of_val_eq (by simpa using h))
    have pos : 0 < runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) := by
      have := sizeIs; omega
    have ne : runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) ≠ 0 := by omega
    by_cases fewer : size.val < capacity.val
    · have countIs : runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) = size.val := by
        have := sizeIs; omega
      obtain ⟨n, nRun, nValue⟩ := natural_of_spec size
      obtain ⟨rest, single, andRun⟩ := and3_eq (.Class (kindClass .Integer)) (.Class (cutClass low))
        (.ObjectComplementOf (.Class (cutClass high)))
      obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.Class thing)
        (.ObjectMaxCardinality n (.Property dataSuper) (some (.ObjectIntersectionOf ⟨.Class (kindClass .Integer),
          .Class (cutClass low), rest⟩))))
      refine ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, hl, hh, qRun, capLt, capLtVal,
        alloc.vec.Vec.index_slice_index, lookupL, lookupH, capRun, sizeRun, zero, fewer, thing_eq, nRun,
        data_super_eq, kind_class_eq, cut_class_eq, data_ontology.not, andRun, run],
        fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
      have lt : runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) < capacity.val := by
        rw [countIs]; exact fewer
      simp only [List.mem_singleton, forall_eq, satisfies, GapFact, pos, lt, ne, true_implies, false_imp_iff,
        imp_true_iff, true_and]
      simp [classDenote, objectRelation, single, nValue, countIs, InRun]
    · refine ⟨some out, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, hl, hh, qRun, capLt, capLtVal,
        alloc.vec.Vec.index_slice_index, lookupL, lookupH, capRun, sizeRun, zero, fewer],
        fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
      have notLt : ¬ runCount (cutAt context.cuts.val low.val) (cutAt context.cuts.val high.val) < capacity.val := by
        have := sizeIs; omega
      simp [GapFact, ne, notLt]

theorem index_unique {values : List datatypes.DataValue} (nodup : values.Nodup) {i j : Nat}
    (hi : i < values.length) (hj : j < values.length) (same : values[i] = values[j]) : i = j :=
  (List.Nodup.getElem_inj_iff nodup).mp same

/-- The axiom between two neighbouring cuts. -/
theorem between_axiom_spec (context : data_ontology.Context) (good : Good context) (fine : FineCuts context.cuts.val)
    (low high : Usize) (hl : low.val < context.cuts.val.length) (hh : high.val < context.cuts.val.length)
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
    · obtain ⟨r, run, facts⟩ := gap_axiom_spec context fine low high hl hh capacity capSmall out
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
    (order : alloc.vec.Vec Usize) (orderIn : ∀ k ∈ order.val, k.val < context.cuts.val.length) (position : Usize)
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
      obtain ⟨r2, run2, facts2⟩ := between_axiom_spec context good fine order.val[prev.val] order.val[position.val]
        hl hh capacity capSmall o1
      cases r2 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, positive, inside, prevRun,
          alloc.vec.Vec.index_slice_index, lookupP, lookupH, cut_class_eq, run1, run2], by simp⟩
      | some o2 =>
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := position) (y := 1#usize) (by scalar_tac))
        have nextIndex : next.val = position.val + 1 := by simpa using nextValue
        obtain ⟨r3, run3, facts3⟩ := chain_axioms_spec context good fine order orderIn next (by omega) capacity
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

/-- Every number among the literal values has both its cuts. -/
def ValuesCut (context : data_ontology.Context) : Prop :=
  ∀ v ∈ context.values.val, Rowl.Datatypes.IsNumber v →
    (⟨v, false⟩ : regions.Cut) ∈ context.cuts.val ∧ (⟨v, true⟩ : regions.Cut) ∈ context.cuts.val

theorem values_cut_spec (context : data_ontology.Context) (index : Usize) :
    ∃ b, data_ontology.values_cut context index = .ok b ∧ (b = true → ∀ (i : Nat) (h : i < context.values.val.length),
      index.val ≤ i → Rowl.Datatypes.IsNumber context.values.val[i] →
        (⟨context.values.val[i], false⟩ : regions.Cut) ∈ context.cuts.val ∧
        (⟨context.values.val[i], true⟩ : regions.Cut) ∈ context.cuts.val) := by
  rw [data_ontology.values_cut]
  by_cases inside : index.val < context.values.val.length
  · have lookup : context.values.index_usize index = .ok context.values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨rest, restRun, restFacts⟩ := values_cut_spec context next
    by_cases number : Rowl.Datatypes.IsNumber context.values.val[index.val]
    · obtain ⟨o1, run1, _, found1⟩ := Rowl.Regions.cut_index_correct context.cuts context.values.val[index.val]
        false 0#usize
      obtain ⟨o2, run2, _, found2⟩ := Rowl.Regions.cut_index_correct context.cuts context.values.val[index.val]
        true 0#usize
      cases o1 with
      | none => exact ⟨false, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
          Rowl.Datatypes.numeric_correct, number, run1, run2], by simp⟩
      | some a =>
        cases o2 with
        | none => exact ⟨false, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
            Rowl.Datatypes.numeric_correct, number, run1, run2], by simp⟩
        | some b =>
          refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
            Rowl.Datatypes.numeric_correct, number, run1, run2, advance, restRun], fun hr i hi low num => ?_⟩
          by_cases here : i = index.val
          · subst here
            obtain ⟨ha, aIs⟩ := found1 a rfl
            obtain ⟨hb, bIs⟩ := found2 b rfl
            exact ⟨aIs ▸ List.getElem_mem ha, bIs ▸ List.getElem_mem hb⟩
          · exact restFacts hr i hi (by omega) num
    · refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
        Rowl.Datatypes.numeric_correct, number, advance, restRun], fun hr i hi low num => ?_⟩
      by_cases here : i = index.val
      · subst here; exact absurd num number
      · exact restFacts hr i hi (by omega) num
  · exact ⟨true, by simp [UScalar.lt_equiv, inside], fun _ i hi low => by omega⟩
termination_by context.values.val.length - index.val
decreasing_by omega

/-- When the kernel finds the context encodable, its cuts can be ordered and
    every number among its literal values has both its cuts. -/
theorem encodable_spec (context : data_ontology.Context) (good : Good context) :
    ∃ b, data_ontology.encodable context = .ok b ∧ (b = true → FineCuts context.cuts.val ∧ ValuesCut context) := by
  rw [data_ontology.encodable]
  obtain ⟨f, fRun, fFacts⟩ := Rowl.Regions.cuts_fit_spec context.cuts 0#usize
    (fun c m _ => good.2.2.2.1.1 c m)
  obtain ⟨v, vRun, vFacts⟩ := values_cut_spec context 0#usize
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
    (fine : FineCuts context.cuts.val) (capacity : Usize) (capSmall : capacity.val < Usize.max / 16)
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
      obtain ⟨r2, run2, facts2⟩ := chain_axioms_spec context good fine order orderIn 1#usize (by simp) capacity
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
