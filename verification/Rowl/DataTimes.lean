import Rowl.DataEdges

/-!
The axioms that `data_ontology` adds for the time cuts of the context
(`time_axioms`). The time cuts are the bounds of the range facets on the time
instants in use, each with a class of the time instants of its line after its
instant, or at or after it when it is not open
(`Rowl.DataMeaning.InTimeCut`). The kernel puts each cut's class inside the
class of its line (`OnLine`), the class of each cut inside the class of every
other cut of its line that holds all of it (`CutWithin`), and, for a closed
and an open cut of a line at one instant, the time instants of the line at
that instant that are no literal values (`pointFree`, counted exactly: one for
each time zone offset from -14:00 to +14:00 with a time zone, and one without):
none at all, or at most their number at any element along `U` when there are
fewer of them than the capacity (`PointFact`, `TimeFacts`). The time instants
at an instant are counted exactly (`point_moments_card`, `free_point_card`).
-/
namespace Rowl.DataTimes
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.DataRegions (namedList add_named_spec natural_of_spec ValuesFit)
open Rowl.Datatypes (Canonical)
open Rowl.Moments (momentOf CanonicalMoment)
open Rowl.TimeOrder (InstantOk)
attribute [local instance low] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe w x

variable {Object' : Type w} {Value' : Type x}

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

theorem usize_big : 4294967295 ≤ Usize.max := by
  have := Usize.max_def
  rcases System.Platform.numBits_eq with e | e <;> simp_all [Usize.numBits]

/-! ### Literal values at an instant -/

/-- A literal value that is a time instant of the line `line` at the place of
    the instant `point` on the time line. -/
def AtPoint (line : Bool) (point : datatypes.Moment) (v : datatypes.DataValue) : Prop :=
  ∃ m, v = .Moment m ∧ m.zone.isSome = line ∧ (momentOf m).key = (momentOf point).key

theorem at_point_spec (v : datatypes.DataValue) (cv : Canonical v)
    (fv : ∀ m, v = .Moment m → m.year.val.length < Usize.max / 16) (line : Bool) (point : datatypes.Moment)
    (gp : InstantOk point 0) :
    data_ontology.at_point v line point = .ok (decide (AtPoint line point v)) := by
  cases v with
  | Moment m =>
    have small := fv m rfl
    have big := usize_big
    obtain ⟨i, iRun, iOk, iKey⟩ := Rowl.TimeOrder.instant_canonical m cv (room := 0) (by omega)
    obtain ⟨o, oRun, oVal⟩ := Rowl.TimeOrder.instant_order_spec i point iOk.1 gp.1 iOk.2.1 gp.2.1
    have one : o = 1#u8 ↔ (momentOf m).key = (momentOf point).key := by
      rw [← iKey, ← Rowl.TimeOrder.ordOf_eq_one (momentOf i).key (momentOf point).key, ← oVal]
      constructor
      · intro e; rw [e]; rfl
      · intro e; exact UScalar.eq_of_val_eq (by simpa using e)
    have atIff : AtPoint line point (.Moment m) ↔ m.zone.isSome = line ∧ o = 1#u8 := by
      rw [one]
      constructor
      · rintro ⟨m', e, z, k⟩
        cases e
        exact ⟨z, k⟩
      · rintro ⟨z, k⟩
        exact ⟨m, rfl, z, k⟩
    rw [data_ontology.at_point, Rowl.TimeOrder.zoned_spec, bind_ok, iRun, bind_ok, oRun, bind_ok]
    by_cases h1 : m.zone.isSome = line <;> by_cases h2 : o = 1#u8 <;> simp [h1, h2, atIff]
  | _ => simp [data_ontology.at_point, AtPoint]

/-- The number of the literal values of a line at an instant. -/
noncomputable def pointNamedCount (values : List datatypes.DataValue) (line : Bool) (point : datatypes.Moment) :
    ℕ :=
  (values.filter (fun v => decide (AtPoint line point v))).length

theorem point_count_spec (context : data_ontology.Context) (good : Good context) (fit : ValuesFit context)
    (line : Bool) (point : datatypes.Moment) (gp : InstantOk point 0) (index count : Usize)
    (room : count.val + (context.values.val.length - index.val) ≤ Usize.max) :
    ∃ r : Usize, data_ontology.point_count context line point index count = .ok r ∧
      r.val = count.val + pointNamedCount (context.values.val.drop index.val) line point := by
  rw [data_ontology.point_count]
  by_cases inside : index.val < context.values.val.length
  · have lookup : context.values.index_usize index = .ok context.values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have member := List.getElem_mem inside
    have atIs := at_point_spec context.values.val[index.val] (good.1.1 _ member) (fit _ member).2 line point gp
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    have countLt : count < core.num.Usize.MAX := by
      simp only [UScalar.lt_equiv, usize_max_val]; omega
    by_cases hit : AtPoint line point context.values.val[index.val]
    · obtain ⟨c1, c1Run, c1Val⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := count) (y := 1#usize) (by scalar_tac))
      have c1Is : c1.val = count.val + 1 := by simpa using c1Val
      obtain ⟨r, run, value⟩ := point_count_spec context good fit line point gp next c1
        (by rw [c1Is, nextIndex]; omega)
      refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, atIs, hit, countLt,
        advance, c1Run, run], ?_⟩
      rw [value, c1Is, nextIndex, split]
      simp only [pointNamedCount, List.filter_cons, hit, decide_true, ↓reduceIte, List.length_cons]
      omega
    · obtain ⟨r, run, value⟩ := point_count_spec context good fit line point gp next count
        (by rw [nextIndex]; omega)
      refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, atIs, hit, advance,
        run], ?_⟩
      rw [value, nextIndex, split]
      simp only [pointNamedCount, List.filter_cons, hit, decide_false, Bool.false_eq_true, ↓reduceIte]
  · refine ⟨count, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show context.values.val.length ≤ index.val by omega), pointNamedCount]
termination_by context.values.val.length - index.val
decreasing_by all_goals (simp at nextValue; omega)

/-- A node that is the individual of a literal value of a line at an
    instant. -/
def PointNamed (context : data_ontology.Context) (J : Interpretation Object' Value') (line : Bool)
    (point : datatypes.Moment) (y : Object') : Prop :=
  ∃ (i : Usize) (_ : i.val < context.values.val.length), AtPoint line point context.values.val[i.val] ∧
    J.namedIndividuals (valueIndividual i) = y

/-- The individuals of the literal values of a line at an instant, from
    `index` on. -/
theorem point_literals_spec (context : data_ontology.Context) (good : Good context) (fit : ValuesFit context)
    (line : Bool) (point : datatypes.Moment) (gp : InstantOk point 0) (index : Usize)
    (found : Option (NonEmpty Individual)) (room : (namedList found).length ≤ index.val) :
    ∃ res, data_ontology.point_literals context line point index found = .ok res ∧ ∀ a, a ∈ namedList res ↔
      a ∈ namedList found ∨ ∃ (i : Usize) (_ : i.val < context.values.val.length), index.val ≤ i.val ∧
        AtPoint line point context.values.val[i.val] ∧ a = .Named (valueIndividual i) := by
  rw [data_ontology.point_literals]
  by_cases inside : index.val < context.values.val.length
  · have lookup : context.values.index_usize index = .ok context.values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have member := List.getElem_mem inside
    have atIs := at_point_spec context.values.val[index.val] (good.1.1 _ member) (fit _ member).2 line point gp
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    by_cases hit : AtPoint line point context.values.val[index.val]
    · have bound : context.values.val.length ≤ Usize.max := context.values.property
      obtain ⟨o, addRun, addList⟩ := add_named_spec found (.Named (valueIndividual index)) (by omega)
      obtain ⟨res, run, members⟩ := point_literals_spec context good fit line point gp next o
        (by rw [addList, nextIndex]; simp; omega)
      refine ⟨res, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, atIs, hit, advance,
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
    · obtain ⟨res, run, members⟩ := point_literals_spec context good fit line point gp next found
        (by rw [nextIndex]; omega)
      refine ⟨res, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, atIs, hit, advance,
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

theorem point_named_iff {context : data_ontology.Context} {J : Interpretation Object' Value'} {line : Bool}
    {point : datatypes.Moment} {found : Option (NonEmpty Individual)}
    (members : ∀ a, a ∈ namedList found ↔ ∃ (i : Usize) (_ : i.val < context.values.val.length),
      AtPoint line point context.values.val[i.val] ∧ a = .Named (valueIndividual i)) (y : Object') :
    (∃ a ∈ namedList found, individual J a = y) ↔ PointNamed context J line point y := by
  constructor
  · rintro ⟨a, mem, same⟩
    obtain ⟨i, hi, atI, rfl⟩ := (members a).mp mem
    exact ⟨i, hi, atI, same⟩
  · rintro ⟨i, hi, atI, same⟩
    exact ⟨_, (members _).mpr ⟨i, hi, atI, rfl⟩, same⟩

/-! ### The axiom on the values at an instant -/

/-- The number of the time instants of a line at an instant: one for each
    time zone offset from -14:00 to +14:00 in minutes with a time zone, and
    one without. -/
def pointSize (line : Bool) : ℕ := if line then 1681 else 1

theorem point_size_spec (line : Bool) :
    ∃ s : Usize, data_ontology.point_size line = .ok s ∧ s.val = pointSize line := by
  cases line
  · exact ⟨1#usize, by simp [data_ontology.point_size], by simp [pointSize]⟩
  · exact ⟨1681#usize, by simp [data_ontology.point_size], by simp [pointSize]⟩

/-- The time instants of a line at an instant that are no literal values,
    counted as the kernel counts them. -/
noncomputable def pointFree (context : data_ontology.Context) (line : Bool) (point : datatypes.Moment) : ℕ :=
  pointSize line - pointNamedCount context.values.val line point

/-- The nodes of the time instants at an instant: in the class of the cut at
    the instant and outside the class of the cut after it. -/
def InPointClass (J : Interpretation Object' Value') (closed «open» : Usize) (y : Object') : Prop :=
  J.classes (timeClass closed) y ∧ ¬ J.classes (timeClass «open») y

theorem point_class_spec (closed «open» : Usize) :
    ∃ c, data_ontology.point_class closed «open» = .ok c ∧
      ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') (y : Object'),
        classDenote J c y ↔ InPointClass J closed «open» y := by
  refine ⟨.ObjectIntersectionOf ⟨.Class (timeClass closed), .ObjectComplementOf (.Class (timeClass «open»)),
    alloc.vec.Vec.new ClassExpression⟩, by simp [data_ontology.point_class, time_class_eq, data_ontology.not,
    data_ontology.and], fun J y => ?_⟩
  rw [inter_iff]
  simp [InPointClass, classDenote, AtLeastTwo.elements, new_val]

/-- What the axiom on the time instants of a line at an instant says, for the
    nodes of the class of the cut at the instant outside the class of the cut
    after it: when every value there is a literal value, the nodes are those
    literal values' individuals, and when fewer than the capacity of them are
    no literal values, at most that many other nodes are there at any element
    along `U`. -/
def PointFact (context : data_ontology.Context) (capacity : Nat) (J : Interpretation Object' Value') (line : Bool)
    (point : datatypes.Moment) (closed «open» : Usize) : Prop :=
  (pointFree context line point = 0 → ∀ y, InPointClass J closed «open» y → PointNamed context J line point y) ∧
  (0 < pointFree context line point → pointFree context line point < capacity → ∀ y, J.classes thing y →
    AtMost (pointFree context line point) (fun y' => J.objectProperties dataSuper y y' ∧
      InPointClass J closed «open» y' ∧ ¬ PointNamed context J line point y'))

theorem point_axiom_spec (context : data_ontology.Context) (good : Good context) (fit : ValuesFit context)
    (line : Bool) (closed «open» capacity : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.point_axiom context line closed «open» capacity out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ (h : closed.val < context.times.val.length),
          PointFact context capacity.val J line (context.times.val[closed.val]'h).instant closed «open») := by
  rw [data_ontology.point_axiom]
  by_cases inside : closed.val < context.times.val.length
  · have lookup : context.times.index_usize closed = .ok context.times.val[closed.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have gc := good.2.2.2.2.2.1 _ (List.getElem_mem inside)
    have gp : InstantOk context.times.val[closed.val].instant 0 := ⟨gc.1, gc.2.1, by have := gc.2.2; omega⟩
    obtain ⟨size, sizeRun, sizeVal⟩ := point_size_spec line
    have bound : context.values.val.length ≤ Usize.max := context.values.property
    obtain ⟨named, namedRun, namedVal⟩ := point_count_spec context good fit line _ gp 0#usize 0#usize
      (by simp [bound])
    have namedIs : named.val = pointNamedCount context.values.val line context.times.val[closed.val].instant := by
      rw [namedVal]; simp
    obtain ⟨free, freeRun, freeVal⟩ : ∃ f : Usize,
        (if named.val ≤ size.val then size - named else ok 0#usize : Result Usize) = .ok f ∧
        f.val = pointFree context line context.times.val[closed.val].instant := by
      by_cases h : named.val ≤ size.val
      · obtain ⟨d, dRun, dVal⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := size) (y := named) h)
        exact ⟨d, by simp [h, dRun], by rw [dVal.1, sizeVal, namedIs]; rfl⟩
      · exact ⟨0#usize, by simp [h], by
          simp only [pointFree]; rw [← namedIs, ← sizeVal]; simp; omega⟩
    obtain ⟨found, foundRun, members0⟩ := point_literals_spec context good fit line _ gp 0#usize none
      (by simp [namedList])
    have members : ∀ a, a ∈ namedList found ↔ ∃ (i : Usize) (_ : i.val < context.values.val.length),
        AtPoint line context.times.val[closed.val].instant context.values.val[i.val] ∧
          a = .Named (valueIndividual i) := by
      intro a
      rw [members0 a]
      simp [namedList]
    obtain ⟨pc, pcRun, pcMeans⟩ := point_class_spec.{w,x} closed «open»
    have whole : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') (P : Prop),
        ((∀ (h : closed.val < context.times.val.length),
          PointFact context capacity.val J line (context.times.val[closed.val]'h).instant closed «open») → P) →
        (P → PointFact context capacity.val J line context.times.val[closed.val].instant closed «open») →
        (P ↔ ∀ (h : closed.val < context.times.val.length),
          PointFact context capacity.val J line (context.times.val[closed.val]'h).instant closed «open») :=
      fun J P forth back => ⟨fun p _ => back p, forth⟩
    by_cases zero : free.val = 0
    · have zero' : free = 0#usize := UScalar.eq_of_val_eq (by simpa using zero)
      have none' : pointFree context line context.times.val[closed.val].instant = 0 := by
        rw [← freeVal]; exact zero
      cases found with
      | none =>
        obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf pc (.ObjectComplementOf pc))
        refine ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, sizeRun, namedRun, freeRun, foundRun, zero', pcRun,
          data_ontology.not, run], fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
        have nothing : ∀ y, ¬ PointNamed context J line context.times.val[closed.val].instant y :=
          fun y named => by simpa [namedList] using (point_named_iff members y).mpr named
        simp only [List.mem_singleton, forall_eq, satisfies, classDenote, pcMeans]
        apply whole J
        · intro holds y inP
          exact absurd ((holds inside).1 none' y inP) (nothing y)
        · intro holds
          exact ⟨fun _ y inP => absurd inP (holds y inP), fun pos => absurd none' (by omega)⟩
      | some list =>
        obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf pc (.ObjectOneOf list))
        refine ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, sizeRun, namedRun, freeRun, foundRun, zero', pcRun, run],
          fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
        have iff := point_named_iff (J := J) members
        simp only [namedList] at iff
        simp only [List.mem_singleton, forall_eq, satisfies, classDenote, pcMeans]
        apply whole J
        · intro holds y inP
          exact (iff y).mpr ((holds inside).1 none' y inP)
        · intro holds
          exact ⟨fun _ y inP => (iff y).mp (holds y inP), fun pos => absurd none' (by omega)⟩
    · have zero' : free ≠ 0#usize := fun h => zero (by rw [h]; rfl)
      by_cases fewer : free.val < capacity.val
      · have fewer' : free < capacity := by simp only [UScalar.lt_equiv]; exact fewer
        obtain ⟨n, nRun, nValue⟩ := natural_of_spec free
        have exact : pointFree context line context.times.val[closed.val].instant = free.val := freeVal.symm
        -- the axiom on the nodes at the instant that are no literal individuals, for a filler of their class
        have tail : ∀ filler : ClassExpression, (∀ {Object' : Type w} {Value' : Type x}
            (J : Interpretation Object' Value') (y : Object'), classDenote J filler y ↔
              InPointClass J closed «open» y ∧ ¬ PointNamed context J line context.times.val[closed.val].instant y) →
            ∃ new, ([⟨alloc.vec.Vec.new Annotation, Axiom.SubClassOf (.Class thing)
                (.ObjectMaxCardinality n (.Property dataSuper) (some filler))⟩] : List AnnotatedAxiom) = new ∧
              ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
                ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ (h : closed.val < context.times.val.length),
                  PointFact context capacity.val J line (context.times.val[closed.val]'h).instant closed «open») := by
          intro filler fillerMeans
          refine ⟨_, rfl, fun J => ?_⟩
          apply whole J
          · intro holds
            have fact := (holds inside).2
            rw [exact] at fact
            simp only [List.mem_singleton, forall_eq, satisfies, classDenote, objectRelation, nValue]
            intro y thing'
            have eq : ∀ y', (J.objectProperties dataSuper y y' ∧ classDenote J filler y') ↔
                (J.objectProperties dataSuper y y' ∧ InPointClass J closed «open» y' ∧
                  ¬ PointNamed context J line context.times.val[closed.val].instant y') :=
              fun y' => and_congr Iff.rfl (fillerMeans J y')
            simp only [eq]
            exact fact (Nat.pos_of_ne_zero zero) fewer y thing'
          · intro holds
            simp only [List.mem_singleton, forall_eq, satisfies, classDenote, objectRelation, nValue] at holds
            refine ⟨fun z => absurd (exact ▸ z) zero, fun _ _ y thing' => ?_⟩
            rw [exact]
            have eq : ∀ y', (J.objectProperties dataSuper y y' ∧ classDenote J filler y') ↔
                (J.objectProperties dataSuper y y' ∧ InPointClass J closed «open» y' ∧
                  ¬ PointNamed context J line context.times.val[closed.val].instant y') :=
              fun y' => and_congr Iff.rfl (fillerMeans J y')
            have := holds y thing'
            simp only [eq] at this
            exact this
        cases found with
        | none =>
          have fillerMeans : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value')
              (y : Object'), classDenote J pc y ↔ InPointClass J closed «open» y ∧
                ¬ PointNamed context J line context.times.val[closed.val].instant y := by
            intro Object' Value' J y
            have nothing : ¬ PointNamed context J line context.times.val[closed.val].instant y :=
              fun named => by simpa [namedList] using (point_named_iff members y).mpr named
            simp [pcMeans, nothing]
          obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.Class thing)
            (.ObjectMaxCardinality n (.Property dataSuper) (some pc)))
          refine ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, sizeRun, namedRun, freeRun, foundRun, zero', fewer', fewer, pcRun,
            thing_eq, nRun, data_super_eq, run], fun out' h => ?_⟩
          obtain ⟨new, same, means⟩ := tail pc fillerMeans
          exact ⟨new, by rw [contents out' h, same], means⟩
        | some list =>
          have fillerMeans : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value')
              (y : Object'), classDenote J (.ObjectIntersectionOf ⟨pc, .ObjectComplementOf (.ObjectOneOf list),
                alloc.vec.Vec.new ClassExpression⟩) y ↔ InPointClass J closed «open» y ∧
                ¬ PointNamed context J line context.times.val[closed.val].instant y := by
            intro Object' Value' J y
            have iff := point_named_iff (J := J) members y
            simp only [namedList] at iff
            rw [inter_iff]
            simp only [AtLeastTwo.elements, new_val, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
              forall_eq, classDenote, pcMeans, ← iff]
          obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.Class thing)
            (.ObjectMaxCardinality n (.Property dataSuper) (some (.ObjectIntersectionOf ⟨pc,
              .ObjectComplementOf (.ObjectOneOf list), alloc.vec.Vec.new ClassExpression⟩))))
          refine ⟨r, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, sizeRun, namedRun, freeRun, foundRun, zero', fewer', fewer, pcRun,
            data_ontology.not, data_ontology.and, thing_eq, nRun, data_super_eq, run], fun out' h => ?_⟩
          obtain ⟨new, same, means⟩ := tail _ fillerMeans
          exact ⟨new, by rw [contents out' h, same], means⟩
      · have fewer' : ¬ free < capacity := by simp only [UScalar.lt_equiv]; exact fewer
        refine ⟨some out, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, lookup, sizeRun, namedRun, freeRun, foundRun, zero', fewer', fewer],
          fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
        have many : capacity.val ≤ pointFree context line context.times.val[closed.val].instant := by
          rw [← freeVal]; omega
        have notZero : pointFree context line context.times.val[closed.val].instant ≠ 0 := by
          rw [← freeVal]; exact zero
        simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
        intro _
        exact ⟨fun z => absurd z notZero, fun _ lt => absurd lt (by omega)⟩
  · have inside' : ¬ closed < alloc.vec.Vec.len context.times := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    refine ⟨some out, by simp [inside'], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    intro h
    exact absurd h inside

/-! ### The time cuts -/

/-- The nodes of the time instants of a line, by the classes of the kinds: the
    time stamps, or the time instants that are no time stamps. -/
def OnLine (J : Interpretation Object' Value') (zoned : Bool) (y : Object') : Prop :=
  if zoned then J.classes (kindClass .DateTimeStamp) y
  else J.classes (kindClass .DateTime) y ∧ ¬ J.classes (kindClass .DateTimeStamp) y

theorem time_line_spec (zoned : Bool) :
    ∃ c, data_ontology.time_line zoned = .ok c ∧
      ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') (y : Object'),
        classDenote J c y ↔ OnLine J zoned y := by
  cases zoned with
  | true =>
    exact ⟨.Class (kindClass .DateTimeStamp), by simp [data_ontology.time_line, kind_class_eq],
      fun J y => by simp [OnLine, classDenote]⟩
  | false =>
    refine ⟨.ObjectIntersectionOf ⟨.Class (kindClass .DateTime),
      .ObjectComplementOf (.Class (kindClass .DateTimeStamp)), alloc.vec.Vec.new ClassExpression⟩,
      by simp [data_ontology.time_line, kind_class_eq, data_ontology.not, data_ontology.and], fun J y => ?_⟩
    rw [inter_iff]
    simp [OnLine, classDenote, AtLeastTwo.elements, new_val]

/-- The cut `b` holds all of the cut `a` of its line: it comes before it, or
    it is at the same instant and holds at least as much there. -/
def CutWithin (a b : data_ontology.TimeCut) : Prop :=
  (momentOf b.instant).key < (momentOf a.instant).key ∨
    ((momentOf a.instant).key = (momentOf b.instant).key ∧ (a.open = true ∨ b.open = false))

section Facts
variable (context : data_ontology.Context) (capacity : Nat) (J : Interpretation Object' Value')

/-- What the axioms between the time cuts at `i` and `j` say: when they are
    two cuts of one line, the class of `i` inside the class of `j` when `j`
    holds all of `i`, and the axiom on the values at their instant when `i`
    is the closed and `j` the open cut there. -/
def TimePairFact (i j : Usize) : Prop :=
  ∀ (hi : i.val < context.times.val.length) (hj : j.val < context.times.val.length),
    (context.times.val[i.val]'hi).zoned = (context.times.val[j.val]'hj).zoned → i ≠ j →
    (CutWithin (context.times.val[i.val]'hi) (context.times.val[j.val]'hj) →
      ∀ y, J.classes (timeClass i) y → J.classes (timeClass j) y) ∧
    ((momentOf (context.times.val[i.val]'hi).instant).key = (momentOf (context.times.val[j.val]'hj).instant).key →
      (context.times.val[i.val]'hi).open = false → (context.times.val[j.val]'hj).open = true →
      PointFact context capacity J (context.times.val[i.val]'hi).zoned (context.times.val[i.val]'hi).instant i j)

/-- What the axioms of the time cuts from `index` on say: each cut's class
    inside the class of its line, and the facts between it and every cut. -/
def TimesFrom (index : Nat) : Prop :=
  ∀ i : Usize, index ≤ i.val →
    (∀ (hi : i.val < context.times.val.length) y, J.classes (timeClass i) y →
      OnLine J (context.times.val[i.val]'hi).zoned y) ∧ ∀ j : Usize, TimePairFact context capacity J i j

/-- What the axioms of the time cuts say. -/
def TimeFacts : Prop := TimesFrom context capacity J 0

end Facts

theorem time_pair_axioms_spec (context : data_ontology.Context) (good : Good context) (fit : ValuesFit context)
    (capacity first second : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.time_pair_axioms context capacity first second out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ TimePairFact context capacity.val J first second) := by
  rw [data_ontology.time_pair_axioms]
  by_cases inside : first.val < context.times.val.length ∧ second.val < context.times.val.length
  · have l1 : context.times.index_usize first = .ok context.times.val[first.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside.1]
    have l2 : context.times.index_usize second = .ok context.times.val[second.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside.2]
    have g1 := good.2.2.2.2.2.1 _ (List.getElem_mem inside.1)
    have g2 := good.2.2.2.2.2.1 _ (List.getElem_mem inside.2)
    obtain ⟨o, oRun, oVal⟩ := Rowl.TimeOrder.instant_order_spec context.times.val[first.val].instant
      context.times.val[second.val].instant g1.1 g2.1 g1.2.1 g2.2.1
    have two : o = 2#u8 ↔ (momentOf context.times.val[second.val].instant).key <
        (momentOf context.times.val[first.val].instant).key := by
      rw [← Rowl.TimeOrder.ordOf_eq_two (momentOf context.times.val[first.val].instant).key
        (momentOf context.times.val[second.val].instant).key, ← oVal]
      constructor
      · intro e; rw [e]; rfl
      · intro e; exact UScalar.eq_of_val_eq (by simpa using e)
    have one : o = 1#u8 ↔ (momentOf context.times.val[first.val].instant).key =
        (momentOf context.times.val[second.val].instant).key := by
      rw [← Rowl.TimeOrder.ordOf_eq_one (momentOf context.times.val[first.val].instant).key
        (momentOf context.times.val[second.val].instant).key, ← oVal]
      constructor
      · intro e; rw [e]; rfl
      · intro e; exact UScalar.eq_of_val_eq (by simpa using e)
    -- the fact, for the two cuts in range
    have whole : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') (P : Prop),
        (P ↔ (context.times.val[first.val].zoned = context.times.val[second.val].zoned → first ≠ second →
          (CutWithin context.times.val[first.val] context.times.val[second.val] →
            ∀ y, J.classes (timeClass first) y → J.classes (timeClass second) y) ∧
          ((momentOf context.times.val[first.val].instant).key =
              (momentOf context.times.val[second.val].instant).key →
            context.times.val[first.val].open = false → context.times.val[second.val].open = true →
            PointFact context capacity.val J context.times.val[first.val].zoned
              context.times.val[first.val].instant first second))) →
        (P ↔ TimePairFact context capacity.val J first second) :=
      fun J P iff => ⟨fun p _ _ => iff.mp p, fun f => iff.mpr (f inside.1 inside.2)⟩
    have cond0 : (decide (first < alloc.vec.Vec.len context.times) &&
        decide (second < alloc.vec.Vec.len context.times)) = true := by
      simp [UScalar.lt_equiv, inside.1, inside.2]
    simp only [cond0, ↓reduceIte, alloc.vec.Vec.index_slice_index, l1, l2, bind_ok]
    by_cases pair : context.times.val[first.val].zoned = context.times.val[second.val].zoned ∧ first ≠ second
    · have cond1 : (decide (context.times.val[first.val].zoned = context.times.val[second.val].zoned) &&
          (first != second)) = true := by
        simp [pair.1, pair.2]
      simp only [cond1, ↓reduceIte, oRun, bind_ok]
      -- the inclusion axiom means the fact when the second cut holds all of the first
      have inclusion : CutWithin context.times.val[first.val] context.times.val[second.val] →
          ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
            ((∀ y, J.classes (timeClass first) y → J.classes (timeClass second) y) ↔
              TimePairFact context capacity.val J first second) := by
        intro within Object' Value' J
        apply whole J
        constructor
        · intro holds _ _
          refine ⟨fun _ => holds, fun same closed opened => ?_⟩
          rcases within with lt | ⟨_, o1 | o2⟩
          · rw [same] at lt; exact absurd lt (lt_irrefl _)
          · rw [closed] at o1; cases o1
          · rw [opened] at o2; cases o2
        · intro holds
          exact (holds pair.1 pair.2).1 within
      have pushed : ∃ res, data_ontology.push out (.SubClassOf (.Class (timeClass first))
            (.Class (timeClass second))) = .ok res ∧ ∀ out', res = some out' →
          ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x}
            (J : Interpretation Object' Value'), ((∀ b ∈ new, satisfies J b.axiom) ↔
              (∀ y, J.classes (timeClass first) y → J.classes (timeClass second) y)) := by
        obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.Class (timeClass first))
          (.Class (timeClass second)))
        refine ⟨r, run, fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
        simp only [List.mem_singleton, forall_eq, satisfies, classDenote]
      by_cases lt : (momentOf context.times.val[second.val].instant).key <
          (momentOf context.times.val[first.val].instant).key
      · have cond2 : (decide (o = 2#u8) || (decide (o = 1#u8) && (context.times.val[first.val].open ||
            decide ¬(context.times.val[second.val].open = true)))) = true := by
          simp [two.mpr lt]
        obtain ⟨r, run, facts⟩ := pushed
        refine ⟨r, by simp only [cond2, ↓reduceIte, time_class_eq, bind_ok]; exact run, fun out' h => ?_⟩
        obtain ⟨new, c, means⟩ := facts out' h
        exact ⟨new, c, fun J => (means J).trans (inclusion (.inl lt) J)⟩
      · have h2 : ¬ o = 2#u8 := fun e => lt (two.mp e)
        by_cases eq : (momentOf context.times.val[first.val].instant).key =
            (momentOf context.times.val[second.val].instant).key
        · have h1 : o = 1#u8 := one.mpr eq
          by_cases point : context.times.val[first.val].open = false ∧ context.times.val[second.val].open = true
          · -- the axiom on the values at the instant
            have cond2 : (decide (o = 2#u8) || (decide (o = 1#u8) && (context.times.val[first.val].open ||
                decide ¬(context.times.val[second.val].open = true)))) = false := by
              simp [h2, h1, point.1, point.2]
            have cond3 : (decide (o = 1#u8) && decide ¬(context.times.val[first.val].open = true) &&
                context.times.val[second.val].open) = true := by
              simp [h1, point.1, point.2]
            obtain ⟨r, run, facts⟩ := point_axiom_spec context good fit context.times.val[first.val].zoned first
              second capacity out
            refine ⟨r, by simp only [cond2, cond3, Bool.false_eq_true, ↓reduceIte]; exact run, fun out' h => ?_⟩
            obtain ⟨new, c, means⟩ := facts out' h
            refine ⟨new, c, fun J => whole J _ ?_⟩
            rw [means J]
            constructor
            · intro fact _ _
              refine ⟨fun within => ?_, fun _ _ _ => fact inside.1⟩
              rcases within with lt' | ⟨_, o1 | o2⟩
              · exact absurd lt' lt
              · rw [point.1] at o1; cases o1
              · rw [point.2] at o2; cases o2
            · intro holds _
              exact (holds pair.1 pair.2).2 eq point.1 point.2
          · have opens : context.times.val[first.val].open = true ∨ context.times.val[second.val].open = false := by
              rcases Bool.eq_false_or_eq_true context.times.val[first.val].open with ho | ho
              · exact .inl ho
              · rcases Bool.eq_false_or_eq_true context.times.val[second.val].open with ho' | ho'
                · exact absurd ⟨ho, ho'⟩ point
                · exact .inr ho'
            have cond2 : (decide (o = 2#u8) || (decide (o = 1#u8) && (context.times.val[first.val].open ||
                decide ¬(context.times.val[second.val].open = true)))) = true := by
              rcases opens with ho | ho <;> simp [h1, ho]
            obtain ⟨r, run, facts⟩ := pushed
            refine ⟨r, by simp only [cond2, ↓reduceIte, time_class_eq, bind_ok]; exact run, fun out' h => ?_⟩
            obtain ⟨new, c, means⟩ := facts out' h
            exact ⟨new, c, fun J => (means J).trans (inclusion (.inr ⟨eq, opens⟩) J)⟩
        · have h1 : ¬ o = 1#u8 := fun e => eq (one.mp e)
          have cond2 : (decide (o = 2#u8) || (decide (o = 1#u8) && (context.times.val[first.val].open ||
              decide ¬(context.times.val[second.val].open = true)))) = false := by
            simp [h2, h1]
          have cond3 : (decide (o = 1#u8) && decide ¬(context.times.val[first.val].open = true) &&
              context.times.val[second.val].open) = false := by
            simp [h1]
          refine ⟨some out, by simp only [cond2, cond3, Bool.false_eq_true, ↓reduceIte],
            fun out' h => ⟨[], by cases h; simp, fun J => whole J _ ?_⟩⟩
          simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
          intro _ _
          refine ⟨fun within => ?_, fun same => absurd same eq⟩
          rcases within with lt' | ⟨same, _⟩
          · exact absurd lt' lt
          · exact absurd same eq
    · have cond1 : (decide (context.times.val[first.val].zoned = context.times.val[second.val].zoned) &&
          (first != second)) = false := by
        simp only [not_and_or, ne_eq, not_not] at pair
        rcases pair with differ | same
        · simp [differ]
        · simp [same]
      refine ⟨some out, by simp only [cond1, Bool.false_eq_true, ↓reduceIte],
        fun out' h => ⟨[], by cases h; simp, fun J => whole J _ ?_⟩⟩
      simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
      intro zone ne
      exact absurd ⟨zone, ne⟩ pair
  · refine ⟨some out, ?_, fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    · simp only [not_and_or] at inside
      rcases inside with a | b
      · simp [UScalar.lt_equiv, a]
      · simp [UScalar.lt_equiv, b]
    · simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
      intro hi hj
      exact absurd ⟨hi, hj⟩ inside

theorem time_pairs_spec (context : data_ontology.Context) (good : Good context) (fit : ValuesFit context)
    (capacity first second : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.time_pairs context capacity first second out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔
          ∀ j : Usize, second.val ≤ j.val → TimePairFact context capacity.val J first j) := by
  rw [data_ontology.time_pairs]
  by_cases inside : second.val < context.times.val.length
  · obtain ⟨r1, run1, f1⟩ := time_pair_axioms_spec context good fit capacity first second out
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, run1], by simp⟩
    | some o1 =>
      obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := second) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = second.val + 1 := by simpa using nextValue
      obtain ⟨r2, run2, f2⟩ := time_pairs_spec context good fit capacity first next o1
      refine ⟨r2, by simp [UScalar.lt_equiv, inside, run1, advance, run2], fun out' h => ?_⟩
      obtain ⟨n2, c2, m2⟩ := f2 out' h
      refine ⟨n1 ++ n2, by rw [c2, c1]; simp, fun J => ?_⟩
      simp only [List.forall_mem_append]
      rw [m1 J, m2 J, nextIndex]
      constructor
      · rintro ⟨here, rest⟩ j le
        by_cases same : j = second
        · subst same; exact here
        · have : j.val ≠ second.val := fun h => same (UScalar.eq_of_val_eq h)
          exact rest j (by omega)
      · intro all
        exact ⟨all second le_rfl, fun j le => all j (by omega)⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    intro j le hi hj
    exact absurd (lt_of_le_of_lt le hj) inside
termination_by context.times.val.length - second.val
decreasing_by omega

theorem time_axioms_spec (context : data_ontology.Context) (good : Good context) (fit : ValuesFit context)
    (capacity index : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.time_axioms context capacity index out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ TimesFrom context capacity.val J index.val) := by
  rw [data_ontology.time_axioms]
  by_cases inside : index.val < context.times.val.length
  · have lookup : context.times.index_usize index = .ok context.times.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨line, lineRun, lineMeans⟩ := time_line_spec.{w,x} context.times.val[index.val].zoned
    obtain ⟨r0, run0, contents0⟩ := push_spec out (.SubClassOf (.Class (timeClass index)) line)
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, ↓reduceIte, time_class_eq, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup]
    rw [lineRun, bind_ok, run0]
    cases r0 with
    | none => exact ⟨none, by simp, by simp⟩
    | some o0 =>
      obtain ⟨r1, run1, f1⟩ := time_pairs_spec context good fit capacity index 0#usize o0
      cases r1 with
      | none => exact ⟨none, by simp only [run1, bind_ok], by simp⟩
      | some o1 =>
        obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIndex : next.val = index.val + 1 := by simpa using nextValue
        obtain ⟨r2, run2, f2⟩ := time_axioms_spec context good fit capacity next o1
        refine ⟨r2, by simp only [run1, bind_ok, advance, run2], fun out' h => ?_⟩
        obtain ⟨n2, c2, m2⟩ := f2 out' h
        refine ⟨⟨alloc.vec.Vec.new Annotation, .SubClassOf (.Class (timeClass index)) line⟩ :: (n1 ++ n2),
          by rw [c2, c1, contents0 o0 rfl]; simp, fun J => ?_⟩
        simp only [List.mem_cons, forall_eq_or_imp, List.forall_mem_append]
        rw [m1 J, m2 J, nextIndex]
        simp only [satisfies, classDenote, lineMeans]
        constructor
        · rintro ⟨incl, pairs, rest⟩ i le
          by_cases same : i = index
          · subst same
            exact ⟨fun _ y hy => incl y hy, fun j => pairs j (by simp)⟩
          · have : i.val ≠ index.val := fun h => same (UScalar.eq_of_val_eq h)
            exact rest i (by omega)
        · intro all
          obtain ⟨incl, pairs⟩ := all index le_rfl
          exact ⟨fun y hy => incl inside y hy, fun j _ => pairs j, fun i le => all i (by omega)⟩
  · have inside' : ¬ index < alloc.vec.Vec.len context.times := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    refine ⟨some out, by simp [inside'], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    intro i le
    exact ⟨fun hi => absurd (lt_of_le_of_lt le hi) inside, fun j hi => absurd (lt_of_le_of_lt le hi) inside⟩
termination_by context.times.val.length - index.val
decreasing_by omega

/-! ### Literal values in the time cuts -/

/-- A literal value that is a time instant of the line `line`. -/
def OnLineValue (line : Bool) (v : datatypes.DataValue) : Prop := ∃ y, v = .Moment y ∧ y.zone.isSome = line

theorem on_line_spec (v : datatypes.DataValue) (line : Bool) :
    data_ontology.on_line v line = .ok (decide (OnLineValue line v)) := by
  cases v with
  | Moment y =>
    rw [data_ontology.on_line, Rowl.TimeOrder.zoned_spec, bind_ok]
    by_cases h : y.zone.isSome = line <;> simp [OnLineValue, h]
  | _ => simp [data_ontology.on_line, OnLineValue]

/-- A literal value that is a time instant in the time cut. -/
def InCutValue (cut : data_ontology.TimeCut) (v : datatypes.DataValue) : Prop :=
  ∃ y, v = .Moment y ∧ InTimeCut cut (momentOf y)

theorem in_time_cut_spec (cut : data_ontology.TimeCut) (gc : InstantOk cut.instant 0) (v : datatypes.DataValue)
    (cv : Canonical v) (fv : ∀ m, v = .Moment m → m.year.val.length < Usize.max / 16) :
    data_ontology.in_time_cut cut v = .ok (decide (InCutValue cut v)) := by
  cases v with
  | Moment m =>
    have small := fv m rfl
    have big := usize_big
    obtain ⟨i, iRun, iOk, iKey⟩ := Rowl.TimeOrder.instant_canonical m cv (room := 0) (by omega)
    obtain ⟨o, oRun, oVal⟩ := Rowl.TimeOrder.instant_order_spec i cut.instant iOk.1 gc.1 iOk.2.1 gc.2.1
    have two : o = 2#u8 ↔ (momentOf cut.instant).key < (momentOf m).key := by
      rw [← iKey, ← Rowl.TimeOrder.ordOf_eq_two (momentOf i).key (momentOf cut.instant).key, ← oVal]
      constructor
      · intro e; rw [e]; rfl
      · intro e; exact UScalar.eq_of_val_eq (by simpa using e)
    have one : o = 1#u8 ↔ (momentOf cut.instant).key = (momentOf m).key := by
      rw [← iKey, @eq_comm _ (momentOf cut.instant).key,
        ← Rowl.TimeOrder.ordOf_eq_one (momentOf i).key (momentOf cut.instant).key, ← oVal]
      constructor
      · intro e; rw [e]; rfl
      · intro e; exact UScalar.eq_of_val_eq (by simpa using e)
    have inIff : InCutValue cut (.Moment m) ↔ o = 2#u8 ∨ (o = 1#u8 ∧ cut.open = false) := by
      rw [two, one]
      unfold InCutValue InTimeCut
      constructor
      · rintro ⟨m', e, holds⟩
        cases e
        exact holds
      · intro holds
        exact ⟨m, rfl, holds⟩
    rw [data_ontology.in_time_cut, iRun, bind_ok, oRun, bind_ok]
    by_cases h2 : o = 2#u8 <;> by_cases h1 : o = 1#u8 <;> cases ho : cut.open <;> simp [h2, h1, ho, inIff]
  | _ => simp [data_ontology.in_time_cut, InCutValue]

/-! ### The values at an instant -/

/-- The time instants of a line at the place of an instant. -/
def PointMoments (line : Bool) (point : datatypes.Moment) : Set Rowl.DatatypeMap.Moment :=
  {m | m.Valid ∧ m.zone.isSome = line ∧ m.key = (momentOf point).key}

/-- There are as many time instants of a line at the place of an instant as
    the kernel counts: 1681 with a time zone, and one without. -/
theorem point_moments_card (line : Bool) {point : datatypes.Moment} (gp : InstantOk point 0) :
    (PointMoments line point).ncard = pointSize line := by
  have valid := gp.1.2.2.2.2.2.2
  have zone : (momentOf point).zone = none := by simp [momentOf, gp.2.1]
  cases line with
  | true =>
    have same : PointMoments true point = Rowl.TimeOrder.zonedAt (momentOf point) := rfl
    rw [same, Rowl.TimeOrder.zonedAt_card valid zone]
    rfl
  | false =>
    have same : PointMoments false point = {momentOf point} := by
      ext m
      constructor
      · rintro ⟨vm, zm, km⟩
        exact Rowl.TimeOrder.unzoned_at valid vm zone (by simpa using zm) km |> fun e => e
      · rintro rfl
        exact ⟨valid, by simp [zone], rfl⟩
    rw [same, Set.ncard_singleton]
    rfl

theorem point_moments_finite (line : Bool) {point : datatypes.Moment} (gp : InstantOk point 0) :
    (PointMoments line point).Finite := by
  apply Set.finite_of_ncard_ne_zero
  rw [point_moments_card line gp]
  cases line <;> simp [pointSize]

/-- The time instants of the literal values. -/
def literalMoments (values : List datatypes.DataValue) : Set Rowl.DatatypeMap.Moment :=
  {m | ∃ y, datatypes.DataValue.Moment y ∈ values ∧ momentOf y = m}

/-- The time instants of a line at an instant that are no literal values. -/
def FreePoint (values : List datatypes.DataValue) (line : Bool) (point : datatypes.Moment) :
    Set Rowl.DatatypeMap.Moment :=
  PointMoments line point \ literalMoments values

/-- The time instant of a kernel value, if it is one. -/
noncomputable def momentValueOf : datatypes.DataValue → Rowl.DatatypeMap.Moment
  | .Moment y => momentOf y
  | _ => momentOf ⟨false, alloc.vec.Vec.new U8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, alloc.vec.Vec.new U8, none⟩

theorem point_lits_eq (values : List datatypes.DataValue) (line : Bool) (point : datatypes.Moment)
    (canonical : ∀ v ∈ values, Canonical v) :
    PointMoments line point ∩ literalMoments values =
      momentValueOf '' {v | v ∈ values.filter (fun v => decide (AtPoint line point v))} := by
  ext m
  constructor
  · rintro ⟨⟨vm, zm, km⟩, y, mem, rfl⟩
    refine ⟨.Moment y, ?_, rfl⟩
    simp only [Set.mem_setOf_eq, List.mem_filter, decide_eq_true_eq]
    have zy : y.zone.isSome = line := by
      rw [← zm]; simp [momentOf]
    exact ⟨mem, y, rfl, zy, km⟩
  · rintro ⟨v, mem, rfl⟩
    simp only [Set.mem_setOf_eq, List.mem_filter, decide_eq_true_eq] at mem
    obtain ⟨inValues, y, rfl, zy, ky⟩ := mem
    have cy : CanonicalMoment y := canonical _ inValues
    refine ⟨⟨cy.2.2.2.2.2.2, by simp [momentValueOf, momentOf, zy], ky⟩, y, inValues, rfl⟩

theorem point_lits_card {values : List datatypes.DataValue} (good : GoodValues values) (line : Bool)
    (point : datatypes.Moment) :
    (PointMoments line point ∩ literalMoments values).ncard = pointNamedCount values line point := by
  rw [point_lits_eq values line point good.1, Set.InjOn.ncard_image]
  · rw [show {v | v ∈ values.filter (fun v => decide (AtPoint line point v))} =
        ↑(values.filter (fun v => decide (AtPoint line point v))).toFinset by ext; simp,
      Set.ncard_coe_finset, List.toFinset_card_of_nodup (good.2.filter _)]
    rfl
  · intro v hv v' hv' same
    simp only [Set.mem_setOf_eq, List.mem_filter, decide_eq_true_eq] at hv hv'
    obtain ⟨m, y, rfl, _, _⟩ := hv
    obtain ⟨m', y', rfl, _, _⟩ := hv'
    simp only [momentValueOf] at same
    rw [Rowl.Datatypes.moment_canonical_injective (good.1 _ m) (good.1 _ m') same]

/-- The time instants of a line at an instant that are no literal values are
    counted exactly by the kernel's count. -/
theorem free_point_card {values : List datatypes.DataValue} (good : GoodValues values) (line : Bool)
    {point : datatypes.Moment} (gp : InstantOk point 0) :
    (FreePoint values line point).ncard = pointSize line - pointNamedCount values line point := by
  have finite := point_moments_finite line gp
  unfold FreePoint
  rw [← Set.sdiff_self_inter, Set.ncard_sdiff Set.inter_subset_left (finite.subset Set.inter_subset_left),
    point_lits_card good line point, point_moments_card line gp]

theorem free_point_finite (values : List datatypes.DataValue) (line : Bool) {point : datatypes.Moment}
    (gp : InstantOk point 0) : (FreePoint values line point).Finite :=
  (point_moments_finite line gp).subset Set.sdiff_subset

/-- At most as many elements meet `P` as there are members of `S` when each of
    them stands for a member of `S` that no other stands for. -/
theorem at_most_of_free {α : Type*} {β : Type*} {P : α → Prop} {S : Set β} (finite : S.Finite)
    (R : α → β → Prop) (exists' : ∀ a, P a → ∃ x ∈ S, R a x)
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

end Rowl.DataTimes
