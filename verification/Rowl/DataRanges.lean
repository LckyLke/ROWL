import Rowl.DataLengths

/-!
The axioms that `data_ontology` adds for the language ranges of the context
(`range_axioms`). Each basic language range of a facet `rdf:langRange`, in
lower case, has the class of the values with a language tag that it matches
(`Rowl.DataMeaning.NodeValue`). The kernel puts each such class inside the
values with a language tag, the class of a range inside the class of every
range that matches it, the classes of two ranges of which neither matches the
other apart, and the class of a range without free tags (`free_tags`) inside
the classes of the ranges that continue it (`IndexFact`); the values with a
language tag go inside the class of `*`, or, without `*` and when every
language tag matches a range, inside the classes of the ranges (`RootFact`).
-/
namespace Rowl.DataRanges
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.DataLengths (and_class_iff)
open Rowl.LangRanges (Matches Continues Free LowerTag)
attribute [local instance low] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe w x

variable {Object' : Type w} {Value' : Type x}

/-! ### The classes -/

/-- The class of the values with a language tag: of `rdf:PlainLiteral` and
    not of `xsd:string`. -/
noncomputable def taggedClass : ClassExpression :=
  .ObjectIntersectionOf ⟨.Class (kindClass .Plain), .ObjectComplementOf (.Class (kindClass .String)),
    alloc.vec.Vec.new ClassExpression⟩

theorem tagged_class_eq : data_ontology.tagged_class = .ok taggedClass := by
  simp [data_ontology.tagged_class, kind_class_eq, data_ontology.not, data_ontology.and, taggedClass]

theorem tagged_class_iff (J : Interpretation Object' Value') (y : Object') :
    classDenote J taggedClass y ↔ J.classes (kindClass .Plain) y ∧ ¬ J.classes (kindClass .String) y := by
  rw [taggedClass, and_class_iff]
  simp [classDenote]

/-- The ranges that continue the range at `first`, or, with no `first`, the
    ranges but `*`. -/
def ContinuesAt (ranges : List (alloc.vec.Vec U8)) (first : Option Usize) (second : Nat) : Prop :=
  ∃ h : second < ranges.length, match first with
    | none => (ranges[second]'h).val ≠ [42#u8]
    | some i => ∃ hi : i.val < ranges.length, Continues (ranges[i.val]'hi).val (ranges[second]'h).val

/-- A longer range that a range but `*` matches goes on after a `-`. -/
theorem continues_iff {r r' : List U8} (notStar : r ≠ [42#u8]) :
    (r.length < r'.length ∧ Matches r r') ↔ ∃ s, r' = r ++ 45#u8 :: s := by
  constructor
  · rintro ⟨longer, star | same | ⟨s, e⟩⟩
    · exact absurd star notStar
    · rw [same] at longer; omega
    · exact ⟨s, e⟩
  · rintro ⟨s, rfl⟩
    exact ⟨by simp, Or.inr (Or.inr ⟨s, rfl⟩)⟩

theorem continues_spec (context : data_ontology.Context) (first : Option Usize) (second : Usize) :
    data_ontology.continues context first second =
      .ok (decide (ContinuesAt context.ranges.val first second.val)) := by
  rw [data_ontology.continues]
  by_cases inside : second.val < context.ranges.val.length
  · have lookup : context.ranges.index_usize second = .ok context.ranges.val[second.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    cases first with
    | none =>
      have iff : ContinuesAt context.ranges.val none second.val ↔ context.ranges.val[second.val].val ≠ [42#u8] :=
        ⟨fun ⟨_, h⟩ => h, fun h => ⟨inside, h⟩⟩
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, Rowl.LangRanges.star_spec, iff]
    | some i =>
      by_cases hi : i.val < context.ranges.val.length
      · have lookupI : context.ranges.index_usize i = .ok context.ranges.val[i.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hi]
        by_cases star : context.ranges.val[i.val].val = [42#u8]
        · have iff : ContinuesAt context.ranges.val (some i) second.val ↔
              context.ranges.val[second.val].val ≠ [42#u8] := by
            constructor
            · rintro ⟨_, _, ⟨_, h⟩ | ⟨bad, _⟩⟩
              · exact h
              · exact absurd star bad
            · intro h
              exact ⟨inside, hi, Or.inl ⟨star, h⟩⟩
          simp [UScalar.lt_equiv, inside, hi, alloc.vec.Vec.index_slice_index, lookup, lookupI,
            Rowl.LangRanges.star_spec, star, iff]
        · by_cases longer : context.ranges.val[i.val].val.length < context.ranges.val[second.val].val.length
          · have iff : ContinuesAt context.ranges.val (some i) second.val ↔
                Matches context.ranges.val[i.val].val context.ranges.val[second.val].val := by
              constructor
              · rintro ⟨_, _, ⟨bad, _⟩ | ⟨_, cont⟩⟩
                · exact absurd bad star
                · exact ((continues_iff star).mpr cont).2
              · intro m
                exact ⟨inside, hi, Or.inr ⟨star, (continues_iff star).mp ⟨longer, m⟩⟩⟩
            simp [UScalar.lt_equiv, inside, hi, alloc.vec.Vec.index_slice_index, lookup, lookupI,
              Rowl.LangRanges.star_spec, star, longer, Rowl.LangRanges.range_matches_spec, iff]
          · have no : ¬ ContinuesAt context.ranges.val (some i) second.val := by
              rintro ⟨_, _, ⟨bad, _⟩ | ⟨_, cont⟩⟩
              · exact star bad
              · exact longer ((continues_iff star).mpr cont).1
            simp [UScalar.lt_equiv, inside, hi, alloc.vec.Vec.index_slice_index, lookup, lookupI,
              Rowl.LangRanges.star_spec, star, longer, no]
      · have no : ¬ ContinuesAt context.ranges.val (some i) second.val := by
          rintro ⟨_, hi', _⟩; exact hi hi'
        simp [UScalar.lt_equiv, inside, hi, alloc.vec.Vec.index_slice_index, lookup, Rowl.LangRanges.star_spec, no]
  · have no : ¬ ContinuesAt context.ranges.val first second.val := fun ⟨h, _⟩ => inside h
    simp [UScalar.lt_equiv, inside, no]

theorem continuing_spec (context : data_ontology.Context) (first : Option Usize) (index : Usize)
    (found : Option ClassExpression) :
    ∃ res, data_ontology.continuing context first index found = .ok res ∧
      (res = none ↔ found = none ∧ ∀ j, index.val ≤ j → ¬ ContinuesAt context.ranges.val first j) ∧
      ∀ c, res = some c → ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') y,
        (classDenote J c y ↔ (∃ c', found = some c' ∧ classDenote J c' y) ∨
          ∃ j : Usize, index.val ≤ j.val ∧ ContinuesAt context.ranges.val first j.val ∧
            J.classes (rangeClass j) y) := by
  rw [data_ontology.continuing.eq_def]
  by_cases inside : index.val < context.ranges.val.length
  · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    have later : ∀ (P : Usize → Prop), (∃ j : Usize, index.val ≤ j.val ∧ P j) ↔
        P index ∨ ∃ j : Usize, next.val ≤ j.val ∧ P j := by
      intro P
      constructor
      · rintro ⟨j, low, p⟩
        by_cases same : j = index
        · subst same; exact .inl p
        · have : j.val ≠ index.val := fun e => same (UScalar.eq_of_val_eq e)
          exact .inr ⟨j, by omega, p⟩
      · rintro (p | ⟨j, low, p⟩)
        · exact ⟨index, le_rfl, p⟩
        · exact ⟨j, by omega, p⟩
    by_cases cont : ContinuesAt context.ranges.val first index.val
    · cases found with
      | none =>
        obtain ⟨res, run, none', facts⟩ := continuing_spec context first next (some (.Class (rangeClass index)))
        refine ⟨res, by simp [UScalar.lt_equiv, inside, continues_spec, cont, range_class_eq, advance, run],
          ?_, fun c hc {_ _} J y => ?_⟩
        · rw [none']
          simp only [reduceCtorEq, false_and, true_and, false_iff, not_forall, not_not]
          exact ⟨index.val, le_rfl, cont⟩
        · rw [facts c hc J y, later (fun j => ContinuesAt context.ranges.val first j.val ∧ J.classes (rangeClass j) y)]
          simp [classDenote, cont]
      | some c0 =>
        obtain ⟨res, run, none', facts⟩ := continuing_spec context first next
          (some (.ObjectUnionOf ⟨c0, .Class (rangeClass index), alloc.vec.Vec.new ClassExpression⟩))
        refine ⟨res, by simp [UScalar.lt_equiv, inside, continues_spec, cont, range_class_eq, data_ontology.or,
          advance, run], ?_, fun c hc {_ _} J y => ?_⟩
        · rw [none']
          simp
        · rw [facts c hc J y, later (fun j => ContinuesAt context.ranges.val first j.val ∧
            J.classes (rangeClass j) y)]
          simp only [Option.some.injEq, exists_eq_left', or_iff, classDenote, cont, true_and]
          tauto
    · obtain ⟨res, run, none', facts⟩ := continuing_spec context first next found
      refine ⟨res, by simp [UScalar.lt_equiv, inside, continues_spec, cont, advance, run], ?_,
        fun c hc {_ _} J y => ?_⟩
      · rw [none']
        constructor
        · rintro ⟨f, all⟩
          refine ⟨f, fun j low => ?_⟩
          by_cases same : j = index.val
          · subst same; exact cont
          · exact all j (by omega)
        · rintro ⟨f, all⟩
          exact ⟨f, fun j low => all j (by omega)⟩
      · rw [facts c hc J y, later (fun j => ContinuesAt context.ranges.val first j.val ∧
          J.classes (rangeClass j) y)]
        simp [cont]
  · refine ⟨found, by simp [UScalar.lt_equiv, inside], ?_, fun c hc {_ _} J y => ?_⟩
    · constructor
      · intro h
        exact ⟨h, fun j low ⟨hj, _⟩ => by omega⟩
      · exact fun h => h.1
    · subst hc
      have none : ¬ ∃ j : Usize, index.val ≤ j.val ∧ ContinuesAt context.ranges.val first j.val ∧
          J.classes (rangeClass j) y := fun ⟨j, low, ⟨hj, _⟩, _⟩ => by omega
      simp [none]
termination_by context.ranges.val.length - index.val
decreasing_by all_goals omega

/-- A node in the classes of the ranges that continue the range at `first`, or
    outside `owl:Thing` when no range continues it. -/
def Covered (context : data_ontology.Context) (J : Interpretation Object' Value') (first : Option Usize)
    (y : Object') : Prop :=
  (∃ j : Usize, ContinuesAt context.ranges.val first j.val ∧ J.classes (rangeClass j) y) ∨
    ((∀ j, ¬ ContinuesAt context.ranges.val first j) ∧ ¬ J.classes thing y)

theorem cover_spec (context : data_ontology.Context) (first : Option Usize) :
    ∃ c, data_ontology.cover context first = .ok c ∧
      ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') y,
        (classDenote J c y ↔ Covered context J first y) := by
  obtain ⟨res, run, none', facts⟩ := continuing_spec.{w,x} context first 0#usize none
  rw [data_ontology.cover, run]
  cases res with
  | none =>
    have all : ∀ j, ¬ ContinuesAt context.ranges.val first j := fun j => (none'.mp rfl).2 j (by simp)
    refine ⟨.ObjectComplementOf (.Class thing), by simp [nothing_eq], fun J y => ?_⟩
    simp only [Covered, classDenote]
    constructor
    · intro h; exact .inr ⟨all, h⟩
    · rintro (⟨j, c, _⟩ | ⟨_, h⟩)
      · exact absurd c (all j.val)
      · exact h
  | some c =>
    refine ⟨c, by simp, fun J y => ?_⟩
    rw [facts c rfl J y]
    have some : ¬ ∀ j, ¬ ContinuesAt context.ranges.val first j := by
      intro all
      exact absurd (none'.mpr ⟨rfl, fun j _ => all j⟩) (by simp)
    simp only [Covered, reduceCtorEq, false_and, exists_false, false_or, show (0#usize).val = 0 from rfl,
      zero_le, true_and, some, and_false, or_false]

/-! ### The pairs of ranges -/

/-- What the axioms of the ranges at `first` and `second` say: the class of
    `second` inside the class of `first` when `first` matches `second`, and the
    two classes apart when neither matches the other, said once. -/
def PairFact (context : data_ontology.Context) (J : Interpretation Object' Value') (first second : Usize) : Prop :=
  ∀ (hf : first.val < context.ranges.val.length) (hs : second.val < context.ranges.val.length), first ≠ second →
    (Matches (context.ranges.val[first.val]'hf).val (context.ranges.val[second.val]'hs).val →
      ∀ y, J.classes (rangeClass second) y → J.classes (rangeClass first) y) ∧
    (¬ Matches (context.ranges.val[first.val]'hf).val (context.ranges.val[second.val]'hs).val →
      ¬ Matches (context.ranges.val[second.val]'hs).val (context.ranges.val[first.val]'hf).val →
      first.val < second.val →
      ∀ y, J.classes (rangeClass first) y → J.classes (rangeClass second) y → ¬ J.classes thing y)

theorem range_pairs_spec (context : data_ontology.Context) (first second : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.range_pairs context first second out = .ok res ∧
      ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ s : Usize, second.val ≤ s.val → s.val < context.ranges.val.length →
            PairFact context J first s) := by
  by_cases inside : first.val < context.ranges.val.length ∧ second.val < context.ranges.val.length
  · obtain ⟨hf, hs⟩ := inside
    have lookF : context.ranges.index_usize first = .ok context.ranges.val[first.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hf]
    have lookS : context.ranges.index_usize second = .ok context.ranges.val[second.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hs]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := second) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = second.val + 1 := by simpa using nextValue
    have tail : ∀ (o1 : alloc.vec.Vec AnnotatedAxiom) (new1 : List AnnotatedAxiom), o1.val = out.val ++ new1 →
        (∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new1, satisfies J b.axiom) ↔ PairFact context J first second)) →
        data_ontology.range_pairs context first second out = data_ontology.range_pairs context first next o1 →
        ∃ res, data_ontology.range_pairs context first second out = .ok res ∧
          ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
            ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
              ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ s : Usize, second.val ≤ s.val →
                s.val < context.ranges.val.length → PairFact context J first s) := by
      intro o1 new1 c1 m1 run
      obtain ⟨r, rRun, f⟩ := range_pairs_spec context first next o1
      refine ⟨r, by rw [run, rRun], fun out' h => ?_⟩
      obtain ⟨n2, c2, m2⟩ := f out' h
      refine ⟨new1 ++ n2, by rw [c2, c1]; simp, fun J => ?_⟩
      simp only [List.forall_mem_append]
      rw [m1 J, m2 J, nextIs]
      constructor
      · rintro ⟨here, later⟩ s low high
        by_cases same : s = second
        · subst same; exact here
        · have : s.val ≠ second.val := fun e => same (UScalar.eq_of_val_eq e)
          exact later s (by omega) high
      · intro all
        exact ⟨all second le_rfl hs, fun s low high => all s (by omega) high⟩
    by_cases same : first = second
    · subst same
      refine tail out [] (by simp) (fun J => ?_) ?_
      · simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, PairFact]
        intro _ _ ne; exact absurd rfl ne
      · rw [data_ontology.range_pairs]
        simp [UScalar.lt_equiv, hf, advance]
    · by_cases m : Matches (context.ranges.val[first.val]'hf).val (context.ranges.val[second.val]'hs).val
      · obtain ⟨r, pushRun, contents⟩ := push_spec out
          (.SubClassOf (.Class (rangeClass second)) (.Class (rangeClass first)))
        cases r with
        | none =>
          refine ⟨none, ?_, fun out' h => nomatch h⟩
          rw [data_ontology.range_pairs]
          simp [UScalar.lt_equiv, hf, hs, same, alloc.vec.Vec.index_slice_index, lookF, lookS,
            Rowl.LangRanges.range_matches_spec, m, range_class_eq, pushRun]
        | some o1 =>
          refine tail o1 _ (contents o1 rfl) (fun J => ?_) ?_
          · simp only [List.mem_singleton, forall_eq, satisfies, classDenote, PairFact]
            constructor
            · intro holds _ _ _
              exact ⟨fun _ => holds, fun no => absurd m no⟩
            · intro holds y inS
              exact (holds hf hs same).1 m y inS
          · rw [data_ontology.range_pairs]
            simp [UScalar.lt_equiv, hf, hs, same, alloc.vec.Vec.index_slice_index, lookF, lookS,
              Rowl.LangRanges.range_matches_spec, m, range_class_eq, pushRun, advance]
      · by_cases m' : Matches (context.ranges.val[second.val]'hs).val (context.ranges.val[first.val]'hf).val
        · refine tail out [] (by simp) (fun J => ?_) ?_
          · simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, PairFact]
            intro _ _ _
            exact ⟨fun mm => absurd mm m, fun _ no => absurd m' no⟩
          · rw [data_ontology.range_pairs]
            simp [UScalar.lt_equiv, hf, hs, same, alloc.vec.Vec.index_slice_index, lookF, lookS,
              Rowl.LangRanges.range_matches_spec, m, m', advance]
        · by_cases lt : first.val < second.val
          · obtain ⟨r, pushRun, contents⟩ := push_spec out (.SubClassOf
              (.ObjectIntersectionOf ⟨.Class (rangeClass first), .Class (rangeClass second),
                alloc.vec.Vec.new ClassExpression⟩) (.ObjectComplementOf (.Class thing)))
            cases r with
            | none =>
              refine ⟨none, ?_, fun out' h => nomatch h⟩
              rw [data_ontology.range_pairs]
              simp [UScalar.lt_equiv, hf, hs, same, alloc.vec.Vec.index_slice_index, lookF, lookS,
                Rowl.LangRanges.range_matches_spec, m, m', lt, range_class_eq, data_ontology.and, nothing_eq, pushRun]
            | some o1 =>
              refine tail o1 _ (contents o1 rfl) (fun J => ?_) ?_
              · simp only [List.mem_singleton, forall_eq, satisfies, PairFact]
                simp only [and_class_iff]
                simp only [classDenote]
                constructor
                · intro holds _ _ _
                  exact ⟨fun mm => absurd mm m, fun _ _ _ y inF inS => holds y ⟨inF, inS⟩⟩
                · intro holds y both
                  exact (holds hf hs same).2 m m' lt y both.1 both.2
              · rw [data_ontology.range_pairs]
                simp [UScalar.lt_equiv, hf, hs, same, alloc.vec.Vec.index_slice_index, lookF, lookS,
                  Rowl.LangRanges.range_matches_spec, m, m', lt, range_class_eq, data_ontology.and, nothing_eq,
                  pushRun, advance]
          · refine tail out [] (by simp) (fun J => ?_) ?_
            · simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, PairFact]
              intro _ _ _
              exact ⟨fun mm => absurd mm m, fun _ _ l => absurd l lt⟩
            · rw [data_ontology.range_pairs]
              simp [UScalar.lt_equiv, hf, hs, same, alloc.vec.Vec.index_slice_index, lookF, lookS,
                Rowl.LangRanges.range_matches_spec, m, m', lt, advance]
  · refine ⟨some out, ?_, fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    · rw [data_ontology.range_pairs]
      simp only [not_and_or] at inside
      rcases inside with h | h <;> simp [UScalar.lt_equiv, h]
    · simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
      intro s low high hf hs
      exact absurd ⟨hf, by omega⟩ inside
termination_by context.ranges.val.length - second.val
decreasing_by all_goals omega

/-! ### The axioms of each range -/

/-- What the axioms of the range at `i` say: its class inside the values with a
    language tag, its pairs, and, without free tags, its class inside the
    classes of the ranges that continue it. -/
def IndexFact (context : data_ontology.Context) (J : Interpretation Object' Value') (i : Usize) : Prop :=
  ∀ (hi : i.val < context.ranges.val.length),
    (∀ y, J.classes (rangeClass i) y → J.classes (kindClass .Plain) y ∧ ¬ J.classes (kindClass .String) y) ∧
    (∀ s : Usize, s.val < context.ranges.val.length → PairFact context J i s) ∧
    ((¬ ∃ t, Free (context.ranges.val[i.val]'hi).val (context.ranges.val.map (·.val)) t) →
      ∀ y, J.classes (rangeClass i) y → Covered context J (some i) y)

theorem range_axioms_from_spec (context : data_ontology.Context) (good : GoodRanges context.ranges.val)
    (index : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.range_axioms_from context index out = .ok res ∧
      ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ i : Usize, index.val ≤ i.val → i.val < context.ranges.val.length →
            IndexFact context J i) := by
  by_cases inside : index.val < context.ranges.val.length
  · have look : context.ranges.index_usize index = .ok context.ranges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have lower : context.ranges.val[index.val].val = [42#u8] ∨
        ∀ b ∈ context.ranges.val[index.val].val, Rowl.LangRanges.LowerLetter b.val := by
      obtain ⟨bytes, basic, low⟩ := good.1 _ (List.getElem_mem inside)
      exact Rowl.LangRanges.lowered_basic basic low
    have free := Rowl.LangRanges.free_tags_spec context.ranges.val[index.val] context.ranges lower
    obtain ⟨r1, run1, c1⟩ := push_spec out (.SubClassOf (.Class (rangeClass index)) taggedClass)
    cases r1 with
    | none =>
      refine ⟨none, ?_, fun out' h => nomatch h⟩
      rw [data_ontology.range_axioms_from]
      simp [UScalar.lt_equiv, inside, range_class_eq, tagged_class_eq, run1]
    | some o1 =>
      obtain ⟨r2, run2, f2⟩ := range_pairs_spec context index 0#usize o1
      cases r2 with
      | none =>
        refine ⟨none, ?_, fun out' h => nomatch h⟩
        rw [data_ontology.range_axioms_from]
        simp [UScalar.lt_equiv, inside, range_class_eq, tagged_class_eq, run1, run2]
      | some o2 =>
        obtain ⟨n2, c2, m2⟩ := f2 o2 rfl
        have tail : ∀ (o3 : alloc.vec.Vec AnnotatedAxiom) (n3 : List AnnotatedAxiom), o3.val = o2.val ++ n3 →
            (∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
              ((∀ b ∈ n3, satisfies J b.axiom) ↔
                ((¬ ∃ t, Free (context.ranges.val[index.val]'inside).val (context.ranges.val.map (·.val)) t) →
                  ∀ y, J.classes (rangeClass index) y → Covered context J (some index) y))) →
            data_ontology.range_axioms_from context index out = data_ontology.range_axioms_from context next o3 →
            ∃ res, data_ontology.range_axioms_from context index out = .ok res ∧
              ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
                ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
                  ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ i : Usize, index.val ≤ i.val →
                    i.val < context.ranges.val.length → IndexFact context J i) := by
          intro o3 n3 c3 m3 run
          obtain ⟨r, rRun, f⟩ := range_axioms_from_spec context good next o3
          refine ⟨r, by rw [run, rRun], fun out' h => ?_⟩
          obtain ⟨n4, c4, m4⟩ := f out' h
          refine ⟨[bare (.SubClassOf (.Class (rangeClass index)) taggedClass)] ++ n2 ++ n3 ++ n4,
            by rw [c4, c3, c2, c1 o1 rfl]; simp [bare], fun J => ?_⟩
          simp only [List.forall_mem_append, List.mem_singleton, forall_eq]
          rw [m2 J, m3 J, m4 J, nextIs]
          simp only [show (0#usize).val = 0 from rfl, Nat.zero_le, true_implies, bare, satisfies,
            tagged_class_iff, classDenote]
          constructor
          · rintro ⟨⟨⟨tagged, pairs⟩, cover⟩, later⟩ i low high
            by_cases same : i = index
            · subst same; exact fun _ => ⟨tagged, pairs, cover⟩
            · have : i.val ≠ index.val := fun e => same (UScalar.eq_of_val_eq e)
              exact later i (by omega) high
          · intro all
            obtain ⟨tagged, pairs, cover⟩ := all index le_rfl inside inside
            exact ⟨⟨⟨tagged, pairs⟩, cover⟩, fun i low high => all i (by omega) high⟩
        by_cases hasFree : ∃ t, Free (context.ranges.val[index.val]'inside).val (context.ranges.val.map (·.val)) t
        · refine tail o2 [] (by simp) (fun J => ?_) ?_
          · simp [hasFree]
          · rw [data_ontology.range_axioms_from]
            simp [UScalar.lt_equiv, inside, range_class_eq, tagged_class_eq, run1, run2, look, free, hasFree, advance]
        · obtain ⟨cov, covRun, covIff⟩ := cover_spec context (some index)
          obtain ⟨r3, run3, c3⟩ := push_spec o2 (.SubClassOf (.Class (rangeClass index)) cov)
          cases r3 with
          | none =>
            refine ⟨none, ?_, fun out' h => nomatch h⟩
            rw [data_ontology.range_axioms_from]
            simp [UScalar.lt_equiv, inside, range_class_eq, tagged_class_eq, run1, run2, look, free, hasFree, covRun,
              run3]
          | some o3 =>
            refine tail o3 _ (c3 o3 rfl) (fun J => ?_) ?_
            · simp only [List.mem_singleton, forall_eq, satisfies, classDenote, hasFree, not_false_eq_true,
                true_implies]
              exact forall_congr' fun y => imp_congr_right fun _ => covIff J y
            · rw [data_ontology.range_axioms_from]
              simp [UScalar.lt_equiv, inside, range_class_eq, tagged_class_eq, run1, run2, look, free, hasFree,
                covRun, run3, advance]
  · refine ⟨some out, ?_, fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    · rw [data_ontology.range_axioms_from]; simp [UScalar.lt_equiv, inside]
    · simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
      intro i low high; omega
termination_by context.ranges.val.length - index.val
decreasing_by all_goals omega

theorem star_index_spec (ranges : alloc.vec.Vec (alloc.vec.Vec U8)) (index : Usize) :
    ∃ r, data_ontology.star_index ranges index = .ok r ∧
      (∀ s, r = some s → ∃ h : s.val < ranges.val.length, (ranges.val[s.val]'h).val = [42#u8]) ∧
      (r = none → ∀ (j : Nat) (h : j < ranges.val.length), index.val ≤ j → (ranges.val[j]'h).val ≠ [42#u8]) := by
  rw [data_ontology.star_index]
  by_cases inside : index.val < ranges.val.length
  · have lookup : ranges.index_usize index = .ok ranges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases here : ranges.val[index.val].val = [42#u8]
    · exact ⟨some index, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
        Rowl.LangRanges.star_spec, here], fun s hs => (by cases hs; exact ⟨inside, here⟩), fun h => (nomatch h)⟩
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, found, missing⟩ := star_index_spec ranges next
      refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
        Rowl.LangRanges.star_spec, here, advance, run], found, fun h j hj low => ?_⟩
      rcases Nat.eq_or_lt_of_le low with same | after
      · subst same; exact here
      · exact missing h j hj (by omega)
  · exact ⟨none, by simp [UScalar.lt_equiv, inside], fun s hs => (nomatch hs), fun _ j hj low => by omega⟩
termination_by ranges.val.length - index.val
decreasing_by simp at nextValue; omega

/-! ### All the axioms of the ranges -/

/-- What the axiom on the values with a language tag says when there are
    ranges: they are in the class of `*`, or, with no `*`, in the classes of
    the ranges when every language tag matches a range. -/
def RootFact (context : data_ontology.Context) (J : Interpretation Object' Value') : Prop :=
  context.ranges.val ≠ [] → ∀ y, J.classes (kindClass .Plain) y → ¬ J.classes (kindClass .String) y →
    (∀ (s : Usize) (hs : s.val < context.ranges.val.length), (context.ranges.val[s.val]'hs).val = [42#u8] →
      J.classes (rangeClass s) y) ∧
    ((∀ r ∈ context.ranges.val, r.val ≠ [42#u8]) →
      (¬ ∃ t, LowerTag t ∧ ∀ r ∈ context.ranges.val, r.val ≠ [42#u8] → ¬ Matches r.val t) →
      Covered context J none y)

/-- What the axioms of the language ranges say. -/
def RangeFacts (context : data_ontology.Context) (J : Interpretation Object' Value') : Prop :=
  (∀ i : Usize, i.val < context.ranges.val.length → IndexFact context J i) ∧ RootFact context J

theorem range_axioms_spec (context : data_ontology.Context) (good : GoodRanges context.ranges.val)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.range_axioms context out = .ok res ∧
      ∀ out', res = some out' → ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ RangeFacts context J) := by
  by_cases empty : context.ranges.val = []
  · have len : alloc.vec.Vec.len context.ranges = 0#usize := UScalar.eq_of_val_eq (by simp [empty])
    refine ⟨some out, by rw [data_ontology.range_axioms]; simp [len], fun out' h =>
      ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff, RangeFacts, RootFact]
    exact ⟨fun i hi => by simp [empty] at hi, fun ne => absurd empty ne⟩
  · have len : ¬ alloc.vec.Vec.len context.ranges = 0#usize := fun h => empty (by
      have := congrArg UScalar.val h; simpa using this)
    obtain ⟨r1, run1, f1⟩ := range_axioms_from_spec context good 0#usize out
    cases r1 with
    | none => exact ⟨none, by rw [data_ontology.range_axioms]; simp [len, run1], fun out' h => nomatch h⟩
    | some o1 =>
      obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
      have from' : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ n1, satisfies J b.axiom) ↔
            ∀ i : Usize, i.val < context.ranges.val.length → IndexFact context J i) := by
        intro Object' Value' J
        rw [m1 J]
        simp [show (0#usize).val = 0 from rfl]
      obtain ⟨s, sRun, found, missing⟩ := star_index_spec context.ranges 0#usize
      cases s with
      | some s0 =>
        obtain ⟨h0, star0⟩ := found s0 rfl
        obtain ⟨r2, run2, c2⟩ := push_spec o1 (.SubClassOf taggedClass (.Class (rangeClass s0)))
        refine ⟨r2, by rw [data_ontology.range_axioms]; simp [len, run1, sRun, tagged_class_eq, range_class_eq, run2],
          fun out' h => ?_⟩
        refine ⟨n1 ++ [bare (.SubClassOf taggedClass (.Class (rangeClass s0)))], by rw [c2 out' h, c1]; simp [bare],
          fun J => ?_⟩
        simp only [List.forall_mem_append, List.mem_singleton, forall_eq]
        rw [from' J]
        simp only [bare, satisfies, tagged_class_iff, classDenote]
        have unique : ∀ (s : Usize) (hs : s.val < context.ranges.val.length),
            (context.ranges.val[s.val]'hs).val = [42#u8] → s = s0 := by
          intro s hs star
          apply UScalar.eq_of_val_eq
          have e : (context.ranges.val.map (·.val))[s.val]'(by simpa using hs) =
              (context.ranges.val.map (·.val))[s0.val]'(by simpa using h0) := by
            simp [star, star0]
          exact (List.Nodup.getElem_inj_iff good.2).mp e
        unfold RangeFacts RootFact
        constructor
        · rintro ⟨idx, root⟩
          refine ⟨idx, fun _ y plain notString => ⟨fun s hs star => ?_, fun noStar =>
            absurd star0 (noStar _ (List.getElem_mem h0))⟩⟩
          rw [unique s hs star]
          exact root y ⟨plain, notString⟩
        · rintro ⟨idx, root⟩
          exact ⟨idx, fun y both => (root empty y both.1 both.2).1 s0 h0 star0⟩
      | none =>
        have noStar : ∀ r ∈ context.ranges.val, r.val ≠ [42#u8] := by
          intro r mem
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem mem
          exact missing rfl j hj (by simp)
        by_cases rootFree : ∃ t, LowerTag t ∧ ∀ r ∈ context.ranges.val, r.val ≠ [42#u8] → ¬ Matches r.val t
        · refine ⟨some o1, by rw [data_ontology.range_axioms]; simp [len, run1, sRun,
            Rowl.LangRanges.root_free_spec, rootFree], fun out' h => ?_⟩
          cases h
          refine ⟨n1, c1, fun J => ?_⟩
          rw [from' J]
          unfold RangeFacts RootFact
          constructor
          · intro idx
            exact ⟨idx, fun _ y _ _ => ⟨fun s hs star => absurd star (noStar _ (List.getElem_mem hs)),
              fun _ no => absurd rootFree no⟩⟩
          · exact fun h => h.1
        · obtain ⟨cov, covRun, covIff⟩ := cover_spec context none
          obtain ⟨r2, run2, c2⟩ := push_spec o1 (.SubClassOf taggedClass cov)
          refine ⟨r2, by rw [data_ontology.range_axioms]; simp [len, run1, sRun, Rowl.LangRanges.root_free_spec,
            rootFree, tagged_class_eq, covRun, run2], fun out' h => ?_⟩
          refine ⟨n1 ++ [bare (.SubClassOf taggedClass cov)], by rw [c2 out' h, c1]; simp [bare], fun J => ?_⟩
          simp only [List.forall_mem_append, List.mem_singleton, forall_eq]
          rw [from' J]
          simp only [bare, satisfies, tagged_class_iff]
          unfold RangeFacts RootFact
          constructor
          · rintro ⟨idx, root⟩
            exact ⟨idx, fun _ y plain notString => ⟨fun s hs star => absurd star (noStar _ (List.getElem_mem hs)),
              fun _ _ => (covIff J y).mp (root y ⟨plain, notString⟩)⟩⟩
          · rintro ⟨idx, root⟩
            exact ⟨idx, fun y both => (covIff J y).mpr ((root empty y both.1 both.2).2 noStar rootFree)⟩

/-! ### A language tag for a node -/

/-- A well-formed language tag in lower case: `en`. -/
theorem en_tag : LowerTag [101#u8, 110#u8] := by
  refine ⟨?_, ?_⟩
  · simpa using Rowl.LangTag.two_letters_well_formed 101 110 (by omega) (by omega)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp [Rowl.LangRanges.LowerLetter]

/-- The depth of a range: `*` at the root, every other range below the ranges
    it continues. -/
def depth (r : List U8) : Nat := if r = [42#u8] then 0 else r.length + 1

theorem depth_continues {r r' : List U8} (c : Continues r r') : depth r < depth r' := by
  rcases c with ⟨rfl, ne⟩ | ⟨ne, s, rfl⟩
  · simp [depth, ne]
  · simp only [depth, ne, ↓reduceIte, Rowl.LangRanges.continued_not_star, List.length_append, List.length_cons]
    omega

/-- A range that matches another range continues it. -/
theorem continues_of_matches {r r' : List U8} (m : Matches r r') (ne : r ≠ r') : Continues r r' := by
  rcases m with star | same | ⟨s, rfl⟩
  · exact .inl ⟨star, fun h => ne (star.trans h.symm)⟩
  · exact absurd same.symm ne
  · by_cases hs : r = [42#u8]
    · exact .inl ⟨hs, Rowl.LangRanges.continued_not_star _ _⟩
    · exact .inr ⟨hs, s, rfl⟩

/-- The classes of two ranges of which neither matches the other are apart. -/
theorem range_facts_apart {context : data_ontology.Context} {J : Interpretation Object' Value'}
    (facts : RangeFacts context J) {i j : Usize} (hi : i.val < context.ranges.val.length)
    (hj : j.val < context.ranges.val.length)
    (m : ¬ Matches (context.ranges.val[i.val]'hi).val (context.ranges.val[j.val]'hj).val)
    (m' : ¬ Matches (context.ranges.val[j.val]'hj).val (context.ranges.val[i.val]'hi).val) {y : Object'}
    (inI : J.classes (rangeClass i) y) (inJ : J.classes (rangeClass j) y) : ¬ J.classes thing y := by
  have ne : i ≠ j := by
    rintro rfl
    exact m (Or.inr (Or.inl rfl))
  rcases Nat.lt_or_ge i.val j.val with lt | ge
  · exact ((facts.1 i hi hi).2.1 j hj hi hj ne).2 m m' lt y inI inJ
  · have lt : j.val < i.val := lt_of_le_of_ne ge (fun e => ne (UScalar.eq_of_val_eq e.symm))
    exact ((facts.1 j hj hj).2.1 i hi hj hi (Ne.symm ne)).2 m' m lt y inJ inI

/-- The class of a range lies inside the class of every range that matches
    it. -/
theorem range_facts_inside {context : data_ontology.Context} {J : Interpretation Object' Value'}
    (facts : RangeFacts context J) {i j : Usize} (hi : i.val < context.ranges.val.length)
    (hj : j.val < context.ranges.val.length) (ne : i ≠ j)
    (m : Matches (context.ranges.val[i.val]'hi).val (context.ranges.val[j.val]'hj).val) {y : Object'}
    (inJ : J.classes (rangeClass j) y) : J.classes (rangeClass i) y :=
  ((facts.1 i hi hi).2.1 j hj hi hj ne).1 m y inJ

/-- Distinct indices of good ranges hold distinct ranges. -/
theorem range_index_injective {ranges : List (alloc.vec.Vec U8)} (good : GoodRanges ranges) {i j : Usize}
    (hi : i.val < ranges.length) (hj : j.val < ranges.length) (same : (ranges[i.val]'hi).val = (ranges[j.val]'hj).val) :
    i = j := by
  apply UScalar.eq_of_val_eq
  have e : (ranges.map (·.val))[i.val]'(by simpa using hi) = (ranges.map (·.val))[j.val]'(by simpa using hj) := by
    simp [same]
  exact (List.Nodup.getElem_inj_iff good.2).mp e

/-- A node of `rdf:PlainLiteral` that is no string has a language tag in lower
    case that the ranges whose classes hold there match, and no other range:
    a free tag of its deepest range, or a tag that no range matches. -/
theorem choose_tag {context : data_ontology.Context} {J : Interpretation Object' Value'}
    (facts : RangeFacts context J) (good : GoodRanges context.ranges.val) (jThing : ∀ y, J.classes thing y)
    {y : Object'} (plain : J.classes (kindClass .Plain) y) (notString : ¬ J.classes (kindClass .String) y) :
    ∃ t, LowerTag t ∧ ∀ (i : Usize) (h : i.val < context.ranges.val.length),
      (J.classes (rangeClass i) y ↔ Matches (context.ranges.val[i.val]'h).val t) := by
  by_cases empty : context.ranges.val = []
  · exact ⟨[101#u8, 110#u8], en_tag, fun i h => absurd h (by simp [empty])⟩
  have rootHere := facts.2 empty y plain notString
  -- the indices of the ranges whose classes hold at the node
  let held : Finset ℕ := (Finset.range context.ranges.val.length).filter
    (fun i => ∃ u : Usize, u.val = i ∧ J.classes (rangeClass u) y)
  have inHeld : ∀ (u : Usize), u.val < context.ranges.val.length → J.classes (rangeClass u) y → u.val ∈ held :=
    fun u hu holds => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu, u, rfl, holds⟩
  by_cases none : held = ∅
  · have notHeld : ∀ (u : Usize), u.val < context.ranges.val.length → ¬ J.classes (rangeClass u) y := by
      intro u hu holds
      have := inHeld u hu holds
      rw [none] at this
      simp at this
    have noStar : ∀ r ∈ context.ranges.val, r.val ≠ [42#u8] := by
      intro r mem star
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem mem
      obtain ⟨u, rfl⟩ := Rowl.DataRegions.usize_of_index context.ranges j hj
      exact notHeld u hj (rootHere.1 u hj star)
    have rootFree : ∃ t, LowerTag t ∧ ∀ r ∈ context.ranges.val, r.val ≠ [42#u8] → ¬ Matches r.val t := by
      by_contra no
      rcases rootHere.2 noStar no with ⟨j, ⟨hj, _⟩, holds⟩ | ⟨_, notThing⟩
      · exact notHeld j hj holds
      · exact notThing (jThing y)
    obtain ⟨t, lt, notMatch⟩ := rootFree
    exact ⟨t, lt, fun i h => ⟨fun holds => absurd holds (notHeld i h),
      fun m => absurd m (notMatch _ (List.getElem_mem h) (noStar _ (List.getElem_mem h)))⟩⟩
  · -- the deepest range whose class holds
    let depthAt : ℕ → ℕ := fun i => if h : i < context.ranges.val.length then depth (context.ranges.val[i]'h).val else 0
    obtain ⟨best, bestIn, bestMax⟩ := Finset.exists_max_image held depthAt (Finset.nonempty_iff_ne_empty.mpr none)
    obtain ⟨bestLt, b, rfl, bHolds⟩ := Finset.mem_filter.mp bestIn
    have hb : b.val < context.ranges.val.length := Finset.mem_range.mp bestLt
    have deepest : ∀ (u : Usize) (hu : u.val < context.ranges.val.length), J.classes (rangeClass u) y →
        depth (context.ranges.val[u.val]'hu).val ≤ depth (context.ranges.val[b.val]'hb).val := by
      intro u hu holds
      have := bestMax u.val (inHeld u hu holds)
      simpa [depthAt, hu, hb] using this
    -- the deepest range has free tags
    have freeTags : ∃ t, Free (context.ranges.val[b.val]'hb).val (context.ranges.val.map (·.val)) t := by
      by_contra noFree
      rcases (facts.1 b hb hb).2.2 noFree y bHolds with ⟨j, ⟨hj, _, cont⟩, holds⟩ | ⟨_, notThing⟩
      · have := deepest j hj holds
        have := depth_continues cont
        omega
      · exact notThing (jThing y)
    obtain ⟨t, lt, mb, notCont⟩ := freeTags
    refine ⟨t, lt, fun i h => ⟨fun holds => ?_, fun m => ?_⟩⟩
    · by_cases comparable : Matches (context.ranges.val[i.val]'h).val (context.ranges.val[b.val]'hb).val ∨
          Matches (context.ranges.val[b.val]'hb).val (context.ranges.val[i.val]'h).val
      · rcases comparable with mib | mbi
        · exact Rowl.LangRanges.matches_trans mib mb
        · by_cases same : (context.ranges.val[b.val]'hb).val = (context.ranges.val[i.val]'h).val
          · rw [← same]; exact mb
          · have := depth_continues (continues_of_matches mbi same)
            have := deepest i h holds
            omega
      · simp only [not_or] at comparable
        exact absurd (jThing y) (range_facts_apart facts h hb comparable.1 comparable.2 holds bHolds)
    · by_cases star : (context.ranges.val[i.val]'h).val = [42#u8]
      · exact rootHere.1 i h star
      rcases Rowl.LangRanges.matches_comparable m mb with mib | mbi
      · by_cases same : i = b
        · subst same; exact bHolds
        · exact range_facts_inside facts h hb same mib bHolds
      · by_cases same : (context.ranges.val[b.val]'hb).val = (context.ranges.val[i.val]'h).val
        · have := range_index_injective good hb h same
          subst this
          exact bHolds
        · exact absurd m (notCont _ (List.mem_map_of_mem (List.getElem_mem h)) (continues_of_matches mbi same))

end Rowl.DataRanges
