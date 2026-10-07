import Rowl.Copies
import Rowl.DatatypeDefinitions
import Rowl.KeyEncoding

/-!
# Datatype definitions unfolded

`unfolding::unfold_items` replaces each datatype that a closure defines, in
the data ranges of the closure's axioms, by the data range of its definition,
unfolded in turn, and drops the definitions and the annotation axioms;
`unfolding::unfold_question` does the same for a question's class expression.
Both look the definitions up in the closure's definitions, copied once
(`unfolding::definitions`).

An interpretation in which the definitions hold gives a data range and its
unfolding the same values (`unfold_range_spec`), and so a class expression and
its unfolding the same instances (`unfold_class_spec`) and an axiom and its
unfolding the same truth (`unfold_axiom_spec`). Conversely, an interpretation
of the unfolding becomes one of the closure when each defined datatype gets
the values of the unfolding of its definition (`extend`): it then gives each
data range of the closure the values that the interpretation gives its
unfolding, and the definitions hold. So a closure and its unfolding have the
same models up to the defined datatypes, and they agree on consistency,
satisfiability, subsumption and instances (`unfolded_consistent`,
`unfolded_satisfiable`, `unfolded_subsumed`, `unfolded_instance`), under every
datatype map that has none of the defined datatypes (`DefinesNew`), as OWL 2
asks of a datatype definition (Structural Specification §9.4).
-/

namespace Rowl.Unfolding
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model Rowl.Owl
open Rowl.DataMeaning (classIndividuals)
open Rowl.DataAxioms (axiomIndividuals)
open Rowl.KeyEncoding (keyIndividuals IsKey closureIndividuals Keyed NamesKeyed)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
universe u v w

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-! ## The definitions -/

/-- The data range of the first definition of a datatype among axioms. -/
def definitionOf : List AnnotatedAxiom → Datatype → Option DataRange
  | [], _ => none
  | a :: rest, dt =>
    match a.axiom with
    | .DatatypeDefinition d r => if d.iri.spelling.val = dt.iri.spelling.val then some r else definitionOf rest dt
    | _ => definitionOf rest dt

private theorem datatype_spelling (a b : Datatype) : a.iri.spelling.val = b.iri.spelling.val ↔ a = b := by
  obtain ⟨⟨sa⟩⟩ := a
  obtain ⟨⟨sb⟩⟩ := b
  simp only [Datatype.mk.injEq, Iri.mk.injEq]
  exact ⟨fun h => (alloc.vec.Vec.eq_iff _ _).mpr h, fun h => by rw [h]⟩

theorem definition_from_eq (defs : alloc.vec.Vec AnnotatedAxiom) (dt : Datatype) (index : Usize) :
    unfolding.definition_from defs dt index = .ok (definitionOf (defs.val.drop index.val) dt) := by
  rw [unfolding.definition_from]
  by_cases inside : index.val < defs.val.length
  · have lookup : defs.index_usize index = .ok defs.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have recursive := definition_from_eq defs dt next
    rw [List.drop_eq_getElem_cons inside]
    cases h : defs.val[index.val].axiom <;>
      simp [inside, alloc.vec.Vec.index_slice_index, lookup, h, definitionOf, advance, recursive, nextIs,
        Rowl.Symbols.same_spelling_total_correct]
    all_goals split <;> rfl
  · have empty : defs.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside, empty, definitionOf]
termination_by defs.val.length - index.val
decreasing_by omega

theorem definitionOf_mem {defs : List AnnotatedAxiom} {dt : Datatype} {r : DataRange}
    (found : definitionOf defs dt = some r) : ∃ a ∈ defs, a.axiom = .DatatypeDefinition dt r := by
  induction defs with
  | nil => simp [definitionOf] at found
  | cons a rest ih =>
    simp only [definitionOf] at found
    split at found
    · rename_i d r' h
      by_cases same : d.iri.spelling.val = dt.iri.spelling.val
      · simp only [same, ↓reduceIte, Option.some.injEq] at found
        rw [datatype_spelling] at same
        subst same found
        exact ⟨a, List.mem_cons_self, h⟩
      · simp only [same, ↓reduceIte] at found
        obtain ⟨b, mb, hb⟩ := ih found
        exact ⟨b, List.mem_cons_of_mem _ mb, hb⟩
    · obtain ⟨b, mb, hb⟩ := ih found
      exact ⟨b, List.mem_cons_of_mem _ mb, hb⟩

/-- The definitions hold in an interpretation. -/
def DefinitionsHold {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (defs : List AnnotatedAxiom) : Prop :=
  ∀ a ∈ defs, satisfies I a.axiom

theorem defined_values {Object : Type u} {Value : Type v} {I : Interpretation Object Value}
    {defs : List AnnotatedAxiom} (hold : DefinitionsHold I defs) {dt : Datatype} {r : DataRange}
    (found : definitionOf defs dt = some r) (x : Value) : I.datatypes dt x ↔ dataDenote I r x := by
  obtain ⟨a, ma, ha⟩ := definitionOf_mem found
  have := hold a ma
  rw [ha] at this
  exact this x

/-! ## The interpretation of the defined datatypes -/

/-- An interpretation in which each defined datatype has the values of the
    unfolding of its definition. -/
def extend {Object : Type u} {Value : Type v} (defs : alloc.vec.Vec AnnotatedAxiom)
    (I : Interpretation Object Value) : Interpretation Object Value :=
  { I with datatypes := fun dt x =>
      match definitionOf defs.val dt with
      | some r => ∃ (fuel : Usize) (r' : DataRange), unfolding.unfold_range defs r fuel = .ok (some r') ∧
          dataDenote I r' x
      | none => I.datatypes dt x }

/-- What the unfolding of a data range keeps: its values where the
    definitions hold, and the values of the extension. -/
def RangeKeeps (defs : alloc.vec.Vec AnnotatedAxiom) (r r' : DataRange) : Prop :=
  (∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), DefinitionsHold I defs.val →
    ∀ x, dataDenote I r x ↔ dataDenote I r' x) ∧
  (∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value) x,
    dataDenote (extend defs I) r x ↔ dataDenote I r' x)

/-- What an unfolding with some fuel gives: the same with more fuel, and what
    `RangeKeeps` says. -/
def RangeSpec (defs : alloc.vec.Vec AnnotatedAxiom) (r : DataRange) (fuel : Usize) : Prop :=
  ∃ res, unfolding.unfold_range defs r fuel = .ok res ∧ ∀ r', res = some r' →
    (∀ g : Usize, fuel.val ≤ g.val → unfolding.unfold_range defs r g = .ok (some r')) ∧ RangeKeeps.{u,v} defs r r'

section Sizes
variable {α : Type} [SizeOf α]

private theorem listN_mem_size {n : Nat} (xs : Aeneas.Data.ListN.ListN α n) {x : α} (h : x ∈ xs.toList) :
    sizeOf x < sizeOf xs := by
  induction xs with
  | nil => simp [Aeneas.Data.ListN.ListN.toList] at h
  | cons head tail ih =>
    simp only [Aeneas.Data.ListN.ListN.toList, List.mem_cons] at h
    rcases h with rfl | h
    · simp +arith
    · have := ih h
      simp only [Data.ListN.ListN.cons.sizeOf_spec]
      omega

private theorem vec_mem_size (xs : alloc.vec.Vec α) {x : α} (h : x ∈ xs.val) : sizeOf x < sizeOf xs := by
  have := listN_mem_size xs.slice.list h
  cases xs with | mk slice => cases slice; simp_all [alloc.vec.Vec.val, Slice.val]; omega

private theorem elements_size (xs : AtLeastTwo α) {x : α} (h : x ∈ xs.elements) : sizeOf x < sizeOf xs := by
  simp only [AtLeastTwo.elements, List.mem_cons] at h
  cases xs with
  | mk first second rest =>
    rcases h with rfl | rfl | h
    · simp +arith
    · simp +arith
    · have := vec_mem_size rest h
      simp +arith only [AtLeastTwo.mk.sizeOf_spec]
      omega

private theorem members_bound (xs : AtLeastTwo α) (e : α) (h : e ∈ xs.elements) :
    sizeOf e < 1 + sizeOf xs := by
  have := elements_size xs h
  omega

end Sizes

private theorem forall2_left {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ a ∈ l1, ∃ b ∈ l2, R a b
  | _, _, .nil, _, member => by cases member
  | _, _, .cons head tail, a, member => by
    rcases List.mem_cons.mp member with same | later
    · exact ⟨_, List.mem_cons_self, same ▸ head⟩
    · obtain ⟨b, inside, rel⟩ := forall2_left tail a later
      exact ⟨b, List.mem_cons_of_mem _ inside, rel⟩

private theorem forall2_right {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ b ∈ l2, ∃ a ∈ l1, R a b
  | _, _, .nil, _, member => by cases member
  | _, _, .cons head tail, b, member => by
    rcases List.mem_cons.mp member with same | later
    · exact ⟨_, List.mem_cons_self, same ▸ head⟩
    · obtain ⟨a, inside, rel⟩ := forall2_right tail b later
      exact ⟨a, List.mem_cons_of_mem _ inside, rel⟩

/-- Members related one by one hold for all members alike. -/
theorem forall2_all {α β : Type} {R : α → β → Prop} {P : α → Prop} {Q : β → Prop} {l1 : List α} {l2 : List β}
    (pairs : List.Forall₂ R l1 l2) (each : ∀ a b, R a b → (P a ↔ Q b)) : (∀ a ∈ l1, P a) ↔ (∀ b ∈ l2, Q b) := by
  constructor
  · intro all b member
    obtain ⟨a, inside, rel⟩ := forall2_right pairs b member
    exact (each a b rel).mp (all a inside)
  · intro all a member
    obtain ⟨b, inside, rel⟩ := forall2_left pairs a member
    exact (each a b rel).mpr (all b inside)

/-- Members related one by one hold for some member alike. -/
theorem forall2_any {α β : Type} {R : α → β → Prop} {P : α → Prop} {Q : β → Prop} {l1 : List α} {l2 : List β}
    (pairs : List.Forall₂ R l1 l2) (each : ∀ a b, R a b → (P a ↔ Q b)) : (∃ a ∈ l1, P a) ↔ (∃ b ∈ l2, Q b) := by
  constructor
  · rintro ⟨a, member, holds⟩
    obtain ⟨b, inside, rel⟩ := forall2_left pairs a member
    exact ⟨b, inside, (each a b rel).mp holds⟩
  · rintro ⟨b, member, holds⟩
    obtain ⟨a, inside, rel⟩ := forall2_right pairs b member
    exact ⟨a, inside, (each a b rel).mpr holds⟩

theorem forall2_map {α β γ : Type _} {R : α → β → Prop} {f : α → γ} {g : β → γ} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → (∀ a b, R a b → f a = g b) → l1.map f = l2.map g
  | _, _, .nil, _ => rfl
  | _, _, .cons head tail, each => by simp [each _ _ head, forall2_map tail each]

/-! ## Data ranges -/

theorem unfold_range_list_spec (defs : alloc.vec.Vec AnnotatedAxiom) (ranges : alloc.vec.Vec DataRange)
    (fuel index : Usize) (out : alloc.vec.Vec DataRange) (each : ∀ r ∈ ranges.val, RangeSpec.{u,v} defs r fuel) :
    ∃ res, unfolding.unfold_range_list defs ranges fuel index out = .ok res ∧ ∀ result, res = some result →
      (∀ g : Usize, fuel.val ≤ g.val → unfolding.unfold_range_list defs ranges g index out = .ok (some result)) ∧
      ∃ ys, result.val = out.val ++ ys ∧ List.Forall₂ (RangeKeeps.{u,v} defs) (ranges.val.drop index.val) ys := by
  rw [unfolding.unfold_range_list]
  by_cases more : index.val < ranges.val.length
  · have lookup : ranges.index_usize index = .ok ranges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    by_cases fits : out.val.length < Usize.max
    · obtain ⟨res, run, facts⟩ := each _ (List.getElem_mem more)
      cases res with
      | none =>
        exact ⟨none, by simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits,
          alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
      | some r' =>
        obtain ⟨mono, keeps⟩ := facts r' rfl
        obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out r' fits)
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = index.val + 1 := by simpa using nextValue
        obtain ⟨res2, run2, facts2⟩ := unfold_range_list_spec defs ranges fuel next pushed each
        refine ⟨res2, by simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits,
          alloc.vec.Vec.index_slice_index, lookup, run, push, advance, run2], fun result hres => ?_⟩
        obtain ⟨mono2, ys, value, pairs⟩ := facts2 result hres
        refine ⟨fun g hg => ?_, r' :: ys, ?_, ?_⟩
        · rw [unfolding.unfold_range_list]
          simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits,
            alloc.vec.Vec.index_slice_index, lookup, mono g hg, push, advance, mono2 g hg]
        · rw [value, contents]
          simp
        · rw [List.drop_eq_getElem_cons more]
          rw [nextIs] at pairs
          exact .cons keeps pairs
    · exact ⟨none, by simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits], by simp⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, more], fun result hres => ?_⟩
    cases hres
    refine ⟨fun g _ => by rw [unfolding.unfold_range_list]; simp [UScalar.lt_equiv, more], [], by simp, ?_⟩
    rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt more)]
    exact .nil
termination_by ranges.val.length - index.val
decreasing_by omega

theorem unfold_range_members_spec (defs : alloc.vec.Vec AnnotatedAxiom) (members : AtLeastTwo DataRange)
    (fuel : Usize) (each : ∀ r ∈ members.elements, RangeSpec.{u,v} defs r fuel) :
    ∃ res, unfolding.unfold_range_members defs members fuel = .ok res ∧ ∀ result, res = some result →
      (∀ g : Usize, fuel.val ≤ g.val → unfolding.unfold_range_members defs members g = .ok (some result)) ∧
      List.Forall₂ (RangeKeeps.{u,v} defs) members.elements result.elements := by
  rw [unfolding.unfold_range_members]
  obtain ⟨r1, run1, facts1⟩ := each members.first (by simp [AtLeastTwo.elements])
  obtain ⟨r2, run2, facts2⟩ := each members.second (by simp [AtLeastTwo.elements])
  obtain ⟨r3, run3, facts3⟩ := unfold_range_list_spec.{u,v} defs members.rest fuel 0#usize
    (alloc.vec.Vec.new DataRange) (fun r mem => each r (by simp [AtLeastTwo.elements, mem]))
  cases r1 with
  | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
  | some first =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
    | some second =>
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
      | some rest =>
        obtain ⟨mono1, keeps1⟩ := facts1 first rfl
        obtain ⟨mono2, keeps2⟩ := facts2 second rfl
        obtain ⟨mono3, ys, value, pairs⟩ := facts3 rest rfl
        refine ⟨some ⟨first, second, rest⟩, by simp [run1, run2, run3], fun result hres => ?_⟩
        cases hres
        refine ⟨fun g hg => ?_, ?_⟩
        · rw [unfolding.unfold_range_members]
          simp [mono1 g hg, mono2 g hg, mono3 g hg]
        · have restIs : rest.val = ys := by simpa using value
          simp only [AtLeastTwo.elements, restIs]
          exact .cons keeps1 (.cons keeps2 (by simpa using pairs))

/-- The unfolding of a data range: with more fuel the same, and with the
    values of the range where the definitions hold and under the extension. -/
theorem unfold_range_spec (defs : alloc.vec.Vec AnnotatedAxiom) (r : DataRange) (fuel : Usize) :
    RangeSpec.{u,v} defs r fuel := by
  cases r with
  | Datatype dt =>
    cases found : definitionOf defs.val dt with
    | none =>
      refine ⟨some (.Datatype dt), by simp [unfolding.unfold_range, definition_from_eq, found,
        Rowl.Copies.copy_datatype_eq], fun r' hr => ?_⟩
      cases hr
      refine ⟨fun g _ => by simp [unfolding.unfold_range, definition_from_eq, found, Rowl.Copies.copy_datatype_eq],
        fun I _ x => Iff.rfl, fun I x => ?_⟩
      rw [dataDenote, dataDenote]
      simp [extend, found]
    | some dr =>
      by_cases positive : 0 < fuel.val
      · obtain ⟨less, lessRun, lessValue⟩ := WP.spec_imp_exists
          (Usize.sub_spec (x := fuel) (y := 1#usize) (by simp; omega))
        have lessIs : less.val = fuel.val - 1 := by simp at lessValue; exact lessValue.1
        obtain ⟨res, run, facts⟩ := unfold_range_spec defs dr less
        refine ⟨res, by simp [unfolding.unfold_range, definition_from_eq, found, UScalar.lt_equiv, positive,
          lessRun, run], fun r' hr => ?_⟩
        obtain ⟨mono, keepsHold, keepsExtend⟩ := facts r' hr
        refine ⟨fun g hg => ?_, fun I hold x => ?_, fun I x => ?_⟩
        · obtain ⟨gl, glRun, glValue⟩ := WP.spec_imp_exists
            (Usize.sub_spec (x := g) (y := 1#usize) (by simp; omega))
          have glIs : gl.val = g.val - 1 := by simp at glValue; exact glValue.1
          rw [unfolding.unfold_range]
          simp [definition_from_eq, found, UScalar.lt_equiv, (by omega : 0 < g.val), glRun,
            mono gl (by omega)]
        · rw [dataDenote]
          exact (defined_values hold found x).trans (keepsHold I hold x)
        · rw [dataDenote]
          simp only [extend, found]
          constructor
          · rintro ⟨g, r'', run'', holds⟩
            by_cases small : g.val < fuel.val
            · obtain ⟨res'', run2, facts''⟩ := unfold_range_spec defs dr g
              rw [run''] at run2
              have same := Result.ok_injective run2
              obtain ⟨mono'', -⟩ := facts'' r'' same.symm
              have atLess := mono'' less (by omega)
              rw [run] at atLess
              have := Result.ok_injective atLess
              rw [hr] at this
              cases this
              exact holds
            · have atG := mono g (by omega)
              rw [run''] at atG
              cases Result.ok_injective atG
              exact holds
          · intro holds
            exact ⟨less, r', by rw [run, hr], holds⟩
      · refine ⟨none, by simp [unfolding.unfold_range, definition_from_eq, found, UScalar.lt_equiv, positive],
          by simp⟩
  | Intersection members =>
    obtain ⟨res, run, facts⟩ := unfold_range_members_spec.{u,v} defs members fuel (fun e mem => by
      have := members_bound members e mem
      exact unfold_range_spec defs e fuel)
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_range, run], by simp⟩
    | some ms =>
      obtain ⟨mono, pairs⟩ := facts ms rfl
      refine ⟨some (.Intersection ms), by simp [unfolding.unfold_range, run], fun r' hr => ?_⟩
      cases hr
      refine ⟨fun g hg => by rw [unfolding.unfold_range]; simp [mono g hg], fun I hold x => ?_, fun I x => ?_⟩
      · have every := forall2_all (P := fun e => dataDenote I e x) (Q := fun e => dataDenote I e x) pairs
          (fun _ _ keeps => keeps.1 I hold x)
        rw [dataDenote, dataDenote]
        simpa [AtLeastTwo.elements] using every
      · have every := forall2_all (P := fun e => dataDenote (extend defs I) e x) (Q := fun e => dataDenote I e x)
          pairs (fun _ _ keeps => keeps.2 I x)
        rw [dataDenote, dataDenote]
        simpa [AtLeastTwo.elements] using every
  | Union members =>
    obtain ⟨res, run, facts⟩ := unfold_range_members_spec.{u,v} defs members fuel (fun e mem => by
      have := members_bound members e mem
      exact unfold_range_spec defs e fuel)
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_range, run], by simp⟩
    | some ms =>
      obtain ⟨mono, pairs⟩ := facts ms rfl
      refine ⟨some (.Union ms), by simp [unfolding.unfold_range, run], fun r' hr => ?_⟩
      cases hr
      refine ⟨fun g hg => by rw [unfolding.unfold_range]; simp [mono g hg], fun I hold x => ?_, fun I x => ?_⟩
      · have some' := forall2_any (P := fun e => dataDenote I e x) (Q := fun e => dataDenote I e x) pairs
          (fun _ _ keeps => keeps.1 I hold x)
        rw [dataDenote, dataDenote]
        simpa [AtLeastTwo.elements, or_assoc] using some'
      · have some' := forall2_any (P := fun e => dataDenote (extend defs I) e x) (Q := fun e => dataDenote I e x)
          pairs (fun _ _ keeps => keeps.2 I x)
        rw [dataDenote, dataDenote]
        simpa [AtLeastTwo.elements, or_assoc] using some'
  | Complement inner =>
    have : sizeOf inner < 1 + sizeOf inner := by omega
    obtain ⟨res, run, facts⟩ := unfold_range_spec defs inner fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_range, run], by simp⟩
    | some inner' =>
      obtain ⟨mono, keepsHold, keepsExtend⟩ := facts inner' rfl
      refine ⟨some (.Complement inner'), by simp [unfolding.unfold_range, run], fun r' hr => ?_⟩
      cases hr
      refine ⟨fun g hg => by rw [unfolding.unfold_range]; simp [mono g hg], fun I hold x => ?_, fun I x => ?_⟩
      · rw [dataDenote, dataDenote]
        exact not_congr (keepsHold I hold x)
      · rw [dataDenote, dataDenote]
        exact not_congr (keepsExtend I x)
  | OneOf literals =>
    have copied : unfolding.unfold_range defs (.OneOf literals) fuel = .ok (some (.OneOf literals)) := by
      cases literals
      simp [unfolding.unfold_range, Rowl.Copies.copy_literal_eq, Rowl.Copies.copy_literals_eq]
    refine ⟨some (.OneOf literals), copied, fun r' hr => ?_⟩
    cases hr
    refine ⟨fun g _ => ?_, fun I _ x => Iff.rfl, fun I x => ?_⟩
    · cases literals
      simp [unfolding.unfold_range, Rowl.Copies.copy_literal_eq, Rowl.Copies.copy_literals_eq]
    · rw [dataDenote, dataDenote]
      simp [extend]
  | Restriction dt facets =>
    cases found : definitionOf defs.val dt with
    | none =>
      have copied : ∀ g : Usize, unfolding.unfold_range defs (.Restriction dt facets) g =
          .ok (some (.Restriction dt facets)) := by
        intro g
        cases facets
        simp [unfolding.unfold_range, definition_from_eq, found, Rowl.Copies.copy_datatype_eq,
          Rowl.Copies.copy_facet_eq, Rowl.Copies.copy_facets_eq]
      refine ⟨some (.Restriction dt facets), copied fuel, fun r' hr => ?_⟩
      cases hr
      refine ⟨fun g _ => copied g, fun I _ x => Iff.rfl, fun I x => ?_⟩
      rw [dataDenote, dataDenote]
      simp [extend, found]
    | some _ =>
      exact ⟨none, by simp [unfolding.unfold_range, definition_from_eq, found], by simp⟩
termination_by (fuel.val, sizeOf r)
decreasing_by
  all_goals subst_vars
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; first | omega | assumption | (simp_wf; omega))

/-- The filler of a data number restriction holds of a value. -/
def RangeFills {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (range : Option DataRange)
    (y : Value) : Prop :=
  match range with
  | none => True
  | some r => dataDenote I r y

theorem unfold_range_filler_spec (defs : alloc.vec.Vec AnnotatedAxiom) (filler : Option DataRange) (fuel : Usize) :
    ∃ res, unfolding.unfold_range_filler defs filler fuel = .ok res ∧ ∀ f', res = some f' →
      (∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), DefinitionsHold I defs.val →
        ∀ y, RangeFills I filler y ↔ RangeFills I f' y) ∧
      (∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value) y,
        RangeFills (extend defs I) filler y ↔ RangeFills I f' y) := by
  cases filler with
  | none =>
    refine ⟨some none, by simp [unfolding.unfold_range_filler], fun f' hf => ?_⟩
    cases hf
    exact ⟨fun I _ y => Iff.rfl, fun I y => Iff.rfl⟩
  | some r =>
    obtain ⟨res, run, facts⟩ := unfold_range_spec.{u,v} defs r fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_range_filler, run], by simp⟩
    | some r' =>
      obtain ⟨_, keepsHold, keepsExtend⟩ := facts r' rfl
      refine ⟨some (some r'), by simp [unfolding.unfold_range_filler, run], fun f' hf => ?_⟩
      cases hf
      exact ⟨fun I hold y => keepsHold I hold y, fun I y => keepsExtend I y⟩

/-! ## Class expressions -/

theorem extend_relation {Object : Type u} {Value : Type v} (defs : alloc.vec.Vec AnnotatedAxiom)
    (I : Interpretation Object Value) (p : ObjectPropertyExpression) :
    objectRelation (extend defs I) p = objectRelation I p := by
  cases p <;> rfl

theorem extend_individual {Object : Type u} {Value : Type v} (defs : alloc.vec.Vec AnnotatedAxiom)
    (I : Interpretation Object Value) (a : Individual) : individual (extend defs I) a = individual I a := by
  cases a <;> rfl

/-- What the unfolding of a class expression keeps: its instances where the
    definitions hold, the instances of the extension, and its individuals. -/
structure ClassKeeps (defs : alloc.vec.Vec AnnotatedAxiom) (c c' : ClassExpression) : Prop where
  hold : ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), DefinitionsHold I defs.val →
    ∀ z, classDenote I c z ↔ classDenote I c' z
  lift : ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value) z,
    classDenote (extend defs I) c z ↔ classDenote I c' z
  names : classIndividuals c' = classIndividuals c

/-- The individuals of a filler. -/
def fillerNames : Option ClassExpression → List Individual
  | none => []
  | some c => classIndividuals c

theorem individuals_members (xs : AtLeastTwo ClassExpression) :
    classIndividuals (.ObjectIntersectionOf xs) = xs.elements.flatMap classIndividuals ∧
      classIndividuals (.ObjectUnionOf xs) = xs.elements.flatMap classIndividuals := by
  constructor <;> (rw [classIndividuals]; simp [AtLeastTwo.elements])

theorem individuals_counted (n : probes.Natural) (p : ObjectPropertyExpression) (f : Option ClassExpression) :
    classIndividuals (.ObjectMinCardinality n p f) = fillerNames f ∧
      classIndividuals (.ObjectMaxCardinality n p f) = fillerNames f ∧
      classIndividuals (.ObjectExactCardinality n p f) = fillerNames f := by
  cases f <;> simp [classIndividuals, fillerNames]

theorem members_names {xs ys : List ClassExpression} {defs : alloc.vec.Vec AnnotatedAxiom}
    (pairs : List.Forall₂ (ClassKeeps.{u,v} defs) xs ys) : ys.flatMap classIndividuals = xs.flatMap classIndividuals := by
  have := forall2_map (f := classIndividuals) (g := classIndividuals) pairs (fun _ _ keeps => keeps.names.symm)
  simp only [List.flatMap_def, this]

/-- What an unfolding of a class expression gives. -/
def ClassSpec (defs : alloc.vec.Vec AnnotatedAxiom) (c : ClassExpression) (fuel : Usize) : Prop :=
  ∃ res, unfolding.unfold_class defs c fuel = .ok res ∧ ∀ c', res = some c' → ClassKeeps.{u,v} defs c c'

theorem unfold_class_list_spec (defs : alloc.vec.Vec AnnotatedAxiom) (classes : alloc.vec.Vec ClassExpression)
    (fuel index : Usize) (out : alloc.vec.Vec ClassExpression)
    (each : ∀ c ∈ classes.val, ClassSpec.{u,v} defs c fuel) :
    ∃ res, unfolding.unfold_class_list defs classes fuel index out = .ok res ∧ ∀ result, res = some result →
      ∃ ys, result.val = out.val ++ ys ∧ List.Forall₂ (ClassKeeps.{u,v} defs) (classes.val.drop index.val) ys := by
  rw [unfolding.unfold_class_list]
  by_cases more : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    by_cases fits : out.val.length < Usize.max
    · obtain ⟨res, run, facts⟩ := each _ (List.getElem_mem more)
      cases res with
      | none =>
        exact ⟨none, by simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits,
          alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
      | some c' =>
        have keeps := facts c' rfl
        obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out c' fits)
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = index.val + 1 := by simpa using nextValue
        obtain ⟨res2, run2, facts2⟩ := unfold_class_list_spec defs classes fuel next pushed each
        refine ⟨res2, by simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits,
          alloc.vec.Vec.index_slice_index, lookup, run, push, advance, run2], fun result hres => ?_⟩
        obtain ⟨ys, value, pairs⟩ := facts2 result hres
        refine ⟨c' :: ys, ?_, ?_⟩
        · rw [value, contents]
          simp
        · rw [List.drop_eq_getElem_cons more]
          rw [nextIs] at pairs
          exact .cons keeps pairs
    · exact ⟨none, by simp [UScalar.lt_equiv, more, alloc.vec.Vec.len_val, usize_max_val, fits], by simp⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, more], fun result hres => ?_⟩
    cases hres
    refine ⟨[], by simp, ?_⟩
    rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt more)]
    exact .nil
termination_by classes.val.length - index.val
decreasing_by omega

theorem unfold_class_members_spec (defs : alloc.vec.Vec AnnotatedAxiom) (members : AtLeastTwo ClassExpression)
    (fuel : Usize) (each : ∀ c ∈ members.elements, ClassSpec.{u,v} defs c fuel) :
    ∃ res, unfolding.unfold_class_members defs members fuel = .ok res ∧ ∀ result, res = some result →
      List.Forall₂ (ClassKeeps.{u,v} defs) members.elements result.elements := by
  rw [unfolding.unfold_class_members]
  obtain ⟨r1, run1, facts1⟩ := each members.first (by simp [AtLeastTwo.elements])
  obtain ⟨r2, run2, facts2⟩ := each members.second (by simp [AtLeastTwo.elements])
  obtain ⟨r3, run3, facts3⟩ := unfold_class_list_spec.{u,v} defs members.rest fuel 0#usize
    (alloc.vec.Vec.new ClassExpression) (fun c mem => each c (by simp [AtLeastTwo.elements, mem]))
  cases r1 with
  | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
  | some first =>
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
    | some second =>
      cases r3 with
      | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
      | some rest =>
        obtain ⟨ys, value, pairs⟩ := facts3 rest rfl
        refine ⟨some ⟨first, second, rest⟩, by simp [run1, run2, run3], fun result hres => ?_⟩
        cases hres
        have restIs : rest.val = ys := by simpa using value
        simp only [AtLeastTwo.elements, restIs]
        exact .cons (facts1 first rfl) (.cons (facts2 second rfl) (by simpa using pairs))

theorem unfold_class_filler_spec (defs : alloc.vec.Vec AnnotatedAxiom) (filler : Option ClassExpression)
    (fuel : Usize) (each : ∀ c, filler = some c → ClassSpec.{u,v} defs c fuel) :
    ∃ res, unfolding.unfold_class_filler defs filler fuel = .ok res ∧ ∀ f', res = some f' →
      (∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), DefinitionsHold I defs.val →
        ∀ y, Rowl.Concepts.FillerHolds I filler y ↔ Rowl.Concepts.FillerHolds I f' y) ∧
      (∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value) y,
        Rowl.Concepts.FillerHolds (extend defs I) filler y ↔ Rowl.Concepts.FillerHolds I f' y) ∧
      fillerNames f' = fillerNames filler := by
  cases filler with
  | none =>
    refine ⟨some none, by simp [unfolding.unfold_class_filler], fun f' hf => ?_⟩
    cases hf
    exact ⟨fun I _ y => Iff.rfl, fun I y => Iff.rfl, rfl⟩
  | some c =>
    obtain ⟨res, run, facts⟩ := each c rfl
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class_filler, run], by simp⟩
    | some c' =>
      obtain ⟨keepsHold, keepsExtend, keepsNames⟩ := facts c' rfl
      refine ⟨some (some c'), by simp [unfolding.unfold_class_filler, run], fun f' hf => ?_⟩
      cases hf
      exact ⟨fun I hold y => keepsHold I hold y, fun I y => keepsExtend I y, by simp [fillerNames, keepsNames]⟩

private theorem atLeast_congr {α : Type u} {n : Nat} {P Q : α → Prop} (h : ∀ y, P y ↔ Q y) :
    AtLeast n P ↔ AtLeast n Q := by
  have : P = Q := funext fun y => propext (h y)
  rw [this]

private theorem atMost_congr {α : Type u} {n : Nat} {P Q : α → Prop} (h : ∀ y, P y ↔ Q y) :
    AtMost n P ↔ AtMost n Q := by
  have : P = Q := funext fun y => propext (h y)
  rw [this]

private theorem exactly_congr {α : Type u} {n : Nat} {P Q : α → Prop} (h : ∀ y, P y ↔ Q y) :
    Exactly n P ↔ Exactly n Q := by
  have : P = Q := funext fun y => propext (h y)
  rw [this]

theorem unfold_class_spec (defs : alloc.vec.Vec AnnotatedAxiom) (c : ClassExpression) (fuel : Usize) :
    ClassSpec.{u,v} defs c fuel := by
  cases c with
  | Class named =>
    refine ⟨some (.Class named), by simp [unfolding.unfold_class, Rowl.Copies.copy_class_name_eq], fun c' hc => ?_⟩
    cases hc
    exact ⟨fun I _ z => Iff.rfl, fun I z => by simp only [classDenote, extend], rfl⟩
  | ObjectIntersectionOf members =>
    obtain ⟨res, run, facts⟩ := unfold_class_members_spec.{u,v} defs members fuel (fun e mem => by
      have := members_bound members e mem
      exact unfold_class_spec defs e fuel)
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class, run], by simp⟩
    | some ms =>
      have pairs := facts ms rfl
      refine ⟨some (.ObjectIntersectionOf ms), by simp [unfolding.unfold_class, run], fun c' hc => ?_⟩
      cases hc
      refine ⟨fun I hold z => ?_, fun I z => ?_, ?_⟩
      · have every := forall2_all (P := fun e => classDenote I e z) (Q := fun e => classDenote I e z) pairs
          (fun _ _ keeps => keeps.1 I hold z)
        rw [classDenote, classDenote]
        simpa [AtLeastTwo.elements] using every
      · have every := forall2_all (P := fun e => classDenote (extend defs I) e z) (Q := fun e => classDenote I e z)
          pairs (fun _ _ keeps => keeps.2 I z)
        rw [classDenote, classDenote]
        simpa [AtLeastTwo.elements] using every
      · rw [(individuals_members ms).1, (individuals_members members).1]
        exact members_names pairs
  | ObjectUnionOf members =>
    obtain ⟨res, run, facts⟩ := unfold_class_members_spec.{u,v} defs members fuel (fun e mem => by
      have := members_bound members e mem
      exact unfold_class_spec defs e fuel)
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class, run], by simp⟩
    | some ms =>
      have pairs := facts ms rfl
      refine ⟨some (.ObjectUnionOf ms), by simp [unfolding.unfold_class, run], fun c' hc => ?_⟩
      cases hc
      refine ⟨fun I hold z => ?_, fun I z => ?_, ?_⟩
      · have some' := forall2_any (P := fun e => classDenote I e z) (Q := fun e => classDenote I e z) pairs
          (fun _ _ keeps => keeps.1 I hold z)
        rw [classDenote, classDenote]
        simpa [AtLeastTwo.elements, or_assoc] using some'
      · have some' := forall2_any (P := fun e => classDenote (extend defs I) e z) (Q := fun e => classDenote I e z)
          pairs (fun _ _ keeps => keeps.2 I z)
        rw [classDenote, classDenote]
        simpa [AtLeastTwo.elements, or_assoc] using some'
      · rw [(individuals_members ms).2, (individuals_members members).2]
        exact members_names pairs
  | ObjectComplementOf inner =>
    obtain ⟨res, run, facts⟩ := unfold_class_spec defs inner fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class, run], by simp⟩
    | some inner' =>
      obtain ⟨keepsHold, keepsExtend, keepsNames⟩ := facts inner' rfl
      refine ⟨some (.ObjectComplementOf inner'), by simp [unfolding.unfold_class, run], fun c' hc => ?_⟩
      cases hc
      refine ⟨fun I hold z => ?_, fun I z => ?_, ?_⟩
      · rw [classDenote, classDenote]
        exact not_congr (keepsHold I hold z)
      · rw [classDenote, classDenote]
        exact not_congr (keepsExtend I z)
      · rw [classIndividuals, classIndividuals]
        exact keepsNames
  | ObjectOneOf individuals =>
    refine ⟨some (.ObjectOneOf individuals), by
      cases individuals
      simp [unfolding.unfold_class, Rowl.Concepts.copy_individual_identity, Rowl.Copies.copy_individuals_eq],
      fun c' hc => ?_⟩
    cases hc
    refine ⟨fun I _ z => Iff.rfl, fun I z => ?_, rfl⟩
    rw [classDenote, classDenote]
    simp only [extend_individual]
  | ObjectSomeValuesFrom role filler =>
    obtain ⟨res, run, facts⟩ := unfold_class_spec defs filler fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class, run], by simp⟩
    | some f' =>
      obtain ⟨keepsHold, keepsExtend, keepsNames⟩ := facts f' rfl
      refine ⟨some (.ObjectSomeValuesFrom role f'), by simp [unfolding.unfold_class, run,
        Rowl.Concepts.copy_role_identity], fun c' hc => ?_⟩
      cases hc
      refine ⟨fun I hold z => ?_, fun I z => ?_, ?_⟩
      · rw [classDenote, classDenote]
        exact exists_congr fun y => and_congr Iff.rfl (keepsHold I hold y)
      · rw [classDenote, classDenote, extend_relation]
        exact exists_congr fun y => and_congr Iff.rfl (keepsExtend I y)
      · rw [classIndividuals, classIndividuals]
        exact keepsNames
  | ObjectAllValuesFrom role filler =>
    obtain ⟨res, run, facts⟩ := unfold_class_spec defs filler fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class, run], by simp⟩
    | some f' =>
      obtain ⟨keepsHold, keepsExtend, keepsNames⟩ := facts f' rfl
      refine ⟨some (.ObjectAllValuesFrom role f'), by simp [unfolding.unfold_class, run,
        Rowl.Concepts.copy_role_identity], fun c' hc => ?_⟩
      cases hc
      refine ⟨fun I hold z => ?_, fun I z => ?_, ?_⟩
      · rw [classDenote, classDenote]
        exact forall_congr' fun y => imp_congr Iff.rfl (keepsHold I hold y)
      · rw [classDenote, classDenote, extend_relation]
        exact forall_congr' fun y => imp_congr Iff.rfl (keepsExtend I y)
      · rw [classIndividuals, classIndividuals]
        exact keepsNames
  | ObjectHasValue role a =>
    refine ⟨some (.ObjectHasValue role a), by simp [unfolding.unfold_class, Rowl.Concepts.copy_role_identity,
      Rowl.Concepts.copy_individual_identity], fun c' hc => ?_⟩
    cases hc
    refine ⟨fun I _ z => Iff.rfl, fun I z => ?_, rfl⟩
    rw [classDenote, classDenote, extend_relation, extend_individual]
  | ObjectHasSelf role =>
    refine ⟨some (.ObjectHasSelf role), by simp [unfolding.unfold_class, Rowl.Concepts.copy_role_identity],
      fun c' hc => ?_⟩
    cases hc
    refine ⟨fun I _ z => Iff.rfl, fun I z => ?_, rfl⟩
    rw [classDenote, classDenote, extend_relation]
  | ObjectMinCardinality count role filler =>
    obtain ⟨res, run, facts⟩ := unfold_class_filler_spec.{u,v} defs filler fuel (fun e same => by
      have : sizeOf e < sizeOf filler := by rw [same]; simp +arith
      exact unfold_class_spec defs e fuel)
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class, run], by simp⟩
    | some f' =>
      obtain ⟨keepsHold, keepsExtend, keepsNames⟩ := facts f' rfl
      refine ⟨some (.ObjectMinCardinality count role f'), by simp [unfolding.unfold_class, run, Rowl.Copies.copy_natural_eq,
        Rowl.Concepts.copy_role_identity], fun c' hc => ?_⟩
      cases hc
      refine ⟨fun I hold z => ?_, fun I z => ?_, ?_⟩
      · rw [classDenote, classDenote]
        exact atLeast_congr fun y => and_congr Iff.rfl (keepsHold I hold y)
      · rw [classDenote, classDenote, extend_relation]
        exact atLeast_congr fun y => and_congr Iff.rfl (keepsExtend I y)
      · rw [(individuals_counted count role f').1, (individuals_counted count role filler).1]
        exact keepsNames
  | ObjectMaxCardinality count role filler =>
    obtain ⟨res, run, facts⟩ := unfold_class_filler_spec.{u,v} defs filler fuel (fun e same => by
      have : sizeOf e < sizeOf filler := by rw [same]; simp +arith
      exact unfold_class_spec defs e fuel)
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class, run], by simp⟩
    | some f' =>
      obtain ⟨keepsHold, keepsExtend, keepsNames⟩ := facts f' rfl
      refine ⟨some (.ObjectMaxCardinality count role f'), by simp [unfolding.unfold_class, run, Rowl.Copies.copy_natural_eq,
        Rowl.Concepts.copy_role_identity], fun c' hc => ?_⟩
      cases hc
      refine ⟨fun I hold z => ?_, fun I z => ?_, ?_⟩
      · rw [classDenote, classDenote]
        exact atMost_congr fun y => and_congr Iff.rfl (keepsHold I hold y)
      · rw [classDenote, classDenote, extend_relation]
        exact atMost_congr fun y => and_congr Iff.rfl (keepsExtend I y)
      · rw [(individuals_counted count role f').2.1, (individuals_counted count role filler).2.1]
        exact keepsNames
  | ObjectExactCardinality count role filler =>
    obtain ⟨res, run, facts⟩ := unfold_class_filler_spec.{u,v} defs filler fuel (fun e same => by
      have : sizeOf e < sizeOf filler := by rw [same]; simp +arith
      exact unfold_class_spec defs e fuel)
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class, run], by simp⟩
    | some f' =>
      obtain ⟨keepsHold, keepsExtend, keepsNames⟩ := facts f' rfl
      refine ⟨some (.ObjectExactCardinality count role f'), by simp [unfolding.unfold_class, run, Rowl.Copies.copy_natural_eq,
        Rowl.Concepts.copy_role_identity], fun c' hc => ?_⟩
      cases hc
      refine ⟨fun I hold z => ?_, fun I z => ?_, ?_⟩
      · rw [classDenote, classDenote]
        exact exactly_congr fun y => and_congr Iff.rfl (keepsHold I hold y)
      · rw [classDenote, classDenote, extend_relation]
        exact exactly_congr fun y => and_congr Iff.rfl (keepsExtend I y)
      · rw [(individuals_counted count role f').2.2, (individuals_counted count role filler).2.2]
        exact keepsNames
  | DataSomeValuesFrom property range =>
    obtain ⟨res, run, facts⟩ := unfold_range_spec.{u,v} defs range fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class, run], by simp⟩
    | some r' =>
      obtain ⟨_, keepsHold, keepsExtend⟩ := facts r' rfl
      refine ⟨some (.DataSomeValuesFrom property r'), by simp [unfolding.unfold_class, run,
        Rowl.Copies.copy_data_property_eq], fun c' hc => ?_⟩
      cases hc
      refine ⟨fun I hold z => ?_, fun I z => ?_, ?_⟩
      · rw [classDenote, classDenote]
        exact exists_congr fun y => and_congr Iff.rfl (keepsHold I hold y)
      · rw [classDenote, classDenote]
        exact exists_congr fun y => and_congr Iff.rfl (keepsExtend I y)
      · simp [classIndividuals]
  | DataAllValuesFrom property range =>
    obtain ⟨res, run, facts⟩ := unfold_range_spec.{u,v} defs range fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class, run], by simp⟩
    | some r' =>
      obtain ⟨_, keepsHold, keepsExtend⟩ := facts r' rfl
      refine ⟨some (.DataAllValuesFrom property r'), by simp [unfolding.unfold_class, run,
        Rowl.Copies.copy_data_property_eq], fun c' hc => ?_⟩
      cases hc
      refine ⟨fun I hold z => ?_, fun I z => ?_, ?_⟩
      · rw [classDenote, classDenote]
        exact forall_congr' fun y => imp_congr Iff.rfl (keepsHold I hold y)
      · rw [classDenote, classDenote]
        exact forall_congr' fun y => imp_congr Iff.rfl (keepsExtend I y)
      · simp [classIndividuals]
  | DataHasValue property literal =>
    refine ⟨some (.DataHasValue property literal), by simp [unfolding.unfold_class,
      Rowl.Copies.copy_data_property_eq, Rowl.Copies.copy_literal_eq], fun c' hc => ?_⟩
    cases hc
    refine ⟨fun I _ z => Iff.rfl, fun I z => ?_, rfl⟩
    rw [classDenote, classDenote]
    exact Iff.rfl
  | DataMinCardinality count property filler =>
    obtain ⟨res, run, facts⟩ := unfold_range_filler_spec.{u,v} defs filler fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class, run], by simp⟩
    | some f' =>
      obtain ⟨keepsHold, keepsExtend⟩ := facts f' rfl
      refine ⟨some (.DataMinCardinality count property f'), by simp [unfolding.unfold_class, run, Rowl.Copies.copy_natural_eq,
        Rowl.Copies.copy_data_property_eq], fun c' hc => ?_⟩
      cases hc
      refine ⟨fun I hold z => ?_, fun I z => ?_, ?_⟩
      · rw [classDenote, classDenote]
        exact atLeast_congr fun y => and_congr Iff.rfl (keepsHold I hold y)
      · rw [classDenote, classDenote]
        exact atLeast_congr fun y => and_congr Iff.rfl (keepsExtend I y)
      · simp [classIndividuals]
  | DataMaxCardinality count property filler =>
    obtain ⟨res, run, facts⟩ := unfold_range_filler_spec.{u,v} defs filler fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class, run], by simp⟩
    | some f' =>
      obtain ⟨keepsHold, keepsExtend⟩ := facts f' rfl
      refine ⟨some (.DataMaxCardinality count property f'), by simp [unfolding.unfold_class, run, Rowl.Copies.copy_natural_eq,
        Rowl.Copies.copy_data_property_eq], fun c' hc => ?_⟩
      cases hc
      refine ⟨fun I hold z => ?_, fun I z => ?_, ?_⟩
      · rw [classDenote, classDenote]
        exact atMost_congr fun y => and_congr Iff.rfl (keepsHold I hold y)
      · rw [classDenote, classDenote]
        exact atMost_congr fun y => and_congr Iff.rfl (keepsExtend I y)
      · simp [classIndividuals]
  | DataExactCardinality count property filler =>
    obtain ⟨res, run, facts⟩ := unfold_range_filler_spec.{u,v} defs filler fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_class, run], by simp⟩
    | some f' =>
      obtain ⟨keepsHold, keepsExtend⟩ := facts f' rfl
      refine ⟨some (.DataExactCardinality count property f'), by simp [unfolding.unfold_class, run, Rowl.Copies.copy_natural_eq,
        Rowl.Copies.copy_data_property_eq], fun c' hc => ?_⟩
      cases hc
      refine ⟨fun I hold z => ?_, fun I z => ?_, ?_⟩
      · rw [classDenote, classDenote]
        exact exactly_congr fun y => and_congr Iff.rfl (keepsHold I hold y)
      · rw [classDenote, classDenote]
        exact exactly_congr fun y => and_congr Iff.rfl (keepsExtend I y)
      · simp [classIndividuals]
termination_by sizeOf c
decreasing_by all_goals (subst_vars; first | omega | (simp_wf <;> omega))

/-! ## Axioms -/

section Extension
variable {Object : Type u} {Value : Type v} (defs : alloc.vec.Vec AnnotatedAxiom) (I : Interpretation Object Value)

@[simp] theorem extend_classes : (extend defs I).classes = I.classes := rfl
@[simp] theorem extend_object_properties : (extend defs I).objectProperties = I.objectProperties := rfl
@[simp] theorem extend_data_properties : (extend defs I).dataProperties = I.dataProperties := rfl
@[simp] theorem extend_named_individuals : (extend defs I).namedIndividuals = I.namedIndividuals := rfl
@[simp] theorem extend_anonymous_individuals : (extend defs I).anonymousIndividuals = I.anonymousIndividuals := rfl
@[simp] theorem extend_literals : (extend defs I).literals = I.literals := rfl
@[simp] theorem extend_facets : (extend defs I).facets = I.facets := rfl
@[simp] theorem extend_named : (extend defs I).named = I.named := rfl

theorem extend_relation_fun : objectRelation (extend defs I) = objectRelation I := funext (extend_relation defs I)

theorem extend_individual_fun : individual (extend defs I) = individual I := funext (extend_individual defs I)

theorem extend_chain (ps : List ObjectPropertyExpression) : chainRelation (extend defs I) ps = chainRelation I ps := by
  induction ps with
  | nil => funext x y; simp [chainRelation]
  | cons p rest ih => funext x y; simp [chainRelation, ih, extend_relation]

theorem extend_sub (sub : SubObjectPropertyExpression) : subRelation (extend defs I) sub = subRelation I sub := by
  cases sub with
  | Single p => simp [subRelation, extend_relation_fun]
  | Chain ps => simp [subRelation, extend_chain]

end Extension

theorem allEqual_map {α : Type} {γ : Sort _} (l : List α) (f : α → γ) :
    allEqual l f ↔ ∀ p ∈ l.map f, ∀ q ∈ l.map f, p = q := by
  simp [allEqual]

theorem pairwiseDisjoint_map {α : Type} {γ : Type _} (l : List α) (f : α → γ → Prop) :
    pairwiseDisjoint l f ↔ (l.map f).Pairwise (fun p q => ∀ x, ¬ (p x ∧ q x)) := by
  simp [pairwiseDisjoint, List.pairwise_map]

/-- The instances of the members, as the members unfold. -/
theorem members_denote {Object : Type u} {Value : Type v} {defs : alloc.vec.Vec AnnotatedAxiom}
    {xs ys : List ClassExpression} (pairs : List.Forall₂ (ClassKeeps.{u,v} defs) xs ys) :
    (∀ (I : Interpretation Object Value), DefinitionsHold I defs.val → xs.map (classDenote I) = ys.map (classDenote I)) ∧
    (∀ (I : Interpretation Object Value), xs.map (classDenote (extend defs I)) = ys.map (classDenote I)) :=
  ⟨fun I hold => forall2_map pairs (fun _ _ keeps => funext fun z => propext (keeps.1 I hold z)),
    fun I => forall2_map pairs (fun _ _ keeps => funext fun z => propext (keeps.2 I z))⟩

/-- What the unfolding of an axiom keeps: its truth where the definitions
    hold, the truth of the extension, its individuals and its keys. -/
structure AxiomKeeps (defs : alloc.vec.Vec AnnotatedAxiom) (a a' : Axiom) : Prop where
  hold : ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), DefinitionsHold I defs.val →
    (satisfies I a ↔ satisfies I a')
  lift : ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value),
    satisfies (extend defs I) a ↔ satisfies I a'
  names : axiomIndividuals a' = axiomIndividuals a
  keys : keyIndividuals a' = keyIndividuals a
  key : IsKey a' ↔ IsKey a
  undefined : ∀ dt r, a' ≠ .DatatypeDefinition dt r

/-- An axiom that the unfolding drops: a datatype definition whose data range
    unfolds, or an annotation axiom, which holds everywhere; it names no
    individual and is no key. -/
def Dropped (defs : alloc.vec.Vec AnnotatedAxiom) (a : Axiom) : Prop :=
  ((∃ dt r r', a = .DatatypeDefinition dt r ∧
    unfolding.unfold_range defs r (alloc.vec.Vec.len defs) = .ok (some r')) ∨
  ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), satisfies I a) ∧
  axiomIndividuals a = [] ∧ keyIndividuals a = [] ∧ ¬ IsKey a

theorem copy_entity_eq (e : Entity) : unfolding.copy_entity e = .ok e := by
  cases e with
  | Class c => simp [unfolding.copy_entity, Rowl.Copies.copy_class_name_eq]
  | Datatype dt => simp [unfolding.copy_entity, Rowl.Copies.copy_datatype_eq]
  | ObjectProperty p => cases p; simp [unfolding.copy_entity, Rowl.Nnf.copy_iri_identity]
  | DataProperty p => simp [unfolding.copy_entity, Rowl.Copies.copy_data_property_eq]
  | AnnotationProperty p => cases p; simp [unfolding.copy_entity, Rowl.Nnf.copy_iri_identity]
  | NamedIndividual a => cases a; simp [unfolding.copy_entity, Rowl.Nnf.copy_iri_identity]

/-- An axiom without class expressions and data ranges is kept as it is. -/
private theorem keeps_self (defs : alloc.vec.Vec AnnotatedAxiom) (a : Axiom)
    (same : ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value),
      satisfies (extend defs I) a ↔ satisfies I a) (undefined : ∀ dt r, a ≠ .DatatypeDefinition dt r) :
    AxiomKeeps.{u,v} defs a a :=
  ⟨fun _ _ => Iff.rfl, same, rfl, rfl, Iff.rfl, undefined⟩

private theorem copied (defs : alloc.vec.Vec AnnotatedAxiom) (a : Axiom) (fuel : Usize)
    (run : unfolding.unfold_axiom defs a fuel = .ok (some (some a)))
    (same : ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value),
      satisfies (extend defs I) a ↔ satisfies I a) (undefined : ∀ dt r, a ≠ .DatatypeDefinition dt r) :
    ∃ res, unfolding.unfold_axiom defs a fuel = .ok res ∧ ∀ o, res = some o →
      (o = none → Dropped.{u,v} defs a) ∧ (∀ a', o = some a' → AxiomKeeps.{u,v} defs a a') :=
  ⟨some (some a), run, fun o ho => by
    cases ho
    exact ⟨by simp, fun a' h => by cases h; exact keeps_self defs a same undefined⟩⟩

private theorem dropped_axiom (defs : alloc.vec.Vec AnnotatedAxiom) (a : Axiom) (fuel : Usize)
    (run : unfolding.unfold_axiom defs a fuel = .ok (some none))
    (holds : ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value), satisfies I a)
    (names : axiomIndividuals a = []) (keys : keyIndividuals a = []) (key : ¬ IsKey a) :
    ∃ res, unfolding.unfold_axiom defs a fuel = .ok res ∧ ∀ o, res = some o →
      (o = none → Dropped.{u,v} defs a) ∧ (∀ a', o = some a' → AxiomKeeps.{u,v} defs a a') :=
  ⟨some none, run, fun o ho => by
    cases ho
    exact ⟨fun _ => ⟨.inr holds, names, keys, key⟩, by simp⟩⟩

private theorem exists_map {α : Type} {β : Type _} (l : List α) (f : α → β → Prop) (x : β) :
    (∃ e ∈ l, f e x) ↔ ∃ p ∈ l.map f, p x := by
  simp

/-- The unfolding of an axiom: a datatype definition whose data range unfolds
    and an annotation axiom go, and every other axiom keeps its truth. -/
theorem unfold_axiom_spec (defs : alloc.vec.Vec AnnotatedAxiom) (a : Axiom) (fuel : Usize)
    (hfuel : fuel = alloc.vec.Vec.len defs) :
    ∃ res, unfolding.unfold_axiom defs a fuel = .ok res ∧ ∀ o, res = some o →
      (o = none → Dropped.{u,v} defs a) ∧ (∀ a', o = some a' → AxiomKeeps.{u,v} defs a a') := by
  cases a with
  | Declaration e =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, copy_entity_eq]) (fun I => by simp [satisfies])
      (fun _ _ h => by cases h)
  | SubClassOf sub sup =>
    obtain ⟨r1, run1, f1⟩ := unfold_class_spec.{u,v} defs sub fuel
    obtain ⟨r2, run2, f2⟩ := unfold_class_spec.{u,v} defs sup fuel
    cases r1 with
    | none => exact ⟨none, by simp [unfolding.unfold_axiom, unfolding.unfold_pair, run1, run2], by simp⟩
    | some sub' =>
      cases r2 with
      | none => exact ⟨none, by simp [unfolding.unfold_axiom, unfolding.unfold_pair, run1, run2], by simp⟩
      | some sup' =>
        obtain ⟨h1, e1, n1⟩ := f1 sub' rfl
        obtain ⟨h2, e2, n2⟩ := f2 sup' rfl
        refine ⟨some (some (.SubClassOf sub' sup')), by simp [unfolding.unfold_axiom, unfolding.unfold_pair, run1,
          run2], fun o ho => ?_⟩
        cases ho
        refine ⟨by simp, fun a' h => ?_⟩
        cases h
        refine ⟨fun I hold => ?_, fun I => ?_, by simp [axiomIndividuals, n1, n2], by simp [keyIndividuals],
          by simp [IsKey], fun _ _ h => by cases h⟩
        · simp only [satisfies]
          exact forall_congr' fun x => imp_congr (h1 I hold x) (h2 I hold x)
        · simp only [satisfies]
          exact forall_congr' fun x => imp_congr (e1 I x) (e2 I x)
  | EquivalentClasses members =>
    obtain ⟨res, run, facts⟩ := unfold_class_members_spec.{u,v} defs members fuel
      (fun c _ => unfold_class_spec defs c fuel)
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_axiom, run], by simp⟩
    | some ms =>
      refine ⟨some (some (.EquivalentClasses ms)), by simp [unfolding.unfold_axiom, run], fun o ho => ?_⟩
      cases ho
      refine ⟨by simp, fun a' h => ?_⟩
      cases h
      have pairs := facts ms rfl
      refine ⟨fun I hold => ?_, fun I => ?_, by simp only [axiomIndividuals]; exact members_names pairs,
        by simp [keyIndividuals], by simp [IsKey], fun _ _ h => by cases h⟩
      · simp only [satisfies, allEqual_map, (members_denote pairs).1 I hold]
      · simp only [satisfies, allEqual_map, (members_denote pairs).2 I]
  | DisjointClasses members =>
    obtain ⟨res, run, facts⟩ := unfold_class_members_spec.{u,v} defs members fuel
      (fun c _ => unfold_class_spec defs c fuel)
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_axiom, run], by simp⟩
    | some ms =>
      refine ⟨some (some (.DisjointClasses ms)), by simp [unfolding.unfold_axiom, run], fun o ho => ?_⟩
      cases ho
      refine ⟨by simp, fun a' h => ?_⟩
      cases h
      have pairs := facts ms rfl
      refine ⟨fun I hold => ?_, fun I => ?_, by simp only [axiomIndividuals]; exact members_names pairs,
        by simp [keyIndividuals], by simp [IsKey], fun _ _ h => by cases h⟩
      · simp only [satisfies, pairwiseDisjoint_map, (members_denote pairs).1 I hold]
      · simp only [satisfies, pairwiseDisjoint_map, (members_denote pairs).2 I]
  | DisjointUnion c members =>
    obtain ⟨res, run, facts⟩ := unfold_class_members_spec.{u,v} defs members fuel
      (fun c _ => unfold_class_spec defs c fuel)
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_axiom, run], by simp⟩
    | some ms =>
      refine ⟨some (some (.DisjointUnion c ms)), by simp [unfolding.unfold_axiom, run,
        Rowl.Copies.copy_class_name_eq], fun o ho => ?_⟩
      cases ho
      refine ⟨by simp, fun a' h => ?_⟩
      cases h
      have pairs := facts ms rfl
      refine ⟨fun I hold => ?_, fun I => ?_, by simp only [axiomIndividuals]; exact members_names pairs,
        by simp [keyIndividuals], by simp [IsKey], fun _ _ h => by cases h⟩
      · simp only [satisfies, pairwiseDisjoint_map, exists_map, (members_denote pairs).1 I hold]
      · simp only [satisfies, pairwiseDisjoint_map, exists_map, (members_denote pairs).2 I, extend_classes]
  | SubObjectPropertyOf sub sup =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Copies.copy_sub_role_eq, Rowl.Concepts.copy_role_identity])
      (fun I => by simp [satisfies, extend_sub, extend_relation_fun])
      (fun _ _ h => by cases h)
  | EquivalentObjectProperties roles =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Copies.copy_role_members_eq])
      (fun I => by simp [satisfies, extend_relation_fun])
      (fun _ _ h => by cases h)
  | DisjointObjectProperties roles =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Copies.copy_role_members_eq])
      (fun I => by simp [satisfies, extend_relation_fun])
      (fun _ _ h => by cases h)
  | InverseObjectProperties p q =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Concepts.copy_role_identity])
      (fun I => by simp [satisfies, extend_relation_fun])
      (fun _ _ h => by cases h)
  | ObjectPropertyDomain role e =>
    obtain ⟨res, run, facts⟩ := unfold_class_spec.{u,v} defs e fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_axiom, run], by simp⟩
    | some e' =>
      obtain ⟨keepsHold, keepsExtend, keepsNames⟩ := facts e' rfl
      refine ⟨some (some (.ObjectPropertyDomain role e')), by simp [unfolding.unfold_axiom, run, Rowl.Concepts.copy_role_identity],
        fun o ho => ?_⟩
      cases ho
      refine ⟨by simp, fun a' h => ?_⟩
      cases h
      refine ⟨fun I hold => ?_, fun I => ?_, by simp only [axiomIndividuals]; exact keepsNames, by simp [keyIndividuals], by simp [IsKey],
        fun _ _ h => by cases h⟩
      · simp only [satisfies]
        exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl (keepsHold I hold x)
      · simp only [satisfies, extend_relation_fun]
        exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl (keepsExtend I x)
  | ObjectPropertyRange role e =>
    obtain ⟨res, run, facts⟩ := unfold_class_spec.{u,v} defs e fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_axiom, run], by simp⟩
    | some e' =>
      obtain ⟨keepsHold, keepsExtend, keepsNames⟩ := facts e' rfl
      refine ⟨some (some (.ObjectPropertyRange role e')), by simp [unfolding.unfold_axiom, run, Rowl.Concepts.copy_role_identity],
        fun o ho => ?_⟩
      cases ho
      refine ⟨by simp, fun a' h => ?_⟩
      cases h
      refine ⟨fun I hold => ?_, fun I => ?_, by simp only [axiomIndividuals]; exact keepsNames, by simp [keyIndividuals], by simp [IsKey],
        fun _ _ h => by cases h⟩
      · simp only [satisfies]
        exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl (keepsHold I hold y)
      · simp only [satisfies, extend_relation_fun]
        exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl (keepsExtend I y)
  | FunctionalObjectProperty p =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Concepts.copy_role_identity])
      (fun I => by simp [satisfies, extend_relation_fun])
      (fun _ _ h => by cases h)
  | InverseFunctionalObjectProperty p =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Concepts.copy_role_identity])
      (fun I => by simp [satisfies, extend_relation_fun])
      (fun _ _ h => by cases h)
  | ReflexiveObjectProperty p =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Concepts.copy_role_identity])
      (fun I => by simp [satisfies, extend_relation_fun])
      (fun _ _ h => by cases h)
  | IrreflexiveObjectProperty p =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Concepts.copy_role_identity])
      (fun I => by simp [satisfies, extend_relation_fun])
      (fun _ _ h => by cases h)
  | SymmetricObjectProperty p =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Concepts.copy_role_identity])
      (fun I => by simp [satisfies, extend_relation_fun])
      (fun _ _ h => by cases h)
  | AsymmetricObjectProperty p =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Concepts.copy_role_identity])
      (fun I => by simp [satisfies, extend_relation_fun])
      (fun _ _ h => by cases h)
  | TransitiveObjectProperty p =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Concepts.copy_role_identity])
      (fun I => by simp [satisfies, extend_relation_fun])
      (fun _ _ h => by cases h)
  | SubDataPropertyOf p q =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Copies.copy_data_property_eq])
      (fun I => by simp [satisfies])
      (fun _ _ h => by cases h)
  | EquivalentDataProperties ps =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Copies.copy_data_members_eq])
      (fun I => by simp [satisfies])
      (fun _ _ h => by cases h)
  | DisjointDataProperties ps =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Copies.copy_data_members_eq])
      (fun I => by simp [satisfies])
      (fun _ _ h => by cases h)
  | DataPropertyDomain p e =>
    obtain ⟨res, run, facts⟩ := unfold_class_spec.{u,v} defs e fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_axiom, run], by simp⟩
    | some e' =>
      obtain ⟨keepsHold, keepsExtend, keepsNames⟩ := facts e' rfl
      refine ⟨some (some (.DataPropertyDomain p e')), by simp [unfolding.unfold_axiom, run,
        Rowl.Copies.copy_data_property_eq], fun o ho => ?_⟩
      cases ho
      refine ⟨by simp, fun a' h => ?_⟩
      cases h
      refine ⟨fun I hold => ?_, fun I => ?_, by simp only [axiomIndividuals]; exact keepsNames, by simp [keyIndividuals], by simp [IsKey],
        fun _ _ h => by cases h⟩
      · simp only [satisfies]
        exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl (keepsHold I hold x)
      · simp only [satisfies, extend_data_properties]
        exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl (keepsExtend I x)
  | DataPropertyRange p r =>
    obtain ⟨res, run, facts⟩ := unfold_range_spec.{u,v} defs r fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_axiom, run], by simp⟩
    | some r' =>
      obtain ⟨_, keepsHold, keepsExtend⟩ := facts r' rfl
      refine ⟨some (some (.DataPropertyRange p r')), by simp [unfolding.unfold_axiom, run,
        Rowl.Copies.copy_data_property_eq], fun o ho => ?_⟩
      cases ho
      refine ⟨by simp, fun a' h => ?_⟩
      cases h
      refine ⟨fun I hold => ?_, fun I => ?_, by simp [axiomIndividuals], by simp [keyIndividuals], by simp [IsKey],
        fun _ _ h => by cases h⟩
      · simp only [satisfies]
        exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl (keepsHold I hold y)
      · simp only [satisfies, extend_data_properties]
        exact forall_congr' fun x => forall_congr' fun y => imp_congr Iff.rfl (keepsExtend I y)
  | FunctionalDataProperty p =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Copies.copy_data_property_eq])
      (fun I => by simp [satisfies])
      (fun _ _ h => by cases h)
  | DatatypeDefinition dt r =>
    obtain ⟨res, run, facts⟩ := unfold_range_spec.{u,v} defs r fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_axiom, run], by simp⟩
    | some r' =>
      refine ⟨some none, by simp [unfolding.unfold_axiom, run], fun o ho => ?_⟩
      cases ho
      exact ⟨fun _ => ⟨.inl ⟨dt, r, r', rfl, by rw [← hfuel]; exact run⟩, by simp [axiomIndividuals],
        by simp [keyIndividuals], by simp [IsKey]⟩, by simp⟩
  | HasKey e ops dps =>
    obtain ⟨res, run, facts⟩ := unfold_class_spec.{u,v} defs e fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_axiom, run], by simp⟩
    | some e' =>
      obtain ⟨keepsHold, keepsExtend, keepsNames⟩ := facts e' rfl
      refine ⟨some (some (.HasKey e' ops dps)), by simp [unfolding.unfold_axiom, run,
        Rowl.Copies.copy_roles_eq, Rowl.Copies.copy_data_list_eq], fun o ho => ?_⟩
      cases ho
      refine ⟨by simp, fun a' h => ?_⟩
      cases h
      refine ⟨fun I hold => ?_, fun I => ?_, by simp [axiomIndividuals], by simp only [keyIndividuals]; exact keepsNames, by simp [IsKey],
        fun _ _ h => by cases h⟩
      · simp only [satisfies, keepsHold I hold]
      · simp only [satisfies, keepsExtend I, extend_named, extend_relation_fun, extend_data_properties]
  | SameIndividual xs =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Copies.copy_individual_members_eq])
      (fun I => by simp [satisfies, extend_individual_fun])
      (fun _ _ h => by cases h)
  | DifferentIndividuals xs =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Copies.copy_individual_members_eq])
      (fun I => by simp [satisfies, extend_individual_fun])
      (fun _ _ h => by cases h)
  | ClassAssertion e a =>
    obtain ⟨res, run, facts⟩ := unfold_class_spec.{u,v} defs e fuel
    cases res with
    | none => exact ⟨none, by simp [unfolding.unfold_axiom, run], by simp⟩
    | some e' =>
      obtain ⟨keepsHold, keepsExtend, keepsNames⟩ := facts e' rfl
      refine ⟨some (some (.ClassAssertion e' a)), by simp [unfolding.unfold_axiom, run,
        Rowl.Concepts.copy_individual_identity], fun o ho => ?_⟩
      cases ho
      refine ⟨by simp, fun a' h => ?_⟩
      cases h
      refine ⟨fun I hold => ?_, fun I => ?_, by simp only [axiomIndividuals, keepsNames], by simp [keyIndividuals], by simp [IsKey],
        fun _ _ h => by cases h⟩
      · simp only [satisfies]
        exact keepsHold I hold _
      · simp only [satisfies, extend_individual_fun]
        exact keepsExtend I _
  | ObjectPropertyAssertion p a b =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Concepts.copy_role_identity, Rowl.Concepts.copy_individual_identity])
      (fun I => by simp [satisfies, extend_relation_fun, extend_individual_fun])
      (fun _ _ h => by cases h)
  | NegativeObjectPropertyAssertion p a b =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Concepts.copy_role_identity, Rowl.Concepts.copy_individual_identity])
      (fun I => by simp [satisfies, extend_relation_fun, extend_individual_fun])
      (fun _ _ h => by cases h)
  | DataPropertyAssertion p a lt =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Copies.copy_data_property_eq, Rowl.Concepts.copy_individual_identity, Rowl.Copies.copy_literal_eq])
      (fun I => by simp [satisfies, extend_individual_fun])
      (fun _ _ h => by cases h)
  | NegativeDataPropertyAssertion p a lt =>
    exact copied defs _ fuel (by simp [unfolding.unfold_axiom, Rowl.Copies.copy_data_property_eq, Rowl.Concepts.copy_individual_identity, Rowl.Copies.copy_literal_eq])
      (fun I => by simp [satisfies, extend_individual_fun])
      (fun _ _ h => by cases h)
  | AnnotationAssertion p s v =>
    exact dropped_axiom defs _ fuel (by simp [unfolding.unfold_axiom]) (fun I => by simp [satisfies])
      (by simp [axiomIndividuals]) (by simp [keyIndividuals]) (by simp [IsKey])
  | SubAnnotationPropertyOf p q =>
    exact dropped_axiom defs _ fuel (by simp [unfolding.unfold_axiom]) (fun I => by simp [satisfies])
      (by simp [axiomIndividuals]) (by simp [keyIndividuals]) (by simp [IsKey])
  | AnnotationPropertyDomain p i =>
    exact dropped_axiom defs _ fuel (by simp [unfolding.unfold_axiom]) (fun I => by simp [satisfies])
      (by simp [axiomIndividuals]) (by simp [keyIndividuals]) (by simp [IsKey])
  | AnnotationPropertyRange p i =>
    exact dropped_axiom defs _ fuel (by simp [unfolding.unfold_axiom]) (fun I => by simp [satisfies])
      (by simp [axiomIndividuals]) (by simp [keyIndividuals]) (by simp [IsKey])

/-! ## Closures -/

theorem has_definitions_runs (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    ∃ b, unfolding.has_definitions items index = .ok b := by
  rw [unfolding.has_definitions]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    cases h : items.val[index.val].axiom
    case DatatypeDefinition => exact ⟨true, by simp [inside, alloc.vec.Vec.index_slice_index, lookup, h]⟩
    all_goals
      obtain ⟨b, run⟩ := has_definitions_runs items next
      exact ⟨b, by simp [inside, alloc.vec.Vec.index_slice_index, lookup, h, advance, run]⟩
  · exact ⟨false, by simp [inside]⟩
termination_by items.val.length - index.val
decreasing_by all_goals omega


/-- The datatype definitions among axioms, without their annotations. -/
def definitionsOf : List AnnotatedAxiom → List AnnotatedAxiom
  | [] => []
  | a :: rest =>
    match a.axiom with
    | .DatatypeDefinition dt r => ⟨alloc.vec.Vec.new Annotation, .DatatypeDefinition dt r⟩ :: definitionsOf rest
    | _ => definitionsOf rest

theorem definitions_from_spec (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) (room : out.val.length + (items.val.length - index.val) ≤ Usize.max) :
    ∃ v, unfolding.definitions_from items index out = .ok v ∧
      v.val = out.val ++ definitionsOf (items.val.drop index.val) := by
  rw [unfolding.definitions_from]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    rw [List.drop_eq_getElem_cons inside]
    cases h : items.val[index.val].axiom
    case DatatypeDefinition dt r =>
      have fits : out.val.length < Usize.max := by omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out
        ⟨alloc.vec.Vec.new Annotation, .DatatypeDefinition dt r⟩ fits)
      obtain ⟨v, run, value⟩ := definitions_from_spec items next pushed (by rw [contents, nextIs]; simp; omega)
      refine ⟨v, by simp [inside, alloc.vec.Vec.index_slice_index, lookup, h, UScalar.lt_equiv,
        alloc.vec.Vec.len_val, usize_max_val, fits, Rowl.Copies.copy_datatype_eq, Rowl.Copies.copy_range_eq, push,
        advance, run], ?_⟩
      rw [value, contents, nextIs]
      simp [definitionsOf, h]
    all_goals
      obtain ⟨v, run, value⟩ := definitions_from_spec items next out (by rw [nextIs]; omega)
      exact ⟨v, by simp [inside, alloc.vec.Vec.index_slice_index, lookup, h, advance, run],
        by rw [value, nextIs]; simp [definitionsOf, h]⟩
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    exact ⟨out, by simp [inside], by simp [empty, definitionsOf]⟩
termination_by items.val.length - index.val
decreasing_by all_goals omega

theorem definitions_spec (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ defs, unfolding.definitions items = .ok defs ∧ defs.val = definitionsOf items.val := by
  obtain ⟨v, run, value⟩ := definitions_from_spec items 0#usize (alloc.vec.Vec.new AnnotatedAxiom)
    (by simp)
  exact ⟨v, by simp [unfolding.definitions, run], by simpa using value⟩

/-- Each definition defines a datatype that is not predefined and that no
    later definition defines again. -/
def Proper : List AnnotatedAxiom → Prop
  | [] => True
  | a :: rest => (∀ dt r, a.axiom = .DatatypeDefinition dt r →
      ¬ Rowl.DatatypeDefinitions.Predefined dt.iri ∧ definitionOf rest dt = none) ∧ Proper rest

theorem definitions_proper_spec (defs : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    ∃ b, unfolding.definitions_proper defs index = .ok b ∧ (b = true → Proper (defs.val.drop index.val)) := by
  rw [unfolding.definitions_proper]
  by_cases inside : index.val < defs.val.length
  · have lookup : defs.index_usize index = .ok defs.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    rw [List.drop_eq_getElem_cons inside]
    cases h : defs.val[index.val].axiom
    case DatatypeDefinition dt r =>
      by_cases pre : Rowl.DatatypeDefinitions.Predefined dt.iri
      · exact ⟨false, by simp [inside, alloc.vec.Vec.index_slice_index, lookup, h,
          Rowl.DatatypeDefinitions.predefined_total_correct, pre], by simp⟩
      · cases found : definitionOf (defs.val.drop next.val) dt with
        | some _ =>
          exact ⟨false, by simp [inside, alloc.vec.Vec.index_slice_index, lookup, h,
            Rowl.DatatypeDefinitions.predefined_total_correct, pre, advance, definition_from_eq, found], by simp⟩
        | none =>
          obtain ⟨b, run, facts⟩ := definitions_proper_spec defs next
          refine ⟨b, by simp [inside, alloc.vec.Vec.index_slice_index, lookup, h,
            Rowl.DatatypeDefinitions.predefined_total_correct, pre, advance, definition_from_eq, found, run],
            fun hb => ?_⟩
          have rest := facts hb
          rw [nextIs] at rest found
          refine ⟨fun dt' r' h' => ?_, rest⟩
          rw [h] at h'
          cases h'
          exact ⟨pre, found⟩
    all_goals
      obtain ⟨b, run, facts⟩ := definitions_proper_spec defs next
      refine ⟨b, by simp [inside, alloc.vec.Vec.index_slice_index, lookup, h, advance, run], fun hb => ?_⟩
      have rest := facts hb
      rw [nextIs] at rest
      exact ⟨fun dt r h' => (by rw [h] at h'; cases h'), rest⟩
  · have empty : defs.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    exact ⟨true, by simp [inside], fun _ => by rw [empty]; trivial⟩
termination_by defs.val.length - index.val
decreasing_by all_goals omega

/-- How a closure unfolds, axiom by axiom: each axiom is kept with its
    unfolding, or dropped. -/
inductive ItemsUnfold (defs : alloc.vec.Vec AnnotatedAxiom) : List AnnotatedAxiom → List AnnotatedAxiom → Prop
  | nil : ItemsUnfold defs [] []
  | keep {a : AnnotatedAxiom} {a' : Axiom} {rest rest' : List AnnotatedAxiom} :
      AxiomKeeps.{u,v} defs a.axiom a' → ItemsUnfold defs rest rest' →
      ItemsUnfold defs (a :: rest) (⟨alloc.vec.Vec.new Annotation, a'⟩ :: rest')
  | drop {a : AnnotatedAxiom} {rest rest' : List AnnotatedAxiom} :
      Dropped.{u,v} defs a.axiom → ItemsUnfold defs rest rest' → ItemsUnfold defs (a :: rest) rest'

theorem unfold_from_spec (defs items : alloc.vec.Vec AnnotatedAxiom) (index : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, unfolding.unfold_from defs items index out = .ok res ∧ ∀ result, res = some result →
      ∃ ys, result.val = out.val ++ ys ∧ ItemsUnfold.{u,v} defs (items.val.drop index.val) ys := by
  rw [unfolding.unfold_from]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨res, run, facts⟩ := unfold_axiom_spec.{u,v} defs items.val[index.val].axiom
      (alloc.vec.Vec.len defs) rfl
    cases res with
    | none =>
      exact ⟨none, by simp [inside, alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
    | some o =>
      obtain ⟨droppedFact, keptFact⟩ := facts o rfl
      cases o with
      | none =>
        obtain ⟨res2, run2, facts2⟩ := unfold_from_spec defs items next out
        refine ⟨res2, by simp [inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, run2],
          fun result hres => ?_⟩
        obtain ⟨ys, value, unfolds⟩ := facts2 result hres
        refine ⟨ys, value, ?_⟩
        rw [List.drop_eq_getElem_cons inside]
        rw [nextIs] at unfolds
        exact .drop (droppedFact rfl) unfolds
      | some a' =>
        by_cases fits : out.val.length < Usize.max
        · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out
            ⟨alloc.vec.Vec.new Annotation, a'⟩ fits)
          obtain ⟨res2, run2, facts2⟩ := unfold_from_spec defs items next pushed
          refine ⟨res2, by simp [inside, alloc.vec.Vec.index_slice_index, lookup, run, UScalar.lt_equiv,
            alloc.vec.Vec.len_val, usize_max_val, fits, push, advance, run2], fun result hres => ?_⟩
          obtain ⟨ys, value, unfolds⟩ := facts2 result hres
          refine ⟨⟨alloc.vec.Vec.new Annotation, a'⟩ :: ys, by rw [value, contents]; simp, ?_⟩
          rw [List.drop_eq_getElem_cons inside]
          rw [nextIs] at unfolds
          exact .keep (keptFact a' rfl) unfolds
        · exact ⟨none, by simp [inside, alloc.vec.Vec.index_slice_index, lookup, run, UScalar.lt_equiv,
            alloc.vec.Vec.len_val, usize_max_val, fits], by simp⟩
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some out, by simp [inside], fun result hres => ?_⟩
    cases hres
    exact ⟨[], by simp, by rw [empty]; exact .nil⟩
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- The unfolding of a closure with its definitions `defs`: the definitions
    are proper, and the closure unfolds axiom by axiom. -/
theorem unfold_items_spec (defs items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, unfolding.unfold_items defs items = .ok res ∧ ∀ unfolded, res = some unfolded →
      Proper defs.val ∧ ItemsUnfold.{u,v} defs items.val unfolded.val := by
  obtain ⟨b, runB, factsB⟩ := definitions_proper_spec defs 0#usize
  cases b with
  | false => exact ⟨none, by simp [unfolding.unfold_items, runB], by simp⟩
  | true =>
    obtain ⟨res, run, facts⟩ := unfold_from_spec.{u,v} defs items 0#usize (alloc.vec.Vec.new AnnotatedAxiom)
    refine ⟨res, by simp [unfolding.unfold_items, runB, run], fun unfolded h => ?_⟩
    obtain ⟨ys, value, unfolds⟩ := facts unfolded h
    have same : unfolded.val = ys := by simpa using value
    exact ⟨by simpa using factsB rfl, by rw [same]; simpa using unfolds⟩

/-- The unfolding of a question. -/
theorem unfold_question_spec (defs : alloc.vec.Vec AnnotatedAxiom) (c : ClassExpression) :
    ∃ res, unfolding.unfold_question defs c = .ok res ∧ ∀ c', res = some c' → ClassKeeps.{u,v} defs c c' := by
  obtain ⟨res, run, facts⟩ := unfold_class_spec.{u,v} defs c (alloc.vec.Vec.len defs)
  exact ⟨res, by simp [unfolding.unfold_question, run], facts⟩

/-! ## Models -/

theorem literal_predefined : Rowl.DatatypeDefinitions.Predefined literalDatatype.iri := by
  unfold Rowl.DatatypeDefinitions.Predefined
  decide

/-- The first definition of a datatype among proper definitions is its only
    one. -/
theorem proper_found {l : List AnnotatedAxiom} (proper : Proper l) {a : AnnotatedAxiom} (mem : a ∈ l)
    {dt : Datatype} {r : DataRange} (h : a.axiom = .DatatypeDefinition dt r) : definitionOf l dt = some r := by
  induction l with
  | nil => cases mem
  | cons b rest ih =>
    obtain ⟨here, later⟩ := proper
    rcases List.mem_cons.mp mem with same | inRest
    · subst same
      simp [definitionOf, h]
    · have found := ih later inRest
      simp only [definitionOf]
      split
      · rename_i d r' hb
        by_cases same : d.iri.spelling.val = dt.iri.spelling.val
        · have none' := (here d r' hb).2
          rw [datatype_spelling] at same
          subst same
          rw [none'] at found
          cases found
        · simp [same, found]
      · exact found

theorem proper_not_predefined {l : List AnnotatedAxiom} (proper : Proper l) {a : AnnotatedAxiom} (mem : a ∈ l)
    {dt : Datatype} {r : DataRange} (h : a.axiom = .DatatypeDefinition dt r) :
    ¬ Rowl.DatatypeDefinitions.Predefined dt.iri := by
  induction l with
  | nil => cases mem
  | cons b rest ih =>
    obtain ⟨here, later⟩ := proper
    rcases List.mem_cons.mp mem with same | inRest
    · subst same
      exact (here dt r h).1
    · exact ih later inRest

theorem mem_definitionsOf {items : List AnnotatedAxiom} {a : AnnotatedAxiom} (mem : a ∈ definitionsOf items) :
    ∃ b ∈ items, ∃ dt r, b.axiom = .DatatypeDefinition dt r ∧ a = ⟨alloc.vec.Vec.new Annotation, .DatatypeDefinition dt r⟩ := by
  induction items with
  | nil => cases mem
  | cons b rest ih =>
    simp only [definitionsOf] at mem
    split at mem
    · rename_i dt r hb
      rcases List.mem_cons.mp mem with same | inRest
      · exact ⟨b, List.mem_cons_self, dt, r, hb, same⟩
      · obtain ⟨c, mc, rest'⟩ := ih inRest
        exact ⟨c, List.mem_cons_of_mem _ mc, rest'⟩
    · obtain ⟨c, mc, rest'⟩ := ih mem
      exact ⟨c, List.mem_cons_of_mem _ mc, rest'⟩

theorem definitionsOf_mem {items : List AnnotatedAxiom} {b : AnnotatedAxiom} (mem : b ∈ items) {dt : Datatype}
    {r : DataRange} (h : b.axiom = .DatatypeDefinition dt r) :
    (⟨alloc.vec.Vec.new Annotation, .DatatypeDefinition dt r⟩ : AnnotatedAxiom) ∈ definitionsOf items := by
  induction items with
  | nil => cases mem
  | cons c rest ih =>
    simp only [definitionsOf]
    rcases List.mem_cons.mp mem with same | inRest
    · subst same
      simp [h]
    · have := ih inRest
      split <;> simp [this]

/-- Two unfoldings of a data range are one. -/
theorem unfold_range_unique {defs : alloc.vec.Vec AnnotatedAxiom} {r : DataRange} {f g : Usize} {a b : DataRange}
    (ha : unfolding.unfold_range defs r f = .ok (some a)) (hb : unfolding.unfold_range defs r g = .ok (some b)) :
    a = b := by
  rcases le_total f.val g.val with fg | gf
  · obtain ⟨res, run, facts⟩ := unfold_range_spec.{0,0} defs r f
    rw [ha] at run
    have same := Result.ok_injective run
    have more := (facts a same.symm).1 g fg
    rw [hb] at more
    exact (Option.some.inj (Result.ok_injective more)).symm
  · obtain ⟨res, run, facts⟩ := unfold_range_spec.{0,0} defs r g
    rw [hb] at run
    have same := Result.ok_injective run
    have more := (facts b same.symm).1 f gf
    rw [ha] at more
    exact Option.some.inj (Result.ok_injective more)

/-- The extension satisfies a definition whose data range unfolds. -/
theorem extend_definition {Object : Type u} {Value : Type v} (defs : alloc.vec.Vec AnnotatedAxiom)
    (I : Interpretation Object Value) {dt : Datatype} {r r' : DataRange} (found : definitionOf defs.val dt = some r)
    (run : unfolding.unfold_range defs r (alloc.vec.Vec.len defs) = .ok (some r')) :
    satisfies (extend defs I) (.DatatypeDefinition dt r) := by
  obtain ⟨res, run2, facts⟩ := unfold_range_spec.{u,v} defs r (alloc.vec.Vec.len defs)
  rw [run] at run2
  obtain ⟨_, _, keepsExtend⟩ := facts r' (Result.ok_injective run2).symm
  intro x
  rw [keepsExtend I x]
  simp only [extend, found]
  constructor
  · rintro ⟨f, r'', run'', holds⟩
    rw [unfold_range_unique run'' run] at holds
    exact holds
  · intro holds
    exact ⟨_, r', run, holds⟩

/-- The closure defines no datatype of the datatype map (OWL 2 Structural
    Specification §9.4). -/
def DefinesNew {Native : Type w} (D : DatatypeMap Native) (items : List AnnotatedAxiom) : Prop :=
  ∀ a ∈ items, ∀ dt r, a.axiom = .DatatypeDefinition dt r → ¬ D.supported dt

/-- The extension of an interpretation is one, for a datatype map that has
    none of the defined datatypes. -/
theorem extend_interpretation {Object : Type u} {Value : Type v} {Native : Type w} {D : DatatypeMap Native}
    {embed : ValueEmbedding D Value} {V : Vocabulary} {I : Interpretation Object Value}
    (interp : IsInterpretation D embed V I) (defs : alloc.vec.Vec AnnotatedAxiom) (proper : Proper defs.val)
    (fresh : DefinesNew D defs.val) : IsInterpretation D embed V (extend defs I) := by
  obtain ⟨thing, nothing, top, bottom, topData, bottomData, datatypes, literal, literals, facets, named⟩ := interp
  refine ⟨thing, nothing, top, bottom, topData, bottomData, fun dt supported x => ?_, fun x => ?_, literals,
    facets, named⟩
  · cases found : definitionOf defs.val dt with
    | none =>
      simp only [extend, found]
      exact datatypes dt supported x
    | some r =>
      obtain ⟨a, ma, ha⟩ := definitionOf_mem found
      exact absurd supported (fresh a ma dt r ha)
  · cases found : definitionOf defs.val literalDatatype with
    | none =>
      simp only [extend, found]
      exact literal x
    | some r =>
      obtain ⟨a, ma, ha⟩ := definitionOf_mem found
      exact absurd literal_predefined (proper_not_predefined proper ma ha)

/-- Other anonymous individuals give a data range the same values. -/
theorem data_denote_anonymous {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (g : AnonymousIndividual → Object) (r : DataRange) (x : Value) :
    dataDenote (withAnonymous I g) r x ↔ dataDenote I r x := by
  cases r with
  | Datatype dt =>
    rw [dataDenote, dataDenote]
    exact Iff.rfl
  | Intersection xs =>
    have each : ∀ e ∈ xs.elements, (dataDenote (withAnonymous I g) e x ↔ dataDenote I e x) := fun e mem => by
      have := members_bound xs e mem
      exact data_denote_anonymous I g e x
    rw [dataDenote, dataDenote, each xs.first (by simp [AtLeastTwo.elements]),
      each xs.second (by simp [AtLeastTwo.elements])]
    exact and_congr_right fun _ => and_congr_right fun _ =>
      forall₂_congr fun e mem => each e (by simp [AtLeastTwo.elements, mem])
  | Union xs =>
    have each : ∀ e ∈ xs.elements, (dataDenote (withAnonymous I g) e x ↔ dataDenote I e x) := fun e mem => by
      have := members_bound xs e mem
      exact data_denote_anonymous I g e x
    rw [dataDenote, dataDenote, each xs.first (by simp [AtLeastTwo.elements]),
      each xs.second (by simp [AtLeastTwo.elements])]
    exact or_congr_right (or_congr_right
      (exists_congr fun e => exists_congr fun mem => each e (by simp [AtLeastTwo.elements, mem])))
  | Complement inner =>
    rw [dataDenote, dataDenote]
    exact not_congr (data_denote_anonymous I g inner x)
  | OneOf xs =>
    rw [dataDenote, dataDenote]
    exact Iff.rfl
  | Restriction dt fs =>
    rw [dataDenote, dataDenote]
    exact Iff.rfl
termination_by sizeOf r
decreasing_by all_goals (subst_vars; first | omega | (simp_wf <;> omega))

/-- The definitions of a closure hold in its models. -/
theorem definitions_hold {Object : Type u} {Value : Type v} {I : Interpretation Object Value}
    {items : List AnnotatedAxiom} (g : AnonymousIndividual → Object)
    (sat : satisfiesClosure (withAnonymous I g) items) : DefinitionsHold I (definitionsOf items) := by
  intro a mem
  obtain ⟨b, mb, dt, r, hb, rfl⟩ := mem_definitionsOf mem
  have holds := sat b mb
  rw [hb] at holds
  intro x
  exact (holds x).trans (data_denote_anonymous I g r x)

theorem items_forward {defs : alloc.vec.Vec AnnotatedAxiom} {items unfolded : List AnnotatedAxiom}
    (unfolds : ItemsUnfold.{u,v} defs items unfolded) {Object : Type u} {Value : Type v}
    (I : Interpretation Object Value) (hold : DefinitionsHold I defs.val) (sat : satisfiesClosure I items) :
    satisfiesClosure I unfolded := by
  induction unfolds with
  | nil => exact fun _ h => by cases h
  | keep keeps _ ih =>
    intro b mem
    rcases List.mem_cons.mp mem with rfl | later
    · exact (keeps.1 I hold).mp (sat _ List.mem_cons_self)
    · exact ih (fun c hc => sat c (List.mem_cons_of_mem _ hc)) b later
  | drop _ _ ih => exact ih (fun c hc => sat c (List.mem_cons_of_mem _ hc))

theorem items_backward {defs : alloc.vec.Vec AnnotatedAxiom} {items unfolded : List AnnotatedAxiom}
    (unfolds : ItemsUnfold.{u,v} defs items unfolded) {Object : Type u} {Value : Type v}
    (I : Interpretation Object Value) (sat : satisfiesClosure I unfolded)
    (defined : ∀ a ∈ items, ∀ dt r r', a.axiom = .DatatypeDefinition dt r →
      unfolding.unfold_range defs r (alloc.vec.Vec.len defs) = .ok (some r') →
      satisfies (extend defs I) a.axiom) :
    satisfiesClosure (extend defs I) items := by
  induction unfolds with
  | nil => exact fun _ h => by cases h
  | keep keeps _ ih =>
    intro b mem
    rcases List.mem_cons.mp mem with rfl | later
    · exact (keeps.2 I).mpr (sat _ List.mem_cons_self)
    · exact ih (fun c hc => sat c (List.mem_cons_of_mem _ hc))
        (fun a ma => defined a (List.mem_cons_of_mem _ ma)) b later
  | drop dropped _ ih =>
    intro b mem
    rcases List.mem_cons.mp mem with rfl | later
    · rcases dropped with ⟨⟨dt, r, r', h, run⟩ | always, -⟩
      · exact defined _ List.mem_cons_self dt r r' h run
      · exact always _
    · exact ih sat (fun a ma => defined a (List.mem_cons_of_mem _ ma)) b later

/-- The unfolding of a closure names the individuals of the closure and has
    its keys. -/
theorem items_names {defs : alloc.vec.Vec AnnotatedAxiom} {items unfolded : List AnnotatedAxiom}
    (unfolds : ItemsUnfold.{u,v} defs items unfolded) :
    closureIndividuals unfolded = closureIndividuals items ∧ (Keyed unfolded ↔ Keyed items) := by
  induction unfolds with
  | nil => exact ⟨rfl, Iff.rfl⟩
  | keep keeps _ ih =>
    obtain ⟨same, keyed⟩ := ih
    constructor
    · simp only [closureIndividuals, List.flatMap_cons] at same ⊢
      rw [keeps.names, keeps.keys, same]
    · simp only [Keyed] at keyed ⊢
      simp only [List.mem_cons, exists_eq_or_imp, keeps.key, keyed]
  | drop dropped _ ih =>
    obtain ⟨same, keyed⟩ := ih
    obtain ⟨_, names, keys, notKey⟩ := dropped
    constructor
    · simp only [closureIndividuals, List.flatMap_cons, names, keys, List.nil_append] at same ⊢
      exact same
    · simp only [Keyed] at keyed ⊢
      simp only [List.mem_cons, exists_eq_or_imp, notKey, false_or, keyed]

/-- A vocabulary that names the keyed individuals of a closure names those
    of its unfolding. -/
theorem names_keyed {V : Vocabulary} {defs : alloc.vec.Vec AnnotatedAxiom} {items unfolded : List AnnotatedAxiom}
    (unfolds : ItemsUnfold.{u,v} defs items unfolded) (names : NamesKeyed V items) : NamesKeyed V unfolded := by
  obtain ⟨same, keyed⟩ := items_names unfolds
  intro k a mem
  exact names (keyed.mp k) a (same ▸ mem)

/-- The unfolding of a closure has no datatype definition. -/
theorem unfolded_undefined {defs : alloc.vec.Vec AnnotatedAxiom} {items unfolded : List AnnotatedAxiom}
    (unfolds : ItemsUnfold.{u,v} defs items unfolded) : ∀ b ∈ unfolded, ∀ dt r, b.axiom ≠ .DatatypeDefinition dt r := by
  induction unfolds with
  | nil => exact fun _ h => by cases h
  | keep keeps _ ih =>
    intro b mem
    rcases List.mem_cons.mp mem with rfl | later
    · exact keeps.undefined
    · exact ih b later
  | drop _ _ ih => exact ih

/-- The unfolding of a closure defines no datatype of any datatype map. -/
theorem unfolded_defines_new {Native : Type w} (D : DatatypeMap Native) {defs : alloc.vec.Vec AnnotatedAxiom}
    {items unfolded : List AnnotatedAxiom} (unfolds : ItemsUnfold.{u,v} defs items unfolded) :
    DefinesNew D unfolded :=
  fun b mem dt r h => absurd h (unfolded_undefined unfolds b mem dt r)

/-- A closure without datatype definitions defines no datatype of any
    datatype map. -/
theorem defines_new_of_none {Native : Type w} (D : DatatypeMap Native) {items : List AnnotatedAxiom}
    (none' : ∀ b ∈ items, ∀ dt r, b.axiom ≠ .DatatypeDefinition dt r) : DefinesNew D items :=
  fun b mem dt r h => absurd h (none' b mem dt r)

theorem extend_anonymous {Object : Type u} {Value : Type v} (defs : alloc.vec.Vec AnnotatedAxiom)
    (I : Interpretation Object Value) (g : AnonymousIndividual → Object) :
    withAnonymous (extend defs I) g = extend defs (withAnonymous I g) := by
  simp only [withAnonymous, extend]
  congr 1
  funext dt x
  split
  · exact propext (exists_congr fun f => exists_congr fun r' =>
      and_congr_right fun _ => (data_denote_anonymous I g r' x).symm)
  · rfl

private theorem definitions_self {Object : Type u} {Value : Type v} {J : Interpretation Object Value}
    {items : List AnnotatedAxiom} (sat : satisfiesClosure J items) : DefinitionsHold J (definitionsOf items) := by
  intro a mem
  obtain ⟨b, mb, dt, r, hb, rfl⟩ := mem_definitionsOf mem
  have holds := sat b mb
  rw [hb] at holds
  exact holds

/-- A model of a closure is a model of its unfolding, in which the
    definitions hold. -/
theorem unfolded_model {Object : Type u} {Value : Type v} {Native : Type w} {D : DatatypeMap Native}
    {embed : ValueEmbedding D Value} {V : Vocabulary} {items defs : alloc.vec.Vec AnnotatedAxiom}
    {unfolded : List AnnotatedAxiom} (hdefs : defs.val = definitionsOf items.val)
    (unfolds : ItemsUnfold.{u,v} defs items.val unfolded) {I : Interpretation Object Value}
    (model : Model D embed V I items.val) : Model D embed V I unfolded ∧ DefinitionsHold I defs.val := by
  obtain ⟨vocab, interp, g, sat⟩ := model
  have holdJ : DefinitionsHold (withAnonymous I g) defs.val := by rw [hdefs]; exact definitions_self sat
  exact ⟨⟨vocab, interp, g, items_forward unfolds _ holdJ sat⟩, by rw [hdefs]; exact definitions_hold g sat⟩

/-- A model of the unfolding of a closure, extended to the defined
    datatypes, is a model of the closure. -/
theorem extended_model {Object : Type u} {Value : Type v} {Native : Type w} {D : DatatypeMap Native}
    {embed : ValueEmbedding D Value} {V : Vocabulary} {items defs : alloc.vec.Vec AnnotatedAxiom}
    {unfolded : List AnnotatedAxiom} (hdefs : defs.val = definitionsOf items.val) (proper : Proper defs.val)
    (unfolds : ItemsUnfold.{u,v} defs items.val unfolded) (fresh : DefinesNew D items.val)
    {I : Interpretation Object Value} (model : Model D embed V I unfolded) :
    Model D embed V (extend defs I) items.val := by
  obtain ⟨vocab, interp, g, sat⟩ := model
  have freshDefs : DefinesNew D defs.val := by
    intro a ma dt r ha
    rw [hdefs] at ma
    obtain ⟨b, mb, dt', r', hb, rfl⟩ := mem_definitionsOf ma
    simp only [Axiom.DatatypeDefinition.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    exact fresh b mb dt' r' hb
  refine ⟨vocab, extend_interpretation interp defs proper freshDefs, g, ?_⟩
  rw [extend_anonymous]
  refine items_backward unfolds _ sat (fun a ma dt r r' ha run => ?_)
  rw [ha]
  have mem := definitionsOf_mem ma ha
  rw [← hdefs] at mem
  exact extend_definition defs _ (proper_found proper mem rfl) run

section Questions
variable {Native : Type w} {D : DatatypeMap Native} {V : Vocabulary} {items defs : alloc.vec.Vec AnnotatedAxiom}
  {unfolded : List AnnotatedAxiom}

/-- A closure and its unfolding have models together. -/
theorem unfolded_consistent (hdefs : defs.val = definitionsOf items.val) (proper : Proper defs.val)
    (unfolds : ItemsUnfold.{u,v} defs items.val unfolded) (fresh : DefinesNew D items.val) :
    Consistent.{u,v,w} D V items.val ↔ Consistent.{u,v,w} D V unfolded := by
  constructor
  · rintro ⟨Object, Value, embed, I, model⟩
    exact ⟨Object, Value, embed, I, (unfolded_model hdefs unfolds model).1⟩
  · rintro ⟨Object, Value, embed, I, model⟩
    exact ⟨Object, Value, embed, extend defs I, extended_model hdefs proper unfolds fresh model⟩

/-- A class expression is satisfiable with a closure exactly when its
    unfolding is with the unfolding of the closure. -/
theorem unfolded_satisfiable (hdefs : defs.val = definitionsOf items.val) (proper : Proper defs.val)
    (unfolds : ItemsUnfold.{u,v} defs items.val unfolded) (fresh : DefinesNew D items.val)
    {c c' : ClassExpression} (keeps : ClassKeeps.{u,v} defs c c') :
    ClassSatisfiable.{u,v,w} D V items.val c ↔ ClassSatisfiable.{u,v,w} D V unfolded c' := by
  constructor
  · rintro ⟨Object, Value, embed, I, model, x, hx⟩
    obtain ⟨model', hold⟩ := unfolded_model hdefs unfolds model
    exact ⟨Object, Value, embed, I, model', x, (keeps.1 I hold x).mp hx⟩
  · rintro ⟨Object, Value, embed, I, model, x, hx⟩
    exact ⟨Object, Value, embed, extend defs I, extended_model hdefs proper unfolds fresh model, x,
      (keeps.2 I x).mpr hx⟩

/-- Subsumption with a closure is subsumption of the unfoldings with the
    unfolding of the closure. -/
theorem unfolded_subsumed (hdefs : defs.val = definitionsOf items.val) (proper : Proper defs.val)
    (unfolds : ItemsUnfold.{u,v} defs items.val unfolded) (fresh : DefinesNew D items.val)
    {a a' b b' : ClassExpression} (keepsA : ClassKeeps.{u,v} defs a a') (keepsB : ClassKeeps.{u,v} defs b b') :
    Subsumed.{u,v,w} D V items.val a b ↔ Subsumed.{u,v,w} D V unfolded a' b' := by
  constructor
  · intro holds Object Value embed I model x hx
    have := holds Object Value embed (extend defs I) (extended_model hdefs proper unfolds fresh model) x
      ((keepsA.2 I x).mpr hx)
    exact (keepsB.2 I x).mp this
  · intro holds Object Value embed I model x hx
    obtain ⟨model', hold⟩ := unfolded_model hdefs unfolds model
    exact (keepsB.1 I hold x).mpr (holds Object Value embed I model' x ((keepsA.1 I hold x).mp hx))

/-- A named individual is an instance of a class expression with a closure
    exactly when it is one of its unfolding with the unfolding of the closure. -/
theorem unfolded_instance (hdefs : defs.val = definitionsOf items.val) (proper : Proper defs.val)
    (unfolds : ItemsUnfold.{u,v} defs items.val unfolded) (fresh : DefinesNew D items.val)
    (ind : NamedIndividual) {c c' : ClassExpression} (keeps : ClassKeeps.{u,v} defs c c') :
    InstanceOf.{u,v,w} D V items.val ind c ↔ InstanceOf.{u,v,w} D V unfolded ind c' := by
  constructor
  · intro holds Object Value embed I model
    have := holds Object Value embed (extend defs I) (extended_model hdefs proper unfolds fresh model)
    exact (keeps.2 I _).mp this
  · intro holds Object Value embed I model
    obtain ⟨model', hold⟩ := unfolded_model hdefs unfolds model
    exact (keeps.1 I hold _).mpr (holds Object Value embed I model')

end Questions

end Rowl.Unfolding
