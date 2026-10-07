import Rowl.DataRegions

/-!
The whole encoding of a closure by `data_ontology`: the axioms its axioms become
(`encode_items_meaning`), and the encoding's own axioms (`encode_meaning`). An
interpretation of the encoding satisfies those exactly when the object
properties of the context relate no data nodes, the data properties' roles lead
from elements that are no data nodes to data nodes, the kinds in use are
included in and disjoint from each other as their datatypes are, the booleans
are the two truth values, each literal value's individual is a data node in the
kinds its value is in, with a pattern of bit classes that tells it apart from
the other literal values and, when numbers are ordered, in the cuts of its
number, the axioms of the cuts hold (`RegionFacts`), and the further individual
is no data node (`Frame`).
-/
namespace Rowl.DataStructure
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.AlcOntology (RoleOf)
open Rowl.Datatypes (InKind)
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.DataRegions
open Rowl.Regions (cutAt Ordered FineCuts)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe u v w x

variable {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}

/-! ### The axioms of a closure -/

/-- What the axioms a closure's axioms become mean, together. -/
def ItemsMeans (context : data_ontology.Context) (items new : List AnnotatedAxiom) : Prop :=
  (∀ {Object : Type u} {Value : Type v} {Object' : Type w} {Value' : Type x}
    (I : Interpretation Object Value) (J : Interpretation Object' Value') (obj : Object → Object')
    (known : Individual → Prop) (atoms : List (DataProperty × Option DataRange × Nat))
    (lit : datatypes.DataValue → Value) (num : ℝ → Value) (place : Object → Value → Object' → Prop),
    Simulates context I J obj known atoms → Placed context I J obj lit num place → RangeFrame I J lit num →
    (∀ item ∈ items, ∀ a ∈ axiomAtoms item.axiom, a ∈ atoms) →
    (∀ item ∈ items, ∀ a ∈ axiomIndividuals item.axiom, known a) →
      ((∀ b ∈ new, satisfies J b.axiom) → ∀ item ∈ items, satisfies I item.axiom) ∧
      (Inert context J obj place → (∀ item ∈ items, satisfies I item.axiom) → ∀ b ∈ new, satisfies J b.axiom)) ∧
  (∀ item ∈ items, ∀ a ∈ axiomIndividuals item.axiom, Plain a) ∧
  (∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'), (∀ b ∈ new, satisfies J b.axiom) →
    ∀ item ∈ items, ∀ a ∈ axiomIndividuals item.axiom, ¬ J.classes dataClass (individual J a))

theorem items_means_nil (context : data_ontology.Context) : ItemsMeans.{u,v,w,x} context [] [] := by
  refine ⟨?_, by simp, fun _ _ => by simp⟩
  intro Object Value Object' Value' I J obj known atoms lit num place _ _ _ _ _
  exact ⟨fun _ => by simp, fun _ _ => by simp⟩

theorem items_means_cons {context : data_ontology.Context} {item : AnnotatedAxiom}
    {rest new1 new2 : List AnnotatedAxiom} (means : AxiomMeans.{u,v,w,x} context item.axiom new1)
    (plain : ∀ a ∈ axiomIndividuals item.axiom, Plain a)
    (names : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
      (∀ b ∈ new1, satisfies J b.axiom) → ∀ a ∈ axiomIndividuals item.axiom, ¬ J.classes dataClass (individual J a))
    (tail : ItemsMeans.{u,v,w,x} context rest new2) : ItemsMeans.{u,v,w,x} context (item :: rest) (new1 ++ new2) := by
  obtain ⟨tailMeans, tailPlain, tailNames⟩ := tail
  refine ⟨?_, ?_, ?_⟩
  · intro Object Value Object' Value' I J obj known atoms lit num place sim placed frame atomsIn indsIn
    obtain ⟨sound1, complete1⟩ := means I J obj known atoms lit num place sim placed frame
      (atomsIn item List.mem_cons_self) (indsIn item List.mem_cons_self)
    obtain ⟨sound2, complete2⟩ := tailMeans I J obj known atoms lit num place sim placed frame
      (fun i m => atomsIn i (List.mem_cons_of_mem _ m)) (fun i m => indsIn i (List.mem_cons_of_mem _ m))
    constructor
    · intro holds i mem
      rcases List.mem_cons.mp mem with rfl | later
      · exact sound1 (fun b m => holds b (List.mem_append_left _ m))
      · exact sound2 (fun b m => holds b (List.mem_append_right _ m)) i later
    · intro inert holds b mem
      rcases List.mem_append.mp mem with early | late
      · exact complete1 inert (holds item List.mem_cons_self) b early
      · exact complete2 inert (fun i m => holds i (List.mem_cons_of_mem _ m)) b late
  · intro i mem
    rcases List.mem_cons.mp mem with rfl | later
    · exact plain
    · exact tailPlain i later
  · intro Object' Value' J holds i mem
    rcases List.mem_cons.mp mem with rfl | later
    · exact names J (fun b m => holds b (List.mem_append_left _ m))
    · exact tailNames J (fun b m => holds b (List.mem_append_right _ m)) i later

theorem encode_items_meaning (context : data_ontology.Context) (items : alloc.vec.Vec AnnotatedAxiom)
    (index : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.encode_items context items index out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ItemsMeans.{u,v,w,x} context (items.val.drop index.val) new := by
  rw [data_ontology.encode_items]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, facts1⟩ := encode_axiom_meaning.{u,v,w,x} context items.val[index.val].axiom out
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some out1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := encode_items_meaning context items next out1
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance,
        restRun], fun out' h => ?_⟩
      obtain ⟨new2, c2, m2⟩ := restFacts out' h
      obtain ⟨new1, c1, m1, p1, n1⟩ := facts1 out1 rfl
      refine ⟨new1 ++ new2, by rw [c2, c1, List.append_assoc], ?_⟩
      rw [split]
      rw [nextIndex] at m2
      exact items_means_cons m1 p1 n1 m2
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], ?_, ?_⟩⟩
    · cases h; simp
    · rw [List.drop_eq_nil_iff.mpr (show items.val.length ≤ index.val by omega)]
      exact items_means_nil context
termination_by items.val.length - index.val
decreasing_by omega

/-! ### The encoding's own names -/

/-- The further individual that is no data node. -/
noncomputable def objectIndividual : NamedIndividual := Classical.choose object_individual_correct

theorem object_individual_eq : data_ontology.object_individual = .ok (.Named objectIndividual) :=
  (Classical.choose_spec object_individual_correct).1

theorem objectIndividual_name : objectIndividual.iri.spelling.val = objectName :=
  (Classical.choose_spec object_individual_correct).2

/-- The bit class of a position. -/
noncomputable def bitClass (position : Usize) : Class := Classical.choose (bit_class_correct position)

theorem bit_class_eq (position : Usize) : data_ontology.bit_class position = .ok (.Class (bitClass position)) :=
  (Classical.choose_spec (bit_class_correct position)).1

theorem bitClass_name (position : Usize) : (bitClass position).iri.spelling.val = bitName position.val :=
  (Classical.choose_spec (bit_class_correct position)).2

/-! ### Object properties and data properties -/

theorem role_axioms_spec (context : data_ontology.Context) (index : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.role_axioms context index out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ r ∈ context.roles.val.drop index.val, ∀ y y',
          J.objectProperties r y y' → ¬ J.classes dataClass y ∧ ¬ J.classes dataClass y') := by
  rw [data_ontology.role_axioms]
  by_cases inside : index.val < context.roles.val.length
  · have lookup : context.roles.index_usize index = .ok context.roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    have eta : ({ iri := { spelling := context.roles.val[index.val].iri.spelling } } : ObjectProperty) =
      context.roles.val[index.val] := rfl
    let r := context.roles.val[index.val]
    obtain ⟨r1, run1, contents1⟩ := push_spec out (.ObjectPropertyDomain (.Property r) (.ObjectComplementOf (.Class dataClass)))
    cases r1 with
    | none =>
      exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
        Rowl.Nnf.copy_bytes_identity, object_class_eq, eta, r, run1], by simp⟩
    | some out1 =>
      obtain ⟨r2, run2, contents2⟩ := push_spec out1 (.ObjectPropertyRange (.Property r) (.ObjectComplementOf (.Class dataClass)))
      cases r2 with
      | none =>
        exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
          Rowl.Nnf.copy_bytes_identity, object_class_eq, eta, r, run1, run2], by simp⟩
      | some out2 =>
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIndex : next.val = index.val + 1 := by simpa using nextValue
        obtain ⟨rest, restRun, restFacts⟩ := role_axioms_spec context next out2
        refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
          Rowl.Nnf.copy_bytes_identity, object_class_eq, eta, r, run1, run2, advance, restRun], fun out' h => ?_⟩
        obtain ⟨new, c, meaning⟩ := restFacts out' h
        refine ⟨bare (.ObjectPropertyDomain (.Property r) (.ObjectComplementOf (.Class dataClass))) ::
          bare (.ObjectPropertyRange (.Property r) (.ObjectComplementOf (.Class dataClass))) :: new,
          by rw [c, contents2 out2 rfl, contents1 out1 rfl]; simp [bare], fun J => ?_⟩
        have tail := meaning J
        rw [nextIndex] at tail
        rw [split]
        simp only [List.mem_cons, forall_eq_or_imp]
        rw [tail]
        simp only [bare, satisfies, objectRelation, classDenote]
        constructor
        · rintro ⟨domain, range, rest⟩
          exact ⟨fun y y' h => ⟨domain y y' h, range y y' h⟩, rest⟩
        · rintro ⟨here, rest⟩
          exact ⟨fun y y' h => (here y y' h).1, fun y y' h => (here y y' h).2, rest⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp [List.drop_eq_nil_iff.mpr (show context.roles.val.length ≤ index.val by omega)]
termination_by context.roles.val.length - index.val
decreasing_by omega

theorem data_axioms_spec (context : data_ontology.Context) (index : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.data_axioms context index out = .ok res ∧ ∀ out', res = some out' →
      (∀ p ∈ context.data.val.drop index.val, ∃ role, data_ontology.data_role context p = .ok (some role)) ∧
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ p ∈ context.data.val.drop index.val, ∀ role,
          data_ontology.data_role context p = .ok (some role) → ∀ y y', objectRelation J role y y' →
            ¬ J.classes dataClass y ∧ J.classes dataClass y') := by
  rw [data_ontology.data_axioms]
  by_cases inside : index.val < context.data.val.length
  · have lookup : context.data.index_usize index = .ok context.data.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r0, run0, _⟩ := data_role_correct context context.data.val[index.val]
    cases r0 with
    | none =>
      exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run0], by simp⟩
    | some role =>
      obtain ⟨r1, run1, contents1⟩ := push_spec out (.ObjectPropertyDomain role (.ObjectComplementOf (.Class dataClass)))
      cases r1 with
      | none =>
        exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run0,
          object_class_eq, run1], by simp⟩
      | some out1 =>
        obtain ⟨r2, run2, contents2⟩ := push_spec out1 (.ObjectPropertyRange role (.Class dataClass))
        cases r2 with
        | none =>
          exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run0,
            object_class_eq, run1, data_class_eq, run2], by simp⟩
        | some out2 =>
          obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
          have nextIndex : next.val = index.val + 1 := by simpa using nextValue
          obtain ⟨rest, restRun, restFacts⟩ := data_axioms_spec context next out2
          refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run0,
            object_class_eq, run1, data_class_eq, run2, advance, restRun], fun out' h => ?_⟩
          obtain ⟨roles, new, c, meaning⟩ := restFacts out' h
          rw [nextIndex] at roles
          have allRoles : ∀ p ∈ context.data.val.drop index.val, ∃ role,
              data_ontology.data_role context p = .ok (some role) := by
            rw [split]
            intro p mem
            rcases List.mem_cons.mp mem with rfl | later
            · exact ⟨role, run0⟩
            · exact roles p later
          refine ⟨allRoles, ?_⟩
          refine ⟨bare (.ObjectPropertyDomain role (.ObjectComplementOf (.Class dataClass))) ::
            bare (.ObjectPropertyRange role (.Class dataClass)) :: new,
            by rw [c, contents2 out2 rfl, contents1 out1 rfl]; simp [bare], fun J => ?_⟩
          have tail := meaning J
          rw [nextIndex] at tail
          rw [split]
          simp only [List.mem_cons, forall_eq_or_imp]
          rw [tail]
          simp only [bare, satisfies, classDenote]
          constructor
          · rintro ⟨domain, range, rest⟩
            refine ⟨fun role' run' y y' h => ?_, rest⟩
            rw [run0] at run'
            cases Result.ok_injective run'
            exact ⟨domain y y' h, range y y' h⟩
          · rintro ⟨here, rest⟩
            exact ⟨fun y y' h => (here role run0 y y' h).1, fun y y' h => (here role run0 y y' h).2, rest⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ?_⟩
    have empty : context.data.val.drop index.val = [] :=
      List.drop_eq_nil_iff.mpr (show context.data.val.length ≤ index.val by omega)
    exact ⟨by simp [empty], [], by cases h; simp, fun J => by simp [empty]⟩
termination_by context.data.val.length - index.val
decreasing_by omega

/-! ### The kinds in use -/

/-- The first kind's class within the second's, when both are in use. -/
def Included (kinds : data_ontology.Kinds) (J : Interpretation Object' Value') (a b : datatypes.Kind) : Prop :=
  Used kinds a = true → Used kinds b = true → ∀ y, J.classes (kindClass a) y → J.classes (kindClass b) y

/-- The two kinds' classes apart, when both are in use. -/
def Apart (kinds : data_ontology.Kinds) (J : Interpretation Object' Value') (a b : datatypes.Kind) : Prop :=
  Used kinds a = true → Used kinds b = true → ∀ y, ¬ (J.classes (kindClass a) y ∧ J.classes (kindClass b) y)

theorem kinds_axiom_spec (kinds : data_ontology.Kinds) (a b : datatypes.Kind) (inclusion : Bool)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.kinds_axiom kinds a b inclusion out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ y ∈ new, satisfies J y.axiom) ↔ (if inclusion then Included kinds J a b else Apart kinds J a b)) := by
  by_cases ua : Used kinds a = true
  · by_cases ub : Used kinds b = true
    · cases inclusion with
      | true =>
        obtain ⟨r, run, contents⟩ := push_spec out (.SubClassOf (.Class (kindClass a)) (.Class (kindClass b)))
        refine ⟨r, by simp [data_ontology.kinds_axiom, used_eq, ua, ub, kind_class_eq, run],
          fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
        simp [bare, satisfies, classDenote, Included, ua, ub]
      | false =>
        obtain ⟨r, run, contents⟩ := push_spec out
          (.DisjointClasses ⟨.Class (kindClass a), .Class (kindClass b), alloc.vec.Vec.new ClassExpression⟩)
        refine ⟨r, by simp [data_ontology.kinds_axiom, used_eq, ua, ub, kind_class_eq, run],
          fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
        simp [bare, satisfies, pairwiseDisjoint, AtLeastTwo.elements, new_val, classDenote, Apart, ua, ub]
    · refine ⟨some out, by simp [data_ontology.kinds_axiom, used_eq, ua, ub],
        fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
      cases inclusion <;> simp [Included, Apart, ub]
  · refine ⟨some out, by simp [data_ontology.kinds_axiom, used_eq, ua],
      fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    cases inclusion <;> simp [Included, Apart, ua]

/-- The booleans are the individuals of the two truth values. -/
def Truths (context : data_ontology.Context) (J : Interpretation Object' Value') : Prop :=
  context.kinds.boolean = true → ∀ y, J.classes (kindClass .Boolean) y →
    ∃ (i : Usize) (h : i.val < context.values.val.length),
      (context.values.val[i.val] = .Truth true ∨ context.values.val[i.val] = .Truth false) ∧
      J.namedIndividuals (valueIndividual i) = y

theorem value_index_unique {context : data_ontology.Context} (good : Good context) {i j : Usize}
    {hi : i.val < context.values.val.length} {hj : j.val < context.values.val.length}
    (same : context.values.val[i.val] = context.values.val[j.val]) : i = j :=
  UScalar.eq_of_val_eq ((List.Nodup.getElem_inj_iff good.1.2).mp same)

/-- Both truth values are literal values of the context when the booleans are
    in use. -/
def TruthsKnown (context : data_ontology.Context) : Prop :=
  context.kinds.boolean = true → ∀ b, ∃ (i : Usize) (h : i.val < context.values.val.length),
    context.values.val[i.val] = .Truth b

theorem truth_axiom_spec (context : data_ontology.Context) (good : Good context) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.truth_axiom context out = .ok res ∧ ∀ out', res = some out' → TruthsKnown context ∧
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ y ∈ new, satisfies J y.axiom) ↔ Truths context J) := by
  rw [data_ontology.truth_axiom]
  by_cases boolean : context.kinds.boolean = true
  · obtain ⟨t, tRun, _, tFound⟩ := value_index_correct context.values (.Truth true) 0#usize
    obtain ⟨f, fRun, _, fFound⟩ := value_index_correct context.values (.Truth false) 0#usize
    cases t with
    | none => exact ⟨none, by simp [boolean, tRun, fRun], by simp⟩
    | some t =>
      cases f with
      | none => exact ⟨none, by simp [boolean, tRun, fRun], by simp⟩
      | some f =>
        obtain ⟨ht, tValue⟩ := tFound t rfl
        obtain ⟨hf, fValue⟩ := fFound f rfl
        obtain ⟨rest, restRun, restContents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec
          (alloc.vec.Vec.new Individual) (.Named (valueIndividual f)) (by simp [new_val]; scalar_tac))
        obtain ⟨r, run, contents⟩ := push_spec out
          (.SubClassOf (.Class (kindClass .Boolean)) (.ObjectOneOf ⟨.Named (valueIndividual t), rest⟩))
        have known : TruthsKnown context := fun _ b => by
          cases b
          · exact ⟨f, hf, fValue⟩
          · exact ⟨t, ht, tValue⟩
        refine ⟨r, by simp [boolean, tRun, fRun, value_individual_eq, restRun, kind_class_eq, run],
          fun out' h => ⟨known, _, contents out' h, fun J => ?_⟩⟩
        simp only [List.mem_singleton, forall_eq, bare, satisfies, classDenote, NonEmpty.elements, restContents,
          new_val, List.nil_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        constructor
        · intro holds _ y inB
          obtain ⟨a, mem, same⟩ := holds y inB
          rcases mem with rfl | rfl
          · exact ⟨t, ht, .inl tValue, same⟩
          · exact ⟨f, hf, .inr fValue, same⟩
        · intro truths y inB
          obtain ⟨i, hi, which, same⟩ := truths boolean y inB
          rcases which with isTrue | isFalse
          · have := value_index_unique (hi := hi) (hj := ht) good (isTrue.trans tValue.symm)
            subst this
            exact ⟨_, .inl rfl, same⟩
          · have := value_index_unique (hi := hi) (hj := hf) good (isFalse.trans fValue.symm)
            subst this
            exact ⟨_, .inr rfl, same⟩
  · exact ⟨some out, by simp [boolean], fun out' h => ⟨fun yes => absurd yes boolean, [], by cases h; simp,
      fun J => by simp [Truths, boolean]⟩⟩

/-- What the axioms on the kinds in use say. -/
structure KindFacts (context : data_ontology.Context) (J : Interpretation Object' Value') : Prop where
  integerDecimal : Included context.kinds J .Integer .Decimal
  integerRational : Included context.kinds J .Integer .Rational
  integerReal : Included context.kinds J .Integer .Real
  decimalRational : Included context.kinds J .Decimal .Rational
  decimalReal : Included context.kinds J .Decimal .Real
  rationalReal : Included context.kinds J .Rational .Real
  stringPlain : Included context.kinds J .String .Plain
  integerString : Apart context.kinds J .Integer .String
  integerPlain : Apart context.kinds J .Integer .Plain
  integerBoolean : Apart context.kinds J .Integer .Boolean
  decimalString : Apart context.kinds J .Decimal .String
  decimalPlain : Apart context.kinds J .Decimal .Plain
  decimalBoolean : Apart context.kinds J .Decimal .Boolean
  rationalString : Apart context.kinds J .Rational .String
  rationalPlain : Apart context.kinds J .Rational .Plain
  rationalBoolean : Apart context.kinds J .Rational .Boolean
  realString : Apart context.kinds J .Real .String
  realPlain : Apart context.kinds J .Real .Plain
  realBoolean : Apart context.kinds J .Real .Boolean
  stringBoolean : Apart context.kinds J .String .Boolean
  plainBoolean : Apart context.kinds J .Plain .Boolean
  truths : Truths context J

theorem number_axioms_spec (kinds : data_ontology.Kinds) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.number_axioms kinds out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ y ∈ new, satisfies J y.axiom) ↔ Included kinds J .Integer .Decimal ∧ Included kinds J .Integer .Rational ∧
          Included kinds J .Integer .Real ∧ Included kinds J .Decimal .Rational ∧ Included kinds J .Decimal .Real ∧
          Included kinds J .Rational .Real) := by
  rw [data_ontology.number_axioms]
  obtain ⟨r1, run1, f1⟩ := kinds_axiom_spec.{w,x} kinds .Integer .Decimal true out
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some o1 =>
  obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
  obtain ⟨r2, run2, f2⟩ := kinds_axiom_spec.{w,x} kinds .Integer .Rational true o1
  cases r2 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some o2 =>
  obtain ⟨n2, c2, m2⟩ := f2 o2 rfl
  obtain ⟨r3, run3, f3⟩ := kinds_axiom_spec.{w,x} kinds .Integer .Real true o2
  cases r3 with
  | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
  | some o3 =>
  obtain ⟨n3, c3, m3⟩ := f3 o3 rfl
  obtain ⟨r4, run4, f4⟩ := kinds_axiom_spec.{w,x} kinds .Decimal .Rational true o3
  cases r4 with
  | none => exact ⟨none, by simp [run1, run2, run3, run4], by simp⟩
  | some o4 =>
  obtain ⟨n4, c4, m4⟩ := f4 o4 rfl
  obtain ⟨r5, run5, f5⟩ := kinds_axiom_spec.{w,x} kinds .Decimal .Real true o4
  cases r5 with
  | none => exact ⟨none, by simp [run1, run2, run3, run4, run5], by simp⟩
  | some o5 =>
  obtain ⟨n5, c5, m5⟩ := f5 o5 rfl
  obtain ⟨r6, run6, f6⟩ := kinds_axiom_spec.{w,x} kinds .Rational .Real true o5
  refine ⟨r6, by simp [run1, run2, run3, run4, run5, run6], fun out' h => ?_⟩
  obtain ⟨n6, c6, m6⟩ := f6 out' h
  refine ⟨n1 ++ n2 ++ n3 ++ n4 ++ n5 ++ n6, by rw [c6, c5, c4, c3, c2, c1]; simp, fun J => ?_⟩
  simp only [List.forall_mem_append, m1, m2, m3, m4, m5, m6, ↓reduceIte]
  tauto

theorem apart_axioms_spec (kinds : data_ontology.Kinds) (k : datatypes.Kind) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.apart_axioms kinds k out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ y ∈ new, satisfies J y.axiom) ↔ Apart kinds J k .String ∧ Apart kinds J k .Plain ∧
          Apart kinds J k .Boolean) := by
  rw [data_ontology.apart_axioms]
  obtain ⟨r1, run1, f1⟩ := kinds_axiom_spec.{w,x} kinds k .String false out
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some o1 =>
  obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
  obtain ⟨r2, run2, f2⟩ := kinds_axiom_spec.{w,x} kinds k .Plain false o1
  cases r2 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some o2 =>
  obtain ⟨n2, c2, m2⟩ := f2 o2 rfl
  obtain ⟨r3, run3, f3⟩ := kinds_axiom_spec.{w,x} kinds k .Boolean false o2
  refine ⟨r3, by simp [run1, run2, run3], fun out' h => ?_⟩
  obtain ⟨n3, c3, m3⟩ := f3 out' h
  refine ⟨n1 ++ n2 ++ n3, by rw [c3, c2, c1]; simp, fun J => ?_⟩
  simp only [List.forall_mem_append, m1, m2, m3, ↓reduceIte, Bool.false_eq_true]
  tauto

theorem kind_axioms_spec (context : data_ontology.Context) (good : Good context) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.kind_axioms context out = .ok res ∧ ∀ out', res = some out' → TruthsKnown context ∧
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ y ∈ new, satisfies J y.axiom) ↔ KindFacts context J) := by
  rw [data_ontology.kind_axioms]
  obtain ⟨r1, run1, f1⟩ := number_axioms_spec.{w,x} context.kinds out
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some o1 =>
  obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
  obtain ⟨r2, run2, f2⟩ := kinds_axiom_spec.{w,x} context.kinds .String .Plain true o1
  cases r2 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some o2 =>
  obtain ⟨n2, c2, m2⟩ := f2 o2 rfl
  obtain ⟨r3, run3, f3⟩ := apart_axioms_spec.{w,x} context.kinds .Integer o2
  cases r3 with
  | none => exact ⟨none, by simp [run1, run2, run3], by simp⟩
  | some o3 =>
  obtain ⟨n3, c3, m3⟩ := f3 o3 rfl
  obtain ⟨r4, run4, f4⟩ := apart_axioms_spec.{w,x} context.kinds .Decimal o3
  cases r4 with
  | none => exact ⟨none, by simp [run1, run2, run3, run4], by simp⟩
  | some o4 =>
  obtain ⟨n4, c4, m4⟩ := f4 o4 rfl
  obtain ⟨r5, run5, f5⟩ := apart_axioms_spec.{w,x} context.kinds .Rational o4
  cases r5 with
  | none => exact ⟨none, by simp [run1, run2, run3, run4, run5], by simp⟩
  | some o5 =>
  obtain ⟨n5, c5, m5⟩ := f5 o5 rfl
  obtain ⟨r6, run6, f6⟩ := apart_axioms_spec.{w,x} context.kinds .Real o5
  cases r6 with
  | none => exact ⟨none, by simp [run1, run2, run3, run4, run5, run6], by simp⟩
  | some o6 =>
  obtain ⟨n6, c6, m6⟩ := f6 o6 rfl
  obtain ⟨r7, run7, f7⟩ := kinds_axiom_spec.{w,x} context.kinds .String .Boolean false o6
  cases r7 with
  | none => exact ⟨none, by simp [run1, run2, run3, run4, run5, run6, run7], by simp⟩
  | some o7 =>
  obtain ⟨n7, c7, m7⟩ := f7 o7 rfl
  obtain ⟨r8, run8, f8⟩ := kinds_axiom_spec.{w,x} context.kinds .Plain .Boolean false o7
  cases r8 with
  | none => exact ⟨none, by simp [run1, run2, run3, run4, run5, run6, run7, run8], by simp⟩
  | some o8 =>
  obtain ⟨n8, c8, m8⟩ := f8 o8 rfl
  obtain ⟨r9, run9, f9⟩ := truth_axiom_spec.{w,x} context good o8
  refine ⟨r9, by simp [run1, run2, run3, run4, run5, run6, run7, run8, run9], fun out' h => ?_⟩
  obtain ⟨known, n9, c9, m9⟩ := f9 out' h
  refine ⟨known, n1 ++ n2 ++ n3 ++ n4 ++ n5 ++ n6 ++ n7 ++ n8 ++ n9,
    by rw [c9, c8, c7, c6, c5, c4, c3, c2, c1]; simp, fun J => ?_⟩
  simp only [List.forall_mem_append, m1, m2, m3, m4, m5, m6, m7, m8, m9, ↓reduceIte, Bool.false_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2, a3, a4, a5, a6⟩, b⟩, c1, c2, c3⟩, d1, d2, d3⟩, e1, e2, e3⟩, f1, f2, f3⟩, g⟩, h⟩, i⟩
    exact ⟨a1, a2, a3, a4, a5, a6, b, c1, c2, c3, d1, d2, d3, e1, e2, e3, f1, f2, f3, g, h, i⟩
  · rintro ⟨a1, a2, a3, a4, a5, a6, b, c1, c2, c3, d1, d2, d3, e1, e2, e3, f1, f2, f3, g, h, i⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2, a3, a4, a5, a6⟩, b⟩, c1, c2, c3⟩, d1, d2, d3⟩, e1, e2, e3⟩, f1, f2, f3⟩, g⟩, h⟩, i⟩

/-! ### The literal values -/

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

theorem bit_correct (value position : Usize) :
    data_ontology.bit value position = .ok (value.val.testBit position.val) := by
  rw [data_ontology.bit]
  by_cases zero : position = 0#usize
  · subst zero
    obtain ⟨m, mRun, mValue⟩ := WP.spec_imp_exists (UScalar.rem_spec value (y := 2#usize) (by simp))
    have same : (m = 1#usize) ↔ value.val % 2 = 1 := by
      constructor
      · intro h
        have := congrArg UScalar.val h
        simp only [mValue] at this
        simpa using this
      · intro h
        apply UScalar.eq_of_val_eq
        simp only [mValue]
        simpa using h
    simp only [↓reduceIte, mRun, bind_ok, Nat.testBit_zero]
    simp [same]
  · have positive : position.val ≠ 0 := fun h => zero (UScalar.eq_of_val_eq (by simpa using h))
    obtain ⟨half, halfRun, halfValue⟩ := UScalar.div_spec value (y := 2#usize) (by simp)
    obtain ⟨prev, prevRun, prevValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := position) (y := 1#usize) (by simp; omega))
    have prevIs : prev.val = position.val - 1 := by simp at prevValue; exact prevValue.1
    have inner := bit_correct half prev
    simp only [zero, ↓reduceIte, halfRun, prevRun, bind_ok, inner]
    have split : position.val = prev.val + 1 := by omega
    rw [split, Nat.testBit_succ, halfValue]
    simp
termination_by position.val
decreasing_by
  have := prevValue
  simp at this
  omega

theorem bits_for_spec (count bits power : Usize) (isPower : power.val = 2 ^ bits.val) :
    ∃ b : Usize, data_ontology.bits_for count bits power = .ok b ∧ count.val ≤ 2 ^ b.val := by
  rw [data_ontology.bits_for]
  have powerBound : power.val ≤ Usize.max := by scalar_tac
  have fits : bits.val < Usize.max := by
    have : bits.val < 2 ^ bits.val := Nat.lt_two_pow_self
    omega
  have countBound : count.val ≤ Usize.max := by scalar_tac
  by_cases more : power.val < count.val
  · have more' : power < count := by simp only [UScalar.lt_equiv]; exact more
    obtain ⟨half, halfRun, halfValue⟩ := UScalar.div_spec core.num.Usize.MAX (y := 2#usize) (by simp)
    have halfIs : half.val = Usize.max / 2 := by rw [halfValue, usize_max_val]; rfl
    obtain ⟨b1, b1Run, b1Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := bits) (y := 1#usize) (by scalar_tac))
    have b1Is : b1.val = bits.val + 1 := by simpa using b1Value
    by_cases room : power.val ≤ half.val
    · have room' : power ≤ half := by simp only [UScalar.le_equiv]; exact room
      have bound : power.val * 2 ≤ Usize.max := by omega
      obtain ⟨p2, p2Run, p2Value⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := power) (y := 2#usize)
        (by simp only [UScalar.max_USize_eq]; simpa using bound))
      have p2Is : p2.val = power.val * 2 := by simpa using p2Value
      obtain ⟨b, run, le⟩ := bits_for_spec count b1 p2 (by rw [p2Is, b1Is, isPower, pow_succ])
      exact ⟨b, by simp [more, more', halfRun, room, room', b1Run, p2Run, run], le⟩
    · have room' : ¬ power ≤ half := by simp only [UScalar.le_equiv]; exact room
      refine ⟨b1, by simp [more, more', halfRun, room, room', b1Run], ?_⟩
      rw [b1Is, pow_succ, ← isPower]
      omega
  · have more' : ¬ power < count := by simp only [UScalar.lt_equiv]; exact more
    exact ⟨bits, by simp [more, more'], by omega⟩
termination_by count.val - power.val
decreasing_by
  have := p2Value
  simp at this
  have : 0 < power.val := by rw [isPower]; exact Nat.two_pow_pos _
  omega

/-- Distinct values below `2 ^ bits` differ at some bit below `bits`. -/
theorem bits_apart {i j bits : Nat} (hi : i < 2 ^ bits) (hj : j < 2 ^ bits) (apart : i ≠ j) :
    ∃ k < bits, i.testBit k ≠ j.testBit k := by
  by_contra none
  apply apart
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases low : k < bits
  · by_contra differ
    exact none ⟨k, low, differ⟩
  · have hik : i < 2 ^ k := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) (by omega))
    have hjk : j < 2 ^ k := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_eq_false_of_lt hik, Nat.testBit_eq_false_of_lt hjk]

theorem member_spec (c : ClassExpression) (positive : Bool) (a : Individual) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.member c positive a out = .ok res ∧ ∀ out', res = some out' →
      out'.val = out.val ++ [bare (.ClassAssertion (if positive then c else .ObjectComplementOf c) a)] := by
  rw [data_ontology.member]
  cases positive with
  | true =>
    obtain ⟨r, run, contents⟩ := push_spec out (.ClassAssertion c a)
    exact ⟨r, by simp [run], fun out' h => by rw [contents out' h]; simp [bare]⟩
  | false =>
    obtain ⟨r, run, contents⟩ := push_spec out (.ClassAssertion (.ObjectComplementOf c) a)
    exact ⟨r, by simp [run], fun out' h => by rw [contents out' h]; simp [bare]⟩

theorem member_holds (J : Interpretation Object' Value') (c : Class) (P : Prop) [Decidable P] (a : Individual) :
    satisfies J (.ClassAssertion (if P then .Class c else .ObjectComplementOf (.Class c)) a) ↔
      (J.classes c (individual J a) ↔ P) := by
  by_cases hp : P <;> simp [hp, satisfies, classDenote]

theorem kind_member_spec (context : data_ontology.Context)
    (canonical : ∀ v ∈ context.values.val, Rowl.Datatypes.Canonical v) (k : datatypes.Kind) (index : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.kind_member context k index out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ y ∈ new, satisfies J y.axiom) ↔ (Used context.kinds k = true → ∀ (h : index.val < context.values.val.length),
          (J.classes (kindClass k) (J.namedIndividuals (valueIndividual index)) ↔
            InKind context.values.val[index.val] k))) := by
  rw [data_ontology.kind_member, used_eq]
  by_cases used : Used context.kinds k = true
  · by_cases inside : index.val < context.values.val.length
    · have lookup : context.values.index_usize index = .ok context.values.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      obtain ⟨r, run, contents⟩ := member_spec (.Class (kindClass k))
        (decide (InKind context.values.val[index.val] k)) (.Named (valueIndividual index)) out
      refine ⟨r, by simp [used, UScalar.lt_equiv, inside, kind_class_eq, alloc.vec.Vec.index_slice_index, lookup,
        Rowl.Datatypes.in_kind_correct _ (canonical _ (List.getElem_mem inside)), value_individual_eq, run],
        fun out' h => ⟨_, contents out' h, fun J => ?_⟩⟩
      simp only [List.mem_singleton, forall_eq, bare, decide_eq_true_eq]
      rw [member_holds]
      exact ⟨fun holds _ _ => holds, fun holds => holds used inside⟩
    · refine ⟨some out, by simp [used, UScalar.lt_equiv, inside], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
      simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
      intro _ h
      exact absurd h inside
  · refine ⟨some out, by simp [used], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp [used]

theorem bit_members_spec (index position bits : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.bit_members index position bits out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ y ∈ new, satisfies J y.axiom) ↔ ∀ j : Usize, position.val ≤ j.val → j.val < bits.val →
          (J.classes (bitClass j) (J.namedIndividuals (valueIndividual index)) ↔ index.val.testBit j.val = true)) := by
  rw [data_ontology.bit_members]
  by_cases inside : position.val < bits.val
  · have inside' : position < bits := by simp only [UScalar.lt_equiv]; exact inside
    obtain ⟨r1, run1, contents1⟩ := member_spec (.Class (bitClass position))
      (index.val.testBit position.val) (.Named (valueIndividual index)) out
    cases r1 with
    | none => exact ⟨none, by simp [inside', bit_class_eq, bit_correct, value_individual_eq, run1], by simp⟩
    | some out1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := position) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = position.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := bit_members_spec index next bits out1
      refine ⟨rest, by simp [inside', bit_class_eq, bit_correct, value_individual_eq, run1, advance, restRun],
        fun out' h => ?_⟩
      obtain ⟨new, c, meaning⟩ := restFacts out' h
      refine ⟨bare (.ClassAssertion (if index.val.testBit position.val = true then .Class (bitClass position)
          else .ObjectComplementOf (.Class (bitClass position))) (.Named (valueIndividual index))) :: new,
        by rw [c, contents1 out1 rfl]; simp, fun J => ?_⟩
      simp only [List.mem_cons, forall_eq_or_imp, meaning]
      simp only [bare]
      rw [member_holds]
      simp only [individual]
      rw [nextIndex]
      constructor
      · rintro ⟨here, rest⟩ j low high
        by_cases same : j.val = position.val
        · have := UScalar.eq_of_val_eq same
          subst this
          exact here
        · exact rest j (by omega) high
      · intro all
        exact ⟨all position (le_refl _) inside, fun j low high => all j (by omega) high⟩
  · have inside' : ¬ position < bits := by simp only [UScalar.lt_equiv]; exact inside
    refine ⟨some out, by simp [inside'], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    intro j low high
    omega
termination_by bits.val - position.val
decreasing_by omega

/-- What the axioms of a numeric literal value's cuts say: when numbers are
    ordered, its individual is in the class of every cut that contains its
    number and in no other cut's class. -/
def CutFact (context : data_ontology.Context) (J : Interpretation Object' Value') (i : Usize)
    (h : i.val < context.values.val.length) : Prop :=
  context.kinds.ordered = true → Rowl.Datatypes.IsNumber context.values.val[i.val] →
    ∀ (a : Usize) (ha : a.val < context.cuts.val.length),
      (J.classes (cutClass a) (J.namedIndividuals (valueIndividual i)) ↔
        Rowl.Regions.InCut context.cuts.val[a.val] (Rowl.Datatypes.numValue context.values.val[i.val]))

theorem cut_unique {context : data_ontology.Context} (good : Good context) {a b : Usize}
    (ha : a.val < context.cuts.val.length) (hb : b.val < context.cuts.val.length)
    (same : context.cuts.val[a.val] = context.cuts.val[b.val]) : a = b :=
  UScalar.eq_of_val_eq ((List.Nodup.getElem_inj_iff good.2.2.2.1.2).mp same)

/-- The memberships of a numeric literal value in the classes of the cuts from
    `cut` on. -/
theorem cut_memberships_spec (context : data_ontology.Context) (fine : FineCuts context.cuts.val) (index : Usize)
    (h : index.val < context.values.val.length) (cv : Rowl.Datatypes.CanonicalNumeric context.values.val[index.val])
    (wv : Rowl.Datatypes.digitWidth context.values.val[index.val] < Usize.max / 8) (cut : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.cut_memberships context index cut out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ y ∈ new, satisfies J y.axiom) ↔ ∀ (a : Usize) (ha : a.val < context.cuts.val.length), cut.val ≤ a.val →
          (J.classes (cutClass a) (J.namedIndividuals (valueIndividual index)) ↔
            Rowl.Regions.InCut context.cuts.val[a.val] (Rowl.Datatypes.numValue context.values.val[index.val]))) := by
  rw [data_ontology.cut_memberships]
  by_cases inside : cut.val < context.cuts.val.length
  · have lookupC : context.cuts.index_usize cut = .ok context.cuts.val[cut.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have lookupV : context.values.index_usize index = .ok context.values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    have fc := Rowl.Regions.fine_at fine inside
    rw [Rowl.Regions.cutAt_eq _ _ inside] at fc
    have inCut := Rowl.Regions.in_cut_correct context.cuts.val[cut.val] fc context.values.val[index.val] cv wv
    obtain ⟨r1, run1, c1⟩ := member_spec (.Class (cutClass cut))
      (decide (Rowl.Regions.InCut context.cuts.val[cut.val] (Rowl.Datatypes.numValue context.values.val[index.val])))
      (.Named (valueIndividual index)) out
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, h, inside, cut_class_eq, alloc.vec.Vec.index_slice_index,
        lookupC, lookupV, inCut, value_individual_eq, run1], by simp⟩
    | some o1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := cut) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = cut.val + 1 := by simpa using nextValue
      obtain ⟨r2, run2, f2⟩ := cut_memberships_spec context fine index h cv wv next o1
      refine ⟨r2, by simp [UScalar.lt_equiv, h, inside, cut_class_eq, alloc.vec.Vec.index_slice_index,
        lookupC, lookupV, inCut, value_individual_eq, run1, advance, run2], fun out' hr => ?_⟩
      obtain ⟨n2, c2, m2⟩ := f2 out' hr
      refine ⟨bare (.ClassAssertion (if decide (Rowl.Regions.InCut context.cuts.val[cut.val]
          (Rowl.Datatypes.numValue context.values.val[index.val])) = true then .Class (cutClass cut)
          else .ObjectComplementOf (.Class (cutClass cut))) (.Named (valueIndividual index))) :: n2,
        by rw [c2, c1 o1 rfl]; simp, fun J => ?_⟩
      simp only [List.mem_cons, forall_eq_or_imp, m2 J, nextIndex]
      have here := member_holds J (cutClass cut)
        (Rowl.Regions.InCut context.cuts.val[cut.val] (Rowl.Datatypes.numValue context.values.val[index.val]))
        (.Named (valueIndividual index))
      simp only [decide_eq_true_eq, bare] at here ⊢
      rw [here]
      simp only [individual]
      constructor
      · rintro ⟨first, rest⟩ a ha low
        by_cases same : a = cut
        · subst same; exact first
        · have : a.val ≠ cut.val := fun e => same (UScalar.eq_of_val_eq e)
          exact rest a ha (by omega)
      · intro all
        exact ⟨all cut inside le_rfl, fun a ha low => all a ha (by omega)⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, h, inside], fun out' hr => ⟨[], by cases hr; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    intro a ha low
    omega
termination_by context.cuts.val.length - cut.val
decreasing_by omega

theorem cut_members_spec (context : data_ontology.Context) (good : Good context) (fine : FineCuts context.cuts.val)
    (fit : ValuesFit context) (index : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.cut_members context index out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ y ∈ new, satisfies J y.axiom) ↔ ∀ (h : index.val < context.values.val.length), CutFact context J index h) := by
  rw [data_ontology.cut_members]
  by_cases ready : context.kinds.ordered = true ∧ index.val < context.values.val.length
  · have inside := ready.2
    have lookup : context.values.index_usize index = .ok context.values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases number : Rowl.Datatypes.IsNumber context.values.val[index.val]
    · have member := List.getElem_mem inside
      have cv := canonical_numeric (good.1.1 _ member) number
      obtain ⟨r, run, f⟩ := cut_memberships_spec context fine index inside cv (fit _ member number) 0#usize out
      refine ⟨r, by simp [UScalar.lt_equiv, ready, alloc.vec.Vec.index_slice_index, lookup,
        Rowl.Datatypes.numeric_correct, number, run], fun out' hr => ?_⟩
      obtain ⟨new, c, m⟩ := f out' hr
      refine ⟨new, c, fun J => ?_⟩
      rw [m J]
      constructor
      · intro all _ _ _ a ha
        exact all a ha (by simp)
      · intro holds a ha _
        exact holds inside ready.1 number a ha
    · refine ⟨some out, by simp [UScalar.lt_equiv, ready, alloc.vec.Vec.index_slice_index, lookup,
        Rowl.Datatypes.numeric_correct, number], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
      simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
      intro _ _ isNumber
      exact absurd isNumber number
  · refine ⟨some out, ?_, fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    · by_cases ordered : context.kinds.ordered = true
      · have outside : ¬ index.val < context.values.val.length := fun h => ready ⟨ordered, h⟩
        simp [UScalar.lt_equiv, ordered, outside]
      · simp [ordered]
    · simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
      intro h ordered
      exact absurd ⟨ordered, h⟩ ready

theorem number_members_spec (context : data_ontology.Context) (good : Good context) (fine : FineCuts context.cuts.val)
    (fit : ValuesFit context) (index : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.number_members context index out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ y ∈ new, satisfies J y.axiom) ↔
          (Used context.kinds .Rational = true → ∀ (h : index.val < context.values.val.length),
            (J.classes (kindClass .Rational) (J.namedIndividuals (valueIndividual index)) ↔
              InKind context.values.val[index.val] .Rational)) ∧
          (Used context.kinds .Real = true → ∀ (h : index.val < context.values.val.length),
            (J.classes (kindClass .Real) (J.namedIndividuals (valueIndividual index)) ↔
              InKind context.values.val[index.val] .Real)) ∧
          ∀ (h : index.val < context.values.val.length), CutFact context J index h) := by
  rw [data_ontology.number_members]
  obtain ⟨r1, run1, f1⟩ := kind_member_spec.{w,x} context good.1.1 .Rational index out
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some o1 =>
  obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
  obtain ⟨r2, run2, f2⟩ := kind_member_spec.{w,x} context good.1.1 .Real index o1
  cases r2 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some o2 =>
  obtain ⟨n2, c2, m2⟩ := f2 o2 rfl
  obtain ⟨r3, run3, f3⟩ := cut_members_spec.{w,x} context good fine fit index o2
  refine ⟨r3, by simp [run1, run2, run3], fun out' h => ?_⟩
  obtain ⟨n3, c3, m3⟩ := f3 out' h
  refine ⟨n1 ++ n2 ++ n3, by rw [c3, c2, c1]; simp, fun J => ?_⟩
  simp only [List.forall_mem_append, m1, m2, m3]
  tauto

/-- What the axioms of one literal value say: its individual is a data node,
    in the classes of the kinds in use its value is in, with the bit classes
    of its index, and in the cuts of its own number. -/
def ValueFact (context : data_ontology.Context) (bits : Usize) (J : Interpretation Object' Value') (i : Usize)
    (h : i.val < context.values.val.length) : Prop :=
  J.classes dataClass (J.namedIndividuals (valueIndividual i)) ∧
  (∀ k, Used context.kinds k = true →
    (J.classes (kindClass k) (J.namedIndividuals (valueIndividual i)) ↔ InKind context.values.val[i.val] k)) ∧
  (∀ j : Usize, j.val < bits.val →
    (J.classes (bitClass j) (J.namedIndividuals (valueIndividual i)) ↔ i.val.testBit j.val = true)) ∧
  CutFact context J i h

theorem value_axioms_spec (context : data_ontology.Context) (good : Good context) (fine : FineCuts context.cuts.val)
    (fit : ValuesFit context) (index bits : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.value_axioms context index bits out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
        ((∀ y ∈ new, satisfies J y.axiom) ↔
          ∀ (i : Usize), index.val ≤ i.val → ∀ (h : i.val < context.values.val.length), ValueFact context bits J i h) := by
  have canonical := good.1.1
  rw [data_ontology.value_axioms]
  by_cases inside : index.val < context.values.val.length
  · have inside' : index < alloc.vec.Vec.len context.values := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    obtain ⟨r0, run0, contents0⟩ := push_spec out (.ClassAssertion (.Class dataClass) (.Named (valueIndividual index)))
    cases r0 with
    | none => exact ⟨none, by simp [inside', data_class_eq, value_individual_eq, run0], by simp⟩
    | some o0 =>
    obtain ⟨r1, run1, f1⟩ := kind_member_spec.{w,x} context canonical .Integer index o0
    cases r1 with
    | none => exact ⟨none, by simp [inside', data_class_eq, value_individual_eq, run0, run1], by simp⟩
    | some o1 =>
    obtain ⟨r2, run2, f2⟩ := kind_member_spec.{w,x} context canonical .Decimal index o1
    cases r2 with
    | none => exact ⟨none, by simp [inside', data_class_eq, value_individual_eq, run0, run1, run2], by simp⟩
    | some o2 =>
    obtain ⟨r3, run3, f3⟩ := kind_member_spec.{w,x} context canonical .String index o2
    cases r3 with
    | none => exact ⟨none, by simp [inside', data_class_eq, value_individual_eq, run0, run1, run2, run3], by simp⟩
    | some o3 =>
    obtain ⟨r4, run4, f4⟩ := kind_member_spec.{w,x} context canonical .Plain index o3
    cases r4 with
    | none =>
      exact ⟨none, by simp [inside', data_class_eq, value_individual_eq, run0, run1, run2, run3, run4], by simp⟩
    | some o4 =>
    obtain ⟨r5, run5, f5⟩ := kind_member_spec.{w,x} context canonical .Boolean index o4
    cases r5 with
    | none =>
      exact ⟨none, by simp [inside', data_class_eq, value_individual_eq, run0, run1, run2, run3, run4, run5],
        by simp⟩
    | some o5 =>
    obtain ⟨r6, run6, f6⟩ := number_members_spec.{w,x} context good fine fit index o5
    cases r6 with
    | none =>
      exact ⟨none, by simp [inside', data_class_eq, value_individual_eq, run0, run1, run2, run3, run4, run5, run6],
        by simp⟩
    | some o6 =>
    obtain ⟨r7, run7, f7⟩ := bit_members_spec.{w,x} index 0#usize bits o6
    cases r7 with
    | none =>
      exact ⟨none, by simp [inside', data_class_eq, value_individual_eq, run0, run1, run2, run3, run4, run5, run6,
        run7], by simp⟩
    | some o7 =>
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨rest, restRun, restFacts⟩ := value_axioms_spec context good fine fit next bits o7
    refine ⟨rest, by simp [inside', data_class_eq, value_individual_eq, run0, run1, run2, run3, run4, run5, run6,
      run7, advance, restRun], fun out' h => ?_⟩
    obtain ⟨n1, c1, m1⟩ := f1 o1 rfl
    obtain ⟨n2, c2, m2⟩ := f2 o2 rfl
    obtain ⟨n3, c3, m3⟩ := f3 o3 rfl
    obtain ⟨n4, c4, m4⟩ := f4 o4 rfl
    obtain ⟨n5, c5, m5⟩ := f5 o5 rfl
    obtain ⟨n6, c6, m6⟩ := f6 o6 rfl
    obtain ⟨n7, c7, m7⟩ := f7 o7 rfl
    obtain ⟨n8, c8, m8⟩ := restFacts out' h
    refine ⟨bare (.ClassAssertion (.Class dataClass) (.Named (valueIndividual index))) ::
      (n1 ++ n2 ++ n3 ++ n4 ++ n5 ++ n6 ++ n7 ++ n8),
      by rw [c8, c7, c6, c5, c4, c3, c2, c1, contents0 o0 rfl]; simp [bare], fun J => ?_⟩
    simp only [List.mem_cons, forall_eq_or_imp, List.forall_mem_append, m1, m2, m3, m4, m5, m6, m7, m8,
      zero_val, Nat.zero_le, true_implies]
    simp only [bare, satisfies, classDenote, individual]
    rw [nextIndex]
    constructor
    · rintro ⟨data, ⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, ⟨k6, k7, cutsHere⟩⟩, bitsHere⟩, rest⟩ i low hi
      by_cases same : i.val = index.val
      · have := UScalar.eq_of_val_eq same
        subst this
        refine ⟨data, fun k used => ?_, fun j high => bitsHere j high, cutsHere hi⟩
        cases k
        · exact k1 used hi
        · exact k2 used hi
        · exact k3 used hi
        · exact k4 used hi
        · exact k5 used hi
        · exact k7 used hi
        · exact k6 used hi
        all_goals simp [Used] at used
      · exact rest i (by omega) hi
    · intro all
      have here := all index (le_refl _) inside
      exact ⟨here.1, ⟨⟨⟨⟨⟨⟨fun used _ => here.2.1 _ used, fun used _ => here.2.1 _ used⟩,
        fun used _ => here.2.1 _ used⟩, fun used _ => here.2.1 _ used⟩, fun used _ => here.2.1 _ used⟩,
        ⟨fun used _ => here.2.1 _ used, fun used _ => here.2.1 _ used, fun h => here.2.2.2⟩⟩,
        fun j high => here.2.2.1 j high⟩, fun i low hi => all i (by omega) hi⟩
  · have inside' : ¬ index < alloc.vec.Vec.len context.values := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    refine ⟨some out, by simp [inside'], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
    simp only [List.not_mem_nil, false_imp_iff, implies_true, true_iff]
    intro i low hi
    omega
termination_by context.values.val.length - index.val
decreasing_by omega

/-! ### The whole encoding -/

/-- What the encoding's own axioms say of an interpretation, for the
    capacity of the counts of data restrictions and the order of the cuts. -/
structure Frame (context : data_ontology.Context) (capacity : Nat) (bits : Usize) (order : List Usize)
    (J : Interpretation Object' Value') : Prop where
  roles : ∀ r ∈ context.roles.val, ∀ y y', J.objectProperties r y y' →
    ¬ J.classes dataClass y ∧ ¬ J.classes dataClass y'
  data : ∀ p ∈ context.data.val, ∀ role, data_ontology.data_role context p = .ok (some role) →
    ∀ y y', objectRelation J role y y' → ¬ J.classes dataClass y ∧ J.classes dataClass y'
  kinds : KindFacts context J
  regions : RegionFacts context capacity order J
  values : ∀ (i : Usize) (h : i.val < context.values.val.length), ValueFact context bits J i h
  object : ¬ J.classes dataClass (J.namedIndividuals objectIndividual)

/-- The encoding of a closure in a context: what its axioms become, and the
    encoding's own axioms, with enough bit classes to tell the literal values
    apart, a role for every data property of the context, and, when numbers are
    ordered, the cuts in order; the context's cuts can be ordered and every
    number among its literal values can be compared with them. -/
theorem encode_meaning (context : data_ontology.Context) (good : Good context) (capacity : Usize)
    (capSmall : capacity.val < Usize.max / 16) (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, data_ontology.encode context capacity items = .ok res ∧ ∀ enc, res = some enc →
      FineCuts context.cuts.val ∧ ValuesFit context ∧
      ∃ (new : List AnnotatedAxiom) (bits : Usize) (order : List Usize), ItemsMeans.{u,v,w,x} context items.val new ∧
        context.values.val.length ≤ 2 ^ bits.val ∧
        (context.kinds.ordered = true → Ordered context.cuts.val (order.map (·.val)) ∧ PointsNamed context order 1) ∧
        (∀ p ∈ context.data.val, ∃ role, data_ontology.data_role context p = .ok (some role)) ∧
        TruthsKnown context ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ enc.val, satisfies J b.axiom) ↔
            (∀ b ∈ new, satisfies J b.axiom) ∧ Frame context capacity.val bits order J) := by
  rw [data_ontology.encode]
  obtain ⟨ok, okRun, okFacts⟩ := encodable_spec context good
  cases ok with
  | false => exact ⟨none, by simp [okRun], by simp⟩
  | true =>
  obtain ⟨fine, valuesFit⟩ := okFacts rfl
  obtain ⟨r1, run1, f1⟩ := encode_items_meaning.{u,v,w,x} context items 0#usize (alloc.vec.Vec.new AnnotatedAxiom)
  cases r1 with
  | none => exact ⟨none, by simp [okRun, run1], by simp⟩
  | some o1 =>
  obtain ⟨new, c1, m1⟩ := f1 o1 rfl
  obtain ⟨r2, run2, f2⟩ := role_axioms_spec.{w,x} context 0#usize o1
  cases r2 with
  | none => exact ⟨none, by simp [okRun, run1, run2], by simp⟩
  | some o2 =>
  obtain ⟨n2, c2, m2⟩ := f2 o2 rfl
  obtain ⟨r3, run3, f3⟩ := data_axioms_spec.{w,x} context 0#usize o2
  cases r3 with
  | none => exact ⟨none, by simp [okRun, run1, run2, run3], by simp⟩
  | some o3 =>
  obtain ⟨roles3, n3, c3, m3⟩ := f3 o3 rfl
  obtain ⟨r4, run4, f4⟩ := kind_axioms_spec.{w,x} context good o3
  cases r4 with
  | none => exact ⟨none, by simp [okRun, run1, run2, run3, run4], by simp⟩
  | some o4 =>
  obtain ⟨known, n4, c4, m4⟩ := f4 o4 rfl
  obtain ⟨r5, run5, f5⟩ := region_axioms_spec.{w,x} context good fine valuesFit capacity capSmall o4
  cases r5 with
  | none => exact ⟨none, by simp [okRun, run1, run2, run3, run4, run5], by simp⟩
  | some o5 =>
  obtain ⟨order, sorted, n5, c5, m5⟩ := f5 o5 rfl
  obtain ⟨bits, bitsRun, bitsLe⟩ := bits_for_spec (alloc.vec.Vec.len context.values) 0#usize 1#usize (by simp)
  obtain ⟨r6, run6, f6⟩ := value_axioms_spec.{w,x} context good fine valuesFit 0#usize bits o5
  cases r6 with
  | none => exact ⟨none, by simp [okRun, run1, run2, run3, run4, run5, bitsRun, run6], by simp⟩
  | some o6 =>
  obtain ⟨n6, c6, m6⟩ := f6 o6 rfl
  obtain ⟨r7, run7, c7⟩ := push_spec o6
    (.ClassAssertion (.ObjectComplementOf (.Class dataClass)) (.Named objectIndividual))
  refine ⟨r7, by simp [okRun, run1, run2, run3, run4, run5, bitsRun, run6, object_class_eq, object_individual_eq,
    run7], fun enc h => ?_⟩
  simp only [zero_val, List.drop_zero] at m1 roles3 m2 m3
  refine ⟨fine, valuesFit, new, bits, order, m1, by simpa using bitsLe, sorted, roles3, known, fun J => ?_⟩
  rw [c7 enc h, c6, c5, c4, c3, c2, c1]
  simp only [new_val, List.nil_append, List.forall_mem_append, m2 J, m3 J, m4 J, m5 J, m6 J, zero_val, Nat.zero_le,
    true_implies]
  simp only [List.mem_singleton, forall_eq, bare, satisfies, classDenote, individual]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨items', roles⟩, data⟩, kinds⟩, regions⟩, values⟩, object⟩
    exact ⟨items', ⟨roles, fun p mem role run y y' rel => data p mem role run y y' rel, kinds, regions, values,
      object⟩⟩
  · rintro ⟨items', frame⟩
    exact ⟨⟨⟨⟨⟨⟨items', frame.roles⟩, frame.data⟩, frame.kinds⟩, frame.regions⟩, frame.values⟩, frame.object⟩

/-- Literal values at distinct indices have distinct individuals in every
    interpretation of the encoding's own axioms. -/
theorem value_individuals_apart {context : data_ontology.Context} {capacity : Nat} {bits : Usize}
    {order : List Usize} {J : Interpretation Object' Value'} (frame : Frame context capacity bits order J) (enough : context.values.val.length ≤ 2 ^ bits.val) (i j : Usize)
    (hi : i.val < context.values.val.length) (hj : j.val < context.values.val.length) (apart : i ≠ j) :
    J.namedIndividuals (valueIndividual i) ≠ J.namedIndividuals (valueIndividual j) := by
  intro same
  have apart' : i.val ≠ j.val := fun h => apart (UScalar.eq_of_val_eq h)
  obtain ⟨k, low, differ⟩ := bits_apart (lt_of_lt_of_le hi enough) (lt_of_lt_of_le hj enough) apart'
  have kSmall : k < Usize.max := by
    have : bits.val ≤ Usize.max := by scalar_tac
    omega
  have lt : k < 2 ^ UScalarTy.Usize.numBits := by
    have := Usize.max_def
    have pos : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
    simp only [Usize.numBits] at this
    omega
  let position : Usize := Usize.ofNatCore k lt
  have positionIs : position.val = k := UScalar.ofNatCore_val_eq lt
  have bi := (frame.values i hi).2.2.1 position (by rw [positionIs]; exact low)
  have bj := (frame.values j hj).2.2.1 position (by rw [positionIs]; exact low)
  rw [same, bj, positionIs] at bi
  exact differ (by cases h1 : i.val.testBit k <;> cases h2 : j.val.testBit k <;> simp_all)

end Rowl.DataStructure
