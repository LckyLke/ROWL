import Rowl.DataStructure
import Rowl.ShiParts

/-!
The actual kernel functions of `key_ontology` that encode keys (`HasKey`) into
SROIQ axioms next to the data encoding of `data_ontology`, and what the axioms
they add say in an interpretation of the encoding.

The encoding marks the named individuals of the closure with the fresh class
`N` (`keyClass`, the name `[0, K]`). A key with one property `r`, when the
closure allows counting, becomes `N ⊑ ≤1 r⁻.(e' ⊓ N)` for the encoding `e'` of
its class expression (`countedAxiom`); every other key becomes the chains
`r ∘ mark ∘ r⁻ ⊑ share(r)` of its roles and, at every named individual `x`,
the assertion `x : ∀share(r₁).(¬N ⊔ ¬e' ⊔ {x} ⊔ ∀share(r₂)⁻.¬{x} ⊔ … ⊔
∀share(r₁)⁻.(¬{x} ⊔ ¬e'))`, whose last disjunct says that `x` is not in `e'`
(`SharedAt`), with `N ⊑ ∃mark.Self`. In a model of the encoding both say that
two named individuals in `e'` that share a named individual along every role
are equal (`KeyHoldsAt`); and in an interpretation in which `mark` relates
exactly the marked elements to themselves and `share(r)` exactly the pairs
that share a marked value along `r` (`Structured`), both hold when two elements
of `N` in `e'` that share a marked value along every role are equal
(`KeyHolds`). The whole encoding is described by `encode_meaning`.
-/
namespace Rowl.KeyEncoding
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.AlcOntology (RoleOf)
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.DataStructure
open Rowl.DataRegions (PointsNamed ValuesFit)
open Rowl.Regions (Ordered FineCuts)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe u v w x

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-! ### Keys -/

/-- A key axiom. -/
def IsKey : Axiom → Prop
  | .HasKey _ _ _ => True
  | _ => False

/-- The individuals of a key's class expression. -/
def keyIndividuals : Axiom → List Individual
  | .HasKey e _ _ => classIndividuals e
  | _ => []

/-- The data restrictions of a key's class expression. -/
def keyAtoms : Axiom → List (DataProperty × Option DataRange × Nat)
  | .HasKey e _ _ => classAtoms e
  | _ => []

/-- The individuals a closure names, those of its keys' class expressions
    included. -/
def closureIndividuals (items : List AnnotatedAxiom) : List Individual :=
  items.flatMap (fun i => axiomIndividuals i.axiom ++ keyIndividuals i.axiom)

/-- Whether a closure has a key. -/
def Keyed (items : List AnnotatedAxiom) : Prop := ∃ item ∈ items, IsKey item.axiom

/-- A vocabulary of a closure with keys: every named individual the closure
    names is one of its individuals, so it is named in every interpretation
    for the vocabulary. A closure without keys asks nothing of the vocabulary. -/
def NamesKeyed (V : Vocabulary) (items : List AnnotatedAxiom) : Prop :=
  Keyed items → ∀ a : NamedIndividual, .Named a ∈ closureIndividuals items → V.individuals (.Named a)

/-- The axioms of a closure other than keys. -/
noncomputable def unkeyedItems (items : List AnnotatedAxiom) : List AnnotatedAxiom :=
  items.filter (fun i => ¬ IsKey i.axiom)

/-- The named individuals among some individuals. -/
def namesOf (nodes : List Individual) : List NamedIndividual :=
  nodes.filterMap (fun a => match a with
    | .Named n => some n
    | .Anonymous _ => none)

theorem mem_namesOf {nodes : List Individual} {n : NamedIndividual} : n ∈ namesOf nodes ↔ .Named n ∈ nodes := by
  simp only [namesOf, List.mem_filterMap]
  constructor
  · rintro ⟨a, mem, same⟩
    cases a with
    | Named m => simp only [Option.some.injEq] at same; subst same; exact mem
    | Anonymous _ => simp at same
  · intro mem
    exact ⟨_, mem, rfl⟩

theorem keyed_of_key {items : List AnnotatedAxiom} {item : AnnotatedAxiom} (mem : item ∈ items)
    {e : ClassExpression} {ops : alloc.vec.Vec ObjectPropertyExpression} {dps : alloc.vec.Vec DataProperty}
    (key : item.axiom = .HasKey e ops dps) : Keyed items :=
  ⟨item, mem, by rw [key]; trivial⟩

theorem is_key_correct (ax : Axiom) : ∃ b, key_ontology.is_key ax = .ok b ∧ (b = true ↔ IsKey ax) := by
  cases ax <;> simp [key_ontology.is_key, IsKey]

theorem has_keys_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    ∃ b, key_ontology.has_keys items index = .ok b ∧
      (b = true ↔ ∃ item ∈ items.val.drop index.val, IsKey item.axiom) := by
  rw [key_ontology.has_keys]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨b, run, iff⟩ := is_key_correct items.val[index.val].axiom
    cases b with
    | true =>
      refine ⟨true, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], ?_⟩
      rw [split]
      exact ⟨fun _ => ⟨_, List.mem_cons_self, iff.mp rfl⟩, fun _ => rfl⟩
    | false =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b', run', iff'⟩ := has_keys_correct items next
      refine ⟨b', by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, run'], ?_⟩
      rw [iff', split, nextIndex]
      constructor
      · rintro ⟨item, mem, key⟩
        exact ⟨item, List.mem_cons_of_mem _ mem, key⟩
      · rintro ⟨item, mem, key⟩
        rcases List.mem_cons.mp mem with rfl | later
        · exact absurd (iff.mpr key) (by simp)
        · exact ⟨item, later, key⟩
  · refine ⟨false, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show items.val.length ≤ index.val by omega)]
termination_by items.val.length - index.val
decreasing_by omega

theorem complex_axiom_runs (ax : Axiom) : ∃ b, key_ontology.complex_axiom ax = .ok b := by
  cases ax with
  | SubObjectPropertyOf sub _ => cases sub <;> exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

theorem complex_roles_runs (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    ∃ b, key_ontology.complex_roles items index = .ok b := by
  rw [key_ontology.complex_roles]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨b, run⟩ := complex_axiom_runs items.val[index.val].axiom
    cases b with
    | true => exact ⟨true, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run]⟩
    | false =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b', run'⟩ := complex_roles_runs items next
      exact ⟨b', by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, run']⟩
  · exact ⟨false, by simp [UScalar.lt_equiv, inside]⟩
termination_by items.val.length - index.val
decreasing_by omega

/-! ### The context -/

theorem key_context_good (context : data_ontology.Context) (ax : Axiom) (good : Good context) :
    ∃ r, key_ontology.key_context context ax = .ok r ∧ Good r := by
  cases ax with
  | HasKey e ops dps =>
    rw [key_ontology.key_context]
    obtain ⟨c1, run1, good1⟩ := class_context_good e context good
    obtain ⟨c2, run2, good2⟩ := roles_context_good c1 ops 0#usize good1
    obtain ⟨c3, run3, good3⟩ := data_list_context_good c2 dps 0#usize good2
    exact ⟨c3, by simp [run1, run2, run3], good3⟩
  | _ => exact ⟨context, by rw [key_ontology.key_context], good⟩

theorem keys_context_good (context : data_ontology.Context) (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize)
    (good : Good context) :
    ∃ r, key_ontology.keys_context context items index = .ok r ∧ Good r := by
  rw [key_ontology.keys_context]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨c, run, cGood⟩ := key_context_good context items.val[index.val].axiom good
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, rest, rGood⟩ := keys_context_good c items next cGood
    exact ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, rest], rGood⟩
  · exact ⟨context, by simp [UScalar.lt_equiv, inside], good⟩
termination_by items.val.length - index.val
decreasing_by omega

/-! ### The encoding's own names -/

/-- The name of the class `N` of the named elements. -/
def keyName : List U8 := [0#u8, 75#u8]
/-- The name of the role `mark` whose self loops mark the named elements. -/
def markName : List U8 := [0#u8, 75#u8, 82#u8]
/-- The name of the role `share(r)`: the pairs of elements that share a marked
    value along `r`. -/
def shareName : ObjectPropertyExpression → List U8
  | .Property p => 0#u8 :: 75#u8 :: 83#u8 :: 0#u8 :: p.iri.spelling.val
  | .Inverse p => 0#u8 :: 75#u8 :: 83#u8 :: 1#u8 :: p.iri.spelling.val

theorem shareName_injective {r s : ObjectPropertyExpression} (same : shareName r = shareName s) : r = s := by
  cases r with
  | Property p =>
    cases s with
    | Property q =>
      simp only [shareName, List.cons.injEq, true_and] at same
      rw [(Rowl.Tableau.property_eq_iff p q).mpr same]
    | Inverse q => simp [shareName] at same
  | Inverse p =>
    cases s with
    | Property q => simp [shareName] at same
    | Inverse q =>
      simp only [shareName, List.cons.injEq, true_and] at same
      rw [(Rowl.Tableau.property_eq_iff p q).mpr same]

theorem key_name_correct (rest : alloc.vec.Vec U8) (room : rest.val.length + 2 ≤ Usize.max) :
    ∃ v, key_ontology.key_name rest = .ok v ∧ v.val = 0#u8 :: 75#u8 :: rest.val := by
  rw [key_ontology.key_name]
  exact tagged_name_correct 75#u8 rest room

theorem named_class_correct : ∃ c : Class, key_ontology.named_class = .ok (.Class c) ∧ c.iri.spelling.val = keyName := by
  obtain ⟨v, run, value⟩ := key_name_correct (alloc.vec.Vec.new U8) (by simp [new_val]; scalar_tac)
  exact ⟨⟨⟨v⟩⟩, by simp [key_ontology.named_class, run], by simp [value, new_val, keyName]⟩

/-- The class `N` of the named elements. -/
noncomputable def keyClass : Class := Classical.choose named_class_correct

theorem named_class_eq : key_ontology.named_class = .ok (.Class keyClass) :=
  (Classical.choose_spec named_class_correct).1

theorem keyClass_name : keyClass.iri.spelling.val = keyName := (Classical.choose_spec named_class_correct).2

theorem mark_role_correct :
    ∃ p : ObjectProperty, key_ontology.mark_role = .ok (.Property p) ∧ p.iri.spelling.val = markName := by
  obtain ⟨rest, restRun, restValue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 82#u8 (by simp [new_val]; scalar_tac))
  obtain ⟨v, run, value⟩ := key_name_correct rest (by rw [restValue]; simp [new_val]; scalar_tac)
  exact ⟨⟨⟨v⟩⟩, by simp [key_ontology.mark_role, restRun, run], by simp [value, restValue, new_val, markName]⟩

/-- The role `mark` whose self loops mark the named elements. -/
noncomputable def markRole : ObjectProperty := Classical.choose mark_role_correct

theorem mark_role_eq : key_ontology.mark_role = .ok (.Property markRole) :=
  (Classical.choose_spec mark_role_correct).1

theorem markRole_name : markRole.iri.spelling.val = markName := (Classical.choose_spec mark_role_correct).2

theorem share_name_correct (p : ObjectProperty) (orientation : U8) :
    ∃ res, key_ontology.share_name p orientation = .ok res ∧
      ∀ q, res = some q → q.iri.spelling.val = 0#u8 :: 75#u8 :: 83#u8 :: orientation :: p.iri.spelling.val := by
  rw [key_ontology.share_name]
  obtain ⟨limit, limitRun, limitValue⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := core.num.Usize.MAX) (y := 4#usize) (by simp [usize_max_val]; scalar_tac))
  have limitIs : limit.val = Usize.max - 4 := by simp [usize_max_val] at limitValue; exact limitValue.1
  by_cases short : p.iri.spelling.val.length < Usize.max - 4
  · have short' : alloc.vec.Vec.len p.iri.spelling < limit := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, limitIs]; exact short
    obtain ⟨r1, run1, value1⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 83#u8 (by simp [new_val]; scalar_tac))
    obtain ⟨r2, run2, value2⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec r1 orientation (by rw [value1]; simp [new_val]; scalar_tac))
    obtain ⟨v, run, value⟩ := copy_after_correct p.iri.spelling 0#usize r2
      (by rw [value2, value1]; simp [new_val]; omega)
    obtain ⟨w, wRun, wValue⟩ := key_name_correct v (by rw [value, value2, value1]; simp [new_val]; omega)
    refine ⟨some ⟨⟨w⟩⟩, by simp [limitRun, limitIs, short, run1, run2, run, wRun], fun q h => ?_⟩
    cases h
    simp [wValue, value, value2, value1, new_val]
  · have notShort : ¬ alloc.vec.Vec.len p.iri.spelling < limit := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, limitIs]; exact short
    exact ⟨none, by simp [limitRun, limitIs, short], by simp⟩

theorem share_role_correct (r : ObjectPropertyExpression) :
    ∃ res, key_ontology.share_role r = .ok res ∧ ∀ q, res = some q → q.iri.spelling.val = shareName r := by
  cases r with
  | Property p =>
    obtain ⟨res, run, facts⟩ := share_name_correct p 0#u8
    exact ⟨res, by simp [key_ontology.share_role, run], fun q h => by rw [facts q h]; rfl⟩
  | Inverse p =>
    obtain ⟨res, run, facts⟩ := share_name_correct p 1#u8
    exact ⟨res, by simp [key_ontology.share_role, run], fun q h => by rw [facts q h]; rfl⟩


/-! ### What the axioms of the keys say -/

/-- The inverse of a role. -/
def inverseRole : ObjectPropertyExpression → ObjectPropertyExpression
  | .Property p => .Inverse p
  | .Inverse p => .Property p

theorem inverse_of_eq (r : ObjectPropertyExpression) : key_ontology.inverse_of r = .ok (inverseRole r) := by
  cases r <;> rfl

theorem not_eq (c : ClassExpression) : key_ontology.not c = .ok (.ObjectComplementOf c) := rfl

theorem nominal_eq (a : Individual) :
    key_ontology.nominal a = .ok (.ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩) := by
  simp [key_ontology.nominal, Rowl.Concepts.copy_individual_identity]

/-- A role of a data property in the data encoding. -/
def DataKeyRole (q : ObjectPropertyExpression) : Prop :=
  ∃ (p : DataProperty) (q' : ObjectProperty), q = .Property q' ∧ DataRoleOf p q'

section Meaning
variable {Object' : Type w} {Value' : Type x}

theorem inverse_relation (J : Interpretation Object' Value') (r : ObjectPropertyExpression) (y y' : Object') :
    objectRelation J (inverseRole r) y y' ↔ objectRelation J r y' y := by
  cases r <;> rfl

/-- `share(r)` relates two elements. -/
def Shares (J : Interpretation Object' Value') (r : ObjectPropertyExpression) (y y' : Object') : Prop :=
  ∃ p : ObjectProperty, p.iri.spelling.val = shareName r ∧ J.objectProperties p y y'

theorem shares_iff {J : Interpretation Object' Value'} {r : ObjectPropertyExpression} {p : ObjectProperty}
    (named : p.iri.spelling.val = shareName r) (y y' : Object') : J.objectProperties p y y' ↔ Shares J r y y' := by
  constructor
  · intro related; exact ⟨p, named, related⟩
  · rintro ⟨q, qNamed, related⟩
    have same : q = p := (Rowl.Tableau.property_eq_iff q p).mpr (qNamed.trans named.symm)
    rw [← same]; exact related

/-- In an interpretation of the encoding, the key holds for the named
    individuals `names`: two of them in `e'` that share one of them along every
    role of an object property and a data node along every role of a data
    property are equal. -/
def KeyHoldsAt (J : Interpretation Object' Value') (e' : ClassExpression) (roles datas : List ObjectPropertyExpression)
    (names : List NamedIndividual) : Prop :=
  ∀ a ∈ names, ∀ b ∈ names, classDenote J e' (J.namedIndividuals a) → classDenote J e' (J.namedIndividuals b) →
    (∀ r ∈ roles, ∃ c ∈ names, objectRelation J r (J.namedIndividuals a) (J.namedIndividuals c) ∧
      objectRelation J r (J.namedIndividuals b) (J.namedIndividuals c)) →
    (∀ q ∈ datas, ∃ z, J.classes dataClass z ∧ objectRelation J q (J.namedIndividuals a) z ∧
      objectRelation J q (J.namedIndividuals b) z) →
    J.namedIndividuals a = J.namedIndividuals b

/-- Two elements of `N` in `e'` that share a marked element along every role
    are equal. -/
def KeyHolds (J : Interpretation Object' Value') (e' : ClassExpression) (roles : List ObjectPropertyExpression)
    (marked : Object' → Prop) : Prop :=
  ∀ y y', J.classes keyClass y → J.classes keyClass y' → classDenote J e' y → classDenote J e' y' →
    (∀ r ∈ roles, ∃ z, marked z ∧ objectRelation J r y z ∧ objectRelation J r y' z) → y = y'

/-- `mark` relates exactly the marked elements to themselves, and `share(r)`
    exactly the pairs of elements that share a marked element along `r`, for
    every role that is not the encoding's own and every role of a data
    property. -/
def Structured (J : Interpretation Object' Value') (marked : Object' → Prop) : Prop :=
  (∀ y y', J.objectProperties markRole y y' ↔ y = y' ∧ marked y) ∧
  ∀ (r : ObjectPropertyExpression) (p : ObjectProperty), p.iri.spelling.val = shareName r →
    (¬ Reserved (RoleOf r).iri.spelling.val ∨ DataKeyRole r) → ∀ y y',
      (J.objectProperties p y y' ↔ ∃ z, marked z ∧ objectRelation J r y z ∧ objectRelation J r y' z)

/-- The counted axiom `N ⊑ ≤1 r⁻.(e' ⊓ N)` of a key with one role. -/
noncomputable def countedAxiom (e' : ClassExpression) (r : ObjectPropertyExpression) : Axiom :=
  .SubClassOf (.Class keyClass) (.ObjectMaxCardinality (.Succ .Zero) (inverseRole r)
    (some (.ObjectIntersectionOf ⟨e', .Class keyClass, alloc.vec.Vec.new ClassExpression⟩)))

theorem counted_holds (J : Interpretation Object' Value') (e' : ClassExpression) (r : ObjectPropertyExpression) :
    satisfies J (countedAxiom e' r) ↔ ∀ z, J.classes keyClass z → ∀ y y',
      objectRelation J r y z → classDenote J e' y → J.classes keyClass y →
      objectRelation J r y' z → classDenote J e' y' → J.classes keyClass y' → y = y' := by
  simp only [countedAxiom, satisfies]
  rw [forall_congr' fun z => imp_congr (by rw [classDenote]) Iff.rfl]
  apply forall_congr'; intro z
  apply imp_congr Iff.rfl
  rw [classDenote.eq_def]
  simp only [Rowl.Probes.naturalValue, Nat.zero_add]
  rw [Rowl.ShiParts.atMost_one_iff]
  simp only [inverse_relation, and_denote, classDenote]
  constructor
  · intro holds y y' ry ey ny ry' ey' ny'
    exact holds y y' ⟨ry, ey, ny⟩ ⟨ry', ey', ny'⟩
  · rintro holds y y' ⟨ry, ey, ny⟩ ⟨ry', ey', ny'⟩
    exact holds y y' ry ey ny ry' ey' ny'

/-- The counted axiom `D ⊑ ≤1 q⁻.(e' ⊓ N)` of a key with the role of one data
    property. -/
noncomputable def dataCountedAxiom (e' : ClassExpression) (q : ObjectPropertyExpression) : Axiom :=
  .SubClassOf (.Class dataClass) (.ObjectMaxCardinality (.Succ .Zero) (inverseRole q)
    (some (.ObjectIntersectionOf ⟨e', .Class keyClass, alloc.vec.Vec.new ClassExpression⟩)))

theorem data_counted_holds (J : Interpretation Object' Value') (e' : ClassExpression) (q : ObjectPropertyExpression) :
    satisfies J (dataCountedAxiom e' q) ↔ ∀ z, J.classes dataClass z → ∀ y y',
      objectRelation J q y z → classDenote J e' y → J.classes keyClass y →
      objectRelation J q y' z → classDenote J e' y' → J.classes keyClass y' → y = y' := by
  simp only [dataCountedAxiom, satisfies]
  rw [forall_congr' fun z => imp_congr (by rw [classDenote]) Iff.rfl]
  apply forall_congr'; intro z
  apply imp_congr Iff.rfl
  rw [classDenote.eq_def]
  simp only [Rowl.Probes.naturalValue, Nat.zero_add]
  rw [Rowl.ShiParts.atMost_one_iff]
  simp only [inverse_relation, and_denote, classDenote]
  constructor
  · intro holds y y' ry ey ny ry' ey' ny'
    exact holds y y' ⟨ry, ey, ny⟩ ⟨ry', ey', ny'⟩
  · rintro holds y y' ⟨ry, ey, ny⟩ ⟨ry', ey', ny'⟩
    exact holds y y' ry ey ny ry' ey' ny'

/-- The chain axiom `r ∘ mark ∘ r⁻ ⊑ p` holds. -/
def ChainHolds (J : Interpretation Object' Value') (r : ObjectPropertyExpression) (p : ObjectProperty) : Prop :=
  ∀ y z z' y', objectRelation J r y z → J.objectProperties markRole z z' → objectRelation J r y' z' →
    J.objectProperties p y y'

theorem chain_holds (J : Interpretation Object' Value') (r : ObjectPropertyExpression) (p : ObjectProperty)
    (rest : alloc.vec.Vec ObjectPropertyExpression) (restIs : rest.val = [inverseRole r]) :
    satisfies J (.SubObjectPropertyOf (.Chain ⟨r, .Property markRole, rest⟩) (.Property p)) ↔ ChainHolds J r p := by
  simp only [satisfies, subRelation, AtLeastTwo.elements, restIs, chainRelation, inverse_relation]
  simp only [objectRelation]
  constructor
  · intro holds y z z' y' ry mark ry'
    exact holds y y' ⟨z, ry, z', mark, y', ry', rfl⟩
  · rintro holds y y' ⟨z, ry, z', mark, y'', ry', rfl⟩
    exact holds y z z' y'' ry mark ry'

/-- The assertion of a key at a named individual `a` with the encoded class
    `e'`, the first share role `p0` and the other share roles `ps`. -/
def SharedHolds (J : Interpretation Object' Value') (e' : ClassExpression) (p0 : ObjectProperty)
    (ps : List ObjectProperty) (a : Object') : Prop :=
  classDenote J e' a → ∀ y, J.objectProperties p0 a y → J.classes keyClass y → classDenote J e' y →
    y = a ∨ ∃ p ∈ ps, ¬ J.objectProperties p a y

theorem nominal_denote (J : Interpretation Object' Value') (a : Individual) (y : Object') :
    classDenote J (.ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩) y ↔ individual J a = y := by
  rw [classDenote]; simp [NonEmpty.elements, new_val]

theorem or_denote (J : Interpretation Object' Value') (c d : ClassExpression) (y : Object') :
    classDenote J (.ObjectUnionOf ⟨c, d, alloc.vec.Vec.new ClassExpression⟩) y ↔
      classDenote J c y ∨ classDenote J d y := by
  rw [union_iff]; simp [AtLeastTwo.elements, new_val]

theorem complement_denote (J : Interpretation Object' Value') (c : ClassExpression) (y : Object') :
    classDenote J (.ObjectComplementOf c) y ↔ ¬ classDenote J c y := by
  rw [classDenote]

theorem class_denote (J : Interpretation Object' Value') (c : Class) (y : Object') :
    classDenote J (.Class c) y ↔ J.classes c y := by
  rw [classDenote]

/-- The disjuncts after `¬N` and `¬e'` of the assertion of a key at `a`: `{a}`,
    `∀p⁻.¬{a}` for every share role `p` of `ps`, and `∀p0⁻.(¬{a} ⊔ ¬e')`. -/
def sharedRest (e' : ClassExpression) (p0 : ObjectProperty) (ps : List ObjectProperty) (a : Individual) :
    List ClassExpression :=
  .ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩ ::
    (ps.map (fun p => .ObjectAllValuesFrom (.Inverse p)
      (.ObjectComplementOf (.ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩))) ++
    [.ObjectAllValuesFrom (.Inverse p0) (.ObjectUnionOf ⟨.ObjectComplementOf
      (.ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩), .ObjectComplementOf e', alloc.vec.Vec.new ClassExpression⟩)])

theorem exists_mem_shared {P : ClassExpression → Prop} {A B C D : ClassExpression}
    {f : ObjectProperty → ClassExpression} {ps : List ObjectProperty} :
    (∃ c ∈ A :: B :: C :: (ps.map f ++ [D]), P c) ↔ P A ∨ P B ∨ P C ∨ (∃ p ∈ ps, P (f p)) ∨ P D := by
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_singleton, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨c, (rfl | rfl | rfl | ⟨p, pMem, rfl⟩ | rfl), holds⟩
    · exact .inl holds
    · exact .inr (.inl holds)
    · exact .inr (.inr (.inl holds))
    · exact .inr (.inr (.inr (.inl ⟨p, pMem, holds⟩)))
    · exact .inr (.inr (.inr (.inr holds)))
  · rintro (h | h | h | ⟨p, pMem, h⟩ | h)
    · exact ⟨A, .inl rfl, h⟩
    · exact ⟨B, .inr (.inl rfl), h⟩
    · exact ⟨C, .inr (.inr (.inl rfl)), h⟩
    · exact ⟨f p, .inr (.inr (.inr (.inl ⟨p, pMem, rfl⟩))), h⟩
    · exact ⟨D, .inr (.inr (.inr (.inr rfl))), h⟩

theorem shared_holds (J : Interpretation Object' Value') (e' : ClassExpression) (p0 : ObjectProperty)
    (ps : List ObjectProperty) (a : Individual) (rest : alloc.vec.Vec ClassExpression)
    (restIs : rest.val = sharedRest e' p0 ps a) :
    satisfies J (.ClassAssertion (.ObjectAllValuesFrom (.Property p0)
      (.ObjectUnionOf ⟨.ObjectComplementOf (.Class keyClass), .ObjectComplementOf e', rest⟩)) a) ↔
      SharedHolds J e' p0 ps (individual J a) := by
  have apartIff : ∀ (p : ObjectProperty) y, classDenote J (.ObjectAllValuesFrom (.Inverse p)
      (.ObjectComplementOf (.ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩))) y ↔
      ¬ J.objectProperties p (individual J a) y := by
    intro p y
    rw [classDenote]
    simp only [objectRelation]
    constructor
    · intro h related
      have := h (individual J a) related
      rw [complement_denote, nominal_denote] at this
      exact this rfl
    · intro h z related
      rw [complement_denote, nominal_denote]
      rintro rfl
      exact h related
  have backIff : ∀ y, J.objectProperties p0 (individual J a) y →
      (classDenote J (.ObjectAllValuesFrom (.Inverse p0) (.ObjectUnionOf ⟨.ObjectComplementOf
        (.ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩), .ObjectComplementOf e', alloc.vec.Vec.new ClassExpression⟩)) y ↔
        ¬ classDenote J e' (individual J a)) := by
    intro y related
    rw [classDenote]
    simp only [objectRelation]
    constructor
    · intro h inE
      have := h (individual J a) related
      rw [or_denote, complement_denote, complement_denote, nominal_denote] at this
      rcases this with notA | notE
      · exact notA rfl
      · exact notE inE
    · intro notE z _
      rw [or_denote, complement_denote, complement_denote, nominal_denote]
      by_cases same : individual J a = z
      · right; rw [← same]; exact notE
      · left; exact same
  have unionIff : ∀ y, J.objectProperties p0 (individual J a) y →
      (classDenote J (.ObjectUnionOf ⟨.ObjectComplementOf (.Class keyClass), .ObjectComplementOf e', rest⟩) y ↔
        ¬ J.classes keyClass y ∨ ¬ classDenote J e' y ∨ individual J a = y ∨
          (∃ p ∈ ps, ¬ J.objectProperties p (individual J a) y) ∨ ¬ classDenote J e' (individual J a)) := by
    intro y related
    rw [union_iff]
    simp only [AtLeastTwo.elements, restIs, sharedRest]
    rw [exists_mem_shared]
    simp only [complement_denote, class_denote, nominal_denote, apartIff, backIff y related]
  simp only [satisfies, SharedHolds]
  rw [classDenote]
  simp only [objectRelation]
  constructor
  · intro holds inE y related inN inE'
    rcases (unionIff y related).mp (holds y related) with notN | notE | same | apart | notA
    · exact absurd inN notN
    · exact absurd inE' notE
    · exact .inl same.symm
    · exact .inr apart
    · exact absurd inE notA
  · intro holds y related
    rw [unionIff y related]
    by_cases inE : classDenote J e' (individual J a)
    · by_cases inN : J.classes keyClass y
      · by_cases inE' : classDenote J e' y
        · rcases holds inE y related inN inE' with same | apart
          · exact .inr (.inr (.inl same.symm))
          · exact .inr (.inr (.inr (.inl apart)))
        · exact .inr (.inl inE')
      · exact .inl inN
    · exact .inr (.inr (.inr (.inr inE)))

end Meaning


/-! ### The axioms of the keys -/

/-- A node of the encoding: a named individual in `N`, an anonymous one no data
    node. -/
def NodeHeld {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') : Individual → Prop
  | .Named n => J.classes keyClass (J.namedIndividuals n)
  | .Anonymous b => ¬ J.classes dataClass (J.anonymousIndividuals b)

theorem named_assertion_spec (a : Individual) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.named_assertion a out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ Plain a ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ NodeHeld J a) := by
  rw [key_ontology.named_assertion]
  obtain ⟨res, run, facts⟩ := object_individual_of_correct a
  cases res with
  | none => exact ⟨none, by simp [run], by simp⟩
  | some copy =>
    obtain ⟨same, plain⟩ := object_individual_of_some run
    subst same
    cases copy with
    | Named n =>
      obtain ⟨r, pushRun, contents⟩ := push_spec out (.ClassAssertion (.Class keyClass) (.Named n))
      refine ⟨r, by simp [run, named_class_eq, pushRun], fun out' h => ⟨[bare (.ClassAssertion (.Class keyClass)
        (.Named n))], by rw [contents out' h]; rfl, plain, fun J => ?_⟩⟩
      simp [bare, satisfies, classDenote, individual, NodeHeld]
    | Anonymous b =>
      obtain ⟨r, pushRun, contents⟩ := push_spec out
        (.ClassAssertion (.ObjectComplementOf (.Class dataClass)) (.Anonymous b))
      refine ⟨r, by simp [run, object_class_eq, pushRun], fun out' h => ⟨[bare (.ClassAssertion
        (.ObjectComplementOf (.Class dataClass)) (.Anonymous b))], by rw [contents out' h]; rfl, plain, fun J => ?_⟩⟩
      simp [bare, satisfies, classDenote, individual, NodeHeld]

theorem named_assertions_spec (nodes : alloc.vec.Vec Individual) (index : Usize) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.named_assertions nodes index out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ (∀ a ∈ nodes.val.drop index.val, Plain a) ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ a ∈ nodes.val.drop index.val, NodeHeld J a) := by
  rw [key_ontology.named_assertions]
  by_cases inside : index.val < nodes.val.length
  · have lookup : nodes.index_usize index = .ok nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, facts1⟩ := named_assertion_spec.{w,x} nodes.val[index.val] out
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some out1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := named_assertions_spec nodes next out1
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance,
        restRun], fun out' h => ?_⟩
      obtain ⟨new2, c2, plain2, means2⟩ := restFacts out' h
      obtain ⟨new1, c1, plain1, means1⟩ := facts1 out1 rfl
      rw [nextIndex] at plain2 means2
      refine ⟨new1 ++ new2, by rw [c2, c1, List.append_assoc], ?_, fun J => ?_⟩
      · rw [split]
        intro a mem
        rcases List.mem_cons.mp mem with rfl | later
        · exact plain1
        · exact plain2 a later
      · rw [split]
        simp only [List.forall_mem_append, means1 J, means2 J, List.forall_mem_cons]
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], by cases h; simp, ?_, fun J => ?_⟩⟩
    · simp [List.drop_eq_nil_iff.mpr (show nodes.val.length ≤ index.val by omega)]
    · simp [List.drop_eq_nil_iff.mpr (show nodes.val.length ≤ index.val by omega)]
termination_by nodes.val.length - index.val
decreasing_by omega

theorem object_role_some {context : data_ontology.Context} {r r' : ObjectPropertyExpression}
    (run : data_ontology.object_role context r = .ok (some r')) :
    r' = r ∧ ¬ Reserved (RoleOf r).iri.spelling.val ∧ (RoleOf r = topObject ∨ RoleOf r ∈ context.roles.val) := by
  obtain ⟨res, run', facts⟩ := object_role_correct context r
  rw [run] at run'
  exact facts r' (Result.ok_injective run').symm

theorem counted_key_spec (context : data_ontology.Context) (e : ClassExpression) (r : ObjectPropertyExpression)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.counted_key context e r out = .ok res ∧ ∀ out', res = some out' →
      ∃ e', data_ontology.encode_class context e = .ok (some e') ∧ ¬ Reserved (RoleOf r).iri.spelling.val ∧
        (RoleOf r = topObject ∨ RoleOf r ∈ context.roles.val) ∧
        out'.val = out.val ++ [bare (countedAxiom e' r)] := by
  rw [key_ontology.counted_key]
  obtain ⟨r1, run1, _⟩ := object_role_correct context r
  obtain ⟨r2, run2⟩ := encode_class_runs context e
  cases r1 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some copy =>
    obtain ⟨same, plain, inContext⟩ := object_role_some run1
    subst same
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some e' =>
      obtain ⟨r3, run3, contents⟩ := push_spec out (.SubClassOf (.Class keyClass) (.ObjectMaxCardinality (.Succ .Zero)
        (inverseRole copy) (some (.ObjectIntersectionOf ⟨e', .Class keyClass, alloc.vec.Vec.new ClassExpression⟩))))
      refine ⟨r3, by simp [run1, run2, named_class_eq, inverse_of_eq, data_ontology.and, run3],
        fun out' h => ⟨e', run2, plain, inContext, by rw [contents out' h]; rfl⟩⟩

theorem data_counted_key_spec (context : data_ontology.Context) (e : ClassExpression) (q : ObjectPropertyExpression)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.data_counted_key context e q out = .ok res ∧ ∀ out', res = some out' →
      ∃ e', data_ontology.encode_class context e = .ok (some e') ∧
        out'.val = out.val ++ [bare (dataCountedAxiom e' q)] := by
  rw [key_ontology.data_counted_key]
  obtain ⟨r1, run1⟩ := encode_class_runs context e
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some e' =>
    obtain ⟨r2, run2, contents⟩ := push_spec out (.SubClassOf (.Class dataClass) (.ObjectMaxCardinality (.Succ .Zero)
      (inverseRole q) (some (.ObjectIntersectionOf ⟨e', .Class keyClass, alloc.vec.Vec.new ClassExpression⟩))))
    refine ⟨r2, by simp [run1, data_class_eq, Rowl.Concepts.copy_role_identity, inverse_of_eq, named_class_eq,
      data_ontology.and, run2], fun out' h => ⟨e', run1, by rw [contents out' h]; rfl⟩⟩

theorem data_chain_spec (q : ObjectPropertyExpression) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.data_chain q out = .ok res ∧ ∀ out', res = some out' →
      ∃ p : ObjectProperty, p.iri.spelling.val = shareName q ∧ ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ ChainHolds J q p) := by
  rw [key_ontology.data_chain]
  obtain ⟨r1, run1, named⟩ := share_role_correct q
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some p =>
    obtain ⟨rest, restRun, restValue⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new ObjectPropertyExpression) (inverseRole q)
        (by simp [new_val]; scalar_tac))
    obtain ⟨r3, run3, contents⟩ := push_spec out
      (.SubObjectPropertyOf (.Chain ⟨q, .Property markRole, rest⟩) (.Property p))
    refine ⟨r3, by simp [run1, Rowl.Concepts.copy_role_identity, inverse_of_eq, restRun, mark_role_eq, run3],
      fun out' h => ⟨p, named p rfl, [bare (.SubObjectPropertyOf (.Chain ⟨q, .Property markRole, rest⟩)
        (.Property p))], by rw [contents out' h]; rfl, fun J => ?_⟩⟩
    simp only [List.mem_singleton, forall_eq, bare]
    exact chain_holds J q p rest (by rw [restValue]; simp [new_val])

theorem data_chains_spec (roles : alloc.vec.Vec ObjectPropertyExpression) (index : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.data_chains roles index out = .ok res ∧ ∀ out', res = some out' →
      (∀ r ∈ roles.val.drop index.val, ∃ p : ObjectProperty, p.iri.spelling.val = shareName r) ∧
      ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ r ∈ roles.val.drop index.val, ∀ p : ObjectProperty,
            p.iri.spelling.val = shareName r → ChainHolds J r p) := by
  rw [key_ontology.data_chains]
  by_cases inside : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, facts1⟩ := data_chain_spec.{w,x} roles.val[index.val] out
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some out1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := data_chains_spec roles next out1
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance,
        restRun], fun out' h => ?_⟩
      obtain ⟨roles2, new2, c2, means2⟩ := restFacts out' h
      obtain ⟨p, pNamed, new1, c1, means1⟩ := facts1 out1 rfl
      rw [nextIndex] at roles2 means2
      refine ⟨?_, new1 ++ new2, by rw [c2, c1, List.append_assoc], fun J => ?_⟩
      · rw [split]
        intro r mem
        rcases List.mem_cons.mp mem with rfl | later
        · exact ⟨p, pNamed⟩
        · exact roles2 r later
      · rw [split]
        simp only [List.forall_mem_append, means1 J, means2 J, List.mem_cons]
        constructor
        · rintro ⟨here, later⟩ r (rfl | mem) q qNamed
          · have same : q = p := (Rowl.Tableau.property_eq_iff q p).mpr (qNamed.trans pNamed.symm)
            rw [same]; exact here
          · exact later r mem q qNamed
        · intro holds
          exact ⟨holds _ (.inl rfl) p pNamed, fun r mem q qNamed => holds r (.inr mem) q qNamed⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨?_, [], by cases h; simp, fun J => ?_⟩⟩
    · simp [List.drop_eq_nil_iff.mpr (show roles.val.length ≤ index.val by omega)]
    · simp [List.drop_eq_nil_iff.mpr (show roles.val.length ≤ index.val by omega)]
termination_by roles.val.length - index.val
decreasing_by omega

theorem append_roles_spec (roles : alloc.vec.Vec ObjectPropertyExpression) (index : Usize)
    (out : alloc.vec.Vec ObjectPropertyExpression) :
    ∃ res, key_ontology.append_roles roles index out = .ok res ∧ ∀ v, res = some v →
      v.val = out.val ++ roles.val.drop index.val := by
  rw [key_ontology.append_roles]
  by_cases inside : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    by_cases room : out.val.length < Usize.max
    · have room' : alloc.vec.Vec.len out < core.num.Usize.MAX := by
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
      obtain ⟨out1, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out roles.val[index.val] room)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := append_roles_spec roles next out1
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, room', alloc.vec.Vec.index_slice_index, lookup,
        Rowl.Concepts.copy_role_identity, push, advance, restRun], fun v h => ?_⟩
      rw [restFacts v h, contents, nextIndex, split]
      simp
    · have full : ¬ alloc.vec.Vec.len out < core.num.Usize.MAX := by
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
      exact ⟨none, by simp [UScalar.lt_equiv, inside, full], by simp⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun v h => ?_⟩
    cases h
    simp [List.drop_eq_nil_iff.mpr (show roles.val.length ≤ index.val by omega)]
termination_by roles.val.length - index.val
decreasing_by omega

/-- The roles of the data properties of a key: those of the data encoding. -/
def DataRoles (context : data_ontology.Context) (dps : List DataProperty) (datas : List ObjectPropertyExpression) :
    Prop :=
  List.Forall₂ (fun p q => data_ontology.data_role context p = .ok (some q) ∧ DataKeyRole q) dps datas

theorem data_roles_unique {context : data_ontology.Context} {dps : List DataProperty}
    {datas datas' : List ObjectPropertyExpression} (h : DataRoles context dps datas) (h' : DataRoles context dps datas') :
    datas = datas' := by
  induction h generalizing datas' with
  | nil => cases h'; rfl
  | cons head _ ih =>
    cases h' with
    | cons head' tail' =>
      rw [Option.some.inj (Result.ok_injective (head.1.symm.trans head'.1)), ih tail']

theorem data_roles_length {context : data_ontology.Context} {dps : List DataProperty}
    {datas : List ObjectPropertyExpression} (h : DataRoles context dps datas) : datas.length = dps.length :=
  (List.Forall₂.length_eq h).symm

theorem data_roles_key {context : data_ontology.Context} {dps : List DataProperty}
    {datas : List ObjectPropertyExpression} (h : DataRoles context dps datas) : ∀ q ∈ datas, DataKeyRole q := by
  induction h with
  | nil => simp
  | cons head _ ih =>
    intro q mem
    rcases List.mem_cons.mp mem with rfl | later
    · exact head.2
    · exact ih q later

theorem data_key_roles_spec (context : data_ontology.Context) (data : alloc.vec.Vec DataProperty) (index : Usize)
    (out : alloc.vec.Vec ObjectPropertyExpression) :
    ∃ res, key_ontology.data_key_roles context data index out = .ok res ∧ ∀ v, res = some v →
      ∃ new, v.val = out.val ++ new ∧ DataRoles context (data.val.drop index.val) new := by
  rw [key_ontology.data_key_roles]
  by_cases inside : index.val < data.val.length
  · have lookup : data.index_usize index = .ok data.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    by_cases bottom : data.val[index.val] = bottomData
    · exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, is_bottom_data_correct,
        bottom], by simp⟩
    · obtain ⟨r1, run1, facts1⟩ := data_role_correct context data.val[index.val]
      cases r1 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
          is_bottom_data_correct, bottom, run1], by simp⟩
      | some q =>
        have dataRole : DataKeyRole q := by
          rcases facts1 q rfl with ⟨isBottom, _⟩ | ⟨_, _, _, q', rfl, roleOf⟩
          · exact absurd isBottom bottom
          · exact ⟨_, q', rfl, roleOf⟩
        by_cases room : out.val.length < Usize.max
        · have room' : alloc.vec.Vec.len out < core.num.Usize.MAX := by
            simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
          obtain ⟨out1, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out q room)
          obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
          have nextIndex : next.val = index.val + 1 := by simpa using nextValue
          obtain ⟨rest, restRun, restFacts⟩ := data_key_roles_spec context data next out1
          refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
            is_bottom_data_correct, bottom, run1, room', push, advance, restRun], fun v h => ?_⟩
          obtain ⟨new, value, roles⟩ := restFacts v h
          rw [nextIndex] at roles
          refine ⟨q :: new, by rw [value, contents]; simp, ?_⟩
          rw [split]
          exact .cons ⟨run1, dataRole⟩ roles
        · have full : ¬ alloc.vec.Vec.len out < core.num.Usize.MAX := by
            simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
          exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
            is_bottom_data_correct, bottom, run1, full], by simp⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun v h => ⟨[], by cases h; simp, ?_⟩⟩
    rw [List.drop_eq_nil_iff.mpr (show data.val.length ≤ index.val by omega)]
    exact .nil
termination_by data.val.length - index.val
decreasing_by omega

theorem chain_spec (context : data_ontology.Context) (r : ObjectPropertyExpression) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.chain context r out = .ok res ∧ ∀ out', res = some out' →
      ¬ Reserved (RoleOf r).iri.spelling.val ∧ (RoleOf r = topObject ∨ RoleOf r ∈ context.roles.val) ∧
      ∃ p : ObjectProperty, p.iri.spelling.val = shareName r ∧ ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ ChainHolds J r p) := by
  rw [key_ontology.chain]
  obtain ⟨r1, run1, _⟩ := object_role_correct context r
  obtain ⟨r2, run2, named⟩ := share_role_correct r
  cases r1 with
  | none => exact ⟨none, by simp [run1, run2], by simp⟩
  | some copy =>
    obtain ⟨same, plain, inContext⟩ := object_role_some run1
    subst same
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some p =>
      obtain ⟨rest, restRun, restValue⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec (alloc.vec.Vec.new ObjectPropertyExpression) (inverseRole copy)
          (by simp [new_val]; scalar_tac))
      obtain ⟨r3, run3, contents⟩ := push_spec out
        (.SubObjectPropertyOf (.Chain ⟨copy, .Property markRole, rest⟩) (.Property p))
      refine ⟨r3, by simp [run1, run2, inverse_of_eq, restRun, mark_role_eq, run3], fun out' h =>
        ⟨plain, inContext, p, named p rfl, [bare (.SubObjectPropertyOf (.Chain ⟨copy, .Property markRole, rest⟩)
          (.Property p))], by rw [contents out' h]; rfl, fun J => ?_⟩⟩
      simp only [List.mem_singleton, forall_eq, bare]
      exact chain_holds J copy p rest (by rw [restValue]; simp [new_val])

theorem chains_spec (context : data_ontology.Context) (roles : alloc.vec.Vec ObjectPropertyExpression) (index : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.chains context roles index out = .ok res ∧ ∀ out', res = some out' →
      (∀ r ∈ roles.val.drop index.val, ¬ Reserved (RoleOf r).iri.spelling.val ∧
        (RoleOf r = topObject ∨ RoleOf r ∈ context.roles.val) ∧
        ∃ p : ObjectProperty, p.iri.spelling.val = shareName r) ∧
      ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ r ∈ roles.val.drop index.val, ∀ p : ObjectProperty,
            p.iri.spelling.val = shareName r → ChainHolds J r p) := by
  rw [key_ontology.chains]
  by_cases inside : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, facts1⟩ := chain_spec.{w,x} context roles.val[index.val] out
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some out1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := chains_spec context roles next out1
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance,
        restRun], fun out' h => ?_⟩
      obtain ⟨roles2, new2, c2, means2⟩ := restFacts out' h
      obtain ⟨plain1, inContext1, p, pNamed, new1, c1, means1⟩ := facts1 out1 rfl
      rw [nextIndex] at roles2 means2
      refine ⟨?_, new1 ++ new2, by rw [c2, c1, List.append_assoc], fun J => ?_⟩
      · rw [split]
        intro r mem
        rcases List.mem_cons.mp mem with rfl | later
        · exact ⟨plain1, inContext1, p, pNamed⟩
        · exact roles2 r later
      · rw [split]
        simp only [List.forall_mem_append, means1 J, means2 J, List.mem_cons]
        constructor
        · rintro ⟨here, later⟩ r (rfl | mem) q qNamed
          · have same : q = p := (Rowl.Tableau.property_eq_iff q p).mpr (qNamed.trans pNamed.symm)
            rw [same]; exact here
          · exact later r mem q qNamed
        · intro holds
          exact ⟨holds _ (.inl rfl) p pNamed, fun r mem q qNamed => holds r (.inr mem) q qNamed⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨?_, [], by cases h; simp, fun J => ?_⟩⟩
    · simp [List.drop_eq_nil_iff.mpr (show roles.val.length ≤ index.val by omega)]
    · simp [List.drop_eq_nil_iff.mpr (show roles.val.length ≤ index.val by omega)]
termination_by roles.val.length - index.val
decreasing_by omega

theorem apart_spec (roles : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) (a : Individual)
    (out : alloc.vec.Vec ClassExpression) :
    ∃ res, key_ontology.apart roles index a out = .ok res ∧ ∀ v, res = some v →
      ∃ ps : List ObjectProperty, List.Forall₂ (fun p r => p.iri.spelling.val = shareName r) ps
        (roles.val.drop index.val) ∧
        v.val = out.val ++ ps.map (fun p => .ObjectAllValuesFrom (.Inverse p)
          (.ObjectComplementOf (.ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩))) := by
  rw [key_ontology.apart]
  by_cases inside : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, named⟩ := share_role_correct roles.val[index.val]
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some p =>
      by_cases room : out.val.length < Usize.max
      · have room' : alloc.vec.Vec.len out < core.num.Usize.MAX := by
          simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
        let c : ClassExpression := .ObjectAllValuesFrom (.Inverse p)
          (.ObjectComplementOf (.ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩))
        obtain ⟨out1, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out c room)
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIndex : next.val = index.val + 1 := by simpa using nextValue
        obtain ⟨rest, restRun, restFacts⟩ := apart_spec roles next a out1
        refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, room',
          nominal_eq, not_eq, push, advance, restRun, c], fun v h => ?_⟩
        obtain ⟨ps, pairs, value⟩ := restFacts v h
        rw [nextIndex] at pairs
        refine ⟨p :: ps, by rw [split]; exact .cons (named p rfl) pairs, ?_⟩
        rw [value, contents]
        simp [c]
      · have full : ¬ alloc.vec.Vec.len out < core.num.Usize.MAX := by
          simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
        exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, full], by simp⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun v h => ⟨[], ?_, by cases h; simp⟩⟩
    simp [List.drop_eq_nil_iff.mpr (show roles.val.length ≤ index.val by omega)]
termination_by roles.val.length - index.val
decreasing_by omega


theorem outside_spec (rest : alloc.vec.Vec ClassExpression) (p : ObjectProperty) (c : ClassExpression) (a : Individual) :
    ∃ res, key_ontology.outside rest p c a = .ok res ∧ ∀ v, res = some v →
      v.val = rest.val ++ [.ObjectAllValuesFrom (.Inverse p) (.ObjectUnionOf ⟨.ObjectComplementOf
        (.ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩), .ObjectComplementOf c, alloc.vec.Vec.new ClassExpression⟩)] := by
  rw [key_ontology.outside]
  by_cases room : rest.val.length < Usize.max
  · have room' : alloc.vec.Vec.len rest < core.num.Usize.MAX := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
    let d : ClassExpression := .ObjectAllValuesFrom (.Inverse p) (.ObjectUnionOf ⟨.ObjectComplementOf
      (.ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩), .ObjectComplementOf c, alloc.vec.Vec.new ClassExpression⟩)
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec rest d room)
    refine ⟨some pushed, by simp [room', nominal_eq, not_eq, data_ontology.or, push, d], fun v h => ?_⟩
    cases h
    rw [contents]
  · have full : ¬ alloc.vec.Vec.len rest < core.num.Usize.MAX := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
    exact ⟨none, by simp [full], by simp⟩


section Shared
variable {Object' : Type w} {Value' : Type x}

/-- The assertion of a key with the roles `r0 :: rs` at an element `a`: if `a`
    is in `e'`, every element of `N` in `e'` that shares a marked value with it
    along `r0`, and along every role of `rs`, is `a`. -/
def SharedAt (J : Interpretation Object' Value') (e' : ClassExpression) (r0 : ObjectPropertyExpression)
    (rs : List ObjectPropertyExpression) (a : Object') : Prop :=
  classDenote J e' a → ∀ y, Shares J r0 a y → J.classes keyClass y → classDenote J e' y →
    y = a ∨ ∃ r ∈ rs, ¬ Shares J r a y

theorem shared_at_iff {J : Interpretation Object' Value'} {e' : ClassExpression} {r0 : ObjectPropertyExpression}
    {rs : List ObjectPropertyExpression} {p0 : ObjectProperty} {ps : List ObjectProperty}
    (named0 : p0.iri.spelling.val = shareName r0)
    (named : List.Forall₂ (fun p r => p.iri.spelling.val = shareName r) ps rs) (a : Object') :
    SharedHolds J e' p0 ps a ↔ SharedAt J e' r0 rs a := by
  have others : (∃ p ∈ ps, ¬ J.objectProperties p a · ) = (∃ r ∈ rs, ¬ Shares J r a ·) := by
    funext y
    apply propext
    clear named0
    induction named with
    | nil => simp
    | cons head tail ih =>
      simp only [List.mem_cons, exists_eq_or_imp]
      rw [shares_iff head, ih]
  simp only [SharedHolds, SharedAt]
  apply imp_congr Iff.rfl
  apply forall_congr'; intro y
  rw [shares_iff named0]
  apply imp_congr Iff.rfl
  apply imp_congr Iff.rfl
  apply imp_congr Iff.rfl
  rw [show (∃ p ∈ ps, ¬ J.objectProperties p a y) ↔ (∃ r ∈ rs, ¬ Shares J r a y) from by
    rw [show (∃ p ∈ ps, ¬ J.objectProperties p a y) = (fun y => ∃ p ∈ ps, ¬ J.objectProperties p a y) y from rfl,
      others]]

end Shared

theorem shared_assertion_spec (context : data_ontology.Context) (e : ClassExpression)
    (roles : alloc.vec.Vec ObjectPropertyExpression) (r0 : ObjectPropertyExpression) (rs : List ObjectPropertyExpression)
    (shape : roles.val = r0 :: rs) (a : Individual) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.shared_assertion context e roles a out = .ok res ∧ ∀ out', res = some out' →
      (∀ n, a = .Named n → ¬ Reserved n.iri.spelling.val) ∧
      ∃ e', data_ontology.encode_class context e = .ok (some e') ∧ ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ SharedAt J e' r0 rs (individual J a)) := by
  rw [key_ontology.shared_assertion]
  have lookup : roles.index_usize 0#usize = .ok r0 := by
    simp [alloc.vec.Vec.index_usize, shape]
  let nominal : ClassExpression := .ObjectOneOf ⟨a, alloc.vec.Vec.new Individual⟩
  obtain ⟨rest, restRun, restValue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new ClassExpression) nominal (by simp [new_val]; scalar_tac))
  obtain ⟨r1, run1⟩ := encode_class_runs context e
  obtain ⟨r2, run2, named2⟩ := share_role_correct r0
  obtain ⟨r3, run3, facts3⟩ := apart_spec roles 1#usize a rest
  obtain ⟨r4, run4, facts4⟩ := object_individual_of_correct a
  cases r1 with
  | none =>
    exact ⟨none, by simp [nominal_eq, restRun, run1, alloc.vec.Vec.index_slice_index, lookup, run2, run3, run4,
      nominal], by simp⟩
  | some e' =>
    cases r2 with
    | none =>
      exact ⟨none, by simp [nominal_eq, restRun, run1, alloc.vec.Vec.index_slice_index, lookup, run2, run3, run4,
        nominal], by simp⟩
    | some p0 =>
      cases r3 with
      | none =>
        exact ⟨none, by simp [nominal_eq, restRun, run1, alloc.vec.Vec.index_slice_index, lookup, run2, run3, run4,
          nominal], by simp⟩
      | some rest1 =>
        cases r4 with
        | none =>
          exact ⟨none, by simp [nominal_eq, restRun, run1, alloc.vec.Vec.index_slice_index, lookup, run2, run3, run4,
            nominal], by simp⟩
        | some copy =>
          obtain ⟨same, plain⟩ := facts4 copy rfl
          subst same
          obtain ⟨ps, pairs, value⟩ := facts3 rest1 rfl
          obtain ⟨r6, run6, facts6⟩ := outside_spec rest1 p0 e' copy
          cases r6 with
          | none =>
            exact ⟨none, by simp [nominal_eq, restRun, run1, alloc.vec.Vec.index_slice_index, lookup, run2, run3,
              run4, run6, nominal], by simp⟩
          | some rest2 =>
            have value2 := facts6 rest2 rfl
            let main : Axiom := .ClassAssertion (.ObjectAllValuesFrom (.Property p0)
              (.ObjectUnionOf ⟨.ObjectComplementOf (.Class keyClass), .ObjectComplementOf e', rest2⟩)) copy
            obtain ⟨r5, run5, contents⟩ := push_spec out main
            refine ⟨r5, by simp [nominal_eq, restRun, run1, alloc.vec.Vec.index_slice_index, lookup, run2, run3,
              run4, run6, nominal, not_eq, named_class_eq, run5, main], fun out' h =>
              ⟨plain, e', run1, [bare main], by rw [contents out' h]; rfl, fun J => ?_⟩⟩
            simp only [List.mem_singleton, forall_eq, bare, main]
            rw [shared_holds J e' p0 ps copy rest2 (by
              rw [value2, value, restValue]; simp [new_val, nominal, sharedRest])]
            have pairs' : List.Forall₂ (fun p r => p.iri.spelling.val = shareName r) ps rs := by
              simpa [shape] using pairs
            exact shared_at_iff (named2 p0 rfl) pairs' (individual J copy)


theorem shared_at_spec (context : data_ontology.Context) (e : ClassExpression)
    (roles : alloc.vec.Vec ObjectPropertyExpression) (r0 : ObjectPropertyExpression) (rs : List ObjectPropertyExpression)
    (shape : roles.val = r0 :: rs) (a : Individual) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.shared_at context e roles a out = .ok res ∧ ∀ out', res = some out' →
      (∀ n, a = .Named n → ¬ Reserved n.iri.spelling.val) ∧
      (∀ n, a = .Named n → ∃ e', data_ontology.encode_class context e = .ok (some e')) ∧
      ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ n, a = .Named n → ∀ e', data_ontology.encode_class context e = .ok (some e') →
            SharedAt J e' r0 rs (J.namedIndividuals n)) := by
  cases a with
  | Named n =>
    rw [key_ontology.shared_at]
    obtain ⟨res, run, facts⟩ := shared_assertion_spec.{w,x} context e roles r0 rs shape (.Named n) out
    refine ⟨res, run, fun out' h => ?_⟩
    obtain ⟨plain, e', eRun, new, c, means⟩ := facts out' h
    refine ⟨plain, fun _ _ => ⟨e', eRun⟩, new, c, fun J => ?_⟩
    rw [means J]
    constructor
    · intro holds m same e'' eRun'
      cases same
      have same : e'' = e' := Option.some.inj (Result.ok_injective (eRun'.symm.trans eRun))
      subst same
      exact holds
    · intro holds
      exact holds n rfl e' eRun
  | Anonymous b =>
    refine ⟨some out, by rw [key_ontology.shared_at], fun out' h => ⟨by simp, by simp, [], by cases h; simp,
      fun J => ?_⟩⟩
    simp

theorem shared_assertions_spec (context : data_ontology.Context) (e : ClassExpression)
    (roles : alloc.vec.Vec ObjectPropertyExpression) (r0 : ObjectPropertyExpression) (rs : List ObjectPropertyExpression)
    (shape : roles.val = r0 :: rs) (nodes : alloc.vec.Vec Individual) (index : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.shared_assertions context e roles nodes index out = .ok res ∧ ∀ out', res = some out' →
      (∀ n, Individual.Named n ∈ nodes.val.drop index.val → ∃ e', data_ontology.encode_class context e = .ok (some e')) ∧
      ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔ ∀ n, Individual.Named n ∈ nodes.val.drop index.val →
            ∀ e', data_ontology.encode_class context e = .ok (some e') → SharedAt J e' r0 rs (J.namedIndividuals n)) := by
  rw [key_ontology.shared_assertions]
  by_cases inside : index.val < nodes.val.length
  · have lookup : nodes.index_usize index = .ok nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, facts1⟩ := shared_at_spec.{w,x} context e roles r0 rs shape nodes.val[index.val] out
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some out1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := shared_assertions_spec context e roles r0 rs shape nodes next out1
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance,
        restRun], fun out' h => ?_⟩
      obtain ⟨exists2, new2, c2, means2⟩ := restFacts out' h
      obtain ⟨_, exists1, new1, c1, means1⟩ := facts1 out1 rfl
      rw [nextIndex] at exists2 means2
      refine ⟨fun n mem => ?_, new1 ++ new2, by rw [c2, c1, List.append_assoc], fun J => ?_⟩
      · rw [split] at mem
        rcases List.mem_cons.mp mem with same | later
        · exact exists1 n same.symm
        · exact exists2 n later
      rw [split]
      simp only [List.forall_mem_append, means1 J, means2 J, List.mem_cons]
      constructor
      · rintro ⟨here, later⟩ n (same | mem)
        · exact here n same.symm
        · exact later n mem
      · intro holds
        exact ⟨fun n same => holds n (.inl same.symm), fun n mem => holds n (.inr mem)⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨?_, [], by cases h; simp, fun J => ?_⟩⟩
    · simp [List.drop_eq_nil_iff.mpr (show nodes.val.length ≤ index.val by omega)]
    · simp [List.drop_eq_nil_iff.mpr (show nodes.val.length ≤ index.val by omega)]
termination_by nodes.val.length - index.val
decreasing_by omega

/-- What the axioms of a key with the class expression `e`, the roles `roles`
    of its object properties and the roles `datas` of its data properties say,
    for the named individuals `names` and the encoding `e'` of `e`: in every
    interpretation that satisfies them, in which `names` are in `N` and, for a
    key that is not counted, `N ⊑ ∃mark.Self` holds, and `D ⊑ ∃mark.Self` too
    when it has a data property, the key holds for `names`; and they hold in
    every interpretation with the structure of `mark` and `share` whose elements
    of `N` and data nodes are marked and whose elements of `N` include `names`,
    in which the key holds for the elements of `N`. -/
def KeyMeans (context : data_ontology.Context) (e : ClassExpression) (roles datas : List ObjectPropertyExpression)
    (names : List NamedIndividual) (shared dataShared : Bool) (new : List AnnotatedAxiom) : Prop :=
  (roles ≠ [] ∨ datas ≠ []) ∧
  (∀ r ∈ roles, ¬ Reserved (RoleOf r).iri.spelling.val ∧ RoleOf r ∈ context.roles.val) ∧
  (∀ q ∈ datas, DataKeyRole q) ∧
  (names ≠ [] → ∃ e', data_ontology.encode_class context e = .ok (some e')) ∧
  (∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'), (∀ b ∈ new, satisfies J b.axiom) →
    (∀ a ∈ names, J.classes keyClass (J.namedIndividuals a)) →
    (shared = true → ∀ y, J.classes keyClass y → J.objectProperties markRole y y) →
    (dataShared = true → ∀ y, J.classes dataClass y → J.objectProperties markRole y y) →
    ∀ e', data_ontology.encode_class context e = .ok (some e') → KeyHoldsAt J e' roles datas names) ∧
  (∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') (marked : Object' → Prop),
    Structured J marked → (∀ y, J.classes keyClass y → marked y) → (∀ y, J.classes dataClass y → marked y) →
    (∀ a ∈ names, J.classes keyClass (J.namedIndividuals a)) →
    (∀ e', data_ontology.encode_class context e = .ok (some e') → KeyHolds J e' (roles ++ datas) marked) →
    ∀ b ∈ new, satisfies J b.axiom)

theorem counted_means {context : data_ontology.Context} {e e' : ClassExpression} {r : ObjectPropertyExpression}
    (eRun : data_ontology.encode_class context e = .ok (some e')) (plain : ¬ Reserved (RoleOf r).iri.spelling.val)
    (inContext : RoleOf r ∈ context.roles.val) (names : List NamedIndividual) :
    KeyMeans.{w,x} context e [r] [] names false false [bare (countedAxiom e' r)] := by
  refine ⟨by simp, by simp [plain, inContext], by simp, fun _ => ⟨e', eRun⟩, fun J holds named _ _ e'' eRun' => ?_,
    fun J marked _ markedN _ _ keys => ?_⟩
  · have same : e'' = e' := Option.some.inj (Result.ok_injective (eRun'.symm.trans eRun))
    subst same
    have counted := (counted_holds J e'' r).mp (holds (bare (countedAxiom e'' r)) (by simp))
    intro a aIn b bIn inA inB shared _
    obtain ⟨c, cIn, ra, rb⟩ := shared r (by simp)
    exact counted _ (named c cIn) _ _ ra inA (named a aIn) rb inB (named b bIn)
  · have key := keys e' eRun
    simp only [List.mem_singleton, forall_eq, bare]
    rw [counted_holds]
    intro z inZ y y' ry ey ny ry' ey' ny'
    exact key y y' ny ny' ey ey' (fun s mem => by
      simp only [List.append_nil, List.mem_singleton] at mem
      subst mem
      exact ⟨z, markedN z inZ, ry, ry'⟩)

theorem data_counted_means {context : data_ontology.Context} {e e' : ClassExpression} {q : ObjectPropertyExpression}
    (eRun : data_ontology.encode_class context e = .ok (some e')) (dataRole : DataKeyRole q)
    (names : List NamedIndividual) :
    KeyMeans.{w,x} context e [] [q] names false false [bare (dataCountedAxiom e' q)] := by
  refine ⟨by simp, by simp, by simp [dataRole], fun _ => ⟨e', eRun⟩, fun J holds named _ _ e'' eRun' => ?_,
    fun J marked _ _ markedD _ keys => ?_⟩
  · have same : e'' = e' := Option.some.inj (Result.ok_injective (eRun'.symm.trans eRun))
    subst same
    have counted := (data_counted_holds J e'' q).mp (holds (bare (dataCountedAxiom e'' q)) (by simp))
    intro a aIn b bIn inA inB _ shared
    obtain ⟨z, inD, ra, rb⟩ := shared q (by simp)
    exact counted z inD _ _ ra inA (named a aIn) rb inB (named b bIn)
  · have key := keys e' eRun
    simp only [List.mem_singleton, forall_eq, bare]
    rw [data_counted_holds]
    intro z inD y y' ry ey ny ry' ey' ny'
    exact key y y' ny ny' ey ey' (fun s mem => by
      simp only [List.nil_append, List.mem_singleton] at mem
      subst mem
      exact ⟨z, markedD z inD, ry, ry'⟩)

theorem shared_means {context : data_ontology.Context} {e : ClassExpression} {roles datas : List ObjectPropertyExpression}
    {r0 : ObjectPropertyExpression} {rs : List ObjectPropertyExpression} (shape : roles ++ datas = r0 :: rs)
    (objectRoles : ∀ r ∈ roles, ¬ Reserved (RoleOf r).iri.spelling.val ∧ RoleOf r ∈ context.roles.val)
    (dataRoles : ∀ q ∈ datas, DataKeyRole q)
    (named : ∀ r ∈ r0 :: rs, ∃ p : ObjectProperty, p.iri.spelling.val = shareName r)
    (names : List NamedIndividual) (chainsNew assertionsNew : List AnnotatedAxiom)
    (chainsMean : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
      (∀ b ∈ chainsNew, satisfies J b.axiom) ↔ ∀ r ∈ r0 :: rs, ∀ p : ObjectProperty,
        p.iri.spelling.val = shareName r → ChainHolds J r p)
    (encoded : names ≠ [] → ∃ e', data_ontology.encode_class context e = .ok (some e'))
    (assertionsMean : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
      (∀ b ∈ assertionsNew, satisfies J b.axiom) ↔ ∀ n ∈ names, ∀ e', data_ontology.encode_class context e = .ok (some e') →
        SharedAt J e' r0 rs (J.namedIndividuals n)) :
    KeyMeans.{w,x} context e roles datas names true (decide (datas ≠ [])) (chainsNew ++ assertionsNew) := by
  have nonempty : roles ≠ [] ∨ datas ≠ [] := by
    by_cases h : roles = []
    · right; intro hd; rw [h, hd] at shape; simp at shape
    · exact .inl h
  have memAll : ∀ r, r ∈ r0 :: rs ↔ r ∈ roles ∨ r ∈ datas := by
    intro r; rw [← shape, List.mem_append]
  refine ⟨nonempty, objectRoles, dataRoles, encoded, fun J holds namedN marks dataMarks e' eRun => ?_,
    fun J marked structured markedN markedD namedN keys => ?_⟩
  · rw [List.forall_mem_append, chainsMean J, assertionsMean J] at holds
    obtain ⟨chains, assertions'⟩ := holds
    have assertions : ∀ n ∈ names, SharedAt J e' r0 rs (J.namedIndividuals n) := fun n nIn => assertions' n nIn e' eRun
    intro a aIn b bIn inA inB sharedObjects sharedData
    have shares : ∀ r ∈ r0 :: rs, Shares J r (J.namedIndividuals a) (J.namedIndividuals b) := by
      intro r mem
      obtain ⟨p, pNamed⟩ := named r mem
      rcases (memAll r).mp mem with inRoles | inDatas
      · obtain ⟨c, cIn, ra, rb⟩ := sharedObjects r inRoles
        exact ⟨p, pNamed, chains r mem p pNamed _ _ _ _ ra (marks rfl _ (namedN c cIn)) rb⟩
      · obtain ⟨z, inD, ra, rb⟩ := sharedData r inDatas
        have dataShared : decide (datas ≠ []) = true := by
          simpa using List.ne_nil_of_mem inDatas
        exact ⟨p, pNamed, chains r mem p pNamed _ _ _ _ ra (dataMarks dataShared z inD) rb⟩
    rcases assertions a aIn inA (J.namedIndividuals b) (shares r0 (by simp)) (namedN b bIn) inB with
      same | ⟨r, rMem, apart⟩
    · exact same.symm
    · exact absurd (shares r (List.mem_cons_of_mem _ rMem)) apart
  · rw [List.forall_mem_append, chainsMean J, assertionsMean J]
    obtain ⟨markIff, shareIff⟩ := structured
    have keyRole : ∀ r ∈ r0 :: rs, ¬ Reserved (RoleOf r).iri.spelling.val ∨ DataKeyRole r := by
      intro r mem
      rcases (memAll r).mp mem with inRoles | inDatas
      · exact .inl (objectRoles r inRoles).1
      · exact .inr (dataRoles r inDatas)
    refine ⟨fun r mem p pNamed y z z' y' ry mark ry' => ?_, fun n nIn e' eRun inE y sharesY inN inE' => ?_⟩
    · obtain ⟨same, markedZ⟩ := (markIff z z').mp mark
      subst same
      exact (shareIff r p pNamed (keyRole r mem) y y').mpr ⟨z, markedZ, ry, ry'⟩
    · by_cases all : ∀ r ∈ rs, Shares J r (J.namedIndividuals n) y
      · left
        refine (keys e' eRun _ _ (namedN n nIn) inN inE inE' (fun r mem => ?_)).symm
        have mem' : r ∈ r0 :: rs := by rw [← shape]; exact mem
        have sharesR : Shares J r (J.namedIndividuals n) y := by
          rcases List.mem_cons.mp mem' with rfl | later
          · exact sharesY
          · exact all r later
        obtain ⟨p, pNamed, related⟩ := sharesR
        exact (shareIff r p pNamed (keyRole r mem') _ y).mp related
      · right
        simp only [not_forall] at all
        obtain ⟨r, mem, apart⟩ := all
        exact ⟨r, mem, apart⟩

/-- A key that is counted: one property, when the closure allows counting. -/
def Counted (objects data : Nat) (counting : Bool) : Prop :=
  counting = true ∧ ((objects = 1 ∧ data = 0) ∨ (objects = 0 ∧ data = 1))

theorem counted_correct (objects data : Usize) (counting : Bool) :
    key_ontology.counted objects data counting = .ok (decide (Counted objects.val data.val counting)) := by
  rw [key_ontology.counted]
  cases counting <;> simp [Counted, UScalar.eq_equiv]

theorem key_with_spec (context : data_ontology.Context) (e : ClassExpression)
    (objects datas : alloc.vec.Vec ObjectPropertyExpression)
    (nodes : alloc.vec.Vec Individual) (counting : Bool) (out : alloc.vec.Vec AnnotatedAxiom)
    (nonempty : objects.val ≠ [] ∨ datas.val ≠ []) (noTop : ∀ r ∈ objects.val, RoleOf r ≠ topObject)
    (dataRoles : ∀ q ∈ datas.val, DataKeyRole q) :
    ∃ res, key_ontology.key_with context e objects datas nodes counting out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧
        KeyMeans.{w,x} context e objects.val datas.val (namesOf nodes.val)
          (decide (¬ Counted objects.val.length datas.val.length counting))
          (decide (¬ Counted objects.val.length datas.val.length counting ∧ datas.val ≠ [])) new := by
  rw [key_ontology.key_with, counted_correct]
  simp only [alloc.vec.Vec.len_val]
  by_cases isCounted : Counted objects.val.length datas.val.length counting
  · rcases isCounted.2 with ⟨o1, d0⟩ | ⟨o0, d1⟩
    · obtain ⟨r, shape⟩ : ∃ r, objects.val = [r] := by
        match h : objects.val, o1 with
        | [r], _ => exact ⟨r, rfl⟩
      have datasNil : datas.val = [] := List.eq_nil_of_length_eq_zero d0
      have one' : alloc.vec.Vec.len objects = 1#usize := UScalar.eq_of_val_eq (by simpa using o1)
      have lookup : objects.index_usize 0#usize = .ok r := by simp [alloc.vec.Vec.index_usize, shape]
      obtain ⟨res, run, facts⟩ := counted_key_spec context e r out
      refine ⟨res, by simp [isCounted, one', alloc.vec.Vec.index_slice_index, lookup, run], fun out' h => ?_⟩
      obtain ⟨e', eRun, plain, inContext, contents⟩ := facts out' h
      have inContext' : RoleOf r ∈ context.roles.val := inContext.resolve_left (noTop r (by simp [shape]))
      refine ⟨[bare (countedAxiom e' r)], contents, ?_⟩
      rw [show decide (¬ Counted objects.val.length datas.val.length counting) = false by simp [isCounted],
        show decide (¬ Counted objects.val.length datas.val.length counting ∧ datas.val ≠ []) = false by
          simp [isCounted], shape, datasNil]
      exact counted_means eRun plain inContext' _
    · obtain ⟨q, shape⟩ : ∃ q, datas.val = [q] := by
        match h : datas.val, d1 with
        | [q], _ => exact ⟨q, rfl⟩
      have objectsNil : objects.val = [] := List.eq_nil_of_length_eq_zero o0
      have notOne : ¬ alloc.vec.Vec.len objects = 1#usize := fun h => by
        have := congrArg UScalar.val h; simp [o0] at this
      have lookup : datas.index_usize 0#usize = .ok q := by simp [alloc.vec.Vec.index_usize, shape]
      obtain ⟨res, run, facts⟩ := data_counted_key_spec context e q out
      refine ⟨res, by simp [isCounted, notOne, alloc.vec.Vec.index_slice_index, lookup, run], fun out' h => ?_⟩
      obtain ⟨e', eRun, contents⟩ := facts out' h
      refine ⟨[bare (dataCountedAxiom e' q)], contents, ?_⟩
      rw [show decide (¬ Counted objects.val.length datas.val.length counting) = false by simp [isCounted],
        show decide (¬ Counted objects.val.length datas.val.length counting ∧ datas.val ≠ []) = false by
          simp [isCounted], shape, objectsNil]
      exact data_counted_means eRun (dataRoles q (by simp [shape])) _
  · obtain ⟨roles0, run0, value0⟩ := append_roles_spec objects 0#usize (alloc.vec.Vec.new ObjectPropertyExpression)
    cases roles0 with
    | none => exact ⟨none, by simp [isCounted, run0], by simp⟩
    | some roles0 =>
    obtain ⟨roles1, run1, value1⟩ := append_roles_spec datas 0#usize roles0
    cases roles1 with
    | none => exact ⟨none, by simp [isCounted, run0, run1], by simp⟩
    | some roles1 =>
    have all : roles1.val = objects.val ++ datas.val := by
      rw [value1 roles1 rfl, value0 roles0 rfl]; simp [new_val]
    obtain ⟨r0, rs, shape⟩ : ∃ r0 rs, objects.val ++ datas.val = r0 :: rs := by
      match h : objects.val ++ datas.val with
      | [] => exact absurd h (by rcases nonempty with n | n <;> simp [n])
      | r0 :: rs => exact ⟨r0, rs, rfl⟩
    obtain ⟨c1, chainsRun, chainsFacts⟩ := chains_spec.{w,x} context objects 0#usize out
    cases c1 with
    | none => exact ⟨none, by simp [isCounted, run0, run1, chainsRun], by simp⟩
    | some out1 =>
    obtain ⟨objectFacts, new1, cc1, means1⟩ := chainsFacts out1 rfl
    obtain ⟨c2, dataRun, dataFacts⟩ := data_chains_spec.{w,x} datas 0#usize out1
    cases c2 with
    | none => exact ⟨none, by simp [isCounted, run0, run1, chainsRun, dataRun], by simp⟩
    | some out2 =>
    obtain ⟨dataNamed, new2, cc2, means2⟩ := dataFacts out2 rfl
    obtain ⟨r3, run3, facts3⟩ := shared_assertions_spec.{w,x} context e roles1 r0 rs (by rw [all, shape]) nodes 0#usize
      out2
    refine ⟨r3, by simp [isCounted, run0, run1, chainsRun, dataRun, run3], fun out' h => ?_⟩
    obtain ⟨exists3, new3, cc3, means3⟩ := facts3 out' h
    refine ⟨(new1 ++ new2) ++ new3, by rw [cc3, cc2, cc1]; simp, ?_⟩
    rw [show decide (¬ Counted objects.val.length datas.val.length counting) = true by simp [isCounted],
      show decide (¬ Counted objects.val.length datas.val.length counting ∧ datas.val ≠ []) =
        decide (datas.val ≠ []) by simp [isCounted]]
    simp only [zero_val, List.drop_zero] at objectFacts means1 dataNamed means2 means3 exists3
    have memAll : ∀ r, r ∈ r0 :: rs ↔ r ∈ objects.val ∨ r ∈ datas.val := by
      intro r; rw [← shape, List.mem_append]
    refine shared_means shape (fun r mem => ?_) dataRoles (fun r mem => ?_) _ (new1 ++ new2) new3 (fun J => ?_)
      (fun nonempty => ?_) (fun J => ?_)
    · obtain ⟨plain, inContext, _⟩ := objectFacts r mem
      exact ⟨plain, inContext.resolve_left (noTop r mem)⟩
    · rcases (memAll r).mp mem with inObjects | inDatas
      · exact (objectFacts r inObjects).2.2
      · exact dataNamed r inDatas
    · rw [List.forall_mem_append, means1 J, means2 J]
      constructor
      · rintro ⟨objectChains, dataChains⟩ r mem p pNamed
        rcases (memAll r).mp mem with inObjects | inDatas
        · exact objectChains r inObjects p pNamed
        · exact dataChains r inDatas p pNamed
      · intro holds
        exact ⟨fun r mem p pNamed => holds r ((memAll r).mpr (.inl mem)) p pNamed,
          fun r mem p pNamed => holds r ((memAll r).mpr (.inr mem)) p pNamed⟩
    · obtain ⟨n, nIn⟩ := List.exists_mem_of_ne_nil _ nonempty
      exact exists3 n (mem_namesOf.mp nIn)
    · rw [means3 J]
      exact ⟨fun holds n nIn => holds n (mem_namesOf.mp nIn), fun holds n nIn => holds n (mem_namesOf.mpr nIn)⟩

theorem any_universal_correct (roles : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) :
    ∃ b, key_ontology.any_universal roles index = .ok b ∧
      (b = false → ∀ r ∈ roles.val.drop index.val, RoleOf r ≠ topObject) := by
  rw [key_ontology.any_universal]
  by_cases inside : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    by_cases top : RoleOf roles.val[index.val] = topObject
    · exact ⟨true, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, universal_correct, top],
        by simp⟩
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b, run, facts⟩ := any_universal_correct roles next
      refine ⟨b, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, universal_correct, top,
        advance, run], fun no r mem => ?_⟩
      rw [split] at mem
      rcases List.mem_cons.mp mem with rfl | later
      · exact top
      · exact facts no r (by rw [nextIndex]; exact later)
  · exact ⟨false, by simp [UScalar.lt_equiv, inside], fun _ r mem => by
      simp [List.drop_eq_nil_iff.mpr (show roles.val.length ≤ index.val by omega)] at mem⟩
termination_by roles.val.length - index.val
decreasing_by omega

/-- Whether the data values of a context let keys with data properties be
    answered: its numbers are not ordered, no floating-point numbers are in
    use, no range facets cut the time lines and no length facets the lengths. -/
def PlainValues (context : data_ontology.Context) : Prop :=
  context.kinds.ordered = false ∧ context.kinds.double = false ∧ context.kinds.float = false ∧
    context.times.val = [] ∧ context.lengths.val = []

theorem key_axioms_spec (context : data_ontology.Context) (e : ClassExpression)
    (objects : alloc.vec.Vec ObjectPropertyExpression) (data : alloc.vec.Vec DataProperty)
    (nodes : alloc.vec.Vec Individual) (counting : Bool) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.key_axioms context e objects data nodes counting out = .ok res ∧ ∀ out', res = some out' →
      (data.val ≠ [] → PlainValues context) ∧ ∃ datas, DataRoles context data.val datas ∧
        ∃ new, out'.val = out.val ++ new ∧
          KeyMeans.{w,x} context e objects.val datas (namesOf nodes.val)
            (decide (¬ Counted objects.val.length data.val.length counting))
            (decide (¬ Counted objects.val.length data.val.length counting ∧ data.val ≠ [])) new := by
  rw [key_ontology.key_axioms]
  by_cases empty : objects.val.length = 0 ∧ data.val.length = 0
  · have e1 : alloc.vec.Vec.len objects = 0#usize := UScalar.eq_of_val_eq (by simpa using empty.1)
    have e2 : alloc.vec.Vec.len data = 0#usize := UScalar.eq_of_val_eq (by simpa using empty.2)
    exact ⟨none, by simp [e1, e2], by simp⟩
  · have notEmpty : ¬ (alloc.vec.Vec.len objects = 0#usize ∧ alloc.vec.Vec.len data = 0#usize) := by
      rintro ⟨h1, h2⟩
      exact empty ⟨by simpa using congrArg UScalar.val h1, by simpa using congrArg UScalar.val h2⟩
    obtain ⟨b, run, facts⟩ := any_universal_correct objects 0#usize
    cases b with
    | true => exact ⟨none, by simp [notEmpty, run], by simp⟩
    | false =>
      have noTop : ∀ r ∈ objects.val, RoleOf r ≠ topObject := by simpa using facts rfl
      by_cases blocked : ¬ data.val = [] ∧ ((((context.kinds.ordered = true ∨ context.kinds.double = true) ∨
          context.kinds.float = true) ∨ ¬ context.times.val = []) ∨ ¬ context.lengths.val = [])
      · exact ⟨none, by simp [notEmpty, run, blocked.1, blocked.2], by simp⟩
      · obtain ⟨r1, run1, facts1⟩ := data_key_roles_spec context data 0#usize (alloc.vec.Vec.new ObjectPropertyExpression)
        cases r1 with
        | none => exact ⟨none, by simp [notEmpty, run, blocked, run1], by simp⟩
        | some datas =>
          obtain ⟨new0, value0, roles0⟩ := facts1 datas rfl
          simp only [zero_val, List.drop_zero, new_val, List.nil_append] at value0 roles0
          rw [← value0] at roles0
          have sameLength := data_roles_length roles0
          have nonempty : objects.val ≠ [] ∨ datas.val ≠ [] := by
            by_contra both
            simp only [not_or, not_not] at both
            exact empty ⟨by simp [both.1], by rw [← sameLength, both.2]; rfl⟩
          have dataRoles : ∀ q ∈ datas.val, DataKeyRole q := data_roles_key roles0
          obtain ⟨res, run2, facts2⟩ := key_with_spec.{w,x} context e objects datas nodes counting out nonempty noTop
            dataRoles
          refine ⟨res, by simp [notEmpty, run, blocked, run1, run2], fun out' h => ?_⟩
          obtain ⟨new, c, means⟩ := facts2 out' h
          refine ⟨fun hasData => ?_, datas.val, roles0, new, c, ?_⟩
          · refine ⟨?_, ?_, ?_, ?_, ?_⟩
            all_goals first
              | (rw [Bool.eq_false_iff]; intro h; exact blocked ⟨hasData, by simp [h]⟩)
              | (by_contra h; exact blocked ⟨hasData, by simp [h]⟩)
          · have ne : datas.val ≠ [] ↔ data.val ≠ [] := by
              rw [ne_eq, ne_eq, ← List.length_eq_zero_iff, ← List.length_eq_zero_iff, sameLength]
            have e1 : decide (¬ Counted objects.val.length datas.val.length counting) =
                decide (¬ Counted objects.val.length data.val.length counting) := by rw [sameLength]
            have e2 : decide (¬ Counted objects.val.length datas.val.length counting ∧ datas.val ≠ []) =
                decide (¬ Counted objects.val.length data.val.length counting ∧ data.val ≠ []) := by
              rw [decide_eq_decide, sameLength, ne]
            rw [e1, e2] at means
            exact means

/-- Whether a key of a closure is not counted, which needs the self loops of
    `mark` at the elements of `N`. -/
def SharedIn (items : List AnnotatedAxiom) (counting : Bool) : Prop :=
  ∃ item ∈ items, ∃ e ops dps, item.axiom = .HasKey e ops dps ∧ ¬ Counted ops.val.length dps.val.length counting

/-- Whether a key of a closure with a data property is not counted, which needs
    the self loops of `mark` at the data nodes. -/
def DataSharedIn (items : List AnnotatedAxiom) (counting : Bool) : Prop :=
  ∃ item ∈ items, ∃ e ops dps, item.axiom = .HasKey e ops dps ∧ ¬ Counted ops.val.length dps.val.length counting ∧
    dps.val ≠ []

/-- What the axioms of the keys of `items` say, for the named individuals
    `names`: every key with a data property is in a context whose data values
    are plain (`PlainValues`), its data properties have roles, and its object properties
    are roles of the context that are not the encoding's; in every
    interpretation that satisfies the axioms, in which `names` are in `N` and
    `mark` has the self loops the keys that are not counted need, every key
    holds for `names`; and the axioms hold in every interpretation with the
    structure of `mark` and `share` whose elements of `N` and data nodes are
    marked and whose elements of `N` include `names`, in which every key holds
    for the elements of `N`. -/
def KeysMeans (context : data_ontology.Context) (items : List AnnotatedAxiom) (names : List NamedIndividual)
    (counting : Bool) (new : List AnnotatedAxiom) : Prop :=
  (∀ item ∈ items, ∀ e ops dps, item.axiom = .HasKey e ops dps →
    (dps.val ≠ [] → PlainValues context) ∧
    ∃ datas, DataRoles context dps.val datas ∧ (ops.val ≠ [] ∨ datas ≠ []) ∧
      (∀ r ∈ ops.val, ¬ Reserved (RoleOf r).iri.spelling.val ∧ RoleOf r ∈ context.roles.val) ∧
      (names ≠ [] → ∃ e', data_ontology.encode_class context e = .ok (some e'))) ∧
  (∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'), (∀ b ∈ new, satisfies J b.axiom) →
    (∀ a ∈ names, J.classes keyClass (J.namedIndividuals a)) →
    (SharedIn items counting → ∀ y, J.classes keyClass y → J.objectProperties markRole y y) →
    (DataSharedIn items counting → ∀ y, J.classes dataClass y → J.objectProperties markRole y y) →
    ∀ item ∈ items, ∀ e ops dps, item.axiom = .HasKey e ops dps → ∀ datas, DataRoles context dps.val datas →
      ∀ e', data_ontology.encode_class context e = .ok (some e') → KeyHoldsAt J e' ops.val datas names) ∧
  (∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value') (marked : Object' → Prop),
    Structured J marked → (∀ y, J.classes keyClass y → marked y) → (∀ y, J.classes dataClass y → marked y) →
    (∀ a ∈ names, J.classes keyClass (J.namedIndividuals a)) →
    (∀ item ∈ items, ∀ e ops dps, item.axiom = .HasKey e ops dps → ∀ datas, DataRoles context dps.val datas →
      ∀ e', data_ontology.encode_class context e = .ok (some e') → KeyHolds J e' (ops.val ++ datas) marked) →
    ∀ b ∈ new, satisfies J b.axiom)

theorem keys_means_nil (context : data_ontology.Context) (names : List NamedIndividual) (counting : Bool) :
    KeysMeans.{w,x} context [] names counting [] :=
  ⟨by simp, fun _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ => by simp⟩

theorem keys_means_cons {context : data_ontology.Context} {item : AnnotatedAxiom} {rest new1 new2 : List AnnotatedAxiom}
    {names : List NamedIndividual} {counting : Bool}
    (head : ∀ e ops dps, item.axiom = .HasKey e ops dps → (dps.val ≠ [] → PlainValues context) ∧
      ∃ datas, DataRoles context dps.val datas ∧
        KeyMeans.{w,x} context e ops.val datas names (decide (¬ Counted ops.val.length dps.val.length counting))
          (decide (¬ Counted ops.val.length dps.val.length counting ∧ dps.val ≠ [])) new1)
    (plain : ¬ IsKey item.axiom → new1 = []) (tail : KeysMeans.{w,x} context rest names counting new2) :
    KeysMeans.{w,x} context (item :: rest) names counting (new1 ++ new2) := by
  obtain ⟨tailFacts, tailSound, tailComplete⟩ := tail
  refine ⟨?_, fun J holds named marks dataMarks => ?_, fun J marked structured markedN markedD named keys => ?_⟩
  · intro i mem e ops dps key
    rcases List.mem_cons.mp mem with rfl | later
    · obtain ⟨ordered, datas, roles, nonempty, objects, _, encoded, _⟩ := head e ops dps key
      exact ⟨ordered, datas, roles, nonempty, objects, encoded⟩
    · exact tailFacts i later e ops dps key
  · intro i mem e ops dps key datas roles e' eRun
    rcases List.mem_cons.mp mem with rfl | later
    · obtain ⟨_, datas', roles', means⟩ := head e ops dps key
      have same := data_roles_unique roles' roles
      subst same
      exact means.2.2.2.2.1 J (fun b m => holds b (List.mem_append_left _ m)) named
        (fun shared => marks ⟨i, List.mem_cons_self, e, ops, dps, key, by simpa using shared⟩)
        (fun shared => dataMarks ⟨i, List.mem_cons_self, e, ops, dps, key, by simpa using shared⟩) e' eRun
    · exact tailSound J (fun b m => holds b (List.mem_append_right _ m)) named
        (fun ⟨j, jMem, rest⟩ => marks ⟨j, List.mem_cons_of_mem _ jMem, rest⟩)
        (fun ⟨j, jMem, rest⟩ => dataMarks ⟨j, List.mem_cons_of_mem _ jMem, rest⟩) i later e ops dps key datas roles
        e' eRun
  · intro b mem
    rcases List.mem_append.mp mem with early | late
    · by_cases key : IsKey item.axiom
      · obtain ⟨e, ops, dps, shape⟩ : ∃ e ops dps, item.axiom = .HasKey e ops dps := by
          revert key; cases item.axiom <;> simp [IsKey]
        obtain ⟨_, datas, roles, means⟩ := head e ops dps shape
        exact means.2.2.2.2.2 J marked structured markedN markedD named
          (fun e' eRun => keys item List.mem_cons_self e ops dps shape datas roles e' eRun) b early
      · rw [plain key] at early; simp at early
    · exact tailComplete J marked structured markedN markedD named
        (fun i iMem => keys i (List.mem_cons_of_mem _ iMem)) b late

theorem axiom_keys_spec (context : data_ontology.Context) (ax : Axiom) (nodes : alloc.vec.Vec Individual)
    (counting : Bool) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.axiom_keys context ax nodes counting out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧
        (∀ e ops dps, ax = .HasKey e ops dps → (dps.val ≠ [] → PlainValues context) ∧
          ∃ datas, DataRoles context dps.val datas ∧
            KeyMeans.{w,x} context e ops.val datas (namesOf nodes.val)
              (decide (¬ Counted ops.val.length dps.val.length counting))
              (decide (¬ Counted ops.val.length dps.val.length counting ∧ dps.val ≠ [])) new) ∧
        (¬ IsKey ax → new = []) := by
  cases ax with
  | HasKey e ops dps =>
    rw [key_ontology.axiom_keys]
    obtain ⟨res, run, facts⟩ := key_axioms_spec.{w,x} context e ops dps nodes counting out
    refine ⟨res, run, fun out' h => ?_⟩
    obtain ⟨ordered, datas, roles, new, c, means⟩ := facts out' h
    refine ⟨new, c, fun e' ops' dps' same => ?_, fun notKey => absurd trivial notKey⟩
    cases same
    exact ⟨ordered, datas, roles, means⟩
  | _ =>
    refine ⟨some out, by rw [key_ontology.axiom_keys], fun out' h => ⟨[], by cases h; simp, by simp, fun _ => rfl⟩⟩

theorem keys_from_spec (context : data_ontology.Context) (items : alloc.vec.Vec AnnotatedAxiom)
    (nodes : alloc.vec.Vec Individual) (index : Usize) (counting : Bool) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.keys_from context items nodes index counting out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧
        KeysMeans.{w,x} context (items.val.drop index.val) (namesOf nodes.val) counting new := by
  rw [key_ontology.keys_from]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, facts1⟩ := axiom_keys_spec.{w,x} context items.val[index.val].axiom nodes counting out
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some out1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := keys_from_spec context items nodes next counting out1
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance,
        restRun], fun out' h => ?_⟩
      obtain ⟨new2, c2, means2⟩ := restFacts out' h
      obtain ⟨new1, c1, head, plain⟩ := facts1 out1 rfl
      rw [nextIndex] at means2
      refine ⟨new1 ++ new2, by rw [c2, c1, List.append_assoc], ?_⟩
      rw [split]
      exact keys_means_cons head plain means2
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], by cases h; simp, ?_⟩⟩
    rw [List.drop_eq_nil_iff.mpr (show items.val.length ≤ index.val by omega)]
    exact keys_means_nil context _ counting
termination_by items.val.length - index.val
decreasing_by omega

theorem shared_key_correct (ax : Axiom) (counting : Bool) :
    ∃ b, key_ontology.shared_key ax counting = .ok b ∧
      (b = true ↔ ∃ e ops dps, ax = .HasKey e ops dps ∧ ¬ Counted ops.val.length dps.val.length counting) := by
  cases ax with
  | HasKey e ops dps =>
    rw [key_ontology.shared_key]
    refine ⟨!decide (Counted ops.val.length dps.val.length counting), by simp [counted_correct], ?_⟩
    simp
  | _ => exact ⟨false, by rw [key_ontology.shared_key], by simp⟩

theorem data_shared_key_correct (ax : Axiom) (counting : Bool) :
    ∃ b, key_ontology.data_shared_key ax counting = .ok b ∧
      (b = true ↔ ∃ e ops dps, ax = .HasKey e ops dps ∧ ¬ Counted ops.val.length dps.val.length counting ∧
        dps.val ≠ []) := by
  cases ax with
  | HasKey e ops dps =>
    rw [key_ontology.data_shared_key]
    refine ⟨decide (dps.val ≠ []) && !decide (Counted ops.val.length dps.val.length counting), ?_, ?_⟩
    · have iff : (alloc.vec.Vec.len dps != 0#usize) = decide (dps.val ≠ []) := by
        rw [Bool.eq_iff_iff]
        simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
        constructor
        · intro h empty
          apply h
          apply UScalar.eq_of_val_eq
          simp [empty]
        · intro h zero
          apply h
          have := congrArg UScalar.val zero
          simpa using this
      simp [counted_correct, iff]
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      constructor
      · rintro ⟨nonempty, notCounted⟩
        exact ⟨e, ops, dps, rfl, notCounted, nonempty⟩
      · rintro ⟨_, _, _, same, notCounted, nonempty⟩
        cases same
        exact ⟨nonempty, notCounted⟩
  | _ => exact ⟨false, by rw [key_ontology.data_shared_key], by simp⟩

theorem shared_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) (counting : Bool) :
    ∃ b, key_ontology.shared_from items index counting = .ok b ∧
      (b = true ↔ SharedIn (items.val.drop index.val) counting) := by
  rw [key_ontology.shared_from]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨b, run, iff⟩ := shared_key_correct items.val[index.val].axiom counting
    cases b with
    | true =>
      refine ⟨true, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], ?_⟩
      obtain ⟨e, ops, dps, shape, notCounted⟩ := iff.mp rfl
      rw [split]
      exact ⟨fun _ => ⟨_, List.mem_cons_self, e, ops, dps, shape, notCounted⟩, fun _ => rfl⟩
    | false =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b', run', iff'⟩ := shared_from_correct items next counting
      refine ⟨b', by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, run'], ?_⟩
      rw [iff', split, nextIndex]
      constructor
      · rintro ⟨i, mem, rest⟩
        exact ⟨i, List.mem_cons_of_mem _ mem, rest⟩
      · rintro ⟨i, mem, e, ops, dps, shape, notCounted⟩
        rcases List.mem_cons.mp mem with rfl | later
        · exact absurd (iff.mpr ⟨e, ops, dps, shape, notCounted⟩) (by simp)
        · exact ⟨i, later, e, ops, dps, shape, notCounted⟩
  · refine ⟨false, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [SharedIn, List.drop_eq_nil_iff.mpr (show items.val.length ≤ index.val by omega)]
termination_by items.val.length - index.val
decreasing_by omega

theorem data_shared_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) (counting : Bool) :
    ∃ b, key_ontology.data_shared_from items index counting = .ok b ∧
      (b = true ↔ DataSharedIn (items.val.drop index.val) counting) := by
  rw [key_ontology.data_shared_from]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨b, run, iff⟩ := data_shared_key_correct items.val[index.val].axiom counting
    cases b with
    | true =>
      refine ⟨true, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], ?_⟩
      obtain ⟨e, ops, dps, shape, notCounted, nonempty⟩ := iff.mp rfl
      rw [split]
      exact ⟨fun _ => ⟨_, List.mem_cons_self, e, ops, dps, shape, notCounted, nonempty⟩, fun _ => rfl⟩
    | false =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b', run', iff'⟩ := data_shared_from_correct items next counting
      refine ⟨b', by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, run'], ?_⟩
      rw [iff', split, nextIndex]
      constructor
      · rintro ⟨i, mem, rest⟩
        exact ⟨i, List.mem_cons_of_mem _ mem, rest⟩
      · rintro ⟨i, mem, e, ops, dps, shape, notCounted, nonempty⟩
        rcases List.mem_cons.mp mem with rfl | later
        · exact absurd (iff.mpr ⟨e, ops, dps, shape, notCounted, nonempty⟩) (by simp)
        · exact ⟨i, later, e, ops, dps, shape, notCounted, nonempty⟩
  · refine ⟨false, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [DataSharedIn, List.drop_eq_nil_iff.mpr (show items.val.length ≤ index.val by omega)]
termination_by items.val.length - index.val
decreasing_by omega

theorem marks_spec (items : alloc.vec.Vec AnnotatedAxiom) (counting : Bool) (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.marks items counting out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ new, satisfies J b.axiom) ↔
            ((SharedIn items.val counting → ∀ y, J.classes keyClass y → J.objectProperties markRole y y) ∧
              (DataSharedIn items.val counting → ∀ y, J.classes dataClass y → J.objectProperties markRole y y))) := by
  rw [key_ontology.marks]
  obtain ⟨b, run, iff⟩ := shared_from_correct items 0#usize counting
  obtain ⟨b1, run1, iff1⟩ := data_shared_from_correct items 0#usize counting
  simp only [zero_val, List.drop_zero] at iff iff1
  let axN : Axiom := .SubClassOf (.Class keyClass) (.ObjectHasSelf (.Property markRole))
  let axD : Axiom := .SubClassOf (.Class dataClass) (.ObjectHasSelf (.Property markRole))
  have markN : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
      satisfies J axN ↔ ∀ y, J.classes keyClass y → J.objectProperties markRole y y := by
    intro _ _ J; simp [axN, satisfies, classDenote, objectRelation]
  have markD : ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
      satisfies J axD ↔ ∀ y, J.classes dataClass y → J.objectProperties markRole y y := by
    intro _ _ J; simp [axD, satisfies, classDenote, objectRelation]
  cases b with
  | true =>
    obtain ⟨r, pushRun, contents⟩ := push_spec out axN
    cases r with
    | none => exact ⟨none, by simp [run, named_class_eq, mark_role_eq, pushRun, axN], by simp⟩
    | some out1 =>
    cases b1 with
    | true =>
      obtain ⟨r2, pushRun2, contents2⟩ := push_spec out1 axD
      refine ⟨r2, by simp [run, named_class_eq, mark_role_eq, pushRun, axN, run1, data_class_eq, pushRun2, axD],
        fun out' h => ⟨[bare axN, bare axD], by rw [contents2 out' h, contents out1 rfl]; simp [bare], fun J => ?_⟩⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, bare,
        markN J, markD J]
      exact ⟨fun ⟨h1, h2⟩ => ⟨fun _ => h1, fun _ => h2⟩, fun ⟨h1, h2⟩ => ⟨h1 (iff.mp rfl), h2 (iff1.mp rfl)⟩⟩
    | false =>
      refine ⟨some out1, by simp [run, named_class_eq, mark_role_eq, pushRun, axN, run1], fun out' h =>
        ⟨[bare axN], by cases h; rw [contents out1 rfl]; rfl, fun J => ?_⟩⟩
      simp only [List.mem_singleton, forall_eq, bare, markN J]
      exact ⟨fun h1 => ⟨fun _ => h1, fun shared => absurd (iff1.mpr shared) (by simp)⟩,
        fun ⟨h1, _⟩ => h1 (iff.mp rfl)⟩
  | false =>
    cases b1 with
    | true =>
      obtain ⟨r2, pushRun2, contents2⟩ := push_spec out axD
      refine ⟨r2, by simp [run, run1, data_class_eq, mark_role_eq, pushRun2, axD], fun out' h =>
        ⟨[bare axD], by rw [contents2 out' h]; rfl, fun J => ?_⟩⟩
      simp only [List.mem_singleton, forall_eq, bare, markD J]
      exact ⟨fun h2 => ⟨fun shared => absurd (iff.mpr shared) (by simp), fun _ => h2⟩,
        fun ⟨_, h2⟩ => h2 (iff1.mp rfl)⟩
    | false =>
      refine ⟨some out, by simp [run, run1], fun out' h => ⟨[], by cases h; simp, fun J => ?_⟩⟩
      simp only [List.not_mem_nil, false_implies, implies_true, true_iff]
      exact ⟨fun shared => absurd (iff.mpr shared) (by simp), fun shared => absurd (iff1.mpr shared) (by simp)⟩

/-! ### The axioms other than keys -/

theorem unkeyed_cons (item : AnnotatedAxiom) (rest : List AnnotatedAxiom) :
    unkeyedItems (item :: rest) = if IsKey item.axiom then unkeyedItems rest else item :: unkeyedItems rest := by
  by_cases key : IsKey item.axiom <;> simp [unkeyedItems, List.filter_cons, key]

theorem unkeyed_spec (context : data_ontology.Context) (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) :
    ∃ res, key_ontology.unkeyed context items index out = .ok res ∧ ∀ out', res = some out' →
      ∃ new, out'.val = out.val ++ new ∧ ItemsMeans.{u,v,w,x} context (unkeyedItems (items.val.drop index.val)) new := by
  rw [key_ontology.unkeyed]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨b, keyRun, keyIff⟩ := is_key_correct items.val[index.val].axiom
    cases b with
    | true =>
      obtain ⟨rest, restRun, restFacts⟩ := unkeyed_spec context items next out
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, keyRun, advance,
        restRun], fun out' h => ?_⟩
      obtain ⟨new, c, means⟩ := restFacts out' h
      rw [nextIndex] at means
      refine ⟨new, c, ?_⟩
      rw [split, unkeyed_cons, if_pos (keyIff.mp rfl)]
      exact means
    | false =>
      obtain ⟨r1, run1, facts1⟩ := encode_axiom_meaning.{u,v,w,x} context items.val[index.val].axiom out
      cases r1 with
      | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, keyRun, run1],
          by simp⟩
      | some out1 =>
        obtain ⟨rest, restRun, restFacts⟩ := unkeyed_spec context items next out1
        refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, keyRun, run1, advance,
          restRun], fun out' h => ?_⟩
        obtain ⟨new2, c2, m2⟩ := restFacts out' h
        obtain ⟨new1, c1, m1, p1, n1⟩ := facts1 out1 rfl
        rw [nextIndex] at m2
        refine ⟨new1 ++ new2, by rw [c2, c1, List.append_assoc], ?_⟩
        have notKey : ¬ IsKey items.val[index.val].axiom := fun key => absurd (keyIff.mpr key) (by simp)
        rw [split, unkeyed_cons, if_neg notKey]
        exact items_means_cons m1 p1 n1 m2
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun out' h => ⟨[], ?_, ?_⟩⟩
    · cases h; simp
    · rw [List.drop_eq_nil_iff.mpr (show items.val.length ≤ index.val by omega)]
      exact items_means_nil context
termination_by items.val.length - index.val
decreasing_by all_goals omega


/-! ### The whole encoding -/

/-- The encoding of a closure with keys for a capacity: the encoding's own
    axioms (the data encoding of no axioms), the encodings of the axioms other
    than keys, `N ⊑ ¬D`, the named individuals of `nodes` in `N`,
    `N ⊑ ∃mark.Self` when a key is not counted, and the axioms of the keys. -/
theorem encode_meaning (context : data_ontology.Context) (good : Good context) (capacity : Usize)
    (capSmall : capacity.val < Usize.max / 16) (items : alloc.vec.Vec AnnotatedAxiom)
    (nodes : alloc.vec.Vec Individual) (counting : Bool) :
    ∃ res, key_ontology.encode context capacity items nodes counting = .ok res ∧ ∀ enc, res = some enc →
      FineCuts context.cuts.val ∧ ValuesFit context ∧
      ∃ (new0 newU newK : List AnnotatedAxiom) (bits : Usize) (order : List Usize),
        ItemsMeans.{u,v,w,x} context [] new0 ∧ ItemsMeans.{u,v,w,x} context (unkeyedItems items.val) newU ∧
        context.values.val.length ≤ 2 ^ bits.val ∧
        (context.kinds.ordered = true → Ordered context.cuts.val (order.map (·.val)) ∧ PointsNamed context order 1) ∧
        (∀ p ∈ context.data.val, ∃ role, data_ontology.data_role context p = .ok (some role)) ∧
        TruthsKnown context ∧
        (∀ a ∈ nodes.val, Plain a) ∧
        KeysMeans.{w,x} context items.val (namesOf nodes.val) counting newK ∧
        ∀ {Object' : Type w} {Value' : Type x} (J : Interpretation Object' Value'),
          ((∀ b ∈ enc.val, satisfies J b.axiom) ↔
            ((∀ b ∈ new0, satisfies J b.axiom) ∧ Frame context capacity.val bits order J) ∧
            (∀ b ∈ newU, satisfies J b.axiom) ∧
            (∀ y, J.classes keyClass y → ¬ J.classes dataClass y) ∧
            (∀ a ∈ nodes.val, NodeHeld J a) ∧
            (SharedIn items.val counting → ∀ y, J.classes keyClass y → J.objectProperties markRole y y) ∧
            (DataSharedIn items.val counting → ∀ y, J.classes dataClass y → J.objectProperties markRole y y) ∧
            (∀ b ∈ newK, satisfies J b.axiom)) := by
  rw [key_ontology.encode]
  obtain ⟨r0, run0, facts0⟩ := Rowl.DataStructure.encode_meaning.{u,v,w,x} context good capacity capSmall
    (alloc.vec.Vec.new AnnotatedAxiom)
  cases r0 with
  | none => exact ⟨none, by simp [run0], by simp⟩
  | some out =>
  obtain ⟨fine, fit, new0, bits, order, means0, enough, sorted, roles, known, iff0⟩ := facts0 out rfl
  obtain ⟨r1, run1, facts1⟩ := unkeyed_spec.{u,v,w,x} context items 0#usize out
  cases r1 with
  | none => exact ⟨none, by simp [run0, run1], by simp⟩
  | some out1 =>
  obtain ⟨newU, c1, meansU⟩ := facts1 out1 rfl
  obtain ⟨r2, run2, c2⟩ := push_spec out1 (.SubClassOf (.Class keyClass) (.ObjectComplementOf (.Class dataClass)))
  cases r2 with
  | none => exact ⟨none, by simp [run0, run1, named_class_eq, object_class_eq, run2], by simp⟩
  | some out2 =>
  obtain ⟨r3, run3, facts3⟩ := named_assertions_spec.{w,x} nodes 0#usize out2
  cases r3 with
  | none => exact ⟨none, by simp [run0, run1, named_class_eq, object_class_eq, run2, run3], by simp⟩
  | some out3 =>
  obtain ⟨newN, c3, plainN, meansN⟩ := facts3 out3 rfl
  obtain ⟨r4, run4, facts4⟩ := marks_spec.{w,x} items counting out3
  cases r4 with
  | none => exact ⟨none, by simp [run0, run1, named_class_eq, object_class_eq, run2, run3, run4], by simp⟩
  | some out4 =>
  obtain ⟨newM, c4, meansM⟩ := facts4 out4 rfl
  obtain ⟨r5, run5, facts5⟩ := keys_from_spec.{w,x} context items nodes 0#usize counting out4
  refine ⟨r5, by simp [run0, run1, named_class_eq, object_class_eq, run2, run3, run4, run5], fun enc h => ?_⟩
  obtain ⟨newK, c5, meansK⟩ := facts5 enc h
  simp only [zero_val, List.drop_zero] at meansU plainN meansN meansK
  refine ⟨fine, fit, new0, newU, newK, bits, order, by simpa [new_val] using means0, meansU, enough, sorted, roles,
    known, plainN, meansK, fun J => ?_⟩
  have apartIff : (∀ b ∈ [bare (.SubClassOf (.Class keyClass) (.ObjectComplementOf (.Class dataClass)))],
      satisfies J b.axiom) ↔ ∀ y, J.classes keyClass y → ¬ J.classes dataClass y := by
    simp [bare, satisfies, classDenote]
  rw [c5, c4, c3, c2 out2 rfl, c1]
  simp only [List.forall_mem_append, iff0 J, meansN J, meansM J]
  rw [show [⟨alloc.vec.Vec.new Annotation, .SubClassOf (.Class keyClass) (.ObjectComplementOf (.Class dataClass))⟩] =
    [bare (.SubClassOf (.Class keyClass) (.ObjectComplementOf (.Class dataClass)))] from rfl, apartIff]
  constructor
  · rintro ⟨⟨⟨⟨⟨base, unkeyed⟩, apart⟩, held⟩, marks, dataMarks⟩, keys⟩
    exact ⟨base, unkeyed, apart, held, marks, dataMarks, keys⟩
  · rintro ⟨base, unkeyed, apart, held, marks, dataMarks, keys⟩
    exact ⟨⟨⟨⟨⟨base, unkeyed⟩, apart⟩, held⟩, marks, dataMarks⟩, keys⟩


/-! ### The individuals a closure names -/

/-- `final` has exactly the individuals of `nodes` and of `xs`, and room for one
    more node. -/
def Grows (nodes final : alloc.vec.Vec Individual) (xs : List Individual) : Prop :=
  (∀ b ∈ final.val, b ∈ nodes.val ∨ b ∈ xs) ∧ (∀ b ∈ nodes.val, b ∈ final.val) ∧ (∀ b ∈ xs, b ∈ final.val) ∧
    final.val.length ≤ Usize.max - 1

theorem grows_self {nodes : alloc.vec.Vec Individual} (room : nodes.val.length ≤ Usize.max - 1) :
    Grows nodes nodes [] :=
  ⟨fun _ m => .inl m, fun _ m => m, by simp, room⟩

theorem grows_trans {n1 n2 n3 : alloc.vec.Vec Individual} {xs ys : List Individual} (h1 : Grows n1 n2 xs)
    (h2 : Grows n2 n3 ys) : Grows n1 n3 (xs ++ ys) := by
  obtain ⟨sub1, keep1, add1, _⟩ := h1
  obtain ⟨sub2, keep2, add2, room2⟩ := h2
  refine ⟨fun b m => ?_, fun b m => keep2 b (keep1 b m), fun b m => ?_, room2⟩
  · rcases sub2 b m with old | new
    · rcases sub1 b old with o | n
      · exact .inl o
      · exact .inr (List.mem_append_left _ n)
    · exact .inr (List.mem_append_right _ new)
  · rcases List.mem_append.mp m with early | late
    · exact keep2 b (add1 b early)
    · exact add2 b late

theorem grows_congr {nodes final : alloc.vec.Vec Individual} {xs ys : List Individual} (h : Grows nodes final xs)
    (same : ∀ b, b ∈ xs ↔ b ∈ ys) : Grows nodes final ys :=
  ⟨fun b m => (h.1 b m).imp id (same b).mp, h.2.1, fun b m => h.2.2.1 b ((same b).mpr m), h.2.2.2⟩

theorem grows_room {nodes final : alloc.vec.Vec Individual} {xs : List Individual} (h : Grows nodes final xs) :
    final.val.length ≤ Usize.max - 1 := h.2.2.2

theorem intern_grows (nodes : alloc.vec.Vec Individual) (a : Individual) (room : nodes.val.length ≤ Usize.max - 1) :
    ∃ result, alc_ontology.intern nodes a = .ok result ∧ ∀ final, result = some final → Grows nodes final [a] := by
  obtain ⟨p, run, value⟩ := Rowl.AlcOntology.position_of nodes a
  rw [alc_ontology.intern]
  by_cases present : a ∈ nodes.val
  · have nonzero : ¬ p.val = 0 := by
      intro zero
      obtain ⟨_, positive, _⟩ := Rowl.AlcOntology.positionOf_present nodes.val a present
      rw [← value, zero] at positive
      simp at positive
    refine ⟨some nodes, by simp [run, nonzero], fun final same => ?_⟩
    cases same
    exact ⟨fun b m => .inl m, fun b m => m, by simpa using present, room⟩
  · have zero : p = 0#usize := by
      apply UScalar.eq_of_val_eq
      rw [value]
      simpa [Rowl.AlcOntology.PositionOf] using Rowl.AlcOntology.positionFrom_absent nodes.val a 0 present
    obtain ⟨limit, limitRun, limitValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := core.num.Usize.MAX) (y := 1#usize) (by simp [usize_max_val]; scalar_tac))
    have limitIs : limit.val = Usize.max - 1 := by simp [usize_max_val] at limitValue; exact limitValue.1
    by_cases fits : nodes.val.length < Usize.max - 1
    · obtain ⟨appended, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec nodes a (by omega))
      refine ⟨some appended, by simp [run, zero, limitRun, limitIs, fits,
        Rowl.AlcOntology.copy_individual_identity, push], fun final same => ?_⟩
      cases same
      rw [Grows, contents]
      refine ⟨fun b m => ?_, fun b m => List.mem_append_left _ m, by simp, by simp; omega⟩
      rcases List.mem_append.mp m with old | new
      · exact .inl old
      · exact .inr new
    · exact ⟨none, by simp [run, zero, limitRun, limitIs, fits], by simp⟩

theorem list_individuals_grows (nodes individuals : alloc.vec.Vec Individual) (index : Usize)
    (room : nodes.val.length ≤ Usize.max - 1) :
    ∃ res, data_ontology.list_individuals nodes individuals index = .ok res ∧ ∀ final, res = some final →
      Grows nodes final (individuals.val.drop index.val) := by
  rw [data_ontology.list_individuals]
  by_cases inside : index.val < individuals.val.length
  · have lookup : individuals.index_usize index = .ok individuals.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, facts1⟩ := intern_grows nodes individuals.val[index.val] room
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some n1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have g1 := facts1 n1 rfl
      obtain ⟨rest, restRun, restFacts⟩ := list_individuals_grows n1 individuals next (grows_room g1)
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance,
        restRun], fun final h => ?_⟩
      have tail := restFacts final h
      rw [nextIndex] at tail
      rw [split]
      exact grows_congr (grows_trans g1 tail) (by simp)
  · exact ⟨some nodes, by simp [UScalar.lt_equiv, inside], fun final h => by
      cases h
      exact grows_congr (grows_self room) (by simp [List.drop_eq_nil_iff.mpr (show individuals.val.length ≤ index.val by omega)])⟩
termination_by individuals.val.length - index.val
decreasing_by omega

theorem classes_individuals_grows (nodes : alloc.vec.Vec Individual) (classes : alloc.vec.Vec ClassExpression)
    (index : Usize) (room : nodes.val.length ≤ Usize.max - 1)
    (each : ∀ e ∈ classes.val, ∀ nodes : alloc.vec.Vec Individual, nodes.val.length ≤ Usize.max - 1 →
      ∃ res, data_ontology.class_individuals nodes e = .ok res ∧
        ∀ final, res = some final → Grows nodes final (classIndividuals e)) :
    ∃ res, data_ontology.classes_individuals nodes classes index = .ok res ∧ ∀ final, res = some final →
      Grows nodes final ((classes.val.drop index.val).flatMap classIndividuals) := by
  rw [data_ontology.classes_individuals]
  by_cases inside : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, facts1⟩ := each _ (List.getElem_mem inside) nodes room
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some n1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have g1 := facts1 n1 rfl
      obtain ⟨rest, restRun, restFacts⟩ := classes_individuals_grows n1 classes next (grows_room g1) each
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance,
        restRun], fun final h => ?_⟩
      have tail := restFacts final h
      rw [nextIndex] at tail
      rw [split, List.flatMap_cons]
      exact grows_trans g1 tail
  · exact ⟨some nodes, by simp [UScalar.lt_equiv, inside], fun final h => by
      cases h
      exact grows_congr (grows_self room) (by simp [List.drop_eq_nil_iff.mpr (show classes.val.length ≤ index.val by omega)])⟩
termination_by classes.val.length - index.val
decreasing_by omega

theorem members_individuals_grows (nodes : alloc.vec.Vec Individual) (members : AtLeastTwo ClassExpression)
    (room : nodes.val.length ≤ Usize.max - 1)
    (each : ∀ e ∈ members.elements, ∀ nodes : alloc.vec.Vec Individual, nodes.val.length ≤ Usize.max - 1 →
      ∃ res, data_ontology.class_individuals nodes e = .ok res ∧
        ∀ final, res = some final → Grows nodes final (classIndividuals e)) :
    ∃ res, data_ontology.members_individuals nodes members = .ok res ∧ ∀ final, res = some final →
      Grows nodes final (members.elements.flatMap classIndividuals) := by
  rw [data_ontology.members_individuals]
  obtain ⟨r1, run1, facts1⟩ := each members.first (by simp [AtLeastTwo.elements]) nodes room
  cases r1 with
  | none => exact ⟨none, by simp [run1], by simp⟩
  | some n1 =>
    have g1 := facts1 n1 rfl
    obtain ⟨r2, run2, facts2⟩ := each members.second (by simp [AtLeastTwo.elements]) n1 (grows_room g1)
    cases r2 with
    | none => exact ⟨none, by simp [run1, run2], by simp⟩
    | some n2 =>
      have g2 := facts2 n2 rfl
      obtain ⟨r3, run3, facts3⟩ := classes_individuals_grows n2 members.rest 0#usize (grows_room g2)
        (fun e mem => each e (by simp [AtLeastTwo.elements, mem]))
      refine ⟨r3, by simp [run1, run2, run3], fun final h => ?_⟩
      have tail := facts3 final h
      simp only [zero_val, List.drop_zero] at tail
      exact grows_congr (grows_trans (grows_trans g1 g2) tail) (by simp [AtLeastTwo.elements, List.append_assoc])

theorem class_individuals_grows (nodes : alloc.vec.Vec Individual) (c : ClassExpression)
    (room : nodes.val.length ≤ Usize.max - 1) :
    ∃ res, data_ontology.class_individuals nodes c = .ok res ∧ ∀ final, res = some final →
      Grows nodes final (classIndividuals c) := by
  have bound : ∀ (xs : AtLeastTwo ClassExpression), ∀ e ∈ xs.elements, sizeOf e < 1 + sizeOf xs := by
    intro xs e mem
    simp only [AtLeastTwo.elements, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · have := first_size xs; omega
    · have := second_size xs; omega
    · have := member_size xs e mem; omega
  have members : ∀ (xs : AtLeastTwo ClassExpression),
      classIndividuals (.ObjectIntersectionOf xs) = xs.elements.flatMap classIndividuals ∧
      classIndividuals (.ObjectUnionOf xs) = xs.elements.flatMap classIndividuals := by
    intro xs
    rw [classIndividuals, classIndividuals]
    simp [AtLeastTwo.elements]
  cases h : c with
  | ObjectIntersectionOf xs =>
    rw [data_ontology.class_individuals, (members xs).1]
    exact members_individuals_grows nodes xs room (fun e mem nodes room => by
      have := bound xs e mem
      exact class_individuals_grows nodes e room)
  | ObjectUnionOf xs =>
    rw [data_ontology.class_individuals, (members xs).2]
    exact members_individuals_grows nodes xs room (fun e mem nodes room => by
      have := bound xs e mem
      exact class_individuals_grows nodes e room)
  | ObjectComplementOf inner =>
    rw [data_ontology.class_individuals, classIndividuals]
    have : sizeOf inner < sizeOf c := by rw [h]; simp
    exact class_individuals_grows nodes inner room
  | ObjectOneOf xs =>
    rw [data_ontology.class_individuals, classIndividuals]
    obtain ⟨r1, run1, facts1⟩ := intern_grows nodes xs.first room
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some n1 =>
      have g1 := facts1 n1 rfl
      obtain ⟨r2, run2, facts2⟩ := list_individuals_grows n1 xs.rest 0#usize (grows_room g1)
      refine ⟨r2, by simp [run1, run2], fun final h => ?_⟩
      have tail := facts2 final h
      simp only [zero_val, List.drop_zero] at tail
      exact grows_congr (grows_trans g1 tail) (by simp [NonEmpty.elements])
  | ObjectSomeValuesFrom _ filler =>
    rw [data_ontology.class_individuals, classIndividuals]
    have : sizeOf filler < sizeOf c := by rw [h]; simp
    exact class_individuals_grows nodes filler room
  | ObjectAllValuesFrom _ filler =>
    rw [data_ontology.class_individuals, classIndividuals]
    have : sizeOf filler < sizeOf c := by rw [h]; simp
    exact class_individuals_grows nodes filler room
  | ObjectHasValue _ a =>
    rw [data_ontology.class_individuals, classIndividuals]
    exact intern_grows nodes a room
  | ObjectMinCardinality _ _ filler | ObjectMaxCardinality _ _ filler | ObjectExactCardinality _ _ filler =>
    cases hf : filler with
    | none =>
      rw [data_ontology.class_individuals, classIndividuals]
      exact ⟨some nodes, rfl, fun final h => by cases h; exact grows_self room⟩
    | some e =>
      rw [data_ontology.class_individuals, classIndividuals]
      have : sizeOf e < sizeOf c := by rw [h, hf]; simp; omega
      exact class_individuals_grows nodes e room
  | Class _ | ObjectHasSelf _ | DataSomeValuesFrom _ _ | DataAllValuesFrom _ _ | DataHasValue _ _
  | DataMinCardinality _ _ _ | DataMaxCardinality _ _ _ | DataExactCardinality _ _ _ =>
    rw [data_ontology.class_individuals.eq_def]
    exact ⟨some nodes, rfl, fun final h => by cases h; exact grows_congr (grows_self room) (by simp [classIndividuals])⟩
termination_by sizeOf c
decreasing_by all_goals (subst_vars; first | omega | (simp_wf; omega))


theorem axiom_individuals_grows (nodes : alloc.vec.Vec Individual) (ax : Axiom)
    (room : nodes.val.length ≤ Usize.max - 1) :
    ∃ res, data_ontology.axiom_individuals nodes ax = .ok res ∧ ∀ final, res = some final →
      Grows nodes final (axiomIndividuals ax) := by
  have keep : ∃ res, (.ok (some nodes) : Result (Option (alloc.vec.Vec Individual))) = .ok res ∧
      ∀ final, res = some final → Grows nodes final [] := ⟨some nodes, rfl, fun final h => by cases h; exact grows_self room⟩
  cases ax with
  | SubClassOf a b =>
    rw [data_ontology.axiom_individuals]
    obtain ⟨r1, run1, facts1⟩ := class_individuals_grows nodes a room
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some n1 =>
      have g1 := facts1 n1 rfl
      obtain ⟨r2, run2, facts2⟩ := class_individuals_grows n1 b (grows_room g1)
      exact ⟨r2, by simp [run1, run2], fun final h => grows_trans g1 (facts2 final h)⟩
  | EquivalentClasses xs | DisjointClasses xs | DisjointUnion _ xs =>
    rw [data_ontology.axiom_individuals]
    exact members_individuals_grows nodes xs room (fun e _ nodes room => class_individuals_grows nodes e room)
  | ObjectPropertyDomain _ e | ObjectPropertyRange _ e | DataPropertyDomain _ e =>
    rw [data_ontology.axiom_individuals]
    exact class_individuals_grows nodes e room
  | SameIndividual xs | DifferentIndividuals xs =>
    rw [data_ontology.axiom_individuals]
    obtain ⟨r1, run1, facts1⟩ := intern_grows nodes xs.first room
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some n1 =>
      have g1 := facts1 n1 rfl
      obtain ⟨r2, run2, facts2⟩ := intern_grows n1 xs.second (grows_room g1)
      cases r2 with
      | none => exact ⟨none, by simp [run1, run2], by simp⟩
      | some n2 =>
        have g2 := facts2 n2 rfl
        obtain ⟨r3, run3, facts3⟩ := list_individuals_grows n2 xs.rest 0#usize (grows_room g2)
        refine ⟨r3, by simp [run1, run2, run3], fun final h => ?_⟩
        have tail := facts3 final h
        simp only [zero_val, List.drop_zero] at tail
        exact grows_congr (grows_trans (grows_trans g1 g2) tail) (by simp [axiomIndividuals, AtLeastTwo.elements])
  | ClassAssertion e a =>
    rw [data_ontology.axiom_individuals]
    obtain ⟨r1, run1, facts1⟩ := intern_grows nodes a room
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some n1 =>
      have g1 := facts1 n1 rfl
      obtain ⟨r2, run2, facts2⟩ := class_individuals_grows n1 e (grows_room g1)
      exact ⟨r2, by simp [run1, run2], fun final h => grows_congr (grows_trans g1 (facts2 final h))
        (by simp [axiomIndividuals])⟩
  | ObjectPropertyAssertion _ a b | NegativeObjectPropertyAssertion _ a b =>
    rw [data_ontology.axiom_individuals]
    obtain ⟨r1, run1, facts1⟩ := intern_grows nodes a room
    cases r1 with
    | none => exact ⟨none, by simp [run1], by simp⟩
    | some n1 =>
      have g1 := facts1 n1 rfl
      obtain ⟨r2, run2, facts2⟩ := intern_grows n1 b (grows_room g1)
      exact ⟨r2, by simp [run1, run2], fun final h => grows_congr (grows_trans g1 (facts2 final h))
        (by simp [axiomIndividuals])⟩
  | DataPropertyAssertion _ a _ | NegativeDataPropertyAssertion _ a _ =>
    rw [data_ontology.axiom_individuals]
    exact intern_grows nodes a room
  | Declaration _ | SubObjectPropertyOf _ _ | EquivalentObjectProperties _ | DisjointObjectProperties _
  | InverseObjectProperties _ _ | FunctionalObjectProperty _ | InverseFunctionalObjectProperty _
  | ReflexiveObjectProperty _ | IrreflexiveObjectProperty _ | SymmetricObjectProperty _
  | AsymmetricObjectProperty _ | TransitiveObjectProperty _ | SubDataPropertyOf _ _ | EquivalentDataProperties _
  | DisjointDataProperties _ | DataPropertyRange _ _ | FunctionalDataProperty _ | DatatypeDefinition _ _
  | HasKey _ _ _ | AnnotationAssertion _ _ _ | SubAnnotationPropertyOf _ _ | AnnotationPropertyDomain _ _
  | AnnotationPropertyRange _ _ =>
    rw [data_ontology.axiom_individuals]
    exact keep

theorem items_individuals_grows (nodes : alloc.vec.Vec Individual) (items : alloc.vec.Vec AnnotatedAxiom)
    (index : Usize) (room : nodes.val.length ≤ Usize.max - 1) :
    ∃ res, data_ontology.items_individuals nodes items index = .ok res ∧ ∀ final, res = some final →
      Grows nodes final ((items.val.drop index.val).flatMap (fun i => axiomIndividuals i.axiom)) := by
  rw [data_ontology.items_individuals]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, facts1⟩ := axiom_individuals_grows nodes items.val[index.val].axiom room
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some n1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have g1 := facts1 n1 rfl
      obtain ⟨rest, restRun, restFacts⟩ := items_individuals_grows n1 items next (grows_room g1)
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance,
        restRun], fun final h => ?_⟩
      have tail := restFacts final h
      rw [nextIndex] at tail
      rw [split, List.flatMap_cons]
      exact grows_trans g1 tail
  · exact ⟨some nodes, by simp [UScalar.lt_equiv, inside], fun final h => by
      cases h
      exact grows_congr (grows_self room) (by simp [List.drop_eq_nil_iff.mpr (show items.val.length ≤ index.val by omega)])⟩
termination_by items.val.length - index.val
decreasing_by omega

theorem key_class_individuals_grows (nodes : alloc.vec.Vec Individual) (ax : Axiom)
    (room : nodes.val.length ≤ Usize.max - 1) :
    ∃ res, key_ontology.key_class_individuals nodes ax = .ok res ∧ ∀ final, res = some final →
      Grows nodes final (keyIndividuals ax) := by
  cases ax with
  | HasKey e _ _ =>
    rw [key_ontology.key_class_individuals]
    exact class_individuals_grows nodes e room
  | _ =>
    rw [key_ontology.key_class_individuals]
    exact ⟨some nodes, rfl, fun final h => by cases h; exact grows_self room⟩

theorem key_individuals_grows (nodes : alloc.vec.Vec Individual) (items : alloc.vec.Vec AnnotatedAxiom)
    (index : Usize) (room : nodes.val.length ≤ Usize.max - 1) :
    ∃ res, key_ontology.key_individuals nodes items index = .ok res ∧ ∀ final, res = some final →
      Grows nodes final ((items.val.drop index.val).flatMap (fun i => keyIndividuals i.axiom)) := by
  rw [key_ontology.key_individuals]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨r1, run1, facts1⟩ := key_class_individuals_grows nodes items.val[index.val].axiom room
    cases r1 with
    | none => exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1], by simp⟩
    | some n1 =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have g1 := facts1 n1 rfl
      obtain ⟨rest, restRun, restFacts⟩ := key_individuals_grows n1 items next (grows_room g1)
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run1, advance,
        restRun], fun final h => ?_⟩
      have tail := restFacts final h
      rw [nextIndex] at tail
      rw [split, List.flatMap_cons]
      exact grows_trans g1 tail
  · exact ⟨some nodes, by simp [UScalar.lt_equiv, inside], fun final h => by
      cases h
      exact grows_congr (grows_self room) (by simp [List.drop_eq_nil_iff.mpr (show items.val.length ≤ index.val by omega)])⟩
termination_by items.val.length - index.val
decreasing_by omega

/-- The individuals the actual kernel collects for a closure with keys are
    exactly the individuals the closure names. -/
theorem closure_nodes (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ r1, data_ontology.items_individuals (alloc.vec.Vec.new Individual) items 0#usize = .ok r1 ∧
      ∀ n1, r1 = some n1 → ∃ r2, key_ontology.key_individuals n1 items 0#usize = .ok r2 ∧
        ∀ nodes, r2 = some nodes → ∀ b, b ∈ nodes.val ↔ b ∈ closureIndividuals items.val := by
  obtain ⟨r1, run1, facts1⟩ := items_individuals_grows (alloc.vec.Vec.new Individual) items 0#usize
    (by simp [new_val])
  refine ⟨r1, run1, fun n1 h1 => ?_⟩
  have g1 := facts1 n1 h1
  obtain ⟨r2, run2, facts2⟩ := key_individuals_grows n1 items 0#usize (grows_room g1)
  refine ⟨r2, run2, fun nodes h2 b => ?_⟩
  have g := grows_trans g1 (facts2 nodes h2)
  simp only [zero_val, List.drop_zero] at g
  obtain ⟨sub, _, add, _⟩ := g
  constructor
  · intro mem
    rcases sub b mem with absurdity | inside
    · simp [new_val] at absurdity
    · simp only [closureIndividuals, List.mem_flatMap, List.mem_append] at inside ⊢
      rcases inside with ⟨i, iMem, inI⟩ | ⟨i, iMem, inI⟩
      · exact ⟨i, iMem, .inl inI⟩
      · exact ⟨i, iMem, .inr inI⟩
  · intro mem
    apply add
    simp only [closureIndividuals, List.mem_flatMap, List.mem_append] at mem ⊢
    obtain ⟨i, iMem, inI | inI⟩ := mem
    · exact .inl ⟨i, iMem, inI⟩
    · exact .inr ⟨i, iMem, inI⟩

end Rowl.KeyEncoding
