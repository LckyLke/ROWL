import Rowl.Vocabulary
import Rowl.Indexing
import Rowl.Keys
import Rowl.Arity
import Rowl.TopData
import Rowl.DatatypeRestrictions
import Rowl.RoleClosure
import Rowl.RoleOrder
import Rowl.AnonymousRestrictions

/-!
OWL 2 DL syntactic validity of a supplied complete axiom closure.

`OwlDlValid` is the conjunction of the independent specifications of the
component checkers, in the order of the condition lists of the 2012 Structural
Specification, Section 3: nonempty keys (§9.5) and structural arities; the
reserved vocabulary (§3.1, §5.1–5.6); the typing constraints (§5.8.1) with the
built-in declarations of Table 5; and the global restrictions of §11.2 with the
positions of defined datatypes (§9.4). The supplied axioms are the complete
axiom closure: imports are not resolved, and anonymous individuals are already
standardized apart. Lexical forms in the lexical spaces of their datatypes
(§5.7) and facet values in the facet spaces of their datatypes (§7.5) need the
normative datatype map and are not part of `OwlDlValid`.

`check_ontology_total_correct` proves that `dl_validity::check_ontology` returns
`Valid` exactly for `OwlDlValid` ontologies and otherwise the first violated
restriction, with the evidence of its component checker and the proof that
every earlier restriction holds. `check_typing` decides the typing constraints
on exact IRI spellings, without a symbol-count limit; `check_declarations`
decides declaration consistency (§5.8.2), which OWL 2 DL does not require.
`strip_annotations_models` and its corollaries prove that annotations have no
logical effect.
-/
namespace Rowl.DlValidity
open Aeneas Aeneas.Std RowlRust RowlRust.model RowlRust.typing RowlRust.collection RowlRust.dl_validity
open Rowl.Collection (Row)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## Kinds, bytes and declarations read from the axioms -/

private theorem same_kind_spec (a b : EntityKind) :
    dl_validity.same_kind a b = .ok (decide (a = b)) := by
  cases a <;> cases b <;> simp [dl_validity.same_kind]

private theorem forbidden_symm (a b : EntityKind) :
    Rowl.Typing.Forbidden a b ↔ Rowl.Typing.Forbidden b a := by
  cases a <;> cases b <;> simp [Rowl.Typing.Forbidden]

private theorem forbidden_irrefl (a : EntityKind) : ¬ Rowl.Typing.Forbidden a a := by
  cases a <;> simp [Rowl.Typing.Forbidden]

private theorem forbidden_spec (a b : EntityKind) :
    dl_validity.forbidden a b = .ok (decide (Rowl.Typing.Forbidden a b)) := by
  cases a <;> cases b <;> simp [dl_validity.forbidden, Rowl.Typing.Forbidden]

private theorem take_last (l : List U8) (i : Nat) (h : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp

private theorem same_before_spec (left right : alloc.vec.Vec U8) (stop : Usize)
    (hl : stop.val ≤ left.val.length) (hr : stop.val ≤ right.val.length) :
    dl_validity.same_before left right stop =
      .ok (decide (left.val.take stop.val = right.val.take stop.val)) := by
  rw [dl_validity.same_before]
  by_cases positive : 0 < stop.val
  · obtain ⟨last, back, lastValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := stop) (y := 1#usize) (by scalar_tac))
    have lastIndex : last.val = stop.val - 1 := by simp at lastValue; omega
    have il : last.val < left.val.length := by omega
    have ir : last.val < right.val.length := by omega
    have lookl : left.index_usize last = .ok left.val[last.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem il]
    have lookr : right.index_usize last = .ok right.val[last.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem ir]
    have positive' : (0#usize) < stop := by simp only [UScalar.lt_equiv]; simpa using positive
    have stopEq : stop.val = last.val + 1 := by omega
    have takeL := take_last left.val last.val il
    have takeR := take_last right.val last.val ir
    have lengths : (left.val.take last.val).length = (right.val.take last.val).length := by
      simp only [List.length_take]; omega
    have key : (left.val.take stop.val = right.val.take stop.val) ↔
        (left.val.take last.val = right.val.take last.val ∧ left.val[last.val] = right.val[last.val]) := by
      rw [stopEq, takeL, takeR]
      constructor
      · intro same
        have parts := List.append_inj same lengths
        simp only [List.cons.injEq, and_true] at parts
        exact parts
      · rintro ⟨front, last⟩
        rw [front, last]
    simp only [positive', ↓reduceIte, back, bind_ok, alloc.vec.Vec.index_slice_index, lookl, lookr]
    by_cases heads : left.val[last.val] = right.val[last.val]
    · have ih := same_before_spec left right last (by omega) (by omega)
      simp only [heads, ↓reduceIte, ih, key, and_true]
    · simp only [heads, ↓reduceIte, key, and_false, decide_false]
  · have zero : stop.val = 0 := by omega
    have notPositive : ¬ (0#usize) < stop := by simp only [UScalar.lt_equiv]; simp [zero]
    simp [notPositive, zero]
termination_by stop.val
decreasing_by omega

/-- Exact byte equality of two IRI spellings, compared from the last byte. -/
theorem same_bytes_spec (left right : alloc.vec.Vec U8) :
    dl_validity.same_bytes left right = .ok (decide (left.val = right.val)) := by
  rw [dl_validity.same_bytes]
  by_cases h : left.val.length = right.val.length
  · have lengths : alloc.vec.Vec.len left = alloc.vec.Vec.len right :=
      UScalar.eq_of_val_eq (by simpa [alloc.vec.Vec.len_val] using h)
    have whole := same_before_spec left right (alloc.vec.Vec.len left)
      (by simp [alloc.vec.Vec.len_val]) (by simp [alloc.vec.Vec.len_val, h])
    simp only [eq_true lengths, ↓reduceIte, whole]
    rw [alloc.vec.Vec.len_val, alloc.vec.Vec.length, List.take_length, h, List.take_length]
  · have unequal : left.val ≠ right.val := fun eq => h (congrArg List.length eq)
    have lengths : ¬ alloc.vec.Vec.len left = alloc.vec.Vec.len right := by
      intro eq
      apply h
      have := congrArg UScalar.val eq
      simpa [alloc.vec.Vec.len_val] using this
    simp [lengths, unequal]

/-- The IRI of a declared entity. -/
private def entityIri : Entity → Iri
  | .Class c => c.iri
  | .Datatype d => d.iri
  | .ObjectProperty p => p.iri
  | .DataProperty p => p.iri
  | .AnnotationProperty p => p.iri
  | .NamedIndividual i => i.iri

private theorem entity_iri_spec (entity : Entity) :
    dl_validity.entity_iri entity = .ok (entityIri entity) := by
  cases entity <;> rfl

private theorem entity_uses_eq (entity : Entity) :
    Rowl.Collection.entityUses entity = [(entityIri entity, Rowl.Typing.kindOf entity)] := by
  cases entity <;> rfl

/-- A row declares the spelling of `iri` as `kind`. -/
private def DeclaresAs (iri : Iri) (kind : EntityKind) (d : Row) : Prop :=
  d.2 = kind ∧ d.1.spelling.val = iri.spelling.val

private theorem item_declares_spec (item : AnnotatedAxiom) (iri : Iri) (kind : EntityKind) :
    dl_validity.item_declares item iri kind =
      .ok (decide (∃ d ∈ Rowl.Collection.declarationUses item, DeclaresAs iri kind d)) := by
  unfold dl_validity.item_declares
  cases h : item.axiom
  case Declaration entity =>
    simp only [h, dl_validity.entity_declares, Rowl.Typing.entity_kind_total_correct, bind_ok,
      same_kind_spec, entity_iri_spec, same_bytes_spec, Rowl.Collection.declarationUses,
      entity_uses_eq, DeclaresAs]
    by_cases k : Rowl.Typing.kindOf entity = kind <;> simp [k]
  all_goals simp [h, Rowl.Collection.declarationUses]

private theorem drop_rows (axioms : alloc.vec.Vec AnnotatedAxiom) (index : Nat)
    (inside : index < axioms.val.length) (f : AnnotatedAxiom → List Row) :
    (axioms.val.drop index).flatMap f = f axioms.val[index] ++ (axioms.val.drop (index + 1)).flatMap f := by
  rw [List.drop_eq_getElem_cons inside, List.flatMap_cons]

private theorem declared_from_spec (axioms : alloc.vec.Vec AnnotatedAxiom) (iri : Iri)
    (kind : EntityKind) (index : Usize) :
    dl_validity.declared_from axioms iri kind index =
      .ok (decide (∃ d ∈ (axioms.val.drop index.val).flatMap Rowl.Collection.declarationUses,
        DeclaresAs iri kind d)) := by
  rw [dl_validity.declared_from]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have cond : index < alloc.vec.Vec.len axioms := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    have size := axioms.property
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextval : next.val = index.val + 1 := by simpa using hv
    have ih := declared_from_spec axioms iri kind next
    have rows := drop_rows axioms index.val inside Rowl.Collection.declarationUses
    simp only [cond, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup, bind_ok, item_declares_spec]
    split
    · rename_i decided
      have here := of_decide_eq_true decided
      have found : ∃ d ∈ (axioms.val.drop index.val).flatMap Rowl.Collection.declarationUses,
          DeclaresAs iri kind d := by
        obtain ⟨d, member, declares⟩ := here
        exact ⟨d, by rw [rows]; exact List.mem_append_left _ member, declares⟩
      simp only [found, decide_true]
    · rename_i decided
      have here := of_decide_eq_false (Bool.of_not_eq_true decided)
      have same : (∃ d ∈ (axioms.val.drop next.val).flatMap Rowl.Collection.declarationUses,
          DeclaresAs iri kind d) ↔ ∃ d ∈ (axioms.val.drop index.val).flatMap Rowl.Collection.declarationUses,
          DeclaresAs iri kind d := by
        rw [rows, nextval]
        constructor
        · rintro ⟨d, member, declares⟩
          exact ⟨d, List.mem_append_right _ member, declares⟩
        · rintro ⟨d, member, declares⟩
          rcases List.mem_append.mp member with member | member
          · exact False.elim (here ⟨d, member, declares⟩)
          · exact ⟨d, member, declares⟩
      simp only [hn, bind_ok, ih]
      congr 1
      exact decide_eq_decide.mpr same
  · have cond : ¬ index < alloc.vec.Vec.len axioms := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp only [cond, ↓reduceIte, empty, List.flatMap_nil, List.not_mem_nil, false_and, exists_false,
      decide_false]
termination_by axioms.val.length - index.val
decreasing_by omega

private theorem builtin_role_spec (iri : Iri) (kind : EntityKind) :
    dl_validity.builtin_role iri kind =
      .ok (decide (Rowl.Builtins.role iri.spelling.val = some kind)) := by
  unfold dl_validity.builtin_role
  rw [Rowl.Builtins.builtin_kind_total_correct]
  cases h : Rowl.Builtins.role iri.spelling.val <;> simp [same_kind_spec]

private theorem conflicting_role_spec (kind role : EntityKind) :
    dl_validity.conflicting_role kind role =
      .ok (if Rowl.Typing.Forbidden kind role then some role else none) := by
  unfold dl_validity.conflicting_role
  by_cases f : Rowl.Typing.Forbidden kind role <;> simp [forbidden_spec, f]

/-- The built-in role of `iri` (Table 5), if it is forbidden together with `kind`. -/
private noncomputable def builtinConflict (iri : Iri) (kind : EntityKind) : Option EntityKind :=
  match Rowl.Builtins.role iri.spelling.val with
  | some role => if Rowl.Typing.Forbidden kind role then some role else none
  | none => none

private theorem builtin_conflict_spec (iri : Iri) (kind : EntityKind) :
    dl_validity.builtin_conflict iri kind = .ok (builtinConflict iri kind) := by
  unfold dl_validity.builtin_conflict builtinConflict
  rw [Rowl.Builtins.builtin_kind_total_correct]
  cases Rowl.Builtins.role iri.spelling.val <;> simp [conflicting_role_spec]

/-- A row declares the spelling of `iri` with a kind forbidden together with `kind`. -/
private def Clashes (iri : Iri) (kind : EntityKind) (d : Row) : Prop :=
  d.1.spelling.val = iri.spelling.val ∧ Rowl.Typing.Forbidden kind d.2

private noncomputable def firstClash (iri : Iri) (kind : EntityKind) (rows : List Row) : Option EntityKind :=
  (rows.find? (fun d => decide (Clashes iri kind d))).map Prod.snd

private theorem item_conflict_spec (item : AnnotatedAxiom) (iri : Iri) (kind : EntityKind) :
    dl_validity.item_conflict item iri kind =
      .ok (firstClash iri kind (Rowl.Collection.declarationUses item)) := by
  unfold dl_validity.item_conflict
  cases h : item.axiom
  case Declaration entity =>
    simp only [h, entity_iri_spec, same_bytes_spec, Rowl.Typing.entity_kind_total_correct, bind_ok,
      conflicting_role_spec, Rowl.Collection.declarationUses, entity_uses_eq, firstClash, Clashes]
    by_cases same : (entityIri entity).spelling.val = iri.spelling.val <;>
      by_cases f : Rowl.Typing.Forbidden kind (Rowl.Typing.kindOf entity) <;> simp [same, f]
  all_goals simp [h, Rowl.Collection.declarationUses, firstClash]

private theorem first_clash_append (iri : Iri) (kind : EntityKind) (front back : List Row) :
    firstClash iri kind (front ++ back) =
      match firstClash iri kind front with
      | some other => some other
      | none => firstClash iri kind back := by
  unfold firstClash
  rw [List.find?_append]
  cases front.find? (fun d => decide (Clashes iri kind d)) <;> simp

private theorem later_conflict_spec (axioms : alloc.vec.Vec AnnotatedAxiom) (iri : Iri)
    (kind : EntityKind) (index : Usize) :
    dl_validity.later_conflict axioms iri kind index =
      .ok (firstClash iri kind ((axioms.val.drop index.val).flatMap Rowl.Collection.declarationUses)) := by
  rw [dl_validity.later_conflict]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have cond : index < alloc.vec.Vec.len axioms := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    have size := axioms.property
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextval : next.val = index.val + 1 := by simpa using hv
    have ih := later_conflict_spec axioms iri kind next
    have rows := drop_rows axioms index.val inside Rowl.Collection.declarationUses
    rw [nextval] at ih
    simp only [cond, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup, bind_ok, item_conflict_spec]
    rw [rows, first_clash_append]
    cases here : firstClash iri kind (Rowl.Collection.declarationUses axioms.val[index.val]) with
    | some other => simp only [here]
    | none => simp only [here, hn, bind_ok, ih]
  · have cond : ¬ index < alloc.vec.Vec.len axioms := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp only [cond, ↓reduceIte, empty, List.flatMap_nil, firstClash, List.find?_nil, Option.map_none]
termination_by axioms.val.length - index.val
decreasing_by omega

private theorem first_clash_none (iri : Iri) (kind : EntityKind) (rows : List Row)
    (none : firstClash iri kind rows = none) : ∀ d ∈ rows, ¬ Clashes iri kind d := by
  intro d member clash
  unfold firstClash at none
  have missing := List.find?_eq_none.mp (Option.map_eq_none_iff.mp none)
  exact missing d member (by simpa using clash)

private theorem first_clash_some (iri : Iri) (kind : EntityKind) (rows : List Row) (other : EntityKind)
    (found : firstClash iri kind rows = some other) :
    ∃ d ∈ rows, Clashes iri kind d ∧ d.2 = other := by
  unfold firstClash at found
  obtain ⟨d, hd, same⟩ := Option.map_eq_some_iff.mp found
  have member := List.mem_of_find?_eq_some hd
  have clash := List.find?_some hd
  exact ⟨d, member, by simpa using clash, same⟩

/-! ## The typing constraints on declaration and use rows (§5.8.1) -/

/-- A declaration row conflicts with `other` (§5.8.1): the two kinds are a class
    and a datatype or two different kinds of property, and `other` is the
    built-in role of the row's IRI (Table 5) or the kind of a declaration of the
    same IRI among `later`. -/
def ConflictWith (later : List Row) (row : Row) (other : EntityKind) : Prop :=
  Rowl.Typing.Forbidden row.2 other ∧
    (Rowl.Builtins.role row.1.spelling.val = some other ∨
      ∃ d ∈ later, d.2 = other ∧ d.1.spelling.val = row.1.spelling.val)

/-- No declaration row conflicts with its built-in role or with a later row. -/
def ConflictFree : List Row → Prop
  | [] => True
  | row :: rest => (∀ other, ¬ ConflictWith rest row other) ∧ ConflictFree rest

/-- The first declaration row that conflicts, and a kind it conflicts with. -/
inductive FirstConflict : List Row → Iri → EntityKind → EntityKind → Prop
  | here {iri kind other rest} : ConflictWith rest (iri, kind) other →
      FirstConflict ((iri, kind) :: rest) iri kind other
  | later {row rest iri kind other} : (∀ k, ¬ ConflictWith rest row k) →
      FirstConflict rest iri kind other → FirstConflict (row :: rest) iri kind other

/-- A use row is declared: it is a named individual and `strict` is false, its
    kind is the built-in role of its IRI (Table 5), or some declaration row
    declares its IRI with its kind. -/
def Declared (strict : Bool) (declarations : List Row) (row : Row) : Prop :=
  (strict = false ∧ row.2 = .NamedIndividual) ∨
    Rowl.Builtins.role row.1.spelling.val = some row.2 ∨
    ∃ d ∈ declarations, d.2 = row.2 ∧ d.1.spelling.val = row.1.spelling.val

/-- The first use row that is not declared. -/
inductive FirstUndeclared (strict : Bool) (declarations : List Row) :
    List Row → Iri → EntityKind → Prop
  | here {iri kind rest} : ¬ Declared strict declarations (iri, kind) →
      FirstUndeclared strict declarations ((iri, kind) :: rest) iri kind
  | later {row rest iri kind} : Declared strict declarations row →
      FirstUndeclared strict declarations rest iri kind →
      FirstUndeclared strict declarations (row :: rest) iri kind

/-- The verdict of `check_typing` against `Rowl.Indexing.RawWellTyped`, the
    independent typing predicate that `check_ontology_typing` also decides.
    Conflicts are reported before missing declarations. -/
def TypingCorrect (o : RawOntology) : TypingCheck → Prop
  | .Valid => Rowl.Indexing.RawWellTyped o
  | .ConflictingDeclarations iri kind other =>
      FirstConflict (Rowl.Indexing.ontologyDeclarations o) iri kind other ∧
      ¬ Rowl.Indexing.RawWellTyped o
  | .MissingDeclaration iri kind =>
      ConflictFree (Rowl.Indexing.ontologyDeclarations o) ∧
      FirstUndeclared false (Rowl.Indexing.ontologyDeclarations o) (Rowl.Indexing.ontologyUses o) iri kind ∧
      ¬ Rowl.Indexing.RawWellTyped o

/-- Declaration consistency (§5.8.2): every entity occurrence of the axioms,
    named individuals included, has its IRI declared with its kind, explicitly
    or by a built-in declaration of Table 5. OWL 2 DL does not require it. -/
def ConsistentDeclarations (o : RawOntology) : Prop :=
  ∀ row ∈ Rowl.Indexing.ontologyUses o,
    Rowl.Builtins.role row.1.spelling.val = some row.2 ∨
      ∃ d ∈ Rowl.Indexing.ontologyDeclarations o, d.2 = row.2 ∧ d.1.spelling.val = row.1.spelling.val

def DeclarationsCorrect (o : RawOntology) : DeclarationCheck → Prop
  | .Consistent => ConsistentDeclarations o
  | .Undeclared iri kind =>
      FirstUndeclared true (Rowl.Indexing.ontologyDeclarations o) (Rowl.Indexing.ontologyUses o) iri kind ∧
      ¬ ConsistentDeclarations o

private theorem declaration_uses_sub (item : AnnotatedAxiom) :
    ∀ row ∈ Rowl.Collection.declarationUses item, row ∈ Rowl.Collection.annotatedUses item := by
  intro row member
  unfold Rowl.Collection.declarationUses at member
  unfold Rowl.Collection.annotatedUses
  cases h : item.axiom <;> simp only [h] at member <;> simp_all [Rowl.Collection.axiomUses]

private theorem declarations_are_uses (o : RawOntology) :
    ∀ row ∈ Rowl.Indexing.ontologyDeclarations o, row ∈ Rowl.Indexing.ontologyUses o := by
  intro row member
  simp only [Rowl.Indexing.ontologyDeclarations, Rowl.Indexing.ontologyUses, List.mem_flatMap] at member ⊢
  obtain ⟨item, inside, declared⟩ := member
  exact ⟨item, inside, declaration_uses_sub item row declared⟩

private theorem conflict_free_iff (rows : List Row) :
    ConflictFree rows ↔
      (∀ a ∈ rows, ∀ r, Rowl.Builtins.role a.1.spelling.val = some r → ¬ Rowl.Typing.Forbidden a.2 r) ∧
      (∀ a ∈ rows, ∀ b ∈ rows, a.1.spelling.val = b.1.spelling.val → ¬ Rowl.Typing.Forbidden a.2 b.2) := by
  induction rows with
  | nil => simp [ConflictFree]
  | cons row rest ih =>
    simp only [ConflictFree, ih, ConflictWith, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨head, builtins, pairs⟩
      refine ⟨⟨fun r role forbidden => head r ⟨forbidden, .inl role⟩, builtins⟩, ?_, ?_⟩
      · refine ⟨fun _ => forbidden_irrefl _, fun b member same forbidden => ?_⟩
        exact head b.2 ⟨forbidden, .inr ⟨b, member, rfl, same.symm⟩⟩
      · intro a member
        refine ⟨fun same forbidden => ?_, fun b inside same => pairs a member b inside same⟩
        exact head a.2 ⟨(forbidden_symm _ _).mp forbidden, .inr ⟨a, member, rfl, same⟩⟩
    · rintro ⟨⟨rowBuiltin, builtins⟩, ⟨_, rowPairs⟩, pairs⟩
      refine ⟨fun other ⟨forbidden, source⟩ => ?_, builtins, fun a member b inside same =>
        (pairs a member).2 b inside same⟩
      rcases source with role | ⟨d, member, kind, same⟩
      · exact rowBuiltin other role forbidden
      · subst kind
        exact rowPairs d member same.symm forbidden

private theorem mem_implicit (source : List Row) (iri : Iri) (kind : EntityKind) :
    (iri, kind) ∈ Rowl.Indexing.implicitSource source ↔
      ∃ e ∈ source, Rowl.Builtins.role e.1.spelling.val = some kind ∧ e.1 = iri := by
  simp only [Rowl.Indexing.implicitSource, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨e, member, role, found, same, rfl⟩
    exact ⟨e, member, by rw [found], same⟩
  · rintro ⟨e, member, found, same⟩
    exact ⟨e, member, kind, found, same, rfl⟩

/-- The typing predicate on rows is equivalent to conflict freedom of the
    explicit declarations together with every use being declared. -/
theorem raw_well_typed_iff (o : RawOntology) :
    Rowl.Indexing.RawWellTyped o ↔
      ConflictFree (Rowl.Indexing.ontologyDeclarations o) ∧
      ∀ row ∈ Rowl.Indexing.ontologyUses o, Declared false (Rowl.Indexing.ontologyDeclarations o) row := by
  rw [conflict_free_iff]
  unfold Rowl.Indexing.RawWellTyped Rowl.Indexing.RowsWellTyped
  constructor
  · rintro ⟨pairs, declared⟩
    refine ⟨⟨fun a member r role forbidden => ?_, fun a ma b mb same forbidden => ?_⟩, ?_⟩
    · have implicit : (a.1, r) ∈ Rowl.Indexing.implicitSource (Rowl.Indexing.ontologyUses o) :=
        (mem_implicit _ _ _).mpr ⟨a, declarations_are_uses o a member, role, rfl⟩
      exact pairs a.1 a.2 a.1 r (List.mem_append_right _ member) (List.mem_append_left _ implicit) rfl forbidden
    · exact pairs a.1 a.2 b.1 b.2 (List.mem_append_right _ ma) (List.mem_append_right _ mb) same forbidden
    · rintro ⟨iri, kind⟩ member
      by_cases named : kind = .NamedIndividual
      · exact .inl ⟨rfl, named⟩
      · obtain ⟨declaredIri, found, same⟩ := declared iri kind member named
        rcases List.mem_append.mp found with implicit | explicit
        · obtain ⟨e, _, role, rfl⟩ := (mem_implicit _ _ _).mp implicit
          exact .inr (.inl (by simpa [same] using role))
        · exact .inr (.inr ⟨(declaredIri, kind), explicit, rfl, same⟩)
  · rintro ⟨⟨builtins, pairs⟩, declared⟩
    refine ⟨fun iri role other otherRole hx hy same forbidden => ?_, fun iri kind member named => ?_⟩
    · rcases List.mem_append.mp hx with ix | dx <;> rcases List.mem_append.mp hy with iy | dy
      · obtain ⟨e, _, re, rfl⟩ := (mem_implicit _ _ _).mp ix
        obtain ⟨f, _, rf, rfl⟩ := (mem_implicit _ _ _).mp iy
        rw [same, rf] at re
        cases Option.some.inj re
        exact forbidden_irrefl _ forbidden
      · obtain ⟨e, _, re, rfl⟩ := (mem_implicit _ _ _).mp ix
        exact builtins (other, otherRole) dy role (by rw [← same]; exact re) ((forbidden_symm _ _).mp forbidden)
      · obtain ⟨f, _, rf, rfl⟩ := (mem_implicit _ _ _).mp iy
        exact builtins (iri, role) dx otherRole (by rw [same]; exact rf) forbidden
      · exact pairs (iri, role) dx (other, otherRole) dy same forbidden
    · rcases declared (iri, kind) member with ⟨_, individual⟩ | builtin | ⟨d, explicit, sameKind, same⟩
      · exact False.elim (named individual)
      · exact ⟨iri, List.mem_append_left _ ((mem_implicit _ _ _).mpr ⟨(iri, kind), member, builtin, rfl⟩), rfl⟩
      · obtain ⟨d1, d2⟩ := d
        simp only at sameKind same
        subst sameKind
        exact ⟨d1, List.mem_append_right _ explicit, same⟩

private theorem first_conflict_not_free {rows : List Row} {iri : Iri} {kind other : EntityKind}
    (first : FirstConflict rows iri kind other) : ¬ ConflictFree rows := by
  induction first with
  | here conflict => exact fun free => free.1 _ conflict
  | later _ _ ih => exact fun free => ih free.2

private theorem first_undeclared_not_all {strict : Bool} {declarations rows : List Row} {iri : Iri}
    {kind : EntityKind} (first : FirstUndeclared strict declarations rows iri kind) :
    ¬ ∀ row ∈ rows, Declared strict declarations row := by
  induction first with
  | here missing => exact fun all => missing (all _ List.mem_cons_self)
  | later _ _ ih => exact fun all => ih (fun row member => all row (List.mem_cons_of_mem _ member))

private theorem consistent_iff (o : RawOntology) :
    ConsistentDeclarations o ↔
      ∀ row ∈ Rowl.Indexing.ontologyUses o, Declared true (Rowl.Indexing.ontologyDeclarations o) row := by
  unfold ConsistentDeclarations Declared
  simp

/-! ## The typing check and declaration consistency -/

private theorem builtin_conflict_none (iri : Iri) (kind : EntityKind)
    (none : builtinConflict iri kind = none) :
    ∀ r, Rowl.Builtins.role iri.spelling.val = some r → ¬ Rowl.Typing.Forbidden kind r := by
  intro r role forbidden
  unfold builtinConflict at none
  rw [role] at none
  simp [forbidden] at none

private theorem builtin_conflict_some (iri : Iri) (kind other : EntityKind)
    (found : builtinConflict iri kind = some other) :
    Rowl.Builtins.role iri.spelling.val = some other ∧ Rowl.Typing.Forbidden kind other := by
  unfold builtinConflict at found
  cases role : Rowl.Builtins.role iri.spelling.val with
  | none => rw [role] at found; simp at found
  | some r =>
    rw [role] at found
    by_cases f : Rowl.Typing.Forbidden kind r
    · simp [f] at found
      subst found
      exact ⟨rfl, f⟩
    · simp [f] at found

private theorem entity_conflict_correct (axioms : alloc.vec.Vec AnnotatedAxiom) (entity : Entity)
    (index : Usize) :
    ∃ r, dl_validity.entity_conflict axioms entity index = .ok r ∧
      (r = none → ∀ k, ¬ ConflictWith ((axioms.val.drop index.val).flatMap Rowl.Collection.declarationUses)
        (entityIri entity, Rowl.Typing.kindOf entity) k) ∧
      (∀ k, r = some k → ConflictWith ((axioms.val.drop index.val).flatMap Rowl.Collection.declarationUses)
        (entityIri entity, Rowl.Typing.kindOf entity) k) := by
  unfold dl_validity.entity_conflict
  simp only [entity_iri_spec, Rowl.Typing.entity_kind_total_correct, builtin_conflict_spec, bind_ok,
    later_conflict_spec]
  cases builtin : builtinConflict (entityIri entity) (Rowl.Typing.kindOf entity) with
  | some r =>
    obtain ⟨role, forbidden⟩ := builtin_conflict_some _ _ _ builtin
    refine ⟨some r, rfl, fun h => by simp at h, fun k same => ?_⟩
    cases Option.some.inj same
    exact ⟨forbidden, .inl role⟩
  | none =>
    refine ⟨_, rfl, fun none k conflict => ?_, fun k found => ?_⟩
    · obtain ⟨forbidden, source⟩ := conflict
      rcases source with role | ⟨d, member, kind, same⟩
      · exact builtin_conflict_none _ _ builtin k role forbidden
      · subst kind
        exact first_clash_none _ _ _ none d member ⟨same, forbidden⟩
    · obtain ⟨d, member, ⟨same, forbidden⟩, kind⟩ := first_clash_some _ _ _ k found
      subst kind
      exact ⟨forbidden, .inr ⟨d, member, rfl, same⟩⟩

private theorem item_conflicts_correct (axioms : alloc.vec.Vec AnnotatedAxiom) (item : AnnotatedAxiom)
    (index : Usize) :
    ∃ r, dl_validity.item_conflicts axioms item index = .ok r ∧
      ((r = .Valid ∧ ∀ row ∈ Rowl.Collection.declarationUses item, ∀ k,
          ¬ ConflictWith ((axioms.val.drop index.val).flatMap Rowl.Collection.declarationUses) row k) ∨
        ∃ iri kind other, r = .ConflictingDeclarations iri kind other ∧
          Rowl.Collection.declarationUses item = [(iri, kind)] ∧
          ConflictWith ((axioms.val.drop index.val).flatMap Rowl.Collection.declarationUses) (iri, kind) other) := by
  unfold dl_validity.item_conflicts
  cases h : item.axiom
  case Declaration entity =>
    obtain ⟨r, run, none, some⟩ := entity_conflict_correct axioms entity index
    have uses : Rowl.Collection.declarationUses item = [(entityIri entity, Rowl.Typing.kindOf entity)] := by
      simp [Rowl.Collection.declarationUses, h, entity_uses_eq]
    cases r with
    | none =>
      refine ⟨.Valid, by simp [run], .inl ⟨rfl, ?_⟩⟩
      rw [uses]
      intro row member k
      rw [List.mem_singleton] at member
      subst member
      exact none rfl k
    | some other =>
      refine ⟨.ConflictingDeclarations (entityIri entity) (Rowl.Typing.kindOf entity) other,
        by simp [run, entity_iri_spec, Rowl.Typing.entity_kind_total_correct], .inr ⟨_, _, other, rfl, uses, some other rfl⟩⟩
  all_goals exact ⟨.Valid, by simp, .inl ⟨rfl, by simp [Rowl.Collection.declarationUses, h]⟩⟩

private def ConflictsCorrect (rows : List Row) : TypingCheck → Prop
  | .Valid => ConflictFree rows
  | .ConflictingDeclarations iri kind other => FirstConflict rows iri kind other
  | .MissingDeclaration _ _ => False

private theorem declaration_uses_shape (item : AnnotatedAxiom) :
    Rowl.Collection.declarationUses item = [] ∨ ∃ row, Rowl.Collection.declarationUses item = [row] := by
  unfold Rowl.Collection.declarationUses
  cases h : item.axiom
  case Declaration entity => exact .inr ⟨_, entity_uses_eq entity⟩
  all_goals exact .inl rfl

private theorem conflict_from_correct (axioms : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    ∃ r, dl_validity.conflict_from axioms index = .ok r ∧
      ConflictsCorrect ((axioms.val.drop index.val).flatMap Rowl.Collection.declarationUses) r := by
  rw [dl_validity.conflict_from]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have size := axioms.property
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextval : next.val = index.val + 1 := by simpa using hv
    have rows := drop_rows axioms index.val inside Rowl.Collection.declarationUses
    rw [rows]
    rw [← nextval] at rows ⊢
    obtain ⟨r, run, verdict⟩ := item_conflicts_correct axioms axioms.val[index.val] next
    rcases verdict with ⟨valid, unconflicted⟩ | ⟨iri, kind, other, conflict, uses, conflictWith⟩
    · subst valid
      obtain ⟨rest, restRun, restCorrect⟩ := conflict_from_correct axioms next
      refine ⟨rest, by simp [inside, alloc.vec.Vec.index_slice_index, lookup, hn, run, restRun], ?_⟩
      rcases declaration_uses_shape axioms.val[index.val] with empty | ⟨row, single⟩
      · rw [empty]
        simpa using restCorrect
      · rw [single]
        have free : ∀ k, ¬ ConflictWith ((axioms.val.drop next.val).flatMap Rowl.Collection.declarationUses) row k :=
          unconflicted row (by rw [single]; exact List.mem_singleton_self row)
        cases rest with
        | Valid => exact ⟨free, restCorrect⟩
        | ConflictingDeclarations iri kind other => exact .later free restCorrect
        | MissingDeclaration _ _ => exact False.elim restCorrect
    · subst conflict
      refine ⟨.ConflictingDeclarations iri kind other,
        by simp [inside, alloc.vec.Vec.index_slice_index, lookup, hn, run], ?_⟩
      rw [uses]
      exact .here conflictWith
  · have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    exact ⟨.Valid, by simp [inside], by simp [empty, ConflictsCorrect, ConflictFree]⟩
termination_by axioms.val.length - index.val
decreasing_by omega

private theorem exempt_spec (kind : EntityKind) (strict : Bool) :
    dl_validity.exempt kind strict = .ok (decide (strict = false ∧ kind = .NamedIndividual)) := by
  unfold dl_validity.exempt
  cases strict <;> cases kind <;> simp

private theorem use_declared_spec (axioms : alloc.vec.Vec AnnotatedAxiom) (iri : Iri) (kind : EntityKind)
    (strict : Bool) :
    dl_validity.use_declared axioms iri kind strict =
      .ok (decide (Declared strict (axioms.val.flatMap Rowl.Collection.declarationUses) (iri, kind))) := by
  unfold dl_validity.use_declared
  have zero : (0#usize).val = 0 := by simp
  have whole := declared_from_spec axioms iri kind 0#usize
  simp only [zero, List.drop_zero] at whole
  by_cases exempt : strict = false ∧ kind = .NamedIndividual
  · simp [exempt_spec, exempt, Declared]
  · by_cases builtin : Rowl.Builtins.role iri.spelling.val = some kind
    · simp [exempt_spec, exempt, builtin_role_spec, builtin, Declared]
    · simp only [exempt_spec, exempt, builtin_role_spec, builtin, whole, decide_false, bind_ok,
        Bool.false_eq_true, ↓reduceIte]
      simp [Declared, exempt, builtin, DeclaresAs]

private def UndeclaredCorrect (strict : Bool) (declarations rows : List Row) :
    Option (Iri × EntityKind) → Prop
  | none => ∀ row ∈ rows, Declared strict declarations row
  | some (iri, kind) => FirstUndeclared strict declarations rows iri kind

private theorem undeclared_from_correct (axioms : alloc.vec.Vec AnnotatedAxiom) (uses : EntityUses)
    (strict : Bool) :
    ∃ r, dl_validity.undeclared_from axioms uses strict = .ok r ∧
      UndeclaredCorrect strict (axioms.val.flatMap Rowl.Collection.declarationUses) (Rowl.Collection.rows uses) r := by
  induction uses with
  | Empty =>
    exact ⟨none, by simp [dl_validity.undeclared_from], by simp [UndeclaredCorrect, Rowl.Collection.rows]⟩
  | Entry iri kind next ih =>
    obtain ⟨r, run, correct⟩ := ih
    rw [dl_validity.undeclared_from]
    by_cases declared : Declared strict (axioms.val.flatMap Rowl.Collection.declarationUses) (iri, kind)
    · refine ⟨r, by simp [use_declared_spec, declared, run], ?_⟩
      cases r with
      | none =>
        intro row member
        rcases List.mem_cons.mp member with same | member
        · subst same
          exact declared
        · exact correct row member
      | some found =>
        obtain ⟨missingIri, missingKind⟩ := found
        exact .later declared correct
    · exact ⟨some (iri, kind), by simp [use_declared_spec, declared], .here declared⟩

private theorem declarations_rows (o : RawOntology) :
    o.axioms.val.flatMap Rowl.Collection.declarationUses = Rowl.Indexing.ontologyDeclarations o := rfl

/-- The typing check terminates and decides `Rowl.Indexing.RawWellTyped`, the
    independent §5.8.1 predicate on original IRI spellings with the built-in
    declarations of Table 5. A conflict is the first conflicting declaration; a
    missing declaration is the first undeclared use after conflict freedom. -/
theorem check_typing_total_correct (o : RawOntology) :
    ∃ r, dl_validity.check_typing o = .ok r ∧ TypingCorrect o r := by
  obtain ⟨conflicts, run, conflictsCorrect⟩ := conflict_from_correct o.axioms 0#usize
  have zero : (0#usize).val = 0 := by simp
  simp only [zero, List.drop_zero, declarations_rows] at conflictsCorrect
  cases conflicts with
  | ConflictingDeclarations iri kind other =>
    refine ⟨.ConflictingDeclarations iri kind other, by simp [dl_validity.check_typing, run],
      conflictsCorrect, ?_⟩
    rw [raw_well_typed_iff]
    exact fun ⟨free, _⟩ => first_conflict_not_free conflictsCorrect free
  | MissingDeclaration _ _ => exact False.elim conflictsCorrect
  | Valid =>
    obtain ⟨collected, collectedRun, collectedCorrect⟩ := Rowl.Collection.axiom_closure_entities_total_correct o
    obtain ⟨missing, missingRun, missingCorrect⟩ := undeclared_from_correct o.axioms collected.uses false
    have usesRows : Rowl.Collection.rows collected.uses = Rowl.Indexing.ontologyUses o := collectedCorrect.2
    rw [usesRows, declarations_rows] at missingCorrect
    cases missing with
    | none =>
      refine ⟨.Valid, by simp [dl_validity.check_typing, run, collectedRun, missingRun], ?_⟩
      exact (raw_well_typed_iff o).mpr ⟨conflictsCorrect, missingCorrect⟩
    | some found =>
      obtain ⟨iri, kind⟩ := found
      refine ⟨.MissingDeclaration iri kind, by simp [dl_validity.check_typing, run, collectedRun, missingRun],
        conflictsCorrect, missingCorrect, ?_⟩
      rw [raw_well_typed_iff]
      exact fun ⟨_, all⟩ => first_undeclared_not_all missingCorrect all

/-- No false acceptance or rejection of the typing constraints of §5.8.1. -/
theorem check_typing_valid_iff (o : RawOntology) :
    dl_validity.check_typing o = .ok .Valid ↔ Rowl.Indexing.RawWellTyped o := by
  obtain ⟨r, run, correct⟩ := check_typing_total_correct o
  rw [run]
  cases r with
  | Valid => simpa [TypingCorrect] using correct
  | ConflictingDeclarations iri kind other => simp [TypingCorrect] at correct; simp [correct.2]
  | MissingDeclaration iri kind => simp [TypingCorrect] at correct; simp [correct.2.2]

/-- Whenever the symbol-indexed `check_ontology_typing` completes, its verdict is
    the verdict of the capacity-free `check_typing`. -/
theorem check_typing_agrees (o : RawOntology) (limit : U32) (table : RowlRust.symbols.SymbolTable)
    (declarations uses : Occurrences) (result : TypingResult)
    (executed : RowlRust.indexing.check_ontology_typing o limit =
      .ok (.Checked table declarations uses result)) :
    result = .Valid ↔ dl_validity.check_typing o = .ok .Valid :=
  (Rowl.Indexing.check_ontology_typing_valid_iff_raw o limit table declarations uses result executed).trans
    (check_typing_valid_iff o).symm

/-- Declaration consistency (§5.8.2) is decided exactly, with the first
    undeclared use as evidence. -/
theorem check_declarations_total_correct (o : RawOntology) :
    ∃ r, dl_validity.check_declarations o = .ok r ∧ DeclarationsCorrect o r := by
  obtain ⟨collected, collectedRun, collectedCorrect⟩ := Rowl.Collection.axiom_closure_entities_total_correct o
  obtain ⟨missing, missingRun, missingCorrect⟩ := undeclared_from_correct o.axioms collected.uses true
  have usesRows : Rowl.Collection.rows collected.uses = Rowl.Indexing.ontologyUses o := collectedCorrect.2
  rw [usesRows, declarations_rows] at missingCorrect
  cases missing with
  | none =>
    exact ⟨.Consistent, by simp [dl_validity.check_declarations, collectedRun, missingRun],
      (consistent_iff o).mpr missingCorrect⟩
  | some found =>
    obtain ⟨iri, kind⟩ := found
    refine ⟨.Undeclared iri kind, by simp [dl_validity.check_declarations, collectedRun, missingRun],
      missingCorrect, ?_⟩
    rw [consistent_iff]
    exact first_undeclared_not_all missingCorrect

theorem check_declarations_valid_iff (o : RawOntology) :
    dl_validity.check_declarations o = .ok .Consistent ↔ ConsistentDeclarations o := by
  obtain ⟨r, run, correct⟩ := check_declarations_total_correct o
  rw [run]
  cases r with
  | Consistent => simpa [DeclarationsCorrect] using correct
  | Undeclared iri kind => simp [DeclarationsCorrect] at correct; simp [correct.2]

/-! ## Property chains and the restriction on the property hierarchy -/

private theorem is_chain_spec (item : AnnotatedAxiom) :
    dl_validity.is_chain item = .ok (decide (Rowl.Roles.AxiomChains item.axiom ≠ [])) := by
  unfold dl_validity.is_chain
  rcases item with ⟨annotations, body⟩
  cases body
  case SubObjectPropertyOf sub sup => cases sub <;> simp [Rowl.Roles.AxiomChains]
  all_goals simp only [Rowl.Roles.AxiomChains, ne_eq, not_true_eq_false, decide_false]

private theorem chain_from_spec (axioms : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    dl_validity.chain_from axioms index =
      .ok (decide (∃ item ∈ axioms.val.drop index.val, Rowl.Roles.AxiomChains item.axiom ≠ [])) := by
  rw [dl_validity.chain_from]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have cond : index < alloc.vec.Vec.len axioms := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    have size := axioms.property
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextval : next.val = index.val + 1 := by simpa using hv
    have ih := chain_from_spec axioms next
    have drop : axioms.val.drop index.val = axioms.val[index.val] :: axioms.val.drop next.val := by
      rw [nextval]; exact List.drop_eq_getElem_cons inside
    simp only [cond, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup, bind_ok, is_chain_spec]
    split
    · rename_i decided
      have here := of_decide_eq_true decided
      have found : ∃ item ∈ axioms.val.drop index.val, Rowl.Roles.AxiomChains item.axiom ≠ [] :=
        ⟨axioms.val[index.val], by rw [drop]; exact List.mem_cons_self, here⟩
      simp only [found, decide_true]
    · rename_i decided
      have here := of_decide_eq_false (Bool.of_not_eq_true decided)
      have same : (∃ item ∈ axioms.val.drop next.val, Rowl.Roles.AxiomChains item.axiom ≠ []) ↔
          ∃ item ∈ axioms.val.drop index.val, Rowl.Roles.AxiomChains item.axiom ≠ [] := by
        rw [drop]
        constructor
        · rintro ⟨item, member, chained⟩
          exact ⟨item, List.mem_cons_of_mem _ member, chained⟩
        · rintro ⟨item, member, chained⟩
          rcases List.mem_cons.mp member with same | member
          · subst same; exact False.elim (here chained)
          · exact ⟨item, member, chained⟩
      simp only [hn, bind_ok, ih]
      congr 1
      exact decide_eq_decide.mpr same
  · have cond : ¬ index < alloc.vec.Vec.len axioms := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp only [cond, ↓reduceIte, empty, List.not_mem_nil, false_and, exists_false, decide_false]
termination_by axioms.val.length - index.val
decreasing_by omega

/-- Whether the closure has a SubObjectPropertyOf axiom with a property chain. -/
theorem has_chain_spec (axioms : alloc.vec.Vec AnnotatedAxiom) :
    dl_validity.has_chain axioms =
      .ok (decide (∃ item ∈ axioms.val, Rowl.Roles.AxiomChains item.axiom ≠ [])) := by
  simpa [dl_validity.has_chain] using chain_from_spec axioms 0#usize

/-- Without property chains the empty order satisfies the restriction on the
    property hierarchy (§11.2), so the regularity search can be skipped. -/
theorem no_chain_regular (items : List AnnotatedAxiom)
    (none : ∀ item ∈ items, Rowl.Roles.AxiomChains item.axiom = []) : Rowl.Roles.Regular items := by
  refine ⟨fun _ _ => False, fun _ _ h => h.elim, fun _ h => h, fun _ _ _ h _ => h,
    fun _ _ _ _ => Iff.rfl, fun _ _ h => h.elim, ?_⟩
  intro chain member
  simp only [List.mem_flatMap] at member
  obtain ⟨item, inside, found⟩ := member
  rw [none item inside] at found
  simp at found

/-! ## OWL 2 DL validity -/

/-- The OWL 2 DL conditions of the 2012 Structural Specification, Section 3, on
    an ontology whose axioms are the complete axiom closure: nonempty keys
    (§9.5); at least two distinct members where the structure requires them and
    pairwise distinct members of disjointness and difference axioms (the
    documented duplicate-disjointness decision of architecture.md); reserved
    IRIs only in their built-in roles, and neither as ontology nor as version IRI
    (§3.1, §5.1–5.6); the typing constraints with the built-in declarations
    (§5.8.1); and the global restrictions of §11.2 on `owl:topDataProperty`,
    datatypes (with the positions of defined datatypes, §9.4), simple roles, the
    property hierarchy and anonymous individuals. The lexical forms of literals
    (§5.7) and facet values (§7.5) need the normative datatype map and are not
    included; imports are not resolved. -/
def OwlDlValid (o : RawOntology) : Prop :=
  Rowl.Keys.ClosureOK o.axioms.val ∧
  Rowl.Arity.ClosureOK o.axioms.val ∧
  Rowl.Vocabulary.VocabularyOK o ∧
  Rowl.Indexing.RawWellTyped o ∧
  Rowl.TopData.ClosureOK o.axioms.val ∧
  Rowl.DatatypeRestrictions.StructuralRestriction o ∧
  Rowl.Roles.SimpleRestriction o.axioms.val ∧
  Rowl.Roles.Regular o.axioms.val ∧
  Rowl.AnonymousRestrictions.Restriction o.axioms.val

/-- The structural conditions on an OWL 2 ontology: keys and arities. -/
def StructureOK (o : RawOntology) : Prop :=
  Rowl.Keys.ClosureOK o.axioms.val ∧ Rowl.Arity.ClosureOK o.axioms.val

/-- The structural conditions, the reserved vocabulary and the typing constraints. -/
def NamesOK (o : RawOntology) : Prop :=
  StructureOK o ∧ Rowl.Vocabulary.VocabularyOK o ∧ Rowl.Indexing.RawWellTyped o

/-- Additionally the restrictions on `owl:topDataProperty` and on datatypes. -/
def DataOK (o : RawOntology) : Prop :=
  NamesOK o ∧ Rowl.TopData.ClosureOK o.axioms.val ∧ Rowl.DatatypeRestrictions.StructuralRestriction o

/-- Additionally the restrictions on simple roles and on the property hierarchy. -/
def RolesOK (o : RawOntology) : Prop :=
  DataOK o ∧ Rowl.Roles.SimpleRestriction o.axioms.val ∧ Rowl.Roles.Regular o.axioms.val

private theorem valid_parts (o : RawOntology) :
    OwlDlValid o ↔ RolesOK o ∧ Rowl.AnonymousRestrictions.Restriction o.axioms.val := by
  simp only [OwlDlValid, RolesOK, DataOK, NamesOK, StructureOK, and_assoc]

/-- `Valid` is exact. Each violation carries the evidence of its component
    checker, the proof that every earlier restriction of the documented order
    holds, and the rejection of `OwlDlValid`. -/
def Correct (o : RawOntology) : DlCheck → Prop
  | .Valid => OwlDlValid o
  | .EmptyKey item => Rowl.Keys.FirstForbidden o.axioms.val item ∧ ¬ OwlDlValid o
  | .Arity item => Rowl.Keys.ClosureOK o.axioms.val ∧ Rowl.Arity.FirstForbidden o.axioms.val item ∧
      ¬ OwlDlValid o
  | .ReservedOntologyIri iri => StructureOK o ∧ Rowl.Vocabulary.Correct o (.ReservedOntologyIri iri) ∧
      ¬ OwlDlValid o
  | .ReservedVersionIri iri => StructureOK o ∧ Rowl.Vocabulary.Correct o (.ReservedVersionIri iri) ∧
      ¬ OwlDlValid o
  | .ReservedEntity iri kind => StructureOK o ∧ Rowl.Vocabulary.Correct o (.ForbiddenEntity iri kind) ∧
      ¬ OwlDlValid o
  | .ConflictingDeclarations iri kind other => StructureOK o ∧ Rowl.Vocabulary.VocabularyOK o ∧
      TypingCorrect o (.ConflictingDeclarations iri kind other) ∧ ¬ OwlDlValid o
  | .MissingDeclaration iri kind => StructureOK o ∧ Rowl.Vocabulary.VocabularyOK o ∧
      TypingCorrect o (.MissingDeclaration iri kind) ∧ ¬ OwlDlValid o
  | .TopDataProperty item => NamesOK o ∧ Rowl.TopData.FirstForbidden o.axioms.val item ∧ ¬ OwlDlValid o
  | .MissingDatatypeDefinition iri => NamesOK o ∧ Rowl.TopData.ClosureOK o.axioms.val ∧
      Rowl.DatatypeRestrictions.StructuralCorrect o (.MissingDefinition iri) ∧ ¬ OwlDlValid o
  | .PredefinedDatatypeRedefined item => NamesOK o ∧ Rowl.TopData.ClosureOK o.axioms.val ∧
      Rowl.DatatypeRestrictions.StructuralCorrect o (.PredefinedRedefined item) ∧ ¬ OwlDlValid o
  | .MultipleDatatypeDefinitions first second => NamesOK o ∧ Rowl.TopData.ClosureOK o.axioms.val ∧
      Rowl.DatatypeRestrictions.StructuralCorrect o (.MultipleDefinitions first second) ∧ ¬ OwlDlValid o
  | .DatatypeCycle smaller larger => NamesOK o ∧ Rowl.TopData.ClosureOK o.axioms.val ∧
      Rowl.DatatypeRestrictions.StructuralCorrect o (.Cycle smaller larger) ∧ ¬ OwlDlValid o
  | .DefinedDatatypeInOntologyAnnotation item => NamesOK o ∧ Rowl.TopData.ClosureOK o.axioms.val ∧
      Rowl.DatatypeRestrictions.StructuralCorrect o (.ForbiddenOntologyAnnotation item) ∧ ¬ OwlDlValid o
  | .DefinedDatatypePosition item => NamesOK o ∧ Rowl.TopData.ClosureOK o.axioms.val ∧
      Rowl.DatatypeRestrictions.StructuralCorrect o (.ForbiddenAxiomPosition item) ∧ ¬ OwlDlValid o
  | .NonSimpleRole role => DataOK o ∧
      Rowl.RoleClosure.SimplicityCorrect o.axioms.val (.ForbiddenRole role) ∧ ¬ OwlDlValid o
  | .IrregularHierarchy sub sup => DataOK o ∧ Rowl.Roles.SimpleRestriction o.axioms.val ∧
      Rowl.RoleOrder.RegularityCorrect o.axioms.val (.HierarchyConflict sub sup) ∧ ¬ OwlDlValid o
  | .AnonymousPosition item => RolesOK o ∧
      Rowl.AnonymousRestrictions.Correct o.axioms.val (.ForbiddenPosition item) ∧ ¬ OwlDlValid o
  | .AnonymousSelfLoop value => RolesOK o ∧
      Rowl.AnonymousRestrictions.Correct o.axioms.val (.SelfLoop value) ∧ ¬ OwlDlValid o
  | .AnonymousCycle left right => RolesOK o ∧
      Rowl.AnonymousRestrictions.Correct o.axioms.val (.Cycle left right) ∧ ¬ OwlDlValid o
  | .AnonymousMultipleAssertions first second => RolesOK o ∧
      Rowl.AnonymousRestrictions.Correct o.axioms.val (.MultipleAssertions first second) ∧ ¬ OwlDlValid o
  | .AnonymousNoBoundaryRoot value => RolesOK o ∧
      Rowl.AnonymousRestrictions.Correct o.axioms.val (.NoBoundaryRoot value) ∧ ¬ OwlDlValid o

private theorem member_of_split {item : AnnotatedAxiom} {axioms : List AnnotatedAxiom}
    {rest : List AnnotatedAxiom → Prop}
    (split : ∃ before after, axioms = before ++ item :: after ∧ rest before) : item ∈ axioms := by
  obtain ⟨before, after, same, _⟩ := split
  simp [same]

private theorem anonymous_graph_stage_correct (o : RawOntology) (prior : RolesOK o) :
    ∃ r, dl_validity.anonymous_graph_stage o = .ok r ∧ Correct o r := by
  obtain ⟨check, run, correct⟩ := Rowl.AnonymousRestrictions.check_anonymous_total_correct o.axioms
  have reject : ¬ Rowl.AnonymousRestrictions.Restriction o.axioms.val → ¬ OwlDlValid o :=
    fun bad valid => bad ((valid_parts o).mp valid).2
  cases check with
  | Allowed =>
    exact ⟨.Valid, by simp [dl_validity.anonymous_graph_stage, run], (valid_parts o).mpr ⟨prior, correct⟩⟩
  | ForbiddenPosition item =>
    exact ⟨.AnonymousPosition item, by simp [dl_validity.anonymous_graph_stage, run], prior, correct,
      reject correct.2⟩
  | SelfLoop value =>
    exact ⟨.AnonymousSelfLoop value, by simp [dl_validity.anonymous_graph_stage, run], prior, correct,
      reject correct.2.2⟩
  | Cycle left right =>
    exact ⟨.AnonymousCycle left right, by simp [dl_validity.anonymous_graph_stage, run], prior, correct,
      reject correct.2.2⟩
  | MultipleAssertions first second =>
    exact ⟨.AnonymousMultipleAssertions first second, by simp [dl_validity.anonymous_graph_stage, run], prior,
      correct, reject correct.2.2.2⟩
  | NoBoundaryRoot value =>
    exact ⟨.AnonymousNoBoundaryRoot value, by simp [dl_validity.anonymous_graph_stage, run], prior, correct,
      reject correct.2.2.2.2⟩

private theorem anonymous_assertion_spec (item : AnnotatedAxiom) :
    dl_validity.anonymous_assertion item = .ok (decide (Rowl.AnonymousBoundary.First item ≠ none)) := by
  unfold dl_validity.anonymous_assertion
  rcases item with ⟨annotations, body⟩
  cases body
  case ObjectPropertyAssertion p a b =>
    cases a <;> cases b <;> simp [Rowl.AnonymousBoundary.First]
  all_goals simp [Rowl.AnonymousBoundary.First]

private theorem anonymous_from_spec (axioms : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    dl_validity.anonymous_from axioms index =
      .ok (decide (∃ item ∈ axioms.val.drop index.val, Rowl.AnonymousBoundary.First item ≠ none)) := by
  rw [dl_validity.anonymous_from]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have cond : index < alloc.vec.Vec.len axioms := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    have size := axioms.property
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextval : next.val = index.val + 1 := by simpa using hv
    have ih := anonymous_from_spec axioms next
    have drop : axioms.val.drop index.val = axioms.val[index.val] :: axioms.val.drop next.val := by
      rw [nextval]; exact List.drop_eq_getElem_cons inside
    simp only [cond, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup, bind_ok, anonymous_assertion_spec]
    split
    · rename_i decided
      have here := of_decide_eq_true decided
      have found : ∃ item ∈ axioms.val.drop index.val, Rowl.AnonymousBoundary.First item ≠ none :=
        ⟨axioms.val[index.val], by rw [drop]; exact List.mem_cons_self, here⟩
      simp only [found, decide_true]
    · rename_i decided
      have here := of_decide_eq_false (Bool.of_not_eq_true decided)
      have same : (∃ item ∈ axioms.val.drop next.val, Rowl.AnonymousBoundary.First item ≠ none) ↔
          ∃ item ∈ axioms.val.drop index.val, Rowl.AnonymousBoundary.First item ≠ none := by
        rw [drop]
        constructor
        · rintro ⟨item, member, endpoint⟩
          exact ⟨item, List.mem_cons_of_mem _ member, endpoint⟩
        · rintro ⟨item, member, endpoint⟩
          rcases List.mem_cons.mp member with same | member
          · subst same; exact False.elim (here endpoint)
          · exact ⟨item, member, endpoint⟩
      simp only [hn, bind_ok, ih]
      congr 1
      exact decide_eq_decide.mpr same
  · have cond : ¬ index < alloc.vec.Vec.len axioms := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp only [cond, ↓reduceIte, empty, List.not_mem_nil, false_and, exists_false, decide_false]
termination_by axioms.val.length - index.val
decreasing_by omega

/-- Whether some object property assertion of the closure has an anonymous endpoint. -/
theorem has_anonymous_assertion_spec (axioms : alloc.vec.Vec AnnotatedAxiom) :
    dl_validity.has_anonymous_assertion axioms =
      .ok (decide (∃ item ∈ axioms.val, Rowl.AnonymousBoundary.First item ≠ none)) := by
  simpa [dl_validity.has_anonymous_assertion] using anonymous_from_spec axioms 0#usize

/-- Without an object property assertion with an anonymous endpoint, the
    anonymous individual graph has no edge and no anonymous individual has an
    assertion with a named one, so the restrictions on anonymous individuals
    (§11.2) reduce to the positional one. -/
theorem no_anonymous_assertion_restriction (items : List AnnotatedAxiom)
    (none : ∀ item ∈ items, Rowl.AnonymousBoundary.First item = none) :
    Rowl.AnonymousRestrictions.Restriction items ↔ Rowl.Anonymous.PositionsOK items := by
  have edges : Rowl.AnonymousGraph.closureEdges items = [] := by
    unfold Rowl.AnonymousGraph.closureEdges
    rw [List.flatMap_eq_nil_iff]
    intro item member
    have first := none item member
    unfold Rowl.AnonymousGraph.axiomEdges
    split
    · rename_i p a b shape
      simp [Rowl.AnonymousBoundary.First, shape] at first
    · rfl
  constructor
  · exact fun restriction => restriction.1
  · intro positions
    refine ⟨positions, ?_, ?_, ?_⟩
    · rw [edges]
      exact ⟨by simp, by simp [Rowl.AnonymousGraph.graph]⟩
    · intro first member second _ same
      have endpoint := none first member
      unfold Rowl.AnonymousMultiplicity.SamePair at same
      split at same
      · rename_i p a b q c d shape _
        simp [Rowl.AnonymousBoundary.First, shape] at endpoint
      · exact False.elim same
    · intro root
      refine ⟨root, SimpleGraph.Reachable.refl _, ?_⟩
      intro first member touches
      have endpoint := none first member
      unfold Rowl.AnonymousBoundary.TouchesNamed at touches
      split at touches
      · rename_i p a n shape
        simp [Rowl.AnonymousBoundary.First, shape] at endpoint
      · rename_i p n a shape
        simp [Rowl.AnonymousBoundary.First, shape] at endpoint
      · exact False.elim touches

private theorem anonymous_stage_correct (o : RawOntology) (prior : RolesOK o) :
    ∃ r, dl_validity.anonymous_stage o = .ok r ∧ Correct o r := by
  unfold dl_validity.anonymous_stage
  rw [has_anonymous_assertion_spec]
  by_cases endpoint : ∃ item ∈ o.axioms.val, Rowl.AnonymousBoundary.First item ≠ none
  · obtain ⟨r, stage, staged⟩ := anonymous_graph_stage_correct o prior
    exact ⟨r, by simp [endpoint, stage], staged⟩
  · have none : ∀ item ∈ o.axioms.val, Rowl.AnonymousBoundary.First item = none := fun item member => by
      by_contra found
      exact endpoint ⟨item, member, found⟩
    have reduce := no_anonymous_assertion_restriction o.axioms.val none
    obtain ⟨positions, run, correct⟩ := Rowl.Anonymous.check_positions_total_correct o.axioms
    cases positions with
    | none =>
      exact ⟨.Valid, by simp [endpoint, run], (valid_parts o).mpr ⟨prior, reduce.mpr correct⟩⟩
    | some item =>
      have rejected : ¬ Rowl.AnonymousRestrictions.Restriction o.axioms.val := fun restriction =>
        correct.1 (restriction.1 item (member_of_split correct.2))
      exact ⟨.AnonymousPosition item, by simp [endpoint, run], prior, ⟨correct, rejected⟩,
        fun valid => rejected ((valid_parts o).mp valid).2⟩

private theorem hierarchy_stage_correct (o : RawOntology) (prior : DataOK o)
    (simple : Rowl.Roles.SimpleRestriction o.axioms.val) :
    ∃ r, dl_validity.hierarchy_stage o = .ok r ∧ Correct o r := by
  unfold dl_validity.hierarchy_stage
  rw [has_chain_spec]
  by_cases chained : ∃ item ∈ o.axioms.val, Rowl.Roles.AxiomChains item.axiom ≠ []
  · obtain ⟨check, run, correct⟩ := Rowl.RoleOrder.check_regularity_total_correct o.axioms
    cases check with
    | Regular order =>
      have regular : Rowl.Roles.Regular o.axioms.val :=
        (Rowl.RoleOrder.check_regularity_accepted_iff o.axioms).mp ⟨order, run⟩
      obtain ⟨r, stage, staged⟩ := anonymous_stage_correct o ⟨prior, simple, regular⟩
      exact ⟨r, by simp [chained, run, stage], staged⟩
    | HierarchyConflict sub sup =>
      exact ⟨.IrregularHierarchy sub sup, by simp [chained, run], prior, simple, correct,
        fun valid => correct.2.2 valid.2.2.2.2.2.2.2.1⟩
    | MissingPair _ _ => exact False.elim correct
    | MissingHierarchyNode _ => exact False.elim correct
  · have regular := no_chain_regular o.axioms.val (fun item member => by
      by_contra found
      exact chained ⟨item, member, found⟩)
    obtain ⟨r, stage, staged⟩ := anonymous_stage_correct o ⟨prior, simple, regular⟩
    exact ⟨r, by simp [chained, stage], staged⟩

private theorem role_stage_correct (o : RawOntology) (prior : DataOK o) :
    ∃ r, dl_validity.role_stage o = .ok r ∧ Correct o r := by
  obtain ⟨check, run, correct⟩ := Rowl.RoleClosure.check_simplicity_total_correct o.axioms
  cases check with
  | Allowed =>
    obtain ⟨r, stage, staged⟩ := hierarchy_stage_correct o prior correct
    exact ⟨r, by simp [dl_validity.role_stage, run, stage], staged⟩
  | ForbiddenRole role =>
    refine ⟨.NonSimpleRole role, by simp [dl_validity.role_stage, run], prior, correct, fun valid => ?_⟩
    have allowed := (Rowl.RoleClosure.check_simplicity_allowed_iff o.axioms).mpr valid.2.2.2.2.2.2.1
    rw [run] at allowed
    simp at allowed
  | MissingNode _ => exact False.elim correct

private theorem datatype_stage_correct (o : RawOntology) (prior : NamesOK o)
    (top : Rowl.TopData.ClosureOK o.axioms.val) :
    ∃ r, dl_validity.datatype_stage o = .ok r ∧ Correct o r := by
  obtain ⟨check, run, correct⟩ := Rowl.DatatypeRestrictions.check_structural_datatypes_total_correct o
  have reject : ¬ Rowl.DatatypeRestrictions.StructuralRestriction o → ¬ OwlDlValid o :=
    fun bad valid => bad valid.2.2.2.2.2.1
  cases check with
  | Allowed =>
    obtain ⟨r, stage, staged⟩ := role_stage_correct o ⟨prior, top, correct⟩
    exact ⟨r, by simp [dl_validity.datatype_stage, run, stage], staged⟩
  | MissingDefinition iri =>
    exact ⟨.MissingDatatypeDefinition iri, by simp [dl_validity.datatype_stage, run], prior, top, correct,
      reject correct.2⟩
  | PredefinedRedefined item =>
    exact ⟨.PredefinedDatatypeRedefined item, by simp [dl_validity.datatype_stage, run], prior, top, correct,
      reject correct.2⟩
  | MultipleDefinitions first second =>
    exact ⟨.MultipleDatatypeDefinitions first second, by simp [dl_validity.datatype_stage, run], prior, top,
      correct, reject correct.2⟩
  | Cycle smaller larger =>
    exact ⟨.DatatypeCycle smaller larger, by simp [dl_validity.datatype_stage, run], prior, top, correct,
      reject correct.2⟩
  | ForbiddenOntologyAnnotation item =>
    exact ⟨.DefinedDatatypeInOntologyAnnotation item, by simp [dl_validity.datatype_stage, run], prior, top,
      correct, reject correct.2.2⟩
  | ForbiddenAxiomPosition item =>
    exact ⟨.DefinedDatatypePosition item, by simp [dl_validity.datatype_stage, run], prior, top, correct,
      reject correct.2.2⟩

private theorem global_stage_correct (o : RawOntology) (prior : NamesOK o) :
    ∃ r, dl_validity.global_stage o = .ok r ∧ Correct o r := by
  obtain ⟨check, run, correct⟩ := Rowl.TopData.check_axioms_total_correct o.axioms
  cases check with
  | none =>
    obtain ⟨r, stage, staged⟩ := datatype_stage_correct o prior correct
    exact ⟨r, by simp [dl_validity.global_stage, run, stage], staged⟩
  | some item =>
    exact ⟨.TopDataProperty item, by simp [dl_validity.global_stage, run], prior, correct,
      fun valid => correct.1 (valid.2.2.2.2.1 item (member_of_split correct.2))⟩

private theorem typing_stage_correct (o : RawOntology) (shape : StructureOK o)
    (vocabulary : Rowl.Vocabulary.VocabularyOK o) :
    ∃ r, dl_validity.typing_stage o = .ok r ∧ Correct o r := by
  obtain ⟨check, run, correct⟩ := check_typing_total_correct o
  cases check with
  | Valid =>
    obtain ⟨r, stage, staged⟩ := global_stage_correct o ⟨shape, vocabulary, correct⟩
    exact ⟨r, by simp [dl_validity.typing_stage, run, stage], staged⟩
  | ConflictingDeclarations iri kind other =>
    exact ⟨.ConflictingDeclarations iri kind other, by simp [dl_validity.typing_stage, run], shape,
      vocabulary, correct, fun valid => correct.2 valid.2.2.2.1⟩
  | MissingDeclaration iri kind =>
    exact ⟨.MissingDeclaration iri kind, by simp [dl_validity.typing_stage, run], shape, vocabulary,
      correct, fun valid => correct.2.2 valid.2.2.2.1⟩

private theorem vocabulary_stage_correct (o : RawOntology) (shape : StructureOK o) :
    ∃ r, dl_validity.vocabulary_stage o = .ok r ∧ Correct o r := by
  obtain ⟨check, run, correct⟩ := Rowl.Vocabulary.check_reserved_vocabulary_total_correct o
  have reject : check ≠ .Valid → ¬ OwlDlValid o := fun failed valid => failed
    (Result.ok_injective (run.symm.trans ((Rowl.Vocabulary.check_reserved_vocabulary_valid_iff o).mpr valid.2.2.1)))
  cases check with
  | Valid =>
    obtain ⟨r, stage, staged⟩ := typing_stage_correct o shape correct
    exact ⟨r, by simp [dl_validity.vocabulary_stage, run, stage], staged⟩
  | ReservedOntologyIri iri =>
    exact ⟨.ReservedOntologyIri iri, by simp [dl_validity.vocabulary_stage, run], shape, correct,
      reject (by simp)⟩
  | ReservedVersionIri iri =>
    exact ⟨.ReservedVersionIri iri, by simp [dl_validity.vocabulary_stage, run], shape, correct,
      reject (by simp)⟩
  | ForbiddenEntity iri kind =>
    exact ⟨.ReservedEntity iri kind, by simp [dl_validity.vocabulary_stage, run], shape, correct,
      reject (by simp)⟩

/-- The composed check terminates and returns `Valid` exactly for `OwlDlValid`
    ontologies; otherwise the first violated restriction in the documented
    order, with its component evidence and every earlier restriction proved. -/
theorem check_ontology_total_correct (o : RawOntology) :
    ∃ r, dl_validity.check_ontology o = .ok r ∧ Correct o r := by
  obtain ⟨keys, keysRun, keysCorrect⟩ := Rowl.Keys.check_keys_total_correct o.axioms
  cases keys with
  | some item =>
    exact ⟨.EmptyKey item, by simp [dl_validity.check_ontology, keysRun], keysCorrect,
      fun valid => keysCorrect.1 (valid.1 item (member_of_split keysCorrect.2))⟩
  | none =>
    obtain ⟨arity, arityRun, arityCorrect⟩ := Rowl.Arity.check_arities_total_correct o.axioms
    cases arity with
    | some item =>
      exact ⟨.Arity item, by simp [dl_validity.check_ontology, keysRun, arityRun], keysCorrect, arityCorrect,
        fun valid => arityCorrect.1 (valid.2.1 item (member_of_split arityCorrect.2))⟩
    | none =>
      obtain ⟨r, stage, staged⟩ := vocabulary_stage_correct o ⟨keysCorrect, arityCorrect⟩
      exact ⟨r, by simp [dl_validity.check_ontology, keysRun, arityRun, stage], staged⟩

private theorem correct_rejects (o : RawOntology) (r : DlCheck) (correct : Correct o r)
    (failure : r ≠ .Valid) : ¬ OwlDlValid o := by
  cases r <;> simp only [Correct] at correct
  case Valid => exact absurd rfl failure
  all_goals tauto

/-- No false acceptance or rejection of the OWL 2 DL restrictions of `OwlDlValid`. -/
theorem check_ontology_valid_iff (o : RawOntology) :
    dl_validity.check_ontology o = .ok .Valid ↔ OwlDlValid o := by
  obtain ⟨r, run, correct⟩ := check_ontology_total_correct o
  rw [run]
  constructor
  · intro same
    have := Result.ok_injective same
    subst this
    exact correct
  · intro valid
    by_cases accepted : r = .Valid
    · subst accepted
      rfl
    · exact absurd valid (correct_rejects o r correct accepted)

/-! ## Restrictions on the built-in vocabulary -/

private theorem listN_mem_size {α : Type} [SizeOf α] {n : Nat}
    (xs : Aeneas.Data.ListN.ListN α n) {x : α} (h : x ∈ xs.toList) : sizeOf x < sizeOf xs := by
  induction xs with
  | nil => simp [Aeneas.Data.ListN.ListN.toList] at h
  | cons head tail ih =>
    simp only [Aeneas.Data.ListN.ListN.toList, List.mem_cons] at h
    rcases h with rfl | h
    · simp +arith
    · have := ih h
      simp only [Data.ListN.ListN.cons.sizeOf_spec]
      omega
private theorem vec_mem_size {α : Type} [SizeOf α] (xs : alloc.vec.Vec α)
    {x : α} (h : x ∈ xs.val) : sizeOf x < sizeOf xs := by
  have := listN_mem_size xs.slice.list h
  cases xs with | mk slice => cases slice; simp_all [alloc.vec.Vec.val, Slice.val]; omega
private theorem first_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.first < sizeOf xs := by
  cases xs; simp +arith
private theorem second_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.second < sizeOf xs := by
  cases xs; simp +arith
private theorem rest_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.rest < sizeOf xs := by
  cases xs; simp +arith

private theorem expression_key_used (property : ObjectPropertyExpression) :
    ((Rowl.Roles.expressionKey property).1, EntityKind.ObjectProperty) ∈ Rowl.Collection.objectUses property := by
  cases property <;> simp [Rowl.Roles.expressionKey, Rowl.Collection.objectUses]

/-- Every role a class expression requires to be simple occurs in it as an object property. -/
private theorem class_required_used (expression : ClassExpression) :
    ∀ key ∈ Rowl.Roles.ClassRequired expression,
      (key.1, EntityKind.ObjectProperty) ∈ Rowl.Collection.classUses expression := by
  cases expression with
  | ObjectIntersectionOf values | ObjectUnionOf values =>
    have first := class_required_used values.first
    have second := class_required_used values.second
    have rest : ∀ e ∈ values.rest.val, ∀ key ∈ Rowl.Roles.ClassRequired e,
        (key.1, EntityKind.ObjectProperty) ∈ Rowl.Collection.classUses e :=
      fun e _ => class_required_used e
    intro key member
    simp only [Rowl.Roles.ClassRequired, List.mem_append, List.mem_flatMap, List.mem_attach, true_and,
      Subtype.exists] at member
    simp only [Rowl.Collection.classUses, List.mem_append, List.mem_flatMap, List.mem_attach, true_and,
      Subtype.exists]
    rcases member with (m | m) | ⟨e, em, m⟩
    · exact .inl (.inl (first key m))
    · exact .inl (.inr (second key m))
    · exact .inr ⟨e, em, rest e em key m⟩
  | ObjectComplementOf child =>
    have ih := class_required_used child
    intro key member
    simp only [Rowl.Roles.ClassRequired] at member
    simp only [Rowl.Collection.classUses]
    exact ih key member
  | ObjectSomeValuesFrom property child | ObjectAllValuesFrom property child =>
    have ih := class_required_used child
    intro key member
    simp only [Rowl.Roles.ClassRequired] at member
    simp only [Rowl.Collection.classUses]
    exact List.mem_append_right _ (ih key member)
  | ObjectHasSelf property =>
    intro key member
    simp only [Rowl.Roles.ClassRequired, List.mem_singleton] at member
    subst member
    simpa [Rowl.Collection.classUses] using expression_key_used property
  | ObjectMinCardinality n property filler | ObjectMaxCardinality n property filler
  | ObjectExactCardinality n property filler =>
    intro key member
    cases filler with
    | none =>
      rw [Rowl.Roles.ClassRequired] at member
      rw [Rowl.Collection.classUses]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst member
      exact List.mem_append_left _ (expression_key_used property)
    | some child =>
      have ih := class_required_used child
      rw [Rowl.Roles.ClassRequired] at member
      rw [Rowl.Collection.classUses]
      rcases List.mem_cons.mp member with same | inner
      · subst same
        exact List.mem_append_left _ (expression_key_used property)
      · exact List.mem_append_right _ (ih key inner)
  | _ => simp [Rowl.Roles.ClassRequired]
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size values; omega) | (have := second_size values; omega) |
    (have := vec_mem_size values.rest ‹_ ∈ _›; have := rest_size values; omega)

private theorem classes_required_used (values : List ClassExpression) (key : Rowl.Roles.Key)
    (member : key ∈ values.flatMap Rowl.Roles.ClassRequired) :
    (key.1, EntityKind.ObjectProperty) ∈ values.flatMap Rowl.Collection.classUses := by
  simp only [List.mem_flatMap] at member ⊢
  obtain ⟨c, inside, found⟩ := member
  exact ⟨c, inside, class_required_used c key found⟩

/-- Every role an axiom requires to be simple occurs in it as an object property. -/
private theorem axiom_required_used (item : AnnotatedAxiom) (key : Rowl.Roles.Key)
    (member : key ∈ Rowl.Roles.AxiomRequired item.axiom) :
    (key.1, EntityKind.ObjectProperty) ∈ Rowl.Collection.annotatedUses item := by
  unfold Rowl.Collection.annotatedUses
  apply List.mem_append_right
  cases h : item.axiom with
  | SubClassOf a b =>
    rw [h] at member
    simp only [Rowl.Roles.AxiomRequired, List.mem_append] at member
    simp only [Rowl.Collection.axiomUses, List.mem_append]
    rcases member with m | m
    · exact .inl (class_required_used a key m)
    · exact .inr (class_required_used b key m)
  | EquivalentClasses values | DisjointClasses values =>
    rw [h] at member
    simp only [Rowl.Collection.axiomUses]
    apply classes_required_used
    simpa [Rowl.Roles.AxiomRequired, AtLeastTwo.elements] using member
  | DisjointUnion c values =>
    rw [h] at member
    simp only [Rowl.Collection.axiomUses]
    apply List.mem_cons_of_mem
    apply classes_required_used
    simpa [Rowl.Roles.AxiomRequired, AtLeastTwo.elements] using member
  | ObjectPropertyDomain p c | ObjectPropertyRange p c =>
    rw [h] at member
    simp only [Rowl.Roles.AxiomRequired] at member
    simp only [Rowl.Collection.axiomUses]
    exact List.mem_append_right _ (class_required_used c key member)
  | DataPropertyDomain p c =>
    rw [h] at member
    simp only [Rowl.Roles.AxiomRequired] at member
    simp only [Rowl.Collection.axiomUses]
    exact List.mem_append_right _ (class_required_used c key member)
  | HasKey c objects datas =>
    rw [h] at member
    simp only [Rowl.Roles.AxiomRequired] at member
    simp only [Rowl.Collection.axiomUses, List.append_assoc]
    exact List.mem_append_left _ (class_required_used c key member)
  | ClassAssertion c individual =>
    rw [h] at member
    simp only [Rowl.Roles.AxiomRequired] at member
    simp only [Rowl.Collection.axiomUses]
    exact List.mem_append_left _ (class_required_used c key member)
  | FunctionalObjectProperty p | InverseFunctionalObjectProperty p | IrreflexiveObjectProperty p
  | AsymmetricObjectProperty p =>
    rw [h] at member
    simp only [Rowl.Roles.AxiomRequired, List.mem_singleton] at member
    subst member
    simpa [Rowl.Collection.axiomUses] using expression_key_used p
  | DisjointObjectProperties values =>
    rw [h] at member
    simp only [Rowl.Roles.AxiomRequired, Rowl.Roles.PropertyKeys, List.mem_cons, List.mem_map] at member
    simp only [Rowl.Collection.axiomUses, AtLeastTwo.elements, List.flatMap_cons, List.mem_append,
      List.mem_flatMap]
    rcases member with same | same | ⟨p, inside, same⟩
    · subst same; exact .inl (expression_key_used values.first)
    · subst same; exact .inr (.inl (expression_key_used values.second))
    · subst same; exact .inr (.inr ⟨p, inside, expression_key_used p⟩)
  | _ => rw [h] at member; simp [Rowl.Roles.AxiomRequired] at member

/-- The restrictions OWL 2 DL places on the built-in vocabulary hold for every
    valid ontology: reserved IRIs have exactly their built-in roles and name
    neither the ontology nor its version (§3.1, §5.1–5.6); `owl:topDataProperty`
    is only a SubDataPropertyOf superproperty (§11.2); `owl:topObjectProperty`
    and `owl:bottomObjectProperty`, which §11.1 makes composite, never stand where
    a simple object property is required (§11.2); and no datatype definition
    defines `rdfs:Literal` or a datatype of the OWL 2 datatype map (§11.2). -/
theorem builtin_vocabulary_restrictions (o : RawOntology) (valid : OwlDlValid o) :
    Rowl.Vocabulary.VocabularyOK o ∧
    Rowl.TopData.ClosureOK o.axioms.val ∧
    (∀ role ∈ o.axioms.val.flatMap (fun item => Rowl.Roles.AxiomRequired item.axiom),
      role.2 = false → ¬ Rowl.Roles.BuiltinComposite role.1) ∧
    (∀ item ∈ o.axioms.val, ∀ datatype range, item.axiom = .DatatypeDefinition datatype range →
      ¬ Rowl.DatatypeDefinitions.Predefined datatype.iri) := by
  obtain ⟨_, _, vocabulary, _, top, datatypes, simple, _, _⟩ := valid
  refine ⟨vocabulary, top, fun role member direct builtin => ?_, fun item inside datatype range shape predefined => ?_⟩
  · have notSimple : ¬ Rowl.Roles.Simple o.axioms.val role := by
      intro isSimple
      apply isSimple role Relation.ReflTransGen.refl
      simp only [List.mem_flatMap] at member
      obtain ⟨item, inside, required⟩ := member
      have used := axiom_required_used item role required
      simp only [Rowl.Roles.Composite, List.mem_flatMap]
      refine ⟨item, inside, List.mem_append_left _ ?_⟩
      simp only [Rowl.Roles.BuiltinSeeds, List.mem_flatMap]
      refine ⟨(role.1, EntityKind.ObjectProperty), used, ?_⟩
      have shape : role = (role.1, false) := by
        obtain ⟨iri, orientation⟩ := role
        simp at direct
        simp [direct]
      simp [builtin, ← shape]
    exact notSimple (simple role member)
  · have occurs : (datatype.iri, EntityKind.Datatype) ∈ o.axioms.val.flatMap Rowl.Collection.annotatedUses := by
      simp only [List.mem_flatMap]
      refine ⟨item, inside, ?_⟩
      simp [Rowl.Collection.annotatedUses, shape, Rowl.Collection.axiomUses]
    have available := datatypes.1.1 datatype.iri occurs
    simp only [Rowl.DatatypeDefinitions.Available, predefined, ↓reduceIte] at available
    exact available item inside (by simp [Rowl.DatatypeDefinitions.Defines, shape])

/-- Punning (§5.9): one IRI may name entities of several kinds. The typing
    constraints forbid only a class together with a datatype and two different
    kinds of property; every other pair of kinds may share an IRI. -/
theorem typing_allows_punning (a b : EntityKind) :
    ¬ Rowl.Typing.Forbidden a b ↔
      a = b ∨ a = .NamedIndividual ∨ b = .NamedIndividual ∨
      ((a = .Class ∨ a = .Datatype) ∧
        (b = .ObjectProperty ∨ b = .DataProperty ∨ b = .AnnotationProperty)) ∨
      ((a = .ObjectProperty ∨ a = .DataProperty ∨ a = .AnnotationProperty) ∧
        (b = .Class ∨ b = .Datatype)) := by
  cases a <;> cases b <;> simp [Rowl.Typing.Forbidden]

/-! ## Annotations have no logical effect -/

/-- The four annotation axioms (§10.2). -/
def annotationAxiom : Axiom → Bool
  | .AnnotationAssertion _ _ _ => true
  | .SubAnnotationPropertyOf _ _ => true
  | .AnnotationPropertyDomain _ _ => true
  | .AnnotationPropertyRange _ _ => true
  | _ => false

/-- The closure without its annotation axioms and without the annotations of
    the remaining axioms, nested annotations included. -/
def stripAnnotations (closure : Rowl.Owl.AxiomClosure) : Rowl.Owl.AxiomClosure :=
  (closure.filter (fun item => !annotationAxiom item.axiom)).map
    (fun item => { item with annotations := alloc.vec.Vec.new Annotation })

universe u v w

/-- Every interpretation satisfies an annotation axiom. -/
theorem annotation_axioms_hold {Object : Type u} {Value : Type v}
    (I : Rowl.Owl.Interpretation Object Value) (body : Axiom) (annotation : annotationAxiom body = true) :
    Rowl.Owl.satisfies I body := by
  cases body <;> simp_all [annotationAxiom, Rowl.Owl.satisfies]

/-- An interpretation satisfies a closure exactly when it satisfies the closure
    without annotations and annotation axioms. -/
theorem strip_annotations_satisfies {Object : Type u} {Value : Type v}
    (I : Rowl.Owl.Interpretation Object Value) (closure : Rowl.Owl.AxiomClosure) :
    Rowl.Owl.satisfiesClosure I (stripAnnotations closure) ↔ Rowl.Owl.satisfiesClosure I closure := by
  simp only [Rowl.Owl.satisfiesClosure, stripAnnotations, List.mem_map, List.mem_filter]
  constructor
  · intro stripped item member
    by_cases annotation : annotationAxiom item.axiom = true
    · exact annotation_axioms_hold I item.axiom annotation
    · exact stripped { item with annotations := alloc.vec.Vec.new Annotation }
        ⟨item, ⟨member, by simpa using annotation⟩, rfl⟩
  · rintro all _ ⟨item, ⟨member, _⟩, rfl⟩
    exact all item member

/-- A closure and its annotation-stripped version have the same models, for
    every reinterpretation of the anonymous individuals. -/
theorem strip_annotations_models {Object : Type u} {Value : Type v}
    (I : Rowl.Owl.Interpretation Object Value) (closure : Rowl.Owl.AxiomClosure) :
    Rowl.Owl.modelsClosure I (stripAnnotations closure) ↔ Rowl.Owl.modelsClosure I closure := by
  simp only [Rowl.Owl.modelsClosure, strip_annotations_satisfies]

theorem strip_annotations_model {Object : Type u} {Value : Type v} {Native : Type w}
    (D : Rowl.Owl.DatatypeMap Native) (embed : Rowl.Owl.ValueEmbedding D Value) (V : Rowl.Owl.Vocabulary)
    (I : Rowl.Owl.Interpretation Object Value) (closure : Rowl.Owl.AxiomClosure) :
    Rowl.Owl.Model D embed V I (stripAnnotations closure) ↔ Rowl.Owl.Model D embed V I closure := by
  simp only [Rowl.Owl.Model, strip_annotations_models]

/-- Annotations change neither consistency nor entailment. -/
theorem strip_annotations_consistent {Native : Type w} (D : Rowl.Owl.DatatypeMap Native)
    (V : Rowl.Owl.Vocabulary) (closure : Rowl.Owl.AxiomClosure) :
    Rowl.Owl.Consistent.{u,v,w} D V (stripAnnotations closure) ↔ Rowl.Owl.Consistent.{u,v,w} D V closure := by
  simp only [Rowl.Owl.Consistent, strip_annotations_model]

theorem strip_annotations_entails {Native : Type w} (D : Rowl.Owl.DatatypeMap Native)
    (V : Rowl.Owl.Vocabulary) (source target : Rowl.Owl.AxiomClosure) :
    Rowl.Owl.Entails.{u,v,w} D V (stripAnnotations source) (stripAnnotations target) ↔
      Rowl.Owl.Entails.{u,v,w} D V source target := by
  simp only [Rowl.Owl.Entails, strip_annotations_model]


end Rowl.DlValidity
