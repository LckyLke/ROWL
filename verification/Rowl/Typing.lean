import Rowl.Generated.RowlKernel

namespace Rowl.Typing
open Aeneas Aeneas.Std RowlRust.typing

deriving instance DecidableEq for EntityKind
attribute [local instance] Classical.propDecidable

def occurrences : Occurrences → List (U32 × EntityKind)
  | .Empty => []
  | .Entry symbol kind next => (symbol, kind) :: occurrences next

/-- The only forbidden combinations in §5.8.1. Class/individual/property reuse
    across these groups is allowed, and named declarations are optional. -/
def Forbidden (a b : EntityKind) : Prop :=
  (a = .Class ∧ b = .Datatype) ∨ (a = .Datatype ∧ b = .Class) ∨
  (a = .ObjectProperty ∧ (b = .DataProperty ∨ b = .AnnotationProperty)) ∨
  (a = .DataProperty ∧ (b = .ObjectProperty ∨ b = .AnnotationProperty)) ∨
  (a = .AnnotationProperty ∧ (b = .ObjectProperty ∨ b = .DataProperty))

private theorem forbidden_symm (a b : EntityKind) : Forbidden a b ↔ Forbidden b a := by
  cases a <;> cases b <;> simp [Forbidden]
private theorem forbidden_irrefl (a : EntityKind) : ¬ Forbidden a a := by
  cases a <;> simp [Forbidden]
private theorem same_kind_correct (a b : EntityKind) : same_kind a b = .ok (decide (a = b)) := by
  cases a <;> cases b <;> simp [same_kind]
private theorem conflicting_correct (a b : EntityKind) :
    conflicting_kinds a b = .ok (decide (Forbidden a b)) := by
  cases a <;> cases b <;> simp [conflicting_kinds, Forbidden]

private theorem declared_correct (ds : Occurrences) (symbol : U32) (kind : EntityKind) :
    declared ds symbol kind = .ok (decide ((symbol, kind) ∈ occurrences ds)) := by
  induction ds with
  | Empty => simp [declared, occurrences]
  | Entry here hereKind next ih =>
    rw [declared]
    by_cases hs : here = symbol
    · subst here
      by_cases hk : hereKind = kind
      · subst hereKind
        simp [same_kind_correct, occurrences]
      · simp only [same_kind_correct, hk, decide_false, ↓reduceIte,
          ih, occurrences, List.mem_cons, Prod.mk.injEq, true_and, Ne.symm hk, false_or]
        simp
    · simp only [hs, ↓reduceIte, ih, occurrences, List.mem_cons, Prod.mk.injEq,
        Ne.symm hs, false_and, false_or]

private def ConflictWith (ds : Occurrences) (symbol : U32) (kind : EntityKind) : Prop :=
  ∃ other, (symbol, other) ∈ occurrences ds ∧ Forbidden other kind

private theorem has_conflict_correct (ds : Occurrences) (symbol : U32) (kind : EntityKind) :
    has_conflict ds symbol kind = .ok (decide (ConflictWith ds symbol kind)) := by
  induction ds with
  | Empty => simp [has_conflict, ConflictWith, occurrences]
  | Entry here hereKind next ih =>
    rw [has_conflict]
    by_cases hs : here = symbol
    · subst here
      by_cases hf : Forbidden hereKind kind
      · simp [conflicting_correct, hf, ConflictWith, occurrences]
      · simp [conflicting_correct, hf, ih, ConflictWith, occurrences]
    · simp only [hs, ↓reduceIte, ih, ConflictWith, occurrences, List.mem_cons,
        Prod.mk.injEq, Ne.symm hs, false_and, false_or]
      rfl

private def NoConflicts (ds : Occurrences) : Prop :=
  (occurrences ds).Pairwise (fun a b => a.1 = b.1 → ¬ Forbidden b.2 a.2)

def ConflictAt (ds : Occurrences) (symbol : U32) : Prop :=
  ∃ a b, (symbol, a) ∈ occurrences ds ∧ (symbol, b) ∈ occurrences ds ∧ Forbidden a b

private theorem first_conflict_correct (ds : Occurrences) :
    ∃ result, first_conflict ds = .ok result ∧
      (result = none ↔ NoConflicts ds) ∧
      (∀ symbol, result = some symbol → ConflictAt ds symbol) := by
  induction ds with
  | Empty => exact ⟨none, by simp [first_conflict], by simp [NoConflicts, occurrences], by simp⟩
  | Entry symbol kind next ih =>
    obtain ⟨result, hr, hn, he⟩ := ih
    have hc := has_conflict_correct next symbol kind
    by_cases conflict : ConflictWith next symbol kind
    · refine ⟨some symbol, by simp [first_conflict, hc, conflict], ?_, ?_⟩
      · obtain ⟨other, hm, hf⟩ := conflict
        simp only [Option.some_ne_none, NoConflicts, occurrences, List.pairwise_cons,
          false_iff, not_and]
        intro all _
        exact all (symbol, other) hm rfl hf
      · intro target ht
        have eq := Option.some.inj ht
        subst target
        obtain ⟨other, hm, hf⟩ := conflict
        exact ⟨other, kind, by simp [occurrences, hm], by simp [occurrences], hf⟩
    · refine ⟨result, by simp [first_conflict, hc, conflict, hr], ?_, ?_⟩
      · have all : ∀ p ∈ occurrences next, symbol = p.1 → ¬ Forbidden p.2 kind := by
          rintro ⟨s, k⟩ hm eq
          change symbol = s at eq
          subst s
          exact fun hf => conflict ⟨k, hm, hf⟩
        constructor
        · intro h; exact List.pairwise_cons.mpr ⟨all, hn.mp h⟩
        · intro h; exact hn.mpr (List.pairwise_cons.mp h).2
      · intro target ht
        obtain ⟨a, b, ha, hb, hf⟩ := he target ht
        exact ⟨a, b, List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb, hf⟩

private def UsesDeclared (ds uses : Occurrences) : Prop :=
  ∀ symbol kind, (symbol, kind) ∈ occurrences uses → kind ≠ .NamedIndividual →
    (symbol, kind) ∈ occurrences ds

def MissingAt (ds uses : Occurrences) (symbol : U32) : Prop :=
  ∃ kind, (symbol, kind) ∈ occurrences uses ∧ kind ≠ .NamedIndividual ∧
    (symbol, kind) ∉ occurrences ds

private theorem first_missing_correct (ds uses : Occurrences) :
    ∃ result, first_missing ds uses = .ok result ∧
      (result = none ↔ UsesDeclared ds uses) ∧
      (∀ symbol, result = some symbol → MissingAt ds uses symbol) := by
  induction uses with
  | Empty => exact ⟨none, by simp [first_missing], by simp [UsesDeclared, occurrences], by simp⟩
  | Entry symbol kind next ih =>
    obtain ⟨result, hr, hn, he⟩ := ih
    have hd := declared_correct ds symbol kind
    by_cases present : kind = .NamedIndividual ∨ (symbol, kind) ∈ occurrences ds
    · have step : first_missing ds (.Entry symbol kind next) = .ok result := by
        rcases present with h | h
        · subst kind; simp [first_missing, hr]
        · cases kind <;> simp [first_missing, hd, h, hr]
      refine ⟨result, step, ?_, ?_⟩
      · have all : UsesDeclared ds (.Entry symbol kind next) ↔ UsesDeclared ds next := by
          unfold UsesDeclared
          constructor
          · intro h s k hm hk; exact h s k (List.mem_cons_of_mem _ hm) hk
          · intro h s k hm hk
            rcases List.mem_cons.mp hm with eq | hm
            · cases eq
              exact present.resolve_left hk
            · exact h s k hm hk
        exact hn.trans all.symm
      · intro s hs
        obtain ⟨k, hm, hn, hd⟩ := he s hs
        exact ⟨k, List.mem_cons_of_mem _ hm, hn, hd⟩
    · have notNamed : kind ≠ .NamedIndividual := fun h => present (Or.inl h)
      have absent : (symbol, kind) ∉ occurrences ds := fun h => present (Or.inr h)
      refine ⟨some symbol, ?_, ?_, ?_⟩
      · cases kind <;> simp_all [first_missing]
      · simp only [Option.some_ne_none, false_iff]
        intro h
        exact absent (h symbol kind (by simp [occurrences]) notNamed)
      · intro s hs
        have eq := Option.some.inj hs
        subst s
        exact ⟨kind, by simp [occurrences], notNamed, absent⟩

def WellTyped (ds uses : Occurrences) : Prop :=
  (∀ symbol, ¬ ConflictAt ds symbol) ∧ UsesDeclared ds uses

private theorem no_conflicts_iff (ds : Occurrences) :
    NoConflicts ds ↔ ∀ symbol, ¬ ConflictAt ds symbol := by
  induction ds with
  | Empty => simp [NoConflicts, ConflictAt, occurrences]
  | Entry s k next ih =>
    constructor
    · intro h symbol ⟨a, b, ha, hb, hf⟩
      obtain ⟨head, tail⟩ := List.pairwise_cons.mp h
      rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
      · cases ha; cases hb; exact forbidden_irrefl k hf
      · cases ha; exact head (s, b) hb rfl ((forbidden_symm _ _).mp hf)
      · cases hb; exact head (s, a) ha rfl hf
      · exact ih.mp tail symbol ⟨a, b, ha, hb, hf⟩
    · intro h
      apply List.pairwise_cons.mpr
      constructor
      · rintro ⟨symbol, kind⟩ hm eq hf
        change s = symbol at eq
        subst symbol
        exact h s ⟨kind, k, List.mem_cons_of_mem _ hm, by simp [occurrences], hf⟩
      · apply ih.mpr
        intro symbol ⟨a, b, ha, hb, hf⟩
        exact h symbol ⟨a, b, List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb, hf⟩

def Correct (ds uses : Occurrences) : TypingResult → Prop
  | .Valid => WellTyped ds uses
  | .ConflictingDeclarations symbol => ConflictAt ds symbol
  | .MissingDeclaration symbol => MissingAt ds uses symbol

def kindOf : RowlRust.model.Entity → EntityKind
  | .Class _ => .Class
  | .Datatype _ => .Datatype
  | .ObjectProperty _ => .ObjectProperty
  | .DataProperty _ => .DataProperty
  | .AnnotationProperty _ => .AnnotationProperty
  | .NamedIndividual _ => .NamedIndividual

/-- Role extraction covers all six raw structural entity constructors. -/
theorem entity_kind_total_correct (entity : RowlRust.model.Entity) :
    entity_kind entity = .ok (kindOf entity) := by cases entity <;> rfl

/-- Total correctness against declaration constraints, for complete supplied tables. -/
theorem validate_typing_total_correct (ds uses : Occurrences) :
    ∃ result, validate_typing ds uses = .ok result ∧ Correct ds uses result := by
  obtain ⟨conflict, hc, hn, he⟩ := first_conflict_correct ds
  cases conflict with
  | some symbol => exact ⟨.ConflictingDeclarations symbol, by simp [validate_typing, hc], he symbol rfl⟩
  | none =>
    obtain ⟨missing, hm, hd, hx⟩ := first_missing_correct ds uses
    cases missing with
    | some symbol => exact ⟨.MissingDeclaration symbol, by simp [validate_typing, hc, hm], hx symbol rfl⟩
    | none => exact ⟨.Valid, by simp [validate_typing, hc, hm],
        (no_conflicts_iff ds).mp (hn.mp rfl), hd.mp rfl⟩

/-- The actual validator accepts exactly the §5.8.1 typing predicate on these tables. -/
theorem validate_typing_valid_iff (ds uses : Occurrences) :
    validate_typing ds uses = .ok .Valid ↔ WellTyped ds uses := by
  obtain ⟨result, hr, hs⟩ := validate_typing_total_correct ds uses
  constructor
  · intro h
    have same := Result.ok_injective (hr.symm.trans h)
    rw [same] at hs
    exact hs
  · intro h
    cases result with
    | Valid => exact hr
    | ConflictingDeclarations symbol => exact False.elim (h.1 symbol hs)
    | MissingDeclaration symbol =>
      obtain ⟨kind, used, named, missing⟩ := hs
      exact False.elim (missing (h.2 symbol kind used named))

end Rowl.Typing
