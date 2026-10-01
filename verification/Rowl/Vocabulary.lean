import Rowl.Builtins
import Rowl.Collection

namespace Rowl.Vocabulary
open Aeneas Aeneas.Std RowlRust.model RowlRust.typing RowlRust.collection RowlRust.vocabulary
attribute [local instance] Classical.propDecidable

/-- Four reviewed namespace strings, independently expressed as byte lists. -/
def reservedPrefixes : List (List U8) := [
  [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8],
  [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 48#u8, 47#u8, 48#u8, 49#u8, 47#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8],
  [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8],
  [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8]
  ]

def Reserved (key : List U8) : Prop := ∃ pattern ∈ reservedPrefixes, pattern.IsPrefix key

def EntityAllowed (iri : Iri) (kind : EntityKind) : Prop :=
  ¬ Reserved iri.spelling.val ∨ Rowl.Builtins.role iri.spelling.val = some kind

def HeaderAllowed : OntologyIdentity → Prop
  | .Anonymous => True
  | .Named ontology version => ¬ Reserved ontology.spelling.val ∧
      ∀ iri ∈ version, ¬ Reserved iri.spelling.val

def ontologyUses (ontology : RawOntology) : List (Iri × EntityKind) :=
  ontology.annotations.val.flatMap Rowl.Collection.annotationUses ++
    ontology.axioms.val.flatMap Rowl.Collection.annotatedUses

def VocabularyOK (ontology : RawOntology) : Prop := HeaderAllowed ontology.identity ∧
  ∀ row ∈ ontologyUses ontology, EntityAllowed row.1 row.2

/-- A diagnostic denotes the first forbidden entity occurrence. -/
inductive FirstForbidden : List (Iri × EntityKind) → Iri → EntityKind → Prop
  | here {iri kind tail} : ¬ EntityAllowed iri kind → FirstForbidden ((iri, kind) :: tail) iri kind
  | later {iri kind tail bad badKind} : EntityAllowed iri kind →
      FirstForbidden tail bad badKind → FirstForbidden ((iri, kind) :: tail) bad badKind

def Correct (ontology : RawOntology) : VocabularyResult → Prop
  | .Valid => VocabularyOK ontology
  | .ReservedOntologyIri iri => ∃ version,
      ontology.identity = .Named iri version ∧ Reserved iri.spelling.val
  | .ReservedVersionIri iri => ∃ header,
      ontology.identity = .Named header (some iri) ∧ ¬ Reserved header.spelling.val ∧ Reserved iri.spelling.val
  | .ForbiddenEntity iri kind => HeaderAllowed ontology.identity ∧ FirstForbidden (ontologyUses ontology) iri kind

private theorem prefix_correct (key : alloc.vec.Vec U8) (pattern : Slice U8) (index : Usize) :
    prefix_from key pattern index = .ok (decide ((pattern.val.drop index.val).IsPrefix (key.val.drop index.val))) := by
  rw [prefix_from]
  by_cases hp : index.val < pattern.val.length
  · have notPrefixEnd : ¬ pattern.val.length ≤ index.val := by omega
    by_cases hk : index.val < key.val.length
    · have notKeyEnd : ¬ key.val.length ≤ index.val := by omega
      have keyIndex : key.index_usize index = .ok key.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hk]
      have prefixIndex : pattern.index_usize index = .ok pattern.val[index.val] := by
        simp [Slice.index_usize, List.getElem?_eq_getElem hp]
      by_cases heads : key.val[index.val] = pattern.val[index.val]
      · have size := pattern.property
        obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextval : next.val = index.val + 1 := by simpa using hv
        have ih := prefix_correct key pattern next
        simp [notPrefixEnd, notKeyEnd, keyIndex, prefixIndex, heads, hn, ih]
        rw [List.drop_eq_getElem_cons hp, List.drop_eq_getElem_cons hk]
        simp only [heads, nextval, List.cons_prefix_cons, eq_self, true_and]
      · simp [notPrefixEnd, notKeyEnd, keyIndex, prefixIndex, heads]
        rw [List.drop_eq_getElem_cons hp, List.drop_eq_getElem_cons hk]
        simp only [List.cons_prefix_cons, Ne.symm heads, false_and, not_false_eq_true]
    · have endKey : key.val.length ≤ index.val := by omega
      simp [notPrefixEnd, endKey]
  · have endPrefix : pattern.val.length ≤ index.val := by omega
    simp [endPrefix]
termination_by pattern.val.length - index.val
decreasing_by omega

/-- Reserved vocabulary includes every IRI with one of the four exact prefixes,
    not only recognized built-ins. Lookalikes are compared without normalization. -/
theorem reserved_iri_total_correct (key : alloc.vec.Vec U8) :
    reserved_iri key = .ok (decide (Reserved key.val)) := by
  simp [reserved_iri, prefix_correct, Reserved, reservedPrefixes, Array.to_slice, Array.make, lift]
  repeat' (split <;> simp_all)

theorem entity_iri_allowed_total_correct (iri : Iri) (kind : EntityKind) :
    entity_iri_allowed iri kind = .ok (decide (EntityAllowed iri kind)) := by
  unfold entity_iri_allowed
  rw [reserved_iri_total_correct]
  by_cases reserved : Reserved iri.spelling.val
  · simp only [reserved, decide_true, bind_ok, ↓reduceIte]
    rw [Rowl.Builtins.builtin_kind_total_correct]
    cases role : Rowl.Builtins.role iri.spelling.val with
    | none => simp [reserved, role, EntityAllowed]
    | some builtin => cases builtin <;> cases kind <;> simp [reserved, role, EntityAllowed]
  · simp [reserved, EntityAllowed]

private def UsesCorrect (uses : EntityUses) : VocabularyResult → Prop
  | .Valid => ∀ row ∈ Rowl.Collection.rows uses, EntityAllowed row.1 row.2
  | .ForbiddenEntity iri kind => FirstForbidden (Rowl.Collection.rows uses) iri kind
  | _ => False

private theorem check_uses_correct (uses : EntityUses) :
    ∃ result, check_uses uses = .ok result ∧ UsesCorrect uses result := by
  induction uses with
  | Empty => exact ⟨.Valid, by simp [check_uses], by simp [UsesCorrect, Rowl.Collection.rows]⟩
  | Entry iri kind next ih =>
    rw [check_uses, entity_iri_allowed_total_correct]
    by_cases allowed : EntityAllowed iri kind
    · obtain ⟨result, hr, correct⟩ := ih
      refine ⟨result, by simp [allowed, hr], ?_⟩
      cases result with
      | Valid => simpa [UsesCorrect, Rowl.Collection.rows, allowed] using correct
      | ForbiddenEntity bad badKind => exact .later allowed correct
      | ReservedOntologyIri bad => exact False.elim correct
      | ReservedVersionIri bad => exact False.elim correct
    · exact ⟨.ForbiddenEntity iri kind, by simp [allowed], .here allowed⟩

private theorem checked_entities (ontology : RawOntology) (headers : HeaderAllowed ontology.identity) :
    ∃ result, (do let collected ← ontology_entities ontology; check_uses collected.uses) = .ok result ∧
      Correct ontology result := by
  obtain ⟨collected, hc, collection⟩ := Rowl.Collection.ontology_entities_total_correct ontology
  obtain ⟨result, hr, correct⟩ := check_uses_correct collected.uses
  refine ⟨result, by simp [hc, hr], ?_⟩
  have collectedRows : Rowl.Collection.rows collected.uses = ontologyUses ontology := collection.2
  cases result with
  | Valid => exact ⟨headers, by simpa [UsesCorrect, collectedRows] using correct⟩
  | ForbiddenEntity bad badKind => exact ⟨headers, by simpa [UsesCorrect, collectedRows] using correct⟩
  | ReservedOntologyIri bad => exact False.elim correct
  | ReservedVersionIri bad => exact False.elim correct

/-- Total actual-AST checking, with headers first and exact first-use diagnostics. -/
theorem check_reserved_vocabulary_total_correct (ontology : RawOntology) :
    ∃ result, check_reserved_vocabulary ontology = .ok result ∧ Correct ontology result := by
  cases identity : ontology.identity with
  | Anonymous =>
    obtain ⟨result, hr, correct⟩ := checked_entities ontology (by simp [HeaderAllowed, identity])
    exact ⟨result, by simp only [check_reserved_vocabulary, identity]; exact hr, correct⟩
  | Named header version =>
    by_cases reservedHeader : Reserved header.spelling.val
    · exact ⟨.ReservedOntologyIri header,
        by simp [check_reserved_vocabulary, identity, reserved_iri_total_correct, reservedHeader],
        version, identity, reservedHeader⟩
    · cases version with
      | none =>
        obtain ⟨result, hr, correct⟩ := checked_entities ontology (by simp [HeaderAllowed, identity, reservedHeader])
        exact ⟨result, by simp only [check_reserved_vocabulary, identity, reserved_iri_total_correct, reservedHeader, decide_false, bind_ok]; exact hr, correct⟩
      | some version =>
        by_cases reservedVersion : Reserved version.spelling.val
        · exact ⟨.ReservedVersionIri version,
            by simp [check_reserved_vocabulary, identity, reserved_iri_total_correct, reservedHeader, reservedVersion],
            header, identity, reservedHeader, reservedVersion⟩
        · obtain ⟨result, hr, correct⟩ := checked_entities ontology (by simp [HeaderAllowed, identity, reservedHeader, reservedVersion])
          exact ⟨result, by simp only [check_reserved_vocabulary, identity, reserved_iri_total_correct, reservedHeader, reservedVersion, decide_false, bind_ok]; exact hr, correct⟩

private theorem forbidden_excludes_allowed {rows : List (Iri × EntityKind)} {iri : Iri} {kind : EntityKind}
    (bad : FirstForbidden rows iri kind) : ¬ (∀ row ∈ rows, EntityAllowed row.1 row.2) := by
  induction bad with
  | here invalid => intro all; exact invalid (all (_, _) (List.mem_cons_self))
  | later allowed failure ih => intro all; exact ih (fun row mem => all row (by simp [mem]))

/-- Acceptance iff all header/entity restrictions hold on the actual raw input.
    This claim is deliberately separate from parsing and complete DL validation. -/
theorem check_reserved_vocabulary_valid_iff (ontology : RawOntology) :
    check_reserved_vocabulary ontology = .ok .Valid ↔ VocabularyOK ontology := by
  obtain ⟨result, hr, correct⟩ := check_reserved_vocabulary_total_correct ontology
  constructor
  · intro accepted
    have same := Result.ok_injective (hr.symm.trans accepted)
    rw [same] at correct
    exact correct
  · intro valid
    cases result with
    | Valid => exact hr
    | ForbiddenEntity iri kind => exact False.elim (forbidden_excludes_allowed correct.2 valid.2)
    | ReservedOntologyIri iri =>
      obtain ⟨version, identity, reserved⟩ := correct
      have allowed := valid.1
      simp [HeaderAllowed, identity, reserved] at allowed
    | ReservedVersionIri iri =>
      obtain ⟨header, identity, _, reserved⟩ := correct
      have allowed := valid.1
      simp [HeaderAllowed, identity, reserved] at allowed

end Rowl.Vocabulary
