import Rowl.Functional

namespace Rowl.FunctionalSelection
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.functional
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The complete standard terminal inventory, in deterministic selection order. -/
def AllTerminals : List Terminal := [
  .Keyword .Prefix,
  .Keyword .Ontology,
  .Keyword .Import,
  .Keyword .Declaration,
  .Keyword .Class,
  .Keyword .Datatype,
  .Keyword .ObjectProperty,
  .Keyword .DataProperty,
  .Keyword .AnnotationProperty,
  .Keyword .NamedIndividual,
  .Keyword .Annotation,
  .Keyword .AnnotationAssertion,
  .Keyword .SubAnnotationPropertyOf,
  .Keyword .AnnotationPropertyDomain,
  .Keyword .AnnotationPropertyRange,
  .Keyword .ObjectInverseOf,
  .Keyword .DataIntersectionOf,
  .Keyword .DataUnionOf,
  .Keyword .DataComplementOf,
  .Keyword .DataOneOf,
  .Keyword .DatatypeRestriction,
  .Keyword .ObjectIntersectionOf,
  .Keyword .ObjectUnionOf,
  .Keyword .ObjectComplementOf,
  .Keyword .ObjectOneOf,
  .Keyword .ObjectSomeValuesFrom,
  .Keyword .ObjectAllValuesFrom,
  .Keyword .ObjectHasValue,
  .Keyword .ObjectHasSelf,
  .Keyword .ObjectMinCardinality,
  .Keyword .ObjectMaxCardinality,
  .Keyword .ObjectExactCardinality,
  .Keyword .DataSomeValuesFrom,
  .Keyword .DataAllValuesFrom,
  .Keyword .DataHasValue,
  .Keyword .DataMinCardinality,
  .Keyword .DataMaxCardinality,
  .Keyword .DataExactCardinality,
  .Keyword .SubClassOf,
  .Keyword .EquivalentClasses,
  .Keyword .DisjointClasses,
  .Keyword .DisjointUnion,
  .Keyword .SubObjectPropertyOf,
  .Keyword .ObjectPropertyChain,
  .Keyword .EquivalentObjectProperties,
  .Keyword .DisjointObjectProperties,
  .Keyword .ObjectPropertyDomain,
  .Keyword .ObjectPropertyRange,
  .Keyword .InverseObjectProperties,
  .Keyword .FunctionalObjectProperty,
  .Keyword .InverseFunctionalObjectProperty,
  .Keyword .ReflexiveObjectProperty,
  .Keyword .IrreflexiveObjectProperty,
  .Keyword .SymmetricObjectProperty,
  .Keyword .AsymmetricObjectProperty,
  .Keyword .TransitiveObjectProperty,
  .Keyword .SubDataPropertyOf,
  .Keyword .EquivalentDataProperties,
  .Keyword .DisjointDataProperties,
  .Keyword .DataPropertyDomain,
  .Keyword .DataPropertyRange,
  .Keyword .FunctionalDataProperty,
  .Keyword .DatatypeDefinition,
  .Keyword .HasKey,
  .Keyword .SameIndividual,
  .Keyword .DifferentIndividuals,
  .Keyword .ClassAssertion,
  .Keyword .ObjectPropertyAssertion,
  .Keyword .NegativeObjectPropertyAssertion,
  .Keyword .DataPropertyAssertion,
  .Keyword .NegativeDataPropertyAssertion,
  .Open,
  .Close,
  .Equals,
  .DatatypeIndicator,
  .Integer,
  .QuotedString,
  .LanguageTag,
  .NodeId,
  .FullIri,
  .PrefixName,
  .AbbreviatedIri,
  .Whitespace,
  .Comment]
/-- Source candidates use exact canonical UTF-8 spans and the independent grammar. -/
def Candidate (bytes : List U8) (position : Nat) (terminal : Terminal) (endpoint : Nat) : Prop :=
  Rowl.Longest.Candidate bytes position (Rowl.Functional.TerminalLanguage terminal) endpoint
/-- The earliest inventory member among independent candidates at the selected
    endpoint. This mathematical filtered list does not execute the Rust scan. -/
def FirstCandidate (terminals : List Terminal) (bytes : List U8) (position : Nat) (token : Token) : Prop :=
  (terminals.filter (fun terminal => decide (Candidate bytes position terminal token.end.val))).head? = some token.terminal
private theorem first_append (terminals extra : List Terminal) (bytes : List U8) (position : Nat) (token : Token)
    (first : FirstCandidate terminals bytes position token) : FirstCandidate (terminals++extra) bytes position token := by
  unfold FirstCandidate at *
  rw [List.filter_append]
  cases filtered : terminals.filter (fun terminal => decide (Candidate bytes position terminal token.end.val)) with
  | nil => simp [filtered] at first
  | cons head tail => simpa [filtered] using first
private theorem first_final (terminals : List Terminal) (bytes : List U8) (position : Nat) (token : Token)
    (absent : ∀ terminal ∈ terminals, ¬ Candidate bytes position terminal token.end.val)
    (present : Candidate bytes position token.terminal token.end.val) :
    FirstCandidate (terminals++[token.terminal]) bytes position token := by
  have empty : terminals.filter (fun terminal => decide (Candidate bytes position terminal token.end.val)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro terminal included
    simp [absent terminal included]
  simp [FirstCandidate,List.filter_append,empty,present]

/-- The selected token is an actual eligible standard terminal at the greatest
    possible endpoint. No-match includes complete absence of eligible terminals. -/
def Correct (bytes : List U8) (position : Nat) : Selection → Prop
  | .NoMatch => (∃ word, Rowl.Regular.Utf8From bytes position word) ∧
      ∀ terminal endpoint, ¬ Candidate bytes position terminal endpoint
  | .Token token => (∃ word, Rowl.Regular.Utf8From bytes position word) ∧ token.start.val = position ∧
      Candidate bytes position token.terminal token.end.val ∧
      (∀ terminal endpoint, Candidate bytes position terminal endpoint → endpoint ≤ token.end.val) ∧
      FirstCandidate AllTerminals bytes position token
  | .MalformedUtf8 error => Rowl.Regular.Utf8Failure bytes position error
private def PassedCorrect (terminals : List Terminal) (bytes : List U8) (position : Nat) : Selection → Prop
  | .NoMatch => (∃ word, Rowl.Regular.Utf8From bytes position word) ∧
      ∀ terminal ∈ terminals, ∀ endpoint, ¬ Candidate bytes position terminal endpoint
  | .Token token => (∃ word, Rowl.Regular.Utf8From bytes position word) ∧ token.start.val = position ∧
      token.terminal ∈ terminals ∧ Candidate bytes position token.terminal token.end.val ∧
      (∀ terminal ∈ terminals, ∀ endpoint, Candidate bytes position terminal endpoint → endpoint ≤ token.end.val) ∧
      FirstCandidate terminals bytes position token
  | .MalformedUtf8 error => Rowl.Regular.Utf8Failure bytes position error

/-- Every terminal type, including all 71 keyword variants, is visited. -/
theorem inventory_complete (terminal : Terminal) : terminal ∈ AllTerminals := by
  cases terminal with
  | Keyword key => cases key <;> simp [AllTerminals]
  | _ => simp [AllTerminals]

private theorem seed_total (terminal : Terminal) (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ result, seed terminal bytes position = .ok result ∧ PassedCorrect [terminal] bytes.val position.val result := by
  obtain ⟨matched, executed, correct⟩ := Rowl.Functional.longest_total_correct terminal bytes position
  rw [seed, executed, bind_ok]
  cases matched with
  | MalformedUtf8 error => exact ⟨.MalformedUtf8 error, rfl, correct⟩
  | Matched endpoint =>
    obtain ⟨utf8, maximum⟩ := correct
    cases endpoint with
    | none =>
      refine ⟨.NoMatch, rfl, utf8, ?_⟩
      intro other included finish candidate
      have equal : other = terminal := by simpa using included
      subst other
      exact maximum finish candidate
    | some finish =>
      refine ⟨.Token ⟨terminal, position, finish⟩, rfl, utf8, rfl, by simp, maximum.1, ?_, ?_⟩
      · intro other included endpoint candidate
        have equal : other = terminal := by simpa using included
        subst other
        exact maximum.2 endpoint candidate
      · simp [FirstCandidate,show Candidate bytes.val position.val terminal finish.val from maximum.1]
@[local step] private theorem seed_spec (terminal : Terminal) (bytes : alloc.vec.Vec U8) (position : Usize) :
    seed terminal bytes position ⦃ result => PassedCorrect [terminal] bytes.val position.val result ⦄ := by
  obtain ⟨result, executed, correct⟩ := seed_total terminal bytes position
  simp [executed, correct]

private theorem extend_total (terminal : Terminal) (bytes : alloc.vec.Vec U8) (position : Usize)
    (previous : Selection) (passed : List Terminal) (invariant : PassedCorrect passed bytes.val position.val previous) :
    ∃ result, extend terminal bytes position previous = .ok result ∧
      PassedCorrect (passed ++ [terminal]) bytes.val position.val result := by
  rw [functional.extend.eq_def]
  cases previous with
  | MalformedUtf8 error => exact ⟨.MalformedUtf8 error, rfl, invariant⟩
  | NoMatch =>
    obtain ⟨result, executed, correct⟩ := seed_total terminal bytes position
    refine ⟨result, executed, ?_⟩
    cases result with
    | MalformedUtf8 error => exact correct
    | NoMatch =>
      refine ⟨correct.1, ?_⟩
      intro other included endpoint candidate
      rcases List.mem_append.mp included with old | fresh
      · exact invariant.2 other old endpoint candidate
      · exact correct.2 other fresh endpoint candidate
    | Token token =>
      refine ⟨correct.1, correct.2.1, by simp [correct.2.2.1], correct.2.2.2.1, ?_, ?_⟩
      · intro other included endpoint candidate
        rcases List.mem_append.mp included with old | fresh
        · exact False.elim (invariant.2 other old endpoint candidate)
        · exact correct.2.2.2.2.1 other fresh endpoint candidate
      · have kind : token.terminal = terminal := by simpa using correct.2.2.1
        rw [← kind]
        exact first_final passed bytes.val position.val token
          (fun other member => invariant.2 other member token.end.val) correct.2.2.2.1
  | Token prior =>
    obtain ⟨matched, executed, correct⟩ := Rowl.Functional.longest_total_correct terminal bytes position
    dsimp only
    rw [executed, bind_ok]
    cases matched with
    | MalformedUtf8 error => exact ⟨.MalformedUtf8 error, rfl, correct⟩
    | Matched endpoint =>
      obtain ⟨utf8, maximum⟩ := correct
      cases endpoint with
      | none =>
        refine ⟨.Token prior, rfl, invariant.1, invariant.2.1, by simp [invariant.2.2.1], invariant.2.2.2.1, ?_, ?_⟩
        · intro other included finish candidate
          rcases List.mem_append.mp included with old | fresh
          · exact invariant.2.2.2.2.1 other old finish candidate
          · have equal : other = terminal := by simpa using fresh
            subst other
            exact False.elim (maximum finish candidate)
        · exact first_append passed [terminal] bytes.val position.val prior invariant.2.2.2.2.2
      | some finish =>
        dsimp only
        by_cases larger : prior.end.val < finish.val
        · refine ⟨.Token ⟨terminal, position, finish⟩, by simp [UScalar.lt_equiv, larger], utf8, rfl, by simp, maximum.1, ?_, ?_⟩
          · intro other included endpoint candidate
            rcases List.mem_append.mp included with old | fresh
            · exact (invariant.2.2.2.2.1 other old endpoint candidate).trans (Nat.le_of_lt larger)
            · have equal : other = terminal := by simpa using fresh
              subst other
              exact maximum.2 endpoint candidate
          · apply first_final passed bytes.val position.val ⟨terminal,position,finish⟩ ?_ maximum.1
            intro other member candidate
            have := invariant.2.2.2.2.1 other member finish.val candidate
            omega
        · refine ⟨.Token prior, by simp [UScalar.lt_equiv, larger], invariant.1, invariant.2.1,
            by simp [invariant.2.2.1], invariant.2.2.2.1, ?_, ?_⟩
          · intro other included endpoint candidate
            rcases List.mem_append.mp included with old | fresh
            · exact invariant.2.2.2.2.1 other old endpoint candidate
            · have equal : other = terminal := by simpa using fresh
              subst other
              exact (maximum.2 endpoint candidate).trans (by omega)
          · exact first_append passed [terminal] bytes.val position.val prior invariant.2.2.2.2.2

@[local step] private theorem extend_spec (terminal : Terminal) (bytes : alloc.vec.Vec U8) (position : Usize)
    (previous : Selection) (passed : List Terminal) (invariant : PassedCorrect passed bytes.val position.val previous) :
    extend terminal bytes position previous ⦃ result => PassedCorrect (passed ++ [terminal]) bytes.val position.val result ⦄ := by
  obtain ⟨result, executed, correct⟩ := extend_total terminal bytes position previous passed invariant
  simp [executed, correct]

private theorem full_correct (bytes : List U8) (position : Nat) (result : Selection)
    (correct : PassedCorrect AllTerminals bytes position result) : Correct bytes position result := by
  cases result with
  | MalformedUtf8 error => exact correct
  | NoMatch => exact ⟨correct.1, fun terminal endpoint => correct.2 terminal (inventory_complete terminal) endpoint⟩
  | Token token => exact ⟨correct.1, correct.2.1, correct.2.2.2.1,
      (fun terminal endpoint => correct.2.2.2.2.1 terminal (inventory_complete terminal) endpoint),correct.2.2.2.2.2⟩

/-- The actual combined selector terminates, visits the full standard inventory,
    and returns an eligible terminal at the global greatest byte endpoint. -/
theorem next_terminal_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ result, next_terminal bytes position = .ok result ∧ Correct bytes.val position.val result := by
  apply WP.spec_imp_exists
  unfold next_terminal
  step*
  apply full_correct
  simpa [AllTerminals] using ‹PassedCorrect _ _ _ _›

/-- Combined selection succeeds exactly when a completely valid UTF-8 suffix
    has some eligible standard terminal, without requiring a caller-supplied kind. -/
theorem next_terminal_selects_iff (bytes : alloc.vec.Vec U8) (position : Usize) :
    (∃ token, next_terminal bytes position = .ok (.Token token)) ↔
      (∃ word, Rowl.Regular.Utf8From bytes.val position.val word) ∧
        ∃ terminal endpoint, Candidate bytes.val position.val terminal endpoint := by
  obtain ⟨result, executed, correct⟩ := next_terminal_total_correct bytes position
  constructor
  · rintro ⟨token, selected⟩
    have equal := Result.ok_injective (executed.symm.trans selected)
    subst result
    exact ⟨correct.1, token.terminal, token.end.val, correct.2.2.1⟩
  · rintro ⟨⟨word, utf8⟩, terminal, endpoint, candidate⟩
    cases result with
    | Token token => exact ⟨token, executed⟩
    | NoMatch => exact False.elim (correct.2 terminal endpoint candidate)
    | MalformedUtf8 error => exact False.elim (Rowl.Regular.failure_excludes_utf8 _ _ _ correct word utf8)

private theorem span_bound {bs : List U8} {start finish : Nat} {word : List Nat}
    (span : Rowl.Longest.Utf8Span bs start finish word) : start ≤ finish ∧ finish ≤ bs.length := by
  induction span with
  | empty bound => exact ⟨le_rfl, bound⟩
  | character _ positive _ _ ih => constructor <;> omega
/-- Every selected terminal strictly advances through a bounded source segment. -/
theorem next_terminal_advances (bytes : alloc.vec.Vec U8) (position : Usize) (token : Token)
    (selected : next_terminal bytes position = .ok (.Token token)) :
    token.start.val = position.val ∧ position.val < token.end.val ∧ token.end.val ≤ bytes.val.length := by
  obtain ⟨result, executed, correct⟩ := next_terminal_total_correct bytes position
  have equal := Result.ok_injective (executed.symm.trans selected)
  subst result
  have atStart := correct.2.1
  obtain ⟨word, span, accepted⟩ := correct.2.2.1
  have nonempty : word ≠ [] := by
    intro equal
    exact Rowl.Functional.grammar_nonempty token.terminal (by simpa [equal] using accepted)
  have strict : ∀ {start finish : Nat} {word : List Nat}, Rowl.Longest.Utf8Span bytes.val start finish word →
      word ≠ [] → start < finish := by
    intro start finish word span notEmpty
    cases span with
    | empty _ => contradiction
    | character _ positive _ tail => have bound := span_bound tail; omega
  exact ⟨atStart, strict span nonempty, (span_bound span).2⟩

/-- Mathematical endpoint maximality and earliest eligible inventory membership
    determine one complete source token, including its kind and both offsets. -/
theorem selected_token_unique (bytes : List U8) (position : Nat) (one two : Token)
    (first : Correct bytes position (.Token one)) (second : Correct bytes position (.Token two)) : one = two := by
  have endValue : one.end.val = two.end.val := Nat.le_antisymm
    (second.2.2.2.1 one.terminal one.end.val first.2.2.1)
    (first.2.2.2.1 two.terminal two.end.val second.2.2.1)
  have endEqual : one.end = two.end := UScalar.eq_of_val_eq endValue
  have startEqual : one.start = two.start := UScalar.eq_of_val_eq (first.2.1.trans second.2.1.symm)
  have firstKind := first.2.2.2.2
  have secondKind := second.2.2.2.2
  unfold FirstCandidate at firstKind secondKind
  rw [endEqual] at firstKind
  have kindEqual : one.terminal = two.terminal := Option.some.inj (firstKind.symm.trans secondKind)
  cases one
  cases two
  congr

/-- The actual selector returns precisely the uniquely specified greatest token,
    with the documented deterministic inventory priority at equal endpoints. -/
theorem next_terminal_token_iff (bytes : alloc.vec.Vec U8) (position : Usize) (token : Token) :
    next_terminal bytes position = .ok (.Token token) ↔ Correct bytes.val position.val (.Token token) := by
  obtain ⟨result,executed,correct⟩ := next_terminal_total_correct bytes position
  constructor
  · intro selected
    have equal := Result.ok_injective (executed.symm.trans selected)
    simpa [equal] using correct
  · intro specified
    cases result with
    | NoMatch => exact False.elim (correct.2 token.terminal token.end.val specified.2.2.1)
    | MalformedUtf8 error =>
      obtain ⟨word,valid⟩ := specified.1
      exact False.elim (Rowl.Regular.failure_excludes_utf8 _ _ _ correct word valid)
    | Token actual =>
      have equal := selected_token_unique bytes.val position.val actual token correct specified
      simpa [equal] using executed
end Rowl.FunctionalSelection
