import Rowl.Collection
import Rowl.Symbols
import Rowl.Typing
import Rowl.Builtins
namespace Rowl.Indexing
open Aeneas Aeneas.Std RowlRust.indexing RowlRust.collection RowlRust.model RowlRust.typing RowlRust.symbols
open Rowl.Symbols

/-- Every occurrence retains its exact spelling, role and position. -/
def Encoded (table : SymbolTable) : List Rowl.Collection.Row → Occurrences → Prop
  | [], .Empty => True
  | (iri, kind) :: rest, .Entry symbol indexedKind next =>
      indexedKind = kind ∧ table.keys.val[symbol.val]? = some iri.spelling ∧ Encoded table rest next
  | _, _ => False

def Extends (before after : SymbolTable) : Prop :=
  after.limit = before.limit ∧ ∃ suffix, after.keys.val = before.keys.val ++ suffix

def AtCapacity (table : SymbolTable) (iri : Iri) : Prop :=
  table.keys.val.length = table.limit.val ∧ iri.spelling.val ∉ byteKeys table

private theorem extends_refl (table : SymbolTable) : Extends table table := ⟨rfl, [], by simp⟩
private theorem extends_trans {a b c : SymbolTable} (ab : Extends a b) (bc : Extends b c) : Extends a c := by
  obtain ⟨hab, xs, hxs⟩ := ab
  obtain ⟨hbc, ys, hys⟩ := bc
  exact ⟨hbc.trans hab, xs ++ ys, by rw [hys, hxs, List.append_assoc]⟩
private theorem get_preserved {before after : SymbolTable} (extension : Extends before after)
    (symbol : U32) (key : alloc.vec.Vec U8) (found : before.keys.val[symbol.val]? = some key) :
    after.keys.val[symbol.val]? = some key := by
  obtain ⟨_, suffix, equality⟩ := extension
  have bound : symbol.val < before.keys.val.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at found
    contradiction
  rw [equality, List.getElem?_append_left bound]
  exact found
private theorem encoded_preserved {before after : SymbolTable} (extension : Extends before after)
    (source : List Rowl.Collection.Row) (indexed : Occurrences) (encoded : Encoded before source indexed) :
    Encoded after source indexed := by
  induction source generalizing indexed with
  | nil => cases indexed <;> simp_all [Encoded]
  | cons row rest ih =>
    cases row with | mk iri kind =>
      cases indexed with
      | Empty => simp [Encoded] at encoded
      | Entry symbol role next =>
        exact ⟨encoded.1, get_preserved extension symbol iri.spelling encoded.2.1, ih next encoded.2.2⟩
private theorem intern_extends (before : SymbolTable) (key : alloc.vec.Vec U8)
    (outcome : InternResult) (after : SymbolTable) (correct : InternCorrect before key outcome after) : Extends before after := by
  cases outcome with
  | Existing s => rw [correct.1]; exact extends_refl before
  | CapacityExceeded => rw [correct.1]; exact extends_refl before
  | Inserted s => exact ⟨correct.2.2.2.1, [key], correct.2.2.2.2⟩
private theorem existing_key (before : SymbolTable) (key : alloc.vec.Vec U8) (symbol : U32)
    (found : firstIndex before key = some symbol.val) : before.keys.val[symbol.val]? = some key := by
  obtain ⟨bound, equal, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
  have value : before.keys.val[symbol.val].val = key.val := by simpa using equal
  have vec : before.keys.val[symbol.val] = key := alloc.vec.Vec.ext _ _ value
  rw [List.getElem?_eq_getElem bound, vec]
private theorem inserted_key (before after : SymbolTable) (key : alloc.vec.Vec U8) (symbol : U32)
    (correct : InternCorrect before key (.Inserted symbol) after) : after.keys.val[symbol.val]? = some key := by
  rw [correct.2.2.2.2, correct.2.1]
  simp
private theorem no_key {table : SymbolTable} {key : alloc.vec.Vec U8}
    (absent : firstIndex table key = none) : key.val ∉ byteKeys table := by
  have all := List.findIdx?_eq_none_iff.mp absent
  simp only [byteKeys, List.mem_map]
  rintro ⟨stored, mem, equal⟩
  have := all stored mem
  simp [equal] at this
private def UsesCorrect (source : EntityUses) (table : SymbolTable) : Indexed → Prop
  | .Complete indexed => Encoded table (Rowl.Collection.rows source) indexed
  | .CapacityExceeded iri => AtCapacity table iri ∧ ∃ kind, (iri, kind) ∈ Rowl.Collection.rows source
private theorem index_uses_correct (source : EntityUses) (before : SymbolTable) (valid : WellFormed before) :
    ∃ outcome after, index_uses source before = .ok (outcome, after) ∧
      WellFormed after ∧ Extends before after ∧ UsesCorrect source after outcome := by
  induction source generalizing before with
  | Empty => exact ⟨.Complete .Empty, before, by simp [index_uses], valid, extends_refl _, trivial⟩
  | Entry iri kind next ih =>
    obtain ⟨result, middle, execute, correct, validMiddle⟩ := intern_total_correct before iri.spelling valid
    have extension := intern_extends before iri.spelling result middle correct
    cases result with
    | CapacityExceeded =>
      have atCapacity : AtCapacity middle iri := by
        rw [correct.1]
        exact ⟨correct.2.2, no_key correct.2.1⟩
      exact ⟨.CapacityExceeded iri, middle, by simp [index_uses, execute], validMiddle, extension,
        atCapacity, kind, by simp [Rowl.Collection.rows]⟩
    | Existing symbol =>
      have found : middle.keys.val[symbol.val]? = some iri.spelling := by
        rw [correct.1]
        exact existing_key before iri.spelling symbol correct.2
      obtain ⟨outcome, after, hr, va, ex, meaning⟩ := ih middle validMiddle
      cases outcome with
      | Complete indexed =>
        exact ⟨.Complete (.Entry symbol kind indexed), after, by simp [index_uses, execute, hr], va,
          extends_trans extension ex, rfl, get_preserved ex symbol iri.spelling found, meaning⟩
      | CapacityExceeded failed =>
        exact ⟨.CapacityExceeded failed, after, by simp [index_uses, execute, hr], va,
          extends_trans extension ex, meaning.1, by
            obtain ⟨role, mem⟩ := meaning.2
            exact ⟨role, List.mem_cons_of_mem _ mem⟩⟩
    | Inserted symbol =>
      have found := inserted_key before middle iri.spelling symbol correct
      obtain ⟨outcome, after, hr, va, ex, meaning⟩ := ih middle validMiddle
      cases outcome with
      | Complete indexed =>
        exact ⟨.Complete (.Entry symbol kind indexed), after, by simp [index_uses, execute, hr], va,
          extends_trans extension ex, rfl, get_preserved ex symbol iri.spelling found, meaning⟩
      | CapacityExceeded failed =>
        exact ⟨.CapacityExceeded failed, after, by simp [index_uses, execute, hr], va,
          extends_trans extension ex, meaning.1, by
            obtain ⟨role, mem⟩ := meaning.2
            exact ⟨role, List.mem_cons_of_mem _ mem⟩⟩

def EntitiesCorrect (entities : CollectedEntities) (limit : U32) : IndexResult → Prop
  | .Complete table declarations uses => WellFormed table ∧ table.limit = limit ∧
      Encoded table (Rowl.Collection.rows entities.declarations) declarations ∧ Encoded table (Rowl.Collection.rows entities.uses) uses
  | .CapacityExceeded table iri => WellFormed table ∧ table.limit = limit ∧ AtCapacity table iri ∧
      ∃ kind, (iri, kind) ∈ Rowl.Collection.rows entities.declarations ++ Rowl.Collection.rows entities.uses

theorem index_entities_total_correct (entities : CollectedEntities) (limit : U32) :
    ∃ result, index_entities entities limit = .ok result ∧ EntitiesCorrect entities limit result := by
  obtain ⟨initial, he, vi, _, li⟩ := empty_total_correct limit
  obtain ⟨declared, middle, hd, vm, em, md⟩ := index_uses_correct entities.declarations initial vi
  cases declared with
  | CapacityExceeded iri =>
    refine ⟨.CapacityExceeded middle iri, by simp [index_entities, he, hd], vm, em.1.trans li, md.1, ?_⟩
    obtain ⟨kind, mem⟩ := md.2
    exact ⟨kind, List.mem_append_left _ mem⟩
  | Complete declarations =>
    obtain ⟨used, finalTable, hu, vf, ef, mu⟩ := index_uses_correct entities.uses middle vm
    cases used with
    | CapacityExceeded iri =>
      refine ⟨.CapacityExceeded finalTable iri, by simp [index_entities, he, hd, hu], vf,
        ef.1.trans (em.1.trans li), mu.1, ?_⟩
      obtain ⟨kind, mem⟩ := mu.2
      exact ⟨kind, List.mem_append_right _ mem⟩
    | Complete uses =>
      exact ⟨.Complete finalTable declarations uses, by simp [index_entities, he, hd, hu], vf,
        ef.1.trans (em.1.trans li), encoded_preserved ef _ _ md, mu⟩

def OntologyCorrect (ontology : RawOntology) (limit : U32) : IndexResult → Prop
  | .Complete table declarations uses => WellFormed table ∧ table.limit = limit ∧
      Encoded table (ontology.axioms.val.flatMap Rowl.Collection.declarationUses) declarations ∧
      Encoded table (ontology.axioms.val.flatMap Rowl.Collection.annotatedUses) uses
  | .CapacityExceeded table iri => WellFormed table ∧ table.limit = limit ∧ AtCapacity table iri ∧
      ∃ kind, (iri, kind) ∈ ontology.axioms.val.flatMap Rowl.Collection.declarationUses ++
        ontology.axioms.val.flatMap Rowl.Collection.annotatedUses

theorem index_ontology_total_correct (ontology : RawOntology) (limit : U32) :
    ∃ result, index_ontology ontology limit = .ok result ∧ OntologyCorrect ontology limit result := by
  obtain ⟨collected, hc, collectedCorrect⟩ := Rowl.Collection.axiom_closure_entities_total_correct ontology
  obtain ⟨result, hr, correct⟩ := index_entities_total_correct collected limit
  refine ⟨result, by simp [index_ontology, hc, hr], ?_⟩
  cases result <;> simp_all [OntologyCorrect, EntitiesCorrect, Rowl.Collection.AxiomClosureCorrect]

/-- Relevant virtual declarations use the mathematical finite vocabulary. -/
def implicitRows (table : SymbolTable) (uses : Occurrences) : List (U32 × EntityKind) :=
  (Rowl.Typing.occurrences uses).filterMap (fun entry =>
    (table.keys.val[entry.1.val]?).bind (fun key => (Rowl.Builtins.role key.val).map (fun role => (entry.1, role))))

/-- Existing explicit declarations remain after all relevant implicit ones. -/
theorem add_builtin_declarations_total_correct (table : SymbolTable) (uses declarations : Occurrences) :
    ∃ augmented, add_builtin_declarations table uses declarations = .ok augmented ∧
      Rowl.Typing.occurrences augmented = implicitRows table uses ++ Rowl.Typing.occurrences declarations := by
  induction uses generalizing declarations with
  | Empty => exact ⟨declarations, by simp [add_builtin_declarations], by simp [implicitRows, Rowl.Typing.occurrences]⟩
  | Entry symbol kind next ih =>
    obtain ⟨tail, ht, content⟩ := ih declarations
    rw [add_builtin_declarations, ht, key_of_total_correct]
    cases found : table.keys.val[symbol.val]? with
    | none => exact ⟨tail, by simp, by simpa [implicitRows, Rowl.Typing.occurrences, found] using content⟩
    | some key =>
      simp only [bind_ok]
      rw [Rowl.Builtins.builtin_kind_total_correct]
      cases role : Rowl.Builtins.role key.val with
      | none => exact ⟨tail, by simp, by simpa [implicitRows, Rowl.Typing.occurrences, found, role] using content⟩
      | some builtinRole =>
        exact ⟨.Entry symbol builtinRole tail, by simp, by simp [implicitRows, Rowl.Typing.occurrences, found, role, content]⟩

def TypingCorrect (ontology : RawOntology) (limit : U32) : IndexedTyping → Prop
  | .Checked table declarations uses result => ∃ explicit,
      OntologyCorrect ontology limit (.Complete table explicit uses) ∧
      Rowl.Typing.occurrences declarations = implicitRows table uses ++ Rowl.Typing.occurrences explicit ∧
      Rowl.Typing.Correct declarations uses result
  | .CapacityExceeded table iri => OntologyCorrect ontology limit (.CapacityExceeded table iri)

theorem check_ontology_typing_total_correct (ontology : RawOntology) (limit : U32) :
    ∃ result, check_ontology_typing ontology limit = .ok result ∧ TypingCorrect ontology limit result := by
  obtain ⟨indexed, hi, correct⟩ := index_ontology_total_correct ontology limit
  cases indexed with
  | CapacityExceeded table iri => exact ⟨.CapacityExceeded table iri, by simp [check_ontology_typing, hi], correct⟩
  | Complete table declarations uses =>
    obtain ⟨augmented, ha, content⟩ := add_builtin_declarations_total_correct table uses declarations
    obtain ⟨result, ht, meaning⟩ := Rowl.Typing.validate_typing_total_correct augmented uses
    exact ⟨.Checked table augmented uses result, by simp [check_ontology_typing, hi, ha, ht], declarations, correct, content, meaning⟩
private theorem key_bound (table : SymbolTable) (symbol : U32) (key : alloc.vec.Vec U8)
    (found : table.keys.val[symbol.val]? = some key) : symbol.val < table.keys.val.length := by
  by_contra h
  rw [List.getElem?_eq_none (by omega)] at found
  contradiction

/-- Numeric identity is exactly byte spelling identity for indexed occurrences. -/
theorem indexed_identity_iff_spelling (table : SymbolTable) (valid : WellFormed table)
    (left right : U32) (leftKey rightKey : alloc.vec.Vec U8)
    (hl : table.keys.val[left.val]? = some leftKey) (hr : table.keys.val[right.val]? = some rightKey) :
    left = right ↔ leftKey.val = rightKey.val := by
  constructor
  · intro same
    subst right
    have keys := Option.some.inj (hl.symm.trans hr)
    rw [keys]
  · intro same
    have bl := key_bound table left leftKey hl
    have br := key_bound table right rightKey hr
    have vl : table.keys.val[left.val] = leftKey := by simpa [List.getElem?_eq_getElem bl] using hl
    have vr : table.keys.val[right.val] = rightKey := by simpa [List.getElem?_eq_getElem br] using hr
    have nd : table.keys.val.Nodup := List.Nodup.of_map alloc.vec.Vec.val valid.1
    have elements : table.keys.val[left.val] = table.keys.val[right.val] := by
      rw [vl, vr]
      exact alloc.vec.Vec.ext _ _ same
    exact UScalar.eq_of_val_eq (nd.getElem_inj_iff.mp elements)

private theorem source_for_symbol (table : SymbolTable) (source : List Rowl.Collection.Row)
    (indexed : Occurrences) (encoded : Encoded table source indexed) (symbol : U32) (kind : EntityKind)
    (mem : (symbol, kind) ∈ Rowl.Typing.occurrences indexed) :
    ∃ iri, (iri, kind) ∈ source ∧ table.keys.val[symbol.val]? = some iri.spelling := by
  induction source generalizing indexed with
  | nil => cases indexed <;> simp_all [Encoded, Rowl.Typing.occurrences]
  | cons row rest ih =>
    obtain ⟨iri, role⟩ := row
    cases indexed with
    | Empty => simp [Encoded] at encoded
    | Entry here hereKind next =>
      rcases List.mem_cons.mp mem with equal | mem
      · cases equal
        exact ⟨iri, by simp [encoded.1], encoded.2.1⟩
      · obtain ⟨original, found, key⟩ := ih next encoded.2.2 mem
        exact ⟨original, List.mem_cons_of_mem _ found, key⟩

private theorem symbol_for_source (table : SymbolTable) (source : List Rowl.Collection.Row)
    (indexed : Occurrences) (encoded : Encoded table source indexed) (iri : Iri) (kind : EntityKind)
    (mem : (iri, kind) ∈ source) :
    ∃ symbol, (symbol, kind) ∈ Rowl.Typing.occurrences indexed ∧ table.keys.val[symbol.val]? = some iri.spelling := by
  induction source generalizing indexed with
  | nil => simp at mem
  | cons row rest ih =>
    obtain ⟨original, role⟩ := row
    cases indexed with
    | Empty => simp [Encoded] at encoded
    | Entry here hereKind next =>
      rcases List.mem_cons.mp mem with equal | mem
      · cases equal
        exact ⟨here, by simp [Rowl.Typing.occurrences, encoded.1], encoded.2.1⟩
      · obtain ⟨symbol, found, key⟩ := ih next encoded.2.2 mem
        exact ⟨symbol, List.mem_cons_of_mem _ found, key⟩

/-- Declaration constraints independently expressed on original IRI spellings. -/
def RowsWellTyped (declarations uses : List Rowl.Collection.Row) : Prop :=
  (∀ iri role other otherRole, (iri, role) ∈ declarations → (other, otherRole) ∈ declarations →
    iri.spelling.val = other.spelling.val → ¬ Rowl.Typing.Forbidden role otherRole) ∧
  (∀ iri kind, (iri, kind) ∈ uses → kind ≠ .NamedIndividual →
    ∃ declared, (declared, kind) ∈ declarations ∧ declared.spelling.val = iri.spelling.val)

/-- The symbolic validator's predicate is equivalent to constraints on raw IRIs. -/
theorem typing_iff_original_spelling (table : SymbolTable) (valid : WellFormed table)
    (declarations uses : List Rowl.Collection.Row) (indexedDeclarations indexedUses : Occurrences)
    (ed : Encoded table declarations indexedDeclarations) (eu : Encoded table uses indexedUses) :
    Rowl.Typing.WellTyped indexedDeclarations indexedUses ↔ RowsWellTyped declarations uses := by
  constructor
  · intro well
    constructor
    · intro iri role other otherRole hi ho same forbidden
      obtain ⟨left, dl, kl⟩ := symbol_for_source table declarations indexedDeclarations ed iri role hi
      obtain ⟨right, dr, kr⟩ := symbol_for_source table declarations indexedDeclarations ed other otherRole ho
      have identities := (indexed_identity_iff_spelling table valid left right _ _ kl kr).mpr same
      subst right
      exact well.1 left ⟨role, otherRole, dl, dr, forbidden⟩
    · intro iri kind hi hn
      obtain ⟨symbol, used, key⟩ := symbol_for_source table uses indexedUses eu iri kind hi
      obtain ⟨declared, hd, kd⟩ := source_for_symbol table declarations indexedDeclarations ed symbol kind (well.2 symbol kind used hn)
      exact ⟨declared, hd, (indexed_identity_iff_spelling table valid symbol symbol _ _ kd key).mp rfl⟩
  · intro well
    constructor
    · intro symbol ⟨leftRole, rightRole, hl, hr, forbidden⟩
      obtain ⟨left, dl, kl⟩ := source_for_symbol table declarations indexedDeclarations ed symbol leftRole hl
      obtain ⟨right, dr, kr⟩ := source_for_symbol table declarations indexedDeclarations ed symbol rightRole hr
      have same := (indexed_identity_iff_spelling table valid symbol symbol _ _ kl kr).mp rfl
      exact well.1 left leftRole right rightRole dl dr same forbidden
    · intro symbol kind used hn
      obtain ⟨iri, hi, ki⟩ := source_for_symbol table uses indexedUses eu symbol kind used
      obtain ⟨declared, hd, same⟩ := well.2 iri kind hi hn
      obtain ⟨other, dm, kd⟩ := symbol_for_source table declarations indexedDeclarations ed declared kind hd
      have identities := (indexed_identity_iff_spelling table valid other symbol _ _ kd ki).mpr same
      simpa [identities] using dm

/-- Virtual declarations use the original occurrence's IRI and normative role. -/
def implicitSource (source : List Rowl.Collection.Row) : List Rowl.Collection.Row :=
  source.filterMap (fun entry => (Rowl.Builtins.role entry.1.spelling.val).map (fun kind => (entry.1, kind)))

def ontologyUses (ontology : RawOntology) : List Rowl.Collection.Row :=
  ontology.axioms.val.flatMap Rowl.Collection.annotatedUses

def ontologyDeclarations (ontology : RawOntology) : List Rowl.Collection.Row :=
  ontology.axioms.val.flatMap Rowl.Collection.declarationUses

def RawWellTyped (ontology : RawOntology) : Prop :=
  RowsWellTyped (implicitSource (ontologyUses ontology) ++ ontologyDeclarations ontology) (ontologyUses ontology)

private theorem augmented_encodes (table : SymbolTable) (source : List Rowl.Collection.Row)
    (uses declarations : Occurrences) (declaredSource : List Rowl.Collection.Row)
    (encoded : Encoded table source uses) (ed : Encoded table declaredSource declarations) :
    ∃ augmented, add_builtin_declarations table uses declarations = .ok augmented ∧
      Encoded table (implicitSource source ++ declaredSource) augmented := by
  induction source generalizing uses with
  | nil =>
    cases uses with
    | Empty => exact ⟨declarations, by simp [add_builtin_declarations], by simpa [implicitSource] using ed⟩
    | Entry _ _ _ => simp [Encoded] at encoded
  | cons row rest ih =>
    obtain ⟨iri, kind⟩ := row
    cases uses with
    | Empty => simp [Encoded] at encoded
    | Entry symbol indexedKind next =>
      obtain ⟨tail, ht, meaning⟩ := ih next encoded.2.2
      have hk : key_of table symbol = .ok (some iri.spelling) := by
        rw [key_of_total_correct, encoded.2.1]
      rw [add_builtin_declarations, ht, hk]
      simp only [bind_ok]
      rw [Rowl.Builtins.builtin_kind_total_correct]
      cases role : Rowl.Builtins.role iri.spelling.val with
      | none => exact ⟨tail, by simp, by simpa [implicitSource, role] using meaning⟩
      | some builtinRole =>
        refine ⟨.Entry symbol builtinRole tail, by simp, ?_⟩
        simp only [implicitSource, List.filterMap_cons, role, Option.map_some, List.cons_append, Encoded]
        exact ⟨trivial, encoded.2.1, meaning⟩

/-- End-to-end declaration acceptance is exactly the predicate on original IRI
    spellings, including implicit built-ins, for every completed indexing run. -/
theorem check_ontology_typing_valid_iff_raw (ontology : RawOntology) (limit : U32)
    (table : SymbolTable) (declarations uses : Occurrences) (result : TypingResult)
    (executed : check_ontology_typing ontology limit = .ok (.Checked table declarations uses result)) :
    result = .Valid ↔ RawWellTyped ontology := by
  obtain ⟨indexed, hi, correct⟩ := index_ontology_total_correct ontology limit
  cases indexed with
  | CapacityExceeded table iri =>
    simp [check_ontology_typing, hi] at executed
  | Complete originalTable explicit actualUses =>
    obtain ⟨valid, _, ed, eu⟩ := correct
    obtain ⟨augmented, ha, augmentedMeaning⟩ := augmented_encodes originalTable (ontologyUses ontology) actualUses explicit
      (ontologyDeclarations ontology) eu ed
    obtain ⟨actualResult, ht, meaning⟩ := Rowl.Typing.validate_typing_total_correct augmented actualUses
    have actual : check_ontology_typing ontology limit = .ok (.Checked originalTable augmented actualUses actualResult) := by
      simp [check_ontology_typing, hi, ha, ht]
    have outputs := Result.ok_injective (actual.symm.trans executed)
    cases outputs
    have verdict : result = .Valid ↔ Rowl.Typing.WellTyped declarations uses := by
      constructor
      · intro isValid
        subst result
        exact Rowl.Typing.validate_typing_valid_iff declarations uses |>.mp ht
      · intro well
        exact Result.ok_injective (ht.symm.trans ((Rowl.Typing.validate_typing_valid_iff declarations uses).mpr well))
    exact verdict.trans (typing_iff_original_spelling table valid _ _ declarations uses augmentedMeaning eu)

end Rowl.Indexing
