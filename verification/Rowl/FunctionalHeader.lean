import Rowl.FunctionalHeaderImport

namespace Rowl.FunctionalHeader
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional_header RowlRust.functional_lexer RowlRust.functional
open Rowl.FunctionalHeaderIdentity Rowl.FunctionalHeaderImport
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- Independent maximal leading-import grammar and diagnostic/count priority.
    Original reference records append in order, preserving repetitions. -/
inductive ScanRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (countLimit valueLimit : Nat) :
    Tokens → List ImportReference → core.result.Result HeaderImports HeaderError → Prop
  | empty (prior : List ImportReference) (records : alloc.vec.Vec ImportReference) (contents : records.val = prior) :
      ScanRun rows source eof countLimit valueLimit .Empty prior (.Ok ⟨records,.Empty⟩)
  | stop (token : Token) (tail : Tokens) (prior : List ImportReference)
      (notImport : token.terminal ≠ .Keyword .Import) (records : alloc.vec.Vec ImportReference) (contents : records.val = prior) :
      ScanRun rows source eof countLimit valueLimit (.Cons token tail) prior (.Ok ⟨records,.Cons token tail⟩)
  | count (token : Token) (tail : Tokens) (prior : List ImportReference)
      (importKind : token.terminal = .Keyword .Import) (full : countLimit ≤ prior.length) :
      ScanRun rows source eof countLimit valueLimit (.Cons token tail) prior (.Err (.ImportLimit token.start))
  | bodyError {token : Token} {tail : Tokens} {prior : List ImportReference} {error : HeaderError}
      (importKind : token.terminal = .Keyword .Import) (room : prior.length < countLimit)
      (body : BodyRun rows source eof valueLimit tail (.Err error)) :
      ScanRun rows source eof countLimit valueLimit (.Cons token tail) prior (.Err error)
  | reference {token : Token} {tail rest : Tokens} {prior : List ImportReference} {target : HeaderIri}
      {result : core.result.Result HeaderImports HeaderError}
      (importKind : token.terminal = .Keyword .Import) (room : prior.length < countLimit)
      (body : BodyRun rows source eof valueLimit tail (.Ok (target,rest)))
      (later : ScanRun rows source eof countLimit valueLimit rest (prior++[⟨token,target⟩]) result) :
      ScanRun rows source eof countLimit valueLimit (.Cons token tail) prior result

private theorem stop_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (token : Token) (tail : Tokens)
    (prior : alloc.vec.Vec ImportReference) (countLimit valueLimit : Usize) (notImport : token.terminal ≠ .Keyword .Import) :
    scan_imports table bytes (.Cons token tail) prior countLimit valueLimit = .ok (.Ok ⟨prior,.Cons token tail⟩) := by
  rw [scan_imports]
  cases token with
  | mk terminal start finish =>
    cases terminal <;> first | rfl | rename_i keyword; cases keyword <;> simp_all

theorem scan_imports_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (prior : alloc.vec.Vec ImportReference) (countLimit valueLimit : Usize) :
    ∃ result, scan_imports table bytes tokens prior countLimit valueLimit = .ok result ∧
      ScanRun table.declarations.val bytes.val bytes.len countLimit.val valueLimit.val tokens prior.val result := by
  cases tokens with
  | Empty => exact ⟨.Ok ⟨prior,.Empty⟩,by rw [scan_imports],.empty _ _ rfl⟩
  | Cons token tail =>
    by_cases kind : token.terminal = .Keyword .Import
    · rw [scan_imports,kind]
      by_cases full : countLimit.val ≤ prior.val.length
      · exact ⟨.Err (.ImportLimit token.start),by simp [alloc.vec.Vec.len_val,UScalar.le_equiv,full],.count _ _ _ kind full⟩
      · have room : prior.val.length < countLimit.val := by omega
        simp only [alloc.vec.Vec.len_val,UScalar.le_equiv,full,↓reduceIte]
        obtain ⟨body,bodyRead,bodyCorrect⟩ := read_import_total_correct table bytes tail valueLimit
        rw [bodyRead,bind_ok]
        cases body with
        | Err error => exact ⟨.Err error,rfl,.bodyError kind room bodyCorrect⟩
        | Ok pair =>
          obtain ⟨target,rest⟩ := pair
          simp only [uncurry_apply_pair]
          obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec prior (⟨token,target⟩ : ImportReference) (by scalar_tac))
          obtain ⟨result,executed,correct⟩ := scan_imports_total_correct table bytes rest appended countLimit valueLimit
          refine ⟨result,by rw [push,bind_ok]; exact executed,.reference kind room bodyCorrect ?_⟩
          simpa [contents] using correct
    · exact ⟨.Ok ⟨prior,.Cons token tail⟩,stop_execution table bytes token tail prior countLimit valueLimit kind,.stop _ _ _ kind _ rfl⟩
termination_by Rowl.FunctionalLexer.TokenCount tokens
decreasing_by
  have progress := import_token_progress bodyCorrect
  simp only [Rowl.FunctionalLexer.TokenCount]
  omega

private theorem scan_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (countLimit valueLimit : Usize)
    {tokens : Tokens} {prior : List ImportReference} {result : core.result.Result HeaderImports HeaderError}
    (run : ScanRun table.declarations.val bytes.val bytes.len countLimit.val valueLimit.val tokens prior result) :
    ∀ records : alloc.vec.Vec ImportReference, records.val = prior → scan_imports table bytes tokens records countLimit valueLimit = .ok result := by
  induction run with
  | empty prior expected contents =>
    intro records same
    have equal : records = expected := (alloc.vec.Vec.eq_iff _ _).mpr (same.trans contents.symm)
    simp [scan_imports,equal]
  | stop token tail prior kind expected contents =>
    intro records same
    have equal : records = expected := (alloc.vec.Vec.eq_iff _ _).mpr (same.trans contents.symm)
    simpa [equal] using stop_execution table bytes token tail records countLimit valueLimit kind
  | count token tail prior kind full =>
    intro records same
    rw [scan_imports,kind]
    simp [alloc.vec.Vec.len_val,UScalar.le_equiv,same,full]
  | @bodyError token tail prior error kind room body =>
    intro records same
    have read := (read_import_result_iff table bytes tail valueLimit (.Err error)).mpr body
    rw [scan_imports,kind]
    simp [alloc.vec.Vec.len_val,UScalar.le_equiv,same,show ¬ countLimit.val ≤ prior.length from by omega,read]
  | @reference token tail rest prior target result kind room body later ih =>
    intro records same
    have read := (read_import_result_iff table bytes tail valueLimit (.Ok (target,rest))).mpr body
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec records (⟨token,target⟩ : ImportReference) (by scalar_tac))
    have next := ih appended (by simpa [same] using contents)
    rw [scan_imports,kind]
    simp [alloc.vec.Vec.len_val,UScalar.le_equiv,same,show ¬ countLimit.val ≤ prior.length from by omega,read,push,next]

theorem scan_imports_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (prior : alloc.vec.Vec ImportReference) (countLimit valueLimit : Usize) (result : core.result.Result HeaderImports HeaderError) :
    scan_imports table bytes tokens prior countLimit valueLimit = .ok result ↔
      ScanRun table.declarations.val bytes.val bytes.len countLimit.val valueLimit.val tokens prior.val result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := scan_imports_total_correct table bytes tokens prior countLimit valueLimit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    exact scan_execution table bytes countLimit valueLimit source prior rfl

/-- Independent complete identity-then-import result and its first-error phases. -/
inductive TailRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (countLimit valueLimit : Nat) :
    Tokens → core.result.Result HeaderTail HeaderError → Prop
  | identityError {tokens : Tokens} {error : HeaderError}
      (identity : IdentityRun rows source valueLimit tokens (.Err error)) :
      TailRun rows source eof countLimit valueLimit tokens (.Err error)
  | importsError {tokens middle : Tokens} {identity : SourceOntologyIdentity} {error : HeaderError}
      (names : IdentityRun rows source valueLimit tokens (.Ok (identity,middle)))
      (imports : ScanRun rows source eof countLimit valueLimit middle [] (.Err error)) :
      TailRun rows source eof countLimit valueLimit tokens (.Err error)
  | ready {tokens middle : Tokens} {identity : SourceOntologyIdentity} {imports : HeaderImports}
      (names : IdentityRun rows source valueLimit tokens (.Ok (identity,middle)))
      (references : ScanRun rows source eof countLimit valueLimit middle [] (.Ok imports)) :
      TailRun rows source eof countLimit valueLimit tokens (.Ok ⟨identity,imports.references,imports.remaining⟩)

theorem read_header_tail_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (countLimit valueLimit : Usize) :
    ∃ result, read_header_tail table bytes tokens countLimit valueLimit = .ok result ∧
      TailRun table.declarations.val bytes.val bytes.len countLimit.val valueLimit.val tokens result := by
  obtain ⟨identity,identityRead,identityCorrect⟩ := read_identity_total_correct table bytes tokens valueLimit
  rw [read_header_tail,identityRead,bind_ok]
  cases identity with
  | Err error => exact ⟨.Err error,rfl,.identityError identityCorrect⟩
  | Ok pair =>
    obtain ⟨identity,middle⟩ := pair
    simp only [uncurry_apply_pair]
    obtain ⟨imports,importsRead,importsCorrect⟩ := scan_imports_total_correct table bytes middle (alloc.vec.Vec.new ImportReference) countLimit valueLimit
    rw [importsRead,bind_ok]
    cases imports with
    | Err error => exact ⟨.Err error,rfl,.importsError identityCorrect (by simpa using importsCorrect)⟩
    | Ok imports => exact ⟨.Ok ⟨identity,imports.references,imports.remaining⟩,rfl,.ready identityCorrect (by simpa using importsCorrect)⟩

theorem read_header_tail_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (countLimit valueLimit : Usize) (result : core.result.Result HeaderTail HeaderError) :
    read_header_tail table bytes tokens countLimit valueLimit = .ok result ↔
      TailRun table.declarations.val bytes.val bytes.len countLimit.val valueLimit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_header_tail_total_correct table bytes tokens countLimit valueLimit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | identityError identity =>
      have read := (read_identity_result_iff table bytes _ valueLimit _).mpr identity
      simp [read_header_tail,read]
    | importsError names imports =>
      have identityRead := (read_identity_result_iff table bytes _ valueLimit _).mpr names
      have importsRead := (scan_imports_result_iff table bytes _ (alloc.vec.Vec.new ImportReference) countLimit valueLimit _).mpr (by simpa using imports)
      simp [read_header_tail,identityRead,importsRead]
    | ready names imports =>
      have identityRead := (read_identity_result_iff table bytes _ valueLimit _).mpr names
      have importsRead := (scan_imports_result_iff table bytes _ (alloc.vec.Vec.new ImportReference) countLimit valueLimit _).mpr (by simpa using imports)
      simp [read_header_tail,identityRead,importsRead]

/-- Source import records consume the maximal leading Import sequence, stopping
    with the original empty or non-Import suffix unchanged. -/
inductive ImportSection (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (valueLimit : Nat) :
    Tokens → List ImportReference → Tokens → Prop
  | empty : ImportSection rows source eof valueLimit .Empty [] .Empty
  | stop {token : Token} {tail : Tokens} (notImport : token.terminal ≠ .Keyword .Import) :
      ImportSection rows source eof valueLimit (.Cons token tail) [] (.Cons token tail)
  | reference {token : Token} {tail rest remaining : Tokens} {target : HeaderIri} {references : List ImportReference}
      (importKind : token.terminal = .Keyword .Import)
      (body : BodyRun rows source eof valueLimit tail (.Ok (target,rest)))
      (later : ImportSection rows source eof valueLimit rest references remaining) :
      ImportSection rows source eof valueLimit (.Cons token tail) (⟨token,target⟩::references) remaining

private theorem scan_section {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {countLimit valueLimit : Nat}
    {tokens : Tokens} {prior : List ImportReference} {result : core.result.Result HeaderImports HeaderError}
    (run : ScanRun rows source eof countLimit valueLimit tokens prior result) : ∀ imports,
    result = .Ok imports → ∃ references, ImportSection rows source eof valueLimit tokens references imports.remaining ∧
      imports.references.val = prior++references := by
  induction run with
  | count | bodyError => intro imports impossible; cases impossible
  | reference kind room body later ih =>
    intro imports accepted
    obtain ⟨references,derivation,contents⟩ := ih imports accepted
    exact ⟨_::references,.reference kind body derivation,by simpa [List.append_assoc] using contents⟩
  | empty prior records contents => intro imports accepted; cases accepted; exact ⟨[],.empty,by simpa using contents⟩
  | stop token tail prior kind records contents => intro imports accepted; cases accepted; exact ⟨[],.stop kind,by simpa using contents⟩
private theorem scan_count {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {countLimit valueLimit : Nat}
    {tokens : Tokens} {prior : List ImportReference} {result : core.result.Result HeaderImports HeaderError}
    (run : ScanRun rows source eof countLimit valueLimit tokens prior result) : ∀ imports,
    result = .Ok imports → prior.length ≤ countLimit → imports.references.val.length ≤ countLimit := by
  induction run with
  | count | bodyError => intro imports impossible bound; cases impossible
  | reference kind room body later ih =>
    intro imports accepted bound
    apply ih imports accepted
    simp
    omega
  | empty prior records contents | stop _ _ prior _ records contents =>
    intro imports accepted bound; cases accepted; simpa [contents] using bound
private theorem section_values {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {valueLimit : Nat}
    {tokens remaining : Tokens} {references : List ImportReference}
    (derivation : ImportSection rows source eof valueLimit tokens references remaining) :
    ∀ reference ∈ references, reference.keyword.terminal = .Keyword .Import ∧ IriValue rows source valueLimit reference.target := by
  induction derivation with
  | empty | stop => simp
  | reference kind body later ih =>
    intro reference member
    rcases List.mem_cons.mp member with same | included
    · subst reference
      exact ⟨kind,(import_source_value body).2⟩
    · exact ih reference included

/-- Import reading is maximal: its preserved suffix is empty or begins with a
    terminal other than Import. Subsequent body validation is a separate stage. -/
theorem import_section_maximal {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {valueLimit : Nat}
    {tokens remaining : Tokens} {references : List ImportReference}
    (derivation : ImportSection rows source eof valueLimit tokens references remaining) :
    remaining = .Empty ∨ ∃ token tail, remaining = .Cons token tail ∧ token.terminal ≠ .Keyword .Import := by
  induction derivation with
  | empty => exact .inl rfl
  | stop kind => exact .inr ⟨_,_,rfl,kind⟩
  | reference _ _ _ ih => exact ih

theorem header_source_values (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (countLimit valueLimit : Usize) (header : HeaderTail)
    (accepted : read_header_tail table bytes tokens countLimit valueLimit = .ok (.Ok header)) :
    IdentityValues table.declarations.val bytes.val valueLimit.val header.identity ∧
    header.imports.val.length ≤ countLimit.val ∧
    (∀ reference ∈ header.imports.val, reference.keyword.terminal = .Keyword .Import ∧
      IriValue table.declarations.val bytes.val valueLimit.val reference.target) ∧
    ∃ middle, IdentityRun table.declarations.val bytes.val valueLimit.val tokens (.Ok (header.identity,middle)) ∧
      ImportSection table.declarations.val bytes.val bytes.len valueLimit.val middle header.imports.val header.remaining := by
  have source := (read_header_tail_result_iff table bytes tokens countLimit valueLimit (.Ok header)).mp accepted
  cases source with
  | @ready middle identity imports names references =>
    obtain ⟨rows,derivation,contents⟩ := scan_section references imports rfl
    have same : imports.references.val = rows := by simpa using contents
    rw [← same] at derivation
    exact ⟨identity_source_values names,scan_count references imports rfl (by simp),section_values derivation,middle,names,derivation⟩

end Rowl.FunctionalHeader
