import Rowl.FunctionalPrefixDeclaration

namespace Rowl.FunctionalPrefixes
open Aeneas Aeneas.Std Aeneas.Std.Result RowlFrontendRust
open RowlFrontendRust.functional_prefixes RowlFrontendRust.functional_lexer RowlFrontendRust.functional
open Rowl.FunctionalPrefixShape Rowl.FunctionalPrefixDeclaration
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- Independent maximal leading-prefix grammar and exact parser phase priority.
    Accepted rows append in source order; the Ontology keyword/opening and suffix
    are returned unchanged. This does not check ontology contents or table rules. -/
inductive Run (source : List U8) (eof : Usize) (countLimit valueLimit : Nat) :
    Tokens → List prefixes.Declaration → core.result.Result PrefixHeader PrefixSyntaxError → Prop
  | empty (prior : List prefixes.Declaration) :
      Run source eof countLimit valueLimit .Empty prior (.Err (.Expected .Ontology eof))
  | unexpected (token : Token) (tail : Tokens) (prior : List prefixes.Declaration)
      (notPrefix : token.terminal ≠ .Keyword .Prefix) (notOntology : token.terminal ≠ .Keyword .Ontology) :
      Run source eof countLimit valueLimit (.Cons token tail) prior (.Err (.Expected .Ontology token.start))
  | count (token : Token) (tail : Tokens) (prior : List prefixes.Declaration)
      (prefixKind : token.terminal = .Keyword .Prefix) (full : countLimit ≤ prior.length) :
      Run source eof countLimit valueLimit (.Cons token tail) prior (.Err (.DeclarationLimit token.start))
  | bodyError {token : Token} {tail : Tokens} {prior : List prefixes.Declaration} {error : PrefixSyntaxError}
      (prefixKind : token.terminal = .Keyword .Prefix) (room : prior.length < countLimit)
      (body : BodyRun source eof valueLimit tail (.Err error)) :
      Run source eof countLimit valueLimit (.Cons token tail) prior (.Err error)
  | declaration {token : Token} {tail rest : Tokens} {prior : List prefixes.Declaration}
      {declaration : prefixes.Declaration} {result : core.result.Result PrefixHeader PrefixSyntaxError}
      (prefixKind : token.terminal = .Keyword .Prefix) (room : prior.length < countLimit)
      (body : BodyRun source eof valueLimit tail (.Ok (declaration,rest)))
      (later : Run source eof countLimit valueLimit rest (prior++[declaration]) result) :
      Run source eof countLimit valueLimit (.Cons token tail) prior result
  | ontologyError {token : Token} {tail : Tokens} {prior : List prefixes.Declaration} {error : PrefixSyntaxError}
      (ontologyKind : token.terminal = .Keyword .Ontology) (failure : Mismatch [.Open] tail eof error) :
      Run source eof countLimit valueLimit (.Cons token tail) prior (.Err error)
  | ready {token opening : Token} {tail rest : Tokens} {prior : List prefixes.Declaration}
      (ontologyKind : token.terminal = .Keyword .Ontology) (openingKind : Taken tail .Open opening rest)
      (declarations : alloc.vec.Vec prefixes.Declaration) (contents : declarations.val = prior) :
      Run source eof countLimit valueLimit (.Cons token tail) prior (.Ok ⟨declarations,token,opening,rest⟩)

private theorem unexpected_execution (bytes : alloc.vec.Vec U8) (token : Token) (tail : Tokens)
    (prior : alloc.vec.Vec prefixes.Declaration) (countLimit valueLimit : Usize)
    (notPrefix : token.terminal ≠ .Keyword .Prefix) (notOntology : token.terminal ≠ .Keyword .Ontology) :
    scan_prefixes bytes (.Cons token tail) prior countLimit valueLimit = .ok (.Err (.Expected .Ontology token.start)) := by
  rw [scan_prefixes]
  cases token with
  | mk terminal start finish =>
    cases terminal <;> first | rfl | rename_i keyword; cases keyword <;> simp_all

/-- Actual maximal prefix scanning terminates even on arbitrary token input:
    every accepted declaration consumes five body tokens plus its keyword. -/
theorem scan_prefixes_total_correct (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (prior : alloc.vec.Vec prefixes.Declaration) (countLimit valueLimit : Usize) :
    ∃ result, scan_prefixes bytes tokens prior countLimit valueLimit = .ok result ∧
      Run bytes.val bytes.len countLimit.val valueLimit.val tokens prior.val result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected .Ontology bytes.len),by rw [scan_prefixes],.empty _⟩
  | Cons token tail =>
    by_cases prefixKind : token.terminal = .Keyword .Prefix
    · rw [scan_prefixes,prefixKind]
      by_cases full : countLimit.val ≤ prior.val.length
      · exact ⟨.Err (.DeclarationLimit token.start),by simp [alloc.vec.Vec.len_val,UScalar.le_equiv,full],.count _ _ _ prefixKind full⟩
      · have room : prior.val.length < countLimit.val := by omega
        simp only [alloc.vec.Vec.len_val,UScalar.le_equiv,full,↓reduceIte]
        obtain ⟨body,bodyRead,bodyCorrect⟩ := read_declaration_total_correct bytes tail valueLimit
        rw [bodyRead,bind_ok]
        cases body with
        | Err error => exact ⟨.Err error,rfl,.bodyError prefixKind room bodyCorrect⟩
        | Ok pair =>
          obtain ⟨declaration,rest⟩ := pair
          simp only [uncurry_apply_pair]
          obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec prior declaration (by scalar_tac))
          obtain ⟨result,executed,correct⟩ := scan_prefixes_total_correct bytes rest appended countLimit valueLimit
          refine ⟨result,by rw [push,bind_ok]; exact executed,.declaration prefixKind room bodyCorrect ?_⟩
          simpa [contents] using correct
    · by_cases ontologyKind : token.terminal = .Keyword .Ontology
      · rw [scan_prefixes,ontologyKind]
        obtain ⟨opening,openingRead,openingCorrect⟩ := take_expected_total_correct tail .Open bytes.len
        simp [openingRead,bind_ok]
        cases opening with
        | Err error => exact ⟨.Err error,rfl,.ontologyError ontologyKind openingCorrect⟩
        | Ok pair =>
          obtain ⟨opening,rest⟩ := pair
          exact ⟨.Ok ⟨prior,token,opening,rest⟩,rfl,.ready ontologyKind openingCorrect prior rfl⟩
      · exact ⟨.Err (.Expected .Ontology token.start),unexpected_execution bytes token tail prior countLimit valueLimit prefixKind ontologyKind,
          .unexpected _ _ _ prefixKind ontologyKind⟩
termination_by Rowl.FunctionalLexer.TokenCount tokens
decreasing_by
  have progress := declaration_token_progress bodyCorrect
  simp only [Rowl.FunctionalLexer.TokenCount]
  omega

private theorem run_execution (bytes : alloc.vec.Vec U8) (countLimit valueLimit : Usize)
    {tokens : Tokens} {prior : List prefixes.Declaration} {result : core.result.Result PrefixHeader PrefixSyntaxError}
    (run : Run bytes.val bytes.len countLimit.val valueLimit.val tokens prior result) :
    ∀ declarations : alloc.vec.Vec prefixes.Declaration, declarations.val = prior →
      scan_prefixes bytes tokens declarations countLimit valueLimit = .ok result := by
  induction run with
  | empty => intro declarations same; rw [scan_prefixes]
  | unexpected token tail prior notPrefix notOntology =>
    intro declarations same
    exact unexpected_execution bytes token tail declarations countLimit valueLimit notPrefix notOntology
  | count token tail prior kind full =>
    intro declarations same
    rw [scan_prefixes,kind]
    simp [alloc.vec.Vec.len_val,UScalar.le_equiv,same,full]
  | @bodyError token tail prior error kind room body =>
    intro declarations same
    have read := (read_declaration_result_iff bytes _ valueLimit _).mpr body
    rw [scan_prefixes,kind]
    simp [alloc.vec.Vec.len_val,UScalar.le_equiv,same,show ¬ countLimit.val ≤ prior.length from by omega,read]
  | @declaration token tail rest prior declaration result kind room body later ih =>
    intro declarations same
    have read := (read_declaration_result_iff bytes tail valueLimit (.Ok (declaration,rest))).mpr body
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec declarations declaration (by scalar_tac))
    have next := ih appended (by simpa [same] using contents)
    rw [scan_prefixes,kind]
    simp [alloc.vec.Vec.len_val,UScalar.le_equiv,same,show ¬ countLimit.val ≤ prior.length from by omega,read,push,next]
  | ontologyError kind failure =>
    intro declarations same
    cases failure with
    | empty => rw [scan_prefixes,kind]; simp [take_expected]
    | wrong _ _ token rest _ wrong =>
      rw [scan_prefixes,kind]
      simp [take_expected,expected_terminal_total_correct,wrong]
    | later _ impossible => cases impossible
  | @ready token opening tail rest prior kind taken expectedRows contents =>
    intro declarations same
    have rowsSame : declarations = expectedRows := (alloc.vec.Vec.eq_iff _ _).mpr (same.trans contents.symm)
    rw [scan_prefixes,kind]
    rw [taken.1]
    simp [take_expected,expected_terminal_total_correct,taken.2,rowsSame]

/-- The whole independent maximal-prefix derivation, including exact rows,
    untouched ontology suffix and first diagnostics, equals actual scanning. -/
theorem scan_prefixes_result_iff (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (prior : alloc.vec.Vec prefixes.Declaration) (countLimit valueLimit : Usize)
    (result : core.result.Result PrefixHeader PrefixSyntaxError) :
    scan_prefixes bytes tokens prior countLimit valueLimit = .ok result ↔
      Run bytes.val bytes.len countLimit.val valueLimit.val tokens prior.val result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := scan_prefixes_total_correct bytes tokens prior countLimit valueLimit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    exact run_execution bytes countLimit valueLimit source prior rfl

/-- Complete original-byte contract: every source is lexed before any prefix
    syntax or count/value limit, and all lexical errors retain the lexer evidence. -/
def Correct (source : List U8) (eof : Usize) (tokenLimit countLimit valueLimit : Nat) :
    core.result.Result PrefixHeader PrefixReadError → Prop
  | .Ok header => ∃ tokens, Rowl.FunctionalLexer.Correct source tokenLimit (.Tokens tokens) ∧
      Run source eof countLimit valueLimit tokens [] (.Ok header)
  | .Err (.Syntax error) => ∃ tokens, Rowl.FunctionalLexer.Correct source tokenLimit (.Tokens tokens) ∧
      Run source eof countLimit valueLimit tokens [] (.Err error)
  | .Err (.InvalidText error) => Rowl.FunctionalLexer.Correct source tokenLimit (.InvalidText error)
  | .Err (.NoToken offset) => Rowl.FunctionalLexer.Correct source tokenLimit (.NoToken offset)
  | .Err (.MissingSeparator offset) => Rowl.FunctionalLexer.Correct source tokenLimit (.MissingSeparator offset)
  | .Err (.TokenLimit offset) => Rowl.FunctionalLexer.Correct source tokenLimit (.TokenLimit offset)
  | .Err (.InvalidSpan _) => False

/-- Public byte-to-prefix-header reading terminates and obeys the composed
    source grammar, exact fields and all lexical/syntax/value/count phases. -/
theorem read_prefix_header_total_correct (bytes : alloc.vec.Vec U8) (tokenLimit countLimit valueLimit : Usize) :
    ∃ result, read_prefix_header bytes tokenLimit countLimit valueLimit = .ok result ∧
      Correct bytes.val bytes.len tokenLimit.val countLimit.val valueLimit.val result := by
  obtain ⟨lexed,lexRead,lexCorrect⟩ := Rowl.FunctionalLexer.lex_total_correct bytes tokenLimit
  rw [read_prefix_header,lexRead,bind_ok]
  cases lexed with
  | Tokens tokens =>
    simp only
    obtain ⟨scanned,scanRead,scanCorrect⟩ := scan_prefixes_total_correct bytes tokens (alloc.vec.Vec.new prefixes.Declaration) countLimit valueLimit
    rw [scanRead,bind_ok]
    cases scanned with
    | Ok header => exact ⟨.Ok header,rfl,tokens,lexCorrect,by simpa using scanCorrect⟩
    | Err error => exact ⟨.Err (.Syntax error),rfl,tokens,lexCorrect,by simpa using scanCorrect⟩
  | InvalidText error => exact ⟨.Err (.InvalidText error),rfl,lexCorrect⟩
  | NoToken offset => exact ⟨.Err (.NoToken offset),rfl,lexCorrect⟩
  | MissingSeparator offset => exact ⟨.Err (.MissingSeparator offset),rfl,lexCorrect⟩
  | TokenLimit offset => exact ⟨.Err (.TokenLimit offset),rfl,lexCorrect⟩
  | InvalidSpan offset =>
    exact False.elim (Rowl.FunctionalLexer.lex_excludes_invalid_span bytes tokenLimit offset lexRead)

/-- Exact original-byte header values are accepted precisely when the independent
    whole-source lexer and maximal leading-prefix grammar derive those values. -/
theorem read_prefix_header_accepted_iff (bytes : alloc.vec.Vec U8) (tokenLimit countLimit valueLimit : Usize)
    (header : PrefixHeader) :
    read_prefix_header bytes tokenLimit countLimit valueLimit = .ok (.Ok header) ↔
      Correct bytes.val bytes.len tokenLimit.val countLimit.val valueLimit.val (.Ok header) := by
  constructor
  · intro accepted
    obtain ⟨actual,executed,correct⟩ := read_prefix_header_total_correct bytes tokenLimit countLimit valueLimit
    have same := Result.ok_injective (executed.symm.trans accepted)
    simpa [same] using correct
  · rintro ⟨tokens,lexSource,headerSource⟩
    have lexRead := (Rowl.FunctionalLexer.lex_tokens_iff bytes tokenLimit tokens).mpr lexSource
    have scanRead := (scan_prefixes_result_iff bytes tokens (alloc.vec.Vec.new prefixes.Declaration) countLimit valueLimit (.Ok header)).mpr
      (by simpa using headerSource)
    simp [read_prefix_header,lexRead,scanRead]

/-- Every prefix syntax/value/count failure and original offset occurs exactly
    when the whole byte reader returns it, after successful complete lexing. -/
theorem read_prefix_header_syntax_error_iff (bytes : alloc.vec.Vec U8) (tokenLimit countLimit valueLimit : Usize)
    (error : PrefixSyntaxError) :
    read_prefix_header bytes tokenLimit countLimit valueLimit = .ok (.Err (.Syntax error)) ↔
      Correct bytes.val bytes.len tokenLimit.val countLimit.val valueLimit.val (.Err (.Syntax error)) := by
  constructor
  · intro rejected
    obtain ⟨actual,executed,correct⟩ := read_prefix_header_total_correct bytes tokenLimit countLimit valueLimit
    have same := Result.ok_injective (executed.symm.trans rejected)
    simpa [same] using correct
  · rintro ⟨tokens,lexSource,headerSource⟩
    have lexRead := (Rowl.FunctionalLexer.lex_tokens_iff bytes tokenLimit tokens).mpr lexSource
    have scanRead := (scan_prefixes_result_iff bytes tokens (alloc.vec.Vec.new prefixes.Declaration) countLimit valueLimit (.Err error)).mpr
      (by simpa using headerSource)
    simp [read_prefix_header,lexRead,scanRead]

/-- Independent complete leading-prefix grammar, with original order and exact
    declaration values, ending at the original Ontology keyword/opening. -/
inductive Section (source : List U8) (eof : Usize) (valueLimit : Nat) :
    Tokens → List prefixes.Declaration → Token → Token → Tokens → Prop
  | ontology {token opening : Token} {tail rest : Tokens}
      (ontologyKind : token.terminal = .Keyword .Ontology) (openingKind : Taken tail .Open opening rest) :
      Section source eof valueLimit (.Cons token tail) [] token opening rest
  | prefixDeclaration {token ontology opening : Token} {tail rest remaining : Tokens}
      {declaration : prefixes.Declaration} {rows : List prefixes.Declaration}
      (prefixKind : token.terminal = .Keyword .Prefix) (body : BodyRun source eof valueLimit tail (.Ok (declaration,rest)))
      (later : Section source eof valueLimit rest rows ontology opening remaining) :
      Section source eof valueLimit (.Cons token tail) (declaration::rows) ontology opening remaining

private theorem run_section {source : List U8} {eof : Usize} {countLimit valueLimit : Nat}
    {tokens : Tokens} {prior : List prefixes.Declaration} {result : core.result.Result PrefixHeader PrefixSyntaxError}
    (run : Run source eof countLimit valueLimit tokens prior result) : ∀ header,
    result = .Ok header → ∃ rows, Section source eof valueLimit tokens rows header.ontology header.opening header.remaining ∧
      header.declarations.val = prior++rows := by
  induction run with
  | empty | unexpected | count | bodyError | ontologyError => intro header impossible; cases impossible
  | declaration kind room body later ih =>
    intro header accepted
    obtain ⟨rows,derivation,contents⟩ := ih header accepted
    exact ⟨_::rows,.prefixDeclaration kind body derivation,by simpa [List.append_assoc] using contents⟩
  | ready kind opening declarations contents =>
    intro header accepted
    cases accepted
    exact ⟨[],.ontology kind opening,by simpa using contents⟩
private theorem run_count {source : List U8} {eof : Usize} {countLimit valueLimit : Nat}
    {tokens : Tokens} {prior : List prefixes.Declaration} {result : core.result.Result PrefixHeader PrefixSyntaxError}
    (run : Run source eof countLimit valueLimit tokens prior result) : ∀ header,
    result = .Ok header → prior.length ≤ countLimit → header.declarations.val.length ≤ countLimit := by
  induction run with
  | empty | unexpected | count | bodyError | ontologyError => intro header impossible bound; cases impossible
  | declaration kind room body later ih =>
    intro header accepted bound
    apply ih header accepted
    simp
    omega
  | ready kind opening declarations contents => intro header accepted bound; cases accepted; simpa [contents] using bound
private theorem section_values {source : List U8} {eof : Usize} {valueLimit : Nat} {tokens rest : Tokens}
    {rows : List prefixes.Declaration} {ontology opening : Token}
    (derivation : Section source eof valueLimit tokens rows ontology opening rest) :
    ∀ row ∈ rows, Rowl.Prefixes.PrefixAccepted row.name.val ∧ Rowl.Prefixes.IriAccepted row.namespace.val := by
  induction derivation with
  | ontology => simp
  | @prefixDeclaration _ _ _ _ _ _ declaration rows kind body later ih =>
    intro row member
    rcases List.mem_cons.mp member with same | included
    · subst row
      exact declaration_value_grammars body
    · exact ih row included

/-- Every accepted original byte header has the complete leading-prefix source
    derivation, exact ordered records, bounded count and lexical value grammars. -/
theorem read_prefix_header_source (bytes : alloc.vec.Vec U8) (tokenLimit countLimit valueLimit : Usize)
    (header : PrefixHeader) (accepted : read_prefix_header bytes tokenLimit countLimit valueLimit = .ok (.Ok header)) :
    (∃ tokens, Rowl.FunctionalLexer.Correct bytes.val tokenLimit.val (.Tokens tokens) ∧
      Section bytes.val bytes.len valueLimit.val tokens header.declarations.val header.ontology header.opening header.remaining) ∧
    header.declarations.val.length ≤ countLimit.val ∧
    (∀ row ∈ header.declarations.val, Rowl.Prefixes.PrefixAccepted row.name.val ∧ Rowl.Prefixes.IriAccepted row.namespace.val) := by
  obtain ⟨tokens,lexSource,run⟩ := (read_prefix_header_accepted_iff bytes tokenLimit countLimit valueLimit header).mp accepted
  obtain ⟨rows,derivation,contents⟩ := run_section run header rfl
  have same : header.declarations.val = rows := by simpa using contents
  rw [← same] at derivation
  exact ⟨⟨tokens,lexSource,derivation⟩,run_count run header rfl (by simp),section_values derivation⟩

/-- Checking source-derived records establishes every normative prefix-table
    requirement while retaining exactly the original parsed declaration vector. -/
theorem checked_source_prefix_table (bytes : alloc.vec.Vec U8) (tokenLimit countLimit valueLimit : Usize)
    (header : PrefixHeader) (table : prefixes.PrefixTable)
    (accepted : read_prefix_header bytes tokenLimit countLimit valueLimit = .ok (.Ok header))
    (checked : prefixes.check header.declarations = .ok (.Ready table)) :
    table.declarations = header.declarations ∧ Rowl.Prefixes.WellFormed table ∧
    ∃ tokens, Rowl.FunctionalLexer.Correct bytes.val tokenLimit.val (.Tokens tokens) ∧
      Section bytes.val bytes.len valueLimit.val tokens table.declarations.val header.ontology header.opening header.remaining := by
  have checkedSource := Rowl.Prefixes.successful_check_correct header.declarations table checked
  have source := (read_prefix_header_source bytes tokenLimit countLimit valueLimit header accepted).1
  exact ⟨checkedSource.1,checkedSource.2,by simpa [checkedSource.1] using source⟩

/-- The byte reader cannot expose an invalid-span lexer fallback. -/
theorem invalid_span_unreachable (bytes : alloc.vec.Vec U8) (tokenLimit countLimit valueLimit offset : Usize) :
    read_prefix_header bytes tokenLimit countLimit valueLimit ≠ .ok (.Err (.InvalidSpan offset)) := by
  intro rejected
  obtain ⟨actual,executed,correct⟩ := read_prefix_header_total_correct bytes tokenLimit countLimit valueLimit
  have same := Result.ok_injective (executed.symm.trans rejected)
  subst actual
  exact correct

end Rowl.FunctionalPrefixes
