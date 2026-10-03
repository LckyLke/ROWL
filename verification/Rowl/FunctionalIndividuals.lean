import Rowl.FunctionalHeaderIdentity
import Rowl.FunctionalNames

/-!
Functional Syntax individuals and individual lists, proved total and exact
against an independent grammar: an individual is an IRI resolved through the
checked prefix rows or a node ID with its exact label, and a list is the
maximal individual sequence before `)`, bounded in length, followed by its
minimum-length check. Every result and first error has its independent
derivation, and every derivation is the actual result.
-/
namespace Rowl.FunctionalIndividuals
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional_individuals
open RowlRust.functional_lexer RowlRust.functional
open Rowl.FunctionalLexer (TokenCount)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The two individual families: a named individual's IRI or a node ID. -/
def IndividualKindOf : Terminal → Option IndividualKind
  | .FullIri => some (.Named .Full)
  | .AbbreviatedIri => some (.Named .Abbreviated)
  | .NodeId => some .Anonymous
  | _ => none
/-- Where the next token starts, or the source length at the end. -/
def Position (eof : Usize) : Tokens → Usize
  | .Empty => eof
  | .Cons token _ => token.start

theorem individual_kind_total_correct (terminal : Terminal) :
    individual_kind terminal = .ok (IndividualKindOf terminal) := by
  cases terminal <;> rfl
theorem closes_total_correct (terminal : Terminal) :
    functional_individuals.closes terminal = .ok (decide (terminal = .Close)) := by
  cases terminal <;> simp [functional_individuals.closes]
theorem position_total_correct (tokens : Tokens) (eof : Usize) : position tokens eof = .ok (Position eof tokens) := by
  cases tokens <;> rfl

/-- Independent individual grammar: an IRI resolves through the checked prefix
    rows; a node ID keeps its exact label without `_:`. A missing token reports
    the original source length, any other token its start. -/
inductive IndividualRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (SourceIndividual × Tokens) IndividualError → Prop
  | empty : IndividualRun rows source eof limit .Empty (.Err (.Expected eof))
  | wrong {token : Token} {rest : Tokens} (other : IndividualKindOf token.terminal = none) :
      IndividualRun rows source eof limit (.Cons token rest) (.Err (.Expected token.start))
  | iriError {token : Token} {rest : Tokens} {kind : functional_iris.SourceIriKind}
      {error : functional_iris.SourceIriError} (individualKind : IndividualKindOf token.terminal = some (.Named kind))
      (failure : Rowl.FunctionalIris.ErrorCorrect rows kind source token.start.val token.end.val limit error) :
      IndividualRun rows source eof limit (.Cons token rest) (.Err (.Iri error))
  | named {token : Token} {rest : Tokens} {kind : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8}
      (individualKind : IndividualKindOf token.terminal = some (.Named kind))
      (valueSource : Rowl.FunctionalIris.Success rows kind source token.start.val token.end.val limit value) :
      IndividualRun rows source eof limit (.Cons token rest) (.Ok (.Named ⟨token,value⟩,rest))
  | anonymousError {token : Token} {rest : Tokens} {error : functional_names.NameError}
      (individualKind : IndividualKindOf token.terminal = some .Anonymous)
      (failure : Rowl.FunctionalNames.ErrorCorrect .NodeId source token.start.val token.end.val limit error) :
      IndividualRun rows source eof limit (.Cons token rest) (.Err (.Anonymous error))
  | anonymous {token : Token} {rest : Tokens} {label : alloc.vec.Vec U8}
      (individualKind : IndividualKindOf token.terminal = some .Anonymous)
      (labelValue : Rowl.FunctionalNames.Correct .NodeId source token.start.val token.end.val limit (.Ok label)) :
      IndividualRun rows source eof limit (.Cons token rest) (.Ok (.Anonymous token label,rest))

/-- Individual reading is total and follows the independent grammar. -/
theorem read_individual_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize) :
    ∃ result, read_individual table bytes tokens limit = .ok result ∧
      IndividualRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected bytes.len),by rw [read_individual],.empty⟩
  | Cons token rest =>
    rw [read_individual]
    simp only [individual_kind_total_correct,bind_ok]
    cases kind : IndividualKindOf token.terminal with
    | none => exact ⟨.Err (.Expected token.start),rfl,.wrong kind⟩
    | some found =>
      cases found with
      | Named family =>
        obtain ⟨result,executed,correct⟩ :=
          Rowl.FunctionalIris.resolve_span_total_correct table family bytes token.start token.end limit
        simp only [executed,bind_ok]
        cases result with
        | Ok value => exact ⟨.Ok (.Named ⟨token,value⟩,rest),rfl,.named kind correct⟩
        | Err error => exact ⟨.Err (.Iri error),rfl,.iriError kind correct⟩
      | Anonymous =>
        obtain ⟨result,executed,correct⟩ :=
          Rowl.FunctionalNames.read_span_total_correct .NodeId bytes token.start token.end limit
        simp only [executed,bind_ok]
        cases result with
        | Ok label => exact ⟨.Ok (.Anonymous token label,rest),rfl,.anonymous kind correct⟩
        | Err error => exact ⟨.Err (.Anonymous error),rfl,.anonymousError kind correct⟩
/-- Every exact individual and first error is equivalent to its independent derivation. -/
theorem read_individual_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limit : Usize)
    (result : core.result.Result (SourceIndividual × Tokens) IndividualError) :
    read_individual table bytes tokens limit = .ok result ↔
      IndividualRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_individual_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    cases source with
    | empty => rw [read_individual]
    | wrong other =>
      rw [read_individual]
      simp [individual_kind_total_correct,other]
    | @iriError token rest kind error individualKind failure =>
      have iriRead := (Rowl.FunctionalIris.resolve_span_error_iff table kind bytes token.start token.end limit error).mpr failure
      rw [read_individual]
      simp [individual_kind_total_correct,individualKind,iriRead]
    | @named token rest kind value individualKind valueSource =>
      have iriRead := (Rowl.FunctionalIris.resolve_span_value_iff table kind bytes token.start token.end limit value).mpr valueSource
      rw [read_individual]
      simp [individual_kind_total_correct,individualKind,iriRead]
    | @anonymousError token rest error individualKind failure =>
      have labelRead := (Rowl.FunctionalNames.read_span_error_iff .NodeId bytes token.start token.end limit error).mpr failure
      rw [read_individual]
      simp [individual_kind_total_correct,individualKind,labelRead]
    | @anonymous token rest label individualKind labelValue =>
      have labelRead := (Rowl.FunctionalNames.read_span_accepted_iff .NodeId bytes token.start token.end limit label).mpr labelValue
      rw [read_individual]
      simp [individual_kind_total_correct,individualKind,labelRead]
/-- An accepted individual consumes exactly its one token. -/
theorem individual_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens rest : Tokens} {individual : SourceIndividual}
    (accepted : IndividualRun rows source eof limit tokens (.Ok (individual,rest))) :
    TokenCount tokens = 1+TokenCount rest := by
  cases accepted <;> rfl

/-- Independent maximal individual sequence: it stops before `)` or at the end;
    otherwise the member count is checked, then one individual is read and
    appended in source order. -/
inductive IndividualsRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    List SourceIndividual → Tokens →
      core.result.Result (alloc.vec.Vec SourceIndividual × Tokens) IndividualError → Prop
  | empty {prior : List SourceIndividual} {records : alloc.vec.Vec SourceIndividual} (contents : records.val = prior) :
      IndividualsRun rows source eof count limit prior .Empty (.Ok (records,.Empty))
  | stop {prior : List SourceIndividual} {token : Token} {tail : Tokens} {records : alloc.vec.Vec SourceIndividual}
      (close : token.terminal = .Close) (contents : records.val = prior) :
      IndividualsRun rows source eof count limit prior (.Cons token tail) (.Ok (records,.Cons token tail))
  | countLimit {prior : List SourceIndividual} {token : Token} {tail : Tokens}
      (notClose : token.terminal ≠ .Close) (full : count ≤ prior.length) :
      IndividualsRun rows source eof count limit prior (.Cons token tail) (.Err (.CountLimit token.start))
  | memberError {prior : List SourceIndividual} {token : Token} {tail : Tokens} {error : IndividualError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (member : IndividualRun rows source eof limit (.Cons token tail) (.Err error)) :
      IndividualsRun rows source eof count limit prior (.Cons token tail) (.Err error)
  | member {prior : List SourceIndividual} {token : Token} {tail rest : Tokens} {item : SourceIndividual}
      {result : core.result.Result (alloc.vec.Vec SourceIndividual × Tokens) IndividualError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (memberRun : IndividualRun rows source eof limit (.Cons token tail) (.Ok (item,rest)))
      (later : IndividualsRun rows source eof count limit (prior++[item]) rest result) :
      IndividualsRun rows source eof count limit prior (.Cons token tail) result

/-- The actual individual scanner terminates, follows the independent grammar,
    and never returns more tokens than it received. -/
theorem read_individuals_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (members : alloc.vec.Vec SourceIndividual) (count limit : Usize) :
    ∃ result, read_individuals table bytes tokens members count limit = .ok result ∧
      IndividualsRun table.declarations.val bytes.val bytes.len count.val limit.val members.val tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest ≤ TokenCount tokens := by
  rw [read_individuals.eq_def]
  cases tokens with
  | Empty =>
    exact ⟨.Ok (members,.Empty),rfl,.empty rfl,by intro value rest same; cases same; simp⟩
  | Cons token tail =>
    simp only [closes_total_correct,bind_ok]
    by_cases close : token.terminal = .Close
    · refine ⟨.Ok (members,.Cons token tail),by simp [close],.stop close rfl,?_⟩
      intro value rest same
      cases same
      simp
    · by_cases full : count.val ≤ members.val.length
      · refine ⟨.Err (.CountLimit token.start),?_,.countLimit close full,by intro value rest impossible; cases impossible⟩
        simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full]
      · have room : members.val.length < count.val := by omega
        obtain ⟨member,memberRead,memberCorrect⟩ := read_individual_total_correct table bytes (.Cons token tail) limit
        cases member with
        | Err error =>
          refine ⟨.Err error,?_,.memberError close room memberCorrect,by intro value rest impossible; cases impossible⟩
          simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,memberRead]
        | Ok pair =>
          obtain ⟨member,rest⟩ := pair
          have memberStep := individual_progress memberCorrect
          obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec members member (by scalar_tac))
          obtain ⟨result,executed,correct,progress⟩ :=
            read_individuals_total_correct table bytes rest appended count limit
          refine ⟨result,?_,.member close room memberCorrect (by simpa [contents] using correct),?_⟩
          · simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,memberRead,push,executed]
          · intro value rest' same
            have one := progress value rest' same
            omega
termination_by TokenCount tokens
decreasing_by
  all_goals
    try subst_vars
    try simp only [TokenCount] at *
    try omega

/-- Every independent individual-sequence derivation is the actual result. -/
theorem individuals_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (count limit : Usize)
    (members : alloc.vec.Vec SourceIndividual) {prior : List SourceIndividual} (contents : members.val = prior)
    {tokens : Tokens} {result : core.result.Result (alloc.vec.Vec SourceIndividual × Tokens) IndividualError}
    (run : IndividualsRun table.declarations.val bytes.val bytes.len count.val limit.val prior tokens result) :
    read_individuals table bytes tokens members count limit = .ok result := by
  cases run with
  | empty records =>
    have equal : members = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_individuals.eq_def,equal]
  | stop close records =>
    have equal : members = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_individuals.eq_def,equal]
    simp [closes_total_correct,close]
  | countLimit notClose full =>
    rw [read_individuals.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,full]
  | memberError notClose room member =>
    have memberRead := (read_individual_result_iff table bytes _ limit _).mpr member
    rw [read_individuals.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,
      show ¬ count.val ≤ prior.length by omega,memberRead]
  | member notClose room memberRun later =>
    have memberRead := (read_individual_result_iff table bytes _ limit _).mpr memberRun
    have step := individual_progress memberRun
    obtain ⟨appended,push,appendedContents⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.push_spec members _ (by rw [contents]; scalar_tac))
    have laterRead := individuals_execution table bytes count limit appended
      (by rw [appendedContents,contents]) later
    rw [read_individuals.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,
      show ¬ count.val ≤ prior.length by omega,memberRead,push,laterRead]
termination_by TokenCount tokens
decreasing_by
  all_goals
    try subst_vars
    try simp only [TokenCount] at *
    try omega

/-- Every exact individual sequence and first error is equivalent to its independent derivation. -/
theorem read_individuals_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (members : alloc.vec.Vec SourceIndividual) (count limit : Usize)
    (result : core.result.Result (alloc.vec.Vec SourceIndividual × Tokens) IndividualError) :
    read_individuals table bytes tokens members count limit = .ok result ↔
      IndividualsRun table.declarations.val bytes.val bytes.len count.val limit.val members.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct,_⟩ := read_individuals_total_correct table bytes tokens members count limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · exact individuals_execution table bytes count limit members rfl

/-- Independent individual list: the maximal sequence from no members, then at
    least `least` of them; a shorter list expects an individual where it stops. -/
inductive ListRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (least count limit : Nat) :
    Tokens → core.result.Result (alloc.vec.Vec SourceIndividual × Tokens) IndividualError → Prop
  | error {tokens : Tokens} {error : IndividualError}
      (members : IndividualsRun rows source eof count limit [] tokens (.Err error)) :
      ListRun rows source eof least count limit tokens (.Err error)
  | tooFew {tokens rest : Tokens} {list : alloc.vec.Vec SourceIndividual}
      (members : IndividualsRun rows source eof count limit [] tokens (.Ok (list,rest)))
      (few : list.val.length < least) :
      ListRun rows source eof least count limit tokens (.Err (.Expected (Position eof rest)))
  | ok {tokens rest : Tokens} {list : alloc.vec.Vec SourceIndividual}
      (members : IndividualsRun rows source eof count limit [] tokens (.Ok (list,rest)))
      (enough : least ≤ list.val.length) :
      ListRun rows source eof least count limit tokens (.Ok (list,rest))

/-- The actual list reader terminates, follows the independent grammar, and
    never returns more tokens than it received. -/
theorem read_individual_list_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (least count limit : Usize) :
    ∃ result, read_individual_list table bytes tokens least count limit = .ok result ∧
      ListRun table.declarations.val bytes.val bytes.len least.val count.val limit.val tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest ≤ TokenCount tokens := by
  rw [read_individual_list]
  obtain ⟨members,membersRead,membersCorrect,membersProgress⟩ :=
    read_individuals_total_correct table bytes tokens (alloc.vec.Vec.new SourceIndividual) count limit
  have start : (alloc.vec.Vec.new SourceIndividual).val = [] := rfl
  rw [start] at membersCorrect
  cases members with
  | Err error =>
    exact ⟨.Err error,by simp [membersRead],.error membersCorrect,by intro value rest impossible; cases impossible⟩
  | Ok pair =>
    obtain ⟨list,rest⟩ := pair
    by_cases few : list.val.length < least.val
    · refine ⟨.Err (.Expected (Position bytes.len rest)),?_,.tooFew membersCorrect few,
        by intro value rest impossible; cases impossible⟩
      simp [membersRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,position_total_correct]
    · have enough : least.val ≤ list.val.length := by omega
      refine ⟨.Ok (list,rest),?_,.ok membersCorrect enough,?_⟩
      · simp [membersRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few]
      · intro value rest' same
        cases same
        exact membersProgress list rest rfl
/-- Every exact individual list and first error is equivalent to its independent derivation. -/
theorem read_individual_list_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (least count limit : Usize)
    (result : core.result.Result (alloc.vec.Vec SourceIndividual × Tokens) IndividualError) :
    read_individual_list table bytes tokens least count limit = .ok result ↔
      ListRun table.declarations.val bytes.val bytes.len least.val count.val limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct,_⟩ := read_individual_list_total_correct table bytes tokens least count limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    have start : (alloc.vec.Vec.new SourceIndividual).val = [] := rfl
    rw [read_individual_list]
    cases source with
    | error members =>
      have membersRead := individuals_execution table bytes count limit (alloc.vec.Vec.new SourceIndividual) start members
      simp [membersRead]
    | tooFew members few =>
      have membersRead := individuals_execution table bytes count limit (alloc.vec.Vec.new SourceIndividual) start members
      simp [membersRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,few,position_total_correct]
    | ok members enough =>
      have membersRead := individuals_execution table bytes count limit (alloc.vec.Vec.new SourceIndividual) start members
      simp [membersRead,alloc.vec.Vec.len_val,UScalar.lt_equiv,Nat.not_lt.mpr enough]
/-- An accepted individual list never consumes more tokens than it is given. -/
theorem list_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {least count limit : Nat}
    {tokens rest : Tokens} {list : alloc.vec.Vec SourceIndividual}
    (accepted : ListRun rows source eof least count limit tokens (.Ok (list,rest))) :
    TokenCount rest ≤ TokenCount tokens := by
  have scan : ∀ {prior : List SourceIndividual} {start : Tokens}
      {result : core.result.Result (alloc.vec.Vec SourceIndividual × Tokens) IndividualError},
      IndividualsRun rows source eof count limit prior start result →
        ∀ {records : alloc.vec.Vec SourceIndividual} {after : Tokens}, result = .Ok (records,after) →
          TokenCount after ≤ TokenCount start := by
    intro prior start result run
    induction run with
    | empty => intro records after same; cases same; simp
    | stop => intro records after same; cases same; simp
    | countLimit => intro records after same; cases same
    | memberError => intro records after same; cases same
    | member _ _ memberRun _ ih =>
      intro records after same
      have one := ih same
      have two := individual_progress memberRun
      omega
  cases accepted with
  | ok members _ => exact scan members rfl
end Rowl.FunctionalIndividuals
