import Rowl.FunctionalClasses
import Rowl.FunctionalAnnotations

/-!
Functional Syntax data property axioms (`SubDataPropertyOf`,
`EquivalentDataProperties`, `DisjointDataProperties`, `DataPropertyDomain`,
`DataPropertyRange`, `FunctionalDataProperty`), datatype definitions and keys,
proved total and exact against an independent grammar that composes the proved
annotation, class-expression, object-property and data-range grammars with
independent property-list grammars. Every result and first error has its
independent derivation, and every derivation is the actual result.
-/
namespace Rowl.FunctionalDataAxioms
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional_data_axioms
open RowlRust.functional_classes (ClassError ClassLimits SourceClass SourceObjectProperty)
open RowlRust.functional_ranges (RangeError SourceDataRange)
open RowlRust.functional_header (HeaderIri)
open RowlRust.functional_annotations (AnnotationLimits SourceAnnotations)
open RowlRust.functional_lexer RowlRust.functional
open Rowl.FunctionalHeaderIdentity (Kind iri_kind_total_correct)
open Rowl.FunctionalLexer (TokenCount)
open Rowl.FunctionalClasses (PropertyRun ClassRun Position offset_of_total_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The eight axiom keywords this stage reads. -/
def FormOf : Terminal → Option AxiomForm
  | .Keyword .SubDataPropertyOf => some .Sub
  | .Keyword .EquivalentDataProperties => some .Equivalent
  | .Keyword .DisjointDataProperties => some .Disjoint
  | .Keyword .DataPropertyDomain => some .Domain
  | .Keyword .DataPropertyRange => some .Range
  | .Keyword .FunctionalDataProperty => some .Functional
  | .Keyword .DatatypeDefinition => some .Definition
  | .Keyword .HasKey => some .Key
  | _ => none
/-- Independent first-terminal class required at each axiom position. -/
def Expected : DataAxiomExpected → Terminal → Prop
  | .Axiom, terminal => ∃ form, FormOf terminal = some form
  | .Open, terminal => terminal = .Open
  | .Iri, terminal => ∃ kind, Kind terminal = some kind
  | .Close, terminal => terminal = .Close

theorem axiom_form_total_correct (terminal : Terminal) : axiom_form terminal = .ok (FormOf terminal) := by
  cases terminal <;> first | rfl | (rename_i keyword; cases keyword <;> rfl)
theorem closes_total_correct (terminal : Terminal) :
    functional_data_axioms.closes terminal = .ok (decide (terminal = .Close)) := by
  cases terminal <;> simp [functional_data_axioms.closes]
theorem expected_terminal_total_correct (expected : DataAxiomExpected) (terminal : Terminal) :
    functional_data_axioms.expected_terminal expected terminal = .ok (decide (Expected expected terminal)) := by
  cases expected <;> cases terminal <;> (try (rename_i keyword; cases keyword)) <;>
    simp [functional_data_axioms.expected_terminal,Expected,axiom_form_total_correct,closes_total_correct,
      iri_kind_total_correct,FormOf,Kind,core.option.Option.is_some]

/-- One syntax step: the first token must belong to the expected class. -/
inductive TakeRun (eof : Usize) (expected : DataAxiomExpected) :
    Tokens → core.result.Result (Token × Tokens) DataAxiomError → Prop
  | empty : TakeRun eof expected .Empty (.Err (.Expected expected eof))
  | wrong (token : Token) (rest : Tokens) (different : ¬ Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Err (.Expected expected token.start))
  | taken (token : Token) (rest : Tokens) (accepted : Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Ok (token,rest))

theorem take_expected_total_correct (tokens : Tokens) (expected : DataAxiomExpected) (eof : Usize) :
    ∃ result, functional_data_axioms.take_expected tokens expected eof = .ok result ∧
      TakeRun eof expected tokens result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected expected eof),rfl,.empty⟩
  | Cons token rest =>
    by_cases accepted : Expected expected token.terminal
    · exact ⟨.Ok (token,rest),by simp [functional_data_axioms.take_expected,expected_terminal_total_correct,accepted],
        .taken _ _ accepted⟩
    · exact ⟨.Err (.Expected expected token.start),
        by simp [functional_data_axioms.take_expected,expected_terminal_total_correct,accepted],.wrong _ _ accepted⟩
private theorem take_run_unique {eof : Usize} {expected : DataAxiomExpected} {tokens : Tokens}
    {one two : core.result.Result (Token × Tokens) DataAxiomError}
    (first : TakeRun eof expected tokens one) (second : TakeRun eof expected tokens two) : one = two := by
  cases first <;> cases second <;> first | rfl | contradiction
theorem take_expected_result_iff (tokens : Tokens) (expected : DataAxiomExpected) (eof : Usize)
    (result : core.result.Result (Token × Tokens) DataAxiomError) :
    functional_data_axioms.take_expected tokens expected eof = .ok result ↔ TakeRun eof expected tokens result := by
  obtain ⟨actual,executed,correct⟩ := take_expected_total_correct tokens expected eof
  constructor
  · intro output
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    have same := take_run_unique correct source
    simpa [same] using executed
theorem take_progress {eof : Usize} {expected : DataAxiomExpected} {tokens rest : Tokens} {token : Token}
    (taken : TakeRun eof expected tokens (.Ok (token,rest))) : TokenCount tokens = 1+TokenCount rest := by
  cases taken
  rfl

/-- One IRI at an axiom position: an IRI token resolved through the checked
    prefix rows; any other token is reported as missing an IRI. -/
inductive IriRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (HeaderIri × Tokens) DataAxiomError → Prop
  | empty : IriRun rows source eof limit .Empty (.Err (.Expected .Iri eof))
  | notIri {token : Token} {rest : Tokens} (none : Kind token.terminal = none) :
      IriRun rows source eof limit (.Cons token rest) (.Err (.Expected .Iri token.start))
  | error {token : Token} {rest : Tokens} {family : functional_iris.SourceIriKind}
      {error : functional_iris.SourceIriError} (kind : Kind token.terminal = some family)
      (failure : Rowl.FunctionalIris.ErrorCorrect rows family source token.start.val token.end.val limit error) :
      IriRun rows source eof limit (.Cons token rest) (.Err (.Iri error))
  | value {token : Token} {rest : Tokens} {family : functional_iris.SourceIriKind} {value : alloc.vec.Vec U8}
      (kind : Kind token.terminal = some family)
      (success : Rowl.FunctionalIris.Success rows family source token.start.val token.end.val limit value) :
      IriRun rows source eof limit (.Cons token rest) (.Ok (⟨token,value⟩,rest))

theorem read_iri_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limit : Usize) :
    ∃ result, read_iri table bytes tokens limit = .ok result ∧
      IriRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected .Iri bytes.len),by rw [read_iri],.empty⟩
  | Cons token rest =>
    rw [read_iri]
    simp only [iri_kind_total_correct,bind_ok]
    cases kind : Kind token.terminal with
    | none => exact ⟨.Err (.Expected .Iri token.start),rfl,.notIri kind⟩
    | some family =>
      obtain ⟨resolved,resolveRead,resolveCorrect⟩ :=
        Rowl.FunctionalIris.resolve_span_total_correct table family bytes token.start token.end limit
      simp only [resolveRead,bind_ok]
      cases resolved with
      | Err error => exact ⟨.Err (.Iri error),rfl,.error kind resolveCorrect⟩
      | Ok value => exact ⟨.Ok (⟨token,value⟩,rest),rfl,.value kind resolveCorrect⟩
theorem read_iri_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limit : Usize) (result : core.result.Result (HeaderIri × Tokens) DataAxiomError) :
    read_iri table bytes tokens limit = .ok result ↔
      IriRun table.declarations.val bytes.val bytes.len limit.val tokens result := by
  obtain ⟨actual,executed,correct⟩ := read_iri_total_correct table bytes tokens limit
  constructor
  · intro output
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [executed]
    congr 1
    cases correct with
    | empty => cases source; rfl
    | notIri none => cases source <;> simp_all
    | @error token rest family error kind failure =>
      cases source with
      | notIri none => simp_all
      | @error _ _ family' error' kind' failure' =>
        rw [kind] at kind'
        cases kind'
        have one := (Rowl.FunctionalIris.resolve_span_error_iff table family bytes token.start token.end limit error).mpr
          failure
        have two := (Rowl.FunctionalIris.resolve_span_error_iff table family bytes token.start token.end limit error').mpr
          failure'
        rw [one] at two
        cases Result.ok_injective two
        rfl
      | @value _ _ family' value kind' success =>
        rw [kind] at kind'
        cases kind'
        have one := (Rowl.FunctionalIris.resolve_span_error_iff table family bytes token.start token.end limit error).mpr
          failure
        have two := (Rowl.FunctionalIris.resolve_span_value_iff table family bytes token.start token.end limit value).mpr
          success
        rw [one] at two
        cases Result.ok_injective two
    | @value token rest family value kind success =>
      cases source with
      | notIri none => simp_all
      | @error _ _ family' error kind' failure =>
        rw [kind] at kind'
        cases kind'
        have one := (Rowl.FunctionalIris.resolve_span_value_iff table family bytes token.start token.end limit value).mpr
          success
        have two := (Rowl.FunctionalIris.resolve_span_error_iff table family bytes token.start token.end limit error).mpr
          failure
        rw [one] at two
        cases Result.ok_injective two
      | @value _ _ family' value' kind' success' =>
        rw [kind] at kind'
        cases kind'
        have one := (Rowl.FunctionalIris.resolve_span_value_iff table family bytes token.start token.end limit value).mpr
          success
        have two := (Rowl.FunctionalIris.resolve_span_value_iff table family bytes token.start token.end limit value').mpr
          success'
        rw [one] at two
        cases Result.ok_injective two
        rfl
theorem iri_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens rest : Tokens} {iri : HeaderIri} (accepted : IriRun rows source eof limit tokens (.Ok (iri,rest))) :
    TokenCount tokens = 1+TokenCount rest := by
  cases accepted
  rfl

/-- Independent maximal IRI sequence: it stops before `)` or at the end;
    otherwise the count is checked, then one IRI is read and appended in source
    order. -/
inductive IrisRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    List HeaderIri → Tokens → core.result.Result (alloc.vec.Vec HeaderIri × Tokens) DataAxiomError → Prop
  | empty {prior : List HeaderIri} {records : alloc.vec.Vec HeaderIri} (contents : records.val = prior) :
      IrisRun rows source eof count limit prior .Empty (.Ok (records,.Empty))
  | stop {prior : List HeaderIri} {token : Token} {tail : Tokens} {records : alloc.vec.Vec HeaderIri}
      (close : token.terminal = .Close) (contents : records.val = prior) :
      IrisRun rows source eof count limit prior (.Cons token tail) (.Ok (records,.Cons token tail))
  | countLimit {prior : List HeaderIri} {token : Token} {tail : Tokens}
      (notClose : token.terminal ≠ .Close) (full : count ≤ prior.length) :
      IrisRun rows source eof count limit prior (.Cons token tail) (.Err (.CountLimit token.start))
  | memberError {prior : List HeaderIri} {token : Token} {tail : Tokens} {error : DataAxiomError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (member : IriRun rows source eof limit (.Cons token tail) (.Err error)) :
      IrisRun rows source eof count limit prior (.Cons token tail) (.Err error)
  | member {prior : List HeaderIri} {token : Token} {tail rest : Tokens} {item : HeaderIri}
      {result : core.result.Result (alloc.vec.Vec HeaderIri × Tokens) DataAxiomError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (memberRun : IriRun rows source eof limit (.Cons token tail) (.Ok (item,rest)))
      (later : IrisRun rows source eof count limit (prior++[item]) rest result) :
      IrisRun rows source eof count limit prior (.Cons token tail) result

theorem read_iris_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (members : alloc.vec.Vec HeaderIri) (limits : ClassLimits) :
    ∃ result, read_iris table bytes tokens members limits = .ok result ∧
      IrisRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val members.val tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest ≤ TokenCount tokens := by
  rw [read_iris.eq_def]
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
    · by_cases full : limits.count.val ≤ members.val.length
      · refine ⟨.Err (.CountLimit token.start),?_,.countLimit close full,by intro value rest impossible; cases impossible⟩
        simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full]
      · have room : members.val.length < limits.count.val := by omega
        obtain ⟨member,memberRead,memberCorrect⟩ := read_iri_total_correct table bytes (.Cons token tail) limits.iri
        cases member with
        | Err error =>
          refine ⟨.Err error,?_,.memberError close room memberCorrect,by intro value rest impossible; cases impossible⟩
          simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,memberRead]
        | Ok pair =>
          obtain ⟨member,rest⟩ := pair
          have memberStep := iri_progress memberCorrect
          obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec members member (by scalar_tac))
          obtain ⟨result,executed,correct,progress⟩ := read_iris_total_correct table bytes rest appended limits
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

theorem iris_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (limits : ClassLimits)
    (members : alloc.vec.Vec HeaderIri) {prior : List HeaderIri} (contents : members.val = prior)
    {tokens : Tokens} {result : core.result.Result (alloc.vec.Vec HeaderIri × Tokens) DataAxiomError}
    (run : IrisRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val prior tokens result) :
    read_iris table bytes tokens members limits = .ok result := by
  induction run generalizing members with
  | empty records =>
    have equal : members = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_iris.eq_def,equal]
  | stop close records =>
    have equal : members = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_iris.eq_def,equal]
    simp [closes_total_correct,close]
  | countLimit notClose full =>
    rw [read_iris.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,full]
  | @memberError prior token tail error notClose room member =>
    have notFull : ¬ limits.count.val ≤ prior.length := by omega
    rw [read_iris.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,notFull,
      (read_iri_result_iff table bytes _ limits.iri _).mpr member]
  | @member prior token tail rest item result notClose room memberRun later ih =>
    have notFull : ¬ limits.count.val ≤ prior.length := by omega
    obtain ⟨appended,push,appendedContents⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.push_spec members _ (by rw [contents]; scalar_tac))
    have laterRead := ih appended (by rw [appendedContents,contents])
    rw [read_iris.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,notFull,
      (read_iri_result_iff table bytes _ limits.iri _).mpr memberRun,push,laterRead]
theorem read_iris_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (members : alloc.vec.Vec HeaderIri) (limits : ClassLimits)
    (result : core.result.Result (alloc.vec.Vec HeaderIri × Tokens) DataAxiomError) :
    read_iris table bytes tokens members limits = .ok result ↔
      IrisRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val members.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct,_⟩ := read_iris_total_correct table bytes tokens members limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · exact iris_execution table bytes limits members rfl

/-- Independent maximal object property sequence of a key: it stops before `)`
    or at the end; otherwise the count is checked, then one object property
    expression is read and appended in source order. -/
inductive ObjectsRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    List SourceObjectProperty → Tokens →
      core.result.Result (alloc.vec.Vec SourceObjectProperty × Tokens) DataAxiomError → Prop
  | empty {prior : List SourceObjectProperty} {records : alloc.vec.Vec SourceObjectProperty}
      (contents : records.val = prior) :
      ObjectsRun rows source eof count limit prior .Empty (.Ok (records,.Empty))
  | stop {prior : List SourceObjectProperty} {token : Token} {tail : Tokens}
      {records : alloc.vec.Vec SourceObjectProperty} (close : token.terminal = .Close) (contents : records.val = prior) :
      ObjectsRun rows source eof count limit prior (.Cons token tail) (.Ok (records,.Cons token tail))
  | countLimit {prior : List SourceObjectProperty} {token : Token} {tail : Tokens}
      (notClose : token.terminal ≠ .Close) (full : count ≤ prior.length) :
      ObjectsRun rows source eof count limit prior (.Cons token tail) (.Err (.CountLimit token.start))
  | memberError {prior : List SourceObjectProperty} {token : Token} {tail : Tokens} {error : ClassError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (member : PropertyRun rows source eof limit (.Cons token tail) (.Err error)) :
      ObjectsRun rows source eof count limit prior (.Cons token tail) (.Err (.Class error))
  | member {prior : List SourceObjectProperty} {token : Token} {tail rest : Tokens} {item : SourceObjectProperty}
      {result : core.result.Result (alloc.vec.Vec SourceObjectProperty × Tokens) DataAxiomError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (memberRun : PropertyRun rows source eof limit (.Cons token tail) (.Ok (item,rest)))
      (later : ObjectsRun rows source eof count limit (prior++[item]) rest result) :
      ObjectsRun rows source eof count limit prior (.Cons token tail) result

theorem read_objects_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (members : alloc.vec.Vec SourceObjectProperty) (limits : ClassLimits) :
    ∃ result, read_objects table bytes tokens members limits = .ok result ∧
      ObjectsRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val members.val tokens
        result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest ≤ TokenCount tokens := by
  rw [read_objects.eq_def]
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
    · by_cases full : limits.count.val ≤ members.val.length
      · refine ⟨.Err (.CountLimit token.start),?_,.countLimit close full,by intro value rest impossible; cases impossible⟩
        simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full]
      · have room : members.val.length < limits.count.val := by omega
        obtain ⟨member,memberRead,memberCorrect⟩ :=
          Rowl.FunctionalClasses.read_object_property_total_correct table bytes (.Cons token tail) limits.iri
        cases member with
        | Err error =>
          refine ⟨.Err (.Class error),?_,.memberError close room memberCorrect,
            by intro value rest impossible; cases impossible⟩
          simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,memberRead]
        | Ok pair =>
          obtain ⟨member,rest⟩ := pair
          have memberStep := Rowl.FunctionalClasses.property_progress memberCorrect
          obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec members member (by scalar_tac))
          obtain ⟨result,executed,correct,progress⟩ := read_objects_total_correct table bytes rest appended limits
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

theorem objects_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (limits : ClassLimits)
    (members : alloc.vec.Vec SourceObjectProperty) {prior : List SourceObjectProperty} (contents : members.val = prior)
    {tokens : Tokens} {result : core.result.Result (alloc.vec.Vec SourceObjectProperty × Tokens) DataAxiomError}
    (run : ObjectsRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val prior tokens result) :
    read_objects table bytes tokens members limits = .ok result := by
  induction run generalizing members with
  | empty records =>
    have equal : members = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_objects.eq_def,equal]
  | stop close records =>
    have equal : members = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_objects.eq_def,equal]
    simp [closes_total_correct,close]
  | countLimit notClose full =>
    rw [read_objects.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,full]
  | @memberError prior token tail error notClose room member =>
    have notFull : ¬ limits.count.val ≤ prior.length := by omega
    rw [read_objects.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,notFull,
      (Rowl.FunctionalClasses.read_object_property_result_iff table bytes _ limits.iri _).mpr member]
  | @member prior token tail rest item result notClose room memberRun later ih =>
    have notFull : ¬ limits.count.val ≤ prior.length := by omega
    obtain ⟨appended,push,appendedContents⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.push_spec members _ (by rw [contents]; scalar_tac))
    have laterRead := ih appended (by rw [appendedContents,contents])
    rw [read_objects.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,notFull,
      (Rowl.FunctionalClasses.read_object_property_result_iff table bytes _ limits.iri _).mpr memberRun,push,laterRead]
theorem read_objects_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (members : alloc.vec.Vec SourceObjectProperty) (limits : ClassLimits)
    (result : core.result.Result (alloc.vec.Vec SourceObjectProperty × Tokens) DataAxiomError) :
    read_objects table bytes tokens members limits = .ok result ↔
      ObjectsRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val members.val tokens
        result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct,_⟩ := read_objects_total_correct table bytes tokens members limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · exact objects_execution table bytes limits members rfl

/-- At least two data properties: the maximal IRI sequence, then the
    two-member minimum, reported where the next member belongs. -/
inductive ListRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Tokens → core.result.Result (alloc.vec.Vec HeaderIri × Tokens) DataAxiomError → Prop
  | error {tokens : Tokens} {error : DataAxiomError}
      (run : IrisRun rows source eof count limit [] tokens (.Err error)) :
      ListRun rows source eof count limit tokens (.Err error)
  | short {tokens rest : Tokens} {members : alloc.vec.Vec HeaderIri}
      (run : IrisRun rows source eof count limit [] tokens (.Ok (members,rest))) (few : members.val.length < 2) :
      ListRun rows source eof count limit tokens (.Err (.Expected .Iri (Position eof rest)))
  | ok {tokens rest : Tokens} {members : alloc.vec.Vec HeaderIri}
      (run : IrisRun rows source eof count limit [] tokens (.Ok (members,rest))) (enough : 2 ≤ members.val.length) :
      ListRun rows source eof count limit tokens (.Ok (members,rest))

theorem read_list_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) :
    ∃ result, read_list table bytes tokens limits = .ok result ∧
      ListRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest ≤ TokenCount tokens := by
  obtain ⟨scanned,scanRead,scanCorrect,scanProgress⟩ :=
    read_iris_total_correct table bytes tokens (alloc.vec.Vec.new HeaderIri) limits
  rw [read_list]
  cases scanned with
  | Err error =>
    exact ⟨.Err error,by simp [scanRead],.error scanCorrect,by intro value rest impossible; cases impossible⟩
  | Ok pair =>
    obtain ⟨members,rest⟩ := pair
    by_cases few : members.val.length < 2
    · have few' : members.val.length ≤ 1 := by omega
      refine ⟨.Err (.Expected .Iri (Position bytes.len rest)),?_,.short scanCorrect few,
        by intro value rest' impossible; cases impossible⟩
      simp [scanRead,alloc.vec.Vec.len_val,few',offset_of_total_correct]
    · have many : ¬ members.val.length ≤ 1 := by omega
      refine ⟨.Ok (members,rest),?_,.ok scanCorrect (by omega),scanProgress⟩
      simp [scanRead,alloc.vec.Vec.len_val,many]
theorem read_list_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) (result : core.result.Result (alloc.vec.Vec HeaderIri × Tokens) DataAxiomError) :
    read_list table bytes tokens limits = .ok result ↔
      ListRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct,_⟩ := read_list_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_list]
    cases source with
    | error run => simp [iris_execution table bytes limits (alloc.vec.Vec.new HeaderIri) rfl run]
    | @short rest members run few =>
      have few' : members.val.length ≤ 1 := by omega
      simp [iris_execution table bytes limits (alloc.vec.Vec.new HeaderIri) rfl run,
        alloc.vec.Vec.len_val,few',offset_of_total_correct]
    | @ok rest members run enough =>
      have many : ¬ members.val.length ≤ 1 := by omega
      simp [iris_execution table bytes limits (alloc.vec.Vec.new HeaderIri) rfl run,alloc.vec.Vec.len_val,many]

/-- A class expression at an axiom position: the independent class grammar with
    the caller's class limits, its errors wrapped. -/
inductive ClassStep (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit depth : Nat) :
    Tokens → core.result.Result (SourceClass × Tokens) DataAxiomError → Prop
  | error {tokens : Tokens} {error : ClassError} (run : ClassRun rows source eof count limit depth tokens (.Err error)) :
      ClassStep rows source eof count limit depth tokens (.Err (.Class error))
  | ok {tokens rest : Tokens} {value : SourceClass}
      (run : ClassRun rows source eof count limit depth tokens (.Ok (value,rest))) :
      ClassStep rows source eof count limit depth tokens (.Ok (value,rest))

theorem read_class_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) :
    ∃ result, read_class table bytes tokens limits = .ok result ∧
      ClassStep table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val tokens
        result := by
  obtain ⟨result,executed,correct⟩ :=
    Rowl.FunctionalClasses.read_class_expression_total_correct table bytes tokens limits
  rw [read_class]
  cases result with
  | Err error => exact ⟨.Err (.Class error),by simp [executed],.error correct⟩
  | Ok pair => exact ⟨.Ok pair,by simp [executed],.ok correct⟩
theorem read_class_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) (result : core.result.Result (SourceClass × Tokens) DataAxiomError) :
    read_class table bytes tokens limits = .ok result ↔
      ClassStep table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val tokens
        result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_class_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_class]
    cases source with
    | error run => simp [(Rowl.FunctionalClasses.read_class_expression_result_iff table bytes tokens limits _).mpr run]
    | ok run => simp [(Rowl.FunctionalClasses.read_class_expression_result_iff table bytes tokens limits _).mpr run]
theorem class_step_progress {table : prefixes.PrefixTable} {bytes : alloc.vec.Vec U8} {limits : ClassLimits}
    {tokens rest : Tokens} {value : SourceClass}
    (step : ClassStep table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val
      tokens (.Ok (value,rest))) : TokenCount rest < TokenCount tokens := by
  cases step with
  | ok run =>
    have read := (Rowl.FunctionalClasses.read_class_expression_result_iff table bytes tokens limits _).mpr run
    rw [functional_classes.read_class_expression] at read
    exact Rowl.FunctionalClasses.class_progress read

/-- A data range at an axiom position: the independent data range grammar with
    the caller's class limits, its errors wrapped. -/
inductive RangeStep (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit depth : Nat) :
    Tokens → core.result.Result (SourceDataRange × Tokens) DataAxiomError → Prop
  | error {tokens : Tokens} {error : RangeError}
      (run : Rowl.FunctionalRanges.RangeRun rows source eof count limit depth tokens (.Err error)) :
      RangeStep rows source eof count limit depth tokens (.Err (.Range error))
  | ok {tokens rest : Tokens} {value : SourceDataRange}
      (run : Rowl.FunctionalRanges.RangeRun rows source eof count limit depth tokens (.Ok (value,rest))) :
      RangeStep rows source eof count limit depth tokens (.Ok (value,rest))

theorem read_range_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) :
    ∃ result, functional_data_axioms.read_range table bytes tokens limits = .ok result ∧
      RangeStep table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val tokens
        result := by
  obtain ⟨result,executed,correct,_⟩ :=
    Rowl.FunctionalRanges.read_data_range_total_correct table bytes tokens limits.depth limits.count limits.iri
  rw [functional_data_axioms.read_range]
  cases result with
  | Err error => exact ⟨.Err (.Range error),by simp [executed],.error correct⟩
  | Ok pair => exact ⟨.Ok pair,by simp [executed],.ok correct⟩
theorem read_range_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) (result : core.result.Result (SourceDataRange × Tokens) DataAxiomError) :
    functional_data_axioms.read_range table bytes tokens limits = .ok result ↔
      RangeStep table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val tokens
        result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_range_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [functional_data_axioms.read_range]
    cases source with
    | error run =>
      simp [(Rowl.FunctionalRanges.read_data_range_result_iff table bytes tokens limits.depth limits.count limits.iri
        _).mpr run]
    | ok run =>
      simp [(Rowl.FunctionalRanges.read_data_range_result_iff table bytes tokens limits.depth limits.count limits.iri
        _).mpr run]
theorem range_step_progress {table : prefixes.PrefixTable} {bytes : alloc.vec.Vec U8} {limits : ClassLimits}
    {tokens rest : Tokens} {value : SourceDataRange}
    (step : RangeStep table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val
      tokens (.Ok (value,rest))) : TokenCount rest < TokenCount tokens := by
  cases step with
  | ok run => exact Rowl.FunctionalRanges.range_progress run

/-- A parenthesized list of a key: `(`, the maximal member sequence, `)`. -/
inductive KeyObjectsRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Tokens → core.result.Result (alloc.vec.Vec SourceObjectProperty × Tokens) DataAxiomError → Prop
  | openError {tokens : Tokens} {error : DataAxiomError} (failure : TakeRun eof .Open tokens (.Err error)) :
      KeyObjectsRun rows source eof count limit tokens (.Err error)
  | membersError {tokens inner : Tokens} {opening : Token} {error : DataAxiomError}
      (opened : TakeRun eof .Open tokens (.Ok (opening,inner)))
      (failure : ObjectsRun rows source eof count limit [] inner (.Err error)) :
      KeyObjectsRun rows source eof count limit tokens (.Err error)
  | closeError {tokens inner rest : Tokens} {opening : Token} {members : alloc.vec.Vec SourceObjectProperty}
      {error : DataAxiomError}
      (opened : TakeRun eof .Open tokens (.Ok (opening,inner)))
      (membersRun : ObjectsRun rows source eof count limit [] inner (.Ok (members,rest)))
      (failure : TakeRun eof .Close rest (.Err error)) :
      KeyObjectsRun rows source eof count limit tokens (.Err error)
  | ok {tokens inner rest remaining : Tokens} {opening close : Token} {members : alloc.vec.Vec SourceObjectProperty}
      (opened : TakeRun eof .Open tokens (.Ok (opening,inner)))
      (membersRun : ObjectsRun rows source eof count limit [] inner (.Ok (members,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      KeyObjectsRun rows source eof count limit tokens (.Ok (members,remaining))
/-- The parenthesized data property list of a key. -/
inductive KeyDataRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Tokens → core.result.Result (alloc.vec.Vec HeaderIri × Tokens) DataAxiomError → Prop
  | openError {tokens : Tokens} {error : DataAxiomError} (failure : TakeRun eof .Open tokens (.Err error)) :
      KeyDataRun rows source eof count limit tokens (.Err error)
  | membersError {tokens inner : Tokens} {opening : Token} {error : DataAxiomError}
      (opened : TakeRun eof .Open tokens (.Ok (opening,inner)))
      (failure : IrisRun rows source eof count limit [] inner (.Err error)) :
      KeyDataRun rows source eof count limit tokens (.Err error)
  | closeError {tokens inner rest : Tokens} {opening : Token} {members : alloc.vec.Vec HeaderIri}
      {error : DataAxiomError}
      (opened : TakeRun eof .Open tokens (.Ok (opening,inner)))
      (membersRun : IrisRun rows source eof count limit [] inner (.Ok (members,rest)))
      (failure : TakeRun eof .Close rest (.Err error)) :
      KeyDataRun rows source eof count limit tokens (.Err error)
  | ok {tokens inner rest remaining : Tokens} {opening close : Token} {members : alloc.vec.Vec HeaderIri}
      (opened : TakeRun eof .Open tokens (.Ok (opening,inner)))
      (membersRun : IrisRun rows source eof count limit [] inner (.Ok (members,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      KeyDataRun rows source eof count limit tokens (.Ok (members,remaining))

theorem read_key_objects_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) :
    ∃ result, read_key_objects table bytes tokens limits = .ok result ∧
      KeyObjectsRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val tokens result := by
  rw [read_key_objects]
  obtain ⟨opened,openRead,openCorrect⟩ := take_expected_total_correct tokens .Open bytes.len
  cases opened with
  | Err error => exact ⟨.Err error,by simp [openRead],.openError openCorrect⟩
  | Ok pair =>
    obtain ⟨opening,inner⟩ := pair
    obtain ⟨members,membersRead,membersCorrect,_⟩ :=
      read_objects_total_correct table bytes inner (alloc.vec.Vec.new SourceObjectProperty) limits
    have start : (alloc.vec.Vec.new SourceObjectProperty).val = [] := rfl
    rw [start] at membersCorrect
    cases members with
    | Err error => exact ⟨.Err error,by simp [openRead,membersRead],.membersError openCorrect membersCorrect⟩
    | Ok pair =>
      obtain ⟨members,rest⟩ := pair
      obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
      cases closed with
      | Err error =>
        exact ⟨.Err error,by simp [openRead,membersRead,closeRead],.closeError openCorrect membersCorrect closeCorrect⟩
      | Ok pair =>
        obtain ⟨close,remaining⟩ := pair
        exact ⟨.Ok (members,remaining),by simp [openRead,membersRead,closeRead],
          .ok openCorrect membersCorrect closeCorrect⟩
theorem read_key_objects_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) (result : core.result.Result (alloc.vec.Vec SourceObjectProperty × Tokens) DataAxiomError) :
    read_key_objects table bytes tokens limits = .ok result ↔
      KeyObjectsRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_key_objects_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_key_objects]
    cases source with
    | openError failure => simp [(take_expected_result_iff _ .Open bytes.len _).mpr failure]
    | membersError opened failure =>
      simp [(take_expected_result_iff _ .Open bytes.len _).mpr opened,
        objects_execution table bytes limits (alloc.vec.Vec.new SourceObjectProperty) rfl failure]
    | closeError opened membersRun failure =>
      simp [(take_expected_result_iff _ .Open bytes.len _).mpr opened,
        objects_execution table bytes limits (alloc.vec.Vec.new SourceObjectProperty) rfl membersRun,
        (take_expected_result_iff _ .Close bytes.len _).mpr failure]
    | ok opened membersRun closing =>
      simp [(take_expected_result_iff _ .Open bytes.len _).mpr opened,
        objects_execution table bytes limits (alloc.vec.Vec.new SourceObjectProperty) rfl membersRun,
        (take_expected_result_iff _ .Close bytes.len _).mpr closing]
theorem read_key_data_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) :
    ∃ result, read_key_data table bytes tokens limits = .ok result ∧
      KeyDataRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val tokens result := by
  rw [read_key_data]
  obtain ⟨opened,openRead,openCorrect⟩ := take_expected_total_correct tokens .Open bytes.len
  cases opened with
  | Err error => exact ⟨.Err error,by simp [openRead],.openError openCorrect⟩
  | Ok pair =>
    obtain ⟨opening,inner⟩ := pair
    obtain ⟨members,membersRead,membersCorrect,_⟩ :=
      read_iris_total_correct table bytes inner (alloc.vec.Vec.new HeaderIri) limits
    have start : (alloc.vec.Vec.new HeaderIri).val = [] := rfl
    rw [start] at membersCorrect
    cases members with
    | Err error => exact ⟨.Err error,by simp [openRead,membersRead],.membersError openCorrect membersCorrect⟩
    | Ok pair =>
      obtain ⟨members,rest⟩ := pair
      obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
      cases closed with
      | Err error =>
        exact ⟨.Err error,by simp [openRead,membersRead,closeRead],.closeError openCorrect membersCorrect closeCorrect⟩
      | Ok pair =>
        obtain ⟨close,remaining⟩ := pair
        exact ⟨.Ok (members,remaining),by simp [openRead,membersRead,closeRead],
          .ok openCorrect membersCorrect closeCorrect⟩
theorem read_key_data_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) (result : core.result.Result (alloc.vec.Vec HeaderIri × Tokens) DataAxiomError) :
    read_key_data table bytes tokens limits = .ok result ↔
      KeyDataRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_key_data_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_key_data]
    cases source with
    | openError failure => simp [(take_expected_result_iff _ .Open bytes.len _).mpr failure]
    | membersError opened failure =>
      simp [(take_expected_result_iff _ .Open bytes.len _).mpr opened,
        iris_execution table bytes limits (alloc.vec.Vec.new HeaderIri) rfl failure]
    | closeError opened membersRun failure =>
      simp [(take_expected_result_iff _ .Open bytes.len _).mpr opened,
        iris_execution table bytes limits (alloc.vec.Vec.new HeaderIri) rfl membersRun,
        (take_expected_result_iff _ .Close bytes.len _).mpr failure]
    | ok opened membersRun closing =>
      simp [(take_expected_result_iff _ .Open bytes.len _).mpr opened,
        iris_execution table bytes limits (alloc.vec.Vec.new HeaderIri) rfl membersRun,
        (take_expected_result_iff _ .Close bytes.len _).mpr closing]

/-- Independent data axiom bodies after the axiom annotations, in source order. -/
inductive BodyRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit depth : Nat) :
    AxiomForm → Tokens → core.result.Result (SourceDataAxiomBody × Tokens) DataAxiomError → Prop
  | subError {tokens : Tokens} {error : DataAxiomError} (failure : IriRun rows source eof limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .Sub tokens (.Err error)
  | supError {tokens rest : Tokens} {sub : HeaderIri} {error : DataAxiomError}
      (subRun : IriRun rows source eof limit tokens (.Ok (sub,rest)))
      (failure : IriRun rows source eof limit rest (.Err error)) :
      BodyRun rows source eof count limit depth .Sub tokens (.Err error)
  | sub {tokens rest remaining : Tokens} {sub sup : HeaderIri}
      (subRun : IriRun rows source eof limit tokens (.Ok (sub,rest)))
      (supRun : IriRun rows source eof limit rest (.Ok (sup,remaining))) :
      BodyRun rows source eof count limit depth .Sub tokens (.Ok (.SubDataPropertyOf sub sup,remaining))
  | equivalentError {tokens : Tokens} {error : DataAxiomError}
      (listRun : ListRun rows source eof count limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .Equivalent tokens (.Err error)
  | equivalent {tokens remaining : Tokens} {members : alloc.vec.Vec HeaderIri}
      (listRun : ListRun rows source eof count limit tokens (.Ok (members,remaining))) :
      BodyRun rows source eof count limit depth .Equivalent tokens (.Ok (.EquivalentDataProperties members,remaining))
  | disjointError {tokens : Tokens} {error : DataAxiomError}
      (listRun : ListRun rows source eof count limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .Disjoint tokens (.Err error)
  | disjoint {tokens remaining : Tokens} {members : alloc.vec.Vec HeaderIri}
      (listRun : ListRun rows source eof count limit tokens (.Ok (members,remaining))) :
      BodyRun rows source eof count limit depth .Disjoint tokens (.Ok (.DisjointDataProperties members,remaining))
  | domainPropertyError {tokens : Tokens} {error : DataAxiomError}
      (failure : IriRun rows source eof limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .Domain tokens (.Err error)
  | domainError {tokens rest : Tokens} {property : HeaderIri} {error : DataAxiomError}
      (propertyRun : IriRun rows source eof limit tokens (.Ok (property,rest)))
      (failure : ClassStep rows source eof count limit depth rest (.Err error)) :
      BodyRun rows source eof count limit depth .Domain tokens (.Err error)
  | domain {tokens rest remaining : Tokens} {property : HeaderIri} {domain : SourceClass}
      (propertyRun : IriRun rows source eof limit tokens (.Ok (property,rest)))
      (domainRun : ClassStep rows source eof count limit depth rest (.Ok (domain,remaining))) :
      BodyRun rows source eof count limit depth .Domain tokens (.Ok (.DataPropertyDomain property domain,remaining))
  | rangePropertyError {tokens : Tokens} {error : DataAxiomError}
      (failure : IriRun rows source eof limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .Range tokens (.Err error)
  | rangeError {tokens rest : Tokens} {property : HeaderIri} {error : DataAxiomError}
      (propertyRun : IriRun rows source eof limit tokens (.Ok (property,rest)))
      (failure : RangeStep rows source eof count limit depth rest (.Err error)) :
      BodyRun rows source eof count limit depth .Range tokens (.Err error)
  | range {tokens rest remaining : Tokens} {property : HeaderIri} {range : SourceDataRange}
      (propertyRun : IriRun rows source eof limit tokens (.Ok (property,rest)))
      (rangeRun : RangeStep rows source eof count limit depth rest (.Ok (range,remaining))) :
      BodyRun rows source eof count limit depth .Range tokens (.Ok (.DataPropertyRange property range,remaining))
  | functionalError {tokens : Tokens} {error : DataAxiomError}
      (failure : IriRun rows source eof limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .Functional tokens (.Err error)
  | functional {tokens remaining : Tokens} {property : HeaderIri}
      (run : IriRun rows source eof limit tokens (.Ok (property,remaining))) :
      BodyRun rows source eof count limit depth .Functional tokens (.Ok (.FunctionalDataProperty property,remaining))
  | definitionDatatypeError {tokens : Tokens} {error : DataAxiomError}
      (failure : IriRun rows source eof limit tokens (.Err error)) :
      BodyRun rows source eof count limit depth .Definition tokens (.Err error)
  | definitionRangeError {tokens rest : Tokens} {datatype : HeaderIri} {error : DataAxiomError}
      (datatypeRun : IriRun rows source eof limit tokens (.Ok (datatype,rest)))
      (failure : RangeStep rows source eof count limit depth rest (.Err error)) :
      BodyRun rows source eof count limit depth .Definition tokens (.Err error)
  | definition {tokens rest remaining : Tokens} {datatype : HeaderIri} {range : SourceDataRange}
      (datatypeRun : IriRun rows source eof limit tokens (.Ok (datatype,rest)))
      (rangeRun : RangeStep rows source eof count limit depth rest (.Ok (range,remaining))) :
      BodyRun rows source eof count limit depth .Definition tokens (.Ok (.DatatypeDefinition datatype range,remaining))
  | keyClassError {tokens : Tokens} {error : DataAxiomError}
      (failure : ClassStep rows source eof count limit depth tokens (.Err error)) :
      BodyRun rows source eof count limit depth .Key tokens (.Err error)
  | keyObjectsError {tokens rest : Tokens} {expression : SourceClass} {error : DataAxiomError}
      (classRun : ClassStep rows source eof count limit depth tokens (.Ok (expression,rest)))
      (failure : KeyObjectsRun rows source eof count limit rest (.Err error)) :
      BodyRun rows source eof count limit depth .Key tokens (.Err error)
  | keyDataError {tokens rest after : Tokens} {expression : SourceClass} {objects : alloc.vec.Vec SourceObjectProperty}
      {error : DataAxiomError}
      (classRun : ClassStep rows source eof count limit depth tokens (.Ok (expression,rest)))
      (objectsRun : KeyObjectsRun rows source eof count limit rest (.Ok (objects,after)))
      (failure : KeyDataRun rows source eof count limit after (.Err error)) :
      BodyRun rows source eof count limit depth .Key tokens (.Err error)
  | key {tokens rest after remaining : Tokens} {expression : SourceClass} {objects : alloc.vec.Vec SourceObjectProperty}
      {data : alloc.vec.Vec HeaderIri}
      (classRun : ClassStep rows source eof count limit depth tokens (.Ok (expression,rest)))
      (objectsRun : KeyObjectsRun rows source eof count limit rest (.Ok (objects,after)))
      (dataRun : KeyDataRun rows source eof count limit after (.Ok (data,remaining))) :
      BodyRun rows source eof count limit depth .Key tokens (.Ok (.HasKey expression objects data,remaining))

/-- The actual body reader terminates and follows the independent grammar. -/
theorem read_body_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (form : AxiomForm)
    (tokens : Tokens) (limits : ClassLimits) :
    ∃ result, functional_data_axioms.read_body table bytes form tokens limits = .ok result ∧
      BodyRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val form tokens
        result := by
  rw [functional_data_axioms.read_body.eq_def]
  cases form with
  | Sub =>
    obtain ⟨sub,subRead,subCorrect⟩ := read_iri_total_correct table bytes tokens limits.iri
    cases sub with
    | Err error => exact ⟨.Err error,by simp [subRead],.subError subCorrect⟩
    | Ok pair =>
      obtain ⟨sub,rest⟩ := pair
      obtain ⟨sup,supRead,supCorrect⟩ := read_iri_total_correct table bytes rest limits.iri
      cases sup with
      | Err error => exact ⟨.Err error,by simp [subRead,supRead],.supError subCorrect supCorrect⟩
      | Ok pair =>
        obtain ⟨sup,remaining⟩ := pair
        exact ⟨.Ok (.SubDataPropertyOf sub sup,remaining),by simp [subRead,supRead],.sub subCorrect supCorrect⟩
  | Equivalent =>
    obtain ⟨listed,listRead,listCorrect,_⟩ := read_list_total_correct table bytes tokens limits
    cases listed with
    | Err error => exact ⟨.Err error,by simp [listRead],.equivalentError listCorrect⟩
    | Ok pair =>
      obtain ⟨members,remaining⟩ := pair
      exact ⟨.Ok (.EquivalentDataProperties members,remaining),by simp [listRead],.equivalent listCorrect⟩
  | Disjoint =>
    obtain ⟨listed,listRead,listCorrect,_⟩ := read_list_total_correct table bytes tokens limits
    cases listed with
    | Err error => exact ⟨.Err error,by simp [listRead],.disjointError listCorrect⟩
    | Ok pair =>
      obtain ⟨members,remaining⟩ := pair
      exact ⟨.Ok (.DisjointDataProperties members,remaining),by simp [listRead],.disjoint listCorrect⟩
  | Domain =>
    obtain ⟨property,propertyRead,propertyCorrect⟩ := read_iri_total_correct table bytes tokens limits.iri
    cases property with
    | Err error => exact ⟨.Err error,by simp [propertyRead],.domainPropertyError propertyCorrect⟩
    | Ok pair =>
      obtain ⟨property,rest⟩ := pair
      obtain ⟨domain,domainRead,domainCorrect⟩ := read_class_total_correct table bytes rest limits
      cases domain with
      | Err error => exact ⟨.Err error,by simp [propertyRead,domainRead],.domainError propertyCorrect domainCorrect⟩
      | Ok pair =>
        obtain ⟨domain,remaining⟩ := pair
        exact ⟨.Ok (.DataPropertyDomain property domain,remaining),by simp [propertyRead,domainRead],
          .domain propertyCorrect domainCorrect⟩
  | Range =>
    obtain ⟨property,propertyRead,propertyCorrect⟩ := read_iri_total_correct table bytes tokens limits.iri
    cases property with
    | Err error => exact ⟨.Err error,by simp [propertyRead],.rangePropertyError propertyCorrect⟩
    | Ok pair =>
      obtain ⟨property,rest⟩ := pair
      obtain ⟨range,rangeRead,rangeCorrect⟩ := read_range_total_correct table bytes rest limits
      cases range with
      | Err error => exact ⟨.Err error,by simp [propertyRead,rangeRead],.rangeError propertyCorrect rangeCorrect⟩
      | Ok pair =>
        obtain ⟨range,remaining⟩ := pair
        exact ⟨.Ok (.DataPropertyRange property range,remaining),by simp [propertyRead,rangeRead],
          .range propertyCorrect rangeCorrect⟩
  | Functional =>
    obtain ⟨property,propertyRead,propertyCorrect⟩ := read_iri_total_correct table bytes tokens limits.iri
    cases property with
    | Err error => exact ⟨.Err error,by simp [propertyRead],.functionalError propertyCorrect⟩
    | Ok pair =>
      obtain ⟨property,remaining⟩ := pair
      exact ⟨.Ok (.FunctionalDataProperty property,remaining),by simp [propertyRead],.functional propertyCorrect⟩
  | Definition =>
    obtain ⟨datatype,datatypeRead,datatypeCorrect⟩ := read_iri_total_correct table bytes tokens limits.iri
    cases datatype with
    | Err error => exact ⟨.Err error,by simp [datatypeRead],.definitionDatatypeError datatypeCorrect⟩
    | Ok pair =>
      obtain ⟨datatype,rest⟩ := pair
      obtain ⟨range,rangeRead,rangeCorrect⟩ := read_range_total_correct table bytes rest limits
      cases range with
      | Err error =>
        exact ⟨.Err error,by simp [datatypeRead,rangeRead],.definitionRangeError datatypeCorrect rangeCorrect⟩
      | Ok pair =>
        obtain ⟨range,remaining⟩ := pair
        exact ⟨.Ok (.DatatypeDefinition datatype range,remaining),by simp [datatypeRead,rangeRead],
          .definition datatypeCorrect rangeCorrect⟩
  | Key =>
    obtain ⟨expression,classRead,classCorrect⟩ := read_class_total_correct table bytes tokens limits
    cases expression with
    | Err error => exact ⟨.Err error,by simp [classRead],.keyClassError classCorrect⟩
    | Ok pair =>
      obtain ⟨expression,rest⟩ := pair
      obtain ⟨objects,objectsRead,objectsCorrect⟩ := read_key_objects_total_correct table bytes rest limits
      cases objects with
      | Err error => exact ⟨.Err error,by simp [classRead,objectsRead],.keyObjectsError classCorrect objectsCorrect⟩
      | Ok pair =>
        obtain ⟨objects,after⟩ := pair
        obtain ⟨data,dataRead,dataCorrect⟩ := read_key_data_total_correct table bytes after limits
        cases data with
        | Err error =>
          exact ⟨.Err error,by simp [classRead,objectsRead,dataRead],
            .keyDataError classCorrect objectsCorrect dataCorrect⟩
        | Ok pair =>
          obtain ⟨data,remaining⟩ := pair
          exact ⟨.Ok (.HasKey expression objects data,remaining),by simp [classRead,objectsRead,dataRead],
            .key classCorrect objectsCorrect dataCorrect⟩
/-- Every exact body and first error is equivalent to its independent derivation. -/
theorem read_body_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (form : AxiomForm)
    (tokens : Tokens) (limits : ClassLimits)
    (result : core.result.Result (SourceDataAxiomBody × Tokens) DataAxiomError) :
    functional_data_axioms.read_body table bytes form tokens limits = .ok result ↔
      BodyRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.depth.val form tokens
        result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_body_total_correct table bytes form tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [functional_data_axioms.read_body.eq_def]
    cases source with
    | subError failure => simp [(read_iri_result_iff table bytes _ limits.iri _).mpr failure]
    | supError subRun failure =>
      simp [(read_iri_result_iff table bytes _ limits.iri _).mpr subRun,
        (read_iri_result_iff table bytes _ limits.iri _).mpr failure]
    | sub subRun supRun =>
      simp [(read_iri_result_iff table bytes _ limits.iri _).mpr subRun,
        (read_iri_result_iff table bytes _ limits.iri _).mpr supRun]
    | equivalentError listRun => simp [(read_list_result_iff table bytes _ limits _).mpr listRun]
    | equivalent listRun => simp [(read_list_result_iff table bytes _ limits _).mpr listRun]
    | disjointError listRun => simp [(read_list_result_iff table bytes _ limits _).mpr listRun]
    | disjoint listRun => simp [(read_list_result_iff table bytes _ limits _).mpr listRun]
    | domainPropertyError failure => simp [(read_iri_result_iff table bytes _ limits.iri _).mpr failure]
    | domainError propertyRun failure =>
      simp [(read_iri_result_iff table bytes _ limits.iri _).mpr propertyRun,
        (read_class_result_iff table bytes _ limits _).mpr failure]
    | domain propertyRun domainRun =>
      simp [(read_iri_result_iff table bytes _ limits.iri _).mpr propertyRun,
        (read_class_result_iff table bytes _ limits _).mpr domainRun]
    | rangePropertyError failure => simp [(read_iri_result_iff table bytes _ limits.iri _).mpr failure]
    | rangeError propertyRun failure =>
      simp [(read_iri_result_iff table bytes _ limits.iri _).mpr propertyRun,
        (read_range_result_iff table bytes _ limits _).mpr failure]
    | range propertyRun rangeRun =>
      simp [(read_iri_result_iff table bytes _ limits.iri _).mpr propertyRun,
        (read_range_result_iff table bytes _ limits _).mpr rangeRun]
    | functionalError failure => simp [(read_iri_result_iff table bytes _ limits.iri _).mpr failure]
    | functional run => simp [(read_iri_result_iff table bytes _ limits.iri _).mpr run]
    | definitionDatatypeError failure => simp [(read_iri_result_iff table bytes _ limits.iri _).mpr failure]
    | definitionRangeError datatypeRun failure =>
      simp [(read_iri_result_iff table bytes _ limits.iri _).mpr datatypeRun,
        (read_range_result_iff table bytes _ limits _).mpr failure]
    | definition datatypeRun rangeRun =>
      simp [(read_iri_result_iff table bytes _ limits.iri _).mpr datatypeRun,
        (read_range_result_iff table bytes _ limits _).mpr rangeRun]
    | keyClassError failure => simp [(read_class_result_iff table bytes _ limits _).mpr failure]
    | keyObjectsError classRun failure =>
      simp [(read_class_result_iff table bytes _ limits _).mpr classRun,
        (read_key_objects_result_iff table bytes _ limits _).mpr failure]
    | keyDataError classRun objectsRun failure =>
      simp [(read_class_result_iff table bytes _ limits _).mpr classRun,
        (read_key_objects_result_iff table bytes _ limits _).mpr objectsRun,
        (read_key_data_result_iff table bytes _ limits _).mpr failure]
    | key classRun objectsRun dataRun =>
      simp [(read_class_result_iff table bytes _ limits _).mpr classRun,
        (read_key_objects_result_iff table bytes _ limits _).mpr objectsRun,
        (read_key_data_result_iff table bytes _ limits _).mpr dataRun]

/-- Independent data axiom grammar in source order: one of the eight keywords,
    `(`, the maximal axiom-annotation sequence (the independent annotation
    grammar with the caller's annotation limits), the body with the caller's
    class limits, then `)`. -/
inductive AxiomRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize)
    (annotationCount annotationIri annotationLexical annotationDepth classCount classIri classDepth : Nat) :
    Tokens → core.result.Result (SourceDataAxiom × Tokens) DataAxiomError → Prop
  | keywordError {tokens : Tokens} {error : DataAxiomError} (failure : TakeRun eof .Axiom tokens (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth tokens (.Err error)
  | openError {keyword : Token} {tail : Tokens} {form : AxiomForm} {error : DataAxiomError}
      (formOf : FormOf keyword.terminal = some form) (failure : TakeRun eof .Open tail (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Err error)
  | annotationError {keyword opening : Token} {tail inner : Tokens} {form : AxiomForm}
      {error : functional_annotations.AnnotationError}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (failure : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Err (.Annotation error))
  | bodyError {keyword opening : Token} {tail inner : Tokens} {form : AxiomForm} {annotations : SourceAnnotations}
      {error : DataAxiomError}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Ok annotations))
      (failure : BodyRun rows source eof classCount classIri classDepth form annotations.remaining (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Err error)
  | closeError {keyword opening : Token} {tail inner rest : Tokens} {form : AxiomForm}
      {annotations : SourceAnnotations} {body : SourceDataAxiomBody} {error : DataAxiomError}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Ok annotations))
      (bodyRun : BodyRun rows source eof classCount classIri classDepth form annotations.remaining (.Ok (body,rest)))
      (failure : TakeRun eof .Close rest (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Err error)
  | ready {keyword opening close : Token} {tail inner rest remaining : Tokens} {form : AxiomForm}
      {annotations : SourceAnnotations} {body : SourceDataAxiomBody}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Ok annotations))
      (bodyRun : BodyRun rows source eof classCount classIri classDepth form annotations.remaining (.Ok (body,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth (.Cons keyword tail) (.Ok (⟨keyword,annotations.annotations,body⟩,remaining))

/-- The actual data axiom reader terminates on every token stream and follows
    the independent grammar. -/
theorem read_data_axiom_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (annotations : AnnotationLimits) (classes : ClassLimits) :
    ∃ result, read_data_axiom table bytes tokens annotations classes = .ok result ∧
      AxiomRun table.declarations.val bytes.val bytes.len annotations.count.val annotations.iri.val
        annotations.lexical.val annotations.depth.val classes.count.val classes.iri.val classes.depth.val tokens
        result := by
  obtain ⟨first,firstRead,firstCorrect⟩ := take_expected_total_correct tokens .Axiom bytes.len
  rw [read_data_axiom]
  cases first with
  | Err error => exact ⟨.Err error,by simp [firstRead],.keywordError firstCorrect⟩
  | Ok pair =>
    obtain ⟨keyword,tail⟩ := pair
    cases firstCorrect with
    | taken _ _ accepted =>
      obtain ⟨form,formOf⟩ := accepted
      obtain ⟨opened,openRead,openCorrect⟩ := take_expected_total_correct tail .Open bytes.len
      cases opened with
      | Err error =>
        exact ⟨.Err error,by simp [firstRead,axiom_form_total_correct,formOf,openRead],.openError formOf openCorrect⟩
      | Ok pair =>
        obtain ⟨opening,inner⟩ := pair
        obtain ⟨annotated,annotatedRead,annotatedCorrect⟩ :=
          Rowl.FunctionalAnnotations.read_annotations_total_correct table bytes inner annotations
        cases annotated with
        | Err error =>
          exact ⟨.Err (.Annotation error),by simp [firstRead,axiom_form_total_correct,formOf,openRead,
            annotatedRead],.annotationError formOf openCorrect annotatedCorrect⟩
        | Ok sequence =>
          obtain ⟨body,bodyRead,bodyCorrect⟩ := read_body_total_correct table bytes form sequence.remaining classes
          cases body with
          | Err error =>
            exact ⟨.Err error,by simp [firstRead,axiom_form_total_correct,formOf,openRead,annotatedRead,bodyRead],
              .bodyError formOf openCorrect annotatedCorrect bodyCorrect⟩
          | Ok pair =>
            obtain ⟨body,rest⟩ := pair
            obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
            cases closed with
            | Err error =>
              exact ⟨.Err error,by simp [firstRead,axiom_form_total_correct,formOf,openRead,annotatedRead,
                bodyRead,closeRead],.closeError formOf openCorrect annotatedCorrect bodyCorrect closeCorrect⟩
            | Ok pair =>
              obtain ⟨close,remaining⟩ := pair
              exact ⟨.Ok (⟨keyword,sequence.annotations,body⟩,remaining),
                by simp [firstRead,axiom_form_total_correct,formOf,openRead,annotatedRead,bodyRead,closeRead],
                .ready formOf openCorrect annotatedCorrect bodyCorrect closeCorrect⟩
/-- Every exact data axiom and first error is equivalent to its independent
    derivation. -/
theorem read_data_axiom_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (annotations : AnnotationLimits) (classes : ClassLimits)
    (result : core.result.Result (SourceDataAxiom × Tokens) DataAxiomError) :
    read_data_axiom table bytes tokens annotations classes = .ok result ↔
      AxiomRun table.declarations.val bytes.val bytes.len annotations.count.val annotations.iri.val
        annotations.lexical.val annotations.depth.val classes.count.val classes.iri.val classes.depth.val tokens
        result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_data_axiom_total_correct table bytes tokens annotations classes
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_data_axiom]
    cases source with
    | keywordError failure => simp [(take_expected_result_iff tokens .Axiom bytes.len _).mpr failure]
    | @openError keyword tail form error formOf failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,axiom_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr failure]
    | @annotationError keyword opening tail inner form error formOf opened failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,axiom_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr opened,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner annotations _).mpr failure]
    | @bodyError keyword opening tail inner form sequence error formOf opened annotated failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,axiom_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr opened,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner annotations _).mpr annotated,
        (read_body_result_iff table bytes form _ classes _).mpr failure]
    | @closeError keyword opening tail inner rest form sequence body error formOf opened annotated bodyRun failure =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,axiom_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr opened,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner annotations _).mpr annotated,
        (read_body_result_iff table bytes form _ classes _).mpr bodyRun,
        (take_expected_result_iff rest .Close bytes.len _).mpr failure]
    | @ready keyword opening close tail inner rest remaining form sequence body formOf opened annotated bodyRun closing =>
      have firstRead := (take_expected_result_iff (.Cons keyword tail) .Axiom bytes.len (.Ok (keyword,tail))).mpr
        (.taken keyword tail ⟨form,formOf⟩)
      simp [firstRead,axiom_form_total_correct,formOf,(take_expected_result_iff tail .Open bytes.len _).mpr opened,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes inner annotations _).mpr annotated,
        (read_body_result_iff table bytes form _ classes _).mpr bodyRun,
        (take_expected_result_iff rest .Close bytes.len _).mpr closing]

/-- A successful data axiom consumes at least its keyword and its closing
    parenthesis, so an axiom loop always makes progress. -/
theorem data_axiom_progress (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens rest : Tokens)
    (annotations : AnnotationLimits) (classes : ClassLimits) (record : SourceDataAxiom)
    (accepted : read_data_axiom table bytes tokens annotations classes = .ok (.Ok (record,rest))) :
    TokenCount rest+2 ≤ TokenCount tokens := by
  have run := (read_data_axiom_result_iff table bytes tokens annotations classes _).mp accepted
  have irisStep : ∀ {start after : Tokens} {prior : alloc.vec.Vec HeaderIri} {members : alloc.vec.Vec HeaderIri},
      IrisRun table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val prior.val start
        (.Ok (members,after)) → TokenCount after ≤ TokenCount start := by
    intro start after prior members step
    have read := (read_iris_result_iff table bytes start prior classes _).mpr step
    obtain ⟨actual,executed,_,progress⟩ := read_iris_total_correct table bytes start prior classes
    rw [read] at executed
    exact progress members after (Result.ok_injective executed).symm
  have listStep : ∀ {start after : Tokens} {members : alloc.vec.Vec HeaderIri},
      ListRun table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val start
        (.Ok (members,after)) → TokenCount after ≤ TokenCount start := by
    intro start after members step
    have read := (read_list_result_iff table bytes start classes _).mpr step
    obtain ⟨actual,executed,_,progress⟩ := read_list_total_correct table bytes start classes
    rw [read] at executed
    exact progress members after (Result.ok_injective executed).symm
  have objectsStep : ∀ {start after : Tokens} {members : alloc.vec.Vec SourceObjectProperty},
      KeyObjectsRun table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val start
        (.Ok (members,after)) → TokenCount after < TokenCount start := by
    intro start after members step
    generalize outputEq : core.result.Result.Ok (members,after) = output at step
    cases step with
    | ok opened membersRun closing =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := take_progress opened
      have read := objects_execution table bytes classes (alloc.vec.Vec.new SourceObjectProperty) rfl membersRun
      obtain ⟨actual,executed,_,progress⟩ :=
        read_objects_total_correct table bytes _ (alloc.vec.Vec.new SourceObjectProperty) classes
      rw [read] at executed
      have two := progress _ _ (Result.ok_injective executed).symm
      have three := take_progress closing
      omega
    | openError | membersError | closeError => cases outputEq
  have dataStep : ∀ {start after : Tokens} {members : alloc.vec.Vec HeaderIri},
      KeyDataRun table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val start
        (.Ok (members,after)) → TokenCount after < TokenCount start := by
    intro start after members step
    generalize outputEq : core.result.Result.Ok (members,after) = output at step
    cases step with
    | ok opened membersRun closing =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := take_progress opened
      have two := irisStep (prior := alloc.vec.Vec.new HeaderIri) membersRun
      have three := take_progress closing
      omega
    | openError | membersError | closeError => cases outputEq
  have bodyStep : ∀ {form : AxiomForm} {start after : Tokens} {body : SourceDataAxiomBody},
      BodyRun table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val classes.depth.val form start
        (.Ok (body,after)) → TokenCount after ≤ TokenCount start := by
    intro form start after body step
    generalize outputEq : core.result.Result.Ok (body,after) = output at step
    cases step with
    | sub subRun supRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := iri_progress subRun
      have two := iri_progress supRun
      omega
    | equivalent listRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      exact listStep listRun
    | disjoint listRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      exact listStep listRun
    | domain propertyRun domainRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := iri_progress propertyRun
      have two := class_step_progress domainRun
      omega
    | range propertyRun rangeRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := iri_progress propertyRun
      have two := range_step_progress rangeRun
      omega
    | functional run =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have := iri_progress run
      omega
    | definition datatypeRun rangeRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := iri_progress datatypeRun
      have two := range_step_progress rangeRun
      omega
    | key classRun objectsRun dataRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := class_step_progress classRun
      have two := objectsStep objectsRun
      have three := dataStep dataRun
      omega
    | subError | supError | equivalentError | disjointError | domainPropertyError | domainError | rangePropertyError
      | rangeError | functionalError | definitionDatatypeError | definitionRangeError | keyClassError
      | keyObjectsError | keyDataError => cases outputEq
  generalize outputEq : core.result.Result.Ok (record,rest) = output at run
  cases run with
  | keywordError | openError | annotationError | bodyError | closeError => cases outputEq
  | ready formOf opened annotated bodyRun closing =>
    injection outputEq with same
    injection same with _ restSame
    subst restSame
    have one := take_progress opened
    have two := Rowl.FunctionalAnnotations.scan_remaining_le annotated _ rfl
    have three := bodyStep bodyRun
    have four := take_progress closing
    simp only [TokenCount] at *
    omega
end Rowl.FunctionalDataAxioms
