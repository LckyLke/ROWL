import Rowl.FunctionalClasses
import Rowl.FunctionalAnnotations

/-!
Functional Syntax object property axioms (`SubObjectPropertyOf` with a property
or a property chain on the left, `EquivalentObjectProperties`,
`DisjointObjectProperties`, `InverseObjectProperties` and the seven property
characteristics), proved total and exact against an independent grammar that
composes the proved annotation and object-property grammars with independent
member-list and chain grammars. Every result and first error has its
independent derivation, and every derivation is the actual result.
-/
namespace Rowl.FunctionalPropertyAxioms
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional_property_axioms
open RowlRust.functional_classes (ClassError ClassLimits SourceObjectProperty)
open RowlRust.functional_annotations (AnnotationLimits SourceAnnotations)
open RowlRust.functional_lexer RowlRust.functional
open Rowl.FunctionalLexer (TokenCount)
open Rowl.FunctionalClasses (PropertyRun Position offset_of_total_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The eleven object property axiom keywords this stage reads. -/
def FormOf : Terminal → Option AxiomForm
  | .Keyword .SubObjectPropertyOf => some .SubObjectPropertyOf
  | .Keyword .EquivalentObjectProperties => some .EquivalentObjectProperties
  | .Keyword .DisjointObjectProperties => some .DisjointObjectProperties
  | .Keyword .InverseObjectProperties => some .InverseObjectProperties
  | .Keyword .FunctionalObjectProperty => some (.Characteristic .Functional)
  | .Keyword .InverseFunctionalObjectProperty => some (.Characteristic .InverseFunctional)
  | .Keyword .ReflexiveObjectProperty => some (.Characteristic .Reflexive)
  | .Keyword .IrreflexiveObjectProperty => some (.Characteristic .Irreflexive)
  | .Keyword .SymmetricObjectProperty => some (.Characteristic .Symmetric)
  | .Keyword .AsymmetricObjectProperty => some (.Characteristic .Asymmetric)
  | .Keyword .TransitiveObjectProperty => some (.Characteristic .Transitive)
  | _ => none
/-- Independent first-terminal class required at each axiom position; the
    `Property` class only names the position of a missing list member. -/
def Expected : PropertyAxiomExpected → Terminal → Prop
  | .Axiom, terminal => ∃ form, FormOf terminal = some form
  | .Open, terminal => terminal = .Open
  | .Property, _ => False
  | .Close, terminal => terminal = .Close
/-- The tokens start with the `ObjectPropertyChain` keyword. -/
def StartsChain : Tokens → Prop
  | .Cons token _ => token.terminal = .Keyword .ObjectPropertyChain
  | .Empty => False

theorem axiom_form_total_correct (terminal : Terminal) : axiom_form terminal = .ok (FormOf terminal) := by
  cases terminal <;> first | rfl | (rename_i keyword; cases keyword <;> rfl)
theorem closes_total_correct (terminal : Terminal) : closes terminal = .ok (decide (terminal = .Close)) := by
  cases terminal <;> simp [closes]
theorem starts_chain_total_correct (terminal : Terminal) :
    starts_chain terminal = .ok (decide (terminal = .Keyword .ObjectPropertyChain)) := by
  cases terminal <;> (try (rename_i keyword; cases keyword)) <;> simp [starts_chain]
theorem expected_terminal_total_correct (expected : PropertyAxiomExpected) (terminal : Terminal) :
    expected_terminal expected terminal = .ok (decide (Expected expected terminal)) := by
  cases expected <;> cases terminal <;> (try (rename_i keyword; cases keyword)) <;>
    simp [expected_terminal,Expected,axiom_form_total_correct,closes_total_correct,FormOf,core.option.Option.is_some]

/-- One syntax step: the first token must belong to the expected class. A
    missing token reports the original source length, a wrong one its start. -/
inductive TakeRun (eof : Usize) (expected : PropertyAxiomExpected) :
    Tokens → core.result.Result (Token × Tokens) PropertyAxiomError → Prop
  | empty : TakeRun eof expected .Empty (.Err (.Expected expected eof))
  | wrong (token : Token) (rest : Tokens) (different : ¬ Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Err (.Expected expected token.start))
  | taken (token : Token) (rest : Tokens) (accepted : Expected expected token.terminal) :
      TakeRun eof expected (.Cons token rest) (.Ok (token,rest))

theorem take_expected_total_correct (tokens : Tokens) (expected : PropertyAxiomExpected) (eof : Usize) :
    ∃ result, take_expected tokens expected eof = .ok result ∧ TakeRun eof expected tokens result := by
  cases tokens with
  | Empty => exact ⟨.Err (.Expected expected eof),rfl,.empty⟩
  | Cons token rest =>
    by_cases accepted : Expected expected token.terminal
    · exact ⟨.Ok (token,rest),by simp [take_expected,expected_terminal_total_correct,accepted],.taken _ _ accepted⟩
    · exact ⟨.Err (.Expected expected token.start),by simp [take_expected,expected_terminal_total_correct,accepted],
        .wrong _ _ accepted⟩
private theorem take_run_unique {eof : Usize} {expected : PropertyAxiomExpected} {tokens : Tokens}
    {one two : core.result.Result (Token × Tokens) PropertyAxiomError}
    (first : TakeRun eof expected tokens one) (second : TakeRun eof expected tokens two) : one = two := by
  cases first <;> cases second <;> first | rfl | contradiction
theorem take_expected_result_iff (tokens : Tokens) (expected : PropertyAxiomExpected) (eof : Usize)
    (result : core.result.Result (Token × Tokens) PropertyAxiomError) :
    take_expected tokens expected eof = .ok result ↔ TakeRun eof expected tokens result := by
  obtain ⟨actual,executed,correct⟩ := take_expected_total_correct tokens expected eof
  constructor
  · intro output
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    have same := take_run_unique correct source
    simpa [same] using executed
theorem take_progress {eof : Usize} {expected : PropertyAxiomExpected} {tokens rest : Tokens} {token : Token}
    (taken : TakeRun eof expected tokens (.Ok (token,rest))) : TokenCount tokens = 1+TokenCount rest := by
  cases taken
  rfl

/-- An object property expression at an axiom position: the independent
    object-property grammar, with its errors wrapped. -/
inductive PropertyStep (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (limit : Nat) :
    Tokens → core.result.Result (SourceObjectProperty × Tokens) PropertyAxiomError → Prop
  | error {tokens : Tokens} {error : ClassError} (run : PropertyRun rows source eof limit tokens (.Err error)) :
      PropertyStep rows source eof limit tokens (.Err (.Class error))
  | ok {tokens rest : Tokens} {value : SourceObjectProperty}
      (run : PropertyRun rows source eof limit tokens (.Ok (value,rest))) :
      PropertyStep rows source eof limit tokens (.Ok (value,rest))

theorem read_property_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limit : Usize) :
    ∃ result, read_property table bytes tokens limit = .ok result ∧
      PropertyStep table.declarations.val bytes.val bytes.len limit.val tokens result := by
  obtain ⟨result,executed,correct⟩ := Rowl.FunctionalClasses.read_object_property_total_correct table bytes tokens limit
  rw [read_property]
  cases result with
  | Err error => exact ⟨.Err (.Class error),by simp [executed],.error correct⟩
  | Ok pair => exact ⟨.Ok pair,by simp [executed],.ok correct⟩
theorem read_property_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limit : Usize) (result : core.result.Result (SourceObjectProperty × Tokens) PropertyAxiomError) :
    read_property table bytes tokens limit = .ok result ↔
      PropertyStep table.declarations.val bytes.val bytes.len limit.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_property_total_correct table bytes tokens limit
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_property]
    cases source with
    | error run => simp [(Rowl.FunctionalClasses.read_object_property_result_iff table bytes tokens limit _).mpr run]
    | ok run => simp [(Rowl.FunctionalClasses.read_object_property_result_iff table bytes tokens limit _).mpr run]
theorem property_step_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens rest : Tokens} {value : SourceObjectProperty}
    (step : PropertyStep rows source eof limit tokens (.Ok (value,rest))) : TokenCount rest < TokenCount tokens := by
  cases step with
  | ok run => exact Rowl.FunctionalClasses.property_progress run

/-- Independent maximal member sequence: it stops before `)` or at the end;
    otherwise the member count is checked, then one object property expression
    is read and appended in source order. -/
inductive PropertiesRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    List SourceObjectProperty → Tokens →
      core.result.Result (alloc.vec.Vec SourceObjectProperty × Tokens) PropertyAxiomError → Prop
  | empty {prior : List SourceObjectProperty} {records : alloc.vec.Vec SourceObjectProperty}
      (contents : records.val = prior) :
      PropertiesRun rows source eof count limit prior .Empty (.Ok (records,.Empty))
  | stop {prior : List SourceObjectProperty} {token : Token} {tail : Tokens}
      {records : alloc.vec.Vec SourceObjectProperty} (close : token.terminal = .Close) (contents : records.val = prior) :
      PropertiesRun rows source eof count limit prior (.Cons token tail) (.Ok (records,.Cons token tail))
  | countLimit {prior : List SourceObjectProperty} {token : Token} {tail : Tokens}
      (notClose : token.terminal ≠ .Close) (full : count ≤ prior.length) :
      PropertiesRun rows source eof count limit prior (.Cons token tail) (.Err (.CountLimit token.start))
  | memberError {prior : List SourceObjectProperty} {token : Token} {tail : Tokens} {error : PropertyAxiomError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (member : PropertyStep rows source eof limit (.Cons token tail) (.Err error)) :
      PropertiesRun rows source eof count limit prior (.Cons token tail) (.Err error)
  | member {prior : List SourceObjectProperty} {token : Token} {tail rest : Tokens} {item : SourceObjectProperty}
      {result : core.result.Result (alloc.vec.Vec SourceObjectProperty × Tokens) PropertyAxiomError}
      (notClose : token.terminal ≠ .Close) (room : prior.length < count)
      (memberRun : PropertyStep rows source eof limit (.Cons token tail) (.Ok (item,rest)))
      (later : PropertiesRun rows source eof count limit (prior++[item]) rest result) :
      PropertiesRun rows source eof count limit prior (.Cons token tail) result

/-- The actual member scanner terminates, follows the independent grammar, and
    never returns more tokens than it received. -/
theorem read_properties_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (members : alloc.vec.Vec SourceObjectProperty) (limits : ClassLimits) :
    ∃ result, read_properties table bytes tokens members limits = .ok result ∧
      PropertiesRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val members.val tokens
        result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest ≤ TokenCount tokens := by
  rw [read_properties.eq_def]
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
        obtain ⟨member,memberRead,memberCorrect⟩ := read_property_total_correct table bytes (.Cons token tail) limits.iri
        cases member with
        | Err error =>
          refine ⟨.Err error,?_,.memberError close room memberCorrect,by intro value rest impossible; cases impossible⟩
          simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,memberRead]
        | Ok pair =>
          obtain ⟨member,rest⟩ := pair
          have memberStep := property_step_progress memberCorrect
          obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec members member (by scalar_tac))
          obtain ⟨result,executed,correct,progress⟩ := read_properties_total_correct table bytes rest appended limits
          refine ⟨result,?_,.member close room memberCorrect (by simpa [contents] using correct),?_⟩
          · simp [close,alloc.vec.Vec.len_val,UScalar.le_equiv,full,memberRead,push,executed]
          · intro value rest' same
            have one := progress value rest' same
            omega
termination_by TokenCount tokens
decreasing_by
  simp only [TokenCount] at *
  omega

/-- Every independent member-sequence derivation is the actual result. -/
theorem properties_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (limits : ClassLimits)
    (members : alloc.vec.Vec SourceObjectProperty) {prior : List SourceObjectProperty} (contents : members.val = prior)
    {tokens : Tokens} {result : core.result.Result (alloc.vec.Vec SourceObjectProperty × Tokens) PropertyAxiomError}
    (run : PropertiesRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val prior tokens
      result) :
    read_properties table bytes tokens members limits = .ok result := by
  induction run generalizing members with
  | empty records =>
    have equal : members = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_properties.eq_def,equal]
  | stop close records =>
    have equal : members = _ := (alloc.vec.Vec.eq_iff _ _).mpr (contents.trans records.symm)
    rw [read_properties.eq_def,equal]
    simp [closes_total_correct,close]
  | countLimit notClose full =>
    rw [read_properties.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,full]
  | @memberError prior token tail error notClose room member =>
    have notFull : ¬ limits.count.val ≤ prior.length := by omega
    rw [read_properties.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,notFull,
      (read_property_result_iff table bytes _ limits.iri _).mpr member]
  | @member prior token tail rest item result notClose room memberRun later ih =>
    have notFull : ¬ limits.count.val ≤ prior.length := by omega
    obtain ⟨appended,push,appendedContents⟩ :=
      WP.spec_imp_exists (alloc.vec.Vec.push_spec members _ (by rw [contents]; scalar_tac))
    have laterRead := ih appended (by rw [appendedContents,contents])
    rw [read_properties.eq_def]
    simp [closes_total_correct,notClose,alloc.vec.Vec.len_val,UScalar.le_equiv,contents,notFull,
      (read_property_result_iff table bytes _ limits.iri _).mpr memberRun,push,laterRead]

/-- At least two members: the maximal member sequence, then the two-member
    minimum, reported where the next member belongs. -/
inductive ListRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Tokens → core.result.Result (alloc.vec.Vec SourceObjectProperty × Tokens) PropertyAxiomError → Prop
  | error {tokens : Tokens} {error : PropertyAxiomError}
      (run : PropertiesRun rows source eof count limit [] tokens (.Err error)) :
      ListRun rows source eof count limit tokens (.Err error)
  | short {tokens rest : Tokens} {members : alloc.vec.Vec SourceObjectProperty}
      (run : PropertiesRun rows source eof count limit [] tokens (.Ok (members,rest))) (few : members.val.length < 2) :
      ListRun rows source eof count limit tokens (.Err (.Expected .Property (Position eof rest)))
  | ok {tokens rest : Tokens} {members : alloc.vec.Vec SourceObjectProperty}
      (run : PropertiesRun rows source eof count limit [] tokens (.Ok (members,rest))) (enough : 2 ≤ members.val.length) :
      ListRun rows source eof count limit tokens (.Ok (members,rest))

theorem read_list_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) :
    ∃ result, read_list table bytes tokens limits = .ok result ∧
      ListRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val tokens result ∧
      ∀ value rest, result = .Ok (value,rest) → TokenCount rest ≤ TokenCount tokens := by
  obtain ⟨scanned,scanRead,scanCorrect,scanProgress⟩ :=
    read_properties_total_correct table bytes tokens (alloc.vec.Vec.new SourceObjectProperty) limits
  rw [read_list]
  cases scanned with
  | Err error =>
    exact ⟨.Err error,by simp [scanRead],.error scanCorrect,by intro value rest impossible; cases impossible⟩
  | Ok pair =>
    obtain ⟨members,rest⟩ := pair
    by_cases few : members.val.length < 2
    · have few' : members.val.length ≤ 1 := by omega
      refine ⟨.Err (.Expected .Property (Position bytes.len rest)),?_,.short scanCorrect few,
        by intro value rest' impossible; cases impossible⟩
      simp [scanRead,alloc.vec.Vec.len_val,few',offset_of_total_correct]
    · have many : ¬ members.val.length ≤ 1 := by omega
      refine ⟨.Ok (members,rest),?_,.ok scanCorrect (by omega),scanProgress⟩
      simp [scanRead,alloc.vec.Vec.len_val,many]
theorem read_list_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits)
    (result : core.result.Result (alloc.vec.Vec SourceObjectProperty × Tokens) PropertyAxiomError) :
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
    | error run => simp [properties_execution table bytes limits (alloc.vec.Vec.new SourceObjectProperty) rfl run]
    | @short rest members run few =>
      have few' : members.val.length ≤ 1 := by omega
      simp [properties_execution table bytes limits (alloc.vec.Vec.new SourceObjectProperty) rfl run,
        alloc.vec.Vec.len_val,few',offset_of_total_correct]
    | @ok rest members run enough =>
      have many : ¬ members.val.length ≤ 1 := by omega
      simp [properties_execution table bytes limits (alloc.vec.Vec.new SourceObjectProperty) rfl run,
        alloc.vec.Vec.len_val,many]

/-- The sub-property of `SubObjectPropertyOf`: at the `ObjectPropertyChain`
    keyword, `(`, at least two members and `)`; otherwise one object property
    expression. -/
inductive SubRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    Tokens → core.result.Result (SourceSubProperty × Tokens) PropertyAxiomError → Prop
  | singleError {tokens : Tokens} {error : PropertyAxiomError} (notChain : ¬ StartsChain tokens)
      (run : PropertyStep rows source eof limit tokens (.Err error)) :
      SubRun rows source eof count limit tokens (.Err error)
  | single {tokens rest : Tokens} {property : SourceObjectProperty} (notChain : ¬ StartsChain tokens)
      (run : PropertyStep rows source eof limit tokens (.Ok (property,rest))) :
      SubRun rows source eof count limit tokens (.Ok (.Single property,rest))
  | openError {keyword : Token} {tail : Tokens} {error : PropertyAxiomError}
      (chain : keyword.terminal = .Keyword .ObjectPropertyChain) (failure : TakeRun eof .Open tail (.Err error)) :
      SubRun rows source eof count limit (.Cons keyword tail) (.Err error)
  | listError {keyword opening : Token} {tail inner : Tokens} {error : PropertyAxiomError}
      (chain : keyword.terminal = .Keyword .ObjectPropertyChain) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (failure : ListRun rows source eof count limit inner (.Err error)) :
      SubRun rows source eof count limit (.Cons keyword tail) (.Err error)
  | closeError {keyword opening : Token} {tail inner rest : Tokens} {members : alloc.vec.Vec SourceObjectProperty}
      {error : PropertyAxiomError}
      (chain : keyword.terminal = .Keyword .ObjectPropertyChain) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (listRun : ListRun rows source eof count limit inner (.Ok (members,rest)))
      (failure : TakeRun eof .Close rest (.Err error)) :
      SubRun rows source eof count limit (.Cons keyword tail) (.Err error)
  | chain {keyword opening close : Token} {tail inner rest remaining : Tokens}
      {members : alloc.vec.Vec SourceObjectProperty}
      (chain : keyword.terminal = .Keyword .ObjectPropertyChain) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (listRun : ListRun rows source eof count limit inner (.Ok (members,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      SubRun rows source eof count limit (.Cons keyword tail) (.Ok (.Chain keyword members,remaining))

private theorem single_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) (notChain : ¬ StartsChain tokens) :
    ∃ result, single table bytes tokens limits.iri = .ok result ∧
      SubRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val tokens result := by
  obtain ⟨property,propertyRead,propertyCorrect⟩ := read_property_total_correct table bytes tokens limits.iri
  rw [single]
  cases property with
  | Err error => exact ⟨.Err error,by simp [propertyRead],.singleError notChain propertyCorrect⟩
  | Ok pair =>
    obtain ⟨property,rest⟩ := pair
    exact ⟨.Ok (.Single property,rest),by simp [propertyRead],.single notChain propertyCorrect⟩
theorem read_sub_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) :
    ∃ result, read_sub table bytes tokens limits = .ok result ∧
      SubRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val tokens result := by
  rw [read_sub.eq_def]
  cases tokens with
  | Empty => exact single_total_correct table bytes .Empty limits (by simp [StartsChain])
  | Cons keyword tail =>
    simp only [starts_chain_total_correct,bind_ok]
    by_cases chain : keyword.terminal = .Keyword .ObjectPropertyChain
    · simp only [chain,decide_true,↓reduceIte]
      obtain ⟨opened,openRead,openCorrect⟩ := take_expected_total_correct tail .Open bytes.len
      cases opened with
      | Err error => exact ⟨.Err error,by simp [openRead],.openError chain openCorrect⟩
      | Ok pair =>
        obtain ⟨opening,inner⟩ := pair
        obtain ⟨listed,listRead,listCorrect,_⟩ := read_list_total_correct table bytes inner limits
        cases listed with
        | Err error => exact ⟨.Err error,by simp [openRead,listRead],.listError chain openCorrect listCorrect⟩
        | Ok pair =>
          obtain ⟨members,rest⟩ := pair
          obtain ⟨closed,closeRead,closeCorrect⟩ := take_expected_total_correct rest .Close bytes.len
          cases closed with
          | Err error =>
            exact ⟨.Err error,by simp [openRead,listRead,closeRead],.closeError chain openCorrect listCorrect closeCorrect⟩
          | Ok pair =>
            obtain ⟨close,remaining⟩ := pair
            exact ⟨.Ok (.Chain keyword members,remaining),by simp [openRead,listRead,closeRead],
              .chain chain openCorrect listCorrect closeCorrect⟩
    · simp only [chain,decide_false,Bool.false_eq_true,↓reduceIte]
      exact single_total_correct table bytes (.Cons keyword tail) limits (by simpa [StartsChain] using chain)
theorem read_sub_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : ClassLimits) (result : core.result.Result (SourceSubProperty × Tokens) PropertyAxiomError) :
    read_sub table bytes tokens limits = .ok result ↔
      SubRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_sub_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_sub.eq_def]
    cases source with
    | singleError notChain run =>
      cases tokens with
      | Empty => simp [single,(read_property_result_iff table bytes _ limits.iri _).mpr run]
      | Cons keyword tail =>
        have different : ¬ keyword.terminal = .Keyword .ObjectPropertyChain := by simpa [StartsChain] using notChain
        simp [starts_chain_total_correct,different,single,(read_property_result_iff table bytes _ limits.iri _).mpr run]
    | single notChain run =>
      cases tokens with
      | Empty => simp [single,(read_property_result_iff table bytes _ limits.iri _).mpr run]
      | Cons keyword tail =>
        have different : ¬ keyword.terminal = .Keyword .ObjectPropertyChain := by simpa [StartsChain] using notChain
        simp [starts_chain_total_correct,different,single,(read_property_result_iff table bytes _ limits.iri _).mpr run]
    | openError chain failure =>
      simp [starts_chain_total_correct,chain,(take_expected_result_iff _ .Open bytes.len _).mpr failure]
    | listError chain opened failure =>
      simp [starts_chain_total_correct,chain,(take_expected_result_iff _ .Open bytes.len _).mpr opened,
        (read_list_result_iff table bytes _ limits _).mpr failure]
    | closeError chain opened listRun failure =>
      simp [starts_chain_total_correct,chain,(take_expected_result_iff _ .Open bytes.len _).mpr opened,
        (read_list_result_iff table bytes _ limits _).mpr listRun,
        (take_expected_result_iff _ .Close bytes.len _).mpr failure]
    | chain chain opened listRun closing =>
      simp [starts_chain_total_correct,chain,(take_expected_result_iff _ .Open bytes.len _).mpr opened,
        (read_list_result_iff table bytes _ limits _).mpr listRun,
        (take_expected_result_iff _ .Close bytes.len _).mpr closing]

/-- Independent property axiom bodies after the axiom annotations, in source
    order. -/
inductive BodyRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count limit : Nat) :
    AxiomForm → Tokens → core.result.Result (SourcePropertyAxiomBody × Tokens) PropertyAxiomError → Prop
  | subError {tokens : Tokens} {error : PropertyAxiomError}
      (subRun : SubRun rows source eof count limit tokens (.Err error)) :
      BodyRun rows source eof count limit .SubObjectPropertyOf tokens (.Err error)
  | supError {tokens rest : Tokens} {sub : SourceSubProperty} {error : PropertyAxiomError}
      (subRun : SubRun rows source eof count limit tokens (.Ok (sub,rest)))
      (failure : PropertyStep rows source eof limit rest (.Err error)) :
      BodyRun rows source eof count limit .SubObjectPropertyOf tokens (.Err error)
  | subProperty {tokens rest remaining : Tokens} {sub : SourceSubProperty} {sup : SourceObjectProperty}
      (subRun : SubRun rows source eof count limit tokens (.Ok (sub,rest)))
      (supRun : PropertyStep rows source eof limit rest (.Ok (sup,remaining))) :
      BodyRun rows source eof count limit .SubObjectPropertyOf tokens (.Ok (.SubObjectPropertyOf sub sup,remaining))
  | equivalentError {tokens : Tokens} {error : PropertyAxiomError}
      (listRun : ListRun rows source eof count limit tokens (.Err error)) :
      BodyRun rows source eof count limit .EquivalentObjectProperties tokens (.Err error)
  | equivalent {tokens remaining : Tokens} {members : alloc.vec.Vec SourceObjectProperty}
      (listRun : ListRun rows source eof count limit tokens (.Ok (members,remaining))) :
      BodyRun rows source eof count limit .EquivalentObjectProperties tokens
        (.Ok (.EquivalentObjectProperties members,remaining))
  | disjointError {tokens : Tokens} {error : PropertyAxiomError}
      (listRun : ListRun rows source eof count limit tokens (.Err error)) :
      BodyRun rows source eof count limit .DisjointObjectProperties tokens (.Err error)
  | disjoint {tokens remaining : Tokens} {members : alloc.vec.Vec SourceObjectProperty}
      (listRun : ListRun rows source eof count limit tokens (.Ok (members,remaining))) :
      BodyRun rows source eof count limit .DisjointObjectProperties tokens
        (.Ok (.DisjointObjectProperties members,remaining))
  | firstError {tokens : Tokens} {error : PropertyAxiomError}
      (failure : PropertyStep rows source eof limit tokens (.Err error)) :
      BodyRun rows source eof count limit .InverseObjectProperties tokens (.Err error)
  | secondError {tokens rest : Tokens} {first : SourceObjectProperty} {error : PropertyAxiomError}
      (firstRun : PropertyStep rows source eof limit tokens (.Ok (first,rest)))
      (failure : PropertyStep rows source eof limit rest (.Err error)) :
      BodyRun rows source eof count limit .InverseObjectProperties tokens (.Err error)
  | inverse {tokens rest remaining : Tokens} {first second : SourceObjectProperty}
      (firstRun : PropertyStep rows source eof limit tokens (.Ok (first,rest)))
      (secondRun : PropertyStep rows source eof limit rest (.Ok (second,remaining))) :
      BodyRun rows source eof count limit .InverseObjectProperties tokens
        (.Ok (.InverseObjectProperties first second,remaining))
  | characteristicError {characteristic : PropertyCharacteristic} {tokens : Tokens} {error : PropertyAxiomError}
      (failure : PropertyStep rows source eof limit tokens (.Err error)) :
      BodyRun rows source eof count limit (.Characteristic characteristic) tokens (.Err error)
  | characteristic {characteristic : PropertyCharacteristic} {tokens remaining : Tokens}
      {property : SourceObjectProperty}
      (run : PropertyStep rows source eof limit tokens (.Ok (property,remaining))) :
      BodyRun rows source eof count limit (.Characteristic characteristic) tokens
        (.Ok (.Characteristic characteristic property,remaining))

/-- The actual body reader terminates and follows the independent grammar. -/
theorem read_body_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (form : AxiomForm)
    (tokens : Tokens) (limits : ClassLimits) :
    ∃ result, read_body table bytes form tokens limits = .ok result ∧
      BodyRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val form tokens result := by
  rw [read_body.eq_def]
  cases form with
  | SubObjectPropertyOf =>
    obtain ⟨sub,subRead,subCorrect⟩ := read_sub_total_correct table bytes tokens limits
    cases sub with
    | Err error => exact ⟨.Err error,by simp [subRead],.subError subCorrect⟩
    | Ok pair =>
      obtain ⟨sub,rest⟩ := pair
      obtain ⟨sup,supRead,supCorrect⟩ := read_property_total_correct table bytes rest limits.iri
      cases sup with
      | Err error => exact ⟨.Err error,by simp [subRead,supRead],.supError subCorrect supCorrect⟩
      | Ok pair =>
        obtain ⟨sup,remaining⟩ := pair
        exact ⟨.Ok (.SubObjectPropertyOf sub sup,remaining),by simp [subRead,supRead],.subProperty subCorrect supCorrect⟩
  | EquivalentObjectProperties =>
    obtain ⟨listed,listRead,listCorrect,_⟩ := read_list_total_correct table bytes tokens limits
    cases listed with
    | Err error => exact ⟨.Err error,by simp [listRead],.equivalentError listCorrect⟩
    | Ok pair =>
      obtain ⟨members,remaining⟩ := pair
      exact ⟨.Ok (.EquivalentObjectProperties members,remaining),by simp [listRead],.equivalent listCorrect⟩
  | DisjointObjectProperties =>
    obtain ⟨listed,listRead,listCorrect,_⟩ := read_list_total_correct table bytes tokens limits
    cases listed with
    | Err error => exact ⟨.Err error,by simp [listRead],.disjointError listCorrect⟩
    | Ok pair =>
      obtain ⟨members,remaining⟩ := pair
      exact ⟨.Ok (.DisjointObjectProperties members,remaining),by simp [listRead],.disjoint listCorrect⟩
  | InverseObjectProperties =>
    obtain ⟨first,firstRead,firstCorrect⟩ := read_property_total_correct table bytes tokens limits.iri
    cases first with
    | Err error => exact ⟨.Err error,by simp [firstRead],.firstError firstCorrect⟩
    | Ok pair =>
      obtain ⟨first,rest⟩ := pair
      obtain ⟨second,secondRead,secondCorrect⟩ := read_property_total_correct table bytes rest limits.iri
      cases second with
      | Err error => exact ⟨.Err error,by simp [firstRead,secondRead],.secondError firstCorrect secondCorrect⟩
      | Ok pair =>
        obtain ⟨second,remaining⟩ := pair
        exact ⟨.Ok (.InverseObjectProperties first second,remaining),by simp [firstRead,secondRead],
          .inverse firstCorrect secondCorrect⟩
  | Characteristic characteristic =>
    obtain ⟨property,propertyRead,propertyCorrect⟩ := read_property_total_correct table bytes tokens limits.iri
    cases property with
    | Err error => exact ⟨.Err error,by simp [propertyRead],.characteristicError propertyCorrect⟩
    | Ok pair =>
      obtain ⟨property,remaining⟩ := pair
      exact ⟨.Ok (.Characteristic characteristic property,remaining),by simp [propertyRead],
        .characteristic propertyCorrect⟩
/-- Every exact body and first error is equivalent to its independent derivation. -/
theorem read_body_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (form : AxiomForm)
    (tokens : Tokens) (limits : ClassLimits)
    (result : core.result.Result (SourcePropertyAxiomBody × Tokens) PropertyAxiomError) :
    read_body table bytes form tokens limits = .ok result ↔
      BodyRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val form tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_body_total_correct table bytes form tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_body.eq_def]
    cases source with
    | subError subRun => simp [(read_sub_result_iff table bytes _ limits _).mpr subRun]
    | supError subRun failure =>
      simp [(read_sub_result_iff table bytes _ limits _).mpr subRun,
        (read_property_result_iff table bytes _ limits.iri _).mpr failure]
    | subProperty subRun supRun =>
      simp [(read_sub_result_iff table bytes _ limits _).mpr subRun,
        (read_property_result_iff table bytes _ limits.iri _).mpr supRun]
    | equivalentError listRun => simp [(read_list_result_iff table bytes _ limits _).mpr listRun]
    | equivalent listRun => simp [(read_list_result_iff table bytes _ limits _).mpr listRun]
    | disjointError listRun => simp [(read_list_result_iff table bytes _ limits _).mpr listRun]
    | disjoint listRun => simp [(read_list_result_iff table bytes _ limits _).mpr listRun]
    | firstError failure => simp [(read_property_result_iff table bytes _ limits.iri _).mpr failure]
    | secondError firstRun failure =>
      simp [(read_property_result_iff table bytes _ limits.iri _).mpr firstRun,
        (read_property_result_iff table bytes _ limits.iri _).mpr failure]
    | inverse firstRun secondRun =>
      simp [(read_property_result_iff table bytes _ limits.iri _).mpr firstRun,
        (read_property_result_iff table bytes _ limits.iri _).mpr secondRun]
    | characteristicError failure => simp [(read_property_result_iff table bytes _ limits.iri _).mpr failure]
    | characteristic run => simp [(read_property_result_iff table bytes _ limits.iri _).mpr run]

/-- Independent property axiom grammar in source order: one of the eleven
    keywords, `(`, the maximal axiom-annotation sequence (the independent
    annotation grammar with the caller's annotation limits), the body with the
    caller's class limits, then `)`. -/
inductive AxiomRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize)
    (annotationCount annotationIri annotationLexical annotationDepth classCount classIri : Nat) :
    Tokens → core.result.Result (SourcePropertyAxiom × Tokens) PropertyAxiomError → Prop
  | keywordError {tokens : Tokens} {error : PropertyAxiomError} (failure : TakeRun eof .Axiom tokens (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        tokens (.Err error)
  | openError {keyword : Token} {tail : Tokens} {form : AxiomForm} {error : PropertyAxiomError}
      (formOf : FormOf keyword.terminal = some form) (failure : TakeRun eof .Open tail (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        (.Cons keyword tail) (.Err error)
  | annotationError {keyword opening : Token} {tail inner : Tokens} {form : AxiomForm}
      {error : functional_annotations.AnnotationError}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (failure : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        (.Cons keyword tail) (.Err (.Annotation error))
  | bodyError {keyword opening : Token} {tail inner : Tokens} {form : AxiomForm} {annotations : SourceAnnotations}
      {error : PropertyAxiomError}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Ok annotations))
      (failure : BodyRun rows source eof classCount classIri form annotations.remaining (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        (.Cons keyword tail) (.Err error)
  | closeError {keyword opening : Token} {tail inner rest : Tokens} {form : AxiomForm}
      {annotations : SourceAnnotations} {body : SourcePropertyAxiomBody} {error : PropertyAxiomError}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Ok annotations))
      (bodyRun : BodyRun rows source eof classCount classIri form annotations.remaining (.Ok (body,rest)))
      (failure : TakeRun eof .Close rest (.Err error)) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        (.Cons keyword tail) (.Err error)
  | ready {keyword opening close : Token} {tail inner rest remaining : Tokens} {form : AxiomForm}
      {annotations : SourceAnnotations} {body : SourcePropertyAxiomBody}
      (formOf : FormOf keyword.terminal = some form) (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (annotated : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth inner [] (.Ok annotations))
      (bodyRun : BodyRun rows source eof classCount classIri form annotations.remaining (.Ok (body,rest)))
      (closing : TakeRun eof .Close rest (.Ok (close,remaining))) :
      AxiomRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        (.Cons keyword tail) (.Ok (⟨keyword,annotations.annotations,body⟩,remaining))

/-- The actual property axiom reader terminates on every token stream and
    follows the independent grammar. -/
theorem read_property_axiom_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (annotations : AnnotationLimits) (classes : ClassLimits) :
    ∃ result, read_property_axiom table bytes tokens annotations classes = .ok result ∧
      AxiomRun table.declarations.val bytes.val bytes.len annotations.count.val annotations.iri.val
        annotations.lexical.val annotations.depth.val classes.count.val classes.iri.val tokens result := by
  obtain ⟨first,firstRead,firstCorrect⟩ := take_expected_total_correct tokens .Axiom bytes.len
  rw [read_property_axiom]
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
/-- Every exact property axiom and first error is equivalent to its independent
    derivation. -/
theorem read_property_axiom_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (annotations : AnnotationLimits) (classes : ClassLimits)
    (result : core.result.Result (SourcePropertyAxiom × Tokens) PropertyAxiomError) :
    read_property_axiom table bytes tokens annotations classes = .ok result ↔
      AxiomRun table.declarations.val bytes.val bytes.len annotations.count.val annotations.iri.val
        annotations.lexical.val annotations.depth.val classes.count.val classes.iri.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_property_axiom_total_correct table bytes tokens annotations classes
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_property_axiom]
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

/-- A successful property axiom consumes at least its keyword and its closing
    parenthesis, so an axiom loop always makes progress. -/
theorem property_axiom_progress (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens rest : Tokens)
    (annotations : AnnotationLimits) (classes : ClassLimits) (record : SourcePropertyAxiom)
    (accepted : read_property_axiom table bytes tokens annotations classes = .ok (.Ok (record,rest))) :
    TokenCount rest+2 ≤ TokenCount tokens := by
  have run := (read_property_axiom_result_iff table bytes tokens annotations classes _).mp accepted
  have listStep : ∀ {start after : Tokens} {members : alloc.vec.Vec SourceObjectProperty},
      ListRun table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val start
        (.Ok (members,after)) → TokenCount after ≤ TokenCount start := by
    intro start after members step
    have read := (read_list_result_iff table bytes start classes _).mpr step
    obtain ⟨actual,executed,_,progress⟩ := read_list_total_correct table bytes start classes
    rw [read] at executed
    exact progress members after (Result.ok_injective executed).symm
  have subStep : ∀ {start after : Tokens} {sub : SourceSubProperty},
      SubRun table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val start (.Ok (sub,after)) →
        TokenCount after ≤ TokenCount start := by
    intro start after sub step
    generalize outputEq : core.result.Result.Ok (sub,after) = output at step
    cases step with
    | single _ propertyRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have := property_step_progress propertyRun
      omega
    | chain _ opened listRun closing =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := take_progress opened
      have two := listStep listRun
      have three := take_progress closing
      simp only [TokenCount] at *
      omega
    | singleError | openError | listError | closeError => cases outputEq
  have bodyStep : ∀ {form : AxiomForm} {start after : Tokens} {body : SourcePropertyAxiomBody},
      BodyRun table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val form start
        (.Ok (body,after)) → TokenCount after ≤ TokenCount start := by
    intro form start after body step
    generalize outputEq : core.result.Result.Ok (body,after) = output at step
    cases step with
    | subProperty subRun supRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := subStep subRun
      have two := property_step_progress supRun
      omega
    | equivalent listRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      exact listStep listRun
    | disjoint listRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      exact listStep listRun
    | inverse firstRun secondRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := property_step_progress firstRun
      have two := property_step_progress secondRun
      omega
    | characteristic propertyRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have := property_step_progress propertyRun
      omega
    | subError | supError | equivalentError | disjointError | firstError | secondError | characteristicError =>
      cases outputEq
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
end Rowl.FunctionalPropertyAxioms
