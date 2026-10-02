import Rowl.FunctionalClassAxioms
import Rowl.FunctionalAssertions
import Rowl.FunctionalAnnotationAxioms
import Rowl.FunctionalDeclarations
import Rowl.FunctionalHeader
import Rowl.FunctionalPrefixes

/-!
Whole Functional Syntax documents, proved total and exact against an
independent grammar that composes the proved stage grammars: the ontology
header, the ontology annotations, the axiom loop (declarations, annotation
axioms, the class, domain and range axioms and the class and object property
assertions; the other logical axioms are reported as unsupported), the closing
parenthesis and the end of the source.
The prefix declarations and their normative table check compose with it through
their own proved readers.
-/
namespace Rowl.FunctionalDocument
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional_document
open RowlRust.functional_lexer RowlRust.functional
open RowlRust.functional_annotations (AnnotationLimits SourceAnnotations)
open RowlRust.functional_classes (ClassLimits)
open RowlRust.functional_declarations (SourceDeclaration DeclarationError)
open RowlRust.functional_annotation_axioms (SourceAnnotationAxiom AnnotationAxiomError)
open RowlRust.functional_class_axioms (SourceClassAxiom ClassAxiomError)
open RowlRust.functional_assertions (SourceAssertion AssertionError)
open RowlRust.functional_header (HeaderTail)
open RowlRust.functional_prefixes (read_prefix_header PrefixHeader PrefixReadError)
open Rowl.FunctionalLexer (TokenCount)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The 37 axiom keywords by family: declarations, the four annotation axioms,
    the six class, domain and range axioms and the three class and object
    property assertions read here, and the other logical axiom forms. -/
def FamilyOf : Terminal → Option AxiomFamily
  | .Keyword .Declaration => some .Declaration
  | .Keyword .AnnotationAssertion => some .Annotation
  | .Keyword .SubAnnotationPropertyOf => some .Annotation
  | .Keyword .AnnotationPropertyDomain => some .Annotation
  | .Keyword .AnnotationPropertyRange => some .Annotation
  | .Keyword .SubClassOf => some .Class
  | .Keyword .EquivalentClasses => some .Class
  | .Keyword .DisjointClasses => some .Class
  | .Keyword .DisjointUnion => some .Class
  | .Keyword .ObjectPropertyDomain => some .Class
  | .Keyword .ObjectPropertyRange => some .Class
  | .Keyword .SubObjectPropertyOf => some .Unsupported
  | .Keyword .EquivalentObjectProperties => some .Unsupported
  | .Keyword .DisjointObjectProperties => some .Unsupported
  | .Keyword .InverseObjectProperties => some .Unsupported
  | .Keyword .FunctionalObjectProperty => some .Unsupported
  | .Keyword .InverseFunctionalObjectProperty => some .Unsupported
  | .Keyword .ReflexiveObjectProperty => some .Unsupported
  | .Keyword .IrreflexiveObjectProperty => some .Unsupported
  | .Keyword .SymmetricObjectProperty => some .Unsupported
  | .Keyword .AsymmetricObjectProperty => some .Unsupported
  | .Keyword .TransitiveObjectProperty => some .Unsupported
  | .Keyword .SubDataPropertyOf => some .Unsupported
  | .Keyword .EquivalentDataProperties => some .Unsupported
  | .Keyword .DisjointDataProperties => some .Unsupported
  | .Keyword .DataPropertyDomain => some .Unsupported
  | .Keyword .DataPropertyRange => some .Unsupported
  | .Keyword .FunctionalDataProperty => some .Unsupported
  | .Keyword .DatatypeDefinition => some .Unsupported
  | .Keyword .HasKey => some .Unsupported
  | .Keyword .SameIndividual => some .Unsupported
  | .Keyword .DifferentIndividuals => some .Unsupported
  | .Keyword .ClassAssertion => some .Assertion
  | .Keyword .ObjectPropertyAssertion => some .Assertion
  | .Keyword .NegativeObjectPropertyAssertion => some .Assertion
  | .Keyword .DataPropertyAssertion => some .Unsupported
  | .Keyword .NegativeDataPropertyAssertion => some .Unsupported
  | _ => none

theorem axiom_family_total_correct (terminal : Terminal) : axiom_family terminal = .ok (FamilyOf terminal) := by
  cases terminal <;> first | rfl | (rename_i keyword; cases keyword <;> rfl)
theorem closes_total_correct (terminal : Terminal) :
    functional_document.closes terminal = .ok (decide (terminal = .Close)) := by
  cases terminal <;> simp [functional_document.closes]

private theorem named_progress {rows : List prefixes.Declaration} {source : List U8} {eof : Usize} {limit : Nat}
    {tokens rest : Tokens} {iri : functional_header.HeaderIri}
    (accepted : Rowl.FunctionalClassAxioms.NamedRun rows source eof limit tokens (.Ok (iri,rest))) :
    TokenCount rest < TokenCount tokens := by
  cases accepted with
  | ok taken kind success =>
    have := Rowl.FunctionalClassAxioms.take_progress taken
    omega

/-- A successful class axiom consumes at least its keyword and its closing
    parenthesis, so an axiom loop always makes progress. -/
theorem class_axiom_progress (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens rest : Tokens)
    (annotations : AnnotationLimits) (classes : ClassLimits) (record : SourceClassAxiom)
    (accepted : functional_class_axioms.read_class_axiom table bytes tokens annotations classes = .ok (.Ok (record,rest))) :
    TokenCount rest+2 ≤ TokenCount tokens := by
  have run := (Rowl.FunctionalClassAxioms.read_class_axiom_result_iff table bytes tokens annotations classes _).mp accepted
  have classStep : ∀ {start after : Tokens} {value : functional_classes.SourceClass},
      Rowl.FunctionalClassAxioms.ClassStep table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val
        classes.depth.val start (.Ok (value,after)) → TokenCount after < TokenCount start := by
    intro start after value step
    cases step with
    | ok classRun =>
      have read := (Rowl.FunctionalClasses.read_class_expression_result_iff table bytes start classes _).mpr classRun
      rw [functional_classes.read_class_expression] at read
      exact Rowl.FunctionalClasses.class_progress read
  have listStep : ∀ {start after : Tokens} {list : alloc.vec.Vec functional_classes.SourceClass},
      Rowl.FunctionalClassAxioms.ListRun table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val
        classes.depth.val start (.Ok (list,after)) → TokenCount after ≤ TokenCount start := by
    intro start after list step
    cases step with
    | ok membersRun enough =>
      have start' : (alloc.vec.Vec.new functional_classes.SourceClass).val = [] := rfl
      rw [← start'] at membersRun
      have read := (Rowl.FunctionalClasses.read_members_result_iff table bytes start
        (alloc.vec.Vec.new functional_classes.SourceClass) classes.depth classes _).mpr membersRun
      obtain ⟨actual,executed,_,progress⟩ :=
        Rowl.FunctionalClasses.read_members_total_correct table bytes start
          (alloc.vec.Vec.new functional_classes.SourceClass) classes.depth classes
      rw [read] at executed
      exact progress list after (Result.ok_injective executed).symm
  have bodyStep : ∀ {form : functional_class_axioms.AxiomForm} {start after : Tokens}
      {body : functional_class_axioms.SourceClassAxiomBody},
      Rowl.FunctionalClassAxioms.BodyRun table.declarations.val bytes.val bytes.len classes.count.val classes.iri.val
        classes.depth.val form start (.Ok (body,after)) → TokenCount after ≤ TokenCount start := by
    intro form start after body step
    generalize outputEq : core.result.Result.Ok (body,after) = output at step
    cases step with
    | subClassOf subRun supRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := classStep subRun
      have two := classStep supRun
      omega
    | equivalent list =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      exact listStep list
    | disjoint list =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      exact listStep list
    | disjointUnion named list =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := named_progress named
      have two := listStep list
      omega
    | domain propertyRun domainRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := Rowl.FunctionalClasses.property_progress propertyRun
      have two := classStep domainRun
      omega
    | range propertyRun rangeRun =>
      injection outputEq with same; injection same with _ restSame; subst restSame
      have one := Rowl.FunctionalClasses.property_progress propertyRun
      have two := classStep rangeRun
      omega
    | subError | supError | equivalentError | disjointError | unionNameError | unionListError
    | domainPropertyError | domainError | rangePropertyError | rangeError => cases outputEq
  generalize outputEq : core.result.Result.Ok (record,rest) = output at run
  cases run with
  | keywordError | openError | annotationError | bodyError | closeError => cases outputEq
  | ready formOf opened annotated bodyRun closing =>
    injection outputEq with same
    injection same with _ restSame
    subst restSame
    have one := Rowl.FunctionalClassAxioms.take_progress opened
    have two := Rowl.FunctionalAnnotations.scan_remaining_le annotated _ rfl
    have three := bodyStep bodyRun
    have four := Rowl.FunctionalClassAxioms.take_progress closing
    simp only [TokenCount] at *
    omega

/-- One axiom of a supported family through its proved reader with the caller's
    limits; the other logical axiom forms are reported at their keyword. -/
inductive AxiomStep (rows : List prefixes.Declaration) (source : List U8) (eof : Usize)
    (annotationCount annotationIri annotationLexical annotationDepth classCount classIri classDepth : Nat) :
    AxiomFamily → Tokens → Usize → core.result.Result (SourceAxiom × Tokens) DocumentError → Prop
  | declarationError {tokens : Tokens} {offset : Usize} {error : DeclarationError}
      (run : Rowl.FunctionalDeclarations.DeclarationRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth tokens (.Err error)) :
      AxiomStep rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth .Declaration tokens offset (.Err (.Declaration error))
  | declaration {tokens rest : Tokens} {offset : Usize} {record : SourceDeclaration}
      (run : Rowl.FunctionalDeclarations.DeclarationRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth tokens (.Ok (record,rest))) :
      AxiomStep rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth .Declaration tokens offset (.Ok (.Declaration record,rest))
  | annotationError {tokens : Tokens} {offset : Usize} {error : AnnotationAxiomError}
      (run : Rowl.FunctionalAnnotationAxioms.AxiomRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth tokens (.Err error)) :
      AxiomStep rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth .Annotation tokens offset (.Err (.AnnotationAxiom error))
  | annotation {tokens rest : Tokens} {offset : Usize} {record : SourceAnnotationAxiom}
      (run : Rowl.FunctionalAnnotationAxioms.AxiomRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth tokens (.Ok (record,rest))) :
      AxiomStep rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth .Annotation tokens offset (.Ok (.Annotation record,rest))
  | classError {tokens : Tokens} {offset : Usize} {error : ClassAxiomError}
      (run : Rowl.FunctionalClassAxioms.AxiomRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth classCount classIri classDepth tokens (.Err error)) :
      AxiomStep rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth .Class tokens offset (.Err (.ClassAxiom error))
  | «class» {tokens rest : Tokens} {offset : Usize} {record : SourceClassAxiom}
      (run : Rowl.FunctionalClassAxioms.AxiomRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth classCount classIri classDepth tokens (.Ok (record,rest))) :
      AxiomStep rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth .Class tokens offset (.Ok (.Class record,rest))
  | assertionError {tokens : Tokens} {offset : Usize} {error : AssertionError}
      (run : Rowl.FunctionalAssertions.AxiomRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth classCount classIri classDepth tokens (.Err error)) :
      AxiomStep rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth .Assertion tokens offset (.Err (.Assertion error))
  | assertion {tokens rest : Tokens} {offset : Usize} {record : SourceAssertion}
      (run : Rowl.FunctionalAssertions.AxiomRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth classCount classIri classDepth tokens (.Ok (record,rest))) :
      AxiomStep rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth .Assertion tokens offset (.Ok (.Assertion record,rest))
  | unsupported {tokens : Tokens} {offset : Usize} :
      AxiomStep rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth .Unsupported tokens offset (.Err (.UnsupportedAxiom offset))

theorem read_axiom_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (family : AxiomFamily)
    (tokens : Tokens) (offset : Usize) (limits : DocumentLimits) :
    ∃ result, read_axiom table bytes family tokens offset limits = .ok result ∧
      AxiomStep table.declarations.val bytes.val bytes.len limits.annotations.count.val limits.annotations.iri.val
        limits.annotations.lexical.val limits.annotations.depth.val limits.classes.count.val limits.classes.iri.val
        limits.classes.depth.val family tokens offset result := by
  rw [read_axiom.eq_def]
  cases family with
  | Declaration =>
    obtain ⟨result,executed,correct⟩ :=
      Rowl.FunctionalDeclarations.read_declaration_total_correct table bytes tokens limits.annotations
    cases result with
    | Err error => exact ⟨.Err (.Declaration error),by simp [executed],.declarationError correct⟩
    | Ok pair =>
      obtain ⟨record,rest⟩ := pair
      exact ⟨.Ok (.Declaration record,rest),by simp [executed],.declaration correct⟩
  | Annotation =>
    obtain ⟨result,executed,correct⟩ :=
      Rowl.FunctionalAnnotationAxioms.read_annotation_axiom_total_correct table bytes tokens limits.annotations
    cases result with
    | Err error => exact ⟨.Err (.AnnotationAxiom error),by simp [executed],.annotationError correct⟩
    | Ok pair =>
      obtain ⟨record,rest⟩ := pair
      exact ⟨.Ok (.Annotation record,rest),by simp [executed],.annotation correct⟩
  | Class =>
    obtain ⟨result,executed,correct⟩ :=
      Rowl.FunctionalClassAxioms.read_class_axiom_total_correct table bytes tokens limits.annotations limits.classes
    cases result with
    | Err error => exact ⟨.Err (.ClassAxiom error),by simp [executed],.classError correct⟩
    | Ok pair =>
      obtain ⟨record,rest⟩ := pair
      exact ⟨.Ok (.Class record,rest),by simp [executed],.«class» correct⟩
  | Assertion =>
    obtain ⟨result,executed,correct⟩ :=
      Rowl.FunctionalAssertions.read_assertion_total_correct table bytes tokens limits.annotations limits.classes
    cases result with
    | Err error => exact ⟨.Err (.Assertion error),by simp [executed],.assertionError correct⟩
    | Ok pair =>
      obtain ⟨record,rest⟩ := pair
      exact ⟨.Ok (.Assertion record,rest),by simp [executed],.assertion correct⟩
  | Unsupported => exact ⟨.Err (.UnsupportedAxiom offset),rfl,.unsupported⟩
theorem read_axiom_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (family : AxiomFamily)
    (tokens : Tokens) (offset : Usize) (limits : DocumentLimits)
    (result : core.result.Result (SourceAxiom × Tokens) DocumentError) :
    read_axiom table bytes family tokens offset limits = .ok result ↔
      AxiomStep table.declarations.val bytes.val bytes.len limits.annotations.count.val limits.annotations.iri.val
        limits.annotations.lexical.val limits.annotations.depth.val limits.classes.count.val limits.classes.iri.val
        limits.classes.depth.val family tokens offset result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_axiom_total_correct table bytes family tokens offset limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_axiom.eq_def]
    cases source with
    | declarationError run =>
      simp [(Rowl.FunctionalDeclarations.read_declaration_result_iff table bytes tokens limits.annotations _).mpr run]
    | declaration run =>
      simp [(Rowl.FunctionalDeclarations.read_declaration_result_iff table bytes tokens limits.annotations _).mpr run]
    | annotationError run =>
      simp [(Rowl.FunctionalAnnotationAxioms.read_annotation_axiom_result_iff table bytes tokens limits.annotations
        _).mpr run]
    | annotation run =>
      simp [(Rowl.FunctionalAnnotationAxioms.read_annotation_axiom_result_iff table bytes tokens limits.annotations
        _).mpr run]
    | classError run =>
      simp [(Rowl.FunctionalClassAxioms.read_class_axiom_result_iff table bytes tokens limits.annotations
        limits.classes _).mpr run]
    | «class» run =>
      simp [(Rowl.FunctionalClassAxioms.read_class_axiom_result_iff table bytes tokens limits.annotations
        limits.classes _).mpr run]
    | assertionError run =>
      simp [(Rowl.FunctionalAssertions.read_assertion_result_iff table bytes tokens limits.annotations
        limits.classes _).mpr run]
    | assertion run =>
      simp [(Rowl.FunctionalAssertions.read_assertion_result_iff table bytes tokens limits.annotations
        limits.classes _).mpr run]
    | unsupported => rfl
/-- A successful axiom step consumes at least one token. -/
theorem axiom_progress (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (family : AxiomFamily)
    (tokens rest : Tokens) (offset : Usize) (limits : DocumentLimits) (item : SourceAxiom)
    (accepted : read_axiom table bytes family tokens offset limits = .ok (.Ok (item,rest))) :
    TokenCount rest < TokenCount tokens := by
  have step := (read_axiom_result_iff table bytes family tokens offset limits _).mp accepted
  generalize outputEq : core.result.Result.Ok (item,rest) = output at step
  cases step with
  | declaration run =>
    injection outputEq with same; injection same with _ restSame; subst restSame
    have := Rowl.FunctionalDeclarations.declaration_token_progress run
    omega
  | annotation run =>
    injection outputEq with same; injection same with _ restSame; subst restSame
    have := (Rowl.FunctionalAnnotationAxioms.annotation_axiom_source_values run).2.2.2
    omega
  | «class» run =>
    injection outputEq with same; injection same with _ restSame; subst restSame
    have read := (Rowl.FunctionalClassAxioms.read_class_axiom_result_iff table bytes tokens limits.annotations
      limits.classes _).mpr run
    have := class_axiom_progress table bytes tokens _ limits.annotations limits.classes _ read
    omega
  | assertion run =>
    injection outputEq with same; injection same with _ restSame; subst restSame
    have read := (Rowl.FunctionalAssertions.read_assertion_result_iff table bytes tokens limits.annotations
      limits.classes _).mpr run
    have := Rowl.FunctionalAssertions.assertion_progress table bytes tokens _ limits.annotations limits.classes _ read
    omega
  | declarationError | annotationError | classError | assertionError | unsupported => cases outputEq

/-- Independent axiom loop: it stops before `)`; any other token must start an
    axiom of one of the 37 forms, after the axiom count is checked, and is read
    through its family's grammar and appended in source order. The end of the
    source is reported as a missing `)`. -/
inductive AxiomsRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize)
    (annotationCount annotationIri annotationLexical annotationDepth classCount classIri classDepth axiomCount : Nat) :
    List SourceAxiom → Tokens → core.result.Result (alloc.vec.Vec SourceAxiom × Tokens) DocumentError → Prop
  | empty {prior : List SourceAxiom} :
      AxiomsRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth axiomCount prior .Empty (.Err (.Expected .Close eof))
  | stop {prior : List SourceAxiom} {token : Token} {tail : Tokens} {records : alloc.vec.Vec SourceAxiom}
      (close : token.terminal = .Close) (contents : records.val = prior) :
      AxiomsRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth axiomCount prior (.Cons token tail) (.Ok (records,.Cons token tail))
  | other {prior : List SourceAxiom} {token : Token} {tail : Tokens}
      (notClose : token.terminal ≠ .Close) (none : FamilyOf token.terminal = none) :
      AxiomsRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth axiomCount prior (.Cons token tail) (.Err (.Expected .Axiom token.start))
  | limit {prior : List SourceAxiom} {token : Token} {tail : Tokens} {family : AxiomFamily}
      (notClose : token.terminal ≠ .Close) (familyOf : FamilyOf token.terminal = some family)
      (full : axiomCount ≤ prior.length) :
      AxiomsRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth axiomCount prior (.Cons token tail) (.Err (.AxiomLimit token.start))
  | stepError {prior : List SourceAxiom} {token : Token} {tail : Tokens} {family : AxiomFamily} {error : DocumentError}
      (notClose : token.terminal ≠ .Close) (familyOf : FamilyOf token.terminal = some family)
      (room : prior.length < axiomCount)
      (step : AxiomStep rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount
        classIri classDepth family (.Cons token tail) token.start (.Err error)) :
      AxiomsRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth axiomCount prior (.Cons token tail) (.Err error)
  | step {prior : List SourceAxiom} {token : Token} {tail rest : Tokens} {family : AxiomFamily} {item : SourceAxiom}
      {result : core.result.Result (alloc.vec.Vec SourceAxiom × Tokens) DocumentError}
      (notClose : token.terminal ≠ .Close) (familyOf : FamilyOf token.terminal = some family)
      (room : prior.length < axiomCount)
      (stepRun : AxiomStep rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount
        classIri classDepth family (.Cons token tail) token.start (.Ok (item,rest)))
      (later : AxiomsRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount
        classIri classDepth axiomCount (prior++[item]) rest result) :
      AxiomsRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount classIri
        classDepth axiomCount prior (.Cons token tail) result

/-- The actual axiom loop terminates on every token stream and follows the
    independent grammar. -/
theorem read_axioms_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (axioms : alloc.vec.Vec SourceAxiom) (limits : DocumentLimits) :
    ∃ result, read_axioms table bytes tokens axioms limits = .ok result ∧
      AxiomsRun table.declarations.val bytes.val bytes.len limits.annotations.count.val limits.annotations.iri.val
        limits.annotations.lexical.val limits.annotations.depth.val limits.classes.count.val limits.classes.iri.val
        limits.classes.depth.val limits.axioms.val axioms.val tokens result := by
  rw [read_axioms.eq_def]
  cases tokens with
  | Empty => exact ⟨.Err (.Expected .Close bytes.len),rfl,.empty⟩
  | Cons token tail =>
    simp only [closes_total_correct,bind_ok]
    by_cases close : token.terminal = .Close
    · exact ⟨.Ok (axioms,.Cons token tail),by simp [close],.stop close rfl⟩
    · simp only [close,decide_false,Bool.false_eq_true,↓reduceIte,axiom_family_total_correct,bind_ok]
      cases familyOf : FamilyOf token.terminal with
      | none => exact ⟨.Err (.Expected .Axiom token.start),rfl,.other close familyOf⟩
      | some family =>
        by_cases full : limits.axioms.val ≤ axioms.val.length
        · exact ⟨.Err (.AxiomLimit token.start),by simp [alloc.vec.Vec.len_val,UScalar.le_equiv,full],
            .limit close familyOf full⟩
        · have room : axioms.val.length < limits.axioms.val := by omega
          obtain ⟨step,stepRead,stepCorrect⟩ := read_axiom_total_correct table bytes family (.Cons token tail)
            token.start limits
          cases step with
          | Err error =>
            exact ⟨.Err error,by simp [alloc.vec.Vec.len_val,UScalar.le_equiv,full,stepRead],
              .stepError close familyOf room stepCorrect⟩
          | Ok pair =>
            obtain ⟨item,rest⟩ := pair
            have progress := axiom_progress table bytes family (.Cons token tail) rest token.start limits item stepRead
            obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec axioms item (by scalar_tac))
            obtain ⟨result,executed,correct⟩ := read_axioms_total_correct table bytes rest appended limits
            exact ⟨result,by simp [alloc.vec.Vec.len_val,UScalar.le_equiv,full,stepRead,push,executed],
              .step close familyOf room stepCorrect (by simpa [contents] using correct)⟩
termination_by TokenCount tokens
decreasing_by
  all_goals
    try subst_vars
    omega
/-- Every independent axiom-loop derivation is the actual result. -/
theorem axioms_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (limits : DocumentLimits)
    {prior : List SourceAxiom} {tokens : Tokens}
    {result : core.result.Result (alloc.vec.Vec SourceAxiom × Tokens) DocumentError}
    (run : AxiomsRun table.declarations.val bytes.val bytes.len limits.annotations.count.val limits.annotations.iri.val
      limits.annotations.lexical.val limits.annotations.depth.val limits.classes.count.val limits.classes.iri.val
      limits.classes.depth.val limits.axioms.val prior tokens result) :
    ∀ axioms : alloc.vec.Vec SourceAxiom, axioms.val = prior →
      read_axioms table bytes tokens axioms limits = .ok result := by
  induction run with
  | empty => intro axioms _; rw [read_axioms.eq_def]
  | stop close contents =>
    intro axioms same
    have equal : axioms = _ := (alloc.vec.Vec.eq_iff _ _).mpr (same.trans contents.symm)
    rw [read_axioms.eq_def,equal]
    simp [closes_total_correct,close]
  | other notClose none =>
    intro axioms _
    rw [read_axioms.eq_def]
    simp [closes_total_correct,notClose,axiom_family_total_correct,none]
  | limit notClose familyOf full =>
    intro axioms same
    rw [read_axioms.eq_def]
    simp [closes_total_correct,notClose,axiom_family_total_correct,familyOf,alloc.vec.Vec.len_val,UScalar.le_equiv,
      same,full]
  | stepError notClose familyOf room step =>
    intro axioms same
    rw [read_axioms.eq_def]
    simp [closes_total_correct,notClose,axiom_family_total_correct,familyOf,alloc.vec.Vec.len_val,UScalar.le_equiv,
      same,Nat.not_le.mpr room,(read_axiom_result_iff table bytes _ _ _ limits _).mpr step]
  | step notClose familyOf room stepRun later ih =>
    intro axioms same
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec axioms _ (by rw [same]; scalar_tac))
    have laterRead := ih appended (by rw [contents,same])
    rw [read_axioms.eq_def]
    simp [closes_total_correct,notClose,axiom_family_total_correct,familyOf,alloc.vec.Vec.len_val,UScalar.le_equiv,
      same,Nat.not_le.mpr room,(read_axiom_result_iff table bytes _ _ _ limits _).mpr stepRun,push,
      laterRead]
/-- Every exact axiom sequence and first error is equivalent to its independent derivation. -/
theorem read_axioms_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (axioms : alloc.vec.Vec SourceAxiom) (limits : DocumentLimits)
    (result : core.result.Result (alloc.vec.Vec SourceAxiom × Tokens) DocumentError) :
    read_axioms table bytes tokens axioms limits = .ok result ↔
      AxiomsRun table.declarations.val bytes.val bytes.len limits.annotations.count.val limits.annotations.iri.val
        limits.annotations.lexical.val limits.annotations.depth.val limits.classes.count.val limits.classes.iri.val
        limits.classes.depth.val limits.axioms.val axioms.val tokens result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_axioms_total_correct table bytes tokens axioms limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    exact axioms_execution table bytes limits source axioms rfl
/-- A successful axiom loop always stops at the ontology's closing parenthesis. -/
theorem axioms_stop_at_close {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}
    {annotationCount annotationIri annotationLexical annotationDepth classCount classIri classDepth axiomCount : Nat}
    {prior : List SourceAxiom} {tokens rest : Tokens} {records : alloc.vec.Vec SourceAxiom}
    (run : AxiomsRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount
      classIri classDepth axiomCount prior tokens (.Ok (records,rest))) :
    ∃ close tail, rest = .Cons close tail ∧ close.terminal = .Close := by
  generalize outputEq : core.result.Result.Ok (records,rest) = output at run
  induction run with
  | stop close contents =>
    injection outputEq with same; injection same with _ restSame; subst restSame
    exact ⟨_,_,rfl,close⟩
  | step _ _ _ _ _ ih => exact ih outputEq
  | empty | other | limit | stepError => cases outputEq

/-- Independent grammar of everything after `Ontology(`: the ontology identity
    and imports, the maximal ontology-annotation sequence, the axiom loop, the
    closing parenthesis, then the end of the source. -/
inductive TailRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize)
    (importCount iriLimit annotationCount annotationIri annotationLexical annotationDepth classCount classIri classDepth
      axiomCount : Nat) :
    Tokens → core.result.Result SourceDocumentTail DocumentError → Prop
  | headerError {tokens : Tokens} {error : functional_header.HeaderError}
      (header : Rowl.FunctionalHeader.TailRun rows source eof importCount iriLimit tokens (.Err error)) :
      TailRun rows source eof importCount iriLimit annotationCount annotationIri annotationLexical annotationDepth
        classCount classIri classDepth axiomCount tokens (.Err (.Header error))
  | annotationError {tokens : Tokens} {header : HeaderTail} {error : functional_annotations.AnnotationError}
      (headerRun : Rowl.FunctionalHeader.TailRun rows source eof importCount iriLimit tokens (.Ok header))
      (annotations : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri annotationLexical
        annotationDepth header.remaining [] (.Err error)) :
      TailRun rows source eof importCount iriLimit annotationCount annotationIri annotationLexical annotationDepth
        classCount classIri classDepth axiomCount tokens (.Err (.Annotation error))
  | axiomsError {tokens : Tokens} {header : HeaderTail} {annotated : SourceAnnotations} {error : DocumentError}
      (headerRun : Rowl.FunctionalHeader.TailRun rows source eof importCount iriLimit tokens (.Ok header))
      (annotationsRun : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri
        annotationLexical annotationDepth header.remaining [] (.Ok annotated))
      (axioms : AxiomsRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount
        classIri classDepth axiomCount [] annotated.remaining (.Err error)) :
      TailRun rows source eof importCount iriLimit annotationCount annotationIri annotationLexical annotationDepth
        classCount classIri classDepth axiomCount tokens (.Err error)
  | trailing {tokens tail : Tokens} {header : HeaderTail} {annotated : SourceAnnotations}
      {records : alloc.vec.Vec SourceAxiom} {close token : Token}
      (headerRun : Rowl.FunctionalHeader.TailRun rows source eof importCount iriLimit tokens (.Ok header))
      (annotationsRun : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri
        annotationLexical annotationDepth header.remaining [] (.Ok annotated))
      (axiomsRun : AxiomsRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount
        classIri classDepth axiomCount [] annotated.remaining (.Ok (records,.Cons close (.Cons token tail)))) :
      TailRun rows source eof importCount iriLimit annotationCount annotationIri annotationLexical annotationDepth
        classCount classIri classDepth axiomCount tokens (.Err (.Expected .End token.start))
  | ready {tokens : Tokens} {header : HeaderTail} {annotated : SourceAnnotations}
      {records : alloc.vec.Vec SourceAxiom} {close : Token}
      (headerRun : Rowl.FunctionalHeader.TailRun rows source eof importCount iriLimit tokens (.Ok header))
      (annotationsRun : Rowl.FunctionalAnnotations.ScanRun rows source eof annotationCount annotationIri
        annotationLexical annotationDepth header.remaining [] (.Ok annotated))
      (axiomsRun : AxiomsRun rows source eof annotationCount annotationIri annotationLexical annotationDepth classCount
        classIri classDepth axiomCount [] annotated.remaining (.Ok (records,.Cons close .Empty))) :
      TailRun rows source eof importCount iriLimit annotationCount annotationIri annotationLexical annotationDepth
        classCount classIri classDepth axiomCount tokens
        (.Ok ⟨header.identity,header.imports,annotated.annotations,records⟩)

/-- The actual document-tail reader terminates and follows the independent
    grammar; its end-of-source fallback before `)` is unreachable. -/
theorem read_document_tail_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : DocumentLimits) :
    ∃ result, read_document_tail table bytes tokens limits = .ok result ∧
      TailRun table.declarations.val bytes.val bytes.len limits.imports.val limits.iri.val
        limits.annotations.count.val limits.annotations.iri.val limits.annotations.lexical.val
        limits.annotations.depth.val limits.classes.count.val limits.classes.iri.val limits.classes.depth.val
        limits.axioms.val tokens result := by
  have start : (alloc.vec.Vec.new SourceAxiom).val = [] := rfl
  rw [read_document_tail]
  obtain ⟨header,headerRead,headerCorrect⟩ :=
    Rowl.FunctionalHeader.read_header_tail_total_correct table bytes tokens limits.imports limits.iri
  cases header with
  | Err error => exact ⟨.Err (.Header error),by simp [headerRead],.headerError headerCorrect⟩
  | Ok header =>
    obtain ⟨annotated,annotatedRead,annotatedCorrect⟩ :=
      Rowl.FunctionalAnnotations.read_annotations_total_correct table bytes header.remaining limits.annotations
    cases annotated with
    | Err error =>
      exact ⟨.Err (.Annotation error),by simp [headerRead,annotatedRead],.annotationError headerCorrect annotatedCorrect⟩
    | Ok annotated =>
      obtain ⟨axioms,axiomsRead,axiomsCorrect⟩ :=
        read_axioms_total_correct table bytes annotated.remaining (alloc.vec.Vec.new SourceAxiom) limits
      rw [start] at axiomsCorrect
      cases axioms with
      | Err error =>
        exact ⟨.Err error,by simp [headerRead,annotatedRead,axiomsRead],
          .axiomsError headerCorrect annotatedCorrect axiomsCorrect⟩
      | Ok pair =>
        obtain ⟨records,rest⟩ := pair
        obtain ⟨close,tail,restSame,_⟩ := axioms_stop_at_close axiomsCorrect
        subst restSame
        cases tail with
        | Empty =>
          exact ⟨.Ok ⟨header.identity,header.imports,annotated.annotations,records⟩,
            by simp [headerRead,annotatedRead,axiomsRead],.ready headerCorrect annotatedCorrect axiomsCorrect⟩
        | Cons token tail =>
          exact ⟨.Err (.Expected .End token.start),by simp [headerRead,annotatedRead,axiomsRead],
            .trailing headerCorrect annotatedCorrect axiomsCorrect⟩
/-- Every exact document tail and first error is equivalent to its independent derivation. -/
theorem read_document_tail_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (tokens : Tokens)
    (limits : DocumentLimits) (result : core.result.Result SourceDocumentTail DocumentError) :
    read_document_tail table bytes tokens limits = .ok result ↔
      TailRun table.declarations.val bytes.val bytes.len limits.imports.val limits.iri.val
        limits.annotations.count.val limits.annotations.iri.val limits.annotations.lexical.val
        limits.annotations.depth.val limits.classes.count.val limits.classes.iri.val limits.classes.depth.val
        limits.axioms.val tokens result := by
  have start : (alloc.vec.Vec.new SourceAxiom).val = [] := rfl
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := read_document_tail_total_correct table bytes tokens limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    rw [read_document_tail]
    cases source with
    | headerError header =>
      simp [(Rowl.FunctionalHeader.read_header_tail_result_iff table bytes tokens limits.imports limits.iri _).mpr header]
    | annotationError headerRun annotations =>
      simp [(Rowl.FunctionalHeader.read_header_tail_result_iff table bytes tokens limits.imports limits.iri _).mpr
          headerRun,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes _ limits.annotations _).mpr annotations]
    | axiomsError headerRun annotationsRun axioms =>
      rw [← start] at axioms
      simp [(Rowl.FunctionalHeader.read_header_tail_result_iff table bytes tokens limits.imports limits.iri _).mpr
          headerRun,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes _ limits.annotations _).mpr annotationsRun,
        (read_axioms_result_iff table bytes _ _ limits _).mpr axioms]
    | trailing headerRun annotationsRun axiomsRun =>
      rw [← start] at axiomsRun
      simp [(Rowl.FunctionalHeader.read_header_tail_result_iff table bytes tokens limits.imports limits.iri _).mpr
          headerRun,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes _ limits.annotations _).mpr annotationsRun,
        (read_axioms_result_iff table bytes _ _ limits _).mpr axiomsRun]
    | ready headerRun annotationsRun axiomsRun =>
      rw [← start] at axiomsRun
      simp [(Rowl.FunctionalHeader.read_header_tail_result_iff table bytes tokens limits.imports limits.iri _).mpr
          headerRun,
        (Rowl.FunctionalAnnotations.read_annotations_result_iff table bytes _ limits.annotations _).mpr annotationsRun,
        (read_axioms_result_iff table bytes _ _ limits _).mpr axiomsRun]

/-- The rejected namespace-table check, by kind. -/
def TableErrorOf : prefixes.Check → TableError
  | .InvalidName _ => .InvalidName
  | .ReservedName _ => .ReservedName
  | .InvalidNamespace _ => .InvalidNamespace
  | _ => .Duplicate
theorem table_error_total_correct (check : prefixes.Check) : table_error check = .ok (TableErrorOf check) := by
  cases check <;> rfl

/-- A document from its original prefix declarations and its tail result. -/
def WithPrefixes (declarations : alloc.vec.Vec prefixes.Declaration) :
    core.result.Result SourceDocumentTail DocumentError → core.result.Result SourceDocument DocumentError
  | .Ok tail => .Ok ⟨declarations,tail⟩
  | .Err error => .Err error

/-- Whole-document reading always terminates. -/
theorem read_document_total (bytes : alloc.vec.Vec U8) (limits : DocumentLimits) :
    ∃ result, read_document bytes limits = .ok result := by
  rw [read_document]
  obtain ⟨header,headerRead,_⟩ :=
    Rowl.FunctionalPrefixes.read_prefix_header_total_correct bytes limits.tokens limits.prefixes limits.prefix_value
  cases header with
  | Err error => exact ⟨.Err (.Prefix error),by simp [headerRead]⟩
  | Ok opening =>
    cases checked : Rowl.Prefixes.Scan opening.declarations [] opening.declarations.val with
    | Ready table =>
      obtain ⟨tail,tailRead,_⟩ := read_document_tail_total_correct table bytes opening.remaining limits
      cases tail with
      | Err error => exact ⟨.Err error,by simp [headerRead,Rowl.Prefixes.check_total_correct,checked,tailRead]⟩
      | Ok tail =>
        exact ⟨.Ok ⟨opening.declarations,tail⟩,by simp [headerRead,Rowl.Prefixes.check_total_correct,checked,tailRead]⟩
    | InvalidName row =>
      exact ⟨.Err (.Table .InvalidName),by simp [headerRead,Rowl.Prefixes.check_total_correct,checked,
        table_error_total_correct,TableErrorOf]⟩
    | ReservedName row =>
      exact ⟨.Err (.Table .ReservedName),by simp [headerRead,Rowl.Prefixes.check_total_correct,checked,
        table_error_total_correct,TableErrorOf]⟩
    | InvalidNamespace row =>
      exact ⟨.Err (.Table .InvalidNamespace),by simp [headerRead,Rowl.Prefixes.check_total_correct,checked,
        table_error_total_correct,TableErrorOf]⟩
    | Duplicate first second =>
      exact ⟨.Err (.Table .Duplicate),by simp [headerRead,Rowl.Prefixes.check_total_correct,checked,
        table_error_total_correct,TableErrorOf]⟩
/-- A prefix-header failure is the document's first error. -/
theorem read_document_prefix_error (bytes : alloc.vec.Vec U8) (limits : DocumentLimits)
    (error : functional_prefixes.PrefixReadError)
    (rejected : read_prefix_header bytes limits.tokens limits.prefixes limits.prefix_value = .ok (.Err error)) :
    read_document bytes limits = .ok (.Err (.Prefix error)) := by
  simp [read_document,rejected]
/-- A rejected namespace table is the document's first error, by kind. -/
theorem read_document_table_error (bytes : alloc.vec.Vec U8) (limits : DocumentLimits)
    (opening : functional_prefixes.PrefixHeader) (checked : prefixes.Check)
    (parsed : read_prefix_header bytes limits.tokens limits.prefixes limits.prefix_value = .ok (.Ok opening))
    (result : prefixes.check opening.declarations = .ok checked) (notReady : ∀ table, checked ≠ .Ready table) :
    read_document bytes limits = .ok (.Err (.Table (TableErrorOf checked))) := by
  cases checked with
  | Ready table => exact absurd rfl (notReady table)
  | _ => simp [read_document,parsed,result,table_error_total_correct,TableErrorOf]
/-- With prefix declarations parsed from the same original bytes and accepted by
    the normative table checker, every exact document and first error is
    equivalent to the independent derivation of everything after `Ontology(`,
    using precisely those namespace rows; an accepted document keeps the
    original declarations. -/
theorem read_document_result_iff (bytes : alloc.vec.Vec U8) (limits : DocumentLimits)
    (opening : functional_prefixes.PrefixHeader) (table : prefixes.PrefixTable)
    (parsed : read_prefix_header bytes limits.tokens limits.prefixes limits.prefix_value = .ok (.Ok opening))
    (checked : prefixes.check opening.declarations = .ok (.Ready table))
    (result : core.result.Result SourceDocument DocumentError) :
    read_document bytes limits = .ok result ↔
      ∃ tail, TailRun opening.declarations.val bytes.val bytes.len limits.imports.val limits.iri.val
        limits.annotations.count.val limits.annotations.iri.val limits.annotations.lexical.val
        limits.annotations.depth.val limits.classes.count.val limits.classes.iri.val limits.classes.depth.val
        limits.axioms.val opening.remaining tail ∧ result = WithPrefixes opening.declarations tail := by
  have same := (Rowl.Prefixes.successful_check_correct opening.declarations table checked).1
  obtain ⟨actual,executed,correct⟩ := read_document_tail_total_correct table bytes opening.remaining limits
  have document : read_document bytes limits = .ok (WithPrefixes opening.declarations actual) := by
    cases actual <;> simp [read_document,parsed,checked,executed,WithPrefixes]
  rw [same] at correct
  rw [document]
  constructor
  · intro equal
    exact ⟨actual,correct,(Result.ok_injective equal).symm⟩
  · rintro ⟨tail,run,resultSame⟩
    have tailRead := (read_document_tail_result_iff table bytes opening.remaining limits tail).mpr (by rwa [same])
    rw [executed] at tailRead
    cases Result.ok_injective tailRead
    rw [resultSame]
end Rowl.FunctionalDocument
