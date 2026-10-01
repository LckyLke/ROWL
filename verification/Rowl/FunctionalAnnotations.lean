import Rowl.FunctionalAnnotationParts

namespace Rowl.FunctionalAnnotations
open Aeneas Aeneas.Std Aeneas.Std.Result RowlFrontendRust
open RowlFrontendRust.functional_annotations
open RowlFrontendRust.functional_lexer RowlFrontendRust.functional
open Rowl.FunctionalAnnotationParts
open Rowl.FunctionalLexer (TokenCount)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- Independent maximal annotation-sequence grammar with recursive nesting and
    exact first-error priority. At each `Annotation` keyword the remaining
    nesting allowance is checked, then this sequence's count, then `(`, the
    nested sequence one level deeper, property, value and `)`. Records append in
    source order; the first non-`Annotation` token stops the sequence unchanged. -/
inductive ScanRun (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count iriLimit lexLimit : Nat) :
    Nat → Tokens → List SourceAnnotation → core.result.Result SourceAnnotations AnnotationError → Prop
  | empty (depth : Nat) (prior : List SourceAnnotation) (records : alloc.vec.Vec SourceAnnotation)
      (contents : records.val = prior) :
      ScanRun rows source eof count iriLimit lexLimit depth .Empty prior (.Ok ⟨records,.Empty⟩)
  | stop (depth : Nat) (token : Token) (tail : Tokens) (prior : List SourceAnnotation)
      (notAnnotation : token.terminal ≠ .Keyword .Annotation) (records : alloc.vec.Vec SourceAnnotation)
      (contents : records.val = prior) :
      ScanRun rows source eof count iriLimit lexLimit depth (.Cons token tail) prior (.Ok ⟨records,.Cons token tail⟩)
  | depthLimit (token : Token) (tail : Tokens) (prior : List SourceAnnotation)
      (annotationKind : token.terminal = .Keyword .Annotation) :
      ScanRun rows source eof count iriLimit lexLimit 0 (.Cons token tail) prior (.Err (.DepthLimit token.start))
  | countLimit (depth : Nat) (token : Token) (tail : Tokens) (prior : List SourceAnnotation)
      (annotationKind : token.terminal = .Keyword .Annotation) (full : count ≤ prior.length) :
      ScanRun rows source eof count iriLimit lexLimit (depth+1) (.Cons token tail) prior (.Err (.CountLimit token.start))
  | openError {depth : Nat} {token : Token} {tail : Tokens} {prior : List SourceAnnotation} {error : AnnotationError}
      (annotationKind : token.terminal = .Keyword .Annotation) (room : prior.length < count)
      (opening : TakeRun eof .Open tail (.Err error)) :
      ScanRun rows source eof count iriLimit lexLimit (depth+1) (.Cons token tail) prior (.Err error)
  | nestedError {depth : Nat} {token opening : Token} {tail inner : Tokens} {prior : List SourceAnnotation}
      {error : AnnotationError}
      (annotationKind : token.terminal = .Keyword .Annotation) (room : prior.length < count)
      (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (nested : ScanRun rows source eof count iriLimit lexLimit depth inner [] (.Err error)) :
      ScanRun rows source eof count iriLimit lexLimit (depth+1) (.Cons token tail) prior (.Err error)
  | finishError {depth : Nat} {token opening : Token} {tail inner : Tokens} {prior : List SourceAnnotation}
      {nested : SourceAnnotations} {error : AnnotationError}
      (annotationKind : token.terminal = .Keyword .Annotation) (room : prior.length < count)
      (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (nestedRun : ScanRun rows source eof count iriLimit lexLimit depth inner [] (.Ok nested))
      (finish : FinishRun rows source eof iriLimit lexLimit nested.remaining (.Err error)) :
      ScanRun rows source eof count iriLimit lexLimit (depth+1) (.Cons token tail) prior (.Err error)
  | annotation {depth : Nat} {token opening : Token} {tail inner : Tokens} {prior : List SourceAnnotation}
      {nested : SourceAnnotations} {finished : AnnotationTail}
      {result : core.result.Result SourceAnnotations AnnotationError}
      (annotationKind : token.terminal = .Keyword .Annotation) (room : prior.length < count)
      (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (nestedRun : ScanRun rows source eof count iriLimit lexLimit depth inner [] (.Ok nested))
      (finish : FinishRun rows source eof iriLimit lexLimit nested.remaining (.Ok finished))
      (later : ScanRun rows source eof count iriLimit lexLimit (depth+1) finished.remaining
        (prior++[⟨token,nested.annotations,finished.property,finished.value⟩]) result) :
      ScanRun rows source eof count iriLimit lexLimit (depth+1) (.Cons token tail) prior result

/-- A successful sequence never returns more tokens than it received. -/
theorem scan_remaining_le {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}
    {count iriLimit lexLimit depth : Nat} {tokens : Tokens} {prior : List SourceAnnotation}
    {result : core.result.Result SourceAnnotations AnnotationError}
    (run : ScanRun rows source eof count iriLimit lexLimit depth tokens prior result) :
    ∀ output, result = .Ok output → TokenCount output.remaining ≤ TokenCount tokens := by
  induction run with
  | empty => intro output accepted; cases accepted; simp
  | stop => intro output accepted; cases accepted; simp
  | depthLimit | countLimit | openError | nestedError | finishError =>
    intro output impossible; cases impossible
  | annotation annotationKind room opened nestedRun finish later nestedIh laterIh =>
    intro output accepted
    have one := take_progress opened
    have two := nestedIh _ rfl
    have three := finish_progress finish
    have four := laterIh output accepted
    simp only [TokenCount] at *
    omega

private theorem stop_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (token : Token)
    (tail : Tokens) (prior : alloc.vec.Vec SourceAnnotation) (depth : Usize) (limits : AnnotationLimits)
    (notAnnotation : token.terminal ≠ .Keyword .Annotation) :
    scan_annotations table bytes (.Cons token tail) prior depth limits = .ok (.Ok ⟨prior,.Cons token tail⟩) := by
  rw [scan_annotations]
  cases token with
  | mk terminal start finish =>
    cases terminal <;> first | rfl | rename_i keyword; cases keyword <;> simp_all

/-- The actual recursive annotation scanner terminates on every token stream and
    follows the independent grammar, including all nested sequences. -/
theorem scan_annotations_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (prior : alloc.vec.Vec SourceAnnotation) (depth : Usize) (limits : AnnotationLimits) :
    ∃ result, scan_annotations table bytes tokens prior depth limits = .ok result ∧
      ScanRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.lexical.val
        depth.val tokens prior.val result := by
  cases tokens with
  | Empty => exact ⟨.Ok ⟨prior,.Empty⟩,by rw [scan_annotations],.empty _ _ _ rfl⟩
  | Cons token tail =>
    by_cases kind : token.terminal = .Keyword .Annotation
    · by_cases zero : depth.val = 0
      · refine ⟨.Err (.DepthLimit token.start),?_,?_⟩
        · rw [scan_annotations,kind]
          simp [UScalar.eq_equiv,zero]
        · rw [zero]
          exact .depthLimit _ _ _ kind
      · obtain ⟨level,levelValue⟩ : ∃ level, depth.val = level+1 := ⟨depth.val-1,by omega⟩
        by_cases full : limits.count.val ≤ prior.val.length
        · refine ⟨.Err (.CountLimit token.start),?_,?_⟩
          · rw [scan_annotations,kind]
            simp [UScalar.eq_equiv,zero,alloc.vec.Vec.len_val,UScalar.le_equiv,full]
          · rw [levelValue]
            exact .countLimit _ _ _ _ kind full
        · have room : prior.val.length < limits.count.val := by omega
          obtain ⟨opened,openRead,openCorrect⟩ := take_expected_total_correct tail .Open bytes.len
          cases opened with
          | Err error =>
            refine ⟨.Err error,?_,?_⟩
            · rw [scan_annotations,kind]
              simp [UScalar.eq_equiv,zero,alloc.vec.Vec.len_val,UScalar.le_equiv,full,openRead]
            · rw [levelValue]
              exact .openError kind room openCorrect
          | Ok pair =>
            obtain ⟨opening,inner⟩ := pair
            obtain ⟨smaller,subExecuted,subValue⟩ :=
              WP.spec_imp_exists (Usize.sub_spec (x := depth) (y := 1#usize) (by scalar_tac))
            have smallerValue : smaller.val = level := by
              have : (1#usize).val = 1 := rfl
              omega
            obtain ⟨nestedResult,nestedRead,nestedCorrect⟩ :=
              scan_annotations_total_correct table bytes inner (alloc.vec.Vec.new SourceAnnotation) smaller limits
            rw [smallerValue] at nestedCorrect
            cases nestedResult with
            | Err error =>
              refine ⟨.Err error,?_,?_⟩
              · rw [scan_annotations,kind]
                simp [UScalar.eq_equiv,zero,alloc.vec.Vec.len_val,UScalar.le_equiv,full,openRead,subExecuted,
                  nestedRead]
              · rw [levelValue]
                exact .nestedError kind room openCorrect (by simpa using nestedCorrect)
            | Ok nested =>
              obtain ⟨finishResult,finishRead,finishCorrect⟩ :=
                finish_annotation_total_correct table bytes nested.remaining limits
              cases finishResult with
              | Err error =>
                refine ⟨.Err error,?_,?_⟩
                · rw [scan_annotations,kind]
                  simp [UScalar.eq_equiv,zero,alloc.vec.Vec.len_val,UScalar.le_equiv,full,openRead,subExecuted,
                    nestedRead,finishRead]
                · rw [levelValue]
                  exact .finishError kind room openCorrect (by simpa using nestedCorrect) finishCorrect
              | Ok finished =>
                obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec prior
                  (⟨token,nested.annotations,finished.property,finished.value⟩ : SourceAnnotation) (by scalar_tac))
                obtain ⟨result,executed,correct⟩ :=
                  scan_annotations_total_correct table bytes finished.remaining appended depth limits
                refine ⟨result,?_,?_⟩
                · rw [scan_annotations,kind]
                  simp [UScalar.eq_equiv,zero,alloc.vec.Vec.len_val,UScalar.le_equiv,full,openRead,subExecuted,
                    nestedRead,finishRead,push,executed]
                · rw [levelValue] at correct ⊢
                  exact .annotation kind room openCorrect (by simpa using nestedCorrect) finishCorrect
                    (by simpa [contents] using correct)
    · exact ⟨.Ok ⟨prior,.Cons token tail⟩,stop_execution table bytes token tail prior depth limits kind,
        .stop _ _ _ _ kind _ rfl⟩
termination_by TokenCount tokens
decreasing_by
  all_goals first
    | (have one := take_progress openCorrect
       have two := scan_remaining_le nestedCorrect nested rfl
       have three := finish_progress finishCorrect
       simp only [TokenCount] at *
       omega)
    | (have one := take_progress openCorrect
       simp only [TokenCount] at *
       omega)

private theorem scan_execution (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8) (limits : AnnotationLimits)
    {depth : Nat} {tokens : Tokens} {prior : List SourceAnnotation}
    {result : core.result.Result SourceAnnotations AnnotationError}
    (run : ScanRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.lexical.val
      depth tokens prior result) :
    ∀ (records : alloc.vec.Vec SourceAnnotation) (level : Usize), records.val = prior → level.val = depth →
      scan_annotations table bytes tokens records level limits = .ok result := by
  induction run with
  | empty depth prior expected contents =>
    intro records level same _
    have equal : records = expected := (alloc.vec.Vec.eq_iff _ _).mpr (same.trans contents.symm)
    simp [scan_annotations,equal]
  | stop depth token tail prior kind expected contents =>
    intro records level same _
    have equal : records = expected := (alloc.vec.Vec.eq_iff _ _).mpr (same.trans contents.symm)
    simpa [equal] using stop_execution table bytes token tail records level limits kind
  | depthLimit token tail prior kind =>
    intro records level same levelValue
    rw [scan_annotations,kind]
    simp [UScalar.eq_equiv,levelValue]
  | countLimit depth token tail prior kind full =>
    intro records level same levelValue
    rw [scan_annotations,kind]
    simp [UScalar.eq_equiv,levelValue,alloc.vec.Vec.len_val,UScalar.le_equiv,same,full]
  | @openError depth token tail prior error kind room opening =>
    intro records level same levelValue
    have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opening
    rw [scan_annotations,kind]
    simp [UScalar.eq_equiv,levelValue,alloc.vec.Vec.len_val,UScalar.le_equiv,same,
      show ¬ limits.count.val ≤ prior.length from by omega,openRead]
  | @nestedError depth token opening tail inner prior error kind room opened nested nestedIh =>
    intro records level same levelValue
    have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
    obtain ⟨smaller,subExecuted,subValue⟩ :=
      WP.spec_imp_exists (Usize.sub_spec (x := level) (y := 1#usize) (by scalar_tac))
    have nestedRead := nestedIh (alloc.vec.Vec.new SourceAnnotation) smaller rfl (by
      have : (1#usize).val = 1 := rfl
      omega)
    rw [scan_annotations,kind]
    simp [UScalar.eq_equiv,levelValue,alloc.vec.Vec.len_val,UScalar.le_equiv,same,
      show ¬ limits.count.val ≤ prior.length from by omega,openRead,subExecuted,nestedRead]
  | @finishError depth token opening tail inner prior nested error kind room opened nestedRun finish nestedIh =>
    intro records level same levelValue
    have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
    obtain ⟨smaller,subExecuted,subValue⟩ :=
      WP.spec_imp_exists (Usize.sub_spec (x := level) (y := 1#usize) (by scalar_tac))
    have nestedRead := nestedIh (alloc.vec.Vec.new SourceAnnotation) smaller rfl (by
      have : (1#usize).val = 1 := rfl
      omega)
    have finishRead := (finish_annotation_result_iff table bytes nested.remaining limits _).mpr finish
    rw [scan_annotations,kind]
    simp [UScalar.eq_equiv,levelValue,alloc.vec.Vec.len_val,UScalar.le_equiv,same,
      show ¬ limits.count.val ≤ prior.length from by omega,openRead,subExecuted,nestedRead,finishRead]
  | @annotation depth token opening tail inner prior nested finished result kind room opened nestedRun finish later
      nestedIh laterIh =>
    intro records level same levelValue
    have openRead := (take_expected_result_iff tail .Open bytes.len _).mpr opened
    obtain ⟨smaller,subExecuted,subValue⟩ :=
      WP.spec_imp_exists (Usize.sub_spec (x := level) (y := 1#usize) (by scalar_tac))
    have nestedRead := nestedIh (alloc.vec.Vec.new SourceAnnotation) smaller rfl (by
      have : (1#usize).val = 1 := rfl
      omega)
    have finishRead := (finish_annotation_result_iff table bytes nested.remaining limits _).mpr finish
    have roomActual : records.val.length < limits.count.val := by simpa [same] using room
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec records
      (⟨token,nested.annotations,finished.property,finished.value⟩ : SourceAnnotation) (by scalar_tac))
    have laterRead := laterIh appended level (by simp [contents,same]) levelValue
    rw [scan_annotations,kind]
    simp [UScalar.eq_equiv,levelValue,alloc.vec.Vec.len_val,UScalar.le_equiv,same,
      show ¬ limits.count.val ≤ prior.length from by omega,openRead,subExecuted,nestedRead,finishRead,push,laterRead]

/-- Every exact sequence result and first error is equivalent to its derivation. -/
theorem scan_annotations_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (prior : alloc.vec.Vec SourceAnnotation) (depth : Usize) (limits : AnnotationLimits)
    (result : core.result.Result SourceAnnotations AnnotationError) :
    scan_annotations table bytes tokens prior depth limits = .ok result ↔
      ScanRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.lexical.val
        depth.val tokens prior.val result := by
  constructor
  · intro output
    obtain ⟨actual,executed,correct⟩ := scan_annotations_total_correct table bytes tokens prior depth limits
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro source
    exact scan_execution table bytes limits source prior depth rfl rfl

/-- The public reader is total and starts an empty top-level sequence with the
    caller's full nesting allowance. -/
theorem read_annotations_total_correct (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limits : AnnotationLimits) :
    ∃ result, read_annotations table bytes tokens limits = .ok result ∧
      ScanRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.lexical.val
        limits.depth.val tokens [] result := by
  obtain ⟨result,executed,correct⟩ :=
    scan_annotations_total_correct table bytes tokens (alloc.vec.Vec.new SourceAnnotation) limits.depth limits
  exact ⟨result,by simpa [read_annotations] using executed,by simpa using correct⟩

/-- Every exact public result and first error is equivalent to its derivation. -/
theorem read_annotations_result_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limits : AnnotationLimits) (result : core.result.Result SourceAnnotations AnnotationError) :
    read_annotations table bytes tokens limits = .ok result ↔
      ScanRun table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.lexical.val
        limits.depth.val tokens [] result := by
  have actual := scan_annotations_result_iff table bytes tokens (alloc.vec.Vec.new SourceAnnotation) limits.depth limits result
  simpa [read_annotations] using actual

/-- Independent grammar of successfully read sequences: a maximal run of complete
    annotations, each with a nested sequence one level deeper, every sequence
    within the count limit and every annotation within the nesting allowance. -/
inductive Section (rows : List prefixes.Declaration) (source : List U8) (eof : Usize) (count iriLimit lexLimit : Nat) :
    Nat → Tokens → List SourceAnnotation → Tokens → Prop
  | empty (depth : Nat) : Section rows source eof count iriLimit lexLimit depth .Empty [] .Empty
  | stop (depth : Nat) {token : Token} {tail : Tokens} (notAnnotation : token.terminal ≠ .Keyword .Annotation) :
      Section rows source eof count iriLimit lexLimit depth (.Cons token tail) [] (.Cons token tail)
  | annotation {depth : Nat} {token opening : Token} {tail inner middle remaining : Tokens}
      {nested : alloc.vec.Vec SourceAnnotation} {finished : AnnotationTail} {annotations : List SourceAnnotation}
      (annotationKind : token.terminal = .Keyword .Annotation)
      (opened : TakeRun eof .Open tail (.Ok (opening,inner)))
      (nestedSection : Section rows source eof count iriLimit lexLimit depth inner nested.val middle)
      (nestedCount : nested.val.length ≤ count)
      (finish : FinishRun rows source eof iriLimit lexLimit middle (.Ok finished))
      (later : Section rows source eof count iriLimit lexLimit (depth+1) finished.remaining annotations remaining) :
      Section rows source eof count iriLimit lexLimit (depth+1) (.Cons token tail)
        (⟨token,nested,finished.property,finished.value⟩::annotations) remaining

private theorem scan_section {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}
    {count iriLimit lexLimit depth : Nat} {tokens : Tokens} {prior : List SourceAnnotation}
    {result : core.result.Result SourceAnnotations AnnotationError}
    (run : ScanRun rows source eof count iriLimit lexLimit depth tokens prior result) :
    ∀ output, result = .Ok output → prior.length ≤ count →
      output.annotations.val.length ≤ count ∧ ∃ annotations,
        Section rows source eof count iriLimit lexLimit depth tokens annotations output.remaining ∧
        output.annotations.val = prior++annotations := by
  induction run with
  | empty depth prior records contents =>
    intro output accepted bound
    cases accepted
    exact ⟨by simpa [contents] using bound,[],.empty depth,by simpa using contents⟩
  | stop depth token tail prior notAnnotation records contents =>
    intro output accepted bound
    cases accepted
    exact ⟨by simpa [contents] using bound,[],.stop depth notAnnotation,by simpa using contents⟩
  | depthLimit | countLimit | openError | nestedError | finishError =>
    intro output impossible; cases impossible
  | annotation annotationKind room opened nestedRun finish later nestedIh laterIh =>
    intro output accepted bound
    obtain ⟨nestedCount,inner,nestedSection,nestedContents⟩ := nestedIh _ rfl (by simp)
    obtain ⟨laterCount,annotations,laterSection,laterContents⟩ := laterIh output accepted (by simp; omega)
    simp only [List.nil_append] at nestedContents
    refine ⟨laterCount,_::annotations,?_,by simpa using laterContents⟩
    rw [← nestedContents] at nestedSection
    exact .annotation annotationKind opened nestedSection nestedCount finish laterSection

private theorem section_scan {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}
    {count iriLimit lexLimit depth : Nat} {tokens remaining : Tokens} {annotations : List SourceAnnotation}
    (derivation : Section rows source eof count iriLimit lexLimit depth tokens annotations remaining) :
    ∀ (prior : List SourceAnnotation) (output : SourceAnnotations), output.annotations.val = prior++annotations →
      output.remaining = remaining → prior.length+annotations.length ≤ count →
      ScanRun rows source eof count iriLimit lexLimit depth tokens prior (.Ok output) := by
  induction derivation with
  | empty depth =>
    intro prior output contents finish bound
    cases output with
    | mk records rest =>
      simp only at contents finish
      subst rest
      exact .empty depth prior records (by simpa using contents)
  | stop depth notAnnotation =>
    intro prior output contents finish bound
    cases output with
    | mk records rest =>
      simp only at contents finish
      subst rest
      exact .stop depth _ _ prior notAnnotation records (by simpa using contents)
  | @annotation depth token opening tail inner middle remaining nested finished annotations annotationKind opened
      nestedSection nestedCount finish later nestedIh laterIh =>
    intro prior output contents ending bound
    have nestedRun := nestedIh [] ⟨nested,middle⟩ rfl rfl (by simpa using nestedCount)
    simp only [List.length_cons] at bound
    have laterRun := laterIh (prior++[⟨token,nested,finished.property,finished.value⟩]) output
      (by simpa using contents) ending (by simp; omega)
    exact .annotation (nested := ⟨nested,middle⟩) annotationKind (by omega) opened nestedRun finish laterRun

/-- A successful top-level sequence derivation is exactly the independent maximal
    section, within the count limit; later axiom stages use it for their annotations. -/
theorem scan_section_accepted {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}
    {count iriLimit lexLimit depth : Nat} {tokens : Tokens} {output : SourceAnnotations}
    (run : ScanRun rows source eof count iriLimit lexLimit depth tokens [] (.Ok output)) :
    output.annotations.val.length ≤ count ∧
      Section rows source eof count iriLimit lexLimit depth tokens output.annotations.val output.remaining := by
  obtain ⟨bound,annotations,derivation,contents⟩ := scan_section run output rfl (by simp)
  simp only [List.nil_append] at contents
  exact ⟨bound,by rw [contents]; exact derivation⟩

/-- Successful public reading is exactly the independent maximal section grammar
    with the top-level count bound; nested bounds are part of the section. -/
theorem read_annotations_accepted_iff (table : prefixes.PrefixTable) (bytes : alloc.vec.Vec U8)
    (tokens : Tokens) (limits : AnnotationLimits) (output : SourceAnnotations) :
    read_annotations table bytes tokens limits = .ok (.Ok output) ↔
      Section table.declarations.val bytes.val bytes.len limits.count.val limits.iri.val limits.lexical.val
        limits.depth.val tokens output.annotations.val output.remaining ∧
      output.annotations.val.length ≤ limits.count.val := by
  rw [read_annotations_result_iff]
  constructor
  · intro run
    obtain ⟨bound,derivation⟩ := scan_section_accepted run
    exact ⟨derivation,bound⟩
  · intro accepted
    exact section_scan accepted.1 [] output (by simp) rfl (by simpa using accepted.2)

/-- Reading is maximal: the preserved suffix is empty or begins with a terminal
    other than `Annotation`. Axioms and the closing token are later stages. -/
theorem section_maximal {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}
    {count iriLimit lexLimit depth : Nat} {tokens remaining : Tokens} {annotations : List SourceAnnotation}
    (derivation : Section rows source eof count iriLimit lexLimit depth tokens annotations remaining) :
    remaining = .Empty ∨ ∃ token tail, remaining = .Cons token tail ∧ token.terminal ≠ .Keyword .Annotation := by
  induction derivation with
  | empty => exact .inl rfl
  | stop _ notAnnotation => exact .inr ⟨_,_,rfl,notAnnotation⟩
  | annotation _ _ _ _ _ _ _ laterIh => exact laterIh

/-- Every top-level record keeps its original `Annotation` keyword token and an
    exact source-linked property IRI; nested records satisfy the same section. -/
theorem section_records {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}
    {count iriLimit lexLimit depth : Nat} {tokens remaining : Tokens} {annotations : List SourceAnnotation}
    (derivation : Section rows source eof count iriLimit lexLimit depth tokens annotations remaining) :
    ∀ annotation ∈ annotations, annotation.keyword.terminal = .Keyword .Annotation ∧
      Rowl.FunctionalHeaderIdentity.IriValue rows source iriLimit annotation.property := by
  induction derivation with
  | empty | stop => simp
  | annotation annotationKind opened nestedSection nestedCount finish later nestedIh laterIh =>
    intro annotation member
    rcases List.mem_cons.mp member with same | included
    · subst annotation
      cases finish with
      | ready named valued closing => exact ⟨annotationKind,(property_source_value named).2⟩
    · exact laterIh annotation included

/-- A successful sequence consumes at least five tokens for every top-level record. -/
theorem section_token_count {rows : List prefixes.Declaration} {source : List U8} {eof : Usize}
    {count iriLimit lexLimit depth : Nat} {tokens remaining : Tokens} {annotations : List SourceAnnotation}
    (derivation : Section rows source eof count iriLimit lexLimit depth tokens annotations remaining) :
    TokenCount remaining+5*annotations.length ≤ TokenCount tokens := by
  induction derivation with
  | empty | stop => simp
  | annotation annotationKind opened nestedSection nestedCount finish later nestedIh laterIh =>
    have one := take_progress opened
    have three := finish_progress finish
    simp only [TokenCount,List.length_cons] at *
    omega
end Rowl.FunctionalAnnotations
