import Rowl.Names

namespace Rowl.Prefixes
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.prefixes
attribute [local instance] Classical.propDecidable
attribute [local simp] alloc.vec.Vec.eq_iff
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

@[local simp] private theorem deref_val {α : Type} (value : alloc.vec.Vec α) : value.deref.val = value.val := by simp [alloc.vec.Vec.deref]

/-- Exact four case-sensitive names reserved by OWL Functional Syntax. -/
def StandardName : Standard → List U8
  | .Rdf => [114#u8,100#u8,102#u8,58#u8]
  | .Rdfs => [114#u8,100#u8,102#u8,115#u8,58#u8]
  | .Xsd => [120#u8,115#u8,100#u8,58#u8]
  | .Owl => [111#u8,119#u8,108#u8,58#u8]
/-- Normative namespace spellings in OWL Table 2, without normalization. -/
def Namespace : Standard → List U8
  | .Rdf => [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,49#u8,57#u8,57#u8,57#u8,47#u8,48#u8,50#u8,47#u8,50#u8,50#u8,45#u8,114#u8,100#u8,102#u8,45#u8,115#u8,121#u8,110#u8,116#u8,97#u8,120#u8,45#u8,110#u8,115#u8,35#u8]
  | .Rdfs => [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,48#u8,47#u8,48#u8,49#u8,47#u8,114#u8,100#u8,102#u8,45#u8,115#u8,99#u8,104#u8,101#u8,109#u8,97#u8,35#u8]
  | .Xsd => [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,49#u8,47#u8,88#u8,77#u8,76#u8,83#u8,99#u8,104#u8,101#u8,109#u8,97#u8,35#u8]
  | .Owl => [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,50#u8,47#u8,48#u8,55#u8,47#u8,111#u8,119#u8,108#u8,35#u8]
/-- Exact standard-label selection on unmodified bytes. -/
noncomputable def StandardFor (keyBytes : List U8) : Option Standard :=
  if keyBytes = StandardName .Rdf then some .Rdf else
  if keyBytes = StandardName .Rdfs then some .Rdfs else
  if keyBytes = StandardName .Xsd then some .Xsd else
  if keyBytes = StandardName .Owl then some .Owl else none
/-- Independent lexical conditions on the actual source bytes. -/
def PrefixAccepted (bytes : List U8) : Prop :=
  ∃ word, Rowl.Regular.Utf8From bytes 0 word ∧ word ∈ Rowl.Names.Prefix
def LocalAccepted (bytes : List U8) : Prop :=
  ∃ word, Rowl.Regular.Utf8From bytes 0 word ∧ word ∈ Rowl.Names.Local
def IriAccepted (bytes : List U8) : Prop :=
  ∃ word, Rowl.Regular.Utf8From bytes 0 word ∧ word ∈ Rowl.Iri.IriLanguage
/-- All lexical/reservation requirements on one supplied declaration. -/
def DeclarationValid (row : Declaration) : Prop :=
  PrefixAccepted row.name.val ∧ StandardFor row.name.val = none ∧ IriAccepted row.namespace.val
/-- Complete table requirements; repeated label names are forbidden even when
    the associated namespaces are identical. -/
def TableValid (rows : List Declaration) : Prop :=
  (∀ row ∈ rows, DeclarationValid row) ∧ (rows.map (fun row => row.name.val)).Nodup
/-- The invariant established by the only public Rust table constructor. -/
def WellFormed (table : PrefixTable) : Prop := TableValid table.declarations.val

private noncomputable def matchesName (keyBytes : List U8) (row : Declaration) : Bool := decide (row.name.val = keyBytes)
/-- Independent mathematical scan over lists, with lexical/reservation/namespace
    errors before duplicate detection and exact original evidence retained. -/
noncomputable def Scan (source : alloc.vec.Vec Declaration) (prior : List Declaration) : List Declaration → Check
  | [] => .Ready ⟨source⟩
  | row :: tail =>
    if ¬ PrefixAccepted row.name.val then .InvalidName row else
    if (StandardFor row.name.val).isSome then .ReservedName row else
    if ¬ IriAccepted row.namespace.val then .InvalidNamespace row else
    match prior.find? (matchesName row.name.val) with
    | some first => .Duplicate first row
    | none => Scan source (prior ++ [row]) tail
/-- Independent exact lookup including the implicit standard namespace macros. -/
noncomputable def Lookup (rows : List Declaration) (keyBytes : List U8) : Option (List U8) :=
  match StandardFor keyBytes with
  | some key => some (Namespace key)
  | none => ((rows.find? (matchesName keyBytes)).map (fun row => row.namespace.val))
/-- Exact concatenation when its full mathematical length fits the byte limit. -/
def Joined (left right : List U8) (limit : Nat) : Option (alloc.vec.Vec U8) → Prop
  | none => limit < left.length + right.length
  | some value => left.length + right.length ≤ limit ∧ value.val = left ++ right
/-- Success and each rejection phase stated using byte grammar, mathematical
    lookup and lengths; no premise assumes parsed keyBytes metadata is correct. -/
def ExpansionCorrect (rows : List Declaration) (label member : List U8) (limit : Nat) : Expansion → Prop
  | .InvalidPrefix => ¬ PrefixAccepted label
  | .InvalidLocal => PrefixAccepted label ∧ ¬ LocalAccepted member
  | .UndeclaredPrefix => PrefixAccepted label ∧ LocalAccepted member ∧ Lookup rows label = none
  | .ResourceLimit => PrefixAccepted label ∧ LocalAccepted member ∧
      ∃ ns, Lookup rows label = some ns ∧ limit < ns.length + member.length
  | .InvalidExpandedIri => PrefixAccepted label ∧ LocalAccepted member ∧
      ∃ ns, Lookup rows label = some ns ∧ ns.length + member.length ≤ limit ∧ ¬ IriAccepted (ns ++ member)
  | .Expanded value => PrefixAccepted label ∧ LocalAccepted member ∧
      ∃ ns, Lookup rows label = some ns ∧ ns.length + member.length ≤ limit ∧
        value.val = ns ++ member ∧ IriAccepted value.val

private theorem accepted_total (result : regular.MatchResult) :
    accepted result = .ok (decide (result = .Matched true)) := by
  cases result with
  | Matched b => cases b <;> simp [accepted]
  | MalformedUtf8 error => simp [accepted]
private theorem validation_bool (validate : alloc.vec.Vec U8 → Result regular.MatchResult)
    (condition : List U8 → Prop) (total : ∀ bytes, ∃ result, validate bytes = .ok result)
    (acceptedIff : ∀ bytes, validate bytes = .ok (.Matched true) ↔ condition bytes.val)
    (bytes : alloc.vec.Vec U8) :
    Aeneas.Std.bind (validate bytes) accepted = .ok (decide (condition bytes.val)) := by
  obtain ⟨result, executed⟩ := total bytes
  have equivalent : result = .Matched true ↔ condition bytes.val := by
    simpa [executed] using acceptedIff bytes
  simpa [executed, accepted_total] using equivalent
private theorem prefix_bool (bytes : alloc.vec.Vec U8) :
    Aeneas.Std.bind (names.validate_prefix bytes) accepted = .ok (decide (PrefixAccepted bytes.val)) :=
  validation_bool names.validate_prefix PrefixAccepted
    (fun bytes => by obtain ⟨result, executed, _⟩ := Rowl.Names.validate_prefix_total_correct bytes; exact ⟨result, executed⟩)
    Rowl.Names.validate_prefix_accepted_iff bytes
private theorem local_bool (bytes : alloc.vec.Vec U8) :
    Aeneas.Std.bind (names.validate_local bytes) accepted = .ok (decide (LocalAccepted bytes.val)) :=
  validation_bool names.validate_local LocalAccepted
    (fun bytes => by obtain ⟨result, executed, _⟩ := Rowl.Names.validate_local_total_correct bytes; exact ⟨result, executed⟩)
    Rowl.Names.validate_local_accepted_iff bytes
private theorem iri_bool (bytes : alloc.vec.Vec U8) :
    Aeneas.Std.bind (iri.validate_iri bytes) accepted = .ok (decide (IriAccepted bytes.val)) :=
  validation_bool iri.validate_iri IriAccepted
    (fun bytes => by obtain ⟨result, executed, _⟩ := Rowl.Iri.validate_iri_total_correct bytes; exact ⟨result, executed⟩)
    Rowl.Iri.validate_iri_accepted_iff bytes

private theorem copy_slice_loop_total (bytes : Slice U8) (output : alloc.vec.Vec U8) (position : Usize)
    (prefixBound : output.val.length ≤ position.val) :
    ∃ after, copy_from bytes position output = .ok after ∧ after.val = output.val ++ bytes.val.drop position.val := by
  rw [copy_from]
  by_cases more : position.val < bytes.val.length
  · have element : bytes.index_usize position = .ok bytes.val[position.val] := by
      simp [Slice.index_usize,List.getElem?_eq_getElem more]
    have size := bytes.property
    have outputBound : output.val.length < Usize.max := by omega
    obtain ⟨appended,pushByte,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec output bytes.val[position.val] outputBound)
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := position) (y := 1#usize) (by scalar_tac))
    have advanced : next.val = position.val+1 := by simpa using nextValue
    have afterBound : appended.val.length ≤ next.val := by simp [contents,advanced]; omega
    obtain ⟨after,tail,copied⟩ := copy_slice_loop_total bytes appended next afterBound
    refine ⟨after,by simp [more,element,pushByte,advance,tail], ?_⟩
    rw [copied,contents,advanced,List.drop_eq_getElem_cons more]
    simp only [List.append_assoc,List.singleton_append]
  · have empty : bytes.val.drop position.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    exact ⟨output,by simp [more],by simp [empty]⟩
termination_by bytes.val.length-position.val
decreasing_by omega

@[local step] private theorem copy_slice_spec (bytes : Slice U8) :
    prefixes.copy bytes ⦃ output => output.val = bytes.val ⦄ := by
  obtain ⟨output,executed,correct⟩ := copy_slice_loop_total bytes (alloc.vec.Vec.new U8) 0#usize (by simp)
  simp [prefixes.copy,executed,correct]


private theorem same_literal_loop_total (key : Slice U8) (pattern : Slice U8)
    (equalLength : key.val.length = pattern.val.length) (index : Usize) :
    same_from key pattern index = .ok (decide (key.val.drop index.val = pattern.val.drop index.val)) := by
  rw [same_from]
  by_cases inside : index.val < key.val.length
  · have patternInside : index.val < pattern.val.length := by omega
    have keyByte : key.index_usize index = .ok key.val[index.val] := by
      simp [Slice.index_usize,List.getElem?_eq_getElem inside]
    have patternByte : pattern.index_usize index = .ok pattern.val[index.val] := by
      simp [Slice.index_usize,List.getElem?_eq_getElem patternInside]
    by_cases heads : key.val[index.val] = pattern.val[index.val]
    · have size := key.property
      obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have advanced : next.val = index.val+1 := by simpa using nextValue
      have tail := same_literal_loop_total key pattern equalLength next
      simp [inside,keyByte,patternByte,heads,advance,tail]
      rw [List.drop_eq_getElem_cons inside,List.drop_eq_getElem_cons patternInside]
      simp only [List.cons.injEq,heads,true_and,advanced]
    · have differentValues : key.val[index.val].val ≠ pattern.val[index.val].val :=
        fun equal => heads (UScalar.eq_of_val_eq equal)
      simp [inside,keyByte,patternByte,heads,differentValues]
      rw [List.drop_eq_getElem_cons inside,List.drop_eq_getElem_cons patternInside]
      simp only [List.cons.injEq,heads,false_and,not_false_eq_true]
  · have keyEmpty : key.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have patternEmpty : pattern.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,keyEmpty,patternEmpty]
termination_by key.val.length-index.val
decreasing_by omega

private theorem same_literal_total (key : Slice U8) (pattern : Slice U8) :
    same key pattern = .ok (decide (key.val = pattern.val)) := by
  rw [same]
  by_cases equalLength : key.val.length = pattern.val.length
  · have tail := same_literal_loop_total key pattern equalLength 0#usize
    simpa [UScalar.eq_equiv, equalLength] using tail
  · have different : key.val ≠ pattern.val := fun equal => equalLength (congrArg List.length equal)
    simp [UScalar.eq_equiv,equalLength,different]


/-- The actual standard-label selector is exact and terminates on all bytes. -/
theorem standard_total_correct (keyBytes : alloc.vec.Vec U8) :
    standard keyBytes = .ok (StandardFor keyBytes.val) := by
  simp [standard, same_literal_total, StandardFor, StandardName, Array.to_slice, Array.make, lift]
  split_ifs <;> rfl
/-- Actual implicit namespace copying returns exactly the normative bytes. -/
theorem namespace_total_correct (key : Standard) :
    ∃ bytes, prefixes.namespace key = .ok bytes ∧ bytes.val = Namespace key := by
  cases key <;> apply WP.spec_imp_exists <;> unfold prefixes.namespace <;> simp only [lift]
  all_goals step*; simp_all [Namespace]

private theorem find_total (rows : alloc.vec.Vec Declaration) (keyBytes : alloc.vec.Vec U8)
    (stop index : Usize) (bound : stop.val ≤ rows.val.length) :
    find_from rows keyBytes stop index =
      .ok (((rows.val.take stop.val).drop index.val).find? (matchesName keyBytes.val)) := by
  rw [find_from]
  by_cases inside : index.val < stop.val
  · have sourceInside : index.val < rows.val.length := by omega
    have lookup : rows.index_usize index = .ok rows.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem sourceInside]
    have takenInside : index.val < (rows.val.take stop.val).length := by simp; omega
    have stepFind : ((rows.val.take stop.val).drop index.val).find? (matchesName keyBytes.val) =
        if rows.val[index.val].name.val = keyBytes.val then some rows.val[index.val]
        else ((rows.val.take stop.val).drop (index.val+1)).find? (matchesName keyBytes.val) := by
      rw [List.drop_eq_getElem_cons takenInside]
      by_cases eqName : rows.val[index.val].name.val = keyBytes.val <;>
        simp only [List.find?_cons, List.getElem_take, matchesName, eqName, decide_true, decide_false, ↓reduceIte]
    by_cases sameName : rows.val[index.val].name.val = keyBytes.val
    · simp [inside, alloc.vec.Vec.index_slice_index, lookup, same_literal_total, sameName, stepFind]
    · obtain ⟨next, advance, value⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using value
      have tail := find_total rows keyBytes stop next bound
      simp [inside, alloc.vec.Vec.index_slice_index, lookup, same_literal_total,
        sameName, advance, tail, stepFind, nv]
  · have empty : (rows.val.take stop.val).drop index.val = [] :=
      List.drop_eq_nil_iff.mpr (by simp; omega)
    simp [inside, empty]
termination_by stop.val - index.val
decreasing_by omega

/-- Exact implicit or first-declared namespace lookup, preserving all bytes. -/
theorem lookup_total_correct (table : PrefixTable) (keyBytes : alloc.vec.Vec U8) :
    ∃ result, lookup table keyBytes = .ok result ∧
      result.map alloc.vec.Vec.val = Lookup table.declarations.val keyBytes.val := by
  rw [lookup, standard_total_correct]
  cases standardCase : StandardFor keyBytes.val with
  | some key =>
    obtain ⟨bytes, copied, spelling⟩ := namespace_total_correct key
    exact ⟨some bytes, by simp [copied], by simp [Lookup, standardCase, spelling]⟩
  | none =>
    have find := find_total table.declarations keyBytes table.declarations.len 0#usize (by simp)
    have exactFind : find_from table.declarations keyBytes table.declarations.len 0#usize =
        .ok (table.declarations.val.find? (matchesName keyBytes.val)) := by simpa using find
    simp only [bind_ok, exactFind]
    cases found : table.declarations.val.find? (matchesName keyBytes.val) with
    | none => exact ⟨none, rfl, by simp [Lookup, standardCase, found]⟩
    | some row =>
      obtain ⟨bytes, copied, spelling⟩ := WP.spec_imp_exists (copy_slice_spec row.namespace.deref)
      exact ⟨some bytes, by simp [copied], by simp [Lookup, standardCase, found, spelling]⟩

private theorem append_total (bytes : Slice U8) (index : Usize) (output : alloc.vec.Vec U8) (limit : Usize)
    (outputBound : output.val.length ≤ limit.val) :
    ∃ result, append_from bytes index output limit = .ok result ∧
      Joined output.val (bytes.val.drop index.val) limit.val result := by
  rw [append_from]
  by_cases inside : index.val < bytes.val.length
  · by_cases full : limit.val ≤ output.val.length
    · refine ⟨none, by simp [inside, full], ?_⟩
      simp only [Joined, List.length_drop]; omega
    · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
        simp [Slice.index_usize, List.getElem?_eq_getElem inside]
      obtain ⟨appended, pushed, contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec output bytes.val[index.val] (by scalar_tac))
      obtain ⟨next, advance, value⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using value
      have afterBound : appended.val.length ≤ limit.val := by simp [contents]; omega
      obtain ⟨result, executed, correct⟩ := append_total bytes next appended limit afterBound
      refine ⟨result, by simp [inside, full, lookup, pushed, advance, executed], ?_⟩
      cases result with
      | none =>
        simp only [Joined, contents, List.length_append, List.length_singleton, List.length_drop, nv] at correct
        simp only [Joined, List.length_drop]; omega
      | some result =>
        refine ⟨?_, ?_⟩
        · simp only [Joined, contents, List.length_append, List.length_singleton, List.length_drop, nv] at correct
          simp only [List.length_drop]; omega
        · rw [correct.2, contents, nv, List.drop_eq_getElem_cons inside]
          simp [List.append_assoc]
  · have empty : bytes.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    exact ⟨some output, by simp [inside], by simp [Joined, empty, outputBound]⟩
termination_by bytes.val.length - index.val
decreasing_by omega

private theorem join_total (left right : alloc.vec.Vec U8) (limit : Usize) :
    ∃ result, join left right limit = .ok result ∧ Joined left.val right.val limit.val result := by
  obtain ⟨first, firstRun, firstCorrect⟩ :=
    append_total left.deref 0#usize (alloc.vec.Vec.new U8) limit (by simp)
  cases first with
  | none =>
    refine ⟨none, by simp [join, firstRun], ?_⟩
    have tooLarge : limit.val < left.val.length := by simpa [Joined] using firstCorrect
    change limit.val < left.val.length + right.val.length
    omega
  | some value =>
    have valueEq : value.val = left.val := by simpa [Joined] using firstCorrect.2
    have valueBound : value.val.length ≤ limit.val := by simpa [Joined, valueEq] using firstCorrect.1
    obtain ⟨result, secondRun, secondCorrect⟩ := append_total right.deref 0#usize value limit valueBound
    exact ⟨result, by simp [join, firstRun, secondRun], by simpa [valueEq] using secondCorrect⟩

private theorem check_from_total (rows : alloc.vec.Vec Declaration) (index : Usize)
    (bound : index.val ≤ rows.val.length) :
    check_from rows index = .ok (Scan rows (rows.val.take index.val) (rows.val.drop index.val)) := by
  rw [check_from]
  by_cases inside : index.val < rows.val.length
  · have lookup : rows.index_usize index = .ok rows.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have listStep : rows.val.drop index.val = rows.val[index.val] :: rows.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons inside
    have prefixStep : rows.val.take (index.val+1) = rows.val.take index.val ++ [rows.val[index.val]] :=
      List.take_succ_eq_append_getElem inside
    rw [listStep, Scan]
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup, bind_ok]
    rw [← Aeneas.Std.bind_assoc, prefix_bool, bind_ok]
    by_cases goodName : PrefixAccepted rows.val[index.val].name.val
    · simp only [goodName, decide_true, ↓reduceIte, not_true_eq_false]
      rw [standard_total_correct, bind_ok]
      cases standardCase : StandardFor rows.val[index.val].name.val with
      | some key => simp [standardCase, core.option.Option.is_some]
      | none =>
        simp only [standardCase, core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        rw [← Aeneas.Std.bind_assoc, iri_bool, bind_ok]
        by_cases goodIri : IriAccepted rows.val[index.val].namespace.val
        · simp only [goodIri, decide_true, not_true_eq_false, ↓reduceIte]
          have found := find_total rows rows.val[index.val].name index 0#usize (by omega)
          simp at found
          rw [found, bind_ok]
          cases foundCase : (rows.val.take index.val).find? (matchesName rows.val[index.val].name.val) with
          | some previous => rfl
          | none =>
            obtain ⟨next, advance, value⟩ := WP.spec_imp_exists
              (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
            have nv : next.val = index.val + 1 := by simpa using value
            have tail := check_from_total rows next (by omega)
            dsimp only
            rw [advance, bind_ok, tail]
            simp only [nv, prefixStep]
        · simp [goodIri]
    · simp [goodName]
  · have finished : index.val = rows.val.length := by omega
    simp [inside, finished, Scan]
termination_by rows.val.length - index.val
decreasing_by omega

/-- Every declaration table check terminates with the exact independently
    specified first diagnostic, or the original immutable table. -/
theorem check_total_correct (rows : alloc.vec.Vec Declaration) :
    check rows = .ok (Scan rows [] rows.val) := by
  simpa [check] using check_from_total rows 0#usize (by simp)
/-- The immutable table accessor retains all supplied names and namespaces. -/
theorem declarations_total_correct (table : PrefixTable) :
    declarations table = .ok table.declarations := rfl

private theorem scan_ready (source : alloc.vec.Vec Declaration) (prior remaining : List Declaration) :
    Scan source prior remaining = .Ready ⟨source⟩ ↔
      (∀ row ∈ remaining, DeclarationValid row) ∧
      (remaining.map (fun row => row.name.val)).Nodup ∧
      ∀ old ∈ prior, ∀ row ∈ remaining, old.name.val ≠ row.name.val := by
  induction remaining generalizing prior with
  | nil => simp [Scan]
  | cons row tail ih =>
    rw [Scan]
    by_cases nameValid : PrefixAccepted row.name.val
    · simp only [nameValid, not_true_eq_false, ↓reduceIte]
      cases standardCase : StandardFor row.name.val with
      | some key => simp [DeclarationValid, standardCase]
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        by_cases iriValid : IriAccepted row.namespace.val
        · simp only [iriValid, not_true_eq_false, ↓reduceIte]
          cases found : prior.find? (matchesName row.name.val) with
          | some previous =>
            have member := (List.find?_eq_some_iff_append.mp found).2
            obtain ⟨before, after, equal, _⟩ := member
            have same : previous.name.val = row.name.val := by
              simpa [matchesName] using (List.find?_eq_some_iff_append.mp found).1
            have included : previous ∈ prior := by simp [equal]
            constructor
            · intro impossible; cases impossible
            · rintro ⟨_, _, separate⟩
              exact False.elim (separate previous included row (by simp) same)
          | none =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [ih]
            have absent : ∀ old ∈ prior, old.name.val ≠ row.name.val := by
              simpa [matchesName] using List.find?_eq_none.mp found
            simp [DeclarationValid, nameValid, iriValid, standardCase, absent,
              List.nodup_cons, List.mem_map, and_assoc, and_left_comm, and_comm]
            aesop
        · simp [DeclarationValid, iriValid]
    · simp [DeclarationValid, nameValid]

/-- Acceptance is exactly all lexical, reservation and unique-name conditions. -/
theorem check_accepts_iff (rows : alloc.vec.Vec Declaration) :
    check rows = .ok (.Ready ⟨rows⟩) ↔ TableValid rows.val := by
  rw [check_total_correct]
  simpa [TableValid] using scan_ready rows [] rows.val

private theorem scan_preserves_source (source : alloc.vec.Vec Declaration) (prior remaining : List Declaration)
    (table : PrefixTable) (ready : Scan source prior remaining = .Ready table) : table.declarations = source := by
  induction remaining generalizing prior with
  | nil => simpa [Scan] using congrArg PrefixTable.declarations (Check.Ready.inj ready).symm
  | cons row tail ih =>
    simp only [Scan] at ready
    split at ready
    · contradiction
    · split at ready
      · contradiction
      · split at ready
        · contradiction
        · split at ready
          · contradiction
          · exact ih _ ready

/-- Actual successful construction retains the original table and establishes
    every condition required by the private Rust construction API. -/
theorem successful_check_correct (rows : alloc.vec.Vec Declaration) (table : PrefixTable)
    (ready : check rows = .ok (.Ready table)) : table.declarations = rows ∧ WellFormed table := by
  have scanned : Scan rows [] rows.val = .Ready table := by
    simpa [check_total_correct] using ready
  have original := scan_preserves_source rows [] rows.val table scanned
  have tableEqual : table = ⟨rows⟩ := by cases table; simpa using original
  have valid : TableValid rows.val := (check_accepts_iff rows).mp (by simpa [tableEqual] using ready)
  exact ⟨original, by simpa [WellFormed, original] using valid⟩

/-- The actual prefix/local expansion terminates on all input bytes with an
    exact success or phase-specific diagnostic, including mathematical byte limits. -/
theorem expand_parts_total_correct (table : PrefixTable) (label member : alloc.vec.Vec U8) (limit : Usize) :
    ∃ result, expand_parts table label member limit = .ok result ∧
      ExpansionCorrect table.declarations.val label.val member.val limit.val result := by
  rw [expand_parts, ← Aeneas.Std.bind_assoc, prefix_bool, bind_ok]
  by_cases prefixValid : PrefixAccepted label.val
  · simp only [prefixValid, decide_true, ↓reduceIte]
    rw [← Aeneas.Std.bind_assoc, local_bool, bind_ok]
    by_cases localValid : LocalAccepted member.val
    · simp only [localValid, decide_true, ↓reduceIte]
      obtain ⟨nsResult, lookedUp, lookupCorrect⟩ := lookup_total_correct table label
      rw [lookedUp, bind_ok]
      cases nsResult with
      | none => exact ⟨.UndeclaredPrefix, rfl, prefixValid, localValid, lookupCorrect.symm⟩
      | some ns =>
        dsimp only
        have lookupSome : Lookup table.declarations.val label.val = some ns.val := lookupCorrect.symm
        obtain ⟨joined, copied, joinCorrect⟩ := join_total ns member limit
        rw [copied, bind_ok]
        cases joined with
        | none => exact ⟨.ResourceLimit, rfl, prefixValid, localValid, ns.val, lookupSome, joinCorrect⟩
        | some value =>
          dsimp only
          rw [← Aeneas.Std.bind_assoc, iri_bool, bind_ok]
          by_cases iriValid : IriAccepted value.val
          · exact ⟨.Expanded value, by simp [iriValid], prefixValid, localValid,
              ns.val, lookupSome, joinCorrect.1, joinCorrect.2, iriValid⟩
          · refine ⟨.InvalidExpandedIri, by simp [iriValid], prefixValid, localValid,
              ns.val, lookupSome, joinCorrect.1, ?_⟩
            simpa [joinCorrect.2] using iriValid
    · exact ⟨.InvalidLocal, by simp [localValid], prefixValid, localValid⟩
  · exact ⟨.InvalidPrefix, by simp [prefixValid], prefixValid⟩

/-- All and only valid, declared, within-limit expansions to absolute IRIs
    succeed; successful bytes remain the exact namespace/local concatenation. -/
theorem expand_parts_accepts_iff (table : PrefixTable) (label member : alloc.vec.Vec U8) (limit : Usize) :
    (∃ value, expand_parts table label member limit = .ok (.Expanded value)) ↔
      PrefixAccepted label.val ∧ LocalAccepted member.val ∧
      ∃ ns, Lookup table.declarations.val label.val = some ns ∧
        ns.length + member.val.length ≤ limit.val ∧ IriAccepted (ns ++ member.val) := by
  obtain ⟨result, executed, correct⟩ := expand_parts_total_correct table label member limit
  constructor
  · rintro ⟨value, expanded⟩
    have equal := Result.ok_injective (executed.symm.trans expanded)
    subst result
    obtain ⟨prefixValid, localValid, ns, lookupSome, bound, contents, iriValid⟩ := correct
    exact ⟨prefixValid, localValid, ns, lookupSome, bound, by simpa [contents] using iriValid⟩
  · rintro ⟨prefixValid, localValid, ns, lookupSome, bound, iriValid⟩
    cases result with
    | Expanded value => exact ⟨value, executed⟩
    | InvalidPrefix => exact False.elim (correct prefixValid)
    | InvalidLocal => exact False.elim (correct.2 localValid)
    | UndeclaredPrefix =>
      change PrefixAccepted label.val ∧ LocalAccepted member.val ∧ Lookup table.declarations.val label.val = none at correct
      have impossible : False := by simpa [lookupSome] using correct.2.2
      exact impossible.elim
    | ResourceLimit =>
      obtain ⟨_, _, other, otherLookup, tooLarge⟩ := correct
      have equal : other = ns := Option.some.inj (otherLookup.symm.trans lookupSome)
      subst other; omega
    | InvalidExpandedIri =>
      obtain ⟨_, _, other, otherLookup, _, invalid⟩ := correct
      have equal : other = ns := Option.some.inj (otherLookup.symm.trans lookupSome)
      subst other; exact False.elim (invalid iriValid)

/-- Exact bounded copying of a source slice, with totality of the actual Rust operation. -/
theorem copy_total_correct (bytes : Slice U8) :
    ∃ output, prefixes.copy bytes = .ok output ∧ output.val = bytes.val :=
  WP.spec_imp_exists (copy_slice_spec bytes)

/-- Bounded concatenation has exact contents or a mathematical length failure. -/
theorem join_total_correct (left right : alloc.vec.Vec U8) (limit : Usize) :
    ∃ result, prefixes.join left right limit = .ok result ∧
      Joined left.val right.val limit.val result := join_total left right limit

/-- Every exact bounded concatenation result is characterized independently. -/
theorem join_result_iff (left right : alloc.vec.Vec U8) (limit : Usize)
    (result : Option (alloc.vec.Vec U8)) :
    prefixes.join left right limit = .ok result ↔ Joined left.val right.val limit.val result := by
  obtain ⟨actual,executed,correct⟩ := join_total_correct left right limit
  constructor
  · intro output
    have same := Result.ok_injective (executed.symm.trans output)
    simpa [same] using correct
  · intro wanted
    have same : actual = result := by
      cases actual with
      | none => cases result with
        | none => rfl
        | some value => change limit.val < left.val.length + right.val.length at correct
                        change left.val.length + right.val.length ≤ limit.val ∧ _ at wanted
                        omega
      | some value => cases result with
        | none => change limit.val < left.val.length + right.val.length at wanted
                  change left.val.length + right.val.length ≤ limit.val ∧ _ at correct
                  omega
        | some other =>
          have sameBytes := correct.2.trans wanted.2.symm
          have equal := (alloc.vec.Vec.eq_iff value other).mpr sameBytes
          simp [equal]
    simpa [same] using executed

end Rowl.Prefixes
