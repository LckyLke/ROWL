import Rowl.IriResolution

/-!
The actual extracted `references` functions compute the RFC 3986 section 5.2
algorithm of `IriResolution.lean` on the bytes of their inputs.
`split_total_correct` proves that `references::split` returns spans of exactly
the Appendix B components. `remove_dots_total_correct` and `merge_spec` prove
the actual dot-segment removal and merging exact, and `absolute_spec` and
`relative_spec` prove that the two branches of the actual transformation build
exactly the recomposed section 5.2.2 target. `resolve_total_correct` proves
that `references::resolve` returns exactly `IriResolution.resolve` of the bytes
of its inputs when both are shorter than `usize::MAX / 8` bytes (nothing when
neither has a scheme), and nothing otherwise. With
`IriResolution.resolve_bytes` and `resolve_iri`, `resolve_utf8_iri` concludes
that for UTF-8 spellings of an IRI and of an IRI reference the actual result is
the UTF-8 spelling of an IRI with exactly the RFC target components, under the
proviso of `resolve_iri`. `is_reference_total_correct` proves that
`references::is_reference` accepts exactly the UTF-8 spellings of RFC 3987 IRI
references, recognizing plain relative references without the grammar.
-/
namespace Rowl.References
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open Rowl.IriResolution
open scoped Computability
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- The bytes of a buffer as numbers. -/
def Word (bytes : List U8) : List Nat := bytes.map (·.val)

/-- The bytes `start..finish` of a buffer, as numbers. -/
def Slice (bytes : List U8) (start finish : Nat) : List Nat := Word ((bytes.drop start).take (finish - start))

/-- The components that span records denote in a buffer. -/
def view (bytes : List U8) (p : references.Parts) : Parts :=
  { scheme := p.scheme.map (fun s => Slice bytes s.start.val s.end.val),
    authority := p.authority.map (fun s => Slice bytes s.start.val s.end.val),
    path := Slice bytes p.path.start.val p.path.end.val,
    query := p.query.map (fun s => Slice bytes s.start.val s.end.val),
    fragment := p.fragment.map (fun s => Slice bytes s.start.val s.end.val) }

/-- A span inside a buffer. -/
def Inside (bytes : List U8) (s : references.Span) : Prop := s.start.val ≤ s.end.val ∧ s.end.val ≤ bytes.length

/-- Every span of a component record lies inside the buffer. -/
def SpansInside (bytes : List U8) (p : references.Parts) : Prop :=
  (∀ s, p.scheme = some s → Inside bytes s) ∧ (∀ s, p.authority = some s → Inside bytes s) ∧
    Inside bytes p.path ∧ (∀ s, p.query = some s → Inside bytes s) ∧ (∀ s, p.fragment = some s → Inside bytes s)

private theorem word_drop_cons {bytes : List U8} {i : Nat} (inside : i < bytes.length) :
    Word (bytes.drop i) = bytes[i].val :: Word (bytes.drop (i + 1)) := by
  unfold Word
  rw [List.drop_eq_getElem_cons inside]
  rfl

private theorem slice_empty (bytes : List U8) {i j : Nat} (order : j ≤ i) : Slice bytes i j = [] := by
  simp [Slice, Word, show j - i = 0 by omega]

private theorem slice_cons {bytes : List U8} {i j : Nat} (before : i < j) (fits : j ≤ bytes.length) :
    Slice bytes i j = bytes[i].val :: Slice bytes (i + 1) j := by
  have inside : i < bytes.length := by omega
  unfold Slice Word
  rw [List.drop_eq_getElem_cons inside, show j - i = (j - (i + 1)) + 1 by omega, List.take_succ_cons]
  rfl

private theorem slice_drop (bytes : List U8) (i k j : Nat) : Slice bytes (i + k) j = (Slice bytes i j).drop k := by
  unfold Slice Word
  rw [← List.map_drop, List.drop_take, List.drop_drop, show j - (i + k) = j - i - k by omega]

private theorem slice_append {bytes : List U8} {i j k : Nat} (first : i ≤ j) (second : j ≤ k) :
    Slice bytes i k = Slice bytes i j ++ Slice bytes j k := by
  unfold Slice Word
  rw [← List.map_append]
  congr 1
  have : k - i = (j - i) + (k - j) := by omega
  rw [this, List.take_add, List.drop_drop, show i + (j - i) = j by omega]

private theorem word_drop_slice {bytes : List U8} {i j : Nat} (order : i ≤ j) :
    Word (bytes.drop i) = Slice bytes i j ++ Word (bytes.drop j) := by
  unfold Slice Word
  rw [← List.map_append]
  congr 1
  conv_lhs => rw [← List.take_append_drop (j - i) (bytes.drop i)]
  rw [List.drop_drop, show i + (j - i) = j by omega]

private theorem slice_all (bytes : List U8) {i : Nat} : Slice bytes i bytes.length = Word (bytes.drop i) := by
  unfold Slice Word
  congr 1
  apply List.take_of_length_le
  simp

private theorem lookup {bytes : alloc.vec.Vec U8} {i : Usize} (inside : i.val < bytes.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) bytes i = .ok bytes.val[i.val] := by
  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]

/-- The characters that continue a component at a level of `stops`. -/
def Continues (level c : Nat) : Bool :=
  !(c == 35 || (0 < level && c == 63) || (1 < level && c == 47) || (2 < level && c == 58))

private theorem continues_scheme : Continues 3 = SchemeChar := by
  funext c; simp only [Continues, SchemeChar]; cases h58 : c == 58 <;> cases h47 : c == 47 <;>
    cases h63 : c == 63 <;> cases h35 : c == 35 <;> simp
private theorem continues_authority : Continues 2 = AuthorityChar := by
  funext c; simp only [Continues, AuthorityChar]; cases h58 : c == 58 <;> cases h47 : c == 47 <;>
    cases h63 : c == 63 <;> cases h35 : c == 35 <;> simp
private theorem continues_path : Continues 1 = PathChar := by
  funext c; simp only [Continues, PathChar]; cases h58 : c == 58 <;> cases h47 : c == 47 <;>
    cases h63 : c == 63 <;> cases h35 : c == 35 <;> simp
private theorem continues_query : Continues 0 = QueryChar := by
  funext c; simp only [Continues, QueryChar]; cases h58 : c == 58 <;> cases h47 : c == 47 <;>
    cases h63 : c == 63 <;> cases h35 : c == 35 <;> simp

theorem stops_spec (level byte : U8) : references.stops level byte = .ok (!Continues level.val byte.val) := by
  unfold references.stops Continues
  split_ifs <;> simp_all [UScalar.eq_equiv, UScalar.lt_equiv]
  all_goals (rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]; omega)

/-- The first byte from `index` that ends a component at `level`, or the end. -/
theorem scan_spec (bytes : alloc.vec.Vec U8) (index : Usize) (level : U8) (inside : index.val ≤ bytes.val.length) :
    ∃ r, references.scan bytes index level = .ok r ∧ index.val ≤ r.val ∧ r.val ≤ bytes.val.length ∧
      (Word (bytes.val.drop index.val)).takeWhile (Continues level.val) = Slice bytes.val index.val r.val ∧
      (Word (bytes.val.drop index.val)).dropWhile (Continues level.val) = Word (bytes.val.drop r.val) := by
  rw [references.scan]
  by_cases more : index.val < bytes.val.length
  · have element := lookup more
    rw [word_drop_cons more]
    by_cases continues : Continues level.val bytes.val[index.val].val = true
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, low, high, takes, drops⟩ := scan_spec bytes next level (by omega)
      rw [nextIs] at low takes drops
      refine ⟨r, ?_, by omega, high, ?_, ?_⟩
      · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, element, stops_spec, continues, advance, run]
      · rw [List.takeWhile_cons_of_pos continues, takes, slice_cons (i := index.val) (j := r.val) (by omega) high]
      · rw [List.dropWhile_cons_of_pos continues, drops]
    · refine ⟨index, ?_, le_refl _, inside, ?_, ?_⟩
      · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, element, stops_spec, continues]
      · rw [List.takeWhile_cons_of_neg continues, slice_empty _ (le_refl _)]
      · rw [List.dropWhile_cons_of_neg continues, word_drop_cons more]
  · have atEnd : index.val = bytes.val.length := by omega
    refine ⟨index, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], le_refl _, inside, ?_, ?_⟩
    · rw [slice_empty _ (le_refl _), atEnd]; simp [Word]
    · rw [atEnd]; simp [Word]
termination_by bytes.val.length - index.val
decreasing_by omega

theorem byte_is_spec (bytes : alloc.vec.Vec U8) (index : Usize) (value : U8) :
    references.byte_is bytes index value = .ok (decide ((Word (bytes.val.drop index.val)).head? = some value.val)) := by
  unfold references.byte_is
  by_cases more : index.val < bytes.val.length
  · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup more, word_drop_cons more, UScalar.eq_equiv]
  · have empty : bytes.val.drop index.val = [] := List.drop_eq_nil_of_le (by omega)
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, empty, Word]

theorem before_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) :
    references.before bytes index finish = .ok (decide (index.val < finish.val ∧ index.val < bytes.val.length)) := by
  unfold references.before
  by_cases first : index.val < finish.val <;> simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, first]

/-- Appending a span of a buffer appends exactly its bytes. -/
theorem append_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (out : alloc.vec.Vec U8)
    (fits : finish.val ≤ bytes.val.length) (room : out.val.length + (finish.val - index.val) ≤ Usize.max) :
    ∃ v, references.append bytes index finish out = .ok v ∧
      Word v.val = Word out.val ++ Slice bytes.val index.val finish.val ∧
      v.val.length = out.val.length + (finish.val - index.val) := by
  rw [references.append]
  by_cases more : index.val < finish.val
  · have inside : index.val < bytes.val.length := by omega
    have short : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out bytes.val[index.val] short)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value, length⟩ := append_spec bytes next finish pushed fits
      (by rw [contents, nextIs]; simp; omega)
    refine ⟨v, ?_, ?_, ?_⟩
    · simp [before_spec, more, inside, lookup inside, push, advance, run]
    · rw [value, contents, nextIs, slice_cons more fits]
      simp [Word]
    · rw [length, contents, nextIs]; simp; omega
  · refine ⟨out, by simp [before_spec, more], ?_, by omega⟩
    rw [slice_empty _ (by omega)]
    simp
termination_by finish.val - index.val
decreasing_by omega

theorem put_spec (out : alloc.vec.Vec U8) (byte : U8) (room : out.val.length < Usize.max) :
    ∃ v, references.put out byte = .ok v ∧ v.val = out.val ++ [byte] := by
  obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out byte room)
  exact ⟨pushed, by simp [references.put, push], contents⟩

theorem at_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (value : U8) (fits : finish.val ≤ bytes.val.length) :
    references.at bytes index finish value = .ok (decide ((Slice bytes.val index.val finish.val)[0]? = some value.val)) := by
  unfold references.at
  by_cases more : index.val < finish.val
  · rw [slice_cons more fits]
    simp [UScalar.lt_equiv, more, byte_is_spec, word_drop_cons (show index.val < bytes.val.length by omega)]
  · rw [slice_empty _ (by omega)]
    simp [UScalar.lt_equiv, more]

/-- `Slice` beyond its start is the dropped slice. -/
private theorem slice_at {bytes : List U8} {i k j : Nat} :
    (Slice bytes (i + k) j)[0]? = (Slice bytes i j)[k]? := by
  rw [slice_drop]; simp

private theorem word_drop_tail (bytes : List U8) (i : Nat) : (Word (bytes.drop i)).tail = Word (bytes.drop (i + 1)) := by
  unfold Word
  rw [← List.map_tail, List.tail_drop]

private theorem word_drop_two (bytes : List U8) (i : Nat) : (Word (bytes.drop i)).drop 2 = Word (bytes.drop (i + 2)) := by
  unfold Word
  rw [← List.map_drop, List.drop_drop]

private theorem word_head_some {bytes : List U8} {i v : Nat} (head : (Word (bytes.drop i)).head? = some v) :
    i < bytes.length := by
  by_contra outside
  rw [List.drop_eq_nil_of_le (by omega)] at head
  simp [Word] at head

theorem scheme_ends_spec (bytes : alloc.vec.Vec U8) (colon : Usize) :
    references.scheme_ends bytes colon =
      .ok (decide (0 < colon.val ∧ (Word (bytes.val.drop colon.val)).head? = some 58)) := by
  unfold references.scheme_ends
  by_cases positive : 0 < colon.val
  · simp [UScalar.lt_equiv, positive, byte_is_spec]
  · simp [UScalar.lt_equiv, positive]

theorem double_slash_spec (bytes : alloc.vec.Vec U8) (index : Usize) :
    references.double_slash bytes index = .ok (decide ([47, 47] <+: Word (bytes.val.drop index.val))) := by
  unfold references.double_slash
  rw [byte_is_spec]
  by_cases first : (Word (bytes.val.drop index.val)).head? = some 47
  · have inside := word_head_some first
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := bytes.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    rw [word_drop_cons inside] at first ⊢
    simp only [List.head?_cons, Option.some.injEq] at first
    simp [first, advance, byte_is_spec, nextIs, List.singleton_prefix_iff_head?_eq_some]
  · have notPrefix : ¬ [47, 47] <+: Word (bytes.val.drop index.val) := by
      intro prefixed
      obtain ⟨rest, same⟩ := prefixed
      rw [← same] at first
      simp at first
    simp [first, notPrefix]

/-- `references::split` returns spans of exactly the components of RFC 3986
    Appendix B. -/
theorem split_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ p, references.split bytes = .ok p ∧ SpansInside bytes.val p ∧ view bytes.val p = split (Word bytes.val) := by
  have size := bytes.property
  obtain ⟨colon, colonRun, _, colonLe, schemeTakes, schemeDrops⟩ := scan_spec bytes 0#usize 3#u8 (by simp)
  simp only [show (3#u8 : U8).val = 3 from rfl, continues_scheme, show (0#usize : Usize).val = 0 from rfl,
    List.drop_zero] at schemeTakes schemeDrops
  -- The scheme and the position after it.
  obtain ⟨start, startRun, schemeIs, afterScheme⟩ : ∃ start : Usize,
      (if decide (0 < colon.val ∧ (Word (bytes.val.drop colon.val)).head? = some 58) then colon + 1#usize
        else ok 0#usize) = ok start ∧
      (schemePart (Word bytes.val)).1 = (if 0 < colon.val ∧ (Word (bytes.val.drop colon.val)).head? = some 58
        then some (Slice bytes.val 0 colon.val) else none) ∧
      (schemePart (Word bytes.val)).2 = Word (bytes.val.drop start.val) ∧ start.val ≤ bytes.val.length := by
    unfold schemePart
    rw [schemeTakes, schemeDrops]
    have nonempty : Slice bytes.val 0 colon.val ≠ [] ↔ 0 < colon.val := by
      constructor
      · intro nonempty; by_contra zero; exact nonempty (slice_empty _ (by omega))
      · intro positive; rw [slice_cons positive colonLe]; simp
    by_cases found : 0 < colon.val ∧ (Word (bytes.val.drop colon.val)).head? = some 58
    · have inside := word_head_some found.2
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := colon) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = colon.val + 1 := by simpa using nextValue
      refine ⟨next, by simp [found, advance], ?_, ?_, by omega⟩
      · rw [if_pos ⟨nonempty.mpr found.1, found.2⟩, if_pos found]
      · rw [if_pos ⟨nonempty.mpr found.1, found.2⟩, word_drop_tail, nextIs]
    · refine ⟨0#usize, by simp [found], ?_, ?_, by simp⟩
      · rw [if_neg (fun x => found ⟨nonempty.mp x.1, x.2⟩), if_neg found]
      · rw [if_neg (fun x => found ⟨nonempty.mp x.1, x.2⟩)]; simp [Word]
  -- The authority and the position of the path.
  obtain ⟨pathStart, pathStartRun, authorityIs, afterAuthority, startLe, pathStartLe, authorityInside⟩ :
      ∃ pathStart : Usize,
      (if decide ([47, 47] <+: Word (bytes.val.drop start.val)) then
        (do let i ← start + 2#usize; references.scan bytes i 2#u8) else ok start) = ok pathStart ∧
      (authorityPart (Word (bytes.val.drop start.val))).1 = (if [47, 47] <+: Word (bytes.val.drop start.val)
        then some (Slice bytes.val (start.val + 2) pathStart.val) else none) ∧
      (authorityPart (Word (bytes.val.drop start.val))).2 = Word (bytes.val.drop pathStart.val) ∧
      start.val ≤ pathStart.val ∧ pathStart.val ≤ bytes.val.length ∧
      ([47, 47] <+: Word (bytes.val.drop start.val) → start.val + 2 ≤ pathStart.val) := by
    unfold authorityPart
    by_cases found : [47, 47] <+: Word (bytes.val.drop start.val)
    · have long := found.length_le
      simp only [Word, List.length_map, List.length_drop, List.length_cons, List.length_nil] at long
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := start) (y := 2#usize) (by scalar_tac))
      have nextIs : next.val = start.val + 2 := by simpa using nextValue
      obtain ⟨r, run, low, high, takes, drops⟩ := scan_spec bytes next 2#u8 (by omega)
      simp only [show (2#u8 : U8).val = 2 from rfl, continues_authority, nextIs] at takes drops low
      refine ⟨r, by simp [found, advance, run], ?_, ?_, by omega, high, fun _ => low⟩
      · rw [if_pos found, if_pos found, word_drop_two, takes]
      · rw [if_pos found, word_drop_two, drops]
    · refine ⟨start, by simp [found], ?_, ?_, le_refl _, afterScheme.2, fun x => absurd x found⟩
      · rw [if_neg found, if_neg found]
      · rw [if_neg found]
  -- The path.
  obtain ⟨pathEnd, pathEndRun, pathLow, pathEndLe, pathTakes, pathDrops⟩ := scan_spec bytes pathStart 1#u8 pathStartLe
  simp only [show (1#u8 : U8).val = 1 from rfl, continues_path] at pathTakes pathDrops
  -- The query and the position after it.
  obtain ⟨queryEnd, queryEndRun, queryIs, afterQuery, queryLow, queryEndLe, queryInside⟩ : ∃ queryEnd : Usize,
      (if decide ((Word (bytes.val.drop pathEnd.val)).head? = some 63) then
        (do let i ← pathEnd + 1#usize; references.scan bytes i 0#u8) else ok pathEnd) = ok queryEnd ∧
      (queryPart (Word (bytes.val.drop pathEnd.val))).1 = (if (Word (bytes.val.drop pathEnd.val)).head? = some 63
        then some (Slice bytes.val (pathEnd.val + 1) queryEnd.val) else none) ∧
      (queryPart (Word (bytes.val.drop pathEnd.val))).2 = Word (bytes.val.drop queryEnd.val) ∧
      pathEnd.val ≤ queryEnd.val ∧ queryEnd.val ≤ bytes.val.length ∧
      ((Word (bytes.val.drop pathEnd.val)).head? = some 63 → pathEnd.val + 1 ≤ queryEnd.val) := by
    unfold queryPart
    by_cases found : (Word (bytes.val.drop pathEnd.val)).head? = some 63
    · have inside := word_head_some found
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := pathEnd) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = pathEnd.val + 1 := by simpa using nextValue
      obtain ⟨r, run, low, high, takes, drops⟩ := scan_spec bytes next 0#u8 (by omega)
      simp only [show (0#u8 : U8).val = 0 from rfl, continues_query, nextIs] at takes drops low
      refine ⟨r, by simp [found, advance, run], ?_, ?_, by omega, high, fun _ => low⟩
      · rw [if_pos found, if_pos found, word_drop_tail, takes]
      · rw [if_pos found, word_drop_tail, drops]
    · refine ⟨pathEnd, by simp [found], ?_, ?_, le_refl _, pathEndLe, fun x => absurd x found⟩
      · rw [if_neg found, if_neg found]
      · rw [if_neg found]
  -- The fragment: what follows the query is empty or begins with `#`.
  have fragmentShape : queryEnd.val < bytes.val.length →
      (Word (bytes.val.drop queryEnd.val)).head? = some 35 := by
    intro more
    rw [word_drop_cons more]
    simp only [List.head?_cons, Option.some.injEq]
    by_cases question : (Word (bytes.val.drop pathEnd.val)).head? = some 63
    · unfold queryPart at afterQuery
      rw [if_pos question] at afterQuery
      simp only at afterQuery
      have stop := drop_while_stops (p := QueryChar) (w := (Word (bytes.val.drop pathEnd.val)).tail)
        (rest := Word (bytes.val.drop (queryEnd.val + 1))) (by rw [afterQuery, word_drop_cons more])
      simpa [QueryChar] using stop
    · unfold queryPart at afterQuery
      rw [if_neg question] at afterQuery
      have same : queryEnd = pathEnd := by
        simp only [question, decide_false, Bool.false_eq_true, if_false] at queryEndRun
        exact (Result.ok_injective queryEndRun).symm
      subst same
      have stop := drop_while_stops (p := PathChar) (w := Word (bytes.val.drop pathStart.val))
        (rest := Word (bytes.val.drop (queryEnd.val + 1))) (by rw [pathDrops, word_drop_cons more])
      simp only [PathChar, Bool.not_eq_false', Bool.or_eq_true, beq_iff_eq] at stop
      rcases stop with q | f
      · exfalso; apply question; rw [word_drop_cons more, q]; rfl
      · exact f
  -- The actual function.
  obtain ⟨o, oRun, oIs⟩ : ∃ o, (if decide (0 < colon.val ∧ (Word (bytes.val.drop colon.val)).head? = some 58) then
      ok (some ({ start := 0#usize, «end» := colon } : references.Span)) else ok none) = ok o ∧
      ((0 < colon.val ∧ (Word (bytes.val.drop colon.val)).head? = some 58) ∧
          o = some { start := 0#usize, «end» := colon } ∨
        ¬ (0 < colon.val ∧ (Word (bytes.val.drop colon.val)).head? = some 58) ∧ o = none) := by
    by_cases found : 0 < colon.val ∧ (Word (bytes.val.drop colon.val)).head? = some 58
    · exact ⟨_, by simp [found], Or.inl ⟨found, rfl⟩⟩
    · exact ⟨_, by simp [found], Or.inr ⟨found, rfl⟩⟩
  obtain ⟨o1, o1Run, o1Is⟩ : ∃ o1, (if decide ([47, 47] <+: Word (bytes.val.drop start.val)) then
      (do let i1 ← start + 2#usize; ok (some ({ start := i1, «end» := pathStart } : references.Span))) else ok none) =
        ok o1 ∧
      (([47, 47] <+: Word (bytes.val.drop start.val) ∧ ∃ i1 : Usize, i1.val = start.val + 2 ∧
          o1 = some { start := i1, «end» := pathStart }) ∨
        (¬ ([47, 47] <+: Word (bytes.val.drop start.val)) ∧ o1 = none)) := by
    by_cases found : [47, 47] <+: Word (bytes.val.drop start.val)
    · have bound := authorityInside found
      obtain ⟨i1, advance, i1Value⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := start) (y := 2#usize) (by scalar_tac))
      exact ⟨_, by simp [found, advance], Or.inl ⟨found, i1, by simpa using i1Value, rfl⟩⟩
    · exact ⟨_, by simp [found], Or.inr ⟨found, rfl⟩⟩
  obtain ⟨o2, o2Run, o2Is⟩ : ∃ o2, (if decide ((Word (bytes.val.drop pathEnd.val)).head? = some 63) then
      (do let i1 ← pathEnd + 1#usize; ok (some ({ start := i1, «end» := queryEnd } : references.Span))) else ok none) =
        ok o2 ∧
      (((Word (bytes.val.drop pathEnd.val)).head? = some 63 ∧ ∃ i1 : Usize, i1.val = pathEnd.val + 1 ∧
          o2 = some { start := i1, «end» := queryEnd }) ∨
        (¬ (Word (bytes.val.drop pathEnd.val)).head? = some 63 ∧ o2 = none)) := by
    by_cases found : (Word (bytes.val.drop pathEnd.val)).head? = some 63
    · have bound := queryInside found
      obtain ⟨i1, advance, i1Value⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := pathEnd) (y := 1#usize) (by scalar_tac))
      exact ⟨_, by simp [found, advance], Or.inl ⟨found, i1, by simpa using i1Value, rfl⟩⟩
    · exact ⟨_, by simp [found], Or.inr ⟨found, rfl⟩⟩
  let record : Option references.Span → references.Parts := fun last =>
    { scheme := o, authority := o1, path := { start := pathStart, «end» := pathEnd }, query := o2, fragment := last }
  obtain ⟨last, lastRun, lastIs⟩ : ∃ last : Option references.Span,
      (if queryEnd < alloc.vec.Vec.len bytes then
        (queryEnd + 1#usize >>= fun i1 => ok (record (some { start := i1, «end» := alloc.vec.Vec.len bytes })))
        else ok (record none)) = ok (record last) ∧
      ((queryEnd.val < bytes.val.length ∧ ∃ i1 : Usize, i1.val = queryEnd.val + 1 ∧
          last = some { start := i1, «end» := alloc.vec.Vec.len bytes }) ∨
        (¬ queryEnd.val < bytes.val.length ∧ last = none)) := by
    by_cases more : queryEnd.val < bytes.val.length
    · obtain ⟨i1, advance, i1Value⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := queryEnd) (y := 1#usize) (by scalar_tac))
      exact ⟨_, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, advance],
        Or.inl ⟨more, i1, by simpa using i1Value, rfl⟩⟩
    · exact ⟨_, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more], Or.inr ⟨more, rfl⟩⟩
  refine ⟨record last, ?_, ?_, ?_⟩
  · rw [references.split]
    have v63 : (63#u8 : U8).val = 63 := rfl
    simp only [colonRun, bind_ok, scheme_ends_spec, startRun, double_slash_spec, pathStartRun, pathEndRun,
      byte_is_spec, v63, queryEndRun, oRun, o1Run, o2Run]
    exact lastRun
  · refine ⟨?_, ?_, ⟨pathLow, pathEndLe⟩, ?_, ?_⟩
    · intro s found
      rcases oIs with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · cases found; exact ⟨by simp, colonLe⟩
      · cases found
    · intro s found
      rcases o1Is with ⟨present, i1, i1Value, rfl⟩ | ⟨_, rfl⟩
      · cases found; exact ⟨by rw [i1Value]; exact authorityInside present, pathStartLe⟩
      · cases found
    · intro s found
      rcases o2Is with ⟨present, i1, i1Value, rfl⟩ | ⟨_, rfl⟩
      · cases found; exact ⟨by rw [i1Value]; exact queryInside present, queryEndLe⟩
      · cases found
    · intro s found
      rcases lastIs with ⟨more, i1, i1Value, rfl⟩ | ⟨_, rfl⟩
      · cases found; exact ⟨by rw [i1Value]; simp [alloc.vec.Vec.len_val]; omega, by simp [alloc.vec.Vec.len_val]⟩
      · cases found
  · unfold split view
    simp only []
    rw [schemeIs, afterScheme.1, authorityIs, afterAuthority, pathTakes, pathDrops, queryIs, afterQuery]
    have fragmentSpec : fragmentPart (Word (bytes.val.drop queryEnd.val)) =
        last.map (fun s => Slice bytes.val s.start.val s.end.val) := by
      unfold fragmentPart
      rcases lastIs with ⟨more, i1, i1Value, rfl⟩ | ⟨atEnd, rfl⟩
      · rw [if_pos (fragmentShape more)]
        simp only [Option.map_some, i1Value, alloc.vec.Vec.len_val, slice_all, word_drop_tail]
      · have empty : bytes.val.drop queryEnd.val = [] := List.drop_eq_nil_of_le (by omega)
        simp [empty, Word]
    rw [fragmentSpec]
    congr 1
    · rcases oIs with ⟨found, rfl⟩ | ⟨found, rfl⟩
      · rw [if_pos found]; simp [record]
      · rw [if_neg found]; simp [record]
    · rcases o1Is with ⟨found, i1, i1Value, rfl⟩ | ⟨found, rfl⟩
      · rw [if_pos found]; simp [record, i1Value]
      · rw [if_neg found]; simp [record]
    · rcases o2Is with ⟨found, i1, i1Value, rfl⟩ | ⟨found, rfl⟩
      · rw [if_pos found]; simp [record, i1Value]
      · rw [if_neg found]; simp [record]

/-! ### Dot-segment removal -/

private theorem slice_length (bytes : List U8) (i j : Nat) (fits : j ≤ bytes.length) :
    (Slice bytes i j).length = j - i := by
  simp [Slice, Word]; omega

private theorem prefix_two {a b : Nat} {l : List Nat} : [a, b] <+: l ↔ l[0]? = some a ∧ l[1]? = some b := by
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> (simp; try omega)
private theorem prefix_three {a b c : Nat} {l : List Nat} :
    [a, b, c] <+: l ↔ l[0]? = some a ∧ l[1]? = some b ∧ l[2]? = some c := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩ <;> (simp; try omega)
private theorem prefix_four {a b c d : Nat} {l : List Nat} :
    [a, b, c, d] <+: l ↔ l[0]? = some a ∧ l[1]? = some b ∧ l[2]? = some c ∧ l[3]? = some d := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, t⟩⟩⟩⟩ <;> (simp; try omega)
private theorem eq_one {a : Nat} {l : List Nat} : l = [a] ↔ l[0]? = some a ∧ l.length = 1 := by
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> (simp; try omega)
private theorem eq_two {a b : Nat} {l : List Nat} : l = [a, b] ↔ (l[0]? = some a ∧ l[1]? = some b) ∧ l.length = 2 := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩ <;> (simp; try omega)
private theorem eq_three {a b c : Nat} {l : List Nat} :
    l = [a, b, c] ↔ (l[0]? = some a ∧ l[1]? = some b ∧ l[2]? = some c) ∧ l.length = 3 := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, t⟩⟩⟩⟩ <;> (simp; try omega)

private theorem get_bound {l : List Nat} {k v : Nat} (found : l[k]? = some v) : k < l.length := by
  by_contra outside
  rw [List.getElem?_eq_none (by omega)] at found
  cases found

theorem starts2_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (a b : U8)
    (fits : finish.val ≤ bytes.val.length) :
    references.starts2 bytes index finish a b =
      .ok (decide ((Slice bytes.val index.val finish.val)[0]? = some a.val ∧
        (Slice bytes.val index.val finish.val)[1]? = some b.val)) := by
  unfold references.starts2
  rw [at_spec bytes index finish a fits]
  by_cases first : (Slice bytes.val index.val finish.val)[0]? = some a.val
  · have bound := get_bound first
    rw [slice_length _ _ _ fits] at bound
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    simp [first, advance, at_spec bytes next finish b fits, nextIs, slice_at]
  · simp [first]

theorem starts3_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (a b c : U8)
    (fits : finish.val ≤ bytes.val.length) :
    references.starts3 bytes index finish a b c =
      .ok (decide ((Slice bytes.val index.val finish.val)[0]? = some a.val ∧
        (Slice bytes.val index.val finish.val)[1]? = some b.val ∧
        (Slice bytes.val index.val finish.val)[2]? = some c.val)) := by
  unfold references.starts3
  rw [starts2_spec bytes index finish a b fits]
  by_cases first : (Slice bytes.val index.val finish.val)[0]? = some a.val ∧
      (Slice bytes.val index.val finish.val)[1]? = some b.val
  · have bound := get_bound first.2
    rw [slice_length _ _ _ fits] at bound
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 2#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 2 := by simpa using nextValue
    simp [first, advance, at_spec bytes next finish c fits, nextIs, slice_at]
  · have notAll : ¬ ((Slice bytes.val index.val finish.val)[0]? = some a.val ∧
        (Slice bytes.val index.val finish.val)[1]? = some b.val ∧
        (Slice bytes.val index.val finish.val)[2]? = some c.val) := fun x => first ⟨x.1, x.2.1⟩
    simp [first, notAll]

theorem starts4_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (a b c d : U8)
    (fits : finish.val ≤ bytes.val.length) :
    references.starts4 bytes index finish a b c d =
      .ok (decide ((Slice bytes.val index.val finish.val)[0]? = some a.val ∧
        (Slice bytes.val index.val finish.val)[1]? = some b.val ∧
        (Slice bytes.val index.val finish.val)[2]? = some c.val ∧
        (Slice bytes.val index.val finish.val)[3]? = some d.val)) := by
  unfold references.starts4
  rw [starts3_spec bytes index finish a b c fits]
  by_cases first : (Slice bytes.val index.val finish.val)[0]? = some a.val ∧
      (Slice bytes.val index.val finish.val)[1]? = some b.val ∧ (Slice bytes.val index.val finish.val)[2]? = some c.val
  · have bound := get_bound first.2.2
    rw [slice_length _ _ _ fits] at bound
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 3#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 3 := by simpa using nextValue
    simp [first, advance, at_spec bytes next finish d fits, nextIs, slice_at]
  · have notAll : ¬ ((Slice bytes.val index.val finish.val)[0]? = some a.val ∧
        (Slice bytes.val index.val finish.val)[1]? = some b.val ∧
        (Slice bytes.val index.val finish.val)[2]? = some c.val ∧
        (Slice bytes.val index.val finish.val)[3]? = some d.val) := fun x => first ⟨x.1, x.2.1, x.2.2.1⟩
    simp [first, notAll]

theorem is1_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (a : U8)
    (fits : finish.val ≤ bytes.val.length) :
    references.is1 bytes index finish a = .ok (decide ((Slice bytes.val index.val finish.val)[0]? = some a.val ∧
      (Slice bytes.val index.val finish.val).length = 1)) := by
  unfold references.is1
  rw [at_spec bytes index finish a fits, slice_length _ _ _ fits]
  by_cases first : (Slice bytes.val index.val finish.val)[0]? = some a.val
  · have bound := get_bound first
    rw [slice_length _ _ _ fits] at bound
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    simp only [first, decide_true, advance, bind_ok, if_true, true_and]
    congr 1
    simp only [UScalar.eq_equiv, nextIs]
    rw [decide_eq_decide]
    omega
  · simp [first]

theorem is2_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (a b : U8)
    (fits : finish.val ≤ bytes.val.length) :
    references.is2 bytes index finish a b = .ok (decide (((Slice bytes.val index.val finish.val)[0]? = some a.val ∧
      (Slice bytes.val index.val finish.val)[1]? = some b.val) ∧ (Slice bytes.val index.val finish.val).length = 2)) := by
  unfold references.is2
  rw [starts2_spec bytes index finish a b fits, slice_length _ _ _ fits]
  by_cases first : (Slice bytes.val index.val finish.val)[0]? = some a.val ∧
      (Slice bytes.val index.val finish.val)[1]? = some b.val
  · have bound := get_bound first.2
    rw [slice_length _ _ _ fits] at bound
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 2#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 2 := by simpa using nextValue
    simp only [first, and_self, decide_true, advance, bind_ok, if_true, true_and]
    congr 1
    simp only [UScalar.eq_equiv, nextIs]
    rw [decide_eq_decide]
    omega
  · have notAll : ¬ (((Slice bytes.val index.val finish.val)[0]? = some a.val ∧
        (Slice bytes.val index.val finish.val)[1]? = some b.val) ∧ finish.val - index.val = 2) := fun x => first x.1
    simp [first, notAll]

theorem is3_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (a b c : U8)
    (fits : finish.val ≤ bytes.val.length) :
    references.is3 bytes index finish a b c =
      .ok (decide (((Slice bytes.val index.val finish.val)[0]? = some a.val ∧
        (Slice bytes.val index.val finish.val)[1]? = some b.val ∧
        (Slice bytes.val index.val finish.val)[2]? = some c.val) ∧ (Slice bytes.val index.val finish.val).length = 3)) := by
  unfold references.is3
  rw [starts3_spec bytes index finish a b c fits, slice_length _ _ _ fits]
  by_cases first : (Slice bytes.val index.val finish.val)[0]? = some a.val ∧
      (Slice bytes.val index.val finish.val)[1]? = some b.val ∧ (Slice bytes.val index.val finish.val)[2]? = some c.val
  · have bound := get_bound first.2.2
    rw [slice_length _ _ _ fits] at bound
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 3#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 3 := by simpa using nextValue
    simp only [first, and_self, decide_true, advance, bind_ok, if_true, true_and]
    congr 1
    simp only [UScalar.eq_equiv, nextIs]
    rw [decide_eq_decide]
    omega
  · have notAll : ¬ (((Slice bytes.val index.val finish.val)[0]? = some a.val ∧
        (Slice bytes.val index.val finish.val)[1]? = some b.val ∧
        (Slice bytes.val index.val finish.val)[2]? = some c.val) ∧ finish.val - index.val = 3) := fun x => first x.1
    simp [first, notAll]

theorem exhausted_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (fits : finish.val ≤ bytes.val.length) :
    references.exhausted bytes index finish = .ok (decide (Slice bytes.val index.val finish.val = [])) := by
  unfold references.exhausted
  have empty : Slice bytes.val index.val finish.val = [] ↔ finish.val ≤ index.val := by
    rw [← List.length_eq_zero_iff, slice_length _ _ _ fits]; omega
  by_cases done : finish.val ≤ index.val
  · simp [UScalar.le_equiv, done, empty.mpr done]
  · have notEmpty : ¬ Slice bytes.val index.val finish.val = [] := fun x => done (empty.mp x)
    simp [UScalar.le_equiv, done, notEmpty, alloc.vec.Vec.len_val, UScalar.lt_equiv]
    omega

/-- The step of RFC 3986 section 5.2.4 that applies to an input buffer, by its
    first characters and its length. -/
def rule (input : List Nat) : references.Step :=
  if input = [] then .Finish
  else if input[0]? = some 46 ∧ input[1]? = some 46 ∧ input[2]? = some 47 then .RemoveParent
  else if input[0]? = some 46 ∧ input[1]? = some 47 then .RemoveCurrent
  else if input[0]? = some 47 ∧ input[1]? = some 46 ∧ input[2]? = some 47 then .SkipCurrent
  else if (input[0]? = some 47 ∧ input[1]? = some 46) ∧ input.length = 2 then .FinalCurrent
  else if input[0]? = some 47 ∧ input[1]? = some 46 ∧ input[2]? = some 46 ∧ input[3]? = some 47 then .SkipParent
  else if (input[0]? = some 47 ∧ input[1]? = some 46 ∧ input[2]? = some 46) ∧ input.length = 3 then .FinalParent
  else if input[0]? = some 46 ∧ input.length = 1 then .DropDots
  else if (input[0]? = some 46 ∧ input[1]? = some 46) ∧ input.length = 2 then .DropDots
  else .MoveSegment

theorem step_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (fits : finish.val ≤ bytes.val.length) :
    references.step bytes index finish = .ok (rule (Slice bytes.val index.val finish.val)) := by
  unfold references.step rule
  have v46 : (46#u8 : U8).val = 46 := rfl
  have v47 : (47#u8 : U8).val = 47 := rfl
  simp only [exhausted_spec bytes index finish fits, starts2_spec bytes index finish _ _ fits,
    starts3_spec bytes index finish _ _ _ fits, starts4_spec bytes index finish _ _ _ _ fits,
    is1_spec bytes index finish _ fits, is2_spec bytes index finish _ _ fits, is3_spec bytes index finish _ _ _ fits,
    bind_ok, v46, v47, decide_eq_true_eq]
  split_ifs <;> rfl

private theorem final_dots (o : List Nat) : removeDots [47] o = o ++ [47] := by
  rw [removeDots]
  simp [firstSegment]
  rw [removeDots]
  simp

/-- Unfolding `removeDots` by its applicable step. -/
private theorem remove_dots_rule (input output : List Nat) : removeDots input output =
    match rule input with
    | .Finish => output
    | .RemoveParent => removeDots (input.drop 3) output
    | .RemoveCurrent => removeDots (input.drop 2) output
    | .SkipCurrent => removeDots (47 :: input.drop 3) output
    | .FinalCurrent => output ++ [47]
    | .SkipParent => removeDots (47 :: input.drop 4) (popSegment output)
    | .FinalParent => popSegment output ++ [47]
    | .DropDots => output
    | .MoveSegment => removeDots (input.drop (firstSegment input).length) (output ++ firstSegment input) := by
  rw [removeDots]
  unfold rule
  rcases input with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩
  · simp
  all_goals simp only [List.cons_prefix_cons, List.nil_prefix, List.prefix_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.getElem?_nil, List.length_cons, List.length_nil, List.cons.injEq,
    Option.some.injEq, reduceCtorEq, and_true, true_and, and_false, false_and, List.cons_ne_nil, not_false_eq_true,
    _root_.dite_true, _root_.dite_false, if_false, Nat.reduceAdd, zero_add, reduceIte, or_false, false_or, and_self,
    List.prefix_cons_iff]
  all_goals split_ifs <;> simp_all [final_dots]

private theorem bne_slash (x : U8) : (x != 47#u8) = !decide (x.val = 47) := by
  have same : (x == 47#u8) = decide (x.val = 47) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq, UScalar.eq_equiv]
    rfl
  simp [bne, same]

theorem inside_segment_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (fits : finish.val ≤ bytes.val.length) :
    references.inside_segment bytes index finish =
      .ok (decide (∃ c, (Slice bytes.val index.val finish.val)[0]? = some c ∧ c ≠ 47)) := by
  unfold references.inside_segment
  rw [before_spec]
  by_cases more : index.val < finish.val
  · have inside : index.val < bytes.val.length := by omega
    rw [slice_cons more fits]
    simp [more, inside, lookup inside, bne_slash]
  · rw [slice_empty _ (by omega)]
    simp [more]

/-- The first `/` from `index` before `finish`, or `finish`. -/
theorem segment_end_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (fits : finish.val ≤ bytes.val.length)
    (order : index.val ≤ finish.val) :
    ∃ stop, references.segment_end bytes index finish = .ok stop ∧ index.val ≤ stop.val ∧ stop.val ≤ finish.val ∧
      (Slice bytes.val index.val finish.val).takeWhile (· != 47) = Slice bytes.val index.val stop.val ∧
      (Slice bytes.val index.val finish.val).dropWhile (· != 47) = Slice bytes.val stop.val finish.val := by
  rw [references.segment_end, inside_segment_spec bytes index finish fits]
  by_cases more : index.val < finish.val
  · have whole := slice_cons more fits
    by_cases slash : bytes.val[index.val].val = 47
    · have stops : ¬ ∃ c, (Slice bytes.val index.val finish.val)[0]? = some c ∧ c ≠ 47 := by
        rw [whole]; simp [slash]
      refine ⟨index, by simp [stops], le_refl _, order, ?_, ?_⟩
      · rw [whole, slice_empty _ (le_refl _)]; simp [slash]
      · rw [whole]; simp [slash]
    · have passes : ∃ c, (Slice bytes.val index.val finish.val)[0]? = some c ∧ c ≠ 47 := by
        rw [whole]; simp [slash]
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨stop, run, low, high, takes, drops⟩ := segment_end_spec bytes next finish fits (by omega)
      rw [nextIs] at low takes drops
      refine ⟨stop, by simp [passes, advance, run], by omega, high, ?_, ?_⟩
      · rw [whole, List.takeWhile_cons_of_pos (by simpa using slash), takes,
          slice_cons (i := index.val) (j := stop.val) (by omega) (by omega)]
      · rw [whole, List.dropWhile_cons_of_pos (by simpa using slash), drops]
  · have stops : ¬ ∃ c, (Slice bytes.val index.val finish.val)[0]? = some c ∧ c ≠ 47 := by
      rw [slice_empty _ (by omega)]; simp
    refine ⟨index, by simp [stops], le_refl _, order, ?_, ?_⟩
    · rw [slice_empty _ (by omega), slice_empty _ (le_refl _)]; rfl
    · rw [slice_empty _ (by omega)]; rfl
termination_by finish.val - index.val
decreasing_by omega

theorem searching_spec (bytes : alloc.vec.Vec U8) (start index : Usize) :
    references.searching bytes start index =
      .ok (decide (start.val < index.val ∧ index.val ≤ bytes.val.length)) := by
  unfold references.searching
  by_cases first : start.val < index.val <;>
    simp [UScalar.lt_equiv, UScalar.le_equiv, alloc.vec.Vec.len_val, first]

/-- The last `/` of `bytes[start..index]`. -/
theorem last_slash_spec (bytes : alloc.vec.Vec U8) (start index : Usize) (order : start.val ≤ index.val)
    (fits : index.val ≤ bytes.val.length) :
    ∃ r, references.last_slash bytes start index = .ok r ∧
      ((r = none ∧ 47 ∉ Slice bytes.val start.val index.val) ∨
        ∃ k : Usize, r = some k ∧ start.val ≤ k.val ∧ k.val < index.val ∧
          Slice bytes.val start.val index.val = Slice bytes.val start.val k.val ++ 47 :: Slice bytes.val (k.val + 1) index.val ∧
          47 ∉ Slice bytes.val (k.val + 1) index.val) := by
  rw [references.last_slash, searching_spec]
  by_cases more : start.val < index.val
  · obtain ⟨previous, back, previousValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := index) (y := 1#usize) (by scalar_tac))
    have previousIs : previous.val = index.val - 1 := by simpa using previousValue.1
    have inside : previous.val < bytes.val.length := by omega
    have look : bytes.index_usize previous = .ok bytes.val[previous.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := slice_append (bytes := bytes.val) (i := start.val) (j := previous.val) (k := index.val)
      (by omega) (by omega)
    have last : Slice bytes.val previous.val index.val = [bytes.val[previous.val].val] := by
      rw [slice_cons (by omega) fits, show previous.val + 1 = index.val by omega, slice_empty _ (le_refl _)]
    by_cases slash : bytes.val[previous.val] = 47#u8
    · have slashValue : bytes.val[previous.val].val = 47 := by rw [slash]; rfl
      refine ⟨some previous, by simp [more, fits, back, lookup inside, look, slash], Or.inr ⟨previous, rfl, by omega, by omega,
        ?_, ?_⟩⟩
      · rw [split, last, slashValue, show previous.val + 1 = index.val by omega, slice_empty _ (le_refl _)]
      · rw [show previous.val + 1 = index.val by omega, slice_empty _ (le_refl _)]; simp
    · have notSlash : bytes.val[previous.val].val ≠ 47 := fun same => slash (UScalar.eq_of_val_eq same)
      obtain ⟨r, run, found⟩ := last_slash_spec bytes start previous (by omega) (by omega)
      refine ⟨r, by simp [more, fits, back, lookup inside, look, slash, run], ?_⟩
      rcases found with ⟨rfl, free⟩ | ⟨k, rfl, low, high, parts, free⟩
      · refine Or.inl ⟨rfl, ?_⟩
        rw [split, last]
        simp [free, Ne.symm notSlash]
      · refine Or.inr ⟨k, rfl, low, by omega, ?_, ?_⟩
        · rw [split, parts, last, slice_append (bytes := bytes.val) (i := k.val + 1) (j := previous.val) (k := index.val)
            (by omega) (by omega), last]
          simp
        · rw [slice_append (bytes := bytes.val) (i := k.val + 1) (j := previous.val) (k := index.val) (by omega)
            (by omega), last]
          simp [free, Ne.symm notSlash]
  · have empty : Slice bytes.val start.val index.val = [] := slice_empty _ (by omega)
    exact ⟨none, by simp [more], Or.inl ⟨rfl, by simp [empty]⟩⟩
termination_by index.val - start.val
decreasing_by omega

theorem pop_segment_spec (out : alloc.vec.Vec U8) :
    ∃ v, references.pop_segment out = .ok v ∧ Word v.val = popSegment (Word out.val) ∧
      v.val.length ≤ out.val.length := by
  unfold references.pop_segment
  have lenIs : (alloc.vec.Vec.len out).val = out.val.length := alloc.vec.Vec.len_val out
  obtain ⟨r, run, found⟩ := last_slash_spec out 0#usize (alloc.vec.Vec.len out) (by simp) (by omega)
  rw [lenIs, show (0#usize : Usize).val = 0 from rfl] at found
  have whole : Word out.val = Slice out.val 0 out.val.length := by rw [slice_all]; rfl
  rcases found with ⟨rfl, free⟩ | ⟨k, rfl, _, high, parts, free⟩
  · refine ⟨alloc.vec.Vec.new U8, by simp [run], ?_, by simp⟩
    rw [whole, pop_free free]; rfl
  · have size := out.property
    obtain ⟨v, appended, contents, length⟩ := append_spec out 0#usize k (alloc.vec.Vec.new U8) (by omega)
      (by rw [show (alloc.vec.Vec.new U8).val = [] from rfl]; simp; omega)
    refine ⟨v, by simp [run, appended], ?_, by rw [length]; simp; omega⟩
    rw [whole, parts, pop_last free, contents]
    simp [Word]

/-- Facts about the input buffer that each step of `rule` uses. -/
private theorem rule_facts {input : List Nat} :
    (rule input = .Finish → input = []) ∧
    (rule input = .RemoveParent → 3 ≤ input.length) ∧
    (rule input = .RemoveCurrent → 2 ≤ input.length) ∧
    (rule input = .SkipCurrent → 3 ≤ input.length ∧ input[2]? = some 47) ∧
    (rule input = .FinalCurrent → input.length = 2) ∧
    (rule input = .SkipParent → 4 ≤ input.length ∧ input[3]? = some 47) ∧
    (rule input = .FinalParent → input.length = 3) ∧
    (rule input = .MoveSegment → input ≠ []) := by
  unfold rule
  rcases input with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩
  · simp
  all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.length_cons,
    List.length_nil, Option.some.injEq, reduceCtorEq, and_true, true_and, and_false, false_and, List.cons_ne_nil,
    not_false_eq_true, if_false, Nat.reduceAdd, zero_add, reduceIte, ne_eq]
  all_goals split_ifs <;> simp_all

/-- `references::remove_dots` removes the dot segments of its input buffer as
    RFC 3986 section 5.2.4 does. -/
theorem remove_dots_total_correct (bytes : alloc.vec.Vec U8) (index finish : Usize) (out : alloc.vec.Vec U8)
    (fits : finish.val ≤ bytes.val.length) (room : out.val.length + (finish.val - index.val) ≤ Usize.max) :
    ∃ v, references.remove_dots bytes index finish out = .ok v ∧
      Word v.val = removeDots (Slice bytes.val index.val finish.val) (Word out.val) ∧
      v.val.length ≤ out.val.length + (finish.val - index.val) := by
  obtain ⟨finishRule, parentRule, currentRule, skipRule, finalSkipRule, backRule, finalBackRule, moveRule⟩ :=
    rule_facts (input := Slice bytes.val index.val finish.val)
  have length := slice_length bytes.val index.val finish.val fits
  rw [references.remove_dots, step_spec bytes index finish fits, remove_dots_rule]
  simp only [bind_ok]
  cases found : rule (Slice bytes.val index.val finish.val) with
  | Finish => exact ⟨out, rfl, rfl, by omega⟩
  | RemoveParent =>
    have long := parentRule found
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 3#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 3 := by simpa using nextValue
    obtain ⟨v, run, value, bound⟩ := remove_dots_total_correct bytes next finish out fits (by omega)
    refine ⟨v, by simp [advance, run], ?_, by omega⟩
    rw [value, nextIs, slice_drop]
  | RemoveCurrent =>
    have long := currentRule found
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 2#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 2 := by simpa using nextValue
    obtain ⟨v, run, value, bound⟩ := remove_dots_total_correct bytes next finish out fits (by omega)
    refine ⟨v, by simp [advance, run], ?_, by omega⟩
    rw [value, nextIs, slice_drop]
  | SkipCurrent =>
    obtain ⟨long, slash⟩ := skipRule found
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 2#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 2 := by simpa using nextValue
    obtain ⟨v, run, value, bound⟩ := remove_dots_total_correct bytes next finish out fits (by omega)
    refine ⟨v, by simp [advance, run], ?_, by omega⟩
    rw [value, nextIs, slice_drop]
    have : (Slice bytes.val index.val finish.val).drop 2 = 47 :: (Slice bytes.val index.val finish.val).drop 3 := by
      rw [List.drop_eq_getElem_cons (by omega)]
      congr 1
      have := List.getElem?_eq_getElem (l := Slice bytes.val index.val finish.val) (i := 2) (by omega)
      rw [slash] at this
      exact (Option.some.inj this).symm
    rw [this]
  | FinalCurrent =>
    have two := finalSkipRule found
    obtain ⟨v, put, contents⟩ := put_spec out 47#u8 (by omega)
    exact ⟨v, put, by rw [contents]; simp [Word], by rw [contents]; simp; omega⟩
  | SkipParent =>
    obtain ⟨long, slash⟩ := backRule found
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 3#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 3 := by simpa using nextValue
    obtain ⟨popped, pop, popValue, popLength⟩ := pop_segment_spec out
    obtain ⟨v, run, value, bound⟩ := remove_dots_total_correct bytes next finish popped fits (by omega)
    refine ⟨v, by simp [advance, pop, run], ?_, by omega⟩
    rw [value, nextIs, slice_drop, popValue]
    have : (Slice bytes.val index.val finish.val).drop 3 = 47 :: (Slice bytes.val index.val finish.val).drop 4 := by
      rw [List.drop_eq_getElem_cons (by omega)]
      congr 1
      have := List.getElem?_eq_getElem (l := Slice bytes.val index.val finish.val) (i := 3) (by omega)
      rw [slash] at this
      exact (Option.some.inj this).symm
    rw [this]
  | FinalParent =>
    have three := finalBackRule found
    obtain ⟨popped, pop, popValue, popLength⟩ := pop_segment_spec out
    obtain ⟨v, put, contents⟩ := put_spec popped 47#u8 (by omega)
    exact ⟨v, by simp [pop, put], by rw [contents]; simp [Word] at popValue ⊢; rw [popValue],
      by rw [contents]; simp; omega⟩
  | DropDots => exact ⟨out, rfl, rfl, by omega⟩
  | MoveSegment =>
    have nonempty := moveRule found
    have more : index.val < finish.val := by
      by_contra done
      exact nonempty (slice_empty _ (by omega))
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨stop, segment, low, high, takes, drops⟩ := segment_end_spec bytes next finish fits (by omega)
    rw [nextIs] at low takes drops
    obtain ⟨moved, append, movedValue, movedLength⟩ := append_spec bytes index stop out (by omega) (by omega)
    obtain ⟨v, run, value, bound⟩ := remove_dots_total_correct bytes stop finish moved fits (by omega)
    have first : firstSegment (Slice bytes.val index.val finish.val) = Slice bytes.val index.val stop.val := by
      rw [slice_cons more fits, slice_cons (i := index.val) (j := stop.val) (by omega) (by omega)]
      by_cases slash : bytes.val[index.val].val = 47
      · rw [slash]
        simp only [firstSegment, takes]
      · rw [first_segment_cons slash, takes]
    refine ⟨v, by simp [advance, segment, append, run], ?_, by omega⟩
    dsimp only
    rw [value, movedValue, first, slice_length _ _ _ (by omega : stop.val ≤ bytes.val.length),
      ← slice_drop, show index.val + (stop.val - index.val) = stop.val by omega]
termination_by finish.val - index.val
decreasing_by all_goals omega

/-! ### Merging, recomposition and the transformed reference -/

private theorem usize_max_large : 4294967295 ≤ Usize.max := by
  simp only [Usize.max, Usize.numBits]
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

private theorem slice_bound (bytes : List U8) (s : references.Span) (inside : Inside bytes s) :
    s.end.val - s.start.val ≤ bytes.length := by
  have := inside.2; omega

/-- The bytes `component` appends: `before` and the span, when the span is defined. -/
def Piece (bytes : List U8) (before : Nat) : Option references.Span → List Nat
  | some s => before :: Slice bytes s.start.val s.end.val
  | none => []

theorem component_spec (bytes : alloc.vec.Vec U8) (span : Option references.Span) (before : U8)
    (out : alloc.vec.Vec U8) (inside : ∀ s, span = some s → Inside bytes.val s)
    (room : out.val.length + 1 + bytes.val.length ≤ Usize.max) :
    ∃ v, references.component bytes span before out = .ok v ∧
      Word v.val = Word out.val ++ Piece bytes.val before.val span ∧
      v.val.length ≤ out.val.length + 1 + bytes.val.length := by
  unfold references.component
  cases span with
  | none => exact ⟨out, rfl, by simp [Piece], by omega⟩
  | some s =>
    have bound := slice_bound bytes.val s (inside s rfl)
    obtain ⟨put, putRun, putValue⟩ := put_spec out before (by omega)
    obtain ⟨v, run, value, length⟩ := append_spec bytes s.start s.end put (inside s rfl).2
      (by rw [putValue]; simp; omega)
    refine ⟨v, by simp [putRun, run], ?_, by rw [length, putValue]; simp; omega⟩
    rw [value, putValue]
    simp [Word, Piece]

/-- The bytes `authority` appends: `//` and the span, when the span is defined. -/
theorem authority_spec (bytes : alloc.vec.Vec U8) (span : Option references.Span) (out : alloc.vec.Vec U8)
    (inside : ∀ s, span = some s → Inside bytes.val s)
    (room : out.val.length + 2 + bytes.val.length ≤ Usize.max) :
    ∃ v, references.authority bytes span out = .ok v ∧
      Word v.val = Word out.val ++ authorityPiece (span.map (fun s => Slice bytes.val s.start.val s.end.val)) ∧
      v.val.length ≤ out.val.length + 2 + bytes.val.length := by
  unfold references.authority
  cases span with
  | none => exact ⟨out, rfl, by simp [authorityPiece], by omega⟩
  | some s =>
    have bound := slice_bound bytes.val s (inside s rfl)
    obtain ⟨put1, put1Run, put1Value⟩ := put_spec out 47#u8 (by omega)
    obtain ⟨put2, put2Run, put2Value⟩ := put_spec put1 47#u8 (by rw [put1Value]; simp; omega)
    obtain ⟨v, run, value, length⟩ := append_spec bytes s.start s.end put2 (inside s rfl).2
      (by rw [put2Value, put1Value]; simp; omega)
    refine ⟨v, by simp [put1Run, put2Run, run], ?_, by rw [length, put2Value, put1Value]; simp; omega⟩
    rw [value, put2Value, put1Value]
    simp [Word, authorityPiece]

theorem bare_authority_spec (b : references.Parts) :
    references.bare_authority b = .ok (decide (b.authority.isSome ∧ b.path.end.val ≤ b.path.start.val)) := by
  unfold references.bare_authority
  cases found : b.authority <;> simp [core.option.Option.is_some, found, UScalar.le_equiv]

theorem clean_path_spec (bytes : alloc.vec.Vec U8) (span : references.Span) (inside : Inside bytes.val span)
    (out : alloc.vec.Vec U8) (room : out.val.length + bytes.val.length ≤ Usize.max) :
    ∃ v, references.clean_path bytes span out = .ok v ∧
      Word v.val = Word out.val ++ removeDots (Slice bytes.val span.start.val span.end.val) [] ∧
      v.val.length ≤ out.val.length + bytes.val.length := by
  unfold references.clean_path
  have bound := slice_bound bytes.val span inside
  obtain ⟨path, run, pathValue, pathLength⟩ := remove_dots_total_correct bytes span.start span.end
    (alloc.vec.Vec.new U8) inside.2 (by rw [show (alloc.vec.Vec.new U8).val = [] from rfl]; simp; omega)
  rw [show (alloc.vec.Vec.new U8).val = [] from rfl] at pathValue pathLength
  simp only [List.length_nil, zero_add] at pathLength
  have lenIs : (alloc.vec.Vec.len path).val = path.val.length := alloc.vec.Vec.len_val path
  obtain ⟨v, appended, value, length⟩ := append_spec path 0#usize (alloc.vec.Vec.len path) out (by omega)
    (by rw [lenIs]; simp; omega)
  refine ⟨v, by simp [run, appended], ?_, by rw [length, lenIs]; simp; omega⟩
  rw [value, lenIs, show (0#usize : Usize).val = 0 from rfl, slice_all, List.drop_zero, pathValue]
  rfl

theorem merge_spec (base : alloc.vec.Vec U8) (b : references.Parts) (bInside : SpansInside base.val b)
    (reference : alloc.vec.Vec U8) (path : references.Span) (pathInside : Inside reference.val path)
    (room : base.val.length + reference.val.length + 1 ≤ Usize.max) :
    ∃ v, references.merge base b reference path = .ok v ∧
      Word v.val = merge (view base.val b) (Slice reference.val path.start.val path.end.val) ∧
      v.val.length ≤ base.val.length + reference.val.length + 1 := by
  unfold references.merge merge
  rw [bare_authority_spec]
  have pathBound := slice_bound reference.val path pathInside
  have basePath := bInside.2.2.1
  obtain ⟨baseStartLe, baseEndLe⟩ := basePath
  obtain ⟨refStartLe, refEndLe⟩ := pathInside
  have emptyPath : (view base.val b).path = [] ↔ b.path.end.val ≤ b.path.start.val := by
    simp only [view]
    rw [← List.length_eq_zero_iff, slice_length _ _ _ baseEndLe]
    omega
  by_cases bare : b.authority.isSome ∧ b.path.end.val ≤ b.path.start.val
  · have bareView : (view base.val b).authority.isSome ∧ (view base.val b).path = [] :=
      ⟨by simpa [view] using bare.1, emptyPath.mpr bare.2⟩
    obtain ⟨slash, slashRun, slashValue⟩ := put_spec (alloc.vec.Vec.new U8) 47#u8
      (by rw [show (alloc.vec.Vec.new U8).val = [] from rfl]; simp; have := usize_max_large; omega)
    rw [show (alloc.vec.Vec.new U8).val = [] from rfl] at slashValue
    obtain ⟨v, run, value, length⟩ := append_spec reference path.start path.end slash refEndLe
      (by rw [slashValue]; simp; omega)
    refine ⟨v, by simp [bare, slashRun, run], ?_, by rw [length, slashValue]; simp; omega⟩
    rw [if_pos bareView, value, slashValue]
    simp [Word]
  · have notBare : ¬ ((view base.val b).authority.isSome ∧ (view base.val b).path = []) := by
      rw [emptyPath]; simpa [view] using bare
    rw [if_neg notBare]
    obtain ⟨r, slashRun, found⟩ := last_slash_spec base b.path.start b.path.end baseStartLe baseEndLe
    rcases found with ⟨rfl, free⟩ | ⟨k, rfl, low, high, parts, free⟩
    · obtain ⟨v, run, value, length⟩ := append_spec reference path.start path.end (alloc.vec.Vec.new U8)
        refEndLe (by rw [show (alloc.vec.Vec.new U8).val = [] from rfl]; simp; omega)
      refine ⟨v, by simp [bare, slashRun, run], ?_, by rw [length]; simp; omega⟩
      rw [value]
      simp only [view]
      rw [dir_free free]
      rfl
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = k.val + 1 := by simpa using nextValue
      obtain ⟨directory, dirRun, dirValue, dirLength⟩ := append_spec base b.path.start next (alloc.vec.Vec.new U8)
        (by omega) (by rw [show (alloc.vec.Vec.new U8).val = [] from rfl]; simp; omega)
      rw [show (alloc.vec.Vec.new U8).val = [] from rfl] at dirValue dirLength
      obtain ⟨v, run, value, length⟩ := append_spec reference path.start path.end directory refEndLe
        (by rw [dirLength]; simp; omega)
      refine ⟨v, by simp [bare, slashRun, advance, dirRun, run], ?_, by rw [length, dirLength]; simp; omega⟩
      rw [value, dirValue]
      simp only [view]
      rw [parts, dir_last free, nextIs, slice_append (bytes := base.val) (i := b.path.start.val) (j := k.val)
        (k := k.val + 1) (by omega) (by omega)]
      have one : Slice base.val k.val (k.val + 1) = [47] := by
        have whole := parts
        rw [slice_cons (i := k.val) (j := k.val + 1) (by omega) (by omega), slice_empty _ (le_refl _)]
        have split := slice_append (bytes := base.val) (i := b.path.start.val) (j := k.val) (k := b.path.end.val)
          (by omega) (by omega)
        rw [split, slice_cons (i := k.val) (j := b.path.end.val) (by omega) (by omega)] at whole
        simp at whole
        rw [whole]
      simp [Word, one]

private theorem word_append (a b : List U8) : Word (a ++ b) = Word a ++ Word b := List.map_append

private theorem piece_query (bytes : List U8) (span : Option references.Span) :
    Piece bytes (63#u8 : U8).val span = queryPiece (span.map (fun s => Slice bytes s.start.val s.end.val)) := by
  cases span <;> rfl

private theorem piece_fragment (bytes : List U8) (span : Option references.Span) :
    Piece bytes (35#u8 : U8).val span = fragmentPiece (span.map (fun s => Slice bytes s.start.val s.end.val)) := by
  cases span <;> rfl

theorem relative_path_spec (base : alloc.vec.Vec U8) (b : references.Parts) (bInside : SpansInside base.val b)
    (reference : alloc.vec.Vec U8) (r : references.Parts) (rInside : SpansInside reference.val r)
    (rScheme : r.scheme = none) (rAuthority : r.authority = none) (out : alloc.vec.Vec U8)
    (room : out.val.length + 3 * base.val.length + 2 * reference.val.length + 4 ≤ Usize.max) :
    ∃ v, references.relative_path base b reference r out = .ok v ∧
      Word v.val = Word out.val ++ (authorityPiece (transform (view base.val b) (view reference.val r)).authority ++
        ((transform (view base.val b) (view reference.val r)).path ++
          queryPiece (transform (view base.val b) (view reference.val r)).query)) ∧
      v.val.length ≤ out.val.length + 3 * base.val.length + 2 * reference.val.length + 4 := by
  obtain ⟨_, bAuthority, bPath, bQuery, _⟩ := bInside
  obtain ⟨_, _, rPath, rQuery, _⟩ := rInside
  obtain ⟨rStartLe, rEndLe⟩ := rPath
  obtain ⟨bStartLe, bEndLe⟩ := bPath
  have usize := usize_max_large
  unfold references.relative_path
  obtain ⟨out1, authorityRun, authorityValue, authorityLength⟩ := authority_spec base b.authority out bAuthority
    (by omega)
  have noScheme : ¬ (view reference.val r).scheme.isSome := by simp [view, rScheme]
  have noAuthority : ¬ (view reference.val r).authority.isSome := by simp [view, rAuthority]
  have emptyPath : (view reference.val r).path = [] ↔ r.path.end.val ≤ r.path.start.val := by
    simp only [view]
    rw [← List.length_eq_zero_iff, slice_length _ _ _ rEndLe]
    omega
  unfold transform
  rw [if_neg noScheme, if_neg noAuthority]
  by_cases empty : r.path.end.val ≤ r.path.start.val
  · rw [if_pos (emptyPath.mpr empty)]
    obtain ⟨out2, appendRun, appendValue, appendLength⟩ := append_spec base b.path.start b.path.end out1 bEndLe
      (by omega)
    by_cases ownQuery : r.query.isSome
    · obtain ⟨v, run, value, length⟩ := component_spec reference r.query 63#u8 out2 rQuery (by omega)
      refine ⟨v, by simp [authorityRun, UScalar.le_equiv, empty, appendRun, core.option.Option.is_some, ownQuery, run],
        ?_, by omega⟩
      rw [value, appendValue, authorityValue, piece_query, if_pos (by simpa [view] using ownQuery)]
      simp [view]
    · obtain ⟨v, run, value, length⟩ := component_spec base b.query 63#u8 out2 bQuery (by omega)
      have noQuery : r.query = none := by simpa using ownQuery
      refine ⟨v, by simp [authorityRun, UScalar.le_equiv, empty, appendRun, core.option.Option.is_some, noQuery, run],
        ?_, by omega⟩
      rw [value, appendValue, authorityValue, piece_query, if_neg (by simpa [view] using ownQuery)]
      simp [view]
  · rw [if_neg (fun x => empty (emptyPath.mp x))]
    have more : r.path.start.val < r.path.end.val := by omega
    have headIs : (view reference.val r).path.head? = (Word (reference.val.drop r.path.start.val)).head? := by
      simp only [view]
      rw [slice_cons more rEndLe, word_drop_cons (by omega)]
      rfl
    by_cases rooted : (Word (reference.val.drop r.path.start.val)).head? = some 47
    · rw [if_pos (by rw [headIs]; exact rooted)]
      obtain ⟨out2, cleanRun, cleanValue, cleanLength⟩ := clean_path_spec reference r.path ⟨rStartLe, rEndLe⟩ out1
        (by omega)
      obtain ⟨v, run, value, length⟩ := component_spec reference r.query 63#u8 out2 rQuery (by omega)
      refine ⟨v, by simp [authorityRun, UScalar.le_equiv, empty, byte_is_spec, rooted, cleanRun, run], ?_, by omega⟩
      rw [value, cleanValue, authorityValue, piece_query]
      simp [view]
    · rw [if_neg (by rw [headIs]; exact rooted)]
      have bInside' : SpansInside base.val b := ⟨by assumption, bAuthority, ⟨bStartLe, bEndLe⟩, bQuery, by assumption⟩
      obtain ⟨merged, mergeRun, mergeValue, mergeLength⟩ := merge_spec base b bInside' reference r.path
        ⟨rStartLe, rEndLe⟩ (by omega)
      have lenIs : (alloc.vec.Vec.len merged).val = merged.val.length := alloc.vec.Vec.len_val merged
      obtain ⟨out2, cleanRun, cleanValue, cleanLength⟩ := clean_path_spec merged
        ⟨0#usize, alloc.vec.Vec.len merged⟩ ⟨by simp, by rw [lenIs]⟩ out1 (by omega)
      obtain ⟨v, run, value, length⟩ := component_spec reference r.query 63#u8 out2 rQuery (by omega)
      have v47 : (47#u8 : U8).val = 47 := rfl
      refine ⟨v, by simp [authorityRun, UScalar.le_equiv, empty, byte_is_spec, v47, rooted, mergeRun, cleanRun, run],
        ?_, by omega⟩
      rw [value, cleanValue, authorityValue, piece_query]
      simp only [lenIs, show (0#usize : Usize).val = 0 from rfl, slice_all, List.drop_zero]
      rw [show Word merged.val = merge (view base.val b) (view reference.val r).path from mergeValue]
      simp [view]

theorem absolute_spec (reference : alloc.vec.Vec U8) (own : references.Span) (r : references.Parts)
    (found : r.scheme = some own) (rInside : SpansInside reference.val r)
    (small : reference.val.length < Usize.max / 8) (base : Parts) :
    ∃ v, references.absolute reference own r = .ok v ∧
      Word v.val = compose (transform base (view reference.val r)) := by
  have usize := usize_max_large
  obtain ⟨rScheme, rAuthority, rPath, rQuery, rFragment⟩ := rInside
  have ownInside := rScheme own found
  have ownBound := slice_bound reference.val own ownInside
  unfold references.absolute
  rw [compose_pieces]
  obtain ⟨v0, run0, value0, length0⟩ := append_spec reference own.start own.end (alloc.vec.Vec.new U8) ownInside.2
    (by rw [show (alloc.vec.Vec.new U8).val = [] from rfl]; simp; omega)
  rw [show (alloc.vec.Vec.new U8).val = [] from rfl] at value0 length0
  obtain ⟨out, putRun, putValue⟩ := put_spec v0 58#u8 (by rw [length0]; simp; omega)
  have outLength : out.val.length = (own.end.val - own.start.val) + 1 := by rw [putValue]; simp [length0]
  obtain ⟨out1, run1, value1, length1⟩ := authority_spec reference r.authority out rAuthority (by omega)
  obtain ⟨out2, run2, value2, length2⟩ := clean_path_spec reference r.path rPath out1 (by omega)
  obtain ⟨out3, run3, value3, length3⟩ := component_spec reference r.query 63#u8 out2 rQuery (by omega)
  obtain ⟨v, run4, value4, length4⟩ := component_spec reference r.fragment 35#u8 out3 rFragment (by omega)
  refine ⟨v, by simp [run0, putRun, run1, run2, run3, run4], ?_⟩
  have isSome : (view reference.val r).scheme.isSome := by simp [view, found]
  unfold transform
  rw [if_pos isSome]
  rw [value4, value3, value2, value1, putValue, word_append, value0, piece_query, piece_fragment]
  simp [view, found, schemePiece, Word]

theorem relative_spec (base : alloc.vec.Vec U8) (b : references.Parts) (bInside : SpansInside base.val b)
    (scheme : references.Span) (found : b.scheme = some scheme) (reference : alloc.vec.Vec U8) (r : references.Parts)
    (rInside : SpansInside reference.val r) (ownScheme : r.scheme = none)
    (small : base.val.length < Usize.max / 8 ∧ reference.val.length < Usize.max / 8) :
    ∃ v, references.relative base b scheme reference r = .ok v ∧
      Word v.val = compose (transform (view base.val b) (view reference.val r)) := by
  have usize := usize_max_large
  obtain ⟨bScheme, bAuthority, bPath, bQuery, bFragment⟩ := bInside
  obtain ⟨rScheme, rAuthority, rPath, rQuery, rFragment⟩ := rInside
  have schemeInside := bScheme scheme found
  have schemeBound := slice_bound base.val scheme schemeInside
  unfold references.relative
  rw [compose_pieces]
  obtain ⟨v0, run0, value0, length0⟩ := append_spec base scheme.start scheme.end (alloc.vec.Vec.new U8)
    schemeInside.2 (by rw [show (alloc.vec.Vec.new U8).val = [] from rfl]; simp; omega)
  rw [show (alloc.vec.Vec.new U8).val = [] from rfl] at value0 length0
  obtain ⟨out, putRun, putValue⟩ := put_spec v0 58#u8 (by rw [length0]; simp; omega)
  have outLength : out.val.length ≤ base.val.length + 1 := by rw [putValue]; simp [length0]; omega
  have noScheme : ¬ (view reference.val r).scheme.isSome := by simp [view, ownScheme]
  by_cases ownAuthority : r.authority.isSome
  · obtain ⟨out1, run1, value1, length1⟩ := authority_spec reference r.authority out rAuthority (by omega)
    obtain ⟨out2, run2, value2, length2⟩ := clean_path_spec reference r.path rPath out1 (by omega)
    obtain ⟨target, run3, value3, length3⟩ := component_spec reference r.query 63#u8 out2 rQuery (by omega)
    obtain ⟨v, run4, value4, length4⟩ := component_spec reference r.fragment 35#u8 target rFragment (by omega)
    refine ⟨v, by simp [run0, putRun, core.option.Option.is_some, ownAuthority, run1, run2, run3, run4], ?_⟩
    unfold transform
    rw [if_neg noScheme, if_pos (by simpa [view] using ownAuthority)]
    rw [value4, value3, value2, value1, putValue, word_append, value0, piece_query, piece_fragment]
    simp [view, found, schemePiece, Word]
  · have noAuthority : r.authority = none := by simpa using ownAuthority
    obtain ⟨target, run1, value1, length1⟩ := relative_path_spec base b ⟨bScheme, bAuthority, bPath, bQuery, bFragment⟩
      reference r ⟨rScheme, rAuthority, rPath, rQuery, rFragment⟩ ownScheme noAuthority out (by omega)
    obtain ⟨v, run4, value4, length4⟩ := component_spec reference r.fragment 35#u8 target rFragment (by omega)
    refine ⟨v, by simp [run0, putRun, core.option.Option.is_some, noAuthority, run1, run4], ?_⟩
    rw [value4, value1, putValue, word_append, value0, piece_fragment]
    have fragmentIs : (transform (view base.val b) (view reference.val r)).fragment =
        r.fragment.map (fun s => Slice reference.val s.start.val s.end.val) := by
      unfold transform
      rw [if_neg noScheme, if_neg (by simpa [view] using ownAuthority)]
      split_ifs <;> rfl
    have schemeIs : (transform (view base.val b) (view reference.val r)).scheme =
        some (Slice base.val scheme.start.val scheme.end.val) := by
      unfold transform
      rw [if_neg noScheme, if_neg (by simpa [view] using ownAuthority)]
      split_ifs <;> simp [view, found]
    rw [fragmentIs, schemeIs]
    simp [schemePiece, Word]

theorem small_spec (base reference : alloc.vec.Vec U8) :
    references.small base reference =
      .ok (decide (base.val.length < Usize.max / 8 ∧ reference.val.length < Usize.max / 8)) := by
  unfold references.small
  obtain ⟨q, div, qValue⟩ := UScalar.div_spec core.num.Usize.MAX (y := 8#usize) (by simp)
  have maxVal : (core.num.Usize.MAX).val = Usize.max := by simp [core.num.Usize.MAX]
  rw [maxVal] at qValue
  by_cases first : base.val.length < Usize.max / 8 <;>
    simp [div, alloc.vec.Vec.len_val, UScalar.lt_equiv, qValue, first]

/-- `references::resolve` resolves by RFC 3986 section 5.2: when both inputs are
    shorter than `usize::MAX / 8` bytes, its result is exactly `resolve` of
    their bytes (none when neither has a scheme), and otherwise none. -/
theorem resolve_total_correct (base reference : alloc.vec.Vec U8) :
    ∃ result, references.resolve base reference = .ok result ∧
      result.map (fun v => Word v.val) =
        if base.val.length < Usize.max / 8 ∧ reference.val.length < Usize.max / 8 then
          resolve (Word base.val) (Word reference.val) else none := by
  unfold references.resolve
  rw [small_spec]
  by_cases fits : base.val.length < Usize.max / 8 ∧ reference.val.length < Usize.max / 8
  · obtain ⟨b, splitBase, bInside, bView⟩ := split_total_correct base
    obtain ⟨r, splitReference, rInside, rView⟩ := split_total_correct reference
    rw [if_pos fits]
    unfold resolve
    rw [← bView, ← rView]
    cases ownScheme : r.scheme with
    | some own =>
      obtain ⟨v, absoluteRun, value⟩ := absolute_spec reference own r ownScheme rInside fits.2 (view base.val b)
      refine ⟨some v, by simp [fits, splitReference, ownScheme, absoluteRun], ?_⟩
      rw [if_pos (Or.inl (by simp [view, ownScheme]))]
      simp [value]
    | none =>
      cases baseScheme : b.scheme with
      | none =>
        refine ⟨none, by simp [fits, splitReference, ownScheme, splitBase, baseScheme], ?_⟩
        rw [if_neg (by simp [view, ownScheme, baseScheme])]
        rfl
      | some scheme =>
        obtain ⟨v, relativeRun, value⟩ := relative_spec base b bInside scheme baseScheme reference r rInside ownScheme fits
        refine ⟨some v, by simp [fits, splitReference, ownScheme, splitBase, baseScheme, relativeRun], ?_⟩
        rw [if_pos (Or.inr (by simp [view, baseScheme]))]
        simp [value]
  · exact ⟨none, by simp [fits], by simp [fits]⟩

/-- For the UTF-8 bytes of an IRI and of an IRI reference, each shorter than
    `usize::MAX / 8` bytes, `references::resolve` returns the UTF-8 bytes of an
    IRI whose Appendix B components are exactly the RFC 3986 section 5.2.2
    target components of their characters, provided the target has an
    authority or a path that does not begin with `//` (see
    `IriResolution.resolve_leaves_iri`). -/
theorem resolve_utf8_iri (base reference : alloc.vec.Vec U8) {b r : List Nat}
    (baseText : Rowl.Regular.Utf8From base.val 0 b) (baseIri : b ∈ Rowl.Iri.IriLanguage)
    (referenceText : Rowl.Regular.Utf8From reference.val 0 r) (referenceIri : r ∈ Rowl.Iri.ReferenceLanguage)
    (fits : base.val.length < Usize.max / 8 ∧ reference.val.length < Usize.max / 8)
    (plain : (transform (split b) (split r)).authority.isSome ∨ ¬ [47, 47] <+: (transform (split b) (split r)).path) :
    ∃ v, references.resolve base reference = .ok (some v) ∧
      ∃ t, Rowl.Regular.Utf8From v.val 0 t ∧ t ∈ Rowl.Iri.IriLanguage ∧ split t = transform (split b) (split r) := by
  obtain ⟨result, run, value⟩ := resolve_total_correct base reference
  rw [if_pos fits] at value
  obtain ⟨t, resolved, iri, parts⟩ := resolve_iri baseIri referenceIri plain
  obtain ⟨bytes, decoded⟩ := resolve_bytes baseText referenceText
  have wordBytes : resolve (Word base.val) (Word reference.val) = some (t.flatMap utf8) := by
    unfold Word; rw [bytes, resolved]; rfl
  rw [wordBytes] at value
  cases result with
  | none => simp at value
  | some v =>
    refine ⟨v, run, ?_⟩
    simp only [Option.map_some, Option.some.injEq] at value
    have target : resolve (Word base.val) (Word reference.val) = some (Word v.val) := by
      rw [wordBytes, value]
    obtain ⟨t', resolved', text⟩ := decoded v.val target
    rw [resolved] at resolved'
    cases resolved'
    exact ⟨t, text, iri, parts⟩

/-! ### Recognizing IRI references -/

/-- An ASCII letter, digit, `-`, `.`, `_` or `~`. -/
def PlainByte (n : Nat) : Prop :=
  (65 ≤ n ∧ n ≤ 90) ∨ (97 ≤ n ∧ n ≤ 122) ∨ (48 ≤ n ∧ n ≤ 57) ∨ n = 45 ∨ n = 46 ∨ n = 95 ∨ n = 126

theorem plain_spec (byte : U8) : references.plain byte = .ok (decide (PlainByte byte.val)) := by
  have key : ∃ b, references.plain byte = .ok b ∧ (b = true ↔ PlainByte byte.val) := by
    unfold references.plain
    split_ifs <;> refine ⟨_, rfl, ?_⟩ <;>
      simp [UScalar.le_equiv, UScalar.lt_equiv, UScalar.eq_equiv, PlainByte] at * <;> omega
  obtain ⟨b, run, iff⟩ := key
  rw [run]
  congr 1
  cases b <;> simp_all

theorem path_byte_spec (bytes : alloc.vec.Vec U8) (index : Usize) :
    references.path_byte bytes index =
      .ok (decide (∃ c, (Word (bytes.val.drop index.val)).head? = some c ∧ (PlainByte c ∨ c = 47))) := by
  unfold references.path_byte
  by_cases more : index.val < bytes.val.length
  · rw [word_drop_cons more]
    by_cases plain : PlainByte bytes.val[index.val].val
    · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup more, plain_spec, plain]
    · by_cases slash : bytes.val[index.val].val = 47
      · have slash' : bytes.val[index.val] = 47#u8 := UScalar.eq_of_val_eq slash
        simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup more, plain_spec, plain, slash, slash']
      · have slash' : ¬ bytes.val[index.val] = 47#u8 := fun same => slash (by rw [same]; rfl)
        simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup more, plain_spec, plain, slash, slash']
  · have empty : bytes.val.drop index.val = [] := List.drop_eq_nil_of_le (by omega)
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, empty, Word]

/-- The end of the plain bytes and slashes from `index`. -/
theorem plain_end_spec (bytes : alloc.vec.Vec U8) (index : Usize) (inside : index.val ≤ bytes.val.length) :
    ∃ e, references.plain_end bytes index = .ok e ∧ index.val ≤ e.val ∧ e.val ≤ bytes.val.length ∧
      (∀ c ∈ Slice bytes.val index.val e.val, PlainByte c ∨ c = 47) ∧
      (∀ c, (Word (bytes.val.drop e.val)).head? = some c → ¬ (PlainByte c ∨ c = 47)) := by
  rw [references.plain_end, path_byte_spec]
  by_cases more : ∃ c, (Word (bytes.val.drop index.val)).head? = some c ∧ (PlainByte c ∨ c = 47)
  · obtain ⟨c, head, good⟩ := more
    have inBounds := word_head_some head
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨e, run, low, high, all, stop⟩ := plain_end_spec bytes next (by omega)
    rw [nextIs] at low all
    have found : ∃ c, (Word (bytes.val.drop index.val)).head? = some c ∧ (PlainByte c ∨ c = 47) := ⟨c, head, good⟩
    refine ⟨e, by simp [found, advance, run], by omega, high, ?_, stop⟩
    rw [slice_cons (by omega) high]
    rw [word_drop_cons inBounds] at head
    simp only [List.head?_cons, Option.some.injEq] at head
    intro d member
    rcases List.mem_cons.mp member with rfl | rest
    · rw [head]; exact good
    · exact all d rest
  · refine ⟨index, by simp [more], le_refl _, inside, by rw [slice_empty _ (le_refl _)]; simp, ?_⟩
    intro c head good
    exact more ⟨c, head, good⟩
termination_by bytes.val.length - index.val
decreasing_by omega

/-- Plain bytes and slashes, optionally followed by `#` and plain bytes and
    slashes. -/
def PlainRelative (w : List Nat) : Prop :=
  ∃ p f, (∀ c ∈ p, PlainByte c ∨ c = 47) ∧ (∀ c ∈ f, PlainByte c ∨ c = 47) ∧
    (w = p ∨ w = p ++ 35 :: f)

theorem plain_relative_spec (bytes : alloc.vec.Vec U8) :
    ∃ b, references.plain_relative bytes = .ok b ∧ (b = true → PlainRelative (Word bytes.val)) := by
  unfold references.plain_relative
  obtain ⟨e, run, _, high, all, stop⟩ := plain_end_spec bytes 0#usize (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl] at all
  have whole : Word bytes.val = Slice bytes.val 0 e.val ++ Word (bytes.val.drop e.val) := by
    rw [← word_drop_slice (Nat.zero_le _)]; rfl
  by_cases more : e.val < bytes.val.length
  · have look := lookup more
    have look2 : bytes.index_usize e = .ok bytes.val[e.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    by_cases hash : bytes.val[e.val] = 35#u8
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := e) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = e.val + 1 := by simpa using nextValue
      obtain ⟨e2, run2, low2, high2, all2, stop2⟩ := plain_end_spec bytes next (by omega)
      rw [nextIs] at low2 all2
      refine ⟨decide (e2 = alloc.vec.Vec.len bytes), by simp [run, alloc.vec.Vec.len_val, UScalar.lt_equiv, more,
        look, look2, hash, advance, run2], fun done => ⟨Slice bytes.val 0 e.val, Slice bytes.val (e.val + 1) e2.val, all,
        all2, Or.inr ?_⟩⟩
      have atEnd : e2.val = bytes.val.length := by
        have := of_decide_eq_true done
        rw [this]; simp [alloc.vec.Vec.len_val]
      rw [whole, word_drop_cons more, show bytes.val[e.val].val = 35 by rw [hash]; rfl, ← slice_all, ← atEnd]
    · refine ⟨false, by simp [run, alloc.vec.Vec.len_val, UScalar.lt_equiv, more, look, look2, hash], by simp⟩
  · have atEnd : e.val = bytes.val.length := by omega
    refine ⟨true, by simp [run, alloc.vec.Vec.len_val, UScalar.lt_equiv, more], fun _ =>
      ⟨Slice bytes.val 0 e.val, [], all, by simp, Or.inl ?_⟩⟩
    rw [whole, atEnd]
    simp [Word]

private theorem mem_take_while {p : Nat → Bool} {l : List Nat} {c : Nat} (member : c ∈ l.takeWhile p) : c ∈ l :=
  (List.takeWhile_prefix p).subset member

private theorem mem_drop_while {p : Nat → Bool} {l : List Nat} {c : Nat} (member : c ∈ l.dropWhile p) : c ∈ l :=
  (List.dropWhile_suffix p).subset member

private theorem plain_ipchar {c : Nat} (plain : PlainByte c) : [c] ∈ Rowl.Iri.Ipchar := by
  unfold Rowl.Iri.Ipchar Rowl.Iri.Iunreserved Rowl.Iri.Unreserved Rowl.Iri.Alpha Rowl.Iri.Digit Rowl.Iri.Ch
  unfold PlainByte at plain
  simp only [Language.mem_add]
  rcases plain with upper | lower | digit | dash | dot | underscore | tilde
  · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨c, rfl, upper.1, upper.2⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨c, rfl, lower.1, lower.2⟩)))
  · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨c, rfl, digit.1, digit.2⟩)))
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨c, rfl, by omega, by omega⟩))))
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl, by omega, by omega⟩)))))
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl, by omega, by omega⟩))))))
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rfl, by omega, by omega⟩))))))

private theorem chars_star {C : Language Nat} {w : List Nat} (each : ∀ c ∈ w, [c] ∈ C) : w ∈ C∗ := by
  induction w with
  | nil => exact Language.nil_mem_kstar C
  | cons c rest ih =>
    have : c :: rest = [c] ++ rest := rfl
    rw [this]
    exact star_cons (each c (by simp)) (ih (fun d member => each d (by simp [member])))

private theorem plain_segment {s : List Nat} (plain : ∀ c ∈ s, PlainByte c) : s ∈ Rowl.Iri.Segment := by
  unfold Rowl.Iri.Segment
  exact chars_star (fun c member => plain_ipchar (plain c member))

private theorem plain_pieces {p : List Nat} (plain : ∀ c ∈ p, PlainByte c ∨ c = 47) : Pieces p := by
  induction size : p.length using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    rcases last_slash_split p with free | ⟨u, v, rfl, free⟩
    · refine (pieces_free free).mpr (plain_segment (fun c member => ?_))
      rcases plain c member with good | slash
      · exact good
      · exact absurd (slash ▸ member) free
    · have shortU : u.length < n := by
        rw [← size]
        simp only [List.length_append, List.length_cons]
        omega
      have shortV : v.length < n := by
        rw [← size]
        simp only [List.length_append, List.length_cons]
        omega
      have plainU : ∀ c ∈ u, PlainByte c ∨ c = 47 := fun c member => plain c (by simp [member])
      have plainV : ∀ c ∈ v, PlainByte c ∨ c = 47 := fun c member => plain c (by simp [member])
      exact pieces_split.mpr ⟨ih u.length shortU plainU rfl, ih v.length shortV plainV rfl⟩

private theorem plain_fragment {f : List Nat} (plain : ∀ c ∈ f, PlainByte c ∨ c = 47) : f ∈ Rowl.Iri.Fragment := by
  unfold Rowl.Iri.Fragment
  refine chars_star (fun c member => ?_)
  simp only [Language.mem_add]
  rcases plain c member with good | rfl
  · exact Or.inl (plain_ipchar good)
  · exact Or.inr (Or.inl (ch_iff.mpr rfl))

private theorem plain_authority {a : List Nat} (plain : ∀ c ∈ a, PlainByte c) : a ∈ Rowl.Iri.Authority := by
  unfold Rowl.Iri.Authority
  have host : a ∈ Rowl.Iri.Host := by
    unfold Rowl.Iri.Host
    simp only [Language.mem_add]
    right; right
    show a ∈ (Rowl.Iri.Iunreserved + (Rowl.Iri.PctEncoded + Rowl.Iri.SubDelims))∗
    refine chars_star (fun c member => ?_)
    have := plain_ipchar (plain c member)
    unfold Rowl.Iri.Ipchar at this
    simp only [Language.mem_add] at this ⊢
    rcases this with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · unfold PlainByte at plain
      rcases h with h | h <;> obtain ⟨cp, same, low, high⟩ := h <;> cases same <;>
        have := plain c member <;> omega
  have := Language.append_mem_mul (optional_iff.mpr (Or.inl rfl) : [] ∈ Rowl.Iri.Optional (Rowl.Iri.Userinfo * Rowl.Iri.Ch 64))
    (Language.append_mem_mul host (optional_iff.mpr (Or.inl rfl) : [] ∈ Rowl.Iri.Optional (Rowl.Iri.Ch 58 * Rowl.Iri.Digit∗)))
  simpa using this

/-- Plain relative references are relative references of RFC 3987. -/
theorem plain_relative_reference {w : List Nat} (plain : PlainRelative w) : w ∈ Rowl.Iri.ReferenceLanguage := by
  obtain ⟨p, f, pPlain, fPlain, shape⟩ := plain
  have fragment : ∀ x, (if w = p then none else some f) = some x → x ∈ Rowl.Iri.Fragment := by
    intro x found
    split_ifs at found
    cases found
    exact plain_fragment fPlain
  have composed : ∀ q : Parts, q.scheme = none → q.query = none →
      q.fragment = (if w = p then none else some f) → authorityPiece q.authority ++ q.path = p → compose q = w := by
    intro q scheme query frag parts
    rw [compose_pieces, scheme, query, frag]
    simp only [schemePiece, queryPiece, List.nil_append]
    rw [← List.append_assoc, parts]
    rcases shape with same | withFragment
    · rw [if_pos same, same]; simp [fragmentPiece]
    · by_cases same : w = p
      · rw [if_pos same, same]; simp [fragmentPiece]
      · rw [if_neg same, withFragment]; rfl
  unfold Rowl.Iri.ReferenceLanguage
  rw [Language.mem_add]
  right
  by_cases double : [47, 47] <+: p
  · obtain ⟨rest, rfl⟩ := double
    have authorityPlain : ∀ c ∈ rest.takeWhile (· != 47), PlainByte c := by
      intro c member
      have notSlash := take_while_passes member
      rcases pPlain c (by simp [mem_take_while member]) with good | slash
      · exact good
      · simp [slash] at notSlash
    have pathRooted : Rooted (rest.dropWhile (· != 47)) := by
      cases tail : rest.dropWhile (· != 47) with
      | nil => exact Or.inl rfl
      | cons c more =>
        have := drop_while_stops tail
        right; simpa using this
    have pathPieces : Pieces (rest.dropWhile (· != 47)) :=
      plain_pieces (fun c member => pPlain c (by simp [mem_drop_while member]))
    have parts : RelativeParts ⟨none, some (rest.takeWhile (· != 47)), rest.dropWhile (· != 47), none,
        if w = [47, 47] ++ rest then none else some f⟩ :=
      ⟨rfl, ⟨plain_authority authorityPlain, path_tail_iff.mpr ⟨pathRooted, pathPieces⟩⟩, by simp, fragment⟩
    have := relative_compose parts
    rwa [composed _ rfl rfl rfl (by simp [authorityPiece, List.takeWhile_append_dropWhile])] at this
  · have pathIn : p ∈ Rowl.Iri.PathAbsolute + (Rowl.Iri.PathNoscheme + 1) := by
      simp only [Language.mem_add, Language.mem_one]
      by_cases empty : p = []
      · exact Or.inr (Or.inr empty)
      by_cases rooted : p.head? = some 47
      · left
        have any := iri_path_of (plain_pieces pPlain) double
        rcases (Language.mem_add _ _ _).mp any with absolute | other
        · exact absolute
        rcases (Language.mem_add _ _ _).mp other with rootless | none
        · exfalso
          unfold Rowl.Iri.PathRootless at rootless
          obtain ⟨seg, hseg, t, _, rfl⟩ := Language.mem_mul.mp rootless
          obtain ⟨c, cs, rfl, plainChar⟩ := segment_nz_head hseg
          simp at rooted
          omega
        · rw [Language.mem_one] at none; exact absurd none empty
      · right; left
        have whole := List.takeWhile_append_dropWhile (p := (· != 47)) (l := p)
        unfold Rowl.Iri.PathNoscheme
        rw [← whole]
        refine Language.append_mem_mul ?_ ?_
        · unfold Rowl.Iri.SegmentNzNc Rowl.Iri.Positive
          obtain ⟨c, more, cs⟩ := List.exists_cons_of_ne_nil empty
          have different : c ≠ 47 := by rw [cs] at rooted; simpa using rooted
          have plainHead : PlainByte c := by
            rcases pPlain c (by simp [cs]) with good | slash
            · exact good
            · exact absurd slash different
          rw [cs, List.takeWhile_cons_of_pos (by simpa using different)]
          have : c :: more.takeWhile (· != 47) = [c] ++ more.takeWhile (· != 47) := rfl
          rw [this]
          have each : ∀ d, PlainByte d → [d] ∈ Rowl.Iri.Iunreserved + (Rowl.Iri.PctEncoded +
              (Rowl.Iri.SubDelims + Rowl.Iri.Ch 64)) := by
            intro d good
            have := plain_ipchar good
            unfold Rowl.Iri.Ipchar at this
            simp only [Language.mem_add] at this ⊢
            rcases this with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · unfold PlainByte at good
              rcases h with h | h <;> obtain ⟨cp, same, low, high⟩ := h <;> cases same <;> omega
          refine Language.append_mem_mul (each c plainHead) (chars_star (fun d member => each d ?_))
          have notSlash := take_while_passes member
          rcases pPlain d (by simp [cs, mem_take_while member]) with good | slash
          · exact good
          · simp [slash] at notSlash
        · refine path_tail_iff.mpr ⟨?_, plain_pieces (fun c member => pPlain c (by
            simp [mem_drop_while member]))⟩
          cases tail : p.dropWhile (· != 47) with
          | nil => exact Or.inl rfl
          | cons c more =>
            have := drop_while_stops tail
            right; simpa using this
    have parts : RelativeParts ⟨none, none, p, none, if w = p then none else some f⟩ :=
      ⟨rfl, pathIn, by simp, fragment⟩
    have := relative_compose parts
    rwa [composed _ rfl rfl rfl (by simp [authorityPiece])] at this

private theorem ascii_text {bytes : List U8} (ascii : ∀ c ∈ Word bytes, c < 128) :
    Rowl.Regular.Utf8From bytes 0 (Word bytes) := by
  apply utf8_encoded
  · intro c member
    have := ascii c member
    unfold Rowl.Encoding.Scalar; omega
  · have : (Word bytes).flatMap utf8 = Word bytes := by
      have each : ∀ c ∈ Word bytes, utf8 c = [c] := by
        intro c member
        unfold utf8
        rw [if_pos (ascii c member)]
      clear ascii
      generalize Word bytes = w at each
      induction w with
      | nil => rfl
      | cons c rest ih =>
        rw [List.flatMap_cons, each c (by simp), ih (fun d member => each d (by simp [member]))]
        rfl
    rw [this]; rfl

private theorem plain_ascii {c : Nat} (plain : PlainByte c ∨ c = 47) : c < 128 := by
  unfold PlainByte at plain; omega

/-- `references::is_reference` accepts exactly the UTF-8 spellings of RFC 3987
    IRI references. -/
theorem is_reference_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ b, references.is_reference bytes = .ok b ∧
      (b = true ↔ ∃ w, Rowl.Regular.Utf8From bytes.val 0 w ∧ w ∈ Rowl.Iri.ReferenceLanguage) := by
  unfold references.is_reference
  obtain ⟨plain, plainRun, plainSound⟩ := plain_relative_spec bytes
  cases plain with
  | true =>
    refine ⟨true, by simp [plainRun], fun _ => ?_, fun _ => rfl⟩
    have shape := plainSound rfl
    refine ⟨Word bytes.val, ascii_text ?_, plain_relative_reference shape⟩
    obtain ⟨p, f, pPlain, fPlain, rfl | same⟩ := shape
    · intro c member; exact plain_ascii (pPlain c member)
    · intro c member
      rw [same] at member
      rcases List.mem_append.mp member with inP | inF
      · exact plain_ascii (pPlain c inP)
      · rcases List.mem_cons.mp inF with rfl | inF
        · omega
        · exact plain_ascii (fPlain c inF)
  | false =>
    obtain ⟨iriResult, iriRun, iriCorrect⟩ := Rowl.Iri.validate_iri_total_correct bytes
    have accepted := Rowl.Iri.validate_reference_accepted_iff bytes
    obtain ⟨referenceResult, referenceRun, _⟩ := Rowl.Iri.validate_reference_total_correct bytes
    rw [referenceRun] at accepted
    have viaReference : ∀ b : Bool, referenceResult = .Matched b →
        (b = true ↔ ∃ w, Rowl.Regular.Utf8From bytes.val 0 w ∧ w ∈ Rowl.Iri.ReferenceLanguage) := by
      intro b same
      subst same
      rw [← accepted]
      constructor
      · rintro rfl; rfl
      · intro equal
        have := Result.ok_injective equal
        cases this
        rfl
    have noReference : ∀ e, referenceResult = .MalformedUtf8 e →
        ¬ ∃ w, Rowl.Regular.Utf8From bytes.val 0 w ∧ w ∈ Rowl.Iri.ReferenceLanguage := by
      intro e same
      subst same
      rw [← accepted]
      intro equal
      have := Result.ok_injective equal
      cases this
    cases iriResult with
    | Matched b2 =>
      cases b2 with
      | true =>
        refine ⟨true, by simp [plainRun, iriRun], fun _ => ?_, fun _ => rfl⟩
        obtain ⟨w, text, iriAccepted⟩ := iriCorrect
        exact ⟨w, text, (Language.mem_add _ _ _).mpr (Or.inl (of_decide_eq_true iriAccepted.symm))⟩
      | false =>
        cases referenceResult with
        | Matched b3 =>
          exact ⟨b3, by simp [plainRun, iriRun, referenceRun]; cases b3 <;> rfl, viaReference b3 rfl⟩
        | MalformedUtf8 e =>
          exact ⟨false, by simp [plainRun, iriRun, referenceRun], by simpa using noReference e rfl⟩
    | MalformedUtf8 e' =>
      cases referenceResult with
      | Matched b3 =>
        exact ⟨b3, by simp [plainRun, iriRun, referenceRun]; cases b3 <;> rfl, viaReference b3 rfl⟩
      | MalformedUtf8 e =>
        exact ⟨false, by simp [plainRun, iriRun, referenceRun], by simpa using noReference e rfl⟩

end Rowl.References
