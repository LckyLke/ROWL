import Rowl.Encoding
import Rowl.Iri

/-!
Reference resolution by RFC 3986 section 5.2, as functions on words of
characters, written independently of the Rust code. A word is split into its
five components by the regular expression of RFC 3986 Appendix B (`split`); a
reference is transformed against a base by the strict algorithm of section
5.2.2 (`transform`), with paths merged as in section 5.2.3 (`merge`) and dot
segments removed as in section 5.2.4 (`removeDots`); the components are
recomposed as in section 5.3 (`compose`).

The algorithm inspects only the ASCII delimiters `#`, `.`, `/`, `:` and `?`.
`resolve_opaque` proves that it commutes with every spelling of characters that
keeps the delimiters and spells every other character as a nonempty word
without them, and UTF-8 is such a spelling (`utf8_opaque`), so resolving UTF-8
bytes is resolving their characters (RFC 3987 section 6.5).

Against the RFC 3987 grammar of `Iri.lean`: `iri_parts_iff` and
`reference_parts_iff` characterize IRIs and IRI references by their grammatical
components, and `split_iri`, `split_relative` prove that the Appendix B split
returns exactly those components. `resolve_iri` proves that resolving an IRI
reference against an IRI gives an IRI whenever the target has an authority or
its path does not begin with `//`; `resolve_leaves_iri` shows that this
condition cannot be dropped: the RFC algorithm resolves `/.//:a` against `a:b`
to `a://:a`, which is not an IRI.
-/
namespace Rowl.IriResolution
open Aeneas.Std Rowl.Iri
open scoped Computability
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-- The five components of RFC 3986 section 3 without their delimiters. An
    undefined component is `none` (RFC 3986 section 5.2.1); the path is always
    defined, possibly empty. -/
structure Parts where
  scheme : Option (List Nat)
  authority : Option (List Nat)
  path : List Nat
  query : Option (List Nat)
  fragment : Option (List Nat)

/-- `[^:/?#]` of Appendix B: a character that continues a scheme. -/
def SchemeChar (c : Nat) : Bool := !(c == 58 || c == 47 || c == 63 || c == 35)
/-- `[^/?#]`: a character that continues an authority. -/
def AuthorityChar (c : Nat) : Bool := !(c == 47 || c == 63 || c == 35)
/-- `[^?#]`: a character that continues a path. -/
def PathChar (c : Nat) : Bool := !(c == 63 || c == 35)
/-- `[^#]`: a character that continues a query. -/
def QueryChar (c : Nat) : Bool := !(c == 35)

/-- `(([^:/?#]+):)?` of Appendix B: the scheme, and the rest of the word. -/
def schemePart (w : List Nat) : Option (List Nat) × List Nat :=
  if w.takeWhile SchemeChar ≠ [] ∧ (w.dropWhile SchemeChar).head? = some 58 then
    (some (w.takeWhile SchemeChar), (w.dropWhile SchemeChar).tail)
  else (none, w)

/-- `(//([^/?#]*))?`: the authority, and the rest of the word. -/
def authorityPart (w : List Nat) : Option (List Nat) × List Nat :=
  if [47, 47] <+: w then (some ((w.drop 2).takeWhile AuthorityChar), (w.drop 2).dropWhile AuthorityChar)
  else (none, w)

/-- `(\?([^#]*))?`: the query, and the rest of the word. -/
def queryPart (w : List Nat) : Option (List Nat) × List Nat :=
  if w.head? = some 63 then (some (w.tail.takeWhile QueryChar), w.tail.dropWhile QueryChar)
  else (none, w)

/-- `(#(.*))?`: the fragment. -/
def fragmentPart (w : List Nat) : Option (List Nat) :=
  if w.head? = some 35 then some w.tail else none

/-- The components of a word by the regular expression of RFC 3986 Appendix B,
    `^(([^:/?#]+):)?(//([^/?#]*))?([^?#]*)(\?([^#]*))?(#(.*))?`. -/
def split (w : List Nat) : Parts :=
  let afterScheme := (schemePart w).2
  let afterAuthority := (authorityPart afterScheme).2
  let afterPath := afterAuthority.dropWhile PathChar
  { scheme := (schemePart w).1
    authority := (authorityPart afterScheme).1
    path := afterAuthority.takeWhile PathChar
    query := (queryPart afterPath).1
    fragment := fragmentPart (queryPart afterPath).2 }

/-- RFC 3986 section 5.3: the word of the components with their delimiters. -/
def compose (p : Parts) : List Nat :=
  (match p.scheme with | some s => s ++ [58] | none => []) ++
  (match p.authority with | some a => 47 :: 47 :: a | none => []) ++
  p.path ++
  (match p.query with | some q => 63 :: q | none => []) ++
  (match p.fragment with | some f => 35 :: f | none => [])

/-- The first segment of an input buffer with its leading `/`, if any, up to
    but not including the next `/` (step 2E of section 5.2.4). -/
def firstSegment : List Nat → List Nat
  | 47 :: rest => 47 :: rest.takeWhile (· != 47)
  | w => w.takeWhile (· != 47)

/-- An output buffer without its last segment and the `/` before it, if any
    (step 2C of section 5.2.4). -/
def popSegment (out : List Nat) : List Nat :=
  ((out.reverse.dropWhile (· != 47)).drop 1).reverse

theorem first_segment_cons {c : Nat} {rest : List Nat} (slash : c ≠ 47) :
    firstSegment (c :: rest) = c :: rest.takeWhile (· != 47) := by
  have keep : (c != 47) = true := by simp [slash]
  unfold firstSegment
  split
  · rename_i same; simp_all
  · simp [List.takeWhile, keep]

private theorem first_segment_length {input : List Nat} (nonempty : input ≠ []) :
    0 < (firstSegment input).length := by
  match input with
  | [] => exact absurd rfl nonempty
  | 47 :: rest => simp [firstSegment]
  | c :: rest =>
    by_cases slash : c = 47
    · subst slash; simp [firstSegment]
    · simp [first_segment_cons slash]

/-- RFC 3986 section 5.2.4: dot segments are removed from the input buffer
    while the remaining segments move to the output buffer, step by step:
    2A removes a leading `../` or `./`; 2B replaces a leading `/./`, or `/.`
    as a complete segment, by `/`; 2C does the same for `/../` and `/..` and
    removes the last segment of the output buffer; 2D removes an input
    buffer that is `.` or `..`; 2E moves the first segment. -/
def removeDots (input output : List Nat) : List Nat :=
  if _empty : input = [] then output
  else if _parent : [46, 46, 47] <+: input then removeDots (input.drop 3) output
  else if _current : [46, 47] <+: input then removeDots (input.drop 2) output
  else if _skip : [47, 46, 47] <+: input then removeDots (47 :: input.drop 3) output
  else if _finalSkip : input = [47, 46] then removeDots [47] output
  else if _back : [47, 46, 46, 47] <+: input then removeDots (47 :: input.drop 4) (popSegment output)
  else if _finalBack : input = [47, 46, 46] then removeDots [47] (popSegment output)
  else if input = [46] ∨ input = [46, 46] then output
  else removeDots (input.drop (firstSegment input).length) (output ++ firstSegment input)
termination_by input.length
decreasing_by
  all_goals first
    | (have := _parent.length_le; simp only [List.length_drop, List.length_cons, List.length_nil] at *; omega)
    | (have := _current.length_le; simp only [List.length_drop, List.length_cons, List.length_nil] at *; omega)
    | (have := _skip.length_le; simp only [List.length_drop, List.length_cons, List.length_nil] at *; omega)
    | (have := _back.length_le; simp only [List.length_drop, List.length_cons, List.length_nil] at *; omega)
    | (subst _finalSkip; simp)
    | (subst _finalBack; simp)
    | (have := first_segment_length _empty
       have : input.length ≠ 0 := fun zero => _empty (List.eq_nil_of_length_eq_zero zero)
       simp only [List.length_drop]; omega)

/-- RFC 3986 section 5.2.3: the reference path appended to `/` when the base
    has an authority and an empty path, and otherwise to all but the last
    segment of the base path, that is, to its characters up to and including
    its right-most `/`, or to nothing when it has no `/`. -/
def merge (base : Parts) (path : List Nat) : List Nat :=
  if base.authority.isSome ∧ base.path = [] then 47 :: path
  else (base.path.reverse.dropWhile (· != 47)).reverse ++ path

/-- RFC 3986 section 5.2.2, strict: the target components of a reference
    against a base. -/
def transform (base r : Parts) : Parts :=
  if r.scheme.isSome then
    { scheme := r.scheme, authority := r.authority, path := removeDots r.path [],
      query := r.query, fragment := r.fragment }
  else if r.authority.isSome then
    { scheme := base.scheme, authority := r.authority, path := removeDots r.path [],
      query := r.query, fragment := r.fragment }
  else if r.path = [] then
    { scheme := base.scheme, authority := base.authority, path := base.path,
      query := if r.query.isSome then r.query else base.query, fragment := r.fragment }
  else if r.path.head? = some 47 then
    { scheme := base.scheme, authority := base.authority, path := removeDots r.path [],
      query := r.query, fragment := r.fragment }
  else
    { scheme := base.scheme, authority := base.authority, path := removeDots (merge base r.path) [],
      query := r.query, fragment := r.fragment }

/-- Resolution of a reference against a base: the recomposed target of
    section 5.2.2. It is defined when the reference has a scheme, which then
    needs no base (section 5.1), or when the base has one (section 5.2.1). -/
def resolve (base reference : List Nat) : Option (List Nat) :=
  if (split reference).scheme.isSome ∨ (split base).scheme.isSome then
    some (compose (transform (split base) (split reference)))
  else none

/-! ### Appendix B loses nothing -/

private theorem take_drop_while (p : Nat → Bool) (w : List Nat) :
    w.takeWhile p ++ w.dropWhile p = w := List.takeWhile_append_dropWhile

/-- The character at which `dropWhile` stops fails its predicate. -/
theorem drop_while_stops {p : Nat → Bool} {w rest : List Nat} {c : Nat}
    (stopped : w.dropWhile p = c :: rest) : p c = false := by
  have nonempty : w.dropWhile p ≠ [] := by simp [stopped]
  have := List.head_dropWhile_not p nonempty
  simpa [stopped] using this

/-- The word left after the scheme is the word after `scheme:`. -/
private theorem scheme_part_spec (w : List Nat) :
    (match (schemePart w).1 with | some s => s ++ [58] | none => []) ++ (schemePart w).2 = w := by
  unfold schemePart
  by_cases found : w.takeWhile SchemeChar ≠ [] ∧ (w.dropWhile SchemeChar).head? = some 58
  · obtain ⟨tail, rest⟩ := List.head?_eq_some_iff.mp found.2
    have whole := take_drop_while SchemeChar w
    rw [rest] at whole
    rw [if_pos found]
    simp only [rest, List.tail_cons, List.append_assoc, List.singleton_append]
    exact whole
  · simp [found]

/-- The word left after the authority is the word after `//authority`. -/
private theorem authority_part_spec (w : List Nat) :
    (match (authorityPart w).1 with | some a => 47 :: 47 :: a | none => []) ++ (authorityPart w).2 = w := by
  unfold authorityPart
  by_cases slashes : [47, 47] <+: w
  · obtain ⟨rest, whole⟩ := slashes
    subst whole
    simp [take_drop_while]
  · simp [slashes]

/-- The word left after the query is the word after `?query`. -/
private theorem query_part_spec (w : List Nat) :
    (match (queryPart w).1 with | some q => 63 :: q | none => []) ++ (queryPart w).2 = w := by
  unfold queryPart
  by_cases question : w.head? = some 63
  · obtain ⟨rest, whole⟩ := List.head?_eq_some_iff.mp question
    subst whole
    simp [take_drop_while]
  · simp [question]

/-- A path ends at a `?` or a `#`, or at the end of the word. -/
private theorem after_path (v : List Nat) :
    v.dropWhile PathChar = [] ∨ (v.dropWhile PathChar).head? = some 63 ∨
      (v.dropWhile PathChar).head? = some 35 := by
  cases tail : v.dropWhile PathChar with
  | nil => exact Or.inl rfl
  | cons c more =>
    have stop := drop_while_stops tail
    simp only [PathChar, Bool.not_eq_false', Bool.or_eq_true, beq_iff_eq] at stop
    rcases stop with q | f
    · simp [q]
    · simp [f]

/-- What follows a query is empty or begins with `#`. -/
private theorem after_query (w : List Nat) (pathEnd : w = [] ∨ w.head? = some 63 ∨ w.head? = some 35) :
    (queryPart w).2 = [] ∨ (queryPart w).2.head? = some 35 := by
  unfold queryPart
  by_cases question : w.head? = some 63
  · simp only [question, if_true]
    cases tail : w.tail.dropWhile QueryChar with
    | nil => exact Or.inl rfl
    | cons c more =>
      have stop := drop_while_stops tail
      simp only [QueryChar, Bool.not_eq_false', beq_iff_eq] at stop
      simp [stop]
  · simp only [question, if_false]
    rcases pathEnd with empty | query | fragment
    · exact Or.inl empty
    · exact absurd query question
    · exact Or.inr fragment

private theorem fragment_part_spec (w : List Nat) (shape : w = [] ∨ w.head? = some 35) :
    (match fragmentPart w with | some f => 35 :: f | none => []) = w := by
  unfold fragmentPart
  rcases shape with empty | fragment
  · subst empty; rfl
  · obtain ⟨rest, whole⟩ := List.head?_eq_some_iff.mp fragment
    subst whole
    simp

/-- Appendix B splits every word into components that recompose to it. -/
theorem compose_split (w : List Nat) : compose (split w) = w := by
  unfold compose split
  simp only []
  have fragments := fragment_part_spec _ (after_query _ (after_path (authorityPart (schemePart w).2).2))
  rw [fragments]
  have queries := query_part_spec ((authorityPart (schemePart w).2).2.dropWhile PathChar)
  have paths := take_drop_while PathChar (authorityPart (schemePart w).2).2
  have authorities := authority_part_spec (schemePart w).2
  have schemes := scheme_part_spec w
  calc _ = (match (schemePart w).1 with | some s => s ++ [58] | none => []) ++
        ((match (authorityPart (schemePart w).2).1 with | some a => 47 :: 47 :: a | none => []) ++
        ((authorityPart (schemePart w).2).2.takeWhile PathChar ++
        ((match (queryPart ((authorityPart (schemePart w).2).2.dropWhile PathChar)).1 with
          | some q => 63 :: q | none => []) ++
          (queryPart ((authorityPart (schemePart w).2).2.dropWhile PathChar)).2))) := by
        simp only [List.append_assoc]
    _ = w := by rw [queries, paths, authorities, schemes]

/-! ### Characters spelled as words

The algorithm inspects only the delimiters `#`, `.`, `/`, `:` and `?`. A
spelling that keeps every delimiter and spells every other character as a
nonempty word without delimiters therefore commutes with it. -/

/-- The characters the algorithm inspects: `#`, `.`, `/`, `:` and `?`. -/
def Delimiter (c : Nat) : Prop := c = 35 ∨ c = 46 ∨ c = 47 ∨ c = 58 ∨ c = 63

/-- A spelling of characters as words that keeps every delimiter and spells
    every other character as a nonempty word without delimiters. -/
structure Opaque (h : Nat → List Nat) : Prop where
  keeps : ∀ c, Delimiter c → h c = [c]
  spells : ∀ c, ¬ Delimiter c → h c ≠ [] ∧ ∀ d ∈ h c, ¬ Delimiter d

/-- Components spelled character by character. -/
def Parts.spell (h : Nat → List Nat) (p : Parts) : Parts :=
  { scheme := p.scheme.map (·.flatMap h), authority := p.authority.map (·.flatMap h),
    path := p.path.flatMap h, query := p.query.map (·.flatMap h),
    fragment := p.fragment.map (·.flatMap h) }

section Spelling
variable {h : Nat → List Nat} (op : Opaque h)
include op

private theorem spell_delimiter {c : Nat} (d : Delimiter c) (w : List Nat) :
    (c :: w).flatMap h = c :: w.flatMap h := by
  simp [op.keeps c d]

private theorem spell_eq_cons {c : Nat} (d : Delimiter c) {w x : List Nat} :
    w.flatMap h = c :: x ↔ ∃ rest, w = c :: rest ∧ x = rest.flatMap h := by
  constructor
  · intro spelled
    cases w with
    | nil => simp at spelled
    | cons a rest =>
      by_cases da : Delimiter a
      · rw [spell_delimiter op da] at spelled
        obtain ⟨same, tail⟩ := List.cons.inj spelled
        subst same
        exact ⟨rest, rfl, tail.symm⟩
      · obtain ⟨nonempty, plain⟩ := op.spells a da
        obtain ⟨e, es, word⟩ := List.exists_cons_of_ne_nil nonempty
        rw [List.flatMap_cons, word, List.cons_append] at spelled
        obtain ⟨same, _⟩ := List.cons.inj spelled
        exact absurd (same ▸ d) (plain e (by simp [word]))
  · rintro ⟨rest, rfl, rfl⟩
    exact spell_delimiter op d rest

private theorem spell_nil {w : List Nat} : w.flatMap h = [] ↔ w = [] := by
  constructor
  · intro spelled
    cases w with
    | nil => rfl
    | cons a rest =>
      by_cases da : Delimiter a
      · simp [spell_delimiter op da] at spelled
      · have := (op.spells a da).1
        simp_all
  · rintro rfl; rfl

private theorem spell_head {c : Nat} (d : Delimiter c) {w : List Nat} :
    (w.flatMap h).head? = some c ↔ w.head? = some c := by
  rw [List.head?_eq_some_iff, List.head?_eq_some_iff]
  constructor
  · rintro ⟨x, spelled⟩
    obtain ⟨rest, rfl, _⟩ := (spell_eq_cons op d).mp spelled
    exact ⟨rest, rfl⟩
  · rintro ⟨rest, rfl⟩
    exact ⟨rest.flatMap h, spell_delimiter op d rest⟩

private theorem spell_tail {c : Nat} (d : Delimiter c) {w : List Nat} (head : w.head? = some c) :
    (w.flatMap h).tail = w.tail.flatMap h := by
  obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp head
  simp [spell_delimiter op d]

private theorem spell_prefix {pattern : List Nat} (delimiters : ∀ d ∈ pattern, Delimiter d) {w : List Nat} :
    (pattern <+: w.flatMap h ↔ pattern <+: w) ∧
      (pattern <+: w → (w.flatMap h).drop pattern.length = (w.drop pattern.length).flatMap h) := by
  induction pattern generalizing w with
  | nil => simp
  | cons d rest ih =>
    have dd : Delimiter d := delimiters d (by simp)
    have more := fun {v : List Nat} => @ih (fun e member => delimiters e (by simp [member])) v
    constructor
    · constructor
      · intro prefixed
        obtain ⟨x, spelled⟩ := prefixed
        rw [List.cons_append] at spelled
        obtain ⟨tail, rfl, tailSpelled⟩ := (spell_eq_cons op dd).mp spelled.symm
        have : rest <+: tail.flatMap h := ⟨x, tailSpelled⟩
        exact (List.cons_prefix_cons).mpr ⟨rfl, more.1.mp this⟩
      · intro prefixed
        obtain ⟨x, rfl⟩ := prefixed
        rw [List.cons_append, spell_delimiter op dd]
        exact (List.cons_prefix_cons).mpr ⟨rfl, more.1.mpr ⟨x, rfl⟩⟩
    · intro prefixed
      obtain ⟨x, rfl⟩ := prefixed
      rw [List.cons_append, spell_delimiter op dd]
      simp only [List.length_cons, List.drop_succ_cons]
      exact more.2 ⟨x, rfl⟩

private theorem spell_eq {pattern : List Nat} (delimiters : ∀ d ∈ pattern, Delimiter d) {w : List Nat} :
    w.flatMap h = pattern ↔ w = pattern := by
  induction pattern generalizing w with
  | nil => exact spell_nil op
  | cons d rest ih =>
    have dd : Delimiter d := delimiters d (by simp)
    constructor
    · intro spelled
      obtain ⟨tail, rfl, tailSpelled⟩ := (spell_eq_cons op dd).mp spelled
      rw [(ih (fun e member => delimiters e (by simp [member]))).mp tailSpelled.symm]
    · rintro rfl
      exact (spell_eq_cons op dd).mpr ⟨rest, rfl, by
        rw [(ih (fun e member => delimiters e (by simp [member]))).mpr rfl]⟩

private theorem spell_take_while {p : Nat → Bool} (passes : ∀ c, ¬ Delimiter c → p c = true) (w : List Nat) :
    (w.flatMap h).takeWhile p = (w.takeWhile p).flatMap h ∧
      (w.flatMap h).dropWhile p = (w.dropWhile p).flatMap h := by
  induction w with
  | nil => simp
  | cons a rest ih =>
    by_cases pa : p a = true
    · by_cases da : Delimiter a
      · rw [spell_delimiter op da]
        simp [List.takeWhile_cons_of_pos pa, List.dropWhile_cons_of_pos pa, spell_delimiter op da, ih]
      · have all : ∀ e ∈ h a, p e = true := fun e member => passes e ((op.spells a da).2 e member)
        rw [List.flatMap_cons, List.takeWhile_append_of_pos all, List.dropWhile_append_of_pos all]
        simp [List.takeWhile_cons_of_pos pa, List.dropWhile_cons_of_pos pa, ih]
    · have da : Delimiter a := by
        by_contra plain
        exact pa (passes a plain)
      rw [spell_delimiter op da]
      simp [List.takeWhile_cons_of_neg pa, List.dropWhile_cons_of_neg pa, spell_delimiter op da]

end Spelling

/-- Reversing every spelled word keeps a spelling op. -/
private theorem opaque_reverse {h : Nat → List Nat} (op : Opaque h) : Opaque (fun c => (h c).reverse) where
  keeps c d := by simp [op.keeps c d]
  spells c d := ⟨by simpa using (op.spells c d).1, fun e member => (op.spells c d).2 e (by simpa using member)⟩

private theorem delimiter_35 : Delimiter 35 := by simp [Delimiter]
private theorem delimiter_46 : Delimiter 46 := by simp [Delimiter]
private theorem delimiter_47 : Delimiter 47 := by simp [Delimiter]
private theorem delimiter_58 : Delimiter 58 := by simp [Delimiter]
private theorem delimiter_63 : Delimiter 63 := by simp [Delimiter]

private theorem scheme_passes : ∀ c, ¬ Delimiter c → SchemeChar c = true := by
  intro c d; unfold Delimiter at d; simp [SchemeChar]; omega
private theorem authority_passes : ∀ c, ¬ Delimiter c → AuthorityChar c = true := by
  intro c d; unfold Delimiter at d; simp [AuthorityChar]; omega
private theorem path_passes : ∀ c, ¬ Delimiter c → PathChar c = true := by
  intro c d; unfold Delimiter at d; simp [PathChar]; omega
private theorem query_passes : ∀ c, ¬ Delimiter c → QueryChar c = true := by
  intro c d; unfold Delimiter at d; simp [QueryChar]; omega
private theorem slash_passes : ∀ c, ¬ Delimiter c → (c != 47) = true := by
  intro c d; unfold Delimiter at d; simp; omega

/-- A word without a leading `/` begins with its first segment. -/
private theorem first_segment_eq {w : List Nat} (notSlash : w.head? ≠ some 47) :
    firstSegment w = w.takeWhile (· != 47) := by
  cases w with
  | nil => rfl
  | cons c rest =>
    have different : c ≠ 47 := by simpa using notSlash
    rw [first_segment_cons different, List.takeWhile_cons]
    simp [different]

/-- The first segment is a prefix of the input buffer. -/
private theorem first_segment_prefix (w : List Nat) : firstSegment w <+: w := by
  by_cases slash : w.head? = some 47
  · obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp slash
    simp only [firstSegment]
    exact (List.cons_prefix_cons).mpr ⟨rfl, List.takeWhile_prefix _⟩
  · rw [first_segment_eq slash]
    exact List.takeWhile_prefix _

section Components
variable {h : Nat → List Nat} (op : Opaque h)
include op

private theorem scheme_part_spell (w : List Nat) :
    schemePart (w.flatMap h) = ((schemePart w).1.map (·.flatMap h), (schemePart w).2.flatMap h) := by
  obtain ⟨takes, drops⟩ := spell_take_while op scheme_passes w
  unfold schemePart
  rw [takes, drops]
  have same : ((w.takeWhile SchemeChar).flatMap h ≠ [] ∧ ((w.dropWhile SchemeChar).flatMap h).head? = some 58) ↔
      (w.takeWhile SchemeChar ≠ [] ∧ (w.dropWhile SchemeChar).head? = some 58) := by
    simp only [ne_eq, spell_nil op, spell_head op delimiter_58]
  by_cases found : w.takeWhile SchemeChar ≠ [] ∧ (w.dropWhile SchemeChar).head? = some 58
  · rw [if_pos (same.mpr found), if_pos found]
    simp [spell_tail op delimiter_58 found.2]
  · rw [if_neg (fun spelled => found (same.mp spelled)), if_neg found]
    simp

private theorem authority_part_spell (w : List Nat) :
    authorityPart (w.flatMap h) = ((authorityPart w).1.map (·.flatMap h), (authorityPart w).2.flatMap h) := by
  have slashes : ∀ d ∈ [47, 47], Delimiter d := by simp [Delimiter]
  obtain ⟨prefixed, dropped⟩ := spell_prefix op slashes (w := w)
  unfold authorityPart
  by_cases found : [47, 47] <+: w
  · rw [if_pos (prefixed.mpr found), if_pos found]
    have two : (w.flatMap h).drop 2 = (w.drop 2).flatMap h := dropped found
    obtain ⟨takes, drops⟩ := spell_take_while op authority_passes (w.drop 2)
    simp [two, takes, drops]
  · rw [if_neg (fun spelled => found (prefixed.mp spelled)), if_neg found]
    simp

private theorem query_part_spell (w : List Nat) :
    queryPart (w.flatMap h) = ((queryPart w).1.map (·.flatMap h), (queryPart w).2.flatMap h) := by
  unfold queryPart
  by_cases found : w.head? = some 63
  · rw [if_pos ((spell_head op delimiter_63).mpr found), if_pos found, spell_tail op delimiter_63 found]
    obtain ⟨takes, drops⟩ := spell_take_while op query_passes w.tail
    simp [takes, drops]
  · rw [if_neg (fun spelled => found ((spell_head op delimiter_63).mp spelled)), if_neg found]
    simp

private theorem fragment_part_spell (w : List Nat) :
    fragmentPart (w.flatMap h) = (fragmentPart w).map (·.flatMap h) := by
  unfold fragmentPart
  by_cases found : w.head? = some 35
  · rw [if_pos ((spell_head op delimiter_35).mpr found), if_pos found, spell_tail op delimiter_35 found]
    simp
  · rw [if_neg (fun spelled => found ((spell_head op delimiter_35).mp spelled)), if_neg found]
    simp

/-- Appendix B splits a spelled word into the spelled components. -/
private theorem split_spell (w : List Nat) : split (w.flatMap h) = (split w).spell h := by
  obtain ⟨takes, drops⟩ := spell_take_while op path_passes (authorityPart (schemePart w).2).2
  simp only [split, Parts.spell, scheme_part_spell op w, authority_part_spell op, takes, drops,
    query_part_spell op, fragment_part_spell op]

/-- Recomposing spelled components spells the recomposed word. -/
private theorem compose_spell (p : Parts) : compose (p.spell h) = (compose p).flatMap h := by
  cases p with
  | mk scheme authority path query fragment =>
    cases scheme <;> cases authority <;> cases query <;> cases fragment <;>
      simp [compose, Parts.spell, List.flatMap_append, op.keeps 58 delimiter_58, op.keeps 47 delimiter_47,
        op.keeps 63 delimiter_63, op.keeps 35 delimiter_35]

private theorem first_segment_spell (w : List Nat) : firstSegment (w.flatMap h) = (firstSegment w).flatMap h := by
  by_cases slash : w.head? = some 47
  · obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp slash
    rw [spell_delimiter op delimiter_47]
    simp only [firstSegment]
    rw [(spell_take_while op slash_passes rest).1, spell_delimiter op delimiter_47]
  · have spelled : (w.flatMap h).head? ≠ some 47 := fun x => slash ((spell_head op delimiter_47).mp x)
    rw [first_segment_eq spelled, first_segment_eq slash]
    exact (spell_take_while op slash_passes w).1

private theorem first_segment_drop_spell (w : List Nat) :
    (w.flatMap h).drop (firstSegment (w.flatMap h)).length = (w.drop (firstSegment w).length).flatMap h := by
  obtain ⟨rest, whole⟩ := first_segment_prefix w
  have dropped : w.drop (firstSegment w).length = rest := by
    have := congrArg (List.drop (firstSegment w).length) whole
    simpa using this.symm
  rw [first_segment_spell op, dropped]
  have spelled : w.flatMap h = (firstSegment w).flatMap h ++ rest.flatMap h := by
    rw [← List.flatMap_append, whole]
  rw [spelled, List.drop_left]

private theorem pop_segment_spell (out : List Nat) : popSegment (out.flatMap h) = (popSegment out).flatMap h := by
  have reversed := opaque_reverse op
  unfold popSegment
  rw [List.reverse_flatMap]
  have dropped := (spell_take_while reversed slash_passes out.reverse).2
  simp only [Function.comp_def] at dropped ⊢
  rw [dropped]
  cases rest : out.reverse.dropWhile (· != 47) with
  | nil => simp
  | cons c tail =>
    have stop := drop_while_stops rest
    have slash : c = 47 := by simpa using stop
    subst slash
    rw [spell_delimiter reversed delimiter_47]
    simp [List.reverse_flatMap, Function.comp_def]

/-- Dot-segment removal commutes with the spelling. -/
private theorem remove_dots_spell (input output : List Nat) :
    removeDots (input.flatMap h) (output.flatMap h) = (removeDots input output).flatMap h := by
  induction size : input.length using Nat.strong_induction_on generalizing input output with
  | _ size ih =>
    have three : ∀ d ∈ [46, 46, 47], Delimiter d := by simp [Delimiter]
    have two : ∀ d ∈ [46, 47], Delimiter d := by simp [Delimiter]
    have skip : ∀ d ∈ [47, 46, 47], Delimiter d := by simp [Delimiter]
    have back : ∀ d ∈ [47, 46, 46, 47], Delimiter d := by simp [Delimiter]
    have finalSkip : ∀ d ∈ [47, 46], Delimiter d := by simp [Delimiter]
    have finalBack : ∀ d ∈ [47, 46, 46], Delimiter d := by simp [Delimiter]
    have dot : ∀ d ∈ [46], Delimiter d := by simp [Delimiter]
    have dots : ∀ d ∈ [46, 46], Delimiter d := by simp [Delimiter]
    have slash : [47].flatMap h = [47] := by simp [op.keeps 47 delimiter_47]
    by_cases empty : input = []
    · subst empty
      conv_lhs => rw [removeDots]
      conv_rhs => rw [removeDots]
      simp
    have spelledEmpty : input.flatMap h ≠ [] := fun x => empty ((spell_nil op).mp x)
    conv_lhs => rw [removeDots]
    conv_rhs => rw [removeDots]
    rw [dif_neg spelledEmpty, dif_neg empty]
    by_cases parent : [46, 46, 47] <+: input
    · rw [dif_pos ((spell_prefix op three).1.mpr parent), dif_pos parent]
      have dropped : (input.flatMap h).drop 3 = (input.drop 3).flatMap h := (spell_prefix op three).2 parent
      rw [dropped]
      exact ih _ (by have := parent.length_le; simp at this; simp; omega) _ _ rfl
    rw [dif_neg (fun x => parent ((spell_prefix op three).1.mp x)), dif_neg parent]
    by_cases current : [46, 47] <+: input
    · rw [dif_pos ((spell_prefix op two).1.mpr current), dif_pos current]
      have dropped : (input.flatMap h).drop 2 = (input.drop 2).flatMap h := (spell_prefix op two).2 current
      rw [dropped]
      exact ih _ (by have := current.length_le; simp at this; simp; omega) _ _ rfl
    rw [dif_neg (fun x => current ((spell_prefix op two).1.mp x)), dif_neg current]
    by_cases skipped : [47, 46, 47] <+: input
    · rw [dif_pos ((spell_prefix op skip).1.mpr skipped), dif_pos skipped]
      have dropped : (input.flatMap h).drop 3 = (input.drop 3).flatMap h := (spell_prefix op skip).2 skipped
      rw [dropped, ← spell_delimiter op delimiter_47]
      exact ih _ (by have := skipped.length_le; simp at this; simp; omega) _ _ rfl
    rw [dif_neg (fun x => skipped ((spell_prefix op skip).1.mp x)), dif_neg skipped]
    by_cases finalSkipped : input = [47, 46]
    · rw [dif_pos ((spell_eq op finalSkip).mpr finalSkipped), dif_pos finalSkipped]
      have step := ih [47].length (by subst finalSkipped; simp only [List.length_cons, List.length_nil] at size ⊢; omega)
        [47] output rfl
      rwa [slash] at step
    rw [dif_neg (fun x => finalSkipped ((spell_eq op finalSkip).mp x)), dif_neg finalSkipped]
    by_cases backed : [47, 46, 46, 47] <+: input
    · rw [dif_pos ((spell_prefix op back).1.mpr backed), dif_pos backed]
      have dropped : (input.flatMap h).drop 4 = (input.drop 4).flatMap h := (spell_prefix op back).2 backed
      rw [dropped, ← spell_delimiter op delimiter_47, pop_segment_spell op]
      exact ih _ (by have := backed.length_le; simp at this; simp; omega) _ _ rfl
    rw [dif_neg (fun x => backed ((spell_prefix op back).1.mp x)), dif_neg backed]
    by_cases finalBacked : input = [47, 46, 46]
    · rw [dif_pos ((spell_eq op finalBack).mpr finalBacked), dif_pos finalBacked, pop_segment_spell op]
      have step := ih [47].length (by subst finalBacked; simp only [List.length_cons, List.length_nil] at size ⊢; omega)
        [47] (popSegment output) rfl
      rwa [slash] at step
    rw [dif_neg (fun x => finalBacked ((spell_eq op finalBack).mp x)), dif_neg finalBacked]
    by_cases dropping : input = [46] ∨ input = [46, 46]
    · rw [if_pos (by rwa [spell_eq op dot, spell_eq op dots]), if_pos dropping]
    rw [if_neg (by rwa [spell_eq op dot, spell_eq op dots]), if_neg dropping]
    rw [first_segment_drop_spell op, first_segment_spell op, ← List.flatMap_append]
    exact ih _ (by
      have := first_segment_length empty
      have : input.length ≠ 0 := fun zero => empty (List.eq_nil_of_length_eq_zero zero)
      simp only [List.length_drop]; omega) _ _ rfl

private theorem merge_spell (b : Parts) (path : List Nat) :
    merge (b.spell h) (path.flatMap h) = (merge b path).flatMap h := by
  unfold merge Parts.spell
  by_cases bare : b.authority.isSome ∧ b.path = []
  · have spelled : (b.authority.map (·.flatMap h)).isSome ∧ b.path.flatMap h = [] := by
      refine ⟨by simpa using bare.1, ?_⟩
      rw [bare.2]; rfl
    rw [if_pos spelled, if_pos bare]
    simp [op.keeps 47 delimiter_47]
  · have spelled : ¬ ((b.authority.map (·.flatMap h)).isSome ∧ b.path.flatMap h = []) := by
      rwa [Option.isSome_map, spell_nil op]
    rw [if_neg spelled, if_neg bare, List.flatMap_append, List.reverse_flatMap]
    have dropped := (spell_take_while (opaque_reverse op) slash_passes b.path.reverse).2
    simp only [Function.comp_def]
    rw [dropped, List.reverse_flatMap]
    simp [Function.comp_def]

private theorem transform_spell (b r : Parts) : transform (b.spell h) (r.spell h) = (transform b r).spell h := by
  have empty := remove_dots_spell op
  unfold transform
  by_cases scheme : r.scheme.isSome
  · have spelled : (r.spell h).scheme.isSome := by simpa [Parts.spell] using scheme
    rw [if_pos spelled, if_pos scheme]
    simpa [Parts.spell] using empty r.path []
  rw [if_neg (by simpa [Parts.spell] using scheme), if_neg scheme]
  by_cases authority : r.authority.isSome
  · rw [if_pos (by simpa [Parts.spell] using authority), if_pos authority]
    simpa [Parts.spell] using empty r.path []
  rw [if_neg (by simpa [Parts.spell] using authority), if_neg authority]
  by_cases path : r.path = []
  · rw [if_pos (by simp [Parts.spell, path]), if_pos path]
    by_cases query : r.query.isSome
    · simp [Parts.spell, query]
    · simp [Parts.spell, query]
  rw [if_neg (by simpa [Parts.spell, spell_nil op] using path), if_neg path]
  by_cases slash : r.path.head? = some 47
  · rw [if_pos (show (r.spell h).path.head? = some 47 from (spell_head op delimiter_47).mpr slash), if_pos slash]
    simpa [Parts.spell] using empty r.path []
  rw [if_neg (show ¬ (r.spell h).path.head? = some 47 from fun x => slash ((spell_head op delimiter_47).mp x)),
    if_neg slash]
  have merged := merge_spell op b r.path
  simp only [Parts.spell] at merged ⊢
  rw [merged]
  simpa using empty (merge b r.path) []

/-- Resolution commutes with every opaque spelling of characters. -/
theorem resolve_opaque (base reference : List Nat) :
    resolve (base.flatMap h) (reference.flatMap h) = (resolve base reference).map (·.flatMap h) := by
  unfold resolve
  rw [split_spell op base, split_spell op reference]
  have same : (((split reference).spell h).scheme.isSome ∨ ((split base).spell h).scheme.isSome) ↔
      ((split reference).scheme.isSome ∨ (split base).scheme.isSome) := by
    simp [Parts.spell]
  by_cases defined : (split reference).scheme.isSome ∨ (split base).scheme.isSome
  · rw [if_pos (same.mpr defined), if_pos defined]
    simp only [Option.map_some]
    rw [transform_spell op, compose_spell op]
  · rw [if_neg (fun x => defined (same.mp x)), if_neg defined]
    rfl

end Components

/-! ### UTF-8

RFC 3987 section 6.5 treats the characters an IRI adds to a URI like unreserved
characters, so resolution applies to the UTF-8 bytes of IRIs: UTF-8 keeps the
ASCII delimiters and spells every other character without them. -/

/-- The UTF-8 encoding of a code point (RFC 3629 section 3), as byte values. -/
def utf8 (c : Nat) : List Nat :=
  if c < 128 then [c]
  else if c < 2048 then [192 + c / 64, 128 + c % 64]
  else if c < 65536 then [224 + c / 4096, 128 + c / 64 % 64, 128 + c % 64]
  else [240 + c / 262144, 128 + c / 4096 % 64, 128 + c / 64 % 64, 128 + c % 64]

/-- UTF-8 keeps the delimiters and spells other characters without them. -/
theorem utf8_opaque : Opaque utf8 where
  keeps c d := by
    unfold Delimiter at d
    unfold utf8
    rw [if_pos (by omega)]
  spells c d := by
    unfold Delimiter at d
    unfold utf8
    split_ifs <;> simp [Delimiter] <;> omega

private theorem drop_cons_of {l : List U8} {i : Nat} {v : U8} (h : l[i]? = some v) :
    l.drop i = v :: l.drop (i + 1) := by
  obtain ⟨inside, value⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons inside, value]

private theorem utf8_two {a b : Nat} (grammar : Rowl.Unicode.Pair a b) :
    utf8 (Rowl.Unicode.value2 a b) = [a, b] := by
  simp only [Rowl.Unicode.Pair, Rowl.Unicode.Tail] at grammar
  unfold utf8 Rowl.Unicode.value2
  rw [if_neg (by omega), if_pos (by omega)]
  simp only [List.cons.injEq, and_true]
  omega

private theorem utf8_three {a b c : Nat} (grammar : Rowl.Unicode.Triple a b c) :
    utf8 (Rowl.Unicode.value3 a b c) = [a, b, c] := by
  simp only [Rowl.Unicode.Triple, Rowl.Unicode.Tail] at grammar
  unfold utf8 Rowl.Unicode.value3
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  simp only [List.cons.injEq, and_true]
  omega

private theorem utf8_four {a b c d : Nat} (grammar : Rowl.Unicode.Quad a b c d) :
    utf8 (Rowl.Unicode.value4 a b c d) = [a, b, c, d] := by
  simp only [Rowl.Unicode.Quad, Rowl.Unicode.Tail] at grammar
  unfold utf8 Rowl.Unicode.value4
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp only [List.cons.injEq, and_true]
  omega

/-- A strictly decoded unit is the UTF-8 encoding of a scalar. -/
theorem prefix_utf8 {bs : List U8} {i cp width : Nat} (unit : Rowl.Unicode.Prefix bs i = some (cp, width)) :
    ((bs.drop i).take width).map (·.val) = utf8 cp ∧ Rowl.Encoding.Scalar cp := by
  unfold Rowl.Unicode.Prefix at unit
  cases first : bs[i]? with
  | none => simp [first] at unit
  | some a =>
    simp only [first, Option.bind_some, Option.bind_eq_bind] at unit
    rw [drop_cons_of first]
    by_cases ascii : a.val < 128
    · simp only [ascii, if_true, Option.some.injEq, Prod.mk.injEq] at unit
      obtain ⟨rfl, rfl⟩ := unit
      refine ⟨by simp [utf8, ascii], ?_⟩
      unfold Rowl.Encoding.Scalar; omega
    · simp only [ascii, if_false] at unit
      by_cases pair : a.val < 224
      · simp only [pair, if_true] at unit
        cases second : bs[i + 1]? with
        | none => simp [second] at unit
        | some b =>
          simp only [second, Option.bind_some] at unit
          by_cases grammar : Rowl.Unicode.Pair a.val b.val
          · simp only [grammar, if_true, Option.some.injEq, Prod.mk.injEq] at unit
            obtain ⟨rfl, rfl⟩ := unit
            rw [drop_cons_of second]
            have bounds := (Rowl.Unicode.byte_grammar_scalar_ranges a.val b.val 0 0).1 grammar
            refine ⟨by simp [utf8_two grammar], ?_⟩
            unfold Rowl.Encoding.Scalar; omega
          · simp [grammar] at unit
      · simp only [pair, if_false] at unit
        by_cases triple : a.val < 240
        · simp only [triple, if_true] at unit
          cases second : bs[i + 1]? with
          | none => simp [second] at unit
          | some b =>
            simp only [second, Option.bind_some] at unit
            cases third : bs[i + 2]? with
            | none => simp [third] at unit
            | some c =>
              simp only [third, Option.bind_some] at unit
              by_cases grammar : Rowl.Unicode.Triple a.val b.val c.val
              · simp only [grammar, if_true, Option.some.injEq, Prod.mk.injEq] at unit
                obtain ⟨rfl, rfl⟩ := unit
                rw [drop_cons_of second, drop_cons_of third]
                have bounds := (Rowl.Unicode.byte_grammar_scalar_ranges a.val b.val c.val 0).2.1 grammar
                refine ⟨by simp [utf8_three grammar], ?_⟩
                unfold Rowl.Encoding.Scalar; omega
              · simp [grammar] at unit
        · simp only [triple, if_false] at unit
          cases second : bs[i + 1]? with
          | none => simp [second] at unit
          | some b =>
            simp only [second, Option.bind_some] at unit
            cases third : bs[i + 2]? with
            | none => simp [third] at unit
            | some c =>
              simp only [third, Option.bind_some] at unit
              cases fourth : bs[i + 3]? with
              | none => simp [fourth] at unit
              | some d =>
                simp only [fourth, Option.bind_some] at unit
                by_cases grammar : Rowl.Unicode.Quad a.val b.val c.val d.val
                · simp only [grammar, if_true, Option.some.injEq, Prod.mk.injEq] at unit
                  obtain ⟨rfl, rfl⟩ := unit
                  rw [drop_cons_of second, drop_cons_of third, drop_cons_of fourth]
                  have bounds := (Rowl.Unicode.byte_grammar_scalar_ranges a.val b.val c.val d.val).2.2 grammar
                  refine ⟨by simp [utf8_four grammar], ?_⟩
                  unfold Rowl.Encoding.Scalar; omega
                · simp [grammar] at unit

/-- Strictly decoded bytes are the UTF-8 encoding of their scalar values. -/
theorem utf8_decoded {bs : List U8} {i : Nat} {w : List Nat} (decoded : Rowl.Regular.Utf8From bs i w) :
    (bs.drop i).map (·.val) = w.flatMap utf8 ∧ ∀ c ∈ w, Rowl.Encoding.Scalar c := by
  induction decoded with
  | endOfInput => simp
  | @character offset cp width tail unit positive fits rest ih =>
    obtain ⟨encoded, scalar⟩ := prefix_utf8 unit
    refine ⟨?_, ?_⟩
    · have split : bs.drop offset = (bs.drop offset).take width ++ bs.drop (offset + width) := by
        rw [← List.drop_drop, List.take_append_drop]
      rw [split, List.map_append, encoded, ih.1, List.flatMap_cons]
    · intro c member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact scalar
      · exact ih.2 c inTail

private theorem drop_value {bs : List U8} {i v : Nat} {rest : List Nat}
    (values : (bs.drop i).map (·.val) = v :: rest) :
    ∃ b : U8, bs[i]? = some b ∧ b.val = v ∧ (bs.drop (i + 1)).map (·.val) = rest := by
  cases split : bs.drop i with
  | nil => simp [split] at values
  | cons b more =>
    rw [split, List.map_cons] at values
    obtain ⟨same, tail⟩ := List.cons.inj values
    refine ⟨b, ?_, same, ?_⟩
    · have : (bs.drop i)[0]? = some b := by simp [split]
      simpa using this
    · rw [← List.drop_drop, split]; simpa using tail

private theorem pair_of_scalar {c : Nat} (low : 128 ≤ c) (high : c < 2048) :
    Rowl.Unicode.Pair (192 + c / 64) (128 + c % 64) ∧ Rowl.Unicode.value2 (192 + c / 64) (128 + c % 64) = c := by
  simp only [Rowl.Unicode.Pair, Rowl.Unicode.Tail, Rowl.Unicode.value2]; omega

private theorem triple_of_scalar {c : Nat} (low : 2048 ≤ c) (high : c < 65536)
    (notSurrogate : ¬ (55296 ≤ c ∧ c ≤ 57343)) :
    Rowl.Unicode.Triple (224 + c / 4096) (128 + c / 64 % 64) (128 + c % 64) ∧
      Rowl.Unicode.value3 (224 + c / 4096) (128 + c / 64 % 64) (128 + c % 64) = c := by
  simp only [Rowl.Unicode.Triple, Rowl.Unicode.Tail, Rowl.Unicode.value3]; omega

private theorem quad_of_scalar {c : Nat} (low : 65536 ≤ c) (high : c ≤ 1114111) :
    Rowl.Unicode.Quad (240 + c / 262144) (128 + c / 4096 % 64) (128 + c / 64 % 64) (128 + c % 64) ∧
      Rowl.Unicode.value4 (240 + c / 262144) (128 + c / 4096 % 64) (128 + c / 64 % 64) (128 + c % 64) = c := by
  simp only [Rowl.Unicode.Quad, Rowl.Unicode.Tail, Rowl.Unicode.value4]; omega

/-- The UTF-8 encoding of a scalar is a strictly decoded unit. -/
theorem utf8_prefix {bs : List U8} {i c : Nat} {rest : List Nat} (scalar : Rowl.Encoding.Scalar c)
    (values : (bs.drop i).map (·.val) = utf8 c ++ rest) :
    Rowl.Unicode.Prefix bs i = some (c, (utf8 c).length) := by
  unfold Rowl.Encoding.Scalar at scalar
  unfold Rowl.Unicode.Prefix
  by_cases ascii : c < 128
  · simp only [utf8, ascii, if_true, List.cons_append, List.nil_append] at values
    obtain ⟨a, at0, value, _⟩ := drop_value values
    simp [at0, value, ascii, utf8]
  · by_cases two : c < 2048
    · simp only [utf8, ascii, two, if_false, if_true, List.cons_append, List.nil_append] at values
      obtain ⟨a, at0, va, values⟩ := drop_value values
      obtain ⟨b, at1, vb, _⟩ := drop_value values
      obtain ⟨grammar, value⟩ := pair_of_scalar (by omega) two
      have notAscii : ¬ a.val < 128 := by omega
      have lead : a.val < 224 := by omega
      simp only [at0, at1, Option.bind_some, Option.bind_eq_bind, notAscii, lead, if_false, if_true]
      rw [va, vb, if_pos grammar, value]
      simp [utf8, ascii, two]
    · by_cases three : c < 65536
      · simp only [utf8, ascii, two, three, if_false, if_true, List.cons_append, List.nil_append] at values
        obtain ⟨a, at0, va, values⟩ := drop_value values
        obtain ⟨b, at1, vb, values⟩ := drop_value values
        obtain ⟨d, at2, vd, _⟩ := drop_value values
        obtain ⟨grammar, value⟩ := triple_of_scalar (by omega) three scalar.2
        have notAscii : ¬ a.val < 128 := by omega
        have notPair : ¬ a.val < 224 := by omega
        have lead : a.val < 240 := by omega
        simp only [at0, at1, at2, Option.bind_some, Option.bind_eq_bind, notAscii, notPair, lead, if_false,
          if_true]
        rw [va, vb, vd, if_pos grammar, value]
        simp [utf8, ascii, two, three]
      · simp only [utf8, ascii, two, three, if_false, List.cons_append, List.nil_append] at values
        obtain ⟨a, at0, va, values⟩ := drop_value values
        obtain ⟨b, at1, vb, values⟩ := drop_value values
        obtain ⟨d, at2, vd, values⟩ := drop_value values
        obtain ⟨e, at3, ve, _⟩ := drop_value values
        obtain ⟨grammar, value⟩ := quad_of_scalar (by omega) scalar.1
        have notAscii : ¬ a.val < 128 := by omega
        have notPair : ¬ a.val < 224 := by omega
        have notTriple : ¬ a.val < 240 := by omega
        simp only [at0, at1, at2, at3, Option.bind_some, Option.bind_eq_bind, notAscii, notPair, notTriple,
          if_false]
        rw [va, vb, vd, ve, if_pos grammar, value]
        simp [utf8, ascii, two, three]

/-- The UTF-8 encoding of scalars decodes strictly to them. -/
theorem utf8_encoded {bs : List U8} {w : List Nat} (scalars : ∀ c ∈ w, Rowl.Encoding.Scalar c)
    (values : bs.map (·.val) = w.flatMap utf8) : Rowl.Regular.Utf8From bs 0 w := by
  suffices general : ∀ i, i ≤ bs.length → (bs.drop i).map (·.val) = w.flatMap utf8 →
      Rowl.Regular.Utf8From bs i w by
    exact general 0 (Nat.zero_le _) (by simpa using values)
  clear values
  induction w with
  | nil =>
    intro i inside empty
    have done : bs.drop i = [] := by simpa using empty
    have atEnd : bs.length ≤ i := List.drop_eq_nil_iff.mp done
    have same : i = bs.length := by omega
    subst same
    exact .endOfInput
  | cons c rest ih =>
    intro i inside spelled
    rw [List.flatMap_cons] at spelled
    have unit := utf8_prefix (scalars c (by simp)) spelled
    have positive : 0 < (utf8 c).length := by unfold utf8; split_ifs <;> simp
    have encoded := (prefix_utf8 unit).1
    have fits : i + (utf8 c).length ≤ bs.length := by
      have := congrArg List.length spelled
      simp only [List.length_map, List.length_drop, List.length_append] at this
      omega
    refine .character unit positive fits (ih (fun d member => scalars d (by simp [member])) (i + (utf8 c).length)
      fits ?_)
    have split : bs.drop i = (bs.drop i).take (utf8 c).length ++ bs.drop (i + (utf8 c).length) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.map_append, encoded] at spelled
    exact List.append_cancel_left spelled

private noncomputable def mark (x c : Nat) : List Nat := if Rowl.Encoding.Scalar c then [c] else [x]

private theorem mark_opaque {x : Nat} (big : 1114111 < x) : Opaque (mark x) where
  keeps c d := by
    unfold Delimiter at d
    unfold mark Rowl.Encoding.Scalar
    rw [if_pos (by omega)]
  spells c d := by
    unfold Delimiter at d
    unfold mark
    split_ifs <;> simp [Delimiter] <;> omega

private theorem mark_map (x : Nat) (w : List Nat) :
    w.flatMap (mark x) = w.map (fun c => if Rowl.Encoding.Scalar c then c else x) := by
  induction w with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.flatMap_cons, List.map_cons, ih]
    unfold mark
    split_ifs <;> rfl

private theorem mark_scalars {x : Nat} {w : List Nat} (scalars : ∀ c ∈ w, Rowl.Encoding.Scalar c) :
    w.flatMap (mark x) = w := by
  rw [mark_map]
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left (fun c member => by simp [scalars c member])

private theorem map_fixed {f : Nat → Nat} : ∀ {w : List Nat}, w.map f = w → ∀ c ∈ w, f c = c
  | [], _, c, member => by simp at member
  | a :: rest, same, c, member => by
    obtain ⟨head, tail⟩ := List.cons.inj same
    rcases List.mem_cons.mp member with rfl | inRest
    · exact head
    · exact map_fixed tail c inRest

/-- Resolving words of Unicode scalars gives a word of Unicode scalars. -/
theorem resolve_scalars {b r t : List Nat} (baseScalars : ∀ c ∈ b, Rowl.Encoding.Scalar c)
    (referenceScalars : ∀ c ∈ r, Rowl.Encoding.Scalar c) (resolved : resolve b r = some t) :
    ∀ c ∈ t, Rowl.Encoding.Scalar c := by
  have fixed : ∀ x, 1114111 < x → ∀ c ∈ t, (if Rowl.Encoding.Scalar c then c else x) = c := by
    intro x big
    have commuted := resolve_opaque (mark_opaque big) b r
    rw [mark_scalars baseScalars, mark_scalars referenceScalars, resolved] at commuted
    simp only [Option.map_some, Option.some.injEq] at commuted
    rw [mark_map] at commuted
    exact map_fixed commuted.symm
  intro c member
  by_contra notScalar
  have one := fixed 1114112 (by norm_num) c member
  have two := fixed 1114113 (by norm_num) c member
  simp only [notScalar, if_false] at one two
  omega

/-- Resolution of UTF-8 bytes is resolution of their characters: for a base and
    a reference that decode strictly, the byte result is defined exactly when
    the character result is, it is the UTF-8 encoding of the character result,
    and its bytes decode strictly to the resolved characters. -/
theorem resolve_bytes {base reference : List U8} {b r : List Nat}
    (baseText : Rowl.Regular.Utf8From base 0 b) (referenceText : Rowl.Regular.Utf8From reference 0 r) :
    resolve (base.map (·.val)) (reference.map (·.val)) = (resolve b r).map (·.flatMap utf8) ∧
      ∀ target : List U8, resolve (base.map (·.val)) (reference.map (·.val)) = some (target.map (·.val)) →
        ∃ t, resolve b r = some t ∧ Rowl.Regular.Utf8From target 0 t := by
  have eb := (utf8_decoded baseText).1
  have er := (utf8_decoded referenceText).1
  simp only [List.drop_zero] at eb er
  have same : resolve (base.map (·.val)) (reference.map (·.val)) = (resolve b r).map (·.flatMap utf8) := by
    rw [eb, er, resolve_opaque utf8_opaque]
  refine ⟨same, fun target spelled => ?_⟩
  rw [same] at spelled
  cases resolved : resolve b r with
  | none => rw [resolved] at spelled; simp at spelled
  | some t =>
    rw [resolved] at spelled
    simp only [Option.map_some, Option.some.injEq] at spelled
    exact ⟨t, rfl, utf8_encoded (resolve_scalars (utf8_decoded baseText).2 (utf8_decoded referenceText).2 resolved)
      spelled.symm⟩

/-! ### Components of the RFC 3987 grammar -/

/-- No word of `L` contains a character satisfying `S`. -/
def Avoids (L : Language Nat) (S : Nat → Prop) : Prop := ∀ w ∈ L, ∀ c ∈ w, ¬ S c

section Avoiding
variable {S : Nat → Prop}

private theorem avoids_range {lower upper : Nat} (outside : ∀ c, lower ≤ c → c ≤ upper → ¬ S c) :
    Avoids (Range lower upper) S := by
  rintro w ⟨cp, rfl, low, high⟩ c member
  simp only [List.mem_singleton] at member
  subst member
  exact outside c low high

private theorem avoids_one : Avoids 1 S := by
  intro w member c inside
  rw [Language.mem_one] at member
  subst member
  simp at inside

private theorem avoids_add {a b : Language Nat} (left : Avoids a S) (right : Avoids b S) : Avoids (a + b) S := by
  intro w member
  rcases (Language.mem_add _ _ _).mp member with inA | inB
  · exact left w inA
  · exact right w inB

private theorem avoids_mul {a b : Language Nat} (left : Avoids a S) (right : Avoids b S) : Avoids (a * b) S := by
  intro w member c inside
  obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp member
  rcases List.mem_append.mp inside with inX | inY
  · exact left x hx c inX
  · exact right y hy c inY

private theorem avoids_star {a : Language Nat} (each : Avoids a S) : Avoids a∗ S := by
  intro w member c inside
  obtain ⟨L, rfl, all⟩ := Language.mem_kstar.mp member
  obtain ⟨y, inL, inY⟩ := List.mem_flatten.mp inside
  exact each y (all y inL) c inY

private theorem avoids_pow {a : Language Nat} (each : Avoids a S) : ∀ n, Avoids (a ^ n) S
  | 0 => by rw [pow_zero]; exact avoids_one
  | n + 1 => by rw [pow_succ]; exact avoids_mul (avoids_pow each n) each

private theorem avoids_at_most {a : Language Nat} (each : Avoids a S) : ∀ n, Avoids (AtMost a n) S
  | 0 => avoids_one
  | n + 1 => avoids_add avoids_one (avoids_mul each (avoids_at_most each n))

end Avoiding

/-- Decompose an avoidance goal into the character ranges of a language. -/
macro "avoiding" : tactic => `(tactic| repeat (first
  | apply avoids_add | apply avoids_mul | apply avoids_star | apply avoids_one
  | apply avoids_pow | apply avoids_at_most
  | (apply avoids_range; intro c low high; omega)))

/-- The general delimiters `#`, `/`, `:` and `?` of RFC 3986 section 2.2. -/
def GenDelim (c : Nat) : Prop := c = 35 ∨ c = 47 ∨ c = 58 ∨ c = 63

private theorem avoids_scheme : Avoids Scheme GenDelim := by
  unfold Scheme Alpha Digit Ch GenDelim; avoiding

private theorem avoids_ipchar : Avoids Ipchar (fun c => c = 35 ∨ c = 47 ∨ c = 63) := by
  unfold Ipchar Iunreserved Unreserved Alpha Digit Ucschar PctEncoded Hex SubDelims Ch; avoiding

private theorem avoids_segment_nz_nc : Avoids SegmentNzNc GenDelim := by
  unfold SegmentNzNc Positive Iunreserved Unreserved Alpha Digit Ucschar PctEncoded Hex SubDelims Ch GenDelim
  avoiding

private theorem avoids_authority : Avoids Authority (fun c => c = 35 ∨ c = 47 ∨ c = 63) := by
  unfold Authority Optional Userinfo Host IpLiteral Ipv6 IpvFuture Ipv4 RegName DecOctet H16 Ls32 ColonPair H16Colon
    CompressedPrefix Positive Iunreserved Unreserved Alpha Digit Ucschar PctEncoded Hex SubDelims Ch
  avoiding

private theorem avoids_query : Avoids Query (· = 35) := by
  unfold Query Ipchar Iprivate Iunreserved Unreserved Alpha Digit Ucschar PctEncoded Hex SubDelims Ch; avoiding

private theorem avoids_fragment : Avoids Fragment (· = 35) := by
  unfold Fragment Ipchar Iunreserved Unreserved Alpha Digit Ucschar PctEncoded Hex SubDelims Ch; avoiding

private theorem avoids_mono {L : Language Nat} {S T : Nat → Prop} (avoids : Avoids L S) (weaker : ∀ c, T c → S c) :
    Avoids L T := fun w member c inside t => avoids w member c inside (weaker c t)

theorem ch_iff {c : Nat} {w : List Nat} : w ∈ Ch c ↔ w = [c] := by
  constructor
  · rintro ⟨cp, rfl, low, high⟩
    have : cp = c := by omega
    rw [this]
  · rintro rfl
    exact ⟨c, rfl, le_refl c, le_refl c⟩

theorem optional_iff {a : Language Nat} {w : List Nat} : w ∈ Optional a ↔ w = [] ∨ w ∈ a := by
  unfold Optional
  rw [Language.mem_add, Language.mem_one]

/-- Words of `a * b` with a cons on the left. -/
private theorem ch_mul_iff {c : Nat} {b : Language Nat} {w : List Nat} :
    w ∈ Ch c * b ↔ ∃ rest, w = c :: rest ∧ rest ∈ b := by
  rw [Language.mem_mul]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rw [ch_iff] at hx
    subst hx
    exact ⟨y, rfl, hy⟩
  · rintro ⟨rest, rfl, member⟩
    exact ⟨[c], ch_iff.mpr rfl, rest, member, rfl⟩

private theorem positive_nonempty {a : Language Nat} (noEmpty : [] ∉ a) {w : List Nat} (member : w ∈ Positive a) :
    w ≠ [] := by
  obtain ⟨x, hx, y, _, rfl⟩ := Language.mem_mul.mp member
  intro empty
  have : x = [] := (List.append_eq_nil_iff.mp empty).1
  exact noEmpty (this ▸ hx)

private theorem ipchar_nonempty : [] ∉ Ipchar := by
  simp [Ipchar, Iunreserved, Unreserved, Alpha, Digit, Ucschar, PctEncoded, SubDelims, Ch, Range, Language.mem_add,
    Language.mem_mul]

/-- `scheme ":"`, when the scheme is defined. -/
def schemePiece : Option (List Nat) → List Nat
  | some s => s ++ [58]
  | none => []
/-- `"//" authority`, when the authority is defined. -/
def authorityPiece : Option (List Nat) → List Nat
  | some a => 47 :: 47 :: a
  | none => []
/-- `"?" query`, when the query is defined. -/
def queryPiece : Option (List Nat) → List Nat
  | some q => 63 :: q
  | none => []
/-- `"#" fragment`, when the fragment is defined. -/
def fragmentPiece : Option (List Nat) → List Nat
  | some f => 35 :: f
  | none => []

theorem compose_pieces (p : Parts) : compose p = schemePiece p.scheme ++
    (authorityPiece p.authority ++ (p.path ++ (queryPiece p.query ++ fragmentPiece p.fragment))) := by
  cases p with
  | mk scheme authority path query fragment =>
    cases scheme <;> cases authority <;> cases query <;> cases fragment <;>
      simp [compose, schemePiece, authorityPiece, queryPiece, fragmentPiece]

/-- The hierarchical part of a reference: `"//" iauthority ipath-abempty`, or a
    path of `paths` when there is no authority. -/
def HierParts (paths : Language Nat) (p : Parts) : Prop :=
  match p.authority with
  | some a => a ∈ Authority ∧ p.path ∈ PathTail
  | none => p.path ∈ paths

/-- `[ "?" iquery ] [ "#" ifragment ]`. -/
def SuffixParts (p : Parts) : Prop :=
  (∀ q, p.query = some q → q ∈ Query) ∧ (∀ f, p.fragment = some f → f ∈ Fragment)

/-- The components of an IRI by the RFC 3987 `IRI` production:
    `scheme ":" ihier-part [ "?" iquery ] [ "#" ifragment ]`, where
    `ihier-part` is `"//" iauthority ipath-abempty` or an absolute, rootless
    or empty path. -/
def IriParts (p : Parts) : Prop :=
  (∃ s, p.scheme = some s ∧ s ∈ Scheme) ∧ HierParts (PathAbsolute + (PathRootless + 1)) p ∧ SuffixParts p

/-- The components of a relative reference by the RFC 3987 `irelative-ref`
    production: `irelative-part [ "?" iquery ] [ "#" ifragment ]`, where
    `irelative-part` is `"//" iauthority ipath-abempty` or an absolute,
    no-scheme or empty path. -/
def RelativeParts (p : Parts) : Prop :=
  p.scheme = none ∧ HierParts (PathAbsolute + (PathNoscheme + 1)) p ∧ SuffixParts p

private theorem suffix_compose {query fragment : Option (List Nat)} (queries : ∀ q, query = some q → q ∈ Query)
    (fragments : ∀ f, fragment = some f → f ∈ Fragment) : queryPiece query ++ fragmentPiece fragment ∈ Suffix := by
  unfold Suffix
  refine Language.append_mem_mul ?_ ?_
  · cases query with
    | none => exact optional_iff.mpr (Or.inl rfl)
    | some q => exact optional_iff.mpr (Or.inr (ch_mul_iff.mpr ⟨q, rfl, queries q rfl⟩))
  · cases fragment with
    | none => exact optional_iff.mpr (Or.inl rfl)
    | some f => exact optional_iff.mpr (Or.inr (ch_mul_iff.mpr ⟨f, rfl, fragments f rfl⟩))

private theorem suffix_decompose {w : List Nat} (member : w ∈ Suffix) :
    ∃ query fragment, (∀ q, query = some q → q ∈ Query) ∧ (∀ f, fragment = some f → f ∈ Fragment) ∧
      queryPiece query ++ fragmentPiece fragment = w := by
  unfold Suffix at member
  obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp member
  obtain ⟨query, queries, xIs⟩ : ∃ query, (∀ q, query = some q → q ∈ Query) ∧ queryPiece query = x := by
    rcases optional_iff.mp hx with rfl | inside
    · exact ⟨none, by simp, rfl⟩
    · obtain ⟨q, rfl, inQuery⟩ := ch_mul_iff.mp inside
      exact ⟨some q, fun q' same => by cases same; exact inQuery, rfl⟩
  obtain ⟨fragment, fragments, yIs⟩ : ∃ fragment, (∀ f, fragment = some f → f ∈ Fragment) ∧
      fragmentPiece fragment = y := by
    rcases optional_iff.mp hy with rfl | inside
    · exact ⟨none, by simp, rfl⟩
    · obtain ⟨f, rfl, inFragment⟩ := ch_mul_iff.mp inside
      exact ⟨some f, fun f' same => by cases same; exact inFragment, rfl⟩
  exact ⟨query, fragment, queries, fragments, by rw [xIs, yIs]⟩

private theorem authority_path_iff {w : List Nat} :
    w ∈ AuthorityPath ↔ ∃ a path, a ∈ Authority ∧ path ∈ PathTail ∧ w = 47 :: 47 :: (a ++ path) := by
  unfold AuthorityPath DoubleSlash
  rw [Language.mem_mul]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨one, rfl, two⟩ := ch_mul_iff.mp hx
    rw [ch_iff] at two
    subst two
    obtain ⟨a, ha, path, hpath, rfl⟩ := Language.mem_mul.mp hy
    exact ⟨a, path, ha, hpath, rfl⟩
  · rintro ⟨a, path, ha, hpath, rfl⟩
    exact ⟨[47, 47], ch_mul_iff.mpr ⟨[47], rfl, ch_iff.mpr rfl⟩, a ++ path, Language.append_mem_mul ha hpath, rfl⟩

/-- Every word of a hierarchical part is an optional authority and a path. -/
private theorem hier_compose {paths : Language Nat} {p : Parts} (hier : HierParts paths p) :
    authorityPiece p.authority ++ p.path ∈ AuthorityPath + paths := by
  unfold HierParts at hier
  rw [Language.mem_add]
  cases found : p.authority with
  | none => rw [found] at hier; exact Or.inr hier
  | some a =>
    rw [found] at hier
    exact Or.inl (authority_path_iff.mpr ⟨a, p.path, hier.1, hier.2, rfl⟩)

private theorem hier_decompose {paths : Language Nat} {w : List Nat} (member : w ∈ AuthorityPath + paths) :
    ∃ authority path, HierParts paths ⟨none, authority, path, none, none⟩ ∧ authorityPiece authority ++ path = w := by
  rcases (Language.mem_add _ _ _).mp member with withAuthority | withoutAuthority
  · obtain ⟨a, path, ha, hpath, rfl⟩ := authority_path_iff.mp withAuthority
    exact ⟨some a, path, ⟨ha, hpath⟩, rfl⟩
  · exact ⟨none, w, withoutAuthority, rfl⟩

/-- Recomposed IRI components are an IRI. -/
theorem iri_compose {p : Parts} (parts : IriParts p) : compose p ∈ IriLanguage := by
  obtain ⟨⟨s, found, scheme⟩, hier, queries, fragments⟩ := parts
  rw [compose_pieces, found]
  unfold IriLanguage schemePiece
  rw [List.append_assoc]
  refine Language.append_mem_mul scheme (Language.append_mem_mul (ch_iff.mpr rfl) ?_)
  rw [← List.append_assoc]
  refine Language.append_mem_mul ?_ (suffix_compose queries fragments)
  unfold HierPart
  have := hier_compose hier
  simpa [Language.mem_add, or_assoc] using this

/-- Recomposed relative-reference components are a relative reference. -/
theorem relative_compose {p : Parts} (parts : RelativeParts p) : compose p ∈ RelativeRef := by
  obtain ⟨found, hier, queries, fragments⟩ := parts
  rw [compose_pieces, found]
  unfold RelativeRef schemePiece
  rw [List.nil_append, ← List.append_assoc]
  refine Language.append_mem_mul ?_ (suffix_compose queries fragments)
  unfold RelativePart
  have := hier_compose hier
  simpa [Language.mem_add, or_assoc] using this

/-- Every IRI is the recomposition of IRI components. -/
theorem iri_decompose {w : List Nat} (member : w ∈ IriLanguage) : ∃ p, IriParts p ∧ compose p = w := by
  unfold IriLanguage at member
  obtain ⟨s, scheme, x, hx, rfl⟩ := Language.mem_mul.mp member
  obtain ⟨y, rfl, hy⟩ := ch_mul_iff.mp hx
  obtain ⟨hier, hierMember, sfx, sfxMember, rfl⟩ := Language.mem_mul.mp hy
  obtain ⟨query, fragment, queries, fragments, rfl⟩ := suffix_decompose sfxMember
  have hierMember' : hier ∈ AuthorityPath + (PathAbsolute + (PathRootless + 1)) := by
    unfold HierPart at hierMember
    simpa [Language.mem_add, or_assoc] using hierMember
  obtain ⟨authority, path, hierParts, rfl⟩ := hier_decompose hierMember'
  refine ⟨⟨some s, authority, path, query, fragment⟩, ⟨⟨s, rfl, scheme⟩, hierParts, queries, fragments⟩, ?_⟩
  rw [compose_pieces]
  simp [schemePiece, List.append_assoc]

/-- Every relative reference is the recomposition of relative components. -/
theorem relative_decompose {w : List Nat} (member : w ∈ RelativeRef) : ∃ p, RelativeParts p ∧ compose p = w := by
  unfold RelativeRef at member
  obtain ⟨hier, hierMember, sfx, sfxMember, rfl⟩ := Language.mem_mul.mp member
  obtain ⟨query, fragment, queries, fragments, rfl⟩ := suffix_decompose sfxMember
  have hierMember' : hier ∈ AuthorityPath + (PathAbsolute + (PathNoscheme + 1)) := by
    unfold RelativePart at hierMember
    simpa [Language.mem_add, or_assoc] using hierMember
  obtain ⟨authority, path, hierParts, rfl⟩ := hier_decompose hierMember'
  refine ⟨⟨none, authority, path, query, fragment⟩, ⟨rfl, hierParts, queries, fragments⟩, ?_⟩
  rw [compose_pieces]
  simp [schemePiece, List.append_assoc]

/-! ### Appendix B finds the grammatical components -/

/-- `takeWhile` and `dropWhile` stop where a word of passing characters ends. -/
private theorem while_split {p : Nat → Bool} {pre rest : List Nat} (passes : ∀ c ∈ pre, p c = true)
    (stops : ∀ c t, rest = c :: t → p c = false) :
    (pre ++ rest).takeWhile p = pre ∧ (pre ++ rest).dropWhile p = rest := by
  rw [List.takeWhile_append_of_pos passes, List.dropWhile_append_of_pos passes]
  cases rest with
  | nil => simp
  | cons c t =>
    have fails : ¬ p c = true := by simp [stops c t rfl]
    simp [List.takeWhile_cons_of_neg fails, List.dropWhile_cons_of_neg fails]

private theorem scheme_char_of {c : Nat} (plain : ¬ GenDelim c) : SchemeChar c = true := by
  unfold GenDelim at plain; simp [SchemeChar]; omega
private theorem authority_char_of {c : Nat} (plain : ¬ (c = 35 ∨ c = 47 ∨ c = 63)) : AuthorityChar c = true := by
  simp [AuthorityChar]; omega
private theorem path_char_of {c : Nat} (plain : ¬ (c = 35 ∨ c = 63)) : PathChar c = true := by
  simp [PathChar]; omega
private theorem query_char_of {c : Nat} (plain : ¬ c = 35) : QueryChar c = true := by
  simp [QueryChar]; omega

private theorem avoids_segment : Avoids Segment (fun c => c = 35 ∨ c = 47 ∨ c = 63) := avoids_star avoids_ipchar

private theorem avoids_segment_nz : Avoids SegmentNz (fun c => c = 35 ∨ c = 47 ∨ c = 63) :=
  avoids_mul avoids_ipchar (avoids_star avoids_ipchar)

private theorem avoids_path_tail : Avoids PathTail (fun c => c = 35 ∨ c = 63) := by
  unfold PathTail
  exact avoids_star (avoids_mul (by unfold Ch; exact avoids_range (by intro c low high; omega))
    (avoids_mono avoids_segment (by intro c h; omega)))

private theorem path_tail_head {t : List Nat} (member : t ∈ PathTail) : t = [] ∨ t.head? = some 47 := by
  unfold PathTail at member
  obtain ⟨L, rfl, all⟩ := Language.mem_kstar.mp member
  cases L with
  | nil => left; rfl
  | cons y rest =>
    right
    obtain ⟨tail, rfl, _⟩ := ch_mul_iff.mp (all y (by simp))
    simp

theorem segment_nz_head {seg : List Nat} (member : seg ∈ SegmentNz) :
    ∃ c cs, seg = c :: cs ∧ ¬ (c = 35 ∨ c = 47 ∨ c = 63) := by
  have nonempty := positive_nonempty ipchar_nonempty member
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  exact ⟨c, cs, rfl, avoids_segment_nz (c :: cs) member c (by simp)⟩

private theorem path_absolute_shape {t : List Nat} (member : t ∈ PathAbsolute) :
    ∃ rest, t = 47 :: rest ∧ rest.head? ≠ some 47 := by
  unfold PathAbsolute at member
  obtain ⟨rest, rfl, inner⟩ := ch_mul_iff.mp member
  refine ⟨rest, rfl, ?_⟩
  rcases optional_iff.mp inner with rfl | nz
  · simp
  · obtain ⟨seg, hseg, tail, _, rfl⟩ := Language.mem_mul.mp nz
    obtain ⟨c, cs, rfl, plain⟩ := segment_nz_head hseg
    simp only [List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
    omega

private theorem avoids_path_absolute : Avoids PathAbsolute (fun c => c = 35 ∨ c = 63) := by
  unfold PathAbsolute
  exact avoids_mul (by unfold Ch; exact avoids_range (by intro c low high; omega))
    (by unfold Optional; exact avoids_add avoids_one (avoids_mul (avoids_mono avoids_segment_nz
      (by intro c h; omega)) avoids_path_tail))

private theorem avoids_path_rootless : Avoids PathRootless (fun c => c = 35 ∨ c = 63) := by
  unfold PathRootless
  exact avoids_mul (avoids_mono avoids_segment_nz (by intro c h; omega)) avoids_path_tail

private theorem avoids_path_noscheme : Avoids PathNoscheme (fun c => c = 35 ∨ c = 63) := by
  unfold PathNoscheme
  exact avoids_mul (avoids_mono avoids_segment_nz_nc (by unfold GenDelim; intro c h; omega)) avoids_path_tail

private theorem scheme_nonempty {s : List Nat} (member : s ∈ Scheme) : s ≠ [] := by
  unfold Scheme at member
  obtain ⟨x, hx, y, _, rfl⟩ := Language.mem_mul.mp member
  unfold Alpha Range at hx
  rcases (Language.mem_add _ _ _).mp hx with ⟨cp, rfl, _⟩ | ⟨cp, rfl, _⟩ <;> simp

/-- A query and fragment begin with `?` or `#`. -/
private theorem suffix_head (query fragment : Option (List Nat)) :
    ∀ c t, queryPiece query ++ fragmentPiece fragment = c :: t → c = 63 ∨ c = 35 := by
  intro c t same
  cases query <;> cases fragment <;> simp [queryPiece, fragmentPiece] at same <;> omega

/-- Paths that never begin with `//` and avoid `?` and `#`. -/
def PlainPaths (paths : Language Nat) : Prop :=
  ∀ path ∈ paths, (∀ c ∈ path, ¬ (c = 35 ∨ c = 63)) ∧ ¬ [47, 47] <+: path

private theorem iri_paths : PlainPaths (PathAbsolute + (PathRootless + 1)) := by
  intro path member
  rcases (Language.mem_add _ _ _).mp member with absolute | other
  · refine ⟨avoids_path_absolute path absolute, ?_⟩
    obtain ⟨rest, rfl, second⟩ := path_absolute_shape absolute
    intro prefixed
    obtain ⟨x, same⟩ := prefixed
    rw [List.cons_append, List.cons.injEq] at same
    rw [← same.2] at second
    simp at second
  rcases (Language.mem_add _ _ _).mp other with rootless | empty
  · refine ⟨avoids_path_rootless path rootless, ?_⟩
    unfold PathRootless at rootless
    obtain ⟨seg, hseg, tail, _, rfl⟩ := Language.mem_mul.mp rootless
    obtain ⟨c, cs, rfl, plain⟩ := segment_nz_head hseg
    intro prefixed
    obtain ⟨x, same⟩ := prefixed
    simp only [List.cons_append, List.cons.injEq] at same
    omega
  · rw [Language.mem_one] at empty
    subst empty
    exact ⟨by simp, by simp⟩

private theorem relative_paths : PlainPaths (PathAbsolute + (PathNoscheme + 1)) := by
  intro path member
  rcases (Language.mem_add _ _ _).mp member with absolute | other
  · exact iri_paths path ((Language.mem_add _ _ _).mpr (Or.inl absolute))
  rcases (Language.mem_add _ _ _).mp other with noscheme | empty
  · refine ⟨avoids_path_noscheme path noscheme, ?_⟩
    unfold PathNoscheme at noscheme
    obtain ⟨seg, hseg, tail, _, rfl⟩ := Language.mem_mul.mp noscheme
    have nonempty := positive_nonempty (by
      simp [Iunreserved, Unreserved, Alpha, Digit, Ucschar, PctEncoded, SubDelims, Ch, Range, Language.mem_add,
        Language.mem_mul]) hseg
    obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil nonempty
    have plain := avoids_segment_nz_nc (c :: cs) hseg c (by simp)
    unfold GenDelim at plain
    intro prefixed
    obtain ⟨x, same⟩ := prefixed
    simp only [List.cons_append, List.cons.injEq] at same
    omega
  · rw [Language.mem_one] at empty
    subst empty
    exact ⟨by simp, by simp⟩

/-- After the scheme, Appendix B recovers the optional authority, the path, the
    query and the fragment of the grammar. -/
private theorem split_after_scheme {paths : Language Nat} (plainPaths : PlainPaths paths) {p : Parts}
    (hier : HierParts paths p) (suffix : SuffixParts p) :
    authorityPart (authorityPiece p.authority ++ (p.path ++ (queryPiece p.query ++ fragmentPiece p.fragment))) =
      (p.authority, p.path ++ (queryPiece p.query ++ fragmentPiece p.fragment)) ∧
    (p.path ++ (queryPiece p.query ++ fragmentPiece p.fragment)).takeWhile PathChar = p.path ∧
    (p.path ++ (queryPiece p.query ++ fragmentPiece p.fragment)).dropWhile PathChar =
      queryPiece p.query ++ fragmentPiece p.fragment ∧
    queryPart (queryPiece p.query ++ fragmentPiece p.fragment) = (p.query, fragmentPiece p.fragment) ∧
    fragmentPart (fragmentPiece p.fragment) = p.fragment := by
  obtain ⟨queries, fragments⟩ := suffix
  have sfxHead := suffix_head p.query p.fragment
  have pathChars : ∀ c ∈ p.path, ¬ (c = 35 ∨ c = 63) := by
    unfold HierParts at hier
    cases found : p.authority with
    | none => rw [found] at hier; exact (plainPaths p.path hier).1
    | some a => rw [found] at hier; exact avoids_path_tail p.path hier.2
  obtain ⟨takes, drops⟩ := while_split (p := PathChar) (fun c inside => path_char_of (pathChars c inside))
    (fun c t same => by
      rcases sfxHead c t same with rfl | rfl <;> rfl)
  refine ⟨?_, takes, drops, ?_, ?_⟩
  · unfold HierParts at hier
    cases found : p.authority with
    | none =>
      rw [found] at hier
      unfold authorityPart
      rw [if_neg]
      · simp [authorityPiece]
      · simp only [authorityPiece, List.nil_append]
        intro prefixed
        obtain ⟨x, same⟩ := prefixed
        have noSlashes := (plainPaths p.path hier).2
        match path : p.path with
        | [] =>
          rw [path, List.nil_append] at same
          have := sfxHead 47 (47 :: x) (by rw [← same]; rfl)
          omega
        | [c] =>
          rw [path] at same pathChars noSlashes
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at same
          obtain ⟨rfl, rest⟩ := same
          have := sfxHead 47 x rest.symm
          omega
        | c :: d :: more =>
          rw [path] at noSlashes same
          simp only [List.cons_append, List.cons.injEq] at same
          obtain ⟨rfl, rfl, _⟩ := same
          exact noSlashes ⟨more, by simp⟩
    | some a =>
      rw [found] at hier
      unfold authorityPart
      rw [if_pos (by simp [authorityPiece])]
      have two : ∀ x : List Nat, (47 :: 47 :: x).drop 2 = x := fun x => rfl
      simp only [authorityPiece, List.cons_append, two]
      have authorityChars : ∀ c ∈ a, AuthorityChar c = true :=
        fun c inside => authority_char_of (avoids_authority a hier.1 c inside)
      obtain ⟨takesA, dropsA⟩ := while_split (p := AuthorityChar) (rest := p.path ++ _) authorityChars
        (fun c t same => by
          rcases path_tail_head hier.2 with empty | slash
          · rw [empty, List.nil_append] at same
            rcases sfxHead c t same with rfl | rfl <;> rfl
          · obtain ⟨rest, restIs⟩ := List.head?_eq_some_iff.mp slash
            rw [restIs, List.cons_append, List.cons.injEq] at same
            rw [← same.1]; rfl)
      rw [takesA, dropsA]
  · unfold queryPart
    cases foundQuery : p.query with
    | none =>
      rw [if_neg]
      · simp [queryPiece]
      · cases foundFragment : p.fragment <;> simp [queryPiece, fragmentPiece]
    | some q =>
      rw [if_pos (by simp [queryPiece])]
      simp only [queryPiece, List.cons_append, List.tail_cons]
      have queryChars : ∀ c ∈ q, QueryChar c = true :=
        fun c inside => query_char_of (avoids_query q (queries q foundQuery) c inside)
      obtain ⟨takesQ, dropsQ⟩ := while_split (p := QueryChar) (rest := fragmentPiece p.fragment) queryChars
        (fun c t same => by
          cases foundFragment : p.fragment with
          | none => rw [foundFragment] at same; simp [fragmentPiece] at same
          | some f =>
            rw [foundFragment] at same
            simp only [fragmentPiece, List.cons.injEq] at same
            rw [← same.1]; rfl)
      rw [takesQ, dropsQ]
  · unfold fragmentPart
    cases p.fragment <;> simp [fragmentPiece]

/-- Appendix B splits a recomposed IRI into exactly its grammatical components. -/
theorem split_iri {p : Parts} (parts : IriParts p) : split (compose p) = p := by
  obtain ⟨⟨s, found, scheme⟩, hier, suffix⟩ := parts
  obtain ⟨authorities, takes, drops, queries, fragments⟩ := split_after_scheme iri_paths hier suffix
  have schemeChars : ∀ c ∈ s, SchemeChar c = true := fun c inside => scheme_char_of (avoids_scheme s scheme c inside)
  have composed : compose p = s ++ 58 :: (authorityPiece p.authority ++
      (p.path ++ (queryPiece p.query ++ fragmentPiece p.fragment))) := by
    rw [compose_pieces, found]; simp [schemePiece]
  have schemes : schemePart (compose p) = (some s, authorityPiece p.authority ++
      (p.path ++ (queryPiece p.query ++ fragmentPiece p.fragment))) := by
    rw [composed]
    obtain ⟨takesS, dropsS⟩ := while_split (p := SchemeChar) (rest := 58 :: (authorityPiece p.authority ++
      (p.path ++ (queryPiece p.query ++ fragmentPiece p.fragment)))) schemeChars (fun c t same => by
      simp only [List.cons.injEq] at same; rw [← same.1]; rfl)
    unfold schemePart
    rw [takesS, dropsS, if_pos ⟨scheme_nonempty scheme, rfl⟩]
    rfl
  cases p with
  | mk scheme' authority path query fragment =>
    simp only at found
    subst found
    simp only [split, schemes, authorities, takes, drops, queries, fragments]

/-- Appendix B splits a recomposed relative reference into exactly its
    grammatical components. -/
theorem split_relative {p : Parts} (parts : RelativeParts p) : split (compose p) = p := by
  obtain ⟨found, hier, suffix⟩ := parts
  obtain ⟨authorities, takes, drops, queries, fragments⟩ := split_after_scheme relative_paths hier suffix
  have composed : compose p = authorityPiece p.authority ++
      (p.path ++ (queryPiece p.query ++ fragmentPiece p.fragment)) := by
    rw [compose_pieces, found]; simp [schemePiece]
  have sfxHead := suffix_head p.query p.fragment
  have schemes : schemePart (compose p) = (none, compose p) := by
    unfold schemePart
    rw [if_neg]
    rw [composed]
    intro ⟨nonempty, colon⟩
    unfold HierParts at hier
    cases foundAuthority : p.authority with
    | some a =>
      rw [foundAuthority] at nonempty
      simp [authorityPiece, SchemeChar] at nonempty
    | none =>
      rw [foundAuthority] at hier nonempty colon
      simp only [authorityPiece, List.nil_append] at nonempty colon
      rcases (Language.mem_add _ _ _).mp hier with absolute | other
      · obtain ⟨rest, restIs, _⟩ := path_absolute_shape absolute
        rw [restIs] at nonempty
        simp [SchemeChar] at nonempty
      rcases (Language.mem_add _ _ _).mp other with noscheme | empty
      · unfold PathNoscheme at noscheme
        obtain ⟨seg, hseg, tail, htail, pathIs⟩ := Language.mem_mul.mp noscheme
        rw [← pathIs, List.append_assoc] at colon
        have segChars : ∀ c ∈ seg, SchemeChar c = true :=
          fun c inside => scheme_char_of (avoids_segment_nz_nc seg hseg c inside)
        obtain ⟨_, dropsS⟩ := while_split (p := SchemeChar) (rest := tail ++ _) segChars (fun c t same => by
          rcases path_tail_head htail with empty | slash
          · rw [empty, List.nil_append] at same
            rcases sfxHead c t same with rfl | rfl <;> rfl
          · obtain ⟨rest, restIs⟩ := List.head?_eq_some_iff.mp slash
            rw [restIs, List.cons_append, List.cons.injEq] at same
            rw [← same.1]; rfl)
        rw [dropsS] at colon
        rcases path_tail_head htail with empty | slash
        · rw [empty, List.nil_append] at colon
          obtain ⟨t, tIs⟩ := List.head?_eq_some_iff.mp colon
          have := sfxHead 58 t tIs
          omega
        · obtain ⟨rest, restIs⟩ := List.head?_eq_some_iff.mp slash
          rw [restIs] at colon
          simp at colon
      · rw [Language.mem_one] at empty
        rw [empty, List.nil_append] at nonempty
        cases sfx : queryPiece p.query ++ fragmentPiece p.fragment with
        | nil => rw [sfx] at nonempty; simp at nonempty
        | cons c t =>
          rw [sfx] at nonempty
          rcases sfxHead c t sfx with rfl | rfl <;> simp [SchemeChar] at nonempty
  cases p with
  | mk scheme' authority path query fragment =>
    simp only at found
    subst found
    simp only [split, schemes]
    rw [composed]
    simp only [authorities, takes, drops, queries, fragments]

/-- IRIs are exactly the words whose Appendix B components are IRI components. -/
theorem iri_parts_iff (w : List Nat) : w ∈ IriLanguage ↔ IriParts (split w) := by
  constructor
  · intro member
    obtain ⟨p, parts, rfl⟩ := iri_decompose member
    rwa [split_iri parts]
  · intro parts
    have := iri_compose parts
    rwa [compose_split] at this

/-- IRI references are exactly the words whose Appendix B components are IRI
    components or relative-reference components. -/
theorem reference_parts_iff (w : List Nat) :
    w ∈ ReferenceLanguage ↔ IriParts (split w) ∨ RelativeParts (split w) := by
  unfold ReferenceLanguage
  rw [Language.mem_add, iri_parts_iff]
  constructor
  · rintro (iri | relative)
    · exact Or.inl iri
    · obtain ⟨p, parts, rfl⟩ := relative_decompose relative
      rw [split_relative parts]
      exact Or.inr parts
  · rintro (iri | relative)
    · exact Or.inl iri
    · right
      have := relative_compose relative
      rwa [compose_split] at this

/-! ### Paths as `/`-separated segments -/

/-- Every `/`-separated piece of the word is an `isegment`. -/
def Pieces (w : List Nat) : Prop := ∀ piece ∈ w.splitOn 47, piece ∈ Segment

/-- Empty, or beginning with `/`. -/
def Rooted (w : List Nat) : Prop := w = [] ∨ w.head? = some 47

theorem take_while_passes {p : Nat → Bool} {l : List Nat} {c : Nat} (member : c ∈ l.takeWhile p) :
    p c = true := by
  have all := List.all_takeWhile (l := l) (p := p)
  rw [List.all_eq_true] at all
  exact all c member

private theorem drop_while_nil {p : Nat → Bool} {l : List Nat} (empty : l.dropWhile p = []) : ∀ c ∈ l, p c = true := by
  intro c member
  have whole := List.takeWhile_append_dropWhile (p := p) (l := l)
  rw [empty, List.append_nil] at whole
  rw [← whole] at member
  exact take_while_passes member

private theorem drop_while_all {p : Nat → Bool} {l : List Nat} (all : ∀ c ∈ l, p c = true) : l.dropWhile p = [] := by
  have := (while_split (pre := l) (rest := []) all (by simp)).2
  simpa using this

private theorem drop_take_while (p : Nat → Bool) (l : List Nat) : l.drop (l.takeWhile p).length = l.dropWhile p := by
  have whole := List.takeWhile_append_dropWhile (p := p) (l := l)
  calc l.drop (l.takeWhile p).length = (l.takeWhile p ++ l.dropWhile p).drop (l.takeWhile p).length := by
        rw [whole]
    _ = l.dropWhile p := List.drop_left' rfl

theorem star_cons {a : Language Nat} {x y : List Nat} (hx : x ∈ a) (hy : y ∈ a∗) : x ++ y ∈ a∗ := by
  obtain ⟨L, rfl, all⟩ := Language.mem_kstar.mp hy
  have joined : x ++ L.flatten = (x :: L).flatten := by simp
  rw [joined]
  exact Language.join_mem_kstar (by
    intro z member
    rcases List.mem_cons.mp member with rfl | inside
    · exact hx
    · exact all z inside)

private theorem segment_nil : [] ∈ Segment := Language.nil_mem_kstar _

private theorem segment_append {x y : List Nat} (hx : x ∈ Segment) (hy : y ∈ Segment) : x ++ y ∈ Segment := by
  unfold Segment at *
  obtain ⟨L, rfl, all⟩ := Language.mem_kstar.mp hx
  clear hx
  induction L with
  | nil => simpa using hy
  | cons z rest ih =>
    rw [List.flatten_cons, List.append_assoc]
    exact star_cons (all z (by simp)) (ih (fun v member => all v (by simp [member])))

private theorem segment_free {s : List Nat} (member : s ∈ Segment) : 47 ∉ s := fun inside =>
  avoids_segment s member 47 inside (by simp)

theorem pieces_free {v : List Nat} (free : 47 ∉ v) : Pieces v ↔ v ∈ Segment := by
  unfold Pieces
  rw [List.splitOn_eq_singleton free]
  simp

private theorem pieces_nil : Pieces [] := (pieces_free (by simp)).mpr segment_nil

theorem pieces_split {u v : List Nat} : Pieces (u ++ 47 :: v) ↔ Pieces u ∧ Pieces v := by
  unfold Pieces
  rw [List.splitOn_append_cons_self]
  simp only [List.mem_append]
  constructor
  · intro all
    exact ⟨fun piece member => all piece (Or.inl member), fun piece member => all piece (Or.inr member)⟩
  · rintro ⟨left, right⟩ piece (member | member)
    · exact left piece member
    · exact right piece member

private theorem pieces_slash {v : List Nat} : Pieces (47 :: v) ↔ Pieces v := by
  have := pieces_split (u := []) (v := v)
  simpa [pieces_nil] using this

/-- Every word is free of `/` or splits at its last `/`. -/
theorem last_slash_split (w : List Nat) : 47 ∉ w ∨ ∃ u v, w = u ++ 47 :: v ∧ 47 ∉ v := by
  by_cases slash : 47 ∈ w
  · right
    have whole := List.takeWhile_append_dropWhile (p := (· != 47)) (l := w.reverse)
    have free : 47 ∉ w.reverse.takeWhile (· != 47) := by
      intro inside; have := take_while_passes inside; simp at this
    generalize w.reverse.takeWhile (· != 47) = T at whole free
    cases rest : w.reverse.dropWhile (· != 47) with
    | nil =>
      have all := drop_while_nil rest 47 (List.mem_reverse.mpr slash)
      simp at all
    | cons c X =>
      have isSlash : c = 47 := by simpa using drop_while_stops rest
      subst isSlash
      rw [rest] at whole
      refine ⟨X.reverse, T.reverse, ?_, fun inside => free (List.mem_reverse.mp inside)⟩
      have := congrArg List.reverse whole
      rw [List.reverse_reverse, List.reverse_append, List.reverse_cons] at this
      rw [← this]
      simp
  · exact Or.inl slash

private theorem drop_free {v : List Nat} (free : 47 ∉ v) : v.reverse.dropWhile (· != 47) = [] := by
  apply drop_while_all
  intro c member
  have : c ≠ 47 := fun same => free (same ▸ List.mem_reverse.mp member)
  simpa using this

theorem pop_free {v : List Nat} (free : 47 ∉ v) : popSegment v = [] := by
  unfold popSegment
  simp [drop_free free]

theorem dir_free {v : List Nat} (free : 47 ∉ v) : (v.reverse.dropWhile (· != 47)).reverse = [] := by
  simp [drop_free free]

private theorem drop_last_slash {u v : List Nat} (free : 47 ∉ v) :
    (u ++ 47 :: v).reverse.dropWhile (· != 47) = 47 :: u.reverse := by
  rw [List.reverse_append, List.reverse_cons]
  have passes : ∀ c ∈ v.reverse, (c != 47) = true := by
    intro c member
    have : c ≠ 47 := fun same => free (same ▸ List.mem_reverse.mp member)
    simpa using this
  obtain ⟨_, drops⟩ := while_split (p := (· != 47)) (rest := 47 :: u.reverse) passes
    (fun c t same => by simp only [List.cons.injEq] at same; rw [← same.1]; rfl)
  simpa [List.append_assoc] using drops

theorem pop_last {u v : List Nat} (free : 47 ∉ v) : popSegment (u ++ 47 :: v) = u := by
  unfold popSegment
  rw [drop_last_slash free]
  simp

theorem dir_last {u v : List Nat} (free : 47 ∉ v) :
    ((u ++ 47 :: v).reverse.dropWhile (· != 47)).reverse = u ++ [47] := by
  rw [drop_last_slash free]
  simp

private theorem pieces_pop {o : List Nat} (pieces : Pieces o) : Pieces (popSegment o) := by
  rcases last_slash_split o with free | ⟨u, v, rfl, free⟩
  · rw [pop_free free]; exact pieces_nil
  · rw [pop_last free]; exact (pieces_split.mp pieces).1

private theorem rooted_pop {o : List Nat} (rooted : Rooted o) : Rooted (popSegment o) := by
  rcases last_slash_split o with free | ⟨u, v, rfl, free⟩
  · rw [pop_free free]; exact Or.inl rfl
  · rw [pop_last free]
    cases u with
    | nil => exact Or.inl rfl
    | cons c rest =>
      rcases rooted with empty | head
      · simp at empty
      · right; simpa using head

private theorem pieces_append_free {o s : List Nat} (pieces : Pieces o) (segment : s ∈ Segment) : Pieces (o ++ s) := by
  have sFree := segment_free segment
  rcases last_slash_split o with free | ⟨u, v, rfl, free⟩
  · have both : 47 ∉ o ++ s := by simp [free, sFree]
    rw [pieces_free both]
    exact segment_append ((pieces_free free).mp pieces) segment
  · rw [List.append_assoc, List.cons_append, pieces_split]
    obtain ⟨left, right⟩ := pieces_split.mp pieces
    refine ⟨left, ?_⟩
    have both : 47 ∉ v ++ s := by simp [free, sFree]
    rw [pieces_free both]
    exact segment_append ((pieces_free free).mp right) segment

/-- `Pieces` is the language `isegment *( "/" isegment )`. -/
private theorem pieces_iff {w : List Nat} : Pieces w ↔ w ∈ Segment * PathTail := by
  induction size : w.length using Nat.strong_induction_on generalizing w with
  | _ size ih =>
    constructor
    · intro pieces
      have whole := List.takeWhile_append_dropWhile (p := (· != 47)) (l := w)
      have headFree : 47 ∉ w.takeWhile (· != 47) := by
        intro inside
        have := take_while_passes inside
        simp at this
      cases rest : w.dropWhile (· != 47) with
      | nil =>
        rw [rest, List.append_nil] at whole
        have free : 47 ∉ w := by rw [← whole]; exact headFree
        have := Language.append_mem_mul ((pieces_free free).mp pieces) (Language.nil_mem_kstar (Ch 47 * Segment))
        simpa [PathTail] using this
      | cons c tail =>
        have isSlash : c = 47 := by simpa using drop_while_stops rest
        subst isSlash
        rw [rest] at whole
        have shorter : tail.length < w.length := by
          rw [← whole]
          simp only [List.length_append, List.length_cons]
          omega
        rw [← whole] at pieces ⊢
        obtain ⟨headPieces, tailPieces⟩ := pieces_split.mp pieces
        obtain ⟨seg, hseg, t, ht, tailIs⟩ := Language.mem_mul.mp
          ((ih tail.length (size ▸ shorter) rfl).mp tailPieces)
        refine Language.append_mem_mul ((pieces_free headFree).mp headPieces) ?_
        rw [← tailIs]
        unfold PathTail at ht ⊢
        have : 47 :: (seg ++ t) = (47 :: seg) ++ t := rfl
        rw [this]
        exact star_cons (ch_mul_iff.mpr ⟨seg, rfl, hseg⟩) ht
    · intro member
      obtain ⟨seg, hseg, t, ht, rfl⟩ := Language.mem_mul.mp member
      unfold PathTail at ht
      obtain ⟨L, rfl, all⟩ := Language.mem_kstar.mp ht
      clear ih size member ht
      induction L generalizing seg with
      | nil => simpa using (pieces_free (segment_free hseg)).mpr hseg
      | cons y L' ih =>
        obtain ⟨s1, rfl, hs1⟩ := ch_mul_iff.mp (all y (by simp))
        rw [List.flatten_cons, List.cons_append, pieces_split]
        exact ⟨(pieces_free (segment_free hseg)).mpr hseg, ih s1 hs1 (fun z member => all z (by simp [member]))⟩

theorem path_tail_iff {t : List Nat} : t ∈ PathTail ↔ Rooted t ∧ Pieces t := by
  constructor
  · intro member
    refine ⟨path_tail_head member, pieces_iff.mpr ?_⟩
    have := Language.append_mem_mul segment_nil member
    simpa using this
  · rintro ⟨rooted, pieces⟩
    rcases rooted with rfl | head
    · exact Language.nil_mem_kstar _
    · obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp head
      obtain ⟨seg, hseg, t, ht, restIs⟩ := Language.mem_mul.mp (pieces_iff.mp (pieces_slash.mp pieces))
      rw [← restIs]
      unfold PathTail at ht ⊢
      have : 47 :: (seg ++ t) = (47 :: seg) ++ t := rfl
      rw [this]
      exact star_cons (ch_mul_iff.mpr ⟨seg, rfl, hseg⟩) ht

private theorem segment_nz_segment {s : List Nat} (member : s ∈ SegmentNz) : s ∈ Segment := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp member
  exact star_cons hx hy

private theorem segment_nz_of {s : List Nat} (member : s ∈ Segment) (nonempty : s ≠ []) : s ∈ SegmentNz := by
  unfold Segment at member
  obtain ⟨L, rfl, all⟩ := Language.mem_kstar.mp member
  clear member
  induction L with
  | nil => simp at nonempty
  | cons z rest ih =>
    by_cases empty : z = []
    · subst empty
      exact ih (fun v inside => all v (by simp [inside])) (by rwa [List.flatten_cons, List.nil_append] at nonempty)
    · rw [List.flatten_cons]
      exact Language.append_mem_mul (all z (by simp))
        (Language.join_mem_kstar (fun v inside => all v (by simp [inside])))

private theorem pieces_of_path_absolute {w : List Nat} (member : w ∈ PathAbsolute) : Rooted w ∧ Pieces w := by
  unfold PathAbsolute at member
  obtain ⟨rest, rfl, inner⟩ := ch_mul_iff.mp member
  refine ⟨Or.inr rfl, pieces_slash.mpr ?_⟩
  rcases optional_iff.mp inner with rfl | nz
  · exact pieces_nil
  · obtain ⟨seg, hseg, t, ht, rfl⟩ := Language.mem_mul.mp nz
    exact pieces_iff.mpr (Language.append_mem_mul (segment_nz_segment hseg) ht)

private theorem pieces_of_path_rootless {w : List Nat} (member : w ∈ PathRootless) : Pieces w := by
  unfold PathRootless at member
  obtain ⟨seg, hseg, t, ht, rfl⟩ := Language.mem_mul.mp member
  exact pieces_iff.mpr (Language.append_mem_mul (segment_nz_segment hseg) ht)

private theorem pieces_of_path_noscheme {w : List Nat} (member : w ∈ PathNoscheme) : Pieces w := by
  unfold PathNoscheme at member
  obtain ⟨seg, hseg, t, ht, rfl⟩ := Language.mem_mul.mp member
  refine pieces_iff.mpr (Language.append_mem_mul ?_ ht)
  unfold SegmentNzNc Positive at hseg
  obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp hseg
  have each : ∀ z ∈ Iunreserved + (PctEncoded + (SubDelims + Ch 64)), z ∈ Ipchar := by
    intro z member
    unfold Ipchar
    simp only [Language.mem_add] at member ⊢
    rcases member with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  refine star_cons (each x hx) ?_
  obtain ⟨L, rfl, all⟩ := Language.mem_kstar.mp hy
  exact Language.join_mem_kstar (fun z inside => each z (all z inside))

/-- A path of segments that does not begin with `//` is an absolute, rootless
    or empty path. -/
theorem iri_path_of {w : List Nat} (pieces : Pieces w) (noDouble : ¬ [47, 47] <+: w) :
    w ∈ PathAbsolute + (PathRootless + 1) := by
  rw [Language.mem_add, Language.mem_add, Language.mem_one]
  obtain ⟨seg, hseg, t, ht, rfl⟩ := Language.mem_mul.mp (pieces_iff.mp pieces)
  by_cases empty : seg = []
  · subst empty
    simp only [List.nil_append] at noDouble ⊢
    rcases path_tail_head ht with rfl | head
    · exact Or.inr (Or.inr rfl)
    · left
      obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp head
      unfold PathAbsolute
      refine ch_mul_iff.mpr ⟨rest, rfl, optional_iff.mpr ?_⟩
      obtain ⟨rooted, restPieces⟩ := path_tail_iff.mp ht
      have restPieces' := pieces_slash.mp restPieces
      obtain ⟨seg', hseg', t', ht', restIs⟩ := Language.mem_mul.mp (pieces_iff.mp restPieces')
      by_cases empty' : seg' = []
      · subst empty'
        simp only [List.nil_append] at restIs
        subst restIs
        rcases path_tail_head ht' with rfl | head'
        · exact Or.inl rfl
        · obtain ⟨more, rfl⟩ := List.head?_eq_some_iff.mp head'
          exact absurd ⟨more, rfl⟩ noDouble
      · right
        rw [← restIs]
        exact Language.append_mem_mul (segment_nz_of hseg' empty') ht'
  · exact Or.inr (Or.inl (Language.append_mem_mul (segment_nz_of hseg empty) ht))

/-- The shape that dot-segment removal keeps: paths of segments, and rooted
    paths. -/
theorem remove_dots_shape (input output : List Nat) (inputPieces : Pieces input) (outputPieces : Pieces output) :
    Pieces (removeDots input output) ∧ (Rooted input → Rooted output → Rooted (removeDots input output)) := by
  induction size : input.length using Nat.strong_induction_on generalizing input output with
  | _ n ih =>
    by_cases empty : input = []
    · subst empty
      rw [removeDots]
      exact ⟨outputPieces, fun _ rooted => by simpa using rooted⟩
    rw [removeDots, dif_neg empty]
    by_cases parent : [46, 46, 47] <+: input
    · rw [dif_pos parent]
      obtain ⟨rest, rfl⟩ := parent
      have restPieces := (pieces_split (u := [46, 46]) (v := rest)).mp (by simpa using inputPieces)
      have shorter : rest.length < n := by
        rw [← size]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have step := ih rest.length shorter rest output restPieces.2 outputPieces rfl
      refine ⟨by simpa using step.1, fun rooted _ => ?_⟩
      rcases rooted with impossible | impossible <;> simp at impossible
    rw [dif_neg parent]
    by_cases current : [46, 47] <+: input
    · rw [dif_pos current]
      obtain ⟨rest, rfl⟩ := current
      have restPieces := (pieces_split (u := [46]) (v := rest)).mp (by simpa using inputPieces)
      have shorter : rest.length < n := by
        rw [← size]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have step := ih rest.length shorter rest output restPieces.2 outputPieces rfl
      refine ⟨by simpa using step.1, fun rooted _ => ?_⟩
      rcases rooted with impossible | impossible <;> simp at impossible
    rw [dif_neg current]
    by_cases skip : [47, 46, 47] <+: input
    · rw [dif_pos skip]
      obtain ⟨rest, rfl⟩ := skip
      have restPieces := (pieces_split (u := [46]) (v := rest)).mp
        (pieces_slash.mp (by simpa using inputPieces))
      have shorter : (47 :: rest).length < n := by
        rw [← size]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have step := ih (47 :: rest).length shorter (47 :: rest) output (pieces_slash.mpr restPieces.2) outputPieces rfl
      refine ⟨by simpa using step.1, fun _ rooted => by simpa using step.2 (Or.inr rfl) rooted⟩
    rw [dif_neg skip]
    by_cases finalSkip : input = [47, 46]
    · rw [dif_pos finalSkip]
      have shorter : [47].length < n := by
        rw [← size, finalSkip]
        simp
      have step := ih [47].length shorter [47] output (pieces_slash.mpr pieces_nil) outputPieces rfl
      exact ⟨step.1, fun _ rooted => step.2 (Or.inr rfl) rooted⟩
    rw [dif_neg finalSkip]
    by_cases back : [47, 46, 46, 47] <+: input
    · rw [dif_pos back]
      obtain ⟨rest, rfl⟩ := back
      have restPieces := (pieces_split (u := [46, 46]) (v := rest)).mp
        (pieces_slash.mp (by simpa using inputPieces))
      have shorter : (47 :: rest).length < n := by
        rw [← size]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have step := ih (47 :: rest).length shorter (47 :: rest) (popSegment output) (pieces_slash.mpr restPieces.2)
        (pieces_pop outputPieces) rfl
      refine ⟨by simpa using step.1, fun _ rooted => by simpa using step.2 (Or.inr rfl) (rooted_pop rooted)⟩
    rw [dif_neg back]
    by_cases finalBack : input = [47, 46, 46]
    · rw [dif_pos finalBack]
      have shorter : [47].length < n := by
        rw [← size, finalBack]
        simp
      have step := ih [47].length shorter [47] (popSegment output) (pieces_slash.mpr pieces_nil)
        (pieces_pop outputPieces) rfl
      exact ⟨step.1, fun _ rooted => step.2 (Or.inr rfl) (rooted_pop rooted)⟩
    rw [dif_neg finalBack]
    by_cases dropping : input = [46] ∨ input = [46, 46]
    · rw [if_pos dropping]
      exact ⟨outputPieces, fun _ rooted => rooted⟩
    rw [if_neg dropping]
    by_cases slash : input.head? = some 47
    · obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp slash
      simp only [firstSegment, List.length_cons]
      have whole := List.takeWhile_append_dropWhile (p := (· != 47)) (l := rest)
      have dropped : (47 :: rest).drop ((rest.takeWhile (· != 47)).length + 1) = rest.dropWhile (· != 47) := by
        rw [List.drop_succ_cons, drop_take_while]
      rw [dropped]
      have restPieces := pieces_slash.mp inputPieces
      obtain ⟨segPieces, tailPieces, tailRooted⟩ : Pieces (rest.takeWhile (· != 47)) ∧
          Pieces (rest.dropWhile (· != 47)) ∧ Rooted (rest.dropWhile (· != 47)) := by
        cases tail : rest.dropWhile (· != 47) with
        | nil =>
          rw [tail, List.append_nil] at whole
          rw [whole]
          exact ⟨restPieces, pieces_nil, Or.inl rfl⟩
        | cons c more =>
          have isSlash : c = 47 := by simpa using drop_while_stops tail
          subst isSlash
          rw [tail] at whole
          rw [← whole] at restPieces
          obtain ⟨left, right⟩ := pieces_split.mp restPieces
          exact ⟨left, pieces_slash.mpr right, Or.inr rfl⟩
      have moved : Pieces (output ++ 47 :: rest.takeWhile (· != 47)) := pieces_split.mpr ⟨outputPieces, segPieces⟩
      have shorter : (rest.dropWhile (· != 47)).length < n := by
        rw [← size]
        have sum := congrArg List.length whole
        rw [List.length_append] at sum
        simp only [List.length_cons]
        omega
      have step := ih (rest.dropWhile (· != 47)).length shorter (rest.dropWhile (· != 47))
        (output ++ 47 :: rest.takeWhile (· != 47)) tailPieces moved rfl
      refine ⟨step.1, fun _ rooted => step.2 tailRooted ?_⟩
      rcases rooted with rfl | head
      · exact Or.inr rfl
      · right
        obtain ⟨more, rfl⟩ := List.head?_eq_some_iff.mp head
        simp
    · rw [first_segment_eq slash]
      have whole := List.takeWhile_append_dropWhile (p := (· != 47)) (l := input)
      rw [drop_take_while]
      have segFree : 47 ∉ input.takeWhile (· != 47) := by
        intro inside; have := take_while_passes inside; simp at this
      obtain ⟨segment, tailPieces⟩ : input.takeWhile (· != 47) ∈ Segment ∧ Pieces (input.dropWhile (· != 47)) := by
        cases tail : input.dropWhile (· != 47) with
        | nil =>
          rw [tail, List.append_nil] at whole
          have free : 47 ∉ input := by rw [← whole]; exact segFree
          have := (pieces_free free).mp inputPieces
          rw [← whole] at this
          exact ⟨this, pieces_nil⟩
        | cons c more =>
          have isSlash : c = 47 := by simpa using drop_while_stops tail
          subst isSlash
          rw [tail] at whole
          rw [← whole] at inputPieces
          obtain ⟨left, right⟩ := pieces_split.mp inputPieces
          exact ⟨(pieces_free segFree).mp left, pieces_slash.mpr right⟩
      have nonempty : input.takeWhile (· != 47) ≠ [] := by
        obtain ⟨c, more, rfl⟩ := List.exists_cons_of_ne_nil empty
        have different : c ≠ 47 := by simpa using slash
        simp [List.takeWhile_cons, different]
      have shorter : (input.dropWhile (· != 47)).length < n := by
        rw [← size]
        have positive : 0 < (input.takeWhile (· != 47)).length := List.length_pos_iff.mpr nonempty
        have sum := congrArg List.length whole
        rw [List.length_append] at sum
        omega
      have step := ih (input.dropWhile (· != 47)).length shorter (input.dropWhile (· != 47))
        (output ++ input.takeWhile (· != 47)) tailPieces (pieces_append_free outputPieces segment) rfl
      refine ⟨step.1, fun rooted _ => ?_⟩
      rcases rooted with impossible | head
      · exact absurd impossible empty
      · exact absurd head slash

theorem merge_shape {b : Parts} (base : IriParts b) {path : List Nat} (pieces : Pieces path) :
    Pieces (merge b path) ∧ (b.authority.isSome → Rooted (merge b path)) := by
  obtain ⟨_, hier, _⟩ := base
  have basePieces : Pieces b.path ∧ (b.authority.isSome → Rooted b.path) := by
    unfold HierParts at hier
    cases found : b.authority with
    | some a =>
      rw [found] at hier
      exact ⟨(path_tail_iff.mp hier.2).2, fun _ => (path_tail_iff.mp hier.2).1⟩
    | none =>
      rw [found] at hier
      refine ⟨?_, by simp⟩
      rcases (Language.mem_add _ _ _).mp hier with absolute | other
      · exact (pieces_of_path_absolute absolute).2
      rcases (Language.mem_add _ _ _).mp other with rootless | empty
      · exact pieces_of_path_rootless rootless
      · rw [Language.mem_one] at empty; rw [empty]; exact pieces_nil
  unfold merge
  by_cases bare : b.authority.isSome ∧ b.path = []
  · rw [if_pos bare]
    exact ⟨pieces_slash.mpr pieces, fun _ => Or.inr rfl⟩
  · rw [if_neg bare]
    rcases last_slash_split b.path with free | ⟨u, v, pathIs, free⟩
    · rw [dir_free free, List.nil_append]
      refine ⟨pieces, fun authority => ?_⟩
      exfalso
      rcases basePieces.2 authority with empty | head
      · exact bare ⟨authority, empty⟩
      · obtain ⟨rest, restIs⟩ := List.head?_eq_some_iff.mp head
        exact free (by rw [restIs]; simp)
    · rw [pathIs, dir_last free, List.append_assoc, List.singleton_append]
      have uPieces := (pieces_split.mp (pathIs ▸ basePieces.1)).1
      refine ⟨pieces_split.mpr ⟨uPieces, pieces⟩, fun authority => ?_⟩
      cases u with
      | nil => exact Or.inr rfl
      | cons c rest =>
        rcases basePieces.2 authority with empty | head
        · rw [pathIs] at empty; simp at empty
        · rw [pathIs] at head; right; simpa using head

/-- The target components of resolving an IRI reference against an IRI are IRI
    components, unless the target has no authority and its path begins with
    `//`: then `"//"` would be read as an authority. -/
theorem transform_iri {b r : Parts} (base : IriParts b) (reference : IriParts r ∨ RelativeParts r)
    (plain : (transform b r).authority.isSome ∨ ¬ [47, 47] <+: (transform b r).path) :
    IriParts (transform b r) := by
  have baseParts := base
  obtain ⟨⟨s, foundScheme, scheme⟩, baseHier, baseQueries, baseFragments⟩ := base
  have clean : ∀ {path : List Nat}, Pieces path → Rooted path →
      removeDots path [] ∈ PathTail := fun {path} pieces rooted =>
    path_tail_iff.mpr ⟨(remove_dots_shape path [] pieces pieces_nil).2 rooted (Or.inl rfl),
      (remove_dots_shape path [] pieces pieces_nil).1⟩
  unfold transform at plain ⊢
  by_cases ownScheme : r.scheme.isSome
  · rw [if_pos ownScheme] at plain ⊢
    have referenceParts : IriParts r := by
      rcases reference with iri | relative
      · exact iri
      · rw [relative.1] at ownScheme; simp at ownScheme
    obtain ⟨scheme', hier, queries, fragments⟩ := referenceParts
    refine ⟨scheme', ?_, queries, fragments⟩
    unfold HierParts at hier ⊢
    simp only at hier ⊢
    cases found : r.authority with
    | some a =>
      rw [found] at hier
      exact ⟨hier.1, clean (path_tail_iff.mp hier.2).2 (path_tail_iff.mp hier.2).1⟩
    | none =>
      rw [found] at hier plain
      simp only [Option.isSome_none, Bool.false_eq_true, false_or] at plain
      apply iri_path_of _ plain
      refine (remove_dots_shape r.path [] ?_ pieces_nil).1
      rcases (Language.mem_add _ _ _).mp hier with absolute | other
      · exact (pieces_of_path_absolute absolute).2
      rcases (Language.mem_add _ _ _).mp other with rootless | empty
      · exact pieces_of_path_rootless rootless
      · rw [Language.mem_one] at empty; rw [empty]; exact pieces_nil
  rw [if_neg ownScheme] at plain ⊢
  have referenceParts : RelativeParts r := by
    rcases reference with iri | relative
    · obtain ⟨⟨s', found', _⟩, _⟩ := iri
      rw [found'] at ownScheme; simp at ownScheme
    · exact relative
  obtain ⟨_, hier, queries, fragments⟩ := referenceParts
  have baseScheme : ∃ s, b.scheme = some s ∧ s ∈ Scheme := ⟨s, foundScheme, scheme⟩
  by_cases ownAuthority : r.authority.isSome
  · rw [if_pos ownAuthority] at plain ⊢
    refine ⟨baseScheme, ?_, queries, fragments⟩
    unfold HierParts at hier ⊢
    simp only at hier ⊢
    obtain ⟨a, found⟩ := Option.isSome_iff_exists.mp ownAuthority
    rw [found] at hier ⊢
    exact ⟨hier.1, clean (path_tail_iff.mp hier.2).2 (path_tail_iff.mp hier.2).1⟩
  rw [if_neg ownAuthority] at plain ⊢
  have noAuthority : r.authority = none := Option.not_isSome_iff_eq_none.mp ownAuthority
  unfold HierParts at hier
  rw [noAuthority] at hier
  have targetHier : ∀ path : List Nat, Pieces path → (b.authority.isSome → Rooted path) →
      (b.authority.isSome ∨ ¬ [47, 47] <+: removeDots path []) →
      HierParts (PathAbsolute + (PathRootless + 1))
        { scheme := b.scheme, authority := b.authority, path := removeDots path [], query := r.query,
          fragment := r.fragment } := by
    intro path pieces rooted noDouble
    unfold HierParts
    simp only
    unfold HierParts at baseHier
    cases found : b.authority with
    | some a =>
      rw [found] at baseHier
      exact ⟨baseHier.1, clean pieces (rooted (by simp [found]))⟩
    | none =>
      rw [found] at noDouble
      simp only [Option.isSome_none, Bool.false_eq_true, false_or] at noDouble
      exact iri_path_of (remove_dots_shape path [] pieces pieces_nil).1 noDouble
  by_cases emptyPath : r.path = []
  · rw [if_pos emptyPath] at plain ⊢
    refine ⟨baseScheme, baseHier, ?_, fragments⟩
    intro q found
    by_cases own : r.query.isSome
    · rw [if_pos own] at found; exact queries q found
    · rw [if_neg own] at found; exact baseQueries q found
  rw [if_neg emptyPath] at plain ⊢
  by_cases rootedPath : r.path.head? = some 47
  · rw [if_pos rootedPath] at plain ⊢
    have absolute : r.path ∈ PathAbsolute := by
      rcases (Language.mem_add _ _ _).mp hier with absolute | other
      · exact absolute
      rcases (Language.mem_add _ _ _).mp other with noscheme | empty
      · exfalso
        unfold PathNoscheme at noscheme
        obtain ⟨seg, hseg, t, _, pathIs⟩ := Language.mem_mul.mp noscheme
        have nonempty := positive_nonempty (by
          simp [Iunreserved, Unreserved, Alpha, Digit, Ucschar, PctEncoded, SubDelims, Ch, Range, Language.mem_add,
            Language.mem_mul]) hseg
        obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil nonempty
        have plainChar := avoids_segment_nz_nc (c :: cs) hseg c (by simp)
        rw [← pathIs] at rootedPath
        simp only [List.cons_append, List.head?_cons, Option.some.injEq] at rootedPath
        unfold GenDelim at plainChar
        omega
      · rw [Language.mem_one] at empty; exact absurd empty emptyPath
    obtain ⟨rooted, pieces⟩ := pieces_of_path_absolute absolute
    exact ⟨baseScheme, targetHier r.path pieces (fun _ => rooted) plain, queries, fragments⟩
  rw [if_neg rootedPath] at plain ⊢
  have relativePieces : Pieces r.path := by
    rcases (Language.mem_add _ _ _).mp hier with absolute | other
    · exact (pieces_of_path_absolute absolute).2
    rcases (Language.mem_add _ _ _).mp other with noscheme | empty
    · exact pieces_of_path_noscheme noscheme
    · rw [Language.mem_one] at empty; rw [empty]; exact pieces_nil
  obtain ⟨mergedPieces, mergedRooted⟩ := merge_shape baseParts relativePieces
  exact ⟨baseScheme, targetHier (merge b r.path) mergedPieces mergedRooted plain, queries, fragments⟩

/-- Resolving an IRI reference against an IRI gives an IRI whose components are
    exactly the target components of RFC 3986 section 5.2.2, provided the
    target has an authority or a path that does not begin with `//`
    (`resolve_leaves_iri` shows that this proviso is needed). -/
theorem resolve_iri {base reference : List Nat} (baseIri : base ∈ IriLanguage)
    (referenceIri : reference ∈ ReferenceLanguage)
    (plain : (transform (split base) (split reference)).authority.isSome ∨
      ¬ [47, 47] <+: (transform (split base) (split reference)).path) :
    ∃ target, resolve base reference = some target ∧ target ∈ IriLanguage ∧
      split target = transform (split base) (split reference) := by
  have baseParts := (iri_parts_iff base).mp baseIri
  have referenceParts := (reference_parts_iff reference).mp referenceIri
  have parts := transform_iri baseParts referenceParts plain
  obtain ⟨⟨s, found, _⟩, _⟩ := baseParts
  refine ⟨compose (transform (split base) (split reference)), ?_, iri_compose parts, split_iri parts⟩
  unfold resolve
  rw [if_pos (Or.inr (by simp [found]))]

/-! ### The proviso of `resolve_iri` is needed -/

private theorem host_shape {h : List Nat} (member : h ∈ Host) : (∀ c ∈ h, c ≠ 58) ∨ h.head? = some 91 := by
  unfold Host at member
  rcases (Language.mem_add _ _ _).mp member with literal | other
  · right
    unfold IpLiteral at literal
    obtain ⟨rest, rfl, _⟩ := ch_mul_iff.mp literal
    rfl
  · left
    have avoids : Avoids (Ipv4 + RegName) (· = 58) := by
      unfold Ipv4 RegName DecOctet Iunreserved Unreserved Alpha Digit Ucschar PctEncoded Hex SubDelims Ch
      avoiding
    exact fun c inside same => avoids h other c inside same

/-- `:a` is no authority: its host would be empty and its port `a`. -/
private theorem colon_a_not_authority : [58, 97] ∉ Authority := by
  intro member
  unfold Authority at member
  obtain ⟨x, hx, y, hy, xy⟩ := Language.mem_mul.mp member
  have xNil : x = [] := by
    rcases optional_iff.mp hx with rfl | inside
    · rfl
    · exfalso
      obtain ⟨u, _, at64, hat, rfl⟩ := Language.mem_mul.mp inside
      rw [ch_iff] at hat
      subst hat
      have : 64 ∈ [58, 97] := by rw [← xy]; simp
      simp at this
  subst xNil
  rw [List.nil_append] at xy
  subst xy
  obtain ⟨h, hh, port, hport, hp⟩ := Language.mem_mul.mp hy
  rcases host_shape hh with free | literal
  · have hNil : h = [] := by
      cases h with
      | nil => rfl
      | cons c rest =>
        simp only [List.cons_append, List.cons.injEq] at hp
        exact absurd hp.1 (free c (by simp))
    subst hNil
    rw [List.nil_append] at hp
    subst hp
    rcases optional_iff.mp hport with impossible | inside
    · simp at impossible
    · obtain ⟨digits, same, hdigits⟩ := ch_mul_iff.mp inside
      simp only [List.cons.injEq, true_and] at same
      subst same
      have avoids : Avoids Digit∗ (· = 97) := by
        unfold Digit; avoiding
      exact avoids [97] hdigits 97 (by simp) rfl
  · obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp literal
    simp at hp

private theorem char_ipchar {c : Nat} (letter : 97 ≤ c ∧ c ≤ 122 ∨ c = 46 ∨ c = 58) : [c] ∈ Ipchar := by
  unfold Ipchar Iunreserved Unreserved Alpha Ch
  rcases letter with letter | dot | colon
  · simp only [Language.mem_add]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨c, rfl, letter.1, letter.2⟩)))
  · subst dot
    simp only [Language.mem_add]
    exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨46, rfl, le_refl _, le_refl _⟩)))))
  · subst colon
    simp only [Language.mem_add]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨58, rfl, le_refl _, le_refl _⟩)))

private theorem char_segment {c : Nat} (letter : 97 ≤ c ∧ c ≤ 122 ∨ c = 46 ∨ c = 58) : [c] ∈ Segment := by
  have := star_cons (char_ipchar letter) (Language.nil_mem_kstar Ipchar)
  simpa [Segment] using this

private theorem char_segment_nz {c : Nat} (letter : 97 ≤ c ∧ c ≤ 122 ∨ c = 46 ∨ c = 58) : [c] ∈ SegmentNz :=
  segment_nz_of (char_segment letter) (by simp)

private theorem example_dots : removeDots [47, 46, 47, 47, 58, 97] [] = [47, 47, 58, 97] := by
  rw [removeDots]
  simp
  rw [removeDots]
  simp [firstSegment]
  rw [removeDots]
  simp [firstSegment]
  rw [removeDots]
  simp

/-- The proviso of `resolve_iri` cannot be dropped: RFC 3986 section 5.2
    resolves the relative reference `/.//:a` against the IRI `a:b` to `a://:a`,
    which reads `:a` as an authority and is no IRI. -/
theorem resolve_leaves_iri :
    [97, 58, 98] ∈ IriLanguage ∧ [47, 46, 47, 47, 58, 97] ∈ ReferenceLanguage ∧
      resolve [97, 58, 98] [47, 46, 47, 47, 58, 97] = some [97, 58, 47, 47, 58, 97] ∧
      [97, 58, 47, 47, 58, 97] ∉ IriLanguage := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have parts : IriParts ⟨some [97], none, [98], none, none⟩ := by
      refine ⟨⟨[97], rfl, ?_⟩, ?_, by simp, by simp⟩
      · unfold Scheme Alpha
        have := Language.append_mem_mul (show [97] ∈ Range 65 90 + Range 97 122 from
          (Language.mem_add _ _ _).mpr (Or.inr ⟨97, rfl, by omega, by omega⟩))
          (Language.nil_mem_kstar (Alpha + (Digit + (Ch 43 + (Ch 45 + Ch 46)))))
        simpa [Alpha] using this
      · unfold HierParts
        simp only [Language.mem_add, Language.mem_one]
        refine Or.inr (Or.inl ?_)
        unfold PathRootless
        have := Language.append_mem_mul (char_segment_nz (c := 98) (Or.inl ⟨by omega, by omega⟩))
          (Language.nil_mem_kstar (Ch 47 * Segment))
        simpa [PathTail] using this
    have := iri_compose parts
    simpa [compose] using this
  · have parts : RelativeParts ⟨none, none, [47, 46, 47, 47, 58, 97], none, none⟩ := by
      refine ⟨rfl, ?_, by simp, by simp⟩
      unfold HierParts
      simp only [Language.mem_add]
      left
      unfold PathAbsolute
      refine ch_mul_iff.mpr ⟨[46, 47, 47, 58, 97], rfl, optional_iff.mpr (Or.inr ?_)⟩
      have tail : [47, 47, 58, 97] ∈ PathTail := by
        refine path_tail_iff.mpr ⟨Or.inr rfl, ?_⟩
        rw [pieces_slash, pieces_slash, pieces_free (by simp)]
        exact segment_append (char_segment (Or.inr (Or.inr rfl))) (char_segment (Or.inl ⟨by omega, by omega⟩))
      exact Language.append_mem_mul (l := SegmentNz) (m := PathTail) (a := [46]) (b := [47, 47, 58, 97])
        (char_segment_nz (Or.inr (Or.inl rfl))) tail
    have := relative_compose parts
    unfold ReferenceLanguage
    rw [Language.mem_add]
    right
    simpa [compose] using this
  · unfold resolve
    have base : split [97, 58, 98] = ⟨some [97], none, [98], none, none⟩ := by
      simp [split, schemePart, authorityPart, queryPart, fragmentPart, SchemeChar, PathChar]
    have reference : split [47, 46, 47, 47, 58, 97] = ⟨none, none, [47, 46, 47, 47, 58, 97], none, none⟩ := by
      simp [split, schemePart, authorityPart, queryPart, fragmentPart, SchemeChar, PathChar]
    rw [base, reference]
    simp [transform, example_dots, compose]
  · intro member
    have parts := (iri_parts_iff _).mp member
    have target : split [97, 58, 47, 47, 58, 97] = ⟨some [97], some [58, 97], [], none, none⟩ := by
      simp [split, schemePart, authorityPart, queryPart, fragmentPart, SchemeChar, AuthorityChar, PathChar]
    rw [target] at parts
    obtain ⟨_, hier, _⟩ := parts
    exact colon_a_not_authority hier.1

end Rowl.IriResolution
