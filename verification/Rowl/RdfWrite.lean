import Rowl.Turtle

/-!
The canonical serialization of raw RDF graphs that the N-Triples and Turtle
writers produce (`rdf_write.rs`), as functions of the graph, the terms these
syntaxes cannot carry, and the proof that `rdf_write::write_graph` writes
exactly that text or reports the first such term.

Every triple is the line `subject predicate object .` and a line feed
(`LinesText`). An IRI is an IRIREF whose characters stay raw where an IRIREF
may hold them raw and are UCHARs `\U` with eight hexadecimal digits otherwise
(`IriText`); a string keeps its characters raw except `"`, `\`, line feed and
carriage return, which are ECHARs (`StringText`); a literal carries its
datatype or language tag; a blank node of the scope `s` and the label `l` is
`_:b`, the two lowercase hexadecimal digits of each byte of `s`, `_` and those
of `l` (`BlankText`). N-Triples cannot carry an IRI that is not an absolute
RFC 3987 IRI, a lexical form that is not UTF-8, the datatype rdf:langString
without a tag, or a tag that is not a well-formed BCP 47 tag of LANGTAG's form;
Turtle, which resolves every IRIREF by RFC 3986 section 5.2, in this form
cannot carry an IRI that resolution changes either.
-/
namespace Rowl.RdfWrite
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open Rowl.NTriples (UnitAt AbsoluteIri LanguageTag LangStringBytes IriCharacter XsdStringBytes)
open Rowl.Unicode (Prefix)
open Rowl.TurtleTokens (Span Resolves)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ## Bytes and characters -/

/-- The byte of a number below 256. -/
def byte (n : Nat) : U8 := ⟨BitVec.ofNat 8 n⟩

theorem byte_val {n : Nat} (h : n < 256) : (byte n).val = n := by
  show (BitVec.ofNat 8 n).toNat = n
  rw [BitVec.toNat_ofNat]
  omega

/-- The uppercase hexadecimal digit of `n`, for `n` below 16. -/
def hexUpper (n : Nat) : U8 := byte (if n < 10 then 48 + n else 55 + n)

/-- The lowercase hexadecimal digit of `n`, for `n` below 16. -/
def hexLower (n : Nat) : U8 := byte (if n < 10 then 48 + n else 87 + n)

/-- The last `count` hexadecimal digits of `v`, the most significant first. -/
def Hex : Nat → Nat → List U8
  | 0, _ => []
  | count + 1, v => Hex count (v / 16) ++ [hexUpper (v % 16)]

/-- The UCHAR of the character `cp`: `\U` and its eight hexadecimal digits. -/
def Uchar (cp : Nat) : List U8 := 92#u8 :: 85#u8 :: Hex 8 cp

/-- The two lowercase hexadecimal digits of each byte. -/
def KeyText : List U8 → List U8
  | [] => []
  | b :: rest => hexLower (b.val / 16) :: hexLower (b.val % 16) :: KeyText rest

/-- The label the writers give the blank node of the scope `scope` and the
    label `label`: `b`, the digits of the scope, `_` and those of the label. -/
def WrittenLabel (scope label : List U8) : List U8 := 98#u8 :: KeyText scope ++ 95#u8 :: KeyText label

/-- The BLANK_NODE_LABEL of a blank node. -/
def BlankText (scope label : List U8) : List U8 := 95#u8 :: 58#u8 :: WrittenLabel scope label

/-- A decoded character has a positive width within the bytes. -/
theorem prefix_bounds {bs : List U8} {i cp w : Nat} (h : Prefix bs i = some (cp, w)) :
    i < bs.length ∧ 0 < w ∧ i + w ≤ bs.length := by
  unfold Prefix at h
  cases ha : bs[i]? with
  | none => simp [ha] at h
  | some a =>
    have hi : i < bs.length := (List.getElem?_eq_some_iff.mp ha).1
    simp only [ha, Option.bind_eq_bind, Option.bind_some] at h
    split_ifs at h with h1 h2 h3
    · simp at h
      omega
    · cases hb : bs[i + 1]? with
      | none => simp [hb] at h
      | some b =>
        have := (List.getElem?_eq_some_iff.mp hb).1
        simp only [hb, Option.bind_some] at h
        split_ifs at h
        simp at h
        omega
    · cases hb : bs[i + 1]? with
      | none => simp [hb] at h
      | some b =>
        cases hc : bs[i + 2]? with
        | none => simp [hb, hc] at h
        | some c =>
          have := (List.getElem?_eq_some_iff.mp hc).1
          simp only [hb, hc, Option.bind_some] at h
          split_ifs at h
          simp at h
          omega
    · cases hb : bs[i + 1]? with
      | none => simp [hb] at h
      | some b =>
        cases hc : bs[i + 2]? with
        | none => simp [hb, hc] at h
        | some c =>
          cases hd : bs[i + 3]? with
          | none => simp [hb, hc, hd] at h
          | some d =>
            have := (List.getElem?_eq_some_iff.mp hd).1
            simp only [hb, hc, hd, Option.bind_some] at h
            split_ifs at h
            simp at h
            omega

/-- The ECHAR letter of a character that a string escapes. -/
def EscapeLetter (cp : Nat) : Option Nat :=
  if cp = 34 then some 34 else if cp = 92 then some 92 else if cp = 10 then some 110
  else if cp = 13 then some 114 else none

/-- The characters of the UTF-8 bytes `s` from `i` in an IRIREF: raw where an
    IRIREF may hold them raw, and UCHARs otherwise. -/
noncomputable def IriText (s : List U8) (i : Nat) : List U8 :=
  match _h : Prefix s i with
  | some (cp, w) => (if IriCharacter cp then Span s i (i + w) else Uchar cp) ++ IriText s (i + w)
  | none => []
termination_by s.length - i
decreasing_by have := prefix_bounds _h; omega

/-- The bytes in a string of the character `cp` that occupies `i..j` of `s`:
    its ECHAR, or the character itself. -/
def StringChar (s : List U8) (i j cp : Nat) : List U8 :=
  match EscapeLetter cp with
  | some m => [92#u8, byte m]
  | none => Span s i j

/-- The characters of the UTF-8 bytes `s` from `i` in a string: raw, except
    the ECHARs of `"`, `\`, line feed and carriage return. -/
noncomputable def StringText (s : List U8) (i : Nat) : List U8 :=
  match _h : Prefix s i with
  | some (cp, w) => StringChar s i (i + w) cp ++ StringText s (i + w)
  | none => []
termination_by s.length - i
decreasing_by have := prefix_bounds _h; omega

/-! ## The text of a graph -/

/-- The IRIREF of the IRI `s`. -/
noncomputable def IriToken (s : List U8) : List U8 := 60#u8 :: IriText s 0 ++ [62#u8]

/-- What follows a literal's string: `^^` and its datatype, or `@` and its tag. -/
noncomputable def KindText : rdf.LiteralKind → List U8
  | .Datatype d => 94#u8 :: 94#u8 :: IriToken d.spelling.val
  | .Language t => 64#u8 :: t.val

/-- A literal: its string, then `^^` and its datatype or `@` and its tag. -/
noncomputable def LiteralText (l : rdf.RdfLiteral) : List U8 :=
  34#u8 :: StringText l.lexical.val 0 ++ 34#u8 :: KindText l.kind

noncomputable def SubjectText : rdf.Subject → List U8
  | .Iri v => IriToken v.spelling.val
  | .Blank b => BlankText b.scope.val b.label.val

noncomputable def ObjectText : rdf.Object → List U8
  | .Iri v => IriToken v.spelling.val
  | .Blank b => BlankText b.scope.val b.label.val
  | .Literal l => LiteralText l

/-- `subject predicate object` of a triple. -/
noncomputable def TripleText (t : rdf.Triple) : List U8 :=
  SubjectText t.subject ++ 32#u8 :: IriToken t.predicate.spelling.val ++ 32#u8 :: ObjectText t.object

/-- The line of a triple: its text, ` .` and a line feed. -/
noncomputable def LineText (t : rdf.Triple) : List U8 := TripleText t ++ [32#u8, 46#u8, 10#u8]

/-- The lines of the triples, in order. -/
noncomputable def LinesText : List rdf.Triple → List U8
  | [] => []
  | t :: ts => LineText t ++ LinesText ts

/-! ## The terms the syntaxes cannot carry -/

/-- The bytes are UTF-8. -/
def Utf8 (s : List U8) : Prop := ∃ word, Rowl.Regular.Utf8From s 0 word

/-- An ASCII letter. -/
def LetterByte (b : U8) : Prop := (65 ≤ b.val ∧ b.val ≤ 90) ∨ (97 ≤ b.val ∧ b.val ≤ 122)
/-- An ASCII letter or digit. -/
def AlnumByte (b : U8) : Prop := LetterByte b ∨ (48 ≤ b.val ∧ b.val ≤ 57)

/-- Subtags: each `-` followed by ASCII letters or digits. -/
inductive Subtags : List U8 → Prop
  | nil : Subtags []
  | cons {w rest} : w ≠ [] → (∀ b ∈ w, AlnumByte b) → Subtags rest → Subtags (45#u8 :: (w ++ rest))

/-- The form of LANGTAG: ASCII letters, then subtags. -/
def TagForm (t : List U8) : Prop :=
  ∃ head rest, t = head ++ rest ∧ head ≠ [] ∧ (∀ b ∈ head, LetterByte b) ∧ Subtags rest

/-- The IRI `s` cannot be written: it is not an absolute RFC 3987 IRI, or,
    for a syntax that resolves its IRIREFs (`resolved`), RFC 3986 resolution
    changes it. -/
noncomputable def IriFault (resolved : Bool) (s : List U8) : Option rdf_write.WriteError :=
  if ¬ AbsoluteIri s then some .InvalidIri
  else if resolved = true ∧ ¬ Resolves [] s s then some .IriChangedByResolution
  else none

/-- The fault of a literal: its lexical form is not UTF-8, its datatype is
    rdf:langString or an IRI that cannot be written, or its tag is not a
    well-formed tag of the LANGTAG form. -/
noncomputable def LiteralFault (resolved : Bool) (l : rdf.RdfLiteral) : Option rdf_write.WriteError :=
  if ¬ Utf8 l.lexical.val then some .MalformedLiteralUtf8
  else match l.kind with
    | .Datatype d =>
        if d.spelling.val = LangStringBytes then some .InvalidLiteralKind else IriFault resolved d.spelling.val
    | .Language t => if TagForm t.val ∧ LanguageTag t.val then none else some .InvalidLanguageTag

noncomputable def SubjectFault (resolved : Bool) : rdf.Subject → Option rdf_write.WriteError
  | .Iri v => IriFault resolved v.spelling.val
  | .Blank _ => none

noncomputable def ObjectFault (resolved : Bool) : rdf.Object → Option rdf_write.WriteError
  | .Iri v => IriFault resolved v.spelling.val
  | .Blank _ => none
  | .Literal l => LiteralFault resolved l

/-- The first fault of a triple: of its subject, predicate, then object. -/
noncomputable def TripleFault (resolved : Bool) (t : rdf.Triple) : Option rdf_write.WriteError :=
  (SubjectFault resolved t.subject).or
    ((IriFault resolved t.predicate.spelling.val).or (ObjectFault resolved t.object))

/-- The first fault of the triples, in order. -/
noncomputable def GraphFault (resolved : Bool) : List rdf.Triple → Option rdf_write.WriteError
  | [] => none
  | t :: ts => (TripleFault resolved t).or (GraphFault resolved ts)

/-- What a writer returns for the triples `ts`: their lines within the budget
    when no term is at fault, the first fault, or the exhausted budget. -/
def WriteCorrect (resolved : Bool) (ts : List rdf.Triple) (limit : Nat) : rdf_write.WriteResult → Prop
  | .Bytes b => GraphFault resolved ts = none ∧ b.val = LinesText ts ∧ b.val.length ≤ limit
  | .Error e => GraphFault resolved ts = some e ∨
      (GraphFault resolved ts = none ∧ e = .ResourceLimit ∧ limit < (LinesText ts).length)


/-! ## Decoding written bytes -/

/-- Decoding looks only at the bytes from its position. -/
theorem prefix_drop (bs : List U8) (i : Nat) : Prefix bs i = Prefix (bs.drop i) 0 := by
  unfold Prefix
  simp only [List.getElem?_drop, Nat.add_zero, Nat.zero_add]

/-- Decoding at the end of a prefix decodes the rest. -/
theorem prefix_append_left (pre l : List U8) (i : Nat) : Prefix (pre ++ l) (pre.length + i) = Prefix l i := by
  rw [prefix_drop, prefix_drop l]
  congr 1
  rw [← List.drop_drop, List.drop_left]

/-- A character is decoded from any bytes that agree with its own. -/
theorem prefix_agree {l l' : List U8} {cp w : Nat} (h : Prefix l 0 = some (cp, w))
    (agree : ∀ k, k < w → l'[k]? = l[k]?) : Prefix l' 0 = some (cp, w) := by
  have bounds := prefix_bounds h
  unfold Prefix at h ⊢
  cases ha : l[0]? with
  | none => simp [ha] at h
  | some a =>
    rw [agree 0 (by omega), ha]
    simp only [ha, Option.bind_eq_bind, Option.bind_some, Nat.zero_add] at h ⊢
    split_ifs at h ⊢ with h1 h2 h3
    · exact h
    · cases hb : l[1]? with
      | none => simp [hb] at h
      | some b =>
        simp only [hb, Option.bind_some] at h
        split_ifs at h with hp
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [agree 1 (by omega), hb]
          simp [hp, h]
    · cases hb : l[1]? with
      | none => simp [hb] at h
      | some b =>
        cases hc : l[2]? with
        | none => simp [hb, hc] at h
        | some c =>
          simp only [hb, hc, Option.bind_some] at h
          split_ifs at h with hp
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [agree 1 (by omega), agree 2 (by omega), hb, hc]
            simp [hp, h]
    · cases hb : l[1]? with
      | none => simp [hb] at h
      | some b =>
        cases hc : l[2]? with
        | none => simp [hb, hc] at h
        | some c =>
          cases hd : l[3]? with
          | none => simp [hb, hc, hd] at h
          | some d =>
            simp only [hb, hc, hd, Option.bind_some] at h
            split_ifs at h with hp
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              rw [agree 1 (by omega), agree 2 (by omega), agree 3 (by omega), hb, hc, hd]
              simp [hp, h]

/-- A character decoded from the first bytes of a list is decoded from any
    longer list. -/
theorem prefix_append_right {l : List U8} {cp w : Nat} (post : List U8) (h : Prefix l 0 = some (cp, w)) :
    Prefix (l ++ post) 0 = some (cp, w) := by
  have bounds := prefix_bounds h
  exact prefix_agree h fun k hk => List.getElem?_append_left (by omega)

/-- The character at `i` is also the first character of its own bytes. -/
theorem prefix_span {s : List U8} {i cp w : Nat} (h : Prefix s i = some (cp, w)) :
    Prefix (Span s i (i + w)) 0 = some (cp, w) := by
  rw [prefix_drop] at h
  have bounds := prefix_bounds h
  unfold Span
  rw [show i + w - i = w by omega]
  exact prefix_agree h fun k hk => by rw [List.getElem?_take]; simp [hk]


/-- An ASCII byte is a character of its own. -/
theorem prefix_ascii (b : U8) (rest : List U8) (h : b.val < 128) : Prefix (b :: rest) 0 = some (b.val, 1) := by
  simp [Prefix, h]

/-- The bytes of a decoded character are its canonical UTF-8 encoding. -/
theorem prefix_encoded {bs : List U8} {cp w : Nat} (h : Prefix bs 0 = some (cp, w)) :
    ∃ e, Rowl.Encoding.EncodeCorrect cp (some e) ∧ Rowl.Encoding.Bytes e = bs.take w := by
  rcases bs with _ | ⟨a, rest⟩
  · simp [Prefix] at h
  · by_cases h1 : a.val < 128
    · simp [Prefix, h1] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.One a, ⟨h1, rfl⟩, by simp [Rowl.Encoding.Bytes]⟩
    · by_cases h2 : a.val < 224
      · rcases rest with _ | ⟨b, rest⟩
        · simp [Prefix, h1, h2] at h
        · simp only [Prefix, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.bind_eq_bind,
            Option.bind_some, h1, h2, if_false, if_true, Nat.zero_add] at h
          split_ifs at h with hp
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨.Two a b, ⟨hp, rfl⟩, by simp [Rowl.Encoding.Bytes]⟩
      · by_cases h3 : a.val < 240
        · rcases rest with _ | ⟨b, _ | ⟨c, rest⟩⟩
          · simp [Prefix, h1, h2, h3] at h
          · simp [Prefix, h1, h2, h3] at h
          · simp only [Prefix, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.bind_eq_bind,
              Option.bind_some, h1, h2, h3, if_false, if_true, Nat.zero_add] at h
            split_ifs at h with hp
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨.Three a b c, ⟨hp, rfl⟩, by simp [Rowl.Encoding.Bytes]⟩
        · rcases rest with _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩
          · simp [Prefix, h1, h2, h3] at h
          · simp [Prefix, h1, h2, h3] at h
          · simp [Prefix, h1, h2, h3] at h
          · simp only [Prefix, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.bind_eq_bind,
              Option.bind_some, h1, h2, h3, if_false, if_true, Nat.zero_add] at h
            split_ifs at h with hp
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨.Four a b c d, ⟨hp, rfl⟩, by simp [Rowl.Encoding.Bytes]⟩

/-- The character at `i` of the bytes `mid` is decoded where they are written. -/
theorem prefix_written {pre mid post : List U8} {i cp w : Nat} (h : Prefix mid i = some (cp, w)) :
    Prefix (pre ++ mid ++ post) (pre.length + i) = some (cp, w) := by
  have bounds := prefix_bounds h
  rw [List.append_assoc, prefix_append_left, prefix_drop, List.drop_append_of_le_length (by omega)]
  rw [prefix_drop] at h
  exact prefix_append_right post h

/-- An ASCII byte is decoded where it is written. -/
theorem prefix_written_ascii {pre post : List U8} {b : U8} (h : b.val < 128) :
    Prefix (pre ++ b :: post) pre.length = some (b.val, 1) := by
  have := prefix_written (pre := pre) (mid := [b]) (post := post) (i := 0) (prefix_ascii b [] h)
  simpa using this

/-- The N-Triples unit of a written character. -/
theorem unit_written {pre mid post : List U8} {i cp w : Nat} (h : Prefix mid i = some (cp, w))
    {c : U32} {next : Usize} (hc : c.val = cp) (hn : next.val = pre.length + i + w) :
    UnitAt (pre ++ mid ++ post) (pre.length + i) c next := by
  have bounds := prefix_bounds h
  refine ⟨by omega, by simp only [List.length_append, List.length_cons]; omega, ?_⟩
  rw [prefix_written h, hc, hn]
  congr 2
  omega

/-- The N-Triples unit of a written ASCII byte. -/
theorem unit_written_ascii {pre post : List U8} {b : U8} (h : b.val < 128) {c : U32} {next : Usize}
    (hc : c.val = b.val) (hn : next.val = pre.length + 1) : UnitAt (pre ++ b :: post) pre.length c next := by
  refine ⟨by omega, by simp only [List.length_append, List.length_cons]; omega, ?_⟩
  rw [prefix_written_ascii h, hc, hn]
  congr 2
  omega

/-- The Turtle unit of a written character. -/
theorem turtle_unit_written {pre mid post : List U8} {i cp w : Nat} (h : Prefix mid i = some (cp, w)) :
    Rowl.TurtleTokens.Unit (pre ++ mid ++ post) (pre.length + i) cp (pre.length + i + w) := by
  have bounds := prefix_bounds h
  refine ⟨by omega, by simp only [List.length_append, List.length_cons]; omega, ?_⟩
  rw [prefix_written h]
  congr 2
  omega

/-- The Turtle unit of a written ASCII byte. -/
theorem turtle_unit_written_ascii {pre post : List U8} {b : U8} (h : b.val < 128) :
    Rowl.TurtleTokens.Unit (pre ++ b :: post) pre.length b.val (pre.length + 1) := by
  refine ⟨by omega, by simp only [List.length_append, List.length_cons]; omega, ?_⟩
  rw [prefix_written_ascii h]
  congr 2
  omega


/-! ## Writing within a budget -/

/-- A writer's result for the output `l` within `limit` bytes: `l`, or the
    exhausted budget when `l` does not fit. -/
def Fits (limit : Nat) (l : List U8) : core.result.Result (alloc.vec.Vec U8) rdf_write.WriteError → Prop
  | .Ok v => v.val = l ∧ l.length ≤ limit
  | .Err e => e = .ResourceLimit ∧ limit < l.length

theorem fits_err {limit : Nat} {A : List U8} {e : rdf_write.WriteError} (h : Fits limit A (.Err e)) (B : List U8) :
    Fits limit (A ++ B) (.Err e) := by
  obtain ⟨rfl, over⟩ := h
  exact ⟨rfl, by simp; omega⟩

theorem fits_ok {limit : Nat} {A : List U8} {v : alloc.vec.Vec U8} (h : Fits limit A (.Ok v)) :
    v.val = A ∧ A.length ≤ limit := h

@[simp] theorem from_residual_write {T : Type} (e : rdf_write.WriteError) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame rdf_write.WriteError) (.Err e) = .ok (.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]

theorem put_spec (output : alloc.vec.Vec U8) (byte : U8) (limit : Usize) :
    ∃ r, rdf_write.put output byte limit = .ok r ∧ Fits limit.val (output.val ++ [byte]) r := by
  unfold rdf_write.put
  by_cases room : output.val.length < limit.val
  · obtain ⟨v, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec output byte (by have := limit.hBounds; scalar_tac))
    exact ⟨.Ok v, by simp [alloc.vec.Vec.len_val, room, push], contents, by simp; omega⟩
  · exact ⟨.Err .ResourceLimit, by simp [alloc.vec.Vec.len_val, room], rfl, by simp; omega⟩

theorem put_from_spec (output : alloc.vec.Vec U8) (bytes : Slice U8) (index limit : Usize)
    (fits : output.val.length ≤ limit.val) :
    ∃ r, rdf_write.put_from output bytes index limit = .ok r ∧
      Fits limit.val (output.val ++ bytes.val.drop index.val) r := by
  rw [rdf_write.put_from]
  by_cases more : index.val < bytes.val.length
  · have lookup : Slice.index_usize bytes index = .ok bytes.val[index.val] := by
      simp [Slice.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
      (by have := bytes.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have split : bytes.val.drop index.val = bytes.val[index.val] :: bytes.val.drop (index.val + 1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨r, run, correct⟩ := put_spec output bytes.val[index.val] limit
    rcases r with v | e
    · obtain ⟨hv, hfit⟩ := fits_ok correct
      obtain ⟨r', run', correct'⟩ := put_from_spec v bytes next limit (by rw [hv]; exact hfit)
      refine ⟨r', ?_, ?_⟩
      · simp [Slice.len_val, more, lookup, run, core.result.Result.Insts.CoreOpsTry.branch, add, run']
      · rw [hv, nextIs] at correct'
        rw [split]
        simpa using correct'
    · refine ⟨.Err e, ?_, ?_⟩
      · simp [Slice.len_val, more, lookup, run, core.result.Result.Insts.CoreOpsTry.branch]
      · rw [split]
        simpa using fits_err correct (bytes.val.drop (index.val + 1))
  · have empty : bytes.val.drop index.val = [] := List.drop_eq_nil_of_le (by omega)
    exact ⟨.Ok output, by simp [Slice.len_val, more], by simp [empty], by simp [empty]; exact fits⟩
termination_by bytes.val.length - index.val
decreasing_by omega

theorem put_span_spec (output bytes : alloc.vec.Vec U8) (index finish limit : Usize)
    (fits : output.val.length ≤ limit.val) (range : finish.val ≤ bytes.val.length) :
    ∃ r, rdf_write.put_span output bytes index finish limit = .ok r ∧
      Fits limit.val (output.val ++ Span bytes.val index.val finish.val) r := by
  rw [rdf_write.put_span]
  by_cases more : index.val < finish.val
  · have inside : index.val < bytes.val.length := by omega
    have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) bytes index =
        .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
      (by have := bytes.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have split : Span bytes.val index.val finish.val = bytes.val[index.val] :: Span bytes.val (index.val + 1) finish.val := by
      unfold Span
      rw [List.drop_eq_getElem_cons inside, show finish.val - index.val = (finish.val - (index.val + 1)) + 1 by omega,
        List.take_succ_cons]
    obtain ⟨r, run, correct⟩ := put_spec output bytes.val[index.val] limit
    rcases r with v | e
    · obtain ⟨hv, hfit⟩ := fits_ok correct
      obtain ⟨r', run', correct'⟩ := put_span_spec v bytes next finish limit (by rw [hv]; exact hfit) range
      refine ⟨r', ?_, ?_⟩
      · simp [UScalar.lt_equiv, more, lookup, run, core.result.Result.Insts.CoreOpsTry.branch, add, run']
      · rw [hv, nextIs] at correct'
        rw [split]
        simpa using correct'
    · refine ⟨.Err e, ?_, ?_⟩
      · simp [UScalar.lt_equiv, more, lookup, run, core.result.Result.Insts.CoreOpsTry.branch]
      · rw [split]
        simpa using fits_err correct (Span bytes.val (index.val + 1) finish.val)
  · have empty : Span bytes.val index.val finish.val = [] := by
      unfold Span
      rw [show finish.val - index.val = 0 by omega, List.take_zero]
    exact ⟨.Ok output, by simp [UScalar.lt_equiv, more], by simp [empty], by simp [empty]; exact fits⟩
termination_by finish.val - index.val
decreasing_by omega


/-! ## Writing terms -/

theorem u8_add {x y : U8} (h : x.val + y.val < 256) : (x + y : Result U8) = .ok (byte (x.val + y.val)) := by
  obtain ⟨z, add, value⟩ := WP.spec_imp_exists (U8.add_spec (x := x) (y := y) (by simp [U8.max, U8.numBits]; omega))
  rw [add]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [byte_val (by omega)]
  simpa using value

theorem u8_div {x : U8} : ∃ q : U8, (x / 16#u8 : Result U8) = .ok q ∧ q.val = x.val / 16 := by
  obtain ⟨q, div, value⟩ := WP.spec_imp_exists (U8.div_spec (x := x) (y := 16#u8) (by simp))
  exact ⟨q, div, by simpa using value⟩

theorem u8_rem {x : U8} : ∃ q : U8, (x % 16#u8 : Result U8) = .ok q ∧ q.val = x.val % 16 := by
  obtain ⟨q, rem, value⟩ := WP.spec_imp_exists (U8.rem_spec (x := x) (y := 16#u8) (by simp))
  exact ⟨q, rem, by simpa using value⟩

theorem hex_lower_spec (n : U8) (small : n.val < 16) : rdf_write.hex_lower n = .ok (hexLower n.val) := by
  unfold rdf_write.hex_lower hexLower
  by_cases digit : n.val < 10
  · have : (48#u8 : U8).val + n.val < 256 := by simp; omega
    simp [UScalar.lt_equiv, digit, u8_add this]
  · have : (87#u8 : U8).val + n.val < 256 := by simp; omega
    simp [UScalar.lt_equiv, digit, u8_add this]

theorem put_key_spec (output key : alloc.vec.Vec U8) (index limit : Usize) (fits : output.val.length ≤ limit.val) :
    ∃ r, rdf_write.put_key output key index limit = .ok r ∧
      Fits limit.val (output.val ++ KeyText (key.val.drop index.val)) r := by
  rw [rdf_write.put_key]
  by_cases more : index.val < key.val.length
  · have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) key index =
        .ok key.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
      (by have := key.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have split : key.val.drop index.val = key.val[index.val] :: key.val.drop (index.val + 1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨high, div, highValue⟩ := u8_div (x := key.val[index.val])
    obtain ⟨low, rem, lowValue⟩ := u8_rem (x := key.val[index.val])
    have highSmall : high.val < 16 := by rw [highValue]; have := key.val[index.val].hBounds; scalar_tac
    have lowSmall : low.val < 16 := by rw [lowValue]; omega
    obtain ⟨r1, run1, c1⟩ := put_spec output (hexLower high.val) limit
    rcases r1 with v1 | e1
    · obtain ⟨h1, f1⟩ := fits_ok c1
      obtain ⟨r2, run2, c2⟩ := put_spec v1 (hexLower low.val) limit
      rcases r2 with v2 | e2
      · obtain ⟨h2, f2⟩ := fits_ok c2
        obtain ⟨r3, run3, c3⟩ := put_key_spec v2 key next limit (by rw [h2]; exact f2)
        refine ⟨r3, ?_, ?_⟩
        · simp [alloc.vec.Vec.len_val, more, lookup, div, hex_lower_spec high highSmall, run1,
            core.result.Result.Insts.CoreOpsTry.branch, rem, hex_lower_spec low lowSmall, run2, add, run3]
        · rw [h2, h1, nextIs] at c3
          rw [split]
          simpa [KeyText, highValue, lowValue] using c3
      · refine ⟨.Err e2, ?_, ?_⟩
        · simp [alloc.vec.Vec.len_val, more, lookup, div, hex_lower_spec high highSmall, run1,
            core.result.Result.Insts.CoreOpsTry.branch, rem, hex_lower_spec low lowSmall, run2]
        · rw [h1] at c2
          rw [split]
          simpa [KeyText, highValue, lowValue] using fits_err c2 (KeyText (key.val.drop (index.val + 1)))
    · refine ⟨.Err e1, ?_, ?_⟩
      · simp [alloc.vec.Vec.len_val, more, lookup, div, hex_lower_spec high highSmall, run1,
          core.result.Result.Insts.CoreOpsTry.branch]
      · rw [split]
        simpa [KeyText, highValue, lowValue] using
          fits_err c1 (hexLower (key.val[index.val].val % 16) :: KeyText (key.val.drop (index.val + 1)))
  · have empty : key.val.drop index.val = [] := List.drop_eq_nil_of_le (by omega)
    exact ⟨.Ok output, by simp [alloc.vec.Vec.len_val, more], by simp [empty, KeyText], by
      simp [empty, KeyText]; exact fits⟩
termination_by key.val.length - index.val
decreasing_by omega

theorem put_blank_spec (output : alloc.vec.Vec U8) (node : rdf.BlankNode) (limit : Usize)
    (fits : output.val.length ≤ limit.val) :
    ∃ r, rdf_write.put_blank output node limit = .ok r ∧
      Fits limit.val (output.val ++ BlankText node.scope.val node.label.val) r := by
  unfold rdf_write.put_blank
  obtain ⟨r1, run1, c1⟩ := put_from_spec output (Array.to_slice (Array.make 3#usize [95#u8, 58#u8, 98#u8])) 0#usize limit fits
  rw [Rowl.TurtleTokens.slice_array] at c1
  rcases r1 with v1 | e1
  · obtain ⟨h1, f1⟩ := fits_ok c1
    obtain ⟨r2, run2, c2⟩ := put_key_spec v1 node.scope 0#usize limit (by rw [h1]; exact f1)
    rcases r2 with v2 | e2
    · obtain ⟨h2, f2⟩ := fits_ok c2
      obtain ⟨r3, run3, c3⟩ := put_spec v2 95#u8 limit
      rcases r3 with v3 | e3
      · obtain ⟨h3, f3⟩ := fits_ok c3
        obtain ⟨r4, run4, c4⟩ := put_key_spec v3 node.label 0#usize limit (by rw [h3]; exact f3)
        refine ⟨r4, ?_, ?_⟩
        · simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2, run3, run4]
        · rw [h3, h2, h1] at c4
          simpa [BlankText, WrittenLabel] using c4
      · refine ⟨.Err e3, ?_, ?_⟩
        · simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2, run3]
        · rw [h2, h1] at c3
          simpa [BlankText, WrittenLabel] using fits_err c3 (KeyText node.label.val)
    · refine ⟨.Err e2, ?_, ?_⟩
      · simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2]
      · rw [h1] at c2
        simpa [BlankText, WrittenLabel] using fits_err c2 (95#u8 :: KeyText node.label.val)
  · refine ⟨.Err e1, ?_, ?_⟩
    · simp [run1, core.result.Result.Insts.CoreOpsTry.branch]
    · simpa [BlankText, WrittenLabel] using fits_err c1 (KeyText node.scope.val ++ 95#u8 :: KeyText node.label.val)

theorem hex_upper_spec (n : U32) (small : n.val < 16) : rdf_write.hex_upper n = .ok (hexUpper n.val) := by
  unfold rdf_write.hex_upper hexUpper
  by_cases digit : n.val < 10
  · obtain ⟨d, add, value⟩ := WP.spec_imp_exists (U32.add_spec (x := 48#u32) (y := n) (by scalar_tac))
    have dv : d.val = 48 + n.val := by simpa using value
    have cast : UScalar.cast .U8 d = byte (48 + n.val) := by
      apply UScalar.eq_of_val_eq
      rw [byte_val (by omega)]
      simp [UScalar.cast_val_eq, dv]
      omega
    simp [digit, add, cast]
  · obtain ⟨d, add, value⟩ := WP.spec_imp_exists (U32.add_spec (x := 55#u32) (y := n) (by scalar_tac))
    have dv : d.val = 55 + n.val := by simpa using value
    have cast : UScalar.cast .U8 d = byte (55 + n.val) := by
      apply UScalar.eq_of_val_eq
      rw [byte_val (by omega)]
      simp [UScalar.cast_val_eq, dv]
      omega
    simp [digit, add, cast]

theorem put_hex_spec (output : alloc.vec.Vec U8) (value count : U32) (limit : Usize)
    (fits : output.val.length ≤ limit.val) :
    ∃ r, rdf_write.put_hex output value count limit = .ok r ∧
      Fits limit.val (output.val ++ Hex count.val value.val) r := by
  rw [rdf_write.put_hex]
  by_cases zero : count.val = 0
  · have : count = 0#u32 := by apply UScalar.eq_of_val_eq; simpa using zero
    subst this
    exact ⟨.Ok output, by simp, by simp [Hex], by simp [Hex]; exact fits⟩
  · obtain ⟨q, div, qValue⟩ := WP.spec_imp_exists (U32.div_spec (x := value) (y := 16#u32) (by simp))
    obtain ⟨c, sub, cValue⟩ := WP.spec_imp_exists (U32.sub_spec (x := count) (y := 1#u32) (by simp; omega))
    obtain ⟨m, rem, mValue⟩ := WP.spec_imp_exists (U32.rem_spec (x := value) (y := 16#u32) (by simp))
    have qIs : q.val = value.val / 16 := by simpa using qValue
    have cIs : c.val = count.val - 1 := by simpa using cValue.1
    have mIs : m.val = value.val % 16 := by simpa using mValue
    have mSmall : m.val < 16 := by rw [mIs]; omega
    have nonzero : count ≠ 0#u32 := by intro h; apply zero; rw [h]; rfl
    have unfoldHex : Hex count.val value.val = Hex c.val q.val ++ [hexUpper m.val] := by
      rw [cIs, qIs, mIs]
      obtain ⟨k, hk⟩ : ∃ k, count.val = k + 1 := ⟨count.val - 1, by omega⟩
      rw [hk, Hex]
      simp
    obtain ⟨r1, run1, c1⟩ := put_hex_spec output q c limit fits
    rcases r1 with v1 | e1
    · obtain ⟨h1, f1⟩ := fits_ok c1
      obtain ⟨r2, run2, c2⟩ := put_spec v1 (hexUpper m.val) limit
      refine ⟨r2, ?_, ?_⟩
      · simp [nonzero, div, sub, run1, core.result.Result.Insts.CoreOpsTry.branch, rem,
          hex_upper_spec m mSmall, run2]
      · rw [h1] at c2
        rw [unfoldHex]
        simpa using c2
    · refine ⟨.Err e1, ?_, ?_⟩
      · simp [nonzero, div, sub, run1, core.result.Result.Insts.CoreOpsTry.branch]
      · rw [unfoldHex]
        simpa using fits_err c1 [hexUpper m.val]
termination_by count.val
decreasing_by omega

theorem put_uchar_spec (output : alloc.vec.Vec U8) (cp : U32) (limit : Usize) :
    ∃ r, rdf_write.put_uchar output cp limit = .ok r ∧ Fits limit.val (output.val ++ Uchar cp.val) r := by
  unfold rdf_write.put_uchar
  obtain ⟨r1, run1, c1⟩ := put_spec output 92#u8 limit
  rcases r1 with v1 | e1
  · obtain ⟨h1, f1⟩ := fits_ok c1
    obtain ⟨r2, run2, c2⟩ := put_spec v1 85#u8 limit
    rcases r2 with v2 | e2
    · obtain ⟨h2, f2⟩ := fits_ok c2
      obtain ⟨r3, run3, c3⟩ := put_hex_spec v2 cp 8#u32 limit (by rw [h2]; exact f2)
      refine ⟨r3, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2, run3], ?_⟩
      rw [h2, h1] at c3
      simpa [Uchar] using c3
    · refine ⟨.Err e2, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2], ?_⟩
      rw [h1] at c2
      simpa [Uchar] using fits_err c2 (Hex 8 cp.val)
  · refine ⟨.Err e1, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
    simpa [Uchar] using fits_err c1 (85#u8 :: Hex 8 cp.val)

theorem iri_raw_spec (cp : U32) : rdf_write.iri_raw cp = .ok (decide (IriCharacter cp.val)) := by
  unfold rdf_write.iri_raw IriCharacter
  by_cases a : 32 < cp.val
  · by_cases b : cp.val = 60
    · simp [UScalar.lt_equiv, UScalar.eq_equiv, a, b]
    · by_cases c : cp.val = 62
      · simp [UScalar.lt_equiv, UScalar.eq_equiv, a, b, c]
      · by_cases d : cp.val = 34
        · simp [UScalar.lt_equiv, UScalar.eq_equiv, a, b, c, d]
        · by_cases e : cp.val = 123
          · simp [UScalar.lt_equiv, UScalar.eq_equiv, a, b, c, d, e]
          · by_cases f : cp.val = 125
            · simp [UScalar.lt_equiv, UScalar.eq_equiv, a, b, c, d, e, f]
            · by_cases g : cp.val = 124
              · simp [UScalar.lt_equiv, UScalar.eq_equiv, a, b, c, d, e, f, g]
              · by_cases h : cp.val = 94
                · simp [UScalar.lt_equiv, UScalar.eq_equiv, a, b, c, d, e, f, g, h]
                · by_cases i : cp.val = 96
                  · simp [UScalar.lt_equiv, UScalar.eq_equiv, a, b, c, d, e, f, g, h, i]
                  · by_cases j : cp.val = 92
                    · simp [UScalar.lt_equiv, UScalar.eq_equiv, a, b, c, d, e, f, g, h, i, j]
                    · simp [UScalar.lt_equiv, UScalar.eq_equiv, a, b, c, d, e, f, g, h, i, j]
  · simp [UScalar.lt_equiv, a]


/-! ## Writing IRIs and strings -/

theorem iri_text_cons {s : List U8} {i cp w : Nat} (h : Prefix s i = some (cp, w)) :
    IriText s i = (if IriCharacter cp then Span s i (i + w) else Uchar cp) ++ IriText s (i + w) := by
  rw [IriText]
  split
  · rename_i cp' w' h'
    rw [h] at h'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    rfl
  · rename_i h'
    rw [h] at h'
    exact absurd h' (by simp)

theorem iri_text_nil {s : List U8} {i : Nat} (h : Prefix s i = none) : IriText s i = [] := by
  rw [IriText]
  split
  · rename_i cp' w' h'
    rw [h] at h'
    exact absurd h' (by simp)
  · rfl

theorem string_text_cons {s : List U8} {i cp w : Nat} (h : Prefix s i = some (cp, w)) :
    StringText s i = StringChar s i (i + w) cp ++ StringText s (i + w) := by
  rw [StringText]
  split
  · rename_i cp' w' h'
    rw [h] at h'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    rfl
  · rename_i h'
    rw [h] at h'
    exact absurd h' (by simp)

theorem string_text_nil {s : List U8} {i : Nat} (h : Prefix s i = none) : StringText s i = [] := by
  rw [StringText]
  split
  · rename_i cp' w' h'
    rw [h] at h'
    exact absurd h' (by simp)
  · rfl

theorem prefix_end (s : List U8) : Prefix s s.length = none := by
  simp [Prefix]

theorem utf8_from_le {s : List U8} {i : Nat} {word : List Nat} (valid : Rowl.Regular.Utf8From s i word) :
    i ≤ s.length := by
  cases valid with
  | endOfInput => omega
  | character _ _ fits _ => omega

/-- A character starts wherever UTF-8 bytes continue. -/
theorem utf8_from_step {s : List U8} {i : Nat} {word : List Nat} (valid : Rowl.Regular.Utf8From s i word)
    (more : i < s.length) : ∃ cp w tail, Prefix s i = some (cp, w) ∧ Rowl.Regular.Utf8From s (i + w) tail := by
  cases valid with
  | endOfInput => omega
  | character found positive fits tail => exact ⟨_, _, _, found, tail⟩

/-- The steps of the actual decoder through UTF-8 bytes. -/
theorem decode_utf8 (s : alloc.vec.Vec U8) (i : Usize) {word : List Nat}
    (valid : Rowl.Regular.Utf8From s.val i.val word) :
    (i.val = s.val.length ∧ unicode.decode_next s i = .ok .End) ∨
    (∃ (cp : U32) (next : Usize) (tail : List Nat), unicode.decode_next s i = .ok (.Scalar cp next) ∧
      i.val < next.val ∧ next.val ≤ s.val.length ∧ Prefix s.val i.val = some (cp.val, next.val - i.val) ∧
      Rowl.Regular.Utf8From s.val next.val tail) := by
  obtain ⟨r, run, correct⟩ := Rowl.Unicode.decode_next_total_correct s i
  have bound := utf8_from_le valid
  rcases r with _ | ⟨cp, next⟩ | error
  · exact Or.inl ⟨correct, run⟩
  · obtain ⟨advanced, fits, found⟩ := correct
    obtain ⟨cp', w, tail, found', rest⟩ := utf8_from_step valid (by omega)
    rw [found] at found'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj found')
    refine Or.inr ⟨cp, next, tail, run, advanced, fits, found, ?_⟩
    rwa [show i.val + (next.val - i.val) = next.val by omega] at rest
  · cases error with
    | InvalidPosition position => simp [Rowl.Unicode.StepCorrect] at correct; omega
    | InvalidUtf8 position =>
      obtain ⟨-, inside, none⟩ := correct
      obtain ⟨cp', w, tail, found', rest⟩ := utf8_from_step valid inside
      rw [none] at found'
      exact absurd found' (by simp)
    | NonXmlCharacter a b => exact absurd correct (by simp [Rowl.Unicode.StepCorrect])

theorem put_iri_character_spec (output spelling : alloc.vec.Vec U8) (index next : Usize) (cp : U32)
    (limit : Usize) (fits : output.val.length ≤ limit.val) (range : next.val ≤ spelling.val.length) :
    ∃ r, rdf_write.put_iri_character output spelling index next cp limit = .ok r ∧
      Fits limit.val (output.val ++ (if IriCharacter cp.val then Span spelling.val index.val next.val
        else Uchar cp.val)) r := by
  unfold rdf_write.put_iri_character
  by_cases raw : IriCharacter cp.val
  · obtain ⟨r, run, correct⟩ := put_span_spec output spelling index next limit fits range
    exact ⟨r, by simp [iri_raw_spec, raw, run], by simpa [raw] using correct⟩
  · obtain ⟨r, run, correct⟩ := put_uchar_spec output cp limit
    exact ⟨r, by simp [iri_raw_spec, raw, run], by simpa [raw] using correct⟩

theorem put_iri_from_spec (output spelling : alloc.vec.Vec U8) (index limit : Usize)
    (fits : output.val.length ≤ limit.val) {word : List Nat}
    (valid : Rowl.Regular.Utf8From spelling.val index.val word) :
    ∃ r, rdf_write.put_iri_from output spelling index limit = .ok r ∧
      Fits limit.val (output.val ++ IriText spelling.val index.val) r := by
  rw [rdf_write.put_iri_from]
  rcases decode_utf8 spelling index valid with ⟨atEnd, run⟩ | ⟨cp, next, tail, run, advanced, bounded, found, rest⟩
  · have empty : IriText spelling.val index.val = [] := by rw [atEnd]; exact iri_text_nil (prefix_end _)
    exact ⟨.Ok output, by simp [run], by simp [empty], by simp [empty]; exact fits⟩
  · have unfoldText := iri_text_cons found
    rw [show index.val + (next.val - index.val) = next.val by omega] at unfoldText
    obtain ⟨r1, run1, c1⟩ := put_iri_character_spec output spelling index next cp limit fits bounded
    rcases r1 with v1 | e1
    · obtain ⟨h1, f1⟩ := fits_ok c1
      obtain ⟨r2, run2, c2⟩ := put_iri_from_spec v1 spelling next limit (by rw [h1]; exact f1) rest
      refine ⟨r2, by simp [run, run1, core.result.Result.Insts.CoreOpsTry.branch, run2], ?_⟩
      rw [h1] at c2
      rw [unfoldText]
      simpa using c2
    · refine ⟨.Err e1, by simp [run, run1, core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
      rw [unfoldText]
      simpa using fits_err c1 (IriText spelling.val next.val)
termination_by spelling.val.length - index.val
decreasing_by omega

theorem put_iri_spec (output : alloc.vec.Vec U8) (iri : rdf.RdfIri) (limit : Usize)
    (valid : Utf8 iri.spelling.val) :
    ∃ r, rdf_write.put_iri output iri limit = .ok r ∧
      Fits limit.val (output.val ++ IriToken iri.spelling.val) r := by
  obtain ⟨word, valid⟩ := valid
  unfold rdf_write.put_iri
  obtain ⟨r1, run1, c1⟩ := put_spec output 60#u8 limit
  rcases r1 with v1 | e1
  · obtain ⟨h1, f1⟩ := fits_ok c1
    obtain ⟨r2, run2, c2⟩ := put_iri_from_spec v1 iri.spelling 0#usize limit (by rw [h1]; exact f1) valid
    rcases r2 with v2 | e2
    · obtain ⟨h2, f2⟩ := fits_ok c2
      obtain ⟨r3, run3, c3⟩ := put_spec v2 62#u8 limit
      refine ⟨r3, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2, run3], ?_⟩
      rw [h2, h1] at c3
      simpa [IriToken] using c3
    · refine ⟨.Err e2, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2], ?_⟩
      rw [h1] at c2
      simpa [IriToken] using fits_err c2 [62#u8]
  · refine ⟨.Err e1, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
    simpa [IriToken] using fits_err c1 (IriText iri.spelling.val 0 ++ [62#u8])

theorem string_escape_spec (cp : U32) :
    ∃ m : U8, rdf_write.string_escape cp = .ok m ∧
      (EscapeLetter cp.val = none → m.val = 0) ∧ (∀ e, EscapeLetter cp.val = some e → m.val = e) := by
  unfold rdf_write.string_escape EscapeLetter
  by_cases a : cp.val = 34
  · exact ⟨34#u8, by simp [UScalar.eq_equiv, a], by simp [a], by simp [a]⟩
  · by_cases b : cp.val = 92
    · exact ⟨92#u8, by simp [UScalar.eq_equiv, a, b], by simp [a, b], by simp [a, b]⟩
    · by_cases c : cp.val = 10
      · exact ⟨110#u8, by simp [UScalar.eq_equiv, a, b, c], by simp [a, b, c], by simp [a, b, c]⟩
      · by_cases d : cp.val = 13
        · exact ⟨114#u8, by simp [UScalar.eq_equiv, a, b, c, d], by simp [a, b, c, d], by simp [a, b, c, d]⟩
        · exact ⟨0#u8, by simp [UScalar.eq_equiv, a, b, c, d], by simp, by simp [a, b, c, d]⟩

theorem escape_letter_small {cp m : Nat} (h : EscapeLetter cp = some m) : m < 256 ∧ m ≠ 0 := by
  unfold EscapeLetter at h
  split_ifs at h <;> simp at h <;> omega

theorem put_string_character_spec (output lexical : alloc.vec.Vec U8) (index next : Usize) (cp : U32)
    (limit : Usize) (fits : output.val.length ≤ limit.val) (range : next.val ≤ lexical.val.length) :
    ∃ r, rdf_write.put_string_character output lexical index next cp limit = .ok r ∧
      Fits limit.val (output.val ++ StringChar lexical.val index.val next.val cp.val) r := by
  unfold rdf_write.put_string_character StringChar
  obtain ⟨m, mRun, mNone, mSome⟩ := string_escape_spec cp
  cases letter : EscapeLetter cp.val with
  | none =>
    have zero : m = 0#u8 := by apply UScalar.eq_of_val_eq; simpa using mNone letter
    obtain ⟨r, run, correct⟩ := put_span_spec output lexical index next limit fits range
    exact ⟨r, by simp [mRun, zero, run], correct⟩
  | some e =>
    have mIs : m.val = e := mSome e letter
    have small := escape_letter_small letter
    have nonzero : m ≠ 0#u8 := by intro h; rw [h] at mIs; simp at mIs; omega
    have mByte : m = byte e := by apply UScalar.eq_of_val_eq; rw [byte_val small.1]; exact mIs
    obtain ⟨r1, run1, c1⟩ := put_spec output 92#u8 limit
    rcases r1 with v1 | e1
    · obtain ⟨h1, f1⟩ := fits_ok c1
      obtain ⟨r2, run2, c2⟩ := put_spec v1 m limit
      refine ⟨r2, by simp [mRun, nonzero, run1, core.result.Result.Insts.CoreOpsTry.branch, run2], ?_⟩
      rw [h1, mByte] at c2
      simpa using c2
    · refine ⟨.Err e1, by simp [mRun, nonzero, run1, core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
      simpa using fits_err c1 [byte e]

theorem put_string_from_spec (output lexical : alloc.vec.Vec U8) (index limit : Usize)
    (fits : output.val.length ≤ limit.val) {word : List Nat}
    (valid : Rowl.Regular.Utf8From lexical.val index.val word) :
    ∃ r, rdf_write.put_string_from output lexical index limit = .ok r ∧
      Fits limit.val (output.val ++ StringText lexical.val index.val) r := by
  rw [rdf_write.put_string_from]
  rcases decode_utf8 lexical index valid with ⟨atEnd, run⟩ | ⟨cp, next, tail, run, advanced, bounded, found, rest⟩
  · have empty : StringText lexical.val index.val = [] := by rw [atEnd]; exact string_text_nil (prefix_end _)
    exact ⟨.Ok output, by simp [run], by simp [empty], by simp [empty]; exact fits⟩
  · have unfoldText := string_text_cons found
    rw [show index.val + (next.val - index.val) = next.val by omega] at unfoldText
    obtain ⟨r1, run1, c1⟩ := put_string_character_spec output lexical index next cp limit fits bounded
    rcases r1 with v1 | e1
    · obtain ⟨h1, f1⟩ := fits_ok c1
      obtain ⟨r2, run2, c2⟩ := put_string_from_spec v1 lexical next limit (by rw [h1]; exact f1) rest
      refine ⟨r2, by simp [run, run1, core.result.Result.Insts.CoreOpsTry.branch, run2], ?_⟩
      rw [h1] at c2
      rw [unfoldText]
      simpa using c2
    · refine ⟨.Err e1, by simp [run, run1, core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
      rw [unfoldText]
      simpa using fits_err c1 (StringText lexical.val next.val)
termination_by lexical.val.length - index.val
decreasing_by omega


/-! ## Writing triples -/

/-- The bytes of a literal's lexical form and datatype are UTF-8. -/
def LiteralUtf8 (l : rdf.RdfLiteral) : Prop :=
  Utf8 l.lexical.val ∧ (match l.kind with
    | .Datatype d => Utf8 d.spelling.val
    | .Language _ => True)

def SubjectUtf8 : rdf.Subject → Prop
  | .Iri v => Utf8 v.spelling.val
  | .Blank _ => True

def ObjectUtf8 : rdf.Object → Prop
  | .Iri v => Utf8 v.spelling.val
  | .Blank _ => True
  | .Literal l => LiteralUtf8 l

/-- The bytes of a triple's IRIs and lexical form are UTF-8. -/
def TripleUtf8 (t : rdf.Triple) : Prop :=
  SubjectUtf8 t.subject ∧ Utf8 t.predicate.spelling.val ∧ ObjectUtf8 t.object

theorem put_literal_spec (output : alloc.vec.Vec U8) (literal : rdf.RdfLiteral) (limit : Usize)
    (valid : LiteralUtf8 literal) :
    ∃ r, rdf_write.put_literal output literal limit = .ok r ∧
      Fits limit.val (output.val ++ LiteralText literal) r := by
  obtain ⟨⟨word, lexicalValid⟩, kindValid⟩ := valid
  unfold rdf_write.put_literal
  obtain ⟨r1, run1, c1⟩ := put_spec output 34#u8 limit
  rcases r1 with v1 | e1
  · obtain ⟨h1, f1⟩ := fits_ok c1
    obtain ⟨r2, run2, c2⟩ := put_string_from_spec v1 literal.lexical 0#usize limit (by rw [h1]; exact f1) lexicalValid
    rcases r2 with v2 | e2
    · obtain ⟨h2, f2⟩ := fits_ok c2
      obtain ⟨r3, run3, c3⟩ := put_spec v2 34#u8 limit
      rcases r3 with v3 | e3
      · obtain ⟨h3, f3⟩ := fits_ok c3
        rw [h2, h1] at h3
        cases kind : literal.kind with
        | Datatype d =>
          rw [kind] at kindValid
          obtain ⟨r4, run4, c4⟩ := put_from_spec v3 (Array.to_slice (Array.make 2#usize [94#u8, 94#u8])) 0#usize
            limit (by rw [h3]; rw [h2, h1] at f3; simpa using f3)
          rw [Rowl.TurtleTokens.slice_array] at c4
          rcases r4 with v4 | e4
          · obtain ⟨h4, f4⟩ := fits_ok c4
            obtain ⟨r5, run5, c5⟩ := put_iri_spec v4 d limit kindValid
            refine ⟨r5, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2, run3, kind, run4, run5], ?_⟩
            rw [h4, h3] at c5
            simpa [LiteralText, KindText, kind] using c5
          · refine ⟨.Err e4, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2, run3, kind, run4], ?_⟩
            rw [h3] at c4
            simpa [LiteralText, KindText, kind] using fits_err c4 (IriToken d.spelling.val)
        | Language t =>
          obtain ⟨r4, run4, c4⟩ := put_spec v3 64#u8 limit
          rcases r4 with v4 | e4
          · obtain ⟨h4, f4⟩ := fits_ok c4
            obtain ⟨r5, run5, c5⟩ := put_span_spec v4 t 0#usize (alloc.vec.Vec.len t) limit (by rw [h4]; exact f4)
              (by simp)
            refine ⟨r5, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2, run3, kind, run4, run5], ?_⟩
            rw [h4, h3] at c5
            simpa [LiteralText, KindText, kind, Span] using c5
          · refine ⟨.Err e4, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2, run3, kind, run4], ?_⟩
            rw [h3] at c4
            simpa [LiteralText, KindText, kind] using fits_err c4 t.val
      · refine ⟨.Err e3, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2, run3], ?_⟩
        rw [h2, h1] at c3
        simpa [LiteralText, List.append_assoc] using fits_err c3
          (KindText literal.kind)
    · refine ⟨.Err e2, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2], ?_⟩
      rw [h1] at c2
      simpa [LiteralText, List.append_assoc] using fits_err c2
        (34#u8 :: KindText literal.kind)
  · refine ⟨.Err e1, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
    simpa [LiteralText] using fits_err c1
      (StringText literal.lexical.val 0 ++ 34#u8 :: KindText literal.kind)

theorem put_subject_spec (output : alloc.vec.Vec U8) (subject : rdf.Subject) (limit : Usize)
    (fits : output.val.length ≤ limit.val) (valid : SubjectUtf8 subject) :
    ∃ r, rdf_write.put_subject output subject limit = .ok r ∧
      Fits limit.val (output.val ++ SubjectText subject) r := by
  cases subject with
  | Iri v =>
    obtain ⟨r, run, correct⟩ := put_iri_spec output v limit valid
    exact ⟨r, by simp [rdf_write.put_subject, run], correct⟩
  | Blank b =>
    obtain ⟨r, run, correct⟩ := put_blank_spec output b limit fits
    exact ⟨r, by simp [rdf_write.put_subject, run], correct⟩

theorem put_object_spec (output : alloc.vec.Vec U8) (object : rdf.Object) (limit : Usize)
    (fits : output.val.length ≤ limit.val) (valid : ObjectUtf8 object) :
    ∃ r, rdf_write.put_object output object limit = .ok r ∧
      Fits limit.val (output.val ++ ObjectText object) r := by
  cases object with
  | Iri v =>
    obtain ⟨r, run, correct⟩ := put_iri_spec output v limit valid
    exact ⟨r, by simp [rdf_write.put_object, run], correct⟩
  | Blank b =>
    obtain ⟨r, run, correct⟩ := put_blank_spec output b limit fits
    exact ⟨r, by simp [rdf_write.put_object, run], correct⟩
  | Literal l =>
    obtain ⟨r, run, correct⟩ := put_literal_spec output l limit valid
    exact ⟨r, by simp [rdf_write.put_object, run], correct⟩

theorem put_triple_spec (output : alloc.vec.Vec U8) (t : rdf.Triple) (limit : Usize)
    (fits : output.val.length ≤ limit.val) (valid : TripleUtf8 t) :
    ∃ r, rdf_write.put_triple output t limit = .ok r ∧ Fits limit.val (output.val ++ TripleText t) r := by
  obtain ⟨subjectValid, predicateValid, objectValid⟩ := valid
  unfold rdf_write.put_triple
  obtain ⟨r1, run1, c1⟩ := put_subject_spec output t.subject limit fits subjectValid
  rcases r1 with v1 | e1
  · obtain ⟨h1, f1⟩ := fits_ok c1
    obtain ⟨r2, run2, c2⟩ := put_spec v1 32#u8 limit
    rcases r2 with v2 | e2
    · obtain ⟨h2, f2⟩ := fits_ok c2
      obtain ⟨r3, run3, c3⟩ := put_iri_spec v2 t.predicate limit predicateValid
      rcases r3 with v3 | e3
      · obtain ⟨h3, f3⟩ := fits_ok c3
        obtain ⟨r4, run4, c4⟩ := put_spec v3 32#u8 limit
        rcases r4 with v4 | e4
        · obtain ⟨h4, f4⟩ := fits_ok c4
          obtain ⟨r5, run5, c5⟩ := put_object_spec v4 t.object limit (by rw [h4]; exact f4) objectValid
          refine ⟨r5, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2, run3, run4, run5], ?_⟩
          rw [h4, h3, h2, h1] at c5
          simpa [TripleText] using c5
        · refine ⟨.Err e4, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2, run3, run4], ?_⟩
          rw [h3, h2, h1] at c4
          simpa [TripleText] using fits_err c4 (ObjectText t.object)
      · refine ⟨.Err e3, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2, run3], ?_⟩
        rw [h2, h1] at c3
        simpa [TripleText] using fits_err c3 (32#u8 :: ObjectText t.object)
    · refine ⟨.Err e2, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch, run2], ?_⟩
      rw [h1] at c2
      simpa [TripleText] using fits_err c2 (IriToken t.predicate.spelling.val ++ 32#u8 :: ObjectText t.object)
  · refine ⟨.Err e1, by simp [run1, core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
    simpa [TripleText] using fits_err c1 (32#u8 :: (IriToken t.predicate.spelling.val ++ 32#u8 :: ObjectText t.object))

theorem lines_text_drop (ts : List rdf.Triple) (i : Nat) (inside : i < ts.length) :
    LinesText (ts.drop i) = LineText ts[i] ++ LinesText (ts.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons inside, LinesText]

theorem put_lines_spec (output : alloc.vec.Vec U8) (triples : alloc.vec.Vec rdf.Triple) (index limit : Usize)
    (fits : output.val.length ≤ limit.val) (valid : ∀ t ∈ triples.val, TripleUtf8 t) :
    ∃ r, rdf_write.put_lines output triples index limit = .ok r ∧
      Fits limit.val (output.val ++ LinesText (triples.val.drop index.val)) r := by
  rw [rdf_write.put_lines]
  by_cases more : index.val < triples.val.length
  · have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice rdf.Triple) triples index =
        .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
      (by have := triples.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r1, run1, c1⟩ := put_triple_spec output triples.val[index.val] limit fits
      (valid _ (List.getElem_mem more))
    rcases r1 with v1 | e1
    · obtain ⟨h1, f1⟩ := fits_ok c1
      obtain ⟨r2, run2, c2⟩ := put_from_spec v1 (Array.to_slice (Array.make 3#usize [32#u8, 46#u8, 10#u8]))
        0#usize limit (by rw [h1]; exact f1)
      rw [Rowl.TurtleTokens.slice_array] at c2
      rcases r2 with v2 | e2
      · obtain ⟨h2, f2⟩ := fits_ok c2
        obtain ⟨r3, run3, c3⟩ := put_lines_spec v2 triples next limit (by rw [h2]; simpa using f2) valid
        refine ⟨r3, by simp [alloc.vec.Vec.len_val, more, lookup, run1, core.result.Result.Insts.CoreOpsTry.branch,
          run2, add, run3], ?_⟩
        rw [h2, h1, nextIs] at c3
        rw [lines_text_drop _ _ more]
        simpa [LineText] using c3
      · refine ⟨.Err e2, by simp [alloc.vec.Vec.len_val, more, lookup, run1,
          core.result.Result.Insts.CoreOpsTry.branch, run2], ?_⟩
        rw [h1] at c2
        rw [lines_text_drop _ _ more]
        simpa [LineText] using fits_err c2 (LinesText (triples.val.drop (index.val + 1)))
    · refine ⟨.Err e1, by simp [alloc.vec.Vec.len_val, more, lookup, run1,
        core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
      rw [lines_text_drop _ _ more]
      simpa [LineText] using fits_err c1 ([32#u8, 46#u8, 10#u8] ++ LinesText (triples.val.drop (index.val + 1)))
  · have empty : triples.val.drop index.val = [] := List.drop_eq_nil_of_le (by omega)
    exact ⟨.Ok output, by simp [alloc.vec.Vec.len_val, more], by simp [empty, LinesText],
      by simp [empty, LinesText]; exact fits⟩
termination_by triples.val.length - index.val
decreasing_by omega


/-! ## Finding the first fault -/

theorem equal_from_spec (a : alloc.vec.Vec U8) (b : Slice U8) (index : Usize) (same : a.val.length = b.val.length) :
    rdf_write.equal_from a b index = .ok (decide (a.val.drop index.val = b.val.drop index.val)) := by
  rw [rdf_write.equal_from]
  by_cases more : index.val < a.val.length
  · have lookupA : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) a index = .ok a.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have moreB : index.val < b.val.length := by omega
    have lookupB : Slice.index_usize b index = .ok b.val[index.val] := by
      simp [Slice.index_usize, List.getElem?_eq_getElem moreB]
    have splitA := List.drop_eq_getElem_cons more
    have splitB := List.drop_eq_getElem_cons moreB
    have lt : index < alloc.vec.Vec.len a := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]
      exact more
    rw [if_pos lt, lookupA, bind_ok, lookupB, bind_ok]
    split
    · rename_i eq
      obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by have := a.property; scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      rw [add, bind_ok, equal_from_spec a b next same]
      congr 1
      apply decide_eq_decide.mpr
      rw [splitA, splitB, List.cons.injEq, nextIs]
      exact ⟨fun h => ⟨eq, h⟩, fun h => h.2⟩
    · rename_i eq
      congr 1
      symm
      apply decide_eq_false
      rw [splitA, splitB, List.cons.injEq]
      exact fun h => eq h.1
  · have emptyA : a.val.drop index.val = [] := List.drop_eq_nil_of_le (by omega)
    have emptyB : b.val.drop index.val = [] := List.drop_eq_nil_of_le (by omega)
    simp [alloc.vec.Vec.len_val, more, emptyA, emptyB]
termination_by a.val.length - index.val
decreasing_by omega

theorem equal_spec (a : alloc.vec.Vec U8) (b : Slice U8) :
    rdf_write.equal a b = .ok (decide (a.val = b.val)) := by
  unfold rdf_write.equal
  by_cases same : a.val.length = b.val.length
  · simp [alloc.vec.Vec.len_val, Slice.len_val, same, equal_from_spec a b 0#usize same]
  · have : a.val ≠ b.val := fun h => same (by rw [h])
    simp [alloc.vec.Vec.len_val, Slice.len_val, same, this]

theorem absolute_spec (spelling : alloc.vec.Vec U8) :
    rdf_write.absolute spelling = .ok (decide (AbsoluteIri spelling.val)) := by
  unfold rdf_write.absolute
  have iff := Rowl.Iri.validate_iri_accepted_iff spelling
  obtain ⟨r, run, _⟩ := Rowl.Iri.validate_iri_total_correct spelling
  rcases r with accepted | error
  · cases accepted with
    | true =>
      have valid : AbsoluteIri spelling.val := iff.mp run
      simp [run, valid]
    | false =>
      have invalid : ¬ AbsoluteIri spelling.val := fun h => by
        have := iff.mpr h
        rw [run] at this
        simp at this
      simp [run, invalid]
  · have invalid : ¬ AbsoluteIri spelling.val := fun h => by
      have := iff.mpr h
      rw [run] at this
      simp at this
    simp [run, invalid]

theorem resolution_keeps_spec (spelling : alloc.vec.Vec U8) :
    rdf_write.resolution_keeps spelling = .ok (decide (Resolves [] spelling.val spelling.val)) := by
  unfold rdf_write.resolution_keeps
  obtain ⟨r, run, value⟩ := Rowl.References.resolve_total_correct (alloc.vec.Vec.new U8) spelling
  have zero : (alloc.vec.Vec.new U8).val = [] := by simp
  rw [zero] at value
  rcases r with _ | target
  · have none : ¬ Resolves [] spelling.val spelling.val := by
      rintro ⟨small, short, resolves⟩
      rw [if_pos ⟨small, short⟩] at value
      rw [resolves] at value
      simp at value
    simp [run, none]
  · simp only [Option.map_some] at value
    split_ifs at value with small
    · simp only [run, bind_ok, equal_spec, alloc.vec.Vec.deref, Slice.from_val]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · intro same
        refine ⟨small.1, small.2, ?_⟩
        rw [← value, same]
      · rintro ⟨-, -, resolves⟩
        rw [resolves] at value
        exact Rowl.TurtleTokens.word_injective (Option.some.inj value)

theorem iri_fault_spec (iri : rdf.RdfIri) (resolved : Bool) :
    rdf_write.iri_fault iri resolved = .ok (IriFault resolved iri.spelling.val) := by
  unfold rdf_write.iri_fault IriFault
  by_cases valid : AbsoluteIri iri.spelling.val
  · cases resolved with
    | false => simp [absolute_spec, valid]
    | true =>
      by_cases keeps : Resolves [] iri.spelling.val iri.spelling.val
      · simp [absolute_spec, valid, resolution_keeps_spec, keeps]
      · simp [absolute_spec, valid, resolution_keeps_spec, keeps]
  · simp [absolute_spec, valid]

theorem utf8_from_spec (bytes : alloc.vec.Vec U8) (index : Usize) :
    rdf_write.utf8_from bytes index = .ok (decide (∃ word, Rowl.Regular.Utf8From bytes.val index.val word)) := by
  rw [rdf_write.utf8_from]
  obtain ⟨r, run, correct⟩ := Rowl.Unicode.decode_next_total_correct bytes index
  rcases r with _ | ⟨cp, next⟩ | error
  · have atEnd : index.val = bytes.val.length := correct
    have valid : ∃ word, Rowl.Regular.Utf8From bytes.val index.val word := ⟨[], by rw [atEnd]; exact .endOfInput⟩
    simp [run, valid]
  · obtain ⟨advanced, bounded, found⟩ := correct
    have rest := utf8_from_spec bytes next
    have same : (∃ word, Rowl.Regular.Utf8From bytes.val index.val word) ↔
        ∃ word, Rowl.Regular.Utf8From bytes.val next.val word := by
      constructor
      · rintro ⟨word, valid⟩
        obtain ⟨cp', w, tail, found', tailValid⟩ := utf8_from_step valid (by omega)
        rw [found] at found'
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj found')
        exact ⟨tail, by rwa [show index.val + (next.val - index.val) = next.val by omega] at tailValid⟩
      · rintro ⟨word, valid⟩
        exact ⟨cp.val :: word, .character found (by omega) (by omega)
          (by rwa [show index.val + (next.val - index.val) = next.val by omega])⟩
    simp only [run, bind_ok, rest]
    exact congrArg _ (decide_eq_decide.mpr same.symm)
  · cases error with
    | InvalidPosition position =>
      obtain ⟨-, over⟩ := correct
      have invalid : ¬ ∃ word, Rowl.Regular.Utf8From bytes.val index.val word := by
        rintro ⟨word, valid⟩
        have := utf8_from_le valid
        omega
      simp [run, invalid]
    | InvalidUtf8 position =>
      obtain ⟨-, inside, none⟩ := correct
      have invalid : ¬ ∃ word, Rowl.Regular.Utf8From bytes.val index.val word := by
        rintro ⟨word, valid⟩
        obtain ⟨cp', w, tail, found', _⟩ := utf8_from_step valid inside
        rw [none] at found'
        exact absurd found' (by simp)
      simp [run, invalid]
    | NonXmlCharacter a b => exact absurd correct (by simp [Rowl.Unicode.StepCorrect])
termination_by bytes.val.length - index.val
decreasing_by omega


/-! ## Language tags -/

/-- The bytes `tag_class` accepts: letters, or letters and digits. -/
noncomputable def TagClass (letters : Bool) (b : U8) : Bool := if letters then decide (LetterByte b) else decide (AlnumByte b)

theorem ascii_letter_spec (b : U8) : rdf_write.ascii_letter b = .ok (decide (LetterByte b)) := by
  unfold rdf_write.ascii_letter LetterByte
  have h65 : (65#u8 ≤ b) ↔ 65 ≤ b.val := by simp [UScalar.le_equiv]
  have h90 : (b ≤ 90#u8) ↔ b.val ≤ 90 := by simp [UScalar.le_equiv]
  have h97 : (97#u8 ≤ b) ↔ 97 ≤ b.val := by simp [UScalar.le_equiv]
  have h122 : (b ≤ 122#u8) ↔ b.val ≤ 122 := by simp [UScalar.le_equiv]
  by_cases a : 65 ≤ b.val <;> by_cases c : b.val ≤ 90 <;> by_cases d : 97 ≤ b.val <;> by_cases e : b.val ≤ 122 <;>
    simp [h65, h90, h97, h122, a, c, d, e]

theorem ascii_alphanumeric_spec (b : U8) : rdf_write.ascii_alphanumeric b = .ok (decide (AlnumByte b)) := by
  unfold rdf_write.ascii_alphanumeric AlnumByte
  have h48 : (48#u8 ≤ b) ↔ 48 ≤ b.val := by simp [UScalar.le_equiv]
  have h57 : (b ≤ 57#u8) ↔ b.val ≤ 57 := by simp [UScalar.le_equiv]
  rw [ascii_letter_spec, bind_ok]
  by_cases a : LetterByte b
  · simp [a]
  · by_cases c : 48 ≤ b.val <;> by_cases d : b.val ≤ 57 <;> simp [h48, h57, a, c, d]

theorem tag_class_spec (b : U8) (letters : Bool) : rdf_write.tag_class b letters = .ok (TagClass letters b) := by
  cases letters <;> simp [rdf_write.tag_class, TagClass, ascii_letter_spec, ascii_alphanumeric_spec]

theorem word_end_spec (bytes : alloc.vec.Vec U8) (index : Usize) (letters : Bool)
    (inside : index.val ≤ bytes.val.length) :
    ∃ u : Usize, rdf_write.word_end bytes index letters = .ok u ∧
      u.val = index.val + ((bytes.val.drop index.val).takeWhile (TagClass letters)).length := by
  rw [rdf_write.word_end]
  by_cases more : index.val < bytes.val.length
  · have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) bytes index =
        .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    by_cases accepted : TagClass letters bytes.val[index.val] = true
    · obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by have := bytes.property; scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨u, run, value⟩ := word_end_spec bytes next letters (by omega)
      refine ⟨u, ?_, ?_⟩
      · simp [rdf_write.tag_byte_at, alloc.vec.Vec.len_val, more, lookup, tag_class_spec, accepted, add, run]
      · rw [value, nextIs, split, List.takeWhile_cons_of_pos accepted]
        simp
        omega
    · refine ⟨index, ?_, ?_⟩
      · simp [rdf_write.tag_byte_at, alloc.vec.Vec.len_val, more, lookup, tag_class_spec, accepted]
      · rw [split, List.takeWhile_cons_of_neg accepted]
        simp
  · refine ⟨index, by simp [rdf_write.tag_byte_at, alloc.vec.Vec.len_val, more], ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by bytes.val.length - index.val
decreasing_by omega

theorem take_while_all {p : U8 → Bool} {w rest : List U8} (all : ∀ b ∈ w, p b = true) (stop : rest.takeWhile p = []) :
    (w ++ rest).takeWhile p = w ∧ (w ++ rest).dropWhile p = rest := by
  induction w with
  | nil => exact ⟨stop, by
      cases rest with
      | nil => rfl
      | cons b tail =>
        have : p b = false := by
          by_contra h
          simp [List.takeWhile_cons, h] at stop
        simp [List.dropWhile_cons, this]⟩
  | cons b tail ih =>
    have pb := all b (by simp)
    obtain ⟨h1, h2⟩ := ih (fun c hc => all c (by simp [hc]))
    exact ⟨by simp [List.takeWhile_cons, pb, h1], by simp [List.dropWhile_cons, pb, h2]⟩

theorem take_while_true {α : Type} {p : α → Bool} {l : List α} {b : α} (h : b ∈ l.takeWhile p) : p b = true :=
  List.all_eq_true.mp List.all_takeWhile b h

theorem drop_while_eq {α : Type} (p : α → Bool) (l : List α) : l.dropWhile p = l.drop (l.takeWhile p).length := by
  have whole := List.takeWhile_append_dropWhile (p := p) (l := l)
  calc l.dropWhile p = (l.takeWhile p ++ l.dropWhile p).drop (l.takeWhile p).length := (List.drop_left' rfl).symm
    _ = l.drop (l.takeWhile p).length := by rw [whole]

theorem subtags_start {l : List U8} (h : Subtags l) : l.takeWhile (TagClass false) = [] := by
  cases h with
  | nil => rfl
  | cons _ _ _ => simp [List.takeWhile_cons, TagClass, AlnumByte, LetterByte]

theorem subtags_start_letters {l : List U8} (h : Subtags l) : l.takeWhile (TagClass true) = [] := by
  cases h with
  | nil => rfl
  | cons _ _ _ => simp [List.takeWhile_cons, TagClass, LetterByte]

theorem subtags_cons_iff (x : List U8) :
    Subtags (45#u8 :: x) ↔ x.takeWhile (TagClass false) ≠ [] ∧ Subtags (x.dropWhile (TagClass false)) := by
  constructor
  · intro h
    generalize hl : (45#u8 :: x) = l at h
    cases h with
    | nil => cases hl
    | @cons w rest nonempty alnum tail =>
      simp only [List.cons.injEq, true_and] at hl
      subst hl
      have all : ∀ b ∈ w, TagClass false b = true := fun b hb => by simp [TagClass, alnum b hb]
      obtain ⟨h1, h2⟩ := take_while_all all (subtags_start tail)
      exact ⟨by rw [h1]; exact nonempty, by rw [h2]; exact tail⟩
  · rintro ⟨nonempty, tail⟩
    have whole := List.takeWhile_append_dropWhile (p := TagClass false) (l := x)
    rw [← whole]
    exact .cons nonempty (fun b hb => by
      have := take_while_true hb
      simpa [TagClass] using this) tail

theorem subtags_from_spec (bytes : alloc.vec.Vec U8) (index : Usize) :
    rdf_write.subtags_from bytes index = .ok (decide (Subtags (bytes.val.drop index.val))) := by
  rw [rdf_write.subtags_from]
  by_cases atEnd : bytes.val.length ≤ index.val
  · rw [List.drop_eq_nil_of_le atEnd]
    simp [alloc.vec.Vec.len_val, atEnd, Subtags.nil]
  · have more : index.val < bytes.val.length := by omega
    have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) bytes index =
        .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    by_cases dash : bytes.val[index.val] = 45#u8
    · obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by have := bytes.property; scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨u, run, value⟩ := word_end_spec bytes next false (by omega)
      have rest : bytes.val.drop index.val = 45#u8 :: bytes.val.drop next.val := by rw [split, dash, nextIs]
      have dropped : (bytes.val.drop next.val).dropWhile (TagClass false) = bytes.val.drop u.val := by
        rw [drop_while_eq, List.drop_drop]
        congr 1
        omega
      by_cases empty : u = next
      · have none : (bytes.val.drop next.val).takeWhile (TagClass false) = [] := by
          rw [empty] at value
          exact List.eq_nil_of_length_eq_zero (by omega)
        simp [alloc.vec.Vec.len_val, atEnd, lookup, dash, add, run, empty, rest, subtags_cons_iff, none]
      · have uValue : u.val ≠ next.val := fun h => empty (UScalar.eq_of_val_eq h)
        have some : (bytes.val.drop next.val).takeWhile (TagClass false) ≠ [] := by
          intro h
          rw [h] at value
          simp at value
          exact uValue value
        have later := subtags_from_spec bytes u
        simp [alloc.vec.Vec.len_val, atEnd, lookup, dash, add, run, empty, later, rest, subtags_cons_iff, some,
          dropped]
    · have notSubtags : ¬ Subtags (bytes.val.drop index.val) := by
        rw [split]
        intro h
        generalize hl : bytes.val[index.val] :: bytes.val.drop (index.val + 1) = l at h
        cases h with
        | nil => cases hl
        | cons _ _ _ =>
          simp only [List.cons.injEq] at hl
          exact dash hl.1
      have dashVal : ¬ (bytes.val[index.val]).val = 45 := fun h => dash (UScalar.eq_of_val_eq (h.trans rfl))
      simp [alloc.vec.Vec.len_val, atEnd, lookup, dash, dashVal, notSubtags]
termination_by bytes.val.length - index.val
decreasing_by
  have := (List.takeWhile_prefix (TagClass false) (l := bytes.val.drop next.val)).length_le
  rw [List.length_drop] at this
  have : u.val ≠ next.val := uValue
  omega

theorem tag_form_iff (t : List U8) :
    TagForm t ↔ t.takeWhile (TagClass true) ≠ [] ∧ Subtags (t.dropWhile (TagClass true)) := by
  constructor
  · rintro ⟨head, rest, rfl, nonempty, letters, tail⟩
    have all : ∀ b ∈ head, TagClass true b = true := fun b hb => by simp [TagClass, letters b hb]
    obtain ⟨h1, h2⟩ := take_while_all all (subtags_start_letters tail)
    exact ⟨by rw [h1]; exact nonempty, by rw [h2]; exact tail⟩
  · rintro ⟨nonempty, tail⟩
    refine ⟨_, _, (List.takeWhile_append_dropWhile (p := TagClass true) (l := t)).symm, nonempty, fun b hb => ?_, tail⟩
    have := take_while_true hb
    simpa [TagClass] using this

theorem tag_form_spec (tag : alloc.vec.Vec U8) : rdf_write.tag_form tag = .ok (decide (TagForm tag.val)) := by
  unfold rdf_write.tag_form
  obtain ⟨head, run, value⟩ := word_end_spec tag 0#usize true (by simp)
  have zero : (0#usize : Usize).val = 0 := rfl
  simp only [zero, List.drop_zero, Nat.zero_add] at value
  rw [tag_form_iff]
  have dropped : tag.val.dropWhile (TagClass true) = tag.val.drop head.val := by
    rw [drop_while_eq, value]
  by_cases empty : head = 0#usize
  · have none : tag.val.takeWhile (TagClass true) = [] := by
      rw [empty] at value
      exact List.eq_nil_of_length_eq_zero (by simpa using value.symm)
    simp [run, empty, none]
  · have some : tag.val.takeWhile (TagClass true) ≠ [] := by
      intro h
      rw [h] at value
      exact empty (UScalar.eq_of_val_eq (by simpa using value))
    simp [run, empty, some, subtags_from_spec tag head, dropped]

theorem well_formed_spec (tag : alloc.vec.Vec U8) : langtag.well_formed tag = .ok (decide (LanguageTag tag.val)) := by
  obtain ⟨accepted, run⟩ := Rowl.LangTag.well_formed_total_correct tag
  have iff := Rowl.LangTag.well_formed_accepted_iff tag
  cases accepted with
  | true => rw [run]; simp [LanguageTag, iff.mp run]
  | false =>
    have invalid : ¬ LanguageTag tag.val := fun h => by
      have := iff.mpr h
      rw [run] at this
      simp at this
    rw [run]
    simp [invalid]

theorem tag_fault_spec (tag : alloc.vec.Vec U8) :
    rdf_write.tag_fault tag = .ok (if TagForm tag.val ∧ LanguageTag tag.val then none
      else some .InvalidLanguageTag) := by
  unfold rdf_write.tag_fault
  by_cases form : TagForm tag.val
  · by_cases valid : LanguageTag tag.val
    · simp [tag_form_spec, form, well_formed_spec, valid]
    · simp [tag_form_spec, form, well_formed_spec, valid]
  · simp [tag_form_spec, form]

/-! ## The first fault of a graph -/

theorem datatype_fault_spec (iri : rdf.RdfIri) (resolved : Bool) :
    rdf_write.datatype_fault iri resolved = .ok (if iri.spelling.val = LangStringBytes then some .InvalidLiteralKind
      else IriFault resolved iri.spelling.val) := by
  unfold rdf_write.datatype_fault
  by_cases lang : iri.spelling.val = LangStringBytes
  · simp [equal_spec, Rowl.TurtleTokens.slice_array, lang, LangStringBytes]
  · have lang' : ¬ iri.spelling.val = [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8,
        119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8,
        49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8,
        45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8,
        97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 108#u8, 97#u8, 110#u8,
        103#u8, 83#u8, 116#u8, 114#u8, 105#u8, 110#u8, 103#u8] := lang
    simp [equal_spec, Rowl.TurtleTokens.slice_array, lang, lang', iri_fault_spec]

theorem literal_fault_spec (literal : rdf.RdfLiteral) (resolved : Bool) :
    rdf_write.literal_fault literal resolved = .ok (LiteralFault resolved literal) := by
  unfold rdf_write.literal_fault LiteralFault
  by_cases valid : Utf8 literal.lexical.val
  · have run : rdf_write.utf8_from literal.lexical 0#usize = .ok true := by
      rw [utf8_from_spec]
      simpa [Utf8] using valid
    cases kind : literal.kind with
    | Datatype d => simp [run, valid, kind, datatype_fault_spec]
    | Language t => simp [run, valid, kind, tag_fault_spec]
  · have run : rdf_write.utf8_from literal.lexical 0#usize = .ok false := by
      rw [utf8_from_spec]
      simpa [Utf8] using valid
    simp [run, valid]

theorem subject_fault_spec (subject : rdf.Subject) (resolved : Bool) :
    rdf_write.subject_fault subject resolved = .ok (SubjectFault resolved subject) := by
  cases subject <;> simp [rdf_write.subject_fault, SubjectFault, iri_fault_spec]

theorem object_fault_spec (object : rdf.Object) (resolved : Bool) :
    rdf_write.object_fault object resolved = .ok (ObjectFault resolved object) := by
  cases object <;> simp [rdf_write.object_fault, ObjectFault, iri_fault_spec, literal_fault_spec]

theorem triple_fault_spec (t : rdf.Triple) (resolved : Bool) :
    rdf_write.triple_fault t resolved = .ok (TripleFault resolved t) := by
  unfold rdf_write.triple_fault TripleFault
  cases hs : SubjectFault resolved t.subject with
  | some e => simp [subject_fault_spec, hs]
  | none =>
    cases hp : IriFault resolved t.predicate.spelling.val with
    | some e => simp [subject_fault_spec, hs, iri_fault_spec, hp]
    | none => simp [subject_fault_spec, hs, iri_fault_spec, hp, object_fault_spec]

theorem graph_fault_spec (triples : alloc.vec.Vec rdf.Triple) (index : Usize) (resolved : Bool) :
    rdf_write.graph_fault triples index resolved = .ok (GraphFault resolved (triples.val.drop index.val)) := by
  rw [rdf_write.graph_fault]
  by_cases more : index.val < triples.val.length
  · have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice rdf.Triple) triples index =
        .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    have lt : index < alloc.vec.Vec.len triples := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]
      exact more
    rw [if_pos lt, lookup, bind_ok, triple_fault_spec, bind_ok, split]
    simp only [GraphFault]
    cases ht : TripleFault resolved triples.val[index.val] with
    | some e => rfl
    | none =>
      obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by have := triples.property; scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      have rest := graph_fault_spec triples next resolved
      rw [nextIs] at rest
      simp only [add, bind_ok, rest, Option.none_or]
  · have ge : ¬ index < alloc.vec.Vec.len triples := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]
      exact more
    rw [if_neg ge, List.drop_eq_nil_of_le (by omega)]
    rfl
termination_by triples.val.length - index.val
decreasing_by omega

theorem iri_fault_none {resolved : Bool} {s : List U8} (h : IriFault resolved s = none) :
    AbsoluteIri s ∧ (resolved = true → Resolves [] s s) := by
  unfold IriFault at h
  split_ifs at h with a b
  exact ⟨by simpa using a, fun r => by
    by_contra keeps
    exact b ⟨r, keeps⟩⟩

theorem absolute_utf8 {s : List U8} (h : AbsoluteIri s) : Utf8 s := by
  obtain ⟨word, valid, _⟩ := h
  exact ⟨word, valid⟩

theorem triple_fault_utf8 {resolved : Bool} {t : rdf.Triple} (h : TripleFault resolved t = none) : TripleUtf8 t := by
  unfold TripleFault at h
  simp only [Option.or_eq_none_iff] at h
  obtain ⟨hs, hp, ho⟩ := h
  refine ⟨?_, absolute_utf8 (iri_fault_none hp).1, ?_⟩
  · cases hsub : t.subject with
    | Iri v =>
      rw [hsub] at hs
      exact absolute_utf8 (iri_fault_none hs).1
    | Blank b => trivial
  · cases hobj : t.object with
    | Iri v =>
      rw [hobj] at ho
      exact absolute_utf8 (iri_fault_none ho).1
    | Blank b => trivial
    | Literal l =>
      rw [hobj] at ho
      simp only [ObjectFault, LiteralFault] at ho
      split_ifs at ho with valid
      refine ⟨by simpa using valid, ?_⟩
      cases kind : l.kind with
      | Datatype d =>
        rw [kind] at ho
        simp only at ho
        split_ifs at ho
        exact absolute_utf8 (iri_fault_none ho).1
      | Language t => trivial

theorem graph_fault_triples {resolved : Bool} : ∀ {ts : List rdf.Triple}, GraphFault resolved ts = none →
    ∀ t ∈ ts, TripleFault resolved t = none
  | [], _, t, member => by simp at member
  | u :: rest, h, t, member => by
    simp only [GraphFault, Option.or_eq_none_iff] at h
    rcases List.mem_cons.mp member with rfl | later
    · exact h.1
    · exact graph_fault_triples h.2 t later

/-- `rdf_write::write_graph` writes exactly the lines of a graph without
    faults within the budget, and otherwise reports its first fault or the
    exhausted budget. -/
theorem write_graph_total_correct (graph : rdf.RawGraph) (resolved : Bool) (limit : Usize) :
    ∃ r, rdf_write.write_graph graph resolved limit = .ok r ∧ WriteCorrect resolved graph.triples.val limit.val r := by
  unfold rdf_write.write_graph
  have faults := graph_fault_spec graph.triples 0#usize resolved
  have zero : (0#usize : Usize).val = 0 := rfl
  simp only [zero, List.drop_zero] at faults
  cases fault : GraphFault resolved graph.triples.val with
  | some e => exact ⟨.Error e, by simp [faults, fault], Or.inl fault⟩
  | none =>
    have valid := fun t member => triple_fault_utf8 (graph_fault_triples fault t member)
    obtain ⟨r, run, correct⟩ := put_lines_spec (alloc.vec.Vec.new U8) graph.triples 0#usize limit (by simp) valid
    simp only [zero, List.drop_zero] at correct
    rcases r with bytes | e
    · obtain ⟨contents, fits⟩ := fits_ok correct
      refine ⟨.Bytes bytes, by simp [faults, fault, run], fault, by simpa using contents, by simpa [contents] using fits⟩
    · obtain ⟨rfl, over⟩ := correct
      exact ⟨.Error .ResourceLimit, by simp [faults, fault, run], Or.inr ⟨fault, rfl, by simpa using over⟩⟩

/-- `ntriples::write` writes exactly the N-Triples lines of a graph whose terms
    N-Triples can carry within the budget, and otherwise returns the first term
    it cannot carry or the exhausted budget. -/
theorem ntriples_write_total_correct (graph : rdf.RawGraph) (limit : Usize) :
    ∃ r, ntriples.write graph limit = .ok r ∧ WriteCorrect false graph.triples.val limit.val r := by
  unfold ntriples.write
  exact write_graph_total_correct graph false limit

/-- `turtle::write` writes the same lines, which are Turtle, for the graphs whose
    IRIs RFC 3986 resolution also leaves, and otherwise returns the first term
    it cannot carry or the exhausted budget. -/
theorem turtle_write_total_correct (graph : rdf.RawGraph) (limit : Usize) :
    ∃ r, turtle.write graph limit = .ok r ∧ WriteCorrect true graph.triples.val limit.val r := by
  unfold turtle.write
  exact write_graph_total_correct graph true limit

end Rowl.RdfWrite
