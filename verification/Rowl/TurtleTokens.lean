import Rowl.NTriples
import Rowl.References
import Rowl.LangTag

/-!
The tokens of RDF 1.1 Turtle (W3C Recommendation, 25 February 2014, section
6.5), as relations over the byte positions of a document, written independently
of the Rust reader. Characters are the strictly decoded UTF-8 units of
`Rowl.Unicode`. Every token reader of `turtle.rs` is proved total and exact:
its result is described by the relation of its token, an error by the
relation's failure with its kind and byte offset (`*_total_correct`), and every
token the relation describes is read with exactly its value (`*_accepted`).

The relations follow the longest-match rule of section 6.5. A name (PN_PREFIX,
BLANK_NODE_LABEL, PN_LOCAL) runs as far as its characters go and ends after its
last character that is not a dot. A long string begins with three quotes only
when a whole long string follows; otherwise the token is the empty string of two
quotes (`LongString.empty`). A LANGTAG ends before a `-` that no letter or digit
follows. IRIREF, STRING_LITERAL_QUOTE, ECHAR, UCHAR, white space and comments
are the N-Triples productions of `NTriples.lean`. An IRI reference must be an
RFC 3987 IRI reference; it is resolved against the base by RFC 3986 section 5.2
(`IriResolution.resolve`), and the IRI of every IRI reference and prefixed name
must be an RFC 3987 IRI. A language tag must be a well-formed BCP 47 tag.
-/
namespace Rowl.TurtleTokens
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open Rowl.NTriples (UnitAt MalformedAt TriviaRuns TriviaFails PnBase AsciiDigit HexValue
  QuotedToken QuotedError QuotedItem ItemError EscapeValue EscapeError HexDigits AbsoluteIri
  LanguageTag XsdStringBytes LangStringBytes RequiredError CopyCorrect)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-! ## Failures and terms -/

/-- A failure: the kind of the first error and its byte offset. -/
abbrev Fault := turtle.ErrorKind × Nat

/-- The Turtle kind of an N-Triples error kind: the kind of the same name, and
    a missing period for the line end that Turtle does not have. -/
def KindOf : ntriples.ErrorKind → turtle.ErrorKind
  | .MalformedUtf8 => .MalformedUtf8
  | .UnexpectedEnd => .UnexpectedEnd
  | .ExpectedIri => .ExpectedIri
  | .ExpectedSubject => .ExpectedSubject
  | .ExpectedObject => .ExpectedObject
  | .ExpectedPeriod => .ExpectedPeriod
  | .ExpectedLineEnd => .ExpectedPeriod
  | .InvalidCharacter => .InvalidCharacter
  | .InvalidEscape => .InvalidEscape
  | .InvalidIri => .InvalidIri
  | .InvalidBlankLabel => .InvalidBlankLabel
  | .InvalidLanguageTag => .InvalidLanguageTag
  | .InvalidLiteralKind => .InvalidLiteralKind
  | .ResourceLimit => .ResourceLimit

/-- The failure of an N-Triples token error. -/
def lifted (e : ntriples.ReadError) : Fault := (KindOf e.kind, e.offset.val)

/-- The failure a reader error reports. -/
def faultOf (e : turtle.ReadError) : Fault := (e.kind, e.offset.val)

/-- The kind of a literal: a datatype IRI or a language tag. -/
inductive Kind where
  | datatype (iri : List U8)
  | language (tag : List U8)

/-- RDF terms by their bytes: IRIs, blank nodes by scope and label, and literals
    by lexical form and kind. -/
inductive Term where
  | iri (spelling : List U8)
  | blank (scope label : List U8)
  | literal (lexical : List U8) (kind : Kind)

/-- The term of an RDF literal. -/
def literalTerm (l : rdf.RdfLiteral) : Term :=
  match l.kind with
  | .Datatype d => .literal l.lexical.val (.datatype d.spelling.val)
  | .Language t => .literal l.lexical.val (.language t.val)

/-- The term of a subject. -/
def subjectTerm : rdf.Subject → Term
  | .Iri v => .iri v.spelling.val
  | .Blank b => .blank b.scope.val b.label.val

/-- The term of an object. -/
def objectTerm : rdf.Object → Term
  | .Iri v => .iri v.spelling.val
  | .Blank b => .blank b.scope.val b.label.val
  | .Literal l => literalTerm l

/-! ## Bytes, characters and character classes -/

/-- The UTF-8 encoded character `c` occupies the bytes `p..q`. -/
def Unit (bs : List U8) (p c q : Nat) : Prop :=
  p < q ∧ q ≤ bs.length ∧ Rowl.Unicode.Prefix bs p = some (c, q - p)

/-- The byte at `i` is `v`. -/
def ByteIs (bs : List U8) (i v : Nat) : Prop := bs[i]?.map (·.val) = some v

/-- The bytes `p..q`. -/
def Span (bs : List U8) (p q : Nat) : List U8 := (bs.drop p).take (q - p)

/-- Reading the character at `p` fails: it is not a UTF-8 encoded character. -/
def Malformed (bs : List U8) (p : Nat) : Prop := MalformedAt bs p

/-- A character is needed at `p`, but the bytes end there or are malformed. -/
def MissingFault (bs : List U8) (p : Nat) (f : Fault) : Prop :=
  (Malformed bs p ∧ f = (.MalformedUtf8, p)) ∨ (p = bs.length ∧ f = (.UnexpectedEnd, p))

/-- White space and comments from `p` fail with `f`. -/
def TriviaFault (bs : List U8) (p : Nat) (f : Fault) : Prop :=
  ∃ e, TriviaFails bs true p e ∧ lifted e = f

/-- PN_CHARS_U of Turtle: PN_CHARS_BASE or `_` (without the `:` of N-Triples). -/
def PnCharsU (c : Nat) : Prop := PnBase c ∨ c = 95
/-- PN_CHARS. -/
def PnChars (c : Nat) : Prop :=
  PnCharsU c ∨ c = 45 ∨ AsciiDigit c ∨ c = 183 ∨ (768 ≤ c ∧ c ≤ 879) ∨ (8255 ≤ c ∧ c ≤ 8256)
/-- The first character of a blank node label: PN_CHARS_U or a digit. -/
def LabelFirst (c : Nat) : Prop := PnCharsU c ∨ AsciiDigit c
/-- The first character of PN_LOCAL other than PLX: PN_CHARS_U, `:` or a digit. -/
def LocalFirstChar (c : Nat) : Prop := PnCharsU c ∨ c = 58 ∨ AsciiDigit c
/-- A later character of PN_LOCAL other than PLX and `.`: PN_CHARS or `:`. -/
def LocalChar (c : Nat) : Prop := PnChars c ∨ c = 58
/-- The characters PN_LOCAL_ESC escapes: ``_~.-!$&'()*+,;=/?#@%``. -/
def LocalEscape (c : Nat) : Prop :=
  c ∈ [95, 126, 46, 45, 33, 36, 38, 39, 40, 41, 42, 43, 44, 59, 61, 47, 63, 35, 64, 37]
/-- `%` or `\`, which begin PLX. -/
def PlxStart (c : Nat) : Prop := c = 37 ∨ c = 92
/-- PN_CHARS_BASE or `:`, which begin a prefixed name and the keywords. -/
def WordStart (c : Nat) : Prop := PnBase c ∨ c = 58
/-- A digit, `+`, `-` or `.`, which begin a number. -/
def NumberStart (c : Nat) : Prop := AsciiDigit c ∨ c = 43 ∨ c = 45 ∨ c = 46
/-- `"` or `'`. -/
def QuoteChar (c : Nat) : Prop := c = 34 ∨ c = 39

/-- The term that a character at a node position begins. -/
noncomputable def StartOf (c : Nat) : turtle.Start :=
  if c = 60 then .Iri else if c = 95 then .Blank else if c = 91 then .Bracket
  else if c = 40 then .Paren else if QuoteChar c then .Quote else if NumberStart c then .Number
  else if WordStart c then .Word else .Other

/-! ## Names -/

/-- The rest of a name from `p`: `(PN_CHARS | '.')*` as far as it goes, ending
    after its last PN_CHARS; `a` is where the name ends so far. -/
inductive NameTail (bs : List U8) : Nat → Nat → Except Fault Nat → Prop
  | malformed {p a} : Malformed bs p → NameTail bs p a (.error (.MalformedUtf8, p))
  | finish {p a} : p = bs.length → NameTail bs p a (.ok a)
  | other {p a c q} : Unit bs p c q → ¬ PnChars c → c ≠ 46 → NameTail bs p a (.ok a)
  | char {p a c q r} : Unit bs p c q → PnChars c → NameTail bs q q r → NameTail bs p a r
  | dot {p a c q r} : Unit bs p c q → c = 46 → NameTail bs q a r → NameTail bs p a r

/-- PNAME_NS `PN_PREFIX? ':'` at `start`: the position of its colon, or none
    when no PNAME_NS begins there. -/
inductive PrefixColon (bs : List U8) (start : Nat) : Except Fault (Option Nat) → Prop
  | malformed : Malformed bs start → PrefixColon bs start (.error (.MalformedUtf8, start))
  | finish : start = bs.length → PrefixColon bs start (.ok none)
  | colon {q} : Unit bs start 58 q → PrefixColon bs start (.ok (some start))
  | other {c q} : Unit bs start c q → c ≠ 58 → ¬ PnBase c → PrefixColon bs start (.ok none)
  | nameFails {c q f} : Unit bs start c q → PnBase c → NameTail bs q q (.error f) →
      PrefixColon bs start (.error f)
  | named {c q e} : Unit bs start c q → PnBase c → NameTail bs q q (.ok e) → ByteIs bs e 58 →
      PrefixColon bs start (.ok (some e))
  | unnamed {c q e} : Unit bs start c q → PnBase c → NameTail bs q q (.ok e) → ¬ ByteIs bs e 58 →
      PrefixColon bs start (.ok none)

/-- A hex digit at `p`, and the position after it. -/
inductive HexAt (bs : List U8) (p : Nat) : Except Fault (Option Nat) → Prop
  | malformed : Malformed bs p → HexAt bs p (.error (.MalformedUtf8, p))
  | finish : p = bs.length → HexAt bs p (.ok none)
  | hex {c q} : Unit bs p c q → HexValue c ≠ none → HexAt bs p (.ok (some q))
  | other {c q} : Unit bs p c q → HexValue c = none → HexAt bs p (.ok none)

/-- PERCENT after its `%`: two hex digits from `q`. -/
inductive Percent (bs : List U8) (q : Nat) : Except Fault (Option Nat) → Prop
  | firstFails {f} : HexAt bs q (.error f) → Percent bs q (.error f)
  | none : HexAt bs q (.ok none) → Percent bs q (.ok none)
  | second {m r} : HexAt bs q (.ok (some m)) → HexAt bs m r → Percent bs q r

/-- PN_LOCAL_ESC after its `\`: an escapable character at `q`. -/
inductive LocalEscaped (bs : List U8) (q : Nat) : Except Fault (Option Nat) → Prop
  | malformed : Malformed bs q → LocalEscaped bs q (.error (.MalformedUtf8, q))
  | finish : q = bs.length → LocalEscaped bs q (.ok none)
  | escape {c n} : Unit bs q c n → LocalEscape c → LocalEscaped bs q (.ok (some n))
  | other {c n} : Unit bs q c n → ¬ LocalEscape c → LocalEscaped bs q (.ok none)

/-- PLX after its first character `c`, which ends at `q`. -/
def Plx (bs : List U8) (c q : Nat) (r : Except Fault (Option Nat)) : Prop :=
  if c = 37 then Percent bs q r else LocalEscaped bs q r

/-- The first unit of PN_LOCAL at `p`: a character or PLX, and its end. -/
inductive LocalFirst (bs : List U8) (p : Nat) : Except Fault (Option Nat) → Prop
  | malformed : Malformed bs p → LocalFirst bs p (.error (.MalformedUtf8, p))
  | finish : p = bs.length → LocalFirst bs p (.ok none)
  | plx {c q r} : Unit bs p c q → PlxStart c → Plx bs c q r → LocalFirst bs p r
  | char {c q} : Unit bs p c q → ¬ PlxStart c → LocalFirstChar c → LocalFirst bs p (.ok (some q))
  | other {c q} : Unit bs p c q → ¬ PlxStart c → ¬ LocalFirstChar c → LocalFirst bs p (.ok none)

/-- A later unit of PN_LOCAL: a part of the name, a dot, or none. -/
inductive LocalStep where
  | part (q : Nat)
  | dot (q : Nat)
  | stop

/-- The unit of PN_LOCAL at `p` after its first. -/
inductive LocalNext (bs : List U8) (p : Nat) : Except Fault LocalStep → Prop
  | malformed : Malformed bs p → LocalNext bs p (.error (.MalformedUtf8, p))
  | finish : p = bs.length → LocalNext bs p (.ok .stop)
  | plxFails {c q f} : Unit bs p c q → PlxStart c → Plx bs c q (.error f) → LocalNext bs p (.error f)
  | plxNone {c q} : Unit bs p c q → PlxStart c → Plx bs c q (.ok none) → LocalNext bs p (.ok .stop)
  | plx {c q n} : Unit bs p c q → PlxStart c → Plx bs c q (.ok (some n)) → LocalNext bs p (.ok (.part n))
  | char {c q} : Unit bs p c q → ¬ PlxStart c → LocalChar c → LocalNext bs p (.ok (.part q))
  | dot {c q} : Unit bs p c q → ¬ PlxStart c → ¬ LocalChar c → c = 46 → LocalNext bs p (.ok (.dot q))
  | other {c q} : Unit bs p c q → ¬ PlxStart c → ¬ LocalChar c → c ≠ 46 → LocalNext bs p (.ok .stop)

/-- The rest of PN_LOCAL from `p`, ending after its last unit that is not a
    dot; `a` is where the local name ends so far. -/
inductive LocalRest (bs : List U8) : Nat → Nat → Except Fault Nat → Prop
  | fails {p a f} : LocalNext bs p (.error f) → LocalRest bs p a (.error f)
  | stop {p a} : LocalNext bs p (.ok .stop) → LocalRest bs p a (.ok a)
  | part {p a q r} : LocalNext bs p (.ok (.part q)) → LocalRest bs q q r → LocalRest bs p a r
  | dot {p a q r} : LocalNext bs p (.ok (.dot q)) → LocalRest bs q a r → LocalRest bs p a r

/-- The end of the PN_LOCAL at `p`, or `p` when none begins there. -/
inductive LocalEnd (bs : List U8) (p : Nat) : Except Fault Nat → Prop
  | fails {f} : LocalFirst bs p (.error f) → LocalEnd bs p (.error f)
  | none : LocalFirst bs p (.ok none) → LocalEnd bs p (.ok p)
  | rest {q r} : LocalFirst bs p (.ok (some q)) → LocalRest bs q q r → LocalEnd bs p r

/-- A local name without the `\` of its escapes; a final `\` stays. -/
def Unescape : List U8 → List U8
  | [] => []
  | [b] => [b]
  | b :: c :: rest => if b.val = 92 then c :: Unescape rest else b :: Unescape (c :: rest)

/-- The namespace of the last declaration of the prefix `key`. -/
noncomputable def Lookup (prefixes : List (List U8 × List U8)) (key : List U8) : Option (List U8) :=
  (prefixes.reverse.find? (fun d => decide (d.1 = key))).map (·.2)

/-! ## IRIs -/

/-- The bytes are an RFC 3987 IRI reference. -/
def IsReference (spelling : List U8) : Prop :=
  ∃ word, Rowl.Regular.Utf8From spelling 0 word ∧ word ∈ Rowl.Iri.ReferenceLanguage

/-- RFC 3986 section 5.2 resolution of the bytes `reference` against the bytes
    `base` gives `target`, for inputs shorter than `usize::MAX / 8` bytes. -/
def Resolves (base reference target : List U8) : Prop :=
  base.length < Usize.max / 8 ∧ reference.length < Usize.max / 8 ∧
    Rowl.IriResolution.resolve (Rowl.References.Word base) (Rowl.References.Word reference) =
      some (Rowl.References.Word target)

/-- The IRIREF or STRING_LITERAL_QUOTE token at `p` with the characters `word`,
    ending at `q`. -/
def QuotedAt (bs : List U8) (iri : Bool) (p : Nat) (word : List U8) (q : Nat) : Prop :=
  ∃ start stop : Usize, start.val = p ∧ stop.val = q ∧ QuotedToken bs start iri word stop

/-- The IRIREF or STRING_LITERAL_QUOTE token at `p` fails with `f`. -/
def QuotedFault (bs : List U8) (iri : Bool) (limit p : Nat) (f : Fault) : Prop :=
  ∃ start : Usize, start.val = p ∧ ∃ e, QuotedError bs start iri limit e ∧ lifted e = f

/-- The IRIREF at `start`, resolved against `base`. -/
inductive IriRef (bs base : List U8) (limit start : Nat) : Except Fault (List U8 × Nat) → Prop
  | token {f} : QuotedFault bs true limit start f → IriRef bs base limit start (.error f)
  | notReference {ref q} : QuotedAt bs true start ref q → ref.length ≤ limit → ¬ IsReference ref →
      IriRef bs base limit start (.error (.InvalidIri, start))
  | unresolved {ref q} : QuotedAt bs true start ref q → ref.length ≤ limit → IsReference ref →
      (∀ t, ¬ Resolves base ref t) → IriRef bs base limit start (.error (.InvalidIri, start))
  | tooLong {ref q t} : QuotedAt bs true start ref q → ref.length ≤ limit → IsReference ref →
      Resolves base ref t → limit < t.length → IriRef bs base limit start (.error (.ResourceLimit, start))
  | invalid {ref q t} : QuotedAt bs true start ref q → ref.length ≤ limit → IsReference ref →
      Resolves base ref t → t.length ≤ limit → ¬ AbsoluteIri t →
      IriRef bs base limit start (.error (.InvalidIri, start))
  | iri {ref q t} : QuotedAt bs true start ref q → ref.length ≤ limit → IsReference ref →
      Resolves base ref t → t.length ≤ limit → AbsoluteIri t → IriRef bs base limit start (.ok (t, q))

/-- The prefixed name at `start`, whose PNAME_NS ends with the colon at `colon`:
    the namespace of its prefix followed by its local name without escapes. -/
inductive Prefixed (bs : List U8) (prefixes : List (List U8 × List U8)) (limit start colon : Nat) :
    Except Fault (List U8 × Nat) → Prop
  | undefined : Lookup prefixes (Span bs start colon) = none →
      Prefixed bs prefixes limit start colon (.error (.UndefinedPrefix, start))
  | localFails {ns f} : Lookup prefixes (Span bs start colon) = some ns → LocalEnd bs (colon + 1) (.error f) →
      Prefixed bs prefixes limit start colon (.error f)
  | tooLong {ns e} : Lookup prefixes (Span bs start colon) = some ns → LocalEnd bs (colon + 1) (.ok e) →
      limit < (ns ++ Unescape (Span bs (colon + 1) e)).length →
      Prefixed bs prefixes limit start colon (.error (.ResourceLimit, start))
  | invalid {ns e} : Lookup prefixes (Span bs start colon) = some ns → LocalEnd bs (colon + 1) (.ok e) →
      (ns ++ Unescape (Span bs (colon + 1) e)).length ≤ limit →
      ¬ AbsoluteIri (ns ++ Unescape (Span bs (colon + 1) e)) →
      Prefixed bs prefixes limit start colon (.error (.InvalidIri, start))
  | iri {ns e} : Lookup prefixes (Span bs start colon) = some ns → LocalEnd bs (colon + 1) (.ok e) →
      (ns ++ Unescape (Span bs (colon + 1) e)).length ≤ limit →
      AbsoluteIri (ns ++ Unescape (Span bs (colon + 1) e)) →
      Prefixed bs prefixes limit start colon (.ok (ns ++ Unescape (Span bs (colon + 1) e), e))

/-- An iri at `start`: an IRIREF, or a prefixed name. -/
inductive IriAt (bs base : List U8) (prefixes : List (List U8 × List U8)) (limit start : Nat) :
    Except Fault (List U8 × Nat) → Prop
  | ref {r} : ByteIs bs start 60 → IriRef bs base limit start r → IriAt bs base prefixes limit start r
  | colonFails {f} : ¬ ByteIs bs start 60 → PrefixColon bs start (.error f) →
      IriAt bs base prefixes limit start (.error f)
  | missing : ¬ ByteIs bs start 60 → PrefixColon bs start (.ok none) →
      IriAt bs base prefixes limit start (.error (.ExpectedIri, start))
  | prefixed {colon r} : ¬ ByteIs bs start 60 → PrefixColon bs start (.ok (some colon)) →
      Prefixed bs prefixes limit start colon r → IriAt bs base prefixes limit start r

/-! ## Blank node labels -/

/-- The BLANK_NODE_LABEL at `start`, whose first byte is `_`: a blank node of the
    caller's scope with the label after `_:`. -/
inductive BlankLabel (bs scope : List U8) (limit start : Nat) : Except Fault (Term × Nat) → Prop
  | noColon : ¬ ByteIs bs (start + 1) 58 → BlankLabel bs scope limit start (.error (.InvalidBlankLabel, start))
  | missing {f} : ByteIs bs (start + 1) 58 → MissingFault bs (start + 2) f →
      BlankLabel bs scope limit start (.error f)
  | badFirst {c q} : ByteIs bs (start + 1) 58 → Unit bs (start + 2) c q → ¬ LabelFirst c →
      BlankLabel bs scope limit start (.error (.InvalidBlankLabel, start + 2))
  | tailFails {c q f} : ByteIs bs (start + 1) 58 → Unit bs (start + 2) c q → LabelFirst c →
      NameTail bs q q (.error f) → BlankLabel bs scope limit start (.error f)
  | tooLong {c q e} : ByteIs bs (start + 1) 58 → Unit bs (start + 2) c q → LabelFirst c →
      NameTail bs q q (.ok e) → limit < e - (start + 2) →
      BlankLabel bs scope limit start (.error (.ResourceLimit, start + 2))
  | label {c q e} : ByteIs bs (start + 1) 58 → Unit bs (start + 2) c q → LabelFirst c →
      NameTail bs q q (.ok e) → e - (start + 2) ≤ limit →
      BlankLabel bs scope limit start (.ok (.blank scope (Span bs (start + 2) e), e))


/-! ## Strings -/

/-- One raw or escaped character `x` of a short string at `p`, ending at `n`. -/
def StringItem (bs : List U8) (p x n : Nat) : Prop :=
  ∃ (cp : U32) (stop : Usize), cp.val = x ∧ stop.val = n ∧ QuotedItem bs false p cp stop

/-- The character of a short string at `p` fails with `f`. -/
def ItemFault (bs : List U8) (p : Nat) (f : Fault) : Prop :=
  ∃ position : Usize, position.val = p ∧ ∃ e, ItemError bs position false e ∧ lifted e = f

/-- The body of STRING_LITERAL_SINGLE_QUOTE from `p` to its closing `'`, with the
    UTF-8 bytes `v` of the characters before `p`. -/
inductive SingleBody (bs : List U8) (limit : Nat) : Nat → List U8 → Except Fault (List U8 × Nat) → Prop
  | missing {p v f} : MissingFault bs p f → SingleBody bs limit p v (.error f)
  | close {p v q} : Unit bs p 39 q → SingleBody bs limit p v (.ok (v, q))
  | itemFails {p v c q f} : Unit bs p c q → c ≠ 39 → ItemFault bs p f → SingleBody bs limit p v (.error f)
  | tooLong {p v c q x n enc} : Unit bs p c q → c ≠ 39 → StringItem bs p x n →
      Rowl.Encoding.EncodeCorrect x (some enc) → limit < v.length + (Rowl.Encoding.Bytes enc).length →
      SingleBody bs limit p v (.error (.ResourceLimit, p))
  | item {p v c q x n enc r} : Unit bs p c q → c ≠ 39 → StringItem bs p x n →
      Rowl.Encoding.EncodeCorrect x (some enc) → v.length + (Rowl.Encoding.Bytes enc).length ≤ limit →
      SingleBody bs limit n (v ++ Rowl.Encoding.Bytes enc) r → SingleBody bs limit p v r

/-- Three quotes `quote` at `p`. -/
def TripleQuote (bs : List U8) (p quote : Nat) : Prop :=
  ByteIs bs p quote ∧ ByteIs bs (p + 1) quote ∧ ByteIs bs (p + 2) quote

/-- One character `x` of a long string at `p`, ending at `n`: any character
    but `\`, or ECHAR or UCHAR. -/
inductive LongItem (bs : List U8) (p : Nat) : Nat → Nat → Prop
  | raw {c q} : Unit bs p c q → c ≠ 92 → LongItem bs p c q
  | escape {q} {cp : U32} {n : Usize} : Unit bs p 92 q → EscapeValue bs false q cp n →
      LongItem bs p cp.val n.val

/-- The body of a long string from `p` to its closing three quotes `quote`,
    with the UTF-8 bytes `v` of the characters before `p`: its characters and
    the position after the closing quotes. -/
inductive LongBody (bs : List U8) (quote : Nat) : Nat → List U8 → List U8 × Nat → Prop
  | close {p v} : TripleQuote bs p quote → LongBody bs quote p v (v, p + 3)
  | item {p v x n enc r} : ¬ TripleQuote bs p quote → LongItem bs p x n →
      Rowl.Encoding.EncodeCorrect x (some enc) → LongBody bs quote n (v ++ Rowl.Encoding.Bytes enc) r →
      LongBody bs quote p v r

/-- The String at `start`, whose first three bytes are the quotes `quote`: the
    long string when one is there, and otherwise, as the longest match, the
    empty short string of the first two quotes. -/
inductive LongString (bs : List U8) (limit quote start : Nat) : Except Fault (List U8 × Nat) → Prop
  | tooLong {v n} : LongBody bs quote (start + 3) [] (v, n) → limit < v.length →
      LongString bs limit quote start (.error (.ResourceLimit, start))
  | long {v n} : LongBody bs quote (start + 3) [] (v, n) → v.length ≤ limit →
      LongString bs limit quote start (.ok (v, n))
  | empty : (∀ v n, ¬ LongBody bs quote (start + 3) [] (v, n)) →
      LongString bs limit quote start (.ok ([], start + 2))

/-- The String at `start`, whose first byte is a quote: its characters and the
    position after it. -/
inductive StringAt (bs : List U8) (limit start : Nat) : Except Fault (List U8 × Nat) → Prop
  | longDouble {r} : TripleQuote bs start 34 → LongString bs limit 34 start r → StringAt bs limit start r
  | longSingle {r} : ¬ TripleQuote bs start 34 → TripleQuote bs start 39 → LongString bs limit 39 start r →
      StringAt bs limit start r
  | doubleFails {f} : ¬ TripleQuote bs start 34 → ¬ TripleQuote bs start 39 → ByteIs bs start 34 →
      QuotedFault bs false limit start f → StringAt bs limit start (.error f)
  | double {w q} : ¬ TripleQuote bs start 34 → ¬ TripleQuote bs start 39 → ByteIs bs start 34 →
      QuotedAt bs false start w q → w.length ≤ limit → StringAt bs limit start (.ok (w, q))
  | single {r} : ¬ TripleQuote bs start 34 → ¬ TripleQuote bs start 39 → ¬ ByteIs bs start 34 →
      SingleBody bs limit (start + 1) [] r → StringAt bs limit start r

/-! ## Language tags and literals -/

/-- An ASCII letter. -/
def Letter (n : Nat) : Prop := (65 ≤ n ∧ n ≤ 90) ∨ (97 ≤ n ∧ n ≤ 122)
/-- An ASCII digit. -/
def Digit (n : Nat) : Prop := 48 ≤ n ∧ n ≤ 57

/-- The end of the ASCII letters from `i`. -/
noncomputable def LettersEnd (bs : List U8) (i : Nat) : Nat :=
  i + ((bs.drop i).takeWhile (fun b => decide (Letter b.val))).length
/-- The end of the ASCII letters and digits from `i`. -/
noncomputable def AlnumsEnd (bs : List U8) (i : Nat) : Nat :=
  i + ((bs.drop i).takeWhile (fun b => decide (Letter b.val ∨ Digit b.val))).length

/-- The end of the subtags `('-' [a-zA-Z0-9]+)*` from `i`, ending before a `-`
    that no letter or digit follows. -/
noncomputable def SubtagsEnd (bs : List U8) (i : Nat) : Nat :=
  if h : ByteIs bs i 45 ∧ i + 1 < AlnumsEnd bs (i + 1) then SubtagsEnd bs (AlnumsEnd bs (i + 1)) else i
termination_by bs.length - i
decreasing_by
  have inside : i < bs.length := by
    obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp h.1
    exact (List.getElem?_eq_some_iff.mp lookup).1
  have bound : AlnumsEnd bs (i + 1) ≤ bs.length := by
    unfold AlnumsEnd
    have := (List.takeWhile_prefix (fun b => decide (Letter b.val ∨ Digit b.val)) (l := bs.drop (i + 1))).length_le
    rw [List.length_drop] at this
    omega
  have := h.2
  omega

/-- The LANGTAG at `start`, whose first byte is `@`: its tag, which must be a
    well-formed BCP 47 language tag, and the position after it. -/
inductive LanguageAt (bs : List U8) (limit start : Nat) : Except Fault (List U8 × Nat) → Prop
  | empty : LettersEnd bs (start + 1) = start + 1 →
      LanguageAt bs limit start (.error (.InvalidLanguageTag, start))
  | tooLong {e} : start + 1 < LettersEnd bs (start + 1) → SubtagsEnd bs (LettersEnd bs (start + 1)) = e →
      limit < e - (start + 1) → LanguageAt bs limit start (.error (.ResourceLimit, start + 1))
  | malformed {e} : start + 1 < LettersEnd bs (start + 1) → SubtagsEnd bs (LettersEnd bs (start + 1)) = e →
      e - (start + 1) ≤ limit → ¬ LanguageTag (Span bs (start + 1) e) →
      LanguageAt bs limit start (.error (.InvalidLanguageTag, start))
  | tag {e} : start + 1 < LettersEnd bs (start + 1) → SubtagsEnd bs (LettersEnd bs (start + 1)) = e →
      e - (start + 1) ≤ limit → LanguageTag (Span bs (start + 1) e) →
      LanguageAt bs limit start (.ok (Span bs (start + 1) e, e))

/-- The datatype after the `^` at `p`: a second `^`, white space and an iri,
    which must not be rdf:langString. -/
inductive DatatypeAt (bs base : List U8) (prefixes : List (List U8 × List U8)) (limit p : Nat) :
    Except Fault (Kind × Nat) → Prop
  | single : ¬ ByteIs bs (p + 1) 94 → DatatypeAt bs base prefixes limit p (.error (.InvalidLiteralKind, p))
  | spaceFails {f} : ByteIs bs (p + 1) 94 → TriviaFault bs (p + 2) f →
      DatatypeAt bs base prefixes limit p (.error f)
  | iriFails {s f} : ByteIs bs (p + 1) 94 → TriviaRuns bs true (p + 2) s →
      IriAt bs base prefixes limit s (.error f) → DatatypeAt bs base prefixes limit p (.error f)
  | langString {s q} : ByteIs bs (p + 1) 94 → TriviaRuns bs true (p + 2) s →
      IriAt bs base prefixes limit s (.ok (LangStringBytes, q)) →
      DatatypeAt bs base prefixes limit p (.error (.InvalidLiteralKind, p))
  | datatype {s d q} : ByteIs bs (p + 1) 94 → TriviaRuns bs true (p + 2) s →
      IriAt bs base prefixes limit s (.ok (d, q)) → d ≠ LangStringBytes →
      DatatypeAt bs base prefixes limit p (.ok (.datatype d, q))

/-- What follows the String that ends at `e`: a LANGTAG or a datatype after
    white space, or nothing, which makes an xsd:string. -/
inductive KindAfter (bs base : List U8) (prefixes : List (List U8 × List U8)) (limit e : Nat) :
    Except Fault (Kind × Nat) → Prop
  | spaceFails {f} : TriviaFault bs e f → KindAfter bs base prefixes limit e (.error f)
  | languageFails {p f} : TriviaRuns bs true e p → ByteIs bs p 64 → LanguageAt bs limit p (.error f) →
      KindAfter bs base prefixes limit e (.error f)
  | language {p t q} : TriviaRuns bs true e p → ByteIs bs p 64 → LanguageAt bs limit p (.ok (t, q)) →
      KindAfter bs base prefixes limit e (.ok (.language t, q))
  | datatype {p r} : TriviaRuns bs true e p → ¬ ByteIs bs p 64 → ByteIs bs p 94 →
      DatatypeAt bs base prefixes limit p r → KindAfter bs base prefixes limit e r
  | plain {p} : TriviaRuns bs true e p → ¬ ByteIs bs p 64 → ¬ ByteIs bs p 94 →
      KindAfter bs base prefixes limit e (.ok (.datatype XsdStringBytes, e))

/-- The RDFLiteral at `start`, whose first byte is a quote. -/
inductive LiteralAt (bs base : List U8) (prefixes : List (List U8 × List U8)) (limit start : Nat) :
    Except Fault (Term × Nat) → Prop
  | stringFails {f} : StringAt bs limit start (.error f) → LiteralAt bs base prefixes limit start (.error f)
  | kindFails {v e f} : StringAt bs limit start (.ok (v, e)) → KindAfter bs base prefixes limit e (.error f) →
      LiteralAt bs base prefixes limit start (.error f)
  | literal {v e k n} : StringAt bs limit start (.ok (v, e)) → KindAfter bs base prefixes limit e (.ok (k, n)) →
      LiteralAt bs base prefixes limit start (.ok (.literal v k, n))


/-! ## Numbers and keywords -/

/-- `true` and `false`. -/
def TrueBytes : List U8 := [116#u8,114#u8,117#u8,101#u8]
def FalseBytes : List U8 := [102#u8,97#u8,108#u8,115#u8,101#u8]
/-- The datatype IRIs of numbers and booleans. -/
def XsdIntegerBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,49#u8,47#u8,88#u8,77#u8,76#u8,83#u8,99#u8,104#u8,101#u8,109#u8,97#u8,35#u8,105#u8,110#u8,116#u8,101#u8,103#u8,101#u8,114#u8]
def XsdDecimalBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,49#u8,47#u8,88#u8,77#u8,76#u8,83#u8,99#u8,104#u8,101#u8,109#u8,97#u8,35#u8,100#u8,101#u8,99#u8,105#u8,109#u8,97#u8,108#u8]
def XsdDoubleBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,49#u8,47#u8,88#u8,77#u8,76#u8,83#u8,99#u8,104#u8,101#u8,109#u8,97#u8,35#u8,100#u8,111#u8,117#u8,98#u8,108#u8,101#u8]
def XsdBooleanBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,49#u8,47#u8,88#u8,77#u8,76#u8,83#u8,99#u8,104#u8,101#u8,109#u8,97#u8,35#u8,98#u8,111#u8,111#u8,108#u8,101#u8,97#u8,110#u8]

/-- The end of the ASCII digits from `i`. -/
noncomputable def DigitsEnd (bs : List U8) (i : Nat) : Nat :=
  i + ((bs.drop i).takeWhile (fun b => decide (Digit b.val))).length

/-- The position after an optional sign `+` or `-` at `i`. -/
noncomputable def Unsigned (bs : List U8) (i : Nat) : Nat :=
  if ByteIs bs i 43 ∨ ByteIs bs i 45 then i + 1 else i

/-- The end of the EXPONENT `[eE] [+-]? [0-9]+` at `i`, if one is there. -/
noncomputable def ExponentEnd (bs : List U8) (i : Nat) : Option Nat :=
  if ByteIs bs i 101 ∨ ByteIs bs i 69 then
    (if Unsigned bs (i + 1) < DigitsEnd bs (Unsigned bs (i + 1)) then
      some (DigitsEnd bs (Unsigned bs (i + 1))) else none)
  else none

/-- The longest INTEGER, DECIMAL or DOUBLE at `start` with its datatype IRI:
    `[+-]? [0-9]+` is an integer, a fraction `'.' [0-9]+` makes it a decimal,
    and an EXPONENT, also after `[0-9]+ '.'` with no fraction digits, a double.
    A `.` that no digit follows ends a number, which then needs integer digits. -/
noncomputable def NumberEnd (bs : List U8) (start : Nat) : Option (Nat × List U8) :=
  let digits := Unsigned bs start
  let point := DigitsEnd bs digits
  if ByteIs bs point 46 then
    let fraction := DigitsEnd bs (point + 1)
    if point + 1 < fraction then
      some (match ExponentEnd bs fraction with
        | some e => (e, XsdDoubleBytes)
        | none => (fraction, XsdDecimalBytes))
    else if digits < point then
      some (match ExponentEnd bs (point + 1) with
        | some e => (e, XsdDoubleBytes)
        | none => (point, XsdIntegerBytes))
    else none
  else if digits < point then
    some (match ExponentEnd bs point with
      | some e => (e, XsdDoubleBytes)
      | none => (point, XsdIntegerBytes))
  else none

/-- The NumericLiteral at `start`, with its lexical form as written. -/
inductive NumberAt (bs : List U8) (limit start : Nat) : Except Fault (Term × Nat) → Prop
  | none : NumberEnd bs start = none → NumberAt bs limit start (.error (.ExpectedObject, start))
  | tooLong {e d} : NumberEnd bs start = some (e, d) → limit < e - start →
      NumberAt bs limit start (.error (.ResourceLimit, start))
  | number {e d} : NumberEnd bs start = some (e, d) → e - start ≤ limit →
      NumberAt bs limit start (.ok (.literal (Span bs start e) (.datatype d), e))

/-- `word` is at `i`. -/
def WordAt (bs : List U8) (i : Nat) (word : List U8) : Prop := word <+: bs.drop i

/-- A LANGTAG continues at `i`: an ASCII letter, digit or `-`. -/
def TagContinues (bs : List U8) (i : Nat) : Prop :=
  ∃ b, bs[i]? = some b ∧ (Letter b.val ∨ Digit b.val ∨ b.val = 45)

/-- The keyword `@` followed by `word` at `start`, where no longer LANGTAG
    begins. -/
def AtKeyword (bs : List U8) (start : Nat) (word : List U8) : Prop :=
  ByteIs bs start 64 ∧ WordAt bs (start + 1) word ∧ ¬ TagContinues bs (start + 1 + word.length)

/-- The ASCII letters `upper` in any case at `i`. -/
def AnyCase (bs : List U8) : Nat → List Nat → Prop
  | _, [] => True
  | i, u :: rest => (ByteIs bs i u ∨ ByteIs bs i (u + 32)) ∧ AnyCase bs (i + 1) rest

/-- The prefixed name, `true` or `false` at `start`, whose first character is
    PN_CHARS_BASE or `:`. -/
inductive WordObject (bs : List U8) (prefixes : List (List U8 × List U8)) (limit start : Nat) :
    Except Fault (Term × Nat) → Prop
  | colonFails {f} : PrefixColon bs start (.error f) → WordObject bs prefixes limit start (.error f)
  | prefixedFails {colon f} : PrefixColon bs start (.ok (some colon)) →
      Prefixed bs prefixes limit start colon (.error f) → WordObject bs prefixes limit start (.error f)
  | prefixed {colon v n} : PrefixColon bs start (.ok (some colon)) →
      Prefixed bs prefixes limit start colon (.ok (v, n)) → WordObject bs prefixes limit start (.ok (.iri v, n))
  | true : PrefixColon bs start (.ok none) → WordAt bs start TrueBytes →
      WordObject bs prefixes limit start (.ok (.literal TrueBytes (.datatype XsdBooleanBytes), start + 4))
  | false : PrefixColon bs start (.ok none) → ¬ WordAt bs start TrueBytes → WordAt bs start FalseBytes →
      WordObject bs prefixes limit start (.ok (.literal FalseBytes (.datatype XsdBooleanBytes), start + 5))
  | other : PrefixColon bs start (.ok none) → ¬ WordAt bs start TrueBytes → ¬ WordAt bs start FalseBytes →
      WordObject bs prefixes limit start (.error (.ExpectedObject, start))


/-! ## Results of the reader -/

/-- A reader result agrees with an outcome of a relation: the same value, seen
    through `view`, or the same failure. -/
def Agrees {A B : Type} (view : A → B) : core.result.Result A turtle.ReadError → Except Fault B → Prop
  | .Ok a, .ok b => view a = b
  | .Err e, .error f => faultOf e = f
  | _, _ => False

theorem agrees_ok {A B : Type} {view : A → B} {a : A} {o : Except Fault B}
    (h : Agrees view (.Ok a) o) : o = .ok (view a) := by
  cases o with
  | error f => exact False.elim h
  | ok b => simp only [Agrees] at h; rw [h]

theorem agrees_err {A B : Type} {view : A → B} {e : turtle.ReadError} {o : Except Fault B}
    (h : Agrees view (.Err e) o) : o = .error (faultOf e) := by
  cases o with
  | error f => simp only [Agrees] at h; rw [h]
  | ok b => exact False.elim h

theorem agrees_ok_inv {A B : Type} {view : A → B} {r : core.result.Result A turtle.ReadError} {b : B}
    (h : Agrees view r (.ok b)) : ∃ a, r = .Ok a ∧ view a = b := by
  cases r with
  | Ok a => exact ⟨a, rfl, h⟩
  | Err e => exact False.elim h

@[simp] theorem from_residual_err {T : Type} (e : turtle.ReadError) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame turtle.ReadError) (.Err e) = .ok (.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]

theorem kind_of_spec (k : ntriples.ErrorKind) : turtle.kind_of k = .ok (KindOf k) := by
  cases k <;> rfl

theorem lift_spec (e : ntriples.ReadError) : turtle.from_ntriples e = .ok ⟨KindOf e.kind, e.offset⟩ := by
  simp [turtle.from_ntriples, kind_of_spec]

@[simp] theorem fault_of_lift (e : ntriples.ReadError) :
    faultOf ⟨KindOf e.kind, e.offset⟩ = lifted e := rfl

theorem error_spec (k : turtle.ErrorKind) (o : Usize) : turtle.error k o = .ok ⟨k, o⟩ := rfl

/-- A natural number below the machine bound is the value of a `usize`. -/
theorem usize_of {n : Nat} (bound : n ≤ Usize.max) : ∃ u : Usize, u.val = n := by
  have h : n < 2 ^ UScalarTy.Usize.numBits := by
    have := Usize.max_def
    simp only [UScalarTy.numBits] at *
    have positive : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
    simp [Usize.numBits] at this
    omega
  exact ⟨UScalar.ofNatCore n h, UScalar.ofNatCore_val_eq h⟩

theorem vec_index {T : Type} {v : alloc.vec.Vec T} {i : Usize} (inside : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) v i = .ok v.val[i.val] := by
  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]

theorem vec_index_usize {T : Type} {v : alloc.vec.Vec T} {i : Usize} (inside : i.val < v.val.length) :
    alloc.vec.Vec.index_usize v i = .ok v.val[i.val] := by
  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]

theorem slice_index {v : Slice U8} {i : Usize} (inside : i.val < v.val.length) :
    Slice.index_usize v i = .ok v.val[i.val] := by
  simp [Slice.index_usize, List.getElem?_eq_getElem inside]

/-! ## Characters -/

theorem unit_unique {bs : List U8} {p c q c' q' : Nat} (one : Unit bs p c q) (two : Unit bs p c' q') :
    c = c' ∧ q = q' := by
  have pair := Prod.mk.inj (Option.some.inj (one.2.2.symm.trans two.2.2))
  refine ⟨pair.1, ?_⟩
  have := one.1
  have := two.1
  omega

theorem malformed_not_unit {bs : List U8} {p c q : Nat} (bad : Malformed bs p) (u : Unit bs p c q) : False := by
  rcases bad with outside | ⟨inside, invalid⟩
  · have := u.1
    have := u.2.1
    omega
  · rw [u.2.2] at invalid
    contradiction

theorem end_not_unit {bs : List U8} {p c q : Nat} (h : p = bs.length) (u : Unit bs p c q) : False := by
  have := u.1
  have := u.2.1
  omega

theorem malformed_not_end {bs : List U8} {p : Nat} (bad : Malformed bs p) (h : p = bs.length) : False := by
  rcases bad with outside | ⟨inside, invalid⟩ <;> omega

theorem unit_progress {bs : List U8} {p c q : Nat} (u : Unit bs p c q) : p < q ∧ q ≤ bs.length := ⟨u.1, u.2.1⟩

/-- What `turtle::unit` reads at `p`: a character, the end, or a malformed
    character. -/
def UnitResult (bs : List U8) (p : Nat) : core.result.Result (Option (U32 × Usize)) turtle.ReadError → Prop
  | .Ok none => p = bs.length
  | .Ok (some (cp, next)) => Unit bs p cp.val next.val
  | .Err e => Malformed bs p ∧ faultOf e = (.MalformedUtf8, p)

theorem unit_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ r, turtle.unit bytes position = .ok r ∧ UnitResult bytes.val position.val r := by
  obtain ⟨r, run, correct⟩ := Rowl.NTriples.at_total_correct bytes position
  cases r with
  | Ok found =>
    refine ⟨.Ok found, by simp [turtle.unit, run], ?_⟩
    rcases found with _ | ⟨cp, next⟩
    · exact correct
    · exact correct
  | Err e =>
    refine ⟨.Err ⟨KindOf e.kind, e.offset⟩, by simp [turtle.unit, run, lift_spec], ?_⟩
    obtain ⟨kind, offset, bad⟩ := correct
    exact ⟨bad, by simp [faultOf, kind, KindOf, offset]⟩

theorem unit_at {bytes : alloc.vec.Vec U8} {position : Usize} {c q : Nat}
    (u : Unit bytes.val position.val c q) :
    ∃ cp next, turtle.unit bytes position = .ok (.Ok (some (cp, next))) ∧ cp.val = c ∧ next.val = q := by
  obtain ⟨r, run, correct⟩ := unit_total_correct bytes position
  rcases r with (_ | ⟨cp, next⟩) | e
  · exact False.elim (end_not_unit correct u)
  · obtain ⟨rfl, rfl⟩ := unit_unique correct u
    exact ⟨cp, next, run, rfl, rfl⟩
  · exact False.elim (malformed_not_unit correct.1 u)

theorem unit_end {bytes : alloc.vec.Vec U8} {position : Usize} (h : position.val = bytes.val.length) :
    turtle.unit bytes position = .ok (.Ok none) := by
  obtain ⟨r, run, correct⟩ := unit_total_correct bytes position
  rcases r with (_ | ⟨cp, next⟩) | e
  · exact run
  · exact False.elim (end_not_unit h correct)
  · exact False.elim (malformed_not_end correct.1 h)

/-- What `turtle::needed` reads at `p`: a character, or a missing one. -/
def NeededResult (bs : List U8) (p : Nat) : core.result.Result (U32 × Usize) turtle.ReadError → Prop
  | .Ok (cp, next) => Unit bs p cp.val next.val
  | .Err e => MissingFault bs p (faultOf e)

theorem needed_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ r, turtle.needed bytes position = .ok r ∧ NeededResult bytes.val position.val r := by
  obtain ⟨r, run, correct⟩ := Rowl.NTriples.required_total_correct bytes position
  cases r with
  | Ok pair =>
    obtain ⟨cp, next⟩ := pair
    exact ⟨.Ok (cp, next), by simp [turtle.needed, run], correct⟩
  | Err e =>
    refine ⟨.Err ⟨KindOf e.kind, e.offset⟩, by simp [turtle.needed, run, lift_spec], ?_⟩
    rcases correct with ⟨kind, offset, bad⟩ | ⟨kind, offset, atEnd⟩
    · exact Or.inl ⟨bad, by simp [faultOf, kind, KindOf, offset]⟩
    · exact Or.inr ⟨atEnd, by simp [faultOf, kind, KindOf, offset]⟩

theorem missing_not_unit {bs : List U8} {p c q : Nat} {f : Fault} (missing : MissingFault bs p f)
    (u : Unit bs p c q) : False := by
  rcases missing with ⟨bad, _⟩ | ⟨atEnd, _⟩
  · exact malformed_not_unit bad u
  · exact end_not_unit atEnd u

theorem needed_at {bytes : alloc.vec.Vec U8} {position : Usize} {c q : Nat}
    (u : Unit bytes.val position.val c q) :
    ∃ cp next, turtle.needed bytes position = .ok (.Ok (cp, next)) ∧ cp.val = c ∧ next.val = q := by
  obtain ⟨r, run, correct⟩ := needed_total_correct bytes position
  rcases r with ⟨cp, next⟩ | e
  · obtain ⟨rfl, rfl⟩ := unit_unique correct u
    exact ⟨cp, next, run, rfl, rfl⟩
  · exact False.elim (missing_not_unit correct u)

/-- What `turtle::space` reads from `p`: the white space and comments there. -/
def SpaceResult (bs : List U8) (p : Nat) : core.result.Result Usize turtle.ReadError → Prop
  | .Ok q => TriviaRuns bs true p q.val
  | .Err e => TriviaFault bs p (faultOf e)

theorem space_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ r, turtle.space bytes position = .ok r ∧ SpaceResult bytes.val position.val r := by
  obtain ⟨r, run, correct⟩ := Rowl.NTriples.skip_total_correct bytes position true
  cases r with
  | Ok next => exact ⟨.Ok next, by simp [turtle.space, run], correct⟩
  | Err e =>
    exact ⟨.Err ⟨KindOf e.kind, e.offset⟩, by simp [turtle.space, run, lift_spec], e, correct, rfl⟩

theorem comment_bound {bs : List U8} {p q : Nat} (runs : Rowl.NTriples.CommentRuns bs p q) :
    p ≤ q ∧ q ≤ bs.length := by
  induction runs with
  | eof => omega
  | eol unit ending => have := unit.1; have := unit.2.1; omega
  | character unit ending tail ih => have := unit.1; omega

theorem trivia_bound {bs : List U8} {p q : Nat} (runs : TriviaRuns bs true p q) : p ≤ q ∧ q ≤ bs.length := by
  induction runs with
  | eof => omega
  | token unit spacing marker => have := unit.1; have := unit.2.1; omega
  | space unit spacing tail ih => have := unit.1; omega
  | commentLine mode unit marker comments => cases mode
  | commentLines mode unit marker comments tail ih =>
    have := unit.1
    have := comment_bound comments
    omega

theorem space_runs {bytes : alloc.vec.Vec U8} {position : Usize} {q : Nat}
    (runs : TriviaRuns bytes.val true position.val q) :
    ∃ stop : Usize, turtle.space bytes position = .ok (.Ok stop) ∧ stop.val = q := by
  have bound := (trivia_bound runs).2
  obtain ⟨stop, value⟩ := usize_of (n := q) (by have := bytes.property; omega)
  have skip := (Rowl.NTriples.skip_accepted_iff bytes position stop true).mpr (by rw [value]; exact runs)
  exact ⟨stop, by simp [turtle.space, skip], value⟩

/-! ## Bytes -/

theorem byte_is_spec (bytes : alloc.vec.Vec U8) (index : Usize) (value : U8) :
    turtle.byte_is bytes index value = .ok (decide (ByteIs bytes.val index.val value.val)) := by
  unfold turtle.byte_is ByteIs
  by_cases inside : index.val < bytes.val.length
  · simp [alloc.vec.Vec.len_val, inside, vec_index inside, vec_index_usize inside, List.getElem?_eq_getElem inside, UScalar.eq_equiv]
  · simp [alloc.vec.Vec.len_val, inside, List.getElem?_eq_none (by omega : bytes.val.length ≤ index.val)]

theorem byte_inside {bs : List U8} {i v : Nat} (h : ByteIs bs i v) : i < bs.length := by
  obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp h
  exact (List.getElem?_eq_some_iff.mp lookup).1

/-! ## Character classes -/

theorem pn_u_spec (cp : U32) : turtle.pn_u cp = .ok (decide (PnCharsU cp.val)) := by
  obtain ⟨_, base, _⟩ := Rowl.NTriples.token_classes_total_correct cp
  simp only [turtle.pn_u, base, bind_ok, PnCharsU, UScalar.eq_equiv]
  by_cases h : PnBase cp.val <;> simp [h]

theorem in_range_spec (cp lower upper : U32) :
    ntriples.in_range cp lower upper = .ok (decide (lower.val ≤ cp.val ∧ cp.val ≤ upper.val)) := by
  simp [ntriples.in_range]
  split <;> simp_all

theorem pn_chars_spec (cp : U32) : turtle.pn_chars cp = .ok (decide (PnChars cp.val)) := by
  obtain ⟨_, _, _, _, digit, _⟩ := Rowl.NTriples.token_classes_total_correct cp
  simp only [turtle.pn_chars, pn_u_spec, digit, in_range_spec, bind_ok, UScalar.eq_equiv]
  by_cases a : PnCharsU cp.val
  · simp [a, PnChars]
  · by_cases b : cp.val = 45
    · simp [a, b, PnChars]
    · by_cases d : AsciiDigit cp.val
      · simp [a, b, d, PnChars]
      · by_cases e : cp.val = 183
        · simp [a, b, d, e, PnChars]
        · simp only [a, b, d, e, decide_false, Bool.false_eq_true, if_false, PnChars, false_or]
          by_cases f : 768 ≤ cp.val ∧ cp.val ≤ 879
          · simp [b, e, f]
          · simp [b, e, f]

theorem label_first_spec (cp : U32) : turtle.label_first cp = .ok (decide (LabelFirst cp.val)) := by
  obtain ⟨_, _, _, _, digit, _⟩ := Rowl.NTriples.token_classes_total_correct cp
  simp only [turtle.label_first, pn_u_spec, digit, bind_ok]
  by_cases a : PnCharsU cp.val <;> simp [a, LabelFirst]

theorem local_first_char_spec (cp : U32) :
    turtle.local_first_char cp = .ok (decide (LocalFirstChar cp.val)) := by
  obtain ⟨_, _, _, _, digit, _⟩ := Rowl.NTriples.token_classes_total_correct cp
  simp only [turtle.local_first_char, pn_u_spec, digit, bind_ok, UScalar.eq_equiv]
  by_cases a : PnCharsU cp.val <;> by_cases b : cp.val = 58 <;> simp_all [LocalFirstChar]

theorem local_char_spec (cp : U32) : turtle.local_char cp = .ok (decide (LocalChar cp.val)) := by
  simp only [turtle.local_char, pn_chars_spec, bind_ok, UScalar.eq_equiv]
  by_cases a : PnChars cp.val <;> simp [a, LocalChar]

theorem local_escape_iff (c : Nat) :
    LocalEscape c ↔ c = 33 ∨ (35 ≤ c ∧ c ≤ 47) ∨ c = 59 ∨ c = 61 ∨ c = 63 ∨ c = 64 ∨ c = 95 ∨ c = 126 := by
  simp only [LocalEscape, List.mem_cons, List.mem_nil_iff, or_false]
  omega

theorem local_escape_spec (cp : U32) : turtle.local_escape cp = .ok (decide (LocalEscape cp.val)) := by
  rw [local_escape_iff]
  simp only [turtle.local_escape, in_range_spec, bind_ok, UScalar.eq_equiv]
  by_cases a : cp.val = 33
  · simp [a]
  · by_cases b : 35 ≤ cp.val ∧ cp.val ≤ 47
    · simp [a, b]
    · by_cases c : cp.val = 59 <;> by_cases d : cp.val = 61 <;> by_cases e : cp.val = 63 <;>
        by_cases f : cp.val = 64 <;> by_cases g : cp.val = 95 <;> simp [a, b, c, d, e, f, g]

theorem plx_start_spec (cp : U32) : turtle.plx_start cp = .ok (decide (PlxStart cp.val)) := by
  simp only [turtle.plx_start, UScalar.eq_equiv]
  by_cases a : cp.val = 37 <;> simp [a, PlxStart]

theorem word_start_spec (cp : U32) : turtle.word_start cp = .ok (decide (WordStart cp.val)) := by
  obtain ⟨_, base, _⟩ := Rowl.NTriples.token_classes_total_correct cp
  simp only [turtle.word_start, base, bind_ok, UScalar.eq_equiv]
  by_cases a : PnBase cp.val <;> simp [a, WordStart]

theorem quote_spec (cp : U32) : turtle.quote cp = .ok (decide (QuoteChar cp.val)) := by
  simp only [turtle.quote, UScalar.eq_equiv]
  by_cases a : cp.val = 34 <;> simp [a, QuoteChar]

theorem number_start_spec (cp : U32) : turtle.number_start cp = .ok (decide (NumberStart cp.val)) := by
  obtain ⟨_, _, _, _, digit, _⟩ := Rowl.NTriples.token_classes_total_correct cp
  simp only [turtle.number_start, digit, bind_ok, UScalar.eq_equiv]
  by_cases a : AsciiDigit cp.val <;> by_cases b : cp.val = 43 <;> by_cases d : cp.val = 45 <;>
    simp_all [NumberStart]

theorem start_of_spec (cp : U32) : turtle.start_of cp = .ok (StartOf cp.val) := by
  simp only [turtle.start_of, quote_spec, number_start_spec, word_start_spec, bind_ok, UScalar.eq_equiv,
    StartOf]
  split_ifs <;> simp_all


/-! ## Names -/

theorem not_pn_chars_46 : ¬ PnChars 46 := by simp [PnChars, PnCharsU, PnBase, AsciiDigit]

theorem name_end_total_correct (bytes : alloc.vec.Vec U8) (position accepted : Usize) :
    ∃ r o, turtle.name_end bytes position accepted = .ok r ∧
      NameTail bytes.val position.val accepted.val o ∧ Agrees (·.val) r o := by
  rw [turtle.name_end]
  obtain ⟨u, run, correct⟩ := unit_total_correct bytes position
  rcases u with (_ | ⟨cp, next⟩) | e
  · exact ⟨.Ok accepted, .ok accepted.val, by simp [run, core.result.Result.Insts.CoreOpsTry.branch],
      .finish correct, rfl⟩
  · have progress := unit_progress correct
    by_cases isName : PnChars cp.val
    · obtain ⟨r, o, tail, tailRun, agree⟩ := name_end_total_correct bytes next next
      exact ⟨r, o, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, pn_chars_spec, isName, tail],
        .char correct isName tailRun, agree⟩
    · by_cases dot : cp.val = 46
      · obtain ⟨r, o, tail, tailRun, agree⟩ := name_end_total_correct bytes next accepted
        exact ⟨r, o, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, pn_chars_spec, isName,
          UScalar.eq_equiv, dot, tail, not_pn_chars_46], .dot correct dot tailRun, agree⟩
      · exact ⟨.Ok accepted, .ok accepted.val, by simp [run, core.result.Result.Insts.CoreOpsTry.branch,
          pn_chars_spec, isName, UScalar.eq_equiv, dot], .other correct isName dot, rfl⟩
  · refine ⟨.Err e, .error (.MalformedUtf8, position.val), by simp [run, core.result.Result.Insts.CoreOpsTry.branch],
      .malformed correct.1, correct.2⟩
termination_by bytes.val.length - position.val
decreasing_by all_goals omega

theorem name_end_accepted {bytes : alloc.vec.Vec U8} : ∀ {p a : Nat} {r : Except Fault Nat},
    NameTail bytes.val p a r → ∀ {e : Nat}, r = .ok e → ∀ (position accepted : Usize),
      position.val = p → accepted.val = a →
      ∃ stop : Usize, turtle.name_end bytes position accepted = .ok (.Ok stop) ∧ stop.val = e := by
  intro p a r tail
  induction tail with
  | malformed bad => intro e h; cases h
  | finish atEnd =>
    intro e h position accepted hp ha
    cases h
    refine ⟨accepted, ?_, ha⟩
    rw [turtle.name_end]
    simp [unit_end (show position.val = bytes.val.length by omega), core.result.Result.Insts.CoreOpsTry.branch]
  | other u notName notDot =>
    intro e h position accepted hp ha
    cases h
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at (show Unit bytes.val position.val _ _ by rw [hp]; exact u)
    refine ⟨accepted, ?_, ha⟩
    rw [turtle.name_end]
    simp [run, core.result.Result.Insts.CoreOpsTry.branch, pn_chars_spec, hc, notName, UScalar.eq_equiv, notDot]
  | char u isName tail ih =>
    intro e h position accepted hp ha
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at (show Unit bytes.val position.val _ _ by rw [hp]; exact u)
    obtain ⟨stop, again, hs⟩ := ih h next next hn hn
    refine ⟨stop, ?_, hs⟩
    rw [turtle.name_end]
    simp [run, core.result.Result.Insts.CoreOpsTry.branch, pn_chars_spec, hc, isName, again]
  | dot u isDot tail ih =>
    intro e h position accepted hp ha
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at (show Unit bytes.val position.val _ _ by rw [hp]; exact u)
    obtain ⟨stop, again, hs⟩ := ih h next accepted hn ha
    have notName : ¬ PnChars 46 := by simp [PnChars, PnCharsU, PnBase, AsciiDigit]
    refine ⟨stop, ?_, hs⟩
    rw [turtle.name_end]
    simp [run, core.result.Result.Insts.CoreOpsTry.branch, pn_chars_spec, notName, UScalar.eq_equiv, hc, isDot, again]

/-- A name tail ends between where it started reading and the end. -/
theorem name_tail_bound {bs : List U8} : ∀ {p a e : Nat}, NameTail bs p a (.ok e) → a ≤ p → p ≤ bs.length →
    a ≤ e ∧ e ≤ bs.length := by
  intro p a e tail
  generalize result : (Except.ok e : Except Fault Nat) = r at tail
  induction tail with
  | malformed bad => cases result
  | finish atEnd => cases result; intro h1 h2; omega
  | other u notName notDot => cases result; intro h1 h2; omega
  | char u isName tail ih =>
    intro h1 h2
    have := unit_progress u
    have := ih result (le_refl _) this.2
    omega
  | dot u isDot tail ih =>
    intro h1 h2
    have := unit_progress u
    have := ih result (by omega) this.2
    omega

theorem prefix_colon_total_correct (bytes : alloc.vec.Vec U8) (start : Usize) :
    ∃ r o, turtle.prefix_colon bytes start = .ok r ∧
      PrefixColon bytes.val start.val o ∧ Agrees (Option.map (·.val)) r o := by
  rw [turtle.prefix_colon]
  obtain ⟨u, run, correct⟩ := unit_total_correct bytes start
  rcases u with (_ | ⟨cp, next⟩) | e
  · exact ⟨.Ok none, .ok none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch], .finish correct, rfl⟩
  · by_cases colon : cp.val = 58
    · exact ⟨.Ok (some start), .ok (some start.val), by simp [run, core.result.Result.Insts.CoreOpsTry.branch,
        UScalar.eq_equiv, colon], .colon (show Unit bytes.val start.val 58 next.val by rw [← colon]; exact correct), rfl⟩
    · obtain ⟨_, isBase, _⟩ := Rowl.NTriples.token_classes_total_correct cp
      by_cases named : PnBase cp.val
      · obtain ⟨r, o, tail, tailRun, agree⟩ := name_end_total_correct bytes next next
        rcases r with stop | e
        · obtain rfl := agrees_ok agree
          by_cases followed : ByteIs bytes.val stop.val 58
          · refine ⟨.Ok (some stop), .ok (some stop.val), ?_, .named correct named tailRun followed, rfl⟩
            simp [run, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, colon, isBase, named,
              turtle.prefix_end, tail, byte_is_spec, followed]
          · refine ⟨.Ok none, .ok none, ?_, .unnamed correct named tailRun followed, rfl⟩
            simp [run, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, colon, isBase, named,
              turtle.prefix_end, tail, byte_is_spec, followed]
        · obtain rfl := agrees_err agree
          refine ⟨.Err e, .error (faultOf e), ?_, .nameFails correct named tailRun, rfl⟩
          simp [run, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, colon, isBase, named,
            turtle.prefix_end, tail]
      · exact ⟨.Ok none, .ok none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv,
          colon, isBase, named], .other correct colon named, rfl⟩
  · exact ⟨.Err e, .error (.MalformedUtf8, start.val), by simp [run, core.result.Result.Insts.CoreOpsTry.branch],
      .malformed correct.1, correct.2⟩

theorem prefix_colon_accepted {bytes : alloc.vec.Vec U8} {start : Usize} {colon : Option Nat}
    (found : PrefixColon bytes.val start.val (.ok colon)) :
    ∃ r, turtle.prefix_colon bytes start = .ok (.Ok r) ∧ r.map (·.val) = colon := by
  rw [turtle.prefix_colon]
  generalize result : (Except.ok colon : Except Fault (Option Nat)) = o at found
  cases found with
  | malformed bad => cases result
  | finish atEnd =>
    cases result
    exact ⟨none, by simp [unit_end atEnd, core.result.Result.Insts.CoreOpsTry.branch], rfl⟩
  | colon u =>
    cases result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    exact ⟨some start, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, hc], rfl⟩
  | other u notColon notBase =>
    cases result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    obtain ⟨_, isBase, _⟩ := Rowl.NTriples.token_classes_total_correct cp
    exact ⟨none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, hc, notColon,
      isBase, notBase], rfl⟩
  | nameFails u named tail => cases result
  | @named c q e u named tail followed =>
    cases result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    obtain ⟨_, isBase, _⟩ := Rowl.NTriples.token_classes_total_correct cp
    obtain ⟨stop, tailRun, hs⟩ := name_end_accepted tail rfl next next hn hn
    have notColon : c ≠ 58 := by intro h; rw [h] at named; simp [PnBase] at named
    refine ⟨some stop, ?_, by simp [hs]⟩
    simp [run, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, notColon, isBase, hc, named,
      turtle.prefix_end, tailRun, byte_is_spec, hs, followed]
  | @unnamed c q e u named tail followed =>
    cases result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    obtain ⟨_, isBase, _⟩ := Rowl.NTriples.token_classes_total_correct cp
    obtain ⟨stop, tailRun, hs⟩ := name_end_accepted tail rfl next next hn hn
    have notColon : c ≠ 58 := by intro h; rw [h] at named; simp [PnBase] at named
    refine ⟨none, ?_, rfl⟩
    simp [run, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, notColon, isBase, hc, named,
      turtle.prefix_end, tailRun, byte_is_spec, hs, followed]

/-- The colon of a PNAME_NS lies after its start and before the end. -/
theorem prefix_colon_bound {bs : List U8} {start colon : Nat}
    (found : PrefixColon bs start (.ok (some colon))) : start ≤ colon ∧ colon < bs.length := by
  generalize result : (Except.ok (some colon) : Except Fault (Option Nat)) = o at found
  cases found with
  | malformed bad => cases result
  | finish atEnd => cases result
  | colon u => cases result; have := unit_progress u; omega
  | other u notColon notBase => cases result
  | nameFails u named tail => cases result
  | named u named tail followed =>
    cases result
    have progress := unit_progress u
    have := name_tail_bound tail (le_refl _) progress.2
    obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp followed
    have := (List.getElem?_eq_some_iff.mp lookup).1
    omega
  | unnamed u named tail followed => cases result

/-! ## Local names -/

theorem hex_at_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ r o, turtle.hex_at bytes position = .ok r ∧ HexAt bytes.val position.val o ∧
      Agrees (Option.map (·.val)) r o := by
  rw [turtle.hex_at]
  obtain ⟨u, run, correct⟩ := unit_total_correct bytes position
  rcases u with (_ | ⟨cp, next⟩) | e
  · exact ⟨.Ok none, .ok none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch], .finish correct, rfl⟩
  · obtain ⟨digit, hexRun, digitValue⟩ := Rowl.NTriples.hex_total_correct cp
    cases digit with
    | none =>
      exact ⟨.Ok none, .ok none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, hexRun,
        core.option.Option.is_some], .other correct (by simpa using digitValue.symm), rfl⟩
    | some d =>
      exact ⟨.Ok (some next), .ok (some next.val), by simp [run, core.result.Result.Insts.CoreOpsTry.branch, hexRun,
        core.option.Option.is_some], .hex correct (by rw [← digitValue]; simp), rfl⟩
  · exact ⟨.Err e, .error (.MalformedUtf8, position.val), by simp [run, core.result.Result.Insts.CoreOpsTry.branch],
      .malformed correct.1, correct.2⟩



theorem hex_at_accepted {bytes : alloc.vec.Vec U8} {position : Usize} {r : Option Nat}
    (found : HexAt bytes.val position.val (.ok r)) :
    ∃ v, turtle.hex_at bytes position = .ok (.Ok v) ∧ v.map (·.val) = r := by
  rw [turtle.hex_at]
  generalize result : (Except.ok r : Except Fault (Option Nat)) = given at found
  cases found with
  | malformed bad => cases result
  | finish atEnd =>
    cases result
    exact ⟨none, by simp [unit_end atEnd, core.result.Result.Insts.CoreOpsTry.branch], rfl⟩
  | hex u isHex =>
    cases result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    obtain ⟨digit, hexRun, digitValue⟩ := Rowl.NTriples.hex_total_correct cp
    cases digit with
    | none => exact False.elim (isHex (by rw [← hc]; simpa using digitValue.symm))
    | some d =>
      exact ⟨some next, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, hexRun,
        core.option.Option.is_some], by simp [hn]⟩
  | other u notHex =>
    cases result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    obtain ⟨digit, hexRun, digitValue⟩ := Rowl.NTriples.hex_total_correct cp
    cases digit with
    | none =>
      exact ⟨none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, hexRun,
        core.option.Option.is_some], rfl⟩
    | some d => exact False.elim (by rw [hc] at digitValue; simp [notHex] at digitValue)

/-- A character found by a reader ends after it and before the end. -/
theorem hex_at_bound {bs : List U8} {p q : Nat} (found : HexAt bs p (.ok (some q))) : p < q ∧ q ≤ bs.length := by
  generalize result : (Except.ok (some q) : Except Fault (Option Nat)) = given at found
  cases found with
  | malformed bad => cases result
  | finish atEnd => cases result
  | hex u isHex => cases result; exact unit_progress u
  | other u notHex => cases result

theorem percent_total_correct (bytes : alloc.vec.Vec U8) (next : Usize) :
    ∃ r o, turtle.percent bytes next = .ok r ∧ Percent bytes.val next.val o ∧
      Agrees (Option.map (·.val)) r o := by
  rw [turtle.percent]
  obtain ⟨r, o, run, first, agree⟩ := hex_at_total_correct bytes next
  rcases r with (_ | second) | e
  · obtain rfl := agrees_ok agree
    exact ⟨.Ok none, .ok none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch], .none first, rfl⟩
  · obtain rfl := agrees_ok agree
    obtain ⟨r2, o2, run2, last, agree2⟩ := hex_at_total_correct bytes second
    exact ⟨r2, o2, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, run2], .second first last, agree2⟩
  · obtain rfl := agrees_err agree
    exact ⟨.Err e, .error (faultOf e), by simp [run, core.result.Result.Insts.CoreOpsTry.branch], .firstFails first,
      rfl⟩

theorem percent_accepted {bytes : alloc.vec.Vec U8} {next : Usize} {r : Option Nat}
    (found : Percent bytes.val next.val (.ok r)) :
    ∃ v, turtle.percent bytes next = .ok (.Ok v) ∧ v.map (·.val) = r := by
  rw [turtle.percent]
  generalize result : (Except.ok r : Except Fault (Option Nat)) = given at found
  cases found with
  | firstFails first => cases result
  | none first =>
    cases result
    obtain ⟨v, run, value⟩ := hex_at_accepted first
    cases v with
    | none => exact ⟨none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch], rfl⟩
    | some _ => simp at value
  | second first last =>
    subst result
    obtain ⟨v, run, value⟩ := hex_at_accepted first
    cases v with
    | none => simp at value
    | some m =>
      simp only [Option.map_some, Option.some.injEq] at value
      obtain ⟨w, run2, value2⟩ := hex_at_accepted (show HexAt bytes.val m.val _ by rw [value]; exact last)
      exact ⟨w, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, run2], value2⟩

theorem local_escaped_total_correct (bytes : alloc.vec.Vec U8) (next : Usize) :
    ∃ r o, turtle.local_escaped bytes next = .ok r ∧ LocalEscaped bytes.val next.val o ∧
      Agrees (Option.map (·.val)) r o := by
  rw [turtle.local_escaped]
  obtain ⟨u, run, correct⟩ := unit_total_correct bytes next
  rcases u with (_ | ⟨cp, after⟩) | e
  · exact ⟨.Ok none, .ok none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch], .finish correct, rfl⟩
  · by_cases escape : LocalEscape cp.val
    · exact ⟨.Ok (some after), .ok (some after.val), by simp [run, core.result.Result.Insts.CoreOpsTry.branch,
        local_escape_spec, escape], .escape correct escape, rfl⟩
    · exact ⟨.Ok none, .ok none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch,
        local_escape_spec, escape], .other correct escape, rfl⟩
  · exact ⟨.Err e, .error (.MalformedUtf8, next.val), by simp [run, core.result.Result.Insts.CoreOpsTry.branch],
      .malformed correct.1, correct.2⟩

theorem local_escaped_accepted {bytes : alloc.vec.Vec U8} {next : Usize} {r : Option Nat}
    (found : LocalEscaped bytes.val next.val (.ok r)) :
    ∃ v, turtle.local_escaped bytes next = .ok (.Ok v) ∧ v.map (·.val) = r := by
  rw [turtle.local_escaped]
  generalize result : (Except.ok r : Except Fault (Option Nat)) = given at found
  cases found with
  | malformed bad => cases result
  | finish atEnd =>
    cases result
    exact ⟨none, by simp [unit_end atEnd, core.result.Result.Insts.CoreOpsTry.branch], rfl⟩
  | escape u isEscape =>
    cases result
    obtain ⟨cp, after, run, hc, hn⟩ := unit_at u
    exact ⟨some after, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, local_escape_spec, hc, isEscape],
      by simp [hn]⟩
  | other u notEscape =>
    cases result
    obtain ⟨cp, after, run, hc, hn⟩ := unit_at u
    exact ⟨none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, local_escape_spec, hc, notEscape], rfl⟩

theorem plx_total_correct (bytes : alloc.vec.Vec U8) (cp : U32) (next : Usize) :
    ∃ r o, turtle.plx bytes cp next = .ok r ∧ Plx bytes.val cp.val next.val o ∧
      Agrees (Option.map (·.val)) r o := by
  rw [turtle.plx]
  by_cases percent : cp.val = 37
  · obtain ⟨r, o, run, correct, agree⟩ := percent_total_correct bytes next
    exact ⟨r, o, by simp [UScalar.eq_equiv, percent, run], by simp [Plx, percent, correct], agree⟩
  · obtain ⟨r, o, run, correct, agree⟩ := local_escaped_total_correct bytes next
    exact ⟨r, o, by simp [UScalar.eq_equiv, percent, run], by simp [Plx, percent, correct], agree⟩

theorem plx_accepted {bytes : alloc.vec.Vec U8} {cp : U32} {next : Usize} {r : Option Nat}
    (found : Plx bytes.val cp.val next.val (.ok r)) :
    ∃ v, turtle.plx bytes cp next = .ok (.Ok v) ∧ v.map (·.val) = r := by
  rw [turtle.plx]
  by_cases percent : cp.val = 37
  · simp only [Plx, percent, if_true] at found
    obtain ⟨v, run, value⟩ := percent_accepted found
    exact ⟨v, by simp [UScalar.eq_equiv, percent, run], value⟩
  · simp only [Plx, percent, if_false] at found
    obtain ⟨v, run, value⟩ := local_escaped_accepted found
    exact ⟨v, by simp [UScalar.eq_equiv, percent, run], value⟩

theorem plx_bound {bs : List U8} {c q n : Nat} (found : Plx bs c q (.ok (some n))) : q < n ∧ n ≤ bs.length := by
  unfold Plx at found
  split at found
  · generalize result : (Except.ok (some n) : Except Fault (Option Nat)) = given at found
    cases found with
    | firstFails first => cases result
    | none first => cases result
    | second first last =>
      subst result
      have := hex_at_bound first
      have := hex_at_bound last
      omega
  · generalize result : (Except.ok (some n) : Except Fault (Option Nat)) = given at found
    cases found with
    | malformed bad => cases result
    | finish atEnd => cases result
    | escape u isEscape => cases result; exact unit_progress u
    | other u notEscape => cases result

theorem local_first_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ r o, turtle.local_first bytes position = .ok r ∧ LocalFirst bytes.val position.val o ∧
      Agrees (Option.map (·.val)) r o := by
  rw [turtle.local_first]
  obtain ⟨u, run, correct⟩ := unit_total_correct bytes position
  rcases u with (_ | ⟨cp, next⟩) | e
  · exact ⟨.Ok none, .ok none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch], .finish correct, rfl⟩
  · by_cases plx : PlxStart cp.val
    · obtain ⟨r, o, plxRun, plxCorrect, agree⟩ := plx_total_correct bytes cp next
      exact ⟨r, o, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, plx_start_spec, plx, plxRun],
        .plx correct plx plxCorrect, agree⟩
    · by_cases first : LocalFirstChar cp.val
      · exact ⟨.Ok (some next), .ok (some next.val), by simp [run, core.result.Result.Insts.CoreOpsTry.branch,
          plx_start_spec, plx, local_first_char_spec, first], .char correct plx first, rfl⟩
      · exact ⟨.Ok none, .ok none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch,
          plx_start_spec, plx, local_first_char_spec, first], .other correct plx first, rfl⟩
  · exact ⟨.Err e, .error (.MalformedUtf8, position.val), by simp [run, core.result.Result.Insts.CoreOpsTry.branch],
      .malformed correct.1, correct.2⟩

theorem local_first_accepted {bytes : alloc.vec.Vec U8} {position : Usize} {r : Option Nat}
    (found : LocalFirst bytes.val position.val (.ok r)) :
    ∃ v, turtle.local_first bytes position = .ok (.Ok v) ∧ v.map (·.val) = r := by
  rw [turtle.local_first]
  generalize result : (Except.ok r : Except Fault (Option Nat)) = given at found
  cases found with
  | malformed bad => cases result
  | finish atEnd =>
    cases result
    exact ⟨none, by simp [unit_end atEnd, core.result.Result.Insts.CoreOpsTry.branch], rfl⟩
  | plx u isPlx plx =>
    subst result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    obtain ⟨v, plxRun, value⟩ := plx_accepted (show Plx bytes.val cp.val next.val _ by rw [hc, hn]; exact plx)
    exact ⟨v, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, plx_start_spec, hc, isPlx, plxRun], value⟩
  | char u notPlx first =>
    cases result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    exact ⟨some next, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, plx_start_spec, hc, notPlx,
      local_first_char_spec, first], by simp [hn]⟩
  | other u notPlx notFirst =>
    cases result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    exact ⟨none, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, plx_start_spec, hc, notPlx,
      local_first_char_spec, notFirst], rfl⟩

theorem local_first_bound {bs : List U8} {p q : Nat} (found : LocalFirst bs p (.ok (some q))) :
    p < q ∧ q ≤ bs.length := by
  generalize result : (Except.ok (some q) : Except Fault (Option Nat)) = given at found
  cases found with
  | malformed bad => cases result
  | finish atEnd => cases result
  | plx u isPlx plx =>
    subst result
    have := unit_progress u
    have := plx_bound plx
    omega
  | char u notPlx first => cases result; exact unit_progress u
  | other u notPlx notFirst => cases result

/-- The step of a later unit of a localRun name. -/
def stepView : turtle.Local → LocalStep
  | .Name n => .part n.val
  | .Dot n => .dot n.val
  | .End => .stop

theorem not_plx_46 : ¬ PlxStart 46 := by simp [PlxStart]
theorem not_local_char_46 : ¬ LocalChar 46 := by simp [LocalChar, PnChars, PnCharsU, PnBase, AsciiDigit]

theorem local_next_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ r o, turtle.local_next bytes position = .ok r ∧ LocalNext bytes.val position.val o ∧
      Agrees stepView r o := by
  rw [turtle.local_next]
  obtain ⟨u, run, correct⟩ := unit_total_correct bytes position
  rcases u with (_ | ⟨cp, next⟩) | e
  · exact ⟨.Ok .End, .ok .stop, by simp [run, core.result.Result.Insts.CoreOpsTry.branch], .finish correct, rfl⟩
  · by_cases plx : PlxStart cp.val
    · obtain ⟨r, o, plxRun, plxCorrect, agree⟩ := plx_total_correct bytes cp next
      rcases r with (_ | after) | e
      · obtain rfl := agrees_ok agree
        exact ⟨.Ok .End, .ok .stop, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, plx_start_spec, plx,
          turtle.local_plx, plxRun], .plxNone correct plx plxCorrect, rfl⟩
      · obtain rfl := agrees_ok agree
        exact ⟨.Ok (.Name after), .ok (.part after.val), by simp [run, core.result.Result.Insts.CoreOpsTry.branch,
          plx_start_spec, plx, turtle.local_plx, plxRun], .plx correct plx plxCorrect, rfl⟩
      · obtain rfl := agrees_err agree
        exact ⟨.Err e, .error (faultOf e), by simp [run, core.result.Result.Insts.CoreOpsTry.branch, plx_start_spec,
          plx, turtle.local_plx, plxRun], .plxFails correct plx plxCorrect, rfl⟩
    · by_cases isPart : LocalChar cp.val
      · exact ⟨.Ok (.Name next), .ok (.part next.val), by simp [run, core.result.Result.Insts.CoreOpsTry.branch,
          plx_start_spec, plx, local_char_spec, isPart], .char correct plx isPart, rfl⟩
      · by_cases dot : cp.val = 46
        · exact ⟨.Ok (.Dot next), .ok (.dot next.val), by simp [run, core.result.Result.Insts.CoreOpsTry.branch,
            plx_start_spec, plx, local_char_spec, isPart, UScalar.eq_equiv, dot, not_plx_46, not_local_char_46],
            .dot correct plx isPart dot, rfl⟩
        · exact ⟨.Ok .End, .ok .stop, by simp [run, core.result.Result.Insts.CoreOpsTry.branch,
            plx_start_spec, plx, local_char_spec, isPart, UScalar.eq_equiv, dot], .other correct plx isPart dot, rfl⟩
  · exact ⟨.Err e, .error (.MalformedUtf8, position.val), by simp [run, core.result.Result.Insts.CoreOpsTry.branch],
      .malformed correct.1, correct.2⟩

theorem local_next_accepted {bytes : alloc.vec.Vec U8} {position : Usize} {r : LocalStep}
    (found : LocalNext bytes.val position.val (.ok r)) :
    ∃ v, turtle.local_next bytes position = .ok (.Ok v) ∧ stepView v = r := by
  rw [turtle.local_next]
  generalize result : (Except.ok r : Except Fault LocalStep) = given at found
  cases found with
  | malformed bad => cases result
  | finish atEnd =>
    cases result
    exact ⟨.End, by simp [unit_end atEnd, core.result.Result.Insts.CoreOpsTry.branch], rfl⟩
  | plxFails u isPlx plx => cases result
  | plxNone u isPlx plx =>
    cases result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    obtain ⟨v, plxRun, value⟩ := plx_accepted (show Plx bytes.val cp.val next.val _ by rw [hc, hn]; exact plx)
    cases v with
    | none => exact ⟨.End, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, plx_start_spec, hc, isPlx,
        turtle.local_plx, plxRun], rfl⟩
    | some _ => simp at value
  | plx u isPlx plx =>
    cases result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    obtain ⟨v, plxRun, value⟩ := plx_accepted (show Plx bytes.val cp.val next.val _ by rw [hc, hn]; exact plx)
    cases v with
    | none => simp at value
    | some after =>
      simp only [Option.map_some, Option.some.injEq] at value
      exact ⟨.Name after, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, plx_start_spec, hc, isPlx,
        turtle.local_plx, plxRun], by simp [stepView, value]⟩
  | char u notPlx isPart =>
    cases result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    exact ⟨.Name next, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, plx_start_spec, hc, notPlx,
      local_char_spec, isPart], by simp [stepView, hn]⟩
  | dot u notPlx notName isDot =>
    cases result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    exact ⟨.Dot next, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, plx_start_spec, hc, notPlx,
      local_char_spec, notName, UScalar.eq_equiv, isDot, not_plx_46, not_local_char_46], by simp [stepView, hn]⟩
  | other u notPlx notName notDot =>
    cases result
    obtain ⟨cp, next, run, hc, hn⟩ := unit_at u
    exact ⟨.End, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, plx_start_spec, hc, notPlx,
      local_char_spec, notName, UScalar.eq_equiv, notDot], rfl⟩

theorem local_next_part_bound {bs : List U8} {p q : Nat} (found : LocalNext bs p (.ok (.part q))) :
    p < q ∧ q ≤ bs.length := by
  generalize result : (Except.ok (.part q) : Except Fault LocalStep) = given at found
  cases found with
  | malformed bad => cases result
  | finish atEnd => cases result
  | plxFails u isPlx plx => cases result
  | plxNone u isPlx plx => cases result
  | plx u isPlx plx =>
    cases result
    have := unit_progress u
    have := plx_bound plx
    exact ⟨by omega, by omega⟩
  | char u notPlx isPart => cases result; exact unit_progress u
  | dot u notPlx notName isDot => cases result
  | other u notPlx notName notDot => cases result

theorem local_next_dot_bound {bs : List U8} {p q : Nat} (found : LocalNext bs p (.ok (.dot q))) :
    p < q ∧ q ≤ bs.length := by
  generalize result : (Except.ok (.dot q) : Except Fault LocalStep) = given at found
  cases found with
  | malformed bad => cases result
  | finish atEnd => cases result
  | plxFails u isPlx plx => cases result
  | plxNone u isPlx plx => cases result
  | plx u isPlx plx => cases result
  | char u notPlx isPart => cases result
  | dot u notPlx notName isDot => cases result; exact unit_progress u
  | other u notPlx notName notDot => cases result

theorem local_rest_total_correct (bytes : alloc.vec.Vec U8) (position accepted : Usize) :
    ∃ r o, turtle.local_rest bytes position accepted = .ok r ∧
      LocalRest bytes.val position.val accepted.val o ∧ Agrees (·.val) r o := by
  rw [turtle.local_rest]
  obtain ⟨r, o, run, correct, agree⟩ := local_next_total_correct bytes position
  rcases r with (next | next | _) | e
  · obtain rfl := agrees_ok agree
    simp only [stepView] at correct
    have bound := local_next_part_bound correct
    obtain ⟨r2, o2, run2, rest, agree2⟩ := local_rest_total_correct bytes next next
    exact ⟨r2, o2, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, run2], .part correct rest, agree2⟩
  · obtain rfl := agrees_ok agree
    simp only [stepView] at correct
    have bound := local_next_dot_bound correct
    obtain ⟨r2, o2, run2, rest, agree2⟩ := local_rest_total_correct bytes next accepted
    exact ⟨r2, o2, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, run2], .dot correct rest, agree2⟩
  · obtain rfl := agrees_ok agree
    exact ⟨.Ok accepted, .ok accepted.val, by simp [run, core.result.Result.Insts.CoreOpsTry.branch],
      .stop correct, rfl⟩
  · obtain rfl := agrees_err agree
    exact ⟨.Err e, .error (faultOf e), by simp [run, core.result.Result.Insts.CoreOpsTry.branch], .fails correct,
      rfl⟩
termination_by bytes.val.length - position.val
decreasing_by all_goals omega

theorem local_rest_accepted {bytes : alloc.vec.Vec U8} : ∀ {p a : Nat} {r : Except Fault Nat},
    LocalRest bytes.val p a r → ∀ {e : Nat}, r = .ok e → ∀ (position accepted : Usize),
      position.val = p → accepted.val = a →
      ∃ stop : Usize, turtle.local_rest bytes position accepted = .ok (.Ok stop) ∧ stop.val = e := by
  intro p a r rest
  induction rest with
  | fails next => intro e h; cases h
  | stop next =>
    intro e h position accepted hp ha
    cases h
    obtain ⟨v, run, value⟩ := local_next_accepted (show LocalNext bytes.val position.val _ by rw [hp]; exact next)
    cases v with
    | Name _ => simp [stepView] at value
    | Dot _ => simp [stepView] at value
    | End =>
      refine ⟨accepted, ?_, ha⟩
      rw [turtle.local_rest]
      simp [run, core.result.Result.Insts.CoreOpsTry.branch]
  | part next rest ih =>
    intro e h position accepted hp ha
    obtain ⟨v, run, value⟩ := local_next_accepted (show LocalNext bytes.val position.val _ by rw [hp]; exact next)
    cases v with
    | Name q =>
      simp only [stepView, LocalStep.part.injEq] at value
      obtain ⟨stop, again, hs⟩ := ih h q q value value
      refine ⟨stop, ?_, hs⟩
      rw [turtle.local_rest]
      simp [run, core.result.Result.Insts.CoreOpsTry.branch, again]
    | Dot _ => simp [stepView] at value
    | End => simp [stepView] at value
  | dot next rest ih =>
    intro e h position accepted hp ha
    obtain ⟨v, run, value⟩ := local_next_accepted (show LocalNext bytes.val position.val _ by rw [hp]; exact next)
    cases v with
    | Name _ => simp [stepView] at value
    | Dot q =>
      simp only [stepView, LocalStep.dot.injEq] at value
      obtain ⟨stop, again, hs⟩ := ih h q accepted value ha
      refine ⟨stop, ?_, hs⟩
      rw [turtle.local_rest]
      simp [run, core.result.Result.Insts.CoreOpsTry.branch, again]
    | End => simp [stepView] at value

theorem local_rest_bound {bs : List U8} : ∀ {p a e : Nat}, LocalRest bs p a (.ok e) → a ≤ p → p ≤ bs.length →
    a ≤ e ∧ e ≤ bs.length := by
  intro p a e rest
  generalize result : (Except.ok e : Except Fault Nat) = r at rest
  induction rest with
  | fails next => cases result
  | stop next => cases result; intro h1 h2; omega
  | part next rest ih =>
    intro h1 h2
    have bound := local_next_part_bound next
    have := ih result (le_refl _) bound.2
    omega
  | dot next rest ih =>
    intro h1 h2
    have bound := local_next_dot_bound next
    have := ih result (by omega) bound.2
    omega

theorem local_end_total_correct (bytes : alloc.vec.Vec U8) (start : Usize) :
    ∃ r o, turtle.local_end bytes start = .ok r ∧ LocalEnd bytes.val start.val o ∧ Agrees (·.val) r o := by
  rw [turtle.local_end]
  obtain ⟨r, o, run, correct, agree⟩ := local_first_total_correct bytes start
  rcases r with (_ | next) | e
  · obtain rfl := agrees_ok agree
    exact ⟨.Ok start, .ok start.val, by simp [run, core.result.Result.Insts.CoreOpsTry.branch], .none correct, rfl⟩
  · obtain rfl := agrees_ok agree
    obtain ⟨r2, o2, run2, rest, agree2⟩ := local_rest_total_correct bytes next next
    exact ⟨r2, o2, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, run2], .rest correct rest, agree2⟩
  · obtain rfl := agrees_err agree
    exact ⟨.Err e, .error (faultOf e), by simp [run, core.result.Result.Insts.CoreOpsTry.branch], .fails correct,
      rfl⟩

theorem local_end_accepted {bytes : alloc.vec.Vec U8} {start : Usize} {e : Nat}
    (found : LocalEnd bytes.val start.val (.ok e)) :
    ∃ stop : Usize, turtle.local_end bytes start = .ok (.Ok stop) ∧ stop.val = e := by
  rw [turtle.local_end]
  generalize result : (Except.ok e : Except Fault Nat) = given at found
  cases found with
  | fails first => cases result
  | none first =>
    cases result
    obtain ⟨v, run, value⟩ := local_first_accepted first
    cases v with
    | none => exact ⟨start, by simp [run, core.result.Result.Insts.CoreOpsTry.branch], rfl⟩
    | some _ => simp at value
  | rest first rest =>
    subst result
    obtain ⟨v, run, value⟩ := local_first_accepted first
    cases v with
    | none => simp at value
    | some next =>
      simp only [Option.map_some, Option.some.injEq] at value
      obtain ⟨stop, again, hs⟩ := local_rest_accepted rest rfl next next value value
      exact ⟨stop, by simp [run, core.result.Result.Insts.CoreOpsTry.branch, again], hs⟩

theorem local_end_bound {bs : List U8} {p e : Nat} (found : LocalEnd bs p (.ok e)) (inside : p ≤ bs.length) :
    p ≤ e ∧ e ≤ bs.length := by
  generalize result : (Except.ok e : Except Fault Nat) = given at found
  cases found with
  | fails first => cases result
  | none first => cases result; omega
  | rest first rest =>
    subst result
    have := local_first_bound first
    have := local_rest_bound rest (le_refl _) this.2
    omega


/-! ## Copies and constants -/

theorem copy_from_spec (values : alloc.vec.Vec U8) (index : Usize) (out : alloc.vec.Vec U8)
    (inside : index.val ≤ values.val.length) (room : out.val.length + (values.val.length - index.val) ≤ Usize.max) :
    ∃ v, turtle.copy_from values index out = .ok v ∧ v.val = out.val ++ values.val.drop index.val := by
  rw [turtle.copy_from]
  by_cases more : index.val < values.val.length
  · obtain ⟨out1, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out values.val[index.val] (by omega))
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, again, value⟩ := copy_from_spec values next out1 (by omega) (by simp [contents, nextIs]; omega)
    refine ⟨v, by simp [alloc.vec.Vec.len_val, more, vec_index more, vec_index_usize more, push, add, again], ?_⟩
    rw [value, contents, nextIs, List.drop_eq_getElem_cons more]
    simp
  · exact ⟨out, by simp [alloc.vec.Vec.len_val, more], by simp [List.drop_eq_nil_of_le (by omega : values.val.length ≤ index.val)]⟩
termination_by values.val.length - index.val
decreasing_by omega

theorem copy_bytes_spec (values : alloc.vec.Vec U8) : turtle.copy_bytes values = .ok values := by
  obtain ⟨v, run, value⟩ := copy_from_spec values 0#usize (alloc.vec.Vec.new U8) (by simp)
    (by simp)
  have same : v = values := (alloc.vec.Vec.eq_iff v values).mpr (by simpa using value)
  rw [turtle.copy_bytes, run, same]

theorem constant_from_spec (values : Slice U8) (index : Usize) (out : alloc.vec.Vec U8)
    (inside : index.val ≤ values.val.length) (room : out.val.length + (values.val.length - index.val) ≤ Usize.max) :
    ∃ v, turtle.constant_from values index out = .ok v ∧ v.val = out.val ++ values.val.drop index.val := by
  rw [turtle.constant_from]
  by_cases more : index.val < values.val.length
  · obtain ⟨out1, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out values.val[index.val] (by omega))
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, again, value⟩ := constant_from_spec values next out1 (by omega) (by simp [contents, nextIs]; omega)
    refine ⟨v, by simp [Slice.len_val, more, slice_index more, push, add, again], ?_⟩
    rw [value, contents, nextIs, List.drop_eq_getElem_cons more]
    simp
  · exact ⟨out, by simp [Slice.len_val, more], by simp [List.drop_eq_nil_of_le (by omega : values.val.length ≤ index.val)]⟩
termination_by values.val.length - index.val
decreasing_by omega

theorem constant_spec (values : Slice U8) : ∃ v, turtle.constant values = .ok v ∧ v.val = values.val := by
  obtain ⟨v, run, value⟩ := constant_from_spec values 0#usize (alloc.vec.Vec.new U8) (by simp)
    (by simp)
  exact ⟨v, by rw [turtle.constant, run], by simpa using value⟩

theorem rdf_iri_spec (spelling : Slice U8) :
    ∃ v, turtle.rdf_iri spelling = .ok v ∧ v.spelling.val = spelling.val := by
  obtain ⟨v, run, value⟩ := constant_spec spelling
  exact ⟨⟨v⟩, by simp [turtle.rdf_iri, run], value⟩

theorem constant_eq (values : Slice U8) :
    turtle.constant values = .ok (alloc.vec.Vec.from values.val values.property) := by
  obtain ⟨v, run, value⟩ := constant_spec values
  rw [run]
  congr 1
  exact (alloc.vec.Vec.eq_iff _ _).mpr (by simp [value])

theorem rdf_iri_eq (s : Slice U8) : turtle.rdf_iri s = .ok ⟨alloc.vec.Vec.from s.val s.property⟩ := by
  simp [turtle.rdf_iri, constant_eq]

theorem xsd_eq (s : Slice U8) : turtle.xsd s = .ok (.Datatype ⟨alloc.vec.Vec.from s.val s.property⟩) := by
  simp [turtle.xsd, rdf_iri_eq]

@[simp] theorem lift_ok {α : Type} (x : α) : lift x = .ok x := rfl

theorem slice_array {n : Usize} {l : List U8} {h : l.length = n.val} :
    (Array.to_slice (Array.make n l h)).val = l := by
  simp [Array.to_slice]

/-! ## Unescaping, lookup and IRIs -/

theorem before_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) :
    turtle.before bytes index finish = .ok (decide (index.val < finish.val ∧ index.val < bytes.val.length)) := by
  unfold turtle.before
  by_cases h : index.val < finish.val <;> simp [h, alloc.vec.Vec.len_val]

theorem push_limited_spec (out : alloc.vec.Vec U8) (byte : U8) (limit : Usize) :
    ∃ r, turtle.push_limited out byte limit = .ok r ∧
      r.map (·.val) = if out.val.length < limit.val then some (out.val ++ [byte]) else none := by
  unfold turtle.push_limited
  by_cases room : out.val.length < limit.val
  · obtain ⟨out1, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out byte (by have := limit.hBounds; scalar_tac))
    exact ⟨some out1, by simp [alloc.vec.Vec.len_val, room, push], by simp [room, contents]⟩
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, room], by simp [room]⟩

/-- Unescaping the bytes from `index` to `finish` appends `Unescape` of them,
    provided every byte fits the limit. -/
theorem unescape_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (out : alloc.vec.Vec U8) (limit : Usize)
    (inside : index.val ≤ finish.val) (bounded : finish.val ≤ bytes.val.length) :
    ∃ r, turtle.unescape bytes index finish out limit = .ok r ∧
      r.map (·.val) =
        if (Unescape (Span bytes.val index.val finish.val)).length = 0 ∨
            out.val.length + (Unescape (Span bytes.val index.val finish.val)).length ≤ limit.val
        then some (out.val ++ Unescape (Span bytes.val index.val finish.val)) else none := by
  rw [turtle.unescape]
  by_cases more : index.val < finish.val
  · have inBytes : index.val < bytes.val.length := by omega
    have spanCons : Span bytes.val index.val finish.val =
        bytes.val[index.val] :: Span bytes.val (index.val + 1) finish.val := by
      unfold Span
      rw [List.drop_eq_getElem_cons inBytes]
      rw [show finish.val - index.val = (finish.val - (index.val + 1)) + 1 by omega, List.take_succ_cons]
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    -- The byte that is pushed and the index after it.
    have byteRun : ∃ byte after, turtle.local_byte bytes index finish = .ok (byte, after) ∧
        index.val < after.val ∧ after.val ≤ finish.val ∧
        Unescape (Span bytes.val index.val finish.val) = byte :: Unescape (Span bytes.val after.val finish.val) := by
      by_cases slash : bytes.val[index.val].val = 92
      · by_cases escaped : index.val + 1 < finish.val
        · have inBytes2 : index.val + 1 < bytes.val.length := by omega
          obtain ⟨after, add2, afterValue⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := next) (y := 1#usize) (by scalar_tac))
          have afterIs : after.val = index.val + 2 := by simp at afterValue; omega
          refine ⟨bytes.val[index.val + 1], after, ?_, by omega, by omega, ?_⟩
          · simp [turtle.local_byte, vec_index inBytes, vec_index_usize inBytes, UScalar.eq_equiv, slash, add, turtle.escaped_byte,
              before_spec, nextIs, escaped, inBytes2, vec_index (show next.val < bytes.val.length by omega),
              vec_index_usize (show next.val < bytes.val.length by omega), add2]
          · have spanCons2 : Span bytes.val (index.val + 1) finish.val =
                bytes.val[index.val + 1] :: Span bytes.val (index.val + 2) finish.val := by
              unfold Span
              rw [List.drop_eq_getElem_cons inBytes2]
              rw [show finish.val - (index.val + 1) = (finish.val - (index.val + 2)) + 1 by omega, List.take_succ_cons]
            rw [spanCons, spanCons2, afterIs]
            simp [Unescape, slash]
        · refine ⟨92#u8, next, ?_, by omega, by omega, ?_⟩
          · simp [turtle.local_byte, vec_index inBytes, vec_index_usize inBytes, UScalar.eq_equiv, slash, add, turtle.escaped_byte,
              before_spec, nextIs, escaped]
          · have last : Span bytes.val (index.val + 1) finish.val = [] := by
              unfold Span
              rw [show finish.val - (index.val + 1) = 0 by omega]
              simp
            rw [spanCons, last, nextIs, last]
            have : bytes.val[index.val] = 92#u8 := UScalar.eq_of_val_eq (by simpa using slash)
            simp [Unescape, this]
      · refine ⟨bytes.val[index.val], next, ?_, by omega, by omega, ?_⟩
        · simp [turtle.local_byte, vec_index inBytes, vec_index_usize inBytes, UScalar.eq_equiv, slash, add]
        · rw [spanCons, nextIs]
          cases rest : Span bytes.val (index.val + 1) finish.val with
          | nil => simp [Unescape]
          | cons c tail => simp [Unescape, slash]
    obtain ⟨byte, after, localRun, progress, within, unescaped⟩ := byteRun
    obtain ⟨pushed, pushRun, pushValue⟩ := push_limited_spec out byte limit
    by_cases room : out.val.length < limit.val
    · rw [if_pos room] at pushValue
      cases pushed with
      | none => simp at pushValue
      | some out1 =>
        simp only [Option.map_some, Option.some.injEq] at pushValue
        obtain ⟨r, again, value⟩ := unescape_spec bytes after finish out1 limit within bounded
        refine ⟨r, by simp [before_spec, more, inBytes, localRun, pushRun, again], ?_⟩
        rw [value, unescaped, pushValue]
        have cond : (Unescape (Span bytes.val after.val finish.val)).length = 0 ∨
              (out.val ++ [byte]).length + (Unescape (Span bytes.val after.val finish.val)).length ≤ limit.val ↔
            (byte :: Unescape (Span bytes.val after.val finish.val)).length = 0 ∨
              out.val.length + (byte :: Unescape (Span bytes.val after.val finish.val)).length ≤ limit.val := by
          simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]
          omega
        by_cases hc : (byte :: Unescape (Span bytes.val after.val finish.val)).length = 0 ∨
            out.val.length + (byte :: Unescape (Span bytes.val after.val finish.val)).length ≤ limit.val
        · rw [if_pos (cond.mpr hc), if_pos hc]
          simp
        · rw [if_neg (fun h => hc (cond.mp h)), if_neg hc]
    · rw [if_neg room] at pushValue
      cases pushed with
      | none =>
        refine ⟨none, by simp [before_spec, more, inBytes, localRun, pushRun], ?_⟩
        rw [unescaped]
        simp only [List.length_cons]
        rw [if_neg (by omega)]
        rfl
      | some _ => simp at pushValue
  · have empty : Span bytes.val index.val finish.val = [] := by
      unfold Span
      rw [show finish.val - index.val = 0 by omega]
      simp
    exact ⟨some out, by simp [before_spec, more], by simp [empty, Unescape]⟩
termination_by finish.val - index.val
decreasing_by omega

theorem same_span_from_spec (key bytes : alloc.vec.Vec U8) (start index : Usize)
    (inside : index.val ≤ key.val.length) (fits : start.val + key.val.length ≤ bytes.val.length) :
    turtle.same_span_from key bytes start index =
      .ok (decide (key.val.drop index.val = (bytes.val.drop (start.val + index.val)).take (key.val.length - index.val))) := by
  rw [turtle.same_span_from]
  by_cases more : index.val < key.val.length
  · obtain ⟨at_, add, atValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := index) (by scalar_tac))
    have atIs : at_.val = start.val + index.val := by simpa using atValue
    have inBytes : at_.val < bytes.val.length := by omega
    obtain ⟨next, add2, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have shape : (key.val.drop index.val = (bytes.val.drop (start.val + index.val)).take (key.val.length - index.val)) ↔
        (key.val[index.val] = bytes.val[at_.val] ∧
          key.val.drop (index.val + 1) = (bytes.val.drop (start.val + (index.val + 1))).take
            (key.val.length - (index.val + 1))) := by
      rw [List.drop_eq_getElem_cons more, List.drop_eq_getElem_cons (show start.val + index.val < bytes.val.length by omega),
        show key.val.length - index.val = (key.val.length - (index.val + 1)) + 1 by omega, List.take_succ_cons,
        List.cons.injEq]
      simp only [atIs, show start.val + index.val + 1 = start.val + (index.val + 1) by omega]
    by_cases same : key.val[index.val] = bytes.val[at_.val]
    · have again := same_span_from_spec key bytes start next (by omega) fits
      rw [nextIs] at again
      simp [alloc.vec.Vec.len_val, more, vec_index more, vec_index_usize more, add, vec_index inBytes, vec_index_usize inBytes, same, add2, again, shape]
    · simp [alloc.vec.Vec.len_val, more, vec_index more, vec_index_usize more, add, vec_index inBytes, vec_index_usize inBytes, same, shape]
  · simp [alloc.vec.Vec.len_val, more, List.drop_eq_nil_of_le (show key.val.length ≤ index.val by omega),
      show key.val.length - index.val = 0 by omega]
termination_by key.val.length - index.val
decreasing_by omega

theorem same_span_spec (key bytes : alloc.vec.Vec U8) (start finish : Usize)
    (ordered : start.val ≤ finish.val) (bounded : finish.val ≤ bytes.val.length) :
    turtle.same_span key bytes start finish = .ok (decide (key.val = Span bytes.val start.val finish.val)) := by
  unfold turtle.same_span
  obtain ⟨count, sub, countValue⟩ := WP.spec_imp_exists (Usize.sub_spec (x := finish) (y := start) (by scalar_tac))
  have countIs : count.val = finish.val - start.val := countValue.1
  by_cases sameLength : key.val.length = finish.val - start.val
  · have equal : (alloc.vec.Vec.len key) = count := by
      apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len_val, sameLength, countIs]
    rw [same_span_from_spec key bytes start 0#usize (by simp) (by omega)]
    simp [sub, equal, Span, sameLength, UScalar.eq_equiv, countIs]
  · have different : ¬ (alloc.vec.Vec.len key) = count := by
      intro h
      apply sameLength
      have := congrArg UScalar.val h
      simpa [alloc.vec.Vec.len_val, countIs] using this
    simp only [sub, different, if_false, bind_ok]
    have lengths : ¬ key.val = Span bytes.val start.val finish.val := by
      intro h
      apply sameLength
      rw [h]
      simp [Span]
      omega
    simp [lengths]

/-- The prefix declarations by their name and namespace. -/
def declarations (prefixes : List turtle.Prefix) : List (List U8 × List U8) :=
  prefixes.map fun p => (p.«name».val, p.iri.val)

theorem lookup_snoc (ds : List (List U8 × List U8)) (d : List U8 × List U8) (key : List U8) :
    Lookup (ds ++ [d]) key = if d.1 = key then some d.2 else Lookup ds key := by
  unfold Lookup
  by_cases h : d.1 = key <;> simp [List.reverse_append, h]

theorem lookup_spec (prefixes : alloc.vec.Vec turtle.Prefix) (bytes : alloc.vec.Vec U8) (start finish count : Usize)
    (ordered : start.val ≤ finish.val) (bounded : finish.val ≤ bytes.val.length)
    (counted : count.val ≤ prefixes.val.length) :
    ∃ r, turtle.lookup prefixes bytes start finish count = .ok r ∧
      (∀ i, r = some i → i.val < prefixes.val.length) ∧
      (r.bind fun i => prefixes.val[i.val]?).map (fun p => p.iri.val) =
        Lookup (declarations (prefixes.val.take count.val)) (Span bytes.val start.val finish.val) := by
  rw [turtle.lookup]
  by_cases positive : 0 < count.val
  · obtain ⟨last, sub, lastValue⟩ := WP.spec_imp_exists (Usize.sub_spec (x := count) (y := 1#usize) (by scalar_tac))
    have lastIs : last.val = count.val - 1 := by simpa using lastValue.1
    have inside : last.val < prefixes.val.length := by omega
    have takeIs : declarations (prefixes.val.take count.val) =
        declarations (prefixes.val.take last.val) ++ [(prefixes.val[last.val].«name».val, prefixes.val[last.val].iri.val)] := by
      unfold declarations
      rw [show count.val = last.val + 1 by omega, List.take_add_one, List.getElem?_eq_getElem inside]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
    by_cases found : prefixes.val[last.val].«name».val = Span bytes.val start.val finish.val
    · refine ⟨some last, ?_, by intro i h; cases h; exact inside, ?_⟩
      · simp [UScalar.lt_equiv, positive, sub, vec_index inside, vec_index_usize inside,
          same_span_spec _ bytes start finish ordered bounded, found]
      · rw [takeIs, lookup_snoc]
        simp [found, List.getElem?_eq_getElem inside]
    · obtain ⟨r, again, rBound, rValue⟩ := lookup_spec prefixes bytes start finish last ordered bounded (by omega)
      refine ⟨r, ?_, rBound, ?_⟩
      · simp [UScalar.lt_equiv, positive, sub, vec_index inside, vec_index_usize inside,
          same_span_spec _ bytes start finish ordered bounded, found, again]
      · rw [rValue, takeIs, lookup_snoc]
        simp [found]
  · have zero : count.val = 0 := by omega
    exact ⟨none, by simp [UScalar.lt_equiv, positive], by simp, by simp [zero, Lookup, declarations]⟩
termination_by count.val
decreasing_by omega

theorem valid_iri_spec (bytes : alloc.vec.Vec U8) :
    turtle.valid_iri bytes = .ok (decide (AbsoluteIri bytes.val)) := by
  by_cases valid : AbsoluteIri bytes.val
  · have recognized := (Rowl.Iri.validate_iri_accepted_iff bytes).mpr valid
    simp [turtle.valid_iri, recognized, valid]
  · obtain ⟨recognized, run, _⟩ := Rowl.Iri.validate_iri_total_correct bytes
    have notTrue : recognized ≠ .Matched true := by
      intro equal
      subst recognized
      exact valid ((Rowl.Iri.validate_iri_accepted_iff bytes).mp run)
    cases recognized with
    | Matched accepted =>
      cases accepted with
      | true => exact False.elim (notTrue rfl)
      | false => simp [turtle.valid_iri, run, valid]
    | MalformedUtf8 _ => simp [turtle.valid_iri, run, valid]

/-- The IRI or failure of a spelling after its limit check, at `start`. -/
noncomputable def Bounded (limit start : Nat) (spelling : List U8) (next : Nat) : Except Fault (List U8 × Nat) :=
  if limit < spelling.length then .error (.ResourceLimit, start)
  else if AbsoluteIri spelling then .ok (spelling, next) else .error (.InvalidIri, start)

/-- The view of an IRI result. -/
def iriView (pair : rdf.RdfIri × Usize) : List U8 × Nat := (pair.1.spelling.val, pair.2.val)

theorem bounded_iri_spec (spelling : alloc.vec.Vec U8) (start next limit : Usize) :
    ∃ r, turtle.bounded_iri spelling start next limit = .ok r ∧
      Agrees iriView r (Bounded limit.val start.val spelling.val next.val) := by
  unfold turtle.bounded_iri turtle.checked_iri Bounded
  by_cases over : limit.val < spelling.val.length
  · exact ⟨.Err ⟨.ResourceLimit, start⟩, by simp [alloc.vec.Vec.len_val, over, error_spec], by simp [over, Agrees, faultOf]⟩
  · by_cases valid : AbsoluteIri spelling.val
    · exact ⟨.Ok (⟨spelling⟩, next), by simp [alloc.vec.Vec.len_val, over, valid_iri_spec, valid],
        by simp [over, valid, Agrees, iriView]⟩
    · exact ⟨.Err ⟨.InvalidIri, start⟩, by simp [alloc.vec.Vec.len_val, over, valid_iri_spec, valid, error_spec],
        by simp [over, valid, Agrees, faultOf]⟩


theorem word_injective {a b : List U8} (same : Rowl.References.Word a = Rowl.References.Word b) : a = b := by
  unfold Rowl.References.Word at same
  exact List.map_injective_iff.mpr (fun x y h => UScalar.eq_of_val_eq h) same

theorem bounded_ok {limit start : Nat} {spelling : List U8} {next : Nat}
    (fits : spelling.length ≤ limit) (valid : AbsoluteIri spelling) :
    Bounded limit start spelling next = .ok (spelling, next) := by
  unfold Bounded
  rw [if_neg (by omega), if_pos valid]

theorem bounded_accepted {spelling : alloc.vec.Vec U8} {start next limit : Usize}
    (fits : spelling.val.length ≤ limit.val) (valid : AbsoluteIri spelling.val) :
    ∃ iri stop, turtle.bounded_iri spelling start next limit = .ok (.Ok (iri, stop)) ∧
      iri.spelling.val = spelling.val ∧ stop.val = next.val := by
  obtain ⟨r, run, agree⟩ := bounded_iri_spec spelling start next limit
  rw [bounded_ok fits valid] at agree
  rcases r with ⟨iri, stop⟩ | e
  · simp only [Agrees, iriView, Prod.mk.injEq] at agree
    exact ⟨iri, stop, run, agree.1, agree.2⟩
  · exact False.elim agree

theorem prefixed_total_correct (bytes : alloc.vec.Vec U8) (start colon : Usize)
    (prefixes : alloc.vec.Vec turtle.Prefix) (limit : Usize)
    (found : PrefixColon bytes.val start.val (.ok (some colon.val))) :
    ∃ r o, turtle.prefixed bytes start colon prefixes limit = .ok r ∧
      Prefixed bytes.val (declarations prefixes.val) limit.val start.val colon.val o ∧ Agrees iriView r o := by
  have bound := prefix_colon_bound found
  unfold turtle.prefixed
  obtain ⟨entry, lookupRun, entryBound, entryValue⟩ := lookup_spec prefixes bytes start colon
    (alloc.vec.Vec.len prefixes) bound.1 (by omega) (by simp [alloc.vec.Vec.len_val])
  rw [show (alloc.vec.Vec.len prefixes).val = prefixes.val.length by simp [alloc.vec.Vec.len_val],
    List.take_length] at entryValue
  cases entry with
  | none =>
    exact ⟨.Err ⟨.UndefinedPrefix, start⟩, .error (.UndefinedPrefix, start.val),
      by simp [lookupRun, error_spec], .undefined (by simpa using entryValue.symm), rfl⟩
  | some i =>
    have inside := entryBound i rfl
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := colon) (y := 1#usize)
      (by have := bytes.property; scalar_tac))
    have nextIs : next.val = colon.val + 1 := by simpa using nextValue
    have namespaceIs : Lookup (declarations prefixes.val) (Span bytes.val start.val colon.val) =
        some (prefixes.val[i.val]).iri.val := by
      rw [← entryValue]
      simp [List.getElem?_eq_getElem inside]
    obtain ⟨r, o, localRun, localCorrect, agree⟩ := local_end_total_correct bytes next
    have localCorrect' : ∀ o', LocalEnd bytes.val next.val o' → LocalEnd bytes.val (colon.val + 1) o' := by
      intro o' h; rw [← nextIs]; exact h
    rcases r with stop | e
    · obtain rfl := agrees_ok agree
      have stopBound := local_end_bound localCorrect (by omega)
      obtain ⟨spelling, unescapeRun, spellingValue⟩ := unescape_spec bytes next stop (prefixes.val[i.val]).iri limit
        stopBound.1 stopBound.2
      rw [nextIs] at spellingValue
      cases spelling with
      | none =>
        refine ⟨.Err ⟨.ResourceLimit, start⟩, .error (.ResourceLimit, start.val), ?_, ?_, rfl⟩
        · simp [lookupRun, add, localRun, core.result.Result.Insts.CoreOpsTry.branch, vec_index inside,
            vec_index_usize inside, copy_bytes_spec, unescapeRun, error_spec]
        · apply Prefixed.tooLong namespaceIs (localCorrect' _ localCorrect)
          split_ifs at spellingValue with fits
          · simp at spellingValue
          · simp only [List.length_append]
            omega
      | some value =>
        simp only [Option.map_some] at spellingValue
        split_ifs at spellingValue with fits
        · simp only [Option.some.injEq] at spellingValue
          obtain ⟨r, boundedRun, agree⟩ := bounded_iri_spec value start stop limit
          refine ⟨r, Bounded limit.val start.val value.val stop.val, ?_, ?_, agree⟩
          · simp [lookupRun, add, localRun, core.result.Result.Insts.CoreOpsTry.branch, vec_index inside,
              vec_index_usize inside, copy_bytes_spec, unescapeRun, boundedRun]
          · rw [spellingValue]
            unfold Bounded
            split_ifs with over valid
            · exact .tooLong namespaceIs (localCorrect' _ localCorrect) over
            · exact .iri namespaceIs (localCorrect' _ localCorrect) (by omega) valid
            · exact .invalid namespaceIs (localCorrect' _ localCorrect) (by omega) valid
    · obtain rfl := agrees_err agree
      exact ⟨.Err e, .error (faultOf e), by simp [lookupRun, add, localRun, core.result.Result.Insts.CoreOpsTry.branch],
        .localFails namespaceIs (localCorrect' _ localCorrect), rfl⟩

theorem prefixed_accepted {bytes : alloc.vec.Vec U8} {start colon : Usize}
    {prefixes : alloc.vec.Vec turtle.Prefix} {limit : Usize}
    (found : PrefixColon bytes.val start.val (.ok (some colon.val))) {v : List U8} {n : Nat}
    (named : Prefixed bytes.val (declarations prefixes.val) limit.val start.val colon.val (.ok (v, n))) :
    ∃ iri stop, turtle.prefixed bytes start colon prefixes limit = .ok (.Ok (iri, stop)) ∧
      iri.spelling.val = v ∧ stop.val = n := by
  have bound := prefix_colon_bound found
  generalize result : (Except.ok (v, n) : Except Fault (List U8 × Nat)) = given at named
  cases named with
  | undefined _ => cases result
  | localFails _ _ => cases result
  | tooLong _ _ _ => cases result
  | invalid _ _ _ _ => cases result
  | @iri ns e hLookup localRun fits isIri =>
    cases result
    unfold turtle.prefixed
    obtain ⟨entry, lookupRun, entryBound, entryValue⟩ := lookup_spec prefixes bytes start colon
      (alloc.vec.Vec.len prefixes) bound.1 (by omega) (by simp [alloc.vec.Vec.len_val])
    rw [show (alloc.vec.Vec.len prefixes).val = prefixes.val.length by simp [alloc.vec.Vec.len_val],
      List.take_length, hLookup] at entryValue
    cases entry with
    | none => simp at entryValue
    | some i =>
      have inside := entryBound i rfl
      simp only [Option.bind_some, List.getElem?_eq_getElem inside, Option.map_some, Option.some.injEq] at entryValue
      obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := colon) (y := 1#usize)
        (by have := bytes.property; scalar_tac))
      have nextIs : next.val = colon.val + 1 := by simpa using nextValue
      obtain ⟨stop, localExec, stopValue⟩ := local_end_accepted (show LocalEnd bytes.val next.val _ by
        rw [nextIs]; exact localRun)
      have stopBound := local_end_bound (show LocalEnd bytes.val next.val (.ok stop.val) by
        rw [nextIs, stopValue]; exact localRun) (by omega)
      obtain ⟨spelling, unescapeRun, spellingValue⟩ := unescape_spec bytes next stop (prefixes.val[i.val]).iri limit
        stopBound.1 stopBound.2
      rw [nextIs, stopValue, entryValue, if_pos (Or.inr (by simpa using fits))] at spellingValue
      cases spelling with
      | none => simp at spellingValue
      | some value =>
        simp only [Option.map_some, Option.some.injEq] at spellingValue
        obtain ⟨iri, s, boundedRun, iriValue, sValue⟩ := bounded_accepted (spelling := value) (start := start)
          (next := stop) (limit := limit) (by rw [spellingValue]; exact fits) (by rw [spellingValue]; exact isIri)
        refine ⟨iri, s, ?_, by rw [iriValue, spellingValue], by rw [sValue, stopValue]⟩
        simp [lookupRun, add, localExec, core.result.Result.Insts.CoreOpsTry.branch, vec_index inside, vec_index_usize inside,
          copy_bytes_spec, unescapeRun, boundedRun]

/-- A prefixed name ends after its colon and before the end. -/
theorem prefixed_bound {bs : List U8} {prefixes : List (List U8 × List U8)} {limit start colon : Nat}
    {v : List U8} {n : Nat} (named : Prefixed bs prefixes limit start colon (.ok (v, n))) (inside : colon < bs.length) :
    colon < n ∧ n ≤ bs.length := by
  generalize result : (Except.ok (v, n) : Except Fault (List U8 × Nat)) = given at named
  cases named with
  | undefined _ => cases result
  | localFails _ _ => cases result
  | tooLong _ _ _ => cases result
  | invalid _ _ _ _ => cases result
  | iri hLookup localRun fits isIri =>
    cases result
    have := local_end_bound localRun (by omega)
    omega

/-- The reader's view of a resolution. -/
theorem resolve_view (base reference : alloc.vec.Vec U8) :
    ∃ result, references.resolve base reference = .ok result ∧
      (∀ v, result = some v → Resolves base.val reference.val v.val) ∧
      (result = none → ∀ t, ¬ Resolves base.val reference.val t) := by
  obtain ⟨result, run, value⟩ := Rowl.References.resolve_total_correct base reference
  refine ⟨result, run, ?_, ?_⟩
  · intro v h
    subst h
    split_ifs at value with small
    · exact ⟨small.1, small.2, by simpa using value.symm⟩
    · simp at value
  · intro h t resolves
    subst h
    obtain ⟨small1, small2, resolved⟩ := resolves
    rw [if_pos ⟨small1, small2⟩] at value
    simp [resolved] at value

theorem iri_ref_total_correct (bytes : alloc.vec.Vec U8) (start : Usize) (base : alloc.vec.Vec U8) (limit : Usize) :
    ∃ r o, turtle.iri_ref bytes start base limit = .ok r ∧
      IriRef bytes.val base.val limit.val start.val o ∧ Agrees iriView r o := by
  unfold turtle.iri_ref
  obtain ⟨token, tokenRun, tokenCorrect⟩ := Rowl.NTriples.quoted_total_correct bytes start true limit
  cases token with
  | Err e =>
    refine ⟨.Err ⟨KindOf e.kind, e.offset⟩, .error (lifted e), ?_, .token ⟨start, rfl, e, tokenCorrect, rfl⟩, rfl⟩
    simp [turtle.quoted_iri, tokenRun, lift_spec, core.result.Result.Insts.CoreOpsTry.branch]
  | Ok pair =>
    obtain ⟨reference, next⟩ := pair
    obtain ⟨quotedToken, fits⟩ := tokenCorrect
    have quoted : QuotedAt bytes.val true start.val reference.val next.val := ⟨start, next, rfl, rfl, quotedToken⟩
    obtain ⟨isRef, refRun, refIff⟩ := Rowl.References.is_reference_total_correct reference
    by_cases isReference : IsReference reference.val
    · have refTrue : isRef = true := refIff.mpr isReference
      obtain ⟨resolved, resolveRun, resolvedSome, resolvedNone⟩ := resolve_view base reference
      cases resolved with
      | none =>
        refine ⟨.Err ⟨.InvalidIri, start⟩, .error (.InvalidIri, start.val), ?_,
          .unresolved quoted fits isReference (resolvedNone rfl), rfl⟩
        simp [turtle.quoted_iri, tokenRun, core.result.Result.Insts.CoreOpsTry.branch, refRun, refTrue, resolveRun,
          error_spec]
      | some spelling =>
        have resolves := resolvedSome spelling rfl
        obtain ⟨r, boundedRun, agree⟩ := bounded_iri_spec spelling start next limit
        refine ⟨r, Bounded limit.val start.val spelling.val next.val, ?_, ?_, agree⟩
        · simp [turtle.quoted_iri, tokenRun, core.result.Result.Insts.CoreOpsTry.branch, refRun, refTrue,
            resolveRun, boundedRun]
        · unfold Bounded
          split_ifs with over valid
          · exact .tooLong quoted fits isReference resolves over
          · exact .iri quoted fits isReference resolves (by omega) valid
          · exact .invalid quoted fits isReference resolves (by omega) valid
    · have refFalse : isRef = false := by
        cases isRef with
        | false => rfl
        | true => exact False.elim (isReference (refIff.mp rfl))
      refine ⟨.Err ⟨.InvalidIri, start⟩, .error (.InvalidIri, start.val), ?_,
        .notReference quoted fits isReference, rfl⟩
      simp [turtle.quoted_iri, tokenRun, core.result.Result.Insts.CoreOpsTry.branch, refRun, refFalse, error_spec]

theorem limit_bound (limit : Usize) : limit.val ≤ Usize.max := by scalar_tac

theorem iri_ref_accepted {bytes : alloc.vec.Vec U8} {start : Usize} {base : alloc.vec.Vec U8} {limit : Usize}
    {v : List U8} {n : Nat} (found : IriRef bytes.val base.val limit.val start.val (.ok (v, n))) :
    ∃ iri stop, turtle.iri_ref bytes start base limit = .ok (.Ok (iri, stop)) ∧
      iri.spelling.val = v ∧ stop.val = n := by
  generalize result : (Except.ok (v, n) : Except Fault (List U8 × Nat)) = given at found
  cases found with
  | token _ => cases result
  | notReference _ _ _ => cases result
  | unresolved _ _ _ _ => cases result
  | tooLong _ _ _ _ _ => cases result
  | invalid _ _ _ _ _ _ => cases result
  | @iri ref q t quoted fits isReference resolves short isIri =>
    cases result
    unfold turtle.iri_ref
    obtain ⟨s, stop, hs, hstop, token⟩ := quoted
    have sameStart : s = start := UScalar.eq_of_val_eq hs
    subst sameStart
    let reference : alloc.vec.Vec U8 := alloc.vec.Vec.from ref (by have := limit_bound limit; omega)
    have refVal : reference.val = ref := alloc.vec.Vec.from_val _ _
    have quotedRun := (Rowl.NTriples.quoted_accepted_iff bytes s stop true limit reference).mpr
      ⟨by rw [refVal]; exact token, by rw [refVal]; exact fits⟩
    obtain ⟨isRef, refRun, refIff⟩ := Rowl.References.is_reference_total_correct reference
    have refTrue : isRef = true := refIff.mpr (by rw [refVal]; exact isReference)
    obtain ⟨resolved, resolveRun, resolvedSome, resolvedNone⟩ := resolve_view base reference
    cases resolved with
    | none => exact False.elim (resolvedNone rfl v (by rw [refVal]; exact resolves))
    | some spelling =>
      have resolves' := resolvedSome spelling rfl
      rw [refVal] at resolves'
      have same : spelling.val = v := word_injective (Option.some.inj (resolves'.2.2.symm.trans resolves.2.2))
      obtain ⟨iri, s', boundedRun, iriValue, sValue⟩ := bounded_accepted (spelling := spelling) (start := s)
        (next := stop) (limit := limit) (by rw [same]; exact short) (by rw [same]; exact isIri)
      exact ⟨iri, s', by simp [turtle.quoted_iri, quotedRun, core.result.Result.Insts.CoreOpsTry.branch, refRun,
        refTrue, resolveRun, boundedRun], by rw [iriValue, same], by rw [sValue, hstop]⟩

theorem iri_ref_bound {bs base : List U8} {limit start : Nat} {v : List U8} {n : Nat}
    (found : IriRef bs base limit start (.ok (v, n))) : start < n ∧ n ≤ bs.length := by
  generalize result : (Except.ok (v, n) : Except Fault (List U8 × Nat)) = given at found
  cases found with
  | token _ => cases result
  | notReference _ _ _ => cases result
  | unresolved _ _ _ _ => cases result
  | tooLong _ _ _ _ _ => cases result
  | invalid _ _ _ _ _ _ => cases result
  | iri quoted fits isReference resolves short isIri =>
    cases result
    obtain ⟨s, stop, hs, hstop, token⟩ := quoted
    have := Rowl.NTriples.quoted_token_progress token
    omega

theorem iri_total_correct (bytes : alloc.vec.Vec U8) (start : Usize) (base : alloc.vec.Vec U8)
    (prefixes : alloc.vec.Vec turtle.Prefix) (limit : Usize) :
    ∃ r o, turtle.iri bytes start base prefixes limit = .ok r ∧
      IriAt bytes.val base.val (declarations prefixes.val) limit.val start.val o ∧ Agrees iriView r o := by
  unfold turtle.iri
  by_cases angle : ByteIs bytes.val start.val 60
  · obtain ⟨r, o, run, correct, agree⟩ := iri_ref_total_correct bytes start base limit
    exact ⟨r, o, by simp [byte_is_spec, angle, run], .ref angle correct, agree⟩
  · obtain ⟨r, o, colonRun, colonCorrect, agree⟩ := prefix_colon_total_correct bytes start
    rcases r with (_ | colon) | e <;> rcases o with f | (_ | c) <;> simp only [Agrees] at agree
    all_goals try (simp at agree; done)
    · exact ⟨.Err ⟨.ExpectedIri, start⟩, .error (.ExpectedIri, start.val), by simp [byte_is_spec, angle, colonRun,
        core.result.Result.Insts.CoreOpsTry.branch, error_spec], .missing angle colonCorrect, rfl⟩
    · simp only [Option.map_some, Option.some.injEq] at agree
      subst agree
      obtain ⟨r, o, run, correct, agree⟩ := prefixed_total_correct bytes start colon prefixes limit colonCorrect
      exact ⟨r, o, by simp [byte_is_spec, angle, colonRun, core.result.Result.Insts.CoreOpsTry.branch, run],
        .prefixed angle colonCorrect correct, agree⟩
    · exact ⟨.Err e, .error f, by simp [byte_is_spec, angle, colonRun, core.result.Result.Insts.CoreOpsTry.branch],
        .colonFails angle colonCorrect, agree⟩

theorem iri_accepted {bytes : alloc.vec.Vec U8} {start : Usize} {base : alloc.vec.Vec U8}
    {prefixes : alloc.vec.Vec turtle.Prefix} {limit : Usize} {v : List U8} {n : Nat}
    (found : IriAt bytes.val base.val (declarations prefixes.val) limit.val start.val (.ok (v, n))) :
    ∃ iri stop, turtle.iri bytes start base prefixes limit = .ok (.Ok (iri, stop)) ∧
      iri.spelling.val = v ∧ stop.val = n := by
  unfold turtle.iri
  generalize result : (Except.ok (v, n) : Except Fault (List U8 × Nat)) = given at found
  cases found with
  | ref angle reference =>
    subst result
    obtain ⟨iri, stop, run, hv, hn⟩ := iri_ref_accepted reference
    exact ⟨iri, stop, by simp [byte_is_spec, angle, run], hv, hn⟩
  | colonFails _ _ => cases result
  | missing _ _ => cases result
  | @prefixed colon r angle colonFound named =>
    subst result
    obtain ⟨c, colonRun, colonValue⟩ := prefix_colon_accepted colonFound
    cases c with
    | none => simp at colonValue
    | some colon' =>
      simp only [Option.map_some, Option.some.injEq] at colonValue
      obtain ⟨iri, stop, run, hv, hn⟩ := prefixed_accepted (bytes := bytes) (start := start) (colon := colon')
        (prefixes := prefixes) (limit := limit) (by rw [colonValue]; exact colonFound) (by rw [colonValue]; exact named)
      exact ⟨iri, stop, by simp [byte_is_spec, angle, colonRun, core.result.Result.Insts.CoreOpsTry.branch, run],
        hv, hn⟩

theorem iri_bound {bs base : List U8} {prefixes : List (List U8 × List U8)} {limit start : Nat} {v : List U8}
    {n : Nat} (found : IriAt bs base prefixes limit start (.ok (v, n))) : start < n ∧ n ≤ bs.length := by
  generalize result : (Except.ok (v, n) : Except Fault (List U8 × Nat)) = given at found
  cases found with
  | ref angle reference => subst result; exact iri_ref_bound reference
  | colonFails _ _ => cases result
  | missing _ _ => cases result
  | prefixed angle colonFound named =>
    subst result
    have colonBound := prefix_colon_bound colonFound
    have := prefixed_bound named colonBound.2
    omega

/-! ## Blank node labels -/

/-- The view of a blank node result. -/
def blankView (pair : rdf.BlankNode × Usize) : Term × Nat := (.blank pair.1.scope.val pair.1.label.val, pair.2.val)

theorem blank_label_total_correct (bytes : alloc.vec.Vec U8) (start : Usize) (scope : alloc.vec.Vec U8)
    (limit : Usize) (inside : start.val < bytes.val.length) :
    ∃ r o, turtle.blank_label bytes start scope limit = .ok r ∧
      BlankLabel bytes.val scope.val limit.val start.val o ∧ Agrees blankView r o := by
  unfold turtle.blank_label
  have bytesBound := bytes.property
  obtain ⟨second, add1, secondValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 1#usize) (by scalar_tac))
  have secondIs : second.val = start.val + 1 := by simpa using secondValue
  by_cases colon : ByteIs bytes.val (start.val + 1) 58
  · have colonInside : start.val + 1 < bytes.val.length := by
      obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp colon
      exact (List.getElem?_eq_some_iff.mp lookup).1
    obtain ⟨third, add2, thirdValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 2#usize) (by scalar_tac))
    have thirdIs : third.val = start.val + 2 := by simpa using thirdValue
    obtain ⟨needed, neededRun, neededCorrect⟩ := needed_total_correct bytes third
    rw [thirdIs] at neededCorrect
    rcases needed with ⟨cp, next⟩ | e
    · by_cases first : LabelFirst cp.val
      · obtain ⟨r, o, tailRun, tail, agree⟩ := name_end_total_correct bytes next next
        rcases r with stop | e
        · obtain rfl := agrees_ok agree
          have bound := name_tail_bound tail (le_refl _) (unit_progress neededCorrect).2
          obtain ⟨copied, copyRun, copyCorrect⟩ := Rowl.NTriples.copy_term_total_correct bytes third stop limit
            ⟨by have := (unit_progress neededCorrect).1; omega, bound.2⟩
          cases copied with
          | Ok label =>
            obtain ⟨fits, value⟩ := copyCorrect
            refine ⟨.Ok (⟨scope, label⟩, stop), .ok (.blank scope.val (Span bytes.val (start.val + 2) stop.val), stop.val),
              ?_, .label colon neededCorrect first tail (by omega), ?_⟩
            · simp [add1, byte_is_spec, secondIs, colon, add2, neededRun, core.result.Result.Insts.CoreOpsTry.branch,
                label_first_spec, first, tailRun, turtle.copied, copyRun, copy_bytes_spec]
            · simp [Agrees, blankView, value, Span, thirdIs]
          | Err e =>
            obtain ⟨over, kind, offset⟩ := copyCorrect
            refine ⟨.Err ⟨KindOf e.kind, e.offset⟩, .error (.ResourceLimit, start.val + 2), ?_,
              .tooLong colon neededCorrect first tail (by omega), ?_⟩
            · simp [add1, byte_is_spec, secondIs, colon, add2, neededRun, core.result.Result.Insts.CoreOpsTry.branch,
                label_first_spec, first, tailRun, turtle.copied, copyRun, lift_spec]
            · simp [Agrees, faultOf, kind, KindOf, offset, thirdIs]
        · obtain rfl := agrees_err agree
          exact ⟨.Err e, .error (faultOf e), by simp [add1, byte_is_spec, secondIs, colon, add2, neededRun,
            core.result.Result.Insts.CoreOpsTry.branch, label_first_spec, first, tailRun],
            .tailFails colon neededCorrect first tail, rfl⟩
      · refine ⟨.Err ⟨.InvalidBlankLabel, third⟩, .error (.InvalidBlankLabel, start.val + 2), ?_,
          .badFirst colon neededCorrect first, by simp [Agrees, faultOf, thirdIs]⟩
        simp [add1, byte_is_spec, secondIs, colon, add2, neededRun, core.result.Result.Insts.CoreOpsTry.branch,
          label_first_spec, first, error_spec]
    · exact ⟨.Err e, .error (faultOf e), by simp [add1, byte_is_spec, secondIs, colon, add2, neededRun,
        core.result.Result.Insts.CoreOpsTry.branch], .missing colon neededCorrect, rfl⟩
  · refine ⟨.Err ⟨.InvalidBlankLabel, start⟩, .error (.InvalidBlankLabel, start.val), ?_, .noColon colon, rfl⟩
    simp [add1, byte_is_spec, secondIs, colon, error_spec]

theorem blank_label_accepted {bytes : alloc.vec.Vec U8} {start : Usize} {scope : alloc.vec.Vec U8}
    {limit : Usize} {t : Term} {n : Nat}
    (found : BlankLabel bytes.val scope.val limit.val start.val (.ok (t, n))) :
    ∃ node stop, turtle.blank_label bytes start scope limit = .ok (.Ok (node, stop)) ∧
      blankView (node, stop) = (t, n) := by
  generalize result : (Except.ok (t, n) : Except Fault (Term × Nat)) = given at found
  cases found with
  | noColon _ => cases result
  | missing _ _ => cases result
  | badFirst _ _ _ => cases result
  | tailFails _ _ _ _ => cases result
  | tooLong _ _ _ _ _ => cases result
  | @label c q e colon u first tail fits =>
    cases result
    unfold turtle.blank_label
    have bytesBound := bytes.property
    have colonInside : start.val + 1 < bytes.val.length := by
      obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp colon
      exact (List.getElem?_eq_some_iff.mp lookup).1
    obtain ⟨second, add1, secondValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 1#usize) (by scalar_tac))
    have secondIs : second.val = start.val + 1 := by simpa using secondValue
    obtain ⟨third, add2, thirdValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 2#usize) (by scalar_tac))
    have thirdIs : third.val = start.val + 2 := by simpa using thirdValue
    obtain ⟨cp, next, neededRun, hc, hn⟩ := needed_at (show Unit bytes.val third.val _ _ by rw [thirdIs]; exact u)
    obtain ⟨stop, tailRun, hs⟩ := name_end_accepted tail rfl next next hn hn
    have bound := name_tail_bound tail (le_refl _) (unit_progress u).2
    obtain ⟨copied, copyRun, copyCorrect⟩ := Rowl.NTriples.copy_term_total_correct bytes third stop limit
      ⟨by have := (unit_progress u).1; omega, by omega⟩
    cases copied with
    | Ok label =>
      obtain ⟨_, value⟩ := copyCorrect
      refine ⟨⟨scope, label⟩, stop, ?_, ?_⟩
      · simp [add1, byte_is_spec, secondIs, colon, add2, neededRun, core.result.Result.Insts.CoreOpsTry.branch,
          label_first_spec, hc, first, tailRun, turtle.copied, copyRun, copy_bytes_spec]
      · simp [blankView, value, Span, thirdIs, hs]
    | Err _ =>
      obtain ⟨over, _, _⟩ := copyCorrect
      omega

theorem blank_label_bound {bs scope : List U8} {limit start : Nat} {t : Term} {n : Nat}
    (found : BlankLabel bs scope limit start (.ok (t, n))) : start < n ∧ n ≤ bs.length := by
  generalize result : (Except.ok (t, n) : Except Fault (Term × Nat)) = given at found
  cases found with
  | noColon _ => cases result
  | missing _ _ => cases result
  | badFirst _ _ _ => cases result
  | tailFails _ _ _ _ => cases result
  | tooLong _ _ _ _ _ => cases result
  | label colon u first tail fits =>
    cases result
    have progress := unit_progress u
    have := name_tail_bound tail (le_refl _) progress.2
    omega


/-! ## Strings -/

/-- The view of a string result. -/
def stringView (pair : alloc.vec.Vec U8 × Usize) : List U8 × Nat := (pair.1.val, pair.2.val)

/-- The bytes of a canonical encoding are the UTF-8 spelling of its scalar. -/
theorem encode_utf8 {x : Nat} {enc : encoding.Encoded} (correct : Rowl.Encoding.EncodeCorrect x (some enc)) :
    (Rowl.Encoding.Bytes enc).map (·.val) = Rowl.IriResolution.utf8 x := by
  cases enc with
  | One a =>
    obtain ⟨small, value⟩ := correct
    simp [Rowl.Encoding.Bytes, Rowl.IriResolution.utf8, value, show x < 128 by omega]
  | Two a b =>
    obtain ⟨pair, value⟩ := correct
    simp only [Rowl.Unicode.Pair, Rowl.Unicode.Tail] at pair
    simp only [Rowl.Unicode.value2] at value
    have h1 : ¬ x < 128 := by omega
    have h2 : x < 2048 := by omega
    simp only [Rowl.Encoding.Bytes, List.map_cons, List.map_nil, Rowl.IriResolution.utf8, h1, h2, if_false, if_true,
      List.cons.injEq, and_true]
    exact ⟨by omega, by omega⟩
  | Three a b c =>
    obtain ⟨triple, value⟩ := correct
    simp only [Rowl.Unicode.Triple, Rowl.Unicode.Tail] at triple
    simp only [Rowl.Unicode.value3] at value
    have h1 : ¬ x < 128 := by omega
    have h2 : ¬ x < 2048 := by omega
    have h3 : x < 65536 := by omega
    simp only [Rowl.Encoding.Bytes, List.map_cons, List.map_nil, Rowl.IriResolution.utf8, h1, h2, h3, if_false,
      if_true, List.cons.injEq, and_true]
    exact ⟨by omega, by omega, by omega⟩
  | Four a b c d =>
    obtain ⟨quad, value⟩ := correct
    simp only [Rowl.Unicode.Quad, Rowl.Unicode.Tail] at quad
    simp only [Rowl.Unicode.value4] at value
    have h1 : ¬ x < 128 := by omega
    have h2 : ¬ x < 2048 := by omega
    have h3 : ¬ x < 65536 := by omega
    simp only [Rowl.Encoding.Bytes, List.map_cons, List.map_nil, Rowl.IriResolution.utf8, h1, h2, h3, if_false,
      List.cons.injEq, and_true]
    exact ⟨by omega, by omega, by omega, by omega⟩

theorem encode_length {x : Nat} {enc : encoding.Encoded} (correct : Rowl.Encoding.EncodeCorrect x (some enc)) :
    (Rowl.Encoding.Bytes enc).length = (Rowl.IriResolution.utf8 x).length := by
  rw [← encode_utf8 correct, List.length_map]

theorem utf8_short {x : Nat} : (Rowl.IriResolution.utf8 x).length ≤ 4 := by
  unfold Rowl.IriResolution.utf8
  split_ifs <;> simp

/-- A raw character takes as many bytes as its encoding. -/
theorem unit_width {bs : List U8} {p c q : Nat} (u : Unit bs p c q) :
    (Rowl.IriResolution.utf8 c).length = q - p := by
  have spelled := (Rowl.IriResolution.prefix_utf8 u.2.2).1
  have := congrArg List.length spelled
  simp only [List.length_map, List.length_take, List.length_drop] at this
  have := u.2.1
  omega

theorem hex_digits_width {bs : List U8} {s count v r stop : Nat} (digits : HexDigits bs s count v r stop) :
    s + count ≤ stop := by
  induction digits with
  | empty => omega
  | digit unit hex tail ih => have := unit.1; omega

theorem escape_width {bs : List U8} {q : Nat} {cp : U32} {n : Usize}
    (escape : EscapeValue bs false q cp n) {enc : encoding.Encoded}
    (correct : Rowl.Encoding.EncodeCorrect cp.val (some enc)) :
    q < n.val ∧ (Rowl.Encoding.Bytes enc).length ≤ n.val - q ∧ n.val ≤ bs.length := by
  rw [encode_length correct]
  have short := utf8_short (x := cp.val)
  cases escape with
  | four unit scalar digits =>
    have width := hex_digits_width digits
    have progress := Rowl.NTriples.hex_digits_progress digits
    have := unit.1
    rcases progress with ⟨zero, _⟩ | ⟨_, _, bound⟩ <;> omega
  | eight unit scalar digits =>
    have width := hex_digits_width digits
    have progress := Rowl.NTriples.hex_digits_progress digits
    have := unit.1
    rcases progress with ⟨zero, _⟩ | ⟨_, _, bound⟩ <;> omega
  | character _ unit echar =>
    have small : cp.val < 128 := by
      unfold Rowl.NTriples.EcharValue at echar
      split_ifs at echar <;> simp at echar <;> omega
    have := unit.1
    have := unit.2.1
    simp [Rowl.IriResolution.utf8, small]
    omega

theorem add_spec (output : alloc.vec.Vec U8) (value : U32) (limit position : Usize)
    (scalar : Rowl.Encoding.Scalar value.val) (bounded : output.val.length ≤ limit.val) :
    ∃ enc, Rowl.Encoding.EncodeCorrect value.val (some enc) ∧ ∃ r, turtle.add output value limit position = .ok r ∧
      match r with
      | .Ok out => output.val.length + (Rowl.Encoding.Bytes enc).length ≤ limit.val ∧
          out.val = output.val ++ Rowl.Encoding.Bytes enc
      | .Err e => limit.val < output.val.length + (Rowl.Encoding.Bytes enc).length ∧ e = ⟨.ResourceLimit, position⟩ := by
  obtain ⟨encoded, encodeRun, encodeCorrect⟩ := Rowl.Encoding.encode_total_correct value
  cases encoded with
  | none => exact False.elim (encodeCorrect scalar)
  | some enc =>
    refine ⟨enc, encodeCorrect, ?_⟩
    obtain ⟨accepted, after, appendRun, accepted_eq, afterValue, _⟩ :=
      Rowl.NTriples.append_encoded_total_correct output enc limit bounded
    by_cases fits : output.val.length + (Rowl.Encoding.Bytes enc).length ≤ limit.val
    · have yes : accepted = true := by simp [accepted_eq, fits]
      refine ⟨.Ok after, by simp [turtle.add, encodeRun, appendRun, yes], fits, ?_⟩
      rw [afterValue, List.take_of_length_le (by omega)]
    · have no : accepted = false := by simp [accepted_eq, fits]
      exact ⟨.Err ⟨.ResourceLimit, position⟩, by simp [turtle.add, encodeRun, appendRun, no, error_spec], by omega, rfl⟩

theorem single_body_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) (output : alloc.vec.Vec U8)
    (limit : Usize) (bounded : output.val.length ≤ limit.val) :
    ∃ r o, turtle.single_body bytes position output limit = .ok r ∧
      SingleBody bytes.val limit.val position.val output.val o ∧ Agrees stringView r o := by
  rw [turtle.single_body]
  obtain ⟨needed, neededRun, neededCorrect⟩ := needed_total_correct bytes position
  rcases needed with ⟨cp, next⟩ | e
  · by_cases close : cp.val = 39
    · exact ⟨.Ok (output, next), .ok (output.val, next.val), by simp [neededRun,
        core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, close], .close (close ▸ neededCorrect), rfl⟩
    · obtain ⟨item, itemRun, itemCorrect⟩ := Rowl.NTriples.quoted_item_total_correct bytes position cp next false
        neededCorrect
      rcases item with ⟨value, stop⟩ | e
      · have progress := Rowl.NTriples.quoted_item_progress itemCorrect
        have stringItem : StringItem bytes.val position.val value.val stop.val := ⟨value, stop, rfl, rfl, itemCorrect⟩
        obtain ⟨enc, encodeCorrect, added, addRun, addCorrect⟩ := add_spec output value limit position progress.1 bounded
        rcases added with out | e
        · obtain ⟨fits, outValue⟩ := addCorrect
          obtain ⟨r, o, again, recCorrect, agree⟩ := single_body_total_correct bytes stop out limit (by rw [outValue]; simp; omega)
          refine ⟨r, o, ?_, .item neededCorrect close stringItem encodeCorrect fits (by rw [← outValue]; exact recCorrect),
            agree⟩
          simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, close, turtle.string_item,
            itemRun, addRun, again]
        · obtain ⟨over, rfl⟩ := addCorrect
          exact ⟨.Err ⟨.ResourceLimit, position⟩, .error (.ResourceLimit, position.val), by simp [neededRun,
            core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, close, turtle.string_item, itemRun, addRun],
            .tooLong neededCorrect close stringItem encodeCorrect over, rfl⟩
      · exact ⟨.Err ⟨KindOf e.kind, e.offset⟩, .error (lifted e), by simp [neededRun,
          core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, close, turtle.string_item, itemRun, lift_spec],
          .itemFails neededCorrect close ⟨position, rfl, e, itemCorrect, rfl⟩, rfl⟩
  · exact ⟨.Err e, .error (faultOf e), by simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch],
      .missing neededCorrect, rfl⟩
termination_by bytes.val.length - position.val
decreasing_by
  have := (Rowl.NTriples.quoted_item_progress itemCorrect).2
  omega

theorem single_body_accepted {bytes : alloc.vec.Vec U8} {limit : Usize} : ∀ {p : Nat} {v : List U8}
    {r : Except Fault (List U8 × Nat)}, SingleBody bytes.val limit.val p v r → ∀ {w n}, r = .ok (w, n) →
      ∀ (position : Usize) (output : alloc.vec.Vec U8), position.val = p → output.val = v →
      output.val.length ≤ limit.val →
      ∃ out stop, turtle.single_body bytes position output limit = .ok (.Ok (out, stop)) ∧
        out.val = w ∧ stop.val = n := by
  intro p v r body
  induction body with
  | missing _ => intro w n h; cases h
  | close u =>
    intro w n h position output hp hv bounded
    cases h
    obtain ⟨cp, next, neededRun, hc, hn⟩ := needed_at (show Unit bytes.val position.val _ _ by rw [hp]; exact u)
    refine ⟨output, next, ?_, hv, hn⟩
    rw [turtle.single_body]
    simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, hc]
  | itemFails _ _ _ => intro w n h; cases h
  | tooLong _ _ _ _ _ => intro w n h; cases h
  | @item p v c q x m enc r u notClose stringItem encodeCorrect fits rest ih =>
    intro w n h position output hp hv bounded
    obtain ⟨cp, next, neededRun, hc, hn⟩ := needed_at (show Unit bytes.val position.val _ _ by rw [hp]; exact u)
    obtain ⟨value, stop, hx, hm, item⟩ := stringItem
    have itemRun := (Rowl.NTriples.quoted_item_accepted_iff bytes position cp value next stop false
      (show Unit bytes.val position.val cp.val next.val by rw [hp, hc, hn]; exact u)).mpr (by rw [hp]; exact item)
    have progress := Rowl.NTriples.quoted_item_progress item
    obtain ⟨enc', encodeCorrect', added, addRun, addCorrect⟩ := add_spec output value limit position progress.1 bounded
    have same := Rowl.Encoding.encoded_unique value.val enc' enc encodeCorrect' (by rw [hx]; exact encodeCorrect)
    subst same
    rcases added with out | e
    · obtain ⟨_, outValue⟩ := addCorrect
      obtain ⟨final, finish, again, hw, hn'⟩ := ih h stop out hm (by rw [outValue, hv])
        (by rw [outValue]; simp; rw [hv]; omega)
      refine ⟨final, finish, ?_, hw, hn'⟩
      rw [turtle.single_body]
      have notClose' : ¬ cp.val = 39 := by rw [hc]; exact notClose
      simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, notClose', turtle.string_item,
        itemRun, addRun, again]
    · obtain ⟨over, _⟩ := addCorrect
      rw [hv] at over
      omega

theorem triple_quote_spec (bytes : alloc.vec.Vec U8) (position : Usize) (quote : U8) :
    turtle.triple_quote bytes position quote = .ok (decide (TripleQuote bytes.val position.val quote.val)) := by
  unfold turtle.triple_quote TripleQuote
  have bytesBound := bytes.property
  by_cases first : ByteIs bytes.val position.val quote.val
  · have inside : position.val < bytes.val.length := by
      obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp first
      exact (List.getElem?_eq_some_iff.mp lookup).1
    obtain ⟨second, add1, secondValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := position) (y := 1#usize)
      (by scalar_tac))
    have secondIs : second.val = position.val + 1 := by simpa using secondValue
    by_cases two : ByteIs bytes.val (position.val + 1) quote.val
    · have inside2 : position.val + 1 < bytes.val.length := by
        obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp two
        exact (List.getElem?_eq_some_iff.mp lookup).1
      obtain ⟨third, add2, thirdValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := position) (y := 2#usize)
        (by scalar_tac))
      have thirdIs : third.val = position.val + 2 := by simpa using thirdValue
      simp [byte_is_spec, first, add1, secondIs, two, add2, thirdIs]
    · simp [byte_is_spec, first, add1, secondIs, two]
  · simp [byte_is_spec, first]

theorem triple_quote_inside {bs : List U8} {p quote : Nat} (three : TripleQuote bs p quote) : p + 2 < bs.length := by
  obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp three.2.2
  exact (List.getElem?_eq_some_iff.mp lookup).1

/-- The view of an item: its scalar and the position after it. -/
theorem long_item_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ r, turtle.long_item bytes position = .ok r ∧
      ∀ value next, r = .Ok (value, next) → LongItem bytes.val position.val value.val next.val ∧
        Rowl.Encoding.Scalar value.val := by
  unfold turtle.long_item
  obtain ⟨needed, neededRun, neededCorrect⟩ := needed_total_correct bytes position
  rcases needed with ⟨cp, next⟩ | e
  · by_cases slash : cp.val = 92
    · obtain ⟨escaped, escapeRun, escapeCorrect⟩ := Rowl.NTriples.escape_total_correct bytes position next false
      refine ⟨match escaped with
        | .Ok pair => .Ok pair
        | .Err e => .Err ⟨KindOf e.kind, e.offset⟩, ?_, ?_⟩
      · rcases escaped with pair | e <;>
          simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, slash, turtle.string_escape,
            escapeRun, lift_spec]
      · intro value stop h
        rcases escaped with ⟨v, s⟩ | e
        · simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have unit : Unit bytes.val position.val 92 next.val := slash ▸ neededCorrect
          exact ⟨LongItem.escape unit escapeCorrect, (Rowl.NTriples.escape_value_progress escapeCorrect).1⟩
        · simp at h
    · refine ⟨.Ok (cp, next), by simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, slash],
        ?_⟩
      intro value stop h
      simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨LongItem.raw neededCorrect slash, (Rowl.IriResolution.prefix_utf8 neededCorrect.2.2).2⟩
  · exact ⟨.Err e, by simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch], by intro _ _ h; simp at h⟩

theorem long_item_width {bs : List U8} {p x n : Nat} (item : LongItem bs p x n) {enc : encoding.Encoded}
    (correct : Rowl.Encoding.EncodeCorrect x (some enc)) :
    p < n ∧ (Rowl.Encoding.Bytes enc).length ≤ n - p ∧ n ≤ bs.length := by
  cases item with
  | raw u notSlash =>
    have := unit_width u
    have := u.1
    have := u.2.1
    rw [encode_length correct]
    omega
  | escape u escape =>
    have := escape_width escape correct
    have := u.1
    omega

theorem long_item_scalar {bs : List U8} {p x n : Nat} (item : LongItem bs p x n) : Rowl.Encoding.Scalar x := by
  cases item with
  | raw u notSlash => exact (Rowl.IriResolution.prefix_utf8 u.2.2).2
  | escape u escape => exact (Rowl.NTriples.escape_value_progress escape).1

theorem long_item_accepted {bytes : alloc.vec.Vec U8} {position : Usize} {x n : Nat}
    (item : LongItem bytes.val position.val x n) :
    ∃ value next, turtle.long_item bytes position = .ok (.Ok (value, next)) ∧ value.val = x ∧ next.val = n := by
  unfold turtle.long_item
  cases item with
  | raw u notSlash =>
    obtain ⟨cp, next, neededRun, hc, hn⟩ := needed_at u
    refine ⟨cp, next, ?_, hc, hn⟩
    simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, hc, notSlash]
  | @escape q cp n u escape =>
    obtain ⟨slash, next, neededRun, hc, hn⟩ := needed_at u
    have escapeRun := (Rowl.NTriples.escape_accepted_iff bytes position next false cp n).mpr (by rw [hn]; exact escape)
    refine ⟨cp, n, ?_, rfl, rfl⟩
    simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, hc, turtle.string_escape, escapeRun]

theorem long_body_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) (quote : U8) (output : alloc.vec.Vec U8)
    (room : output.val.length ≤ position.val) :
    ∃ r, turtle.long_body bytes position quote output = .ok r ∧
      ∀ v n, r = .Ok (v, n) → LongBody bytes.val quote.val position.val output.val (v.val, n.val) := by
  rw [turtle.long_body]
  have bytesBound := bytes.property
  by_cases close : TripleQuote bytes.val position.val quote.val
  · have inside := triple_quote_inside close
    obtain ⟨after, add, afterValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := position) (y := 3#usize)
      (by scalar_tac))
    have afterIs : after.val = position.val + 3 := by simpa using afterValue
    refine ⟨.Ok (output, after), by simp [triple_quote_spec, close, add], ?_⟩
    intro v n h
    simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [afterIs]
    exact .close close
  · obtain ⟨item, itemRun, itemCorrect⟩ := long_item_total_correct bytes position
    rcases item with ⟨value, next⟩ | e
    · obtain ⟨item, scalar⟩ := itemCorrect value next rfl
      have maxValue : (core.num.Usize.MAX).val = Usize.max := by simp [core.num.Usize.MAX]
      obtain ⟨enc, encodeCorrect, added, addRun, addCorrect⟩ := add_spec output value core.num.Usize.MAX position scalar
        (by rw [maxValue]; exact output.property)
      have width := long_item_width item encodeCorrect
      rcases added with out | e
      · obtain ⟨_, outValue⟩ := addCorrect
        obtain ⟨r, again, recCorrect⟩ := long_body_total_correct bytes next quote out (by rw [outValue]; simp; omega)
        refine ⟨r, by simp [triple_quote_spec, close, itemRun, core.result.Result.Insts.CoreOpsTry.branch, addRun, again],
          ?_⟩
        intro v n h
        exact .item close item encodeCorrect (by rw [← outValue]; exact recCorrect v n h)
      · obtain ⟨over, _⟩ := addCorrect
        rw [maxValue] at over
        omega
    · exact ⟨.Err e, by simp [triple_quote_spec, close, itemRun, core.result.Result.Insts.CoreOpsTry.branch],
        by intro _ _ h; simp at h⟩
termination_by bytes.val.length - position.val
decreasing_by
  have := long_item_width item encodeCorrect
  omega

theorem long_body_accepted {bytes : alloc.vec.Vec U8} {quote : U8} : ∀ {p : Nat} {v : List U8}
    {result : List U8 × Nat}, LongBody bytes.val quote.val p v result →
      ∀ (position : Usize) (output : alloc.vec.Vec U8), position.val = p → output.val = v →
      output.val.length ≤ position.val →
      ∃ out stop, turtle.long_body bytes position quote output = .ok (.Ok (out, stop)) ∧
        out.val = result.1 ∧ stop.val = result.2 := by
  intro p v result body
  induction body with
  | close three =>
    intro position output hp hv room
    have bytesBound := bytes.property
    have inside := triple_quote_inside three
    obtain ⟨after, add, afterValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := position) (y := 3#usize)
      (by scalar_tac))
    have afterIs : after.val = position.val + 3 := by simpa using afterValue
    refine ⟨output, after, ?_, hv, by rw [afterIs, hp]⟩
    rw [turtle.long_body]
    simp [triple_quote_spec, hp, three, add]
  | @item p v x n enc r notClose item encodeCorrect rest ih =>
    intro position output hp hv room
    obtain ⟨value, next, itemRun, hx, hn⟩ := long_item_accepted (show LongItem bytes.val position.val x n by
      rw [hp]; exact item)
    have scalar : Rowl.Encoding.Scalar value.val := by
      rw [hx]
      exact long_item_scalar item
    have maxValue : (core.num.Usize.MAX).val = Usize.max := by simp [core.num.Usize.MAX]
    obtain ⟨enc', encodeCorrect', added, addRun, addCorrect⟩ := add_spec output value core.num.Usize.MAX position scalar
      (by rw [maxValue]; exact output.property)
    have same := Rowl.Encoding.encoded_unique value.val enc' enc encodeCorrect' (by rw [hx]; exact encodeCorrect)
    subst same
    have width := long_item_width item encodeCorrect
    rcases added with out | e
    · obtain ⟨_, outValue⟩ := addCorrect
      obtain ⟨final, finish, again, hw, hn'⟩ := ih next out hn (by rw [outValue, hv])
        (by rw [outValue]; simp; rw [hn]; omega)
      refine ⟨final, finish, ?_, hw, hn'⟩
      rw [turtle.long_body]
      have notClose' : ¬ TripleQuote bytes.val position.val quote.val := by rw [hp]; exact notClose
      simp [triple_quote_spec, notClose', itemRun, core.result.Result.Insts.CoreOpsTry.branch, addRun, again]
    · obtain ⟨over, _⟩ := addCorrect
      rw [maxValue] at over
      have := bytes.property
      omega

theorem long_string_total_correct (bytes : alloc.vec.Vec U8) (start : Usize) (quote : U8) (limit : Usize)
    (three : TripleQuote bytes.val start.val quote.val) :
    ∃ r o, turtle.long_string bytes start quote limit = .ok r ∧
      LongString bytes.val limit.val quote.val start.val o ∧ Agrees stringView r o := by
  unfold turtle.long_string
  have bytesBound := bytes.property
  have inside := triple_quote_inside three
  obtain ⟨body, add, bodyValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 3#usize) (by scalar_tac))
  have bodyIs : body.val = start.val + 3 := by simpa using bodyValue
  obtain ⟨r, longRun, longCorrect⟩ := long_body_total_correct bytes body quote (alloc.vec.Vec.new U8) (by simp)
  rcases r with ⟨value, finish⟩ | e
  · have long := longCorrect value finish rfl
    rw [bodyIs] at long
    by_cases over : limit.val < value.val.length
    · exact ⟨.Err ⟨.ResourceLimit, start⟩, .error (.ResourceLimit, start.val), by simp [add, longRun,
        turtle.bounded_string, alloc.vec.Vec.len_val, over, error_spec], .tooLong long over, rfl⟩
    · exact ⟨.Ok (value, finish), .ok (value.val, finish.val), by simp [add, longRun, turtle.bounded_string,
        alloc.vec.Vec.len_val, over], .long long (by omega), rfl⟩
  · obtain ⟨two, add2, twoValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 2#usize) (by scalar_tac))
    have twoIs : two.val = start.val + 2 := by simpa using twoValue
    refine ⟨.Ok (alloc.vec.Vec.new U8, two), .ok ([], start.val + 2), by simp [add, longRun, add2], ?_,
      by simp [Agrees, stringView, twoIs]⟩
    apply LongString.empty
    intro v n long
    obtain ⟨out, stop, run, _, _⟩ := long_body_accepted long body (alloc.vec.Vec.new U8) bodyIs rfl (by simp)
    rw [longRun] at run
    simp at run

theorem long_string_accepted {bytes : alloc.vec.Vec U8} {start : Usize} {quote : U8} {limit : Usize}
    (three : TripleQuote bytes.val start.val quote.val) {w : List U8} {n : Nat}
    (found : LongString bytes.val limit.val quote.val start.val (.ok (w, n))) :
    ∃ out stop, turtle.long_string bytes start quote limit = .ok (.Ok (out, stop)) ∧ out.val = w ∧ stop.val = n := by
  unfold turtle.long_string
  have bytesBound := bytes.property
  have inside := triple_quote_inside three
  obtain ⟨body, add, bodyValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 3#usize) (by scalar_tac))
  have bodyIs : body.val = start.val + 3 := by simpa using bodyValue
  generalize result : (Except.ok (w, n) : Except Fault (List U8 × Nat)) = given at found
  cases found with
  | tooLong _ _ => cases result
  | long long fits =>
    cases result
    obtain ⟨out, stop, run, hw, hn⟩ := long_body_accepted long body (alloc.vec.Vec.new U8) bodyIs rfl (by simp)
    have hw' : out.val = w := hw
    have notOver : ¬ limit.val < out.val.length := by rw [hw']; omega
    exact ⟨out, stop, by simp [add, run, turtle.bounded_string, alloc.vec.Vec.len_val, notOver], hw, hn⟩
  | empty none =>
    cases result
    obtain ⟨r, longRun, longCorrect⟩ := long_body_total_correct bytes body quote (alloc.vec.Vec.new U8) (by simp)
    rcases r with ⟨value, finish⟩ | e
    · exact False.elim (none _ _ (by rw [← bodyIs]; exact longCorrect value finish rfl))
    · obtain ⟨two, add2, twoValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 2#usize) (by scalar_tac))
      have twoIs : two.val = start.val + 2 := by simpa using twoValue
      exact ⟨alloc.vec.Vec.new U8, two, by simp [add, longRun, add2], rfl, twoIs⟩

@[simp] theorem u8_34 : (34#u8 : U8).val = 34 := rfl
@[simp] theorem u8_39 : (39#u8 : U8).val = 39 := rfl

theorem string_total_correct (bytes : alloc.vec.Vec U8) (start limit : Usize)
    (inside : start.val < bytes.val.length) :
    ∃ r o, turtle.string bytes start limit = .ok r ∧ StringAt bytes.val limit.val start.val o ∧ Agrees stringView r o := by
  unfold turtle.string
  have bytesBound := bytes.property
  by_cases d3 : TripleQuote bytes.val start.val 34
  · obtain ⟨r, o, run, correct, agree⟩ := long_string_total_correct bytes start 34#u8 limit (by simpa using d3)
    exact ⟨r, o, by simp [triple_quote_spec, d3, run], .longDouble d3 (by simpa using correct), agree⟩
  · by_cases s3 : TripleQuote bytes.val start.val 39
    · obtain ⟨r, o, run, correct, agree⟩ := long_string_total_correct bytes start 39#u8 limit (by simpa using s3)
      exact ⟨r, o, by simp [triple_quote_spec, d3, s3, run], .longSingle d3 s3 (by simpa using correct), agree⟩
    · by_cases d1 : ByteIs bytes.val start.val 34
      · obtain ⟨token, tokenRun, tokenCorrect⟩ := Rowl.NTriples.quoted_total_correct bytes start false limit
        cases token with
        | Ok pair =>
          obtain ⟨w, q⟩ := pair
          obtain ⟨tok, fits⟩ := tokenCorrect
          exact ⟨.Ok (w, q), .ok (w.val, q.val), by simp [triple_quote_spec, d3, s3, byte_is_spec, d1,
            turtle.quoted_string, tokenRun], .double d3 s3 d1 ⟨start, q, rfl, rfl, tok⟩ fits, rfl⟩
        | Err e =>
          exact ⟨.Err ⟨KindOf e.kind, e.offset⟩, .error (lifted e), by simp [triple_quote_spec, d3, s3, byte_is_spec, d1,
            turtle.quoted_string, tokenRun, lift_spec], .doubleFails d3 s3 d1 ⟨start, rfl, e, tokenCorrect, rfl⟩, rfl⟩
      · obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 1#usize)
          (by scalar_tac))
        have nextIs : next.val = start.val + 1 := by simpa using nextValue
        obtain ⟨r, o, run, correct, agree⟩ := single_body_total_correct bytes next (alloc.vec.Vec.new U8) limit (by simp)
        exact ⟨r, o, by simp [triple_quote_spec, d3, s3, byte_is_spec, d1, add, run],
          .single d3 s3 d1 (by rw [← nextIs]; simpa using correct), agree⟩

theorem string_accepted {bytes : alloc.vec.Vec U8} {start limit : Usize} (inside : start.val < bytes.val.length)
    {w : List U8} {n : Nat} (found : StringAt bytes.val limit.val start.val (.ok (w, n))) :
    ∃ out stop, turtle.string bytes start limit = .ok (.Ok (out, stop)) ∧ out.val = w ∧ stop.val = n := by
  unfold turtle.string
  have bytesBound := bytes.property
  generalize result : (Except.ok (w, n) : Except Fault (List U8 × Nat)) = given at found
  cases found with
  | longDouble d3 long =>
    subst result
    obtain ⟨out, stop, run, hw, hn⟩ := long_string_accepted (quote := 34#u8) (by simpa using d3) (by simpa using long)
    exact ⟨out, stop, by simp [triple_quote_spec, d3, run], hw, hn⟩
  | longSingle d3 s3 long =>
    subst result
    obtain ⟨out, stop, run, hw, hn⟩ := long_string_accepted (quote := 39#u8) (by simpa using s3) (by simpa using long)
    exact ⟨out, stop, by simp [triple_quote_spec, d3, s3, run], hw, hn⟩
  | doubleFails _ _ _ _ => cases result
  | double d3 s3 d1 quoted fits =>
    cases result
    obtain ⟨s, stop, hs, hstop, tok⟩ := quoted
    have sameStart : s = start := UScalar.eq_of_val_eq hs
    subst sameStart
    let output : alloc.vec.Vec U8 := alloc.vec.Vec.from w (by have := limit_bound limit; omega)
    have outVal : output.val = w := alloc.vec.Vec.from_val _ _
    have tokenRun := (Rowl.NTriples.quoted_accepted_iff bytes s stop false limit output).mpr
      ⟨by rw [outVal]; exact tok, by rw [outVal]; exact fits⟩
    exact ⟨output, stop, by simp [triple_quote_spec, d3, s3, byte_is_spec, d1, turtle.quoted_string, tokenRun], outVal,
      hstop⟩
  | single d3 s3 d1 body =>
    subst result
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 1#usize)
      (by scalar_tac))
    have nextIs : next.val = start.val + 1 := by simpa using nextValue
    obtain ⟨out, stop, run, hw, hn⟩ := single_body_accepted body rfl next (alloc.vec.Vec.new U8) nextIs rfl (by simp)
    exact ⟨out, stop, by simp [triple_quote_spec, d3, s3, byte_is_spec, d1, add, run], hw, hn⟩

/-! ## Language tags -/

theorem letter_byte_spec (b : U8) : turtle.letter_byte b = .ok (decide (Letter b.val)) := by
  unfold turtle.letter_byte Letter
  by_cases a : 65 ≤ b.val <;> by_cases c : b.val ≤ 90 <;> by_cases d : 97 ≤ b.val <;>
    simp [UScalar.le_equiv, a, c, d]

theorem digit_byte_spec (b : U8) : turtle.digit_byte b = .ok (decide (Digit b.val)) := by
  unfold turtle.digit_byte Digit
  by_cases a : 48 ≤ b.val <;> simp [UScalar.le_equiv, a]

theorem alnum_byte_spec (b : U8) : turtle.alnum_byte b = .ok (decide (Letter b.val ∨ Digit b.val)) := by
  unfold turtle.alnum_byte
  by_cases a : Letter b.val <;> simp [letter_byte_spec, digit_byte_spec, a]

theorem letters_end_spec (bytes : alloc.vec.Vec U8) (index : Usize) (inside : index.val ≤ bytes.val.length) :
    ∃ u : Usize, turtle.letters_end bytes index = .ok u ∧ u.val = LettersEnd bytes.val index.val := by
  rw [turtle.letters_end]
  by_cases more : index.val < bytes.val.length
  · have dropCons := List.drop_eq_getElem_cons more
    by_cases letter : Letter bytes.val[index.val].val
    · obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by have := bytes.property; scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨u, again, value⟩ := letters_end_spec bytes next (by omega)
      refine ⟨u, by simp [alloc.vec.Vec.len_val, more, vec_index more, vec_index_usize more, letter_byte_spec, letter, add, again], ?_⟩
      rw [value, nextIs]
      unfold LettersEnd
      rw [dropCons, List.takeWhile_cons_of_pos (by simpa using letter)]
      simp
      omega
    · refine ⟨index, by simp [alloc.vec.Vec.len_val, more, vec_index more, vec_index_usize more, letter_byte_spec, letter], ?_⟩
      unfold LettersEnd
      rw [dropCons, List.takeWhile_cons_of_neg (by simpa using letter)]
      simp
  · refine ⟨index, by simp [alloc.vec.Vec.len_val, more], ?_⟩
    unfold LettersEnd
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by bytes.val.length - index.val
decreasing_by omega

theorem alnums_end_spec (bytes : alloc.vec.Vec U8) (index : Usize) (inside : index.val ≤ bytes.val.length) :
    ∃ u : Usize, turtle.alnums_end bytes index = .ok u ∧ u.val = AlnumsEnd bytes.val index.val := by
  rw [turtle.alnums_end]
  by_cases more : index.val < bytes.val.length
  · have dropCons := List.drop_eq_getElem_cons more
    by_cases alnum : Letter bytes.val[index.val].val ∨ Digit bytes.val[index.val].val
    · obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by have := bytes.property; scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨u, again, value⟩ := alnums_end_spec bytes next (by omega)
      refine ⟨u, by simp [alloc.vec.Vec.len_val, more, vec_index more, vec_index_usize more, alnum_byte_spec, alnum, add, again], ?_⟩
      rw [value, nextIs]
      unfold AlnumsEnd
      rw [dropCons, List.takeWhile_cons_of_pos (by simpa using alnum)]
      simp
      omega
    · refine ⟨index, by simp [alloc.vec.Vec.len_val, more, vec_index more, vec_index_usize more, alnum_byte_spec, alnum], ?_⟩
      unfold AlnumsEnd
      rw [dropCons, List.takeWhile_cons_of_neg (by simpa using alnum)]
      simp
  · refine ⟨index, by simp [alloc.vec.Vec.len_val, more], ?_⟩
    unfold AlnumsEnd
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by bytes.val.length - index.val
decreasing_by omega

theorem letters_end_bound (bs : List U8) (i : Nat) (inside : i ≤ bs.length) :
    i ≤ LettersEnd bs i ∧ LettersEnd bs i ≤ bs.length := by
  unfold LettersEnd
  have := (List.takeWhile_prefix (fun b => decide (Letter b.val)) (l := bs.drop i)).length_le
  rw [List.length_drop] at this
  omega

theorem alnums_end_bound (bs : List U8) (i : Nat) (inside : i ≤ bs.length) :
    i ≤ AlnumsEnd bs i ∧ AlnumsEnd bs i ≤ bs.length := by
  unfold AlnumsEnd
  have := (List.takeWhile_prefix (fun b => decide (Letter b.val ∨ Digit b.val)) (l := bs.drop i)).length_le
  rw [List.length_drop] at this
  omega

theorem subtags_end_bound (bs : List U8) (i : Nat) (inside : i ≤ bs.length) :
    i ≤ SubtagsEnd bs i ∧ SubtagsEnd bs i ≤ bs.length := by
  rw [SubtagsEnd]
  split_ifs with more
  · have := alnums_end_bound bs (i + 1) (by
      obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp more.1
      have := (List.getElem?_eq_some_iff.mp lookup).1
      omega)
    have := subtags_end_bound bs (AlnumsEnd bs (i + 1)) this.2
    omega
  · omega
termination_by bs.length - i
decreasing_by
  have := alnums_end_bound bs (i + 1) (by
    obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp more.1
    have := (List.getElem?_eq_some_iff.mp lookup).1
    omega)
  omega

theorem subtags_end_spec (bytes : alloc.vec.Vec U8) (index : Usize) :
    ∃ u : Usize, turtle.subtags_end bytes index = .ok u ∧ u.val = SubtagsEnd bytes.val index.val := by
  rw [turtle.subtags_end]
  by_cases dash : ByteIs bytes.val index.val 45
  · have more : index.val < bytes.val.length := by
      obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp dash
      exact (List.getElem?_eq_some_iff.mp lookup).1
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
      (by have := bytes.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨finish, alnums, finishValue⟩ := alnums_end_spec bytes next (by omega)
    have bound := alnums_end_bound bytes.val (index.val + 1) (by omega)
    by_cases subtag : index.val + 1 < AlnumsEnd bytes.val (index.val + 1)
    · obtain ⟨u, again, value⟩ := subtags_end_spec bytes finish
      refine ⟨u, by simp [byte_is_spec, dash, add, alnums, UScalar.lt_equiv, nextIs, finishValue, subtag, again], ?_⟩
      rw [value, finishValue, nextIs]
      conv_rhs => rw [SubtagsEnd]
      rw [dif_pos ⟨dash, subtag⟩]
    · refine ⟨index, by simp [byte_is_spec, dash, add, alnums, UScalar.lt_equiv, nextIs, finishValue, subtag], ?_⟩
      rw [SubtagsEnd, dif_neg (fun h => subtag h.2)]
  · refine ⟨index, by simp [byte_is_spec, dash], ?_⟩
    rw [SubtagsEnd, dif_neg (fun h => dash h.1)]
termination_by bytes.val.length - index.val
decreasing_by
  have := alnums_end_bound bytes.val (index.val + 1) (by omega)
  rw [nextIs] at finishValue
  omega

theorem well_formed_spec (bytes : alloc.vec.Vec U8) :
    langtag.well_formed bytes = .ok (decide (LanguageTag bytes.val)) := by
  obtain ⟨accepted, run⟩ := Rowl.LangTag.well_formed_total_correct bytes
  by_cases tag : LanguageTag bytes.val
  · rw [(Rowl.LangTag.well_formed_accepted_iff bytes).mpr tag]
    simp [tag]
  · cases accepted with
    | true => exact False.elim (tag ((Rowl.LangTag.well_formed_accepted_iff bytes).mp run))
    | false => rw [run]; simp [tag]

theorem language_total_correct (bytes : alloc.vec.Vec U8) (start limit : Usize)
    (inside : start.val < bytes.val.length) :
    ∃ r o, turtle.language bytes start limit = .ok r ∧ LanguageAt bytes.val limit.val start.val o ∧
      Agrees stringView r o := by
  unfold turtle.language
  obtain ⟨first, add, firstValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 1#usize)
    (by have := bytes.property; scalar_tac))
  have firstIs : first.val = start.val + 1 := by simpa using firstValue
  obtain ⟨head, letters, headValue⟩ := letters_end_spec bytes first (by omega)
  have headBound := letters_end_bound bytes.val (start.val + 1) (by omega)
  by_cases nonempty : start.val + 1 < LettersEnd bytes.val (start.val + 1)
  · obtain ⟨finish, subtags, finishValue⟩ := subtags_end_spec bytes head
    have finishBound := subtags_end_bound bytes.val (LettersEnd bytes.val (start.val + 1)) headBound.2
    rw [headValue, firstIs] at finishValue
    obtain ⟨copied, copyRun, copyCorrect⟩ := Rowl.NTriples.copy_term_total_correct bytes first finish limit
      ⟨by omega, by omega⟩
    rw [firstIs, finishValue] at copyCorrect
    cases copied with
    | Ok value =>
      obtain ⟨fits, valueIs⟩ := copyCorrect
      by_cases tag : LanguageTag value.val
      · refine ⟨.Ok (value, finish), .ok (Span bytes.val (start.val + 1) (SubtagsEnd bytes.val
          (LettersEnd bytes.val (start.val + 1))), SubtagsEnd bytes.val (LettersEnd bytes.val (start.val + 1))), ?_,
          .tag nonempty rfl fits (by rw [Span, ← valueIs]; exact tag), by simp [Agrees, stringView, valueIs, Span, finishValue]⟩
        simp [add, letters, UScalar.lt_equiv, firstIs, headValue, nonempty, subtags, turtle.copied, copyRun,
          core.result.Result.Insts.CoreOpsTry.branch, well_formed_spec, tag]
      · refine ⟨.Err ⟨.InvalidLanguageTag, start⟩, .error (.InvalidLanguageTag, start.val), ?_,
          .malformed nonempty rfl fits (by rw [Span, ← valueIs]; exact tag), rfl⟩
        simp [add, letters, UScalar.lt_equiv, firstIs, headValue, nonempty, subtags, turtle.copied, copyRun,
          core.result.Result.Insts.CoreOpsTry.branch, well_formed_spec, tag, error_spec]
    | Err e =>
      obtain ⟨over, kind, offset⟩ := copyCorrect
      refine ⟨.Err ⟨KindOf e.kind, e.offset⟩, .error (.ResourceLimit, start.val + 1), ?_, .tooLong nonempty rfl over, ?_⟩
      · simp [add, letters, UScalar.lt_equiv, firstIs, headValue, nonempty, subtags, turtle.copied, copyRun,
          core.result.Result.Insts.CoreOpsTry.branch, lift_spec]
      · simp [Agrees, faultOf, kind, KindOf, offset]
  · have none : LettersEnd bytes.val (start.val + 1) = start.val + 1 := by omega
    exact ⟨.Err ⟨.InvalidLanguageTag, start⟩, .error (.InvalidLanguageTag, start.val), by simp [add, letters,
      UScalar.lt_equiv, firstIs, headValue, nonempty, error_spec], .empty none, rfl⟩

theorem language_accepted {bytes : alloc.vec.Vec U8} {start limit : Usize} (inside : start.val < bytes.val.length)
    {t : List U8} {n : Nat} (found : LanguageAt bytes.val limit.val start.val (.ok (t, n))) :
    ∃ out stop, turtle.language bytes start limit = .ok (.Ok (out, stop)) ∧ out.val = t ∧ stop.val = n := by
  unfold turtle.language
  generalize result : (Except.ok (t, n) : Except Fault (List U8 × Nat)) = given at found
  cases found with
  | empty _ => cases result
  | tooLong _ _ _ => cases result
  | malformed _ _ _ _ => cases result
  | tag nonempty finish fits tag =>
    cases result
    obtain ⟨first, add, firstValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 1#usize)
      (by have := bytes.property; scalar_tac))
    have firstIs : first.val = start.val + 1 := by simpa using firstValue
    obtain ⟨head, letters, headValue⟩ := letters_end_spec bytes first (by omega)
    have headBound := letters_end_bound bytes.val (start.val + 1) (by omega)
    obtain ⟨stop, subtags, stopValue⟩ := subtags_end_spec bytes head
    rw [headValue, firstIs, finish] at stopValue
    have finishBound := subtags_end_bound bytes.val (LettersEnd bytes.val (start.val + 1)) headBound.2
    rw [finish] at finishBound
    obtain ⟨copied, copyRun, copyCorrect⟩ := Rowl.NTriples.copy_term_total_correct bytes first stop limit
      ⟨by omega, by omega⟩
    rw [firstIs, stopValue] at copyCorrect
    cases copied with
    | Ok value =>
      obtain ⟨_, valueIs⟩ := copyCorrect
      have isTag : LanguageTag value.val := by rw [valueIs]; exact tag
      refine ⟨value, stop, ?_, by rw [valueIs]; rfl, stopValue⟩
      simp [add, letters, UScalar.lt_equiv, firstIs, headValue, nonempty, subtags, turtle.copied, copyRun,
        core.result.Result.Insts.CoreOpsTry.branch, well_formed_spec, isTag]
    | Err _ =>
      obtain ⟨over, _, _⟩ := copyCorrect
      omega

theorem language_bound {bs : List U8} {limit start : Nat} {t : List U8} {n : Nat}
    (found : LanguageAt bs limit start (.ok (t, n))) (inside : start < bs.length) : start < n ∧ n ≤ bs.length := by
  generalize result : (Except.ok (t, n) : Except Fault (List U8 × Nat)) = given at found
  cases found with
  | empty _ => cases result
  | tooLong _ _ _ => cases result
  | malformed _ _ _ _ => cases result
  | tag nonempty finish fits tag =>
    cases result
    have letters := letters_end_bound bs (start + 1) (by omega)
    have subtags := subtags_end_bound bs (LettersEnd bs (start + 1)) letters.2
    omega


/-! ## Literals -/

theorem same_constant_from_spec (value : alloc.vec.Vec U8) (pattern : Slice U8) (index : Usize)
    (inside : index.val ≤ value.val.length) (same : value.val.length = pattern.val.length) :
    turtle.same_constant_from value pattern index = .ok (decide (value.val.drop index.val = pattern.val.drop index.val)) := by
  rw [turtle.same_constant_from]
  by_cases more : index.val < value.val.length
  · have inPattern : index.val < pattern.val.length := by omega
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
      (by have := value.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have shape : value.val.drop index.val = pattern.val.drop index.val ↔
        (value.val[index.val] = pattern.val[index.val] ∧ value.val.drop (index.val + 1) = pattern.val.drop (index.val + 1)) := by
      rw [List.drop_eq_getElem_cons more, List.drop_eq_getElem_cons inPattern, List.cons.injEq]
    by_cases equal : value.val[index.val] = pattern.val[index.val]
    · have again := same_constant_from_spec value pattern next (by omega) same
      rw [nextIs] at again
      simp [alloc.vec.Vec.len_val, more, vec_index more, vec_index_usize more, slice_index inPattern, equal, add, again, shape]
    · simp [alloc.vec.Vec.len_val, more, vec_index more, vec_index_usize more, slice_index inPattern, equal, shape]
  · simp [alloc.vec.Vec.len_val, more, List.drop_eq_nil_of_le (show value.val.length ≤ index.val by omega),
      List.drop_eq_nil_of_le (show pattern.val.length ≤ index.val by omega)]
termination_by value.val.length - index.val
decreasing_by omega

theorem same_constant_spec (value : alloc.vec.Vec U8) (pattern : Slice U8) :
    turtle.same_constant value pattern = .ok (decide (value.val = pattern.val)) := by
  unfold turtle.same_constant
  by_cases same : value.val.length = pattern.val.length
  · have equal : alloc.vec.Vec.len value = Slice.len pattern := by
      apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len_val, Slice.len_val, same]
    simp [equal, same_constant_from_spec value pattern 0#usize (by simp) same]
  · have different : ¬ alloc.vec.Vec.len value = Slice.len pattern := by
      intro h; apply same; have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len_val, Slice.len_val] using this
    have notEqual : ¬ value.val = pattern.val := fun h => same (by rw [h])
    simp [different, notEqual]

theorem lang_string_spec (spelling : alloc.vec.Vec U8) :
    turtle.lang_string spelling = .ok (decide (spelling.val = LangStringBytes)) := by
  unfold turtle.lang_string
  simp [same_constant_spec, LangStringBytes, slice_array]

/-- The view of a literal kind. -/
def kindView : rdf.LiteralKind → Kind
  | .Datatype d => .datatype d.spelling.val
  | .Language t => .language t.val

/-- The view of a literal kind result. -/
def kindResult (pair : rdf.LiteralKind × Usize) : Kind × Nat := (kindView pair.1, pair.2.val)

@[simp] theorem u8_94 : (94#u8 : U8).val = 94 := rfl
@[simp] theorem u8_64 : (64#u8 : U8).val = 64 := rfl
@[simp] theorem u8_60 : (60#u8 : U8).val = 60 := rfl
@[simp] theorem u8_58 : (58#u8 : U8).val = 58 := rfl

theorem datatype_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) (base : alloc.vec.Vec U8)
    (prefixes : alloc.vec.Vec turtle.Prefix) (limit : Usize) (inside : position.val < bytes.val.length) :
    ∃ r o, turtle.datatype bytes position base prefixes limit = .ok r ∧
      DatatypeAt bytes.val base.val (declarations prefixes.val) limit.val position.val o ∧ Agrees kindResult r o := by
  unfold turtle.datatype
  have bytesBound := bytes.property
  obtain ⟨second, add, secondValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := position) (y := 1#usize)
    (by scalar_tac))
  have secondIs : second.val = position.val + 1 := by simpa using secondValue
  by_cases caret : ByteIs bytes.val (position.val + 1) 94
  · have inside2 : position.val + 1 < bytes.val.length := by
      obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp caret
      exact (List.getElem?_eq_some_iff.mp lookup).1
    obtain ⟨third, add2, thirdValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := position) (y := 2#usize)
      (by scalar_tac))
    have thirdIs : third.val = position.val + 2 := by simpa using thirdValue
    obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct bytes third
    rw [thirdIs] at spaceCorrect
    rcases spaced with s | e
    · obtain ⟨r, o, iriRun, iriCorrect, agree⟩ := iri_total_correct bytes s base prefixes limit
      rcases r with ⟨d, next⟩ | e
      · obtain rfl := agrees_ok agree
        by_cases lang : d.spelling.val = LangStringBytes
        · refine ⟨.Err ⟨.InvalidLiteralKind, position⟩, .error (.InvalidLiteralKind, position.val), ?_,
            .langString caret spaceCorrect (by simp only [iriView] at iriCorrect; rw [← lang]; exact iriCorrect), rfl⟩
          simp [add, byte_is_spec, secondIs, caret, add2, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, iriRun,
            lang_string_spec, lang, error_spec]
        · refine ⟨.Ok (.Datatype d, next), .ok (.datatype d.spelling.val, next.val), ?_,
            .datatype caret spaceCorrect iriCorrect lang, rfl⟩
          simp [add, byte_is_spec, secondIs, caret, add2, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, iriRun,
            lang_string_spec, lang]
      · obtain rfl := agrees_err agree
        exact ⟨.Err e, .error (faultOf e), by simp [add, byte_is_spec, secondIs, caret, add2, spaceRun,
          core.result.Result.Insts.CoreOpsTry.branch, iriRun], .iriFails caret spaceCorrect iriCorrect, rfl⟩
    · exact ⟨.Err e, .error (faultOf e), by simp [add, byte_is_spec, secondIs, caret, add2, spaceRun,
        core.result.Result.Insts.CoreOpsTry.branch], .spaceFails caret spaceCorrect, rfl⟩
  · exact ⟨.Err ⟨.InvalidLiteralKind, position⟩, .error (.InvalidLiteralKind, position.val), by simp [add,
      byte_is_spec, secondIs, caret, error_spec], .single caret, rfl⟩

theorem datatype_accepted {bytes : alloc.vec.Vec U8} {position : Usize} {base : alloc.vec.Vec U8}
    {prefixes : alloc.vec.Vec turtle.Prefix} {limit : Usize} (inside : position.val < bytes.val.length) {k : Kind}
    {n : Nat} (found : DatatypeAt bytes.val base.val (declarations prefixes.val) limit.val position.val (.ok (k, n))) :
    ∃ kind next, turtle.datatype bytes position base prefixes limit = .ok (.Ok (kind, next)) ∧
      kindResult (kind, next) = (k, n) := by
  unfold turtle.datatype
  have bytesBound := bytes.property
  obtain ⟨second, add, secondValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := position) (y := 1#usize)
    (by scalar_tac))
  have secondIs : second.val = position.val + 1 := by simpa using secondValue
  generalize result : (Except.ok (k, n) : Except Fault (Kind × Nat)) = given at found
  cases found with
  | single _ => cases result
  | spaceFails _ _ => cases result
  | iriFails _ _ _ => cases result
  | langString _ _ _ => cases result
  | @datatype s d q caret spaced iriFound notLang =>
    cases result
    have inside2 : position.val + 1 < bytes.val.length := by
      obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp caret
      exact (List.getElem?_eq_some_iff.mp lookup).1
    obtain ⟨third, add2, thirdValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := position) (y := 2#usize)
      (by scalar_tac))
    have thirdIs : third.val = position.val + 2 := by simpa using thirdValue
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs (show TriviaRuns bytes.val true third.val s by
      rw [thirdIs]; exact spaced)
    obtain ⟨iri, next, iriRun, hv, hn⟩ := iri_accepted (show IriAt bytes.val base.val _ limit.val stop.val _ by
      rw [stopValue]; exact iriFound)
    have notLang' : ¬ iri.spelling.val = LangStringBytes := by rw [hv]; exact notLang
    exact ⟨.Datatype iri, next, by simp [add, byte_is_spec, secondIs, caret, add2, spaceRun,
      core.result.Result.Insts.CoreOpsTry.branch, iriRun, lang_string_spec, notLang'],
      by simp [kindResult, kindView, hv, hn]⟩

theorem datatype_bound {bs base : List U8} {prefixes : List (List U8 × List U8)} {limit p : Nat} {k : Kind}
    {n : Nat} (found : DatatypeAt bs base prefixes limit p (.ok (k, n))) : p < n ∧ n ≤ bs.length := by
  generalize result : (Except.ok (k, n) : Except Fault (Kind × Nat)) = given at found
  cases found with
  | single _ => cases result
  | spaceFails _ _ => cases result
  | iriFails _ _ _ => cases result
  | langString _ _ _ => cases result
  | datatype caret spaced iriFound notLang =>
    cases result
    have := trivia_bound spaced
    have := iri_bound iriFound
    omega

theorem literal_kind_total_correct (bytes : alloc.vec.Vec U8) (finish : Usize) (base : alloc.vec.Vec U8)
    (prefixes : alloc.vec.Vec turtle.Prefix) (limit : Usize) :
    ∃ r o, turtle.literal_kind bytes finish base prefixes limit = .ok r ∧
      KindAfter bytes.val base.val (declarations prefixes.val) limit.val finish.val o ∧ Agrees kindResult r o := by
  unfold turtle.literal_kind
  obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct bytes finish
  rcases spaced with p | e
  · have pBound := trivia_bound spaceCorrect
    by_cases at_ : ByteIs bytes.val p.val 64
    · have inside : p.val < bytes.val.length := by
        obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp at_
        exact (List.getElem?_eq_some_iff.mp lookup).1
      obtain ⟨r, o, run, correct, agree⟩ := language_total_correct bytes p limit inside
      rcases r with ⟨tag, next⟩ | e
      · obtain rfl := agrees_ok agree
        exact ⟨.Ok (.Language tag, next), .ok (.language tag.val, next.val), by simp [spaceRun,
          core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, at_, run], .language spaceCorrect at_ correct, rfl⟩
      · obtain rfl := agrees_err agree
        exact ⟨.Err e, .error (faultOf e), by simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec,
          at_, run], .languageFails spaceCorrect at_ correct, rfl⟩
    · by_cases caret : ByteIs bytes.val p.val 94
      · have inside : p.val < bytes.val.length := by
          obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp caret
          exact (List.getElem?_eq_some_iff.mp lookup).1
        obtain ⟨r, o, run, correct, agree⟩ := datatype_total_correct bytes p base prefixes limit inside
        exact ⟨r, o, by simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, at_, caret, run],
          .datatype spaceCorrect at_ caret correct, agree⟩
      · refine ⟨?r, .ok (.datatype XsdStringBytes, finish.val), ?run, .plain spaceCorrect at_ caret, ?agree⟩
        case run => simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, at_, caret, xsd_eq]; rfl
        case agree => simp [Agrees, kindResult, kindView, slice_array, XsdStringBytes]
  · exact ⟨.Err e, .error (faultOf e), by simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch],
      .spaceFails spaceCorrect, rfl⟩

theorem literal_kind_accepted {bytes : alloc.vec.Vec U8} {finish : Usize} {base : alloc.vec.Vec U8}
    {prefixes : alloc.vec.Vec turtle.Prefix} {limit : Usize} {k : Kind} {n : Nat}
    (found : KindAfter bytes.val base.val (declarations prefixes.val) limit.val finish.val (.ok (k, n))) :
    ∃ kind next, turtle.literal_kind bytes finish base prefixes limit = .ok (.Ok (kind, next)) ∧
      kindResult (kind, next) = (k, n) := by
  unfold turtle.literal_kind
  generalize result : (Except.ok (k, n) : Except Fault (Kind × Nat)) = given at found
  cases found with
  | spaceFails _ => cases result
  | languageFails _ _ _ => cases result
  | @language p t q spaced at_ tag =>
    cases result
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    have inside : p < bytes.val.length := by
      obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp at_
      exact (List.getElem?_eq_some_iff.mp lookup).1
    obtain ⟨out, next, run, ho, hn⟩ := language_accepted (bytes := bytes) (start := stop) (limit := limit)
      (by rw [stopValue]; exact inside) (by rw [stopValue]; exact tag)
    exact ⟨.Language out, next, by simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, stopValue,
      at_, run], by simp [kindResult, kindView, ho, hn]⟩
  | @datatype p r spaced at_ caret datatype =>
    subst result
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    have inside : p < bytes.val.length := by
      obtain ⟨b, lookup, _⟩ := Option.map_eq_some_iff.mp caret
      exact (List.getElem?_eq_some_iff.mp lookup).1
    obtain ⟨kind, next, run, value⟩ := datatype_accepted (bytes := bytes) (position := stop) (base := base)
      (prefixes := prefixes) (limit := limit) (by rw [stopValue]; exact inside) (by rw [stopValue]; exact datatype)
    exact ⟨kind, next, by simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, stopValue, at_,
      caret, run], value⟩
  | @plain p spaced at_ caret =>
    cases result
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    refine ⟨?kind, finish, ?run, ?value⟩
    case run => simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, stopValue, at_, caret, xsd_eq]; rfl
    case value => simp [kindResult, kindView, slice_array, XsdStringBytes]

theorem kind_after_bound {bs base : List U8} {prefixes : List (List U8 × List U8)} {limit e : Nat} {k : Kind}
    {n : Nat} (found : KindAfter bs base prefixes limit e (.ok (k, n))) (inside : e ≤ bs.length) :
    e ≤ n ∧ n ≤ bs.length := by
  generalize result : (Except.ok (k, n) : Except Fault (Kind × Nat)) = given at found
  cases found with
  | spaceFails _ => cases result
  | languageFails _ _ _ => cases result
  | @language p t q spaced at_ tag =>
    cases result
    have := trivia_bound spaced
    have inside2 : p < bs.length := byte_inside at_
    have := language_bound tag inside2
    omega
  | datatype spaced at_ caret datatype =>
    subst result
    have := trivia_bound spaced
    have := datatype_bound datatype
    omega
  | plain spaced at_ caret => cases result; omega

/-- The view of a literal result. -/
def literalResult (pair : rdf.RdfLiteral × Usize) : Term × Nat := (literalTerm pair.1, pair.2.val)

theorem literal_total_correct (bytes : alloc.vec.Vec U8) (start : Usize) (base : alloc.vec.Vec U8)
    (prefixes : alloc.vec.Vec turtle.Prefix) (limit : Usize) (inside : start.val < bytes.val.length) :
    ∃ r o, turtle.literal bytes start base prefixes limit = .ok r ∧
      LiteralAt bytes.val base.val (declarations prefixes.val) limit.val start.val o ∧ Agrees literalResult r o := by
  unfold turtle.literal
  obtain ⟨r, o, run, correct, agree⟩ := string_total_correct bytes start limit inside
  rcases r with ⟨lexical, finish⟩ | e
  · obtain rfl := agrees_ok agree
    obtain ⟨r, o, kindRun, kindCorrect, agree⟩ := literal_kind_total_correct bytes finish base prefixes limit
    rcases r with ⟨kind, next⟩ | e
    · obtain rfl := agrees_ok agree
      refine ⟨.Ok (⟨lexical, kind⟩, next), .ok (.literal lexical.val (kindView kind), next.val), by simp [run,
        core.result.Result.Insts.CoreOpsTry.branch, kindRun], .literal correct kindCorrect, ?_⟩
      cases kind <;> simp [Agrees, literalResult, literalTerm, kindView]
    · obtain rfl := agrees_err agree
      exact ⟨.Err e, .error (faultOf e), by simp [run, core.result.Result.Insts.CoreOpsTry.branch, kindRun],
        .kindFails correct kindCorrect, rfl⟩
  · obtain rfl := agrees_err agree
    exact ⟨.Err e, .error (faultOf e), by simp [run, core.result.Result.Insts.CoreOpsTry.branch], .stringFails correct,
      rfl⟩

theorem literal_accepted {bytes : alloc.vec.Vec U8} {start : Usize} {base : alloc.vec.Vec U8}
    {prefixes : alloc.vec.Vec turtle.Prefix} {limit : Usize} (inside : start.val < bytes.val.length) {t : Term}
    {n : Nat} (found : LiteralAt bytes.val base.val (declarations prefixes.val) limit.val start.val (.ok (t, n))) :
    ∃ lit next, turtle.literal bytes start base prefixes limit = .ok (.Ok (lit, next)) ∧
      literalResult (lit, next) = (t, n) := by
  unfold turtle.literal
  generalize result : (Except.ok (t, n) : Except Fault (Term × Nat)) = given at found
  cases found with
  | stringFails _ => cases result
  | kindFails _ _ => cases result
  | @literal v e k m string kind =>
    cases result
    obtain ⟨lexical, finish, stringRun, hv, he⟩ := string_accepted inside string
    obtain ⟨kd, next, kindRun, kindValue⟩ := literal_kind_accepted (bytes := bytes) (finish := finish) (base := base)
      (prefixes := prefixes) (limit := limit) (by rw [he]; exact kind)
    refine ⟨⟨lexical, kd⟩, next, by simp [stringRun, core.result.Result.Insts.CoreOpsTry.branch, kindRun], ?_⟩
    simp only [kindResult, Prod.mk.injEq] at kindValue
    simp only [literalResult, Prod.mk.injEq]
    refine ⟨?_, kindValue.2⟩
    cases kd <;> simp_all [literalTerm, kindView]

theorem long_body_bound {bs : List U8} {quote : Nat} : ∀ {p : Nat} {v : List U8} {r : List U8 × Nat},
    LongBody bs quote p v r → p < r.2 ∧ r.2 ≤ bs.length := by
  intro p v r body
  induction body with
  | close three => have := triple_quote_inside three; simp; omega
  | item notClose item encodeCorrect rest ih =>
    have := long_item_width item encodeCorrect
    omega

theorem single_body_bound {bs : List U8} {limit : Nat} : ∀ {p : Nat} {v : List U8} {r : Except Fault (List U8 × Nat)},
    SingleBody bs limit p v r → ∀ {w n}, r = .ok (w, n) → p < n ∧ n ≤ bs.length := by
  intro p v r body
  induction body with
  | missing _ => intro w n h; cases h
  | close u => intro w n h; cases h; exact unit_progress u
  | itemFails _ _ _ => intro w n h; cases h
  | tooLong _ _ _ _ _ => intro w n h; cases h
  | item u notClose stringItem encodeCorrect fits rest ih =>
    intro w n h
    obtain ⟨cp, stop, hx, hm, item⟩ := stringItem
    have := Rowl.NTriples.quoted_item_progress item
    have := ih h
    omega

theorem string_bound {bs : List U8} {limit start : Nat} {w : List U8} {n : Nat}
    (found : StringAt bs limit start (.ok (w, n))) : start < n ∧ n ≤ bs.length := by
  have longBound : ∀ {quote}, TripleQuote bs start quote → LongString bs limit quote start (.ok (w, n)) →
      start < n ∧ n ≤ bs.length := by
    intro quote three long
    have := triple_quote_inside three
    generalize result : (Except.ok (w, n) : Except Fault (List U8 × Nat)) = given at long
    cases long with
    | tooLong _ _ => cases result
    | long body fits => cases result; have := long_body_bound body; simp at this; omega
    | empty _ => cases result; omega
  generalize result : (Except.ok (w, n) : Except Fault (List U8 × Nat)) = given at found
  cases found with
  | longDouble three long => subst result; exact longBound three long
  | longSingle _ three long => subst result; exact longBound three long
  | doubleFails _ _ _ _ => cases result
  | double _ _ _ quoted fits =>
    cases result
    obtain ⟨s, stop, hs, hstop, token⟩ := quoted
    have := Rowl.NTriples.quoted_token_progress token
    omega
  | single _ _ _ body =>
    have := single_body_bound body result.symm
    omega

theorem literal_bound {bs base : List U8} {prefixes : List (List U8 × List U8)} {limit start : Nat} {t : Term}
    {n : Nat} (found : LiteralAt bs base prefixes limit start (.ok (t, n))) :
    start < n ∧ n ≤ bs.length := by
  generalize result : (Except.ok (t, n) : Except Fault (Term × Nat)) = given at found
  cases found with
  | stringFails _ => cases result
  | kindFails _ _ => cases result
  | literal string kind =>
    cases result
    have := string_bound string
    have := kind_after_bound kind this.2
    omega


/-! ## Numbers -/

theorem digits_end_spec (bytes : alloc.vec.Vec U8) (index : Usize) (inside : index.val ≤ bytes.val.length) :
    ∃ u : Usize, turtle.digits_end bytes index = .ok u ∧ u.val = DigitsEnd bytes.val index.val := by
  rw [turtle.digits_end]
  by_cases more : index.val < bytes.val.length
  · have dropCons := List.drop_eq_getElem_cons more
    by_cases digit : Digit bytes.val[index.val].val
    · obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by have := bytes.property; scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨u, again, value⟩ := digits_end_spec bytes next (by omega)
      refine ⟨u, by simp [alloc.vec.Vec.len_val, more, vec_index more, vec_index_usize more, digit_byte_spec, digit, add, again], ?_⟩
      rw [value, nextIs]
      unfold DigitsEnd
      rw [dropCons, List.takeWhile_cons_of_pos (by simpa using digit)]
      simp
      omega
    · refine ⟨index, by simp [alloc.vec.Vec.len_val, more, vec_index more, vec_index_usize more, digit_byte_spec, digit], ?_⟩
      unfold DigitsEnd
      rw [dropCons, List.takeWhile_cons_of_neg (by simpa using digit)]
      simp
  · refine ⟨index, by simp [alloc.vec.Vec.len_val, more], ?_⟩
    unfold DigitsEnd
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
termination_by bytes.val.length - index.val
decreasing_by omega

theorem digits_end_bound (bs : List U8) (i : Nat) (inside : i ≤ bs.length) :
    i ≤ DigitsEnd bs i ∧ DigitsEnd bs i ≤ bs.length := by
  unfold DigitsEnd
  have := (List.takeWhile_prefix (fun b => decide (Digit b.val)) (l := bs.drop i)).length_le
  simp at this
  omega

theorem sign_at_spec (bytes : alloc.vec.Vec U8) (index : Usize) :
    turtle.sign_at bytes index = .ok (decide (ByteIs bytes.val index.val 43 ∨ ByteIs bytes.val index.val 45)) := by
  unfold turtle.sign_at
  by_cases plus : ByteIs bytes.val index.val 43 <;> simp [byte_is_spec, plus]

theorem exponent_at_spec (bytes : alloc.vec.Vec U8) (index : Usize) :
    turtle.exponent_at bytes index = .ok (decide (ByteIs bytes.val index.val 101 ∨ ByteIs bytes.val index.val 69)) := by
  unfold turtle.exponent_at
  by_cases e : ByteIs bytes.val index.val 101 <;> simp [byte_is_spec, e]

theorem unsigned_spec (bytes : alloc.vec.Vec U8) (index : Usize) (inside : index.val ≤ bytes.val.length) :
    ∃ u : Usize, turtle.unsigned bytes index = .ok u ∧ u.val = Unsigned bytes.val index.val ∧
      u.val ≤ bytes.val.length := by
  unfold turtle.unsigned Unsigned
  by_cases sign : ByteIs bytes.val index.val 43 ∨ ByteIs bytes.val index.val 45
  · have more : index.val < bytes.val.length := by rcases sign with h | h <;> exact byte_inside h
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
      (by have := bytes.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    exact ⟨next, by simp [sign_at_spec, sign, add], by rw [if_pos sign, nextIs], by omega⟩
  · exact ⟨index, by simp [sign_at_spec, sign], by rw [if_neg sign], inside⟩

theorem exponent_end_spec (bytes : alloc.vec.Vec U8) (index : Usize) :
    ∃ r, turtle.exponent_end bytes index = .ok r ∧ r.map (·.val) = ExponentEnd bytes.val index.val := by
  unfold turtle.exponent_end ExponentEnd
  by_cases e : ByteIs bytes.val index.val 101 ∨ ByteIs bytes.val index.val 69
  · have more : index.val < bytes.val.length := by rcases e with h | h <;> exact byte_inside h
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
      (by have := bytes.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨d, unsignedRun, dValue, dBound⟩ := unsigned_spec bytes next (by omega)
    obtain ⟨finish, digitsRun, finishValue⟩ := digits_end_spec bytes d dBound
    rw [nextIs] at dValue
    rw [if_pos e]
    by_cases found : Unsigned bytes.val (index.val + 1) < DigitsEnd bytes.val (Unsigned bytes.val (index.val + 1))
    · refine ⟨some finish, by simp [exponent_at_spec, e, turtle.exponent_digits, add, unsignedRun, digitsRun,
        UScalar.lt_equiv, dValue, finishValue, found], ?_⟩
      rw [if_pos found]
      simp [finishValue, dValue]
    · refine ⟨none, by simp [exponent_at_spec, e, turtle.exponent_digits, add, unsignedRun, digitsRun,
        UScalar.lt_equiv, dValue, finishValue, found], ?_⟩
      rw [if_neg found]
      rfl
  · exact ⟨none, by simp [exponent_at_spec, e], by rw [if_neg e]; rfl⟩

theorem exponent_end_bound {bs : List U8} {i e : Nat} (h : ExponentEnd bs i = some e) : i < e ∧ e ≤ bs.length := by
  unfold ExponentEnd at h
  split_ifs at h with marker some
  · simp only [Option.some.injEq] at h
    have more : i < bs.length := by rcases marker with h | h <;> exact byte_inside h
    have unsignedLe : Unsigned bs (i + 1) ≤ bs.length := by
      unfold Unsigned
      split_ifs with sign
      · have := (show i + 1 < bs.length by rcases sign with h | h <;> exact byte_inside h); omega
      · omega
    have := digits_end_bound bs (Unsigned bs (i + 1)) unsignedLe
    have : i + 1 ≤ Unsigned bs (i + 1) := by unfold Unsigned; split_ifs <;> omega
    omega

/-- The datatype IRI of a number kind. -/
def numberIri : turtle.Number → List U8
  | .Integer => XsdIntegerBytes
  | .Decimal => XsdDecimalBytes
  | .Double => XsdDoubleBytes

/-- The view of the end and kind of a number. -/
def numberView (pair : Usize × turtle.Number) : Nat × List U8 := (pair.1.val, numberIri pair.2)

theorem with_exponent_spec (bytes : alloc.vec.Vec U8) (finish : Usize) (plain : turtle.Number) :
    ∃ r, turtle.with_exponent bytes finish plain = .ok r ∧
      numberView r = match ExponentEnd bytes.val finish.val with
        | some e => (e, XsdDoubleBytes)
        | none => (finish.val, numberIri plain) := by
  unfold turtle.with_exponent
  obtain ⟨r, run, value⟩ := exponent_end_spec bytes finish
  cases r with
  | none =>
    rw [← value]
    exact ⟨(finish, plain), by simp [run], rfl⟩
  | some after =>
    rw [← value]
    exact ⟨(after, .Double), by simp [run], rfl⟩

theorem number_end_spec (bytes : alloc.vec.Vec U8) (start : Usize) (inside : start.val ≤ bytes.val.length) :
    ∃ r, turtle.number_end bytes start = .ok r ∧ r.map numberView = NumberEnd bytes.val start.val := by
  unfold turtle.number_end NumberEnd
  have bytesBound := bytes.property
  obtain ⟨digits, unsignedRun, digitsValue, digitsBound⟩ := unsigned_spec bytes start inside
  obtain ⟨point, digitsEndRun, pointValue⟩ := digits_end_spec bytes digits digitsBound
  have pointBound := digits_end_bound bytes.val digits.val digitsBound
  rw [digitsValue] at pointValue pointBound
  simp only
  by_cases dot : ByteIs bytes.val point.val 46
  · have more := byte_inside dot
    rw [pointValue] at dot more
    rw [if_pos dot]
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := point) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = point.val + 1 := by simpa using nextValue
    obtain ⟨fractionEnd, fractionRun, fractionValue⟩ := digits_end_spec bytes next (by omega)
    have fractionBound := digits_end_bound bytes.val (point.val + 1) (by omega)
    rw [nextIs, pointValue] at fractionValue
    by_cases decimal : DigitsEnd bytes.val (Unsigned bytes.val start.val) + 1 <
        DigitsEnd bytes.val (DigitsEnd bytes.val (Unsigned bytes.val start.val) + 1)
    · obtain ⟨p, withRun, pValue⟩ := with_exponent_spec bytes fractionEnd .Decimal
      refine ⟨some p, ?_, ?_⟩
      · simp [unsignedRun, digitsEndRun, byte_is_spec, pointValue, dot, turtle.fraction, add, fractionRun,
          UScalar.lt_equiv, nextIs, fractionValue, decimal, withRun]
      · rw [if_pos decimal]
        simp only [Option.map_some, Option.some.injEq]
        rw [pValue, fractionValue]
        cases ExponentEnd bytes.val (DigitsEnd bytes.val (DigitsEnd bytes.val (Unsigned bytes.val start.val) + 1)) <;> rfl
    · rw [if_neg decimal]
      by_cases whole : Unsigned bytes.val start.val < DigitsEnd bytes.val (Unsigned bytes.val start.val)
      · rw [if_pos whole]
        obtain ⟨e, expRun, eValue⟩ := exponent_end_spec bytes next
        rw [nextIs, pointValue] at eValue
        cases e with
        | none =>
          refine ⟨some (point, .Integer), ?_, ?_⟩
          · simp [unsignedRun, digitsEndRun, byte_is_spec, pointValue, dot, turtle.fraction, add, fractionRun,
              UScalar.lt_equiv, nextIs, fractionValue, decimal, digitsValue, whole, expRun]
          · rw [← eValue]
            simp [numberView, numberIri, pointValue]
        | some after =>
          refine ⟨some (after, .Double), ?_, ?_⟩
          · simp [unsignedRun, digitsEndRun, byte_is_spec, pointValue, dot, turtle.fraction, add, fractionRun,
              UScalar.lt_equiv, nextIs, fractionValue, decimal, digitsValue, whole, expRun]
          · rw [← eValue]
            simp [numberView, numberIri]
      · rw [if_neg whole]
        refine ⟨none, ?_, rfl⟩
        simp [unsignedRun, digitsEndRun, byte_is_spec, pointValue, dot, turtle.fraction, add, fractionRun,
          UScalar.lt_equiv, nextIs, fractionValue, decimal, digitsValue, whole]
  · rw [pointValue] at dot
    rw [if_neg dot]
    by_cases whole : Unsigned bytes.val start.val < DigitsEnd bytes.val (Unsigned bytes.val start.val)
    · rw [if_pos whole]
      obtain ⟨p, withRun, pValue⟩ := with_exponent_spec bytes point .Integer
      refine ⟨some p, ?_, ?_⟩
      · simp [unsignedRun, digitsEndRun, byte_is_spec, pointValue, dot, UScalar.lt_equiv, digitsValue, whole, withRun]
      · simp only [Option.map_some, Option.some.injEq]
        rw [pValue, pointValue]
        cases ExponentEnd bytes.val (DigitsEnd bytes.val (Unsigned bytes.val start.val)) <;> rfl
    · rw [if_neg whole]
      refine ⟨none, ?_, rfl⟩
      simp [unsignedRun, digitsEndRun, byte_is_spec, pointValue, dot, UScalar.lt_equiv, digitsValue, whole]

theorem number_end_bound {bs : List U8} {start e : Nat} {d : List U8} (h : NumberEnd bs start = some (e, d))
    (inside : start ≤ bs.length) : start < e ∧ e ≤ bs.length := by
  have unsignedBound : start ≤ Unsigned bs start ∧ Unsigned bs start ≤ bs.length := by
    unfold Unsigned
    split_ifs with sign
    · have := (show start < bs.length by rcases sign with h | h <;> exact byte_inside h); omega
    · omega
  have pointBound := digits_end_bound bs (Unsigned bs start) unsignedBound.2
  unfold NumberEnd at h
  simp only at h
  split_ifs at h with dot decimal whole whole
  · have more := byte_inside dot
    have fractionBound := digits_end_bound bs (DigitsEnd bs (Unsigned bs start) + 1) (by omega)
    revert h
    cases expo : ExponentEnd bs (DigitsEnd bs (DigitsEnd bs (Unsigned bs start) + 1)) with
    | none => intro h; simp at h; omega
    | some after => intro h; simp at h; have := exponent_end_bound expo; omega
  · have more := byte_inside dot
    revert h
    cases expo : ExponentEnd bs (DigitsEnd bs (Unsigned bs start) + 1) with
    | none => intro h; simp at h; omega
    | some after => intro h; simp at h; have := exponent_end_bound expo; omega
  · revert h
    cases expo : ExponentEnd bs (DigitsEnd bs (Unsigned bs start)) with
    | none => intro h; simp at h; omega
    | some after => intro h; simp at h; have := exponent_end_bound expo; omega

theorem number_total_correct (bytes : alloc.vec.Vec U8) (start limit : Usize)
    (inside : start.val ≤ bytes.val.length) :
    ∃ r o, turtle.number bytes start limit = .ok r ∧ NumberAt bytes.val limit.val start.val o ∧
      Agrees literalResult r o := by
  unfold turtle.number
  obtain ⟨found, numberRun, numberValue⟩ := number_end_spec bytes start inside
  cases found with
  | none =>
    exact ⟨.Err ⟨.ExpectedObject, start⟩, .error (.ExpectedObject, start.val), by simp [numberRun, error_spec],
      .none (by simpa using numberValue.symm), rfl⟩
  | some pair =>
    obtain ⟨finish, kind⟩ := pair
    simp only [Option.map_some] at numberValue
    have numberIs : NumberEnd bytes.val start.val = some (finish.val, numberIri kind) := by
      rw [← numberValue]; rfl
    have bound := number_end_bound numberIs inside
    obtain ⟨copied, copyRun, copyCorrect⟩ := Rowl.NTriples.copy_term_total_correct bytes start finish limit
      ⟨by omega, by omega⟩
    cases copied with
    | Ok lexical =>
      obtain ⟨fits, lexicalValue⟩ := copyCorrect
      cases kind with
      | Integer =>
        refine ⟨?r1, _, ?run1, .number numberIs fits, ?agree1⟩
        case run1 => simp [numberRun, turtle.copied, copyRun, core.result.Result.Insts.CoreOpsTry.branch, xsd_eq]; rfl
        case agree1 => simp [Agrees, literalResult, literalTerm, lexicalValue, Span, numberIri, XsdIntegerBytes,
          slice_array, kindView]
      | Decimal =>
        refine ⟨?r2, _, ?run2, .number numberIs fits, ?agree2⟩
        case run2 => simp [numberRun, turtle.copied, copyRun, core.result.Result.Insts.CoreOpsTry.branch, xsd_eq]; rfl
        case agree2 => simp [Agrees, literalResult, literalTerm, lexicalValue, Span, numberIri, XsdDecimalBytes,
          slice_array, kindView]
      | Double =>
        refine ⟨?r3, _, ?run3, .number numberIs fits, ?agree3⟩
        case run3 => simp [numberRun, turtle.copied, copyRun, core.result.Result.Insts.CoreOpsTry.branch, xsd_eq]; rfl
        case agree3 => simp [Agrees, literalResult, literalTerm, lexicalValue, Span, numberIri, XsdDoubleBytes,
          slice_array, kindView]
    | Err e =>
      obtain ⟨over, kindIs, offset⟩ := copyCorrect
      refine ⟨.Err ⟨KindOf e.kind, e.offset⟩, .error (.ResourceLimit, start.val), ?_, .tooLong numberIs over, ?_⟩
      · simp [numberRun, turtle.copied, copyRun, core.result.Result.Insts.CoreOpsTry.branch, lift_spec]
      · simp [Agrees, faultOf, kindIs, KindOf, offset]

theorem number_accepted {bytes : alloc.vec.Vec U8} {start limit : Usize} (inside : start.val ≤ bytes.val.length)
    {t : Term} {n : Nat} (found : NumberAt bytes.val limit.val start.val (.ok (t, n))) :
    ∃ lit next, turtle.number bytes start limit = .ok (.Ok (lit, next)) ∧ literalResult (lit, next) = (t, n) := by
  obtain ⟨r, o, run, correct, agree⟩ := number_total_correct bytes start limit inside
  generalize result : (Except.ok (t, n) : Except Fault (Term × Nat)) = given at found
  cases found with
  | none _ => cases result
  | tooLong _ _ => cases result
  | @number e d numberIs fits =>
    cases result
    cases correct with
    | none none => rw [numberIs] at none; cases none
    | tooLong numberIs' over =>
      rw [numberIs] at numberIs'
      simp only [Option.some.injEq, Prod.mk.injEq] at numberIs'
      omega
    | number numberIs' fits' =>
      rw [numberIs] at numberIs'
      simp only [Option.some.injEq, Prod.mk.injEq] at numberIs'
      obtain ⟨rfl, rfl⟩ := numberIs'
      rcases r with ⟨lit, next⟩ | err
      · exact ⟨lit, next, run, agree⟩
      · exact False.elim agree

theorem number_bound {bs : List U8} {limit start : Nat} {t : Term} {n : Nat}
    (found : NumberAt bs limit start (.ok (t, n))) (inside : start ≤ bs.length) : start < n ∧ n ≤ bs.length := by
  generalize result : (Except.ok (t, n) : Except Fault (Term × Nat)) = given at found
  cases found with
  | none _ => cases result
  | tooLong _ _ => cases result
  | number numberIs fits => cases result; exact number_end_bound numberIs inside

/-! ## Keywords -/

theorem word_from_spec (bytes : alloc.vec.Vec U8) (start : Usize) (word : Slice U8) (index : Usize)
    (inside : index.val ≤ word.val.length) (fits : start.val + word.val.length ≤ bytes.val.length) :
    turtle.word_from bytes start word index =
      .ok (decide (word.val.drop index.val = (bytes.val.drop (start.val + index.val)).take (word.val.length - index.val))) := by
  rw [turtle.word_from]
  by_cases more : index.val < word.val.length
  · obtain ⟨at_, add, atValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := index)
      (by have := bytes.property; scalar_tac))
    have atIs : at_.val = start.val + index.val := by simpa using atValue
    have inBytes : at_.val < bytes.val.length := by omega
    obtain ⟨next, add2, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
      (by have := word.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have shape : (word.val.drop index.val = (bytes.val.drop (start.val + index.val)).take (word.val.length - index.val)) ↔
        (bytes.val[at_.val] = word.val[index.val] ∧
          word.val.drop (index.val + 1) = (bytes.val.drop (start.val + (index.val + 1))).take
            (word.val.length - (index.val + 1))) := by
      rw [List.drop_eq_getElem_cons more, List.drop_eq_getElem_cons (show start.val + index.val < bytes.val.length by omega),
        show word.val.length - index.val = (word.val.length - (index.val + 1)) + 1 by omega, List.take_succ_cons,
        List.cons.injEq]
      simp only [atIs, show start.val + index.val + 1 = start.val + (index.val + 1) by omega, eq_comm]
    by_cases same : bytes.val[at_.val] = word.val[index.val]
    · have again := word_from_spec bytes start word next (by omega) fits
      rw [nextIs] at again
      simp [Slice.len_val, more, add, vec_index inBytes, vec_index_usize inBytes, slice_index more, same, add2, again, shape]
    · simp [Slice.len_val, more, add, vec_index inBytes, vec_index_usize inBytes, slice_index more, same, shape]
  · simp [Slice.len_val, more, List.drop_eq_nil_of_le (show word.val.length ≤ index.val by omega),
      show word.val.length - index.val = 0 by omega]
termination_by word.val.length - index.val
decreasing_by omega

theorem word_at_spec (bytes : alloc.vec.Vec U8) (start : Usize) (word : Slice U8)
    (inside : start.val ≤ bytes.val.length) :
    turtle.word_at bytes start word = .ok (decide (WordAt bytes.val start.val word.val)) := by
  unfold turtle.word_at WordAt
  obtain ⟨rest, sub, restValue⟩ := WP.spec_imp_exists (Usize.sub_spec (x := alloc.vec.Vec.len bytes) (y := start)
    (by simp [alloc.vec.Vec.len_val]; omega))
  have restIs : rest.val = bytes.val.length - start.val := by simpa [alloc.vec.Vec.len_val] using restValue.1
  by_cases fits : word.val.length ≤ bytes.val.length - start.val
  · rw [word_from_spec bytes start word 0#usize (by simp) (by omega)]
    simp only [UScalar.le_equiv, alloc.vec.Vec.len_val, inside, decide_true, if_true, sub, Slice.len_val, restIs,
      fits, bind_ok]
    simp only [List.drop_zero, Nat.add_zero, Nat.sub_zero, show (0#usize : Usize).val = 0 from rfl]
    congr 1
    simp only [decide_eq_decide]
    rw [List.prefix_iff_eq_take]
  · simp only [UScalar.le_equiv, alloc.vec.Vec.len_val, inside, decide_true, if_true, sub, Slice.len_val, restIs,
      fits, if_false, bind_ok]
    have notPrefix : ¬ word.val <+: bytes.val.drop start.val := by
      intro h
      have := h.length_le
      simp at this
      omega
    simp [notPrefix]

theorem either_spec (bytes : alloc.vec.Vec U8) (index : Usize) (upper lower : U8) :
    turtle.either bytes index upper lower =
      .ok (decide (ByteIs bytes.val index.val upper.val ∨ ByteIs bytes.val index.val lower.val)) := by
  unfold turtle.either
  by_cases a : ByteIs bytes.val index.val upper.val <;> simp [byte_is_spec, a]

theorem tag_byte_spec (b : U8) : turtle.tag_byte b = .ok (decide (Letter b.val ∨ Digit b.val ∨ b.val = 45)) := by
  unfold turtle.tag_byte
  by_cases a : Letter b.val
  · simp [letter_byte_spec, a]
  · by_cases d : Digit b.val <;> simp [letter_byte_spec, digit_byte_spec, a, d, UScalar.eq_equiv]

theorem tag_continues_spec (bytes : alloc.vec.Vec U8) (index : Usize) :
    turtle.tag_continues bytes index = .ok (decide (TagContinues bytes.val index.val)) := by
  unfold turtle.tag_continues TagContinues
  by_cases more : index.val < bytes.val.length
  · simp [alloc.vec.Vec.len_val, more, vec_index more, vec_index_usize more, tag_byte_spec, List.getElem?_eq_getElem more]
  · simp [alloc.vec.Vec.len_val, more, List.getElem?_eq_none (show bytes.val.length ≤ index.val by omega)]

theorem at_keyword_spec (bytes : alloc.vec.Vec U8) (start : Usize) (word : Slice U8) :
    turtle.at_keyword bytes start word = .ok (decide (AtKeyword bytes.val start.val word.val)) := by
  unfold turtle.at_keyword AtKeyword
  by_cases at_ : ByteIs bytes.val start.val 64
  · have inside := byte_inside at_
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 1#usize)
      (by have := bytes.property; scalar_tac))
    have nextIs : next.val = start.val + 1 := by simpa using nextValue
    by_cases word_ : WordAt bytes.val (start.val + 1) word.val
    · have fits : start.val + 1 + word.val.length ≤ bytes.val.length := by
        have := word_.length_le
        simp at this
        omega
      obtain ⟨after, add2, afterValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := next) (y := Slice.len word)
        (by simp [Slice.len_val]; have := bytes.property; scalar_tac))
      have afterIs : after.val = start.val + 1 + word.val.length := by simp [Slice.len_val] at afterValue; omega
      simp [byte_is_spec, at_, add, word_at_spec bytes next word (by omega), nextIs, word_, add2,
        tag_continues_spec, afterIs]
    · simp [byte_is_spec, at_, add, word_at_spec bytes next word (by omega), nextIs, word_]
  · simp [byte_is_spec, at_]

/-! ## Booleans and words -/

theorem boolean_spec (lexical : Slice U8) :
    ∃ lit, turtle.boolean lexical = .ok lit ∧ literalTerm lit = .literal lexical.val (.datatype XsdBooleanBytes) := by
  refine ⟨?lit, ?run, ?value⟩
  case run => simp [turtle.boolean, constant_eq, xsd_eq]; rfl
  case value => simp [literalTerm, XsdBooleanBytes, slice_array]

/-- The view of an object result. -/
def objectResult (pair : rdf.Object × Usize) : Term × Nat := (objectTerm pair.1, pair.2.val)

theorem boolean_at_spec (bytes : alloc.vec.Vec U8) (start : Usize) (inside : start.val < bytes.val.length) :
    ∃ r, turtle.boolean_at bytes start = .ok r ∧
      (WordAt bytes.val start.val TrueBytes →
        Agrees objectResult r (.ok (.literal TrueBytes (.datatype XsdBooleanBytes), start.val + 4))) ∧
      (¬ WordAt bytes.val start.val TrueBytes → WordAt bytes.val start.val FalseBytes →
        Agrees objectResult r (.ok (.literal FalseBytes (.datatype XsdBooleanBytes), start.val + 5))) ∧
      (¬ WordAt bytes.val start.val TrueBytes → ¬ WordAt bytes.val start.val FalseBytes →
        Agrees objectResult r (.error (.ExpectedObject, start.val))) := by
  unfold turtle.boolean_at
  have bytesBound := bytes.property
  have trueAt := word_at_spec bytes start (Array.to_slice (Array.make 4#usize [116#u8, 114#u8, 117#u8, 101#u8]))
    (by omega)
  have falseAt := word_at_spec bytes start (Array.to_slice (Array.make 5#usize [102#u8, 97#u8, 108#u8, 115#u8, 101#u8]))
    (by omega)
  rw [slice_array] at trueAt falseAt
  by_cases yes : WordAt bytes.val start.val TrueBytes
  · have fits : start.val + 4 ≤ bytes.val.length := by
      have := yes.length_le
      simp [TrueBytes] at this
      omega
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 4#usize) (by scalar_tac))
    have nextIs : next.val = start.val + 4 := by simpa using nextValue
    obtain ⟨lit, boolRun, litValue⟩ := boolean_spec (Array.to_slice (Array.make 4#usize [116#u8, 114#u8, 117#u8, 101#u8]))
    rw [slice_array] at litValue
    refine ⟨.Ok (.Literal lit, next), ?_, fun _ => ?_, fun no => absurd yes no, fun no => absurd yes no⟩
    · simp only [TrueBytes] at yes
      simp [trueAt, yes, boolRun, add]
    · simp [Agrees, objectResult, objectTerm, litValue, nextIs, TrueBytes]
  · by_cases no : WordAt bytes.val start.val FalseBytes
    · have fits : start.val + 5 ≤ bytes.val.length := by
        have := no.length_le
        simp [FalseBytes] at this
        omega
      obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := start) (y := 5#usize) (by scalar_tac))
      have nextIs : next.val = start.val + 5 := by simpa using nextValue
      obtain ⟨lit, boolRun, litValue⟩ := boolean_spec
        (Array.to_slice (Array.make 5#usize [102#u8, 97#u8, 108#u8, 115#u8, 101#u8]))
      rw [slice_array] at litValue
      refine ⟨.Ok (.Literal lit, next), ?_, fun h => absurd h yes, fun _ _ => ?_, fun _ h => absurd no h⟩
      · simp only [TrueBytes] at yes
        simp only [FalseBytes] at no
        simp [trueAt, yes, falseAt, no, boolRun, add]
      · simp [Agrees, objectResult, objectTerm, litValue, nextIs, FalseBytes]
    · refine ⟨.Err ⟨.ExpectedObject, start⟩, ?_, fun h => absurd h yes, fun _ h => absurd h no, fun _ _ => rfl⟩
      simp only [TrueBytes] at yes
      simp only [FalseBytes] at no
      simp [trueAt, yes, falseAt, no, error_spec]

theorem boolean_at_total_correct (bytes : alloc.vec.Vec U8) (start : Usize) (inside : start.val < bytes.val.length)
    (unnamed : PrefixColon bytes.val start.val (.ok none)) {prefixes : List (List U8 × List U8)} {limit : Nat} :
    ∃ r o, turtle.boolean_at bytes start = .ok r ∧ WordObject bytes.val prefixes limit start.val o ∧
      Agrees objectResult r o := by
  obtain ⟨r, run, yesCase, noCase, otherCase⟩ := boolean_at_spec bytes start inside
  by_cases yes : WordAt bytes.val start.val TrueBytes
  · exact ⟨r, _, run, .true unnamed yes, yesCase yes⟩
  · by_cases no : WordAt bytes.val start.val FalseBytes
    · exact ⟨r, _, run, .false unnamed yes no, noCase yes no⟩
    · exact ⟨r, _, run, .other unnamed yes no, otherCase yes no⟩

theorem word_object_total_correct (bytes : alloc.vec.Vec U8) (start : Usize) (prefixes : alloc.vec.Vec turtle.Prefix)
    (limit : Usize) (inside : start.val < bytes.val.length) :
    ∃ r o, turtle.word_object bytes start prefixes limit = .ok r ∧
      WordObject bytes.val (declarations prefixes.val) limit.val start.val o ∧ Agrees objectResult r o := by
  unfold turtle.word_object
  obtain ⟨r, o, colonRun, colonCorrect, agree⟩ := prefix_colon_total_correct bytes start
  rcases r with (_ | colon) | e
  · obtain rfl := agrees_ok agree
    obtain ⟨r, o, run, correct, agree⟩ := boolean_at_total_correct bytes start inside colonCorrect
      (prefixes := declarations prefixes.val) (limit := limit.val)
    exact ⟨r, o, by simp [colonRun, core.result.Result.Insts.CoreOpsTry.branch, run], correct, agree⟩
  · obtain rfl := agrees_ok agree
    obtain ⟨r, o, run, correct, agree⟩ := prefixed_total_correct bytes start colon prefixes limit colonCorrect
    rcases r with ⟨iri, next⟩ | e
    · obtain rfl := agrees_ok agree
      exact ⟨.Ok (.Iri iri, next), .ok (.iri iri.spelling.val, next.val), by simp [colonRun,
        core.result.Result.Insts.CoreOpsTry.branch, run], .prefixed colonCorrect correct, rfl⟩
    · obtain rfl := agrees_err agree
      exact ⟨.Err e, .error (faultOf e), by simp [colonRun, core.result.Result.Insts.CoreOpsTry.branch, run],
        .prefixedFails colonCorrect correct, rfl⟩
  · obtain rfl := agrees_err agree
    exact ⟨.Err e, .error (faultOf e), by simp [colonRun, core.result.Result.Insts.CoreOpsTry.branch],
      .colonFails colonCorrect, rfl⟩

theorem word_object_accepted {bytes : alloc.vec.Vec U8} {start : Usize} {prefixes : alloc.vec.Vec turtle.Prefix}
    {limit : Usize} (inside : start.val < bytes.val.length) {t : Term} {n : Nat}
    (found : WordObject bytes.val (declarations prefixes.val) limit.val start.val (.ok (t, n))) :
    ∃ v next, turtle.word_object bytes start prefixes limit = .ok (.Ok (v, next)) ∧ objectResult (v, next) = (t, n) := by
  obtain ⟨r, o, run, correct, agree⟩ := word_object_total_correct bytes start prefixes limit inside
  generalize result : (Except.ok (t, n) : Except Fault (Term × Nat)) = given at found
  cases found with
  | colonFails _ => cases result
  | prefixedFails _ _ => cases result
  | @prefixed colon v m colonFound named =>
    cases result
    obtain ⟨c, colonRun, colonValue⟩ := prefix_colon_accepted colonFound
    cases c with
    | none => simp at colonValue
    | some colon' =>
      simp only [Option.map_some, Option.some.injEq] at colonValue
      obtain ⟨iri, stop, prefixedRun, hv, hn⟩ := prefixed_accepted (bytes := bytes) (start := start) (colon := colon')
        (prefixes := prefixes) (limit := limit) (by rw [colonValue]; exact colonFound) (by rw [colonValue]; exact named)
      refine ⟨.Iri iri, stop, ?_, by simp [objectResult, objectTerm, hv, hn]⟩
      unfold turtle.word_object
      simp [colonRun, core.result.Result.Insts.CoreOpsTry.branch, prefixedRun]
  | true unnamed yes =>
    cases result
    obtain ⟨c, colonRun, colonValue⟩ := prefix_colon_accepted unnamed
    cases c with
    | some _ => simp at colonValue
    | none =>
      obtain ⟨r2, run2, yesCase, _, _⟩ := boolean_at_spec bytes start inside
      obtain ⟨v, rfl, value⟩ := agrees_ok_inv (yesCase yes)
      refine ⟨v.1, v.2, ?_, value⟩
      unfold turtle.word_object
      simp [colonRun, core.result.Result.Insts.CoreOpsTry.branch, run2]
  | false unnamed notTrue no =>
    cases result
    obtain ⟨c, colonRun, colonValue⟩ := prefix_colon_accepted unnamed
    cases c with
    | some _ => simp at colonValue
    | none =>
      obtain ⟨r2, run2, _, noCase, _⟩ := boolean_at_spec bytes start inside
      obtain ⟨v, rfl, value⟩ := agrees_ok_inv (noCase notTrue no)
      refine ⟨v.1, v.2, ?_, value⟩
      unfold turtle.word_object
      simp [colonRun, core.result.Result.Insts.CoreOpsTry.branch, run2]
  | other _ _ _ => cases result

theorem word_object_bound {bs : List U8} {prefixes : List (List U8 × List U8)} {limit start : Nat} {t : Term}
    {n : Nat} (found : WordObject bs prefixes limit start (.ok (t, n))) (inside : start < bs.length) :
    start < n ∧ n ≤ bs.length := by
  generalize result : (Except.ok (t, n) : Except Fault (Term × Nat)) = given at found
  cases found with
  | colonFails _ => cases result
  | prefixedFails _ _ => cases result
  | prefixed colonFound named =>
    cases result
    have colonBound := prefix_colon_bound colonFound
    have := prefixed_bound named colonBound.2
    omega
  | true _ yes =>
    cases result
    have := yes.length_le
    simp [TrueBytes] at this
    omega
  | false _ _ no =>
    cases result
    have := no.length_le
    simp [FalseBytes] at this
    omega
  | other _ _ _ => cases result

end Rowl.TurtleTokens
