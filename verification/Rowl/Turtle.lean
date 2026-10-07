import Rowl.TurtleTokens

/-!
The triples of an RDF 1.1 Turtle document (W3C Recommendation, 25 February
2014, sections 6.5 and 7), as relations over the byte positions of the
document, written independently of the Rust reader, and the proof that
`turtle::read_with_limits` reads exactly them.

`Document bs scope base termLimit tripleLimit ts` holds when the bytes `bs` are
a Turtle document whose terms fit `termLimit` bytes, which denotes the triples
`ts` in order, at most `tripleLimit` of them, read against the base IRI `base`;
`DocumentError` gives the first error of any other bytes. The relations follow
the grammar of section 6.5 and the triples constructors of section 7: a subject
sets `curSubject`, a verb `curPredicate`, and each object makes the triple
`curSubject curPredicate object` after the triples inside the object. A blank
node property list `[` at byte offset `n` makes the blank node with the label
`0xFF` followed by the decimal digits of `n`; the list node of a collection
member that begins at byte offset `n` has the label `0xFE` followed by those
digits, and each list node gets `rdf:first` its member and `rdf:rest` the next
list node or `rdf:nil`. These labels can be no labels of the document, whose
bytes are UTF-8. Labelled blank nodes and these nodes carry the caller's scope.
-/
namespace Rowl.Turtle
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open Rowl.NTriples (UnitAt MalformedAt TriviaRuns TriviaFails XsdStringBytes LangStringBytes)
open Rowl.TurtleTokens
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ## Triples, contexts and node labels -/

/-- A triple by the terms of its subject, predicate and object. -/
structure Spo where
  subject : Term
  predicate : List U8
  object : Term

/-- The triple of an RDF triple. -/
def spo (t : rdf.Triple) : Spo := ⟨subjectTerm t.subject, t.predicate.spelling.val, objectTerm t.object⟩

/-- What a statement is read in: the bytes, the blank node scope, the base
    IRI, the prefix declarations (name and namespace, in order) and the limits
    on term bytes and triples. -/
structure Context where
  bs : List U8
  scope : List U8
  base : List U8
  prefixes : List (List U8 × List U8)
  termLimit : Nat
  tripleLimit : Nat

/-- The decimal digits of `n`. -/
def Decimal (n : Nat) : List U8 :=
  (if n < 10 then [] else Decimal (n / 10)) ++ [⟨BitVec.ofNat 8 (48 + n % 10)⟩]
termination_by n
decreasing_by omega

/-- The blank node of the `[` at byte offset `n`. -/
def bracketTerm (c : Context) (n : Nat) : Term := .blank c.scope (255#u8 :: Decimal n)
/-- The list node of the collection member at byte offset `n`. -/
def listTerm (c : Context) (n : Nat) : Term := .blank c.scope (254#u8 :: Decimal n)

/-- rdf:type, rdf:first, rdf:rest and rdf:nil. -/
def RdfTypeBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,49#u8,57#u8,57#u8,57#u8,47#u8,48#u8,50#u8,47#u8,50#u8,50#u8,45#u8,114#u8,100#u8,102#u8,45#u8,115#u8,121#u8,110#u8,116#u8,97#u8,120#u8,45#u8,110#u8,115#u8,35#u8,116#u8,121#u8,112#u8,101#u8]
def RdfFirstBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,49#u8,57#u8,57#u8,57#u8,47#u8,48#u8,50#u8,47#u8,50#u8,50#u8,45#u8,114#u8,100#u8,102#u8,45#u8,115#u8,121#u8,110#u8,116#u8,97#u8,120#u8,45#u8,110#u8,115#u8,35#u8,102#u8,105#u8,114#u8,115#u8,116#u8]
def RdfRestBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,49#u8,57#u8,57#u8,57#u8,47#u8,48#u8,50#u8,47#u8,50#u8,50#u8,45#u8,114#u8,100#u8,102#u8,45#u8,115#u8,121#u8,110#u8,116#u8,97#u8,120#u8,45#u8,110#u8,115#u8,35#u8,114#u8,101#u8,115#u8,116#u8]
def RdfNilBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,49#u8,57#u8,57#u8,57#u8,47#u8,48#u8,50#u8,47#u8,50#u8,50#u8,45#u8,114#u8,100#u8,102#u8,45#u8,115#u8,121#u8,110#u8,116#u8,97#u8,120#u8,45#u8,110#u8,115#u8,35#u8,110#u8,105#u8,108#u8]

/-! ## Terms -/

/-- The term at `start` that makes no triples, by the kind its first character
    begins: an IRIREF, a labelled blank node, a literal, a number, a prefixed
    name or a boolean. -/
inductive TermAt (c : Context) (start : Nat) : turtle.Start → Except Fault (Term × Nat) → Prop
  | iriFails {f} : IriRef c.bs c.base c.termLimit start (.error f) → TermAt c start .Iri (.error f)
  | iri {v n} : IriRef c.bs c.base c.termLimit start (.ok (v, n)) → TermAt c start .Iri (.ok (.iri v, n))
  | blank {r} : BlankLabel c.bs c.scope c.termLimit start r → TermAt c start .Blank r
  | literal {r} : LiteralAt c.bs c.base c.prefixes c.termLimit start r → TermAt c start .Quote r
  | number {r} : NumberAt c.bs c.termLimit start r → TermAt c start .Number r
  | word {r} : WordObject c.bs c.prefixes c.termLimit start r → TermAt c start .Word r
  | bracket : TermAt c start .Bracket (.error (.ExpectedObject, start))
  | paren : TermAt c start .Paren (.error (.ExpectedObject, start))
  | other : TermAt c start .Other (.error (.ExpectedObject, start))

/-- The verb at `position` after white space: an iri, or `a` for rdf:type
    when no prefixed name begins there. -/
inductive VerbAt (c : Context) (position : Nat) : Except Fault (List U8 × Nat) → Prop
  | spaceFails {f} : TriviaFault c.bs position f → VerbAt c position (.error f)
  | missing {s f} : TriviaRuns c.bs true position s → MissingFault c.bs s f → VerbAt c position (.error f)
  | iri {s q r} : TriviaRuns c.bs true position s → Unit c.bs s 60 q →
      IriRef c.bs c.base c.termLimit s r → VerbAt c position r
  | colonFails {s ch q f} : TriviaRuns c.bs true position s → Unit c.bs s ch q → ch ≠ 60 → WordStart ch →
      PrefixColon c.bs s (.error f) → VerbAt c position (.error f)
  | prefixed {s ch q colon r} : TriviaRuns c.bs true position s → Unit c.bs s ch q → ch ≠ 60 →
      WordStart ch → PrefixColon c.bs s (.ok (some colon)) →
      Prefixed c.bs c.prefixes c.termLimit s colon r → VerbAt c position r
  | a {s q} : TriviaRuns c.bs true position s → Unit c.bs s 97 q → PrefixColon c.bs s (.ok none) →
      VerbAt c position (.ok (RdfTypeBytes, q))
  | notA {s ch q} : TriviaRuns c.bs true position s → Unit c.bs s ch q → ch ≠ 60 → WordStart ch →
      PrefixColon c.bs s (.ok none) → ch ≠ 97 → VerbAt c position (.error (.ExpectedVerb, s))
  | other {s ch q} : TriviaRuns c.bs true position s → Unit c.bs s ch q → ch ≠ 60 → ¬ WordStart ch →
      VerbAt c position (.error (.ExpectedVerb, s))

/-- A verb must follow a `;` when the next byte is there and is none of `;`,
    `.` and `]`. -/
def VerbFollows (bs : List U8) (q : Nat) : Prop :=
  q < bs.length ∧ ¬ ByteIs bs q 59 ∧ ¬ ByteIs bs q 46 ∧ ¬ ByteIs bs q 93

/-! ## Objects, property lists and collections -/

mutual
/-- The object at `start`, after which `count` triples precede: its node, the
    position after it and the triples inside it. -/
inductive NodeAt (c : Context) : Nat → Nat → Except Fault (Term × Nat × List Spo) → Prop
  | missing {start count f} : MissingFault c.bs start f → NodeAt c start count (.error f)
  | termFails {start count ch q f} : Unit c.bs start ch q → StartOf ch ≠ .Bracket → StartOf ch ≠ .Paren →
      TermAt c start (StartOf ch) (.error f) → NodeAt c start count (.error f)
  | term {start count ch q t n} : Unit c.bs start ch q → StartOf ch ≠ .Bracket → StartOf ch ≠ .Paren →
      TermAt c start (StartOf ch) (.ok (t, n)) → NodeAt c start count (.ok (t, n, []))
  | bracketFails {start count ch q f} : Unit c.bs start ch q → StartOf ch = .Bracket →
      BracketAt c start count (.error f) → NodeAt c start count (.error f)
  | bracket {start count ch q t n ts listed} : Unit c.bs start ch q → StartOf ch = .Bracket →
      BracketAt c start count (.ok (t, n, ts, listed)) → NodeAt c start count (.ok (t, n, ts))
  | collection {start count ch q r} : Unit c.bs start ch q → StartOf ch = .Paren →
      CollectionAt c start count r → NodeAt c start count r

/-- The `[` at `start`: ANON, or a blank node property list and its triples;
    the flag tells whether there was a property list. -/
inductive BracketAt (c : Context) : Nat → Nat → Except Fault (Term × Nat × List Spo × Bool) → Prop
  | spaceFails {start count f} : TriviaFault c.bs (start + 1) f → BracketAt c start count (.error f)
  | anon {start count p} : TriviaRuns c.bs true (start + 1) p → ByteIs c.bs p 93 →
      BracketAt c start count (.ok (bracketTerm c start, p + 1, [], false))
  | listFails {start count p f} : TriviaRuns c.bs true (start + 1) p → ¬ ByteIs c.bs p 93 →
      ListAt c (bracketTerm c start) p count (.error f) → BracketAt c start count (.error f)
  | closeFails {start count p q ts f} : TriviaRuns c.bs true (start + 1) p → ¬ ByteIs c.bs p 93 →
      ListAt c (bracketTerm c start) p count (.ok (q, ts)) → TriviaFault c.bs q f →
      BracketAt c start count (.error f)
  | unclosed {start count p q ts e} : TriviaRuns c.bs true (start + 1) p → ¬ ByteIs c.bs p 93 →
      ListAt c (bracketTerm c start) p count (.ok (q, ts)) → TriviaRuns c.bs true q e → ¬ ByteIs c.bs e 93 →
      BracketAt c start count (.error (.ExpectedBracket, e))
  | list {start count p q ts e} : TriviaRuns c.bs true (start + 1) p → ¬ ByteIs c.bs p 93 →
      ListAt c (bracketTerm c start) p count (.ok (q, ts)) → TriviaRuns c.bs true q e → ByteIs c.bs e 93 →
      BracketAt c start count (.ok (bracketTerm c start, e + 1, ts, true))

/-- The collection at `start`: rdf:nil when empty, and otherwise the list node
    of its first member and the triples of all members. -/
inductive CollectionAt (c : Context) : Nat → Nat → Except Fault (Term × Nat × List Spo) → Prop
  | spaceFails {start count f} : TriviaFault c.bs (start + 1) f → CollectionAt c start count (.error f)
  | empty {start count p} : TriviaRuns c.bs true (start + 1) p → ByteIs c.bs p 41 →
      CollectionAt c start count (.ok (.iri RdfNilBytes, p + 1, []))
  | firstFails {start count p f} : TriviaRuns c.bs true (start + 1) p → ¬ ByteIs c.bs p 41 →
      ObjectAt c (listTerm c p) RdfFirstBytes p count (.error f) → CollectionAt c start count (.error f)
  | restFails {start count p q ts f} : TriviaRuns c.bs true (start + 1) p → ¬ ByteIs c.bs p 41 →
      ObjectAt c (listTerm c p) RdfFirstBytes p count (.ok (q, ts)) →
      MembersAt c q p (count + ts.length) (.error f) → CollectionAt c start count (.error f)
  | list {start count p q ts n us} : TriviaRuns c.bs true (start + 1) p → ¬ ByteIs c.bs p 41 →
      ObjectAt c (listTerm c p) RdfFirstBytes p count (.ok (q, ts)) →
      MembersAt c q p (count + ts.length) (.ok (n, us)) →
      CollectionAt c start count (.ok (listTerm c p, n, ts ++ us))

/-- The members of a collection from `position` up to `)`, after the member at
    `last`; each list node gets `rdf:rest` the next one, the last rdf:nil. -/
inductive MembersAt (c : Context) : Nat → Nat → Nat → Except Fault (Nat × List Spo) → Prop
  | spaceFails {position last count f} : TriviaFault c.bs position f → MembersAt c position last count (.error f)
  | closeFull {position last count p} : TriviaRuns c.bs true position p → ByteIs c.bs p 41 →
      c.tripleLimit ≤ count → MembersAt c position last count (.error (.ResourceLimit, p))
  | close {position last count p} : TriviaRuns c.bs true position p → ByteIs c.bs p 41 →
      count < c.tripleLimit →
      MembersAt c position last count (.ok (p + 1, [⟨listTerm c last, RdfRestBytes, .iri RdfNilBytes⟩]))
  | linkFull {position last count p} : TriviaRuns c.bs true position p → ¬ ByteIs c.bs p 41 →
      c.tripleLimit ≤ count → MembersAt c position last count (.error (.ResourceLimit, p))
  | memberFails {position last count p f} : TriviaRuns c.bs true position p → ¬ ByteIs c.bs p 41 →
      count < c.tripleLimit → ObjectAt c (listTerm c p) RdfFirstBytes p (count + 1) (.error f) →
      MembersAt c position last count (.error f)
  | restFails {position last count p q ts f} : TriviaRuns c.bs true position p → ¬ ByteIs c.bs p 41 →
      count < c.tripleLimit → ObjectAt c (listTerm c p) RdfFirstBytes p (count + 1) (.ok (q, ts)) →
      MembersAt c q p (count + 1 + ts.length) (.error f) → MembersAt c position last count (.error f)
  | more {position last count p q ts n us} : TriviaRuns c.bs true position p → ¬ ByteIs c.bs p 41 →
      count < c.tripleLimit → ObjectAt c (listTerm c p) RdfFirstBytes p (count + 1) (.ok (q, ts)) →
      MembersAt c q p (count + 1 + ts.length) (.ok (n, us)) →
      MembersAt c position last count (.ok (n, ⟨listTerm c last, RdfRestBytes, listTerm c p⟩ :: ts ++ us))

/-- An object at `position` with the subject `s` and the predicate `pr`: its
    node and, after the triples inside it, the triple `s pr node`. -/
inductive ObjectAt (c : Context) : Term → List U8 → Nat → Nat → Except Fault (Nat × List Spo) → Prop
  | spaceFails {s pr position count f} : TriviaFault c.bs position f → ObjectAt c s pr position count (.error f)
  | nodeFails {s pr position count p f} : TriviaRuns c.bs true position p → NodeAt c p count (.error f) →
      ObjectAt c s pr position count (.error f)
  | full {s pr position count p t n ts} : TriviaRuns c.bs true position p → NodeAt c p count (.ok (t, n, ts)) →
      c.tripleLimit ≤ count + ts.length → ObjectAt c s pr position count (.error (.ResourceLimit, p))
  | object {s pr position count p t n ts} : TriviaRuns c.bs true position p →
      NodeAt c p count (.ok (t, n, ts)) → count + ts.length < c.tripleLimit →
      ObjectAt c s pr position count (.ok (n, ts ++ [⟨s, pr, t⟩]))

/-- An objectList at `position`: objects separated by `,`. -/
inductive ObjectsAt (c : Context) : Term → List U8 → Nat → Nat → Except Fault (Nat × List Spo) → Prop
  | firstFails {s pr position count f} : ObjectAt c s pr position count (.error f) →
      ObjectsAt c s pr position count (.error f)
  | restFails {s pr position count n ts f} : ObjectAt c s pr position count (.ok (n, ts)) →
      MoreObjectsAt c s pr n (count + ts.length) (.error f) → ObjectsAt c s pr position count (.error f)
  | list {s pr position count n ts m us} : ObjectAt c s pr position count (.ok (n, ts)) →
      MoreObjectsAt c s pr n (count + ts.length) (.ok (m, us)) →
      ObjectsAt c s pr position count (.ok (m, ts ++ us))

/-- The objects after the first of an objectList, each after a `,`. -/
inductive MoreObjectsAt (c : Context) : Term → List U8 → Nat → Nat → Except Fault (Nat × List Spo) → Prop
  | spaceFails {s pr position count f} : TriviaFault c.bs position f →
      MoreObjectsAt c s pr position count (.error f)
  | finish {s pr position count p} : TriviaRuns c.bs true position p → ¬ ByteIs c.bs p 44 →
      MoreObjectsAt c s pr position count (.ok (p, []))
  | objectFails {s pr position count p f} : TriviaRuns c.bs true position p → ByteIs c.bs p 44 →
      ObjectAt c s pr (p + 1) count (.error f) → MoreObjectsAt c s pr position count (.error f)
  | restFails {s pr position count p n ts f} : TriviaRuns c.bs true position p → ByteIs c.bs p 44 →
      ObjectAt c s pr (p + 1) count (.ok (n, ts)) → MoreObjectsAt c s pr n (count + ts.length) (.error f) →
      MoreObjectsAt c s pr position count (.error f)
  | more {s pr position count p n ts m us} : TriviaRuns c.bs true position p → ByteIs c.bs p 44 →
      ObjectAt c s pr (p + 1) count (.ok (n, ts)) → MoreObjectsAt c s pr n (count + ts.length) (.ok (m, us)) →
      MoreObjectsAt c s pr position count (.ok (m, ts ++ us))

/-- A predicateObjectList at `position` with the subject `s`. -/
inductive ListAt (c : Context) : Term → Nat → Nat → Except Fault (Nat × List Spo) → Prop
  | verbFails {s position count f} : VerbAt c position (.error f) → ListAt c s position count (.error f)
  | objectsFails {s position count pr n f} : VerbAt c position (.ok (pr, n)) →
      ObjectsAt c s pr n count (.error f) → ListAt c s position count (.error f)
  | restFails {s position count pr n m ts f} : VerbAt c position (.ok (pr, n)) →
      ObjectsAt c s pr n count (.ok (m, ts)) → MorePredicatesAt c s m (count + ts.length) (.error f) →
      ListAt c s position count (.error f)
  | list {s position count pr n m ts k us} : VerbAt c position (.ok (pr, n)) →
      ObjectsAt c s pr n count (.ok (m, ts)) → MorePredicatesAt c s m (count + ts.length) (.ok (k, us)) →
      ListAt c s position count (.ok (k, ts ++ us))

/-- The rest of a predicateObjectList: `;` followed by a verb and its objects,
    or by nothing. -/
inductive MorePredicatesAt (c : Context) : Term → Nat → Nat → Except Fault (Nat × List Spo) → Prop
  | spaceFails {s position count f} : TriviaFault c.bs position f → MorePredicatesAt c s position count (.error f)
  | finish {s position count p} : TriviaRuns c.bs true position p → ¬ ByteIs c.bs p 59 →
      MorePredicatesAt c s position count (.ok (p, []))
  | afterFails {s position count p f} : TriviaRuns c.bs true position p → ByteIs c.bs p 59 →
      TriviaFault c.bs (p + 1) f → MorePredicatesAt c s position count (.error f)
  | empty {s position count p q r} : TriviaRuns c.bs true position p → ByteIs c.bs p 59 →
      TriviaRuns c.bs true (p + 1) q → ¬ VerbFollows c.bs q → MorePredicatesAt c s q count r →
      MorePredicatesAt c s position count r
  | verbFails {s position count p q f} : TriviaRuns c.bs true position p → ByteIs c.bs p 59 →
      TriviaRuns c.bs true (p + 1) q → VerbFollows c.bs q → VerbAt c q (.error f) →
      MorePredicatesAt c s position count (.error f)
  | objectsFails {s position count p q pr n f} : TriviaRuns c.bs true position p → ByteIs c.bs p 59 →
      TriviaRuns c.bs true (p + 1) q → VerbFollows c.bs q → VerbAt c q (.ok (pr, n)) →
      ObjectsAt c s pr n count (.error f) → MorePredicatesAt c s position count (.error f)
  | restFails {s position count p q pr n m ts f} : TriviaRuns c.bs true position p → ByteIs c.bs p 59 →
      TriviaRuns c.bs true (p + 1) q → VerbFollows c.bs q → VerbAt c q (.ok (pr, n)) →
      ObjectsAt c s pr n count (.ok (m, ts)) → MorePredicatesAt c s m (count + ts.length) (.error f) →
      MorePredicatesAt c s position count (.error f)
  | more {s position count p q pr n m ts k us} : TriviaRuns c.bs true position p → ByteIs c.bs p 59 →
      TriviaRuns c.bs true (p + 1) q → VerbFollows c.bs q → VerbAt c q (.ok (pr, n)) →
      ObjectsAt c s pr n count (.ok (m, ts)) → MorePredicatesAt c s m (count + ts.length) (.ok (k, us)) →
      MorePredicatesAt c s position count (.ok (k, ts ++ us))
end

/-! ## Statements -/

/-- The subject at `start` of a triples statement that does not begin with `[`:
    an IRIREF, a labelled blank node, a collection or a prefixed name. -/
inductive SubjectAt (c : Context) (start count : Nat) : Except Fault (Term × Nat × List Spo) → Prop
  | missing {f} : MissingFault c.bs start f → SubjectAt c start count (.error f)
  | iriFails {ch q f} : Unit c.bs start ch q → StartOf ch = .Iri →
      IriRef c.bs c.base c.termLimit start (.error f) → SubjectAt c start count (.error f)
  | iri {ch q v n} : Unit c.bs start ch q → StartOf ch = .Iri →
      IriRef c.bs c.base c.termLimit start (.ok (v, n)) → SubjectAt c start count (.ok (.iri v, n, []))
  | blankFails {ch q f} : Unit c.bs start ch q → StartOf ch = .Blank →
      BlankLabel c.bs c.scope c.termLimit start (.error f) → SubjectAt c start count (.error f)
  | blank {ch q t n} : Unit c.bs start ch q → StartOf ch = .Blank →
      BlankLabel c.bs c.scope c.termLimit start (.ok (t, n)) → SubjectAt c start count (.ok (t, n, []))
  | collection {ch q r} : Unit c.bs start ch q → StartOf ch = .Paren → CollectionAt c start count r →
      SubjectAt c start count r
  | colonFails {ch q f} : Unit c.bs start ch q → StartOf ch = .Word → PrefixColon c.bs start (.error f) →
      SubjectAt c start count (.error f)
  | unnamed {ch q} : Unit c.bs start ch q → StartOf ch = .Word → PrefixColon c.bs start (.ok none) →
      SubjectAt c start count (.error (.ExpectedSubject, start))
  | prefixedFails {ch q colon f} : Unit c.bs start ch q → StartOf ch = .Word →
      PrefixColon c.bs start (.ok (some colon)) → Prefixed c.bs c.prefixes c.termLimit start colon (.error f) →
      SubjectAt c start count (.error f)
  | prefixed {ch q colon v n} : Unit c.bs start ch q → StartOf ch = .Word →
      PrefixColon c.bs start (.ok (some colon)) → Prefixed c.bs c.prefixes c.termLimit start colon (.ok (v, n)) →
      SubjectAt c start count (.ok (.iri v, n, []))
  | other {ch q} : Unit c.bs start ch q → StartOf ch ≠ .Iri → StartOf ch ≠ .Blank → StartOf ch ≠ .Paren →
      StartOf ch ≠ .Word → SubjectAt c start count (.error (.ExpectedSubject, start))

/-- The optional predicateObjectList after a blank node property list subject:
    none when `.` follows. -/
inductive OptionalListAt (c : Context) (s : Term) (position count : Nat) : Except Fault (Nat × List Spo) → Prop
  | spaceFails {f} : TriviaFault c.bs position f → OptionalListAt c s position count (.error f)
  | none {p} : TriviaRuns c.bs true position p → ByteIs c.bs p 46 → OptionalListAt c s position count (.ok (p, []))
  | list {p r} : TriviaRuns c.bs true position p → ¬ ByteIs c.bs p 46 → ListAt c s p count r →
      OptionalListAt c s position count r

/-- The triples statement at `start`, without its `.`. -/
inductive TriplesAt (c : Context) (start count : Nat) : Except Fault (Nat × List Spo) → Prop
  | bracketFails {f} : ByteIs c.bs start 91 → BracketAt c start count (.error f) → TriplesAt c start count (.error f)
  | anonFails {t n ts f} : ByteIs c.bs start 91 → BracketAt c start count (.ok (t, n, ts, false)) →
      ListAt c t n (count + ts.length) (.error f) → TriplesAt c start count (.error f)
  | anon {t n ts m us} : ByteIs c.bs start 91 → BracketAt c start count (.ok (t, n, ts, false)) →
      ListAt c t n (count + ts.length) (.ok (m, us)) → TriplesAt c start count (.ok (m, ts ++ us))
  | listedFails {t n ts f} : ByteIs c.bs start 91 → BracketAt c start count (.ok (t, n, ts, true)) →
      OptionalListAt c t n (count + ts.length) (.error f) → TriplesAt c start count (.error f)
  | listed {t n ts m us} : ByteIs c.bs start 91 → BracketAt c start count (.ok (t, n, ts, true)) →
      OptionalListAt c t n (count + ts.length) (.ok (m, us)) → TriplesAt c start count (.ok (m, ts ++ us))
  | subjectFails {f} : ¬ ByteIs c.bs start 91 → SubjectAt c start count (.error f) →
      TriplesAt c start count (.error f)
  | subjectListFails {t n ts f} : ¬ ByteIs c.bs start 91 → SubjectAt c start count (.ok (t, n, ts)) →
      ListAt c t n (count + ts.length) (.error f) → TriplesAt c start count (.error f)
  | subject {t n ts m us} : ¬ ByteIs c.bs start 91 → SubjectAt c start count (.ok (t, n, ts)) →
      ListAt c t n (count + ts.length) (.ok (m, us)) → TriplesAt c start count (.ok (m, ts ++ us))

/-- The `.` that ends a statement, after white space at `position`. -/
inductive PeriodAt (bs : List U8) (position : Nat) : Except Fault Nat → Prop
  | spaceFails {f} : TriviaFault bs position f → PeriodAt bs position (.error f)
  | period {p} : TriviaRuns bs true position p → ByteIs bs p 46 → PeriodAt bs position (.ok (p + 1))
  | missing {p} : TriviaRuns bs true position p → ¬ ByteIs bs p 46 →
      PeriodAt bs position (.error (.ExpectedPeriod, p))

/-- `prefix`, `base`, and `PREFIX` and `BASE` in upper case. -/
def PrefixWord : List U8 := [112#u8,114#u8,101#u8,102#u8,105#u8,120#u8]
def BaseWord : List U8 := [98#u8,97#u8,115#u8,101#u8]
def PrefixUpper : List Nat := [80, 82, 69, 70, 73, 88]
def BaseUpper : List Nat := [66, 65, 83, 69]

/-- How a statement begins. -/
inductive Opening where
  | atPrefix | atBase | sparqlPrefix | sparqlBase | triples

/-- How the statement at `start` begins: `@prefix` or `@base`, where no longer
    LANGTAG begins, `PREFIX` or `BASE` in any case, where no PNAME_NS begins,
    or else a triples statement. -/
inductive OpeningAt (bs : List U8) (start : Nat) : Except Fault Opening → Prop
  | atPrefix : AtKeyword bs start PrefixWord → OpeningAt bs start (.ok .atPrefix)
  | atBase : ¬ AtKeyword bs start PrefixWord → AtKeyword bs start BaseWord → OpeningAt bs start (.ok .atBase)
  | prefixFails {f} : ¬ AtKeyword bs start PrefixWord → ¬ AtKeyword bs start BaseWord →
      AnyCase bs start PrefixUpper → PrefixColon bs start (.error f) → OpeningAt bs start (.error f)
  | prefixName {colon} : ¬ AtKeyword bs start PrefixWord → ¬ AtKeyword bs start BaseWord →
      AnyCase bs start PrefixUpper → PrefixColon bs start (.ok (some colon)) → OpeningAt bs start (.ok .triples)
  | sparqlPrefix : ¬ AtKeyword bs start PrefixWord → ¬ AtKeyword bs start BaseWord →
      AnyCase bs start PrefixUpper → PrefixColon bs start (.ok none) → OpeningAt bs start (.ok .sparqlPrefix)
  | baseFails {f} : ¬ AtKeyword bs start PrefixWord → ¬ AtKeyword bs start BaseWord →
      ¬ AnyCase bs start PrefixUpper → AnyCase bs start BaseUpper → PrefixColon bs start (.error f) →
      OpeningAt bs start (.error f)
  | baseName {colon} : ¬ AtKeyword bs start PrefixWord → ¬ AtKeyword bs start BaseWord →
      ¬ AnyCase bs start PrefixUpper → AnyCase bs start BaseUpper → PrefixColon bs start (.ok (some colon)) →
      OpeningAt bs start (.ok .triples)
  | sparqlBase : ¬ AtKeyword bs start PrefixWord → ¬ AtKeyword bs start BaseWord →
      ¬ AnyCase bs start PrefixUpper → AnyCase bs start BaseUpper → PrefixColon bs start (.ok none) →
      OpeningAt bs start (.ok .sparqlBase)
  | triples : ¬ AtKeyword bs start PrefixWord → ¬ AtKeyword bs start BaseWord →
      ¬ AnyCase bs start PrefixUpper → ¬ AnyCase bs start BaseUpper → OpeningAt bs start (.ok .triples)

/-- The PNAME_NS and IRIREF of a prefix declaration after its keyword at
    `position`: the prefix name and its namespace, resolved against `base`. -/
inductive PrefixDeclaration (bs base : List U8) (limit position : Nat) :
    Except Fault ((List U8 × List U8) × Nat) → Prop
  | spaceFails {f} : TriviaFault bs position f → PrefixDeclaration bs base limit position (.error f)
  | colonFails {s f} : TriviaRuns bs true position s → PrefixColon bs s (.error f) →
      PrefixDeclaration bs base limit position (.error f)
  | missing {s} : TriviaRuns bs true position s → PrefixColon bs s (.ok none) →
      PrefixDeclaration bs base limit position (.error (.ExpectedPrefix, s))
  | tooLong {s colon} : TriviaRuns bs true position s → PrefixColon bs s (.ok (some colon)) →
      limit < colon - s → PrefixDeclaration bs base limit position (.error (.ResourceLimit, s))
  | iriSpaceFails {s colon f} : TriviaRuns bs true position s → PrefixColon bs s (.ok (some colon)) →
      colon - s ≤ limit → TriviaFault bs (colon + 1) f → PrefixDeclaration bs base limit position (.error f)
  | iriFails {s colon p f} : TriviaRuns bs true position s → PrefixColon bs s (.ok (some colon)) →
      colon - s ≤ limit → TriviaRuns bs true (colon + 1) p → IriRef bs base limit p (.error f) →
      PrefixDeclaration bs base limit position (.error f)
  | declaration {s colon p ns n} : TriviaRuns bs true position s → PrefixColon bs s (.ok (some colon)) →
      colon - s ≤ limit → TriviaRuns bs true (colon + 1) p → IriRef bs base limit p (.ok (ns, n)) →
      PrefixDeclaration bs base limit position (.ok ((Span bs s colon, ns), n))

/-- The IRIREF of a base declaration after its keyword at `position`, resolved
    against the base before it. -/
inductive BaseDeclaration (bs base : List U8) (limit position : Nat) : Except Fault (List U8 × Nat) → Prop
  | spaceFails {f} : TriviaFault bs position f → BaseDeclaration bs base limit position (.error f)
  | iri {s r} : TriviaRuns bs true position s → IriRef bs base limit s r → BaseDeclaration bs base limit position r

/-- The bytes, the scope and the limits of a document. -/
structure Doc where
  bs : List U8
  scope : List U8
  termLimit : Nat
  tripleLimit : Nat

/-- The base IRI and the prefix declarations in force. -/
structure Env where
  base : List U8
  prefixes : List (List U8 × List U8)

/-- The context of a statement. -/
def Doc.at (d : Doc) (e : Env) : Context := ⟨d.bs, d.scope, e.base, e.prefixes, d.termLimit, d.tripleLimit⟩

/-- The statement at `start` in the environment `e`, after `count` triples:
    the position after it, the environment after it and its triples. -/
inductive StatementAt (d : Doc) (e : Env) (start count : Nat) : Except Fault (Nat × Env × List Spo) → Prop
  | openingFails {f} : OpeningAt d.bs start (.error f) → StatementAt d e start count (.error f)
  | atPrefixFails {f} : OpeningAt d.bs start (.ok .atPrefix) →
      PrefixDeclaration d.bs e.base d.termLimit (start + 7) (.error f) → StatementAt d e start count (.error f)
  | atPrefixPeriodFails {decl n f} : OpeningAt d.bs start (.ok .atPrefix) →
      PrefixDeclaration d.bs e.base d.termLimit (start + 7) (.ok (decl, n)) → PeriodAt d.bs n (.error f) →
      StatementAt d e start count (.error f)
  | atPrefix {decl n m} : OpeningAt d.bs start (.ok .atPrefix) →
      PrefixDeclaration d.bs e.base d.termLimit (start + 7) (.ok (decl, n)) → PeriodAt d.bs n (.ok m) →
      StatementAt d e start count (.ok (m, ⟨e.base, e.prefixes ++ [decl]⟩, []))
  | atBaseFails {f} : OpeningAt d.bs start (.ok .atBase) →
      BaseDeclaration d.bs e.base d.termLimit (start + 5) (.error f) → StatementAt d e start count (.error f)
  | atBasePeriodFails {b n f} : OpeningAt d.bs start (.ok .atBase) →
      BaseDeclaration d.bs e.base d.termLimit (start + 5) (.ok (b, n)) → PeriodAt d.bs n (.error f) →
      StatementAt d e start count (.error f)
  | atBase {b n m} : OpeningAt d.bs start (.ok .atBase) →
      BaseDeclaration d.bs e.base d.termLimit (start + 5) (.ok (b, n)) → PeriodAt d.bs n (.ok m) →
      StatementAt d e start count (.ok (m, ⟨b, e.prefixes⟩, []))
  | sparqlPrefixFails {f} : OpeningAt d.bs start (.ok .sparqlPrefix) →
      PrefixDeclaration d.bs e.base d.termLimit (start + 6) (.error f) → StatementAt d e start count (.error f)
  | sparqlPrefix {decl n} : OpeningAt d.bs start (.ok .sparqlPrefix) →
      PrefixDeclaration d.bs e.base d.termLimit (start + 6) (.ok (decl, n)) →
      StatementAt d e start count (.ok (n, ⟨e.base, e.prefixes ++ [decl]⟩, []))
  | sparqlBaseFails {f} : OpeningAt d.bs start (.ok .sparqlBase) →
      BaseDeclaration d.bs e.base d.termLimit (start + 4) (.error f) → StatementAt d e start count (.error f)
  | sparqlBase {b n} : OpeningAt d.bs start (.ok .sparqlBase) →
      BaseDeclaration d.bs e.base d.termLimit (start + 4) (.ok (b, n)) →
      StatementAt d e start count (.ok (n, ⟨b, e.prefixes⟩, []))
  | triplesFails {f} : OpeningAt d.bs start (.ok .triples) → TriplesAt (d.at e) start count (.error f) →
      StatementAt d e start count (.error f)
  | triplesPeriodFails {n ts f} : OpeningAt d.bs start (.ok .triples) →
      TriplesAt (d.at e) start count (.ok (n, ts)) → PeriodAt d.bs n (.error f) →
      StatementAt d e start count (.error f)
  | triples {n ts m} : OpeningAt d.bs start (.ok .triples) → TriplesAt (d.at e) start count (.ok (n, ts)) →
      PeriodAt d.bs n (.ok m) → StatementAt d e start count (.ok (m, e, ts))

/-- The statements from `position` to the end of the document, after `count`
    triples, and their triples. -/
inductive StatementsAt (d : Doc) : Env → Nat → Nat → Except Fault (List Spo) → Prop
  | spaceFails {e position count f} : TriviaFault d.bs position f → StatementsAt d e position count (.error f)
  | finish {e position count} : TriviaRuns d.bs true position d.bs.length →
      StatementsAt d e position count (.ok [])
  | statementFails {e position count p f} : TriviaRuns d.bs true position p → p < d.bs.length →
      StatementAt d e p count (.error f) → StatementsAt d e position count (.error f)
  | restFails {e position count p m e' ts f} : TriviaRuns d.bs true position p → p < d.bs.length →
      StatementAt d e p count (.ok (m, e', ts)) → StatementsAt d e' m (count + ts.length) (.error f) →
      StatementsAt d e position count (.error f)
  | more {e position count p m e' ts us} : TriviaRuns d.bs true position p → p < d.bs.length →
      StatementAt d e p count (.ok (m, e', ts)) → StatementsAt d e' m (count + ts.length) (.ok us) →
      StatementsAt d e position count (.ok (ts ++ us))

/-- The bytes `bs` are a Turtle document that, read against `base` with blank
    nodes of the scope `scope`, denotes the triples `ts` in order; every term
    fits `termLimit` bytes and there are at most `tripleLimit` triples. -/
def Document (bs scope base : List U8) (termLimit tripleLimit : Nat) (ts : List Spo) : Prop :=
  StatementsAt ⟨bs, scope, termLimit, tripleLimit⟩ ⟨base, []⟩ 0 0 (.ok ts)

/-- Reading the bytes `bs` fails first with `f`. -/
def DocumentError (bs scope base : List U8) (termLimit tripleLimit : Nat) (f : Fault) : Prop :=
  StatementsAt ⟨bs, scope, termLimit, tripleLimit⟩ ⟨base, []⟩ 0 0 (.error f)


/-! ## The reader's context and results -/

/-- The context of the reader's context. -/
def ctxOf (cx : turtle.Context) : Context :=
  ⟨cx.bytes.val, cx.scope.val, cx.base.val, declarations cx.prefixes.val, cx.limits.max_term_bytes.val,
    cx.limits.max_triples.val⟩

/-- A node result agrees with an outcome: the same node, end and new triples
    after the triples `out`, or the same failure. -/
def GrownAgrees {A : Type} (view : A → Term) (out : List rdf.Triple) :
    core.result.Result (A × Usize × alloc.vec.Vec rdf.Triple) turtle.ReadError →
      Except Fault (Term × Nat × List Spo) → Prop
  | .Ok (a, n, out'), .ok (t, m, ts) => view a = t ∧ n.val = m ∧ out'.val.map spo = out.map spo ++ ts
  | .Err e, .error f => faultOf e = f
  | _, _ => False

/-- A result without a node agrees with an outcome: the same end and new
    triples, or the same failure. -/
def EmittedAgrees (out : List rdf.Triple) :
    core.result.Result (Usize × alloc.vec.Vec rdf.Triple) turtle.ReadError → Except Fault (Nat × List Spo) → Prop
  | .Ok (n, out'), .ok (m, ts) => n.val = m ∧ out'.val.map spo = out.map spo ++ ts
  | .Err e, .error f => faultOf e = f
  | _, _ => False

/-- A bracket result agrees with an outcome. -/
def BracketAgrees (out : List rdf.Triple) :
    core.result.Result (rdf.BlankNode × Usize × alloc.vec.Vec rdf.Triple × Bool) turtle.ReadError →
      Except Fault (Term × Nat × List Spo × Bool) → Prop
  | .Ok (b, n, out', l), .ok (t, m, ts, l') =>
      Term.blank b.scope.val b.label.val = t ∧ n.val = m ∧ out'.val.map spo = out.map spo ++ ts ∧ l = l'
  | .Err e, .error f => faultOf e = f
  | _, _ => False

theorem grown_ok {A : Type} {view : A → Term} {out : List rdf.Triple} {a : A} {n : Usize}
    {out' : alloc.vec.Vec rdf.Triple} {o : Except Fault (Term × Nat × List Spo)}
    (h : GrownAgrees view out (.Ok (a, n, out')) o) :
    ∃ ts, o = .ok (view a, n.val, ts) ∧ out'.val.map spo = out.map spo ++ ts := by
  cases o with
  | error f => exact False.elim h
  | ok v =>
    obtain ⟨t, m, ts⟩ := v
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨ts, by rw [h1, h2], h3⟩

theorem grown_err {A : Type} {view : A → Term} {out : List rdf.Triple} {e : turtle.ReadError}
    {o : Except Fault (Term × Nat × List Spo)} (h : GrownAgrees view out (.Err e) o) : o = .error (faultOf e) := by
  cases o with
  | error f => simp only [GrownAgrees] at h; rw [h]
  | ok v => exact False.elim h

theorem emitted_ok {out : List rdf.Triple} {n : Usize} {out' : alloc.vec.Vec rdf.Triple}
    {o : Except Fault (Nat × List Spo)} (h : EmittedAgrees out (.Ok (n, out')) o) :
    ∃ ts, o = .ok (n.val, ts) ∧ out'.val.map spo = out.map spo ++ ts := by
  cases o with
  | error f => exact False.elim h
  | ok v =>
    obtain ⟨m, ts⟩ := v
    obtain ⟨h1, h2⟩ := h
    exact ⟨ts, by rw [h1], h2⟩

theorem emitted_err {out : List rdf.Triple} {e : turtle.ReadError} {o : Except Fault (Nat × List Spo)}
    (h : EmittedAgrees out (.Err e) o) : o = .error (faultOf e) := by
  cases o with
  | error f => simp only [EmittedAgrees] at h; rw [h]
  | ok v => exact False.elim h

theorem bracket_ok {out : List rdf.Triple} {b : rdf.BlankNode} {n : Usize} {out' : alloc.vec.Vec rdf.Triple}
    {l : Bool} {o : Except Fault (Term × Nat × List Spo × Bool)} (h : BracketAgrees out (.Ok (b, n, out', l)) o) :
    ∃ ts, o = .ok (.blank b.scope.val b.label.val, n.val, ts, l) ∧ out'.val.map spo = out.map spo ++ ts := by
  cases o with
  | error f => exact False.elim h
  | ok v =>
    obtain ⟨t, m, ts, l'⟩ := v
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨ts, by rw [h1, h2, h4], h3⟩

theorem bracket_err {out : List rdf.Triple} {e : turtle.ReadError} {o : Except Fault (Term × Nat × List Spo × Bool)}
    (h : BracketAgrees out (.Err e) o) : o = .error (faultOf e) := by
  cases o with
  | error f => simp only [BracketAgrees] at h; rw [h]
  | ok v => exact False.elim h

/-! ## Copies, constants and labels -/

theorem copy_iri_spec (iri : rdf.RdfIri) : turtle.copy_iri iri = .ok iri := by
  simp [turtle.copy_iri, copy_bytes_spec]

theorem copy_subject_spec (s : rdf.Subject) : turtle.copy_subject s = .ok s := by
  cases s <;> simp [turtle.copy_subject, copy_iri_spec, copy_bytes_spec]

/-- The object that is a subject node. -/
def objectOf : rdf.Subject → rdf.Object
  | .Iri v => .Iri v
  | .Blank b => .Blank b

theorem object_of_spec (s : rdf.Subject) : turtle.object_of s = .ok (objectOf s) := by
  cases s <;> rfl

theorem object_of_term (s : rdf.Subject) : objectTerm (objectOf s) = subjectTerm s := by
  cases s <;> rfl

theorem rdf_type_spec : ∃ v, turtle.rdf_type = .ok v ∧ v.spelling.val = RdfTypeBytes := by
  refine ⟨?v, ?run, ?value⟩
  case run => simp [turtle.rdf_type, rdf_iri_eq]; rfl
  case value => simp [slice_array, RdfTypeBytes]

theorem rdf_first_spec : ∃ v, turtle.rdf_first = .ok v ∧ v.spelling.val = RdfFirstBytes := by
  refine ⟨?v, ?run, ?value⟩
  case run => simp [turtle.rdf_first, rdf_iri_eq]; rfl
  case value => simp [slice_array, RdfFirstBytes]

theorem rdf_rest_spec : ∃ v, turtle.rdf_rest = .ok v ∧ v.spelling.val = RdfRestBytes := by
  refine ⟨?v, ?run, ?value⟩
  case run => simp [turtle.rdf_rest, rdf_iri_eq]; rfl
  case value => simp [slice_array, RdfRestBytes]

theorem rdf_nil_spec : ∃ v, turtle.rdf_nil = .ok v ∧ v.spelling.val = RdfNilBytes := by
  refine ⟨?v, ?run, ?value⟩
  case run => simp [turtle.rdf_nil, rdf_iri_eq]; rfl
  case value => simp [slice_array, RdfNilBytes]

theorem usize_max_bound : Usize.max ≤ 18446744073709551615 := by
  have := System.Platform.numBits_eq
  rcases this with h | h <;> simp [Usize.max, Usize.numBits, h]

theorem usize_max_large : 4294967295 ≤ Usize.max := by
  have := System.Platform.numBits_eq
  rcases this with h | h <;> simp [Usize.max, Usize.numBits, h]

theorem decimal_short (k : Nat) : ∀ n, n < 10 ^ (k + 1) → (Decimal n).length ≤ k + 1 := by
  induction k with
  | zero =>
    intro n small
    rw [Decimal, if_pos (by simpa using small)]
    simp
  | succ k ih =>
    intro n small
    rw [Decimal]
    split_ifs with one
    · simp
    · have := ih (n / 10) (by rw [pow_succ] at small; omega)
      simp
      omega

theorem decimal_length (n : Nat) (bound : n ≤ Usize.max) : (Decimal n).length ≤ 20 := by
  apply decimal_short 19
  have := usize_max_bound
  omega

theorem digit_byte_eq (n : Nat) (byte : U8) (value : byte.val = 48 + n % 10) :
    byte = ⟨BitVec.ofNat 8 (48 + n % 10)⟩ := by
  apply UScalar.eq_of_val_eq
  rw [value]
  show 48 + n % 10 = (BitVec.ofNat 8 (48 + n % 10)).toNat
  rw [BitVec.toNat_ofNat]
  omega

theorem digits_spec (number : Usize) (out : alloc.vec.Vec U8) (room : out.val.length + 20 ≤ Usize.max) :
    ∃ v, turtle.digits number out = .ok v ∧ v.val = out.val ++ Decimal number.val := by
  rw [turtle.digits]
  have u8max : U8.max = 255 := by simp [U8.max, U8.numBits]
  have v48 : (48#u8 : U8).val = 48 := rfl
  obtain ⟨digit, mod, digitValue⟩ := WP.spec_imp_exists (Usize.rem_spec (x := number) (y := 10#usize) (by simp))
  have digitIs : digit.val = number.val % 10 := by simpa using digitValue
  have castIs : (UScalar.cast .U8 digit).val = number.val % 10 := by
    simp [UScalar.cast_val_eq, digitIs]
    omega
  obtain ⟨byte, add, byteValue⟩ := WP.spec_imp_exists (U8.add_spec (x := 48#u8) (y := UScalar.cast .U8 digit)
    (by rw [castIs, v48, u8max]; omega))
  have byteIs : byte = ⟨BitVec.ofNat 8 (48 + number.val % 10)⟩ :=
    digit_byte_eq number.val byte (by rw [byteValue, v48, castIs])
  by_cases small : number.val < 10
  · obtain ⟨v, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out byte (by omega))
    refine ⟨v, by simp [UScalar.lt_equiv, small, mod, add, push], ?_⟩
    rw [contents, byteIs]
    conv_rhs => rw [Decimal, if_pos small]
    simp
  · obtain ⟨quotient, div, quotientValue⟩ := WP.spec_imp_exists (Usize.div_spec (x := number) (y := 10#usize) (by simp))
    have quotientIs : quotient.val = number.val / 10 := by simpa using quotientValue
    obtain ⟨prefix_, again, prefixValue⟩ := digits_spec quotient out room
    have prefixLength : prefix_.val.length + 1 ≤ Usize.max := by
      have whole := decimal_length number.val (by scalar_tac)
      rw [Decimal, if_neg small, List.length_append, List.length_singleton] at whole
      rw [prefixValue, List.length_append, quotientIs]
      omega
    obtain ⟨v, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec prefix_ byte (by omega))
    refine ⟨v, by simp [UScalar.lt_equiv, small, div, again, mod, add, push], ?_⟩
    rw [contents, prefixValue, byteIs, quotientIs]
    conv_rhs => rw [Decimal, if_neg small]
    simp
termination_by number.val
decreasing_by
  have := quotientIs
  omega

theorem marked_spec (marker : U8) (number : Usize) :
    ∃ v, turtle.marked marker number = .ok v ∧ v.val = marker :: Decimal number.val := by
  obtain ⟨label, push, contents⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) marker (by simp; have := usize_max_large; omega))
  obtain ⟨v, run, value⟩ := digits_spec number label (by rw [contents]; simp; have := usize_max_large; omega)
  exact ⟨v, by simp [turtle.marked, push, run], by rw [value, contents]; simp⟩

theorem bracket_node_spec (scope : alloc.vec.Vec U8) (start : Usize) :
    ∃ b, turtle.bracket_node scope start = .ok b ∧ b.scope = scope ∧ b.label.val = 255#u8 :: Decimal start.val := by
  obtain ⟨label, run, value⟩ := marked_spec 255#u8 start
  exact ⟨⟨scope, label⟩, by simp [turtle.bracket_node, copy_bytes_spec, run], rfl, value⟩

theorem list_node_spec (scope : alloc.vec.Vec U8) (start : Usize) :
    ∃ b, turtle.list_node scope start = .ok b ∧ b.scope = scope ∧ b.label.val = 254#u8 :: Decimal start.val := by
  obtain ⟨label, run, value⟩ := marked_spec 254#u8 start
  exact ⟨⟨scope, label⟩, by simp [turtle.list_node, copy_bytes_spec, run], rfl, value⟩

theorem emit_spec (triples : alloc.vec.Vec rdf.Triple) (triple : rdf.Triple) (limits : turtle.Limits)
    (position : Usize) :
    ∃ r, turtle.emit triples triple limits position = .ok r ∧
      (triples.val.length < limits.max_triples.val → ∃ out, r = .Ok out ∧ out.val = triples.val ++ [triple]) ∧
      (limits.max_triples.val ≤ triples.val.length → r = .Err ⟨.ResourceLimit, position⟩) := by
  unfold turtle.emit
  by_cases room : triples.val.length < limits.max_triples.val
  · obtain ⟨out, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec triples triple (by have := limits.max_triples.hBounds; scalar_tac))
    exact ⟨.Ok out, by simp [alloc.vec.Vec.len_val, room, push], fun _ => ⟨out, rfl, contents⟩,
      fun full => absurd room (by omega)⟩
  · exact ⟨.Err ⟨.ResourceLimit, position⟩, by simp [alloc.vec.Vec.len_val, room, error_spec],
      fun h => absurd h room, fun _ => rfl⟩


/-! ## Terms and verbs -/

theorem blank_object {r : core.result.Result (rdf.BlankNode × Usize) turtle.ReadError}
    {o : Except Fault (Term × Nat)} (agree : Agrees blankView r o) :
    Agrees objectResult (match r with
      | .Ok (node, next) => .Ok (.Blank node, next)
      | .Err e => .Err e) o := by
  rcases r with ⟨node, next⟩ | e
  · obtain rfl := agrees_ok agree
    rfl
  · obtain rfl := agrees_err agree
    rfl

theorem literal_object {r : core.result.Result (rdf.RdfLiteral × Usize) turtle.ReadError}
    {o : Except Fault (Term × Nat)} (agree : Agrees literalResult r o) :
    Agrees objectResult (match r with
      | .Ok (lit, next) => .Ok (.Literal lit, next)
      | .Err e => .Err e) o := by
  rcases r with ⟨lit, next⟩ | e
  · obtain rfl := agrees_ok agree
    rfl
  · obtain rfl := agrees_err agree
    rfl

theorem term_total_correct (cx : turtle.Context) (start : Usize) (kind : turtle.Start)
    (inside : start.val < cx.bytes.val.length) :
    ∃ r o, turtle.term cx start kind = .ok r ∧ TermAt (ctxOf cx) start.val kind o ∧ Agrees objectResult r o := by
  unfold turtle.term
  cases kind with
  | Iri =>
    obtain ⟨r, o, run, correct, agree⟩ := iri_ref_total_correct cx.bytes start cx.base cx.limits.max_term_bytes
    rcases r with ⟨iri, next⟩ | e
    · obtain rfl := agrees_ok agree
      exact ⟨.Ok (.Iri iri, next), .ok (.iri iri.spelling.val, next.val), by simp [run,
        core.result.Result.Insts.CoreOpsTry.branch], .iri correct, rfl⟩
    · obtain rfl := agrees_err agree
      exact ⟨.Err e, .error (faultOf e), by simp [run, core.result.Result.Insts.CoreOpsTry.branch], .iriFails correct, rfl⟩
  | Blank =>
    obtain ⟨r, o, run, correct, agree⟩ := blank_label_total_correct cx.bytes start cx.scope cx.limits.max_term_bytes inside
    refine ⟨_, o, ?_, .blank correct, blank_object agree⟩
    rcases r with ⟨node, next⟩ | e <;> simp [run, core.result.Result.Insts.CoreOpsTry.branch]
  | Bracket => exact ⟨.Err ⟨.ExpectedObject, start⟩, _, by simp [error_spec], .bracket, rfl⟩
  | Paren => exact ⟨.Err ⟨.ExpectedObject, start⟩, _, by simp [error_spec], .paren, rfl⟩
  | Quote =>
    obtain ⟨r, o, run, correct, agree⟩ := literal_total_correct cx.bytes start cx.base cx.prefixes
      cx.limits.max_term_bytes inside
    refine ⟨_, o, ?_, .literal correct, literal_object agree⟩
    rcases r with ⟨lit, next⟩ | e <;> simp [run, core.result.Result.Insts.CoreOpsTry.branch]
  | Number =>
    obtain ⟨r, o, run, correct, agree⟩ := number_total_correct cx.bytes start cx.limits.max_term_bytes (by omega)
    refine ⟨_, o, ?_, .number correct, literal_object agree⟩
    rcases r with ⟨lit, next⟩ | e <;> simp [run, core.result.Result.Insts.CoreOpsTry.branch]
  | Word =>
    obtain ⟨r, o, run, correct, agree⟩ := word_object_total_correct cx.bytes start cx.prefixes
      cx.limits.max_term_bytes inside
    exact ⟨r, o, run, .word correct, agree⟩
  | Other => exact ⟨.Err ⟨.ExpectedObject, start⟩, _, by simp [error_spec], .other, rfl⟩

theorem term_accepted {cx : turtle.Context} {start : Usize} {kind : turtle.Start}
    (inside : start.val < cx.bytes.val.length) {t : Term} {n : Nat}
    (found : TermAt (ctxOf cx) start.val kind (.ok (t, n))) :
    ∃ v next, turtle.term cx start kind = .ok (.Ok (v, next)) ∧ objectResult (v, next) = (t, n) := by
  unfold turtle.term
  generalize result : (Except.ok (t, n) : Except Fault (Term × Nat)) = given at found
  cases found with
  | iriFails _ => cases result
  | iri found =>
    cases result
    obtain ⟨iri, next, run, hv, hn⟩ := iri_ref_accepted found
    exact ⟨.Iri iri, next, by simp [run, core.result.Result.Insts.CoreOpsTry.branch],
      by simp [objectResult, objectTerm, hv, hn]⟩
  | blank found =>
    subst result
    obtain ⟨node, next, run, value⟩ := blank_label_accepted found
    exact ⟨.Blank node, next, by simp [run, core.result.Result.Insts.CoreOpsTry.branch], value⟩
  | literal found =>
    subst result
    obtain ⟨lit, next, run, value⟩ := literal_accepted inside found
    exact ⟨.Literal lit, next, by simp [run, core.result.Result.Insts.CoreOpsTry.branch], value⟩
  | number found =>
    subst result
    obtain ⟨lit, next, run, value⟩ := number_accepted (by omega) found
    exact ⟨.Literal lit, next, by simp [run, core.result.Result.Insts.CoreOpsTry.branch], value⟩
  | word found =>
    subst result
    obtain ⟨v, next, run, value⟩ := word_object_accepted inside found
    exact ⟨v, next, run, value⟩
  | bracket => cases result
  | paren => cases result
  | other => cases result

theorem term_bound {c : Context} {start : Nat} {kind : turtle.Start} {t : Term} {n : Nat}
    (found : TermAt c start kind (.ok (t, n))) (inside : start < c.bs.length) : start < n ∧ n ≤ c.bs.length := by
  generalize result : (Except.ok (t, n) : Except Fault (Term × Nat)) = given at found
  cases found with
  | iriFails _ => cases result
  | iri found => cases result; exact iri_ref_bound found
  | blank found => subst result; exact blank_label_bound found
  | literal found => subst result; exact literal_bound found
  | number found => subst result; exact number_bound found (by omega)
  | word found => subst result; exact word_object_bound found inside
  | bracket => cases result
  | paren => cases result
  | other => cases result

theorem verb_follows_spec (bytes : alloc.vec.Vec U8) (index : Usize) :
    turtle.verb_follows bytes index = .ok (decide (VerbFollows bytes.val index.val)) := by
  unfold turtle.verb_follows VerbFollows ByteIs
  by_cases more : index.val < bytes.val.length
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, decide_true, if_true, vec_index more,
      vec_index_usize more, bind_ok, List.getElem?_eq_getElem more, Option.map_some, Option.some.injEq, true_and]
    by_cases a : bytes.val[index.val].val = 59
    · simp [a, bne, UScalar.eq_equiv]
    · by_cases b : bytes.val[index.val].val = 46
      · simp [a, b, bne, UScalar.eq_equiv]
      · by_cases d : bytes.val[index.val].val = 93 <;> simp [a, b, d, bne, UScalar.eq_equiv]
  · simp [alloc.vec.Vec.len_val, more]

theorem word_97 : WordStart 97 := by simp [WordStart, Rowl.NTriples.PnBase]

theorem verb_total_correct (cx : turtle.Context) (position : Usize) :
    ∃ r o, turtle.verb cx position = .ok r ∧ VerbAt (ctxOf cx) position.val o ∧ Agrees iriView r o := by
  unfold turtle.verb
  obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct cx.bytes position
  rcases spaced with s | e
  · obtain ⟨needed, neededRun, neededCorrect⟩ := needed_total_correct cx.bytes s
    rcases needed with ⟨cp, next⟩ | e
    · by_cases angle : cp.val = 60
      · obtain ⟨r, o, run, correct, agree⟩ := iri_ref_total_correct cx.bytes s cx.base cx.limits.max_term_bytes
        exact ⟨r, o, by simp [spaceRun, neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, angle,
          run], .iri spaceCorrect (show Unit cx.bytes.val s.val 60 next.val by rw [← angle]; exact neededCorrect)
          correct, agree⟩
      · by_cases word : WordStart cp.val
        · obtain ⟨r, o, colonRun, colonCorrect, agree⟩ := prefix_colon_total_correct cx.bytes s
          rcases r with (_ | colon) | e
          · obtain rfl := agrees_ok agree
            by_cases isA : cp.val = 97
            · obtain ⟨typeIri, typeRun, typeValue⟩ := rdf_type_spec
              refine ⟨.Ok (typeIri, next), .ok (RdfTypeBytes, next.val), ?_,
                .a spaceCorrect (show Unit cx.bytes.val s.val 97 next.val by rw [← isA]; exact neededCorrect)
                  colonCorrect, by simp [Agrees, iriView, typeValue]⟩
              simp [spaceRun, neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, angle,
                word_start_spec, word, word_97, colonRun, turtle.keyword_a, isA, typeRun]
            · refine ⟨.Err ⟨.ExpectedVerb, s⟩, .error (.ExpectedVerb, s.val), ?_,
                .notA spaceCorrect neededCorrect angle word colonCorrect isA, rfl⟩
              simp [spaceRun, neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, angle,
                word_start_spec, word, colonRun, turtle.keyword_a, isA, error_spec]
          · obtain rfl := agrees_ok agree
            obtain ⟨r, o, run, correct, agree⟩ := prefixed_total_correct cx.bytes s colon cx.prefixes
              cx.limits.max_term_bytes colonCorrect
            exact ⟨r, o, by simp [spaceRun, neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv,
              angle, word_start_spec, word, colonRun, run], .prefixed spaceCorrect neededCorrect angle word colonCorrect
              correct, agree⟩
          · obtain rfl := agrees_err agree
            exact ⟨.Err e, .error (faultOf e), by simp [spaceRun, neededRun, core.result.Result.Insts.CoreOpsTry.branch,
              UScalar.eq_equiv, angle, word_start_spec, word, colonRun], .colonFails spaceCorrect neededCorrect angle
              word colonCorrect, rfl⟩
        · exact ⟨.Err ⟨.ExpectedVerb, s⟩, .error (.ExpectedVerb, s.val), by simp [spaceRun, neededRun,
            core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, angle, word_start_spec, word, error_spec],
            .other spaceCorrect neededCorrect angle word, rfl⟩
    · exact ⟨.Err e, .error (faultOf e), by simp [spaceRun, neededRun, core.result.Result.Insts.CoreOpsTry.branch],
        .missing spaceCorrect neededCorrect, rfl⟩
  · exact ⟨.Err e, .error (faultOf e), by simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch],
      .spaceFails spaceCorrect, rfl⟩

theorem verb_accepted {cx : turtle.Context} {position : Usize} {pr : List U8} {n : Nat}
    (found : VerbAt (ctxOf cx) position.val (.ok (pr, n))) :
    ∃ iri next, turtle.verb cx position = .ok (.Ok (iri, next)) ∧ iri.spelling.val = pr ∧ next.val = n := by
  unfold turtle.verb
  generalize result : (Except.ok (pr, n) : Except Fault (List U8 × Nat)) = given at found
  cases found with
  | spaceFails _ => cases result
  | missing _ _ => cases result
  | @iri s q r spaced u found =>
    subst result
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    obtain ⟨cp, next, neededRun, hc, hn⟩ := needed_at u
    obtain ⟨iri, finish, run, hv, hf⟩ := iri_ref_accepted (limit := cx.limits.max_term_bytes) found
    exact ⟨iri, finish, by simp [spaceRun, neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv, hc,
      run], hv, hf⟩
  | colonFails _ _ _ _ _ => cases result
  | @prefixed s ch q colon r spaced u notAngle word colonFound named =>
    subst result
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    obtain ⟨cp, next, neededRun, hc, hn⟩ := needed_at u
    obtain ⟨c, colonRun, colonValue⟩ := prefix_colon_accepted colonFound
    cases c with
    | none => simp at colonValue
    | some colon' =>
      simp only [Option.map_some, Option.some.injEq] at colonValue
      subst colonValue
      subst hc
      obtain ⟨iri, finish, run, hv, hf⟩ := prefixed_accepted (bytes := cx.bytes) (start := stop) (colon := colon')
        (prefixes := cx.prefixes) (limit := cx.limits.max_term_bytes) colonFound named
      exact ⟨iri, finish, by simp [spaceRun, neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv,
        notAngle, word_start_spec, word, colonRun, run], hv, hf⟩
  | @a s q spaced u colonFound =>
    cases result
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    obtain ⟨cp, next, neededRun, hc, hn⟩ := needed_at u
    obtain ⟨c, colonRun, colonValue⟩ := prefix_colon_accepted colonFound
    cases c with
    | some _ => simp at colonValue
    | none =>
      obtain ⟨typeIri, typeRun, typeValue⟩ := rdf_type_spec
      exact ⟨typeIri, next, by simp [spaceRun, neededRun, core.result.Result.Insts.CoreOpsTry.branch, UScalar.eq_equiv,
        hc, word_start_spec, word_97, colonRun, turtle.keyword_a, typeRun], typeValue, hn⟩
  | notA _ _ _ _ _ _ => cases result
  | other _ _ _ _ => cases result

theorem verb_bound {c : Context} {position : Nat} {pr : List U8} {n : Nat}
    (found : VerbAt c position (.ok (pr, n))) : position < n ∧ n ≤ c.bs.length := by
  generalize result : (Except.ok (pr, n) : Except Fault (List U8 × Nat)) = given at found
  cases found with
  | spaceFails _ => cases result
  | missing _ _ => cases result
  | iri spaced u found =>
    subst result
    have := trivia_bound spaced
    have := iri_ref_bound found
    omega
  | colonFails _ _ _ _ _ => cases result
  | prefixed spaced u notAngle word colonFound named =>
    subst result
    have := trivia_bound spaced
    have colonBound := prefix_colon_bound colonFound
    have := prefixed_bound named colonBound.2
    omega
  | a spaced u colonFound =>
    cases result
    have := trivia_bound spaced
    have := unit_progress u
    omega
  | notA _ _ _ _ _ _ => cases result
  | other _ _ _ _ => cases result


/-! ## Objects, property lists and collections in the grammar are read -/

theorem add_one {bytes : alloc.vec.Vec U8} {x : Usize} (inside : x.val < bytes.val.length) :
    ∃ y : Usize, (x + 1#usize : Result Usize) = .ok y ∧ y.val = x.val + 1 := by
  obtain ⟨y, add, value⟩ := WP.spec_imp_exists (Usize.add_spec (x := x) (y := 1#usize)
    (by have := bytes.property; scalar_tac))
  exact ⟨y, add, by simpa using value⟩

theorem map_length {out out' : alloc.vec.Vec rdf.Triple} {ts : List Spo}
    (contents : out'.val.map spo = out.val.map spo ++ ts) : out'.val.length = out.val.length + ts.length := by
  simpa using congrArg List.length contents

theorem grown_intro {A : Type} {view : A → Term} {out : List rdf.Triple} {a : A} {n : Usize}
    {out' : alloc.vec.Vec rdf.Triple} {ts : List Spo} (contents : out'.val.map spo = out.map spo ++ ts) :
    GrownAgrees view out (.Ok (a, n, out')) (.ok (view a, n.val, ts)) := ⟨rfl, rfl, contents⟩

theorem emitted_intro {out : List rdf.Triple} {n : Usize} {out' : alloc.vec.Vec rdf.Triple} {ts : List Spo}
    (contents : out'.val.map spo = out.map spo ++ ts) : EmittedAgrees out (.Ok (n, out')) (.ok (n.val, ts)) :=
  ⟨rfl, contents⟩

theorem bracket_intro {out : List rdf.Triple} {b : rdf.BlankNode} {n : Usize} {out' : alloc.vec.Vec rdf.Triple}
    {l : Bool} {ts : List Spo} (contents : out'.val.map spo = out.map spo ++ ts) :
    BracketAgrees out (.Ok (b, n, out', l)) (.ok (.blank b.scope.val b.label.val, n.val, ts, l)) :=
  ⟨rfl, rfl, contents, rfl⟩

theorem node_missing {cx : turtle.Context} {start : Usize} {out : alloc.vec.Vec rdf.Triple} {e : turtle.ReadError}
    (neededRun : turtle.needed cx.bytes start = .ok (.Err e)) : turtle.node cx start out = .ok (.Err e) := by
  rw [turtle.node]
  simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch]

theorem node_term_ok {cx : turtle.Context} {start : Usize} {out : alloc.vec.Vec rdf.Triple} {cp : U32}
    {next : Usize} {value : rdf.Object} {finish : Usize}
    (neededRun : turtle.needed cx.bytes start = .ok (.Ok (cp, next)))
    (notBracket : StartOf cp.val ≠ .Bracket) (notParen : StartOf cp.val ≠ .Paren)
    (termRun : turtle.term cx start (StartOf cp.val) = .ok (.Ok (value, finish))) :
    turtle.node cx start out = .ok (.Ok (value, finish, out)) := by
  rw [turtle.node]
  simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec]
  split <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch]

theorem node_term_err {cx : turtle.Context} {start : Usize} {out : alloc.vec.Vec rdf.Triple} {cp : U32}
    {next : Usize} {e : turtle.ReadError}
    (neededRun : turtle.needed cx.bytes start = .ok (.Ok (cp, next)))
    (notBracket : StartOf cp.val ≠ .Bracket) (notParen : StartOf cp.val ≠ .Paren)
    (termRun : turtle.term cx start (StartOf cp.val) = .ok (.Err e)) :
    turtle.node cx start out = .ok (.Err e) := by
  rw [turtle.node]
  simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec]
  split <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch]

theorem node_bracket_ok {cx : turtle.Context} {start : Usize} {out : alloc.vec.Vec rdf.Triple} {cp : U32}
    {next : Usize} {b : rdf.BlankNode} {finish : Usize} {out' : alloc.vec.Vec rdf.Triple} {l : Bool}
    (neededRun : turtle.needed cx.bytes start = .ok (.Ok (cp, next))) (isBracket : StartOf cp.val = .Bracket)
    (bracketRun : turtle.bracket cx start out = .ok (.Ok (b, finish, out', l))) :
    turtle.node cx start out = .ok (.Ok (.Blank b, finish, out')) := by
  rw [turtle.node]
  simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, isBracket, bracketRun]

theorem node_bracket_err {cx : turtle.Context} {start : Usize} {out : alloc.vec.Vec rdf.Triple} {cp : U32}
    {next : Usize} {e : turtle.ReadError}
    (neededRun : turtle.needed cx.bytes start = .ok (.Ok (cp, next))) (isBracket : StartOf cp.val = .Bracket)
    (bracketRun : turtle.bracket cx start out = .ok (.Err e)) :
    turtle.node cx start out = .ok (.Err e) := by
  rw [turtle.node]
  simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, isBracket, bracketRun]

theorem node_paren_ok {cx : turtle.Context} {start : Usize} {out : alloc.vec.Vec rdf.Triple} {cp : U32}
    {next : Usize} {s : rdf.Subject} {finish : Usize} {out' : alloc.vec.Vec rdf.Triple}
    (neededRun : turtle.needed cx.bytes start = .ok (.Ok (cp, next))) (isParen : StartOf cp.val = .Paren)
    (collectionRun : turtle.collection cx start out = .ok (.Ok (s, finish, out'))) :
    turtle.node cx start out = .ok (.Ok (objectOf s, finish, out')) := by
  rw [turtle.node]
  simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, isParen, collectionRun, object_of_spec]

theorem node_paren_err {cx : turtle.Context} {start : Usize} {out : alloc.vec.Vec rdf.Triple} {cp : U32}
    {next : Usize} {e : turtle.ReadError}
    (neededRun : turtle.needed cx.bytes start = .ok (.Ok (cp, next))) (isParen : StartOf cp.val = .Paren)
    (collectionRun : turtle.collection cx start out = .ok (.Err e)) :
    turtle.node cx start out = .ok (.Err e) := by
  rw [turtle.node]
  simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, isParen, collectionRun]

theorem bracket_term (cx : turtle.Context) (start : Usize) {node : rdf.BlankNode} (scopeIs : node.scope = cx.scope)
    (labelIs : node.label.val = 255#u8 :: Decimal start.val) :
    Term.blank node.scope.val node.label.val = bracketTerm (ctxOf cx) start.val := by
  simp [bracketTerm, ctxOf, scopeIs, labelIs]

theorem list_term (cx : turtle.Context) (start : Usize) {node : rdf.BlankNode} (scopeIs : node.scope = cx.scope)
    (labelIs : node.label.val = 254#u8 :: Decimal start.val) :
    Term.blank node.scope.val node.label.val = listTerm (ctxOf cx) start.val := by
  simp [listTerm, ctxOf, scopeIs, labelIs]

mutual

theorem node_accepted (cx : turtle.Context) (start : Usize) (out : alloc.vec.Vec rdf.Triple) {t : Term} {n : Nat}
    {ts : List Spo} (found : NodeAt (ctxOf cx) start.val out.val.length (.ok (t, n, ts))) :
    ∃ v next out', turtle.node cx start out = .ok (.Ok (v, next, out')) ∧ objectTerm v = t ∧ next.val = n ∧
      out'.val.map spo = out.val.map spo ++ ts ∧ start.val < n ∧ n ≤ cx.bytes.val.length := by
  generalize result : (Except.ok (t, n, ts) : Except Fault (Term × Nat × List Spo)) = given at found
  cases found with
  | missing _ => cases result
  | termFails _ _ _ _ => cases result
  | term u notBracket notParen termFound =>
    cases result
    have u : Unit cx.bytes.val start.val _ _ := u
    have inside := unit_progress u
    obtain ⟨cp, next, neededRun, hc, _⟩ := needed_at u
    subst hc
    obtain ⟨v, finish, termRun, value⟩ := term_accepted (cx := cx) (start := start) (by omega) termFound
    have bound : start.val < _ ∧ _ ≤ cx.bytes.val.length := term_bound termFound (by show start.val < cx.bytes.val.length; omega)
    simp only [objectResult, Prod.mk.injEq] at value
    exact ⟨v, finish, out, node_term_ok neededRun notBracket notParen termRun, value.1, value.2, by simp,
      bound.1, bound.2⟩
  | bracketFails _ _ _ => cases result
  | bracket u isBracket bracketFound =>
    cases result
    have u : Unit cx.bytes.val start.val _ _ := u
    obtain ⟨cp, next, neededRun, hc, _⟩ := needed_at u
    subst hc
    obtain ⟨b, finish, out', bracketRun, value, rest⟩ := bracket_accepted cx start out bracketFound
    exact ⟨.Blank b, finish, out', node_bracket_ok neededRun isBracket bracketRun, value, rest⟩
  | collection u isParen collectionFound =>
    subst result
    have u : Unit cx.bytes.val start.val _ _ := u
    obtain ⟨cp, next, neededRun, hc, _⟩ := needed_at u
    subst hc
    obtain ⟨s, finish, out', collectionRun, value, rest⟩ := collection_accepted cx start out collectionFound
    exact ⟨objectOf s, finish, out', node_paren_ok neededRun isParen collectionRun,
      by rw [object_of_term]; exact value, rest⟩
termination_by 5 * (cx.bytes.val.length - start.val) + 1
decreasing_by all_goals omega

theorem bracket_accepted (cx : turtle.Context) (start : Usize) (out : alloc.vec.Vec rdf.Triple) {t : Term} {n : Nat}
    {ts : List Spo} {l : Bool} (found : BracketAt (ctxOf cx) start.val out.val.length (.ok (t, n, ts, l))) :
    ∃ b next out', turtle.bracket cx start out = .ok (.Ok (b, next, out', l)) ∧
      Term.blank b.scope.val b.label.val = t ∧ next.val = n ∧ out'.val.map spo = out.val.map spo ++ ts ∧
      start.val < n ∧ n ≤ cx.bytes.val.length := by
  obtain ⟨node, nodeRun, scopeIs, labelIs⟩ := bracket_node_spec cx.scope start
  have nodeTerm := bracket_term cx start scopeIs labelIs
  generalize result : (Except.ok (t, n, ts, l) : Except Fault (Term × Nat × List Spo × Bool)) = given at found
  cases found with
  | spaceFails _ => cases result
  | @anon _ _ p spaced closing =>
    cases result
    simp only [ctxOf] at spaced closing
    have bound := trivia_bound spaced
    have inside := byte_inside closing
    obtain ⟨i, add, iValue⟩ := add_one (bytes := cx.bytes) (x := start) (by omega)
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs (bytes := cx.bytes) (position := i) (by rw [iValue]; exact spaced)
    subst stopValue
    obtain ⟨j, add2, jValue⟩ := add_one (bytes := cx.bytes) (x := stop) inside
    refine ⟨node, j, out, ?_, nodeTerm, jValue, by simp, by omega, by omega⟩
    rw [turtle.bracket]
    simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, closing, nodeRun, add2]
  | listFails _ _ _ => cases result
  | closeFails _ _ _ _ => cases result
  | unclosed _ _ _ _ _ => cases result
  | @list _ _ p q ts' e spaced opening listFound closeSpaced closing =>
    cases result
    simp only [ctxOf] at spaced opening closeSpaced closing
    have bound := trivia_bound spaced
    obtain ⟨i, add, iValue⟩ := add_one (bytes := cx.bytes) (x := start) (by omega)
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs (bytes := cx.bytes) (position := i) (by rw [iValue]; exact spaced)
    subst stopValue
    rw [← nodeTerm] at listFound
    obtain ⟨after, out1, listRun, afterValue, contents, lower, upper⟩ :=
      predicate_object_list_accepted cx stop (.Blank node) out listFound
    subst afterValue
    have closeBound := trivia_bound closeSpaced
    have inside := byte_inside closing
    obtain ⟨close, closeRun, closeValue⟩ := space_runs closeSpaced
    subst closeValue
    obtain ⟨j, add2, jValue⟩ := add_one (bytes := cx.bytes) (x := close) inside
    refine ⟨node, j, out1, ?_, nodeTerm, jValue, contents, by omega, by omega⟩
    rw [turtle.bracket]
    simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, opening, nodeRun, listRun,
      closeRun, closing, add2]
termination_by 5 * (cx.bytes.val.length - start.val)
decreasing_by all_goals omega

theorem collection_accepted (cx : turtle.Context) (start : Usize) (out : alloc.vec.Vec rdf.Triple) {t : Term}
    {n : Nat} {ts : List Spo} (found : CollectionAt (ctxOf cx) start.val out.val.length (.ok (t, n, ts))) :
    ∃ s next out', turtle.collection cx start out = .ok (.Ok (s, next, out')) ∧ subjectTerm s = t ∧ next.val = n ∧
      out'.val.map spo = out.val.map spo ++ ts ∧ start.val < n ∧ n ≤ cx.bytes.val.length := by
  generalize result : (Except.ok (t, n, ts) : Except Fault (Term × Nat × List Spo)) = given at found
  cases found with
  | spaceFails _ => cases result
  | @empty _ _ p spaced closing =>
    cases result
    simp only [ctxOf] at spaced closing
    have bound := trivia_bound spaced
    have inside := byte_inside closing
    obtain ⟨i, add, iValue⟩ := add_one (bytes := cx.bytes) (x := start) (by omega)
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs (bytes := cx.bytes) (position := i) (by rw [iValue]; exact spaced)
    subst stopValue
    obtain ⟨j, add2, jValue⟩ := add_one (bytes := cx.bytes) (x := stop) inside
    obtain ⟨nil, nilRun, nilValue⟩ := rdf_nil_spec
    refine ⟨.Iri nil, j, out, ?_, by simp [subjectTerm, nilValue], jValue, by simp, by omega, by omega⟩
    rw [turtle.collection]
    simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, closing, nilRun, add2]
  | firstFails _ _ _ => cases result
  | restFails _ _ _ _ => cases result
  | @list _ _ p q ts' m us spaced opening memberFound membersFound =>
    cases result
    simp only [ctxOf] at spaced opening
    have bound := trivia_bound spaced
    obtain ⟨i, add, iValue⟩ := add_one (bytes := cx.bytes) (x := start) (by omega)
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs (bytes := cx.bytes) (position := i) (by rw [iValue]; exact spaced)
    subst stopValue
    obtain ⟨after, out1, memberRun, afterValue, contents1, lower, upper⟩ := member_accepted cx stop out memberFound
    have length1 := map_length contents1
    subst afterValue
    rw [← length1] at membersFound
    obtain ⟨finish, out2, membersRun, finishValue, contents2, lower2, upper2⟩ :=
      members_accepted cx after stop out1 membersFound
    obtain ⟨node, nodeRun, scopeIs, labelIs⟩ := list_node_spec cx.scope stop
    refine ⟨.Blank node, finish, out2, ?_, list_term cx stop scopeIs labelIs, finishValue,
      by rw [contents2, contents1, List.append_assoc], by omega, by omega⟩
    rw [turtle.collection]
    simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, opening, memberRun, membersRun,
      nodeRun]
termination_by 5 * (cx.bytes.val.length - start.val)
decreasing_by all_goals omega

theorem member_accepted (cx : turtle.Context) (start : Usize) (out : alloc.vec.Vec rdf.Triple) {n : Nat}
    {ts : List Spo}
    (found : ObjectAt (ctxOf cx) (listTerm (ctxOf cx) start.val) RdfFirstBytes start.val out.val.length (.ok (n, ts))) :
    ∃ next out', turtle.member cx start out = .ok (.Ok (next, out')) ∧ next.val = n ∧
      out'.val.map spo = out.val.map spo ++ ts ∧ start.val < n ∧ n ≤ cx.bytes.val.length := by
  obtain ⟨node, nodeRun, scopeIs, labelIs⟩ := list_node_spec cx.scope start
  obtain ⟨first, firstRun, firstValue⟩ := rdf_first_spec
  rw [← list_term cx start scopeIs labelIs, ← firstValue] at found
  obtain ⟨next, out', run, rest⟩ := object_accepted cx start (.Blank node) first out found
  exact ⟨next, out', by rw [turtle.member]; simp [nodeRun, firstRun, run], rest⟩
termination_by 5 * (cx.bytes.val.length - start.val) + 3
decreasing_by all_goals omega

theorem members_accepted (cx : turtle.Context) (position last : Usize) (out : alloc.vec.Vec rdf.Triple) {n : Nat}
    {ts : List Spo} (found : MembersAt (ctxOf cx) position.val last.val out.val.length (.ok (n, ts))) :
    ∃ next out', turtle.members cx position last out = .ok (.Ok (next, out')) ∧ next.val = n ∧
      out'.val.map spo = out.val.map spo ++ ts ∧ position.val < n ∧ n ≤ cx.bytes.val.length := by
  obtain ⟨link, linkRun, linkScope, linkLabel⟩ := list_node_spec cx.scope last
  have linkTerm := list_term cx last linkScope linkLabel
  obtain ⟨rest, restRun, restValue⟩ := rdf_rest_spec
  generalize result : (Except.ok (n, ts) : Except Fault (Nat × List Spo)) = given at found
  cases found with
  | spaceFails _ => cases result
  | closeFull _ _ _ => cases result
  | @close _ _ _ p spaced closing room =>
    cases result
    simp only [ctxOf] at spaced closing room
    have bound := trivia_bound spaced
    have inside := byte_inside closing
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    obtain ⟨nil, nilRun, nilValue⟩ := rdf_nil_spec
    obtain ⟨r, emitRun, emitOk, _⟩ := emit_spec out ⟨.Blank link, rest, .Iri nil⟩ cx.limits stop
    obtain ⟨out', rfl, contents⟩ := emitOk room
    obtain ⟨j, add, jValue⟩ := add_one (bytes := cx.bytes) (x := stop) inside
    refine ⟨j, out', ?_, jValue, ?_, by omega, by omega⟩
    · rw [turtle.members]
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, linkRun, byte_is_spec, closing, restRun, nilRun,
        emitRun, add]
    · rw [contents]
      simp [spo, subjectTerm, objectTerm, linkTerm, restValue, nilValue]
  | linkFull _ _ _ => cases result
  | memberFails _ _ _ _ => cases result
  | restFails _ _ _ _ _ => cases result
  | @more _ _ _ p q ts' m us spaced opening room memberFound membersFound =>
    cases result
    simp only [ctxOf] at spaced opening room
    have bound := trivia_bound spaced
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    obtain ⟨node, nodeRun, nodeScope, nodeLabel⟩ := list_node_spec cx.scope stop
    have nodeTerm := list_term cx stop nodeScope nodeLabel
    obtain ⟨r, emitRun, emitOk, _⟩ := emit_spec out ⟨.Blank link, rest, .Blank node⟩ cx.limits stop
    obtain ⟨out1, rfl, contents1⟩ := emitOk room
    have length1 : out1.val.length = out.val.length + 1 := by rw [contents1]; simp
    rw [← length1] at memberFound
    obtain ⟨after, out2, memberRun, afterValue, contents2, lower, upper⟩ := member_accepted cx stop out1 memberFound
    have length2 := map_length contents2
    subst afterValue
    rw [← length1, ← length2] at membersFound
    obtain ⟨finish, out3, membersRun, finishValue, contents3, lower2, upper2⟩ :=
      members_accepted cx after stop out2 membersFound
    refine ⟨finish, out3, ?_, finishValue, ?_, by omega, by omega⟩
    · rw [turtle.members]
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, linkRun, byte_is_spec, opening, restRun, nodeRun,
        emitRun, memberRun, membersRun]
    · rw [contents3, contents2, contents1]
      simp [spo, subjectTerm, objectTerm, linkTerm, restValue, nodeTerm]
termination_by 5 * (cx.bytes.val.length - position.val) + 4
decreasing_by all_goals omega

theorem object_accepted (cx : turtle.Context) (position : Usize) (subject : rdf.Subject) (predicate : rdf.RdfIri)
    (out : alloc.vec.Vec rdf.Triple) {n : Nat} {ts : List Spo}
    (found : ObjectAt (ctxOf cx) (subjectTerm subject) predicate.spelling.val position.val out.val.length
      (.ok (n, ts))) :
    ∃ next out', turtle.object cx position subject predicate out = .ok (.Ok (next, out')) ∧ next.val = n ∧
      out'.val.map spo = out.val.map spo ++ ts ∧ position.val < n ∧ n ≤ cx.bytes.val.length := by
  generalize result : (Except.ok (n, ts) : Except Fault (Nat × List Spo)) = given at found
  cases found with
  | spaceFails _ => cases result
  | nodeFails _ _ => cases result
  | full _ _ _ => cases result
  | @object _ _ _ _ p t m ts' spaced nodeFound room =>
    cases result
    simp only [ctxOf] at spaced room
    have bound := trivia_bound spaced
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    obtain ⟨v, next, out1, nodeRun, value, nextValue, contents1, lower, upper⟩ := node_accepted cx stop out nodeFound
    have length1 := map_length contents1
    obtain ⟨r, emitRun, emitOk, _⟩ := emit_spec out1 ⟨subject, predicate, v⟩ cx.limits stop
    obtain ⟨out2, rfl, contents2⟩ := emitOk (by rw [length1]; exact room)
    refine ⟨next, out2, ?_, nextValue, ?_, by omega, by omega⟩
    · rw [turtle.object]
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, nodeRun, copy_subject_spec, copy_iri_spec, emitRun]
    · rw [contents2, List.map_append, contents1, ← value]
      simp [spo]
termination_by 5 * (cx.bytes.val.length - position.val) + 2
decreasing_by all_goals omega

theorem object_list_accepted (cx : turtle.Context) (position : Usize) (subject : rdf.Subject)
    (predicate : rdf.RdfIri) (out : alloc.vec.Vec rdf.Triple) {n : Nat} {ts : List Spo}
    (found : ObjectsAt (ctxOf cx) (subjectTerm subject) predicate.spelling.val position.val out.val.length
      (.ok (n, ts))) :
    ∃ next out', turtle.object_list cx position subject predicate out = .ok (.Ok (next, out')) ∧ next.val = n ∧
      out'.val.map spo = out.val.map spo ++ ts ∧ position.val < n ∧ n ≤ cx.bytes.val.length := by
  generalize result : (Except.ok (n, ts) : Except Fault (Nat × List Spo)) = given at found
  cases found with
  | firstFails _ => cases result
  | restFails _ _ => cases result
  | @list _ _ _ _ q ts' m us objectFound moreFound =>
    cases result
    obtain ⟨next, out1, objectRun, nextValue, contents1, lower, upper⟩ :=
      object_accepted cx position subject predicate out objectFound
    have length1 := map_length contents1
    subst nextValue
    rw [← length1] at moreFound
    obtain ⟨finish, out2, moreRun, finishValue, contents2, lower2, upper2⟩ :=
      more_objects_accepted cx next subject predicate out1 moreFound
    refine ⟨finish, out2, ?_, finishValue, by rw [contents2, contents1, List.append_assoc], by omega, by omega⟩
    rw [turtle.object_list]
    simp [objectRun, core.result.Result.Insts.CoreOpsTry.branch, moreRun]
termination_by 5 * (cx.bytes.val.length - position.val) + 3
decreasing_by all_goals omega

theorem more_objects_accepted (cx : turtle.Context) (position : Usize) (subject : rdf.Subject)
    (predicate : rdf.RdfIri) (out : alloc.vec.Vec rdf.Triple) {n : Nat} {ts : List Spo}
    (found : MoreObjectsAt (ctxOf cx) (subjectTerm subject) predicate.spelling.val position.val out.val.length
      (.ok (n, ts))) :
    ∃ next out', turtle.more_objects cx position subject predicate out = .ok (.Ok (next, out')) ∧ next.val = n ∧
      out'.val.map spo = out.val.map spo ++ ts ∧ position.val ≤ n ∧ n ≤ cx.bytes.val.length := by
  generalize result : (Except.ok (n, ts) : Except Fault (Nat × List Spo)) = given at found
  cases found with
  | spaceFails _ => cases result
  | @finish _ _ _ _ p spaced notComma =>
    cases result
    simp only [ctxOf] at spaced notComma
    have bound := trivia_bound spaced
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    refine ⟨stop, out, ?_, rfl, by simp, by omega, by omega⟩
    rw [turtle.more_objects]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, notComma]
  | objectFails _ _ _ => cases result
  | restFails _ _ _ _ => cases result
  | @more _ _ _ _ p q ts' m us spaced comma objectFound moreFound =>
    cases result
    simp only [ctxOf] at spaced comma
    have bound := trivia_bound spaced
    have inside := byte_inside comma
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    obtain ⟨i, add, iValue⟩ := add_one (bytes := cx.bytes) (x := stop) inside
    rw [← iValue] at objectFound
    obtain ⟨after, out1, objectRun, afterValue, contents1, lower, upper⟩ :=
      object_accepted cx i subject predicate out objectFound
    have length1 := map_length contents1
    subst afterValue
    rw [← length1] at moreFound
    obtain ⟨finish, out2, moreRun, finishValue, contents2, lower2, upper2⟩ :=
      more_objects_accepted cx after subject predicate out1 moreFound
    refine ⟨finish, out2, ?_, finishValue, by rw [contents2, contents1, List.append_assoc], by omega, by omega⟩
    rw [turtle.more_objects]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, comma, add, objectRun, moreRun]
termination_by 5 * (cx.bytes.val.length - position.val)
decreasing_by all_goals omega

theorem predicate_object_list_accepted (cx : turtle.Context) (position : Usize) (subject : rdf.Subject)
    (out : alloc.vec.Vec rdf.Triple) {n : Nat} {ts : List Spo}
    (found : ListAt (ctxOf cx) (subjectTerm subject) position.val out.val.length (.ok (n, ts))) :
    ∃ next out', turtle.predicate_object_list cx position subject out = .ok (.Ok (next, out')) ∧ next.val = n ∧
      out'.val.map spo = out.val.map spo ++ ts ∧ position.val < n ∧ n ≤ cx.bytes.val.length := by
  generalize result : (Except.ok (n, ts) : Except Fault (Nat × List Spo)) = given at found
  cases found with
  | verbFails _ => cases result
  | objectsFails _ _ => cases result
  | restFails _ _ _ => cases result
  | @list _ _ _ pr q m ts' k us verbFound objectsFound moreFound =>
    cases result
    have verbBound : position.val < q ∧ q ≤ cx.bytes.val.length := verb_bound verbFound
    obtain ⟨predicate, next, verbRun, predicateValue, nextValue⟩ := verb_accepted verbFound
    subst predicateValue
    subst nextValue
    obtain ⟨after, out1, listRun, afterValue, contents1, lower, upper⟩ :=
      object_list_accepted cx next subject predicate out objectsFound
    have length1 := map_length contents1
    subst afterValue
    rw [← length1] at moreFound
    obtain ⟨finish, out2, moreRun, finishValue, contents2, lower2, upper2⟩ :=
      more_predicates_accepted cx after subject out1 moreFound
    refine ⟨finish, out2, ?_, finishValue, by rw [contents2, contents1, List.append_assoc], by omega, by omega⟩
    rw [turtle.predicate_object_list]
    simp [verbRun, core.result.Result.Insts.CoreOpsTry.branch, listRun, moreRun]
termination_by 5 * (cx.bytes.val.length - position.val)
decreasing_by all_goals omega

theorem more_predicates_accepted (cx : turtle.Context) (position : Usize) (subject : rdf.Subject)
    (out : alloc.vec.Vec rdf.Triple) {n : Nat} {ts : List Spo}
    (found : MorePredicatesAt (ctxOf cx) (subjectTerm subject) position.val out.val.length (.ok (n, ts))) :
    ∃ next out', turtle.more_predicates cx position subject out = .ok (.Ok (next, out')) ∧ next.val = n ∧
      out'.val.map spo = out.val.map spo ++ ts ∧ position.val ≤ n ∧ n ≤ cx.bytes.val.length := by
  generalize result : (Except.ok (n, ts) : Except Fault (Nat × List Spo)) = given at found
  cases found with
  | spaceFails _ => cases result
  | @finish _ _ _ p spaced notSemicolon =>
    cases result
    simp only [ctxOf] at spaced notSemicolon
    have bound := trivia_bound spaced
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    refine ⟨stop, out, ?_, rfl, by simp, by omega, by omega⟩
    rw [turtle.more_predicates]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, notSemicolon]
  | afterFails _ _ _ => cases result
  | @empty _ _ _ p q r spaced semicolon spacedAfter notFollows restFound =>
    subst result
    simp only [ctxOf] at spaced semicolon spacedAfter notFollows
    have bound := trivia_bound spaced
    have inside := byte_inside semicolon
    have boundAfter := trivia_bound spacedAfter
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    obtain ⟨i, add, iValue⟩ := add_one (bytes := cx.bytes) (x := stop) inside
    obtain ⟨after, spaceRun2, afterValue⟩ := space_runs (bytes := cx.bytes) (position := i)
      (by rw [iValue]; exact spacedAfter)
    subst afterValue
    obtain ⟨finish, out1, restRun, finishValue, contents, lower, upper⟩ :=
      more_predicates_accepted cx after subject out restFound
    refine ⟨finish, out1, ?_, finishValue, contents, by omega, upper⟩
    rw [turtle.more_predicates]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, semicolon, add, spaceRun2,
      verb_follows_spec, notFollows, restRun]
  | verbFails _ _ _ _ _ => cases result
  | objectsFails _ _ _ _ _ _ => cases result
  | restFails _ _ _ _ _ _ _ => cases result
  | @more _ _ _ p q pr n' m ts' k us spaced semicolon spacedAfter follows verbFound objectsFound moreFound =>
    cases result
    simp only [ctxOf] at spaced semicolon spacedAfter follows
    have bound := trivia_bound spaced
    have inside := byte_inside semicolon
    have boundAfter := trivia_bound spacedAfter
    have verbBound : q < n' ∧ n' ≤ cx.bytes.val.length := verb_bound verbFound
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    obtain ⟨i, add, iValue⟩ := add_one (bytes := cx.bytes) (x := stop) inside
    obtain ⟨after, spaceRun2, afterValue⟩ := space_runs (bytes := cx.bytes) (position := i)
      (by rw [iValue]; exact spacedAfter)
    subst afterValue
    obtain ⟨predicate, objects, verbRun, predicateValue, objectsValue⟩ := verb_accepted verbFound
    subst predicateValue
    subst objectsValue
    obtain ⟨finish, out1, listRun, finishValue, contents1, lower, upper⟩ :=
      object_list_accepted cx objects subject predicate out objectsFound
    have length1 := map_length contents1
    subst finishValue
    rw [← length1] at moreFound
    obtain ⟨final, out2, moreRun, finalValue, contents2, lower2, upper2⟩ :=
      more_predicates_accepted cx finish subject out1 moreFound
    refine ⟨final, out2, ?_, finalValue, by rw [contents2, contents1, List.append_assoc], by omega, by omega⟩
    rw [turtle.more_predicates]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, semicolon, add, spaceRun2,
      verb_follows_spec, follows, verbRun, listRun, moreRun]
termination_by 5 * (cx.bytes.val.length - position.val)
decreasing_by all_goals omega

end


/-! ## Objects, property lists and collections: total correctness -/

mutual

theorem node_total_correct (cx : turtle.Context) (start : Usize) (out : alloc.vec.Vec rdf.Triple) :
    ∃ r o, turtle.node cx start out = .ok r ∧ NodeAt (ctxOf cx) start.val out.val.length o ∧
      GrownAgrees objectTerm out.val r o := by
  obtain ⟨needed, neededRun, neededCorrect⟩ := needed_total_correct cx.bytes start
  rcases needed with ⟨cp, next⟩ | e
  · have u : Unit cx.bytes.val start.val cp.val next.val := neededCorrect
    have inside := unit_progress u
    by_cases isBracket : StartOf cp.val = .Bracket
    · obtain ⟨r, o, run, correct, agree⟩ := bracket_total_correct cx start out (by omega)
      rcases r with ⟨b, finish, out', l⟩ | e
      · obtain ⟨ts, rfl, contents⟩ := bracket_ok agree
        exact ⟨.Ok (.Blank b, finish, out'), _, node_bracket_ok neededRun isBracket run, .bracket u isBracket correct,
          grown_intro contents⟩
      · obtain rfl := bracket_err agree
        exact ⟨.Err e, .error (faultOf e), node_bracket_err neededRun isBracket run,
          .bracketFails u isBracket correct, rfl⟩
    · by_cases isParen : StartOf cp.val = .Paren
      · obtain ⟨r, o, run, correct, agree⟩ := collection_total_correct cx start out (by omega)
        rcases r with ⟨s, finish, out'⟩ | e
        · obtain ⟨ts, rfl, contents⟩ := grown_ok agree
          refine ⟨.Ok (objectOf s, finish, out'), _, node_paren_ok neededRun isParen run, ?_, grown_intro contents⟩
          rw [object_of_term]
          exact .collection u isParen correct
        · obtain rfl := grown_err agree
          exact ⟨.Err e, .error (faultOf e), node_paren_err neededRun isParen run, .collection u isParen correct, rfl⟩
      · obtain ⟨r, o, run, correct, agree⟩ := term_total_correct cx start (StartOf cp.val) (by omega)
        rcases r with ⟨v, finish⟩ | e
        · obtain rfl := agrees_ok agree
          exact ⟨.Ok (v, finish, out), _, node_term_ok neededRun isBracket isParen run,
            .term u isBracket isParen correct, grown_intro (ts := []) (by simp)⟩
        · obtain rfl := agrees_err agree
          exact ⟨.Err e, .error (faultOf e), node_term_err neededRun isBracket isParen run,
            .termFails u isBracket isParen correct, rfl⟩
  · exact ⟨.Err e, .error (faultOf e), node_missing neededRun, .missing neededCorrect, rfl⟩
termination_by 5 * (cx.bytes.val.length - start.val) + 1
decreasing_by all_goals omega

theorem bracket_total_correct (cx : turtle.Context) (start : Usize) (out : alloc.vec.Vec rdf.Triple)
    (inside : start.val < cx.bytes.val.length) :
    ∃ r o, turtle.bracket cx start out = .ok r ∧ BracketAt (ctxOf cx) start.val out.val.length o ∧
      BracketAgrees out.val r o := by
  obtain ⟨i, add, iValue⟩ := add_one inside
  obtain ⟨node, nodeRun, scopeIs, labelIs⟩ := bracket_node_spec cx.scope start
  have nodeTerm := bracket_term cx start scopeIs labelIs
  obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct cx.bytes i
  rw [iValue] at spaceCorrect
  rcases spaced with stop | e
  · have runs : TriviaRuns cx.bytes.val true (start.val + 1) stop.val := spaceCorrect
    have bound := trivia_bound runs
    by_cases closing : ByteIs cx.bytes.val stop.val 93
    · obtain ⟨j, add2, jValue⟩ := add_one (byte_inside closing)
      refine ⟨.Ok (node, j, out, false), _, ?_, ?_, bracket_intro (ts := []) (by simp)⟩
      · rw [turtle.bracket]
        simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, closing, nodeRun, add2]
      · rw [nodeTerm, jValue]
        exact .anon runs closing
    · obtain ⟨r, o, listRun, listCorrect, agree⟩ := predicate_object_list_total_correct cx stop (.Blank node) out
      have listCorrect' : ListAt (ctxOf cx) (bracketTerm (ctxOf cx) start.val) stop.val out.val.length o := by
        rw [← nodeTerm]
        exact listCorrect
      rcases r with ⟨after, out1⟩ | e
      · obtain ⟨ts, rfl, contents⟩ := emitted_ok agree
        obtain ⟨closed, closeRun, closeCorrect⟩ := space_total_correct cx.bytes after
        rcases closed with close | e
        · have closeRuns : TriviaRuns cx.bytes.val true after.val close.val := closeCorrect
          by_cases closing2 : ByteIs cx.bytes.val close.val 93
          · obtain ⟨j, add2, jValue⟩ := add_one (byte_inside closing2)
            refine ⟨.Ok (node, j, out1, true), _, ?_, ?_, bracket_intro contents⟩
            · rw [turtle.bracket]
              simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, closing, nodeRun,
                listRun, closeRun, closing2, add2]
            · rw [nodeTerm, jValue]
              exact .list runs closing listCorrect' closeRuns closing2
          · refine ⟨.Err ⟨.ExpectedBracket, close⟩, .error (.ExpectedBracket, close.val), ?_,
              .unclosed runs closing listCorrect' closeRuns closing2, rfl⟩
            rw [turtle.bracket]
            simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, closing, nodeRun,
              listRun, closeRun, closing2, error_spec]
        · refine ⟨.Err e, .error (faultOf e), ?_, .closeFails runs closing listCorrect' closeCorrect, rfl⟩
          rw [turtle.bracket]
          simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, closing, nodeRun, listRun,
            closeRun]
      · obtain rfl := emitted_err agree
        refine ⟨.Err e, .error (faultOf e), ?_, .listFails runs closing listCorrect', rfl⟩
        rw [turtle.bracket]
        simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, closing, nodeRun, listRun]
  · refine ⟨.Err e, .error (faultOf e), ?_, .spaceFails spaceCorrect, rfl⟩
    rw [turtle.bracket]
    simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch]
termination_by 5 * (cx.bytes.val.length - start.val)
decreasing_by all_goals omega

theorem collection_total_correct (cx : turtle.Context) (start : Usize) (out : alloc.vec.Vec rdf.Triple)
    (inside : start.val < cx.bytes.val.length) :
    ∃ r o, turtle.collection cx start out = .ok r ∧ CollectionAt (ctxOf cx) start.val out.val.length o ∧
      GrownAgrees subjectTerm out.val r o := by
  obtain ⟨i, add, iValue⟩ := add_one inside
  obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct cx.bytes i
  rw [iValue] at spaceCorrect
  rcases spaced with stop | e
  · have runs : TriviaRuns cx.bytes.val true (start.val + 1) stop.val := spaceCorrect
    have bound := trivia_bound runs
    by_cases closing : ByteIs cx.bytes.val stop.val 41
    · obtain ⟨j, add2, jValue⟩ := add_one (byte_inside closing)
      obtain ⟨nil, nilRun, nilValue⟩ := rdf_nil_spec
      refine ⟨.Ok (.Iri nil, j, out), _, ?_, ?_, grown_intro (ts := []) (by simp)⟩
      · rw [turtle.collection]
        simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, closing, nilRun, add2]
      · rw [show subjectTerm (.Iri nil) = .iri RdfNilBytes by simp [subjectTerm, nilValue], jValue]
        exact .empty runs closing
    · obtain ⟨r, o, memberRun, memberCorrect, agree⟩ := member_total_correct cx stop out
      rcases r with ⟨after, out1⟩ | e
      · obtain ⟨ts, rfl, contents⟩ := emitted_ok agree
        obtain ⟨_, _, _, _, _, lower, upper⟩ := member_accepted cx stop out memberCorrect
        have length1 := map_length contents
        obtain ⟨r, o, membersRun, membersCorrect, agree⟩ := members_total_correct cx after stop out1
        rw [length1] at membersCorrect
        obtain ⟨node, nodeRun, scopeIs, labelIs⟩ := list_node_spec cx.scope stop
        rcases r with ⟨finish, out2⟩ | e
        · obtain ⟨us, rfl, contents2⟩ := emitted_ok agree
          refine ⟨.Ok (.Blank node, finish, out2), _, ?_, ?_,
            grown_intro (ts := ts ++ us) (by rw [contents2, contents, List.append_assoc])⟩
          · rw [turtle.collection]
            simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, closing, memberRun,
              membersRun, nodeRun]
          · rw [show subjectTerm (.Blank node) = listTerm (ctxOf cx) stop.val from list_term cx stop scopeIs labelIs]
            exact .list runs closing memberCorrect membersCorrect
        · obtain rfl := emitted_err agree
          refine ⟨.Err e, .error (faultOf e), ?_, .restFails runs closing memberCorrect membersCorrect, rfl⟩
          rw [turtle.collection]
          simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, closing, memberRun,
            membersRun]
      · obtain rfl := emitted_err agree
        refine ⟨.Err e, .error (faultOf e), ?_, .firstFails runs closing memberCorrect, rfl⟩
        rw [turtle.collection]
        simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, closing, memberRun]
  · refine ⟨.Err e, .error (faultOf e), ?_, .spaceFails spaceCorrect, rfl⟩
    rw [turtle.collection]
    simp [add, spaceRun, core.result.Result.Insts.CoreOpsTry.branch]
termination_by 5 * (cx.bytes.val.length - start.val)
decreasing_by all_goals omega

theorem member_total_correct (cx : turtle.Context) (start : Usize) (out : alloc.vec.Vec rdf.Triple) :
    ∃ r o, turtle.member cx start out = .ok r ∧
      ObjectAt (ctxOf cx) (listTerm (ctxOf cx) start.val) RdfFirstBytes start.val out.val.length o ∧
      EmittedAgrees out.val r o := by
  obtain ⟨node, nodeRun, scopeIs, labelIs⟩ := list_node_spec cx.scope start
  obtain ⟨first, firstRun, firstValue⟩ := rdf_first_spec
  obtain ⟨r, o, run, correct, agree⟩ := object_total_correct cx start (.Blank node) first out
  have correct' : ObjectAt (ctxOf cx) (listTerm (ctxOf cx) start.val) RdfFirstBytes start.val out.val.length o := by
    rw [← list_term cx start scopeIs labelIs, ← firstValue]
    exact correct
  exact ⟨r, o, by rw [turtle.member]; simp [nodeRun, firstRun, run], correct', agree⟩
termination_by 5 * (cx.bytes.val.length - start.val) + 3
decreasing_by all_goals omega

theorem members_total_correct (cx : turtle.Context) (position last : Usize) (out : alloc.vec.Vec rdf.Triple) :
    ∃ r o, turtle.members cx position last out = .ok r ∧
      MembersAt (ctxOf cx) position.val last.val out.val.length o ∧ EmittedAgrees out.val r o := by
  obtain ⟨link, linkRun, linkScope, linkLabel⟩ := list_node_spec cx.scope last
  have linkTerm := list_term cx last linkScope linkLabel
  obtain ⟨rest, restRun, restValue⟩ := rdf_rest_spec
  obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct cx.bytes position
  rcases spaced with stop | e
  · have runs : TriviaRuns cx.bytes.val true position.val stop.val := spaceCorrect
    have bound := trivia_bound runs
    by_cases closing : ByteIs cx.bytes.val stop.val 41
    · obtain ⟨nil, nilRun, nilValue⟩ := rdf_nil_spec
      obtain ⟨r, emitRun, emitOk, emitFull⟩ := emit_spec out ⟨.Blank link, rest, .Iri nil⟩ cx.limits stop
      by_cases room : out.val.length < cx.limits.max_triples.val
      · obtain ⟨out1, rfl, contents⟩ := emitOk room
        obtain ⟨j, add, jValue⟩ := add_one (byte_inside closing)
        refine ⟨.Ok (j, out1), _, ?_, ?_,
          emitted_intro (ts := [⟨listTerm (ctxOf cx) last.val, RdfRestBytes, .iri RdfNilBytes⟩]) ?_⟩
        · rw [turtle.members]
          simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, linkRun, byte_is_spec, closing, restRun, nilRun,
            emitRun, add]
        · rw [jValue]
          exact .close runs closing room
        · rw [contents]
          simp [spo, subjectTerm, objectTerm, linkTerm, restValue, nilValue]
      · obtain rfl := emitFull (by omega)
        refine ⟨.Err ⟨.ResourceLimit, stop⟩, .error (.ResourceLimit, stop.val), ?_,
          .closeFull runs closing (by show cx.limits.max_triples.val ≤ out.val.length; omega), rfl⟩
        rw [turtle.members]
        simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, linkRun, byte_is_spec, closing, restRun, nilRun,
          emitRun]
    · obtain ⟨node, nodeRun, nodeScope, nodeLabel⟩ := list_node_spec cx.scope stop
      have nodeTerm := list_term cx stop nodeScope nodeLabel
      obtain ⟨r, emitRun, emitOk, emitFull⟩ := emit_spec out ⟨.Blank link, rest, .Blank node⟩ cx.limits stop
      by_cases room : out.val.length < cx.limits.max_triples.val
      · obtain ⟨out1, rfl, contents1⟩ := emitOk room
        have length1 : out1.val.length = out.val.length + 1 := by rw [contents1]; simp
        obtain ⟨r, o, memberRun, memberCorrect, agree⟩ := member_total_correct cx stop out1
        rcases r with ⟨after, out2⟩ | e
        · obtain ⟨ts, rfl, contents2⟩ := emitted_ok agree
          obtain ⟨_, _, _, _, _, lower, upper⟩ := member_accepted cx stop out1 memberCorrect
          have length2 := map_length contents2
          rw [length1] at memberCorrect
          obtain ⟨r, o, membersRun, membersCorrect, agree⟩ := members_total_correct cx after stop out2
          rw [length2, length1] at membersCorrect
          rcases r with ⟨finish, out3⟩ | e
          · obtain ⟨us, rfl, contents3⟩ := emitted_ok agree
            refine ⟨.Ok (finish, out3), _, ?_, .more runs closing room memberCorrect membersCorrect,
              emitted_intro ?_⟩
            · rw [turtle.members]
              simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, linkRun, byte_is_spec, closing, restRun,
                nodeRun, emitRun, memberRun, membersRun]
            · rw [contents3, contents2, contents1]
              simp [spo, subjectTerm, objectTerm, linkTerm, restValue, nodeTerm]
          · obtain rfl := emitted_err agree
            refine ⟨.Err e, .error (faultOf e), ?_, .restFails runs closing room memberCorrect membersCorrect, rfl⟩
            rw [turtle.members]
            simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, linkRun, byte_is_spec, closing, restRun,
              nodeRun, emitRun, memberRun, membersRun]
        · obtain rfl := emitted_err agree
          rw [length1] at memberCorrect
          refine ⟨.Err e, .error (faultOf e), ?_, .memberFails runs closing room memberCorrect, rfl⟩
          rw [turtle.members]
          simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, linkRun, byte_is_spec, closing, restRun,
            nodeRun, emitRun, memberRun]
      · obtain rfl := emitFull (by omega)
        refine ⟨.Err ⟨.ResourceLimit, stop⟩, .error (.ResourceLimit, stop.val), ?_,
          .linkFull runs closing (by show cx.limits.max_triples.val ≤ out.val.length; omega), rfl⟩
        rw [turtle.members]
        simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, linkRun, byte_is_spec, closing, restRun, nodeRun,
          emitRun]
  · refine ⟨.Err e, .error (faultOf e), ?_, .spaceFails spaceCorrect, rfl⟩
    rw [turtle.members]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch]
termination_by 5 * (cx.bytes.val.length - position.val) + 4
decreasing_by all_goals omega

theorem object_total_correct (cx : turtle.Context) (position : Usize) (subject : rdf.Subject)
    (predicate : rdf.RdfIri) (out : alloc.vec.Vec rdf.Triple) :
    ∃ r o, turtle.object cx position subject predicate out = .ok r ∧
      ObjectAt (ctxOf cx) (subjectTerm subject) predicate.spelling.val position.val out.val.length o ∧
      EmittedAgrees out.val r o := by
  obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct cx.bytes position
  rcases spaced with stop | e
  · have runs : TriviaRuns cx.bytes.val true position.val stop.val := spaceCorrect
    have bound := trivia_bound runs
    obtain ⟨r, o, nodeRun, nodeCorrect, agree⟩ := node_total_correct cx stop out
    rcases r with ⟨v, next, out1⟩ | e
    · obtain ⟨ts, rfl, contents1⟩ := grown_ok agree
      have length1 := map_length contents1
      obtain ⟨r, emitRun, emitOk, emitFull⟩ := emit_spec out1 ⟨subject, predicate, v⟩ cx.limits stop
      by_cases room : out1.val.length < cx.limits.max_triples.val
      · obtain ⟨out2, rfl, contents2⟩ := emitOk room
        refine ⟨.Ok (next, out2), _, ?_,
          .object runs nodeCorrect (by show out.val.length + ts.length < cx.limits.max_triples.val; omega),
          emitted_intro ?_⟩
        · rw [turtle.object]
          simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, nodeRun, copy_subject_spec, copy_iri_spec,
            emitRun]
        · rw [contents2, List.map_append, contents1]
          simp [spo]
      · obtain rfl := emitFull (by omega)
        refine ⟨.Err ⟨.ResourceLimit, stop⟩, .error (.ResourceLimit, stop.val), ?_,
          .full runs nodeCorrect (by show cx.limits.max_triples.val ≤ out.val.length + ts.length; omega), rfl⟩
        rw [turtle.object]
        simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, nodeRun, copy_subject_spec, copy_iri_spec,
          emitRun]
    · obtain rfl := grown_err agree
      refine ⟨.Err e, .error (faultOf e), ?_, .nodeFails runs nodeCorrect, rfl⟩
      rw [turtle.object]
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, nodeRun]
  · refine ⟨.Err e, .error (faultOf e), ?_, .spaceFails spaceCorrect, rfl⟩
    rw [turtle.object]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch]
termination_by 5 * (cx.bytes.val.length - position.val) + 2
decreasing_by all_goals omega

theorem object_list_total_correct (cx : turtle.Context) (position : Usize) (subject : rdf.Subject)
    (predicate : rdf.RdfIri) (out : alloc.vec.Vec rdf.Triple) :
    ∃ r o, turtle.object_list cx position subject predicate out = .ok r ∧
      ObjectsAt (ctxOf cx) (subjectTerm subject) predicate.spelling.val position.val out.val.length o ∧
      EmittedAgrees out.val r o := by
  obtain ⟨r, o, objectRun, objectCorrect, agree⟩ := object_total_correct cx position subject predicate out
  rcases r with ⟨next, out1⟩ | e
  · obtain ⟨ts, rfl, contents1⟩ := emitted_ok agree
    obtain ⟨_, _, _, _, _, lower, upper⟩ := object_accepted cx position subject predicate out objectCorrect
    have length1 := map_length contents1
    obtain ⟨r, o, moreRun, moreCorrect, agree⟩ := more_objects_total_correct cx next subject predicate out1
    rw [length1] at moreCorrect
    rcases r with ⟨finish, out2⟩ | e
    · obtain ⟨us, rfl, contents2⟩ := emitted_ok agree
      refine ⟨.Ok (finish, out2), _, ?_, .list objectCorrect moreCorrect,
        emitted_intro (by rw [contents2, contents1, List.append_assoc])⟩
      rw [turtle.object_list]
      simp [objectRun, core.result.Result.Insts.CoreOpsTry.branch, moreRun]
    · obtain rfl := emitted_err agree
      refine ⟨.Err e, .error (faultOf e), ?_, .restFails objectCorrect moreCorrect, rfl⟩
      rw [turtle.object_list]
      simp [objectRun, core.result.Result.Insts.CoreOpsTry.branch, moreRun]
  · obtain rfl := emitted_err agree
    refine ⟨.Err e, .error (faultOf e), ?_, .firstFails objectCorrect, rfl⟩
    rw [turtle.object_list]
    simp [objectRun, core.result.Result.Insts.CoreOpsTry.branch]
termination_by 5 * (cx.bytes.val.length - position.val) + 3
decreasing_by all_goals omega

theorem more_objects_total_correct (cx : turtle.Context) (position : Usize) (subject : rdf.Subject)
    (predicate : rdf.RdfIri) (out : alloc.vec.Vec rdf.Triple) :
    ∃ r o, turtle.more_objects cx position subject predicate out = .ok r ∧
      MoreObjectsAt (ctxOf cx) (subjectTerm subject) predicate.spelling.val position.val out.val.length o ∧
      EmittedAgrees out.val r o := by
  obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct cx.bytes position
  rcases spaced with stop | e
  · have runs : TriviaRuns cx.bytes.val true position.val stop.val := spaceCorrect
    have bound := trivia_bound runs
    by_cases comma : ByteIs cx.bytes.val stop.val 44
    · have inside := byte_inside comma
      obtain ⟨i, add, iValue⟩ := add_one inside
      obtain ⟨r, o, objectRun, objectCorrect, agree⟩ := object_total_correct cx i subject predicate out
      rcases r with ⟨after, out1⟩ | e
      · obtain ⟨ts, rfl, contents1⟩ := emitted_ok agree
        obtain ⟨_, _, _, _, _, lower, upper⟩ := object_accepted cx i subject predicate out objectCorrect
        have length1 := map_length contents1
        rw [iValue] at objectCorrect
        obtain ⟨r, o, moreRun, moreCorrect, agree⟩ := more_objects_total_correct cx after subject predicate out1
        rw [length1] at moreCorrect
        rcases r with ⟨finish, out2⟩ | e
        · obtain ⟨us, rfl, contents2⟩ := emitted_ok agree
          refine ⟨.Ok (finish, out2), _, ?_, .more runs comma objectCorrect moreCorrect,
            emitted_intro (by rw [contents2, contents1, List.append_assoc])⟩
          rw [turtle.more_objects]
          simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, comma, add, objectRun, moreRun]
        · obtain rfl := emitted_err agree
          refine ⟨.Err e, .error (faultOf e), ?_, .restFails runs comma objectCorrect moreCorrect, rfl⟩
          rw [turtle.more_objects]
          simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, comma, add, objectRun, moreRun]
      · obtain rfl := emitted_err agree
        rw [iValue] at objectCorrect
        refine ⟨.Err e, .error (faultOf e), ?_, .objectFails runs comma objectCorrect, rfl⟩
        rw [turtle.more_objects]
        simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, comma, add, objectRun]
    · refine ⟨.Ok (stop, out), _, ?_, .finish runs comma, emitted_intro (ts := []) (by simp)⟩
      rw [turtle.more_objects]
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, comma]
  · refine ⟨.Err e, .error (faultOf e), ?_, .spaceFails spaceCorrect, rfl⟩
    rw [turtle.more_objects]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch]
termination_by 5 * (cx.bytes.val.length - position.val)
decreasing_by all_goals omega

theorem predicate_object_list_total_correct (cx : turtle.Context) (position : Usize) (subject : rdf.Subject)
    (out : alloc.vec.Vec rdf.Triple) :
    ∃ r o, turtle.predicate_object_list cx position subject out = .ok r ∧
      ListAt (ctxOf cx) (subjectTerm subject) position.val out.val.length o ∧ EmittedAgrees out.val r o := by
  obtain ⟨r, o, verbRun, verbCorrect, agree⟩ := verb_total_correct cx position
  rcases r with ⟨predicate, next⟩ | e
  · obtain rfl := agrees_ok agree
    have verbCorrect' : VerbAt (ctxOf cx) position.val (.ok (predicate.spelling.val, next.val)) := verbCorrect
    have verbBound : position.val < next.val ∧ next.val ≤ cx.bytes.val.length := verb_bound verbCorrect'
    obtain ⟨r, o, listRun, listCorrect, agree⟩ := object_list_total_correct cx next subject predicate out
    rcases r with ⟨after, out1⟩ | e
    · obtain ⟨ts, rfl, contents1⟩ := emitted_ok agree
      obtain ⟨_, _, _, _, _, lower, upper⟩ := object_list_accepted cx next subject predicate out listCorrect
      have length1 := map_length contents1
      obtain ⟨r, o, moreRun, moreCorrect, agree⟩ := more_predicates_total_correct cx after subject out1
      rw [length1] at moreCorrect
      rcases r with ⟨finish, out2⟩ | e
      · obtain ⟨us, rfl, contents2⟩ := emitted_ok agree
        refine ⟨.Ok (finish, out2), _, ?_, .list verbCorrect' listCorrect moreCorrect,
          emitted_intro (by rw [contents2, contents1, List.append_assoc])⟩
        rw [turtle.predicate_object_list]
        simp [verbRun, core.result.Result.Insts.CoreOpsTry.branch, listRun, moreRun]
      · obtain rfl := emitted_err agree
        refine ⟨.Err e, .error (faultOf e), ?_, .restFails verbCorrect' listCorrect moreCorrect, rfl⟩
        rw [turtle.predicate_object_list]
        simp [verbRun, core.result.Result.Insts.CoreOpsTry.branch, listRun, moreRun]
    · obtain rfl := emitted_err agree
      refine ⟨.Err e, .error (faultOf e), ?_, .objectsFails verbCorrect' listCorrect, rfl⟩
      rw [turtle.predicate_object_list]
      simp [verbRun, core.result.Result.Insts.CoreOpsTry.branch, listRun]
  · obtain rfl := agrees_err agree
    refine ⟨.Err e, .error (faultOf e), ?_, .verbFails verbCorrect, rfl⟩
    rw [turtle.predicate_object_list]
    simp [verbRun, core.result.Result.Insts.CoreOpsTry.branch]
termination_by 5 * (cx.bytes.val.length - position.val)
decreasing_by all_goals omega

theorem more_predicates_total_correct (cx : turtle.Context) (position : Usize) (subject : rdf.Subject)
    (out : alloc.vec.Vec rdf.Triple) :
    ∃ r o, turtle.more_predicates cx position subject out = .ok r ∧
      MorePredicatesAt (ctxOf cx) (subjectTerm subject) position.val out.val.length o ∧
      EmittedAgrees out.val r o := by
  obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct cx.bytes position
  rcases spaced with stop | e
  · have runs : TriviaRuns cx.bytes.val true position.val stop.val := spaceCorrect
    have bound := trivia_bound runs
    by_cases semicolon : ByteIs cx.bytes.val stop.val 59
    · have inside := byte_inside semicolon
      obtain ⟨i, add, iValue⟩ := add_one inside
      obtain ⟨spaced2, spaceRun2, spaceCorrect2⟩ := space_total_correct cx.bytes i
      rw [iValue] at spaceCorrect2
      rcases spaced2 with after | e
      · have runs2 : TriviaRuns cx.bytes.val true (stop.val + 1) after.val := spaceCorrect2
        have bound2 := trivia_bound runs2
        by_cases follows : VerbFollows cx.bytes.val after.val
        · obtain ⟨r, o, verbRun, verbCorrect, agree⟩ := verb_total_correct cx after
          rcases r with ⟨predicate, objects⟩ | e
          · obtain rfl := agrees_ok agree
            have verbCorrect' : VerbAt (ctxOf cx) after.val (.ok (predicate.spelling.val, objects.val)) :=
              verbCorrect
            have verbBound : after.val < objects.val ∧ objects.val ≤ cx.bytes.val.length := verb_bound verbCorrect'
            obtain ⟨r, o, listRun, listCorrect, agree⟩ := object_list_total_correct cx objects subject predicate out
            rcases r with ⟨finish, out1⟩ | e
            · obtain ⟨ts, rfl, contents1⟩ := emitted_ok agree
              obtain ⟨_, _, _, _, _, lower, upper⟩ := object_list_accepted cx objects subject predicate out listCorrect
              have length1 := map_length contents1
              obtain ⟨r, o, moreRun, moreCorrect, agree⟩ := more_predicates_total_correct cx finish subject out1
              rw [length1] at moreCorrect
              rcases r with ⟨final, out2⟩ | e
              · obtain ⟨us, rfl, contents2⟩ := emitted_ok agree
                refine ⟨.Ok (final, out2), _, ?_,
                  .more runs semicolon runs2 follows verbCorrect' listCorrect moreCorrect,
                  emitted_intro (by rw [contents2, contents1, List.append_assoc])⟩
                rw [turtle.more_predicates]
                simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, semicolon, add, spaceRun2,
                  verb_follows_spec, follows, verbRun, listRun, moreRun]
              · obtain rfl := emitted_err agree
                refine ⟨.Err e, .error (faultOf e), ?_,
                  .restFails runs semicolon runs2 follows verbCorrect' listCorrect moreCorrect, rfl⟩
                rw [turtle.more_predicates]
                simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, semicolon, add, spaceRun2,
                  verb_follows_spec, follows, verbRun, listRun, moreRun]
            · obtain rfl := emitted_err agree
              refine ⟨.Err e, .error (faultOf e), ?_,
                .objectsFails runs semicolon runs2 follows verbCorrect' listCorrect, rfl⟩
              rw [turtle.more_predicates]
              simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, semicolon, add, spaceRun2,
                verb_follows_spec, follows, verbRun, listRun]
          · obtain rfl := agrees_err agree
            refine ⟨.Err e, .error (faultOf e), ?_, .verbFails runs semicolon runs2 follows verbCorrect, rfl⟩
            rw [turtle.more_predicates]
            simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, semicolon, add, spaceRun2,
              verb_follows_spec, follows, verbRun]
        · obtain ⟨r, o, restRun, restCorrect, agree⟩ := more_predicates_total_correct cx after subject out
          refine ⟨r, o, ?_, .empty runs semicolon runs2 follows restCorrect, agree⟩
          rw [turtle.more_predicates]
          simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, semicolon, add, spaceRun2,
            verb_follows_spec, follows, restRun]
      · refine ⟨.Err e, .error (faultOf e), ?_, .afterFails runs semicolon spaceCorrect2, rfl⟩
        rw [turtle.more_predicates]
        simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, semicolon, add, spaceRun2]
    · refine ⟨.Ok (stop, out), _, ?_, .finish runs semicolon, emitted_intro (ts := []) (by simp)⟩
      rw [turtle.more_predicates]
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, semicolon]
  · refine ⟨.Err e, .error (faultOf e), ?_, .spaceFails spaceCorrect, rfl⟩
    rw [turtle.more_predicates]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch]
termination_by 5 * (cx.bytes.val.length - position.val)
decreasing_by all_goals omega

end


/-! ## Subjects and triples statements -/

theorem subject_total_correct (cx : turtle.Context) (start : Usize) (out : alloc.vec.Vec rdf.Triple) :
    ∃ r o, turtle.subject cx start out = .ok r ∧ SubjectAt (ctxOf cx) start.val out.val.length o ∧
      GrownAgrees subjectTerm out.val r o := by
  obtain ⟨needed, neededRun, neededCorrect⟩ := needed_total_correct cx.bytes start
  rcases needed with ⟨cp, next⟩ | e
  · have u : Unit cx.bytes.val start.val cp.val next.val := neededCorrect
    have inside := unit_progress u
    cases kindIs : StartOf cp.val with
    | Iri =>
      obtain ⟨r, o, run, correct, agree⟩ := iri_ref_total_correct cx.bytes start cx.base cx.limits.max_term_bytes
      rcases r with ⟨iri, finish⟩ | e
      · obtain rfl := agrees_ok agree
        refine ⟨.Ok (.Iri iri, finish, out), _, ?_, .iri u kindIs correct, grown_intro (ts := []) (by simp)⟩
        rw [turtle.subject]
        simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, run]
      · obtain rfl := agrees_err agree
        refine ⟨.Err e, _, ?_, .iriFails u kindIs correct, rfl⟩
        rw [turtle.subject]
        simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, run]
    | Blank =>
      obtain ⟨r, o, run, correct, agree⟩ := blank_label_total_correct cx.bytes start cx.scope
        cx.limits.max_term_bytes (by omega)
      rcases r with ⟨node, finish⟩ | e
      · obtain rfl := agrees_ok agree
        refine ⟨.Ok (.Blank node, finish, out), _, ?_, .blank u kindIs correct, grown_intro (ts := []) (by simp)⟩
        rw [turtle.subject]
        simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, run]
      · obtain rfl := agrees_err agree
        refine ⟨.Err e, _, ?_, .blankFails u kindIs correct, rfl⟩
        rw [turtle.subject]
        simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, run]
    | Bracket =>
      refine ⟨.Err ⟨.ExpectedSubject, start⟩, .error (.ExpectedSubject, start.val), ?_,
        .other u (by simp [kindIs]) (by simp [kindIs]) (by simp [kindIs]) (by simp [kindIs]), rfl⟩
      rw [turtle.subject]
      simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, error_spec]
    | Paren =>
      obtain ⟨r, o, run, correct, agree⟩ := collection_total_correct cx start out (by omega)
      refine ⟨r, o, ?_, .collection u kindIs correct, agree⟩
      rw [turtle.subject]
      simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, run]
    | Quote =>
      refine ⟨.Err ⟨.ExpectedSubject, start⟩, .error (.ExpectedSubject, start.val), ?_,
        .other u (by simp [kindIs]) (by simp [kindIs]) (by simp [kindIs]) (by simp [kindIs]), rfl⟩
      rw [turtle.subject]
      simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, error_spec]
    | Number =>
      refine ⟨.Err ⟨.ExpectedSubject, start⟩, .error (.ExpectedSubject, start.val), ?_,
        .other u (by simp [kindIs]) (by simp [kindIs]) (by simp [kindIs]) (by simp [kindIs]), rfl⟩
      rw [turtle.subject]
      simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, error_spec]
    | Word =>
      obtain ⟨r, o, colonRun, colonCorrect, agree⟩ := prefix_colon_total_correct cx.bytes start
      rcases r with (_ | colon) | e
      · obtain rfl := agrees_ok agree
        refine ⟨.Err ⟨.ExpectedSubject, start⟩, .error (.ExpectedSubject, start.val), ?_,
          .unnamed u kindIs colonCorrect, rfl⟩
        rw [turtle.subject]
        simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, colonRun, error_spec]
      · obtain rfl := agrees_ok agree
        obtain ⟨r, o, run, correct, agree⟩ := prefixed_total_correct cx.bytes start colon cx.prefixes
          cx.limits.max_term_bytes colonCorrect
        rcases r with ⟨iri, finish⟩ | e
        · obtain rfl := agrees_ok agree
          refine ⟨.Ok (.Iri iri, finish, out), _, ?_, .prefixed u kindIs colonCorrect correct,
            grown_intro (ts := []) (by simp)⟩
          rw [turtle.subject]
          simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, colonRun, run]
        · obtain rfl := agrees_err agree
          refine ⟨.Err e, _, ?_, .prefixedFails u kindIs colonCorrect correct, rfl⟩
          rw [turtle.subject]
          simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, colonRun, run]
      · obtain rfl := agrees_err agree
        refine ⟨.Err e, _, ?_, .colonFails u kindIs colonCorrect, rfl⟩
        rw [turtle.subject]
        simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, colonRun]
    | Other =>
      refine ⟨.Err ⟨.ExpectedSubject, start⟩, .error (.ExpectedSubject, start.val), ?_,
        .other u (by simp [kindIs]) (by simp [kindIs]) (by simp [kindIs]) (by simp [kindIs]), rfl⟩
      rw [turtle.subject]
      simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, error_spec]
  · refine ⟨.Err e, _, ?_, .missing neededCorrect, rfl⟩
    rw [turtle.subject]
    simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch]

theorem subject_accepted (cx : turtle.Context) (start : Usize) (out : alloc.vec.Vec rdf.Triple) {t : Term}
    {n : Nat} {ts : List Spo} (found : SubjectAt (ctxOf cx) start.val out.val.length (.ok (t, n, ts))) :
    ∃ s next out', turtle.subject cx start out = .ok (.Ok (s, next, out')) ∧ subjectTerm s = t ∧ next.val = n ∧
      out'.val.map spo = out.val.map spo ++ ts ∧ start.val < n ∧ n ≤ cx.bytes.val.length := by
  generalize result : (Except.ok (t, n, ts) : Except Fault (Term × Nat × List Spo)) = given at found
  cases found with
  | missing _ => cases result
  | iriFails _ _ _ => cases result
  | @iri ch q v m u kindIs iriFound =>
    cases result
    have u : Unit cx.bytes.val start.val ch q := u
    obtain ⟨cp, next, neededRun, hc, _⟩ := needed_at u
    subst hc
    have bound := iri_ref_bound (bs := cx.bytes.val) iriFound
    obtain ⟨iri, finish, run, hv, hn⟩ := iri_ref_accepted (bytes := cx.bytes) (base := cx.base)
      (limit := cx.limits.max_term_bytes) iriFound
    refine ⟨.Iri iri, finish, out, ?_, by simp [subjectTerm, hv], hn, by simp, bound.1, bound.2⟩
    rw [turtle.subject]
    simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, run]
  | blankFails _ _ _ => cases result
  | @blank ch q t' m u kindIs blankFound =>
    cases result
    have u : Unit cx.bytes.val start.val ch q := u
    obtain ⟨cp, next, neededRun, hc, _⟩ := needed_at u
    subst hc
    have bound := blank_label_bound (bs := cx.bytes.val) blankFound
    obtain ⟨node, finish, run, value⟩ := blank_label_accepted (bytes := cx.bytes) (scope := cx.scope)
      (limit := cx.limits.max_term_bytes) blankFound
    simp only [blankView, Prod.mk.injEq] at value
    refine ⟨.Blank node, finish, out, ?_, value.1, value.2, by simp, bound.1, bound.2⟩
    rw [turtle.subject]
    simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, run]
  | @collection ch q r u kindIs collectionFound =>
    subst result
    have u : Unit cx.bytes.val start.val ch q := u
    obtain ⟨cp, next, neededRun, hc, _⟩ := needed_at u
    subst hc
    obtain ⟨s, finish, out', run, rest⟩ := collection_accepted cx start out collectionFound
    refine ⟨s, finish, out', ?_, rest⟩
    rw [turtle.subject]
    simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, run]
  | colonFails _ _ _ => cases result
  | unnamed _ _ _ => cases result
  | prefixedFails _ _ _ _ => cases result
  | @prefixed ch q colon v m u kindIs colonFound named =>
    cases result
    have u : Unit cx.bytes.val start.val ch q := u
    obtain ⟨cp, next, neededRun, hc, _⟩ := needed_at u
    subst hc
    have colonFound : PrefixColon cx.bytes.val start.val (.ok (some colon)) := colonFound
    have colonBound := prefix_colon_bound colonFound
    have bound := prefixed_bound (bs := cx.bytes.val) named colonBound.2
    obtain ⟨c, colonRun, colonValue⟩ := prefix_colon_accepted colonFound
    cases c with
    | none => simp at colonValue
    | some colon' =>
      simp only [Option.map_some, Option.some.injEq] at colonValue
      subst colonValue
      obtain ⟨iri, finish, run, hv, hn⟩ := prefixed_accepted (bytes := cx.bytes) (start := start) (colon := colon')
        (prefixes := cx.prefixes) (limit := cx.limits.max_term_bytes) colonFound named
      refine ⟨.Iri iri, finish, out, ?_, by simp [subjectTerm, hv], hn, by simp, by omega, bound.2⟩
      rw [turtle.subject]
      simp [neededRun, core.result.Result.Insts.CoreOpsTry.branch, start_of_spec, kindIs, colonRun, run]
  | other _ _ _ _ _ => cases result

theorem optional_list_total_correct (cx : turtle.Context) (position : Usize) (subject : rdf.Subject)
    (out : alloc.vec.Vec rdf.Triple) :
    ∃ r o, turtle.optional_list cx position subject out = .ok r ∧
      OptionalListAt (ctxOf cx) (subjectTerm subject) position.val out.val.length o ∧ EmittedAgrees out.val r o := by
  obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct cx.bytes position
  rcases spaced with stop | e
  · have runs : TriviaRuns cx.bytes.val true position.val stop.val := spaceCorrect
    by_cases period : ByteIs cx.bytes.val stop.val 46
    · refine ⟨.Ok (stop, out), _, ?_, .none runs period, emitted_intro (ts := []) (by simp)⟩
      rw [turtle.optional_list]
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, period]
    · obtain ⟨r, o, run, correct, agree⟩ := predicate_object_list_total_correct cx stop subject out
      refine ⟨r, o, ?_, .list runs period correct, agree⟩
      rw [turtle.optional_list]
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, period, run]
  · refine ⟨.Err e, _, ?_, .spaceFails spaceCorrect, rfl⟩
    rw [turtle.optional_list]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch]

theorem optional_list_accepted (cx : turtle.Context) (position : Usize) (subject : rdf.Subject)
    (out : alloc.vec.Vec rdf.Triple) {n : Nat} {ts : List Spo}
    (found : OptionalListAt (ctxOf cx) (subjectTerm subject) position.val out.val.length (.ok (n, ts))) :
    ∃ next out', turtle.optional_list cx position subject out = .ok (.Ok (next, out')) ∧ next.val = n ∧
      out'.val.map spo = out.val.map spo ++ ts ∧ position.val ≤ n ∧ n ≤ cx.bytes.val.length := by
  generalize result : (Except.ok (n, ts) : Except Fault (Nat × List Spo)) = given at found
  cases found with
  | spaceFails _ => cases result
  | @none p spaced period =>
    cases result
    simp only [ctxOf] at spaced period
    have bound := trivia_bound spaced
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    refine ⟨stop, out, ?_, rfl, by simp, bound.1, bound.2⟩
    rw [turtle.optional_list]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, period]
  | @list p r spaced period listFound =>
    subst result
    simp only [ctxOf] at spaced period
    have bound := trivia_bound spaced
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    obtain ⟨next, out', run, nextValue, contents, lower, upper⟩ :=
      predicate_object_list_accepted cx stop subject out listFound
    refine ⟨next, out', ?_, nextValue, contents, by omega, upper⟩
    rw [turtle.optional_list]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, period, run]

theorem triples_total_correct (cx : turtle.Context) (start : Usize) (out : alloc.vec.Vec rdf.Triple) :
    ∃ r o, turtle.triples cx start out = .ok r ∧ TriplesAt (ctxOf cx) start.val out.val.length o ∧
      EmittedAgrees out.val r o := by
  by_cases opening : ByteIs cx.bytes.val start.val 91
  · obtain ⟨r, o, bracketRun, bracketCorrect, agree⟩ := bracket_total_correct cx start out (byte_inside opening)
    rcases r with ⟨node, next, out1, listed⟩ | e
    · obtain ⟨ts, rfl, contents1⟩ := bracket_ok agree
      have length1 := map_length contents1
      cases listed with
      | false =>
        obtain ⟨r, o, listRun, listCorrect, agree⟩ := predicate_object_list_total_correct cx next (.Blank node) out1
        rw [length1] at listCorrect
        rcases r with ⟨finish, out2⟩ | e
        · obtain ⟨us, rfl, contents2⟩ := emitted_ok agree
          refine ⟨.Ok (finish, out2), _, ?_, .anon opening bracketCorrect listCorrect,
            emitted_intro (by rw [contents2, contents1, List.append_assoc])⟩
          rw [turtle.triples]
          simp [byte_is_spec, opening, bracketRun, core.result.Result.Insts.CoreOpsTry.branch, listRun]
        · obtain rfl := emitted_err agree
          refine ⟨.Err e, _, ?_, .anonFails opening bracketCorrect listCorrect, rfl⟩
          rw [turtle.triples]
          simp [byte_is_spec, opening, bracketRun, core.result.Result.Insts.CoreOpsTry.branch, listRun]
      | true =>
        obtain ⟨r, o, listRun, listCorrect, agree⟩ := optional_list_total_correct cx next (.Blank node) out1
        rw [length1] at listCorrect
        rcases r with ⟨finish, out2⟩ | e
        · obtain ⟨us, rfl, contents2⟩ := emitted_ok agree
          refine ⟨.Ok (finish, out2), _, ?_, .listed opening bracketCorrect listCorrect,
            emitted_intro (by rw [contents2, contents1, List.append_assoc])⟩
          rw [turtle.triples]
          simp [byte_is_spec, opening, bracketRun, core.result.Result.Insts.CoreOpsTry.branch, listRun]
        · obtain rfl := emitted_err agree
          refine ⟨.Err e, _, ?_, .listedFails opening bracketCorrect listCorrect, rfl⟩
          rw [turtle.triples]
          simp [byte_is_spec, opening, bracketRun, core.result.Result.Insts.CoreOpsTry.branch, listRun]
    · obtain rfl := bracket_err agree
      refine ⟨.Err e, _, ?_, .bracketFails opening bracketCorrect, rfl⟩
      rw [turtle.triples]
      simp [byte_is_spec, opening, bracketRun, core.result.Result.Insts.CoreOpsTry.branch]
  · obtain ⟨r, o, subjectRun, subjectCorrect, agree⟩ := subject_total_correct cx start out
    rcases r with ⟨s, next, out1⟩ | e
    · obtain ⟨ts, rfl, contents1⟩ := grown_ok agree
      have length1 := map_length contents1
      obtain ⟨r, o, listRun, listCorrect, agree⟩ := predicate_object_list_total_correct cx next s out1
      rw [length1] at listCorrect
      rcases r with ⟨finish, out2⟩ | e
      · obtain ⟨us, rfl, contents2⟩ := emitted_ok agree
        refine ⟨.Ok (finish, out2), _, ?_, .subject opening subjectCorrect listCorrect,
          emitted_intro (by rw [contents2, contents1, List.append_assoc])⟩
        rw [turtle.triples]
        simp [byte_is_spec, opening, subjectRun, core.result.Result.Insts.CoreOpsTry.branch, listRun]
      · obtain rfl := emitted_err agree
        refine ⟨.Err e, _, ?_, .subjectListFails opening subjectCorrect listCorrect, rfl⟩
        rw [turtle.triples]
        simp [byte_is_spec, opening, subjectRun, core.result.Result.Insts.CoreOpsTry.branch, listRun]
    · obtain rfl := grown_err agree
      refine ⟨.Err e, _, ?_, .subjectFails opening subjectCorrect, rfl⟩
      rw [turtle.triples]
      simp [byte_is_spec, opening, subjectRun, core.result.Result.Insts.CoreOpsTry.branch]

theorem triples_accepted (cx : turtle.Context) (start : Usize) (out : alloc.vec.Vec rdf.Triple) {n : Nat}
    {ts : List Spo} (found : TriplesAt (ctxOf cx) start.val out.val.length (.ok (n, ts))) :
    ∃ next out', turtle.triples cx start out = .ok (.Ok (next, out')) ∧ next.val = n ∧
      out'.val.map spo = out.val.map spo ++ ts ∧ start.val < n ∧ n ≤ cx.bytes.val.length := by
  generalize result : (Except.ok (n, ts) : Except Fault (Nat × List Spo)) = given at found
  cases found with
  | bracketFails _ _ => cases result
  | anonFails _ _ _ => cases result
  | @anon t m ts' k us opening bracketFound listFound =>
    cases result
    have opening : ByteIs cx.bytes.val start.val 91 := opening
    obtain ⟨b, next, out1, bracketRun, value, nextValue, contents1, lower, upper⟩ :=
      bracket_accepted cx start out bracketFound
    have length1 := map_length contents1
    subst value
    subst nextValue
    rw [← length1] at listFound
    obtain ⟨finish, out2, listRun, finishValue, contents2, lower2, upper2⟩ :=
      predicate_object_list_accepted cx next (.Blank b) out1 listFound
    refine ⟨finish, out2, ?_, finishValue, by rw [contents2, contents1, List.append_assoc], by omega, by omega⟩
    rw [turtle.triples]
    simp [byte_is_spec, opening, bracketRun, core.result.Result.Insts.CoreOpsTry.branch, listRun]
  | listedFails _ _ _ => cases result
  | @listed t m ts' k us opening bracketFound listFound =>
    cases result
    have opening : ByteIs cx.bytes.val start.val 91 := opening
    obtain ⟨b, next, out1, bracketRun, value, nextValue, contents1, lower, upper⟩ :=
      bracket_accepted cx start out bracketFound
    have length1 := map_length contents1
    subst value
    subst nextValue
    rw [← length1] at listFound
    obtain ⟨finish, out2, listRun, finishValue, contents2, lower2, upper2⟩ :=
      optional_list_accepted cx next (.Blank b) out1 listFound
    refine ⟨finish, out2, ?_, finishValue, by rw [contents2, contents1, List.append_assoc], by omega, by omega⟩
    rw [turtle.triples]
    simp [byte_is_spec, opening, bracketRun, core.result.Result.Insts.CoreOpsTry.branch, listRun]
  | subjectFails _ _ => cases result
  | subjectListFails _ _ _ => cases result
  | @subject t m ts' k us opening subjectFound listFound =>
    cases result
    have opening : ¬ ByteIs cx.bytes.val start.val 91 := opening
    obtain ⟨s, next, out1, subjectRun, value, nextValue, contents1, lower, upper⟩ :=
      subject_accepted cx start out subjectFound
    have length1 := map_length contents1
    subst value
    subst nextValue
    rw [← length1] at listFound
    obtain ⟨finish, out2, listRun, finishValue, contents2, lower2, upper2⟩ :=
      predicate_object_list_accepted cx next s out1 listFound
    refine ⟨finish, out2, ?_, finishValue, by rw [contents2, contents1, List.append_assoc], by omega, by omega⟩
    rw [turtle.triples]
    simp [byte_is_spec, opening, subjectRun, core.result.Result.Insts.CoreOpsTry.branch, listRun]

/-! ## Periods and directives -/

theorem period_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) :
    ∃ r o, turtle.period bytes position = .ok r ∧ PeriodAt bytes.val position.val o ∧ Agrees (·.val) r o := by
  obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct bytes position
  rcases spaced with stop | e
  · have runs : TriviaRuns bytes.val true position.val stop.val := spaceCorrect
    by_cases period : ByteIs bytes.val stop.val 46
    · obtain ⟨j, add, jValue⟩ := add_one (byte_inside period)
      refine ⟨.Ok j, .ok (stop.val + 1), ?_, .period runs period, jValue⟩
      rw [turtle.period]
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, period, add]
    · refine ⟨.Err ⟨.ExpectedPeriod, stop⟩, .error (.ExpectedPeriod, stop.val), ?_, .missing runs period, rfl⟩
      rw [turtle.period]
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, period, error_spec]
  · refine ⟨.Err e, _, ?_, .spaceFails spaceCorrect, rfl⟩
    rw [turtle.period]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch]

theorem period_accepted {bytes : alloc.vec.Vec U8} {position : Usize} {m : Nat}
    (found : PeriodAt bytes.val position.val (.ok m)) :
    ∃ next, turtle.period bytes position = .ok (.Ok next) ∧ next.val = m ∧ position.val < m ∧
      m ≤ bytes.val.length := by
  generalize result : (Except.ok m : Except Fault Nat) = given at found
  cases found with
  | spaceFails _ => cases result
  | @period p spaced period =>
    cases result
    have bound := trivia_bound spaced
    have inside := byte_inside period
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    subst stopValue
    obtain ⟨j, add, jValue⟩ := add_one inside
    refine ⟨j, ?_, jValue, by omega, by omega⟩
    rw [turtle.period]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, byte_is_spec, period, add]
  | missing _ _ => cases result

theorem add_const {bytes : alloc.vec.Vec U8} {x k : Usize} (fits : x.val + k.val ≤ bytes.val.length) :
    ∃ y : Usize, (x + k : Result Usize) = .ok y ∧ y.val = x.val + k.val := by
  obtain ⟨y, add, value⟩ := WP.spec_imp_exists (Usize.add_spec (x := x) (y := k)
    (by have := bytes.property; scalar_tac))
  exact ⟨y, add, by simpa using value⟩

theorem byte_either {bs : List U8} {i u : Nat} (h : ByteIs bs i u ∨ ByteIs bs i (u + 32)) : i < bs.length := by
  rcases h with h | h <;> exact byte_inside h

theorem prefix_word_spec (bytes : alloc.vec.Vec U8) (start : Usize) :
    turtle.prefix_word bytes start = .ok (decide (AnyCase bytes.val start.val PrefixUpper)) := by
  unfold turtle.prefix_word
  simp only [PrefixUpper, AnyCase, and_true]
  by_cases a0 : ByteIs bytes.val start.val 80 ∨ ByteIs bytes.val start.val (80 + 32)
  · have in0 := byte_either a0
    obtain ⟨i1, add1, v1⟩ := add_const (bytes := bytes) (x := start) (k := 1#usize) (by simp; omega)
    simp only [show (1#usize : Usize).val = 1 from rfl] at v1
    by_cases a1 : ByteIs bytes.val (start.val + 1) 82 ∨ ByteIs bytes.val (start.val + 1) (82 + 32)
    · have in1 := byte_either a1
      obtain ⟨i2, add2, v2⟩ := add_const (bytes := bytes) (x := start) (k := 2#usize) (by simp; omega)
      simp only [show (2#usize : Usize).val = 2 from rfl] at v2
      by_cases a2 : ByteIs bytes.val (start.val + 1 + 1) 69 ∨ ByteIs bytes.val (start.val + 1 + 1) (69 + 32)
      · have in2 := byte_either a2
        obtain ⟨i3, add3, v3⟩ := add_const (bytes := bytes) (x := start) (k := 3#usize) (by simp; omega)
        simp only [show (3#usize : Usize).val = 3 from rfl] at v3
        by_cases a3 : ByteIs bytes.val (start.val + 1 + 1 + 1) 70 ∨
            ByteIs bytes.val (start.val + 1 + 1 + 1) (70 + 32)
        · have in3 := byte_either a3
          obtain ⟨i4, add4, v4⟩ := add_const (bytes := bytes) (x := start) (k := 4#usize) (by simp; omega)
          simp only [show (4#usize : Usize).val = 4 from rfl] at v4
          by_cases a4 : ByteIs bytes.val (start.val + 1 + 1 + 1 + 1) 73 ∨
              ByteIs bytes.val (start.val + 1 + 1 + 1 + 1) (73 + 32)
          · have in4 := byte_either a4
            obtain ⟨i5, add5, v5⟩ := add_const (bytes := bytes) (x := start) (k := 5#usize) (by simp; omega)
            simp only [show (5#usize : Usize).val = 5 from rfl] at v5
            have e1 : start.val + 1 + 1 = start.val + 2 := by omega
            have e2 : start.val + 1 + 1 + 1 = start.val + 3 := by omega
            have e3 : start.val + 1 + 1 + 1 + 1 = start.val + 4 := by omega
            have e4 : start.val + 1 + 1 + 1 + 1 + 1 = start.val + 5 := by omega
            simp only [e1, e2, e3, e4] at a2 a3 a4 ⊢
            simp only [Nat.reduceAdd] at a0 a1 a2 a3 a4 ⊢
            simp [either_spec, a0, a1, a2, a3, a4, add1, v1, add2, v2, add3, v3, add4, v4, add5, v5]
          · have e1 : start.val + 1 + 1 = start.val + 2 := by omega
            have e2 : start.val + 1 + 1 + 1 = start.val + 3 := by omega
            have e3 : start.val + 1 + 1 + 1 + 1 = start.val + 4 := by omega
            simp only [e1, e2, e3] at a2 a3 a4 ⊢
            simp only [Nat.reduceAdd] at a0 a1 a2 a3 a4 ⊢
            simp [either_spec, a0, a1, a2, a3, a4, add1, v1, add2, v2, add3, v3, add4, v4]
        · have e1 : start.val + 1 + 1 = start.val + 2 := by omega
          have e2 : start.val + 1 + 1 + 1 = start.val + 3 := by omega
          simp only [e1, e2] at a2 a3 ⊢
          simp only [Nat.reduceAdd] at a0 a1 a2 a3 ⊢
          simp [either_spec, a0, a1, a2, a3, add1, v1, add2, v2, add3, v3]
      · have e1 : start.val + 1 + 1 = start.val + 2 := by omega
        simp only [e1] at a2 ⊢
        simp only [Nat.reduceAdd] at a0 a1 a2 ⊢
        simp [either_spec, a0, a1, a2, add1, v1, add2, v2]
    · simp only [Nat.reduceAdd] at a0 a1 ⊢
      simp [either_spec, a0, a1, add1, v1]
  · simp only [Nat.reduceAdd] at a0 ⊢
    simp [either_spec, a0]


theorem base_word_spec (bytes : alloc.vec.Vec U8) (start : Usize) :
    turtle.base_word bytes start = .ok (decide (AnyCase bytes.val start.val BaseUpper)) := by
  unfold turtle.base_word
  simp only [BaseUpper, AnyCase, and_true]
  by_cases a0 : ByteIs bytes.val start.val 66 ∨ ByteIs bytes.val start.val (66 + 32)
  · have in0 := byte_either a0
    obtain ⟨i1, add1, v1⟩ := add_const (bytes := bytes) (x := start) (k := 1#usize) (by simp; omega)
    simp only [show (1#usize : Usize).val = 1 from rfl] at v1
    by_cases a1 : ByteIs bytes.val (start.val + 1) 65 ∨ ByteIs bytes.val (start.val + 1) (65 + 32)
    · have in1 := byte_either a1
      obtain ⟨i2, add2, v2⟩ := add_const (bytes := bytes) (x := start) (k := 2#usize) (by simp; omega)
      simp only [show (2#usize : Usize).val = 2 from rfl] at v2
      by_cases a2 : ByteIs bytes.val (start.val + 1 + 1) 83 ∨ ByteIs bytes.val (start.val + 1 + 1) (83 + 32)
      · have in2 := byte_either a2
        obtain ⟨i3, add3, v3⟩ := add_const (bytes := bytes) (x := start) (k := 3#usize) (by simp; omega)
        simp only [show (3#usize : Usize).val = 3 from rfl] at v3
        have e1 : start.val + 1 + 1 = start.val + 2 := by omega
        have e2 : start.val + 1 + 1 + 1 = start.val + 3 := by omega
        simp only [e1, e2] at a2 ⊢
        simp only [Nat.reduceAdd] at a0 a1 a2 ⊢
        simp [either_spec, a0, a1, a2, add1, v1, add2, v2, add3, v3]
      · have e1 : start.val + 1 + 1 = start.val + 2 := by omega
        simp only [e1] at a2 ⊢
        simp only [Nat.reduceAdd] at a0 a1 a2 ⊢
        simp [either_spec, a0, a1, a2, add1, v1, add2, v2]
    · simp only [Nat.reduceAdd] at a0 a1 ⊢
      simp [either_spec, a0, a1, add1, v1]
  · simp only [Nat.reduceAdd] at a0 ⊢
    simp [either_spec, a0]

theorem at_keyword_fits {bs : List U8} {start : Nat} {word : List U8} (h : AtKeyword bs start word) :
    start + 1 + word.length ≤ bs.length := by
  have prefixLength := h.2.1.length_le
  have inside := byte_inside h.1
  simp at prefixLength
  omega

theorem any_case_fits {bs : List U8} : ∀ {u : Nat} {us : List Nat} {i : Nat}, AnyCase bs i (u :: us) →
    i + us.length + 1 ≤ bs.length
  | u, [], i, h => by
    simp only [AnyCase, and_true] at h
    have := byte_either h
    simp
    omega
  | u, v :: us, i, h => by
    simp only [AnyCase] at h
    have := any_case_fits (u := v) (us := us) (i := i + 1) h.2
    simp
    omega

/-- A statement opening agrees with an outcome: the same opening, with the
    position after its keyword, or the same failure. -/
def StartAgrees (start : Nat) : core.result.Result turtle.Statement turtle.ReadError → Except Fault Opening → Prop
  | .Ok (.AtPrefix i), .ok .atPrefix => i.val = start + 7
  | .Ok (.AtBase i), .ok .atBase => i.val = start + 5
  | .Ok (.Prefix i), .ok .sparqlPrefix => i.val = start + 6
  | .Ok (.Base i), .ok .sparqlBase => i.val = start + 4
  | .Ok .Triples, .ok .triples => True
  | .Err e, .error f => faultOf e = f
  | _, _ => False

theorem statement_start_total_correct (bytes : alloc.vec.Vec U8) (start : Usize) :
    ∃ r o, turtle.statement_start bytes start = .ok r ∧ OpeningAt bytes.val start.val o ∧
      StartAgrees start.val r o := by
  unfold turtle.statement_start
  have prefixAt := at_keyword_spec bytes start
    (Array.to_slice (Array.make 6#usize [112#u8, 114#u8, 101#u8, 102#u8, 105#u8, 120#u8]))
  have baseAt := at_keyword_spec bytes start (Array.to_slice (Array.make 4#usize [98#u8, 97#u8, 115#u8, 101#u8]))
  rw [slice_array] at prefixAt baseAt
  by_cases atPrefix : AtKeyword bytes.val start.val PrefixWord
  · have fits := at_keyword_fits atPrefix
    obtain ⟨i, add, iValue⟩ := add_const (bytes := bytes) (x := start) (k := 7#usize)
      (by simp [PrefixWord] at fits ⊢; omega)
    refine ⟨.Ok (.AtPrefix i), .ok .atPrefix, ?_, .atPrefix atPrefix, by simp only [StartAgrees]; simpa using iValue⟩
    simp only [PrefixWord] at atPrefix
    simp [prefixAt, atPrefix, add]
  · by_cases atBase : AtKeyword bytes.val start.val BaseWord
    · have fits := at_keyword_fits atBase
      obtain ⟨i, add, iValue⟩ := add_const (bytes := bytes) (x := start) (k := 5#usize)
        (by simp [BaseWord] at fits ⊢; omega)
      refine ⟨.Ok (.AtBase i), .ok .atBase, ?_, .atBase atPrefix atBase, by simp only [StartAgrees]; simpa using iValue⟩
      simp only [PrefixWord] at atPrefix
      simp only [BaseWord] at atBase
      simp [prefixAt, atPrefix, baseAt, atBase, add]
    · by_cases sparqlPrefix : AnyCase bytes.val start.val PrefixUpper
      · have fits := any_case_fits (show AnyCase bytes.val start.val (80 :: [82, 69, 70, 73, 88]) from sparqlPrefix)
        obtain ⟨i, add, iValue⟩ := add_const (bytes := bytes) (x := start) (k := 6#usize) (by simp at fits ⊢; omega)
        obtain ⟨r, o, colonRun, colonCorrect, agree⟩ := prefix_colon_total_correct bytes start
        simp only [PrefixWord] at atPrefix
        simp only [BaseWord] at atBase
        rcases r with (_ | colon) | e
        · obtain rfl := agrees_ok agree
          refine ⟨.Ok (.Prefix i), .ok .sparqlPrefix, ?_, .sparqlPrefix atPrefix atBase sparqlPrefix colonCorrect,
            by simp only [StartAgrees]; simpa using iValue⟩
          simp [prefixAt, atPrefix, baseAt, atBase, prefix_word_spec, sparqlPrefix, add, turtle.sparql, colonRun,
            core.result.Result.Insts.CoreOpsTry.branch]
        · obtain rfl := agrees_ok agree
          refine ⟨.Ok .Triples, .ok .triples, ?_, .prefixName atPrefix atBase sparqlPrefix colonCorrect, trivial⟩
          simp [prefixAt, atPrefix, baseAt, atBase, prefix_word_spec, sparqlPrefix, add, turtle.sparql, colonRun,
            core.result.Result.Insts.CoreOpsTry.branch]
        · obtain rfl := agrees_err agree
          refine ⟨.Err e, _, ?_, .prefixFails atPrefix atBase sparqlPrefix colonCorrect, rfl⟩
          simp [prefixAt, atPrefix, baseAt, atBase, prefix_word_spec, sparqlPrefix, add, turtle.sparql, colonRun,
            core.result.Result.Insts.CoreOpsTry.branch]
      · by_cases sparqlBase : AnyCase bytes.val start.val BaseUpper
        · have fits := any_case_fits (show AnyCase bytes.val start.val (66 :: [65, 83, 69]) from sparqlBase)
          obtain ⟨i, add, iValue⟩ := add_const (bytes := bytes) (x := start) (k := 4#usize) (by simp at fits ⊢; omega)
          obtain ⟨r, o, colonRun, colonCorrect, agree⟩ := prefix_colon_total_correct bytes start
          simp only [PrefixWord] at atPrefix
          simp only [BaseWord] at atBase
          rcases r with (_ | colon) | e
          · obtain rfl := agrees_ok agree
            refine ⟨.Ok (.Base i), .ok .sparqlBase, ?_,
              .sparqlBase atPrefix atBase sparqlPrefix sparqlBase colonCorrect, by simp only [StartAgrees]; simpa using iValue⟩
            simp [prefixAt, atPrefix, baseAt, atBase, prefix_word_spec, sparqlPrefix, base_word_spec, sparqlBase,
              add, turtle.sparql, colonRun, core.result.Result.Insts.CoreOpsTry.branch]
          · obtain rfl := agrees_ok agree
            refine ⟨.Ok .Triples, .ok .triples, ?_, .baseName atPrefix atBase sparqlPrefix sparqlBase colonCorrect,
              trivial⟩
            simp [prefixAt, atPrefix, baseAt, atBase, prefix_word_spec, sparqlPrefix, base_word_spec, sparqlBase,
              add, turtle.sparql, colonRun, core.result.Result.Insts.CoreOpsTry.branch]
          · obtain rfl := agrees_err agree
            refine ⟨.Err e, _, ?_, .baseFails atPrefix atBase sparqlPrefix sparqlBase colonCorrect, rfl⟩
            simp [prefixAt, atPrefix, baseAt, atBase, prefix_word_spec, sparqlPrefix, base_word_spec, sparqlBase,
              add, turtle.sparql, colonRun, core.result.Result.Insts.CoreOpsTry.branch]
        · refine ⟨.Ok .Triples, .ok .triples, ?_, .triples atPrefix atBase sparqlPrefix sparqlBase, trivial⟩
          simp only [PrefixWord] at atPrefix
          simp only [BaseWord] at atBase
          simp [prefixAt, atPrefix, baseAt, atBase, prefix_word_spec, sparqlPrefix, base_word_spec, sparqlBase]

theorem opening_accepted {bytes : alloc.vec.Vec U8} {start : Usize} {op : Opening}
    (found : OpeningAt bytes.val start.val (.ok op)) :
    ∃ s, turtle.statement_start bytes start = .ok (.Ok s) ∧ StartAgrees start.val (.Ok s) (.ok op) := by
  unfold turtle.statement_start
  have prefixAt := at_keyword_spec bytes start
    (Array.to_slice (Array.make 6#usize [112#u8, 114#u8, 101#u8, 102#u8, 105#u8, 120#u8]))
  have baseAt := at_keyword_spec bytes start (Array.to_slice (Array.make 4#usize [98#u8, 97#u8, 115#u8, 101#u8]))
  rw [slice_array] at prefixAt baseAt
  generalize result : (Except.ok op : Except Fault Opening) = given at found
  cases found with
  | atPrefix atPrefix =>
    cases result
    have fits := at_keyword_fits atPrefix
    obtain ⟨i, add, iValue⟩ := add_const (bytes := bytes) (x := start) (k := 7#usize)
      (by simp [PrefixWord] at fits ⊢; omega)
    refine ⟨.AtPrefix i, ?_, by simp only [StartAgrees]; simpa using iValue⟩
    simp only [PrefixWord] at atPrefix
    simp [prefixAt, atPrefix, add]
  | atBase atPrefix atBase =>
    cases result
    have fits := at_keyword_fits atBase
    obtain ⟨i, add, iValue⟩ := add_const (bytes := bytes) (x := start) (k := 5#usize)
      (by simp [BaseWord] at fits ⊢; omega)
    refine ⟨.AtBase i, ?_, by simp only [StartAgrees]; simpa using iValue⟩
    simp only [PrefixWord] at atPrefix
    simp only [BaseWord] at atBase
    simp [prefixAt, atPrefix, baseAt, atBase, add]
  | prefixFails _ _ _ _ => cases result
  | @prefixName colon atPrefix atBase sparqlPrefix colonFound =>
    cases result
    have fits := any_case_fits (show AnyCase bytes.val start.val (80 :: [82, 69, 70, 73, 88]) from sparqlPrefix)
    obtain ⟨i, add, iValue⟩ := add_const (bytes := bytes) (x := start) (k := 6#usize) (by simp at fits ⊢; omega)
    obtain ⟨c, colonRun, colonValue⟩ := prefix_colon_accepted colonFound
    cases c with
    | none => simp at colonValue
    | some colon' =>
      refine ⟨.Triples, ?_, trivial⟩
      simp only [PrefixWord] at atPrefix
      simp only [BaseWord] at atBase
      simp [prefixAt, atPrefix, baseAt, atBase, prefix_word_spec, sparqlPrefix, add, turtle.sparql, colonRun,
        core.result.Result.Insts.CoreOpsTry.branch]
  | sparqlPrefix atPrefix atBase sparqlPrefix colonFound =>
    cases result
    have fits := any_case_fits (show AnyCase bytes.val start.val (80 :: [82, 69, 70, 73, 88]) from sparqlPrefix)
    obtain ⟨i, add, iValue⟩ := add_const (bytes := bytes) (x := start) (k := 6#usize) (by simp at fits ⊢; omega)
    obtain ⟨c, colonRun, colonValue⟩ := prefix_colon_accepted colonFound
    cases c with
    | some _ => simp at colonValue
    | none =>
      refine ⟨.Prefix i, ?_, by simp only [StartAgrees]; simpa using iValue⟩
      simp only [PrefixWord] at atPrefix
      simp only [BaseWord] at atBase
      simp [prefixAt, atPrefix, baseAt, atBase, prefix_word_spec, sparqlPrefix, add, turtle.sparql, colonRun,
        core.result.Result.Insts.CoreOpsTry.branch]
  | baseFails _ _ _ _ _ => cases result
  | @baseName colon atPrefix atBase sparqlPrefix sparqlBase colonFound =>
    cases result
    have fits := any_case_fits (show AnyCase bytes.val start.val (66 :: [65, 83, 69]) from sparqlBase)
    obtain ⟨i, add, iValue⟩ := add_const (bytes := bytes) (x := start) (k := 4#usize) (by simp at fits ⊢; omega)
    obtain ⟨c, colonRun, colonValue⟩ := prefix_colon_accepted colonFound
    cases c with
    | none => simp at colonValue
    | some colon' =>
      refine ⟨.Triples, ?_, trivial⟩
      simp only [PrefixWord] at atPrefix
      simp only [BaseWord] at atBase
      simp [prefixAt, atPrefix, baseAt, atBase, prefix_word_spec, sparqlPrefix, base_word_spec, sparqlBase, add,
        turtle.sparql, colonRun, core.result.Result.Insts.CoreOpsTry.branch]
  | sparqlBase atPrefix atBase sparqlPrefix sparqlBase colonFound =>
    cases result
    have fits := any_case_fits (show AnyCase bytes.val start.val (66 :: [65, 83, 69]) from sparqlBase)
    obtain ⟨i, add, iValue⟩ := add_const (bytes := bytes) (x := start) (k := 4#usize) (by simp at fits ⊢; omega)
    obtain ⟨c, colonRun, colonValue⟩ := prefix_colon_accepted colonFound
    cases c with
    | some _ => simp at colonValue
    | none =>
      refine ⟨.Base i, ?_, by simp only [StartAgrees]; simpa using iValue⟩
      simp only [PrefixWord] at atPrefix
      simp only [BaseWord] at atBase
      simp [prefixAt, atPrefix, baseAt, atBase, prefix_word_spec, sparqlPrefix, base_word_spec, sparqlBase, add,
        turtle.sparql, colonRun, core.result.Result.Insts.CoreOpsTry.branch]
  | triples atPrefix atBase sparqlPrefix sparqlBase =>
    cases result
    refine ⟨.Triples, ?_, trivial⟩
    simp only [PrefixWord] at atPrefix
    simp only [BaseWord] at atBase
    simp [prefixAt, atPrefix, baseAt, atBase, prefix_word_spec, sparqlPrefix, base_word_spec, sparqlBase]

theorem copied_spec (bytes : alloc.vec.Vec U8) (start finish limit : Usize)
    (range : start.val ≤ finish.val ∧ finish.val ≤ bytes.val.length) :
    ∃ r, turtle.copied bytes start finish limit = .ok r ∧
      (finish.val - start.val ≤ limit.val → ∃ v, r = .Ok v ∧ v.val = Span bytes.val start.val finish.val) ∧
      (limit.val < finish.val - start.val → ∃ e, r = .Err e ∧ faultOf e = (.ResourceLimit, start.val)) := by
  obtain ⟨copied, copyRun, copyCorrect⟩ := Rowl.NTriples.copy_term_total_correct bytes start finish limit range
  cases copied with
  | Ok v =>
    obtain ⟨fits, value⟩ := copyCorrect
    exact ⟨.Ok v, by simp [turtle.copied, copyRun], fun _ => ⟨v, rfl, value⟩, fun over => absurd fits (by omega)⟩
  | Err e =>
    obtain ⟨over, kindIs, offset⟩ := copyCorrect
    exact ⟨.Err ⟨KindOf e.kind, e.offset⟩, by simp [turtle.copied, copyRun, lift_spec],
      fun fits => absurd fits (by omega), fun _ => ⟨_, rfl, by simp [faultOf, kindIs, KindOf, offset]⟩⟩

/-- The view of a prefix declaration: its name and namespace, and the end. -/
def prefixView (pair : turtle.Prefix × Usize) : (List U8 × List U8) × Nat :=
  ((pair.1.«name».val, pair.1.iri.val), pair.2.val)

theorem prefix_declaration_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) (base : alloc.vec.Vec U8)
    (limit : Usize) :
    ∃ r o, turtle.prefix_declaration bytes position base limit = .ok r ∧
      PrefixDeclaration bytes.val base.val limit.val position.val o ∧ Agrees prefixView r o := by
  unfold turtle.prefix_declaration turtle.prefix_name
  obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct bytes position
  rcases spaced with s | e
  · have runs : TriviaRuns bytes.val true position.val s.val := spaceCorrect
    obtain ⟨r, o, colonRun, colonCorrect, agree⟩ := prefix_colon_total_correct bytes s
    rcases r with (_ | colon) | e
    · obtain rfl := agrees_ok agree
      refine ⟨.Err ⟨.ExpectedPrefix, s⟩, .error (.ExpectedPrefix, s.val), ?_, .missing runs colonCorrect, rfl⟩
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, colonRun, error_spec]
    · obtain rfl := agrees_ok agree
      have colonCorrect : PrefixColon bytes.val s.val (.ok (some colon.val)) := colonCorrect
      have colonBound := prefix_colon_bound colonCorrect
      obtain ⟨copied, copyRun, copyOk, copyErr⟩ := copied_spec bytes s colon limit ⟨colonBound.1, by omega⟩
      by_cases fits : colon.val - s.val ≤ limit.val
      · obtain ⟨spelled, rfl, spelledValue⟩ := copyOk fits
        obtain ⟨after, add, afterValue⟩ := add_one colonBound.2
        obtain ⟨spaced2, spaceRun2, spaceCorrect2⟩ := space_total_correct bytes after
        rw [afterValue] at spaceCorrect2
        rcases spaced2 with p | e
        · have runs2 : TriviaRuns bytes.val true (colon.val + 1) p.val := spaceCorrect2
          obtain ⟨r, o, iriRun, iriCorrect, agree⟩ := iri_ref_total_correct bytes p base limit
          rcases r with ⟨ns, next⟩ | e
          · obtain rfl := agrees_ok agree
            refine ⟨.Ok (⟨spelled, ns.spelling⟩, next), _, ?_, .declaration runs colonCorrect fits runs2 iriCorrect, ?_⟩
            · simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, colonRun, copyRun, add, spaceRun2, iriRun]
            · simp [Agrees, prefixView, spelledValue, iriView]
          · obtain rfl := agrees_err agree
            refine ⟨.Err e, _, ?_, .iriFails runs colonCorrect fits runs2 iriCorrect, rfl⟩
            simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, colonRun, copyRun, add, spaceRun2, iriRun]
        · refine ⟨.Err e, _, ?_, .iriSpaceFails runs colonCorrect fits spaceCorrect2, rfl⟩
          simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, colonRun, copyRun, add, spaceRun2]
      · obtain ⟨e, rfl, faultIs⟩ := copyErr (by omega)
        refine ⟨.Err e, .error (.ResourceLimit, s.val), ?_, .tooLong runs colonCorrect (by omega), faultIs⟩
        simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, colonRun, copyRun]
    · obtain rfl := agrees_err agree
      refine ⟨.Err e, _, ?_, .colonFails runs colonCorrect, rfl⟩
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, colonRun]
  · refine ⟨.Err e, _, ?_, .spaceFails spaceCorrect, rfl⟩
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch]

theorem prefix_declaration_accepted {bytes : alloc.vec.Vec U8} {position : Usize} {base : alloc.vec.Vec U8}
    {limit : Usize} {decl : List U8 × List U8} {n : Nat}
    (found : PrefixDeclaration bytes.val base.val limit.val position.val (.ok (decl, n))) :
    ∃ p next, turtle.prefix_declaration bytes position base limit = .ok (.Ok (p, next)) ∧
      (p.«name».val, p.iri.val) = decl ∧ next.val = n ∧ position.val < n ∧ n ≤ bytes.val.length := by
  generalize result : (Except.ok (decl, n) : Except Fault ((List U8 × List U8) × Nat)) = given at found
  cases found with
  | spaceFails _ => cases result
  | colonFails _ _ => cases result
  | missing _ _ => cases result
  | tooLong _ _ _ => cases result
  | iriSpaceFails _ _ _ _ => cases result
  | iriFails _ _ _ _ _ => cases result
  | @declaration s colon p ns m spaced colonFound fits spaced2 iriFound =>
    cases result
    unfold turtle.prefix_declaration turtle.prefix_name
    have bound := trivia_bound spaced
    obtain ⟨start, spaceRun, startValue⟩ := space_runs spaced
    subst startValue
    have colonBound := prefix_colon_bound colonFound
    obtain ⟨c, colonRun, colonValue⟩ := prefix_colon_accepted colonFound
    cases c with
    | none => simp at colonValue
    | some colon' =>
      simp only [Option.map_some, Option.some.injEq] at colonValue
      subst colonValue
      obtain ⟨copied, copyRun, copyOk, _⟩ := copied_spec bytes start colon' limit ⟨colonBound.1, by omega⟩
      obtain ⟨spelled, rfl, spelledValue⟩ := copyOk fits
      obtain ⟨after, add, afterValue⟩ := add_one colonBound.2
      have bound2 := trivia_bound spaced2
      obtain ⟨iriStart, spaceRun2, iriStartValue⟩ := space_runs (bytes := bytes) (position := after)
        (by rw [afterValue]; exact spaced2)
      subst iriStartValue
      have iriBound := iri_ref_bound iriFound
      obtain ⟨iri, next, iriRun, iriValue, nextValue⟩ := iri_ref_accepted iriFound
      refine ⟨⟨spelled, iri.spelling⟩, next, ?_, by simp [spelledValue, iriValue], nextValue, by omega, by omega⟩
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, colonRun, copyRun, add, spaceRun2, iriRun]

theorem base_declaration_total_correct (bytes : alloc.vec.Vec U8) (position : Usize) (base : alloc.vec.Vec U8)
    (limit : Usize) :
    ∃ r o, turtle.base_declaration bytes position base limit = .ok r ∧
      BaseDeclaration bytes.val base.val limit.val position.val o ∧ Agrees stringView r o := by
  unfold turtle.base_declaration
  obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct bytes position
  rcases spaced with s | e
  · have runs : TriviaRuns bytes.val true position.val s.val := spaceCorrect
    obtain ⟨r, o, iriRun, iriCorrect, agree⟩ := iri_ref_total_correct bytes s base limit
    rcases r with ⟨iri, next⟩ | e
    · obtain rfl := agrees_ok agree
      refine ⟨.Ok (iri.spelling, next), _, ?_, .iri runs iriCorrect, rfl⟩
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, iriRun]
    · obtain rfl := agrees_err agree
      refine ⟨.Err e, _, ?_, .iri runs iriCorrect, rfl⟩
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, iriRun]
  · refine ⟨.Err e, _, ?_, .spaceFails spaceCorrect, rfl⟩
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch]

theorem base_declaration_accepted {bytes : alloc.vec.Vec U8} {position : Usize} {base : alloc.vec.Vec U8}
    {limit : Usize} {b : List U8} {n : Nat} (found : BaseDeclaration bytes.val base.val limit.val position.val (.ok (b, n))) :
    ∃ v next, turtle.base_declaration bytes position base limit = .ok (.Ok (v, next)) ∧ v.val = b ∧ next.val = n ∧
      position.val < n ∧ n ≤ bytes.val.length := by
  generalize result : (Except.ok (b, n) : Except Fault (List U8 × Nat)) = given at found
  cases found with
  | spaceFails _ => cases result
  | @iri s r spaced iriFound =>
    subst result
    unfold turtle.base_declaration
    have bound := trivia_bound spaced
    obtain ⟨start, spaceRun, startValue⟩ := space_runs spaced
    subst startValue
    have iriBound := iri_ref_bound iriFound
    obtain ⟨iri, next, iriRun, iriValue, nextValue⟩ := iri_ref_accepted iriFound
    refine ⟨iri.spelling, next, ?_, iriValue, nextValue, by omega, by omega⟩
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, iriRun]

/-! ## Statements and documents -/

/-- The document of the reader's inputs. -/
def docOf (bytes scope : alloc.vec.Vec U8) (limits : turtle.Limits) : Doc :=
  ⟨bytes.val, scope.val, limits.max_term_bytes.val, limits.max_triples.val⟩

/-- The environment of the reader's state. -/
def envOf (state : turtle.State) : Env := ⟨state.base.val, declarations state.prefixes.val⟩

/-- A statement result agrees with an outcome: the same end, environment and
    new triples, or the same failure. -/
def StatementAgrees (state : turtle.State) :
    core.result.Result (Usize × turtle.State) turtle.ReadError → Except Fault (Nat × Env × List Spo) → Prop
  | .Ok (n, s), .ok (m, e, ts) => n.val = m ∧ envOf s = e ∧ s.triples.val.map spo = state.triples.val.map spo ++ ts
  | .Err e, .error f => faultOf e = f
  | _, _ => False

/-- A result of all triples agrees with an outcome: the triples `out` before
    and the new ones, or the same failure. -/
def TriplesAgrees (out : List rdf.Triple) :
    core.result.Result (alloc.vec.Vec rdf.Triple) turtle.ReadError → Except Fault (List Spo) → Prop
  | .Ok v, .ok ts => v.val.map spo = out.map spo ++ ts
  | .Err e, .error f => faultOf e = f
  | _, _ => False

theorem statement_ok {state : turtle.State} {n : Usize} {s : turtle.State} {o : Except Fault (Nat × Env × List Spo)}
    (h : StatementAgrees state (.Ok (n, s)) o) :
    ∃ ts, o = .ok (n.val, envOf s, ts) ∧ s.triples.val.map spo = state.triples.val.map spo ++ ts := by
  rcases o with f | ⟨m, e, ts⟩
  · exact False.elim h
  · obtain ⟨h1, h2, h3⟩ := h
    exact ⟨ts, by rw [h1, h2], h3⟩

theorem statement_err {state : turtle.State} {e : turtle.ReadError} {o : Except Fault (Nat × Env × List Spo)}
    (h : StatementAgrees state (.Err e) o) : o = .error (faultOf e) := by
  rcases o with f | v
  · simp only [StatementAgrees] at h; rw [h]
  · exact False.elim h

theorem triples_ok {out : List rdf.Triple} {v : alloc.vec.Vec rdf.Triple} {o : Except Fault (List Spo)}
    (h : TriplesAgrees out (.Ok v) o) : ∃ ts, o = .ok ts ∧ v.val.map spo = out.map spo ++ ts := by
  rcases o with f | ts
  · exact False.elim h
  · exact ⟨ts, rfl, h⟩

theorem triples_err {out : List rdf.Triple} {e : turtle.ReadError} {o : Except Fault (List Spo)}
    (h : TriplesAgrees out (.Err e) o) : o = .error (faultOf e) := by
  rcases o with f | ts
  · simp only [TriplesAgrees] at h; rw [h]
  · exact False.elim h

theorem start_at_prefix {start : Nat} {i : Usize} {o : Except Fault Opening}
    (h : StartAgrees start (.Ok (.AtPrefix i)) o) : o = .ok .atPrefix ∧ i.val = start + 7 := by
  rcases o with f | op
  · exact False.elim h
  · cases op <;> first | exact ⟨rfl, h⟩ | exact False.elim h

theorem start_at_base {start : Nat} {i : Usize} {o : Except Fault Opening}
    (h : StartAgrees start (.Ok (.AtBase i)) o) : o = .ok .atBase ∧ i.val = start + 5 := by
  rcases o with f | op
  · exact False.elim h
  · cases op <;> first | exact ⟨rfl, h⟩ | exact False.elim h

theorem start_prefix {start : Nat} {i : Usize} {o : Except Fault Opening}
    (h : StartAgrees start (.Ok (.Prefix i)) o) : o = .ok .sparqlPrefix ∧ i.val = start + 6 := by
  rcases o with f | op
  · exact False.elim h
  · cases op <;> first | exact ⟨rfl, h⟩ | exact False.elim h

theorem start_base {start : Nat} {i : Usize} {o : Except Fault Opening}
    (h : StartAgrees start (.Ok (.Base i)) o) : o = .ok .sparqlBase ∧ i.val = start + 4 := by
  rcases o with f | op
  · exact False.elim h
  · cases op <;> first | exact ⟨rfl, h⟩ | exact False.elim h

theorem start_triples {start : Nat} {o : Except Fault Opening}
    (h : StartAgrees start (.Ok .Triples) o) : o = .ok .triples := by
  rcases o with f | op
  · exact False.elim h
  · cases op <;> first | rfl | exact False.elim h

theorem start_err {start : Nat} {e : turtle.ReadError} {o : Except Fault Opening}
    (h : StartAgrees start (.Err e) o) : o = .error (faultOf e) := by
  rcases o with f | op
  · simp only [StartAgrees] at h; rw [h]
  · exact False.elim h

theorem start_ok_at_prefix {start : Nat} {s : turtle.Statement} (h : StartAgrees start (.Ok s) (.ok .atPrefix)) :
    ∃ i, s = .AtPrefix i ∧ i.val = start + 7 := by
  cases s <;> first | exact ⟨_, rfl, h⟩ | exact False.elim h

theorem start_ok_at_base {start : Nat} {s : turtle.Statement} (h : StartAgrees start (.Ok s) (.ok .atBase)) :
    ∃ i, s = .AtBase i ∧ i.val = start + 5 := by
  cases s <;> first | exact ⟨_, rfl, h⟩ | exact False.elim h

theorem start_ok_prefix {start : Nat} {s : turtle.Statement} (h : StartAgrees start (.Ok s) (.ok .sparqlPrefix)) :
    ∃ i, s = .Prefix i ∧ i.val = start + 6 := by
  cases s <;> first | exact ⟨_, rfl, h⟩ | exact False.elim h

theorem start_ok_base {start : Nat} {s : turtle.Statement} (h : StartAgrees start (.Ok s) (.ok .sparqlBase)) :
    ∃ i, s = .Base i ∧ i.val = start + 4 := by
  cases s <;> first | exact ⟨_, rfl, h⟩ | exact False.elim h

theorem start_ok_triples {start : Nat} {s : turtle.Statement} (h : StartAgrees start (.Ok s) (.ok .triples)) :
    s = .Triples := by
  cases s <;> first | rfl | exact False.elim h

theorem declarations_push (prefixes : List turtle.Prefix) (p : turtle.Prefix) :
    declarations (prefixes ++ [p]) = declarations prefixes ++ [(p.«name».val, p.iri.val)] := by
  simp [declarations]

theorem statement_total_correct (bytes scope : alloc.vec.Vec U8) (limits : turtle.Limits) (start : Usize)
    (state : turtle.State) (inside : start.val < bytes.val.length) (room : state.prefixes.val.length ≤ start.val) :
    ∃ r o, turtle.statement bytes scope limits start state = .ok r ∧
      StatementAt (docOf bytes scope limits) (envOf state) start.val state.triples.val.length o ∧
      StatementAgrees state r o := by
  have pushRoom : state.prefixes.val.length < Usize.max := by have := bytes.property; omega
  obtain ⟨r, o, startRun, startCorrect, agree⟩ := statement_start_total_correct bytes start
  rcases r with ((after | after | after | after | _) | e)
  · obtain ⟨rfl, afterValue⟩ := start_at_prefix agree
    obtain ⟨r, o, declRun, declCorrect, agree⟩ :=
      prefix_declaration_total_correct bytes after state.base limits.max_term_bytes
    rw [afterValue] at declCorrect
    rcases r with ⟨p, next⟩ | e
    · obtain rfl := agrees_ok agree
      obtain ⟨r, o, periodRun, periodCorrect, agree⟩ := period_total_correct bytes next
      rcases r with m | e
      · obtain rfl := agrees_ok agree
        obtain ⟨prefixes, pushRun, pushValue⟩ :=
          WP.spec_imp_exists (alloc.vec.Vec.push_spec state.prefixes p pushRoom)
        refine ⟨.Ok (m, { state with prefixes := prefixes }), _, ?_,
          .atPrefix startCorrect declCorrect periodCorrect, ?_⟩
        · rw [turtle.statement]
          simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun, periodRun, turtle.declare, pushRun]
        · simp [StatementAgrees, envOf, pushValue, declarations_push, prefixView]
      · obtain rfl := agrees_err agree
        refine ⟨.Err e, _, ?_, .atPrefixPeriodFails startCorrect declCorrect periodCorrect, rfl⟩
        rw [turtle.statement]
        simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun, periodRun]
    · obtain rfl := agrees_err agree
      refine ⟨.Err e, _, ?_, .atPrefixFails startCorrect declCorrect, rfl⟩
      rw [turtle.statement]
      simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun]
  · obtain ⟨rfl, afterValue⟩ := start_at_base agree
    obtain ⟨r, o, declRun, declCorrect, agree⟩ :=
      base_declaration_total_correct bytes after state.base limits.max_term_bytes
    rw [afterValue] at declCorrect
    rcases r with ⟨b, next⟩ | e
    · obtain rfl := agrees_ok agree
      obtain ⟨r, o, periodRun, periodCorrect, agree⟩ := period_total_correct bytes next
      rcases r with m | e
      · obtain rfl := agrees_ok agree
        refine ⟨.Ok (m, { state with base := b }), _, ?_, .atBase startCorrect declCorrect periodCorrect, ?_⟩
        · rw [turtle.statement]
          simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun, periodRun]
        · simp [StatementAgrees, envOf, stringView]
      · obtain rfl := agrees_err agree
        refine ⟨.Err e, _, ?_, .atBasePeriodFails startCorrect declCorrect periodCorrect, rfl⟩
        rw [turtle.statement]
        simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun, periodRun]
    · obtain rfl := agrees_err agree
      refine ⟨.Err e, _, ?_, .atBaseFails startCorrect declCorrect, rfl⟩
      rw [turtle.statement]
      simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun]
  · obtain ⟨rfl, afterValue⟩ := start_prefix agree
    obtain ⟨r, o, declRun, declCorrect, agree⟩ :=
      prefix_declaration_total_correct bytes after state.base limits.max_term_bytes
    rw [afterValue] at declCorrect
    rcases r with ⟨p, next⟩ | e
    · obtain rfl := agrees_ok agree
      obtain ⟨prefixes, pushRun, pushValue⟩ :=
        WP.spec_imp_exists (alloc.vec.Vec.push_spec state.prefixes p pushRoom)
      refine ⟨.Ok (next, { state with prefixes := prefixes }), _, ?_, .sparqlPrefix startCorrect declCorrect, ?_⟩
      · rw [turtle.statement]
        simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun, turtle.declare, pushRun]
      · simp [StatementAgrees, envOf, pushValue, declarations_push, prefixView]
    · obtain rfl := agrees_err agree
      refine ⟨.Err e, _, ?_, .sparqlPrefixFails startCorrect declCorrect, rfl⟩
      rw [turtle.statement]
      simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun]
  · obtain ⟨rfl, afterValue⟩ := start_base agree
    obtain ⟨r, o, declRun, declCorrect, agree⟩ :=
      base_declaration_total_correct bytes after state.base limits.max_term_bytes
    rw [afterValue] at declCorrect
    rcases r with ⟨b, next⟩ | e
    · obtain rfl := agrees_ok agree
      refine ⟨.Ok (next, { state with base := b }), _, ?_, .sparqlBase startCorrect declCorrect, ?_⟩
      · rw [turtle.statement]
        simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun]
      · simp [StatementAgrees, envOf, stringView]
    · obtain rfl := agrees_err agree
      refine ⟨.Err e, _, ?_, .sparqlBaseFails startCorrect declCorrect, rfl⟩
      rw [turtle.statement]
      simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun]
  · obtain rfl := start_triples agree
    obtain ⟨r, o, triplesRun, triplesCorrect, agree⟩ :=
      triples_total_correct ⟨bytes, scope, state.base, state.prefixes, limits⟩ start state.triples
    rcases r with ⟨after, out⟩ | e
    · obtain ⟨ts, rfl, contents⟩ := emitted_ok agree
      obtain ⟨r, o, periodRun, periodCorrect, agree⟩ := period_total_correct bytes after
      rcases r with m | e
      · obtain rfl := agrees_ok agree
        refine ⟨.Ok (m, { state with triples := out }), _, ?_, .triples startCorrect triplesCorrect periodCorrect, ?_⟩
        · rw [turtle.statement]
          simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, triplesRun, periodRun]
        · simp [StatementAgrees, envOf, contents]
      · obtain rfl := agrees_err agree
        refine ⟨.Err e, _, ?_, .triplesPeriodFails startCorrect triplesCorrect periodCorrect, rfl⟩
        rw [turtle.statement]
        simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, triplesRun, periodRun]
    · obtain rfl := emitted_err agree
      refine ⟨.Err e, _, ?_, .triplesFails startCorrect triplesCorrect, rfl⟩
      rw [turtle.statement]
      simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, triplesRun]
  · obtain rfl := start_err agree
    refine ⟨.Err e, _, ?_, .openingFails startCorrect, rfl⟩
    rw [turtle.statement]
    simp [startRun, core.result.Result.Insts.CoreOpsTry.branch]

theorem statement_accepted (bytes scope : alloc.vec.Vec U8) (limits : turtle.Limits) (start : Usize)
    (state : turtle.State) (inside : start.val < bytes.val.length) (room : state.prefixes.val.length ≤ start.val)
    {m : Nat} {e' : Env} {ts : List Spo}
    (found : StatementAt (docOf bytes scope limits) (envOf state) start.val state.triples.val.length
      (.ok (m, e', ts))) :
    ∃ next s, turtle.statement bytes scope limits start state = .ok (.Ok (next, s)) ∧ next.val = m ∧
      envOf s = e' ∧ s.triples.val.map spo = state.triples.val.map spo ++ ts ∧ start.val < m ∧
      m ≤ bytes.val.length ∧ s.prefixes.val.length ≤ state.prefixes.val.length + 1 := by
  have pushRoom : state.prefixes.val.length < Usize.max := by have := bytes.property; omega
  generalize result : (Except.ok (m, e', ts) : Except Fault (Nat × Env × List Spo)) = given at found
  cases found with
  | openingFails _ => cases result
  | atPrefixFails _ _ => cases result
  | atPrefixPeriodFails _ _ _ => cases result
  | @atPrefix decl n m' opening declFound periodFound =>
    cases result
    obtain ⟨s, startRun, agree⟩ := opening_accepted opening
    obtain ⟨after, rfl, afterValue⟩ := start_ok_at_prefix agree
    rw [← afterValue] at declFound
    obtain ⟨p, next, declRun, declValue, nextValue, declLower, declUpper⟩ :=
      prefix_declaration_accepted (bytes := bytes) (position := after) (base := state.base)
        (limit := limits.max_term_bytes) declFound
    subst nextValue
    obtain ⟨finish, periodRun, finishValue, periodLower, periodUpper⟩ :=
      period_accepted (bytes := bytes) (position := next) periodFound
    obtain ⟨prefixes, pushRun, pushValue⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec state.prefixes p pushRoom)
    refine ⟨finish, { state with prefixes := prefixes }, ?_, finishValue, ?_, by simp, by omega, by omega,
      by simp [pushValue]⟩
    · rw [turtle.statement]
      simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun, periodRun, turtle.declare, pushRun]
    · simp [envOf, pushValue, declarations_push, ← declValue]
  | atBaseFails _ _ => cases result
  | atBasePeriodFails _ _ _ => cases result
  | @atBase b n m' opening declFound periodFound =>
    cases result
    obtain ⟨s, startRun, agree⟩ := opening_accepted opening
    obtain ⟨after, rfl, afterValue⟩ := start_ok_at_base agree
    rw [← afterValue] at declFound
    obtain ⟨v, next, declRun, declValue, nextValue, declLower, declUpper⟩ :=
      base_declaration_accepted (bytes := bytes) (position := after) (base := state.base)
        (limit := limits.max_term_bytes) declFound
    subst nextValue
    obtain ⟨finish, periodRun, finishValue, periodLower, periodUpper⟩ :=
      period_accepted (bytes := bytes) (position := next) periodFound
    refine ⟨finish, { state with base := v }, ?_, finishValue, ?_, by simp, by omega, by omega, by simp⟩
    · rw [turtle.statement]
      simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun, periodRun]
    · simp [envOf, declValue]
  | sparqlPrefixFails _ _ => cases result
  | @sparqlPrefix decl n opening declFound =>
    cases result
    obtain ⟨s, startRun, agree⟩ := opening_accepted opening
    obtain ⟨after, rfl, afterValue⟩ := start_ok_prefix agree
    rw [← afterValue] at declFound
    obtain ⟨p, next, declRun, declValue, nextValue, declLower, declUpper⟩ :=
      prefix_declaration_accepted (bytes := bytes) (position := after) (base := state.base)
        (limit := limits.max_term_bytes) declFound
    obtain ⟨prefixes, pushRun, pushValue⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec state.prefixes p pushRoom)
    refine ⟨next, { state with prefixes := prefixes }, ?_, nextValue, ?_, by simp, by omega, by omega,
      by simp [pushValue]⟩
    · rw [turtle.statement]
      simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun, turtle.declare, pushRun]
    · simp [envOf, pushValue, declarations_push, ← declValue]
  | sparqlBaseFails _ _ => cases result
  | @sparqlBase b n opening declFound =>
    cases result
    obtain ⟨s, startRun, agree⟩ := opening_accepted opening
    obtain ⟨after, rfl, afterValue⟩ := start_ok_base agree
    rw [← afterValue] at declFound
    obtain ⟨v, next, declRun, declValue, nextValue, declLower, declUpper⟩ :=
      base_declaration_accepted (bytes := bytes) (position := after) (base := state.base)
        (limit := limits.max_term_bytes) declFound
    refine ⟨next, { state with base := v }, ?_, nextValue, ?_, by simp, by omega, by omega, by simp⟩
    · rw [turtle.statement]
      simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, declRun]
    · simp [envOf, declValue]
  | triplesFails _ _ => cases result
  | triplesPeriodFails _ _ _ => cases result
  | @triples n ts' m' opening triplesFound periodFound =>
    cases result
    obtain ⟨s, startRun, agree⟩ := opening_accepted opening
    obtain rfl := start_ok_triples agree
    obtain ⟨after, out, triplesRun, afterValue, contents, triplesLower, triplesUpper⟩ :=
      triples_accepted ⟨bytes, scope, state.base, state.prefixes, limits⟩ start state.triples triplesFound
    subst afterValue
    obtain ⟨finish, periodRun, finishValue, periodLower, periodUpper⟩ :=
      period_accepted (bytes := bytes) (position := after) periodFound
    refine ⟨finish, { state with triples := out }, ?_, finishValue, by simp [envOf], contents, by omega,
      by omega, by simp⟩
    rw [turtle.statement]
    simp [startRun, core.result.Result.Insts.CoreOpsTry.branch, triplesRun, periodRun]

theorem statements_total_correct (bytes scope : alloc.vec.Vec U8) (limits : turtle.Limits) (position : Usize)
    (state : turtle.State) (room : state.prefixes.val.length ≤ position.val) :
    ∃ r o, turtle.statements bytes scope limits position state = .ok r ∧
      StatementsAt (docOf bytes scope limits) (envOf state) position.val state.triples.val.length o ∧
      TriplesAgrees state.triples.val r o := by
  obtain ⟨spaced, spaceRun, spaceCorrect⟩ := space_total_correct bytes position
  rcases spaced with start | e
  · have runs : TriviaRuns bytes.val true position.val start.val := spaceCorrect
    have bound := trivia_bound runs
    by_cases more : start.val < bytes.val.length
    · obtain ⟨r, o, stmtRun, stmtCorrect, agree⟩ :=
        statement_total_correct bytes scope limits start state more (by omega)
      rcases r with ⟨finish, state'⟩ | e
      · obtain ⟨ts, rfl, contents⟩ := statement_ok agree
        obtain ⟨next', s', run', _, _, _, lower, upper, prefixRoom⟩ :=
          statement_accepted bytes scope limits start state more (by omega) stmtCorrect
        rw [stmtRun] at run'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj (Result.ok_injective run'))
        have length1 := map_length contents
        obtain ⟨r, o, restRun, restCorrect, agree⟩ :=
          statements_total_correct bytes scope limits finish state' (by omega)
        rw [length1] at restCorrect
        rcases r with v | e
        · obtain ⟨us, rfl, contents2⟩ := triples_ok agree
          refine ⟨.Ok v, _, ?_, .more runs more stmtCorrect restCorrect, ?_⟩
          · rw [turtle.statements]
            simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, alloc.vec.Vec.len_val, more, stmtRun,
              restRun]
          · show v.val.map spo = state.triples.val.map spo ++ (ts ++ us)
            rw [contents2, contents, List.append_assoc]
        · obtain rfl := triples_err agree
          refine ⟨.Err e, _, ?_, .restFails runs more stmtCorrect restCorrect, rfl⟩
          rw [turtle.statements]
          simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, alloc.vec.Vec.len_val, more, stmtRun, restRun]
      · obtain rfl := statement_err agree
        refine ⟨.Err e, _, ?_, .statementFails runs more stmtCorrect, rfl⟩
        rw [turtle.statements]
        simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, alloc.vec.Vec.len_val, more, stmtRun]
    · have atEnd : start.val = bytes.val.length := by omega
      refine ⟨.Ok state.triples, .ok [], ?_,
        .finish (show TriviaRuns bytes.val true position.val bytes.val.length by rw [← atEnd]; exact runs),
        by simp [TriplesAgrees]⟩
      rw [turtle.statements]
      simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, alloc.vec.Vec.len_val, more]
  · refine ⟨.Err e, _, ?_, .spaceFails spaceCorrect, rfl⟩
    rw [turtle.statements]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch]
termination_by bytes.val.length - position.val
decreasing_by omega

theorem statements_accepted (bytes scope : alloc.vec.Vec U8) (limits : turtle.Limits) (position : Usize)
    (state : turtle.State) (room : state.prefixes.val.length ≤ position.val) {ts : List Spo}
    (found : StatementsAt (docOf bytes scope limits) (envOf state) position.val state.triples.val.length (.ok ts)) :
    ∃ v, turtle.statements bytes scope limits position state = .ok (.Ok v) ∧
      v.val.map spo = state.triples.val.map spo ++ ts := by
  generalize result : (Except.ok ts : Except Fault (List Spo)) = given at found
  cases found with
  | spaceFails _ => cases result
  | finish spaced =>
    cases result
    have spaced : TriviaRuns bytes.val true position.val bytes.val.length := spaced
    obtain ⟨stop, spaceRun, stopValue⟩ := space_runs spaced
    refine ⟨state.triples, ?_, by simp⟩
    rw [turtle.statements]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, alloc.vec.Vec.len_val, stopValue]
  | statementFails _ _ _ => cases result
  | restFails _ _ _ _ => cases result
  | @more _ _ _ p m e' ts' us spaced more stmtFound restFound =>
    cases result
    have spaced : TriviaRuns bytes.val true position.val p := spaced
    have more : p < bytes.val.length := more
    have bound := trivia_bound spaced
    obtain ⟨start, spaceRun, startValue⟩ := space_runs spaced
    subst startValue
    obtain ⟨finish, state', stmtRun, finishValue, envValue, contents, lower, upper, prefixRoom⟩ :=
      statement_accepted bytes scope limits start state more (by omega) stmtFound
    have length1 := map_length contents
    subst finishValue
    subst envValue
    rw [← length1] at restFound
    obtain ⟨v, restRun, contents2⟩ := statements_accepted bytes scope limits finish state' (by omega) restFound
    refine ⟨v, ?_, by rw [contents2, contents, List.append_assoc]⟩
    rw [turtle.statements]
    simp [spaceRun, core.result.Result.Insts.CoreOpsTry.branch, alloc.vec.Vec.len_val, more, stmtRun, restRun]
termination_by bytes.val.length - position.val
decreasing_by omega

/-! ## The reader -/

theorem vec_eq {v w : alloc.vec.Vec U8} (h : v.val = w.val) : v = w := (alloc.vec.Vec.eq_iff v w).mpr h

theorem iri_eq {a b : rdf.RdfIri} (h : a.spelling.val = b.spelling.val) : a = b := by
  cases a
  cases b
  simp only at h
  rw [vec_eq h]

theorem subject_term_injective {a b : rdf.Subject} (h : subjectTerm a = subjectTerm b) : a = b := by
  cases a with
  | Iri v =>
    cases b with
    | Iri w =>
      simp only [subjectTerm, Term.iri.injEq] at h
      rw [iri_eq h]
    | Blank _ => simp [subjectTerm] at h
  | Blank x =>
    cases b with
    | Iri _ => simp [subjectTerm] at h
    | Blank y =>
      simp only [subjectTerm, Term.blank.injEq] at h
      cases x
      cases y
      simp only at h
      rw [vec_eq h.1, vec_eq h.2]

theorem literal_term_injective {a b : rdf.RdfLiteral} (h : literalTerm a = literalTerm b) : a = b := by
  rcases a with ⟨la, ka⟩
  rcases b with ⟨lb, kb⟩
  cases ka with
  | Datatype da =>
    cases kb with
    | Datatype db =>
      simp only [literalTerm, Term.literal.injEq, Kind.datatype.injEq] at h
      rw [vec_eq h.1, iri_eq h.2]
    | Language tb => simp [literalTerm] at h
  | Language ta =>
    cases kb with
    | Datatype db => simp [literalTerm] at h
    | Language tb =>
      simp only [literalTerm, Term.literal.injEq, Kind.language.injEq] at h
      rw [vec_eq h.1, vec_eq h.2]

theorem object_term_injective {a b : rdf.Object} (h : objectTerm a = objectTerm b) : a = b := by
  cases a with
  | Iri v =>
    cases b with
    | Iri w =>
      simp only [objectTerm, Term.iri.injEq] at h
      rw [iri_eq h]
    | Blank _ => simp [objectTerm] at h
    | Literal l => cases l with | mk lexical kind => cases kind <;> simp [objectTerm, literalTerm] at h
  | Blank x =>
    cases b with
    | Iri _ => simp [objectTerm] at h
    | Blank y =>
      simp only [objectTerm, Term.blank.injEq] at h
      cases x
      cases y
      simp only at h
      rw [vec_eq h.1, vec_eq h.2]
    | Literal l => cases l with | mk lexical kind => cases kind <;> simp [objectTerm, literalTerm] at h
  | Literal l =>
    cases b with
    | Iri _ => cases l with | mk lexical kind => cases kind <;> simp [objectTerm, literalTerm] at h
    | Blank _ => cases l with | mk lexical kind => cases kind <;> simp [objectTerm, literalTerm] at h
    | Literal l' =>
      simp only [objectTerm] at h
      rw [literal_term_injective h]

/-- Triples are determined by their terms. -/
theorem spo_injective {a b : rdf.Triple} (h : spo a = spo b) : a = b := by
  rcases a with ⟨sa, pa, oa⟩
  rcases b with ⟨sb, pb, ob⟩
  simp only [spo, Spo.mk.injEq] at h
  rw [subject_term_injective h.1, iri_eq h.2.1, object_term_injective h.2.2]

theorem graph_equal {first second : rdf.RawGraph} (same : first.triples.val.map spo = second.triples.val.map spo) :
    first = second := by
  have lists : first.triples.val = second.triples.val := (List.map_injective_iff.mpr fun _ _ => spo_injective) same
  cases first with
  | mk a =>
    cases second with
    | mk b =>
      congr 1
      exact (alloc.vec.Vec.eq_iff a b).mpr lists

/-- What `turtle::read_with_limits` returns: a graph whose triples the bytes
    denote, or the first error of the bytes. -/
def ReadCorrect (bs scope base : List U8) (termLimit tripleLimit : Nat) : turtle.ReadResult → Prop
  | .Graph g => Document bs scope base termLimit tripleLimit (g.triples.val.map spo)
  | .Error e => DocumentError bs scope base termLimit tripleLimit (faultOf e)

/-- The reader starts with the base and no prefixes or triples. -/
def initial (base : alloc.vec.Vec U8) : turtle.State :=
  ⟨base, alloc.vec.Vec.new turtle.Prefix, alloc.vec.Vec.new rdf.Triple⟩

theorem initial_document {bytes scope base : alloc.vec.Vec U8} {limits : turtle.Limits}
    {o : Except Fault (List Spo)} :
    StatementsAt (docOf bytes scope limits) (envOf (initial base)) (0#usize : Usize).val
      (initial base).triples.val.length o ↔
    StatementsAt ⟨bytes.val, scope.val, limits.max_term_bytes.val, limits.max_triples.val⟩ ⟨base.val, []⟩ 0 0 o := by
  have zero : (0#usize : Usize).val = 0 := by simp
  have none : (initial base).triples.val.length = 0 := by simp [initial]
  have env : envOf (initial base) = ⟨base.val, []⟩ := by simp [envOf, initial, declarations]
  rw [zero, none, env]
  rfl

/-- `turtle::read_with_limits` always returns: a graph whose triples are, in
    order, exactly the ones the bytes denote as a Turtle document read against
    `base` within the limits, or the first error of the bytes. -/
theorem read_with_limits_total_correct (bytes scope base : alloc.vec.Vec U8) (limits : turtle.Limits) :
    ∃ r, turtle.read_with_limits bytes scope base limits = .ok r ∧
      ReadCorrect bytes.val scope.val base.val limits.max_term_bytes.val limits.max_triples.val r := by
  obtain ⟨r, o, run, correct, agree⟩ := statements_total_correct bytes scope limits 0#usize (initial base)
    (by simp [initial])
  have correct := initial_document.mp correct
  rcases r with v | e
  · obtain ⟨ts, rfl, contents⟩ := triples_ok agree
    refine ⟨.Graph ⟨v⟩, ?_, ?_⟩
    · simp only [initial] at run
      simp [turtle.read_with_limits, copy_bytes_spec, run]
    · have same : v.val.map spo = ts := by simpa [initial] using contents
      show StatementsAt _ _ 0 0 (.ok (v.val.map spo))
      rw [same]
      exact correct
  · obtain rfl := triples_err agree
    refine ⟨.Error e, ?_, correct⟩
    simp only [initial] at run
    simp [turtle.read_with_limits, copy_bytes_spec, run]

/-- `turtle::read_with_limits` returns a graph exactly when the bytes are a
    Turtle document within the limits that denotes the graph's triples in order. -/
theorem read_with_limits_accepted_iff (bytes scope base : alloc.vec.Vec U8) (limits : turtle.Limits)
    (graph : rdf.RawGraph) :
    turtle.read_with_limits bytes scope base limits = .ok (.Graph graph) ↔
      Document bytes.val scope.val base.val limits.max_term_bytes.val limits.max_triples.val
        (graph.triples.val.map spo) := by
  constructor
  · intro accepted
    obtain ⟨r, run, correct⟩ := read_with_limits_total_correct bytes scope base limits
    rw [accepted] at run
    obtain rfl := Result.ok_injective run
    exact correct
  · intro document
    obtain ⟨v, run, contents⟩ := statements_accepted bytes scope limits 0#usize (initial base) (by simp [initial])
      (initial_document.mpr document)
    have same : (⟨v⟩ : rdf.RawGraph) = graph := graph_equal (by simpa [initial] using contents)
    subst same
    simp only [initial] at run
    simp [turtle.read_with_limits, copy_bytes_spec, run]

theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by simp [core.num.Usize.MAX]

/-- `turtle::read` with no limits beyond the machine's: a graph exactly for the
    Turtle documents, with their triples in order, and otherwise the first
    error. -/
theorem read_total_correct (bytes scope base : alloc.vec.Vec U8) :
    ∃ r, turtle.read bytes scope base = .ok r ∧ ReadCorrect bytes.val scope.val base.val Usize.max Usize.max r := by
  obtain ⟨r, run, correct⟩ := read_with_limits_total_correct bytes scope base
    ⟨core.num.Usize.MAX, core.num.Usize.MAX⟩
  simp only [usize_max_val] at correct
  exact ⟨r, by simp [turtle.read, run], correct⟩

/-- `turtle::read` returns a graph exactly when the bytes are a Turtle document
    that denotes the graph's triples in order. -/
theorem read_accepted_iff (bytes scope base : alloc.vec.Vec U8) (graph : rdf.RawGraph) :
    turtle.read bytes scope base = .ok (.Graph graph) ↔
      Document bytes.val scope.val base.val Usize.max Usize.max (graph.triples.val.map spo) := by
  have iff := read_with_limits_accepted_iff bytes scope base ⟨core.num.Usize.MAX, core.num.Usize.MAX⟩ graph
  simp only [usize_max_val] at iff
  exact iff

end Rowl.Turtle
