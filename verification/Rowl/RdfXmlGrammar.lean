import Rowl.XmlGrammar
import Rowl.NTriples
import Rowl.IriResolution
import Rowl.References
import Rowl.Encoding

/-!
# The RDF/XML grammar

RDF 1.1 XML Syntax (W3C Recommendation, 25 February 2014), sections 5, 6 and 7,
as relations over the element trees of `XmlGrammar`, written independently of
the Rust reader.

An element becomes an element event (§6.1.2): its URI is its namespace name
followed by its local name; `xml:base` sets its base IRI by RFC 3986 section 5.2
resolution against the base IRI of its parent (`Scoped`), `xml:lang` its
language; the reserved XML names are removed from its attributes, and the
others become attribute events whose URI is the namespace name followed by the
local name, or, for the names `ID`, `about`, `resource`, `parseType` and `type`
without namespace, the RDF namespace name followed by the name (`Events`, §6.1.4).
No two attribute events of an element may have the same URI.

The productions of section 7 are relations over element events with the triples
they add, in an order fixed here: a node element's `rdf:type` triple, its
property attributes in document order and its property elements in order; a
property element's object first, then its statement and the reification of it,
then the content of `rdf:parseType="Resource"`; a collection member's triples,
those of the later members, and its `rdf:first` and `rdf:rest` triples. The
state threads the number of generated blank nodes, of which the `n`-th has the
label `0xFF` followed by the decimal digits of `n`, and the `rdf:ID` values
with their base IRIs, which must be new (constraint-id, §5.4).

IRIs are compared and resolved as the UTF-8 bytes of their characters
(`utf8Bytes`); every IRI of a triple is an RFC 3987 IRI and every resolved
attribute value an RFC 3987 IRI reference. Literals without language have the
datatype xsd:string. `rdf:datatype` names its datatype as written. An empty
property element with `rdf:datatype` and no other attribute than `rdf:ID` has
the empty literal of that datatype: RDF 1.1 added `rdf:datatype` to the
attributes of empty property elements under the erratum "allow datatyped empty
literals" without changing the action of the production, which would give a
blank node. `rdf:parseType="Literal"`, and the other values that read as
Literal, have no relation here: the XML literal needs XML canonicalization,
which is not specified. Terms are at most `termLimit` bytes long, names at most
`termLimit` code points, and `rdf:li` counters below `itemLimit`; `Graph` also
bounds the triples, generated blank nodes and `rdf:ID` values by `itemLimit`.
-/

namespace Rowl.RdfXmlGrammar
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
attribute [local instance] Classical.propDecidable

/-! ## Terms and statements -/

/-- The kind of a literal: its datatype IRI, or its language tag. -/
inductive Kind where
  | datatype (iri : List U8)
  | language (tag : List U8)

/-- RDF terms by their bytes. -/
inductive Term where
  | iri (spelling : List U8)
  | blank (scope label : List U8)
  | literal (lexical : List U8) (kind : Kind)

/-- A triple by its terms. -/
structure Statement where
  subject : Term
  predicate : List U8
  object : Term

/-- The term of a literal of the raw graph. -/
def literalTerm (l : rdf.RdfLiteral) : Term :=
  match l.kind with
  | .Datatype d => .literal l.lexical.val (.datatype d.spelling.val)
  | .Language t => .literal l.lexical.val (.language t.val)

/-- The term of a subject of the raw graph. -/
def subjectTerm : rdf.Subject → Term
  | .Iri v => .iri v.spelling.val
  | .Blank b => .blank b.scope.val b.label.val

/-- The term of an object of the raw graph. -/
def objectTerm : rdf.Object → Term
  | .Iri v => .iri v.spelling.val
  | .Blank b => .blank b.scope.val b.label.val
  | .Literal l => literalTerm l

/-- The statement of a triple of the raw graph. -/
def statementOf (t : rdf.Triple) : Statement :=
  ⟨subjectTerm t.subject, t.predicate.spelling.val, objectTerm t.object⟩

/-! ## Spellings -/

/-- The byte with value `n`. -/
def byte (n : Nat) : U8 := ⟨BitVec.ofNat 8 n⟩

/-- The UTF-8 bytes of a word of code points. -/
def utf8Bytes (w : Word) : List U8 := (w.flatMap Rowl.IriResolution.utf8).map byte

/-- A word of Unicode scalar values whose UTF-8 bytes `b` are at most `limit`. -/
def Spelled (limit : Nat) (w : Word) (b : List U8) : Prop :=
  (∀ c ∈ w, Rowl.Encoding.Scalar c) ∧ b = utf8Bytes w ∧ b.length ≤ limit

/-- The bytes are the UTF-8 spelling of an RFC 3987 IRI reference. -/
def IriReference (b : List U8) : Prop :=
  ∃ w, Rowl.Regular.Utf8From b 0 w ∧ w ∈ Rowl.Iri.ReferenceLanguage

/-- The decimal digits of `n`, as code points. -/
def digits (n : Nat) : Word :=
  (if n < 10 then [] else digits (n / 10)) ++ [48 + n % 10]
termination_by n
decreasing_by omega

/-! ## The RDF vocabulary (§5.1) and the URIs of events -/

/-- The RDF namespace name. -/
def rdfNs : Word := lit "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

/-- `rdf:name`. -/
def rdfName (s : String) : Word := rdfNs ++ lit s

/-- The bytes of the IRI `rdf:name`. -/
def rdfBytes (s : String) : List U8 := utf8Bytes (rdfName s)

/-- The bytes of xsd:string. -/
def xsdString : List U8 := utf8Bytes (lit "http://www.w3.org/2001/XMLSchema#string")

/-- §7.2.2 coreSyntaxTerms. -/
def coreSyntaxTerms : List Word :=
  ["RDF", "ID", "about", "parseType", "resource", "nodeID", "datatype"].map rdfName

/-- §7.2.4 oldTerms. -/
def oldTerms : List Word := ["aboutEach", "aboutEachPrefix", "bagID"].map rdfName

/-- §7.2.5 nodeElementURIs. -/
def NodeElementUri (u : Word) : Prop := u ∉ coreSyntaxTerms ∧ u ≠ rdfName "li" ∧ u ∉ oldTerms

/-- §7.2.6 propertyElementURIs. -/
def PropertyElementUri (u : Word) : Prop :=
  u ∉ coreSyntaxTerms ∧ u ≠ rdfName "Description" ∧ u ∉ oldTerms

/-- §7.2.7 propertyAttributeURIs. -/
def PropertyAttributeUri (u : Word) : Prop :=
  u ∉ coreSyntaxTerms ∧ u ≠ rdfName "Description" ∧ u ≠ rdfName "li" ∧ u ∉ oldTerms

/-- §5.1: no namespace name may extend the RDF namespace name. -/
def NamespaceAllowed (ns : Word) : Prop := ¬ (rdfNs <+: ns ∧ ns ≠ rdfNs)

/-- `rdf:_n` (§7.4). -/
def memberUri (n : Nat) : Word := rdfName "_" ++ digits n

/-! ## Contexts and states -/

/-- What an element is read in: the base IRI and language of its parent's
    element event, the caller's blank node scope and the limits. -/
structure Ctx where
  base : List U8
  lang : Word
  scope : List U8
  termLimit : Nat
  itemLimit : Nat

/-- The number of generated blank nodes, and the rdf:ID values with the base
    IRIs they were given against, in document order. -/
structure St where
  blanks : Nat
  ids : List (Word × List U8)

/-- The next generated blank node (§6.3.3 generated-blank-node-id): its label
    is 0xFF followed by the decimal digits of the number of earlier ones, and
    no UTF-8 label of rdf:nodeID contains the byte 0xFF. -/
def fresh (c : Ctx) (st : St) : Term × St :=
  (.blank c.scope (byte 255 :: (digits st.blanks).map byte), ⟨st.blanks + 1, st.ids⟩)

/-! ## Element events (§6.1.2) -/

/-- A word that begins with `xml` in any case. -/
def XmlLetters (w : Word) : Prop :=
  ∃ a b d rest, w = a :: b :: d :: rest ∧ (a = 120 ∨ a = 88) ∧ (b = 109 ∨ b = 77) ∧ (d = 108 ∨ d = 76)

/-- A reserved XML name: a prefix, or a local name without prefix, that
    begins with `xml` in any case. -/
def Reserved (a : xml.Attribute) : Prop :=
  match a.ns_prefix with
  | some p => XmlLetters (word p)
  | none => XmlLetters (word a.local_name)

/-- The names without namespace that are read in the RDF namespace. -/
def unqualifiedNames : List Word := ["ID", "about", "resource", "parseType", "type"].map lit

/-- The URI of an attribute event (§6.1.4). -/
inductive AttrUri (limit : Nat) (a : xml.Attribute) : Word → Prop
  | qualified {ns : alloc.vec.Vec U32} : a.ns_name = some ns → NamespaceAllowed (word ns) →
      (word ns ++ word a.local_name).length ≤ limit → AttrUri limit a (word ns ++ word a.local_name)
  | unqualified : a.ns_name = none → word a.local_name ∈ unqualifiedNames →
      (rdfNs ++ word a.local_name).length ≤ limit → AttrUri limit a (rdfNs ++ word a.local_name)

/-- The attribute events of an element: the URI and string value of each
    attribute that is no reserved XML name, in document order. -/
inductive Events (limit : Nat) : List xml.Attribute → List (Word × Word) → Prop
  | nil : Events limit [] []
  | reserved {a rest evs} : Reserved a → Events limit rest evs → Events limit (a :: rest) evs
  | event {a rest u evs} : ¬ Reserved a → AttrUri limit a u → Events limit rest evs →
      Events limit (a :: rest) ((u, word a.value) :: evs)

/-- The URI of an element event. -/
inductive ElementUri (limit : Nat) (e : xml.Element) : Word → Prop
  | mk {ns : alloc.vec.Vec U32} : e.ns_name = some ns → NamespaceAllowed (word ns) →
      (word ns ++ word e.local_name).length ≤ limit → ElementUri limit e (word ns ++ word e.local_name)

/-- The value of the attribute in the XML namespace with local name `l`. -/
def xmlValue (l : Word) : List xml.Attribute → Option Word
  | [] => none
  | a :: rest =>
    if optWord a.ns_name = some xmlNamespace ∧ word a.local_name = l then some (word a.value)
    else xmlValue l rest

/-- The reference `v` resolved against the base IRI of `c` (RFC 3986 section
    5.2), within the term limit. -/
def ResolvedRef (c : Ctx) (v : Word) (i : List U8) : Prop :=
  ∃ r, Spelled c.termLimit v r ∧ IriReference r ∧
    Rowl.IriResolution.resolve (Rowl.References.Word c.base) (Rowl.References.Word r) =
      some (Rowl.References.Word i) ∧ i.length ≤ c.termLimit

/-- The base IRI of an element: its `xml:base` resolved against the base IRI
    of its parent (XML Base), or that base IRI. -/
inductive BaseOf (c : Ctx) : Option Word → List U8 → Prop
  | inherited : BaseOf c none c.base
  | given {v b} : ResolvedRef c v b → BaseOf c (some v) b

/-- The context of an element's own event: its base IRI and its language. -/
inductive Scoped (c : Ctx) (e : xml.Element) : Ctx → Prop
  | mk {b} : BaseOf c (xmlValue (lit "base") e.attributes.val) b →
      Scoped c e { c with base := b, lang := (xmlValue (lit "lang") e.attributes.val).getD c.lang }

/-- The event of an element in context `c`: its context and its attribute
    events, whose URIs are distinct. -/
def Prepared (c : Ctx) (e : xml.Element) (c' : Ctx) (evs : List (Word × Word)) : Prop :=
  Scoped c e c' ∧ Events c.termLimit e.attributes.val evs ∧ (evs.map Prod.fst).Nodup

/-- The string value of the event with URI `u`. -/
def attrValue (u : Word) : List (Word × Word) → Option Word
  | [] => none
  | ev :: evs => if ev.1 = u then some ev.2 else attrValue u evs

/-- An event with URI `u` occurs. -/
def Has (evs : List (Word × Word)) (u : Word) : Prop := ∃ v, (u, v) ∈ evs

/-- Every event has one of the URIs `us`. -/
def Only (evs : List (Word × Word)) (us : List Word) : Prop := ∀ ev ∈ evs, ev.1 ∈ us

/-! ## Terms of events -/

/-- The IRI spelled by `u`: an RFC 3987 IRI within the term limit. -/
def IriOf (c : Ctx) (u : Word) (i : List U8) : Prop := Spelled c.termLimit u i ∧ Rowl.NTriples.AbsoluteIri i

/-- `resolve(e, v)` of §6.3.3 and §5.3: an RFC 3987 IRI. -/
def Resolved (c : Ctx) (v : Word) (i : List U8) : Prop := ResolvedRef c v i ∧ Rowl.NTriples.AbsoluteIri i

/-- A literal with the language of `c`: of datatype xsd:string without one. -/
inductive LiteralOf (c : Ctx) (v : Word) : Term → Prop
  | plain {b} : c.lang = [] → Spelled c.termLimit v b → LiteralOf c v (.literal b (.datatype xsdString))
  | tagged {b t} : c.lang ≠ [] → Spelled c.termLimit v b → Spelled c.termLimit c.lang t →
      Rowl.NTriples.LanguageTag t → LiteralOf c v (.literal b (.language t))

/-- A literal of the datatype `d`, which may not be rdf:langString. -/
inductive TypedOf (c : Ctx) (v d : Word) : Term → Prop
  | mk {b i} : Spelled c.termLimit v b → IriOf c d i → i ≠ rdfBytes "langString" →
      TypedOf c v d (.literal b (.datatype i))

/-- rdf:ID (§7.2.22, §5.4 constraint-id): an NCName; its IRI is `#` and the
    value resolved against the base IRI, and the pair of value and base IRI must
    be new. -/
inductive IdIri (c : Ctx) (v : Word) (st : St) : List U8 → St → Prop
  | mk {i} : NCName v → Resolved c (35 :: v) i → (v, c.base) ∉ st.ids →
      IdIri c v st i ⟨st.blanks, st.ids ++ [(v, c.base)]⟩

/-- rdf:nodeID (§7.2.23): the blank node labelled by the UTF-8 spelling of an
    NCName, in the caller's scope. -/
inductive NodeIdOf (c : Ctx) (v : Word) : Term → Prop
  | mk {b} : NCName v → Spelled c.termLimit v b → NodeIdOf c v (.blank c.scope b)

/-! ## Node elements (§7.2.11) -/

/-- §7.2.11: the attributes of a node element are at most one of rdf:ID,
    rdf:nodeID and rdf:about, and property attributes. -/
def NodeAttributes (evs : List (Word × Word)) : Prop :=
  (∀ ev ∈ evs, ev.1 = rdfName "ID" ∨ ev.1 = rdfName "nodeID" ∨ ev.1 = rdfName "about" ∨
    PropertyAttributeUri ev.1) ∧
  ¬ (Has evs (rdfName "ID") ∧ Has evs (rdfName "nodeID")) ∧
  ¬ (Has evs (rdfName "ID") ∧ Has evs (rdfName "about")) ∧
  ¬ (Has evs (rdfName "nodeID") ∧ Has evs (rdfName "about"))

/-- The subject of a node element. -/
inductive SubjectOf (c : Ctx) (evs : List (Word × Word)) (st : St) : Term → St → Prop
  | id {v i st'} : attrValue (rdfName "ID") evs = some v → IdIri c v st i st' → SubjectOf c evs st (.iri i) st'
  | nodeId {v t} : attrValue (rdfName "ID") evs = none → attrValue (rdfName "nodeID") evs = some v →
      NodeIdOf c v t → SubjectOf c evs st t st
  | about {v i} : attrValue (rdfName "ID") evs = none → attrValue (rdfName "nodeID") evs = none →
      attrValue (rdfName "about") evs = some v → Resolved c v i → SubjectOf c evs st (.iri i) st
  | fresh : attrValue (rdfName "ID") evs = none → attrValue (rdfName "nodeID") evs = none →
      attrValue (rdfName "about") evs = none → SubjectOf c evs st (fresh c st).1 (fresh c st).2

/-- The rdf:type triple of a node element other than rdf:Description. -/
inductive TypeTriple (c : Ctx) (s : Term) (u : Word) : List Statement → Prop
  | description : u = rdfName "Description" → TypeTriple c s u []
  | typed {i} : u ≠ rdfName "Description" → IriOf c u i → TypeTriple c s u [⟨s, rdfBytes "type", .iri i⟩]

/-- The triples of the property attributes among the events, with subject
    `s`: rdf:type with the resolved IRI, any other with a literal. -/
inductive PropAttrs (c : Ctx) (s : Term) : List (Word × Word) → List Statement → Prop
  | nil : PropAttrs c s [] []
  | skip {u v evs ts} : ¬ PropertyAttributeUri u → PropAttrs c s evs ts → PropAttrs c s ((u, v) :: evs) ts
  | type {v evs i ts} : Resolved c v i → PropAttrs c s evs ts →
      PropAttrs c s ((rdfName "type", v) :: evs) (⟨s, rdfBytes "type", .iri i⟩ :: ts)
  | literal {u v evs p o ts} : PropertyAttributeUri u → u ≠ rdfName "type" → IriOf c u p → LiteralOf c v o →
      PropAttrs c s evs ts → PropAttrs c s ((u, v) :: evs) (⟨s, p, o⟩ :: ts)

/-! ## Property elements (§7.2.13 to §7.2.21) -/

/-- The reification of the statement `t` by `r` (§7.3). -/
def reification (r : List U8) (t : Statement) : List Statement :=
  [⟨.iri r, rdfBytes "subject", t.subject⟩, ⟨.iri r, rdfBytes "predicate", .iri t.predicate⟩,
   ⟨.iri r, rdfBytes "object", t.object⟩, ⟨.iri r, rdfBytes "type", .iri (rdfBytes "Statement")⟩]

/-- The statement `t` of a property element, reified when the element has
    rdf:ID. -/
inductive Stated (c : Ctx) (evs : List (Word × Word)) (t : Statement) (st : St) : List Statement → St → Prop
  | plain : attrValue (rdfName "ID") evs = none → Stated c evs t st [t] st
  | reified {v i st'} : attrValue (rdfName "ID") evs = some v → IdIri c v st i st' →
      Stated c evs t st (t :: reification i t) st'

/-- The predicate of a property element and the rdf:li counter after it
    (§7.2.14, §7.4). -/
inductive Predicate (c : Ctx) (e : xml.Element) (li : Nat) : List U8 → Nat → Prop
  | member {p} : ElementUri c.termLimit e (rdfName "li") → li < c.itemLimit → IriOf c (memberUri li) p →
      Predicate c e li p (li + 1)
  | named {u p} : ElementUri c.termLimit e u → u ≠ rdfName "li" → PropertyElementUri u → IriOf c u p →
      Predicate c e li p li

/-- White space (§7.2.12). -/
def Ws (t : Word) : Prop := ∀ x ∈ t, IsSpace x

/-- Children that are white space text only. -/
def AllWs (nodes : List xml.Node) : Prop := ∀ x ∈ nodes, ∃ t, x = .Text t ∧ Ws (word t)

/-- The attributes of an empty property element with an object resource:
    rdf:ID, at most one of rdf:resource and rdf:nodeID, and property
    attributes. -/
def EmptyAttributes (evs : List (Word × Word)) : Prop :=
  (∀ ev ∈ evs, ev.1 = rdfName "ID" ∨ ev.1 = rdfName "resource" ∨ ev.1 = rdfName "nodeID" ∨
    PropertyAttributeUri ev.1) ∧
  ¬ (Has evs (rdfName "resource") ∧ Has evs (rdfName "nodeID"))

/-- The object of an empty property element with an object resource. -/
inductive EmptyObject (c : Ctx) (evs : List (Word × Word)) (st : St) : Term → St → Prop
  | resource {v i} : attrValue (rdfName "resource") evs = some v → Resolved c v i → EmptyObject c evs st (.iri i) st
  | nodeId {v t} : attrValue (rdfName "resource") evs = none → attrValue (rdfName "nodeID") evs = some v →
      NodeIdOf c v t → EmptyObject c evs st t st
  | fresh : attrValue (rdfName "resource") evs = none → attrValue (rdfName "nodeID") evs = none →
      EmptyObject c evs st (fresh c st).1 (fresh c st).2

/-- The literal of a literal property element: typed by rdf:datatype, or in
    the element's language. -/
inductive TextObject (c : Ctx) (evs : List (Word × Word)) (v : Word) : Term → Prop
  | typed {d o} : attrValue (rdfName "datatype") evs = some d → TypedOf c v d o → TextObject c evs v o
  | plain {o} : attrValue (rdfName "datatype") evs = none → LiteralOf c v o → TextObject c evs v o

mutual
/-- §7.2.11 nodeElement, read in context `c` from state `st`: its subject,
    its triples and the state after them. -/
inductive NodeElement : Ctx → xml.Element → St → Term → List Statement → St → Prop
  | mk {c e c' evs u st s st1 ts1 ts2 ts3 st'} :
      Prepared c e c' evs → ElementUri c.termLimit e u → NodeElementUri u → NodeAttributes evs →
      SubjectOf c' evs st s st1 → TypeTriple c' s u ts1 → PropAttrs c' s evs ts2 →
      PropertyElts c' s e.children.val 1 st1 ts3 st' →
      NodeElement c e st s (ts1 ++ ts2 ++ ts3) st'

/-- §7.2.13 propertyEltList of the node with subject `s`, with the rdf:li
    counter. -/
inductive PropertyElts : Ctx → Term → List xml.Node → Nat → St → List Statement → St → Prop
  | nil {c s li st} : PropertyElts c s [] li st [] st
  | space {c s t rest li st ts st'} : Ws (word t) → PropertyElts c s rest li st ts st' →
      PropertyElts c s (.Text t :: rest) li st ts st'
  | elt {c s e rest li li' st st1 ts1 ts2 st'} : PropertyElt c s e li li' st ts1 st1 →
      PropertyElts c s rest li' st1 ts2 st' → PropertyElts c s (.Element e :: rest) li st (ts1 ++ ts2) st'

/-- §7.2.14 propertyElt of the node with subject `s`, with the rdf:li counter
    before and after it. -/
inductive PropertyElt : Ctx → Term → xml.Element → Nat → Nat → St → List Statement → St → Prop
  /-- §7.2.15 resourcePropertyElt. -/
  | resource {c s e li li' c' evs p pre n post st sn tsn st1 ts st'} :
      Prepared c e c' evs → Predicate c e li p li' → attrValue (rdfName "parseType") evs = none →
      Only evs [rdfName "ID"] → e.children.val = pre ++ [.Element n] ++ post → AllWs pre → AllWs post →
      NodeElement c' n st sn tsn st1 → Stated c' evs ⟨s, p, sn⟩ st1 ts st' →
      PropertyElt c s e li li' st (tsn ++ ts) st'
  /-- §7.2.16 literalPropertyElt. -/
  | literal {c s e li li' c' evs p t o st ts st'} :
      Prepared c e c' evs → Predicate c e li p li' → attrValue (rdfName "parseType") evs = none →
      Only evs [rdfName "ID", rdfName "datatype"] → e.children.val = [.Text t] →
      TextObject c' evs (word t) o → Stated c' evs ⟨s, p, o⟩ st ts st' →
      PropertyElt c s e li li' st ts st'
  /-- §7.2.18 parseTypeResourcePropertyElt. -/
  | parseResource {c s e li li' c' evs p st ts st2 tsc st'} :
      Prepared c e c' evs → Predicate c e li p li' → attrValue (rdfName "parseType") evs = some (lit "Resource") →
      Only evs [rdfName "ID", rdfName "parseType"] →
      Stated c' evs ⟨s, p, (fresh c' st).1⟩ (fresh c' st).2 ts st2 →
      PropertyElts c' (fresh c' st).1 e.children.val 1 st2 tsc st' →
      PropertyElt c s e li li' st (ts ++ tsc) st'
  /-- §7.2.19 parseTypeCollectionPropertyElt. -/
  | collection {c s e li li' c' evs p st h tsl st1 ts st'} :
      Prepared c e c' evs → Predicate c e li p li' → attrValue (rdfName "parseType") evs = some (lit "Collection") →
      Only evs [rdfName "ID", rdfName "parseType"] → NodeList c' e.children.val st h tsl st1 →
      Stated c' evs ⟨s, p, h⟩ st1 ts st' → PropertyElt c s e li li' st (tsl ++ ts) st'
  /-- §7.2.21 emptyPropertyElt without attributes other than rdf:ID. -/
  | emptyLiteral {c s e li li' c' evs p o st ts st'} :
      Prepared c e c' evs → Predicate c e li p li' → attrValue (rdfName "parseType") evs = none →
      e.children.val = [] → Only evs [rdfName "ID"] → LiteralOf c' [] o → Stated c' evs ⟨s, p, o⟩ st ts st' →
      PropertyElt c s e li li' st ts st'
  /-- §7.2.21 emptyPropertyElt with rdf:datatype: the empty typed literal. -/
  | emptyTyped {c s e li li' c' evs p d o st ts st'} :
      Prepared c e c' evs → Predicate c e li p li' → attrValue (rdfName "parseType") evs = none →
      e.children.val = [] → Only evs [rdfName "ID", rdfName "datatype"] → attrValue (rdfName "datatype") evs = some d →
      TypedOf c' [] d o → Stated c' evs ⟨s, p, o⟩ st ts st' → PropertyElt c s e li li' st ts st'
  /-- §7.2.21 emptyPropertyElt with an object resource. -/
  | emptyResource {c s e li li' c' evs p r st st1 tsa ts st'} :
      Prepared c e c' evs → Predicate c e li p li' → attrValue (rdfName "parseType") evs = none →
      e.children.val = [] → ¬ Only evs [rdfName "ID"] → attrValue (rdfName "datatype") evs = none →
      EmptyAttributes evs → EmptyObject c' evs st r st1 → PropAttrs c' r evs tsa →
      Stated c' evs ⟨s, p, r⟩ st1 ts st' → PropertyElt c s e li li' st (tsa ++ ts) st'

/-- The members of a collection (§7.2.19): the first list node or rdf:nil,
    the triples and the state after them. -/
inductive NodeList : Ctx → List xml.Node → St → Term → List Statement → St → Prop
  | nil {c st} : NodeList c [] st (.iri (rdfBytes "nil")) [] st
  | space {c t rest st h ts st'} : Ws (word t) → NodeList c rest st h ts st' → NodeList c (.Text t :: rest) st h ts st'
  | member {c f rest st sf tsf st2 h tsr st3} :
      NodeElement c f (fresh c st).2 sf tsf st2 → NodeList c rest st2 h tsr st3 →
      NodeList c (.Element f :: rest) st (fresh c st).1
        (tsf ++ tsr ++ [⟨(fresh c st).1, rdfBytes "first", sf⟩, ⟨(fresh c st).1, rdfBytes "rest", h⟩]) st3
end

/-- §7.2.10 nodeElementList. -/
inductive NodeElements (c : Ctx) : List xml.Node → St → List Statement → St → Prop
  | nil {st} : NodeElements c [] st [] st
  | space {t rest st ts st'} : Ws (word t) → NodeElements c rest st ts st' →
      NodeElements c (.Text t :: rest) st ts st'
  | node {n rest st sn tsn st1 ts st'} : NodeElement c n st sn tsn st1 → NodeElements c rest st1 ts st' →
      NodeElements c (.Element n :: rest) st (tsn ++ ts) st'

/-- §7.2.1, §7.2.8, §7.2.9: the root element rdf:RDF without attributes and
    with a nodeElementList, or a root node element. -/
inductive Doc (c : Ctx) (root : xml.Element) : List Statement → St → Prop
  | rdf {c' evs ts st'} : Prepared c root c' evs → evs = [] → ElementUri c.termLimit root (rdfName "RDF") →
      NodeElements c' root.children.val ⟨0, []⟩ ts st' → Doc c root ts st'
  | node {s ts st'} : NodeElement c root ⟨0, []⟩ s ts st' → Doc c root ts st'

/-- The RDF graph of an element tree read against the base IRI `base` with
    blank nodes in `scope`: its triples `ts` in order, within the limits. -/
def Graph (base scope : List U8) (termLimit itemLimit : Nat) (root : xml.Element) (ts : List Statement) : Prop :=
  base.length ≤ termLimit ∧
  ∃ st, Doc ⟨base, [], scope, termLimit, itemLimit⟩ root ts st ∧
    ts.length ≤ itemLimit ∧ st.blanks ≤ itemLimit ∧ st.ids.length ≤ itemLimit

end Rowl.RdfXmlGrammar
