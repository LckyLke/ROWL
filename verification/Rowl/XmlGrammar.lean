import Rowl.Unicode

/-!
# The grammar of XML documents read for RDF/XML

An independent statement of XML 1.0 (Fifth Edition) and Namespaces in XML 1.0
(Third Edition), for the documents `xml::read` supports, written over words of
code points. Every production is a relation between a word and what the
production yields: the element tree of the infoset as RDF/XML reads it, and the
cost of entity expansions. Nothing here refers to the Rust functions; only the
element tree is stated with the extracted Rust types, so that the theorems in
`Xml.lean` can say that `read` returns it.

The productions are numbered as in the XML Recommendation. Where the grammar
says `Char`, any code point is allowed here: every word below is part of a
document whose characters are all `Char`s (`Decoded`), or of a replacement
text built from such characters and from character references, which must be
`Char`s (WFC Legal Character).

The supported documents differ from all well-formed ones as follows: the
encoding declaration, when present, names UTF-8; the internal subset holds only
entity declarations, comments, processing instructions and white space; every
entity reference names a declared internal entity or a predefined one, whose
character it always denotes; and the expansions cost at most the budget.
-/

namespace Rowl.XmlGrammar
open Aeneas Aeneas.Std RowlRust
attribute [local instance] Classical.propDecidable

noncomputable section

/-- A word of code points. -/
abbrev Word := List Nat

/-- The code points of an ASCII string. -/
def lit (s : String) : Word := s.toList.map Char.toNat

/-- `pat` occurs in `w`. -/
def Contains (pat w : Word) : Prop := ∃ a b, w = a ++ pat ++ b

/-! ## Characters and names (§2.2, §2.3; Namespaces §3, §4) -/

/-- [3] the characters of S. -/
def IsSpace (c : Nat) : Prop := c = 32 ∨ c = 9 ∨ c = 13 ∨ c = 10

/-- [4] NameStartChar. -/
def NameStartChar (c : Nat) : Prop :=
  c = 58 ∨ (65 ≤ c ∧ c ≤ 90) ∨ c = 95 ∨ (97 ≤ c ∧ c ≤ 122) ∨ (0xC0 ≤ c ∧ c ≤ 0xD6) ∨
  (0xD8 ≤ c ∧ c ≤ 0xF6) ∨ (0xF8 ≤ c ∧ c ≤ 0x2FF) ∨ (0x370 ≤ c ∧ c ≤ 0x37D) ∨
  (0x37F ≤ c ∧ c ≤ 0x1FFF) ∨ (0x200C ≤ c ∧ c ≤ 0x200D) ∨ (0x2070 ≤ c ∧ c ≤ 0x218F) ∨
  (0x2C00 ≤ c ∧ c ≤ 0x2FEF) ∨ (0x3001 ≤ c ∧ c ≤ 0xD7FF) ∨ (0xF900 ≤ c ∧ c ≤ 0xFDCF) ∨
  (0xFDF0 ≤ c ∧ c ≤ 0xFFFD) ∨ (0x10000 ≤ c ∧ c ≤ 0xEFFFF)

/-- [4a] NameChar. -/
def NameChar (c : Nat) : Prop :=
  NameStartChar c ∨ c = 45 ∨ c = 46 ∨ (48 ≤ c ∧ c ≤ 57) ∨ c = 0xB7 ∨
  (0x300 ≤ c ∧ c ≤ 0x36F) ∨ (0x203F ≤ c ∧ c ≤ 0x2040)

/-- [3] S: one or more white space characters. -/
def S (w : Word) : Prop := w ≠ [] ∧ ∀ c ∈ w, IsSpace c

/-- S?: possibly empty white space. -/
def OptS (w : Word) : Prop := ∀ c ∈ w, IsSpace c

/-- [5] Name. -/
def Name (w : Word) : Prop := ∃ c rest, w = c :: rest ∧ NameStartChar c ∧ ∀ d ∈ rest, NameChar d

/-- Namespaces [4] NCName: a Name without a colon. -/
def NCName (w : Word) : Prop := Name w ∧ 58 ∉ w

/-- Namespaces [7] QName, with its prefix (when it has one) and local part. -/
inductive QName : Word → Option Word → Word → Prop
  | unprefixed {l : Word} : NCName l → QName l none l
  | prefixed {p l : Word} : NCName p → NCName l → QName (p ++ 58 :: l) (some p) l

/-- [25] Eq. -/
def Eq (w : Word) : Prop := ∃ a b, w = a ++ 61 :: b ∧ OptS a ∧ OptS b

/-- A quotation mark around a literal. -/
def Quote (q : Nat) : Prop := q = 34 ∨ q = 39

/-! ## Comments, processing instructions, CDATA sections, character data -/

/-- [15] the body of a comment: `((Char - '-') | ('-' (Char - '-')))*`. -/
inductive CommentBody : Word → Prop
  | nil : CommentBody []
  | char {c : Nat} {rest : Word} : c ≠ 45 → CommentBody rest → CommentBody (c :: rest)
  | dash {c : Nat} {rest : Word} : c ≠ 45 → CommentBody rest → CommentBody (45 :: c :: rest)

/-- [15] Comment. -/
def Comment (w : Word) : Prop := ∃ body, w = lit "<!--" ++ body ++ lit "-->" ∧ CommentBody body

/-- [17] PITarget: an NCName (Namespaces §7) other than `xml` in any case. -/
def PITarget (t : Word) : Prop :=
  NCName t ∧ ¬ ∃ a b c, t = [a, b, c] ∧ (a = 120 ∨ a = 88) ∧ (b = 109 ∨ b = 77) ∧ (c = 108 ∨ c = 76)

/-- [16] PI. -/
def PI (w : Word) : Prop :=
  ∃ t rest, w = lit "<?" ++ t ++ rest ++ lit "?>" ∧ PITarget t ∧
    (rest = [] ∨ ∃ s d, rest = s ++ d ∧ S s ∧ ¬ Contains (lit "?>") d)

/-- [18] CDSect, with its character data. -/
def CDSect (w data : Word) : Prop :=
  w = lit "<![CDATA[" ++ data ++ lit "]]>" ∧ ¬ Contains (lit "]]>") data

/-- [14] CharData. -/
def CharData (w : Word) : Prop := (∀ c ∈ w, c ≠ 60 ∧ c ≠ 38) ∧ ¬ Contains (lit "]]>") w

/-! ## References (§4.1, §4.6) -/

def IsDigit (c : Nat) : Prop := 48 ≤ c ∧ c ≤ 57

/-- The value of a hexadecimal digit. -/
def hexDigit (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else none

def decimalValue (ds : Word) : Nat := ds.foldl (fun v d => v * 10 + (d - 48)) 0

def hexValue (ds : Word) : Nat := ds.foldl (fun v d => v * 16 + (hexDigit d).getD 0) 0

/-- [66] CharRef, with the code point it denotes. -/
inductive CharRef : Word → Nat → Prop
  | decimal {ds : Word} : ds ≠ [] → (∀ d ∈ ds, IsDigit d) →
      CharRef (lit "&#" ++ ds ++ [59]) (decimalValue ds)
  | hex {ds : Word} : ds ≠ [] → (∀ d ∈ ds, hexDigit d ≠ none) →
      CharRef (lit "&#x" ++ ds ++ [59]) (hexValue ds)

/-- [68] EntityRef, whose name is an NCName (Namespaces §7). -/
def EntityRef (w ename : Word) : Prop := w = 38 :: ename ++ [59] ∧ NCName ename

/-- §4.6: the character of a predefined entity. -/
def predefinedChar (ename : Word) : Option Nat :=
  if ename = lit "lt" then some 60
  else if ename = lit "gt" then some 62
  else if ename = lit "amp" then some 38
  else if ename = lit "apos" then some 39
  else if ename = lit "quot" then some 34
  else none

/-- A declared general entity: internal with its replacement text, external
    parsed, or unparsed. -/
inductive Def
  | internal (text : Word)
  | external
  | unparsed

/-- General entity declarations in document order. -/
abbrev Env := List (Word × Def)

/-- The binding declaration of an entity: the first one (§4.2). -/
def lookup (env : Env) (ename : Word) : Option Def :=
  (env.find? (fun d => decide (d.1 = ename))).map (·.2)

/-! ## Attribute values (§3.1, §3.3.3) -/

/-- The normalized form of a literal character in an attribute value. -/
def normalized (c : Nat) : Nat := if IsSpace c then 32 else c

/-- §3.3.3: attribute text and its normalized value, for entities not already
    being expanded (`stack`), with the cost of its expansions; `q` is the
    delimiting quote, which cannot occur in it, and `none` for a replacement
    text, where quotes are characters like others (§4.4.5). -/
inductive AttText (env : Env) : List Word → Option Nat → Word → Word → Nat → Prop
  | nil {stack : List Word} {q : Option Nat} : AttText env stack q [] [] 0
  | char {stack : List Word} {q : Option Nat} {c : Nat} {rest out : Word} {k : Nat} :
      c ≠ 60 → c ≠ 38 → q ≠ some c → AttText env stack q rest out k →
      AttText env stack q (c :: rest) (normalized c :: out) k
  | charRef {stack : List Word} {q : Option Nat} {r : Word} {v : Nat} {rest out : Word} {k : Nat} :
      CharRef r v → Rowl.Unicode.XmlChar v → AttText env stack q rest out k →
      AttText env stack q (r ++ rest) (v :: out) k
  | predefined {stack : List Word} {q : Option Nat} {r ename : Word} {v : Nat} {rest out : Word}
      {k : Nat} :
      EntityRef r ename → predefinedChar ename = some v → AttText env stack q rest out k →
      AttText env stack q (r ++ rest) (v :: out) k
  | entity {stack : List Word} {q : Option Nat} {r ename text sub rest out : Word} {k1 k2 : Nat} :
      EntityRef r ename → predefinedChar ename = none → lookup env ename = some (.internal text) →
      ename ∉ stack → AttText env (ename :: stack) none text sub k1 →
      AttText env stack q rest out k2 →
      AttText env stack q (r ++ rest) (sub ++ out) (text.length + 1 + k1 + k2)

/-- [10] AttValue with its normalized value. -/
def AttValue (env : Env) (stack : List Word) (w value : Word) (k : Nat) : Prop :=
  ∃ q body, Quote q ∧ w = q :: body ++ [q] ∧ AttText env stack (some q) body value k

/-- `(S Attribute)*` of a start tag: the attribute specifications as written,
    each a QName and a normalized value ([41] Attribute ::= Name Eq AttValue). -/
inductive Specs (env : Env) : List Word → Word → List (Word × Word) → Nat → Prop
  | nil {stack : List Word} : Specs env stack [] [] 0
  | cons {stack : List Word} {s n e v value rest : Word} {p : Option Word} {l : Word}
      {specs : List (Word × Word)} {k1 k2 : Nat} :
      S s → QName n p l → Eq e → AttValue env stack v value k1 → Specs env stack rest specs k2 →
      Specs env stack (s ++ n ++ e ++ v ++ rest) ((n, value) :: specs) (k1 + k2)

/-! ## Namespaces (Namespaces §3, §5, §6) -/

def xmlNamespace : Word := lit "http://www.w3.org/XML/1998/namespace"
def xmlnsNamespace : Word := lit "http://www.w3.org/2000/xmlns/"

/-- A namespace binding: `none` for the default namespace. -/
abbrev Binding := Option Word × Word

/-- The namespace declaration an attribute specification makes: `xmlns`
    declares the default namespace, `xmlns:p` the prefix `p`. -/
def declaration (spec : Word × Word) : Option Binding :=
  if spec.1 = lit "xmlns" then some (none, spec.2)
  else if lit "xmlns:" <+: spec.1 then some (some (spec.1.drop 6), spec.2)
  else none

/-- [NSC: Reserved Prefixes and Namespace Names] and [NSC: No Prefix
    Undeclaring]. -/
def DeclarationOk : Binding → Prop
  | (none, v) => v ≠ xmlNamespace ∧ v ≠ xmlnsNamespace
  | (some p, v) => p ≠ lit "xmlns" ∧ (p = lit "xml" → v = xmlNamespace) ∧
      (p ≠ lit "xml" → v ≠ [] ∧ v ≠ xmlNamespace ∧ v ≠ xmlnsNamespace)

/-- The bindings in scope, innermost last. -/
abbrev Scope := List Binding

/-- The innermost binding of a prefix. -/
def lookupPrefix (scope : Scope) (p : Word) : Option Word :=
  (scope.reverse.find? (fun b => decide (b.1 = some p))).map (·.2)

/-- The default namespace in scope: the innermost `xmlns`, where an empty
    value means no default namespace. -/
def defaultNamespace (scope : Scope) : Option Word :=
  match scope.reverse.find? (fun b => decide (b.1 = none)) with
  | some (_, v) => if v = [] then none else some v
  | none => none

/-- The namespace name of a prefix: `xml` is bound by definition. -/
def prefixNamespace (scope : Scope) (p : Word) : Option Word :=
  if p = lit "xml" then some xmlNamespace else lookupPrefix scope p

/-- The prefix, namespace name and local name of an element QName: unprefixed
    names are in the default namespace, `xmlns` is no element prefix and every
    other prefix must be declared. -/
inductive ElementName (scope : Scope) : Word → Option Word → Option Word → Word → Prop
  | unprefixed {l : Word} : NCName l → ElementName scope l none (defaultNamespace scope) l
  | prefixed {p l ns : Word} : NCName p → NCName l → p ≠ lit "xmlns" →
      prefixNamespace scope p = some ns → ElementName scope (p ++ 58 :: l) (some p) (some ns) l

/-- The prefix, namespace name and local name of an attribute QName:
    unprefixed attributes have no namespace. -/
inductive AttributeName (scope : Scope) : Word → Option Word → Option Word → Word → Prop
  | unprefixed {l : Word} : NCName l → AttributeName scope l none none l
  | prefixed {p l ns : Word} : NCName p → NCName l →
      prefixNamespace scope p = some ns → AttributeName scope (p ++ 58 :: l) (some p) (some ns) l

/-! ## The element tree -/

/-- The code points of a Rust buffer. -/
def word (v : alloc.vec.Vec U32) : Word := v.val.map (·.val)

def optWord (v : Option (alloc.vec.Vec U32)) : Option Word := v.map word

/-- An attribute as prefix, namespace name, local name and value. -/
def attributeView (a : xml.Attribute) : Option Word × Option Word × Word × Word :=
  (optWord a.ns_prefix, optWord a.ns_name, word a.local_name, word a.value)

def bindingView (b : xml.Binding) : Binding := (optWord b.ns_prefix, word b.value)

/-- A child as a run of characters or an element. -/
def nodeView : xml.Node → Word ⊕ xml.Element
  | .Element e => .inr e
  | .Text t => .inl (word t)

/-- What content contributes to an element's children, in order: characters
    and elements. Comments and processing instructions contribute nothing. -/
inductive Item
  | char (c : Nat)
  | elem (e : xml.Element)

/-- The children of content items: every maximal run of characters is one
    text node. -/
def runs : List Item → List (Word ⊕ xml.Element)
  | [] => []
  | .elem e :: rest => .inr e :: runs rest
  | .char c :: rest =>
    match runs rest with
    | .inl t :: more => .inl (c :: t) :: more
    | more => .inl [c] :: more

/-- The specifications that are not namespace declarations. -/
def plain (specs : List (Word × Word)) : List (Word × Word) :=
  specs.filter (fun s => decide (declaration s = none))

/-- The namespace declarations of the specifications, in document order. -/
def declarations (specs : List (Word × Word)) : List Binding := specs.filterMap declaration

/-- What a start tag with QName `n` and specifications `specs` gives an
    element in scope `scope`: [WFC: Unique Att Spec], the namespace
    constraints, its name, its attributes and declarations. -/
structure StartTag (scope : Scope) (n : Word) (specs : List (Word × Word)) (e : xml.Element) : Prop where
  unique : (specs.map (·.1)).Nodup
  allowed : ∀ d ∈ declarations specs, DeclarationOk d
  declared : e.declarations.val.map bindingView = declarations specs
  named : ElementName (scope ++ declarations specs) n (optWord e.ns_prefix) (optWord e.ns_name)
    (word e.local_name)
  attributes : List.Forall₂
    (fun (s : Word × Word) (a : xml.Attribute) =>
      AttributeName (scope ++ declarations specs) s.1 (optWord a.ns_prefix) (optWord a.ns_name)
        (word a.local_name) ∧ word a.value = s.2)
    (plain specs) e.attributes.val
  distinct : (e.attributes.val.map (fun a => (optWord a.ns_name, word a.local_name))).Nodup

mutual
/-- [39] element, in an entity context `stack` and scope `scope`, with the
    element it denotes and the cost of its expansions. -/
inductive Element (env : Env) : List Word → Scope → Word → xml.Element → Nat → Prop
  | empty {stack : List Word} {scope : Scope} {n attrs s : Word} {p : Option Word} {l : Word}
      {specs : List (Word × Word)} {k : Nat} {e : xml.Element} :
      QName n p l → Specs env stack attrs specs k → OptS s → StartTag scope n specs e →
      e.children.val = [] →
      Element env stack scope (60 :: n ++ attrs ++ s ++ lit "/>") e k
  | full {stack : List Word} {scope : Scope} {n attrs s body s2 : Word} {p : Option Word} {l : Word}
      {specs : List (Word × Word)} {k1 k2 : Nat} {items : List Item} {e : xml.Element} :
      QName n p l → Specs env stack attrs specs k1 → OptS s → StartTag scope n specs e →
      Content env stack (scope ++ declarations specs) body items k2 → OptS s2 →
      e.children.val.map nodeView = runs items →
      Element env stack scope (60 :: n ++ attrs ++ s ++ [62] ++ body ++ lit "</" ++ n ++ s2 ++ [62])
        e (k1 + k2)

/-- [43] content: `CharData? ((element | Reference | CDSect | PI | Comment)
    CharData?)*`, with the items it contributes. -/
inductive Content (env : Env) : List Word → Scope → Word → List Item → Nat → Prop
  | nil {stack : List Word} {scope : Scope} : Content env stack scope [] [] 0
  | last {stack : List Word} {scope : Scope} {cd : Word} :
      cd ≠ [] → CharData cd → Content env stack scope cd (cd.map .char) 0
  | data {stack : List Word} {scope : Scope} {cd m rest : Word} {x items : List Item} {k1 k2 : Nat} :
      cd ≠ [] → CharData cd → Markup env stack scope m x k1 → Content env stack scope rest items k2 →
      Content env stack scope (cd ++ m ++ rest) (cd.map .char ++ x ++ items) (k1 + k2)
  | markup {stack : List Word} {scope : Scope} {m rest : Word} {x items : List Item} {k1 k2 : Nat} :
      Markup env stack scope m x k1 → Content env stack scope rest items k2 →
      Content env stack scope (m ++ rest) (x ++ items) (k1 + k2)

/-- The markup items of content: an element, a reference (whose entity's
    replacement text is read as content, §4.4.2), a CDATA section, a
    processing instruction or a comment. -/
inductive Markup (env : Env) : List Word → Scope → Word → List Item → Nat → Prop
  | element {stack : List Word} {scope : Scope} {w : Word} {e : xml.Element} {k : Nat} :
      Element env stack scope w e k → Markup env stack scope w [.elem e] k
  | charRef {stack : List Word} {scope : Scope} {w : Word} {v : Nat} :
      CharRef w v → Rowl.Unicode.XmlChar v → Markup env stack scope w [.char v] 0
  | predefined {stack : List Word} {scope : Scope} {w ename : Word} {v : Nat} :
      EntityRef w ename → predefinedChar ename = some v → Markup env stack scope w [.char v] 0
  | entity {stack : List Word} {scope : Scope} {w ename text : Word} {items : List Item} {k : Nat} :
      EntityRef w ename → predefinedChar ename = none → lookup env ename = some (.internal text) →
      ename ∉ stack → Content env (ename :: stack) scope text items k →
      Markup env stack scope w items (text.length + 1 + k)
  | cdata {stack : List Word} {scope : Scope} {w data : Word} :
      CDSect w data → Markup env stack scope w (data.map .char) 0
  | pi {stack : List Word} {scope : Scope} {w : Word} : PI w → Markup env stack scope w [] 0
  | comment {stack : List Word} {scope : Scope} {w : Word} : Comment w → Markup env stack scope w [] 0
end

/-! ## The prolog and the document type declaration (§2.8, §4.2) -/

/-- [27] Misc*. -/
inductive Miscs : Word → Prop
  | nil : Miscs []
  | comment {c rest : Word} : Comment c → Miscs rest → Miscs (c ++ rest)
  | pi {c rest : Word} : PI c → Miscs rest → Miscs (c ++ rest)
  | space {c rest : Word} : S c → Miscs rest → Miscs (c ++ rest)

/-- [26] VersionNum. -/
def VersionNum (w : Word) : Prop := ∃ ds, w = lit "1." ++ ds ∧ ds ≠ [] ∧ ∀ d ∈ ds, IsDigit d

/-- [24] VersionInfo. -/
def VersionInfo (w : Word) : Prop :=
  ∃ s e q num, w = s ++ lit "version" ++ e ++ q :: num ++ [q] ∧ S s ∧ Eq e ∧ Quote q ∧ VersionNum num

/-- [81] EncName. -/
def EncName (w : Word) : Prop :=
  ∃ c rest, w = c :: rest ∧ ((65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122)) ∧
    ∀ d ∈ rest, (65 ≤ d ∧ d ≤ 90) ∨ (97 ≤ d ∧ d ≤ 122) ∨ IsDigit d ∨ d = 46 ∨ d = 95 ∨ d = 45

/-- `UTF-8`, matched case-insensitively (§4.3.3): the only supported encoding. -/
def Utf8Name (w : Word) : Prop :=
  ∃ a b c, w = [a, b, c, 45, 56] ∧ (a = 117 ∨ a = 85) ∧ (b = 116 ∨ b = 84) ∧ (c = 102 ∨ c = 70)

/-- [80] EncodingDecl naming UTF-8. -/
def EncodingDecl (w : Word) : Prop :=
  ∃ s e q ename, w = s ++ lit "encoding" ++ e ++ q :: ename ++ [q] ∧ S s ∧ Eq e ∧ Quote q ∧
    EncName ename ∧ Utf8Name ename

/-- [32] SDDecl. -/
def SDDecl (w : Word) : Prop :=
  ∃ s e q yn, w = s ++ lit "standalone" ++ e ++ q :: yn ++ [q] ∧ S s ∧ Eq e ∧ Quote q ∧
    (yn = lit "yes" ∨ yn = lit "no")

/-- [23] XMLDecl. -/
def XMLDecl (w : Word) : Prop :=
  ∃ v e sd s, w = lit "<?xml" ++ v ++ e ++ sd ++ s ++ lit "?>" ∧ VersionInfo v ∧
    (e = [] ∨ EncodingDecl e) ∧ (sd = [] ∨ SDDecl sd) ∧ OptS s

/-- [11] SystemLiteral. -/
def SystemLiteral (w : Word) : Prop := ∃ q body, Quote q ∧ w = q :: body ++ [q] ∧ q ∉ body

/-- [13] PubidChar. -/
def PubidChar (c : Nat) : Prop :=
  c = 32 ∨ c = 13 ∨ c = 10 ∨ (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ IsDigit c ∨
  c ∈ lit "-'()+,./:=?;!*#@$_%"

/-- [12] PubidLiteral. -/
def PubidLiteral (w : Word) : Prop :=
  ∃ q body, Quote q ∧ w = q :: body ++ [q] ∧ ∀ c ∈ body, PubidChar c ∧ c ≠ q

/-- [75] ExternalID. -/
def ExternalID (w : Word) : Prop :=
  (∃ s l, w = lit "SYSTEM" ++ s ++ l ∧ S s ∧ SystemLiteral l) ∨
  (∃ s1 p s2 l, w = lit "PUBLIC" ++ s1 ++ p ++ s2 ++ l ∧ S s1 ∧ PubidLiteral p ∧ S s2 ∧
    SystemLiteral l)

/-- [9] the body of an EntityValue in the internal subset and its replacement
    text (§4.5): character references are replaced, general entity references
    are bypassed, and parameter-entity references cannot occur ([WFC: PEs in
    Internal Subset]). -/
inductive ValueText (q : Nat) : Word → Word → Prop
  | nil : ValueText q [] []
  | char {c : Nat} {rest out : Word} :
      c ≠ q → c ≠ 37 → c ≠ 38 → ValueText q rest out → ValueText q (c :: rest) (c :: out)
  | charRef {r : Word} {v : Nat} {rest out : Word} :
      CharRef r v → Rowl.Unicode.XmlChar v → ValueText q rest out → ValueText q (r ++ rest) (v :: out)
  | entityRef {r ename rest out : Word} :
      EntityRef r ename → ValueText q rest out → ValueText q (r ++ rest) (r ++ out)

/-- [9] EntityValue with its replacement text. -/
def EntityValue (w text : Word) : Prop :=
  ∃ q body, Quote q ∧ w = q :: body ++ [q] ∧ ValueText q body text

/-- [73] EntityDef with the definition it gives. -/
inductive EntityDef : Word → Def → Prop
  | internal {w text : Word} : EntityValue w text → EntityDef w (.internal text)
  | external {w : Word} : ExternalID w → EntityDef w .external
  | unparsed {e s1 s2 n : Word} : ExternalID e → S s1 → S s2 → NCName n →
      EntityDef (e ++ s1 ++ lit "NDATA" ++ s2 ++ n) .unparsed

/-- [71] GEDecl, whose name is an NCName (Namespaces §7). -/
def GEDecl (w : Word) (decl : Word × Def) : Prop :=
  ∃ s1 n s2 d df s3, w = lit "<!ENTITY" ++ s1 ++ n ++ s2 ++ d ++ s3 ++ [62] ∧ S s1 ∧ NCName n ∧
    S s2 ∧ EntityDef d df ∧ OptS s3 ∧ decl = (n, df)

/-- [72] PEDecl. -/
def PEDecl (w : Word) : Prop :=
  ∃ s1 s2 n s3 d s4, w = lit "<!ENTITY" ++ s1 ++ [37] ++ s2 ++ n ++ s3 ++ d ++ s4 ++ [62] ∧ S s1 ∧
    S s2 ∧ NCName n ∧ S s3 ∧ ((∃ t, EntityValue d t) ∨ ExternalID d) ∧ OptS s4

/-- [28b] intSubset, restricted to entity declarations, comments, processing
    instructions and white space, with the general entities in order. -/
inductive IntSubset : Word → Env → Prop
  | nil : IntSubset [] []
  | general {d rest : Word} {decl : Word × Def} {env : Env} :
      GEDecl d decl → IntSubset rest env → IntSubset (d ++ rest) (decl :: env)
  | parameter {d rest : Word} {env : Env} : PEDecl d → IntSubset rest env → IntSubset (d ++ rest) env
  | comment {d rest : Word} {env : Env} : Comment d → IntSubset rest env → IntSubset (d ++ rest) env
  | pi {d rest : Word} {env : Env} : PI d → IntSubset rest env → IntSubset (d ++ rest) env
  | space {d rest : Word} {env : Env} : S d → IntSubset rest env → IntSubset (d ++ rest) env

/-- [28] doctypedecl with the general entities of its internal subset; its
    name is a QName (Namespaces [16]). The external subset is not read. -/
def Doctype (w : Word) (env : Env) : Prop :=
  ∃ s1 n p l ext s2 rest, w = lit "<!DOCTYPE" ++ s1 ++ n ++ ext ++ s2 ++ rest ∧ S s1 ∧ QName n p l ∧
    (ext = [] ∨ ∃ s e, ext = s ++ e ∧ S s ∧ ExternalID e) ∧ OptS s2 ∧
    ((rest = [62] ∧ env = []) ∨
      ∃ body s3, rest = [91] ++ body ++ [93] ++ s3 ++ [62] ∧ IntSubset body env ∧ OptS s3)

/-- [22] prolog, with the general entities declared. -/
def Prolog (w : Word) (env : Env) : Prop :=
  ∃ d m rest, w = d ++ m ++ rest ∧ (d = [] ∨ XMLDecl d) ∧ Miscs m ∧
    ((rest = [] ∧ env = []) ∨ ∃ dt m2, rest = dt ++ m2 ∧ Doctype dt env ∧ Miscs m2)

/-- [1] document: its root element and the cost of its expansions. -/
def Document (cs : Word) (root : xml.Element) (cost : Nat) : Prop :=
  ∃ pro env body tail, cs = pro ++ body ++ tail ∧ Prolog pro env ∧ Element env [] [] body root cost ∧
    Miscs tail

/-! ## Characters of a document entity (§2.11, §4.3.3) -/

/-- §2.11: `#xD #xA` and any other `#xD` become `#xA`. -/
def normalizeLines : Word → Word
  | [] => []
  | 13 :: 10 :: rest => 10 :: normalizeLines rest
  | 13 :: rest => 10 :: normalizeLines rest
  | c :: rest => c :: normalizeLines rest

/-- §4.3.3: a leading byte order mark is no character of the document. -/
def stripOrderMark : Word → Word
  | 0xFEFF :: rest => rest
  | w => w

/-- The characters of a document entity: strict UTF-8 units, each a `Char`,
    without a leading byte order mark and with normalized line ends. -/
def Decoded (bs : List U8) (cs : Word) : Prop :=
  ∃ units, Rowl.Unicode.TextFrom bs 0 units ∧ cs = normalizeLines (stripOrderMark (units.map (·.1)))

/-- A supported document read from bytes: its characters derive a document
    whose expansions cost at most the budget. -/
def Read (bs : List U8) (budget : Nat) (root : xml.Element) : Prop :=
  ∃ cs cost, Decoded bs cs ∧ Document cs root cost ∧ cost ≤ budget

end

end Rowl.XmlGrammar
