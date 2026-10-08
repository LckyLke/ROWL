import Rowl.XmlGrammar
import Mathlib.Computability.Language

/-!
The regular expressions of XML Schema 1.1 Part 2, Appendix G, which the facet
`xsd:pattern` uses (§4.3.4). An expression is read left to right from its code
points by the productions [64]–[98]: each relation below holds of the code
points where its production begins, what the production denotes, and the code
points that follow it. The rules that resolve the grammar's ambiguities are
part of the reading: a branch takes pieces for as long as an atom can begin, a
quantifier after an atom belongs to it, a character group whose first character
is `^` is negative (§G.4.1), and after a single character in a character group
a hyphen is a subtraction when `[` follows it, a character of its own when `]`
or `-[` follows it, and otherwise ends a range at the next single character,
which may not be an unescaped hyphen, nor may the first (§G.4.1).

An expression denotes the strings (lists of code points) of §G.1–§G.4:
branches separated by `|` the union of theirs, pieces the concatenation of
theirs, a quantifier the repetitions of its atom's, and a character class its
characters as strings of one character. Category and block escapes refer to a
Unicode database (`UnicodeData`): the general category of each code point and
the blocks that the processor recognizes, an unrecognized block name standing
for every character (§G.4.2.4). The complement of a set of characters is taken
among all code points; strings of XML characters, the only ones a datatype has,
are in it exactly when they are in the complement among the XML characters.

Each production reads its code points in at most one way, with one meaning
(`regExp_unique` and the theorems before it).
-/
namespace Rowl.XsdRegex
open scoped Computability

/-- A Unicode database (§G.4.2.2, §G.4.2.3): the general category of each code
    point as its two ASCII letters, and the code points of each block that the
    processor recognizes, by its normalized name. -/
structure UnicodeData where
  category : ℕ → ℕ × ℕ
  block : List ℕ → Option (Set ℕ)

/-- A set of characters, by their code points. -/
abbrev Chars := Set ℕ

/-- The strings of one character of a set. -/
def single (C : Chars) : Language ℕ := {w | ∃ c ∈ C, w = [c]}

/-! ### Characters -/

/-- [73] A metacharacter (§G.3): `.`, `\`, `?`, `*`, `+`, `{`, `}`, `(`, `)`,
    `|`, `[` or `]`. A normal character is any other. -/
def Meta (c : ℕ) : Prop :=
  c = 46 ∨ c = 92 ∨ c = 63 ∨ c = 42 ∨ c = 43 ∨ c = 123 ∨ c = 125 ∨ c = 40 ∨ c = 41 ∨ c = 124 ∨ c = 91 ∨
    c = 93

/-- Whether an atom can begin with a character: a normal character, `\`, `[`,
    `.` or `(`. -/
def AtomStart (c : ℕ) : Prop := ¬ Meta c ∨ c = 92 ∨ c = 91 ∨ c = 46 ∨ c = 40

/-- Whether a quantifier begins with a character: `?`, `*`, `+` or `{`. -/
def QuantifierStart (c : ℕ) : Prop := c = 63 ∨ c = 42 ∨ c = 43 ∨ c = 123

/-- [84] The character of a single-character escape `\x` by its letter: `\n`,
    `\r` and `\t` the line feed, the carriage return and the tab, and `\\`,
    `\|`, `\.`, `\?`, `\*`, `\+`, `\(`, `\)`, `\{`, `\}`, `\-`, `\[`, `\]` and
    `\^` the character after `\`. -/
def escapedChar (x : ℕ) : Option ℕ :=
  if x = 110 then some 10
  else if x = 114 then some 13
  else if x = 116 then some 9
  else if x = 92 ∨ x = 124 ∨ x = 46 ∨ x = 63 ∨ x = 42 ∨ x = 43 ∨ x = 40 ∨ x = 41 ∨ x = 123 ∨ x = 125 ∨
      x = 45 ∨ x = 91 ∨ x = 93 ∨ x = 94 then some x
  else none

/-! ### Character class escapes -/

/-- [88]–[95] The name of a category: `L`, `M`, `N`, `P`, `Z`, `S` or `C`, alone
    or with a second letter of its category. -/
def CategoryName : List ℕ → Prop
  | [x] => x = 76 ∨ x = 77 ∨ x = 78 ∨ x = 80 ∨ x = 90 ∨ x = 83 ∨ x = 67
  | [x, y] =>
    (x = 76 ∧ (y = 117 ∨ y = 108 ∨ y = 116 ∨ y = 109 ∨ y = 111)) ∨
    (x = 77 ∧ (y = 110 ∨ y = 99 ∨ y = 101)) ∨
    (x = 78 ∧ (y = 100 ∨ y = 108 ∨ y = 111)) ∨
    (x = 80 ∧ (y = 99 ∨ y = 100 ∨ y = 115 ∨ y = 101 ∨ y = 105 ∨ y = 102 ∨ y = 111)) ∨
    (x = 90 ∧ (y = 115 ∨ y = 108 ∨ y = 112)) ∨
    (x = 83 ∧ (y = 109 ∨ y = 99 ∨ y = 107 ∨ y = 111)) ∨
    (x = 67 ∧ (y = 99 ∨ y = 102 ∨ y = 111 ∨ y = 110))
  | _ => False

/-- The characters of a category (§G.4.2.2): those of the category with both
    letters, or, for one letter, those of every category whose first letter it
    is, but `Cs`. -/
def categoryChars (U : UnicodeData) : List ℕ → Chars
  | [x] => {c | (U.category c).1 = x ∧ U.category c ≠ (67, 115)}
  | [x, y] => {c | U.category c = (x, y)}
  | _ => ∅

/-- [96] A character of a block name: an ASCII letter or digit, or `-`. -/
def BlockChar (c : ℕ) : Prop := (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ (48 ≤ c ∧ c ≤ 57) ∨ c = 45

/-- [87] A property in the braces of `\p{…}`, or of `\P{…}` (`complement`), and
    its characters: a category and its characters or the others, or `Is` and a
    block name and the characters of the block or the others, but every
    character for a block that the database does not recognize
    (§G.4.2.3, §G.4.2.4). -/
def PropertyChars (U : UnicodeData) (complement : Bool) (label : List ℕ) (C : Chars) : Prop :=
  (CategoryName label ∧ C = if complement then (categoryChars U label)ᶜ else categoryChars U label) ∨
  ∃ x, label = 73 :: 115 :: x ∧ x ≠ [] ∧ (∀ c ∈ x, BlockChar c) ∧
    C = match U.block x with
      | some B => if complement then Bᶜ else B
      | none => Set.univ

/-- The characters of `\w` (§G.4.2.5): the code points up to `#x10FFFF` but
    those of the categories `P`, `Z` and `C`. -/
def wordChars (U : UnicodeData) : Chars :=
  {c | c ≤ 0x10FFFF ∧ c ∉ categoryChars U [80] ∧ c ∉ categoryChars U [90] ∧ c ∉ categoryChars U [67]}

/-- [97] The characters of a multi-character escape `\x` by its letter
    (§G.4.2.5): `\s` the space, tab, line feed and carriage return, `\i` the
    name start characters of XML, `\c` the name characters, `\d` those of the
    category `Nd`, `\w` those of `wordChars`, and each upper-case letter the
    characters that its lower-case letter leaves out. -/
def multiChars (U : UnicodeData) (x : ℕ) : Option Chars :=
  if x = 115 then some {c | XmlGrammar.IsSpace c}
  else if x = 83 then some {c | ¬ XmlGrammar.IsSpace c}
  else if x = 105 then some {c | XmlGrammar.NameStartChar c}
  else if x = 73 then some {c | ¬ XmlGrammar.NameStartChar c}
  else if x = 99 then some {c | XmlGrammar.NameChar c}
  else if x = 67 then some {c | ¬ XmlGrammar.NameChar c}
  else if x = 100 then some (categoryChars U [78, 100])
  else if x = 68 then some (categoryChars U [78, 100])ᶜ
  else if x = 119 then some (wordChars U)
  else if x = 87 then some (wordChars U)ᶜ
  else none

/-- [83], [85], [86] A character class escape and its characters: a
    multi-character escape, or `\p{…}` or `\P{…}` with a property. -/
inductive ClassEscape (U : UnicodeData) : List ℕ → Chars → List ℕ → Prop
  | multi {x C rest} : multiChars U x = some C → ClassEscape U (92 :: x :: rest) C rest
  | property {label C rest} : PropertyChars U false label C →
      ClassEscape U (92 :: 112 :: 123 :: (label ++ 125 :: rest)) C rest
  | complement {label C rest} : PropertyChars U true label C →
      ClassEscape U (92 :: 80 :: 123 :: (label ++ 125 :: rest)) C rest

/-! ### Character class expressions -/

/-- [80] A single character in a character group and the character it stands
    for: [84] a single-character escape, or [82] any character but `\`, `[`
    and `]`. -/
inductive SingleChar : List ℕ → ℕ → List ℕ → Prop
  | escape {x c rest} : escapedChar x = some c → SingleChar (92 :: x :: rest) c rest
  | plain {c rest} : c ≠ 92 → c ≠ 91 → c ≠ 93 → SingleChar (c :: rest) c rest

/-- The code points begin with a hyphen. -/
def HyphenFirst (s : List ℕ) : Prop := s.head? = some 45

/-- [79], [81] A character group part and its characters, with the rules of
    §G.4.1 for a hyphen after a single character: before `[` it is a
    subtraction, which the part leaves; before `]` or `-[` it is a character of
    the part; and otherwise it makes a range with the single character after it,
    from the code point of the one to that of the other, neither of them an
    unescaped hyphen. -/
inductive Part (U : UnicodeData) : List ℕ → Chars → List ℕ → Prop
  | escape {s C rest} : ClassEscape U s C rest → Part U s C rest
  | single {s c rest} : SingleChar s c rest → ¬ HyphenFirst rest → Part U s {c} rest
  | subtraction {s c rest} : SingleChar s c (45 :: 91 :: rest) → Part U s {c} (45 :: 91 :: rest)
  | hyphen {s c rest} : SingleChar s c (45 :: 93 :: rest) → Part U s {c, 45} (93 :: rest)
  | hyphenSubtraction {s c rest} : SingleChar s c (45 :: 45 :: 91 :: rest) →
      Part U s {c, 45} (45 :: 91 :: rest)
  | range {s c t d rest} : ¬ HyphenFirst s → SingleChar s c (45 :: t) → ¬ HyphenFirst t →
      SingleChar t d rest → Part U s {x | c ≤ x ∧ x ≤ d} rest

/-- Where the parts of a character group end: before `]` or a subtraction
    `-[`. -/
def PartsEnd (s : List ℕ) : Prop := s.head? = some 93 ∨ s.take 2 = [45, 91]

/-- [77] A positive character group: parts for as long as they do not end, and
    the union of their characters. -/
inductive Parts (U : UnicodeData) : List ℕ → Chars → List ℕ → Prop
  | last {s C rest} : Part U s C rest → PartsEnd rest → Parts U s C rest
  | more {s C t D rest} : Part U s C t → ¬ PartsEnd t → Parts U t D rest → Parts U s (C ∪ D) rest

mutual
/-- [76], [78] A character group and its characters: after `^` a negative group,
    the characters that its parts leave out, and otherwise a positive group;
    and then, after `-`, possibly a class expression, whose characters the
    group leaves out. -/
inductive CharGroup (U : UnicodeData) : List ℕ → Chars → List ℕ → Prop
  | positive {s C rest} : s.head? ≠ some 94 → Parts U s C rest → rest.head? = some 93 → CharGroup U s C rest
  | negative {s C rest} : Parts U s C rest → rest.head? = some 93 → CharGroup U (94 :: s) Cᶜ rest
  | positiveMinus {s C t D rest} : s.head? ≠ some 94 → Parts U s C (45 :: t) → ClassExpr U t D rest →
      CharGroup U s (C \ D) rest
  | negativeMinus {s C t D rest} : Parts U s C (45 :: t) → ClassExpr U t D rest →
      CharGroup U (94 :: s) (Cᶜ \ D) rest

/-- [75] A character class expression: a character group between `[` and
    `]`. -/
inductive ClassExpr (U : UnicodeData) : List ℕ → Chars → List ℕ → Prop
  | mk {s C rest} : CharGroup U s C (93 :: rest) → ClassExpr U (91 :: s) C rest
end

/-- [74] A character class and its characters: a single-character escape, a
    character class escape, a character class expression, or [98] `.`, every
    character but the line feed and the carriage return. -/
inductive CharClass (U : UnicodeData) : List ℕ → Chars → List ℕ → Prop
  | single {x c rest} : escapedChar x = some c → CharClass U (92 :: x :: rest) {c} rest
  | escape {s C rest} : ClassEscape U s C rest → CharClass U s C rest
  | expr {s C rest} : ClassExpr U s C rest → CharClass U s C rest
  | wildcard {rest} : CharClass U (46 :: rest) {c | c ≠ 10 ∧ c ≠ 13} rest

/-! ### Quantifiers -/

/-- A decimal digit. -/
def Digit (d : ℕ) : Prop := 48 ≤ d ∧ d ≤ 57

/-- The number that decimal digits write. -/
def digitsValue (ds : List ℕ) : ℕ := ds.foldl (fun v d => 10 * v + (d - 48)) 0

/-- [71] A numeral: decimal digits for as long as they go on, and its number. -/
def Numeral (s : List ℕ) (n : ℕ) (rest : List ℕ) : Prop :=
  ∃ ds, s = ds ++ rest ∧ ds ≠ [] ∧ (∀ d ∈ ds, Digit d) ∧ (∀ d ∈ rest.head?, ¬ Digit d) ∧ n = digitsValue ds

/-- [67]–[70] A quantifier and the least and, if there is one, the greatest
    number of repetitions it allows: `?` none or one, `*` any number, `+` at
    least one, `{n}` exactly `n`, `{n,}` at least `n` and `{n,m}` from `n` to
    `m`, where `n ≤ m` (§G.2). -/
inductive Quantifier : List ℕ → ℕ → Option ℕ → List ℕ → Prop
  | optional {rest} : Quantifier (63 :: rest) 0 (some 1) rest
  | star {rest} : Quantifier (42 :: rest) 0 none rest
  | plus {rest} : Quantifier (43 :: rest) 1 none rest
  | exact {s n rest} : Numeral s n (125 :: rest) → Quantifier (123 :: s) n (some n) rest
  | atLeast {s n rest} : Numeral s n (44 :: 125 :: rest) → Quantifier (123 :: s) n none rest
  | between {s n t m rest} : Numeral s n (44 :: t) → Numeral t m (125 :: rest) → n ≤ m →
      Quantifier (123 :: s) n (some m) rest

/-- The concatenations of strings of `L`: from `n` to `m` of them, or at least
    `n` without `m`. -/
def Repeats (L : Language ℕ) (n : ℕ) : Option ℕ → Language ℕ
  | none => L ^ n * L∗
  | some m => {w | ∃ k, n ≤ k ∧ k ≤ m ∧ w ∈ L ^ k}

/-! ### Regular expressions -/

mutual
/-- [64] A regular expression: branches separated by `|`, and the union of
    their strings. -/
inductive RegExp (U : UnicodeData) : List ℕ → Language ℕ → List ℕ → Prop
  | last {s L rest} : Branch U s L rest → rest.head? ≠ some 124 → RegExp U s L rest
  | more {s L t M rest} : Branch U s L (124 :: t) → RegExp U t M rest → RegExp U s (L + M) rest

/-- [65] A branch: pieces for as long as an atom can begin, and the
    concatenation of their strings. -/
inductive Branch (U : UnicodeData) : List ℕ → Language ℕ → List ℕ → Prop
  | done {s} : (∀ c ∈ s.head?, ¬ AtomStart c) → Branch U s 1 s
  | piece {s L t M rest} : Piece U s L t → Branch U t M rest → Branch U s (L * M) rest

/-- [66] A piece: an atom with the quantifier that follows it, if one does, and
    the strings of the atom, repeated as the quantifier allows. -/
inductive Piece (U : UnicodeData) : List ℕ → Language ℕ → List ℕ → Prop
  | atom {s L rest} : Atom U s L rest → (∀ c ∈ rest.head?, ¬ QuantifierStart c) → Piece U s L rest
  | quantified {s L t n m rest} : Atom U s L t → Quantifier t n m rest → Piece U s (Repeats L n m) rest

/-- [72] An atom: a normal character, a character class or a regular expression
    in parentheses, and its strings. -/
inductive Atom (U : UnicodeData) : List ℕ → Language ℕ → List ℕ → Prop
  | normal {c rest} : ¬ Meta c → Atom U (c :: rest) (single {c}) rest
  | charClass {s C rest} : CharClass U s C rest → Atom U s (single C) rest
  | group {s L rest} : RegExp U s L (41 :: rest) → Atom U (40 :: s) L rest
end

/-- A regular expression that is all of the code points `cps`, and its
    strings `L`. -/
def Pattern (U : UnicodeData) (cps : List ℕ) (L : Language ℕ) : Prop := RegExp U cps L []

/-! ### One reading -/

theorem singleChar_unique {s c c' rest rest'} (h : SingleChar s c rest) (h' : SingleChar s c' rest') :
    c = c' ∧ rest = rest' := by
  cases h with
  | escape e =>
    cases h' with
    | escape e' => simp_all
    | plain n _ _ => exact absurd rfl n
  | plain n a b =>
    cases h' with
    | escape _ => exact absurd rfl n
    | plain => exact ⟨rfl, rfl⟩

theorem escapedChar_some {x c : ℕ} (e : escapedChar x = some c) :
    x = 110 ∨ x = 114 ∨ x = 116 ∨ x = 92 ∨ x = 124 ∨ x = 46 ∨ x = 63 ∨ x = 42 ∨ x = 43 ∨ x = 40 ∨
      x = 41 ∨ x = 123 ∨ x = 125 ∨ x = 45 ∨ x = 91 ∨ x = 93 ∨ x = 94 := by
  unfold escapedChar at e
  split_ifs at e <;> omega

theorem multiChars_some {U : UnicodeData} {x : ℕ} {C : Chars} (m : multiChars U x = some C) :
    x = 115 ∨ x = 83 ∨ x = 105 ∨ x = 73 ∨ x = 99 ∨ x = 67 ∨ x = 100 ∨ x = 68 ∨ x = 119 ∨ x = 87 := by
  unfold multiChars at m
  split_ifs at m <;> omega

theorem escaped_not_multi {U : UnicodeData} {x c C} (e : escapedChar x = some c) (m : multiChars U x = some C) :
    False := by
  have := escapedChar_some e
  have := multiChars_some m
  omega

theorem categoryName_no_brace {label : List ℕ} (h : CategoryName label) : ∀ c ∈ label, c ≠ 125 := by
  match label, h with
  | [x], h => simp only [CategoryName] at h; simp; omega
  | [x, y], h => simp only [CategoryName] at h; simp; omega

theorem property_no_brace {U : UnicodeData} {b : Bool} {label : List ℕ} {C : Chars} (h : PropertyChars U b label C) :
    ∀ c ∈ label, c ≠ 125 := by
  rcases h with ⟨cat, _⟩ | ⟨x, rfl, _, block, _⟩
  · exact categoryName_no_brace cat
  · intro c mem
    simp only [List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · decide
    · decide
    · have := block c mem
      simp only [BlockChar] at this
      omega

/-- Code points that end at the first `}`: the names before it are the same. -/
theorem brace_split {a b r r' : List ℕ} (ha : ∀ c ∈ a, c ≠ 125) (hb : ∀ c ∈ b, c ≠ 125)
    (h : a ++ 125 :: r = b ++ 125 :: r') : a = b ∧ r = r' := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa using h
    | cons y b =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1.symm (hb y (by simp))
  | cons x a ih =>
    cases b with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1 (ha x (by simp))
    | cons y b =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rest⟩ := h
      have := ih (fun c m => ha c (by simp [m])) (fun c m => hb c (by simp [m])) rest
      exact ⟨by rw [this.1], this.2⟩

theorem categoryName_not_block {x : List ℕ} (ne : x ≠ []) : ¬ CategoryName (73 :: 115 :: x) := by
  cases x with
  | nil => exact absurd rfl ne
  | cons a x => simp [CategoryName]

theorem property_unique {U : UnicodeData} {b : Bool} {label C C'} (h : PropertyChars U b label C)
    (h' : PropertyChars U b label C') : C = C' := by
  rcases h with ⟨cat, rfl⟩ | ⟨x, rfl, ne, _, rfl⟩
  · rcases h' with ⟨_, rfl⟩ | ⟨x, eq, ne, _, _⟩
    · rfl
    · subst eq
      exact absurd cat (categoryName_not_block ne)
  · rcases h' with ⟨cat, _⟩ | ⟨y, eq, _, _, rfl⟩
    · exact absurd cat (categoryName_not_block ne)
    · simp only [List.cons.injEq, true_and] at eq
      rw [eq]

/-- The three forms of a character class escape. -/
theorem classEscape_iff {U : UnicodeData} {s C rest} : ClassEscape U s C rest ↔
    (∃ x, s = 92 :: x :: rest ∧ multiChars U x = some C) ∨
    (∃ label, s = 92 :: 112 :: 123 :: (label ++ 125 :: rest) ∧ PropertyChars U false label C) ∨
    (∃ label, s = 92 :: 80 :: 123 :: (label ++ 125 :: rest) ∧ PropertyChars U true label C) := by
  constructor
  · intro h
    cases h with
    | multi m => exact Or.inl ⟨_, rfl, m⟩
    | property p => exact Or.inr (Or.inl ⟨_, rfl, p⟩)
    | complement p => exact Or.inr (Or.inr ⟨_, rfl, p⟩)
  · rintro (⟨x, rfl, m⟩ | ⟨label, rfl, p⟩ | ⟨label, rfl, p⟩)
    · exact .multi m
    · exact .property p
    · exact .complement p

theorem classEscape_unique {U : UnicodeData} {s C C' rest rest'} (h : ClassEscape U s C rest)
    (h' : ClassEscape U s C' rest') : C = C' ∧ rest = rest' := by
  rcases classEscape_iff.mp h with ⟨x, rfl, m⟩ | ⟨label, rfl, p⟩ | ⟨label, rfl, p⟩ <;>
    rcases classEscape_iff.mp h' with ⟨x', eq, m'⟩ | ⟨label', eq, p'⟩ | ⟨label', eq, p'⟩ <;>
    simp only [List.cons.injEq, true_and] at eq
  · obtain ⟨rfl, rfl⟩ := eq
    simp_all
  · have := multiChars_some m
    omega
  · have := multiChars_some m
    omega
  · have := multiChars_some m'
    omega
  · obtain ⟨rfl, rfl⟩ := brace_split (property_no_brace p) (property_no_brace p') eq
    exact ⟨property_unique p p', rfl⟩
  · omega
  · have := multiChars_some m'
    omega
  · omega
  · obtain ⟨rfl, rfl⟩ := brace_split (property_no_brace p) (property_no_brace p') eq
    exact ⟨property_unique p p', rfl⟩

theorem classEscape_head {U : UnicodeData} {s C rest} (h : ClassEscape U s C rest) :
    ∃ x tail, s = 92 :: x :: tail ∧ escapedChar x = none := by
  rcases classEscape_iff.mp h with ⟨x, rfl, m⟩ | ⟨label, rfl, p⟩ | ⟨label, rfl, p⟩
  · refine ⟨x, rest, rfl, ?_⟩
    cases e : escapedChar x with
    | none => rfl
    | some c => exact (escaped_not_multi e m).elim
  · exact ⟨_, _, rfl, by decide⟩
  · exact ⟨_, _, rfl, by decide⟩

theorem not_escape_single {U : UnicodeData} {s C rest c rest'} (h : ClassEscape U s C rest)
    (h' : SingleChar s c rest') : False := by
  obtain ⟨x, tail, rfl, none⟩ := classEscape_head h
  cases h' with
  | escape e => simp_all
  | plain n => exact n rfl

theorem part_unique {U : UnicodeData} {s C C' rest rest'} (h : Part U s C rest) (h' : Part U s C' rest') :
    C = C' ∧ rest = rest' := by
  cases h with
  | escape e =>
    cases h' with
    | escape e' => exact classEscape_unique e e'
    | single c => exact (not_escape_single e c).elim
    | subtraction c => exact (not_escape_single e c).elim
    | hyphen c => exact (not_escape_single e c).elim
    | hyphenSubtraction c => exact (not_escape_single e c).elim
    | range _ c => exact (not_escape_single e c).elim
  | single c n =>
    cases h' with
    | escape e' => exact (not_escape_single e' c).elim
    | single c' n' => obtain ⟨rfl, rfl⟩ := singleChar_unique c c'; exact ⟨rfl, rfl⟩
    | subtraction c' => obtain ⟨_, rfl⟩ := singleChar_unique c c'; exact absurd rfl n
    | hyphen c' => obtain ⟨_, rfl⟩ := singleChar_unique c c'; exact absurd rfl n
    | hyphenSubtraction c' => obtain ⟨_, rfl⟩ := singleChar_unique c c'; exact absurd rfl n
    | range _ c' => obtain ⟨_, rfl⟩ := singleChar_unique c c'; exact absurd rfl n
  | subtraction c =>
    cases h' with
    | escape e' => exact (not_escape_single e' c).elim
    | single c' n' => obtain ⟨_, eq⟩ := singleChar_unique c c'; rw [← eq] at n'; exact absurd rfl n'
    | subtraction c' => obtain ⟨rfl, eq⟩ := singleChar_unique c c'; exact ⟨rfl, eq⟩
    | hyphen c' => obtain ⟨_, eq⟩ := singleChar_unique c c'; simp at eq
    | hyphenSubtraction c' => obtain ⟨_, eq⟩ := singleChar_unique c c'; simp at eq
    | range _ c' _ d =>
      obtain ⟨_, eq⟩ := singleChar_unique c c'
      simp only [List.cons.injEq, true_and] at eq
      subst eq
      cases d with
      | plain _ n => exact absurd rfl n
  | hyphen c =>
    cases h' with
    | escape e' => exact (not_escape_single e' c).elim
    | single c' n' => obtain ⟨_, eq⟩ := singleChar_unique c c'; rw [← eq] at n'; exact absurd rfl n'
    | subtraction c' => obtain ⟨_, eq⟩ := singleChar_unique c c'; simp at eq
    | hyphen c' =>
      obtain ⟨rfl, eq⟩ := singleChar_unique c c'
      simp at eq
      subst eq
      exact ⟨rfl, rfl⟩
    | hyphenSubtraction c' => obtain ⟨_, eq⟩ := singleChar_unique c c'; simp at eq
    | range _ c' _ d =>
      obtain ⟨_, eq⟩ := singleChar_unique c c'
      simp only [List.cons.injEq, true_and] at eq
      subst eq
      cases d with
      | plain _ _ n => exact absurd rfl n
  | hyphenSubtraction c =>
    cases h' with
    | escape e' => exact (not_escape_single e' c).elim
    | single c' n' => obtain ⟨_, eq⟩ := singleChar_unique c c'; rw [← eq] at n'; exact absurd rfl n'
    | subtraction c' => obtain ⟨_, eq⟩ := singleChar_unique c c'; simp at eq
    | hyphen c' => obtain ⟨_, eq⟩ := singleChar_unique c c'; simp at eq
    | hyphenSubtraction c' =>
      obtain ⟨rfl, eq⟩ := singleChar_unique c c'
      simp at eq
      subst eq
      exact ⟨rfl, rfl⟩
    | range _ c' t _ =>
      obtain ⟨_, eq⟩ := singleChar_unique c c'
      simp only [List.cons.injEq, true_and] at eq
      subst eq
      exact absurd rfl t
  | range n c t d =>
    cases h' with
    | escape e' => exact (not_escape_single e' c).elim
    | single c' n' => obtain ⟨_, eq⟩ := singleChar_unique c c'; rw [← eq] at n'; exact absurd rfl n'
    | subtraction c' =>
      obtain ⟨_, eq⟩ := singleChar_unique c c'
      simp only [List.cons.injEq, true_and] at eq
      subst eq
      cases d with
      | plain _ n => exact absurd rfl n
    | hyphen c' =>
      obtain ⟨_, eq⟩ := singleChar_unique c c'
      simp only [List.cons.injEq, true_and] at eq
      subst eq
      cases d with
      | plain _ _ n => exact absurd rfl n
    | hyphenSubtraction c' =>
      obtain ⟨_, eq⟩ := singleChar_unique c c'
      simp only [List.cons.injEq, true_and] at eq
      subst eq
      exact absurd rfl t
    | range _ c' _ d' =>
      obtain ⟨rfl, eq⟩ := singleChar_unique c c'
      simp only [List.cons.injEq, true_and] at eq
      subst eq
      obtain ⟨rfl, rfl⟩ := singleChar_unique d d'
      exact ⟨rfl, rfl⟩

theorem parts_unique {U : UnicodeData} {s C C' rest rest'} (h : Parts U s C rest) (h' : Parts U s C' rest') :
    C = C' ∧ rest = rest' := by
  induction h generalizing C' rest' with
  | last p e =>
    cases h' with
    | last p' _ => exact part_unique p p'
    | more p' n _ => obtain ⟨_, rfl⟩ := part_unique p p'; exact absurd e n
  | more p n _ ih =>
    cases h' with
    | last p' e => obtain ⟨_, rfl⟩ := part_unique p p'; exact absurd e n
    | more p' _ q' =>
      obtain ⟨rfl, rfl⟩ := part_unique p p'
      obtain ⟨rfl, rfl⟩ := ih q'
      exact ⟨rfl, rfl⟩

mutual
theorem charGroup_unique {U : UnicodeData} {s C C' rest rest'} :
    CharGroup U s C rest → CharGroup U s C' rest' → C = C' ∧ rest = rest'
  | .positive n p e, .positive _ p' _ => parts_unique p p'
  | .positive _ p e, .negative _ _ => absurd rfl ‹(94 :: _).head? ≠ some 94›
  | .positive _ p e, .positiveMinus _ p' _ => by obtain ⟨_, rfl⟩ := parts_unique p p'; simp at e
  | .positive _ p e, .negativeMinus _ _ => absurd rfl ‹(94 :: _).head? ≠ some 94›
  | .negative _ _, .positive n _ _ => absurd rfl n
  | .negative p e, .negative p' _ => by obtain ⟨rfl, rfl⟩ := parts_unique p p'; exact ⟨rfl, rfl⟩
  | .negative _ _, .positiveMinus n _ _ => absurd rfl n
  | .negative p e, .negativeMinus p' _ => by obtain ⟨_, rfl⟩ := parts_unique p p'; simp at e
  | .positiveMinus _ p _, .positive _ p' e => by obtain ⟨_, rfl⟩ := parts_unique p p'; simp at e
  | .positiveMinus _ _ _, .negative _ _ => absurd rfl ‹(94 :: _).head? ≠ some 94›
  | .positiveMinus _ p x, .positiveMinus _ p' x' => by
    obtain ⟨rfl, eq⟩ := parts_unique p p'
    simp only [List.cons.injEq, true_and] at eq
    subst eq
    obtain ⟨rfl, rfl⟩ := classExpr_unique x x'
    exact ⟨rfl, rfl⟩
  | .positiveMinus _ _ _, .negativeMinus _ _ => absurd rfl ‹(94 :: _).head? ≠ some 94›
  | .negativeMinus _ _, .positive n _ _ => absurd rfl n
  | .negativeMinus p _, .negative p' e => by obtain ⟨_, rfl⟩ := parts_unique p p'; simp at e
  | .negativeMinus _ _, .positiveMinus n _ _ => absurd rfl n
  | .negativeMinus p x, .negativeMinus p' x' => by
    obtain ⟨rfl, eq⟩ := parts_unique p p'
    simp only [List.cons.injEq, true_and] at eq
    subst eq
    obtain ⟨rfl, rfl⟩ := classExpr_unique x x'
    exact ⟨rfl, rfl⟩

theorem classExpr_unique {U : UnicodeData} {s C C' rest rest'} :
    ClassExpr U s C rest → ClassExpr U s C' rest' → C = C' ∧ rest = rest'
  | .mk g, .mk g' => by
    obtain ⟨rfl, eq⟩ := charGroup_unique g g'
    simp only [List.cons.injEq, true_and] at eq
    exact ⟨rfl, eq⟩
end

theorem charClass_unique {U : UnicodeData} {s C C' rest rest'} (h : CharClass U s C rest)
    (h' : CharClass U s C' rest') : C = C' ∧ rest = rest' := by
  cases h with
  | single e =>
    cases h' with
    | single e' => simp_all
    | escape x => obtain ⟨_, _, eq, none⟩ := classEscape_head x; simp only [List.cons.injEq] at eq; simp_all
    | expr x => cases x
  | escape x =>
    cases h' with
    | single e => obtain ⟨_, _, eq, none⟩ := classEscape_head x; simp only [List.cons.injEq] at eq; simp_all
    | escape x' => exact classEscape_unique x x'
    | expr x' => obtain ⟨_, _, eq, _⟩ := classEscape_head x; cases x'; simp at eq
    | wildcard => obtain ⟨_, _, eq, _⟩ := classEscape_head x; simp at eq
  | expr x =>
    cases h' with
    | single e => cases x
    | escape x' => obtain ⟨_, _, eq, _⟩ := classEscape_head x'; cases x; simp at eq
    | expr x' => exact classExpr_unique x x'
    | wildcard => cases x
  | wildcard =>
    cases h' with
    | escape x' => obtain ⟨_, _, eq, _⟩ := classEscape_head x'; simp at eq
    | expr x' => cases x'
    | wildcard => exact ⟨rfl, rfl⟩

/-- Digits followed by no digit: the digits are the same in two such splits. -/
theorem digits_split {ds ds' r r' : List ℕ} (digits : ∀ d ∈ ds, Digit d) (digits' : ∀ d ∈ ds', Digit d)
    (stop : ∀ d ∈ r.head?, ¬ Digit d) (stop' : ∀ d ∈ r'.head?, ¬ Digit d) (eq : ds ++ r = ds' ++ r') :
    ds = ds' := by
  induction ds generalizing ds' with
  | nil =>
    cases ds' with
    | nil => rfl
    | cons d ds' =>
      simp only [List.nil_append, List.cons_append] at eq
      subst eq
      exact absurd (digits' d (by simp)) (stop d (by simp))
  | cons d ds ih =>
    cases ds' with
    | nil =>
      simp only [List.nil_append, List.cons_append] at eq
      subst eq
      exact absurd (digits d (by simp)) (stop' d (by simp))
    | cons d' ds' =>
      simp only [List.cons_append, List.cons.injEq] at eq
      obtain ⟨rfl, eq⟩ := eq
      rw [ih (fun x m => digits x (by simp [m])) (fun x m => digits' x (by simp [m])) eq]

theorem numeral_unique {s n n' rest rest'} (h : Numeral s n rest) (h' : Numeral s n' rest') :
    n = n' ∧ rest = rest' := by
  obtain ⟨ds, rfl, _, digits, stop, rfl⟩ := h
  obtain ⟨ds', eq, _, digits', stop', rfl⟩ := h'
  obtain rfl := digits_split digits digits' stop stop' eq
  exact ⟨rfl, List.append_cancel_left eq⟩

theorem numeral_head {s n rest} (h : Numeral s n rest) : ∃ d tail, s = d :: tail ∧ Digit d := by
  obtain ⟨ds, rfl, ne, digits, _, _⟩ := h
  cases ds with
  | nil => exact absurd rfl ne
  | cons d ds => exact ⟨d, ds ++ rest, rfl, digits d (by simp)⟩

theorem quantifier_unique {s n n' m m' rest rest'} (h : Quantifier s n m rest) (h' : Quantifier s n' m' rest') :
    n = n' ∧ m = m' ∧ rest = rest' := by
  cases h with
  | optional => cases h'; exact ⟨rfl, rfl, rfl⟩
  | star => cases h'; exact ⟨rfl, rfl, rfl⟩
  | plus => cases h'; exact ⟨rfl, rfl, rfl⟩
  | exact a =>
    cases h' with
    | exact a' =>
      obtain ⟨rfl, eq⟩ := numeral_unique a a'
      simp at eq
      exact ⟨rfl, rfl, eq⟩
    | atLeast a' => obtain ⟨_, eq⟩ := numeral_unique a a'; simp at eq
    | between a' _ _ => obtain ⟨_, eq⟩ := numeral_unique a a'; simp at eq
  | atLeast a =>
    cases h' with
    | exact a' => obtain ⟨_, eq⟩ := numeral_unique a a'; simp at eq
    | atLeast a' =>
      obtain ⟨rfl, eq⟩ := numeral_unique a a'
      simp at eq
      exact ⟨rfl, rfl, eq⟩
    | between a' b' _ =>
      obtain ⟨_, eq⟩ := numeral_unique a a'
      simp only [List.cons.injEq, true_and] at eq
      subst eq
      obtain ⟨d, tail, eq, digit⟩ := numeral_head b'
      simp only [List.cons.injEq] at eq
      rw [← eq.1] at digit
      simp [Digit] at digit
  | between a b _ =>
    cases h' with
    | exact a' => obtain ⟨_, eq⟩ := numeral_unique a a'; simp at eq
    | atLeast a' =>
      obtain ⟨_, eq⟩ := numeral_unique a a'
      simp only [List.cons.injEq, true_and] at eq
      subst eq
      obtain ⟨d, tail, eq, digit⟩ := numeral_head b
      simp only [List.cons.injEq] at eq
      rw [← eq.1] at digit
      simp [Digit] at digit
    | between a' b' _ =>
      obtain ⟨rfl, eq⟩ := numeral_unique a a'
      simp only [List.cons.injEq, true_and] at eq
      subst eq
      obtain ⟨rfl, eq⟩ := numeral_unique b b'
      simp at eq
      exact ⟨rfl, rfl, eq⟩

theorem quantifier_head {s n m rest} (h : Quantifier s n m rest) : ∃ c tail, s = c :: tail ∧ QuantifierStart c := by
  cases h <;> exact ⟨_, _, rfl, by simp [QuantifierStart]⟩

theorem classExpr_head {U : UnicodeData} {s C rest} (h : ClassExpr U s C rest) : ∃ tail, s = 91 :: tail := by
  cases h; exact ⟨_, rfl⟩

theorem charClass_head {U : UnicodeData} {s C rest} (h : CharClass U s C rest) :
    ∃ c tail, s = c :: tail ∧ (c = 92 ∨ c = 91 ∨ c = 46) := by
  cases h with
  | single => exact ⟨_, _, rfl, by simp⟩
  | escape x => obtain ⟨_, _, rfl, _⟩ := classEscape_head x; exact ⟨_, _, rfl, by simp⟩
  | expr x => obtain ⟨_, rfl⟩ := classExpr_head x; exact ⟨_, _, rfl, by simp⟩
  | wildcard => exact ⟨_, _, rfl, by simp⟩

theorem atom_head {U : UnicodeData} {s L rest} (h : Atom U s L rest) : ∃ c tail, s = c :: tail ∧ AtomStart c := by
  cases h with
  | normal n => exact ⟨_, _, rfl, Or.inl n⟩
  | charClass x =>
    obtain ⟨c, _, rfl, hc⟩ := charClass_head x
    exact ⟨_, _, rfl, by simp only [AtomStart]; omega⟩
  | group => exact ⟨_, _, rfl, by simp [AtomStart]⟩

theorem piece_head {U : UnicodeData} {s L rest} (h : Piece U s L rest) : ∃ c tail, s = c :: tail ∧ AtomStart c := by
  cases h with
  | atom a => exact atom_head a
  | quantified a => exact atom_head a

mutual
theorem regExp_unique {U : UnicodeData} {s L L' rest rest'} (h : RegExp U s L rest) (h' : RegExp U s L' rest') :
    L = L' ∧ rest = rest' :=
  match h, h' with
  | .last b _, .last b' _ => branch_unique b b'
  | .last b n, .more b' _ => by obtain ⟨_, rfl⟩ := branch_unique b b'; exact absurd rfl n
  | .more b _, .last b' n => by obtain ⟨_, eq⟩ := branch_unique b b'; rw [← eq] at n; exact absurd rfl n
  | .more b r, .more b' r' => by
    obtain ⟨rfl, eq⟩ := branch_unique b b'
    simp only [List.cons.injEq, true_and] at eq
    subst eq
    obtain ⟨rfl, rfl⟩ := regExp_unique r r'
    exact ⟨rfl, rfl⟩
termination_by structural h

theorem branch_unique {U : UnicodeData} {s L L' rest rest'} (h : Branch U s L rest) (h' : Branch U s L' rest') :
    L = L' ∧ rest = rest' :=
  match h, h' with
  | .done _, .done _ => ⟨rfl, rfl⟩
  | .done n, .piece p _ => by obtain ⟨c, _, rfl, start⟩ := piece_head p; exact absurd start (n c rfl)
  | .piece p _, .done n => by obtain ⟨c, _, rfl, start⟩ := piece_head p; exact absurd start (n c rfl)
  | .piece p b, .piece p' b' => by
    obtain ⟨rfl, rfl⟩ := piece_unique p p'
    obtain ⟨rfl, rfl⟩ := branch_unique b b'
    exact ⟨rfl, rfl⟩
termination_by structural h

theorem piece_unique {U : UnicodeData} {s L L' rest rest'} (h : Piece U s L rest) (h' : Piece U s L' rest') :
    L = L' ∧ rest = rest' :=
  match h, h' with
  | .atom a _, .atom a' _ => atom_unique a a'
  | .atom a n, .quantified a' q => by
    obtain ⟨_, rfl⟩ := atom_unique a a'
    obtain ⟨c, _, rfl, start⟩ := quantifier_head q
    exact absurd start (n c rfl)
  | .quantified a q, .atom a' n => by
    obtain ⟨_, rfl⟩ := atom_unique a a'
    obtain ⟨c, _, rfl, start⟩ := quantifier_head q
    exact absurd start (n c rfl)
  | .quantified a q, .quantified a' q' => by
    obtain ⟨rfl, rfl⟩ := atom_unique a a'
    obtain ⟨rfl, rfl, rfl⟩ := quantifier_unique q q'
    exact ⟨rfl, rfl⟩
termination_by structural h

theorem atom_unique {U : UnicodeData} {s L L' rest rest'} (h : Atom U s L rest) (h' : Atom U s L' rest') :
    L = L' ∧ rest = rest' :=
  match h, h' with
  | .normal _, .normal _ => ⟨rfl, rfl⟩
  | .normal n, .charClass x => by
    obtain ⟨c, _, eq, hc⟩ := charClass_head x
    simp only [List.cons.injEq] at eq
    rw [eq.1] at n
    exact absurd (by simp only [Meta]; omega) n
  | .normal n, .group _ => absurd (by simp [Meta]) n
  | .charClass x, .normal n => by
    obtain ⟨c, _, eq, hc⟩ := charClass_head x
    simp only [List.cons.injEq] at eq
    rw [eq.1] at n
    exact absurd (by simp only [Meta]; omega) n
  | .charClass x, .charClass x' => by
    obtain ⟨rfl, rfl⟩ := charClass_unique x x'
    exact ⟨rfl, rfl⟩
  | .charClass x, .group _ => by
    obtain ⟨c, _, eq, hc⟩ := charClass_head x
    simp only [List.cons.injEq] at eq
    omega
  | .group _, .normal n => absurd (by simp [Meta]) n
  | .group _, .charClass x => by
    obtain ⟨c, _, eq, hc⟩ := charClass_head x
    simp only [List.cons.injEq] at eq
    omega
  | .group r, .group r' => by
    obtain ⟨rfl, eq⟩ := regExp_unique r r'
    simp only [List.cons.injEq, true_and] at eq
    exact ⟨rfl, eq⟩
termination_by structural h
end

/-- A regular expression has one set of strings. -/
theorem pattern_unique {U : UnicodeData} {cps : List ℕ} {L L' : Language ℕ} (h : Pattern U cps L)
    (h' : Pattern U cps L') : L = L' :=
  (regExp_unique h h').1

end Rowl.XsdRegex
