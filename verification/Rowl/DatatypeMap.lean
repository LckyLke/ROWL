import Rowl.OwlSemantics
import Rowl.LangTag

/-!
Independent specification of the OWL 2 datatype map on five of its datatypes:
`xsd:integer`, `xsd:decimal`, `xsd:string`, `rdf:PlainLiteral` and
`xsd:boolean` (2012 Structural Specification §4, XML Schema 1.1 Part 2 and the
rdf:PlainLiteral specification). Numbers are rationals, strings the UTF-8
bytes of XML characters, language tags well-formed BCP 47 tags compared in
lower case, and the values of the three families are pairwise different.
`Normative` says that a datatype map agrees with the OWL 2 datatype map on
these datatypes and leaves every other datatype open; facets are not
specified here.
-/
namespace Rowl.DatatypeMap
open Aeneas Aeneas.Std RowlRust.model
open Rowl.Owl (DatatypeMap)
universe w

/-- `xsd:integer` -/
def integerType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 105#u8, 110#u8, 116#u8, 101#u8, 103#u8, 101#u8, 114#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:decimal` -/
def decimalType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 100#u8, 101#u8, 99#u8, 105#u8, 109#u8, 97#u8, 108#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:string` -/
def stringType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 115#u8, 116#u8, 114#u8, 105#u8, 110#u8, 103#u8] (by simp; scalar_tac)⟩⟩
/-- `rdf:PlainLiteral` -/
def plainType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 80#u8, 108#u8, 97#u8, 105#u8, 110#u8, 76#u8, 105#u8, 116#u8, 101#u8, 114#u8, 97#u8, 108#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:boolean` -/
def booleanType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 98#u8, 111#u8, 111#u8, 108#u8, 101#u8, 97#u8, 110#u8] (by simp; scalar_tac)⟩⟩

/-- An ASCII decimal digit. -/
def Digit (byte : U8) : Prop := 48 ≤ byte.val ∧ byte.val ≤ 57
/-- Every byte is an ASCII decimal digit. -/
def Digits (bytes : List U8) : Prop := ∀ byte ∈ bytes, Digit byte
/-- The natural number that the digits write in base ten. -/
def digitsValue (bytes : List U8) : Nat :=
  bytes.foldl (fun value byte => 10 * value + (byte.val - 48)) 0
/-- An optional sign: nothing, `+` or `-`. -/
def Sign (sign : List U8) : Prop := sign = [] ∨ sign = [43#u8] ∨ sign = [45#u8]
/-- The factor of a sign. -/
def signValue (sign : List U8) : ℚ := if sign = [45#u8] then -1 else 1

/-- `text` is a lexical form `(\+|-)?[0-9]+` of `xsd:integer` for the
    number `q`. -/
def IntegerForm (text : List U8) (q : ℚ) : Prop :=
  ∃ sign whole, Sign sign ∧ Digits whole ∧ whole ≠ [] ∧ text = sign ++ whole ∧
    q = signValue sign * digitsValue whole
/-- `text` is a lexical form `(\+|-)?([0-9]+(\.[0-9]*)?|\.[0-9]+)` of
    `xsd:decimal` for the number `q`. -/
def DecimalForm (text : List U8) (q : ℚ) : Prop :=
  ∃ sign whole fraction, Sign sign ∧ Digits whole ∧ Digits fraction ∧
    ((text = sign ++ whole ∧ whole ≠ [] ∧ fraction = []) ∨
      (text = sign ++ whole ++ 46#u8 :: fraction ∧ (whole ≠ [] ∨ fraction ≠ []))) ∧
    q = signValue sign * ((digitsValue whole : ℚ) + (digitsValue fraction : ℚ) / 10 ^ fraction.length)
/-- The integers. -/
def IsInteger (q : ℚ) : Prop := ∃ z : ℤ, q = z
/-- The decimal numbers: integers divided by a power of ten. -/
def IsDecimal (q : ℚ) : Prop := ∃ (z : ℤ) (n : ℕ), q = z / 10 ^ n

/-- The UTF-8 encoding of a string of XML characters. -/
def XmlText (bytes : List U8) : Prop := ∃ text, Rowl.Unicode.TextFrom bytes 0 text
/-- A well-formed BCP 47 language tag. -/
def LanguageTag (bytes : List U8) : Prop :=
  ∃ word, Rowl.Regular.Utf8From bytes 0 word ∧ word ∈ Rowl.LangTag.WellFormedLanguage
/-- `lowered` is `bytes` with ASCII upper case in lower case. -/
def Lowered (bytes lowered : List U8) : Prop :=
  lowered.map (·.val) = bytes.map fun byte => if 65 ≤ byte.val ∧ byte.val ≤ 90 then byte.val + 32 else byte.val
/-- A well-formed language tag in lower case. -/
def TagValue (tag : List U8) : Prop := ∃ written, LanguageTag written ∧ Lowered written tag
/-- `lexical` is `text@tag` with no `@` in `tag`. -/
def PlainSplit (lexical text tag : List U8) : Prop := lexical = text ++ 64#u8 :: tag ∧ 64#u8 ∉ tag
/-- `text` is a lexical form of `xsd:boolean` for the truth value `b`. -/
def TruthForm (text : List U8) (b : Bool) : Prop :=
  (b = true ∧ (text = [116#u8, 114#u8, 117#u8, 101#u8] ∨ text = [49#u8])) ∨
  (b = false ∧ (text = [102#u8, 97#u8, 108#u8, 115#u8, 101#u8] ∨ text = [48#u8]))

/-- A datatype map that is the OWL 2 datatype map on the five datatypes: they
    are supported, with these lexical spaces and lexical-to-value mappings; a
    number is the image of a rational, a string or a pair of a string and a
    lower-case language tag the image of its bytes, and a truth value the image
    of a Boolean, injectively on the values; the value spaces are the integers,
    the decimal numbers, the strings, the strings with or without a language
    tag and the two truth values; and numbers, plain literals and truth values
    are pairwise different. -/
structure Normative {Native : Type w} (D : DatatypeMap Native) where
  number : ℚ → Native
  text : List U8 → Native
  tagged : List U8 → List U8 → Native
  truth : Bool → Native
  number_injective : Function.Injective number
  text_injective : ∀ s t, XmlText s → XmlText t → text s = text t → s = t
  tagged_injective : ∀ s t l m, XmlText s → XmlText t → TagValue l → TagValue m →
    tagged s l = tagged t m → s = t ∧ l = m
  truth_injective : Function.Injective truth
  number_text : ∀ q s, XmlText s → number q ≠ text s
  number_tagged : ∀ q s l, XmlText s → TagValue l → number q ≠ tagged s l
  number_truth : ∀ q b, number q ≠ truth b
  text_tagged : ∀ s t l, XmlText s → XmlText t → TagValue l → text s ≠ tagged t l
  text_truth : ∀ s b, XmlText s → text s ≠ truth b
  tagged_truth : ∀ s l b, XmlText s → TagValue l → tagged s l ≠ truth b
  integer_supported : D.supported integerType
  decimal_supported : D.supported decimalType
  string_supported : D.supported stringType
  plain_supported : D.supported plainType
  boolean_supported : D.supported booleanType
  integer_space : ∀ x, D.valueSpace integerType x ↔ ∃ q, IsInteger q ∧ x = number q
  decimal_space : ∀ x, D.valueSpace decimalType x ↔ ∃ q, IsDecimal q ∧ x = number q
  string_space : ∀ x, D.valueSpace stringType x ↔ ∃ s, XmlText s ∧ x = text s
  plain_space : ∀ x, D.valueSpace plainType x ↔
    (∃ s, XmlText s ∧ x = text s) ∨ ∃ s l, XmlText s ∧ TagValue l ∧ x = tagged s l
  boolean_space : ∀ x, D.valueSpace booleanType x ↔ ∃ b, x = truth b
  integer_lexical : ∀ t, D.lexicalSpace integerType t ↔ ∃ q, IntegerForm t q
  integer_value : ∀ t q, IntegerForm t q → D.lexicalValue integerType t = number q
  decimal_lexical : ∀ t, D.lexicalSpace decimalType t ↔ ∃ q, DecimalForm t q
  decimal_value : ∀ t q, DecimalForm t q → D.lexicalValue decimalType t = number q
  string_lexical : ∀ t, D.lexicalSpace stringType t ↔ XmlText t
  string_value : ∀ t, XmlText t → D.lexicalValue stringType t = text t
  plain_lexical : ∀ t, D.lexicalSpace plainType t ↔
    ∃ s l, PlainSplit t s l ∧ XmlText s ∧ (l = [] ∨ LanguageTag l)
  plain_text : ∀ t s, PlainSplit t s [] → XmlText s → D.lexicalValue plainType t = text s
  plain_tagged : ∀ t s l m, PlainSplit t s l → XmlText s → LanguageTag l → Lowered l m →
    D.lexicalValue plainType t = tagged s m
  boolean_lexical : ∀ t, D.lexicalSpace booleanType t ↔ ∃ b, TruthForm t b
  boolean_value : ∀ t b, TruthForm t b → D.lexicalValue booleanType t = truth b

end Rowl.DatatypeMap
