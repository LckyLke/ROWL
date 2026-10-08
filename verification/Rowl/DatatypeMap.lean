import Rowl.OwlSemantics
import Rowl.LangTag
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Log
import Mathlib.Data.Rat.Floor
import Mathlib.Data.EReal.Basic

/-!
Independent specification of the OWL 2 datatype map on the datatypes the
reasoner knows (2012 Structural Specification §4, XML Schema 1.1 Part 2 and the
rdf:PlainLiteral specification): `owl:real`, `owl:rational`, `xsd:decimal`,
`xsd:integer` and its twelve subtypes, `xsd:string` and its six subtypes
`xsd:normalizedString`, `xsd:token`, `xsd:language`, `xsd:NMTOKEN`, `xsd:Name`
and `xsd:NCName`, `rdf:PlainLiteral`, `xsd:boolean`, `xsd:anyURI`,
`xsd:hexBinary` and `xsd:base64Binary`, `xsd:dateTime` and `xsd:dateTimeStamp`,
and `xsd:double` and `xsd:float`, with the four range facets
`xsd:minInclusive`, `xsd:maxInclusive`, `xsd:minExclusive` and
`xsd:maxExclusive`.

Numbers are real numbers: the value space of `owl:real` is the image of ℝ, and
the rationals, decimals and integers are the images of their own sets, so a
value of one numeric datatype is the same value in every numeric datatype whose
value space has it (§4.1: the numeric value spaces are nested). Strings are the
UTF-8 bytes of XML characters, language tags well-formed BCP 47 tags compared in
lower case, and the values of the families are pairwise different.

`owl:real` has no lexical forms; `owl:rational` has the forms
`numerator/denominator`; the integer subtypes have the integer forms whose
numbers lie within their bounds. A facet value of a range facet is the set of
all real numbers on the facet's side of the constraining value, the same set
for every datatype whose facet space has the pair; a datatype restriction
intersects it with the datatype's value space (Direct Semantics Table 4), which
gives the per-datatype facet values of Table 4 of §4.1. The facet spaces are
those of Table 4 for `owl:real` and `owl:rational` (every real constraining
value) and those of XML Schema for its numeric datatypes (a constraining value
of the datatype's value space). The values of `xsd:double` and `xsd:float`
are those of their binary formats (`Binary`), each datatype apart from the
reals and from the other; their range facets take a constraining value of the
datatype and select its values on the facet's side in the order of XML Schema,
in which the two zeros are equal and NaN is comparable to no value. The range
facets of `xsd:dateTime` and `xsd:dateTimeStamp` take a time instant and select
the time instants on its side in the order of XML Schema: by their places on the
time line (`Moment.key`), and between an instant with a time zone and one
without only when that holds for every offset the latter could have. `Normative`
says that a datatype map agrees with the OWL 2 datatype map on these datatypes
and facets and leaves every other datatype open.
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

/-- `owl:real` -/
def realType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 114#u8, 101#u8, 97#u8, 108#u8] (by simp; scalar_tac)⟩⟩
/-- `owl:rational` -/
def rationalType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 114#u8, 97#u8, 116#u8, 105#u8, 111#u8, 110#u8, 97#u8, 108#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:nonNegativeInteger` -/
def nonNegativeIntegerType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 110#u8, 111#u8, 110#u8, 78#u8, 101#u8, 103#u8, 97#u8, 116#u8, 105#u8, 118#u8, 101#u8, 73#u8, 110#u8, 116#u8, 101#u8, 103#u8, 101#u8, 114#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:nonPositiveInteger` -/
def nonPositiveIntegerType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 110#u8, 111#u8, 110#u8, 80#u8, 111#u8, 115#u8, 105#u8, 116#u8, 105#u8, 118#u8, 101#u8, 73#u8, 110#u8, 116#u8, 101#u8, 103#u8, 101#u8, 114#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:positiveInteger` -/
def positiveIntegerType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 112#u8, 111#u8, 115#u8, 105#u8, 116#u8, 105#u8, 118#u8, 101#u8, 73#u8, 110#u8, 116#u8, 101#u8, 103#u8, 101#u8, 114#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:negativeInteger` -/
def negativeIntegerType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 110#u8, 101#u8, 103#u8, 97#u8, 116#u8, 105#u8, 118#u8, 101#u8, 73#u8, 110#u8, 116#u8, 101#u8, 103#u8, 101#u8, 114#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:long` -/
def longType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 108#u8, 111#u8, 110#u8, 103#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:int` -/
def intType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 105#u8, 110#u8, 116#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:short` -/
def shortType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 115#u8, 104#u8, 111#u8, 114#u8, 116#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:byte` -/
def byteType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 98#u8, 121#u8, 116#u8, 101#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:unsignedLong` -/
def unsignedLongType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 117#u8, 110#u8, 115#u8, 105#u8, 103#u8, 110#u8, 101#u8, 100#u8, 76#u8, 111#u8, 110#u8, 103#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:unsignedInt` -/
def unsignedIntType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 117#u8, 110#u8, 115#u8, 105#u8, 103#u8, 110#u8, 101#u8, 100#u8, 73#u8, 110#u8, 116#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:unsignedShort` -/
def unsignedShortType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 117#u8, 110#u8, 115#u8, 105#u8, 103#u8, 110#u8, 101#u8, 100#u8, 83#u8, 104#u8, 111#u8, 114#u8, 116#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:unsignedByte` -/
def unsignedByteType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 117#u8, 110#u8, 115#u8, 105#u8, 103#u8, 110#u8, 101#u8, 100#u8, 66#u8, 121#u8, 116#u8, 101#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:anyURI` -/
def anyUriType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 97#u8, 110#u8, 121#u8, 85#u8, 82#u8, 73#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:hexBinary` -/
def hexBinaryType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 104#u8, 101#u8, 120#u8, 66#u8, 105#u8, 110#u8, 97#u8, 114#u8, 121#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:base64Binary` -/
def base64BinaryType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 98#u8, 97#u8, 115#u8, 101#u8, 54#u8, 52#u8, 66#u8, 105#u8, 110#u8, 97#u8, 114#u8, 121#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:normalizedString` -/
def normalizedStringType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 110#u8, 111#u8, 114#u8, 109#u8, 97#u8, 108#u8, 105#u8, 122#u8, 101#u8, 100#u8, 83#u8, 116#u8, 114#u8, 105#u8, 110#u8, 103#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:token` -/
def tokenType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 116#u8, 111#u8, 107#u8, 101#u8, 110#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:language` -/
def languageType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 108#u8, 97#u8, 110#u8, 103#u8, 117#u8, 97#u8, 103#u8, 101#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:NMTOKEN` -/
def nmtokenType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 78#u8, 77#u8, 84#u8, 79#u8, 75#u8, 69#u8, 78#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:Name` -/
def nameType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 78#u8, 97#u8, 109#u8, 101#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:NCName` -/
def ncnameType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 78#u8, 67#u8, 78#u8, 97#u8, 109#u8, 101#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:dateTime` -/
def dateTimeType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 100#u8, 97#u8, 116#u8, 101#u8, 84#u8, 105#u8, 109#u8, 101#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:dateTimeStamp` -/
def dateTimeStampType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 100#u8, 97#u8, 116#u8, 101#u8, 84#u8, 105#u8, 109#u8, 101#u8, 83#u8, 116#u8, 97#u8, 109#u8, 112#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:double` -/
def doubleType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 100#u8, 111#u8, 117#u8, 98#u8, 108#u8, 101#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:float` -/
def floatType : Datatype := ⟨⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 102#u8, 108#u8, 111#u8, 97#u8, 116#u8] (by simp; scalar_tac)⟩⟩
/-- `xsd:minInclusive` -/
def minInclusiveFacet : Iri := ⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 109#u8, 105#u8, 110#u8, 73#u8, 110#u8, 99#u8, 108#u8, 117#u8, 115#u8, 105#u8, 118#u8, 101#u8] (by simp; scalar_tac)⟩
/-- `xsd:maxInclusive` -/
def maxInclusiveFacet : Iri := ⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 109#u8, 97#u8, 120#u8, 73#u8, 110#u8, 99#u8, 108#u8, 117#u8, 115#u8, 105#u8, 118#u8, 101#u8] (by simp; scalar_tac)⟩
/-- `xsd:minExclusive` -/
def minExclusiveFacet : Iri := ⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 109#u8, 105#u8, 110#u8, 69#u8, 120#u8, 99#u8, 108#u8, 117#u8, 115#u8, 105#u8, 118#u8, 101#u8] (by simp; scalar_tac)⟩
/-- `xsd:maxExclusive` -/
def maxExclusiveFacet : Iri := ⟨alloc.vec.Vec.from [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 109#u8, 97#u8, 120#u8, 69#u8, 120#u8, 99#u8, 108#u8, 117#u8, 115#u8, 105#u8, 118#u8, 101#u8] (by simp; scalar_tac)⟩

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

/-- `text` is a lexical form `numerator/denominator` of `owl:rational` for the
    number `q` (§4.1): the numerator an integer with the syntax of
    `xsd:integer`, and the denominator a positive integer with the syntax of
    `xsd:integer` without a sign; the number is their quotient. -/
def RationalForm (text : List U8) (q : ℚ) : Prop :=
  ∃ numerator denominator p, text = numerator ++ 47#u8 :: denominator ∧ IntegerForm numerator p ∧
    Digits denominator ∧ 0 < digitsValue denominator ∧ q = p / digitsValue denominator
/-- The integers within optional least and greatest values. -/
def Bounded (lower upper : Option ℤ) (z : ℤ) : Prop :=
  (∀ l, lower = some l → l ≤ z) ∧ (∀ u, upper = some u → z ≤ u)
/-- The integer datatypes of XML Schema below `xsd:integer`, each with the least
    and greatest values of its value space (XML Schema 1.1 Part 2 §3.4). -/
def integerSubtypes : List (Datatype × Option ℤ × Option ℤ) :=
  [(nonNegativeIntegerType, some 0, none), (nonPositiveIntegerType, none, some 0),
   (positiveIntegerType, some 1, none), (negativeIntegerType, none, some (-1)),
   (longType, some (-9223372036854775808), some 9223372036854775807),
   (intType, some (-2147483648), some 2147483647),
   (shortType, some (-32768), some 32767),
   (byteType, some (-128), some 127),
   (unsignedLongType, some 0, some 18446744073709551615),
   (unsignedIntType, some 0, some 4294967295),
   (unsignedShortType, some 0, some 65535),
   (unsignedByteType, some 0, some 255)]
/-- The numeric datatypes of XML Schema here. -/
def xsdNumericTypes : List Datatype := integerType :: decimalType :: integerSubtypes.map (·.1)
/-- The four range facets. -/
def rangeFacets : List Iri := [minInclusiveFacet, maxInclusiveFacet, minExclusiveFacet, maxExclusiveFacet]

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

/-- The values of `xsd:anyURI`, `xsd:hexBinary` and `xsd:base64Binary`: an
    IRI as the UTF-8 bytes of its characters, and the octets of either binary
    datatype, each datatype with a copy of its own (§4.5, §4.6: the binary
    value spaces are disjoint, and IRIs are not strings). -/
inductive Coded where
  | uri (s : List U8)
  | hex (o : List U8)
  | base64 (o : List U8)
deriving DecidableEq

/-- A `Coded` value proper: the bytes of an IRI are XML text. -/
def Coded.Valid : Coded → Prop
  | .uri s => XmlText s
  | .hex _ => True
  | .base64 _ => True

/-- The value of a hexadecimal digit `[0-9a-fA-F]`. -/
def hexDigitValue (byte : U8) : Option Nat :=
  if 48 ≤ byte.val ∧ byte.val ≤ 57 then some (byte.val - 48)
  else if 65 ≤ byte.val ∧ byte.val ≤ 70 then some (byte.val - 55)
  else if 97 ≤ byte.val ∧ byte.val ≤ 102 then some (byte.val - 87)
  else none

/-- `text` is a lexical form `([0-9a-fA-F]{2})*` of `xsd:hexBinary` for the
    octets `o` (XML Schema 1.1 Part 2 §3.3.15): two digits for each octet, the
    first its high half. -/
def HexForm : List U8 → List U8 → Prop
  | [], o => o = []
  | [_], _ => False
  | a :: b :: rest, o => ∃ x y octet o', hexDigitValue a = some x ∧ hexDigitValue b = some y ∧
      o = octet :: o' ∧ octet.val = 16 * x + y ∧ HexForm rest o'

/-- The value of a character of the Base64 alphabet `[A-Za-z0-9+/]`. -/
def base64Value (byte : U8) : Option Nat :=
  if 65 ≤ byte.val ∧ byte.val ≤ 90 then some (byte.val - 65)
  else if 97 ≤ byte.val ∧ byte.val ≤ 122 then some (byte.val - 71)
  else if 48 ≤ byte.val ∧ byte.val ≤ 57 then some (byte.val + 4)
  else if byte.val = 43 then some 62
  else if byte.val = 47 then some 63
  else none

/-- `text` is `chars` with at most one space after each character but the last,
    the spaces that the grammar of `xsd:base64Binary` allows. -/
def Spaced : List U8 → List U8 → Prop
  | text, [] => text = []
  | text, [c] => text = [c]
  | text, c :: d :: cs => ∃ rest, (text = c :: rest ∨ text = c :: 32#u8 :: rest) ∧ Spaced rest (d :: cs)

/-- Base64 groups without spaces that encode the octets `o` (XML Schema 1.1
    Part 2 §3.3.16, RFC 2045): groups of four characters of three octets each,
    the last group possibly `a b c =` with `c` a multiple of four for two octets
    or `a b = =` with `b` a multiple of sixteen for one. -/
def Base64Chars : List U8 → List U8 → Prop
  | [], o => o = []
  | a :: b :: c :: d :: rest, o =>
    ∃ va vb, base64Value a = some va ∧ base64Value b = some vb ∧
      ((∃ vc vd x y z o', base64Value c = some vc ∧ base64Value d = some vd ∧ o = x :: y :: z :: o' ∧
          x.val = va * 4 + vb / 16 ∧ y.val = vb % 16 * 16 + vc / 4 ∧ z.val = vc % 4 * 64 + vd ∧
          Base64Chars rest o') ∨
       (∃ vc x y, rest = [] ∧ base64Value c = some vc ∧ d = 61#u8 ∧ vc % 4 = 0 ∧ o = [x, y] ∧
          x.val = va * 4 + vb / 16 ∧ y.val = vb % 16 * 16 + vc / 4) ∨
       (∃ x, rest = [] ∧ c = 61#u8 ∧ d = 61#u8 ∧ vb % 16 = 0 ∧ o = [x] ∧ x.val = va * 4 + vb / 16))
  | _, _ => False

/-- `text` is a lexical form of `xsd:base64Binary` for the octets `o`. -/
def Base64Form (text o : List U8) : Prop := ∃ chars, Spaced text chars ∧ Base64Chars chars o

/-- XML 1.1 `NameStartChar`, the same in XML 1.0, fifth edition. -/
def NameStartChar (cp : Nat) : Prop :=
  cp = 0x3A ∨ (0x41 ≤ cp ∧ cp ≤ 0x5A) ∨ cp = 0x5F ∨ (0x61 ≤ cp ∧ cp ≤ 0x7A) ∨ (0xC0 ≤ cp ∧ cp ≤ 0xD6) ∨
    (0xD8 ≤ cp ∧ cp ≤ 0xF6) ∨ (0xF8 ≤ cp ∧ cp ≤ 0x2FF) ∨ (0x370 ≤ cp ∧ cp ≤ 0x37D) ∨
    (0x37F ≤ cp ∧ cp ≤ 0x1FFF) ∨ (0x200C ≤ cp ∧ cp ≤ 0x200D) ∨ (0x2070 ≤ cp ∧ cp ≤ 0x218F) ∨
    (0x2C00 ≤ cp ∧ cp ≤ 0x2FEF) ∨ (0x3001 ≤ cp ∧ cp ≤ 0xD7FF) ∨ (0xF900 ≤ cp ∧ cp ≤ 0xFDCF) ∨
    (0xFDF0 ≤ cp ∧ cp ≤ 0xFFFD) ∨ (0x10000 ≤ cp ∧ cp ≤ 0xEFFFF)

/-- XML 1.1 `NameChar`. -/
def NameChar (cp : Nat) : Prop :=
  NameStartChar cp ∨ cp = 0x2D ∨ cp = 0x2E ∨ (0x30 ≤ cp ∧ cp ≤ 0x39) ∨ cp = 0xB7 ∨
    (0x300 ≤ cp ∧ cp ≤ 0x36F) ∨ (0x203F ≤ cp ∧ cp ≤ 0x2040)

/-- `cps` are the code points of the XML characters that `bytes` encode. -/
def TextChars (bytes : List U8) (cps : List Nat) : Prop :=
  ∃ text, Rowl.Unicode.TextFrom bytes 0 text ∧ text.map Prod.fst = cps

/-- An ASCII letter `[a-zA-Z]`. -/
def Letter (byte : U8) : Prop := (65 ≤ byte.val ∧ byte.val ≤ 90) ∨ (97 ≤ byte.val ∧ byte.val ≤ 122)

/-- A subtag of `xsd:language`: one to eight letters, and digits too unless it
    is the first. -/
def Subtag (first : Bool) (subtag : List U8) : Prop :=
  1 ≤ subtag.length ∧ subtag.length ≤ 8 ∧
    ∀ byte ∈ subtag, Letter byte ∨ (first = false ∧ 48 ≤ byte.val ∧ byte.val ≤ 57)

/-- `text` matches `[a-zA-Z]{1,8}(-[a-zA-Z0-9]{1,8})*`. -/
def LanguageForm (text : List U8) : Prop :=
  ∃ (first : List U8) (rest : List (List U8)), Subtag true first ∧ (∀ subtag ∈ rest, Subtag false subtag) ∧
    text = first ++ (rest.map (45#u8 :: ·)).flatten

/-- The six subtypes of `xsd:string` (XML Schema 1.1 Part 2 §3.4). -/
inductive StringSubtype where
  | normalized | token | language | nmtoken | name | ncname
deriving DecidableEq

/-- The datatype of a subtype of `xsd:string`. -/
def StringSubtype.datatype : StringSubtype → Datatype
  | .normalized => normalizedStringType
  | .token => tokenType
  | .language => languageType
  | .nmtoken => nmtokenType
  | .name => nameType
  | .ncname => ncnameType

/-- The lexical forms of a subtype of `xsd:string`, which are also its values
    (§3.4: the lexical space and the value space are the same set of
    strings): no tab, line feed or carriage return in a normalized string; a
    token also without a space first or last or two spaces in a row; a
    language matching its pattern; the strings that match the XML 1.1
    productions `Nmtoken` and `Name`; and the names without `:` for `NCName`
    (Namespaces in XML 1.1). -/
def StringSubtype.Form : StringSubtype → List U8 → Prop
  | .normalized, t => XmlText t ∧ 9#u8 ∉ t ∧ 10#u8 ∉ t ∧ 13#u8 ∉ t
  | .token, t => (XmlText t ∧ 9#u8 ∉ t ∧ 10#u8 ∉ t ∧ 13#u8 ∉ t) ∧ t.head? ≠ some 32#u8 ∧
      t.getLast? ≠ some 32#u8 ∧ ∀ i, t[i]? = some 32#u8 → t[i + 1]? ≠ some 32#u8
  | .language, t => LanguageForm t
  | .nmtoken, t => ∃ cps, TextChars t cps ∧ cps ≠ [] ∧ ∀ c ∈ cps, NameChar c
  | .name, t => ∃ c cps, TextChars t (c :: cps) ∧ NameStartChar c ∧ ∀ c' ∈ cps, NameChar c'
  | .ncname, t => (∃ c cps, TextChars t (c :: cps) ∧ NameStartChar c ∧ ∀ c' ∈ cps, NameChar c') ∧ 58#u8 ∉ t

/-- A time instant of `xsd:dateTime` (XML Schema 1.1 Part 2 §D.2.1, the
    seven-property model): the date and the time as written, and the time zone
    offset in minutes when there is one. Two values of one instant at
    different offsets are different values (OWL 2 Structural Specification
    §4.7: equal, but not identical). -/
structure Moment where
  year : ℤ
  month : ℕ
  day : ℕ
  hour : ℕ
  minute : ℕ
  second : ℚ
  zone : Option ℤ
deriving DecidableEq

/-- A leap year of the proleptic Gregorian calendar, in which year zero is one
    (XML Schema 1.1 Part 2 §D.3.2, ·daysInMonth·). -/
def leapYear (year : ℤ) : Bool := year % 400 = 0 || (year % 4 = 0 && year % 100 ≠ 0)

/-- The number of days of a month in a year. -/
def daysIn (year : ℤ) (month : ℕ) : ℕ :=
  if month = 2 then (if leapYear year then 29 else 28)
  else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31

/-- A time instant proper: a month of the year, a day of the month, an hour of
    the day, a minute of the hour, seconds a decimal number below 60, and an
    offset of at most fourteen hours. -/
def Moment.Valid (m : Moment) : Prop :=
  1 ≤ m.month ∧ m.month ≤ 12 ∧ 1 ≤ m.day ∧ m.day ≤ daysIn m.year m.month ∧ m.hour < 24 ∧ m.minute < 60 ∧
    0 ≤ m.second ∧ m.second < 60 ∧ IsDecimal m.second ∧ ∀ z, m.zone = some z → -840 ≤ z ∧ z ≤ 840

/-- `text` is two digits that write `n`. -/
def TwoDigits (text : List U8) (n : ℕ) : Prop := text.length = 2 ∧ Digits text ∧ n = digitsValue text

/-- `text` is a year `-?([1-9][0-9]{3,}|0[0-9]{3})` that writes `year`. -/
def YearForm (text : List U8) (year : ℤ) : Prop :=
  ∃ (negative : Bool) (digits : List U8), text = (if negative then [45#u8] else []) ++ digits ∧ Digits digits ∧
    4 ≤ digits.length ∧ (4 < digits.length → digits.head? ≠ some 48#u8) ∧
    year = (if negative then -1 else 1) * (digitsValue digits : ℤ)

/-- `text` is a time zone `Z` or `(+|-)hh:mm` of at most fourteen hours that
    writes the offset `zone` in minutes. -/
def ZoneForm (text : List U8) (zone : ℤ) : Prop :=
  (text = [90#u8] ∧ zone = 0) ∨
  ∃ (west : Bool) (hh mm : List U8) (h m : ℕ), text = (if west then 45#u8 else 43#u8) :: hh ++ 58#u8 :: mm ∧
    TwoDigits hh h ∧ TwoDigits mm m ∧ ((h ≤ 13 ∧ m ≤ 59) ∨ (h = 14 ∧ m = 0)) ∧
    zone = (if west then -1 else 1) * ((60 * h + m : ℕ) : ℤ)

/-- The value of the digits of a fraction of a second. -/
def fractionValue (digits : List U8) : ℚ := (digitsValue digits : ℚ) / 10 ^ digits.length

/-- The day after a date. -/
def nextDate (year : ℤ) (month day : ℕ) : ℤ × ℕ × ℕ :=
  if day < daysIn year month then (year, month, day + 1)
  else if month < 12 then (year, month + 1, 1) else (year + 1, 1, 1)

/-- The days of the months of a year before a month. -/
def daysBefore (year : ℤ) (month : ℕ) : ℕ := ((List.range (month - 1)).map fun k => daysIn year (k + 1)).sum

/-- The place of a moment on the time line in seconds (XML Schema 1.1 Part 2
    §E.3.4, ·timeOnTimeline·): the days of the years before its year in the
    proleptic Gregorian calendar, of the months before its month and of the
    days before its day, its time of the day, and its time zone offset taken
    away; a moment without a time zone is placed as at UTC. -/
def Moment.key (m : Moment) : ℚ :=
  ((31536000 * (m.year - 1) + 86400 * ((m.year - 1) / 400 - (m.year - 1) / 100 + (m.year - 1) / 4) +
    86400 * (daysBefore m.year m.month : ℤ) + 86400 * ((m.day : ℤ) - 1) + 3600 * (m.hour : ℤ) +
    60 * ((m.minute : ℤ) - m.zone.getD 0) : ℤ) : ℚ) + m.second

/-- `a` is before `b` in the order of XML Schema 1.1 (Part 2 §D.2.1, OWL 2
    Structural Specification §4.7): by their places on the time line when both
    have a time zone or neither has, and otherwise only when it is so for
    every offset the one without a time zone could have, -14:00 to +14:00. -/
def Moment.Lt (a b : Moment) : Prop :=
  (a.zone.isSome = b.zone.isSome ∧ a.key < b.key) ∨
    (a.zone.isSome = true ∧ b.zone = none ∧ a.key < b.key - 50400) ∨
    (a.zone = none ∧ b.zone.isSome = true ∧ a.key + 50400 < b.key)

/-- `a` and `b` are equal in the order of XML Schema: at one place on the time
    line, both with a time zone or both without one. Equal values with
    different offsets are still different values. -/
def Moment.Same (a b : Moment) : Prop := a.zone.isSome = b.zone.isSome ∧ a.key = b.key

/-- `a` is at or before `b`. -/
def Moment.Le (a b : Moment) : Prop := a.Lt b ∨ a.Same b

/-- `text` is a lexical form of `xsd:dateTime` for the moment `m` (XML Schema
    1.1 Part 2 §3.3.7): a year, `-`, a month, `-`, a day of the month, `T`, a
    time `hh:mm:ss` with an optional fraction `.d+` of a second, and an optional
    time zone. The value is the date and the time as written when the hours are
    below 24 and the minutes and seconds below 60, and `24:00:00` with a
    fraction of zero is the first instant of the next day. -/
def MomentForm (text : List U8) (m : Moment) : Prop :=
  ∃ (yearText mm dd hh mi ss fraction zoneText : List U8) (year : ℤ) (month day hour minute second : ℕ)
    (zone : Option ℤ),
    text = yearText ++ 45#u8 :: mm ++ 45#u8 :: dd ++ 84#u8 :: hh ++ 58#u8 :: mi ++ 58#u8 :: ss ++
      (if fraction = [] then [] else 46#u8 :: fraction) ++ zoneText ∧
    YearForm yearText year ∧ TwoDigits mm month ∧ 1 ≤ month ∧ month ≤ 12 ∧ TwoDigits dd day ∧ 1 ≤ day ∧
    day ≤ daysIn year month ∧ TwoDigits hh hour ∧ TwoDigits mi minute ∧ TwoDigits ss second ∧ Digits fraction ∧
    ((zoneText = [] ∧ zone = none) ∨ ∃ z, ZoneForm zoneText z ∧ zone = some z) ∧
    ((hour < 24 ∧ minute < 60 ∧ second < 60 ∧
        m = ⟨year, month, day, hour, minute, second + fractionValue fraction, zone⟩) ∨
     (hour = 24 ∧ minute = 0 ∧ second = 0 ∧ fractionValue fraction = 0 ∧
        m = ⟨(nextDate year month day).1, (nextDate year month day).2.1, (nextDate year month day).2.2, 0, 0, 0,
          zone⟩))

/-- A floating-point format of XML Schema (§3.3.4, §3.3.5): the digits of the
    significand and the least and the greatest exponent of 2. -/
structure FloatFormat where
  precision : ℕ
  least : ℤ
  most : ℤ

/-- The format of `xsd:double`. -/
def doubleFormat : FloatFormat := ⟨53, -1074, 971⟩
/-- The format of `xsd:float`. -/
def floatFormat : FloatFormat := ⟨24, -149, 104⟩

/-- A value of `xsd:double` or `xsd:float` (XML Schema 1.1 Part 2 §3.3.5): a
    nonzero number, a zero with its sign, an infinity with its sign, or NaN.
    The two zeros are different values, equal but not identical (OWL 2
    Structural Specification §4.2), and NaN is one value. -/
inductive Binary where
  | finite (value : ℚ)
  | zero (negative : Bool)
  | infinity (negative : Bool)
  | nan
deriving DecidableEq

/-- A value of the format: a nonzero number is `m × 2^e` with `0 < |m| < 2^p`
    and an exponent between the least and the greatest. -/
def Binary.Valid (f : FloatFormat) : Binary → Prop
  | .finite q => ∃ (m e : ℤ), q = m * (2 : ℚ) ^ e ∧ 0 < abs m ∧ abs m < 2 ^ f.precision ∧ f.least ≤ e ∧ e ≤ f.most
  | _ => True

/-- The place of a value in the order of XML Schema 1.1 on the values of
    `xsd:double` and `xsd:float` (Part 2 §3.3.4.1 and §3.3.5.1): a number at its
    value, both zeros at zero, and the infinities at the ends of the extended
    real line; NaN has no place, so that it is comparable to no value, itself
    included. -/
noncomputable def Binary.key : Binary → Option EReal
  | .finite q => some ((q : ℝ) : EReal)
  | .zero _ => some 0
  | .infinity negative => some (if negative then ⊥ else ⊤)
  | .nan => none

/-- `a` is at or below `b` in the order of XML Schema: the two zeros are equal,
    and NaN is neither. -/
def Binary.Le (a b : Binary) : Prop := ∃ x y, a.key = some x ∧ b.key = some y ∧ x ≤ y

/-- `a` is below `b` in the order of XML Schema. -/
def Binary.Lt (a b : Binary) : Prop := ∃ x y, a.key = some x ∧ b.key = some y ∧ x < y

/-- `floatingPointRound` of XML Schema 1.1 Part 2 (§E.1.1, the auxiliary
    functions for binary floating-point lexical mappings) for a nonzero
    number: the exponent `e` with `2^(p−1) ≤ |v| / 2^e < 2^p`, or the least
    exponent where that is below it, and an infinity above the greatest;
    otherwise the nearer of the multiples of `2^e` around `|v|`, at a tie the
    one with the even quotient, a zero when that is zero, and an infinity when
    it is `2^p × 2^eMax` or more. -/
noncomputable def roundBinary (f : FloatFormat) (v : ℚ) : Binary :=
  if f.most < Int.log 2 (abs v) - f.precision + 1 then .infinity (decide (v < 0))
  else
    let e := max (Int.log 2 (abs v) - f.precision + 1) f.least
    let c := Int.floor (abs v / (2 : ℚ) ^ e) + 1
    let middle := c * (2 : ℚ) ^ e - (2 : ℚ) ^ (e - 1)
    let n : ℚ := if middle < abs v then c * (2 : ℚ) ^ e else if abs v < middle then (c - 1) * (2 : ℚ) ^ e
      else if c % 2 = 0 then c * (2 : ℚ) ^ e else (c - 1) * (2 : ℚ) ^ e
    if n = 0 then .zero (decide (v < 0))
    else if n < (2 : ℚ) ^ f.precision * (2 : ℚ) ^ f.most then .finite (if v < 0 then -n else n)
    else .infinity (decide (v < 0))

/-- `text` is an optional sign, `+` or `-`: negative for `-`. -/
def SignForm (text : List U8) (negative : Bool) : Prop :=
  (text = [] ∧ negative = false) ∨ (text = [43#u8] ∧ negative = false) ∨ (text = [45#u8] ∧ negative = true)

/-- `text` is an unsigned decimal numeral `[0-9]+(\.[0-9]*)?|\.[0-9]+` whose
    digits without the point are `digits`, `places` of them after the point. -/
def UnsignedForm (text digits : List U8) (places : ℕ) : Prop :=
  ∃ whole fraction, Digits whole ∧ Digits fraction ∧ digits = whole ++ fraction ∧ places = fraction.length ∧
    ((text = whole ∧ whole ≠ [] ∧ fraction = []) ∨ (text = whole ++ 46#u8 :: fraction ∧ (whole ≠ [] ∨ fraction ≠ [])))

/-- `text` is an optional exponent `[Ee](\+|-)?[0-9]+` that writes `x`, or
    nothing for 0. -/
def ExponentForm (text : List U8) (x : ℤ) : Prop :=
  (text = [] ∧ x = 0) ∨ ∃ (mark : U8) (sign digits : List U8) (negative : Bool),
    (mark = 69#u8 ∨ mark = 101#u8) ∧ SignForm sign negative ∧ Digits digits ∧ digits ≠ [] ∧
    text = mark :: sign ++ digits ∧ x = (if negative then -1 else 1) * (digitsValue digits : ℤ)

/-- `text` is a numeral of `xsd:double` and `xsd:float` (§3.3.5.2:
    `(\+|-)?([0-9]+(\.[0-9]*)?|\.[0-9]+)([Ee](\+|-)?[0-9]+)?`), negative after
    `-`, for the decimal number `v`. -/
def NumeralForm (text : List U8) (negative : Bool) (v : ℚ) : Prop :=
  ∃ sign unsigned exponent digits places x, text = sign ++ unsigned ++ exponent ∧ SignForm sign negative ∧
    UnsignedForm unsigned digits places ∧ ExponentForm exponent x ∧
    v = (if negative then -1 else 1) * (digitsValue digits : ℚ) * (10 : ℚ) ^ (x - places)

/-- `text` is a lexical form of the format for the value `b` (§3.3.4.2 and
    §3.3.5.2, `floatLexicalMap` and `doubleLexicalMap`): `INF` or `+INF`,
    `-INF` and `NaN` for the special values, a numeral of zero for the zero of
    its sign, and a numeral of another number for its rounding. -/
def BinaryForm (f : FloatFormat) (text : List U8) (b : Binary) : Prop :=
  ((text = [73#u8, 78#u8, 70#u8] ∨ text = [43#u8, 73#u8, 78#u8, 70#u8]) ∧ b = .infinity false) ∨
  (text = [45#u8, 73#u8, 78#u8, 70#u8] ∧ b = .infinity true) ∨
  (text = [78#u8, 97#u8, 78#u8] ∧ b = .nan) ∨
  ∃ negative v, NumeralForm text negative v ∧ ((v = 0 ∧ b = .zero negative) ∨ (v ≠ 0 ∧ b = roundBinary f v))

/-- A datatype map that is the OWL 2 datatype map on the datatypes here: they
    are supported, with these lexical spaces and lexical-to-value mappings; a
    number is the image of a real number, the rationals' images agreeing with
    `number`, a string or a pair of a string and a lower-case language tag the
    image of its bytes, and a truth value the image of a Boolean, injectively on
    the values; the value spaces are the real numbers, the rationals, the
    decimal numbers, the integers and the integers within each subtype's
    bounds, the strings, the strings with or without a language tag and the two
    truth values; numbers, plain literals and truth values are pairwise
    different; the facet spaces of the numeric datatypes are the four range
    facets with every real (`owl:real`, `owl:rational`) or every value of the
    datatype (XML Schema) as constraining value; the facet value of a range
    facet with a real constraining value is the set of reals on its side; and
    the values of `xsd:anyURI` (the XML texts, with the identity as lexical
    mapping), `xsd:hexBinary` and `xsd:base64Binary` (the octet sequences) are
    the images of their `Coded` values, injectively and apart from the
    numbers, plain literals and truth values; each subtype of `xsd:string`
    has the strings of its lexical forms as values, each the value of its own
    form; and the values of `xsd:dateTime` are the images of the valid moments,
    injectively and apart from every other value, those of
    `xsd:dateTimeStamp` the images of the moments with a time zone, and each
    lexical form has the value of its moment, and their facet spaces are the
    four range facets with a time instant as constraining value, one with a
    time zone for `xsd:dateTimeStamp`, whose facet values are the time
    instants on the facet's side of it in the order of XML Schema
    (`Moment.Le`, `Moment.Lt`); and the values of `xsd:double`
    and `xsd:float` are the images of the values of their formats, injectively,
    the two datatypes apart from each other and from every other value
    (OWL 2 Structural Specification §4.2), each lexical form with the value
    that `BinaryForm` gives it, and their facet spaces the four range facets
    with a value of the datatype as constraining value, whose facet values
    are the datatype's values on the facet's side of it in the order of XML
    Schema (`Binary.Le`, `Binary.Lt`). -/
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
  real : ℝ → Native
  real_injective : Function.Injective real
  real_number : ∀ q : ℚ, real q = number q
  real_text : ∀ r s, XmlText s → real r ≠ text s
  real_tagged : ∀ r s l, XmlText s → TagValue l → real r ≠ tagged s l
  real_truth : ∀ r b, real r ≠ truth b
  real_supported : D.supported realType
  rational_supported : D.supported rationalType
  subtype_supported : ∀ s ∈ integerSubtypes, D.supported s.1
  real_space : ∀ x, D.valueSpace realType x ↔ ∃ r, x = real r
  rational_space : ∀ x, D.valueSpace rationalType x ↔ ∃ q : ℚ, x = number q
  subtype_space : ∀ s ∈ integerSubtypes, ∀ x,
    D.valueSpace s.1 x ↔ ∃ z : ℤ, Bounded s.2.1 s.2.2 z ∧ x = number (z : ℚ)
  real_lexical : ∀ t, ¬ D.lexicalSpace realType t
  rational_lexical : ∀ t, D.lexicalSpace rationalType t ↔ ∃ q, RationalForm t q
  rational_value : ∀ t q, RationalForm t q → D.lexicalValue rationalType t = number q
  subtype_lexical : ∀ s ∈ integerSubtypes, ∀ t,
    D.lexicalSpace s.1 t ↔ ∃ z : ℤ, Bounded s.2.1 s.2.2 z ∧ IntegerForm t (z : ℚ)
  subtype_value : ∀ s ∈ integerSubtypes, ∀ t (z : ℤ), Bounded s.2.1 s.2.2 z → IntegerForm t (z : ℚ) →
    D.lexicalValue s.1 t = number (z : ℚ)
  real_facets : ∀ f v, D.facetSpace realType f v ↔ f ∈ rangeFacets ∧ ∃ r, v = real r
  rational_facets : ∀ f v, D.facetSpace rationalType f v ↔ f ∈ rangeFacets ∧ ∃ r, v = real r
  xsd_facets : ∀ dt ∈ xsdNumericTypes, ∀ f v, D.facetSpace dt f v ↔ f ∈ rangeFacets ∧ D.valueSpace dt v
  min_inclusive_value : ∀ r y, D.facetValue minInclusiveFacet (real r) y ↔ ∃ s, r ≤ s ∧ y = real s
  max_inclusive_value : ∀ r y, D.facetValue maxInclusiveFacet (real r) y ↔ ∃ s, s ≤ r ∧ y = real s
  min_exclusive_value : ∀ r y, D.facetValue minExclusiveFacet (real r) y ↔ ∃ s, r < s ∧ y = real s
  max_exclusive_value : ∀ r y, D.facetValue maxExclusiveFacet (real r) y ↔ ∃ s, s < r ∧ y = real s
  coded : Coded → Native
  coded_injective : ∀ a b, a.Valid → b.Valid → coded a = coded b → a = b
  real_coded : ∀ r a, a.Valid → real r ≠ coded a
  text_coded : ∀ s a, XmlText s → a.Valid → text s ≠ coded a
  tagged_coded : ∀ s l a, XmlText s → TagValue l → a.Valid → tagged s l ≠ coded a
  truth_coded : ∀ b a, a.Valid → truth b ≠ coded a
  uri_supported : D.supported anyUriType
  hex_supported : D.supported hexBinaryType
  base64_supported : D.supported base64BinaryType
  uri_space : ∀ x, D.valueSpace anyUriType x ↔ ∃ s, XmlText s ∧ x = coded (.uri s)
  hex_space : ∀ x, D.valueSpace hexBinaryType x ↔ ∃ o, x = coded (.hex o)
  base64_space : ∀ x, D.valueSpace base64BinaryType x ↔ ∃ o, x = coded (.base64 o)
  uri_lexical : ∀ t, D.lexicalSpace anyUriType t ↔ XmlText t
  uri_value : ∀ t, XmlText t → D.lexicalValue anyUriType t = coded (.uri t)
  hex_lexical : ∀ t, D.lexicalSpace hexBinaryType t ↔ ∃ o, HexForm t o
  hex_value : ∀ t o, HexForm t o → D.lexicalValue hexBinaryType t = coded (.hex o)
  base64_lexical : ∀ t, D.lexicalSpace base64BinaryType t ↔ ∃ o, Base64Form t o
  base64_value : ∀ t o, Base64Form t o → D.lexicalValue base64BinaryType t = coded (.base64 o)
  string_subtype_supported : ∀ s : StringSubtype, D.supported s.datatype
  string_subtype_space : ∀ (s : StringSubtype) x, D.valueSpace s.datatype x ↔ ∃ t, s.Form t ∧ x = text t
  string_subtype_lexical : ∀ (s : StringSubtype) t, D.lexicalSpace s.datatype t ↔ s.Form t
  string_subtype_value : ∀ (s : StringSubtype) t, s.Form t → D.lexicalValue s.datatype t = text t
  moment : Moment → Native
  moment_injective : ∀ a b, a.Valid → b.Valid → moment a = moment b → a = b
  real_moment : ∀ r a, a.Valid → real r ≠ moment a
  text_moment : ∀ s a, XmlText s → a.Valid → text s ≠ moment a
  tagged_moment : ∀ s l a, XmlText s → TagValue l → a.Valid → tagged s l ≠ moment a
  truth_moment : ∀ b a, a.Valid → truth b ≠ moment a
  coded_moment : ∀ c a, c.Valid → a.Valid → coded c ≠ moment a
  datetime_supported : D.supported dateTimeType
  stamp_supported : D.supported dateTimeStampType
  datetime_space : ∀ x, D.valueSpace dateTimeType x ↔ ∃ m, m.Valid ∧ x = moment m
  stamp_space : ∀ x, D.valueSpace dateTimeStampType x ↔ ∃ m, m.Valid ∧ m.zone ≠ none ∧ x = moment m
  datetime_lexical : ∀ t, D.lexicalSpace dateTimeType t ↔ ∃ m, MomentForm t m
  datetime_value : ∀ t m, MomentForm t m → D.lexicalValue dateTimeType t = moment m
  stamp_lexical : ∀ t, D.lexicalSpace dateTimeStampType t ↔ ∃ m, MomentForm t m ∧ m.zone ≠ none
  stamp_value : ∀ t m, MomentForm t m → m.zone ≠ none → D.lexicalValue dateTimeStampType t = moment m
  datetime_facets : ∀ f v, D.facetSpace dateTimeType f v ↔ f ∈ rangeFacets ∧ ∃ m, m.Valid ∧ v = moment m
  stamp_facets : ∀ f v, D.facetSpace dateTimeStampType f v ↔
    f ∈ rangeFacets ∧ ∃ m, m.Valid ∧ m.zone ≠ none ∧ v = moment m
  min_inclusive_moment : ∀ b y, b.Valid →
    (D.facetValue minInclusiveFacet (moment b) y ↔ ∃ x, x.Valid ∧ b.Le x ∧ y = moment x)
  max_inclusive_moment : ∀ b y, b.Valid →
    (D.facetValue maxInclusiveFacet (moment b) y ↔ ∃ x, x.Valid ∧ x.Le b ∧ y = moment x)
  min_exclusive_moment : ∀ b y, b.Valid →
    (D.facetValue minExclusiveFacet (moment b) y ↔ ∃ x, x.Valid ∧ b.Lt x ∧ y = moment x)
  max_exclusive_moment : ∀ b y, b.Valid →
    (D.facetValue maxExclusiveFacet (moment b) y ↔ ∃ x, x.Valid ∧ x.Lt b ∧ y = moment x)
  double : Binary → Native
  float : Binary → Native
  double_injective : ∀ a b, a.Valid doubleFormat → b.Valid doubleFormat → double a = double b → a = b
  float_injective : ∀ a b, a.Valid floatFormat → b.Valid floatFormat → float a = float b → a = b
  double_float : ∀ a b, a.Valid doubleFormat → b.Valid floatFormat → double a ≠ float b
  real_double : ∀ r a, a.Valid doubleFormat → real r ≠ double a
  real_float : ∀ r a, a.Valid floatFormat → real r ≠ float a
  text_double : ∀ s a, XmlText s → a.Valid doubleFormat → text s ≠ double a
  text_float : ∀ s a, XmlText s → a.Valid floatFormat → text s ≠ float a
  tagged_double : ∀ s l a, XmlText s → TagValue l → a.Valid doubleFormat → tagged s l ≠ double a
  tagged_float : ∀ s l a, XmlText s → TagValue l → a.Valid floatFormat → tagged s l ≠ float a
  truth_double : ∀ b a, a.Valid doubleFormat → truth b ≠ double a
  truth_float : ∀ b a, a.Valid floatFormat → truth b ≠ float a
  coded_double : ∀ c a, c.Valid → a.Valid doubleFormat → coded c ≠ double a
  coded_float : ∀ c a, c.Valid → a.Valid floatFormat → coded c ≠ float a
  moment_double : ∀ m a, m.Valid → a.Valid doubleFormat → moment m ≠ double a
  moment_float : ∀ m a, m.Valid → a.Valid floatFormat → moment m ≠ float a
  double_supported : D.supported doubleType
  float_supported : D.supported floatType
  double_space : ∀ x, D.valueSpace doubleType x ↔ ∃ b, b.Valid doubleFormat ∧ x = double b
  float_space : ∀ x, D.valueSpace floatType x ↔ ∃ b, b.Valid floatFormat ∧ x = float b
  double_lexical : ∀ t, D.lexicalSpace doubleType t ↔ ∃ b, BinaryForm doubleFormat t b
  double_value : ∀ t b, BinaryForm doubleFormat t b → D.lexicalValue doubleType t = double b
  float_lexical : ∀ t, D.lexicalSpace floatType t ↔ ∃ b, BinaryForm floatFormat t b
  float_value : ∀ t b, BinaryForm floatFormat t b → D.lexicalValue floatType t = float b
  double_facets : ∀ f v, D.facetSpace doubleType f v ↔ f ∈ rangeFacets ∧ ∃ b, b.Valid doubleFormat ∧ v = double b
  float_facets : ∀ f v, D.facetSpace floatType f v ↔ f ∈ rangeFacets ∧ ∃ b, b.Valid floatFormat ∧ v = float b
  min_inclusive_double : ∀ b y, b.Valid doubleFormat →
    (D.facetValue minInclusiveFacet (double b) y ↔ ∃ x, x.Valid doubleFormat ∧ b.Le x ∧ y = double x)
  max_inclusive_double : ∀ b y, b.Valid doubleFormat →
    (D.facetValue maxInclusiveFacet (double b) y ↔ ∃ x, x.Valid doubleFormat ∧ x.Le b ∧ y = double x)
  min_exclusive_double : ∀ b y, b.Valid doubleFormat →
    (D.facetValue minExclusiveFacet (double b) y ↔ ∃ x, x.Valid doubleFormat ∧ b.Lt x ∧ y = double x)
  max_exclusive_double : ∀ b y, b.Valid doubleFormat →
    (D.facetValue maxExclusiveFacet (double b) y ↔ ∃ x, x.Valid doubleFormat ∧ x.Lt b ∧ y = double x)
  min_inclusive_float : ∀ b y, b.Valid floatFormat →
    (D.facetValue minInclusiveFacet (float b) y ↔ ∃ x, x.Valid floatFormat ∧ b.Le x ∧ y = float x)
  max_inclusive_float : ∀ b y, b.Valid floatFormat →
    (D.facetValue maxInclusiveFacet (float b) y ↔ ∃ x, x.Valid floatFormat ∧ x.Le b ∧ y = float x)
  min_exclusive_float : ∀ b y, b.Valid floatFormat →
    (D.facetValue minExclusiveFacet (float b) y ↔ ∃ x, x.Valid floatFormat ∧ b.Lt x ∧ y = float x)
  max_exclusive_float : ∀ b y, b.Valid floatFormat →
    (D.facetValue maxExclusiveFacet (float b) y ↔ ∃ x, x.Valid floatFormat ∧ x.Lt b ∧ y = float x)

end Rowl.DatatypeMap
