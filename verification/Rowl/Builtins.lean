import Rowl.Typing
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Rowl.Builtins
open Aeneas Aeneas.Std RowlRust.builtins RowlRust.typing
private def entries_0 : List (List U8 × EntityKind) := [
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 84#u8, 104#u8, 105#u8, 110#u8, 103#u8], .Class),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 78#u8, 111#u8, 116#u8, 104#u8, 105#u8, 110#u8, 103#u8], .Class),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 116#u8, 111#u8, 112#u8, 79#u8, 98#u8, 106#u8, 101#u8, 99#u8, 116#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8], .ObjectProperty),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 98#u8, 111#u8, 116#u8, 116#u8, 111#u8, 109#u8, 79#u8, 98#u8, 106#u8, 101#u8, 99#u8, 116#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8], .ObjectProperty),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 116#u8, 111#u8, 112#u8, 68#u8, 97#u8, 116#u8, 97#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8], .DataProperty),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 98#u8, 111#u8, 116#u8, 116#u8, 111#u8, 109#u8, 68#u8, 97#u8, 116#u8, 97#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8], .DataProperty),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 48#u8, 47#u8, 48#u8, 49#u8, 47#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 76#u8, 105#u8, 116#u8, 101#u8, 114#u8, 97#u8, 108#u8], .Datatype)
  ]
private def entries_1 : List (List U8 × EntityKind) := [
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 114#u8, 101#u8, 97#u8, 108#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 114#u8, 97#u8, 116#u8, 105#u8, 111#u8, 110#u8, 97#u8, 108#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 100#u8, 101#u8, 99#u8, 105#u8, 109#u8, 97#u8, 108#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 105#u8, 110#u8, 116#u8, 101#u8, 103#u8, 101#u8, 114#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 110#u8, 111#u8, 110#u8, 78#u8, 101#u8, 103#u8, 97#u8, 116#u8, 105#u8, 118#u8, 101#u8, 73#u8, 110#u8, 116#u8, 101#u8, 103#u8, 101#u8, 114#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 110#u8, 111#u8, 110#u8, 80#u8, 111#u8, 115#u8, 105#u8, 116#u8, 105#u8, 118#u8, 101#u8, 73#u8, 110#u8, 116#u8, 101#u8, 103#u8, 101#u8, 114#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 112#u8, 111#u8, 115#u8, 105#u8, 116#u8, 105#u8, 118#u8, 101#u8, 73#u8, 110#u8, 116#u8, 101#u8, 103#u8, 101#u8, 114#u8], .Datatype)
  ]
private def entries_2 : List (List U8 × EntityKind) := [
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 110#u8, 101#u8, 103#u8, 97#u8, 116#u8, 105#u8, 118#u8, 101#u8, 73#u8, 110#u8, 116#u8, 101#u8, 103#u8, 101#u8, 114#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 108#u8, 111#u8, 110#u8, 103#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 105#u8, 110#u8, 116#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 115#u8, 104#u8, 111#u8, 114#u8, 116#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 98#u8, 121#u8, 116#u8, 101#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 117#u8, 110#u8, 115#u8, 105#u8, 103#u8, 110#u8, 101#u8, 100#u8, 76#u8, 111#u8, 110#u8, 103#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 117#u8, 110#u8, 115#u8, 105#u8, 103#u8, 110#u8, 101#u8, 100#u8, 73#u8, 110#u8, 116#u8], .Datatype)
  ]
private def entries_3 : List (List U8 × EntityKind) := [
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 117#u8, 110#u8, 115#u8, 105#u8, 103#u8, 110#u8, 101#u8, 100#u8, 83#u8, 104#u8, 111#u8, 114#u8, 116#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 117#u8, 110#u8, 115#u8, 105#u8, 103#u8, 110#u8, 101#u8, 100#u8, 66#u8, 121#u8, 116#u8, 101#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 100#u8, 111#u8, 117#u8, 98#u8, 108#u8, 101#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 102#u8, 108#u8, 111#u8, 97#u8, 116#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 115#u8, 116#u8, 114#u8, 105#u8, 110#u8, 103#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 110#u8, 111#u8, 114#u8, 109#u8, 97#u8, 108#u8, 105#u8, 122#u8, 101#u8, 100#u8, 83#u8, 116#u8, 114#u8, 105#u8, 110#u8, 103#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 116#u8, 111#u8, 107#u8, 101#u8, 110#u8], .Datatype)
  ]
private def entries_4 : List (List U8 × EntityKind) := [
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 108#u8, 97#u8, 110#u8, 103#u8, 117#u8, 97#u8, 103#u8, 101#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 78#u8, 97#u8, 109#u8, 101#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 78#u8, 67#u8, 78#u8, 97#u8, 109#u8, 101#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 78#u8, 77#u8, 84#u8, 79#u8, 75#u8, 69#u8, 78#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 98#u8, 111#u8, 111#u8, 108#u8, 101#u8, 97#u8, 110#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 104#u8, 101#u8, 120#u8, 66#u8, 105#u8, 110#u8, 97#u8, 114#u8, 121#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 98#u8, 97#u8, 115#u8, 101#u8, 54#u8, 52#u8, 66#u8, 105#u8, 110#u8, 97#u8, 114#u8, 121#u8], .Datatype)
  ]
private def entries_5 : List (List U8 × EntityKind) := [
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 97#u8, 110#u8, 121#u8, 85#u8, 82#u8, 73#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 100#u8, 97#u8, 116#u8, 101#u8, 84#u8, 105#u8, 109#u8, 101#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 100#u8, 97#u8, 116#u8, 101#u8, 84#u8, 105#u8, 109#u8, 101#u8, 83#u8, 116#u8, 97#u8, 109#u8, 112#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 80#u8, 108#u8, 97#u8, 105#u8, 110#u8, 76#u8, 105#u8, 116#u8, 101#u8, 114#u8, 97#u8, 108#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 88#u8, 77#u8, 76#u8, 76#u8, 105#u8, 116#u8, 101#u8, 114#u8, 97#u8, 108#u8], .Datatype),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 48#u8, 47#u8, 48#u8, 49#u8, 47#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 108#u8, 97#u8, 98#u8, 101#u8, 108#u8], .AnnotationProperty),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 48#u8, 47#u8, 48#u8, 49#u8, 47#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 99#u8, 111#u8, 109#u8, 109#u8, 101#u8, 110#u8, 116#u8], .AnnotationProperty)
  ]
private def entries_6 : List (List U8 × EntityKind) := [
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 48#u8, 47#u8, 48#u8, 49#u8, 47#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 115#u8, 101#u8, 101#u8, 65#u8, 108#u8, 115#u8, 111#u8], .AnnotationProperty),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 48#u8, 47#u8, 48#u8, 49#u8, 47#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 105#u8, 115#u8, 68#u8, 101#u8, 102#u8, 105#u8, 110#u8, 101#u8, 100#u8, 66#u8, 121#u8], .AnnotationProperty),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 100#u8, 101#u8, 112#u8, 114#u8, 101#u8, 99#u8, 97#u8, 116#u8, 101#u8, 100#u8], .AnnotationProperty),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 118#u8, 101#u8, 114#u8, 115#u8, 105#u8, 111#u8, 110#u8, 73#u8, 110#u8, 102#u8, 111#u8], .AnnotationProperty),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 112#u8, 114#u8, 105#u8, 111#u8, 114#u8, 86#u8, 101#u8, 114#u8, 115#u8, 105#u8, 111#u8, 110#u8], .AnnotationProperty),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 98#u8, 97#u8, 99#u8, 107#u8, 119#u8, 97#u8, 114#u8, 100#u8, 67#u8, 111#u8, 109#u8, 112#u8, 97#u8, 116#u8, 105#u8, 98#u8, 108#u8, 101#u8, 87#u8, 105#u8, 116#u8, 104#u8], .AnnotationProperty),
  ([104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 105#u8, 110#u8, 99#u8, 111#u8, 109#u8, 112#u8, 97#u8, 116#u8, 105#u8, 98#u8, 108#u8, 101#u8, 87#u8, 105#u8, 116#u8, 104#u8], .AnnotationProperty)
  ]
/-- Independent finite declaration-role table reviewed against the normative vocabulary. -/
def entities : List (List U8 × EntityKind) := entries_0 ++ entries_1 ++ entries_2 ++ entries_3 ++ entries_4 ++ entries_5 ++ entries_6
private def lookup (key : List U8) (entries : List (List U8 × EntityKind)) : Option EntityKind :=
  (entries.find? (fun entry => decide (key = entry.1))).map Prod.snd
def role (key : List U8) : Option EntityKind := lookup key entities
private theorem lookup_append (key : List U8) (left right : List (List U8 × EntityKind)) :
    lookup key (left ++ right) = match lookup key left with | some kind => some kind | none => lookup key right := by
  simp only [lookup, List.find?_append]
  cases left.find? (fun entry => decide (key = entry.1)) <;> simp

private theorem equal_correct (key : alloc.vec.Vec U8) (pattern : Slice U8)
    (equalLength : key.val.length = pattern.val.length) (index : Usize) :
    equal_from key pattern index = .ok (decide (key.val.drop index.val = pattern.val.drop index.val)) := by
  rw [equal_from]
  by_cases h : index.val < key.val.length
  · have hr : index.val < pattern.val.length := by omega
    have hkIndex : key.index_usize index = .ok key.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    have hpIndex : pattern.index_usize index = .ok pattern.val[index.val] := by
      simp [Slice.index_usize, List.getElem?_eq_getElem hr]
    by_cases heads : key.val[index.val] = pattern.val[index.val]
    · have size := key.property
      obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have ih := equal_correct key pattern equalLength next
      simp [h, hkIndex, hpIndex, heads, hn, ih]
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq, heads, true_and, nextval]
    · simp [h, hkIndex, hpIndex, heads]
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq, heads, false_and, not_false_eq_true]
  · have hk : key.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hp : pattern.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [h, hk, hp]
termination_by key.val.length - index.val
decreasing_by omega

private theorem same_pattern_correct (key : alloc.vec.Vec U8) (pattern : Slice U8) :
    same_pattern key pattern = .ok (decide (key.val = pattern.val)) := by
  rw [same_pattern]
  by_cases h : key.val.length = pattern.val.length
  · have ih := equal_correct key pattern h 0#usize
    simpa [h] using ih
  · have unequal : key.val ≠ pattern.val := fun eq => h (congrArg List.length eq)
    simp [h, unequal]

private theorem group_0_correct (key : alloc.vec.Vec U8) :
    group_0 key = .ok (lookup key.val entries_0) := by
  simp [group_0, same_pattern_correct, lookup, entries_0, Array.to_slice, Array.make, lift, List.find?_cons]
  repeat' (split <;> simp_all)

private theorem group_1_correct (key : alloc.vec.Vec U8) :
    group_1 key = .ok (lookup key.val entries_1) := by
  simp [group_1, same_pattern_correct, lookup, entries_1, Array.to_slice, Array.make, lift, List.find?_cons]
  repeat' (split <;> simp_all)

private theorem group_2_correct (key : alloc.vec.Vec U8) :
    group_2 key = .ok (lookup key.val entries_2) := by
  simp [group_2, same_pattern_correct, lookup, entries_2, Array.to_slice, Array.make, lift, List.find?_cons]
  repeat' (split <;> simp_all)

private theorem group_3_correct (key : alloc.vec.Vec U8) :
    group_3 key = .ok (lookup key.val entries_3) := by
  simp [group_3, same_pattern_correct, lookup, entries_3, Array.to_slice, Array.make, lift, List.find?_cons]
  repeat' (split <;> simp_all)

private theorem group_4_correct (key : alloc.vec.Vec U8) :
    group_4 key = .ok (lookup key.val entries_4) := by
  simp [group_4, same_pattern_correct, lookup, entries_4, Array.to_slice, Array.make, lift, List.find?_cons]
  repeat' (split <;> simp_all)

private theorem group_5_correct (key : alloc.vec.Vec U8) :
    group_5 key = .ok (lookup key.val entries_5) := by
  simp [group_5, same_pattern_correct, lookup, entries_5, Array.to_slice, Array.make, lift, List.find?_cons]
  repeat' (split <;> simp_all)

private theorem group_6_correct (key : alloc.vec.Vec U8) :
    group_6 key = .ok (lookup key.val entries_6) := by
  simp [group_6, same_pattern_correct, lookup, entries_6, Array.to_slice, Array.make, lift, List.find?_cons]
  repeat' (split <;> simp_all)

/-- Recognition is exact for every byte vector, not just the listed examples. -/
theorem builtin_kind_total_correct (key : alloc.vec.Vec U8) :
    builtin_kind key = .ok (role key.val) := by
  simp only [builtin_kind, group_0_correct, group_1_correct, group_2_correct, group_3_correct, group_4_correct, group_5_correct, group_6_correct, role, entities, lookup_append]
  repeat' first | split | simp_all
end Rowl.Builtins
