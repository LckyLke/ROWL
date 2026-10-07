import Rowl.RdfReadIndexes
import Rowl.Collection

/-!
# Completeness of the expression readers of the RDF mapping

For the expressions of OWL 2 that the reverse mapping reads back, the readers
of `rdf_mapping` return exactly the expression whose forward mapping
(`TOPE`, `TCE`, `TDR` of `RdfMapping.lean`) the graph holds at known positions,
use exactly those positions and record exactly the blank nodes of that mapping,
in order (`role_complete`, `cells_complete`, `range_reads`, `class_reads`).
Literals must be readable (`LiteralReadable`: not an `rdf:PlainLiteral` with an
empty language tag), facets those of OWL 2 (`owl2Facets`) and cardinalities at
most 10000 (`CardinalityReadable`);
the properties of restrictions must be classified as object or data properties
(`UsesTyped`).
-/

namespace Rowl.RdfReadExpressions
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust Rowl.RdfMapping Rowl.RdfReadIndexes
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-! ### The expressions the reader reads back -/

/-- A literal the reader reads back: every literal except an `rdf:PlainLiteral`
    with an empty language tag, which the forward mapping writes as the
    `xsd:string` literal of its text. -/
def LiteralReadable (v : model.Literal) : Prop :=
  ¬ (v.datatype.iri.spelling.val = rdfPlainLiteral ∧ ∃ text, v.lexical.val = text ++ [64#u8])

def xsdLength : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 108#u8, 101#u8, 110#u8, 103#u8, 116#u8, 104#u8]
def xsdMinLength : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 109#u8, 105#u8, 110#u8, 76#u8, 101#u8, 110#u8, 103#u8, 116#u8, 104#u8]
def xsdMaxLength : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 109#u8, 97#u8, 120#u8, 76#u8, 101#u8, 110#u8, 103#u8, 116#u8, 104#u8]
def xsdPattern : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 112#u8, 97#u8, 116#u8, 116#u8, 101#u8, 114#u8, 110#u8]
def xsdMinInclusive : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 109#u8, 105#u8, 110#u8, 73#u8, 110#u8, 99#u8, 108#u8, 117#u8, 115#u8, 105#u8, 118#u8, 101#u8]
def xsdMaxInclusive : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 109#u8, 97#u8, 120#u8, 73#u8, 110#u8, 99#u8, 108#u8, 117#u8, 115#u8, 105#u8, 118#u8, 101#u8]
def xsdMinExclusive : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 109#u8, 105#u8, 110#u8, 69#u8, 120#u8, 99#u8, 108#u8, 117#u8, 115#u8, 105#u8, 118#u8, 101#u8]
def xsdMaxExclusive : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 109#u8, 97#u8, 120#u8, 69#u8, 120#u8, 99#u8, 108#u8, 117#u8, 115#u8, 105#u8, 118#u8, 101#u8]
def rdfLangRange : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 108#u8, 97#u8, 110#u8, 103#u8, 82#u8, 97#u8, 110#u8, 103#u8, 101#u8]

/-- The constraining facets of the OWL 2 datatype map (§4 of the structural
    specification): the eight facets of XML Schema that OWL 2 uses and
    `rdf:langRange`. -/
def owl2Facets : List (List U8) :=
  [xsdLength, xsdMinLength, xsdMaxLength, xsdPattern, xsdMinInclusive, xsdMaxInclusive, xsdMinExclusive,
    xsdMaxExclusive, rdfLangRange]

/-- A cardinality the reader reads back: at most 10000 (`CARDINALITY_LIMIT`). -/
def CardinalityReadable (n : probes.Natural) : Prop := Rowl.Probes.naturalValue n ≤ 10000

mutual
/-- The data ranges the reader reads back: those whose literals it reads back,
    with the facets of OWL 2. -/
inductive RangeReadable : model.DataRange → Prop
  | datatype (d : model.Datatype) : RangeReadable (.Datatype d)
  | intersection (xs : model.AtLeastTwo model.DataRange) : RangesReadable (members2 xs) →
      RangeReadable (.Intersection xs)
  | union (xs : model.AtLeastTwo model.DataRange) : RangesReadable (members2 xs) → RangeReadable (.Union xs)
  | complement (r : model.DataRange) : RangeReadable r → RangeReadable (.Complement r)
  | oneOf (xs : model.NonEmpty model.Literal) : (∀ v ∈ members1 xs, LiteralReadable v) →
      RangeReadable (.OneOf xs)
  | restriction (d : model.Datatype) (xs : model.NonEmpty model.FacetRestriction) :
      (∀ f ∈ members1 xs, LiteralReadable f.value ∧ f.facet.spelling.val ∈ owl2Facets) →
      RangeReadable (.Restriction d xs)

/-- Data ranges the reader reads back. -/
inductive RangesReadable : List model.DataRange → Prop
  | nil : RangesReadable []
  | cons (r : model.DataRange) (rs : List model.DataRange) : RangeReadable r → RangesReadable rs →
      RangesReadable (r :: rs)
end

mutual
/-- The class expressions the reader reads back: those whose cardinalities,
    literals and data ranges it reads back. -/
inductive ClassReadable : model.ClassExpression → Prop
  | named (c : model.Class) : ClassReadable (.Class c)
  | intersection (xs : model.AtLeastTwo model.ClassExpression) : ClassesReadable (members2 xs) →
      ClassReadable (.ObjectIntersectionOf xs)
  | union (xs : model.AtLeastTwo model.ClassExpression) : ClassesReadable (members2 xs) →
      ClassReadable (.ObjectUnionOf xs)
  | complement (c : model.ClassExpression) : ClassReadable c → ClassReadable (.ObjectComplementOf c)
  | oneOf (xs : model.NonEmpty model.Individual) : ClassReadable (.ObjectOneOf xs)
  | some (role : model.ObjectPropertyExpression) (c : model.ClassExpression) : ClassReadable c →
      ClassReadable (.ObjectSomeValuesFrom role c)
  | all (role : model.ObjectPropertyExpression) (c : model.ClassExpression) : ClassReadable c →
      ClassReadable (.ObjectAllValuesFrom role c)
  | hasValue (role : model.ObjectPropertyExpression) (a : model.Individual) :
      ClassReadable (.ObjectHasValue role a)
  | hasSelf (role : model.ObjectPropertyExpression) : ClassReadable (.ObjectHasSelf role)
  | min (n : probes.Natural) (role : model.ObjectPropertyExpression) : CardinalityReadable n →
      ClassReadable (.ObjectMinCardinality n role none)
  | max (n : probes.Natural) (role : model.ObjectPropertyExpression) : CardinalityReadable n →
      ClassReadable (.ObjectMaxCardinality n role none)
  | exact (n : probes.Natural) (role : model.ObjectPropertyExpression) : CardinalityReadable n →
      ClassReadable (.ObjectExactCardinality n role none)
  | minQualified (n : probes.Natural) (role : model.ObjectPropertyExpression) (c : model.ClassExpression) :
      CardinalityReadable n → ClassReadable c → ClassReadable (.ObjectMinCardinality n role (some c))
  | maxQualified (n : probes.Natural) (role : model.ObjectPropertyExpression) (c : model.ClassExpression) :
      CardinalityReadable n → ClassReadable c → ClassReadable (.ObjectMaxCardinality n role (some c))
  | exactQualified (n : probes.Natural) (role : model.ObjectPropertyExpression) (c : model.ClassExpression) :
      CardinalityReadable n → ClassReadable c → ClassReadable (.ObjectExactCardinality n role (some c))
  | dataSome (d : model.DataProperty) (r : model.DataRange) : RangeReadable r →
      ClassReadable (.DataSomeValuesFrom d r)
  | dataAll (d : model.DataProperty) (r : model.DataRange) : RangeReadable r →
      ClassReadable (.DataAllValuesFrom d r)
  | dataHasValue (d : model.DataProperty) (v : model.Literal) : LiteralReadable v →
      ClassReadable (.DataHasValue d v)
  | dataMin (n : probes.Natural) (d : model.DataProperty) : CardinalityReadable n →
      ClassReadable (.DataMinCardinality n d none)
  | dataMax (n : probes.Natural) (d : model.DataProperty) : CardinalityReadable n →
      ClassReadable (.DataMaxCardinality n d none)
  | dataExact (n : probes.Natural) (d : model.DataProperty) : CardinalityReadable n →
      ClassReadable (.DataExactCardinality n d none)
  | dataMinQualified (n : probes.Natural) (d : model.DataProperty) (r : model.DataRange) :
      CardinalityReadable n → RangeReadable r → ClassReadable (.DataMinCardinality n d (some r))
  | dataMaxQualified (n : probes.Natural) (d : model.DataProperty) (r : model.DataRange) :
      CardinalityReadable n → RangeReadable r → ClassReadable (.DataMaxCardinality n d (some r))
  | dataExactQualified (n : probes.Natural) (d : model.DataProperty) (r : model.DataRange) :
      CardinalityReadable n → RangeReadable r → ClassReadable (.DataExactCardinality n d (some r))

/-- Class expressions the reader reads back. -/
inductive ClassesReadable : List model.ClassExpression → Prop
  | nil : ClassesReadable []
  | cons (c : model.ClassExpression) (cs : List model.ClassExpression) : ClassReadable c → ClassesReadable cs →
      ClassesReadable (c :: cs)
end

/-- The reader classifies the properties among the uses as their kinds. -/
def UsesTyped (kinds : rdf_mapping.Kinds) (rows : List (model.Iri × typing.EntityKind)) : Prop :=
  ∀ row ∈ rows, (row.2 = .ObjectProperty → rdf_mapping.property_kind kinds row.1.spelling = .ok (some .Object)) ∧
    (row.2 = .DataProperty → rdf_mapping.property_kind kinds row.1.spelling = .ok (some .Data))

theorem uses_typed_append {kinds : rdf_mapping.Kinds} {rows rows' : List (model.Iri × typing.EntityKind)} :
    UsesTyped kinds (rows ++ rows') ↔ UsesTyped kinds rows ∧ UsesTyped kinds rows' := by
  constructor
  · intro h
    exact ⟨fun row member => h row (List.mem_append_left _ member),
      fun row member => h row (List.mem_append_right _ member)⟩
  · rintro ⟨h1, h2⟩ row member
    rcases List.mem_append.mp member with left | right
    · exact h1 row left
    · exact h2 row right

/-- The objects of the triples at the positions are the nodes, in order. -/
def Elements (triples : List rdf.Triple) (firsts : List Usize) (ns : List Node) : Prop :=
  List.Forall₂ (fun (f : Usize) n => ∃ t, triples[f.val]? = some t ∧ objectView t.object = n) firsts ns


/-! ### Names, individuals, literals and numbers -/

theorem node_iri_complete (node : rdf.Object) (iri : model.Iri) (view : objectView node = iriNode iri) :
    rdf_mapping.node_iri node = .ok (some iri) := by
  cases node with
  | Iri r =>
    have same : r.spelling.val = iri.spelling.val := by simpa [objectView, iriNode] using view
    simp only [rdf_mapping.node_iri, iri_of_identity, bind_ok]
    rw [iri_ext (i := ⟨r.spelling⟩) (j := iri) same]
  | Blank _ => simp [objectView, iriNode] at view
  | Literal _ => simp [objectView, iriNode] at view

theorem node_individual_complete (node : rdf.Object) (a : model.Individual)
    (view : objectView node = individualNode a) : rdf_mapping.node_individual node = .ok (some a) := by
  cases a with
  | Named i =>
    cases node with
    | Iri r =>
      have same : r.spelling.val = i.iri.spelling.val := by
        simpa [objectView, individualNode, iriNode] using view
      simp only [rdf_mapping.node_individual, iri_of_identity, bind_ok]
      rw [iri_ext (i := ⟨r.spelling⟩) (j := i.iri) same]
    | Blank _ => simp [objectView, individualNode, iriNode] at view
    | Literal _ => simp [objectView, individualNode, iriNode] at view
  | Anonymous an =>
    cases node with
    | Iri _ => simp [objectView, individualNode, anonymousNode] at view
    | Blank b =>
      have same : b = ⟨an.scope, an.label⟩ := by simpa [objectView, individualNode, anonymousNode] using view
      subst same
      simp [rdf_mapping.node_individual, Rowl.Nnf.copy_bytes_identity]
    | Literal _ => simp [objectView, individualNode, anonymousNode] at view

theorem element_at (triples : alloc.vec.Vec rdf.Triple) (f : Usize) (t : rdf.Triple)
    (at_f : triples.val[f.val]? = some t) : rdf_mapping.element triples f = .ok (some t.object) := by
  have inside : f.val < triples.val.length := (List.getElem?_eq_some_iff.mp at_f).1
  rw [rdf_mapping.element]
  simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, main_lookup triples f t at_f]

theorem append_from_total (bytes : alloc.vec.Vec U8) :
    ∀ (index : Usize) (out : alloc.vec.Vec U8), ∃ r, rdf_mapping.append_from out bytes index = .ok r := by
  intro index
  induction e : bytes.val.length - index.val generalizing index with
  | zero =>
    intro out
    have done : ¬ index.val < bytes.val.length := by omega
    exact ⟨out, by rw [rdf_mapping.append_from]; simp [UScalar.lt_equiv, done]⟩
  | succ n ih =>
    intro out
    have more : index.val < bytes.val.length := by omega
    have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    by_cases room : out.val.length < Usize.max
    · obtain ⟨pushed, push, -⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out bytes.val[index.val] room)
      obtain ⟨r, run⟩ := ih next (by omega) pushed
      exact ⟨r, by rw [rdf_mapping.append_from]; simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, usize_max_val,
        room, lookup, push, advance, run]⟩
    · obtain ⟨r, run⟩ := ih next (by omega) out
      exact ⟨r, by rw [rdf_mapping.append_from]; simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, usize_max_val,
        room, advance, run]⟩

theorem spelled_total (key : Slice U8) :
    ∀ (index : Usize) (out : alloc.vec.Vec U8), ∃ r, rdf_mapping.spelled key index out = .ok r := by
  intro index
  induction e : key.val.length - index.val generalizing index with
  | zero =>
    intro out
    have done : ¬ index.val < key.val.length := by omega
    exact ⟨out, by rw [rdf_mapping.spelled]; simp [UScalar.lt_equiv, done]⟩
  | succ n ih =>
    intro out
    have more : index.val < key.val.length := by omega
    have lookup : key.index_usize index = .ok key.val[index.val] := by
      simp [Slice.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    by_cases room : out.val.length < Usize.max
    · obtain ⟨pushed, push, -⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out key.val[index.val] room)
      obtain ⟨r, run⟩ := ih next (by omega) pushed
      exact ⟨r, by rw [rdf_mapping.spelled]; simp [Slice.len_val, UScalar.lt_equiv, more, usize_max_val,
        room, lookup, push, advance, run]⟩
    · obtain ⟨r, run⟩ := ih next (by omega) out
      exact ⟨r, by rw [rdf_mapping.spelled]; simp [Slice.len_val, UScalar.lt_equiv, more, usize_max_val,
        room, advance, run]⟩

theorem literal_ext {v : model.Literal} {lexical spelling : alloc.vec.Vec U8} (l : lexical.val = v.lexical.val)
    (d : spelling.val = v.datatype.iri.spelling.val) : ({ lexical, datatype := ⟨⟨spelling⟩⟩ } : model.Literal) = v := by
  obtain ⟨lex, ⟨⟨sp⟩⟩⟩ := v
  simp only at l d
  rw [vec_eq_of_val l, vec_eq_of_val d]

/-- The reader reads a literal back from its forward image. -/
theorem literal_complete (node : rdf.Object) (v : model.Literal) (n : Node) (literal : LiteralNode v n)
    (readable : LiteralReadable v) (view : objectView node = n) : rdf_mapping.node_literal node = .ok (some v) := by
  cases literal with
  | typed notPlain =>
    cases node with
    | Literal lit =>
      obtain ⟨lex, kind⟩ := lit
      cases kind with
      | Datatype d =>
        simp only [objectView, literalView, Node.literal.injEq, LiteralView.typed.injEq] at view
        obtain ⟨lexEq, dEq⟩ := view
        have notPlain' : ¬ d.spelling.val = rdfPlainLiteral := by rw [dEq]; exact notPlain
        simp only [rdfPlainLiteral] at notPlain'
        simp only [rdf_mapping.node_literal, rdf_mapping.literal_of, lift, bind_ok, same_correct, array_slice_val,
          notPlain', decide_false, Bool.false_eq_true, ↓reduceIte, Rowl.Nnf.copy_bytes_identity, iri_of_identity]
        rw [literal_ext lexEq dEq]
      | Language _ => simp [objectView, literalView] at view
    | Iri _ => simp [objectView] at view
    | Blank _ => simp [objectView] at view
  | tagged text tag isPlain lexEq tagNonempty noAt =>
    cases node with
    | Literal lit =>
      obtain ⟨lex, kind⟩ := lit
      cases kind with
      | Datatype _ => simp [objectView, literalView] at view
      | Language tg =>
        simp only [objectView, literalView, Node.literal.injEq, LiteralView.tagged.injEq] at view
        obtain ⟨textEq, tagEq⟩ := view
        have tagLen : tg.val.length ≠ 0 := by rw [tagEq]; simpa using tagNonempty
        have notZero : ¬ alloc.vec.Vec.len tg = 0#usize := by
          intro h
          apply tagLen
          have := congrArg UScalar.val h
          simpa [alloc.vec.Vec.len_val] using this
        have atFree : rdf_mapping.has_at tg 0#usize = .ok false := by
          rw [has_at_correct]
          simp [tagEq, noAt]
        have total : v.lexical.val.length ≤ Usize.max := v.lexical.property
        have short : lex.val.length + tg.val.length < Usize.max := by
          rw [lexEq] at total
          rw [textEq, tagEq]
          simp at total
          omega
        obtain ⟨room, roomRun, roomValue⟩ := WP.spec_imp_exists
          (Usize.sub_spec (x := core.num.Usize.MAX) (y := alloc.vec.Vec.len tg)
            (by simp [usize_max_val, alloc.vec.Vec.len_val]))
        have roomIs : room.val = Usize.max - tg.val.length := by
          simp [usize_max_val, alloc.vec.Vec.len_val] at roomValue; omega
        have fits : lex.val.length < room.val := by rw [roomIs]; omega
        have pushRoom : lex.val.length < Usize.max := by omega
        obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec lex 64#u8 pushRoom)
        obtain ⟨appended, appendRun⟩ := append_from_total tg 0#usize pushed
        have appendVal := append_from_spec tg 0#usize pushed appended (by rw [contents]; simp; omega) appendRun
        obtain ⟨plain, plainRun⟩ := spelled_total (Array.to_slice (Array.make 55#usize [104#u8, 116#u8, 116#u8, 112#u8,
          58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8,
          57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8,
          121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 80#u8, 108#u8, 97#u8, 105#u8, 110#u8,
          76#u8, 105#u8, 116#u8, 101#u8, 114#u8, 97#u8, 108#u8] (by simp))) 0#usize (alloc.vec.Vec.new U8)
        have plainVal := spelled_spec _ 0#usize (alloc.vec.Vec.new U8) plain (by simp) plainRun
        rw [rdf_mapping.node_literal.eq_def]
        simp only [rdf_mapping.literal_of]
        simp only [notZero, ↓reduceIte, atFree, bind_ok, Bool.false_eq_true, roomRun, alloc.vec.Vec.len_val,
          UScalar.lt_equiv, fits, Rowl.Nnf.copy_bytes_identity, push, appendRun, lift, plainRun]
        have result : ({ lexical := appended, datatype := ⟨⟨plain⟩⟩ } : model.Literal) = v := by
          apply literal_ext
          · rw [appendVal, contents, lexEq, textEq, tagEq]
            simp
          · rw [plainVal, isPlain]
            simp [array_slice_val, rdfPlainLiteral]
        rw [result]
    | Iri _ => simp [objectView] at view
    | Blank _ => simp [objectView] at view
  | plain text isPlain lexEq => exact absurd ⟨isPlain, text, lexEq⟩ readable

theorem natural_value_injective : ∀ {m n : probes.Natural},
    Rowl.Probes.naturalValue m = Rowl.Probes.naturalValue n → m = n
  | .Zero, .Zero, _ => rfl
  | .Succ m, .Succ n, h => by
    simp only [Rowl.Probes.naturalValue, Nat.add_right_cancel_iff] at h
    rw [natural_value_injective h]
  | .Zero, .Succ n, h => by simp [Rowl.Probes.naturalValue] at h
  | .Succ m, .Zero, h => by simp [Rowl.Probes.naturalValue] at h

theorem natural_up_total : ∀ (count : Usize) (out : probes.Natural), ∃ r, rdf_mapping.natural_up count out = .ok r := by
  intro count
  induction e : count.val generalizing count with
  | zero =>
    intro out
    have zero : count = 0#usize := UScalar.eq_of_val_eq (by simp [e])
    exact ⟨out, by rw [rdf_mapping.natural_up]; simp [zero]⟩
  | succ n ih =>
    intro out
    have notZero : ¬ count = 0#usize := fun h => by rw [h] at e; simp at e
    obtain ⟨fewer, back, fewerValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := count) (y := 1#usize) (by scalar_tac))
    obtain ⟨r, run⟩ := ih fewer (by simp at fewerValue; omega) (.Succ out)
    exact ⟨r, by rw [rdf_mapping.natural_up]; simp [notZero, back, run]⟩

/-- The reader reads a cardinality back from its canonical literal. -/
theorem natural_complete (node : rdf.Object) (n : probes.Natural) (natural : NaturalNode n (objectView node))
    (small : CardinalityReadable n) : rdf_mapping.node_natural node = .ok (some n) := by
  obtain ⟨digits, canonical, view⟩ := natural
  obtain ⟨nonempty, isDigits, numeric, short⟩ := canonical
  cases node with
  | Iri _ => simp [objectView] at view
  | Blank _ => simp [objectView] at view
  | Literal lit =>
    obtain ⟨lex, kind⟩ := lit
    cases kind with
    | Language _ => simp [objectView, literalView] at view
    | Datatype d =>
      simp only [objectView, literalView, Node.literal.injEq, LiteralView.typed.injEq] at view
      obtain ⟨lexEq, dEq⟩ := view
      have dEq' := dEq
      simp only [xsdNonNegativeInteger] at dEq'
      have valueLt : Rowl.Probes.naturalValue n < 2 ^ UScalarTy.Usize.numBits := by
        have : 10000 < 2 ^ UScalarTy.Usize.numBits := by
          have := System.Platform.numBits_eq
          simp only [UScalarTy.numBits]
          rcases this with h | h <;> simp [h]
        unfold CardinalityReadable at small
        omega
      obtain ⟨value, valueVal⟩ : ∃ value : Usize, value.val = Rowl.Probes.naturalValue n :=
        ⟨UScalar.ofNatCore (Rowl.Probes.naturalValue n) valueLt, UScalar.ofNatCore_val_eq _⟩
      have bounded : Rowl.Decimal.Bounded lex.val 0 lex.val.length 10000 value.val := by
        rw [valueVal, lexEq]
        refine ⟨?_, le_refl _, ?_, ?_, small⟩
        · cases digits with
          | nil => exact absurd rfl nonempty
          | cons _ _ => simp
        · simpa [Rowl.Decimal.Slice] using isDigits
        · simpa [Rowl.Decimal.Slice] using numeric
      have limitVal : (rdf_mapping.CARDINALITY_LIMIT).val = 10000 := by simp [rdf_mapping.CARDINALITY_LIMIT]
      have readRun : decimal.read_bounded lex 0#usize (alloc.vec.Vec.len lex)
          rdf_mapping.CARDINALITY_LIMIT = .ok (some value) := by
        rw [Rowl.Decimal.read_bounded_some_iff]
        simpa [alloc.vec.Vec.len_val, limitVal] using bounded
      obtain ⟨m, upRun⟩ := natural_up_total value .Zero
      have upValue := natural_up_spec value .Zero m upRun
      have same : m = n := natural_value_injective (by rw [upValue, valueVal]; simp [Rowl.Probes.naturalValue])
      subst same
      rw [rdf_mapping.node_natural.eq_def]
      simp only [lift, bind_ok, same_correct, array_slice_val, dEq', decide_true, ↓reduceIte]
      by_cases long : 1 < lex.val.length
      · have longU : alloc.vec.Vec.len lex > 1#usize := by
          rw [gt_iff_lt, UScalar.lt_equiv]
          simpa [alloc.vec.Vec.len_val] using long
        have lookup : lex.index_usize 0#usize = .ok lex.val[0] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem (show 0 < lex.val.length by omega)]
        have notZero : ¬ lex.val[0] = 48#u8 := by
          intro h
          rcases short with one | head
          · rw [← lexEq] at one; omega
          · apply head
            rw [← lexEq, List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < lex.val.length by omega), h]
        simp only [longU, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup, bind_ok, notZero, readRun, upRun]
      · have shortU : ¬ alloc.vec.Vec.len lex > 1#usize := by
          rw [gt_iff_lt, UScalar.lt_equiv]
          simpa [alloc.vec.Vec.len_val] using long
        simp only [shortU, ↓reduceIte, readRun, bind_ok, upRun]

theorem true_complete (node : rdf.Object) (view : objectView node = trueNode) :
    rdf_mapping.node_true node = .ok true := by
  cases node with
  | Iri _ => simp [objectView, trueNode] at view
  | Blank _ => simp [objectView, trueNode] at view
  | Literal lit =>
    obtain ⟨lex, kind⟩ := lit
    cases kind with
    | Language _ => simp [objectView, literalView, trueNode] at view
    | Datatype d =>
      simp only [objectView, literalView, trueNode, Node.literal.injEq, LiteralView.typed.injEq] at view
      obtain ⟨lexEq, dEq⟩ := view
      simp only [xsdBoolean] at dEq
      rw [rdf_mapping.node_true.eq_def]
      simp [lift, same_correct, array_slice_val, dEq, lexEq]


/-! ### Object property expressions and list cells -/

theorem marked_nil_take (s : rdf_mapping.State) (index : Usize) :
    Marked s { s with used := s.used.set index true } (fun i => i ∈ [index.val]) [] :=
  marked_same (marked_take s index) (fun i => by simp)

theorem single_position {triples : List rdf.Triple} {pos : List Nat} {p : Pattern} (h : At triples pos [p]) :
    ∃ i, pos = [i] := by
  have len := at_length h
  match pos, len with
  | [i], _ => exact ⟨i, rfl⟩

theorem pair_positions {triples : List rdf.Triple} {pos : List Nat} {p q : Pattern} {ps : List Pattern}
    (h : At triples pos (p :: q :: ps)) : ∃ i j rest, pos = i :: j :: rest := by
  have len := at_length h
  match pos, len with
  | i :: j :: rest, _ => exact ⟨i, j, rest, rfl⟩

theorem triple_positions {triples : List rdf.Triple} {pos : List Nat} {p q r : Pattern} {ps : List Pattern}
    (h : At triples pos (p :: q :: r :: ps)) : ∃ i j k rest, pos = i :: j :: k :: rest := by
  have len := at_length h
  match pos, len with
  | i :: j :: k :: rest, _ => exact ⟨i, j, k, rest, rfl⟩

/-- The reader reads an object property expression back from its forward image. -/
theorem role_complete (triples : alloc.vec.Vec rdf.Triple) {role : model.ObjectPropertyExpression} {s0 s1 : Supply}
    {n : Node} {ps : List Pattern} (tope : TOPE role s0 n ps s1) {fresh : Supply} (split : s0 = fresh ++ s1)
    {s : rdf_mapping.State} {pos : List Nat} {node : rdf.Object} (view : objectView node = n)
    (ready : Ready triples s pos ps fresh) :
    ∃ s', rdf_mapping.property_expression triples node s = .ok (some (role, s')) ∧
      Marked s s' (fun i => i ∈ pos) fresh := by
  cases tope with
  | named p =>
    have empty : fresh = [] := by simpa using split
    subst empty
    have noPos : pos = [] := by have := at_length ready.holds; simpa using this
    subst noPos
    cases node with
    | Iri r =>
      have same : r.spelling.val = p.iri.spelling.val := by simpa [objectView, iriNode] using view
      refine ⟨s, ?_, ready_nil_marked s⟩
      rw [rdf_mapping.property_expression.eq_def]
      simp only [iri_of_identity, bind_ok]
      rw [iri_ext (i := ⟨r.spelling⟩) (j := p.iri) same]
    | Blank _ => simp [objectView, iriNode] at view
    | Literal _ => simp [objectView, iriNode] at view
  | inverse p x =>
    have freshIs : fresh = [x] := by
      have h : [x] ++ s1 = fresh ++ s1 := by simpa using split
      exact (List.append_cancel_right h).symm
    subst freshIs
    obtain ⟨i, rfl⟩ := single_position ready.holds
    cases node with
    | Blank b =>
      have bx : b = x := by simpa [objectView] using view
      subst bx
      have ready' : Ready triples s ([i] ++ []) (headPatterns b [(owlInverseOf, iriNode p.iri)] ++ []) (b :: []) := by
        simpa [headPatterns] using ready
      have heads := heads_of_ready ready' rfl (fun _ m => by simp at m) (by simp) (by simp)
      have unused := ready.free i (by simp)
      obtain ⟨found, foundVal, findRun⟩ := find_hit triples s b ready.complete heads (k := 0) rfl owlInverseOf
        (fun _ => rfl) unused
      obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads (k := 0) rfl
      simp only [List.getElem_cons_zero] at object
      cases objectIs : t.object with
      | Iri r =>
        rw [objectIs] at object
        have same : r.spelling.val = p.iri.spelling.val := by simpa [objectView, iriNode] using object
        have m1 := marked_nil_take s found
        have room := ready.room
        obtain ⟨s2, recordRun, m2⟩ := record_ok { s with used := s.used.set found true } b
          (by simp at room ⊢; omega)
        refine ⟨s2, ?_, ?_⟩
        · rw [rdf_mapping.property_expression.eq_def]
          simp only [lift, bind_ok, findRun, array_slice_val, owlInverseOf,
            alloc.vec.Vec.index_slice_index, main_lookup triples found t (by rw [foundVal]; exact at_t), objectIs,
            take_correct, recordRun, iri_of_identity]
          rw [iri_ext (i := ⟨r.spelling⟩) (j := p.iri) same]
        · refine marked_same (marked_trans m1 m2) (fun j => ?_)
          simp [foundVal]
      | Blank _ => rw [objectIs] at object; simp [objectView, iriNode] at object
      | Literal _ => rw [objectIs] at object; simp [objectView, iriNode] at object
    | Iri _ => simp [objectView] at view
    | Literal _ => simp [objectView] at view

theorem list_of_cons (c : rdf.BlankNode) (cs : List rdf.BlankNode) (e : Node) (es : List Node) :
    listOf (c :: cs) (e :: es) = (.blank c, ⟨.blank c, rdfFirst, e⟩ :: ⟨.blank c, rdfRest, (listOf cs es).1⟩ ::
      (listOf cs es).2) := rfl

/-- The reader reads the cells of a list back from its forward image, in order,
    with the positions of their `rdf:first` triples. -/
theorem cells_complete (triples : alloc.vec.Vec rdf.Triple) :
    ∀ (cells : List rdf.BlankNode) (elements : List Node), cells.length = elements.length → cells.Nodup →
    ∀ (s : rdf_mapping.State) (pos : List Nat) (node : rdf.Object) (out : alloc.vec.Vec Usize) (fuel : Usize),
      objectView node = (listOf cells elements).1 → Ready triples s pos (listOf cells elements).2 cells →
      cells.length ≤ fuel.val → out.val.length + cells.length ≤ Usize.max →
      ∃ (firsts : alloc.vec.Vec Usize) (news : List Usize) (s' : rdf_mapping.State),
        rdf_mapping.cells triples node s out fuel = .ok (some (firsts, s')) ∧ firsts.val = out.val ++ news ∧
        Elements triples.val news elements ∧ Marked s s' (fun i => i ∈ pos) cells := by
  intro cells
  induction cells with
  | nil =>
    intro elements lengths _ s pos node out fuel view ready _ _
    have empty : elements = [] := by cases elements <;> simp_all
    subst empty
    have noPos : pos = [] := by have := at_length ready.holds; simpa [listOf] using this
    subst noPos
    refine ⟨out, [], s, ?_, by simp, List.Forall₂.nil, ready_nil_marked s⟩
    rw [rdf_mapping.cells]
    have nil : objectView node = .iri rdfNil := by simpa [listOf] using view
    simp [is_nil_correct, nil]
  | cons c cs ih =>
    intro elements lengths nodup s pos node out fuel view ready fuelOk room
    cases elements with
    | nil => simp at lengths
    | cons e es =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
      have cOut : c ∉ cs := (List.nodup_cons.mp nodup).1
      have nodupRest : cs.Nodup := (List.nodup_cons.mp nodup).2
      rw [list_of_cons] at view ready
      obtain ⟨h0, h1, rpos, rfl⟩ := pair_positions ready.holds
      cases node with
      | Iri _ => simp [objectView] at view
      | Literal _ => simp [objectView] at view
      | Blank b =>
        have bc : b = c := by simpa [objectView] using view
        subst bc
        let head : List (List U8 × Node) := [(rdfFirst, e), (rdfRest, (listOf cs es).1)]
        have ready3 : Ready triples s ([h0, h1] ++ rpos ++ []) (headPatterns b head ++ (listOf cs es).2 ++ [])
            ([b] ++ cs ++ []) := by simpa [headPatterns, head] using ready
        have ready2 : Ready triples s ([h0, h1] ++ rpos) (headPatterns b head ++ (listOf cs es).2) (b :: cs) := by
          simpa [headPatterns, head] using ready
        have restSubjects : BlankSubjects cs (listOf cs es).2 := blank_subjects_of (list_of_subjects cs es)
        have heads := heads_of_ready ready2 rfl restSubjects cOut (by simp [head, rdfFirst, rdfRest])
        have nodupPos := ready.nodup
        have h01 : h0 ≠ h1 := by
          intro same; subst same; simp at nodupPos
        have unused0 := ready.free h0 (by simp)
        have unused1 := ready.free h1 (by simp)
        obtain ⟨found0, found0Val, find0⟩ := find_hit triples s b ready.complete heads (k := 0) rfl rdfFirst
          (fun _ => rfl) unused0
        obtain ⟨_, t0, at0, -, -, object0⟩ := heads_at_triple heads (k := 0) rfl
        have m1 := marked_nil_take s found0
        let s1 : rdf_mapping.State := { s with used := s.used.set found0 true }
        have unused1' : s1.used.val[h1]? = some false :=
          marked_unused m1 unused1 (by simp [found0Val]; exact fun h => h01 h.symm)
        obtain ⟨found1, found1Val, find1⟩ := find_hit triples s1 b ready.complete
          (heads_at_mono heads (fun j => marked_back m1)) (k := 1) rfl rdfRest (fun _ => rfl) unused1'
        obtain ⟨_, t1, at1, -, -, object1⟩ := heads_at_triple heads (k := 1) rfl
        have m2 := marked_nil_take s1 found1
        let s2 : rdf_mapping.State := { s1 with used := s1.used.set found1 true }
        have room0 := ready.room
        obtain ⟨s3, recordRun, m3⟩ := record_ok s2 b (by
          show s.blanks.val.length < Usize.max
          simp at room0; omega)
        have m123 := marked_trans (marked_trans m1 m2) m3
        have positive : fuel > 0#usize := by scalar_tac
        obtain ⟨fewer, back, fewerValue⟩ := WP.spec_imp_exists
          (Usize.sub_spec (x := fuel) (y := 1#usize) (by scalar_tac))
        have fewerIs : fewer.val + 1 = fuel.val := by simp at fewerValue; omega
        have outRoom : out.val.length < Usize.max := by simp at room; omega
        obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out found0 outRoom)
        have readyRest := ready_middle ready3 rfl (at_length (at_append_inv ready2.holds rfl).2 ▸ rfl)
          (by simpa using nodup) (blank_subjects_head b head) (fun _ m => by simp at m) m123
          (fun j hj => by
            simp only [List.mem_singleton] at hj
            rcases hj with (h | h) | h
            · rw [h, found0Val]; simp
            · rw [h, found1Val]; simp
            · exact h.elim) (by simp)
        obtain ⟨firsts, news, s', cellsRun, firstsIs, elementsOk, mRest⟩ := ih es lengths nodupRest s3 rpos t1.object
          pushed fewer (by simpa [head] using object1) readyRest (by simp only [List.length_cons] at fuelOk; omega)
          (by rw [contents]; simp at room ⊢; omega)
        have cellRun : rdf_mapping.cell triples (.Blank b) s = .ok (some (found0, found1, s3)) := by
          rw [rdf_mapping.cell]
          simp only [lift, bind_ok, find0, array_slice_val, rdfFirst, take_correct]
          have find1' : ∀ key : Slice U8, key.val = rdfRest → rdf_mapping.find triples
              { used := s.used.set found0 true, blanks := s.blanks, subjects := s.subjects, sources := s.sources } b key =
              .ok (some found1) := find1
          simp only [find1', array_slice_val, rdfRest, take_correct, bind_ok]
          have recordRun' : rdf_mapping.record
              { used := (s.used.set found0 true).set found1 true, blanks := s.blanks, subjects := s.subjects,
                sources := s.sources } b = .ok s3 := recordRun
          rw [recordRun', bind_ok]
        refine ⟨firsts, found0 :: news, s', ?_, by rw [firstsIs, contents]; simp, ?_, ?_⟩
        · rw [rdf_mapping.cells]
          have notNil : ¬ objectView (rdf.Object.Blank b) = .iri rdfNil := by simp [objectView]
          simp only [is_nil_correct, notNil, decide_false, Bool.false_eq_true, ↓reduceIte, positive, cellRun, bind_ok,
            alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, outRoom]
          change (Std.bind (alloc.vec.Vec.push out found0) _) = _
          rw [push, bind_ok]
          simp only [alloc.vec.Vec.index_slice_index, main_lookup triples found1 t1 (by rw [found1Val]; exact at1),
            bind_ok, back, cellsRun]
        · refine List.Forall₂.cons ⟨t0, by rw [found0Val]; exact at0, by simpa [head] using object0⟩ elementsOk
        · refine marked_same (marked_trans m123 mRest) (fun j => ?_)
          simp only [found0Val, found1Val, List.mem_cons]
          tauto

/-! ### The elements of lists -/

theorem elements_drop_nil {triples : List rdf.Triple} {firsts : alloc.vec.Vec Usize} {index : Usize}
    (h : Elements triples (firsts.val.drop index.val) []) : firsts.val.length ≤ index.val := by
  have empty : firsts.val.drop index.val = [] := List.forall₂_nil_right_iff.mp h
  simpa using empty

theorem elements_drop_cons {triples : List rdf.Triple} {firsts : alloc.vec.Vec Usize} {index : Usize}
    {n : Node} {ns : List Node} (h : Elements triples (firsts.val.drop index.val) (n :: ns)) :
    ∃ (inside : index.val < firsts.val.length) (t : rdf.Triple), triples[firsts.val[index.val].val]? = some t ∧
      objectView t.object = n ∧ Elements triples (firsts.val.drop (index.val + 1)) ns := by
  have inside : index.val < firsts.val.length := by
    apply Classical.byContradiction
    intro outside
    have empty : firsts.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    rw [empty] at h
    cases h
  rw [List.drop_eq_getElem_cons inside] at h
  obtain ⟨⟨t, at_t, view⟩, rest⟩ := List.forall₂_cons.mp h
  exact ⟨inside, t, at_t, view, rest⟩

theorem new_length (T : Type) : (alloc.vec.Vec.new T).val.length = 0 := by simp

theorem firsts_lookup (firsts : alloc.vec.Vec Usize) (index : Usize) (inside : index.val < firsts.val.length) :
    firsts.index_usize index = .ok firsts.val[index.val] := by
  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]

theorem individual_members_complete (triples : alloc.vec.Vec rdf.Triple) (firsts : alloc.vec.Vec Usize) :
    ∀ (members : List model.Individual) (index : Usize) (out : alloc.vec.Vec model.Individual),
      Elements triples.val (firsts.val.drop index.val) (members.map individualNode) →
      out.val.length + members.length ≤ Usize.max →
      ∃ v, rdf_mapping.individual_members triples firsts index out = .ok (some v) ∧ v.val = out.val ++ members := by
  intro members
  induction members with
  | nil =>
    intro index out elements _
    have done := elements_drop_nil elements
    refine ⟨out, ?_, by simp⟩
    rw [rdf_mapping.individual_members]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, show ¬ index.val < firsts.val.length by omega]
  | cons a more ih =>
    intro index out elements room
    obtain ⟨inside, t, at_t, view, rest⟩ := elements_drop_cons elements
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := firsts.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have outRoom : out.val.length < Usize.max := by simp at room; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out a outRoom)
    obtain ⟨v, run, value⟩ := ih next pushed (by rw [nextIs]; exact rest) (by rw [contents]; simp at room ⊢; omega)
    refine ⟨v, ?_, by rw [value, contents]; simp⟩
    rw [rdf_mapping.individual_members]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      firsts_lookup firsts index inside, bind_ok, element_at triples _ t at_t,
      node_individual_complete t.object a view, usize_max_val, outRoom, push, advance, run]

theorem literal_members_complete (triples : alloc.vec.Vec rdf.Triple) (firsts : alloc.vec.Vec Usize) :
    ∀ (members : List model.Literal) (nodes : List Node) (index : Usize) (out : alloc.vec.Vec model.Literal),
      List.Forall₂ LiteralNode members nodes → (∀ v ∈ members, LiteralReadable v) →
      Elements triples.val (firsts.val.drop index.val) nodes →
      out.val.length + members.length ≤ Usize.max →
      ∃ v, rdf_mapping.literal_members triples firsts index out = .ok (some v) ∧ v.val = out.val ++ members := by
  intro members
  induction members with
  | nil =>
    intro nodes index out literals _ elements _
    have empty : nodes = [] := List.forall₂_nil_left_iff.mp literals
    subst empty
    have done := elements_drop_nil elements
    refine ⟨out, ?_, by simp⟩
    rw [rdf_mapping.literal_members]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, show ¬ index.val < firsts.val.length by omega]
  | cons a more ih =>
    intro nodes index out literals readable elements room
    obtain ⟨n, ns, rfl, literal, restLiterals⟩ : ∃ n ns, nodes = n :: ns ∧ LiteralNode a n ∧
        List.Forall₂ LiteralNode more ns := by
      cases literals with
      | cons literal rest => exact ⟨_, _, rfl, literal, rest⟩
    obtain ⟨inside, t, at_t, view, rest⟩ := elements_drop_cons elements
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := firsts.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have outRoom : out.val.length < Usize.max := by simp at room; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out a outRoom)
    obtain ⟨v, run, value⟩ := ih ns next pushed restLiterals (fun w m => readable w (List.mem_cons_of_mem _ m))
      (by rw [nextIs]; exact rest) (by rw [contents]; simp at room ⊢; omega)
    refine ⟨v, ?_, by rw [value, contents]; simp⟩
    rw [rdf_mapping.literal_members]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      firsts_lookup firsts index inside, bind_ok, element_at triples _ t at_t,
      literal_complete t.object a n literal (readable a (by simp)) view, usize_max_val, outRoom, push, advance, run]

theorem non_empty_ext {α : Type} {xs : model.NonEmpty α} {first : α} {rest : alloc.vec.Vec α}
    (h1 : first = xs.first) (h2 : rest.val = xs.rest.val) : ({ first, rest } : model.NonEmpty α) = xs := by
  obtain ⟨f, r⟩ := xs
  simp only at h1 h2
  rw [h1, vec_eq_of_val h2]

theorem at_least_two_ext {α : Type} {xs : model.AtLeastTwo α} {first second : α} {rest : alloc.vec.Vec α}
    (h1 : first = xs.first) (h2 : second = xs.second) (h3 : rest.val = xs.rest.val) :
    ({ first, second, rest } : model.AtLeastTwo α) = xs := by
  obtain ⟨f, s, r⟩ := xs
  simp only at h1 h2 h3
  rw [h1, h2, vec_eq_of_val h3]

theorem firsts_from_cells {triples : List rdf.Triple} {firsts : alloc.vec.Vec Usize} {news : List Usize}
    {elements : List Node} (firstsIs : firsts.val = (alloc.vec.Vec.new Usize).val ++ news)
    (elementsOk : Elements triples news elements) : Elements triples (firsts.val.drop (0#usize : Usize).val) elements := by
  have zero : (0#usize : Usize).val = 0 := by simp
  rw [zero, List.drop_zero, firstsIs]
  simpa using elementsOk

theorem elements_length {triples : List rdf.Triple} {firsts : List Usize} {ns : List Node}
    (h : Elements triples firsts ns) : firsts.length = ns.length := List.Forall₂.length_eq h

/-- The individuals of a nonempty list read back from its forward image. -/
theorem individual_list1_complete (triples : alloc.vec.Vec rdf.Triple) (xs : model.NonEmpty model.Individual)
    (cells : List rdf.BlankNode) (cellsLen : cells.length = (members1 xs).length) (nodup : cells.Nodup)
    (s : rdf_mapping.State) (pos : List Nat) (node : rdf.Object) (fuel : Usize)
    (view : objectView node = (listOf cells ((members1 xs).map individualNode)).1)
    (ready : Ready triples s pos (listOf cells ((members1 xs).map individualNode)).2 cells)
    (fuelOk : cells.length ≤ fuel.val) :
    ∃ s', rdf_mapping.individual_list1 triples node s fuel = .ok (some (xs, s')) ∧
      Marked s s' (fun i => i ∈ pos) cells := by
  have cellsMax : cells.length ≤ Usize.max := by have := fuel.hBounds; scalar_tac
  obtain ⟨firsts, news, s', cellsRun, firstsIs, elementsOk, marked⟩ := cells_complete triples cells
    ((members1 xs).map individualNode) (by simp [cellsLen]) nodup s pos node (alloc.vec.Vec.new Usize) fuel view ready
    fuelOk (by simp; omega)
  have elements0 := firsts_from_cells firstsIs elementsOk
  simp only [members1, List.map_cons] at elements0
  obtain ⟨inside0, t0, at0, view0, rest0⟩ := elements_drop_cons elements0
  have one : (1#usize : Usize).val = 0 + 1 := by simp
  have zero : (0#usize : Usize).val = 0 := by simp
  obtain ⟨v, membersRun, value⟩ := individual_members_complete triples firsts xs.rest.val 1#usize
    (alloc.vec.Vec.new model.Individual) (by rw [one, ← zero]; exact rest0)
    (by have h := xs.rest.property; rw [new_length]; omega)
  have long : alloc.vec.Vec.len firsts ≥ 1#usize := by
    have h : 0 < firsts.val.length := by rw [zero] at inside0; exact inside0
    clear * - h
    scalar_tac
  refine ⟨s', ?_, marked⟩
  rw [rdf_mapping.individual_list1]
  simp only [cellsRun, bind_ok, uncurry_apply_pair, long, ↓reduceIte, alloc.vec.Vec.index_slice_index,
    firsts_lookup firsts 0#usize inside0, element_at triples _ t0 at0, node_individual_complete t0.object xs.first view0,
    membersRun]
  rw [non_empty_ext rfl (by rw [value]; simp)]

/-- The literals of a nonempty list read back from its forward image. -/
theorem literal_list1_complete (triples : alloc.vec.Vec rdf.Triple) (xs : model.NonEmpty model.Literal)
    (cells : List rdf.BlankNode) (nodes : List Node) (cellsLen : cells.length = (members1 xs).length)
    (literals : List.Forall₂ LiteralNode (members1 xs) nodes) (readable : ∀ v ∈ members1 xs, LiteralReadable v)
    (nodup : cells.Nodup) (s : rdf_mapping.State) (pos : List Nat) (node : rdf.Object) (fuel : Usize)
    (view : objectView node = (listOf cells nodes).1) (ready : Ready triples s pos (listOf cells nodes).2 cells)
    (fuelOk : cells.length ≤ fuel.val) :
    ∃ s', rdf_mapping.literal_list1 triples node s fuel = .ok (some (xs, s')) ∧
      Marked s s' (fun i => i ∈ pos) cells := by
  have cellsMax : cells.length ≤ Usize.max := by have := fuel.hBounds; scalar_tac
  have nodesLen := List.Forall₂.length_eq literals
  obtain ⟨firsts, news, s', cellsRun, firstsIs, elementsOk, marked⟩ := cells_complete triples cells nodes
    (by rw [cellsLen, nodesLen]) nodup s pos node (alloc.vec.Vec.new Usize) fuel view ready fuelOk (by simp; omega)
  have elements0 := firsts_from_cells firstsIs elementsOk
  obtain ⟨n0, ns, rfl, literal0, restLiterals⟩ : ∃ n0 ns, nodes = n0 :: ns ∧ LiteralNode xs.first n0 ∧
      List.Forall₂ LiteralNode xs.rest.val ns := by
    simp only [members1] at literals
    cases literals with
    | cons literal rest => exact ⟨_, _, rfl, literal, rest⟩
  obtain ⟨inside0, t0, at0, view0, rest0⟩ := elements_drop_cons elements0
  have one : (1#usize : Usize).val = 0 + 1 := by simp
  have zero : (0#usize : Usize).val = 0 := by simp
  obtain ⟨v, membersRun, value⟩ := literal_members_complete triples firsts xs.rest.val ns 1#usize
    (alloc.vec.Vec.new model.Literal) restLiterals (fun w m => readable w (by simp [members1, m]))
    (by rw [one, ← zero]; exact rest0) (by have h := xs.rest.property; rw [new_length]; omega)
  have long : alloc.vec.Vec.len firsts ≥ 1#usize := by
    have h : 0 < firsts.val.length := by rw [zero] at inside0; exact inside0
    clear * - h
    scalar_tac
  refine ⟨s', ?_, marked⟩
  rw [rdf_mapping.literal_list1]
  simp only [cellsRun, bind_ok, uncurry_apply_pair, long, ↓reduceIte, alloc.vec.Vec.index_slice_index,
    firsts_lookup firsts 0#usize inside0, element_at triples _ t0 at0,
    literal_complete t0.object xs.first n0 literal0 (readable xs.first (by simp [members1])) view0, membersRun]
  rw [non_empty_ext rfl (by rw [value]; simp)]

/-- The individuals of a list of at least two read back from its forward image. -/
theorem individual_list2_complete (triples : alloc.vec.Vec rdf.Triple) (xs : model.AtLeastTwo model.Individual)
    (cells : List rdf.BlankNode) (cellsLen : cells.length = (members2 xs).length) (nodup : cells.Nodup)
    (s : rdf_mapping.State) (pos : List Nat) (node : rdf.Object) (fuel : Usize)
    (view : objectView node = (listOf cells ((members2 xs).map individualNode)).1)
    (ready : Ready triples s pos (listOf cells ((members2 xs).map individualNode)).2 cells)
    (fuelOk : cells.length ≤ fuel.val) :
    ∃ s', rdf_mapping.individual_list2 triples node s fuel = .ok (some (xs, s')) ∧
      Marked s s' (fun i => i ∈ pos) cells := by
  have cellsMax : cells.length ≤ Usize.max := by have := fuel.hBounds; scalar_tac
  obtain ⟨firsts, news, s', cellsRun, firstsIs, elementsOk, marked⟩ := cells_complete triples cells
    ((members2 xs).map individualNode) (by simp [cellsLen]) nodup s pos node (alloc.vec.Vec.new Usize) fuel view ready
    fuelOk (by simp; omega)
  have elements0 := firsts_from_cells firstsIs elementsOk
  simp only [members2, List.map_cons] at elements0
  obtain ⟨inside0, t0, at0, view0, rest0⟩ := elements_drop_cons elements0
  have one : (1#usize : Usize).val = 0 + 1 := by simp
  have zero : (0#usize : Usize).val = 0 := by simp
  have two : (2#usize : Usize).val = 0 + 1 + 1 := by simp
  obtain ⟨inside1, t1, at1, view1, rest1⟩ := elements_drop_cons (index := 1#usize) (by rw [one, ← zero]; exact rest0)
  obtain ⟨v, membersRun, value⟩ := individual_members_complete triples firsts xs.rest.val 2#usize
    (alloc.vec.Vec.new model.Individual) (by rw [two, ← one]; exact rest1)
    (by have h := xs.rest.property; rw [new_length]; omega)
  have long : alloc.vec.Vec.len firsts ≥ 2#usize := by
    have h : 1 < firsts.val.length := by rw [one] at inside1; simpa using inside1
    clear * - h
    scalar_tac
  refine ⟨s', ?_, marked⟩
  rw [rdf_mapping.individual_list2]
  simp only [cellsRun, bind_ok, uncurry_apply_pair, long, ↓reduceIte, alloc.vec.Vec.index_slice_index,
    firsts_lookup firsts 0#usize inside0, element_at triples _ t0 at0, node_individual_complete t0.object xs.first view0,
    firsts_lookup firsts 1#usize inside1, element_at triples _ t1 at1, node_individual_complete t1.object xs.second view1,
    membersRun]
  rw [at_least_two_ext rfl rfl (by rw [value]; simp)]

/-! ### Facets -/

theorem tfacets_split {fs : List model.FacetRestriction} {s0 s1 : Supply} {ns : List Node} {ps : List Pattern}
    (h : TFacets fs s0 ns ps s1) : ∃ fresh, s0 = fresh ++ s1 ∧ SubjectsIn fresh ps := tfacets_fresh h

/-- The facet restriction of the blank element node at `firsts[index]`. -/
theorem facet_element_complete (triples : alloc.vec.Vec rdf.Triple) (firsts : alloc.vec.Vec Usize) (index : Usize)
    (f : model.FacetRestriction) (y : rdf.BlankNode) (value : Node) (literal : LiteralNode f.value value)
    (readable : LiteralReadable f.value) (inside : index.val < firsts.val.length) (t : rdf.Triple)
    (at_t : triples.val[firsts.val[index.val].val]? = some t) (view : objectView t.object = .blank y)
    (s : rdf_mapping.State) (i : Nat) (ready : Ready triples s [i] [⟨.blank y, f.facet.spelling.val, value⟩] [y]) :
    ∃ s', rdf_mapping.facet_element triples firsts index s = .ok (some (f, s')) ∧
      Marked s s' (fun j => j ∈ [i]) [y] := by
  have ready' : Ready triples s ([i] ++ []) (headPatterns y [(f.facet.spelling.val, value)] ++ []) (y :: []) := by
    simpa [headPatterns] using ready
  have heads := heads_of_ready ready' rfl (fun _ m => by simp at m) (by simp) (by simp)
  have unused := ready.free i (by simp)
  obtain ⟨found, foundVal, findRun⟩ := find_any_hit triples s y ready.complete heads unused
  obtain ⟨_, u, at_u, -, predicate, object⟩ := heads_at_triple heads (k := 0) rfl
  simp only [List.getElem_cons_zero] at predicate object
  cases elementIs : t.object with
  | Blank b =>
    rw [elementIs] at view
    have by' : b = y := by simpa [objectView] using view
    subst by'
    have m1 := marked_nil_take s found
    have room := ready.room
    obtain ⟨s2, recordRun, m2⟩ := record_ok { s with used := s.used.set found true } b (by simp at room ⊢; omega)
    refine ⟨s2, ?_, ?_⟩
    · rw [rdf_mapping.facet_element]
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        firsts_lookup firsts index inside, bind_ok, element_at triples _ t at_t, elementIs, findRun,
        main_lookup triples found u (by rw [foundVal]; exact at_u),
        literal_complete u.object f.value value literal readable object, take_correct, recordRun, iri_of_identity]
      have facet : ({ spelling := u.predicate.spelling } : model.Iri) = f.facet := iri_ext predicate
      rw [facet]
    · refine marked_same (marked_trans m1 m2) (fun j => ?_)
      simp [foundVal]
  | Iri _ => rw [elementIs] at view; simp [objectView] at view
  | Literal _ => rw [elementIs] at view; simp [objectView] at view

/-- The facet restrictions of the blank element nodes from `firsts[index]` on. -/
theorem facet_members_complete (triples : alloc.vec.Vec rdf.Triple) (firsts : alloc.vec.Vec Usize) :
    ∀ {fs : List model.FacetRestriction} {s0 s1 : Supply} {ns : List Node} {ps : List Pattern},
      TFacets fs s0 ns ps s1 → (∀ f ∈ fs, LiteralReadable f.value) →
      ∀ (fresh : Supply), s0 = fresh ++ s1 → fresh.Nodup →
      ∀ (index : Usize) (s : rdf_mapping.State) (pos : List Nat) (out : alloc.vec.Vec model.FacetRestriction),
        Elements triples.val (firsts.val.drop index.val) ns → Ready triples s pos ps fresh →
        out.val.length + fs.length ≤ Usize.max →
        ∃ v s', rdf_mapping.facet_members triples firsts index s out = .ok (some (v, s')) ∧ v.val = out.val ++ fs ∧
          Marked s s' (fun i => i ∈ pos) fresh := by
  intro fs s0 s1 ns ps h
  induction h with
  | nil s =>
    intro _ fresh split _ index st pos out elements ready _
    have empty : fresh = [] := by simpa using split
    subst empty
    have noPos : pos = [] := by have := at_length ready.holds; simpa using this
    subst noPos
    have done := elements_drop_nil elements
    refine ⟨out, st, ?_, by simp, ready_nil_marked st⟩
    rw [rdf_mapping.facet_members]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, show ¬ index.val < firsts.val.length by omega]
  | cons f fs y s s' value ns ps literal tail ih =>
    intro readable fresh split nodup index st pos out elements ready room
    obtain ⟨rest, restEq, restSubjects⟩ := tfacets_fresh tail
    have freshIs : fresh = y :: rest := by
      rw [restEq] at split
      have h : (y :: rest) ++ s' = fresh ++ s' := by simpa using split
      exact (List.append_cancel_right h).symm
    subst freshIs
    have yOut : y ∉ rest := (List.nodup_cons.mp nodup).1
    have nodupRest : rest.Nodup := (List.nodup_cons.mp nodup).2
    obtain ⟨i, rpos, rfl⟩ : ∃ i rpos, pos = i :: rpos := by
      have := at_length ready.holds
      match pos, this with
      | i :: rpos, _ => exact ⟨i, rpos, rfl⟩
    obtain ⟨inside, t, at_t, view, restElements⟩ := elements_drop_cons elements
    have ready3 : Ready triples st ([i] ++ rpos ++ []) ([⟨.blank y, f.facet.spelling.val, value⟩] ++ ps ++ [])
        ([y] ++ rest ++ []) := by simpa using ready
    have ready0 : Ready triples st ([] ++ [i] ++ rpos) ([] ++ [⟨.blank y, f.facet.spelling.val, value⟩] ++ ps)
        ([] ++ [y] ++ rest) := by simpa using ready
    have readyHead := ready_middle ready0 rfl rfl (by simpa using nodup) (fun _ m => by simp at m)
      (blank_subjects_of restSubjects) (marked_refl st) (fun _ h => h.elim) (by simp)
    obtain ⟨s2, elementRun, m1⟩ := facet_element_complete triples firsts index f y value literal
      (readable f (by simp)) inside t at_t view st i readyHead
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := firsts.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have outRoom : out.val.length < Usize.max := by simp at room; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out f outRoom)
    have len2 : rpos.length = ps.length := by have := at_length ready.holds; simpa using this
    have readyRest := ready_middle ready3 rfl len2
      (by simpa using nodup) (blank_subjects_head y [(f.facet.spelling.val, value)]) (fun _ m => by simp at m)
      m1 (fun j hj => by simpa using hj) (by simp)
    obtain ⟨v, s3, run, value', m2⟩ := ih (fun g m => readable g (List.mem_cons_of_mem _ m)) rest restEq nodupRest
      next s2 rpos pushed (by rw [nextIs]; exact restElements) readyRest (by rw [contents]; simp at room ⊢; omega)
    refine ⟨v, s3, ?_, by rw [value', contents]; simp, ?_⟩
    · rw [rdf_mapping.facet_members]
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, elementRun, bind_ok, uncurry_apply_pair,
        usize_max_val, outRoom, push, advance, run]
    · refine marked_same (marked_trans m1 m2) (fun j => ?_)
      simp only [List.mem_cons, List.mem_singleton]
      tauto

/-! ### Data ranges -/

/-- `data_range` reads `r` back from any node of its forward image. -/
def RangeReads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (r : model.DataRange) (s0 : Supply)
    (n : Node) (ps : List Pattern) (s1 : Supply) : Prop :=
  ∀ (fresh : Supply), s0 = fresh ++ s1 → fresh.Nodup →
  ∀ (s : rdf_mapping.State) (pos : List Nat) (node : rdf.Object) (fuel : Usize),
    objectView node = n → Ready triples s pos ps fresh → ps.length ≤ fuel.val →
    ∃ s', rdf_mapping.data_range triples kinds node s fuel = .ok (some (r, s')) ∧
      Marked s s' (fun i => i ∈ pos) fresh

/-- Data ranges in order, each read back. -/
inductive RangesRead (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) :
    List model.DataRange → Supply → List Node → List Pattern → Supply → Prop
  | nil (s : Supply) : RangesRead triples kinds [] s [] [] s
  | cons (r : model.DataRange) (rs : List model.DataRange) (s s1 s2 : Supply) (n : Node) (ns : List Node)
      (ps qs : List Pattern) : TDR r s n ps s1 → RangeReads triples kinds r s n ps s1 →
      RangesRead triples kinds rs s1 ns qs s2 → RangesRead triples kinds (r :: rs) s (n :: ns) (ps ++ qs) s2

theorem ranges_read_fresh {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {rs : List model.DataRange} {s0 s1 : Supply} {ns : List Node} {ps : List Pattern}
    (h : RangesRead triples kinds rs s0 ns ps s1) : ∃ fresh, s0 = fresh ++ s1 ∧ SubjectsIn fresh ps := by
  induction h with
  | nil s => exact ⟨[], by simp, subjects_in_nil _⟩
  | cons r rs s s1 s2 n ns ps qs head _ _ ih =>
    obtain ⟨f1, eq1, sub1⟩ := tdr_fresh head
    obtain ⟨f2, eq2, sub2⟩ := ih
    exact ⟨f1 ++ f2, by rw [eq1, eq2, List.append_assoc], subjects_pair sub1 sub2⟩

theorem ranges_read_length {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {rs : List model.DataRange} {s0 s1 : Supply} {ns : List Node} {ps : List Pattern}
    (h : RangesRead triples kinds rs s0 ns ps s1) : ns.length = rs.length := by
  induction h with
  | nil => rfl
  | cons => simp_all

theorem ranges_read_cons_inv {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {r : model.DataRange} {rs : List model.DataRange} {s0 s1 : Supply} {ns : List Node} {ps : List Pattern}
    (h : RangesRead triples kinds (r :: rs) s0 ns ps s1) :
    ∃ (sMid : Supply) (n : Node) (ns' : List Node) (p q : List Pattern), ns = n :: ns' ∧ ps = p ++ q ∧
      TDR r s0 n p sMid ∧ RangeReads triples kinds r s0 n p sMid ∧ RangesRead triples kinds rs sMid ns' q s1 := by
  cases h with
  | cons _ _ _ sMid _ n ns' p q head reads tail => exact ⟨sMid, n, ns', p, q, rfl, rfl, head, reads, tail⟩

theorem marked_fresh_eq {s s' : rdf_mapping.State} {m : Nat → Prop} {f f' : List rdf.BlankNode}
    (h : Marked s s' m f) (same : f = f') : Marked s s' m f' := by
  subst same; exact h

theorem fresh_split {f1 f2 fresh s1 s2 : Supply} (eq1 : f1 ++ s1 = fresh ++ s2) (eq2 : s1 = f2 ++ s2) :
    fresh = f1 ++ f2 := by
  rw [eq2] at eq1
  have h : (f1 ++ f2) ++ s2 = fresh ++ s2 := by simpa using eq1
  exact (List.append_cancel_right h).symm

/-- The data range of the element `firsts[index]`. -/
theorem range_element_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (firsts : alloc.vec.Vec Usize) (index : Usize) {r : model.DataRange} {s0 s1 : Supply} {n : Node}
    {ps : List Pattern} (reads : RangeReads triples kinds r s0 n ps s1) {fresh : Supply} (split : s0 = fresh ++ s1)
    (nodup : fresh.Nodup) {ns : List Node} (elements : Elements triples.val (firsts.val.drop index.val) (n :: ns))
    (s : rdf_mapping.State) (pos : List Nat) (fuel : Usize) (ready : Ready triples s pos ps fresh)
    (fuelOk : ps.length ≤ fuel.val) :
    ∃ s', rdf_mapping.range_element triples kinds firsts index s fuel = .ok (some (r, s')) ∧
      Marked s s' (fun i => i ∈ pos) fresh := by
  obtain ⟨inside, t, at_t, view, -⟩ := elements_drop_cons elements
  obtain ⟨s', run, marked⟩ := reads fresh split nodup s pos t.object fuel view ready fuelOk
  refine ⟨s', ?_, marked⟩
  rw [rdf_mapping.range_element]
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
    firsts_lookup firsts index inside, bind_ok, element_at triples _ t at_t, run]

/-- The data ranges of the elements from `firsts[index]` on. -/
theorem range_members_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (firsts : alloc.vec.Vec Usize) :
    ∀ {rs : List model.DataRange} {s0 s1 : Supply} {ns : List Node} {ps : List Pattern},
      RangesRead triples kinds rs s0 ns ps s1 → ∀ (fresh : Supply), s0 = fresh ++ s1 → fresh.Nodup →
      ∀ (index : Usize) (s : rdf_mapping.State) (pos : List Nat) (out : alloc.vec.Vec model.DataRange) (fuel : Usize),
        Elements triples.val (firsts.val.drop index.val) ns → Ready triples s pos ps fresh → ps.length ≤ fuel.val →
        out.val.length + rs.length ≤ Usize.max →
        ∃ v s', rdf_mapping.range_members triples kinds firsts index s out fuel = .ok (some (v, s')) ∧
          v.val = out.val ++ rs ∧ Marked s s' (fun i => i ∈ pos) fresh := by
  intro rs s0 s1 ns ps h
  induction h with
  | nil s =>
    intro fresh split _ index st pos out fuel elements ready _ _
    have empty : fresh = [] := by simpa using split
    subst empty
    have noPos : pos = [] := by have := at_length ready.holds; simpa using this
    subst noPos
    have done := elements_drop_nil elements
    refine ⟨out, st, ?_, by simp, ready_nil_marked st⟩
    rw [rdf_mapping.range_members]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, show ¬ index.val < firsts.val.length by omega]
  | cons r rs s s1 s2 n ns ps qs head reads tail ih =>
    intro fresh split nodup index st pos out fuel elements ready fuelOk room
    obtain ⟨f1, eq1, sub1⟩ := tdr_fresh head
    obtain ⟨f2, eq2, sub2⟩ := ranges_read_fresh tail
    have freshIs := fresh_split (by rw [← eq1]; exact split) eq2
    subst freshIs
    obtain ⟨pos1, pos2, rfl, at1, at2⟩ := at_split ready.holds
    have nodup1 : f1.Nodup := (List.nodup_append.mp nodup).1
    have nodup2 : f2.Nodup := (List.nodup_append.mp nodup).2.1
    have ready1 := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (by simpa using ready) rfl (at_length at1)
      (by simpa using nodup) (fun _ m => by simp at m) (blank_subjects_of sub2) (marked_refl st) (fun _ h => h.elim)
      (by simp)
    obtain ⟨inside, t, at_t, view, restElements⟩ := elements_drop_cons elements
    simp only [List.length_append] at fuelOk
    obtain ⟨s3, run1, m1⟩ := reads f1 eq1 nodup1 st pos1 t.object fuel view ready1 (by omega)
    have ready2 := ready_middle (pos3 := []) (ps3 := []) (f3 := []) (by simpa using ready) (at_length at1)
      (at_length at2) (by simpa using nodup) (blank_subjects_of sub1) (fun _ m => by simp at m) m1
      (fun _ h => h) (le_refl _)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := firsts.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have outRoom : out.val.length < Usize.max := by simp at room; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out r outRoom)
    obtain ⟨v, s4, run2, value, m2⟩ := ih f2 eq2 nodup2 next s3 pos2 pushed fuel (by rw [nextIs]; exact restElements)
      ready2 (by omega) (by rw [contents]; simp at room ⊢; omega)
    refine ⟨v, s4, ?_, by rw [value, contents]; simp, ?_⟩
    · rw [rdf_mapping.range_members]
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        firsts_lookup firsts index inside, bind_ok, element_at triples _ t at_t, run1, uncurry_apply_pair,
        usize_max_val, outRoom, push, advance, run2]
    · refine marked_same (marked_trans m1 m2) (fun j => ?_)
      simp only [List.mem_append]

/-- The data ranges of a list of at least two read back from its forward image. -/
theorem range_list2_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (xs : model.AtLeastTwo model.DataRange) (cells : List rdf.BlankNode) (nodes : List Node) (ps : List Pattern)
    (s0 s1 : Supply) (cellsLen : cells.length = (members2 xs).length)
    (members : RangesRead triples kinds (members2 xs) s0 nodes ps s1) (fresh : Supply) (split : s0 = fresh ++ s1)
    (nodup : (cells ++ fresh).Nodup) (s : rdf_mapping.State) (pos : List Nat) (node : rdf.Object) (fuel : Usize)
    (view : objectView node = (listOf cells nodes).1)
    (ready : Ready triples s pos ((listOf cells nodes).2 ++ ps) (cells ++ fresh))
    (fuelOk : ((listOf cells nodes).2 ++ ps).length ≤ fuel.val) :
    ∃ s', rdf_mapping.range_list2 triples kinds node s fuel = .ok (some (xs, s')) ∧
      Marked s s' (fun i => i ∈ pos) (cells ++ fresh) := by
  have nodesLen := ranges_read_length members
  have lists := list_of_length cells nodes (by rw [cellsLen, nodesLen])
  obtain ⟨f, eqf, subf⟩ := ranges_read_fresh members
  have freshIs : fresh = f := by
    rw [eqf] at split
    exact (List.append_cancel_right split).symm
  subst freshIs
  obtain ⟨cpos, mpos, rfl, atC, atM⟩ := at_split ready.holds
  have nodupCells : cells.Nodup := (List.nodup_append.mp nodup).1
  have nodupMembers : fresh.Nodup := (List.nodup_append.mp nodup).2.1
  have readyCells := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (by simpa using ready) rfl (at_length atC)
    (by simpa using nodup) (fun _ m => by simp at m) (blank_subjects_of subf) (marked_refl s) (fun _ h => h.elim)
    (by simp)
  simp only [List.length_append, lists] at fuelOk
  obtain ⟨firsts, news, s2, cellsRun, firstsIs, elementsOk, mCells⟩ := cells_complete triples cells nodes
    (by rw [cellsLen, nodesLen]) nodupCells s cpos node (alloc.vec.Vec.new Usize) fuel view readyCells (by omega)
    (by simp; have := fuel.hBounds; scalar_tac)
  have readyMembers := ready_middle (pos3 := []) (ps3 := []) (f3 := []) (by simpa using ready) (at_length atC)
    (at_length atM) (by simpa using nodup) (blank_subjects_of (list_of_subjects cells nodes))
    (fun _ m => by simp at m) mCells (fun _ h => h) (le_refl _)
  have elements0 := firsts_from_cells firstsIs elementsOk
  -- the members: first, second and the rest
  obtain ⟨sA, nA, nsA, pA, qA, rfl, rfl, headA, readsA, tailA⟩ := ranges_read_cons_inv members
  obtain ⟨sB, nB, nsB, pB, pC, rfl, rfl, headB, readsB, tailC⟩ := ranges_read_cons_inv tailA
  obtain ⟨fA, eqA, subA⟩ := tdr_fresh headA
  obtain ⟨fB, eqB, subB⟩ := tdr_fresh headB
  obtain ⟨fC, eqC, subC⟩ := ranges_read_fresh tailC
  have freshIs : fresh = fA ++ (fB ++ fC) := by
    rw [eqA, eqB, eqC] at eqf
    have h : (fA ++ (fB ++ fC)) ++ s1 = fresh ++ s1 := by simpa using eqf
    exact (List.append_cancel_right h).symm
  subst freshIs
  obtain ⟨posA, posBC, rfl, atA, atBC⟩ := at_split atM
  obtain ⟨posB, posC, rfl, atB, atC'⟩ := at_split atBC
  have nodupAll := nodupMembers
  have readyA := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (pos3 := posB ++ posC) (ps3 := pB ++ pC)
    (f3 := fB ++ fC) (by simpa using readyMembers) rfl (at_length atA) (by simpa using nodupAll)
    (fun _ m => by simp at m) (blank_subjects_of (subjects_pair subB subC)) (marked_refl s2) (fun _ h => h.elim)
    (by simp)
  simp only [List.length_append] at fuelOk
  obtain ⟨inside0, t0, at0, view0, rest0⟩ := elements_drop_cons elements0
  obtain ⟨sA', runA, mA⟩ := readsA fA eqA (List.nodup_append.mp nodupAll).1 s2 posA t0.object fuel view0 readyA
    (by omega)
  have readyB := ready_middle (pos1 := posA) (ps1 := pA) (f1 := fA) (pos3 := posC) (ps3 := pC)
    (f3 := fC) (by simpa [List.append_assoc] using readyMembers) (at_length atA) (at_length atB)
    (by simpa [List.append_assoc] using nodupAll) (blank_subjects_of subA) (blank_subjects_of subC) mA
    (fun _ h => h) (le_refl _)
  have one : (1#usize : Usize).val = 0 + 1 := by simp
  have zero : (0#usize : Usize).val = 0 := by simp
  obtain ⟨inside1, t1, at1, view1, rest1⟩ := elements_drop_cons (index := 1#usize) (by rw [one, ← zero]; exact rest0)
  obtain ⟨sB', runB, mB⟩ := readsB fB eqB (List.nodup_append.mp (List.nodup_append.mp nodupAll).2.1).1 sA' posB
    t1.object fuel view1 readyB (by omega)
  have mAB := marked_trans mA mB
  have readyC := ready_middle (pos1 := posA ++ posB) (ps1 := pA ++ pB) (f1 := fA ++ fB) (pos3 := [])
    (ps3 := []) (f3 := []) (by simpa [List.append_assoc] using readyMembers)
    (by simp [at_length atA, at_length atB]) (at_length atC')
    (by simpa [List.append_assoc] using nodupAll) (blank_subjects_of (subjects_pair subA subB))
    (fun _ m => by simp at m) mAB (fun j hj => by simp only [List.mem_append]; exact hj) (le_refl _)
  have two : (2#usize : Usize).val = 0 + 1 + 1 := by simp
  obtain ⟨v, sC', runC, value, mC⟩ := range_members_complete triples kinds firsts tailC fC eqC
    (List.nodup_append.mp (List.nodup_append.mp nodupAll).2.1).2.1 2#usize sB' posC
    (alloc.vec.Vec.new model.DataRange) fuel (by rw [two, ← one]; exact rest1) readyC (by omega)
    (by rw [new_length]; have := xs.rest.property; omega)
  have elementA : rdf_mapping.range_element triples kinds firsts 0#usize s2 fuel = .ok (some (xs.first, sA')) := by
    rw [rdf_mapping.range_element]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside0, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      firsts_lookup firsts 0#usize inside0, bind_ok, element_at triples _ t0 at0, runA]
  have elementB : rdf_mapping.range_element triples kinds firsts 1#usize sA' fuel = .ok (some (xs.second, sB')) := by
    rw [rdf_mapping.range_element]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside1, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      firsts_lookup firsts 1#usize inside1, bind_ok, element_at triples _ t1 at1, runB]
  refine ⟨sC', ?_, ?_⟩
  · rw [rdf_mapping.range_list2]
    simp only [cellsRun, bind_ok, uncurry_apply_pair, elementA, elementB, runC]
    rw [at_least_two_ext rfl rfl (by rw [value]; simp)]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_trans mCells mAB) mC) (by simp)) (fun j => ?_)
    simp only [List.mem_append, List.append_assoc]
    tauto

/-! ### The data range constructs -/

/-- The head of the construct of a blank node: its triples about the node at
    the first positions, and the rest after. -/
theorem construct_setup {triples : alloc.vec.Vec rdf.Triple} {s : rdf_mapping.State} {pos : List Nat}
    {x : rdf.BlankNode} {head : List (List U8 × Node)} {rest : List Pattern} {f : List rdf.BlankNode}
    (ready : Ready triples s pos (headPatterns x head ++ rest) (x :: f)) (sub : BlankSubjects f rest)
    (outside : x ∉ f) (distinct : (head.map (·.1)).Nodup) :
    ∃ hpos rpos, pos = hpos ++ rpos ∧ hpos.length = head.length ∧ rpos.length = rest.length ∧
      HeadsAt triples.val s.used.val x hpos head := by
  obtain ⟨hpos, rpos, rfl, atH, atR⟩ := at_split ready.holds
  have lenH : hpos.length = head.length := by rw [at_length atH, head_patterns_length]
  exact ⟨hpos, rpos, rfl, lenH, at_length atR, heads_of_ready ready lenH sub outside distinct⟩

/-- `data_range` goes from a blank node typed `rdfs:Datatype` to its construct. -/
theorem data_range_blank (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (x : rdf.BlankNode)
    (s : rdf_mapping.State) (fuel : Usize)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {hpos : List Nat} {head : List (List U8 × Node)} (heads : HeadsAt triples.val s.used.val x hpos head) {i : Nat}
    (hi : hpos[0]? = some i) (typed : ∀ h : 0 < head.length, head[0] = (rdfType, .iri rdfsDatatype))
    (unused : s.used.val[i]? = some false) (room : s.blanks.val.length < Usize.max) (positive : 0 < fuel.val) :
    ∃ (s1 : rdf_mapping.State) (fewer : Usize), fewer.val + 1 = fuel.val ∧ Marked s s1 (fun j => j ∈ [i]) [x] ∧
      rdf_mapping.data_range triples kinds (.Blank x) s fuel = rdf_mapping.range_construct triples kinds x s1 fewer := by
  obtain ⟨found, foundVal, findRun⟩ := find_type_hit triples s x complete heads hi rdfsDatatype typed unused
  obtain ⟨s1, recordRun, m2⟩ := record_ok { s with used := s.used.set found true } x room
  obtain ⟨fewer, back, fewerValue⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := fuel) (y := 1#usize) (by scalar_tac))
  refine ⟨s1, fewer, by simp at fewerValue; omega, ?_, ?_⟩
  · refine marked_same (marked_trans (marked_nil_take s found) m2) (fun j => ?_)
    simp [foundVal]
  · have pos' : fuel > 0#usize := by scalar_tac
    rw [rdf_mapping.data_range]
    simp only [pos', ↓reduceIte, lift, bind_ok, findRun, array_slice_val, rdfsDatatype, take_correct, recordRun, back]

theorem heads_rest {triples : List rdf.Triple} {used used' : List Bool} {x : rdf.BlankNode} {hpos : List Nat}
    {head : List (List U8 × Node)} (heads : HeadsAt triples used x hpos head) {m : Nat → Prop}
    {g : List rdf.BlankNode} {s s' : rdf_mapping.State} (same : used = s.used.val) (same' : used' = s'.used.val)
    (marked : Marked s s' m g) : HeadsAt triples used' x hpos head := by
  subst same; subst same'
  exact heads_at_mono heads (fun j => marked_back marked)

/-- Reading the members of a data range construct: the list after the head. -/
theorem list_range_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (key : List U8)
    (construct : model.AtLeastTwo model.DataRange → model.DataRange) (misses : List (List U8))
    (dispatch : ∀ (x : rdf.BlankNode) (s : rdf_mapping.State) (fuel : Usize) (i : Nat) (found : Usize) (t : rdf.Triple),
      found.val = i → triples.val[i]? = some t →
      (∀ k : Slice U8, k.val = key → rdf_mapping.find triples s x k = .ok (some found)) →
      (∀ P ∈ misses, ∀ k : Slice U8, k.val = P → rdf_mapping.find triples s x k = .ok none) →
      ∀ (xs' : model.AtLeastTwo model.DataRange) (s'' : rdf_mapping.State),
      rdf_mapping.range_list2 triples kinds t.object { s with used := s.used.set found true } fuel = .ok (some (xs', s'')) →
      rdf_mapping.range_construct triples kinds x s fuel = .ok (some (construct xs', s'')))
    (keyType : key ≠ rdfType) (missType : ∀ P ∈ misses, P ≠ rdfType) (missKey : ∀ P ∈ misses, P ≠ key)
    (xs : model.AtLeastTwo model.DataRange) (x : rdf.BlankNode) (cells : List rdf.BlankNode) (s s' : Supply)
    (nodes : List Node) (ps : List Pattern) (cellsLen : cells.length = (members2 xs).length)
    (members : RangesRead triples kinds (members2 xs) s nodes ps s') :
    RangeReads triples kinds (construct xs) (x :: (cells ++ s)) (.blank x)
      (⟨.blank x, rdfType, .iri rdfsDatatype⟩ :: ⟨.blank x, key, (listOf cells nodes).1⟩ ::
        ((listOf cells nodes).2 ++ ps)) s' := by
  intro fresh split nodup st pos node fuel view ready fuelOk
  obtain ⟨f, eqf, subf⟩ := ranges_read_fresh members
  have freshIs : fresh = x :: (cells ++ f) := by
    rw [eqf] at split
    have h : (x :: (cells ++ f)) ++ s' = fresh ++ s' := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  cases node with
  | Iri _ => simp [objectView] at view
  | Literal _ => simp [objectView] at view
  | Blank b =>
    have bx : b = x := by simpa [objectView] using view
    subst bx
    let head : List (List U8 × Node) := [(rdfType, .iri rdfsDatatype), (key, (listOf cells nodes).1)]
    have outside : b ∉ cells ++ f := (List.nodup_cons.mp nodup).1
    have restSubjects : BlankSubjects (cells ++ f) ((listOf cells nodes).2 ++ ps) :=
      blank_subjects_of (subjects_pair (list_of_subjects cells nodes) subf)
    have ready' : Ready triples st pos (headPatterns b head ++ ((listOf cells nodes).2 ++ ps)) (b :: (cells ++ f)) := by
      simpa [headPatterns, head] using ready
    obtain ⟨hpos, rpos, rfl, lenH, lenR, heads⟩ := construct_setup ready' restSubjects outside
      (by simp [head]; exact fun h => keyType h.symm)
    obtain ⟨h0, h1, rfl⟩ : ∃ h0 h1, hpos = [h0, h1] := by
      match hpos, lenH with
      | [h0, h1], _ => exact ⟨h0, h1, rfl⟩
    have nodupPos := ready.nodup
    have h01 : h0 ≠ h1 := by intro same; subst same; simp at nodupPos
    have room := ready.room
    simp only [List.length_cons, List.length_append] at fuelOk room
    obtain ⟨s1, fewer, fewerIs, m1, rangeRun⟩ := data_range_blank triples kinds b st fuel ready.complete heads
      (i := h0) rfl (fun _ => rfl) (ready.free h0 (by simp)) (by omega) (by omega)
    have unused1 : s1.used.val[h1]? = some false :=
      marked_unused m1 (ready.free h1 (by simp)) (by simp; exact fun h => h01 h.symm)
    have heads1 := heads_rest heads rfl rfl m1
    obtain ⟨found, foundVal, findRun⟩ := find_hit triples s1 b (by rw [m1.subjects]; exact ready.complete) heads1
      (k := 1) rfl key (fun _ => rfl) unused1
    obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads (k := 1) rfl
    have missRuns : ∀ P ∈ misses, ∀ k : Slice U8, k.val = P → rdf_mapping.find triples s1 b k = .ok none := by
      intro P member
      apply find_miss triples s1 b heads1 P
      intro k hk
      match k, hk with
      | 0, _ => exact (missType P member).symm
      | 1, _ => exact (missKey P member).symm
    have m2 := marked_nil_take s1 found
    have m12 := marked_trans m1 m2
    have readyRest := ready_middle (pos1 := [h0, h1]) (pos3 := []) (ps3 := []) (f3 := [])
      (by simpa [head, headPatterns] using ready) rfl (by simpa using lenR) (by simpa using nodup)
      (blank_subjects_head b head) (fun _ m => by simp at m) m12
      (fun j hj => by
        simp only [List.mem_singleton] at hj
        rcases hj with h | h
        · simp [h]
        · simp [h, foundVal]) (by simp)
    obtain ⟨s3, listRun, m3⟩ := range_list2_complete triples kinds xs cells nodes ps s s' cellsLen members f eqf
      (List.nodup_cons.mp nodup).2 { s1 with used := s1.used.set found true } rpos t.object fewer
      (by simpa [head] using object) readyRest (by simp; omega)
    refine ⟨s3, ?_, ?_⟩
    · rw [rangeRun]
      exact dispatch b s1 fewer h1 found t foundVal at_t findRun missRuns xs s3 listRun
    · refine marked_same (marked_fresh_eq (marked_trans m12 m3) (by simp)) (fun j => ?_)
      simp only [List.mem_cons, List.mem_append, List.mem_singleton, foundVal]
      tauto

theorem range_intersection_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (xs : model.AtLeastTwo model.DataRange) (x : rdf.BlankNode) (cells : List rdf.BlankNode) (s s' : Supply)
    (nodes : List Node) (ps : List Pattern) (cellsLen : cells.length = (members2 xs).length)
    (members : RangesRead triples kinds (members2 xs) s nodes ps s') :
    RangeReads triples kinds (.Intersection xs) (x :: (cells ++ s)) (.blank x)
      (⟨.blank x, rdfType, .iri rdfsDatatype⟩ :: ⟨.blank x, owlIntersectionOf, (listOf cells nodes).1⟩ ::
        ((listOf cells nodes).2 ++ ps)) s' :=
  list_range_reads triples kinds owlIntersectionOf .Intersection []
    (fun x s fuel i found t foundVal at_t findRun _ xs' s'' listRun => by
      rw [rdf_mapping.range_construct]
      simp only [lift, bind_ok, findRun, array_slice_val, owlIntersectionOf, take_correct,
        alloc.vec.Vec.index_slice_index, main_lookup triples found t (by rw [foundVal]; exact at_t), listRun,
        uncurry_apply_pair])
    (by simp [owlIntersectionOf, rdfType]) (by simp) (by simp) xs x cells s s' nodes ps cellsLen members

theorem range_union_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (xs : model.AtLeastTwo model.DataRange) (x : rdf.BlankNode) (cells : List rdf.BlankNode) (s s' : Supply)
    (nodes : List Node) (ps : List Pattern) (cellsLen : cells.length = (members2 xs).length)
    (members : RangesRead triples kinds (members2 xs) s nodes ps s') :
    RangeReads triples kinds (.Union xs) (x :: (cells ++ s)) (.blank x)
      (⟨.blank x, rdfType, .iri rdfsDatatype⟩ :: ⟨.blank x, owlUnionOf, (listOf cells nodes).1⟩ ::
        ((listOf cells nodes).2 ++ ps)) s' :=
  list_range_reads triples kinds owlUnionOf .Union [owlIntersectionOf]
    (fun x s fuel i found t foundVal at_t findRun misses xs' s'' listRun => by
      have miss := misses owlIntersectionOf (by simp)
      rw [rdf_mapping.range_construct]
      simp only [lift, bind_ok, miss, findRun, array_slice_val, owlIntersectionOf, owlUnionOf, take_correct,
        alloc.vec.Vec.index_slice_index, main_lookup triples found t (by rw [foundVal]; exact at_t), listRun,
        uncurry_apply_pair])
    (by simp [owlUnionOf, rdfType]) (by simp [owlIntersectionOf, rdfType])
    (by simp [owlIntersectionOf, owlUnionOf]) xs x cells s s' nodes ps cellsLen members

theorem miss_of_heads {triples : alloc.vec.Vec rdf.Triple} {s : rdf_mapping.State} {x : rdf.BlankNode}
    {hpos : List Nat} {head : List (List U8 × Node)} (heads : HeadsAt triples.val s.used.val x hpos head)
    (P : List U8) (absent : P ∉ head.map (·.1)) :
    ∀ k : Slice U8, k.val = P → rdf_mapping.find triples s x k = .ok none := by
  apply find_miss triples s x heads P
  intro k hk same
  apply absent
  rw [← same]
  exact List.mem_map.mpr ⟨head[k], List.getElem_mem hk, rfl⟩

theorem range_complement_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (r : model.DataRange) (x : rdf.BlankNode) (s s' : Supply) (n : Node) (ps : List Pattern)
    (inner : TDR r s n ps s') (reads : RangeReads triples kinds r s n ps s') :
    RangeReads triples kinds (.Complement r) (x :: s) (.blank x)
      (⟨.blank x, rdfType, .iri rdfsDatatype⟩ :: ⟨.blank x, owlDatatypeComplementOf, n⟩ :: ps) s' := by
  intro fresh split nodup st pos node fuel view ready fuelOk
  obtain ⟨f, eqf, subf⟩ := tdr_fresh inner
  have freshIs : fresh = x :: f := by
    rw [eqf] at split
    have h : (x :: f) ++ s' = fresh ++ s' := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  cases node with
  | Iri _ => simp [objectView] at view
  | Literal _ => simp [objectView] at view
  | Blank b =>
    have bx : b = x := by simpa [objectView] using view
    subst bx
    let head : List (List U8 × Node) := [(rdfType, .iri rdfsDatatype), (owlDatatypeComplementOf, n)]
    have outside : b ∉ f := (List.nodup_cons.mp nodup).1
    have ready' : Ready triples st pos (headPatterns b head ++ ps) (b :: f) := by
      simpa [headPatterns, head] using ready
    obtain ⟨hpos, rpos, rfl, lenH, lenR, heads⟩ := construct_setup ready' (blank_subjects_of subf) outside
      (by simp [head, rdfType, owlDatatypeComplementOf])
    obtain ⟨h0, h1, rfl⟩ : ∃ h0 h1, hpos = [h0, h1] := by
      match hpos, lenH with
      | [h0, h1], _ => exact ⟨h0, h1, rfl⟩
    have nodupPos := ready.nodup
    have h01 : h0 ≠ h1 := by intro same; subst same; simp at nodupPos
    have room := ready.room
    simp only [List.length_cons] at fuelOk room
    obtain ⟨s1, fewer, fewerIs, m1, rangeRun⟩ := data_range_blank triples kinds b st fuel ready.complete heads
      (i := h0) rfl (fun _ => rfl) (ready.free h0 (by simp)) (by omega) (by omega)
    have unused1 : s1.used.val[h1]? = some false :=
      marked_unused m1 (ready.free h1 (by simp)) (by simp; exact fun h => h01 h.symm)
    have heads1 := heads_rest heads rfl rfl m1
    have complete1 : SubjectsComplete triples.val s1.subjects.val (alloc.vec.Vec.len s1.subjects)
        triples.val.length := by rw [m1.subjects]; exact ready.complete
    obtain ⟨found, foundVal, findRun⟩ := find_hit triples s1 b complete1 heads1 (k := 1) rfl owlDatatypeComplementOf
      (fun _ => rfl) unused1
    obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads (k := 1) rfl
    have missI := miss_of_heads heads1 owlIntersectionOf (by simp [head, rdfType, owlIntersectionOf,
      owlDatatypeComplementOf])
    have missU := miss_of_heads heads1 owlUnionOf (by simp [head, rdfType, owlUnionOf, owlDatatypeComplementOf])
    have m2 := marked_nil_take s1 found
    have m12 := marked_trans m1 m2
    have readyRest := ready_middle (pos1 := [h0, h1]) (pos3 := []) (ps3 := []) (f3 := [])
      (by simpa [head, headPatterns] using ready) rfl (by simpa using lenR) (by simpa using nodup)
      (blank_subjects_head b head) (fun _ m => by simp at m) m12
      (fun j hj => by
        simp only [List.mem_singleton] at hj
        rcases hj with h | h
        · simp [h]
        · simp [h, foundVal]) (by simp)
    obtain ⟨s3, innerRun, m3⟩ := reads f eqf (List.nodup_cons.mp nodup).2 { s1 with used := s1.used.set found true }
      rpos t.object fewer (by simpa [head] using object) readyRest (by omega)
    refine ⟨s3, ?_, ?_⟩
    · rw [rangeRun, rdf_mapping.range_construct]
      simp only [lift, bind_ok, missI, missU, findRun, array_slice_val, owlIntersectionOf, owlUnionOf,
        owlDatatypeComplementOf, take_correct, alloc.vec.Vec.index_slice_index,
        main_lookup triples found t (by rw [foundVal]; exact at_t), innerRun, uncurry_apply_pair]
    · refine marked_same (marked_fresh_eq (marked_trans m12 m3) (by simp)) (fun j => ?_)
      simp only [List.mem_cons, List.mem_append, List.mem_singleton, foundVal]
      tauto

theorem range_one_of_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (xs : model.NonEmpty model.Literal) (x : rdf.BlankNode) (cells : List rdf.BlankNode) (s : Supply)
    (nodes : List Node) (cellsLen : cells.length = (members1 xs).length)
    (literals : List.Forall₂ LiteralNode (members1 xs) nodes) (readable : ∀ v ∈ members1 xs, LiteralReadable v) :
    RangeReads triples kinds (.OneOf xs) (x :: (cells ++ s)) (.blank x)
      (⟨.blank x, rdfType, .iri rdfsDatatype⟩ :: ⟨.blank x, owlOneOf, (listOf cells nodes).1⟩ ::
        (listOf cells nodes).2) s := by
  intro fresh split nodup st pos node fuel view ready fuelOk
  have freshIs : fresh = x :: cells := by
    have h : (x :: cells) ++ s = fresh ++ s := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  have nodesLen := List.Forall₂.length_eq literals
  have lists := list_of_length cells nodes (by rw [cellsLen, nodesLen])
  cases node with
  | Iri _ => simp [objectView] at view
  | Literal _ => simp [objectView] at view
  | Blank b =>
    have bx : b = x := by simpa [objectView] using view
    subst bx
    let head : List (List U8 × Node) := [(rdfType, .iri rdfsDatatype), (owlOneOf, (listOf cells nodes).1)]
    have outside : b ∉ cells := (List.nodup_cons.mp nodup).1
    have ready' : Ready triples st pos (headPatterns b head ++ (listOf cells nodes).2) (b :: cells) := by
      simpa [headPatterns, head] using ready
    obtain ⟨hpos, rpos, rfl, lenH, lenR, heads⟩ := construct_setup ready'
      (blank_subjects_of (list_of_subjects cells nodes)) outside (by simp [head, rdfType, owlOneOf])
    obtain ⟨h0, h1, rfl⟩ : ∃ h0 h1, hpos = [h0, h1] := by
      match hpos, lenH with
      | [h0, h1], _ => exact ⟨h0, h1, rfl⟩
    have nodupPos := ready.nodup
    have h01 : h0 ≠ h1 := by intro same; subst same; simp at nodupPos
    have room := ready.room
    simp only [List.length_cons, lists] at fuelOk room
    obtain ⟨s1, fewer, fewerIs, m1, rangeRun⟩ := data_range_blank triples kinds b st fuel ready.complete heads
      (i := h0) rfl (fun _ => rfl) (ready.free h0 (by simp)) (by omega) (by omega)
    have unused1 : s1.used.val[h1]? = some false :=
      marked_unused m1 (ready.free h1 (by simp)) (by simp; exact fun h => h01 h.symm)
    have heads1 := heads_rest heads rfl rfl m1
    have complete1 : SubjectsComplete triples.val s1.subjects.val (alloc.vec.Vec.len s1.subjects)
        triples.val.length := by rw [m1.subjects]; exact ready.complete
    obtain ⟨found, foundVal, findRun⟩ := find_hit triples s1 b complete1 heads1 (k := 1) rfl owlOneOf
      (fun _ => rfl) unused1
    obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads (k := 1) rfl
    have missI := miss_of_heads heads1 owlIntersectionOf (by simp [head, rdfType, owlIntersectionOf, owlOneOf])
    have missU := miss_of_heads heads1 owlUnionOf (by simp [head, rdfType, owlUnionOf, owlOneOf])
    have missC := miss_of_heads heads1 owlDatatypeComplementOf
      (by simp [head, rdfType, owlDatatypeComplementOf, owlOneOf])
    have m2 := marked_nil_take s1 found
    have m12 := marked_trans m1 m2
    have readyRest := ready_middle (pos1 := [h0, h1]) (pos3 := []) (ps3 := []) (f3 := [])
      (by simpa [head, headPatterns] using ready) rfl (by simpa using lenR) (by simpa using nodup)
      (blank_subjects_head b head) (fun _ m => by simp at m) m12
      (fun j hj => by
        simp only [List.mem_singleton] at hj
        rcases hj with h | h
        · simp [h]
        · simp [h, foundVal]) (by simp)
    obtain ⟨s3, listRun, m3⟩ := literal_list1_complete triples xs cells nodes cellsLen literals readable
      (List.nodup_cons.mp nodup).2 { s1 with used := s1.used.set found true } rpos t.object fewer
      (by simpa [head] using object) readyRest (by omega)
    refine ⟨s3, ?_, ?_⟩
    · rw [rangeRun, rdf_mapping.range_construct]
      simp only [lift, bind_ok, missI, missU, missC, findRun, array_slice_val, owlIntersectionOf, owlUnionOf,
        owlDatatypeComplementOf, owlOneOf, take_correct, alloc.vec.Vec.index_slice_index,
        main_lookup triples found t (by rw [foundVal]; exact at_t), listRun, uncurry_apply_pair]
    · refine marked_same (marked_fresh_eq (marked_trans m12 m3) (by simp)) (fun j => ?_)
      simp only [List.mem_cons, List.mem_append, List.mem_singleton, foundVal]
      tauto

theorem tfacets_cons_inv {f : model.FacetRestriction} {fs : List model.FacetRestriction} {s0 s1 : Supply}
    {ns : List Node} {ps : List Pattern} (h : TFacets (f :: fs) s0 ns ps s1) :
    ∃ (y : rdf.BlankNode) (s : Supply) (value : Node) (ns' : List Node) (ps' : List Pattern),
      s0 = y :: s ∧ ns = .blank y :: ns' ∧ ps = ⟨.blank y, f.facet.spelling.val, value⟩ :: ps' ∧
      LiteralNode f.value value ∧ TFacets fs s ns' ps' s1 := by
  cases h with
  | cons _ _ y s _ value ns' ps' literal tail => exact ⟨y, s, value, ns', ps', rfl, rfl, rfl, literal, tail⟩

theorem range_restriction_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (d : model.Datatype) (xs : model.NonEmpty model.FacetRestriction) (x : rdf.BlankNode)
    (cells : List rdf.BlankNode) (s s' : Supply) (nodes : List Node) (ps : List Pattern)
    (cellsLen : cells.length = (members1 xs).length) (facets : TFacets (members1 xs) s nodes ps s')
    (readable : ∀ f ∈ members1 xs, LiteralReadable f.value) :
    RangeReads triples kinds (.Restriction d xs) (x :: (cells ++ s)) (.blank x)
      (⟨.blank x, rdfType, .iri rdfsDatatype⟩ :: ⟨.blank x, owlOnDatatype, iriNode d.iri⟩ ::
        ⟨.blank x, owlWithRestrictions, (listOf cells nodes).1⟩ :: ((listOf cells nodes).2 ++ ps)) s' := by
  intro fresh split nodup st pos node fuel view ready fuelOk
  obtain ⟨f, eqf, subf⟩ := tfacets_fresh facets
  have freshIs : fresh = x :: (cells ++ f) := by
    rw [eqf] at split
    have h : (x :: (cells ++ f)) ++ s' = fresh ++ s' := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  have nodesLen := tfacets_length facets
  have lists := list_of_length cells nodes (by rw [cellsLen, nodesLen])
  cases node with
  | Iri _ => simp [objectView] at view
  | Literal _ => simp [objectView] at view
  | Blank b =>
    have bx : b = x := by simpa [objectView] using view
    subst bx
    let head : List (List U8 × Node) :=
      [(rdfType, .iri rdfsDatatype), (owlOnDatatype, iriNode d.iri), (owlWithRestrictions, (listOf cells nodes).1)]
    have outside : b ∉ cells ++ f := (List.nodup_cons.mp nodup).1
    have restSubjects : BlankSubjects (cells ++ f) ((listOf cells nodes).2 ++ ps) :=
      blank_subjects_of (subjects_pair (list_of_subjects cells nodes) subf)
    have ready' : Ready triples st pos (headPatterns b head ++ ((listOf cells nodes).2 ++ ps)) (b :: (cells ++ f)) := by
      simpa [headPatterns, head] using ready
    obtain ⟨hpos, rpos, rfl, lenH, lenR, heads⟩ := construct_setup ready' restSubjects outside
      (by simp [head, rdfType, owlOnDatatype, owlWithRestrictions])
    obtain ⟨h0, h1, h2, rfl⟩ : ∃ h0 h1 h2, hpos = [h0, h1, h2] := by
      match hpos, lenH with
      | [h0, h1, h2], _ => exact ⟨h0, h1, h2, rfl⟩
    have nodupPos := ready.nodup
    have h01 : h0 ≠ h1 := by intro same; subst same; simp at nodupPos
    have h02 : h0 ≠ h2 := by intro same; subst same; simp at nodupPos
    have h12 : h1 ≠ h2 := by intro same; subst same; simp at nodupPos
    have room := ready.room
    simp only [List.length_cons, List.length_append, lists] at fuelOk room
    obtain ⟨s1, fewer, fewerIs, m1, rangeRun⟩ := data_range_blank triples kinds b st fuel ready.complete heads
      (i := h0) rfl (fun _ => rfl) (ready.free h0 (by simp)) (by omega) (by omega)
    have heads1 := heads_rest heads rfl rfl m1
    have complete1 : SubjectsComplete triples.val s1.subjects.val (alloc.vec.Vec.len s1.subjects)
        triples.val.length := by rw [m1.subjects]; exact ready.complete
    have unused1 : s1.used.val[h1]? = some false :=
      marked_unused m1 (ready.free h1 (by simp)) (by simp; exact fun h => h01 h.symm)
    obtain ⟨found1, found1Val, find1⟩ := find_hit triples s1 b complete1 heads1 (k := 1) rfl owlOnDatatype
      (fun _ => rfl) unused1
    obtain ⟨_, t1, at1, -, -, object1⟩ := heads_at_triple heads (k := 1) rfl
    have missI := miss_of_heads heads1 owlIntersectionOf
      (by simp [head, rdfType, owlIntersectionOf, owlOnDatatype, owlWithRestrictions])
    have missU := miss_of_heads heads1 owlUnionOf
      (by simp [head, rdfType, owlUnionOf, owlOnDatatype, owlWithRestrictions])
    have missC := miss_of_heads heads1 owlDatatypeComplementOf
      (by simp [head, rdfType, owlDatatypeComplementOf, owlOnDatatype, owlWithRestrictions])
    have missO := miss_of_heads heads1 owlOneOf
      (by simp [head, rdfType, owlOneOf, owlOnDatatype, owlWithRestrictions])
    have m2 := marked_nil_take s1 found1
    let s2 : rdf_mapping.State := { s1 with used := s1.used.set found1 true }
    have m12 := marked_trans m1 m2
    have unused2 : s2.used.val[h2]? = some false :=
      marked_unused m12 (ready.free h2 (by simp)) (by
        simp only [List.mem_singleton, found1Val]
        intro h
        rcases h with h | h
        · exact h02 h.symm
        · exact h12 h.symm)
    have heads2 := heads_rest heads rfl rfl m12
    obtain ⟨found2, found2Val, find2⟩ := find_hit triples s2 b (by rw [m12.subjects]; exact ready.complete) heads2
      (k := 2) rfl owlWithRestrictions (fun _ => rfl) unused2
    obtain ⟨_, t2, at2, -, -, object2⟩ := heads_at_triple heads (k := 2) rfl
    have m3 := marked_nil_take s2 found2
    have m123 := marked_trans m12 m3
    -- the list cells, then the facets
    obtain ⟨cpos, fpos, rfl, atC, atF⟩ := at_split (at_append_inv ready'.holds (by rw [head_patterns_length]; exact lenH)).2
    have readyCells := ready_middle (pos1 := [h0, h1, h2]) (pos3 := fpos) (ps3 := ps) (f3 := f)
      (by simpa [head, headPatterns] using ready) rfl (at_length atC) (by simpa using nodup)
      (blank_subjects_head b head) (blank_subjects_of subf) m123
      (fun j hj => by
        simp only [List.mem_singleton] at hj
        rcases hj with (h | h) | h
        · simp [h]
        · simp [h, found1Val]
        · simp [h, found2Val]) (by simp)
    let s3 : rdf_mapping.State := { s2 with used := s2.used.set found2 true }
    obtain ⟨firsts, news, s4, cellsRun, firstsIs, elementsOk, mCells⟩ := cells_complete triples cells nodes
      (by rw [cellsLen, nodesLen]) (List.nodup_append.mp (List.nodup_cons.mp nodup).2).1 s3 cpos t2.object
      (alloc.vec.Vec.new Usize) fewer (by simpa [head] using object2) readyCells (by omega)
      (by simp; have := fewer.hBounds; scalar_tac)
    have mHead := marked_trans m123 mCells
    have readyFacets := ready_middle (pos1 := [h0, h1, h2] ++ cpos) (pos2 := fpos) (pos3 := [])
      (ps1 := headPatterns b head ++ (listOf cells nodes).2) (ps2 := ps) (ps3 := [])
      (f1 := b :: cells) (f2 := f) (f3 := [])
      (by simpa [head, headPatterns, List.append_assoc] using ready)
      (by simp [at_length atC, head_patterns_length, head]; omega) (at_length atF)
      (by simpa [List.append_assoc] using nodup)
      (blank_subjects_append (blank_subjects_mono (blank_subjects_head b head) (fun y m => by simp at m; simp [m]))
        (blank_subjects_mono (blank_subjects_of (list_of_subjects cells nodes)) (fun y m => by simp [m])))
      (fun _ m => by simp at m) mHead
      (fun j hj => by
        simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj ⊢
        rcases hj with ((h | h) | h) | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl (by rw [h, found1Val])))
        · exact Or.inl (Or.inr (Or.inr (by rw [h, found2Val])))
        · exact Or.inr h) (by simp)
    -- the first facet and the others
    obtain ⟨y0, sRest, value0, nsRest, psRest, rfl, rfl, rfl, literal0, tailFacets⟩ := tfacets_cons_inv facets
    obtain ⟨fRest, eqRest, subRest⟩ := tfacets_fresh tailFacets
    have fIs : f = y0 :: fRest := by
      rw [eqRest] at eqf
      have h : (y0 :: fRest) ++ s' = f ++ s' := by simpa using eqf
      exact (List.append_cancel_right h).symm
    subst fIs
    obtain ⟨i0, iRest, rfl⟩ : ∃ i0 iRest, fpos = i0 :: iRest := by
      have := at_length atF
      match fpos, this with
      | i0 :: iRest, _ => exact ⟨i0, iRest, rfl⟩
    have elements0 := firsts_from_cells firstsIs elementsOk
    obtain ⟨inside0, u0, at0, view0, rest0⟩ := elements_drop_cons elements0
    have nodupF : (y0 :: fRest).Nodup := (List.nodup_append.mp (List.nodup_cons.mp nodup).2).2.1
    have readyFirst := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (pos2 := [i0])
      (ps2 := [⟨.blank y0, xs.first.facet.spelling.val, value0⟩]) (f2 := [y0]) (pos3 := iRest) (ps3 := psRest)
      (f3 := fRest) (by simpa using readyFacets) rfl rfl (by simpa using nodupF) (fun _ m => by simp at m)
      (blank_subjects_of subRest) (marked_refl s4) (fun _ h => h.elim) (by simp)
    obtain ⟨s5, elementRun, mFirst⟩ := facet_element_complete triples firsts 0#usize xs.first y0 value0 literal0
      (readable xs.first (by simp [members1])) inside0 u0 at0 view0 s4 i0 readyFirst
    have readyRestFacets := ready_middle (pos1 := [i0]) (ps1 := [⟨.blank y0, xs.first.facet.spelling.val, value0⟩])
      (f1 := [y0]) (pos2 := iRest) (ps2 := psRest) (f2 := fRest) (pos3 := []) (ps3 := []) (f3 := [])
      (by simpa using readyFacets) rfl (by have := at_length atF; simpa using this) (by simpa using nodupF)
      (blank_subjects_head y0 [(xs.first.facet.spelling.val, value0)]) (fun _ m => by simp at m) mFirst
      (fun _ h => h) (by simp)
    have one : (1#usize : Usize).val = 0 + 1 := by simp
    have zero : (0#usize : Usize).val = 0 := by simp
    obtain ⟨v, s6, membersRun, value, mRest⟩ := facet_members_complete triples firsts tailFacets
      (fun g m => readable g (by simp [members1, m])) fRest eqRest (List.nodup_cons.mp nodupF).2 1#usize s5 iRest
      (alloc.vec.Vec.new model.FacetRestriction) (by rw [one, ← zero]; exact rest0) readyRestFacets
      (by rw [new_length]; have := xs.rest.property; omega)
    have baseRun : rdf_mapping.node_iri t1.object = .ok (some d.iri) :=
      node_iri_complete t1.object d.iri (by simpa [head] using object1)
    have find2' : ∀ k : Slice U8, k.val = owlWithRestrictions → rdf_mapping.find triples
        { used := s1.used.set found1 true, blanks := s1.blanks, subjects := s1.subjects, sources := s1.sources } b k =
        .ok (some found2) := find2
    have cellsRun' : rdf_mapping.cells triples t2.object
        { used := (s1.used.set found1 true).set found2 true, blanks := s1.blanks, subjects := s1.subjects,
          sources := s1.sources } (alloc.vec.Vec.new Usize) fewer = .ok (some (firsts, s4)) := cellsRun
    refine ⟨s6, ?_, ?_⟩
    · rw [rangeRun, rdf_mapping.range_construct]
      simp only [lift, bind_ok, missI, missU, missC, missO, find1, array_slice_val, owlIntersectionOf, owlUnionOf,
        owlDatatypeComplementOf, owlOneOf, owlOnDatatype, alloc.vec.Vec.index_slice_index,
        main_lookup triples found1 t1 (by rw [found1Val]; exact at1), baseRun, take_correct]
      simp only [find2', array_slice_val, owlWithRestrictions, take_correct, bind_ok,
        alloc.vec.Vec.index_slice_index, main_lookup triples found2 t2 (by rw [found2Val]; exact at2), cellsRun',
        uncurry_apply_pair, elementRun, membersRun]
      rw [non_empty_ext rfl (by rw [value]; simp)]
    · refine marked_same (marked_fresh_eq (marked_trans (marked_trans mHead mFirst) mRest) (by simp)) (fun j => ?_)
      simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, false_or, found1Val,
        found2Val, or_assoc, or_comm, or_left_comm]

theorem range_datatype_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (d : model.Datatype)
    (s : Supply) : RangeReads triples kinds (.Datatype d) s (iriNode d.iri) [] s := by
  intro fresh split _ st pos node fuel view ready _
  have empty : fresh = [] := by simpa using split
  subst empty
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
  cases node with
  | Iri r =>
    have same : r.spelling.val = d.iri.spelling.val := by simpa [objectView, iriNode] using view
    refine ⟨st, ?_, ready_nil_marked st⟩
    rw [rdf_mapping.data_range]
    simp only [iri_of_identity, bind_ok]
    have datatype : ({ iri := { spelling := r.spelling } } : model.Datatype) = d := by
      obtain ⟨⟨sp⟩⟩ := d
      simp only at same ⊢
      rw [vec_eq_of_val same]
    rw [datatype]
  | Blank _ => simp [objectView, iriNode] at view
  | Literal _ => simp [objectView, iriNode] at view

mutual
/-- Every readable data range is read back from its forward image. -/
theorem range_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) :
    ∀ {r : model.DataRange} {s0 : Supply} {n : Node} {ps : List Pattern} {s1 : Supply},
      TDR r s0 n ps s1 → RangeReadable r → RangeReads triples kinds r s0 n ps s1
  | _, _, _, _, _, .datatype d s, _ => range_datatype_reads triples kinds d s
  | _, _, _, _, _, .intersection xs x cells s s' nodes ps cellsLen inner, readable => by
    cases readable with
    | intersection _ members =>
      exact range_intersection_reads triples kinds xs x cells s s' nodes ps cellsLen
        (ranges_read triples kinds inner members)
  | _, _, _, _, _, .union xs x cells s s' nodes ps cellsLen inner, readable => by
    cases readable with
    | union _ members =>
      exact range_union_reads triples kinds xs x cells s s' nodes ps cellsLen (ranges_read triples kinds inner members)
  | _, _, _, _, _, .complement r x s s' node ps inner, readable => by
    cases readable with
    | complement _ innerReadable =>
      exact range_complement_reads triples kinds r x s s' node ps inner (range_reads triples kinds inner innerReadable)
  | _, _, _, _, _, .oneOf xs x cells s nodes cellsLen literals, readable => by
    cases readable with
    | oneOf _ literalsReadable =>
      exact range_one_of_reads triples kinds xs x cells s nodes cellsLen literals literalsReadable
  | _, _, _, _, _, .restriction d xs x cells s s' nodes ps cellsLen facets, readable => by
    cases readable with
    | restriction _ _ facetsReadable =>
      exact range_restriction_reads triples kinds d xs x cells s s' nodes ps cellsLen facets
        (fun f member => (facetsReadable f member).1)

/-- Readable data ranges in order are each read back. -/
theorem ranges_read (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) :
    ∀ {rs : List model.DataRange} {s0 : Supply} {ns : List Node} {ps : List Pattern} {s1 : Supply},
      TDRs rs s0 ns ps s1 → RangesReadable rs → RangesRead triples kinds rs s0 ns ps s1
  | _, _, _, _, _, .nil s, _ => .nil s
  | _, _, _, _, _, .cons r rs s s1 s2 n ns ps qs head tail, readable => by
    cases readable with
    | cons _ _ headReadable tailReadable =>
      exact .cons r rs s s1 s2 n ns ps qs head (range_reads triples kinds head headReadable)
        (ranges_read triples kinds tail tailReadable)
end

/-! ### Class expressions: lists, dispatch and the steps of the readers -/

/-- `class_expression` reads `c` back from any node of its forward image. -/
def ClassReads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (c : model.ClassExpression)
    (s0 : Supply) (n : Node) (ps : List Pattern) (s1 : Supply) : Prop :=
  ∀ (fresh : Supply), s0 = fresh ++ s1 → fresh.Nodup →
  ∀ (s : rdf_mapping.State) (pos : List Nat) (node : rdf.Object) (fuel : Usize),
    objectView node = n → Ready triples s pos ps fresh → ps.length ≤ fuel.val →
    ∃ s', rdf_mapping.class_expression triples kinds node s fuel = .ok (some (c, s')) ∧
      Marked s s' (fun i => i ∈ pos) fresh

/-- Class expressions in order, each read back. -/
inductive ClassesRead (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) :
    List model.ClassExpression → Supply → List Node → List Pattern → Supply → Prop
  | nil (s : Supply) : ClassesRead triples kinds [] s [] [] s
  | cons (c : model.ClassExpression) (cs : List model.ClassExpression) (s s1 s2 : Supply) (n : Node) (ns : List Node)
      (ps qs : List Pattern) : TCE c s n ps s1 → ClassReads triples kinds c s n ps s1 →
      ClassesRead triples kinds cs s1 ns qs s2 → ClassesRead triples kinds (c :: cs) s (n :: ns) (ps ++ qs) s2

theorem classes_read_fresh {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {cs : List model.ClassExpression} {s0 s1 : Supply} {ns : List Node} {ps : List Pattern}
    (h : ClassesRead triples kinds cs s0 ns ps s1) : ∃ fresh, s0 = fresh ++ s1 ∧ SubjectsIn fresh ps := by
  induction h with
  | nil s => exact ⟨[], by simp, subjects_in_nil _⟩
  | cons c cs s s1 s2 n ns ps qs head _ _ ih =>
    obtain ⟨f1, eq1, sub1⟩ := tce_fresh head
    obtain ⟨f2, eq2, sub2⟩ := ih
    exact ⟨f1 ++ f2, by rw [eq1, eq2, List.append_assoc], subjects_pair sub1 sub2⟩

theorem classes_read_length {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {cs : List model.ClassExpression} {s0 s1 : Supply} {ns : List Node} {ps : List Pattern}
    (h : ClassesRead triples kinds cs s0 ns ps s1) : ns.length = cs.length := by
  induction h with
  | nil => rfl
  | cons => simp_all

theorem classes_read_cons_inv {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {c : model.ClassExpression} {cs : List model.ClassExpression} {s0 s1 : Supply} {ns : List Node}
    {ps : List Pattern} (h : ClassesRead triples kinds (c :: cs) s0 ns ps s1) :
    ∃ (sMid : Supply) (n : Node) (ns' : List Node) (p q : List Pattern), ns = n :: ns' ∧ ps = p ++ q ∧
      TCE c s0 n p sMid ∧ ClassReads triples kinds c s0 n p sMid ∧ ClassesRead triples kinds cs sMid ns' q s1 := by
  cases h with
  | cons _ _ _ sMid _ n ns' p q head reads tail => exact ⟨sMid, n, ns', p, q, rfl, rfl, head, reads, tail⟩

/-- The class expressions of the elements from `firsts[index]` on. -/
theorem class_members_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (firsts : alloc.vec.Vec Usize) :
    ∀ {cs : List model.ClassExpression} {s0 s1 : Supply} {ns : List Node} {ps : List Pattern},
      ClassesRead triples kinds cs s0 ns ps s1 → ∀ (fresh : Supply), s0 = fresh ++ s1 → fresh.Nodup →
      ∀ (index : Usize) (s : rdf_mapping.State) (pos : List Nat) (out : alloc.vec.Vec model.ClassExpression)
        (fuel : Usize),
        Elements triples.val (firsts.val.drop index.val) ns → Ready triples s pos ps fresh → ps.length ≤ fuel.val →
        out.val.length + cs.length ≤ Usize.max →
        ∃ v s', rdf_mapping.class_members triples kinds firsts index s out fuel = .ok (some (v, s')) ∧
          v.val = out.val ++ cs ∧ Marked s s' (fun i => i ∈ pos) fresh := by
  intro cs s0 s1 ns ps h
  induction h with
  | nil s =>
    intro fresh split _ index st pos out fuel elements ready _ _
    have empty : fresh = [] := by simpa using split
    subst empty
    have noPos : pos = [] := by have := at_length ready.holds; simpa using this
    subst noPos
    have done := elements_drop_nil elements
    refine ⟨out, st, ?_, by simp, ready_nil_marked st⟩
    rw [rdf_mapping.class_members]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, show ¬ index.val < firsts.val.length by omega]
  | cons c cs s s1 s2 n ns ps qs head reads tail ih =>
    intro fresh split nodup index st pos out fuel elements ready fuelOk room
    obtain ⟨f1, eq1, sub1⟩ := tce_fresh head
    obtain ⟨f2, eq2, sub2⟩ := classes_read_fresh tail
    have freshIs := fresh_split (by rw [← eq1]; exact split) eq2
    subst freshIs
    obtain ⟨pos1, pos2, rfl, at1, at2⟩ := at_split ready.holds
    have nodup1 : f1.Nodup := (List.nodup_append.mp nodup).1
    have nodup2 : f2.Nodup := (List.nodup_append.mp nodup).2.1
    have ready1 := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (by simpa using ready) rfl (at_length at1)
      (by simpa using nodup) (fun _ m => by simp at m) (blank_subjects_of sub2) (marked_refl st) (fun _ h => h.elim)
      (by simp)
    obtain ⟨inside, t, at_t, view, restElements⟩ := elements_drop_cons elements
    simp only [List.length_append] at fuelOk
    obtain ⟨s3, run1, m1⟩ := reads f1 eq1 nodup1 st pos1 t.object fuel view ready1 (by omega)
    have ready2 := ready_middle (pos3 := []) (ps3 := []) (f3 := []) (by simpa using ready) (at_length at1)
      (at_length at2) (by simpa using nodup) (blank_subjects_of sub1) (fun _ m => by simp at m) m1
      (fun _ h => h) (le_refl _)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := firsts.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have outRoom : out.val.length < Usize.max := by simp at room; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out c outRoom)
    obtain ⟨v, s4, run2, value, m2⟩ := ih f2 eq2 nodup2 next s3 pos2 pushed fuel (by rw [nextIs]; exact restElements)
      ready2 (by omega) (by rw [contents]; simp at room ⊢; omega)
    refine ⟨v, s4, ?_, by rw [value, contents]; simp, ?_⟩
    · rw [rdf_mapping.class_members]
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        firsts_lookup firsts index inside, bind_ok, element_at triples _ t at_t, run1, uncurry_apply_pair,
        usize_max_val, outRoom, push, advance, run2]
    · refine marked_same (marked_trans m1 m2) (fun j => ?_)
      simp only [List.mem_append]

/-- The class expressions of a list of at least two read back from its forward image. -/
theorem class_list2_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (xs : model.AtLeastTwo model.ClassExpression) (cells : List rdf.BlankNode) (nodes : List Node) (ps : List Pattern)
    (s0 s1 : Supply) (cellsLen : cells.length = (members2 xs).length)
    (members : ClassesRead triples kinds (members2 xs) s0 nodes ps s1) (fresh : Supply) (split : s0 = fresh ++ s1)
    (nodup : (cells ++ fresh).Nodup) (s : rdf_mapping.State) (pos : List Nat) (node : rdf.Object) (fuel : Usize)
    (view : objectView node = (listOf cells nodes).1)
    (ready : Ready triples s pos ((listOf cells nodes).2 ++ ps) (cells ++ fresh))
    (fuelOk : ((listOf cells nodes).2 ++ ps).length ≤ fuel.val) :
    ∃ s', rdf_mapping.class_list2 triples kinds node s fuel = .ok (some (xs, s')) ∧
      Marked s s' (fun i => i ∈ pos) (cells ++ fresh) := by
  have nodesLen := classes_read_length members
  have lists := list_of_length cells nodes (by rw [cellsLen, nodesLen])
  obtain ⟨f, eqf, subf⟩ := classes_read_fresh members
  have freshIs : fresh = f := by
    rw [eqf] at split
    exact (List.append_cancel_right split).symm
  subst freshIs
  obtain ⟨cpos, mpos, rfl, atC, atM⟩ := at_split ready.holds
  have nodupCells : cells.Nodup := (List.nodup_append.mp nodup).1
  have nodupMembers : fresh.Nodup := (List.nodup_append.mp nodup).2.1
  have readyCells := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (by simpa using ready) rfl (at_length atC)
    (by simpa using nodup) (fun _ m => by simp at m) (blank_subjects_of subf) (marked_refl s) (fun _ h => h.elim)
    (by simp)
  simp only [List.length_append, lists] at fuelOk
  obtain ⟨firsts, news, s2, cellsRun, firstsIs, elementsOk, mCells⟩ := cells_complete triples cells nodes
    (by rw [cellsLen, nodesLen]) nodupCells s cpos node (alloc.vec.Vec.new Usize) fuel view readyCells (by omega)
    (by simp; have := fuel.hBounds; scalar_tac)
  have readyMembers := ready_middle (pos3 := []) (ps3 := []) (f3 := []) (by simpa using ready) (at_length atC)
    (at_length atM) (by simpa using nodup) (blank_subjects_of (list_of_subjects cells nodes))
    (fun _ m => by simp at m) mCells (fun _ h => h) (le_refl _)
  have elements0 := firsts_from_cells firstsIs elementsOk
  obtain ⟨sA, nA, nsA, pA, qA, rfl, rfl, headA, readsA, tailA⟩ := classes_read_cons_inv members
  obtain ⟨sB, nB, nsB, pB, pC, rfl, rfl, headB, readsB, tailC⟩ := classes_read_cons_inv tailA
  obtain ⟨fA, eqA, subA⟩ := tce_fresh headA
  obtain ⟨fB, eqB, subB⟩ := tce_fresh headB
  obtain ⟨fC, eqC, subC⟩ := classes_read_fresh tailC
  have freshIs : fresh = fA ++ (fB ++ fC) := by
    rw [eqA, eqB, eqC] at eqf
    have h : (fA ++ (fB ++ fC)) ++ s1 = fresh ++ s1 := by simpa using eqf
    exact (List.append_cancel_right h).symm
  subst freshIs
  obtain ⟨posA, posBC, rfl, atA, atBC⟩ := at_split atM
  obtain ⟨posB, posC, rfl, atB, atC'⟩ := at_split atBC
  have nodupAll := nodupMembers
  have readyA := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (pos3 := posB ++ posC) (ps3 := pB ++ pC)
    (f3 := fB ++ fC) (by simpa using readyMembers) rfl (at_length atA) (by simpa using nodupAll)
    (fun _ m => by simp at m) (blank_subjects_of (subjects_pair subB subC)) (marked_refl s2) (fun _ h => h.elim)
    (by simp)
  simp only [List.length_append] at fuelOk
  obtain ⟨inside0, t0, at0, view0, rest0⟩ := elements_drop_cons elements0
  obtain ⟨sA', runA, mA⟩ := readsA fA eqA (List.nodup_append.mp nodupAll).1 s2 posA t0.object fuel view0 readyA
    (by omega)
  have readyB := ready_middle (pos1 := posA) (ps1 := pA) (f1 := fA) (pos3 := posC) (ps3 := pC)
    (f3 := fC) (by simpa [List.append_assoc] using readyMembers) (at_length atA) (at_length atB)
    (by simpa [List.append_assoc] using nodupAll) (blank_subjects_of subA) (blank_subjects_of subC) mA
    (fun _ h => h) (le_refl _)
  have one : (1#usize : Usize).val = 0 + 1 := by simp
  have zero : (0#usize : Usize).val = 0 := by simp
  obtain ⟨inside1, t1, at1, view1, rest1⟩ := elements_drop_cons (index := 1#usize) (by rw [one, ← zero]; exact rest0)
  obtain ⟨sB', runB, mB⟩ := readsB fB eqB (List.nodup_append.mp (List.nodup_append.mp nodupAll).2.1).1 sA' posB
    t1.object fuel view1 readyB (by omega)
  have mAB := marked_trans mA mB
  have readyC := ready_middle (pos1 := posA ++ posB) (ps1 := pA ++ pB) (f1 := fA ++ fB) (pos3 := [])
    (ps3 := []) (f3 := []) (by simpa [List.append_assoc] using readyMembers)
    (by simp [at_length atA, at_length atB]) (at_length atC')
    (by simpa [List.append_assoc] using nodupAll) (blank_subjects_of (subjects_pair subA subB))
    (fun _ m => by simp at m) mAB (fun j hj => by simp only [List.mem_append]; exact hj) (le_refl _)
  have two : (2#usize : Usize).val = 0 + 1 + 1 := by simp
  obtain ⟨v, sC', runC, value, mC⟩ := class_members_complete triples kinds firsts tailC fC eqC
    (List.nodup_append.mp (List.nodup_append.mp nodupAll).2.1).2.1 2#usize sB' posC
    (alloc.vec.Vec.new model.ClassExpression) fuel (by rw [two, ← one]; exact rest1) readyC (by omega)
    (by rw [new_length]; have := xs.rest.property; omega)
  have long : alloc.vec.Vec.len firsts ≥ 2#usize := by
    have h : 1 < firsts.val.length := by rw [one] at inside1; simpa using inside1
    clear * - h
    scalar_tac
  refine ⟨sC', ?_, ?_⟩
  · rw [rdf_mapping.class_list2]
    simp only [cellsRun, bind_ok, uncurry_apply_pair, long, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      firsts_lookup firsts 0#usize inside0, element_at triples _ t0 at0, runA,
      firsts_lookup firsts 1#usize inside1, element_at triples _ t1 at1, runB, runC]
    rw [at_least_two_ext rfl rfl (by rw [value]; simp)]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_trans mCells mAB) mC) (by simp)) (fun j => ?_)
    simp only [List.mem_append, List.append_assoc]
    tauto

/-- `class_expression` goes from a blank node typed `owl:Restriction` to its restriction. -/
theorem class_blank_restriction (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (x : rdf.BlankNode)
    (s : rdf_mapping.State) (fuel : Usize)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {hpos : List Nat} {head : List (List U8 × Node)} (heads : HeadsAt triples.val s.used.val x hpos head) {i : Nat}
    (hi : hpos[0]? = some i) (typed : ∀ h : 0 < head.length, head[0] = (rdfType, .iri owlRestriction))
    (unused : s.used.val[i]? = some false) (room : s.blanks.val.length < Usize.max) (positive : 0 < fuel.val) :
    ∃ (s1 : rdf_mapping.State) (fewer : Usize), fewer.val + 1 = fuel.val ∧ Marked s s1 (fun j => j ∈ [i]) [x] ∧
      rdf_mapping.class_expression triples kinds (.Blank x) s fuel =
        rdf_mapping.restriction triples kinds x s1 fewer := by
  obtain ⟨found, foundVal, findRun⟩ := find_type_hit triples s x complete heads hi owlRestriction typed unused
  obtain ⟨s1, recordRun, m2⟩ := record_ok { s with used := s.used.set found true } x room
  obtain ⟨fewer, back, fewerValue⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := fuel) (y := 1#usize) (by scalar_tac))
  refine ⟨s1, fewer, by simp at fewerValue; omega, ?_, ?_⟩
  · refine marked_same (marked_trans (marked_nil_take s found) m2) (fun j => ?_)
    simp [foundVal]
  · have pos' : fuel > 0#usize := by scalar_tac
    rw [rdf_mapping.class_expression]
    simp only [pos', ↓reduceIte, lift, bind_ok, findRun, array_slice_val, owlRestriction, take_correct, recordRun,
      back]

/-- `class_expression` goes from a blank node typed `owl:Class` to its construct. -/
theorem class_blank_construct (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (x : rdf.BlankNode)
    (s : rdf_mapping.State) (fuel : Usize)
    (complete : SubjectsComplete triples.val s.subjects.val (alloc.vec.Vec.len s.subjects) triples.val.length)
    {hpos : List Nat} {head : List (List U8 × Node)} (heads : HeadsAt triples.val s.used.val x hpos head) {i : Nat}
    (hi : hpos[0]? = some i) (typed : ∀ h : 0 < head.length, head[0] = (rdfType, .iri owlClass))
    (notRestriction : ∀ (k : Nat) (h : k < head.length), head[k] ≠ (rdfType, .iri owlRestriction))
    (unused : s.used.val[i]? = some false) (room : s.blanks.val.length < Usize.max) (positive : 0 < fuel.val) :
    ∃ (s1 : rdf_mapping.State) (fewer : Usize), fewer.val + 1 = fuel.val ∧ Marked s s1 (fun j => j ∈ [i]) [x] ∧
      rdf_mapping.class_expression triples kinds (.Blank x) s fuel =
        rdf_mapping.class_construct triples kinds x s1 fewer := by
  have missR := find_type_miss triples s x heads owlRestriction notRestriction
  obtain ⟨found, foundVal, findRun⟩ := find_type_hit triples s x complete heads hi owlClass typed unused
  obtain ⟨s1, recordRun, m2⟩ := record_ok { s with used := s.used.set found true } x room
  obtain ⟨fewer, back, fewerValue⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := fuel) (y := 1#usize) (by scalar_tac))
  refine ⟨s1, fewer, by simp at fewerValue; omega, ?_, ?_⟩
  · refine marked_same (marked_trans (marked_nil_take s found) m2) (fun j => ?_)
    simp [foundVal]
  · have pos' : fuel > 0#usize := by scalar_tac
    rw [rdf_mapping.class_expression]
    simp only [pos', ↓reduceIte, lift, bind_ok, missR, findRun, array_slice_val, owlRestriction, owlClass,
      take_correct, recordRun, back]

theorem node_kind_object (kinds : rdf_mapping.Kinds) {role : model.ObjectPropertyExpression} {s0 s1 : Supply}
    {n : Node} {ps : List Pattern} (tope : TOPE role s0 n ps s1) (node : rdf.Object) (view : objectView node = n)
    (typed : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    rdf_mapping.node_kind kinds node = .ok (some .Object) := by
  cases tope with
  | named q =>
    cases node with
    | Iri r =>
      have same : r.spelling = q.iri.spelling := vec_eq_of_val (by simpa [objectView, iriNode] using view)
      rw [rdf_mapping.node_kind.eq_def]
      simp only [same]
      exact typed q rfl
    | Blank _ => simp [objectView, iriNode] at view
    | Literal _ => simp [objectView, iriNode] at view
  | inverse q x =>
    cases node with
    | Blank _ => rw [rdf_mapping.node_kind.eq_def]
    | Iri _ => simp [objectView] at view
    | Literal _ => simp [objectView] at view

theorem node_kind_data (kinds : rdf_mapping.Kinds) (d : model.DataProperty) (node : rdf.Object)
    (view : objectView node = iriNode d.iri)
    (typed : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data)) :
    rdf_mapping.node_kind kinds node = .ok (some .Data) := by
  cases node with
  | Iri r =>
    have same : r.spelling = d.iri.spelling := vec_eq_of_val (by simpa [objectView, iriNode] using view)
    rw [rdf_mapping.node_kind.eq_def]
    simp only [same]
    exact typed
  | Blank _ => simp [objectView, iriNode] at view
  | Literal _ => simp [objectView, iriNode] at view

/-- The step of `restriction` past the `owl:onProperty` triple. -/
theorem restriction_step (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (x : rdf.BlankNode)
    (s : rdf_mapping.State) (fuel : Usize) (found : Usize) (t : rdf.Triple)
    (findRun : ∀ k : Slice U8, k.val = owlOnProperty → rdf_mapping.find triples s x k = .ok (some found))
    (at_t : triples.val[found.val]? = some t) :
    (∀ (role : model.ObjectPropertyExpression) (s3 : rdf_mapping.State),
      rdf_mapping.node_kind kinds t.object = .ok (some .Object) →
      rdf_mapping.property_expression triples t.object { s with used := s.used.set found true } =
        .ok (some (role, s3)) →
      rdf_mapping.restriction triples kinds x s fuel = rdf_mapping.object_restriction triples kinds x role s3 fuel) ∧
    (∀ d : model.DataProperty, rdf_mapping.node_kind kinds t.object = .ok (some .Data) →
      rdf_mapping.node_iri t.object = .ok (some d.iri) →
      rdf_mapping.restriction triples kinds x s fuel =
        rdf_mapping.data_restriction triples kinds x d { s with used := s.used.set found true } fuel) := by
  constructor
  · intro role s3 kind roleRun
    rw [rdf_mapping.restriction]
    simp only [lift, bind_ok, findRun, array_slice_val, owlOnProperty, take_correct, alloc.vec.Vec.index_slice_index,
      main_lookup triples found t at_t, kind, roleRun, uncurry_apply_pair]
  · intro d kind iriRun
    rw [rdf_mapping.restriction]
    simp only [lift, bind_ok, findRun, array_slice_val, owlOnProperty, take_correct, alloc.vec.Vec.index_slice_index,
      main_lookup triples found t at_t, kind, iriRun]

/-! ### The last steps of the class expression readers -/

section leaves
variable (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (x : rdf.BlankNode)
  (role : model.ObjectPropertyExpression) (property : model.DataProperty) (s : rdf_mapping.State) (fuel : Usize)
  (found : Usize) (t : rdf.Triple)

/-- A lookup that finds the triple at `found`. -/
abbrev Hit (key : List U8) : Prop :=
  ∀ k : Slice U8, k.val = key → rdf_mapping.find triples s x k = .ok (some found)

/-- A lookup that finds nothing. -/
abbrev Miss (key : List U8) : Prop :=
  ∀ k : Slice U8, k.val = key → rdf_mapping.find triples s x k = .ok none

theorem object_restriction_some (hit : Hit triples x s found owlSomeValuesFrom)
    (at_t : triples.val[found.val]? = some t) (c : model.ClassExpression) (s' : rdf_mapping.State)
    (run : rdf_mapping.class_expression triples kinds t.object { s with used := s.used.set found true } fuel =
      .ok (some (c, s'))) :
    rdf_mapping.object_restriction triples kinds x role s fuel = .ok (some (.ObjectSomeValuesFrom role c, s')) := by
  rw [rdf_mapping.object_restriction]
  simp only [lift, bind_ok, hit, array_slice_val, owlSomeValuesFrom, take_correct, alloc.vec.Vec.index_slice_index,
    main_lookup triples found t at_t, run, uncurry_apply_pair]

theorem object_restriction_all (miss1 : Miss triples x s owlSomeValuesFrom)
    (hit : Hit triples x s found owlAllValuesFrom) (at_t : triples.val[found.val]? = some t) (c : model.ClassExpression)
    (s' : rdf_mapping.State)
    (run : rdf_mapping.class_expression triples kinds t.object { s with used := s.used.set found true } fuel =
      .ok (some (c, s'))) :
    rdf_mapping.object_restriction triples kinds x role s fuel = .ok (some (.ObjectAllValuesFrom role c, s')) := by
  rw [rdf_mapping.object_restriction]
  simp only [lift, bind_ok, miss1, hit, array_slice_val, owlSomeValuesFrom, owlAllValuesFrom, take_correct,
    alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run, uncurry_apply_pair]

theorem object_restriction_has_value (miss1 : Miss triples x s owlSomeValuesFrom)
    (miss2 : Miss triples x s owlAllValuesFrom) (hit : Hit triples x s found owlHasValue)
    (at_t : triples.val[found.val]? = some t) (a : model.Individual)
    (run : rdf_mapping.node_individual t.object = .ok (some a)) :
    rdf_mapping.object_restriction triples kinds x role s fuel =
      .ok (some (.ObjectHasValue role a, { s with used := s.used.set found true })) := by
  rw [rdf_mapping.object_restriction]
  simp only [lift, bind_ok, miss1, miss2, hit, array_slice_val, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue,
    take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run]

theorem object_restriction_has_self (miss1 : Miss triples x s owlSomeValuesFrom)
    (miss2 : Miss triples x s owlAllValuesFrom) (miss3 : Miss triples x s owlHasValue)
    (hit : Hit triples x s found owlHasSelf) (at_t : triples.val[found.val]? = some t)
    (run : rdf_mapping.node_true t.object = .ok true) :
    rdf_mapping.object_restriction triples kinds x role s fuel =
      .ok (some (.ObjectHasSelf role, { s with used := s.used.set found true })) := by
  rw [rdf_mapping.object_restriction]
  simp only [lift, bind_ok, miss1, miss2, miss3, hit, array_slice_val, owlSomeValuesFrom, owlAllValuesFrom,
    owlHasValue, owlHasSelf, take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run,
    ↓reduceIte]

theorem object_restriction_cardinality (miss1 : Miss triples x s owlSomeValuesFrom)
    (miss2 : Miss triples x s owlAllValuesFrom) (miss3 : Miss triples x s owlHasValue)
    (miss4 : Miss triples x s owlHasSelf) :
    rdf_mapping.object_restriction triples kinds x role s fuel =
      rdf_mapping.object_cardinality triples kinds x role s fuel := by
  rw [rdf_mapping.object_restriction]
  simp only [lift, bind_ok, miss1, miss2, miss3, miss4, array_slice_val, owlSomeValuesFrom, owlAllValuesFrom,
    owlHasValue, owlHasSelf]

theorem object_cardinality_min (hit : Hit triples x s found owlMinCardinality)
    (at_t : triples.val[found.val]? = some t) (n : probes.Natural) (run : rdf_mapping.node_natural t.object = .ok (some n)) :
    rdf_mapping.object_cardinality triples kinds x role s fuel =
      .ok (some (.ObjectMinCardinality n role none, { s with used := s.used.set found true })) := by
  rw [rdf_mapping.object_cardinality]
  simp only [lift, bind_ok, hit, array_slice_val, owlMinCardinality, take_correct, alloc.vec.Vec.index_slice_index,
    main_lookup triples found t at_t, run]

theorem object_cardinality_max (miss1 : Miss triples x s owlMinCardinality)
    (hit : Hit triples x s found owlMaxCardinality)
    (at_t : triples.val[found.val]? = some t) (n : probes.Natural) (run : rdf_mapping.node_natural t.object = .ok (some n)) :
    rdf_mapping.object_cardinality triples kinds x role s fuel =
      .ok (some (.ObjectMaxCardinality n role none, { s with used := s.used.set found true })) := by
  rw [rdf_mapping.object_cardinality]
  simp only [lift, bind_ok, miss1, hit, array_slice_val, owlMinCardinality, owlMaxCardinality, take_correct,
    alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run]

theorem object_cardinality_exact (miss1 : Miss triples x s owlMinCardinality)
    (miss2 : Miss triples x s owlMaxCardinality) (hit : Hit triples x s found owlCardinality)
    (at_t : triples.val[found.val]? = some t) (n : probes.Natural) (run : rdf_mapping.node_natural t.object = .ok (some n)) :
    rdf_mapping.object_cardinality triples kinds x role s fuel =
      .ok (some (.ObjectExactCardinality n role none, { s with used := s.used.set found true })) := by
  rw [rdf_mapping.object_cardinality]
  simp only [lift, bind_ok, miss1, miss2, hit, array_slice_val, owlMinCardinality, owlMaxCardinality, owlCardinality,
    take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run]

theorem object_cardinality_qualified (miss1 : Miss triples x s owlMinCardinality)
    (miss2 : Miss triples x s owlMaxCardinality) (miss3 : Miss triples x s owlCardinality) :
    rdf_mapping.object_cardinality triples kinds x role s fuel =
      rdf_mapping.object_qualified triples kinds x role s fuel := by
  rw [rdf_mapping.object_cardinality]
  simp only [lift, bind_ok, miss1, miss2, miss3, array_slice_val, owlMinCardinality, owlMaxCardinality, owlCardinality]

/-- `on_class` reads the qualifying class. -/
theorem on_class_run (s2 : rdf_mapping.State) (found2 : Usize) (t2 : rdf.Triple)
    (hit : ∀ k : Slice U8, k.val = owlOnClass → rdf_mapping.find triples s2 x k = .ok (some found2))
    (at2 : triples.val[found2.val]? = some t2) (c : model.ClassExpression) (s' : rdf_mapping.State)
    (run : rdf_mapping.class_expression triples kinds t2.object { s2 with used := s2.used.set found2 true } fuel =
      .ok (some (c, s'))) :
    rdf_mapping.on_class triples kinds x s2 fuel = .ok (some (c, s')) := by
  rw [rdf_mapping.on_class]
  simp only [lift, bind_ok, hit, array_slice_val, owlOnClass, take_correct, alloc.vec.Vec.index_slice_index,
    main_lookup triples found2 t2 at2, run]

theorem object_qualified_min (hit : Hit triples x s found owlMinQualifiedCardinality)
    (at_t : triples.val[found.val]? = some t) (n : probes.Natural) (run : rdf_mapping.node_natural t.object = .ok (some n))
    (c : model.ClassExpression) (s' : rdf_mapping.State)
    (onClass : rdf_mapping.on_class triples kinds x { s with used := s.used.set found true } fuel = .ok (some (c, s'))) :
    rdf_mapping.object_qualified triples kinds x role s fuel =
      .ok (some (.ObjectMinCardinality n role (some c), s')) := by
  rw [rdf_mapping.object_qualified]
  simp only [lift, bind_ok, hit, array_slice_val, owlMinQualifiedCardinality, take_correct,
    alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run, onClass, uncurry_apply_pair]

theorem object_qualified_max (miss1 : Miss triples x s owlMinQualifiedCardinality)
    (hit : Hit triples x s found owlMaxQualifiedCardinality)
    (at_t : triples.val[found.val]? = some t) (n : probes.Natural) (run : rdf_mapping.node_natural t.object = .ok (some n))
    (c : model.ClassExpression) (s' : rdf_mapping.State)
    (onClass : rdf_mapping.on_class triples kinds x { s with used := s.used.set found true } fuel = .ok (some (c, s'))) :
    rdf_mapping.object_qualified triples kinds x role s fuel =
      .ok (some (.ObjectMaxCardinality n role (some c), s')) := by
  rw [rdf_mapping.object_qualified]
  simp only [lift, bind_ok, miss1, hit, array_slice_val, owlMinQualifiedCardinality, owlMaxQualifiedCardinality,
    take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run, onClass, uncurry_apply_pair]

theorem object_qualified_exact (miss1 : Miss triples x s owlMinQualifiedCardinality)
    (miss2 : Miss triples x s owlMaxQualifiedCardinality) (hit : Hit triples x s found owlQualifiedCardinality)
    (at_t : triples.val[found.val]? = some t) (n : probes.Natural) (run : rdf_mapping.node_natural t.object = .ok (some n))
    (c : model.ClassExpression) (s' : rdf_mapping.State)
    (onClass : rdf_mapping.on_class triples kinds x { s with used := s.used.set found true } fuel = .ok (some (c, s'))) :
    rdf_mapping.object_qualified triples kinds x role s fuel =
      .ok (some (.ObjectExactCardinality n role (some c), s')) := by
  rw [rdf_mapping.object_qualified]
  simp only [lift, bind_ok, miss1, miss2, hit, array_slice_val, owlMinQualifiedCardinality, owlMaxQualifiedCardinality,
    owlQualifiedCardinality, take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run,
    onClass, uncurry_apply_pair]

theorem data_restriction_some (hit : Hit triples x s found owlSomeValuesFrom)
    (at_t : triples.val[found.val]? = some t) (r : model.DataRange) (s' : rdf_mapping.State)
    (run : rdf_mapping.data_range triples kinds t.object { s with used := s.used.set found true } fuel =
      .ok (some (r, s'))) :
    rdf_mapping.data_restriction triples kinds x property s fuel =
      .ok (some (.DataSomeValuesFrom property r, s')) := by
  rw [rdf_mapping.data_restriction]
  simp only [lift, bind_ok, hit, array_slice_val, owlSomeValuesFrom, take_correct, alloc.vec.Vec.index_slice_index,
    main_lookup triples found t at_t, run, uncurry_apply_pair]

theorem data_restriction_all (miss1 : Miss triples x s owlSomeValuesFrom)
    (hit : Hit triples x s found owlAllValuesFrom) (at_t : triples.val[found.val]? = some t) (r : model.DataRange)
    (s' : rdf_mapping.State)
    (run : rdf_mapping.data_range triples kinds t.object { s with used := s.used.set found true } fuel =
      .ok (some (r, s'))) :
    rdf_mapping.data_restriction triples kinds x property s fuel =
      .ok (some (.DataAllValuesFrom property r, s')) := by
  rw [rdf_mapping.data_restriction]
  simp only [lift, bind_ok, miss1, hit, array_slice_val, owlSomeValuesFrom, owlAllValuesFrom, take_correct,
    alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run, uncurry_apply_pair]

theorem data_restriction_has_value (miss1 : Miss triples x s owlSomeValuesFrom)
    (miss2 : Miss triples x s owlAllValuesFrom) (hit : Hit triples x s found owlHasValue)
    (at_t : triples.val[found.val]? = some t) (v : model.Literal) (run : rdf_mapping.node_literal t.object = .ok (some v)) :
    rdf_mapping.data_restriction triples kinds x property s fuel =
      .ok (some (.DataHasValue property v, { s with used := s.used.set found true })) := by
  rw [rdf_mapping.data_restriction]
  simp only [lift, bind_ok, miss1, miss2, hit, array_slice_val, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue,
    take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run]

theorem data_restriction_cardinality (miss1 : Miss triples x s owlSomeValuesFrom)
    (miss2 : Miss triples x s owlAllValuesFrom) (miss3 : Miss triples x s owlHasValue) :
    rdf_mapping.data_restriction triples kinds x property s fuel =
      rdf_mapping.data_cardinality triples kinds x property s fuel := by
  rw [rdf_mapping.data_restriction]
  simp only [lift, bind_ok, miss1, miss2, miss3, array_slice_val, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue]

theorem data_cardinality_min (hit : Hit triples x s found owlMinCardinality)
    (at_t : triples.val[found.val]? = some t) (n : probes.Natural) (run : rdf_mapping.node_natural t.object = .ok (some n)) :
    rdf_mapping.data_cardinality triples kinds x property s fuel =
      .ok (some (.DataMinCardinality n property none, { s with used := s.used.set found true })) := by
  rw [rdf_mapping.data_cardinality]
  simp only [lift, bind_ok, hit, array_slice_val, owlMinCardinality, take_correct, alloc.vec.Vec.index_slice_index,
    main_lookup triples found t at_t, run]

theorem data_cardinality_max (miss1 : Miss triples x s owlMinCardinality)
    (hit : Hit triples x s found owlMaxCardinality)
    (at_t : triples.val[found.val]? = some t) (n : probes.Natural) (run : rdf_mapping.node_natural t.object = .ok (some n)) :
    rdf_mapping.data_cardinality triples kinds x property s fuel =
      .ok (some (.DataMaxCardinality n property none, { s with used := s.used.set found true })) := by
  rw [rdf_mapping.data_cardinality]
  simp only [lift, bind_ok, miss1, hit, array_slice_val, owlMinCardinality, owlMaxCardinality, take_correct,
    alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run]

theorem data_cardinality_exact (miss1 : Miss triples x s owlMinCardinality)
    (miss2 : Miss triples x s owlMaxCardinality) (hit : Hit triples x s found owlCardinality)
    (at_t : triples.val[found.val]? = some t) (n : probes.Natural) (run : rdf_mapping.node_natural t.object = .ok (some n)) :
    rdf_mapping.data_cardinality triples kinds x property s fuel =
      .ok (some (.DataExactCardinality n property none, { s with used := s.used.set found true })) := by
  rw [rdf_mapping.data_cardinality]
  simp only [lift, bind_ok, miss1, miss2, hit, array_slice_val, owlMinCardinality, owlMaxCardinality, owlCardinality,
    take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run]

theorem data_cardinality_qualified (miss1 : Miss triples x s owlMinCardinality)
    (miss2 : Miss triples x s owlMaxCardinality) (miss3 : Miss triples x s owlCardinality) :
    rdf_mapping.data_cardinality triples kinds x property s fuel =
      rdf_mapping.data_qualified triples kinds x property s fuel := by
  rw [rdf_mapping.data_cardinality]
  simp only [lift, bind_ok, miss1, miss2, miss3, array_slice_val, owlMinCardinality, owlMaxCardinality, owlCardinality]

/-- `on_data_range` reads the qualifying data range. -/
theorem on_data_range_run (s2 : rdf_mapping.State) (found2 : Usize) (t2 : rdf.Triple)
    (hit : ∀ k : Slice U8, k.val = owlOnDataRange → rdf_mapping.find triples s2 x k = .ok (some found2))
    (at2 : triples.val[found2.val]? = some t2) (r : model.DataRange) (s' : rdf_mapping.State)
    (run : rdf_mapping.data_range triples kinds t2.object { s2 with used := s2.used.set found2 true } fuel =
      .ok (some (r, s'))) :
    rdf_mapping.on_data_range triples kinds x s2 fuel = .ok (some (r, s')) := by
  rw [rdf_mapping.on_data_range]
  simp only [lift, bind_ok, hit, array_slice_val, owlOnDataRange, take_correct, alloc.vec.Vec.index_slice_index,
    main_lookup triples found2 t2 at2, run]

theorem data_qualified_min (hit : Hit triples x s found owlMinQualifiedCardinality)
    (at_t : triples.val[found.val]? = some t) (n : probes.Natural) (run : rdf_mapping.node_natural t.object = .ok (some n))
    (r : model.DataRange) (s' : rdf_mapping.State)
    (onRange : rdf_mapping.on_data_range triples kinds x { s with used := s.used.set found true } fuel =
      .ok (some (r, s'))) :
    rdf_mapping.data_qualified triples kinds x property s fuel =
      .ok (some (.DataMinCardinality n property (some r), s')) := by
  rw [rdf_mapping.data_qualified]
  simp only [lift, bind_ok, hit, array_slice_val, owlMinQualifiedCardinality, take_correct,
    alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run, onRange, uncurry_apply_pair]

theorem data_qualified_max (miss1 : Miss triples x s owlMinQualifiedCardinality)
    (hit : Hit triples x s found owlMaxQualifiedCardinality)
    (at_t : triples.val[found.val]? = some t) (n : probes.Natural) (run : rdf_mapping.node_natural t.object = .ok (some n))
    (r : model.DataRange) (s' : rdf_mapping.State)
    (onRange : rdf_mapping.on_data_range triples kinds x { s with used := s.used.set found true } fuel =
      .ok (some (r, s'))) :
    rdf_mapping.data_qualified triples kinds x property s fuel =
      .ok (some (.DataMaxCardinality n property (some r), s')) := by
  rw [rdf_mapping.data_qualified]
  simp only [lift, bind_ok, miss1, hit, array_slice_val, owlMinQualifiedCardinality, owlMaxQualifiedCardinality,
    take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run, onRange, uncurry_apply_pair]

theorem data_qualified_exact (miss1 : Miss triples x s owlMinQualifiedCardinality)
    (miss2 : Miss triples x s owlMaxQualifiedCardinality) (hit : Hit triples x s found owlQualifiedCardinality)
    (at_t : triples.val[found.val]? = some t) (n : probes.Natural) (run : rdf_mapping.node_natural t.object = .ok (some n))
    (r : model.DataRange) (s' : rdf_mapping.State)
    (onRange : rdf_mapping.on_data_range triples kinds x { s with used := s.used.set found true } fuel =
      .ok (some (r, s'))) :
    rdf_mapping.data_qualified triples kinds x property s fuel =
      .ok (some (.DataExactCardinality n property (some r), s')) := by
  rw [rdf_mapping.data_qualified]
  simp only [lift, bind_ok, miss1, miss2, hit, array_slice_val, owlMinQualifiedCardinality, owlMaxQualifiedCardinality,
    owlQualifiedCardinality, take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run,
    onRange, uncurry_apply_pair]

theorem class_construct_intersection (hit : Hit triples x s found owlIntersectionOf)
    (at_t : triples.val[found.val]? = some t) (xs : model.AtLeastTwo model.ClassExpression) (s' : rdf_mapping.State)
    (run : rdf_mapping.class_list2 triples kinds t.object { s with used := s.used.set found true } fuel =
      .ok (some (xs, s'))) :
    rdf_mapping.class_construct triples kinds x s fuel = .ok (some (.ObjectIntersectionOf xs, s')) := by
  rw [rdf_mapping.class_construct]
  simp only [lift, bind_ok, hit, array_slice_val, owlIntersectionOf, take_correct, alloc.vec.Vec.index_slice_index,
    main_lookup triples found t at_t, run, uncurry_apply_pair]

theorem class_construct_union (miss1 : Miss triples x s owlIntersectionOf) (hit : Hit triples x s found owlUnionOf)
    (at_t : triples.val[found.val]? = some t) (xs : model.AtLeastTwo model.ClassExpression) (s' : rdf_mapping.State)
    (run : rdf_mapping.class_list2 triples kinds t.object { s with used := s.used.set found true } fuel =
      .ok (some (xs, s'))) :
    rdf_mapping.class_construct triples kinds x s fuel = .ok (some (.ObjectUnionOf xs, s')) := by
  rw [rdf_mapping.class_construct]
  simp only [lift, bind_ok, miss1, hit, array_slice_val, owlIntersectionOf, owlUnionOf, take_correct,
    alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run, uncurry_apply_pair]

theorem class_construct_complement (miss1 : Miss triples x s owlIntersectionOf) (miss2 : Miss triples x s owlUnionOf)
    (hit : Hit triples x s found owlComplementOf) (at_t : triples.val[found.val]? = some t) (c : model.ClassExpression)
    (s' : rdf_mapping.State)
    (run : rdf_mapping.class_expression triples kinds t.object { s with used := s.used.set found true } fuel =
      .ok (some (c, s'))) :
    rdf_mapping.class_construct triples kinds x s fuel = .ok (some (.ObjectComplementOf c, s')) := by
  rw [rdf_mapping.class_construct]
  simp only [lift, bind_ok, miss1, miss2, hit, array_slice_val, owlIntersectionOf, owlUnionOf, owlComplementOf,
    take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run, uncurry_apply_pair]

theorem class_construct_one_of (miss1 : Miss triples x s owlIntersectionOf) (miss2 : Miss triples x s owlUnionOf)
    (miss3 : Miss triples x s owlComplementOf) (hit : Hit triples x s found owlOneOf)
    (at_t : triples.val[found.val]? = some t) (xs : model.NonEmpty model.Individual) (s' : rdf_mapping.State)
    (run : rdf_mapping.individual_list1 triples t.object { s with used := s.used.set found true } fuel =
      .ok (some (xs, s'))) :
    rdf_mapping.class_construct triples kinds x s fuel = .ok (some (.ObjectOneOf xs, s')) := by
  rw [rdf_mapping.class_construct]
  simp only [lift, bind_ok, miss1, miss2, miss3, hit, array_slice_val, owlIntersectionOf, owlUnionOf, owlComplementOf,
    owlOneOf, take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples found t at_t, run, uncurry_apply_pair]

end leaves

/-! ### The first steps on a restriction or a construct node -/

/-- The positions of the patterns of a node after its first two. -/
theorem two_heads {l : List Nat} {head : List (List U8 × Node)} {tail : List (List U8 × Node)}
    (len : l.length = (head ++ tail).length) (two : head.length = 2) :
    ∃ h0 h1 tpos, l = [h0, h1] ++ tpos ∧ tpos.length = tail.length := by
  match l, len with
  | h0 :: h1 :: tpos, len =>
    refine ⟨h0, h1, tpos, rfl, ?_⟩
    simp only [List.length_cons, List.length_append, two] at len
    omega
  | [], len => simp [two] at len
  | [_], len => simp [two] at len; omega

theorem marked_prefix {s s1 s2 s3 : rdf_mapping.State} {h0 : Nat} {found : Usize} {pos1 : List Nat} {x : rdf.BlankNode}
    {f1 : List rdf.BlankNode} {h1 : Nat} (foundVal : found.val = h1) (m1 : Marked s s1 (fun j => j ∈ [h0]) [x])
    (m2 : Marked s1 s2 (fun j => j ∈ [found.val]) []) (m3 : Marked s2 s3 (fun j => j ∈ pos1) f1) :
    Marked s s3 (fun j => j ∈ [h0, h1] ++ pos1) (x :: f1) := by
  refine marked_same (marked_fresh_eq (marked_trans (marked_trans m1 m2) m3) (by simp)) (fun j => ?_)
  simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, foundVal]

/-- The steps of `class_expression` on an object restriction up to `object_restriction`. -/
theorem object_restriction_prefix (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    {role : model.ObjectPropertyExpression} {sR0 sR1 : Supply} {n1 : Node} {p1 : List Pattern}
    (tope : TOPE role sR0 n1 p1 sR1)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object))
    (x : rdf.BlankNode) (tailHead : List (List U8 × Node)) (rest : List Pattern) (f1 f2 : List rdf.BlankNode)
    (split1 : sR0 = f1 ++ sR1) (sub2 : BlankSubjects f2 rest) (s : rdf_mapping.State) (pos : List Nat) (fuel : Usize)
    (ready : Ready triples s pos (headPatterns x ([(rdfType, .iri owlRestriction), (owlOnProperty, n1)] ++ tailHead) ++
      (p1 ++ rest)) (x :: (f1 ++ f2)))
    (nodup : (x :: (f1 ++ f2)).Nodup)
    (distinct : (([(rdfType, .iri owlRestriction), (owlOnProperty, n1)] ++ tailHead).map (·.1)).Nodup)
    (fuelOk : 0 < fuel.val) :
    ∃ (h0 h1 : Nat) (tpos pos1 pos2 : List Nat) (s3 : rdf_mapping.State) (fewer : Usize),
      pos = [h0, h1] ++ tpos ++ (pos1 ++ pos2) ∧ tpos.length = tailHead.length ∧ pos1.length = p1.length ∧
      pos2.length = rest.length ∧ fewer.val + 1 = fuel.val ∧
      Marked s s3 (fun j => j ∈ [h0, h1] ++ pos1) (x :: f1) ∧
      rdf_mapping.class_expression triples kinds (.Blank x) s fuel =
        rdf_mapping.object_restriction triples kinds x role s3 fewer ∧
      HeadsAt triples.val s3.used.val x ([h0, h1] ++ tpos)
        ([(rdfType, .iri owlRestriction), (owlOnProperty, n1)] ++ tailHead) ∧
      (∀ j ∈ tpos, s3.used.val[j]? = some false) := by
  obtain ⟨roleFresh, roleEq, roleSubjects⟩ := tope_fresh tope
  have f1Is : f1 = roleFresh := by
    rw [roleEq] at split1
    exact (List.append_cancel_right split1).symm
  subst f1Is
  have outside : x ∉ f1 ++ f2 := (List.nodup_cons.mp nodup).1
  have restSubjects : BlankSubjects (f1 ++ f2) (p1 ++ rest) :=
    blank_subjects_append (blank_subjects_mono (blank_subjects_of roleSubjects) (fun y m => by simp [m]))
      (blank_subjects_mono sub2 (fun y m => by simp [m]))
  obtain ⟨hpos, rpos, rfl, lenH, lenR, heads⟩ := construct_setup ready restSubjects outside distinct
  obtain ⟨h0, h1, tpos, rfl, lenT⟩ := two_heads lenH rfl
  obtain ⟨pos1, pos2, rfl, at1, at2⟩ := at_split (at_append_inv ready.holds
    (by rw [head_patterns_length]; exact lenH)).2
  have nodupPos := ready.nodup
  simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, List.mem_append, not_or] at nodupPos
  have h01 : h0 ≠ h1 := nodupPos.1.1
  have room := ready.room
  simp only [List.length_cons, List.length_append] at room
  obtain ⟨s1, fewer, fewerIs, m1, step1⟩ := class_blank_restriction triples kinds x s fuel ready.complete heads
    (i := h0) rfl (fun _ => rfl) (ready.free h0 (by simp)) (by omega) fuelOk
  have heads1 := heads_rest heads rfl rfl m1
  have complete1 : SubjectsComplete triples.val s1.subjects.val (alloc.vec.Vec.len s1.subjects)
      triples.val.length := by rw [m1.subjects]; exact ready.complete
  have unused1 : s1.used.val[h1]? = some false :=
    marked_unused m1 (ready.free h1 (by simp)) (by simp; exact fun h => h01 h.symm)
  obtain ⟨found1, found1Val, find1⟩ := find_hit triples s1 x complete1 heads1 (k := 1) rfl owlOnProperty
    (fun _ => rfl) unused1
  obtain ⟨_, t1, at1', -, -, object1⟩ := heads_at_triple heads (k := 1) rfl
  have m2 := marked_nil_take s1 found1
  have m12 := marked_trans m1 m2
  have readyRole := ready_middle (pos1 := [h0, h1] ++ tpos) (pos2 := pos1) (pos3 := pos2)
    (ps1 := headPatterns x ([(rdfType, .iri owlRestriction), (owlOnProperty, n1)] ++ tailHead)) (ps2 := p1)
    (ps3 := rest) (f1 := [x]) (f2 := f1) (f3 := f2) (by simpa using ready)
    (by rw [head_patterns_length]; simp [lenT]) (at_length at1) (by simpa using nodup)
    (blank_subjects_head x _) sub2 m12
    (fun j hj => by
      simp only [List.mem_singleton] at hj
      rcases hj with h | h
      · simp [h]
      · simp [h, found1Val]) (by simp)
  obtain ⟨s3, roleRun, m3⟩ := role_complete triples tope roleEq (by simpa [head_patterns_length] using object1)
    readyRole
  have kind := node_kind_object kinds tope t1.object (by simpa using object1) roleTyped
  have at1'' : triples.val[found1.val]? = some t1 := by rw [found1Val]; exact at1'
  have step2 := (restriction_step triples kinds x s1 fewer found1 t1 find1 at1'').1 role s3 kind roleRun
  have m123 := marked_prefix found1Val m1 m2 m3
  refine ⟨h0, h1, tpos, pos1, pos2, s3, fewer, rfl, lenT, at_length at1, at_length at2, fewerIs, m123,
    by rw [step1, step2], heads_at_mono heads (fun j => marked_back m123), ?_⟩
  intro j member
  apply marked_unused m123 (ready.free j (by simp [member]))
  simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  have nodupAll := ready.nodup
  rintro ((rfl | rfl) | inPos1)
  · exact nodupPos.1.2.1 member
  · exact nodupPos.2.1.1 member
  · have := (List.nodup_append.mp (List.nodup_append.mp nodupAll).2.1).2.2
    simp at nodupAll
    exact (List.nodup_append.mp nodupPos.2.2).2.2 j member j (List.mem_append_left _ inPos1) rfl

/-- The steps of `class_expression` on a data restriction up to `data_restriction`. -/
theorem data_restriction_prefix (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (d : model.DataProperty) (dataTyped : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data))
    (x : rdf.BlankNode) (tailHead : List (List U8 × Node)) (rest : List Pattern) (f : List rdf.BlankNode)
    (sub : BlankSubjects f rest) (s : rdf_mapping.State) (pos : List Nat) (fuel : Usize)
    (ready : Ready triples s pos (headPatterns x ([(rdfType, .iri owlRestriction), (owlOnProperty, iriNode d.iri)] ++
      tailHead) ++ rest) (x :: f))
    (nodup : (x :: f).Nodup)
    (distinct : (([(rdfType, .iri owlRestriction), (owlOnProperty, iriNode d.iri)] ++ tailHead).map (·.1)).Nodup)
    (fuelOk : 0 < fuel.val) :
    ∃ (h0 h1 : Nat) (tpos pos2 : List Nat) (s2 : rdf_mapping.State) (fewer : Usize),
      pos = [h0, h1] ++ tpos ++ pos2 ∧ tpos.length = tailHead.length ∧ pos2.length = rest.length ∧
      fewer.val + 1 = fuel.val ∧ Marked s s2 (fun j => j ∈ [h0, h1]) [x] ∧
      rdf_mapping.class_expression triples kinds (.Blank x) s fuel =
        rdf_mapping.data_restriction triples kinds x d s2 fewer ∧
      HeadsAt triples.val s2.used.val x ([h0, h1] ++ tpos)
        ([(rdfType, .iri owlRestriction), (owlOnProperty, iriNode d.iri)] ++ tailHead) ∧
      (∀ j ∈ tpos, s2.used.val[j]? = some false) := by
  have outside : x ∉ f := (List.nodup_cons.mp nodup).1
  obtain ⟨hpos, rpos, rfl, lenH, lenR, heads⟩ := construct_setup ready sub outside distinct
  obtain ⟨h0, h1, tpos, rfl, lenT⟩ := two_heads lenH rfl
  have nodupPos := ready.nodup
  simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, List.mem_append, not_or] at nodupPos
  have h01 : h0 ≠ h1 := nodupPos.1.1
  have room := ready.room
  simp only [List.length_cons] at room
  obtain ⟨s1, fewer, fewerIs, m1, step1⟩ := class_blank_restriction triples kinds x s fuel ready.complete heads
    (i := h0) rfl (fun _ => rfl) (ready.free h0 (by simp)) (by omega) fuelOk
  have heads1 := heads_rest heads rfl rfl m1
  have complete1 : SubjectsComplete triples.val s1.subjects.val (alloc.vec.Vec.len s1.subjects)
      triples.val.length := by rw [m1.subjects]; exact ready.complete
  have unused1 : s1.used.val[h1]? = some false :=
    marked_unused m1 (ready.free h1 (by simp)) (by simp; exact fun h => h01 h.symm)
  obtain ⟨found1, found1Val, find1⟩ := find_hit triples s1 x complete1 heads1 (k := 1) rfl owlOnProperty
    (fun _ => rfl) unused1
  obtain ⟨_, t1, at1', -, -, object1⟩ := heads_at_triple heads (k := 1) rfl
  have m2 := marked_nil_take s1 found1
  have view1 : objectView t1.object = iriNode d.iri := by simpa using object1
  have kind := node_kind_data kinds d t1.object view1 dataTyped
  have at1'' : triples.val[found1.val]? = some t1 := by rw [found1Val]; exact at1'
  have step2 := (restriction_step triples kinds x s1 fewer found1 t1 find1 at1'').2 d kind
    (node_iri_complete t1.object d.iri view1)
  have m12 : Marked s { s1 with used := s1.used.set found1 true } (fun j => j ∈ [h0, h1]) [x] := by
    refine marked_same (marked_fresh_eq (marked_trans m1 m2) (by simp)) (fun j => ?_)
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, found1Val]
  refine ⟨h0, h1, tpos, rpos, _, fewer, rfl, lenT, by rw [lenR], fewerIs, m12, by rw [step1, step2],
    heads_at_mono heads (fun j => marked_back m12), ?_⟩
  intro j member
  apply marked_unused m12 (ready.free j (by simp [member]))
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  rintro (rfl | rfl)
  · exact nodupPos.1.2.1 member
  · exact nodupPos.2.1.1 member

/-- The steps of `class_expression` on a Boolean construct or enumeration up to `class_construct`. -/
theorem class_construct_prefix (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (x : rdf.BlankNode) (key : List U8) (value : Node) (rest : List Pattern) (f : List rdf.BlankNode)
    (sub : BlankSubjects f rest) (s : rdf_mapping.State) (pos : List Nat) (fuel : Usize)
    (ready : Ready triples s pos (headPatterns x [(rdfType, .iri owlClass), (key, value)] ++ rest) (x :: f))
    (nodup : (x :: f).Nodup) (keyType : key ≠ rdfType) (fuelOk : 0 < fuel.val) :
    ∃ (h0 h1 : Nat) (pos2 : List Nat) (s1 : rdf_mapping.State) (fewer : Usize),
      pos = [h0, h1] ++ pos2 ∧ pos2.length = rest.length ∧ fewer.val + 1 = fuel.val ∧
      Marked s s1 (fun j => j ∈ [h0]) [x] ∧
      rdf_mapping.class_expression triples kinds (.Blank x) s fuel =
        rdf_mapping.class_construct triples kinds x s1 fewer ∧
      HeadsAt triples.val s1.used.val x [h0, h1] [(rdfType, .iri owlClass), (key, value)] ∧
      s1.used.val[h1]? = some false := by
  have outside : x ∉ f := (List.nodup_cons.mp nodup).1
  obtain ⟨hpos, rpos, rfl, lenH, lenR, heads⟩ := construct_setup ready sub outside
    (by simp; exact fun h => keyType h.symm)
  obtain ⟨h0, h1, rfl⟩ : ∃ h0 h1, hpos = [h0, h1] := by
    match hpos, lenH with
    | [h0, h1], _ => exact ⟨h0, h1, rfl⟩
  have nodupPos := ready.nodup
  have h01 : h0 ≠ h1 := by intro same; subst same; simp at nodupPos
  have room := ready.room
  simp only [List.length_cons] at room
  obtain ⟨s1, fewer, fewerIs, m1, step1⟩ := class_blank_construct triples kinds x s fuel ready.complete heads
    (i := h0) rfl (fun _ => rfl)
    (by
      intro k hk same
      match k, hk with
      | 0, _ => simp [owlClass, owlRestriction] at same
      | 1, _ => simp at same; exact keyType same.1) (ready.free h0 (by simp)) (by omega) fuelOk
  refine ⟨h0, h1, rpos, s1, fewer, rfl, lenR, fewerIs, m1, step1, heads_rest heads rfl rfl m1, ?_⟩
  exact marked_unused m1 (ready.free h1 (by simp)) (by simp; exact fun h => h01 h.symm)

/-! ### Helpers for the cases of class expressions -/

theorem fresh_restriction {x : rdf.BlankNode} {s s1 s2 f1 f2 fresh : Supply} (eq1 : s = f1 ++ s1)
    (eq2 : s1 = f2 ++ s2) (split : x :: s = fresh ++ s2) : fresh = x :: (f1 ++ f2) := by
  rw [eq1, eq2] at split
  have h : (x :: (f1 ++ f2)) ++ s2 = fresh ++ s2 := by simpa using split
  exact (List.append_cancel_right h).symm

theorem node_blank {node : rdf.Object} {x : rdf.BlankNode} (view : objectView node = .blank x) :
    node = .Blank x := by
  cases node with
  | Blank b => simp only [objectView, Node.blank.injEq] at view; rw [view]
  | Iri _ => simp [objectView] at view
  | Literal _ => simp [objectView] at view

theorem one_position {l : List Nat} (len : l.length = 1) : ∃ a, l = [a] := by
  match l, len with
  | [a], _ => exact ⟨a, rfl⟩

theorem two_positions {l : List Nat} (len : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, len with
  | [a, b], _ => exact ⟨a, b, rfl⟩

/-- The patterns after the head and the first part are ready once both are read. -/
theorem ready_after {triples : alloc.vec.Vec rdf.Triple} {s s' : rdf_mapping.State} {hpos pos1 pos2 : List Nat}
    {x : rdf.BlankNode} {head : List (List U8 × Node)} {p1 p2 : List Pattern} {f1 f2 : List rdf.BlankNode}
    {m : Nat → Prop} {g : List rdf.BlankNode}
    (ready : Ready triples s (hpos ++ (pos1 ++ pos2)) (headPatterns x head ++ (p1 ++ p2)) (x :: (f1 ++ f2)))
    (lenH : hpos.length = head.length) (len1 : pos1.length = p1.length) (len2 : pos2.length = p2.length)
    (nodup : (x :: (f1 ++ f2)).Nodup) (sub1 : BlankSubjects f1 p1) (marked : Marked s s' m g)
    (inside : ∀ j, m j → j ∈ hpos ++ pos1) (recorded : g.length ≤ f1.length + 1) :
    Ready triples s' pos2 p2 f2 := by
  have ready' : Ready triples s ((hpos ++ pos1) ++ pos2 ++ []) ((headPatterns x head ++ p1) ++ p2 ++ [])
      ((x :: f1) ++ f2 ++ []) := by simpa [List.append_assoc] using ready
  exact ready_middle ready' (by simp [lenH, len1, head_patterns_length]) len2 (by simpa using nodup)
    (blank_subjects_append (blank_subjects_mono (blank_subjects_head x head) (fun y m => by simp at m; simp [m]))
      (blank_subjects_mono sub1 (fun y m => by simp [m]))) (fun _ m => by simp at m) marked inside
    (by simp; omega)

theorem marked_finish {s s3 s4 s5 : rdf_mapping.State} {h0 h1 h2 : Nat} {found : Usize} {pos1 pos2 : List Nat}
    {x : rdf.BlankNode} {f1 f2 : List rdf.BlankNode} (foundVal : found.val = h2)
    (mPrefix : Marked s s3 (fun j => j ∈ [h0, h1] ++ pos1) (x :: f1))
    (m4 : Marked s3 s4 (fun j => j ∈ [found.val]) []) (m5 : Marked s4 s5 (fun j => j ∈ pos2) f2) :
    Marked s s5 (fun j => j ∈ [h0, h1] ++ [h2] ++ (pos1 ++ pos2)) (x :: (f1 ++ f2)) := by
  refine marked_same (marked_fresh_eq (marked_trans (marked_trans mPrefix m4) m5) (by simp)) (fun j => ?_)
  simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, false_or, foundVal,
    or_assoc, or_comm, or_left_comm]

theorem marked_finish2 {s s3 s4 s5 s6 : rdf_mapping.State} {h0 h1 h2 h3 : Nat} {found found' : Usize}
    {pos1 pos2 : List Nat} {x : rdf.BlankNode} {f1 f2 : List rdf.BlankNode} (foundVal : found.val = h2)
    (foundVal' : found'.val = h3) (mPrefix : Marked s s3 (fun j => j ∈ [h0, h1] ++ pos1) (x :: f1))
    (m4 : Marked s3 s4 (fun j => j ∈ [found.val]) []) (m5 : Marked s4 s5 (fun j => j ∈ [found'.val]) [])
    (m6 : Marked s5 s6 (fun j => j ∈ pos2) f2) :
    Marked s s6 (fun j => j ∈ [h0, h1] ++ [h2, h3] ++ (pos1 ++ pos2)) (x :: (f1 ++ f2)) := by
  refine marked_same (marked_fresh_eq (marked_trans (marked_trans (marked_trans mPrefix m4) m5) m6) (by simp))
    (fun j => ?_)
  simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, false_or, foundVal,
    foundVal', or_assoc, or_comm, or_left_comm]

theorem positions_free {pos : List Nat} {used : List Bool} {a : Nat} (free : ∀ i ∈ pos, used[i]? = some false)
    (member : a ∈ pos) : used[a]? = some false := free a member

/-! ### Object restrictions -/

/-- An object restriction with a class filler, read through `object_restriction`. -/
theorem object_filler_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (key : List U8) (construct : model.ObjectPropertyExpression → model.ClassExpression → model.ClassExpression)
    (keyNodup : ([rdfType, owlOnProperty, key] : List (List U8)).Nodup)
    (leaf : ∀ (x : rdf.BlankNode) (role : model.ObjectPropertyExpression) (s : rdf_mapping.State) (fuel found : Usize)
      (t : rdf.Triple) (hpos : List Nat) (head : List (List U8 × Node)),
      HeadsAt triples.val s.used.val x hpos head → (head.map (·.1)) = [rdfType, owlOnProperty, key] →
      Hit triples x s found key → triples.val[found.val]? = some t →
      ∀ (c : model.ClassExpression) (s' : rdf_mapping.State),
      rdf_mapping.class_expression triples kinds t.object { s with used := s.used.set found true } fuel =
        .ok (some (c, s')) →
      rdf_mapping.object_restriction triples kinds x role s fuel = .ok (some (construct role c, s')))
    (role : model.ObjectPropertyExpression) (c : model.ClassExpression) (x : rdf.BlankNode) (s s1 s2 : Supply)
    (n1 n2 : Node) (p1 p2 : List Pattern) (tope : TOPE role s n1 p1 s1) (inner : TCE c s1 n2 p2 s2)
    (reads : ClassReads triples kinds c s1 n2 p2 s2)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    ClassReads triples kinds (construct role c) (x :: s) (.blank x)
      (restrictionHead x n1 ++ ⟨.blank x, key, n2⟩ :: (p1 ++ p2)) s2 := by
  intro fresh split nodup st pos node fuel view ready fuelOk
  obtain ⟨f1, eq1, sub1⟩ := tope_fresh tope
  obtain ⟨f2, eq2, sub2⟩ := tce_fresh inner
  have freshIs := fresh_restriction eq1 eq2 split
  subst freshIs
  have nodeIs := node_blank view
  subst nodeIs
  let tail : List (List U8 × Node) := [(key, n2)]
  have ready' : Ready triples st pos (headPatterns x ([(rdfType, .iri owlRestriction), (owlOnProperty, n1)] ++ tail) ++
      (p1 ++ p2)) (x :: (f1 ++ f2)) := by simpa [restrictionHead, headPatterns, tail] using ready
  simp only [restrictionHead, List.length_append, List.length_cons, List.length_nil] at fuelOk
  obtain ⟨h0, h1, tpos, pos1, pos2, s3, fewer, rfl, lenT, len1, len2, fewerIs, mPrefix, step, heads3, freeT⟩ :=
    object_restriction_prefix triples kinds tope roleTyped x tail p2 f1 f2 eq1 (blank_subjects_of sub2) st pos fuel
      ready' nodup (by simpa [tail] using keyNodup) (by omega)
  obtain ⟨h2, rfl⟩ := one_position (by simpa [tail] using lenT)
  have complete3 : SubjectsComplete triples.val s3.subjects.val (alloc.vec.Vec.len s3.subjects)
      triples.val.length := by rw [mPrefix.subjects]; exact ready.complete
  obtain ⟨found, foundVal, hit⟩ := find_hit triples s3 x complete3 heads3 (k := 2) rfl key (fun _ => rfl)
    (freeT h2 (by simp))
  obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads3 (k := 2) rfl
  have m4 := marked_nil_take s3 found
  have ready4 := ready_after (hpos := [h0, h1, h2]) (by simpa using ready') (by simp [tail]) len1 len2 nodup
    (blank_subjects_of sub1) (marked_trans mPrefix m4)
    (fun j hj => by
      simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, foundVal] at hj ⊢
      tauto) (by simp)
  obtain ⟨s5, fillerRun, m5⟩ := reads f2 eq2 (List.nodup_append.mp (List.nodup_cons.mp nodup).2).2.1 _ pos2 t.object
    fewer (by simpa [tail] using object) ready4 (by omega)
  refine ⟨s5, ?_, ?_⟩
  · rw [step]
    exact leaf x role s3 fewer found t _ _ heads3 (by simp [tail]) hit (by rw [foundVal]; exact at_t) c s5 fillerRun
  · exact marked_same (marked_finish foundVal mPrefix m4 m5) (fun j => by simp [tail])

theorem class_some_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (role : model.ObjectPropertyExpression) (c : model.ClassExpression) (x : rdf.BlankNode) (s s1 s2 : Supply)
    (n1 n2 : Node) (p1 p2 : List Pattern) (tope : TOPE role s n1 p1 s1) (inner : TCE c s1 n2 p2 s2)
    (reads : ClassReads triples kinds c s1 n2 p2 s2)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    ClassReads triples kinds (.ObjectSomeValuesFrom role c) (x :: s) (.blank x)
      (restrictionHead x n1 ++ ⟨.blank x, owlSomeValuesFrom, n2⟩ :: (p1 ++ p2)) s2 :=
  object_filler_reads triples kinds owlSomeValuesFrom .ObjectSomeValuesFrom
    (by simp [rdfType, owlOnProperty, owlSomeValuesFrom])
    (fun x role s fuel found t _ _ _ _ hit at_t c s' run =>
      object_restriction_some triples kinds x role s fuel found t hit at_t c s' run)
    role c x s s1 s2 n1 n2 p1 p2 tope inner reads roleTyped

theorem class_all_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (role : model.ObjectPropertyExpression) (c : model.ClassExpression) (x : rdf.BlankNode) (s s1 s2 : Supply)
    (n1 n2 : Node) (p1 p2 : List Pattern) (tope : TOPE role s n1 p1 s1) (inner : TCE c s1 n2 p2 s2)
    (reads : ClassReads triples kinds c s1 n2 p2 s2)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    ClassReads triples kinds (.ObjectAllValuesFrom role c) (x :: s) (.blank x)
      (restrictionHead x n1 ++ ⟨.blank x, owlAllValuesFrom, n2⟩ :: (p1 ++ p2)) s2 :=
  object_filler_reads triples kinds owlAllValuesFrom .ObjectAllValuesFrom
    (by simp [rdfType, owlOnProperty, owlAllValuesFrom])
    (fun x role s fuel found t _ _ heads keys hit at_t c s' run =>
      object_restriction_all triples kinds x role s fuel found t
        (miss_of_heads heads owlSomeValuesFrom (by rw [keys]; simp [rdfType, owlOnProperty, owlSomeValuesFrom,
          owlAllValuesFrom])) hit at_t c s' run)
    role c x s s1 s2 n1 n2 p1 p2 tope inner reads roleTyped

/-- An object restriction with a value and no filler, read through `object_restriction`. -/
theorem object_value_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (key : List U8) (value : Node) (result : model.ObjectPropertyExpression → model.ClassExpression)
    (keyNodup : ([rdfType, owlOnProperty, key] : List (List U8)).Nodup)
    (leaf : ∀ (x : rdf.BlankNode) (role : model.ObjectPropertyExpression) (s : rdf_mapping.State) (fuel found : Usize)
      (t : rdf.Triple) (hpos : List Nat) (head : List (List U8 × Node)),
      HeadsAt triples.val s.used.val x hpos head → (head.map (·.1)) = [rdfType, owlOnProperty, key] →
      Hit triples x s found key → triples.val[found.val]? = some t → objectView t.object = value →
      rdf_mapping.object_restriction triples kinds x role s fuel =
        .ok (some (result role, { s with used := s.used.set found true })))
    (role : model.ObjectPropertyExpression) (x : rdf.BlankNode) (s s1 : Supply) (n1 : Node) (p1 : List Pattern)
    (tope : TOPE role s n1 p1 s1)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    ClassReads triples kinds (result role) (x :: s) (.blank x)
      (restrictionHead x n1 ++ ⟨.blank x, key, value⟩ :: p1) s1 := by
  intro fresh split nodup st pos node fuel view ready fuelOk
  obtain ⟨f1, eq1, sub1⟩ := tope_fresh tope
  have freshIs := fresh_restriction (f2 := []) eq1 (by simp) split
  subst freshIs
  have nodeIs := node_blank view
  subst nodeIs
  let tail : List (List U8 × Node) := [(key, value)]
  have ready' : Ready triples st pos (headPatterns x ([(rdfType, .iri owlRestriction), (owlOnProperty, n1)] ++ tail) ++
      (p1 ++ [])) (x :: (f1 ++ [])) := by simpa [restrictionHead, headPatterns, tail] using ready
  simp only [restrictionHead, List.length_append, List.length_cons, List.length_nil] at fuelOk
  obtain ⟨h0, h1, tpos, pos1, pos2, s3, fewer, rfl, lenT, len1, len2, fewerIs, mPrefix, step, heads3, freeT⟩ :=
    object_restriction_prefix triples kinds tope roleTyped x tail [] f1 [] eq1 (fun _ m => by simp at m) st pos fuel
      ready' (by simpa using nodup) (by simpa [tail] using keyNodup) (by omega)
  obtain ⟨h2, rfl⟩ := one_position (by simpa [tail] using lenT)
  have noPos2 : pos2 = [] := by simpa using len2
  subst noPos2
  have complete3 : SubjectsComplete triples.val s3.subjects.val (alloc.vec.Vec.len s3.subjects)
      triples.val.length := by rw [mPrefix.subjects]; exact ready.complete
  obtain ⟨found, foundVal, hit⟩ := find_hit triples s3 x complete3 heads3 (k := 2) rfl key (fun _ => rfl)
    (freeT h2 (by simp))
  obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads3 (k := 2) rfl
  have m4 := marked_nil_take s3 found
  refine ⟨{ s3 with used := s3.used.set found true }, ?_, ?_⟩
  · rw [step]
    exact leaf x role s3 fewer found t _ _ heads3 (by simp [tail]) hit (by rw [foundVal]; exact at_t)
      (by simpa [tail] using object)
  · exact marked_same (marked_fresh_eq (marked_finish foundVal mPrefix m4 (ready_nil_marked _)) (by simp))
      (fun j => by simp [tail])

theorem class_has_value_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (role : model.ObjectPropertyExpression) (a : model.Individual) (x : rdf.BlankNode) (s s1 : Supply) (n1 : Node)
    (p1 : List Pattern) (tope : TOPE role s n1 p1 s1)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    ClassReads triples kinds (.ObjectHasValue role a) (x :: s) (.blank x)
      (restrictionHead x n1 ++ ⟨.blank x, owlHasValue, individualNode a⟩ :: p1) s1 :=
  object_value_reads triples kinds owlHasValue (individualNode a) (fun role => .ObjectHasValue role a)
    (by simp [rdfType, owlOnProperty, owlHasValue])
    (fun x role s fuel found t _ _ heads keys hit at_t view =>
      object_restriction_has_value triples kinds x role s fuel found t
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlSomeValuesFrom, owlHasValue]))
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlAllValuesFrom, owlHasValue]))
        hit at_t a (node_individual_complete t.object a view))
    role x s s1 n1 p1 tope roleTyped

theorem class_has_self_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (role : model.ObjectPropertyExpression) (x : rdf.BlankNode) (s s1 : Supply) (n1 : Node)
    (p1 : List Pattern) (tope : TOPE role s n1 p1 s1)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    ClassReads triples kinds (.ObjectHasSelf role) (x :: s) (.blank x)
      (restrictionHead x n1 ++ ⟨.blank x, owlHasSelf, trueNode⟩ :: p1) s1 :=
  object_value_reads triples kinds owlHasSelf trueNode (fun role => .ObjectHasSelf role)
    (by simp [rdfType, owlOnProperty, owlHasSelf])
    (fun x role s fuel found t _ _ heads keys hit at_t view =>
      object_restriction_has_self triples kinds x role s fuel found t
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlSomeValuesFrom, owlHasSelf]))
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlAllValuesFrom, owlHasSelf]))
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlHasValue, owlHasSelf]))
        hit at_t (true_complete t.object view))
    role x s s1 n1 p1 tope roleTyped

theorem cardinality_misses {triples : alloc.vec.Vec rdf.Triple} {x : rdf.BlankNode} {s : rdf_mapping.State}
    {hpos : List Nat} {head : List (List U8 × Node)} (heads : HeadsAt triples.val s.used.val x hpos head)
    (key : List U8) (keys : head.map (·.1) = [rdfType, owlOnProperty, key])
    (misses : ∀ P ∈ [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlHasSelf], P ≠ rdfType ∧ P ≠ owlOnProperty ∧
      P ≠ key) :
    ∀ P ∈ [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlHasSelf], Miss triples x s P := by
  intro P member
  apply miss_of_heads heads P
  rw [keys]
  obtain ⟨h1, h2, h3⟩ := misses P member
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h1, h2, h3⟩

theorem class_min_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (n : probes.Natural)
    (role : model.ObjectPropertyExpression) (x : rdf.BlankNode) (s s1 : Supply) (n1 m : Node)
    (p1 : List Pattern) (tope : TOPE role s n1 p1 s1) (natural : NaturalNode n m) (small : CardinalityReadable n)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    ClassReads triples kinds (.ObjectMinCardinality n role none) (x :: s) (.blank x)
      (restrictionHead x n1 ++ ⟨.blank x, owlMinCardinality, m⟩ :: p1) s1 :=
  object_value_reads triples kinds owlMinCardinality m (fun role => .ObjectMinCardinality n role none)
    (by simp [rdfType, owlOnProperty, owlMinCardinality])
    (fun x role s fuel found t _ _ heads keys hit at_t view => by
      have misses := cardinality_misses heads owlMinCardinality keys (by
        simp [rdfType, owlOnProperty, owlMinCardinality, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlHasSelf])
      rw [object_restriction_cardinality triples kinds x role s fuel (misses _ (by simp)) (misses _ (by simp))
        (misses _ (by simp)) (misses _ (by simp))]
      exact object_cardinality_min triples kinds x role s fuel found t hit at_t n
        (natural_complete t.object n (by rw [view]; exact natural) small))
    role x s s1 n1 p1 tope roleTyped

theorem class_max_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (n : probes.Natural)
    (role : model.ObjectPropertyExpression) (x : rdf.BlankNode) (s s1 : Supply) (n1 m : Node)
    (p1 : List Pattern) (tope : TOPE role s n1 p1 s1) (natural : NaturalNode n m) (small : CardinalityReadable n)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    ClassReads triples kinds (.ObjectMaxCardinality n role none) (x :: s) (.blank x)
      (restrictionHead x n1 ++ ⟨.blank x, owlMaxCardinality, m⟩ :: p1) s1 :=
  object_value_reads triples kinds owlMaxCardinality m (fun role => .ObjectMaxCardinality n role none)
    (by simp [rdfType, owlOnProperty, owlMaxCardinality])
    (fun x role s fuel found t _ _ heads keys hit at_t view => by
      have misses := cardinality_misses heads owlMaxCardinality keys (by
        simp [rdfType, owlOnProperty, owlMaxCardinality, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlHasSelf])
      rw [object_restriction_cardinality triples kinds x role s fuel (misses _ (by simp)) (misses _ (by simp))
        (misses _ (by simp)) (misses _ (by simp))]
      exact object_cardinality_max triples kinds x role s fuel found t
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlMinCardinality, owlMaxCardinality]))
        hit at_t n (natural_complete t.object n (by rw [view]; exact natural) small))
    role x s s1 n1 p1 tope roleTyped

theorem class_exact_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (n : probes.Natural)
    (role : model.ObjectPropertyExpression) (x : rdf.BlankNode) (s s1 : Supply) (n1 m : Node)
    (p1 : List Pattern) (tope : TOPE role s n1 p1 s1) (natural : NaturalNode n m) (small : CardinalityReadable n)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    ClassReads triples kinds (.ObjectExactCardinality n role none) (x :: s) (.blank x)
      (restrictionHead x n1 ++ ⟨.blank x, owlCardinality, m⟩ :: p1) s1 :=
  object_value_reads triples kinds owlCardinality m (fun role => .ObjectExactCardinality n role none)
    (by simp [rdfType, owlOnProperty, owlCardinality])
    (fun x role s fuel found t _ _ heads keys hit at_t view => by
      have misses := cardinality_misses heads owlCardinality keys (by
        simp [rdfType, owlOnProperty, owlCardinality, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlHasSelf])
      rw [object_restriction_cardinality triples kinds x role s fuel (misses _ (by simp)) (misses _ (by simp))
        (misses _ (by simp)) (misses _ (by simp))]
      exact object_cardinality_exact triples kinds x role s fuel found t
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlMinCardinality, owlCardinality]))
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlMaxCardinality, owlCardinality]))
        hit at_t n (natural_complete t.object n (by rw [view]; exact natural) small))
    role x s s1 n1 p1 tope roleTyped

/-- A qualified object cardinality restriction, read through `object_restriction`. -/
theorem object_qualified_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (key : List U8) (m : Node)
    (construct : model.ObjectPropertyExpression → model.ClassExpression → model.ClassExpression)
    (keyNodup : ([rdfType, owlOnProperty, key, owlOnClass] : List (List U8)).Nodup)
    (leaf : ∀ (x : rdf.BlankNode) (role : model.ObjectPropertyExpression) (s : rdf_mapping.State) (fuel found : Usize)
      (t : rdf.Triple) (hpos : List Nat) (head : List (List U8 × Node)),
      HeadsAt triples.val s.used.val x hpos head → (head.map (·.1)) = [rdfType, owlOnProperty, key, owlOnClass] →
      Hit triples x s found key → triples.val[found.val]? = some t → objectView t.object = m →
      ∀ (c : model.ClassExpression) (s' : rdf_mapping.State),
      rdf_mapping.on_class triples kinds x { s with used := s.used.set found true } fuel = .ok (some (c, s')) →
      rdf_mapping.object_restriction triples kinds x role s fuel = .ok (some (construct role c, s')))
    (role : model.ObjectPropertyExpression) (c : model.ClassExpression) (x : rdf.BlankNode) (s s1 s2 : Supply)
    (n1 n2 : Node) (p1 p2 : List Pattern) (tope : TOPE role s n1 p1 s1) (inner : TCE c s1 n2 p2 s2)
    (reads : ClassReads triples kinds c s1 n2 p2 s2)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    ClassReads triples kinds (construct role c) (x :: s) (.blank x)
      (restrictionHead x n1 ++ ⟨.blank x, key, m⟩ :: ⟨.blank x, owlOnClass, n2⟩ :: (p1 ++ p2)) s2 := by
  intro fresh split nodup st pos node fuel view ready fuelOk
  obtain ⟨f1, eq1, sub1⟩ := tope_fresh tope
  obtain ⟨f2, eq2, sub2⟩ := tce_fresh inner
  have freshIs := fresh_restriction eq1 eq2 split
  subst freshIs
  have nodeIs := node_blank view
  subst nodeIs
  let tail : List (List U8 × Node) := [(key, m), (owlOnClass, n2)]
  have ready' : Ready triples st pos (headPatterns x ([(rdfType, .iri owlRestriction), (owlOnProperty, n1)] ++ tail) ++
      (p1 ++ p2)) (x :: (f1 ++ f2)) := by simpa [restrictionHead, headPatterns, tail] using ready
  simp only [restrictionHead, List.length_append, List.length_cons, List.length_nil] at fuelOk
  obtain ⟨h0, h1, tpos, pos1, pos2, s3, fewer, rfl, lenT, len1, len2, fewerIs, mPrefix, step, heads3, freeT⟩ :=
    object_restriction_prefix triples kinds tope roleTyped x tail p2 f1 f2 eq1 (blank_subjects_of sub2) st pos fuel
      ready' nodup (by simpa [tail] using keyNodup) (by omega)
  obtain ⟨h2, h3, rfl⟩ := two_positions (by simpa [tail] using lenT)
  have nodupPos := ready.nodup
  simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, List.mem_append, not_or] at nodupPos
  have h23 : h2 ≠ h3 := nodupPos.2.2.1.1
  have complete3 : SubjectsComplete triples.val s3.subjects.val (alloc.vec.Vec.len s3.subjects)
      triples.val.length := by rw [mPrefix.subjects]; exact ready.complete
  obtain ⟨found2, found2Val, hit2⟩ := find_hit triples s3 x complete3 heads3 (k := 2) rfl key (fun _ => rfl)
    (freeT h2 (by simp))
  obtain ⟨_, t2, at2, -, -, object2⟩ := heads_at_triple heads3 (k := 2) rfl
  have m4 := marked_nil_take s3 found2
  let s4 : rdf_mapping.State := { s3 with used := s3.used.set found2 true }
  have heads4 := heads_rest heads3 rfl rfl m4
  have unused3 : s4.used.val[h3]? = some false :=
    marked_unused m4 (freeT h3 (by simp)) (by simp [found2Val]; exact fun h => h23 h.symm)
  obtain ⟨found3, found3Val, hit3⟩ := find_hit triples s4 x (by rw [m4.subjects]; exact complete3) heads4 (k := 3)
    rfl owlOnClass (fun _ => rfl) unused3
  obtain ⟨_, t3, at3, -, -, object3⟩ := heads_at_triple heads3 (k := 3) rfl
  have m5 := marked_nil_take s4 found3
  have ready6 := ready_after (hpos := [h0, h1, h2, h3]) (by simpa using ready') (by simp [tail]) len1 len2 nodup
    (blank_subjects_of sub1) (marked_trans (marked_trans mPrefix m4) m5)
    (fun j hj => by
      simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, found2Val, found3Val]
        at hj ⊢
      tauto) (by simp)
  obtain ⟨s6, fillerRun, m6⟩ := reads f2 eq2 (List.nodup_append.mp (List.nodup_cons.mp nodup).2).2.1 _ pos2 t3.object
    fewer (by simpa [tail] using object3) ready6 (by omega)
  have onClass := on_class_run triples kinds x fewer s4 found3 t3 hit3 (by rw [found3Val]; exact at3) c s6 fillerRun
  refine ⟨s6, ?_, ?_⟩
  · rw [step]
    exact leaf x role s3 fewer found2 t2 _ _ heads3 (by simp [tail]) hit2 (by rw [found2Val]; exact at2)
      (by simpa [tail] using object2) c s6 onClass
  · exact marked_same (marked_finish2 found2Val found3Val mPrefix m4 m5 m6) (fun j => by simp [tail])

theorem qualified_misses {triples : alloc.vec.Vec rdf.Triple} {x : rdf.BlankNode} {s : rdf_mapping.State}
    {hpos : List Nat} {head : List (List U8 × Node)} (heads : HeadsAt triples.val s.used.val x hpos head)
    (key : List U8) (keys : head.map (·.1) = [rdfType, owlOnProperty, key, owlOnClass])
    (P : List U8) (h1 : P ≠ rdfType) (h2 : P ≠ owlOnProperty) (h3 : P ≠ key) (h4 : P ≠ owlOnClass) :
    Miss triples x s P := by
  apply miss_of_heads heads P
  rw [keys]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h1, h2, h3, h4⟩

theorem object_restriction_qualified {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {x : rdf.BlankNode} {role : model.ObjectPropertyExpression} {s : rdf_mapping.State} {fuel : Usize}
    {hpos : List Nat} {head : List (List U8 × Node)} (heads : HeadsAt triples.val s.used.val x hpos head)
    (key : List U8) (keys : head.map (·.1) = [rdfType, owlOnProperty, key, owlOnClass])
    (distinct : ∀ P ∈ [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlHasSelf, owlMinCardinality,
      owlMaxCardinality, owlCardinality], P ≠ key) :
    rdf_mapping.object_restriction triples kinds x role s fuel =
      rdf_mapping.object_qualified triples kinds x role s fuel := by
  have miss : ∀ P ∈ [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlHasSelf, owlMinCardinality,
      owlMaxCardinality, owlCardinality], Miss triples x s P := by
    intro P member
    apply qualified_misses heads key keys P _ _ (distinct P member) <;>
    · simp at member
      rcases member with h | h | h | h | h | h | h <;> subst h <;>
        simp [rdfType, owlOnProperty, owlOnClass, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlHasSelf,
          owlMinCardinality, owlMaxCardinality, owlCardinality]
  rw [object_restriction_cardinality triples kinds x role s fuel (miss _ (by simp)) (miss _ (by simp))
    (miss _ (by simp)) (miss _ (by simp)),
    object_cardinality_qualified triples kinds x role s fuel (miss _ (by simp)) (miss _ (by simp)) (miss _ (by simp))]

theorem class_min_qualified_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (n : probes.Natural)
    (role : model.ObjectPropertyExpression) (c : model.ClassExpression) (x : rdf.BlankNode) (s s1 s2 : Supply)
    (n1 n2 m : Node) (p1 p2 : List Pattern) (tope : TOPE role s n1 p1 s1) (natural : NaturalNode n m)
    (small : CardinalityReadable n) (inner : TCE c s1 n2 p2 s2) (reads : ClassReads triples kinds c s1 n2 p2 s2)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    ClassReads triples kinds (.ObjectMinCardinality n role (some c)) (x :: s) (.blank x)
      (restrictionHead x n1 ++ ⟨.blank x, owlMinQualifiedCardinality, m⟩ :: ⟨.blank x, owlOnClass, n2⟩ ::
        (p1 ++ p2)) s2 :=
  object_qualified_reads triples kinds owlMinQualifiedCardinality m (fun role c => .ObjectMinCardinality n role (some c))
    (by simp [rdfType, owlOnProperty, owlMinQualifiedCardinality, owlOnClass])
    (fun x role s fuel found t _ _ heads keys hit at_t view c s' onClass => by
      rw [object_restriction_qualified heads _ keys (by
        simp [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlHasSelf, owlMinCardinality, owlMaxCardinality,
          owlCardinality, owlMinQualifiedCardinality])]
      exact object_qualified_min triples kinds x role s fuel found t hit at_t n
        (natural_complete t.object n (by rw [view]; exact natural) small) c s' onClass)
    role c x s s1 s2 n1 n2 p1 p2 tope inner reads roleTyped

theorem class_max_qualified_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (n : probes.Natural)
    (role : model.ObjectPropertyExpression) (c : model.ClassExpression) (x : rdf.BlankNode) (s s1 s2 : Supply)
    (n1 n2 m : Node) (p1 p2 : List Pattern) (tope : TOPE role s n1 p1 s1) (natural : NaturalNode n m)
    (small : CardinalityReadable n) (inner : TCE c s1 n2 p2 s2) (reads : ClassReads triples kinds c s1 n2 p2 s2)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    ClassReads triples kinds (.ObjectMaxCardinality n role (some c)) (x :: s) (.blank x)
      (restrictionHead x n1 ++ ⟨.blank x, owlMaxQualifiedCardinality, m⟩ :: ⟨.blank x, owlOnClass, n2⟩ ::
        (p1 ++ p2)) s2 :=
  object_qualified_reads triples kinds owlMaxQualifiedCardinality m (fun role c => .ObjectMaxCardinality n role (some c))
    (by simp [rdfType, owlOnProperty, owlMaxQualifiedCardinality, owlOnClass])
    (fun x role s fuel found t _ _ heads keys hit at_t view c s' onClass => by
      rw [object_restriction_qualified heads _ keys (by
        simp [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlHasSelf, owlMinCardinality, owlMaxCardinality,
          owlCardinality, owlMaxQualifiedCardinality])]
      exact object_qualified_max triples kinds x role s fuel found t
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlMinQualifiedCardinality,
          owlMaxQualifiedCardinality, owlOnClass]))
        hit at_t n (natural_complete t.object n (by rw [view]; exact natural) small) c s' onClass)
    role c x s s1 s2 n1 n2 p1 p2 tope inner reads roleTyped

theorem class_exact_qualified_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (n : probes.Natural) (role : model.ObjectPropertyExpression) (c : model.ClassExpression) (x : rdf.BlankNode)
    (s s1 s2 : Supply) (n1 n2 m : Node) (p1 p2 : List Pattern) (tope : TOPE role s n1 p1 s1)
    (natural : NaturalNode n m) (small : CardinalityReadable n) (inner : TCE c s1 n2 p2 s2)
    (reads : ClassReads triples kinds c s1 n2 p2 s2)
    (roleTyped : ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object)) :
    ClassReads triples kinds (.ObjectExactCardinality n role (some c)) (x :: s) (.blank x)
      (restrictionHead x n1 ++ ⟨.blank x, owlQualifiedCardinality, m⟩ :: ⟨.blank x, owlOnClass, n2⟩ ::
        (p1 ++ p2)) s2 :=
  object_qualified_reads triples kinds owlQualifiedCardinality m
    (fun role c => .ObjectExactCardinality n role (some c))
    (by simp [rdfType, owlOnProperty, owlQualifiedCardinality, owlOnClass])
    (fun x role s fuel found t _ _ heads keys hit at_t view c s' onClass => by
      rw [object_restriction_qualified heads _ keys (by
        simp [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlHasSelf, owlMinCardinality, owlMaxCardinality,
          owlCardinality, owlQualifiedCardinality])]
      exact object_qualified_exact triples kinds x role s fuel found t
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlMinQualifiedCardinality,
          owlQualifiedCardinality, owlOnClass]))
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlMaxQualifiedCardinality,
          owlQualifiedCardinality, owlOnClass]))
        hit at_t n (natural_complete t.object n (by rw [view]; exact natural) small) c s' onClass)
    role c x s s1 s2 n1 n2 p1 p2 tope inner reads roleTyped

/-! ### Data restrictions -/

theorem marked_data_prefix {s s2 : rdf_mapping.State} {h0 h1 : Nat} {x : rdf.BlankNode}
    (m : Marked s s2 (fun j => j ∈ [h0, h1]) [x]) : Marked s s2 (fun j => j ∈ [h0, h1] ++ ([] : List Nat)) (x :: []) :=
  marked_same m (fun j => by simp)

/-- A data restriction with a data range filler, read through `data_restriction`. -/
theorem data_filler_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (key : List U8) (construct : model.DataProperty → model.DataRange → model.ClassExpression)
    (keyNodup : ([rdfType, owlOnProperty, key] : List (List U8)).Nodup)
    (leaf : ∀ (x : rdf.BlankNode) (d : model.DataProperty) (s : rdf_mapping.State) (fuel found : Usize)
      (t : rdf.Triple) (hpos : List Nat) (head : List (List U8 × Node)),
      HeadsAt triples.val s.used.val x hpos head → (head.map (·.1)) = [rdfType, owlOnProperty, key] →
      Hit triples x s found key → triples.val[found.val]? = some t →
      ∀ (r : model.DataRange) (s' : rdf_mapping.State),
      rdf_mapping.data_range triples kinds t.object { s with used := s.used.set found true } fuel = .ok (some (r, s')) →
      rdf_mapping.data_restriction triples kinds x d s fuel = .ok (some (construct d r, s')))
    (d : model.DataProperty) (r : model.DataRange) (x : rdf.BlankNode) (s s1 : Supply) (n : Node) (p : List Pattern)
    (inner : TDR r s n p s1) (reads : RangeReads triples kinds r s n p s1)
    (dataTyped : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data)) :
    ClassReads triples kinds (construct d r) (x :: s) (.blank x)
      (restrictionHead x (iriNode d.iri) ++ ⟨.blank x, key, n⟩ :: p) s1 := by
  intro fresh split nodup st pos node fuel view ready fuelOk
  obtain ⟨f, eqf, subf⟩ := tdr_fresh inner
  have freshIs := fresh_restriction (f1 := []) (by simp) eqf split
  simp only [List.nil_append] at freshIs
  subst freshIs
  have nodeIs := node_blank view
  subst nodeIs
  let tail : List (List U8 × Node) := [(key, n)]
  have ready' : Ready triples st pos (headPatterns x ([(rdfType, .iri owlRestriction), (owlOnProperty, iriNode d.iri)] ++
      tail) ++ p) (x :: f) := by simpa [restrictionHead, headPatterns, tail] using ready
  simp only [restrictionHead, List.length_append, List.length_cons, List.length_nil] at fuelOk
  obtain ⟨h0, h1, tpos, pos2, s2, fewer, rfl, lenT, len2, fewerIs, mPrefix, step, heads2, freeT⟩ :=
    data_restriction_prefix triples kinds d dataTyped x tail p f (blank_subjects_of subf) st pos fuel ready' nodup
      (by simpa [tail] using keyNodup) (by omega)
  obtain ⟨h2, rfl⟩ := one_position (by simpa [tail] using lenT)
  have complete2 : SubjectsComplete triples.val s2.subjects.val (alloc.vec.Vec.len s2.subjects)
      triples.val.length := by rw [mPrefix.subjects]; exact ready.complete
  obtain ⟨found, foundVal, hit⟩ := find_hit triples s2 x complete2 heads2 (k := 2) rfl key (fun _ => rfl)
    (freeT h2 (by simp))
  obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads2 (k := 2) rfl
  have m3 := marked_nil_take s2 found
  have ready4 := ready_after (hpos := [h0, h1, h2]) (pos1 := []) (p1 := []) (f1 := []) (by simpa using ready')
    (by simp [tail]) rfl len2 (by simpa using nodup) (fun _ m => by simp at m)
    (marked_trans (marked_data_prefix mPrefix) m3)
    (fun j hj => by
      simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, foundVal] at hj ⊢
      tauto) (by simp)
  obtain ⟨s4, fillerRun, m4⟩ := reads f eqf (List.nodup_cons.mp nodup).2 _ pos2 t.object fewer
    (by simpa [tail] using object) ready4 (by omega)
  refine ⟨s4, ?_, ?_⟩
  · rw [step]
    exact leaf x d s2 fewer found t _ _ heads2 (by simp [tail]) hit (by rw [foundVal]; exact at_t) r s4 fillerRun
  · exact marked_same (marked_fresh_eq (marked_finish foundVal (marked_data_prefix mPrefix) m3 m4) (by simp))
      (fun j => by simp [tail])

/-- A data restriction with a value and no filler, read through `data_restriction`. -/
theorem data_value_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (key : List U8) (value : Node) (result : model.DataProperty → model.ClassExpression)
    (keyNodup : ([rdfType, owlOnProperty, key] : List (List U8)).Nodup)
    (leaf : ∀ (x : rdf.BlankNode) (d : model.DataProperty) (s : rdf_mapping.State) (fuel found : Usize)
      (t : rdf.Triple) (hpos : List Nat) (head : List (List U8 × Node)),
      HeadsAt triples.val s.used.val x hpos head → (head.map (·.1)) = [rdfType, owlOnProperty, key] →
      Hit triples x s found key → triples.val[found.val]? = some t → objectView t.object = value →
      rdf_mapping.data_restriction triples kinds x d s fuel =
        .ok (some (result d, { s with used := s.used.set found true })))
    (d : model.DataProperty) (x : rdf.BlankNode) (s : Supply)
    (dataTyped : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data)) :
    ClassReads triples kinds (result d) (x :: s) (.blank x)
      (restrictionHead x (iriNode d.iri) ++ [⟨.blank x, key, value⟩]) s := by
  intro fresh split nodup st pos node fuel view ready fuelOk
  have freshIs : fresh = [x] := by
    have h : [x] ++ s = fresh ++ s := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  have nodeIs := node_blank view
  subst nodeIs
  let tail : List (List U8 × Node) := [(key, value)]
  have ready' : Ready triples st pos (headPatterns x ([(rdfType, .iri owlRestriction), (owlOnProperty, iriNode d.iri)] ++
      tail) ++ []) (x :: []) := by simpa [restrictionHead, headPatterns, tail] using ready
  simp only [restrictionHead, List.length_append, List.length_cons, List.length_nil] at fuelOk
  obtain ⟨h0, h1, tpos, pos2, s2, fewer, rfl, lenT, len2, fewerIs, mPrefix, step, heads2, freeT⟩ :=
    data_restriction_prefix triples kinds d dataTyped x tail [] [] (fun _ m => by simp at m) st pos fuel ready'
      (by simp) (by simpa [tail] using keyNodup) (by omega)
  obtain ⟨h2, rfl⟩ := one_position (by simpa [tail] using lenT)
  have noPos2 : pos2 = [] := by simpa using len2
  subst noPos2
  have complete2 : SubjectsComplete triples.val s2.subjects.val (alloc.vec.Vec.len s2.subjects)
      triples.val.length := by rw [mPrefix.subjects]; exact ready.complete
  obtain ⟨found, foundVal, hit⟩ := find_hit triples s2 x complete2 heads2 (k := 2) rfl key (fun _ => rfl)
    (freeT h2 (by simp))
  obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads2 (k := 2) rfl
  have m3 := marked_nil_take s2 found
  refine ⟨{ s2 with used := s2.used.set found true }, ?_, ?_⟩
  · rw [step]
    exact leaf x d s2 fewer found t _ _ heads2 (by simp [tail]) hit (by rw [foundVal]; exact at_t)
      (by simpa [tail] using object)
  · refine marked_same (marked_fresh_eq (marked_trans mPrefix m3) (by simp)) (fun j => ?_)
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, false_or, foundVal,
      or_assoc]

theorem class_data_some_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (d : model.DataProperty) (r : model.DataRange) (x : rdf.BlankNode) (s s1 : Supply) (n : Node) (p : List Pattern)
    (inner : TDR r s n p s1) (reads : RangeReads triples kinds r s n p s1)
    (dataTyped : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data)) :
    ClassReads triples kinds (.DataSomeValuesFrom d r) (x :: s) (.blank x)
      (restrictionHead x (iriNode d.iri) ++ ⟨.blank x, owlSomeValuesFrom, n⟩ :: p) s1 :=
  data_filler_reads triples kinds owlSomeValuesFrom .DataSomeValuesFrom
    (by simp [rdfType, owlOnProperty, owlSomeValuesFrom])
    (fun x d s fuel found t _ _ _ _ hit at_t r s' run =>
      data_restriction_some triples kinds x d s fuel found t hit at_t r s' run)
    d r x s s1 n p inner reads dataTyped

theorem class_data_all_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (d : model.DataProperty) (r : model.DataRange) (x : rdf.BlankNode) (s s1 : Supply) (n : Node) (p : List Pattern)
    (inner : TDR r s n p s1) (reads : RangeReads triples kinds r s n p s1)
    (dataTyped : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data)) :
    ClassReads triples kinds (.DataAllValuesFrom d r) (x :: s) (.blank x)
      (restrictionHead x (iriNode d.iri) ++ ⟨.blank x, owlAllValuesFrom, n⟩ :: p) s1 :=
  data_filler_reads triples kinds owlAllValuesFrom .DataAllValuesFrom
    (by simp [rdfType, owlOnProperty, owlAllValuesFrom])
    (fun x d s fuel found t _ _ heads keys hit at_t r s' run =>
      data_restriction_all triples kinds x d s fuel found t
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlSomeValuesFrom, owlAllValuesFrom]))
        hit at_t r s' run)
    d r x s s1 n p inner reads dataTyped

theorem class_data_has_value_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (d : model.DataProperty) (v : model.Literal) (x : rdf.BlankNode) (s : Supply) (n : Node)
    (literal : LiteralNode v n) (readable : LiteralReadable v)
    (dataTyped : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data)) :
    ClassReads triples kinds (.DataHasValue d v) (x :: s) (.blank x)
      (restrictionHead x (iriNode d.iri) ++ [⟨.blank x, owlHasValue, n⟩]) s :=
  data_value_reads triples kinds owlHasValue n (fun d => .DataHasValue d v)
    (by simp [rdfType, owlOnProperty, owlHasValue])
    (fun x d s fuel found t _ _ heads keys hit at_t view =>
      data_restriction_has_value triples kinds x d s fuel found t
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlSomeValuesFrom, owlHasValue]))
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlAllValuesFrom, owlHasValue]))
        hit at_t v (literal_complete t.object v n literal readable view))
    d x s dataTyped

theorem data_cardinality_misses {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {x : rdf.BlankNode} {d : model.DataProperty} {s : rdf_mapping.State} {fuel : Usize}
    {hpos : List Nat} {head : List (List U8 × Node)} (heads : HeadsAt triples.val s.used.val x hpos head)
    (key : List U8) (keys : head.map (·.1) = [rdfType, owlOnProperty, key])
    (misses : ∀ P ∈ [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue], P ≠ rdfType ∧ P ≠ owlOnProperty ∧ P ≠ key) :
    rdf_mapping.data_restriction triples kinds x d s fuel = rdf_mapping.data_cardinality triples kinds x d s fuel := by
  have miss : ∀ P ∈ [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue], Miss triples x s P := by
    intro P member
    apply miss_of_heads heads P
    rw [keys]
    obtain ⟨h1, h2, h3⟩ := misses P member
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨h1, h2, h3⟩
  exact data_restriction_cardinality triples kinds x d s fuel (miss _ (by simp)) (miss _ (by simp)) (miss _ (by simp))

theorem class_data_min_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (n : probes.Natural)
    (d : model.DataProperty) (x : rdf.BlankNode) (s : Supply) (m : Node) (natural : NaturalNode n m)
    (small : CardinalityReadable n) (dataTyped : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data)) :
    ClassReads triples kinds (.DataMinCardinality n d none) (x :: s) (.blank x)
      (restrictionHead x (iriNode d.iri) ++ [⟨.blank x, owlMinCardinality, m⟩]) s :=
  data_value_reads triples kinds owlMinCardinality m (fun d => .DataMinCardinality n d none)
    (by simp [rdfType, owlOnProperty, owlMinCardinality])
    (fun x d s fuel found t _ _ heads keys hit at_t view => by
      rw [data_cardinality_misses heads _ keys (by
        simp [rdfType, owlOnProperty, owlMinCardinality, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue])]
      exact data_cardinality_min triples kinds x d s fuel found t hit at_t n
        (natural_complete t.object n (by rw [view]; exact natural) small))
    d x s dataTyped

theorem class_data_max_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (n : probes.Natural)
    (d : model.DataProperty) (x : rdf.BlankNode) (s : Supply) (m : Node) (natural : NaturalNode n m)
    (small : CardinalityReadable n) (dataTyped : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data)) :
    ClassReads triples kinds (.DataMaxCardinality n d none) (x :: s) (.blank x)
      (restrictionHead x (iriNode d.iri) ++ [⟨.blank x, owlMaxCardinality, m⟩]) s :=
  data_value_reads triples kinds owlMaxCardinality m (fun d => .DataMaxCardinality n d none)
    (by simp [rdfType, owlOnProperty, owlMaxCardinality])
    (fun x d s fuel found t _ _ heads keys hit at_t view => by
      rw [data_cardinality_misses heads _ keys (by
        simp [rdfType, owlOnProperty, owlMaxCardinality, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue])]
      exact data_cardinality_max triples kinds x d s fuel found t
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlMinCardinality, owlMaxCardinality]))
        hit at_t n (natural_complete t.object n (by rw [view]; exact natural) small))
    d x s dataTyped

theorem class_data_exact_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (n : probes.Natural)
    (d : model.DataProperty) (x : rdf.BlankNode) (s : Supply) (m : Node) (natural : NaturalNode n m)
    (small : CardinalityReadable n) (dataTyped : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data)) :
    ClassReads triples kinds (.DataExactCardinality n d none) (x :: s) (.blank x)
      (restrictionHead x (iriNode d.iri) ++ [⟨.blank x, owlCardinality, m⟩]) s :=
  data_value_reads triples kinds owlCardinality m (fun d => .DataExactCardinality n d none)
    (by simp [rdfType, owlOnProperty, owlCardinality])
    (fun x d s fuel found t _ _ heads keys hit at_t view => by
      rw [data_cardinality_misses heads _ keys (by
        simp [rdfType, owlOnProperty, owlCardinality, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue])]
      exact data_cardinality_exact triples kinds x d s fuel found t
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlMinCardinality, owlCardinality]))
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlMaxCardinality, owlCardinality]))
        hit at_t n (natural_complete t.object n (by rw [view]; exact natural) small))
    d x s dataTyped

/-- A qualified data cardinality restriction, read through `data_restriction`. -/
theorem data_qualified_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (key : List U8) (m : Node) (construct : model.DataProperty → model.DataRange → model.ClassExpression)
    (keyNodup : ([rdfType, owlOnProperty, key, owlOnDataRange] : List (List U8)).Nodup)
    (leaf : ∀ (x : rdf.BlankNode) (d : model.DataProperty) (s : rdf_mapping.State) (fuel found : Usize)
      (t : rdf.Triple) (hpos : List Nat) (head : List (List U8 × Node)),
      HeadsAt triples.val s.used.val x hpos head → (head.map (·.1)) = [rdfType, owlOnProperty, key, owlOnDataRange] →
      Hit triples x s found key → triples.val[found.val]? = some t → objectView t.object = m →
      ∀ (r : model.DataRange) (s' : rdf_mapping.State),
      rdf_mapping.on_data_range triples kinds x { s with used := s.used.set found true } fuel = .ok (some (r, s')) →
      rdf_mapping.data_restriction triples kinds x d s fuel = .ok (some (construct d r, s')))
    (d : model.DataProperty) (r : model.DataRange) (x : rdf.BlankNode) (s s1 : Supply) (rn : Node) (p : List Pattern)
    (inner : TDR r s rn p s1) (reads : RangeReads triples kinds r s rn p s1)
    (dataTyped : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data)) :
    ClassReads triples kinds (construct d r) (x :: s) (.blank x)
      (restrictionHead x (iriNode d.iri) ++ ⟨.blank x, key, m⟩ :: ⟨.blank x, owlOnDataRange, rn⟩ :: p) s1 := by
  intro fresh split nodup st pos node fuel view ready fuelOk
  obtain ⟨f, eqf, subf⟩ := tdr_fresh inner
  have freshIs := fresh_restriction (f1 := []) (by simp) eqf split
  simp only [List.nil_append] at freshIs
  subst freshIs
  have nodeIs := node_blank view
  subst nodeIs
  let tail : List (List U8 × Node) := [(key, m), (owlOnDataRange, rn)]
  have ready' : Ready triples st pos (headPatterns x ([(rdfType, .iri owlRestriction), (owlOnProperty, iriNode d.iri)] ++
      tail) ++ p) (x :: f) := by simpa [restrictionHead, headPatterns, tail] using ready
  simp only [restrictionHead, List.length_append, List.length_cons, List.length_nil] at fuelOk
  obtain ⟨h0, h1, tpos, pos2, s2, fewer, rfl, lenT, len2, fewerIs, mPrefix, step, heads2, freeT⟩ :=
    data_restriction_prefix triples kinds d dataTyped x tail p f (blank_subjects_of subf) st pos fuel ready' nodup
      (by simpa [tail] using keyNodup) (by omega)
  obtain ⟨h2, h3, rfl⟩ := two_positions (by simpa [tail] using lenT)
  have nodupPos := ready.nodup
  simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, List.mem_append, not_or] at nodupPos
  have h23 : h2 ≠ h3 := nodupPos.2.2.1.1
  have complete2 : SubjectsComplete triples.val s2.subjects.val (alloc.vec.Vec.len s2.subjects)
      triples.val.length := by rw [mPrefix.subjects]; exact ready.complete
  obtain ⟨found2, found2Val, hit2⟩ := find_hit triples s2 x complete2 heads2 (k := 2) rfl key (fun _ => rfl)
    (freeT h2 (by simp))
  obtain ⟨_, t2, at2, -, -, object2⟩ := heads_at_triple heads2 (k := 2) rfl
  have m3 := marked_nil_take s2 found2
  let s3 : rdf_mapping.State := { s2 with used := s2.used.set found2 true }
  have heads3 := heads_rest heads2 rfl rfl m3
  have unused3 : s3.used.val[h3]? = some false :=
    marked_unused m3 (freeT h3 (by simp)) (by simp [found2Val]; exact fun h => h23 h.symm)
  obtain ⟨found3, found3Val, hit3⟩ := find_hit triples s3 x (by rw [m3.subjects]; exact complete2) heads3 (k := 3)
    rfl owlOnDataRange (fun _ => rfl) unused3
  obtain ⟨_, t3, at3, -, -, object3⟩ := heads_at_triple heads2 (k := 3) rfl
  have m4 := marked_nil_take s3 found3
  have ready5 := ready_after (hpos := [h0, h1, h2, h3]) (pos1 := []) (p1 := []) (f1 := []) (by simpa using ready')
    (by simp [tail]) rfl len2 (by simpa using nodup) (fun _ m => by simp at m)
    (marked_trans (marked_trans (marked_data_prefix mPrefix) m3) m4)
    (fun j hj => by
      simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, found2Val, found3Val]
        at hj ⊢
      tauto) (by simp)
  obtain ⟨s5, fillerRun, m5⟩ := reads f eqf (List.nodup_cons.mp nodup).2 _ pos2 t3.object fewer
    (by simpa [tail] using object3) ready5 (by omega)
  have onRange := on_data_range_run triples kinds x fewer s3 found3 t3 hit3 (by rw [found3Val]; exact at3) r s5
    fillerRun
  refine ⟨s5, ?_, ?_⟩
  · rw [step]
    exact leaf x d s2 fewer found2 t2 _ _ heads2 (by simp [tail]) hit2 (by rw [found2Val]; exact at2)
      (by simpa [tail] using object2) r s5 onRange
  · exact marked_same (marked_fresh_eq (marked_finish2 found2Val found3Val (marked_data_prefix mPrefix) m3 m4 m5)
      (by simp)) (fun j => by simp [tail])

theorem data_restriction_qualified {triples : alloc.vec.Vec rdf.Triple} {kinds : rdf_mapping.Kinds}
    {x : rdf.BlankNode} {d : model.DataProperty} {s : rdf_mapping.State} {fuel : Usize}
    {hpos : List Nat} {head : List (List U8 × Node)} (heads : HeadsAt triples.val s.used.val x hpos head)
    (key : List U8) (keys : head.map (·.1) = [rdfType, owlOnProperty, key, owlOnDataRange])
    (distinct : ∀ P ∈ [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlMinCardinality, owlMaxCardinality,
      owlCardinality], P ≠ key) :
    rdf_mapping.data_restriction triples kinds x d s fuel = rdf_mapping.data_qualified triples kinds x d s fuel := by
  have miss : ∀ P ∈ [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlMinCardinality, owlMaxCardinality,
      owlCardinality], Miss triples x s P := by
    intro P member
    apply miss_of_heads heads P
    rw [keys]
    have key' := distinct P member
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, key', ?_⟩ <;>
    · simp at member
      rcases member with h | h | h | h | h | h <;> subst h <;>
        simp [rdfType, owlOnProperty, owlOnDataRange, owlSomeValuesFrom, owlAllValuesFrom, owlHasValue,
          owlMinCardinality, owlMaxCardinality, owlCardinality]
  rw [data_restriction_cardinality triples kinds x d s fuel (miss _ (by simp)) (miss _ (by simp)) (miss _ (by simp)),
    data_cardinality_qualified triples kinds x d s fuel (miss _ (by simp)) (miss _ (by simp)) (miss _ (by simp))]

theorem class_data_min_qualified_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (n : probes.Natural) (d : model.DataProperty) (r : model.DataRange) (x : rdf.BlankNode) (s s1 : Supply)
    (m rn : Node) (p : List Pattern) (natural : NaturalNode n m) (small : CardinalityReadable n)
    (inner : TDR r s rn p s1) (reads : RangeReads triples kinds r s rn p s1)
    (dataTyped : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data)) :
    ClassReads triples kinds (.DataMinCardinality n d (some r)) (x :: s) (.blank x)
      (restrictionHead x (iriNode d.iri) ++ ⟨.blank x, owlMinQualifiedCardinality, m⟩ ::
        ⟨.blank x, owlOnDataRange, rn⟩ :: p) s1 :=
  data_qualified_reads triples kinds owlMinQualifiedCardinality m (fun d r => .DataMinCardinality n d (some r))
    (by simp [rdfType, owlOnProperty, owlMinQualifiedCardinality, owlOnDataRange])
    (fun x d s fuel found t _ _ heads keys hit at_t view r s' onRange => by
      rw [data_restriction_qualified heads _ keys (by
        simp [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlMinCardinality, owlMaxCardinality, owlCardinality,
          owlMinQualifiedCardinality])]
      exact data_qualified_min triples kinds x d s fuel found t hit at_t n
        (natural_complete t.object n (by rw [view]; exact natural) small) r s' onRange)
    d r x s s1 rn p inner reads dataTyped

theorem class_data_max_qualified_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (n : probes.Natural) (d : model.DataProperty) (r : model.DataRange) (x : rdf.BlankNode) (s s1 : Supply)
    (m rn : Node) (p : List Pattern) (natural : NaturalNode n m) (small : CardinalityReadable n)
    (inner : TDR r s rn p s1) (reads : RangeReads triples kinds r s rn p s1)
    (dataTyped : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data)) :
    ClassReads triples kinds (.DataMaxCardinality n d (some r)) (x :: s) (.blank x)
      (restrictionHead x (iriNode d.iri) ++ ⟨.blank x, owlMaxQualifiedCardinality, m⟩ ::
        ⟨.blank x, owlOnDataRange, rn⟩ :: p) s1 :=
  data_qualified_reads triples kinds owlMaxQualifiedCardinality m (fun d r => .DataMaxCardinality n d (some r))
    (by simp [rdfType, owlOnProperty, owlMaxQualifiedCardinality, owlOnDataRange])
    (fun x d s fuel found t _ _ heads keys hit at_t view r s' onRange => by
      rw [data_restriction_qualified heads _ keys (by
        simp [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlMinCardinality, owlMaxCardinality, owlCardinality,
          owlMaxQualifiedCardinality])]
      exact data_qualified_max triples kinds x d s fuel found t
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlMinQualifiedCardinality,
          owlMaxQualifiedCardinality, owlOnDataRange]))
        hit at_t n (natural_complete t.object n (by rw [view]; exact natural) small) r s' onRange)
    d r x s s1 rn p inner reads dataTyped

theorem class_data_exact_qualified_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (n : probes.Natural) (d : model.DataProperty) (r : model.DataRange) (x : rdf.BlankNode) (s s1 : Supply)
    (m rn : Node) (p : List Pattern) (natural : NaturalNode n m) (small : CardinalityReadable n)
    (inner : TDR r s rn p s1) (reads : RangeReads triples kinds r s rn p s1)
    (dataTyped : rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data)) :
    ClassReads triples kinds (.DataExactCardinality n d (some r)) (x :: s) (.blank x)
      (restrictionHead x (iriNode d.iri) ++ ⟨.blank x, owlQualifiedCardinality, m⟩ ::
        ⟨.blank x, owlOnDataRange, rn⟩ :: p) s1 :=
  data_qualified_reads triples kinds owlQualifiedCardinality m (fun d r => .DataExactCardinality n d (some r))
    (by simp [rdfType, owlOnProperty, owlQualifiedCardinality, owlOnDataRange])
    (fun x d s fuel found t _ _ heads keys hit at_t view r s' onRange => by
      rw [data_restriction_qualified heads _ keys (by
        simp [owlSomeValuesFrom, owlAllValuesFrom, owlHasValue, owlMinCardinality, owlMaxCardinality, owlCardinality,
          owlQualifiedCardinality])]
      exact data_qualified_exact triples kinds x d s fuel found t
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlMinQualifiedCardinality,
          owlQualifiedCardinality, owlOnDataRange]))
        (miss_of_heads heads _ (by rw [keys]; simp [rdfType, owlOnProperty, owlMaxQualifiedCardinality,
          owlQualifiedCardinality, owlOnDataRange]))
        hit at_t n (natural_complete t.object n (by rw [view]; exact natural) small) r s' onRange)
    d r x s s1 rn p inner reads dataTyped

/-! ### Boolean constructs and enumerations -/

/-- A construct of a blank node typed `owl:Class`: the triple with `key` at the
    second position is found, and the rest of the patterns are read after it. -/
theorem construct_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (key : List U8)
    (keyType : key ≠ rdfType) (c : model.ClassExpression) (x : rdf.BlankNode) (value : Node) (rest : List Pattern)
    (f : List rdf.BlankNode) (sub : BlankSubjects f rest)
    (body : ∀ (s : rdf_mapping.State) (fuel found : Usize) (t : rdf.Triple) (h0 h1 : Nat),
      HeadsAt triples.val s.used.val x [h0, h1] [(rdfType, .iri owlClass), (key, value)] →
      Hit triples x s found key → found.val = h1 → triples.val[found.val]? = some t → objectView t.object = value →
      ∀ (pos2 : List Nat), Ready triples { s with used := s.used.set found true } pos2 rest f →
      rest.length ≤ fuel.val →
      ∃ s', rdf_mapping.class_construct triples kinds x s fuel = .ok (some (c, s')) ∧
        Marked { s with used := s.used.set found true } s' (fun j => j ∈ pos2) f)
    (s : rdf_mapping.State) (pos : List Nat) (fuel : Usize)
    (ready : Ready triples s pos (⟨.blank x, rdfType, .iri owlClass⟩ :: ⟨.blank x, key, value⟩ :: rest) (x :: f))
    (nodup : (x :: f).Nodup) (fuelOk : (rest.length + 2) ≤ fuel.val) :
    ∃ s', rdf_mapping.class_expression triples kinds (.Blank x) s fuel = .ok (some (c, s')) ∧
      Marked s s' (fun j => j ∈ pos) (x :: f) := by
  have ready' : Ready triples s pos (headPatterns x [(rdfType, .iri owlClass), (key, value)] ++ rest) (x :: f) := by
    simpa [headPatterns] using ready
  obtain ⟨h0, h1, pos2, s1, fewer, rfl, len2, fewerIs, m1, step, heads1, unused1⟩ :=
    class_construct_prefix triples kinds x key value rest f sub s pos fuel ready' nodup keyType (by omega)
  have complete1 : SubjectsComplete triples.val s1.subjects.val (alloc.vec.Vec.len s1.subjects)
      triples.val.length := by rw [m1.subjects]; exact ready.complete
  obtain ⟨found, foundVal, hit⟩ := find_hit triples s1 x complete1 heads1 (k := 1) rfl key (fun _ => rfl) unused1
  obtain ⟨_, t, at_t, -, -, object⟩ := heads_at_triple heads1 (k := 1) rfl
  have m2 := marked_nil_take s1 found
  have ready2 := ready_middle (pos1 := [h0, h1]) (pos3 := []) (ps3 := []) (f3 := [])
    (ps1 := headPatterns x [(rdfType, .iri owlClass), (key, value)]) (f1 := [x]) (by simpa using ready') rfl len2
    (by simpa using nodup) (blank_subjects_head x _) (fun _ m => by simp at m) (marked_trans m1 m2)
    (fun j hj => by
      simp only [List.mem_singleton] at hj
      rcases hj with h | h
      · simp [h]
      · simp [h, foundVal]) (by simp)
  obtain ⟨s', run, m3⟩ := body s1 fewer found t h0 h1 heads1 hit foundVal (by rw [foundVal]; exact at_t)
    (by simpa using object) pos2 ready2 (by omega)
  refine ⟨s', by rw [step, run], ?_⟩
  refine marked_same (marked_fresh_eq (marked_trans (marked_trans m1 m2) m3) (by simp)) (fun j => ?_)
  simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, false_or, foundVal,
    or_assoc]

theorem class_list_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (key : List U8)
    (keyType : key ≠ rdfType) (construct : model.AtLeastTwo model.ClassExpression → model.ClassExpression)
    (leaf : ∀ (s : rdf_mapping.State) (fuel found : Usize) (t : rdf.Triple) (x : rdf.BlankNode) (h0 h1 : Nat)
      (value : Node), HeadsAt triples.val s.used.val x [h0, h1] [(rdfType, .iri owlClass), (key, value)] →
      Hit triples x s found key → triples.val[found.val]? = some t →
      ∀ (xs : model.AtLeastTwo model.ClassExpression) (s' : rdf_mapping.State),
      rdf_mapping.class_list2 triples kinds t.object { s with used := s.used.set found true } fuel = .ok (some (xs, s')) →
      rdf_mapping.class_construct triples kinds x s fuel = .ok (some (construct xs, s')))
    (xs : model.AtLeastTwo model.ClassExpression) (x : rdf.BlankNode) (cells : List rdf.BlankNode) (s s' : Supply)
    (nodes : List Node) (ps : List Pattern) (cellsLen : cells.length = (members2 xs).length)
    (members : ClassesRead triples kinds (members2 xs) s nodes ps s') :
    ClassReads triples kinds (construct xs) (x :: (cells ++ s)) (.blank x)
      (⟨.blank x, rdfType, .iri owlClass⟩ :: ⟨.blank x, key, (listOf cells nodes).1⟩ ::
        ((listOf cells nodes).2 ++ ps)) s' := by
  intro fresh split nodup st pos node fuel view ready fuelOk
  obtain ⟨f, eqf, subf⟩ := classes_read_fresh members
  have freshIs : fresh = x :: (cells ++ f) := by
    rw [eqf] at split
    have h : (x :: (cells ++ f)) ++ s' = fresh ++ s' := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  have nodeIs := node_blank view
  subst nodeIs
  simp only [List.length_cons] at fuelOk
  exact construct_reads triples kinds key keyType (construct xs) x (listOf cells nodes).1
    ((listOf cells nodes).2 ++ ps) (cells ++ f) (blank_subjects_of (subjects_pair (list_of_subjects cells nodes) subf))
    (fun st' fuel found t h0 h1 heads hit foundVal at_t view pos2 ready2 fuelOk2 => by
      obtain ⟨s'', listRun, marked⟩ := class_list2_complete triples kinds xs cells nodes ps s s' cellsLen members f eqf
        (List.nodup_cons.mp nodup).2 _ pos2 t.object fuel view ready2 fuelOk2
      exact ⟨s'', leaf st' fuel found t x h0 h1 _ heads hit at_t xs s'' listRun, marked⟩)
    st pos fuel ready nodup fuelOk

theorem class_intersection_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (xs : model.AtLeastTwo model.ClassExpression) (x : rdf.BlankNode) (cells : List rdf.BlankNode) (s s' : Supply)
    (nodes : List Node) (ps : List Pattern) (cellsLen : cells.length = (members2 xs).length)
    (members : ClassesRead triples kinds (members2 xs) s nodes ps s') :
    ClassReads triples kinds (.ObjectIntersectionOf xs) (x :: (cells ++ s)) (.blank x)
      (⟨.blank x, rdfType, .iri owlClass⟩ :: ⟨.blank x, owlIntersectionOf, (listOf cells nodes).1⟩ ::
        ((listOf cells nodes).2 ++ ps)) s' :=
  class_list_reads triples kinds owlIntersectionOf (by simp [owlIntersectionOf, rdfType]) .ObjectIntersectionOf
    (fun s fuel found t x _ _ _ _ hit at_t xs s' run =>
      class_construct_intersection triples kinds x s fuel found t hit at_t xs s' run)
    xs x cells s s' nodes ps cellsLen members

theorem class_union_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (xs : model.AtLeastTwo model.ClassExpression) (x : rdf.BlankNode) (cells : List rdf.BlankNode) (s s' : Supply)
    (nodes : List Node) (ps : List Pattern) (cellsLen : cells.length = (members2 xs).length)
    (members : ClassesRead triples kinds (members2 xs) s nodes ps s') :
    ClassReads triples kinds (.ObjectUnionOf xs) (x :: (cells ++ s)) (.blank x)
      (⟨.blank x, rdfType, .iri owlClass⟩ :: ⟨.blank x, owlUnionOf, (listOf cells nodes).1⟩ ::
        ((listOf cells nodes).2 ++ ps)) s' :=
  class_list_reads triples kinds owlUnionOf (by simp [owlUnionOf, rdfType]) .ObjectUnionOf
    (fun s fuel found t x _ _ _ heads hit at_t xs s' run =>
      class_construct_union triples kinds x s fuel found t
        (miss_of_heads heads _ (by simp [rdfType, owlIntersectionOf, owlUnionOf])) hit at_t xs s' run)
    xs x cells s s' nodes ps cellsLen members

theorem class_complement_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (c : model.ClassExpression) (x : rdf.BlankNode) (s s' : Supply) (n : Node) (ps : List Pattern)
    (inner : TCE c s n ps s') (reads : ClassReads triples kinds c s n ps s') :
    ClassReads triples kinds (.ObjectComplementOf c) (x :: s) (.blank x)
      (⟨.blank x, rdfType, .iri owlClass⟩ :: ⟨.blank x, owlComplementOf, n⟩ :: ps) s' := by
  intro fresh split nodup st pos node fuel view ready fuelOk
  obtain ⟨f, eqf, subf⟩ := tce_fresh inner
  have freshIs : fresh = x :: f := by
    rw [eqf] at split
    have h : (x :: f) ++ s' = fresh ++ s' := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  have nodeIs := node_blank view
  subst nodeIs
  simp only [List.length_cons] at fuelOk
  exact construct_reads triples kinds owlComplementOf (by simp [owlComplementOf, rdfType]) (.ObjectComplementOf c) x n
    ps f (blank_subjects_of subf)
    (fun st' fuel found t h0 h1 heads hit foundVal at_t view pos2 ready2 fuelOk2 => by
      obtain ⟨s'', run, marked⟩ := reads f eqf (List.nodup_cons.mp nodup).2 _ pos2 t.object fuel view ready2 fuelOk2
      exact ⟨s'', class_construct_complement triples kinds x st' fuel found t
        (miss_of_heads heads _ (by simp [rdfType, owlIntersectionOf, owlComplementOf]))
        (miss_of_heads heads _ (by simp [rdfType, owlUnionOf, owlComplementOf])) hit at_t c s'' run, marked⟩)
    st pos fuel ready nodup fuelOk

theorem class_one_of_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (xs : model.NonEmpty model.Individual) (x : rdf.BlankNode) (cells : List rdf.BlankNode) (s : Supply)
    (cellsLen : cells.length = (members1 xs).length) :
    ClassReads triples kinds (.ObjectOneOf xs) (x :: (cells ++ s)) (.blank x)
      (⟨.blank x, rdfType, .iri owlClass⟩ ::
        ⟨.blank x, owlOneOf, (listOf cells ((members1 xs).map individualNode)).1⟩ ::
        (listOf cells ((members1 xs).map individualNode)).2) s := by
  intro fresh split nodup st pos node fuel view ready fuelOk
  have freshIs : fresh = x :: cells := by
    have h : (x :: cells) ++ s = fresh ++ s := by simpa using split
    exact (List.append_cancel_right h).symm
  subst freshIs
  have nodeIs := node_blank view
  subst nodeIs
  have lists := list_of_length cells ((members1 xs).map individualNode) (by rw [cellsLen, List.length_map])
  simp only [List.length_cons] at fuelOk
  exact construct_reads triples kinds owlOneOf (by simp [owlOneOf, rdfType]) (.ObjectOneOf xs) x
    (listOf cells ((members1 xs).map individualNode)).1 (listOf cells ((members1 xs).map individualNode)).2 cells
    (blank_subjects_of (list_of_subjects cells _))
    (fun st' fuel found t h0 h1 heads hit foundVal at_t view pos2 ready2 fuelOk2 => by
      obtain ⟨s'', run, marked⟩ := individual_list1_complete triples xs cells cellsLen (List.nodup_cons.mp nodup).2 _
        pos2 t.object fuel view ready2 (by rw [lists] at fuelOk2; omega)
      exact ⟨s'', class_construct_one_of triples kinds x st' fuel found t
        (miss_of_heads heads _ (by simp [rdfType, owlIntersectionOf, owlOneOf]))
        (miss_of_heads heads _ (by simp [rdfType, owlUnionOf, owlOneOf]))
        (miss_of_heads heads _ (by simp [rdfType, owlComplementOf, owlOneOf])) hit at_t xs s'' run, marked⟩)
    st pos fuel ready nodup fuelOk

theorem class_named_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) (c : model.Class)
    (s : Supply) : ClassReads triples kinds (.Class c) s (iriNode c.iri) [] s := by
  intro fresh split _ st pos node fuel view ready _
  have empty : fresh = [] := by simpa using split
  subst empty
  have noPos : pos = [] := by have := at_length ready.holds; simpa using this
  subst noPos
  cases node with
  | Iri r =>
    have same : r.spelling.val = c.iri.spelling.val := by simpa [objectView, iriNode] using view
    refine ⟨st, ?_, ready_nil_marked st⟩
    rw [rdf_mapping.class_expression]
    simp only [iri_of_identity, bind_ok]
    have named : ({ iri := { spelling := r.spelling } } : model.Class) = c := by
      obtain ⟨⟨sp⟩⟩ := c
      simp only at same ⊢
      rw [vec_eq_of_val same]
    rw [named]
  | Blank _ => simp [objectView, iriNode] at view
  | Literal _ => simp [objectView, iriNode] at view

/-! ### Every readable class expression is read back -/

theorem role_typed {kinds : rdf_mapping.Kinds} {role : model.ObjectPropertyExpression}
    (h : UsesTyped kinds (Rowl.Collection.objectUses role)) :
    ∀ q, role = .Property q → rdf_mapping.property_kind kinds q.iri.spelling = .ok (some .Object) := by
  intro q eq
  subst eq
  exact (h (q.iri, .ObjectProperty) (by simp [Rowl.Collection.objectUses])).1 rfl

theorem data_typed {kinds : rdf_mapping.Kinds} {d : model.DataProperty}
    (h : UsesTyped kinds (Rowl.Collection.dataUses d)) :
    rdf_mapping.property_kind kinds d.iri.spelling = .ok (some .Data) :=
  (h (d.iri, .DataProperty) (by simp [Rowl.Collection.dataUses])).2 rfl

theorem members_typed {kinds : rdf_mapping.Kinds} {xs : model.AtLeastTwo model.ClassExpression}
    (h : UsesTyped kinds (Rowl.Collection.classUses xs.first ++ Rowl.Collection.classUses xs.second ++
      xs.rest.val.attach.flatMap (fun e => Rowl.Collection.classUses e.val))) :
    ∀ c ∈ members2 xs, UsesTyped kinds (Rowl.Collection.classUses c) := by
  intro c member row rowMember
  apply h row
  simp only [members2, List.mem_cons] at member
  rcases member with rfl | rfl | inRest
  · exact List.mem_append_left _ (List.mem_append_left _ rowMember)
  · exact List.mem_append_left _ (List.mem_append_right _ rowMember)
  · apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨⟨c, inRest⟩, List.mem_attach _ _, rowMember⟩

mutual
/-- Every readable class expression whose properties the reader classifies is
    read back from its forward image. -/
theorem class_reads (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) :
    ∀ {c : model.ClassExpression} {s0 : Supply} {n : Node} {ps : List Pattern} {s1 : Supply},
      TCE c s0 n ps s1 → ClassReadable c → UsesTyped kinds (Rowl.Collection.classUses c) →
      ClassReads triples kinds c s0 n ps s1
  | _, _, _, _, _, .named c s, _, _ => class_named_reads triples kinds c s
  | _, _, _, _, _, .intersection xs x cells s s' nodes ps cellsLen inner, readable, typed => by
    cases readable with
    | intersection _ members =>
      rw [Rowl.Collection.classUses] at typed
      exact class_intersection_reads triples kinds xs x cells s s' nodes ps cellsLen
        (classes_read triples kinds inner members (members_typed typed))
  | _, _, _, _, _, .union xs x cells s s' nodes ps cellsLen inner, readable, typed => by
    cases readable with
    | union _ members =>
      rw [Rowl.Collection.classUses] at typed
      exact class_union_reads triples kinds xs x cells s s' nodes ps cellsLen
        (classes_read triples kinds inner members (members_typed typed))
  | _, _, _, _, _, .complement c x s s' node ps inner, readable, typed => by
    cases readable with
    | complement _ innerReadable =>
      rw [Rowl.Collection.classUses] at typed
      exact class_complement_reads triples kinds c x s s' node ps inner
        (class_reads triples kinds inner innerReadable typed)
  | _, _, _, _, _, .oneOf xs x cells s cellsLen, _, _ => class_one_of_reads triples kinds xs x cells s cellsLen
  | _, _, _, _, _, .some role c x s s1 s2 n1 n2 p1 p2 tope inner, readable, typed => by
    cases readable with
    | some _ _ innerReadable =>
      rw [Rowl.Collection.classUses] at typed
      obtain ⟨roleUses, cUses⟩ := uses_typed_append.mp typed
      exact class_some_reads triples kinds role c x s s1 s2 n1 n2 p1 p2 tope inner
        (class_reads triples kinds inner innerReadable cUses) (role_typed roleUses)
  | _, _, _, _, _, .all role c x s s1 s2 n1 n2 p1 p2 tope inner, readable, typed => by
    cases readable with
    | all _ _ innerReadable =>
      rw [Rowl.Collection.classUses] at typed
      obtain ⟨roleUses, cUses⟩ := uses_typed_append.mp typed
      exact class_all_reads triples kinds role c x s s1 s2 n1 n2 p1 p2 tope inner
        (class_reads triples kinds inner innerReadable cUses) (role_typed roleUses)
  | _, _, _, _, _, .hasValue role a x s s1 n1 p1 tope, _, typed => by
    rw [Rowl.Collection.classUses] at typed
    exact class_has_value_reads triples kinds role a x s s1 n1 p1 tope (role_typed (uses_typed_append.mp typed).1)
  | _, _, _, _, _, .hasSelf role x s s1 n1 p1 tope, _, typed => by
    rw [Rowl.Collection.classUses] at typed
    exact class_has_self_reads triples kinds role x s s1 n1 p1 tope (role_typed typed)
  | _, _, _, _, _, .min n role x s s1 n1 m p1 tope natural, readable, typed => by
    cases readable with
    | min _ _ small =>
      rw [Rowl.Collection.classUses] at typed
      exact class_min_reads triples kinds n role x s s1 n1 m p1 tope natural small
        (role_typed (uses_typed_append.mp typed).1)
  | _, _, _, _, _, .max n role x s s1 n1 m p1 tope natural, readable, typed => by
    cases readable with
    | max _ _ small =>
      rw [Rowl.Collection.classUses] at typed
      exact class_max_reads triples kinds n role x s s1 n1 m p1 tope natural small
        (role_typed (uses_typed_append.mp typed).1)
  | _, _, _, _, _, .exact n role x s s1 n1 m p1 tope natural, readable, typed => by
    cases readable with
    | exact _ _ small =>
      rw [Rowl.Collection.classUses] at typed
      exact class_exact_reads triples kinds n role x s s1 n1 m p1 tope natural small
        (role_typed (uses_typed_append.mp typed).1)
  | _, _, _, _, _, .minQualified n role c x s s1 s2 n1 n2 m p1 p2 tope natural inner, readable, typed => by
    cases readable with
    | minQualified _ _ _ small innerReadable =>
      rw [Rowl.Collection.classUses] at typed
      obtain ⟨roleUses, cUses⟩ := uses_typed_append.mp typed
      exact class_min_qualified_reads triples kinds n role c x s s1 s2 n1 n2 m p1 p2 tope natural small inner
        (class_reads triples kinds inner innerReadable cUses) (role_typed roleUses)
  | _, _, _, _, _, .maxQualified n role c x s s1 s2 n1 n2 m p1 p2 tope natural inner, readable, typed => by
    cases readable with
    | maxQualified _ _ _ small innerReadable =>
      rw [Rowl.Collection.classUses] at typed
      obtain ⟨roleUses, cUses⟩ := uses_typed_append.mp typed
      exact class_max_qualified_reads triples kinds n role c x s s1 s2 n1 n2 m p1 p2 tope natural small inner
        (class_reads triples kinds inner innerReadable cUses) (role_typed roleUses)
  | _, _, _, _, _, .exactQualified n role c x s s1 s2 n1 n2 m p1 p2 tope natural inner, readable, typed => by
    cases readable with
    | exactQualified _ _ _ small innerReadable =>
      rw [Rowl.Collection.classUses] at typed
      obtain ⟨roleUses, cUses⟩ := uses_typed_append.mp typed
      exact class_exact_qualified_reads triples kinds n role c x s s1 s2 n1 n2 m p1 p2 tope natural small inner
        (class_reads triples kinds inner innerReadable cUses) (role_typed roleUses)
  | _, _, _, _, _, .dataSome d r x s s1 n p inner, readable, typed => by
    cases readable with
    | dataSome _ _ rangeReadable =>
      rw [Rowl.Collection.classUses] at typed
      exact class_data_some_reads triples kinds d r x s s1 n p inner (range_reads triples kinds inner rangeReadable)
        (data_typed (uses_typed_append.mp typed).1)
  | _, _, _, _, _, .dataAll d r x s s1 n p inner, readable, typed => by
    cases readable with
    | dataAll _ _ rangeReadable =>
      rw [Rowl.Collection.classUses] at typed
      exact class_data_all_reads triples kinds d r x s s1 n p inner (range_reads triples kinds inner rangeReadable)
        (data_typed (uses_typed_append.mp typed).1)
  | _, _, _, _, _, .dataHasValue d v x s n literal, readable, typed => by
    cases readable with
    | dataHasValue _ _ literalReadable =>
      rw [Rowl.Collection.classUses] at typed
      exact class_data_has_value_reads triples kinds d v x s n literal literalReadable
        (data_typed (uses_typed_append.mp typed).1)
  | _, _, _, _, _, .dataMin n d x s m natural, readable, typed => by
    cases readable with
    | dataMin _ _ small =>
      rw [Rowl.Collection.classUses] at typed
      exact class_data_min_reads triples kinds n d x s m natural small (data_typed (uses_typed_append.mp typed).1)
  | _, _, _, _, _, .dataMax n d x s m natural, readable, typed => by
    cases readable with
    | dataMax _ _ small =>
      rw [Rowl.Collection.classUses] at typed
      exact class_data_max_reads triples kinds n d x s m natural small (data_typed (uses_typed_append.mp typed).1)
  | _, _, _, _, _, .dataExact n d x s m natural, readable, typed => by
    cases readable with
    | dataExact _ _ small =>
      rw [Rowl.Collection.classUses] at typed
      exact class_data_exact_reads triples kinds n d x s m natural small (data_typed (uses_typed_append.mp typed).1)
  | _, _, _, _, _, .dataMinQualified n d r x s s1 m rn p natural inner, readable, typed => by
    cases readable with
    | dataMinQualified _ _ _ small rangeReadable =>
      rw [Rowl.Collection.classUses] at typed
      exact class_data_min_qualified_reads triples kinds n d r x s s1 m rn p natural small inner
        (range_reads triples kinds inner rangeReadable) (data_typed (uses_typed_append.mp typed).1)
  | _, _, _, _, _, .dataMaxQualified n d r x s s1 m rn p natural inner, readable, typed => by
    cases readable with
    | dataMaxQualified _ _ _ small rangeReadable =>
      rw [Rowl.Collection.classUses] at typed
      exact class_data_max_qualified_reads triples kinds n d r x s s1 m rn p natural small inner
        (range_reads triples kinds inner rangeReadable) (data_typed (uses_typed_append.mp typed).1)
  | _, _, _, _, _, .dataExactQualified n d r x s s1 m rn p natural inner, readable, typed => by
    cases readable with
    | dataExactQualified _ _ _ small rangeReadable =>
      rw [Rowl.Collection.classUses] at typed
      exact class_data_exact_qualified_reads triples kinds n d r x s s1 m rn p natural small inner
        (range_reads triples kinds inner rangeReadable) (data_typed (uses_typed_append.mp typed).1)

/-- Readable class expressions in order are each read back. -/
theorem classes_read (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds) :
    ∀ {cs : List model.ClassExpression} {s0 : Supply} {ns : List Node} {ps : List Pattern} {s1 : Supply},
      TCEs cs s0 ns ps s1 → ClassesReadable cs → (∀ c ∈ cs, UsesTyped kinds (Rowl.Collection.classUses c)) →
      ClassesRead triples kinds cs s0 ns ps s1
  | _, _, _, _, _, .nil s, _, _ => .nil s
  | _, _, _, _, _, .cons c cs s s1 s2 n ns ps qs head tail, readable, typed => by
    cases readable with
    | cons _ _ headReadable tailReadable =>
      exact .cons c cs s s1 s2 n ns ps qs head (class_reads triples kinds head headReadable (typed c (by simp)))
        (classes_read triples kinds tail tailReadable (fun d m => typed d (List.mem_cons_of_mem _ m)))
end

/-! ### Lists of properties -/

theorem topes_fresh {es : List model.ObjectPropertyExpression} {s : Supply} {ns : List Node} {ps : List Pattern}
    {s' : Supply} (h : TOPEs es s ns ps s') : ∃ fresh, s = fresh ++ s' ∧ SubjectsIn fresh ps := by
  induction h with
  | nil s => exact ⟨[], by simp, subjects_in_nil _⟩
  | cons e es s s1 s2 n ns ps qs head _ ih =>
    obtain ⟨f1, eq1, sub1⟩ := tope_fresh head
    obtain ⟨f2, eq2, sub2⟩ := ih
    exact ⟨f1 ++ f2, by rw [eq1, eq2, List.append_assoc], subjects_pair sub1 sub2⟩

theorem topes_cons_inv {e : model.ObjectPropertyExpression} {es : List model.ObjectPropertyExpression}
    {s0 s1 : Supply} {ns : List Node} {ps : List Pattern} (h : TOPEs (e :: es) s0 ns ps s1) :
    ∃ (sMid : Supply) (n : Node) (ns' : List Node) (p q : List Pattern), ns = n :: ns' ∧ ps = p ++ q ∧
      TOPE e s0 n p sMid ∧ TOPEs es sMid ns' q s1 := by
  cases h with
  | cons _ _ _ sMid _ n ns' p q head tail => exact ⟨sMid, n, ns', p, q, rfl, rfl, head, tail⟩

/-- The object property expression of the element `firsts[index]`. -/
theorem property_element_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (firsts : alloc.vec.Vec Usize) (index : Usize) {e : model.ObjectPropertyExpression} {s0 s1 : Supply}
    {n : Node} {ps : List Pattern} (tope : TOPE e s0 n ps s1)
    (typed : UsesTyped kinds (Rowl.Collection.objectUses e)) {fresh : Supply} (split : s0 = fresh ++ s1)
    {ns : List Node} (elements : Elements triples.val (firsts.val.drop index.val) (n :: ns))
    (s : rdf_mapping.State) (pos : List Nat) (ready : Ready triples s pos ps fresh) :
    ∃ s', rdf_mapping.property_element triples kinds firsts index s = .ok (some (e, s')) ∧
      Marked s s' (fun i => i ∈ pos) fresh := by
  obtain ⟨inside, t, at_t, view, -⟩ := elements_drop_cons elements
  obtain ⟨s', run, marked⟩ := role_complete triples tope split view ready
  refine ⟨s', ?_, marked⟩
  rw [rdf_mapping.property_element]
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
    firsts_lookup firsts index inside, bind_ok, element_at triples _ t at_t,
    node_kind_object kinds tope t.object view (role_typed typed), run]

/-- The object property expressions of the elements from `firsts[index]` on. -/
theorem property_members_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (firsts : alloc.vec.Vec Usize) :
    ∀ {es : List model.ObjectPropertyExpression} {s0 s1 : Supply} {ns : List Node} {ps : List Pattern},
      TOPEs es s0 ns ps s1 → (∀ e ∈ es, UsesTyped kinds (Rowl.Collection.objectUses e)) →
      ∀ (fresh : Supply), s0 = fresh ++ s1 → fresh.Nodup →
      ∀ (index : Usize) (s : rdf_mapping.State) (pos : List Nat)
        (out : alloc.vec.Vec model.ObjectPropertyExpression),
        Elements triples.val (firsts.val.drop index.val) ns → Ready triples s pos ps fresh →
        out.val.length + es.length ≤ Usize.max →
        ∃ v s', rdf_mapping.property_members triples kinds firsts index s out = .ok (some (v, s')) ∧
          v.val = out.val ++ es ∧ Marked s s' (fun i => i ∈ pos) fresh := by
  intro es s0 s1 ns ps h
  induction h with
  | nil s =>
    intro _ fresh split _ index st pos out elements ready _
    have empty : fresh = [] := by simpa using split
    subst empty
    have noPos : pos = [] := by have := at_length ready.holds; simpa using this
    subst noPos
    have done := elements_drop_nil elements
    refine ⟨out, st, ?_, by simp, ready_nil_marked st⟩
    rw [rdf_mapping.property_members]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, show ¬ index.val < firsts.val.length by omega]
  | cons e es s s1 s2 n ns ps qs head tail ih =>
    intro typed fresh split nodup index st pos out elements ready room
    obtain ⟨f1, eq1, sub1⟩ := tope_fresh head
    obtain ⟨f2, eq2, sub2⟩ := topes_fresh tail
    have freshIs := fresh_split (by rw [← eq1]; exact split) eq2
    subst freshIs
    obtain ⟨pos1, pos2, rfl, at1, at2⟩ := at_split ready.holds
    have nodup2 : f2.Nodup := (List.nodup_append.mp nodup).2.1
    have ready1 := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (by simpa using ready) rfl (at_length at1)
      (by simpa using nodup) (fun _ m => by simp at m) (blank_subjects_of sub2) (marked_refl st) (fun _ h => h.elim)
      (by simp)
    obtain ⟨inside, t, at_t, view, restElements⟩ := elements_drop_cons elements
    obtain ⟨s3, run1, m1⟩ := role_complete triples head eq1 view ready1
    have ready2 := ready_middle (pos3 := []) (ps3 := []) (f3 := []) (by simpa using ready) (at_length at1)
      (at_length at2) (by simpa using nodup) (blank_subjects_of sub1) (fun _ m => by simp at m) m1
      (fun _ h => h) (le_refl _)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := firsts.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have outRoom : out.val.length < Usize.max := by simp at room; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out e outRoom)
    obtain ⟨v, s4, run2, value, m2⟩ := ih (fun b m => typed b (List.mem_cons_of_mem _ m)) f2 eq2 nodup2 next s3
      pos2 pushed (by rw [nextIs]; exact restElements) ready2 (by rw [contents]; simp at room ⊢; omega)
    refine ⟨v, s4, ?_, by rw [value, contents]; simp, ?_⟩
    · rw [rdf_mapping.property_members]
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        firsts_lookup firsts index inside, bind_ok, element_at triples _ t at_t,
        node_kind_object kinds head t.object view (role_typed (typed e (by simp))), run1, uncurry_apply_pair,
        usize_max_val, outRoom, push, advance, run2]
    · refine marked_same (marked_trans m1 m2) (fun j => ?_)
      simp only [List.mem_append]

/-- The object property expressions of a list of at least two read back from its
    forward image. -/
theorem property_list2_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (xs : model.AtLeastTwo model.ObjectPropertyExpression) (cells : List rdf.BlankNode) (nodes : List Node)
    (ps : List Pattern) (s0 s1 : Supply) (cellsLen : cells.length = (members2 xs).length)
    (members : TOPEs (members2 xs) s0 nodes ps s1)
    (typed : ∀ e ∈ members2 xs, UsesTyped kinds (Rowl.Collection.objectUses e)) (fresh : Supply)
    (split : s0 = fresh ++ s1) (nodup : (cells ++ fresh).Nodup) (s : rdf_mapping.State) (pos : List Nat)
    (node : rdf.Object) (fuel : Usize) (view : objectView node = (listOf cells nodes).1)
    (ready : Ready triples s pos ((listOf cells nodes).2 ++ ps) (cells ++ fresh))
    (fuelOk : cells.length ≤ fuel.val) :
    ∃ s', rdf_mapping.property_list2 triples kinds node s fuel = .ok (some (xs, s')) ∧
      Marked s s' (fun i => i ∈ pos) (cells ++ fresh) := by
  have nodesLen := topes_length members
  have lists := list_of_length cells nodes (by rw [cellsLen, nodesLen])
  obtain ⟨f, eqf, subf⟩ := topes_fresh members
  have freshIs : fresh = f := by
    rw [eqf] at split
    exact (List.append_cancel_right split).symm
  subst freshIs
  obtain ⟨cpos, mpos, rfl, atC, atM⟩ := at_split ready.holds
  have nodupCells : cells.Nodup := (List.nodup_append.mp nodup).1
  have nodupMembers : fresh.Nodup := (List.nodup_append.mp nodup).2.1
  have readyCells := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (by simpa using ready) rfl (at_length atC)
    (by simpa using nodup) (fun _ m => by simp at m) (blank_subjects_of subf) (marked_refl s) (fun _ h => h.elim)
    (by simp)
  obtain ⟨firsts, news, s2, cellsRun, firstsIs, elementsOk, mCells⟩ := cells_complete triples cells nodes
    (by rw [cellsLen, nodesLen]) nodupCells s cpos node (alloc.vec.Vec.new Usize) fuel view readyCells fuelOk
    (by simp; have := fuel.hBounds; scalar_tac)
  have readyMembers := ready_middle (pos3 := []) (ps3 := []) (f3 := []) (by simpa using ready) (at_length atC)
    (at_length atM) (by simpa using nodup) (blank_subjects_of (list_of_subjects cells nodes))
    (fun _ m => by simp at m) mCells (fun _ h => h) (le_refl _)
  have elements0 := firsts_from_cells firstsIs elementsOk
  obtain ⟨sA, nA, nsA, pA, qA, rfl, rfl, headA, tailA⟩ := topes_cons_inv members
  obtain ⟨sB, nB, nsB, pB, pC, rfl, rfl, headB, tailC⟩ := topes_cons_inv tailA
  obtain ⟨fA, eqA, subA⟩ := tope_fresh headA
  obtain ⟨fB, eqB, subB⟩ := tope_fresh headB
  obtain ⟨fC, eqC, subC⟩ := topes_fresh tailC
  have freshIs : fresh = fA ++ (fB ++ fC) := by
    rw [eqA, eqB, eqC] at eqf
    have h : (fA ++ (fB ++ fC)) ++ s1 = fresh ++ s1 := by simpa using eqf
    exact (List.append_cancel_right h).symm
  subst freshIs
  obtain ⟨posA, posBC, rfl, atA, atBC⟩ := at_split atM
  obtain ⟨posB, posC, rfl, atB, atC'⟩ := at_split atBC
  have nodupAll := nodupMembers
  have readyA := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (pos3 := posB ++ posC) (ps3 := pB ++ pC)
    (f3 := fB ++ fC) (by simpa using readyMembers) rfl (at_length atA) (by simpa using nodupAll)
    (fun _ m => by simp at m) (blank_subjects_of (subjects_pair subB subC)) (marked_refl s2) (fun _ h => h.elim)
    (by simp)
  have typedA := typed xs.first (by simp [members2])
  have typedB := typed xs.second (by simp [members2])
  have typedC : ∀ e ∈ xs.rest.val, UsesTyped kinds (Rowl.Collection.objectUses e) :=
    fun e m => typed e (by simp [members2, m])
  obtain ⟨inside0, t0, at0, view0, rest0⟩ := elements_drop_cons elements0
  obtain ⟨sA', runA, mA⟩ := property_element_complete triples kinds firsts 0#usize headA typedA eqA elements0 s2
    posA readyA
  have readyB := ready_middle (pos1 := posA) (ps1 := pA) (f1 := fA) (pos3 := posC) (ps3 := pC)
    (f3 := fC) (by simpa [List.append_assoc] using readyMembers) (at_length atA) (at_length atB)
    (by simpa [List.append_assoc] using nodupAll) (blank_subjects_of subA) (blank_subjects_of subC) mA
    (fun _ h => h) (le_refl _)
  have one : (1#usize : Usize).val = 0 + 1 := by simp
  have zero : (0#usize : Usize).val = 0 := by simp
  have elements1 : Elements triples.val (firsts.val.drop (1#usize : Usize).val) (nB :: nsB) := by
    rw [one, ← zero]; exact rest0
  obtain ⟨inside1, t1, at1, view1, rest1⟩ := elements_drop_cons elements1
  obtain ⟨sB', runB, mB⟩ := property_element_complete triples kinds firsts 1#usize headB typedB eqB elements1 sA'
    posB readyB
  have mAB := marked_trans mA mB
  have readyC := ready_middle (pos1 := posA ++ posB) (ps1 := pA ++ pB) (f1 := fA ++ fB) (pos3 := [])
    (ps3 := []) (f3 := []) (by simpa [List.append_assoc] using readyMembers)
    (by simp [at_length atA, at_length atB]) (at_length atC')
    (by simpa [List.append_assoc] using nodupAll) (blank_subjects_of (subjects_pair subA subB))
    (fun _ m => by simp at m) mAB (fun j hj => by simp only [List.mem_append]; exact hj) (le_refl _)
  have two : (2#usize : Usize).val = 0 + 1 + 1 := by simp
  obtain ⟨v, sC', runC, value, mC⟩ := property_members_complete triples kinds firsts tailC typedC fC eqC
    (List.nodup_append.mp (List.nodup_append.mp nodupAll).2.1).2.1 2#usize sB' posC
    (alloc.vec.Vec.new model.ObjectPropertyExpression) (by rw [two, ← one]; exact rest1) readyC
    (by rw [new_length]; have := xs.rest.property; omega)
  refine ⟨sC', ?_, ?_⟩
  · rw [rdf_mapping.property_list2]
    simp only [cellsRun, bind_ok, uncurry_apply_pair, runA, runB, runC]
    rw [at_least_two_ext rfl rfl (by rw [value]; simp)]
  · refine marked_same (marked_fresh_eq (marked_trans (marked_trans mCells mAB) mC) (by simp)) (fun j => ?_)
    simp only [List.mem_append, List.append_assoc]
    tauto

/-- The data property of the element `firsts[index]`. -/
theorem data_element_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (firsts : alloc.vec.Vec Usize) (index : Usize) (d : model.DataProperty) {ns : List Node}
    (elements : Elements triples.val (firsts.val.drop index.val) (iriNode d.iri :: ns))
    (typed : UsesTyped kinds (Rowl.Collection.dataUses d)) :
    rdf_mapping.data_element triples kinds firsts index = .ok (some d) := by
  obtain ⟨inside, t, at_t, view, -⟩ := elements_drop_cons elements
  rw [rdf_mapping.data_element]
  simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
    firsts_lookup firsts index inside, bind_ok, element_at triples _ t at_t,
    node_kind_data kinds d t.object view (data_typed typed), node_iri_complete t.object d.iri view]

/-- The data properties of the elements from `firsts[index]` on. -/
theorem data_members_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (firsts : alloc.vec.Vec Usize) :
    ∀ (members : List model.DataProperty) (index : Usize) (out : alloc.vec.Vec model.DataProperty),
      Elements triples.val (firsts.val.drop index.val) (members.map (iriNode ·.iri)) →
      (∀ d ∈ members, UsesTyped kinds (Rowl.Collection.dataUses d)) →
      out.val.length + members.length ≤ Usize.max →
      ∃ v, rdf_mapping.data_members triples kinds firsts index out = .ok (some v) ∧ v.val = out.val ++ members := by
  intro members
  induction members with
  | nil =>
    intro index out elements _ _
    have done := elements_drop_nil elements
    refine ⟨out, ?_, by simp⟩
    rw [rdf_mapping.data_members]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, show ¬ index.val < firsts.val.length by omega]
  | cons d rest ih =>
    intro index out elements typed room
    obtain ⟨inside, t, at_t, view, restElements⟩ := elements_drop_cons elements
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := firsts.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have outRoom : out.val.length < Usize.max := by simp at room; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out ({ iri := d.iri } : model.DataProperty) outRoom)
    obtain ⟨v, run, value⟩ := ih next pushed (by rw [nextIs]; exact restElements)
      (fun b m => typed b (List.mem_cons_of_mem _ m)) (by rw [contents]; simp at room ⊢; omega)
    refine ⟨v, ?_, by rw [value, contents]; simp⟩
    rw [rdf_mapping.data_members]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      firsts_lookup firsts index inside, bind_ok, element_at triples _ t at_t,
      node_kind_data kinds d t.object view (data_typed (typed d (by simp))),
      node_iri_complete t.object d.iri view, usize_max_val, outRoom, push, advance, run]

/-- The data properties of a list of at least two read back from its forward image. -/
theorem data_list2_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (xs : model.AtLeastTwo model.DataProperty) (cells : List rdf.BlankNode)
    (cellsLen : cells.length = (members2 xs).length) (nodup : cells.Nodup)
    (typed : ∀ d ∈ members2 xs, UsesTyped kinds (Rowl.Collection.dataUses d))
    (s : rdf_mapping.State) (pos : List Nat) (node : rdf.Object) (fuel : Usize)
    (view : objectView node = (listOf cells ((members2 xs).map (iriNode ·.iri))).1)
    (ready : Ready triples s pos (listOf cells ((members2 xs).map (iriNode ·.iri))).2 cells)
    (fuelOk : cells.length ≤ fuel.val) :
    ∃ s', rdf_mapping.data_list2 triples kinds node s fuel = .ok (some (xs, s')) ∧
      Marked s s' (fun i => i ∈ pos) cells := by
  have cellsMax : cells.length ≤ Usize.max := by have := fuel.hBounds; scalar_tac
  obtain ⟨firsts, news, s', cellsRun, firstsIs, elementsOk, marked⟩ := cells_complete triples cells
    ((members2 xs).map (iriNode ·.iri)) (by simp [cellsLen]) nodup s pos node (alloc.vec.Vec.new Usize) fuel view
    ready fuelOk (by simp; omega)
  have elements0 := firsts_from_cells firstsIs elementsOk
  simp only [members2, List.map_cons] at elements0
  obtain ⟨inside0, t0, at0, view0, rest0⟩ := elements_drop_cons elements0
  have one : (1#usize : Usize).val = 0 + 1 := by simp
  have zero : (0#usize : Usize).val = 0 := by simp
  have two : (2#usize : Usize).val = 0 + 1 + 1 := by simp
  have elements1 : Elements triples.val (firsts.val.drop (1#usize : Usize).val)
      (iriNode xs.second.iri :: xs.rest.val.map (iriNode ·.iri)) := by
    rw [one, ← zero]; exact rest0
  obtain ⟨inside1, t1, at1, view1, rest1⟩ := elements_drop_cons elements1
  obtain ⟨v, membersRun, value⟩ := data_members_complete triples kinds firsts xs.rest.val 2#usize
    (alloc.vec.Vec.new model.DataProperty) (by rw [two, ← one]; exact rest1)
    (fun d m => typed d (by simp [members2, m])) (by have h := xs.rest.property; rw [new_length]; omega)
  refine ⟨s', ?_, marked⟩
  rw [rdf_mapping.data_list2]
  simp only [cellsRun, bind_ok, uncurry_apply_pair,
    data_element_complete triples kinds firsts 0#usize xs.first elements0 (typed xs.first (by simp [members2])),
    data_element_complete triples kinds firsts 1#usize xs.second elements1 (typed xs.second (by simp [members2])),
    membersRun]
  rw [at_least_two_ext rfl rfl (by rw [value]; simp)]

/-! ### The properties of keys -/

theorem new_len (T : Type) : alloc.vec.Vec.len (alloc.vec.Vec.new T) = 0#usize := by
  apply UScalar.eq_of_val_eq
  simp

/-- The data properties of a key from `firsts[index]` on, after its object
    property expressions. -/
theorem key_datas_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (firsts : alloc.vec.Vec Usize) (s : rdf_mapping.State) (objects : alloc.vec.Vec model.ObjectPropertyExpression) :
    ∀ (datas : List model.DataProperty) (index : Usize) (out : alloc.vec.Vec model.DataProperty),
      Elements triples.val (firsts.val.drop index.val) (datas.map (iriNode ·.iri)) →
      (∀ d ∈ datas, UsesTyped kinds (Rowl.Collection.dataUses d)) → out.val.length + datas.length ≤ Usize.max →
      ∃ v, rdf_mapping.key_members triples kinds firsts index s objects out = .ok (some (objects, v, s)) ∧
        v.val = out.val ++ datas := by
  intro datas
  induction datas with
  | nil =>
    intro index out elements _ _
    have done := elements_drop_nil elements
    refine ⟨out, ?_, by simp⟩
    rw [rdf_mapping.key_members]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, show ¬ index.val < firsts.val.length by omega]
  | cons d rest ih =>
    intro index out elements typed room
    obtain ⟨inside, t, at_t, view, restElements⟩ := elements_drop_cons elements
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := firsts.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have outRoom : out.val.length < Usize.max := by simp at room; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out ({ iri := d.iri } : model.DataProperty) outRoom)
    obtain ⟨v, run, value⟩ := ih next pushed (by rw [nextIs]; exact restElements)
      (fun b m => typed b (List.mem_cons_of_mem _ m)) (by rw [contents]; simp at room ⊢; omega)
    refine ⟨v, ?_, by rw [value, contents]; simp⟩
    rw [rdf_mapping.key_members]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      firsts_lookup firsts index inside, bind_ok, element_at triples _ t at_t,
      node_kind_data kinds d t.object view (data_typed (typed d (by simp))),
      node_iri_complete t.object d.iri view, usize_max_val, outRoom, push, advance, run]

/-- The properties of a key from `firsts[index]` on: its object property
    expressions, then its data properties. -/
theorem key_members_complete (triples : alloc.vec.Vec rdf.Triple) (kinds : rdf_mapping.Kinds)
    (firsts : alloc.vec.Vec Usize) (datas : List model.DataProperty)
    (dataTyped : ∀ d ∈ datas, UsesTyped kinds (Rowl.Collection.dataUses d)) (dataRoom : datas.length ≤ Usize.max) :
    ∀ {es : List model.ObjectPropertyExpression} {s0 s1 : Supply} {ns : List Node} {ps : List Pattern},
      TOPEs es s0 ns ps s1 → (∀ e ∈ es, UsesTyped kinds (Rowl.Collection.objectUses e)) →
      ∀ (fresh : Supply), s0 = fresh ++ s1 → fresh.Nodup →
      ∀ (index : Usize) (s : rdf_mapping.State) (pos : List Nat)
        (objects : alloc.vec.Vec model.ObjectPropertyExpression),
        Elements triples.val (firsts.val.drop index.val) (ns ++ datas.map (iriNode ·.iri)) →
        Ready triples s pos ps fresh → objects.val.length + es.length ≤ Usize.max →
        ∃ vo vd s', rdf_mapping.key_members triples kinds firsts index s objects (alloc.vec.Vec.new _) =
          .ok (some (vo, vd, s')) ∧ vo.val = objects.val ++ es ∧ vd.val = datas ∧
          Marked s s' (fun i => i ∈ pos) fresh := by
  intro es s0 s1 ns ps h
  induction h with
  | nil s =>
    intro _ fresh split _ index st pos objects elements ready _
    have empty : fresh = [] := by simpa using split
    subst empty
    have noPos : pos = [] := by have := at_length ready.holds; simpa using this
    subst noPos
    obtain ⟨v, run, value⟩ := key_datas_complete triples kinds firsts st objects datas index
      (alloc.vec.Vec.new _) (by simpa using elements) dataTyped (by rw [new_length]; omega)
    exact ⟨objects, v, st, run, by simp, by rw [value]; simp, ready_nil_marked st⟩
  | cons e es s s1 s2 n ns ps qs head tail ih =>
    intro typed fresh split nodup index st pos objects elements ready room
    obtain ⟨f1, eq1, sub1⟩ := tope_fresh head
    obtain ⟨f2, eq2, sub2⟩ := topes_fresh tail
    have freshIs := fresh_split (by rw [← eq1]; exact split) eq2
    subst freshIs
    obtain ⟨pos1, pos2, rfl, at1, at2⟩ := at_split ready.holds
    have nodup2 : f2.Nodup := (List.nodup_append.mp nodup).2.1
    have ready1 := ready_middle (pos1 := []) (ps1 := []) (f1 := []) (by simpa using ready) rfl (at_length at1)
      (by simpa using nodup) (fun _ m => by simp at m) (blank_subjects_of sub2) (marked_refl st) (fun _ h => h.elim)
      (by simp)
    obtain ⟨inside, t, at_t, view, restElements⟩ := elements_drop_cons (by simpa using elements)
    obtain ⟨s3, run1, m1⟩ := role_complete triples head eq1 view ready1
    have ready2 := ready_middle (pos3 := []) (ps3 := []) (f3 := []) (by simpa using ready) (at_length at1)
      (at_length at2) (by simpa using nodup) (blank_subjects_of sub1) (fun _ m => by simp at m) m1
      (fun _ h => h) (le_refl _)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by have := firsts.property; scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have outRoom : objects.val.length < Usize.max := by simp at room; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec objects e outRoom)
    obtain ⟨vo, vd, s4, run2, value, datasIs, m2⟩ := ih (fun b m => typed b (List.mem_cons_of_mem _ m)) f2 eq2
      nodup2 next s3 pos2 pushed (by rw [nextIs]; exact restElements) ready2
      (by rw [contents]; simp at room ⊢; omega)
    refine ⟨vo, vd, s4, ?_, by rw [value, contents]; simp, datasIs, ?_⟩
    · rw [rdf_mapping.key_members]
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        firsts_lookup firsts index inside, bind_ok, element_at triples _ t at_t,
        node_kind_object kinds head t.object view (role_typed (typed e (by simp))), new_len, run1,
        uncurry_apply_pair, usize_max_val, outRoom, push, advance, run2]
    · refine marked_same (marked_trans m1 m2) (fun j => ?_)
      simp only [List.mem_append]

end Rowl.RdfReadExpressions
