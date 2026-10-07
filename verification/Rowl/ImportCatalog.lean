import Rowl.Imports
import Rowl.SourceReasoning
import Rowl.NTriples
import Rowl.Turtle
import Rowl.DlValidity

/-!
Import closures, first part: the headers of a catalog of documents and the
catalog of their imports, against OWL 2 Structural Specification §3.2 and §3.4.

The caller supplies every document; nothing is fetched. `read_source` reads a
document with its verified reader: Functional Syntax documents to the raw OWL
ontology of their bytes (`SourceReasoning.SourceOntology`), N-Triples and Turtle
documents to the ontology that the reverse RDF mapping reads from the graph
their bytes denote by the N-Triples and Turtle grammars (`ReadAs`). Their node
IDs and blank nodes become anonymous individuals of a caller scope;
`read_sources` gives each document the scope of its position (`scopeOf`), eight
bytes that differ for different positions (`scope_injective`).

An import IRI names a document when it is the document's ontology IRI or
version IRI (`Names`, §3.2 and §3.4). A document directly imports the documents
its import IRIs name (`DirectlyImports`), and the import closure of a document
is everything it reaches that way (`InClosure`, §3.4). `catalog` builds the
symbol-indexed catalog of `Imports.lean` from the read ontologies: its edges are
exactly the direct imports (`catalog_edges`), so its reachability is exactly the
import closure (`catalog_reachable`). `lookup` tells whether an import IRI names
no document, exactly one or several (`lookup_correct`).

The reverse RDF mapping has no termination proof, so reading N-Triples and
Turtle documents is proved correct whenever it returns; reading Functional
Syntax documents is also proved to return (`read_sources_functional_total`).
-/
namespace Rowl.ImportCatalog
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open RowlRust.import_catalog (Format Source SourceError Unread Lookup)
open Rowl.Imports (rows keys ids Edge Reachable)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

private theorem bind_eq_ok {α β : Type} {x : Result α} {f : α → Result β} {y : β}
    (h : (x >>= f) = Result.ok y) : ∃ a, x = Result.ok a ∧ f a = Result.ok y := by
  cases hx : x.match with
  | ok a =>
    have xa : x = Result.ok a := Result.match.isOk.mp hx
    subst xa
    exact ⟨a, rfl, by simpa using h⟩
  | vis e k =>
    have xv : x = Result.vis e k := Result.match.isVis.mp hx
    subst xv
    have h' : Aeneas.Std.bind (Result.vis e k) f = Result.ok y := h
    rw [bind_vis] at h'
    exact absurd h' vis_not_ok
  | div =>
    have xd : x = Result.div := Result.match.isDiv.mp hx
    subst xd
    have h' : Aeneas.Std.bind Result.div f = Result.ok y := h
    rw [bind_div] at h'
    exact absurd h' div_not_ok

/-! ## Scopes -/

/-- The bytes of a number, least significant first. -/
def scopeBytes (value : Nat) : Nat → List U8
  | 0 => []
  | n + 1 => ⟨BitVec.ofNat 8 (value % 256)⟩ :: scopeBytes (value / 256) n

/-- The scope of the anonymous individuals of the document at a position: the
    eight bytes of the position, least significant first. -/
def scopeOf (index : Nat) : List U8 := scopeBytes index 8

theorem scope_length (index : Nat) : (scopeOf index).length = 8 := by
  have general : ∀ value n, (scopeBytes value n).length = n := by
    intro value n
    induction n generalizing value with
    | zero => rfl
    | succ n ih => simp [scopeBytes, ih]
  exact general index 8

/-- The scope as the kernel's byte vector. -/
def scopeVec (index : Nat) : alloc.vec.Vec U8 :=
  alloc.vec.Vec.from (scopeOf index) (by rw [scope_length]; scalar_tac)

/-- Different positions below `256 ^ 8` have different scopes. -/
theorem scope_injective (a b : Nat) (ha : a < 256 ^ 8) (hb : b < 256 ^ 8)
    (same : scopeOf a = scopeOf b) : a = b := by
  have general : ∀ n a b, a < 256 ^ n → b < 256 ^ n → scopeBytes a n = scopeBytes b n → a = b := by
    intro n
    induction n with
    | zero => intro a b ha hb _; simp at ha hb; omega
    | succ n ih =>
      intro a b ha hb same
      simp only [scopeBytes, List.cons.injEq] at same
      have low : a % 256 = b % 256 := by
        have := congrArg UScalar.val same.1
        simp only [UScalar.val, BitVec.toNat_ofNat, UScalarTy.U8_numBits_eq] at this
        omega
      have high := ih (a / 256) (b / 256) (by rw [pow_succ] at ha; omega) (by rw [pow_succ] at hb; omega)
        same.2
      omega
  exact general 8 a b ha hb same

/-- Every machine position is below `256 ^ 8`. -/
theorem usize_below (x : Usize) : x.val < 256 ^ 8 := by
  have bound := x.hBounds
  have bits : UScalarTy.Usize.numBits ≤ 64 := by
    rw [UScalarTy.Usize_numBits_eq]
    cases System.Platform.numBits_eq <;> simp [*]
  have power : 2 ^ UScalarTy.Usize.numBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) bits
  have : (256 : Nat) ^ 8 = 2 ^ 64 := by norm_num
  rw [this]
  exact lt_of_lt_of_le bound power

private theorem scope_bytes_correct (value count : Usize) (out : alloc.vec.Vec U8) (small : count.val ≤ 8)
    (room : out.val.length + (8 - count.val) ≤ Usize.max) :
    ∃ v, import_catalog.scope_bytes value count out = .ok v ∧
      v.val = out.val ++ scopeBytes value.val (8 - count.val) := by
  rw [import_catalog.scope_bytes]
  by_cases more : count.val < 8
  · have more' : count < 8#usize := by simpa [UScalar.lt_equiv] using more
    obtain ⟨low, lowRun, lowValue⟩ := WP.spec_imp_exists (Usize.rem_spec value (y := 256#usize) (by simp))
    have byteValue : (UScalar.cast .U8 low).val = value.val % 256 := by
      rw [UScalar.cast_val_eq, lowValue]
      simp
    have short : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out (UScalar.cast .U8 low) short)
    obtain ⟨high, highRun, highValue⟩ := WP.spec_imp_exists (Usize.div_spec value (y := 256#usize) (by simp))
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := count) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = count.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value'⟩ := scope_bytes_correct high next pushed (by omega) (by rw [contents]; simp; omega)
    refine ⟨v, by simp [more', lowRun, push, highRun, advance, run], ?_⟩
    rw [value', contents, nextIs, highValue]
    have steps : 8 - count.val = (8 - (count.val + 1)) + 1 := by omega
    rw [steps, scopeBytes]
    have same : (⟨BitVec.ofNat 8 (value.val % 256)⟩ : U8) = UScalar.cast .U8 low := by
      apply UScalar.eq_of_val_eq
      show (BitVec.ofNat 8 (value.val % 256)).toNat = (UScalar.cast .U8 low).val
      rw [BitVec.toNat_ofNat, byteValue]; omega
    simp [same]
  · have eight : count.val = 8 := by omega
    have notMore : ¬ count < 8#usize := by simp [UScalar.lt_equiv]; omega
    refine ⟨out, by simp [notMore], ?_⟩
    simp [eight, scopeBytes]
termination_by 8 - count.val
decreasing_by omega

/-- `document_scope` builds the scope of a position. -/
theorem document_scope_correct (index : Usize) :
    import_catalog.document_scope index = .ok (scopeVec index.val) := by
  obtain ⟨v, run, value⟩ := scope_bytes_correct index 0#usize (alloc.vec.Vec.new U8) (by simp)
    (by simp; scalar_tac)
  rw [import_catalog.document_scope, run]
  congr 1
  apply alloc.vec.Vec.ext
  simp [value, scopeVec, scopeOf]

/-! ## Reading documents -/

/-- A document read by its verified reader, with its node IDs or blank nodes as
    anonymous individuals of `scope`. A Functional Syntax document is read to the
    raw OWL ontology of its bytes: its prefix header and namespace table parsed
    from the bytes, the rest derived by the document grammar, and the model of
    the read document. An N-Triples or Turtle document is read to the ontology
    that the reverse RDF mapping reads from the graph whose triples the bytes
    denote, in order, by the N-Triples or the Turtle grammar (Turtle against the
    base IRI of the format). -/
def ReadAs (limits : functional_document.DocumentLimits) (scope : alloc.vec.Vec U8) (source : Source)
    (o : RawOntology) : Prop :=
  match source.format with
  | .Functional => Rowl.SourceReasoning.SourceOntology source.bytes limits scope o
  | .NTriples => ∃ graph mapped,
      Rowl.NTriples.Document source.bytes.val scope.val source.bytes.val.length source.bytes.val.length
        graph.triples.val ∧
      rdf_mapping.map_graph graph = .ok (some mapped) ∧ mapped.ontology = o
  | .Turtle base => ∃ graph mapped,
      Rowl.Turtle.Document source.bytes.val scope.val base.val Usize.max Usize.max
        (graph.triples.val.map Rowl.Turtle.spo) ∧
      rdf_mapping.map_graph graph = .ok (some mapped) ∧ mapped.ontology = o

/-- Why reading failed: the first error of the reader, or a graph that the
    reverse RDF mapping does not read. A read Functional Syntax document always
    has a model, so `Unmapped` never happens. -/
def RejectedAs (limits : functional_document.DocumentLimits) (scope : alloc.vec.Vec U8) (source : Source) :
    SourceError → Prop
  | .Functional error => source.format = .Functional ∧
      functional_document.read_document source.bytes limits = .ok (.Err error)
  | .Unmapped => False
  | .Triples error => source.format = .NTriples ∧
      Rowl.NTriples.DocumentError source.bytes.val scope.val source.bytes.val.length source.bytes.val.length error
  | .Turtle error => ∃ base, source.format = .Turtle base ∧
      Rowl.Turtle.DocumentError source.bytes.val scope.val base.val Usize.max Usize.max
        (Rowl.TurtleTokens.faultOf error)
  | .Graph =>
      (source.format = .NTriples ∧ ∃ graph,
        Rowl.NTriples.Document source.bytes.val scope.val source.bytes.val.length source.bytes.val.length
          graph.triples.val ∧ rdf_mapping.map_graph graph = .ok none) ∨
      (∃ base, source.format = .Turtle base ∧ ∃ graph,
        Rowl.Turtle.Document source.bytes.val scope.val base.val Usize.max Usize.max
          (graph.triples.val.map Rowl.Turtle.spo) ∧ rdf_mapping.map_graph graph = .ok none)

/-- What `read_source` returns: an ontology read from the bytes, or why not. -/
def ReadCorrect (limits : functional_document.DocumentLimits) (scope : alloc.vec.Vec U8) (source : Source) :
    core.result.Result RawOntology SourceError → Prop
  | .Ok o => ReadAs limits scope source o
  | .Err error => RejectedAs limits scope source error


/-- A vector index is in range exactly when its value is below the length. -/
private theorem lt_len_iff {α : Type} (v : alloc.vec.Vec α) (i : Usize) :
    i < alloc.vec.Vec.len v ↔ i.val < v.val.length := by
  simp [UScalar.lt_equiv, alloc.vec.Vec.len_val]

private theorem graph_ontology_correct (graph : rdf.RawGraph) (result : core.result.Result RawOntology SourceError)
    (ran : import_catalog.graph_ontology graph = .ok result) :
    (∃ mapped, rdf_mapping.map_graph graph = .ok (some mapped) ∧ result = .Ok mapped.ontology) ∨
      (rdf_mapping.map_graph graph = .ok none ∧ result = .Err .Graph) := by
  rw [import_catalog.graph_ontology] at ran
  obtain ⟨o, mapped, ran⟩ := bind_eq_ok ran
  cases o with
  | none => exact .inr ⟨mapped, (Result.ok_injective ran).symm⟩
  | some m => exact .inl ⟨m, mapped, (Result.ok_injective ran).symm⟩

/-- Whatever `read_source` returns is the result of the document's verified
    reader: an ontology read from the bytes as `ReadAs` says, or the first
    error. -/
theorem read_source_correct (source : Source) (limits : functional_document.DocumentLimits)
    (scope : alloc.vec.Vec U8) (result : core.result.Result RawOntology SourceError)
    (ran : import_catalog.read_source source limits scope = .ok result) :
    ReadCorrect limits scope source result := by
  rcases source with ⟨format, bytes⟩
  cases format with
  | Functional =>
    simp only [import_catalog.read_source, import_catalog.read_functional] at ran
    obtain ⟨r, run, errors, notNone, ontologies⟩ := Rowl.SourceReasoning.source_ontology_correct bytes limits scope
    rw [run] at ran
    cases r with
    | Ok o =>
      cases o with
      | none => exact absurd rfl notNone
      | some o =>
        simp only [bind_ok] at ran
        cases Result.ok_injective ran
        exact ontologies o rfl
    | Err e =>
      simp only [bind_ok] at ran
      cases Result.ok_injective ran
      simp only [ReadCorrect, RejectedAs]
      exact ⟨trivial, (errors e).mp rfl⟩
  | NTriples =>
    simp only [import_catalog.read_source, import_catalog.read_ntriples] at ran
    obtain ⟨r, run, correct⟩ := Rowl.NTriples.read_total_correct bytes scope
    rw [run] at ran
    cases r with
    | Graph graph =>
      simp only [bind_ok] at ran
      rcases graph_ontology_correct graph result ran with ⟨mapped, mapRun, same⟩ | ⟨mapRun, same⟩
      · subst same
        exact ⟨graph, mapped, correct, mapRun, rfl⟩
      · subst same
        simp only [ReadCorrect, RejectedAs]
        exact .inl ⟨trivial, graph, correct, mapRun⟩
    | Error e =>
      simp only [bind_ok] at ran
      cases Result.ok_injective ran
      simp only [ReadCorrect, RejectedAs]
      exact ⟨trivial, correct⟩
  | Turtle base =>
    simp only [import_catalog.read_source, import_catalog.read_turtle] at ran
    obtain ⟨r, run, correct⟩ := Rowl.Turtle.read_total_correct bytes scope base
    rw [run] at ran
    cases r with
    | Graph graph =>
      simp only [bind_ok] at ran
      rcases graph_ontology_correct graph result ran with ⟨mapped, mapRun, same⟩ | ⟨mapRun, same⟩
      · subst same
        exact ⟨graph, mapped, correct, mapRun, rfl⟩
      · subst same
        simp only [ReadCorrect, RejectedAs]
        exact .inr ⟨base, rfl, graph, correct, mapRun⟩
    | Error e =>
      simp only [bind_ok] at ran
      cases Result.ok_injective ran
      simp only [ReadCorrect, RejectedAs]
      exact ⟨base, rfl, correct⟩

/-- Reading a Functional Syntax document always returns. -/
theorem read_source_functional_total (source : Source) (limits : functional_document.DocumentLimits)
    (scope : alloc.vec.Vec U8) (functional : source.format = .Functional) :
    ∃ result, import_catalog.read_source source limits scope = .ok result := by
  rcases source with ⟨format, bytes⟩
  cases functional
  obtain ⟨r, run, -, -, -⟩ := Rowl.SourceReasoning.source_ontology_correct bytes limits scope
  cases r with
  | Ok o =>
    cases o with
    | none => exact ⟨.Err .Unmapped, by simp [import_catalog.read_source, import_catalog.read_functional, run]⟩
    | some o => exact ⟨.Ok o, by simp [import_catalog.read_source, import_catalog.read_functional, run]⟩
  | Err e => exact ⟨.Err (.Functional e), by simp [import_catalog.read_source, import_catalog.read_functional, run]⟩

/-- Every document of a catalog read, in the scope of its position, to the
    ontology at the same position. -/
def AllRead (limits : functional_document.DocumentLimits) (sources : List Source) (docs : List RawOntology) :
    Prop :=
  docs.length = sources.length ∧
    ∀ i s o, sources[i]? = some s → docs[i]? = some o → ReadAs limits (scopeVec i) s o

/-- What `read_sources` returns: every document read, or the first document
    that cannot be read, every earlier one being read. -/
def SourcesCorrect (limits : functional_document.DocumentLimits) (sources : List Source) :
    core.result.Result (alloc.vec.Vec RawOntology) Unread → Prop
  | .Ok docs => AllRead limits sources docs.val
  | .Err unread =>
      (∀ i < unread.document.val, ∀ s, sources[i]? = some s → ∃ o, ReadAs limits (scopeVec i) s o) ∧
      ∃ s, sources[unread.document.val]? = some s ∧
        RejectedAs limits (scopeVec unread.document.val) s unread.error

private theorem read_at_run (sources : alloc.vec.Vec Source) (limits : functional_document.DocumentLimits)
    (index : Usize) (s : Source) (found : sources.val[index.val]? = some s) :
    import_catalog.read_at sources limits index = import_catalog.read_source s limits (scopeVec index.val) := by
  have lookup : sources.index_usize index = .ok s := by
    simp [alloc.vec.Vec.index_usize, found]
  simp [import_catalog.read_at, alloc.vec.Vec.index_slice_index, lookup, document_scope_correct]

private theorem read_from_correct (sources : alloc.vec.Vec Source) (limits : functional_document.DocumentLimits)
    (index : Usize) (out : alloc.vec.Vec RawOntology) (count : out.val.length = index.val)
    (earlier : ∀ i s o, sources.val[i]? = some s → out.val[i]? = some o → ReadAs limits (scopeVec i) s o)
    (inside : index.val ≤ sources.val.length)
    (result : core.result.Result (alloc.vec.Vec RawOntology) Unread)
    (ran : import_catalog.read_from sources limits index out = .ok result) :
    SourcesCorrect limits sources.val result := by
  rw [import_catalog.read_from] at ran
  by_cases more : index.val < sources.val.length
  · simp only [lt_len_iff, more, ↓reduceIte] at ran
    obtain ⟨r, readRun, ran⟩ := bind_eq_ok ran
    have found : sources.val[index.val]? = some (sources.val[index.val]'more) := List.getElem?_eq_getElem more
    rw [read_at_run sources limits index _ found] at readRun
    have correct := read_source_correct _ limits _ r readRun
    cases r with
    | Ok o =>
      simp only at ran
      have room : out.val.length < Usize.max := by have := sources.property; omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out o room)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      rw [push] at ran
      simp only [bind_ok] at ran
      rw [advance] at ran
      simp only [bind_ok] at ran
      refine read_from_correct sources limits next pushed (by simp [contents, count, nextIs]) ?_
        (by omega) result ran
      intro i s' o' sourceAt docAt
      by_cases old : i < out.val.length
      · have item : pushed.val[i]? = out.val[i]? := by
          rw [contents, List.getElem?_append_left old]
        rw [item] at docAt
        exact earlier i s' o' sourceAt docAt
      · have bound : i < pushed.val.length := (List.getElem?_eq_some_iff.mp docAt).1
        have last : i = index.val := by simp [contents] at bound; omega
        subst last
        have item : pushed.val[index.val]? = some o := by
          rw [contents, ← count]
          simp
        rw [item] at docAt
        cases docAt
        rw [found] at sourceAt
        cases sourceAt
        exact correct
    | Err e =>
      simp only at ran
      cases Result.ok_injective ran
      refine ⟨?_, _, found, correct⟩
      intro i below s' sourceAt
      have inside' : i < out.val.length := by simp at below; omega
      exact ⟨out.val[i], earlier i s' _ sourceAt (List.getElem?_eq_getElem inside')⟩
  · have finished : index.val = sources.val.length := by omega
    simp only [lt_len_iff, more, ↓reduceIte] at ran
    cases Result.ok_injective ran
    exact ⟨by omega, earlier⟩
termination_by sources.val.length - index.val
decreasing_by omega

/-- Whatever `read_sources` returns is right: every document read by its
    verified reader in the scope of its position, or the first document that
    cannot be read. -/
theorem read_sources_correct (sources : alloc.vec.Vec Source) (limits : functional_document.DocumentLimits)
    (result : core.result.Result (alloc.vec.Vec RawOntology) Unread)
    (ran : import_catalog.read_sources sources limits = .ok result) :
    SourcesCorrect limits sources.val result :=
  read_from_correct sources limits 0#usize (alloc.vec.Vec.new RawOntology) (by simp)
    (fun i s o _ docAt => by simp at docAt) (by simp) result (by simpa [import_catalog.read_sources] using ran)

private theorem read_from_functional_total (sources : alloc.vec.Vec Source)
    (limits : functional_document.DocumentLimits) (all : ∀ s ∈ sources.val, s.format = .Functional)
    (index : Usize) (out : alloc.vec.Vec RawOntology) (count : out.val.length = index.val) :
    ∃ result, import_catalog.read_from sources limits index out = .ok result := by
  rw [import_catalog.read_from]
  by_cases more : index.val < sources.val.length
  · have found : sources.val[index.val]? = some (sources.val[index.val]'more) := List.getElem?_eq_getElem more
    obtain ⟨r, readRun⟩ := read_source_functional_total (sources.val[index.val]'more) limits (scopeVec index.val)
      (all _ (List.getElem_mem more))
    rw [← read_at_run sources limits index _ found] at readRun
    cases r with
    | Ok o =>
      have room : out.val.length < Usize.max := by have := sources.property; omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out o room)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨result, run⟩ := read_from_functional_total sources limits all next pushed
        (by simp [contents, count, nextIs])
      exact ⟨result, by simp [lt_len_iff, more, readRun, push, advance, run]⟩
    | Err e => exact ⟨.Err ⟨index, e⟩, by simp [lt_len_iff, more, readRun]⟩
  · exact ⟨.Ok out, by simp [lt_len_iff, more]⟩
termination_by sources.val.length - index.val
decreasing_by omega

/-- Reading a catalog of Functional Syntax documents always returns. -/
theorem read_sources_functional_total (sources : alloc.vec.Vec Source)
    (limits : functional_document.DocumentLimits) (all : ∀ s ∈ sources.val, s.format = .Functional) :
    ∃ result, import_catalog.read_sources sources limits = .ok result := by
  simpa [import_catalog.read_sources] using
    read_from_functional_total sources limits all 0#usize (alloc.vec.Vec.new RawOntology) (by simp)

/-! ## Import IRIs and the documents they name -/

/-- §3.2, §3.4: an import IRI names an ontology when it is the ontology IRI or
    the version IRI of the ontology, spelled with the same bytes. -/
def NamesIdentity (identity : OntologyIdentity) (iri : Iri) : Prop :=
  match identity with
  | .Anonymous => False
  | .Named ontology version =>
      ontology.spelling.val = iri.spelling.val ∨ ∃ v, version = some v ∧ v.spelling.val = iri.spelling.val

/-- The import IRI names the ontology. -/
def Names (o : RawOntology) (iri : Iri) : Prop := NamesIdentity o.identity iri

/-- The import IRI names the document at position `j`. -/
def NamedAt (docs : List RawOntology) (iri : Iri) (j : Nat) : Prop :=
  ∃ o, docs[j]? = some o ∧ Names o iri

theorem names_correct (identity : OntologyIdentity) (iri : Iri) :
    import_catalog.names identity iri = .ok (decide (NamesIdentity identity iri)) := by
  cases identity with
  | Anonymous => simp [import_catalog.names, NamesIdentity]
  | Named ontology version =>
    simp only [import_catalog.names, Rowl.DlValidity.same_bytes_spec, bind_ok]
    by_cases h : ontology.spelling.val = iri.spelling.val
    · simp [h, NamesIdentity]
    · cases version with
      | none => simp [h, NamesIdentity]
      | some v => simp [h, NamesIdentity, Rowl.DlValidity.same_bytes_spec]

/-- The positions, from `start` on, of the documents the IRI names, in order. -/
noncomputable def Targets (docs : List RawOntology) (iri : Iri) (start : Nat) : List Nat :=
  (List.range' start (docs.length - start)).filter (fun j => decide (NamedAt docs iri j))

theorem mem_targets (docs : List RawOntology) (iri : Iri) (start j : Nat) :
    j ∈ Targets docs iri start ↔ start ≤ j ∧ NamedAt docs iri j := by
  simp only [Targets, List.mem_filter, List.mem_range', decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, named⟩
    exact ⟨by omega, named⟩
  · rintro ⟨low, named⟩
    obtain ⟨o, found, n⟩ := named
    have inside : j < docs.length := (List.getElem?_eq_some_iff.mp found).1
    exact ⟨⟨j - start, by omega, by omega⟩, ⟨o, found, n⟩⟩

theorem targets_sorted (docs : List RawOntology) (iri : Iri) (start : Nat) :
    (Targets docs iri start).Pairwise (· < ·) := by
  unfold Targets
  apply List.Pairwise.filter
  exact List.pairwise_lt_range'

private theorem targets_step (docs : List RawOntology) (iri : Iri) (j : Nat) (h : j < docs.length) :
    Targets docs iri j =
      if Names (docs[j]'h) iri then j :: Targets docs iri (j + 1) else Targets docs iri (j + 1) := by
  have count : docs.length - j = (docs.length - (j + 1)) + 1 := by omega
  have named : NamedAt docs iri j ↔ Names (docs[j]'h) iri := by
    constructor
    · rintro ⟨o, found, n⟩
      rw [List.getElem?_eq_getElem h] at found
      cases found
      exact n
    · intro n
      exact ⟨docs[j]'h, List.getElem?_eq_getElem h, n⟩
  simp only [Targets, count, List.range'_succ, List.filter_cons]
  by_cases n : Names (docs[j]'h) iri <;> simp [n, named]

private theorem targets_done (docs : List RawOntology) (iri : Iri) (j : Nat) (h : docs.length ≤ j) :
    Targets docs iri j = [] := by
  simp [Targets, show docs.length - j = 0 by omega]

theorem targets_from_correct (docs : alloc.vec.Vec RawOntology) (iri : Iri) (index : Usize)
    (fits : docs.val.length ≤ U32.max + 1) (inside : index.val ≤ docs.val.length) :
    ∃ found, import_catalog.targets_from docs iri index = .ok found ∧
      (ids found).map UScalar.val = Targets docs.val iri index.val := by
  rw [import_catalog.targets_from]
  by_cases more : index.val < docs.val.length
  · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨rest, restRun, restValue⟩ := targets_from_correct docs iri next fits (by omega)
    have lookup : docs.index_usize index = .ok (docs.val[index.val]'more) := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have keyValue : (UScalar.cast .U32 index).val = index.val := by
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      simp only [U32.max_eq] at fits
      simp
      omega
    rw [targets_step docs.val iri index.val more]
    by_cases named : Names (docs.val[index.val]'more) iri
    · refine ⟨.Cons (UScalar.cast .U32 index) rest, ?_, ?_⟩
      · have namedId : NamesIdentity (docs.val[index.val]'more).identity iri := named
        simp [lt_len_iff, more, advance, restRun, alloc.vec.Vec.index_slice_index, lookup, names_correct,
          namedId]
      · simp [ids, keyValue, restValue, nextIs, named]
    · refine ⟨rest, ?_, ?_⟩
      · have namedId : ¬ NamesIdentity (docs.val[index.val]'more).identity iri := named
        simp [lt_len_iff, more, advance, restRun, alloc.vec.Vec.index_slice_index, lookup, names_correct,
          namedId]
      · simp [restValue, nextIs, named]
  · exact ⟨.Empty, by simp [lt_len_iff, more], by simp [ids, targets_done docs.val iri index.val (by omega)]⟩
termination_by docs.val.length - index.val
decreasing_by omega

/-- What `lookup` answers, against the documents the IRI names (§3.2, §3.4):
    none, exactly one, or the first two of several. -/
def LookupCorrect (docs : List RawOntology) (iri : Iri) : Lookup → Prop
  | .Missing => ∀ j, ¬ NamedAt docs iri j
  | .Unique k => ∀ j, NamedAt docs iri j ↔ j = k.val
  | .Ambiguous first second => first.val < second.val ∧ NamedAt docs iri first.val ∧
      NamedAt docs iri second.val ∧ ∀ j, j < second.val → NamedAt docs iri j → j = first.val

theorem lookup_correct (docs : alloc.vec.Vec RawOntology) (iri : Iri) (fits : docs.val.length ≤ U32.max + 1) :
    ∃ result, import_catalog.lookup docs iri = .ok result ∧ LookupCorrect docs.val iri result := by
  obtain ⟨found, run, value⟩ := targets_from_correct docs iri 0#usize fits (by simp)
  have members : ∀ j, j ∈ (ids found).map UScalar.val ↔ NamedAt docs.val iri j := by
    intro j
    rw [value, mem_targets]
    simp
  have sorted : ((ids found).map UScalar.val).Pairwise (· < ·) := by
    rw [value]; exact targets_sorted docs.val iri 0
  rw [import_catalog.lookup, run]
  cases found with
  | Empty =>
    refine ⟨.Missing, by simp, ?_⟩
    intro j named
    simpa [ids] using (members j).mpr named
  | Cons first rest =>
    cases rest with
    | Empty =>
      refine ⟨.Unique first, by simp, ?_⟩
      intro j
      rw [← members j]
      simp [ids]
    | Cons second tail =>
      refine ⟨.Ambiguous first second, by simp, ?_⟩
      have firstNamed := (members first.val).mp (by simp [ids])
      have secondNamed := (members second.val).mp (by simp [ids])
      simp only [ids, List.map_cons] at sorted
      rw [List.pairwise_cons, List.pairwise_cons] at sorted
      obtain ⟨firstBelow, secondBelow, _⟩ := sorted
      refine ⟨firstBelow second.val List.mem_cons_self, firstNamed, secondNamed, ?_⟩
      intro j below named
      have member := (members j).mpr named
      simp only [ids, List.map_cons, List.mem_cons] at member
      rcases member with same | same | inTail
      · exact same
      · omega
      · have larger := secondBelow j inTail
        omega

/-! ## The catalog -/

/-- The positions of the documents the import IRIs name, import by import. -/
noncomputable def Dependencies (docs : List RawOntology) (iris : List Iri) : List Nat :=
  iris.flatMap (fun iri => Targets docs iri 0)

theorem mem_dependencies (docs : List RawOntology) (iris : List Iri) (j : Nat) :
    j ∈ Dependencies docs iris ↔ ∃ iri ∈ iris, NamedAt docs iri j := by
  simp [Dependencies, mem_targets]

private theorem append_correct (a b : imports.DocumentIds) :
    ∃ c, import_catalog.append a b = .ok c ∧ ids c = ids a ++ ids b := by
  induction a with
  | Empty => exact ⟨b, by simp [import_catalog.append], by simp [ids]⟩
  | Cons k tail ih =>
    obtain ⟨c, hc, hv⟩ := ih
    exact ⟨.Cons k c, by simp [import_catalog.append, hc], by simp [ids, hv]⟩

theorem dependencies_from_correct (docs : alloc.vec.Vec RawOntology) (iris : alloc.vec.Vec Iri) (index : Usize)
    (fits : docs.val.length ≤ U32.max + 1) (inside : index.val ≤ iris.val.length) :
    ∃ found, import_catalog.dependencies_from docs iris index = .ok found ∧
      (ids found).map UScalar.val = Dependencies docs.val (iris.val.drop index.val) := by
  rw [import_catalog.dependencies_from]
  by_cases more : index.val < iris.val.length
  · have lookup : iris.index_usize index = .ok (iris.val[index.val]'more) := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨first, firstRun, firstValue⟩ := targets_from_correct docs (iris.val[index.val]'more) 0#usize fits
      (by simp)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨rest, restRun, restValue⟩ := dependencies_from_correct docs iris next fits (by omega)
    obtain ⟨joined, joinRun, joinValue⟩ := append_correct first rest
    refine ⟨joined, ?_, ?_⟩
    · simp [lt_len_iff, more, alloc.vec.Vec.index_slice_index, lookup, firstRun, advance, restRun, joinRun]
    · rw [joinValue, List.map_append, firstValue, restValue, nextIs, List.drop_eq_getElem_cons more]
      simp only [Dependencies, List.flatMap_cons]
      simp
  · refine ⟨.Empty, by simp [lt_len_iff, more], ?_⟩
    simp [ids, Dependencies, List.drop_eq_nil_of_le (show iris.val.length ≤ index.val by omega)]
termination_by iris.val.length - index.val
decreasing_by omega

/-- A catalog of the documents `docs`: no more documents than `u32` keys, every
    document under its position, in order, without bytes, with the positions of
    the documents its import IRIs name, import by import. -/
def CatalogOf (docs : List RawOntology) (c : imports.DocumentCatalog) : Prop :=
  docs.length ≤ U32.max ∧
  (keys c).map UScalar.val = List.range docs.length ∧
  ∀ row ∈ rows c, row.2.1.val = [] ∧
    ∃ o, docs[row.1.val]? = some o ∧ (ids row.2.2).map UScalar.val = Dependencies docs o.imports.val

private theorem catalog_from_correct (docs : alloc.vec.Vec RawOntology) (index : Usize)
    (fits : docs.val.length ≤ U32.max) (inside : index.val ≤ docs.val.length) :
    ∃ c, import_catalog.catalog_from docs index = .ok c ∧
      (rows c).map (fun row => row.1.val) = List.range' index.val (docs.val.length - index.val) ∧
      ∀ row ∈ rows c, row.2.1.val = [] ∧
        ∃ o, docs.val[row.1.val]? = some o ∧ (ids row.2.2).map UScalar.val = Dependencies docs.val o.imports.val := by
  rw [import_catalog.catalog_from]
  by_cases more : index.val < docs.val.length
  · have keyValue : (UScalar.cast .U32 index).val = index.val := by
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      simp only [U32.max_eq] at fits
      simp
      omega
    have lookup : docs.index_usize index = .ok (docs.val[index.val]'more) := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨deps, depsRun, depsValue⟩ := dependencies_from_correct docs (docs.val[index.val]'more).imports 0#usize
      (by omega) (by simp)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨rest, restRun, restKeys, restRows⟩ := catalog_from_correct docs next fits (by omega)
    refine ⟨.Document (UScalar.cast .U32 index) (alloc.vec.Vec.new U8) deps rest, ?_, ?_, ?_⟩
    · simp [lt_len_iff, more, alloc.vec.Vec.index_slice_index, lookup, depsRun, advance, restRun]
    · have count : docs.val.length - index.val = (docs.val.length - (index.val + 1)) + 1 := by omega
      simp [rows, keyValue, restKeys, nextIs, count, List.range'_succ]
    · intro row member
      simp only [rows, List.mem_cons] at member
      rcases member with same | later
      · subst same
        refine ⟨by simp, docs.val[index.val]'more, ?_, ?_⟩
        · simp [keyValue, List.getElem?_eq_getElem more]
        · simpa using depsValue
      · exact restRows row later
  · refine ⟨.Empty, by simp [lt_len_iff, more], ?_, ?_⟩
    · simp [rows, show docs.val.length - index.val = 0 by omega]
    · simp [rows]
termination_by docs.val.length - index.val
decreasing_by omega

/-- `catalog` builds the catalog of the documents exactly when there are no more
    of them than `u32` keys. -/
theorem catalog_correct (docs : alloc.vec.Vec RawOntology) :
    ∃ result, import_catalog.catalog docs = .ok result ∧
      (result = none ↔ U32.max < docs.val.length) ∧ ∀ c, result = some c → CatalogOf docs.val c := by
  have rmax : U32.rMax = U32.max := by simp [U32.rMax, U32.max_eq]
  rw [import_catalog.catalog]
  by_cases fits : docs.val.length ≤ U32.max
  · have fits' : docs.val.length ≤ U32.rMax := by rw [rmax]; exact fits
    obtain ⟨c, run, keyed, rowsOk⟩ := catalog_from_correct docs 0#usize fits (by simp)
    refine ⟨some c, ?_, by simp; omega, ?_⟩
    · have power : 2 ^ 32 ≤ 2 ^ System.Platform.numBits :=
        Nat.pow_le_pow_right (by omega) (by cases System.Platform.numBits_eq <;> simp [*])
      simp [UScalar.le_equiv, alloc.vec.Vec.len_val, UScalar.cast_val_eq, core.num.U32.MAX, fits', run,
        Nat.mod_eq_of_lt (show U32.rMax < 2 ^ System.Platform.numBits by simp [U32.rMax]; omega)]
    · intro c' same
      cases same
      refine ⟨fits, ?_, rowsOk⟩
      have zero : (0#usize : Usize).val = 0 := by simp
      rw [zero, Nat.sub_zero] at keyed
      rw [List.range_eq_range']
      simpa [keys, List.map_map, Function.comp_def] using keyed
  · have fits' : ¬ docs.val.length ≤ U32.rMax := by rw [rmax]; exact fits
    have power : 2 ^ 32 ≤ 2 ^ System.Platform.numBits :=
      Nat.pow_le_pow_right (by omega) (by cases System.Platform.numBits_eq <;> simp [*])
    exact ⟨none, by simp [UScalar.le_equiv, alloc.vec.Vec.len_val, UScalar.cast_val_eq, core.num.U32.MAX, fits',
      Nat.mod_eq_of_lt (show U32.rMax < 2 ^ System.Platform.numBits by simp [U32.rMax]; omega)], by simp; omega,
      by simp⟩

/-! ## Direct imports and the import closure -/

/-- §3.4: the document at position `i` directly imports the document at
    position `j`: one of the import IRIs of `i` names `j`. -/
def DirectlyImports (docs : List RawOntology) (i j : Nat) : Prop :=
  ∃ o, docs[i]? = some o ∧ ∃ iri ∈ o.imports.val, NamedAt docs iri j

/-- §3.4: the document at position `j` is in the import closure of the document
    at position `root`: it is the root or imported by it, directly or not. -/
def InClosure (docs : List RawOntology) (root j : Nat) : Prop :=
  Relation.ReflTransGen (DirectlyImports docs) root j

/-- The keys of a catalog of the documents are distinct. -/
theorem catalog_keys_nodup (docs : List RawOntology) (c : imports.DocumentCatalog) (built : CatalogOf docs c) :
    (keys c).Nodup := by
  have distinct : ((keys c).map UScalar.val).Nodup := by rw [built.2.1]; exact List.nodup_range
  exact List.Nodup.of_map _ distinct

private theorem u32_ext {a b : U32} (same : a.val = b.val) : a = b := UScalar.eq_of_val_eq same

/-- The catalog's edges are exactly the direct imports of the documents. -/
theorem catalog_edges (docs : List RawOntology) (c : imports.DocumentCatalog) (built : CatalogOf docs c)
    (a b : U32) : Edge c a b ↔ DirectlyImports docs a.val b.val := by
  obtain ⟨_, keyed, rowsOk⟩ := built
  constructor
  · rintro ⟨bytes, deps, member, target⟩
    obtain ⟨_, o, found, depsValue⟩ := rowsOk _ member
    refine ⟨o, found, ?_⟩
    have inDeps : b.val ∈ Dependencies docs o.imports.val := by
      rw [← depsValue]; exact List.mem_map_of_mem target
    exact (mem_dependencies docs o.imports.val b.val).mp inDeps
  · rintro ⟨o, found, iri, imported, named⟩
    have inside : a.val < docs.length := (List.getElem?_eq_some_iff.mp found).1
    have keyed' : a.val ∈ (keys c).map UScalar.val := by rw [keyed]; exact List.mem_range.mpr inside
    obtain ⟨key, keyMember, keySame⟩ := List.mem_map.mp keyed'
    have keyIs : key = a := u32_ext keySame
    subst keyIs
    obtain ⟨⟨k, bytes, deps⟩, rowMember, rowKey⟩ := List.mem_map.mp keyMember
    simp only at rowKey
    subst rowKey
    obtain ⟨_, o', found', depsValue⟩ := rowsOk _ rowMember
    simp only at found'
    rw [found] at found'
    cases found'
    have inDeps : b.val ∈ (ids deps).map UScalar.val := by
      rw [depsValue]; exact (mem_dependencies docs o.imports.val b.val).mpr ⟨iri, imported, named⟩
    obtain ⟨x, xMember, xSame⟩ := List.mem_map.mp inDeps
    have xIs : x = b := u32_ext xSame
    subst xIs
    exact ⟨bytes, deps, rowMember, xMember⟩

/-- Reachability in the catalog is exactly the import closure (§3.4). -/
theorem catalog_reachable (docs : List RawOntology) (c : imports.DocumentCatalog) (built : CatalogOf docs c)
    (root target : U32) : Reachable c root target ↔ InClosure docs root.val target.val := by
  constructor
  · intro reach
    induction reach with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ edge ih => exact ih.tail ((catalog_edges docs c built _ _).mp edge)
  · intro closure
    have general : ∀ m, Relation.ReflTransGen (DirectlyImports docs) root.val m →
        ∀ k : U32, k.val = m → Reachable c root k := by
      intro m path
      induction path with
      | refl =>
        intro k same
        have : k = root := u32_ext same
        subst this
        exact Relation.ReflTransGen.refl
      | @tail middle last _ edge ih =>
        intro k same
        have inside : middle < docs.length := by
          obtain ⟨o, found, _⟩ := edge
          exact (List.getElem?_eq_some_iff.mp found).1
        have small : middle < 2 ^ 32 := by
          have := built.1
          simp only [U32.max_eq] at this
          omega
        let key : U32 := ⟨BitVec.ofNat 32 middle⟩
        have keyValue : key.val = middle := by
          show (BitVec.ofNat 32 middle).toNat = middle
          rw [BitVec.toNat_ofNat]
          omega
        have step : Edge c key k := (catalog_edges docs c built key k).mpr (by rw [keyValue, same]; exact edge)
        exact (ih key keyValue).tail step
    exact general target.val closure target rfl

end Rowl.ImportCatalog
