import Rowl.ImportCatalog
import Rowl.AnonymousScopes
import Rowl.Nnf

/-!
Import closures, second part: the import closure of a root document, its axiom
closure and its meaning (OWL 2 Structural Specification §3.4, Direct Semantics
§2.4).

`import_closure::assemble` takes the ontologies of a catalog, each read in the
scope of its position, and a root position. It builds the catalog of
`ImportCatalog.lean`, resolves it from the root with the proved
`imports::resolve`, and marks the documents of the import closure
(`InClosure`). Every import IRI of a document of the closure must name exactly
one document (`Resolved`); otherwise the first that does not, in catalog order,
is the error, naming the document and the IRI (`FirstUnresolved`). Every
anonymous individual of a document of the closure must have the scope of its
position (`ClosureScoped`); otherwise the first document that does not is the
error. The closure (`AssembledFrom`) then has the documents of the import
closure in catalog order, the root's identity and imports, and the ontology
annotations and axioms of those documents in that order, every axiom with its
document and position (`origins`).

`closure_models` gives the meaning: an interpretation is a model of the
assembled axioms exactly when it is a model of the axioms of every document of
the import closure, each with an assignment of its anonymous individuals of
its own — the anonymous individuals of the documents are standardized apart.
Consistency, entailment, satisfiability, subsumption and instance checking of
the assembled axioms are therefore those of the import closure.
-/
namespace Rowl.ImportClosure
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open RowlRust.import_closure (Closure ClosureError Origin Gathered)
open RowlRust.import_catalog (Source Unread)
open Rowl.Imports (rows keys ids Edge Reachable)
open Rowl.ImportCatalog (NamedAt InClosure DirectlyImports CatalogOf scopeOf scopeVec AllRead SourcesCorrect
  LookupCorrect)
open Rowl.AnonymousScopes (ScopedOntology ScopedAnnotated ScopedAxiom ScopedParts models_parts)
open Rowl.Owl (DatatypeMap ValueEmbedding Vocabulary IsVocabulary IsInterpretation Interpretation Model
  modelsClosure Consistent Entails ClassSatisfiable Subsumed InstanceOf classDenote)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v w

/-! ## What the closure is -/

/-- The axioms of the document at position `i`, none past the end. -/
def axiomsAt (docs : List RawOntology) (i : Nat) : List AnnotatedAxiom := (docs[i]?.map (·.axioms.val)).getD []
/-- The ontology annotations of the document at position `i`. -/
def annotationsAt (docs : List RawOntology) (i : Nat) : List Annotation := (docs[i]?.map (·.annotations.val)).getD []
/-- The import IRIs of the document at position `i`. -/
def importsAt (docs : List RawOntology) (i : Nat) : List Iri := (docs[i]?.map (·.imports.val)).getD []

/-- The positions of the documents of the import closure of `root`, in catalog order. -/
noncomputable def ClosureDocuments (docs : List RawOntology) (root : Nat) : List Nat :=
  (List.range docs.length).filter (fun i => decide (InClosure docs root i))

/-- The import IRI names exactly one document (§3.2, §3.4). -/
def Resolved (docs : List RawOntology) (iri : Iri) : Prop := ∃ j, ∀ k, NamedAt docs iri k ↔ k = j

/-- Every import IRI of every document of the import closure names exactly one document. -/
def ImportsResolved (docs : List RawOntology) (root : Nat) : Prop :=
  ∀ i, InClosure docs root i → ∀ iri ∈ importsAt docs i, Resolved docs iri

/-- The first import IRI, in catalog order, of a document of the import closure
    that names no document or several: the document at `d` is in the closure,
    its import IRI at some position `p` is `iri` and does not name exactly one
    document, its earlier import IRIs and every import IRI of every earlier
    document of the closure do. -/
def FirstUnresolved (docs : List RawOntology) (root d : Nat) (iri : Iri) : Prop :=
  InClosure docs root d ∧ ¬ Resolved docs iri ∧
  (∃ p : Nat, (importsAt docs d)[p]? = some iri ∧ ∀ q < p, ∀ earlier, (importsAt docs d)[q]? = some earlier →
    Resolved docs earlier) ∧
  ∀ i < d, InClosure docs root i → ∀ earlier ∈ importsAt docs i, Resolved docs earlier

/-- Every anonymous individual of every document of the import closure has the
    scope of the document's position (§5.6.2). -/
def ClosureScoped (docs : List RawOntology) (root : Nat) : Prop :=
  ∀ i, InClosure docs root i → ∀ o, docs[i]? = some o → ScopedOntology (scopeOf i) o

/-- The assembled closure of the import closure of `root`: the documents of the
    closure in catalog order, the root's identity and imports, the ontology
    annotations and the axioms of the documents of the closure in that order,
    and for every axiom its document and its position among that document's
    axioms. -/
def AssembledFrom (docs : List RawOntology) (root : Nat) (c : Closure) : Prop :=
  ∃ o, docs[root]? = some o ∧
    c.documents.val.map UScalar.val = ClosureDocuments docs root ∧
    c.ontology.identity = o.identity ∧ c.ontology.imports = o.imports ∧
    c.ontology.annotations.val = (ClosureDocuments docs root).flatMap (annotationsAt docs) ∧
    c.ontology.axioms.val = (ClosureDocuments docs root).flatMap (axiomsAt docs) ∧
    c.origins.val.map (fun origin => (origin.document.val, origin.position.val)) =
      (ClosureDocuments docs root).flatMap (fun i => (List.range (axiomsAt docs i).length).map (fun p => (i, p)))

/-- What `assemble` returns for the ontologies `docs` and the root. -/
def AssembleCorrect (docs : List RawOntology) (root : Nat) : core.result.Result Closure ClosureError → Prop
  | .Ok c => root < docs.length ∧ docs.length ≤ U32.max ∧ ImportsResolved docs root ∧ ClosureScoped docs root ∧
      AssembledFrom docs root c
  | .Err .NoRoot => docs.length ≤ root
  | .Err .TooManyDocuments => root < docs.length ∧ U32.max < docs.length
  | .Err .Unresolved => False
  | .Err (.Unread _) => False
  | .Err (.MissingImport document iri) => root < docs.length ∧ docs.length ≤ U32.max ∧
      FirstUnresolved docs root document.val iri ∧ ∀ j, ¬ NamedAt docs iri j
  | .Err (.AmbiguousImport document iri first second) => root < docs.length ∧ docs.length ≤ U32.max ∧
      FirstUnresolved docs root document.val iri ∧ first.val < second.val ∧
      NamedAt docs iri first.val ∧ NamedAt docs iri second.val
  | .Err (.OutOfScope document) => root < docs.length ∧ docs.length ≤ U32.max ∧ ImportsResolved docs root ∧
      InClosure docs root document.val ∧
      (∀ o, docs[document.val]? = some o → ¬ ScopedOntology (scopeOf document.val) o) ∧
      ∀ i < document.val, InClosure docs root i → ∀ o, docs[i]? = some o → ScopedOntology (scopeOf i) o
  | .Err .TooLarge => root < docs.length ∧ docs.length ≤ U32.max ∧ ImportsResolved docs root ∧
      ClosureScoped docs root ∧
      (Usize.max < ((ClosureDocuments docs root).flatMap (axiomsAt docs)).length ∨
        Usize.max < ((ClosureDocuments docs root).flatMap (annotationsAt docs)).length)

/-! ## The closure's documents -/

theorem mem_closure_documents (docs : List RawOntology) (root i : Nat) :
    i ∈ ClosureDocuments docs root ↔ i < docs.length ∧ InClosure docs root i := by
  simp [ClosureDocuments]

theorem closure_documents_nodup (docs : List RawOntology) (root : Nat) : (ClosureDocuments docs root).Nodup :=
  (List.nodup_range).filter _

/-- Every document of the import closure of a document of the catalog is in the catalog. -/
theorem closure_inside (docs : List RawOntology) (root i : Nat) (inside : root < docs.length)
    (closure : InClosure docs root i) : i < docs.length := by
  induction closure with
  | refl => exact inside
  | tail _ edge _ =>
    obtain ⟨_, _, _, _, o, found, _⟩ := edge
    exact (List.getElem?_eq_some_iff.mp found).1

/-! ## The steps of `assemble` -/

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

private theorem lt_len_iff {α : Type} (v : alloc.vec.Vec α) (i : Usize) :
    i < alloc.vec.Vec.len v ↔ i.val < v.val.length := by
  simp [UScalar.lt_equiv, alloc.vec.Vec.len_val]

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by simp [core.num.Usize.MAX]

private theorem below_max_iff {α : Type} (v : alloc.vec.Vec α) :
    alloc.vec.Vec.len v < core.num.Usize.MAX ↔ v.val.length < Usize.max := by
  simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]

private theorem cast_u32_val (k : U32) : (UScalar.cast .Usize k).val = k.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  rw [UScalarTy.Usize_numBits_eq, UScalarTy.U32_numBits_eq]
  cases System.Platform.numBits_eq <;> simp [*]

private theorem lookup_vec {α : Type} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    v.index_usize i = .ok (v.val[i.val]'h) := by
  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]

/-! ### Marking the closure -/

private theorem falses_correct (count : Usize) (out : alloc.vec.Vec Bool)
    (allFalse : ∀ b ∈ out.val, b = false) (small : out.val.length ≤ count.val) :
    ∃ v, import_closure.falses count out = .ok v ∧ v.val = List.replicate count.val false := by
  rw [import_closure.falses]
  by_cases more : out.val.length < count.val
  · have room : out.val.length < Usize.max := by have := count.hBounds; scalar_tac
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out false room)
    obtain ⟨v, run, value⟩ := falses_correct count pushed
      (by rw [contents]; intro b member; simp at member; rcases member with old | new
          · exact allFalse b old
          · exact new) (by rw [contents]; simp; omega)
    exact ⟨v, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more, push, run], value⟩
  · have same : out.val.length = count.val := by omega
    refine ⟨out, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, more], ?_⟩
    exact List.eq_replicate_iff.mpr ⟨same, allFalse⟩
termination_by count.val - out.val.length
decreasing_by
  have : pushed.val.length = out.val.length + 1 := by rw [contents]; simp
  omega

/-- The positions of the keys of a resolved closure. -/
def Marked (closure : imports.DocumentCatalog) (i : Nat) : Prop := ∃ k ∈ keys closure, k.val = i

private theorem mark_correct (closure : imports.DocumentCatalog) (included : alloc.vec.Vec Bool) :
    ∃ v, import_closure.mark closure included = .ok v ∧
      ∀ i, v.val[i]? = (included.val[i]?).map (fun b => b || decide (Marked closure i)) := by
  induction closure generalizing included with
  | Empty =>
    refine ⟨included, by simp [import_closure.mark], ?_⟩
    intro i
    cases included.val[i]? <;> simp [Marked, keys, rows]
  | Document key bytes deps next ih =>
    have keyValue := cast_u32_val key
    by_cases inside : key.val < included.val.length
    · have inside' : (UScalar.cast .Usize key).val < included.val.length := by rw [keyValue]; exact inside
      obtain ⟨v, run, value⟩ := ih (included.set (UScalar.cast .Usize key) true)
      refine ⟨v, ?_, ?_⟩
      · simp [import_closure.mark, lt_len_iff, keyValue, inside, alloc.vec.Vec.index_mut_usize,
          lookup_vec included _ inside', run]
      · intro i
        rw [value i, alloc.vec.Vec.set_val_eq, List.getElem?_set, keyValue]
        by_cases same : key.val = i
        · subst same
          simp [inside, List.getElem?_eq_getElem inside, Marked, keys, rows]
        · simp only [same, ↓reduceIte]
          cases included.val[i]? <;> simp [Marked, keys, rows, same]
    · have outside : ¬ (UScalar.cast .Usize key).val < included.val.length := by rw [keyValue]; exact inside
      obtain ⟨v, run, value⟩ := ih included
      refine ⟨v, ?_, ?_⟩
      · simp [import_closure.mark, lt_len_iff, keyValue, inside, run]
      · intro i
        rw [value i]
        by_cases same : key.val = i
        · subst same
          simp [List.getElem?_eq_none (show included.val.length ≤ key.val by omega)]
        · cases included.val[i]? <;> simp [Marked, keys, rows, same]

private theorem included_at_correct (included : alloc.vec.Vec Bool) (index : Usize) :
    import_closure.included_at included index = .ok ((included.val[index.val]?).getD false) := by
  rw [import_closure.included_at]
  by_cases inside : index.val < included.val.length
  · simp [lt_len_iff, inside, alloc.vec.Vec.index_slice_index, lookup_vec included index inside,
      List.getElem?_eq_getElem inside]
  · simp [lt_len_iff, inside, List.getElem?_eq_none (show included.val.length ≤ index.val by omega)]

/-- The marks of the closure's keys among `count` positions. -/
private theorem marks_correct (closure : imports.DocumentCatalog) (count : Usize) :
    ∃ start v, import_closure.falses count (alloc.vec.Vec.new Bool) = .ok start ∧
      import_closure.mark closure start = .ok v ∧
      ∀ index : Usize, import_closure.included_at v index =
        .ok (decide (index.val < count.val ∧ Marked closure index.val)) := by
  obtain ⟨start, startRun, startValue⟩ := falses_correct count (alloc.vec.Vec.new Bool)
    (by intro b member; simp at member) (by simp)
  obtain ⟨v, run, value⟩ := mark_correct closure start
  refine ⟨start, v, startRun, run, ?_⟩
  intro index
  rw [included_at_correct, value, startValue]
  by_cases inside : index.val < count.val
  · simp [List.getElem?_replicate, inside]
  · simp [List.getElem?_replicate, inside]

/-! ### Imports and scopes of the marked documents -/

private theorem lookup_resolved (docs : List RawOntology) (iri : Iri) (k : U32)
    (correct : LookupCorrect docs iri (.Unique k)) : Resolved docs iri := ⟨k.val, correct⟩

private theorem missing_unresolved (docs : List RawOntology) (iri : Iri)
    (correct : ∀ j, ¬ NamedAt docs iri j) : ¬ Resolved docs iri := by
  rintro ⟨j, named⟩
  exact correct j ((named j).mpr rfl)

private theorem ambiguous_unresolved (docs : List RawOntology) (iri : Iri) (a b : Nat) (different : a < b)
    (na : NamedAt docs iri a) (nb : NamedAt docs iri b) : ¬ Resolved docs iri := by
  rintro ⟨j, named⟩
  have ha := (named a).mp na
  have hb := (named b).mp nb
  omega

/-- The error for an import IRI of document `d` that names no document or several. -/
def UnresolvedError (docs : List RawOntology) (d : Nat) (iri : Iri) : ClosureError → Prop
  | .MissingImport document i => document.val = d ∧ i = iri ∧ ∀ j, ¬ NamedAt docs iri j
  | .AmbiguousImport document i first second => document.val = d ∧ i = iri ∧ first.val < second.val ∧
      NamedAt docs iri first.val ∧ NamedAt docs iri second.val
  | _ => False

private theorem unresolved_error_not (docs : List RawOntology) (d : Nat) (iri : Iri) (e : ClosureError)
    (error : UnresolvedError docs d iri e) : ¬ Resolved docs iri := by
  cases e with
  | MissingImport document i => exact missing_unresolved docs iri error.2.2
  | AmbiguousImport document i first second =>
    exact ambiguous_unresolved docs iri _ _ error.2.2.1 error.2.2.2.1 error.2.2.2.2
  | _ => exact error.elim

private theorem unresolved_import_correct (ontologies : alloc.vec.Vec RawOntology) (iris : alloc.vec.Vec Iri)
    (document index : Usize) (fits : ontologies.val.length ≤ U32.max + 1) :
    ∃ r, import_closure.unresolved_import ontologies iris document index = .ok r ∧
      match r with
      | none => ∀ iri ∈ iris.val.drop index.val, Resolved ontologies.val iri
      | some e => ∃ p iri, index.val ≤ p ∧ iris.val[p]? = some iri ∧
          (∀ q earlier, index.val ≤ q → q < p → iris.val[q]? = some earlier → Resolved ontologies.val earlier) ∧
          UnresolvedError ontologies.val document.val iri e := by
  rw [import_closure.unresolved_import]
  by_cases more : index.val < iris.val.length
  · obtain ⟨l, lookupRun, lookupCorrect⟩ := Rowl.ImportCatalog.lookup_correct ontologies (iris.val[index.val]'more) fits
    have item := lookup_vec iris index more
    cases l with
    | Missing =>
      refine ⟨some (.MissingImport document (iris.val[index.val]'more)), ?_, ?_⟩
      · simp [lt_len_iff, more, alloc.vec.Vec.index_slice_index, item, lookupRun, Rowl.Nnf.copy_iri_identity]
      · exact ⟨index.val, iris.val[index.val]'more, le_refl _, List.getElem?_eq_getElem more,
          fun q _ low high _ => absurd high (by omega), rfl, rfl, lookupCorrect⟩
    | Unique k =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, correct⟩ := unresolved_import_correct ontologies iris document next fits
      refine ⟨r, by simp [lt_len_iff, more, alloc.vec.Vec.index_slice_index, item, lookupRun, advance, run], ?_⟩
      have here : Resolved ontologies.val (iris.val[index.val]'more) := lookup_resolved _ _ k lookupCorrect
      cases r with
      | none =>
        intro iri member
        rw [List.drop_eq_getElem_cons more] at member
        rcases List.mem_cons.mp member with same | later
        · subst same; exact here
        · rw [nextIs] at correct; exact correct iri later
      | some e =>
        obtain ⟨p, iri, low, found, earlier, error⟩ := correct
        refine ⟨p, iri, by omega, found, ?_, error⟩
        intro q earlierIri qLow qHigh qFound
        by_cases first : q = index.val
        · subst first
          rw [List.getElem?_eq_getElem more] at qFound
          cases qFound
          exact here
        · exact earlier q earlierIri (by omega) qHigh qFound
    | Ambiguous first second =>
      refine ⟨some (.AmbiguousImport document (iris.val[index.val]'more) (UScalar.cast .Usize first)
        (UScalar.cast .Usize second)), ?_, ?_⟩
      · simp [lt_len_iff, more, alloc.vec.Vec.index_slice_index, item, lookupRun, Rowl.Nnf.copy_iri_identity]
      · obtain ⟨order, firstNamed, secondNamed, _⟩ := lookupCorrect
        refine ⟨index.val, iris.val[index.val]'more, le_refl _, List.getElem?_eq_getElem more,
          fun q _ low high _ => absurd high (by omega), rfl, rfl, ?_, ?_, ?_⟩
        · rw [cast_u32_val, cast_u32_val]; exact order
        · rw [cast_u32_val]; exact firstNamed
        · rw [cast_u32_val]; exact secondNamed
  · refine ⟨none, by simp [lt_len_iff, more], ?_⟩
    intro iri member
    simp [List.drop_eq_nil_of_le (show iris.val.length ≤ index.val by omega)] at member
termination_by iris.val.length - index.val
decreasing_by omega

private theorem imports_at_get (docs : List RawOntology) (i : Nat) (h : i < docs.length) :
    importsAt docs i = (docs[i]'h).imports.val := by
  simp [importsAt, List.getElem?_eq_getElem h]

private theorem imports_at_outside (docs : List RawOntology) (i : Nat) (h : docs.length ≤ i) :
    importsAt docs i = [] := by
  simp [importsAt, List.getElem?_eq_none h]

private theorem check_imports_correct (ontologies : alloc.vec.Vec RawOntology) (included : alloc.vec.Vec Bool)
    (sel : Nat → Prop) (flags : ∀ i : Usize, import_closure.included_at included i = .ok (decide (sel i.val)))
    (fits : ontologies.val.length ≤ U32.max + 1) (index : Usize) :
    ∃ r, import_closure.check_imports ontologies included index = .ok r ∧
      match r with
      | none => ∀ i, index.val ≤ i → sel i → ∀ iri ∈ importsAt ontologies.val i, Resolved ontologies.val iri
      | some e => ∃ d iri, index.val ≤ d ∧ sel d ∧
          (∃ p : Nat, (importsAt ontologies.val d)[p]? = some iri ∧ ∀ q < p, ∀ earlier,
            (importsAt ontologies.val d)[q]? = some earlier → Resolved ontologies.val earlier) ∧
          (∀ i, index.val ≤ i → i < d → sel i → ∀ earlier ∈ importsAt ontologies.val i,
            Resolved ontologies.val earlier) ∧
          UnresolvedError ontologies.val d iri e := by
  rw [import_closure.check_imports]
  by_cases more : index.val < ontologies.val.length
  · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨rest, restRun, restCorrect⟩ := check_imports_correct ontologies included sel flags fits next
    by_cases chosen : sel index.val
    · have item := lookup_vec ontologies index more
      obtain ⟨r, run, correct⟩ := unresolved_import_correct ontologies (ontologies.val[index.val]'more).imports
        index 0#usize fits
      cases r with
      | none =>
        refine ⟨rest, by simp [lt_len_iff, more, flags, chosen, alloc.vec.Vec.index_slice_index, item, run,
          advance, restRun], ?_⟩
        have here : ∀ iri ∈ importsAt ontologies.val index.val, Resolved ontologies.val iri := by
          rw [imports_at_get _ _ more]; simpa using correct
        cases rest with
        | none =>
          intro i low sel' iri member
          by_cases first : i = index.val
          · subst first; exact here iri member
          · exact restCorrect i (by omega) sel' iri member
        | some e =>
          obtain ⟨d, iri, low, selD, position, earlier, error⟩ := restCorrect
          refine ⟨d, iri, by omega, selD, position, ?_, error⟩
          intro i iLow iHigh sel' earlierIri member
          by_cases first : i = index.val
          · subst first; exact here earlierIri member
          · exact earlier i (by omega) iHigh sel' earlierIri member
      | some e =>
        refine ⟨some e, by simp [lt_len_iff, more, flags, chosen, alloc.vec.Vec.index_slice_index, item, run], ?_⟩
        obtain ⟨p, iri, _, found, earlier, error⟩ := correct
        refine ⟨index.val, iri, le_refl _, chosen, ⟨p, ?_, ?_⟩, ?_, error⟩
        · rw [imports_at_get _ _ more]; exact found
        · intro q below earlierIri qFound
          rw [imports_at_get _ _ more] at qFound
          exact earlier q earlierIri (by simp) below qFound
        · intro i low high; omega
    · refine ⟨rest, by simp [lt_len_iff, more, flags, chosen, advance, restRun], ?_⟩
      cases rest with
      | none =>
        intro i low sel' iri member
        by_cases first : i = index.val
        · subst first; exact absurd sel' chosen
        · exact restCorrect i (by omega) sel' iri member
      | some e =>
        obtain ⟨d, iri, low, selD, position, earlier, error⟩ := restCorrect
        refine ⟨d, iri, by omega, selD, position, ?_, error⟩
        intro i iLow iHigh sel' earlierIri member
        by_cases first : i = index.val
        · subst first; exact absurd sel' chosen
        · exact earlier i (by omega) iHigh sel' earlierIri member
  · refine ⟨none, by simp [lt_len_iff, more], ?_⟩
    intro i low _ iri member
    rw [imports_at_outside _ _ (by omega)] at member
    simp at member
termination_by ontologies.val.length - index.val
decreasing_by omega

private theorem scope_vec_val (i : Nat) : (scopeVec i).val = scopeOf i := by
  simp [scopeVec]

private theorem check_scopes_correct (ontologies : alloc.vec.Vec RawOntology) (included : alloc.vec.Vec Bool)
    (sel : Nat → Prop) (flags : ∀ i : Usize, import_closure.included_at included i = .ok (decide (sel i.val)))
    (index : Usize) :
    ∃ r, import_closure.check_scopes ontologies included index = .ok r ∧
      match r with
      | none => ∀ i, index.val ≤ i → sel i → ∀ o, ontologies.val[i]? = some o → ScopedOntology (scopeOf i) o
      | some d => index.val ≤ d.val ∧ sel d.val ∧
          (∀ o, ontologies.val[d.val]? = some o → ¬ ScopedOntology (scopeOf d.val) o) ∧
          ∀ i, index.val ≤ i → i < d.val → sel i → ∀ o, ontologies.val[i]? = some o →
            ScopedOntology (scopeOf i) o := by
  rw [import_closure.check_scopes]
  by_cases more : index.val < ontologies.val.length
  · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨rest, restRun, restCorrect⟩ := check_scopes_correct ontologies included sel flags next
    have item := lookup_vec ontologies index more
    have found : ontologies.val[index.val]? = some (ontologies.val[index.val]'more) := List.getElem?_eq_getElem more
    have afterHere : ∀ i, index.val ≤ i → i ≠ index.val → index.val + 1 ≤ i := fun i a b => by omega
    by_cases chosen : sel index.val
    · by_cases inScope : ScopedOntology (scopeOf index.val) (ontologies.val[index.val]'more)
      · refine ⟨rest, by simp [lt_len_iff, more, flags, chosen, Rowl.ImportCatalog.document_scope_correct,
          alloc.vec.Vec.index_slice_index, item, Rowl.AnonymousScopes.scoped_ontology_correct, scope_vec_val,
          inScope, advance, restRun], ?_⟩
        cases rest with
        | none =>
          intro i low sel' o oFound
          by_cases first : i = index.val
          · subst first; rw [found] at oFound; cases oFound; exact inScope
          · exact restCorrect i (by rw [nextIs]; exact afterHere i low first) sel' o oFound
        | some d =>
          obtain ⟨low, selD, notScoped, earlier⟩ := restCorrect
          refine ⟨by omega, selD, notScoped, ?_⟩
          intro i iLow iHigh sel' o oFound
          by_cases first : i = index.val
          · subst first; rw [found] at oFound; cases oFound; exact inScope
          · exact earlier i (by rw [nextIs]; exact afterHere i iLow first) iHigh sel' o oFound
      · refine ⟨some index, by simp [lt_len_iff, more, flags, chosen, Rowl.ImportCatalog.document_scope_correct,
          alloc.vec.Vec.index_slice_index, item, Rowl.AnonymousScopes.scoped_ontology_correct, scope_vec_val,
          inScope], ?_⟩
        refine ⟨le_refl _, chosen, ?_, fun i low high => absurd high (by omega)⟩
        intro o oFound
        rw [found] at oFound
        cases oFound
        exact inScope
    · refine ⟨rest, by simp [lt_len_iff, more, flags, chosen, advance, restRun], ?_⟩
      cases rest with
      | none =>
        intro i low sel' o oFound
        by_cases first : i = index.val
        · subst first; exact absurd sel' chosen
        · exact restCorrect i (by rw [nextIs]; exact afterHere i low first) sel' o oFound
      | some d =>
        obtain ⟨low, selD, notScoped, earlier⟩ := restCorrect
        refine ⟨by omega, selD, notScoped, ?_⟩
        intro i iLow iHigh sel' o oFound
        by_cases first : i = index.val
        · subst first; exact absurd sel' chosen
        · exact earlier i (by rw [nextIs]; exact afterHere i iLow first) iHigh sel' o oFound
  · refine ⟨none, by simp [lt_len_iff, more], ?_⟩
    intro i low _ o oFound
    have : ontologies.val[i]? = none := List.getElem?_eq_none (by omega)
    rw [this] at oFound
    cases oFound
termination_by ontologies.val.length - index.val
decreasing_by omega

/-! ### Moving the records -/

private theorem move_annotations_correct (source : alloc.vec.Vec Annotation) (position : Usize)
    (out : alloc.vec.Vec Annotation) :
    ∃ r, import_closure.move_annotations source position out = .ok r ∧
      (∀ v, r = some v → v.val = out.val ++ source.val.drop position.val) ∧
      (r = none → Usize.max < out.val.length + (source.val.length - position.val)) := by
  rw [import_closure.move_annotations]
  by_cases more : position.val < source.val.length
  · by_cases room : out.val.length < Usize.max
    · obtain ⟨placeholder, placeholderRun⟩ : ∃ a, import_closure.placeholder_annotation = .ok a :=
        ⟨_, rfl⟩
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out (source.val[position.val]'more) room)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := position) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = position.val + 1 := by simpa using nextValue
      obtain ⟨r, run, someCase, noneCase⟩ :=
        move_annotations_correct (source.set position placeholder) next pushed
      refine ⟨r, ?_, ?_, ?_⟩
      · simp [lt_len_iff, more, below_max_iff, room, alloc.vec.Vec.index_mut_usize,
          lookup_vec source position more, placeholderRun, core.mem.replace, push, advance, run]
      · intro v same
        rw [someCase v same, contents, alloc.vec.Vec.set_val_eq, nextIs, List.drop_set]
        simp only [show position.val < position.val + 1 by omega, ↓reduceIte, List.append_assoc,
          List.singleton_append]
        rw [List.drop_eq_getElem_cons more]
      · intro none'
        have := noneCase none'
        rw [contents, alloc.vec.Vec.set_val_eq, nextIs] at this
        simp at this
        omega
    · refine ⟨none, by simp [lt_len_iff, more, below_max_iff, room], by simp, ?_⟩
      intro _
      have := out.property
      omega
  · refine ⟨some out, by simp [lt_len_iff, more], ?_, by simp⟩
    intro v same
    cases same
    simp [List.drop_eq_nil_of_le (show source.val.length ≤ position.val by omega)]
termination_by source.val.length - position.val
decreasing_by
  simp only [alloc.vec.Vec.set_val_eq, List.length_set] at *
  omega

/-- The document and position of every origin. -/
def originPairs (origins : List Origin) : List (Nat × Nat) :=
  origins.map (fun origin => (origin.document.val, origin.position.val))

private theorem move_axioms_correct (source : alloc.vec.Vec AnnotatedAxiom) (position document : Usize)
    (out : alloc.vec.Vec AnnotatedAxiom) (origins : alloc.vec.Vec Origin)
    (same : origins.val.length = out.val.length) :
    ∃ r, import_closure.move_axioms source position document out origins = .ok r ∧
      (∀ a o, r = some (a, o) → a.val = out.val ++ source.val.drop position.val ∧
        originPairs o.val = originPairs origins.val ++
          (List.range' position.val (source.val.length - position.val)).map (fun p => (document.val, p)) ∧
        o.val.length = a.val.length) ∧
      (r = none → Usize.max < out.val.length + (source.val.length - position.val)) := by
  rw [import_closure.move_axioms]
  by_cases more : position.val < source.val.length
  · by_cases room : out.val.length < Usize.max
    · obtain ⟨placeholder, placeholderRun⟩ : ∃ a, import_closure.placeholder_axiom = .ok a := ⟨_, rfl⟩
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out (source.val[position.val]'more) room)
      obtain ⟨pushedOrigins, pushOrigin, originContents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec origins ({ document, position } : Origin) (by omega))
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := position) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = position.val + 1 := by simpa using nextValue
      obtain ⟨r, run, someCase, noneCase⟩ :=
        move_axioms_correct (source.set position placeholder) next document pushed pushedOrigins
          (by rw [contents, originContents]; simp [same])
      refine ⟨r, ?_, ?_, ?_⟩
      · simp [lt_len_iff, more, below_max_iff, room, alloc.vec.Vec.index_mut_usize,
          lookup_vec source position more, placeholderRun, core.mem.replace, push, pushOrigin, advance, run]
      · intro a o same'
        obtain ⟨axiomsValue, originsValue, lengths⟩ := someCase a o same'
        refine ⟨?_, ?_, lengths⟩
        · rw [axiomsValue, contents, alloc.vec.Vec.set_val_eq, nextIs, List.drop_set]
          simp only [show position.val < position.val + 1 by omega, ↓reduceIte, List.append_assoc,
            List.singleton_append]
          rw [List.drop_eq_getElem_cons more]
        · rw [originsValue, originContents, alloc.vec.Vec.set_val_eq, nextIs]
          have count : source.val.length - position.val = (source.val.length - (position.val + 1)) + 1 := by
            omega
          simp [originPairs, count, List.range'_succ]
      · intro none'
        have := noneCase none'
        rw [contents, alloc.vec.Vec.set_val_eq, nextIs] at this
        simp at this
        omega
    · refine ⟨none, by simp [lt_len_iff, more, below_max_iff, room], by simp, ?_⟩
      intro _
      have := out.property
      omega
  · refine ⟨some (out, origins), by simp [lt_len_iff, more], ?_, by simp⟩
    intro a o same'
    cases same'
    refine ⟨?_, ?_, same⟩
    · simp [List.drop_eq_nil_of_le (show source.val.length ≤ position.val by omega)]
    · simp [show source.val.length - position.val = 0 by omega]
termination_by source.val.length - position.val
decreasing_by
  simp only [alloc.vec.Vec.set_val_eq, List.length_set] at *
  omega

private theorem gather_one_correct (document : RawOntology) (index : Usize) (out : Gathered)
    (room : out.documents.val.length < Usize.max) (same : out.origins.val.length = out.axioms.val.length) :
    ∃ r, import_closure.gather_one document index out = .ok r ∧
      (∀ g, r = some g →
        g.documents.val = out.documents.val ++ [index] ∧
        g.annotations.val = out.annotations.val ++ document.annotations.val ∧
        g.axioms.val = out.axioms.val ++ document.axioms.val ∧
        originPairs g.origins.val = originPairs out.origins.val ++
          (List.range document.axioms.val.length).map (fun p => (index.val, p)) ∧
        g.origins.val.length = g.axioms.val.length) ∧
      (r = none → Usize.max < out.annotations.val.length + document.annotations.val.length ∨
        Usize.max < out.axioms.val.length + document.axioms.val.length) := by
  obtain ⟨docs', push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out.documents index room)
  obtain ⟨ra, annRun, annSome, annNone⟩ := move_annotations_correct document.annotations 0#usize out.annotations
  cases ra with
  | none =>
    refine ⟨none, by simp [import_closure.gather_one, push, annRun], by simp, ?_⟩
    intro _
    left
    simpa using annNone rfl
  | some anns =>
    obtain ⟨rx, axRun, axSome, axNone⟩ :=
      move_axioms_correct document.axioms 0#usize index out.axioms out.origins same
    cases rx with
    | none =>
      refine ⟨none, by simp [import_closure.gather_one, push, annRun, axRun], by simp, ?_⟩
      intro _
      right
      simpa using axNone rfl
    | some pair =>
      obtain ⟨axs, origs⟩ := pair
      refine ⟨some ⟨docs', anns, axs, origs⟩, by simp [import_closure.gather_one, push, annRun, axRun], ?_,
        by simp⟩
      intro g same'
      cases same'
      obtain ⟨av, ov, lv⟩ := axSome axs origs rfl
      refine ⟨contents, by simpa using annSome anns rfl, by simpa using av, ?_, lv⟩
      rw [ov]
      simp [List.range_eq_range']

/-- The positions from `index` on, below `n`, that `sel` chooses, in order. -/
noncomputable def chosenFrom (sel : Nat → Prop) (n index : Nat) : List Nat :=
  (List.range' index (n - index)).filter (fun i => decide (sel i))

private theorem chosen_step (sel : Nat → Prop) (n index : Nat) (h : index < n) :
    chosenFrom sel n index = if sel index then index :: chosenFrom sel n (index + 1) else chosenFrom sel n (index + 1) := by
  have count : n - index = (n - (index + 1)) + 1 := by omega
  simp only [chosenFrom, count, List.range'_succ, List.filter_cons]
  by_cases s : sel index <;> simp [s]

private theorem chosen_done (sel : Nat → Prop) (n index : Nat) (h : n ≤ index) : chosenFrom sel n index = [] := by
  simp [chosenFrom, show n - index = 0 by omega]

private theorem mem_chosen (sel : Nat → Prop) (n index i : Nat) :
    i ∈ chosenFrom sel n index ↔ index ≤ i ∧ i < n ∧ sel i := by
  simp only [chosenFrom, List.mem_filter, List.mem_range', decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, s⟩; exact ⟨by omega, by omega, s⟩
  · rintro ⟨low, high, s⟩; exact ⟨⟨i - index, by omega, by omega⟩, s⟩

private theorem flat_congr {α β : Type} (l : List α) (f g : α → List β) (same : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.flatMap_cons]
    rw [same x List.mem_cons_self, ih (fun y member => same y (List.mem_cons_of_mem _ member))]

private theorem axioms_at_set (docs : List RawOntology) (k i : Nat) (x : RawOntology) (h : k ≠ i) :
    axiomsAt (docs.set k x) i = axiomsAt docs i := by
  simp [axiomsAt, List.getElem?_set_ne h]

private theorem annotations_at_set (docs : List RawOntology) (k i : Nat) (x : RawOntology) (h : k ≠ i) :
    annotationsAt (docs.set k x) i = annotationsAt docs i := by
  simp [annotationsAt, List.getElem?_set_ne h]

private theorem axioms_at_get (docs : List RawOntology) (i : Nat) (h : i < docs.length) :
    axiomsAt docs i = (docs[i]'h).axioms.val := by
  simp [axiomsAt, List.getElem?_eq_getElem h]

private theorem annotations_at_get (docs : List RawOntology) (i : Nat) (h : i < docs.length) :
    annotationsAt docs i = (docs[i]'h).annotations.val := by
  simp [annotationsAt, List.getElem?_eq_getElem h]

private theorem gather_correct (ontologies : alloc.vec.Vec RawOntology) (included : alloc.vec.Vec Bool)
    (sel : Nat → Prop) (flags : ∀ i : Usize, import_closure.included_at included i = .ok (decide (sel i.val)))
    (index : Usize) (out : Gathered) (docsRoom : out.documents.val.length ≤ index.val)
    (same : out.origins.val.length = out.axioms.val.length) :
    ∃ r, import_closure.gather ontologies included index out = .ok r ∧
      (∀ g, r = some g →
        g.documents.val.map UScalar.val = out.documents.val.map UScalar.val ++
          chosenFrom sel ontologies.val.length index.val ∧
        g.annotations.val = out.annotations.val ++
          (chosenFrom sel ontologies.val.length index.val).flatMap (annotationsAt ontologies.val) ∧
        g.axioms.val = out.axioms.val ++
          (chosenFrom sel ontologies.val.length index.val).flatMap (axiomsAt ontologies.val) ∧
        originPairs g.origins.val = originPairs out.origins.val ++
          (chosenFrom sel ontologies.val.length index.val).flatMap
            (fun i => (List.range (axiomsAt ontologies.val i).length).map (fun p => (i, p)))) ∧
      (r = none →
        Usize.max < out.annotations.val.length +
          ((chosenFrom sel ontologies.val.length index.val).flatMap (annotationsAt ontologies.val)).length ∨
        Usize.max < out.axioms.val.length +
          ((chosenFrom sel ontologies.val.length index.val).flatMap (axiomsAt ontologies.val)).length) := by
  rw [import_closure.gather]
  by_cases more : index.val < ontologies.val.length
  · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    rw [chosen_step sel _ _ more]
    by_cases chosen : sel index.val
    · simp only [chosen, ↓reduceIte]
      have room : out.documents.val.length < Usize.max := by have := ontologies.property; omega
      have item := lookup_vec ontologies index more
      obtain ⟨r1, oneRun, oneSome, oneNone⟩ := gather_one_correct (ontologies.val[index.val]'more) index out room same
      obtain ⟨emptyDoc, emptyRun⟩ : ∃ e, import_closure.empty_ontology = .ok e := ⟨_, rfl⟩
      have emptyIs : emptyDoc = ⟨.Anonymous, alloc.vec.Vec.new Iri, alloc.vec.Vec.new Annotation,
          alloc.vec.Vec.new AnnotatedAxiom⟩ := by
        simp [import_closure.empty_ontology] at emptyRun; exact emptyRun.symm
      cases r1 with
      | none =>
        refine ⟨none, by simp [lt_len_iff, more, flags, chosen, alloc.vec.Vec.index_mut_usize, item, emptyRun,
          core.mem.replace, oneRun], by simp, ?_⟩
        intro _
        rcases oneNone rfl with over | over
        · left
          simp only [List.flatMap_cons, List.length_append, annotations_at_get _ _ more]
          omega
        · right
          simp only [List.flatMap_cons, List.length_append, axioms_at_get _ _ more]
          omega
      | some g1 =>
        obtain ⟨d1, a1, x1, o1, l1⟩ := oneSome g1 rfl
        let rest := ontologies.set index emptyDoc
        have restLen : rest.val.length = ontologies.val.length := by simp [rest]
        obtain ⟨r, run, someCase, noneCase⟩ := gather_correct rest included sel flags next g1
          (by rw [d1]; simp; omega) l1
        have chosenRest : chosenFrom sel rest.val.length next.val = chosenFrom sel ontologies.val.length (index.val + 1) := by
          rw [restLen, nextIs]
        have axiomsRest : (chosenFrom sel ontologies.val.length (index.val + 1)).flatMap (axiomsAt rest.val) =
            (chosenFrom sel ontologies.val.length (index.val + 1)).flatMap (axiomsAt ontologies.val) := by
          apply flat_congr
          intro i member
          have low := ((mem_chosen _ _ _ _).mp member).1
          simp only [rest, alloc.vec.Vec.set_val_eq]
          exact axioms_at_set _ _ _ _ (by omega)
        have annotationsRest : (chosenFrom sel ontologies.val.length (index.val + 1)).flatMap (annotationsAt rest.val) =
            (chosenFrom sel ontologies.val.length (index.val + 1)).flatMap (annotationsAt ontologies.val) := by
          apply flat_congr
          intro i member
          have low := ((mem_chosen _ _ _ _).mp member).1
          simp only [rest, alloc.vec.Vec.set_val_eq]
          exact annotations_at_set _ _ _ _ (by omega)
        have originsRest : (chosenFrom sel ontologies.val.length (index.val + 1)).flatMap
              (fun i => (List.range (axiomsAt rest.val i).length).map (fun p => (i, p))) =
            (chosenFrom sel ontologies.val.length (index.val + 1)).flatMap
              (fun i => (List.range (axiomsAt ontologies.val i).length).map (fun p => (i, p))) := by
          apply flat_congr
          intro i member
          have low := ((mem_chosen _ _ _ _).mp member).1
          simp only [rest, alloc.vec.Vec.set_val_eq]
          rw [axioms_at_set _ _ _ _ (by omega)]
        refine ⟨r, ?_, ?_, ?_⟩
        · simp [lt_len_iff, more, flags, chosen, alloc.vec.Vec.index_mut_usize, item, emptyRun,
            core.mem.replace, oneRun, advance, run, rest]
        · intro g same'
          obtain ⟨dg, ag, xg, og⟩ := someCase g same'
          rw [chosenRest] at dg ag xg og
          rw [axiomsRest] at xg
          rw [annotationsRest] at ag
          rw [originsRest] at og
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [dg, d1]; simp
          · rw [ag, a1]; simp [List.flatMap_cons, annotations_at_get _ _ more]
          · rw [xg, x1]; simp [List.flatMap_cons, axioms_at_get _ _ more]
          · rw [og, o1]; simp [List.flatMap_cons, axioms_at_get _ _ more]
        · intro none'
          rcases noneCase none' with over | over
          · left
            rw [chosenRest, annotationsRest, a1] at over
            simp only [List.flatMap_cons, List.length_append, annotations_at_get _ _ more] at over ⊢
            omega
          · right
            rw [chosenRest, axiomsRest, x1] at over
            simp only [List.flatMap_cons, List.length_append, axioms_at_get _ _ more] at over ⊢
            omega
    · simp only [chosen, ↓reduceIte]
      obtain ⟨r, run, someCase, noneCase⟩ := gather_correct ontologies included sel flags next out
        (by omega) same
      rw [nextIs] at someCase noneCase
      exact ⟨r, by simp [lt_len_iff, more, flags, chosen, advance, run], someCase, noneCase⟩
  · refine ⟨some out, by simp [lt_len_iff, more], ?_, by simp⟩
    intro g same'
    cases same'
    simp [chosen_done sel ontologies.val.length index.val (by omega)]
termination_by ontologies.val.length - index.val
decreasing_by
  all_goals simp_wf
  all_goals omega

private theorem take_header_correct (ontologies : alloc.vec.Vec RawOntology) (root : Usize)
    (inside : root.val < ontologies.val.length) :
    ∃ v, import_closure.take_header ontologies root =
        .ok (v, (ontologies.val[root.val]'inside).identity, (ontologies.val[root.val]'inside).imports) ∧
      v.val.length = ontologies.val.length ∧
      (∀ i, axiomsAt v.val i = axiomsAt ontologies.val i) ∧
      (∀ i, annotationsAt v.val i = annotationsAt ontologies.val i) := by
  let o := ontologies.val[root.val]'inside
  let first := ontologies.set root { o with identity := .Anonymous }
  have firstLen : first.val.length = ontologies.val.length := by simp [first]
  have inside1 : root.val < first.val.length := by rw [firstLen]; exact inside
  have firstAt : first.val[root.val]'inside1 = { o with identity := .Anonymous } := by simp [first]
  let second := first.set root { o with identity := .Anonymous, imports := alloc.vec.Vec.new Iri }
  refine ⟨second, ?_, by simp [second, firstLen], ?_, ?_⟩
  · have look1 := lookup_vec ontologies root inside
    have look2 := lookup_vec first root inside1
    rw [firstAt] at look2
    simp [import_closure.take_header, alloc.vec.Vec.index_mut_usize, look1, core.mem.replace, first, o]
    simp [second, first, o] at look2 ⊢
    simp [look2]
  · intro i
    by_cases same : root.val = i
    · subst same
      simp [axiomsAt, second, first, o, List.getElem?_set_self, inside]
    · simp [axiomsAt, second, first, List.getElem?_set_ne same]
  · intro i
    by_cases same : root.val = i
    · subst same
      simp [annotationsAt, second, first, o, List.getElem?_set_self, inside]
    · simp [annotationsAt, second, first, List.getElem?_set_ne same]

/-! ### The whole assembly -/

private theorem closure_documents_chosen (docs : List RawOntology) (root : Nat) :
    chosenFrom (fun i => i < docs.length ∧ InClosure docs root i) docs.length 0 = ClosureDocuments docs root := by
  unfold chosenFrom ClosureDocuments
  rw [Nat.sub_zero, ← List.range_eq_range']
  apply List.filter_congr
  intro i member
  have inside := List.mem_range.mp member
  simp [inside]

private theorem finish_correct (ontologies : alloc.vec.Vec RawOntology) (included : alloc.vec.Vec Bool)
    (root : Usize) (inside : root.val < ontologies.val.length) (fits : ontologies.val.length ≤ U32.max)
    (flags : ∀ i : Usize, import_closure.included_at included i =
      .ok (decide (i.val < ontologies.val.length ∧ InClosure ontologies.val root.val i.val))) :
    ∃ r, import_closure.finish ontologies included root = .ok r ∧ AssembleCorrect ontologies.val root.val r := by
  let sel := fun i => i < ontologies.val.length ∧ InClosure ontologies.val root.val i
  have fits' : ontologies.val.length ≤ U32.max + 1 := by omega
  have selIff : ∀ i, InClosure ontologies.val root.val i → sel i :=
    fun i closure => ⟨closure_inside _ _ _ inside closure, closure⟩
  have selFlags : ∀ i : Usize, import_closure.included_at included i =
      .ok (@decide (sel i.val) (Classical.propDecidable _)) := by
    intro i
    rw [flags i]
    congr 1
    exact decide_eq_decide.mpr Iff.rfl
  have zero : (0#usize : Usize).val = 0 := by simp
  rw [import_closure.finish]
  obtain ⟨ri, importsRun, importsCorrect⟩ := check_imports_correct ontologies included sel selFlags fits' 0#usize
  cases ri with
  | some e =>
    refine ⟨.Err e, by simp [importsRun], ?_⟩
    obtain ⟨d, iri, _, selD, position, earlier, error⟩ := importsCorrect
    have first : FirstUnresolved ontologies.val root.val d iri := by
      refine ⟨selD.2, unresolved_error_not _ _ _ _ error, position, ?_⟩
      intro i below closure earlierIri member
      exact earlier i (by simp) below (selIff i closure) earlierIri member
    cases e with
    | MissingImport document i =>
      obtain ⟨same, rfl, missing⟩ := error
      rw [← same] at first
      exact ⟨inside, fits, first, missing⟩
    | AmbiguousImport document i a b =>
      obtain ⟨same, rfl, order, na, nb⟩ := error
      rw [← same] at first
      exact ⟨inside, fits, first, order, na, nb⟩
    | _ => exact error.elim
  | none =>
    have resolved : ImportsResolved ontologies.val root.val := by
      intro i closure iri member
      exact importsCorrect i (by simp) (selIff i closure) iri member
    obtain ⟨rs, scopesRun, scopesCorrect⟩ := check_scopes_correct ontologies included sel selFlags 0#usize
    cases rs with
    | some d =>
      refine ⟨.Err (.OutOfScope d), by simp [importsRun, scopesRun], ?_⟩
      obtain ⟨_, selD, notScoped, earlier⟩ := scopesCorrect
      refine ⟨inside, fits, resolved, selD.2, notScoped, ?_⟩
      intro i below closure o found
      exact earlier i (by simp) below (selIff i closure) o found
    | none =>
      have inScope : ClosureScoped ontologies.val root.val := by
        intro i closure o found
        exact scopesCorrect i (by simp) (selIff i closure) o found
      obtain ⟨headless, headerRun, headerLen, headerAxioms, headerAnnotations⟩ :=
        take_header_correct ontologies root inside
      have headlessFlags : ∀ i : Usize, import_closure.included_at included i =
          .ok (@decide ((fun i => i < headless.val.length ∧ InClosure ontologies.val root.val i) i.val)
            (Classical.propDecidable _)) := by
        intro i
        rw [flags i]
        congr 1
        exact decide_eq_decide.mpr (by rw [headerLen])
      obtain ⟨rg, gatherRun, gatherSome, gatherNone⟩ := gather_correct headless included
        (fun i => i < headless.val.length ∧ InClosure ontologies.val root.val i) headlessFlags 0#usize
        ⟨alloc.vec.Vec.new Usize, alloc.vec.Vec.new Annotation, alloc.vec.Vec.new AnnotatedAxiom,
          alloc.vec.Vec.new Origin⟩ (by simp) (by simp)
      have chosenIs : chosenFrom (fun i => i < headless.val.length ∧ InClosure ontologies.val root.val i)
          headless.val.length 0 = ClosureDocuments ontologies.val root.val := by
        rw [headerLen]; exact closure_documents_chosen _ _
      have axiomsIs : ∀ l : List Nat, l.flatMap (axiomsAt headless.val) = l.flatMap (axiomsAt ontologies.val) :=
        fun l => flat_congr _ _ _ (fun i _ => headerAxioms i)
      have annotationsIs : ∀ l : List Nat,
          l.flatMap (annotationsAt headless.val) = l.flatMap (annotationsAt ontologies.val) :=
        fun l => flat_congr _ _ _ (fun i _ => headerAnnotations i)
      have originsIs : ∀ l : List Nat,
          l.flatMap (fun i => (List.range (axiomsAt headless.val i).length).map (fun p => (i, p))) =
          l.flatMap (fun i => (List.range (axiomsAt ontologies.val i).length).map (fun p => (i, p))) :=
        fun l => flat_congr _ _ _ (fun i _ => by rw [headerAxioms i])
      cases rg with
      | none =>
        refine ⟨.Err .TooLarge, by simp [importsRun, scopesRun, headerRun, gatherRun], ?_⟩
        refine ⟨inside, fits, resolved, inScope, ?_⟩
        rcases gatherNone rfl with over | over
        · right
          rw [zero, chosenIs, annotationsIs] at over
          simpa using over
        · left
          rw [zero, chosenIs, axiomsIs] at over
          simpa using over
      | some g =>
        obtain ⟨dg, ag, xg, og⟩ := gatherSome g rfl
        rw [zero, chosenIs] at dg ag xg og
        rw [annotationsIs] at ag
        rw [axiomsIs] at xg
        rw [originsIs] at og
        refine ⟨.Ok ⟨g.documents, ⟨(ontologies.val[root.val]'inside).identity,
            (ontologies.val[root.val]'inside).imports, g.annotations, g.axioms⟩, g.origins⟩,
          by simp [importsRun, scopesRun, headerRun, gatherRun], ?_⟩
        refine ⟨inside, fits, resolved, inScope, ontologies.val[root.val]'inside,
          List.getElem?_eq_getElem inside, ?_, rfl, rfl, ?_, ?_, ?_⟩
        · simpa using dg
        · simpa using ag
        · simpa using xg
        · simpa [originPairs] using og

/-- The positions marked from a resolved closure are exactly the import closure. -/
private theorem marked_iff (docs : List RawOntology) (c closure : imports.DocumentCatalog)
    (built : CatalogOf docs c) (rootKey : U32)
    (resolved : Rowl.Imports.Correct c rootKey (.Complete closure)) (i : Nat) (inside : i < docs.length) :
    Marked closure i ↔ InClosure docs rootKey.val i := by
  obtain ⟨_, _, members⟩ := resolved
  constructor
  · rintro ⟨k, member, rfl⟩
    exact (Rowl.ImportCatalog.catalog_reachable docs c built rootKey k).mp ((members k).mp member)
  · intro closure'
    have small : i < 2 ^ 32 := by
      have := built.1
      simp only [U32.max_eq] at this
      omega
    let k : U32 := ⟨BitVec.ofNat 32 i⟩
    have kv : k.val = i := by
      show (BitVec.ofNat 32 i).toNat = i
      rw [BitVec.toNat_ofNat]
      omega
    exact ⟨k, (members k).mpr ((Rowl.ImportCatalog.catalog_reachable docs c built rootKey k).mpr
      (by rw [kv]; exact closure')), kv⟩

/-- `assemble` always returns, and returns exactly what `AssembleCorrect` says:
    the closure of the import closure of the root, or the first reason why
    there is none. -/
theorem assemble_correct (ontologies : alloc.vec.Vec RawOntology) (root : Usize) :
    ∃ r, import_closure.assemble ontologies root = .ok r ∧ AssembleCorrect ontologies.val root.val r := by
  rw [import_closure.assemble]
  by_cases inside : root.val < ontologies.val.length
  · obtain ⟨built?, catalogRun, noneIff, catalogOf⟩ := Rowl.ImportCatalog.catalog_correct ontologies
    cases built? with
    | none =>
      exact ⟨.Err .TooManyDocuments, by simp [lt_len_iff, inside, catalogRun], inside, noneIff.mp rfl⟩
    | some c =>
      have built := catalogOf c rfl
      have fits := built.1
      have rootValue : (UScalar.cast .U32 root).val = root.val := by
        apply UScalar.cast_val_mod_pow_of_inBounds_eq
        simp only [U32.max_eq] at fits
        simp
        omega
      have complete : ∃ closure, imports.resolve (UScalar.cast .U32 root) c = .ok (.Complete closure) := by
        apply (Rowl.Imports.resolve_complete_iff _ c).mpr
        refine ⟨Rowl.ImportCatalog.catalog_keys_nodup ontologies.val c built, ?_⟩
        intro key reach
        have closure := (Rowl.ImportCatalog.catalog_reachable ontologies.val c built _ key).mp reach
        rw [rootValue] at closure
        have keyInside := closure_inside _ _ _ inside closure
        have keyed : key.val ∈ (keys c).map UScalar.val := by
          rw [built.2.1]; exact List.mem_range.mpr keyInside
        obtain ⟨k, member, same⟩ := List.mem_map.mp keyed
        have : k = key := UScalar.eq_of_val_eq same
        rw [← this]
        exact member
      obtain ⟨closure, resolvedRun⟩ := complete
      obtain ⟨res, resRun, resCorrect⟩ := Rowl.Imports.resolve_total_correct (UScalar.cast .U32 root) c
      have same := Result.ok_injective (resRun.symm.trans resolvedRun)
      subst same
      obtain ⟨start, included, startRun, markRun, marks⟩ := marks_correct closure (alloc.vec.Vec.len ontologies)
      have flags : ∀ i : Usize, import_closure.included_at included i =
          .ok (decide (i.val < ontologies.val.length ∧ InClosure ontologies.val root.val i.val)) := by
        intro i
        rw [marks i]
        congr 1
        apply decide_eq_decide.mpr
        simp only [alloc.vec.Vec.len_val]
        constructor
        · rintro ⟨inside', marked⟩
          exact ⟨inside', by rw [← rootValue]; exact (marked_iff _ c closure built _ resCorrect _ inside').mp marked⟩
        · rintro ⟨inside', closure'⟩
          exact ⟨inside', (marked_iff _ c closure built _ resCorrect _ inside').mpr (by rw [rootValue]; exact closure')⟩
      obtain ⟨r, finishRun, finishCorrect⟩ := finish_correct ontologies included root inside fits flags
      exact ⟨r, by simp [lt_len_iff, inside, catalogRun, resolvedRun, startRun, markRun, finishRun], finishCorrect⟩
  · exact ⟨.Err .NoRoot, by simp [lt_len_iff, inside], by simp [AssembleCorrect]; omega⟩

/-- What `source_closure` returns: the first unreadable document, or the
    assembled closure of the documents as their verified readers read them. -/
def SourceClosureCorrect (limits : functional_document.DocumentLimits) (sources : List Source) (root : Nat) :
    core.result.Result Closure ClosureError → Prop
  | .Err (.Unread unread) => SourcesCorrect limits sources (.Err unread)
  | result => ∃ docs, AllRead limits sources docs ∧ AssembleCorrect docs root result

/-- Whatever `source_closure` returns is right: every document of the catalog
    is read by its verified reader in the scope of its position, and the result
    is the closure of the import closure of the root, or why there is none. -/
theorem source_closure_correct (sources : alloc.vec.Vec Source) (root : Usize)
    (limits : functional_document.DocumentLimits) (result : core.result.Result Closure ClosureError)
    (ran : import_closure.source_closure sources root limits = .ok result) :
    SourceClosureCorrect limits sources.val root.val result := by
  rw [import_closure.source_closure] at ran
  obtain ⟨read, readRun, ran⟩ := bind_eq_ok ran
  have readCorrect := Rowl.ImportCatalog.read_sources_correct sources limits read readRun
  cases read with
  | Ok docs =>
    simp only at ran
    obtain ⟨r, run, correct⟩ := assemble_correct docs root
    have same : r = result := Result.ok_injective (run.symm.trans ran)
    subst same
    cases r with
    | Ok c => exact ⟨docs.val, readCorrect, correct⟩
    | Err e =>
      cases e with
      | Unread u => exact correct.elim
      | _ => exact ⟨docs.val, readCorrect, correct⟩
  | Err unread =>
    simp only at ran
    cases Result.ok_injective ran
    exact readCorrect

/-- A catalog of Functional Syntax documents always gives a result. -/
theorem source_closure_functional_total (sources : alloc.vec.Vec Source) (root : Usize)
    (limits : functional_document.DocumentLimits) (all : ∀ s ∈ sources.val, s.format = .Functional) :
    ∃ result, import_closure.source_closure sources root limits = .ok result := by
  obtain ⟨read, readRun⟩ := Rowl.ImportCatalog.read_sources_functional_total sources limits all
  cases read with
  | Ok docs =>
    obtain ⟨r, run, _⟩ := assemble_correct docs root
    exact ⟨r, by simp [import_closure.source_closure, readRun, run]⟩
  | Err unread => exact ⟨.Err (.Unread unread), by simp [import_closure.source_closure, readRun]⟩

/-! ## Meaning -/

/-- The documents of the closure as axiom lists with the scope of their position. -/
noncomputable def closureParts (docs : List RawOntology) (root : Nat) : List (List U8 × List AnnotatedAxiom) :=
  (ClosureDocuments docs root).map (fun i => (scopeOf i, axiomsAt docs i))

private theorem parts_axioms (docs : List RawOntology) (root : Nat) :
    (closureParts docs root).flatMap Prod.snd = (ClosureDocuments docs root).flatMap (axiomsAt docs) := by
  simp [closureParts, List.flatMap_map]

private theorem parts_scoped (docs : List RawOntology) (root : Nat) (inScope : ClosureScoped docs root) :
    ScopedParts (closureParts docs root) := by
  intro part member item within
  obtain ⟨i, inClosure, rfl⟩ := List.mem_map.mp member
  obtain ⟨_, closure⟩ := (mem_closure_documents docs root i).mp inClosure
  simp only [axiomsAt] at within
  cases found : docs[i]? with
  | none => simp [found] at within
  | some o =>
    simp only [found, Option.map_some, Option.getD_some] at within
    exact ((inScope i closure o found).2 item within).2

private theorem parts_distinct (docs : List RawOntology) (root : Nat) (fits : docs.length ≤ Usize.max) :
    ((closureParts docs root).map Prod.fst).Nodup := by
  have small : ∀ i ∈ ClosureDocuments docs root, i < 256 ^ 8 := by
    intro i member
    have inside := ((mem_closure_documents docs root i).mp member).1
    have bound : Usize.max < 256 ^ 8 := by
      have := Rowl.ImportCatalog.usize_below core.num.Usize.MAX
      simpa [core.num.Usize.MAX] using this
    omega
  simp only [closureParts, List.map_map]
  apply List.Nodup.map_on _ (closure_documents_nodup docs root)
  intro a ma b mb same
  exact Rowl.ImportCatalog.scope_injective a b (small a ma) (small b mb) same

private theorem models_empty_of_missing {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (docs : List RawOntology) (i : Nat) (outside : docs.length ≤ i) : modelsClosure I (axiomsAt docs i) := by
  refine ⟨I.anonymousIndividuals, ?_⟩
  intro item member
  simp [axiomsAt, List.getElem?_eq_none outside] at member

/-- An interpretation is a model of the assembled axioms exactly when it is a
    model of the axioms of every document of the import closure, each with an
    assignment of its anonymous individuals of its own (§2.4, §3.4, §5.6.2). -/
theorem closure_models {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (docs : List RawOntology) (root : Nat) (c : Closure) (fits : docs.length ≤ Usize.max)
    (inScope : ClosureScoped docs root) (assembled : AssembledFrom docs root c) :
    modelsClosure I c.ontology.axioms.val ↔ ∀ i, InClosure docs root i → modelsClosure I (axiomsAt docs i) := by
  obtain ⟨_, _, _, _, _, _, axioms, _⟩ := assembled
  rw [axioms, ← parts_axioms, models_parts I _ (parts_scoped docs root inScope) (parts_distinct docs root fits)]
  constructor
  · intro each i closure
    by_cases inside : i < docs.length
    · exact each (scopeOf i, axiomsAt docs i)
        (List.mem_map.mpr ⟨i, (mem_closure_documents docs root i).mpr ⟨inside, closure⟩, rfl⟩)
    · exact models_empty_of_missing I docs i (by omega)
  · intro each part member
    obtain ⟨i, inClosure, rfl⟩ := List.mem_map.mp member
    exact each i ((mem_closure_documents docs root i).mp inClosure).2

/-- §2.4 with §3.4: a model of the import closure of `root` — an interpretation
    for the datatype map and vocabulary that is a model of the axioms of every
    document of the closure, each document's anonymous individuals interpreted
    on their own. -/
def ImportClosureModel {Object : Type u} {Value : Type v} {Native : Type w} (D : DatatypeMap Native)
    (embed : ValueEmbedding D Value) (V : Vocabulary) (I : Interpretation Object Value)
    (docs : List RawOntology) (root : Nat) : Prop :=
  IsVocabulary D V ∧ IsInterpretation D embed V I ∧ ∀ i, InClosure docs root i → modelsClosure I (axiomsAt docs i)

/-- The models of the assembled axioms are exactly the models of the import closure. -/
theorem closure_model_iff {Object : Type u} {Value : Type v} {Native : Type w} (D : DatatypeMap Native)
    (embed : ValueEmbedding D Value) (V : Vocabulary) (I : Interpretation Object Value)
    (docs : List RawOntology) (root : Nat) (c : Closure) (fits : docs.length ≤ Usize.max)
    (inScope : ClosureScoped docs root) (assembled : AssembledFrom docs root c) :
    Model D embed V I c.ontology.axioms.val ↔ ImportClosureModel D embed V I docs root := by
  simp only [Model, ImportClosureModel, closure_models I docs root c fits inScope assembled]

/-- The assembled axioms are consistent exactly when the import closure has a model. -/
theorem closure_consistent_iff {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (docs : List RawOntology) (root : Nat) (c : Closure) (fits : docs.length ≤ Usize.max)
    (inScope : ClosureScoped docs root) (assembled : AssembledFrom docs root c) :
    Consistent.{u, v, w} D V c.ontology.axioms.val ↔
      ∃ (Object : Type u) (Value : Type v) (embed : ValueEmbedding D Value) (I : Interpretation Object Value),
        ImportClosureModel D embed V I docs root := by
  simp only [Consistent, closure_model_iff D _ V _ docs root c fits inScope assembled]

/-- The assembled axioms entail exactly what every model of the import closure satisfies. -/
theorem closure_entails_iff {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (docs : List RawOntology) (root : Nat) (c : Closure) (fits : docs.length ≤ Usize.max)
    (inScope : ClosureScoped docs root) (assembled : AssembledFrom docs root c) (target : Rowl.Owl.AxiomClosure) :
    Entails.{u, v, w} D V c.ontology.axioms.val target ↔
      ∀ (Object : Type u) (Value : Type v) (embed : ValueEmbedding D Value) (I : Interpretation Object Value),
        ImportClosureModel D embed V I docs root → Model D embed V I target := by
  simp only [Entails, closure_model_iff D _ V _ docs root c fits inScope assembled]

/-- A class is satisfiable in the assembled axioms exactly when some model of the import closure has an instance. -/
theorem closure_satisfiable_iff {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (docs : List RawOntology) (root : Nat) (c : Closure) (fits : docs.length ≤ Usize.max)
    (inScope : ClosureScoped docs root) (assembled : AssembledFrom docs root c) (e : ClassExpression) :
    ClassSatisfiable.{u, v, w} D V c.ontology.axioms.val e ↔
      ∃ (Object : Type u) (Value : Type v) (embed : ValueEmbedding D Value) (I : Interpretation Object Value),
        ImportClosureModel D embed V I docs root ∧ ∃ x, classDenote I e x := by
  simp only [ClassSatisfiable, closure_model_iff D _ V _ docs root c fits inScope assembled]

/-- Subsumption in the assembled axioms is subsumption in every model of the import closure. -/
theorem closure_subsumed_iff {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (docs : List RawOntology) (root : Nat) (c : Closure) (fits : docs.length ≤ Usize.max)
    (inScope : ClosureScoped docs root) (assembled : AssembledFrom docs root c) (sub sup : ClassExpression) :
    Subsumed.{u, v, w} D V c.ontology.axioms.val sub sup ↔
      ∀ (Object : Type u) (Value : Type v) (embed : ValueEmbedding D Value) (I : Interpretation Object Value),
        ImportClosureModel D embed V I docs root → ∀ x, classDenote I sub x → classDenote I sup x := by
  simp only [Subsumed, closure_model_iff D _ V _ docs root c fits inScope assembled]

/-- Instance checking in the assembled axioms is instance checking in every model of the import closure. -/
theorem closure_instance_iff {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (docs : List RawOntology) (root : Nat) (c : Closure) (fits : docs.length ≤ Usize.max)
    (inScope : ClosureScoped docs root) (assembled : AssembledFrom docs root c) (a : NamedIndividual)
    (e : ClassExpression) :
    InstanceOf.{u, v, w} D V c.ontology.axioms.val a e ↔
      ∀ (Object : Type u) (Value : Type v) (embed : ValueEmbedding D Value) (I : Interpretation Object Value),
        ImportClosureModel D embed V I docs root → classDenote I e (I.namedIndividuals a) := by
  simp only [InstanceOf, closure_model_iff D _ V _ docs root c fits inScope assembled]

/-! ## Provenance -/

private theorem flat_origins {α : Type} (l : List Nat) (f : Nat → List α) :
    ∀ (k : Nat) (ip : Nat × Nat),
      (l.flatMap (fun i => (List.range (f i).length).map (fun p => (i, p))))[k]? = some ip →
      ip.1 ∈ l ∧ (l.flatMap f)[k]? = (f ip.1)[ip.2]? := by
  induction l with
  | nil => intro k ip found; simp at found
  | cons i rest ih =>
    intro k ip found
    simp only [List.flatMap_cons] at found ⊢
    by_cases head : k < (f i).length
    · rw [List.getElem?_append_left (by simpa using head)] at found
      rw [List.getElem?_append_left head]
      simp [head] at found
      obtain rfl := found.symm
      exact ⟨List.mem_cons_self, rfl⟩
    · rw [List.getElem?_append_right (by simp; omega)] at found
      rw [List.getElem?_append_right (by omega)]
      simp only [List.length_map, List.length_range] at found
      obtain ⟨member, same⟩ := ih (k - (f i).length) ip found
      exact ⟨List.mem_cons_of_mem _ member, same⟩

/-- Every axiom of the closure is the axiom at its origin: its document is in
    the import closure and has the axiom at the recorded position. -/
theorem closure_provenance (docs : List RawOntology) (root : Nat) (c : Closure)
    (assembled : AssembledFrom docs root c) (k : Nat) (h : k < c.ontology.axioms.val.length) :
    ∃ origin, c.origins.val[k]? = some origin ∧ InClosure docs root origin.document.val ∧
      (axiomsAt docs origin.document.val)[origin.position.val]? = some c.ontology.axioms.val[k] := by
  obtain ⟨_, _, _, _, _, _, axioms, origins⟩ := assembled
  have lengths : c.origins.val.length = c.ontology.axioms.val.length := by
    have := congrArg List.length origins
    simp only [List.length_map] at this
    rw [this, axioms, List.length_flatMap, List.length_flatMap]
    simp
  have inside : k < c.origins.val.length := by omega
  refine ⟨c.origins.val[k], List.getElem?_eq_getElem inside, ?_⟩
  have found : (c.origins.val.map (fun origin => (origin.document.val, origin.position.val)))[k]? =
      some (c.origins.val[k].document.val, c.origins.val[k].position.val) := by
    simp [List.getElem?_eq_getElem inside]
  rw [origins] at found
  obtain ⟨member, same⟩ := flat_origins _ (axiomsAt docs) k _ found
  refine ⟨((mem_closure_documents docs root _).mp member).2, ?_⟩
  rw [← same, ← axioms]
  exact List.getElem?_eq_getElem h

/-- From the bytes: whenever `source_closure` assembles a closure, its documents
    are read by their verified readers, every import IRI of the import closure
    names exactly one document, and an interpretation is a model of the
    assembled axioms exactly when it is a model of the axioms of every document
    of the import closure, each with its own anonymous individuals. -/
theorem source_closure_models (sources : alloc.vec.Vec Source) (root : Usize)
    (limits : functional_document.DocumentLimits) (c : Closure)
    (ran : import_closure.source_closure sources root limits = .ok (.Ok c)) :
    ∃ docs, AllRead limits sources.val docs ∧ ImportsResolved docs root.val ∧ ClosureScoped docs root.val ∧
      AssembledFrom docs root.val c ∧
      ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value),
        modelsClosure I c.ontology.axioms.val ↔ ∀ i, InClosure docs root.val i → modelsClosure I (axiomsAt docs i) := by
  obtain ⟨docs, read, inside, fits, resolved, inScope, assembled⟩ := source_closure_correct sources root limits _ ran
  have small : docs.length ≤ Usize.max := by
    have := Rowl.ImportCatalog.usize_below core.num.Usize.MAX
    simp only [U32.max_eq] at fits
    have bound : (4294967295 : Nat) ≤ Usize.max := by scalar_tac
    omega
  exact ⟨docs, read, resolved, inScope, assembled, fun I => closure_models I docs root.val c small inScope assembled⟩

end Rowl.ImportClosure
