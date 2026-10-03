import Rowl.Hierarchy

/-!
The concept table of the completion graph tableau: every concept is interned
once, as an entry whose parts are the indices of earlier entries. Interning is
proved exact: entries are only appended, every part comes before its entry
(`WellFormed`), the table rebuilds every interned concept (`meaning`), and every
maximum restriction records the complement of its filler (`Complements`).
Closing the table adds `∀t.d` for every universal restriction `∀q.d` and every
transitive role `t` included in `q`, the restrictions that the tableau passes
along transitive roles.
-/
namespace Rowl.ConceptTable
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Concepts (copy_role_identity same_role_correct copy_concept_identity negate_correct)
open Rowl.Hierarchy (Below Closed transitives below_correct)
open Rowl.Tableau (class_eq_iff)
open Rowl.Nnf (copy_iri_identity)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- The indices of an entry's parts. -/
def parts : concept_table.Entry → List Nat
  | .And a b => [a.val,b.val]
  | .Or a b => [a.val,b.val]
  | .Exists _ c => [c.val]
  | .Forall _ c => [c.val]
  | .AtLeast _ _ c => [c.val]
  | .AtMost _ _ c d => [c.val,d.val]
  | _ => []

/-- Every entry's parts come before it. -/
def WellFormed (entries : List concept_table.Entry) : Prop :=
  ∀ i e, entries[i]? = some e → ∀ p ∈ parts e, p < i

/-- The concept an index stands for, rebuilt from the table; an index out of
    range, or with a part that does not come before it, reads as the top
    concept. -/
def meaning (entries : List concept_table.Entry) (i : Nat) : concepts.Concept :=
  match entries[i]? with
  | some .Top => .Top
  | some .Bottom => .Bottom
  | some (.Atom c) => .Atom c
  | some (.NotAtom c) => .NotAtom c
  | some (.One a) => .One a
  | some (.NotOne a) => .NotOne a
  | some (.And a b) =>
    if _first : a.val < i then
      if _second : b.val < i then .And (meaning entries a.val) (meaning entries b.val) else .Top
    else .Top
  | some (.Or a b) =>
    if _first : a.val < i then
      if _second : b.val < i then .Or (meaning entries a.val) (meaning entries b.val) else .Top
    else .Top
  | some (.Exists r c) => if _inner : c.val < i then .Exists r (meaning entries c.val) else .Top
  | some (.Forall r c) => if _inner : c.val < i then .Forall r (meaning entries c.val) else .Top
  | some (.AtLeast n r c) => if _inner : c.val < i then .AtLeast n r (meaning entries c.val) else .Top
  | some (.AtMost n r c _) => if _inner : c.val < i then .AtMost n r (meaning entries c.val) else .Top
  | none => .Top
termination_by i

/-- The concept of an entry, with its parts rebuilt from the table. -/
def rebuild (entries : List concept_table.Entry) : concept_table.Entry → concepts.Concept
  | .Top => .Top
  | .Bottom => .Bottom
  | .Atom c => .Atom c
  | .NotAtom c => .NotAtom c
  | .One a => .One a
  | .NotOne a => .NotOne a
  | .And a b => .And (meaning entries a.val) (meaning entries b.val)
  | .Or a b => .Or (meaning entries a.val) (meaning entries b.val)
  | .Exists r c => .Exists r (meaning entries c.val)
  | .Forall r c => .Forall r (meaning entries c.val)
  | .AtLeast n r c => .AtLeast n r (meaning entries c.val)
  | .AtMost n r c _ => .AtMost n r (meaning entries c.val)

/-- In a well-formed table, an index means its entry with the parts rebuilt. -/
theorem meaning_at (entries : List concept_table.Entry) (wf : WellFormed entries) (k : Nat)
    (e : concept_table.Entry) (at_k : entries[k]? = some e) : meaning entries k = rebuild entries e := by
  have below := wf k e at_k
  rw [meaning.eq_def,at_k]
  cases e with
  | And a b =>
    have first : a.val < k := below a.val (by simp [parts])
    have second : b.val < k := below b.val (by simp [parts])
    simp only [dif_pos first,dif_pos second,rebuild]
  | Or a b =>
    have first : a.val < k := below a.val (by simp [parts])
    have second : b.val < k := below b.val (by simp [parts])
    simp only [dif_pos first,dif_pos second,rebuild]
  | Exists r c =>
    have inner : c.val < k := below c.val (by simp [parts])
    simp only [dif_pos inner,rebuild]
  | Forall r c =>
    have inner : c.val < k := below c.val (by simp [parts])
    simp only [dif_pos inner,rebuild]
  | AtLeast n r c =>
    have inner : c.val < k := below c.val (by simp [parts])
    simp only [dif_pos inner,rebuild]
  | AtMost n r c d =>
    have inner : c.val < k := below c.val (by simp [parts])
    simp only [dif_pos inner,rebuild]
  | Top | Bottom | Atom _ | NotAtom _ | One _ | NotOne _ => rfl

/-- Appending entries changes no meaning of a well-formed table. -/
theorem meaning_append (entries more : List concept_table.Entry) (wf : WellFormed entries) :
    ∀ i, i < entries.length → meaning (entries ++ more) i = meaning entries i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro inside
    have same : (entries ++ more)[i]? = entries[i]? := List.getElem?_append_left inside
    rw [meaning.eq_def (entries ++ more) i,meaning.eq_def entries i,same]
    cases entry : entries[i]? with
    | none => rfl
    | some e =>
      have below := wf i e entry
      cases e with
      | And a b =>
        have first : a.val < i := below a.val (by simp [parts])
        have second : b.val < i := below b.val (by simp [parts])
        simp only [dif_pos first,dif_pos second]
        rw [ih a.val first (by omega),ih b.val second (by omega)]
      | Or a b =>
        have first : a.val < i := below a.val (by simp [parts])
        have second : b.val < i := below b.val (by simp [parts])
        simp only [dif_pos first,dif_pos second]
        rw [ih a.val first (by omega),ih b.val second (by omega)]
      | Exists r c =>
        have inner : c.val < i := below c.val (by simp [parts])
        simp only [dif_pos inner]
        rw [ih c.val inner (by omega)]
      | Forall r c =>
        have inner : c.val < i := below c.val (by simp [parts])
        simp only [dif_pos inner]
        rw [ih c.val inner (by omega)]
      | AtLeast n r c =>
        have inner : c.val < i := below c.val (by simp [parts])
        simp only [dif_pos inner]
        rw [ih c.val inner (by omega)]
      | AtMost n r c d =>
        have inner : c.val < i := below c.val (by simp [parts])
        simp only [dif_pos inner]
        rw [ih c.val inner (by omega)]
      | Top | Bottom | Atom _ | NotAtom _ | One _ | NotOne _ => rfl

/-- A well-formed table stays well formed when an entry whose parts all come
    before the end is appended. -/
theorem wellFormed_append (entries : List concept_table.Entry) (wf : WellFormed entries) (e : concept_table.Entry)
    (partsIn : ∀ p ∈ parts e, p < entries.length) : WellFormed (entries ++ [e]) := by
  intro i e' at_i p member
  by_cases inside : i < entries.length
  · rw [List.getElem?_append_left inside] at at_i
    exact wf i e' at_i p member
  · have last : i = entries.length := by
      have := (List.getElem?_eq_some_iff.mp at_i).1
      simp at this; omega
    subst last
    simp at at_i
    subst at_i
    exact partsIn p member

/-- The actual entry comparison decides structural equality. -/
theorem same_entry_correct (a b : concept_table.Entry) : concept_table.same_entry a b = .ok (decide (a = b)) := by
  cases a with
  | Atom k =>
    cases b with
    | Atom k' =>
      rw [concept_table.same_entry,Rowl.Symbols.same_spelling_total_correct]
      have same : (concept_table.Entry.Atom k = .Atom k') ↔ k.iri.spelling.val = k'.iri.spelling.val := by
        rw [concept_table.Entry.Atom.injEq,class_eq_iff]
      simp only [same]
    | _ => rw [concept_table.same_entry]; simp
  | NotAtom k =>
    cases b with
    | NotAtom k' =>
      rw [concept_table.same_entry,Rowl.Symbols.same_spelling_total_correct]
      have same : (concept_table.Entry.NotAtom k = .NotAtom k') ↔ k.iri.spelling.val = k'.iri.spelling.val := by
        rw [concept_table.Entry.NotAtom.injEq,class_eq_iff]
      simp only [same]
    | _ => rw [concept_table.same_entry]; simp
  | One a =>
    cases b with
    | One a' =>
      rw [concept_table.same_entry,Rowl.AssertionEquality.same_individual_value_total_correct]
      simp
    | _ => rw [concept_table.same_entry]; simp
  | NotOne a =>
    cases b with
    | NotOne a' =>
      rw [concept_table.same_entry,Rowl.AssertionEquality.same_individual_value_total_correct]
      simp
    | _ => rw [concept_table.same_entry]; simp
  | And a1 b1 =>
    cases b with
    | And a2 b2 =>
      rw [concept_table.same_entry]
      by_cases first : a1 = a2
      · subst first; simp
      · simp [first]
    | _ => rw [concept_table.same_entry]; simp
  | Or a1 b1 =>
    cases b with
    | Or a2 b2 =>
      rw [concept_table.same_entry]
      by_cases first : a1 = a2
      · subst first; simp
      · simp [first]
    | _ => rw [concept_table.same_entry]; simp
  | Exists r1 c1 =>
    cases b with
    | Exists r2 c2 =>
      rw [concept_table.same_entry]
      by_cases first : c1 = c2
      · subst first; simp [same_role_correct]
      · simp [first]
    | _ => rw [concept_table.same_entry]; simp
  | Forall r1 c1 =>
    cases b with
    | Forall r2 c2 =>
      rw [concept_table.same_entry]
      by_cases first : c1 = c2
      · subst first; simp [same_role_correct]
      · simp [first]
    | _ => rw [concept_table.same_entry]; simp
  | AtLeast n1 r1 c1 =>
    cases b with
    | AtLeast n2 r2 c2 =>
      rw [concept_table.same_entry]
      by_cases bound : n1 = n2
      · subst bound
        by_cases first : c1 = c2
        · subst first; simp [same_role_correct]
        · simp [first]
      · simp [bound]
    | _ => rw [concept_table.same_entry]; simp
  | AtMost n1 r1 c1 d1 =>
    cases b with
    | AtMost n2 r2 c2 d2 =>
      rw [concept_table.same_entry]
      by_cases bound : n1 = n2
      · subst bound
        by_cases first : c1 = c2
        · subst first
          by_cases second : d1 = d2
          · subst second; simp [same_role_correct]
          · simp [second]
        · simp [first]
      · simp [bound]
    | _ => rw [concept_table.same_entry]; simp
  | Top => cases b <;> rw [concept_table.same_entry] <;> simp
  | Bottom => cases b <;> rw [concept_table.same_entry] <;> simp

private theorem position_from_correct (entries : alloc.vec.Vec concept_table.Entry) (entry : concept_table.Entry)
    (index : Usize) :
    ∃ p : Usize, concept_table.position_from entries entry index = .ok p ∧
      (p.val < entries.val.length → entries.val[p.val]? = some entry) ∧
      (¬ p.val < entries.val.length → entry ∉ entries.val.drop index.val) := by
  rw [concept_table.position_from]
  by_cases more : index.val < entries.val.length
  · have lookup : entries.index_usize index = .ok entries.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : entries.val.drop index.val = entries.val[index.val] :: entries.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    by_cases found : entries.val[index.val] = entry
    · refine ⟨index,?_,fun _ => by rw [List.getElem?_eq_getElem more,found],fun outside => absurd more outside⟩
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,same_entry_correct,found,decide_true]
    · obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val+1 := by simpa using indexValue
      obtain ⟨p,run,hit,miss⟩ := position_from_correct entries entry index'
      refine ⟨p,?_,hit,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,same_entry_correct,found,decide_false,Bool.false_eq_true,advance,run]
      · intro outside member
        rw [split] at member
        rcases List.mem_cons.mp member with same | later
        · exact found same.symm
        · exact miss outside (by rw [nextIndex]; exact later)
  · refine ⟨alloc.vec.Vec.len entries,?_,?_,?_⟩
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more]
    · simp
    · intro _
      simp [List.drop_eq_nil_iff.mpr (show entries.val.length ≤ index.val by omega)]
termination_by entries.val.length - index.val
decreasing_by omega

/-- Adding an entry keeps the table or appends the entry, and the result is an
    index of the entry. -/
theorem add_correct (entries : alloc.vec.Vec concept_table.Entry) (entry : concept_table.Entry) :
    ∃ result, concept_table.add entries entry = .ok result ∧ ∀ t k, result = some (t,k) →
      (t.val = entries.val ∨ t.val = entries.val ++ [entry]) ∧ t.val[k.val]? = some entry := by
  obtain ⟨p,run,hit,_⟩ := position_from_correct entries entry 0#usize
  rw [concept_table.add]
  by_cases found : p.val < entries.val.length
  · refine ⟨some (entries,p),?_,?_⟩
    · simp [run,alloc.vec.Vec.len_val,UScalar.lt_equiv,found]
    · intro t k same
      simp only [Option.some.injEq,Prod.mk.injEq] at same
      obtain ⟨rfl,rfl⟩ := same
      exact ⟨.inl rfl,hit found⟩
  · rw [concept_table.push_new]
    by_cases room : entries.val.length < Usize.max
    · obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec entries entry room)
      refine ⟨some (pushed,alloc.vec.Vec.len entries),?_,?_⟩
      · simp [run,alloc.vec.Vec.len_val,UScalar.lt_equiv,found,usize_max_val,room,push]
      · intro t k same
        simp only [Option.some.injEq,Prod.mk.injEq] at same
        obtain ⟨rfl,rfl⟩ := same
        refine ⟨.inr contents,?_⟩
        rw [contents]
        simp
    · refine ⟨none,?_,by simp⟩
      simp [run,alloc.vec.Vec.len_val,UScalar.lt_equiv,found,usize_max_val,room]

/-- Adding to a well-formed table an entry whose parts lie inside it keeps the
    table well formed and appended to, and the index rebuilds the entry. -/
theorem add_wellFormed (entries : alloc.vec.Vec concept_table.Entry) (entry : concept_table.Entry)
    (wf : WellFormed entries.val) (partsIn : ∀ p ∈ parts entry, p < entries.val.length) :
    ∃ result, concept_table.add entries entry = .ok result ∧ ∀ t k, result = some (t,k) →
      WellFormed t.val ∧ (∃ more, t.val = entries.val ++ more) ∧ k.val < t.val.length ∧
        t.val[k.val]? = some entry ∧ meaning t.val k.val = rebuild t.val entry := by
  obtain ⟨result,run,spec⟩ := add_correct entries entry
  refine ⟨result,run,?_⟩
  intro t k same
  obtain ⟨shape,at_k⟩ := spec t k same
  have wf' : WellFormed t.val := by
    rcases shape with same' | appended
    · rw [same']; exact wf
    · rw [appended]; exact wellFormed_append entries.val wf entry partsIn
  refine ⟨wf',?_,(List.getElem?_eq_some_iff.mp at_k).1,at_k,meaning_at t.val wf' k.val entry at_k⟩
  rcases shape with same' | appended
  · exact ⟨[],by simp [same']⟩
  · exact ⟨[entry],appended⟩

/-- Every maximum restriction of the table records the complement of its
    filler: the index that rebuilds the filler's negation. -/
def Complements (entries : List concept_table.Entry) : Prop :=
  ∀ (i : Nat) n r c d, entries[i]? = some (concept_table.Entry.AtMost n r c d) →
    concepts.negate (meaning entries c.val) = .ok (some (meaning entries d.val))

/-- Appending entries keeps the complements of a well-formed table, provided the
    new maximum restrictions record theirs. -/
theorem complements_append (entries more : List concept_table.Entry) (wf : WellFormed entries)
    (old : Complements entries)
    (fresh : ∀ (j : Nat) n r c d, more[j]? = some (concept_table.Entry.AtMost n r c d) →
      concepts.negate (meaning (entries ++ more) c.val) = .ok (some (meaning (entries ++ more) d.val))) :
    Complements (entries ++ more) := by
  intro i n r c d at_i
  by_cases inside : i < entries.length
  · rw [List.getElem?_append_left inside] at at_i
    have below := wf i _ at_i
    have first : c.val < i := below c.val (by simp [parts])
    have second : d.val < i := below d.val (by simp [parts])
    rw [meaning_append entries more wf c.val (by omega),meaning_append entries more wf d.val (by omega)]
    exact old i n r c d at_i
  · rw [List.getElem?_append_right (by omega)] at at_i
    exact fresh _ n r c d at_i

/-- The number of constructors of a concept, ignoring roles and bounds; a
    complement is no larger. -/
def size : concepts.Concept → Nat
  | .And a b | .Or a b => size a + size b + 1
  | .Exists _ c | .Forall _ c | .AtLeast _ _ c | .AtMost _ _ c => size c + 1
  | _ => 1

theorem negate_size (c : concepts.Concept) : ∀ c', concepts.negate c = .ok (some c') → size c' ≤ size c := by
  induction c with
  | Top | Bottom =>
    intro c' run
    rw [concepts.negate] at run
    cases Result.ok_injective run
    simp [size]
  | Atom k | NotAtom k =>
    intro c' run
    rw [concepts.negate] at run
    cases k
    simp only [copy_iri_identity,bind_ok,Result.ok.injEq,Option.some.injEq] at run
    subst run
    simp [size]
  | One a | NotOne a =>
    intro c' run
    rw [concepts.negate] at run
    simp only [Rowl.Concepts.copy_individual_identity,bind_ok,Result.ok.injEq,Option.some.injEq] at run
    subst run
    simp [size]
  | And a b ihA ihB | Or a b ihA ihB =>
    intro c' run
    rw [concepts.negate,concepts.negate_pair] at run
    obtain ⟨ra,runA,_⟩ := negate_correct.{0,0} a
    obtain ⟨rb,runB,_⟩ := negate_correct.{0,0} b
    cases ra with
    | none => simp [runA] at run
    | some a' =>
      cases rb with
      | none => simp [runA,runB] at run
      | some b' =>
        simp only [runA,runB,bind_ok,concepts.join,Bool.false_eq_true,↓reduceIte,Result.ok.injEq,
          Option.some.injEq] at run
        subst run
        have one := ihA a' runA
        have two := ihB b' runB
        simp only [size]
        omega
  | Exists r c ih | Forall r c ih =>
    intro c' run
    rw [concepts.negate] at run
    obtain ⟨rc,runC,_⟩ := negate_correct.{0,0} c
    cases rc with
    | none => simp [runC] at run
    | some inner =>
      simp only [runC,bind_ok,copy_role_identity,Result.ok.injEq,Option.some.injEq] at run
      subst run
      have := ih inner runC
      simp only [size]
      omega
  | AtLeast n r c _ =>
    intro c' run
    rw [concepts.negate] at run
    by_cases zero : n = 0#usize
    · simp only [zero,↓reduceIte,Result.ok.injEq,Option.some.injEq] at run
      subst run
      simp [size]
    · obtain ⟨m,lower,_⟩ := WP.spec_imp_exists (Usize.sub_spec (x := n) (y := 1#usize) (by
        have : n.val ≠ 0 := fun same => zero (UScalar.eq_of_val_eq (by simpa using same))
        scalar_tac))
      simp only [zero,↓reduceIte,lower,bind_ok,copy_role_identity,copy_concept_identity,Result.ok.injEq,
        Option.some.injEq] at run
      subst run
      simp [size]
  | AtMost n r c _ =>
    intro c' run
    rw [concepts.negate] at run
    by_cases less : n < core.num.Usize.MAX
    · obtain ⟨m,higher,_⟩ := WP.spec_imp_exists (Usize.add_spec (x := n) (y := 1#usize) (by
        rw [UScalar.lt_equiv] at less; simp [core.num.Usize.MAX] at less; scalar_tac))
      simp only [less,↓reduceIte,higher,bind_ok,copy_role_identity,copy_concept_identity,Result.ok.injEq,
        Option.some.injEq] at run
      subst run
      simp [size]
    · simp [less] at run

/-- Adding an entry keeps the complements, provided a maximum restriction
    records the complement of its filler. -/
private theorem add_complements (entries : alloc.vec.Vec concept_table.Entry) (entry : concept_table.Entry)
    (wf : WellFormed entries.val) (old : Complements entries.val)
    (fresh : ∀ n r c d, entry = .AtMost n r c d → concepts.negate (meaning (entries.val ++ [entry]) c.val) =
      .ok (some (meaning (entries.val ++ [entry]) d.val)))
    (result : Option (alloc.vec.Vec concept_table.Entry × Usize)) (run : concept_table.add entries entry = .ok result) :
    ∀ t k, result = some (t,k) → Complements t.val := by
  obtain ⟨result',run',spec⟩ := add_correct entries entry
  rw [run] at run'
  cases Result.ok_injective run'
  intro t k same
  rcases (spec t k same).1 with kept | appended
  · rw [kept]; exact old
  · rw [appended]
    refine complements_append entries.val [entry] wf old ?_
    intro j n r c d at_j
    have : j = 0 := by
      have := (List.getElem?_eq_some_iff.mp at_j).1
      simp at this; omega
    subst this
    simp only [List.getElem?_cons_zero,Option.some.injEq] at at_j
    exact fresh n r c d at_j

/-- Interning terminates; when there is room, it appends to a well-formed table,
    keeps it well formed, returns an index that rebuilds the concept exactly,
    and keeps the complements of the table's maximum restrictions. -/
theorem intern_correct (concept : concepts.Concept) (entries : alloc.vec.Vec concept_table.Entry)
    (wf : WellFormed entries.val) :
    ∃ result, concept_table.intern entries concept = .ok result ∧ ∀ t k, result = some (t,k) →
      WellFormed t.val ∧ (∃ more, t.val = entries.val ++ more) ∧ k.val < t.val.length ∧
        meaning t.val k.val = concept ∧ (Complements entries.val → Complements t.val) := by
  -- A leaf: the entry is added as it is.
  have leaf : ∀ (entry : concept_table.Entry), parts entry = [] → (∀ n r c d, entry ≠ .AtMost n r c d) →
      ∃ result, concept_table.add entries entry = .ok result ∧ ∀ t k, result = some (t,k) →
        WellFormed t.val ∧ (∃ more, t.val = entries.val ++ more) ∧ k.val < t.val.length ∧
          meaning t.val k.val = rebuild t.val entry ∧ (Complements entries.val → Complements t.val) := by
    intro entry noParts notMost
    obtain ⟨result,run,spec⟩ := add_wellFormed entries entry wf (by simp [noParts])
    refine ⟨result,run,?_⟩
    intro t k same
    obtain ⟨wf',grows,inside,_,rebuilt⟩ := spec t k same
    exact ⟨wf',grows,inside,rebuilt,fun old => add_complements entries entry wf old
      (fun n r c d isMost => absurd isMost (notMost n r c d)) result run t k same⟩
  cases concept with
  | Top =>
    obtain ⟨result,run,spec⟩ := leaf .Top rfl (by intro n r c d impossible; cases impossible)
    refine ⟨result,by rw [concept_table.intern]; exact run,?_⟩
    intro t k same
    obtain ⟨wf',grows,inside,rebuilt,keeps⟩ := spec t k same
    exact ⟨wf',grows,inside,by rw [rebuilt]; rfl,keeps⟩
  | Bottom =>
    obtain ⟨result,run,spec⟩ := leaf .Bottom rfl (by intro n r c d impossible; cases impossible)
    refine ⟨result,by rw [concept_table.intern]; exact run,?_⟩
    intro t k same
    obtain ⟨wf',grows,inside,rebuilt,keeps⟩ := spec t k same
    exact ⟨wf',grows,inside,by rw [rebuilt]; rfl,keeps⟩
  | Atom c =>
    obtain ⟨result,run,spec⟩ := leaf (.Atom c) rfl (by intro n r c d impossible; cases impossible)
    refine ⟨result,?_,?_⟩
    · cases c
      rw [concept_table.intern]
      simp only [copy_iri_identity,bind_ok]
      exact run
    · intro t k same
      obtain ⟨wf',grows,inside,rebuilt,keeps⟩ := spec t k same
      exact ⟨wf',grows,inside,by rw [rebuilt]; rfl,keeps⟩
  | NotAtom c =>
    obtain ⟨result,run,spec⟩ := leaf (.NotAtom c) rfl (by intro n r c d impossible; cases impossible)
    refine ⟨result,?_,?_⟩
    · cases c
      rw [concept_table.intern]
      simp only [copy_iri_identity,bind_ok]
      exact run
    · intro t k same
      obtain ⟨wf',grows,inside,rebuilt,keeps⟩ := spec t k same
      exact ⟨wf',grows,inside,by rw [rebuilt]; rfl,keeps⟩
  | One a =>
    obtain ⟨result,run,spec⟩ := leaf (.One a) rfl (by intro n r c d impossible; cases impossible)
    refine ⟨result,?_,?_⟩
    · rw [concept_table.intern]
      simp only [Rowl.Concepts.copy_individual_identity,bind_ok]
      exact run
    · intro t k same
      obtain ⟨wf',grows,inside,rebuilt,keeps⟩ := spec t k same
      exact ⟨wf',grows,inside,by rw [rebuilt]; rfl,keeps⟩
  | NotOne a =>
    obtain ⟨result,run,spec⟩ := leaf (.NotOne a) rfl (by intro n r c d impossible; cases impossible)
    refine ⟨result,?_,?_⟩
    · rw [concept_table.intern]
      simp only [Rowl.Concepts.copy_individual_identity,bind_ok]
      exact run
    · intro t k same
      obtain ⟨wf',grows,inside,rebuilt,keeps⟩ := spec t k same
      exact ⟨wf',grows,inside,by rw [rebuilt]; rfl,keeps⟩
  | And a b =>
    rw [concept_table.intern,concept_table.intern_pair]
    obtain ⟨first,firstRun,firstSpec⟩ := intern_correct a entries wf
    cases first with
    | none => exact ⟨none,by simp [firstRun],by simp⟩
    | some pair =>
      obtain ⟨t1,i1⟩ := pair
      obtain ⟨wf1,⟨more1,grows1⟩,inside1,meaning1,keeps1⟩ := firstSpec t1 i1 rfl
      obtain ⟨second,secondRun,secondSpec⟩ := intern_correct b t1 wf1
      cases second with
      | none => exact ⟨none,by simp [firstRun,secondRun],by simp⟩
      | some pair =>
        obtain ⟨t2,i2⟩ := pair
        obtain ⟨wf2,⟨more2,grows2⟩,inside2,meaning2,keeps2⟩ := secondSpec t2 i2 rfl
        have one : ∀ more, meaning (t2.val ++ more) i1.val = a := by
          intro more
          rw [grows2,List.append_assoc,meaning_append t1.val (more2 ++ more) wf1 i1.val inside1,meaning1]
        have two : ∀ more, meaning (t2.val ++ more) i2.val = b := by
          intro more
          rw [meaning_append t2.val more wf2 i2.val inside2,meaning2]
        obtain ⟨result,run,spec⟩ := add_wellFormed t2 (.And i1 i2) wf2
          (by simp only [parts,List.mem_cons,List.not_mem_nil,or_false]; rintro p (rfl | rfl) <;>
              simp only [grows2,List.length_append] at * <;> omega)
        refine ⟨result,by simp [firstRun,secondRun,run],?_⟩
        intro t k same
        obtain ⟨wf',⟨more3,grows3⟩,inside,_,rebuilt⟩ := spec t k same
        refine ⟨wf',⟨more1 ++ more2 ++ more3,by simp [grows3,grows2,grows1]⟩,inside,?_,?_⟩
        · rw [rebuilt,rebuild,grows3,one,two]
        · exact fun old => add_complements t2 _ wf2 (keeps2 (keeps1 old))
            (fun n r c d impossible => by cases impossible) result run t k same
  | Or a b =>
    rw [concept_table.intern,concept_table.intern_pair]
    obtain ⟨first,firstRun,firstSpec⟩ := intern_correct a entries wf
    cases first with
    | none => exact ⟨none,by simp [firstRun],by simp⟩
    | some pair =>
      obtain ⟨t1,i1⟩ := pair
      obtain ⟨wf1,⟨more1,grows1⟩,inside1,meaning1,keeps1⟩ := firstSpec t1 i1 rfl
      obtain ⟨second,secondRun,secondSpec⟩ := intern_correct b t1 wf1
      cases second with
      | none => exact ⟨none,by simp [firstRun,secondRun],by simp⟩
      | some pair =>
        obtain ⟨t2,i2⟩ := pair
        obtain ⟨wf2,⟨more2,grows2⟩,inside2,meaning2,keeps2⟩ := secondSpec t2 i2 rfl
        have one : ∀ more, meaning (t2.val ++ more) i1.val = a := by
          intro more
          rw [grows2,List.append_assoc,meaning_append t1.val (more2 ++ more) wf1 i1.val inside1,meaning1]
        have two : ∀ more, meaning (t2.val ++ more) i2.val = b := by
          intro more
          rw [meaning_append t2.val more wf2 i2.val inside2,meaning2]
        obtain ⟨result,run,spec⟩ := add_wellFormed t2 (.Or i1 i2) wf2
          (by simp only [parts,List.mem_cons,List.not_mem_nil,or_false]; rintro p (rfl | rfl) <;>
              simp only [grows2,List.length_append] at * <;> omega)
        refine ⟨result,by simp [firstRun,secondRun,run],?_⟩
        intro t k same
        obtain ⟨wf',⟨more3,grows3⟩,inside,_,rebuilt⟩ := spec t k same
        refine ⟨wf',⟨more1 ++ more2 ++ more3,by simp [grows3,grows2,grows1]⟩,inside,?_,?_⟩
        · rw [rebuilt,rebuild,grows3,one,two]
        · exact fun old => add_complements t2 _ wf2 (keeps2 (keeps1 old))
            (fun n r c d impossible => by cases impossible) result run t k same
  | Exists r c =>
    rw [concept_table.intern,concept_table.intern_restriction]
    obtain ⟨inner,innerRun,innerSpec⟩ := intern_correct c entries wf
    cases inner with
    | none => exact ⟨none,by simp [innerRun],by simp⟩
    | some pair =>
      obtain ⟨t1,i1⟩ := pair
      obtain ⟨wf1,⟨more1,grows1⟩,inside1,meaning1,keeps1⟩ := innerSpec t1 i1 rfl
      have one : ∀ more, meaning (t1.val ++ more) i1.val = c := by
        intro more
        rw [meaning_append t1.val more wf1 i1.val inside1,meaning1]
      obtain ⟨result,run,spec⟩ := add_wellFormed t1 (.Exists r i1) wf1
        (by simp only [parts,List.mem_cons,List.not_mem_nil,or_false]; rintro p rfl; exact inside1)
      refine ⟨result,by simp [innerRun,copy_role_identity,run],?_⟩
      intro t k same
      obtain ⟨wf',⟨more2,grows2⟩,inside,_,rebuilt⟩ := spec t k same
      refine ⟨wf',⟨more1 ++ more2,by simp [grows2,grows1]⟩,inside,by rw [rebuilt,rebuild,grows2,one],?_⟩
      exact fun old => add_complements t1 _ wf1 (keeps1 old)
        (fun n r c d impossible => by cases impossible) result run t k same
  | Forall r c =>
    rw [concept_table.intern,concept_table.intern_restriction]
    obtain ⟨inner,innerRun,innerSpec⟩ := intern_correct c entries wf
    cases inner with
    | none => exact ⟨none,by simp [innerRun],by simp⟩
    | some pair =>
      obtain ⟨t1,i1⟩ := pair
      obtain ⟨wf1,⟨more1,grows1⟩,inside1,meaning1,keeps1⟩ := innerSpec t1 i1 rfl
      have one : ∀ more, meaning (t1.val ++ more) i1.val = c := by
        intro more
        rw [meaning_append t1.val more wf1 i1.val inside1,meaning1]
      obtain ⟨result,run,spec⟩ := add_wellFormed t1 (.Forall r i1) wf1
        (by simp only [parts,List.mem_cons,List.not_mem_nil,or_false]; rintro p rfl; exact inside1)
      refine ⟨result,by simp [innerRun,copy_role_identity,run],?_⟩
      intro t k same
      obtain ⟨wf',⟨more2,grows2⟩,inside,_,rebuilt⟩ := spec t k same
      refine ⟨wf',⟨more1 ++ more2,by simp [grows2,grows1]⟩,inside,by rw [rebuilt,rebuild,grows2,one],?_⟩
      exact fun old => add_complements t1 _ wf1 (keeps1 old)
        (fun n r c d impossible => by cases impossible) result run t k same
  | AtLeast n r c =>
    rw [concept_table.intern,concept_table.intern_at_least]
    obtain ⟨inner,innerRun,innerSpec⟩ := intern_correct c entries wf
    cases inner with
    | none => exact ⟨none,by simp [innerRun],by simp⟩
    | some pair =>
      obtain ⟨t1,i1⟩ := pair
      obtain ⟨wf1,⟨more1,grows1⟩,inside1,meaning1,keeps1⟩ := innerSpec t1 i1 rfl
      have one : ∀ more, meaning (t1.val ++ more) i1.val = c := by
        intro more
        rw [meaning_append t1.val more wf1 i1.val inside1,meaning1]
      obtain ⟨result,run,spec⟩ := add_wellFormed t1 (.AtLeast n r i1) wf1
        (by simp only [parts,List.mem_cons,List.not_mem_nil,or_false]; rintro p rfl; exact inside1)
      refine ⟨result,by simp [innerRun,copy_role_identity,run],?_⟩
      intro t k same
      obtain ⟨wf',⟨more2,grows2⟩,inside,_,rebuilt⟩ := spec t k same
      refine ⟨wf',⟨more1 ++ more2,by simp [grows2,grows1]⟩,inside,by rw [rebuilt,rebuild,grows2,one],?_⟩
      exact fun old => add_complements t1 _ wf1 (keeps1 old)
        (fun n r c d impossible => by cases impossible) result run t k same
  | AtMost n r c =>
    rw [concept_table.intern,concept_table.intern_at_most]
    obtain ⟨inner,innerRun,innerSpec⟩ := intern_correct c entries wf
    cases inner with
    | none => exact ⟨none,by simp [innerRun],by simp⟩
    | some pair =>
      obtain ⟨t1,i1⟩ := pair
      obtain ⟨wf1,⟨more1,grows1⟩,inside1,meaning1,keeps1⟩ := innerSpec t1 i1 rfl
      obtain ⟨negated,negRun,_⟩ := negate_correct.{0,0} c
      cases negated with
      | none => exact ⟨none,by simp [innerRun,negRun],by simp⟩
      | some c' =>
        have smaller := negate_size c c' negRun
        obtain ⟨other,otherRun,otherSpec⟩ := intern_correct c' t1 wf1
        cases other with
        | none => exact ⟨none,by simp [innerRun,negRun,otherRun],by simp⟩
        | some pair =>
          obtain ⟨t2,i2⟩ := pair
          obtain ⟨wf2,⟨more2,grows2⟩,inside2,meaning2,keeps2⟩ := otherSpec t2 i2 rfl
          have one : ∀ more, meaning (t2.val ++ more) i1.val = c := by
            intro more
            rw [grows2,List.append_assoc,meaning_append t1.val (more2 ++ more) wf1 i1.val inside1,meaning1]
          have two : ∀ more, meaning (t2.val ++ more) i2.val = c' := by
            intro more
            rw [meaning_append t2.val more wf2 i2.val inside2,meaning2]
          obtain ⟨result,run,spec⟩ := add_wellFormed t2 (.AtMost n r i1 i2) wf2
            (by simp only [parts,List.mem_cons,List.not_mem_nil,or_false]; rintro p (rfl | rfl) <;>
                simp only [grows2,List.length_append] at * <;> omega)
          refine ⟨result,by simp [innerRun,negRun,otherRun,copy_role_identity,run],?_⟩
          intro t k same
          obtain ⟨wf',⟨more3,grows3⟩,inside,_,rebuilt⟩ := spec t k same
          refine ⟨wf',⟨more1 ++ more2 ++ more3,by simp [grows3,grows2,grows1]⟩,inside,
            by rw [rebuilt,rebuild,grows3,one],?_⟩
          refine fun old => add_complements t2 _ wf2 (keeps2 (keeps1 old)) ?_ result run t k same
          intro n' r' c'' d'' isMost
          simp only [concept_table.Entry.AtMost.injEq] at isMost
          obtain ⟨_,_,rfl,rfl⟩ := isMost
          rw [one,two]
          exact negRun
termination_by size concept
decreasing_by all_goals simp only [size] at *; omega

/-- The transitive restrictions of `∀sup.filler` that the closure adds: `∀t.filler`
    for every transitive role `t` included in `sup`. -/
def Added (h : hierarchy.RoleHierarchy) (sup : ObjectPropertyExpression) (filler : Usize)
    (e : concept_table.Entry) : Prop :=
  ∃ t ∈ transitives h, Below h t sup ∧ e = .Forall t filler

private theorem transitive_restrictions_correct (h : hierarchy.RoleHierarchy) (sup : ObjectPropertyExpression)
    (filler : Usize) (index : Usize) (entries : alloc.vec.Vec concept_table.Entry) (wf : WellFormed entries.val)
    (fillerIn : filler.val < entries.val.length) :
    ∃ result, concept_table.transitive_restrictions entries h index sup filler = .ok result ∧ ∀ t, result = some t →
      WellFormed t.val ∧ (∃ more, t.val = entries.val ++ more ∧ ∀ e ∈ more, Added h sup filler e) ∧
      ∀ tr ∈ (transitives h).drop index.val, Below h tr sup →
        ∃ j : Nat, t.val[j]? = some (concept_table.Entry.Forall tr filler) := by
  rw [concept_table.transitive_restrictions]
  by_cases more : index.val < h.transitive.val.length
  · have lookup : h.transitive.index_usize index = .ok h.transitive.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : (transitives h).drop index.val = h.transitive.val[index.val] :: (transitives h).drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have listed : h.transitive.val[index.val] ∈ transitives h := List.getElem_mem more
    by_cases included : Below h h.transitive.val[index.val] sup
    · obtain ⟨added,addRun,addSpec⟩ := add_wellFormed entries (.Forall h.transitive.val[index.val] filler) wf
        (by simp only [parts,List.mem_cons,List.not_mem_nil,or_false]; rintro p rfl; exact fillerIn)
      cases added with
      | none =>
        refine ⟨none,?_,by simp⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,below_correct,included,decide_true,copy_role_identity,addRun]
      | some pair =>
        obtain ⟨t1,k1⟩ := pair
        obtain ⟨wf1,⟨more1,grows1⟩,_,at_k1,_⟩ := addSpec t1 k1 rfl
        have fillerIn1 : filler.val < t1.val.length := by rw [grows1]; simp; omega
        obtain ⟨result,run,spec⟩ := transitive_restrictions_correct h sup filler index' t1 wf1 fillerIn1
        refine ⟨result,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,below_correct,included,decide_true,copy_role_identity,addRun,advance]
          exact run
        · intro t same
          obtain ⟨wf',⟨more2,grows2,added2⟩,found⟩ := spec t same
          have more1Added : ∀ e ∈ more1, Added h sup filler e := by
            have shape := (add_correct entries (.Forall h.transitive.val[index.val] filler))
            obtain ⟨r,rRun,rSpec⟩ := shape
            rw [addRun] at rRun
            cases Result.ok_injective rRun
            rcases (rSpec t1 k1 rfl).1 with same' | appended
            · have : more1 = [] := by
                have := grows1.symm.trans same'
                simpa using this
              subst this; simp
            · have : more1 = [.Forall h.transitive.val[index.val] filler] := by
                have := grows1.symm.trans appended
                simpa using this
              subst this
              intro e member
              simp only [List.mem_singleton] at member
              exact ⟨_,listed,included,member⟩
          refine ⟨wf',⟨more1 ++ more2,by simp [grows2,grows1],?_⟩,?_⟩
          · intro e member
            rcases List.mem_append.mp member with first | second
            · exact more1Added e first
            · exact added2 e second
          · intro tr member below
            rw [split] at member
            rcases List.mem_cons.mp member with rfl | later
            · refine ⟨k1.val,?_⟩
              rw [grows2,List.getElem?_append_left (List.getElem?_eq_some_iff.mp at_k1).1,at_k1]
            · exact found tr (by rw [nextIndex]; exact later) below
    · obtain ⟨result,run,spec⟩ := transitive_restrictions_correct h sup filler index' entries wf fillerIn
      refine ⟨result,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,below_correct,included,decide_false,Bool.false_eq_true,advance,run]
      · intro t same
        obtain ⟨wf',grows,found⟩ := spec t same
        refine ⟨wf',grows,?_⟩
        intro tr member below
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · exact absurd below included
        · exact found tr (by rw [nextIndex]; exact later) below
  · refine ⟨some entries,?_,?_⟩
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more]
    · intro t same
      cases same
      refine ⟨wf,⟨[],by simp,by simp⟩,?_⟩
      intro tr member
      have empty : (transitives h).drop index.val = [] :=
        List.drop_eq_nil_iff.mpr (by simp only [transitives]; omega)
      rw [empty] at member
      cases member
termination_by h.transitive.val.length - index.val
decreasing_by all_goals omega

/-- What the closure adds: transitive restrictions of universal restrictions
    among the original entries before `limit`. -/
def FromOriginal (h : hierarchy.RoleHierarchy) (original : List concept_table.Entry) (limit : Nat)
    (e : concept_table.Entry) : Prop :=
  ∃ (i : Nat) (q : ObjectPropertyExpression) (d : Usize), i < limit ∧
    original[i]? = some (concept_table.Entry.Forall q d) ∧ Added h q d e

private theorem close_from_correct (h : hierarchy.RoleHierarchy) (original : List concept_table.Entry)
    (limit : Usize) (index : Usize) (entries : alloc.vec.Vec concept_table.Entry) (wf : WellFormed entries.val)
    (limitIn : limit.val ≤ original.length) (prefixed : ∃ more, entries.val = original ++ more) :
    ∃ result, concept_table.close_from entries h index limit = .ok result ∧ ∀ t, result = some t →
      WellFormed t.val ∧ (∃ more, t.val = entries.val ++ more ∧ ∀ e ∈ more, FromOriginal h original limit.val e) ∧
      ∀ (i : Nat) q d, index.val ≤ i → i < limit.val → original[i]? = some (concept_table.Entry.Forall q d) →
        ∀ tr ∈ transitives h, Below h tr q → ∃ j : Nat, t.val[j]? = some (concept_table.Entry.Forall tr d) := by
  obtain ⟨prefixMore,prefixShape⟩ := prefixed
  by_cases more : index.val < limit.val
  · have inside : index.val < entries.val.length := by rw [prefixShape]; simp; omega
    have lookup : entries.index_usize index = .ok entries.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have atOriginal : entries.val[index.val] = original[index.val]'(by omega) := by
      simp only [prefixShape,List.getElem_append_left (show index.val < original.length by omega)]
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest : ∀ (e : concept_table.Entry), entries.val[index.val] = e → (∀ q d, e ≠ .Forall q d) →
        ∃ result, concept_table.close_from entries h index limit = .ok result ∧ ∀ t, result = some t →
          WellFormed t.val ∧ (∃ more, t.val = entries.val ++ more ∧ ∀ e ∈ more, FromOriginal h original limit.val e) ∧
          ∀ (i : Nat) q d, index.val ≤ i → i < limit.val → original[i]? = some (concept_table.Entry.Forall q d) →
            ∀ tr ∈ transitives h, Below h tr q → ∃ j : Nat, t.val[j]? = some (concept_table.Entry.Forall tr d) := by
      intro e same notUniversal
      obtain ⟨result,run,spec⟩ := close_from_correct h original limit index' entries wf limitIn ⟨prefixMore,prefixShape⟩
      refine ⟨result,?_,?_⟩
      · rw [concept_table.close_from]
        cases e <;> first
          | (exact absurd rfl (notUniversal _ _))
          | simp only [UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.len_val,inside,alloc.vec.Vec.index_slice_index,
              lookup,bind_ok,same,advance,run]
      · intro t sameResult
        obtain ⟨wf',grows,found⟩ := spec t sameResult
        refine ⟨wf',grows,?_⟩
        intro i q d low high at_i tr member below
        by_cases here : i = index.val
        · subst here
          have : entries.val[index.val] = .Forall q d := by
            rw [atOriginal]; exact (List.getElem?_eq_some_iff.mp at_i).2
          rw [same] at this
          exact absurd this (notUniversal q d)
        · exact found i q d (by omega) high at_i tr member below
    cases entry : entries.val[index.val] with
    | Forall q d =>
      have dIn : d.val < entries.val.length := by
        have := wf index.val (.Forall q d) (by rw [List.getElem?_eq_getElem inside,entry])
        have := this d.val (by simp [parts])
        omega
      obtain ⟨added,addedRun,addedSpec⟩ := transitive_restrictions_correct h q d 0#usize entries wf dIn
      cases added with
      | none =>
        refine ⟨none,?_,by simp⟩
        rw [concept_table.close_from]
        simp only [UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.len_val,inside,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,entry,copy_role_identity]
        simp only [uncurry_apply_pair,addedRun,bind_ok]
      | some t1 =>
        obtain ⟨wf1,⟨more1,grows1,added1⟩,found1⟩ := addedSpec t1 rfl
        obtain ⟨result,run,spec⟩ := close_from_correct h original limit index' t1 wf1 limitIn
          ⟨prefixMore ++ more1,by rw [grows1,prefixShape,List.append_assoc]⟩
        refine ⟨result,?_,?_⟩
        · rw [concept_table.close_from]
          simp only [UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.len_val,inside,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,entry,copy_role_identity]
          simp only [uncurry_apply_pair,addedRun,bind_ok,advance,run]
        · intro t sameResult
          obtain ⟨wf',⟨more2,grows2,added2⟩,found⟩ := spec t sameResult
          have universalHere : original[index.val]? = some (.Forall q d) := by
            rw [List.getElem?_eq_getElem (show index.val < original.length by omega),← atOriginal,entry]
          refine ⟨wf',⟨more1 ++ more2,by rw [grows2,grows1,List.append_assoc],?_⟩,?_⟩
          · intro e member
            rcases List.mem_append.mp member with first | second
            · exact ⟨index.val,q,d,more,universalHere,added1 e first⟩
            · exact added2 e second
          · intro i q' d' low high at_i tr member below
            by_cases here : i = index.val
            · subst here
              rw [universalHere] at at_i
              simp only [Option.some.injEq,concept_table.Entry.Forall.injEq] at at_i
              obtain ⟨rfl,rfl⟩ := at_i
              obtain ⟨j,at_j⟩ := found1 tr (by simpa using member) below
              refine ⟨j,?_⟩
              rw [grows2,List.getElem?_append_left (List.getElem?_eq_some_iff.mp at_j).1,at_j]
            · exact found i q' d' (by omega) high at_i tr member below
    | Top => exact rest .Top entry (by intro q d impossible; cases impossible)
    | Bottom => exact rest .Bottom entry (by intro q d impossible; cases impossible)
    | Atom c => exact rest (.Atom c) entry (by intro q d impossible; cases impossible)
    | NotAtom c => exact rest (.NotAtom c) entry (by intro q d impossible; cases impossible)
    | One a => exact rest (.One a) entry (by intro q d impossible; cases impossible)
    | NotOne a => exact rest (.NotOne a) entry (by intro q d impossible; cases impossible)
    | And a b => exact rest (.And a b) entry (by intro q d impossible; cases impossible)
    | Or a b => exact rest (.Or a b) entry (by intro q d impossible; cases impossible)
    | Exists r c => exact rest (.Exists r c) entry (by intro q d impossible; cases impossible)
    | AtLeast n r c => exact rest (.AtLeast n r c) entry (by intro q d impossible; cases impossible)
    | AtMost n r c d' => exact rest (.AtMost n r c d') entry (by intro q d impossible; cases impossible)
  · refine ⟨some entries,?_,?_⟩
    · rw [concept_table.close_from]
      simp [UScalar.lt_equiv,more]
    · intro t same
      cases same
      refine ⟨wf,⟨[],by simp,by simp⟩,?_⟩
      intro i q d low high
      omega
termination_by limit.val - index.val
decreasing_by all_goals omega

/-- The table's closure: with every universal restriction `∀q.d` and every
    transitive role `t` included in `q`, it has `∀t.d`. -/
def TransitiveClosed (h : hierarchy.RoleHierarchy) (entries : List concept_table.Entry) : Prop :=
  ∀ (i : Nat) q d, entries[i]? = some (concept_table.Entry.Forall q d) → ∀ t ∈ transitives h, Below h t q →
    ∃ j : Nat, entries[j]? = some (concept_table.Entry.Forall t d)

/-- Closing a well-formed table terminates; when there is room, it appends only
    transitive restrictions of its universal restrictions, keeps it well formed,
    and makes it transitively closed whenever the hierarchy's inclusions include
    their compositions. -/
theorem close_correct (h : hierarchy.RoleHierarchy) (entries : alloc.vec.Vec concept_table.Entry)
    (wf : WellFormed entries.val) :
    ∃ result, concept_table.close entries h = .ok result ∧ ∀ t, result = some t →
      WellFormed t.val ∧ (∃ more, t.val = entries.val ++ more ∧
        ∀ e ∈ more, FromOriginal h entries.val entries.val.length e) ∧
      ((∀ a b c, Below h a b → Below h b c → Below h a c) → TransitiveClosed h t.val) := by
  obtain ⟨result,run,spec⟩ := close_from_correct h entries.val (alloc.vec.Vec.len entries) 0#usize entries wf
    (by simp) ⟨[],by simp⟩
  refine ⟨result,by rw [concept_table.close]; exact run,?_⟩
  intro t same
  obtain ⟨wf',⟨more,grows,fromOriginal⟩,found⟩ := spec t same
  refine ⟨wf',⟨more,grows,by simpa using fromOriginal⟩,?_⟩
  intro composes i q d at_i tr member below
  by_cases old : i < entries.val.length
  · have original : entries.val[i]? = some (.Forall q d) := by
      rw [grows,List.getElem?_append_left old] at at_i; exact at_i
    exact found i q d (by simp) (by simpa using old) original tr member below
  · have newEntry : more[i - entries.val.length]? = some (.Forall q d) := by
      rw [grows,List.getElem?_append_right (by omega)] at at_i; exact at_i
    obtain ⟨i0,q0,d0,low,at_i0,t0,_,t0q0,shape⟩ :=
      fromOriginal _ (List.mem_of_getElem? newEntry)
    simp only [concept_table.Entry.Forall.injEq] at shape
    obtain ⟨sameRole,sameFiller⟩ := shape
    subst sameRole sameFiller
    exact found i0 q0 d (by simp) (by simpa using low) at_i0 tr member (composes tr q q0 below t0q0)
/-- The actual test decides whether an entry is `∀role.filler`. -/
theorem universal_is_correct (e : concept_table.Entry) (role : ObjectPropertyExpression) (filler : Usize) :
    concept_table.universal_is e role filler = .ok (decide (e = .Forall role filler)) := by
  cases e with
  | Forall other inner =>
    rw [concept_table.universal_is]
    by_cases same : inner = filler
    · subst same; simp [same_role_correct]
    · simp [same]
  | _ => rw [concept_table.universal_is]; simp

/-- The search for `∀role.filler` returns an index of it, or the length of the
    table when no entry from `index` on is `∀role.filler`. -/
theorem universal_from_correct (entries : alloc.vec.Vec concept_table.Entry) (role : ObjectPropertyExpression)
    (filler index : Usize) :
    ∃ p : Usize, concept_table.universal_from entries role filler index = .ok p ∧
      (p.val < entries.val.length → entries.val[p.val]? = some (concept_table.Entry.Forall role filler)) ∧
      (¬ p.val < entries.val.length → concept_table.Entry.Forall role filler ∉ entries.val.drop index.val) := by
  rw [concept_table.universal_from]
  by_cases more : index.val < entries.val.length
  · have lookup : entries.index_usize index = .ok entries.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : entries.val.drop index.val = entries.val[index.val] :: entries.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    by_cases found : entries.val[index.val] = .Forall role filler
    · refine ⟨index,?_,fun _ => by rw [List.getElem?_eq_getElem more,found],fun outside => absurd more outside⟩
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,universal_is_correct,found,decide_true]
    · obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val+1 := by simpa using indexValue
      obtain ⟨p,run,hit,miss⟩ := universal_from_correct entries role filler index'
      refine ⟨p,?_,hit,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,universal_is_correct,found,decide_false,Bool.false_eq_true,advance,run]
      · intro outside member
        rw [split] at member
        rcases List.mem_cons.mp member with same | later
        · exact found same.symm
        · exact miss outside (by rw [nextIndex]; exact later)
  · refine ⟨alloc.vec.Vec.len entries,?_,?_,?_⟩
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more]
    · simp
    · intro _
      simp [List.drop_eq_nil_iff.mpr (show entries.val.length ≤ index.val by omega)]
termination_by entries.val.length - index.val
decreasing_by omega

/-- In a transitively closed table, the search finds `∀t.d` for every universal
    restriction `∀q.d` and every transitive role `t` included in `q`. -/
theorem universal_found (h : hierarchy.RoleHierarchy) (entries : alloc.vec.Vec concept_table.Entry)
    (closed : TransitiveClosed h entries.val) (i : Nat) (q : ObjectPropertyExpression) (d : Usize)
    (at_i : entries.val[i]? = some (.Forall q d)) (t : ObjectPropertyExpression) (transitive : t ∈ transitives h)
    (below : Below h t q) :
    ∃ p : Usize, concept_table.universal_from entries t d 0#usize = .ok p ∧
      entries.val[p.val]? = some (.Forall t d) := by
  obtain ⟨p,run,hit,miss⟩ := universal_from_correct entries t d 0#usize
  refine ⟨p,run,?_⟩
  by_cases inside : p.val < entries.val.length
  · exact hit inside
  · obtain ⟨j,at_j⟩ := closed i q d at_i t transitive below
    exact absurd (by simpa using List.mem_of_getElem? at_j) (miss inside)
end Rowl.ConceptTable
