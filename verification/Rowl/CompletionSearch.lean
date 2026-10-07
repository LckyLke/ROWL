import Rowl.ConceptTable

/-!
The rule search of the completion graph tableau, proved exact against
independent predicates on its lists. A label satisfies an entry (`Holds`)
when conjunctions and disjunctions hold propositionally and every other entry
is listed; a literal clashes with a label when its complement is listed; and
each search returns a missing item exactly when there is one, or the first
unblocked node with an unwitnessed existential restriction. Blocking is
equality blocking: a tree node is blocked when two tree nodes on its path to its
named root have the same label.
-/
namespace Rowl.CompletionSearch
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Concepts (inv inv_inv same_role_correct copy_role_identity inverse_correct)
open Rowl.Hierarchy (Below below_correct transitives)
open Rowl.Tableau (class_eq_iff)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-- A label satisfies an entry: conjunctions and disjunctions are read
    propositionally, and every other entry must be listed. -/
def Holds (entries : List concept_table.Entry) (label : List Usize) (c : Nat) : Prop :=
  match entries[c]? with
  | some .Top => True
  | some .Bottom => False
  | some (.And a b) =>
    if _first : a.val < c then
      if _second : b.val < c then Holds entries label a.val ∧ Holds entries label b.val else False
    else False
  | some (.Or a b) =>
    if _first : a.val < c then
      if _second : b.val < c then Holds entries label a.val ∨ Holds entries label b.val else False
    else False
  | some _ => ∃ i ∈ label, i.val = c
  | none => False
termination_by c

/-- A named class, a nominal or a self restriction and its complement. -/
def Complementary : concept_table.Entry → concept_table.Entry → Prop
  | .Atom x, .NotAtom y => x = y
  | .NotAtom x, .Atom y => x = y
  | .One a, .NotOne b => a = b
  | .NotOne a, .One b => a = b
  | .HasSelf r, .NotSelf s => r = s
  | .NotSelf r, .HasSelf s => r = s
  | _, _ => False

/-- Some listed entry is the complement of entry `item`. -/
def Clashes (entries : List concept_table.Entry) (label : List Usize) (item : Usize) : Prop :=
  ∃ other ∈ label, ∃ e e', entries[item.val]? = some e ∧ entries[other.val]? = some e' ∧ Complementary e e'

/-- The label lists the named class. -/
def HasAtom (entries : List concept_table.Entry) (label : List Usize) (c : Class) : Prop :=
  ∃ i ∈ label, entries[i.val]? = some (.Atom c)

private theorem usize_eq_iff (a b : Usize) : a = b ↔ a.val = b.val := by
  constructor
  · rintro rfl; rfl
  · intro same; exact UScalar.eq_of_val_eq same

theorem contains_correct (label : alloc.vec.Vec Usize) (item index : Usize) :
    completion.contains label item index = .ok (decide (item ∈ label.val.drop index.val)) := by
  rw [completion.contains]
  by_cases more : index.val < label.val.length
  · have lookup : label.index_usize index = .ok label.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : label.val.drop index.val = label.val[index.val] :: label.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := contains_correct label item index'
    rw [nextIndex] at rest
    rw [split]
    by_cases found : label.val[index.val] = item
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,found]
      simp
    · have found' : ¬ item = label.val[index.val] := fun same => found same.symm
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,found,advance,rest,List.mem_cons,found',false_or]
  · have empty : label.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by label.val.length - index.val
decreasing_by omega

/-- Membership of an index in a label, by value. -/
theorem mem_index_iff (label : List Usize) (c : Usize) : c ∈ label ↔ ∃ i ∈ label, i.val = c.val := by
  constructor
  · intro member; exact ⟨c,member,rfl⟩
  · rintro ⟨i,member,same⟩
    rw [← (usize_eq_iff i c).mpr same]; exact member

/-- The actual satisfaction test decides `Holds`. -/
theorem holds_correct (entries : alloc.vec.Vec concept_table.Entry) (label : alloc.vec.Vec Usize) :
    ∀ (n : Nat) (c : Usize), c.val = n →
      completion.holds entries label c = .ok (decide (Holds entries.val label.val c.val)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c same
    rw [completion.holds,Holds.eq_def]
    by_cases inside : c.val < entries.val.length
    · have lookup : entries.index_usize c = .ok entries.val[c.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
      have entry : entries.val[c.val]? = some entries.val[c.val] := List.getElem?_eq_getElem inside
      rw [entry]
      cases e : entries.val[c.val] with
      | Top => simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,e]
      | Bottom => simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,e]
      | Atom k =>
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,e,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero]
        congr 1
        exact decide_eq_decide.mpr (mem_index_iff label.val c)
      | NotAtom k =>
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,e,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero]
        congr 1
        exact decide_eq_decide.mpr (mem_index_iff label.val c)
      | One a =>
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,e,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero]
        congr 1
        exact decide_eq_decide.mpr (mem_index_iff label.val c)
      | NotOne a =>
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,e,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero]
        congr 1
        exact decide_eq_decide.mpr (mem_index_iff label.val c)
      | HasSelf r =>
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,e,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero]
        congr 1
        exact decide_eq_decide.mpr (mem_index_iff label.val c)
      | NotSelf r =>
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,e,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero]
        congr 1
        exact decide_eq_decide.mpr (mem_index_iff label.val c)
      | Exists r d =>
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,e,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero]
        congr 1
        exact decide_eq_decide.mpr (mem_index_iff label.val c)
      | Forall r d =>
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,e,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero]
        congr 1
        exact decide_eq_decide.mpr (mem_index_iff label.val c)
      | AtLeast m r d =>
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,e,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero]
        congr 1
        exact decide_eq_decide.mpr (mem_index_iff label.val c)
      | AtMost m r d d' =>
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,e,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero]
        congr 1
        exact decide_eq_decide.mpr (mem_index_iff label.val c)
      | And a b =>
        by_cases first : a.val < c.val
        · by_cases second : b.val < c.val
          · have left := ih a.val (by omega) a rfl
            have right := ih b.val (by omega) b rfl
            simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookup,bind_ok,e,first,second,dif_pos,left,right]
            by_cases one : Holds entries.val label.val a.val
            · simp [one]
            · simp [one]
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,e,first,second]
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,e,first]
      | Or a b =>
        by_cases first : a.val < c.val
        · by_cases second : b.val < c.val
          · have left := ih a.val (by omega) a rfl
            have right := ih b.val (by omega) b rfl
            simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookup,bind_ok,e,first,second,dif_pos,left,right]
            by_cases one : Holds entries.val label.val a.val
            · simp [one]
            · simp [one]
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,e,first,second]
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,e,first]
    · have none : entries.val[c.val]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,none]

theorem complementary_correct (a b : concept_table.Entry) :
    completion.complementary a b = .ok (decide (Complementary a b)) := by
  cases a with
  | Atom x =>
    cases b with
    | NotAtom y =>
      rw [completion.complementary,Rowl.Symbols.same_spelling_total_correct]
      simp only [Complementary,class_eq_iff]
    | _ => rw [completion.complementary]; simp [Complementary]
  | NotAtom x =>
    cases b with
    | Atom y =>
      rw [completion.complementary,Rowl.Symbols.same_spelling_total_correct]
      simp only [Complementary,class_eq_iff]
    | _ => rw [completion.complementary]; simp [Complementary]
  | One x =>
    cases b with
    | NotOne y =>
      rw [completion.complementary,Rowl.AssertionEquality.same_individual_value_total_correct]
      simp only [Complementary]
      congr 1
    | _ => rw [completion.complementary]; simp [Complementary]
  | NotOne x =>
    cases b with
    | One y =>
      rw [completion.complementary,Rowl.AssertionEquality.same_individual_value_total_correct]
      simp only [Complementary]
      congr 1
    | _ => rw [completion.complementary]; simp [Complementary]
  | HasSelf r =>
    cases b with
    | NotSelf s => rw [completion.complementary]; simp [Complementary,same_role_correct]
    | _ => rw [completion.complementary]; simp [Complementary]
  | NotSelf r =>
    cases b with
    | HasSelf s => rw [completion.complementary]; simp [Complementary,same_role_correct]
    | _ => rw [completion.complementary]; simp [Complementary]
  | _ => rw [completion.complementary]; simp [Complementary]

private theorem clashes_cons (entries : List concept_table.Entry) (head : Usize) (rest : List Usize) (item : Usize)
    (no : ¬ ∃ e e', entries[item.val]? = some e ∧ entries[head.val]? = some e' ∧ Complementary e e') :
    Clashes entries rest item ↔ Clashes entries (head :: rest) item := by
  constructor
  · rintro ⟨other,member,found⟩
    exact ⟨other,List.mem_cons_of_mem _ member,found⟩
  · rintro ⟨other,member,found⟩
    rcases List.mem_cons.mp member with rfl | later
    · exact absurd found no
    · exact ⟨other,later,found⟩

theorem clashes_correct (entries : alloc.vec.Vec concept_table.Entry) (label : alloc.vec.Vec Usize) (item index : Usize) :
    completion.clashes entries label item index =
      .ok (decide (Clashes entries.val (label.val.drop index.val) item)) := by
  rw [completion.clashes]
  by_cases more : index.val < label.val.length
  · have lookup : label.index_usize index = .ok label.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : label.val.drop index.val = label.val[index.val] :: label.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := clashes_correct entries label item index'
    rw [nextIndex] at rest
    by_cases itemIn : item.val < entries.val.length
    · by_cases otherIn : label.val[index.val].val < entries.val.length
      · have one : entries.index_usize item = .ok entries.val[item.val] := by
          simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem itemIn]
        have two : entries.index_usize label.val[index.val] = .ok entries.val[label.val[index.val].val] := by
          simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem otherIn]
        by_cases comp : Complementary entries.val[item.val] entries.val[label.val[index.val].val]
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,itemIn,otherIn,one,two,complementary_correct,comp,decide_true]
          congr 1
          symm
          rw [decide_eq_true_iff]
          refine ⟨label.val[index.val],by rw [split]; exact List.mem_cons_self ..,_,_,
            List.getElem?_eq_getElem itemIn,List.getElem?_eq_getElem otherIn,comp⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,itemIn,otherIn,one,two,complementary_correct,comp,decide_false,Bool.false_eq_true,
            advance,rest]
          congr 1
          rw [decide_eq_decide,split]
          apply clashes_cons
          rintro ⟨e,e',first,second,found⟩
          rw [List.getElem?_eq_getElem itemIn] at first
          rw [List.getElem?_eq_getElem otherIn] at second
          cases first; cases second
          exact comp found
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,itemIn,otherIn,Bool.false_eq_true,advance,rest]
        congr 1
        rw [decide_eq_decide,split]
        apply clashes_cons
        rintro ⟨e,e',_,second,_⟩
        rw [List.getElem?_eq_none_iff.mpr (by omega)] at second
        cases second
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,itemIn,Bool.false_eq_true,advance,rest]
      congr 1
      rw [decide_eq_decide,split]
      apply clashes_cons
      rintro ⟨e,e',first,_,_⟩
      rw [List.getElem?_eq_none_iff.mpr (by omega)] at first
      cases first
  · have empty : label.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty,Clashes]
termination_by label.val.length - index.val
decreasing_by omega

theorem is_atom_correct (e : concept_table.Entry) (c : Class) :
    completion.is_atom e c = .ok (decide (e = .Atom c)) := by
  cases e with
  | Atom k =>
    rw [completion.is_atom,Rowl.Symbols.same_spelling_total_correct]
    simp only [concept_table.Entry.Atom.injEq,class_eq_iff]
  | _ => rw [completion.is_atom]; simp

theorem subset_correct (small large : alloc.vec.Vec Usize) (index : Usize) :
    completion.subset small large index = .ok (decide (∀ i ∈ small.val.drop index.val, i ∈ large.val)) := by
  rw [completion.subset]
  by_cases more : index.val < small.val.length
  · have lookup : small.index_usize index = .ok small.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : small.val.drop index.val = small.val[index.val] :: small.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := subset_correct small large index'
    rw [nextIndex] at rest
    rw [split]
    by_cases found : small.val[index.val] ∈ large.val
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,found,decide_true,advance,
        rest,List.forall_mem_cons,true_and]
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,found,decide_false,
        Bool.false_eq_true,List.forall_mem_cons,false_and]
  · have empty : small.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by small.val.length - index.val
decreasing_by omega

/-- The actual label comparison decides whether two labels list the same items. -/
theorem same_label_correct (left right : alloc.vec.Vec Usize) :
    completion.same_label left right = .ok (decide (∀ i, i ∈ left.val ↔ i ∈ right.val)) := by
  rw [completion.same_label,subset_correct]
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero]
  by_cases first : ∀ i ∈ left.val, i ∈ right.val
  · rw [decide_eq_true first]
    simp only [bind_ok,↓reduceIte,subset_correct,show (0#usize).val = 0 from rfl,List.drop_zero]
    congr 1
    rw [decide_eq_decide]
    constructor
    · intro second i
      exact ⟨first i,second i⟩
    · intro both i member
      exact (both i).mpr member
  · rw [decide_eq_false first]
    simp only [bind_ok,Bool.false_eq_true,↓reduceIte]
    congr 1
    symm
    rw [decide_eq_false_iff_not]
    intro both
    exact first (fun i member => (both i).mp member)
/-- What a node with this label must satisfy: the requirements at the node, the
    TBox concept, and the concept of every unfolding whose class it lists. -/
def NodeNeeds (P : completion.Problem) (label : List Usize) (x : Nat) (c : Usize) : Prop :=
  (∃ q ∈ P.requirements.val, q.node.val = x ∧ q.concept = c) ∨ c = P.axioms ∨
    ∃ u ∈ P.unfoldings.val, HasAtom P.entries.val label u.class ∧ u.concept = c
/-- The label satisfies everything the node needs. -/
def NodeOk (P : completion.Problem) (label : List Usize) (x : Nat) : Prop :=
  ∀ c, NodeNeeds P label x c → Holds P.entries.val label c.val
/-- What a label must satisfy apart from the requirements of individuals: the
    TBox concept and the concept of every unfolding whose class it lists. -/
def LocalNeeds (P : completion.Problem) (label : List Usize) (c : Usize) : Prop :=
  c = P.axioms ∨ ∃ u ∈ P.unfoldings.val, HasAtom P.entries.val label u.class ∧ u.concept = c

/-- For every entry, the listed indices point to exactly the unfoldings whose
    class the entry is. -/
def TriggersFor (entries : List concept_table.Entry) (unfoldings : List completion.Unfolding)
    (triggers : List (alloc.vec.Vec Usize)) : Prop :=
  triggers.length = entries.length ∧
  ∀ i (inside : i < triggers.length) (u : completion.Unfolding),
    (∃ k ∈ triggers[i].val, unfoldings[k.val]? = some u) ↔ (u ∈ unfoldings ∧ entries[i]? = some (.Atom u.class))

/-- The problem's triggers list the unfoldings of every entry. -/
def TriggersOk (P : completion.Problem) : Prop := TriggersFor P.entries.val P.unfoldings.val P.triggers.val

private theorem missing_among_correct (P : completion.Problem) (label listed : alloc.vec.Vec Usize) (index : Usize) :
    ∃ r, completion.missing_among P label listed index = .ok r ∧
      (∀ c, r = some c → (∃ k ∈ listed.val.drop index.val, ∃ u, P.unfoldings.val[k.val]? = some u ∧ u.concept = c) ∧
        ¬ Holds P.entries.val label.val c.val) ∧
      (r = none → ∀ k ∈ listed.val.drop index.val, ∀ u, P.unfoldings.val[k.val]? = some u →
        Holds P.entries.val label.val u.concept.val) := by
  rw [completion.missing_among]
  by_cases more : index.val < listed.val.length
  · have lookup : listed.index_usize index = .ok listed.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : listed.val.drop index.val = listed.val[index.val] :: listed.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := missing_among_correct P label listed index'
    rw [nextIndex] at found absent
    have foundLater : ∀ c, r = some c → (∃ k ∈ listed.val.drop index.val, ∃ u,
        P.unfoldings.val[k.val]? = some u ∧ u.concept = c) ∧ ¬ Holds P.entries.val label.val c.val := by
      intro c same
      obtain ⟨⟨k,member,u,at_k,concept⟩,missing⟩ := found c same
      exact ⟨⟨k,by rw [split]; exact List.mem_cons_of_mem _ member,u,at_k,concept⟩,missing⟩
    by_cases inside : listed.val[index.val].val < P.unfoldings.val.length
    · have lookupU : P.unfoldings.index_usize listed.val[index.val] =
          .ok P.unfoldings.val[listed.val[index.val].val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
      by_cases satisfied : Holds P.entries.val label.val P.unfoldings.val[listed.val[index.val].val].concept.val
      · refine ⟨r,?_,foundLater,?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,inside,lookup,lookupU,
            holds_correct _ _ _ _ rfl,satisfied,advance,run]
        · intro none k member u at_k
          rw [split] at member
          rcases List.mem_cons.mp member with rfl | later
          · rw [List.getElem?_eq_getElem inside] at at_k
            cases Option.some.inj at_k
            exact satisfied
          · exact absent none k later u at_k
      · refine ⟨some P.unfoldings.val[listed.val[index.val].val].concept,?_,?_,by simp⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,inside,lookup,lookupU,
            holds_correct _ _ _ _ rfl,satisfied]
        · intro c same
          cases same
          exact ⟨⟨_,by rw [split]; exact List.mem_cons_self ..,_,List.getElem?_eq_getElem inside,rfl⟩,satisfied⟩
    · refine ⟨r,?_,foundLater,?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,inside,lookup,advance,run]
      · intro none k member u at_k
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · rw [List.getElem?_eq_none (by omega)] at at_k
          cases at_k
        · exact absent none k later u at_k
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ k member
    rw [List.drop_eq_nil_iff.mpr (by omega)] at member
    cases member
termination_by listed.val.length - index.val
decreasing_by omega

/-- The search over the label's items finds an unfolding of one of them that the
    label does not satisfy, or nothing when it satisfies every unfolding whose
    class is listed from `index` on. -/
theorem missing_unfolding_correct (P : completion.Problem) (label : alloc.vec.Vec Usize) (triggers : TriggersOk P)
    (index : Usize) :
    ∃ r, completion.missing_unfolding P label index = .ok r ∧
      (∀ c, r = some c → (∃ u ∈ P.unfoldings.val, HasAtom P.entries.val label.val u.class ∧ u.concept = c) ∧
        ¬ Holds P.entries.val label.val c.val) ∧
      (r = none → ∀ u ∈ P.unfoldings.val, (∃ i ∈ label.val.drop index.val, P.entries.val[i.val]? = some (.Atom u.class)) →
        Holds P.entries.val label.val u.concept.val) := by
  obtain ⟨lengths,lists⟩ := triggers
  rw [completion.missing_unfolding]
  by_cases more : index.val < label.val.length
  · have lookup : label.index_usize index = .ok label.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : label.val.drop index.val = label.val[index.val] :: label.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    have itemListed : label.val[index.val] ∈ label.val := List.getElem_mem more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := missing_unfolding_correct P label ⟨lengths,lists⟩ index'
    rw [nextIndex] at absent
    by_cases itemIn : label.val[index.val].val < P.triggers.val.length
    · have lookupT : P.triggers.index_usize label.val[index.val] = .ok P.triggers.val[label.val[index.val].val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem itemIn]
      obtain ⟨here,hereRun,hereFound,hereAbsent⟩ :=
        missing_among_correct P label P.triggers.val[label.val[index.val].val] 0#usize
      simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at hereFound hereAbsent
      cases here with
      | some c =>
        refine ⟨some c,?_,?_,by simp⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,itemIn,lookup,lookupT,hereRun]
        · intro c' same
          cases same
          obtain ⟨⟨k,member,u,at_k,concept⟩,missing⟩ := hereFound c rfl
          obtain ⟨uIn,atom⟩ := (lists label.val[index.val].val itemIn u).mp ⟨k,member,at_k⟩
          exact ⟨⟨u,uIn,⟨_,itemListed,atom⟩,concept⟩,missing⟩
      | none =>
        refine ⟨r,?_,found,?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,itemIn,lookup,lookupT,hereRun,advance,run]
        · intro none u member ⟨i,iMember,atom⟩
          rw [split] at iMember
          rcases List.mem_cons.mp iMember with rfl | later
          · obtain ⟨k,kMember,at_k⟩ := (lists _ itemIn u).mpr ⟨member,atom⟩
            exact hereAbsent rfl k kMember u at_k
          · exact absent none u member ⟨i,later,atom⟩
    · refine ⟨r,?_,found,?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,itemIn,lookup,advance,run]
      · intro none u member ⟨i,iMember,atom⟩
        rw [split] at iMember
        rcases List.mem_cons.mp iMember with rfl | later
        · rw [List.getElem?_eq_none (by rw [← lengths]; omega)] at atom
          cases atom
        · exact absent none u member ⟨i,later,atom⟩
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ u _ ⟨i,iMember,_⟩
    rw [List.drop_eq_nil_iff.mpr (by omega)] at iMember
    cases iMember
termination_by label.val.length - index.val
decreasing_by omega

/-- The search at one label returns something the label needs locally and does
    not satisfy, or nothing when it satisfies everything it needs locally. -/
theorem missing_at_correct (P : completion.Problem) (label : alloc.vec.Vec Usize) (triggers : TriggersOk P) :
    ∃ r, completion.missing_at P label = .ok r ∧
      (∀ c, r = some c → LocalNeeds P label.val c ∧ ¬ Holds P.entries.val label.val c.val) ∧
      (r = none → ∀ c, LocalNeeds P label.val c → Holds P.entries.val label.val c.val) := by
  rw [completion.missing_at]
  by_cases axiomsHold : Holds P.entries.val label.val P.axioms.val
  · obtain ⟨r2,run2,found2,absent2⟩ := missing_unfolding_correct P label triggers 0#usize
    simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at found2 absent2
    refine ⟨r2,by simp [holds_correct _ _ _ _ rfl,axiomsHold,run2],?_,?_⟩
    · intro c same
      obtain ⟨⟨u,member,atom,concept⟩,missing⟩ := found2 c same
      exact ⟨.inr ⟨u,member,atom,concept⟩,missing⟩
    · intro none c needs
      rcases needs with rfl | ⟨u,member,atom,rfl⟩
      · exact axiomsHold
      · exact absent2 none u member atom
  · refine ⟨some P.axioms,by simp [holds_correct _ _ _ _ rfl,axiomsHold],?_,by simp⟩
    intro c same
    cases same
    exact ⟨.inl rfl,axiomsHold⟩

/-- The label of a node. -/
def labelOf (nodes : List completion.Node) (x : Nat) : List Usize :=
  match nodes[x]? with
  | some n => n.label.val
  | none => []

/-- `unmet` decides whether `x` is a node whose label does not satisfy `c`. -/
private theorem unmet_correct (P : completion.Problem) (nodes : alloc.vec.Vec completion.Node) (x c : Usize) :
    completion.unmet P nodes x c =
      .ok (decide (x.val < nodes.val.length ∧ ¬ Holds P.entries.val (labelOf nodes.val x.val) c.val)) := by
  rw [completion.unmet]
  by_cases inside : x.val < nodes.val.length
  · have lookup : nodes.index_usize x = .ok nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have labelIs : labelOf nodes.val x.val = nodes.val[x.val].label.val := by
      simp [labelOf,List.getElem?_eq_getElem inside]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,alloc.vec.Vec.index_slice_index,lookup,
      holds_correct _ _ _ _ rfl,labelIs]
  · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside]

/-- One pass over the requirements: the first of `requirements[index..]` whose
    node does not satisfy it, with that node, or none when every requirement of
    a node holds there. -/
private theorem missing_requirement_correct (P : completion.Problem) (nodes : alloc.vec.Vec completion.Node)
    (index : Usize) :
    ∃ r, completion.missing_requirement P nodes index = .ok r ∧
      (∀ x c, r = some (x,c) → x.val < nodes.val.length ∧
        (∃ q ∈ P.requirements.val.drop index.val, q.node = x ∧ q.concept = c) ∧
        ¬ Holds P.entries.val (labelOf nodes.val x.val) c.val) ∧
      (r = none → ∀ q ∈ P.requirements.val.drop index.val, q.node.val < nodes.val.length →
        Holds P.entries.val (labelOf nodes.val q.node.val) q.concept.val) := by
  rw [completion.missing_requirement]
  by_cases more : index.val < P.requirements.val.length
  · have lookup : P.requirements.index_usize index = .ok P.requirements.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : P.requirements.val.drop index.val =
        P.requirements.val[index.val] :: P.requirements.val.drop (index.val+1) := List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have unmetRun := unmet_correct P nodes P.requirements.val[index.val].node P.requirements.val[index.val].concept
    by_cases missing : P.requirements.val[index.val].node.val < nodes.val.length ∧
        ¬ Holds P.entries.val (labelOf nodes.val P.requirements.val[index.val].node.val)
          P.requirements.val[index.val].concept.val
    · have decided := decide_eq_true missing
      refine ⟨some (P.requirements.val[index.val].node,P.requirements.val[index.val].concept),?_,?_,by simp⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,unmetRun,decided]
      · intro x c same
        simp only [Option.some.injEq,Prod.mk.injEq] at same
        obtain ⟨rfl,rfl⟩ := same
        exact ⟨missing.1,⟨_,by rw [split]; exact List.mem_cons_self ..,rfl,rfl⟩,missing.2⟩
    · have decided := decide_eq_false missing
      obtain ⟨r,run,found,absent⟩ := missing_requirement_correct P nodes index'
      refine ⟨r,?_,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,unmetRun,decided,Bool.false_eq_true,advance,run]
      · intro x c same
        obtain ⟨inside,⟨q,member,at_q,value⟩,fails⟩ := found x c same
        rw [nextIndex] at member
        exact ⟨inside,⟨q,by rw [split]; exact List.mem_cons_of_mem _ member,at_q,value⟩,fails⟩
      · intro none q member inside
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · by_contra fails
          exact missing ⟨inside,fails⟩
        · exact absent none q (by rw [nextIndex]; exact later) inside
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ q member
    rw [List.drop_eq_nil_iff.mpr (by omega)] at member
    cases member
termination_by P.requirements.val.length - index.val
decreasing_by all_goals omega

/-- The node search returns a node and something it needs locally and lacks, or
    nothing when every node from `index` on satisfies what it needs locally. -/
private theorem missing_local_correct (P : completion.Problem) (nodes : alloc.vec.Vec completion.Node) (index : Usize)
    (triggers : TriggersOk P) :
    ∃ r, completion.missing_local P nodes index = .ok r ∧
      (∀ x c, r = some (x,c) → x.val < nodes.val.length ∧ LocalNeeds P (labelOf nodes.val x.val) c ∧
        ¬ Holds P.entries.val (labelOf nodes.val x.val) c.val) ∧
      (r = none → ∀ y, index.val ≤ y → y < nodes.val.length → ∀ c, LocalNeeds P (labelOf nodes.val y) c →
        Holds P.entries.val (labelOf nodes.val y) c.val) := by
  rw [completion.missing_local]
  by_cases more : index.val < nodes.val.length
  · have lookup : nodes.index_usize index = .ok nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have labelHere : labelOf nodes.val index.val = nodes.val[index.val].label.val := by
      simp [labelOf,List.getElem?_eq_getElem more]
    obtain ⟨here,hereRun,hereFound,hereAbsent⟩ := missing_at_correct P nodes.val[index.val].label triggers
    cases here with
    | some c =>
      refine ⟨some (index,c),?_,?_,by simp⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,hereRun]
      · intro x c' same
        simp only [Option.some.injEq,Prod.mk.injEq] at same
        obtain ⟨rfl,rfl⟩ := same
        rw [labelHere]
        exact ⟨more,hereFound c rfl⟩
    | none =>
      obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val+1 := by simpa using indexValue
      obtain ⟨r,run,found,absent⟩ := missing_local_correct P nodes index' triggers
      refine ⟨r,?_,found,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,hereRun,advance,run]
      · intro none y low high
        by_cases same : y = index.val
        · subst same
          rw [labelHere]
          exact hereAbsent rfl
        · exact absent none y (by omega) high
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ y low high
    omega
termination_by nodes.val.length - index.val
decreasing_by omega

/-- The label lists an entry `∀t.f`. -/
def HasUniversal (entries : List concept_table.Entry) (label : List Usize) (t : ObjectPropertyExpression)
    (f : Usize) : Prop :=
  ∃ i ∈ label, entries[i.val]? = some (.Forall t f)

/-- An entry that the label `L` requires of a node reached along `r`: the filler
    `f` of a listed `∀q.f` with `r` included in `q`, or an entry `∀t.f` for a
    transitive role `t` between them. -/
def EdgeNeeds (entries : List concept_table.Entry) (h : hierarchy.RoleHierarchy) (L : List Usize)
    (r : ObjectPropertyExpression) (c : Usize) : Prop :=
  ∃ i ∈ L, ∃ q f, entries[i.val]? = some (.Forall q f) ∧ Below h r q ∧
    (c = f ∨ ∃ t ∈ transitives h, Below h r t ∧ Below h t q ∧ entries[c.val]? = some (.Forall t f))

/-- A node with label `L'` reached along `r` satisfies everything `L` requires:
    every filler, and every transitive restriction the table has. -/
def EdgeOk (entries : List concept_table.Entry) (h : hierarchy.RoleHierarchy) (L : List Usize)
    (r : ObjectPropertyExpression) (L' : List Usize) : Prop :=
  ∀ i ∈ L, ∀ q f, entries[i.val]? = some (.Forall q f) → Below h r q →
    Holds entries L' f.val ∧ ∀ t ∈ transitives h, Below h r t → Below h t q →
      (∃ j : Nat, entries[j]? = some (.Forall t f)) → HasUniversal entries L' t f

/-- A label satisfies a restriction entry exactly when it lists it. -/
theorem holds_listed (entries : List concept_table.Entry) (L : List Usize) (c : Nat) (e : concept_table.Entry)
    (at_c : entries[c]? = some e) (listed : ∀ a b, e ≠ .And a b ∧ e ≠ .Or a b) (notTop : e ≠ .Top)
    (notBottom : e ≠ .Bottom) : Holds entries L c ↔ ∃ i ∈ L, i.val = c := by
  rw [Holds.eq_def,at_c]
  cases e with
  | Top => exact absurd rfl notTop
  | Bottom => exact absurd rfl notBottom
  | And a b => exact absurd rfl (listed a b).1
  | Or a b => exact absurd rfl (listed a b).2
  | _ => rfl

theorem has_universal_correct (entries : alloc.vec.Vec concept_table.Entry) (label : alloc.vec.Vec Usize)
    (t : ObjectPropertyExpression) (f index : Usize) :
    completion.has_universal entries label t f index =
      .ok (decide (HasUniversal entries.val (label.val.drop index.val) t f)) := by
  rw [completion.has_universal]
  by_cases more : index.val < label.val.length
  · have lookup : label.index_usize index = .ok label.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : label.val.drop index.val = label.val[index.val] :: label.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := has_universal_correct entries label t f index'
    rw [nextIndex] at rest
    have cons : ¬ entries.val[label.val[index.val].val]? = some (.Forall t f) →
        (HasUniversal entries.val (label.val.drop (index.val+1)) t f ↔
          HasUniversal entries.val (label.val.drop index.val) t f) := by
      intro no
      rw [split]
      constructor
      · rintro ⟨i,member,found⟩
        exact ⟨i,List.mem_cons_of_mem _ member,found⟩
      · rintro ⟨i,member,found⟩
        rcases List.mem_cons.mp member with rfl | later
        · exact absurd found no
        · exact ⟨i,later,found⟩
    by_cases itemIn : label.val[index.val].val < entries.val.length
    · have one : entries.index_usize label.val[index.val] = .ok entries.val[label.val[index.val].val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem itemIn]
      by_cases found : entries.val[label.val[index.val].val] = .Forall t f
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,itemIn,one,Rowl.ConceptTable.universal_is_correct,found,decide_true]
        congr 1
        symm
        rw [decide_eq_true_iff]
        exact ⟨label.val[index.val],by rw [split]; exact List.mem_cons_self ..,
          by rw [List.getElem?_eq_getElem itemIn,found]⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,itemIn,one,Rowl.ConceptTable.universal_is_correct,found,decide_false,Bool.false_eq_true,
          advance,rest]
        congr 1
        rw [decide_eq_decide]
        apply cons
        rw [List.getElem?_eq_getElem itemIn]
        intro same
        exact found (Option.some.inj same)
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,itemIn,Bool.false_eq_true,advance,rest]
      congr 1
      rw [decide_eq_decide]
      apply cons
      rw [List.getElem?_eq_none_iff.mpr (by omega)]
      simp
  · have empty : label.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty,HasUniversal]
termination_by label.val.length - index.val
decreasing_by omega

private theorem missing_transitive_correct (entries : alloc.vec.Vec concept_table.Entry) (h : hierarchy.RoleHierarchy)
    (role sup : ObjectPropertyExpression) (filler : Usize) (target : alloc.vec.Vec Usize) (index : Usize) :
    ∃ r, completion.missing_transitive entries h role sup filler target index = .ok r ∧
      (∀ c, r = some c → ∃ t ∈ (transitives h).drop index.val, Below h role t ∧ Below h t sup ∧
        entries.val[c.val]? = some (.Forall t filler) ∧ ¬ HasUniversal entries.val target.val t filler) ∧
      (r = none → ∀ t ∈ (transitives h).drop index.val, Below h role t → Below h t sup →
        (∃ j : Nat, entries.val[j]? = some (.Forall t filler)) → HasUniversal entries.val target.val t filler) := by
  rw [completion.missing_transitive]
  by_cases more : index.val < h.transitive.val.length
  · have lookup : h.transitive.index_usize index = .ok h.transitive.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : (transitives h).drop index.val = h.transitive.val[index.val] :: (transitives h).drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := missing_transitive_correct entries h role sup filler target index'
    rw [nextIndex] at found absent
    have later : ∀ c, r = some c → ∃ t ∈ (transitives h).drop index.val, Below h role t ∧ Below h t sup ∧
        entries.val[c.val]? = some (.Forall t filler) ∧ ¬ HasUniversal entries.val target.val t filler := by
      intro c same
      obtain ⟨t,member,rest⟩ := found c same
      exact ⟨t,by rw [split]; exact List.mem_cons_of_mem _ member,rest⟩
    have current := h.transitive.val[index.val]
    by_cases first : Below h role h.transitive.val[index.val]
    · by_cases second : Below h h.transitive.val[index.val] sup
      · by_cases has : HasUniversal entries.val target.val h.transitive.val[index.val] filler
        · refine ⟨r,?_,later,?_⟩
          · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookup,bind_ok,below_correct,first,second,decide_true,has_universal_correct,
              show (0#usize).val = 0 from rfl,List.drop_zero,has,advance,run]
          · intro none t member one two exists'
            rw [split] at member
            rcases List.mem_cons.mp member with rfl | rest
            · exact has
            · exact absent none t rest one two exists'
        · obtain ⟨p,pRun,hit,miss⟩ := Rowl.ConceptTable.universal_from_correct entries h.transitive.val[index.val]
            filler 0#usize
          by_cases inside : p.val < entries.val.length
          · refine ⟨some p,?_,?_,by simp⟩
            · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
                lookup,bind_ok,below_correct,first,second,decide_true,has_universal_correct,
                show (0#usize).val = 0 from rfl,List.drop_zero,has,decide_false,Bool.false_eq_true,pRun,inside]
            · intro c same
              cases same
              exact ⟨_,by rw [split]; exact List.mem_cons_self ..,first,second,hit inside,has⟩
          · refine ⟨r,?_,later,?_⟩
            · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
                lookup,bind_ok,below_correct,first,second,decide_true,has_universal_correct,
                show (0#usize).val = 0 from rfl,List.drop_zero,has,decide_false,Bool.false_eq_true,pRun,inside,
                advance,run]
            · intro none t member one two exists'
              rw [split] at member
              rcases List.mem_cons.mp member with rfl | rest
              · obtain ⟨j,at_j⟩ := exists'
                exact absurd (by simpa using List.mem_of_getElem? at_j) (miss inside)
              · exact absent none t rest one two exists'
      · refine ⟨r,?_,later,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,below_correct,first,second,decide_true,decide_false,Bool.false_eq_true,advance,run]
        · intro none t member one two exists'
          rw [split] at member
          rcases List.mem_cons.mp member with rfl | rest
          · exact absurd two second
          · exact absent none t rest one two exists'
    · refine ⟨r,?_,later,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,below_correct,first,decide_false,Bool.false_eq_true,advance,run]
      · intro none t member one two exists'
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | rest
        · exact absurd one first
        · exact absent none t rest one two exists'
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ t member
    rw [List.drop_eq_nil_iff.mpr (by simp only [transitives]; omega)] at member
    cases member
termination_by h.transitive.val.length - index.val
decreasing_by all_goals omega

private theorem missing_for_correct (entries : alloc.vec.Vec concept_table.Entry) (h : hierarchy.RoleHierarchy)
    (item : Usize) (role : ObjectPropertyExpression) (target : alloc.vec.Vec Usize) :
    ∃ r, completion.missing_for entries h item role target = .ok r ∧
      (∀ c, r = some c → ∃ q f, entries.val[item.val]? = some (.Forall q f) ∧ Below h role q ∧
        ((c = f ∧ ¬ Holds entries.val target.val f.val) ∨ ∃ t ∈ transitives h, Below h role t ∧ Below h t q ∧
          entries.val[c.val]? = some (.Forall t f) ∧ ¬ HasUniversal entries.val target.val t f)) ∧
      (r = none → ∀ q f, entries.val[item.val]? = some (.Forall q f) → Below h role q →
        Holds entries.val target.val f.val ∧ ∀ t ∈ transitives h, Below h role t → Below h t q →
          (∃ j : Nat, entries.val[j]? = some (.Forall t f)) → HasUniversal entries.val target.val t f) := by
  rw [completion.missing_for]
  by_cases inside : item.val < entries.val.length
  · have lookup : entries.index_usize item = .ok entries.val[item.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have at_item : entries.val[item.val]? = some entries.val[item.val] := List.getElem?_eq_getElem inside
    cases entry : entries.val[item.val] with
    | Forall q f =>
      rw [entry] at at_item
      by_cases included : Below h role q
      · by_cases satisfied : Holds entries.val target.val f.val
        · obtain ⟨r,run,found,absent⟩ := missing_transitive_correct entries h role q f target 0#usize
          simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at found absent
          refine ⟨r,?_,?_,?_⟩
          · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookup,bind_ok,entry,below_correct,included,decide_true,holds_correct _ _ _ _ rfl,satisfied,run]
          · intro c same
            obtain ⟨t,member,one,two,at_c,missing⟩ := found c same
            exact ⟨q,f,at_item,included,.inr ⟨t,member,one,two,at_c,missing⟩⟩
          · intro none q' f' at_item' included'
            rw [at_item] at at_item'
            simp only [Option.some.injEq,concept_table.Entry.Forall.injEq] at at_item'
            obtain ⟨rfl,rfl⟩ := at_item'
            exact ⟨satisfied,absent none⟩
        · refine ⟨some f,?_,?_,by simp⟩
          · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookup,bind_ok,entry,below_correct,included,decide_true,holds_correct _ _ _ _ rfl,satisfied,
              decide_false,Bool.false_eq_true]
          · intro c same
            cases same
            exact ⟨q,f,at_item,included,.inl ⟨rfl,satisfied⟩⟩
      · refine ⟨none,?_,by simp,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,entry,below_correct,included,decide_false,Bool.false_eq_true]
        · intro _ q' f' at_item' included'
          rw [at_item] at at_item'
          simp only [Option.some.injEq,concept_table.Entry.Forall.injEq] at at_item'
          obtain ⟨rfl,rfl⟩ := at_item'
          exact absurd included' included
    | _ =>
      rw [entry] at at_item
      refine ⟨none,?_,by simp,?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,entry]
      · intro _ q' f' at_item'
        rw [at_item] at at_item'
        cases at_item'
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],by simp,?_⟩
    intro _ q f at_item
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at at_item
    cases at_item

/-- An entry required along an edge and missing at the target: its filler, or a
    transitive restriction, which a label lists exactly when it satisfies it. -/
private theorem required_missing (entries : List concept_table.Entry) (h : hierarchy.RoleHierarchy)
    (L target : List Usize) (role : ObjectPropertyExpression) (c : Usize) (i : Usize) (member : i ∈ L)
    (found : ∃ q f, entries[i.val]? = some (.Forall q f) ∧ Below h role q ∧
      ((c = f ∧ ¬ Holds entries target f.val) ∨ ∃ t ∈ transitives h, Below h role t ∧ Below h t q ∧
        entries[c.val]? = some (.Forall t f) ∧ ¬ HasUniversal entries target t f)) :
    EdgeNeeds entries h L role c ∧ ¬ Holds entries target c.val := by
  obtain ⟨q,f,at_i,included,kind⟩ := found
  rcases kind with ⟨rfl,missing⟩ | ⟨t,transitive,one,two,at_c,missing⟩
  · exact ⟨⟨i,member,q,c,at_i,included,.inl rfl⟩,missing⟩
  · refine ⟨⟨i,member,q,f,at_i,included,.inr ⟨t,transitive,one,two,at_c⟩⟩,?_⟩
    rw [holds_listed entries target c.val _ at_c (by intro a b; simp) (by simp) (by simp)]
    rintro ⟨j,listed,same⟩
    exact missing ⟨j,listed,by rw [same]; exact at_c⟩

theorem missing_along_correct (entries : alloc.vec.Vec concept_table.Entry) (h : hierarchy.RoleHierarchy)
    (label : alloc.vec.Vec Usize) (role : ObjectPropertyExpression) (target : alloc.vec.Vec Usize) (index : Usize) :
    ∃ r, completion.missing_along entries h label role target index = .ok r ∧
      (∀ c, r = some c → EdgeNeeds entries.val h (label.val.drop index.val) role c ∧
        ¬ Holds entries.val target.val c.val) ∧
      (r = none → EdgeOk entries.val h (label.val.drop index.val) role target.val) := by
  rw [completion.missing_along]
  by_cases more : index.val < label.val.length
  · have lookup : label.index_usize index = .ok label.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : label.val.drop index.val = label.val[index.val] :: label.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨here,hereRun,hereFound,hereAbsent⟩ := missing_for_correct entries h label.val[index.val] role target
    cases here with
    | some c =>
      refine ⟨some c,?_,?_,by simp⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,hereRun]
      · intro c' same
        cases same
        rw [split]
        exact required_missing entries.val h _ target.val role c label.val[index.val] (List.mem_cons_self ..)
          (hereFound c rfl)
    | none =>
      obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val+1 := by simpa using indexValue
      obtain ⟨r,run,found,absent⟩ := missing_along_correct entries h label role target index'
      rw [nextIndex] at found absent
      refine ⟨r,?_,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,hereRun,advance,run]
      · intro c same
        obtain ⟨⟨i,member,rest⟩,missing⟩ := found c same
        exact ⟨⟨i,by rw [split]; exact List.mem_cons_of_mem _ member,rest⟩,missing⟩
      · intro none i member q f at_i included
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · exact hereAbsent rfl q f at_i included
        · exact absent none i later q f at_i included
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ i member
    rw [List.drop_eq_nil_iff.mpr (by omega)] at member
    cases member
termination_by label.val.length - index.val
decreasing_by omega

/-- The search along one edge returns a node at either end with an entry the
    other end requires and it lacks, or nothing when both directions are
    satisfied. -/
theorem missing_edge_correct (entries : alloc.vec.Vec concept_table.Entry) (h : hierarchy.RoleHierarchy)
    (nodes : alloc.vec.Vec completion.Node) (source target : Usize) (role : ObjectPropertyExpression) :
    ∃ r, completion.missing_edge entries h nodes source target role = .ok r ∧
      (∀ x c, r = some (x,c) → source.val < nodes.val.length ∧ target.val < nodes.val.length ∧
        ((x = target ∧ EdgeNeeds entries.val h (labelOf nodes.val source.val) role c ∧
            ¬ Holds entries.val (labelOf nodes.val target.val) c.val) ∨
          (x = source ∧ EdgeNeeds entries.val h (labelOf nodes.val target.val) (inv role) c ∧
            ¬ Holds entries.val (labelOf nodes.val source.val) c.val))) ∧
      (r = none → source.val < nodes.val.length → target.val < nodes.val.length →
        EdgeOk entries.val h (labelOf nodes.val source.val) role (labelOf nodes.val target.val) ∧
        EdgeOk entries.val h (labelOf nodes.val target.val) (inv role) (labelOf nodes.val source.val)) := by
  rw [completion.missing_edge]
  by_cases sourceIn : source.val < nodes.val.length
  · by_cases targetIn : target.val < nodes.val.length
    · have one : nodes.index_usize source = .ok nodes.val[source.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem sourceIn]
      have two : nodes.index_usize target = .ok nodes.val[target.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem targetIn]
      have sourceLabel : labelOf nodes.val source.val = nodes.val[source.val].label.val := by
        simp [labelOf,List.getElem?_eq_getElem sourceIn]
      have targetLabel : labelOf nodes.val target.val = nodes.val[target.val].label.val := by
        simp [labelOf,List.getElem?_eq_getElem targetIn]
      rw [sourceLabel,targetLabel]
      obtain ⟨forward,forwardRun,forwardFound,forwardAbsent⟩ :=
        missing_along_correct entries h nodes.val[source.val].label role nodes.val[target.val].label 0#usize
      simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at forwardFound forwardAbsent
      cases forward with
      | some c =>
        refine ⟨some (target,c),?_,?_,by simp⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,targetIn,↓reduceIte,
            alloc.vec.Vec.index_slice_index,one,two,bind_ok,forwardRun]
        · intro x c' same
          simp only [Option.some.injEq,Prod.mk.injEq] at same
          obtain ⟨rfl,rfl⟩ := same
          exact ⟨sourceIn,targetIn,.inl ⟨rfl,forwardFound c rfl⟩⟩
      | none =>
        obtain ⟨backward,backwardRun,backwardFound,backwardAbsent⟩ :=
          missing_along_correct entries h nodes.val[target.val].label (inv role) nodes.val[source.val].label 0#usize
        simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at backwardFound backwardAbsent
        cases backward with
        | some c =>
          refine ⟨some (source,c),?_,?_,by simp⟩
          · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,targetIn,↓reduceIte,
              alloc.vec.Vec.index_slice_index,one,two,bind_ok,forwardRun,inverse_correct,backwardRun]
          · intro x c' same
            simp only [Option.some.injEq,Prod.mk.injEq] at same
            obtain ⟨rfl,rfl⟩ := same
            exact ⟨sourceIn,targetIn,.inr ⟨rfl,backwardFound c rfl⟩⟩
        | none =>
          refine ⟨none,?_,by simp,fun _ _ _ => ⟨forwardAbsent rfl,backwardAbsent rfl⟩⟩
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,targetIn,↓reduceIte,
            alloc.vec.Vec.index_slice_index,one,two,bind_ok,forwardRun,inverse_correct,backwardRun]
    · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,targetIn],by simp,?_⟩
      intro _ _ inside
      exact absurd inside targetIn
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn],by simp,?_⟩
    intro _ inside
    exact absurd inside sourceIn
/-- The role of the existential entry that created a tree node. -/
def createdRole (entries : List concept_table.Entry) (n : completion.Node) : Option ObjectPropertyExpression :=
  match entries[n.via.val]? with
  | some (.Exists r _) => some r
  | _ => none

theorem created_role_correct (entries : alloc.vec.Vec concept_table.Entry) (via : Usize) :
    completion.created_role entries via =
      .ok (match entries.val[via.val]? with
        | some (.Exists r _) => some r
        | _ => none) := by
  rw [completion.created_role]
  by_cases inside : via.val < entries.val.length
  · have lookup : entries.index_usize via = .ok entries.val[via.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    rw [List.getElem?_eq_getElem inside]
    cases entry : entries.val[via.val] <;>
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,entry,copy_role_identity]
  · rw [List.getElem?_eq_none_iff.mpr (by omega)]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside]

theorem missing_link_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy)
    (nodes : alloc.vec.Vec completion.Node) (index : Usize) :
    ∃ r, completion.missing_link P h nodes index = .ok r ∧
      (∀ x c, r = some (x,c) → ∃ l ∈ P.links.val.drop index.val, l.from.val < nodes.val.length ∧
        l.to.val < nodes.val.length ∧
        ((x = l.to ∧ EdgeNeeds P.entries.val h (labelOf nodes.val l.from.val) l.role c ∧
            ¬ Holds P.entries.val (labelOf nodes.val l.to.val) c.val) ∨
          (x = l.from ∧ EdgeNeeds P.entries.val h (labelOf nodes.val l.to.val) (inv l.role) c ∧
            ¬ Holds P.entries.val (labelOf nodes.val l.from.val) c.val))) ∧
      (r = none → ∀ l ∈ P.links.val.drop index.val, l.from.val < nodes.val.length → l.to.val < nodes.val.length →
        EdgeOk P.entries.val h (labelOf nodes.val l.from.val) l.role (labelOf nodes.val l.to.val) ∧
        EdgeOk P.entries.val h (labelOf nodes.val l.to.val) (inv l.role) (labelOf nodes.val l.from.val)) := by
  rw [completion.missing_link]
  by_cases more : index.val < P.links.val.length
  · have lookup : P.links.index_usize index = .ok P.links.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : P.links.val.drop index.val = P.links.val[index.val] :: P.links.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨here,hereRun,hereFound,hereAbsent⟩ := missing_edge_correct P.entries h nodes
      P.links.val[index.val].from P.links.val[index.val].to P.links.val[index.val].role
    cases here with
    | some found =>
      obtain ⟨x,c⟩ := found
      refine ⟨some (x,c),?_,?_,by simp⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,hereRun]
      · intro x' c' same
        simp only [Option.some.injEq,Prod.mk.injEq] at same
        obtain ⟨rfl,rfl⟩ := same
        exact ⟨_,by rw [split]; exact List.mem_cons_self ..,hereFound x c rfl⟩
    | none =>
      obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val+1 := by simpa using indexValue
      obtain ⟨r,run,found,absent⟩ := missing_link_correct P h nodes index'
      rw [nextIndex] at found absent
      refine ⟨r,?_,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,hereRun,advance,run]
      · intro x c same
        obtain ⟨l,member,rest⟩ := found x c same
        exact ⟨l,by rw [split]; exact List.mem_cons_of_mem _ member,rest⟩
      · intro none l member
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · exact hereAbsent rfl
        · exact absent none l later
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ l member
    rw [List.drop_eq_nil_iff.mpr (by omega)] at member
    cases member
termination_by P.links.val.length - index.val
decreasing_by omega

theorem missing_tree_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy)
    (nodes : alloc.vec.Vec completion.Node) (index : Usize) :
    ∃ r, completion.missing_tree P h nodes index = .ok r ∧
      (∀ x c, r = some (x,c) → ∃ y n s, index.val ≤ y ∧ nodes.val[y]? = some n ∧ n.tree = true ∧
        createdRole P.entries.val n = some s ∧ n.parent.val < nodes.val.length ∧
        ((x.val = y ∧ EdgeNeeds P.entries.val h (labelOf nodes.val n.parent.val) s c ∧
            ¬ Holds P.entries.val (labelOf nodes.val y) c.val) ∨
          (x = n.parent ∧ EdgeNeeds P.entries.val h (labelOf nodes.val y) (inv s) c ∧
            ¬ Holds P.entries.val (labelOf nodes.val n.parent.val) c.val))) ∧
      (r = none → ∀ y n s, index.val ≤ y → nodes.val[y]? = some n → n.tree = true →
        createdRole P.entries.val n = some s → n.parent.val < nodes.val.length →
        EdgeOk P.entries.val h (labelOf nodes.val n.parent.val) s (labelOf nodes.val y) ∧
        EdgeOk P.entries.val h (labelOf nodes.val y) (inv s) (labelOf nodes.val n.parent.val)) := by
  rw [completion.missing_tree]
  by_cases more : index.val < nodes.val.length
  · have lookup : nodes.index_usize index = .ok nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have at_index : nodes.val[index.val]? = some nodes.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := missing_tree_correct P h nodes index'
    rw [nextIndex] at found absent
    have later : ∀ x c, r = some (x,c) → ∃ y n s, index.val ≤ y ∧ nodes.val[y]? = some n ∧ n.tree = true ∧
        createdRole P.entries.val n = some s ∧ n.parent.val < nodes.val.length ∧
        ((x.val = y ∧ EdgeNeeds P.entries.val h (labelOf nodes.val n.parent.val) s c ∧
            ¬ Holds P.entries.val (labelOf nodes.val y) c.val) ∨
          (x = n.parent ∧ EdgeNeeds P.entries.val h (labelOf nodes.val y) (inv s) c ∧
            ¬ Holds P.entries.val (labelOf nodes.val n.parent.val) c.val)) := by
      intro x c same
      obtain ⟨y,n,s,low,rest⟩ := found x c same
      exact ⟨y,n,s,by omega,rest⟩
    have skip : (∀ s, nodes.val[index.val].tree = true → createdRole P.entries.val nodes.val[index.val] = some s →
        nodes.val[index.val].parent.val < nodes.val.length →
        EdgeOk P.entries.val h (labelOf nodes.val nodes.val[index.val].parent.val) s (labelOf nodes.val index.val) ∧
        EdgeOk P.entries.val h (labelOf nodes.val index.val) (inv s)
          (labelOf nodes.val nodes.val[index.val].parent.val)) →
        r = none → ∀ y n s, index.val ≤ y → nodes.val[y]? = some n → n.tree = true →
          createdRole P.entries.val n = some s → n.parent.val < nodes.val.length →
          EdgeOk P.entries.val h (labelOf nodes.val n.parent.val) s (labelOf nodes.val y) ∧
          EdgeOk P.entries.val h (labelOf nodes.val y) (inv s) (labelOf nodes.val n.parent.val) := by
      intro hereOk none y n s low at_y tree role parentIn
      by_cases same : y = index.val
      · subst same
        rw [at_index] at at_y
        cases at_y
        exact hereOk s tree role parentIn
      · exact absent none y n s (by omega) at_y tree role parentIn
    by_cases tree : nodes.val[index.val].tree = true
    · have roleRun := created_role_correct P.entries nodes.val[index.val].via
      cases role : createdRole P.entries.val nodes.val[index.val] with
      | none =>
        have roleNone : (match P.entries.val[nodes.val[index.val].via.val]? with
            | some (.Exists r _) => some r
            | _ => none) = none := role
        refine ⟨r,?_,later,skip (fun s _ impossible => by rw [role] at impossible; cases impossible)⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,tree,uncurry_apply_pair,roleRun,roleNone,advance,run]
      | some s =>
        have roleSome : (match P.entries.val[nodes.val[index.val].via.val]? with
            | some (.Exists r _) => some r
            | _ => none) = some s := role
        obtain ⟨edge,edgeRun,edgeFound,edgeAbsent⟩ := missing_edge_correct P.entries h nodes
          nodes.val[index.val].parent index s
        cases edge with
        | some pair =>
          obtain ⟨x,c⟩ := pair
          refine ⟨some (x,c),?_,?_,by simp⟩
          · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookup,bind_ok,tree,uncurry_apply_pair,roleRun,roleSome,edgeRun]
          · intro x' c' same
            simp only [Option.some.injEq,Prod.mk.injEq] at same
            obtain ⟨rfl,rfl⟩ := same
            obtain ⟨parentIn,_,kind⟩ := edgeFound x c rfl
            refine ⟨index.val,nodes.val[index.val],s,le_refl _,at_index,tree,role,parentIn,?_⟩
            rcases kind with ⟨rfl,needs,missing⟩ | ⟨rfl,needs,missing⟩
            · exact .inl ⟨rfl,needs,missing⟩
            · exact .inr ⟨rfl,needs,missing⟩
        | none =>
          refine ⟨r,?_,later,skip (fun s' _ role' parentIn => ?_)⟩
          · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookup,bind_ok,tree,uncurry_apply_pair,roleRun,roleSome,edgeRun,advance,run]
          · rw [role] at role'
            cases role'
            exact edgeAbsent rfl parentIn more
    · refine ⟨r,?_,later,skip (fun s isTree => absurd isTree tree)⟩
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,tree,uncurry_apply_pair,Bool.false_eq_true,advance,run]
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ y n s low at_y
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at at_y
    cases at_y
termination_by nodes.val.length - index.val
decreasing_by omega
/-- `y` is a neighbour of `x` along a role included in `r`: a child created along
    such a role, the parent when the inverse of the role that created `x` is such
    a role, or a named node linked to `x` in either direction. -/
def Neighbour (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node) (x : Nat)
    (r : ObjectPropertyExpression) (y : Nat) : Prop :=
  (∃ ny, nodes[y]? = some ny ∧ ny.tree = true ∧ ny.parent.val = x ∧
    ∃ s, createdRole P.entries.val ny = some s ∧ Below h s r) ∨
  (∃ nx, nodes[x]? = some nx ∧ nx.tree = true ∧ nx.parent.val = y ∧ y < nodes.length ∧
    ∃ s, createdRole P.entries.val nx = some s ∧ Below h (inv s) r) ∨
  (∃ l ∈ P.links.val, l.from.val = x ∧ l.to.val = y ∧ y < nodes.length ∧ Below h l.role r) ∨
  (∃ l ∈ P.links.val, l.to.val = x ∧ l.from.val = y ∧ y < nodes.length ∧ Below h (inv l.role) r)

/-- Some neighbour of `x` along a role included in `r` satisfies the entry `f`. -/
def Witnessed (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node) (x : Nat)
    (r : ObjectPropertyExpression) (f : Usize) : Prop :=
  ∃ y, Neighbour P h nodes x r y ∧ Holds P.entries.val (labelOf nodes y) f.val

private theorem role_match (entries : List concept_table.Entry) (n : completion.Node) :
    (match entries[n.via.val]? with
      | some (.Exists r _) => some r
      | _ => none) = createdRole entries n := rfl

private theorem child_witness_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy)
    (nodes : alloc.vec.Vec completion.Node) (x : Usize) (r : ObjectPropertyExpression) (f index : Usize) :
    completion.child_witness P h nodes x r f index = .ok (decide (∃ y, index.val ≤ y ∧ ∃ ny,
      nodes.val[y]? = some ny ∧ ny.tree = true ∧ ny.parent.val = x.val ∧
      (∃ s, createdRole P.entries.val ny = some s ∧ Below h s r) ∧ Holds P.entries.val ny.label.val f.val)) := by
  rw [completion.child_witness]
  by_cases more : index.val < nodes.val.length
  · have lookup : nodes.index_usize index = .ok nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have at_index : nodes.val[index.val]? = some nodes.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := child_witness_correct P h nodes x r f index'
    rw [nextIndex] at rest
    have cons : ¬ (nodes.val[index.val].tree = true ∧ nodes.val[index.val].parent.val = x.val ∧
        (∃ s, createdRole P.entries.val nodes.val[index.val] = some s ∧ Below h s r) ∧
        Holds P.entries.val nodes.val[index.val].label.val f.val) →
        decide (∃ y, index.val + 1 ≤ y ∧ ∃ ny, nodes.val[y]? = some ny ∧ ny.tree = true ∧ ny.parent.val = x.val ∧
          (∃ s, createdRole P.entries.val ny = some s ∧ Below h s r) ∧ Holds P.entries.val ny.label.val f.val) =
        decide (∃ y, index.val ≤ y ∧ ∃ ny, nodes.val[y]? = some ny ∧ ny.tree = true ∧ ny.parent.val = x.val ∧
          (∃ s, createdRole P.entries.val ny = some s ∧ Below h s r) ∧ Holds P.entries.val ny.label.val f.val) := by
      intro no
      rw [decide_eq_decide]
      constructor
      · rintro ⟨y,low,rest⟩; exact ⟨y,by omega,rest⟩
      · rintro ⟨y,low,ny,at_y,rest⟩
        by_cases same : y = index.val
        · subst same
          rw [at_index] at at_y
          cases at_y
          exact absurd rest no
        · exact ⟨y,by omega,ny,at_y,rest⟩
    have yes : (nodes.val[index.val].tree = true ∧ nodes.val[index.val].parent.val = x.val ∧
        (∃ s, createdRole P.entries.val nodes.val[index.val] = some s ∧ Below h s r) ∧
        Holds P.entries.val nodes.val[index.val].label.val f.val) →
        ok true = ok (decide (∃ y, index.val ≤ y ∧ ∃ ny, nodes.val[y]? = some ny ∧ ny.tree = true ∧
          ny.parent.val = x.val ∧ (∃ s, createdRole P.entries.val ny = some s ∧ Below h s r) ∧
          Holds P.entries.val ny.label.val f.val)) := by
      intro found
      congr 1
      symm
      rw [decide_eq_true_iff]
      exact ⟨index.val,le_refl _,_,at_index,found⟩
    have roleRun := created_role_correct P.entries nodes.val[index.val].via
    rw [role_match] at roleRun
    by_cases tree : nodes.val[index.val].tree = true
    · by_cases parent : nodes.val[index.val].parent = x
      · have parentVal : nodes.val[index.val].parent.val = x.val := by rw [parent]
        cases role : createdRole P.entries.val nodes.val[index.val] with
        | none =>
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,tree,parent,roleRun,role,uncurry_apply_pair,Bool.false_eq_true,advance,rest]
          rw [cons (by rintro ⟨_,_,⟨s,impossible,_⟩,_⟩; rw [role] at impossible; cases impossible)]
        | some s =>
          by_cases included : Below h s r
          · by_cases holds : Holds P.entries.val nodes.val[index.val].label.val f.val
            · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
                lookup,bind_ok,tree,parent,roleRun,role,uncurry_apply_pair,below_correct,included,decide_true,
                holds_correct _ _ _ _ rfl,holds]
              exact yes ⟨tree,parentVal,⟨s,role,included⟩,holds⟩
            · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
                lookup,bind_ok,tree,parent,roleRun,role,uncurry_apply_pair,below_correct,included,decide_true,
                holds_correct _ _ _ _ rfl,holds,decide_false,Bool.false_eq_true,advance,rest]
              rw [cons (fun found => holds found.2.2.2)]
          · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookup,bind_ok,tree,parent,roleRun,role,uncurry_apply_pair,below_correct,included,decide_false,
              Bool.false_eq_true,advance,rest]
            rw [cons (by
              rintro ⟨_,_,⟨s',same,included'⟩,_⟩
              rw [role] at same
              cases same
              exact included included')]
      · have parentVal : ¬ nodes.val[index.val].parent.val = x.val := fun same => parent (UScalar.eq_of_val_eq same)
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,tree,parent,uncurry_apply_pair,Bool.false_eq_true,advance,rest]
        rw [cons (fun found => parentVal found.2.1)]
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,tree,uncurry_apply_pair,Bool.false_eq_true,advance,rest]
      rw [cons (fun found => tree found.1)]
  · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte]
    congr 1
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨y,low,ny,at_y,_⟩
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at at_y
    cases at_y
termination_by nodes.val.length - index.val
decreasing_by omega

private theorem parent_witness_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy)
    (nodes : alloc.vec.Vec completion.Node) (x : Usize) (r : ObjectPropertyExpression) (f : Usize) :
    completion.parent_witness P h nodes x r f = .ok (decide (∃ nx, nodes.val[x.val]? = some nx ∧ nx.tree = true ∧
      nx.parent.val < nodes.val.length ∧ (∃ s, createdRole P.entries.val nx = some s ∧ Below h (inv s) r) ∧
      Holds P.entries.val (labelOf nodes.val nx.parent.val) f.val)) := by
  rw [completion.parent_witness]
  by_cases inside : x.val < nodes.val.length
  · have lookup : nodes.index_usize x = .ok nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have at_x : nodes.val[x.val]? = some nodes.val[x.val] := List.getElem?_eq_getElem inside
    have unique : ∀ (Q : completion.Node → Prop), (∃ nx, nodes.val[x.val]? = some nx ∧ Q nx) ↔ Q nodes.val[x.val] := by
      intro Q
      constructor
      · rintro ⟨nx,at_x',holds⟩; rw [at_x] at at_x'; cases at_x'; exact holds
      · intro holds; exact ⟨_,at_x,holds⟩
    have roleRun := created_role_correct P.entries nodes.val[x.val].via
    rw [role_match] at roleRun
    by_cases tree : nodes.val[x.val].tree = true
    · by_cases parentIn : nodes.val[x.val].parent.val < nodes.val.length
      · have parentLookup : nodes.index_usize nodes.val[x.val].parent =
            .ok nodes.val[nodes.val[x.val].parent.val] := by
          simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem parentIn]
        have parentLabel : labelOf nodes.val nodes.val[x.val].parent.val =
            nodes.val[nodes.val[x.val].parent.val].label.val := by
          simp [labelOf,List.getElem?_eq_getElem parentIn]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,tree,parentIn,roleRun]
        cases role : createdRole P.entries.val nodes.val[x.val] with
        | none =>
          simp only
          congr 1
          symm
          rw [decide_eq_false_iff_not,unique]
          rintro ⟨_,_,⟨s,same,_⟩,_⟩
          rw [role] at same
          cases same
        | some s =>
          by_cases included : Below h (inv s) r
          · simp only [inverse_correct,below_correct,included,decide_true,bind_ok,↓reduceIte,parentLookup,
              holds_correct _ _ _ _ rfl]
            congr 1
            rw [decide_eq_decide,unique,parentLabel]
            constructor
            · intro holds
              exact ⟨tree,parentIn,⟨s,role,included⟩,holds⟩
            · rintro ⟨_,_,_,holds⟩
              exact holds
          · simp only [inverse_correct,below_correct,included,decide_false,bind_ok,Bool.false_eq_true,↓reduceIte]
            congr 1
            symm
            rw [decide_eq_false_iff_not,unique]
            rintro ⟨_,_,⟨s',same,included'⟩,_⟩
            rw [role] at same
            cases same
            exact included included'
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,tree,parentIn]
        congr 1
        symm
        rw [decide_eq_false_iff_not,unique]
        rintro ⟨_,inside',_⟩
        exact parentIn inside'
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,tree,Bool.false_eq_true]
      congr 1
      symm
      rw [decide_eq_false_iff_not,unique]
      rintro ⟨isTree,_⟩
      exact tree isTree
  · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte]
    congr 1
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨nx,at_x,_⟩
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at at_x
    cases at_x

private theorem forward_witness_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy)
    (nodes : alloc.vec.Vec completion.Node) (l : completion.Link) (x : Usize) (r : ObjectPropertyExpression)
    (f : Usize) :
    completion.forward_witness P h nodes l x r f = .ok (decide (l.from = x ∧ l.to.val < nodes.val.length ∧
      Below h l.role r ∧ Holds P.entries.val (labelOf nodes.val l.to.val) f.val)) := by
  rw [completion.forward_witness]
  by_cases source : l.from = x
  · by_cases target : l.to.val < nodes.val.length
    · have lookup : nodes.index_usize l.to = .ok nodes.val[l.to.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem target]
      have targetLabel : labelOf nodes.val l.to.val = nodes.val[l.to.val].label.val := by
        simp [labelOf,List.getElem?_eq_getElem target]
      by_cases included : Below h l.role r
      · simp [source,alloc.vec.Vec.len_val,UScalar.lt_equiv,target,below_correct,included,lookup,
          holds_correct _ _ _ _ rfl,targetLabel]
      · simp [source,alloc.vec.Vec.len_val,UScalar.lt_equiv,target,below_correct,included]
    · simp [source,alloc.vec.Vec.len_val,UScalar.lt_equiv,target]
  · simp [source]

private theorem backward_witness_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy)
    (nodes : alloc.vec.Vec completion.Node) (l : completion.Link) (x : Usize) (r : ObjectPropertyExpression)
    (f : Usize) :
    completion.backward_witness P h nodes l x r f = .ok (decide (l.to = x ∧ l.from.val < nodes.val.length ∧
      Below h (inv l.role) r ∧ Holds P.entries.val (labelOf nodes.val l.from.val) f.val)) := by
  rw [completion.backward_witness]
  by_cases source : l.to = x
  · by_cases target : l.from.val < nodes.val.length
    · have lookup : nodes.index_usize l.from = .ok nodes.val[l.from.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem target]
      have targetLabel : labelOf nodes.val l.from.val = nodes.val[l.from.val].label.val := by
        simp [labelOf,List.getElem?_eq_getElem target]
      by_cases included : Below h (inv l.role) r
      · simp [source,alloc.vec.Vec.len_val,UScalar.lt_equiv,target,inverse_correct,below_correct,included,lookup,
          holds_correct _ _ _ _ rfl,targetLabel]
      · simp [source,alloc.vec.Vec.len_val,UScalar.lt_equiv,target,inverse_correct,below_correct,included]
    · simp [source,alloc.vec.Vec.len_val,UScalar.lt_equiv,target]
  · simp [source]

private theorem link_witness_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy)
    (nodes : alloc.vec.Vec completion.Node) (x : Usize) (r : ObjectPropertyExpression) (f index : Usize) :
    completion.link_witness P h nodes x r f index = .ok (decide (∃ l ∈ P.links.val.drop index.val,
      (l.from = x ∧ l.to.val < nodes.val.length ∧ Below h l.role r ∧
        Holds P.entries.val (labelOf nodes.val l.to.val) f.val) ∨
      (l.to = x ∧ l.from.val < nodes.val.length ∧ Below h (inv l.role) r ∧
        Holds P.entries.val (labelOf nodes.val l.from.val) f.val))) := by
  rw [completion.link_witness]
  by_cases more : index.val < P.links.val.length
  · have lookup : P.links.index_usize index = .ok P.links.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : P.links.val.drop index.val = P.links.val[index.val] :: P.links.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := link_witness_correct P h nodes x r f index'
    rw [nextIndex] at rest
    rw [split]
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok,forward_witness_correct,backward_witness_correct]
    by_cases forward : P.links.val[index.val].from = x ∧ P.links.val[index.val].to.val < nodes.val.length ∧
        Below h P.links.val[index.val].role r ∧ Holds P.entries.val (labelOf nodes.val P.links.val[index.val].to.val) f.val
    · rw [decide_eq_true forward]
      simp only [↓reduceIte]
      congr 1
      symm
      rw [decide_eq_true_iff]
      exact ⟨_,List.mem_cons_self ..,.inl forward⟩
    · rw [decide_eq_false forward]
      by_cases backward : P.links.val[index.val].to = x ∧ P.links.val[index.val].from.val < nodes.val.length ∧
          Below h (inv P.links.val[index.val].role) r ∧
          Holds P.entries.val (labelOf nodes.val P.links.val[index.val].from.val) f.val
      · rw [decide_eq_true backward]
        simp only [Bool.false_eq_true,↓reduceIte]
        congr 1
        symm
        rw [decide_eq_true_iff]
        exact ⟨_,List.mem_cons_self ..,.inr backward⟩
      · rw [decide_eq_false backward]
        simp only [Bool.false_eq_true,↓reduceIte,advance,bind_ok,rest]
        congr 1
        rw [decide_eq_decide]
        constructor
        · rintro ⟨l,member,found⟩
          exact ⟨l,List.mem_cons_of_mem _ member,found⟩
        · rintro ⟨l,member,found⟩
          rcases List.mem_cons.mp member with rfl | later
          · rcases found with found | found
            · exact absurd found forward
            · exact absurd found backward
          · exact ⟨l,later,found⟩
  · have empty : P.links.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by P.links.val.length - index.val
decreasing_by omega

/-- The actual witness search decides `Witnessed`. -/
theorem has_witness_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy)
    (nodes : alloc.vec.Vec completion.Node) (x : Usize) (r : ObjectPropertyExpression) (f : Usize) :
    completion.has_witness P h nodes x r f = .ok (decide (Witnessed P h nodes.val x.val r f)) := by
  rw [completion.has_witness,child_witness_correct,parent_witness_correct,link_witness_correct]
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero,zero_le,true_and]
  have iff : Witnessed P h nodes.val x.val r f ↔
      (∃ (y : Nat) (ny : completion.Node), nodes.val[y]? = some ny ∧ ny.tree = true ∧ ny.parent.val = x.val ∧
        (∃ s, createdRole P.entries.val ny = some s ∧ Below h s r) ∧ Holds P.entries.val ny.label.val f.val) ∨
      (∃ nx, nodes.val[x.val]? = some nx ∧ nx.tree = true ∧ nx.parent.val < nodes.val.length ∧
        (∃ s, createdRole P.entries.val nx = some s ∧ Below h (inv s) r) ∧
        Holds P.entries.val (labelOf nodes.val nx.parent.val) f.val) ∨
      (∃ l ∈ P.links.val, (l.from = x ∧ l.to.val < nodes.val.length ∧ Below h l.role r ∧
          Holds P.entries.val (labelOf nodes.val l.to.val) f.val) ∨
        (l.to = x ∧ l.from.val < nodes.val.length ∧ Below h (inv l.role) r ∧
          Holds P.entries.val (labelOf nodes.val l.from.val) f.val)) := by
    constructor
    · rintro ⟨y,neighbour,holds⟩
      rcases neighbour with ⟨ny,at_y,tree,parent,role⟩ | ⟨nx,at_x,tree,parent,yIn,role⟩ |
          ⟨l,member,source,target,yIn,included⟩ | ⟨l,member,target,source,yIn,included⟩
      · have label : labelOf nodes.val y = ny.label.val := by simp [labelOf,at_y]
        exact .inl ⟨y,ny,at_y,tree,parent,role,by rw [← label]; exact holds⟩
      · exact .inr (.inl ⟨nx,at_x,tree,by rw [parent]; exact yIn,role,by rw [parent]; exact holds⟩)
      · exact .inr (.inr ⟨l,member,.inl ⟨UScalar.eq_of_val_eq source,by rw [target]; exact yIn,included,
          by rw [target]; exact holds⟩⟩)
      · exact .inr (.inr ⟨l,member,.inr ⟨UScalar.eq_of_val_eq target,by rw [source]; exact yIn,included,
          by rw [source]; exact holds⟩⟩)
    · rintro (⟨y,ny,at_y,tree,parent,role,holds⟩ | ⟨nx,at_x,tree,parentIn,role,holds⟩ |
          ⟨l,member,⟨source,target,included,holds⟩ | ⟨target,source,included,holds⟩⟩)
      · have label : labelOf nodes.val y = ny.label.val := by simp [labelOf,at_y]
        exact ⟨y,.inl ⟨ny,at_y,tree,parent,role⟩,by rw [label]; exact holds⟩
      · exact ⟨nx.parent.val,.inr (.inl ⟨nx,at_x,tree,rfl,parentIn,role⟩),holds⟩
      · exact ⟨l.to.val,.inr (.inr (.inl ⟨l,member,by rw [source],rfl,target,included⟩)),holds⟩
      · exact ⟨l.from.val,.inr (.inr (.inr ⟨l,member,by rw [target],rfl,source,included⟩)),holds⟩
  by_cases child : ∃ (y : Nat) (ny : completion.Node), nodes.val[y]? = some ny ∧ ny.tree = true ∧ ny.parent.val = x.val ∧
      (∃ s, createdRole P.entries.val ny = some s ∧ Below h s r) ∧ Holds P.entries.val ny.label.val f.val
  · rw [decide_eq_true child]
    simp only [bind_ok,↓reduceIte]
    congr 1
    symm
    rw [decide_eq_true_iff]
    exact iff.mpr (.inl child)
  · rw [decide_eq_false child]
    by_cases parent : ∃ nx, nodes.val[x.val]? = some nx ∧ nx.tree = true ∧ nx.parent.val < nodes.val.length ∧
        (∃ s, createdRole P.entries.val nx = some s ∧ Below h (inv s) r) ∧
        Holds P.entries.val (labelOf nodes.val nx.parent.val) f.val
    · rw [decide_eq_true parent]
      simp only [bind_ok,Bool.false_eq_true,↓reduceIte]
      congr 1
      symm
      rw [decide_eq_true_iff]
      exact iff.mpr (.inr (.inl parent))
    · rw [decide_eq_false parent]
      simp only [bind_ok,Bool.false_eq_true,↓reduceIte]
      congr 1
      rw [decide_eq_decide]
      constructor
      · intro link
        exact iff.mpr (.inr (.inr link))
      · intro witnessed
        rcases iff.mp witnessed with found | found | found
        · exact absurd found child
        · exact absurd found parent
        · exact found
theorem missing_witness_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy)
    (nodes : alloc.vec.Vec completion.Node) (x index : Usize) :
    ∃ r, completion.missing_witness P h nodes x index = .ok r ∧
      (∀ i, r = some i → i ∈ (labelOf nodes.val x.val).drop index.val ∧ ∃ role f,
        P.entries.val[i.val]? = some (.Exists role f) ∧ ¬ Witnessed P h nodes.val x.val role f) ∧
      (r = none → ∀ i ∈ (labelOf nodes.val x.val).drop index.val, ∀ role f,
        P.entries.val[i.val]? = some (.Exists role f) → Witnessed P h nodes.val x.val role f) := by
  rw [completion.missing_witness]
  by_cases inside : x.val < nodes.val.length
  · have lookup : nodes.index_usize x = .ok nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have label : labelOf nodes.val x.val = nodes.val[x.val].label.val := by
      simp [labelOf,List.getElem?_eq_getElem inside]
    rw [label]
    by_cases more : index.val < nodes.val[x.val].label.val.length
    · have itemLookup : nodes.val[x.val].label.index_usize index = .ok nodes.val[x.val].label.val[index.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
      have split : nodes.val[x.val].label.val.drop index.val =
          nodes.val[x.val].label.val[index.val] :: nodes.val[x.val].label.val.drop (index.val+1) :=
        List.drop_eq_getElem_cons more
      obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val+1 := by simpa using indexValue
      obtain ⟨r,run,found,absent⟩ := missing_witness_correct P h nodes x index'
      rw [nextIndex,label] at found absent
      have later : ∀ i, r = some i → i ∈ nodes.val[x.val].label.val.drop index.val ∧ ∃ role f,
          P.entries.val[i.val]? = some (.Exists role f) ∧ ¬ Witnessed P h nodes.val x.val role f := by
        intro i same
        obtain ⟨member,rest⟩ := found i same
        exact ⟨by rw [split]; exact List.mem_cons_of_mem _ member,rest⟩
      have item := nodes.val[x.val].label.val[index.val]
      by_cases itemIn : nodes.val[x.val].label.val[index.val].val < P.entries.val.length
      · have entryLookup : P.entries.index_usize nodes.val[x.val].label.val[index.val] =
            .ok P.entries.val[nodes.val[x.val].label.val[index.val].val] := by
          simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem itemIn]
        have at_item := List.getElem?_eq_getElem itemIn
        cases entry : P.entries.val[nodes.val[x.val].label.val[index.val].val] with
        | Exists role f =>
          rw [entry] at at_item
          by_cases witnessed : Witnessed P h nodes.val x.val role f
          · refine ⟨r,?_,later,?_⟩
            · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
                lookup,bind_ok,more,itemLookup,itemIn,entryLookup,entry,has_witness_correct,witnessed,decide_true,
                Bool.not_true,Bool.false_eq_true,advance,run]
              simp [advance,run]
            · intro none i member role' f' at_i
              rw [split] at member
              rcases List.mem_cons.mp member with rfl | rest
              · rw [at_item] at at_i
                simp only [Option.some.injEq,concept_table.Entry.Exists.injEq] at at_i
                obtain ⟨rfl,rfl⟩ := at_i
                exact witnessed
              · exact absent none i rest role' f' at_i
          · refine ⟨some nodes.val[x.val].label.val[index.val],?_,?_,by simp⟩
            · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
                lookup,bind_ok,more,itemLookup,itemIn,entryLookup,entry,has_witness_correct,witnessed,decide_false,
                Bool.not_false]
              simp
            · intro i same
              cases same
              exact ⟨by rw [split]; exact List.mem_cons_self ..,role,f,at_item,witnessed⟩
        | _ =>
          rw [entry] at at_item
          refine ⟨r,?_,later,?_⟩
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemIn,entryLookup,entry,
              advance,run]
          · intro none i member role' f' at_i
            rw [split] at member
            rcases List.mem_cons.mp member with rfl | rest
            · rw [at_item] at at_i; cases at_i
            · exact absent none i rest role' f' at_i
      · refine ⟨r,?_,later,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,more,itemLookup,itemIn,Bool.false_eq_true,advance,run]
        · intro none i member role' f' at_i
          rw [split] at member
          rcases List.mem_cons.mp member with rfl | rest
          · rw [List.getElem?_eq_none_iff.mpr (by omega)] at at_i; cases at_i
          · exact absent none i rest role' f' at_i
    · refine ⟨none,?_,by simp,?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more]
      · intro _ i member
        rw [List.drop_eq_nil_iff.mpr (by omega)] at member
        cases member
  · have label : labelOf nodes.val x.val = [] := by
      simp [labelOf,List.getElem?_eq_none_iff.mpr (show nodes.val.length ≤ x.val by omega)]
    rw [label]
    refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],by simp,by simp⟩
termination_by (labelOf nodes.val x.val).length - index.val
decreasing_by
  simp only [labelOf,List.getElem?_eq_getElem inside]
  omega

/-- Two labels list the same items. -/
def SameLabel (L L' : List Usize) : Prop := ∀ i, i ∈ L ↔ i ∈ L'

/-- The tree nodes from `x` up to its named root, nearest first, following
    parents with smaller indices. -/
def treePath (nodes : List completion.Node) (x : Nat) : List Nat :=
  match nodes[x]? with
  | some n =>
    if n.tree = true then
      if _below : n.parent.val < x then x :: treePath nodes n.parent.val else [x]
    else []
  | none => []
termination_by x

/-- Blocking along tree paths: some tree node on the path from `x` to its named
    root has the label of a tree node above it. -/
def PathBlocked (nodes : List completion.Node) (x : Nat) : Prop :=
  match nodes[x]? with
  | some n =>
    if _below : n.parent.val < x then
      n.tree = true ∧ ((∃ v ∈ treePath nodes n.parent.val, SameLabel (labelOf nodes x) (labelOf nodes v)) ∨
        PathBlocked nodes n.parent.val)
    else False
  | none => False
termination_by x

/-- Anywhere equality blocking: a tree node is blocked when its parent is, or
    when an earlier tree node that is not blocked has a label of the same length
    with the same items. -/
def Blocked (nodes : List completion.Node) (x : Nat) : Prop :=
  match nodes[x]? with
  | some n =>
    if _below : n.parent.val < x then
      n.tree = true ∧ (Blocked nodes n.parent.val ∨
        ∃ v, ∃ _ : v < x, (∃ m, nodes[v]? = some m ∧ m.tree = true) ∧ ¬ Blocked nodes v ∧
          (labelOf nodes v).length = (labelOf nodes x).length ∧ SameLabel (labelOf nodes x) (labelOf nodes v))
    else False
  | none => False
termination_by x

/-- `v` blocks `x` by the flags: a tree node whose flag says unblocked, with a
    label of the same length and items as `x`'s. -/
def FlagBlocks (nodes : List completion.Node) (flags : List Bool) (x v : Nat) : Prop :=
  x < nodes.length ∧ (∃ m, nodes[v]? = some m ∧ m.tree = true) ∧ flags[v]? = some false ∧
    (labelOf nodes v).length = (labelOf nodes x).length ∧ SameLabel (labelOf nodes x) (labelOf nodes v)

theorem blocks_correct (nodes : alloc.vec.Vec completion.Node) (flags : alloc.vec.Vec Bool) (node v : Usize) :
    ∃ b, completion.blocks nodes flags node v = .ok b ∧ (b = true ↔ FlagBlocks nodes.val flags.val node.val v.val) := by
  rw [completion.blocks]
  by_cases nodeIn : node.val < nodes.val.length
  · by_cases vIn : v.val < nodes.val.length
    · by_cases vFlag : v.val < flags.val.length
      · have atV := List.getElem?_eq_getElem vIn
        have atF := List.getElem?_eq_getElem vFlag
        have lookupV : nodes.index_usize v = .ok nodes.val[v.val] := by simp [alloc.vec.Vec.index_usize, atV]
        have lookupN : nodes.index_usize node = .ok nodes.val[node.val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem nodeIn]
        have lookupF : flags.index_usize v = .ok flags.val[v.val] := by simp [alloc.vec.Vec.index_usize, atF]
        have labelV : labelOf nodes.val v.val = nodes.val[v.val].label.val := by simp [labelOf, atV]
        have labelN : labelOf nodes.val node.val = nodes.val[node.val].label.val := by
          simp [labelOf, List.getElem?_eq_getElem nodeIn]
        by_cases tree : nodes.val[v.val].tree = true
        · cases flag : flags.val[v.val] with
          | true =>
            refine ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nodeIn, vIn, vFlag, lookupV, lookupF,
              tree, flag], ?_⟩
            simp only [Bool.false_eq_true, false_iff]
            rintro ⟨_, _, flagFalse, _⟩
            rw [atF, flag] at flagFalse
            cases flagFalse
          | false =>
            by_cases lengths : nodes.val[v.val].label.val.length = nodes.val[node.val].label.val.length
            · refine ⟨decide (∀ i, i ∈ nodes.val[node.val].label.val ↔ i ∈ nodes.val[v.val].label.val),
                by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nodeIn, vIn, vFlag, lookupV, lookupN, lookupF, tree,
                  flag, lengths, same_label_correct], ?_⟩
              rw [decide_eq_true_iff]
              constructor
              · intro same
                refine ⟨nodeIn, ⟨_, atV, tree⟩, by rw [atF, flag], by rw [labelV, labelN]; exact lengths, ?_⟩
                rw [labelN, labelV]
                exact same
              · rintro ⟨_, _, _, _, same⟩
                rw [labelN, labelV] at same
                exact same
            · refine ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nodeIn, vIn, vFlag, lookupV, lookupN,
                lookupF, tree, flag, lengths], ?_⟩
              simp only [Bool.false_eq_true, false_iff]
              rintro ⟨_, _, _, sameLength, _⟩
              rw [labelV, labelN] at sameLength
              exact lengths sameLength
        · refine ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nodeIn, vIn, vFlag, lookupV, tree], ?_⟩
          simp only [Bool.false_eq_true, false_iff]
          rintro ⟨_, ⟨m, at_m, mTree⟩, _⟩
          rw [atV] at at_m
          cases Option.some.inj at_m
          exact tree mTree
      · refine ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nodeIn, vIn, vFlag], ?_⟩
        simp only [Bool.false_eq_true, false_iff]
        rintro ⟨_, _, flagFalse, _⟩
        rw [List.getElem?_eq_none (by omega)] at flagFalse
        cases flagFalse
    · refine ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nodeIn, vIn], ?_⟩
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨_, ⟨m, at_m, _⟩, _⟩
      rw [List.getElem?_eq_none (by omega)] at at_m
      cases at_m
  · refine ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, nodeIn], ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨inside, _⟩
    exact nodeIn inside

theorem repeated_before_correct (nodes : alloc.vec.Vec completion.Node) (flags : alloc.vec.Vec Bool) (node v : Usize) :
    ∃ b, completion.repeated_before nodes flags node v = .ok b ∧
      (b = true ↔ ∃ k, v.val ≤ k ∧ k < node.val ∧ FlagBlocks nodes.val flags.val node.val k) := by
  rw [completion.repeated_before]
  by_cases more : v.val < node.val
  · obtain ⟨here, hereRun, hereSpec⟩ := blocks_correct nodes flags node v
    cases here with
    | true =>
      refine ⟨true, by simp [UScalar.lt_equiv, more, hereRun], ?_⟩
      simp only [true_iff]
      exact ⟨v.val, le_refl _, more, hereSpec.mp rfl⟩
    | false =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := v) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = v.val + 1 := by simpa using nextValue
      obtain ⟨r, run, spec⟩ := repeated_before_correct nodes flags node next
      refine ⟨r, by simp [UScalar.lt_equiv, more, hereRun, advance, run], ?_⟩
      rw [spec, nextIndex]
      constructor
      · rintro ⟨k, low, high, blocks⟩
        exact ⟨k, by omega, high, blocks⟩
      · rintro ⟨k, low, high, blocks⟩
        by_cases same : k = v.val
        · subst same
          exact absurd (hereSpec.mpr blocks) (by simp)
        · exact ⟨k, by omega, high, blocks⟩
  · refine ⟨false, by simp [UScalar.lt_equiv, more], ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨k, low, high, _⟩
    omega
termination_by node.val - v.val
decreasing_by omega

theorem flagged_correct (flags : alloc.vec.Vec Bool) (index : Usize) :
    completion.flagged flags index = .ok (decide (flags.val[index.val]? = some true)) := by
  rw [completion.flagged]
  by_cases inside : index.val < flags.val.length
  · have lookup : flags.index_usize index = .ok flags.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, List.getElem?_eq_getElem inside]
  · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, List.getElem?_eq_none (show flags.val.length ≤ index.val
      by omega)]

/-- With right flags for the nodes before it, `blocked_at` decides `Blocked`. -/
theorem blocked_at_correct (nodes : alloc.vec.Vec completion.Node) (flags : alloc.vec.Vec Bool) (x : Usize)
    (flagsOk : ∀ y < x.val, flags.val[y]? = some (decide (Blocked nodes.val y))) :
    completion.blocked_at nodes flags x = .ok (decide (Blocked nodes.val x.val)) := by
  rw [completion.blocked_at]
  by_cases inside : x.val < nodes.val.length
  · have at_x := List.getElem?_eq_getElem inside
    have lookup : nodes.index_usize x = .ok nodes.val[x.val] := by simp [alloc.vec.Vec.index_usize, at_x]
    have unfold : Blocked nodes.val x.val ↔ nodes.val[x.val].parent.val < x.val ∧ nodes.val[x.val].tree = true ∧
        (Blocked nodes.val nodes.val[x.val].parent.val ∨
          ∃ v, ∃ _ : v < x.val, (∃ m, nodes.val[v]? = some m ∧ m.tree = true) ∧ ¬ Blocked nodes.val v ∧
            (labelOf nodes.val v).length = (labelOf nodes.val x.val).length ∧
            SameLabel (labelOf nodes.val x.val) (labelOf nodes.val v)) := by
      rw [Blocked.eq_def, at_x]
      simp only
      split
      · rename_i below
        simp [below]
      · rename_i below
        simp [below]
    -- the flags say exactly which earlier nodes are blocked
    have flagMeaning : ∀ v < x.val, (flags.val[v]? = some false ↔ ¬ Blocked nodes.val v) := by
      intro v low
      rw [flagsOk v low]
      by_cases blocked : Blocked nodes.val v <;> simp [blocked]
    have repeats : ∀ b, (b = true ↔ ∃ k, 0 ≤ k ∧ k < x.val ∧ FlagBlocks nodes.val flags.val x.val k) →
        (b = true ↔ ∃ v, ∃ _ : v < x.val, (∃ m, nodes.val[v]? = some m ∧ m.tree = true) ∧ ¬ Blocked nodes.val v ∧
          (labelOf nodes.val v).length = (labelOf nodes.val x.val).length ∧
          SameLabel (labelOf nodes.val x.val) (labelOf nodes.val v)) := by
      intro b spec
      rw [spec]
      constructor
      · rintro ⟨k, _, high, _, tree, flag, lengths, same⟩
        exact ⟨k, high, tree, (flagMeaning k high).mp flag, lengths, same⟩
      · rintro ⟨k, high, tree, free, lengths, same⟩
        exact ⟨k, Nat.zero_le _, high, inside, tree, (flagMeaning k high).mpr free, lengths, same⟩
    by_cases tree : nodes.val[x.val].tree = true
    · by_cases below : nodes.val[x.val].parent.val < x.val
      · have parentFlag := flagsOk _ below
        obtain ⟨r, run, spec⟩ := repeated_before_correct nodes flags x 0#usize
        have spec' := repeats r (by simpa using spec)
        by_cases parentBlocked : Blocked nodes.val nodes.val[x.val].parent.val
        · have flagTrue : completion.flagged flags nodes.val[x.val].parent = .ok true := by
            rw [flagged_correct, parentFlag]
            simp [parentBlocked]
          rw [show (decide (Blocked nodes.val x.val)) = true from decide_eq_true
            (unfold.mpr ⟨below, tree, .inl parentBlocked⟩)]
          simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, tree, below, flagTrue]
        · have flagFalse : completion.flagged flags nodes.val[x.val].parent = .ok false := by
            rw [flagged_correct, parentFlag]
            simp [parentBlocked]
          have same : r = decide (Blocked nodes.val x.val) := by
            cases r with
            | true =>
              symm
              rw [decide_eq_true_iff]
              exact unfold.mpr ⟨below, tree, .inr (spec'.mp rfl)⟩
            | false =>
              symm
              rw [decide_eq_false_iff_not]
              intro blocked
              obtain ⟨_, _, parentOrRepeat⟩ := unfold.mp blocked
              rcases parentOrRepeat with parent | found
              · exact parentBlocked parent
              · exact absurd (spec'.mpr found) (by simp)
          rw [← same]
          simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, tree, below, flagFalse, run]
      · rw [show (decide (Blocked nodes.val x.val)) = false from decide_eq_false
          (fun blocked => below (unfold.mp blocked).1)]
        simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, tree, below]
    · rw [show (decide (Blocked nodes.val x.val)) = false from decide_eq_false
        (fun blocked => tree (unfold.mp blocked).2.1)]
      simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, tree]
  · rw [show (decide (Blocked nodes.val x.val)) = false from decide_eq_false (fun blocked => by
      rw [Blocked.eq_def, List.getElem?_eq_none (show nodes.val.length ≤ x.val by omega)] at blocked
      exact blocked)]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]

/-- The flags of every node: whether it is blocked. -/
theorem blocking_correct (nodes : alloc.vec.Vec completion.Node) (index : Usize) (out : alloc.vec.Vec Bool)
    (length : out.val.length = index.val)
    (outOk : ∀ y < index.val, out.val[y]? = some (decide (Blocked nodes.val y))) :
    ∃ r, completion.blocking nodes index out = .ok r ∧
      ∀ y < nodes.val.length, r.val[y]? = some (decide (Blocked nodes.val y)) := by
  rw [completion.blocking]
  by_cases more : index.val < nodes.val.length
  · have room : out.val.length < Usize.max := by have := nodes.property; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (decide (Blocked nodes.val index.val)) room)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, run, spec⟩ := blocking_correct nodes next pushed (by rw [contents, nextIndex]; simp [length])
      (by
        intro y low
        rw [contents]
        by_cases same : y = index.val
        · subst same
          rw [List.getElem?_append_right (by omega), length, Nat.sub_self]
          rfl
        · rw [List.getElem?_append_left (by omega)]
          exact outOk y (by omega))
    refine ⟨r, ?_, spec⟩
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, blocked_at_correct nodes out index outOk, push,
      advance, run]
  · refine ⟨out, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], ?_⟩
    intro y low
    exact outOk y (by omega)
termination_by nodes.val.length - index.val
decreasing_by omega

theorem missing_successor_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy)
    (nodes : alloc.vec.Vec completion.Node) (flags : alloc.vec.Vec Bool)
    (flagsOk : ∀ y < nodes.val.length, flags.val[y]? = some (decide (Blocked nodes.val y))) (index : Usize) :
    ∃ r, completion.missing_successor P h nodes flags index = .ok r ∧
      (∀ x i, r = some (x,i) → index.val ≤ x.val ∧ x.val < nodes.val.length ∧ ¬ Blocked nodes.val x.val ∧
        i ∈ labelOf nodes.val x.val ∧ ∃ role f, P.entries.val[i.val]? = some (.Exists role f) ∧
          ¬ Witnessed P h nodes.val x.val role f) ∧
      (r = none → ∀ y, index.val ≤ y → y < nodes.val.length → ¬ Blocked nodes.val y →
        ∀ i ∈ labelOf nodes.val y, ∀ role f, P.entries.val[i.val]? = some (.Exists role f) →
          Witnessed P h nodes.val y role f) := by
  rw [completion.missing_successor]
  by_cases more : index.val < nodes.val.length
  · obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := missing_successor_correct P h nodes flags flagsOk index'
    rw [nextIndex] at found absent
    have later : ∀ x i, r = some (x,i) → index.val ≤ x.val ∧ x.val < nodes.val.length ∧ ¬ Blocked nodes.val x.val ∧
        i ∈ labelOf nodes.val x.val ∧ ∃ role f, P.entries.val[i.val]? = some (.Exists role f) ∧
          ¬ Witnessed P h nodes.val x.val role f := by
      intro x i same
      obtain ⟨low,rest⟩ := found x i same
      exact ⟨by omega,rest⟩
    obtain ⟨w,wRun,wFound,wAbsent⟩ := missing_witness_correct P h nodes index 0#usize
    simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at wFound wAbsent
    cases w with
    | none =>
      refine ⟨r,?_,later,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,wRun,bind_ok,advance,run]
      · intro none y low high notBlocked
        by_cases same : y = index.val
        · subst same; exact wAbsent rfl
        · exact absent none y (by omega) high notBlocked
    | some i =>
      by_cases blocked : Blocked nodes.val index.val
      · refine ⟨r,?_,later,?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,wRun,flagged_correct,flagsOk index.val more,blocked,
            advance,run]
        · intro none y low high notBlocked
          by_cases same : y = index.val
          · subst same; exact absurd blocked notBlocked
          · exact absent none y (by omega) high notBlocked
      · refine ⟨some (index,i),?_,?_,by simp⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,wRun,flagged_correct,flagsOk index.val more,blocked]
        · intro x i' same
          simp only [Option.some.injEq,Prod.mk.injEq] at same
          obtain ⟨rfl,rfl⟩ := same
          obtain ⟨member,rest⟩ := wFound i rfl
          exact ⟨le_refl _,more,blocked,member,rest⟩
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ y low high
    omega
termination_by nodes.val.length - index.val
decreasing_by omega
/-- An entry that node `x` needs: something the node needs itself, or something
    an edge requires of it from the other end. -/
def Needs (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node) (x : Nat)
    (c : Usize) : Prop :=
  NodeNeeds P (labelOf nodes x) x c ∨
  (∃ l ∈ P.links.val, l.from.val < nodes.length ∧ l.to.val < nodes.length ∧
    ((x = l.to.val ∧ EdgeNeeds P.entries.val h (labelOf nodes l.from.val) l.role c) ∨
      (x = l.from.val ∧ EdgeNeeds P.entries.val h (labelOf nodes l.to.val) (inv l.role) c))) ∨
  (∃ y n s, nodes[y]? = some n ∧ n.tree = true ∧ createdRole P.entries.val n = some s ∧
    n.parent.val < nodes.length ∧
    ((x = y ∧ EdgeNeeds P.entries.val h (labelOf nodes n.parent.val) s c) ∨
      (x = n.parent.val ∧ EdgeNeeds P.entries.val h (labelOf nodes y) (inv s) c)))

/-- No rule applies: every node satisfies what it needs, every edge is
    satisfied in both directions, and every existential restriction of an
    unblocked node has a witness. -/
def Complete (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node) : Prop :=
  (∀ y < nodes.length, NodeOk P (labelOf nodes y) y) ∧
  (∀ l ∈ P.links.val, l.from.val < nodes.length → l.to.val < nodes.length →
    EdgeOk P.entries.val h (labelOf nodes l.from.val) l.role (labelOf nodes l.to.val) ∧
    EdgeOk P.entries.val h (labelOf nodes l.to.val) (inv l.role) (labelOf nodes l.from.val)) ∧
  (∀ y n s, nodes[y]? = some n → n.tree = true → createdRole P.entries.val n = some s →
    n.parent.val < nodes.length →
    EdgeOk P.entries.val h (labelOf nodes n.parent.val) s (labelOf nodes y) ∧
    EdgeOk P.entries.val h (labelOf nodes y) (inv s) (labelOf nodes n.parent.val)) ∧
  (∀ x < nodes.length, ¬ Blocked nodes x → ∀ i ∈ labelOf nodes x, ∀ r f,
    P.entries.val[i.val]? = some (.Exists r f) → Witnessed P h nodes x r f)

/-- The search for missing work returns a node and an entry it needs and lacks:
    an unmet requirement of an individual, found in one pass over the
    requirements, else what a link or a tree edge requires of one of its ends,
    else what the first node misses locally; when it returns nothing, every node
    has what it needs and every edge is satisfied in both directions. -/
theorem missing_work_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy)
    (nodes : alloc.vec.Vec completion.Node) (triggers : TriggersOk P) :
    ∃ r, completion.missing_work P h nodes = .ok r ∧
      (∀ x c, r = some (x,c) → x.val < nodes.val.length ∧ Needs P h nodes.val x.val c ∧
        ¬ Holds P.entries.val (labelOf nodes.val x.val) c.val) ∧
      (r = none → (∀ y < nodes.val.length, NodeOk P (labelOf nodes.val y) y) ∧
        (∀ l ∈ P.links.val, l.from.val < nodes.val.length → l.to.val < nodes.val.length →
          EdgeOk P.entries.val h (labelOf nodes.val l.from.val) l.role (labelOf nodes.val l.to.val) ∧
          EdgeOk P.entries.val h (labelOf nodes.val l.to.val) (inv l.role) (labelOf nodes.val l.from.val)) ∧
        (∀ y n s, nodes.val[y]? = some n → n.tree = true → createdRole P.entries.val n = some s →
          n.parent.val < nodes.val.length →
          EdgeOk P.entries.val h (labelOf nodes.val n.parent.val) s (labelOf nodes.val y) ∧
          EdgeOk P.entries.val h (labelOf nodes.val y) (inv s) (labelOf nodes.val n.parent.val))) := by
  rw [completion.missing_work]
  obtain ⟨r1,run1,found1,absent1⟩ := missing_requirement_correct P nodes 0#usize
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at found1 absent1
  cases r1 with
  | some pair =>
    obtain ⟨x,c⟩ := pair
    refine ⟨some (x,c),by simp [run1],?_,by simp⟩
    intro x' c' same
    simp only [Option.some.injEq,Prod.mk.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    obtain ⟨inside,⟨q,member,at_q,value⟩,fails⟩ := found1 x c rfl
    exact ⟨inside,.inl (.inl ⟨q,member,by rw [at_q],value⟩),fails⟩
  | none =>
    obtain ⟨link,linkRun,linkFound,linkAbsent⟩ := missing_link_correct P h nodes 0#usize
    simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at linkFound linkAbsent
    cases link with
    | some pair =>
      obtain ⟨x,c⟩ := pair
      refine ⟨some (x,c),by simp [run1,linkRun],?_,by simp⟩
      intro x' c' same
      simp only [Option.some.injEq,Prod.mk.injEq] at same
      obtain ⟨rfl,rfl⟩ := same
      obtain ⟨l,member,sourceIn,targetIn,kind⟩ := linkFound x c rfl
      rcases kind with ⟨rfl,needs,missing⟩ | ⟨rfl,needs,missing⟩
      · exact ⟨targetIn,.inr (.inl ⟨l,member,sourceIn,targetIn,.inl ⟨rfl,needs⟩⟩),missing⟩
      · exact ⟨sourceIn,.inr (.inl ⟨l,member,sourceIn,targetIn,.inr ⟨rfl,needs⟩⟩),missing⟩
    | none =>
      have linksOk := linkAbsent rfl
      obtain ⟨tree,treeRun,treeFound,treeAbsent⟩ := missing_tree_correct P h nodes 0#usize
      cases tree with
      | some pair =>
        obtain ⟨x,c⟩ := pair
        refine ⟨some (x,c),by simp [run1,linkRun,treeRun],?_,by simp⟩
        intro x' c' same
        simp only [Option.some.injEq,Prod.mk.injEq] at same
        obtain ⟨rfl,rfl⟩ := same
        obtain ⟨y,n,s,_,at_y,isTree,role,parentIn,kind⟩ := treeFound x c rfl
        have yIn : y < nodes.val.length := (List.getElem?_eq_some_iff.mp at_y).1
        rcases kind with ⟨same,needs,missing⟩ | ⟨rfl,needs,missing⟩
        · refine ⟨by rw [same]; exact yIn,.inr (.inr ⟨y,n,s,at_y,isTree,role,parentIn,.inl ⟨same,needs⟩⟩),?_⟩
          rw [same]; exact missing
        · exact ⟨parentIn,.inr (.inr ⟨y,n,s,at_y,isTree,role,parentIn,.inr ⟨rfl,needs⟩⟩),missing⟩
      | none =>
        have treesOk := treeAbsent rfl
        obtain ⟨r2,run2,found2,absent2⟩ := missing_local_correct P nodes 0#usize triggers
        refine ⟨r2,by simp [run1,linkRun,treeRun,run2],?_,?_⟩
        · intro x c same
          obtain ⟨inside,needs,fails⟩ := found2 x c same
          exact ⟨inside,.inl (.inr needs),fails⟩
        · intro none
          refine ⟨?_,linksOk,fun y n s at_y isTree role parentIn =>
            treesOk y n s (Nat.zero_le _) at_y isTree role parentIn⟩
          intro y inside c needs
          rcases needs with ⟨q,member,at_q,rfl⟩ | localNeeds
          · rw [← at_q] at inside ⊢
            exact absent1 rfl q member inside
          · exact absent2 none y (Nat.zero_le _) inside c localNeeds

/-- The rule search returns a node and an entry it needs and lacks, else an
    unblocked node with an existential restriction without a witness, else
    `Done`, and then no rule applies. -/
theorem next_step_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : alloc.vec.Vec completion.Node)
    (triggers : TriggersOk P) :
    ∃ s, completion.next_step P h nodes = .ok s ∧
      (∀ x c, s = .Add x c → x.val < nodes.val.length ∧ Needs P h nodes.val x.val c ∧
        ¬ Holds P.entries.val (labelOf nodes.val x.val) c.val) ∧
      (∀ x i, s = .Create x i → x.val < nodes.val.length ∧ ¬ Blocked nodes.val x.val ∧ i ∈ labelOf nodes.val x.val ∧
        ∃ r f, P.entries.val[i.val]? = some (.Exists r f) ∧ ¬ Witnessed P h nodes.val x.val r f) ∧
      (s = .Done → Complete P h nodes.val) := by
  rw [completion.next_step]
  obtain ⟨work,workRun,workFound,workAbsent⟩ := missing_work_correct P h nodes triggers
  cases work with
  | some pair =>
    obtain ⟨x,c⟩ := pair
    refine ⟨.Add x c,by simp [workRun],?_,by simp,by simp⟩
    intro x' c' same
    simp only [completion.Step.Add.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    exact workFound x c rfl
  | none =>
    obtain ⟨nodesOk,linksOk,treesOk⟩ := workAbsent rfl
    obtain ⟨flags,flagsRun,flagsOk⟩ := blocking_correct nodes 0#usize (alloc.vec.Vec.new Bool) (by simp)
      (by intro y low; simp at low)
    obtain ⟨successor,successorRun,successorFound,successorAbsent⟩ :=
      missing_successor_correct P h nodes flags flagsOk 0#usize
    cases successor with
    | some pair =>
      obtain ⟨x,i⟩ := pair
      refine ⟨.Create x i,by simp [workRun,flagsRun,successorRun],by simp,?_,by simp⟩
      intro x' i' same
      simp only [completion.Step.Create.injEq] at same
      obtain ⟨rfl,rfl⟩ := same
      obtain ⟨_,rest⟩ := successorFound x i rfl
      exact rest
    | none =>
      refine ⟨.Done,by simp [workRun,flagsRun,successorRun],by simp,by simp,?_⟩
      intro _
      exact ⟨nodesOk,linksOk,treesOk,
        fun x xIn notBlocked => successorAbsent rfl x (Nat.zero_le _) xIn notBlocked⟩
end Rowl.CompletionSearch
