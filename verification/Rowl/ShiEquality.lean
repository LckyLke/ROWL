import Rowl.AlcOntology

/-!
The individual equalities and inequalities of the ontology queries. Every member
of a `SameIndividual` or `DifferentIndividuals` axiom gets a node, and the nodes
of the members of each equality are joined under one representative by a union
of classes. Every node's representative is joined to the node by a chain of
equalities, so every OWL model gives a node and its representative one element,
and the members of each equality share their representative. The checks for an
inequality two of whose members share a representative, and for inequalities at
all, are exact.
-/
namespace Rowl.ShiEquality
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.AlcOntology (PositionOf positionOf_le position_of intern_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe w

/-- The individuals of an equality or inequality. -/
def MembersOf : Axiom → List Individual
  | .SameIndividual xs => xs.elements
  | .DifferentIndividuals xs => xs.elements
  | _ => []

/-- An individual inequality. -/
def Different : Axiom → Prop
  | .DifferentIndividuals _ => True
  | _ => False

/-- The positions of two members of one equality. -/
noncomputable def Equal (items : List AnnotatedAxiom) (nodes : List Individual) (i j : Nat) : Prop :=
  ∃ item ∈ items, ∃ xs, item.axiom = .SameIndividual xs ∧ ∃ a ∈ xs.elements, ∃ b ∈ xs.elements,
    PositionOf nodes a = i ∧ PositionOf nodes b = j

/-- The representative of a node: its entry, or the node itself outside the list. -/
def Representative (same : List Usize) (n : Nat) : Nat :=
  match same[n]? with
  | some b => b.val
  | none => n

/-- The node of an individual: the representative of its position. -/
noncomputable def RepOf (same : List Usize) (nodes : List Individual) (a : Individual) : Nat :=
  Representative same (PositionOf nodes a)

/-- Representatives of `count` nodes, each a node that a chain of the pairs of
    `r` joins to its node. -/
structure Reps (r : Nat → Nat → Prop) (count : Nat) (same : List Usize) : Prop where
  length : same.length = count
  range : ∀ (k : Nat) (b : Usize), same[k]? = some b → b.val < count
  joined : ∀ (k : Nat) (b : Usize), same[k]? = some b → Relation.EqvGen r b.val k

/-- Representatives of the nodes and one more: each a node that a chain of
    equalities joins to its node, and one shared by the members of each
    equality. -/
structure Joins (items : List AnnotatedAxiom) (nodes : List Individual) (same : List Usize) : Prop where
  reps : Reps (Equal items nodes) (nodes.length + 1) same
  equal : ∀ item ∈ items, ∀ xs, item.axiom = .SameIndividual xs → ∀ a ∈ xs.elements, ∀ b ∈ xs.elements,
    RepOf same nodes a = RepOf same nodes b

/-- An inequality two of whose members share a node. -/
noncomputable def Clashes (same : List Usize) (nodes : List Individual) : Axiom → Prop
  | .DifferentIndividuals xs => ¬ xs.elements.Pairwise (fun a b => RepOf same nodes a ≠ RepOf same nodes b)
  | _ => False

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- Interning the remaining members keeps every node, adds each of them, and
    leaves room for one more node. -/
theorem intern_rest_correct (nodes rest : alloc.vec.Vec Individual) (index : Usize)
    (room : nodes.val.length ≤ Usize.max-1) :
    ∃ result, shi_ontology.intern_rest nodes rest index = .ok result ∧ ∀ final, result = some final →
      (∀ b ∈ nodes.val, b ∈ final.val) ∧ (∀ a ∈ rest.val.drop index.val, a ∈ final.val) ∧
      final.val.length ≤ Usize.max-1 := by
  rw [shi_ontology.intern_rest]
  by_cases more : index.val < rest.val.length
  · have lookup : rest.index_usize index = .ok rest.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : rest.val.drop index.val = rest.val[index.val] :: rest.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨interned,internRun,internSpec⟩ := intern_correct nodes rest.val[index.val] room
    cases interned with
    | none =>
      exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,internRun],
        by intro final impossible; cases impossible⟩
    | some grown =>
      obtain ⟨kept,added,grownRoom⟩ := internSpec grown rfl
      obtain ⟨result,run,spec⟩ := intern_rest_correct grown rest next grownRoom
      refine ⟨result,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,internRun,advance,run],?_⟩
      intro final same
      obtain ⟨keptLater,restIn,finalRoom⟩ := spec final same
      refine ⟨fun b member => keptLater b (kept b member),?_,finalRoom⟩
      intro a member
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact keptLater _ added
      · rw [nextIndex] at restIn
        exact restIn a later
  · have empty : rest.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some nodes,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro final same
    cases same
    exact ⟨fun b member => member,by simp [empty],room⟩
termination_by rest.val.length - index.val
decreasing_by omega

/-- Interning the members of an equality or inequality keeps every node, adds
    each member, and leaves room for one more node. -/
theorem intern_members_correct (nodes : alloc.vec.Vec Individual) (members : AtLeastTwo Individual)
    (room : nodes.val.length ≤ Usize.max-1) :
    ∃ result, shi_ontology.intern_members nodes members = .ok result ∧ ∀ final, result = some final →
      (∀ b ∈ nodes.val, b ∈ final.val) ∧ (∀ a ∈ members.elements, a ∈ final.val) ∧
      final.val.length ≤ Usize.max-1 := by
  rw [shi_ontology.intern_members]
  obtain ⟨one,oneRun,oneSpec⟩ := intern_correct nodes members.first room
  cases one with
  | none => exact ⟨none,by simp [oneRun],by intro final impossible; cases impossible⟩
  | some first =>
    obtain ⟨keptOne,addedOne,roomOne⟩ := oneSpec first rfl
    obtain ⟨two,twoRun,twoSpec⟩ := intern_correct first members.second roomOne
    cases two with
    | none => exact ⟨none,by simp [oneRun,twoRun],by intro final impossible; cases impossible⟩
    | some second =>
      obtain ⟨keptTwo,addedTwo,roomTwo⟩ := twoSpec second rfl
      obtain ⟨result,run,spec⟩ := intern_rest_correct second members.rest 0#usize roomTwo
      refine ⟨result,by simp [oneRun,twoRun,run],?_⟩
      intro final same
      obtain ⟨keptRest,restIn,finalRoom⟩ := spec final same
      refine ⟨fun b member => keptRest b (keptTwo b (keptOne b member)),?_,finalRoom⟩
      intro a member
      simp only [AtLeastTwo.elements,List.mem_cons] at member
      rcases member with rfl | rfl | later
      · exact keptRest _ (keptTwo _ addedOne)
      · exact keptRest _ addedTwo
      · exact restIn a (by simpa using later)

/-- Interning the members of the equalities and inequalities keeps every node,
    adds every member, and leaves room for one more node. -/
theorem members_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize)
    (nodes : alloc.vec.Vec Individual) (room : nodes.val.length ≤ Usize.max-1) :
    ∃ result, shi_ontology.members_from items index nodes = .ok result ∧ ∀ final, result = some final →
      (∀ b ∈ nodes.val, b ∈ final.val) ∧
      (∀ item ∈ items.val.drop index.val, ∀ a ∈ MembersOf item.axiom, a ∈ final.val) ∧
      final.val.length ≤ Usize.max-1 := by
  rw [shi_ontology.members_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have tail : ∀ middle : alloc.vec.Vec Individual, (∀ b ∈ nodes.val, b ∈ middle.val) →
        (∀ a ∈ MembersOf items.val[index.val].axiom, a ∈ middle.val) → middle.val.length ≤ Usize.max-1 →
        ∃ result, shi_ontology.members_from items next middle = .ok result ∧ ∀ final, result = some final →
          (∀ b ∈ nodes.val, b ∈ final.val) ∧
          (∀ item ∈ items.val.drop index.val, ∀ a ∈ MembersOf item.axiom, a ∈ final.val) ∧
          final.val.length ≤ Usize.max-1 := by
      intro middle kept here middleRoom
      obtain ⟨result,run,spec⟩ := members_from_correct items next middle middleRoom
      refine ⟨result,run,?_⟩
      intro final same
      obtain ⟨kept',later,finalRoom⟩ := spec final same
      refine ⟨fun b member => kept' b (kept b member),?_,finalRoom⟩
      intro item member a mentioned
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | rest
      · exact kept' a (here a mentioned)
      · rw [nextIndex] at later
        exact later item rest a mentioned
    cases item : items.val[index.val].axiom with
    | SameIndividual xs =>
      obtain ⟨middle,middleRun,middleSpec⟩ := intern_members_correct nodes xs room
      cases middle with
      | none => exact ⟨none,by simp [more,lookup,item,middleRun],by intro final impossible; cases impossible⟩
      | some middle =>
        obtain ⟨kept,members,middleRoom⟩ := middleSpec middle rfl
        obtain ⟨result,run,spec⟩ := tail middle kept (by simpa [item,MembersOf] using members) middleRoom
        exact ⟨result,by simp [more,lookup,item,middleRun,advance,run],spec⟩
    | DifferentIndividuals xs =>
      obtain ⟨middle,middleRun,middleSpec⟩ := intern_members_correct nodes xs room
      cases middle with
      | none => exact ⟨none,by simp [more,lookup,item,middleRun],by intro final impossible; cases impossible⟩
      | some middle =>
        obtain ⟨kept,members,middleRoom⟩ := middleSpec middle rfl
        obtain ⟨result,run,spec⟩ := tail middle kept (by simpa [item,MembersOf] using members) middleRoom
        exact ⟨result,by simp [more,lookup,item,middleRun,advance,run],spec⟩
    | _ =>
      obtain ⟨result,run,spec⟩ := tail nodes (fun b member => member) (by simp [item,MembersOf]) room
      exact ⟨result,by simp [more,lookup,item,advance,run],spec⟩
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some nodes,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro final same
    cases same
    exact ⟨fun b member => member,by simp [empty],room⟩
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- Every node from `index` below `count` becomes its own representative after
    the ones before it. -/
theorem identity_from_correct (count index : Usize) (out : alloc.vec.Vec Usize)
    (length : out.val.length = index.val) (values : ∀ (k : Nat) (b : Usize), out.val[k]? = some b → b.val = k)
    (inside : index.val ≤ count.val) :
    ∃ result, shi_ontology.identity_from count index out = .ok result ∧ result.val.length = count.val ∧
      ∀ (k : Nat) (b : Usize), result.val[k]? = some b → b.val = k := by
  rw [shi_ontology.identity_from]
  by_cases more : index.val < count.val
  · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out index (by have := count.hBounds; scalar_tac))
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨result,run,resultLength,resultValues⟩ := identity_from_correct count next appended
      (by rw [contents,nextIndex]; simp [length])
      (by
        intro k b at_k
        rw [contents] at at_k
        by_cases old : k < out.val.length
        · rw [List.getElem?_append_left old] at at_k
          exact values k b at_k
        · rw [List.getElem?_append_right (by omega)] at at_k
          have zero : k - out.val.length = 0 := by
            by_contra nonzero
            have : [index][k - out.val.length]? = none := by simp; omega
            rw [this] at at_k
            cases at_k
          rw [zero] at at_k
          simp at at_k
          rw [← at_k]
          omega)
      (by omega)
    exact ⟨result,by simp [UScalar.lt_equiv,more,push,advance,run],resultLength,resultValues⟩
  · have full : index.val = count.val := by omega
    exact ⟨out,by simp [UScalar.lt_equiv,more],by omega,values⟩
termination_by count.val - index.val
decreasing_by omega

/-- Relabelling replaces `source` by `target` in the entries from `index` on. -/
theorem relabel_correct (same : alloc.vec.Vec Usize) (source target index : Usize) :
    ∃ result, shi_ontology.relabel same source target index = .ok result ∧
      ∀ k, result.val[k]? = (same.val[k]?).map (fun b => if index.val ≤ k ∧ b = source then target else b) := by
  rw [shi_ontology.relabel]
  by_cases more : index.val < same.val.length
  · have lookup : same.index_usize index = .ok same.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    by_cases hit : same.val[index.val] = source
    · let changed := same.set index target
      have changedVal : changed.val = same.val.set index.val target := by
        simp [changed,alloc.vec.Vec.set_val_eq]
      obtain ⟨result,run,values⟩ := relabel_correct changed source target next
      refine ⟨result,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,hit,alloc.vec.Vec.index_mut_slice_index,alloc.vec.Vec.index_mut_usize,advance]
        simpa [changed] using run
      · intro k
        rw [values k,changedVal,nextIndex]
        by_cases here : k = index.val
        · subst here
          simp [List.getElem?_set_self more,hit,List.getElem?_eq_getElem more]
        · rw [List.getElem?_set_ne (by omega)]
          have iff : index.val+1 ≤ k ↔ index.val ≤ k := by omega
          simp only [iff]
    · obtain ⟨result,run,values⟩ := relabel_correct same source target next
      refine ⟨result,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,hit,advance]
        simpa using run
      · intro k
        rw [values k,nextIndex]
        by_cases here : k = index.val
        · subst here
          simp [List.getElem?_eq_getElem more,hit]
        · have iff : index.val+1 ≤ k ↔ index.val ≤ k := by omega
          simp only [iff]
  · refine ⟨same,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro k
    cases at_k : same.val[k]? with
    | none => rfl
    | some b =>
      have : k < same.val.length := by
        by_contra outside
        rw [List.getElem?_eq_none (by omega)] at at_k
        cases at_k
      simp [show ¬ index.val ≤ k by omega]
termination_by same.val.length - index.val
decreasing_by
  all_goals
    try simp [changed,alloc.vec.Vec.set_val_eq]
    omega

/-- Uniting two nodes inside the list replaces the representative of the second
    by that of the first everywhere; otherwise nothing changes. -/
theorem unite_correct (same : alloc.vec.Vec Usize) (left right : Usize) :
    ∃ result, shi_ontology.unite same left right = .ok result ∧
      (∀ into source, same.val[left.val]? = some into → same.val[right.val]? = some source →
        result.val = same.val.map (fun b => if b = source then into else b)) ∧
      ((same.val[left.val]? = none ∨ same.val[right.val]? = none) → result = same) := by
  rw [shi_ontology.unite]
  by_cases leftIn : left.val < same.val.length
  · by_cases rightIn : right.val < same.val.length
    · have leftLookup : same.index_usize left = .ok same.val[left.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem leftIn]
      have rightLookup : same.index_usize right = .ok same.val[right.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem rightIn]
      have someLeft : same.val[left.val]? = some same.val[left.val] := List.getElem?_eq_getElem leftIn
      have someRight : same.val[right.val]? = some same.val[right.val] := List.getElem?_eq_getElem rightIn
      by_cases equal : same.val[left.val] = same.val[right.val]
      · refine ⟨same,?_,?_,?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,leftIn,rightIn,leftLookup,rightLookup,equal]
        · intro into source atLeft atRight
          rw [someLeft] at atLeft
          rw [someRight] at atRight
          cases atLeft
          cases atRight
          conv => lhs; rw [← List.map_id same.val]
          apply List.map_congr_left
          intro b _
          by_cases hit : b = same.val[right.val]
          · simp [hit,equal]
          · simp [hit]
        · intro missing
          rcases missing with none | none
          · simp [someLeft] at none
          · simp [someRight] at none
      · obtain ⟨result,run,values⟩ := relabel_correct same same.val[right.val] same.val[left.val] 0#usize
        refine ⟨result,?_,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,leftIn,rightIn,↓reduceIte,alloc.vec.Vec.index_slice_index,
            leftLookup,rightLookup,bind_ok,equal]
          exact run
        · intro into source atLeft atRight
          rw [someLeft] at atLeft
          rw [someRight] at atRight
          cases atLeft
          cases atRight
          apply List.ext_getElem?
          intro k
          rw [values k,List.getElem?_map]
          simp
        · intro missing
          rcases missing with none | none
          · simp [someLeft] at none
          · simp [someRight] at none
    · refine ⟨same,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,leftIn,rightIn],?_,fun _ => rfl⟩
      intro into source _ atRight
      rw [List.getElem?_eq_none (by omega)] at atRight
      cases atRight
  · refine ⟨same,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,leftIn],?_,fun _ => rfl⟩
    intro into source atLeft _
    rw [List.getElem?_eq_none (by omega)] at atLeft
    cases atLeft

/-- Joining two nodes that a chain relates keeps representatives, keeps every
    pair of nodes that shared a representative together, and gives the two
    nodes one representative. -/
theorem united_reps {r : Nat → Nat → Prop} {count : Nat} {same : List Usize} {left right : Nat}
    {into source : Usize} (reps : Reps r count same) (atLeft : same[left]? = some into)
    (atRight : same[right]? = some source) (pair : Relation.EqvGen r left right) :
    Reps r count (same.map (fun b => if b = source then into else b)) ∧
      (∀ (x y : Nat), same[x]? = same[y]? →
        (same.map (fun b => if b = source then into else b))[x]? =
          (same.map (fun b => if b = source then into else b))[y]?) ∧
      (same.map (fun b => if b = source then into else b))[left]? =
        (same.map (fun b => if b = source then into else b))[right]? := by
  refine ⟨⟨by simp [reps.length],?_,?_⟩,?_,?_⟩
  · intro k b at_k
    rw [List.getElem?_map] at at_k
    cases old : same[k]? with
    | none => rw [old] at at_k; cases at_k
    | some c =>
      rw [old] at at_k
      simp only [Option.map_some,Option.some.injEq] at at_k
      subst at_k
      by_cases hit : c = source
      · simp only [hit,↓reduceIte]
        exact reps.range left into atLeft
      · simp only [hit,↓reduceIte]
        exact reps.range k c old
  · intro k b at_k
    rw [List.getElem?_map] at at_k
    cases old : same[k]? with
    | none => rw [old] at at_k; cases at_k
    | some c =>
      rw [old] at at_k
      simp only [Option.map_some,Option.some.injEq] at at_k
      subst at_k
      by_cases hit : c = source
      · simp only [hit,↓reduceIte]
        have one := reps.joined left into atLeft
        have two := reps.joined right source atRight
        have three := reps.joined k c old
        rw [hit] at three
        exact .trans _ _ _ one (.trans _ _ _ pair (.trans _ _ _ (.symm _ _ two) three))
      · simp only [hit,↓reduceIte]
        exact reps.joined k c old
  · intro x y same_xy
    rw [List.getElem?_map,List.getElem?_map,same_xy]
  · rw [List.getElem?_map,List.getElem?_map,atLeft,atRight]
    by_cases hit : into = source
    · simp [hit]
    · simp [hit]

/-- Uniting the node `first` with the node of every member of `rest[index..]`,
    each related to it by a chain, keeps representatives and earlier unions, and
    gives them all one representative. -/
theorem unite_rest_correct (same : alloc.vec.Vec Usize) (nodes : alloc.vec.Vec Individual) (first : Usize)
    (rest : alloc.vec.Vec Individual) (index : Usize) {r : Nat → Nat → Prop} {count : Nat}
    (reps : Reps r count same.val) (firstIn : first.val < count)
    (pairs : ∀ a ∈ rest.val, Relation.EqvGen r first.val (PositionOf nodes.val a))
    (positions : ∀ a ∈ rest.val, PositionOf nodes.val a < count) :
    ∃ result, shi_ontology.unite_rest same nodes first rest index = .ok result ∧ Reps r count result.val ∧
      (∀ (x y : Nat), same.val[x]? = same.val[y]? → result.val[x]? = result.val[y]?) ∧
      ∀ a ∈ rest.val.drop index.val, result.val[first.val]? = result.val[PositionOf nodes.val a]? := by
  rw [shi_ontology.unite_rest]
  by_cases more : index.val < rest.val.length
  · have lookup : rest.index_usize index = .ok rest.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : rest.val.drop index.val = rest.val[index.val] :: rest.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have member : rest.val[index.val] ∈ rest.val := List.getElem_mem more
    obtain ⟨other,otherRun,otherValue⟩ := position_of nodes rest.val[index.val]
    have otherIn : other.val < count := by rw [otherValue]; exact positions _ member
    have firstLt : first.val < same.val.length := by rw [reps.length]; exact firstIn
    have otherLt : other.val < same.val.length := by rw [reps.length]; exact otherIn
    have atFirst : same.val[first.val]? = some same.val[first.val] := List.getElem?_eq_getElem firstLt
    have atOther : same.val[other.val]? = some same.val[other.val] := List.getElem?_eq_getElem otherLt
    obtain ⟨united,uniteRun,uniteValues,_⟩ := unite_correct same first other
    have unitedVal := uniteValues _ _ atFirst atOther
    obtain ⟨unitedReps,unitedKeeps,unitedJoins⟩ := united_reps reps atFirst atOther
      (by rw [otherValue]; exact pairs _ member)
    rw [← unitedVal] at unitedReps unitedKeeps unitedJoins
    obtain ⟨result,run,resultReps,resultKeeps,resultJoins⟩ :=
      unite_rest_correct united nodes first rest next unitedReps firstIn pairs positions
    refine ⟨result,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,otherRun,uniteRun,advance,run],
      resultReps,fun x y same_xy => resultKeeps x y (unitedKeeps x y same_xy),?_⟩
    intro a inRest
    rw [split] at inRest
    rcases List.mem_cons.mp inRest with rfl | later
    · rw [← otherValue]
      exact resultKeeps _ _ unitedJoins
    · rw [nextIndex] at resultJoins
      exact resultJoins a later
  · have empty : rest.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    exact ⟨same,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],reps,fun x y same_xy => same_xy,
      by simp [empty]⟩
termination_by rest.val.length - index.val
decreasing_by omega

/-- Uniting the members of the equalities of `items[index..]` keeps
    representatives and earlier unions, and gives the members of each equality
    one representative. -/
theorem equalities_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (index : Usize) (same : alloc.vec.Vec Usize) {count : Nat}
    (reps : Reps (Equal items.val nodes.val) count same.val) (wide : nodes.val.length < count) :
    ∃ result, shi_ontology.equalities_from items nodes index same = .ok result ∧
      Reps (Equal items.val nodes.val) count result.val ∧
      (∀ (x y : Nat), same.val[x]? = same.val[y]? → result.val[x]? = result.val[y]?) ∧
      ∀ item ∈ items.val.drop index.val, ∀ xs, item.axiom = .SameIndividual xs → ∀ a ∈ xs.elements,
        ∀ b ∈ xs.elements, result.val[PositionOf nodes.val a]? = result.val[PositionOf nodes.val b]? := by
  rw [shi_ontology.equalities_from]
  have positionIn : ∀ a, PositionOf nodes.val a < count := fun a => by
    have := positionOf_le nodes.val a
    omega
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have itemIn : items.val[index.val] ∈ items.val := List.getElem_mem more
    cases item : items.val[index.val].axiom with
    | SameIndividual xs =>
      have pairOf : ∀ a ∈ xs.elements, ∀ b ∈ xs.elements,
          Relation.EqvGen (Equal items.val nodes.val) (PositionOf nodes.val a) (PositionOf nodes.val b) :=
        fun a aIn b bIn => .rel _ _ ⟨items.val[index.val],itemIn,xs,item,a,aIn,b,bIn,rfl,rfl⟩
      have firstIn : xs.first ∈ xs.elements := by simp [AtLeastTwo.elements]
      have secondIn : xs.second ∈ xs.elements := by simp [AtLeastTwo.elements]
      have restIn : ∀ a ∈ xs.rest.val, a ∈ xs.elements := fun a member => by simp [AtLeastTwo.elements,member]
      obtain ⟨first,firstRun,firstValue⟩ := position_of nodes xs.first
      obtain ⟨second,secondRun,secondValue⟩ := position_of nodes xs.second
      have firstLt : first.val < same.val.length := by rw [reps.length,firstValue]; exact positionIn _
      have secondLt : second.val < same.val.length := by rw [reps.length,secondValue]; exact positionIn _
      have atFirst : same.val[first.val]? = some same.val[first.val] := List.getElem?_eq_getElem firstLt
      have atSecond : same.val[second.val]? = some same.val[second.val] := List.getElem?_eq_getElem secondLt
      obtain ⟨united,uniteRun,uniteValues,_⟩ := unite_correct same first second
      have unitedVal := uniteValues _ _ atFirst atSecond
      obtain ⟨unitedReps,unitedKeeps,unitedJoins⟩ := united_reps reps atFirst atSecond
        (by rw [firstValue,secondValue]; exact pairOf _ firstIn _ secondIn)
      rw [← unitedVal] at unitedReps unitedKeeps unitedJoins
      obtain ⟨joined,joinedRun,joinedReps,joinedKeeps,joinedJoins⟩ :=
        unite_rest_correct united nodes first xs.rest 0#usize unitedReps
          (by rw [firstValue]; exact positionIn _)
          (fun a member => by rw [firstValue]; exact pairOf _ firstIn _ (restIn a member))
          (fun a _ => positionIn a)
      obtain ⟨result,run,resultReps,resultKeeps,resultJoins⟩ :=
        equalities_from_correct items nodes next joined joinedReps wide
      refine ⟨result,?_,resultReps,fun x y same_xy => resultKeeps x y (joinedKeeps x y (unitedKeeps x y same_xy)),?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,item,firstRun,secondRun,uniteRun,joinedRun,
          advance,run]
      · have toFirst : ∀ a ∈ xs.elements, result.val[PositionOf nodes.val a]? = result.val[first.val]? := by
          intro a member
          simp only [AtLeastTwo.elements,List.mem_cons] at member
          rcases member with rfl | rfl | later
          · rw [firstValue]
          · rw [← secondValue]
            exact resultKeeps _ _ (joinedKeeps _ _ unitedJoins.symm)
          · exact (resultKeeps _ _ (joinedJoins a (by simpa using later))).symm
        intro other member ys statement a aIn b bIn
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · rw [item] at statement
          cases statement
          rw [toFirst a aIn,toFirst b bIn]
        · rw [nextIndex] at resultJoins
          exact resultJoins other later ys statement a aIn b bIn
    | _ =>
      obtain ⟨result,run,resultReps,resultKeeps,resultJoins⟩ :=
        equalities_from_correct items nodes next same reps wide
      refine ⟨result,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,item,advance,run],resultReps,
        resultKeeps,?_⟩
      intro other member ys statement a aIn b bIn
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | later
      · rw [item] at statement
        cases statement
      · rw [nextIndex] at resultJoins
        exact resultJoins other later ys statement a aIn b bIn
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    exact ⟨same,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],reps,fun x y same_xy => same_xy,
      by simp [empty]⟩
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- A representative lookup is exact. -/
theorem representative_correct (same : alloc.vec.Vec Usize) (n : Usize) :
    ∃ r, shi_ontology.representative same n = .ok r ∧ r.val = Representative same.val n.val := by
  rw [shi_ontology.representative]
  by_cases inside : n.val < same.val.length
  · have lookup : same.index_usize n = .ok same.val[n.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    refine ⟨same.val[n.val],by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup],?_⟩
    simp [Representative,List.getElem?_eq_getElem inside]
  · refine ⟨n,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],?_⟩
    simp [Representative,List.getElem?_eq_none (show same.val.length ≤ n.val by omega)]

/-- The node of an individual is the representative of its position. -/
theorem node_of_correct (nodes : alloc.vec.Vec Individual) (same : alloc.vec.Vec Usize) (a : Individual) :
    ∃ r, shi_ontology.node_of nodes same a = .ok r ∧ r.val = RepOf same.val nodes.val a := by
  obtain ⟨p,pRun,pValue⟩ := position_of nodes a
  obtain ⟨r,rRun,rValue⟩ := representative_correct same p
  refine ⟨r,by rw [shi_ontology.node_of]; simp [pRun,rRun],?_⟩
  rw [rValue,pValue]
  rfl

/-- The representatives of the nodes of a closure: every node starts as its own
    representative, and the members of every equality are united. -/
theorem joins_of (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual) (count : Usize)
    (countIs : count.val = nodes.val.length + 1) :
    ∃ start same, shi_ontology.identity_from count 0#usize (alloc.vec.Vec.new Usize) = .ok start ∧
      shi_ontology.equalities_from items nodes 0#usize start = .ok same ∧ Joins items.val nodes.val same.val := by
  obtain ⟨start,startRun,startLength,startValues⟩ := identity_from_correct count 0#usize
    (alloc.vec.Vec.new Usize) (by simp) (by simp) (by simp)
  have startReps : Reps (Equal items.val nodes.val) (nodes.val.length + 1) start.val := by
    refine ⟨by omega,?_,?_⟩
    · intro k b at_k
      have value := startValues k b at_k
      have : k < start.val.length := by
        by_contra outside
        rw [List.getElem?_eq_none (by omega)] at at_k
        cases at_k
      omega
    · intro k b at_k
      rw [startValues k b at_k]
      exact .refl _
  obtain ⟨same,sameRun,sameReps,_,sameJoins⟩ := equalities_from_correct items nodes 0#usize start startReps
    (by omega)
  refine ⟨start,same,startRun,sameRun,sameReps,?_⟩
  intro item member xs statement a aIn b bIn
  have equal := sameJoins item (by simpa using member) xs statement a aIn b bIn
  have inside : PositionOf nodes.val b < same.val.length := by
    rw [sameReps.length]
    have := positionOf_le nodes.val b
    omega
  unfold RepOf Representative
  rw [equal,List.getElem?_eq_getElem inside]

/-- Nodes that a chain of related pairs joins take one value under any
    assignment that agrees on every related pair. -/
theorem eqvGen_value {α : Sort w} {r : Nat → Nat → Prop} (v : Nat → α) (agrees : ∀ i j, r i j → v i = v j) :
    ∀ {i j}, Relation.EqvGen r i j → v i = v j := by
  intro i j joined
  induction joined with
  | rel x y related => exact agrees x y related
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ first second => exact first.trans second

/-- A node and its representative take one value under any assignment that
    gives the members of every equality one value. -/
theorem representative_value {items : List AnnotatedAxiom} {nodes : List Individual} {same : List Usize}
    (joins : Joins items nodes same) {α : Sort w} (v : Nat → α) (agrees : ∀ i j, Equal items nodes i j → v i = v j)
    (n : Nat) : v (Representative same n) = v n := by
  unfold Representative
  cases at_n : same[n]? with
  | none => rfl
  | some b => exact eqvGen_value v agrees (joins.reps.joined n b at_n)

/-- Every representative is a node. -/
theorem representative_le {items : List AnnotatedAxiom} {nodes : List Individual} {same : List Usize}
    (joins : Joins items nodes same) (n : Nat) (inside : n ≤ nodes.length) :
    Representative same n ≤ nodes.length := by
  unfold Representative
  cases at_n : same[n]? with
  | none => exact inside
  | some b =>
    have := joins.reps.range n b at_n
    simp only
    omega

/-- The node of an individual is a node. -/
theorem repOf_le {items : List AnnotatedAxiom} {nodes : List Individual} {same : List Usize}
    (joins : Joins items nodes same) (a : Individual) : RepOf same nodes a ≤ nodes.length :=
  representative_le joins _ (positionOf_le nodes a)

/-- The search for a member with a given node is exact. -/
theorem meets_correct (nodes : alloc.vec.Vec Individual) (same : alloc.vec.Vec Usize) (node : Usize)
    (rest : alloc.vec.Vec Individual) (index : Usize) :
    shi_ontology.meets nodes same node rest index =
      .ok (decide (∃ a ∈ rest.val.drop index.val, RepOf same.val nodes.val a = node.val)) := by
  rw [shi_ontology.meets]
  by_cases more : index.val < rest.val.length
  · have lookup : rest.index_usize index = .ok rest.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : rest.val.drop index.val = rest.val[index.val] :: rest.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨here,hereRun,hereValue⟩ := node_of_correct nodes same rest.val[index.val]
    have later := meets_correct nodes same node rest next
    rw [nextIndex] at later
    have shape : (∃ a ∈ rest.val.drop index.val, RepOf same.val nodes.val a = node.val) ↔
        RepOf same.val nodes.val rest.val[index.val] = node.val ∨
          ∃ a ∈ rest.val.drop (index.val+1), RepOf same.val nodes.val a = node.val := by
      rw [split]
      simp only [List.mem_cons,exists_eq_or_imp]
    by_cases hit : here = node
    · have hitVal : RepOf same.val nodes.val rest.val[index.val] = node.val := by rw [← hereValue,hit]
      rw [decide_eq_true (shape.mpr (.inl hitVal))]
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,hereRun,hit]
    · have missVal : ¬ RepOf same.val nodes.val rest.val[index.val] = node.val := by
        intro equal
        apply hit
        apply UScalar.eq_of_val_eq
        rw [hereValue,equal]
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,hereRun,hit,advance,later]
      congr 1
      exact decide_eq_decide.mpr ⟨fun found => shape.mpr (.inr found),
        fun found => (shape.mp found).resolve_left missVal⟩
  · have empty : rest.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by rest.val.length - index.val
decreasing_by omega

/-- The search for two members with one node is exact. -/
theorem repeats_correct (nodes : alloc.vec.Vec Individual) (same : alloc.vec.Vec Usize)
    (rest : alloc.vec.Vec Individual) (index : Usize) :
    shi_ontology.repeats nodes same rest index =
      .ok (decide (¬ (rest.val.drop index.val).Pairwise
        (fun a b => RepOf same.val nodes.val a ≠ RepOf same.val nodes.val b))) := by
  rw [shi_ontology.repeats]
  by_cases more : index.val < rest.val.length
  · have lookup : rest.index_usize index = .ok rest.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : rest.val.drop index.val = rest.val[index.val] :: rest.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨here,hereRun,hereValue⟩ := node_of_correct nodes same rest.val[index.val]
    have met := meets_correct nodes same here rest next
    have later := repeats_correct nodes same rest next
    rw [nextIndex] at met later
    have shape : (rest.val.drop index.val).Pairwise
          (fun a b => RepOf same.val nodes.val a ≠ RepOf same.val nodes.val b) ↔
        (∀ b ∈ rest.val.drop (index.val+1),
          RepOf same.val nodes.val rest.val[index.val] ≠ RepOf same.val nodes.val b) ∧
        (rest.val.drop (index.val+1)).Pairwise
          (fun a b => RepOf same.val nodes.val a ≠ RepOf same.val nodes.val b) := by
      rw [split,List.pairwise_cons]
    by_cases hit : ∃ a ∈ rest.val.drop (index.val+1), RepOf same.val nodes.val a = here.val
    · have broken : ¬ (rest.val.drop index.val).Pairwise
          (fun a b => RepOf same.val nodes.val a ≠ RepOf same.val nodes.val b) := by
        intro whole
        obtain ⟨a,aIn,equal⟩ := hit
        exact (shape.mp whole).1 a aIn (by rw [← hereValue,equal])
      rw [decide_eq_true broken]
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,hereRun,advance,met]
      rw [decide_eq_true hit]
      rfl
    · have firstHolds : ∀ b ∈ rest.val.drop (index.val+1),
          RepOf same.val nodes.val rest.val[index.val] ≠ RepOf same.val nodes.val b := by
        intro b bIn equal
        exact hit ⟨b,bIn,by rw [hereValue,equal]⟩
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,hereRun,advance,met]
      rw [decide_eq_false hit]
      simp only [Bool.false_eq_true,↓reduceIte,later]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · intro broken whole
        exact broken (shape.mp whole).2
      · intro broken rest'
        exact broken (shape.mpr ⟨firstHolds,rest'⟩)
  · have empty : rest.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by rest.val.length - index.val
decreasing_by omega

/-- The check whether two members of an inequality share a node is exact. -/
theorem shares_correct (nodes : alloc.vec.Vec Individual) (same : alloc.vec.Vec Usize) (members : AtLeastTwo Individual) :
    shi_ontology.shares nodes same members =
      .ok (decide (¬ members.elements.Pairwise (fun a b => RepOf same.val nodes.val a ≠ RepOf same.val nodes.val b))) := by
  rw [shi_ontology.shares]
  obtain ⟨first,firstRun,firstValue⟩ := node_of_correct nodes same members.first
  obtain ⟨second,secondRun,secondValue⟩ := node_of_correct nodes same members.second
  have zero : (0#usize).val = 0 := rfl
  have metFirst := meets_correct nodes same first members.rest 0#usize
  have metSecond := meets_correct nodes same second members.rest 0#usize
  have repeated := repeats_correct nodes same members.rest 0#usize
  rw [zero,List.drop_zero] at metFirst metSecond repeated
  simp only [AtLeastTwo.elements,List.pairwise_cons,List.mem_cons,forall_eq_or_imp]
  simp only [firstRun,secondRun,bind_ok]
  by_cases one : first = second
  · have oneVal : RepOf same.val nodes.val members.first = RepOf same.val nodes.val members.second := by
      rw [← firstValue,← secondValue,one]
    simp [one,oneVal]
  · have oneVal : RepOf same.val nodes.val members.first ≠ RepOf same.val nodes.val members.second := by
      intro equal
      apply one
      apply UScalar.eq_of_val_eq
      rw [firstValue,secondValue,equal]
    simp only [one,↓reduceIte,metFirst]
    by_cases two : ∃ a ∈ members.rest.val, RepOf same.val nodes.val a = first.val
    · rw [decide_eq_true two]
      obtain ⟨a,aIn,equal⟩ := two
      have broken : ¬ ((RepOf same.val nodes.val members.first ≠ RepOf same.val nodes.val members.second ∧
          ∀ b ∈ members.rest.val, RepOf same.val nodes.val members.first ≠ RepOf same.val nodes.val b) ∧
          (∀ b ∈ members.rest.val, RepOf same.val nodes.val members.second ≠ RepOf same.val nodes.val b) ∧
          members.rest.val.Pairwise (fun a b => RepOf same.val nodes.val a ≠ RepOf same.val nodes.val b)) := by
        rintro ⟨⟨_,firstApart⟩,_⟩
        exact firstApart a aIn (by rw [← firstValue,equal])
      simp [broken]
    · rw [decide_eq_false two]
      simp only [Bool.false_eq_true,↓reduceIte,metSecond]
      have firstApart : ∀ b ∈ members.rest.val,
          RepOf same.val nodes.val members.first ≠ RepOf same.val nodes.val b := by
        intro b bIn equal
        exact two ⟨b,bIn,by rw [firstValue,equal]⟩
      by_cases three : ∃ a ∈ members.rest.val, RepOf same.val nodes.val a = second.val
      · rw [decide_eq_true three]
        obtain ⟨a,aIn,equal⟩ := three
        have broken : ¬ ((RepOf same.val nodes.val members.first ≠ RepOf same.val nodes.val members.second ∧
            ∀ b ∈ members.rest.val, RepOf same.val nodes.val members.first ≠ RepOf same.val nodes.val b) ∧
            (∀ b ∈ members.rest.val, RepOf same.val nodes.val members.second ≠ RepOf same.val nodes.val b) ∧
            members.rest.val.Pairwise (fun a b => RepOf same.val nodes.val a ≠ RepOf same.val nodes.val b)) := by
          rintro ⟨_,secondApart,_⟩
          exact secondApart a aIn (by rw [← secondValue,equal])
        simp [broken]
      · rw [decide_eq_false three]
        have secondApart : ∀ b ∈ members.rest.val,
            RepOf same.val nodes.val members.second ≠ RepOf same.val nodes.val b := by
          intro b bIn equal
          exact three ⟨b,bIn,by rw [secondValue,equal]⟩
        simp only [bind_ok,Bool.false_eq_true,↓reduceIte,repeated]
        congr 1
        apply decide_eq_decide.mpr
        constructor
        · intro broken whole
          exact broken whole.2.2
        · intro broken rest'
          exact broken ⟨⟨oneVal,firstApart⟩,secondApart,rest'⟩

/-- The check for an inequality two of whose members share a node is exact. -/
theorem clash_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (nodes : alloc.vec.Vec Individual)
    (same : alloc.vec.Vec Usize) (index : Usize) :
    shi_ontology.clash_from items nodes same index =
      .ok (decide (∃ item ∈ items.val.drop index.val, Clashes same.val nodes.val item.axiom)) := by
  rw [shi_ontology.clash_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have later := clash_from_correct items nodes same next
    rw [nextIndex] at later
    rw [split]
    simp only [List.mem_cons,exists_eq_or_imp]
    cases item : items.val[index.val].axiom with
    | DifferentIndividuals xs =>
      have shared := shares_correct nodes same xs
      by_cases hit : Clashes same.val nodes.val (.DifferentIndividuals xs)
      · have broken : ¬ xs.elements.Pairwise (fun a b => RepOf same.val nodes.val a ≠ RepOf same.val nodes.val b) := hit
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,item,shared]
        rw [decide_eq_true broken]
        simp [hit]
      · have whole : xs.elements.Pairwise (fun a b => RepOf same.val nodes.val a ≠ RepOf same.val nodes.val b) := by
          by_contra broken
          exact hit broken
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,item,shared]
        rw [decide_eq_false (not_not.mpr whole)]
        simp only [Bool.false_eq_true,↓reduceIte,advance,bind_ok,later]
        congr 1
        exact decide_eq_decide.mpr ⟨fun rest => .inr rest,fun both => both.resolve_left hit⟩
    | _ =>
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,item,advance,later]
      congr 1
      exact decide_eq_decide.mpr ⟨fun rest => .inr rest,fun both => both.resolve_left (by simp [Clashes])⟩
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- The check for inequalities is exact. -/
theorem has_different_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    shi_ontology.has_different items index =
      .ok (decide (∃ item ∈ items.val.drop index.val, Different item.axiom)) := by
  rw [shi_ontology.has_different]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have later := has_different_correct items next
    rw [nextIndex] at later
    rw [split]
    simp only [List.mem_cons,exists_eq_or_imp]
    cases item : items.val[index.val].axiom with
    | DifferentIndividuals xs =>
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,item,Different]
    | _ =>
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,item,advance,later]
      congr 1
      exact decide_eq_decide.mpr ⟨fun rest => .inr rest,fun both => both.resolve_left (by simp [Different])⟩
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by items.val.length - index.val
decreasing_by all_goals omega
end Rowl.ShiEquality
