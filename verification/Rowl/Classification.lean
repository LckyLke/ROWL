import Rowl.DataOntology

/-!
Classification of named classes against the Direct Semantics. `Told` is what a
single subclass, equivalence or disjoint-union axiom of the closure says about
two named classes, and every told pair is subsumed in every model. The
classification's answers are proved to be exactly subsumption and
satisfiability under every normative datatype map and vocabulary: each answer
is a proved prepared query's answer or follows from earlier answers by the
meaning of subsumption (reflexivity, transitivity, classes without instances,
and told pairs).
-/
namespace Rowl.Classification
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DatatypeMap (Normative)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable
universe u v w

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-! ### What the axioms tell -/

/-- `e` names `b`: it is `b`, or an intersection with `b` among its members. -/
def Names (e : ClassExpression) (b : Class) : Prop :=
  e = .Class b ∨ ∃ xs, e = .ObjectIntersectionOf xs ∧ ClassExpression.Class b ∈ xs.elements

/-- What a single subclass, equivalence or disjoint-union axiom of the closure
    says about two named classes. -/
inductive Told (items : List AnnotatedAxiom) : Class → Class → Prop
  | sub {a b : Class} {e : ClassExpression} :
      (∃ item ∈ items, item.axiom = .SubClassOf (.Class a) e) → Names e b → Told items a b
  | equivalent {a b : Class} {e : ClassExpression} {xs : AtLeastTwo ClassExpression} :
      (∃ item ∈ items, item.axiom = .EquivalentClasses xs) → ClassExpression.Class a ∈ xs.elements →
      e ∈ xs.elements → Names e b → Told items a b
  | union {a b : Class} {xs : AtLeastTwo ClassExpression} :
      (∃ item ∈ items, item.axiom = .DisjointUnion b xs) → ClassExpression.Class a ∈ xs.elements → Told items a b

private theorem class_denote {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (c : Class)
    (x : Object) : classDenote I (.Class c) x ↔ I.classes c x := by
  rw [classDenote]

private theorem anonymous_class {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (assignment : AnonymousIndividual → Object) (c : Class) (x : Object) :
    classDenote (withAnonymous I assignment) (.Class c) x ↔ classDenote I (.Class c) x := by
  rw [class_denote, class_denote]
  rfl

private theorem names_denote {Object : Type u} {Value : Type v} (J : Interpretation Object Value)
    {e : ClassExpression} {b : Class} (names : Names e b) (x : Object) (inside : classDenote J e x) :
    classDenote J (.Class b) x := by
  rcases names with rfl | ⟨xs, rfl, member⟩
  · exact inside
  · rw [classDenote] at inside
    obtain ⟨first, second, rest⟩ := inside
    simp only [AtLeastTwo.elements, List.mem_cons] at member
    rcases member with same | same | later
    · rw [same]; exact first
    · rw [same]; exact second
    · exact rest _ later

/-- Every told pair is subsumed in every model of the closure. -/
theorem told_subsumed {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary) (items : List AnnotatedAxiom)
    {a b : Class} (told : Told items a b) : Subsumed.{u,v,w} D V items (.Class a) (.Class b) := by
  intro Object Value embed I model x member
  obtain ⟨_, _, assignment, sat⟩ := model
  have lift := anonymous_class I assignment
  cases told with
  | sub found names =>
    obtain ⟨item, itemIn, axiomIs⟩ := found
    have holds := sat item itemIn
    rw [axiomIs] at holds
    exact (lift b x).mp (names_denote _ names x (holds x ((lift a x).mpr member)))
  | equivalent found aIn eIn names =>
    obtain ⟨item, itemIn, axiomIs⟩ := found
    have holds := sat item itemIn
    rw [axiomIs] at holds
    have same := holds _ aIn _ eIn
    have inE := (congrFun same x).mp ((lift a x).mpr member)
    exact (lift b x).mp (names_denote _ names x inE)
  | union found aIn =>
    obtain ⟨item, itemIn, axiomIs⟩ := found
    have holds := sat item itemIn
    rw [axiomIs] at holds
    have inUnion := (holds.1 x).mpr ⟨_, aIn, (lift a x).mpr member⟩
    exact (lift b x).mp ((class_denote _ b x).mpr inUnion)

/-! ### The meaning of subsumption -/

theorem subsumed_refl {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary) (items : List AnnotatedAxiom)
    (e : ClassExpression) : Subsumed.{u,v,w} D V items e e :=
  fun _ _ _ _ _ _ inside => inside

theorem subsumed_trans {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary) (items : List AnnotatedAxiom)
    {a b c : ClassExpression} (first : Subsumed.{u,v,w} D V items a b) (second : Subsumed.{u,v,w} D V items b c) :
    Subsumed.{u,v,w} D V items a c :=
  fun Object Value embed I model x inside => second Object Value embed I model x (first Object Value embed I model x inside)

theorem unsatisfiable_subsumed {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (items : List AnnotatedAxiom) {a : ClassExpression} (b : ClassExpression)
    (empty : ¬ ClassSatisfiable.{u,v,w} D V items a) : Subsumed.{u,v,w} D V items a b := by
  intro Object Value embed I model x inside
  exact absurd ⟨Object, Value, embed, I, model, x, inside⟩ empty

theorem not_subsumed_unsatisfiable {Native : Type w} (D : DatatypeMap Native) (V : Vocabulary)
    (items : List AnnotatedAxiom) {a b : ClassExpression} (some : ClassSatisfiable.{u,v,w} D V items a)
    (empty : ¬ ClassSatisfiable.{u,v,w} D V items b) : ¬ Subsumed.{u,v,w} D V items a b := by
  intro sub
  obtain ⟨Object, Value, embed, I, model, x, inside⟩ := some
  exact empty ⟨Object, Value, embed, I, model, x, sub Object Value embed I model x inside⟩

/-- An answer for a pair of named classes under every normative datatype map
    and vocabulary: `yes` means subsumed, `no` not subsumed. -/
def Right (items : List AnnotatedAxiom) (a b : Class) (code : U8) : Prop :=
  (code.val = 2 → ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary),
    IsVocabulary D V → Subsumed.{u, max w v, w} D V items (.Class a) (.Class b)) ∧
  (code.val = 1 → ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary),
    IsVocabulary D V → ¬ Subsumed.{u, max w v, w} D V items (.Class a) (.Class b))

/-- Satisfiability answers for the listed classes. -/
def SatisfiableRight (items : List AnnotatedAxiom) (classes : List Class) (answers : List Bool) : Prop :=
  answers.length = classes.length ∧ ∀ (i : Nat) (c : Class) (s : Bool), classes[i]? = some c → answers[i]? = some s →
    ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
      (s = true ↔ ClassSatisfiable.{u, max w v, w} D V items (.Class c))

/-! ### The told parents -/

/-- Every listed told parent is a listed class that the closure tells is above. -/
def ParentsOk (items : List AnnotatedAxiom) (classes : List Class) (parents : List (alloc.vec.Vec Usize)) : Prop :=
  parents.length = classes.length ∧
  ∀ (c : Nat) (row : alloc.vec.Vec Usize), parents[c]? = some row → ∀ p ∈ row.val, ∃ child parent,
    classes[c]? = some child ∧ classes[p.val]? = some parent ∧ Told items child parent

private theorem class_eq_of_spelling {c d : Class} (same : c.iri.spelling.val = d.iri.spelling.val) : c = d := by
  obtain ⟨⟨s⟩⟩ := c
  obtain ⟨⟨t⟩⟩ := d
  have : s = t := (alloc.vec.Vec.eq_iff s t).mpr same
  subst this
  rfl

theorem position_spec (classes : alloc.vec.Vec Class) (cls : Class) (index : Usize) :
    ∃ p, classification.position classes cls index = .ok p ∧ p.val ≤ classes.val.length ∧
      (p.val < classes.val.length → classes.val[p.val]? = some cls) := by
  rw [classification.position]
  by_cases more : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    by_cases same : classes.val[index.val].iri.spelling.val = cls.iri.spelling.val
    · refine ⟨index, ?_, by omega, fun _ => ?_⟩
      · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, Rowl.Symbols.same_spelling_total_correct, same]
      · rw [List.getElem?_eq_getElem more, class_eq_of_spelling same]
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      obtain ⟨p, run, bound, found⟩ := position_spec classes cls next
      refine ⟨p, ?_, bound, found⟩
      simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, Rowl.Symbols.same_spelling_total_correct, same,
        advance, run]
  · refine ⟨alloc.vec.Vec.len classes, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], by simp, ?_⟩
    intro below
    simp at below
termination_by classes.val.length - index.val
decreasing_by
  have := nextValue
  simp at this
  omega

theorem tell_spec (items : List AnnotatedAxiom) (classes : alloc.vec.Vec Class) (child parent : Class)
    (told : Told items child parent) (parents : alloc.vec.Vec (alloc.vec.Vec Usize))
    (good : ParentsOk items classes.val parents.val) :
    ∃ r, classification.tell classes child parent parents = .ok r ∧ ParentsOk items classes.val r.val := by
  obtain ⟨lengths, rows⟩ := good
  obtain ⟨c, cRun, cBound, cFound⟩ := position_spec classes child 0#usize
  obtain ⟨p, pRun, pBound, pFound⟩ := position_spec classes parent 0#usize
  rw [classification.tell, cRun, bind_ok, pRun, bind_ok]
  by_cases cIn : c.val < parents.val.length
  · by_cases pIn : p.val < classes.val.length
    · have lookup : parents.index_usize c = .ok parents.val[c.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem cIn]
      by_cases room : parents.val[c.val].val.length < Usize.max
      · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec parents.val[c.val] p room)
        refine ⟨parents.set c pushed, ?_, ?_⟩
        · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, cIn, pIn, lookup, usize_max_val, room,
            alloc.vec.Vec.index_mut_usize, push]
        · refine ⟨by simp [lengths], ?_⟩
          intro c' row at_c' q member
          rw [alloc.vec.Vec.set_val_eq] at at_c'
          by_cases same : c' = c.val
          · subst same
            rw [List.getElem?_set_self cIn] at at_c'
            cases Option.some.inj at_c'
            rw [contents] at member
            rcases List.mem_append.mp member with old | new
            · exact rows c.val _ (List.getElem?_eq_getElem cIn) q old
            · simp only [List.mem_singleton] at new
              subst new
              exact ⟨child, parent, cFound (by omega), pFound pIn, told⟩
          · rw [List.getElem?_set_ne (Ne.symm same)] at at_c'
            exact rows c' row at_c' q member
      · refine ⟨parents, ?_, lengths, rows⟩
        simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, cIn, pIn, lookup, usize_max_val, room]
    · exact ⟨parents, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, cIn, pIn], lengths, rows⟩
  · exact ⟨parents, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, cIn], lengths, rows⟩

theorem tell_named_spec (items : List AnnotatedAxiom) (classes : alloc.vec.Vec Class) (child : Class)
    (member : ClassExpression) (told : ∀ b, member = .Class b → Told items child b)
    (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (good : ParentsOk items classes.val parents.val) :
    ∃ r, classification.tell_named classes child member parents = .ok r ∧ ParentsOk items classes.val r.val := by
  rw [classification.tell_named.eq_def]
  cases member
  case Class parent => exact tell_spec items classes child parent (told parent rfl) parents good
  all_goals exact ⟨parents, rfl, good⟩

theorem tell_members_spec (items : List AnnotatedAxiom) (classes : alloc.vec.Vec Class) (child : Class)
    (members : alloc.vec.Vec ClassExpression) (told : ∀ b, ClassExpression.Class b ∈ members.val → Told items child b)
    (index : Usize) (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (good : ParentsOk items classes.val parents.val) :
    ∃ r, classification.tell_members classes child members index parents = .ok r ∧
      ParentsOk items classes.val r.val := by
  rw [classification.tell_members]
  by_cases more : index.val < members.val.length
  · have lookup : members.index_usize index = .ok members.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have member : members.val[index.val] ∈ members.val := List.getElem_mem more
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨mid, midRun, midGood⟩ := tell_named_spec items classes child members.val[index.val]
      (fun b same => told b (by rw [← same]; exact member)) parents good
    obtain ⟨r, run, rGood⟩ := tell_members_spec items classes child members told next mid midGood
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, midRun, advance, run], rGood⟩
  · exact ⟨parents, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], good⟩
termination_by members.val.length - index.val
decreasing_by omega

theorem tell_expression_spec (items : List AnnotatedAxiom) (classes : alloc.vec.Vec Class) (child : Class)
    (expression : ClassExpression) (told : ∀ b, Names expression b → Told items child b)
    (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (good : ParentsOk items classes.val parents.val) :
    ∃ r, classification.tell_expression classes child expression parents = .ok r ∧
      ParentsOk items classes.val r.val := by
  rw [classification.tell_expression.eq_def]
  cases expression
  case Class parent => exact tell_spec items classes child parent (told parent (.inl rfl)) parents good
  case ObjectIntersectionOf members =>
    have named : ∀ b, ClassExpression.Class b ∈ members.elements → Told items child b :=
      fun b member => told b (.inr ⟨members, rfl, member⟩)
    obtain ⟨p1, run1, good1⟩ := tell_named_spec items classes child members.first
      (fun b same => named b (by rw [← same]; simp [AtLeastTwo.elements])) parents good
    obtain ⟨p2, run2, good2⟩ := tell_named_spec items classes child members.second
      (fun b same => named b (by rw [← same]; simp [AtLeastTwo.elements])) p1 good1
    obtain ⟨p3, run3, good3⟩ := tell_members_spec items classes child members.rest
      (fun b member => named b (by simp [AtLeastTwo.elements, member])) 0#usize p2 good2
    exact ⟨p3, by simp [run1, run2, run3], good3⟩
  all_goals exact ⟨parents, rfl, good⟩

theorem tell_list_spec (items : List AnnotatedAxiom) (classes : alloc.vec.Vec Class) (child : Class)
    (members : alloc.vec.Vec ClassExpression) (told : ∀ e ∈ members.val, ∀ b, Names e b → Told items child b)
    (index : Usize) (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (good : ParentsOk items classes.val parents.val) :
    ∃ r, classification.tell_list classes child members index parents = .ok r ∧
      ParentsOk items classes.val r.val := by
  rw [classification.tell_list]
  by_cases more : index.val < members.val.length
  · have lookup : members.index_usize index = .ok members.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨mid, midRun, midGood⟩ := tell_expression_spec items classes child members.val[index.val]
      (told _ (List.getElem_mem more)) parents good
    obtain ⟨r, run, rGood⟩ := tell_list_spec items classes child members told next mid midGood
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, midRun, advance, run], rGood⟩
  · exact ⟨parents, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], good⟩
termination_by members.val.length - index.val
decreasing_by omega

theorem tell_all_spec (items : List AnnotatedAxiom) (classes : alloc.vec.Vec Class) (child : Class)
    (members : AtLeastTwo ClassExpression) (told : ∀ e ∈ members.elements, ∀ b, Names e b → Told items child b)
    (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (good : ParentsOk items classes.val parents.val) :
    ∃ r, classification.tell_all classes child members parents = .ok r ∧ ParentsOk items classes.val r.val := by
  rw [classification.tell_all]
  obtain ⟨p1, run1, good1⟩ := tell_expression_spec items classes child members.first
    (told _ (by simp [AtLeastTwo.elements])) parents good
  obtain ⟨p2, run2, good2⟩ := tell_expression_spec items classes child members.second
    (told _ (by simp [AtLeastTwo.elements])) p1 good1
  obtain ⟨p3, run3, good3⟩ := tell_list_spec items classes child members.rest
    (fun e member => told e (by simp [AtLeastTwo.elements, member])) 0#usize p2 good2
  exact ⟨p3, by simp [run1, run2, run3], good3⟩

theorem tell_member_spec (items : List AnnotatedAxiom) (classes : alloc.vec.Vec Class)
    (member : ClassExpression) (members : AtLeastTwo ClassExpression)
    (listed : ∃ item ∈ items, item.axiom = .EquivalentClasses members) (memberIn : member ∈ members.elements)
    (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (good : ParentsOk items classes.val parents.val) :
    ∃ r, classification.tell_member classes member members parents = .ok r ∧ ParentsOk items classes.val r.val := by
  rw [classification.tell_member.eq_def]
  cases member
  case Class child =>
    exact tell_all_spec items classes child members
      (fun e eIn b names => .equivalent listed memberIn eIn names) parents good
  all_goals exact ⟨parents, rfl, good⟩

theorem tell_equivalent_rest_spec (items : List AnnotatedAxiom) (classes : alloc.vec.Vec Class)
    (members : AtLeastTwo ClassExpression) (listed : ∃ item ∈ items, item.axiom = .EquivalentClasses members)
    (index : Usize) (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (good : ParentsOk items classes.val parents.val) :
    ∃ r, classification.tell_equivalent_rest classes members index parents = .ok r ∧
      ParentsOk items classes.val r.val := by
  rw [classification.tell_equivalent_rest]
  by_cases more : index.val < members.rest.val.length
  · have lookup : members.rest.index_usize index = .ok members.rest.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨mid, midRun, midGood⟩ := tell_member_spec items classes members.rest.val[index.val] members listed
      (by simp [AtLeastTwo.elements, List.getElem_mem more]) parents good
    obtain ⟨r, run, rGood⟩ := tell_equivalent_rest_spec items classes members listed next mid midGood
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, midRun, advance, run], rGood⟩
  · exact ⟨parents, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], good⟩
termination_by members.rest.val.length - index.val
decreasing_by omega

theorem tell_equivalent_spec (items : List AnnotatedAxiom) (classes : alloc.vec.Vec Class)
    (members : AtLeastTwo ClassExpression) (listed : ∃ item ∈ items, item.axiom = .EquivalentClasses members)
    (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (good : ParentsOk items classes.val parents.val) :
    ∃ r, classification.tell_equivalent classes members parents = .ok r ∧ ParentsOk items classes.val r.val := by
  rw [classification.tell_equivalent]
  obtain ⟨p1, run1, good1⟩ := tell_member_spec items classes members.first members listed
    (by simp [AtLeastTwo.elements]) parents good
  obtain ⟨p2, run2, good2⟩ := tell_member_spec items classes members.second members listed
    (by simp [AtLeastTwo.elements]) p1 good1
  obtain ⟨p3, run3, good3⟩ := tell_equivalent_rest_spec items classes members listed 0#usize p2 good2
  exact ⟨p3, by simp [run1, run2, run3], good3⟩

theorem tell_under_spec (items : List AnnotatedAxiom) (classes : alloc.vec.Vec Class) (union : Class)
    (member : ClassExpression) (members : AtLeastTwo ClassExpression)
    (listed : ∃ item ∈ items, item.axiom = .DisjointUnion union members) (memberIn : member ∈ members.elements)
    (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (good : ParentsOk items classes.val parents.val) :
    ∃ r, classification.tell_under classes union member parents = .ok r ∧ ParentsOk items classes.val r.val := by
  rw [classification.tell_under.eq_def]
  cases member
  case Class child => exact tell_spec items classes child union (.union listed memberIn) parents good
  all_goals exact ⟨parents, rfl, good⟩

theorem tell_union_rest_spec (items : List AnnotatedAxiom) (classes : alloc.vec.Vec Class) (union : Class)
    (members : AtLeastTwo ClassExpression) (listed : ∃ item ∈ items, item.axiom = .DisjointUnion union members)
    (index : Usize) (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (good : ParentsOk items classes.val parents.val) :
    ∃ r, classification.tell_union_rest classes union members.rest index parents = .ok r ∧
      ParentsOk items classes.val r.val := by
  rw [classification.tell_union_rest]
  by_cases more : index.val < members.rest.val.length
  · have lookup : members.rest.index_usize index = .ok members.rest.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨mid, midRun, midGood⟩ := tell_under_spec items classes union members.rest.val[index.val] members listed
      (by simp [AtLeastTwo.elements, List.getElem_mem more]) parents good
    obtain ⟨r, run, rGood⟩ := tell_union_rest_spec items classes union members listed next mid midGood
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, midRun, advance, run], rGood⟩
  · exact ⟨parents, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], good⟩
termination_by members.rest.val.length - index.val
decreasing_by omega

theorem tell_union_spec (items : List AnnotatedAxiom) (classes : alloc.vec.Vec Class) (union : Class)
    (members : AtLeastTwo ClassExpression) (listed : ∃ item ∈ items, item.axiom = .DisjointUnion union members)
    (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (good : ParentsOk items classes.val parents.val) :
    ∃ r, classification.tell_union classes union members parents = .ok r ∧ ParentsOk items classes.val r.val := by
  rw [classification.tell_union]
  obtain ⟨p1, run1, good1⟩ := tell_under_spec items classes union members.first members listed
    (by simp [AtLeastTwo.elements]) parents good
  obtain ⟨p2, run2, good2⟩ := tell_under_spec items classes union members.second members listed
    (by simp [AtLeastTwo.elements]) p1 good1
  obtain ⟨p3, run3, good3⟩ := tell_union_rest_spec items classes union members listed 0#usize p2 good2
  exact ⟨p3, by simp [run1, run2, run3], good3⟩

theorem tell_axiom_spec (items : List AnnotatedAxiom) (classes : alloc.vec.Vec Class) (statement : Axiom)
    (listed : ∃ item ∈ items, item.axiom = statement)
    (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (good : ParentsOk items classes.val parents.val) :
    ∃ r, classification.tell_axiom classes statement parents = .ok r ∧ ParentsOk items classes.val r.val := by
  rw [classification.tell_axiom.eq_def]
  cases statement
  case SubClassOf sub parent =>
    cases sub
    case Class child =>
      exact tell_expression_spec items classes child parent (fun b names => .sub listed names) parents good
    all_goals exact ⟨parents, rfl, good⟩
  case EquivalentClasses members => exact tell_equivalent_spec items classes members listed parents good
  case DisjointUnion union members => exact tell_union_spec items classes union members listed parents good
  all_goals exact ⟨parents, rfl, good⟩

theorem told_from_spec (items : alloc.vec.Vec AnnotatedAxiom) (classes : alloc.vec.Vec Class) (index : Usize)
    (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (good : ParentsOk items.val classes.val parents.val) :
    ∃ r, classification.told_from items classes index parents = .ok r ∧ ParentsOk items.val classes.val r.val := by
  rw [classification.told_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨mid, midRun, midGood⟩ := tell_axiom_spec items.val classes items.val[index.val].axiom
      ⟨_, List.getElem_mem more, rfl⟩ parents good
    obtain ⟨r, run, rGood⟩ := told_from_spec items classes next mid midGood
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, midRun, advance, run], rGood⟩
  · exact ⟨parents, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], good⟩
termination_by items.val.length - index.val
decreasing_by omega

theorem empty_rows_spec (count : Usize) (out : alloc.vec.Vec (alloc.vec.Vec Usize))
    (short : out.val.length ≤ count.val) (empty : ∀ row ∈ out.val, row.val = []) :
    ∃ r, classification.empty_rows count out = .ok r ∧ r.val.length = count.val ∧ ∀ row ∈ r.val, row.val = [] := by
  rw [classification.empty_rows]
  by_cases more : out.val.length < count.val
  · have room : out.val.length < Usize.max := by have := count.hBounds; scalar_tac
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (alloc.vec.Vec.new Usize) room)
    obtain ⟨r, run, length, rows⟩ := empty_rows_spec count pushed (by rw [contents]; simp; omega)
      (by
        intro row member
        rw [contents] at member
        rcases List.mem_append.mp member with old | new
        · exact empty row old
        · simp at new; rw [new]; rfl)
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, push, run], length, rows⟩
  · exact ⟨out, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], by omega, empty⟩
termination_by count.val - out.val.length
decreasing_by rw [contents]; simp; omega

/-- The told parents of the listed classes: every listed parent is a listed
    class the closure tells is above. -/
theorem told_spec (items : alloc.vec.Vec AnnotatedAxiom) (classes : alloc.vec.Vec Class) :
    ∃ r, classification.told items classes = .ok r ∧ ParentsOk items.val classes.val r.val := by
  rw [classification.told]
  obtain ⟨rows, rowsRun, length, empty⟩ := empty_rows_spec (alloc.vec.Vec.len classes)
    (alloc.vec.Vec.new (alloc.vec.Vec Usize)) (by simp) (by simp)
  obtain ⟨r, run, good⟩ := told_from_spec items classes 0#usize rows
    ⟨by simp [length], fun c row at_c p member => by
      rw [empty row (List.mem_of_getElem? at_c)] at member
      cases member⟩
  exact ⟨r, by simp [rowsRun, run], good⟩


/-! ### Codes and helpers -/

private theorem yes_val : classification.YES.val = 2 := by unfold classification.YES; rfl
private theorem no_val : classification.NO.val = 1 := by unfold classification.NO; rfl
private theorem unknown_val : classification.UNKNOWN.val = 0 := by unfold classification.UNKNOWN; rfl

private theorem u8_eq_iff (a b : U8) : a = b ↔ a.val = b.val := by
  constructor
  · rintro rfl; rfl
  · intro same; exact UScalar.eq_of_val_eq same

theorem filled_spec (count : Usize) (value : U8) (out : alloc.vec.Vec U8) (short : out.val.length ≤ count.val)
    (all : ∀ x ∈ out.val, x = value) :
    ∃ r, classification.filled count value out = .ok r ∧ r.val.length = count.val ∧ ∀ x ∈ r.val, x = value := by
  rw [classification.filled]
  by_cases more : out.val.length < count.val
  · have room : out.val.length < Usize.max := by have := count.hBounds; scalar_tac
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out value room)
    obtain ⟨r, run, length, rAll⟩ := filled_spec count value pushed (by rw [contents]; simp; omega)
      (by
        intro x member
        rw [contents] at member
        rcases List.mem_append.mp member with old | new
        · exact all x old
        · simpa using new)
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, push, run], length, rAll⟩
  · exact ⟨out, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], by omega, all⟩
termination_by count.val - out.val.length
decreasing_by rw [contents]; simp; omega

theorem zeros_spec (count : Usize) (out : alloc.vec.Vec Usize) (short : out.val.length ≤ count.val) :
    ∃ r, classification.zeros count out = .ok r ∧ r.val.length = count.val := by
  rw [classification.zeros]
  by_cases more : out.val.length < count.val
  · have room : out.val.length < Usize.max := by have := count.hBounds; scalar_tac
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out 0#usize room)
    obtain ⟨r, run, length⟩ := zeros_spec count pushed (by rw [contents]; simp; omega)
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, push, run], length⟩
  · exact ⟨out, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], by omega⟩
termination_by count.val - out.val.length
decreasing_by rw [contents]; simp; omega

theorem unclassified_spec (count : Usize) (out : alloc.vec.Vec Bool) (short : out.val.length ≤ count.val)
    (all : ∀ x ∈ out.val, x = false) :
    ∃ r, classification.unclassified count out = .ok r ∧ r.val.length = count.val ∧ ∀ x ∈ r.val, x = false := by
  rw [classification.unclassified]
  by_cases more : out.val.length < count.val
  · have room : out.val.length < Usize.max := by have := count.hBounds; scalar_tac
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out false room)
    obtain ⟨r, run, length, rAll⟩ := unclassified_spec count pushed (by rw [contents]; simp; omega)
      (by
        intro x member
        rw [contents] at member
        rcases List.mem_append.mp member with old | new
        · exact all x old
        · simpa using new)
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, push, run], length, rAll⟩
  · exact ⟨out, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], by omega, all⟩
termination_by count.val - out.val.length
decreasing_by rw [contents]; simp; omega

theorem unknown_rows_spec (count : Usize) (out : alloc.vec.Vec (alloc.vec.Vec U8)) (short : out.val.length ≤ count.val)
    (all : ∀ row ∈ out.val, row.val.length = count.val ∧ ∀ x ∈ row.val, x = classification.UNKNOWN) :
    ∃ r, classification.unknown_rows count out = .ok r ∧ r.val.length = count.val ∧
      ∀ row ∈ r.val, row.val.length = count.val ∧ ∀ x ∈ row.val, x = classification.UNKNOWN := by
  rw [classification.unknown_rows]
  by_cases more : out.val.length < count.val
  · have room : out.val.length < Usize.max := by have := count.hBounds; scalar_tac
    obtain ⟨row, rowRun, rowLength, rowAll⟩ := filled_spec count classification.UNKNOWN
      (alloc.vec.Vec.new U8) (by simp) (by simp)
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out row room)
    obtain ⟨r, run, length, rAll⟩ := unknown_rows_spec count pushed (by rw [contents]; simp; omega)
      (by
        intro x member
        rw [contents] at member
        rcases List.mem_append.mp member with old | new
        · exact all x old
        · simp only [List.mem_singleton] at new
          rw [new]
          exact ⟨rowLength, rowAll⟩)
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, rowRun, push, run], length, rAll⟩
  · exact ⟨out, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], by omega, all⟩
termination_by count.val - out.val.length
decreasing_by rw [contents]; simp; omega

/-! ### The order -/

theorem deepest_spec (depth listed : alloc.vec.Vec Usize) (index best cap : Usize) :
    ∃ r, classification.deepest depth listed index best cap = .ok r := by
  rw [classification.deepest]
  by_cases more : index.val < listed.val.length
  · have lookup : listed.index_usize index = .ok listed.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    by_cases inside : listed.val[index.val].val < depth.val.length
    · have lookupD : depth.index_usize listed.val[index.val] = .ok depth.val[listed.val[index.val].val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      by_cases below : depth.val[listed.val[index.val].val].val < cap.val
      · obtain ⟨up, upRun, _⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := depth.val[listed.val[index.val].val]) (y := 1#usize) (by scalar_tac))
        by_cases le : best.val ≤ depth.val[listed.val[index.val].val].val
        · obtain ⟨r, run⟩ := deepest_spec depth listed next up cap
          exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, UScalar.le_equiv, more, lookup, inside,
            lookupD, below, le, upRun, advance, run]⟩
        · obtain ⟨r, run⟩ := deepest_spec depth listed next best cap
          exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, UScalar.le_equiv, more, lookup, inside,
            lookupD, below, le, advance, run]⟩
      · obtain ⟨r, run⟩ := deepest_spec depth listed next best cap
        exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, inside, lookupD, below,
          advance, run]⟩
    · obtain ⟨r, run⟩ := deepest_spec depth listed next best cap
      exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, inside, advance, run]⟩
  · exact ⟨best, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more]⟩
termination_by listed.val.length - index.val
decreasing_by all_goals omega

theorem deepen_spec (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (depth : alloc.vec.Vec Usize)
    (cap index : Usize) :
    ∃ r, classification.deepen parents depth cap index = .ok r ∧ r.val.length = depth.val.length := by
  rw [classification.deepen]
  by_cases more : index.val < depth.val.length
  · by_cases moreP : index.val < parents.val.length
    · have lookupP : parents.index_usize index = .ok parents.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem moreP]
      have lookupD : depth.index_usize index = .ok depth.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
      obtain ⟨best, bestRun⟩ := deepest_spec depth parents.val[index.val] 0#usize depth.val[index.val] cap
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, length⟩ := deepen_spec parents (depth.set index best) cap next
      refine ⟨r, ?_, by rw [length]; simp⟩
      simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, moreP, lookupP, lookupD, bestRun,
        alloc.vec.Vec.index_mut_usize, advance, run]
    · exact ⟨depth, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, moreP], rfl⟩
  · exact ⟨depth, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], rfl⟩
termination_by depth.val.length - index.val
decreasing_by simp; omega

theorem depths_spec (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (depth : alloc.vec.Vec Usize)
    (cap rounds : Usize) :
    ∃ r, classification.depths parents depth cap rounds = .ok r ∧ r.val.length = depth.val.length := by
  rw [classification.depths]
  by_cases positive : 0 < rounds.val
  · obtain ⟨depth1, run1, length1⟩ := deepen_spec parents depth cap 0#usize
    obtain ⟨fewer, back, fewerValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := rounds) (y := 1#usize) (by scalar_tac))
    have fewerIs : fewer.val = rounds.val - 1 := by simp at fewerValue; omega
    obtain ⟨r, run, length⟩ := depths_spec parents depth1 cap fewer
    refine ⟨r, ?_, by rw [length, length1]⟩
    have positiveU : rounds > 0#usize := by scalar_tac
    simp [positiveU, run1, back, run]
  · have positiveU : ¬ rounds > 0#usize := by scalar_tac
    exact ⟨depth, by simp [positiveU], rfl⟩
termination_by rounds.val
decreasing_by omega

theorem at_level_spec (depth : alloc.vec.Vec Usize) (level index : Usize) (out : alloc.vec.Vec Usize) :
    ∃ r, classification.at_level depth level index out = .ok r := by
  rw [classification.at_level]
  by_cases more : index.val < depth.val.length
  · have lookup : depth.index_usize index = .ok depth.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    by_cases same : depth.val[index.val] = level
    · by_cases room : out.val.length < Usize.max
      · obtain ⟨pushed, push, _⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out index room)
        obtain ⟨r, run⟩ := at_level_spec depth level next pushed
        exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, same, usize_max_val, room, push,
          advance, run]⟩
      · obtain ⟨r, run⟩ := at_level_spec depth level next out
        exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, same, usize_max_val, room,
          advance, run]⟩
    · obtain ⟨r, run⟩ := at_level_spec depth level next out
      exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, same, advance, run]⟩
  · exact ⟨out, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more]⟩
termination_by depth.val.length - index.val
decreasing_by all_goals omega

theorem levels_spec (depth : alloc.vec.Vec Usize) (level cap : Usize) (out : alloc.vec.Vec Usize) :
    ∃ r, classification.levels depth level cap out = .ok r := by
  rw [classification.levels]
  by_cases within : level.val ≤ cap.val
  · by_cases room : level.val < Usize.max
    · obtain ⟨mid, midRun⟩ := at_level_spec depth level 0#usize out
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := level) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = level.val + 1 := by simpa using nextValue
      obtain ⟨r, run⟩ := levels_spec depth next cap mid
      exact ⟨r, by simp [UScalar.le_equiv, UScalar.lt_equiv, within, usize_max_val, room, midRun, advance, run]⟩
    · exact ⟨out, by simp [UScalar.le_equiv, UScalar.lt_equiv, within, usize_max_val, room]⟩
  · exact ⟨out, by simp [UScalar.le_equiv, within]⟩
termination_by cap.val + 1 - level.val
decreasing_by omega

/-! ### Answers -/

/-- Every answer of a row of class `a` is right. -/
def RowRight (items : List AnnotatedAxiom) (classes : List Class) (a : Nat) (row : List U8) : Prop :=
  row.length = classes.length ∧ (∀ (b : Nat) (code : U8), row[b]? = some code → code.val ≤ 2) ∧
    ∃ ca, classes[a]? = some ca ∧ ∀ (b : Nat) (code : U8) (cb : Class), row[b]? = some code → classes[b]? = some cb →
      Right.{u,v,w} items ca cb code

/-- A row answers every class with `yes` or `no`. -/
def Complete (row : List U8) : Prop := ∀ (b : Nat) (code : U8), row[b]? = some code → code.val = 1 ∨ code.val = 2

/-- The rows so far: every row is right, and classified rows are complete. -/
def RowsRight (items : List AnnotatedAxiom) (classes : List Class) (rows : List (alloc.vec.Vec U8))
    (done : List Bool) : Prop :=
  rows.length = classes.length ∧ done.length = classes.length ∧
  ∀ (q : Nat) (row : alloc.vec.Vec U8), rows[q]? = some row →
    RowRight.{u,v,w} items classes q row.val ∧ (done[q]? = some true → Complete row.val)

theorem listed_spec (list : alloc.vec.Vec Usize) (item index : Usize) :
    classification.listed list item index = .ok (decide (item ∈ list.val.drop index.val)) := by
  rw [classification.listed]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    by_cases here : list.val[index.val] = item
    · rw [List.drop_eq_getElem_cons more]
      simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, here]
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have rest := listed_spec list item next
      rw [nextIndex] at rest
      have other : item ≠ list.val[index.val] := fun same => here same.symm
      have memIff : item ∈ list.val.drop (index.val + 1) ↔ item ∈ list.val.drop index.val := by
        rw [List.drop_eq_getElem_cons more, List.mem_cons]
        exact ⟨Or.inr, fun h => h.resolve_left other⟩
      simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, here, advance, rest, memIff]
  · have empty : list.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, empty]
termination_by list.val.length - index.val
decreasing_by omega

theorem refused_spec (row : alloc.vec.Vec U8) (parents : alloc.vec.Vec Usize) (index : Usize) :
    ∃ r, classification.refused row parents index = .ok r ∧
      (r = true → ∃ p ∈ parents.val, row.val[p.val]? = some classification.NO) := by
  rw [classification.refused]
  by_cases more : index.val < parents.val.length
  · have lookup : parents.index_usize index = .ok parents.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have member : parents.val[index.val] ∈ parents.val := List.getElem_mem more
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, run, spec⟩ := refused_spec row parents next
    by_cases inside : parents.val[index.val].val < row.val.length
    · have lookupR : row.index_usize parents.val[index.val] = .ok row.val[parents.val[index.val].val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      by_cases no : row.val[parents.val[index.val].val] = classification.NO
      · refine ⟨true, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, inside, lookupR, no], ?_⟩
        intro _
        exact ⟨_, member, by rw [List.getElem?_eq_getElem inside, no]⟩
      · exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, inside, lookupR, no, advance, run],
          spec⟩
    · exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, inside, advance, run], spec⟩
  · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], by simp⟩
termination_by parents.val.length - index.val
decreasing_by all_goals omega

theorem inherited_spec (rows : alloc.vec.Vec (alloc.vec.Vec U8)) (done : alloc.vec.Vec Bool)
    (parents : alloc.vec.Vec Usize) (b index : Usize) :
    ∃ r, classification.inherited rows done parents b index = .ok r ∧
      (r = true → ∃ p ∈ parents.val, ∃ row, rows.val[p.val]? = some row ∧
        row.val[b.val]? = some classification.YES) := by
  rw [classification.inherited]
  by_cases more : index.val < parents.val.length
  · have lookup : parents.index_usize index = .ok parents.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have member : parents.val[index.val] ∈ parents.val := List.getElem_mem more
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, run, spec⟩ := inherited_spec rows done parents b next
    by_cases doneIn : parents.val[index.val].val < done.val.length
    · by_cases rowsIn : parents.val[index.val].val < rows.val.length
      · have lookupD : done.index_usize parents.val[index.val] = .ok done.val[parents.val[index.val].val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem doneIn]
        have lookupR : rows.index_usize parents.val[index.val] = .ok rows.val[parents.val[index.val].val] := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem rowsIn]
        by_cases isDone : done.val[parents.val[index.val].val] = true
        · by_cases bIn : b.val < rows.val[parents.val[index.val].val].val.length
          · have lookupB : rows.val[parents.val[index.val].val].index_usize b =
                .ok rows.val[parents.val[index.val].val].val[b.val] := by
              simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem bIn]
            by_cases yes : rows.val[parents.val[index.val].val].val[b.val] = classification.YES
            · refine ⟨true, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, doneIn, rowsIn, lookupD,
                isDone, lookupR, bIn, lookupB, yes], ?_⟩
              intro _
              exact ⟨_, member, _, List.getElem?_eq_getElem rowsIn, by rw [List.getElem?_eq_getElem bIn, yes]⟩
            · exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, doneIn, rowsIn, lookupD,
                isDone, lookupR, bIn, lookupB, yes, advance, run], spec⟩
          · exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, doneIn, rowsIn, lookupD,
              isDone, lookupR, bIn, advance, run], spec⟩
        · exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, doneIn, rowsIn, lookupD,
            isDone, advance, run], spec⟩
      · exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, doneIn, rowsIn, advance, run], spec⟩
    · exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, doneIn, advance, run], spec⟩
  · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], by simp⟩
termination_by parents.val.length - index.val
decreasing_by all_goals omega

theorem unsatisfiable_spec (satisfiable : alloc.vec.Vec Bool) (b : Usize) :
    classification.unsatisfiable satisfiable b = .ok (decide (satisfiable.val[b.val]? = some false)) := by
  rw [classification.unsatisfiable]
  by_cases inside : b.val < satisfiable.val.length
  · have lookup : satisfiable.index_usize b = .ok satisfiable.val[b.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    cases value : satisfiable.val[b.val] <;>
      simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, value, List.getElem?_eq_getElem inside]
  · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, List.getElem?_eq_none (show
      satisfiable.val.length ≤ b.val by omega)]

theorem told_parent_spec (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (a b : Usize) :
    ∃ r, classification.told_parent parents a b = .ok r ∧
      (r = true → ∃ row, parents.val[a.val]? = some row ∧ b ∈ row.val) := by
  rw [classification.told_parent]
  by_cases inside : a.val < parents.val.length
  · have lookup : parents.index_usize a = .ok parents.val[a.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    refine ⟨_, by simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte,
      alloc.vec.Vec.index_slice_index, lookup, bind_ok, listed_spec]; rfl, ?_⟩
    intro listedIn
    refine ⟨_, List.getElem?_eq_getElem inside, ?_⟩
    simpa using listedIn
  · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside], by simp⟩

theorem refuted_spec (row : alloc.vec.Vec U8) (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (b : Usize) :
    ∃ r, classification.refuted row parents b = .ok r ∧
      (r = true → ∃ prow, parents.val[b.val]? = some prow ∧ ∃ p ∈ prow.val, row.val[p.val]? = some classification.NO) := by
  rw [classification.refuted]
  by_cases inside : b.val < parents.val.length
  · have lookup : parents.index_usize b = .ok parents.val[b.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨r, run, spec⟩ := refused_spec row parents.val[b.val] 0#usize
    refine ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, run], ?_⟩
    intro yes
    exact ⟨_, List.getElem?_eq_getElem inside, spec yes⟩
  · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside], by simp⟩

theorem inherits_spec (rows : alloc.vec.Vec (alloc.vec.Vec U8)) (done : alloc.vec.Vec Bool)
    (parents : alloc.vec.Vec (alloc.vec.Vec Usize)) (a b : Usize) :
    ∃ r, classification.inherits rows done parents a b = .ok r ∧
      (r = true → ∃ arow, parents.val[a.val]? = some arow ∧ ∃ q ∈ arow.val, ∃ qrow, rows.val[q.val]? = some qrow ∧
        qrow.val[b.val]? = some classification.YES) := by
  rw [classification.inherits]
  by_cases inside : a.val < parents.val.length
  · have lookup : parents.index_usize a = .ok parents.val[a.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨r, run, spec⟩ := inherited_spec rows done parents.val[a.val] b 0#usize
    refine ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, run], ?_⟩
    intro yes
    exact ⟨_, List.getElem?_eq_getElem inside, spec yes⟩
  · exact ⟨false, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside], by simp⟩

theorem ask_spec (items : alloc.vec.Vec AnnotatedAxiom) (prepared : data_ontology.Prepared)
    (data : Rowl.DataOntology.DataPrepared items prepared) (classes : alloc.vec.Vec Class) (a b : Usize) :
    ∃ r, classification.ask prepared classes a b = .ok r ∧ ∀ code, r = some code → (code.val = 1 ∨ code.val = 2) ∧
      ∀ ca cb, classes.val[a.val]? = some ca → classes.val[b.val]? = some cb → Right.{u,v,w} items.val ca cb code := by
  rw [classification.ask]
  by_cases aIn : a.val < classes.val.length
  · by_cases bIn : b.val < classes.val.length
    · have lookupA : classes.index_usize a = .ok classes.val[a.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem aIn]
      have lookupB : classes.index_usize b = .ok classes.val[b.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem bIn]
      have namedA : classification.named classes.val[a.val] = .ok (.Class classes.val[a.val]) := by
        simp [classification.named, Rowl.Nnf.copy_iri_identity]
      have namedB : classification.named classes.val[b.val] = .ok (.Class classes.val[b.val]) := by
        simp [classification.named, Rowl.Nnf.copy_iri_identity]
      obtain ⟨result, run, facts⟩ := Rowl.DataOntology.prepared_subsumed_correct.{u,v,w} items prepared data
        (.Class classes.val[a.val]) (.Class classes.val[b.val])
      cases result with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, aIn, bIn, lookupA, lookupB, namedA, namedB,
          run], by simp⟩
      | some answer =>
        cases answer with
        | true =>
          refine ⟨some classification.YES, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, aIn, bIn, lookupA,
            lookupB, namedA, namedB, run], ?_⟩
          intro code same
          cases same
          refine ⟨by rw [yes_val]; omega, ?_⟩
          intro ca cb at_a at_b
          rw [List.getElem?_eq_getElem aIn] at at_a
          rw [List.getElem?_eq_getElem bIn] at at_b
          cases Option.some.inj at_a
          cases Option.some.inj at_b
          refine ⟨fun _ _ D normative V vocabulary => (facts _ rfl D normative V vocabulary).mp rfl, ?_⟩
          intro one
          rw [yes_val] at one
          omega
        | false =>
          refine ⟨some classification.NO, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, aIn, bIn, lookupA,
            lookupB, namedA, namedB, run], ?_⟩
          intro code same
          cases same
          refine ⟨by rw [no_val]; omega, ?_⟩
          intro ca cb at_a at_b
          rw [List.getElem?_eq_getElem aIn] at at_a
          rw [List.getElem?_eq_getElem bIn] at at_b
          cases Option.some.inj at_a
          cases Option.some.inj at_b
          refine ⟨fun two => by rw [no_val] at two; omega, ?_⟩
          intro _ _ D normative V vocabulary sub
          exact Bool.false_ne_true ((facts _ rfl D normative V vocabulary).mpr sub)
    · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, aIn, bIn], by simp⟩
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, aIn], by simp⟩

/-- The context every answer is drawn from: right satisfiability answers,
    right told parents and right rows. -/
structure Context (items : List AnnotatedAxiom) (classes : List Class) (satisfiable : List Bool)
    (parents : List (alloc.vec.Vec Usize)) (rows : List (alloc.vec.Vec U8)) (done : List Bool) : Prop where
  satisfiable : SatisfiableRight.{u,v,w} items classes satisfiable
  parents : ParentsOk items classes parents
  rows : RowsRight.{u,v,w} items classes rows done

theorem decide_spec (items : alloc.vec.Vec AnnotatedAxiom) (prepared : data_ontology.Prepared)
    (data : Rowl.DataOntology.DataPrepared items prepared)
    (classes : alloc.vec.Vec Class) (satisfiable : alloc.vec.Vec Bool) (parents : alloc.vec.Vec (alloc.vec.Vec Usize))
    (rows : alloc.vec.Vec (alloc.vec.Vec U8)) (done : alloc.vec.Vec Bool) (row : alloc.vec.Vec U8) (a b : Usize)
    (context : Context.{u,v,w} items.val classes.val satisfiable.val parents.val rows.val done.val)
    (rowRight : RowRight.{u,v,w} items.val classes.val a.val row.val)
    (aSat : satisfiable.val[a.val]? = some true) :
    ∃ r, classification.decide prepared classes satisfiable parents rows done row a b = .ok r ∧
      ∀ code, r = some code → (code.val = 1 ∨ code.val = 2) ∧ ∀ ca cb, classes.val[a.val]? = some ca →
        classes.val[b.val]? = some cb → Right.{u,v,w} items.val ca cb code := by
  obtain ⟨satRight, parentsOk, rowsRight⟩ := context
  obtain ⟨_, _, ca0, at_a0, rowSpec⟩ := rowRight
  have satA : ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
      ClassSatisfiable.{u, max w v, w} D V items.val (.Class ca0) :=
    fun D normative V vocabulary => (satRight.2 a.val ca0 true at_a0 aSat D normative V vocabulary).mp rfl
  have yesCode : classification.YES.val = 1 ∨ classification.YES.val = 2 := by rw [yes_val]; omega
  have noCode : classification.NO.val = 1 ∨ classification.NO.val = 2 := by rw [no_val]; omega
  rw [classification.decide]
  by_cases same : a = b
  · subst same
    refine ⟨some classification.YES, by simp, ?_⟩
    intro code h
    cases h
    refine ⟨yesCode, ?_⟩
    intro ca cb at_a at_b
    rw [at_a] at at_b
    cases Option.some.inj at_b
    exact ⟨fun _ _ D _ V _ => subsumed_refl D V items.val _, fun one => by rw [yes_val] at one; omega⟩
  · rw [unsatisfiable_spec]
    by_cases unsatB : satisfiable.val[b.val]? = some false
    · refine ⟨some classification.NO, by simp [same, unsatB], ?_⟩
      intro code h
      cases h
      refine ⟨noCode, ?_⟩
      intro ca cb at_a at_b
      rw [at_a0] at at_a
      cases Option.some.inj at_a
      refine ⟨fun two => by rw [no_val] at two; omega, ?_⟩
      intro _ _ D normative V vocabulary
      exact not_subsumed_unsatisfiable D V items.val (satA D normative V vocabulary)
        (fun sat => Bool.false_ne_true ((satRight.2 b.val cb false at_b unsatB D normative V vocabulary).mpr sat))
    · obtain ⟨t, tRun, tSpec⟩ := told_parent_spec parents a b
      cases t with
      | true =>
        refine ⟨some classification.YES, by simp [same, unsatB, tRun], ?_⟩
        intro code h
        cases h
        refine ⟨yesCode, ?_⟩
        intro ca cb at_a at_b
        obtain ⟨prow, at_prow, member⟩ := tSpec rfl
        obtain ⟨child, parent, at_child, at_parent, told⟩ := parentsOk.2 a.val prow at_prow b member
        rw [at_a] at at_child
        rw [at_b] at at_parent
        cases Option.some.inj at_child
        cases Option.some.inj at_parent
        exact ⟨fun _ _ D _ V _ => told_subsumed D V items.val told, fun one => by rw [yes_val] at one; omega⟩
      | false =>
        obtain ⟨f, fRun, fSpec⟩ := refuted_spec row parents b
        cases f with
        | true =>
          refine ⟨some classification.NO, by simp [same, unsatB, tRun, fRun], ?_⟩
          intro code h
          cases h
          refine ⟨noCode, ?_⟩
          intro ca cb at_a at_b
          rw [at_a0] at at_a
          cases Option.some.inj at_a
          obtain ⟨prow, at_prow, p, member, at_p⟩ := fSpec rfl
          obtain ⟨child, parent, at_child, at_parent, told⟩ := parentsOk.2 b.val prow at_prow p member
          rw [at_b] at at_child
          cases Option.some.inj at_child
          have refutedRight := rowSpec p.val classification.NO parent at_p at_parent
          refine ⟨fun two => by rw [no_val] at two; omega, ?_⟩
          intro _ _ D normative V vocabulary sub
          exact refutedRight.2 no_val D normative V vocabulary
            (subsumed_trans D V items.val sub (told_subsumed D V items.val told))
        | false =>
          obtain ⟨i, iRun, iSpec⟩ := inherits_spec rows done parents a b
          cases i with
          | true =>
            refine ⟨some classification.YES, by simp [same, unsatB, tRun, fRun, iRun], ?_⟩
            intro code h
            cases h
            refine ⟨yesCode, ?_⟩
            intro ca cb at_a at_b
            obtain ⟨arow, at_arow, q, member, qrow, at_qrow, at_qb⟩ := iSpec rfl
            obtain ⟨child, parent, at_child, at_parent, told⟩ := parentsOk.2 a.val arow at_arow q member
            rw [at_a] at at_child
            cases Option.some.inj at_child
            obtain ⟨⟨_, _, cq, at_cq, qSpec⟩, _⟩ := rowsRight.2.2 q.val qrow at_qrow
            rw [at_parent] at at_cq
            cases Option.some.inj at_cq
            have inheritedRight := qSpec b.val classification.YES cb at_qb at_b
            exact ⟨fun _ _ D normative V vocabulary => subsumed_trans D V items.val
                (told_subsumed D V items.val told) (inheritedRight.1 yes_val D normative V vocabulary),
              fun one => by rw [yes_val] at one; omega⟩
          | false =>
            obtain ⟨r, rRun, rSpec⟩ := ask_spec.{u,v,w} items prepared data classes a b
            exact ⟨r, by simp [same, unsatB, tRun, fRun, iRun, rRun], rSpec⟩

theorem unknown_at_spec (row : alloc.vec.Vec U8) (b : Usize) :
    classification.unknown_at row b = .ok (decide (row.val[b.val]? = some classification.UNKNOWN)) := by
  rw [classification.unknown_at]
  by_cases inside : b.val < row.val.length
  · have lookup : row.index_usize b = .ok row.val[b.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, lookup, List.getElem?_eq_getElem inside]
  · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, List.getElem?_eq_none (show
      row.val.length ≤ b.val by omega)]

/-- Setting a right answer keeps a row right. -/
private theorem row_right_set (items : List AnnotatedAxiom) (classes : List Class) (a : Nat) (row : alloc.vec.Vec U8)
    (b : Usize) (code : U8) (rowRight : RowRight.{u,v,w} items classes a row.val) (small : code.val ≤ 2)
    (answer : ∀ ca cb, classes[a]? = some ca → classes[b.val]? = some cb → Right.{u,v,w} items ca cb code) :
    RowRight.{u,v,w} items classes a (row.set b code).val := by
  obtain ⟨length, codes, ca, at_a, spec⟩ := rowRight
  refine ⟨by simp [length], ?_, ca, at_a, ?_⟩
  · intro b' code' at_b'
    rw [alloc.vec.Vec.set_val_eq] at at_b'
    by_cases same : b' = b.val
    · subst same
      have inside : b.val < row.val.length := by
        have := (List.getElem?_eq_some_iff.mp at_b').1
        simpa using this
      rw [List.getElem?_set_self inside] at at_b'
      cases Option.some.inj at_b'
      exact small
    · rw [List.getElem?_set_ne (Ne.symm same)] at at_b'
      exact codes b' code' at_b'
  intro b' code' cb at_b' at_cb
  rw [alloc.vec.Vec.set_val_eq] at at_b'
  by_cases same : b' = b.val
  · subst same
    have inside : b.val < row.val.length := by
      have := (List.getElem?_eq_some_iff.mp at_b').1
      simpa using this
    rw [List.getElem?_set_self inside] at at_b'
    cases Option.some.inj at_b'
    exact answer ca cb at_a at_cb
  · rw [List.getElem?_set_ne (Ne.symm same)] at at_b'
    exact spec b' code' cb at_b' at_cb

theorem fill_spec (items : alloc.vec.Vec AnnotatedAxiom) (prepared : data_ontology.Prepared)
    (data : Rowl.DataOntology.DataPrepared items prepared)
    (classes : alloc.vec.Vec Class) (satisfiable : alloc.vec.Vec Bool) (parents : alloc.vec.Vec (alloc.vec.Vec Usize))
    (rows : alloc.vec.Vec (alloc.vec.Vec U8)) (done : alloc.vec.Vec Bool) (order : alloc.vec.Vec Usize) (a : Usize)
    (context : Context.{u,v,w} items.val classes.val satisfiable.val parents.val rows.val done.val)
    (aSat : satisfiable.val[a.val]? = some true) (index : Usize) (row : alloc.vec.Vec U8)
    (rowRight : RowRight.{u,v,w} items.val classes.val a.val row.val) :
    ∃ r, classification.fill prepared classes satisfiable parents rows done order a index row = .ok r ∧
      ∀ row', r = some row' → RowRight.{u,v,w} items.val classes.val a.val row'.val := by
  rw [classification.fill]
  by_cases more : index.val < order.val.length
  · have lookup : order.index_usize index = .ok order.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    by_cases unknown : row.val[order.val[index.val].val]? = some classification.UNKNOWN
    · obtain ⟨d, dRun, dSpec⟩ := decide_spec.{u,v,w} items prepared data classes satisfiable parents rows done row a
        order.val[index.val] context rowRight aSat
      cases d with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, unknown_at_spec, unknown, dRun], by simp⟩
      | some answer =>
        have inside : order.val[index.val].val < row.val.length := (List.getElem?_eq_some_iff.mp unknown).1
        obtain ⟨codes, answerRight⟩ := dSpec answer rfl
        obtain ⟨r, run, spec⟩ := fill_spec items prepared data classes satisfiable parents rows done order a context
          aSat next (row.set order.val[index.val] answer)
          (row_right_set items.val classes.val a.val row order.val[index.val] answer rowRight (by omega) answerRight)
        refine ⟨r, ?_, spec⟩
        simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, unknown_at_spec, unknown, dRun, alloc.vec.Vec.index_mut_usize,
          alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside, advance, run]
    · obtain ⟨r, run, spec⟩ := fill_spec items prepared data classes satisfiable parents rows done order a context
        aSat next row rowRight
      exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, unknown_at_spec, unknown, advance, run], spec⟩
  · exact ⟨some row, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], by intro row' same; cases same; exact rowRight⟩
termination_by order.val.length - index.val
decreasing_by all_goals omega

theorem fill_rest_spec (items : alloc.vec.Vec AnnotatedAxiom) (prepared : data_ontology.Prepared)
    (data : Rowl.DataOntology.DataPrepared items prepared)
    (classes : alloc.vec.Vec Class) (satisfiable : alloc.vec.Vec Bool) (parents : alloc.vec.Vec (alloc.vec.Vec Usize))
    (rows : alloc.vec.Vec (alloc.vec.Vec U8)) (done : alloc.vec.Vec Bool) (a : Usize)
    (context : Context.{u,v,w} items.val classes.val satisfiable.val parents.val rows.val done.val)
    (aSat : satisfiable.val[a.val]? = some true) (b : Usize) (row : alloc.vec.Vec U8)
    (rowRight : RowRight.{u,v,w} items.val classes.val a.val row.val)
    (before : ∀ k code, k < b.val → row.val[k]? = some code → code.val = 1 ∨ code.val = 2) :
    ∃ r, classification.fill_rest prepared classes satisfiable parents rows done a b row = .ok r ∧
      ∀ row', r = some row' → RowRight.{u,v,w} items.val classes.val a.val row'.val ∧ Complete row'.val := by
  rw [classification.fill_rest]
  by_cases more : b.val < row.val.length
  · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := b) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = b.val + 1 := by simpa using nextValue
    have lookupRow : row.index_usize b = .ok row.val[b.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    by_cases unknown : row.val[b.val] = classification.UNKNOWN
    · obtain ⟨d, dRun, dSpec⟩ := decide_spec.{u,v,w} items prepared data classes satisfiable parents rows done row a b
        context rowRight aSat
      cases d with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookupRow, unknown, dRun], by simp⟩
      | some answer =>
        obtain ⟨nonzero, answerRight⟩ := dSpec answer rfl
        obtain ⟨r, run, spec⟩ := fill_rest_spec items prepared data classes satisfiable parents rows done a context
          aSat next (row.set b answer)
          (row_right_set items.val classes.val a.val row b answer rowRight (by omega) answerRight)
          (by
            intro k code low at_k
            rw [alloc.vec.Vec.set_val_eq] at at_k
            by_cases same : k = b.val
            · subst same
              rw [List.getElem?_set_self more] at at_k
              cases Option.some.inj at_k
              exact nonzero
            · rw [List.getElem?_set_ne (Ne.symm same)] at at_k
              exact before k code (by omega) at_k)
        refine ⟨r, ?_, spec⟩
        simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookupRow, unknown, dRun, alloc.vec.Vec.index_mut_usize,
          alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more, advance, run]
    · obtain ⟨r, run, spec⟩ := fill_rest_spec items prepared data classes satisfiable parents rows done a context
        aSat next row rowRight
        (by
          intro k code low at_k
          by_cases same : k = b.val
          · subst same
            have small := rowRight.2.1 b.val code at_k
            rw [List.getElem?_eq_getElem more] at at_k
            have isCode := Option.some.inj at_k
            have nonzero : code.val ≠ 0 := by
              intro zero
              apply unknown
              rw [isCode]
              exact UScalar.eq_of_val_eq (by rw [zero, unknown_val])
            omega
          · exact before k code (by omega) at_k)
      exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookupRow, unknown, advance, run], spec⟩
  · refine ⟨some row, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], ?_⟩
    intro row' same
    cases same
    refine ⟨rowRight, ?_⟩
    intro k code at_k
    exact before k code (by have := (List.getElem?_eq_some_iff.mp at_k).1; omega) at_k
termination_by row.val.length - b.val
decreasing_by all_goals first | omega | (simp; omega)

theorem row_of_spec (items : alloc.vec.Vec AnnotatedAxiom) (prepared : data_ontology.Prepared)
    (data : Rowl.DataOntology.DataPrepared items prepared)
    (classes : alloc.vec.Vec Class) (satisfiable : alloc.vec.Vec Bool) (parents : alloc.vec.Vec (alloc.vec.Vec Usize))
    (rows : alloc.vec.Vec (alloc.vec.Vec U8)) (done : alloc.vec.Vec Bool) (order : alloc.vec.Vec Usize) (a : Usize)
    (context : Context.{u,v,w} items.val classes.val satisfiable.val parents.val rows.val done.val)
    (aIn : a.val < classes.val.length) :
    ∃ r, classification.row_of prepared classes satisfiable parents rows done order a = .ok r ∧
      ∀ row, r = some row → RowRight.{u,v,w} items.val classes.val a.val row.val ∧ Complete row.val := by
  have satLength := context.satisfiable.1
  have satIn : a.val < satisfiable.val.length := by omega
  have lookup : satisfiable.index_usize a = .ok satisfiable.val[a.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem satIn]
  obtain ⟨ca, at_a⟩ : ∃ ca, classes.val[a.val]? = some ca := ⟨_, List.getElem?_eq_getElem aIn⟩
  rw [classification.row_of]
  cases value : satisfiable.val[a.val] with
  | true =>
    have aSat : satisfiable.val[a.val]? = some true := by rw [List.getElem?_eq_getElem satIn, value]
    obtain ⟨blank, blankRun, blankLength, blankAll⟩ := filled_spec (alloc.vec.Vec.len classes)
      classification.UNKNOWN (alloc.vec.Vec.new U8) (by simp) (by simp)
    have blankRight : RowRight.{u,v,w} items.val classes.val a.val blank.val := by
      refine ⟨by simpa using blankLength, ?_, ca, at_a, ?_⟩
      · intro b code at_b
        have isUnknown := blankAll code (List.mem_of_getElem? at_b)
        subst isUnknown
        simp [unknown_val]
      intro b code cb at_b _
      have isUnknown := blankAll code (List.mem_of_getElem? at_b)
      subst isUnknown
      exact ⟨fun two => by rw [unknown_val] at two; omega, fun one => by rw [unknown_val] at one; omega⟩
    obtain ⟨f, fRun, fSpec⟩ := fill_spec.{u,v,w} items prepared data classes satisfiable parents rows done order a
      context aSat 0#usize blank blankRight
    cases f with
    | none =>
      exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, satIn, lookup, value, blankRun, fRun], by simp⟩
    | some filledRow =>
      obtain ⟨r, run, spec⟩ := fill_rest_spec.{u,v,w} items prepared data classes satisfiable parents rows done a
        context aSat 0#usize filledRow (fSpec filledRow rfl) (by intro k code low; simp at low)
      exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, satIn, lookup, value, blankRun, fRun, run], spec⟩
  | false =>
    have aUnsat : satisfiable.val[a.val]? = some false := by rw [List.getElem?_eq_getElem satIn, value]
    obtain ⟨full, fullRun, fullLength, fullAll⟩ := filled_spec (alloc.vec.Vec.len classes)
      classification.YES (alloc.vec.Vec.new U8) (by simp) (by simp)
    refine ⟨some full, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, satIn, lookup, value, fullRun], ?_⟩
    intro row same
    cases same
    refine ⟨⟨by simpa using fullLength, ?_, ca, at_a, ?_⟩, ?_⟩
    · intro b code at_b
      have isYes := fullAll code (List.mem_of_getElem? at_b)
      subst isYes
      simp [yes_val]
    · intro b code cb at_b _
      have isYes := fullAll code (List.mem_of_getElem? at_b)
      subst isYes
      refine ⟨fun _ _ D normative V vocabulary => unsatisfiable_subsumed D V items.val _ (fun sat =>
        Bool.false_ne_true ((context.satisfiable.2 a.val ca false at_a aUnsat D normative V vocabulary).mpr sat)), ?_⟩
      intro one
      rw [yes_val] at one
      omega
    · intro b code at_b
      have isYes := fullAll code (List.mem_of_getElem? at_b)
      subst isYes
      simp [yes_val]

/-- The rows after classifying every class from `a` on: every row right and
    complete. -/
def Classified (items : List AnnotatedAxiom) (classes : List Class) (rows : List (alloc.vec.Vec U8)) : Prop :=
  rows.length = classes.length ∧
  ∀ (q : Nat) (row : alloc.vec.Vec U8), rows[q]? = some row → RowRight.{u,v,w} items classes q row.val ∧ Complete row.val

theorem classify_rest_spec (items : alloc.vec.Vec AnnotatedAxiom) (prepared : data_ontology.Prepared)
    (data : Rowl.DataOntology.DataPrepared items prepared)
    (classes : alloc.vec.Vec Class) (satisfiable : alloc.vec.Vec Bool) (parents : alloc.vec.Vec (alloc.vec.Vec Usize))
    (order : alloc.vec.Vec Usize) (a : Usize) (rows : alloc.vec.Vec (alloc.vec.Vec U8)) (done : alloc.vec.Vec Bool)
    (context : Context.{u,v,w} items.val classes.val satisfiable.val parents.val rows.val done.val)
    (before : ∀ q, q < a.val → done.val[q]? = some true) :
    ∃ r, classification.classify_rest prepared classes satisfiable parents order a rows done = .ok r ∧
      ∀ rows', r = some rows' → Classified.{u,v,w} items.val classes.val rows'.val := by
  obtain ⟨satRight, parentsOk, rowsLength, doneLength, rowsSpec⟩ := context
  rw [classification.classify_rest]
  by_cases more : a.val < rows.val.length
  · have moreDone : a.val < done.val.length := by omega
    have lookupD : done.index_usize a = .ok done.val[a.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem moreDone]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := a) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = a.val + 1 := by simpa using nextValue
    cases isDone : done.val[a.val] with
    | true =>
      obtain ⟨r, run, spec⟩ := classify_rest_spec items prepared data classes satisfiable parents order next rows done
        ⟨satRight, parentsOk, rowsLength, doneLength, rowsSpec⟩
        (by
          intro q low
          by_cases same : q = a.val
          · subst same; rw [List.getElem?_eq_getElem moreDone, isDone]
          · exact before q (by omega))
      exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, moreDone, lookupD, isDone, advance, run], spec⟩
    | false =>
      obtain ⟨row, rowRun, rowSpec⟩ := row_of_spec.{u,v,w} items prepared data classes satisfiable parents rows done
        order a ⟨satRight, parentsOk, rowsLength, doneLength, rowsSpec⟩ (by omega)
      cases row with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, moreDone, lookupD, isDone, rowRun],
          by simp⟩
      | some newRow =>
        obtain ⟨newRight, newComplete⟩ := rowSpec newRow rfl
        have context' : Context.{u,v,w} items.val classes.val satisfiable.val parents.val (rows.set a newRow).val
            (done.set a true).val := by
          refine ⟨satRight, parentsOk, by simp [rowsLength], by simp [doneLength], ?_⟩
          intro q qrow at_q
          rw [alloc.vec.Vec.set_val_eq] at at_q
          by_cases same : q = a.val
          · subst same
            rw [List.getElem?_set_self more] at at_q
            cases Option.some.inj at_q
            exact ⟨newRight, fun _ => newComplete⟩
          · rw [List.getElem?_set_ne (Ne.symm same)] at at_q
            obtain ⟨qRight, qComplete⟩ := rowsSpec q qrow at_q
            refine ⟨qRight, fun qDone => qComplete ?_⟩
            rw [alloc.vec.Vec.set_val_eq, List.getElem?_set_ne (Ne.symm same)] at qDone
            exact qDone
        obtain ⟨r, run, spec⟩ := classify_rest_spec items prepared data classes satisfiable parents order next
          (rows.set a newRow) (done.set a true) context'
          (by
            intro q low
            rw [alloc.vec.Vec.set_val_eq]
            by_cases same : q = a.val
            · subst same; rw [List.getElem?_set_self moreDone]
            · rw [List.getElem?_set_ne (Ne.symm same)]; exact before q (by omega))
        refine ⟨r, ?_, spec⟩
        simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, moreDone, lookupD, isDone, rowRun,
          alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more,
          List.getElem?_eq_getElem moreDone, advance, run]
  · refine ⟨some rows, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], ?_⟩
    intro rows' same
    cases same
    refine ⟨rowsLength, ?_⟩
    intro q row at_q
    obtain ⟨qRight, qComplete⟩ := rowsSpec q row at_q
    exact ⟨qRight, qComplete (before q (by have := (List.getElem?_eq_some_iff.mp at_q).1; omega))⟩
termination_by rows.val.length - a.val
decreasing_by all_goals first | omega | (simp; omega)

theorem classify_from_spec (items : alloc.vec.Vec AnnotatedAxiom) (prepared : data_ontology.Prepared)
    (data : Rowl.DataOntology.DataPrepared items prepared)
    (classes : alloc.vec.Vec Class) (satisfiable : alloc.vec.Vec Bool) (parents : alloc.vec.Vec (alloc.vec.Vec Usize))
    (order : alloc.vec.Vec Usize) (index : Usize) (rows : alloc.vec.Vec (alloc.vec.Vec U8)) (done : alloc.vec.Vec Bool)
    (context : Context.{u,v,w} items.val classes.val satisfiable.val parents.val rows.val done.val) :
    ∃ r, classification.classify_from prepared classes satisfiable parents order index rows done = .ok r ∧
      ∀ rows', r = some rows' → Classified.{u,v,w} items.val classes.val rows'.val := by
  obtain ⟨satRight, parentsOk, rowsLength, doneLength, rowsSpec⟩ := context
  rw [classification.classify_from]
  by_cases more : index.val < order.val.length
  · have lookup : order.index_usize index = .ok order.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    have skip : ∃ r, classification.classify_from prepared classes satisfiable parents order next rows done = .ok r ∧
        ∀ rows', r = some rows' → Classified.{u,v,w} items.val classes.val rows'.val :=
      classify_from_spec items prepared data classes satisfiable parents order next rows done
        ⟨satRight, parentsOk, rowsLength, doneLength, rowsSpec⟩
    by_cases fresh : order.val[index.val].val < rows.val.length ∧ order.val[index.val].val < done.val.length ∧
        done.val[order.val[index.val].val]? = some false
    · obtain ⟨inRows, inDone, notDone⟩ := fresh
      have lookupD : done.index_usize order.val[index.val] = .ok done.val[order.val[index.val].val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inDone]
      have isFalse : done.val[order.val[index.val].val] = false := by
        rw [List.getElem?_eq_getElem inDone] at notDone; exact Option.some.inj notDone
      obtain ⟨row, rowRun, rowSpec⟩ := row_of_spec.{u,v,w} items prepared data classes satisfiable parents rows done
        order order.val[index.val] ⟨satRight, parentsOk, rowsLength, doneLength, rowsSpec⟩ (by omega)
      cases row with
      | none =>
        exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, inRows, inDone, lookupD, isFalse,
          rowRun], by simp⟩
      | some newRow =>
        obtain ⟨newRight, newComplete⟩ := rowSpec newRow rfl
        have context' : Context.{u,v,w} items.val classes.val satisfiable.val parents.val
            (rows.set order.val[index.val] newRow).val (done.set order.val[index.val] true).val := by
          refine ⟨satRight, parentsOk, by simp [rowsLength], by simp [doneLength], ?_⟩
          intro q qrow at_q
          rw [alloc.vec.Vec.set_val_eq] at at_q
          by_cases same : q = order.val[index.val].val
          · subst same
            rw [List.getElem?_set_self inRows] at at_q
            cases Option.some.inj at_q
            exact ⟨newRight, fun _ => newComplete⟩
          · rw [List.getElem?_set_ne (Ne.symm same)] at at_q
            obtain ⟨qRight, qComplete⟩ := rowsSpec q qrow at_q
            refine ⟨qRight, fun qDone => qComplete ?_⟩
            rw [alloc.vec.Vec.set_val_eq, List.getElem?_set_ne (Ne.symm same)] at qDone
            exact qDone
        obtain ⟨r, run, spec⟩ := classify_from_spec items prepared data classes satisfiable parents order next
          (rows.set order.val[index.val] newRow) (done.set order.val[index.val] true) context'
        refine ⟨r, ?_, spec⟩
        simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, inRows, inDone, lookupD, isFalse, rowRun,
          alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inRows,
          List.getElem?_eq_getElem inDone, advance, run]
    · obtain ⟨r, run, spec⟩ := skip
      refine ⟨r, ?_, spec⟩
      by_cases inRows : order.val[index.val].val < rows.val.length
      · by_cases inDone : order.val[index.val].val < done.val.length
        · have lookupD : done.index_usize order.val[index.val] = .ok done.val[order.val[index.val].val] := by
            simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inDone]
          have isTrue : done.val[order.val[index.val].val] = true := by
            cases value : done.val[order.val[index.val].val]
            · exact absurd ⟨inRows, inDone, by rw [List.getElem?_eq_getElem inDone, value]⟩ fresh
            · rfl
          simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, inRows, inDone, lookupD, isTrue, advance, run]
        · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, inRows, inDone, advance, run]
      · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, inRows, advance, run]
  · obtain ⟨r, run, spec⟩ := classify_rest_spec.{u,v,w} items prepared data classes satisfiable parents order 0#usize
      rows done ⟨satRight, parentsOk, rowsLength, doneLength, rowsSpec⟩ (by intro q low; simp at low)
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, run], spec⟩
termination_by order.val.length - index.val
decreasing_by all_goals omega

theorem satisfiable_from_spec (items : alloc.vec.Vec AnnotatedAxiom) (prepared : data_ontology.Prepared)
    (data : Rowl.DataOntology.DataPrepared items prepared) (classes : alloc.vec.Vec Class) (index : Usize)
    (out : alloc.vec.Vec Bool) (lengthIs : out.val.length = index.val) (inside : index.val ≤ classes.val.length)
    (sofar : ∀ i c s, i < index.val → classes.val[i]? = some c → out.val[i]? = some s →
      ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
        (s = true ↔ ClassSatisfiable.{u, max w v, w} D V items.val (.Class c))) :
    ∃ r, classification.satisfiable_from prepared classes index out = .ok r ∧
      ∀ answers, r = some answers → SatisfiableRight.{u,v,w} items.val classes.val answers.val := by
  rw [classification.satisfiable_from]
  by_cases more : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have namedC : classification.named classes.val[index.val] = .ok (.Class classes.val[index.val]) := by
      simp [classification.named, Rowl.Nnf.copy_iri_identity]
    obtain ⟨result, run, facts⟩ := Rowl.DataOntology.prepared_class_satisfiable_correct.{u,v,w} items prepared data
      (.Class classes.val[index.val])
    cases result with
    | none => exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, namedC, run], by simp⟩
    | some answer =>
      have room : out.val.length < Usize.max := by have := classes.property; omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out answer room)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, rRun, rSpec⟩ := satisfiable_from_spec items prepared data classes next pushed
        (by rw [contents, nextIndex]; simp [lengthIs]) (by omega)
        (by
          intro i c s low at_c at_s
          rw [contents] at at_s
          by_cases same : i = index.val
          · subst same
            rw [List.getElem?_append_right (by omega), lengthIs, Nat.sub_self] at at_s
            simp only [List.getElem?_cons_zero, Option.some.injEq] at at_s
            subst at_s
            rw [List.getElem?_eq_getElem more] at at_c
            cases Option.some.inj at_c
            exact facts answer rfl
          · rw [List.getElem?_append_left (by omega)] at at_s
            exact sofar i c s (by omega) at_c at_s)
      exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, namedC, run, usize_max_val, room,
        push, advance, rRun], rSpec⟩
  · refine ⟨some out, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], ?_⟩
    intro answers same
    cases same
    refine ⟨by omega, ?_⟩
    intro i c s at_c at_s
    exact sofar i c s (by have := (List.getElem?_eq_some_iff.mp at_c).1; omega) at_c at_s
termination_by classes.val.length - index.val
decreasing_by omega

/-! ### The answer matrix -/

theorem answers_spec (row : alloc.vec.Vec U8) (index : Usize) (out : alloc.vec.Vec Bool)
    (lengthIs : out.val.length = index.val) (inside : index.val ≤ row.val.length)
    (sofar : ∀ (j : Nat) (code : U8), j < index.val → row.val[j]? = some code →
      out.val[j]? = some (decide (code = classification.YES))) :
    ∃ r, classification.answers row index out = .ok r ∧ r.val.length = row.val.length ∧
      ∀ (j : Nat) (code : U8), row.val[j]? = some code → r.val[j]? = some (decide (code = classification.YES)) := by
  rw [classification.answers]
  by_cases more : index.val < row.val.length
  · have room : out.val.length < Usize.max := by have := row.property; omega
    have lookup : row.index_usize index = .ok row.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (decide (row.val[index.val] = classification.YES)) room)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, run, length, spec⟩ := answers_spec row next pushed (by rw [contents, nextIndex]; simp [lengthIs])
      (by omega)
      (by
        intro j code low at_j
        rw [contents]
        by_cases same : j = index.val
        · subst same
          rw [List.getElem?_append_right (by omega), lengthIs, Nat.sub_self]
          rw [List.getElem?_eq_getElem more] at at_j
          cases Option.some.inj at_j
          simp
        · rw [List.getElem?_append_left (by omega)]
          exact sofar j code (by omega) at_j)
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, usize_max_val, room, lookup, push, advance, run],
      length, spec⟩
  · refine ⟨out, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], by omega, ?_⟩
    intro j code at_j
    exact sofar j code (by have := (List.getElem?_eq_some_iff.mp at_j).1; omega) at_j
termination_by row.val.length - index.val
decreasing_by omega

theorem all_answers_spec (rows : alloc.vec.Vec (alloc.vec.Vec U8)) (index : Usize)
    (out : alloc.vec.Vec (alloc.vec.Vec Bool)) (lengthIs : out.val.length = index.val)
    (inside : index.val ≤ rows.val.length)
    (sofar : ∀ (q : Nat) (row : alloc.vec.Vec U8), q < index.val → rows.val[q]? = some row →
      ∃ answers : alloc.vec.Vec Bool, out.val[q]? = some answers ∧
        ∀ (j : Nat) (code : U8), row.val[j]? = some code → answers.val[j]? = some (decide (code = classification.YES))) :
    ∃ r, classification.all_answers rows index out = .ok r ∧ r.val.length = rows.val.length ∧
      ∀ (q : Nat) (row : alloc.vec.Vec U8), rows.val[q]? = some row → ∃ answers : alloc.vec.Vec Bool,
        r.val[q]? = some answers ∧
        ∀ (j : Nat) (code : U8), row.val[j]? = some code → answers.val[j]? = some (decide (code = classification.YES)) := by
  rw [classification.all_answers]
  by_cases more : index.val < rows.val.length
  · have room : out.val.length < Usize.max := by have := rows.property; omega
    have lookup : rows.index_usize index = .ok rows.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨answers, answersRun, _, answersSpec⟩ := answers_spec rows.val[index.val] 0#usize
      (alloc.vec.Vec.new Bool) (by simp) (by simp) (by intro j code low; simp at low)
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out answers room)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, run, length, spec⟩ := all_answers_spec rows next pushed
      (by rw [contents, nextIndex]; simp [lengthIs]) (by omega)
      (by
        intro q row low at_q
        rw [contents]
        by_cases same : q = index.val
        · subst same
          rw [List.getElem?_eq_getElem more] at at_q
          cases Option.some.inj at_q
          refine ⟨answers, ?_, answersSpec⟩
          rw [List.getElem?_append_right (by omega), lengthIs, Nat.sub_self]
          simp
        · rw [List.getElem?_append_left (by omega)]
          exact sofar q row (by omega) at_q)
    exact ⟨r, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, usize_max_val, room, lookup, answersRun, push,
      advance, run], length, spec⟩
  · refine ⟨out, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], by omega, ?_⟩
    intro q row at_q
    exact sofar q row (by have := (List.getElem?_eq_some_iff.mp at_q).1; omega) at_q
termination_by rows.val.length - index.val
decreasing_by omega

/-! ### Classification -/

/-- Classification is right: whenever it answers, it lists, for every listed
    class, whether the class is satisfiable and, for every pair of listed classes,
    whether the first is subsumed by the second, exactly as the semantics decides
    over every vocabulary and normative datatype map. -/
theorem classify_correct (items : alloc.vec.Vec AnnotatedAxiom) (prepared : data_ontology.Prepared)
    (data : Rowl.DataOntology.DataPrepared items prepared) (classes : alloc.vec.Vec Class) :
    ∃ r, classification.classify prepared items classes = .ok r ∧
      ∀ result, r = some result →
        result.satisfiable.val.length = classes.val.length ∧
        result.subsumed.val.length = classes.val.length ∧
        (∀ (i : Nat) (a : Class), classes.val[i]? = some a → ∃ s : Bool, result.satisfiable.val[i]? = some s ∧
          ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
            (s = true ↔ ClassSatisfiable.{u, max w v, w} D V items.val (.Class a))) ∧
        (∀ (i j : Nat) (a b : Class), classes.val[i]? = some a → classes.val[j]? = some b →
          ∃ (row : alloc.vec.Vec Bool) (s : Bool), result.subsumed.val[i]? = some row ∧ row.val[j]? = some s ∧
            ∀ {Native : Type w} (D : DatatypeMap Native) (_ : Normative D) (V : Vocabulary), IsVocabulary D V →
              (s = true ↔ Subsumed.{u, max w v, w} D V items.val (.Class a) (.Class b))) := by
  rw [classification.classify]
  obtain ⟨sat, satRun, satSpec⟩ := satisfiable_from_spec.{u,v,w} items prepared data classes 0#usize
    (alloc.vec.Vec.new Bool) (by simp) (by simp) (by intro i c s low; simp at low)
  cases sat with
  | none => exact ⟨none, by simp [satRun], by simp⟩
  | some answers =>
    have satRight := satSpec answers rfl
    obtain ⟨parents, parentsRun, parentsOk⟩ := told_spec items classes
    obtain ⟨zero, zeroRun, _⟩ := zeros_spec (alloc.vec.Vec.len classes) (alloc.vec.Vec.new Usize) (by simp)
    obtain ⟨depth, depthRun, _⟩ := depths_spec parents zero 32#usize 32#usize
    obtain ⟨order, orderRun⟩ := levels_spec depth 0#usize 32#usize (alloc.vec.Vec.new Usize)
    obtain ⟨rows, rowsRun, rowsLength, rowsAll⟩ := unknown_rows_spec (alloc.vec.Vec.len classes)
      (alloc.vec.Vec.new (alloc.vec.Vec U8)) (by simp) (by simp)
    obtain ⟨done, doneRun, doneLength, doneAll⟩ := unclassified_spec (alloc.vec.Vec.len classes)
      (alloc.vec.Vec.new Bool) (by simp) (by simp)
    have rowsLen : rows.val.length = classes.val.length := by simpa using rowsLength
    have context : Context.{u,v,w} items.val classes.val answers.val parents.val rows.val done.val := by
      refine ⟨satRight, parentsOk, rowsLen, by simpa using doneLength, ?_⟩
      intro q row at_q
      obtain ⟨rowLength, rowAll⟩ := rowsAll row (List.mem_of_getElem? at_q)
      have qIn : q < classes.val.length := by
        have := (List.getElem?_eq_some_iff.mp at_q).1
        omega
      refine ⟨⟨by simpa using rowLength, ?_, classes.val[q], List.getElem?_eq_getElem qIn, ?_⟩, ?_⟩
      · intro b code at_b
        have isUnknown := rowAll code (List.mem_of_getElem? at_b)
        subst isUnknown
        simp [unknown_val]
      · intro b code cb at_b _
        have isUnknown := rowAll code (List.mem_of_getElem? at_b)
        subst isUnknown
        exact ⟨fun two => by rw [unknown_val] at two; omega, fun one => by rw [unknown_val] at one; omega⟩
      · intro isDone
        have := doneAll true (List.mem_of_getElem? isDone)
        cases this
    obtain ⟨c, cRun, cSpec⟩ := classify_from_spec.{u,v,w} items prepared data classes answers parents order 0#usize
      rows done context
    cases c with
    | none =>
      exact ⟨none, by simp [satRun, parentsRun, zeroRun, depthRun, orderRun, rowsRun, doneRun, cRun], by simp⟩
    | some final =>
      obtain ⟨finalLength, finalSpec⟩ := cSpec final rfl
      obtain ⟨subsumed, subsumedRun, subsumedLength, subsumedSpec⟩ := all_answers_spec final 0#usize
        (alloc.vec.Vec.new (alloc.vec.Vec Bool)) (by simp) (by simp) (by intro q row low; simp at low)
      refine ⟨some { satisfiable := answers, subsumed := subsumed }, by simp [satRun, parentsRun, zeroRun, depthRun,
        orderRun, rowsRun, doneRun, cRun, subsumedRun], ?_⟩
      intro result same
      cases same
      refine ⟨satRight.1, by rw [subsumedLength, finalLength], ?_, ?_⟩
      · intro i a at_a
        have iIn : i < answers.val.length := by
          have := (List.getElem?_eq_some_iff.mp at_a).1
          rw [satRight.1]
          exact this
        exact ⟨answers.val[i], List.getElem?_eq_getElem iIn,
          fun D normative V vocabulary => satRight.2 i a _ at_a (List.getElem?_eq_getElem iIn) D normative V vocabulary⟩
      · intro i j a b at_a at_b
        have iIn : i < final.val.length := by
          have := (List.getElem?_eq_some_iff.mp at_a).1
          rw [finalLength]
          exact this
        obtain ⟨⟨rowLength, _, ca, at_ca, rowSpec⟩, complete⟩ := finalSpec i final.val[i] (List.getElem?_eq_getElem iIn)
        rw [at_a] at at_ca
        cases Option.some.inj at_ca
        have jIn : j < final.val[i].val.length := by
          have := (List.getElem?_eq_some_iff.mp at_b).1
          rw [rowLength]
          exact this
        obtain ⟨answersRow, at_answers, answersSpec⟩ := subsumedSpec i final.val[i] (List.getElem?_eq_getElem iIn)
        have codeAt := List.getElem?_eq_getElem jIn
        refine ⟨answersRow, _, at_answers, answersSpec j _ codeAt, ?_⟩
        intro Native D normative V vocabulary
        have right := rowSpec j _ b codeAt at_b
        rw [decide_eq_true_iff]
        rcases complete j _ codeAt with one | two
        · constructor
          · intro same
            rw [same, yes_val] at one
            omega
          · intro sub
            exact absurd sub (right.2 one D normative V vocabulary)
        · exact ⟨fun _ => right.1 two D normative V vocabulary,
            fun _ => UScalar.eq_of_val_eq (by rw [two, yes_val])⟩

end Rowl.Classification
