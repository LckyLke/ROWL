import Rowl.Hierarchy

/-!
Role chains `r1 ∘ … ∘ rn ⊑ r` for the completion forest: what a chain means
in an interpretation, the automata of the complex roles, and the two facts
that the encoding with fresh classes rests on. In every model of the role
axioms and the chains, the automaton of a role accepts only pairs that the
role relates (`accepts_initial`). Conversely, the role axioms and the chains
derive from the relations of any interpretation the least relations that
satisfy them (`Closure`); a role that no chain reaches keeps its relation
(`stage_simple`), and atoms that unfold as their automata require carry their
fillers along every derived pair (`stage_atoms`).
-/
namespace Rowl.ChainSemantics
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation)
open Rowl.Concepts (inv inv_inv relation_inv)
open Rowl.Hierarchy (Below Closed Respects inclusionList transitives below_refl respects_below)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
universe u v

section
variable {Object : Type u} {Value : Type v}

/-- The pairs related along the roles of a list, one after the other. -/
def Along (R : ObjectPropertyExpression → Object → Object → Prop) :
    List ObjectPropertyExpression → Object → Object → Prop
  | [], x, y => x = y
  | r :: w, x, y => ∃ z, R r x z ∧ Along R w z y

theorem along_append (R : ObjectPropertyExpression → Object → Object → Prop)
    (u w : List ObjectPropertyExpression) (x y : Object) :
    Along R (u ++ w) x y ↔ ∃ z, Along R u x z ∧ Along R w z y := by
  induction u generalizing x with
  | nil => simp [Along]
  | cons r u ih =>
    simp only [List.cons_append,Along,ih]
    constructor
    · rintro ⟨z,first,m,rest,last⟩; exact ⟨m,⟨z,first,rest⟩,last⟩
    · rintro ⟨m,⟨z,first,rest⟩,last⟩; exact ⟨z,first,m,rest,last⟩

theorem along_single (R : ObjectPropertyExpression → Object → Object → Prop) (r : ObjectPropertyExpression)
    (x y : Object) : Along R [r] x y ↔ R r x y := by
  simp [Along]

theorem along_mono {R R' : ObjectPropertyExpression → Object → Object → Prop}
    (sub : ∀ r x y, R r x y → R' r x y) :
    ∀ (w : List ObjectPropertyExpression) (x y : Object), Along R w x y → Along R' w x y
  | [], _, _, same => same
  | r :: w, _, y, ⟨z,first,rest⟩ => ⟨z,sub r _ z first,along_mono sub w z y rest⟩

/-- Reading the inverted roles backwards relates the reversed pairs. -/
theorem along_reverse (R : ObjectPropertyExpression → Object → Object → Prop)
    (flip : ∀ r x y, R (inv r) x y ↔ R r y x) :
    ∀ (w : List ObjectPropertyExpression) (x y : Object), Along R ((w.map inv).reverse) y x ↔ Along R w x y
  | [], x, y => by simp [Along]; exact eq_comm
  | r :: w, x, y => by
    rw [List.map_cons,List.reverse_cons,along_append]
    constructor
    · rintro ⟨z,rest,last⟩
      have last' : R (inv r) z x := (along_single R (inv r) z x).mp last
      exact ⟨z,(flip r z x).mp last',(along_reverse R flip w z y).mp rest⟩
    · rintro ⟨z,first,rest⟩
      exact ⟨z,(along_reverse R flip w z y).mpr rest,(along_single R (inv r) z x).mpr ((flip r z x).mpr first)⟩

/-- The interpretation relates every pair related along the roles of a chain
    by the chain's role. -/
def Chained (I : Interpretation Object Value) (chs : List role_chains.Chain) : Prop :=
  ∀ ch ∈ chs, ∀ x y, Along (objectRelation I) ch.roles.val x y → objectRelation I ch.sup x y

/-- With every chain the list has its mirror: the inverted roles reversed,
    included in the inverted role. -/
def Mirrored (chs : List role_chains.Chain) : Prop :=
  ∀ ch ∈ chs, ∃ ch' ∈ chs, ch'.roles.val = (ch.roles.val.map inv).reverse ∧ ch'.sup = inv ch.sup

/-- Every interpretation satisfying a chain satisfies its mirror. -/
theorem chained_mirror (I : Interpretation Object Value) (ch : role_chains.Chain)
    (holds : ∀ x y, Along (objectRelation I) ch.roles.val x y → objectRelation I ch.sup x y)
    (x y : Object) (along : Along (objectRelation I) ((ch.roles.val.map inv).reverse) x y) :
    objectRelation I (inv ch.sup) x y := by
  rw [relation_inv]
  exact holds y x ((along_reverse (objectRelation I) (fun r a b => relation_inv I r a b) _ y x).mp along)

end

/-- Each role includes the other. -/
def Equivalent (h : hierarchy.RoleHierarchy) (a b : ObjectPropertyExpression) : Prop :=
  Below h a b ∧ Below h b a

/-- A role is complex when the role of a chain is included in it. -/
def Complex (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain) (r : ObjectPropertyExpression) : Prop :=
  ∃ ch ∈ chs, Below h ch.sup r

theorem complex_up {h : hierarchy.RoleHierarchy} (closed : Closed h) {chs : List role_chains.Chain}
    {s r : ObjectPropertyExpression} (complex : Complex h chs s) (below : Below h s r) : Complex h chs r := by
  obtain ⟨ch,member,sub⟩ := complex
  exact ⟨ch,member,closed.1 _ _ _ sub below⟩

theorem equivalent_symm {h : hierarchy.RoleHierarchy} {a b : ObjectPropertyExpression} (e : Equivalent h a b) :
    Equivalent h b a := ⟨e.2,e.1⟩

/-- A segment of an automaton: from `start` to `stop` along `length` roles of
    a chain from `offset` on. -/
structure Seg where
  start : role_chains.State
  stop : role_chains.State
  offset : Nat
  length : Nat

/-- A chain of two roles equivalent to `c`, whose role is equivalent to `c`. -/
def Twin (h : hierarchy.RoleHierarchy) (ch : role_chains.Chain) (c : ObjectPropertyExpression) : Prop :=
  ∃ a b, ch.roles.val = [a,b] ∧ Equivalent h ch.sup c ∧ Equivalent h a c ∧ Equivalent h b c

/-- The segment a chain adds to the automaton of `c`: from the final state
    back to it when its first role is equivalent to `c`, from the initial
    state back to it when its last role is, and from the initial to the final
    state otherwise; none for a chain whose role is not equivalent to `c`, for
    a twin and for fewer than two roles. -/
noncomputable def segOf (h : hierarchy.RoleHierarchy) (ch : role_chains.Chain) (c : ObjectPropertyExpression) :
    Option Seg :=
  match ch.roles.val with
  | [] => none
  | [_] => none
  | a :: b :: rest =>
    if Equivalent h ch.sup c then
      if Equivalent h a c then
        if rest = [] ∧ Equivalent h b c then none
        else some ⟨.Final,.Final,1,rest.length+1⟩
      else if Equivalent h ((b :: rest).getLast (by simp)) c then
        some ⟨.Initial,.Initial,0,rest.length+1⟩
      else some ⟨.Initial,.Final,0,rest.length+2⟩
    else none

/-- The three shapes of a segment. -/
theorem segOf_shape {h : hierarchy.RoleHierarchy} {ch : role_chains.Chain} {c : ObjectPropertyExpression} {g : Seg}
    (found : segOf h ch c = some g) :
    Equivalent h ch.sup c ∧ 2 ≤ ch.roles.val.length ∧ 1 ≤ g.length ∧
      ((g.start = .Final ∧ g.stop = .Final ∧ g.offset = 1 ∧ g.length + 1 = ch.roles.val.length ∧
          ∃ a rest, ch.roles.val = a :: rest ∧ Equivalent h a c) ∨
        (g.start = .Initial ∧ g.stop = .Initial ∧ g.offset = 0 ∧ g.length + 1 = ch.roles.val.length ∧
          ∃ rest a, ch.roles.val = rest ++ [a] ∧ Equivalent h a c) ∨
        (g.start = .Initial ∧ g.stop = .Final ∧ g.offset = 0 ∧ g.length = ch.roles.val.length)) := by
  unfold segOf at found
  split at found
  · cases found
  · cases found
  · rename_i a b rest roles
    rw [roles]
    by_cases sup : Equivalent h ch.sup c
    · simp only [sup,↓reduceIte] at found
      by_cases first : Equivalent h a c
      · simp only [first,↓reduceIte] at found
        by_cases twin : rest = [] ∧ Equivalent h b c
        · simp [twin] at found
        · simp only [twin,↓reduceIte,Option.some.injEq] at found
          subst found
          refine ⟨sup,by simp,by simp,.inl ⟨rfl,rfl,rfl,by simp,a,b :: rest,rfl,first⟩⟩
      · simp only [first,↓reduceIte] at found
        by_cases last : Equivalent h ((b :: rest).getLast (by simp)) c
        · simp only [last,↓reduceIte,Option.some.injEq] at found
          subst found
          refine ⟨sup,by simp,by simp,.inr (.inl ⟨rfl,rfl,rfl,by simp,(a :: b :: rest).dropLast,
            (b :: rest).getLast (by simp),?_,last⟩)⟩
          have := List.dropLast_append_getLast (l := a :: b :: rest) (by simp)
          rw [List.getLast_cons (by simp)] at this
          exact this.symm
        · simp only [last,↓reduceIte,Option.some.injEq] at found
          subst found
          exact ⟨sup,by simp,by simp,.inr (.inr ⟨rfl,rfl,rfl,by simp⟩)⟩
    · simp [sup] at found

/-- A chain of at least two roles whose role is equivalent to `c` is a twin
    or adds a segment. -/
theorem segOf_some {h : hierarchy.RoleHierarchy} {ch : role_chains.Chain} {c : ObjectPropertyExpression}
    (long : 2 ≤ ch.roles.val.length) (sup : Equivalent h ch.sup c) (single : ¬ Twin h ch c) :
    ∃ g, segOf h ch c = some g := by
  unfold segOf
  split
  · rename_i roles; rw [roles] at long; simp at long
  · rename_i roles; rw [roles] at long; simp at long
  · rename_i a b rest roles
    simp only [sup,↓reduceIte]
    by_cases first : Equivalent h a c
    · simp only [first,↓reduceIte]
      by_cases twin : rest = [] ∧ Equivalent h b c
      · obtain ⟨rfl,second⟩ := twin
        exact absurd ⟨a,b,roles,sup,first,second⟩ single
      · simp [twin]
    · simp only [first,↓reduceIte]
      split <;> simp

/-- The state before the role at position `j` of a segment of chain `k`. -/
def before (g : Seg) (k j : Usize) : role_chains.State := if j.val = 0 then g.start else .Inside k j
/-- The state after the role at position `j' - 1`. -/
def after (g : Seg) (k j' : Usize) : role_chains.State := if j'.val = g.length then g.stop else .Inside k j'

/-- The transitions of the automaton of the complex role `c`. -/
inductive Trans (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain) (c : ObjectPropertyExpression) :
    role_chains.State → role_chains.Label → role_chains.State → Prop
  | direct : Trans h chs c .Initial .Direct .Final
  | sub {s : ObjectPropertyExpression} : (s,c) ∈ inclusionList h → Complex h chs s → ¬ Below h c s →
      Trans h chs c .Initial (.Role s) .Final
  | loop : (∃ t ∈ transitives h, Equivalent h t c) → Trans h chs c .Final .Empty .Initial
  | twin {k : Nat} {ch : role_chains.Chain} : chs[k]? = some ch → Twin h ch c → Trans h chs c .Final .Empty .Initial
  | segment {k j j' : Usize} {ch : role_chains.Chain} {g : Seg} {l : ObjectPropertyExpression} :
      chs[k.val]? = some ch → segOf h ch c = some g → j.val < g.length → j'.val = j.val + 1 →
      ch.roles.val[g.offset + j.val]? = some l → Trans h chs c (before g k j) (.Role l) (after g k j')

section
variable {Object : Type u} {Value : Type v}

/-- What a transition reads in an interpretation. -/
def LabelRel (I : Interpretation Object Value) (c : ObjectPropertyExpression) :
    role_chains.Label → Object → Object → Prop
  | .Direct, x, y => objectRelation I c x y
  | .Role s, x, y => objectRelation I s x y
  | .Empty, x, y => x = y

/-- The automaton of `c` reads a path from the first element to the second,
    from the state to the final state. -/
inductive Accepts (I : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    (c : ObjectPropertyExpression) : role_chains.State → Object → Object → Prop
  | done (x : Object) : Accepts I h chs c .Final x x
  | step {q : role_chains.State} {l : role_chains.Label} {q' : role_chains.State} {x z y : Object} :
      Trans h chs c q l q' → LabelRel I c l x z → Accepts I h chs c q' z y → Accepts I h chs c q x y

/-- The roles that lead from the initial state to a state. -/
noncomputable def prefixOf (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain) (c : ObjectPropertyExpression) :
    role_chains.State → List ObjectPropertyExpression
  | .Initial => []
  | .Final => [c]
  | .Inside k j =>
    match chs[k.val]? with
    | none => []
    | some ch =>
      match segOf h ch c with
      | none => []
      | some g => (if g.start = .Final then [c] else []) ++ (ch.roles.val.drop g.offset).take j.val

/-- What a path from a state to the final state establishes: whatever leads
    along the state's prefix to its start is related by `c` to its end. -/
def Goal (I : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    (c : ObjectPropertyExpression) (q : role_chains.State) (x y : Object) : Prop :=
  ∀ u, Along (objectRelation I) (prefixOf h chs c q) u x → objectRelation I c u y

private theorem prefix_before {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain} {c : ObjectPropertyExpression}
    {k j : Usize} {ch : role_chains.Chain} {g : Seg} (get : chs[k.val]? = some ch) (found : segOf h ch c = some g) :
    prefixOf h chs c (before g k j) =
      (if g.start = .Final then [c] else []) ++ (ch.roles.val.drop g.offset).take j.val := by
  obtain ⟨_,_,_,shape⟩ := segOf_shape found
  unfold before
  by_cases zero : j.val = 0
  · simp only [zero,↓reduceIte,List.take_zero,List.append_nil]
    rcases shape with ⟨start,_⟩ | ⟨start,_⟩ | ⟨start,_⟩ <;> rw [start] <;> simp [prefixOf]
  · simp only [zero,↓reduceIte,prefixOf,get,found]

private theorem prefix_after {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain} {c : ObjectPropertyExpression}
    {k j' : Usize} {ch : role_chains.Chain} {g : Seg} (get : chs[k.val]? = some ch) (found : segOf h ch c = some g)
    (inside : j'.val ≠ g.length) :
    prefixOf h chs c (after g k j') =
      (if g.start = .Final then [c] else []) ++ (ch.roles.val.drop g.offset).take j'.val := by
  unfold after
  simp only [inside,↓reduceIte,prefixOf,get,found]

theorem goal_initial {I : Interpretation Object Value} {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain}
    {c : ObjectPropertyExpression} {x y : Object} :
    Goal I h chs c .Initial x y ↔ objectRelation I c x y := by
  constructor
  · intro goal; exact goal x rfl
  · intro rel u along
    have same : u = x := along
    rw [same]; exact rel

theorem goal_final {I : Interpretation Object Value} {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain}
    {c : ObjectPropertyExpression} {x y : Object} :
    Goal I h chs c .Final x y ↔ ∀ u, objectRelation I c u x → objectRelation I c u y := by
  constructor
  · intro goal u rel; exact goal u ⟨x,rel,rfl⟩
  · intro hyp u along
    obtain ⟨m,rel,same⟩ := along
    rw [same] at rel
    exact hyp u rel

/-- In every model of the role axioms and the chains, every path that the
    automaton of `c` reads from a state establishes the state's goal. -/
theorem accepts_goal {I : Interpretation Object Value} {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain}
    (respects : Respects I h) (chained : Chained I chs) {c : ObjectPropertyExpression} :
    ∀ {q : role_chains.State} {x y : Object}, Accepts I h chs c q x y → Goal I h chs c q x y := by
  intro q x y accepts
  induction accepts with
  | done x => exact goal_final.mpr (fun _ rel => rel)
  | @step q l q' x z y trans label _ ih =>
    cases trans with
    | direct =>
      rw [goal_initial]
      exact goal_final.mp ih x label
    | sub listed _ _ =>
      rw [goal_initial]
      exact goal_final.mp ih x (respects.1 _ _ listed _ _ label)
    | loop transitive =>
      obtain ⟨t,member,equiv⟩ := transitive
      have same : x = z := label
      rw [← same] at ih
      have second : objectRelation I c x y := goal_initial.mp ih
      rw [goal_final]
      intro u first
      exact respects_below respects equiv.1
        (respects.2 t member u x y (respects_below respects equiv.2 first) (respects_below respects equiv.2 second))
    | twin get twin =>
      obtain ⟨a,b,roles,sup,first,second⟩ := twin
      have same : x = z := label
      rw [← same] at ih
      have last : objectRelation I c x y := goal_initial.mp ih
      have member : _ ∈ chs := List.mem_of_getElem? get
      rw [goal_final]
      intro u rel
      refine respects_below respects sup.1 (chained _ member u y ?_)
      rw [roles]
      exact ⟨x,respects_below respects first.2 rel,y,respects_below respects second.2 last,rfl⟩
    | @segment k j j' ch g l get found below next role =>
      obtain ⟨sup,long,positive,shape⟩ := segOf_shape found
      have member : ch ∈ chs := List.mem_of_getElem? get
      have within : g.offset + j.val < ch.roles.val.length := by
        by_contra outside
        rw [List.getElem?_eq_none (by omega)] at role
        cases role
      have grow : (ch.roles.val.drop g.offset).take j'.val =
          (ch.roles.val.drop g.offset).take j.val ++ [l] := by
        rw [next,List.take_add_one,List.getElem?_drop,role]
        rfl
      intro u along
      rw [prefix_before get found] at along
      have extended : Along (objectRelation I)
          ((if g.start = .Final then [c] else []) ++ (ch.roles.val.drop g.offset).take j'.val) u z := by
        rw [grow,← List.append_assoc,along_append]
        exact ⟨x,along,(along_single _ _ _ _).mpr label⟩
      by_cases inside : j'.val = g.length
      · -- The segment ends here.
        have goal : Goal I h chs c (after g k j') z y := ih
        unfold after at goal
        simp only [inside,↓reduceIte] at goal
        rw [inside] at extended
        rcases shape with ⟨start,stop,offset,length,a,rest,roles,first⟩ |
          ⟨start,stop,offset,length,rest,a,roles,last⟩ | ⟨start,stop,offset,length⟩
        · have segment : (ch.roles.val.drop g.offset).take g.length = rest := by
            rw [roles] at length
            simp only [List.length_cons] at length
            rw [roles,offset,List.drop_one,List.tail_cons,show g.length = rest.length by omega,List.take_length]
          rw [segment] at extended
          simp only [start,↓reduceIte,List.singleton_append] at extended
          rw [stop,goal_final] at goal
          obtain ⟨m,cm,along⟩ := extended
          refine goal u (respects_below respects sup.1 (chained ch member u z ?_))
          rw [roles]
          exact ⟨m,respects_below respects first.2 cm,along⟩
        · have segment : (ch.roles.val.drop g.offset).take g.length = rest := by
            rw [roles] at length
            simp only [List.length_append,List.length_singleton] at length
            rw [roles,offset,List.drop_zero,show g.length = rest.length by omega,List.take_left' rfl]
          rw [segment] at extended
          simp only [start,reduceCtorEq,↓reduceIte,List.nil_append] at extended
          rw [stop,goal_initial] at goal
          refine respects_below respects sup.1 (chained ch member u y ?_)
          rw [roles,along_append]
          exact ⟨z,extended,(along_single _ _ _ _).mpr (respects_below respects last.2 goal)⟩
        · have segment : (ch.roles.val.drop g.offset).take g.length = ch.roles.val := by
            rw [offset,List.drop_zero,length,List.take_length]
          rw [segment] at extended
          simp only [start,reduceCtorEq,↓reduceIte,List.nil_append] at extended
          rw [stop,goal_final] at goal
          exact goal u (respects_below respects sup.1 (chained ch member u z extended))
      · have goal : Goal I h chs c (after g k j') z y := ih
        rw [Goal,prefix_after get found inside] at goal
        exact goal u extended

/-- In every model of the role axioms and the chains, the automaton of `c`
    accepts only pairs related by `c`. -/
theorem accepts_initial {I : Interpretation Object Value} {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain}
    (respects : Respects I h) (chained : Chained I chs) {c : ObjectPropertyExpression} {x y : Object}
    (accepts : Accepts I h chs c .Initial x y) : objectRelation I c x y :=
  accepts_goal respects chained accepts x rfl

/-- The automaton of `c` accepts every pair related by `c`. -/
theorem accepts_of_rel (I : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    {c : ObjectPropertyExpression} {x y : Object} (rel : objectRelation I c x y) :
    Accepts I h chs c .Initial x y :=
  .step .direct rel (.done y)

/-! ### The relations that the role axioms derive -/

/-- The pairs that the role axioms and the chains derive in `n` rounds from
    the relations of `J`. -/
def Stage (J : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain) :
    Nat → ObjectPropertyExpression → Object → Object → Prop
  | 0, r, x, y => objectRelation J r x y
  | n+1, r, x, y => Stage J h chs n r x y ∨ (∃ s, (s,r) ∈ inclusionList h ∧ Stage J h chs n s x y) ∨
      (r ∈ transitives h ∧ ∃ z, Stage J h chs n r x z ∧ Stage J h chs n r z y) ∨
      (∃ ch ∈ chs, ch.sup = r ∧ Along (Stage J h chs n) ch.roles.val x y)

/-- The pairs that the role axioms and the chains derive. -/
def Closure (J : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    (r : ObjectPropertyExpression) (x y : Object) : Prop :=
  ∃ n, Stage J h chs n r x y

theorem stage_le {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain}
    {n m : Nat} (le : n ≤ m) {r : ObjectPropertyExpression} {x y : Object} (stage : Stage J h chs n r x y) :
    Stage J h chs m r x y := by
  induction m with
  | zero => rw [Nat.le_zero.mp le] at stage; exact stage
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le le with lt | same
    · exact .inl (ih (by omega))
    · rw [← same]; exact stage

theorem closure_base {J : Interpretation Object Value} (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    {r : ObjectPropertyExpression} {x y : Object} (rel : objectRelation J r x y) : Closure J h chs r x y :=
  ⟨0,rel⟩

theorem closure_incl {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain}
    {s r : ObjectPropertyExpression} (listed : (s,r) ∈ inclusionList h) {x y : Object}
    (rel : Closure J h chs s x y) : Closure J h chs r x y := by
  obtain ⟨n,stage⟩ := rel
  exact ⟨n+1,.inr (.inl ⟨s,listed,stage⟩)⟩

theorem closure_below {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain}
    {s r : ObjectPropertyExpression} (below : Below h s r) {x y : Object}
    (rel : Closure J h chs s x y) : Closure J h chs r x y := by
  rcases below with same | listed
  · rw [← same]; exact rel
  · exact closure_incl listed rel

theorem closure_trans {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain}
    {r : ObjectPropertyExpression} (transitive : r ∈ transitives h) {x y z : Object}
    (first : Closure J h chs r x y) (second : Closure J h chs r y z) : Closure J h chs r x z := by
  obtain ⟨n,s1⟩ := first
  obtain ⟨m,s2⟩ := second
  exact ⟨max n m+1,.inr (.inr (.inl ⟨transitive,y,stage_le (by omega) s1,stage_le (by omega) s2⟩))⟩

theorem along_closure {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain} :
    ∀ (w : List ObjectPropertyExpression) (x y : Object), Along (Closure J h chs) w x y →
      ∃ n, Along (Stage J h chs n) w x y
  | [], _, _, same => ⟨0,same⟩
  | r :: w, _, y, ⟨z,⟨n,first⟩,rest⟩ => by
    obtain ⟨m,later⟩ := along_closure w z y rest
    exact ⟨max n m,z,stage_le (by omega) first,along_mono (fun _ _ _ s => stage_le (by omega) s) w z y later⟩

theorem closure_chain {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain}
    {ch : role_chains.Chain} (member : ch ∈ chs) {x y : Object} (along : Along (Closure J h chs) ch.roles.val x y) :
    Closure J h chs ch.sup x y := by
  obtain ⟨n,stages⟩ := along_closure _ x y along
  exact ⟨n+1,.inr (.inr (.inr ⟨ch,member,rfl,stages⟩))⟩

/-- In a closed hierarchy with mirrored chains, the derived relation of an
    inverse role relates exactly the reversed pairs. -/
theorem stage_mirror {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} (closed : Closed h)
    {chs : List role_chains.Chain} (mirrored : Mirrored chs) :
    ∀ n (r : ObjectPropertyExpression) (x y : Object), Stage J h chs n r x y ↔ Stage J h chs n (inv r) y x := by
  intro n
  induction n with
  | zero => intro r x y; simp only [Stage,relation_inv]
  | succ n ih =>
    have forward : ∀ (r : ObjectPropertyExpression) (x y : Object),
        Stage J h chs (n+1) r x y → Stage J h chs (n+1) (inv r) y x := by
      intro r x y stage
      rcases stage with kept | ⟨s,listed,stage⟩ | ⟨transitive,z,first,second⟩ | ⟨ch,member,sup,along⟩
      · exact .inl ((ih r x y).mp kept)
      · rcases closed.2.1 s r (.inr listed) with same | listed'
        · have : s = r := by rw [← inv_inv s,same,inv_inv]
          subst this
          exact .inl ((ih s x y).mp stage)
        · exact .inr (.inl ⟨inv s,listed',(ih s x y).mp stage⟩)
      · exact .inr (.inr (.inl ⟨closed.2.2 r transitive,z,(ih r z y).mp second,(ih r x z).mp first⟩))
      · obtain ⟨ch',member',roles,sup'⟩ := mirrored ch member
        refine .inr (.inr (.inr ⟨ch',member',by rw [sup',sup],?_⟩))
        rw [roles]
        exact (along_reverse (Stage J h chs n) (fun r a b => (ih r b a).symm) _ x y).mpr along
    intro r x y
    constructor
    · exact forward r x y
    · intro stage
      have := forward (inv r) y x stage
      rwa [inv_inv] at this

theorem closure_mirror {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} (closed : Closed h)
    {chs : List role_chains.Chain} (mirrored : Mirrored chs) (r : ObjectPropertyExpression) (x y : Object) :
    Closure J h chs r x y ↔ Closure J h chs (inv r) y x := by
  constructor
  · rintro ⟨n,stage⟩; exact ⟨n,(stage_mirror closed mirrored n r x y).mp stage⟩
  · rintro ⟨n,stage⟩; exact ⟨n,(stage_mirror closed mirrored n r x y).mpr stage⟩

/-- A role that is not complex relates in `J`, which respects the role
    hierarchy, every pair that the role axioms derive for it. -/
theorem stage_simple {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} (closed : Closed h)
    {chs : List role_chains.Chain} (respects : Respects J h) :
    ∀ n (r : ObjectPropertyExpression) (x y : Object), Stage J h chs n r x y → ¬ Complex h chs r →
      objectRelation J r x y := by
  intro n
  induction n with
  | zero => intro r x y stage _; exact stage
  | succ n ih =>
    intro r x y stage simple
    rcases stage with kept | ⟨s,listed,stage⟩ | ⟨transitive,z,first,second⟩ | ⟨ch,member,sup,_⟩
    · exact ih r x y kept simple
    · have simple' : ¬ Complex h chs s := fun complex => simple (complex_up closed complex (.inr listed))
      exact respects.1 s r listed x y (ih s x y stage simple')
    · exact respects.2 r transitive x z y (ih r x z first simple) (ih r z y second simple)
    · exact absurd ⟨ch,member,by rw [sup]; exact below_refl h r⟩ simple

theorem closure_simple {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} (closed : Closed h)
    {chs : List role_chains.Chain} (respects : Respects J h) {r : ObjectPropertyExpression} (simple : ¬ Complex h chs r)
    {x y : Object} : Closure J h chs r x y ↔ objectRelation J r x y := by
  constructor
  · rintro ⟨n,stage⟩; exact stage_simple closed respects n r x y stage simple
  · exact closure_base h chs

/-! ### Atoms along derived pairs -/

/-- What an atom requires of an element for a transition labelled `l` to the
    atom at `j`. -/
def Requires (J : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    (T : List role_chains.Atom) (cls : Usize → Object → Prop) (c : ObjectPropertyExpression) (l : role_chains.Label)
    (j : Usize) (y : Object) : Prop :=
  match l with
  | .Direct => ∀ z, objectRelation J c y z → cls j z
  | .Role s => (Complex h chs s → ∃ j2 : Usize, T[j2.val]? = some ⟨s,.Initial,.Atom j⟩ ∧ cls j2 y) ∧
      (¬ Complex h chs s → ∀ z, objectRelation J s y z → cls j z)
  | .Empty => cls j y

/-- Every element of an atom of the table satisfies the filler of a final
    state and, for every transition, what the atom requires. -/
def Unfolds (J : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    (T : List role_chains.Atom) (cls : Usize → Object → Prop) (fill : role_chains.Filler → Object → Prop) : Prop :=
  ∀ (k : Usize) (a : role_chains.Atom), T[k.val]? = some a → ∀ y, cls k y →
    (a.state = .Final → fill a.filler y) ∧
    ∀ l q', Trans h chs a.role a.state l q' →
      ∃ j : Usize, T[j.val]? = some ⟨a.role,q',a.filler⟩ ∧ Requires J h chs T cls a.role l j y

/-- Every natural number up to `Usize.max` is the value of a `Usize`. -/
theorem usize_of {n : Nat} (bound : n ≤ Usize.max) : ∃ u : Usize, u.val = n := by
  have lt : n < 2 ^ UScalarTy.Usize.numBits := by
    have := Usize.max_def
    have pos : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
    simp only [Usize.numBits] at this
    omega
  exact ⟨Usize.ofNatCore n lt,UScalar.ofNatCore_val_eq lt⟩

/-- The state of the segment of chain `k` after `j` of its roles. -/
def stateAt (g : Seg) (k j : Usize) : role_chains.State := if j.val = g.length then g.stop else before g k j

/-- Walking along the segment of a chain: when every transition along a role
    leads from an atom with an element to an atom of the target with the
    next element, a path along the remaining roles of the segment leads to
    an atom of the end of the segment. -/
theorem walk {Object : Type u} {R : ObjectPropertyExpression → Object → Object → Prop}
    {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain} {T : List role_chains.Atom} {cls : Usize → Object → Prop}
    {c : ObjectPropertyExpression} {F : role_chains.Filler}
    (step : ∀ (k : Usize) (q q' : role_chains.State) (l : ObjectPropertyExpression) (x z : Object),
      T[k.val]? = some ⟨c,q,F⟩ → cls k x → Trans h chs c q (.Role l) q' → R l x z →
        ∃ j : Usize, T[j.val]? = some ⟨c,q',F⟩ ∧ cls j z)
    {kc : Usize} {ch : role_chains.Chain} {g : Seg} (get : chs[kc.val]? = some ch) (found : segOf h ch c = some g) :
    ∀ (m : Nat) (j : Usize) (x y : Object), g.length - j.val = m → j.val ≤ g.length →
      Along R (((ch.roles.val.drop g.offset).take g.length).drop j.val) x y →
      (∃ k : Usize, T[k.val]? = some ⟨c,stateAt g kc j,F⟩ ∧ cls k x) →
      ∃ j' : Usize, T[j'.val]? = some ⟨c,g.stop,F⟩ ∧ cls j' y := by
  obtain ⟨_,_,positive,shape⟩ := segOf_shape found
  have fits : g.offset + g.length ≤ ch.roles.val.length := by
    rcases shape with ⟨_,_,_,length,_⟩ | ⟨_,_,_,length,_⟩ | ⟨_,_,_,length⟩ <;> omega
  have small : ch.roles.val.length ≤ Usize.max := ch.roles.property
  intro m
  induction m with
  | zero =>
    intro j x y left le path start
    have done : j.val = g.length := by omega
    have empty : ((ch.roles.val.drop g.offset).take g.length).drop j.val = [] := by
      rw [List.drop_eq_nil_iff,List.length_take,List.length_drop]; omega
    rw [empty] at path
    have same : x = y := path
    subst same
    obtain ⟨k,at_k,member⟩ := start
    refine ⟨k,?_,member⟩
    rw [at_k]
    unfold stateAt
    simp [done]
  | succ m ih =>
    intro j x y left le path start
    have lt : j.val < g.length := by omega
    have within : g.offset + j.val < ch.roles.val.length := by omega
    have split : ((ch.roles.val.drop g.offset).take g.length).drop j.val =
        ch.roles.val[g.offset + j.val] :: ((ch.roles.val.drop g.offset).take g.length).drop (j.val+1) := by
      rw [List.drop_eq_getElem_cons (by rw [List.length_take,List.length_drop]; omega)]
      simp [List.getElem_take,List.getElem_drop]
    rw [split] at path
    obtain ⟨z,first,rest⟩ := path
    obtain ⟨j',advance,j'Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
    have next : j'.val = j.val + 1 := by simpa using j'Val
    have trans : Trans h chs c (before g kc j) (.Role ch.roles.val[g.offset + j.val]) (after g kc j') :=
      .segment get found lt next (List.getElem?_eq_getElem within)
    obtain ⟨k,at_k,member⟩ := start
    have here : stateAt g kc j = before g kc j := by unfold stateAt; simp [show j.val ≠ g.length by omega]
    rw [here] at at_k
    obtain ⟨j1,at_j1,member1⟩ := step k _ _ _ x z at_k member trans first
    have there : after g kc j' = stateAt g kc j' := by
      unfold after stateAt before; simp [next]
    rw [there] at at_j1
    exact ih j' z y (by omega) (by omega) (by rw [next]; exact rest) ⟨j1,at_j1,member1⟩

/-- Atoms that unfold as their automata require carry their elements along
    every pair that the role axioms derive: from the atom of the initial
    state of a role equivalent to the derived one to the atom of its final
    state with the same filler. -/
theorem stage_atoms {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} (closed : Closed h)
    {chs : List role_chains.Chain} (long : ∀ ch ∈ chs, 2 ≤ ch.roles.val.length) (few : chs.length ≤ Usize.max)
    (respects : Respects J h) {T : List role_chains.Atom} {cls : Usize → Object → Prop}
    {fill : role_chains.Filler → Object → Prop} (unfolds : Unfolds J h chs T cls fill)
    (fillAtom : ∀ (j : Usize) y, fill (.Atom j) y → cls j y) :
    ∀ n (r : ObjectPropertyExpression) (x y : Object), Stage J h chs n r x y →
      ∀ (k : Usize) (a : role_chains.Atom), T[k.val]? = some a → Equivalent h a.role r → a.state = .Initial → cls k x →
        ∃ j : Usize, T[j.val]? = some ⟨a.role,.Final,a.filler⟩ ∧ cls j y := by
  -- The direct transition from the initial state.
  have direct : ∀ (k : Usize) (c : ObjectPropertyExpression) (F : role_chains.Filler) (x y : Object),
      T[k.val]? = some ⟨c,.Initial,F⟩ → cls k x → objectRelation J c x y →
        ∃ j : Usize, T[j.val]? = some ⟨c,.Final,F⟩ ∧ cls j y := by
    intro k c F x y get member rel
    obtain ⟨j,at_j,requires⟩ := (unfolds k _ get x member).2 .Direct .Final .direct
    exact ⟨j,at_j,requires y rel⟩
  -- An empty transition.
  have empty : ∀ (k : Usize) (c : ObjectPropertyExpression) (q q' : role_chains.State) (F : role_chains.Filler) (x : Object),
      T[k.val]? = some ⟨c,q,F⟩ → cls k x → Trans h chs c q .Empty q' →
        ∃ j : Usize, T[j.val]? = some ⟨c,q',F⟩ ∧ cls j x := by
    intro k c q q' F x get member trans
    obtain ⟨j,at_j,requires⟩ := (unfolds k _ get x member).2 .Empty q' trans
    exact ⟨j,at_j,requires⟩
  intro n
  induction n with
  | zero =>
    intro r x y rel k a get equiv initial member
    obtain ⟨c,q,F⟩ := a
    simp only at equiv initial
    subst initial
    exact direct k c F x y get member (respects_below respects equiv.2 rel)
  | succ n ih =>
    -- A transition along a role, through the derived pairs of the previous round.
    have along : ∀ (k : Usize) (c : ObjectPropertyExpression) (q q' : role_chains.State) (F : role_chains.Filler)
        (l : ObjectPropertyExpression) (x z : Object), T[k.val]? = some ⟨c,q,F⟩ → cls k x →
        Trans h chs c q (.Role l) q' → Stage J h chs n l x z →
          ∃ j : Usize, T[j.val]? = some ⟨c,q',F⟩ ∧ cls j z := by
      intro k c q q' F l x z get member trans stage
      obtain ⟨j,at_j,nested,plain⟩ := (unfolds k _ get x member).2 (.Role l) q' trans
      refine ⟨j,at_j,?_⟩
      by_cases complex : Complex h chs l
      · obtain ⟨j2,at_j2,member2⟩ := nested complex
        obtain ⟨j3,at_j3,member3⟩ := ih l x z stage j2 _ at_j2 ⟨below_refl h l,below_refl h l⟩ rfl member2
        exact fillAtom j z ((unfolds j3 _ at_j3 z member3).1 rfl)
      · exact plain complex z (stage_simple closed respects n l x z stage complex)
    intro r x y stage k a get equiv initial member
    obtain ⟨c,q,F⟩ := a
    simp only at equiv initial
    subst initial
    rcases stage with kept | ⟨s,listed,stage⟩ | ⟨transitive,z,first,second⟩ | ⟨ch,member',sup,path⟩
    · exact ih r x y kept k _ get equiv rfl member
    · have sc : Below h s c := closed.1 _ _ _ (.inr listed) equiv.2
      by_cases complex : Complex h chs s
      · by_cases back : Below h c s
        · exact ih s x y stage k _ get ⟨back,sc⟩ rfl member
        · have listed' : (s,c) ∈ inclusionList h := by
            rcases sc with same | listed'
            · exact absurd (by rw [same]; exact below_refl h c) back
            · exact listed'
          exact along k c .Initial .Final F s x y get member (.sub listed' complex back) stage
      · exact direct k c F x y get member (respects_below respects sc (stage_simple closed respects n s x y stage complex))
    · obtain ⟨j1,at_j1,member1⟩ := ih r x z first k _ get equiv rfl member
      obtain ⟨j2,at_j2,member2⟩ := empty j1 c .Final .Initial F z at_j1 member1
        (.loop ⟨r,transitive,equivalent_symm equiv⟩)
      exact ih r z y second j2 _ at_j2 equiv rfl member2
    · subst sup
      obtain ⟨index,index_lt,index_get⟩ := List.getElem_of_mem member'
      obtain ⟨kc,kcVal⟩ := usize_of (n := index) (by omega)
      have get' : chs[kc.val]? = some ch := by rw [kcVal,List.getElem?_eq_getElem index_lt,index_get]
      have chainEquiv : Equivalent h ch.sup c := equivalent_symm equiv
      by_cases twin : Twin h ch c
      · obtain ⟨a,b,roles,_,first,second⟩ := twin
        rw [roles] at path
        obtain ⟨z,sa,m,sb,same⟩ := path
        subst same
        obtain ⟨j1,at_j1,member1⟩ := ih a x z sa k _ get (equivalent_symm first) rfl member
        obtain ⟨j2,at_j2,member2⟩ := empty j1 c .Final .Initial F z at_j1 member1
          (.twin get' ⟨a,b,roles,chainEquiv,first,second⟩)
        exact ih b z m sb j2 _ at_j2 (equivalent_symm second) rfl member2
      · obtain ⟨g,found⟩ := segOf_some (long ch member') chainEquiv twin
        have walking := walk (R := Stage J h chs n) (fun k q q' l x z get member trans stage =>
          along k c q q' F l x z get member trans stage) get' found
        obtain ⟨_,_,positive,shape⟩ := segOf_shape found
        rcases shape with ⟨start,stop,offset,length,a,rest,roles,first⟩ |
          ⟨start,stop,offset,length,rest,a,roles,last⟩ | ⟨start,stop,offset,length⟩
        · -- The first role is equivalent: on to the final state, then around it.
          rw [roles] at path
          obtain ⟨z,sa,rest_path⟩ := path
          obtain ⟨j1,at_j1,member1⟩ := ih a x z sa k _ get (equivalent_symm first) rfl member
          have word : ((ch.roles.val.drop g.offset).take g.length).drop 0 = rest := by
            rw [roles,offset,List.drop_zero,List.drop_one,List.tail_cons]
            rw [roles] at length
            simp only [List.length_cons] at length
            rw [show g.length = rest.length by omega,List.take_length]
          obtain ⟨j0,j0Val⟩ := usize_of (n := 0) (by simp)
          have := walking (g.length - 0) j0 z y (by rw [j0Val]) (by rw [j0Val]; omega)
            (by rw [j0Val,word]; exact rest_path)
            ⟨j1,by rw [at_j1]; unfold stateAt before; simp [j0Val,start]; omega,member1⟩
          rwa [stop] at this
        · -- The last role is equivalent: around the initial state, then on.
          rw [roles,along_append] at path
          obtain ⟨z,rest_path,last_path⟩ := path
          obtain ⟨m,sa,same⟩ := last_path
          subst same
          have word : ((ch.roles.val.drop g.offset).take g.length).drop 0 = rest := by
            rw [roles,offset,List.drop_zero,List.drop_zero]
            rw [roles] at length
            simp only [List.length_append,List.length_singleton] at length
            rw [show g.length = rest.length by omega,List.take_left' rfl]
          obtain ⟨j0,j0Val⟩ := usize_of (n := 0) (by simp)
          obtain ⟨j1,at_j1,member1⟩ := walking (g.length - 0) j0 x z (by rw [j0Val]) (by rw [j0Val]; omega)
            (by rw [j0Val,word]; exact rest_path)
            ⟨k,by rw [get]; unfold stateAt before; simp [j0Val,start]; omega,member⟩
          rw [stop] at at_j1
          exact ih a z m sa j1 _ at_j1 (equivalent_symm last) rfl member1
        · have word : ((ch.roles.val.drop g.offset).take g.length).drop 0 = ch.roles.val := by
            rw [offset,List.drop_zero,List.drop_zero,length,List.take_length]
          obtain ⟨j0,j0Val⟩ := usize_of (n := 0) (by simp)
          have := walking (g.length - 0) j0 x y (by rw [j0Val]) (by rw [j0Val]; omega)
            (by rw [j0Val,word]; exact path)
            ⟨k,by rw [get]; unfold stateAt before; simp [j0Val,start]; omega,member⟩
          rwa [stop] at this

end
end Rowl.ChainSemantics
