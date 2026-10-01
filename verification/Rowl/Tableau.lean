import Rowl.Nnf

/-!
A decision procedure for ALC concept satisfiability without a TBox, proved
total, sound and complete against the concept meaning of `Rowl.Nnf`. Soundness
builds an explicit tree model over paths; completeness follows any model, in any
universe. Composed with the NNF translation, a rejection proves an OWL class
expression empty in every OWL interpretation.
-/
namespace Rowl.Tableau
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation classDenote)
open Rowl.Nnf (conceptDenote)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v

/-- The concepts of a list, in order. -/
def toList : tableau.Concepts → List nnf.NnfConcept
  | .Empty => []
  | .Entry c next => c :: toList next
/-- The list holding the given concepts, in order. -/
def fromList : List nnf.NnfConcept → tableau.Concepts
  | [] => .Empty
  | c :: rest => .Entry c (fromList rest)
theorem toList_fromList (cs : List nnf.NnfConcept) : toList (fromList cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp [toList,fromList,ih]

/-- The size of a concept; every step of the procedure shrinks the total size. -/
def weight : nnf.NnfConcept → Nat
  | .Top => 1
  | .Bottom => 1
  | .Atom _ => 1
  | .NotAtom _ => 1
  | .And a b => weight a + weight b + 1
  | .Or a b => weight a + weight b + 1
  | .Exists _ c => weight c + 1
  | .Forall _ c => weight c + 1
def total (cs : List nnf.NnfConcept) : Nat := (cs.map weight).sum

/-- Named-class literals and restrictions: what remains once conjunctions and
    disjunctions are expanded. -/
def Literal : nnf.NnfConcept → Prop
  | .Atom _ => True
  | .NotAtom _ => True
  | .Exists _ _ => True
  | .Forall _ _ => True
  | _ => False
/-- A named class occurs both negated and positively. -/
def Clash (cs : List nnf.NnfConcept) : Prop := ∃ k, .NotAtom k ∈ cs ∧ .Atom k ∈ cs
/-- The fillers of every universal restriction on the role, in list order. -/
noncomputable def fillers (role : ObjectProperty) : List nnf.NnfConcept → List nnf.NnfConcept
  | [] => []
  | .Forall r d :: rest => if r = role then d :: fillers role rest else fillers role rest
  | _ :: rest => fillers role rest
/-- The role and filler of every existential restriction, in list order. -/
def existentials : List nnf.NnfConcept → List (ObjectProperty × nnf.NnfConcept)
  | [] => []
  | .Exists r c :: rest => (r,c) :: existentials rest
  | _ :: rest => existentials rest

variable {Object : Type u} {Value : Type v}

/-- Every concept in the list holds at the element. -/
def Holds (I : Interpretation Object Value) (x : Object) (cs : List nnf.NnfConcept) : Prop :=
  ∀ c ∈ cs, conceptDenote I c x
/-- Some interpretation, in the given universes, has an element in every concept. -/
def Satisfiable (cs : List nnf.NnfConcept) : Prop :=
  ∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (x : Object), Holds I x cs
/-- A tree interpretation over paths has every concept at its root. -/
def TreeSatisfiable (cs : List nnf.NnfConcept) : Prop :=
  ∃ I : Interpretation (List Nat) Unit, Holds I [] cs
/-- The procedure's contract: acceptance yields a tree model, and every model,
    in the given universes, forces acceptance. -/
def Decides (cs : List nnf.NnfConcept) (result : Bool) : Prop :=
  (result = true → TreeSatisfiable cs) ∧ (Satisfiable.{u,v} cs → result = true)

theorem class_eq_iff (a b : Class) : a = b ↔ a.iri.spelling.val = b.iri.spelling.val := by
  cases a with | mk ai => cases b with | mk bi => cases ai; cases bi; simp [alloc.vec.Vec.eq_iff]
theorem property_eq_iff (a b : ObjectProperty) : a = b ↔ a.iri.spelling.val = b.iri.spelling.val := by
  cases a with | mk ai => cases b with | mk bi => cases ai; cases bi; simp [alloc.vec.Vec.eq_iff]

theorem fillers_mem (role : ObjectProperty) (cs : List nnf.NnfConcept) (d : nnf.NnfConcept) :
    d ∈ fillers role cs ↔ .Forall role d ∈ cs := by
  induction cs with
  | nil => simp [fillers]
  | cons c rest ih =>
    cases c with
    | Forall r e =>
      by_cases same : r = role
      · subst same; simp [fillers,ih,eq_comm]
      · simp only [fillers,same,if_false,ih,List.mem_cons]
        constructor
        · exact .inr
        · rintro (equal | later)
          · cases equal; exact absurd rfl same
          · exact later
    | _ => simp [fillers,ih]
theorem fillers_exists_total (cs : List nnf.NnfConcept) (role : ObjectProperty) (d : nnf.NnfConcept)
    (member : .Exists role d ∈ cs) : total (fillers role cs) + weight d + 1 ≤ total cs := by
  have bounded : ∀ cs : List nnf.NnfConcept, total (fillers role cs) ≤ total cs := by
    intro cs
    induction cs with
    | nil => simp [fillers,total]
    | cons c rest ih =>
      cases c with
      | Forall r e =>
        by_cases same : r = role
        · simp [fillers,same,total,weight] at *; omega
        · simp [fillers,same,total,weight] at *; omega
      | _ => simp [fillers,total,weight] at *; omega
  induction cs with
  | nil => simp at member
  | cons c rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst same
      have := bounded rest
      simp [fillers,total,weight] at *; omega
    · have := ih later
      cases c with
      | Forall r e =>
        by_cases same : r = role
        · simp [fillers,same,total,weight] at *; omega
        · simp [fillers,same,total,weight] at *; omega
      | _ => simp [fillers,total,weight] at *; omega
theorem existentials_mem (cs : List nnf.NnfConcept) (r : ObjectProperty) (c : nnf.NnfConcept) :
    (r,c) ∈ existentials cs ↔ .Exists r c ∈ cs := by
  induction cs with
  | nil => simp [existentials]
  | cons d rest ih =>
    cases d with
    | Exists s e => simp [existentials,ih,eq_comm,and_comm]
    | _ => simp [existentials,ih]

theorem duplicate_correct (list : tableau.Concepts) : tableau.duplicate list = .ok (list,list) := by
  induction list with
  | Empty => rw [tableau.duplicate]
  | Entry c next ih => rw [tableau.duplicate]; simp [ih]
theorem contains_atom_correct (list : tableau.Concepts) (k : Class) :
    tableau.contains_atom list k = .ok (decide (.Atom k ∈ toList list),list) := by
  induction list with
  | Empty => rw [tableau.contains_atom.eq_def]; simp [toList]
  | Entry c next ih =>
    rw [tableau.contains_atom.eq_def]
    cases c with
    | Atom other =>
      have same : (other.iri.spelling.val = k.iri.spelling.val) ↔ k = other := by
        rw [class_eq_iff]; exact eq_comm
      by_cases equal : k = other
      · subst equal; simp [ih,toList,Rowl.Symbols.same_spelling_total_correct]
      · have different : ¬ other.iri.spelling.val = k.iri.spelling.val := fun h => equal (same.mp h)
        simp [ih,toList,Rowl.Symbols.same_spelling_total_correct,different,equal]
    | _ => simp [ih,toList]
theorem has_clash_correct (all cursor : tableau.Concepts) :
    tableau.has_clash all cursor =
      .ok (decide (∃ k, .NotAtom k ∈ toList cursor ∧ .Atom k ∈ toList all),all) := by
  induction cursor with
  | Empty => rw [tableau.has_clash.eq_def]; simp [toList]
  | Entry c next ih =>
    rw [tableau.has_clash.eq_def]
    cases c with
    | NotAtom k =>
      by_cases present : .Atom k ∈ toList all
      · simp [contains_atom_correct,ih,toList,present]
      · simp [contains_atom_correct,ih,toList,present]
    | _ => simp [ih,toList]
theorem universal_fillers_correct (list : tableau.Concepts) (role : ObjectProperty) :
    tableau.universal_fillers list role = .ok (fromList (fillers role (toList list)),list) := by
  induction list with
  | Empty => rw [tableau.universal_fillers]; simp [toList,fillers,fromList]
  | Entry c next ih =>
    rw [tableau.universal_fillers]
    cases c with
    | Forall r d =>
      by_cases same : r = role
      · subst same; simp [ih,toList,fillers,fromList,Rowl.Symbols.same_spelling_total_correct]
      · have different : ¬ r.iri.spelling.val = role.iri.spelling.val := fun h => same ((property_eq_iff r role).mpr h)
        simp [ih,toList,fillers,Rowl.Symbols.same_spelling_total_correct,different,same]
    | _ => simp [ih,toList,fillers]

theorem holds_cons (I : Interpretation Object Value) (x : Object) (c : nnf.NnfConcept) (cs : List nnf.NnfConcept) :
    Holds I x (c :: cs) ↔ conceptDenote I c x ∧ Holds I x cs := by
  simp [Holds]
theorem holds_of_subset {I : Interpretation Object Value} {x : Object} {small large : List nnf.NnfConcept}
    (subset : ∀ c ∈ small, c ∈ large) (holds : Holds I x large) : Holds I x small :=
  fun c member => holds c (subset c member)
theorem tree_of_subset {small large : List nnf.NnfConcept} (subset : ∀ c ∈ small, c ∈ large)
    (model : TreeSatisfiable large) : TreeSatisfiable small := by
  obtain ⟨I,holds⟩ := model
  exact ⟨I,holds_of_subset subset holds⟩
theorem satisfiable_of_subset {small large : List nnf.NnfConcept} (subset : ∀ c ∈ small, c ∈ large)
    (model : Satisfiable.{u,v} large) : Satisfiable.{u,v} small := by
  obtain ⟨Object,Value,I,x,holds⟩ := model
  exact ⟨Object,Value,I,x,holds_of_subset subset holds⟩

/-- An interpretation with no class or role facts. -/
def emptyModel : Interpretation (List Nat) Unit where
  objectsNonempty := ⟨[]⟩
  dataNonempty := ⟨()⟩
  classes _ _ := False
  objectProperties _ _ _ := False
  dataProperties _ _ _ := False
  namedIndividuals _ := []
  anonymousIndividuals _ := []
  datatypes _ _ := False
  literals _ := ()
  facets _ _ := False
  named _ := False
/-- The tree model of a clash-free leaf: the root [] has exactly the given named
    classes, and the root's i-th successor i :: p continues as path p of the
    i-th successor model, reached along that successor's role. -/
def tree (atoms : Class → Prop) (successors : List (ObjectProperty × Interpretation (List Nat) Unit)) :
    Interpretation (List Nat) Unit where
  objectsNonempty := ⟨[]⟩
  dataNonempty := ⟨()⟩
  classes k p := match p with
    | [] => atoms k
    | i :: q => ∃ s, successors[i]? = some s ∧ s.2.classes k q
  objectProperties r p q := match p, q with
    | [], [i] => ∃ s, successors[i]? = some s ∧ s.1 = r
    | i :: p', j :: q' => i = j ∧ ∃ s, successors[i]? = some s ∧ s.2.objectProperties r p' q'
    | _, _ => False
  dataProperties _ _ _ := False
  namedIndividuals _ := []
  anonymousIndividuals _ := []
  datatypes _ _ := False
  literals _ := ()
  facets _ _ := False
  named _ := False

/-- Below the root, the tree model behaves exactly like the chosen successor model. -/
theorem tree_subtree (atoms : Class → Prop) (successors : List (ObjectProperty × Interpretation (List Nat) Unit))
    (i : Nat) (s : ObjectProperty × Interpretation (List Nat) Unit) (found : successors[i]? = some s) :
    ∀ (c : nnf.NnfConcept) (p : List Nat), conceptDenote (tree atoms successors) c (i :: p) ↔ conceptDenote s.2 c p := by
  intro c
  induction c with
  | Top => intro p; simp [conceptDenote]
  | Bottom => intro p; simp [conceptDenote]
  | Atom k =>
    intro p
    show (∃ s', successors[i]? = some s' ∧ s'.2.classes k p) ↔ s.2.classes k p
    rw [found]
    constructor
    · rintro ⟨s',same,holds⟩; cases same; exact holds
    · intro holds; exact ⟨s,rfl,holds⟩
  | NotAtom k =>
    intro p
    show (¬ ∃ s', successors[i]? = some s' ∧ s'.2.classes k p) ↔ ¬ s.2.classes k p
    rw [found]
    constructor
    · intro none holds; exact none ⟨s,rfl,holds⟩
    · rintro none ⟨s',same,holds⟩; cases same; exact none holds
  | And a b iha ihb => intro p; simp [conceptDenote,iha,ihb]
  | Or a b iha ihb => intro p; simp [conceptDenote,iha,ihb]
  | Exists r c ih =>
    intro p
    simp only [conceptDenote]
    constructor
    · rintro ⟨y,edge,holds⟩
      cases y with
      | nil => simp [tree] at edge
      | cons j q =>
        simp only [tree] at edge
        obtain ⟨rfl,s',found',edge⟩ := edge
        rw [found] at found'
        cases found'
        exact ⟨q,edge,(ih q).mp holds⟩
    · rintro ⟨q,edge,holds⟩
      exact ⟨i :: q,(show i = i ∧ ∃ s', successors[i]? = some s' ∧ s'.2.objectProperties r p q from ⟨rfl,s,found,edge⟩),
        (ih q).mpr holds⟩
  | Forall r c ih =>
    intro p
    simp only [conceptDenote]
    constructor
    · intro all q edge
      exact (ih q).mp (all (i :: q)
        (show i = i ∧ ∃ s', successors[i]? = some s' ∧ s'.2.objectProperties r p q from ⟨rfl,s,found,edge⟩))
    · intro all y edge
      cases y with
      | nil => simp [tree] at edge
      | cons j q =>
        simp only [tree] at edge
        obtain ⟨rfl,s',found',edge⟩ := edge
        rw [found] at found'
        cases found'
        exact (ih q).mpr (all q edge)

/-- A clash-free list of literals whose existential successors all have tree
    models has a tree model itself: its root carries the positive named classes. -/
theorem tree_root (cs : List nnf.NnfConcept) (literal : ∀ c ∈ cs, Literal c) (noClash : ¬ Clash cs)
    (models : ∀ r c, .Exists r c ∈ cs → TreeSatisfiable (c :: fillers r cs)) : TreeSatisfiable cs := by
  let model : ObjectProperty × nnf.NnfConcept → Interpretation (List Nat) Unit := fun rc =>
    if h : TreeSatisfiable (rc.2 :: fillers rc.1 cs) then Classical.choose h else emptyModel
  have modelHolds : ∀ r c, .Exists r c ∈ cs → Holds (model (r,c)) [] (c :: fillers r cs) := by
    intro r c member
    have h := models r c member
    simp only [model,h,↓reduceDIte]
    exact Classical.choose_spec h
  let successors := (existentials cs).map (fun rc => (rc.1,model rc))
  refine ⟨tree (fun k => .Atom k ∈ cs) successors,?_⟩
  intro c member
  have isLiteral := literal c member
  cases c with
  | Top | Bottom | And _ _ | Or _ _ => simp [Literal] at isLiteral
  | Atom k => simp [conceptDenote,tree,member]
  | NotAtom k =>
    simp only [conceptDenote,tree]
    intro positive
    exact noClash ⟨k,member,positive⟩
  | Exists r d =>
    have listed : (r,d) ∈ existentials cs := (existentials_mem cs r d).mpr member
    obtain ⟨i,found⟩ := List.mem_iff_getElem?.mp listed
    have successor : successors[i]? = some (r,model (r,d)) := by
      simp [successors,List.getElem?_map,found]
    refine ⟨[i],by simp only [tree]; exact ⟨_,successor,rfl⟩,?_⟩
    rw [tree_subtree _ _ i _ successor d []]
    exact (modelHolds r d member) d (by simp)
  | Forall r d =>
    intro y edge
    cases y with
    | nil => simp [tree] at edge
    | cons i q =>
      cases q with
      | cons _ _ => simp [tree] at edge
      | nil =>
        simp only [tree] at edge
        obtain ⟨s,found,role⟩ := edge
        have listed : ∃ rc, (existentials cs)[i]? = some rc ∧ s = (rc.1,model rc) := by
          simp only [successors,List.getElem?_map] at found
          cases h : (existentials cs)[i]? with
          | none => rw [h] at found; cases found
          | some rc => rw [h] at found; cases found; exact ⟨rc,rfl,rfl⟩
        obtain ⟨rc,rcFound,rfl⟩ := listed
        have rcMember : (rc.1,rc.2) ∈ existentials cs := List.mem_of_getElem? rcFound
        have exists_member := (existentials_mem cs rc.1 rc.2).mp rcMember
        simp only at role
        subst role
        rw [tree_subtree _ _ i _ found d []]
        exact (modelHolds rc.1 rc.2 exists_member) d
          (List.mem_cons_of_mem _ ((fillers_mem rc.1 cs d).mpr member))

private theorem cons_literal {c : nnf.NnfConcept} {literals : tableau.Concepts} (isLiteral : Literal c)
    (literal : ∀ d ∈ toList literals, Literal d) : ∀ d ∈ toList (.Entry c literals), Literal d := by
  intro d member
  simp only [toList,List.mem_cons] at member
  rcases member with rfl | rest
  · exact isLiteral
  · exact literal d rest
/-- Moving a concept from the pending list to the literal list keeps the same members. -/
private theorem move_literal {c : nnf.NnfConcept} {next literals : tableau.Concepts} {result : Bool}
    (decides : Decides.{u,v} (toList next ++ toList (.Entry c literals)) result) :
    Decides.{u,v} (toList (.Entry c next) ++ toList literals) result := by
  have same : ∀ d, d ∈ toList (.Entry c next) ++ toList literals ↔ d ∈ toList next ++ toList (.Entry c literals) := by
    intro d; simp [toList]; tauto
  exact ⟨fun accepted => tree_of_subset (fun d member => (same d).mp member) (decides.1 accepted),
    fun model => decides.2 (satisfiable_of_subset (fun d member => (same d).mpr member) model)⟩

/-- Every existential in `cursor` is checked with its successor list against `all`. -/
private theorem existentials_hold_correct (all cursor : tableau.Concepts)
    (child : ∀ r c, .Exists r c ∈ toList cursor →
      ∃ result, tableau.expand (.Entry c (fromList (fillers r (toList all)))) .Empty = .ok result) :
    ∃ result, tableau.existentials_hold all cursor = .ok (result,all) ∧
      (result = true ↔ ∀ r c, .Exists r c ∈ toList cursor →
        tableau.expand (.Entry c (fromList (fillers r (toList all)))) .Empty = .ok true) := by
  induction cursor with
  | Empty => exact ⟨true,by rw [tableau.existentials_hold.eq_def],by simp [toList]⟩
  | Entry c next ih =>
    obtain ⟨later,laterRead,laterIff⟩ := ih (fun r d member => child r d (by simp [toList,member]))
    rw [tableau.existentials_hold.eq_def]
    cases c with
    | Exists r d =>
      obtain ⟨here,hereRead⟩ := child r d (by simp [toList])
      refine ⟨here && later,?_,?_⟩
      · cases here <;> simp [universal_fillers_correct,hereRead,laterRead]
      · rw [Bool.and_eq_true,laterIff]
        constructor
        · rintro ⟨yes,rest⟩ r' d' member
          simp only [toList,List.mem_cons] at member
          rcases member with same | later'
          · cases same; rw [hereRead,yes]
          · exact rest r' d' later'
        · intro all'
          refine ⟨?_,fun r' d' member => all' r' d' (by simp [toList,member])⟩
          have accepted := all' r d (by simp [toList])
          rw [hereRead] at accepted
          exact Result.ok_injective accepted
    | _ =>
      refine ⟨later,by simpa using laterRead,?_⟩
      rw [laterIff]
      simp [toList]

/-- The actual procedure terminates on every pending list and literal list, and
    decides exactly whether all their concepts hold at one element. -/
theorem expand_correct (pending literals : tableau.Concepts) (literal : ∀ c ∈ toList literals, Literal c) :
    ∃ result, tableau.expand pending literals = .ok result ∧
      Decides.{u,v} (toList pending ++ toList literals) result := by
  cases pending with
  | Empty =>
    have successors : ∀ r c, .Exists r c ∈ toList literals →
        ∃ result, tableau.expand (.Entry c (fromList (fillers r (toList literals)))) .Empty = .ok result ∧
          Decides.{u,v} (c :: fillers r (toList literals)) result := by
      intro r c member
      have bound := fillers_exists_total (toList literals) r c member
      obtain ⟨result,executed,decides⟩ :=
        expand_correct (.Entry c (fromList (fillers r (toList literals)))) .Empty (by simp [toList])
      exact ⟨result,executed,by simpa [toList,toList_fromList] using decides⟩
    rw [tableau.expand.eq_def]
    simp only [duplicate_correct,has_clash_correct,bind_ok,uncurry_apply_pair]
    by_cases clash : ∃ k, .NotAtom k ∈ toList literals ∧ .Atom k ∈ toList literals
    · refine ⟨false,by simp [clash],?_,?_⟩
      · intro impossible; cases impossible
      · rintro ⟨Object,Value,I,x,holds⟩
        obtain ⟨k,negative,positive⟩ := clash
        have no := holds (.NotAtom k) (by simp [toList,negative])
        have yes := holds (.Atom k) (by simp [toList,positive])
        exact absurd yes no
    · obtain ⟨result,executed,iff⟩ := existentials_hold_correct literals literals
        (fun r c member => (successors r c member).imp fun _ h => h.1)
      refine ⟨result,by simp [clash,executed],?_,?_⟩
      · intro accepted
        have all := iff.mp accepted
        simp only [toList,List.nil_append]
        exact tree_root (toList literals) literal clash fun r c member => by
          obtain ⟨answer,run,decides⟩ := successors r c member
          have yes := all r c member
          rw [run] at yes
          exact decides.1 (Result.ok_injective yes)
      · rintro ⟨Object,Value,I,x,holds⟩
        simp only [toList,List.nil_append] at holds
        apply iff.mpr
        intro r c member
        obtain ⟨answer,run,decides⟩ := successors r c member
        rw [run]
        have exists' := holds (.Exists r c) member
        obtain ⟨y,edge,inner⟩ := exists'
        have model : Satisfiable.{u,v} (c :: fillers r (toList literals)) := by
          refine ⟨Object,Value,I,y,?_⟩
          intro d member'
          simp only [List.mem_cons] at member'
          rcases member' with rfl | filler
          · exact inner
          · exact holds (.Forall r d) ((fillers_mem r _ d).mp filler) y edge
        rw [decides.2 model]
  | Entry c next =>
    rw [tableau.expand.eq_def]
    cases c with
    | Top =>
      obtain ⟨result,executed,decides⟩ := expand_correct next literals literal
      refine ⟨result,by simpa using executed,?_,?_⟩
      · intro accepted
        obtain ⟨I,holds⟩ := decides.1 accepted
        refine ⟨I,fun d member => ?_⟩
        simp only [toList,List.cons_append,List.mem_cons] at member
        rcases member with rfl | rest
        · simp [conceptDenote]
        · exact holds d rest
      · intro model
        exact decides.2 (satisfiable_of_subset (fun d member => by
          simp only [toList,List.cons_append,List.mem_cons]; exact .inr member) model)
    | Bottom =>
      refine ⟨false,rfl,?_⟩
      constructor
      · intro impossible; cases impossible
      · rintro ⟨Object,Value,I,x,holds⟩
        exact absurd (holds .Bottom (by simp [toList])) (by simp [conceptDenote])
    | And a b =>
      obtain ⟨result,executed,decides⟩ := expand_correct (.Entry a (.Entry b next)) literals literal
      refine ⟨result,by simpa using executed,?_,?_⟩
      · intro accepted
        obtain ⟨I,holds⟩ := decides.1 accepted
        refine ⟨I,fun d member => ?_⟩
        simp only [toList,List.cons_append,List.mem_cons] at member
        rcases member with rfl | rest
        · exact ⟨holds a (by simp [toList]),holds b (by simp [toList])⟩
        · exact holds d (by simp [toList,rest])
      · rintro ⟨Object,Value,I,x,holds⟩
        apply decides.2
        refine ⟨Object,Value,I,x,fun d member => ?_⟩
        have conj := holds (.And a b) (by simp [toList])
        simp only [toList,List.cons_append,List.mem_cons] at member
        rcases member with rfl | rfl | rest
        · exact conj.1
        · exact conj.2
        · exact holds d (by simp [toList,rest])
    | Or a b =>
      obtain ⟨left,leftRun,leftDecides⟩ := expand_correct (.Entry a next) literals literal
      obtain ⟨right,rightRun,rightDecides⟩ := expand_correct (.Entry b next) literals literal
      refine ⟨left || right,?_,?_,?_⟩
      · cases left <;> simp [duplicate_correct,leftRun,rightRun]
      · intro accepted
        rcases Bool.or_eq_true_iff.mp accepted with yes | yes
        · obtain ⟨I,holds⟩ := leftDecides.1 yes
          refine ⟨I,fun d member => ?_⟩
          simp only [toList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rest
          · exact .inl (holds a (by simp [toList]))
          · exact holds d (by simp [toList,rest])
        · obtain ⟨I,holds⟩ := rightDecides.1 yes
          refine ⟨I,fun d member => ?_⟩
          simp only [toList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rest
          · exact .inr (holds b (by simp [toList]))
          · exact holds d (by simp [toList,rest])
      · rintro ⟨Object,Value,I,x,holds⟩
        have disj := holds (.Or a b) (by simp [toList])
        rw [Bool.or_eq_true_iff]
        rcases disj with yes | yes
        · left
          apply leftDecides.2
          refine ⟨Object,Value,I,x,fun d member => ?_⟩
          simp only [toList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rest
          · exact yes
          · exact holds d (by simp [toList,rest])
        · right
          apply rightDecides.2
          refine ⟨Object,Value,I,x,fun d member => ?_⟩
          simp only [toList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rest
          · exact yes
          · exact holds d (by simp [toList,rest])
    | Atom k =>
      obtain ⟨result,executed,decides⟩ := expand_correct next (.Entry (.Atom k) literals)
        (cons_literal (by simp [Literal]) literal)
      exact ⟨result,by simpa using executed,move_literal decides⟩
    | NotAtom k =>
      obtain ⟨result,executed,decides⟩ := expand_correct next (.Entry (.NotAtom k) literals)
        (cons_literal (by simp [Literal]) literal)
      exact ⟨result,by simpa using executed,move_literal decides⟩
    | Exists r d =>
      obtain ⟨result,executed,decides⟩ := expand_correct next (.Entry (.Exists r d) literals)
        (cons_literal (by simp [Literal]) literal)
      exact ⟨result,by simpa using executed,move_literal decides⟩
    | Forall r d =>
      obtain ⟨result,executed,decides⟩ := expand_correct next (.Entry (.Forall r d) literals)
        (cons_literal (by simp [Literal]) literal)
      exact ⟨result,by simpa using executed,move_literal decides⟩
termination_by (total (toList pending) + total (toList literals),total (toList pending))
decreasing_by
  all_goals simp_wf
  all_goals
    try rw [Prod.lex_def]
    simp only [toList,toList_fromList,total,weight,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil] at *
    omega

/-- The public procedure terminates, every acceptance comes with a tree model, and
    every concept with an instance in some interpretation, in any universe, is accepted. -/
theorem satisfiable_correct (c : nnf.NnfConcept) :
    ∃ result, tableau.satisfiable c = .ok result ∧
      (result = true → ∃ I : Interpretation (List Nat) Unit, conceptDenote I c []) ∧
      ((∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (x : Object),
        conceptDenote I c x) → result = true) := by
  obtain ⟨result,executed,decides⟩ := expand_correct.{u,v} (.Entry c .Empty) .Empty (by simp [toList])
  refine ⟨result,by rw [tableau.satisfiable]; exact executed,?_,?_⟩
  · intro accepted
    obtain ⟨I,holds⟩ := decides.1 accepted
    exact ⟨I,holds c (by simp [toList])⟩
  · rintro ⟨Object,Value,I,x,holds⟩
    exact decides.2 ⟨Object,Value,I,x,fun d member => by
      simp [toList] at member
      subst member
      exact holds⟩

/-- The tableau never rejects an OWL class expression that has an instance in an
    OWL interpretation (one fixing owl:Thing and owl:Nothing). -/
theorem class_instances_accepted (e : ClassExpression) (c : nnf.NnfConcept)
    (translated : nnf.nnf e true = .ok (some c)) (I : Interpretation Object Value)
    (fixes : Rowl.Nnf.Fixes I) (x : Object) (member : classDenote I e x) :
    tableau.satisfiable c = .ok true := by
  obtain ⟨result,executed,_,complete⟩ := satisfiable_correct.{u,v} c
  rw [executed]
  have instance' := (Rowl.Nnf.nnf_meaning e true c translated I fixes x).mpr member
  rw [complete ⟨Object,Value,I,x,instance'⟩]
/-- A rejection proves the OWL class expression empty in every OWL interpretation,
    which is how unsatisfiability and subsumption answers are justified. -/
theorem rejected_class_empty (e : ClassExpression) (c : nnf.NnfConcept)
    (translated : nnf.nnf e true = .ok (some c)) (rejected : tableau.satisfiable c = .ok false)
    (I : Interpretation Object Value) (fixes : Rowl.Nnf.Fixes I) (x : Object) : ¬ classDenote I e x := by
  intro member
  have accepted := class_instances_accepted e c translated I fixes x member
  rw [rejected] at accepted
  cases Result.ok_injective accepted
end Rowl.Tableau
