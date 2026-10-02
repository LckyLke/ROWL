import Rowl.RoleBox

/-!
Hintikka families: the certificate a tableau with blocking produces. A family
is a list of clash-free literal sets that all satisfy the TBox concept, where
every existential restriction has a witness set in the family satisfying what
the universal restrictions require along its role (`roleFillers`): the filler
of every universal restriction on a property that includes the role, and the
restriction itself on every transitive property in between. Any such family is
a model: its elements are the literal sets themselves, and a set reaches
another along a role when the other satisfies everything the first requires
along that role. When the listed inclusions include their compositions, this
model respects the role axioms. This semantic core is independent of the Rust
procedure.
-/
namespace Rowl.Hintikka
open RowlRust RowlRust.model
open Rowl.Owl (Interpretation)
open Rowl.Nnf (conceptDenote)
open Rowl.RoleBox (Below Respects transitives below_refl)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
universe u v

/-- A literal set satisfies a concept syntactically: conjunctions and
    disjunctions are read propositionally; every other concept must be listed. -/
def Sat (L : List nnf.NnfConcept) : nnf.NnfConcept → Prop
  | .Top => True
  | .Bottom => False
  | .Atom k => .Atom k ∈ L
  | .NotAtom k => .NotAtom k ∈ L
  | .And a b => Sat L a ∧ Sat L b
  | .Or a b => Sat L a ∨ Sat L b
  | .Exists r c => .Exists r c ∈ L
  | .Forall r c => .Forall r c ∈ L
/-- The literal set satisfies every concept of the list. -/
def SatAll (L cs : List nnf.NnfConcept) : Prop := ∀ c ∈ cs, Sat L c
/-- No named class occurs both negated and positively. -/
def ClashFree (L : List nnf.NnfConcept) : Prop := ∀ k, .NotAtom k ∈ L → .Atom k ∉ L

/-- What the universal restriction `∀sup.d` requires of an element reached
    along `sub`: nothing unless `sub` is included in `sup`; otherwise `d` and
    `∀t.d` for every transitive `t` between them, in the listed order. -/
noncomputable def universalItems (rb : role_box.RoleBox) (sub sup : ObjectProperty) (d : nnf.NnfConcept) :
    List nnf.NnfConcept :=
  if Below rb sub sup then
    d :: ((transitives rb).filter (fun t => decide (Below rb sub t ∧ Below rb t sup))).map (fun t => .Forall t d)
  else []
/-- What the universal restrictions of a list require of an element reached
    along the role, in list order. -/
noncomputable def roleFillers (rb : role_box.RoleBox) (role : ObjectProperty) :
    List nnf.NnfConcept → List nnf.NnfConcept
  | [] => []
  | .Forall q d :: rest => universalItems rb role q d ++ roleFillers rb role rest
  | _ :: rest => roleFillers rb role rest

theorem universalItems_mem (rb : role_box.RoleBox) (sub sup : ObjectProperty) (d x : nnf.NnfConcept) :
    x ∈ universalItems rb sub sup d ↔ Below rb sub sup ∧
      (x = d ∨ ∃ t ∈ transitives rb, Below rb sub t ∧ Below rb t sup ∧ x = .Forall t d) := by
  unfold universalItems
  by_cases below : Below rb sub sup
  · simp only [below,↓reduceIte,List.mem_cons,List.mem_map,List.mem_filter,decide_eq_true_eq,true_and]
    constructor
    · rintro (rfl | ⟨t,⟨member,first,second⟩,rfl⟩)
      · exact .inl rfl
      · exact .inr ⟨t,member,first,second,rfl⟩
    · rintro (rfl | ⟨t,member,first,second,rfl⟩)
      · exact .inl rfl
      · exact .inr ⟨t,⟨member,first,second⟩,rfl⟩
  · simp [below]
/-- An item is required along a role exactly when some universal restriction of
    the list on a property including the role asks for it. -/
theorem roleFillers_mem (rb : role_box.RoleBox) (role : ObjectProperty) (L : List nnf.NnfConcept)
    (x : nnf.NnfConcept) :
    x ∈ roleFillers rb role L ↔ ∃ q d, .Forall q d ∈ L ∧ Below rb role q ∧
      (x = d ∨ ∃ t ∈ transitives rb, Below rb role t ∧ Below rb t q ∧ x = .Forall t d) := by
  induction L with
  | nil => simp [roleFillers]
  | cons c rest ih =>
    cases c with
    | Forall q d =>
      simp only [roleFillers,List.mem_append,universalItems_mem,ih,List.mem_cons]
      constructor
      · rintro (⟨below,required⟩ | ⟨q',d',member,below,required⟩)
        · exact ⟨q,d,.inl rfl,below,required⟩
        · exact ⟨q',d',.inr member,below,required⟩
      · rintro ⟨q',d',(same | member),below,required⟩
        · cases same; exact .inl ⟨below,required⟩
        · exact .inr ⟨q',d',member,below,required⟩
    | _ =>
      simp only [roleFillers,ih,List.mem_cons]
      constructor
      · rintro ⟨q',d',member,rest'⟩; exact ⟨q',d',.inr member,rest'⟩
      · rintro ⟨q',d',(same | member),rest'⟩
        · cases same
        · exact ⟨q',d',member,rest'⟩

/-- Every existential restriction of `L` has a witness in `pool`: a literal set
    satisfying the TBox concept, the filler and everything the universal
    restrictions of `L` require along its role. -/
def Witnessed (rb : role_box.RoleBox) (axioms : nnf.NnfConcept) (pool : List (List nnf.NnfConcept))
    (L : List nnf.NnfConcept) : Prop :=
  ∀ r c, .Exists r c ∈ L → ∃ L', L' ∈ pool ∧ Sat L' axioms ∧ Sat L' c ∧ ∀ x ∈ roleFillers rb r L, Sat L' x
/-- Every set of the family is clash-free, satisfies the TBox concept, and has its
    existentials witnessed in the family or among the ancestors. -/
def Coherent (rb : role_box.RoleBox) (axioms : nnf.NnfConcept) (family ancestors : List (List nnf.NnfConcept)) :
    Prop :=
  ∀ L ∈ family, ClashFree L ∧ Sat L axioms ∧ Witnessed rb axioms (family ++ ancestors) L

/-- Syntactic satisfaction only grows with the literal set. -/
theorem sat_mono {L L' : List nnf.NnfConcept} (sub : ∀ c ∈ L, c ∈ L') : ∀ c, Sat L c → Sat L' c := by
  intro c
  induction c with
  | Top | Bottom => exact id
  | Atom k | NotAtom k => exact sub _
  | Exists r c | Forall r c => exact sub _
  | And a b iha ihb => exact fun h => ⟨iha h.1,ihb h.2⟩
  | Or a b iha ihb => exact fun h => h.elim (fun x => .inl (iha x)) (fun x => .inr (ihb x))
/-- A literal is satisfied exactly when it is listed. -/
theorem sat_literal (L : List nnf.NnfConcept) (c : nnf.NnfConcept) (literal : Rowl.Tableau.Literal c) :
    Sat L c ↔ c ∈ L := by
  cases c <;> simp_all [Sat,Rowl.Tableau.Literal]

/-- The model of a family: its elements are the family's literal sets; a set
    belongs to a named class when it lists it, and a set reaches another along a
    role when the other satisfies everything the first requires along that role. -/
noncomputable def familyModel (rb : role_box.RoleBox) (family : List (List nnf.NnfConcept))
    (root : List nnf.NnfConcept) (rootMember : root ∈ family) : Interpretation {L // L ∈ family} Unit where
  objectsNonempty := ⟨⟨root,rootMember⟩⟩
  dataNonempty := ⟨()⟩
  classes k L := .Atom k ∈ L.val
  objectProperties r L L' := ∀ x ∈ roleFillers rb r L.val, Sat L'.val x
  dataProperties _ _ _ := False
  namedIndividuals _ := ⟨root,rootMember⟩
  anonymousIndividuals _ := ⟨root,rootMember⟩
  datatypes _ _ := False
  literals _ := ()
  facets _ _ := False
  named _ := False

/-- Truth lemma: in the model of a closed coherent family, each set has every
    concept it satisfies syntactically. -/
theorem family_truth (rb : role_box.RoleBox) (axioms : nnf.NnfConcept) (family : List (List nnf.NnfConcept))
    (coherent : Coherent rb axioms family []) (root : List nnf.NnfConcept) (rootMember : root ∈ family) :
    ∀ (c : nnf.NnfConcept) (L : {L // L ∈ family}), Sat L.val c →
      conceptDenote (familyModel rb family root rootMember) c L := by
  intro c
  induction c with
  | Top => intro L _; trivial
  | Bottom => intro L impossible; exact impossible
  | Atom k => intro L holds; exact holds
  | NotAtom k =>
    intro L holds positive
    exact (coherent L.val L.property).1 k holds positive
  | And a b iha ihb => intro L holds; exact ⟨iha L holds.1,ihb L holds.2⟩
  | Or a b iha ihb =>
    intro L holds
    exact holds.elim (fun x => .inl (iha L x)) (fun x => .inr (ihb L x))
  | Exists r c ih =>
    intro L holds
    obtain ⟨L',member,_,filler,required⟩ := (coherent L.val L.property).2.2 r c holds
    simp only [List.append_nil] at member
    exact ⟨⟨L',member⟩,required,ih ⟨L',member⟩ filler⟩
  | Forall r c ih =>
    intro L holds L' edge
    exact ih L' (edge c ((roleFillers_mem rb r L.val c).mpr ⟨r,c,holds,below_refl rb r,.inl rfl⟩))

/-- When the listed inclusions include their compositions, the model of a family
    satisfies every listed inclusion and transitivity. -/
theorem family_respects (rb : role_box.RoleBox) (closed : Rowl.RoleBox.Closed rb)
    (family : List (List nnf.NnfConcept)) (root : List nnf.NnfConcept) (rootMember : root ∈ family) :
    Respects (familyModel rb family root rootMember) rb := by
  refine ⟨?_,?_⟩
  · intro s r listed L L' edge x required
    apply edge x
    obtain ⟨q,d,member,below,kind⟩ := (roleFillers_mem rb r L.val x).mp required
    have sr : Below rb s r := .inr listed
    refine (roleFillers_mem rb s L.val x).mpr ⟨q,d,member,closed s r q sr below,?_⟩
    rcases kind with rfl | ⟨t,transitive,first,second,rfl⟩
    · exact .inl rfl
    · exact .inr ⟨t,transitive,closed s r t sr first,second,rfl⟩
  · intro t transitive L1 L2 L3 first second x required
    obtain ⟨q,d,member,below,kind⟩ := (roleFillers_mem rb t L1.val x).mp required
    rcases kind with rfl | ⟨t',transitive',tt',t'q,rfl⟩
    · have along : (nnf.NnfConcept.Forall t x) ∈ L2.val :=
        first _ ((roleFillers_mem rb t L1.val _).mpr
          ⟨q,x,member,below,.inr ⟨t,transitive,below_refl rb t,below,rfl⟩⟩)
      exact second x ((roleFillers_mem rb t L2.val x).mpr ⟨t,x,along,below_refl rb t,.inl rfl⟩)
    · have along : (nnf.NnfConcept.Forall t' d) ∈ L2.val := first _ required
      exact second _ ((roleFillers_mem rb t L2.val _).mpr
        ⟨t',d,along,tt',.inr ⟨t',transitive',tt',below_refl rb t',rfl⟩⟩)

/-- A closed coherent family with a set satisfying the concept yields a model of
    the TBox concept and the role axioms with an instance of the concept. -/
theorem model_of_family (rb : role_box.RoleBox) (closed : Rowl.RoleBox.Closed rb) (axioms c : nnf.NnfConcept)
    (family : List (List nnf.NnfConcept)) (coherent : Coherent rb axioms family []) (root : List nnf.NnfConcept)
    (rootMember : root ∈ family) (rootSat : Sat root c) :
    ∃ (Object : Type) (I : Interpretation Object Unit), Respects I rb ∧ (∀ y, conceptDenote I axioms y) ∧
      ∃ x, conceptDenote I c x := by
  refine ⟨{L // L ∈ family},familyModel rb family root rootMember,
    family_respects rb closed family root rootMember,?_,⟨root,rootMember⟩,?_⟩
  · intro y
    exact family_truth rb axioms family coherent root rootMember axioms y (coherent y.val y.property).2.1
  · exact family_truth rb axioms family coherent root rootMember c ⟨root,rootMember⟩ rootSat
end Rowl.Hintikka
