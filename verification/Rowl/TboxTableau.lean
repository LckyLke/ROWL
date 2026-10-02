import Rowl.Hintikka

/-!
Concept satisfiability with respect to a TBox concept and role axioms, by a
tableau with subset blocking, proved total, sound and complete. The role axioms
are inclusions between named object properties and transitive named object
properties (the logic SH). Every acceptance yields a coherent Hintikka family
and therefore, when the listed inclusions include their compositions, a model
of the TBox concept and the role axioms with an instance of the input; any such
model, in any universe, forces acceptance. Termination: unblocked nodes add
pairwise distinct subsets of a finite closure to the history, so the history
length is bounded by 2 ^ |closure|. The closure contains, for every transitive
property, its universal restriction on every filler of a universal restriction.
-/
namespace Rowl.TboxTableau
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation classDenote)
open Rowl.Nnf (conceptDenote)
open Rowl.Tableau (toList weight total Holds existentials existentials_mem class_eq_iff property_eq_iff)
open Rowl.RoleBox (Below Respects transitives below_refl respects_below below_correct closed_of_empty
  respects_of_empty)
open Rowl.Hintikka (Sat SatAll ClashFree Witnessed Coherent sat_mono sat_literal universalItems roleFillers
  roleFillers_mem)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v

/-- The concepts of an item list, in order; a `Through` item stands for its
    universal restriction. -/
def itemsList : tbox.Items → List nnf.NnfConcept
  | .Empty => []
  | .Concept c next => c :: itemsList next
  | .Through t d next => .Forall t d :: itemsList next
/-- The item list holding the given concepts, in order. -/
def fromConcepts : List nnf.NnfConcept → tbox.Items
  | [] => .Empty
  | c :: rest => .Concept c (fromConcepts rest)
theorem itemsList_fromConcepts (cs : List nnf.NnfConcept) : itemsList (fromConcepts cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp [itemsList,fromConcepts,ih]

/-- The ancestor item sets, nearest first. -/
def historyList : tbox.History → List (List nnf.NnfConcept)
  | .Empty => []
  | .Entry label next => itemsList label :: historyList next

/-- All subconcepts of a concept, including the concept itself. -/
def subconcepts : nnf.NnfConcept → List nnf.NnfConcept
  | .And a b => .And a b :: (subconcepts a ++ subconcepts b)
  | .Or a b => .Or a b :: (subconcepts a ++ subconcepts b)
  | .Exists r c => .Exists r c :: subconcepts c
  | .Forall r c => .Forall r c :: subconcepts c
  | c => [c]
/-- A concept list closed under direct subconcepts. -/
def Closed (cl : List nnf.NnfConcept) : Prop :=
  (∀ a b, .And a b ∈ cl → a ∈ cl ∧ b ∈ cl) ∧ (∀ a b, .Or a b ∈ cl → a ∈ cl ∧ b ∈ cl) ∧
  (∀ r c, .Exists r c ∈ cl → c ∈ cl) ∧ (∀ r c, .Forall r c ∈ cl → c ∈ cl)

theorem subconcepts_self (c : nnf.NnfConcept) : c ∈ subconcepts c := by
  cases c <;> simp [subconcepts]
theorem subconcepts_closed (c : nnf.NnfConcept) : Closed (subconcepts c) := by
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ => refine ⟨?_,?_,?_,?_⟩ <;> intros <;> simp_all [subconcepts]
  | And a b iha ihb =>
    refine ⟨?_,?_,?_,?_⟩
    · intro x y member
      simp only [subconcepts,List.mem_cons,List.mem_append] at member ⊢
      rcases member with same | inA | inB
      · cases same; exact ⟨.inr (.inl (subconcepts_self _)),.inr (.inr (subconcepts_self _))⟩
      · have := iha.1 x y inA; exact ⟨.inr (.inl this.1),.inr (.inl this.2)⟩
      · have := ihb.1 x y inB; exact ⟨.inr (.inr this.1),.inr (.inr this.2)⟩
    · intro x y member
      simp only [subconcepts,List.mem_cons,List.mem_append] at member ⊢
      rcases member with same | inA | inB
      · cases same
      · have := iha.2.1 x y inA; exact ⟨.inr (.inl this.1),.inr (.inl this.2)⟩
      · have := ihb.2.1 x y inB; exact ⟨.inr (.inr this.1),.inr (.inr this.2)⟩
    · intro r x member
      simp only [subconcepts,List.mem_cons,List.mem_append] at member ⊢
      rcases member with same | inA | inB
      · cases same
      · exact .inr (.inl (iha.2.2.1 r x inA))
      · exact .inr (.inr (ihb.2.2.1 r x inB))
    · intro r x member
      simp only [subconcepts,List.mem_cons,List.mem_append] at member ⊢
      rcases member with same | inA | inB
      · cases same
      · exact .inr (.inl (iha.2.2.2 r x inA))
      · exact .inr (.inr (ihb.2.2.2 r x inB))
  | Or a b iha ihb =>
    refine ⟨?_,?_,?_,?_⟩
    · intro x y member
      simp only [subconcepts,List.mem_cons,List.mem_append] at member ⊢
      rcases member with same | inA | inB
      · cases same
      · have := iha.1 x y inA; exact ⟨.inr (.inl this.1),.inr (.inl this.2)⟩
      · have := ihb.1 x y inB; exact ⟨.inr (.inr this.1),.inr (.inr this.2)⟩
    · intro x y member
      simp only [subconcepts,List.mem_cons,List.mem_append] at member ⊢
      rcases member with same | inA | inB
      · cases same; exact ⟨.inr (.inl (subconcepts_self _)),.inr (.inr (subconcepts_self _))⟩
      · have := iha.2.1 x y inA; exact ⟨.inr (.inl this.1),.inr (.inl this.2)⟩
      · have := ihb.2.1 x y inB; exact ⟨.inr (.inr this.1),.inr (.inr this.2)⟩
    · intro r x member
      simp only [subconcepts,List.mem_cons,List.mem_append] at member ⊢
      rcases member with same | inA | inB
      · cases same
      · exact .inr (.inl (iha.2.2.1 r x inA))
      · exact .inr (.inr (ihb.2.2.1 r x inB))
    · intro r x member
      simp only [subconcepts,List.mem_cons,List.mem_append] at member ⊢
      rcases member with same | inA | inB
      · cases same
      · exact .inr (.inl (iha.2.2.2 r x inA))
      · exact .inr (.inr (ihb.2.2.2 r x inB))
  | Exists s c ih =>
    refine ⟨?_,?_,?_,?_⟩
    · intro x y member
      simp only [subconcepts,List.mem_cons] at member ⊢
      rcases member with same | inner
      · cases same
      · have := ih.1 x y inner; exact ⟨.inr this.1,.inr this.2⟩
    · intro x y member
      simp only [subconcepts,List.mem_cons] at member ⊢
      rcases member with same | inner
      · cases same
      · have := ih.2.1 x y inner; exact ⟨.inr this.1,.inr this.2⟩
    · intro r x member
      simp only [subconcepts,List.mem_cons] at member ⊢
      rcases member with same | inner
      · cases same; exact .inr (subconcepts_self _)
      · exact .inr (ih.2.2.1 r x inner)
    · intro r x member
      simp only [subconcepts,List.mem_cons] at member ⊢
      rcases member with same | inner
      · cases same
      · exact .inr (ih.2.2.2 r x inner)
  | Forall s c ih =>
    refine ⟨?_,?_,?_,?_⟩
    · intro x y member
      simp only [subconcepts,List.mem_cons] at member ⊢
      rcases member with same | inner
      · cases same
      · have := ih.1 x y inner; exact ⟨.inr this.1,.inr this.2⟩
    · intro x y member
      simp only [subconcepts,List.mem_cons] at member ⊢
      rcases member with same | inner
      · cases same
      · have := ih.2.1 x y inner; exact ⟨.inr this.1,.inr this.2⟩
    · intro r x member
      simp only [subconcepts,List.mem_cons] at member ⊢
      rcases member with same | inner
      · cases same
      · exact .inr (ih.2.2.1 r x inner)
    · intro r x member
      simp only [subconcepts,List.mem_cons] at member ⊢
      rcases member with same | inner
      · cases same; exact .inr (subconcepts_self _)
      · exact .inr (ih.2.2.2 r x inner)
theorem closed_append {a b : List nnf.NnfConcept} (ca : Closed a) (cb : Closed b) : Closed (a ++ b) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x y member
    rcases List.mem_append.mp member with inA | inB
    · have := ca.1 x y inA; exact ⟨List.mem_append_left _ this.1,List.mem_append_left _ this.2⟩
    · have := cb.1 x y inB; exact ⟨List.mem_append_right _ this.1,List.mem_append_right _ this.2⟩
  · intro x y member
    rcases List.mem_append.mp member with inA | inB
    · have := ca.2.1 x y inA; exact ⟨List.mem_append_left _ this.1,List.mem_append_left _ this.2⟩
    · have := cb.2.1 x y inB; exact ⟨List.mem_append_right _ this.1,List.mem_append_right _ this.2⟩
  · intro r x member
    rcases List.mem_append.mp member with inA | inB
    · exact List.mem_append_left _ (ca.2.2.1 r x inA)
    · exact List.mem_append_right _ (cb.2.2.1 r x inB)
  · intro r x member
    rcases List.mem_append.mp member with inA | inB
    · exact List.mem_append_left _ (ca.2.2.2 r x inA)
    · exact List.mem_append_right _ (cb.2.2.2 r x inB)

/-- Pairwise distinct subsets of a finite list are at most 2 ^ (its distinct size). -/
theorem history_bound (cl : List nnf.NnfConcept) (hs : List (List nnf.NnfConcept))
    (distinct : (hs.map List.toFinset).Nodup) (within : ∀ h ∈ hs, ∀ c ∈ h, c ∈ cl) :
    hs.length ≤ 2 ^ cl.toFinset.card := by
  have card : (hs.map List.toFinset).toFinset.card = hs.length := by
    rw [List.toFinset_card_of_nodup distinct,List.length_map]
  have sub : (hs.map List.toFinset).toFinset ⊆ cl.toFinset.powerset := by
    intro s member
    simp only [List.mem_toFinset,List.mem_map] at member
    obtain ⟨h,hmem,rfl⟩ := member
    rw [Finset.mem_powerset]
    intro c cmem
    rw [List.mem_toFinset] at cmem ⊢
    exact within h hmem c cmem
  have := Finset.card_le_card sub
  rw [Finset.card_powerset,card] at this
  exact this

/-- The filler of a universal restriction. -/
def forallFiller : nnf.NnfConcept → Option nnf.NnfConcept
  | .Forall _ d => some d
  | _ => none
/-- A closure together with `∀t.d` for every transitive property `t` and every
    filler `d` of a universal restriction in it. -/
def withThroughs (rb : role_box.RoleBox) (base : List nnf.NnfConcept) : List nnf.NnfConcept :=
  base ++ (transitives rb).flatMap (fun t => (base.filterMap forallFiller).map (fun d => .Forall t d))
/-- Every universal restriction of the list carries over to every transitive
    property. -/
def Throughs (rb : role_box.RoleBox) (cl : List nnf.NnfConcept) : Prop :=
  ∀ q d, .Forall q d ∈ cl → ∀ t ∈ transitives rb, .Forall t d ∈ cl

theorem withThroughs_mem (rb : role_box.RoleBox) (base : List nnf.NnfConcept) (c : nnf.NnfConcept) :
    c ∈ withThroughs rb base ↔ c ∈ base ∨ ∃ t ∈ transitives rb, ∃ q d, .Forall q d ∈ base ∧ c = .Forall t d := by
  simp only [withThroughs,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_filterMap]
  constructor
  · rintro (inBase | ⟨t,member,d,⟨e,eMember,filler⟩,rfl⟩)
    · exact .inl inBase
    · cases e with
      | Forall q d' =>
        simp only [forallFiller,Option.some.injEq] at filler
        subst filler
        exact .inr ⟨t,member,q,d',eMember,rfl⟩
      | _ => simp [forallFiller] at filler
  · rintro (inBase | ⟨t,member,q,d,eMember,rfl⟩)
    · exact .inl inBase
    · exact .inr ⟨t,member,d,⟨.Forall q d,eMember,rfl⟩,rfl⟩
theorem withThroughs_base {rb : role_box.RoleBox} {base : List nnf.NnfConcept} {c : nnf.NnfConcept}
    (member : c ∈ base) : c ∈ withThroughs rb base :=
  (withThroughs_mem rb base c).mpr (.inl member)
theorem withThroughs_closed (rb : role_box.RoleBox) {base : List nnf.NnfConcept} (closed : Closed base) :
    Closed (withThroughs rb base) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a b member
    rcases (withThroughs_mem rb base _).mp member with inBase | ⟨_,_,_,_,_,impossible⟩
    · exact ⟨withThroughs_base (closed.1 a b inBase).1,withThroughs_base (closed.1 a b inBase).2⟩
    · cases impossible
  · intro a b member
    rcases (withThroughs_mem rb base _).mp member with inBase | ⟨_,_,_,_,_,impossible⟩
    · exact ⟨withThroughs_base (closed.2.1 a b inBase).1,withThroughs_base (closed.2.1 a b inBase).2⟩
    · cases impossible
  · intro r c member
    rcases (withThroughs_mem rb base _).mp member with inBase | ⟨_,_,_,_,_,impossible⟩
    · exact withThroughs_base (closed.2.2.1 r c inBase)
    · cases impossible
  · intro r c member
    rcases (withThroughs_mem rb base _).mp member with inBase | ⟨t,_,q,d,inner,same⟩
    · exact withThroughs_base (closed.2.2.2 r c inBase)
    · cases same
      exact withThroughs_base (closed.2.2.2 q _ inner)
theorem withThroughs_throughs (rb : role_box.RoleBox) (base : List nnf.NnfConcept) :
    Throughs rb (withThroughs rb base) := by
  intro q d member t transitive
  rcases (withThroughs_mem rb base _).mp member with inBase | ⟨t',_,q',d',inner,same⟩
  · exact (withThroughs_mem rb base _).mpr (.inr ⟨t,transitive,q,d,inBase,rfl⟩)
  · cases same
    exact (withThroughs_mem rb base _).mpr (.inr ⟨t,transitive,q',d,inner,rfl⟩)

/-- Acceptance certificate at a node: a family coherent relative to the ancestors,
    and a set in the family or among the ancestors satisfying every current concept. -/
def Accepts (rb : role_box.RoleBox) (axioms : nnf.NnfConcept) (ancestors : List (List nnf.NnfConcept))
    (current : List nnf.NnfConcept) : Prop :=
  ∃ family, (∃ L, (L ∈ family ∨ L ∈ ancestors) ∧ SatAll L current) ∧ Coherent rb axioms family ancestors
/-- Some model of the role axioms, in the given universes, satisfies the TBox
    concept at every element and every current concept at one element. -/
def ModelSat (rb : role_box.RoleBox) (axioms : nnf.NnfConcept) (current : List nnf.NnfConcept) : Prop :=
  ∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (x : Object),
    Respects I rb ∧ (∀ y, conceptDenote I axioms y) ∧ Holds I x current
/-- The procedure's contract at a node. -/
def Decides (rb : role_box.RoleBox) (axioms : nnf.NnfConcept) (ancestors : List (List nnf.NnfConcept))
    (current : List nnf.NnfConcept) (result : Bool) : Prop :=
  (result = true → Accepts rb axioms ancestors current) ∧ (ModelSat.{u,v} rb axioms current → result = true)
/-- Invariants of every call: everything stays inside a closed finite closure
    that carries universal restrictions over to the transitive properties,
    ancestor item sets are pairwise distinct, the literal list holds only
    literals, and satisfying the current concepts entails the node's goals,
    which include the TBox concept. -/
structure Invariant (rb : role_box.RoleBox) (cl : List nnf.NnfConcept) (axioms : nnf.NnfConcept)
    (goals : List nnf.NnfConcept) (pending literals : tbox.Items) (history : tbox.History) : Prop where
  closed : Closed cl
  throughs : Throughs rb cl
  axiomsIn : axioms ∈ cl
  axiomsGoal : axioms ∈ goals
  pendingIn : ∀ c ∈ itemsList pending, c ∈ cl
  literalsIn : ∀ c ∈ itemsList literals, c ∈ cl
  historyIn : ∀ h ∈ historyList history, ∀ c ∈ h, c ∈ cl
  distinct : ((historyList history).map List.toFinset).Nodup
  literal : ∀ c ∈ itemsList literals, Rowl.Tableau.Literal c
  covers : ∀ L, SatAll L (itemsList pending ++ itemsList literals) → SatAll L goals

theorem duplicate_correct (list : tbox.Items) : tbox.duplicate list = .ok (list,list) := by
  induction list with
  | Empty => rw [tbox.duplicate]
  | Concept c next ih => rw [tbox.duplicate]; simp [ih]
  | Through t d next ih => rw [tbox.duplicate]; simp [ih]
theorem duplicate_history_correct (history : tbox.History) :
    tbox.duplicate_history history = .ok (history,history) := by
  induction history with
  | Empty => rw [tbox.duplicate_history]
  | Entry label next ih => rw [tbox.duplicate_history]; simp [duplicate_correct,ih]
theorem same_concept_correct (a b : nnf.NnfConcept) : tbox.same_concept a b = .ok (decide (a = b)) := by
  induction a generalizing b with
  | Top => cases b <;> rw [tbox.same_concept] <;> simp
  | Bottom => cases b <;> rw [tbox.same_concept] <;> simp
  | Atom k =>
    cases b with
    | Atom k' =>
      rw [tbox.same_concept]
      by_cases equal : k = k'
      · subst equal; simp [Rowl.Symbols.same_spelling_total_correct]
      · have different : ¬ k.iri.spelling.val = k'.iri.spelling.val := fun h => equal ((class_eq_iff k k').mpr h)
        simp [Rowl.Symbols.same_spelling_total_correct,different,equal]
    | _ => rw [tbox.same_concept]; simp
  | NotAtom k =>
    cases b with
    | NotAtom k' =>
      rw [tbox.same_concept]
      by_cases equal : k = k'
      · subst equal; simp [Rowl.Symbols.same_spelling_total_correct]
      · have different : ¬ k.iri.spelling.val = k'.iri.spelling.val := fun h => equal ((class_eq_iff k k').mpr h)
        simp [Rowl.Symbols.same_spelling_total_correct,different,equal]
    | _ => rw [tbox.same_concept]; simp
  | And a1 b1 ih1 ih2 =>
    cases b with
    | And a2 b2 =>
      rw [tbox.same_concept]
      by_cases first : a1 = a2
      · subst first; simp [ih1,ih2]
      · simp [ih1,ih2,first]
    | _ => rw [tbox.same_concept]; simp
  | Or a1 b1 ih1 ih2 =>
    cases b with
    | Or a2 b2 =>
      rw [tbox.same_concept]
      by_cases first : a1 = a2
      · subst first; simp [ih1,ih2]
      · simp [ih1,ih2,first]
    | _ => rw [tbox.same_concept]; simp
  | Exists r1 c1 ih =>
    cases b with
    | Exists r2 c2 =>
      rw [tbox.same_concept]
      by_cases role : r1 = r2
      · subst role; simp [Rowl.Symbols.same_spelling_total_correct,ih]
      · have different : ¬ r1.iri.spelling.val = r2.iri.spelling.val := fun h => role ((property_eq_iff r1 r2).mpr h)
        simp [Rowl.Symbols.same_spelling_total_correct,different,role]
    | _ => rw [tbox.same_concept]; simp
  | Forall r1 c1 ih =>
    cases b with
    | Forall r2 c2 =>
      rw [tbox.same_concept]
      by_cases role : r1 = r2
      · subst role; simp [Rowl.Symbols.same_spelling_total_correct,ih]
      · have different : ¬ r1.iri.spelling.val = r2.iri.spelling.val := fun h => role ((property_eq_iff r1 r2).mpr h)
        simp [Rowl.Symbols.same_spelling_total_correct,different,role]
    | _ => rw [tbox.same_concept]; simp
theorem contains_atom_correct (list : tbox.Items) (k : Class) :
    tbox.contains_atom list k = .ok (decide (.Atom k ∈ itemsList list),list) := by
  induction list with
  | Empty => rw [tbox.contains_atom.eq_def]; simp [itemsList]
  | Concept c next ih =>
    rw [tbox.contains_atom.eq_def]
    cases c with
    | Atom other =>
      have same : (other.iri.spelling.val = k.iri.spelling.val) ↔ k = other := by
        rw [class_eq_iff]; exact eq_comm
      by_cases equal : k = other
      · subst equal; simp [ih,itemsList,Rowl.Symbols.same_spelling_total_correct]
      · have different : ¬ other.iri.spelling.val = k.iri.spelling.val := fun h => equal (same.mp h)
        simp [ih,itemsList,Rowl.Symbols.same_spelling_total_correct,different,equal]
    | _ => simp [ih,itemsList]
  | Through t d next ih => rw [tbox.contains_atom.eq_def]; simp [ih,itemsList]
theorem has_clash_correct (all cursor : tbox.Items) :
    tbox.has_clash all cursor =
      .ok (decide (∃ k, .NotAtom k ∈ itemsList cursor ∧ .Atom k ∈ itemsList all),all) := by
  induction cursor with
  | Empty => rw [tbox.has_clash.eq_def]; simp [itemsList]
  | Concept c next ih =>
    rw [tbox.has_clash.eq_def]
    cases c with
    | NotAtom k =>
      by_cases present : .Atom k ∈ itemsList all
      · simp [contains_atom_correct,ih,itemsList,present]
      · simp [contains_atom_correct,ih,itemsList,present]
    | _ => simp [ih,itemsList]
  | Through t d next ih => rw [tbox.has_clash.eq_def]; simp [ih,itemsList]
theorem universal_is_correct (role : ObjectProperty) (filler concept : nnf.NnfConcept) :
    tbox.universal_is role filler concept = .ok (decide (concept = .Forall role filler)) := by
  rw [tbox.universal_is.eq_def]
  cases concept with
  | Forall other inner =>
    by_cases sameRole : role = other
    · subst sameRole
      by_cases sameFiller : filler = inner
      · subst sameFiller; simp [Rowl.Symbols.same_spelling_total_correct,same_concept_correct]
      · have sameFiller' : ¬ inner = filler := fun h => sameFiller h.symm
        simp [Rowl.Symbols.same_spelling_total_correct,same_concept_correct,sameFiller,sameFiller']
    · have different : ¬ role.iri.spelling.val = other.iri.spelling.val :=
        fun h => sameRole ((property_eq_iff _ _).mpr h)
      have sameRole' : ¬ other = role := fun h => sameRole h.symm
      simp [Rowl.Symbols.same_spelling_total_correct,different,sameRole']
  | _ => simp
theorem contains_concept_correct (list : tbox.Items) (sought : nnf.NnfConcept) :
    tbox.contains_concept list sought = .ok (decide (sought ∈ itemsList list),list) := by
  induction list with
  | Empty => rw [tbox.contains_concept]; simp [itemsList]
  | Concept c next ih =>
    rw [tbox.contains_concept]
    by_cases same : c = sought
    · subst same; simp [same_concept_correct,ih,itemsList]
    · have different : ¬ sought = c := fun h => same h.symm
      simp [same_concept_correct,ih,itemsList,same,different]
  | Through t d next ih =>
    rw [tbox.contains_concept]
    by_cases same : sought = .Forall t d
    · subst same; simp [universal_is_correct,ih,itemsList]
    · simp [universal_is_correct,ih,itemsList,same]
theorem contains_universal_correct (list : tbox.Items) (role : ObjectProperty) (filler : nnf.NnfConcept) :
    tbox.contains_universal list role filler = .ok (decide (.Forall role filler ∈ itemsList list),list) := by
  induction list with
  | Empty => rw [tbox.contains_universal]; simp [itemsList]
  | Concept c next ih =>
    rw [tbox.contains_universal]
    by_cases same : c = .Forall role filler
    · subst same; simp [universal_is_correct,ih,itemsList]
    · have different : ¬ .Forall role filler = c := fun h => same h.symm
      simp [universal_is_correct,ih,itemsList,same,different]
  | Through t d next ih =>
    rw [tbox.contains_universal]
    by_cases sameRole : role = t
    · subst sameRole
      by_cases sameFiller : filler = d
      · subst sameFiller; simp [Rowl.Symbols.same_spelling_total_correct,same_concept_correct,ih,itemsList]
      · simp [Rowl.Symbols.same_spelling_total_correct,same_concept_correct,ih,itemsList,sameFiller]
    · have different : ¬ role.iri.spelling.val = t.iri.spelling.val :=
        fun h => sameRole ((property_eq_iff _ _).mpr h)
      simp [Rowl.Symbols.same_spelling_total_correct,ih,itemsList,different,sameRole]
theorem subset_correct (small large : tbox.Items) :
    tbox.subset small large = .ok (decide (∀ c ∈ itemsList small, c ∈ itemsList large),small,large) := by
  induction small with
  | Empty => rw [tbox.subset]; simp [itemsList]
  | Concept c next ih =>
    rw [tbox.subset]
    by_cases present : c ∈ itemsList large <;> simp [contains_concept_correct,ih,itemsList,present]
  | Through t d next ih =>
    rw [tbox.subset]
    by_cases present : nnf.NnfConcept.Forall t d ∈ itemsList large <;>
      simp [contains_universal_correct,ih,itemsList,present]
theorem blocked_correct (label : tbox.Items) (history : tbox.History) :
    tbox.blocked label history =
      .ok (decide (∃ h ∈ historyList history, ∀ c ∈ itemsList label, c ∈ h),label,history) := by
  induction history with
  | Empty => rw [tbox.blocked]; simp [historyList]
  | Entry ancestor next ih =>
    rw [tbox.blocked]
    by_cases inside : ∀ c ∈ itemsList label, c ∈ itemsList ancestor
    · simp [subset_correct,ih,historyList,eq_true inside]
    · simp [subset_correct,ih,historyList,inside]

/-- The transitive properties from `index` that include `sub` and are included
    in `sup`, as their universal restrictions on the filler, in front of `tail`. -/
theorem transitive_from_correct (rb : role_box.RoleBox) (index : Usize) (sub sup : ObjectProperty)
    (filler : nnf.NnfConcept) (tail : tbox.Items) :
    ∃ result, tbox.transitive_from rb index sub sup filler tail = .ok result ∧
      itemsList result = ((rb.transitive.val.drop index.val).filter
        (fun t => decide (Below rb sub t ∧ Below rb t sup))).map (fun t => nnf.NnfConcept.Forall t filler) ++
        itemsList tail := by
  rw [tbox.transitive_from]
  by_cases more : index.val < rb.transitive.val.length
  · have lookup : rb.transitive.index_usize index = .ok rb.transitive.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : rb.transitive.val.drop index.val =
        rb.transitive.val[index.val] :: rb.transitive.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨rest,restRun,restList⟩ := transitive_from_correct rb index' sub sup filler tail
    rw [nextIndex] at restList
    rw [split]
    by_cases first : Below rb sub rb.transitive.val[index.val]
    · by_cases second : Below rb rb.transitive.val[index.val] sup
      · refine ⟨.Through rb.transitive.val[index.val] filler rest,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,advance,restRun,below_correct,first,second,decide_true]
        · rw [List.filter_cons_of_pos (by simp [first,second]),List.map_cons,List.cons_append,← restList]
          rfl
      · refine ⟨rest,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,advance,restRun,below_correct,first,second,decide_true,decide_false,
            Bool.false_eq_true]
        · rw [List.filter_cons_of_neg (by simp [second]),restList]
    · refine ⟨rest,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,advance,restRun,below_correct,first,decide_false,Bool.false_eq_true]
      · rw [List.filter_cons_of_neg (by simp [first]),restList]
  · have empty : rb.transitive.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨tail,?_,?_⟩
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more]
    · simp [empty]
termination_by rb.transitive.val.length - index.val
decreasing_by omega

/-- What one universal restriction requires along `sub`, in front of `tail`. -/
theorem universal_correct (rb : role_box.RoleBox) (sub sup : ObjectProperty) (filler : nnf.NnfConcept)
    (tail : tbox.Items) :
    ∃ result, tbox.universal rb sub sup filler tail = .ok result ∧
      itemsList result = universalItems rb sub sup filler ++ itemsList tail := by
  rw [tbox.universal,below_correct]
  by_cases below : Below rb sub sup
  · obtain ⟨rest,run,list⟩ := transitive_from_correct rb 0#usize sub sup filler tail
    refine ⟨.Concept filler rest,by simp [below,run],?_⟩
    simp [itemsList,list,universalItems,below,transitives]
  · exact ⟨tail,by simp [below],by simp [universalItems,below]⟩
/-- What the universal restrictions of a list require along a role; the list is
    handed back. -/
theorem role_fillers_correct (list : tbox.Items) (role : ObjectProperty) (rb : role_box.RoleBox) :
    ∃ fillers, tbox.role_fillers list role rb = .ok (fillers,list) ∧
      itemsList fillers = roleFillers rb role (itemsList list) := by
  induction list with
  | Empty => exact ⟨.Empty,by rw [tbox.role_fillers],by simp [itemsList,roleFillers]⟩
  | Concept c next ih =>
    obtain ⟨fillers,run,list⟩ := ih
    rw [tbox.role_fillers]
    cases c with
    | Forall q d =>
      obtain ⟨result,universalRun,universalList⟩ := universal_correct rb role q d fillers
      exact ⟨result,by simp [run,universalRun],by simp [itemsList,roleFillers,universalList,list]⟩
    | _ => exact ⟨fillers,by simp [run],by simp [itemsList,roleFillers,list]⟩
  | Through t d next ih =>
    obtain ⟨fillers,run,list⟩ := ih
    rw [tbox.role_fillers]
    obtain ⟨result,universalRun,universalList⟩ := universal_correct rb role t d fillers
    exact ⟨result,by simp [run,universalRun],by simp [itemsList,roleFillers,universalList,list]⟩

/-- Every existential in `cursor` is checked through its successor call. -/
private theorem existentials_hold_correct (all cursor : tbox.Items) (history : tbox.History)
    (axioms : nnf.NnfConcept) (rb : role_box.RoleBox)
    (child : ∀ r c, .Exists r c ∈ itemsList cursor → ∀ F, tbox.role_fillers all r rb = .ok (F,all) →
      ∃ result, tbox.expand (.Concept c (.Concept axioms F)) .Empty history axioms rb = .ok result) :
    ∃ result, tbox.existentials_hold all cursor history axioms rb = .ok (result,all,history) ∧
      (result = true ↔ ∀ r c, .Exists r c ∈ itemsList cursor → ∀ F, tbox.role_fillers all r rb = .ok (F,all) →
        tbox.expand (.Concept c (.Concept axioms F)) .Empty history axioms rb = .ok true) := by
  induction cursor with
  | Empty => exact ⟨true,by rw [tbox.existentials_hold.eq_def],by simp [itemsList]⟩
  | Concept c next ih =>
    obtain ⟨later,laterRead,laterIff⟩ := ih (fun r d member => child r d (by simp [itemsList,member]))
    rw [tbox.existentials_hold.eq_def]
    cases c with
    | Exists r d =>
      obtain ⟨F,fillersRun,_⟩ := role_fillers_correct all r rb
      obtain ⟨here,hereRead⟩ := child r d (by simp [itemsList]) F fillersRun
      refine ⟨here && later,?_,?_⟩
      · cases here <;> simp [fillersRun,duplicate_history_correct,hereRead,laterRead]
      · rw [Bool.and_eq_true,laterIff]
        constructor
        · rintro ⟨yes,rest⟩ r' d' member F' run'
          simp only [itemsList,List.mem_cons] at member
          rcases member with same | later'
          · cases same
            have equal := Result.ok_injective (run'.symm.trans fillersRun)
            simp only [Prod.mk.injEq] at equal
            rw [equal.1,hereRead,yes]
          · exact rest r' d' later' F' run'
        · intro all'
          refine ⟨?_,fun r' d' member => all' r' d' (by simp [itemsList,member])⟩
          have accepted := all' r d (by simp [itemsList]) F fillersRun
          rw [hereRead] at accepted
          exact Result.ok_injective accepted
    | _ =>
      refine ⟨later,by simpa using laterRead,?_⟩
      rw [laterIff]
      simp [itemsList]
  | Through t d next ih =>
    obtain ⟨later,laterRead,laterIff⟩ := ih (fun r d' member => child r d' (by simp [itemsList,member]))
    rw [tbox.existentials_hold.eq_def]
    refine ⟨later,by simpa using laterRead,?_⟩
    rw [laterIff]
    simp [itemsList]

private theorem witnessed_mono {rb : role_box.RoleBox} {axioms : nnf.NnfConcept}
    {pool pool' : List (List nnf.NnfConcept)} {L : List nnf.NnfConcept} (sub : ∀ X ∈ pool, X ∈ pool')
    (witnessed : Witnessed rb axioms pool L) : Witnessed rb axioms pool' L := by
  intro r c member
  obtain ⟨L',inPool,rest⟩ := witnessed r c member
  exact ⟨L',sub L' inPool,rest⟩
private theorem accepts_of_implies {rb : role_box.RoleBox} {axioms : nnf.NnfConcept}
    {ancestors : List (List nnf.NnfConcept)} {current current' : List nnf.NnfConcept}
    (implies : ∀ L, SatAll L current' → SatAll L current)
    (accepted : Accepts rb axioms ancestors current') : Accepts rb axioms ancestors current := by
  obtain ⟨family,⟨L,member,sat⟩,coherent⟩ := accepted
  exact ⟨family,⟨L,member,implies L sat⟩,coherent⟩
private theorem model_of_implies {rb : role_box.RoleBox} {axioms : nnf.NnfConcept}
    {current current' : List nnf.NnfConcept}
    (implies : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (x : Object),
      Holds I x current → Holds I x current')
    (model : ModelSat.{u,v} rb axioms current) : ModelSat.{u,v} rb axioms current' := by
  obtain ⟨Object,Value,I,x,respects,everywhere,holds⟩ := model
  exact ⟨Object,Value,I,x,respects,everywhere,implies Object Value I x holds⟩

private theorem coherent_append {rb : role_box.RoleBox} {axioms : nnf.NnfConcept}
    {F G ancestors : List (List nnf.NnfConcept)}
    (cf : Coherent rb axioms F ancestors) (cg : Coherent rb axioms G ancestors) :
    Coherent rb axioms (F ++ G) ancestors := by
  intro L member
  rcases List.mem_append.mp member with inF | inG
  · obtain ⟨clashFree,axiomsSat,witnessed⟩ := cf L inF
    refine ⟨clashFree,axiomsSat,witnessed_mono ?_ witnessed⟩
    intro X xmem
    rcases List.mem_append.mp xmem with own | old
    · exact List.mem_append_left _ (List.mem_append_left _ own)
    · exact List.mem_append_right _ old
  · obtain ⟨clashFree,axiomsSat,witnessed⟩ := cg L inG
    refine ⟨clashFree,axiomsSat,witnessed_mono ?_ witnessed⟩
    intro X xmem
    rcases List.mem_append.mp xmem with own | old
    · exact List.mem_append_left _ (List.mem_append_right _ own)
    · exact List.mem_append_right _ old
/-- Certificates for several goals below the same ancestors merge into one family. -/
private theorem combine {rb : role_box.RoleBox} {axioms : nnf.NnfConcept} {ancestors : List (List nnf.NnfConcept)}
    (wanted : List (List nnf.NnfConcept)) (each : ∀ goal ∈ wanted, Accepts rb axioms ancestors goal) :
    ∃ family, (∀ goal ∈ wanted, ∃ L, (L ∈ family ∨ L ∈ ancestors) ∧ SatAll L goal) ∧
      Coherent rb axioms family ancestors := by
  induction wanted with
  | nil => exact ⟨[],by simp,by simp [Coherent]⟩
  | cons goal rest ih =>
    obtain ⟨F,⟨L,located,sat⟩,cf⟩ := each goal (by simp)
    obtain ⟨G,covered,cg⟩ := ih (fun g member => each g (by simp [member]))
    refine ⟨F ++ G,?_,coherent_append cf cg⟩
    intro g member
    rcases List.mem_cons.mp member with rfl | later
    · refine ⟨L,?_,sat⟩
      rcases located with own | old
      · exact .inl (List.mem_append_left _ own)
      · exact .inr old
    · obtain ⟨L',located',sat'⟩ := covered g later
      refine ⟨L',?_,sat'⟩
      rcases located' with own | old
      · exact .inl (List.mem_append_right _ own)
      · exact .inr old

/-- Moving a literal from the pending list to the literal list keeps the invariants. -/
private theorem move {rb : role_box.RoleBox} {cl : List nnf.NnfConcept} {axioms : nnf.NnfConcept}
    {goals : List nnf.NnfConcept} {c : nnf.NnfConcept} {pending next literals literals' : tbox.Items}
    {history : tbox.History} (inv : Invariant rb cl axioms goals pending literals history)
    (isLiteral : Rowl.Tableau.Literal c) (pendingIs : itemsList pending = c :: itemsList next)
    (literalsIs : itemsList literals' = c :: itemsList literals) :
    Invariant rb cl axioms goals next literals' history :=
  { closed := inv.closed
    throughs := inv.throughs
    axiomsIn := inv.axiomsIn
    axiomsGoal := inv.axiomsGoal
    pendingIn := fun d member => inv.pendingIn d (by rw [pendingIs]; exact List.mem_cons_of_mem _ member)
    literalsIn := by
      intro d member
      rw [literalsIs] at member
      rcases List.mem_cons.mp member with rfl | rest
      · exact inv.pendingIn _ (by rw [pendingIs]; exact List.mem_cons_self ..)
      · exact inv.literalsIn d rest
    historyIn := inv.historyIn
    distinct := inv.distinct
    literal := by
      intro d member
      rw [literalsIs] at member
      rcases List.mem_cons.mp member with rfl | rest
      · exact isLiteral
      · exact inv.literal d rest
    covers := fun L sat => inv.covers L (fun d member => sat d (by
      rw [pendingIs] at member
      rw [literalsIs]
      simp only [List.cons_append,List.mem_cons,List.mem_append] at member ⊢
      tauto)) }
/-- Moving a literal keeps the same concepts, so the same contract. -/
private theorem moved {rb : role_box.RoleBox} {axioms : nnf.NnfConcept} {ancestors : List (List nnf.NnfConcept)}
    {c : nnf.NnfConcept} {pending next literals literals' : tbox.Items} {result : Bool}
    (pendingIs : itemsList pending = c :: itemsList next) (literalsIs : itemsList literals' = c :: itemsList literals)
    (decides : Decides.{u,v} rb axioms ancestors (itemsList next ++ itemsList literals') result) :
    Decides.{u,v} rb axioms ancestors (itemsList pending ++ itemsList literals) result := by
  have same : ∀ d, d ∈ itemsList pending ++ itemsList literals ↔ d ∈ itemsList next ++ itemsList literals' := by
    intro d; rw [pendingIs,literalsIs]; simp; tauto
  exact ⟨fun accepted => accepts_of_implies (fun L sat d member => sat d ((same d).mp member)) (decides.1 accepted),
    fun model => decides.2 (model_of_implies (fun _ _ I x holds d member => holds d ((same d).mpr member)) model)⟩

/-- The actual procedure terminates on every call satisfying the invariants and
    decides exactly whether the current concepts are satisfiable together with the
    TBox concept and the role axioms, relative to the ancestors used for blocking. -/
theorem expand_correct (rb : role_box.RoleBox) (cl : List nnf.NnfConcept) (axioms : nnf.NnfConcept)
    (goals : List nnf.NnfConcept) (pending literals : tbox.Items) (history : tbox.History) :
    Invariant rb cl axioms goals pending literals history →
    ∃ result, tbox.expand pending literals history axioms rb = .ok result ∧
      Decides.{u,v} rb axioms (historyList history) (itemsList pending ++ itemsList literals) result := by
  intro inv
  cases pending with
  | Empty =>
    rw [tbox.expand.eq_def]
    simp only [duplicate_correct,has_clash_correct,bind_ok,uncurry_apply_pair]
    by_cases clash : ∃ k, .NotAtom k ∈ itemsList literals ∧ .Atom k ∈ itemsList literals
    · refine ⟨false,by simp [clash],?_⟩
      constructor
      · intro impossible; cases impossible
      · rintro ⟨Object,Value,I,x,_,_,holds⟩
        obtain ⟨k,negative,positive⟩ := clash
        exact absurd (holds (.Atom k) (by simp [itemsList,positive]))
          (holds (.NotAtom k) (by simp [itemsList,negative]))
    · by_cases blockedHere : ∃ h ∈ historyList history, ∀ d ∈ itemsList literals, d ∈ h
      · refine ⟨true,by simp [clash,blocked_correct,blockedHere],?_⟩
        constructor
        · intro _
          obtain ⟨h,hmem,sub⟩ := blockedHere
          refine ⟨[],⟨h,.inr hmem,?_⟩,by simp [Coherent]⟩
          intro c cmem
          simp only [itemsList,List.nil_append] at cmem
          exact (sat_literal h c (inv.literal c cmem)).mpr (sub c cmem)
        · intro _; rfl
      · have extendedIn : ∀ h ∈ itemsList literals :: historyList history, ∀ c ∈ h, c ∈ cl := by
          intro h member c cmem
          rcases List.mem_cons.mp member with rfl | old
          · exact inv.literalsIn c cmem
          · exact inv.historyIn h old c cmem
        have extendedDistinct : ((itemsList literals :: historyList history).map List.toFinset).Nodup := by
          rw [List.map_cons,List.nodup_cons]
          refine ⟨?_,inv.distinct⟩
          intro member
          simp only [List.mem_map] at member
          obtain ⟨h,hmem,same⟩ := member
          apply blockedHere
          refine ⟨h,hmem,fun d dmem => ?_⟩
          have : d ∈ (itemsList literals).toFinset := List.mem_toFinset.mpr dmem
          rw [← same] at this
          exact List.mem_toFinset.mp this
        have bound := history_bound cl _ extendedDistinct extendedIn
        have successors : ∀ r c, .Exists r c ∈ itemsList literals → ∀ F,
            tbox.role_fillers literals r rb = .ok (F,literals) → ∃ result,
            tbox.expand (.Concept c (.Concept axioms F)) .Empty (.Entry literals history) axioms rb = .ok result ∧
            Decides.{u,v} rb axioms (itemsList literals :: historyList history)
              (c :: axioms :: roleFillers rb r (itemsList literals)) result := by
          intro r c member F run
          obtain ⟨F',run',list'⟩ := role_fillers_correct literals r rb
          have equal := Result.ok_injective (run.symm.trans run')
          simp only [Prod.mk.injEq] at equal
          obtain ⟨rfl,-⟩ := equal
          have cIn : c ∈ cl := inv.closed.2.2.1 r c (inv.literalsIn _ member)
          obtain ⟨result,executed,decides⟩ := expand_correct rb cl axioms
            (c :: axioms :: roleFillers rb r (itemsList literals))
            (.Concept c (.Concept axioms F)) .Empty (.Entry literals history)
            { closed := inv.closed, throughs := inv.throughs, axiomsIn := inv.axiomsIn, axiomsGoal := by simp,
              pendingIn := by
                intro d dmem
                simp only [itemsList,list',List.mem_cons] at dmem
                rcases dmem with rfl | rfl | filler
                · exact cIn
                · exact inv.axiomsIn
                · obtain ⟨q,e,universal,_,kind⟩ := (roleFillers_mem rb r _ d).mp filler
                  have universalIn := inv.literalsIn _ universal
                  rcases kind with rfl | ⟨t,transitive,_,_,rfl⟩
                  · exact inv.closed.2.2.2 q d universalIn
                  · exact inv.throughs q e universalIn t transitive
              literalsIn := by simp [itemsList], historyIn := extendedIn, distinct := extendedDistinct,
              literal := by simp [itemsList],
              covers := by intro L sat; simpa [itemsList,list'] using sat }
          exact ⟨result,executed,by simpa [itemsList,list',historyList] using decides⟩
        obtain ⟨result,executed,iff⟩ := existentials_hold_correct literals literals (.Entry literals history) axioms rb
          (fun r c member F run => (successors r c member F run).imp fun _ h => h.1)
        refine ⟨result,by simp [clash,blocked_correct,blockedHere,executed],?_⟩
        constructor
        · intro accepted
          have all := iff.mp accepted
          have each : ∀ goal ∈ (existentials (itemsList literals)).map
              (fun rc => rc.2 :: axioms :: roleFillers rb rc.1 (itemsList literals)),
              Accepts rb axioms (itemsList literals :: historyList history) goal := by
            intro goal member
            obtain ⟨⟨r,c⟩,rcMember,rfl⟩ := List.mem_map.mp member
            have exists' := (existentials_mem _ r c).mp rcMember
            obtain ⟨F,run,_⟩ := role_fillers_correct literals r rb
            obtain ⟨answer,answerRun,decides⟩ := successors r c exists' F run
            have yes := all r c exists' F run
            rw [answerRun] at yes
            exact decides.1 (Result.ok_injective yes)
          obtain ⟨F,covered,coherent⟩ := combine _ each
          have literalSat : SatAll (itemsList literals) (itemsList tbox.Items.Empty ++ itemsList literals) := by
            intro c cmem
            simp only [itemsList,List.nil_append] at cmem
            exact (sat_literal _ c (inv.literal c cmem)).mpr cmem
          refine ⟨itemsList literals :: F,⟨itemsList literals,.inl (List.mem_cons_self ..),literalSat⟩,?_⟩
          intro X member
          rcases List.mem_cons.mp member with rfl | deeper
          · refine ⟨fun k negative positive => clash ⟨k,negative,positive⟩,
              inv.covers _ literalSat axioms inv.axiomsGoal,?_⟩
            intro r c exists'
            have goalIn : c :: axioms :: roleFillers rb r (itemsList literals) ∈ (existentials (itemsList literals)).map
                (fun rc => rc.2 :: axioms :: roleFillers rb rc.1 (itemsList literals)) :=
              List.mem_map.mpr ⟨(r,c),(existentials_mem _ r c).mpr exists',rfl⟩
            obtain ⟨L,located,sat⟩ := covered _ goalIn
            refine ⟨L,?_,sat axioms (by simp),sat c (by simp),fun x xmem =>
              sat x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ xmem))⟩
            rcases located with own | ancestral
            · exact List.mem_append_left _ (List.mem_cons_of_mem _ own)
            · rcases List.mem_cons.mp ancestral with rfl | old
              · exact List.mem_append_left _ (List.mem_cons_self ..)
              · exact List.mem_append_right _ old
          · obtain ⟨clashFree,axiomsSat,witnessed⟩ := coherent X deeper
            refine ⟨clashFree,axiomsSat,witnessed_mono ?_ witnessed⟩
            intro Y ymem
            rcases List.mem_append.mp ymem with own | ancestral
            · exact List.mem_append_left _ (List.mem_cons_of_mem _ own)
            · rcases List.mem_cons.mp ancestral with rfl | old
              · exact List.mem_append_left _ (List.mem_cons_self ..)
              · exact List.mem_append_right _ old
        · rintro ⟨Object,Value,I,x,respects,everywhere,holds⟩
          simp only [itemsList,List.nil_append] at holds
          apply iff.mpr
          intro r c member F run
          obtain ⟨answer,answerRun,decides⟩ := successors r c member F run
          rw [answerRun]
          obtain ⟨y,edge,inner⟩ := holds (.Exists r c) member
          have model : ModelSat.{u,v} rb axioms (c :: axioms :: roleFillers rb r (itemsList literals)) := by
            refine ⟨Object,Value,I,y,respects,everywhere,?_⟩
            intro d dmem
            simp only [List.mem_cons] at dmem
            rcases dmem with rfl | rfl | filler
            · exact inner
            · exact everywhere y
            · obtain ⟨q,e,universal,below,kind⟩ := (roleFillers_mem rb r _ d).mp filler
              have universal' := holds (.Forall q e) universal
              rcases kind with rfl | ⟨t,transitive,first,second,rfl⟩
              · exact universal' y (respects_below respects below edge)
              · intro z next
                exact universal' z (respects_below respects second
                  (respects.2 t transitive x y z (respects_below respects first edge) next))
          rw [decides.2 model]
  | Concept c next =>
    rw [tbox.expand.eq_def]
    cases c with
    | Top =>
      obtain ⟨result,executed,decides⟩ := expand_correct rb cl axioms goals next literals history
        { inv with
          pendingIn := fun d member => inv.pendingIn d (by simp [itemsList,member])
          covers := fun L sat => inv.covers L (by
            intro d member
            simp only [itemsList,List.cons_append,List.mem_cons] at member
            rcases member with rfl | rest
            · exact trivial
            · exact sat d rest) }
      refine ⟨result,by simpa using executed,?_,?_⟩
      · intro accepted
        exact accepts_of_implies (fun L sat d member => by
          simp only [itemsList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rest
          · exact trivial
          · exact sat d rest) (decides.1 accepted)
      · intro model
        exact decides.2 (model_of_implies (fun _ _ I x holds d member => holds d (by
          simp only [itemsList,List.cons_append,List.mem_cons]; exact .inr member)) model)
    | Bottom =>
      refine ⟨false,rfl,?_⟩
      constructor
      · intro impossible; cases impossible
      · rintro ⟨Object,Value,I,x,_,_,holds⟩
        exact absurd (holds .Bottom (by simp [itemsList])) (by simp [conceptDenote])
    | And a b =>
      have abIn := inv.closed.1 a b (inv.pendingIn _ (by simp [itemsList]))
      obtain ⟨result,executed,decides⟩ := expand_correct rb cl axioms goals (.Concept a (.Concept b next))
        literals history
        { inv with
          pendingIn := by
            intro d member
            simp only [itemsList,List.mem_cons] at member
            rcases member with rfl | rfl | rest
            · exact abIn.1
            · exact abIn.2
            · exact inv.pendingIn d (by simp [itemsList,rest])
          covers := fun L sat => inv.covers L (by
            intro d member
            simp only [itemsList,List.cons_append,List.mem_cons] at member
            rcases member with rfl | rest
            · exact ⟨sat a (by simp [itemsList]),sat b (by simp [itemsList])⟩
            · exact sat d (by simp [itemsList,rest])) }
      refine ⟨result,by simpa using executed,?_,?_⟩
      · intro accepted
        exact accepts_of_implies (fun L sat d member => by
          simp only [itemsList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rest
          · exact ⟨sat a (by simp [itemsList]),sat b (by simp [itemsList])⟩
          · exact sat d (by simp [itemsList,rest])) (decides.1 accepted)
      · intro model
        exact decides.2 (model_of_implies (fun _ _ I x holds d member => by
          have conj := holds (.And a b) (by simp [itemsList])
          simp only [itemsList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rfl | rest
          · exact conj.1
          · exact conj.2
          · exact holds d (by simp [itemsList,rest])) model)
    | Or a b =>
      have abIn := inv.closed.2.1 a b (inv.pendingIn _ (by simp [itemsList]))
      obtain ⟨left,leftRun,leftDecides⟩ := expand_correct rb cl axioms goals (.Concept a next) literals history
        { inv with
          pendingIn := by
            intro d member
            simp only [itemsList,List.mem_cons] at member
            rcases member with rfl | rest
            · exact abIn.1
            · exact inv.pendingIn d (by simp [itemsList,rest])
          covers := fun L sat => inv.covers L (by
            intro d member
            simp only [itemsList,List.cons_append,List.mem_cons] at member
            rcases member with rfl | rest
            · exact .inl (sat a (by simp [itemsList]))
            · exact sat d (by simp [itemsList,rest])) }
      obtain ⟨right,rightRun,rightDecides⟩ := expand_correct rb cl axioms goals (.Concept b next) literals history
        { inv with
          pendingIn := by
            intro d member
            simp only [itemsList,List.mem_cons] at member
            rcases member with rfl | rest
            · exact abIn.2
            · exact inv.pendingIn d (by simp [itemsList,rest])
          covers := fun L sat => inv.covers L (by
            intro d member
            simp only [itemsList,List.cons_append,List.mem_cons] at member
            rcases member with rfl | rest
            · exact .inr (sat b (by simp [itemsList]))
            · exact sat d (by simp [itemsList,rest])) }
      refine ⟨left || right,?_,?_,?_⟩
      · cases left <;> simp [duplicate_correct,duplicate_history_correct,leftRun,rightRun]
      · intro accepted
        rcases Bool.or_eq_true_iff.mp accepted with yes | yes
        · exact accepts_of_implies (fun L sat d member => by
            simp only [itemsList,List.cons_append,List.mem_cons] at member
            rcases member with rfl | rest
            · exact .inl (sat a (by simp [itemsList]))
            · exact sat d (by simp [itemsList,rest])) (leftDecides.1 yes)
        · exact accepts_of_implies (fun L sat d member => by
            simp only [itemsList,List.cons_append,List.mem_cons] at member
            rcases member with rfl | rest
            · exact .inr (sat b (by simp [itemsList]))
            · exact sat d (by simp [itemsList,rest])) (rightDecides.1 yes)
      · rintro ⟨Object,Value,I,x,respects,everywhere,holds⟩
        have disj := holds (.Or a b) (by simp [itemsList])
        rw [Bool.or_eq_true_iff]
        rcases disj with yes | yes
        · left
          apply leftDecides.2
          refine ⟨Object,Value,I,x,respects,everywhere,fun d member => ?_⟩
          simp only [itemsList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rest
          · exact yes
          · exact holds d (by simp [itemsList,rest])
        · right
          apply rightDecides.2
          refine ⟨Object,Value,I,x,respects,everywhere,fun d member => ?_⟩
          simp only [itemsList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rest
          · exact yes
          · exact holds d (by simp [itemsList,rest])
    | Atom k =>
      obtain ⟨result,executed,decides⟩ := expand_correct rb cl axioms goals next
        (.Concept (.Atom k) literals) history
        (move (c := .Atom k) inv (by simp [Rowl.Tableau.Literal]) (by simp [itemsList]) (by simp [itemsList]))
      exact ⟨result,by simpa using executed,moved (c := .Atom k) (by simp [itemsList]) (by simp [itemsList]) decides⟩
    | NotAtom k =>
      obtain ⟨result,executed,decides⟩ := expand_correct rb cl axioms goals next
        (.Concept (.NotAtom k) literals) history
        (move (c := .NotAtom k) inv (by simp [Rowl.Tableau.Literal]) (by simp [itemsList]) (by simp [itemsList]))
      exact ⟨result,by simpa using executed,moved (c := .NotAtom k) (by simp [itemsList]) (by simp [itemsList]) decides⟩
    | Exists r d =>
      obtain ⟨result,executed,decides⟩ := expand_correct rb cl axioms goals next
        (.Concept (.Exists r d) literals) history
        (move (c := .Exists r d) inv (by simp [Rowl.Tableau.Literal]) (by simp [itemsList]) (by simp [itemsList]))
      exact ⟨result,by simpa using executed,moved (c := .Exists r d) (by simp [itemsList]) (by simp [itemsList]) decides⟩
    | Forall r d =>
      obtain ⟨result,executed,decides⟩ := expand_correct rb cl axioms goals next
        (.Concept (.Forall r d) literals) history
        (move (c := .Forall r d) inv (by simp [Rowl.Tableau.Literal]) (by simp [itemsList]) (by simp [itemsList]))
      exact ⟨result,by simpa using executed,moved (c := .Forall r d) (by simp [itemsList]) (by simp [itemsList]) decides⟩
  | Through t d next =>
    rw [tbox.expand.eq_def]
    obtain ⟨result,executed,decides⟩ := expand_correct rb cl axioms goals next (.Through t d literals) history
      (move (c := .Forall t d) inv (by simp [Rowl.Tableau.Literal]) (by simp [itemsList]) (by simp [itemsList]))
    exact ⟨result,by simpa using executed,moved (c := .Forall t d) (by simp [itemsList]) (by simp [itemsList]) decides⟩
termination_by (2 ^ cl.toFinset.card - (historyList history).length,
  total (itemsList pending) + total (itemsList literals),total (itemsList pending))
decreasing_by
  all_goals simp_wf
  all_goals
    subst_vars
    try rw [Prod.lex_def]
    try rw [Prod.lex_def]
    simp only [itemsList,historyList,total,weight,List.map_cons,List.sum_cons,List.map_nil,
      List.sum_nil,List.length_cons] at *
    omega

/-- The public procedure terminates; every acceptance comes, when the listed
    inclusions include their compositions, with a model of the role axioms in
    which the TBox concept holds everywhere and the concept has an instance; and
    every such model, in any universe, forces acceptance. -/
theorem satisfiable_with_correct (c axioms : nnf.NnfConcept) (rb : role_box.RoleBox) :
    ∃ result, tbox.satisfiable_with c axioms rb = .ok result ∧
      (result = true → Rowl.RoleBox.Closed rb → ∃ (Object : Type) (I : Interpretation Object Unit),
        Respects I rb ∧ (∀ y, conceptDenote I axioms y) ∧ ∃ x, conceptDenote I c x) ∧
      ((∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        Respects I rb ∧ (∀ y, conceptDenote I axioms y) ∧ ∃ x, conceptDenote I c x) → result = true) := by
  have base := closed_append (subconcepts_closed c) (subconcepts_closed axioms)
  obtain ⟨result,executed,decides⟩ := expand_correct.{u,v} rb (withThroughs rb (subconcepts c ++ subconcepts axioms))
    axioms [c,axioms] (.Concept c (.Concept axioms .Empty)) .Empty .Empty
    { closed := withThroughs_closed rb base
      throughs := withThroughs_throughs rb _
      axiomsIn := withThroughs_base (List.mem_append_right _ (subconcepts_self axioms))
      axiomsGoal := by simp
      pendingIn := by
        intro d member
        simp only [itemsList,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · exact withThroughs_base (List.mem_append_left _ (subconcepts_self _))
        · exact withThroughs_base (List.mem_append_right _ (subconcepts_self _))
      literalsIn := by simp [itemsList]
      historyIn := by simp [historyList]
      distinct := by simp [historyList]
      literal := by simp [itemsList]
      covers := by intro L sat; simpa [itemsList] using sat }
  refine ⟨result,by rw [tbox.satisfiable_with]; exact executed,?_,?_⟩
  · intro accepted closed
    obtain ⟨family,⟨L,located,sat⟩,coherent⟩ := decides.1 accepted
    simp only [historyList,List.not_mem_nil,or_false] at located
    exact Rowl.Hintikka.model_of_family rb closed axioms c family coherent L located (sat c (by simp [itemsList]))
  · rintro ⟨Object,Value,I,respects,everywhere,x,holds⟩
    exact decides.2 ⟨Object,Value,I,x,respects,everywhere,fun d member => by
      simp only [itemsList,List.mem_cons,List.not_mem_nil,or_false,List.append_nil] at member
      rcases member with rfl | rfl
      · exact holds
      · exact everywhere x⟩

/-- The subconcepts of every concept in a list. -/
def listSubconcepts : List nnf.NnfConcept → List nnf.NnfConcept
  | [] => []
  | c :: rest => subconcepts c ++ listSubconcepts rest
theorem listSubconcepts_closed : ∀ cs, Closed (listSubconcepts cs)
  | [] => ⟨by simp [listSubconcepts],by simp [listSubconcepts],by simp [listSubconcepts],by simp [listSubconcepts]⟩
  | c :: rest => closed_append (subconcepts_closed c) (listSubconcepts_closed rest)
theorem listSubconcepts_self : ∀ {cs : List nnf.NnfConcept} {c : nnf.NnfConcept}, c ∈ cs → c ∈ listSubconcepts cs
  | _ :: _, _, member => by
    rcases List.mem_cons.mp member with rfl | later
    · exact List.mem_append_left _ (subconcepts_self _)
    · exact List.mem_append_right _ (listSubconcepts_self later)

/-- The procedure for an item list terminates; every acceptance comes, when the
    listed inclusions include their compositions, with a model of the role
    axioms in which the TBox concept holds everywhere and one element satisfies
    every item; and every such model, in any universe, forces acceptance. -/
theorem satisfiable_items_correct (items : tbox.Items) (axioms : nnf.NnfConcept) (rb : role_box.RoleBox) :
    ∃ result, tbox.satisfiable_items items axioms rb = .ok result ∧
      (result = true → Rowl.RoleBox.Closed rb → ∃ (Object : Type) (I : Interpretation Object Unit),
        Respects I rb ∧ (∀ y, conceptDenote I axioms y) ∧ ∃ x, Holds I x (itemsList items)) ∧
      ((∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        Respects I rb ∧ (∀ y, conceptDenote I axioms y) ∧ ∃ x, Holds I x (itemsList items)) → result = true) := by
  have base := closed_append (listSubconcepts_closed (itemsList items)) (subconcepts_closed axioms)
  obtain ⟨result,executed,decides⟩ := expand_correct.{u,v} rb
    (withThroughs rb (listSubconcepts (itemsList items) ++ subconcepts axioms)) axioms (axioms :: itemsList items)
    (.Concept axioms items) .Empty .Empty
    { closed := withThroughs_closed rb base
      throughs := withThroughs_throughs rb _
      axiomsIn := withThroughs_base (List.mem_append_right _ (subconcepts_self axioms))
      axiomsGoal := by simp
      pendingIn := by
        intro d member
        simp only [itemsList,List.mem_cons] at member
        rcases member with rfl | inner
        · exact withThroughs_base (List.mem_append_right _ (subconcepts_self _))
        · exact withThroughs_base (List.mem_append_left _ (listSubconcepts_self inner))
      literalsIn := by simp [itemsList]
      historyIn := by simp [historyList]
      distinct := by simp [historyList]
      literal := by simp [itemsList]
      covers := by intro L sat; simpa [itemsList] using sat }
  refine ⟨result,by rw [tbox.satisfiable_items]; exact executed,?_,?_⟩
  · intro accepted closed
    obtain ⟨family,⟨L,located,sat⟩,coherent⟩ := decides.1 accepted
    simp only [historyList,List.not_mem_nil,or_false] at located
    refine ⟨{L // L ∈ family},Rowl.Hintikka.familyModel rb family L located,
      Rowl.Hintikka.family_respects rb closed family L located,fun y => ?_,⟨L,located⟩,fun d member => ?_⟩
    · exact Rowl.Hintikka.family_truth rb axioms family coherent L located axioms y (coherent y.val y.property).2.1
    · exact Rowl.Hintikka.family_truth rb axioms family coherent L located d ⟨L,located⟩
        (sat d (by simp [itemsList,member]))
  · rintro ⟨Object,Value,I,respects,everywhere,x,holds⟩
    exact decides.2 ⟨Object,Value,I,x,respects,everywhere,fun d member => by
      simp only [itemsList,List.mem_cons,List.append_nil] at member
      rcases member with rfl | inner
      · exact everywhere x
      · exact holds d inner⟩

/-- The ALC entry points use no role axioms. -/
theorem no_roles_correct : ∃ rb, tbox.no_roles = .ok rb ∧ rb.inclusions.val = [] ∧ rb.transitive.val = [] :=
  ⟨_,rfl,rfl,rfl⟩

/-- The public procedure terminates; every acceptance comes with a model in which
    the TBox concept holds everywhere and the concept has an instance; and every
    such model, in any universe, forces acceptance. -/
theorem satisfiable_in_correct (c axioms : nnf.NnfConcept) :
    ∃ result, tbox.satisfiable_in c axioms = .ok result ∧
      (result = true → ∃ (Object : Type) (I : Interpretation Object Unit),
        (∀ y, conceptDenote I axioms y) ∧ ∃ x, conceptDenote I c x) ∧
      ((∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        (∀ y, conceptDenote I axioms y) ∧ ∃ x, conceptDenote I c x) → result = true) := by
  obtain ⟨rb,noRun,noInclusions,noTransitive⟩ := no_roles_correct
  obtain ⟨result,executed,sound,complete⟩ := satisfiable_with_correct.{u,v} c axioms rb
  refine ⟨result,by simp only [tbox.satisfiable_in,noRun,bind_ok,executed],?_,?_⟩
  · intro accepted
    obtain ⟨Object,I,_,everywhere,x,holds⟩ := sound accepted (closed_of_empty rb noInclusions)
    exact ⟨Object,I,everywhere,x,holds⟩
  · rintro ⟨Object,Value,I,everywhere,x,holds⟩
    exact complete ⟨Object,Value,I,respects_of_empty I rb noInclusions noTransitive,everywhere,x,holds⟩

/-- A rejection proves the concept empty in every interpretation, in any
    universe, where the TBox concept holds at every element. -/
theorem rejected_empty_in_models (c axioms : nnf.NnfConcept) (rejected : tbox.satisfiable_in c axioms = .ok false)
    {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (model : ∀ y, conceptDenote I axioms y)
    (x : Object) : ¬ conceptDenote I c x := by
  intro member
  obtain ⟨result,executed,_,complete⟩ := satisfiable_in_correct.{u,v} c axioms
  have same := Result.ok_injective (executed.symm.trans rejected)
  have yes := complete ⟨Object,Value,I,model,x,member⟩
  rw [same] at yes
  cases yes
/-- The procedure never rejects an OWL class expression with an instance in an OWL
    interpretation (one fixing owl:Thing and owl:Nothing) in which the TBox class
    expression holds at every element. -/
theorem class_instances_accepted_in (e t : ClassExpression) (c axioms : nnf.NnfConcept)
    (translated : nnf.nnf e true = .ok (some c)) (internalized : nnf.nnf t true = .ok (some axioms))
    {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (fixes : Rowl.Nnf.Fixes I)
    (model : ∀ y, classDenote I t y) (x : Object) (member : classDenote I e x) :
    tbox.satisfiable_in c axioms = .ok true := by
  obtain ⟨result,executed,_,complete⟩ := satisfiable_in_correct.{u,v} c axioms
  rw [executed]
  have everywhere : ∀ y, conceptDenote I axioms y := fun y =>
    (Rowl.Nnf.nnf_meaning t true axioms internalized I fixes y).mpr (model y)
  have instance' := (Rowl.Nnf.nnf_meaning e true c translated I fixes x).mpr member
  rw [complete ⟨Object,Value,I,everywhere,x,instance'⟩]
/-- A rejection proves the OWL class expression empty in every OWL interpretation in
    which the TBox class expression holds at every element, which is how
    unsatisfiability and subsumption answers under such a TBox are justified. -/
theorem rejected_class_empty_in (e t : ClassExpression) (c axioms : nnf.NnfConcept)
    (translated : nnf.nnf e true = .ok (some c)) (internalized : nnf.nnf t true = .ok (some axioms))
    (rejected : tbox.satisfiable_in c axioms = .ok false)
    {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (fixes : Rowl.Nnf.Fixes I)
    (model : ∀ y, classDenote I t y) (x : Object) : ¬ classDenote I e x := by
  intro member
  have accepted := class_instances_accepted_in e t c axioms translated internalized I fixes model x member
  rw [rejected] at accepted
  cases Result.ok_injective accepted

theorem items_of_correct (list : tableau.Concepts) : tbox.items_of list = .ok (fromConcepts (toList list)) := by
  induction list with
  | Empty => rw [tbox.items_of]; rfl
  | Entry c next ih => rw [tbox.items_of]; simp [ih,toList,fromConcepts]

/-- The procedure for a list of concepts terminates; every acceptance comes with
    a model in which the TBox concept holds everywhere and one element is in
    every concept of the list; and every such model, in any universe, forces
    acceptance. -/
theorem satisfiable_all_correct (concepts : tableau.Concepts) (axioms : nnf.NnfConcept) :
    ∃ result, tbox.satisfiable_all concepts axioms = .ok result ∧
      (result = true → ∃ (Object : Type) (I : Interpretation Object Unit),
        (∀ y, conceptDenote I axioms y) ∧ ∃ x, Holds I x (toList concepts)) ∧
      ((∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        (∀ y, conceptDenote I axioms y) ∧ ∃ x, Holds I x (toList concepts)) → result = true) := by
  obtain ⟨rb,noRun,noInclusions,noTransitive⟩ := no_roles_correct
  obtain ⟨result,executed,sound,complete⟩ :=
    satisfiable_items_correct.{u,v} (fromConcepts (toList concepts)) axioms rb
  rw [itemsList_fromConcepts] at sound complete
  refine ⟨result,by simp only [tbox.satisfiable_all,noRun,items_of_correct,bind_ok,executed],?_,?_⟩
  · intro accepted
    obtain ⟨Object,I,_,everywhere,x,holds⟩ := sound accepted (closed_of_empty rb noInclusions)
    exact ⟨Object,I,everywhere,x,holds⟩
  · rintro ⟨Object,Value,I,everywhere,x,holds⟩
    exact complete ⟨Object,Value,I,respects_of_empty I rb noInclusions noTransitive,everywhere,x,holds⟩
end Rowl.TboxTableau
