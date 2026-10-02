import Rowl.Hintikka

/-!
ALC concept satisfiability with respect to a TBox concept, by a tableau with
subset blocking, proved total, sound and complete. Every acceptance yields a
coherent Hintikka family and therefore a model of the TBox concept with an
instance of the input; any model, in any universe, forces acceptance.
Termination: unblocked nodes add pairwise distinct subsets of a finite closure
to the history, so the history length is bounded by 2 ^ |closure|.
-/
namespace Rowl.TboxTableau
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation classDenote)
open Rowl.Nnf (conceptDenote)
open Rowl.Tableau (toList fromList toList_fromList weight total Holds fillers fillers_mem existentials
  existentials_mem duplicate_correct has_clash_correct universal_fillers_correct class_eq_iff property_eq_iff)
open Rowl.Hintikka (Sat SatAll ClashFree Witnessed Coherent sat_mono sat_literal)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v

/-- The ancestor literal sets, nearest first. -/
def historyList : tbox.History → List (List nnf.NnfConcept)
  | .Empty => []
  | .Entry label next => toList label :: historyList next

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

/-- Acceptance certificate at a node: a family coherent relative to the ancestors,
    and a set in the family or among the ancestors satisfying every current concept. -/
def Accepts (axioms : nnf.NnfConcept) (ancestors : List (List nnf.NnfConcept)) (current : List nnf.NnfConcept) : Prop :=
  ∃ family, (∃ L, (L ∈ family ∨ L ∈ ancestors) ∧ SatAll L current) ∧ Coherent axioms family ancestors
/-- Some model, in the given universes, satisfies the TBox concept at every element
    and every current concept at one element. -/
def ModelSat (axioms : nnf.NnfConcept) (current : List nnf.NnfConcept) : Prop :=
  ∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (x : Object),
    (∀ y, conceptDenote I axioms y) ∧ Holds I x current
/-- The procedure's contract at a node. -/
def Decides (axioms : nnf.NnfConcept) (ancestors : List (List nnf.NnfConcept)) (current : List nnf.NnfConcept)
    (result : Bool) : Prop :=
  (result = true → Accepts axioms ancestors current) ∧ (ModelSat.{u,v} axioms current → result = true)
/-- Invariants of every call: everything stays inside a closed finite closure,
    ancestor literal sets are pairwise distinct, the literal list holds only
    literals, and satisfying the current concepts entails the node's goals,
    which include the TBox concept. -/
structure Invariant (cl : List nnf.NnfConcept) (axioms : nnf.NnfConcept) (goals : List nnf.NnfConcept)
    (pending literals : tableau.Concepts) (history : tbox.History) : Prop where
  closed : Closed cl
  axiomsIn : axioms ∈ cl
  axiomsGoal : axioms ∈ goals
  pendingIn : ∀ c ∈ toList pending, c ∈ cl
  literalsIn : ∀ c ∈ toList literals, c ∈ cl
  historyIn : ∀ h ∈ historyList history, ∀ c ∈ h, c ∈ cl
  distinct : ((historyList history).map List.toFinset).Nodup
  literal : ∀ c ∈ toList literals, Rowl.Tableau.Literal c
  covers : ∀ L, SatAll L (toList pending ++ toList literals) → SatAll L goals

theorem duplicate_history_correct (history : tbox.History) : tbox.duplicate_history history = .ok (history,history) := by
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
theorem contains_concept_correct (list : tableau.Concepts) (sought : nnf.NnfConcept) :
    tbox.contains_concept list sought = .ok (decide (sought ∈ toList list),list) := by
  induction list with
  | Empty => rw [tbox.contains_concept]; simp [toList]
  | Entry c next ih =>
    rw [tbox.contains_concept]
    by_cases same : c = sought
    · subst same; simp [same_concept_correct,ih,toList]
    · have different : ¬ sought = c := fun h => same h.symm
      simp [same_concept_correct,ih,toList,same,different]
theorem subset_correct (small large : tableau.Concepts) :
    tbox.subset small large = .ok (decide (∀ c ∈ toList small, c ∈ toList large),small,large) := by
  induction small with
  | Empty => rw [tbox.subset]; simp [toList]
  | Entry c next ih =>
    rw [tbox.subset]
    by_cases present : c ∈ toList large <;> simp [contains_concept_correct,ih,toList,present]
theorem blocked_correct (label : tableau.Concepts) (history : tbox.History) :
    tbox.blocked label history =
      .ok (decide (∃ h ∈ historyList history, ∀ c ∈ toList label, c ∈ h),label,history) := by
  induction history with
  | Empty => rw [tbox.blocked]; simp [historyList]
  | Entry ancestor next ih =>
    rw [tbox.blocked]
    by_cases inside : ∀ c ∈ toList label, c ∈ toList ancestor
    · simp [subset_correct,ih,historyList,eq_true inside]
    · simp [subset_correct,ih,historyList,inside]

/-- Every existential in `cursor` is checked through its successor call. -/
private theorem existentials_hold_correct (all cursor : tableau.Concepts) (history : tbox.History)
    (axioms : nnf.NnfConcept)
    (child : ∀ r c, .Exists r c ∈ toList cursor → ∃ result,
      tbox.expand (.Entry c (.Entry axioms (fromList (fillers r (toList all))))) .Empty history axioms = .ok result) :
    ∃ result, tbox.existentials_hold all cursor history axioms = .ok (result,all,history) ∧
      (result = true ↔ ∀ r c, .Exists r c ∈ toList cursor →
        tbox.expand (.Entry c (.Entry axioms (fromList (fillers r (toList all))))) .Empty history axioms = .ok true) := by
  induction cursor with
  | Empty => exact ⟨true,by rw [tbox.existentials_hold.eq_def],by simp [toList]⟩
  | Entry c next ih =>
    obtain ⟨later,laterRead,laterIff⟩ := ih (fun r d member => child r d (by simp [toList,member]))
    rw [tbox.existentials_hold.eq_def]
    cases c with
    | Exists r d =>
      obtain ⟨here,hereRead⟩ := child r d (by simp [toList])
      refine ⟨here && later,?_,?_⟩
      · cases here <;> simp [universal_fillers_correct,duplicate_history_correct,hereRead,laterRead]
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

private theorem witnessed_mono {axioms : nnf.NnfConcept} {pool pool' : List (List nnf.NnfConcept)}
    {L : List nnf.NnfConcept} (sub : ∀ X ∈ pool, X ∈ pool') (witnessed : Witnessed axioms pool L) :
    Witnessed axioms pool' L := by
  intro r c member
  obtain ⟨L',inPool,rest⟩ := witnessed r c member
  exact ⟨L',sub L' inPool,rest⟩
private theorem accepts_of_implies {axioms : nnf.NnfConcept} {ancestors : List (List nnf.NnfConcept)}
    {current current' : List nnf.NnfConcept} (implies : ∀ L, SatAll L current' → SatAll L current)
    (accepted : Accepts axioms ancestors current') : Accepts axioms ancestors current := by
  obtain ⟨family,⟨L,member,sat⟩,coherent⟩ := accepted
  exact ⟨family,⟨L,member,implies L sat⟩,coherent⟩
private theorem model_of_implies {axioms : nnf.NnfConcept} {current current' : List nnf.NnfConcept}
    (implies : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (x : Object),
      Holds I x current → Holds I x current')
    (model : ModelSat.{u,v} axioms current) : ModelSat.{u,v} axioms current' := by
  obtain ⟨Object,Value,I,x,everywhere,holds⟩ := model
  exact ⟨Object,Value,I,x,everywhere,implies Object Value I x holds⟩

private theorem coherent_append {axioms : nnf.NnfConcept} {F G ancestors : List (List nnf.NnfConcept)}
    (cf : Coherent axioms F ancestors) (cg : Coherent axioms G ancestors) : Coherent axioms (F ++ G) ancestors := by
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
private theorem combine {axioms : nnf.NnfConcept} {ancestors : List (List nnf.NnfConcept)}
    (wanted : List (List nnf.NnfConcept)) (each : ∀ goal ∈ wanted, Accepts axioms ancestors goal) :
    ∃ family, (∀ goal ∈ wanted, ∃ L, (L ∈ family ∨ L ∈ ancestors) ∧ SatAll L goal) ∧
      Coherent axioms family ancestors := by
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
private theorem move {cl : List nnf.NnfConcept} {axioms : nnf.NnfConcept} {goals : List nnf.NnfConcept}
    {c : nnf.NnfConcept} {next literals : tableau.Concepts} {history : tbox.History}
    (inv : Invariant cl axioms goals (.Entry c next) literals history) (isLiteral : Rowl.Tableau.Literal c) :
    Invariant cl axioms goals next (.Entry c literals) history :=
  { closed := inv.closed
    axiomsIn := inv.axiomsIn
    axiomsGoal := inv.axiomsGoal
    pendingIn := fun d member => inv.pendingIn d (by simp [toList,member])
    literalsIn := by
      intro d member
      simp only [toList,List.mem_cons] at member
      rcases member with rfl | rest
      · exact inv.pendingIn _ (by simp [toList])
      · exact inv.literalsIn d rest
    historyIn := inv.historyIn
    distinct := inv.distinct
    literal := by
      intro d member
      simp only [toList,List.mem_cons] at member
      rcases member with rfl | rest
      · exact isLiteral
      · exact inv.literal d rest
    covers := fun L sat => inv.covers L (fun d member => sat d (by
      simp only [toList,List.cons_append,List.mem_cons,List.mem_append] at member ⊢
      tauto)) }
/-- Moving a literal keeps the same concepts, so the same contract. -/
private theorem moved {axioms : nnf.NnfConcept} {ancestors : List (List nnf.NnfConcept)} {c : nnf.NnfConcept}
    {next literals : tableau.Concepts} {result : Bool}
    (decides : Decides.{u,v} axioms ancestors (toList next ++ toList (.Entry c literals)) result) :
    Decides.{u,v} axioms ancestors (toList (.Entry c next) ++ toList literals) result := by
  have same : ∀ d, d ∈ toList (.Entry c next) ++ toList literals ↔ d ∈ toList next ++ toList (.Entry c literals) := by
    intro d; simp [toList]; tauto
  exact ⟨fun accepted => accepts_of_implies (fun L sat d member => sat d ((same d).mp member)) (decides.1 accepted),
    fun model => decides.2 (model_of_implies (fun _ _ I x holds d member => holds d ((same d).mpr member)) model)⟩

/-- The actual procedure terminates on every call satisfying the invariants and
    decides exactly whether the current concepts are satisfiable together with the
    TBox concept, relative to the ancestors used for blocking. -/
theorem expand_correct (cl : List nnf.NnfConcept) (axioms : nnf.NnfConcept) (goals : List nnf.NnfConcept)
    (pending literals : tableau.Concepts) (history : tbox.History) :
    Invariant cl axioms goals pending literals history →
    ∃ result, tbox.expand pending literals history axioms = .ok result ∧
      Decides.{u,v} axioms (historyList history) (toList pending ++ toList literals) result := by
  intro inv
  cases pending with
  | Empty =>
    rw [tbox.expand.eq_def]
    simp only [duplicate_correct,has_clash_correct,bind_ok,uncurry_apply_pair]
    by_cases clash : ∃ k, .NotAtom k ∈ toList literals ∧ .Atom k ∈ toList literals
    · refine ⟨false,by simp [clash],?_⟩
      constructor
      · intro impossible; cases impossible
      · rintro ⟨Object,Value,I,x,_,holds⟩
        obtain ⟨k,negative,positive⟩ := clash
        exact absurd (holds (.Atom k) (by simp [toList,positive])) (holds (.NotAtom k) (by simp [toList,negative]))
    · by_cases blockedHere : ∃ h ∈ historyList history, ∀ d ∈ toList literals, d ∈ h
      · refine ⟨true,by simp [clash,blocked_correct,blockedHere],?_⟩
        constructor
        · intro _
          obtain ⟨h,hmem,sub⟩ := blockedHere
          refine ⟨[],⟨h,.inr hmem,?_⟩,by simp [Coherent]⟩
          intro c cmem
          simp only [toList,List.nil_append] at cmem
          exact (sat_literal h c (inv.literal c cmem)).mpr (sub c cmem)
        · intro _; rfl
      · have extendedIn : ∀ h ∈ toList literals :: historyList history, ∀ c ∈ h, c ∈ cl := by
          intro h member c cmem
          rcases List.mem_cons.mp member with rfl | old
          · exact inv.literalsIn c cmem
          · exact inv.historyIn h old c cmem
        have extendedDistinct : ((toList literals :: historyList history).map List.toFinset).Nodup := by
          rw [List.map_cons,List.nodup_cons]
          refine ⟨?_,inv.distinct⟩
          intro member
          simp only [List.mem_map] at member
          obtain ⟨h,hmem,same⟩ := member
          apply blockedHere
          refine ⟨h,hmem,fun d dmem => ?_⟩
          have : d ∈ (toList literals).toFinset := List.mem_toFinset.mpr dmem
          rw [← same] at this
          exact List.mem_toFinset.mp this
        have bound := history_bound cl _ extendedDistinct extendedIn
        have successors : ∀ r c, .Exists r c ∈ toList literals → ∃ result,
            tbox.expand (.Entry c (.Entry axioms (fromList (fillers r (toList literals))))) .Empty
              (.Entry literals history) axioms = .ok result ∧
            Decides.{u,v} axioms (toList literals :: historyList history)
              (c :: axioms :: fillers r (toList literals)) result := by
          intro r c member
          have cIn : c ∈ cl := inv.closed.2.2.1 r c (inv.literalsIn _ member)
          obtain ⟨result,executed,decides⟩ := expand_correct cl axioms (c :: axioms :: fillers r (toList literals))
            (.Entry c (.Entry axioms (fromList (fillers r (toList literals))))) .Empty (.Entry literals history)
            { closed := inv.closed, axiomsIn := inv.axiomsIn, axiomsGoal := by simp,
              pendingIn := by
                intro d dmem
                simp only [toList,toList_fromList,List.mem_cons] at dmem
                rcases dmem with rfl | rfl | filler
                · exact cIn
                · exact inv.axiomsIn
                · exact inv.closed.2.2.2 r d (inv.literalsIn _ ((fillers_mem r _ d).mp filler))
              literalsIn := by simp [toList], historyIn := extendedIn, distinct := extendedDistinct,
              literal := by simp [toList],
              covers := by intro L sat; simpa [toList,toList_fromList] using sat }
          exact ⟨result,executed,by simpa [toList,toList_fromList,historyList] using decides⟩
        obtain ⟨result,executed,iff⟩ := existentials_hold_correct literals literals (.Entry literals history) axioms
          (fun r c member => (successors r c member).imp fun _ h => h.1)
        refine ⟨result,by simp [clash,blocked_correct,blockedHere,executed],?_⟩
        constructor
        · intro accepted
          have all := iff.mp accepted
          have each : ∀ goal ∈ (existentials (toList literals)).map
              (fun rc => rc.2 :: axioms :: fillers rc.1 (toList literals)),
              Accepts axioms (toList literals :: historyList history) goal := by
            intro goal member
            obtain ⟨⟨r,c⟩,rcMember,rfl⟩ := List.mem_map.mp member
            have exists' := (existentials_mem _ r c).mp rcMember
            obtain ⟨answer,run,decides⟩ := successors r c exists'
            have yes := all r c exists'
            rw [run] at yes
            exact decides.1 (Result.ok_injective yes)
          obtain ⟨F,covered,coherent⟩ := combine _ each
          have literalSat : SatAll (toList literals) (toList tableau.Concepts.Empty ++ toList literals) := by
            intro c cmem
            simp only [toList,List.nil_append] at cmem
            exact (sat_literal _ c (inv.literal c cmem)).mpr cmem
          refine ⟨toList literals :: F,⟨toList literals,.inl (List.mem_cons_self ..),literalSat⟩,?_⟩
          intro X member
          rcases List.mem_cons.mp member with rfl | deeper
          · refine ⟨fun k negative positive => clash ⟨k,negative,positive⟩,
              inv.covers _ literalSat axioms inv.axiomsGoal,?_⟩
            intro r c exists'
            have goalIn : c :: axioms :: fillers r (toList literals) ∈ (existentials (toList literals)).map
                (fun rc => rc.2 :: axioms :: fillers rc.1 (toList literals)) :=
              List.mem_map.mpr ⟨(r,c),(existentials_mem _ r c).mpr exists',rfl⟩
            obtain ⟨L,located,sat⟩ := covered _ goalIn
            refine ⟨L,?_,sat axioms (by simp),sat c (by simp),fun d dmem =>
              sat d (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ((fillers_mem r _ d).mpr dmem)))⟩
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
        · rintro ⟨Object,Value,I,x,everywhere,holds⟩
          simp only [toList,List.nil_append] at holds
          apply iff.mpr
          intro r c member
          obtain ⟨answer,run,decides⟩ := successors r c member
          rw [run]
          obtain ⟨y,edge,inner⟩ := holds (.Exists r c) member
          have model : ModelSat.{u,v} axioms (c :: axioms :: fillers r (toList literals)) := by
            refine ⟨Object,Value,I,y,everywhere,?_⟩
            intro d dmem
            simp only [List.mem_cons] at dmem
            rcases dmem with rfl | rfl | filler
            · exact inner
            · exact everywhere y
            · exact holds (.Forall r d) ((fillers_mem r _ d).mp filler) y edge
          rw [decides.2 model]
  | Entry c next =>
    rw [tbox.expand.eq_def]
    cases c with
    | Top =>
      obtain ⟨result,executed,decides⟩ := expand_correct cl axioms goals next literals history
        { inv with
          pendingIn := fun d member => inv.pendingIn d (by simp [toList,member])
          covers := fun L sat => inv.covers L (by
            intro d member
            simp only [toList,List.cons_append,List.mem_cons] at member
            rcases member with rfl | rest
            · exact trivial
            · exact sat d rest) }
      refine ⟨result,by simpa using executed,?_,?_⟩
      · intro accepted
        exact accepts_of_implies (fun L sat d member => by
          simp only [toList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rest
          · exact trivial
          · exact sat d rest) (decides.1 accepted)
      · intro model
        exact decides.2 (model_of_implies (fun _ _ I x holds d member => holds d (by
          simp only [toList,List.cons_append,List.mem_cons]; exact .inr member)) model)
    | Bottom =>
      refine ⟨false,rfl,?_⟩
      constructor
      · intro impossible; cases impossible
      · rintro ⟨Object,Value,I,x,_,holds⟩
        exact absurd (holds .Bottom (by simp [toList])) (by simp [conceptDenote])
    | And a b =>
      have abIn := inv.closed.1 a b (inv.pendingIn _ (by simp [toList]))
      obtain ⟨result,executed,decides⟩ := expand_correct cl axioms goals (.Entry a (.Entry b next)) literals history
        { inv with
          pendingIn := by
            intro d member
            simp only [toList,List.mem_cons] at member
            rcases member with rfl | rfl | rest
            · exact abIn.1
            · exact abIn.2
            · exact inv.pendingIn d (by simp [toList,rest])
          covers := fun L sat => inv.covers L (by
            intro d member
            simp only [toList,List.cons_append,List.mem_cons] at member
            rcases member with rfl | rest
            · exact ⟨sat a (by simp [toList]),sat b (by simp [toList])⟩
            · exact sat d (by simp [toList,rest])) }
      refine ⟨result,by simpa using executed,?_,?_⟩
      · intro accepted
        exact accepts_of_implies (fun L sat d member => by
          simp only [toList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rest
          · exact ⟨sat a (by simp [toList]),sat b (by simp [toList])⟩
          · exact sat d (by simp [toList,rest])) (decides.1 accepted)
      · intro model
        exact decides.2 (model_of_implies (fun _ _ I x holds d member => by
          have conj := holds (.And a b) (by simp [toList])
          simp only [toList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rfl | rest
          · exact conj.1
          · exact conj.2
          · exact holds d (by simp [toList,rest])) model)
    | Or a b =>
      have abIn := inv.closed.2.1 a b (inv.pendingIn _ (by simp [toList]))
      obtain ⟨left,leftRun,leftDecides⟩ := expand_correct cl axioms goals (.Entry a next) literals history
        { inv with
          pendingIn := by
            intro d member
            simp only [toList,List.mem_cons] at member
            rcases member with rfl | rest
            · exact abIn.1
            · exact inv.pendingIn d (by simp [toList,rest])
          covers := fun L sat => inv.covers L (by
            intro d member
            simp only [toList,List.cons_append,List.mem_cons] at member
            rcases member with rfl | rest
            · exact .inl (sat a (by simp [toList]))
            · exact sat d (by simp [toList,rest])) }
      obtain ⟨right,rightRun,rightDecides⟩ := expand_correct cl axioms goals (.Entry b next) literals history
        { inv with
          pendingIn := by
            intro d member
            simp only [toList,List.mem_cons] at member
            rcases member with rfl | rest
            · exact abIn.2
            · exact inv.pendingIn d (by simp [toList,rest])
          covers := fun L sat => inv.covers L (by
            intro d member
            simp only [toList,List.cons_append,List.mem_cons] at member
            rcases member with rfl | rest
            · exact .inr (sat b (by simp [toList]))
            · exact sat d (by simp [toList,rest])) }
      refine ⟨left || right,?_,?_,?_⟩
      · cases left <;> simp [duplicate_correct,duplicate_history_correct,leftRun,rightRun]
      · intro accepted
        rcases Bool.or_eq_true_iff.mp accepted with yes | yes
        · exact accepts_of_implies (fun L sat d member => by
            simp only [toList,List.cons_append,List.mem_cons] at member
            rcases member with rfl | rest
            · exact .inl (sat a (by simp [toList]))
            · exact sat d (by simp [toList,rest])) (leftDecides.1 yes)
        · exact accepts_of_implies (fun L sat d member => by
            simp only [toList,List.cons_append,List.mem_cons] at member
            rcases member with rfl | rest
            · exact .inr (sat b (by simp [toList]))
            · exact sat d (by simp [toList,rest])) (rightDecides.1 yes)
      · rintro ⟨Object,Value,I,x,everywhere,holds⟩
        have disj := holds (.Or a b) (by simp [toList])
        rw [Bool.or_eq_true_iff]
        rcases disj with yes | yes
        · left
          apply leftDecides.2
          refine ⟨Object,Value,I,x,everywhere,fun d member => ?_⟩
          simp only [toList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rest
          · exact yes
          · exact holds d (by simp [toList,rest])
        · right
          apply rightDecides.2
          refine ⟨Object,Value,I,x,everywhere,fun d member => ?_⟩
          simp only [toList,List.cons_append,List.mem_cons] at member
          rcases member with rfl | rest
          · exact yes
          · exact holds d (by simp [toList,rest])
    | Atom k =>
      obtain ⟨result,executed,decides⟩ := expand_correct cl axioms goals next (.Entry (.Atom k) literals) history
        (move inv (by simp [Rowl.Tableau.Literal]))
      exact ⟨result,by simpa using executed,moved decides⟩
    | NotAtom k =>
      obtain ⟨result,executed,decides⟩ := expand_correct cl axioms goals next (.Entry (.NotAtom k) literals) history
        (move inv (by simp [Rowl.Tableau.Literal]))
      exact ⟨result,by simpa using executed,moved decides⟩
    | Exists r d =>
      obtain ⟨result,executed,decides⟩ := expand_correct cl axioms goals next (.Entry (.Exists r d) literals) history
        (move inv (by simp [Rowl.Tableau.Literal]))
      exact ⟨result,by simpa using executed,moved decides⟩
    | Forall r d =>
      obtain ⟨result,executed,decides⟩ := expand_correct cl axioms goals next (.Entry (.Forall r d) literals) history
        (move inv (by simp [Rowl.Tableau.Literal]))
      exact ⟨result,by simpa using executed,moved decides⟩
termination_by (2 ^ cl.toFinset.card - (historyList history).length,
  total (toList pending) + total (toList literals),total (toList pending))
decreasing_by
  all_goals simp_wf
  all_goals
    subst_vars
    try rw [Prod.lex_def]
    try rw [Prod.lex_def]
    simp only [toList,toList_fromList,historyList,total,weight,List.map_cons,List.sum_cons,List.map_nil,
      List.sum_nil,List.length_cons] at *
    omega
/-- The public procedure terminates; every acceptance comes with a model in which
    the TBox concept holds everywhere and the concept has an instance; and every
    such model, in any universe, forces acceptance. -/
theorem satisfiable_in_correct (c axioms : nnf.NnfConcept) :
    ∃ result, tbox.satisfiable_in c axioms = .ok result ∧
      (result = true → ∃ (Object : Type) (I : Interpretation Object Unit),
        (∀ y, conceptDenote I axioms y) ∧ ∃ x, conceptDenote I c x) ∧
      ((∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        (∀ y, conceptDenote I axioms y) ∧ ∃ x, conceptDenote I c x) → result = true) := by
  obtain ⟨result,executed,decides⟩ := expand_correct.{u,v} (subconcepts c ++ subconcepts axioms) axioms [c,axioms]
    (.Entry c (.Entry axioms .Empty)) .Empty .Empty
    { closed := closed_append (subconcepts_closed c) (subconcepts_closed axioms)
      axiomsIn := List.mem_append_right _ (subconcepts_self axioms)
      axiomsGoal := by simp
      pendingIn := by
        intro d member
        simp only [toList,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · exact List.mem_append_left _ (subconcepts_self _)
        · exact List.mem_append_right _ (subconcepts_self _)
      literalsIn := by simp [toList]
      historyIn := by simp [historyList]
      distinct := by simp [historyList]
      literal := by simp [toList]
      covers := by intro L sat; simpa [toList] using sat }
  refine ⟨result,by rw [tbox.satisfiable_in]; exact executed,?_,?_⟩
  · intro accepted
    obtain ⟨family,⟨L,located,sat⟩,coherent⟩ := decides.1 accepted
    simp only [historyList,List.not_mem_nil,or_false] at located
    exact Rowl.Hintikka.model_of_family axioms c family coherent L located (sat c (by simp [toList]))
  · rintro ⟨Object,Value,I,everywhere,x,holds⟩
    exact decides.2 ⟨Object,Value,I,x,everywhere,fun d member => by
      simp only [toList,List.mem_cons,List.not_mem_nil,or_false,List.append_nil] at member
      rcases member with rfl | rfl
      · exact holds
      · exact everywhere x⟩

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
  obtain ⟨result,executed,decides⟩ := expand_correct.{u,v}
    (listSubconcepts (toList concepts) ++ subconcepts axioms) axioms (axioms :: toList concepts)
    (.Entry axioms concepts) .Empty .Empty
    { closed := closed_append (listSubconcepts_closed _) (subconcepts_closed axioms)
      axiomsIn := List.mem_append_right _ (subconcepts_self axioms)
      axiomsGoal := by simp
      pendingIn := by
        intro d member
        simp only [toList,List.mem_cons] at member
        rcases member with rfl | inner
        · exact List.mem_append_right _ (subconcepts_self _)
        · exact List.mem_append_left _ (listSubconcepts_self inner)
      literalsIn := by simp [toList]
      historyIn := by simp [historyList]
      distinct := by simp [historyList]
      literal := by simp [toList]
      covers := by intro L sat; simpa [toList] using sat }
  refine ⟨result,by rw [tbox.satisfiable_all]; exact executed,?_,?_⟩
  · intro accepted
    obtain ⟨family,⟨L,located,sat⟩,coherent⟩ := decides.1 accepted
    simp only [historyList,List.not_mem_nil,or_false] at located
    refine ⟨{L // L ∈ family},Rowl.Hintikka.familyModel family L located,fun y => ?_,⟨L,located⟩,fun d member => ?_⟩
    · exact Rowl.Hintikka.family_truth axioms family coherent L located axioms y (coherent y.val y.property).2.1
    · exact Rowl.Hintikka.family_truth axioms family coherent L located d ⟨L,located⟩
        (sat d (by simp [toList,member]))
  · rintro ⟨Object,Value,I,everywhere,x,holds⟩
    exact decides.2 ⟨Object,Value,I,x,everywhere,fun d member => by
      simp only [toList,List.mem_cons,List.append_nil] at member
      rcases member with rfl | inner
      · exact everywhere x
      · exact holds d inner⟩
end Rowl.TboxTableau
