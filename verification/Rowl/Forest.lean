import Rowl.ForestSteps

/-!
The completion forest's run: totality and the meaning of its rejections. Every
rule application adds a literal to the label of an active node, expands a
restriction of an unblocked node, merges two neighbours, merges a node into
the named node of its nominal, or creates new named nodes for a maximum
restriction of a named node, and each of these decreases the measure, so `run`
terminates on every forest that keeps the invariant; a node with `¬∃r.Self`
that is its own neighbour along `r`, or with a common neighbour along both roles
of a disjoint pair, is a clash. An acceptance comes with a
complete forest that keeps the invariant; a rejection with a set of branch
points rules out every model, in any universes, that holds under those points. Branching on a disjunction or on
a neighbour's choice for a maximum restriction retries the second alternative
only when the first failure depends on the new branch point; merging tries the
pairs of neighbours that are not known to differ in turn, since in every model
of a maximum restriction two of its counted neighbours coincide; merging a tree
node into its tree parent adds the loops of their edge to the parent. Every model
places a node with a nominal and the named node of its individual on the
individual, so their merge is forced and a difference between them is a clash.
Every model of a maximum restriction of a named node has an exact number of
counted neighbours, between 1 and the bound when one exists, so the rule for new
named nodes tries the guesses in turn, and the bound it records makes the
neighbour it counts coincide with one of as many counted named neighbours.
-/
namespace Rowl.Forest
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation)
open Rowl.Concepts (inv inv_inv relation_inv denote negate_correct)
open Rowl.Hierarchy (Below Closed Respects Constrained transitives below_refl respects_below below_correct)
open Rowl.ConceptTable (WellFormed meaning meaning_at rebuild parts Complements complements_append FromOriginal Added)
open Rowl.CompletionSearch (Holds Complementary Clashes contains_correct clashes_correct holds_listed)
open Rowl.Completion (Sub pendingList pendingWeight three_pow_lt join_correct without_from_correct
  copy_label_correct copy_pending_correct copy_links_correct holds_mono holds_denote grow_strict Corresponds Unfolds
  corresponds_append unfolds_append intern_facts_correct intern_definitions_correct)
open Rowl.ForestSearch
open Rowl.ForestOps
open Rowl.ForestInv
open Rowl.ForestSteps
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
universe u v

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- A listed literal holds in the label. -/
theorem holds_literal (entries : List concept_table.Entry) (L : List Usize) (c : Usize) (e : concept_table.Entry)
    (at_c : entries[c.val]? = some e) (literal : ForestInv.Literal e) (member : c ∈ L) : Holds entries L c.val := by
  rw [holds_listed entries L c.val e at_c]
  · exact ⟨c,member,rfl⟩
  all_goals cases e <;> simp_all [ForestInv.Literal]

/-- A branch: the left alternative under the new branch point `fresh`, and the
    right one, depending on the points the left failure depended on, only when
    that failure depends on `fresh`. Its answer means what `Answers` says for
    any extra entries that imply one of the alternatives and the rest. -/
theorem branch_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (F : forest.Forest)
    (x left right : Usize) (next : completion.Pending) (deps : alloc.vec.Vec Usize) (fresh : Usize)
    (extra : List Usize) (freshF : FreshForest F fresh.val) (freshDeps : ∀ k ∈ deps.val, k.val < fresh.val)
    (leftCase : ∀ (deps' : alloc.vec.Vec Usize) (fresh' : Usize), fresh'.val = fresh.val + 1 →
      (∀ k ∈ deps'.val, k.val < fresh'.val) →
      ∃ r, forest.add P h F x (.Item left next) deps' fresh' = .ok r ∧
        Answers.{u,v} P h count F x.val (left :: pendingList next) deps'.val fresh'.val r)
    (rightCase : ∀ deps' : alloc.vec.Vec Usize, (∀ k ∈ deps'.val, k.val < fresh.val) →
      ∃ r, forest.add P h F x (.Item right next) deps' fresh = .ok r ∧
        Answers.{u,v} P h count F x.val (right :: pendingList next) deps'.val fresh.val r)
    (split : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (z : Object),
      (∀ c ∈ extra, denote I (meaning P.entries.val c.val) z) →
        (denote I (meaning P.entries.val left.val) z ∨ denote I (meaning P.entries.val right.val) z) ∧
        ∀ c ∈ pendingList next, denote I (meaning P.entries.val c.val) z) :
    ∃ r, forest.branch P h F x left right next deps fresh = .ok r ∧
      Answers.{u,v} P h count F x.val extra deps.val fresh.val r := by
  rw [forest.branch]
  by_cases room : fresh.val < Usize.max
  · obtain ⟨point,pointRun,pointValue⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new Usize) fresh (by simp; scalar_tac))
    obtain ⟨leftDeps,leftDepsRun,leftDepsSpec⟩ := join_correct deps point
    obtain ⟨next',advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := fresh) (y := 1#usize) (by scalar_tac))
    have nextIs : next'.val = fresh.val + 1 := by simpa using nextValue
    simp only [UScalar.lt_equiv,usize_max_val,room,↓reduceIte,copy_forest_correct,copy_pending_correct,bind_ok,
      pointRun,leftDepsRun]
    cases leftDeps with
    | none => exact ⟨none,by simp,by simp,by simp⟩
    | some left_deps =>
    have leftMembers : ∀ k, k ∈ left_deps.val ↔ k ∈ deps.val ∨ k = fresh := by
      intro k
      rw [leftDepsSpec left_deps rfl k,pointValue]
      simp
    obtain ⟨leftResult,leftRun,leftSound,leftComplete⟩ := leftCase left_deps next' nextIs (by
      intro k member
      rw [nextIs]
      rcases (leftMembers k).mp member with given | rfl
      · have := freshDeps k given
        omega
      · omega)
    simp only [advance,bind_ok,leftRun]
    cases leftResult with
    | none => exact ⟨none,rfl,by simp,by simp⟩
    | some outcome =>
    cases outcome with
    | Accepted => exact ⟨some .Accepted,rfl,fun _ => leftSound rfl,by simp⟩
    | Rejected D1 =>
    obtain ⟨leftBound,leftNone⟩ := leftComplete D1 rfl
    by_cases depends : fresh ∈ D1.val
    · obtain ⟨rest,restRun,restSpec⟩ := without_from_correct D1 fresh 0#usize (alloc.vec.Vec.new Usize) (by simp)
      obtain ⟨rightDeps,rightDepsRun,rightDepsSpec⟩ := join_correct deps rest
      simp only [contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,depends,decide_true,
        ↓reduceIte,restRun,bind_ok,rightDepsRun]
      cases rightDeps with
      | none => exact ⟨none,by simp,by simp,by simp⟩
      | some right_deps =>
      have rightMembers : ∀ k, k ∈ right_deps.val ↔ k ∈ deps.val ∨ (k ∈ D1.val ∧ k ≠ fresh) := by
        intro k
        rw [rightDepsSpec right_deps rfl k,restSpec k]
        simp
      obtain ⟨right,rightRun,rightSound,rightComplete⟩ := rightCase right_deps (by
        intro k member
        rcases (rightMembers k).mp member with given | ⟨listed,other⟩
        · exact freshDeps k given
        · have bound := leftBound k listed
          rw [nextIs] at bound
          have : k.val ≠ fresh.val := fun same => other (UScalar.eq_of_val_eq same)
          omega)
      refine ⟨right,by simp [rightRun],rightSound,?_⟩
      intro D2 rejected
      obtain ⟨rightBound,rightNone⟩ := rightComplete D2 rejected
      refine ⟨rightBound,?_⟩
      rintro ⟨Object,Value,I,π,models,extras⟩
      by_cases subRight : Sub right_deps.val D2.val
      · have subDeps : Sub deps.val D2.val := fun k member => subRight k ((rightMembers k).mpr (.inl member))
        obtain ⟨either,nextHolds⟩ := split Object Value I (π x.val) (extras subDeps)
        rcases either with one | two
        · -- The left alternative holds: the left failure rules this model out.
          apply leftNone
          refine ⟨Object,Value,I,π,models_transfer freshF ?_ models,?_⟩
          · intro k below member
            apply subRight k
            apply (rightMembers k).mpr
            refine .inr ⟨member,?_⟩
            intro same
            rw [same] at below
            omega
          · intro _ c member
            rcases List.mem_cons.mp member with rfl | later
            · exact one
            · exact nextHolds c later
        · apply rightNone
          refine ⟨Object,Value,I,π,models,?_⟩
          intro _ c member
          rcases List.mem_cons.mp member with rfl | later
          · exact two
          · exact nextHolds c later
      · apply rightNone
        exact ⟨Object,Value,I,π,models,fun sub => absurd sub subRight⟩
    · simp only [contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,depends,decide_false,
        Bool.false_eq_true,↓reduceIte,bind_ok]
      refine ⟨some (.Rejected D1),rfl,by simp,?_⟩
      intro D same
      simp only [Option.some.injEq,completion.Outcome.Rejected.injEq] at same
      subst same
      refine ⟨?_,?_⟩
      · intro k member
        have bound := leftBound k member
        rw [nextIs] at bound
        have : k.val ≠ fresh.val := fun same => depends (by rw [← UScalar.eq_of_val_eq same]; exact member)
        omega
      · -- The left failure does not depend on the branch point: it rules out the
        -- model whatever the alternative.
        rintro ⟨Object,Value,I,π,models,_⟩
        apply leftNone
        refine ⟨Object,Value,I,π,models,?_⟩
        intro sub
        exact absurd (sub fresh ((leftMembers fresh).mpr (.inr rfl))) depends
  · refine ⟨none,?_,by simp,by simp⟩
    simp [UScalar.lt_equiv,usize_max_val,room]

/-- Adding pending entries to an active node terminates and means what `Answers`
    says, given that `run` does so on forests of measure below `M` and every way
    the additions can end has a measure below `M`. -/
theorem add_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (M : Nat)
    (IH : ∀ (F : forest.Forest) (fresh : Usize), ForestInv.measure P F < M → Inv P h count F →
      FreshForest F fresh.val →
      ∃ r, forest.run P h F fresh = .ok r ∧ Answers.{u,v} P h count F 0 [] [] fresh.val r) :
    ∀ (w : Nat) (pending : completion.Pending) (F : forest.Forest) (x : Usize) (deps : alloc.vec.Vec Usize)
      (fresh : Usize),
      pendingWeight (pendingList pending) = w → Inv P h count F → Active F.nodes.val x.val →
      FreshForest F fresh.val → (∀ k ∈ deps.val, k.val < fresh.val) →
      (∀ F' : forest.Forest, Inv P h count F' → Grows F F' →
        (∀ y, y ≠ x.val → labelOf F'.nodes.val y = labelOf F.nodes.val y) →
        (∀ c ∈ pendingList pending, Holds P.entries.val (labelOf F'.nodes.val x.val) c.val) →
        ForestInv.measure P F' < M) →
      ∃ r, forest.add P h F x pending deps fresh = .ok r ∧
        Answers.{u,v} P h count F x.val (pendingList pending) deps.val fresh.val r := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro pending F x deps fresh weight inv active freshF freshDeps progress
  have xIn := active_inside active
  cases pending with
  | Empty =>
    obtain ⟨r,run,sound,complete⟩ := IH F fresh
      (progress F inv (grows_refl F) (fun _ _ => rfl) (by simp [pendingList])) inv freshF
    refine ⟨r,by rw [forest.add]; exact run,sound,?_⟩
    intro D rejected
    obtain ⟨bound,none⟩ := complete D rejected
    exact ⟨bound,fun model => none (fullModel_any P h F x.val 0 deps.val [] D.val model)⟩
  | Item c next =>
    have wf := inv.shape.wellFormed
    by_cases cIn : c.val < P.entries.val.length
    · have lookup : P.entries.index_usize c = .ok P.entries.val[c.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem cIn]
      have at_c : P.entries.val[c.val]? = some P.entries.val[c.val] := List.getElem?_eq_getElem cIn
      have below := wf c.val _ at_c
      have weightIs : pendingWeight (pendingList (.Item c next)) = 3 ^ c.val + pendingWeight (pendingList next) := by
        simp [pendingWeight,pendingList]
      -- A literal is added unless it is there or clashes.
      have literalCase : ForestInv.Literal P.entries.val[c.val] →
          ∃ r, forest.add_literal P h F x c next deps fresh = .ok r ∧
            Answers.{u,v} P h count F x.val (c :: pendingList next) deps.val fresh.val r := by
        intro literal
        have nodeLookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
          simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem xIn]
        have at_x : F.nodes.val[x.val]? = some F.nodes.val[x.val] := List.getElem?_eq_getElem xIn
        have labelIs : labelOf F.nodes.val x.val = F.nodes.val[x.val].label.val := by
          simp [labelOf,at_x]
        have depsIs : nodeDeps F x.val = F.nodes.val[x.val].deps.val := by
          simp [nodeDeps,at_x]
        have smaller : pendingWeight (pendingList next) < w := by
          rw [← weight,weightIs]; have := pow_pos (show 0 < 3 by omega) c.val; omega
        rw [forest.add_literal]
        by_cases present : c ∈ labelOf F.nodes.val x.val
        · obtain ⟨r,run,sound,complete⟩ := ih _ smaller next F x deps fresh rfl inv active freshF freshDeps (by
            intro F' inv' grows' others' holds'
            apply progress F' inv' grows' others'
            intro c' member
            rcases List.mem_cons.mp member with rfl | later
            · exact holds_literal _ _ c' _ at_c literal (grows_label grows' x.val c' present)
            · exact holds' c' later)
          refine ⟨r,?_,sound,?_⟩
          · rw [labelIs] at present
            simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,↓reduceIte,alloc.vec.Vec.index_slice_index,
              nodeLookup,bind_ok,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,present,decide_true,
              run]
          · intro D rejected
            obtain ⟨bound,none⟩ := complete D rejected
            exact ⟨bound,fun model => none (fullModel_drop P h _ _ _ _ _ _ model)⟩
        · have absent : c ∉ F.nodes.val[x.val].label.val := by rwa [← labelIs]
          by_cases clash : Clashes P.entries.val (labelOf F.nodes.val x.val) c
          · obtain ⟨joined,joinRun,joinSpec⟩ := join_correct F.nodes.val[x.val].deps deps
            have clash' : Clashes P.entries.val F.nodes.val[x.val].label.val c := by rwa [← labelIs]
            cases joined with
            | none =>
              refine ⟨none,?_,by simp,by simp⟩
              simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,↓reduceIte,alloc.vec.Vec.index_slice_index,
                nodeLookup,bind_ok,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,absent,
                decide_false,Bool.false_eq_true,clashes_correct,clash',decide_true,joinRun]
            | some clashSet =>
              refine ⟨some (.Rejected clashSet),?_,by simp,?_⟩
              · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,↓reduceIte,alloc.vec.Vec.index_slice_index,
                  nodeLookup,bind_ok,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,absent,
                  decide_false,Bool.false_eq_true,clashes_correct,clash',decide_true,joinRun]
              · intro D same
                simp only [Option.some.injEq,completion.Outcome.Rejected.injEq] at same
                subst same
                have members := joinSpec clashSet rfl
                refine ⟨?_,?_⟩
                · intro k member
                  rcases (members k).mp member with old | given
                  · exact freshF.1 x.val k (by rw [depsIs]; exact old)
                  · exact freshDeps k given
                · rintro ⟨Object,Value,I,π,models,extras⟩
                  obtain ⟨j,listed,e,e',at_c',at_j,complementary⟩ := clash
                  have here := extras (fun k member => (members k).mpr (.inr member)) c (List.mem_cons_self ..)
                  have there := models.labels x.val
                    (fun k member => (members k).mpr (.inl (by rw [← depsIs]; exact member))) j listed
                  rw [meaning_at P.entries.val wf c.val e at_c'] at here
                  rw [meaning_at P.entries.val wf j.val e' at_j] at there
                  cases e <;> cases e' <;> simp only [Complementary] at complementary <;>
                    first | (subst complementary; exact there here) | (subst complementary; exact here there)
          · obtain ⟨inserted,insertRun,insertSpec⟩ := insert_correct F x c deps
            have clash' : ¬ Clashes P.entries.val F.nodes.val[x.val].label.val c := by rwa [← labelIs]
            cases inserted with
            | none =>
              refine ⟨none,?_,by simp,by simp⟩
              simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,↓reduceIte,alloc.vec.Vec.index_slice_index,
                nodeLookup,bind_ok,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,absent,
                decide_false,Bool.false_eq_true,clashes_correct,clash',insertRun]
            | some F1 =>
              obtain ⟨_,label,joined,labelValue,joinedValue,F1Is⟩ := insertSpec F1 rfl
              obtain ⟨inv1,grows1,others1,new1⟩ := insert_inv P h count F inv x xIn c P.entries.val[c.val] at_c
                literal present clash label joined labelValue F1 F1Is
              have fresh1 : FreshForest F1 fresh.val := by
                refine ⟨?_,by rw [grows1.2.1]; exact freshF.2.1,by rw [grows1.2.2.1]; exact freshF.2.2.1,
                  by rw [grows1.2.2.2.2.1]; exact freshF.2.2.2⟩
                intro y k member
                rw [F1Is] at member
                obtain ⟨_,other,here⟩ := set_node F.nodes x xIn
                  ⟨label,F.nodes.val[x.val].parent,F.nodes.val[x.val].roles,F.nodes.val[x.val].seed,
                    F.nodes.val[x.val].tree,F.nodes.val[x.val].active,F.nodes.val[x.val].done,joined⟩
                by_cases same : y = x.val
                · subst same
                  simp only [nodeDeps] at member
                  rw [here] at member
                  rcases (joinedValue k).mp member with old | given
                  · exact freshF.1 x.val k (by rw [depsIs]; exact old)
                  · exact freshDeps k given
                · apply freshF.1 y k
                  simp only [nodeDeps] at member ⊢
                  rw [other y same] at member
                  exact member
              obtain ⟨r,run,sound,complete⟩ := ih _ smaller next F1 x deps fresh rfl inv1
                ((grows_active grows1 x.val).mpr active) fresh1 freshDeps
                (by
                  intro F' inv' grows' others' holds'
                  apply progress F' inv' (grows_trans grows1 grows')
                    (fun y different => by rw [others' y different,others1 y different])
                  intro c' member
                  rcases List.mem_cons.mp member with rfl | later
                  · exact holds_literal _ _ c' _ at_c literal
                      (grows_label grows' x.val c' (by rw [new1]; exact List.mem_append_right _ (by simp)))
                  · exact holds' c' later)
              refine ⟨r,?_,sound,?_⟩
              · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,↓reduceIte,alloc.vec.Vec.index_slice_index,
                  nodeLookup,bind_ok,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,absent,
                  decide_false,Bool.false_eq_true,clashes_correct,clash',insertRun,run]
              · intro D rejected
                obtain ⟨bound,none⟩ := complete D rejected
                refine ⟨bound,fun model => none ?_⟩
                rw [F1Is]
                exact fullModel_insert P h F x xIn c (pendingList next) deps.val D.val label joined labelValue
                  joinedValue model
      cases entry : P.entries.val[c.val] with
      | Top =>
        have smaller : pendingWeight (pendingList next) < w := by
          rw [← weight,weightIs]; have := pow_pos (show 0 < 3 by omega) c.val; omega
        obtain ⟨r,run,sound,complete⟩ := ih _ smaller next F x deps fresh rfl inv active freshF freshDeps (by
          intro F' inv' grows' others' holds'
          apply progress F' inv' grows' others'
          intro c' member
          rcases List.mem_cons.mp member with rfl | later
          · rw [Holds.eq_def,at_c,entry]; trivial
          · exact holds' c' later)
        refine ⟨r,?_,sound,?_⟩
        · rw [forest.add]
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
            bind_ok,entry,run]
        · intro D rejected
          obtain ⟨bound,none⟩ := complete D rejected
          exact ⟨bound,fun model => none (fullModel_drop P h _ _ _ _ _ _ model)⟩
      | Bottom =>
        refine ⟨some (.Rejected deps),?_,by simp,?_⟩
        · rw [forest.add]
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,lookup,entry]
        · intro D same
          simp only [Option.some.injEq,completion.Outcome.Rejected.injEq] at same
          subst same
          refine ⟨freshDeps,?_⟩
          rintro ⟨Object,Value,I,π,_,extras⟩
          have here := extras (fun k member => member) c (List.mem_cons_self ..)
          rw [meaning_at P.entries.val wf c.val _ at_c,entry] at here
          exact here
      | One a =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [forest.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
      | NotOne a =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [forest.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
      | HasSelf r' =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [forest.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
      | NotSelf r' =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [forest.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
      | And a b =>
        rw [entry] at below
        have aBelow : a.val < c.val := below a.val (by simp [parts])
        have bBelow : b.val < c.val := below b.val (by simp [parts])
        have smaller : pendingWeight (pendingList (.Item a (.Item b next))) < w := by
          rw [← weight,weightIs]
          have := three_pow_lt a.val b.val c.val aBelow bBelow
          simp [pendingWeight,pendingList] at this ⊢
          omega
        obtain ⟨r,run,sound,complete⟩ := ih _ smaller (.Item a (.Item b next)) F x deps fresh rfl inv active
          freshF freshDeps (by
          intro F' inv' grows' others' holds'
          apply progress F' inv' grows' others'
          intro c' member
          rcases List.mem_cons.mp member with rfl | later
          · rw [Holds.eq_def,at_c,entry]
            simp only [dif_pos aBelow,dif_pos bBelow]
            exact ⟨holds' a (by simp [pendingList]),holds' b (by simp [pendingList])⟩
          · exact holds' c' (by simp [pendingList,later]))
        refine ⟨r,?_,sound,?_⟩
        · rw [forest.add]
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
            bind_ok,entry,run]
        · intro D rejected
          obtain ⟨bound,none⟩ := complete D rejected
          refine ⟨bound,fun model => none ?_⟩
          apply fullModel_imply P h F x.val _ _ _ _ _ model
          intro Object Value I z extras c' member
          have both := extras c (List.mem_cons_self ..)
          rw [meaning_at P.entries.val wf c.val _ at_c,entry] at both
          simp only [pendingList,List.mem_cons] at member
          rcases member with rfl | rfl | later
          · exact both.1
          · exact both.2
          · exact extras c' (List.mem_cons_of_mem _ later)
      | Or a b =>
        rw [entry] at below
        have aBelow : a.val < c.val := below a.val (by simp [parts])
        have bBelow : b.val < c.val := below b.val (by simp [parts])
        have smallerLeft : pendingWeight (pendingList (.Item a next)) < w := by
          rw [← weight,weightIs]
          have := Nat.pow_lt_pow_right (show 1 < 3 by omega) aBelow
          simp [pendingWeight,pendingList] at this ⊢
          omega
        have smallerRight : pendingWeight (pendingList (.Item b next)) < w := by
          rw [← weight,weightIs]
          have := Nat.pow_lt_pow_right (show 1 < 3 by omega) bBelow
          simp [pendingWeight,pendingList] at this ⊢
          omega
        have orHolds : ∀ (L : List Usize), (Holds P.entries.val L a.val ∨ Holds P.entries.val L b.val) →
            Holds P.entries.val L c.val := by
          intro L either
          rw [Holds.eq_def,at_c,entry]
          simp only [dif_pos aBelow,dif_pos bBelow]
          exact either
        have branchProgress : ∀ (d : Usize), (∀ (L : List Usize), Holds P.entries.val L d.val →
            Holds P.entries.val L c.val) →
            ∀ F' : forest.Forest, Inv P h count F' → Grows F F' →
              (∀ y, y ≠ x.val → labelOf F'.nodes.val y = labelOf F.nodes.val y) →
              (∀ c' ∈ pendingList (.Item d next), Holds P.entries.val (labelOf F'.nodes.val x.val) c'.val) →
              ForestInv.measure P F' < M := by
          intro d implies F' inv' grows' others' holds'
          apply progress F' inv' grows' others'
          intro c' member
          rcases List.mem_cons.mp member with rfl | later
          · exact implies _ (holds' d (List.mem_cons_self ..))
          · exact holds' c' (List.mem_cons_of_mem _ later)
        have code : forest.add P h F x (.Item c next) deps fresh = forest.branch P h F x a b next deps fresh := by
          rw [forest.add]
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
            bind_ok,entry]
        rw [code]
        apply branch_correct P h count F x a b next deps fresh (c :: pendingList next) freshF freshDeps
        · intro deps' fresh' _ freshDeps'
          have freshF' : FreshForest F fresh'.val := by
            refine ⟨?_,?_,?_,?_⟩
            · intro y k member; have := freshF.1 y k member; omega
            · intro e member k kIn; have := freshF.2.1 e member k kIn; omega
            · intro d member k kIn; have := freshF.2.2.1 d member k kIn; omega
            · intro cap member k kIn; have := freshF.2.2.2 cap member k kIn; omega
          exact ih _ smallerLeft (.Item a next) F x deps' fresh' rfl inv active freshF' freshDeps'
            (branchProgress a (fun L holds => orHolds L (.inl holds)))
        · intro deps' freshDeps'
          exact ih _ smallerRight (.Item b next) F x deps' fresh rfl inv active freshF freshDeps'
            (branchProgress b (fun L holds => orHolds L (.inr holds)))
        · intro Object Value I z extras
          have either := extras c (List.mem_cons_self ..)
          rw [meaning_at P.entries.val wf c.val _ at_c,entry] at either
          exact ⟨either,fun c' member => extras c' (List.mem_cons_of_mem _ member)⟩
      | Atom k =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [forest.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
      | NotAtom k =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [forest.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
      | Exists r' f =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [forest.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
      | Forall r' f =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [forest.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
      | AtLeast m r' f =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [forest.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
      | AtMost m r' f f' =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [forest.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
    · refine ⟨none,?_,by simp,by simp⟩
      rw [forest.add]
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn]

theorem fresh_succ {F : forest.Forest} {fresh fresh' : Nat} (freshF : FreshForest F fresh) (more : fresh ≤ fresh') :
    FreshForest F fresh' := by
  refine ⟨?_,?_,?_,?_⟩
  · intro y k member; have := freshF.1 y k member; omega
  · intro e member k kIn; have := freshF.2.1 e member k kIn; omega
  · intro d member k kIn; have := freshF.2.2.1 d member k kIn; omega
  · intro cap member k kIn; have := freshF.2.2.2 cap member k kIn; omega

/-- A merge terminates; a rejection rules out every model under the rejected
    points that places the two nodes on one element, and those points include
    the ones the merge was given. -/
theorem merge_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (M : Nat)
    (IH : ∀ (F : forest.Forest) (fresh : Usize), ForestInv.measure P F < M → Inv P h count F →
      FreshForest F fresh.val →
      ∃ r, forest.run P h F fresh = .ok r ∧ Answers.{u,v} P h count F 0 [] [] fresh.val r)
    (F : forest.Forest) (source into : Usize) (deps : alloc.vec.Vec Usize) (fresh : Usize)
    (inv : Inv P h count F) (mergeShape : MergeShape F source.val into.val)
    (small : ForestInv.measure P F ≤ M) (freshF : FreshForest F fresh.val)
    (freshDeps : ∀ k ∈ deps.val, k.val < fresh.val) :
    ∃ r, forest.merge P h F source into deps fresh = .ok r ∧
      (r = some .Accepted → ∃ F' : forest.Forest, Inv P h count F' ∧ Complete P h F') ∧
      (∀ D : alloc.vec.Vec Usize, r = some (.Rejected D) → (∀ k ∈ D.val, k.val < fresh.val) ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
          Models P h F I π D.val → Sub deps.val D.val ∧ π source.val ≠ π into.val) := by
  have activeS := mergeShape.2.1
  have sourceIn := active_inside activeS
  have at_s : F.nodes.val[source.val]? = some F.nodes.val[source.val] := List.getElem?_eq_getElem sourceIn
  have lookupS : F.nodes.index_usize source = .ok F.nodes.val[source.val] := by
    simp [alloc.vec.Vec.index_usize,at_s]
  have labelCopy := copy_label_correct F.nodes.val[source.val].label 0#usize (alloc.vec.Vec.new Usize) (by simp)
    (by simp)
  rw [forest.merge]
  simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookupS,
    bind_ok,labelCopy,into_parent_correct]
  -- The rest of the merge, with the label of `source` and, when `into` is its
  -- tree parent, the loops of its edge to add to `into`.
  have tail : ∀ (extra : alloc.vec.Vec Usize) (zero : Usize), zero.val = 0 →
      (∀ c ∈ extra.val, c ∈ F.nodes.val[source.val].label.val ∨
      (F.nodes.val[source.val].tree = true ∧ F.nodes.val[source.val].parent = into ∧
        ∃ s ∈ F.nodes.val[source.val].roles.val, ∃ q, P.entries.val[c.val]? = some (.HasSelf q) ∧
          (q = s ∨ Rowl.Concepts.inv q = s))) →
      ∃ r, (do
          let o ← completion.join deps F.nodes.val[source.val].deps
          match o with
            | none => ok none
            | some joined => do
              let o1 ← forest.merged F source into joined
              match o1 with
                | none => ok none
                | some graph1 => do
                  let p ← forest.pending_from extra zero
                  forest.add P h graph1 into p joined fresh) = .ok r ∧
        (r = some .Accepted → ∃ F' : forest.Forest, Inv P h count F' ∧ Complete P h F') ∧
        (∀ D : alloc.vec.Vec Usize, r = some (.Rejected D) → (∀ k ∈ D.val, k.val < fresh.val) ∧
          ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
            Models P h F I π D.val → Sub deps.val D.val ∧ π source.val ≠ π into.val) := by
    intro extra zero zeroIs extraOk
    obtain ⟨joinedResult,joinRun,joinSpec⟩ := join_correct deps F.nodes.val[source.val].deps
    simp only [joinRun,bind_tc_ok]
    cases joinedResult with
    | none => exact ⟨none,by simp,by simp,by simp⟩
    | some joined =>
    have joinedIs := joinSpec joined rfl
    obtain ⟨mergedResult,mergedRun,mergedSpec⟩ := merged_correct F inv.shape source into joined mergeShape
    simp only [mergedRun,bind_tc_ok]
    cases mergedResult with
    | none => exact ⟨none,by simp,by simp,by simp⟩
    | some G =>
    have merged := mergedSpec G rfl
    have sourceDeps : Sub (nodeDeps F source.val) joined.val := by
      intro k member
      exact (joinedIs k).mpr (.inr (by simpa [nodeDeps,at_s] using member))
    have joinedFresh : ∀ k ∈ joined.val, k.val < fresh.val := by
      intro k member
      rcases (joinedIs k).mp member with given | old
      · exact freshDeps k given
      · exact freshF.1 source.val k (by simp [nodeDeps,at_s,old])
    have invG := merged_inv inv merged mergeShape.2.1
    have smaller := merged_measure inv merged activeS
    obtain ⟨r,run,sound,complete⟩ := add_correct.{u,v} P h count M IH _
      (pendingOf (extra.val.drop zero.val)) G into joined fresh rfl invG
      merged.intoActive (merged_fresh merged freshF joinedFresh) joinedFresh (by
        intro F' inv' grows' _ _
        have := measure_le_grows P grows' invG.nodup
        omega)
    refine ⟨r,by simp only [pending_from_correct,bind_tc_ok,run],sound,?_⟩
    intro D rejected
    obtain ⟨bound,none⟩ := complete D rejected
    refine ⟨bound,?_⟩
    intro Object Value I π models
    by_cases equal : Sub joined.val D.val → π source.val = π into.val
    · exfalso
      obtain ⟨modelsG,extra⟩ := merged_models merged sourceDeps models equal
      apply none
      refine ⟨Object,Value,I,π,modelsG,?_⟩
      intro sub c member
      rw [pendingList_of] at member
      simp only [zeroIs,List.drop_zero] at member
      rcases extraOk c member with listed | ⟨sTree,parentIs,s,sIn,q,at_c,which⟩
      · exact extra sub c (by simp [labelOf,at_s,listed])
      · -- A loop along a role of the edge of `source`, whose ends are now one element.
        have edge := (models.tree source.val _ at_s sTree
          (fun k listed => sub k (sourceDeps k (by simpa [nodeDeps,at_s] using listed)))).1 s sIn
        rw [parentIs,equal sub] at edge
        rw [meaning_at P.entries.val inv.shape.wellFormed c.val _ at_c]
        rcases which with rfl | rfl
        · exact edge
        · exact (relation_inv I q _ _).mp edge
    · obtain ⟨sub,different⟩ := Classical.not_imp.mp equal
      exact ⟨fun k member => sub k ((joinedIs k).mpr (.inl member)),different⟩
  by_cases parentIs : IntoParent F source into
  · simp only [decide_eq_true parentIs,↓reduceIte]
    obtain ⟨ns,ni,at_s',_,sTree,_,parent⟩ := parentIs
    rw [at_s] at at_s'
    cases at_s'
    obtain ⟨loops,loopsRun,loopsSpec⟩ := loops_of_correct P.entries F.nodes.val[source.val].roles 0#usize
      F.nodes.val[source.val].label
    rw [loopsRun]
    simp only [bind_ok]
    cases loops with
    | none => exact ⟨none,by simp,by simp,by simp⟩
    | some label1 =>
      simp only
      apply tail label1 0#usize rfl
      intro c member
      rcases loopsSpec label1 rfl c member with listed | found
      · exact .inl listed
      · exact .inr ⟨sTree,parent,found⟩
  · simp only [decide_eq_false parentIs,Bool.false_eq_true,↓reduceIte]
    exact tail F.nodes.val[source.val].label 0#usize rfl (fun c member => .inl member)

theorem mem_take_succ {α : Type} (l : List α) (i : Nat) (inside : i < l.length) (p : α)
    (member : p ∈ l.take (i + 1)) : p ∈ l.take i ∨ p = l[i] := by
  rw [List.take_add_one,List.getElem?_eq_getElem inside] at member
  simp only [Option.toList_some,List.mem_append,List.mem_singleton] at member
  exact member

/-- Trying the merges of the pairs from `index` on terminates. When every model
    under the points of the rule places some pair on one element, and the
    models under `skipped` place none of the earlier pairs on one element, the
    answer means what `Answers` says. -/
theorem choices_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (M : Nat)
    (IH : ∀ (F : forest.Forest) (fresh : Usize), ForestInv.measure P F < M → Inv P h count F →
      FreshForest F fresh.val →
      ∃ r, forest.run P h F fresh = .ok r ∧ Answers.{u,v} P h count F 0 [] [] fresh.val r)
    (F : forest.Forest) (x : Usize) (pairs : alloc.vec.Vec forest.Pair) (deps : alloc.vec.Vec Usize) (fresh : Usize)
    (inv : Inv P h count F) (small : ForestInv.measure P F ≤ M) (freshF : FreshForest F fresh.val)
    (freshDeps : ∀ k ∈ deps.val, k.val < fresh.val)
    (shapes : ∀ p ∈ pairs.val, MergeShape F (orientOf F x p).1.val (orientOf F x p).2.val)
    (collide : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object)
      (D : List Usize), Sub deps.val D → Models P h F I π D →
        ∃ p ∈ pairs.val, π (orientOf F x p).1.val = π (orientOf F x p).2.val) :
    ∀ (n : Nat) (index : Usize) (skipped : alloc.vec.Vec Usize), pairs.val.length - index.val = n →
      (∀ k ∈ skipped.val, k.val < fresh.val) →
      (∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object)
        (D : List Usize), Sub skipped.val D → Models P h F I π D →
          ∀ p ∈ pairs.val.take index.val, π (orientOf F x p).1.val ≠ π (orientOf F x p).2.val) →
      ∃ r, forest.choices P h F x pairs index deps skipped fresh = .ok r ∧
        Answers.{u,v} P h count F 0 [] [] fresh.val r := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro index skipped remaining freshSkipped excluded
  rw [forest.choices]
  by_cases more : index.val < pairs.val.length
  · have lookup : pairs.index_usize index = .ok pairs.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have pairIn : pairs.val[index.val] ∈ pairs.val := List.getElem_mem more
    obtain ⟨src,dst,orientIs⟩ : ∃ src dst, orientOf F x pairs.val[index.val] = (src,dst) := ⟨_,_,rfl⟩
    have shapeHere : MergeShape F src.val dst.val := by
      have := shapes _ pairIn
      rw [orientIs] at this
      exact this
    by_cases notLast : next.val < pairs.val.length
    · by_cases room : fresh.val < Usize.max
      · obtain ⟨point,pointRun,pointValue⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec (alloc.vec.Vec.new Usize) fresh (by simp; scalar_tac))
        obtain ⟨hereResult,hereRun,hereSpec⟩ := join_correct deps point
        obtain ⟨fresh',advance',freshValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := fresh) (y := 1#usize) (by scalar_tac))
        have freshIs : fresh'.val = fresh.val + 1 := by simpa using freshValue
        cases hereResult with
        | none =>
          refine ⟨none,?_,by simp,by simp⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,orient_correct,orientIs,advance,notLast,
            usize_max_val,room,copy_forest_correct,pointRun,hereRun]
        | some here =>
        have hereMembers : ∀ k, k ∈ here.val ↔ k ∈ deps.val ∨ k = fresh := by
          intro k
          rw [hereSpec here rfl k,pointValue]
          simp
        obtain ⟨r1,run1,sound1,complete1⟩ := merge_correct.{u,v} P h count M IH F src dst here fresh' inv
          shapeHere small (fresh_succ freshF (by omega)) (by
            intro k member
            rw [freshIs]
            rcases (hereMembers k).mp member with given | rfl
            · have := freshDeps k given
              omega
            · omega)
        cases r1 with
        | none =>
          refine ⟨none,?_,by simp,by simp⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,orient_correct,orientIs,advance,notLast,
            usize_max_val,room,copy_forest_correct,pointRun,hereRun,advance',run1]
        | some outcome =>
        cases outcome with
        | Accepted =>
          refine ⟨some .Accepted,?_,fun _ => sound1 rfl,by simp⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,orient_correct,orientIs,advance,notLast,
            usize_max_val,room,copy_forest_correct,pointRun,hereRun,advance',run1]
        | Rejected D1 =>
        obtain ⟨bound1,rules1⟩ := complete1 D1 rfl
        by_cases depends : fresh ∈ D1.val
        · obtain ⟨rest,restRun,restSpec⟩ := without_from_correct D1 fresh 0#usize (alloc.vec.Vec.new Usize)
            (by simp)
          obtain ⟨skippedResult,skippedRun,skippedSpec⟩ := join_correct skipped rest
          cases skippedResult with
          | none =>
            refine ⟨none,?_,by simp,by simp⟩
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,orient_correct,orientIs,advance,notLast,
              usize_max_val,room,copy_forest_correct,pointRun,hereRun,advance',run1,contains_correct,depends,
              restRun,skippedRun]
          | some skipped1 =>
          have skippedMembers : ∀ k, k ∈ skipped1.val ↔ k ∈ skipped.val ∨ (k ∈ D1.val ∧ k ≠ fresh) := by
            intro k
            rw [skippedSpec skipped1 rfl k,restSpec k]
            simp
          obtain ⟨r,run,answers⟩ := ih (n - 1) (by omega) next skipped1 (by omega)
            (by
              intro k member
              rcases (skippedMembers k).mp member with old | ⟨listed,other⟩
              · exact freshSkipped k old
              · have := bound1 k listed
                rw [freshIs] at this
                have : k.val ≠ fresh.val := fun same => other (UScalar.eq_of_val_eq same)
                omega)
            (by
              intro Object Value I π D sub models p member
              rw [nextIs] at member
              rcases mem_take_succ pairs.val index.val more p member with earlier | rfl
              · exact excluded Object Value I π D (fun k listed => sub k ((skippedMembers k).mpr (.inl listed)))
                  models p earlier
              · -- A model under the new skipped points is one under the failure's points.
                have models1 : Models P h F I π D1.val := by
                  apply models_transfer freshF _ models
                  intro k below listed
                  apply sub k
                  apply (skippedMembers k).mpr
                  refine .inr ⟨listed,?_⟩
                  intro same
                  rw [same] at below
                  omega
                rw [orientIs]
                exact (rules1 Object Value I π models1).2)
          refine ⟨r,?_,answers⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,orient_correct,orientIs,advance,notLast,
            usize_max_val,room,copy_forest_correct,pointRun,hereRun,advance',run1,contains_correct,depends,
            restRun,skippedRun,run]
        · refine ⟨some (.Rejected D1),?_,by simp,?_⟩
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,orient_correct,orientIs,advance,notLast,
              usize_max_val,room,copy_forest_correct,pointRun,hereRun,advance',run1,contains_correct,depends]
          intro D same
          simp only [Option.some.injEq,completion.Outcome.Rejected.injEq] at same
          subst same
          refine ⟨?_,?_⟩
          · intro k member
            have bound := bound1 k member
            rw [freshIs] at bound
            have : k.val ≠ fresh.val := fun same => depends (by rw [← UScalar.eq_of_val_eq same]; exact member)
            omega
          · rintro ⟨Object,Value,I,π,models,_⟩
            have := (rules1 Object Value I π models).1 fresh ((hereMembers fresh).mpr (.inr rfl))
            exact depends this
      · refine ⟨none,?_,by simp,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,orient_correct,orientIs,advance,notLast,
          usize_max_val,room]
    · -- The last pair: its merge depends on the points of the earlier failures.
      obtain ⟨lastResult,lastRun,lastSpec⟩ := join_correct deps skipped
      cases lastResult with
      | none =>
        refine ⟨none,?_,by simp,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,orient_correct,orientIs,advance,notLast,lastRun]
      | some last =>
      have lastMembers := lastSpec last rfl
      obtain ⟨r1,run1,sound1,complete1⟩ := merge_correct.{u,v} P h count M IH F src dst last fresh inv
        shapeHere small freshF (by
          intro k member
          rcases (lastMembers k).mp member with given | old
          · exact freshDeps k given
          · exact freshSkipped k old)
      refine ⟨r1,?_,sound1,?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,orient_correct,orientIs,advance,notLast,lastRun,
          run1]
      intro D rejected
      obtain ⟨bound,rules⟩ := complete1 D rejected
      refine ⟨bound,?_⟩
      rintro ⟨Object,Value,I,π,models,_⟩
      obtain ⟨sub,different⟩ := rules Object Value I π models
      obtain ⟨p,member,equal⟩ := collide Object Value I π D.val
        (fun k listed => sub k ((lastMembers k).mpr (.inl listed))) models
      have all : p ∈ pairs.val.take (index.val + 1) := by
        rw [List.take_of_length_le (by omega)]
        exact member
      rcases mem_take_succ pairs.val index.val more p all with earlier | rfl
      · exact excluded Object Value I π D.val (fun k listed => sub k ((lastMembers k).mpr (.inr listed))) models
          p earlier equal
      · rw [orientIs] at equal
        exact different equal
  · -- No pair is left: every model under the points collides somewhere excluded.
    obtain ⟨clashResult,clashRun,clashSpec⟩ := join_correct deps skipped
    cases clashResult with
    | none =>
      refine ⟨none,?_,by simp,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,clashRun]
    | some clash =>
    have clashMembers := clashSpec clash rfl
    refine ⟨some (.Rejected clash),by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,clashRun],by simp,?_⟩
    intro D same
    simp only [Option.some.injEq,completion.Outcome.Rejected.injEq] at same
    subst same
    refine ⟨?_,?_⟩
    · intro k member
      rcases (clashMembers k).mp member with given | old
      · exact freshDeps k given
      · exact freshSkipped k old
    · rintro ⟨Object,Value,I,π,models,_⟩
      obtain ⟨p,member,equal⟩ := collide Object Value I π clash.val
        (fun k listed => (clashMembers k).mpr (.inl listed)) models
      have all : p ∈ pairs.val.take index.val := by
        rw [List.take_of_length_le (by omega)]
        exact member
      exact excluded Object Value I π clash.val (fun k listed => (clashMembers k).mpr (.inr listed)) models p all
        equal

/-- The merge rule for a maximum restriction with too many neighbours satisfying
    its filler terminates and means what `Answers` says: in every model of the
    restriction two of its first `n + 1` counted neighbours coincide, so some
    pair that is not known to differ is merged in every model. -/
theorem merge_rule_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (M : Nat)
    (IH : ∀ (F : forest.Forest) (fresh : Usize), ForestInv.measure P F < M → Inv P h count F →
      FreshForest F fresh.val →
      ∃ r, forest.run P h F fresh = .ok r ∧ Answers.{u,v} P h count F 0 [] [] fresh.val r)
    (F : forest.Forest) (x i fresh : Usize) (inv : Inv P h count F) (small : ForestInv.measure P F ≤ M)
    (freshF : FreshForest F fresh.val) (active : Active F.nodes.val x.val) (member : i ∈ labelOf F.nodes.val x.val)
    (n : Usize) (r : ObjectPropertyExpression) (c c' : Usize)
    (at_i : P.entries.val[i.val]? = some (.AtMost n r c c')) (excess : Excess P h F x.val r c n)
    (unrepeated : Unrepeated P h F x.val r c) :
    ∃ res, forest.merge_rule P h F x i fresh = .ok res ∧ Answers.{u,v} P h count F 0 [] [] fresh.val res := by
  have xIn := active_inside active
  have wf := inv.shape.wellFormed
  have iIn : i.val < P.entries.val.length := (List.getElem?_eq_some_iff.mp at_i).1
  have entryIs : P.entries.val[i.val] = .AtMost n r c c' := by
    rw [List.getElem?_eq_getElem iIn] at at_i
    simpa using at_i
  have lookup : P.entries.index_usize i = .ok (.AtMost n r c c') := by
    simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem iIn,entryIs]
  by_cases room : n.val < Usize.max
  · obtain ⟨listResult,listRun,listSpec⟩ := neighbours_correct P h F x r
    cases listResult with
    | none =>
      refine ⟨none,?_,by simp,by simp⟩
      rw [forest.merge_rule]
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,usize_max_val,room,listRun]
    | some list =>
    obtain ⟨members,nodup⟩ := listSpec list rfl
    obtain ⟨manyResult,manyRun,manySpec⟩ := satisfying_correct P.entries F list c 0#usize (alloc.vec.Vec.new Usize)
    cases manyResult with
    | none =>
      refine ⟨none,?_,by simp,by simp⟩
      rw [forest.merge_rule]
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,usize_max_val,room,listRun,manyRun]
    | some many =>
    have manyIs : many.val = list.val.filter
        (fun y => decide (Holds P.entries.val (labelOf F.nodes.val y.val) c.val)) := by
      simpa using manySpec many rfl
    obtain ⟨bound',advance,boundValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := n) (y := 1#usize) (by scalar_tac))
    have boundIs : bound'.val = n.val + 1 := by simpa using boundValue
    obtain ⟨chosen,chosenRun,chosenIs⟩ := first_nodes_correct many bound' 0#usize (alloc.vec.Vec.new Usize)
      (by simp)
    obtain ⟨ruleResult,ruleRun,ruleSpec⟩ := rule_deps_correct P F x xIn
    cases ruleResult with
    | none =>
      refine ⟨none,?_,by simp,by simp⟩
      rw [forest.merge_rule]
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,usize_max_val,room,listRun,manyRun,advance,
        chosenRun,ruleRun]
    | some deps =>
    obtain ⟨covers,edgeCovers,origin⟩ := ruleSpec deps rfl
    obtain ⟨diffResult,diffRun,diffSpec⟩ := differences_deps_correct F chosen 0#usize deps
    cases diffResult with
    | none =>
      refine ⟨none,?_,by simp,by simp⟩
      rw [forest.merge_rule]
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,usize_max_val,room,listRun,manyRun,advance,
        chosenRun,ruleRun,diffRun]
    | some deps1 =>
    have deps1Members := diffSpec deps1 rfl
    obtain ⟨pairsResult,pairsRun,pairsSpec⟩ := pairs_from_correct F chosen 0#usize (alloc.vec.Vec.new forest.Pair)
    cases pairsResult with
    | none =>
      refine ⟨none,?_,by simp,by simp⟩
      rw [forest.merge_rule]
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,usize_max_val,room,listRun,manyRun,advance,
        chosenRun,ruleRun,diffRun,pairsRun]
    | some pairs =>
    have pairsMembers := pairsSpec pairs rfl
    have chosenVal : chosen.val = many.val.take (n.val + 1) := by
      rw [chosenIs]
      simp [boundIs]
    have manyLong : n.val < many.val.length := by
      rw [manyIs]
      exact (excess_iff P h F x.val r c n list.val members nodup).mp excess
    have chosenLength : chosen.val.length = n.val + 1 := by
      rw [chosenVal,List.length_take]
      omega
    have chosenNodup : chosen.val.Nodup := by
      rw [chosenVal,manyIs]
      exact List.Nodup.sublist (List.take_sublist _ _) (nodup.filter _)
    have chosenProps : ∀ z ∈ chosen.val, Neighbour P h F x.val r z.val ∧
        Holds P.entries.val (labelOf F.nodes.val z.val) c.val := by
      intro z listed
      rw [chosenVal] at listed
      have inMany := List.mem_of_mem_take listed
      rw [manyIs,List.mem_filter] at inMany
      exact ⟨(members z).mp inMany.1,by simpa using inMany.2⟩
    have freshDeps1 : ∀ k ∈ deps1.val, k.val < fresh.val := by
      intro k listed
      rcases (deps1Members k).mp listed with old | ⟨d,dIn,_,_,kIn⟩
      · rcases origin k old with ⟨y,there⟩ | ⟨e,eIn,there⟩
        · exact freshF.1 y k there
        · exact freshF.2.1 e eIn k there
      · exact freshF.2.2.1 d (List.mem_of_mem_drop dIn) k kIn
    -- At a named node, the counted neighbours are no tree nodes that the model may repeat.
    have fine : ∀ y z, y ∈ chosen.val → z ∈ chosen.val → Named F.nodes.val x.val →
        ¬ Repeated F.nodes.val x.val y.val ∧ ¬ Repeated F.nodes.val x.val z.val := by
      intro y z yIn zIn named
      exact ⟨fun repeated => unrepeated named y (chosenProps y yIn).1 repeated (chosenProps y yIn).2,
        fun repeated => unrepeated named z (chosenProps z zIn).1 repeated (chosenProps z zIn).2⟩
    have shapes : ∀ p ∈ pairs.val, MergeShape F (orientOf F x p).1.val (orientOf F x p).2.val := by
      intro p listed
      rcases (pairsMembers p).mp listed with empty | ⟨a,b,ha,hb,_,less,first,second,_⟩
      · simp at empty
      · have different : p.first ≠ p.second := by
          rw [first,second]
          intro same
          have := (List.Nodup.getElem_inj_iff chosenNodup).mp same
          omega
        exact (orient_shape inv.shape x active r p
          (by rw [first]; exact (chosenProps _ (List.getElem_mem ha)).1)
          (by rw [second]; exact (chosenProps _ (List.getElem_mem hb)).1) different
          (by rw [first,second]; exact fun named _ _ => fine _ _ (List.getElem_mem ha) (List.getElem_mem hb) named)).1
    have collide : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object)
        (D : List Usize), Sub deps1.val D → Models P h F I π D →
          ∃ p ∈ pairs.val, π (orientOf F x p).1.val = π (orientOf F x p).2.val := by
      intro Object Value I π D sub models
      have cover : ∀ y, Near P F x.val y → Sub (nodeDeps F y) D :=
        fun y near k listed => sub k ((deps1Members k).mpr (.inl (covers y near k listed)))
      have edgeCover : ∀ e ∈ F.edges.val, (rep F e.from = x ∨ rep F e.to = x) → Sub e.deps.val D :=
        fun e eIn touches k listed => sub k ((deps1Members k).mpr (.inl (edgeCovers e eIn touches k listed)))
      have atMost := models.labels x.val (cover x.val (.inl rfl)) i member
      rw [meaning_at P.entries.val wf i.val _ at_i] at atMost
      simp only [rebuild,denote,Rowl.Owl.AtMost] at atMost
      -- Two of the counted neighbours coincide.
      obtain ⟨a,b,ha,hb,less,equal⟩ : ∃ a b, ∃ (ha : a < chosen.val.length) (hb : b < chosen.val.length),
          a < b ∧ π chosen.val[a].val = π chosen.val[b].val := by
        by_contra noCollision
        apply atMost
        refine ⟨fun k => π (chosen.val[k.val]'(by rw [chosenLength]; exact k.isLt)).val,?_,?_⟩
        · intro k1 k2 same
          apply Fin.ext
          by_contra different
          rcases Nat.lt_or_gt_of_ne different with lt | gt
          · exact noCollision ⟨k1.val,k2.val,_,_,lt,same⟩
          · exact noCollision ⟨k2.val,k1.val,_,_,gt,same.symm⟩
        · intro k
          have inChosen : chosen.val[k.val]'(by rw [chosenLength]; exact k.isLt) ∈ chosen.val :=
            List.getElem_mem _
          obtain ⟨neighbour,holds⟩ := chosenProps _ inChosen
          exact ⟨neighbour_holds models x r _ neighbour cover edgeCover,
            holds_denote P.entries.val wf I _ _
              (models.labels _ (cover _ (neighbour_near P h F x.val r _ neighbour))) c.val holds⟩
      by_cases differ : Differ F chosen.val[a] chosen.val[b]
      · exfalso
        obtain ⟨d,dIn,ends⟩ := differ
        have dDeps : Sub d.deps.val D := by
          intro k kIn
          apply sub k
          apply (deps1Members k).mpr
          refine .inr ⟨d,by simpa using dIn,?_,?_,kIn⟩
          · rcases ends with ⟨l,_⟩ | ⟨l,_⟩
            · rw [l]; exact List.getElem_mem _
            · rw [l]; exact List.getElem_mem _
          · rcases ends with ⟨_,r'⟩ | ⟨_,r'⟩
            · rw [r']; exact List.getElem_mem _
            · rw [r']; exact List.getElem_mem _
        have apart := models.distinct d dIn dDeps
        rcases ends with ⟨l,r'⟩ | ⟨l,r'⟩
        · rw [l,r'] at apart
          exact apart equal
        · rw [l,r'] at apart
          exact apart equal.symm
      · let p : forest.Pair := ⟨chosen.val[a],chosen.val[b]⟩
        have pIn : p ∈ pairs.val := (pairsMembers p).mpr (.inr ⟨a,b,ha,hb,Nat.zero_le _,less,rfl,rfl,differ⟩)
        refine ⟨p,pIn,?_⟩
        have different : p.first ≠ p.second := by
          intro same
          have := (List.Nodup.getElem_inj_iff chosenNodup).mp same
          omega
        rcases orient_either F x p with same | same
        · rw [same]
          exact equal
        · rw [same]
          exact equal.symm
    obtain ⟨res,run,answers⟩ := choices_correct.{u,v} P h count M IH F x pairs deps1 fresh inv small freshF
      freshDeps1 shapes collide _ 0#usize (alloc.vec.Vec.new Usize) rfl (by simp) (by simp)
    refine ⟨res,?_,answers⟩
    rw [forest.merge_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,usize_max_val,room,listRun,manyRun,advance,
      chosenRun,ruleRun,diffRun,pairsRun,run]
  · refine ⟨none,?_,by simp,by simp⟩
    rw [forest.merge_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,usize_max_val,room]

/-- Between at least one and at most `n` elements with a property, there is an
    exact number of them. -/
theorem exactly_between {α : Type u} (Q : α → Prop) (n : Nat) (one : Rowl.Owl.AtLeast 1 Q)
    (most : Rowl.Owl.AtMost n Q) : ∃ k, 1 ≤ k ∧ k ≤ n ∧ Rowl.Owl.Exactly k Q := by
  have found : ∃ j, Rowl.Owl.AtMost j Q := ⟨n,most⟩
  obtain ⟨k,kMost,kMin⟩ : ∃ k, Rowl.Owl.AtMost k Q ∧ ∀ j < k, ¬ Rowl.Owl.AtMost j Q :=
    ⟨Nat.find found,Nat.find_spec found,fun j lt => Nat.find_min found lt⟩
  have kLe : k ≤ n := by
    by_contra more
    exact kMin n (by omega) most
  have kPos : 1 ≤ k := by
    by_contra zero
    have isZero : k = 0 := by omega
    subst isZero
    exact kMost one
  have kLeast : Rowl.Owl.AtLeast k Q := by
    have notBelow := kMin (k - 1) (by omega)
    unfold Rowl.Owl.AtMost at notBelow
    have := not_not.mp notBelow
    rwa [show k - 1 + 1 = k by omega] at this
  exact ⟨k,kPos,kLe,kLeast,kMost⟩

/-- A rejection of the forest with the new named nodes of a guess rules out every
    model of the forest, under the rejected points, in which the node has as
    many counted neighbours as guessed, and those points include the ones the
    new nodes were given. -/
theorem named_rejected {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F F' : forest.Forest}
    {x i : Usize} {n : Usize} {r : ObjectPropertyExpression} {c c' : Usize} {many : Nat}
    {deps : alloc.vec.Vec Usize} {D : List Usize} (inv : Inv P h count F) (made : NamedMade F F' x i r c many deps)
    (at_i : P.entries.val[i.val]? = some (.AtMost n r c c')) (xIn : x.val < F.nodes.val.length)
    (none : ¬ FullModel.{u,v} P h F' 0 [] [] D) :
    ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
      Models P h F I π D → Sub deps.val D ∧
        ¬ Rowl.Owl.Exactly many (fun y => objectRelation I r (π x.val) y ∧ denote I (meaning P.entries.val c.val) y) := by
  intro Object Value I π models
  by_contra notBoth
  apply none
  -- Without the points of the new nodes, or with the right guess, the forest
  -- with the new nodes has a model.
  have placed : ∃ g : Nat → Object, (Sub deps.val D → (∀ k < many, objectRelation I r (π x.val) (g k) ∧
      denote I (meaning P.entries.val c.val) (g k)) ∧ (∀ a < many, ∀ b < many, g a = g b → a = b)) ∧
      (Sub deps.val D → ∀ n' r' d d', P.entries.val[i.val]? = some (.AtMost n' r' d d') →
        Rowl.Owl.AtMost many
          (fun y => objectRelation I r' (π x.val) y ∧ denote I (meaning P.entries.val d.val) y)) := by
    by_cases sub : Sub deps.val D
    · have exactly : Rowl.Owl.Exactly many
          (fun y => objectRelation I r (π x.val) y ∧ denote I (meaning P.entries.val c.val) y) := by
        by_contra wrong
        exact notBoth ⟨sub,wrong⟩
      obtain ⟨⟨f,injective,each⟩,most⟩ := exactly
      refine ⟨fun k => if hk : k < many then f ⟨k,hk⟩ else π x.val,fun _ => ⟨?_,?_⟩,?_⟩
      · intro k kIn
        simp only [dif_pos kIn]
        exact each ⟨k,kIn⟩
      · intro a aIn b bIn same
        simp only [dif_pos aIn,dif_pos bIn] at same
        exact congrArg Fin.val (injective same)
      · intro _ n' r' d d' at_i'
        rw [at_i] at at_i'
        simp only [Option.some.injEq,concept_table.Entry.AtMost.injEq] at at_i'
        obtain ⟨_,rfl,rfl,_⟩ := at_i'
        exact most
    · exact ⟨fun _ => π x.val,fun yes => absurd yes sub,fun yes => absurd yes sub⟩
  obtain ⟨g,witnesses,bounded⟩ := placed
  obtain ⟨π',models'⟩ := named_models inv.shape made xIn models g witnesses bounded
  exact ⟨Object,Value,I,π',models',by simp⟩

theorem atMostCount_le_sum (entries : List concept_table.Entry) (i : Nat) (e : concept_table.Entry)
    (at_i : entries[i]? = some e) : atMostCount e ≤ (entries.map atMostCount).sum := by
  have member : atMostCount e ∈ entries.map atMostCount := List.mem_map.mpr ⟨e,List.mem_of_getElem? at_i,rfl⟩
  exact List.le_sum_of_mem member

/-- Trying the guesses from `many` up to `n` for the number of counted
    neighbours terminates. When every model under the points of the rule has an
    exact number of them between 1 and `n`, and the models under `skipped` none
    of the earlier ones, the answer means what `Answers` says. -/
theorem guesses_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (M : Nat)
    (IH : ∀ (F : forest.Forest) (fresh : Usize), ForestInv.measure P F < M → Inv P h count F →
      FreshForest F fresh.val →
      ∃ r, forest.run P h F fresh = .ok r ∧ Answers.{u,v} P h count F 0 [] [] fresh.val r)
    (F : forest.Forest) (x i n : Usize) (r : ObjectPropertyExpression) (c c' : Usize)
    (at_i : P.entries.val[i.val]? = some (.AtMost n r c c')) (deps : alloc.vec.Vec Usize) (fresh : Usize)
    (inv : Inv P h count F) (small : ForestInv.measure P F ≤ M) (freshF : FreshForest F fresh.val)
    (freshDeps : ∀ k ∈ deps.val, k.val < fresh.val) (activeX : Active F.nodes.val x.val)
    (namedX : Named F.nodes.val x.val) (uncapped : ¬ Capped F x.val i.val)
    (fits : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object)
      (D : List Usize), Sub deps.val D → Models P h F I π D → ∃ k, 1 ≤ k ∧ k ≤ n.val ∧
        Rowl.Owl.Exactly k (fun y => objectRelation I r (π x.val) y ∧ denote I (meaning P.entries.val c.val) y)) :
    ∀ (gap : Nat) (many : Usize) (skipped : alloc.vec.Vec Usize), n.val + 1 - many.val = gap → 1 ≤ many.val →
      (∀ k ∈ skipped.val, k.val < fresh.val) →
      (∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object)
        (D : List Usize), Sub skipped.val D → Models P h F I π D → ∀ k, 1 ≤ k → k < many.val →
          ¬ Rowl.Owl.Exactly k
            (fun y => objectRelation I r (π x.val) y ∧ denote I (meaning P.entries.val c.val) y)) →
      ∃ res, forest.guesses P h F x i r c n many deps skipped fresh = .ok res ∧
        Answers.{u,v} P h count F 0 [] [] fresh.val res := by
  have xIn := active_inside activeX
  have iIn : i.val < P.entries.val.length := (List.getElem?_eq_some_iff.mp at_i).1
  have most : AtMostAt P i.val := ⟨n,r,c,c',at_i⟩
  have nSum : n.val ≤ (P.entries.val.map atMostCount).sum :=
    atMostCount_le_sum P.entries.val i.val _ at_i
  -- Making the new named nodes of a guess keeps the invariant and lightens the forest.
  have makes : ∀ (F' : forest.Forest) (k : Nat) (deps' : alloc.vec.Vec Usize),
      NamedMade F F' x i r c k deps' → k ≤ n.val →
      Inv P h count F' ∧ ForestInv.measure P F' < ForestInv.measure P F := by
    intro F' k deps' made few
    refine ⟨named_inv inv made namedX activeX,named_measure made xIn namedX most iIn uncapped (by omega) ?_⟩
    have := F'.nodes.property
    simp [Usize.max] at this ⊢
    scalar_tac
  intro gap
  induction gap using Nat.strong_induction_on with
  | _ gap ih =>
  intro many skipped remaining positive freshSkipped excluded
  rw [forest.guesses]
  by_cases within : many.val ≤ n.val
  · by_cases notLast : many.val < n.val
    · by_cases room : fresh.val < Usize.max
      · obtain ⟨point,pointRun,pointValue⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec (alloc.vec.Vec.new Usize) fresh (by simp; scalar_tac))
        obtain ⟨hereResult,hereRun,hereSpec⟩ := join_correct deps point
        obtain ⟨fresh',advance',freshValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := fresh) (y := 1#usize) (by scalar_tac))
        have freshIs : fresh'.val = fresh.val + 1 := by simpa using freshValue
        obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := many) (y := 1#usize) (by scalar_tac))
        have nextIs : next.val = many.val + 1 := by simpa using nextValue
        cases hereResult with
        | none =>
          refine ⟨none,?_,by simp,by simp⟩
          simp [UScalar.le_equiv,UScalar.lt_equiv,within,notLast,usize_max_val,room,copy_forest_correct,
            pointRun,hereRun]
        | some here =>
        have hereMembers : ∀ k, k ∈ here.val ↔ k ∈ deps.val ∨ k = fresh := by
          intro k
          rw [hereSpec here rfl k,pointValue]
          simp
        have hereFresh : ∀ k ∈ here.val, k.val < fresh'.val := by
          intro k member
          rw [freshIs]
          rcases (hereMembers k).mp member with given | rfl
          · have := freshDeps k given
            omega
          · omega
        obtain ⟨namedResult,namedRun,namedSpec⟩ := named_correct F x i r c many here
        cases namedResult with
        | none =>
          refine ⟨none,?_,by simp,by simp⟩
          simp [UScalar.le_equiv,UScalar.lt_equiv,within,notLast,usize_max_val,room,copy_forest_correct,
            pointRun,hereRun,namedRun]
        | some F' =>
        have made := namedSpec F' rfl
        obtain ⟨inv',smaller⟩ := makes F' many.val here made within
        have freshF' : FreshForest F' fresh'.val :=
          named_fresh made (fresh_succ freshF (by omega)) hereFresh
        obtain ⟨r1,run1,sound1,complete1⟩ := IH F' fresh' (by omega) inv' freshF'
        cases r1 with
        | none =>
          refine ⟨none,?_,by simp,by simp⟩
          simp [UScalar.le_equiv,UScalar.lt_equiv,within,notLast,usize_max_val,room,copy_forest_correct,
            pointRun,hereRun,namedRun,advance',run1]
        | some outcome =>
        cases outcome with
        | Accepted =>
          refine ⟨some .Accepted,?_,fun _ => sound1 rfl,by simp⟩
          simp [UScalar.le_equiv,UScalar.lt_equiv,within,notLast,usize_max_val,room,copy_forest_correct,
            pointRun,hereRun,namedRun,advance',run1]
        | Rejected D1 =>
        obtain ⟨bound1,none1⟩ := complete1 D1 rfl
        have rules1 := named_rejected inv made at_i xIn none1
        by_cases depends : fresh ∈ D1.val
        · obtain ⟨rest,restRun,restSpec⟩ := without_from_correct D1 fresh 0#usize (alloc.vec.Vec.new Usize)
            (by simp)
          obtain ⟨skippedResult,skippedRun,skippedSpec⟩ := join_correct skipped rest
          cases skippedResult with
          | none =>
            refine ⟨none,?_,by simp,by simp⟩
            simp [UScalar.le_equiv,UScalar.lt_equiv,within,notLast,usize_max_val,room,copy_forest_correct,
              pointRun,hereRun,namedRun,advance',run1,contains_correct,depends,restRun,skippedRun]
          | some skipped1 =>
          have skippedMembers : ∀ k, k ∈ skipped1.val ↔ k ∈ skipped.val ∨ (k ∈ D1.val ∧ k ≠ fresh) := by
            intro k
            rw [skippedSpec skipped1 rfl k,restSpec k]
            simp
          obtain ⟨res,run,answers⟩ := ih (gap - 1) (by omega) next skipped1 (by omega) (by omega)
            (by
              intro k member
              rcases (skippedMembers k).mp member with old | ⟨listed,other⟩
              · exact freshSkipped k old
              · have := bound1 k listed
                rw [freshIs] at this
                have : k.val ≠ fresh.val := fun same => other (UScalar.eq_of_val_eq same)
                omega)
            (by
              intro Object Value I π D sub models k low high
              rw [nextIs] at high
              by_cases earlier : k < many.val
              · exact excluded Object Value I π D (fun j listed => sub j ((skippedMembers j).mpr (.inl listed)))
                  models k low earlier
              · have kIs : k = many.val := by omega
                subst kIs
                -- A model under the new skipped points is one under the failure's points.
                have models1 : Models P h F I π D1.val := by
                  apply models_transfer freshF _ models
                  intro j below listed
                  apply sub j
                  apply (skippedMembers j).mpr
                  refine .inr ⟨listed,?_⟩
                  intro same
                  rw [same] at below
                  omega
                exact (rules1 Object Value I π models1).2)
          refine ⟨res,?_,answers⟩
          simp [UScalar.le_equiv,UScalar.lt_equiv,within,notLast,usize_max_val,room,copy_forest_correct,
            pointRun,hereRun,namedRun,advance',run1,contains_correct,depends,restRun,skippedRun,advance,run]
        · refine ⟨some (.Rejected D1),?_,by simp,?_⟩
          · simp [UScalar.le_equiv,UScalar.lt_equiv,within,notLast,usize_max_val,room,copy_forest_correct,
              pointRun,hereRun,namedRun,advance',run1,contains_correct,depends]
          intro D same
          simp only [Option.some.injEq,completion.Outcome.Rejected.injEq] at same
          subst same
          refine ⟨?_,?_⟩
          · intro k member
            have bound := bound1 k member
            rw [freshIs] at bound
            have : k.val ≠ fresh.val := fun same => depends (by rw [← UScalar.eq_of_val_eq same]; exact member)
            omega
          · rintro ⟨Object,Value,I,π,models,_⟩
            have := (rules1 Object Value I π models).1 fresh ((hereMembers fresh).mpr (.inr rfl))
            exact depends this
      · refine ⟨none,?_,by simp,by simp⟩
        simp [UScalar.le_equiv,UScalar.lt_equiv,within,notLast,usize_max_val,room]
    · -- The last guess: its nodes depend on the points of the earlier failures.
      have isLast : many.val = n.val := by omega
      obtain ⟨lastResult,lastRun,lastSpec⟩ := join_correct deps skipped
      cases lastResult with
      | none =>
        refine ⟨none,?_,by simp,by simp⟩
        simp [UScalar.le_equiv,UScalar.lt_equiv,within,notLast,lastRun]
      | some last =>
      have lastMembers := lastSpec last rfl
      have lastFresh : ∀ k ∈ last.val, k.val < fresh.val := by
        intro k member
        rcases (lastMembers k).mp member with given | old
        · exact freshDeps k given
        · exact freshSkipped k old
      obtain ⟨namedResult,namedRun,namedSpec⟩ := named_correct F x i r c many last
      cases namedResult with
      | none =>
        refine ⟨none,?_,by simp,by simp⟩
        simp [UScalar.le_equiv,UScalar.lt_equiv,within,notLast,lastRun,namedRun]
      | some F' =>
      have made := namedSpec F' rfl
      obtain ⟨inv',smaller⟩ := makes F' many.val last made within
      obtain ⟨r1,run1,sound1,complete1⟩ := IH F' fresh (by omega) inv' (named_fresh made freshF lastFresh)
      refine ⟨r1,?_,sound1,?_⟩
      · simp [UScalar.le_equiv,UScalar.lt_equiv,within,notLast,lastRun,namedRun,run1]
      intro D rejected
      obtain ⟨bound,none⟩ := complete1 D rejected
      refine ⟨bound,?_⟩
      rintro ⟨Object,Value,I,π,models,_⟩
      obtain ⟨sub,wrong⟩ := named_rejected inv made at_i xIn none Object Value I π models
      obtain ⟨k,low,high,exactly⟩ := fits Object Value I π D.val
        (fun j listed => sub j ((lastMembers j).mpr (.inl listed))) models
      by_cases earlier : k < many.val
      · exact excluded Object Value I π D.val (fun j listed => sub j ((lastMembers j).mpr (.inr listed))) models
          k low earlier exactly
      · have kIs : k = many.val := by omega
        rw [kIs] at exactly
        exact wrong exactly
  · -- No guess is left: every model under the points has an excluded number.
    obtain ⟨clashResult,clashRun,clashSpec⟩ := join_correct deps skipped
    cases clashResult with
    | none =>
      refine ⟨none,?_,by simp,by simp⟩
      simp [UScalar.le_equiv,UScalar.lt_equiv,within,clashRun]
    | some clash =>
    have clashMembers := clashSpec clash rfl
    refine ⟨some (.Rejected clash),by simp [UScalar.le_equiv,UScalar.lt_equiv,within,clashRun],by simp,?_⟩
    intro D same
    simp only [Option.some.injEq,completion.Outcome.Rejected.injEq] at same
    subst same
    refine ⟨?_,?_⟩
    · intro k member
      rcases (clashMembers k).mp member with given | old
      · exact freshDeps k given
      · exact freshSkipped k old
    · rintro ⟨Object,Value,I,π,models,_⟩
      obtain ⟨k,low,high,exactly⟩ := fits Object Value I π clash.val
        (fun j listed => (clashMembers j).mpr (.inl listed)) models
      exact excluded Object Value I π clash.val (fun j listed => (clashMembers j).mpr (.inr listed)) models
        k low (by omega) exactly

/-- The rule for a maximum restriction of a named node that counts a neighbour
    the model may repeat, without a bound from new named nodes, terminates and
    means what `Answers` says: every model of the restriction has between 1 and
    `n` counted neighbours, so some guess is right in every model. -/
theorem name_rule_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (M : Nat)
    (IH : ∀ (F : forest.Forest) (fresh : Usize), ForestInv.measure P F < M → Inv P h count F →
      FreshForest F fresh.val →
      ∃ r, forest.run P h F fresh = .ok r ∧ Answers.{u,v} P h count F 0 [] [] fresh.val r)
    (F : forest.Forest) (x i fresh : Usize) (inv : Inv P h count F) (small : ForestInv.measure P F ≤ M)
    (freshF : FreshForest F fresh.val) (active : Active F.nodes.val x.val) (member : i ∈ labelOf F.nodes.val x.val)
    (n : Usize) (r : ObjectPropertyExpression) (c c' : Usize)
    (at_i : P.entries.val[i.val]? = some (.AtMost n r c c')) (repeated : ¬ Unrepeated P h F x.val r c)
    (uncapped : ∀ cap ∈ F.caps.val, ¬ (cap.node = x ∧ cap.restriction = i)) :
    ∃ res, forest.name_rule P h F x i fresh = .ok res ∧ Answers.{u,v} P h count F 0 [] [] fresh.val res := by
  have xIn := active_inside active
  have wf := inv.shape.wellFormed
  have iIn : i.val < P.entries.val.length := (List.getElem?_eq_some_iff.mp at_i).1
  have entryIs : P.entries.val[i.val] = .AtMost n r c c' := by
    rw [List.getElem?_eq_getElem iIn] at at_i
    simpa using at_i
  have lookup : P.entries.index_usize i = .ok (.AtMost n r c c') := by
    simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem iIn,entryIs]
  -- The named node and a counted neighbour the model may repeat.
  obtain ⟨namedX,found⟩ := Classical.not_imp.mp repeated
  obtain ⟨y,found⟩ := Classical.not_forall.mp found
  obtain ⟨neighbour,found⟩ := Classical.not_imp.mp found
  obtain ⟨_,holdsY⟩ := Classical.not_imp.mp found
  have holdsY : Holds P.entries.val (labelOf F.nodes.val y.val) c.val := not_not.mp holdsY
  have notCapped : ¬ Capped F x.val i.val := by
    rintro ⟨cap,listed,node,restriction⟩
    exact uncapped cap listed ⟨UScalar.eq_of_val_eq node,UScalar.eq_of_val_eq restriction⟩
  obtain ⟨ruleResult,ruleRun,ruleSpec⟩ := rule_deps_correct P F x xIn
  cases ruleResult with
  | none =>
    refine ⟨none,?_,by simp,by simp⟩
    rw [forest.name_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,ruleRun]
  | some deps =>
  obtain ⟨covers,edgeCovers,origin⟩ := ruleSpec deps rfl
  have freshDeps : ∀ k ∈ deps.val, k.val < fresh.val := by
    intro k listed
    rcases origin k listed with ⟨z,there⟩ | ⟨e,eIn,there⟩
    · exact freshF.1 z k there
    · exact freshF.2.1 e eIn k there
  have fits : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object)
      (D : List Usize), Sub deps.val D → Models P h F I π D → ∃ k, 1 ≤ k ∧ k ≤ n.val ∧
        Rowl.Owl.Exactly k (fun z => objectRelation I r (π x.val) z ∧ denote I (meaning P.entries.val c.val) z) := by
    intro Object Value I π D sub models
    have cover : ∀ z, Near P F x.val z → Sub (nodeDeps F z) D :=
      fun z near k listed => sub k (covers z near k listed)
    have edgeCover : ∀ e ∈ F.edges.val, (rep F e.from = x ∨ rep F e.to = x) → Sub e.deps.val D :=
      fun e eIn touches k listed => sub k (edgeCovers e eIn touches k listed)
    have atMost := models.labels x.val (cover x.val (.inl rfl)) i member
    rw [meaning_at P.entries.val wf i.val _ at_i] at atMost
    simp only [rebuild,denote] at atMost
    apply exactly_between _ n.val _ atMost
    refine ⟨fun _ => π y.val,fun a b _ => Subsingleton.elim a b,fun _ => ⟨?_,?_⟩⟩
    · exact neighbour_holds models x r _ neighbour cover edgeCover
    · exact holds_denote P.entries.val wf I _ _
        (models.labels _ (cover _ (neighbour_near P h F x.val r _ neighbour))) c.val holdsY
  obtain ⟨res,run,answers⟩ := guesses_correct.{u,v} P h count M IH F x i n r c c' at_i deps fresh inv small freshF
    freshDeps active namedX notCapped fits _ 1#usize (alloc.vec.Vec.new Usize) rfl (by simp) (by simp)
    (by intro _ _ _ _ _ _ _ k low high; simp at high; omega)
  refine ⟨res,?_,answers⟩
  rw [forest.name_rule]
  simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,ruleRun,run]

/-- The merge for a maximum restriction of a named node with a bound from new
    named nodes that counts a neighbour the model may repeat terminates and
    means what `Answers` says: in every model of the bound, two of its first
    `bound` counted named neighbours and that neighbour coincide, so some pair
    that is not known to differ is merged in every model. -/
theorem capped_rule_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (M : Nat)
    (IH : ∀ (F : forest.Forest) (fresh : Usize), ForestInv.measure P F < M → Inv P h count F →
      FreshForest F fresh.val →
      ∃ r, forest.run P h F fresh = .ok r ∧ Answers.{u,v} P h count F 0 [] [] fresh.val r)
    (F : forest.Forest) (x i fresh : Usize) (inv : Inv P h count F) (small : ForestInv.measure P F ≤ M)
    (freshF : FreshForest F fresh.val) (active : Active F.nodes.val x.val)
    (n : Usize) (r : ObjectPropertyExpression) (c c' : Usize)
    (at_i : P.entries.val[i.val]? = some (.AtMost n r c c')) :
    ∃ res, forest.capped_rule P h F x i fresh = .ok res ∧ Answers.{u,v} P h count F 0 [] [] fresh.val res := by
  have xIn := active_inside active
  have wf := inv.shape.wellFormed
  have iIn : i.val < P.entries.val.length := (List.getElem?_eq_some_iff.mp at_i).1
  have entryIs : P.entries.val[i.val] = .AtMost n r c c' := by
    rw [List.getElem?_eq_getElem iIn] at at_i
    simpa using at_i
  have lookup : P.entries.index_usize i = .ok (.AtMost n r c c') := by
    simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem iIn,entryIs]
  obtain ⟨capResult,capRun,capFound,_⟩ := cap_at_correct F.caps x i 0#usize
  cases capResult with
  | none =>
    refine ⟨none,?_,by simp,by simp⟩
    rw [forest.capped_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,capRun]
  | some k =>
  obtain ⟨kIn,kNode,kRestriction⟩ := capFound k rfl
  have capLookup : F.caps.index_usize k = .ok F.caps.val[k.val] := by
    simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem kIn]
  have capIn : F.caps.val[k.val] ∈ F.caps.val := List.getElem_mem kIn
  obtain ⟨listResult,listRun,listSpec⟩ := neighbours_correct P h F x r
  cases listResult with
  | none =>
    refine ⟨none,?_,by simp,by simp⟩
    rw [forest.capped_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,capRun,listRun]
  | some list =>
  obtain ⟨members,nodup⟩ := listSpec list rfl
  obtain ⟨manyResult,manyRun,manySpec⟩ := satisfying_correct P.entries F list c 0#usize (alloc.vec.Vec.new Usize)
  cases manyResult with
  | none =>
    refine ⟨none,?_,by simp,by simp⟩
    rw [forest.capped_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,capRun,listRun,manyRun]
  | some many =>
  have manyIs : many.val = list.val.filter
      (fun y => decide (Holds P.entries.val (labelOf F.nodes.val y.val) c.val)) := by
    simpa using manySpec many rfl
  obtain ⟨namedResult,namedRun,namedSpec⟩ := named_of_correct F many 0#usize (alloc.vec.Vec.new Usize)
  cases namedResult with
  | none =>
    refine ⟨none,?_,by simp,by simp⟩
    rw [forest.capped_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,capRun,listRun,manyRun,namedRun]
  | some named =>
  have namedIs : named.val = many.val.filter
      (fun y => decide (∃ m, F.nodes.val[y.val]? = some m ∧ m.tree = false)) := by
    simpa using namedSpec named rfl
  obtain ⟨chosen,chosenRun,chosenIs⟩ := first_nodes_correct named F.caps.val[k.val].bound 0#usize
    (alloc.vec.Vec.new Usize) (by simp)
  have chosenVal : chosen.val = named.val.take F.caps.val[k.val].bound.val := by
    rw [chosenIs]
    simp
  by_cases short : chosen.val.length < F.caps.val[k.val].bound.val
  · refine ⟨none,?_,by simp,by simp⟩
    rw [forest.capped_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,capRun,listRun,manyRun,namedRun,
      alloc.vec.Vec.index_slice_index,capLookup,chosenRun,short]
  obtain ⟨otherResult,otherRun,otherFound,_⟩ := first_repeated_correct F many x 0#usize
  cases otherResult with
  | none =>
    refine ⟨none,?_,by simp,by simp⟩
    rw [forest.capped_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,capRun,listRun,manyRun,namedRun,
      alloc.vec.Vec.index_slice_index,capLookup,chosenRun,short,otherRun]
  | some other =>
  obtain ⟨otherIn,otherRepeated⟩ := otherFound other rfl
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at otherIn
  by_cases room : chosen.val.length < Usize.max
  swap
  · refine ⟨none,?_,by simp,by simp⟩
    rw [forest.capped_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,capRun,listRun,manyRun,namedRun,
      alloc.vec.Vec.index_slice_index,capLookup,chosenRun,short,otherRun,usize_max_val,room]
  obtain ⟨chosen1,push,chosen1Is⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec chosen other room)
  obtain ⟨ruleResult,ruleRun,ruleSpec⟩ := rule_deps_correct P F x xIn
  cases ruleResult with
  | none =>
    refine ⟨none,?_,by simp,by simp⟩
    rw [forest.capped_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,capRun,listRun,manyRun,namedRun,
      alloc.vec.Vec.index_slice_index,capLookup,chosenRun,short,otherRun,usize_max_val,room,push,ruleRun]
  | some deps =>
  obtain ⟨covers,edgeCovers,origin⟩ := ruleSpec deps rfl
  obtain ⟨joinResult,joinRun,joinSpec⟩ := join_correct deps F.caps.val[k.val].deps
  cases joinResult with
  | none =>
    refine ⟨none,?_,by simp,by simp⟩
    rw [forest.capped_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,capRun,listRun,manyRun,namedRun,
      alloc.vec.Vec.index_slice_index,capLookup,chosenRun,short,otherRun,usize_max_val,room,push,ruleRun,joinRun]
  | some deps0 =>
  have deps0Members := joinSpec deps0 rfl
  obtain ⟨diffResult,diffRun,diffSpec⟩ := differences_deps_correct F chosen1 0#usize deps0
  cases diffResult with
  | none =>
    refine ⟨none,?_,by simp,by simp⟩
    rw [forest.capped_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,capRun,listRun,manyRun,namedRun,
      alloc.vec.Vec.index_slice_index,capLookup,chosenRun,short,otherRun,usize_max_val,room,push,ruleRun,joinRun,
      diffRun]
  | some deps1 =>
  have deps1Members := diffSpec deps1 rfl
  obtain ⟨pairsResult,pairsRun,pairsSpec⟩ := pairs_from_correct F chosen1 0#usize (alloc.vec.Vec.new forest.Pair)
  cases pairsResult with
  | none =>
    refine ⟨none,?_,by simp,by simp⟩
    rw [forest.capped_rule]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,capRun,listRun,manyRun,namedRun,
      alloc.vec.Vec.index_slice_index,capLookup,chosenRun,short,otherRun,usize_max_val,room,push,ruleRun,joinRun,
      diffRun,pairsRun]
  | some pairs =>
  have pairsMembers := pairsSpec pairs rfl
  -- The chosen nodes: the first `bound` named counted neighbours and the repeated one.
  have chosenLength : chosen1.val.length = F.caps.val[k.val].bound.val + 1 := by
    rw [chosen1Is]
    have : chosen.val.length ≤ F.caps.val[k.val].bound.val := by
      rw [chosenVal,List.length_take]
      omega
    simp
    omega
  have namedIn : ∀ z ∈ chosen.val, z ∈ many.val ∧ ∃ m, F.nodes.val[z.val]? = some m ∧ m.tree = false := by
    intro z listed
    rw [chosenVal] at listed
    have inNamed := List.mem_of_mem_take listed
    rw [namedIs,List.mem_filter] at inNamed
    exact ⟨inNamed.1,by simpa using inNamed.2⟩
  have chosenProps : ∀ z ∈ chosen1.val, Neighbour P h F x.val r z.val ∧
      Holds P.entries.val (labelOf F.nodes.val z.val) c.val := by
    intro z listed
    rw [chosen1Is] at listed
    have inMany : z ∈ many.val := by
      rcases List.mem_append.mp listed with old | new
      · exact (namedIn z old).1
      · rw [List.mem_singleton] at new
        rw [new]
        exact otherIn
    rw [manyIs,List.mem_filter] at inMany
    exact ⟨(members z).mp inMany.1,by simpa using inMany.2⟩
  -- Only the repeated neighbour is a tree node.
  have treeIs : ∀ z ∈ chosen1.val, (∃ m, F.nodes.val[z.val]? = some m ∧ m.tree = true) → z = other := by
    intro z listed ⟨m,at_z,tree⟩
    rw [chosen1Is] at listed
    rcases List.mem_append.mp listed with old | new
    · obtain ⟨_,m',at_z',root⟩ := namedIn z old
      rw [at_z] at at_z'
      cases at_z'
      rw [tree] at root
      cases root
    · exact List.mem_singleton.mp new
  have chosenNodup : chosen1.val.Nodup := by
    rw [chosen1Is]
    apply List.nodup_append.mpr
    refine ⟨?_,List.nodup_singleton _,?_⟩
    · rw [chosenVal,namedIs,manyIs]
      exact List.Nodup.sublist (List.take_sublist _ _) ((nodup.filter _).filter _)
    · intro a listed b single same
      rw [List.mem_singleton] at single
      subst single
      subst same
      obtain ⟨_,m,at_a,root⟩ := namedIn _ listed
      obtain ⟨m',at_a',tree,_⟩ := otherRepeated
      rw [at_a] at at_a'
      cases at_a'
      rw [root] at tree
      cases tree
  have freshDeps1 : ∀ k ∈ deps1.val, k.val < fresh.val := by
    intro j listed
    rcases (deps1Members j).mp listed with old | ⟨d,dIn,_,_,jIn⟩
    · rcases (deps0Members j).mp old with rule | capDep
      · rcases origin j rule with ⟨y,there⟩ | ⟨e,eIn,there⟩
        · exact freshF.1 y j there
        · exact freshF.2.1 e eIn j there
      · exact freshF.2.2.2 _ capIn j capDep
    · exact freshF.2.2.1 d (List.mem_of_mem_drop dIn) j jIn
  have shapes : ∀ p ∈ pairs.val, MergeShape F (orientOf F x p).1.val (orientOf F x p).2.val := by
    intro p listed
    rcases (pairsMembers p).mp listed with empty | ⟨a,b,ha,hb,_,less,first,second,_⟩
    · simp at empty
    · have different : p.first ≠ p.second := by
        rw [first,second]
        intro same
        have := (List.Nodup.getElem_inj_iff chosenNodup).mp same
        omega
      refine (orient_shape inv.shape x active r p
        (by rw [first]; exact (chosenProps _ (List.getElem_mem ha)).1)
        (by rw [second]; exact (chosenProps _ (List.getElem_mem hb)).1) different ?_).1
      intro _ firstTree secondTree
      exfalso
      rw [first] at firstTree
      rw [second] at secondTree
      apply different
      rw [first,second,treeIs _ (List.getElem_mem ha) firstTree,treeIs _ (List.getElem_mem hb) secondTree]
  have collide : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object)
      (D : List Usize), Sub deps1.val D → Models P h F I π D →
        ∃ p ∈ pairs.val, π (orientOf F x p).1.val = π (orientOf F x p).2.val := by
    intro Object Value I π D sub models
    have cover : ∀ y, Near P F x.val y → Sub (nodeDeps F y) D :=
      fun y near j listed => sub j ((deps1Members j).mpr (.inl ((deps0Members j).mpr (.inl (covers y near j listed)))))
    have edgeCover : ∀ e ∈ F.edges.val, (rep F e.from = x ∨ rep F e.to = x) → Sub e.deps.val D :=
      fun e eIn touches j listed =>
        sub j ((deps1Members j).mpr (.inl ((deps0Members j).mpr (.inl (edgeCovers e eIn touches j listed)))))
    have capSub : Sub F.caps.val[k.val].deps.val D :=
      fun j listed => sub j ((deps1Members j).mpr (.inl ((deps0Members j).mpr (.inr listed))))
    have atMost := models.caps _ capIn capSub n r c c' (by rw [kRestriction]; exact at_i)
    rw [kNode] at atMost
    simp only [Rowl.Owl.AtMost] at atMost
    -- Two of the chosen neighbours coincide.
    obtain ⟨a,b,ha,hb,less,equal⟩ : ∃ a b, ∃ (ha : a < chosen1.val.length) (hb : b < chosen1.val.length),
        a < b ∧ π chosen1.val[a].val = π chosen1.val[b].val := by
      by_contra noCollision
      apply atMost
      refine ⟨fun j => π (chosen1.val[j.val]'(by rw [chosenLength]; exact j.isLt)).val,?_,?_⟩
      · intro j1 j2 same
        apply Fin.ext
        by_contra different
        rcases Nat.lt_or_gt_of_ne different with lt | gt
        · exact noCollision ⟨j1.val,j2.val,_,_,lt,same⟩
        · exact noCollision ⟨j2.val,j1.val,_,_,gt,same.symm⟩
      · intro j
        have inChosen : chosen1.val[j.val]'(by rw [chosenLength]; exact j.isLt) ∈ chosen1.val :=
          List.getElem_mem _
        obtain ⟨neighbour,holds⟩ := chosenProps _ inChosen
        exact ⟨neighbour_holds models x r _ neighbour cover edgeCover,
          holds_denote P.entries.val wf I _ _
            (models.labels _ (cover _ (neighbour_near P h F x.val r _ neighbour))) c.val holds⟩
    by_cases differ : Differ F chosen1.val[a] chosen1.val[b]
    · exfalso
      obtain ⟨d,dIn,ends⟩ := differ
      have dDeps : Sub d.deps.val D := by
        intro j jIn
        apply sub j
        apply (deps1Members j).mpr
        refine .inr ⟨d,by simpa using dIn,?_,?_,jIn⟩
        · rcases ends with ⟨l,_⟩ | ⟨l,_⟩
          · rw [l]; exact List.getElem_mem _
          · rw [l]; exact List.getElem_mem _
        · rcases ends with ⟨_,r'⟩ | ⟨_,r'⟩
          · rw [r']; exact List.getElem_mem _
          · rw [r']; exact List.getElem_mem _
      have apart := models.distinct d dIn dDeps
      rcases ends with ⟨l,r'⟩ | ⟨l,r'⟩
      · rw [l,r'] at apart
        exact apart equal
      · rw [l,r'] at apart
        exact apart equal.symm
    · let p : forest.Pair := ⟨chosen1.val[a],chosen1.val[b]⟩
      have pIn : p ∈ pairs.val := (pairsMembers p).mpr (.inr ⟨a,b,ha,hb,Nat.zero_le _,less,rfl,rfl,differ⟩)
      refine ⟨p,pIn,?_⟩
      have different : p.first ≠ p.second := by
        intro same
        have := (List.Nodup.getElem_inj_iff chosenNodup).mp same
        omega
      rcases orient_either F x p with same | same
      · rw [same]
        exact equal
      · rw [same]
        exact equal.symm
  obtain ⟨res,run,answers⟩ := choices_correct.{u,v} P h count M IH F x pairs deps1 fresh inv small freshF
    freshDeps1 shapes collide _ 0#usize (alloc.vec.Vec.new Usize) rfl (by simp) (by simp)
  refine ⟨res,?_,answers⟩
  rw [forest.capped_rule]
  simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,iIn,lookup,capRun,listRun,manyRun,namedRun,
    alloc.vec.Vec.index_slice_index,capLookup,chosenRun,short,otherRun,usize_max_val,room,push,ruleRun,joinRun,
    diffRun,pairsRun,run]

/-- Expanding a restriction of an active unblocked node, then running on,
    terminates and means what `Answers` says. -/
theorem create_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (M : Nat)
    (IH : ∀ (F : forest.Forest) (fresh : Usize), ForestInv.measure P F < M → Inv P h count F →
      FreshForest F fresh.val →
      ∃ r, forest.run P h F fresh = .ok r ∧ Answers.{u,v} P h count F 0 [] [] fresh.val r)
    (F : forest.Forest) (x i fresh : Usize) (inv : Inv P h count F) (small : ForestInv.measure P F ≤ M)
    (freshF : FreshForest F fresh.val) (active : Active F.nodes.val x.val) (free : ¬ Blocked F.nodes.val x.val)
    (member : i ∈ labelOf F.nodes.val x.val) (notDone : i ∉ doneOf F.nodes.val x.val) :
    ∃ r, forest.create P h F x i fresh = .ok r ∧ Answers.{u,v} P h count F 0 [] [] fresh.val r := by
  rw [forest.create]
  obtain ⟨r1,run1,spec1⟩ := expanded_correct P.entries F x i
  cases r1 with
  | none => exact ⟨none,by simp [run1],by simp,by simp⟩
  | some F' =>
  obtain ⟨e,role,filler,cnt,nx,at_i,gen,created⟩ := spec1 F' rfl
  have listed := generator_listed P.entries.val i.val e at_i role filler cnt gen
  have few := generator_count_le P.entries.val i.val e at_i role filler cnt gen
  have inv' := created_inv inv created active member notDone listed
  have smaller := created_measure inv created active free member notDone few
  obtain ⟨r,run,sound,complete⟩ := IH F' fresh (by omega) inv' (created_fresh created freshF)
  refine ⟨r,by simp [run1,run],sound,?_⟩
  intro D rejected
  obtain ⟨bound,none⟩ := complete D rejected
  refine ⟨bound,?_⟩
  rintro ⟨Object,Value,I,π,models,_⟩
  obtain ⟨π',models'⟩ := created_models inv.shape created e at_i gen member models
  exact none ⟨Object,Value,I,π',models',by simp⟩

/-- The nominal rule for a nominal of an active node whose named node is another
    node terminates and means what `Answers` says: every model under the points
    of both nodes places them on the individual of the nominal, so a recorded
    difference between them is a clash; otherwise the node is merged into the
    named node of the nominal. -/
theorem nominal_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (M : Nat)
    (IH : ∀ (F : forest.Forest) (fresh : Usize), ForestInv.measure P F < M → Inv P h count F →
      FreshForest F fresh.val →
      ∃ r, forest.run P h F fresh = .ok r ∧ Answers.{u,v} P h count F 0 [] [] fresh.val r)
    (F : forest.Forest) (x named fresh : Usize) (inv : Inv P h count F) (small : ForestInv.measure P F ≤ M)
    (freshF : FreshForest F fresh.val) (active : Active F.nodes.val x.val) (i : Usize)
    (member : i ∈ labelOf F.nodes.val x.val) (a : Individual) (at_i : P.entries.val[i.val]? = some (.One a))
    (namedIs : NominalRoot P F a = some named) (different : named ≠ x) :
    ∃ res, forest.nominal P h F x named fresh = .ok res ∧ Answers.{u,v} P h count F 0 [] [] fresh.val res := by
  have xIn := active_inside active
  obtain ⟨q,qIn,names,repIs⟩ := nominalRoot_some namedIs
  obtain ⟨namedBelow,activeNamed⟩ := rep_in inv.shape q.node (inv.shape.requirements q qIn)
  rw [repIs] at namedBelow activeNamed
  have namedIn := active_inside activeNamed
  have at_x : F.nodes.val[x.val]? = some F.nodes.val[x.val] := List.getElem?_eq_getElem xIn
  have at_named : F.nodes.val[named.val]? = some F.nodes.val[named.val] := List.getElem?_eq_getElem namedIn
  have lookupX : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
    simp [alloc.vec.Vec.index_usize,at_x]
  have lookupNamed : F.nodes.index_usize named = .ok F.nodes.val[named.val] := by
    simp [alloc.vec.Vec.index_usize,at_named]
  have xDeps : nodeDeps F x.val = F.nodes.val[x.val].deps.val := by simp [nodeDeps,at_x]
  have namedDeps : nodeDeps F named.val = F.nodes.val[named.val].deps.val := by simp [nodeDeps,at_named]
  have xActive : F.nodes.val[x.val].active = true := by
    obtain ⟨n,at_n,yes⟩ := active
    rw [at_x,Option.some.injEq] at at_n
    rw [at_n]
    exact yes
  have apart : x.val ≠ named.val := fun same => different (UScalar.eq_of_val_eq same.symm)
  -- Every model under the points of both nodes places them on the individual.
  have meets : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object)
      (D : List Usize), Sub (nodeDeps F x.val) D → Sub (nodeDeps F named.val) D → Models P h F I π D →
        π x.val = π named.val := by
    intro Object Value I π D subX subNamed models
    have here := models.labels x.val subX i member
    rw [meaning_at P.entries.val inv.shape.wellFormed i.val _ at_i] at here
    have there := models.requirements q qIn
    rw [meaning_at P.entries.val inv.shape.wellFormed q.concept.val _ names] at there
    have same := models.same q.node (by rw [repIs]; exact subNamed)
    rw [repIs] at same
    simp only [rebuild,denote] at here there
    rw [← here,there]
    exact same
  rw [forest.nominal]
  obtain ⟨joinedResult,joinRun,joinSpec⟩ := join_correct F.nodes.val[x.val].deps F.nodes.val[named.val].deps
  simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,namedIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookupX,
    lookupNamed,bind_ok,joinRun]
  cases joinedResult with
  | none => exact ⟨none,by simp,by simp,by simp⟩
  | some deps =>
  have depsIs := joinSpec deps rfl
  have freshDeps : ∀ k ∈ deps.val, k.val < fresh.val := by
    intro k listed
    rcases (depsIs k).mp listed with old | old
    · exact freshF.1 x.val k (by rw [xDeps]; exact old)
    · exact freshF.1 named.val k (by rw [namedDeps]; exact old)
  -- Under the points of the rule, every model places both nodes on one element.
  have meet : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object)
      (D : List Usize), Sub deps.val D → Models P h F I π D → π x.val = π named.val := by
    intro Object Value I π D sub models
    refine meets Object Value I π D ?_ ?_ models
    · intro k listed
      rw [xDeps] at listed
      exact sub k ((depsIs k).mpr (.inl listed))
    · intro k listed
      rw [namedDeps] at listed
      exact sub k ((depsIs k).mpr (.inr listed))
  by_cases differ : ∃ d ∈ F.distinct.val, (d.left = x ∧ d.right = named) ∨ (d.left = named ∧ d.right = x)
  · obtain ⟨pair,pushPair,pairIs⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new Usize) x (by simp; scalar_tac))
    obtain ⟨pair1,pushPair1,pair1Is⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec pair named (by simp [pairIs]; scalar_tac))
    obtain ⟨clashResult,clashRun,clashSpec⟩ := differences_deps_correct F pair1 0#usize deps
    simp only [differ_correct,show (0#usize).val = 0 from rfl,List.drop_zero,decide_eq_true differ,↓reduceIte,
      pushPair,pushPair1,clashRun,bind_ok]
    cases clashResult with
    | none => exact ⟨none,by simp,by simp,by simp⟩
    | some clash =>
    have clashMembers := clashSpec clash rfl
    refine ⟨some (.Rejected clash),by simp,by simp,?_⟩
    intro D same
    simp only [Option.some.injEq,completion.Outcome.Rejected.injEq] at same
    subst same
    refine ⟨?_,?_⟩
    · intro k listed
      rcases (clashMembers k).mp listed with old | ⟨d,dIn,_,_,kIn⟩
      · exact freshDeps k old
      · exact freshF.2.2.1 d (List.mem_of_mem_drop dIn) k kIn
    · rintro ⟨Object,Value,I,π,models,_⟩
      obtain ⟨d,dIn,ends⟩ := differ
      have dDeps : Sub d.deps.val clash.val := by
        intro k kIn
        apply (clashMembers k).mpr
        refine .inr ⟨d,by simpa using dIn,?_,?_,kIn⟩
        · rcases ends with ⟨l,_⟩ | ⟨l,_⟩ <;> simp [pair1Is,pairIs,l]
        · rcases ends with ⟨_,r'⟩ | ⟨_,r'⟩ <;> simp [pair1Is,pairIs,r']
      have separate := models.distinct d dIn dDeps
      have equal := meet Object Value I π clash.val (fun k listed => (clashMembers k).mpr (.inl listed)) models
      rcases ends with ⟨l,r'⟩ | ⟨l,r'⟩
      · rw [l,r'] at separate
        exact separate equal
      · rw [l,r'] at separate
        exact separate equal.symm
  · simp only [differ_correct,show (0#usize).val = 0 from rfl,List.drop_zero,decide_eq_false differ,bind_ok,
      Bool.false_eq_true,↓reduceIte]
    -- A merge of `x` into the named node: every model places them on one element.
    have shape : MergeShape F x.val named.val := by
      refine ⟨apart,active,activeNamed,?_⟩
      by_cases tree : F.nodes.val[x.val].tree = true
      · exact .inl ⟨_,at_x,tree,.inr (.inr (.inl namedBelow))⟩
      · exact .inr ⟨⟨_,at_x,by simpa using tree⟩,namedBelow⟩
    obtain ⟨r,run,sound,complete⟩ := merge_correct.{u,v} P h count M IH F x named deps fresh inv shape small
      freshF freshDeps
    refine ⟨r,run,sound,?_⟩
    intro D rejected
    obtain ⟨bound,rules⟩ := complete D rejected
    refine ⟨bound,?_⟩
    rintro ⟨Object,Value,I,π,models,_⟩
    obtain ⟨sub,separate⟩ := rules Object Value I π models
    exact separate (meet Object Value I π D.val sub models)

/-- The main loop terminates on every forest that keeps the invariant and whose
    points are below `fresh`, and its answer means what `Answers` says. -/
theorem run_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) :
    ∀ (m : Nat) (F : forest.Forest) (fresh : Usize), ForestInv.measure P F = m → Inv P h count F →
      FreshForest F fresh.val →
      ∃ r, forest.run P h F fresh = .ok r ∧ Answers.{u,v} P h count F 0 [] [] fresh.val r := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F fresh same inv freshF
  have IH : ∀ (F' : forest.Forest) (fresh' : Usize), ForestInv.measure P F' < m → Inv P h count F' →
      FreshForest F' fresh'.val →
      ∃ r, forest.run P h F' fresh' = .ok r ∧ Answers.{u,v} P h count F' 0 [] [] fresh'.val r :=
    fun F' fresh' smaller inv' fresh'' => ih _ smaller F' fresh' rfl inv' fresh''
  have wf := inv.shape.wellFormed
  obtain ⟨step,stepRun,addCase,chooseCase,mergeCase,nameCase,cappedCase,nominalCase,loopCase,overlapCase,createCase,
    doneCase⟩ := next_step_correct P h F
  rw [forest.run,stepRun]
  cases step with
  | none => exact ⟨none,by simp,by simp,by simp⟩
  | some s =>
  cases s with
  | Add y c =>
    obtain ⟨yIn,needs,missing⟩ := addCase y c rfl
    have active := addNeeds_active inv.shape y.val c needs
    obtain ⟨ruleResult,ruleRun,ruleSpec⟩ := rule_deps_correct P F y yIn
    cases ruleResult with
    | none => exact ⟨none,by simp [ruleRun],by simp,by simp⟩
    | some deps =>
    obtain ⟨covers,edgeCovers,origin⟩ := ruleSpec deps rfl
    obtain ⟨r,run,sound,complete⟩ := add_correct.{u,v} P h count m IH _ (.Item c .Empty) F y deps fresh rfl inv
      active freshF
      (by
        intro k member
        rcases origin k member with ⟨z,there⟩ | ⟨e,eIn,there⟩
        · exact freshF.1 z k there
        · exact freshF.2.1 e eIn k there)
      (by
        intro F' inv' grows' _ holds'
        rw [← same]
        apply measure_lt_label inv inv' grows' y.val active
        exact grow_strict P.entries.val _ _ (inv.nodup y.val) (grows_label grows' y.val) c.val
          (holds' c (by simp [pendingList])) missing)
    refine ⟨r,by simp [ruleRun,run],sound,?_⟩
    intro D rejected
    obtain ⟨bound,none⟩ := complete D rejected
    refine ⟨bound,?_⟩
    rintro ⟨Object,Value,I,π,models,_⟩
    apply none
    refine ⟨Object,Value,I,π,models,?_⟩
    intro sub c' member
    simp only [pendingList,List.mem_singleton] at member
    subst member
    exact needs_hold wf models y c' needs (fun z near k listed => sub k (covers z near k listed))
      (fun e eIn touches k listed => sub k (edgeCovers e eIn touches k listed))
  | Choose y c c' =>
    obtain ⟨x,activeX,i,member,n,r,c0,c0',at_i,y',stepIs,neighbour,notLeft,notRight⟩ := chooseCase y c c' rfl
    simp only [forest.Step.Choose.injEq] at stepIs
    obtain ⟨rfl,rfl,rfl⟩ := stepIs
    have active := neighbour_active inv.shape x.val activeX r _ neighbour
    have yIn := active_inside active
    obtain ⟨ruleResult,ruleRun,ruleSpec⟩ := rule_deps_correct P F y yIn
    cases ruleResult with
    | none => exact ⟨none,by simp [ruleRun],by simp,by simp⟩
    | some deps =>
    obtain ⟨_,_,origin⟩ := ruleSpec deps rfl
    have freshDeps : ∀ k ∈ deps.val, k.val < fresh.val := by
      intro k member
      rcases origin k member with ⟨z,there⟩ | ⟨e,eIn,there⟩
      · exact freshF.1 z k there
      · exact freshF.2.1 e eIn k there
    -- Either alternative makes the label of `y` grow, which the measure counts.
    have grown : ∀ d : Usize, ¬ Holds P.entries.val (labelOf F.nodes.val y.val) d.val →
        ∀ F' : forest.Forest, Inv P h count F' → Grows F F' →
          (∀ z, z ≠ y.val → labelOf F'.nodes.val z = labelOf F.nodes.val z) →
          (∀ c ∈ pendingList (.Item d .Empty), Holds P.entries.val (labelOf F'.nodes.val y.val) c.val) →
          ForestInv.measure P F' < m := by
      intro d absent F' inv' grows' _ holds'
      rw [← same]
      apply measure_lt_label inv inv' grows' y.val active
      exact grow_strict P.entries.val _ _ (inv.nodup y.val) (grows_label grows' y.val) d.val
        (holds' d (by simp [pendingList])) absent
    obtain ⟨res,run,sound,complete⟩ := branch_correct.{u,v} P h count F y c c' .Empty deps fresh [] freshF freshDeps
      (by
        intro deps' fresh' freshIs freshDeps'
        exact add_correct.{u,v} P h count m IH _ (.Item c .Empty) F y deps' fresh' rfl inv active
          (fresh_succ freshF (by omega)) freshDeps' (grown c notLeft))
      (by
        intro deps' freshDeps'
        exact add_correct.{u,v} P h count m IH _ (.Item c' .Empty) F y deps' fresh rfl inv active freshF
          freshDeps' (grown c' notRight))
      (by
        intro Object Value I z _
        refine ⟨?_,by simp [pendingList]⟩
        obtain ⟨negated,negateRun,negateSpec⟩ := negate_correct.{u,v} (meaning P.entries.val c.val)
        rw [inv.shape.complements i.val n r c c' at_i] at negateRun
        simp only [Result.ok.injEq] at negateRun
        subst negateRun
        have complement := negateSpec (meaning P.entries.val c'.val) rfl Object Value I z
        by_cases left : denote I (meaning P.entries.val c.val) z
        · exact .inl left
        · exact .inr (complement.mpr left))
    refine ⟨res,by simp [ruleRun,run],sound,?_⟩
    intro D rejected
    obtain ⟨bound,none⟩ := complete D rejected
    exact ⟨bound,fun model => none (fullModel_any P h F 0 y.val [] deps.val D.val model)⟩
  | Merge x i =>
    obtain ⟨activeX,i',member,n,r,c,c',at_i,cases⟩ := mergeCase x i rfl
    obtain ⟨stepIs,excess,unrepeated⟩ : forest.Step.Merge x i = .Merge x i' ∧ Excess P h F x.val r c n ∧
        Unrepeated P h F x.val r c := by
      rcases cases with merge | ⟨_,⟨isName,_⟩ | ⟨isCapped,_⟩⟩
      · exact merge
      · cases isName
      · cases isCapped
    simp only [forest.Step.Merge.injEq,true_and] at stepIs
    subst stepIs
    obtain ⟨res,run,answers⟩ := merge_rule_correct.{u,v} P h count m IH F x i fresh inv (by omega) freshF activeX
      member n r c c' at_i excess unrepeated
    exact ⟨res,by simp [run],answers⟩
  | Name x i =>
    obtain ⟨activeX,i',member,n,r,c,c',at_i,cases⟩ := nameCase x i rfl
    obtain ⟨stepIs,repeated,uncapped⟩ : forest.Step.Name x i = .Name x i' ∧ ¬ Unrepeated P h F x.val r c ∧
        ∀ cap ∈ F.caps.val, ¬ (cap.node = x ∧ cap.restriction = i') := by
      rcases cases with ⟨isMerge,_⟩ | ⟨repeated,⟨isName,uncapped⟩ | ⟨isCapped,_⟩⟩
      · cases isMerge
      · exact ⟨isName,repeated,uncapped⟩
      · cases isCapped
    simp only [forest.Step.Name.injEq,true_and] at stepIs
    subst stepIs
    obtain ⟨res,run,answers⟩ := name_rule_correct.{u,v} P h count m IH F x i fresh inv (by omega) freshF activeX
      member n r c c' at_i repeated uncapped
    exact ⟨res,by simp [run],answers⟩
  | Capped x i =>
    obtain ⟨activeX,i',_,n,r,c,c',at_i,cases⟩ := cappedCase x i rfl
    obtain stepIs : forest.Step.Capped x i = .Capped x i' := by
      rcases cases with ⟨isMerge,_⟩ | ⟨_,⟨isName,_⟩ | ⟨isCapped,_⟩⟩
      · cases isMerge
      · cases isName
      · exact isCapped
    simp only [forest.Step.Capped.injEq,true_and] at stepIs
    subst stepIs
    obtain ⟨res,run,answers⟩ := capped_rule_correct.{u,v} P h count m IH F x i fresh inv (by omega) freshF activeX
      n r c c' at_i
    exact ⟨res,by simp [run],answers⟩
  | Nominal x named =>
    obtain ⟨activeX,i,member,a,at_i,namedIs,different⟩ := nominalCase x named rfl
    obtain ⟨res,run,answers⟩ := nominal_correct.{u,v} P h count m IH F x named fresh inv (by omega) freshF activeX i
      member a at_i namedIs different
    exact ⟨res,by simp [run],answers⟩
  | Loop x =>
    -- A node with `¬∃r.Self` that is its own neighbour along `r`: no model.
    obtain ⟨activeX,i,member,s,at_i,loop⟩ := loopCase x rfl
    obtain ⟨ruleResult,ruleRun,ruleSpec⟩ := rule_deps_correct P F x (active_inside activeX)
    cases ruleResult with
    | none => exact ⟨none,by simp [ruleRun],by simp,by simp⟩
    | some deps =>
    obtain ⟨covers,edgeCovers,origin⟩ := ruleSpec deps rfl
    refine ⟨some (.Rejected deps),by simp [ruleRun],by simp,?_⟩
    intro D same
    simp only [Option.some.injEq,completion.Outcome.Rejected.injEq] at same
    subst same
    refine ⟨?_,?_⟩
    · intro k listed
      rcases origin k listed with ⟨z,there⟩ | ⟨e,eIn,there⟩
      · exact freshF.1 z k there
      · exact freshF.2.1 e eIn k there
    · rintro ⟨Object,Value,I,π,models,_⟩
      have related := neighbour_holds models x s x.val loop covers edgeCovers
      have notSelf := models.labels x.val (covers x.val (.inl rfl)) i member
      rw [meaning.eq_def,at_i] at notSelf
      exact notSelf related
  | Overlap x =>
    -- A common neighbour along both roles of a disjoint pair: no model.
    obtain ⟨activeX,d,dIn,y,left,right⟩ := overlapCase x rfl
    obtain ⟨ruleResult,ruleRun,ruleSpec⟩ := rule_deps_correct P F x (active_inside activeX)
    cases ruleResult with
    | none => exact ⟨none,by simp [ruleRun],by simp,by simp⟩
    | some deps =>
    obtain ⟨covers,edgeCovers,origin⟩ := ruleSpec deps rfl
    refine ⟨some (.Rejected deps),by simp [ruleRun],by simp,?_⟩
    intro D same
    simp only [Option.some.injEq,completion.Outcome.Rejected.injEq] at same
    subst same
    refine ⟨?_,?_⟩
    · intro k listed
      rcases origin k listed with ⟨z,there⟩ | ⟨e,eIn,there⟩
      · exact freshF.1 z k there
      · exact freshF.2.1 e eIn k there
    · rintro ⟨Object,Value,I,π,models,_⟩
      exact models.constrained d dIn (π x.val) (π y.val)
        ⟨neighbour_holds models x d.left y.val left covers edgeCovers,
          neighbour_holds models x d.right y.val right covers edgeCovers⟩
  | Create x i =>
    obtain ⟨activeX,free,member,_,_,_,_,_,_,notDone,_⟩ := createCase x i rfl
    obtain ⟨res,run,answers⟩ := create_correct.{u,v} P h count m IH F x i fresh inv (by omega) freshF activeX free
      member notDone
    exact ⟨res,by simp [run],answers⟩
  | Stuck => exact ⟨none,by simp,by simp,by simp⟩
  | Done => exact ⟨some .Accepted,by simp,fun _ => ⟨F,inv,doneCase rfl⟩,by simp⟩

/-! ### Deciding a problem -/

theorem simple_from_correct (h : hierarchy.RoleHierarchy) (role : ObjectPropertyExpression) (index : Usize) :
    forest.simple_from h role index = .ok (decide (∀ t ∈ h.transitive.val.drop index.val, ¬ Below h t role)) := by
  rw [forest.simple_from]
  by_cases more : index.val < h.transitive.val.length
  · have lookup : h.transitive.index_usize index = .ok h.transitive.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : h.transitive.val.drop index.val = h.transitive.val[index.val] :: h.transitive.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := simple_from_correct h role next
    rw [nextIndex] at rest
    rw [split]
    by_cases hit : Below h h.transitive.val[index.val] role
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,below_correct,hit,decide_true,List.forall_mem_cons,not_true_eq_false,false_and,decide_false]
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,below_correct,hit,decide_false,Bool.false_eq_true,advance,rest,List.forall_mem_cons,
        not_false_eq_true,true_and]
  · have empty : h.transitive.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by h.transitive.val.length - index.val
decreasing_by omega

/-- A number restriction or the complement of a self restriction is on a role
    that includes no transitive role. -/
def CountsSimply (h : hierarchy.RoleHierarchy) : concept_table.Entry → Prop
  | .AtLeast _ r _ => ∀ t ∈ transitives h, ¬ Below h t r
  | .AtMost _ r _ _ => ∀ t ∈ transitives h, ¬ Below h t r
  | .NotSelf r => ∀ t ∈ transitives h, ¬ Below h t r
  | _ => True

theorem counting_simple_correct (entries : alloc.vec.Vec concept_table.Entry) (h : hierarchy.RoleHierarchy)
    (index : Usize) :
    forest.counting_simple entries h index = .ok (decide (∀ e ∈ entries.val.drop index.val, CountsSimply h e)) := by
  rw [forest.counting_simple]
  by_cases more : index.val < entries.val.length
  · have lookup : entries.index_usize index = .ok entries.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : entries.val.drop index.val = entries.val[index.val] :: entries.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := counting_simple_correct entries h next
    rw [nextIndex] at rest
    obtain ⟨e,eIs⟩ : ∃ e, entries.val[index.val] = e := ⟨_,rfl⟩
    rw [eIs] at lookup split
    rw [split]
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok]
    cases e with
    | AtLeast m role filler =>
      have unfold : (∀ e ∈ concept_table.Entry.AtLeast m role filler :: entries.val.drop (index.val+1), CountsSimply h e) ↔
          (∀ t ∈ h.transitive.val, ¬ Below h t role) ∧ ∀ e ∈ entries.val.drop (index.val+1), CountsSimply h e := by
        simp only [List.forall_mem_cons,CountsSimply,transitives]
      simp only [simple_from_correct,bind_ok,show (0#usize).val = 0 from rfl,List.drop_zero,unfold,Bool.decide_and]
      by_cases s' : ∀ t ∈ h.transitive.val, ¬ Below h t role
      · simp only [decide_eq_true s',↓reduceIte,advance,bind_ok,rest,Bool.true_and]
      · simp only [decide_eq_false s',Bool.false_eq_true,↓reduceIte,Bool.false_and]
    | AtMost m role filler other =>
      have unfold : (∀ e ∈ concept_table.Entry.AtMost m role filler other :: entries.val.drop (index.val+1), CountsSimply h e) ↔
          (∀ t ∈ h.transitive.val, ¬ Below h t role) ∧ ∀ e ∈ entries.val.drop (index.val+1), CountsSimply h e := by
        simp only [List.forall_mem_cons,CountsSimply,transitives]
      simp only [simple_from_correct,bind_ok,show (0#usize).val = 0 from rfl,List.drop_zero,unfold,Bool.decide_and]
      by_cases s' : ∀ t ∈ h.transitive.val, ¬ Below h t role
      · simp only [decide_eq_true s',↓reduceIte,advance,bind_ok,rest,Bool.true_and]
      · simp only [decide_eq_false s',Bool.false_eq_true,↓reduceIte,Bool.false_and]
    | NotSelf role =>
      have unfold : (∀ e ∈ concept_table.Entry.NotSelf role :: entries.val.drop (index.val+1), CountsSimply h e) ↔
          (∀ t ∈ h.transitive.val, ¬ Below h t role) ∧ ∀ e ∈ entries.val.drop (index.val+1), CountsSimply h e := by
        simp only [List.forall_mem_cons,CountsSimply,transitives]
      simp only [simple_from_correct,bind_ok,show (0#usize).val = 0 from rfl,List.drop_zero,unfold,Bool.decide_and]
      by_cases s' : ∀ t ∈ h.transitive.val, ¬ Below h t role
      · simp only [decide_eq_true s',↓reduceIte,advance,bind_ok,rest,Bool.true_and]
      · simp only [decide_eq_false s',Bool.false_eq_true,↓reduceIte,Bool.false_and]
    | Top | Bottom | Atom _ | NotAtom _ | One _ | NotOne _ | HasSelf _ | And _ _ | Or _ _ | Exists _ _
    | Forall _ _ =>
      simp [CountsSimply,advance,rest]
  · have empty : entries.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by entries.val.length - index.val
decreasing_by omega

theorem simpleCounting_of (h : hierarchy.RoleHierarchy) (entries : List concept_table.Entry)
    (simple : ∀ e ∈ entries, CountsSimply h e)
    (pairs : ∀ d ∈ h.disjoint.val, (∀ t ∈ transitives h, ¬ Below h t d.left) ∧ ∀ t ∈ transitives h, ¬ Below h t d.right) :
    SimpleCounting h entries := by
  refine ⟨?_,?_,?_,pairs⟩
  · intro i n r c at_i
    exact simple _ (List.mem_of_getElem? at_i)
  · intro i n r c d at_i
    exact simple _ (List.mem_of_getElem? at_i)
  · intro i r at_i
    exact simple _ (List.mem_of_getElem? at_i)

theorem disjoint_simple_correct (h : hierarchy.RoleHierarchy) (index : Usize) :
    forest.disjoint_simple h index = .ok (decide (∀ d ∈ h.disjoint.val.drop index.val,
      (∀ t ∈ transitives h, ¬ Below h t d.left) ∧ ∀ t ∈ transitives h, ¬ Below h t d.right)) := by
  rw [forest.disjoint_simple]
  by_cases more : index.val < h.disjoint.val.length
  · have lookup : h.disjoint.index_usize index = .ok h.disjoint.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : h.disjoint.val.drop index.val = h.disjoint.val[index.val] :: h.disjoint.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := disjoint_simple_correct h next
    rw [nextIndex] at rest
    rw [split]
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok,simple_from_correct,show (0#usize).val = 0 from rfl,List.drop_zero,List.forall_mem_cons,transitives]
    by_cases left : ∀ t ∈ h.transitive.val, ¬ Below h t h.disjoint.val[index.val].left
    · by_cases right : ∀ t ∈ h.transitive.val, ¬ Below h t h.disjoint.val[index.val].right
      · simp only [decide_eq_true left,decide_eq_true right,↓reduceIte,advance,bind_ok,rest,transitives]
        congr 1
        exact decide_eq_decide.mpr ⟨fun later => ⟨⟨left,right⟩,later⟩,fun both => both.2⟩
      · simp only [decide_eq_true left,decide_eq_false right,Bool.false_eq_true,↓reduceIte]
        simp [right]
    · simp only [decide_eq_false left,Bool.false_eq_true,↓reduceIte]
      simp [left]
  · have empty : h.disjoint.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by h.disjoint.val.length - index.val
decreasing_by omega

/-- A named node with an empty label. -/
def root : forest.Node :=
  ⟨alloc.vec.Vec.new Usize,0#usize,alloc.vec.Vec.new ObjectPropertyExpression,0#usize,false,true,
    alloc.vec.Vec.new Usize,alloc.vec.Vec.new Usize⟩

theorem roots_correct (count : Usize) (F : forest.Forest) (inside : F.nodes.val.length ≤ count.val)
    (roots : ∀ n ∈ F.nodes.val, n = root) (sameLength : F.same.val.length = F.nodes.val.length)
    (sameIs : ∀ (i : Nat) (b : Usize), F.same.val[i]? = some b → b.val = i) :
    ∃ F', forest.roots count F = .ok (some F') ∧ F'.nodes.val.length = count.val ∧ (∀ n ∈ F'.nodes.val, n = root) ∧
      F'.same.val.length = count.val ∧ (∀ (i : Nat) (b : Usize), F'.same.val[i]? = some b → b.val = i) ∧
      F'.edges = F.edges ∧ F'.distinct = F.distinct ∧ F'.caps = F.caps := by
  rw [forest.roots]
  by_cases more : F.nodes.val.length < count.val
  · have room : F.nodes.val.length < Usize.max := by have := count.hBounds; scalar_tac
    have sameRoom : F.same.val.length < Usize.max := by rw [sameLength]; exact room
    obtain ⟨nodes1,pushNodes,nodesIs⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec F.nodes root room)
    obtain ⟨same1,pushSame,sameIs1⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec F.same (alloc.vec.Vec.len F.nodes) sameRoom)
    obtain ⟨F',run,length',roots',sameLength',sameIs',edges',distinct',caps'⟩ := roots_correct count
      { F with nodes := nodes1, same := same1 } (by simp [nodesIs]; omega)
      (by
        intro n member
        simp only [nodesIs,List.mem_append,List.mem_singleton] at member
        rcases member with old | new
        · exact roots n old
        · exact new)
      (by simp [nodesIs,sameIs1,sameLength])
      (by
        intro i b at_i
        simp only [sameIs1] at at_i
        by_cases old : i < F.same.val.length
        · rw [List.getElem?_append_left old] at at_i
          exact sameIs i b at_i
        · rw [List.getElem?_append_right (by omega)] at at_i
          have : i - F.same.val.length = 0 := by
            have := (List.getElem?_eq_some_iff.mp at_i).1
            simp at this
            omega
          have iIs : i = F.same.val.length := by omega
          rw [this] at at_i
          simp only [List.getElem?_cons_zero,Option.some.injEq] at at_i
          rw [← at_i]
          simp [iIs,sameLength])
    refine ⟨F',?_,length',roots',sameLength',sameIs',edges',distinct',caps'⟩
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,usize_max_val,room]
    have pushNodes' : F.nodes.push ⟨alloc.vec.Vec.new Usize,0#usize,alloc.vec.Vec.new ObjectPropertyExpression,0#usize,
        false,true,alloc.vec.Vec.new Usize,alloc.vec.Vec.new Usize⟩ = .ok nodes1 := pushNodes
    simp [pushNodes',pushSame,run]
  · refine ⟨F,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by omega,roots,by omega,sameIs,rfl,rfl,rfl⟩
termination_by count.val - F.nodes.val.length
decreasing_by
  simp [nodesIs]
  omega

/-- The problem the forest runs on is the input: its TBox concept, links,
    requirements and unfoldings. -/
def Interned (P : completion.Problem) (query facts : List completion.Fact) (links : List completion.Link)
    (axioms : concepts.Concept) (definitions : List completion.Definition) : Prop :=
  meaning P.entries.val P.axioms.val = axioms ∧ P.links.val = links ∧
    Corresponds (query ++ facts) P.entries.val P.requirements.val ∧
    Unfolds definitions P.entries.val P.unfoldings.val

/-- Interning the self restriction of the role of every existential and minimum
    restriction of `entries[index..limit]` keeps the table well formed, only
    appends to it and keeps the complements of maximum restrictions. -/
theorem loop_entries_correct (entries : alloc.vec.Vec concept_table.Entry) (limit index : Usize)
    (wf : WellFormed entries.val) :
    ∃ r, forest.loop_entries entries limit index = .ok r ∧ ∀ t, r = some t →
      WellFormed t.val ∧ (∃ more, t.val = entries.val ++ more) ∧ (Complements entries.val → Complements t.val) := by
  rw [forest.loop_entries]
  by_cases low : index.val < limit.val
  · by_cases more : index.val < entries.val.length
    · have lookup : entries.index_usize index = .ok entries.val[index.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
      obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val + 1 := by simpa using indexValue
      obtain ⟨e,eIs⟩ : ∃ e, entries.val[index.val] = e := ⟨_,rfl⟩
      rw [eIs] at lookup
      simp only [UScalar.lt_equiv,low,↓reduceIte,alloc.vec.Vec.len_val,more,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok]
      cases e with
      | Exists role c =>
        obtain ⟨res,run,spec⟩ := Rowl.ConceptTable.intern_correct (.HasSelf role) entries wf
        cases res with
        | none => exact ⟨none,by simp [Rowl.Concepts.copy_role_identity,run],by simp⟩
        | some pair =>
          obtain ⟨t1,k⟩ := pair
          obtain ⟨wf1,⟨more1,grows1⟩,_,_,keeps1⟩ := spec t1 k rfl
          obtain ⟨r,run2,spec2⟩ := loop_entries_correct t1 limit index' wf1
          refine ⟨r,by simp [Rowl.Concepts.copy_role_identity,run,advance,run2],?_⟩
          intro t same
          obtain ⟨wf2,⟨more2,grows2⟩,keeps2⟩ := spec2 t same
          exact ⟨wf2,⟨more1 ++ more2,by rw [grows2,grows1,List.append_assoc]⟩,fun c => keeps2 (keeps1 c)⟩
      | AtLeast n role c =>
        obtain ⟨res,run,spec⟩ := Rowl.ConceptTable.intern_correct (.HasSelf role) entries wf
        cases res with
        | none => exact ⟨none,by simp [Rowl.Concepts.copy_role_identity,run],by simp⟩
        | some pair =>
          obtain ⟨t1,k⟩ := pair
          obtain ⟨wf1,⟨more1,grows1⟩,_,_,keeps1⟩ := spec t1 k rfl
          obtain ⟨r,run2,spec2⟩ := loop_entries_correct t1 limit index' wf1
          refine ⟨r,by simp [Rowl.Concepts.copy_role_identity,run,advance,run2],?_⟩
          intro t same
          obtain ⟨wf2,⟨more2,grows2⟩,keeps2⟩ := spec2 t same
          exact ⟨wf2,⟨more1 ++ more2,by rw [grows2,grows1,List.append_assoc]⟩,fun c => keeps2 (keeps1 c)⟩
      | _ =>
        obtain ⟨r,run,spec⟩ := loop_entries_correct entries limit index' wf
        exact ⟨r,by simp [advance,run],spec⟩
    · refine ⟨some entries,by simp [UScalar.lt_equiv,low,alloc.vec.Vec.len_val,more],?_⟩
      intro t same
      cases same
      exact ⟨wf,⟨[],by simp⟩,id⟩
  · refine ⟨some entries,by simp [UScalar.lt_equiv,low],?_⟩
    intro t same
    cases same
    exact ⟨wf,⟨[],by simp⟩,id⟩
termination_by limit.val - index.val
decreasing_by all_goals omega

/-- The completion forest terminates. An acceptance comes with a complete forest
    that keeps the invariant for the interned input; a rejection rules out
    every model, in any universes, of the role hierarchy and its disjoint pairs
    in which the TBox
    concept and every definition hold everywhere and every fact and link holds
    at the elements of its named individuals. No answer means that a structure
    would exceed the `usize` range, that a number restriction or the complement
    of a self restriction is on a role that is not simple, or that a nominal, a
    maximum restriction or a loop is outside what the rules handle. -/
theorem satisfiable_answers (count : Usize) (query facts : alloc.vec.Vec completion.Fact)
    (links : alloc.vec.Vec completion.Link) (axioms : concepts.Concept)
    (definitions : alloc.vec.Vec completion.Definition) (h : hierarchy.RoleHierarchy) (closed : Closed h)
    (factsIn : ∀ f ∈ query.val ++ facts.val, f.node.val < count.val)
    (linksIn : ∀ l ∈ links.val, l.from.val < count.val ∧ l.to.val < count.val) :
    ∃ r, forest.satisfiable count query facts links axioms definitions h = .ok r ∧
      (r = some true → ∃ (P : completion.Problem) (F : forest.Forest),
        Interned P query.val facts.val links.val axioms definitions.val ∧ Inv P h count.val F ∧ Complete P h F) ∧
      (r = some false → ¬ ∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
        Respects I h ∧ Constrained I h ∧ (∀ y, denote I axioms y) ∧
        (∀ d ∈ definitions.val, ∀ y, I.classes d.class y → denote I d.concept y) ∧
        (∀ f ∈ query.val ++ facts.val, denote I f.concept (π f.node.val)) ∧
        (∀ l ∈ links.val, objectRelation I l.role (π l.from.val) (π l.to.val))) := by
  have emptyTable : WellFormed (alloc.vec.Vec.new concept_table.Entry).val := by
    intro i e at_i
    simp at at_i
  have emptyComplements : Complements (alloc.vec.Vec.new concept_table.Entry).val := by
    intro i n r c d at_i
    simp at at_i
  obtain ⟨r0,run0,spec0⟩ := Rowl.ConceptTable.intern_correct axioms (alloc.vec.Vec.new concept_table.Entry) emptyTable
  cases r0 with
  | none => exact ⟨none,by rw [forest.satisfiable]; simp [run0],by simp,by simp⟩
  | some pair0 =>
  obtain ⟨t0,ax⟩ := pair0
  obtain ⟨wf0,_,axIn,axMeaning,keeps0⟩ := spec0 t0 ax rfl
  obtain ⟨rq,runq,specq⟩ := intern_facts_correct query 0#usize t0 (alloc.vec.Vec.new completion.Requirement) []
    wf0 (by simp) (by simp [Corresponds])
  cases rq with
  | none => exact ⟨none,by rw [forest.satisfiable]; simp [run0,runq],by simp,by simp⟩
  | some pairq =>
  obtain ⟨tq,requirementsq⟩ := pairq
  obtain ⟨wfq,⟨moreq,growsq⟩,correspondsq,keepsq⟩ := specq tq requirementsq rfl
  obtain ⟨r1,run1,spec1⟩ := intern_facts_correct facts 0#usize tq requirementsq query.val wfq (by simp)
    (by simpa using correspondsq)
  cases r1 with
  | none => exact ⟨none,by rw [forest.satisfiable]; simp [run0,runq,run1],by simp,by simp⟩
  | some pair1 =>
  obtain ⟨t1,requirements⟩ := pair1
  obtain ⟨wf1,⟨more1,grows1⟩,corresponds1,keeps1⟩ := spec1 t1 requirements rfl
  obtain ⟨r2,run2,spec2⟩ := intern_definitions_correct definitions 0#usize t1
    (alloc.vec.Vec.new completion.Unfolding) wf1 (by simp) (by simp [Unfolds])
  cases r2 with
  | none => exact ⟨none,by rw [forest.satisfiable]; simp [run0,runq,run1,run2],by simp,by simp⟩
  | some pair2 =>
  obtain ⟨t2,unfoldings⟩ := pair2
  obtain ⟨wf2,⟨more2,grows2⟩,unfolds2,keeps2⟩ := spec2 t2 unfoldings rfl
  obtain ⟨rl,runl,specl⟩ := loop_entries_correct t2 (alloc.vec.Vec.len t2) 0#usize wf2
  cases rl with
  | none => exact ⟨none,by rw [forest.satisfiable]; simp [run0,runq,run1,run2,runl],by simp,by simp⟩
  | some tl =>
  obtain ⟨wfl,⟨morel,growsl⟩,keepsl⟩ := specl tl rfl
  obtain ⟨r3,run3,spec3⟩ := Rowl.ConceptTable.close_correct h tl wfl
  cases r3 with
  | none => exact ⟨none,by rw [forest.satisfiable]; simp [run0,runq,run1,run2,runl,run3],by simp,by simp⟩
  | some t3 =>
  obtain ⟨wf3,⟨more3,grows3,fromOriginal⟩,closedTable⟩ := spec3 t3 rfl
  have complements2 : Complements t2.val := keeps2 (keeps1 (keepsq (keeps0 emptyComplements)))
  have complementsl : Complements tl.val := keepsl complements2
  have complements3 : Complements t3.val := by
    rw [grows3]
    apply complements_append _ _ wfl complementsl
    intro j n r c d at_j
    obtain ⟨_,_,_,_,_,t,_,_,isForall⟩ := fromOriginal _ (List.mem_of_getElem? at_j)
    cases isForall
  by_cases simple : ∀ e ∈ t3.val, CountsSimply h e
  swap
  · refine ⟨none,?_,by simp,by simp⟩
    rw [forest.satisfiable]
    simp [run0,runq,run1,run2,runl,run3,counting_simple_correct,simple]
  have simple' : ∀ e ∈ t3.val.drop (0#usize).val, CountsSimply h e := by simpa using simple
  by_cases pairsSimple : ∀ d ∈ h.disjoint.val,
      (∀ t ∈ transitives h, ¬ Below h t d.left) ∧ ∀ t ∈ transitives h, ¬ Below h t d.right
  swap
  · refine ⟨none,?_,by simp,by simp⟩
    rw [forest.satisfiable]
    simp only [run0,runq,run1,run2,runl,run3,bind_ok,uncurry_apply_pair,counting_simple_correct]
    rw [decide_eq_true simple']
    simp [disjoint_simple_correct,pairsSimple]
  have simpleCounting : SimpleCounting h t3.val := simpleCounting_of h t3.val simple pairsSimple
  have pairsSimple' : ∀ d ∈ h.disjoint.val.drop (0#usize).val,
      (∀ t ∈ transitives h, ¬ Below h t d.left) ∧ ∀ t ∈ transitives h, ¬ Below h t d.right := by
    simpa using pairsSimple
  obtain ⟨F0,run4,length0,roots0,sameLength0,sameIs0,edges0,distinct0,caps0⟩ := roots_correct count
    ⟨alloc.vec.Vec.new forest.Node,alloc.vec.Vec.new forest.Edge,alloc.vec.Vec.new forest.Distinct,
      alloc.vec.Vec.new Usize,alloc.vec.Vec.new forest.Cap⟩ (by simp) (by simp) (by simp) (by simp)
  let P : completion.Problem := { entries := t3, links, requirements, unfoldings, axioms := ax }
  have axMeaning3 : meaning t3.val ax.val = axioms := by
    have insideq : ax.val < tq.val.length := by rw [growsq]; simp; omega
    have inside1 : ax.val < t1.val.length := by rw [grows1]; simp; omega
    have inside2 : ax.val < t2.val.length := by rw [grows2]; simp; omega
    have insidel : ax.val < tl.val.length := by rw [growsl]; simp; omega
    rw [grows3,Rowl.ConceptTable.meaning_append _ _ wfl _ insidel,growsl,
      Rowl.ConceptTable.meaning_append _ _ wf2 _ inside2,grows2,
      Rowl.ConceptTable.meaning_append _ _ wf1 _ inside1,grows1,Rowl.ConceptTable.meaning_append _ _ wfq _ insideq,
      growsq,Rowl.ConceptTable.meaning_append _ _ wf0 _ axIn,axMeaning]
  have correspondsl : Corresponds (query.val ++ facts.val) tl.val requirements.val := by
    rw [growsl,grows2]
    exact corresponds_append _ _ _ (by rw [← grows2]; exact wf2) _ (corresponds_append _ _ _ wf1 _ corresponds1)
  have corresponds3 : Corresponds (query.val ++ facts.val) t3.val requirements.val := by
    rw [grows3]
    exact corresponds_append _ _ _ wfl _ correspondsl
  have unfolds3 : Unfolds definitions.val t3.val unfoldings.val := by
    rw [grows3]
    exact unfolds_append _ _ _ wfl _ (by rw [growsl]; exact unfolds_append _ _ _ wf2 _ unfolds2)
  have rootNode : ∀ (y : Nat) (n : forest.Node), F0.nodes.val[y]? = some n → n = root :=
    fun y n at_y => roots0 n (List.mem_of_getElem? at_y)
  have rootLabel : ∀ y, labelOf F0.nodes.val y = [] := by
    intro y
    unfold labelOf
    cases at_y : F0.nodes.val[y]? with
    | none => rfl
    | some n =>
      rw [rootNode y n at_y]
      rfl
  have rootDone : ∀ y, doneOf F0.nodes.val y = [] := by
    intro y
    unfold doneOf
    cases at_y : F0.nodes.val[y]? with
    | none => rfl
    | some n =>
      rw [rootNode y n at_y]
      rfl
  have rootDeps : ∀ y, nodeDeps F0 y = [] := by
    intro y
    unfold nodeDeps
    cases at_y : F0.nodes.val[y]? with
    | none => rfl
    | some n =>
      rw [rootNode y n at_y]
      rfl
  have activeRoot : ∀ y, y < count.val → Active F0.nodes.val y := by
    intro y yIn
    have yIn' : y < F0.nodes.val.length := by rw [length0]; exact yIn
    refine ⟨_,List.getElem?_eq_getElem yIn',?_⟩
    rw [rootNode y _ (List.getElem?_eq_getElem yIn')]
    rfl
  have inv0 : Inv P h count.val F0 := by
    refine ⟨⟨wf3,complements3,closedTable closed.1,closed,simpleCounting,?_,by rw [length0],sameLength0,?_,?_,?_,
      linksIn,?_,?_,?_,?_,?_,by intro cap member; rw [caps0] at member; simp at member⟩,?_,?_,?_,?_⟩
    · intro y n at_y _
      rw [rootNode y n at_y]
      rfl
    · intro b member
      obtain ⟨a,at_a⟩ := List.mem_iff_getElem?.mp member
      have value := sameIs0 a b at_a
      have aIn : a < count.val := by rw [← sameLength0]; exact (List.getElem?_eq_some_iff.mp at_a).1
      have aIn' : a < F0.nodes.val.length := by rw [length0]; exact aIn
      rw [value]
      exact ⟨⟨_,List.getElem?_eq_getElem aIn',by rw [rootNode a _ (List.getElem?_eq_getElem aIn')]; rfl⟩,
        activeRoot a aIn⟩
    · intro y n at_y tree
      rw [rootNode y n at_y] at tree
      cases tree
    · intro y n at_y tree
      rw [rootNode y n at_y] at tree
      cases tree
    · intro q member
      obtain ⟨_,f,listed,node,_⟩ := corresponds3.1 q member
      rw [node]
      exact factsIn f listed
    · intro e member
      rw [edges0] at member
      simp at member
    · intro d member
      rw [distinct0] at member
      simp at member
    · intro y i member
      rw [rootLabel y] at member
      cases member
    · intro y i member
      rw [rootLabel y] at member
      cases member
    · intro y
      rw [rootLabel y]
      exact List.nodup_nil
    · intro y
      rw [rootDone y]
      exact List.nodup_nil
    · intro y i member
      rw [rootDone y] at member
      cases member
    · intro y n at_y s member
      rw [rootNode y n at_y] at member
      simp [root] at member
  have fresh0 : FreshForest F0 (0#usize).val := by
    refine ⟨?_,?_,?_,by intro cap member; rw [caps0] at member; simp at member⟩
    · intro y k member
      rw [rootDeps y] at member
      cases member
    · intro e member
      rw [edges0] at member
      simp at member
    · intro d member
      rw [distinct0] at member
      simp at member
  obtain ⟨r,run,sound,complete⟩ := run_correct.{u,v} P h count.val _ F0 0#usize rfl inv0 fresh0
  have run' : forest.run ⟨t3,links,requirements,unfoldings,ax⟩ h F0 0#usize = .ok r := run
  have linksCopy := copy_links_correct links 0#usize (alloc.vec.Vec.new completion.Link) (by simp) (by simp)
  have code : ∀ (rest : Option Bool), (match r with
      | none => ok none
      | some completion.Outcome.Accepted => ok (some true)
      | some (completion.Outcome.Rejected _) => ok (some false) : Result (Option Bool)) = .ok rest →
      forest.satisfiable count query facts links axioms definitions h = .ok rest := by
    intro rest same
    rw [forest.satisfiable]
    simp only [run0,runq,run1,run2,runl,run3,bind_ok,uncurry_apply_pair,counting_simple_correct,linksCopy,run4]
    rw [decide_eq_true simple']
    simp only [↓reduceIte,bind_ok,disjoint_simple_correct]
    rw [decide_eq_true pairsSimple']
    simp only [↓reduceIte,bind_ok,run4,linksCopy,run']
    cases r with
    | none => simpa using same
    | some outcome => cases outcome <;> simpa using same
  cases r with
  | none => exact ⟨none,code none rfl,by simp,by simp⟩
  | some outcome =>
  cases outcome with
  | Accepted =>
    refine ⟨some true,code _ rfl,?_,by simp⟩
    intro _
    obtain ⟨F',inv',complete'⟩ := sound rfl
    exact ⟨P,F',⟨axMeaning3,rfl,corresponds3,unfolds3⟩,inv',complete'⟩
  | Rejected D =>
    refine ⟨some false,code _ rfl,by simp,?_⟩
    intro _
    rintro ⟨Object,Value,I,π,respects,constrained,axiomsHold,definitionsHold,factsHold,linksHold⟩
    apply (complete D rfl).2
    refine ⟨Object,Value,I,π,⟨respects,constrained,?_,?_,?_,linksHold,?_,?_,?_,?_,?_,?_,
      by intro cap member; rw [caps0] at member; simp at member⟩,by simp⟩
    · intro y
      show denote I (meaning t3.val ax.val) y
      rw [axMeaning3]
      exact axiomsHold y
    · intro w member y classes
      obtain ⟨_,d,listed,same,means⟩ := unfolds3.1 w member
      show denote I (meaning t3.val w.concept.val) y
      rw [means]
      exact definitionsHold d listed y (by rw [← same]; exact classes)
    · intro q member
      obtain ⟨_,f,listed,node,means⟩ := corresponds3.1 q member
      show denote I (meaning t3.val q.concept.val) (π q.node.val)
      rw [means,node]
      exact factsHold f listed
    · intro a _
      unfold rep
      cases at_a : F0.same.val[a.val]? with
      | none => rfl
      | some b => rw [sameIs0 a.val b at_a]
    · intro y _ i member
      rw [rootLabel y] at member
      cases member
    · intro y n at_y tree
      rw [rootNode y n at_y] at tree
      cases tree
    · intro e member
      rw [edges0] at member
      simp at member
    · intro d member
      rw [distinct0] at member
      simp at member
    · intro y n at_y _ beyond
      have := (List.getElem?_eq_some_iff.mp at_y).1
      rw [length0] at this
      rw [sameLength0] at beyond
      omega

end Rowl.Forest
