import Rowl.ForestSteps

/-!
The completion forest's run: totality and the meaning of its rejections. Every
rule application adds a literal to the label of an active node, expands a
restriction of an unblocked node, or merges two neighbours, and each of these
decreases the measure, so `run` terminates on every forest that keeps the
invariant. An acceptance comes with a complete forest that keeps the
invariant; a rejection with a set of branch points rules out every model, in
any universes, that holds under those points. Branching on a disjunction or on
a neighbour's choice for a maximum restriction retries the second alternative
only when the first failure depends on the new branch point; merging tries the
pairs of neighbours that are not known to differ in turn, since in every model
of a maximum restriction two of its counted neighbours coincide.
-/
namespace Rowl.Forest
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation)
open Rowl.Concepts (inv inv_inv relation_inv denote negate_correct)
open Rowl.Hierarchy (Below Closed Respects transitives below_refl respects_below below_correct)
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
                  cases e <;> cases e' <;> simp only [Complementary] at complementary
                  · subst complementary; exact there here
                  · subst complementary; exact here there
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
                refine ⟨?_,by rw [grows1.2.1]; exact freshF.2.1,by rw [grows1.2.2.1]; exact freshF.2.2⟩
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
            refine ⟨?_,?_,?_⟩
            · intro y k member; have := freshF.1 y k member; omega
            · intro e member k kIn; have := freshF.2.1 e member k kIn; omega
            · intro d member k kIn; have := freshF.2.2 d member k kIn; omega
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
  refine ⟨?_,?_,?_⟩
  · intro y k member; have := freshF.1 y k member; omega
  · intro e member k kIn; have := freshF.2.1 e member k kIn; omega
  · intro d member k kIn; have := freshF.2.2 d member k kIn; omega

/-- A merge of two neighbours terminates; a rejection rules out every model under
    the rejected points that places them on one element, and those points
    include the ones the merge was given. -/
theorem merge_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (M : Nat)
    (IH : ∀ (F : forest.Forest) (fresh : Usize), ForestInv.measure P F < M → Inv P h count F →
      FreshForest F fresh.val →
      ∃ r, forest.run P h F fresh = .ok r ∧ Answers.{u,v} P h count F 0 [] [] fresh.val r)
    (F : forest.Forest) (x source into : Usize) (deps : alloc.vec.Vec Usize) (fresh : Usize)
    (inv : Inv P h count F) (mergeShape : MergeShape count F x.val source.val into.val)
    (small : ForestInv.measure P F ≤ M) (freshF : FreshForest F fresh.val)
    (freshDeps : ∀ k ∈ deps.val, k.val < fresh.val) :
    ∃ r, forest.merge P h F x source into deps fresh = .ok r ∧
      (r = some .Accepted → ∃ F' : forest.Forest, Inv P h count F' ∧ Complete P h F') ∧
      (∀ D : alloc.vec.Vec Usize, r = some (.Rejected D) → (∀ k ∈ D.val, k.val < fresh.val) ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
          Models P h F I π D.val → Sub deps.val D.val ∧ π source.val ≠ π into.val) := by
  have activeS := mergeShape.2.2.1
  have sourceIn := active_inside activeS
  have at_s : F.nodes.val[source.val]? = some F.nodes.val[source.val] := List.getElem?_eq_getElem sourceIn
  have lookupS : F.nodes.index_usize source = .ok F.nodes.val[source.val] := by
    simp [alloc.vec.Vec.index_usize,at_s]
  have labelCopy := copy_label_correct F.nodes.val[source.val].label 0#usize (alloc.vec.Vec.new Usize) (by simp)
    (by simp)
  obtain ⟨joinedResult,joinRun,joinSpec⟩ := join_correct deps F.nodes.val[source.val].deps
  rw [forest.merge]
  simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookupS,
    bind_ok,labelCopy,joinRun]
  cases joinedResult with
  | none => exact ⟨none,by simp,by simp,by simp⟩
  | some joined =>
  have joinedIs := joinSpec joined rfl
  obtain ⟨mergedResult,mergedRun,mergedSpec⟩ := merged_correct F inv.shape x source into joined mergeShape
  simp only [mergedRun]
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
  have invG := merged_inv inv merged
  have smaller := merged_measure inv merged activeS
  obtain ⟨r,run,sound,complete⟩ := add_correct.{u,v} P h count M IH _
    (pendingOf (F.nodes.val[source.val].label.val.drop (0#usize).val)) G into joined fresh rfl invG
    merged.intoActive (merged_fresh merged freshF joinedFresh) joinedFresh (by
      intro F' inv' grows' _ _
      have := measure_le_grows P grows' invG.nodup
      omega)
  refine ⟨r,by simp only [pending_from_correct,bind_ok,run],sound,?_⟩
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
    simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at member
    exact extra sub c (by simp [labelOf,at_s,member])
  · obtain ⟨sub,different⟩ := Classical.not_imp.mp equal
    exact ⟨fun k member => sub k ((joinedIs k).mpr (.inl member)),different⟩

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
    (shapes : ∀ p ∈ pairs.val, MergeShape count F x.val (orientOf F x p).1.val (orientOf F x p).2.val)
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
    have shapeHere : MergeShape count F x.val src.val dst.val := by
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
        obtain ⟨r1,run1,sound1,complete1⟩ := merge_correct.{u,v} P h count M IH F x src dst here fresh' inv
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
      obtain ⟨r1,run1,sound1,complete1⟩ := merge_correct.{u,v} P h count M IH F x src dst last fresh inv
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
    (at_i : P.entries.val[i.val]? = some (.AtMost n r c c')) (excess : Excess P h F x.val r c n) :
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
      · exact freshF.2.2 d (List.mem_of_mem_drop dIn) k kIn
    have shapes : ∀ p ∈ pairs.val, MergeShape count F x.val (orientOf F x p).1.val (orientOf F x p).2.val := by
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
          (by rw [second]; exact (chosenProps _ (List.getElem_mem hb)).1) different).1
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
        rcases (orient_shape inv.shape x active r p (chosenProps _ (List.getElem_mem ha)).1
          (chosenProps _ (List.getElem_mem hb)).1 different).2 with same | same
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
  obtain ⟨step,stepRun,addCase,chooseCase,mergeCase,createCase,doneCase⟩ := next_step_correct P h F
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
    obtain ⟨activeX,i',member,n,r,c,c',at_i,stepIs,excess⟩ := mergeCase x i rfl
    simp only [forest.Step.Merge.injEq,true_and] at stepIs
    subst stepIs
    obtain ⟨res,run,answers⟩ := merge_rule_correct.{u,v} P h count m IH F x i fresh inv (by omega) freshF activeX
      member n r c c' at_i excess
    exact ⟨res,by simp [run],answers⟩
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

/-- A number restriction counts along a role that includes no transitive role. -/
def CountsSimply (h : hierarchy.RoleHierarchy) : concept_table.Entry → Prop
  | .AtLeast _ r _ => ∀ t ∈ transitives h, ¬ Below h t r
  | .AtMost _ r _ _ => ∀ t ∈ transitives h, ¬ Below h t r
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
    | Top | Bottom | Atom _ | NotAtom _ | And _ _ | Or _ _ | Exists _ _ | Forall _ _ =>
      simp [CountsSimply,advance,rest]
  · have empty : entries.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by entries.val.length - index.val
decreasing_by omega

theorem simpleCounting_of (h : hierarchy.RoleHierarchy) (entries : List concept_table.Entry)
    (simple : ∀ e ∈ entries, CountsSimply h e) : SimpleCounting h entries := by
  refine ⟨?_,?_⟩
  · intro i n r c at_i
    exact simple _ (List.mem_of_getElem? at_i)
  · intro i n r c d at_i
    exact simple _ (List.mem_of_getElem? at_i)

/-- A named node with an empty label. -/
def root : forest.Node :=
  ⟨alloc.vec.Vec.new Usize,0#usize,alloc.vec.Vec.new ObjectPropertyExpression,0#usize,false,true,
    alloc.vec.Vec.new Usize,alloc.vec.Vec.new Usize⟩

theorem roots_correct (count : Usize) (F : forest.Forest) (inside : F.nodes.val.length ≤ count.val)
    (roots : ∀ n ∈ F.nodes.val, n = root) (sameLength : F.same.val.length = F.nodes.val.length)
    (sameIs : ∀ (i : Nat) (b : Usize), F.same.val[i]? = some b → b.val = i) :
    ∃ F', forest.roots count F = .ok (some F') ∧ F'.nodes.val.length = count.val ∧ (∀ n ∈ F'.nodes.val, n = root) ∧
      F'.same.val.length = count.val ∧ (∀ (i : Nat) (b : Usize), F'.same.val[i]? = some b → b.val = i) ∧
      F'.edges = F.edges ∧ F'.distinct = F.distinct := by
  rw [forest.roots]
  by_cases more : F.nodes.val.length < count.val
  · have room : F.nodes.val.length < Usize.max := by have := count.hBounds; scalar_tac
    have sameRoom : F.same.val.length < Usize.max := by rw [sameLength]; exact room
    obtain ⟨nodes1,pushNodes,nodesIs⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec F.nodes root room)
    obtain ⟨same1,pushSame,sameIs1⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec F.same (alloc.vec.Vec.len F.nodes) sameRoom)
    obtain ⟨F',run,length',roots',sameLength',sameIs',edges',distinct'⟩ := roots_correct count
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
    refine ⟨F',?_,length',roots',sameLength',sameIs',edges',distinct'⟩
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,usize_max_val,room]
    have pushNodes' : F.nodes.push ⟨alloc.vec.Vec.new Usize,0#usize,alloc.vec.Vec.new ObjectPropertyExpression,0#usize,
        false,true,alloc.vec.Vec.new Usize,alloc.vec.Vec.new Usize⟩ = .ok nodes1 := pushNodes
    simp [pushNodes',pushSame,run]
  · refine ⟨F,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by omega,roots,by omega,sameIs,rfl,rfl⟩
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

/-- The completion forest terminates. An acceptance comes with a complete forest
    that keeps the invariant for the interned input; a rejection rules out
    every model, in any universes, of the role hierarchy in which the TBox
    concept and every definition hold everywhere and every fact and link holds
    at the elements of its named individuals. No answer means that a structure
    would exceed the `usize` range or that a number restriction counts along a
    role that is not simple. -/
theorem satisfiable_answers (count : Usize) (query facts : alloc.vec.Vec completion.Fact)
    (links : alloc.vec.Vec completion.Link) (axioms : concepts.Concept)
    (definitions : alloc.vec.Vec completion.Definition) (h : hierarchy.RoleHierarchy) (closed : Closed h)
    (factsIn : ∀ f ∈ query.val ++ facts.val, f.node.val < count.val)
    (linksIn : ∀ l ∈ links.val, l.from.val < count.val ∧ l.to.val < count.val) :
    ∃ r, forest.satisfiable count query facts links axioms definitions h = .ok r ∧
      (r = some true → ∃ (P : completion.Problem) (F : forest.Forest),
        Interned P query.val facts.val links.val axioms definitions.val ∧ Inv P h count.val F ∧ Complete P h F) ∧
      (r = some false → ¬ ∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
        Respects I h ∧ (∀ y, denote I axioms y) ∧
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
  obtain ⟨r3,run3,spec3⟩ := Rowl.ConceptTable.close_correct h t2 wf2
  cases r3 with
  | none => exact ⟨none,by rw [forest.satisfiable]; simp [run0,runq,run1,run2,run3],by simp,by simp⟩
  | some t3 =>
  obtain ⟨wf3,⟨more3,grows3,fromOriginal⟩,closedTable⟩ := spec3 t3 rfl
  have complements2 : Complements t2.val := keeps2 (keeps1 (keepsq (keeps0 emptyComplements)))
  have complements3 : Complements t3.val := by
    rw [grows3]
    apply complements_append _ _ wf2 complements2
    intro j n r c d at_j
    obtain ⟨_,_,_,_,_,t,_,_,isForall⟩ := fromOriginal _ (List.mem_of_getElem? at_j)
    cases isForall
  by_cases simple : ∀ e ∈ t3.val, CountsSimply h e
  swap
  · refine ⟨none,?_,by simp,by simp⟩
    rw [forest.satisfiable]
    simp [run0,runq,run1,run2,run3,counting_simple_correct,simple]
  have simpleCounting : SimpleCounting h t3.val := simpleCounting_of h t3.val simple
  have simple' : ∀ e ∈ t3.val.drop (0#usize).val, CountsSimply h e := by simpa using simple
  obtain ⟨F0,run4,length0,roots0,sameLength0,sameIs0,edges0,distinct0⟩ := roots_correct count
    ⟨alloc.vec.Vec.new forest.Node,alloc.vec.Vec.new forest.Edge,alloc.vec.Vec.new forest.Distinct,
      alloc.vec.Vec.new Usize⟩ (by simp) (by simp) (by simp) (by simp)
  let P : completion.Problem := { entries := t3, links, requirements, unfoldings, axioms := ax }
  have axMeaning3 : meaning t3.val ax.val = axioms := by
    have insideq : ax.val < tq.val.length := by rw [growsq]; simp; omega
    have inside1 : ax.val < t1.val.length := by rw [grows1]; simp; omega
    have inside2 : ax.val < t2.val.length := by rw [grows2]; simp; omega
    rw [grows3,Rowl.ConceptTable.meaning_append _ _ wf2 _ inside2,grows2,
      Rowl.ConceptTable.meaning_append _ _ wf1 _ inside1,grows1,Rowl.ConceptTable.meaning_append _ _ wfq _ insideq,
      growsq,Rowl.ConceptTable.meaning_append _ _ wf0 _ axIn,axMeaning]
  have corresponds3 : Corresponds (query.val ++ facts.val) t3.val requirements.val := by
    rw [grows3,grows2]
    exact corresponds_append _ _ _ (by rw [← grows2]; exact wf2) _ (corresponds_append _ _ _ wf1 _ corresponds1)
  have unfolds3 : Unfolds definitions.val t3.val unfoldings.val := by
    rw [grows3]
    exact unfolds_append _ _ _ wf2 _ unfolds2
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
      linksIn,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
    · intro y n at_y
      rw [rootNode y n at_y]
      simp only [root,true_iff]
      rw [← length0]
      exact (List.getElem?_eq_some_iff.mp at_y).1
    · intro b member
      obtain ⟨a,at_a⟩ := List.mem_iff_getElem?.mp member
      have value := sameIs0 a b at_a
      have aIn : a < count.val := by rw [← sameLength0]; exact (List.getElem?_eq_some_iff.mp at_a).1
      rw [value]
      exact ⟨aIn,activeRoot a aIn⟩
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
    refine ⟨?_,?_,?_⟩
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
    simp only [run0,runq,run1,run2,run3,bind_ok,uncurry_apply_pair,counting_simple_correct,linksCopy,run4]
    rw [decide_eq_true simple']
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
    rintro ⟨Object,Value,I,π,respects,axiomsHold,definitionsHold,factsHold,linksHold⟩
    apply (complete D rfl).2
    refine ⟨Object,Value,I,π,⟨respects,?_,?_,?_,linksHold,?_,?_,?_,?_,?_⟩,by simp⟩
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

end Rowl.Forest
