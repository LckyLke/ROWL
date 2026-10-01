import Rowl.RoleClosure

namespace Rowl.RoleOrder
open Aeneas Aeneas.Std RowlRust.model RowlRust.roles RowlRust.role_order Rowl.Roles
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- Independent least closure of the strict-order constraints. This relation
    need not be irreflexive; the eventual validator must reject its conflicts. -/
inductive Derived (seeds : List Edge) : Key → Key → Prop
  | seed {sub sup} : (sub,sup) ∈ seeds → Derived seeds sub sup
  | trans {a b c} : Derived seeds a b → Derived seeds b c → Derived seeds a c
  | source_inverse {sub sup} : Derived seeds sub sup → sup.2 = false → Derived seeds (inverse sub) sup

/-- Full finite pair pairSpace, retaining source occurrence order/duplicates. -/
def Universe (nodes : List Key) : List Edge := nodes.flatMap (fun sub => nodes.map (fun sup => (sub,sup)))

/-- Exact closure or a genuinely derived absent pair. -/
def Correct (nodes : List Key) (seeds : List Edge) : OrderClosure → Prop
  | .Complete edges => (edgeKeys edges).Nodup ∧
      (∀ edge ∈ edgeKeys edges, edge ∈ Universe nodes) ∧
      ∀ sub sup, (sub,sup) ∈ edgeKeys edges ↔ Derived seeds sub sup
  | .MissingPair sub sup => Derived seeds (key sub) (key sup) ∧ (key sub,key sup) ∉ Universe nodes

private theorem append_total (left right : Edges) :
    ∃ output, append left right = .ok output ∧ edgeKeys output = edgeKeys left ++ edgeKeys right := by
  induction left with
  | Empty => exact ⟨right,by simp [append],by simp [edgeKeys]⟩
  | Entry sub sup next ih =>
    obtain ⟨output,executed,correct⟩ := ih
    exact ⟨.Entry sub sup output,by simp [append,executed],by simp [edgeKeys,correct]⟩

private theorem split_total (values : Roles) : split_roles values = .ok (values,values) := by
  induction values with
  | Empty => simp [split_roles]
  | Entry role next ih => cases role; simp [split_roles,ih]

private theorem pairs_with_total (source : Role) (targets : Roles) :
    ∃ output, pairs_with source targets = .ok (output,targets) ∧
      edgeKeys output = (roleKeys targets).map (fun target => (key source,target)) := by
  induction targets with
  | Empty => exact ⟨.Empty,by simp [pairs_with],by simp [edgeKeys,roleKeys]⟩
  | Entry role next ih =>
    obtain ⟨output,executed,correct⟩ := ih
    exact ⟨.Entry source role output,by cases source; cases role; simp [pairs_with,executed],
      by simp [edgeKeys,roleKeys,correct]⟩

private theorem all_pairs_total (sources targets : Roles) :
    ∃ output, all_pairs sources targets = .ok output ∧
      edgeKeys output = (roleKeys sources).flatMap (fun source => (roleKeys targets).map (fun target => (source,target))) := by
  induction sources with
  | Empty => exact ⟨.Empty,by simp [all_pairs],by simp [roleKeys,edgeKeys]⟩
  | Entry role next ih =>
    obtain ⟨head,headExecuted,headCorrect⟩ := pairs_with_total role targets
    obtain ⟨tail,tailExecuted,tailCorrect⟩ := ih
    obtain ⟨output,executed,correct⟩ := append_total head tail
    exact ⟨output,by simp [all_pairs,headExecuted,tailExecuted,executed],
      by simp [roleKeys,correct,headCorrect,tailCorrect]⟩

private theorem contains_total (values : Edges) (sub sup : Role) :
    contains values sub sup = .ok (decide ((key sub,key sup) ∈ edgeKeys values),values) := by
  induction values with
  | Empty => simp [contains,edgeKeys]
  | Entry a b next ih =>
    rw [contains,Rowl.RoleClosure.same_role_total_correct]
    by_cases sameSub : key a = key sub
    · by_cases sameSup : key b = key sup
      · simp [Rowl.RoleClosure.same_role_total_correct,sameSub,sameSup,edgeKeys]
      · simp [Rowl.RoleClosure.same_role_total_correct,sameSub,sameSup,ih,edgeKeys,Ne.symm sameSup]
    · simp [sameSub,ih,edgeKeys,Ne.symm sameSub]

private def TakenCorrect (values : Edges) (sub sup : Role) : TakenPair → Prop
  | .Missing => (key sub,key sup) ∉ edgeKeys values
  | .Found remaining => (edgeKeys values).Perm ((key sub,key sup) :: edgeKeys remaining)

private theorem take_total (values : Edges) (sub sup : Role) :
    ∃ result, take values sub sup = .ok result ∧ TakenCorrect values sub sup result := by
  induction values with
  | Empty => exact ⟨.Missing,by simp [take],by simp [TakenCorrect,edgeKeys]⟩
  | Entry a b next ih =>
    by_cases same : (key a,key b) = (key sub,key sup)
    · have subEq : key a = key sub := congrArg Prod.fst same
      have supEq : key b = key sup := congrArg Prod.snd same
      exact ⟨.Found next,by simp [take,Rowl.RoleClosure.same_role_total_correct,subEq,supEq],
        by simp [TakenCorrect,edgeKeys,same]⟩
    · have pairFalse : ¬ (key a = key sub ∧ key b = key sup) := by simpa only [Prod.mk.injEq] using same
      obtain ⟨result,executed,correct⟩ := ih
      cases result with
      | Missing =>
        exact ⟨.Missing,by by_cases subEq : key a = key sub <;> by_cases supEq : key b = key sup <;> simp_all [take,Rowl.RoleClosure.same_role_total_correct],
          by simpa [TakenCorrect,edgeKeys,Ne.symm same] using correct⟩
      | Found remaining =>
        refine ⟨.Found (.Entry a b remaining),by by_cases subEq : key a = key sub <;> by_cases supEq : key b = key sup <;> simp_all [take,Rowl.RoleClosure.same_role_total_correct],?_⟩
        exact (List.Perm.cons (key a,key b) correct).trans (List.Perm.swap ..)

private theorem predecessors_total (sub sup : Role) (values : Edges) :
    ∃ output, predecessors sub sup values = .ok (output,values) ∧
      ∀ a b, (a,b) ∈ edgeKeys output ↔ b = key sup ∧ (a,key sub) ∈ edgeKeys values := by
  induction values with
  | Empty => exact ⟨.Empty,by simp [predecessors],by simp [edgeKeys]⟩
  | Entry a b next ih =>
    obtain ⟨output,executed,correct⟩ := ih
    by_cases same : key b = key sub
    · refine ⟨.Entry a sup output,by cases sup; cases a; simp [predecessors,executed,Rowl.RoleClosure.same_role_total_correct,same],?_⟩
      intro left right
      simp [edgeKeys,same,correct left right]
      tauto
    · refine ⟨output,by simp [predecessors,executed,Rowl.RoleClosure.same_role_total_correct,same],?_⟩
      intro left right
      simp [edgeKeys,correct left right,Ne.symm same]

private theorem successors_total (sub sup : Role) (values : Edges) :
    ∃ output, successors sub sup values = .ok (output,values) ∧
      ∀ a b, (a,b) ∈ edgeKeys output ↔ a = key sub ∧ (key sup,b) ∈ edgeKeys values := by
  induction values with
  | Empty => exact ⟨.Empty,by simp [RowlRust.role_order.successors],by simp [edgeKeys]⟩
  | Entry a b next ih =>
    obtain ⟨output,executed,correct⟩ := ih
    by_cases same : key a = key sup
    · refine ⟨.Entry sub b output,by cases sub; cases b; simp [RowlRust.role_order.successors,executed,Rowl.RoleClosure.same_role_total_correct,same],?_⟩
      intro left right
      simp [edgeKeys,same,correct left right]
      tauto
    · refine ⟨output,by simp [RowlRust.role_order.successors,executed,Rowl.RoleClosure.same_role_total_correct,same],?_⟩
      intro left right
      simp [edgeKeys,correct left right,Ne.symm same]

private theorem inverse_source_total (sub sup : Role) :
    ∃ output, inverse_source sub sup = .ok output ∧
      edgeKeys output = if (key sup).2 = false then [(inverse (key sub),key sup)] else [] := by
  cases sub with
  | mk iri orientation => cases sup with | mk other direction =>
    cases orientation <;> cases direction <;> exact ⟨_,rfl,rfl⟩

private structure Invariant (pairSpace seeds : List Edge) (pending available resolved : Edges) : Prop where
  partition : (edgeKeys available ++ edgeKeys resolved).Perm pairSpace
  distinct : (edgeKeys resolved).Nodup
  pendingDerived : ∀ sub sup, (sub,sup) ∈ edgeKeys pending → Derived seeds sub sup
  resolvedDerived : ∀ sub sup, (sub,sup) ∈ edgeKeys resolved → Derived seeds sub sup
  seedFrontier : ∀ edge ∈ seeds, edge ∈ edgeKeys resolved ∨ edge ∈ edgeKeys pending
  transFrontier : ∀ a b c, (a,b) ∈ edgeKeys resolved → (b,c) ∈ edgeKeys resolved →
    (a,c) ∈ edgeKeys resolved ∨ (a,c) ∈ edgeKeys pending
  inverseFrontier : ∀ sub sup, (sub,sup) ∈ edgeKeys resolved → sup.2 = false →
    (inverse sub,sup) ∈ edgeKeys resolved ∨ (inverse sub,sup) ∈ edgeKeys pending

private theorem finish (nodes : List Key) (seeds : List Edge) (available resolved : Edges)
    (inv : Invariant (Universe nodes) seeds .Empty available resolved) :
    Correct nodes seeds (.Complete resolved) := by
  refine ⟨inv.distinct,?_,fun sub sup => ⟨inv.resolvedDerived sub sup,?_⟩⟩
  · intro edge member
    exact inv.partition.mem_iff.mp (List.mem_append_right _ member)
  · intro derived
    induction derived with
    | seed member => simpa [edgeKeys] using inv.seedFrontier _ member
    | trans first second ih₁ ih₂ => simpa [edgeKeys] using inv.transFrontier _ _ _ ih₁ ih₂
    | source_inverse path direct ih => simpa [edgeKeys] using inv.inverseFrontier _ _ ih direct

private theorem advance_seen (pairSpace seeds : List Edge) (sub sup : Role) (tail available resolved : Edges)
    (inv : Invariant pairSpace seeds (.Entry sub sup tail) available resolved)
    (seen : (key sub,key sup) ∈ edgeKeys resolved) : Invariant pairSpace seeds tail available resolved := by
  have move (edge : Edge) (h : edge ∈ edgeKeys resolved ∨ edge ∈ edgeKeys (.Entry sub sup tail)) :
      edge ∈ edgeKeys resolved ∨ edge ∈ edgeKeys tail := by
    rcases h with h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl (h ▸ seen)
      · exact Or.inr h
  refine ⟨inv.partition,inv.distinct,?_,inv.resolvedDerived,?_,?_,?_⟩
  · intro a b member; exact inv.pendingDerived a b (by simp [edgeKeys,member])
  · intro edge member; exact move edge (inv.seedFrontier edge member)
  · intro a b c first second; exact move (a,c) (inv.transFrontier a b c first second)
  · intro a b member direct; exact move (inverse a,b) (inv.inverseFrontier a b member direct)

private theorem advance_new (pairSpace seeds : List Edge) (sub sup : Role)
    (tail available resolved remaining pending invEdges before after : Edges)
    (inv : Invariant pairSpace seeds (.Entry sub sup tail) available resolved)
    (unseen : (key sub,key sup) ∉ edgeKeys resolved)
    (taken : (edgeKeys available).Perm ((key sub,key sup) :: edgeKeys remaining))
    (inverseKeys : edgeKeys invEdges = if (key sup).2 = false then [(inverse (key sub),key sup)] else [])
    (beforeKeys : ∀ a b, (a,b) ∈ edgeKeys before ↔ b = key sup ∧ (a,key sub) ∈ edgeKeys resolved)
    (afterKeys : ∀ a b, (a,b) ∈ edgeKeys after ↔ a = key sub ∧ (key sup,b) ∈ edgeKeys resolved)
    (pendingKeys : edgeKeys pending = edgeKeys invEdges ++ edgeKeys before ++ edgeKeys after ++ edgeKeys tail) :
    Invariant pairSpace seeds pending remaining (.Entry sub sup resolved) := by
  have current : Derived seeds (key sub) (key sup) := inv.pendingDerived _ _ (by simp [edgeKeys])
  have move (edge : Edge) (h : edge ∈ edgeKeys resolved ∨ edge ∈ edgeKeys (.Entry sub sup tail)) :
      edge ∈ edgeKeys (.Entry sub sup resolved) ∨ edge ∈ edgeKeys pending := by
    rcases h with h | h
    · exact Or.inl (by simp [edgeKeys,h])
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl (by simp [edgeKeys,h])
      · exact Or.inr (by rw [pendingKeys]; simp [h])
  have inBefore {a b : Key} (h : (a,b) ∈ edgeKeys before) : (a,b) ∈ edgeKeys pending := by rw [pendingKeys]; simp [h]
  have inAfter {a b : Key} (h : (a,b) ∈ edgeKeys after) : (a,b) ∈ edgeKeys pending := by rw [pendingKeys]; simp [h]
  have inInverse {a b : Key} (h : (a,b) ∈ edgeKeys invEdges) : (a,b) ∈ edgeKeys pending := by rw [pendingKeys]; simp [h]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have moved := taken.append_right (edgeKeys resolved)
    have reorder : (((key sub,key sup) :: edgeKeys remaining) ++ edgeKeys resolved).Perm
        (edgeKeys remaining ++ (key sub,key sup) :: edgeKeys resolved) := List.perm_middle.symm
    exact (moved.trans reorder).symm.trans inv.partition
  · simpa [edgeKeys,List.nodup_cons] using And.intro unseen inv.distinct
  · intro a b member
    rw [pendingKeys] at member
    simp only [List.mem_append] at member
    rcases member with ((h | h) | h) | h
    · rw [inverseKeys] at h
      by_cases direct : (key sup).2 = false
      · have equal : (a,b) = (inverse (key sub),key sup) := by simpa [direct] using h
        cases equal
        exact current.source_inverse direct
      · simp [direct] at h
    · obtain ⟨rfl,previous⟩ := (beforeKeys a b).mp h
      exact (inv.resolvedDerived _ _ previous).trans current
    · obtain ⟨rfl,next⟩ := (afterKeys a b).mp h
      exact current.trans (inv.resolvedDerived _ _ next)
    · exact inv.pendingDerived a b (by simp [edgeKeys,h])
  · intro a b member
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact current
    · exact inv.resolvedDerived a b member
  · intro edge member; exact move edge (inv.seedFrontier edge member)
  · intro a b c first second
    rcases List.mem_cons.mp first with first | first
    · obtain ⟨left,middle⟩ := Prod.mk.inj first
      rcases List.mem_cons.mp second with second | second
      · obtain ⟨middle₂,right⟩ := Prod.mk.inj second
        exact Or.inl (by simp [edgeKeys,left,right])
      · exact Or.inr (inAfter ((afterKeys a c).mpr ⟨left,by simpa [middle] using second⟩))
    · rcases List.mem_cons.mp second with second | second
      · obtain ⟨middle,right⟩ := Prod.mk.inj second
        exact Or.inr (inBefore ((beforeKeys a c).mpr ⟨right,by simpa [middle] using first⟩))
      · exact move (a,c) (inv.transFrontier a b c first second)
  · intro a b member direct
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact Or.inr (inInverse (by rw [inverseKeys]; simp [direct]))
    · exact move (inverse a,b) (inv.inverseFrontier a b member direct)

private theorem discover_total (nodes : List Key) (seeds : List Edge) (pending available resolved : Edges)
    (inv : Invariant (Universe nodes) seeds pending available resolved) :
    ∃ output, discover pending available resolved = .ok output ∧ Correct nodes seeds output := by
  cases pending with
  | Empty => exact ⟨.Complete resolved,by simp [discover],finish nodes seeds available resolved inv⟩
  | Entry sub sup tail =>
    have contains := contains_total resolved sub sup
    by_cases seen : (key sub,key sup) ∈ edgeKeys resolved
    · obtain ⟨output,executed,correct⟩ := discover_total nodes seeds tail available resolved
        (advance_seen _ _ sub sup tail available resolved inv seen)
      exact ⟨output,by simp [discover,contains,seen,executed],correct⟩
    · obtain ⟨taken,takeExecuted,takeCorrect⟩ := take_total available sub sup
      cases taken with
      | Missing =>
        refine ⟨.MissingPair sub sup,by simp [discover,contains,seen,takeExecuted],?_,?_⟩
        · exact inv.pendingDerived _ _ (by simp [edgeKeys])
        · intro member
          have partition := inv.partition.mem_iff.mpr member
          rcases List.mem_append.mp partition with h | h
          · exact takeCorrect h
          · exact seen h
      | Found remaining =>
        obtain ⟨before,beforeExecuted,beforeCorrect⟩ := predecessors_total sub sup resolved
        obtain ⟨after,afterExecuted,afterCorrect⟩ := successors_total sub sup resolved
        obtain ⟨inverseEdges,inverseExecuted,inverseCorrect⟩ := inverse_source_total sub sup
        obtain ⟨next₁,next₁Executed,next₁Correct⟩ := append_total after tail
        obtain ⟨next₂,next₂Executed,next₂Correct⟩ := append_total before next₁
        obtain ⟨next,nextExecuted,nextCorrect⟩ := append_total inverseEdges next₂
        have pendingKeys : edgeKeys next = edgeKeys inverseEdges ++ edgeKeys before ++ edgeKeys after ++ edgeKeys tail := by
          simp [nextCorrect,next₂Correct,next₁Correct,List.append_assoc]
        have nextInv := advance_new _ _ sub sup tail available resolved remaining next inverseEdges before after inv seen takeCorrect inverseCorrect beforeCorrect afterCorrect pendingKeys
        obtain ⟨output,executed,correct⟩ := discover_total nodes seeds next remaining (.Entry sub sup resolved) nextInv
        exact ⟨output,by simp [discover,contains,seen,takeExecuted,beforeExecuted,afterExecuted,inverseExecuted,next₁Executed,next₂Executed,nextExecuted,executed],correct⟩
termination_by ((edgeKeys available).length,(edgeKeys pending).length)
decreasing_by
  · simp_all [edgeKeys]
  · have lengthEq := takeCorrect.length_eq
    change (edgeKeys available).length = ((key sub,key sup) :: edgeKeys remaining).length at lengthEq
    simp only [List.length_cons] at lengthEq
    simp_wf
    omega

/-- The actual finite pair worklist is total and computes exactly the least
    transitive/inverse-source closure, including cycles and duplicate inputs. -/
theorem close_order_total_correct (nodes : Roles) (seeds : Edges) :
    ∃ output, close_order nodes seeds = .ok output ∧ Correct (roleKeys nodes) (edgeKeys seeds) output := by
  obtain ⟨pairSpace,built,universeKeys⟩ := all_pairs_total nodes nodes
  have inv : Invariant (Universe (roleKeys nodes)) (edgeKeys seeds) seeds pairSpace .Empty := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · simp [edgeKeys,universeKeys,Universe]
    · simp [edgeKeys]
    · intro sub sup member; exact Derived.seed member
    · simp [edgeKeys]
    · intro edge member; exact Or.inr member
    · simp [edgeKeys]
    · simp [edgeKeys]
  obtain ⟨output,executed,correct⟩ := discover_total _ _ seeds pairSpace .Empty inv
  exact ⟨output,by simp [close_order,split_total,built,executed],correct⟩

theorem close_order_complete_iff (nodes : Roles) (seeds : Edges) :
    (∃ output, close_order nodes seeds = .ok (.Complete output)) ↔
      ∀ sub sup, Derived (edgeKeys seeds) sub sup → (sub,sup) ∈ Universe (roleKeys nodes) := by
  constructor
  · rintro ⟨output,executed⟩
    obtain ⟨actual,run,correct⟩ := close_order_total_correct nodes seeds
    have equal := Result.ok_injective (run.symm.trans executed)
    rw [equal] at correct
    exact fun sub sup derived => correct.2.1 (sub,sup) ((correct.2.2 sub sup).mpr derived)
  · intro present
    obtain ⟨actual,run,correct⟩ := close_order_total_correct nodes seeds
    cases actual with
    | Complete output => exact ⟨output,run⟩
    | MissingPair sub sup => exact False.elim (correct.2 (present _ _ correct.1))

/-- Drop the last operand only when it equals the chain superproperty. -/
noncomputable def TrimLast (sup : Key) : List Key → List Key
  | [] => []
  | [last] => if last = sup then [] else [last]
  | head :: second :: tail => head :: TrimLast sup (second :: tail)

noncomputable def Selected (sup : Key) : List Key → List Key
  | [] => []
  | head :: tail => if head = sup then (if tail = [sup] then [] else tail) else TrimLast sup (head :: tail)

def Top (role : Key) : Prop := role.2 = false ∧ role.1.spelling.val = TopBytes
noncomputable def ChainSeeds (chain : Chain) : List Edge :=
  let sup := expressionKey chain.2
  if Top sup then [] else (Selected sup (PropertyKeys chain.1)).map (fun role => (role,sup))
noncomputable def Seeds (items : List AnnotatedAxiom) : List Edge :=
  (items.flatMap (fun item => AxiomChains item.axiom)).flatMap ChainSeeds

private theorem to_super_total (values : Roles) (sup : Role) :
    ∃ output, to_super values sup = .ok output ∧ edgeKeys output = (roleKeys values).map (fun sub => (sub,key sup)) := by
  induction values with
  | Empty => exact ⟨.Empty,by simp [to_super],by simp [roleKeys,edgeKeys]⟩
  | Entry role next ih =>
    obtain ⟨output,executed,correct⟩ := ih
    exact ⟨.Entry role sup output,by cases sup; simp [to_super,executed],by simp [roleKeys,edgeKeys,correct]⟩

private theorem trim_last_total (values : Roles) (sup : Role) :
    ∃ output, trim_last values sup = .ok output ∧
      edgeKeys output = (TrimLast (key sup) (roleKeys values)).map (fun sub => (sub,key sup)) := by
  induction values with
  | Empty => exact ⟨.Empty,by simp [trim_last],by simp [roleKeys,edgeKeys,TrimLast]⟩
  | Entry role next ih =>
    cases next with
    | Empty =>
      by_cases same : key role = key sup
      · exact ⟨.Empty,by simp [trim_last,Rowl.RoleClosure.same_role_total_correct,same],by simp [TrimLast,roleKeys,edgeKeys,same]⟩
      · exact ⟨.Entry role sup .Empty,by cases sup; simp [trim_last,Rowl.RoleClosure.same_role_total_correct,same],by simp [TrimLast,roleKeys,edgeKeys,same]⟩
    | Entry second tail =>
      obtain ⟨output,executed,correct⟩ := ih
      exact ⟨.Entry role sup output,by cases sup; simp [trim_last,executed],by simp [roleKeys,edgeKeys,TrimLast,correct]⟩

private theorem empty_total (values : Roles) : roles_empty values = .ok (decide (roleKeys values = [])) := by
  cases values <;> simp [roles_empty,roleKeys]

private theorem non_top_seeds_total (values : Roles) (sup : Role) :
    ∃ output, non_top_seeds values sup = .ok output ∧
      edgeKeys output = (Selected (key sup) (roleKeys values)).map (fun sub => (sub,key sup)) := by
  cases values with
  | Empty => exact ⟨.Empty,by simp [non_top_seeds],by simp [Selected,roleKeys,edgeKeys]⟩
  | Entry role next =>
    by_cases first : key role = key sup
    · cases next with
      | Empty => exact ⟨.Empty,by simp [non_top_seeds,Rowl.RoleClosure.same_role_total_correct,first],by simp [Selected,roleKeys,edgeKeys,first]⟩
      | Entry second rest =>
        by_cases transitive : roleKeys rest = [] ∧ key second = key sup
        · obtain ⟨empty,secondEq⟩ := transitive
          exact ⟨.Empty,by simp [non_top_seeds,Rowl.RoleClosure.same_role_total_correct,empty_total,first,empty,secondEq],by simp [Selected,roleKeys,edgeKeys,first,empty,secondEq]⟩
        · obtain ⟨output,executed,correct⟩ := to_super_total (.Entry second rest) sup
          refine ⟨output,?_,?_⟩
          · by_cases empty : roleKeys rest = [] <;> by_cases secondEq : key second = key sup <;>
              simp_all [non_top_seeds,Rowl.RoleClosure.same_role_total_correct,empty_total]
          · have notPair : ¬ (key second = key sup ∧ roleKeys rest = []) := by simpa only [and_comm] using transitive
            simpa [Selected,roleKeys,first,List.cons.injEq,notPair] using correct
    · obtain ⟨output,executed,correct⟩ := trim_last_total (.Entry role next) sup
      exact ⟨output,by simp [non_top_seeds,Rowl.RoleClosure.same_role_total_correct,first,executed],by simpa [Selected,roleKeys,first] using correct⟩

private theorem chain_seeds_total (chain : AtLeastTwo ObjectPropertyExpression) (sup : ObjectPropertyExpression) :
    ∃ output, chain_seeds chain sup = .ok output ∧ edgeKeys output = ChainSeeds (chain,sup) := by
  obtain ⟨role,converted,roleCorrect⟩ := expression_role_total_correct sup
  obtain ⟨values,readValues,valuesCorrect⟩ := property_roles_total_correct chain
  have top : is_top_role role = .ok (decide (Top (expressionKey sup))) := by
    rw [is_top_role_total_correct]
    apply congrArg Result.ok
    apply decide_eq_decide.mpr
    simp only [Top,roleCorrect]
  by_cases isTop : Top (expressionKey sup)
  · exact ⟨.Empty,by simp [chain_seeds,converted,top,isTop],by simp [ChainSeeds,isTop,edgeKeys]⟩
  · obtain ⟨output,executed,correct⟩ := non_top_seeds_total values role
    refine ⟨output,by simp [chain_seeds,converted,top,isTop,readValues,executed],?_⟩
    simpa [ChainSeeds,isTop,valuesCorrect,roleCorrect] using correct

private theorem all_chain_seeds_total (chains : Chains) :
    ∃ output, all_chain_seeds chains = .ok output ∧ edgeKeys output = (chainKeys chains).flatMap ChainSeeds := by
  induction chains with
  | Empty => exact ⟨.Empty,by simp [all_chain_seeds],by simp [chainKeys,edgeKeys]⟩
  | Entry chain sup next ih =>
    obtain ⟨head,headExecuted,headCorrect⟩ := chain_seeds_total chain sup
    obtain ⟨tail,tailExecuted,tailCorrect⟩ := ih
    obtain ⟨output,executed,correct⟩ := append_total head tail
    exact ⟨output,by simp [all_chain_seeds,headExecuted,tailExecuted,executed],by simp [chainKeys,correct,headCorrect,tailCorrect]⟩

private def AllBelow (order : Key → Key → Prop) (sup : Key) (terms : List Key) : Prop :=
  ∀ role ∈ terms, order role sup

private theorem allBelow_cons (order : Key → Key → Prop) (sup head : Key) (tail : List Key) :
    AllBelow order sup (head :: tail) ↔ order head sup ∧ AllBelow order sup tail := by
  simp only [AllBelow,List.forall_mem_cons]

private theorem trim_last_iff (order : Key → Key → Prop) (sup : Key) (terms : List Key) :
    AllBelow order sup (TrimLast sup terms) ↔
      AllBelow order sup terms ∨ (∃ before, terms = before ++ [sup] ∧ AllBelow order sup before) := by
  induction terms with
  | nil => simp [TrimLast,AllBelow]
  | cons head tail ih =>
    cases tail with
    | nil =>
      by_cases same : head = sup
      · subst head
        constructor
        · intro _; exact Or.inr ⟨[],rfl,by simp [AllBelow]⟩
        · intro _; simp [TrimLast,AllBelow]
      · rw [TrimLast,if_neg same]
        constructor
        · intro below; exact Or.inl below
        · rintro (below | ⟨before,equal,prior⟩)
          · exact below
          · have len : before.length = 0 := by
              have lengthEq := congrArg List.length equal
              simp only [List.length_singleton,List.length_append] at lengthEq
              omega
            have empty : before = [] := List.length_eq_zero_iff.mp len
            subst before
            have contradiction : head = sup := List.singleton_inj.mp equal
            exact False.elim (same contradiction)
    | cons second rest =>
      rw [TrimLast,allBelow_cons,ih]
      constructor
      · rintro ⟨headBelow,all | ⟨before,equal,beforeBelow⟩⟩
        · exact Or.inl ((allBelow_cons ..).mpr ⟨headBelow,all⟩)
        · exact Or.inr ⟨head :: before,by simp [equal],(allBelow_cons ..).mpr ⟨headBelow,beforeBelow⟩⟩
      · rintro (all | ⟨before,equal,beforeBelow⟩)
        · exact ⟨(allBelow_cons ..).mp all |>.1,Or.inl ((allBelow_cons ..).mp all |>.2)⟩
        · cases before with
          | nil => simp at equal
          | cons prior rest =>
            obtain ⟨rfl,tailEqual⟩ := List.cons.inj equal
            exact ⟨(allBelow_cons ..).mp beforeBelow |>.1,
              Or.inr ⟨rest,tailEqual,(allBelow_cons ..).mp beforeBelow |>.2⟩⟩

private def Conditions (order : Key → Key → Prop) (sup : Key) (terms : List Key) : Prop :=
  Top sup ∨ terms = [sup,sup] ∨ AllBelow order sup terms ∨
    (∃ tail, terms = sup :: tail ∧ AllBelow order sup tail) ∨
    (∃ before, terms = before ++ [sup] ∧ AllBelow order sup before)

private theorem chain_conditions (order : Key → Key → Prop) (chain : Chain) :
    ChainOrdered order chain ↔ Conditions order (expressionKey chain.2) (PropertyKeys chain.1) := by
  have transitive : (chain.1.rest.val = [] ∧ expressionKey chain.1.first = expressionKey chain.2 ∧ expressionKey chain.1.second = expressionKey chain.2) ↔
      PropertyKeys chain.1 = [expressionKey chain.2,expressionKey chain.2] := by
    simp only [PropertyKeys,List.cons.injEq,List.map_eq_nil_iff]
    tauto
  have leftRec : (expressionKey chain.1.first = expressionKey chain.2 ∧
      AllBelow order (expressionKey chain.2) (expressionKey chain.1.second :: chain.1.rest.val.map expressionKey)) ↔
      (∃ tail, PropertyKeys chain.1 = expressionKey chain.2 :: tail ∧ AllBelow order (expressionKey chain.2) tail) := by
    constructor
    · rintro ⟨first,below⟩
      exact ⟨_,by simp only [PropertyKeys,first],below⟩
    · rintro ⟨tail,equal,below⟩
      obtain ⟨first,other⟩ := List.cons.inj equal
      exact ⟨first,by simpa only [other] using below⟩
  change (Top (expressionKey chain.2) ∨ _ ∨ AllBelow order (expressionKey chain.2) (PropertyKeys chain.1) ∨ _ ∨ _) ↔ _
  rw [transitive]
  change (Top (expressionKey chain.2) ∨ PropertyKeys chain.1 = [expressionKey chain.2,expressionKey chain.2] ∨
    AllBelow order (expressionKey chain.2) (PropertyKeys chain.1) ∨
    (expressionKey chain.1.first = expressionKey chain.2 ∧ AllBelow order (expressionKey chain.2) (expressionKey chain.1.second :: chain.1.rest.val.map expressionKey)) ∨
    (∃ before,PropertyKeys chain.1 = before ++ [expressionKey chain.2] ∧ AllBelow order (expressionKey chain.2) before)) ↔ _
  rw [leftRec]
  rfl

private theorem selected_conditions (order : Key → Key → Prop) (sup first second : Key) (rest : List Key)
    (strict : ¬ order sup sup) (notTop : ¬ Top sup) :
    AllBelow order sup (Selected sup (first :: second :: rest)) ↔
      Conditions order sup (first :: second :: rest) := by
  by_cases starts : first = sup
  · subst first
    by_cases short : second :: rest = [sup]
    · simp [Selected,Conditions,short,AllBelow]
    · simp only [Selected,if_pos rfl,if_neg short]
      constructor
      · intro below
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨second :: rest,rfl,below⟩)))
      · rintro (top | exactPair | all | ⟨tail,equal,below⟩ | ⟨before,equal,below⟩)
        · exact False.elim (notTop top)
        · exact False.elim (short (List.cons.inj exactPair).2)
        · exact (List.forall_mem_cons.mp all).2
        · have same : second :: rest = tail := (List.cons.inj equal).2
          simpa [same] using below
        · cases before with
          | nil => simp at equal
          | cons head tail =>
            have same : sup = head := (List.cons.inj equal).1
            exact False.elim (strict (by simpa [same] using (List.forall_mem_cons.mp below).1))
  · rw [Selected,if_neg starts,trim_last_iff]
    unfold Conditions
    constructor
    · rintro (all | last)
      · exact Or.inr (Or.inr (Or.inl all))
      · exact Or.inr (Or.inr (Or.inr (Or.inr last)))
    · rintro (top | exactPair | all | ⟨tail,equal,below⟩ | last)
      · exact False.elim (notTop top)
      · exact False.elim (starts (List.cons.inj exactPair).1)
      · exact Or.inl all
      · exact False.elim (starts (List.cons.inj equal).1)
      · exact Or.inr last

/-- For a strict order, the chain alternatives reduce exactly to the forced
    dependency list. Endpoint recursion is preserved; middle recursion forces
    a self-dependency and must subsequently be rejected. -/
theorem chain_seeds_iff (order : Key → Key → Prop) (chain : Chain)
    (strict : ∀ role, ¬ order role role) :
    (∀ edge ∈ ChainSeeds chain, order edge.1 edge.2) ↔ ChainOrdered order chain := by
  rw [chain_conditions]
  by_cases top : Top (expressionKey chain.2)
  · simp [ChainSeeds,top,Conditions]
  · simp only [ChainSeeds,if_neg top]
    have below : (∀ edge ∈ (Selected (expressionKey chain.2) (PropertyKeys chain.1)).map (fun role => (role,expressionKey chain.2)), order edge.1 edge.2) ↔
        AllBelow order (expressionKey chain.2) (Selected (expressionKey chain.2) (PropertyKeys chain.1)) := by
      constructor
      · intro below role member
        exact below (role,expressionKey chain.2) (List.mem_map.mpr ⟨role,member,rfl⟩)
      · intro below edge member
        obtain ⟨role,roleMember,rfl⟩ := List.mem_map.mp member
        exact below role roleMember
    rw [below]
    exact selected_conditions order (expressionKey chain.2) _ _ _ (strict _) top

private theorem trim_last_subset (sup : Key) (terms : List Key) : ∀ role ∈ TrimLast sup terms, role ∈ terms := by
  induction terms with
  | nil => simp [TrimLast]
  | cons head tail ih =>
    cases tail with
    | nil => by_cases same : head = sup <;> simp [TrimLast,same]
    | cons second rest =>
      intro role member
      rcases List.mem_cons.mp member with member | member
      · simp [member]
      · exact List.mem_cons_of_mem _ (ih role member)

private theorem selected_subset (sup : Key) (terms : List Key) : ∀ role ∈ Selected sup terms, role ∈ terms := by
  cases terms with
  | nil => simp [Selected]
  | cons head tail =>
    by_cases first : head = sup
    · by_cases short : tail = [sup]
      · simp [Selected,first,short]
      · intro role member
        exact List.mem_cons_of_mem _ (by simpa only [Selected,if_pos first,if_neg short] using member)
    · intro role member
      exact trim_last_subset sup _ role (by simpa only [Selected,if_neg first] using member)

private theorem nodes_iff (rows : List Rowl.Collection.Row) (role : Key) :
    role ∈ Nodes rows ↔ (role.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ rows := by
  rcases role with ⟨iri,orientation⟩
  cases orientation <;> simp [Nodes,List.mem_flatMap]

private theorem inverse_nodes (items : List AnnotatedAxiom) (role : Key) (member : role ∈ AllNodes items) :
    inverse role ∈ AllNodes items := by
  obtain ⟨item,itemMember,roleMember⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨item,itemMember,(nodes_iff _ _).mpr ((nodes_iff _ role).mp roleMember)⟩

private theorem object_uses (expression : ObjectPropertyExpression) :
    Rowl.Collection.objectUses expression = [((expressionKey expression).1,RowlRust.typing.EntityKind.ObjectProperty)] := by
  cases expression <;> rfl

private theorem property_keys_typed (values : AtLeastTwo ObjectPropertyExpression) (role : Key)
    (member : role ∈ PropertyKeys values) :
    (role.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ values.elements.flatMap Rowl.Collection.objectUses := by
  have mapped : PropertyKeys values = values.elements.map expressionKey := by simp [PropertyKeys,AtLeastTwo.elements]
  rw [mapped] at member
  obtain ⟨expression,expressionMember,rfl⟩ := List.mem_map.mp member
  exact List.mem_flatMap.mpr ⟨expression,expressionMember,by simp [object_uses]⟩

private theorem seeds_nodes (items : List AnnotatedAxiom) (sub sup : Key) (member : (sub,sup) ∈ Seeds items) :
    sub ∈ AllNodes items ∧ sup ∈ AllNodes items := by
  obtain ⟨chain,chainMember,seedMember⟩ := List.mem_flatMap.mp member
  obtain ⟨item,itemMember,axiomMember⟩ := List.mem_flatMap.mp chainMember
  have localNodes : sub ∈ Nodes (Rowl.Collection.axiomUses item.axiom) ∧ sup ∈ Nodes (Rowl.Collection.axiomUses item.axiom) := by
    cases body : item.axiom with
    | SubObjectPropertyOf source target =>
      rw [body] at axiomMember
      cases source with
      | Single expression => simp [AxiomChains] at axiomMember
      | Chain operands =>
        have equal : chain = (operands,target) := by simpa [AxiomChains] using axiomMember
        subst chain
        by_cases top : Top (expressionKey target)
        · simp [ChainSeeds,top] at seedMember
        · obtain ⟨role,roleMember,equal⟩ := List.mem_map.mp (by simpa only [ChainSeeds,if_neg top] using seedMember)
          have roleIsSub : role = sub := congrArg Prod.fst equal
          have targetIsSup : expressionKey target = sup := congrArg Prod.snd equal
          have typed := property_keys_typed operands role (selected_subset _ _ _ roleMember)
          constructor
          · rw [← roleIsSub]
            apply (nodes_iff _ _).mpr
            exact List.mem_append_left _ typed
          · rw [← targetIsSup]
            apply (nodes_iff _ _).mpr
            simp [Rowl.Collection.axiomUses,object_uses]
    | _ => simp [AxiomChains,body] at axiomMember
  have lift (role : Key) (member : role ∈ Nodes (Rowl.Collection.axiomUses item.axiom)) : role ∈ AllNodes items :=
    List.mem_flatMap.mpr ⟨item,itemMember,(nodes_iff _ _).mpr (List.mem_append_right _ ((nodes_iff _ _).mp member))⟩
  exact ⟨lift sub localNodes.1,lift sup localNodes.2⟩

private theorem derived_nodes (items : List AnnotatedAxiom) {sub sup : Key} (derived : Derived (Seeds items) sub sup) :
    sub ∈ AllNodes items ∧ sup ∈ AllNodes items := by
  induction derived with
  | seed member => exact seeds_nodes items _ _ member
  | trans first second ih₁ ih₂ => exact ⟨ih₁.1,ih₂.2⟩
  | source_inverse path direct ih => exact ⟨inverse_nodes items _ ih.1,ih.2⟩

private theorem universe_iff (nodes : List Key) (sub sup : Key) :
    (sub,sup) ∈ Universe nodes ↔ sub ∈ nodes ∧ sup ∈ nodes := by
  constructor
  · intro member
    obtain ⟨a,first,inside⟩ := List.mem_flatMap.mp member
    obtain ⟨b,second,equal⟩ := List.mem_map.mp inside
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
    exact ⟨first,second⟩
  · rintro ⟨first,second⟩
    exact List.mem_flatMap.mpr ⟨sub,first,List.mem_map.mpr ⟨sup,second,rfl⟩⟩

private theorem facts_order_total (items : List AnnotatedAxiom) (facts : RoleFacts) (correct : ClosureCorrect items facts) :
    ∃ output, (do let seeds ← all_chain_seeds facts.chains; close_order facts.nodes seeds) = .ok (.Complete output) ∧
      (edgeKeys output).Nodup ∧ ∀ sub sup, (sub,sup) ∈ edgeKeys output ↔ Derived (Seeds items) sub sup := by
  obtain ⟨seeds,seedsExecuted,seedsCorrect⟩ := all_chain_seeds_total facts.chains
  rw [correct.2.2.2.2] at seedsCorrect
  have allPresent : ∀ sub sup, Derived (edgeKeys seeds) sub sup → (sub,sup) ∈ Universe (roleKeys facts.nodes) := by
    intro sub sup derived
    rw [correct.1,universe_iff]
    exact derived_nodes items (by simpa only [seedsCorrect,Seeds] using derived)
  obtain ⟨output,executed⟩ := (close_order_complete_iff facts.nodes seeds).mpr allPresent
  obtain ⟨actual,run,outputCorrect⟩ := close_order_total_correct facts.nodes seeds
  have equal := Result.ok_injective (run.symm.trans executed)
  rw [equal] at outputCorrect
  exact ⟨output,by simp [seedsExecuted,executed],outputCorrect.1,by simpa only [seedsCorrect,Seeds] using outputCorrect.2.2⟩

/-- Actual chain syntax supplies the full finite universe needed by order
    closure. MissingPair is impossible; output is precisely the forced closure. -/
theorem least_chain_order_total_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ output, least_chain_order items = .ok (.Complete output) ∧
      (edgeKeys output).Nodup ∧ ∀ sub sup, (sub,sup) ∈ edgeKeys output ↔ Derived (Seeds items.val) sub sup := by
  obtain ⟨facts,collected,correct⟩ := collect_facts_total_correct items
  obtain ⟨output,executed,distinct,membership⟩ := facts_order_total items.val facts correct
  refine ⟨output,?_,distinct,membership⟩
  simp only [least_chain_order,collected,bind_ok]
  exact executed

/-- Predicate satisfied by an actual finite ordering witness. -/
def Witness (items : List AnnotatedAxiom) (order : Key → Key → Prop) : Prop :=
  (∀ sub sup, order sub sup → sub ∈ AllNodes items ∧ sup ∈ AllNodes items) ∧
  (∀ role, ¬ order role role) ∧
  (∀ a b c, order a b → order b c → order a c) ∧
  (∀ left right : Iri, (left,false) ∈ AllNodes items → (right,false) ∈ AllNodes items →
    (order (left,false) (right,false) ↔ order (left,true) (right,false))) ∧
  (∀ sub sup, order sub sup → ¬ Reachable items sup sub) ∧
  (∀ chain ∈ items.flatMap (fun item => AxiomChains item.axiom),ChainOrdered order chain)

private theorem derived_minimal (items : List AnnotatedAxiom) (order : Key → Key → Prop)
    (witness : Witness items order) {sub sup : Key} (derived : Derived (Seeds items) sub sup) : order sub sup := by
  obtain ⟨inside,strict,transitive,inversions,compatible,chains⟩ := witness
  induction derived with
  | seed member =>
    obtain ⟨chain,chainMember,seedMember⟩ := List.mem_flatMap.mp member
    exact (chain_seeds_iff order chain strict).mpr (chains chain chainMember) _ seedMember
  | trans first second ih₁ ih₂ => exact transitive _ _ _ ih₁ ih₂
  | @source_inverse sub sup path direct ih =>
    have typed := derived_nodes items path
    rcases sub with ⟨left,orientation⟩
    rcases sup with ⟨right,direction⟩
    cases direction with
    | true => simp at direct
    | false =>
      cases orientation with
      | false =>
        exact (inversions left right typed.1 typed.2).mp ih
      | true =>
        have normal : (left,false) ∈ AllNodes items := inverse_nodes items _ typed.1
        exact (inversions left right normal typed.2).mpr ih

/-- Every permitted ordering contains the computed closure. A conflicting
    derived pair therefore proves nonexistence of any valid ordering. -/
theorem forced_conflict_implies_irregular (items : List AnnotatedAxiom) (sub sup : Key)
    (derived : Derived (Seeds items) sub sup) (opposite : Reachable items sup sub) : ¬ Regular items := by
  rintro ⟨order,witness⟩
  have forced := derived_minimal items order witness derived
  exact witness.2.2.2.2.1 sub sup forced opposite

private theorem derived_witness (items : List AnnotatedAxiom)
    (compatible : ∀ sub sup, Derived (Seeds items) sub sup → ¬ Reachable items sup sub) :
    Witness items (Derived (Seeds items)) := by
  have strict (role : Key) : ¬ Derived (Seeds items) role role := fun derived => compatible role role derived Relation.ReflTransGen.refl
  refine ⟨fun _ _ derived => derived_nodes items derived,strict,fun _ _ _ first second => first.trans second,?_,compatible,?_⟩
  · intro left right leftMember rightMember
    constructor
    · intro derived; exact derived.source_inverse rfl
    · intro derived; exact derived.source_inverse rfl
  · intro chain member
    apply (chain_seeds_iff _ chain strict).mp
    intro edge seed
    exact Derived.seed (List.mem_flatMap.mpr ⟨chain,member,seed⟩)

private theorem hierarchy_closure_total (items : List AnnotatedAxiom) (facts : RoleFacts)
    (correct : ClosureCorrect items facts) (source : Role) (present : key source ∈ AllNodes items) :
    ∃ output, non_simple_closure facts.nodes (.Entry source .Empty) facts.edges = .ok (.Complete output) ∧
      ∀ role, role ∈ roleKeys output ↔ Reachable items (key source) role := by
  have edgesEq : (fun sub sup => (sub,sup) ∈ edgeKeys facts.edges) = Hierarchy items := by
    funext sub sup
    apply propext
    rw [correct.2.1]
    simp [Hierarchy,List.mem_flatMap]
  have reachEq (role : Key) : Rowl.RoleClosure.Reach (edgeKeys facts.edges) (roleKeys (.Entry source .Empty)) role ↔
      Reachable items (key source) role := by
    unfold Rowl.RoleClosure.Reach
    rw [edgesEq]
    simp only [roleKeys,List.mem_singleton,exists_eq_left]
    rfl
  have reachedPresent : ∀ role, Rowl.RoleClosure.Reach (edgeKeys facts.edges) (roleKeys (.Entry source .Empty)) role →
      role ∈ roleKeys facts.nodes := by
    intro role reached
    rw [correct.1]
    have path := (reachEq role).mp reached
    induction path with
    | refl => exact present
    | @tail sub sup path edge ih => exact Rowl.RoleClosure.hierarchy_target_nodes items sub sup edge
  obtain ⟨output,executed⟩ := (Rowl.RoleClosure.non_simple_closure_complete_iff facts.nodes (.Entry source .Empty) facts.edges).mpr reachedPresent
  obtain ⟨actual,run,outputCorrect⟩ := Rowl.RoleClosure.non_simple_closure_total_correct facts.nodes (.Entry source .Empty) facts.edges
  have equal := Result.ok_injective (run.symm.trans executed)
  rw [equal] at outputCorrect
  exact ⟨output,executed,fun role => (outputCorrect.2.2 role).trans (reachEq role)⟩

private theorem contains_role_total (values : Roles) (sought : Role) :
    contains_role values sought = .ok (decide (key sought ∈ roleKeys values),values) := by
  induction values with
  | Empty => simp [contains_role,roleKeys]
  | Entry role next ih =>
    rw [contains_role,Rowl.RoleClosure.same_role_total_correct]
    by_cases same : key role = key sought
    · simp [same,roleKeys]
    · simp [same,ih,roleKeys,Ne.symm same]

private def Checked (items : List AnnotatedAxiom) (original : Edges) : RegularityCheck → Prop
  | .Regular order => edgeKeys order = edgeKeys original ∧
      ∀ sub sup, (sub,sup) ∈ edgeKeys original → ¬ Reachable items sup sub
  | .HierarchyConflict sub sup => ∃ before after,
      edgeKeys original = before ++ (key sub,key sup) :: after ∧
      (∀ sub sup, (sub,sup) ∈ before → ¬ Reachable items sup sub) ∧ Reachable items (key sup) (key sub)
  | .MissingPair _ _ | .MissingHierarchyNode _ => False

private theorem check_pairs_total (items : alloc.vec.Vec AnnotatedAxiom) (original : Edges)
    (inside : ∀ sub sup, (sub,sup) ∈ edgeKeys original → sub ∈ AllNodes items.val ∧ sup ∈ AllNodes items.val) :
    ∃ output, check_pairs items original = .ok output ∧ Checked items.val original output := by
  induction original with
  | Empty => exact ⟨.Regular .Empty,by simp [check_pairs],by simp [Checked,edgeKeys]⟩
  | Entry sub sup next ih =>
    have present := (inside (key sub) (key sup) (by simp [edgeKeys])).2
    obtain ⟨facts,collected,factsCorrect⟩ := collect_facts_total_correct items
    obtain ⟨reached,classified,reachEq⟩ := hierarchy_closure_total items.val facts factsCorrect sup present
    have contains := contains_role_total reached sub
    by_cases conflict : Reachable items.val (key sup) (key sub)
    · have member : key sub ∈ roleKeys reached := (reachEq _).mpr conflict
      refine ⟨.HierarchyConflict sub sup,by simp [check_pairs,collected,classified,contains,member],[],edgeKeys next,?_,?_,conflict⟩
      · simp [edgeKeys]
      · simp
    · have member : key sub ∉ roleKeys reached := fun h => conflict ((reachEq _).mp h)
      obtain ⟨output,executed,correct⟩ := ih (fun a b h => inside a b (by simp [edgeKeys,h]))
      cases output with
      | Regular order =>
        refine ⟨.Regular (.Entry sub sup order),by simp [check_pairs,collected,classified,contains,member,executed],?_,?_⟩
        · simp [edgeKeys,correct.1]
        · intro a b h
          rcases List.mem_cons.mp h with equal | h
          · cases equal; exact conflict
          · exact correct.2 a b h
      | HierarchyConflict a b =>
        obtain ⟨before,after,order,prior,opposite⟩ := correct
        refine ⟨.HierarchyConflict a b,by simp [check_pairs,collected,classified,contains,member,executed],
          (key sub,key sup) :: before,after,?_,?_,opposite⟩
        · simp [edgeKeys,order]
        · intro a b h
          rcases List.mem_cons.mp h with equal | h
          · cases equal; exact conflict
          · exact prior a b h
      | MissingPair a b => exact False.elim correct
      | MissingHierarchyNode role => exact False.elim correct

/-- A concrete permitted order or an unavoidable hierarchy conflict. The two
    malformed-universe outcomes are excluded for the actual raw entry point. -/
def RegularityCorrect (items : List AnnotatedAxiom) : RegularityCheck → Prop
  | .Regular order => (edgeKeys order).Nodup ∧ Witness items (fun sub sup => (sub,sup) ∈ edgeKeys order)
  | .HierarchyConflict sub sup => Derived (Seeds items) (key sub) (key sup) ∧
      Reachable items (key sup) (key sub) ∧ ¬ Regular items
  | .MissingPair _ _ | .MissingHierarchyNode _ => False

/-- Actual full raw-closure regularity decision is total, with a concrete order
    on success and an unavoidable forced-pair contradiction on rejection. -/
theorem check_regularity_total_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ output, check_regularity items = .ok output ∧ RegularityCorrect items.val output := by
  obtain ⟨order,ordered,distinct,membership⟩ := least_chain_order_total_correct items
  have inside : ∀ sub sup, (sub,sup) ∈ edgeKeys order → sub ∈ AllNodes items.val ∧ sup ∈ AllNodes items.val :=
    fun sub sup h => derived_nodes items.val ((membership sub sup).mp h)
  obtain ⟨output,checked,correct⟩ := check_pairs_total items order inside
  refine ⟨output,by simp [check_regularity,ordered,checked],?_⟩
  cases output with
  | Regular actual =>
    obtain ⟨same,compatible⟩ := correct
    have relationEq : (fun sub sup => (sub,sup) ∈ edgeKeys actual) = Derived (Seeds items.val) := by
      funext sub sup
      apply propext
      rw [same]
      exact membership sub sup
    refine ⟨by simpa [same] using distinct,?_⟩
    rw [relationEq]
    exact derived_witness items.val (fun sub sup derived => compatible sub sup ((membership sub sup).mpr derived))
  | HierarchyConflict sub sup =>
    obtain ⟨before,after,sequence,prior,opposite⟩ := correct
    have present : (key sub,key sup) ∈ edgeKeys order := by rw [sequence]; simp
    have derived := (membership _ _).mp present
    exact ⟨derived,opposite,forced_conflict_implies_irregular items.val _ _ derived opposite⟩
  | MissingPair sub sup => exact False.elim correct
  | MissingHierarchyNode role => exact False.elim correct

/-- Success iff some ordering satisfies precisely the independent OWL 2
    structural property-hierarchy restriction; no caller supplies that order. -/
theorem check_regularity_accepted_iff (items : alloc.vec.Vec AnnotatedAxiom) :
    (∃ order, check_regularity items = .ok (.Regular order)) ↔ Regular items.val := by
  obtain ⟨output,executed,correct⟩ := check_regularity_total_correct items
  constructor
  · rintro ⟨order,accepted⟩
    have equal := Result.ok_injective (executed.symm.trans accepted)
    rw [equal] at correct
    exact ⟨_,correct.2⟩
  · intro regular
    cases output with
    | Regular order => exact ⟨order,executed⟩
    | HierarchyConflict sub sup => exact False.elim (correct.2.2 regular)
    | MissingPair sub sup => exact False.elim correct
    | MissingHierarchyNode role => exact False.elim correct

end Rowl.RoleOrder
