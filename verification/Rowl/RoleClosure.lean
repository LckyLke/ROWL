import Rowl.Roles
import Rowl.Symbols

namespace Rowl.RoleClosure
open Aeneas Aeneas.Std RowlRust.model RowlRust.roles Rowl.Roles
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- Multi-root reachability in the supplied finite structural graph. -/
def Reach (edges : List Edge) (roots : List Key) (target : Key) : Prop :=
  ∃ root ∈ roots, Relation.ReflTransGen (fun sub sup => (sub,sup) ∈ edges) root target

/-- Completeness retains exact role identity and rejects a reached absent node.
    Duplicate inputs are permitted; complete output contains each key once. -/
def Correct (nodes roots : List Key) (edges : List Edge) : RoleClosure → Prop
  | .Complete roles => (roleKeys roles).Nodup ∧
      (∀ role ∈ roleKeys roles, role ∈ nodes) ∧
      ∀ role, role ∈ roleKeys roles ↔ Reach edges roots role
  | .MissingNode role => Reach edges roots (key role) ∧ key role ∉ nodes

private theorem iri_equal (left right : Iri) :
    left.spelling.val = right.spelling.val ↔ left = right := by
  constructor
  · intro h
    cases left with | mk a => cases right with | mk b =>
      have equal := alloc.vec.Vec.ext a b h
      cases equal
      rfl
  · rintro rfl; rfl

/-- Comparisons use byte identity, not reference identity or normalized IRIs. -/
theorem same_role_total_correct (left right : Role) :
    same_role left right = .ok (decide (key left = key right)) := by
  rw [same_role]
  rw [Rowl.Symbols.same_spelling_total_correct]
  by_cases orientation : left.inverse = right.inverse
  · simp [orientation,key,iri_equal]
  · simp [orientation,key]

private theorem contains_total (roles : Roles) (sought : Role) :
    contains_role roles sought = .ok (decide (key sought ∈ roleKeys roles),roles) := by
  induction roles with
  | Empty => simp [contains_role,roleKeys]
  | Entry role next ih =>
    rw [contains_role,same_role_total_correct]
    by_cases same : key role = key sought
    · simp [same,roleKeys]
    · simp [same,ih,roleKeys,Ne.symm same]

private def TakenCorrect (roles : Roles) (sought : Role) : TakenRole → Prop
  | .Missing => key sought ∉ roleKeys roles
  | .Found remaining => (roleKeys roles).Perm (key sought :: roleKeys remaining)

private theorem take_total (roles : Roles) (sought : Role) :
    ∃ result, take_role roles sought = .ok result ∧ TakenCorrect roles sought result := by
  induction roles with
  | Empty => exact ⟨.Missing,by simp [take_role],by simp [TakenCorrect,roleKeys]⟩
  | Entry role next ih =>
    by_cases same : key role = key sought
    · refine ⟨.Found next,by simp [take_role,same_role_total_correct,same],?_⟩
      simp [TakenCorrect,roleKeys,same]
    · obtain ⟨taken,executed,correct⟩ := ih
      cases taken with
      | Missing =>
        exact ⟨.Missing,by simp [take_role,same_role_total_correct,same,executed],
          by simpa [TakenCorrect,roleKeys,Ne.symm same] using correct⟩
      | Found remaining =>
        refine ⟨.Found (.Entry role remaining),by simp [take_role,same_role_total_correct,same,executed],?_⟩
        exact (List.Perm.cons (key role) correct).trans (List.Perm.swap ..)

private theorem successors_total (edges : Edges) (source : Role) :
    ∃ output, successors edges source = .ok (output,edges) ∧
      ∀ target, target ∈ roleKeys output ↔ (key source,target) ∈ edgeKeys edges := by
  induction edges with
  | Empty => exact ⟨.Empty,by simp [successors],by simp [roleKeys,edgeKeys]⟩
  | Entry sub sup next ih =>
    obtain ⟨output,executed,correct⟩ := ih
    by_cases same : key sub = key source
    · refine ⟨.Entry sup output,by simp [successors,executed,copy_role,same_role_total_correct,same],?_⟩
      intro target
      simp [roleKeys,edgeKeys,same,correct target]
    · refine ⟨output,by simp [successors,executed,copy_role,same_role_total_correct,same],?_⟩
      intro target
      simp [edgeKeys,Ne.symm same,correct target]

private theorem append_total (left right : Roles) :
    ∃ output, roles_append left right = .ok output ∧ roleKeys output = roleKeys left ++ roleKeys right := by
  induction left with
  | Empty => exact ⟨right,by simp [roles_append],by simp [roleKeys]⟩
  | Entry role next ih =>
    obtain ⟨output,executed,correct⟩ := ih
    exact ⟨.Entry role output,by simp [roles_append,executed],by simp [roleKeys,correct]⟩

private structure Invariant (nodes roots : List Key) (edges : List Edge)
    (pending available resolved : Roles) : Prop where
  partition : (roleKeys available ++ roleKeys resolved).Perm nodes
  distinct : (roleKeys resolved).Nodup
  pendingReach : ∀ role ∈ roleKeys pending, Reach edges roots role
  resolvedReach : ∀ role ∈ roleKeys resolved, Reach edges roots role
  rootFrontier : ∀ root ∈ roots, root ∈ roleKeys resolved ∨ root ∈ roleKeys pending
  edgeFrontier : ∀ source ∈ roleKeys resolved, ∀ target,
    (source,target) ∈ edges → target ∈ roleKeys resolved ∨ target ∈ roleKeys pending

private theorem finish (nodes roots : List Key) (edges : List Edge) (available resolved : Roles)
    (inv : Invariant nodes roots edges .Empty available resolved) :
    Correct nodes roots edges (.Complete resolved) := by
  refine ⟨inv.distinct,?_,fun role => ⟨inv.resolvedReach role,?_⟩⟩
  · intro role member
    exact inv.partition.mem_iff.mp (List.mem_append_right _ member)
  · rintro ⟨root,rootMember,path⟩
    have rootResolved : root ∈ roleKeys resolved := by simpa [roleKeys] using inv.rootFrontier root rootMember
    induction path with
    | refl => exact rootResolved
    | @tail source target path edge ih => simpa [roleKeys] using inv.edgeFrontier source ih target edge

private theorem advance_seen (nodes roots : List Key) (edges : List Edge) (role : Role)
    (tail available resolved : Roles)
    (inv : Invariant nodes roots edges (.Entry role tail) available resolved)
    (seen : key role ∈ roleKeys resolved) : Invariant nodes roots edges tail available resolved := by
  have move (target : Key) (h : target ∈ roleKeys resolved ∨ target ∈ roleKeys (.Entry role tail)) :
      target ∈ roleKeys resolved ∨ target ∈ roleKeys tail := by
    rcases h with h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl (h ▸ seen)
      · exact Or.inr h
  refine ⟨inv.partition,inv.distinct,?_,inv.resolvedReach,?_,?_⟩
  · intro target h; exact inv.pendingReach target (by simp [roleKeys,h])
  · intro root h; exact move root (inv.rootFrontier root h)
  · intro source h target edge; exact move target (inv.edgeFrontier source h target edge)

private theorem advance_new (nodes roots : List Key) (edges : List Edge) (role : Role)
    (tail available resolved remaining pending neighbors : Roles)
    (inv : Invariant nodes roots edges (.Entry role tail) available resolved)
    (unseen : key role ∉ roleKeys resolved)
    (taken : (roleKeys available).Perm (key role :: roleKeys remaining))
    (neighborKeys : ∀ target, target ∈ roleKeys neighbors ↔ (key role,target) ∈ edges)
    (pendingKeys : roleKeys pending = roleKeys neighbors ++ roleKeys tail) :
    Invariant nodes roots edges pending remaining (.Entry role resolved) := by
  have roleReach : Reach edges roots (key role) := inv.pendingReach (key role) (by simp [roleKeys])
  have move (target : Key) (h : target ∈ roleKeys resolved ∨ target ∈ roleKeys (.Entry role tail)) :
      target ∈ roleKeys (.Entry role resolved) ∨ target ∈ roleKeys pending := by
    rcases h with h | h
    · exact Or.inl (by simp [roleKeys,h])
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl (by simp [roleKeys,h])
      · exact Or.inr (by rw [pendingKeys]; exact List.mem_append_right _ h)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have moved := taken.append_right (roleKeys resolved)
    have reorder : ((key role :: roleKeys remaining) ++ roleKeys resolved).Perm
        (roleKeys remaining ++ key role :: roleKeys resolved) := List.perm_middle.symm
    exact (moved.trans reorder).symm.trans inv.partition
  · simpa [roleKeys,List.nodup_cons] using And.intro unseen inv.distinct
  · intro target h
    rw [pendingKeys] at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨root,member,path⟩ := roleReach
      exact ⟨root,member,path.tail ((neighborKeys target).mp h)⟩
    · exact inv.pendingReach target (by simp [roleKeys,h])
  · intro target h
    rcases List.mem_cons.mp h with h | h
    · exact h ▸ roleReach
    · exact inv.resolvedReach target h
  · intro root h; exact move root (inv.rootFrontier root h)
  · intro source h target edge
    rcases List.mem_cons.mp h with h | h
    · subst source
      exact Or.inr (by rw [pendingKeys]; exact List.mem_append_left _ ((neighborKeys target).mpr edge))
    · exact move target (inv.edgeFrontier source h target edge)

private theorem discover_total (nodes roots : List Key) (edges : Edges)
    (pending available resolved : Roles)
    (inv : Invariant nodes roots (edgeKeys edges) pending available resolved) :
    ∃ output, discover_roles pending available resolved edges = .ok output ∧ Correct nodes roots (edgeKeys edges) output := by
  cases pending with
  | Empty => exact ⟨.Complete resolved,by simp [discover_roles],finish nodes roots _ available resolved inv⟩
  | Entry role tail =>
    have contains := contains_total resolved role
    by_cases seen : key role ∈ roleKeys resolved
    · obtain ⟨output,executed,correct⟩ := discover_total nodes roots edges tail available resolved
        (advance_seen nodes roots _ role tail available resolved inv seen)
      exact ⟨output,by simp [discover_roles,contains,seen,executed],correct⟩
    · obtain ⟨taken,takeExecuted,takeCorrect⟩ := take_total available role
      cases taken with
      | Missing =>
        refine ⟨.MissingNode role,by simp [discover_roles,contains,seen,takeExecuted],?_,?_⟩
        · exact inv.pendingReach (key role) (by simp [roleKeys])
        · intro member
          have partition := inv.partition.mem_iff.mpr member
          rcases List.mem_append.mp partition with h | h
          · exact takeCorrect h
          · exact seen h
      | Found remaining =>
        obtain ⟨neighbors,neighborsExecuted,neighborsCorrect⟩ := successors_total edges role
        obtain ⟨next,nextExecuted,nextCorrect⟩ := append_total neighbors tail
        have nextInv := advance_new nodes roots _ role tail available resolved remaining next neighbors inv seen takeCorrect neighborsCorrect nextCorrect
        obtain ⟨output,executed,correct⟩ := discover_total nodes roots edges next remaining (.Entry role resolved) nextInv
        exact ⟨output,by simp [discover_roles,contains,seen,takeExecuted,neighborsExecuted,nextExecuted,executed],correct⟩
termination_by ((roleKeys available).length,(roleKeys pending).length)
decreasing_by
  · simp_all [roleKeys]
  · have lengthEq := takeCorrect.length_eq
    change (roleKeys available).length = (key role :: roleKeys remaining).length at lengthEq
    simp only [List.length_cons] at lengthEq
    simp_wf
    omega

/-- Actual finite worklist reachability is total, exact and duplicate tolerant.
    The decreasing available-node/pending-task measure needs no fuel bound. -/
theorem non_simple_closure_total_correct (nodes roots : Roles) (edges : Edges) :
    ∃ output, non_simple_closure nodes roots edges = .ok output ∧
      Correct (roleKeys nodes) (roleKeys roots) (edgeKeys edges) output := by
  have inv : Invariant (roleKeys nodes) (roleKeys roots) (edgeKeys edges) roots nodes .Empty := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simp [roleKeys]
    · simp [roleKeys]
    · intro role member; exact ⟨role,member,Relation.ReflTransGen.refl⟩
    · simp [roleKeys]
    · intro root member; exact Or.inr member
    · simp [roleKeys]
  simpa [non_simple_closure] using discover_total _ _ edges roots nodes .Empty inv

/-- A complete result is possible precisely when every reached key is present
    in the supplied node universe. Unreached absent endpoints do not interfere. -/
theorem non_simple_closure_complete_iff (nodes roots : Roles) (edges : Edges) :
    (∃ output, non_simple_closure nodes roots edges = .ok (.Complete output)) ↔
      ∀ role, Reach (edgeKeys edges) (roleKeys roots) role → role ∈ roleKeys nodes := by
  constructor
  · rintro ⟨output,executed⟩
    obtain ⟨actual,run,correct⟩ := non_simple_closure_total_correct nodes roots edges
    have equal := Result.ok_injective (run.symm.trans executed)
    rw [equal] at correct
    exact fun role reach => correct.2.1 role ((correct.2.2 role).mpr reach)
  · intro present
    obtain ⟨actual,run,correct⟩ := non_simple_closure_total_correct nodes roots edges
    cases actual with
    | Complete output => exact ⟨output,run⟩
    | MissingNode role => exact False.elim (correct.2 (present (key role) correct.1))

private theorem nodes_iff (rows : List Rowl.Collection.Row) (role : Key) :
    role ∈ Nodes rows ↔ (role.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ rows := by
  rcases role with ⟨iri,orientation⟩
  cases orientation <;> simp [Nodes,List.mem_flatMap]

private theorem object_uses (expression : ObjectPropertyExpression) :
    Rowl.Collection.objectUses expression = [((expressionKey expression).1,RowlRust.typing.EntityKind.ObjectProperty)] := by
  cases expression <;> rfl

private theorem directed_typed (rows : List Rowl.Collection.Row) (sub sup : Key)
    (subTyped : (sub.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ rows)
    (supTyped : (sup.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ rows) (edge : Edge)
    (member : edge ∈ Directed sub sup) :
    (edge.1.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ rows ∧
    (edge.2.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ rows := by
  simp only [Rowl.Roles.Directed,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl <;> exact ⟨subTyped,supTyped⟩

private theorem equivalent_typed (rows : List Rowl.Collection.Row) (sub sup : Key)
    (subTyped : (sub.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ rows)
    (supTyped : (sup.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ rows) (edge : Edge)
    (member : edge ∈ Equivalent sub sup) :
    (edge.1.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ rows ∧
    (edge.2.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ rows := by
  rcases List.mem_append.mp member with h | h
  · exact directed_typed rows sub sup subTyped supTyped edge h
  · exact directed_typed rows sup sub supTyped subTyped edge h

private theorem pairs_typed (rows : List Rowl.Collection.Row) (roles : List Key)
    (typed : ∀ role ∈ roles, (role.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ rows)
    (edge : Edge) (member : edge ∈ Pairs roles) :
    (edge.1.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ rows ∧
    (edge.2.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ rows := by
  induction roles with
  | nil => simp [Pairs] at member
  | cons head tail ih =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨other,otherMember,edgeMember⟩ := List.mem_flatMap.mp h
      exact equivalent_typed rows head other (typed head (by simp)) (typed other (by simp [otherMember])) edge edgeMember
    · exact ih (fun role h => typed role (by simp [h])) h

private theorem property_keys_typed (values : AtLeastTwo ObjectPropertyExpression) (role : Key)
    (member : role ∈ PropertyKeys values) :
    (role.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ values.elements.flatMap Rowl.Collection.objectUses := by
  have mapped : PropertyKeys values = values.elements.map expressionKey := by simp [PropertyKeys,AtLeastTwo.elements]
  rw [mapped] at member
  obtain ⟨expression,expressionMember,rfl⟩ := List.mem_map.mp member
  exact List.mem_flatMap.mpr ⟨expression,expressionMember,by simp [object_uses]⟩

private theorem axiom_edges_typed (body : Axiom) (edge : Edge) (member : edge ∈ AxiomEdges body) :
    (edge.1.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ Rowl.Collection.axiomUses body ∧
    (edge.2.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ Rowl.Collection.axiomUses body := by
  cases body with
  | SubObjectPropertyOf sub sup =>
    cases sub with
    | Single sub =>
      apply directed_typed _ (expressionKey sub) (expressionKey sup) _ _ edge member
      · simp [Rowl.Collection.axiomUses,Rowl.Collection.subObjectUses,object_uses]
      · simp [Rowl.Collection.axiomUses,Rowl.Collection.subObjectUses,object_uses]
    | Chain chain => simp [AxiomEdges] at member
  | EquivalentObjectProperties values =>
    exact pairs_typed _ (PropertyKeys values) (property_keys_typed values) edge member
  | InverseObjectProperties sub sup =>
    apply equivalent_typed _ (expressionKey sub) (inverse (expressionKey sup)) _ _ edge member
    · simp [Rowl.Collection.axiomUses,object_uses]
    · simp [Rowl.Collection.axiomUses,object_uses,inverse]
  | SymmetricObjectProperty property =>
    apply directed_typed _ (expressionKey property) (inverse (expressionKey property)) _ _ edge member
    · simp [Rowl.Collection.axiomUses,object_uses]
    · simp [Rowl.Collection.axiomUses,object_uses,inverse]
  | _ => simp [AxiomEdges] at member

private theorem axiom_seeds_typed (body : Axiom) (role : Key) (member : role ∈ AxiomSeeds body) :
    (role.1,RowlRust.typing.EntityKind.ObjectProperty) ∈ Rowl.Collection.axiomUses body := by
  cases body with
  | SubObjectPropertyOf sub sup =>
    cases sub with
    | Single sub => simp [AxiomSeeds] at member
    | Chain chain =>
      simp only [AxiomSeeds,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at member
      rcases member with rfl | rfl <;> simp [Rowl.Collection.axiomUses,object_uses,inverse]
  | TransitiveObjectProperty property =>
    simp only [AxiomSeeds,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl <;> simp [Rowl.Collection.axiomUses,object_uses,inverse]
  | _ => simp [AxiomSeeds] at member

private theorem builtin_seeds_nodes (rows : List Rowl.Collection.Row) (role : Key)
    (member : role ∈ BuiltinSeeds rows) : role ∈ Nodes rows := by
  obtain ⟨row,rowMember,seedMember⟩ := List.mem_flatMap.mp member
  by_cases required : row.2 = RowlRust.typing.EntityKind.ObjectProperty ∧ BuiltinComposite row.1
  · have same : role = (row.1,false) := by simpa [required] using seedMember
    subst role
    apply (nodes_iff rows _).mpr
    have equal : (row.1,RowlRust.typing.EntityKind.ObjectProperty) = row := Prod.ext rfl required.1.symm
    rw [equal]
    exact rowMember
  · simp [required] at seedMember

private theorem closure_roots_nodes (items : List AnnotatedAxiom) (role : Key)
    (member : Composite items role) : role ∈ AllNodes items := by
  obtain ⟨item,itemMember,seedMember⟩ := List.mem_flatMap.mp member
  apply List.mem_flatMap.mpr
  refine ⟨item,itemMember,?_⟩
  rcases List.mem_append.mp seedMember with builtin | explicit
  · exact builtin_seeds_nodes _ role builtin
  · apply (nodes_iff _ role).mpr
    exact List.mem_append_right _ (axiom_seeds_typed item.axiom role explicit)

theorem hierarchy_target_nodes (items : List AnnotatedAxiom) (sub sup : Key)
    (edge : Hierarchy items sub sup) : sup ∈ AllNodes items := by
  obtain ⟨item,itemMember,edgeMember⟩ := edge
  have typed := (axiom_edges_typed item.axiom (sub,sup) edgeMember).2
  exact List.mem_flatMap.mpr ⟨item,itemMember,(nodes_iff _ sup).mpr (List.mem_append_right _ typed)⟩

private theorem raw_reached_nodes (items : List AnnotatedAxiom) (role : Key)
    (root : Key) (composite : Composite items root) (path : Reachable items root role) :
    role ∈ AllNodes items := by
  induction path with
  | refl => exact closure_roots_nodes items root composite
  | @tail sub sup path edge ih => exact hierarchy_target_nodes items sub sup edge

private theorem reach_raw_iff (items : List AnnotatedAxiom) (facts : RoleFacts)
    (correct : ClosureCorrect items facts) (role : Key) :
    Reach (edgeKeys facts.edges) (roleKeys facts.composite) role ↔
      ∃ root, Composite items root ∧ Reachable items root role := by
  have edgesEq : (fun sub sup => (sub,sup) ∈ edgeKeys facts.edges) = Hierarchy items := by
    funext sub sup
    apply propext
    rw [correct.2.1]
    simp [Hierarchy,List.mem_flatMap]
  unfold Reach
  rw [edgesEq,correct.2.2.1]
  rfl

private theorem facts_closure_correct (items : List AnnotatedAxiom) (facts : RoleFacts)
    (factsCorrect : ClosureCorrect items facts) :
    ∃ output, non_simple_closure facts.nodes facts.composite facts.edges = .ok (.Complete output) ∧
      (roleKeys output).Nodup ∧ ∀ role, role ∈ roleKeys output ↔ ¬ Simple items role := by
  have present : ∀ role, Reach (edgeKeys facts.edges) (roleKeys facts.composite) role → role ∈ roleKeys facts.nodes := by
    intro role reached
    obtain ⟨root,composite,path⟩ := (reach_raw_iff items facts factsCorrect role).mp reached
    rw [factsCorrect.1]
    exact raw_reached_nodes items role root composite path
  obtain ⟨output,executed⟩ := (non_simple_closure_complete_iff facts.nodes facts.composite facts.edges).mpr present
  obtain ⟨actual,run,correct⟩ := non_simple_closure_total_correct facts.nodes facts.composite facts.edges
  have equal := Result.ok_injective (run.symm.trans executed)
  rw [equal] at correct
  refine ⟨output,executed,correct.1,?_⟩
  intro role
  rw [correct.2.2 role,reach_raw_iff items facts factsCorrect role]
  simp only [Simple,not_forall,Classical.not_imp,not_not]
  constructor
  · rintro ⟨root,composite,path⟩; exact ⟨root,path,composite⟩
  · rintro ⟨root,path,composite⟩; exact ⟨root,composite,path⟩

/-- The actual raw syntax supplies every reached node; the malformed-universe
    outcome of the generic worklist is impossible for this entry point. Exact
    non-simple membership follows the independently stated OWL hierarchy. -/
theorem classify_non_simple_total_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ output, classify_non_simple items = .ok (.Complete output) ∧
      (roleKeys output).Nodup ∧ ∀ role, role ∈ roleKeys output ↔ ¬ Simple items.val role := by
  obtain ⟨facts,collected,factsCorrect⟩ := collect_facts_total_correct items
  obtain ⟨output,executed,distinct,membership⟩ := facts_closure_correct items.val facts factsCorrect
  exact ⟨output,by simp [classify_non_simple,collected,executed],distinct,membership⟩

private def RequiredCorrect (required nonSimple : List Key) : SimplicityCheck → Prop
  | .Allowed => ∀ role ∈ required, role ∉ nonSimple
  | .ForbiddenRole role => ∃ before after, required = before ++ key role :: after ∧
      (∀ prior ∈ before, prior ∉ nonSimple) ∧ key role ∈ nonSimple
  | .MissingNode _ => False

/-- Only the simple-role restriction, with exact first offending occurrence.
    The generic worklist's missing-node outcome is excluded for actual raw ASTs. -/
def SimplicityCorrect (items : List AnnotatedAxiom) : SimplicityCheck → Prop
  | .Allowed => SimpleRestriction items
  | .ForbiddenRole role => ∃ before after,
      items.flatMap (fun item => AxiomRequired item.axiom) = before ++ key role :: after ∧
      (∀ prior ∈ before, Simple items prior) ∧ ¬ Simple items (key role)
  | .MissingNode _ => False

private theorem check_required_total (required nonSimple : Roles) :
    ∃ output, check_required required nonSimple = .ok output ∧
      RequiredCorrect (roleKeys required) (roleKeys nonSimple) output := by
  induction required with
  | Empty => exact ⟨.Allowed,by simp [check_required],by simp [RequiredCorrect,roleKeys]⟩
  | Entry role next ih =>
    have contains := contains_total nonSimple role
    by_cases found : key role ∈ roleKeys nonSimple
    · refine ⟨.ForbiddenRole role,by simp [check_required,contains,found],[],roleKeys next,?_,?_,found⟩
      · simp [roleKeys]
      · simp
    · obtain ⟨output,executed,correct⟩ := ih
      refine ⟨output,by simp [check_required,contains,found,executed],?_⟩
      cases output with
      | Allowed =>
        intro candidate member
        rcases List.mem_cons.mp member with member | member
        · exact member ▸ found
        · exact correct candidate member
      | ForbiddenRole forbidden =>
        obtain ⟨before,after,order,prior,same⟩ := correct
        refine ⟨key role :: before,after,?_,?_,same⟩
        · simp [roleKeys,order]
        · intro candidate member
          rcases List.mem_cons.mp member with member | member
          · exact member ▸ found
          · exact prior candidate member
      | MissingNode missing => exact False.elim correct

/-- The executable whole-closure checker terminates and accepts exactly the
    simple-role restriction, or identifies its first non-simple required role. -/
theorem check_simplicity_total_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ output, check_simplicity items = .ok output ∧ SimplicityCorrect items.val output := by
  obtain ⟨facts,collected,factsCorrect⟩ := collect_facts_total_correct items
  obtain ⟨nonSimple,classified,distinct,membership⟩ := facts_closure_correct items.val facts factsCorrect
  obtain ⟨output,checked,correct⟩ := check_required_total facts.simple_required nonSimple
  refine ⟨output,by simp [check_simplicity,collected,classified,checked],?_⟩
  rw [factsCorrect.2.2.2.1] at correct
  have simple (role : Key) : role ∉ roleKeys nonSimple ↔ Simple items.val role := by
    rw [membership role,not_not]
  cases output with
  | Allowed => exact fun role required => (simple role).mp (correct role required)
  | ForbiddenRole role =>
    obtain ⟨before,after,order,prior,nonSimple⟩ := correct
    exact ⟨before,after,order,fun role member => (simple role).mp (prior role member),(membership _).mp nonSimple⟩
  | MissingNode role => exact False.elim correct

theorem check_simplicity_allowed_iff (items : alloc.vec.Vec AnnotatedAxiom) :
    check_simplicity items = .ok .Allowed ↔ SimpleRestriction items.val := by
  obtain ⟨output,executed,correct⟩ := check_simplicity_total_correct items
  constructor
  · intro allowed
    have equal := Result.ok_injective (executed.symm.trans allowed)
    simpa [equal,SimplicityCorrect] using correct
  · intro allowed
    cases output with
    | Allowed => exact executed
    | ForbiddenRole role =>
      obtain ⟨before,after,order,prior,nonSimple⟩ := correct
      have required : key role ∈ items.val.flatMap (fun item => AxiomRequired item.axiom) := by
        rw [order]; simp
      exact False.elim (nonSimple (allowed (key role) required))
    | MissingNode role => exact False.elim correct

end Rowl.RoleClosure

