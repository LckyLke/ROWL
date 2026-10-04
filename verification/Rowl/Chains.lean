import Rowl.ChainModel

/-!
The actual entry point `role_chains.satisfiable`: satisfiability as the
completion forest decides it, with role chains as further role axioms. With no
chains it is the forest; otherwise the chains with their mirrors, the checks,
the encoding and the definitions of the atoms are composed with the forest's
own correctness theorem, and the two model constructions of `ChainModel` carry
models across in both directions.
-/
namespace Rowl.Chains
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation)
open Rowl.Concepts (denote inv inv_inv)
open Rowl.Hierarchy (Below Closed Respects Constrained)
open Rowl.ChainSemantics
open Rowl.ChainOps
open Rowl.ChainModel
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
universe u v

private theorem forall2_left {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ a ∈ l1, ∃ b ∈ l2, R a b
  | _, _, .nil, _, member => by cases member
  | _, _, .cons head tail, a, member => by
    rcases List.mem_cons.mp member with same | later
    · exact ⟨_,List.mem_cons_self,same ▸ head⟩
    · obtain ⟨b,inside,rel⟩ := forall2_left tail a later
      exact ⟨b,List.mem_cons_of_mem _ inside,rel⟩

private theorem forall2_right {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ b ∈ l2, ∃ a ∈ l1, R a b
  | _, _, .nil, _, member => by cases member
  | _, _, .cons head tail, b, member => by
    rcases List.mem_cons.mp member with same | later
    · exact ⟨_,List.mem_cons_self,same ▸ head⟩
    · obtain ⟨a,inside,rel⟩ := forall2_right tail b later
      exact ⟨a,List.mem_cons_of_mem _ inside,rel⟩

private theorem forall2_eq {α : Type} : ∀ {l1 l2 : List α}, List.Forall₂ (fun a b => b = a) l1 l2 → l2 = l1
  | _, _, .nil => rfl
  | _, _, .cons head tail => by rw [head,forall2_eq tail]

/-- The chains followed by their mirrors: every chain is there, every chain of
    the list is one of them or the mirror of one, and every one has its
    mirror. -/
def Closes (chs all : List role_chains.Chain) : Prop :=
  (∀ ch ∈ chs, ch ∈ all) ∧
  (∀ ch ∈ all, ch ∈ chs ∨ ∃ ch0 ∈ chs, ch.roles.val = (ch0.roles.val.map inv).reverse ∧ ch.sup = inv ch0.sup) ∧
  (∀ ch0 ∈ chs, ∃ ch ∈ all, ch.roles.val = (ch0.roles.val.map inv).reverse ∧ ch.sup = inv ch0.sup)

private theorem reverse_mirror (w : List ObjectPropertyExpression) :
    (((w.map inv).reverse).map inv).reverse = w := by
  rw [List.map_reverse,List.reverse_reverse,List.map_map]
  have : inv ∘ inv = id := funext inv_inv
  rw [this,List.map_id]

theorem closes_mirrored {chs all : List role_chains.Chain} (closes : Closes chs all) : Mirrored all := by
  intro ch member
  rcases closes.2.1 ch member with original | ⟨ch0,member0,roles,sup⟩
  · exact closes.2.2 ch original
  · refine ⟨ch0,closes.1 ch0 member0,?_,?_⟩
    · rw [roles,reverse_mirror]
    · rw [sup,inv_inv]

theorem closes_chained {chs all : List role_chains.Chain} (closes : Closes chs all)
    {Object : Type u} {Value : Type v} (I : Interpretation Object Value) :
    Chained I chs ↔ Chained I all := by
  constructor
  · intro chained ch member
    rcases closes.2.1 ch member with original | ⟨ch0,member0,roles,sup⟩
    · exact chained ch original
    · intro x y along
      rw [sup]
      rw [roles] at along
      exact chained_mirror I ch0 (chained ch0 member0) x y along
  · intro chained ch member
    exact chained ch (closes.1 ch member)

theorem closes_long {chs all : List role_chains.Chain} (closes : Closes chs all)
    (long : ∀ ch ∈ chs, 2 ≤ ch.roles.val.length) : ∀ ch ∈ all, 2 ≤ ch.roles.val.length := by
  intro ch member
  rcases closes.2.1 ch member with original | ⟨ch0,member0,roles,_⟩
  · exact long ch original
  · rw [roles,List.length_reverse,List.length_map]; exact long ch0 member0

/-- The actual chains with their mirrors. -/
theorem closes_of_copies (chs copies all : alloc.vec.Vec role_chains.Chain)
    (run0 : role_chains.copy_chains chs false 0#usize (alloc.vec.Vec.new role_chains.Chain) = .ok (some copies))
    (run1 : role_chains.copy_chains chs true 0#usize copies = .ok (some all)) : Closes chs.val all.val := by
  obtain ⟨o0,run0',spec0⟩ := copy_chains_correct chs false 0#usize (alloc.vec.Vec.new role_chains.Chain)
  rw [run0] at run0'
  obtain ⟨added0,copiesIs,pairs0⟩ := spec0 copies (Result.ok_injective run0').symm
  have copiesEq : copies.val = chs.val := by
    rw [copiesIs,new_val,List.nil_append]
    simp only [Bool.false_eq_true,↓reduceIte,zero_val,List.drop_zero] at pairs0
    exact forall2_eq pairs0
  obtain ⟨o1,run1',spec1⟩ := copy_chains_correct chs true 0#usize copies
  rw [run1] at run1'
  obtain ⟨added1,allIs,pairs1⟩ := spec1 all (Result.ok_injective run1').symm
  simp only [↓reduceIte,zero_val,List.drop_zero] at pairs1
  rw [copiesEq] at allIs
  refine ⟨?_,?_,?_⟩
  · intro ch member; rw [allIs]; exact List.mem_append_left _ member
  · intro ch member
    rw [allIs] at member
    rcases List.mem_append.mp member with original | mirrored
    · exact .inl original
    · obtain ⟨ch0,member0,roles,sup⟩ := forall2_right pairs1 ch mirrored
      exact .inr ⟨ch0,member0,roles,sup⟩
  · intro ch0 member0
    obtain ⟨ch,member,roles,sup⟩ := forall2_left pairs1 ch0 member0
    exact ⟨ch,by rw [allIs]; exact List.mem_append_right _ member,roles,sup⟩


theorem long_from_zero (chains : alloc.vec.Vec role_chains.Chain) :
    role_chains.long_from chains 0#usize = .ok (decide (∀ ch ∈ chains.val, 2 ≤ ch.roles.val.length)) := by
  rw [long_from_correct]
  congr 1

theorem pairs_fit_zero (h : hierarchy.RoleHierarchy) (chains : alloc.vec.Vec role_chains.Chain) :
    role_chains.pairs_fit h chains 0#usize = .ok (decide (∀ d ∈ h.disjoint.val,
      ¬ Complex h chains.val d.left ∧ ¬ Complex h chains.val d.right)) := by
  rw [pairs_fit_correct]
  congr 1

theorem facts_fit_zero (h : hierarchy.RoleHierarchy) (chains : alloc.vec.Vec role_chains.Chain)
    (facts : alloc.vec.Vec completion.Fact) :
    role_chains.facts_fit h chains facts 0#usize = .ok (decide (∀ f ∈ facts.val, Fits h chains.val f.concept)) := by
  rw [facts_fit_correct]
  congr 1

theorem definitions_fit_zero (h : hierarchy.RoleHierarchy) (chains : alloc.vec.Vec role_chains.Chain)
    (definitions : alloc.vec.Vec completion.Definition) :
    role_chains.definitions_fit h chains definitions 0#usize =
      .ok (decide (∀ d ∈ definitions.val, ¬ Spaced d.class ∧ Fits h chains.val d.concept)) := by
  rw [definitions_fit_correct]
  congr 1

/-- The empty tables are in order. -/
theorem tableOk_empty : TableOk (alloc.vec.Vec.new role_chains.Atom).val (alloc.vec.Vec.new concepts.Concept).val :=
  ⟨by simp [new_val],by intro k a at_k; simp [new_val] at at_k⟩

/-- Satisfiability with role chains. The answer is the forest's when there are
    no chains; otherwise it needs chains of at least two roles, disjoint pairs,
    number restrictions and self restrictions on roles that no chain reaches,
    and classes that start with no space. An acceptance comes with a model of
    the role hierarchy, the chains and the disjoint pairs where the TBox
    concept and every definition hold everywhere and every fact and link holds
    at the elements of its nodes, and a rejection rules out every such model,
    in any universes. -/
theorem satisfiable_correct (count : Usize) (query facts : alloc.vec.Vec completion.Fact)
    (links : alloc.vec.Vec completion.Link) (axioms : concepts.Concept)
    (definitions : alloc.vec.Vec completion.Definition) (h : hierarchy.RoleHierarchy) (closed : Closed h)
    (chs : alloc.vec.Vec role_chains.Chain) (positive : 0 < count.val)
    (factsIn : ∀ f ∈ query.val ++ facts.val, f.node.val < count.val)
    (linksIn : ∀ l ∈ links.val, l.from.val < count.val ∧ l.to.val < count.val) :
    ∃ r, role_chains.satisfiable count query facts links axioms definitions h chs = .ok r ∧
      (r = some true → ∃ (Object : Type) (I : Interpretation Object Unit) (π : Nat → Object),
        Respects I h ∧ Chained I chs.val ∧ Constrained I h ∧ (∀ y, denote I axioms y) ∧
        (∀ d ∈ definitions.val, ∀ y, I.classes d.class y → denote I d.concept y) ∧
        (∀ f ∈ query.val ++ facts.val, denote I f.concept (π f.node.val)) ∧
        (∀ l ∈ links.val, objectRelation I l.role (π l.from.val) (π l.to.val))) ∧
      (r = some false → ¬ ∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
        Respects I h ∧ Chained I chs.val ∧ Constrained I h ∧ (∀ y, denote I axioms y) ∧
        (∀ d ∈ definitions.val, ∀ y, I.classes d.class y → denote I d.concept y) ∧
        (∀ f ∈ query.val ++ facts.val, denote I f.concept (π f.node.val)) ∧
        (∀ l ∈ links.val, objectRelation I l.role (π l.from.val) (π l.to.val))) := by
  rw [role_chains.satisfiable]
  by_cases empty : chs.val.length = 0
  · have len0 : alloc.vec.Vec.len chs = 0#usize := UScalar.eq_of_val_eq (by simp [empty])
    obtain ⟨r,run,accepted,rejected⟩ := Rowl.ForestModel.satisfiable_correct.{u,v} count query facts links axioms
      definitions h closed positive factsIn linksIn
    have noChains : chs.val = [] := List.eq_nil_of_length_eq_zero empty
    refine ⟨r,by simp only [len0,↓reduceIte]; exact run,?_,?_⟩
    · intro yes
      obtain ⟨Object,I,π,resp,cons,ax,defs,fs,ls⟩ := accepted yes
      exact ⟨Object,I,π,resp,(by intro ch member; rw [noChains] at member; cases member),cons,ax,defs,fs,ls⟩
    · rintro no ⟨Object,Value,I,π,resp,_,cons,ax,defs,fs,ls⟩
      exact rejected no ⟨Object,Value,I,π,resp,cons,ax,defs,fs,ls⟩
  have len0 : ¬ alloc.vec.Vec.len chs = 0#usize := fun same => empty (by simpa using congrArg UScalar.val same)
  rw [if_neg len0,long_from_zero,bind_ok]
  by_cases long : ∀ ch ∈ chs.val, 2 ≤ ch.roles.val.length
  swap
  · exact ⟨none,by simp only [long,decide_false,Bool.false_eq_true,↓reduceIte],by simp,by simp⟩
  simp only [decide_eq_true long,↓reduceIte]
  obtain ⟨o0,run0,_⟩ := copy_chains_correct chs false 0#usize (alloc.vec.Vec.new role_chains.Chain)
  cases o0 with
  | none => exact ⟨none,by rw [run0,bind_ok],by simp,by simp⟩
  | some copies =>
  simp only [run0,bind_ok]
  obtain ⟨o1,run1,_⟩ := copy_chains_correct chs true 0#usize copies
  cases o1 with
  | none => exact ⟨none,by rw [run1,bind_ok],by simp,by simp⟩
  | some all =>
  simp only [run1,bind_ok]
  have closes := closes_of_copies chs copies all run0 run1
  have mirrored := closes_mirrored closes
  have longAll := closes_long closes long
  have few : all.val.length ≤ Usize.max := all.property
  rw [pairs_fit_zero,bind_ok]
  by_cases pairsOk : ∀ d ∈ h.disjoint.val, ¬ Complex h all.val d.left ∧ ¬ Complex h all.val d.right
  swap
  · exact ⟨none,by simp only [pairsOk,decide_false,Bool.false_eq_true,↓reduceIte],by simp,by simp⟩
  simp only [decide_eq_true pairsOk,↓reduceIte]
  rw [fits_correct,bind_ok]
  by_cases fitsAx : Fits h all.val axioms
  swap
  · exact ⟨none,by simp only [fitsAx,decide_false,Bool.false_eq_true,↓reduceIte],by simp,by simp⟩
  simp only [decide_eq_true fitsAx,↓reduceIte]
  rw [facts_fit_zero,bind_ok]
  by_cases fitsQ : ∀ f ∈ query.val, Fits h all.val f.concept
  swap
  · exact ⟨none,by simp only [fitsQ,decide_false,Bool.false_eq_true,↓reduceIte],by simp,by simp⟩
  simp only [decide_eq_true fitsQ,↓reduceIte]
  rw [facts_fit_zero,bind_ok]
  by_cases fitsF : ∀ f ∈ facts.val, Fits h all.val f.concept
  swap
  · exact ⟨none,by simp only [fitsF,decide_false,Bool.false_eq_true,↓reduceIte],by simp,by simp⟩
  simp only [decide_eq_true fitsF,↓reduceIte]
  rw [definitions_fit_zero,bind_ok]
  by_cases fitsD : ∀ d ∈ definitions.val, ¬ Spaced d.class ∧ Fits h all.val d.concept
  swap
  · exact ⟨none,by simp only [fitsD,decide_false,Bool.false_eq_true,↓reduceIte],by simp,by simp⟩
  simp only [decide_eq_true fitsD,↓reduceIte]
  obtain ⟨o2,run2,spec2⟩ := encode_correct h all axioms fitsAx true _ _ tableOk_empty
  cases o2 with
  | none => exact ⟨none,by rw [run2,bind_ok],by simp,by simp⟩
  | some triple =>
  obtain ⟨atoms0,bases0,axioms1⟩ := triple
  obtain ⟨_,_,ok0,encAx,_⟩ := spec2 _ _ _ rfl
  simp only [run2,bind_ok]
  obtain ⟨o3,run3,spec3⟩ := encode_facts_correct h all query 0#usize atoms0 bases0
    (alloc.vec.Vec.new completion.Fact) ok0 (by simpa [zero_val] using fitsQ)
  show ∃ r, (Std.bind (role_chains.encode_facts h all query 0#usize atoms0 bases0
    (alloc.vec.Vec.new completion.Fact)) _) = Result.ok r ∧ _
  cases o3 with
  | none => exact ⟨none,by rw [run3,bind_ok],by simp,by simp⟩
  | some triple =>
  obtain ⟨atoms1,bases1,query1⟩ := triple
  obtain ⟨pa1,pb1,ok1,encQ,query1Is,pairsQ⟩ := spec3 _ _ _ rfl
  simp only [run3,bind_ok]
  obtain ⟨o4,run4,spec4⟩ := encode_facts_correct h all facts 0#usize atoms1 bases1
    (alloc.vec.Vec.new completion.Fact) ok1 (by simpa [zero_val] using fitsF)
  show ∃ r, (Std.bind (role_chains.encode_facts h all facts 0#usize atoms1 bases1
    (alloc.vec.Vec.new completion.Fact)) _) = Result.ok r ∧ _
  cases o4 with
  | none => exact ⟨none,by rw [run4,bind_ok],by simp,by simp⟩
  | some triple =>
  obtain ⟨atoms2,bases2,facts1⟩ := triple
  obtain ⟨pa2,pb2,ok2,encF,facts1Is,pairsF⟩ := spec4 _ _ _ rfl
  simp only [run4,bind_ok]
  obtain ⟨o5,run5,spec5⟩ := encode_definitions_correct h all definitions 0#usize atoms2 bases2
    (alloc.vec.Vec.new completion.Definition) ok2 (by
      intro d member; simp only [zero_val,List.drop_zero] at member; exact (fitsD d member).2)
  show ∃ r, (Std.bind (role_chains.encode_definitions h all definitions 0#usize atoms2 bases2
    (alloc.vec.Vec.new completion.Definition)) _) = Result.ok r ∧ _
  cases o5 with
  | none => exact ⟨none,by rw [run5,bind_ok],by simp,by simp⟩
  | some triple =>
  obtain ⟨atoms3,bases3,definitions1⟩ := triple
  obtain ⟨pa3,pb3,ok3,encD,definitions1Is,pairsD⟩ := spec5 _ _ _ rfl
  simp only [run5,bind_ok]
  obtain ⟨o6,run6,spec6⟩ := generate_correct.{u,v} h all bases3 atoms3 0#usize definitions1 ok3 (by simp)
  obtain ⟨o6',run6',spec6'⟩ := generate_correct.{0,0} h all bases3 atoms3 0#usize definitions1 ok3 (by simp)
  have same6 : o6' = o6 := Result.ok_injective (run6'.symm.trans run6)
  subst same6
  show ∃ r, (Std.bind (role_chains.generate h all bases3 atoms3 0#usize definitions1) _) = Result.ok r ∧ _
  cases o6' with
  | none => exact ⟨none,by rw [run6,bind_ok],by simp,by simp⟩
  | some pair =>
  obtain ⟨T,defsOut⟩ := pair
  obtain ⟨pa4,ok4,defs,defsIs,soundDefs,completeDefs⟩ := spec6 _ _ rfl
  obtain ⟨_,_,defs',defsIs',soundDefs',completeDefs'⟩ := spec6' _ _ rfl
  have sameDefs : defs' = defs := by
    rw [defsIs] at defsIs'
    exact (List.append_cancel_left defsIs').symm
  subst sameDefs
  simp only [run6,bind_ok]
  show ∃ r, forest.satisfiable count query1 facts1 links axioms1 defsOut h = Result.ok r ∧ _
  -- The encodings, read with the final tables.
  have pT : atoms0.val <+: T.val := pa1.trans (pa2.trans (pa3.trans pa4))
  have pB : bases0.val <+: bases3.val := pb1.trans (pb2.trans pb3)
  have encAx' := enc_mono pT pB encAx
  rw [new_val,List.nil_append] at query1Is facts1Is definitions1Is
  simp only [zero_val,List.drop_zero] at pairsQ pairsF pairsD
  have pairsQ' : List.Forall₂ (fun (f e : completion.Fact) => e.node = f.node ∧
      Enc h all.val T.val bases3.val true f.concept e.concept) query.val query1.val := by
    rw [query1Is]
    exact pairsQ.imp (fun f e ⟨node,enc⟩ => ⟨node,enc_mono (pa2.trans (pa3.trans pa4)) (pb2.trans pb3) enc⟩)
  have pairsF' : List.Forall₂ (fun (f e : completion.Fact) => e.node = f.node ∧
      Enc h all.val T.val bases3.val true f.concept e.concept) facts.val facts1.val := by
    rw [facts1Is]
    exact pairsF.imp (fun f e ⟨node,enc⟩ => ⟨node,enc_mono (pa3.trans pa4) pb3 enc⟩)
  have pairsD' : List.Forall₂ (fun (d e : completion.Definition) => e.class = d.class ∧
      Enc h all.val T.val bases3.val true d.concept e.concept) definitions.val definitions1.val := by
    rw [definitions1Is]
    exact pairsD.imp (fun d e ⟨cls,enc⟩ => ⟨cls,enc_mono pa4 (List.prefix_refl _) enc⟩)
  have pairsAll : List.Forall₂ (fun (f e : completion.Fact) => e.node = f.node ∧
      Enc h all.val T.val bases3.val true f.concept e.concept) (query.val ++ facts.val) (query1.val ++ facts1.val) :=
    List.rel_append pairsQ' pairsF'
  have fitsAll : ∀ f ∈ query.val ++ facts.val, Fits h all.val f.concept := by
    intro f member
    rcases List.mem_append.mp member with q | f'
    · exact fitsQ f q
    · exact fitsF f f'
  have factsIn' : ∀ e ∈ query1.val ++ facts1.val, e.node.val < count.val := by
    intro e member
    obtain ⟨f,fMember,node,_⟩ := forall2_right pairsAll e member
    rw [node]; exact factsIn f fMember
  obtain ⟨r,run,accepted,rejected⟩ := Rowl.ForestModel.satisfiable_correct.{u,v} count query1 facts1 links axioms1
    defsOut h closed positive factsIn' linksIn
  refine ⟨r,run,?_,?_⟩
  · -- A model of the encoding, closed under the role axioms.
    intro yes
    obtain ⟨Object,J,π,respJ,consJ,axJ,defsJ,factsJ,linksJ⟩ := accepted yes
    have atoms : ∀ (k : Usize) (a : role_chains.Atom), T.val[k.val]? = some a →
        ∃ D, Defines.{0,0} h all.val bases3.val T.val a D ∧ ∀ y, J.classes (nameOf k) y → denote J D y := by
      intro k a at_k
      obtain ⟨d,member,cls,defines⟩ := completeDefs' k a (by simp) at_k
      refine ⟨d.concept,defines,fun y holds => defsJ d (by rw [defsIs]; exact List.mem_append_right _ member) y
        (by rw [cls]; exact holds)⟩
    obtain ⟨respI,chainedI,consI,encI,classesI,individualsI,relationsI⟩ :=
      accept_model closed mirrored longAll few closes.1 pairsOk ok4 atoms respJ consJ
    refine ⟨Object,closureModel J h all.val,π,respI,chainedI,consI,?_,?_,?_,?_⟩
    · intro y; exact encI encAx' fitsAx y (axJ y)
    · intro d member y holds
      obtain ⟨e,eMember,cls,enc⟩ := forall2_left pairsD' d member
      rw [classesI] at holds
      exact encI enc (fitsD d member).2 y (defsJ e (by rw [defsIs]; exact List.mem_append_left _ eMember) y
        (by rw [cls]; exact holds))
    · intro f member
      obtain ⟨e,eMember,node,enc⟩ := forall2_left pairsAll f member
      have holds := factsJ e eMember
      rw [node] at holds
      exact encI enc (fitsAll f member) _ holds
    · intro l member
      exact relationsI l.role _ _ (linksJ l member)
  · -- A model of the chains with its atoms is a model of the encoding.
    rintro no ⟨Object,Value,I,π,respI,chainedI,consI,axI,defsI,factsI,linksI⟩
    have chainedAll := (closes_chained closes I).mp chainedI
    obtain ⟨respJ,consJ,encJ,atomsJ,plainJ,_,relationsJ⟩ :=
      reject_model (T := T.val) (B := bases3.val) respI chainedAll consI ok4
    apply rejected no
    refine ⟨Object,Value,withAtoms I h all.val T.val bases3.val T.val.length,π,respJ,consJ,?_,?_,?_,?_⟩
    · intro y; exact (encJ encAx' fitsAx y).mpr (axI y)
    · intro e member y holds
      rw [defsIs] at member
      rcases List.mem_append.mp member with original | atom
      · obtain ⟨d,dMember,cls,enc⟩ := forall2_right pairsD' e original
        rw [cls,plainJ _ (fitsD d dMember).1] at holds
        exact (encJ enc (fitsD d dMember).2 y).mpr (defsI d dMember y holds)
      · obtain ⟨k,a,_,at_k,cls,defines⟩ := soundDefs e atom
        rw [cls] at holds
        exact atomsJ at_k defines y holds
    · intro e member
      obtain ⟨f,fMember,node,enc⟩ := forall2_right pairsAll e member
      rw [node]
      exact (encJ enc (fitsAll f fMember) _).mpr (factsI f fMember)
    · intro l member
      rw [relationsJ]
      exact linksI l member

end Rowl.Chains
