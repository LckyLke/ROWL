import Rowl.ChainOps
import Rowl.ForestModel

/-!
The models of the encoding of role chains. A model of the role axioms and the
chains becomes a model of the encoding once every atom holds where every path
that its automaton reads leads into its filler (`withAtoms`, `enc_sound`).
Conversely, a model of the encoding, which the completion forest builds, becomes
a model of the role axioms and the chains once every role relates the pairs
that the role axioms derive from its relations (`closureModel`, `enc_complete`):
the atoms carry their fillers along every derived pair.
-/
namespace Rowl.ChainModel
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation AtLeast AtMost)
open Rowl.Concepts (denote inv inv_inv relation_inv negate_correct atLeast_congr)
open Rowl.Hierarchy (Below Closed Respects Constrained inclusionList transitives below_refl respects_below)
open Rowl.ChainSemantics
open Rowl.ChainOps
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
universe u v

section
variable {Object : Type u} {Value : Type v}

theorem atLeast_mono {n : Nat} {P Q : Object → Prop} (sub : ∀ y, P y → Q y) (many : AtLeast n P) :
    AtLeast n Q := by
  obtain ⟨f,inj,holds⟩ := many
  exact ⟨f,inj,fun i => sub _ (holds i)⟩

theorem atMost_anti {n : Nat} {P Q : Object → Prop} (sub : ∀ y, P y → Q y) (few : AtMost n Q) : AtMost n P :=
  fun many => few (atLeast_mono sub many)

/-- Two interpretations that differ at most in their classes. -/
def SameBut (I J : Interpretation Object Value) : Prop :=
  I.objectProperties = J.objectProperties ∧ I.namedIndividuals = J.namedIndividuals ∧
    I.anonymousIndividuals = J.anonymousIndividuals

theorem sameBut_relation {I J : Interpretation Object Value} (same : SameBut I J) (r : ObjectPropertyExpression) :
    objectRelation I r = objectRelation J r := by
  cases r <;> simp [objectRelation,same.1]

theorem sameBut_individual {I J : Interpretation Object Value} (same : SameBut I J) (a : Individual) :
    Rowl.Owl.individual I a = Rowl.Owl.individual J a := by
  cases a <;> simp [Rowl.Owl.individual,same.2.1,same.2.2]

/-- A concept means the same in interpretations that differ only in classes it
    does not mention. -/
theorem denote_frame {I J : Interpretation Object Value} (same : SameBut I J) :
    ∀ (D : concepts.Concept), (∀ cl, Mentions cl D → I.classes cl = J.classes cl) →
      ∀ x, denote I D x ↔ denote J D x := by
  intro D
  induction D with
  | Top => intro _ x; rfl
  | Bottom => intro _ x; rfl
  | Atom cl => intro classes x; simp only [denote,classes cl rfl]
  | NotAtom cl => intro classes x; simp only [denote,classes cl rfl]
  | One a => intro _ x; simp only [denote,sameBut_individual same a]
  | NotOne a => intro _ x; simp only [denote,sameBut_individual same a]
  | HasSelf r => intro _ x; simp only [denote,sameBut_relation same r]
  | NotSelf r => intro _ x; simp only [denote,sameBut_relation same r]
  | And a b iha ihb =>
    intro classes x
    simp only [denote,iha (fun cl m => classes cl (.inl m)) x,ihb (fun cl m => classes cl (.inr m)) x]
  | Or a b iha ihb =>
    intro classes x
    simp only [denote,iha (fun cl m => classes cl (.inl m)) x,ihb (fun cl m => classes cl (.inr m)) x]
  | Exists r f ih =>
    intro classes x
    simp only [denote,sameBut_relation same r]
    exact exists_congr (fun y => and_congr_right (fun _ => ih classes y))
  | Forall r f ih =>
    intro classes x
    simp only [denote,sameBut_relation same r]
    exact forall_congr' (fun y => imp_congr_right (fun _ => ih classes y))
  | AtLeast n r f ih =>
    intro classes x
    simp only [denote,sameBut_relation same r]
    exact atLeast_congr _ (fun y => and_congr_right (fun _ => ih classes y))
  | AtMost n r f ih =>
    intro classes x
    simp only [denote,sameBut_relation same r,AtMost]
    exact not_congr (atLeast_congr _ (fun y => and_congr_right (fun _ => ih classes y)))

/-! ### From a model of the chains to a model of the encoding -/

/-- What a filler means in an interpretation. -/
def fillSem (J : Interpretation Object Value) (B : List concepts.Concept) : role_chains.Filler → Object → Prop
  | .Base b, y => denote J ((B[b.val]?).getD .Top) y
  | .Atom j, y => J.classes (nameOf j) y

theorem fillSem_concept (J : Interpretation Object Value) (B : List concepts.Concept) (F : role_chains.Filler)
    (y : Object) : fillSem J B F y ↔ denote J (fillerConcept B F) y := by
  cases F <;> rfl

/-- `I` where each of the first `n` atoms of `T` holds where every path that
    its automaton reads in `I` leads into its filler. -/
def withAtoms (I : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    (T : List role_chains.Atom) (B : List concepts.Concept) : Nat → Interpretation Object Value
  | 0 => I
  | n+1 =>
    match T[n]? with
    | none => withAtoms I h chs T B n
    | some a =>
      { withAtoms I h chs T B n with
        classes := fun cl y =>
          if ∃ k : Usize, k.val = n ∧ cl = nameOf k then
            ∀ z, Accepts I h chs a.role a.state y z → fillSem (withAtoms I h chs T B n) B a.filler z
          else (withAtoms I h chs T B n).classes cl y }

theorem withAtoms_succ (I : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    (T : List role_chains.Atom) (B : List concepts.Concept) (n : Nat) :
    withAtoms I h chs T B (n+1) =
      match T[n]? with
      | none => withAtoms I h chs T B n
      | some a =>
        { withAtoms I h chs T B n with
          classes := fun cl y =>
            if ∃ k : Usize, k.val = n ∧ cl = nameOf k then
              ∀ z, Accepts I h chs a.role a.state y z → fillSem (withAtoms I h chs T B n) B a.filler z
            else (withAtoms I h chs T B n).classes cl y } := rfl

theorem withAtoms_same (I : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    (T : List role_chains.Atom) (B : List concepts.Concept) : ∀ n, SameBut (withAtoms I h chs T B n) I
  | 0 => ⟨rfl,rfl,rfl⟩
  | n+1 => by
    have previous := withAtoms_same I h chs T B n
    rw [withAtoms_succ]
    split
    · exact previous
    · exact previous

/-- Classes of no atom from `m` to `n` keep their meaning. -/
theorem withAtoms_stable (I : Interpretation Object Value) (h : hierarchy.RoleHierarchy)
    (chs : List role_chains.Chain) (T : List role_chains.Atom) (B : List concepts.Concept) (m : Nat) (cl : model.Class) :
    ∀ n, m ≤ n → (∀ k : Usize, m ≤ k.val → k.val < n → cl ≠ nameOf k) →
      (withAtoms I h chs T B n).classes cl = (withAtoms I h chs T B m).classes cl := by
  intro n
  induction n with
  | zero => intro le _; rw [Nat.le_zero.mp le]
  | succ n ih =>
    intro le other
    rcases Nat.lt_or_eq_of_le le with lt | same
    · have previous := ih (by omega) (fun k low high => other k low (by omega))
      rw [← previous,withAtoms_succ]
      split
      · rfl
      · funext y
        have no : ¬ ∃ k : Usize, k.val = n ∧ cl = nameOf k := by
          rintro ⟨k,kIs,same⟩
          exact other k (by omega) (by omega) same
        simp only [no,↓reduceIte]
    · rw [same]

/-- The meaning of the atom at `k` once it is added. -/
theorem withAtoms_atom (I : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    (T : List role_chains.Atom) (B : List concepts.Concept) {k : Usize} {a : role_chains.Atom}
    (at_k : T[k.val]? = some a) (y : Object) :
    (withAtoms I h chs T B (k.val+1)).classes (nameOf k) y ↔
      ∀ z, Accepts I h chs a.role a.state y z → fillSem (withAtoms I h chs T B k.val) B a.filler z := by
  rw [withAtoms_succ]
  simp only [at_k]
  have yes : ∃ k' : Usize, k'.val = k.val ∧ nameOf k = nameOf k' := ⟨k,rfl,rfl⟩
  simp only [yes,↓reduceIte]

/-- A filler means the same once later atoms are added. -/
theorem fillSem_stable (I : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    (T : List role_chains.Atom) (B : List concepts.Concept) {k n : Nat} (le : k ≤ n) {F : role_chains.Filler}
    (ok : FillerOk B k F) (z : Object) :
    fillSem (withAtoms I h chs T B k) B F z ↔ fillSem (withAtoms I h chs T B n) B F z := by
  have nameStable : ∀ j : Usize, j.val < k →
      (withAtoms I h chs T B n).classes (nameOf j) = (withAtoms I h chs T B k).classes (nameOf j) := by
    intro j lt
    exact withAtoms_stable I h chs T B k (nameOf j) n le (by
      intro k' low _ same
      have := nameOf_injective same
      subst this
      omega)
  cases F with
  | Atom j =>
    simp only [fillSem]
    rw [nameStable j ok]
  | Base b =>
    obtain ⟨D,at_b,classes⟩ := ok
    simp only [fillSem,at_b,Option.getD_some]
    have same : SameBut (withAtoms I h chs T B k) (withAtoms I h chs T B n) := by
      obtain ⟨p1,n1,a1⟩ := withAtoms_same I h chs T B k
      obtain ⟨p2,n2,a2⟩ := withAtoms_same I h chs T B n
      exact ⟨p1.trans p2.symm,n1.trans n2.symm,a1.trans a2.symm⟩
    apply denote_frame same
    intro cl mentions
    rcases classes cl mentions with plain | ⟨j,rfl,lt⟩
    · symm
      exact withAtoms_stable I h chs T B k cl n le (by
        intro k' _ _ same
        exact plain (same ▸ nameOf_spaced k'))
    · exact (nameStable j lt).symm

/-- In `withAtoms` with every atom of an ordered table, an atom holds where
    every path that its automaton reads leads into its filler. -/
theorem atom_meaning (I : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    {T : List role_chains.Atom} {B : List concepts.Concept} (ok : TableOk T B) {k : Usize} {a : role_chains.Atom}
    (at_k : T[k.val]? = some a) (y : Object) :
    (withAtoms I h chs T B T.length).classes (nameOf k) y ↔
      ∀ z, Accepts I h chs a.role a.state y z → fillSem (withAtoms I h chs T B T.length) B a.filler z := by
  have inside : k.val < T.length := (List.getElem?_eq_some_iff.mp at_k).1
  rw [withAtoms_stable I h chs T B (k.val+1) (nameOf k) T.length (by omega) (by
    intro k' low _ same
    have := nameOf_injective same
    subst this
    omega)]
  rw [withAtoms_atom I h chs T B at_k y]
  exact forall_congr' (fun z => imp_congr_right (fun _ =>
    fillSem_stable I h chs T B (by omega) (ok.2 k.val a at_k) z))

/-- Classes that start no space mean in `withAtoms` what they mean in `I`. -/
theorem withAtoms_plain (I : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain)
    (T : List role_chains.Atom) (B : List concepts.Concept) (n : Nat) {cl : model.Class} (plain : ¬ Spaced cl) :
    (withAtoms I h chs T B n).classes cl = I.classes cl :=
  withAtoms_stable I h chs T B 0 cl n (Nat.zero_le n) (by
    intro k _ _ same
    exact plain (same ▸ nameOf_spaced k))


/-- For a model of the role axioms and the chains, every encoding means in
    `withAtoms` with all atoms what the encoded concept means. -/
theorem enc_sound {I : Interpretation Object Value} {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain}
    (respects : Respects I h) (chained : Chained I chs) {T : List role_chains.Atom} {B : List concepts.Concept}
    (ok : TableOk T B) {p : Bool} {D D' : concepts.Concept} (enc : Enc h chs T B p D D') (fits : Fits h chs D) :
    ∀ x, denote (withAtoms I h chs T B T.length) D' x ↔ denote I D x := by
  have same := withAtoms_same I h chs T B T.length
  -- Reading the automaton of a role is reading the role.
  have reads : ∀ (r : ObjectPropertyExpression) (P : Object → Prop) (x : Object),
      (∀ z, Accepts I h chs r .Initial x z → P z) ↔ (∀ z, objectRelation I r x z → P z) := by
    intro r P x
    constructor
    · intro all z rel; exact all z (accepts_of_rel I h chs rel)
    · intro all z acc; exact all z (accepts_initial respects chained acc)
  induction enc with
  | top p => intro x; rfl
  | bottom p => intro x; rfl
  | atom p cl => intro x; simp only [denote,withAtoms_plain I h chs T B _ fits]
  | notAtom p cl => intro x; simp only [denote,withAtoms_plain I h chs T B _ fits]
  | one p a => intro x; simp only [denote,sameBut_individual same a]
  | notOne p a => intro x; simp only [denote,sameBut_individual same a]
  | hasSelf p r => intro x; simp only [denote,sameBut_relation same r]
  | notSelf p r => intro x; simp only [denote,sameBut_relation same r]
  | and _ _ iha ihb => intro x; simp only [denote,iha fits.1 x,ihb fits.2 x]
  | or _ _ iha ihb => intro x; simp only [denote,iha fits.1 x,ihb fits.2 x]
  | @existsPos r e e' _ ih =>
    intro x
    simp only [denote,sameBut_relation same r]
    exact exists_congr (fun y => and_congr_right (fun _ => ih fits y))
  | @existsSimple r e e' _ _ ih =>
    intro x
    simp only [denote,sameBut_relation same r]
    exact exists_congr (fun y => and_congr_right (fun _ => ih fits y))
  | @existsComplex r e e' n k b _ _ neg at_k at_b ih =>
    intro x
    obtain ⟨rn,runN,meansN⟩ := negate_correct.{u,v} e'
    rw [neg] at runN
    have nIs := Result.ok_injective runN
    subst nIs
    simp only [denote]
    rw [atom_meaning I h chs ok at_k x]
    simp only [fillSem,at_b,Option.getD_some]
    rw [reads r _ x]
    simp only [meansN n rfl Object Value (withAtoms I h chs T B T.length),ih fits]
    constructor
    · intro notAll
      by_contra none
      apply notAll
      intro z rel holds
      exact none ⟨z,rel,holds⟩
    · rintro ⟨z,rel,holds⟩ all
      exact all z rel holds
  | @forallComplex r e e' k b _ _ at_k at_b ih =>
    intro x
    simp only [denote]
    rw [atom_meaning I h chs ok at_k x]
    simp only [fillSem,at_b,Option.getD_some]
    rw [reads r _ x]
    exact forall_congr' (fun z => imp_congr_right (fun _ => ih fits z))
  | @forallSimple r e e' _ _ ih =>
    intro x
    simp only [denote,sameBut_relation same r]
    exact forall_congr' (fun y => imp_congr_right (fun _ => ih fits y))
  | @forallNeg r e e' _ ih =>
    intro x
    simp only [denote,sameBut_relation same r]
    exact forall_congr' (fun y => imp_congr_right (fun _ => ih fits y))
  | @atLeast p n r e e' _ ih =>
    intro x
    simp only [denote,sameBut_relation same r]
    exact atLeast_congr _ (fun y => and_congr_right (fun _ => ih fits.2 y))
  | @atMost p n r e e' _ ih =>
    intro x
    simp only [denote,sameBut_relation same r,AtMost]
    exact not_congr (atLeast_congr _ (fun y => and_congr_right (fun _ => ih fits.2 y)))

/-- For a model of the role axioms and the chains, `withAtoms` with all atoms
    satisfies the definition of every atom. -/
theorem atom_defined {I : Interpretation Object Value} {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain}
    (respects : Respects I h) (chained : Chained I chs) {T : List role_chains.Atom} {B : List concepts.Concept}
    (ok : TableOk T B) {k : Usize} {a : role_chains.Atom} (at_k : T[k.val]? = some a) {D : concepts.Concept}
    (defines : Defines.{u,v} h chs B T a D) (y : Object)
    (member : (withAtoms I h chs T B T.length).classes (nameOf k) y) :
    denote (withAtoms I h chs T B T.length) D y := by
  set J := withAtoms I h chs T B T.length with JIs
  have same := withAtoms_same I h chs T B T.length
  have reading := (atom_meaning I h chs ok at_k y).mp member
  rw [defines.2 T (List.prefix_refl _) ok.1 J y]
  refine ⟨?_,?_⟩
  · intro final
    rw [← fillSem_concept]
    exact reading y (by rw [final]; exact .done y)
  · intro l q' trans
    obtain ⟨j,at_j,nested⟩ := defines.1 l q' trans
    refine ⟨j,at_j,?_⟩
    -- The atom of the target holds wherever a step of the transition leads.
    have onward : ∀ z, LabelRel I a.role l y z → J.classes (nameOf j) z := by
      intro z step
      rw [atom_meaning I h chs ok at_j z]
      intro w accepts
      exact reading w (.step trans step accepts)
    cases l with
    | Direct =>
      intro z rel
      exact onward z (by rw [sameBut_relation same] at rel; exact rel)
    | Empty => exact onward y rfl
    | Role s =>
      refine ⟨?_,?_⟩
      · intro complex
        obtain ⟨j2,at_j2⟩ := nested s rfl complex
        refine ⟨j2,at_j2,?_⟩
        show J.classes (nameOf j2) y
        rw [JIs,atom_meaning I h chs ok at_j2 y]
        intro z accepts
        exact onward z (accepts_initial respects chained accepts)
      · intro _ z rel
        exact onward z (by rw [sameBut_relation same] at rel; exact rel)


/-! ### From a model of the encoding to a model of the chains -/

/-- `J` where every role relates the pairs that the role axioms and the
    chains derive from the relations of `J`. -/
def closureModel (J : Interpretation Object Value) (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain) :
    Interpretation Object Value :=
  { J with objectProperties := fun p x y => Closure J h chs (.Property p) x y }

theorem closureModel_rel {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} (closed : Closed h)
    {chs : List role_chains.Chain} (mirrored : Mirrored chs) (r : ObjectPropertyExpression) (x y : Object) :
    objectRelation (closureModel J h chs) r x y ↔ Closure J h chs r x y := by
  cases r with
  | Property p => rfl
  | Inverse p =>
    show Closure J h chs (.Property p) y x ↔ Closure J h chs (.Inverse p) x y
    rw [closure_mirror closed mirrored (.Property p) y x]
    rfl

theorem closureModel_individual (J : Interpretation Object Value) (h : hierarchy.RoleHierarchy)
    (chs : List role_chains.Chain) (a : Individual) :
    Rowl.Owl.individual (closureModel J h chs) a = Rowl.Owl.individual J a := by
  cases a <;> rfl

/-- In a model `J` of the encoding, the atoms unfold as their automata
    require. -/
theorem unfolds_of_defined {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy}
    {chs : List role_chains.Chain} {T : List role_chains.Atom} {B : List concepts.Concept} (ok : TableOk T B)
    (atoms : ∀ (k : Usize) (a : role_chains.Atom), T[k.val]? = some a →
      ∃ D, Defines.{u,v} h chs B T a D ∧ ∀ y, J.classes (nameOf k) y → denote J D y) :
    Unfolds J h chs T (fun j y => J.classes (nameOf j) y) (fillSem J B) := by
  intro k a at_k y member
  obtain ⟨D,defines,holds⟩ := atoms k a at_k
  have means := (defines.2 T (List.prefix_refl _) ok.1 J y).mp (holds y member)
  refine ⟨fun final => (fillSem_concept J B a.filler y).mpr (means.1 final),?_⟩
  intro l q' trans
  exact means.2 l q' trans

/-- For a model `J` of the role hierarchy and of the definitions of the atoms,
    an encoding in a positive position implies the encoded concept in the
    closure model, and the encoded concept in a negative position implies the
    encoding. -/
theorem enc_complete {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} (closed : Closed h)
    {chs : List role_chains.Chain} (mirrored : Mirrored chs) (long : ∀ ch ∈ chs, 2 ≤ ch.roles.val.length)
    (few : chs.length ≤ Usize.max) (respects : Respects J h) {T : List role_chains.Atom} {B : List concepts.Concept}
    (ok : TableOk T B)
    (atoms : ∀ (k : Usize) (a : role_chains.Atom), T[k.val]? = some a →
      ∃ D, Defines.{u,v} h chs B T a D ∧ ∀ y, J.classes (nameOf k) y → denote J D y)
    {p : Bool} {D D' : concepts.Concept} (enc : Enc h chs T B p D D') (fits : Fits h chs D) :
    ∀ x, (p = true → denote J D' x → denote (closureModel J h chs) D x) ∧
      (p = false → denote (closureModel J h chs) D x → denote J D' x) := by
  have unfolds := unfolds_of_defined ok atoms
  have rel := fun r x y => closureModel_rel (J := J) closed mirrored r x y
  -- Pairs derived along a complex role carry the atom of its initial state.
  have carry : ∀ (r : ObjectPropertyExpression) (k : Usize) (F : role_chains.Filler) (x y : Object),
      T[k.val]? = some ⟨r,.Initial,F⟩ → J.classes (nameOf k) x → Closure J h chs r x y → fillSem J B F y := by
    intro r k F x y at_k member closure
    obtain ⟨n,stage⟩ := closure
    obtain ⟨j,at_j,member'⟩ := stage_atoms closed long few respects unfolds (fun j y holds => holds)
      n r x y stage k _ at_k ⟨below_refl h r,below_refl h r⟩ rfl member
    exact (unfolds j _ at_j y member').1 rfl
  induction enc with
  | top p => intro x; exact ⟨fun _ _ => trivial,fun _ _ => trivial⟩
  | bottom p => intro x; exact ⟨fun _ holds => holds,fun _ holds => holds⟩
  | atom p cl => intro x; exact ⟨fun _ holds => holds,fun _ holds => holds⟩
  | notAtom p cl => intro x; exact ⟨fun _ holds => holds,fun _ holds => holds⟩
  | one p a =>
    intro x
    simp only [denote,closureModel_individual]
    exact ⟨fun _ holds => holds,fun _ holds => holds⟩
  | notOne p a =>
    intro x
    simp only [denote,closureModel_individual]
    exact ⟨fun _ holds => holds,fun _ holds => holds⟩
  | hasSelf p r =>
    intro x
    simp only [denote,rel,closure_simple closed respects fits]
    exact ⟨fun _ holds => holds,fun _ holds => holds⟩
  | notSelf p r =>
    intro x
    simp only [denote,rel,closure_simple closed respects fits]
    exact ⟨fun _ holds => holds,fun _ holds => holds⟩
  | and _ _ iha ihb =>
    intro x
    refine ⟨?_,?_⟩
    · rintro positive ⟨ha,hb⟩
      exact ⟨(iha fits.1 x).1 positive ha,(ihb fits.2 x).1 positive hb⟩
    · rintro negative ⟨ha,hb⟩
      exact ⟨(iha fits.1 x).2 negative ha,(ihb fits.2 x).2 negative hb⟩
  | or _ _ iha ihb =>
    intro x
    refine ⟨?_,?_⟩
    · rintro positive (ha | hb)
      · exact .inl ((iha fits.1 x).1 positive ha)
      · exact .inr ((ihb fits.2 x).1 positive hb)
    · rintro negative (ha | hb)
      · exact .inl ((iha fits.1 x).2 negative ha)
      · exact .inr ((ihb fits.2 x).2 negative hb)
  | @existsPos r e e' _ ih =>
    intro x
    refine ⟨?_,fun bad => Bool.noConfusion bad⟩
    rintro _ ⟨y,related,holds⟩
    exact ⟨y,(rel r x y).mpr (closure_base h chs related),(ih fits y).1 rfl holds⟩
  | @existsSimple r e e' simple _ ih =>
    intro x
    refine ⟨fun bad => Bool.noConfusion bad,?_⟩
    rintro _ ⟨y,related,holds⟩
    exact ⟨y,(closure_simple closed respects simple).mp ((rel r x y).mp related),(ih fits y).2 rfl holds⟩
  | @existsComplex r e e' n k b _ _ neg at_k at_b ih =>
    intro x
    refine ⟨fun bad => Bool.noConfusion bad,?_⟩
    rintro _ ⟨y,related,holds⟩ member
    obtain ⟨rn,runN,meansN⟩ := negate_correct.{u,v} e'
    rw [neg] at runN
    have nIs := Result.ok_injective runN
    subst nIs
    have filled := carry r k (.Base b) x y at_k member ((rel r x y).mp related)
    simp only [fillSem,at_b,Option.getD_some] at filled
    exact (meansN n rfl Object Value J y).mp filled ((ih fits y).2 rfl holds)
  | @forallComplex r e e' k b _ _ at_k at_b ih =>
    intro x
    refine ⟨?_,fun bad => Bool.noConfusion bad⟩
    intro _ member y related
    have filled := carry r k (.Base b) x y at_k member ((rel r x y).mp related)
    simp only [fillSem,at_b,Option.getD_some] at filled
    exact (ih fits y).1 rfl filled
  | @forallSimple r e e' simple _ ih =>
    intro x
    refine ⟨?_,fun bad => Bool.noConfusion bad⟩
    intro _ all y related
    exact (ih fits y).1 rfl (all y ((closure_simple closed respects simple).mp ((rel r x y).mp related)))
  | @forallNeg r e e' _ ih =>
    intro x
    refine ⟨fun bad => Bool.noConfusion bad,?_⟩
    intro _ all y related
    exact (ih fits y).2 rfl (all y ((rel r x y).mpr (closure_base h chs related)))
  | @atLeast p n r e e' _ ih =>
    intro x
    have same : ∀ y, objectRelation (closureModel J h chs) r x y ↔ objectRelation J r x y := fun y =>
      (rel r x y).trans (closure_simple closed respects fits.1)
    refine ⟨?_,?_⟩
    · intro positive many
      exact atLeast_mono (fun y ⟨related,holds⟩ => ⟨(same y).mpr related,(ih fits.2 y).1 positive holds⟩) many
    · intro negative many
      exact atLeast_mono (fun y ⟨related,holds⟩ => ⟨(same y).mp related,(ih fits.2 y).2 negative holds⟩) many
  | @atMost p n r e e' _ ih =>
    intro x
    have same : ∀ y, objectRelation (closureModel J h chs) r x y ↔ objectRelation J r x y := fun y =>
      (rel r x y).trans (closure_simple closed respects fits.1)
    refine ⟨?_,?_⟩
    · intro positive few'
      subst positive
      exact atMost_anti (fun y ⟨related,holds⟩ => ⟨(same y).mp related,(ih fits.2 y).2 rfl holds⟩) few'
    · intro negative few'
      subst negative
      exact atMost_anti (fun y ⟨related,holds⟩ => ⟨(same y).mpr related,(ih fits.2 y).1 rfl holds⟩) few'


/-! ### Packages for the actual entry point -/

/-- A model `J` of the encoding with the closure of its roles: a model of the
    role hierarchy, the chains of `chs` (which `all` includes) and the
    disjoint pairs, where encodings in positive positions imply what they
    encode and classes, individuals and the pairs of `J` stay. -/
theorem accept_model {J : Interpretation Object Value} {h : hierarchy.RoleHierarchy} (closed : Closed h)
    {chs all : List role_chains.Chain} (mirrored : Mirrored all) (long : ∀ ch ∈ all, 2 ≤ ch.roles.val.length)
    (few : all.length ≤ Usize.max) (sub : ∀ ch ∈ chs, ch ∈ all)
    (pairs : ∀ d ∈ h.disjoint.val, ¬ Complex h all d.left ∧ ¬ Complex h all d.right)
    {T : List role_chains.Atom} {B : List concepts.Concept} (ok : TableOk T B)
    (atoms : ∀ (k : Usize) (a : role_chains.Atom), T[k.val]? = some a →
      ∃ D, Defines.{u,v} h all B T a D ∧ ∀ y, J.classes (nameOf k) y → denote J D y)
    (respects : Respects J h) (constrained : Constrained J h) :
    Respects (closureModel J h all) h ∧ Chained (closureModel J h all) chs ∧ Constrained (closureModel J h all) h ∧
      (∀ {D D' : concepts.Concept}, Enc h all T B true D D' → Fits h all D →
        ∀ x, denote J D' x → denote (closureModel J h all) D x) ∧
      (closureModel J h all).classes = J.classes ∧
      (∀ a, Rowl.Owl.individual (closureModel J h all) a = Rowl.Owl.individual J a) ∧
      (∀ r x y, objectRelation J r x y → objectRelation (closureModel J h all) r x y) := by
  have rel := fun r x y => closureModel_rel (J := J) closed mirrored r x y
  refine ⟨⟨?_,?_⟩,?_,?_,?_,rfl,closureModel_individual J h all,?_⟩
  · intro s r listed x y related
    exact (rel r x y).mpr (closure_incl listed ((rel s x y).mp related))
  · intro t transitive x y z first second
    exact (rel t x z).mpr (closure_trans transitive ((rel t x y).mp first) ((rel t y z).mp second))
  · intro ch member x y along
    exact (rel ch.sup x y).mpr (closure_chain (sub ch member)
      (along_mono (fun r a b related => (rel r a b).mp related) _ x y along))
  · intro d member x y ⟨left,right⟩
    obtain ⟨simpleL,simpleR⟩ := pairs d member
    exact constrained d member x y ⟨(closure_simple closed respects simpleL).mp ((rel d.left x y).mp left),
      (closure_simple closed respects simpleR).mp ((rel d.right x y).mp right)⟩
  · intro D D' enc fits x holds
    exact (enc_complete closed mirrored long few respects ok atoms enc fits x).1 rfl holds
  · intro r x y related
    exact (rel r x y).mpr (closure_base h all related)

/-- A model `I` of the role hierarchy, the chains and the disjoint pairs with
    its atoms: a model of the role hierarchy and the disjoint pairs where every
    encoding means what it encodes, every atom satisfies its definition, and
    plain classes, individuals and pairs stay. -/
theorem reject_model {I : Interpretation Object Value} {h : hierarchy.RoleHierarchy} {all : List role_chains.Chain}
    (respects : Respects I h) (chained : Chained I all) (constrained : Constrained I h)
    {T : List role_chains.Atom} {B : List concepts.Concept} (ok : TableOk T B) :
    Respects (withAtoms I h all T B T.length) h ∧ Constrained (withAtoms I h all T B T.length) h ∧
      (∀ {p : Bool} {D D' : concepts.Concept}, Enc h all T B p D D' → Fits h all D →
        ∀ x, denote (withAtoms I h all T B T.length) D' x ↔ denote I D x) ∧
      (∀ {k : Usize} {a : role_chains.Atom} {D : concepts.Concept}, T[k.val]? = some a →
        Defines.{u,v} h all B T a D → ∀ y, (withAtoms I h all T B T.length).classes (nameOf k) y →
          denote (withAtoms I h all T B T.length) D y) ∧
      (∀ cl, ¬ Spaced cl → (withAtoms I h all T B T.length).classes cl = I.classes cl) ∧
      (∀ a, Rowl.Owl.individual (withAtoms I h all T B T.length) a = Rowl.Owl.individual I a) ∧
      (∀ r, objectRelation (withAtoms I h all T B T.length) r = objectRelation I r) := by
  have same := withAtoms_same I h all T B T.length
  refine ⟨⟨?_,?_⟩,?_,fun enc fits => enc_sound respects chained ok enc fits,
    fun at_k defines => atom_defined respects chained ok at_k defines,
    fun cl plain => withAtoms_plain I h all T B _ plain,sameBut_individual same,sameBut_relation same⟩
  · intro s r listed x y related
    rw [sameBut_relation same] at related ⊢
    exact respects.1 s r listed x y related
  · intro t transitive x y z first second
    rw [sameBut_relation same] at first second ⊢
    exact respects.2 t transitive x y z first second
  · intro d member x y both
    rw [sameBut_relation same,sameBut_relation same] at both
    exact constrained d member x y both

end
end Rowl.ChainModel
