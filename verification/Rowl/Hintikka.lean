import Rowl.Tableau

/-!
Hintikka families: the certificate a tableau with blocking produces. A family
is a list of clash-free literal sets that all satisfy the TBox concept, where
every existential restriction has a witness set in the family. Any such family
is a model: its elements are the literal sets themselves. This semantic core is
independent of the Rust procedure.
-/
namespace Rowl.Hintikka
open RowlRust RowlRust.model
open Rowl.Owl (Interpretation)
open Rowl.Nnf (conceptDenote)
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
/-- Every existential restriction of `L` has a witness in `pool`: a literal set
    satisfying the TBox concept, the filler and every matching universal filler. -/
def Witnessed (axioms : nnf.NnfConcept) (pool : List (List nnf.NnfConcept)) (L : List nnf.NnfConcept) : Prop :=
  ∀ r c, .Exists r c ∈ L → ∃ L', L' ∈ pool ∧ Sat L' axioms ∧ Sat L' c ∧ ∀ d, .Forall r d ∈ L → Sat L' d
/-- Every set of the family is clash-free, satisfies the TBox concept, and has its
    existentials witnessed in the family or among the ancestors. -/
def Coherent (axioms : nnf.NnfConcept) (family ancestors : List (List nnf.NnfConcept)) : Prop :=
  ∀ L ∈ family, ClashFree L ∧ Sat L axioms ∧ Witnessed axioms (family ++ ancestors) L

/-- Syntactic satisfaction only grows with the literal set. -/
theorem sat_mono {L L' : List nnf.NnfConcept} (sub : ∀ c ∈ L, c ∈ L') : ∀ c, Sat L c → Sat L' c := by
  intro c
  induction c with
  | Top | Bottom => exact id
  | Atom k | NotAtom k => exact sub _
  | Exists r c _ | Forall r c _ => exact sub _
  | And a b iha ihb => exact fun h => ⟨iha h.1,ihb h.2⟩
  | Or a b iha ihb => exact fun h => h.elim (fun x => .inl (iha x)) (fun x => .inr (ihb x))
/-- A literal is satisfied exactly when it is listed. -/
theorem sat_literal (L : List nnf.NnfConcept) (c : nnf.NnfConcept) (literal : Rowl.Tableau.Literal c) :
    Sat L c ↔ c ∈ L := by
  cases c <;> simp_all [Sat,Rowl.Tableau.Literal]

/-- The model of a family: its elements are the family's literal sets; a set
    belongs to a named class when it lists it, and a set reaches another along a
    role when the other satisfies every universal filler on that role. -/
def familyModel (family : List (List nnf.NnfConcept)) (root : List nnf.NnfConcept) (rootMember : root ∈ family) :
    Interpretation {L // L ∈ family} Unit where
  objectsNonempty := ⟨⟨root,rootMember⟩⟩
  dataNonempty := ⟨()⟩
  classes k L := .Atom k ∈ L.val
  objectProperties r L L' := ∀ d, .Forall r d ∈ L.val → Sat L'.val d
  dataProperties _ _ _ := False
  namedIndividuals _ := ⟨root,rootMember⟩
  anonymousIndividuals _ := ⟨root,rootMember⟩
  datatypes _ _ := False
  literals _ := ()
  facets _ _ := False
  named _ := False

/-- Truth lemma: in the model of a closed coherent family, each set has every
    concept it satisfies syntactically. -/
theorem family_truth (axioms : nnf.NnfConcept) (family : List (List nnf.NnfConcept))
    (coherent : Coherent axioms family []) (root : List nnf.NnfConcept) (rootMember : root ∈ family) :
    ∀ (c : nnf.NnfConcept) (L : {L // L ∈ family}), Sat L.val c →
      conceptDenote (familyModel family root rootMember) c L := by
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
    obtain ⟨L',member,_,filler,universal⟩ := (coherent L.val L.property).2.2 r c holds
    simp only [List.append_nil] at member
    exact ⟨⟨L',member⟩,universal,ih ⟨L',member⟩ filler⟩
  | Forall r c ih =>
    intro L holds L' edge
    exact ih L' (edge c holds)

/-- A closed coherent family with a set satisfying the concept yields a model of
    the TBox concept with an instance of the concept. -/
theorem model_of_family (axioms c : nnf.NnfConcept) (family : List (List nnf.NnfConcept))
    (coherent : Coherent axioms family []) (root : List nnf.NnfConcept) (rootMember : root ∈ family)
    (rootSat : Sat root c) :
    ∃ (Object : Type) (I : Interpretation Object Unit), (∀ y, conceptDenote I axioms y) ∧ ∃ x, conceptDenote I c x := by
  refine ⟨{L // L ∈ family},familyModel family root rootMember,?_,⟨root,rootMember⟩,?_⟩
  · intro y
    exact family_truth axioms family coherent root rootMember axioms y (coherent y.val y.property).2.1
  · exact family_truth axioms family coherent root rootMember c ⟨root,rootMember⟩ rootSat
end Rowl.Hintikka
