import Rowl.KeyEncoding
import Rowl.DataSound

/-!
Models of the key encoding and OWL models with keys. From an OWL model of a
closure whose named individuals are named, `liftedN` makes a model of the
closure's key encoding: the lifted interpretation of the data encoding, with
`N` the named elements, `mark` the self loops of the named elements and the
data nodes, and `share(r)` the pairs that share such an element along `r`
(`keyed_lifted_model`). From a model of the key encoding, `keyedSound` makes an
OWL model of the closure: the OWL interpretation of the data encoding's
soundness proof, with the named elements exactly the closure's named
individuals and every other named individual placed at the first of them
(`keyed_encoded_model`). In both, every question whose individuals the closure
names holds exactly where its encoding does.
-/
namespace Rowl.KeyModels
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DatatypeMap (Normative)
open Rowl.Datatypes (Canonical valueOf typeOf kindOf InKind)
open Rowl.AlcOntology (RoleOf)
open Rowl.DataEncoding
open Rowl.DataMeaning
open Rowl.DataAxioms
open Rowl.DataStructure
open Rowl.DataComplete
open Rowl.DataSound
open Rowl.KeyEncoding
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe u v w x

/-! ### Names that are not the key encoding's -/

theorem plain_not_key {s : List U8} (plain : ¬ Reserved s) : s ≠ keyName := by
  rintro rfl; exact plain (by simp [Reserved, keyName])
theorem plain_not_mark {s : List U8} (plain : ¬ Reserved s) : s ≠ markName := by
  rintro rfl; exact plain (by simp [Reserved, markName])
theorem plain_not_share {s : List U8} (plain : ¬ Reserved s) (r : ObjectPropertyExpression) : s ≠ shareName r := by
  rintro rfl; cases r <;> exact plain (by simp [Reserved, shareName])

theorem data_not_key : dataClass.iri.spelling.val ≠ keyName := by simp [dataClass_name, dataName, keyName]
theorem kind_not_key (k : datatypes.Kind) : (kindClass k).iri.spelling.val ≠ keyName := by
  simp [kindClass_name, kindName, keyName]
theorem bit_not_key (j : Usize) : (bitClass j).iri.spelling.val ≠ keyName := by
  simp [bitClass_name, bitName, keyName]
theorem thing_not_key : thing.iri.spelling.val ≠ keyName := plain_not_key thing_plain
theorem nothing_not_key : nothing.iri.spelling.val ≠ keyName := plain_not_key nothing_plain

theorem data_role_not_mark {p : DataProperty} {q : ObjectProperty} (h : DataRoleOf p q) :
    q.iri.spelling.val ≠ markName := by
  simp only [DataRoleOf] at h; simp [h, dataRoleName, markName]
theorem data_role_not_share {p : DataProperty} {q : ObjectProperty} (h : DataRoleOf p q)
    (r : ObjectPropertyExpression) : q.iri.spelling.val ≠ shareName r := by
  simp only [DataRoleOf] at h; cases r <;> simp [h, dataRoleName, shareName]

/-- The role whose `share` role a role is, if it is one. -/
noncomputable def sharedRole (p : ObjectProperty) : Option ObjectPropertyExpression :=
  if h : ∃ r, p.iri.spelling.val = shareName r then some (Classical.choose h) else none

theorem sharedRole_share {p : ObjectProperty} {r : ObjectPropertyExpression} (h : p.iri.spelling.val = shareName r) :
    sharedRole p = some r := by
  have ex : ∃ r, p.iri.spelling.val = shareName r := ⟨r, h⟩
  simp only [sharedRole, dif_pos ex]
  exact congrArg some (shareName_injective ((Classical.choose_spec ex).symm.trans h))

theorem sharedRole_none {p : ObjectProperty} (h : ∀ r, p.iri.spelling.val ≠ shareName r) : sharedRole p = none := by
  have ex : ¬ ∃ r, p.iri.spelling.val = shareName r := fun ⟨r, same⟩ => h r same
  simp only [sharedRole, dif_neg ex]

/-! ### The lifted interpretation with the key encoding's names -/

section Lifted
variable {Object : Type u} {Value : Type v}

/-- The named elements of an OWL interpretation in the lifted one. -/
def KeyNamed (I : Interpretation Object Value) : Object ⊕ Value → Prop
  | .inl z => I.named z
  | .inr _ => False

/-- The marked elements: the named elements and the data nodes. -/
def Marked (I : Interpretation Object Value) : Object ⊕ Value → Prop
  | .inl z => I.named z
  | .inr _ => True

theorem marked_of_named (I : Interpretation Object Value) (y : Object ⊕ Value) (named : KeyNamed I y) :
    Marked I y := by
  cases y with
  | inl z => exact named
  | inr _ => trivial

/-- The interpretation of the key encoding made from an OWL interpretation: the
    lifted interpretation of the data encoding, with `N` the named elements,
    `mark` the self loops of the marked elements and `share(r)` the pairs that
    share a marked element along `r`. -/
noncomputable def liftedN (context : data_ontology.Context) (I : Interpretation Object Value)
    (lit : datatypes.DataValue → Value) (x0 : Object) : Interpretation (Object ⊕ Value) Value :=
  { lifted context I lit x0 with
    classes := fun c y => if c.iri.spelling.val = keyName then KeyNamed I y else (lifted context I lit x0).classes c y
    objectProperties := fun p y y' =>
      if p.iri.spelling.val = markName then y = y' ∧ Marked I y
      else match sharedRole p with
        | some r => ∃ z, Marked I z ∧ objectRelation (lifted context I lit x0) r y z ∧
            objectRelation (lifted context I lit x0) r y' z
        | none => (lifted context I lit x0).objectProperties p y y' }

variable {context : data_ontology.Context} {I : Interpretation Object Value} {lit : datatypes.DataValue → Value}
  {x0 : Object}

theorem liftedN_class {c : Class} (other : c.iri.spelling.val ≠ keyName) (y : Object ⊕ Value) :
    (liftedN context I lit x0).classes c y = (lifted context I lit x0).classes c y := by
  simp only [liftedN, other, ↓reduceIte]

theorem liftedN_key (y : Object ⊕ Value) : (liftedN context I lit x0).classes keyClass y = KeyNamed I y := by
  simp only [liftedN, keyClass_name, ↓reduceIte]

theorem liftedN_role {p : ObjectProperty} (notMark : p.iri.spelling.val ≠ markName)
    (notShare : ∀ r, p.iri.spelling.val ≠ shareName r) (y y' : Object ⊕ Value) :
    (liftedN context I lit x0).objectProperties p y y' = (lifted context I lit x0).objectProperties p y y' := by
  simp only [liftedN, notMark, ↓reduceIte, sharedRole_none notShare]

theorem liftedN_mark (y y' : Object ⊕ Value) :
    (liftedN context I lit x0).objectProperties markRole y y' ↔ y = y' ∧ Marked I y := by
  simp only [liftedN, markRole_name, ↓reduceIte]

theorem liftedN_share {p : ObjectProperty} {r : ObjectPropertyExpression} (share : p.iri.spelling.val = shareName r)
    (y y' : Object ⊕ Value) :
    (liftedN context I lit x0).objectProperties p y y' ↔ ∃ z, Marked I z ∧
      objectRelation (lifted context I lit x0) r y z ∧ objectRelation (lifted context I lit x0) r y' z := by
  have notMark : p.iri.spelling.val ≠ markName := by
    rw [share]; cases r <;> simp [shareName, markName]
  simp only [liftedN, notMark, ↓reduceIte, sharedRole_share share]

theorem liftedN_named : (liftedN context I lit x0).namedIndividuals = (lifted context I lit x0).namedIndividuals := rfl

theorem liftedN_plain_class {c : Class} (plain : ¬ Reserved c.iri.spelling.val) (y : Object ⊕ Value) :
    (liftedN context I lit x0).classes c y = (lifted context I lit x0).classes c y :=
  liftedN_class (plain_not_key plain) y

theorem liftedN_data_class (y : Object ⊕ Value) :
    (liftedN context I lit x0).classes dataClass y = (lifted context I lit x0).classes dataClass y :=
  liftedN_class data_not_key y

theorem liftedN_kind_class (k : datatypes.Kind) (y : Object ⊕ Value) :
    (liftedN context I lit x0).classes (kindClass k) y = (lifted context I lit x0).classes (kindClass k) y :=
  liftedN_class (kind_not_key k) y

theorem liftedN_bit_class (j : Usize) (y : Object ⊕ Value) :
    (liftedN context I lit x0).classes (bitClass j) y = (lifted context I lit x0).classes (bitClass j) y :=
  liftedN_class (bit_not_key j) y

theorem liftedN_plain_role {p : ObjectProperty} (plain : ¬ Reserved p.iri.spelling.val) (y y' : Object ⊕ Value) :
    (liftedN context I lit x0).objectProperties p y y' = (lifted context I lit x0).objectProperties p y y' :=
  liftedN_role (plain_not_mark plain) (plain_not_share plain) y y'

theorem liftedN_relation {r : ObjectPropertyExpression} (plain : ¬ Reserved (RoleOf r).iri.spelling.val)
    (y y' : Object ⊕ Value) :
    objectRelation (liftedN context I lit x0) r y y' ↔ objectRelation (lifted context I lit x0) r y y' := by
  cases r with
  | Property p => simp only [objectRelation]; rw [liftedN_plain_role (show ¬ Reserved p.iri.spelling.val from plain)]
  | Inverse p => simp only [objectRelation]; rw [liftedN_plain_role (show ¬ Reserved p.iri.spelling.val from plain)]

theorem liftedN_data_relation {p : DataProperty} {role : ObjectPropertyExpression}
    (run : data_ontology.data_role context p = .ok (some role)) (y y' : Object ⊕ Value) :
    objectRelation (liftedN context I lit x0) role y y' ↔ objectRelation (lifted context I lit x0) role y y' := by
  obtain ⟨res, run', facts⟩ := data_role_correct context p
  rw [run] at run'
  cases Result.ok_injective run'
  rcases facts role rfl with ⟨_, rfl⟩ | ⟨_, _, _, q, rfl, roleOf⟩
  · exact liftedN_relation (r := .Property bottomObject) bottom_plain y y'
  · simp only [objectRelation]
    rw [liftedN_role (data_role_not_mark roleOf) (data_role_not_share roleOf)]

end Lifted


/-! ### The lifted interpretation keeps the data encoding's correspondence -/

section Transfer
variable {Object : Type u} {Value : Type v} {Native : Type w} {D : DatatypeMap Native}
  {embed : ValueEmbedding D Value} {V : Vocabulary} {I : Interpretation Object Value}
  {context : data_ontology.Context}

theorem liftedN_node (N : Normative D) (x0 : Object) (v : Value) :
    NodeValue context I (liftedN context I (litOf N embed) x0) (litOf N embed) (.inr v) v where
  kinds := fun k used => by rw [liftedN_kind_class]; exact (lifted_node N x0 v).kinds k used
  values := (lifted_node N x0 v).values

theorem liftedN_range_frame (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) :
    RangeFrame I (liftedN context I (litOf N embed) x0) (litOf N embed) where
  literal := (lifted_range_frame (context := context) N x0 vocab interp).literal
  thing := fun y => by
    rw [liftedN_class thing_not_key]; exact (lifted_range_frame (context := context) N x0 vocab interp).thing y
  literals := (lifted_range_frame (context := context) N x0 vocab interp).literals

theorem liftedN_filler (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) {range : Option DataRange} {filler : Option ClassExpression}
    (run : data_ontology.encode_optional_range context range = .ok (some filler)) (v : Value) :
    Rowl.Concepts.FillerHolds (liftedN context I (litOf N embed) x0) filler (.inr v) ↔ RangeHolds I range v := by
  rcases optional_range_meaning.{u,v,max u v,v} context range filler run with ⟨rfl, rfl⟩ | ⟨r, c, rfl, rfl, means⟩
  · simp [Rowl.Concepts.FillerHolds, RangeHolds]
  · simp only [Rowl.Concepts.FillerHolds, RangeHolds]
    exact (means I _ _ (liftedN_range_frame N x0 vocab interp) (.inr v) v (liftedN_node N x0 v)).symm

theorem liftedN_simulates (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) (good : Good context) (atoms : List (DataProperty × Option DataRange × Nat)) :
    Simulates context I (liftedN context I (litOf N embed) x0) Sum.inl Plain atoms := by
  have base := lifted_simulates (context := context) N x0 vocab interp good atoms
  refine ⟨Sum.inl_injective, fun y => ?_, fun c z plain => ?_, fun r z y plain => ?_,
    fun r inContext y y' related => ?_, fun y y' => ?_, base.individuals,
    fun p range n mem role filler roleRun fillerRun z => ?_⟩
  · rw [liftedN_data_class]; exact base.objects y
  · rw [liftedN_plain_class plain]; exact base.classes c z plain
  · rw [liftedN_plain_role plain]; exact base.roles r z y plain
  · have plain := (good.2.1 r inContext).1
    rw [liftedN_plain_role plain] at related
    rw [liftedN_data_class, liftedN_data_class]
    exact base.closed r inContext y y' related
  · rw [liftedN_plain_role topObject_plain]; exact base.topAll y y'
  · rw [base.data p range n mem role filler roleRun fillerRun z]
    have same : ∀ y, (objectRelation (lifted context I (litOf N embed) x0) role (.inl z) y ∧
        Rowl.Concepts.FillerHolds (lifted context I (litOf N embed) x0) filler y) ↔
        (objectRelation (liftedN context I (litOf N embed) x0) role (.inl z) y ∧
          Rowl.Concepts.FillerHolds (liftedN context I (litOf N embed) x0) filler y) := by
      intro y
      rw [liftedN_data_relation roleRun]
      constructor
      · rintro ⟨related, fill⟩
        obtain ⟨v, rfl, _⟩ := (lifted_data_role interp.2.2.2.1 interp.2.2.2.2.2.1 roleRun z _).mp related
        exact ⟨related, (liftedN_filler N x0 vocab interp fillerRun v).mpr
          ((lifted_filler N x0 vocab interp fillerRun v).mp fill)⟩
      · rintro ⟨related, fill⟩
        obtain ⟨v, rfl, _⟩ := (lifted_data_role interp.2.2.2.1 interp.2.2.2.2.2.1 roleRun z _).mp related
        exact ⟨related, (lifted_filler N x0 vocab interp fillerRun v).mpr
          ((liftedN_filler N x0 vocab interp fillerRun v).mp fill)⟩
    simp only [same]

theorem liftedN_placed (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) :
    Placed context I (liftedN context I (litOf N embed) x0) Sum.inl (litOf N embed) (fun _ v d => d = .inr v) := by
  have base := lifted_placed (context := context) N x0 vocab interp
  refine ⟨base.functional, base.injective, fun _ v d h => h ▸ liftedN_node N x0 v, fun p role run z v => ?_,
    base.literals, base.top⟩
  rw [base.data p role run z v]
  simp only [liftedN_data_relation run]

theorem liftedN_inert (N : Normative D) (x0 : Object) (interp : IsInterpretation D embed V I) :
    Inert context (liftedN context I (litOf N embed) x0) Sum.inl (fun _ v d => d = .inr v) := by
  have base := lifted_inert (context := context) N x0 interp
  refine ⟨fun c y plain notThing dataNode => ?_, fun p role run y y' related => ?_,
    fun p role run z d related => ?_⟩
  · rw [liftedN_data_class] at dataNode
    rw [liftedN_plain_class plain]
    exact base.classes c y plain notThing dataNode
  · rw [liftedN_data_relation run] at related
    rw [liftedN_data_class]
    exact base.sources p role run y y' related
  · rw [liftedN_data_relation run] at related
    exact base.placed p role run z d related

theorem liftedN_frame {lit : datatypes.DataValue → Value} {x0 : Object} {bits : Usize} (good : Good context)
    (frame : Frame context bits (lifted context I lit x0)) : Frame context bits (liftedN context I lit x0) := by
  obtain ⟨roles, data, kinds, values, object⟩ := frame
  refine ⟨fun r mem y y' related => ?_, fun p mem role run y y' related => ?_, ?_, fun i h => ?_, ?_⟩
  · rw [liftedN_plain_role (good.2.1 r mem).1] at related
    rw [liftedN_data_class, liftedN_data_class]
    exact roles r mem y y' related
  · rw [liftedN_data_relation run] at related
    rw [liftedN_data_class, liftedN_data_class]
    exact data p mem role run y y' related
  · cases kinds
    constructor <;> simp only [Included, Apart, Truths, liftedN_kind_class, liftedN_named] <;> assumption
  · have := values i h
    simp only [ValueFact, liftedN_data_class, liftedN_kind_class, liftedN_bit_class, liftedN_named] at this ⊢
    exact this
  · rw [liftedN_data_class, liftedN_named]; exact object

theorem liftedN_interpretation (N : Normative D) (x0 : Object) (interp : IsInterpretation D embed V I) :
    IsInterpretation D embed V (liftedN context I (litOf N embed) x0) := by
  obtain ⟨hThing, hNothing, hTop, hBottom, rest⟩ := lifted_interpretation (context := context) N x0 interp
  refine ⟨fun y => ?_, fun y => ?_, fun y y' => ?_, fun y y' => ?_, rest⟩
  · rw [liftedN_class thing_not_key]; exact hThing y
  · rw [liftedN_class nothing_not_key]; exact hNothing y
  · rw [liftedN_plain_role topObject_plain]; exact hTop y y'
  · rw [liftedN_plain_role bottom_plain]; exact hBottom y y'

theorem liftedN_structured (lit : datatypes.DataValue → Value) (x0 : Object) :
    Structured (liftedN context I lit x0) (Marked I) := by
  refine ⟨fun y y' => liftedN_mark y y', fun r p named plain y y' => ?_⟩
  rw [liftedN_share named]
  simp only [liftedN_relation plain]

theorem liftedN_class_iff (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) (good : Good context) {c c' : ClassExpression}
    (run : data_ontology.encode_class context c = .ok (some c')) (plain : ∀ a ∈ classIndividuals c, Plain a)
    (z : Object) : classDenote I c z ↔ classDenote (liftedN context I (litOf N embed) x0) c' (.inl z) := by
  obtain ⟨res, run', means⟩ := encode_class_meaning.{u,v,max u v,v} context c
  rw [run] at run'
  cases Result.ok_injective run'
  exact means c' rfl I _ Sum.inl Plain (classAtoms c) (liftedN_simulates N x0 vocab interp good _) (fun _ h => h)
    plain z

theorem liftedN_successor {lit : datatypes.DataValue → Value} {x0 : Object} {r : ObjectPropertyExpression}
    (plain : ¬ Reserved (RoleOf r).iri.spelling.val) (notTop : RoleOf r ≠ topObject) {a : Object}
    {y : Object ⊕ Value} (related : objectRelation (liftedN context I lit x0) r (.inl a) y) : ∃ b, y = .inl b := by
  rw [liftedN_relation plain] at related
  cases r with
  | Property p =>
    cases y with
    | inl b => exact ⟨b, rfl⟩
    | inr v =>
      simp only [objectRelation, lifted] at related
      rcases related with top | ⟨q, roleOf, _⟩
      · exact absurd top notTop
      · exact absurd (data_role_reserved roleOf) plain
  | Inverse p =>
    cases y with
    | inl b => exact ⟨b, rfl⟩
    | inr v =>
      simp only [objectRelation, lifted] at related
      exact absurd related notTop

/-- A key of the OWL interpretation holds for the elements of `N` in the lifted
    one. -/
theorem liftedN_key_holds (N : Normative D) (x0 : Object) (vocab : IsVocabulary D V)
    (interp : IsInterpretation D embed V I) (good : Good context) {e e' : ClassExpression}
    {ops : List ObjectPropertyExpression} (run : data_ontology.encode_class context e = .ok (some e'))
    (plain : ∀ a ∈ classIndividuals e, Plain a)
    (opsIn : ∀ r ∈ ops, ¬ Reserved (RoleOf r).iri.spelling.val ∧ RoleOf r ∈ context.roles.val)
    (key : ∀ x y, classDenote I e x → I.named x → classDenote I e y → I.named y →
      (∀ p ∈ ops, ∃ z, I.named z ∧ objectRelation I p x z ∧ objectRelation I p y z) → x = y) :
    KeyHolds (liftedN context I (litOf N embed) x0) e' ops (Marked I) := by
  intro y y' ny ny' ey ey' shared
  rw [liftedN_key] at ny ny'
  cases y with
  | inr _ => exact absurd ny id
  | inl a =>
  cases y' with
  | inr _ => exact absurd ny' id
  | inl b =>
  refine congrArg Sum.inl (key a b ((liftedN_class_iff N x0 vocab interp good run plain a).mpr ey) ny
    ((liftedN_class_iff N x0 vocab interp good run plain b).mpr ey') ny' (fun p mem => ?_))
  obtain ⟨z, markedZ, ra, rb⟩ := shared p mem
  have notTop : RoleOf p ≠ topObject := fun same => (good.2.1 _ (opsIn p mem).2).2 same
  obtain ⟨c, rfl⟩ := liftedN_successor (opsIn p mem).1 notTop ra
  have sim := liftedN_simulates N x0 vocab interp good []
  exact ⟨c, markedZ, (relation_place sim p (opsIn p mem).1 a c).mpr ra, (relation_place sim p (opsIn p mem).1 b c).mpr rb⟩

end Transfer


/-! ### The OWL interpretation made from a model of the key encoding -/

section Sound
variable {Object' : Type u} {Value' : Type x} {Native : Type w} {D : DatatypeMap Native}

/-- Where the named individuals outside `names` are placed: at the first of
    `names`, or at `o` when there is none. -/
noncomputable def fallback (context : data_ontology.Context) (J : Interpretation Object' Value') (N : Normative D)
    (atoms : List (DataProperty × Option DataRange × Nat)) (names : List NamedIndividual) (o : Element J) :
    Element J :=
  match names with
  | [] => o
  | b :: _ => (sound.{u,v,w,x} context J N atoms o).namedIndividuals b

/-- The OWL interpretation made from a model of the key encoding: the data
    encoding's interpretation `sound`, with the named individuals outside
    `names` at the first of them and the named elements exactly the elements of
    `names` (or `o` when there is none). -/
noncomputable def keyedSound (context : data_ontology.Context) (J : Interpretation Object' Value') (N : Normative D)
    (atoms : List (DataProperty × Option DataRange × Nat)) (names : List NamedIndividual) (o : Element J) :
    Interpretation (Element J) (Values.{v,w} Native) :=
  { sound.{u,v,w,x} context J N atoms o with
    namedIndividuals := fun a => if a ∈ names then (sound.{u,v,w,x} context J N atoms o).namedIndividuals a
      else fallback.{u,v,w,x} context J N atoms names o
    named := fun z => (∃ a ∈ names, z = (sound.{u,v,w,x} context J N atoms o).namedIndividuals a) ∨
      (names = [] ∧ z = o) }

/-- The individuals that a model of the encoding places at elements that are no
    data nodes, the named ones among `names`. -/
def KnownIn (J : Interpretation Object' Value') (names : List NamedIndividual) (a : Individual) : Prop :=
  Known J a ∧ ∀ n, a = .Named n → n ∈ names

variable {context : data_ontology.Context} {J : Interpretation Object' Value'} {N : Normative D}
  {atoms : List (DataProperty × Option DataRange × Nat)} {names : List NamedIndividual} {bits : Usize}

theorem keyedSound_name {o : Element J} {a : NamedIndividual} (inNames : a ∈ names) :
    (keyedSound.{u,v,w,x} context J N atoms names o).namedIndividuals a =
      (sound.{u,v,w,x} context J N atoms o).namedIndividuals a := by
  simp only [keyedSound, if_pos inNames]

/-- A data range holds at a value in the OWL interpretation made from a model of
    the key encoding exactly when it holds there in the data encoding's: both
    have the same datatypes, literals and facets. -/
theorem keyedSound_data (o : Element J) (r : DataRange) (y : Values.{v,w} Native) :
    dataDenote (keyedSound.{u,v,w,x} context J N atoms names o) r y ↔
      dataDenote (sound.{u,v,w,x} context J N atoms o) r y := by
  cases h : r with
  | Datatype dt => rw [dataDenote, dataDenote]; rfl
  | Intersection xs =>
    rw [dataDenote, dataDenote]
    have first := keyedSound_data o xs.first y
    have second := keyedSound_data o xs.second y
    rw [first, second]
    exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun e => imp_congr_right fun mem =>
      keyedSound_data o e y))
  | Union xs =>
    rw [dataDenote, dataDenote]
    have first := keyedSound_data o xs.first y
    have second := keyedSound_data o xs.second y
    rw [first, second]
    exact or_congr Iff.rfl (or_congr Iff.rfl (exists_congr fun e => exists_congr fun mem =>
      keyedSound_data o e y))
  | Complement e =>
    rw [dataDenote, dataDenote]
    exact not_congr (keyedSound_data o e y)
  | OneOf xs => rw [dataDenote, dataDenote]; rfl
  | Restriction dt xs => rw [dataDenote, dataDenote]; rfl
termination_by sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

theorem keyedSound_range (o : Element J) (range : Option DataRange) (y : Values.{v,w} Native) :
    RangeHolds (keyedSound.{u,v,w,x} context J N atoms names o) range y ↔
      RangeHolds (sound.{u,v,w,x} context J N atoms o) range y := by
  cases range with
  | none => exact Iff.rfl
  | some r => exact keyedSound_data o r y

theorem keyedSound_simulates (good : Good context) (frame : Frame context bits J)
    (enough : context.values.val.length ≤ 2 ^ bits.val) (jThing : ∀ d, J.classes thing d)
    (jTop : ∀ y y', J.objectProperties topObject y y') (o : Element J) :
    Simulates context (keyedSound.{u,v,w,x} context J N atoms names o) J Subtype.val (KnownIn J names) atoms := by
  have base := sound_simulates.{u,v,w,x} (N := N) (atoms := atoms) good frame enough jThing jTop o
  refine ⟨base.injective, base.objects, base.classes, base.roles, base.closed, base.topAll, fun a known => ?_,
    fun p range n mem role filler roleRun fillerRun z => ?_⟩
  swap
  · have := base.data p range n mem role filler roleRun fillerRun z
    simp only [keyedSound_range]
    exact this
  cases a with
  | Named n =>
    have known' : ¬ J.classes dataClass (J.namedIndividuals n) := known.1
    simp only [individual, keyedSound_name (known.2 n rfl), sound, dif_pos known']
  | Anonymous b => exact base.individuals (.Anonymous b) known.1

theorem keyedSound_placed (good : Good context) (frame : Frame context bits J)
    (enough : context.values.val.length ≤ 2 ^ bits.val) (o : Element J) :
    Placed context (keyedSound.{u,v,w,x} context J N atoms names o) J Subtype.val (litValue N)
      (fun z y d => Place.{u,v,w,x} context J N atoms z.1 y d) := by
  have base := sound_placed.{u,v,w,x} (N := N) (atoms := atoms) good frame enough o
  exact ⟨base.functional, base.injective, fun z v d pl => ⟨(base.nodes z v d pl).kinds, (base.nodes z v d pl).values⟩,
    base.data, base.literals, base.top⟩

theorem keyedSound_range_frame (jThing : ∀ d, J.classes thing d) (o : Element J) :
    RangeFrame (keyedSound.{u,v,w,x} context J N atoms names o) J (litValue N) := by
  have base := sound_range_frame.{u,v,w,x} (context := context) (N := N) (atoms := atoms) jThing o
  exact ⟨base.literal, base.thing, base.literals⟩

theorem keyedSound_interpretation (V : Vocabulary) (jThing : ∀ d, J.classes thing d)
    (jNothing : ∀ d, ¬ J.classes nothing d) (jTop : ∀ y y', J.objectProperties topObject y y')
    (jBottom : ∀ y y', ¬ J.objectProperties bottomObject y y') (o : Element J) :
    IsInterpretation D (ValueEmbedding.ofEmbedding D ⟨embedValue.{v,w}, embedValue_injective⟩) V
      (keyedSound.{u,v,w,x} context J N atoms names o) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, _⟩ := sound_interpretation.{u,v,w,x} (context := context)
    (J := J) (N := N) (atoms := atoms) V jThing jNothing jTop jBottom o
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, fun a _ => ?_⟩
  by_cases inNames : a ∈ names
  · exact .inl ⟨a, inNames, keyedSound_name inNames⟩
  · rcases names with _ | ⟨b, rest⟩
    · exact .inr ⟨rfl, by simp [keyedSound, fallback]⟩
    · exact .inl ⟨b, List.mem_cons_self, by simp only [keyedSound, fallback, if_neg inNames]⟩

theorem relation_val (o : Element J) (r : ObjectPropertyExpression) (y y' : Element J) :
    objectRelation (keyedSound.{u,v,w,x} context J N atoms names o) r y y' ↔ objectRelation J r y.1 y'.1 := by
  cases r <;> rfl

end Sound


/-! ### The models -/

section Models

theorem withAnonymous_self_eq {Object : Type u} {Value : Type v} (I : Interpretation Object Value) :
    withAnonymous I I.anonymousIndividuals = I := by
  cases I; rfl

theorem liftedN_anonymous {Object : Type u} {Value : Type v} (context : data_ontology.Context)
    (I : Interpretation Object Value) (lit : datatypes.DataValue → Value) (x0 : Object)
    (g : AnonymousIndividual → Object) :
    withAnonymous (liftedN context I lit x0) (Sum.inl ∘ g) = liftedN context (withAnonymous I g) lit x0 := rfl

theorem unkeyed_closure {items : List AnnotatedAxiom} {item : AnnotatedAxiom} (mem : item ∈ unkeyedItems items)
    {a : Individual} (inside : a ∈ axiomIndividuals item.axiom) : a ∈ closureIndividuals items :=
  List.mem_flatMap.mpr ⟨item, (List.mem_filter.mp mem).1, List.mem_append_left _ inside⟩

theorem key_closure {items : List AnnotatedAxiom} {item : AnnotatedAxiom} (mem : item ∈ items)
    {e : ClassExpression} {ops : alloc.vec.Vec ObjectPropertyExpression} {dps : alloc.vec.Vec DataProperty}
    (shape : item.axiom = .HasKey e ops dps) {a : Individual} (inside : a ∈ classIndividuals e) :
    a ∈ closureIndividuals items :=
  List.mem_flatMap.mpr ⟨item, mem, List.mem_append_right _ (by rw [shape]; exact inside)⟩

/-- A model of a closure's key encoding gives an OWL model of the closure
    whose elements stand at the model's elements that are no data nodes, with
    the closure's named individuals at their own elements, and at which each
    question whose individuals are named individuals of the closure holds
    exactly when its encoding does. -/
theorem keyed_encoded_model {Object' : Type u} {Value' : Type (max w v)} {Native : Type w} {D : DatatypeMap Native}
    (N : Normative D) {V : Vocabulary} (vocab : IsVocabulary D V) {context : data_ontology.Context}
    (good : Good context) {items : alloc.vec.Vec AnnotatedAxiom} {nodes : alloc.vec.Vec Individual}
    {counting : Bool} {enc : alloc.vec.Vec AnnotatedAxiom}
    (encRun : key_ontology.encode context items nodes counting = .ok (some enc))
    (nodesExact : ∀ b, b ∈ nodes.val ↔ b ∈ closureIndividuals items.val)
    {embed' : ValueEmbedding D Value'} {J : Interpretation Object' Value'} (model : Model D embed' V J enc.val)
    (questions : List ClassExpression)
    (known : ∀ e ∈ questions, ∀ a ∈ classIndividuals e, (∃ n, a = .Named n) ∧ a ∈ nodes.val) :
    ∃ (Object : Type u) (Value : Type (max w v)) (embed : ValueEmbedding D Value) (I : Interpretation Object Value)
      (point : Object → Object'), Model D embed V I items.val ∧
      (∀ y, ¬ J.classes dataClass y → ∃ z, point z = y) ∧
      (∀ a : NamedIndividual, Individual.Named a ∈ nodes.val →
        ¬ J.classes dataClass (J.namedIndividuals a) ∧ point (I.namedIndividuals a) = J.namedIndividuals a) ∧
      ∀ e ∈ questions, ∀ e', data_ontology.encode_class context e = .ok (some e') →
        ∀ z, classDenote I e z ↔ classDenote J e' (point z) := by
  obtain ⟨_, jInterp, g, jSat⟩ := model
  obtain ⟨res, run, facts⟩ := Rowl.KeyEncoding.encode_meaning.{u, max v w, u, max w v} context good items nodes
    counting
  rw [encRun] at run
  cases Result.ok_injective run
  obtain ⟨_, newU, _, bits, _, meansU, enough, _, _, _, keysMeans, iff⟩ := facts enc rfl
  obtain ⟨⟨_, frame⟩, newUHolds, apart, held, marks, keysHold⟩ := (iff (withAnonymous J g)).mp jSat
  let o : Element (withAnonymous J g) := ⟨(withAnonymous J g).namedIndividuals objectIndividual, frame.object⟩
  let names := namesOf nodes.val
  let atoms := (unkeyedItems items.val).flatMap (fun i => axiomAtoms i.axiom) ++
    items.val.flatMap (fun i => keyAtoms i.axiom) ++ questions.flatMap classAtoms
  let I := keyedSound.{u,v,w,max w v} context (withAnonymous J g) N atoms names o
  have sim : Simulates context I (withAnonymous J g) Subtype.val (KnownIn (withAnonymous J g) names) atoms :=
    keyedSound_simulates good frame enough jInterp.1 jInterp.2.2.1 o
  have nodeKnown : ∀ a ∈ nodes.val, KnownIn (withAnonymous J g) names a := by
    intro a mem
    have h := held a mem
    cases a with
    | Named n => exact ⟨apart _ h, fun m same => by cases same; exact mem_namesOf.mpr mem⟩
    | Anonymous b => exact ⟨h, fun m same => by cases same⟩
  have unkeyedSat : ∀ item ∈ unkeyedItems items.val, satisfies I item.axiom :=
    (meansU.1 I (withAnonymous J g) Subtype.val (KnownIn (withAnonymous J g) names) atoms (litValue N) _ sim
      (keyedSound_placed good frame enough o) (keyedSound_range_frame (context := context) (J := withAnonymous J g) (N := N)
        (atoms := atoms) (names := names) jInterp.1 o)
      (fun item mem a inside => List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨item, mem, inside⟩)))
      (fun item mem a inside => nodeKnown a ((nodesExact a).mpr (unkeyed_closure mem inside)))).1 newUHolds
  have namedAt : names ≠ [] → ∀ z, I.named z →
      ∃ a ∈ names, z = I.namedIndividuals a ∧ z.1 = J.namedIndividuals a := by
    rintro nonempty z (⟨a, aIn, rfl⟩ | ⟨isEmpty, _⟩)
    · refine ⟨a, aIn, (keyedSound_name aIn).symm, ?_⟩
      have known' : ¬ (withAnonymous J g).classes dataClass ((withAnonymous J g).namedIndividuals a) :=
        (nodeKnown _ (mem_namesOf.mp aIn)).1
      simp only [sound, dif_pos known']
      rfl
    · exact absurd isEmpty nonempty
  have keysSat : ∀ item ∈ items.val, IsKey item.axiom → satisfies I item.axiom := by
    intro item mem key
    obtain ⟨e, ops, dps, shape⟩ : ∃ e ops dps, item.axiom = .HasKey e ops dps := by
      revert key; cases item.axiom <;> simp [IsKey]
    obtain ⟨_, _, _, encoded⟩ := keysMeans.1 item mem e ops dps shape
    rw [shape]
    simp only [satisfies]
    intro y y' inE ny inE' ny' sharedOps _
    by_cases empty : names = []
    · rcases ny with ⟨a, aIn, _⟩ | ⟨_, rfl⟩
      · rw [empty] at aIn; simp at aIn
      · rcases ny' with ⟨a, aIn, _⟩ | ⟨_, rfl⟩
        · rw [empty] at aIn; simp at aIn
        · rfl
    · obtain ⟨e', eRun⟩ := encoded empty
      have holdsAt := keysMeans.2.1 (withAnonymous J g) keysHold (fun n nIn => held _ (mem_namesOf.mp nIn)) marks
        item mem e ops dps shape e' eRun
      have classIff : ∀ z, classDenote I e z ↔ classDenote (withAnonymous J g) e' z.1 := by
        obtain ⟨res, run', means⟩ := encode_class_meaning.{u, max v w, u, max w v} context e
        rw [eRun] at run'
        cases Result.ok_injective run'
        exact means e' rfl I (withAnonymous J g) Subtype.val (KnownIn (withAnonymous J g) names) atoms sim
          (fun t h => List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr
            ⟨item, mem, by rw [shape]; exact h⟩)))
          (fun t h => nodeKnown t ((nodesExact t).mpr (key_closure mem shape h)))
      obtain ⟨a, aIn, _, ya⟩ := namedAt empty y ny
      obtain ⟨b, bIn, _, yb⟩ := namedAt empty y' ny'
      apply Subtype.ext
      rw [ya, yb]
      refine holdsAt a aIn b bIn (ya ▸ (classIff y).mp inE) (yb ▸ (classIff y').mp inE') (fun r rIn => ?_)
      obtain ⟨z, nz, ry, ry'⟩ := sharedOps r rIn
      obtain ⟨c, cIn, _, zc⟩ := namedAt empty z nz
      refine ⟨c, cIn, ?_, ?_⟩
      · have := (relation_val o r y z).mp ry
        rw [ya, zc] at this
        exact this
      · have := (relation_val o r y' z).mp ry'
        rw [yb, zc] at this
        exact this
  have satisfied : satisfiesClosure I items.val := by
    intro item mem
    by_cases key : IsKey item.axiom
    · exact keysSat item mem key
    · exact unkeyedSat item (List.mem_filter.mpr ⟨mem, by simpa using key⟩)
  have simQ : Simulates context I J Subtype.val (fun a => ∃ e ∈ questions, a ∈ classIndividuals e) atoms := by
    refine simulates_anonymous N good g frame enough jInterp.1 o sim (fun a ⟨e, mem, inside⟩ => ?_)
    obtain ⟨⟨n, rfl⟩, aIn⟩ := known e mem a inside
    exact sim.individuals _ (nodeKnown _ aIn)
  refine ⟨Element (withAnonymous J g), Values.{v,w} Native,
    ValueEmbedding.ofEmbedding D ⟨embedValue, embedValue_injective⟩, I, Subtype.val,
    ⟨vocab, keyedSound_interpretation (context := context) (J := withAnonymous J g) (N := N) (atoms := atoms)
      (names := names) V jInterp.1 jInterp.2.1 jInterp.2.2.1 jInterp.2.2.2.1 o,
      I.anonymousIndividuals, by rw [withAnonymous_self_eq]; exact satisfied⟩,
    fun y outside => ⟨⟨y, outside⟩, rfl⟩, fun a aIn => ?_, fun e mem e' run z => ?_⟩
  · have known' : ¬ (withAnonymous J g).classes dataClass ((withAnonymous J g).namedIndividuals a) :=
      (nodeKnown _ aIn).1
    refine ⟨known', ?_⟩
    rw [keyedSound_name (mem_namesOf.mpr aIn)]
    simp only [sound, dif_pos known']
    rfl
  · obtain ⟨res, run', means⟩ := encode_class_meaning.{u, max v w, u, max w v} context e
    rw [run] at run'
    cases Result.ok_injective run'
    exact means e' rfl I J Subtype.val _ atoms simQ
      (fun t h => List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, mem, h⟩)) (fun t h => ⟨e, mem, h⟩) z

/-- An OWL model of a closure with keys, for a vocabulary that names the
    closure's named individuals, gives a model of the closure's key encoding
    whose elements that are no data nodes are the OWL model's elements, and at
    which each question whose individuals are not the encoding's holds exactly
    as at those elements. -/
theorem keyed_lifted_model {Object : Type u} {Value : Type (max w v)} {Native : Type w} {D : DatatypeMap Native}
    (N : Normative D) {V : Vocabulary} (vocab : IsVocabulary D V) {context : data_ontology.Context}
    (good : Good context) {items : alloc.vec.Vec AnnotatedAxiom} {nodes : alloc.vec.Vec Individual}
    {counting : Bool} {enc : alloc.vec.Vec AnnotatedAxiom}
    (encRun : key_ontology.encode context items nodes counting = .ok (some enc))
    (nodesExact : ∀ b, b ∈ nodes.val ↔ b ∈ closureIndividuals items.val)
    (vocabNamed : NamesKeyed V items.val) (keyed : Keyed items.val)
    {embed : ValueEmbedding D Value} {I : Interpretation Object Value} (model : Model D embed V I items.val)
    (questions : List ClassExpression) (plain : ∀ e ∈ questions, ∀ a ∈ classIndividuals e, Plain a) :
    ∃ J : Interpretation (Object ⊕ Value) Value, Model D embed V J enc.val ∧
      (∀ z, ¬ J.classes dataClass (.inl z)) ∧
      (∀ a : NamedIndividual, ¬ Reserved a.iri.spelling.val → J.namedIndividuals a = .inl (I.namedIndividuals a)) ∧
      ∀ e ∈ questions, ∀ e', data_ontology.encode_class context e = .ok (some e') →
        ∀ z, classDenote I e z ↔ classDenote J e' (.inl z) := by
  obtain ⟨_, interp, g, sat⟩ := model
  obtain ⟨x0⟩ := I.objectsNonempty
  have interp0 : IsInterpretation D embed V (withAnonymous I g) := interp
  obtain ⟨res, run, facts⟩ := Rowl.KeyEncoding.encode_meaning.{u, max w v, max u w v, max w v} context good items
    nodes counting
  rw [encRun] at run
  cases Result.ok_injective run
  obtain ⟨new0, newU, newK, bits, means0, meansU, _, _, truths, plainNodes, keysMeans, iff⟩ := facts enc rfl
  have placed := liftedN_placed (context := context) N x0 vocab interp0
  have rangeFrame := liftedN_range_frame (context := context) N x0 vocab interp0
  have inert := liftedN_inert (context := context) N x0 interp0
  have frame := liftedN_frame good (lifted_frame N x0 vocab interp0 good truths bits)
  have sat0 : ∀ b ∈ new0, satisfies (liftedN context (withAnonymous I g) (litOf N embed) x0) b.axiom :=
    (means0.1 (withAnonymous I g) _ Sum.inl Plain [] (litOf N embed) _
      (liftedN_simulates N x0 vocab interp0 good []) placed rangeFrame (by simp) (by simp)).2 inert (by simp)
  have satU : ∀ b ∈ newU, satisfies (liftedN context (withAnonymous I g) (litOf N embed) x0) b.axiom :=
    (meansU.1 (withAnonymous I g) _ Sum.inl Plain _ (litOf N embed) _
      (liftedN_simulates N x0 vocab interp0 good ((unkeyedItems items.val).flatMap (fun i => axiomAtoms i.axiom)))
      placed rangeFrame (fun item mem a inside => List.mem_flatMap.mpr ⟨item, mem, inside⟩) meansU.2.1).2 inert
      (fun item mem => sat item (List.mem_filter.mp mem).1)
  have apart : ∀ y, (liftedN context (withAnonymous I g) (litOf N embed) x0).classes keyClass y →
      ¬ (liftedN context (withAnonymous I g) (litOf N embed) x0).classes dataClass y := by
    intro y inN
    rw [liftedN_key] at inN
    cases y with
    | inl z => rw [liftedN_data_class]; exact lifted_element N x0 z
    | inr _ => exact absurd inN id
  have held : ∀ a ∈ nodes.val, NodeHeld (liftedN context (withAnonymous I g) (litOf N embed) x0) a := by
    intro a mem
    cases a with
    | Named n =>
      have plainN : ¬ Reserved n.iri.spelling.val := plainNodes _ mem
      show (liftedN context (withAnonymous I g) (litOf N embed) x0).classes keyClass
        ((liftedN context (withAnonymous I g) (litOf N embed) x0).namedIndividuals n)
      rw [liftedN_key, liftedN_named, lifted_plain_name plainN]
      exact interp.2.2.2.2.2.2.2.2.2.2 n (vocabNamed keyed n ((nodesExact _).mp mem))
    | Anonymous b =>
      show ¬ (liftedN context (withAnonymous I g) (litOf N embed) x0).classes dataClass
        ((liftedN context (withAnonymous I g) (litOf N embed) x0).anonymousIndividuals b)
      rw [liftedN_data_class]
      exact lifted_element N x0 _
  have marks : SharedIn items.val counting → ∀ y,
      (liftedN context (withAnonymous I g) (litOf N embed) x0).classes keyClass y →
      (liftedN context (withAnonymous I g) (litOf N embed) x0).objectProperties markRole y y := by
    intro _ y inN
    rw [liftedN_key] at inN
    exact (liftedN_mark y y).mpr ⟨rfl, marked_of_named _ y inN⟩
  have keysSat : ∀ b ∈ newK, satisfies (liftedN context (withAnonymous I g) (litOf N embed) x0) b.axiom := by
    refine keysMeans.2.2 _ (Marked (withAnonymous I g)) (liftedN_structured _ x0)
      (fun y inN => by rw [liftedN_key] at inN; exact marked_of_named _ y inN)
      (fun n nIn => held _ (mem_namesOf.mp nIn)) (fun item mem e ops dps shape e' eRun => ?_)
    obtain ⟨noData, _, opsIn, _⟩ := keysMeans.1 item mem e ops dps shape
    have keySat := sat item mem
    rw [shape] at keySat
    refine liftedN_key_holds N x0 vocab interp0 good eRun (fun a inside => ?_) opsIn ?_
    · exact plainNodes a ((nodesExact a).mpr (key_closure mem shape inside))
    · intro x y inE nx inE' ny shared
      exact keySat x y inE nx inE' ny shared (by rw [noData]; simp)
  have satJ := (iff (liftedN context (withAnonymous I g) (litOf N embed) x0)).mpr
    ⟨⟨sat0, frame⟩, satU, apart, held, marks, keysSat⟩
  refine ⟨liftedN context I (litOf N embed) x0, ⟨vocab, liftedN_interpretation N x0 interp, Sum.inl ∘ g, ?_⟩,
    fun z => ?_, fun a plainA => ?_, fun e mem e' run z => ?_⟩
  · rw [liftedN_anonymous]
    exact satJ
  · rw [liftedN_data_class]; exact lifted_element N x0 z
  · exact lifted_plain_name plainA
  · exact liftedN_class_iff N x0 vocab interp good run (plain e mem) z

end Models

end Rowl.KeyModels
