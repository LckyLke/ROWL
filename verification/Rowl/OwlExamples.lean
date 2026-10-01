import Rowl.OwlLaws

/- Checked semantic regressions, deliberately independent of the future tableau.
   The empty datatype map is a valid parameter map, not the normative OWL map. -/
namespace Rowl.Owl.Examples
open Aeneas.Std RowlRust.model
attribute [local simp] alloc.vec.Vec.eq_iff

def emptyMap : DatatypeMap Unit where
  supported := fun _ => False
  lexicalSpace := fun _ _ => False
  facetSpace := fun _ _ _ => False
  valueSpace := fun _ _ => False
  lexicalValue := fun _ _ => ()
  facetValue := fun _ _ _ => False
  excludesLiteral := id
  lexicalUtf8 := by simp
  lexicalInSpace := by simp
  facetInSpace := by simp

def vocabulary : Vocabulary where
  classes := fun _ => True
  objectProperties := fun _ => True
  dataProperties := fun _ => True
  individuals := fun _ => True
  datatypes := fun dt => dt = literalDatatype
  literals := fun _ => False
  facets := fun _ => False

def emptyNatMap : DatatypeMap Nat where
  supported := fun _ => False
  lexicalSpace := fun _ _ => False
  facetSpace := fun _ _ _ => False
  valueSpace := fun _ _ => False
  lexicalValue := fun _ _ => 0
  facetValue := fun _ _ _ => False
  excludesLiteral := id
  lexicalUtf8 := by simp
  lexicalInSpace := by simp
  facetInSpace := by simp

/-- An infinite unused carrier does not force an infinite data domain. -/
theorem unused_native_values_do_not_expand_domain :
    ∃ embed : ValueEmbedding emptyNatMap Unit, embed 0 = embed 1 := by
  refine ⟨⟨fun _ => (), ?_⟩, rfl⟩
  intro _ _ hx
  obtain ⟨_, h, _⟩ := hx
  exact False.elim h

def singleton : Interpretation Unit Unit where
  objectsNonempty := inferInstance
  dataNonempty := inferInstance
  classes := fun c _ => c = thing
  objectProperties := fun p _ _ => p = topObject
  dataProperties := fun p _ _ => p = topData
  namedIndividuals := fun _ => ()
  anonymousIndividuals := fun _ => ()
  datatypes := fun dt _ => dt = literalDatatype
  literals := fun _ => ()
  facets := fun _ _ => False
  named := fun _ => True

theorem valid_vocabulary : IsVocabulary emptyMap vocabulary := by
  simp [IsVocabulary, vocabulary, emptyMap]
theorem valid_singleton : IsInterpretation emptyMap (ValueEmbedding.ofEmbedding emptyMap (Function.Embedding.refl Unit)) vocabulary singleton := by
  simp [IsInterpretation, singleton, emptyMap, vocabulary,
    thing, nothing, topObject, bottomObject, topData, bottomData]

def impossible : Class := ⟨⟨alloc.vec.Vec.from [117#u8, 114#u8, 110#u8, 58#u8, 114#u8, 111#u8, 119#u8, 108#u8, 58#u8, 101#u8, 120#u8, 97#u8, 109#u8, 112#u8, 108#u8, 101#u8, 58#u8, 73#u8, 109#u8, 112#u8, 111#u8, 115#u8, 115#u8, 105#u8, 98#u8, 108#u8, 101#u8] (by simp; scalar_tac)⟩⟩
def emptyClassClosure : AxiomClosure :=
  [⟨alloc.vec.Vec.from [] (by simp), .SubClassOf (.Class impossible) (.Class nothing)⟩]

theorem empty_class_ontology_consistent : Consistent.{0,0,0} emptyMap vocabulary emptyClassClosure := by
  refine ⟨Unit, Unit, ValueEmbedding.ofEmbedding emptyMap (Function.Embedding.refl Unit), singleton, valid_vocabulary, valid_singleton, ?_⟩
  apply satisfaction_gives_model
  simp [satisfiesClosure, emptyClassClosure, satisfies, classDenote, singleton, impossible, thing]

theorem asserted_nothing_impossible (I : Interpretation Unit Unit)
    (valid : IsInterpretation emptyMap (ValueEmbedding.ofEmbedding emptyMap (Function.Embedding.refl Unit)) vocabulary I)
    (a : Individual) : ¬ satisfies I (.ClassAssertion (.Class nothing) a) := by
  simp only [satisfies, classDenote]
  exact valid.2.1 _

def alice : NamedIndividual := ⟨⟨alloc.vec.Vec.from [117#u8, 114#u8, 110#u8, 58#u8, 114#u8, 111#u8, 119#u8, 108#u8, 58#u8, 101#u8, 120#u8, 97#u8, 109#u8, 112#u8, 108#u8, 101#u8, 58#u8, 65#u8, 108#u8, 105#u8, 99#u8, 101#u8] (by simp; scalar_tac)⟩⟩
def bob : NamedIndividual := ⟨⟨alloc.vec.Vec.from [117#u8, 114#u8, 110#u8, 58#u8, 114#u8, 111#u8, 119#u8, 108#u8, 58#u8, 101#u8, 120#u8, 97#u8, 109#u8, 112#u8, 108#u8, 101#u8, 58#u8, 66#u8, 111#u8, 98#u8] (by simp; scalar_tac)⟩⟩
theorem distinct_names_can_coincide : alice ≠ bob ∧
    individual singleton (.Named alice) = individual singleton (.Named bob) := by
  constructor
  · intro h
    have := congrArg (fun a : NamedIndividual => a.iri.spelling) h
    simp [alice, bob] at this
  · rfl

def blank : AnonymousIndividual :=
  ⟨alloc.vec.Vec.from [100#u8, 111#u8, 99#u8] (by simp; scalar_tac),
   alloc.vec.Vec.from [120#u8] (by simp; scalar_tac)⟩
def boolean : Interpretation Bool Unit where
  objectsNonempty := inferInstance
  dataNonempty := inferInstance
  classes := fun c x => c = thing ∨ (c ≠ nothing ∧ x = true)
  objectProperties := fun p _ _ => p = topObject
  dataProperties := fun p _ _ => p = topData
  namedIndividuals := fun _ => false
  anonymousIndividuals := fun _ => false
  datatypes := fun dt _ => dt = literalDatatype
  literals := fun _ => ()
  facets := fun _ _ => False
  named := fun _ => False

def anonymousVocabulary : Vocabulary := { vocabulary with
  individuals := fun a => match a with | .Named _ => False | .Anonymous _ => True }
theorem valid_boolean : IsInterpretation emptyMap (ValueEmbedding.ofEmbedding emptyMap (Function.Embedding.refl Unit))
    anonymousVocabulary boolean := by
  simp [IsInterpretation, boolean, emptyMap, anonymousVocabulary, vocabulary,
    thing, nothing, topObject, bottomObject, topData, bottomData]
def blankAssertion : AxiomClosure :=
  [⟨alloc.vec.Vec.from [] (by simp), .ClassAssertion (.Class impossible) (.Anonymous blank)⟩]
theorem anonymous_model_need_not_satisfy :
    modelsClosure boolean blankAssertion ∧ ¬ satisfiesClosure boolean blankAssertion := by
  constructor
  · refine ⟨fun _ => true, ?_⟩
    simp [satisfiesClosure, blankAssertion, satisfies, classDenote, individual, withAnonymous, boolean,
      impossible, nothing]
  · simp [satisfiesClosure, blankAssertion, satisfies, classDenote, individual, boolean, impossible, thing]

theorem unnamed_existential_witness :
    classDenote boolean
      (.ObjectSomeValuesFrom (.Property topObject) (.Class impossible)) false ∧
    ¬ boolean.named true := by
  constructor
  · rw [classDenote]
    refine ⟨true, rfl, ?_⟩
    simp [classDenote, boolean, impossible, nothing]
  · simp [boolean]

end Rowl.Owl.Examples
