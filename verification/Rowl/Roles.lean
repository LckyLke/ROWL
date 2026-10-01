import Rowl.Collection
import Mathlib.Logic.Relation

namespace Rowl.Roles
open Aeneas Aeneas.Std RowlRust.model RowlRust.roles
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
abbrev Key := Iri × Bool
abbrev Edge := Key × Key
abbrev Chain := AtLeastTwo ObjectPropertyExpression × ObjectPropertyExpression

def key (role : Role) : Key := (role.iri,role.inverse)
def inverse (role : Key) : Key := (role.1,!role.2)
def expressionKey : ObjectPropertyExpression → Key
  | .Property p => (p.iri,false)
  | .Inverse p => (p.iri,true)
def roleKeys : Roles → List Key
  | .Empty => []
  | .Entry role next => key role :: roleKeys next
def edgeKeys : Edges → List Edge
  | .Empty => []
  | .Entry sub sup next => (key sub,key sup) :: edgeKeys next
def chainKeys : Chains → List Chain
  | .Empty => []
  | .Entry chain sup next => (chain,sup) :: chainKeys next

noncomputable def Nodes (rows : List Rowl.Collection.Row) : List Key :=
  rows.flatMap (fun row => if row.2 = .ObjectProperty then [(row.1,false),(row.1,true)] else [])
def TopBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,50#u8,47#u8,48#u8,55#u8,47#u8,111#u8,119#u8,108#u8,35#u8,116#u8,111#u8,112#u8,79#u8,98#u8,106#u8,101#u8,99#u8,116#u8,80#u8,114#u8,111#u8,112#u8,101#u8,114#u8,116#u8,121#u8]
def BottomBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,50#u8,47#u8,48#u8,55#u8,47#u8,111#u8,119#u8,108#u8,35#u8,98#u8,111#u8,116#u8,116#u8,111#u8,109#u8,79#u8,98#u8,106#u8,101#u8,99#u8,116#u8,80#u8,114#u8,111#u8,112#u8,101#u8,114#u8,116#u8,121#u8]
def BuiltinComposite (iri : Iri) : Prop := iri.spelling.val = TopBytes ∨ iri.spelling.val = BottomBytes
noncomputable def BuiltinSeeds (rows : List Rowl.Collection.Row) : List Key :=
  rows.flatMap (fun row => if row.2 = .ObjectProperty ∧ BuiltinComposite row.1 then [(row.1,false)] else [])
def Directed (sub sup : Key) : List Edge := [(sub,sup),(inverse sub,inverse sup)]
def Equivalent (left right : Key) : List Edge := Directed left right ++ Directed right left
/-- Every distinct occurrence pair, preserving duplicates in raw input. -/
def Pairs : List Key → List Edge
  | [] => []
  | head::tail => tail.flatMap (Equivalent head) ++ Pairs tail

def PropertyKeys (values : AtLeastTwo ObjectPropertyExpression) : List Key :=
  expressionKey values.first :: expressionKey values.second :: values.rest.val.map expressionKey

private theorem listN_mem_size {α : Type} [SizeOf α]
    (xs : Aeneas.Data.ListN.ListN α n) {x : α} (h : x ∈ xs.toList) : sizeOf x < sizeOf xs := by
  induction xs with
  | nil => simp [Aeneas.Data.ListN.ListN.toList] at h
  | cons head tail ih =>
    simp only [Aeneas.Data.ListN.ListN.toList,List.mem_cons] at h
    rcases h with rfl | h
    · simp +arith
    · have := ih h
      simp only [Data.ListN.ListN.cons.sizeOf_spec]
      omega
private theorem vec_mem_size {α : Type} [SizeOf α] (xs : alloc.vec.Vec α)
    {x : α} (h : x ∈ xs.val) : sizeOf x < sizeOf xs := by
  have := listN_mem_size xs.slice.list h
  cases xs with | mk slice => cases slice; simp_all [alloc.vec.Vec.val,Slice.val]; omega
private theorem first_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.first < sizeOf xs := by
  cases xs; simp +arith
private theorem second_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.second < sizeOf xs := by
  cases xs; simp +arith
private theorem rest_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.rest < sizeOf xs := by
  cases xs; simp +arith

def ClassRequired (expression : ClassExpression) : List Key :=
  match expression with
  | .ObjectIntersectionOf xs | .ObjectUnionOf xs =>
    ClassRequired xs.first ++ ClassRequired xs.second ++ xs.rest.val.attach.flatMap (fun e => ClassRequired e.val)
  | .ObjectComplementOf child | .ObjectSomeValuesFrom _ child | .ObjectAllValuesFrom _ child => ClassRequired child
  | .ObjectHasSelf property => [expressionKey property]
  | .ObjectMinCardinality _ property filler | .ObjectMaxCardinality _ property filler |
      .ObjectExactCardinality _ property filler =>
    expressionKey property :: (match filler with | none => [] | some child => ClassRequired child)
  | _ => []
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest e.property; have := rest_size xs; omega)

def AxiomRequired : Axiom → List Key
  | .SubClassOf a b => ClassRequired a ++ ClassRequired b
  | .EquivalentClasses xs | .DisjointClasses xs | .DisjointUnion _ xs =>
    ClassRequired xs.first ++ ClassRequired xs.second ++ xs.rest.val.flatMap ClassRequired
  | .ObjectPropertyDomain _ ce | .ObjectPropertyRange _ ce | .DataPropertyDomain _ ce |
      .HasKey ce _ _ | .ClassAssertion ce _ => ClassRequired ce
  | .FunctionalObjectProperty p | .InverseFunctionalObjectProperty p | .IrreflexiveObjectProperty p |
      .AsymmetricObjectProperty p => [expressionKey p]
  | .DisjointObjectProperties ps => PropertyKeys ps
  | _ => []
def AxiomEdges : Axiom → List Edge
  | .SubObjectPropertyOf (.Single sub) sup => Directed (expressionKey sub) (expressionKey sup)
  | .EquivalentObjectProperties values => Pairs (PropertyKeys values)
  | .InverseObjectProperties a b => Equivalent (expressionKey a) (inverse (expressionKey b))
  | .SymmetricObjectProperty p => Directed (expressionKey p) (inverse (expressionKey p))
  | _ => []
def AxiomSeeds : Axiom → List Key
  | .SubObjectPropertyOf (.Chain _) sup => [expressionKey sup,inverse (expressionKey sup)]
  | .TransitiveObjectProperty p => [expressionKey p,inverse (expressionKey p)]
  | _ => []
def AxiomChains : Axiom → List Chain
  | .SubObjectPropertyOf (.Chain chain) sup => [(chain,sup)]
  | _ => []

def Correct (item : AnnotatedAxiom) (facts : RoleFacts) : Prop :=
  roleKeys facts.nodes = Nodes (Rowl.Collection.annotatedUses item) ∧
  edgeKeys facts.edges = AxiomEdges item.axiom ∧
  roleKeys facts.composite = BuiltinSeeds (Rowl.Collection.annotatedUses item) ++ AxiomSeeds item.axiom ∧
  roleKeys facts.simple_required = AxiomRequired item.axiom ∧
  chainKeys facts.chains = AxiomChains item.axiom

def ClosureCorrect (items : List AnnotatedAxiom) (facts : RoleFacts) : Prop :=
  roleKeys facts.nodes = items.flatMap (fun item => Nodes (Rowl.Collection.annotatedUses item)) ∧
  edgeKeys facts.edges = items.flatMap (fun item => AxiomEdges item.axiom) ∧
  roleKeys facts.composite = items.flatMap (fun item => BuiltinSeeds (Rowl.Collection.annotatedUses item) ++ AxiomSeeds item.axiom) ∧
  roleKeys facts.simple_required = items.flatMap (fun item => AxiomRequired item.axiom) ∧
  chainKeys facts.chains = items.flatMap (fun item => AxiomChains item.axiom)

private theorem expression_total (expression : ObjectPropertyExpression) :
    expression_role expression = .ok ⟨(expressionKey expression).1,(expressionKey expression).2⟩ := by
  cases expression <;> rfl
private theorem inverse_total (role : Role) : inverse_role role = .ok ⟨(key role).1,!(key role).2⟩ := by
  cases role with | mk iri orientation => cases orientation <;> simp [inverse_role,key]
@[local step] private theorem roles_append_spec (left right : Roles) :
    roles_append left right ⦃ output => roleKeys output = roleKeys left ++ roleKeys right ⦄ := by
  induction left with
  | Empty => simp [roles_append,roleKeys]
  | Entry role next ih =>
    rw [roles_append]
    step as ⟨output,correct⟩
    simp [roleKeys,correct]
@[local step] private theorem edges_append_spec (left right : Edges) :
    edges_append left right ⦃ output => edgeKeys output = edgeKeys left ++ edgeKeys right ⦄ := by
  induction left with
  | Empty => simp [edges_append,edgeKeys]
  | Entry sub sup next ih =>
    rw [edges_append]
    step as ⟨output,correct⟩
    simp [edgeKeys,correct]
@[local step] private theorem chains_append_spec (left right : Chains) :
    chains_append left right ⦃ output => chainKeys output = chainKeys left ++ chainKeys right ⦄ := by
  induction left with
  | Empty => simp [chains_append,chainKeys]
  | Entry chain sup next ih =>
    rw [chains_append]
    step as ⟨output,correct⟩
    simp [chainKeys,correct]
@[local step] private theorem pair_roles_spec (role : Role) :
    pair_roles role ⦃ output => roleKeys output = [key role,inverse (key role)] ⦄ := by
  simp [pair_roles,copy_role,inverse_role,roleKeys,key,inverse]
@[local step] private theorem edge_pair_spec (sub sup : Role) :
    edge_pair sub sup ⦃ output => edgeKeys output = Directed (key sub) (key sup) ⦄ := by
  simp [edge_pair,copy_role,inverse_role,edgeKeys,key,Directed,inverse]
@[local step] private theorem both_edges_spec (left right : Role) :
    both_edges left right ⦃ output => edgeKeys output = Equivalent (key left) (key right) ⦄ := by
  simp only [both_edges,copy_role,bind_ok]
  step as ⟨backward,backwards⟩
  step as ⟨forward,forwards⟩
  step as ⟨output,correct⟩
  simp [correct,forwards,backwards,Equivalent]

private theorem equal_total (key : alloc.vec.Vec U8) (pattern : Slice U8)
    (equalLength : key.val.length = pattern.val.length) (index : Usize) :
    same_pattern_from key pattern index = .ok (decide (key.val.drop index.val = pattern.val.drop index.val)) := by
  rw [same_pattern_from]
  by_cases h : index.val < key.val.length
  · have hr : index.val < pattern.val.length := by omega
    have hkIndex : key.index_usize index = .ok key.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    have hpIndex : pattern.index_usize index = .ok pattern.val[index.val] := by
      simp [Slice.index_usize, List.getElem?_eq_getElem hr]
    by_cases heads : key.val[index.val] = pattern.val[index.val]
    · have size := key.property
      obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have ih := equal_total key pattern equalLength next
      simp [h, hkIndex, hpIndex, heads, hn, ih]
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq, heads, true_and, nextval]
    · simp [h, hkIndex, hpIndex, heads]
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq, heads, false_and, not_false_eq_true]
  · have hk : key.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hp : pattern.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [h, hk, hp]
termination_by key.val.length - index.val
decreasing_by omega

private theorem same_pattern_total (key : alloc.vec.Vec U8) (pattern : Slice U8) :
    same_pattern key pattern = .ok (decide (key.val = pattern.val)) := by
  rw [same_pattern]
  by_cases h : key.val.length = pattern.val.length
  · have ih := equal_total key pattern h 0#usize
    simpa [h] using ih
  · have unequal : key.val ≠ pattern.val := fun eq => h (congrArg List.length eq)
    simp [h, unequal]


private theorem builtin_total (iri : Iri) : builtin_composite iri = .ok (decide (BuiltinComposite iri)) := by
  simp [builtin_composite,same_pattern_total,BuiltinComposite,TopBytes,BottomBytes,Array.to_slice,Array.make,lift]
  split <;> simp_all

@[local step] private theorem nodes_spec (uses : RowlRust.collection.EntityUses) :
    nodes_from uses ⦃ output => roleKeys output = Nodes (Rowl.Collection.rows uses) ⦄ := by
  induction uses with
  | Empty => simp [nodes_from,roleKeys,Nodes,Rowl.Collection.rows]
  | Entry iri kind next ih =>
    rw [nodes_from]
    step as ⟨tail,tailValues⟩
    cases kind <;> simp only [Nodes,Rowl.Collection.rows,List.flatMap_cons] at *
    all_goals try simpa [roleKeys] using tailValues
    step as ⟨pair,pairValues⟩
    step as ⟨output,outputValues⟩
    simp [outputValues,pairValues,tailValues,key,inverse]

@[local step] private theorem composites_spec (uses : RowlRust.collection.EntityUses) :
    composites_from uses ⦃ output => roleKeys output = BuiltinSeeds (Rowl.Collection.rows uses) ⦄ := by
  induction uses with
  | Empty => simp [composites_from,roleKeys,BuiltinSeeds,Rowl.Collection.rows]
  | Entry iri kind next ih =>
    rw [composites_from]
    step as ⟨tail,tailValues⟩
    cases kind <;> simp only [BuiltinSeeds,Rowl.Collection.rows,List.flatMap_cons] at *
    all_goals try simpa [roleKeys] using tailValues
    simp only [builtin_total,bind_ok]
    by_cases composite : BuiltinComposite iri <;> simp [composite,roleKeys,key,tailValues]

@[local step] private theorem property_roles_from_spec (values : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) :
    property_roles_from values index ⦃ output => roleKeys output = (values.val.drop index.val).map expressionKey ⦄ := by
  rw [property_roles_from]
  by_cases inside : index.val < values.val.length
  · have atIndex : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have size := values.property
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have advanced : next.val = index.val+1 := by simpa using nextValue
    simp [UScalar.lt_equiv,alloc.vec.Vec.len_val,inside,↓reduceIte,atIndex,bind_ok,expression_total,advance]
    have ih := property_roles_from_spec values next
    step with ih as ⟨tail,tailValues⟩
    rw [←List.map_drop,List.drop_eq_getElem_cons inside]
    simp only [roleKeys,key,tailValues,advanced,List.map_cons]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [UScalar.lt_equiv,alloc.vec.Vec.len_val,inside,roleKeys,empty]
termination_by values.val.length-index.val
decreasing_by omega

@[local step] private theorem property_roles_spec (values : AtLeastTwo ObjectPropertyExpression) :
    property_roles values ⦃ output => roleKeys output = PropertyKeys values ⦄ := by
  simp only [property_roles,expression_total,bind_ok]
  step as ⟨tail,tailValues⟩
  simp [roleKeys,key,tailValues,PropertyKeys]

@[local step] private theorem equivalent_rest_spec (first : ObjectPropertyExpression)
    (values : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) :
    equivalent_rest first values index ⦃ output =>
      edgeKeys output = ((values.val.drop index.val).map expressionKey).flatMap (Equivalent (expressionKey first)) ⦄ := by
  rw [equivalent_rest]
  by_cases inside : index.val < values.val.length
  · have atIndex : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have size := values.property
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have advanced : next.val = index.val+1 := by simpa using nextValue
    simp [UScalar.lt_equiv,alloc.vec.Vec.len_val,inside,↓reduceIte,expression_total,atIndex,bind_ok]
    step as ⟨edges,edgeValues⟩
    simp only [advance,bind_ok]
    have ih := equivalent_rest_spec first values next
    step with ih as ⟨tail,tailValues⟩
    step as ⟨output,outputValues⟩
    rw [←List.map_drop,List.drop_eq_getElem_cons inside]
    simp only [outputValues,edgeValues,tailValues,key,advanced,List.map_cons,List.flatMap_cons]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [UScalar.lt_equiv,alloc.vec.Vec.len_val,inside,edgeKeys,empty]
termination_by values.val.length-index.val
decreasing_by omega

@[local step] private theorem equivalent_pairs_spec (values : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) :
    equivalent_pairs_from values index ⦃ output => edgeKeys output = Pairs ((values.val.drop index.val).map expressionKey) ⦄ := by
  rw [equivalent_pairs_from]
  by_cases inside : index.val < values.val.length
  · have atIndex : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have size := values.property
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have advanced : next.val = index.val+1 := by simpa using nextValue
    simp [UScalar.lt_equiv,alloc.vec.Vec.len_val,inside,↓reduceIte,atIndex,advance,bind_ok]
    step as ⟨edges,edgeValues⟩
    have ih := equivalent_pairs_spec values next
    step with ih as ⟨tail,tailValues⟩
    step as ⟨output,outputValues⟩
    rw [←List.map_drop,List.drop_eq_getElem_cons inside]
    simp only [outputValues,edgeValues,tailValues,advanced,Pairs,List.map_cons]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [UScalar.lt_equiv,alloc.vec.Vec.len_val,inside,edgeKeys,empty,Pairs]
termination_by values.val.length-index.val
decreasing_by omega

@[local step] private theorem equivalent_edges_spec (values : AtLeastTwo ObjectPropertyExpression) :
    equivalent_edges values ⦃ output => edgeKeys output = Pairs (PropertyKeys values) ⦄ := by
  simp only [equivalent_edges,expression_total,bind_ok]
  step as ⟨firstSecond,firstSecondValues⟩
  step as ⟨firstRest,firstRestValues⟩
  step as ⟨secondRest,secondRestValues⟩
  step as ⟨restPairs,restPairValues⟩
  step as ⟨lastPart,lastValues⟩
  step as ⟨restPart,restValues⟩
  step as ⟨output,outputValues⟩
  simp [outputValues,restValues,lastValues,firstSecondValues,firstRestValues,secondRestValues,restPairValues,
    PropertyKeys,Pairs,key,List.append_assoc]

private theorem classes_spec_of (values : alloc.vec.Vec ClassExpression)
    (child : ∀ item ∈ values.val, class_requirements item ⦃ output => roleKeys output = ClassRequired item ⦄)
    (index : Usize) :
    classes_from values index ⦃ output => roleKeys output = (values.val.drop index.val).flatMap ClassRequired ⦄ := by
  rw [classes_from]
  by_cases inside : index.val < values.val.length
  · have atIndex : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have size := values.property
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have advanced : next.val = index.val+1 := by simpa using nextValue
    simp [UScalar.lt_equiv,alloc.vec.Vec.len_val,inside,↓reduceIte,atIndex,bind_ok]
    step with child values.val[index.val] (List.getElem_mem inside) as ⟨head,headValues⟩
    simp only [advance,bind_ok]
    have ih := classes_spec_of values child next
    step with ih as ⟨tail,tailValues⟩
    step as ⟨output,outputValues⟩
    rw [List.drop_eq_getElem_cons inside]
    simp only [outputValues,headValues,tailValues,advanced,List.flatMap_cons]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [UScalar.lt_equiv,alloc.vec.Vec.len_val,inside,roleKeys,empty]
termination_by values.val.length-index.val
decreasing_by omega

@[local step] private theorem class_spec (expression : ClassExpression) :
    class_requirements expression ⦃ output => roleKeys output = ClassRequired expression ⦄ := by
  cases expression with
  | ObjectIntersectionOf values | ObjectUnionOf values =>
    have first := class_spec values.first
    have second := class_spec values.second
    have rest := classes_spec_of values.rest (fun item _ => class_spec item) 0#usize
    rw [class_requirements]
    step with first as ⟨a,aValues⟩
    step with second as ⟨b,bValues⟩
    step with rest as ⟨c,cValues⟩
    step as ⟨bc,bcValues⟩
    step as ⟨output,outputValues⟩
    simp [outputValues,bcValues,aValues,bValues,cValues,ClassRequired]
  | ObjectComplementOf child | ObjectSomeValuesFrom property child | ObjectAllValuesFrom property child =>
    have ih := class_spec child
    rw [class_requirements]
    simpa [ClassRequired] using ih
  | ObjectHasSelf property => simp [class_requirements,expression_total,roleKeys,key,ClassRequired]
  | ObjectMinCardinality n property filler | ObjectMaxCardinality n property filler | ObjectExactCardinality n property filler =>
    rw [class_requirements]
    simp only [expression_total,bind_ok]
    cases filler with
    | none => simp [optional_class,roleKeys,key,ClassRequired]
    | some child =>
      have ih := class_spec child
      simp only [optional_class]
      step with ih as ⟨output,correct⟩
      simp [roleKeys,key,correct,ClassRequired]
  | _ => simp [class_requirements,roleKeys,ClassRequired]
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := first_size values; omega) | (have := second_size values; omega) |
    (have := vec_mem_size values.rest ‹_ ∈ _›; have := rest_size values; omega)

@[local step] private theorem classes_spec (values : alloc.vec.Vec ClassExpression) (index : Usize) :
    classes_from values index ⦃ output => roleKeys output = (values.val.drop index.val).flatMap ClassRequired ⦄ :=
  classes_spec_of values (fun item _ => class_spec item) index

@[local step] private theorem axiom_requirements_spec (body : Axiom) :
    axiom_requirements body ⦃ output => roleKeys output = AxiomRequired body ⦄ := by
  cases body with
  | SubClassOf a b =>
    simp only [axiom_requirements]
    step as ⟨left,leftValues⟩
    step as ⟨right,rightValues⟩
    step as ⟨output,outputValues⟩
    simp [AxiomRequired,outputValues,leftValues,rightValues]
  | EquivalentClasses values | DisjointClasses values | DisjointUnion cl values =>
    simp only [axiom_requirements]
    step as ⟨a,aValues⟩
    step as ⟨b,bValues⟩
    step as ⟨c,cValues⟩
    step as ⟨bc,bcValues⟩
    step as ⟨output,outputValues⟩
    simp [AxiomRequired,outputValues,bcValues,aValues,bValues,cValues]
  | ObjectPropertyDomain p ce | ObjectPropertyRange p ce | DataPropertyDomain p ce | HasKey ce ps ds | ClassAssertion ce individual =>
    simp only [axiom_requirements,AxiomRequired]
    exact class_spec ce
  | FunctionalObjectProperty p | InverseFunctionalObjectProperty p | IrreflexiveObjectProperty p | AsymmetricObjectProperty p =>
    simp [axiom_requirements,expression_total,roleKeys,key,AxiomRequired]
  | DisjointObjectProperties ps =>
    simp only [axiom_requirements,AxiomRequired]
    exact property_roles_spec ps
  | _ => simp [axiom_requirements,roleKeys,AxiomRequired]

/-- Complete nested occurrence collection for the simple-role restriction. -/
theorem class_requirements_total_correct (expression : ClassExpression) :
    ∃ output, class_requirements expression = .ok output ∧ roleKeys output = ClassRequired expression :=
  WP.spec_imp_exists (class_spec expression)

/-- Source-linked preprocessing of the complete raw axiom, with original IRI
    values and chain order; no caller-supplied numeric role metadata is trusted. -/
theorem axiom_facts_total_correct (item : AnnotatedAxiom) :
    ∃ output, axiom_facts item = .ok output ∧ Correct item output := by
  suffices total : axiom_facts item ⦃ output => Correct item output ⦄ from WP.spec_imp_exists total
  obtain ⟨uses,collected,usesValues⟩ := Rowl.Collection.axiom_entities_total_correct item
  rw [axiom_facts]
  simp only [collected,bind_ok]
  step as ⟨nodes,nodeValues⟩
  step as ⟨builtin,builtinValues⟩
  step as ⟨required,requiredValues⟩
  cases shape : item.axiom with
  | SubObjectPropertyOf sub sup =>
    cases sub with
    | Single sub =>
      simp only [expression_total,bind_ok]
      step as ⟨edges,edgeValues⟩
      simp [Correct,shape,nodeValues,builtinValues,requiredValues,usesValues,
        AxiomEdges,AxiomSeeds,AxiomChains,edgeValues,chainKeys,key]
    | Chain chain =>
      simp only [expression_total,bind_ok]
      step as ⟨pair,pairValues⟩
      step as ⟨seeds,seedValues⟩
      simp [Correct,shape,nodeValues,builtinValues,requiredValues,usesValues,
        AxiomEdges,AxiomSeeds,AxiomChains,edgeKeys,chainKeys,seedValues,pairValues,key]
  | EquivalentObjectProperties values =>
    step as ⟨edges,edgeValues⟩
    simp [Correct,shape,nodeValues,builtinValues,requiredValues,usesValues,
      AxiomEdges,AxiomSeeds,AxiomChains,edgeValues,chainKeys]
  | InverseObjectProperties a b =>
    simp only [expression_total,inverse_role,bind_ok]
    step as ⟨edges,edgeValues⟩
    simp [Correct,shape,nodeValues,builtinValues,requiredValues,usesValues,
      AxiomEdges,AxiomSeeds,AxiomChains,edgeValues,chainKeys,key,inverse]
  | SymmetricObjectProperty property =>
    simp only [expression_total,inverse_role,bind_ok]
    step as ⟨edges,edgeValues⟩
    simp [Correct,shape,nodeValues,builtinValues,requiredValues,usesValues,
      AxiomEdges,AxiomSeeds,AxiomChains,edgeValues,chainKeys,key,inverse]
  | TransitiveObjectProperty property =>
    simp only [expression_total,bind_ok]
    step as ⟨pair,pairValues⟩
    step as ⟨seeds,seedValues⟩
    simp [Correct,shape,nodeValues,builtinValues,requiredValues,usesValues,
      AxiomEdges,AxiomSeeds,AxiomChains,edgeKeys,chainKeys,seedValues,pairValues,key]
  | _ =>
    simp [Correct,shape,nodeValues,builtinValues,requiredValues,usesValues,
      AxiomEdges,AxiomSeeds,AxiomChains,edgeKeys,chainKeys]

@[local step] private theorem append_facts_spec (left right : RoleFacts) :
    append_facts left right ⦃ output =>
      roleKeys output.nodes = roleKeys left.nodes ++ roleKeys right.nodes ∧
      edgeKeys output.edges = edgeKeys left.edges ++ edgeKeys right.edges ∧
      roleKeys output.composite = roleKeys left.composite ++ roleKeys right.composite ∧
      roleKeys output.simple_required = roleKeys left.simple_required ++ roleKeys right.simple_required ∧
      chainKeys output.chains = chainKeys left.chains ++ chainKeys right.chains ⦄ := by
  rw [append_facts]
  step as ⟨nodes,nodesValues⟩
  step as ⟨edges,edgesValues⟩
  step as ⟨composite,compositeValues⟩
  step as ⟨required,requiredValues⟩
  step as ⟨chains,chainsValues⟩
  simp [nodesValues,edgesValues,compositeValues,requiredValues,chainsValues]

private theorem facts_from_total (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    ∃ output, facts_from items index = .ok output ∧ ClosureCorrect (items.val.drop index.val) output := by
  suffices total : facts_from items index ⦃ output => ClosureCorrect (items.val.drop index.val) output ⦄ from
    WP.spec_imp_exists total
  rw [facts_from]
  by_cases inside : index.val < items.val.length
  · have atIndex : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have size := items.property
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have advanced : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨head,readHead,headCorrect⟩ := axiom_facts_total_correct items.val[index.val]
    obtain ⟨tail,readTail,tailCorrect⟩ := facts_from_total items next
    simp [inside,atIndex,readHead,advance,readTail]
    step as ⟨output,nodes,edges,seeds,required,chains⟩
    rw [List.drop_eq_getElem_cons inside]
    obtain ⟨headNodes,headEdges,headSeeds,headRequired,headChains⟩ := headCorrect
    obtain ⟨tailNodes,tailEdges,tailSeeds,tailRequired,tailChains⟩ := tailCorrect
    simp only [ClosureCorrect,List.flatMap_cons,nodes,edges,seeds,required,chains,headNodes,headEdges,headSeeds,headRequired,headChains,
      tailNodes,tailEdges,tailSeeds,tailRequired,tailChains,advanced,and_self,eq_self_iff_true]
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,ClosureCorrect,roleKeys,edgeKeys,chainKeys,empty]
termination_by items.val.length-index.val
decreasing_by omega

/-- Every supplied closure occurrence and every nested constraint is retained
    in deterministic order. This does not certify the remaining DL checks. -/
theorem collect_facts_total_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ output, collect_facts items = .ok output ∧ ClosureCorrect items.val output := by
  simpa [collect_facts] using facts_from_total items 0#usize

/-- Role conversion retains the original IRI value and exact orientation. -/
theorem expression_role_total_correct (expression : ObjectPropertyExpression) :
    ∃ output, expression_role expression = .ok output ∧ key output = expressionKey expression := by
  exact ⟨⟨(expressionKey expression).1,(expressionKey expression).2⟩,expression_total expression,rfl⟩

theorem inverse_role_total_correct (role : Role) :
    ∃ output, inverse_role role = .ok output ∧ key output = inverse (key role) := by
  cases role with
  | mk iri orientation =>
    cases orientation <;> exact ⟨_,rfl,rfl⟩

theorem inverse_role_involutive (role : Role) :
    (do let other ← inverse_role role; inverse_role other) = .ok role := by
  cases role with
  | mk iri orientation => cases orientation <;> simp [inverse_role,key]

/-- Membership in AllOPE is independent of explicit orientation: every typed
    object property occurrence contributes both p and INV(p), and untyped IRI
    references/punned non-property uses do not create role nodes. -/
theorem collect_facts_nodes_iff (items : alloc.vec.Vec AnnotatedAxiom) (facts : RoleFacts)
    (collected : collect_facts items = .ok facts) (iri : Iri) (orientation : Bool) :
    (iri,orientation) ∈ roleKeys facts.nodes ↔
      (iri,RowlRust.typing.EntityKind.ObjectProperty) ∈ items.val.flatMap Rowl.Collection.annotatedUses := by
  obtain ⟨actual,executed,correct⟩ := collect_facts_total_correct items
  have equal := Result.ok_injective (executed.symm.trans collected)
  subst actual
  rw [correct.1]
  cases orientation <;> simp [Nodes,List.mem_flatMap]

/-- The structural property hierarchy; chain operands are deliberately absent. -/
def Hierarchy (items : List AnnotatedAxiom) (sub sup : Key) : Prop :=
  ∃ item ∈ items, (sub,sup) ∈ AxiomEdges item.axiom

def Reachable (items : List AnnotatedAxiom) (sub sup : Key) : Prop :=
  Relation.ReflTransGen (Hierarchy items) sub sup

def Composite (items : List AnnotatedAxiom) (role : Key) : Prop :=
  role ∈ items.flatMap (fun item => BuiltinSeeds (Rowl.Collection.annotatedUses item) ++ AxiomSeeds item.axiom)

def Simple (items : List AnnotatedAxiom) (role : Key) : Prop :=
  ∀ sub, Reachable items sub role → ¬ Composite items sub

def SimpleRestriction (items : List AnnotatedAxiom) : Prop :=
  ∀ role ∈ items.flatMap (fun item => AxiomRequired item.axiom), Simple items role

/-- Exact ordered regularity alternatives, including the top-property exemption
    and the two-endpoint transitivity form. Other chain operands must be strict. -/
def ChainOrdered (order : Key → Key → Prop) (chain : Chain) : Prop :=
  let sup := expressionKey chain.2
  let terms := PropertyKeys chain.1
  (sup.2 = false ∧ sup.1.spelling.val = TopBytes) ∨
  (chain.1.rest.val = [] ∧ expressionKey chain.1.first = sup ∧ expressionKey chain.1.second = sup) ∨
  (∀ role ∈ terms, order role sup) ∨
  (expressionKey chain.1.first = sup ∧ ∀ role ∈ terms.drop 1, order role sup) ∨
  (∃ before, terms = before ++ [sup] ∧ ∀ role ∈ before, order role sup)

noncomputable def AllNodes (items : List AnnotatedAxiom) : List Key :=
  items.flatMap (fun item => Nodes (Rowl.Collection.annotatedUses item))

/-- §11.2's strict-order existence condition on AllOPE. The inverse-source
    equivalence is stated for object-property names exactly as in the text;
    no additional inverse-target invariance is assumed. -/
def Regular (items : List AnnotatedAxiom) : Prop :=
  ∃ order : Key → Key → Prop,
    (∀ sub sup, order sub sup → sub ∈ AllNodes items ∧ sup ∈ AllNodes items) ∧
    (∀ role, ¬ order role role) ∧
    (∀ a b c, order a b → order b c → order a c) ∧
    (∀ left right : Iri, (left,false) ∈ AllNodes items → (right,false) ∈ AllNodes items →
      (order (left,false) (right,false) ↔ order (left,true) (right,false))) ∧
    (∀ sub sup, order sub sup → ¬ Reachable items sup sub) ∧
    (∀ chain ∈ items.flatMap (fun item => AxiomChains item.axiom), ChainOrdered order chain)

private theorem non_simple_iff (items : List AnnotatedAxiom) (role : Key) :
    ¬ Simple items role ↔ ∃ sub, Composite items sub ∧ Reachable items sub role := by
  simp only [Simple,not_forall,Classical.not_imp,not_not]
  constructor
  · rintro ⟨sub,reached,composite⟩; exact ⟨sub,composite,reached⟩
  · rintro ⟨sub,composite,reached⟩; exact ⟨sub,reached,composite⟩

/-- The executable collector's edge set is exactly the independent structural
    hierarchy relation, so later reachability cannot rely on invented edges. -/
theorem collect_facts_hierarchy_iff (items : alloc.vec.Vec AnnotatedAxiom) (facts : RoleFacts)
    (collected : collect_facts items = .ok facts) (sub sup : Key) :
    (sub,sup) ∈ edgeKeys facts.edges ↔ Hierarchy items.val sub sup := by
  obtain ⟨actual,executed,correct⟩ := collect_facts_total_correct items
  have equal := Result.ok_injective (executed.symm.trans collected)
  subst actual
  rw [correct.2.1]
  simp [Hierarchy,List.mem_flatMap]

/-- Composite roots are derived from actual typed raw syntax, not an asserted
    external classification or an assumption about arbitrary role names. -/
theorem collect_facts_composite_iff (items : alloc.vec.Vec AnnotatedAxiom) (facts : RoleFacts)
    (collected : collect_facts items = .ok facts) (role : Key) :
    role ∈ roleKeys facts.composite ↔ Composite items.val role := by
  obtain ⟨actual,executed,correct⟩ := collect_facts_total_correct items
  have equal := Result.ok_injective (executed.symm.trans collected)
  subst actual
  rw [correct.2.2.1]
  rfl

/-- Ordered chain conversion, exposed for the subsequent regularity proof. -/
theorem property_roles_total_correct (values : AtLeastTwo ObjectPropertyExpression) :
    ∃ output, property_roles values = .ok output ∧ roleKeys output = PropertyKeys values := by
  exact WP.spec_imp_exists (property_roles_spec values)

theorem is_top_role_total_correct (role : Role) :
    is_top_role role = .ok (decide ((key role).2 = false ∧ (key role).1.spelling.val = TopBytes)) := by
  cases role with
  | mk iri orientation =>
    cases orientation <;> simp [is_top_role,key,same_pattern_total,TopBytes,Array.to_slice,Array.make,lift]

end Rowl.Roles

