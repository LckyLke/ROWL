import Rowl.XmlRefs

/-!
# Entities in the XML reader

The declared general entities as the grammar's environment, their lookup by
name, the stack of entities being expanded and the expansion budget.
-/

namespace Rowl.XmlEntities
open Aeneas Aeneas.Std RowlRust Rowl.XmlGrammar
open Rowl.XmlScan Rowl.XmlRefs
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- The definition an entity declaration gives. -/
def defOf (e : xml.Entity) : Def :=
  match e.kind with
  | .Internal => .internal (word e.text)
  | .External => .external
  | .Unparsed => .unparsed

/-- The declared entities as the grammar's environment. -/
def envView (env : alloc.vec.Vec xml.Entity) : Env := env.val.map (fun e => (word e.«name», defOf e))

/-- A buffer without the code point 0, which no `Char` is. -/
def NoZero (cs : alloc.vec.Vec U32) : Prop := ∀ c ∈ word cs, c ≠ 0

/-- Replacement texts have no 0. -/
def EnvOk (env : alloc.vec.Vec xml.Entity) : Prop := ∀ e ∈ env.val, NoZero e.text

/-- The name of the entity declared at a position. -/
def nameAt (env : alloc.vec.Vec xml.Entity) (k : Nat) : Option Word := (env.val[k]?).map (fun e => word e.«name»)

/-- A position declaring an entity whose name no earlier position declares. -/
def First (env : alloc.vec.Vec xml.Entity) (k : Nat) : Prop :=
  k < env.val.length ∧ ∀ k' < k, nameAt env k' ≠ nameAt env k

/-- The stack of positions being expanded stands for the names being expanded. -/
def StackOk (env : alloc.vec.Vec xml.Entity) (stack : alloc.vec.Vec Usize) (names : List Word) : Prop :=
  (stack.val.map (·.val)).Nodup ∧ (∀ k ∈ stack.val, First env k.val) ∧
    ∀ nm, nm ∈ names ↔ ∃ k ∈ stack.val, nameAt env k.val = some nm

theorem vec_next {α : Type} {v : alloc.vec.Vec α} {k : Usize} (h : k.val < v.val.length) :
    ∃ z : Usize, (k + 1#usize : Result Usize) = Result.ok z ∧ z.val = k.val + 1 :=
  succ_spec (x := k) (y := alloc.vec.Vec.len v) (by rw [alloc.vec.Vec.len_val]; exact h)

theorem envView_length (env : alloc.vec.Vec xml.Entity) : (envView env).length = env.val.length := by
  simp [envView]

/-- `find?` on a mapped list finds the first position with the name. -/
theorem lookup_first (env : alloc.vec.Vec xml.Entity) (w : Word) :
    (lookup (envView env) w = none ↔ ∀ k, nameAt env k ≠ some w) ∧
    (∀ k e, env.val[k]? = some e → word e.«name» = w → (∀ k' < k, nameAt env k' ≠ some w) →
      lookup (envView env) w = some (defOf e)) := by
  unfold lookup envView nameAt
  generalize env.val = l
  induction l with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨ih1, ih2⟩ := ih
    by_cases h : word e.«name» = w
    · refine ⟨?_, ?_⟩
      · simp [List.find?_cons, h]
        exact ⟨0, by simp [h]⟩
      · intro k e' hk he' before
        cases k with
        | zero => simp at hk; subst hk; simp [List.find?_cons, h]
        | succ k => exact absurd (by simp [h]) (before 0 (by omega))
    · refine ⟨?_, ?_⟩
      · simp only [List.map_cons, List.find?_cons, h, decide_false]
        rw [ih1]
        constructor
        · intro all k
          cases k with
          | zero => simp [h]
          | succ k => simpa using all k
        · intro all k; simpa using all (k + 1)
      · intro k e' hk he' before
        cases k with
        | zero => simp at hk; subst hk; exact absurd he' h
        | succ k =>
          simp only [List.map_cons, List.find?_cons, h, decide_false]
          exact ih2 k e' (by simpa using hk) he' (fun k' lt => by simpa using before (k' + 1) (by omega))

theorem find_entity_spec (env : alloc.vec.Vec xml.Entity) (cs : alloc.vec.Vec U32) (start stop : Usize)
    {w rest : Word} (split : (word cs).drop start.val = w ++ rest) (hs : stop.val = start.val + w.length)
    (k : Usize) :
    ∃ r, xml.find_entity env cs start stop k = .ok r ∧
      match r with
      | none => ∀ k', k.val ≤ k' → nameAt env k' ≠ some w
      | some k' => k.val ≤ k'.val ∧ (∃ e, env.val[k'.val]? = some e ∧ word e.«name» = w) ∧
          ∀ k'', k.val ≤ k'' → k'' < k'.val → nameAt env k'' ≠ some w := by
  rw [xml.find_entity]
  by_cases more : k.val < env.val.length
  · have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice xml.Entity) env k =
        .ok env.val[k.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    by_cases found : word env.val[k.val].«name» = w
    · refine ⟨some k, by simp [alloc.vec.Vec.len_val, more, lookup, word_is_eq _ cs start stop split hs, found],
        le_refl _, ⟨_, List.getElem?_eq_getElem more, found⟩, fun k'' lo hi => by omega⟩
    · obtain ⟨k1, hk1, hk1v⟩ := vec_next more
      obtain ⟨r, hr, spec⟩ := find_entity_spec env cs start stop split hs k1
      refine ⟨r, by simp [alloc.vec.Vec.len_val, more, lookup, word_is_eq _ cs start stop split hs, found,
        hk1, hr], ?_⟩
      have here : nameAt env k.val ≠ some w := by
        simp [nameAt, List.getElem?_eq_getElem more, found]
      cases r with
      | none =>
        intro k' lo
        by_cases e : k' = k.val
        · subst e; exact here
        · exact spec k' (by omega)
      | some k' =>
        obtain ⟨lo, hfound, before⟩ := spec
        refine ⟨by omega, hfound, fun k'' lo2 hi2 => ?_⟩
        by_cases e : k'' = k.val
        · subst e; exact here
        · exact before k'' (by omega) hi2
  · refine ⟨none, by simp [alloc.vec.Vec.len_val, more], ?_⟩
    intro k' lo
    simp [nameAt, List.getElem?_eq_none (by omega : env.val.length ≤ k')]
termination_by env.val.length - k.val
decreasing_by omega

theorem on_stack_eq (stack : alloc.vec.Vec Usize) (k i : Usize) :
    xml.on_stack stack k i = .ok (decide (∃ t, i.val ≤ t ∧ ∃ h : t < stack.val.length, stack.val[t] = k)) := by
  rw [xml.on_stack]
  by_cases more : i.val < stack.val.length
  · have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Usize) stack i =
        .ok stack.val[i.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    by_cases here : stack.val[i.val] = k
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_true, lookup, bind_ok, here]
      congr 1
      exact (decide_eq_true ⟨i.val, le_refl _, more, here⟩).symm
    · obtain ⟨i1, hi1, hi1v⟩ := vec_next more
      have rest := on_stack_eq stack k i1
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_true, lookup, bind_ok, here, ite_false,
        hi1, rest]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨t, lo, ht, e⟩; exact ⟨t, by omega, ht, e⟩
      · rintro ⟨t, lo, ht, e⟩
        refine ⟨t, ?_, ht, e⟩
        by_cases eq : t = i.val
        · subst eq; exact absurd e here
        · omega
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ite_false]
    congr 1
    refine (decide_eq_false ?_).symm
    rintro ⟨t, lo, ht, _⟩; omega
termination_by stack.val.length - i.val
decreasing_by omega

theorem on_stack_member (stack : alloc.vec.Vec Usize) (k : Usize) :
    xml.on_stack stack k 0#usize = .ok (decide (k ∈ stack.val)) := by
  rw [on_stack_eq]
  congr 2
  apply propext
  constructor
  · rintro ⟨t, _, ht, e⟩; rw [← e]; exact List.getElem_mem ht
  · intro m
    obtain ⟨t, ht, e⟩ := List.getElem_of_mem m
    exact ⟨t, by simp, ht, e⟩

theorem internal_eq (env : alloc.vec.Vec xml.Entity) (k : Usize) (h : k.val < env.val.length) :
    xml.internal env k = .ok (decide (∃ t, defOf env.val[k.val] = .internal t)) := by
  have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice xml.Entity) env k =
      .ok env.val[k.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
  unfold xml.internal defOf
  simp only [lookup, bind_ok]
  cases env.val[k.val].kind <;> simp

theorem spend_spec (env : alloc.vec.Vec xml.Entity) (k budget origin : Usize) (h : k.val < env.val.length) :
    ∃ r, xml.spend env k budget origin = .ok r ∧
      match r with
      | .Ok b => env.val[k.val].text.val.length < budget.val ∧ b.val = budget.val - env.val[k.val].text.val.length - 1
      | .Err _ => budget.val ≤ env.val[k.val].text.val.length := by
  have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice xml.Entity) env k =
      .ok env.val[k.val] := by
    simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
  unfold xml.spend
  by_cases enough : env.val[k.val].text.val.length < budget.val
  · obtain ⟨d, hd, hdv⟩ := sub_eq (x := budget) (y := alloc.vec.Vec.len env.val[k.val].text) (by
      simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length]; omega)
    obtain ⟨d1, hd1, hd1v⟩ := sub_eq (x := d) (y := 1#usize) (by rw [hdv, alloc.vec.Vec.len_val]; simp; omega)
    refine ⟨.Ok d1, by simp [lookup, UScalar.le_equiv, alloc.vec.Vec.len_val, Nat.not_le.mpr enough, hd, hd1],
      enough, ?_⟩
    rw [hd1v, hdv, alloc.vec.Vec.len_val]; simp
  · refine ⟨.Err ⟨.ResourceLimit, origin⟩, by simp [lookup, UScalar.le_equiv, alloc.vec.Vec.len_val,
      Nat.not_lt.mp enough, xml.fail], Nat.not_lt.mp enough⟩

theorem copy_stack_spec (stack : alloc.vec.Vec Usize) (i : Usize) (out : alloc.vec.Vec Usize)
    (room : out.val.length + (stack.val.length - i.val) ≤ Usize.max) :
    ∃ v, xml.copy_stack stack i out = .ok (.Ok v) ∧ v.val = out.val ++ stack.val.drop i.val := by
  rw [xml.copy_stack]
  by_cases more : i.val < stack.val.length
  · have lookup : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Usize) stack i =
        .ok stack.val[i.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have r1 : out.val.length < Usize.max := by omega
    obtain ⟨o1, ho1, ho1v⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out stack.val[i.val] r1)
    obtain ⟨i1, hi1, hi1v⟩ := vec_next more
    obtain ⟨v, hv, hvv⟩ := copy_stack_spec stack i1 o1 (by rw [ho1v, hi1v]; simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp [alloc.vec.Vec.len_val, more, core.num.Usize.MAX, r1, lookup, ho1, hi1, hv]
    · rw [hvv, ho1v, hi1v, List.drop_eq_getElem_cons more]; simp
  · refine ⟨out, by simp [alloc.vec.Vec.len_val, more], ?_⟩
    simp [List.drop_eq_nil_of_le (by omega : stack.val.length ≤ i.val)]
termination_by stack.val.length - i.val
decreasing_by omega

theorem pushed_spec (stack : alloc.vec.Vec Usize) (k origin : Usize) (room : stack.val.length < Usize.max) :
    ∃ s, xml.pushed stack k origin = .ok (.Ok s) ∧ s.val = stack.val ++ [k] := by
  unfold xml.pushed
  obtain ⟨v, hv, hvv⟩ := copy_stack_spec stack 0#usize (alloc.vec.Vec.new Usize) (by simp)
  have veq : v = stack := by apply alloc.vec.Vec.ext; rw [hvv]; simp
  subst veq
  obtain ⟨s, hs, hsv⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec v k room)
  exact ⟨s, by simp [hv, core.result.Result.Insts.CoreOpsTry.branch, alloc.vec.Vec.len_val,
    core.num.Usize.MAX, room, hs], hsv⟩

/-! ## Expanding a reference -/

theorem nameAt_some {env : alloc.vec.Vec xml.Entity} {k : Nat} {w : Word} (h : nameAt env k = some w) :
    ∃ e, env.val[k]? = some e ∧ word e.«name» = w := by
  unfold nameAt at h
  cases e : env.val[k]? with
  | none => rw [e] at h; simp at h
  | some x => rw [e] at h; simp at h; exact ⟨x, rfl, h⟩

/-- The stack, a list of distinct declaration positions, has room for one more. -/
theorem stack_room {env : alloc.vec.Vec xml.Entity} {stack : alloc.vec.Vec Usize} {names : List Word}
    (h : StackOk env stack names) {k : Nat} (fk : First env k) (notIn : ∀ x ∈ stack.val, x.val ≠ k) :
    stack.val.length < Usize.max := by
  have nd : (k :: stack.val.map (·.val)).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, h.1⟩
    intro m
    obtain ⟨x, hx, e⟩ := List.mem_map.mp m
    exact notIn x hx e
  have all : ∀ x ∈ k :: stack.val.map (·.val), x < env.val.length := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | m
    · exact fk.1
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp m
      exact (h.2.1 y hy).1
  have bound : (k :: stack.val.map (·.val)).length ≤ env.val.length := by
    have sub : (k :: stack.val.map (·.val)) ⊆ List.range env.val.length := by
      intro x hx; exact List.mem_range.mpr (all x hx)
    exact (List.Nodup.subperm nd sub).length_le.trans (by simp)
  have := env.property
  simp at bound
  omega

/-- Expanding a reference to the entity named `w`. -/
theorem expandable_spec (cs : alloc.vec.Vec U32) (start stop : Usize) (env : alloc.vec.Vec xml.Entity)
    (stack : alloc.vec.Vec Usize) (origin : Usize) {names : List Word} (hstack : StackOk env stack names)
    {w rest : Word} (split : (word cs).drop start.val = w ++ rest) (hs : stop.val = start.val + w.length) :
    ∃ r, xml.expandable cs start stop env stack origin = .ok r ∧
      (∀ k, r = .Ok k → ∃ e, env.val[k.val]? = some e ∧ First env k.val ∧ word e.«name» = w ∧
        lookup (envView env) w = some (.internal (word e.text)) ∧ w ∉ names) ∧
      (∀ t, lookup (envView env) w = some (.internal t) → w ∉ names → ∃ k, r = .Ok k) := by
  unfold xml.expandable
  obtain ⟨found, hf, spec⟩ := find_entity_spec env cs start stop split hs 0#usize
  cases found with
  | none =>
    have none_ : lookup (envView env) w = none := (lookup_first env w).1.mpr (fun k => spec k (by simp))
    refine ⟨.Err ⟨.UndeclaredEntity, origin⟩, by simp [hf, xml.fail], by simp, ?_⟩
    intro t h; rw [none_] at h; cases h
  | some k =>
    obtain ⟨_, ⟨e, he, hname⟩, before⟩ := spec
    have inside : k.val < env.val.length := by
      by_contra out; rw [List.getElem?_eq_none (by omega)] at he; cases he
    have ek : env.val[k.val] = e := by rw [List.getElem?_eq_getElem inside] at he; exact Option.some.inj he
    have look : lookup (envView env) w = some (defOf e) :=
      (lookup_first env w).2 k.val e he hname (fun k' lt => before k' (by simp) lt)
    have first : First env k.val := by
      refine ⟨inside, fun k' lt => ?_⟩
      have := before k' (by simp) lt
      rw [show nameAt env k.val = some w by simp [nameAt, he, hname]]
      exact this
    simp only [hf, bind_ok]
    rw [internal_eq env k inside, ek]
    by_cases int : ∃ t, defOf e = .internal t
    · obtain ⟨t, ht⟩ := int
      have tv : t = word e.text := by
        unfold defOf at ht; cases hk : e.kind <;> rw [hk] at ht <;> simp at ht; exact ht.symm
      subst tv
      have intE : ∃ t, defOf e = .internal t := ⟨_, ht⟩
      rw [on_stack_member]
      by_cases onStack : k ∈ stack.val
      · refine ⟨.Err ⟨.RecursiveEntity, origin⟩, by simp [intE, onStack, xml.fail], by simp, ?_⟩
        intro _ _ notIn
        exfalso; apply notIn
        exact (hstack.2.2 w).mpr ⟨k, onStack, by simp [nameAt, he, hname]⟩
      · refine ⟨.Ok k, by simp [intE, onStack], ?_, fun _ _ _ => ⟨k, rfl⟩⟩
        intro k' eq
        simp at eq; subst eq
        refine ⟨e, he, first, hname, by rw [look, ht], ?_⟩
        intro m
        obtain ⟨k'', hk'', hn⟩ := (hstack.2.2 w).mp m
        have fk := (hstack.2.1 k'' hk'')
        -- two first positions with the same name are equal
        have same : k''.val = k.val := by
          by_contra ne
          rcases Nat.lt_or_gt_of_ne ne with lt | gt
          · exact first.2 k''.val lt (by rw [hn]; simp [nameAt, he, hname])
          · exact fk.2 k.val gt (by rw [hn]; simp [nameAt, he, hname])
        apply onStack
        have : k'' = k := UScalar.eq_of_val_eq same
        rw [← this]; exact hk''
    · refine ⟨.Err ⟨.UndeclaredEntity, origin⟩, by simp [int, xml.fail], by simp, ?_⟩
      intro t h _
      rw [look] at h
      exact (int ⟨t, Option.some.inj h⟩).elim

end Rowl.XmlEntities
