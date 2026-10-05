import Rowl.Longest

/-!
Node tables and the continuation-stack matcher of `compiled`, against an
independent reading of the table. `lang nodes i` is the language of node `i`,
where a part that does not come before its node, and an index outside the
table, read as the empty language. A stack lists the nodes still to match, the
next one last, and stands for the concatenation of their languages from the
last to the first; a state stands for the union of its stacks.

Compiling an expression adds nodes whose root has the expression's language
and keeps every node's flag equal to whether its language has the empty word.
On such a table each matching step replaces the state's language by the words
that remain after the consumed code point, so the matcher returns exactly the
derivative matcher's result, and on a valid suffix the scan returns exactly the
greatest-prefix result, unless a vector runs out of room.
-/
namespace Rowl.Compiled
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.compiled (Kind Node Table)
open Rowl.Regular (Denotes Utf8From)
open scoped Computability
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-! ### Languages of nodes, stacks and states -/

/-- The language a node kind stands for, with its parts read by `part`. -/
def kindLang (part : Nat → Language Nat) : Kind → Language Nat
  | .Empty => 0
  | .Epsilon => 1
  | .Interval lower upper => {w | ∃ c, w = [c] ∧ lower.val ≤ c ∧ c ≤ upper.val}
  | .Alternative a b => part a.val + part b.val
  | .Sequence a b => part a.val * part b.val
  | .Repeat a => (part a.val)∗

/-- The language of node `i`; a part that does not come before its node, and an
    index outside the table, read as the empty language. -/
def lang (nodes : List Node) (i : Nat) : Language Nat :=
  match nodes[i]? with
  | none => 0
  | some n => kindLang (fun j => if _h : j < i then lang nodes j else 0) n.kind
termination_by i

theorem lang_eq (nodes : List Node) (i : Nat) :
    lang nodes i = match nodes[i]? with
      | none => 0
      | some n => kindLang (fun j => if _h : j < i then lang nodes j else 0) n.kind := by
  rw [lang]

theorem lang_none (nodes : List Node) (i : Nat) (outside : nodes.length ≤ i) : lang nodes i = 0 := by
  rw [lang_eq, List.getElem?_eq_none outside]

theorem lang_some (nodes : List Node) (i : Nat) (inside : i < nodes.length) :
    lang nodes i = kindLang (fun j => if _h : j < i then lang nodes j else 0) nodes[i].kind := by
  rw [lang_eq, List.getElem?_eq_getElem inside]

/-- Appending nodes keeps the language of every node already in the table. -/
theorem lang_append (nodes more : List Node) : ∀ i, i < nodes.length → lang (nodes ++ more) i = lang nodes i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro inside
    rw [lang_some (nodes ++ more) i (by simp; omega), lang_some nodes i inside, List.getElem_append_left inside]
    congr 1
    funext j
    by_cases below : j < i
    · rw [dif_pos below, dif_pos below, ih j below (by omega)]
    · rw [dif_neg below, dif_neg below]

/-- Every node's flag says whether its language has the empty word. -/
def Flagged (nodes : List Node) : Prop :=
  ∀ i (inside : i < nodes.length), (nodes[i].nullable = true ↔ [] ∈ lang nodes i)

/-- The concatenation of the languages of a stack's nodes, the last first. -/
def stackLang (nodes : List Node) (stack : List Usize) : Language Nat :=
  (stack.reverse.map (fun j => lang nodes j.val)).prod

/-- The union of the languages of a state's stacks. -/
def stateLang (nodes : List Node) (state : List (alloc.vec.Vec Usize)) : Language Nat :=
  (state.map (fun s => stackLang nodes s.val)).sum

/-- The words that remain after `c` begins a word of `L`. -/
def After (L : Language Nat) (c : Nat) : Language Nat := {u | c :: u ∈ L}

@[simp] theorem mem_after (L : Language Nat) (c : Nat) (u : List Nat) : u ∈ After L c ↔ c :: u ∈ L := Iff.rfl

theorem stackLang_nil (nodes : List Node) : stackLang nodes [] = 1 := by simp [stackLang]

theorem stackLang_push (nodes : List Node) (base : List Usize) (top : Usize) :
    stackLang nodes (base ++ [top]) = lang nodes top.val * stackLang nodes base := by
  simp [stackLang, List.reverse_append]

theorem stackLang_single (nodes : List Node) (top : Usize) : stackLang nodes [top] = lang nodes top.val := by
  simpa [stackLang_nil] using stackLang_push nodes [] top

theorem stateLang_nil (nodes : List Node) : stateLang nodes [] = 0 := by simp [stateLang]

theorem stateLang_push (nodes : List Node) (state : List (alloc.vec.Vec Usize)) (s : alloc.vec.Vec Usize) :
    stateLang nodes (state ++ [s]) = stateLang nodes state + stackLang nodes s.val := by
  simp [stateLang, List.sum_append]

theorem stateLang_cons (nodes : List Node) (s : alloc.vec.Vec Usize) (state : List (alloc.vec.Vec Usize)) :
    stateLang nodes (s :: state) = stackLang nodes s.val + stateLang nodes state := by
  simp [stateLang]

theorem mem_stateLang (nodes : List Node) (state : List (alloc.vec.Vec Usize)) (w : List Nat) :
    w ∈ stateLang nodes state ↔ ∃ s ∈ state, w ∈ stackLang nodes s.val := by
  induction state with
  | nil => simp [stateLang_nil]
  | cons s rest ih =>
    rw [stateLang_cons, Language.mem_add, ih]
    simp

private theorem nil_mul (a b : Language Nat) : [] ∈ a * b ↔ [] ∈ a ∧ [] ∈ b := by
  rw [Language.mem_mul]
  constructor
  · rintro ⟨left, hl, right, hr, eq⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp eq
    exact ⟨hl, hr⟩
  · rintro ⟨ha, hb⟩
    exact ⟨[], ha, [], hb, rfl⟩

private theorem nil_prod (ls : List (Language Nat)) : [] ∈ ls.prod ↔ ∀ l ∈ ls, [] ∈ l := by
  induction ls with
  | nil => simp
  | cons l rest ih => rw [List.prod_cons, nil_mul, ih]; simp

theorem nil_stackLang (nodes : List Node) (stack : List Usize) :
    [] ∈ stackLang nodes stack ↔ ∀ j ∈ stack, [] ∈ lang nodes j.val := by
  rw [stackLang, nil_prod]
  simp

private theorem cons_mul (a b : Language Nat) (cp : Nat) (word : List Nat) :
    cp :: word ∈ a * b ↔
      (∃ left right, word = left ++ right ∧ cp :: left ∈ a ∧ right ∈ b) ∨
      ([] ∈ a ∧ cp :: word ∈ b) := by
  rw [Language.mem_mul]
  constructor
  · rintro ⟨left, hl, right, hr, eq⟩
    cases left with
    | nil => simp only [List.nil_append] at eq; exact Or.inr ⟨hl, eq ▸ hr⟩
    | cons head tail =>
      have heq := List.cons.inj eq
      rcases heq with ⟨rfl, heq⟩
      exact Or.inl ⟨tail, right, heq.symm, hl, hr⟩
  · rintro (⟨left, right, eq, hl, hr⟩ | ⟨hl, hr⟩)
    · exact ⟨cp :: left, hl, right, hr, by simp [eq]⟩
    · exact ⟨[], hl, cp :: word, hr, rfl⟩

private theorem cons_star (a : Language Nat) (cp : Nat) (word : List Nat) :
    cp :: word ∈ a∗ ↔
      ∃ left right, word = left ++ right ∧ cp :: left ∈ a ∧ right ∈ a∗ := by
  constructor
  · rw [Language.mem_kstar_iff_exists_nonempty]
    rintro ⟨chunks, eq, good⟩
    cases chunks with
    | nil => simp at eq
    | cons first rest =>
      obtain ⟨hf, hn⟩ := good first (by simp)
      cases first with
      | nil => exact False.elim (hn rfl)
      | cons head tail =>
        simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at eq
        rcases eq with ⟨rfl, eq⟩
        refine ⟨tail, rest.flatten, eq, hf, ?_⟩
        exact Language.join_mem_kstar (fun w hw => (good w (by simp [hw])).1)
  · rintro ⟨left, right, eq, hl, hr⟩
    obtain ⟨chunks, hword, good⟩ := Language.mem_kstar.mp hr
    apply Language.mem_kstar.mpr
    refine ⟨(cp :: left) :: chunks, ?_, ?_⟩
    · simp [List.flatten_cons, eq, hword]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact hl
      · exact good w hw

theorem after_zero (c : Nat) : After 0 c = 0 := by
  ext u; simp

theorem after_one (c : Nat) : After 1 c = 0 := by
  ext u; simp

theorem after_add (a b : Language Nat) (c : Nat) : After (a + b) c = After a c + After b c := by
  ext u; simp [Language.mem_add]

theorem after_mul (a b : Language Nat) (c : Nat) :
    After (a * b) c = After a c * b + (if [] ∈ a then After b c else 0) := by
  ext u
  rw [mem_after, cons_mul, Language.mem_add, Language.mem_mul]
  by_cases empty : [] ∈ a
  · simp only [empty, if_true, true_and, mem_after]
    constructor
    · rintro (⟨l, r, rfl, hl, hr⟩ | h)
      · exact Or.inl ⟨l, hl, r, hr, rfl⟩
      · exact Or.inr h
    · rintro (⟨l, hl, r, hr, rfl⟩ | h)
      · exact Or.inl ⟨l, r, rfl, hl, hr⟩
      · exact Or.inr h
  · simp only [empty, if_false, false_and, or_false, mem_after]
    constructor
    · rintro ⟨l, r, rfl, hl, hr⟩
      exact Or.inl ⟨l, hl, r, hr, rfl⟩
    · rintro (⟨l, hl, r, hr, rfl⟩ | h)
      · exact ⟨l, r, rfl, hl, hr⟩
      · exact absurd h (Language.notMem_zero _)

theorem after_star (a : Language Nat) (c : Nat) : After (a∗) c = After a c * a∗ := by
  ext u
  rw [mem_after, cons_star, Language.mem_mul]
  constructor
  · rintro ⟨l, r, rfl, hl, hr⟩
    exact ⟨l, hl, r, hr, rfl⟩
  · rintro ⟨l, hl, r, hr, rfl⟩
    exact ⟨l, r, rfl, hl, hr⟩

theorem after_interval (lower upper : U32) (c : Nat) :
    After {w | ∃ c', w = [c'] ∧ lower.val ≤ c' ∧ c' ≤ upper.val} c =
      if lower.val ≤ c ∧ c ≤ upper.val then 1 else 0 := by
  ext u
  by_cases inside : lower.val ≤ c ∧ c ≤ upper.val
  · simp only [inside, and_self, if_true, mem_after, Language.mem_one]
    constructor
    · rintro ⟨c', same, _, _⟩
      exact (List.cons.inj same).2
    · rintro rfl
      exact ⟨c, rfl, inside.1, inside.2⟩
  · simp only [inside, if_false, mem_after]
    constructor
    · rintro ⟨c', same, low, high⟩
      obtain ⟨rfl, -⟩ := List.cons.inj same
      exact absurd ⟨low, high⟩ inside
    · intro member
      exact absurd member (Language.notMem_zero _)

/-! ### Building tables -/

/-- A table grows: nodes are only appended, and a full table stays full. -/
def Grows (t t' : Table) : Prop :=
  (∃ more, t'.nodes.val = t.nodes.val ++ more) ∧ (t.full = true → t'.full = true)

theorem grows_refl (t : Table) : Grows t t := ⟨⟨[], by simp⟩, id⟩

theorem grows_trans {t t' t'' : Table} (first : Grows t t') (second : Grows t' t'') : Grows t t'' := by
  obtain ⟨⟨more, grown⟩, stays⟩ := first
  obtain ⟨⟨more', grown'⟩, stays'⟩ := second
  exact ⟨⟨more ++ more', by rw [grown', grown, List.append_assoc]⟩, fun full => stays' (stays full)⟩

theorem grows_lang {t t' : Table} (grows : Grows t t') (i : Nat) (inside : i < t.nodes.val.length) :
    lang t'.nodes.val i = lang t.nodes.val i := by
  obtain ⟨⟨more, grown⟩, _⟩ := grows
  rw [grown, lang_append _ _ i inside]

theorem grows_length {t t' : Table} (grows : Grows t t') : t.nodes.val.length ≤ t'.nodes.val.length := by
  obtain ⟨⟨more, grown⟩, _⟩ := grows
  rw [grown]; simp

theorem grows_open {t t' : Table} (grows : Grows t t') (open' : t'.full = false) : t.full = false := by
  cases full : t.full
  · rfl
  · rw [grows.2 full] at open'; cases open'

theorem accepts_empty_spec (nodes : alloc.vec.Vec Node) (part : Usize) (flagged : Flagged nodes.val) :
    compiled.accepts_empty nodes part = .ok (decide (part.val < nodes.val.length ∧ [] ∈ lang nodes.val part.val)) := by
  rw [compiled.accepts_empty]
  by_cases inside : part.val < nodes.val.length
  · have lookup : nodes.index_usize part = .ok nodes.val[part.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup, bind_ok, true_and]
    congr 1
    by_cases empty : [] ∈ lang nodes.val part.val
    · simp [empty, (flagged part.val inside).mpr empty]
    · have flag : nodes.val[part.val].nullable = false := by
        cases value : nodes.val[part.val].nullable
        · rfl
        · exact absurd ((flagged part.val inside).mp value) empty
      simp [empty, flag]
  · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside]

/-- The language a part has when read from a table of length `size`. -/
def partOf (nodes : List Node) (size : Nat) (j : Nat) : Language Nat :=
  if j < size then lang nodes j else 0

theorem nullable_of_spec (nodes : alloc.vec.Vec Node) (kind : Kind) (flagged : Flagged nodes.val) :
    compiled.nullable_of nodes kind =
      .ok (decide ([] ∈ kindLang (partOf nodes.val nodes.val.length) kind)) := by
  have part : ∀ j : Usize, [] ∈ partOf nodes.val nodes.val.length j.val ↔
      j.val < nodes.val.length ∧ [] ∈ lang nodes.val j.val := by
    intro j
    by_cases inside : j.val < nodes.val.length
    · simp [partOf, inside]
    · simp [partOf, inside, Language.notMem_zero]
  cases kind with
  | Empty => simp [compiled.nullable_of, kindLang, Language.notMem_zero]
  | Epsilon => simp [compiled.nullable_of, kindLang, Language.mem_one]
  | Interval lower upper => simp [compiled.nullable_of, kindLang]
  | Alternative a b =>
    rw [compiled.nullable_of, accepts_empty_spec _ _ flagged]
    simp only [kindLang, Language.mem_add, part, bind_ok]
    by_cases first : a.val < nodes.val.length ∧ [] ∈ lang nodes.val a.val
    · simp [first]
    · simp only [first, decide_false, Bool.false_eq_true, ↓reduceIte, false_or]
      rw [accepts_empty_spec _ _ flagged]
  | Sequence a b =>
    rw [compiled.nullable_of, accepts_empty_spec _ _ flagged]
    simp only [kindLang, nil_mul, part, bind_ok]
    by_cases first : a.val < nodes.val.length ∧ [] ∈ lang nodes.val a.val
    · simp only [first, decide_true, ↓reduceIte, true_and]
      rw [accepts_empty_spec _ _ flagged]
    · simp [first]
  | Repeat a => simp [compiled.nullable_of, kindLang, Language.nil_mem_kstar]

private theorem lang_append' {pushed : alloc.vec.Vec Node} {nodes : List Node} {extra : Node}
    (contents : pushed.val = nodes ++ [extra]) (i : Nat) (old : i < nodes.length) :
    lang pushed.val i = lang nodes i := by
  rw [contents]; exact lang_append nodes [extra] i old

/-- Adding a node appends it, keeps every flag right, and gives the new node
    the language of its kind with parts read from the table before it. -/
theorem add_spec (t : Table) (kind : Kind) (flagged : Flagged t.nodes.val) :
    ∃ i t', compiled.add t kind = .ok (i, t') ∧ Flagged t'.nodes.val ∧ Grows t t' ∧
      (t'.full = false → i.val = t.nodes.val.length ∧ i.val < t'.nodes.val.length ∧
        lang t'.nodes.val i.val = kindLang (partOf t.nodes.val t.nodes.val.length) kind) := by
  rw [compiled.add]
  by_cases room : t.nodes.val.length < Usize.max
  · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec t.nodes ⟨kind, decide ([] ∈ kindLang (partOf t.nodes.val t.nodes.val.length) kind)⟩ room)
    have position : (alloc.vec.Vec.len t.nodes).val = t.nodes.val.length := alloc.vec.Vec.len_val _
    have newLang : lang pushed.val t.nodes.val.length = kindLang (partOf t.nodes.val t.nodes.val.length) kind := by
      rw [lang_some _ _ (by rw [contents]; simp)]
      simp only [contents, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
      congr 1
      funext j
      unfold partOf
      by_cases below : j < t.nodes.val.length
      · rw [dif_pos below, if_pos below, lang_append _ _ j below]
      · rw [dif_neg below, if_neg below]
    refine ⟨alloc.vec.Vec.len t.nodes, { t with nodes := pushed }, ?_, ?_, ?_, ?_⟩
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, ↓reduceIte,
        nullable_of_spec _ _ flagged, bind_ok, push]
    · intro i inside
      by_cases old : i < t.nodes.val.length
      · have before : pushed.val[i] = t.nodes.val[i] := by
          simp only [contents]; exact List.getElem_append_left old
        simp only
        rw [before, lang_append' contents i old]
        exact flagged i old
      · have last : i = t.nodes.val.length := by
          have : i < t.nodes.val.length + 1 := by simpa [contents] using inside
          omega
        subst last
        simp only
        have atEnd : pushed.val[t.nodes.val.length] =
            ⟨kind, decide ([] ∈ kindLang (partOf t.nodes.val t.nodes.val.length) kind)⟩ := by
          simp [contents]
        rw [atEnd, newLang]
        simp
    · exact ⟨⟨_, contents⟩, fun full => full⟩
    · intro _
      refine ⟨position, ?_, ?_⟩
      · simp [position, contents]
      · rw [position]; exact newLang
  · refine ⟨alloc.vec.Vec.len t.nodes, { t with full := true }, ?_, flagged, ⟨⟨[], by simp⟩, fun _ => rfl⟩, ?_⟩
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, ↓reduceIte]
    · intro opened; cases opened

/-- Compiling an expression adds nodes whose root has the expression's language. -/
theorem compile_spec (e : regular.Expression) : ∀ (t : Table), Flagged t.nodes.val →
    ∃ i t', compiled.compile t e = .ok (i, t') ∧ Flagged t'.nodes.val ∧ Grows t t' ∧
      (t'.full = false → i.val < t'.nodes.val.length ∧ lang t'.nodes.val i.val = Denotes e) := by
  induction e with
  | Empty =>
    intro t flagged
    obtain ⟨i, t', run, flagged', grows, spec⟩ := add_spec t .Empty flagged
    refine ⟨i, t', by rw [compiled.compile]; exact run, flagged', grows, ?_⟩
    intro opened
    obtain ⟨_, inside, value⟩ := spec opened
    exact ⟨inside, by rw [value]; rfl⟩
  | Epsilon =>
    intro t flagged
    obtain ⟨i, t', run, flagged', grows, spec⟩ := add_spec t .Epsilon flagged
    refine ⟨i, t', by rw [compiled.compile]; exact run, flagged', grows, ?_⟩
    intro opened
    obtain ⟨_, inside, value⟩ := spec opened
    exact ⟨inside, by rw [value]; rfl⟩
  | Interval lower upper =>
    intro t flagged
    obtain ⟨i, t', run, flagged', grows, spec⟩ := add_spec t (.Interval lower upper) flagged
    refine ⟨i, t', by rw [compiled.compile]; exact run, flagged', grows, ?_⟩
    intro opened
    obtain ⟨_, inside, value⟩ := spec opened
    exact ⟨inside, by rw [value]; rfl⟩
  | Alternative left right ihl ihr =>
    intro t flagged
    obtain ⟨a, t1, run1, flagged1, grows1, spec1⟩ := ihl t flagged
    obtain ⟨b, t2, run2, flagged2, grows2, spec2⟩ := ihr t1 flagged1
    obtain ⟨i, t3, run3, flagged3, grows3, spec3⟩ := add_spec t2 (.Alternative a b) flagged2
    refine ⟨i, t3, by rw [compiled.compile]; simp [run1, run2, run3], flagged3,
      grows_trans grows1 (grows_trans grows2 grows3), ?_⟩
    intro opened
    have open2 := grows_open grows3 opened
    have open1 := grows_open grows2 open2
    obtain ⟨insideA, langA⟩ := spec1 open1
    obtain ⟨insideB, langB⟩ := spec2 open2
    obtain ⟨_, inside, value⟩ := spec3 opened
    have aIn : a.val < t2.nodes.val.length := lt_of_lt_of_le insideA (grows_length grows2)
    refine ⟨inside, ?_⟩
    rw [value]
    simp only [kindLang, partOf, if_pos aIn, if_pos insideB, Denotes]
    rw [grows_lang grows2 a.val insideA, langA, langB]
  | Sequence left right ihl ihr =>
    intro t flagged
    obtain ⟨a, t1, run1, flagged1, grows1, spec1⟩ := ihl t flagged
    obtain ⟨b, t2, run2, flagged2, grows2, spec2⟩ := ihr t1 flagged1
    obtain ⟨i, t3, run3, flagged3, grows3, spec3⟩ := add_spec t2 (.Sequence a b) flagged2
    refine ⟨i, t3, by rw [compiled.compile]; simp [run1, run2, run3], flagged3,
      grows_trans grows1 (grows_trans grows2 grows3), ?_⟩
    intro opened
    have open2 := grows_open grows3 opened
    have open1 := grows_open grows2 open2
    obtain ⟨insideA, langA⟩ := spec1 open1
    obtain ⟨insideB, langB⟩ := spec2 open2
    obtain ⟨_, inside, value⟩ := spec3 opened
    have aIn : a.val < t2.nodes.val.length := lt_of_lt_of_le insideA (grows_length grows2)
    refine ⟨inside, ?_⟩
    rw [value]
    simp only [kindLang, partOf, if_pos aIn, if_pos insideB, Denotes]
    rw [grows_lang grows2 a.val insideA, langA, langB]
  | Repeat inner ih =>
    intro t flagged
    obtain ⟨a, t1, run1, flagged1, grows1, spec1⟩ := ih t flagged
    obtain ⟨i, t2, run2, flagged2, grows2, spec2⟩ := add_spec t1 (.Repeat a) flagged1
    refine ⟨i, t2, by rw [compiled.compile]; simp [run1, run2], flagged2, grows_trans grows1 grows2, ?_⟩
    intro opened
    have open1 := grows_open grows2 opened
    obtain ⟨insideA, langA⟩ := spec1 open1
    obtain ⟨_, inside, value⟩ := spec2 opened
    refine ⟨inside, ?_⟩
    rw [value]
    simp only [kindLang, partOf, if_pos insideA, Denotes]
    rw [langA]

/-! ### Stacks -/

theorem copy_from_spec (stack : alloc.vec.Vec Usize) (finish : Usize) (bound : finish.val ≤ stack.val.length)
    (index : Usize) (out : alloc.vec.Vec Usize) (copied : out.val = stack.val.take index.val)
    (below : index.val ≤ finish.val) :
    ∃ r, compiled.copy_from stack index finish out = .ok r ∧ r.val = stack.val.take finish.val := by
  rw [compiled.copy_from]
  by_cases more : index.val < finish.val
  · have inside : index.val < stack.val.length := by omega
    have lookup : stack.index_usize index = .ok stack.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have room : out.val.length < Usize.max := by
      rw [copied]; simp; have := stack.property; omega
    obtain ⟨appended, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out stack.val[index.val] room)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, run, value⟩ := copy_from_spec stack finish bound next appended
      (by rw [contents, copied, nextIndex, List.take_succ_eq_append_getElem inside]) (by omega)
    refine ⟨r, ?_, value⟩
    simp only [UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.len_val, inside, usize_max_val, room,
      alloc.vec.Vec.index_slice_index, lookup, bind_ok, push, advance, run]
  · have same : index.val = finish.val := by omega
    refine ⟨out, by simp [UScalar.lt_equiv, more], by rw [copied, same]⟩
termination_by finish.val - index.val
decreasing_by omega

theorem copy_all (stack : alloc.vec.Vec Usize) :
    ∃ r, compiled.copy_from stack 0#usize (alloc.vec.Vec.len stack) (alloc.vec.Vec.new Usize) = .ok r ∧
      r.val = stack.val := by
  obtain ⟨r, run, value⟩ := copy_from_spec stack (alloc.vec.Vec.len stack) (by simp) 0#usize
    (alloc.vec.Vec.new Usize) (by simp) (by simp)
  exact ⟨r, run, by rw [value]; simp⟩

theorem above_spec (base : alloc.vec.Vec Usize) (top : Usize) :
    ∃ r, compiled.above base top = .ok r ∧ ∀ s, r = some s → s.val = base.val ++ [top] := by
  obtain ⟨copy, run, value⟩ := copy_all base
  rw [compiled.above, run, bind_ok]
  by_cases room : copy.val.length < Usize.max
  · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec copy top room)
    refine ⟨some pushed, ?_, ?_⟩
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, ↓reduceIte, push, bind_ok]
    · intro s same
      cases same
      rw [contents, value]
  · exact ⟨none, by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room], by simp⟩


private theorem drop_cons_eq {α : Type} (l : List α) (i : Nat) (inside : i < l.length) :
    l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons inside

theorem same_from_spec (left right : alloc.vec.Vec Usize) (equal : left.val.length = right.val.length)
    (index : Usize) : compiled.same_from left right index =
      .ok (decide (left.val.drop index.val = right.val.drop index.val)) := by
  rw [compiled.same_from]
  by_cases more : index.val < left.val.length
  · have moreRight : index.val < right.val.length := by omega
    have lookupLeft : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have lookupRight : right.index_usize index = .ok right.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem moreRight]
    have split : left.val.drop index.val = right.val.drop index.val ↔
        left.val[index.val] = right.val[index.val] ∧
          left.val.drop (index.val + 1) = right.val.drop (index.val + 1) := by
      rw [drop_cons_eq _ _ more, drop_cons_eq _ _ moreRight, List.cons.injEq]
    by_cases head : left.val[index.val] = right.val[index.val]
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have rest := same_from_spec left right equal next
      rw [nextIndex] at rest
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, moreRight, ↓reduceIte,
        alloc.vec.Vec.index_slice_index, lookupLeft, lookupRight, bind_ok, head, advance, rest]
      simp only [split, head, true_and]
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, moreRight, ↓reduceIte,
        alloc.vec.Vec.index_slice_index, lookupLeft, lookupRight, bind_ok, head]
      simp only [split, head, false_and, decide_false]
  · have emptyLeft : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have emptyRight : right.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, emptyLeft, emptyRight]
termination_by left.val.length - index.val
decreasing_by omega

theorem same_spec (left right : alloc.vec.Vec Usize) :
    compiled.same left right = .ok (decide (left.val = right.val)) := by
  rw [compiled.same]
  by_cases equal : left.val.length = right.val.length
  · have lengths : alloc.vec.Vec.len left = alloc.vec.Vec.len right :=
      UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len_val, equal])
    simp only [lengths, ↓reduceIte, same_from_spec left right equal, show (0#usize).val = 0 from rfl,
      List.drop_zero]
  · have lengths : alloc.vec.Vec.len left ≠ alloc.vec.Vec.len right := by
      intro same; exact equal (by simpa [alloc.vec.Vec.len_val] using congrArg UScalar.val same)
    have different : left.val ≠ right.val := fun same => equal (by rw [same])
    simp only [lengths, ↓reduceIte, different, decide_false]

theorem listed_spec (states : alloc.vec.Vec (alloc.vec.Vec Usize)) (stack : alloc.vec.Vec Usize)
    (index : Usize) : compiled.listed states stack index =
      .ok (decide (∃ s ∈ states.val.drop index.val, s.val = stack.val)) := by
  rw [compiled.listed]
  by_cases more : index.val < states.val.length
  · have lookup : states.index_usize index = .ok states.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split : (∃ s ∈ states.val.drop index.val, s.val = stack.val) ↔
        states.val[index.val].val = stack.val ∨ ∃ s ∈ states.val.drop (index.val + 1), s.val = stack.val := by
      rw [drop_cons_eq _ _ more]
      constructor
      · rintro ⟨s, member, same⟩
        rcases List.mem_cons.mp member with rfl | later
        · exact Or.inl same
        · exact Or.inr ⟨s, later, same⟩
      · rintro (same | ⟨s, member, same⟩)
        · exact ⟨_, List.mem_cons_self .., same⟩
        · exact ⟨s, List.mem_cons_of_mem _ member, same⟩
    by_cases here : states.val[index.val].val = stack.val
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        lookup, bind_ok, same_spec, here, decide_true]
      simp only [split, here, true_or, decide_true]
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have rest := listed_spec states stack next
      rw [nextIndex] at rest
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        lookup, bind_ok, same_spec, here, decide_false, Bool.false_eq_true, advance, rest]
      simp only [split, here, false_or]
  · have empty : states.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, empty]
termination_by states.val.length - index.val
decreasing_by omega

/-- Inserting a stack adds its language to the state's, unless there is no room. -/
theorem insert_spec (nodes : List Node) (out : alloc.vec.Vec (alloc.vec.Vec Usize)) (stack : alloc.vec.Vec Usize) :
    ∃ r, compiled.insert out stack = .ok r ∧
      (r.1 = true → stateLang nodes r.2.val = stateLang nodes out.val + stackLang nodes stack.val) := by
  rw [compiled.insert, listed_spec]
  simp only [show (0#usize).val = 0 from rfl, List.drop_zero]
  by_cases found : ∃ s ∈ out.val, s.val = stack.val
  · refine ⟨(true, out), by simp [found], ?_⟩
    intro _
    obtain ⟨s, member, same⟩ := found
    ext w
    rw [Language.mem_add]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | h)
      · exact h
      · rw [mem_stateLang]
        exact ⟨s, member, by rw [same]; exact h⟩
  · simp only [found, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases room : out.val.length < Usize.max
    · obtain ⟨copy, run, value⟩ := copy_all stack
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out copy room)
      refine ⟨(true, pushed), ?_, ?_⟩
      · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, run, push]
      · intro _
        rw [contents, stateLang_push, value]
    · exact ⟨(false, out), by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room], by simp⟩

/-! ### Matching steps -/

/-- The language of a part read inside node `index`. -/
private theorem part_lang (nodes : List Node) (index : Nat) (j : Usize) :
    (if _h : j.val < index then lang nodes j.val else 0) = (if j.val < index then lang nodes j.val else 0) := by
  by_cases below : j.val < index <;> simp [below]

/-- Deriving node `index` on top of `base` adds the words that remain after the
    code point to the state, unless there is no room. -/
theorem derive_spec (nodes : alloc.vec.Vec Node) (flagged : Flagged nodes.val) (c : U32) :
    ∀ (n : Nat) (index : Usize) (base : alloc.vec.Vec Usize) (out : alloc.vec.Vec (alloc.vec.Vec Usize)),
      index.val = n →
      ∃ r, compiled.derive nodes index base c out = .ok r ∧
        (r.1 = true → stateLang nodes.val r.2.val =
          stateLang nodes.val out.val + After (lang nodes.val index.val) c.val * stackLang nodes.val base.val) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro index base out same
    subst same
    rw [compiled.derive]
    by_cases inside : index.val < nodes.val.length
    · have lookup : nodes.index_usize index = .ok nodes.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      rw [lang_some nodes.val index.val inside]
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, UScalar.le_equiv, inside, ↓reduceIte,
        alloc.vec.Vec.index_slice_index, lookup, bind_ok]
      cases kind : nodes.val[index.val].kind with
      | Empty =>
        refine ⟨(true, out), rfl, ?_⟩
        intro _
        simp only [kindLang, after_zero, zero_mul, add_zero]
      | Epsilon =>
        refine ⟨(true, out), rfl, ?_⟩
        intro _
        simp only [kindLang, after_one, zero_mul, add_zero]
      | Interval lower upper =>
        simp only [kindLang, after_interval]
        by_cases range : lower.val ≤ c.val ∧ c.val ≤ upper.val
        · obtain ⟨r, run, spec⟩ := insert_spec nodes.val out base
          refine ⟨r, by simp only [range.1, range.2, ↓reduceIte]; exact run, ?_⟩
          intro done
          rw [spec done, if_pos range, one_mul]
        · refine ⟨(true, out), ?_, ?_⟩
          · by_cases low : lower.val ≤ c.val
            · have high : ¬ c.val ≤ upper.val := fun high => range ⟨low, high⟩
              simp only [low, high, ↓reduceIte]
            · simp only [low, ↓reduceIte]
          · intro _
            rw [if_neg range, zero_mul, add_zero]
      | Alternative a b =>
        simp only [kindLang, after_add, add_mul]
        by_cases first : a.val < index.val
        · obtain ⟨r, run, spec⟩ := ih a.val first a base out rfl
          obtain ⟨done, out1⟩ := r
          cases done with
          | false =>
            refine ⟨(false, out1), ?_, by simp⟩
            simp [first, run]
          | true =>
            have state1 := spec rfl
            by_cases second : b.val < index.val
            · obtain ⟨r2, run2, spec2⟩ := ih b.val second b base out1 rfl
              refine ⟨r2, ?_, ?_⟩
              · simp [first, second, run, run2]
              · intro done
                rw [spec2 done, state1, dif_pos first, dif_pos second, add_assoc]
            · refine ⟨(true, out1), ?_, ?_⟩
              · simp [first, second, run]
              · intro _
                rw [state1, dif_pos first, dif_neg second, after_zero, zero_mul, add_zero]
        · by_cases second : b.val < index.val
          · obtain ⟨r2, run2, spec2⟩ := ih b.val second b base out rfl
            refine ⟨r2, ?_, ?_⟩
            · simp [first, second, run2]
            · intro done
              rw [spec2 done, dif_neg first, dif_pos second, after_zero, zero_mul, zero_add]
          · refine ⟨(true, out), ?_, ?_⟩
            · simp [first, second]
            · intro _
              rw [dif_neg first, dif_neg second, after_zero, zero_mul, add_zero, add_zero]
      | Sequence a b =>
        simp only [kindLang]
        by_cases both : a.val < index.val ∧ b.val < index.val
        · rw [dif_pos both.1, dif_pos both.2]
          obtain ⟨o, aboveRun, aboveSpec⟩ := above_spec base b
          cases o with
          | none =>
            refine ⟨(false, out), ?_, by simp⟩
            simp [both.1, both.2, aboveRun]
          | some stack =>
            have stackValue := aboveSpec stack rfl
            obtain ⟨r, run, spec⟩ := ih a.val both.1 a stack out rfl
            obtain ⟨done, out1⟩ := r
            cases done with
            | false =>
              refine ⟨(false, out1), ?_, by simp⟩
              simp [both.1, both.2, aboveRun, run]
            | true =>
              have state1 := spec rfl
              have aIn : a.val < nodes.val.length := by omega
              have lookupA : nodes.index_usize a = .ok nodes.val[a.val] := by
                simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem aIn]
              rw [stackValue, stackLang_push] at state1
              rw [after_mul, add_mul]
              by_cases empty : [] ∈ lang nodes.val a.val
              · have flag : nodes.val[a.val].nullable = true := (flagged a.val aIn).mpr empty
                obtain ⟨r2, run2, spec2⟩ := ih b.val both.2 b base out1 rfl
                refine ⟨r2, ?_, ?_⟩
                · simp [both.1, both.2, aboveRun, run, lookupA, flag, run2]
                · intro done
                  rw [spec2 done, state1, if_pos empty, mul_assoc, add_assoc]
              · have flag : nodes.val[a.val].nullable = false := by
                  cases value : nodes.val[a.val].nullable
                  · rfl
                  · exact absurd ((flagged a.val aIn).mp value) empty
                refine ⟨(true, out1), ?_, ?_⟩
                · simp [both.1, both.2, aboveRun, run, lookupA, flag]
                · intro _
                  rw [state1, if_neg empty, mul_assoc, zero_mul, add_zero]
        · refine ⟨(true, out), ?_, ?_⟩
          · by_cases aBelow : a.val < index.val
            · have bBelow : ¬ b.val < index.val := fun h => both ⟨aBelow, h⟩
              simp only [aBelow, bBelow, ↓reduceIte]
            · simp only [aBelow, ↓reduceIte]
          · intro _
            have zero : (if _h : a.val < index.val then lang nodes.val a.val else 0) *
                (if _h : b.val < index.val then lang nodes.val b.val else 0) = 0 := by
              by_cases aBelow : a.val < index.val
              · have bBelow : ¬ b.val < index.val := fun h => both ⟨aBelow, h⟩
                rw [dif_neg bBelow, mul_zero]
              · rw [dif_neg aBelow, zero_mul]
            rw [zero, after_zero, zero_mul, add_zero]
      | Repeat body =>
        simp only [kindLang]
        by_cases below : body.val < index.val
        · rw [dif_pos below]
          obtain ⟨o, aboveRun, aboveSpec⟩ := above_spec base index
          cases o with
          | none =>
            refine ⟨(false, out), ?_, by simp⟩
            simp [below, aboveRun]
          | some stack =>
            have stackValue := aboveSpec stack rfl
            obtain ⟨r, run, spec⟩ := ih body.val below body stack out rfl
            refine ⟨r, ?_, ?_⟩
            · simp [below, aboveRun, run]
            · intro done
              rw [spec done, stackValue, stackLang_push, lang_some nodes.val index.val inside, kind]
              simp only [kindLang, dif_pos below]
              rw [after_star, mul_assoc]
        · rw [dif_neg below]
          refine ⟨(true, out), ?_, ?_⟩
          · simp only [below, ↓reduceIte]
          · intro _
            have one : (0 : Language Nat)∗ = 1 := by
              ext w
              rw [Language.mem_kstar, Language.mem_one]
              constructor
              · rintro ⟨chunks, rfl, good⟩
                cases chunks with
                | nil => rfl
                | cons first rest => exact absurd (good first (by simp)) (Language.notMem_zero _)
              · rintro rfl
                exact ⟨[], rfl, by simp⟩
            rw [one, after_one, zero_mul, add_zero]
    · refine ⟨(true, out), by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside], ?_⟩
      intro _
      rw [lang_none _ _ (by omega), after_zero, zero_mul, add_zero]

theorem derive_stack_spec (nodes : alloc.vec.Vec Node) (flagged : Flagged nodes.val) (c : U32)
    (stack : alloc.vec.Vec Usize) (length : Usize) (out : alloc.vec.Vec (alloc.vec.Vec Usize))
    (bound : length.val ≤ stack.val.length) :
    ∃ r, compiled.derive_stack nodes stack length c out = .ok r ∧
      (r.1 = true → stateLang nodes.val r.2.val =
        stateLang nodes.val out.val + After (stackLang nodes.val (stack.val.take length.val)) c.val) := by
  rw [compiled.derive_stack]
  by_cases positive : 0 < length.val
  · obtain ⟨previous, back, previousValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := length) (y := 1#usize) (by scalar_tac))
    have previousIndex : previous.val = length.val - 1 := by simp at previousValue; omega
    have topIn : previous.val < stack.val.length := by omega
    have lookup : stack.index_usize previous = .ok stack.val[previous.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem topIn]
    obtain ⟨base, copyRun, baseValue⟩ := copy_from_spec stack previous (by omega) 0#usize
      (alloc.vec.Vec.new Usize) (by simp) (by simp)
    have split : stack.val.take length.val = base.val ++ [stack.val[previous.val]] := by
      rw [baseValue, show length.val = previous.val + 1 by omega, List.take_succ_eq_append_getElem topIn]
    obtain ⟨r, run, spec⟩ := derive_spec nodes flagged c _ stack.val[previous.val] base out rfl
    obtain ⟨done, out1⟩ := r
    have positiveU : (0#usize).val < length.val := by simpa using positive
    have nonzero : ¬ length.val = 0 := by omega
    cases done with
    | false =>
      refine ⟨(false, out1), ?_, by simp⟩
      simp [UScalar.lt_equiv, UScalar.le_equiv, alloc.vec.Vec.len_val, positiveU, nonzero, bound, back, lookup,
        copyRun, run]
    | true =>
      have state1 := spec rfl
      rw [split, stackLang_push, after_mul]
      by_cases empty : stack.val[previous.val].val < nodes.val.length ∧
          [] ∈ lang nodes.val stack.val[previous.val].val
      · obtain ⟨r2, run2, spec2⟩ := derive_stack_spec nodes flagged c stack previous out1 (by omega)
        refine ⟨r2, ?_, ?_⟩
        · simp [UScalar.lt_equiv, UScalar.le_equiv, alloc.vec.Vec.len_val, positiveU, nonzero, bound,
            back, lookup, copyRun, run, accepts_empty_spec _ _ flagged, empty, run2]
        · intro done
          rw [spec2 done, state1, ← baseValue, if_pos empty.2, add_assoc]
      · refine ⟨(true, out1), ?_, ?_⟩
        · simp [UScalar.lt_equiv, UScalar.le_equiv, alloc.vec.Vec.len_val, positiveU, nonzero, bound,
            back, lookup, copyRun, run, accepts_empty_spec _ _ flagged, empty]
        · intro _
          have notEmpty : ¬ [] ∈ lang nodes.val stack.val[previous.val].val := by
            intro member
            by_cases topInside : stack.val[previous.val].val < nodes.val.length
            · exact empty ⟨topInside, member⟩
            · rw [lang_none _ _ (by omega)] at member; exact Language.notMem_zero _ member
          rw [state1, if_neg notEmpty, add_zero]
  · have zero : length.val = 0 := by omega
    have positiveU : ¬ (0#usize).val < length.val := by simpa using positive
    refine ⟨(true, out), by simp only [UScalar.lt_equiv, positiveU, ↓reduceIte], ?_⟩
    intro _
    rw [zero, List.take_zero, stackLang_nil, after_one, add_zero]
termination_by length.val
decreasing_by omega

theorem step_spec (nodes : alloc.vec.Vec Node) (flagged : Flagged nodes.val) (c : U32)
    (state : alloc.vec.Vec (alloc.vec.Vec Usize)) (index : Usize) (out : alloc.vec.Vec (alloc.vec.Vec Usize)) :
    ∃ r, compiled.step nodes state index c out = .ok r ∧
      (r.1 = true → stateLang nodes.val r.2.val =
        stateLang nodes.val out.val + After (stateLang nodes.val (state.val.drop index.val)) c.val) := by
  rw [compiled.step]
  by_cases more : index.val < state.val.length
  · have lookup : state.index_usize index = .ok state.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨r, run, spec⟩ := derive_stack_spec nodes flagged c state.val[index.val]
      (alloc.vec.Vec.len state.val[index.val]) out (by simp [alloc.vec.Vec.len_val])
    obtain ⟨done, out1⟩ := r
    cases done with
    | false =>
      refine ⟨(false, out1), ?_, by simp⟩
      simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, run]
    | true =>
      have state1 := spec rfl
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r2, run2, spec2⟩ := step_spec nodes flagged c state next out1
      refine ⟨r2, ?_, ?_⟩
      · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, lookup, run, advance, run2]
      · intro done
        rw [spec2 done, state1, nextIndex, drop_cons_eq _ _ more, stateLang_cons, after_add, add_assoc]
        simp [alloc.vec.Vec.len_val]
  · have empty : state.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨(true, out), by simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more], ?_⟩
    intro _
    rw [empty, stateLang_nil, after_zero, add_zero]
termination_by state.val.length - index.val
decreasing_by omega

private theorem mem_lang_inside (nodes : List Node) (j : Nat) (member : [] ∈ lang nodes j) : j < nodes.length := by
  by_contra outside
  rw [lang_none _ _ (by omega)] at member
  exact Language.notMem_zero _ member

theorem empty_from_spec (nodes : alloc.vec.Vec Node) (flagged : Flagged nodes.val) (stack : alloc.vec.Vec Usize)
    (index : Usize) : compiled.empty_from nodes stack index =
      .ok (decide ([] ∈ stackLang nodes.val (stack.val.drop index.val))) := by
  rw [compiled.empty_from, nil_stackLang]
  by_cases more : index.val < stack.val.length
  · have lookup : stack.index_usize index = .ok stack.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split : (∀ j ∈ stack.val.drop index.val, [] ∈ lang nodes.val j.val) ↔
        [] ∈ lang nodes.val stack.val[index.val].val ∧
          ∀ j ∈ stack.val.drop (index.val + 1), [] ∈ lang nodes.val j.val := by
      rw [drop_cons_eq _ _ more, List.forall_mem_cons]
    by_cases head : [] ∈ lang nodes.val stack.val[index.val].val
    · have headInside := mem_lang_inside _ _ head
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have rest := empty_from_spec nodes flagged stack next
      rw [nextIndex, nil_stackLang] at rest
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        lookup, bind_ok, accepts_empty_spec _ _ flagged, headInside, head, and_self, decide_true, advance, rest]
      by_cases tail : ∀ j ∈ stack.val.drop (index.val + 1), [] ∈ lang nodes.val j.val <;> simp [split, head, tail]
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        lookup, bind_ok, accepts_empty_spec _ _ flagged, head, and_false, decide_false, Bool.false_eq_true]
      simp only [split, head, false_and, decide_false]
  · have empty : stack.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, empty]
termination_by stack.val.length - index.val
decreasing_by omega

theorem accepting_spec (nodes : alloc.vec.Vec Node) (flagged : Flagged nodes.val)
    (state : alloc.vec.Vec (alloc.vec.Vec Usize)) (index : Usize) : compiled.accepting nodes state index =
      .ok (decide ([] ∈ stateLang nodes.val (state.val.drop index.val))) := by
  rw [compiled.accepting]
  by_cases more : index.val < state.val.length
  · have lookup : state.index_usize index = .ok state.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split : [] ∈ stateLang nodes.val (state.val.drop index.val) ↔
        [] ∈ stackLang nodes.val state.val[index.val].val ∨
          [] ∈ stateLang nodes.val (state.val.drop (index.val + 1)) := by
      rw [drop_cons_eq _ _ more, stateLang_cons, Language.mem_add]
    by_cases head : [] ∈ stackLang nodes.val state.val[index.val].val
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        lookup, bind_ok, empty_from_spec _ flagged, show (0#usize).val = 0 from rfl, List.drop_zero, head,
        decide_true]
      simp only [split, head, true_or, decide_true]
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have rest := accepting_spec nodes flagged state next
      rw [nextIndex] at rest
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        lookup, bind_ok, empty_from_spec _ flagged, show (0#usize).val = 0 from rfl, List.drop_zero, head,
        decide_false, Bool.false_eq_true, advance, rest]
      simp only [split, head, false_or]
  · have empty : state.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, empty, stateLang_nil, Language.notMem_zero]
termination_by state.val.length - index.val
decreasing_by omega

theorem start_spec (nodes : List Node) (root : Usize) :
    ∃ s, compiled.start root = .ok s ∧ stateLang nodes s.val = lang nodes root.val := by
  rw [compiled.start]
  have room : (alloc.vec.Vec.new Usize).val.length < Usize.max := by simp; scalar_tac
  obtain ⟨stack, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec (alloc.vec.Vec.new Usize) root room)
  have room' : (alloc.vec.Vec.new (alloc.vec.Vec Usize)).val.length < Usize.max := by simp; scalar_tac
  obtain ⟨state, push', contents'⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new (alloc.vec.Vec Usize)) stack room')
  refine ⟨state, by simp only [push, bind_ok, push'], ?_⟩
  rw [contents']
  simp [stateLang, contents, stackLang_single]

/-! ### Matching whole inputs and greatest prefixes -/

private theorem prefix_at_end (bs : List U8) : Rowl.Unicode.Prefix bs bs.length = none := by
  simp [Rowl.Unicode.Prefix]

private theorem utf8_tail {bs : List U8} {offset cp width : Nat} {word : List Nat}
    (valid : Utf8From bs offset word) (unit : Rowl.Unicode.Prefix bs offset = some (cp, width)) :
    ∃ tail, Utf8From bs (offset + width) tail := by
  cases valid with
  | endOfInput => rw [prefix_at_end] at unit; cases unit
  | character other _ _ tail =>
    rw [unit] at other
    cases Option.some.inj other
    exact ⟨_, tail⟩

private theorem next_valid {bs : List U8} {offset next : Usize} {cp : U32}
    (valid : ∃ word, Utf8From bs offset.val word) (advance : offset.val < next.val)
    (unit : Rowl.Unicode.Prefix bs offset.val = some (cp.val, next.val - offset.val)) :
    ∃ word, Utf8From bs next.val word := by
  obtain ⟨word, utf8⟩ := valid
  obtain ⟨tail, rest⟩ := utf8_tail utf8 unit
  exact ⟨tail, by rwa [show offset.val + (next.val - offset.val) = next.val by omega] at rest⟩

/-- On a table whose flags are right, matching from a state with the language of
    an expression returns what the derivative matcher returns on it, unless a
    vector runs out of room. -/
theorem match_from_eq (nodes : alloc.vec.Vec Node) (flagged : Flagged nodes.val) (bytes : alloc.vec.Vec U8)
    (offset : Usize) (state : alloc.vec.Vec (alloc.vec.Vec Usize)) (e : regular.Expression)
    (same : stateLang nodes.val state.val = Denotes e) :
    ∃ r, compiled.match_from nodes state bytes offset = .ok r ∧
      ∀ m, r = some m → regular.match_from e bytes offset = .ok m := by
  obtain ⟨step, decoded, correct⟩ := Rowl.Unicode.decode_next_total_correct bytes offset
  rw [compiled.match_from, regular.match_from, decoded, bind_ok, bind_ok]
  cases step with
  | End =>
    refine ⟨_, by simp only [accepting_spec _ flagged, bind_ok]; rfl, ?_⟩
    intro m found
    simp only [Option.some.injEq] at found
    subst found
    simp only [Rowl.Regular.nullable_total_correct, bind_ok, show (0#usize).val = 0 from rfl, List.drop_zero, same]
  | Error error =>
    refine ⟨_, rfl, ?_⟩
    intro m found
    simp only [Option.some.injEq] at found
    subst found
    rfl
  | Scalar cp next =>
    obtain ⟨advance, bound, _⟩ := correct
    obtain ⟨derived, derivedRun, derivedLang⟩ := Rowl.Regular.derivative_total_correct e cp
    obtain ⟨r, run, spec⟩ := step_spec nodes flagged cp state 0#usize (alloc.vec.Vec.new (alloc.vec.Vec Usize))
    obtain ⟨done, out⟩ := r
    cases done with
    | false =>
      refine ⟨none, ?_, by simp⟩
      simp [run]
    | true =>
      have outLang : stateLang nodes.val out.val = Denotes derived := by
        rw [spec rfl]
        ext w
        simp [stateLang_nil, same, derivedLang]
      obtain ⟨r2, run2, spec2⟩ := match_from_eq nodes flagged bytes next out derived outLang
      refine ⟨r2, ?_, ?_⟩
      · simp [run, run2]
      · intro m found
        simp only [derivedRun, bind_ok]
        exact spec2 m found
termination_by bytes.val.length - offset.val
decreasing_by omega

/-- Matching with a compiled table returns the derivative matcher's result on
    the expression of its root, unless a vector runs out of room. -/
theorem matches_eq (t : Table) (root : Usize) (bytes : alloc.vec.Vec U8) (e : regular.Expression)
    (flagged : Flagged t.nodes.val)
    (rooted : t.full = false → lang t.nodes.val root.val = Denotes e) :
    ∃ r, compiled.matches t root bytes = .ok r ∧ ∀ m, r = some m → regular.matches_utf8 e bytes = .ok m := by
  rw [compiled.matches]
  cases full : t.full with
  | true => exact ⟨none, by simp, by simp⟩
  | false =>
    obtain ⟨s, run, value⟩ := start_spec t.nodes.val root
    obtain ⟨r, run2, spec⟩ := match_from_eq t.nodes flagged bytes 0#usize s e (by rw [value]; exact rooted full)
    refine ⟨r, by simp only [Bool.false_eq_true, ↓reduceIte, run, bind_ok, run2], ?_⟩
    intro m found
    rw [regular.matches_utf8]
    exact spec m found

private theorem failure_of_step (bytes : alloc.vec.Vec U8) (offset : Usize) (error : unicode.TextError)
    (correct : Rowl.Unicode.StepCorrect bytes.val offset (.Error error)) :
    Rowl.Regular.Utf8Failure bytes.val offset.val error := by
  cases error with
  | InvalidPosition position => exact .position (congrArg UScalar.val correct.1) correct.2
  | InvalidUtf8 position => exact .utf8 (congrArg UScalar.val correct.1) correct.2.1 correct.2.2
  | NonXmlCharacter _ _ => exact False.elim correct

/-- An expression without words keeps the previous endpoint on a valid suffix. -/
theorem scan_dead (bytes : alloc.vec.Vec U8) (offset : Usize) (e : regular.Expression) (last : Option Usize)
    (dead : ∀ w, w ∉ Denotes e) (valid : ∃ word, Utf8From bytes.val offset.val word) :
    longest.scan e bytes offset last = .ok (.Matched last) := by
  obtain ⟨step, decoded, correct⟩ := Rowl.Unicode.decode_next_total_correct bytes offset
  have notNullable : regular.nullable e = .ok false := by
    rw [Rowl.Regular.nullable_total_correct]; simp [dead []]
  rw [longest.scan, notNullable, bind_ok]
  simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, decoded]
  cases step with
  | End => rfl
  | Error error =>
    exfalso
    obtain ⟨word, utf8⟩ := valid
    exact Rowl.Regular.failure_excludes_utf8 _ _ _ (failure_of_step bytes offset error correct) word utf8
  | Scalar cp next =>
    obtain ⟨advance, bound, unit⟩ := correct
    obtain ⟨derived, derivedRun, derivedLang⟩ := Rowl.Regular.derivative_total_correct e cp
    simp only [derivedRun, bind_ok]
    exact scan_dead bytes next derived last (fun w member => dead (cp.val :: w) ((derivedLang w).mp member))
      (next_valid valid advance unit)
termination_by bytes.val.length - offset.val
decreasing_by omega

/-- On a valid suffix the compiled scan from a state with the language of an
    expression returns what the derivative scan returns on it, unless a vector
    runs out of room. -/
theorem scan_from_eq (nodes : alloc.vec.Vec Node) (flagged : Flagged nodes.val) (bytes : alloc.vec.Vec U8)
    (offset : Usize) (state : alloc.vec.Vec (alloc.vec.Vec Usize)) (e : regular.Expression)
    (last : Option Usize) (same : stateLang nodes.val state.val = Denotes e)
    (valid : ∃ word, Utf8From bytes.val offset.val word) :
    ∃ r, compiled.scan_from nodes state bytes offset last = .ok r ∧
      ∀ m, r = some m → longest.scan e bytes offset last = .ok m := by
  obtain ⟨step, decoded, correct⟩ := Rowl.Unicode.decode_next_total_correct bytes offset
  rw [compiled.scan_from]
  by_cases empty : state.val.length = 0
  · have emptyU : alloc.vec.Vec.len state = 0#usize := UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len_val, empty])
    refine ⟨some (.Matched last), by simp only [emptyU, ↓reduceIte], ?_⟩
    intro m found
    simp only [Option.some.injEq] at found
    subst found
    have noStacks : state.val = [] := List.eq_nil_of_length_eq_zero empty
    apply scan_dead bytes offset e last _ valid
    intro w member
    rw [← same, noStacks, stateLang_nil] at member
    exact Language.notMem_zero _ member
  · have emptyU : alloc.vec.Vec.len state ≠ 0#usize := by
      intro h; exact empty (by simpa [alloc.vec.Vec.len_val] using congrArg UScalar.val h)
    have nullable := Rowl.Regular.nullable_total_correct e
    rw [longest.scan, nullable, bind_ok]
    simp only [emptyU, ↓reduceIte, accepting_spec _ flagged, bind_ok, show (0#usize).val = 0 from rfl,
      List.drop_zero, same, decoded]
    by_cases empty' : [] ∈ Denotes e
    · simp only [empty', decide_true, ↓reduceIte, bind_ok]
      cases step with
      | End =>
        refine ⟨_, rfl, ?_⟩
        intro m found
        simp only [Option.some.injEq] at found
        subst found
        rfl
      | Error error =>
        refine ⟨_, rfl, ?_⟩
        intro m found
        simp only [Option.some.injEq] at found
        subst found
        rfl
      | Scalar cp next =>
        obtain ⟨advance, bound, unit⟩ := correct
        obtain ⟨derived, derivedRun, derivedLang⟩ := Rowl.Regular.derivative_total_correct e cp
        obtain ⟨r, run, spec⟩ := step_spec nodes flagged cp state 0#usize (alloc.vec.Vec.new (alloc.vec.Vec Usize))
        obtain ⟨done, out⟩ := r
        cases done with
        | false =>
          refine ⟨none, ?_, by simp⟩
          simp [run]
        | true =>
          have outLang : stateLang nodes.val out.val = Denotes derived := by
            rw [spec rfl]
            ext w
            simp [stateLang_nil, same, derivedLang]
          obtain ⟨r2, run2, spec2⟩ := scan_from_eq nodes flagged bytes next out derived (some offset) outLang
            (next_valid valid advance unit)
          refine ⟨r2, by simp [run, run2], ?_⟩
          intro m found
          simp only [derivedRun, bind_ok]
          exact spec2 m found
    · simp only [empty', decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
      cases step with
      | End =>
        refine ⟨_, rfl, ?_⟩
        intro m found
        simp only [Option.some.injEq] at found
        subst found
        rfl
      | Error error =>
        refine ⟨_, rfl, ?_⟩
        intro m found
        simp only [Option.some.injEq] at found
        subst found
        rfl
      | Scalar cp next =>
        obtain ⟨advance, bound, unit⟩ := correct
        obtain ⟨derived, derivedRun, derivedLang⟩ := Rowl.Regular.derivative_total_correct e cp
        obtain ⟨r, run, spec⟩ := step_spec nodes flagged cp state 0#usize (alloc.vec.Vec.new (alloc.vec.Vec Usize))
        obtain ⟨done, out⟩ := r
        cases done with
        | false =>
          refine ⟨none, ?_, by simp⟩
          simp [run]
        | true =>
          have outLang : stateLang nodes.val out.val = Denotes derived := by
            rw [spec rfl]
            ext w
            simp [stateLang_nil, same, derivedLang]
          obtain ⟨r2, run2, spec2⟩ := scan_from_eq nodes flagged bytes next out derived (last) outLang
            (next_valid valid advance unit)
          refine ⟨r2, by simp [run, run2], ?_⟩
          intro m found
          simp only [derivedRun, bind_ok]
          exact spec2 m found
termination_by bytes.val.length - offset.val
decreasing_by all_goals omega

/-- On a valid suffix the compiled greatest-prefix scan returns the derivative
    greatest-prefix result on the expression of its root, unless a vector runs
    out of room. -/
theorem longest_valid_eq (t : Table) (root : Usize) (bytes : alloc.vec.Vec U8) (offset : Usize)
    (e : regular.Expression) (flagged : Flagged t.nodes.val)
    (rooted : t.full = false → lang t.nodes.val root.val = Denotes e)
    (valid : ∃ word, Utf8From bytes.val offset.val word) :
    ∃ r, compiled.longest_valid t root bytes offset = .ok r ∧
      ∀ m, r = some m → longest.longest_prefix e bytes offset = .ok m := by
  rw [compiled.longest_valid]
  cases full : t.full with
  | true => exact ⟨none, by simp, by simp⟩
  | false =>
    obtain ⟨s, run, value⟩ := start_spec t.nodes.val root
    obtain ⟨r, run2, spec⟩ := scan_from_eq t.nodes flagged bytes offset s e none
      (by rw [value]; exact rooted full) valid
    refine ⟨r, by simp only [Bool.false_eq_true, ↓reduceIte, run, bind_ok, run2], ?_⟩
    intro m found
    rw [longest.longest_prefix]
    exact spec m found

/-- An empty table has right flags. -/
theorem table_spec : ∃ t, compiled.table = .ok t ∧ t.nodes.val = [] ∧ t.full = false ∧ Flagged t.nodes.val := by
  refine ⟨_, rfl, by simp, rfl, ?_⟩
  intro i inside
  simp at inside

/-- Compiling an expression into an empty table gives a table whose root, while
    the table has room, has the expression's language. -/
theorem compile_fresh (e : regular.Expression) :
    ∃ t root t', compiled.table = .ok t ∧ compiled.compile t e = .ok (root, t') ∧ Flagged t'.nodes.val ∧
      (t'.full = false → lang t'.nodes.val root.val = Denotes e) := by
  obtain ⟨t, made, _, _, flagged⟩ := table_spec
  obtain ⟨root, t', run, flagged', _, spec⟩ := compile_spec e t flagged
  exact ⟨t, root, t', made, run, flagged', fun opened => (spec opened).2⟩

end Rowl.Compiled
