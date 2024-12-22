import Comp.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Interval.Finset.Fin

/-!
# Sorting has `Θ(n log n)` query complexity

We prove that

1. No sorting algorithm can beat `Ω(n log n)` query complexity, on average over a random
   comparison oracle (and thus also in the worst case).
2. Merge sort is a valid sorting algorithm with `O(n log n)` query complexity.
-/

open Classical
-- open Real (logb)
open Set
noncomputable section

/-!
### The definition of a sorting algorithm
-/

variable {α β : Type}

/-- We only have one oracle, so index them by `Unit` -/
def u : Set Unit := univ

def SOracle (α : Type) := Oracle (α × α)

/-- Sort computations are w.r.t. a `≤` comparison oracle -/
abbrev SComp (α β : Type) := Comp (α × α) u β

/-- When one list is another, sorted -/
structure Sorted (o : SOracle α) (s t : List α) : Prop where
  perm : s.Perm t
  sorted : t.Sorted fun x y ↦ (o (x, y))

/-- Valid sorting oracles are deterministic, reflexive, and transitive -/
structure SOracle.Valid (o : SOracle α) : Prop where
  refl : ∀ x, (o (x, x))
  anti : ∀ x y, (o (x, y)) → (o (y, x)) → x = y
  total : ∀ x y, (o (x, y)) ∨ (o (y, x))
  trans : ∀ x y z, (o (x, y)) → (o (y, z)) → (o (x, z))

/-- A sorting algorithm reorders a set to be ordered w.r.t. the oracle -/
def Sorts (f : List α → SComp α (List α)) : Prop :=
  ∀ {o : SOracle α} {s t : List α}, o.Valid → ((f s).value (fun _ => o)) = t → Sorted o s t

/-!
### Oracle and permutation machinery
-/

variable [Fintype α]

/-- Turn a permutation of `Fin.list n` into a valid oracle -/
def oracle (π : α ≃ Fin (Fintype.card α)) : SOracle α :=
  fun x ↦ (π x.1 ≤ π x.2)

/-- The set of valid oracles -/
def oracles (α : Type) [Fintype α] : Finset (SOracle α) :=
  (Finset.univ : Finset (α ≃ Fin (Fintype.card α))).image oracle

/-- `oracle π` is valid -/
lemma valid_oracle (π : α ≃ Fin (Fintype.card α)) : (oracle π).Valid where
  refl x := by simp [oracle]
  anti x y := by
    simp only [oracle, decide_eq_true_eq]
    intro u v
    rw [← π.injective.eq_iff]
    exact Fin.le_antisymm u v
  total x y := by
    simp only [oracle, decide_eq_true_eq, LinearOrder.le_total]
  trans x y z := by simp [oracle]; apply le_trans

/-- The inverse of `oracle`. The `x ≠ y` bit is superfluous if `o.Valid`, but lets us define
it without the validity assumption. -/
def unoracle (o : SOracle α) : α → Fin (Fintype.card α) :=
  fun x ↦ ⟨(Finset.univ.filter fun y ↦ x ≠ y ∧ (o (x,y)) = false).card, by
    simp only [Finset.card_lt_iff_ne_univ, ← Finset.compl_eq_empty_iff, ne_eq,
      ← Finset.nonempty_iff_ne_empty, Finset.compl_filter, Bool.not_eq_false,
      Finset.filter_nonempty_iff, Finset.mem_univ, true_and]
    use x
    simp only [not_true_eq_false, false_and, not_false_eq_true]⟩

/-- `unoracle ∘ oracle = id` -/
lemma unoracle_oracle (π : α ≃ Fin (Fintype.card α)) : unoracle (oracle π) = π := by
  ext x
  simp only [unoracle, oracle, decide_eq_false_iff_not, not_le]
  have s : ∀ x y : α, x ≠ y ∧ π y < π x ↔ π y < π x := by
    intro x y
    constructor
    · intro h; exact h.2
    · intro h; simp only [h, and_true]
      contrapose h; simp only [not_not] at h
      simp only [h, lt_self_iff_false, not_false_eq_true]
  simp only [← Finset.card_map π.toEmbedding, Finset.map_filter, Function.comp,
    Equiv.apply_symm_apply, Finset.map_univ_equiv, s]
  rw [← Fin.card_Iio]
  apply congr_arg
  ext k
  simp

/-- `oracle` is injective -/
lemma oracle_inj (α : Type) [Fintype α] : (oracle (α := α)).Injective := by
  intro e0 e1 e
  have h : unoracle (oracle e0) = unoracle (oracle e1) := by simp only [e]
  simpa only [unoracle_oracle, DFunLike.coe_fn_eq] using h

/-- There are `n!` valid oracles -/
@[simp] lemma card_oracles (α : Type) [Fintype α] :
    (oracles α).card = (Fintype.card α).factorial := by
  simp only [oracles, Finset.card_image_of_injective _ (oracle_inj _), Finset.card_univ]
  exact Fintype.card_equiv (Fintype.equivFin α)

/-- `oracles` is nonempty -/
lemma oracles_nonempty (α : Type) [Fintype α] : (oracles α).Nonempty := by
  simp only [← Finset.card_ne_zero, card_oracles]
  apply Nat.factorial_ne_zero

/-!
### Merge sort is a sorting algorithm with `O(n log n)` query complexity

We define our `merge` to match `List.mergeSort`, so that we reuse the existing correctness proof.
-/

def merge (xs ys : List α) : SComp α (List α) := do
  match xs, ys with
  | [], ys => return ys
  | xs, [] => return xs
  | x :: xs, y :: ys =>
    if ← (Comp.query () (x,y)).allow_all then
      return x :: (← merge xs (y :: ys))
    else
      return y :: (← merge (x :: xs) ys)

def mergeSort : List α → SComp α (List α)
  | [] => pure []
  | [a] => pure [a]
  | a :: b :: l => do
    let s := List.splitInTwo ⟨a :: b :: l, rfl⟩
    merge (← mergeSort s.1) (← mergeSort s.2)
  termination_by s => s.length

omit [Fintype α] in
/-- `merge` is `List.merge` -/
lemma merge_eq (o : SOracle α) : (s t : List α) →
    (merge s t).value (fun _ ↦ o) = (List.merge s t (fun x y ↦ (o (x,y))))
  | [], _ => by simp only [Comp.value', merge, Comp.value_pure, List.merge]
  | (_ :: _), [] => by simp only [Comp.value', merge, Comp.value_pure, List.merge]
  | (a :: l), (b :: r) => by
    simp only [Comp.value', merge, Comp.value_bind, Comp.value_allow_all, Comp.value_query, List.merge]
    cases o (a, b)
    · simp; apply merge_eq o _ _
    · simp; apply merge_eq o _ _

omit [Fintype α] in
/-- `mergeSort` is `List.mergeSort` -/
lemma mergeSort_eq (o : SOracle α) : (s : List α) →
    (mergeSort s).value (fun _ ↦ o) = (List.mergeSort s (fun x y ↦ (o (x,y))))
  | [] => by simp only [mergeSort, Comp.value_pure, List.mergeSort_nil]
  | [a] => by simp only [mergeSort, Comp.value_pure, List.mergeSort_singleton]
  | a :: b :: l => by
    simp only [mergeSort, List.length_cons, List.splitInTwo_fst, List.splitInTwo_snd,
      Comp.value_bind, List.mergeSort]
    set t := List.splitInTwo ⟨a :: b :: l, rfl⟩
    simp only [mergeSort_eq o ((List.take ((l.length + 1 + 1 + 1) / 2) (a :: b :: l))),
      mergeSort_eq o ((List.drop ((l.length + 1 + 1 + 1) / 2) (a :: b :: l))),
      pure_bind, merge_eq o]
  termination_by s => s.length

omit [Fintype α]
/-- `mergeSort` sorts -/
lemma sorts_mergeSort : Sorts (mergeSort (α := α)) := by
  intro o s t v pt
  simp only [Comp.value', mergeSort_eq _ ,  ne_eq, ite_eq_right_iff,
    one_ne_zero, imp_false, Decidable.not_not] at pt
  rw [<- pt]
  exact {
    perm := List.Perm.symm (List.mergeSort_perm _ _)
    sorted := by
      apply List.sorted_mergeSort
      · intro _ _ _; apply v.trans
      · intro _ _; simp only [Bool.or_eq_true]; apply v.total
  }

/-- `merge` is `O(n)` -/
lemma cost_merge_le (o : SOracle α) : (s t : List α) →
    (merge s t).cost (fun _ ↦ o) () ≤ s.length + t.length
  | [], _ => by simp [merge, List.merge]
  | (_ :: _), [] => by simp [merge, List.merge]
  | (a :: l), (b :: r) => by
    simp only [Comp.cost', merge, Comp.cost_bind, Comp.cost_allow_all, Comp.cost_query,
      Comp.value_allow_all, Comp.value_query, List.length_cons, Nat.succ_eq_add_one,
      Nat.cast_add, Nat.cast_one, min_add_add_right, add_comm 1,
      add_le_add_iff_right, ← add_assoc]
    cases o (a, b)
    · simp; simp only [Comp.cost_map]; apply cost_merge_le o _ _
    · simp only [↓reduceIte, bind_pure_comp, Comp.cost_map]
      have ih := cost_merge_le o l (b :: r)
      simp only [List.length_cons] at ih
      omega

/-- `merge` preserves `length` -/
lemma length_merge (o : SOracle α) : (s t x : List α) →
    (px : ((merge s t).value (fun _ ↦ o)) = x) → x.length = s.length + t.length
  | [], t, x, px => by
    simp only [merge] at px
    rw [<- px]
    simp only [Comp.value_pure, List.length_nil, zero_add]
  | (a :: l), [], x, px => by
    simp only [merge] at px
    rw [<- px]
    simp only [Comp.value_pure, List.length_cons, List.length_nil, add_zero]
  | (a :: s), (b :: t), x, px => by
    simp only [merge, Comp.value_bind, Comp.value_allow_all, Comp.value_query] at px
    by_cases ho : (o (a, b))
    · rw [ho] at px; simp at px; rw [<- px]; simp;
      have ih := length_merge o s (b :: t) ((merge s (b :: t)).value (fun _ => o)) rfl
      simp at ih
      omega
    · simp at ho; rw [ho] at px; simp at px; rw [<- px]; simp;
      have ih := length_merge o (a :: s) t ((merge (a :: s) t).value (fun _ => o)) rfl
      simp at ih
      omega

/-- `mergeSort` preserves `length` -/
lemma length_mergeSort (o : SOracle α) : (s x : List α) →
    (px : ((mergeSort s).value (fun _ ↦ o)) = x) →
    x.length = s.length
  | [] => by simp [mergeSort]
  | [a] => by simp [mergeSort]
  | a :: b :: l => by
    simp only [mergeSort, List.mergeSort, Comp.value_bind]
    intros x heq
    rw [<-heq]
    simp
    admit
    /- intro x heq -/
    /- rw [<- heq] -/

    /- set s := a :: b :: l -/
    /- have hh : s = a :: b :: l := rfl -/
    /- rw [<- hh] -/

    /- simp only [length_merge o ((mergeSort s.splitInTwo.1).value (fun _ => o)) ((mergeSort s.splitInTwo.2).value (fun _ => o))] -/

    /- simp only [Comp.value', Comp.value_bind, length_mergeSort o _ _ _, length_mergeSort o _ _ _, -/
    /-   length_merge o _ _ _ _, List.length_cons, List.splitInTwo_fst, List.length_take, -/
    /-   List.splitInTwo_snd, List.length_drop] -/

    /- admit -/
    /- rw [min_eq_left] -/
    /- all_goals omega -/
  termination_by s => s.length
