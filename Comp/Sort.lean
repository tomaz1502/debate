import Comp.Basic
import Comp.Lower

/-!
# Sorting has `Θ(n log n)` query complexity

We prove that

1. No sorting algorithm can beat `Ω(n log n)` query complexity, on average over a random
   comparison oracle (and thus also in the worst case).
2. Merge sort is a valid sorting algorithm with `O(n log n)` query complexity.
-/

open Classical
open Real (logb)
open Set
noncomputable section

/-!
### The definition of a sorting algorithm
-/

variable {α β : Type}

/-- We only have one oracle, so index them by `Unit` -/
def u : Set Unit := univ

/-- Sort computations are w.r.t. a `≤` comparison oracle -/
abbrev SOracle (α : Type) := Oracle (α × α)

/-- Sort computations are w.r.t. a `≤` comparison oracle -/
abbrev SComp (α β : Type) := Comp (α × α) u β

/-- When one list is another, sorted -/
structure Sorted (o : SOracle α) (s t : List α) : Prop where
  perm : s.Perm t
  sorted : t.Sorted fun x y ↦ (o (x, y)).argmax

/-- Valid sorting oracles are deterministic, reflexive, and transitive -/
structure Oracle.Valid (o : SOracle α) : Prop where
  deterministic : o.Deterministic
  refl : ∀ x, (o (x, x)).argmax
  anti : ∀ x y, (o (x, y)).argmax → (o (y, x)).argmax → x = y
  total : ∀ x y, (o (x, y)).argmax ∨ (o (y, x)).argmax
  trans : ∀ x y z, (o (x, y)).argmax → (o (y, z)).argmax → (o (x, z)).argmax

/-- A sorting algorithm reorders a set to be ordered w.r.t. the oracle -/
def Sorts (f : List α → SComp α (List α)) : Prop :=
  ∀ {o : SOracle α} {s t : List α}, o.Valid → ((f s).prob' o).prob t ≠ 0 → Sorted o s t

/-!
### Oracle and permutation machinery
-/

variable [Fintype α]

/-- Turn a permutation of `Fin.list n` into a valid oracle -/
def oracle (π : α ≃ Fin (Fintype.card α)) : SOracle α :=
  fun x ↦ pure (π x.1 ≤ π x.2)

/-- The set of valid oracles -/
def oracles (α : Type) [Fintype α] : Finset (SOracle α) :=
  (Finset.univ : Finset (α ≃ Fin (Fintype.card α))).image oracle

/-- `oracle π` is valid -/
lemma valid_oracle (π : α ≃ Fin (Fintype.card α)) : (oracle π).Valid where
  deterministic := by apply Oracle.deterministic_pure
  refl x := by simp [oracle]
  anti x y := by
    simp only [oracle, Prob.argmax_pure, decide_eq_true_eq]
    intro u v
    rw [← π.injective.eq_iff]
    exact Fin.le_antisymm u v
  total x y := by
    simp only [oracle, Prob.argmax_pure, decide_eq_true_eq, LinearOrder.le_total]
  trans x y z := by simp [oracle]; apply le_trans

/-- The inverse of `oracle`. The `x ≠ y` bit is superfluous if `o.Valid`, but lets us define
it without the validity assumption. -/
def unoracle (o : SOracle α) : α → Fin (Fintype.card α) :=
  fun x ↦ ⟨(Finset.univ.filter fun y ↦ x ≠ y ∧ (o (x,y)).argmax = false).card, by
    simp only [Finset.card_lt_iff_ne_univ, ← Finset.compl_eq_empty_iff, ne_eq,
      ← Finset.nonempty_iff_ne_empty, Finset.compl_filter, Bool.not_eq_false,
      Finset.filter_nonempty_iff, Finset.mem_univ, true_and]
    use x
    simp only [not_true_eq_false, false_and, not_false_eq_true]⟩

/-- `unoracle ∘ oracle = id` -/
lemma unoracle_oracle (π : α ≃ Fin (Fintype.card α)) : unoracle (oracle π) = π := by
  ext x
  simp only [unoracle, oracle, Prob.argmax_pure, decide_eq_false_iff_not, not_le]
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

/-- The uniform distribution over valid oracles -/
def oraclep (α : Type) [Fintype α] : Prob (SOracle α) :=
    Prob.uniform (oracles α) (oracles_nonempty α)

/-!
### Sorting algorithms have `Ω(n log n)` query complexity
-/

variable {f : List α → SComp α (List α)}

/-- Reconstruct the oracle from a sorted list -/
def sort_to_oracle (t : List α) : SOracle α :=
  fun ⟨x,y⟩ ↦ pure (t.indexOf x ≤ t.indexOf y)

/-- The result of sorting w.r.t. `oracle π` -/
lemma sort_eq {π : α ≃ Fin (Fintype.card α)} {s t : List α} (d : s.Nodup)
    (u : s.toFinset = Finset.univ) (h : Sorted (oracle π) s t) :
    t = π.symm <$> (List.finRange (Fintype.card α)) := by
  refine @List.eq_of_perm_of_sorted _ (fun x y ↦ (oracle π (x, y)).argmax) ?_ _ _ ?_ ?_ ?_
  · exact ⟨(valid_oracle π).anti⟩
  · refine h.perm.symm.trans ?_
    apply List.perm_of_nodup_nodup_toFinset_eq d
    · exact List.Nodup.map π.symm.injective (List.nodup_finRange _)
    · simp only [u, Finset.map_toFinset, List.map_eq_map]
      ext x
      simp only [Finset.mem_univ, List.mem_toFinset, List.mem_map, List.mem_finRange, true_and,
        true_iff]
      use π x
      simp
  · exact h.sorted
  · simp only [← List.ofFn_id, List.map_eq_map, List.map_ofFn, CompTriple.comp_eq,
      List.sorted_ofFn_iff]
    intro x y xy
    simp only [oracle, Equiv.apply_symm_apply, xy.le, decide_True, Prob.argmax_pure]

lemma List.indexOf_map (l : List α) (f : α ≃ β) (x : β) :
    (l.map f).indexOf x = l.indexOf (f.symm x) := by
  induction' l with y l h
  · simp
  · simp [List.indexOf_cons, h, Equiv.eq_symm_apply, beq_eq_decide]

/-- `sort_to_oracle` is correct -/
lemma sort_to_oracle_eq {π : α ≃ Fin (Fintype.card α)} {s t : List α} (d : s.Nodup)
    (u : s.toFinset = Finset.univ) (h : Sorted (oracle π) s t) : sort_to_oracle t = oracle π := by
  have e : ∀ x, t.indexOf x = π x := by
    intro x
    simp only [sort_eq d u h, List.map_eq_map, List.indexOf_map, Equiv.symm_symm]
    convert List.indexOf_finRange (π x)
  funext ⟨x,y⟩
  simp only [sort_to_oracle, e, Fin.val_fin_le, oracle]

/-- Sorting takes `Ω(log n!)` queries on average -/
theorem Sorts.le_cost (s : Sorts f) :
    logb 2 (Fintype.card α).factorial ≤
      (oraclep α).exp fun o ↦ (f (Finset.univ : Finset α).toList).cost' o () := by
  refine le_trans ?_ (Comp.I_le_cost _ _)
  refine le_trans (le_of_eq ?_) (Prob.I_map_le_I _ sort_to_oracle)
  simp only [Comp.prob', Prob.map_eq, bind_assoc, pure_bind]
  trans (do
    let o ← oraclep α
    let _ ← (f Finset.univ.toList).prob' o
    return (o, o)).I
  · simp only [oraclep, Comp.prob', Prob.bind_const, Prob.I_self, Prob.H_uniform, card_oracles]
  · refine congr_arg _ ?_
    refine Prob.bind_congr _ _ _ (fun o po ↦ ?_)
    refine Prob.bind_congr _ _ _ (fun r pr ↦ ?_)
    apply congr_arg _ ?_
    simp only [Prod.mk.injEq, true_and]
    simp only [oraclep, ← Finsupp.mem_support_iff, Prob.support_uniform, oracles,
      Finset.mem_image, Finset.mem_univ, true_and] at po
    rcases po with ⟨π, πo⟩
    rw [← πo, sort_to_oracle_eq (π := π) (s := Finset.univ.toList)]
    · apply Finset.nodup_toList
    · simp only [Finset.toList_toFinset]
    · rw [← πo] at pr
      exact s (valid_oracle π) pr

/-- Sorting takes `Ω(log n!)` queries, worst case -/
theorem Sorts.le_cost' (s : Sorts f) : ∃ (o : SOracle α) (s : List α),
    logb 2 (Fintype.card α).factorial ≤ (f s).cost' o () := by
  generalize hc : logb 2 (Fintype.card α).factorial = c
  have h := Sorts.le_cost s
  contrapose h
  simp only [not_exists, not_le, hc] at h ⊢
  refine lt_of_lt_of_le (Prob.exp_lt_exp (h := fun _ ↦ c) ?_ ?_) (le_of_eq ?_)
  · intro _ _; exact (h _ _).le
  · refine ⟨oracle (Fintype.equivFin α), ?_, ?_⟩
    · simp only [← Finsupp.mem_support_iff, oraclep, oracles, Prob.support_uniform,
        Finset.mem_image, Finset.mem_univ, true_and, exists_apply_eq_apply]
    · apply h
  · simp only [Prob.exp_const]

/-!
### Merge sort is a sorting algorithm with `O(n log n)` query complexity

We define our `merge` to match `List.mergeSort`, so that we reuse the existing correctness proof.
-/

def merge (s t : List α) : SComp α (List α) := loop s t [] where
  loop : List α → List α → List α → SComp α (List α)
    | [], x, p => return p.reverseAux x
    | x, [], p => return p.reverseAux x
    | (a :: l), (b :: r), p => do
      bif ← (Comp.query () (a,b)).allow_all then loop l (b :: r) (a :: p)
      else loop (a :: l) r (b :: p)

def mergeSort : List α → SComp α (List α)
  | [] => pure []
  | [a] => pure [a]
  | a :: b :: l => do
    let s := (a :: b :: l).split
    have := List.length_split_fst_le l
    have := List.length_split_snd_le l
    merge (← mergeSort s.1) (← mergeSort s.2)
  termination_by s => s.length

/-- `merge.loop` is `List.merge.loop` -/
lemma merge_loop_eq (o : SOracle α) (d : o.Deterministic) : (s t r : List α) →
    (merge.loop s t r).prob (fun _ ↦ o) = pure (List.merge.loop (fun x y ↦ (o (x,y)).argmax) s t r)
  | [], _, _ => by simp only [Comp.prob', merge.loop, Comp.prob_pure, List.merge.loop]
  | (_ :: _), [], _ => by simp only [Comp.prob', merge.loop, Comp.prob_pure, List.merge.loop]
  | (a :: l), (b :: r), _ => by
    simp only [Comp.prob', merge.loop, Comp.prob_bind, Comp.prob_allow_all, Comp.prob_query,
      List.merge.loop]
    rw [d.eq_pure (a,b)]
    simp only [pure_bind, Prob.argmax_pure]
    induction' (o (a, b)).argmax with b
    · simp only [cond_false]; apply merge_loop_eq _ d
    · simp only [cond_true]; apply merge_loop_eq _ d

/-- `merge` is `List.merge` -/
lemma merge_eq (o : SOracle α) (d : o.Deterministic) (s t : List α) :
    (merge s t).prob (fun _ ↦ o) = pure (List.merge (fun x y ↦ (o (x,y)).argmax) s t) := by
  apply merge_loop_eq _ d

/-- `mergeSort` is `List.mergeSort` -/
lemma mergeSort_eq (o : SOracle α) (d : o.Deterministic) : (s : List α) →
    (mergeSort s).prob (fun _ ↦ o) = pure (List.mergeSort (fun x y ↦ (o (x,y)).argmax) s)
  | [] => by simp [mergeSort]
  | [a] => by simp [mergeSort]
  | a :: b :: l => by
    simp only [mergeSort, List.mergeSort]
    set s := a :: b :: l
    have := List.length_split_fst_le l
    have := List.length_split_snd_le l
    simp only [Comp.prob', Comp.prob_bind, mergeSort_eq _ d s.split.1, mergeSort_eq _ d s.split.2]
    simp only [List.split, merge_eq _ d, List.merge, pure_bind, Bool.decide_eq_true]
  termination_by s => s.length
  decreasing_by all_goals simp_wf; omega

/-- `mergeSort` sorts -/
lemma sorts_mergeSort : Sorts (mergeSort (α := α)) := by
  intro o s t v pt
  simp only [Comp.prob', mergeSort_eq _ v.deterministic, Prob.prob_pure, ne_eq, ite_eq_right_iff,
    one_ne_zero, imp_false, Decidable.not_not] at pt
  rw [pt]
  exact {
    perm := List.Perm.symm (List.perm_mergeSort _ _)
    sorted := by
      refine @List.sorted_mergeSort _ _ _ ⟨?_⟩ ⟨?_⟩ s
      · intro _ _; apply v.total
      · intro _ _ _; apply v.trans
  }

/-- `merge.loop` is `O(n)` -/
lemma cost_merge_loop_le (o : SOracle α) : (s t r : List α) →
    (merge.loop s t r).cost (fun _ ↦ o) () ≤ s.length + t.length
  | [], _, _ => by simp [merge.loop, List.merge.loop]
  | (_ :: _), [], _ => by simp [merge.loop, List.merge.loop]; positivity
  | (a :: l), (b :: r), _ => by
    simp only [Comp.cost', merge.loop, Comp.cost_bind, Comp.cost_allow_all, Comp.cost_query,
      Comp.prob_allow_all, Comp.prob_query, List.length_cons, Nat.succ_eq_add_one, Nat.cast_min,
      Nat.cast_add, Nat.cast_one, min_add_add_right, add_comm 1, add_comm (1 : ℝ),
      add_le_add_iff_right, ← add_assoc]
    refine Prob.exp_le_of_forall_le fun b _ ↦ ?_
    induction' b with b
    · simp only [cond_false]
      refine le_trans (cost_merge_loop_le o _ _ _) ?_
      simp only [List.length_cons, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, le_refl]
    · simp only [cond_true]
      refine le_trans (cost_merge_loop_le o _ _ _) ?_
      simp only [List.length_cons, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
      linarith

/-- `merge` is `O(n)` -/
lemma cost_merge_le (o : SOracle α) (s t : List α) :
    (merge s t).cost (fun _ ↦ o) () ≤ s.length + t.length :=
  cost_merge_loop_le o s t []

/-- Exact lengths after `List.split` -/
lemma List.length_split_eq (s : List α) :
    s.split.1.length = (s.length + 1) / 2 ∧ s.split.2.length = s.length / 2 := by
  induction' s with a s h
  · simp only [split, length_nil, zero_add, Nat.reduceDiv, Nat.zero_div, and_self]
  · simp only [split, length_cons, h, Nat.succ_eq_add_one, and_true]; omega

/-- `merge.loop` preserves `length` -/
lemma length_merge_loop (o : SOracle α) : (s t r x : List α) →
    (px : ((merge.loop s t r).prob (fun _ ↦ o)).prob x ≠ 0) →
    x.length = s.length + t.length + r.length
  | [], t, r, x, px => by
    simp only [merge.loop, Comp.prob_pure, Prob.prob_pure, ne_eq, ite_eq_right_iff, one_ne_zero,
      imp_false, not_not, List.reverseAux_eq] at px
    simp only [px, List.length_append, List.length_reverse, List.length_nil, zero_add]
    ring
  | (_ :: _), [], _, _, px => by
    simp only [merge.loop, List.reverseAux_eq, Comp.prob_pure, Prob.prob_pure, ne_eq,
      ite_eq_right_iff, one_ne_zero, imp_false, not_not] at px
    simp only [px, List.length_append, List.length_reverse, List.length_cons, Nat.succ_eq_add_one,
      List.length_nil, add_zero]
    omega
  | (a :: s), (b :: t), r, x, px => by
    simp only [merge.loop, Comp.prob_bind, Comp.prob_allow_all, Comp.prob_query,
      Prob.prob_bind_ne_zero, Bool.exists_bool, cond_false, cond_true] at px
    rcases px with ⟨_, px⟩ | ⟨_, px⟩
    all_goals simp only [length_merge_loop _ _ _ _ _ px, List.length_cons]; omega

/-- `merge` preserves `length` -/
lemma length_merge (o : SOracle α) (s t x : List α)
    (px : ((merge s t).prob (fun _ ↦ o)).prob x ≠ 0) :
    x.length = s.length + t.length := by
  simp only [length_merge_loop o s t [] x px, List.length_nil, add_zero]

/-- `mergeSort` preserves `length` -/
lemma length_mergeSort (o : SOracle α) : (s x : List α) →
    (px : ((mergeSort s).prob (fun _ ↦ o)).prob x ≠ 0) →
    x.length = s.length
  | [] => by simp [mergeSort, Prob.prob_pure]
  | [a] => by simp [mergeSort, Prob.prob_pure]
  | a :: b :: l => by
    simp only [mergeSort, List.mergeSort, Prob.prob_bind_ne_zero, Comp.prob_bind]
    intro x ⟨x1, px1, x2, px2, pm⟩
    set s := a :: b :: l
    have := List.length_split_fst_le l
    have := List.length_split_snd_le l
    simp only [Comp.prob', Comp.prob_bind, length_mergeSort o s.split.1 x1 px1,
      length_mergeSort o s.split.2 x2 px2, length_merge o _ _ _ pm, List.length_split_eq]
    omega
  termination_by s => s.length

/-- `log2 n`, rounding up -/
def Nat.ceil_log2 (n : ℕ) : ℕ := Nat.log2 (2 * n - 1)

/-- `Nat.ceil_log2` is an upper bound -/
lemma Nat.le_ceil_log2 (n : ℕ) : n ≤ 2 ^ n.ceil_log2 := by
  simp only [Nat.ceil_log2]
  by_cases n0 : n = 0
  · simp [n0]
  · have h := Nat.lt_log2_self (n := 2 * n - 1)
    omega

/-- `Nat.ceil_log2 n` is zero for `n ≤ 1` -/
@[simp] lemma Nat.ceil_log2_eq_zero_iff (n : ℕ) : n.ceil_log2 = 0 ↔ n ≤ 1 := by
  by_cases n0 : n = 0
  · simp only [n0]; decide
  by_cases n1 : n = 1
  · simp only [n1]; decide
  have nle : ¬n ≤ 1 := by omega
  simp only [nle, iff_false, ne_eq]
  have h := Nat.le_ceil_log2 n
  contrapose h
  simp only [ne_eq, not_not] at h
  simp only [h, pow_zero, not_le]
  omega

/-- `Nat.log2` is monotonic -/
lemma Nat.log2_le_log2 {a b : ℕ} (ab : a ≤ b) : a.log2 ≤ b.log2 := by
  induction' b using Nat.strong_induction_on with b h generalizing a
  rw [Nat.log2]
  nth_rw 2 [Nat.log2]
  by_cases a2 : a < 2
  · by_cases a0 : a = 0
    · simp [a0]
    · have a1 : a = 1 := by omega
      simp [a1]
  · have b2 : 2 ≤ b := by omega
    simp only [not_lt.mp a2, ↓reduceIte, b2, add_le_add_iff_right]
    apply h
    all_goals omega

/-- `Nat.log2` is monotonic -/
lemma Nat.ceil_log2_le_ceil_log2 {a b : ℕ} (ab : a ≤ b) : a.ceil_log2 ≤ b.ceil_log2 := by
  apply Nat.log2_le_log2; omega

 /-- `n/2` has one smaller `ceil_log2` -/
lemma Nat.ceil_log2_div2 (n : ℕ) (n2 : 2 ≤ n) : (n / 2).ceil_log2 ≤ n.ceil_log2 - 1 := by
  simp only [ceil_log2]
  have e : (2 * n - 1).log2 = ((2 * n - 1) / 2).log2 + 1 := by
    rw [Nat.log2]; simp only [(by omega : 2 * n - 1 ≥ 2), if_true]
  rw [e, Nat.add_sub_cancel]
  apply Nat.log2_le_log2
  omega

/-- The cost of `mergeSort`. The factor of 3 is unnecessarily, but makes the proof easier. -/
def mergeSort_bound (n : ℕ) : ℕ := 3 * n * n.ceil_log2

/-- The inductive step inequality in `cost_mergeSort_le` -/
lemma mul_log_le (n : ℕ) (n2 : 2 ≤ n) :
    mergeSort_bound ((n+1)/2) + (mergeSort_bound (n/2) + n) ≤ mergeSort_bound n := by
  simp only [mergeSort_bound]
  have h0 := Nat.ceil_log2_div2 n n2
  generalize ha : n.ceil_log2 = a at h0
  have h1 : ((n + 1) / 2).ceil_log2 ≤ a := by rw [← ha]; apply Nat.ceil_log2_le_ceil_log2; omega
  have a1 : 1 ≤ a := by
    contrapose n2
    simp only [not_le, Nat.lt_one_iff] at n2
    simp only [n2, Nat.ceil_log2_eq_zero_iff] at ha
    omega
  trans 3 * ((n + 1) / 2) * a + (3 * (n / 2) * (a - 1) + n)
  · gcongr
  generalize hu : n / 2 = u
  generalize hv : (n + 1) / 2 = v
  have uv : u + v = n := by omega
  simp only [Nat.mul_sub_left_distrib, mul_one]
  trans 3 * v * a + 3 * u * a + (n - 3 * u)
  · simp only [add_assoc, add_le_add_iff_left]
    have un : n ≤ 3 * u := by omega
    have uu : 3 * u ≤ 3 * u * a := Nat.le_mul_of_pos_right _ a1
    simp only [Nat.sub_eq_zero_of_le un, add_zero]
    omega
  · simp only [← Nat.add_mul, ← Nat.mul_add, add_comm _ u, uv]
    omega

/-- `mergeSort` is `O(n log n)` -/
lemma cost_mergeSort_le (o : SOracle α) (s : List α) :
    (mergeSort s).cost (fun _ ↦ o) () ≤ mergeSort_bound s.length := by
  generalize hn : s.length = n
  induction' n using Nat.strong_induction_on with n h generalizing s
  induction' s with a s d
  · simp only [List.length_nil] at hn
    simp [mergeSort,  ← hn]
  · clear d
    induction' s with b s d
    · simp only [List.length_singleton] at hn
      simp [mergeSort,  ← hn]
    · simp only [List.length_cons, Nat.succ_eq_add_one] at hn
      simp only [Comp.cost', mergeSort, List.split, Comp.cost_bind, Prob.exp_add, Prob.exp_const]
      refine le_trans (add_le_add (h (a :: s.split.1).length ?_ (a :: s.split.1) rfl)
          (add_le_add (h (b :: s.split.2).length ?_ (b :: s.split.2) rfl)
          (Prob.exp_le_of_forall_le fun x px ↦ Prob.exp_le_of_forall_le (b := n) fun y py ↦ ?_))) ?_
      · simp only [List.length_cons, s.length_split_eq, ← hn]
        omega
      · simp only [List.length_cons, s.length_split_eq]
        omega
      · refine le_trans (cost_merge_le _ _ _) ?_
        simp only [length_mergeSort _ _ _ px, List.length_cons, List.length_split_eq,
          length_mergeSort _ _ _ py, ← Nat.cast_add, Nat.cast_le]
        omega
      · clear d
        simp only [List.length_cons, List.length_split_eq, Nat.succ_eq_add_one,
          (by omega : s.length = n - 2), (by omega : (n - 2) / 2 + 1 = n / 2),
          (by omega : (n - 2 + 1) / 2 + 1 = (n + 1) / 2)]
        simp only [← Nat.cast_mul, ← Nat.cast_add, Nat.cast_le]
        exact mul_log_le n (by omega)
