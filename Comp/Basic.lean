import Comp.Oracle
import Comp.Defs
import Mathlib.Algebra.Order.Ring.Nat




/-!
## Basic properties of `Comp`
-/

open Classical
open Option (some none)
noncomputable section

variable {ι I : Type}
variable {s t u : Set I}
variable {α β γ : Type}

namespace Comp

lemma map_eq (f : α → β) (x : Comp ι s α) : f <$> x = x >>= (λ x ↦ pure (f x)) := rfl

/-- `Comp` is a lawful monad -/
instance : LawfulMonad (Comp ι s) := LawfulMonad.mk'
  (id_map := by
    intro α f
    simp only [map_eq, id, bind, bind']
    induction' f with _ _ _ _ _ _ h0 h1
    · rfl
    · simp only [bind', h0, h1])
  (pure_bind := by intro α β x f; simp only [bind, bind'])
  (bind_assoc := by
    intro α β β f g h
    simp only [bind]
    induction' f with _ _ _ _ _ _ h0 h1
    · rfl
    · simp only [bind', h0, h1])

/-- Running a `pure'` is `pure` -/
@[simp] lemma value_pure' (x : α) (o : I → Oracle ι) : (pure' x : Comp ι s α).value o = x := by
  simp only [value, run, map_pure]

@[simp] lemma value_pure (x : α) (o : I → Oracle ι) : (pure x : Comp ι s α).value o = x := by
  simp only [pure, value_pure']

-- The definition of `Comp.bind` as `simp` lemmas
@[simp] lemma pure'_bind (x : α) (f : α → Comp ι s β) : (pure' x : Comp ι s α) >>= f = f x := rfl
@[simp] lemma query'_bind (o : I) (m : o ∈ s) (y : ι) (f0 f1 : Comp ι s α)
    (g : α → Comp ι s β) : query' o m y f0 f1 >>= g = .query' o m y (f0 >>= g) (f1 >>= g) := rfl

/-- Cost is nonnegative -/
@[simp] lemma cost_nonneg {f : Comp ι s α} {o : I → Oracle ι} {i : I} : 0 ≤ f.cost o i := by
  simp only [zero_le]

/-- `pure` is free -/
@[simp] lemma cost_pure (x : α) (o : I → Oracle ι) (i : I) : (pure x : Comp ι s α).cost o i = 0 := by
  simp only [cost, run, Nat.cast_zero]

/-- `pure` is free -/
@[simp] lemma cost'_pure (x : α) (o : Oracle ι) (i : I) : (pure x : Comp ι s α).cost' o i = 0 := by
  simp only [cost', cost_pure]

/-- `pure'` is free -/
@[simp] lemma cost_pure' (x : α) (o : I → Oracle ι) (i : I) :
    (Comp.pure' x : Comp ι s α).cost o i = 0 := by
  simp only [cost, run, Nat.cast_zero]

/-- `pure'` is free -/
@[simp] lemma cost'_pure' (x : α) (o : Oracle ι) (i : I) :
    (Comp.pure' x : Comp ι s α).cost' o i = 0 := by
  simp only [cost', cost_pure']

/-- `query'` costs one query, plus the rest -/
@[simp] lemma cost_query' {i : I} (m : i ∈ s) (y : ι) (f0 f1 : Comp ι s α)
    (o : I → Oracle ι) (j : I) :
    (Comp.query' i m y f0 f1).cost o j =
      (if j = i then 1 else 0) + (if (o i y) then f0.cost o j else f1.cost o j) := by
  simp [cost, run]
  cases o i y
  · exact Nat.add_comm _ _
  · exact Nat.add_comm _ _

@[simp] lemma cost_query (i : I) (y : ι) (o : I → Oracle ι) :
    (query i y).cost o i = 1 := by
  simp only [query, cost_query', ite_true, cost_pure, ite_self, add_zero]

lemma cost_of_not_mem (f : Comp ι s α) (o : I → Oracle ι) {i : I} (is : i ∉ s) :
    f.cost o i = 0 := by
  induction' f with a j js y f0 f1 h0 h1
  · rfl
  · simp only [cost_query']
    by_cases ij : i = j
    · rw [ij] at is; exact False.elim (is js)
    · simp [ij, h0, h1]

/-- Expanding `query'.run` -/
lemma run_query {i : I} (m : i ∈ s) (y : ι) (f0 f1 : Comp ι s α)
    (o : I → Oracle ι) : (Comp.query' i m y f0 f1).run o =
      let x := (o i) y
      let (z,c) := if x then f0.run o else f1.run o
      (z, c + fun j => if j = i then 1 else 0) := rfl

@[simp] lemma value_query' (i : I) (m : i ∈ s) (y : ι) (f0 f1 : Comp ι s α)
    (o : I → Oracle ι) :
    (query' i m y f0 f1).value o = (if o i y then f0.value o else f1.value o) := by
  simp only [value, run_query]
  cases o i y
  · rfl
  · rfl

@[simp] lemma value_query (i : I) (y : ι) (o : I → Oracle ι) :
    (query i y).value o = o i y := by
  simp only [query, value_query'];
  cases o i y
  · rfl
  · rfl

/-- The cost of `f >>= g` is roughly `f.cost + g.cost` -/
lemma cost_bind (f : Comp ι s α) (g : α → Comp ι s β) (o : I → Oracle ι) (i : I) :
    (f >>= g).cost o i = f.cost o i + ((g (f.value o)).cost o i) := by
  induction' f with a b c d e f h0 h1
  · simp only [cost_pure', zero_add, value_pure', bind, bind']
  · simp only [bind, bind'] at h0 h1
    simp only [cost_query', bind, bind', add_assoc, h0, h1]
    apply congr_arg₂ _ rfl
    split
    · simp only [value_query']; simp; aesop
    · simp only [value_query']; simp; aesop

@[simp] lemma value_bind (f : Comp ι s α) (g : α → Comp ι s β) (o : I → Oracle ι) :
    (f >>= g).value o = (g (f.value o)).value o := by
  induction' f with a b c d e f h0 h1
  · rfl
  · simp only [value_query', query'_bind]; simp only [h0, h1];
    cases o b d
    · rfl
    · rfl

/-!
## `allow` and `allow_all` don't change `.prob` or `.cost`
-/

@[simp] lemma value_allow (f : Comp ι s α) (st : s ⊆ t) (o : I → Oracle ι) :
    (f.allow st).value o = f.value o := by
  induction' f with a b c d e f h0 h1
  · simp only [allow]; rfl
  · simp only [allow, value_query', h0, h1]

@[simp] lemma value_allow_all (f : Comp ι s α) (o : I → Oracle ι) :
    f.allow_all.value o = f.value o := by
  apply value_allow

@[simp] lemma cost_allow (f : Comp ι s α) (st : s ⊆ t) (o : I → Oracle ι) (i : I) :
    (f.allow st).cost o i = f.cost o i := by
  induction' f with _ _ _ _ _ _ h0 h1
  · simp only [allow, cost_pure, cost_pure']
  · simp only [allow, cost_query', h0, h1]

@[simp] lemma cost_allow_all (f : Comp ι s α) (o : I → Oracle ι) (i : I) :
    f.allow_all.cost o i = f.cost o i := by
  apply cost_allow

@[simp] lemma allow_pure (x : α) (st : s ⊆ t) : (pure x : Comp ι s α).allow st = pure x := by
  simp only [allow]

@[simp] lemma allow_all_pure (x : α) : (pure x : Comp ι s α).allow_all = pure x := by
  simp only [allow_all, allow_pure]

/- @[simp] lemma allow_bind (f : Comp ι s α) (g : α → Comp ι s β) (st : s ⊆ t) : -/
/-     (f >>= g).allow st = f.allow st >>= fun x ↦ (g x).allow st := by -/
/-   have e : ∀ v, bind' v g = v >>= g := fun _ ↦ rfl -/
/-   induction' f with x β u v h j m y f0 f1 h0 h1 -/
/-   · simp only [pure'_bind, allow, pure_bind] -/
/-   · simp only [allow, e, h, sample'_bind, pure_bind] -/
/-   · simp only [allow, e, h0, h1, query'_bind] -/

/- @[simp] lemma allow_all_bind (f : Comp ι s α) (g : α → Comp ι s β) : -/
/-     (f >>= g).allow_all = f.allow_all >>= fun x ↦ (g x).allow_all := -/
/-   allow_bind f g _ -/

/- @[simp] lemma allow_allow (f : Comp ι s α) (st : s ⊆ t) (tu : t ⊆ u) : -/
/-     (f.allow st).allow tu = f.allow (st.trans tu) := by -/
/-   induction' f with x β u v h j m y f0 f1 h0 h1 -/
/-   · simp only [allow] -/
/-   · simp only [allow, bind', h, sample'_bind, pure_bind] -/
/-   · simp only [allow, h0, h1] -/

/- @[simp] lemma allow_all_allow (f : Comp ι s α) (st : s ⊆ t) : -/
/-     (f.allow st).allow_all = f.allow_all := by -/
/-   simp only [allow_all, allow_allow] -/

@[simp] lemma value_map (f : α → β) (g : Comp ι s α) (o : I → Oracle ι) :
    (f <$> g).value o = f  (g.value o) := by
  simp only [Comp.map_eq, value_bind, value_pure]

lemma cost_map (f : α → β) (g : Comp ι s α) (o : I → Oracle ι) (i : I) :
    (f <$> g).cost o i = g.cost o i := by
  simp only [map_eq, cost_bind, cost_pure, add_zero]
