/-
Copyright (c) 2025 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Tomaz Mascarenhas
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Set.Basic

/-!
# Definition of a model of computation based on oracles.

This module defines and provide a Monad instance for a model of computation to be used for
reasoning on the upper bound of query complexity of algorithms.

Note that this is the deterministic version. In the future, the stochastic version will
be ported. With it, one will be able to prove lower bounds on the query complexity
of algorithms. The design of the types here is based on the original stochastic version.
Source:
  https://github.com/girving/debate/blob/862fdb1cf55df0d541b802bdb1e672d724df6398/Comp/Oracle.lean

## Main Definitions

- Comp (ι : Type) {I : Type} (s : Set I) (α : Type) : Type
- Comp.run : Comp ι s α → (I → Oracle ι) → α × (I → ℕ)
-/

open Classical
open Set
noncomputable section

variable {ι I : Type}
variable {s t : Set I}
variable {α β γ : Type}

-- A deterministic oracle is a map from `α` to `Bool`
def Oracle (α : Type) := α → Bool

/- A deterministic computation that can make oracle queries.
   A computation is either a value or an oracle drawn from a given set,
   a value to be queried by the oracle and two other computations, to
   be run depending on the answer of the oracle.
-/
inductive Comp (ι : Type) {I : Type} (s : Set I) (α : Type) : Type where
  | pure' : α → Comp ι s α
  | query' : (o : I) → o ∈ s → ι → Comp ι s α → Comp ι s α → Comp ι s α

namespace Comp

/-- Bind two `Comp`s together -/
def bind' (f : Comp ι s α) (g : α → Comp ι s β) : Comp ι s β := match f with
  | .pure' x => g x
  | .query' o m y f0 f1 => .query' o m y (f0.bind' g) (f1.bind' g)

/-- `Comp` is a monad -/
instance : Monad (Comp ι s) where
  pure := Comp.pure'
  bind := Comp.bind'

/-- The simplest case of `Comp.query'` -/
def query (i : I) (y : ι) : Comp ι {i} Bool :=
  Comp.query' i (mem_singleton _) y (pure true) (pure false)

/-- The value and query counts of a `Comp ι s`, once we supply oracles -/
def run (f : Comp ι s α) (o : I → Oracle ι) : α × (I → ℕ) := match f with
  | .pure' x => (x, fun _ => 0)
  | .query' i _ y f0 f1 =>
    let x := (o i) y
    let (z,c) := if x then f0.run o else f1.run o
    (z, c + fun j => if j = i then 1 else 0)

/-- The value of a `Comp ι s` -/
def value (f : Comp ι s α) (o : I → Oracle ι) : α :=
  Prod.fst (f.run o)

/-- The value of a `Comp ι s` when all oracles are the same -/
@[simp] def value' (f : Comp ι s α) (o : Oracle ι) : α :=
  f.value fun _ ↦ o

/-- The cost of a `Comp ι s` for a specific oracle -/
def cost (f : Comp ι s α) (o : I → Oracle ι) (i : I) : ℕ :=
  Prod.snd (f.run o) i

/-- The cost of a `Comp ι s`, when run with a single oracle -/
def cost' (f : Comp ι s α) (o : Oracle ι) : I → ℕ :=
  f.cost fun _ ↦ o

/-- Allow more oracles in a computation -/
def allow (f : Comp ι s α) (st : s ⊆ t) : Comp ι t α := match f with
  | .pure' x => pure x
  | .query' i m y f0 f1 => .query' i (st m) y (f0.allow st) (f1.allow st)

/-- Allow all oracles in a computation -/
def allow_all (f : Comp ι s α) : Comp ι (@univ I) α :=
  f.allow (subset_univ s)

end Comp
