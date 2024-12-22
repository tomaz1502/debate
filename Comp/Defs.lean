import Comp.Oracle
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Set.Basic


/-!
## Oracle-relative probabilitistic computations

`Prob α` represents the result of a probabilistic computation, but has no information about
how long the computation took.  `Comp ι s α` is a computation that is allowed to consult any
oracle `o ∈ s`, and produces a distribution over results and calls to each oracle.
-/

open Classical
open Option (some none)
open Set
noncomputable section

variable {ι I : Type}
variable {s t : Set I}
variable {α β γ : Type}

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

def cost (f : Comp ι s α) (o : I → Oracle ι) (i : I) : ℕ :=
  Prod.snd (f.run o) i

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
