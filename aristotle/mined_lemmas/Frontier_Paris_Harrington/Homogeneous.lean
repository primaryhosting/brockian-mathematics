/-
# The infinite Ramsey theorem

Mathlib (as of this project's pinned version) contains no form of Ramsey's theorem, so we develop
the infinite version here, for colourings of `n`-element subsets of `ℕ` with `k` colours.

An infinite homogeneous set is presented as the range of a strictly monotone function `f : ℕ → ℕ`.
-/
import Mathlib

set_option autoImplicit false

namespace Frontier

open Finset

/-- `Homogeneous n c f a` says that every `n`-element subset of the range of `f` has colour `a`. -/

def Homogeneous {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (f : ℕ → ℕ) (a : Fin k) : Prop :=
  ∀ s : Finset ℕ, s.card = n → c (s.image f) = a

/-- A finite subset of the range of a map is the image of a finite set of the same
cardinality. -/
