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

def StrengthenedFiniteRamsey : Prop :=
  ∀ n k m : ℕ, ∃ N : ℕ, ∀ c : Finset ℕ → Fin k, ∃ Y : Finset ℕ, IsPHWitness n m N c Y

/-- Along an ultrafilter, a family of colourings has a limit colouring. -/
