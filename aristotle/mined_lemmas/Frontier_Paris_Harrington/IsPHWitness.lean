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

def IsPHWitness {k : ℕ} (n m N : ℕ) (c : Finset ℕ → Fin k) (Y : Finset ℕ) : Prop :=
  Y ⊆ Finset.Icc 1 N ∧ m ≤ Y.card ∧ RelativelyLarge Y ∧
    ∃ a : Fin k, ∀ t ⊆ Y, t.card = n → c t = a

/-- The **strengthened finite Ramsey theorem** (the Paris–Harrington statement): for all `n, k, m`
there is `N` such that every `k`-colouring of the `n`-element subsets of `{1, …, N}` admits a
relatively large homogeneous subset of `{1, …, N}` with at least `m` elements. -/
