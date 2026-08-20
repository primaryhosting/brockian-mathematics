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

def RelativelyLarge (Y : Finset ℕ) : Prop := ∃ h : Y.Nonempty, Y.min' h ≤ Y.card

/-- `Y` witnesses the strengthened finite Ramsey property for the colouring `c` of `n`-element
sets inside `{1, …, N}`, with size demand `m`: it is a relatively large homogeneous subset of
`{1, …, N}` with at least `m` elements. -/
