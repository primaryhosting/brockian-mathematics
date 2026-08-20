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

lemma limit_coloring_finite_agreement {k : ℕ} (U : Ultrafilter ℕ) (F : ℕ → Finset ℕ → Fin k)
    (c : Finset ℕ → Fin k) (hc : ∀ s : Finset ℕ, {N | F N s = c s} ∈ U)
    (T : Finset (Finset ℕ)) : {N | ∀ s ∈ T, F N s = c s} ∈ U :=
  (Filter.eventually_all_finset T).mpr fun s _ => hc s

/-- From an infinite homogeneous set one extracts a relatively large finite homogeneous set of any
prescribed size, consisting of positive numbers. -/
