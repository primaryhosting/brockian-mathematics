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

theorem finite_ramsey (n k m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin k, ∃ Y ⊆ Finset.Icc 1 N,
      m ≤ Y.card ∧ ∃ a : Fin k, ∀ t ⊆ Y, t.card = n → c t = a := by
  obtain ⟨N, hN⟩ := Paris_Harrington n k m
  refine ⟨N, fun c => ?_⟩
  obtain ⟨Y, hsub, hcard, -, hhom⟩ := hN c
  exact ⟨Y, hsub, hcard, hhom⟩

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

