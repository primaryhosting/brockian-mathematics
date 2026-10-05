import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open MeasureTheory

/-! ## The standard Gaussian measure and the statement of the inequality -/

/-- The standard Gaussian (probability) measure on `ℝ ^ n`, realised as the `n`-fold product
of the one-dimensional standard Gaussian `N(0,1)`. -/

theorem symmetricConvex_nested_dim_one {K L : Set (Fin 1 → ℝ)}
    (hK : SymmetricConvex K) (hL : SymmetricConvex L) : K ⊆ L ∨ L ⊆ K := by
  rcases symmetricConvexReal_nested (coord1_convex hK) (coord1_symm hK)
      (coord1_convex hL) (coord1_symm hL) with h | h
  · left
    intro x hx
    exact (mem_coord1_iff x).mp (h ((mem_coord1_iff x).mpr hx))
  · right
    intro x hx
    exact (mem_coord1_iff x).mp (h ((mem_coord1_iff x).mpr hx))

/-! ## The base cases of the Gaussian correlation inequality -/

/-- **Gaussian correlation inequality, base case `n = 1`.**
For the standard Gaussian measure on the line, `γ(K) · γ(L) ≤ γ(K ∩ L)` for all symmetric
convex sets `K`, `L`. (This is the one-dimensional instance of Royen's theorem; the proof
proceeds through the fact that symmetric convex subsets of the line are nested.) -/
