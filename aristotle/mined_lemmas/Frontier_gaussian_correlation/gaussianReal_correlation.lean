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

theorem gaussianReal_correlation {A B : Set ℝ} (hAc : Convex ℝ A) (hAs : ∀ x ∈ A, -x ∈ A)
    (hBc : Convex ℝ B) (hBs : ∀ x ∈ B, -x ∈ B) :
    ProbabilityTheory.gaussianReal 0 1 A * ProbabilityTheory.gaussianReal 0 1 B
      ≤ ProbabilityTheory.gaussianReal 0 1 (A ∩ B) := by
  rcases symmetricConvexReal_nested hAc hAs hBc hBs with h | h
  · exact measure_mul_le_measure_inter_of_subset _ h
  · rw [mul_comm, Set.inter_comm]
    exact measure_mul_le_measure_inter_of_subset _ h

/-! ## Transfer from `Fin 1 → ℝ` to `ℝ` -/

/-- The coordinate description of a subset of `Fin 1 → ℝ`. -/
